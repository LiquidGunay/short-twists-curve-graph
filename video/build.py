"""Render the Manim chapters and mux the measured Kokoro audio, captions and chapter marks."""
import argparse
import json
import os
import shutil
import subprocess
from pathlib import Path

import av
import imageio_ffmpeg
from PIL import Image

from surface import build as build_surface

HERE=Path(__file__).resolve().parent
FPS=30
CHAPTERS={
    'Opening':'Curves and moves','Collar':'One turn in a collar','Fold':'A six-edge route',
    'Bounds':'The annular lower bound','Search':'Excluding five moves',
    'Census':'Why fourteen is sharp','AnyDistance':'Seven and beyond',
}


def render(data,cache,names,width,height):
    os.environ['CURVE_FILM_DATA']=str(data)
    os.environ.setdefault('PYTHONUTF8','1')
    from manim import tempconfig
    import scenes
    if not (data/'surface-paths.json').exists():
        build_surface(data)
    for name in names:
        is_poster=name=='Poster'
        settings={'media_dir':str(cache/'manim'/name),'output_file':name,'pixel_width':width,
                  'pixel_height':height,'frame_rate':FPS,'renderer':'cairo','background_color':scenes.BG,
                  'write_to_movie':not is_poster,'save_last_frame':is_poster,'format':'png' if is_poster else 'mp4',
                  'disable_caching':False,'progress_bar':'none','verbosity':'WARNING',
                  'preview':False,'show_in_file_browser':False,'max_files_cached':800}
        with tempconfig(settings):
            scene=getattr(scenes,name)()
            scene.render()
            writer=scene.renderer.file_writer
            if is_poster:
                with Image.open(writer.image_file_path) as frame:
                    frame.convert('RGB').save(cache/'poster.jpg',quality=92,optimize=True)
            else:
                shutil.copyfile(writer.movie_file_path,cache/f'{name}.mp4')
        print(f'Finished {name}',flush=True)


def frames_in(movie):
    with av.open(str(movie)) as video:
        stream=video.streams.video[0]
        if stream.average_rate!=FPS:
            raise ValueError(f'Unexpected frame rate in {movie}.')
        return stream.frames or sum(1 for _ in video.decode(stream))


def mux(data,cache,destination):
    ffmpeg=imageio_ffmpeg.get_ffmpeg_exe()
    schedule=json.loads((data/'timing.json').read_text(encoding='utf8'))
    chapters=[';FFMETADATA1']; files=[]
    for name,title in CHAPTERS.items():
        entry=schedule['scenes'][name]
        expected=entry['frames']
        clip=cache/f'{name}.mp4'
        actual=frames_in(clip)
        if abs(actual-expected)>3:
            raise ValueError(f'{name}: {actual} frames, expected {expected}')
        if actual!=expected:
            # Cairo may round the last static hold by a frame at a cut.
            fixed=cache/f'{name}-aligned.mp4'
            subprocess.run([ffmpeg,'-y','-v','error','-i',str(clip),'-vf','tpad=stop_mode=clone:stop_duration=0.1',
                            '-frames:v',str(expected),'-c:v','libx264','-crf','17','-pix_fmt','yuv420p',str(fixed)],check=True)
            clip=fixed
        files.append(f"file '{clip.name}'")
        chapters.extend(['[CHAPTER]',f'TIMEBASE=1/{FPS}',f"START={entry['start']}",
                         f"END={entry['start']+expected}",f'title={title}'])
    (cache/'clips.txt').write_text('\n'.join(files)+'\n',encoding='utf8')
    (cache/'chapters.ffmeta').write_text('\n'.join(chapters)+'\n',encoding='utf8')
    destination.parent.mkdir(parents=True,exist_ok=True)
    end_sample=schedule['frames']*(48000//FPS)
    audio_filter=f'loudnorm=I=-17:TP=-1.5:LRA=8,aresample=48000,atrim=end_sample={end_sample},asetpts=N/SR/TB'
    subprocess.run([ffmpeg,'-y','-v','warning','-f','concat','-safe','1','-i',str(cache/'clips.txt'),
                    '-i',str(data/'narration.wav'),'-i',str(data/'captions.srt'),'-f','ffmetadata','-i',str(cache/'chapters.ffmeta'),
                    '-map','0:v:0','-map','1:a:0','-map','2:s:0','-map_chapters','3','-map_metadata','3:g',
                    '-c:v','copy','-c:a','aac','-b:a','160k','-ar','48000','-af',audio_filter,
                    '-c:s','mov_text','-metadata:s:a:0','language=eng','-metadata:s:s:0','language=eng',
                    '-disposition:s:0','0','-metadata','title=Six moves on a double torus',
                    '-movflags','+faststart',str(destination)],check=True)
    if frames_in(destination)!=schedule['frames']:
        raise ValueError('The delivered frame count differs from the authored timeline.')
    print(destination, f"{schedule['frames']/FPS:.2f} s",flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('action',choices=['render','poster','mux','all'])
    p.add_argument('--data',type=Path,required=True,help='directory produced by narrate.py')
    p.add_argument('--cache',type=Path,required=True,help='Manim working directory')
    p.add_argument('--output',type=Path,default=HERE/'six-moves.mp4')
    p.add_argument('--scenes',nargs='+',choices=list(CHAPTERS),default=list(CHAPTERS))
    p.add_argument('--width',type=int,default=1920)
    p.add_argument('--height',type=int,default=1080)
    args=p.parse_args()
    data,cache=args.data.resolve(),args.cache.resolve()
    cache.mkdir(parents=True,exist_ok=True)
    if args.action in ('render','all'):
        render(data,cache,args.scenes,args.width,args.height)
    if args.action in ('poster','all'):
        render(data,cache,['Poster'],args.width,args.height)
    if args.action in ('mux','all'):
        mux(data,cache,args.output.resolve())
