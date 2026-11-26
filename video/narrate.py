"""Synthesize the film's Kokoro narration, speech-timed captions and 30 fps cue sheet."""
import argparse
import hashlib
import json
import re
import textwrap
import wave
from pathlib import Path

import numpy as np
import onnxruntime as ort
from kokoro_onnx import Kokoro

RATE = 24000
FPS = 30
SAMPLES_PER_FRAME = RATE // FPS
HERE = Path(__file__).resolve().parent


def phrases(text):
    """Give the synthesizer complete sentences, or clauses at natural pauses."""
    for sentence in re.split(r'(?<=[.?!])\s+', text):
        if len(sentence) <= 108:
            yield sentence
            continue
        choices = [m.end() for m in re.finditer(r',\s+|;\s+|(?= and | but | so that | that if | if | when | which )',sentence)]
        choices = [p for p in choices if 26 <= p <= len(sentence)-22]
        if choices:
            split = min(choices,key=lambda n: abs(n-len(sentence)/2))
            yield sentence[:split].strip()
            yield from phrases(sentence[split:].strip())
        else:
            yield sentence


def voice_text(text):
    for before,after in (('A and B','ay and bee'),('from A to B','from ay to bee'),
                         ('twist A around B','twist ay around bee'),('along A,','along ay,')):
        text = text.replace(before,after)
    return text


def trim(samples):
    samples = np.asarray(samples,dtype=np.float32).reshape(-1)
    voiced = np.flatnonzero(np.abs(samples) > 0.008)
    if not len(voiced):
        raise ValueError('Kokoro returned silence.')
    margin = round(RATE*.045)
    return samples[max(0,int(voiced[0])-margin):min(len(samples),int(voiced[-1])+margin+1)]


def timestamp(sample, vtt=False):
    millis = round(1000*sample/RATE)
    sep = '.' if vtt else ','
    return f'{millis//3600000:02d}:{millis//60000%60:02d}:{millis//1000%60:02d}{sep}{millis%1000:03d}'


def run(args):
    output = args.out.resolve()
    output.mkdir(parents=True,exist_ok=True)
    cache = output/'speech-cache'
    cache.mkdir(exist_ok=True)
    script = json.loads((HERE/'script.json').read_text(encoding='utf8'))
    options = ort.SessionOptions()
    options.intra_op_num_threads = args.threads
    options.inter_op_num_threads = 1
    session = ort.InferenceSession(str(args.model.resolve()),sess_options=options,providers=['CPUExecutionProvider'])
    engine = Kokoro.from_session(session,str(args.voices.resolve()))

    buffer, captions, scenes = [], [], {}
    cursor = 0
    def append(samples):
        nonlocal cursor
        buffer.append(samples)
        cursor += len(samples)
    def pause(seconds):
        append(np.zeros(round(seconds*RATE),dtype=np.float32))
    def align():
        append(np.zeros((-cursor)%SAMPLES_PER_FRAME,dtype=np.float32))

    model_tag = hashlib.sha256(args.model.read_bytes()).hexdigest()[:16]
    for scene,beats in script.items():
        start = cursor
        track = []
        pause(.20 if scene != 'Opening' else .32)
        for index,(name,text) in enumerate(beats):
            frame = (cursor-start)//SAMPLES_PER_FRAME
            for phrase in phrases(text):
                spoken = voice_text(phrase)
                key = hashlib.sha256(f'{model_tag}|{args.voice}|{args.speed}|{spoken}'.encode()).hexdigest()[:24]
                path = cache/f'{key}.npy'
                if not path.exists():
                    audio,rate = engine.create(spoken,voice=args.voice,speed=args.speed,lang='en-us')
                    if rate != RATE:
                        raise ValueError(f'Unexpected sample rate {rate}.')
                    np.save(path,trim(audio))
                samples = np.load(path,allow_pickle=False)
                t0 = cursor
                append(samples)
                captions.append((t0,cursor,phrase))
                pause(.17 if phrase[-1] in '.!?' else .095)
            pause(.22 if index+1<len(beats) else .56)
            align()
            track.append({'id':name,'start':frame,'end':(cursor-start)//SAMPLES_PER_FRAME,'text':text})
            print(scene,name,f'{cursor/RATE:.2f}s',flush=True)
        scenes[scene]={'start':start//SAMPLES_PER_FRAME,'frames':(cursor-start)//SAMPLES_PER_FRAME,'beats':track}
    audio=np.concatenate(buffer)
    peak=max(float(np.max(np.abs(audio))),1e-6)
    pcm=np.round(audio*(min(1.5,.92/peak)*32767)).astype('<i2')
    with wave.open(str(output/'narration.wav'),'wb') as out:
        out.setparams((1,2,RATE,0,'NONE','not compressed'))
        out.writeframes(pcm.tobytes())
    for vtt in (False,True):
        blocks=[]
        for i,(t0,t1,phrase) in enumerate(captions,1):
            wrapped='\n'.join(textwrap.wrap(phrase,49,break_long_words=False,break_on_hyphens=False))
            blocks.append(f'{i}\n{timestamp(t0,vtt)} --> {timestamp(t1,vtt)}\n{wrapped}\n')
        prefix='WEBVTT\n\n' if vtt else ''
        (output/('captions.vtt' if vtt else 'captions.srt')).write_text(prefix+'\n'.join(blocks),encoding='utf8')
    result={'fps':FPS,'sample_rate':RATE,'frames':cursor//SAMPLES_PER_FRAME,
            'voice':args.voice,'speed':args.speed,'scenes':scenes}
    (output/'timing.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf8')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--model',type=Path,required=True)
    parser.add_argument('--voices',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--voice',default='af_heart')
    parser.add_argument('--speed',type=float,default=1.01)
    parser.add_argument('--threads',type=int,default=3)
    run(parser.parse_args())
