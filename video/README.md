# Six moves on a double torus

This animated companion follows a particular pair of curves from twelve initial crossings through one and two Dehn twists. It then compares every genus-two distance-four starting pair with twelve or thirteen crossings and the fourteen-crossing example that attains six. The seven chapters are embedded in the MP4. English subtitles can be selected in a compatible player. [Watch the film](six-moves.mp4) · [Captions](captions.vtt) · [Spoken script](script.json)

## Chapters

| Start | Chapter |
|---|---|
| 0:00 | Disjoint curves and the five-edge shortcut |
| 0:16 | Mahanta's marked pair and a twist in the collar |
| 0:50 | Building the six-edge route |
| 1:12 | What the annular projection can exclude |
| 1:43 | Ruling out every five-edge route |
| 2:23 | The census and the 14-crossing witness |
| 3:03 | A geodesic of length seven |

## Rebuild the film

The release uses Python 3.12, Manim Community's Cairo renderer, and the Kokoro-82M v1.0 model through the ONNX runtime. The voice is the stock English voice **af_heart**, at speed 1.01. The surface and its visible curves are calculated by the supplied Python code. The render used Georgia and Segoe UI on Windows. Liberation Serif and DejaVu Sans are supported alternatives.

From the repository root, install the media dependencies in a Python environment and create a working directory.

~~~sh
python -m pip install -r video/requirements.txt
python -c "from pathlib import Path; Path('.build/models').mkdir(parents=True,exist_ok=True)"
~~~

Download the two upstream Kokoro assets below to the indicated filenames in that directory. On Unix-like systems these commands use curl. Use curl.exe on Windows.

~~~sh
curl -fL -o .build/models/kokoro-v1.0.onnx https://github.com/thewh1teagle/kokoro-onnx/releases/download/model-files-v1.0/kokoro-v1.0.onnx
curl -fL -o .build/models/voices-v1.0.bin https://github.com/thewh1teagle/kokoro-onnx/releases/download/model-files-v1.0/voices-v1.0.bin
python video/narrate.py --model .build/models/kokoro-v1.0.onnx --voices .build/models/voices-v1.0.bin --out .build/film
python video/build.py all --data .build/film --cache .build/render --output .build/six-moves.mp4
~~~

The first Python command synthesizes the speech, measures each phrase in audio samples, and writes a lossless narration master, captions and a frame-aligned timeline. The second renders the scenes at 1920 × 1080 and 30 fps, then combines them with the narration and chapter marks. To iterate on a particular chapter, use the render action and specify its class name.

~~~sh
python video/build.py render --data .build/film --cache .build/render --scenes Collar Fold
~~~

The two loops at the opening illustrate disjointness. The numbered rows show the actual twelve- and fourteen-crossing witnesses. Reading along each curve and recording the signs recovers the marked surface by the construction in §2 of the paper. The collar uses three representative moving strands for legibility. The entire first pair has twelve. The graph of candidate shortcuts illustrates branching, and its displayed totals come from the checked computation. The counts of five and eleven starting classes allow orientation-reversing surface homeomorphisms and keep the order of the two curves.

The model weights and voice data are distributed upstream. [Kokoro model card and license](https://huggingface.co/hexgrad/Kokoro-82M) · [ONNX distribution](https://github.com/thewh1teagle/kokoro-onnx/releases/tag/model-files-v1.0) · [Manim installation guide](https://docs.manim.community/en/stable/installation.html)
