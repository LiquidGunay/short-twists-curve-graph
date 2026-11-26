"""Enumerate the six-band family containing the two additional marked pairs."""
from itertools import combinations
from pathlib import Path
import sys

try:
    import verify_distance_six as curves
except ModuleNotFoundError:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'outputs'))
    import verify_distance_six as curves

def template():
    opposite, _ = curves.triangulate(curves.cut_faces(curves.FIGURE_18))
    edge_sides = [side for side, other in enumerate(opposite) if side < other]
    circles, visited = [], set()
    for start in range(len(opposite)):
        if start in visited:
            continue
        cycle, side = [], start
        while side not in visited:
            cycle.append(side)
            visited.add(side)
            other = opposite[side]
            side = (other // 3) * 3 + (other + 1) % 3
        circles.append(cycle)
    assert len(circles) == 2 and len(edge_sides) == 6
    return opposite, edge_sides, circles

def diagrams(crossings):
    opposite, edge_sides, circles = template()
    for cuts in combinations(range(1,crossings),5):
        boundaries = (0,) + cuts + (crossings,)
        widths = tuple(right-left for left,right in zip(boundaries,boundaries[1:]))
        ends, first = {}, 0
        for side,width in zip(edge_sides,widths):
            # A paired arc has an even and an odd endpoint.
            bundle = list(range(first,first+2*width,2))
            ends[side] = bundle
            ends[opposite[side]] = [k+1 for k in reversed(bundle)]
            first += 2*width
        top, bottom = [[k for side in circle for k in ends[side]] for circle in circles]
        if len(top) != crossings:
            continue
        bottom.reverse()
        for shift in range(crossings):
            matched = [0]*(2*crossings)
            labels = [0]*(2*crossings)
            for j, a in enumerate(top):
                b = bottom[(j+shift)%crossings]
                matched[a],matched[b] = b,a
                labels[a],labels[b] = j+1,-j-1
            dart = top[0]
            cycle = []
            while True:
                cycle.append(labels[dart])
                dart = matched[dart^1]
                if dart == top[0]:
                    break
            if len(cycle) == crossings:
                yield widths,shift,tuple(cycle)

if __name__ == '__main__':
    for target in (curves.THIRTEEN_CROSSINGS,curves.FOURTEEN_CROSSINGS):
        for index,(widths,shift,word) in enumerate(diagrams(len(target))):
            if word == target:
                print(f'{len(target)} crossings: widths {widths}, shift {shift}, connected diagram {index+1}.')
                break
        else:
            raise AssertionError('Target not found in the enumerated family.')
