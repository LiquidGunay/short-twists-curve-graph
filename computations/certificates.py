"""Recover upper-bound witnesses. Edge weights use the checker's deterministic triangle-side order."""
import json
from collections import Counter
from pathlib import Path
import sys

try:
    import verify_distance_six as c
except ModuleNotFoundError:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'outputs'))
    import verify_distance_six as c

def witness(code, m):
    faces = c.cut_faces(code)
    g2 = 2 + len(code) - len(faces) if code else 0
    if g2 < 4:
        return dict(steps=[], terminal_crossings=len(code), terminal_neighborhood_genus=g2//2)
    if m == 2:
        return None
    paired, strips = c.triangulate(faces)
    bound = m - 2 if all(strips) else m - 1
    for route in c.normal_curves(paired,bound):
        new = c.neighbour_pair(route, strips)
        answer = witness(new, m-1)
        if answer is not None:
            counts = Counter(min(d,paired[d]) for d, _, _ in route)
            weights = [counts[d] for d,opp in enumerate(paired) if d < opp]
            answer['steps'].insert(0, weights)
            return answer
    return None

def run():
    data = {}
    for seed in [c.FIGURE_18,c.THIRTEEN_CROSSINGS,c.FOURTEEN_CROSSINGS]:
        n = len(seed)
        data[f'{n} seed'] = witness(seed,4)
        d = 5 if n < 14 else 6
        data[f'{n} unit twist'] = witness(c.twist_diagram(seed,1),d)
    data['12 double twist'] = witness(c.twist_diagram(c.FIGURE_18,2),6)
    data['12 triple twist'] = witness(c.twist_diagram(c.FIGURE_18,3),6)
    nested = c.twist_diagram(c.twist_diagram(c.FOUR_SQUARES,1),1)
    data['four squares, nested unit twists'] = witness(nested,5)
    print(json.dumps(data, indent=2))

if __name__ == '__main__':
    run()
