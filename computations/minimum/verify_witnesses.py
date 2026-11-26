"""Reconstruct the extremal diagrams and test their exact distances."""
import argparse
from collections import Counter
from itertools import permutations, product
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import census_small_seeds as census
import certificates
import verify_distance_six as curves


def chart_word(mate, circles, widths, shift):
    edges = [d for d, other in enumerate(mate) if d < other]
    ends = {}
    first = 0
    for edge, width in zip(edges, widths):
        strands = range(first, first+width)
        ends[edge] = [(s, 0) for s in strands]
        ends[mate[edge]] = [(s, 1) for s in reversed(strands)]
        first += width
    top, bottom = [[p for dart in circle for p in ends[dart]] for circle in circles]
    bottom.reverse()
    assert len(top) == len(bottom) == first
    glue, labels = {}, {}
    for j, p in enumerate(top):
        q = bottom[(j+shift) % first]
        glue[p], glue[q] = q, p
        labels[p], labels[q] = j+1, -j-1
    p = top[0]
    word = []
    while True:
        word.append(labels[p])
        p = glue[p[0], 1-p[1]]
        if p == top[0]:
            break
    assert sorted(map(abs, word)) == list(range(1, first+1))
    return tuple(word)


def conservative_reachable(word, budget, calls):
    """Use the uniform bound B-1 from BMM, even on original, uncollapsed edges."""
    calls[budget] += 1
    if not word:
        return True
    faces = curves.cut_faces(word)
    if len(faces) > len(word)-2:
        return True
    assert len(faces) == len(word)-2 and all(len(f) >= 2 for f in faces)
    if budget == 2:
        return False
    mate, strips = curves.triangulate(faces)
    for route in curves.normal_curves(mate, budget-1):
        if conservative_reachable(curves.neighbour_pair(route, strips), budget-1, calls):
            return True
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--uniform-bound", action="store_true",
                        help="also exclude shortcuts with the larger BMM search at every node")
    args = parser.parse_args()
    # Euler characteristic allows three crossings only with one ribbon boundary.
    # Cyclically place label 1 first, then inspect both orders and all eight signs.
    for tail in permutations((2, 3)):
        for signs in product((1, -1), repeat=3):
            word = tuple(i*s for i, s in zip((1,)+tail, signs))
            assert len(curves.ribbon_face_lengths(word)) == 3
    charts = census.triangulations()
    # Check the actual charts compiled into the separate lower-bound verifier.
    source = (HERE / "certify_lower.cpp").read_text(encoding="utf-8")
    table = source.split("triangulations = {{", 1)[1].split("}};", 1)[0]
    compiled = [tuple(map(int, group.split(","))) for group in re.findall(r"\{([0-9,]+)\}", table)]
    assert compiled == [tuple(mate) for mate, _ in charts] and len(charts) == 6
    examples = json.loads((HERE / "witnesses.json").read_text(encoding="utf-8"))
    signed_totals = []
    for sample in examples:
        d = sample["distance"]
        mate, circles = charts[sample["chart"]]
        word = chart_word(mate, circles, sample["widths"], sample["shift"])
        assert list(word) == sample["word"]
        signed_totals.append(abs(sum(1 if i > 0 else -1 for i in word)))
        profile = dict(Counter(curves.ribbon_face_lengths(word)))
        assert profile == {4: len(word)-6, 6: 4}
        curves.verify_distance(f"widths {sample['widths']}, shift {sample['shift']}", word, d, audit=True)
        path = certificates.witness(word, d)
        assert path is not None and len(path["steps"]) == d-2
        print("Upper path", json.dumps(path), flush=True)
        if args.uniform_bound:
            calls = Counter()
            if conservative_reachable(word, d-1, calls):
                raise RuntimeError(f"short path at {len(word)} crossings")
            print("Uniform-bound calls by remaining budget:", dict(sorted(calls.items(), reverse=True)),
                  flush=True)
    assert [(sample["distance"], total) for sample,total in zip(examples,signed_totals)] == [
        (5, 0), (6, 96), (6, 48)]
    print("Absolute algebraic intersections:", signed_totals, flush=True)


if __name__ == "__main__":
    main()
