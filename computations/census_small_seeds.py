"""Enumerate ordered distance-four pairs with 12 or 13 crossings on closed S_2.

Only the Python standard library and the companion verify_distance_six module
are required. Run: python census_small_seeds.py [12 13].
"""
from collections import Counter
from itertools import combinations_with_replacement, permutations, product
from pathlib import Path
import sys

try:
    import verify_distance_six as curves
except ModuleNotFoundError:
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'outputs'))
    import verify_distance_six as curves


ROTATION = tuple(3 * (d // 3) + (d + 1) % 3 for d in range(12))


def pairings(remaining, mate):
    """All ways of identifying the twelve triangle sides in six pairs."""
    if not remaining:
        yield tuple(mate)
        return
    first = remaining[0]
    for i, other in enumerate(remaining[1:], 1):
        mate[first], mate[other] = other, first
        yield from pairings(remaining[1:i] + remaining[i+1:], mate)


def boundary_circles(mate):
    unseen = set(range(12))
    circles = []
    while unseen:
        d = min(unseen)
        circle = []
        while d in unseen:
            unseen.remove(d)
            circle.append(d)
            d = ROTATION[mate[d]]
        circles.append(circle)
    return circles


def rooted_code(mate, start):
    """A canonical numbering from one dart, following rotation and edge gluing."""
    order = [start]
    index = {start: 0}
    code = []
    for d in order:
        for target in (ROTATION[d], mate[d]):
            if target not in index:
                index[target] = len(order)
                order.append(target)
            code.append(index[target])
    return tuple(code), set(order)


def triangulation_key(mate):
    unseen = set(range(12))
    components = []
    while unseen:
        _, part = rooted_code(mate, min(unseen))
        components.append(min(rooted_code(mate, d)[0] for d in part))
        unseen -= part
    return tuple(sorted(components))


def triangulations():
    seen, eligible, selected = set(), set(), []
    total = 0
    for mate in pairings(tuple(range(12)), [0]*12):
        total += 1
        circles = boundary_circles(mate)
        if len(circles) == 2:
            eligible.add(mate)
            code = triangulation_key(mate)
            if code not in seen:
                seen.add(code)
                selected.append((mate, circles))
    assert total == 10_395
    # Check the reduction by actually applying every allowed triangle relabeling.
    relabelings = [
        tuple(3*order[d//3] + (d%3 + turns[d//3]) % 3 for d in range(12))
        for order in permutations(range(4)) for turns in product(range(3),repeat=4)
    ]
    covered = set()
    for mate, _ in selected:
        orbit = set()
        for labels in relabelings:
            renamed = [0]*12
            for d in range(12):
                renamed[labels[d]] = labels[mate[d]]
            orbit.add(tuple(renamed))
        assert covered.isdisjoint(orbit)
        covered.update(orbit)
    assert covered == eligible
    print(f'{len(eligible)} labeled pairings have two ideal vertices. '
          f'Checked all {len(relabelings)} orientation-preserving triangle relabelings.',flush=True)
    return selected


def diagrams(n, mate, circles):
    """Place parallel copies on each edge and reglue the two boundary circles."""
    edges = [d for d in range(12) if d < mate[d]]
    for cuts in combinations_with_replacement(range(n+1), 5):
        points = (0,) + cuts + (n,)
        ends = {}
        for j, d in enumerate(edges):
            low, high = 2*points[j], 2*points[j+1]
            ends[d] = range(low, high, 2)
            ends[mate[d]] = range(high-1, low-1, -2)
        top, bottom = [[k for d in circle for k in ends[d]] for circle in circles]
        if len(top) != n:
            continue
        bottom.reverse()
        for shift in range(n):
            matching, signed = [0]*(2*n), [0]*(2*n)
            for j, upper in enumerate(top):
                lower = bottom[(j+shift) % n]
                matching[upper], matching[lower] = lower, upper
                signed[upper], signed[lower] = j+1, -j-1
            d = top[0]
            word = []
            while True:
                word.append(signed[d])
                d = matching[d ^ 1]
                if d == top[0]:
                    break
            if len(word) == n:
                yield tuple(word)


def diagram_key(word):
    """Allow cyclic relabeling and reversal on each curve, and global sign change."""
    n = len(word)
    best = None
    for order in (word, word[::-1]):
        for j, initial in enumerate(order):
            cycle = order[j:] + order[:j]
            for direction in (1, -1):
                code = tuple((1 if v*initial > 0 else -1) *
                             (1 + direction*(abs(v)-abs(initial)) % n) for v in cycle)
                if best is None or code < best:
                    best = code
    return best


def audit_size(n, shapes):
    seen, seeds = set(), []
    for mate, circles in shapes:
        for word in diagrams(n, mate, circles):
            # A filling genus-two diagram has N-2 faces and no complementary bigon.
            faces = curves.cut_faces(word)
            if len(faces) != n-2 or any(len(f) < 2 for f in faces):
                continue
            code = diagram_key(word)
            if code in seen:
                continue
            seen.add(code)
            if not curves.reachable(code,3) and curves.reachable(code,4):
                seeds.append(code)
    results = Counter()
    for seed in sorted(seeds):
        image = curves.twist_diagram(seed,1)
        distance = next(d for d in (3,4,5,6) if curves.reachable(image,d))
        curves.verify_distance(f'{n}-crossing seed {seed}, one twist', image, distance, audit=True)
        results[distance] += 1
    print(f'{n} crossings: {len(seen)} ordered filling diagram classes, '
          f'{len(seeds)} at distance four. Unit-twist distance counts: {dict(results)}.',flush=True)


if __name__ == '__main__':
    shapes = triangulations()
    print(f'{len(shapes)} oriented triangulation types with two ideal vertices.',flush=True)
    for n in map(int, sys.argv[1:] or ['12','13']):
        audit_size(n,shapes)
