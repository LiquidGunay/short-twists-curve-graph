"""Verify the distance-six examples. Run with Python 3.9 or later, standard library only.

A diagram is a cyclic signed permutation. Intersections are numbered from 1
along the first curve, and listed in order along the second. A positive sign
means that the second curve leaves the crossing on the chosen positive side
of the first. Reversing the orientation of the surface is immaterial.

Completeness: Birman, Margalit and Menasco, Theorem 1.1 and Proposition 3.7,
https://arxiv.org/pdf/1408.4133. The companion note explains the ribbon graph,
the normal coordinates, and the terminal Euler characteristic test.
"""
from collections import Counter
from functools import lru_cache
from itertools import product


# Section 6, Figures 18 and 22-27 of arXiv:2211.15290v3.
FIGURE_18 = (1, -8, -3, -10, 5, 6, 7, -2, -9, -4, 11, 12)
THIRTEEN_CROSSINGS = (1, -8, -3, -9, -4, 11, 13, 2, 7, 6, 5, 10, 12)
FOURTEEN_CROSSINGS = (1, -9, -3, -11, -5, -6, -7, -8, -2, -10, -4, 12, 13, 14)
# Crossing order of the horizontal and vertical curves on the four squares in Section 6.
FOUR_SQUARES = (1, 2, 4, 3)


def twist_diagram(code, power):
    """Return the diagram of (a, T_b^power(a)) given (a,b); power > 0.

    In a collar with circumference 4n, strand j of a is at column 4j.
    Push the other copy to one side of a before twisting. Its strand in
    column 4j starts one unit to the right or left according to orientation
    and wraps through exactly 'power' turns. No crossings occur outside.
    """
    assert power > 0
    n = len(code)
    circumference = 4 * n
    columns = [None] * n
    signs = [None] * n
    for col, signed_label in enumerate(code):
        index = abs(signed_label) - 1
        columns[index] = 4 * col
        signs[index] = 1 if signed_label > 0 else -1
    assert None not in columns
    on_a = [[] for _ in code]
    on_twisted = [[] for _ in code]
    for strand in range(n):
        start = columns[strand] + signs[strand]
        for fixed in range(n):
            first = (columns[fixed] - start) % circumference
            for turn in range(power):
                height = first + turn * circumference
                key = (strand, fixed, turn)
                on_a[fixed].append((signs[fixed] * height, key))
                on_twisted[strand].append((signs[strand] * height, key))
    labels = {}
    for points in on_a:
        for _, key in sorted(points):
            labels[key] = len(labels) + 1
    return tuple(signs[s] * signs[f] * labels[s, f, k]
                 for points in on_twisted for _, (s, f, k) in sorted(points))


def cut_faces(code):
    """Collapse the two boundary circles of the cut surface to ideal vertices.

    Dart 2j follows the j-th oriented segment of the second curve.
    Dart 2j+1 is its reverse. The two boundary circles inherit opposite orders.
    """
    n = len(code)
    positive = [0] * n
    negative = [0] * n
    for j, label in enumerate(code):
        index = abs(label) - 1
        outgoing, incoming = 2 * j, (2 * j - 1) % (2 * n)
        if label < 0:
            outgoing, incoming = incoming, outgoing
        positive[index], negative[index] = outgoing, incoming
    next_dart = [0] * (2 * n)
    for j in range(n):
        next_dart[positive[j] ^ 1] = positive[(j + 1) % n]
        next_dart[negative[j] ^ 1] = negative[j - 1]
    faces = []
    seen = bytearray(2 * n)
    for start in range(2 * n):
        if seen[start]:
            continue
        d = start
        face = []
        while not seen[d]:
            face.append(d)
            seen[d] = 1
            d = next_dart[d]
        faces.append(face)
    return faces


def triangulate(faces):
    """Collapse each strip of parallel arcs, then fan-triangulate each polygon.

    The return value pairs triangle sides and records the consecutive original
    darts crossed on exiting through each side.
    """
    parallel = {}
    for face in faces:
        if len(face) == 2:
            u, v = face
            parallel[u], parallel[v] = v, u
    triangles = []
    diagonals = {}
    fresh = sum(map(len, faces))
    for face in faces:
        if len(face) == 2:
            continue
        assert len(face) >= 3
        first = face[0]
        for i in range(1, len(face) - 2):
            triangles.extend((first, face[i], fresh))
            diagonals[fresh], diagonals[fresh + 1] = fresh + 1, fresh
            first = fresh + 1
            fresh += 2
        triangles.extend((first, face[-2], face[-1]))
    position = {d: i for i, d in enumerate(triangles)}
    opposite, strips = [], []
    for d in triangles:
        strip = []
        if d in diagonals:
            other = diagonals[d]
        else:
            e = d
            while True:
                strip.append(e)
                other = e ^ 1
                if other not in parallel:
                    break
                e = parallel[other]
        opposite.append(position[other])
        strips.append(tuple(strip))
    return tuple(opposite), strips


@lru_cache(maxsize=None)
def normal_curves(opposite, bound):
    """Enumerate connected normal curves with at most 'bound' hits per edge.

    An entry (side,t,reverse) records a crossing of an edge from the given
    side. The last two fields index the same point in the two boundary orders.
    """
    n = len(opposite)
    edge = [0] * n
    count = 0
    for d, other in enumerate(opposite):
        if d < other:
            edge[d] = edge[other] = count
            count += 1
    patterns = []
    for weights in product(range(bound + 1), repeat=count):
        total = sum(weights)
        if not total:
            continue
        width = [weights[e] for e in edge]
        triangle_arcs = {}
        for start in range(0, n, 3):
            a, b, c = width[start:start + 3]
            if (a + b + c) % 2 or 2 * max(a, b, c) > a + b + c:
                break
            for u, v, w in ((0, 1, 2), (1, 2, 0), (2, 0, 1)):
                d, f = start + u, start + v
                joins = (width[d] + width[f] - width[start + w]) // 2
                for t in range(joins):
                    p1, p2 = (d, width[d] - 1 - t), (f, t)
                    triangle_arcs[p1], triangle_arcs[p2] = p2, p1
        else:
            start_slot = next(iter(triangle_arcs))
            d, t = start_slot
            route = []
            while True:
                reverse = width[d] - 1 - t
                route.append((d, t, reverse))
                d, t = triangle_arcs[opposite[d], reverse]
                if (d, t) == start_slot:
                    break
            if len(route) == total:
                patterns.append(tuple(route))
    return tuple(sorted(patterns, key=len))


def neighbour_pair(route, strips):
    """Read the signed diagram of (candidate neighbour, second curve).

    As we trace the candidate, label its crossings in order. Sorting by the
    original segment and position then recovers the order on the second curve.
    """
    crosses = []
    for side, t, reverse in route:
        for dart in strips[side]:
            number = len(crosses) + 1
            if dart % 2:
                crosses.append((dart // 2, reverse, -number))
            else:
                crosses.append((dart // 2, t, number))
    return tuple(number for _, _, number in sorted(crosses))


def ribbon_face_lengths(code):
    """Count the original polygon sides independently, using four darts per crossing.

    Directions 0,1,2,3 are forward on a, forward on b, backward on a,
    and backward on b. Compose edge reversal with the crossing rotation.
    """
    n = len(code)
    opp = [0] * (4 * n)
    rot = [0] * (4 * n)
    for j, signed in enumerate(code):
        v = abs(signed) - 1
        nxt = abs(code[(j + 1) % n]) - 1
        for u, w in ((4*v, 4*((v+1) % n)+2), (4*v+1, 4*nxt+3)):
            opp[u], opp[w] = w, u
        step = 1 if signed > 0 else -1
        for d in range(4):
            rot[4*v+d] = 4*v+(d+step) % 4
    seen = bytearray(4*n)
    lengths = []
    for d in range(4*n):
        if seen[d]:
            continue
        length = 0
        while not seen[d]:
            seen[d] = 1
            length += 1
            d = rot[opp[d]]
        lengths.append(length)
    return sorted(lengths)


def reachable(code, budget, genus=2, stats=None, audit=False):
    """Decide distance <= budget, for budget >= 2 and a minimal diagram.

    Birman-Margalit-Menasco Theorem 1.1 guarantees that when the endpoints
    fill, some first neighbour of a shortest path is in normal_curves. A
    peripheral normal curve can represent the current first endpoint. A
    repeated vertex cannot make a false positive for a bounded walk.
    """
    assert budget >= 2
    if stats is not None:
        stats[budget] += 1
    if not code:
        return True
    faces = cut_faces(code)
    if audit:
        assert sorted(2*len(f) for f in faces) == ribbon_face_lengths(code)
    # The connected regular neighbourhood has Euler characteristic -len(code)
    # and one boundary circle per face cycle. It fills precisely when its
    # genus is the genus of the ambient closed surface.
    twice_genus = 2 + len(code) - len(faces)
    assert 0 <= twice_genus <= 2 * genus and twice_genus % 2 == 0
    if twice_genus < 2 * genus:
        return True
    if budget == 2:
        return False
    opposite, strips = triangulate(faces)
    assert len(opposite) == 12 * genus - 12
    # When every side comes from the original second curve, Prop. 3.7
    # improves the bound on every coordinate by one (BMM, Section 3.6).
    bound = budget - 2 if all(strips) else budget - 1
    for route in normal_curves(opposite, bound):
        if reachable(neighbour_pair(route, strips), budget - 1, genus, stats, audit):
            return True
    return False


def verify_distance(label, diagram, expected, audit=False):
    """Check both the lower bound and the upper bound and report search counts."""
    lower_calls = Counter()
    if reachable(diagram, expected - 1, stats=lower_calls, audit=audit):
        raise ValueError(f'{label}: found a path shorter than {expected}')
    if not reachable(diagram, expected, audit=audit):
        raise ValueError(f'{label}: failed to find a path of length {expected}')
    calls = dict(sorted(lower_calls.items(), reverse=True))
    print(f'{label}: {len(diagram)} intersections, distance {expected}. '
          f'Lower-bound calls by edge budget: {calls}', flush=True)


def vertices_at_distance(distance):
    """Return twist definitions and endpoints on the four-square surface.

    Trace the requested index back through the reflected paths. Only the
    logarithmically many twist definitions need to be stored.
    """
    if distance < 0:
        raise ValueError('Distance must be a nonnegative integer.')
    seed = ['h', 'e', 's', 'P(e)', 'P(h)']
    length = len(seed) - 1
    stages = []
    definitions = ['P = T_v']
    pivot = seed[-1]
    while length < distance:
        name = f'F{len(stages) + 1}'
        definitions.append(f'{name} = (T_{{{pivot}}})^{2 * length - 4}')
        stages.append((length, name))
        pivot = f'{name}(h)'
        length = 2 * length - 2
    index = distance
    twists = []
    for old_length, name in reversed(stages):
        if index >= old_length:
            twists.append(name)
            index = 2 * old_length - 2 - index
    endpoint = seed[index]
    for name in reversed(twists):
        endpoint = f'{name}({endpoint})'
    return definitions, ('h', endpoint)


if __name__ == '__main__':
    from argparse import ArgumentParser
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--distance', type=int, metavar='N',
                        help='print vertices at distance N on the four-square surface (paper, Section 6)')
    parser.add_argument('--audit', action='store_true',
                        help='cross-check every nonempty ribbon diagram by a separate four-dart face walk')
    args = parser.parse_args()
    if args.distance is not None:
        if args.distance < 0:
            parser.error('N must be nonnegative.')
        definitions, endpoints = vertices_at_distance(args.distance)
        print('Use the four squares and curves h, v, e, s in Section 6 of the paper.')
        print(*definitions, sep='\n')
        print(f'Distance {args.distance} endpoints: {endpoints[0]} and {endpoints[1]}')
    else:
        verify_distance('Figure 18 seed', FIGURE_18, 4, args.audit)
        for power, distance in [(1, 5), (2, 6), (3, 6)]:
            verify_distance(f'Figure 18, power {power}', twist_diagram(FIGURE_18, power), distance, args.audit)
        for label, seed, distance in [('Thirteen', THIRTEEN_CROSSINGS, 5), ('Fourteen', FOURTEEN_CROSSINGS, 6)]:
            verify_distance(f'{label}-crossing seed', seed, 4, args.audit)
            verify_distance(f'{label}-crossing seed, one twist', twist_diagram(seed, 1), distance, args.audit)
        nested = twist_diagram(twist_diagram(FOUR_SQUARES, 1), 1)
        verify_distance('Four squares, nested unit twists', nested, 5, args.audit)
