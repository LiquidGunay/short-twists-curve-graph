"""Export the six exhaustively checked cut triangulations and their short curves."""
from pathlib import Path
from itertools import permutations, product
import argparse
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import census_small_seeds as census
import verify_distance_six as curves

def edge_permutations(mate, edges):
    edge_id = {side: i for i, d in enumerate(edges) for side in (d, mate[d])}
    symmetries = set()
    for order in permutations(range(4)):
        for turns in product(range(3), repeat=4):
            for orientation in (1, -1):
                labels = [3*order[d//3] + (orientation*(d%3) + turns[d//3])%3
                          for d in range(12)]
                if all(labels[mate[d]] == mate[labels[d]] for d in range(12)):
                    symmetries.add(tuple(edge_id[labels[d]] for d in edges))
    return sorted(symmetries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='destination for the generated atlas')
    args = parser.parse_args()
    shapes = census.triangulations()
    with args.output.open('w', encoding='ascii') as out:
        def emit(*values):
            print(*values, file=out)

        emit(len(shapes))
        for mate, circles in shapes:
            emit(*mate)
            for circle in circles:
                emit(len(circle), *circle)
            edges = [i for i in range(12) if i < mate[i]]
            symmetries = edge_permutations(mate, edges)
            emit(len(symmetries))
            for symmetry in symmetries:
                emit(*symmetry)
            for bound in range(1, 6):
                routes = curves.normal_curves(tuple(mate), bound)
                emit(len(routes))
                for route in routes:
                    emit(len(route), *(value for hit in route for value in hit))
    print('wrote', args.output, flush=True)


if __name__ == '__main__':
    main()
