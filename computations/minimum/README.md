# Minimum crossings on the closed double torus

The computer-assisted proof gives **40 crossings at distance five** and **132 crossings at distance six**. For the latter lower bound the direct census checks 17,383,334 width vectors that passed the first path test, 2,123,473,921 cyclic gluings and 540,360,860 connected presentations. Each connected case admits a path of at most five moves. Each row counts presentations and can include several encodings of one isotopy class. [Proof and chart diagram](../../paper/minimum-six.pdf) · [Per-size counts](census.csv) · [Signed crossing words](witnesses.json)

## Check the extremal examples

From the repository root, with Python 3.9 or newer, run

~~~sh
python computations/minimum/verify_witnesses.py --uniform-bound
~~~

This checks the six-chart atlas against all 10,395 triangle-side involutions, constructs the signed crossing words from the weights and shifts, and reconstructs their squares and hexagons. It separately finds a path and excludes all shorter paths using the efficient-geodesic theorem. With the larger bound on every normal coordinate, the shortcut test for the first 132-crossing example reaches 429,456 terminal diagrams. The two distance-six witnesses have absolute algebraic intersections 96 and 48, so no homeomorphism interchanges the two unordered pairs. [Saved run with both sets of search counts and path coordinates](endpoint-audit.txt) · [Lean reconstruction](../../proof/MinimumExamples.lean) · [Birman–Margalit–Menasco, Theorem 1.1](https://arxiv.org/pdf/1408.4133)

## Reproduce the lower bounds

The direct verifier requires a C++17 compiler. These shell commands compile it and check all positive intersection counts strictly below the thresholds. Choose `--jobs` to match the CPU. On Windows, use the path to the compiled `.exe` in place of `./certify_lower`.

~~~sh
c++ -std=c++17 -O3 computations/minimum/certify_lower.cpp -o certify_lower
python computations/minimum/run_census.py ./certify_lower 4 11 audit-four --jobs 4 --verify
python computations/minimum/run_census.py ./certify_lower 5 39 audit-five --jobs 4 --verify
python computations/minimum/run_census.py ./certify_lower 6 131 audit-six --jobs 8 --verify
~~~

Each output directory contains one transcript per intersection count and a combined CSV. For each target the released file has the same rows, in intersection order. The final column records completion of every shift and chart in the row. The number of surviving vectors times the crossing count equals the number of gluings. Zero surviving diagrams means that every connected gluing received a short-path certificate. For the boundary cases, running `./certify_lower 5 40 40 first` or `./certify_lower 6 132 132 first` stops at the first unresolved diagram. Stopping there does not count all minimizers. The dedicated endpoint verifier decides its exact distance for the published coordinates.

The proof only needs the implication that a short path found by the program exists in the surface graph. For each connected pair the code computes the ribbon genus or follows explicit embedded circuits through parallel bands. An established threshold at a smaller target can finish the path argument early. The target being proved is disabled as an input threshold. No width-vector symmetry reduction is used in this verifier.

## Reproduce the separate discovery computation

~~~sh
python computations/minimum/atlas.py atlas.txt
c++ -std=c++17 -O3 computations/minimum/discovery.cpp -o discovery
./discovery atlas.txt census 5 24 40 24
./discovery atlas.txt census 6 48 132 40
~~~

The last argument supplies a proven lower threshold for distance at least five. Use 24 while searching at distance five and 40 after the five-distance census is complete. This implementation partitions widths by the boundary incidence of each edge, reduces under chart symmetries, and reads crossing orders by following matched strand ends. It searches normal curves in triangulated polygons. The published ledger records completed rows below the first witness. On the overlap, both implementations have identical counts of width vectors passing the first cut at **each individual intersection count**. [Discovery ledger](discovery-census.csv) · [Direct verifier](certify_lower.cpp) · [Discovery source](discovery.cpp)

The two programs use the same topological classification of weighted cut surfaces. Their agreement checks two implementations of that argument. The mathematical coverage of surface pairs and the identification of the finite distance test with the curve graph are explained in the paper.
