# How much of distance six is proved in Lean?

The strongest unconditional result constructs two essential embedded circles on the compact topological space specified by the 14-crossing gluing word. Lean proves that the second circle represents the image of the first under one turn of the cylinder and gives a bijection between their intersection set and `Fin 196`. The step from this pair to distance six in the curve graph of the closed double torus remains conditional. [Named curves and theorems](SurfaceExamples.lean)

## The two curves

Write the cylinder as `(ℝ/ℤ) × [0,1]`. Its horizontal coordinate records cyclic position along the twist axis. The signed word divides that coordinate into fourteen slots. The labels prescribe which strand follows which when it crosses the seam. The intended surface is obtained by gluing the boundary intervals in this order. Lean takes the topological quotient, proves compactness and embeds the open interior of the cylinder in it. It proves that the maps `(x,t) ↦ (x+k t,t)` descend to homeomorphisms, with the opposite shear as inverse. [Gluing and shear](MarkedCylinder.lean) · [Open collar and circle parametrization](MarkedFamily.lean)

The marked circle runs up four slots and down ten. Take the vertical coordinate modulo one. On the curve its signed changes add to −6. A homotopy to a constant would give it a continuous lift into the real line, and the signed changes around any closed lift sum to zero. This contradiction proves essentiality. The proof of embeddedness includes points where the strands meet the seam. Moving a strand from offset 1/2 to 3/4 gives a continuous family of embedded circles, so the pushed-off copy represents the same vertex. [Lift under homotopy](CircleLifts.lean) · [Closed embeddings](MarkedEmbeddings.lean) · [Essentiality and isotopy](EssentialMarking.lean)

The twist of the pushed-off curve has one crossing for each ordered choice of a fixed and a moving strand. A seam invariant excludes additional intersections on the boundary. The construction, the isotopy and the crossing bijection use Lean's ordinary logical foundations. The count concerns the specified representatives. A minimum over all representatives of those isotopy classes requires a separate geometric argument. [Crossing bijection](CollarCrossings.lean) · [Integer coordinates and their order](CrossingOrder.lean) · [Examples](SurfaceExamples.lean)

| Declaration in `ShortTwists.Examples` | Conclusion |
| --- | --- |
| `fourteenStart`, `fourteenEnd` | Two essential embedded circles in the gluing quotient. |
| `end_vertex_is_twist` | The endpoint represents the once-twisted starting vertex. |
| `actualCrossings` | A bijection from `Fin 196` to all common points. |
| `signed_words_agree` | Sorting the geometric crossing coordinates reproduces all three sample one-turn words, including the full 196-entry word. This finite comparison uses the native evaluator. |

## Extremal examples with 40 and 132 crossings

Lean regenerates three signed words from six band widths and a cyclic shift, computes their polygonal faces and checks both distance budgets for each. It checks the three-crossing base case and the different signed intersection totals of the two six-distance examples. The declarations `five_of_geometry` and `six_of_geometry` transfer witness decisions to graph distance assuming the geometric interpretation described below. The global lower-bound census runs separately in C++. [Extremal examples](MinimumExamples.lean) · [Minimum-intersection proof](../paper/minimum-six.pdf) · [Census](../computations/minimum/)

## What still separates the computation from distance six?

In the formal graph, a vertex is an unoriented isotopy class of essential embedded circles. Adjacency means distinct classes have disjoint representatives. Exact distance six requires a six-edge walk and a lower bound on the length of **every** walk. The executable search reproduces a six-edge outcome on the diagram and rejects five. Lean proves its cache and early exit preserve the recursive predicate for every input. The question about a shortcut is whether that recursion examined enough geometric moves. [Curve graph](IsotopyGraph.lean) · [Walks and exact distance](CurveDistance.lean) · [Checker](FiniteDiagrams.lean)

The theorem `named_pair_six_of_geometry` takes a `GeometricSearch` on the gluing quotient and an interpretation of the given word as the named pair. From these premises it establishes exact distance for the two specific vertices. The structure has three local obligations. [Exact theorem](SurfaceExamples.lean) · [Definitions and transfer proof](SearchSemantics.lean)

1. Prove that the terminal diagram test detects exactly the pairs that are equal, adjacent, or admit a common neighbor. Lean proves the Euler-characteristic calculation for arbitrary complementary pieces with boundary. The geometric work is identifying those pieces from the diagram in minimal position and relating a complementary nondisk to an essential disjoint curve. [Euler calculation](FillingEuler.lean)
2. Realize every allowed first move as keeping the current vertex or moving to a disjoint one, with the stated child diagram for the next pair.
3. Prove that whenever a short geometric path exists for a nonterminal diagram, at least one of the bounded candidate routes preserves the remaining path budget. Birman, Margalit and Menasco supply the efficient-geodesic theorem used in the manuscript. A Lean proof must also track the coordinate bounds, the tightening of the diagram and the interpretation of each new pair. [Theorem 1.1 and Proposition 3.7](https://arxiv.org/pdf/1408.4133)

The project also lacks a formal homeomorphism from this particular quotient to the closed genus-two surface. The finite ribbon computation verifies 14 vertices, 28 edges and 12 disk-face cycles in the combinatorial description, giving Euler characteristic −2 there. Turning those cells into a surface classification theorem is a further obligation. For the all-powers result one must additionally formalize the annular projection estimate. [Sources and related Lean libraries](library-audit.md)

## The census and its scope

Lean verifies that six listed triangulation types cover the eligible labeled side pairings in disjoint orbits. It enumerates widths and boundary shifts, then checks the component and symmetry filters. At 12 crossings it obtains 348 canonical filling-diagram outputs and five that pass the distance-four test. At 13 the counts are 499 and eleven. All sixteen pass the one-twist distance-five test. The two finite generators also have coverage proofs for fixed-point-free involutions and lists of nonnegative widths of the specified length and sum. The surface theorem still needs the fact that every relevant geometric pair admits an enumerated presentation. [Census program](SmallCensus.lean) · [Coverage proofs](CensusCoverage.lean) · [Tests on the sixteen seeds](FiniteDiagrams.lean)

## Build and trust

Run these commands in the directory containing `lakefile.lean` and `lean-toolchain`. The cache command downloads precompiled mathlib dependencies. The build checks the local proof sources.

~~~sh
lake exe cache get
lake build
~~~

The toolchain and dependency revisions are pinned. Each principal module prints axiom dependencies. The geometric proofs and the correctness of the recursion use `propext`, `Quot.sound` and `Classical.choice`. Large concrete evaluations additionally use `Lean.ofReduceBool`. Explicit theorem parameters, including `GeometricSearch`, appear in theorem statements separately from these axiom reports. [Checked build output](build-audit.txt)
