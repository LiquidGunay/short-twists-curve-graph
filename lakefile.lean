import Lake
open Lake DSL

package shortTwists

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.8.0"

@[default_target]
lean_lib ShortTwists where
  srcDir := "proof"
  roots := #[`CurveDistance, `FiniteDiagrams, `IsotopyGraph, `MarkedCylinder,
    `CollarCrossings, `CrossingOrder, `MarkedFamily, `MarkedEmbeddings, `CircleLifts,
    `EssentialMarking, `SearchSemantics, `FillingEuler, `SmallCensus, `CensusCoverage, `SurfaceExamples]
