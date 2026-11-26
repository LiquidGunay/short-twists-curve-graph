import SmallCensus
import SearchSemantics

/-! Finite checks for the extremal examples on the closed double torus.
Each word is constructed from six band widths and a boundary gluing shift.
The global lower bounds are proved by the separate exhaustive census. -/
namespace ShortTwists.Minimum
open FiniteDiagrams ShortTwists.Census

def exampleWord (n : Nat) (widths : List Nat) (shift : Nat) : Code :=
  let m := shapes[2]!
  let boundary := circles m
  let pieces := ends m widths
  let top := boundary[0]!.foldl (fun (a : Array Nat) d => a ++ pieces[d]!) #[]
  let bottom := (boundary[1]!.foldl (fun (a : Array Nat) d => a ++ pieces[d]!) #[]).reverse
  (circuit n shift top bottom).getD #[]

def exampleFive := exampleWord 40 [2,11,7,7,2,11] 4
def exampleSix := exampleWord 132 [30,30,6,6,30,30] 13
def otherSix := exampleWord 132 [29,30,7,7,30,29] 13

def signedTotal (word : Code) : Int :=
  word.foldl (fun total label => total + (if label > 0 then 1 else -1)) 0

/-- Start the second traversal at label 1. Its remaining labels are 2,3 or 3,2.
All sixteen signed three-crossing words have three ribbon boundary cycles. -/
theorem three_crossing_faces : ∀ (reverse a b c : Bool),
    let second : Int := if reverse then 3 else 2
    let third : Int := if reverse then 2 else 3
    (originalFaces #[if a then (1 : Int) else -1,
                     if b then second else -second,
                     if c then third else -third]).size = 3 := by native_decide

theorem five_diagram :
    exampleFive.size = 40 ∧ faceProfile exampleFive = (38,34,4) ∧
    exactTest exampleFive 5 = true := by native_decide

theorem six_diagram :
    exampleSix.size = 132 ∧ faceProfile exampleSix = (130,126,4) ∧
    exactTest exampleSix 6 = true := by native_decide

theorem other_six_diagram :
    otherSix.size = 132 ∧ faceProfile otherSix = (130,126,4) ∧
    exactTest otherSix 6 = true := by native_decide

theorem differing_algebraic_counts :
    (signedTotal exampleSix).natAbs = 96 ∧ (signedTotal otherSix).natAbs = 48 := by
  native_decide

variable {X : Type*} [TopologicalSpace X]

theorem five_of_geometry (G : GeometricSearch X) {a b : Vertex X}
    (h : G.represents exampleFive a b) : CurveDistance.AtDistance Adjacent a b 5 :=
  checked_distance G h (by decide) five_diagram.2.2

theorem six_of_geometry (G : GeometricSearch X) {a b : Vertex X}
    (h : G.represents exampleSix a b) : CurveDistance.AtDistance Adjacent a b 6 :=
  checked_distance G h (by decide) six_diagram.2.2

#print axioms three_crossing_faces
#print axioms five_diagram
#print axioms six_diagram
#print axioms other_six_diagram
#print axioms differing_algebraic_counts
#print axioms six_of_geometry
end ShortTwists.Minimum
