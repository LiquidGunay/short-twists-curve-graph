import CrossingOrder
import EssentialMarking
import SearchSemantics
import SmallCensus

/-! The geometric and finite results for the named diagrams.
The exact distance statement at the end explicitly takes the missing
surface-interpretation theorems as premises. -/
namespace ShortTwists.Examples
open Cylinder FiniteDiagrams

/-- Read the same crossing points in the two orders along the marked curves.
Each event is indexed by its physical slot on each side of the twist. -/
def oneTurnWord (s : Code) : Code := Id.run do
  let n := s.size
  let mut fixed : Array (Nat × Nat) := #[]
  let mut moving : Array (Nat × Nat) := #[]
  let mut sameSign := Array.mkArray (n*n) false
  for f in [:n] do
    let F := s[f]!
    for m in [:n] do
      let M := s[m]!
      let key := f*n+m
      let h := tick n f m (decide (0<M))
      let uf := (F.natAbs-1)*(4*n) + readTick n h (decide (0<F))
      let um := (M.natAbs-1)*(4*n) + readTick n h (decide (0<M))
      fixed := fixed.push (uf,key)
      moving := moving.push (um,key)
      sameSign := sameSign.set! key (decide (0<F) == decide (0<M))
  let mut labels := Array.mkArray (n*n) (0 : Int)
  let fixedOrder := fixed.qsort (fun a b => a.1 < b.1)
  for j in [:fixedOrder.size] do
    labels := labels.set! fixedOrder[j]!.2 (j+1 : Nat)
  return (moving.qsort (fun a b => a.1 < b.1)).map (fun e =>
    if sameSign[e.2]! then labels[e.2]! else -labels[e.2]!)

theorem signed_words_agree :
    oneTurnWord p12 = FiniteDiagrams.twist p12 1 ∧
    oneTurnWord p13 = FiniteDiagrams.twist p13 1 ∧
    oneTurnWord p14 = FiniteDiagrams.twist p14 1 := by native_decide

theorem census_counts :
    (Census.listed 12).length = 5 ∧ (Census.listed 13).length = 11 := by native_decide

theorem fourteen_ribbon_counts : p14.size = 14 ∧ (originalFaces p14).size = 12 := by native_decide

theorem fourteen_ribbon_euler :
    (p14.size : ℤ) - 2*(p14.size : ℤ) + ((originalFaces p14).size : ℤ) = -2 := by
  rw [fourteen_ribbon_counts.1,fourteen_ribbon_counts.2]
  norm_num

private def fourteenSlot (j : Fin p14.size) : Fin p14.size :=
  let slots := #[0,8,2,10,4,5,6,7,1,9,3,11,12,13]
  ⟨slots[j.val]! % p14.size,Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 8192 in
def fourteenTraversal : Traversal p14 where
  loc := fourteenSlot
  covers := by change ∀ y, ∃ x, fourteenSlot x=y; decide
  distinct := by change ∀ ⦃i j⦄, fourteenSlot i=fourteenSlot j → i=j; decide
  next := by unfold follows; decide
  onlyNext := by unfold follows; decide

theorem fourteen_total : algebraicTotal p14 = -6 := by decide

noncomputable section

/-- A bijection with the entire point set of the two specified representatives. -/
def fourteenCrossings : Fin 196 ≃
    ↥(trace p14 mid ∩ (Cylinder.twist p14 1 '' trace p14 pushOff)) :=
  finProdFinEquiv.symm.trans (surfaceCrossingEquiv p14)

private theorem total_ne : algebraicTotal p14 ≠ 0 := by rw [fourteen_total]; decide
private theorem mid_inside : (mid:ℝ) ∈ Set.Ioo 0 1 := by constructor <;> norm_num [mid]
private theorem offset_inside : (pushOff:ℝ) ∈ Set.Ioo 0 1 := by
  constructor <;> norm_num [pushOff,quarter]

def fourteenStart : EssentialLoop (Surface p14) :=
  essentialMarked fourteenTraversal (by decide) mid_inside total_ne
def fourteenPushOff : EssentialLoop (Surface p14) :=
  essentialMarked fourteenTraversal (by decide) offset_inside total_ne
def fourteenEnd : EssentialLoop (Surface p14) := pushLoop (Cylinder.twist p14 1) fourteenPushOff

theorem end_vertex_is_twist :
    vertex fourteenEnd = pushVertex (Cylinder.twist p14 1) (vertex fourteenStart) :=
  congrArg (pushVertex (Cylinder.twist p14 1))
    (vertex_offset_eq fourteenTraversal (by decide) offset_inside mid_inside total_ne)

theorem start_range : Set.range fourteenStart.param = trace p14 mid :=
  markedLoop_range fourteenTraversal (by decide) mid

theorem end_range : Set.range fourteenEnd.param = Cylinder.twist p14 1 '' trace p14 pushOff := by
  rw [← markedLoop_range fourteenTraversal (by decide) pushOff]
  exact Set.range_comp (Cylinder.twist p14 1) (markedLoop fourteenTraversal (by decide) pushOff)

/-- The two actual essential embedded circles have this many common points. -/
def actualCrossings : Fin 196 ≃
    ↥(Set.range fourteenStart.param ∩ Set.range fourteenEnd.param) := by
  rw [start_range,end_range]
  exact fourteenCrossings

/-- The intended distance statement on the marked quotient. Its identification
with the closed double torus is an additional topological obligation. -/
def MarkedDistanceClaim (s : Code) (k : ℤ) (d : ℕ) : Prop :=
  ∃ a : EssentialLoop (Surface s), Set.range a.param = trace s mid ∧
    CurveDistance.AtDistance Adjacent (vertex a) (pushVertex (Cylinder.twist s k) (vertex a)) d

theorem named_pair_six_of_geometry (G : GeometricSearch (Surface p14))
    (marked : G.represents (oneTurnWord p14) (vertex fourteenStart) (vertex fourteenEnd)) :
    CurveDistance.AtDistance Adjacent (vertex fourteenStart) (vertex fourteenEnd) 6 := by
  rw [signed_words_agree.2.2] at marked
  exact checked_distance G marked (by decide) fourteen_twist_distance_test

theorem fourteen_six_of_geometry (G : GeometricSearch (Surface p14))
    (marked : G.represents (oneTurnWord p14) (vertex fourteenStart) (vertex fourteenEnd)) :
    MarkedDistanceClaim p14 1 6 := by
  exact ⟨fourteenStart,start_range,end_vertex_is_twist ▸ named_pair_six_of_geometry G marked⟩

theorem twelve_double_of_geometry (G : GeometricSearch (Surface p12))
    (a : EssentialLoop (Surface p12)) (htrace : Set.range a.param = trace p12 mid)
    (marked : G.represents (FiniteDiagrams.twist p12 2) (vertex a)
      (pushVertex (Cylinder.twist p12 2) (vertex a))) :
    MarkedDistanceClaim p12 2 6 :=
  ⟨a,htrace,checked_distance G marked (by decide) twelve_double_distance_test⟩

#print axioms fourteenCrossings
#print axioms actualCrossings
#print axioms end_vertex_is_twist
#print axioms signed_words_agree
#print axioms fourteen_six_of_geometry
end
end ShortTwists.Examples
