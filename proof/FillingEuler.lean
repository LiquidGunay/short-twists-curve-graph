import SearchSemantics
import Mathlib.Tactic.Ring

/-! Euler-characteristic part of the two-edge test for a connected ribbon
neighborhood on the double torus. The hypotheses are the two geometric
cell-count identities, written separately so their precise use is visible. -/
namespace ShortTwists.Filling
open FiniteDiagrams

structure Piece where
  genus : ℕ
  boundary : ℕ
  meetsRibbon : 0 < boundary

def Piece.euler (p : Piece) : ℤ := 2-2*(p.genus : ℤ)-(p.boundary : ℤ)
def Piece.defect (p : Piece) : ℕ := p.genus+(p.boundary-1)
def Piece.diskData (p : Piece) : Prop := p.genus=0 ∧ p.boundary=1

theorem positive_defect (p : Piece) : 0<p.defect ↔ ¬ p.diskData := by
  have := p.meetsRibbon
  unfold Piece.defect Piece.diskData
  omega

theorem euler_sum (pieces : List Piece) :
    (pieces.map Piece.euler).sum =
      ((pieces.map Piece.boundary).sum : ℤ)-2*((pieces.map Piece.defect).sum : ℤ) := by
  induction pieces with
  | nil => rfl
  | cons p ps ih =>
    have hb := p.meetsRibbon
    simp only [List.map_cons,List.sum_cons,ih,Piece.euler,Piece.defect,Nat.cast_add,
      Nat.cast_sub (show 1 ≤ p.boundary by omega),Nat.cast_one]
    ring

theorem defect_some (ps : List Piece) :
    0 < (ps.map Piece.defect).sum ↔ ∃ p ∈ ps, ¬ p.diskData := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons,List.sum_cons,List.mem_cons]
    constructor
    · intro h
      by_cases hd : 0<p.defect
      · exact ⟨_,Or.inl rfl,(positive_defect p).mp hd⟩
      · obtain ⟨a,ha,nd⟩ := ih.mp (by omega)
        exact ⟨_,Or.inr ha,nd⟩
    · rintro ⟨a,eq|mem,h⟩
      · subst a; have := (positive_defect p).mpr h; omega
      · have := ih.mpr ⟨a,mem,h⟩; omega

/-- For a nonempty crossing word, one boundary circle per ribbon face and
additivity of Euler characteristic on a genus-two surface turn the Boolean
terminal test into the existence of a complementary piece with nondisk data. -/
theorem terminal_iff_complement {s : Code} (nonempty : s.isEmpty = false) (ps : List Piece)
    (boundaryCount : (ps.map Piece.boundary).sum = (originalFaces s).size)
    (surfaceEuler : -(s.size : ℤ) + (ps.map Piece.euler).sum = -2) :
    terminal s = true ↔ ∃ p ∈ ps, ¬ p.diskData := by
  rw [← defect_some]
  rw [euler_sum,boundaryCount] at surfaceEuler
  simp only [terminal,nonempty,Bool.false_or,decide_eq_true_eq]
  omega

#print axioms terminal_iff_complement
end ShortTwists.Filling
