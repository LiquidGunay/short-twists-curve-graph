import IsotopyGraph
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! A signed permutation gives a square presentation of the marked surface:
take the cylinder about b, cut its circumference into n slots in order on b,
and glue exit to entrance in order on a. The same transverse parameter u is
used on both ends, reversed in a negatively oriented slot. -/
namespace ShortTwists.Cylinder
noncomputable section
open unitInterval

abbrev Annulus := Turn × unitInterval

def boundary (p : Annulus) : Prop := p.2 = 0 ∨ p.2 = 1

def slot (n j : ℕ) (u : ℝ) : Turn := (((j : ℝ) + u) / n : ℝ)

def oriented (positive : Bool) (t : unitInterval) : unitInterval :=
  if positive then t else σ t

def positive (s : Array Int) (j : Fin s.size) : Bool := decide (0 < s[j])

def strand (s : Array Int) (j : Fin s.size) (u t : unitInterval) : Annulus :=
  (slot s.size j (oriented (positive s j) u), oriented (positive s j) t)

def follows (s : Array Int) (j k : Fin s.size) : Prop :=
  s[k].natAbs = s[j].natAbs % s.size + 1

inductive Seam (s : Array Int) : Annulus → Annulus → Prop
  | glue (j k : Fin s.size) (next : follows s j k) (u : unitInterval) :
    Seam s (strand s j u 1) (strand s k u 0)

abbrev Surface (s : Array Int) := Quot (Seam s)
def project (s : Array Int) : Annulus → Surface s := Quot.mk _

theorem compact_surface (s : Array Int) : CompactSpace (Surface s) := inferInstance

theorem seam_boundary {s : Array Int} {p q : Annulus} (h : Seam s p q) :
    boundary p ∧ boundary q := by
  cases h with
  | glue j k _ u =>
    constructor
    · simp only [boundary, strand, oriented]
      split <;> simp
    · simp only [boundary, strand, oriented]
      split <;> simp

/-- Continuous integral shear on the actual real cylinder. -/
def shear (k : ℤ) (p : Annulus) : Annulus :=
  (p.1 + k • ((p.2 : ℝ) : Turn), p.2)

theorem continuous_shear (k : ℤ) : Continuous (shear k) := by
  have ha : Continuous (fun p : Annulus => ((p.2 : ℝ) : Turn)) :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_subtype_val.comp continuous_snd)
  exact (continuous_fst.add (ha.const_smul k)).prod_mk continuous_snd

theorem shear_boundary (k : ℤ) {p : Annulus} (h : boundary p) : shear k p = p := by
  rcases p with ⟨x,t⟩
  rcases h with h|h <;> change t = _ at h <;> subst t
  · simp [shear, QuotientAddGroup.mk_zero]
  · simp [shear, AddCircle.coe_period]

theorem shear_add (k l : ℤ) (p : Annulus) : shear k (shear l p) = shear (k+l) p := by
  simp [shear, add_zsmul, add_assoc, add_comm, add_left_comm]

@[simp] theorem shear_zero (p : Annulus) : shear 0 p = p := by simp [shear]

def onSurface (s : Array Int) (k : ℤ) : Surface s → Surface s :=
  Quot.lift (fun p => project s (shear k p)) (by
    intro p q h
    change project s (shear k p) = project s (shear k q)
    rw [shear_boundary k (seam_boundary h).1, shear_boundary k (seam_boundary h).2]
    exact Quot.sound h)

theorem continuous_onSurface (s : Array Int) (k : ℤ) : Continuous (onSurface s k) :=
  continuous_quot_lift _ (continuous_quot_mk.comp (continuous_shear k))

@[simp] theorem on_project (s : Array Int) (k : ℤ) (p : Annulus) :
    onSurface s k (project s p) = project s (shear k p) := rfl

theorem onSurface_add (s : Array Int) (k l : ℤ) (q : Surface s) :
    onSurface s k (onSurface s l q) = onSurface s (k+l) q := by
  induction q using Quot.inductionOn with
  | h p => exact congrArg (project s) (shear_add k l p)

@[simp] theorem onSurface_zero (s : Array Int) (q : Surface s) : onSurface s 0 q = q := by
  induction q using Quot.inductionOn with
  | h p => exact congrArg (project s) (shear_zero p)

/-- A full turn is the shear (x,t) ↦ (x+t,t); its inverse is the opposite shear. -/
def twist (s : Array Int) (k : ℤ) : Surface s ≃ₜ Surface s where
  toFun := onSurface s k
  invFun := onSurface s (-k)
  left_inv q := by rw [onSurface_add]; simp
  right_inv q := by rw [onSurface_add]; simp
  continuous_toFun := continuous_onSurface s k
  continuous_invFun := continuous_onSurface s (-k)

def interiorPoint (s : Array Int) : Surface s → Option Annulus := by
  classical
  refine Quot.lift (fun p => if boundary p then none else some p) ?_
  intro p q h
  simp [(seam_boundary h).1, (seam_boundary h).2]

/-- An interior point keeps its original coordinates under all boundary identifications. -/
theorem same_as_interior (s : Array Int) {p q : Annulus} (hp : ¬ boundary p)
    (eq : project s p = project s q) : p = q := by
  classical
  have h := congrArg (interiorPoint s) eq
  change (if boundary p then none else some p) = (if boundary q then none else some q) at h
  by_cases hq : boundary q <;> simp_all

def trace (s : Array Int) (u : unitInterval) : Set (Surface s) :=
  {q | ∃ (j : Fin s.size) (t : unitInterval), q = project s (strand s j u t)}

theorem twist_preserves_distance (s : Array Int) (k : ℤ) {a b : Vertex (Surface s)} {n : ℕ}
    (h : CurveDistance.AtDistance Adjacent a b n) :
    CurveDistance.AtDistance Adjacent (pushVertex (twist s k) a) (pushVertex (twist s k) b) n :=
  push_exact (twist s k) h

#print axioms twist_preserves_distance
end
end ShortTwists.Cylinder
