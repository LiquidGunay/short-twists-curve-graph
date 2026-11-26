import MarkedCylinder
import Mathlib.Data.Fintype.Card

/-! Actual point intersections of a transverse representative with a once-sheared
parallel copy in the quotient surface. All identifications of seam points are
included. The count is a count of these representatives. -/
namespace ShortTwists.Cylinder
noncomputable section
open unitInterval
variable {ι κ : Type*}

def inside (t : unitInterval) : Prop := t ≠ 0 ∧ t ≠ 1

def openStrands (s : Array Int) (x : ι → Turn) : Set (Surface s) :=
  {q | ∃ i t, inside t ∧ project s (x i, t) = q}

def level (θ : Turn) : unitInterval :=
  let r := AddCircle.equivIco (1 : ℝ) 0 θ
  ⟨r.1, r.2.1, by simpa only [zero_add] using r.2.2.le⟩

theorem level_coe (θ : Turn) : ((level θ : ℝ) : Turn) = θ :=
  (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply θ

theorem level_lt_one (θ : Turn) : (level θ : ℝ) < 1 := by
  simpa only [zero_add] using ((AddCircle.equivIco (1 : ℝ) 0 θ).2.2)

theorem level_inside {θ : Turn} (h : θ ≠ 0) : inside (level θ) := by
  constructor
  · intro z
    apply h
    rw [← level_coe θ, z]
    rfl
  · intro z
    have lt := level_lt_one θ
    rw [z] at lt
    exact (lt_irrefl (1 : ℝ)) lt

theorem level_unique {t : unitInterval} (ht : inside t) (θ : Turn)
    (h : ((t : ℝ) : Turn) = θ) : t = level θ := by
  have tl : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun h => ht.2 (Subtype.ext h))
  apply Subtype.ext
  apply (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
    (x := (t : ℝ)) (y := (level θ : ℝ))
    ⟨t.2.1, by simpa only [zero_add] using tl⟩
    ⟨(level θ).2.1, by simpa only [zero_add] using level_lt_one θ⟩).mp
  exact h.trans (level_coe θ).symm

abbrev OpenCrossings (s : Array Int) (x : ι → Turn) (y : κ → Turn) :=
  ↥(openStrands s x ∩ (twist s 1 '' openStrands s y))

def crossingPoint (s : Array Int) (x : ι → Turn) (y : κ → Turn)
    (apart : ∀ i j, x i ≠ y j) (p : ι × κ) : OpenCrossings s x y := by
  let t := level (x p.1 - y p.2)
  have ht : inside t := level_inside (sub_ne_zero.mpr (apart _ _))
  refine ⟨project s (x p.1,t), ⟨p.1,t,ht,rfl⟩,
    project s (y p.2,t), ⟨p.2,t,ht,rfl⟩, ?_⟩
  change project s (shear 1 (y p.2,t)) = project s (x p.1,t)
  apply congrArg (fun z : Turn => project s (z,t))
  simp [t, level_coe]

/-- Each ordered pair of vertical strands contributes exactly one interior point. -/
def oneTurnEquiv (s : Array Int) (x : ι → Turn) (y : κ → Turn)
    (hx : Function.Injective x) (hy : Function.Injective y) (apart : ∀ i j, x i ≠ y j) :
    (ι × κ) ≃ OpenCrossings s x y := by
  apply Equiv.ofBijective (crossingPoint s x y apart)
  constructor
  · intro a b he
    have he' := congrArg Subtype.val he
    change project s (x a.1, level (x a.1 - y a.2)) =
      project s (x b.1, level (x b.1 - y b.2)) at he'
    have ht := level_inside (sub_ne_zero.mpr (apart a.1 a.2))
    have hcoords := same_as_interior s (p := (x a.1, level (x a.1 - y a.2)))
      (not_or_intro ht.1 ht.2) he'
    have hxi : x a.1 = x b.1 := congrArg Prod.fst hcoords
    have hh := congrArg (fun p : Annulus => ((p.2 : ℝ) : Turn)) hcoords
    change (((level (x a.1 - y a.2) : ℝ) : Turn)) =
      (((level (x b.1 - y b.2) : ℝ) : Turn)) at hh
    rw [level_coe,level_coe,hxi] at hh
    exact Prod.ext (hx hxi) (hy (sub_right_injective hh))
  · rintro ⟨q, ⟨i,t,ht,hit⟩, r, ⟨j,u,hu,rhit⟩, image⟩
    subst q
    subst r
    change project s (shear 1 (y j,u)) = project s (x i,t) at image
    have coords := same_as_interior s (p := (x i,t)) (not_or_intro ht.1 ht.2) image.symm
    have tu : t = u := congrArg Prod.snd coords
    subst u
    have xx : x i = y j + ((t : ℝ) : Turn) := by
      simpa [shear] using congrArg Prod.fst coords
    have yy : ((t : ℝ) : Turn) = x i - y j := by rw [xx]; abel
    have he := level_unique ht _ yy
    exact ⟨(i,j), Subtype.ext (congrArg (fun v => project s (x i,v)) he.symm)⟩

def mid : unitInterval := ⟨1/2, by constructor <;> norm_num⟩
def quarter : unitInterval := ⟨1/4, by constructor <;> norm_num⟩
def pushOff : unitInterval := σ quarter

def strandX (s : Array Int) (u : unitInterval) (j : Fin s.size) : Turn :=
  slot s.size j (oriented (positive s j) u)

theorem oriented_twice (b : Bool) (t : unitInterval) : oriented b (oriented b t) = t := by
  cases b <;> simp [oriented]

theorem oriented_mid (b : Bool) : oriented b mid = mid := by
  cases b <;> apply Subtype.ext <;> norm_num [oriented,mid]

private theorem nat_cast_turn (j : ℕ) : ((j : ℝ) : Turn) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨(j : ℤ),by simp [zsmul_eq_mul]⟩

theorem smul_slot {n : ℕ} (j : Fin n) (u : ℝ) : n • slot n j u = (u : Turn) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt))
  rw [slot, ← AddCircle.coe_nsmul (1:ℝ), nsmul_eq_mul]
  have eq : (n : ℝ) * ((j + u) / n) = j + u := by field_simp
  rw [eq, AddCircle.coe_add, nat_cast_turn, zero_add]

private theorem oriented_grid (b : Bool) (u : unitInterval) :
    (2 : ℕ) • (((oriented b u : unitInterval) : ℝ) : Turn) = 0 ↔
      (2 : ℕ) • ((u : ℝ) : Turn) = 0 := by
  cases b
  · simp only [oriented, Bool.false_eq_true, ↓reduceIte, coe_symm_eq,
      AddCircle.coe_sub, AddCircle.coe_period, zero_sub, smul_neg, neg_eq_zero]
  · rfl

/-- A seam-invariant parity test separates the old verticals from their push-off. -/
def gridMarker (s : Array Int) : Surface s → Prop :=
  Quot.lift (fun p : Annulus => (2 : ℕ) • (s.size • p.1) = 0) (by
    intro p q h
    cases h with
    | glue j k _ u =>
      change ((2 : ℕ) • (s.size • slot s.size j _) = 0) =
        ((2 : ℕ) • (s.size • slot s.size k _) = 0)
      rw [smul_slot,smul_slot]
      exact propext ((oriented_grid _ _).trans (oriented_grid _ _).symm))

theorem marker_on_strand (s : Array Int) (j : Fin s.size) (u t : unitInterval) :
    gridMarker s (project s (strand s j u t)) ↔ (2 : ℕ) • ((u : ℝ) : Turn) = 0 := by
  change (2 : ℕ) • (s.size • slot s.size j _) = 0 ↔ _
  rw [smul_slot, oriented_grid]

private theorem mid_on_grid : (2 : ℕ) • ((mid : ℝ) : Turn) = 0 := by
  rw [← AddCircle.coe_nsmul (1:ℝ), nsmul_eq_mul]
  change (((2 * (1/2) : ℝ) : Turn)) = 0
  rw [show (2 * (1/2) : ℝ) = 1 by norm_num]
  exact AddCircle.coe_period (1 : ℝ)

private theorem quarter_off_grid : (2 : ℕ) • ((quarter : ℝ) : Turn) ≠ 0 := by
  rw [← AddCircle.coe_nsmul (1:ℝ), nsmul_eq_mul]
  change (((2 * (1/4) : ℝ) : Turn)) ≠ 0
  intro h
  have ha : (2 * (1/4) : ℝ) ∈ Set.Ico 0 1 := by constructor <;> norm_num
  have hr := (AddCircle.coe_eq_zero_iff_of_mem_Ico ha).mp h
  norm_num at hr

private theorem pushOff_off_grid : (2 : ℕ) • ((pushOff : ℝ) : Turn) ≠ 0 :=
  fun h => quarter_off_grid ((oriented_grid false quarter).mp h)

theorem slot_unique {n : ℕ} {i j : Fin n} {u v : ℝ}
    (hu : u ∈ Set.Ioo 0 1) (hv : v ∈ Set.Ioo 0 1)
    (h : slot n i u = slot n j v) : i = j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have within (k : Fin n) {z : ℝ} (hz : z ∈ Set.Ioo 0 1) :
      ((k : ℝ) + z) / n ∈ Set.Ico 0 (0 + (1 : ℝ)) := by
    have hk : (k : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
    obtain ⟨hz0,hz1⟩ := hz
    exact ⟨div_nonneg (by positivity) hn.le,(div_lt_iff hn).mpr (by linarith)⟩
  have e := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0)
    (within i hu) (within j hv)).mp h
  have vEq : (i : ℝ) + u = (j : ℝ) + v := (div_left_inj' hn.ne').mp e
  obtain ⟨hu0,hu1⟩ := hu
  obtain ⟨hv0,hv1⟩ := hv
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with lt|eq|lt
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast lt
    linarith
  · exact eq
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast lt
    linarith

theorem oriented_inside (b : Bool) (u : unitInterval) (hu : (u:ℝ) ∈ Set.Ioo 0 1) :
    ((oriented b u : unitInterval) : ℝ) ∈ Set.Ioo 0 1 := by
  obtain ⟨h0,h1⟩ := hu
  cases b
  · change 0 < 1 - (u:ℝ) ∧ 1 - (u:ℝ) < 1
    constructor <;> linarith
  · exact ⟨h0,h1⟩

private theorem strandX_injective (s : Array Int) (u : unitInterval)
    (hu : (u:ℝ) ∈ Set.Ioo 0 1) : Function.Injective (strandX s u) :=
  fun _ _ h => slot_unique (oriented_inside _ _ hu) (oriented_inside _ _ hu) h

private theorem strands_apart (s : Array Int) (i j : Fin s.size) :
    strandX s mid i ≠ strandX s pushOff j := by
  intro eq
  have h := (marker_on_strand s i mid 0).mpr mid_on_grid
  change (2 : ℕ) • (s.size • strandX s mid i) = 0 at h
  rw [eq] at h
  exact pushOff_off_grid ((marker_on_strand s j pushOff 0).mp h)

private theorem vertical_in_trace (s : Array Int) (u : unitInterval) (i : Fin s.size) (t : unitInterval) :
    project s (strandX s u i,t) ∈ trace s u := by
  refine ⟨i,oriented (positive s i) t,?_⟩
  simp [strandX,strand,oriented_twice]

theorem crossings_in_interior (s : Array Int) :
    trace s mid ∩ (twist s 1 '' trace s pushOff) =
    openStrands s (strandX s mid) ∩ (twist s 1 '' openStrands s (strandX s pushOff)) := by
  ext q
  constructor
  · rintro ⟨⟨i,t,eq⟩,r,⟨j,u,eq'⟩,hit⟩
    subst q
    subst r
    let p := strand s i mid t
    let v := strand s j pushOff u
    change project s (shear 1 v) = project s p at hit
    have hv : ¬ boundary v := by
      intro hb
      rw [shear_boundary 1 hb] at hit
      have mark : gridMarker s (project s v) := hit.symm ▸ (marker_on_strand s i mid t).mpr mid_on_grid
      exact pushOff_off_grid ((marker_on_strand s j pushOff u).mp mark)
    have coords := same_as_interior s (p := shear 1 v) (q := p) hv hit
    have hvi : inside v.2 := ⟨fun a => hv (Or.inl a),fun a => hv (Or.inr a)⟩
    have hpi : inside p.2 := (congrArg Prod.snd coords) ▸ hvi
    exact ⟨⟨i,p.2,hpi,rfl⟩,project s v,⟨j,v.2,hvi,rfl⟩,hit⟩
  · rintro ⟨⟨i,t,_,rfl⟩,r,⟨j,u,_,rfl⟩,hit⟩
    exact ⟨vertical_in_trace s mid i t,_,vertical_in_trace s pushOff j u,hit⟩

/-- Every crossing on the glued surface is accounted for, including all possibilities
at identified boundary points. The two representatives have exactly n² intersection points. -/
def surfaceCrossingEquiv (s : Array Int) : (Fin s.size × Fin s.size) ≃
    ↥(trace s mid ∩ (twist s 1 '' trace s pushOff)) := by
  rw [crossings_in_interior]
  apply oneTurnEquiv
  · exact strandX_injective _ _ (by constructor <;> norm_num [mid])
  · exact strandX_injective _ _ (by constructor <;> norm_num [pushOff,quarter])
  · exact strands_apart s

#print axioms surfaceCrossingEquiv

end
end ShortTwists.Cylinder
