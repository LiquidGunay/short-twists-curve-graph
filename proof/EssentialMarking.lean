import MarkedEmbeddings
import CircleLifts

/-! The physical height modulo one is well-defined on the glued cylinder.
Along each piece of the marked curve it winds once with the sign of that
piece. A real lift would force the sum of all these signed changes to vanish. -/
namespace ShortTwists.Cylinder
noncomputable section
open unitInterval
open scoped BigOperators

private theorem boundary_height {p : Annulus} (h : boundary p) : ((p.2 : ℝ) : Turn) = 0 := by
  rcases h with h|h <;> rw [h]
  · rfl
  · exact AddCircle.coe_period (1:ℝ)

def height (s : Array Int) : C(Surface s,Turn) := by
  let f : Annulus → Turn := fun p => ((p.2 : ℝ) : Turn)
  have glues : ∀ p q, Seam s p q → f p = f q := fun _ _ h =>
    (boundary_height (seam_boundary h).1).trans (boundary_height (seam_boundary h).2).symm
  exact ⟨Quot.lift f glues,continuous_quot_lift _
    ((AddCircle.continuous_mk' (1:ℝ)).comp (continuous_subtype_val.comp continuous_snd))⟩

def signWeight (s : Array Int) (i : Fin s.size) : ℤ := if positive s i then 1 else -1
def algebraicTotal (s : Array Int) : ℤ := ∑ i, signWeight s i

private theorem integer_fiber_constant (g : C(unitInterval,ℝ))
    (hg : ∀ t, ((g t : ℝ):Turn) = 0) : g 1 = g 0 := by
  have ints (t : unitInterval) : ∃ z : ℤ, (z:ℝ)=g t := by
    obtain ⟨z,h⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hg t)
    exact ⟨z,by simpa [zsmul_eq_mul] using h⟩
  let w := fun t => Classical.choose (ints t)
  have hw (t) : ((w t:ℤ):ℝ)=g t := Classical.choose_spec (ints t)
  have cw : Continuous w := Int.closedEmbedding_coe_real.toEmbedding.continuous_iff.mpr
    (show Continuous (fun t => ((w t:ℤ):ℝ)) from (funext hw).symm ▸ g.continuous)
  exact (hw 1).symm.trans ((congrArg (fun z : ℤ => (z:ℝ))
    (PreconnectedSpace.constant (by infer_instance) cw (x := 1) (y := 0))).trans (hw 0))

private theorem successor_eq_rotate {n : ℕ} (i : Fin n) : successor i = finRotate n i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨k,hk⟩ := i
    by_cases h : k<n
    · exact (show successor (⟨k,hk⟩ : Fin (n+1)) = ⟨k+1,Nat.succ_lt_succ h⟩ from
        dif_pos (Nat.succ_lt_succ h)).trans (finRotate_of_lt h).symm
    · have e : k=n := by omega
      subst k
      exact (show successor (⟨n,hk⟩ : Fin (n+1)) = ⟨0,Nat.zero_lt_succ _⟩ from
        dif_neg (Nat.lt_irrefl _)).trans finRotate_last'.symm

theorem zero_total_of_lift {s : Array Int} (T : Traversal s) (hn : 0<s.size) (u : unitInterval)
    (lift : RealLiftable ((height s).comp (markedLoop T hn u))) : algebraicTotal s = 0 := by
  obtain ⟨L,hL⟩ := lift
  let start := fun j : Fin s.size => L (slot s.size j 0)
  have step (j : Fin s.size) : start (successor j)-start j = (signWeight s (T.loc j):ℝ) := by
    let b := positive s (T.loc j)
    let gap : C(unitInterval,ℝ) := ⟨fun t => L (slot s.size j t)-(oriented b t:ℝ),
      (L.continuous.comp ((AddCircle.continuous_mk' (1:ℝ)).comp
        (((continuous_const (y := (j:ℝ))).add continuous_subtype_val).div_const (s.size:ℝ)))).sub
        (continuous_subtype_val.comp (continuous_oriented b))⟩
    have fixes (t : unitInterval) : ((gap t:ℝ):Turn) = 0 := by
      change (((L (slot s.size j t)-(oriented b t:ℝ)):ℝ):Turn) = 0
      rw [AddCircle.coe_sub, hL]
      change height s (markedLoop T hn u (slot s.size j t)) - _ = 0
      rw [loop_at_slot]
      exact sub_self _
    have same := integer_fiber_constant gap fixes
    change L (slot s.size j 1)-(oriented b 1:ℝ) = L (slot s.size j 0)-(oriented b 0:ℝ) at same
    rw [last_slot] at same
    cases hb : positive s (T.loc j) <;>
      simp [b,hb,start,signWeight,oriented] at same ⊢ <;> linarith
  have totals : ∑ j, (start (successor j)-start j) = ∑ j, (signWeight s (T.loc j):ℝ) :=
    Finset.sum_congr rfl (fun j _ => step j)
  simp only [Finset.sum_sub_distrib,successor_eq_rotate] at totals
  rw [(finRotate s.size).sum_comp Finset.univ start (by simp),sub_self] at totals
  let perm : Equiv.Perm (Fin s.size) := Equiv.ofBijective T.loc ⟨T.distinct,T.covers⟩
  have relabel := Equiv.Perm.sum_comp perm Finset.univ
    (fun j => (signWeight s j:ℝ)) (by simp)
  change (∑ j, (signWeight s (T.loc j):ℝ)) = _ at relabel
  have z := totals.trans relabel
  unfold algebraicTotal
  exact_mod_cast z.symm

def essentialMarked {s : Array Int} (T : Traversal s) (hn : 0<s.size) {u : unitInterval}
    (hu : (u:ℝ) ∈ Set.Ioo 0 1) (nonzero : algebraicTotal s ≠ 0) : EssentialLoop (Surface s) where
  param := markedLoop T hn u
  embedded := (markedLoop_closedEmbedding T hn hu).toEmbedding
  essential := by
    intro p null
    apply nonzero
    have H := null.hcomp (ContinuousMap.Homotopic.refl (height s))
    have eq : (height s).comp (ContinuousMap.const Turn p) = ContinuousMap.const Turn (height s p) :=
      ContinuousMap.ext (fun _ => rfl)
    rw [eq] at H
    exact zero_total_of_lift T hn u (realLiftable_of_null H)

theorem offsetPath_inside {u v : unitInterval} (hu : (u:ℝ) ∈ Set.Ioo 0 1)
    (hv : (v:ℝ) ∈ Set.Ioo 0 1) (t : unitInterval) :
    ((offsetPath u v t : unitInterval) : ℝ) ∈ Set.Ioo 0 1 := by
  rcases t.2.1.eq_or_lt with ht|ht
  · have eq : t=0 := Subtype.ext ht.symm
    simpa [eq] using hu
  · change 0 < (1-(t:ℝ))*u+t*v ∧ (1-(t:ℝ))*u+t*v < 1
    refine ⟨add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr t.2.2) hu.1.le)
      (mul_pos ht hv.1),?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr hu.2.le),
      mul_pos ht (sub_pos.mpr hv.2)]

theorem vertex_offset_eq {s : Array Int} (T : Traversal s) (hn : 0<s.size) {u v : unitInterval}
    (hu : (u:ℝ) ∈ Set.Ioo 0 1) (hv : (v:ℝ) ∈ Set.Ioo 0 1) (nonzero : algebraicTotal s ≠ 0) :
    vertex (essentialMarked T hn hu nonzero) = vertex (essentialMarked T hn hv nonzero) :=
  Quot.sound (.isotopy (offsetHomotopy T hn u v) (fun t =>
    (markedLoop_closedEmbedding T hn (offsetPath_inside hu hv t)).toEmbedding))

#print axioms zero_total_of_lift
#print axioms essentialMarked
#print axioms vertex_offset_eq
end
end ShortTwists.Cylinder
