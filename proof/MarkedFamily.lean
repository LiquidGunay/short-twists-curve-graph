import CollarCrossings

/-! The glued interior is an embedded open annulus. We also identify a cycle
of closed intervals with the usual real circle. This gives continuous circle
parametrizations of the marked traces, including the one used for the push-off. -/
namespace ShortTwists.Cylinder
noncomputable section
open unitInterval

abbrev Interior := {p : Annulus // ¬ boundary p}

theorem interior_open : IsOpen {p : Annulus | ¬ boundary p} := by
  have h : IsClosed {p : Annulus | boundary p} :=
    (isClosed_eq continuous_snd (continuous_const (y := (0 : unitInterval)))).union
      (isClosed_eq continuous_snd (continuous_const (y := (1 : unitInterval))))
  exact h.isOpen_compl

theorem open_collar (s : Array Int) :
    OpenEmbedding (fun p : Interior => project s p.val) := by
  apply openEmbedding_of_continuous_injective_open (continuous_quot_mk.comp continuous_subtype_val)
  · intro a b h
    exact Subtype.ext (same_as_interior s a.property h)
  · intro U hU
    apply (quotientMap_quot_mk.isOpen_preimage).mp
    have e : project s ⁻¹' ((fun p : Interior => project s p.val) '' U) = Subtype.val '' U := by
      ext p
      constructor
      · rintro ⟨q,hq,e⟩
        exact ⟨q,hq,same_as_interior s q.property e⟩
      · rintro ⟨q,hq,rfl⟩
        exact ⟨q,hq,rfl⟩
    change IsOpen (project s ⁻¹' ((fun p : Interior => project s p.val) '' U))
    rw [e]
    exact interior_open.openEmbedding_subtype_val.isOpenMap U hU

def core (s : Array Int) (x : Turn) : Surface s := project s (x,mid)

theorem core_embedding (s : Array Int) : Embedding (core s) := by
  have hmid : ¬ boundary ((0 : Turn), mid) := by
    change ¬ (mid = 0 ∨ mid = 1)
    rintro (e|e) <;> have h := congrArg Subtype.val e <;> norm_num [mid] at h
  let embed : Turn → Interior := fun x => ⟨(x,mid),hmid⟩
  have cout : Continuous embed := (continuous_id.prod_mk continuous_const).subtype_mk _
  have cin : Continuous (fun p : Interior => p.val.1) := continuous_fst.comp continuous_subtype_val
  exact (open_collar s).toEmbedding.comp ((show Function.LeftInverse
    (fun p : Interior => p.val.1) embed from fun _ => rfl).embedding cin cout)

def successor {n : ℕ} (j : Fin n) : Fin n :=
  if h : j.val+1<n then ⟨j.val+1,h⟩ else ⟨0,Nat.zero_lt_of_lt j.isLt⟩

inductive Join (n : ℕ) : (Fin n × unitInterval) → (Fin n × unitInterval) → Prop
  | next (j : Fin n) : Join n (j,1) (successor j,0)

abbrev Segments (n : ℕ) := Quot (Join n)

theorem last_slot {n : ℕ} (j : Fin n) : slot n j 1 = slot n (successor j) 0 := by
  unfold successor slot
  split
  · norm_num
  · rename_i hn
    have eq : j.val+1=n := by have := j.isLt; omega
    have jr : (j : ℝ)+1=n := by exact_mod_cast eq
    have nz : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt))
    simp [jr,nz,AddCircle.coe_period,QuotientAddGroup.mk_zero]

def segmentPoint (n : ℕ) : Segments n → Turn :=
  Quot.lift (fun p => slot n p.1 (p.2 : ℝ)) (by
    intro p q h
    cases h with | next j => exact last_slot j)

theorem continuous_segmentPoint (n : ℕ) : Continuous (segmentPoint n) := by
  apply continuous_quot_lift
  apply continuous_prod_of_discrete_left.mpr
  intro j
  change Continuous (fun t : unitInterval => (((((j:ℝ)+(t:ℝ))/n) : ℝ) : Turn))
  exact (AddCircle.continuous_mk' (1:ℝ)).comp
    (((continuous_const (y := (j:ℝ))).add continuous_subtype_val).div_const (n:ℝ))

private theorem normalize_segment {n : ℕ} (p : Segments n) :
    ∃ (j : Fin n) (t : unitInterval), (t : ℝ)<1 ∧ p = Quot.mk _ (j,t) := by
  induction p using Quot.inductionOn with
  | h p =>
    obtain ⟨j,t⟩ := p
    by_cases h : t=1
    · subst t
      exact ⟨_,0,zero_lt_one,Quot.sound (.next j)⟩
    · exact ⟨j,t,lt_of_le_of_ne t.2.2 (fun e => h (Subtype.ext e)),rfl⟩

theorem segmentPoint_injective (n : ℕ) : Function.Injective (segmentPoint n) := by
  intro a b e
  obtain ⟨j,t,ht,rfl⟩ := normalize_segment a
  obtain ⟨k,u,hu,rfl⟩ := normalize_segment b
  have hn : (0:ℝ)<n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have mem (i : Fin n) (z : unitInterval) (hz : (z : ℝ)<1) :
      ((i : ℝ)+z)/n ∈ Set.Ico 0 (0+1 : ℝ) := by
    have hi : (i : ℝ)+1≤n := by exact_mod_cast i.isLt
    exact ⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) z.2.1) hn.le,
      by rw [zero_add,div_lt_one hn]; linarith⟩
  have vals := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0)
    (mem j t ht) (mem k u hu)).mp e
  have sum : (j : ℝ)+t = (k : ℝ)+u := (div_left_inj' hn.ne').mp vals
  have eq : j=k := by
    rcases lt_trichotomy j k with lt|same|gt
    · have z : (j:ℝ)+1≤k := by exact_mod_cast lt
      linarith [u.2.1]
    · exact same
    · have z : (k:ℝ)+1≤j := by exact_mod_cast gt
      linarith [t.2.1]
  subst k
  have et : t=u := Subtype.ext (add_left_cancel sum)
  rw [et]

theorem segmentPoint_surjective {n : ℕ} (hn : 0<n) : Function.Surjective (segmentPoint n) := by
  intro θ
  let v : ℝ := n*(level θ : ℝ)
  have nz : (0:ℝ)<n := by exact_mod_cast hn
  have hv : 0≤v := mul_nonneg nz.le (level θ).2.1
  have vlt : v<n := by dsimp [v]; nlinarith [level_lt_one θ]
  let j : Fin n := ⟨⌊v⌋₊,(Nat.floor_lt hv).mpr vlt⟩
  let t : unitInterval := ⟨v-j,sub_nonneg.mpr (Nat.floor_le hv),
    by have := Nat.lt_floor_add_one v; change v-(⌊v⌋₊:ℝ) ≤ 1; linarith⟩
  refine ⟨Quot.mk _ (j,t),?_⟩
  change (((((j:ℝ)+(v-j))/n) : ℝ) : Turn) = θ
  rw [show ((j:ℝ)+(v-j))/n = (level θ : ℝ) by dsimp [v]; field_simp]
  exact level_coe θ

/-- Each of n successive intervals parametrizes one of the equal arcs of a circle. -/
def subdividedCircle {n : ℕ} (hn : 0<n) : Segments n ≃ₜ Turn :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (segmentPoint n) ⟨segmentPoint_injective n,segmentPoint_surjective hn⟩)
    (continuous_segmentPoint n)

/-- The location in the cylinder of each successive crossing along the first curve. -/
structure Traversal (s : Array Int) where
  loc : Fin s.size → Fin s.size
  covers : Function.Surjective loc
  distinct : Function.Injective loc
  next : ∀ j, follows s (loc j) (loc (successor j))
  onlyNext : ∀ j k, follows s (loc j) k → k = loc (successor j)

theorem continuous_oriented (b : Bool) : Continuous (oriented b) := by
  cases b
  · exact unitInterval.continuous_symm
  · exact continuous_id

private def strip (s : Array Int) (i : Fin s.size) :
    C(unitInterval × unitInterval, Surface s) where
  toFun p := project s (strand s i p.2 p.1)
  continuous_toFun := by
    apply continuous_quot_mk.comp
    apply Continuous.prod_mk _ ((continuous_oriented _).comp continuous_fst)
    exact (AddCircle.continuous_mk' (1:ℝ)).comp
      (((continuous_const (y := (i:ℝ))).add (continuous_subtype_val.comp
        ((continuous_oriented _).comp continuous_snd))).div_const (s.size:ℝ))

private def resolvedStrips {s : Array Int} (T : Traversal s) :
    C(Fin s.size × unitInterval, C(unitInterval,Surface s)) where
  toFun p := (strip s (T.loc p.1)).curry p.2
  continuous_toFun := continuous_prod_of_discrete_left.mpr
    (fun j => (strip s (T.loc j)).curry.continuous)

def familyOnSegments {s : Array Int} (T : Traversal s) :
    C(Segments s.size,C(unitInterval,Surface s)) := by
  have glue : ∀ p q, Join s.size p q → resolvedStrips T p = resolvedStrips T q := by
    intro p q rel
    cases rel with
    | next j =>
      exact ContinuousMap.ext (fun u => Quot.sound (.glue _ _ (T.next j) u))
  exact ⟨Quot.lift (resolvedStrips T) glue, continuous_quot_lift _ (resolvedStrips T).continuous⟩

theorem family_at_piece {s : Array Int} (T : Traversal s) (j : Fin s.size) (t u : unitInterval) :
    familyOnSegments T (Quot.mk _ (j,t)) u = project s (strand s (T.loc j) u t) := by
  simp [familyOnSegments,resolvedStrips,strip,Quot.lift_mk]

/-- Varying the transverse offset continuously gives all the marked traces. -/
def markedFamily {s : Array Int} (T : Traversal s) (hn : 0<s.size) :
    C(Turn × unitInterval,Surface s) :=
  ((familyOnSegments T).comp (subdividedCircle hn).symm.toContinuousMap).uncurry

def markedLoop {s : Array Int} (T : Traversal s) (hn : 0<s.size) (u : unitInterval) :
    C(Turn, Surface s) :=
  ⟨fun z => markedFamily T hn (z,u),(markedFamily T hn).continuous.comp
    (continuous_id.prod_mk continuous_const)⟩

theorem markedLoop_range {s : Array Int} (T : Traversal s) (hn : 0<s.size) (u : unitInterval) :
    Set.range (markedLoop T hn u) = trace s u := by
  ext q
  constructor
  · rintro ⟨z,rfl⟩
    obtain ⟨⟨j,t⟩,eq⟩ := Quot.exists_rep ((subdividedCircle hn).symm z)
    refine ⟨T.loc j,t,?_⟩
    change familyOnSegments T ((subdividedCircle hn).symm z) u = _
    rw [←eq]
    exact family_at_piece T j t u
  · rintro ⟨i,t,rfl⟩
    obtain ⟨j,rfl⟩ := T.covers i
    refine ⟨subdividedCircle hn (Quot.mk _ (j,t)),?_⟩
    change familyOnSegments T ((subdividedCircle hn).symm ((subdividedCircle hn) _)) u = _
    rw [Homeomorph.symm_apply_apply]
    exact family_at_piece T j t u

def offsetPath (u v : unitInterval) : Path u v where
  toFun t := ⟨(1-(t:ℝ))*u+t*v,
    add_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) u.2.1) (mul_nonneg t.2.1 v.2.1),
    by nlinarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr u.2.2),
                  mul_nonneg t.2.1 (sub_nonneg.mpr v.2.2)]⟩
  continuous_toFun := (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)).subtype_mk _
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

def offsetHomotopy {s : Array Int} (T : Traversal s) (hn : 0<s.size) (u v : unitInterval) :
    (markedLoop T hn u).Homotopy (markedLoop T hn v) := by
  let path := offsetPath u v
  exact {
    toFun := fun p => markedFamily T hn (p.2,path p.1)
    continuous_toFun := (markedFamily T hn).continuous.comp
      (continuous_snd.prod_mk (path.continuous.comp continuous_fst))
    map_zero_left := fun z => by change markedFamily T hn (z,path 0) = _; rw [path.source]; rfl
    map_one_left := fun z => by change markedFamily T hn (z,path 1) = _; rw [path.target]; rfl }

theorem offset_homotopy {s : Array Int} (T : Traversal s) (hn : 0<s.size) (u v : unitInterval) :
    (markedLoop T hn u).Homotopic (markedLoop T hn v) := ⟨offsetHomotopy T hn u v⟩

#print axioms core_embedding
#print axioms markedLoop_range
#print axioms offset_homotopy

end
end ShortTwists.Cylinder
