import MarkedFamily

/-! Closed subsets of a parametrized trace can be recognized before gluing.
This proves that the whole curve is embedded, including at seam crossings. -/
namespace ShortTwists.Cylinder
noncomputable section
open unitInterval

private theorem isolated_slot {n : ℕ} {i j : Fin n} {x y : unitInterval}
    (hx : (x:ℝ) ∈ Set.Ioo 0 1) (e : slot n i x = slot n j y) : i=j ∧ x=y := by
  have angles := congrArg (fun a : Turn => n • a) e
  simp only [smul_slot] at angles
  have xnz : ((x:ℝ):Turn) ≠ 0 := fun h => hx.1.ne'
    ((AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hx.1.le,hx.2⟩).mp h)
  have ylo : 0 < (y:ℝ) := lt_of_le_of_ne y.2.1 (by
    intro h; apply xnz; rw [angles,←h]; rfl)
  have yhi : (y:ℝ)<1 := lt_of_le_of_ne y.2.2 (by
    intro h; apply xnz; rw [angles,h]; exact AddCircle.coe_period (1:ℝ))
  refine ⟨slot_unique hx ⟨ylo,yhi⟩ e,Subtype.ext ?_⟩
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := 0)
    ⟨hx.1.le,by simpa only [zero_add] using hx.2⟩
    ⟨ylo.le,by simpa only [zero_add] using yhi⟩).mp angles

private theorem raw_strand_unique {s : Array Int} {i j : Fin s.size} {u v t w : unitInterval}
    (hu : (u:ℝ) ∈ Set.Ioo 0 1) (e : strand s i u t = strand s j v w) :
    i=j ∧ u=v ∧ t=w := by
  obtain ⟨rfl,off⟩ := isolated_slot (oriented_inside _ u hu) (congrArg Prod.fst e)
  have inj : Function.Injective (oriented (positive s i)) :=
    (show Function.LeftInverse (oriented (positive s i)) (oriented (positive s i)) from
      oriented_twice _).injective
  exact ⟨rfl,inj off,inj (congrArg Prod.snd e)⟩

private def raw {s : Array Int} (T : Traversal s) (u : unitInterval) (K : Set Turn)
    (p : Annulus) : Prop :=
  ∃ (j : Fin s.size) (t : unitInterval), strand s (T.loc j) u t = p ∧ slot s.size j t ∈ K

private theorem read_raw {s : Array Int} (T : Traversal s) {u : unitInterval}
    (hu : (u:ℝ) ∈ Set.Ioo 0 1) (K : Set Turn) (j : Fin s.size) (v t : unitInterval) :
    raw T u K (strand s (T.loc j) v t) ↔ u=v ∧ slot s.size j t ∈ K := by
  constructor
  · rintro ⟨l,w,h,ink⟩
    obtain ⟨eq,uv,rfl⟩ := raw_strand_unique hu h
    obtain rfl := T.distinct eq
    exact ⟨uv,ink⟩
  · rintro ⟨rfl,h⟩
    exact ⟨j,t,rfl,h⟩

private def traceMarker {s : Array Int} (T : Traversal s) {u : unitInterval}
    (hu : (u:ℝ) ∈ Set.Ioo 0 1) (K : Set Turn) : Surface s → Prop :=
  Quot.lift (raw T u K) (by
    intro p q h
    cases h with
    | glue i k next v =>
      obtain ⟨j,rfl⟩ := T.covers i
      have eq := T.onlyNext j k next
      subst k
      apply propext
      rw [read_raw T hu K,read_raw T hu K]
      exact and_congr_right (fun _ => by
        change slot s.size j 1 ∈ K ↔ slot s.size (successor j) 0 ∈ K
        rw [last_slot]))

theorem loop_at_slot {s : Array Int} (T : Traversal s) (hn : 0<s.size)
    (j : Fin s.size) (t u : unitInterval) :
    markedLoop T hn u (slot s.size j t) = project s (strand s (T.loc j) u t) := by
  change familyOnSegments T ((subdividedCircle hn).symm
    (subdividedCircle hn (Quot.mk _ (j,t)))) u = _
  rw [Homeomorph.symm_apply_apply]
  exact family_at_piece _ _ _ _

private theorem marker_on_loop {s : Array Int} (T : Traversal s) (hn : 0<s.size)
    {u : unitInterval} (hu : (u:ℝ) ∈ Set.Ioo 0 1) (K : Set Turn) (z : Turn) :
    traceMarker T hu K (markedLoop T hn u z) ↔ z∈K := by
  obtain ⟨l,rfl⟩ := segmentPoint_surjective hn z
  induction l using Quot.inductionOn with
  | h p =>
    obtain ⟨j,t⟩ := p
    change traceMarker T hu K (markedLoop T hn u (slot s.size j t)) ↔ _
    rw [loop_at_slot]
    exact (read_raw T hu K j u t).trans (and_iff_right rfl)

private theorem preimage_loop_image {s : Array Int} (T : Traversal s) (hn : 0<s.size)
    {u : unitInterval} (hu : (u:ℝ) ∈ Set.Ioo 0 1) (K : Set Turn) :
    project s ⁻¹' ((markedLoop T hn u) '' K) = {p | raw T u K p} := by
  ext p
  constructor
  · rintro ⟨z,hz,h⟩
    have pass := (marker_on_loop T hn hu K z).mpr hz
    rw [h] at pass
    exact pass
  · rintro ⟨j,t,rfl,h⟩
    exact ⟨_,h,loop_at_slot T hn j t u⟩

/-- A closed subset of the trace lifts to a compact collection of segments
in the Hausdorff cylinder, hence its image in the surface quotient is closed. -/
theorem markedLoop_closedEmbedding {s : Array Int} (T : Traversal s) (hn : 0<s.size)
    {u : unitInterval} (hu : (u:ℝ) ∈ Set.Ioo 0 1) : ClosedEmbedding (markedLoop T hn u) := by
  apply closedEmbedding_of_continuous_injective_closed (markedLoop T hn u).continuous
  · intro a b h
    have member := (marker_on_loop T hn hu {a} a).mpr rfl
    rw [h] at member
    exact ((marker_on_loop T hn hu {a} b).mp member).symm
  · intro K hK
    apply quotientMap_quot_mk.isClosed_preimage.mp
    change IsClosed (project s ⁻¹' ((markedLoop T hn u) '' K))
    rw [preimage_loop_image T hn hu]
    let lift : Fin s.size × unitInterval → Annulus := fun p => strand s (T.loc p.1) u p.2
    let angle : Fin s.size × unitInterval → Turn := fun p => slot s.size p.1 p.2
    have hc : Continuous lift := by
      apply continuous_prod_of_discrete_left.mpr
      intro j
      exact (continuous_const (y := strandX s u (T.loc j))).prod_mk
        (continuous_oriented (positive s (T.loc j)))
    have ha : Continuous angle := (continuous_segmentPoint s.size).comp continuous_quot_mk
    have eq : {p | raw T u K p} = lift '' (angle ⁻¹' K) := by
      ext p
      constructor
      · rintro ⟨j,t,h,ink⟩; exact ⟨(j,t),ink,h⟩
      · rintro ⟨⟨j,t⟩,ink,h⟩; exact ⟨j,t,h,ink⟩
    rw [eq]
    exact ((hK.preimage ha).isCompact.image hc).isClosed

#print axioms markedLoop_closedEmbedding
end
end ShortTwists.Cylinder
