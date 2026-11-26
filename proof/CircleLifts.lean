import IsotopyGraph

/-! A null-homotopic circle-valued map on a compact space admits a real lift.
Near any time in a homotopy, all pointwise differences avoid the antipode.
Using one branch of the circle coordinate there makes liftability locally constant. -/
namespace ShortTwists
noncomputable section
open Set Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

def RealLiftable (f : C(X,Turn)) : Prop :=
  ∃ g : C(X,ℝ), ∀ z, ((g z : ℝ) : Turn) = f z

private def antipode : Turn := ((1/2 : ℝ) : Turn)

private theorem zero_ne_antipode : (0:Turn) ≠ antipode := by
  intro e
  have h := (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1:ℝ))
    (by constructor <;> norm_num : (1/2:ℝ) ∈ Set.Ico 0 1)).mp e.symm
  norm_num at h

private theorem lifts_near {f g : C(X,Turn)} (H : f.Homotopy g) (t : unitInterval) :
    ∀ᶠ r in 𝓝 t, RealLiftable (H.toContinuousMap.curry r) ↔
      RealLiftable (H.toContinuousMap.curry t) := by
  let Δ : C(unitInterval × X,Turn) :=
    ⟨fun p => H p - H (t,p.2),H.continuous.sub
      (H.continuous.comp (continuous_const.prod_mk continuous_snd))⟩
  have hU : IsOpen {r : unitInterval | MapsTo (Δ.curry r) univ {antipode}ᶜ} :=
    (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ isClosed_singleton.isOpen_compl).preimage
      Δ.curry.continuous
  have ht : MapsTo (Δ.curry t) univ {antipode}ᶜ := by
    intro z _
    change H (t,z)-H (t,z) ≠ antipode
    simpa only [sub_self] using zero_ne_antipode
  filter_upwards [hU.mem_nhds ht] with r hr
  have havoid (z : X) : Δ.curry r z ≠ antipode := hr (Set.mem_univ z)
  let branch : C(X,ℝ) :=
    ⟨fun z => (AddCircle.equivIco (1:ℝ) (1/2) (Δ.curry r z)).val,
      continuous_iff_continuousAt.mpr (fun z => continuousAt_subtype_val.comp
        ((AddCircle.continuousAt_equivIco (1:ℝ) (1/2) (havoid z)).comp
          (Δ.curry r).continuous.continuousAt))⟩
  have hb (z : X) : ((branch z : ℝ) : Turn) = H (r,z)-H (t,z) :=
    (AddCircle.equivIco (1:ℝ) (1/2)).symm_apply_apply _
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨⟨fun z => a z-branch z,a.continuous.sub branch.continuous⟩,fun z => ?_⟩
    change (((a z-branch z:ℝ)):Turn) = H (t,z)
    rw [AddCircle.coe_sub,ha,hb]
    change H (r,z)-(H (r,z)-H (t,z)) = _
    abel
  · rintro ⟨b,hb'⟩
    refine ⟨⟨fun z => b z+branch z,b.continuous.add branch.continuous⟩,fun z => ?_⟩
    change (((b z+branch z:ℝ)):Turn) = H (r,z)
    rw [AddCircle.coe_add,hb',hb]
    change H (t,z)+(H (r,z)-H (t,z)) = _
    abel

theorem realLiftable_of_homotopic {f g : C(X,Turn)} (H : f.Homotopic g) (hg : RealLiftable g) :
    RealLiftable f := by
  obtain ⟨H⟩ := H
  let clim := fun t : unitInterval => H.toContinuousMap.curry t
  let S : Set unitInterval := {t | RealLiftable (clim t)}
  have ho : IsOpen S := isOpen_iff_mem_nhds.mpr (fun t ht =>
    (lifts_near H t).mono (fun _ close => close.mpr ht))
  have hc : IsOpen Sᶜ := isOpen_iff_mem_nhds.mpr (fun t ht =>
    (lifts_near H t).mono (fun _ close h => ht (close.mp h)))
  have eg : clim 1 = g := ContinuousMap.ext H.map_one_left
  have ef : clim 0 = f := ContinuousMap.ext H.map_zero_left
  have eq := (show IsClopen S from ⟨isOpen_compl_iff.mp hc,ho⟩).eq_univ
    ⟨1,show RealLiftable (clim 1) from eg.symm ▸ hg⟩
  have h0 : (0:unitInterval) ∈ S := eq.symm ▸ mem_univ _
  exact ef ▸ h0

theorem realLiftable_of_null {f : C(X,Turn)} {p : Turn}
    (h : f.Homotopic (ContinuousMap.const X p)) : RealLiftable f :=
  realLiftable_of_homotopic h ⟨ContinuousMap.const X ((AddCircle.equivIco (1:ℝ) 0 p).val),
    fun _ => (AddCircle.equivIco (1:ℝ) 0).symm_apply_apply p⟩

#print axioms realLiftable_of_null
end
end ShortTwists
