import CurveDistance
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Instances.AddCircle

/-! The topological graph. Vertices are unoriented isotopy classes of essential
embedded circles. An isotopy is a jointly continuous family of embeddings.
Quotienting also by all homeomorphic reparametrizations forgets the parametrization. -/
namespace ShortTwists

noncomputable section

abbrev Turn := AddCircle (1 : ℝ)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[ext] structure EssentialLoop (X : Type*) [TopologicalSpace X] where
  param : C(Turn, X)
  embedded : Embedding param
  essential : ∀ p : X, ¬ param.Homotopic (ContinuousMap.const Turn p)

inductive ReparamOrIsotopy : EssentialLoop X → EssentialLoop X → Prop
  | isotopy {a b} (H : a.param.Homotopy b.param)
      (throughEmbeddings : ∀ t : unitInterval, Embedding (fun z : Turn => H (t,z))) :
      ReparamOrIsotopy a b
  | reparam {a b} (e : Turn ≃ₜ Turn) (h : ∀ z, a.param z = b.param (e z)) :
      ReparamOrIsotopy a b

abbrev Vertex (X : Type*) [TopologicalSpace X] := Quot (@ReparamOrIsotopy X _)

def vertex (a : EssentialLoop X) : Vertex X := Quot.mk _ a

def Adjacent (u v : Vertex X) : Prop :=
  u ≠ v ∧ ∃ a b : EssentialLoop X, vertex a = u ∧ vertex b = v ∧
    ∀ s t : Turn, a.param s ≠ b.param t

theorem adjacent_symm {u v : Vertex X} (h : Adjacent u v) : Adjacent v u := by
  obtain ⟨hne,a,b,ha,hb,h⟩ := h
  exact ⟨hne.symm,b,a,hb,ha,fun s t => (h t s).symm⟩

def pushLoop (e : X ≃ₜ Y) (a : EssentialLoop X) : EssentialLoop Y where
  param := ⟨fun z => e (a.param z), e.continuous.comp a.param.continuous⟩
  embedded := e.embedding.comp a.embedded
  essential := by
    intro p h
    obtain ⟨H⟩ := h
    apply a.essential (e.symm p)
    exact ⟨{
      toFun := fun q => e.symm (H q)
      continuous_toFun := e.symm.continuous.comp H.continuous
      map_zero_left := fun z => (congrArg e.symm (H.map_zero_left z)).trans (e.symm_apply_apply _)
      map_one_left := fun z => congrArg e.symm (H.map_one_left z) }⟩

theorem push_relation (e : X ≃ₜ Y) {a b : EssentialLoop X}
    (h : ReparamOrIsotopy a b) : ReparamOrIsotopy (pushLoop e a) (pushLoop e b) := by
  cases h with
  | reparam f h => exact .reparam f (fun z => congrArg e (h z))
  | isotopy H hem =>
    refine .isotopy {
      toFun := fun q => e (H q)
      continuous_toFun := e.continuous.comp H.continuous
      map_zero_left := fun z => congrArg e (H.map_zero_left z)
      map_one_left := fun z => congrArg e (H.map_one_left z) } ?_
    exact fun t => e.embedding.comp (hem t)

def pushVertex (e : X ≃ₜ Y) : Vertex X → Vertex Y :=
  Quot.lift (fun a => vertex (pushLoop e a)) (fun _ _ h => Quot.sound (push_relation e h))

theorem unpush (e : X ≃ₜ Y) (v : Vertex X) : pushVertex e.symm (pushVertex e v) = v := by
  induction v using Quot.inductionOn with
  | h a =>
    apply congrArg vertex
    apply EssentialLoop.ext
    apply ContinuousMap.ext
    intro z
    exact e.symm_apply_apply (a.param z)

theorem push_adjacent (e : X ≃ₜ Y) {u v : Vertex X} (h : Adjacent u v) :
    Adjacent (pushVertex e u) (pushVertex e v) := by
  obtain ⟨hne,a,b,rfl,rfl,disj⟩ := h
  constructor
  · intro eq
    exact hne ((unpush e _).symm.trans ((congrArg (pushVertex e.symm) eq).trans (unpush e _)))
  · exact ⟨pushLoop e a,pushLoop e b,rfl,rfl,fun s t eq => disj s t (e.injective eq)⟩

private def mapWalk (e : X ≃ₜ Y) {a b : Vertex X} {n}
    (w : CurveDistance.Walk Adjacent a b n) :
    CurveDistance.Walk Adjacent (pushVertex e a) (pushVertex e b) n := by
  induction w with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (push_adjacent e h) ih

theorem push_exact (e : X ≃ₜ Y) {a b : Vertex X} {n}
    (d : CurveDistance.AtDistance Adjacent a b n) :
    CurveDistance.AtDistance Adjacent (pushVertex e a) (pushVertex e b) n := by
  obtain ⟨⟨w⟩, shortest⟩ := d
  refine ⟨⟨mapWalk e w⟩, ?_⟩
  intro m walk
  have back := mapWalk e.symm walk
  rw [unpush, unpush] at back
  exact shortest back

theorem push_vertex_fixed (e : X ≃ₜ X) (a : EssentialLoop X)
    (h : ∀ z, e (a.param z) = a.param z) : pushVertex e (vertex a) = vertex a := by
  apply congrArg vertex
  apply EssentialLoop.ext
  exact ContinuousMap.ext h

#print axioms push_exact
end
end ShortTwists
