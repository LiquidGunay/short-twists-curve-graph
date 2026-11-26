import FiniteDiagrams
import IsotopyGraph

/-! Relate the *executable* search to genuine walks. Only the three explicitly
stated local surface lemmas in GeometricSearch remain parameters of the transfer. -/
namespace FiniteDiagrams

def cut (s : Code) := triangulate (cutFaces s) s.size
def candidates (s : Code) (k : Nat) : List Route :=
  (routes (cut s).opp (coordinateBound (cut s) k)).toList

def Search : Nat → Code → Prop
  | 0, s => terminal s = true
  | k+1, s => terminal s = true ∨
      ∃ r ∈ candidates s k, Search k (neighbor (cut s) r)

theorem visit_iff {α σ : Type} {test : α → σ → Bool × σ} {P : α → Prop}
    (ok : ∀ x c, (test x c).1 = true ↔ P x) (xs : List α) (cache : σ) :
    (visit test xs cache).1 = true ↔ ∃ r ∈ xs, P r := by
  induction xs generalizing cache with
  | nil => simp [visit]
  | cons a xs ih =>
    cases he : test a cache with
    | mk b next =>
      have ha := ok a cache
      rw [he] at ha
      cases b with
      | false =>
        have hn : ¬ P a := fun hp => Bool.noConfusion (ha.mpr hp)
        simp [visit,he,ih,List.mem_cons,or_and_right,exists_or,hn]
      | true =>
        have hp : P a := ha.mp rfl
        simp [visit,he,List.mem_cons,or_and_right,exists_or,hp]

theorem reachable_iff (k : Nat) (s : Code) (cache : RouteCache) :
    (reachable k s cache).1 = true ↔ Search k s := by
  induction k generalizing s cache with
  | zero => rfl
  | succ k ih =>
    cases ht : terminal s with
    | true => simp [reachable,Search,ht]
    | false =>
      let tr := cut s
      let row := getRoutes tr.opp (coordinateBound tr k) cache
      simp only [reachable,Search,ht,Bool.false_eq_true,if_false,false_or]
      change (visit (fun r => reachable k (neighbor tr r)) row.1.val.toList row.2).1 = true ↔ _
      rw [visit_iff (fun r c => ih (neighbor tr r) c), row.1.property]
      rfl

theorem exactTest_iff (d : Nat) (s : Code) :
    exactTest s d = true ↔ ¬ Search (d-3) s ∧ Search (d-2) s := by
  cases h : (reachable (d-3) s).run {} with
  | mk b next =>
    have lo := reachable_iff (d-3) s {}
    change ((reachable (d-3) s).run {}).1 = true ↔ _ at lo
    rw [h] at lo
    cases b with
    | true =>
      have yes := lo.mp rfl
      simp [exactTest,h,yes]
    | false =>
      have no : ¬ Search (d-3) s := fun hp => Bool.noConfusion (lo.mpr hp)
      simpa [exactTest,h,no] using reachable_iff (d-2) s next

#print axioms reachable_iff
end FiniteDiagrams

namespace ShortTwists
open CurveDistance FiniteDiagrams
variable {X : Type*} [TopologicalSpace X]

def Within (a b : Vertex X) (m : Nat) : Prop :=
  ∃ l, l ≤ m ∧ Nonempty (Walk Adjacent a b l)

theorem within_two (a b : Vertex X) :
    Within a b 2 ↔ a=b ∨ Adjacent a b ∨ ∃ c, Adjacent a c ∧ Adjacent c b := by
  constructor
  · rintro ⟨_,h,⟨w⟩⟩
    cases w with
    | nil => exact Or.inl rfl
    | cons e w =>
      cases w with
      | nil => exact Or.inr (Or.inl e)
      | cons f w =>
        cases w with
        | nil => exact Or.inr (Or.inr ⟨_,e,f⟩)
        | cons => omega
  · rintro (rfl|edge|⟨c,e,f⟩)
    · exact ⟨0,by decide,⟨.nil _⟩⟩
    · exact ⟨1,by decide,⟨.cons edge (.nil _)⟩⟩
    · exact ⟨2,by decide,⟨.cons e (.cons f (.nil _))⟩⟩

/-- A local interpretation for diagrams realized on X. Each premise is restricted
to realized diagrams. In particular, malformed arrays are never required to denote curves. -/
structure GeometricSearch (X : Type*) [TopologicalSpace X] where
  represents : Code → Vertex X → Vertex X → Prop
  filling : ∀ {s a b}, represents s a b →
    (terminal s = true ↔ a=b ∨ Adjacent a b ∨ ∃ c, Adjacent a c ∧ Adjacent c b)
  legal : ∀ {s a b k r}, represents s a b → r ∈ candidates s k →
    ∃ z, (z=a ∨ Adjacent a z) ∧ represents (neighbor (cut s) r) z b
  efficient : ∀ {s a b k}, represents s a b → terminal s = false → Within a b (k+3) →
    ∃ r ∈ candidates s k, ∃ z, represents (neighbor (cut s) r) z b ∧ Within z b (k+2)

theorem search_iff_walk (G : GeometricSearch X) (k : Nat) {s a b}
    (h : G.represents s a b) : Search k s ↔ Within a b (k+2) := by
  induction k generalizing s a b with
  | zero => exact (G.filling h).trans (within_two a b).symm
  | succ k ih =>
    constructor
    · rintro (last|⟨r,mem,rest⟩)
      · obtain ⟨n,hn,w⟩ := (within_two a b).mpr ((G.filling h).mp last)
        exact ⟨n,by omega,w⟩
      · obtain ⟨z,step,meaning⟩ := G.legal h mem
        obtain ⟨n,hn,⟨w⟩⟩ := (ih meaning).mp rest
        rcases step with rfl|e
        · exact ⟨n,by omega,⟨w⟩⟩
        · exact ⟨n+1,by omega,⟨.cons e w⟩⟩
    · intro walk
      cases term : terminal s with
      | true => exact Or.inl term
      | false =>
        obtain ⟨r,mem,z,meaning,short⟩ := G.efficient h term walk
        exact Or.inr ⟨r,mem,(ih meaning).mpr short⟩

theorem checked_distance (G : GeometricSearch X) {s a b d} (h : G.represents s a b)
    (hd : 3 ≤ d) (cert : exactTest s d = true) : AtDistance Adjacent a b d := by
  obtain ⟨lower,upper⟩ := (exactTest_iff d s).mp cert
  have no := fun w => lower ((search_iff_walk G (d-3) h).mpr w)
  obtain ⟨l,hl,⟨walk⟩⟩ := (search_iff_walk G (d-2) h).mp upper
  have lb : ∀ {n}, Walk Adjacent a b n → d ≤ n := by
    intro n w
    by_contra small
    exact no ⟨n,by omega,⟨w⟩⟩
  have eq : l=d := by have := lb walk; omega
  exact ⟨⟨eq ▸ walk⟩,@lb⟩

#print axioms checked_distance
end ShortTwists
