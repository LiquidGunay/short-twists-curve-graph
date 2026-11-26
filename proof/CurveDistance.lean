import Lean

/-!
Graph part of the Dehn twist argument. Tested with Lean 4.8.0, core only.
The hypotheses below describe single edges, heights, and the two endpoints.
The short-walk obstruction is proved here by induction on arbitrary walks.
-/

namespace CurveDistance

universe u
variable {V : Type u} {E : V → V → Prop}

inductive Walk (E : V → V → Prop) : V → V → Nat → Type u
  | nil (v : V) : Walk E v v 0
  | cons {x y z : V} {n : Nat} : E x y → Walk E y z n → Walk E x z (n + 1)

namespace Walk

noncomputable def append {x y z : V} {n m : Nat} (s : Walk E x y n) (t : Walk E y z m) :
    Walk E x z (n + m) := by
  induction s with
  | nil => simpa using t
  | cons edge _ ih => simpa [Nat.succ_add] using Walk.cons edge (ih t)

noncomputable def map (F : V → V) (pres : ∀ {x y}, E x y → E (F x) (F y))
    {x y : V} {n : Nat} (s : Walk E x y n) : Walk E (F x) (F y) n := by
  induction s with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (pres edge) ih

noncomputable def reverse (sym : ∀ {x y}, E x y → E y x)
    {x y : V} {n : Nat} (s : Walk E x y n) : Walk E y x n := by
  induction s with
  | nil => exact .nil _
  | cons edge _ ih => exact ih.append (.cons (sym edge) (.nil _))

theorem height_le (h : V → Nat) (up : ∀ {x y}, E x y → h y ≤ h x + 1)
    {x y : V} {n : Nat} (s : Walk E x y n) : h y ≤ h x + n := by
  induction s with
  | nil => omega
  | cons edge _ ih => have := up edge; omega

/-- Either the projection can travel the required distance in n steps,
or the walk pays for descending to height at most one and climbing out. -/
theorem obstruction (h p : V → Nat)
    (up : ∀ {x y}, E x y → h y ≤ h x + 1)
    (down : ∀ {x y}, E x y → h x ≤ h y + 1)
    (localStep : ∀ {x y}, E x y → 1 < h x → 1 < h y → p y ≤ p x + 1)
    {x y : V} {n : Nat} (s : Walk E x y n) :
    p y ≤ p x + n ∨ h x + h y ≤ n + 2 := by
  induction s with
  | nil => left; omega
  | @cons x b y k edge tail ih =>
    have hu := tail.height_le h up
    have hx := down edge
    by_cases lowX : h x ≤ 1
    · have := up edge; right; omega
    by_cases lowB : h b ≤ 1
    · right; omega
    have hp := localStep edge (by omega) (by omega)
    rcases ih with h₁ | h₂
    · left; omega
    · right; omega

theorem split {a b : V} {m t : Nat} (walk : Walk E a b m) (ht : t ≤ m) :
    ∃ z, Nonempty (Walk E a z t) ∧ Nonempty (Walk E z b (m-t)) := by
  induction walk generalizing t with
  | nil v =>
    have : t = 0 := by omega
    subst t
    exact ⟨v, ⟨.nil _⟩, ⟨.nil _⟩⟩
  | @cons a b c l e rest ih =>
    cases t with
    | zero => exact ⟨a, ⟨.nil _⟩, ⟨.cons e rest⟩⟩
    | succ t =>
      obtain ⟨z, ⟨front⟩, ⟨back⟩⟩ := ih (t := t) (by omega)
      exact ⟨z, ⟨.cons e front⟩, ⟨by simpa using back⟩⟩

end Walk

def AtDistance (E : V → V → Prop) (x y : V) (n : Nat) : Prop :=
  Nonempty (Walk E x y n) ∧ ∀ {m}, Walk E x y m → n ≤ m

/-- F folds a prefix of length r-1 at its fixed endpoint w. For a surface,
h is distance from the twist core. p is distance from a chosen annular arc,
using one projected arc per crossing vertex and extremal endpoint arcs. -/
theorem fold_exact (h p : V → Nat) (F : V → V)
    (sym : ∀ {x y}, E x y → E y x)
    (pres : ∀ {x y}, E x y → E (F x) (F y))
    (up : ∀ {x y}, E x y → h y ≤ h x + 1)
    (localStep : ∀ {x y}, E x y → 1 < h x → 1 < h y → p y ≤ p x + 1)
    {a w : V} {r : Nat} (prefixWalk : Walk E a w (r - 1)) (fixW : F w = w)
    (ha : h a = r) (hf : h (F a) = r) (gap : p a + (2*r-2) ≤ p (F a)) :
    AtDistance E a (F a) (2*r-2) := by
  constructor
  · have imageWalk := Walk.map (E := E) F (@pres) prefixWalk
    have back := Walk.reverse (E := E) (@sym) imageWalk
    rw [fixW] at back
    have path := prefixWalk.append back
    have eqn : (r - 1) + (r - 1) = 2*r-2 := by omega
    exact ⟨eqn ▸ path⟩
  · intro m path
    rcases path.obstruction h p up (fun e => up (sym e)) localStep with hp | hd
    · omega
    · omega

/-- Every prescribed initial length of a geodesic is attained. -/
theorem prefix_exact {x y : V} {n : Nat} (d : AtDistance E x y n)
    {k : Nat} (hk : k ≤ n) : ∃ z, AtDistance E x z k := by
  obtain ⟨⟨s⟩, shortest⟩ := d
  obtain ⟨z, ⟨front⟩, ⟨back⟩⟩ := s.split hk
  refine ⟨z, ⟨front⟩, ?_⟩
  intro t shortcut
  have := shortest (shortcut.append back)
  omega

theorem every_distance_of_unbounded {x : V}
    (unbounded : ∀ k : Nat, ∃ y n, k ≤ n ∧ AtDistance E x y n) (k : Nat) :
    ∃ z, AtDistance E x z k := by
  obtain ⟨_, _, hk, d⟩ := unbounded k
  exact prefix_exact d hk

/-! Correctness of recursive elimination from local geometric hypotheses.
    extra = 0 means that two edges remain. The two surface inputs are the
    filling criterion and existence of a first efficient neighbor. -/
def shortPath {D : Type u} (terminal : D → Prop) (children : D → Nat → List D) :
    Nat → D → Prop
  | 0, x => terminal x
  | k+1, x => terminal x ∨ ∃ y ∈ children x (k+3), shortPath terminal children k y

theorem finite_search_correct {D : Type u} (δ : D → Nat)
    (terminal : D → Prop) (children : D → Nat → List D)
    (base : ∀ x, terminal x ↔ δ x ≤ 2)
    (legal : ∀ x m y, y ∈ children x m → δ x ≤ δ y + 1)
    (efficient : ∀ x m, 2 < δ x → δ x ≤ m →
      ∃ y ∈ children x m, δ y + 1 = δ x)
    (k : Nat) (x : D) : shortPath terminal children k x ↔ δ x ≤ k+2 := by
  induction k generalizing x with
  | zero => exact base x
  | succ k ih =>
    constructor
    · intro h
      rcases h with last | ⟨y, mem, rest⟩
      · have := (base x).mp last; omega
      · have := (ih y).mp rest
        have := legal x _ y mem
        omega
    · intro h
      by_cases small : δ x ≤ 2
      · exact Or.inl ((base x).mpr small)
      · obtain ⟨y, mem, eqn⟩ := efficient x (k+3) (by omega) (by omega)
        exact Or.inr ⟨y, mem, (ih y).mpr (by omega)⟩

#print axioms fold_exact
#print axioms every_distance_of_unbounded
#print axioms finite_search_correct
end CurveDistance
