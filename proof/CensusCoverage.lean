import SmallCensus
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.List

/-! Coverage of the two unbounded combinatorial generators in the census. -/
namespace ShortTwists.Census

private theorem nat_compare_agrees : instBEqNat = @instBEqOfDecidableEq ℕ instDecidableEqNat := by
  change BEq.mk _ = BEq.mk _
  apply congrArg BEq.mk
  funext a b
  change (a == b) = decide (a = b)
  exact Bool.eq_iff_iff.mpr ((beq_iff_eq a b).trans decide_eq_true_eq.symm.to_iff)

theorem mem_widths (k n : ℕ) (ws : List ℕ) :
    ws ∈ widths k n ↔ ws.length=k ∧ ws.sum=n := by
  induction k generalizing n ws with
  | zero =>
    cases ws with
    | nil => by_cases h : n=0 <;> simp_all [widths,eq_comm]
    | cons w tail => by_cases h : n=0 <;> simp [widths,h]
  | succ k ih =>
    cases ws with
    | nil => simp [widths]
    | cons w tail =>
      simp only [widths,List.mem_bind,List.mem_range,List.mem_map,List.cons.injEq,
        List.length_cons,List.sum_cons,Nat.succ.injEq]
      constructor
      · rintro ⟨a,ha,z,hz,rfl,rfl⟩
        obtain ⟨h1,h2⟩ := (ih _ _).mp hz
        exact ⟨h1,by omega⟩
      · rintro ⟨h1,h2⟩
        exact ⟨w,by omega,tail,(ih _ _).mpr ⟨h1,by omega⟩,rfl,rfl⟩

/-- Every fixed-point-free involution of the input sides appears as a pairing.
The orientation of the two entries in a generated pair is immaterial. -/
theorem pairings_cover (p : ℕ → ℕ) (k : ℕ) (xs : List ℕ) (nd : xs.Nodup)
    (len : xs.length=2*k) (closed : ∀ x∈xs, p x∈xs)
    (inv : ∀ x∈xs, p (p x)=x) (free : ∀ x∈xs, p x≠x) :
    ∃ ps ∈ pairings k xs, ∀ x∈xs, (x,p x)∈ps ∨ (p x,x)∈ps := by
  induction k generalizing xs with
  | zero =>
    have eq : xs=[] := List.length_eq_zero.mp (by omega)
    subst xs
    exact ⟨[],by decide,by simp⟩
  | succ k ih =>
    cases xs with
    | nil => simp only [List.length_nil] at len; omega
    | cons a rest =>
      obtain ⟨notin,nodup⟩ := List.nodup_cons.mp nd
      have ha : a∈a::rest := List.mem_cons_self _ _
      let b := p a
      have ba : b≠a := free a ha
      have hb : b∈rest := (List.mem_cons.mp (closed a ha)).resolve_left ba
      have pb : p b=a := inv a ha
      let rem := rest.erase b
      have er : rem = @List.erase ℕ (@instBEqOfDecidableEq ℕ instDecidableEqNat) rest b :=
        congrArg (fun e : BEq ℕ => @List.erase ℕ e rest b) nat_compare_agrees
      have keep {x} : x ∈ rem ↔ x≠b ∧ x∈rest := by
        rw [er]
        exact nodup.mem_erase_iff
      have old {x} (hx : x∈rem) : x∈a::rest := List.mem_cons_of_mem _ (keep.mp hx).2
      have mapRem (x) (hx : x∈rem) : p x∈rem := by
        have iv := inv x (old hx)
        have diff : p x≠a := by intro e; exact (keep.mp hx).1 (iv.symm.trans (congrArg p e))
        apply keep.mpr
        refine ⟨?_,(List.mem_cons.mp (closed x (old hx))).resolve_left diff⟩
        intro e
        have xa : x=a := (iv.symm.trans (congrArg p e)).trans pb
        exact notin (xa ▸ (keep.mp hx).2)
      have lr := List.length_erase_add_one hb
      have lr' : rem.length=2*k := by
        rw [er]
        simp only [List.length_cons] at len
        omega
      have nd' : rem.Nodup := er.symm ▸ (nodup.erase b)
      obtain ⟨tail,gen,covers⟩ := ih rem nd' lr' mapRem
        (fun x hx => inv x (old hx)) (fun x hx => free x (old hx))
      refine ⟨(a,b)::tail,List.mem_bind.mpr ⟨b,hb,List.mem_map.mpr ⟨tail,gen,rfl⟩⟩,?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hr
      · exact Or.inl (List.mem_cons_self _ _)
      · by_cases eq : x=b
        · subst x; rw [pb]; exact Or.inr (List.mem_cons_self _ _)
        · exact (covers x (keep.mpr ⟨eq,hr⟩)).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)

#print axioms mem_widths
#print axioms pairings_cover
end ShortTwists.Census
