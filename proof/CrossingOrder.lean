import CollarCrossings

/-! Integral coordinates for the physical crossings. Positions are measured in
quarter-slot units. These formulas determine the two cyclic orders read by the
finite checker. -/
namespace ShortTwists.Cylinder
open unitInterval

def fixedColumn (f : ℕ) := 4*f + 2
def movingColumn (m : ℕ) (positive : Bool) := 4*m + if positive then 3 else 1
def tick (n f m : ℕ) (up : Bool) :=
  let x := fixedColumn f
  let y := movingColumn m up
  if y ≤ x then x-y else 4*n+x-y

def readTick (n h : ℕ) (up : Bool) := if up then h else 4*n-h

noncomputable section

theorem tick_bounds {n : ℕ} (f m : Fin n) (up : Bool) :
    0 < tick n f m up ∧ tick n f m up < 4*n := by
  have hf := f.isLt
  have hm := m.isLt
  cases up <;> simp only [tick,fixedColumn,movingColumn,Bool.false_eq_true,if_false,if_true]
    <;> split <;> omega

def tickHeight {n : ℕ} (f m : Fin n) (up : Bool) : unitInterval := by
  have hn : (0 : ℝ) < 4*n := by exact_mod_cast (Nat.zero_lt_of_lt (tick_bounds f m up).2)
  exact ⟨(tick n f m up : ℝ)/(4*n), div_nonneg (Nat.cast_nonneg _) hn.le,
    (div_le_one hn).mpr (by exact_mod_cast (tick_bounds f m up).2.le)⟩

theorem tickHeight_inside {n : ℕ} (f m : Fin n) (up : Bool) :
    inside (tickHeight f m up) := by
  have hn : (0 : ℝ) < 4*n := by exact_mod_cast (Nat.zero_lt_of_lt (tick_bounds f m up).2)
  have gt : 0 < (tickHeight f m up : ℝ) :=
    div_pos (by exact_mod_cast (tick_bounds f m up).1) hn
  have lt : (tickHeight f m up : ℝ) < 1 :=
    (div_lt_one hn).mpr (by exact_mod_cast (tick_bounds f m up).2)
  exact ⟨fun h => gt.ne' (congrArg Subtype.val h),fun h => lt.ne (congrArg Subtype.val h)⟩

private theorem fixed_coord (s : Array Int) (f : Fin s.size) :
    strandX s mid f = (((fixedColumn f : ℝ)/(4*s.size) : ℝ) : Turn) := by
  change slot s.size f (oriented (positive s f) mid) = _
  rw [oriented_mid]
  apply congrArg (fun r : ℝ => (r : Turn))
  change ((f : ℝ) + 1/2)/s.size = (fixedColumn f : ℝ)/(4*s.size)
  have hn : (s.size : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt f.isLt))
  push_cast [fixedColumn]
  field_simp
  ring

private theorem moving_coord (s : Array Int) (m : Fin s.size) :
    strandX s pushOff m = (((movingColumn m (positive s m) : ℝ)/(4*s.size) : ℝ) : Turn) := by
  apply congrArg (fun r : ℝ => (r : Turn))
  change ((m : ℝ)+(oriented (positive s m) pushOff : ℝ))/s.size = _
  have hn : (s.size : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt m.isLt))
  cases positive s m <;> simp [oriented,pushOff,quarter,movingColumn] <;> field_simp <;> ring

/-- At the named height the once-twisted moving strand lands on the fixed strand.
The proof handles both sides of the cylinder cut, where one full period is lost. -/
theorem tick_hits (s : Array Int) (f m : Fin s.size) :
    strandX s pushOff m + (((tickHeight f m (positive s m) : unitInterval) : ℝ) : Turn) =
      strandX s mid f := by
  rw [moving_coord,fixed_coord,← AddCircle.coe_add]
  let x := fixedColumn f
  let y := movingColumn m (positive s m)
  let N := s.size
  change (((y : ℝ)/(4*N) + (tick N f m (positive s m) : ℝ)/(4*N) : ℝ) : Turn) =
    (((x : ℝ)/(4*N) : ℝ) : Turn)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt m.isLt))
  by_cases h : y ≤ x
  · have ht : tick N f m (positive s m) + y = x := by
      change (if y ≤ x then x-y else 4*N+x-y) + y = x
      rw [if_pos h]; omega
    have hr : (tick N f m (positive s m) : ℝ) + y = x := by exact_mod_cast ht
    exact congrArg (fun t : ℝ => (t : Turn)) (by rw [← add_div]; congr 1; linarith)
  · have hyle : y ≤ 4*N := by
      have hm := m.isLt
      dsimp [y,movingColumn,N]
      split <;> omega
    have ht : tick N f m (positive s m) + y = 4*N+x := by
      change (if y ≤ x then x-y else 4*N+x-y) + y = 4*N+x
      rw [if_neg h]; omega
    have hr : (tick N f m (positive s m) : ℝ) + y = 4*N+x := by exact_mod_cast ht
    have e : (y:ℝ)/(4*N) + (tick N f m (positive s m) : ℝ)/(4*N) = (x:ℝ)/(4*N)+1 := by
      field_simp
      linarith
    rw [e, AddCircle.coe_add_period]

theorem tick_is_geometric_height (s : Array Int) (f m : Fin s.size) :
    tickHeight f m (positive s m) = level (strandX s mid f - strandX s pushOff m) := by
  apply level_unique (tickHeight_inside _ _ _)
  rw [← tick_hits s f m]
  abel

/-- Along either oriented strand the crossing parameter is this integer key
divided by 4n. Thus sorting the keys sorts the crossings on that strand. -/
theorem traversal_coordinate {n : ℕ} (f m : Fin n) (movingUp readUp : Bool) :
    ((oriented readUp (tickHeight f m movingUp) : unitInterval) : ℝ) =
    (readTick n (tick n f m movingUp) readUp : ℝ)/(4*n) := by
  cases readUp
  · change 1 - (tick n f m movingUp : ℝ)/(4*n) = ((4*n-tick n f m movingUp : ℕ) : ℝ)/(4*n)
    rw [Nat.cast_sub (tick_bounds f m movingUp).2.le]
    push_cast
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt f.isLt))
    field_simp
  · rfl

#print axioms tick_is_geometric_height
end
end ShortTwists.Cylinder
