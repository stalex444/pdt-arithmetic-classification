module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets
public import ExclusionRegion.Pass
public import ExclusionRegion.Box
public import ExclusionRegion.Converse
public import ExclusionRegion.Controls

@[expose] public section

namespace ExclusionRegion

open Real

/-! NON-VACUITY: the accepted set has an explicit rational point; the two roots exist, so the
hypotheses of `pass_strong` are satisfiable; the left side of the equivalence is satisfiable;
the accepted set is not everything; and `1 < b` cannot be dropped from `pass_strong`. -/

/-- An explicit rational point of the accepted set. -/
theorem A_rational_point : A 1.3247 1.2207 := by
  obtain ⟨hpl, hpu⟩ := pi_sq_bounds
  rw [A_iff]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hpu (by norm_num)).trans (by norm_num)
  · exact le_trans (by norm_num) (mul_le_mul_of_nonneg_left hpl (by norm_num))

/-- The five windows are satisfiable (at a rational point, with `p = 15`, `k = 29`). -/
theorem five_satisfiable : ∃ (a b : ℝ) (p k : ℕ), C1 a b p ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a k :=
  ⟨_, _, 15, 29, converse _ _ A_rational_point⟩

/-- The cubic `x³ = x + 1` has a real root above 1. -/
theorem exists_cubic_root : ∃ a : ℝ, 1 < a ∧ a ^ 3 = a + 1 := by
  have hf : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) := by fun_prop
  have m : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 1) 1)
      ((fun x : ℝ => x ^ 3 - x - 1) 2) := by constructor <;> norm_num
  obtain ⟨a, _, hfa⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hf m
  have ha3 : a ^ 3 = a + 1 := by have h : a ^ 3 - a - 1 = 0 := hfa; linarith
  exact ⟨a, one_lt_of_cubic ha3, ha3⟩

/-- The quartic `x⁴ = x + 1` has a real root above 1. -/
theorem exists_quartic_root : ∃ b : ℝ, 1 < b ∧ b ^ 4 = b + 1 := by
  have hf : ContinuousOn (fun x : ℝ => x ^ 4 - x - 1) (Set.Icc 1 2) := by fun_prop
  have m : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 4 - x - 1) 1)
      ((fun x : ℝ => x ^ 4 - x - 1) 2) := by constructor <;> norm_num
  obtain ⟨b, hb, hfb⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hf m
  have hb4 : b ^ 4 = b + 1 := by have h : b ^ 4 - b - 1 = 0 := hfb; linarith
  have hb1 : 1 < b := by
    rcases eq_or_lt_of_le hb.1 with h | h
    · rw [← h] at hb4; norm_num at hb4
    · exact h
  exact ⟨b, hb1, hb4⟩

/-- `pass_strong` is not vacuous: the two roots exist and the pair is in the accepted set. -/
theorem pass_nonvacuous : ∃ a b : ℝ, a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b ∧ A a b := by
  obtain ⟨a, _, ha3⟩ := exists_cubic_root
  obtain ⟨b, hb1, hb4⟩ := exists_quartic_root
  exact ⟨a, b, ha3, hb4, hb1, pass_strong a b ha3 hb1 hb4⟩

/-- The accepted set is not everything. -/
theorem not_A_one_one : ¬ A 1 1 := by
  intro h
  have := (box 1 1 h).1
  norm_num at this

/-- `1 < b` cannot be dropped from `pass_strong`: the quartic has a second real root (in
`[-1, 0]`), and no pair with that `b` is in the accepted set. -/
theorem pass_needs_one_lt_b : ∃ b : ℝ, b ^ 4 = b + 1 ∧ ∀ a : ℝ, ¬ A a b := by
  have hf : ContinuousOn (fun x : ℝ => x ^ 4 - x - 1) (Set.Icc (-1) 0) := by fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 4 - x - 1) 0)
      ((fun x : ℝ => x ^ 4 - x - 1) (-1)) := by
    constructor <;> norm_num
  obtain ⟨b, hb, hfb⟩ := intermediate_value_Icc' (by norm_num : (-1 : ℝ) ≤ 0) hf hmem
  have hfb' : b ^ 4 - b - 1 = 0 := hfb
  refine ⟨b, by linarith, fun a hA => ?_⟩
  have := (pos_of_A hA).2
  linarith [hb.2]

#print axioms A_rational_point
#print axioms five_satisfiable
#print axioms exists_cubic_root
#print axioms exists_quartic_root
#print axioms pass_nonvacuous
#print axioms not_A_one_one
#print axioms pass_needs_one_lt_b

end ExclusionRegion
