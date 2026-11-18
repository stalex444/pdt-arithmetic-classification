module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets

@[expose] public section

namespace ExclusionRegion

open Real

/-! CONTROLS: explicit rational witnesses showing which hypotheses carry weight. Together with
`control_iii` ({1, 2, 5}), `control_135` and `control_145` show that no two of constraints 2, 3, 4
can be dropped, even with the ordering `1 < b < a`. -/

theorem pi_sq_bounds : (3.141592 : ℝ) ^ 2 ≤ π ^ 2 ∧ π ^ 2 ≤ (3.141593 : ℝ) ^ 2 :=
  ⟨pow_le_pow_left₀ (by norm_num) Real.pi_gt_d6.le 2,
   pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2⟩

/-- Constraint 1 at a rational point, from two rational inequalities against `π ∈ (3.141592,
3.141593)`. -/
theorem C1_of_rat {a b : ℝ} {p : ℕ} (hl : 136.35082 * (3.141593 : ℝ) ^ 2 ≤ (a * b) ^ p)
    (hu : (a * b) ^ p ≤ 137.72118 * (3.141592 : ℝ) ^ 2) : C1 a b p := by
  have hpi : 0 < π ^ 2 := by positivity
  obtain ⟨hpl, hpu⟩ := pi_sq_bounds
  rw [C1_iff, le_div_iff₀ hpi, div_le_iff₀ hpi]
  exact ⟨(mul_le_mul_of_nonneg_left hpu (by norm_num)).trans hl,
    hu.trans (mul_le_mul_of_nonneg_left hpl (by norm_num))⟩

/-- **Control (i).** Without the ordering `b < a` and without constraint 4, a pair passes
constraints 1, 2, 3, 5 at `p = 11` (here `b > a`). -/
theorem control_i : ∃ (a b : ℝ) (p k : ℕ),
    C1 a b p ∧ C2 a ∧ C3 a b ∧ C5 a k ∧ p ≠ 15 := by
  refine ⟨1.32380523, 1.45546497, 11, 29, ?_, ?_, ?_, ?_, by norm_num⟩
  · exact C1_of_rat (by norm_num) (by norm_num)
  · rw [C2_iff]; unfold lam; norm_num
  · rw [C3_iff]; unfold lam psi; norm_num
  · rw [C5_iff]; norm_num

/-- **Control (ii).** With constraint 1 deleted the `b`-box fails: a pair passes constraints
2, 3, 4, 5 with `b` outside `[1.2195208, 1.2220188]`. -/
theorem control_ii : ∃ (a b : ℝ) (k : ℕ),
    C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a k ∧ ¬ (1.2195208 ≤ b ∧ b ≤ 1.2220188) := by
  refine ⟨1.3255, 1.2194, 29, ?_, ?_, ?_, ?_, by norm_num⟩
  · rw [C2_iff]; unfold lam; norm_num
  · rw [C3_iff]; unfold lam psi; norm_num
  · rw [C4_iff]; unfold lam psi; norm_num
  · rw [C5_iff]; norm_num

/-- **Control (iii).** With constraints 3 and 4 both deleted, `p = 15` fails even with
`1 < b < a`: a pair passes constraints 1, 2, 5 at `p = 14`. -/
theorem control_iii : ∃ (a b : ℝ) (p k : ℕ),
    1 < b ∧ b < a ∧ C1 a b p ∧ C2 a ∧ C5 a k ∧ p ≠ 15 := by
  refine ⟨1.3247, 1.2634, 14, 29, by norm_num, by norm_num, ?_, ?_, ?_, by norm_num⟩
  · exact C1_of_rat (by norm_num) (by norm_num)
  · rw [C2_iff]; unfold lam; norm_num
  · rw [C5_iff]; norm_num

/-- **Control (i), explicit.** The witness of `control_i` has `1 < a < b` and fails
constraint 4. So `b < a` cannot be dropped from `companion_drop_C4_strong`, and constraint 4
cannot be dropped from `forward_strong`. -/
theorem control_i_explicit : ∃ (a b : ℝ) (p k : ℕ),
    1 < a ∧ a < b ∧ C1 a b p ∧ C2 a ∧ C3 a b ∧ C5 a k ∧ ¬ C4 a b ∧ p ≠ 15 := by
  refine ⟨1.32380523, 1.45546497, 11, 29, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_,
    by norm_num⟩
  · exact C1_of_rat (by norm_num) (by norm_num)
  · rw [C2_iff]; unfold lam; norm_num
  · rw [C3_iff]; unfold lam psi; norm_num
  · rw [C5_iff]; norm_num
  · rw [C4_iff]; unfold lam psi; norm_num

/-- **Control (ii), ordered.** The witness of `control_ii` is inside the test's ordering
`1 < b < a`: with constraint 1 deleted the `b`-box fails even there. -/
theorem control_ii_ordered : ∃ (a b : ℝ) (k : ℕ),
    1 < b ∧ b < a ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a k ∧ ¬ (1.2195208 ≤ b ∧ b ≤ 1.2220188) := by
  refine ⟨1.3255, 1.2194, 29, by norm_num, by norm_num, ?_, ?_, ?_, ?_, by norm_num⟩
  · rw [C2_iff]; unfold lam; norm_num
  · rw [C3_iff]; unfold lam psi; norm_num
  · rw [C4_iff]; unfold lam psi; norm_num
  · rw [C5_iff]; norm_num

/-- **Control {1, 3, 5}.** With constraints 2 and 4 both deleted, `k = 29` fails even with
`1 < b < a`: the pair `(1.3372, 1.2094)` passes constraints 1, 3, 5 at `p = 15`, `k = 28`. -/
theorem control_135 : ∃ (a b : ℝ) (p k : ℕ),
    1 < b ∧ b < a ∧ C1 a b p ∧ C3 a b ∧ C5 a k ∧ k ≠ 29 := by
  refine ⟨1.3372, 1.2094, 15, 28, by norm_num, by norm_num, ?_, ?_, ?_, by norm_num⟩
  · exact C1_of_rat (by norm_num) (by norm_num)
  · rw [C3_iff]; unfold lam psi; norm_num
  · rw [C5_iff]; norm_num

/-- **Control {1, 4, 5}.** With constraints 2 and 3 both deleted, both exponents fail even with
`1 < b < a`: the pair `(1.3517, 1.2379)` passes constraints 1, 4, 5 at `p = 14`, `k = 27`. -/
theorem control_145 : ∃ (a b : ℝ) (p k : ℕ),
    1 < b ∧ b < a ∧ C1 a b p ∧ C4 a b ∧ C5 a k ∧ p ≠ 15 ∧ k ≠ 29 := by
  refine ⟨1.3517, 1.2379, 14, 27, by norm_num, by norm_num, ?_, ?_, ?_, by norm_num, by norm_num⟩
  · exact C1_of_rat (by norm_num) (by norm_num)
  · rw [C4_iff]; unfold lam psi; norm_num
  · rw [C5_iff]; norm_num

#print axioms control_i
#print axioms control_i_explicit
#print axioms control_ii_ordered
#print axioms control_135
#print axioms control_145
#print axioms control_ii
#print axioms control_iii

end ExclusionRegion
