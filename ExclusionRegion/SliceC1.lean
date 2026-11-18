module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets

@[expose] public section

namespace ExclusionRegion

open Real

/-! SLICE FROM CONSTRAINT 1 ALONE. `slice` (Slice.lean) takes the accepted set `A`, which carries
constraint 5. On the three-coupling path constraint 5 is absent, so the slice is restated from
constraint 1 at `p = 15` and `a³ = a + 1`, `1 < a`. Also: the real root above 1 of `x³ = x + 1`
(resp. `x⁴ = x + 1`) is unique, so the window conclusions name one number each. -/

/-- **SLICE (constraint 1 alone).** If `a³ = a + 1`, `1 < a` and constraint 1 holds at `p = 15`,
then `b` lies in the slice `S = [1.22032003, 1.22113387]`. -/
theorem slice_of_C1 (a b : ℝ) :
    a ^ 3 = a + 1 → 1 < a → C1 a b 15 → 1.22032003 ≤ b ∧ b ≤ 1.22113387 := by
  intro ha3 ha h1
  rw [C1_iff] at h1
  obtain ⟨h3', h4'⟩ := h1
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  have h3 : 136.35082 * π ^ 2 ≤ (a * b) ^ 15 := (le_div_iff₀ hpi).mp h3'
  have h4 : (a * b) ^ 15 ≤ 137.72118 * π ^ 2 := (div_le_iff₀ hpi).mp h4'
  have ha0 : 0 < a := by linarith
  have habp : 0 < (a * b) ^ 15 := lt_of_lt_of_le (by positivity) h3
  have hab : 0 < a * b := (Odd.pow_pos_iff ⟨7, by norm_num⟩).mp habp
  have hb0 : 0 < b := by
    by_contra hc
    have hc := not_lt.mp hc
    have := mul_nonpos_of_nonneg_of_nonpos ha0.le hc
    linarith
  have hal : 1.324717957 < a := root_gt (n := 3) (by norm_num) ha.le ha3 (by norm_num)
  have hau : a < 1.324717958 := root_lt (n := 3) (by norm_num) ha3 (by norm_num) (by norm_num)
  have hpl : (3.14159265358979323846 : ℝ) ^ 2 ≤ π ^ 2 :=
    pow_le_pow_left₀ (by norm_num) Real.pi_gt_d20.le 2
  have hpu : π ^ 2 ≤ (3.14159265358979323847 : ℝ) ^ 2 :=
    pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d20.le 2
  have hab0 : 0 ≤ a * b := hab.le
  constructor
  · by_contra hc
    have hc := not_le.mp hc
    have e1 : a * b ≤ 1.324717958 * 1.22032003 := mul_le_mul hau.le hc.le hb0.le (by norm_num)
    have e2 : (a * b) ^ 15 ≤ ((1.324717958 : ℝ) * 1.22032003) ^ 15 := pow_le_pow_left₀ hab0 e1 15
    have e3 : ((1.324717958 : ℝ) * 1.22032003) ^ 15
        < 136.35082 * 3.14159265358979323846 ^ 2 := by norm_num
    have e4 : (136.35082 : ℝ) * 3.14159265358979323846 ^ 2 ≤ 136.35082 * π ^ 2 :=
      mul_le_mul_of_nonneg_left hpl (by norm_num)
    exact lt_irrefl _ (lt_of_le_of_lt e2 (lt_of_lt_of_le e3 (e4.trans h3)))
  · by_contra hc
    have hc := not_le.mp hc
    have e1 : (1.324717957 : ℝ) * 1.22113387 ≤ a * b :=
      mul_le_mul hal.le hc.le (by norm_num) ha0.le
    have e2 : ((1.324717957 : ℝ) * 1.22113387) ^ 15 ≤ (a * b) ^ 15 :=
      pow_le_pow_left₀ (by norm_num) e1 15
    have e3 : (137.72118 : ℝ) * 3.14159265358979323847 ^ 2
        < ((1.324717957 : ℝ) * 1.22113387) ^ 15 := by norm_num
    have e4 : (137.72118 : ℝ) * π ^ 2 ≤ 137.72118 * 3.14159265358979323847 ^ 2 :=
      mul_le_mul_of_nonneg_left hpu (by norm_num)
    exact lt_irrefl _ (lt_of_le_of_lt (h4.trans e4) (lt_of_lt_of_le e3 e2))

/-- The real root above 1 of `x³ = x + 1` is unique. -/
theorem cubic_root_unique {x y : ℝ} (hx : 1 < x) (hy : 1 < y) (hx3 : x ^ 3 = x + 1)
    (hy3 : y ^ 3 = y + 1) : x = y := by
  have h : (x - y) * (x ^ 2 + x * y + y ^ 2 - 1) = 0 := by linear_combination hx3 - hy3
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · nlinarith

/-- The real root above 1 of `x⁴ = x + 1` is unique. -/
theorem quartic_root_unique {x y : ℝ} (hx : 1 < x) (hy : 1 < y) (hx4 : x ^ 4 = x + 1)
    (hy4 : y ^ 4 = y + 1) : x = y := by
  have h : (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 1) = 0 := by
    linear_combination hx4 - hy4
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · nlinarith [mul_pos (zero_lt_one.trans hx) (zero_lt_one.trans hy)]

#print axioms slice_of_C1
#print axioms cubic_root_unique
#print axioms quartic_root_unique

end ExclusionRegion
