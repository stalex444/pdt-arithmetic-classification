module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets

@[expose] public section

namespace ExclusionRegion

open Real

/-! Target 4, PASS: the real root of `x³ = x + 1` and the real root of `x⁴ = x + 1` above 1 lie
in the accepted set, and 15 and 29 are the nearest integers. The cubic has one real root, so
`1 < a` is not a hypothesis of the strong forms; the quartic has a second real root (in
`[-1, 0]`), so `1 < b` is needed (`pass_needs_one_lt_b` in NonVacuity.lean). -/

/-- A real root of `x³ = x + 1` is above 1 (the cubic has one real root). -/
theorem one_lt_of_cubic {a : ℝ} (h : a ^ 3 = a + 1) : 1 < a := by
  by_contra hc
  have hc := not_lt.mp hc
  rcases le_or_gt 0 a with h0 | h0
  · have := mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr hc)) (by linarith : (0 : ℝ) ≤ a + 1)
    nlinarith
  · have h3 : a ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ h0
    have h1 : a < -1 := by linarith
    have := mul_pos (mul_pos (neg_pos.mpr h0) (by linarith : (0 : ℝ) < 1 - a))
      (by linarith : (0 : ℝ) < -a - 1)
    nlinarith

theorem rho_bracket {a : ℝ} (ha : 1 < a) (ha3 : a ^ 3 = a + 1) : 1.32471 < a ∧ a < 1.32472 :=
  ⟨root_gt (n := 3) (by norm_num) ha.le ha3 (by norm_num),
   root_lt (n := 3) (by norm_num) ha3 (by norm_num) (by norm_num)⟩

theorem Q_bracket {b : ℝ} (hb : 1 < b) (hb4 : b ^ 4 = b + 1) : 1.22074 < b ∧ b < 1.22075 :=
  ⟨root_gt (n := 4) (by norm_num) hb.le hb4 (by norm_num),
   root_lt (n := 4) (by norm_num) hb4 (by norm_num) (by norm_num)⟩

/-- **Target 4, strong form.** Any real root `a` of `x³ = x + 1` and the root `b > 1` of
`x⁴ = x + 1` are in the accepted set. `1 < a` is not assumed. -/
theorem pass_strong (a b : ℝ) (ha3 : a ^ 3 = a + 1) (hb : 1 < b) (hb4 : b ^ 4 = b + 1) :
    A a b := by
  have ha : 1 < a := one_lt_of_cubic ha3
  obtain ⟨hal, hau⟩ := rho_bracket ha ha3
  obtain ⟨hbl, hbu⟩ := Q_bracket hb hb4
  have hpl : (3.141592 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d6.le 2
  have hpu : π ^ 2 ≤ (3.141593 : ℝ) ^ 2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2
  have hab_l : (1.32471 : ℝ) * 1.22074 ≤ a * b :=
    mul_le_mul hal.le hbl.le (by norm_num) (by linarith)
  have hab_u : a * b ≤ 1.32472 * 1.22075 := mul_le_mul hau.le hbu.le (by linarith) (by norm_num)
  have hab0 : 0 ≤ a * b := mul_nonneg (by linarith) (by linarith)
  rw [A_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (3407.656 : ℝ) ≤ 1.32471 ^ 29 := by norm_num
      _ ≤ a ^ 29 := pow_le_pow_left₀ (by norm_num) hal.le 29
  · calc a ^ 29 ≤ (1.32472 : ℝ) ^ 29 := pow_le_pow_left₀ (by linarith) hau.le 29
      _ ≤ 3546.744 := by norm_num
  · calc 136.35082 * π ^ 2 ≤ 136.35082 * (3.141593 : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hpu (by norm_num)
      _ ≤ ((1.32471 : ℝ) * 1.22074) ^ 15 := by norm_num
      _ ≤ (a * b) ^ 15 := pow_le_pow_left₀ (by norm_num) hab_l 15
  · calc (a * b) ^ 15 ≤ ((1.32472 : ℝ) * 1.22075) ^ 15 := pow_le_pow_left₀ hab0 hab_u 15
      _ ≤ 137.72118 * (3.141592 : ℝ) ^ 2 := by norm_num
      _ ≤ 137.72118 * π ^ 2 := mul_le_mul_of_nonneg_left hpl (by norm_num)

/-- **Target 4** as first stated. The hypothesis `1 < a` is not needed (`pass_strong` is the
statement without it); it is kept, unused, so that the original signature stays available. -/
theorem pass (a b : ℝ) (_ha : 1 < a) (ha3 : a ^ 3 = a + 1) (hb : 1 < b) (hb4 : b ^ 4 = b + 1) :
    A a b :=
  pass_strong a b ha3 hb hb4

/-- **Nearest integers, strong form.** At the two roots, `15` is the nearest integer to
`log(T1 π²)/log(ab)` and `29` the nearest to `log T5/log a`, stated without logarithms.
`1 < a` is not assumed. -/
theorem pass_nearest_strong (a b : ℝ) (ha3 : a ^ 3 = a + 1) (hb : 1 < b)
    (hb4 : b ^ 4 = b + 1) :
    (a * b) ^ 29 < (T1 * π ^ 2) ^ 2 ∧ (T1 * π ^ 2) ^ 2 < (a * b) ^ 31 ∧
      a ^ 57 < T5 ^ 2 ∧ T5 ^ 2 < a ^ 59 := by
  have ha : 1 < a := one_lt_of_cubic ha3
  obtain ⟨hal, hau⟩ := rho_bracket ha ha3
  obtain ⟨hbl, hbu⟩ := Q_bracket hb hb4
  have hpl : (3.141592 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d6.le 2
  have hpu : π ^ 2 ≤ (3.141593 : ℝ) ^ 2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2
  have hab_l : (1.32471 : ℝ) * 1.22074 ≤ a * b :=
    mul_le_mul hal.le hbl.le (by norm_num) (by linarith)
  have hab_u : a * b ≤ 1.32472 * 1.22075 := mul_le_mul hau.le hbu.le (by linarith) (by norm_num)
  have hab0 : 0 ≤ a * b := mul_nonneg (by linarith) (by linarith)
  have hpi0 : (0 : ℝ) ≤ 137.036 * π ^ 2 := by positivity
  unfold T1 T5
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (a * b) ^ 29 ≤ ((1.32472 : ℝ) * 1.22075) ^ 29 := pow_le_pow_left₀ hab0 hab_u 29
      _ < (137.036 * (3.141592 : ℝ) ^ 2) ^ 2 := by norm_num
      _ ≤ (137.036 * π ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by norm_num) (mul_le_mul_of_nonneg_left hpl (by norm_num)) 2
  · calc (137.036 * π ^ 2) ^ 2 ≤ (137.036 * (3.141593 : ℝ) ^ 2) ^ 2 :=
          pow_le_pow_left₀ hpi0 (mul_le_mul_of_nonneg_left hpu (by norm_num)) 2
      _ < ((1.32471 : ℝ) * 1.22074) ^ 31 := by norm_num
      _ ≤ (a * b) ^ 31 := pow_le_pow_left₀ (by norm_num) hab_l 31
  · calc a ^ 57 ≤ (1.32472 : ℝ) ^ 57 := pow_le_pow_left₀ (by linarith) hau.le 57
      _ < (3477.2 : ℝ) ^ 2 := by norm_num
  · calc (3477.2 : ℝ) ^ 2 < (1.32471 : ℝ) ^ 59 := by norm_num
      _ ≤ a ^ 59 := pow_le_pow_left₀ (by norm_num) hal.le 59

/-- The nearest-integer statement as first stated. The hypothesis `1 < a` is not needed
(`pass_nearest_strong` is the statement without it). -/
theorem pass_nearest (a b : ℝ) (_ha : 1 < a) (ha3 : a ^ 3 = a + 1) (hb : 1 < b)
    (hb4 : b ^ 4 = b + 1) :
    (a * b) ^ 29 < (T1 * π ^ 2) ^ 2 ∧ (T1 * π ^ 2) ^ 2 < (a * b) ^ 31 ∧
      a ^ 57 < T5 ^ 2 ∧ T5 ^ 2 < a ^ 59 :=
  pass_nearest_strong a b ha3 hb hb4

#print axioms one_lt_of_cubic
#print axioms pass_strong
#print axioms pass
#print axioms pass_nearest_strong
#print axioms pass_nearest

end ExclusionRegion
