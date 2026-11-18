module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets

@[expose] public section

namespace ExclusionRegion

open Real

/-! Target 2, BOX: the accepted set lies in a rectangle (literals rounded outward). -/

/-- On the accepted set `a` and `b` are positive. -/
theorem pos_of_A {a b : ℝ} (h : A a b) : 0 < a ∧ 0 < b := by
  rw [A_iff] at h
  obtain ⟨h1, _, h3, _⟩ := h
  have ha0 := pos_of_pow29 h1
  have hab : 0 < (a * b) ^ 15 := lt_of_lt_of_le (by positivity) h3
  have hab0 : 0 < a * b := (Odd.pow_pos_iff ⟨7, by norm_num⟩).mp hab
  refine ⟨ha0, ?_⟩
  by_contra hc
  have hc := not_lt.mp hc
  have := mul_nonpos_of_nonneg_of_nonpos ha0.le hc
  linarith

/-- Nine-digit internal bounds on `a` from the window on `a^29`. -/
theorem a_sharp_of_pow29 {a : ℝ} (h1 : 3407.656 ≤ a ^ 29) (h2 : a ^ 29 ≤ 3546.744) :
    1.323758673 ≤ a ∧ a ≤ 1.325586052 :=
  pow29_bracket (by norm_num) (by norm_num) (by norm_num) h1 h2

/-- **Target 2.** The accepted set lies in the box, and in it `1 < b < a`. -/
theorem box (a b : ℝ) (h : A a b) :
    1.3237586 ≤ a ∧ a ≤ 1.3255861 ∧ 1.2195208 ≤ b ∧ b ≤ 1.2220188 ∧ 1 < b ∧ b < a := by
  obtain ⟨ha0, hb0⟩ := pos_of_A h
  rw [A_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨hal, hau⟩ := a_sharp_of_pow29 h1 h2
  have hpl : (3.141592 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d6.le 2
  have hpu : π ^ 2 ≤ (3.141593 : ℝ) ^ 2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2
  have hab0 : 0 ≤ a * b := (mul_pos ha0 hb0).le
  have hbl : 1.2195208 ≤ b := by
    by_contra hc
    have hc := not_le.mp hc
    have e1 : a * b ≤ 1.325586052 * 1.2195208 := mul_le_mul hau hc.le hb0.le (by norm_num)
    have e2 : (a * b) ^ 15 ≤ ((1.325586052 : ℝ) * 1.2195208) ^ 15 := pow_le_pow_left₀ hab0 e1 15
    have e3 : ((1.325586052 : ℝ) * 1.2195208) ^ 15 < 136.35082 * 3.141592 ^ 2 := by norm_num
    have e4 : (136.35082 : ℝ) * 3.141592 ^ 2 ≤ 136.35082 * π ^ 2 :=
      mul_le_mul_of_nonneg_left hpl (by norm_num)
    exact lt_irrefl _ (lt_of_le_of_lt e2 (lt_of_lt_of_le e3 (e4.trans h3)))
  have hbu : b ≤ 1.2220188 := by
    by_contra hc
    have hc := not_le.mp hc
    have e1 : (1.323758673 : ℝ) * 1.2220188 ≤ a * b :=
      mul_le_mul hal hc.le (by norm_num) ha0.le
    have e2 : ((1.323758673 : ℝ) * 1.2220188) ^ 15 ≤ (a * b) ^ 15 :=
      pow_le_pow_left₀ (by norm_num) e1 15
    have e3 : (137.72118 : ℝ) * 3.141593 ^ 2 < ((1.323758673 : ℝ) * 1.2220188) ^ 15 := by norm_num
    have e4 : (137.72118 : ℝ) * π ^ 2 ≤ 137.72118 * 3.141593 ^ 2 :=
      mul_le_mul_of_nonneg_left hpu (by norm_num)
    exact lt_irrefl _ (lt_of_le_of_lt (h4.trans e4) (lt_of_lt_of_le e3 e2))
  refine ⟨by linarith, by linarith, hbl, hbu, by linarith, by linarith⟩

#print axioms box

end ExclusionRegion
