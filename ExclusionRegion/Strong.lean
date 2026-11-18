module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets
public import ExclusionRegion.Forward

@[expose] public section

namespace ExclusionRegion

open Real

/-! Target 1b, STRONG FORWARD: no ordering hypothesis and no exponent ranges. Targets 1a and 5,
the test-shaped statement, as a corollary. -/

/-- For `a > 0` and `b ≤ 1` (including `b = 0` and negative `b`, with `x/0 = 0`), the
constraint-3 quantity is not positive. -/
theorem C3val_nonpos {a b : ℝ} (ha : 0 < a) (hb : b ≤ 1) : lam b / (psi a b) ^ 3 ≤ 0 := by
  unfold lam psi
  rcases le_or_gt b 0 with hb0 | hb0
  · have h1 : 1 / b ≤ 0 := one_div_nonpos.mpr hb0
    have h2 : b / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hb0 ha.le
    have h3 : (b / a) ^ 3 ≤ 0 := Odd.pow_nonpos ⟨1, by norm_num⟩ h2
    exact div_nonpos_of_nonneg_of_nonpos (by linarith) h3
  · have h1 : 1 ≤ 1 / b := one_le_one_div hb0 hb
    have h3 : 0 ≤ (b / a) ^ 3 := pow_nonneg (div_nonneg hb0.le ha.le) 3
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) h3

/-- Constraint 3 forces `b > 1`. -/
theorem b_gt_one_of_C3 {a b : ℝ} (ha : 0 < a) (h : C3 a b) : 1 < b := by
  rw [C3_iff] at h
  by_contra hc
  have hc := not_lt.mp hc
  have := C3val_nonpos ha hc
  linarith [h.1]

/-- With `a ≤ 1.3256`, constraint 3 excludes `b > 2`. -/
theorem b_le_two_of_C3 {a b : ℝ} (ha0 : 0 < a) (hau : a ≤ 1.3256) (hb : 1 < b) (h : C3 a b) :
    b ≤ 2 := by
  obtain ⟨h1, _⟩ := C3_poly ha0 (by linarith) h
  by_contra hc
  have hc := not_le.mp hc
  have t : 32 * b - 48 ≤ b ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (b - 2)) (by nlinarith : (0 : ℝ) ≤ b ^ 2 + 4 * b + 12)]
  have ha3 : a ^ 3 ≤ 2.33 := (pow_le_pow_left₀ ha0.le hau 3).trans (by norm_num)
  have m : (b - 1) * a ^ 3 ≤ (b - 1) * 2.33 := mul_le_mul_of_nonneg_left ha3 (by linarith)
  linarith

/-- **Target 1b.** For all real `a`, `b` and all natural `p`, `k`: the five windows force
`p = 15`, `k = 29` and the accepted set. -/
theorem forward_strong (a b : ℝ) (p k : ℕ)
    (h : C1 a b p ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a k) :
    p = 15 ∧ k = 29 ∧ A a b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hal0, hau0⟩ := a_of_C2 h2
  have hk : k = 29 := k_of_C5 (by linarith) (by linarith) h5
  subst hk
  have h5' := C5_iff.mp h5
  obtain ⟨hal, hau⟩ := a_of_pow29 h5'.1 h5'.2
  have ha0 : 0 < a := by linarith
  have hb : 1 < b := b_gt_one_of_C3 ha0 h3
  have hb2 : b ≤ 2 := b_le_two_of_C3 ha0 hau hb h3
  obtain ⟨hp, hA⟩ := finish hb hb2 h1 h4 h5
  exact ⟨hp, rfl, hA⟩

/-- **Targets 1a and 5.** The forward direction in the shape of the public test: `1 < b < a`,
`p ∈ [3, 60]`, `k ∈ [2, 100]`, and the five windows. The ordering `1 < b < a` and the four
exponent bounds are NOT needed: the proof does not use them (they are bound with underscores),
and `forward_strong` is the same statement without them. They are kept in the signature only so
that it reads as the test does. (This statement was also proved under the name
`forward_test_shaped`; one name is kept.) -/
theorem test_shaped (a b : ℝ) (p k : ℕ) (_hb : 1 < b) (_hba : b < a)
    (_hp3 : 3 ≤ p) (_hp60 : p ≤ 60) (_hk2 : 2 ≤ k) (_hk100 : k ≤ 100)
    (h1 : C1 a b p) (h2 : C2 a) (h3 : C3 a b) (h4 : C4 a b) (h5 : C5 a k) :
    p = 15 ∧ k = 29 ∧ A a b :=
  forward_strong a b p k ⟨h1, h2, h3, h4, h5⟩

#print axioms forward_strong
#print axioms test_shaped

end ExclusionRegion
