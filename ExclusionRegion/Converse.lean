module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets
public import ExclusionRegion.Strong
public import ExclusionRegion.Box

@[expose] public section

namespace ExclusionRegion

open Real

/-! Target 1c, CONVERSE, and the IFF: the five windows are exactly the accepted set at the
exponents 15 and 29. -/

/-- **Target 1c.** Every point of the accepted set satisfies the five windows at `(15, 29)`. -/
theorem converse (a b : ℝ) (h : A a b) :
    C1 a b 15 ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a 29 := by
  obtain ⟨hal, hau, hbl, hbu, hb1, hba⟩ := box a b h
  rw [A_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hpi : 0 < π ^ 2 := by positivity
  have ha0 : 0 < a := by linarith
  have ha1 : 1 < a := by linarith
  have hb0 : 0 < b := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [C1_iff, le_div_iff₀ hpi, div_le_iff₀ hpi]
    exact ⟨h3, h4⟩
  · rw [C2_iff]
    unfold lam
    have e1 : 1 / a ≤ 1 / 1.3237586 := one_div_le_one_div_of_le (by norm_num) hal
    have n1 : (1 : ℝ) / 1.3237586 ≤ 0.7555 := by norm_num
    have e2 : 1 / 1.3255861 ≤ 1 / a := one_div_le_one_div_of_le ha0 hau
    have n2 : (0.7543 : ℝ) ≤ 1 / 1.3255861 := by norm_num
    have f1 := e1.trans n1
    have f2 := n2.trans e2
    constructor <;> linarith
  · rw [C3_iff, C3val_eq ha0 hb0, le_div_iff₀ (pow_pos hb0 4), div_le_iff₀ (pow_pos hb0 4)]
    have b4u : b ^ 4 ≤ (1.2220188 : ℝ) ^ 4 := pow_le_pow_left₀ hb0.le hbu 4
    have b4l : (1.2195208 : ℝ) ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ (by norm_num) hbl 4
    have a3l : (1.3237586 : ℝ) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by norm_num) hal 3
    have a3u : a ^ 3 ≤ (1.3255861 : ℝ) ^ 3 := pow_le_pow_left₀ ha0.le hau 3
    constructor
    · calc 0.2265858 * b ^ 4 ≤ 0.2265858 * (1.2220188 : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_left b4u (by norm_num)
        _ ≤ ((1.2195208 : ℝ) - 1) * (1.3237586 : ℝ) ^ 3 := by norm_num
        _ ≤ (b - 1) * a ^ 3 := mul_le_mul (by linarith) a3l (by norm_num) (by linarith)
    · calc (b - 1) * a ^ 3 ≤ ((1.2220188 : ℝ) - 1) * (1.3255861 : ℝ) ^ 3 :=
            mul_le_mul (by linarith) a3u (pow_nonneg ha0.le 3) (by norm_num)
        _ ≤ 0.2358342 * (1.2195208 : ℝ) ^ 4 := by norm_num
        _ ≤ 0.2358342 * b ^ 4 := mul_le_mul_of_nonneg_left b4l (by norm_num)
  · rw [C4_iff]
    constructor
    · have hge := C4val_ge (aU := 1.3255861) (β := 1.2195208) (by norm_num) hbl (by linarith)
        ha1 hau (by norm_num)
      have n : (0.11564 : ℝ) ≤ ((1.2195208 : ℝ) - 1) ^ 3 * 1.3255861 ^ 5
          / (4 * (1.3255861 - 1) ^ 3 * 1.2195208 ^ 5) := by norm_num
      exact n.trans hge
    · have hle := C4val_le (aL := 1.3237586) (β := 1.2220188) (by norm_num) hal (by linarith)
        hb1 hbu (by norm_num)
      have n : ((1.2220188 : ℝ) - 1) ^ 3 * 1.3237586 ^ 5
          / (4 * (1.3237586 - 1) ^ 3 * 1.2220188 ^ 5) ≤ 0.12036 := by norm_num
      exact hle.trans n
  · rw [C5_iff]
    exact ⟨h1, h2⟩

/-- **Target 1 (SET, iff).** For all real `a`, `b` and natural `p`, `k`, the five windows hold
exactly when `p = 15`, `k = 29` and `(a, b)` is in the accepted set. -/
theorem exclusion_iff (a b : ℝ) (p k : ℕ) :
    (C1 a b p ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a k) ↔ (p = 15 ∧ k = 29 ∧ A a b) := by
  constructor
  · exact forward_strong a b p k
  · rintro ⟨hp, hk, hA⟩
    subst hp
    subst hk
    exact converse a b hA

#print axioms converse
#print axioms exclusion_iff

end ExclusionRegion
