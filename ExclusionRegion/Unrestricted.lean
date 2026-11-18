module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets
public import ExclusionRegion.Forward
public import ExclusionRegion.Strong
public import ExclusionRegion.Companion
public import ExclusionRegion.Converse

@[expose] public section

namespace ExclusionRegion

open Real

/-! UNRESTRICTED four-constraint statements. For all real `a`, `b` and all natural `p`, `k`
(no ordering, no sign condition, no exponent range):

* `strong_drop_C3`: constraints 1, 2, 4, 5 force `p = 15`, `k = 29` and the accepted set;
* `strong_drop_C2`: constraints 1, 3, 4, 5 force `p = 15`, `k = 29` and the accepted set.

Constraint 4 cannot be dropped this way (`control_i`); `companion_drop_C4_strong` keeps `b < a`.

Coordinates: `lam a`, `lam b` and `psi a b` are used as they stand in the definitions, with
`psi a b * (1 - lam b) = 1 - lam a` and `a * b * ((1 - lam a) * (1 - lam b)) = 1`. -/

/-! ### General tools -/

theorem base_le_of_pow_le {z c : ℝ} {n : ℕ} (hn : n ≠ 0) (hc : 0 ≤ c) (h : z ^ n ≤ c ^ n) :
    z ≤ c := by
  by_contra hne
  have := pow_lt_pow_left₀ (not_le.mp hne) hc hn
  linarith

theorem le_base_of_pow_le {z c : ℝ} {n : ℕ} (hn : n ≠ 0) (hz : 0 ≤ z) (h : c ^ n ≤ z ^ n) :
    c ≤ z := by
  by_contra hne
  have := pow_lt_pow_left₀ (not_le.mp hne) hz hn
  linarith

/-- If `L ≤ |ab| ≤ U`, with `U^n` below the constraint-1 window and `L^(n+1)` above it, then no
exponent meets the window. -/
theorem not_C1_of_abs {a b L U : ℝ} {p : ℕ} (n : ℕ) (hL : 1 ≤ L) (hl : L ≤ |a * b|)
    (hu : |a * b| ≤ U) (hUn : U ^ n < 136.35082 * 3.14 ^ 2)
    (hLn : 137.72118 * 3.15 ^ 2 < L ^ (n + 1)) : ¬ C1 a b p := by
  intro h
  rw [C1_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hpi : 0 < π ^ 2 := by positivity
  rw [le_div_iff₀ hpi] at h1
  rw [div_le_iff₀ hpi] at h2
  have hpl : (3.14 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d2.le 2
  have hpu : π ^ 2 ≤ (3.15 : ℝ) ^ 2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
  have e4 : (136.35082 : ℝ) * 3.14 ^ 2 ≤ 136.35082 * π ^ 2 :=
    mul_le_mul_of_nonneg_left hpl (by norm_num)
  have e5 : (137.72118 : ℝ) * π ^ 2 ≤ 137.72118 * 3.15 ^ 2 :=
    mul_le_mul_of_nonneg_left hpu (by norm_num)
  have hz1 : 1 ≤ |a * b| := hL.trans hl
  have hz0 : 0 ≤ |a * b| := abs_nonneg _
  have hpos : 0 < (a * b) ^ p := lt_of_lt_of_le (by positivity) h1
  have habs : |a * b| ^ p = (a * b) ^ p := by rw [← abs_pow, abs_of_pos hpos]
  rcases Nat.lt_or_ge n p with hlt | hge
  · have e1 : |a * b| ^ (n + 1) ≤ |a * b| ^ p := pow_le_pow_right₀ hz1 (by omega)
    have e2 : L ^ (n + 1) ≤ |a * b| ^ (n + 1) := pow_le_pow_left₀ (by linarith) hl (n + 1)
    rw [habs] at e1
    exact lt_irrefl _ (lt_of_lt_of_le hLn (e2.trans (e1.trans (h2.trans e5))))
  · have e1 : |a * b| ^ p ≤ |a * b| ^ n := pow_le_pow_right₀ hz1 hge
    have e2 : |a * b| ^ n ≤ U ^ n := pow_le_pow_left₀ hz0 hu n
    rw [habs] at e1
    exact lt_irrefl _ (lt_of_le_of_lt (e1.trans e2) (lt_of_lt_of_le hUn (e4.trans h1)))

theorem psi_mul_self {a b : ℝ} (ha : a ≠ 0) : b = psi a b * a := by
  unfold psi
  field_simp

theorem mul_eq_psi_mul {a b : ℝ} (ha : a ≠ 0) : a * b = psi a b * (a * a) := by
  calc a * b = a * (psi a b * a) := congrArg (fun t => a * t) (psi_mul_self ha)
    _ = psi a b * (a * a) := by ring

theorem not_C3_a_zero (b : ℝ) : ¬ C3 0 b := by
  rw [C3_iff]; unfold lam psi; norm_num

theorem not_C3_b_zero (a : ℝ) : ¬ C3 a 0 := by
  rw [C3_iff]; unfold lam psi; norm_num

theorem not_C4_b_zero (a : ℝ) : ¬ C4 a 0 := by
  rw [C4_iff]; unfold lam psi; norm_num

/-! ### Constraint 3 dropped: constraints 1, 2, 4, 5 -/

/-- Constraints 2 and 4, cross-multiplied: `lam b ^ 3` between two multiples of `psi ^ 2`. -/
theorem C4_psi_of_C2 {a b : ℝ} (h2 : C2 a) (hψ : psi a b ≠ 0) (h4 : C4 a b) :
    0.0063945 * (psi a b) ^ 2 ≤ (lam b) ^ 3 ∧ (lam b) ^ 3 ≤ 0.0075045 * (psi a b) ^ 2 := by
  rw [C2_iff] at h2
  rw [C4_iff] at h4
  obtain ⟨x1, x2⟩ := h2
  obtain ⟨h4l, h4u⟩ := h4
  have hψ2 : 0 < (psi a b) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hψ))
  have hx3l : (0.240002 : ℝ) ^ 3 ≤ (lam a) ^ 3 := pow_le_pow_left₀ (by norm_num) x1 3
  have hx3u : (lam a) ^ 3 ≤ (0.249798 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) x2 3
  have hx3 : 0 < (lam a) ^ 3 := pow_pos (by linarith) 3
  have hden : 0 < 4 * (lam a) ^ 3 * (psi a b) ^ 2 := mul_pos (mul_pos (by norm_num) hx3) hψ2
  rw [le_div_iff₀ hden] at h4l
  rw [div_le_iff₀ hden] at h4u
  have n1 : (0.0138243 : ℝ) ≤ 0.240002 ^ 3 := by norm_num
  have n2 : (0.249798 : ℝ) ^ 3 ≤ 0.0155873 := by norm_num
  have m1 : (0.0138243 : ℝ) * (psi a b) ^ 2 ≤ (lam a) ^ 3 * (psi a b) ^ 2 :=
    mul_le_mul_of_nonneg_right (n1.trans hx3l) hψ2.le
  have m2 : (lam a) ^ 3 * (psi a b) ^ 2 ≤ 0.0155873 * (psi a b) ^ 2 :=
    mul_le_mul_of_nonneg_right (hx3u.trans n2) hψ2.le
  constructor <;> linarith

/-- With constraint 2, constraint 4 fails for `0 < b ≤ 1`. -/
theorem not_C4_of_b_le_one {a b : ℝ} (h2 : C2 a) (hb0 : 0 < b) (hb1 : b ≤ 1) : ¬ C4 a b := by
  intro h4
  rw [C2_iff] at h2
  rw [C4_iff] at h4
  have h1 : 1 ≤ 1 / b := one_le_one_div hb0 hb1
  have hy : lam b ≤ 0 := by unfold lam; linarith
  have hy3 : lam b ^ 3 ≤ 0 := Odd.pow_nonpos ⟨1, by norm_num⟩ hy
  have hden : 0 ≤ 4 * lam a ^ 3 * psi a b ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith [h2.1]) 3)) (sq_nonneg _)
  have := div_nonpos_of_nonpos_of_nonneg hy3 hden
  linarith [h4.1]

/-- With constraint 2 and `b > 2`, constraint 4 puts `ab` in `[12, 25]`, where no power meets the
constraint-1 window (`25² < 1344 < 1367 < 12³`). This is the branch `b ∈ [14.05, 14.45]`. -/
theorem not_C1_of_C4_big {a b : ℝ} {p : ℕ} (h2 : C2 a) (hb : 2 < b) (h4 : C4 a b) :
    ¬ C1 a b p := by
  obtain ⟨hal, hau⟩ := a_of_C2 h2
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hψ0 : 0 < psi a b := by unfold psi; exact div_pos hb0 ha0
  have hbψ : b = psi a b * a := psi_mul_self ha0.ne'
  obtain ⟨c1, c2⟩ := C4_psi_of_C2 h2 hψ0.ne' h4
  have hv0 : 0 < 1 / b := one_div_pos.mpr hb0
  have hv : 1 / b ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hb.le
  have hy1 : lam b ≤ 1 := by unfold lam; linarith
  have hy2 : 1 / 2 ≤ lam b := by unfold lam; linarith
  have hy3u : lam b ^ 3 ≤ 1 := pow_le_one₀ (by linarith) hy1
  have hy3l : (0.125 : ℝ) ≤ lam b ^ 3 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hy2 3)
  have hψu : psi a b ≤ 12.51 :=
    base_le_of_pow_le (n := 2) (by norm_num) (by norm_num)
      (le_trans (by linarith : psi a b ^ 2 ≤ 156.5) (by norm_num))
  have hψl : 4.08 ≤ psi a b :=
    le_base_of_pow_le (n := 2) (by norm_num) hψ0.le
      (le_trans (by norm_num) (by linarith : (16.65 : ℝ) ≤ psi a b ^ 2))
  have hb5 : 5 ≤ b := by
    have := mul_le_mul hψl hal (by norm_num) hψ0.le
    linarith
  have hv5 : 1 / b ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hb5
  have hy8 : 0.8 ≤ lam b := by unfold lam; linarith
  have hy83 : (0.512 : ℝ) ≤ lam b ^ 3 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 0.8) hy8 3)
  have hψl2 : 8.2 ≤ psi a b :=
    le_base_of_pow_le (n := 2) (by norm_num) hψ0.le
      (le_trans (by norm_num) (by linarith : (68 : ℝ) ≤ psi a b ^ 2))
  have haa_l : (1.3157 : ℝ) * 1.3157 ≤ a * a := mul_le_mul hal hal (by norm_num) ha0.le
  have haa_u : a * a ≤ 1.333 * 1.333 := mul_le_mul hau hau ha0.le (by norm_num)
  have hab : a * b = psi a b * (a * a) := mul_eq_psi_mul ha0.ne'
  have hab0 : 0 < a * b := mul_pos ha0 hb0
  have hL : 12 ≤ |a * b| := by
    have := mul_le_mul hψl2 haa_l (by norm_num) hψ0.le
    rw [abs_of_pos hab0, hab]
    exact le_trans (by norm_num) this
  have hU : |a * b| ≤ 25 := by
    have := mul_le_mul hψu haa_u (mul_nonneg ha0.le ha0.le) (by norm_num)
    rw [abs_of_pos hab0, hab]
    exact le_trans this (by norm_num)
  exact not_C1_of_abs 2 (by norm_num) hL hU (by norm_num) (by norm_num)

/-- With constraint 2 and `b < 0`, constraint 4 puts `|ab|` in `[12, 25]`, where no power meets
the constraint-1 window. This is the branch `b ∈ [-17.49, -17.09]`. -/
theorem not_C1_of_C4_neg {a b : ℝ} {p : ℕ} (h2 : C2 a) (hb : b < 0) (h4 : C4 a b) :
    ¬ C1 a b p := by
  obtain ⟨hal, hau⟩ := a_of_C2 h2
  have ha0 : 0 < a := by linarith
  have hψ0 : psi a b < 0 := by unfold psi; exact div_neg_of_neg_of_pos hb ha0
  have hbψ : b = psi a b * a := psi_mul_self ha0.ne'
  obtain ⟨c1, c2⟩ := C4_psi_of_C2 h2 hψ0.ne h4
  have hz0 : 0 < -psi a b := by linarith
  have hz2 : (-psi a b) ^ 2 = psi a b ^ 2 := by ring
  have hv0 : 1 / b < 0 := one_div_neg.mpr hb
  have hy1 : 1 ≤ lam b := by unfold lam; linarith
  have hy3l : 1 ≤ lam b ^ 3 := one_le_pow₀ hy1
  have hzl : 11.5 ≤ -psi a b :=
    le_base_of_pow_le (n := 2) (by norm_num) hz0.le
      (le_trans (by norm_num) (by rw [hz2]; linarith : (133 : ℝ) ≤ (-psi a b) ^ 2))
  have hb15 : 15 ≤ -b := by
    have := mul_le_mul hzl hal (by norm_num) hz0.le
    linarith
  have hv15 : 1 / (-b) ≤ 1 / 15 := one_div_le_one_div_of_le (by norm_num) hb15
  have e15 : 1 / (-b) = -(1 / b) := by
    have hb' : b ≠ 0 := hb.ne
    field_simp
  have hy2 : lam b ≤ 16 / 15 := by unfold lam; linarith
  have hy3u : lam b ^ 3 ≤ 1.2137 :=
    le_trans (pow_le_pow_left₀ (by linarith) hy2 3) (by norm_num)
  have hzu : -psi a b ≤ 13.8 :=
    base_le_of_pow_le (n := 2) (by norm_num) (by norm_num)
      (le_trans (by rw [hz2]; linarith : (-psi a b) ^ 2 ≤ 190) (by norm_num))
  have haa_l : (1.3157 : ℝ) * 1.3157 ≤ a * a := mul_le_mul hal hal (by norm_num) ha0.le
  have haa_u : a * a ≤ 1.333 * 1.333 := mul_le_mul hau hau ha0.le (by norm_num)
  have hab : a * b = psi a b * (a * a) := mul_eq_psi_mul ha0.ne'
  have habn : a * b < 0 := mul_neg_of_pos_of_neg ha0 hb
  have habs : |a * b| = -psi a b * (a * a) := by
    rw [abs_of_neg habn, hab]; ring
  have hL : 12 ≤ |a * b| := by
    have := mul_le_mul hzl haa_l (by norm_num) hz0.le
    rw [habs]
    exact le_trans (by norm_num) this
  have hU : |a * b| ≤ 25 := by
    have := mul_le_mul hzu haa_u (mul_nonneg ha0.le ha0.le) (by norm_num)
    rw [habs]
    exact le_trans this (by norm_num)
  exact not_C1_of_abs 2 (by norm_num) hL hU (by norm_num) (by norm_num)

/-- **Constraint 3 dropped, unrestricted.** For all real `a`, `b` and all natural `p`, `k`:
constraints 1, 2, 4, 5 force `p = 15`, `k = 29` and the accepted set. No ordering, no sign
condition, no exponent range. -/
theorem strong_drop_C3 (a b : ℝ) (p k : ℕ) (h : C1 a b p ∧ C2 a ∧ C4 a b ∧ C5 a k) :
    p = 15 ∧ k = 29 ∧ A a b := by
  obtain ⟨h1, h2, h4, h5⟩ := h
  rcases lt_trichotomy b 0 with hb | hb | hb
  · exact absurd h1 (not_C1_of_C4_neg h2 hb h4)
  · subst hb
    exact absurd h4 (not_C4_b_zero a)
  · rcases le_or_gt b 1 with hb1 | hb1
    · exact absurd h4 (not_C4_of_b_le_one h2 hb hb1)
    · rcases le_or_gt b 2 with hb2 | hb2
      · exact forward_core hb1 hb2 h1 h2 h4 h5
      · exact absurd h1 (not_C1_of_C4_big h2 hb2 h4)

/-! ### Constraint 2 dropped: constraints 1, 3, 4, 5 -/

/-- Constraints 3 and 4 exclude `a < 0`. -/
theorem not_C3_C4_of_a_neg {a b : ℝ} (ha : a < 0) (h3 : C3 a b) (h4 : C4 a b) : False := by
  have hua : 1 / a < 0 := one_div_neg.mpr ha
  have hxa : 1 < lam a := by unfold lam; linarith
  have hxa3 : 0 < lam a ^ 3 := pow_pos (by linarith) 3
  rcases lt_trichotomy b 0 with hb | hb | hb
  · -- `a < 0`, `b < 0`: constraint 3 gives `psi ≥ 1.6`, then the constraint-4 value is `< 0.11564`
    have hψ : 0 < psi a b := by unfold psi; exact div_pos_of_neg_of_neg hb ha
    have hψ3 : 0 < psi a b ^ 3 := pow_pos hψ 3
    have hvb : 1 / b < 0 := one_div_neg.mpr hb
    have hyb : 1 < lam b := by unfold lam; linarith
    rw [C3_iff] at h3
    rw [C4_iff] at h4
    have h3u := h3.2
    rw [div_le_iff₀ hψ3] at h3u
    have hψ16 : 1.6 ≤ psi a b :=
      le_base_of_pow_le (n := 3) (by norm_num) hψ.le
        (le_trans (by norm_num) (by linarith : (4.1 : ℝ) ≤ psi a b ^ 3))
    have hbψ : b = psi a b * a := psi_mul_self ha.ne
    have hba : b < a := by
      have := mul_le_mul_of_nonpos_right hψ16 ha.le
      linarith
    have hinv : 1 / a < 1 / b := one_div_lt_one_div_of_neg_of_lt ha hba
    have hle : lam b ≤ lam a := by unfold lam; linarith
    have hle3 : lam b ^ 3 ≤ lam a ^ 3 := pow_le_pow_left₀ (by linarith) hle 3
    have hψ2 : (2.56 : ℝ) ≤ psi a b ^ 2 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1.6) hψ16 2)
    have hden : 0 < 4 * lam a ^ 3 * psi a b ^ 2 :=
      mul_pos (mul_pos (by norm_num) hxa3) (pow_pos hψ 2)
    have h4l := h4.1
    rw [le_div_iff₀ hden] at h4l
    have m : lam a ^ 3 * 2.56 ≤ lam a ^ 3 * psi a b ^ 2 :=
      mul_le_mul_of_nonneg_left hψ2 hxa3.le
    linarith
  · subst hb
    exact not_C3_b_zero a h3
  · -- `a < 0 < b`: constraint 3 needs `lam b < 0`, and then the constraint-4 value is `≤ 0`
    have hψ : psi a b < 0 := by unfold psi; exact div_neg_of_pos_of_neg hb ha
    have hψ3 : psi a b ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ hψ
    rw [C3_iff] at h3
    rw [C4_iff] at h4
    have hyb : lam b < 0 := by
      by_contra hc
      have := div_nonpos_of_nonneg_of_nonpos (not_lt.mp hc) hψ3.le
      linarith [h3.1]
    have hyb3 : lam b ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ hyb
    have hden : 0 ≤ 4 * lam a ^ 3 * psi a b ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hxa3.le) (sq_nonneg _)
    have := div_nonpos_of_nonpos_of_nonneg hyb3.le hden
    linarith [h4.1]

/-- Constraints 3 and 4 exclude `0 < a ≤ 1`. -/
theorem not_C3_C4_of_a_le_one {a b : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (h3 : C3 a b)
    (h4 : C4 a b) : False := by
  have hb : 1 < b := b_gt_one_of_C3 ha0 h3
  rw [C4_iff] at h4
  have hxa : lam a ≤ 0 := by
    have := one_le_one_div ha0 ha1
    unfold lam; linarith
  have hyb : 0 ≤ lam b := by
    have h1 : 1 / b ≤ 1 := (div_le_one (by linarith : (0 : ℝ) < b)).mpr hb.le
    unfold lam; linarith
  have hx3 : lam a ^ 3 ≤ 0 := Odd.pow_nonpos ⟨1, by norm_num⟩ hxa
  have hden : 4 * lam a ^ 3 * psi a b ^ 2 ≤ 0 := by
    have h2 : 0 ≤ psi a b ^ 2 := sq_nonneg _
    have h3' : lam a ^ 3 * psi a b ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx3 h2
    linarith
  have := div_nonpos_of_nonneg_of_nonpos (pow_nonneg hyb 3) hden
  linarith [h4.1]

/-- Constraints 3 and 4 alone force `1 < a` and `1 < b`, for all real `a`, `b`. -/
theorem one_lt_of_C3_C4 {a b : ℝ} (h3 : C3 a b) (h4 : C4 a b) : 1 < a ∧ 1 < b := by
  have ha : 1 < a := by
    by_contra hc
    have hc := not_lt.mp hc
    rcases lt_trichotomy a 0 with h | h | h
    · exact not_C3_C4_of_a_neg h h3 h4
    · subst h
      exact not_C3_a_zero b h3
    · exact not_C3_C4_of_a_le_one h hc h3 h4
  exact ⟨ha, b_gt_one_of_C3 (by linarith) h3⟩

/-- `y(1-y)³` is nonincreasing on `[1/4, 1]`. -/
theorem quartic_anti {y z : ℝ} (hy : 1 / 4 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    z * (1 - z) ^ 3 ≤ y * (1 - y) ^ 3 := by
  obtain ⟨p, rfl⟩ : ∃ p, y = 1 - p := ⟨1 - y, by ring⟩
  obtain ⟨q, rfl⟩ : ∃ q, z = 1 - q := ⟨1 - z, by ring⟩
  have hp : p ≤ 3 / 4 := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hqp : q ≤ p := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hq : q ≤ 3 / 4 := by linarith
  have e : (1 - p) * (1 - (1 - p)) ^ 3 - (1 - q) * (1 - (1 - q)) ^ 3
      = (p - q) * (p ^ 2 + p * q + q ^ 2 - (p + q) * (p ^ 2 + q ^ 2)) := by ring
  have t1 : p ^ 2 * p ≤ p ^ 2 * (3 / 4) := mul_le_mul_of_nonneg_left hp (sq_nonneg p)
  have t2 : q ^ 2 * q ≤ q ^ 2 * (3 / 4) := mul_le_mul_of_nonneg_left hq (sq_nonneg q)
  have t3 : p * q * (p + q) ≤ p * q * (3 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hp0 hq0)
  have t4 : 0 ≤ (p - q) ^ 2 := sq_nonneg _
  have hG : 0 ≤ p ^ 2 + p * q + q ^ 2 - (p + q) * (p ^ 2 + q ^ 2) := by
    nlinarith [t1, t2, t3, t4]
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ p - q) hG
  linarith

/-- Constraints 3 (lower) and 4 (upper) with `psi` eliminated: `t² y⁷ ≤ 64 s³ x⁹`. -/
theorem elim_psi_lower {x y ψ t s : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hψ : 0 ≤ ψ) (ht : 0 ≤ t)
    (hs : 0 ≤ s) (h3 : t * ψ ^ 3 ≤ y) (h4 : y ^ 3 ≤ s * (4 * x ^ 3 * ψ ^ 2)) :
    t ^ 2 * y ^ 7 ≤ 64 * s ^ 3 * x ^ 9 := by
  have c4 := pow_le_pow_left₀ (pow_nonneg hy.le 3) h4 3
  have c3 := pow_le_pow_left₀ (mul_nonneg ht (pow_nonneg hψ 3)) h3 2
  have hn : 0 ≤ 64 * s ^ 3 * x ^ 9 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 3)) (pow_nonneg hx 9)
  have key : t ^ 2 * y ^ 7 * y ^ 2 ≤ 64 * s ^ 3 * x ^ 9 * y ^ 2 := by
    calc t ^ 2 * y ^ 7 * y ^ 2 = t ^ 2 * (y ^ 3) ^ 3 := by ring
      _ ≤ t ^ 2 * (s * (4 * x ^ 3 * ψ ^ 2)) ^ 3 := mul_le_mul_of_nonneg_left c4 (sq_nonneg t)
      _ = 64 * s ^ 3 * x ^ 9 * (t * ψ ^ 3) ^ 2 := by ring
      _ ≤ 64 * s ^ 3 * x ^ 9 * y ^ 2 := mul_le_mul_of_nonneg_left c3 hn
  exact le_of_mul_le_mul_right key (pow_pos hy 2)

/-- Constraints 3 (upper) and 4 (lower) with `psi` eliminated: `64 s³ x⁹ ≤ t² y⁷`. -/
theorem elim_psi_upper {x y ψ t s : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hs : 0 ≤ s)
    (h3 : y ≤ t * ψ ^ 3) (h4 : s * (4 * x ^ 3 * ψ ^ 2) ≤ y ^ 3) :
    64 * s ^ 3 * x ^ 9 ≤ t ^ 2 * y ^ 7 := by
  have h0 : 0 ≤ s * (4 * x ^ 3 * ψ ^ 2) :=
    mul_nonneg hs (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx 3)) (sq_nonneg ψ))
  have c4 := pow_le_pow_left₀ h0 h4 3
  have c3 := pow_le_pow_left₀ hy.le h3 2
  have hn : 0 ≤ 64 * s ^ 3 * x ^ 9 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hs 3)) (pow_nonneg hx 9)
  have key : 64 * s ^ 3 * x ^ 9 * y ^ 2 ≤ t ^ 2 * y ^ 7 * y ^ 2 := by
    calc 64 * s ^ 3 * x ^ 9 * y ^ 2 ≤ 64 * s ^ 3 * x ^ 9 * (t * ψ ^ 3) ^ 2 :=
          mul_le_mul_of_nonneg_left c3 hn
      _ = t ^ 2 * (s * (4 * x ^ 3 * ψ ^ 2)) ^ 3 := by ring
      _ ≤ t ^ 2 * (y ^ 3) ^ 3 := mul_le_mul_of_nonneg_left c4 (sq_nonneg t)
      _ = t ^ 2 * y ^ 7 * y ^ 2 := by ring
  exact le_of_mul_le_mul_right key (pow_pos hy 2)

/-- One interval of the middle exclusion: for `y ∈ [y0, y1] ⊆ [1/4, 1]`, constraint 3 (upper)
caps `x` at `X`, and then `0.46 y⁷ ≤ x⁹` fails. -/
theorem mid_step {x y y0 y1 X : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1)
    (hq : 1 / 4 ≤ y0) (h1 : y1 ≤ 1)
    (hA : 0.46 * y ^ 7 ≤ x ^ 9)
    (hC : y * (1 - y) ^ 3 ≤ 0.2358342 * (1 - x) ^ 3)
    (n1 : 0.2358342 * (1 - X) ^ 3 ≤ y1 * (1 - y1) ^ 3)
    (n2 : X ^ 9 < 0.46 * y0 ^ 7) : False := by
  have m := quartic_anti (hq.trans hy0) hy1 h1
  have hX : x ≤ X := by
    by_contra hc
    have hc := not_le.mp hc
    have h3 := pow_lt_pow_left₀ (by linarith : 1 - x < 1 - X) (by linarith : (0 : ℝ) ≤ 1 - x)
      (by norm_num : (3 : ℕ) ≠ 0)
    have h4 : 0.2358342 * (1 - x) ^ 3 < 0.2358342 * (1 - X) ^ 3 :=
      mul_lt_mul_of_pos_left h3 (by norm_num)
    exact lt_irrefl _ (lt_of_lt_of_le h4 (n1.trans (m.trans hC)))
  have e1 : x ^ 9 ≤ X ^ 9 := pow_le_pow_left₀ hx0 hX 9
  have e2 : y0 ^ 7 ≤ y ^ 7 := pow_le_pow_left₀ (by linarith) hy0 7
  have e3 : 0.46 * y0 ^ 7 ≤ 0.46 * y ^ 7 := mul_le_mul_of_nonneg_left e2 (by norm_num)
  exact lt_irrefl _ (lt_of_lt_of_le n2 (e3.trans (hA.trans e1)))

/-- The second patch, in the coordinates `x = lam a`, `y = lam b`, `ψ = psi a b`: for
`1/4 < y < 1` (that is `b > 4/3`), constraints 3 and 4 put `(1-x)(1-y) = 1/(ab)` in
`[0.002, 1/45]`. -/
theorem patch2_core {x y ψ : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hy : 1 / 4 < y) (hy1 : y < 1)
    (hψ : ψ * (1 - y) = 1 - x)
    (h3l : 0.2265858 * ψ ^ 3 ≤ y) (h3u : y ≤ 0.2358342 * ψ ^ 3)
    (h4l : 0.11564 * (4 * x ^ 3 * ψ ^ 2) ≤ y ^ 3)
    (h4u : y ^ 3 ≤ 0.12036 * (4 * x ^ 3 * ψ ^ 2)) :
    0.002 ≤ (1 - x) * (1 - y) ∧ (1 - x) * (1 - y) ≤ 1 / 45 := by
  have hy0 : 0 < y := by linarith
  have hv : 0 < 1 - y := by linarith
  have hu : 0 < 1 - x := by linarith
  have hψ0 : 0 < ψ := by
    rw [(eq_div_iff hv.ne').mpr hψ]
    exact div_pos hu hv
  have hy7n : 0 ≤ y ^ 7 := pow_nonneg hy0.le 7
  have hA0 := elim_psi_lower (t := 0.2265858) (s := 0.12036) hx0.le hy0 hψ0.le (by norm_num)
    (by norm_num) h3l h4u
  have hB0 := elim_psi_upper (t := 0.2358342) (s := 0.11564) hx0.le hy0 (by norm_num)
    h3u h4l
  -- `0.46 y⁷ ≤ x⁹ ≤ 0.562 y⁷`
  have hA : 0.46 * y ^ 7 ≤ x ^ 9 := by
    have c : (0.46 : ℝ) * (64 * 0.12036 ^ 3) ≤ 0.2265858 ^ 2 := by norm_num
    have c' := mul_le_mul_of_nonneg_right c hy7n
    refine le_of_mul_le_mul_left ?_ (by norm_num : (0 : ℝ) < 64 * 0.12036 ^ 3)
    calc (64 : ℝ) * 0.12036 ^ 3 * (0.46 * y ^ 7) = 0.46 * (64 * 0.12036 ^ 3) * y ^ 7 := by ring
      _ ≤ 0.2265858 ^ 2 * y ^ 7 := c'
      _ ≤ 64 * 0.12036 ^ 3 * x ^ 9 := hA0
  have hB : x ^ 9 ≤ 0.562 * y ^ 7 := by
    have c : (0.2358342 : ℝ) ^ 2 ≤ 64 * 0.11564 ^ 3 * 0.562 := by norm_num
    have c' := mul_le_mul_of_nonneg_right c hy7n
    refine le_of_mul_le_mul_left ?_ (by norm_num : (0 : ℝ) < 64 * 0.11564 ^ 3)
    calc (64 : ℝ) * 0.11564 ^ 3 * x ^ 9 ≤ 0.2358342 ^ 2 * y ^ 7 := hB0
      _ ≤ 64 * 0.11564 ^ 3 * 0.562 * y ^ 7 := c'
      _ = 64 * 0.11564 ^ 3 * (0.562 * y ^ 7) := by ring
  -- constraint 3 in `(x, y)`
  have hv3 : 0 ≤ (1 - y) ^ 3 := pow_nonneg hv.le 3
  have eψ : ψ ^ 3 * (1 - y) ^ 3 = (1 - x) ^ 3 := by rw [← mul_pow, hψ]
  have hCu : y * (1 - y) ^ 3 ≤ 0.2358342 * (1 - x) ^ 3 := by
    have := mul_le_mul_of_nonneg_right h3u hv3
    calc y * (1 - y) ^ 3 ≤ 0.2358342 * ψ ^ 3 * (1 - y) ^ 3 := this
      _ = 0.2358342 * (ψ ^ 3 * (1 - y) ^ 3) := by ring
      _ = 0.2358342 * (1 - x) ^ 3 := by rw [eψ]
  have hCl : 0.2265858 * (1 - x) ^ 3 ≤ y * (1 - y) ^ 3 := by
    have := mul_le_mul_of_nonneg_right h3l hv3
    calc 0.2265858 * (1 - x) ^ 3 = 0.2265858 * (ψ ^ 3 * (1 - y) ^ 3) := by rw [eψ]
      _ = 0.2265858 * ψ ^ 3 * (1 - y) ^ 3 := by ring
      _ ≤ y * (1 - y) ^ 3 := this
  constructor
  · -- `x ≤ 0.94`, then `1 - y ≥ 0.0365`
    have hy7 : y ^ 7 ≤ 1 := pow_le_one₀ hy0.le hy1.le
    have hx94 : x ≤ 0.94 :=
      base_le_of_pow_le (n := 9) (by norm_num) (by norm_num)
        (hB.trans ((mul_le_mul_of_nonneg_left hy7 (by norm_num)).trans (by norm_num)))
    have h06 : (0.06 : ℝ) ^ 3 ≤ (1 - x) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    have hyv : y * (1 - y) ^ 3 ≤ 1 * (1 - y) ^ 3 := mul_le_mul_of_nonneg_right hy1.le hv3
    have hv365 : 0.0365 ≤ 1 - y :=
      le_base_of_pow_le (n := 3) (by norm_num) hv.le
        ((by norm_num : (0.0365 : ℝ) ^ 3 ≤ 0.2265858 * 0.06 ^ 3).trans
          ((mul_le_mul_of_nonneg_left h06 (by norm_num)).trans
            (hCl.trans (hyv.trans (one_mul _).le))))
    have := mul_le_mul (by linarith : (0.06 : ℝ) ≤ 1 - x) hv365 (by norm_num) hu.le
    exact le_trans (by norm_num) this
  · -- `y > 7/8` (six intervals), then `x ≥ 0.826`
    have hy78 : 7 / 8 < y := by
      by_contra hc
      have hc := not_lt.mp hc
      rcases le_or_gt y 0.44 with c1 | c1
      · exact mid_step (y0 := 1 / 4) (y1 := 0.44) (X := 0.311) hx0.le hx1.le hy.le c1
          (by norm_num) (by norm_num) hA hCu (by norm_num) (by norm_num)
      rcases le_or_gt y 0.625 with c2 | c2
      · exact mid_step (y0 := 0.44) (y1 := 0.625) (X := 0.482) hx0.le hx1.le c1.le c2
          (by norm_num) (by norm_num) hA hCu (by norm_num) (by norm_num)
      rcases le_or_gt y 0.75 with c3 | c3
      · exact mid_step (y0 := 0.625) (y1 := 0.75) (X := 0.633) hx0.le hx1.le c2.le c3
          (by norm_num) (by norm_num) hA hCu (by norm_num) (by norm_num)
      rcases le_or_gt y 0.82 with c4 | c4
      · exact mid_step (y0 := 0.75) (y1 := 0.82) (X := 0.728) hx0.le hx1.le c3.le c4
          (by norm_num) (by norm_num) hA hCu (by norm_num) (by norm_num)
      rcases le_or_gt y 0.86 with c5 | c5
      · exact mid_step (y0 := 0.82) (y1 := 0.86) (X := 0.785) hx0.le hx1.le c4.le c5
          (by norm_num) (by norm_num) hA hCu (by norm_num) (by norm_num)
      · exact mid_step (y0 := 0.86) (y1 := 7 / 8) (X := 0.807) hx0.le hx1.le c5.le hc
          (by norm_num) (by norm_num) hA hCu (by norm_num) (by norm_num)
    have hx826 : 0.826 ≤ x :=
      le_base_of_pow_le (n := 9) (by norm_num) hx0.le
        ((by norm_num : (0.826 : ℝ) ^ 9 ≤ 0.46 * (7 / 8) ^ 7).trans
          ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hy78.le 7)
            (by norm_num)).trans hA))
    have := mul_le_mul (by linarith : 1 - x ≤ 0.174) (by linarith : 1 - y ≤ 1 / 8) hv.le
      (by norm_num)
    exact le_trans this (by norm_num)

/-- With `1 < a` and `b > 4/3`, constraints 3 and 4 put `ab` in `[45, 500]`, where no power meets
the constraint-1 window (`500 < 1344 < 1367 < 45²`). This is the second patch
`a ∈ [6.60, 8.60]`, `b ∈ [10.47, 13.58]`. -/
theorem not_C1_of_C3_C4_big {a b : ℝ} {p : ℕ} (ha : 1 < a) (hb : 4 / 3 < b) (h3 : C3 a b)
    (h4 : C4 a b) : ¬ C1 a b p := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [C3_iff] at h3
  rw [C4_iff] at h4
  have hψ0 : 0 < psi a b := by unfold psi; exact div_pos hb0 ha0
  have hua : 1 / a < 1 := (div_lt_one ha0).mpr ha
  have hua0 : 0 < 1 / a := one_div_pos.mpr ha0
  have hvb : 1 / b < 3 / 4 := (div_lt_iff₀ hb0).mpr (by linarith)
  have hvb0 : 0 < 1 / b := one_div_pos.mpr hb0
  have hx0 : 0 < lam a := by unfold lam; linarith
  have hx1 : lam a < 1 := by unfold lam; linarith
  have hy : 1 / 4 < lam b := by unfold lam; linarith
  have hy1 : lam b < 1 := by unfold lam; linarith
  have hψ : psi a b * (1 - lam b) = 1 - lam a := by
    unfold psi lam
    field_simp
    ring
  have hψ3 : 0 < psi a b ^ 3 := pow_pos hψ0 3
  have hden : 0 < 4 * lam a ^ 3 * psi a b ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hx0 3)) (pow_pos hψ0 2)
  obtain ⟨h3l, h3u⟩ := h3
  obtain ⟨h4l, h4u⟩ := h4
  rw [le_div_iff₀ hψ3] at h3l
  rw [div_le_iff₀ hψ3] at h3u
  rw [le_div_iff₀ hden] at h4l
  rw [div_le_iff₀ hden] at h4u
  obtain ⟨P1, P2⟩ := patch2_core hx0 hx1 hy hy1 hψ h3l h3u h4l h4u
  have hab : a * b * ((1 - lam a) * (1 - lam b)) = 1 := by
    unfold lam
    field_simp
    ring
  have hab0 : 0 < a * b := mul_pos ha0 hb0
  have hL : 45 ≤ |a * b| := by
    have := mul_le_mul_of_nonneg_left P2 hab0.le
    rw [hab] at this
    rw [abs_of_pos hab0]
    linarith
  have hU : |a * b| ≤ 500 := by
    have := mul_le_mul_of_nonneg_left P1 hab0.le
    rw [hab] at this
    rw [abs_of_pos hab0]
    linarith
  exact not_C1_of_abs 1 (by norm_num) hL hU (by norm_num) (by norm_num)

/-- **Constraint 2 dropped, unrestricted.** For all real `a`, `b` and all natural `p`, `k`:
constraints 1, 3, 4, 5 force `p = 15`, `k = 29` and the accepted set. No ordering, no sign
condition, no exponent range, and no helium constraint. -/
theorem strong_drop_C2 (a b : ℝ) (p k : ℕ) (h : C1 a b p ∧ C3 a b ∧ C4 a b ∧ C5 a k) :
    p = 15 ∧ k = 29 ∧ A a b := by
  obtain ⟨h1, h3, h4, h5⟩ := h
  obtain ⟨ha1, hb1⟩ := one_lt_of_C3_C4 h3 h4
  rcases le_or_gt b (4 / 3) with hb | hb
  · obtain ⟨hal0, hau0⟩ := a_of_C3_C4_of_le ha1 hb1 hb h3 h4
    have hk : k = 29 := k_of_C5 hal0 hau0 h5
    subst hk
    obtain ⟨hp, hA⟩ := finish hb1 (by linarith) h1 h4 h5
    exact ⟨hp, rfl, hA⟩
  · exact absurd h1 (not_C1_of_C3_C4_big ha1 hb h3 h4)

/-! ### The two four-constraint equivalences, and the ordered constraint-4 companion -/

/-- Constraints 1, 3, 4, 5 hold exactly when `p = 15`, `k = 29` and `(a, b)` is in the accepted
set (so constraint 2 follows from the other four). -/
theorem iff_drop_C2 (a b : ℝ) (p k : ℕ) :
    (C1 a b p ∧ C3 a b ∧ C4 a b ∧ C5 a k) ↔ (p = 15 ∧ k = 29 ∧ A a b) := by
  constructor
  · exact strong_drop_C2 a b p k
  · rintro ⟨hp, hk, hA⟩
    subst hp
    subst hk
    obtain ⟨h1, _, h3, h4, h5⟩ := converse a b hA
    exact ⟨h1, h3, h4, h5⟩

/-- Constraints 1, 2, 4, 5 hold exactly when `p = 15`, `k = 29` and `(a, b)` is in the accepted
set (so constraint 3 follows from the other four). -/
theorem iff_drop_C3 (a b : ℝ) (p k : ℕ) :
    (C1 a b p ∧ C2 a ∧ C4 a b ∧ C5 a k) ↔ (p = 15 ∧ k = 29 ∧ A a b) := by
  constructor
  · exact strong_drop_C3 a b p k
  · rintro ⟨hp, hk, hA⟩
    subst hp
    subst hk
    obtain ⟨h1, h2, _, h4, h5⟩ := converse a b hA
    exact ⟨h1, h2, h4, h5⟩

/-- **Constraint 4 dropped, `1 < b` not assumed.** With `b < a` and constraints 1, 2, 3, 5.
The ordering `b < a` is needed here (`control_i_explicit`). -/
theorem companion_drop_C4_strong (a b : ℝ) (p k : ℕ) (hba : b < a)
    (h1 : C1 a b p) (h2 : C2 a) (h3 : C3 a b) (h5 : C5 a k) :
    p = 15 ∧ k = 29 ∧ A a b :=
  companion_drop_C4 a b p k (b_gt_one_of_C3 (by linarith [(a_of_C2 h2).1]) h3) hba h1 h2 h3 h5

#print axioms not_C1_of_abs
#print axioms quartic_anti
#print axioms patch2_core
#print axioms one_lt_of_C3_C4
#print axioms strong_drop_C3
#print axioms strong_drop_C2
#print axioms iff_drop_C2
#print axioms iff_drop_C3
#print axioms companion_drop_C4_strong

end ExclusionRegion
