module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets

@[expose] public section

namespace ExclusionRegion

open Real

/-! FORWARD: the steps every forward statement is built from, and `forward_core`. The statement
in the public test's shape (target 1a) is `test_shaped` in Strong.lean: one statement, one name. -/

/-- Constraint 2 puts `a` in the helium interval. -/
theorem a_of_C2 {a : ℝ} (h : C2 a) : 1.3157 ≤ a ∧ a ≤ 1.333 := by
  rw [C2_iff] at h
  obtain ⟨h1, h2⟩ := h
  unfold lam at h1 h2
  have hinv : 0 < 1 / a := by linarith
  have ha : 0 < a := one_div_pos.mp hinv
  have e : 1 / a * a = 1 := by field_simp
  have p1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 0.759998 - 1 / a) ha.le
  have p2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / a - 0.750202) ha.le
  constructor <;> nlinarith

/-- With `a` near the helium interval, constraint 5 forces `k = 29`, for every natural `k`. -/
theorem k_of_C5 {a : ℝ} {k : ℕ} (hl : 1.315 ≤ a) (hu : a ≤ 1.335) (h : C5 a k) : k = 29 := by
  rw [C5_iff] at h
  obtain ⟨h1, h2⟩ := h
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 ≤ a := by linarith
  by_contra hk
  rcases Nat.lt_or_ge k 29 with hlt | hge
  · have e1 : a ^ k ≤ a ^ 28 := pow_le_pow_right₀ ha1 (by omega)
    have e2 : a ^ 28 ≤ (1.335 : ℝ) ^ 28 := pow_le_pow_left₀ ha0 hu 28
    have e3 : (1.335 : ℝ) ^ 28 < 3407.656 := by norm_num
    exact lt_irrefl _ (lt_of_le_of_lt (h1.trans (e1.trans e2)) e3)
  · have hk30 : 30 ≤ k := by omega
    have e1 : a ^ 30 ≤ a ^ k := pow_le_pow_right₀ ha1 hk30
    have e2 : (1.315 : ℝ) ^ 30 ≤ a ^ 30 := pow_le_pow_left₀ (by norm_num) hl 30
    have e3 : (3546.744 : ℝ) < 1.315 ^ 30 := by norm_num
    exact lt_irrefl _ (lt_of_lt_of_le e3 ((e2.trans e1).trans h2))

/-- The window on `a^29` pins `a` to four digits (enough for the exponent step). -/
theorem a_of_pow29 {a : ℝ} (h1 : 3407.656 ≤ a ^ 29) (h2 : a ^ 29 ≤ 3546.744) :
    1.3237 ≤ a ∧ a ≤ 1.3256 :=
  pow29_bracket (by norm_num) (by norm_num) (by norm_num) h1 h2

/-- With `a` pinned and `1 < b ≤ 2`, constraint 4 confines `b` to `[1.19, 1.26]`. -/
theorem b_of_C4 {a b : ℝ} (hal : 1.3237 ≤ a) (hau : a ≤ 1.3256) (hb : 1 < b) (hb2 : b ≤ 2)
    (h : C4 a b) : 1.19 ≤ b ∧ b ≤ 1.26 := by
  rw [C4_iff] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · by_contra hc
    have hc := not_le.mp hc
    have hle := C4val_le (aL := 1.3237) (β := 1.19) (by norm_num) hal (by linarith) hb hc.le
      (by norm_num)
    have hnum : ((1.19 : ℝ) - 1) ^ 3 * 1.3237 ^ 5 / (4 * (1.3237 - 1) ^ 3 * 1.19 ^ 5) < 0.11564 := by
      norm_num
    exact lt_irrefl _ (lt_of_le_of_lt (h1.trans hle) hnum)
  · by_contra hc
    have hc := not_le.mp hc
    have hge := C4val_ge (aU := 1.3256) (β := 1.26) (by norm_num) hc.le hb2 (by linarith) hau
      (by norm_num)
    have hnum : (0.12036 : ℝ) < ((1.26 : ℝ) - 1) ^ 3 * 1.3256 ^ 5 / (4 * (1.3256 - 1) ^ 3 * 1.26 ^ 5) := by
      norm_num
    exact lt_irrefl _ (lt_of_lt_of_le hnum (hge.trans h2))

/-- With `a` pinned and `b ∈ [1.19, 1.26]`, constraint 1 forces `p = 15`, for every natural `p`. -/
theorem p_of_C1 {a b : ℝ} {p : ℕ} (hal : 1.3237 ≤ a) (hau : a ≤ 1.3256) (hbl : 1.19 ≤ b)
    (hbu : b ≤ 1.26) (h : C1 a b p) : p = 15 := by
  rw [C1_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hpi : 0 < π ^ 2 := by positivity
  rw [le_div_iff₀ hpi] at h1
  rw [div_le_iff₀ hpi] at h2
  have hpl : (3.14 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d2.le 2
  have hpu : π ^ 2 ≤ (3.15 : ℝ) ^ 2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
  have hab_l : (1.3237 : ℝ) * 1.19 ≤ a * b := mul_le_mul hal hbl (by norm_num) (by linarith)
  have hab_u : a * b ≤ 1.3256 * 1.26 := mul_le_mul hau hbu (by linarith) (by norm_num)
  have hc1 : (1 : ℝ) ≤ 1.3237 * 1.19 := by norm_num
  have hab1 : 1 ≤ a * b := hc1.trans hab_l
  have hab0 : 0 ≤ a * b := by linarith
  by_contra hp
  rcases Nat.lt_or_ge p 15 with hlt | hge
  · have e1 : (a * b) ^ p ≤ (a * b) ^ 14 := pow_le_pow_right₀ hab1 (by omega)
    have e2 : (a * b) ^ 14 ≤ ((1.3256 : ℝ) * 1.26) ^ 14 := pow_le_pow_left₀ hab0 hab_u 14
    have e3 : ((1.3256 : ℝ) * 1.26) ^ 14 < 136.35082 * 3.14 ^ 2 := by norm_num
    have e4 : (136.35082 : ℝ) * 3.14 ^ 2 ≤ 136.35082 * π ^ 2 :=
      mul_le_mul_of_nonneg_left hpl (by norm_num)
    exact lt_irrefl _ (lt_of_le_of_lt (e1.trans e2) (lt_of_lt_of_le e3 (e4.trans h1)))
  · have hp16 : 16 ≤ p := by omega
    have e1 : (a * b) ^ 16 ≤ (a * b) ^ p := pow_le_pow_right₀ hab1 hp16
    have e2 : ((1.3237 : ℝ) * 1.19) ^ 16 ≤ (a * b) ^ 16 := pow_le_pow_left₀ (by norm_num) hab_l 16
    have e3 : (137.72118 : ℝ) * 3.15 ^ 2 < ((1.3237 : ℝ) * 1.19) ^ 16 := by norm_num
    have e4 : (137.72118 : ℝ) * π ^ 2 ≤ 137.72118 * 3.15 ^ 2 :=
      mul_le_mul_of_nonneg_left hpu (by norm_num)
    exact lt_irrefl _ (lt_of_le_of_lt (h2.trans e4) (lt_of_lt_of_le e3 (e2.trans e1)))

/-- Constraints 1 and 5 at the exponents 15 and 29 are the accepted set. -/
theorem A_of_C1_C5 {a b : ℝ} (h1 : C1 a b 15) (h5 : C5 a 29) : A a b := by
  rw [C1_iff] at h1
  rw [C5_iff] at h5
  have hpi : 0 < π ^ 2 := by positivity
  obtain ⟨h1a, h1b⟩ := h1
  rw [le_div_iff₀ hpi] at h1a
  rw [div_le_iff₀ hpi] at h1b
  rw [A_iff]
  exact ⟨h5.1, h5.2, h1a, h1b⟩

/-- The last two steps, shared by every forward statement: with `a` pinned by `a^29` and
`1 < b ≤ 2`, constraints 4 and 1 give `p = 15` and the accepted set. -/
theorem finish {a b : ℝ} {p : ℕ} (hb : 1 < b) (hb2 : b ≤ 2)
    (h1 : C1 a b p) (h4 : C4 a b) (h5 : C5 a 29) : p = 15 ∧ A a b := by
  have h5' := C5_iff.mp h5
  obtain ⟨hal, hau⟩ := a_of_pow29 h5'.1 h5'.2
  obtain ⟨hbl, hbu⟩ := b_of_C4 hal hau hb hb2 h4
  have hp : p = 15 := p_of_C1 hal hau hbl hbu h1
  subst hp
  exact ⟨rfl, A_of_C1_C5 h1 h5⟩

/-- Constraints 1, 2, 4, 5 with `1 < b ≤ 2` (constraint 3 not used). -/
theorem forward_core {a b : ℝ} {p k : ℕ} (hb : 1 < b) (hb2 : b ≤ 2)
    (h1 : C1 a b p) (h2 : C2 a) (h4 : C4 a b) (h5 : C5 a k) :
    p = 15 ∧ k = 29 ∧ A a b := by
  obtain ⟨hal0, hau0⟩ := a_of_C2 h2
  have hk : k = 29 := k_of_C5 (by linarith) (by linarith) h5
  subst hk
  obtain ⟨hp, hA⟩ := finish hb hb2 h1 h4 h5
  exact ⟨hp, rfl, hA⟩

#print axioms forward_core

end ExclusionRegion
