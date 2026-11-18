module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets
public import ExclusionRegion.Forward

@[expose] public section

namespace ExclusionRegion

open Real

/-! Target 6, COMPANION: with `1 < b < a`, any one of constraints 2, 3, 4 can be dropped. No
exponent range is assumed in any of the three. -/

/-- Constraints 3 (upper) and 4 (lower) combined: `s · 4(a-1)³a⁴ ≤ t³ b⁷`. -/
theorem comp_upper {a b t s : ℝ} (ha : 1 < a) (hb : 1 < b)
    (h3 : (b - 1) * a ^ 3 ≤ t * b ^ 4) (h4 : s * (4 * (a - 1) ^ 3 * b ^ 5) ≤ (b - 1) ^ 3 * a ^ 5) :
    s * (4 * (a - 1) ^ 3 * a ^ 4) ≤ t ^ 3 * b ^ 7 := by
  have hb0 : 0 < b := by linarith
  have h0 : 0 ≤ (b - 1) * a ^ 3 := mul_nonneg (by linarith) (pow_nonneg (by linarith) 3)
  have c := pow_le_pow_left₀ h0 h3 3
  have key : s * (4 * (a - 1) ^ 3 * a ^ 4) * b ^ 5 ≤ t ^ 3 * b ^ 7 * b ^ 5 := by
    calc s * (4 * (a - 1) ^ 3 * a ^ 4) * b ^ 5 = s * (4 * (a - 1) ^ 3 * b ^ 5) * a ^ 4 := by ring
      _ ≤ (b - 1) ^ 3 * a ^ 5 * a ^ 4 := mul_le_mul_of_nonneg_right h4 (pow_nonneg (by linarith) 4)
      _ = ((b - 1) * a ^ 3) ^ 3 := by ring
      _ ≤ (t * b ^ 4) ^ 3 := c
      _ = t ^ 3 * b ^ 7 * b ^ 5 := by ring
  exact le_of_mul_le_mul_right key (pow_pos hb0 5)

/-- Constraints 3 (lower) and 4 (upper) combined: `t³ b⁷ ≤ s · 4(a-1)³a⁴`. -/
theorem comp_lower {a b t s : ℝ} (ha : 1 < a) (hb : 1 < b) (ht : 0 ≤ t)
    (h3 : t * b ^ 4 ≤ (b - 1) * a ^ 3) (h4 : (b - 1) ^ 3 * a ^ 5 ≤ s * (4 * (a - 1) ^ 3 * b ^ 5)) :
    t ^ 3 * b ^ 7 ≤ s * (4 * (a - 1) ^ 3 * a ^ 4) := by
  have hb0 : 0 < b := by linarith
  have h0 : 0 ≤ t * b ^ 4 := mul_nonneg ht (pow_nonneg hb0.le 4)
  have c := pow_le_pow_left₀ h0 h3 3
  have key : t ^ 3 * b ^ 7 * b ^ 5 ≤ s * (4 * (a - 1) ^ 3 * a ^ 4) * b ^ 5 := by
    calc t ^ 3 * b ^ 7 * b ^ 5 = (t * b ^ 4) ^ 3 := by ring
      _ ≤ ((b - 1) * a ^ 3) ^ 3 := c
      _ = (b - 1) ^ 3 * a ^ 5 * a ^ 4 := by ring
      _ ≤ s * (4 * (a - 1) ^ 3 * b ^ 5) * a ^ 4 :=
          mul_le_mul_of_nonneg_right h4 (pow_nonneg (by linarith) 4)
      _ = s * (4 * (a - 1) ^ 3 * a ^ 4) * b ^ 5 := by ring
  exact le_of_mul_le_mul_right key (pow_pos hb0 5)

/-- With `1 < a` and `1 < b ≤ 4/3`, constraints 3 and 4 alone put `a` in `[1.315, 1.335]`. No
ordering of `a` and `b` is assumed. -/
theorem a_of_C3_C4_of_le {a b : ℝ} (ha1 : 1 < a) (hb : 1 < b) (hb43 : b ≤ 4 / 3)
    (h3 : C3 a b) (h4 : C4 a b) : 1.315 ≤ a ∧ a ≤ 1.335 := by
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨p3l, p3u⟩ := C3_poly ha0 hb0 h3
  obtain ⟨p4l, p4u⟩ := C4_poly ha1 hb0 h4
  have hbm : 0 < b - 1 := by linarith
  constructor
  · by_contra hc
    have hc := not_le.mp hc
    -- `b ≥ 1.22`
    have hb22 : 1.22 ≤ b := by
      by_contra hb'
      have hb' := not_le.mp hb'
      have g0 := g3_cross hb.le hb'.le (by norm_num)
      have g1 : (b - 1) * 2.2153 ≤ 0.22 * b ^ 4 := by
        calc (b - 1) * 2.2153 ≤ (b - 1) * 1.22 ^ 4 :=
              mul_le_mul_of_nonneg_left (by norm_num) hbm.le
          _ ≤ (1.22 - 1) * b ^ 4 := g0
          _ = 0.22 * b ^ 4 := by norm_num
      have a3 : a ^ 3 ≤ 2.274 := (pow_le_pow_left₀ ha0.le hc.le 3).trans (by norm_num)
      have m : (b - 1) * a ^ 3 ≤ (b - 1) * 2.274 := mul_le_mul_of_nonneg_left a3 hbm.le
      linarith
    have id := comp_lower (t := 0.2265858) (s := 0.12036) ha1 hb (by norm_num) p3l p4u
    have b7 : (4.0227 : ℝ) ≤ b ^ 7 :=
      (by norm_num : (4.0227 : ℝ) ≤ 1.22 ^ 7).trans (pow_le_pow_left₀ (by norm_num) hb22 7)
    have l1 : (0.04678 : ℝ) ≤ (0.2265858 : ℝ) ^ 3 * b ^ 7 :=
      (by norm_num : (0.04678 : ℝ) ≤ (0.2265858 : ℝ) ^ 3 * 4.0227).trans
        (mul_le_mul_of_nonneg_left b7 (by norm_num))
    have a4 : a ^ 4 ≤ (1.315 : ℝ) ^ 4 := pow_le_pow_left₀ ha0.le hc.le 4
    have a13 : (a - 1) ^ 3 ≤ (0.315 : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have prod : (a - 1) ^ 3 * a ^ 4 ≤ 0.0935 :=
      (mul_le_mul a13 a4 (pow_nonneg ha0.le 4) (by norm_num)).trans (by norm_num)
    have y : (0.04678 : ℝ) ≤ 0.12036 * (4 * (a - 1) ^ 3 * a ^ 4) := l1.trans id
    linarith
  · by_contra hc
    have hc := not_le.mp hc
    -- `b ≤ 1.22`
    have hb22 : b ≤ 1.22 := by
      by_contra hb'
      have hb' := not_le.mp hb'
      have g0 := g3_cross (by norm_num : (1 : ℝ) ≤ 1.22) hb'.le hb43
      have g1 : 0.22 * b ^ 4 ≤ (b - 1) * 2.2154 := by
        calc 0.22 * b ^ 4 = (1.22 - 1) * b ^ 4 := by norm_num
          _ ≤ (b - 1) * 1.22 ^ 4 := g0
          _ ≤ (b - 1) * 2.2154 := mul_le_mul_of_nonneg_left (by norm_num) hbm.le
      have a3 : (2.3792 : ℝ) ≤ a ^ 3 :=
        (by norm_num : (2.3792 : ℝ) ≤ 1.335 ^ 3).trans (pow_le_pow_left₀ (by norm_num) hc.le 3)
      have m : (b - 1) * 2.3792 ≤ (b - 1) * a ^ 3 := mul_le_mul_of_nonneg_left a3 hbm.le
      linarith
    have id := comp_upper (t := 0.2358342) (s := 0.11564) ha1 hb p3u p4l
    have b7 : b ^ 7 ≤ 4.0228 := (pow_le_pow_left₀ hb0.le hb22 7).trans (by norm_num)
    have u1 : (0.2358342 : ℝ) ^ 3 * b ^ 7 ≤ 0.05277 :=
      (mul_le_mul_of_nonneg_left b7 (by norm_num)).trans (by norm_num)
    have a4 : (1.335 : ℝ) ^ 4 ≤ a ^ 4 := pow_le_pow_left₀ (by norm_num) hc.le 4
    have a13 : (0.335 : ℝ) ^ 3 ≤ (a - 1) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    have prod : (0.1194 : ℝ) ≤ (a - 1) ^ 3 * a ^ 4 :=
      (by norm_num : (0.1194 : ℝ) ≤ 0.335 ^ 3 * 1.335 ^ 4).trans
        (mul_le_mul a13 a4 (by norm_num) (pow_nonneg (by linarith) 3))
    have y : 0.11564 * (4 * (a - 1) ^ 3 * a ^ 4) ≤ (0.05277 : ℝ) := id.trans u1
    linarith

/-- With `1 < b < a`, constraints 3 and 4 alone put `a` in `[1.315, 1.335]`: the ordering gives
`b ≤ 1.31 ≤ 4/3`, and `a_of_C3_C4_of_le` applies. -/
theorem a_of_C3_C4 {a b : ℝ} (hb : 1 < b) (hba : b < a) (h3 : C3 a b) (h4 : C4 a b) :
    1.315 ≤ a ∧ a ≤ 1.335 := by
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨_, p3u⟩ := C3_poly ha0 hb0 h3
  have hbm : 0 < b - 1 := by linarith
  -- `b ≤ 1.31 ≤ 4/3`, from constraint 3 and `b < a`
  have hb131 : b ≤ 1.31 := by
    have e1 : b ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hb0.le hba.le 3
    have e2 : (b - 1) * b ^ 3 ≤ (b - 1) * a ^ 3 := mul_le_mul_of_nonneg_left e1 hbm.le
    have e3 : (b - 1) * b ^ 3 ≤ 0.2358342 * b * b ^ 3 := by
      calc (b - 1) * b ^ 3 ≤ (b - 1) * a ^ 3 := e2
        _ ≤ 0.2358342 * b ^ 4 := p3u
        _ = 0.2358342 * b * b ^ 3 := by ring
    have e4 : b - 1 ≤ 0.2358342 * b := le_of_mul_le_mul_right e3 (pow_pos hb0 3)
    linarith
  exact a_of_C3_C4_of_le (by linarith) hb (by linarith) h3 h4

/-- With `a` pinned and `1 < b ≤ 4/3`, constraint 3 confines `b` to `[1.19, 1.26]`. -/
theorem b_of_C3 {a b : ℝ} (hal : 1.3237 ≤ a) (hau : a ≤ 1.3256) (hb : 1 < b) (hb43 : b ≤ 4 / 3)
    (h : C3 a b) : 1.19 ≤ b ∧ b ≤ 1.26 := by
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  obtain ⟨p3l, p3u⟩ := C3_poly ha0 hb0 h
  have hb4 : 0 < b ^ 4 := pow_pos hb0 4
  have hbm : 0 < b - 1 := by linarith
  constructor
  · by_contra hc
    have hc := not_le.mp hc
    have g0 := g3_cross hb.le hc.le (by norm_num)
    have g1 : (b - 1) * 2.005 ≤ 0.19 * b ^ 4 := by
      calc (b - 1) * 2.005 ≤ (b - 1) * 1.19 ^ 4 :=
            mul_le_mul_of_nonneg_left (by norm_num) hbm.le
        _ ≤ (1.19 - 1) * b ^ 4 := g0
        _ = 0.19 * b ^ 4 := by norm_num
    have a3 : a ^ 3 ≤ 2.33 := (pow_le_pow_left₀ ha0.le hau 3).trans (by norm_num)
    have m : (b - 1) * a ^ 3 ≤ (b - 1) * 2.33 := mul_le_mul_of_nonneg_left a3 hbm.le
    linarith
  · by_contra hc
    have hc := not_le.mp hc
    have g0 := g3_cross (by norm_num : (1 : ℝ) ≤ 1.26) hc.le hb43
    have g1 : 0.26 * b ^ 4 ≤ (b - 1) * 2.5205 := by
      calc 0.26 * b ^ 4 = (1.26 - 1) * b ^ 4 := by norm_num
        _ ≤ (b - 1) * 1.26 ^ 4 := g0
        _ ≤ (b - 1) * 2.5205 := mul_le_mul_of_nonneg_left (by norm_num) hbm.le
    have a3 : (2.3193 : ℝ) ≤ a ^ 3 :=
      (by norm_num : (2.3193 : ℝ) ≤ 1.3237 ^ 3).trans (pow_le_pow_left₀ (by norm_num) hal 3)
    have m : (b - 1) * 2.3193 ≤ (b - 1) * a ^ 3 := mul_le_mul_of_nonneg_left a3 hbm.le
    linarith

/-- **Target 6, constraint 2 dropped.** `1 < b < a` with constraints 1, 3, 4, 5. -/
theorem companion_drop_C2 (a b : ℝ) (p k : ℕ) (hb : 1 < b) (hba : b < a)
    (h1 : C1 a b p) (h3 : C3 a b) (h4 : C4 a b) (h5 : C5 a k) :
    p = 15 ∧ k = 29 ∧ A a b := by
  obtain ⟨hal0, hau0⟩ := a_of_C3_C4 hb hba h3 h4
  have hk : k = 29 := k_of_C5 hal0 hau0 h5
  subst hk
  obtain ⟨hp, hA⟩ := finish hb (by linarith) h1 h4 h5
  exact ⟨hp, rfl, hA⟩

/-- **Target 6, constraint 3 dropped.** `1 < b < a` with constraints 1, 2, 4, 5. -/
theorem companion_drop_C3 (a b : ℝ) (p k : ℕ) (hb : 1 < b) (hba : b < a)
    (h1 : C1 a b p) (h2 : C2 a) (h4 : C4 a b) (h5 : C5 a k) :
    p = 15 ∧ k = 29 ∧ A a b := by
  have hau0 := (a_of_C2 h2).2
  exact forward_core hb (by linarith) h1 h2 h4 h5

/-- **Target 6, constraint 4 dropped.** `1 < b < a` with constraints 1, 2, 3, 5. -/
theorem companion_drop_C4 (a b : ℝ) (p k : ℕ) (hb : 1 < b) (hba : b < a)
    (h1 : C1 a b p) (h2 : C2 a) (h3 : C3 a b) (h5 : C5 a k) :
    p = 15 ∧ k = 29 ∧ A a b := by
  obtain ⟨hal0, hau0⟩ := a_of_C2 h2
  have hk : k = 29 := k_of_C5 (by linarith) (by linarith) h5
  subst hk
  have h5' := C5_iff.mp h5
  obtain ⟨hal, hau⟩ := a_of_pow29 h5'.1 h5'.2
  obtain ⟨hbl, hbu⟩ := b_of_C3 hal hau hb (by linarith) h3
  have hp : p = 15 := p_of_C1 hal hau hbl hbu h1
  subst hp
  exact ⟨rfl, rfl, A_of_C1_C5 h1 h5⟩

#print axioms a_of_C3_C4_of_le
#print axioms a_of_C3_C4
#print axioms companion_drop_C2
#print axioms companion_drop_C3
#print axioms companion_drop_C4

end ExclusionRegion
