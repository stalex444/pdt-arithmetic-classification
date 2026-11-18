module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Brackets
public import ExclusionRegion.Forward
public import ExclusionRegion.Companion
public import ExclusionRegion.Unrestricted

@[expose] public section

namespace ExclusionRegion

open Real

/-! STAGE 2, THE THREE GAUGE-COUPLING WINDOWS without helium or τ/e (F:518: the first, third and
fourth rows of the deposit's Table 2; targets and windows as the test's constants). For all real
`a`, `b` and every natural `p`, constraints 1, 3, 4 force `p = 15` and put `(a, b)` in an
outward-rounded rational box; helium (constraint 2) follows; and on `1 < a`, `1 < b` the three
constraints are exactly constraint 1 at `p = 15` with constraint 4 (constraint 3 selects the branch).
π enters through constraint 1.

Route: `one_lt_of_C3_C4` and `not_C1_of_C3_C4_big` put `(a, b)` on the near patch; there
`a_of_C3_C4_of_le` gives `a ∈ [1.315, 1.335]`, constraint 4 gives `b ∈ [1.21, 1.23]`, so
`ab ∈ [1.591, 1.643]` and constraint 1 admits only `p = 15`. The box comes from constraints 1
(at 15) and 4 alone: its extremes lie on their boundary curves, and each side is a cross of the
monotone quantities `(x-1)³/x⁵` (`C4val_le`, `C4val_ge`) against `ab ∈ [L, U]`. -/

/-- Constraints 3 and 4, with constraint 1 at some exponent, put `(a, b)` on the near patch. -/
theorem near_of_C1_C3_C4 {a b : ℝ} {p : ℕ} (h1 : C1 a b p) (h3 : C3 a b) (h4 : C4 a b) :
    1 < a ∧ 1 < b ∧ b ≤ 4 / 3 := by
  obtain ⟨ha, hb⟩ := one_lt_of_C3_C4 h3 h4
  refine ⟨ha, hb, ?_⟩
  by_contra hc
  exact not_C1_of_C3_C4_big ha (not_le.mp hc) h3 h4 h1

/-- With `a ∈ [1.315, 1.335]` and `1 < b ≤ 2`, constraint 4 confines `b` to `[1.21, 1.23]`. -/
theorem b_of_C4_wide {a b : ℝ} (hal : 1.315 ≤ a) (hau : a ≤ 1.335) (hb : 1 < b) (hb2 : b ≤ 2)
    (h : C4 a b) : 1.21 ≤ b ∧ b ≤ 1.23 := by
  rw [C4_iff] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · by_contra hc
    have hc := not_le.mp hc
    have hle := C4val_le (aL := 1.315) (β := 1.21) (by norm_num) hal (by linarith) hb hc.le
      (by norm_num)
    have hnum : ((1.21 : ℝ) - 1) ^ 3 * 1.315 ^ 5 / (4 * (1.315 - 1) ^ 3 * 1.21 ^ 5) < 0.11564 := by
      norm_num
    exact lt_irrefl _ (lt_of_le_of_lt (h1.trans hle) hnum)
  · by_contra hc
    have hc := not_le.mp hc
    have hge := C4val_ge (aU := 1.335) (β := 1.23) (by norm_num) hc.le hb2 (by linarith) hau
      (by norm_num)
    have hnum : (0.12036 : ℝ) < ((1.23 : ℝ) - 1) ^ 3 * 1.335 ^ 5 / (4 * (1.335 - 1) ^ 3 * 1.23 ^ 5) := by
      norm_num
    exact lt_irrefl _ (lt_of_lt_of_le hnum (hge.trans h2))

/-- With `a ∈ [1.315, 1.335]` and `b ∈ [1.21, 1.23]`, constraint 1 forces `p = 15`. -/
theorem p_of_C1_wide {a b : ℝ} {p : ℕ} (hal : 1.315 ≤ a) (hau : a ≤ 1.335) (hbl : 1.21 ≤ b)
    (hbu : b ≤ 1.23) (h : C1 a b p) : p = 15 := by
  rw [C1_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hpi : 0 < π ^ 2 := by positivity
  rw [le_div_iff₀ hpi] at h1
  rw [div_le_iff₀ hpi] at h2
  have hpl : (3.14 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d2.le 2
  have hpu : π ^ 2 ≤ (3.15 : ℝ) ^ 2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
  have hab_l : (1.315 : ℝ) * 1.21 ≤ a * b := mul_le_mul hal hbl (by norm_num) (by linarith)
  have hab_u : a * b ≤ 1.335 * 1.23 := mul_le_mul hau hbu (by linarith) (by norm_num)
  have hab1 : 1 ≤ a * b := le_trans (by norm_num) hab_l
  have hab0 : 0 ≤ a * b := by linarith
  by_contra hp
  rcases Nat.lt_or_ge p 15 with hlt | hge
  · have e1 : (a * b) ^ p ≤ (a * b) ^ 14 := pow_le_pow_right₀ hab1 (by omega)
    have e2 : (a * b) ^ 14 ≤ ((1.335 : ℝ) * 1.23) ^ 14 := pow_le_pow_left₀ hab0 hab_u 14
    have e3 : ((1.335 : ℝ) * 1.23) ^ 14 < 136.35082 * 3.14 ^ 2 := by norm_num
    have e4 : (136.35082 : ℝ) * 3.14 ^ 2 ≤ 136.35082 * π ^ 2 :=
      mul_le_mul_of_nonneg_left hpl (by norm_num)
    exact lt_irrefl _ (lt_of_le_of_lt (e1.trans e2) (lt_of_lt_of_le e3 (e4.trans h1)))
  · have hp16 : 16 ≤ p := by omega
    have e1 : (a * b) ^ 16 ≤ (a * b) ^ p := pow_le_pow_right₀ hab1 hp16
    have e2 : ((1.315 : ℝ) * 1.21) ^ 16 ≤ (a * b) ^ 16 := pow_le_pow_left₀ (by norm_num) hab_l 16
    have e3 : (137.72118 : ℝ) * 3.15 ^ 2 < ((1.315 : ℝ) * 1.21) ^ 16 := by norm_num
    have e4 : (137.72118 : ℝ) * π ^ 2 ≤ 137.72118 * 3.15 ^ 2 :=
      mul_le_mul_of_nonneg_left hpu (by norm_num)
    exact lt_irrefl _ (lt_of_le_of_lt (h2.trans e4) (lt_of_lt_of_le e3 (e2.trans e1)))

/-- `π²` between the squares of Mathlib's 20-decimal bounds. -/
theorem pi_sq_d20 :
    (3.14159265358979323846 : ℝ) ^ 2 ≤ π ^ 2 ∧ π ^ 2 ≤ (3.14159265358979323847 : ℝ) ^ 2 :=
  ⟨pow_le_pow_left₀ (by norm_num) Real.pi_gt_d20.le 2,
   pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d20.le 2⟩

/-- Constraint 1 at `p = 15`, for positive `a`, `b`, pins `ab` to `[1.616579870237, 1.617657958458]`. -/
theorem ab_of_C1_15 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : C1 a b 15) :
    1.616579870237 ≤ a * b ∧ a * b ≤ 1.617657958458 := by
  rw [C1_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hpi : 0 < π ^ 2 := by positivity
  rw [le_div_iff₀ hpi] at h1
  rw [div_le_iff₀ hpi] at h2
  obtain ⟨hpl, hpu⟩ := pi_sq_d20
  have hab0 : 0 ≤ a * b := (mul_pos ha hb).le
  constructor
  · refine le_base_of_pow_le (n := 15) (by norm_num) hab0 ?_
    calc (1.616579870237 : ℝ) ^ 15 ≤ 136.35082 * 3.14159265358979323846 ^ 2 := by norm_num
      _ ≤ 136.35082 * π ^ 2 := mul_le_mul_of_nonneg_left hpl (by norm_num)
      _ ≤ (a * b) ^ 15 := h1
  · refine base_le_of_pow_le (n := 15) (by norm_num) (by norm_num) ?_
    calc (a * b) ^ 15 ≤ 137.72118 * π ^ 2 := h2
      _ ≤ 137.72118 * 3.14159265358979323847 ^ 2 := mul_le_mul_of_nonneg_left hpu (by norm_num)
      _ ≤ (1.617657958458 : ℝ) ^ 15 := by norm_num

/-- **The box from constraints 1 (at 15) and 4.** For `1 < a`, `1 < b`. -/
theorem box_of_C1_C4 {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (h1 : C1 a b 15) (h4 : C4 a b) :
    1.3231557 ≤ a ∧ a ≤ 1.3265140 ∧ 1.2191706 ≤ b ∧ b ≤ 1.2220763 := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨hL, hU⟩ := ab_of_C1_15 ha0 hb0 h1
  have ha2 : a ≤ 2 := by
    have := lt_mul_of_one_lt_right ha0 hb
    linarith
  have hb2 : b ≤ 2 := by
    have := lt_mul_of_one_lt_left hb0 ha
    linarith
  rw [C4_iff] at h4
  obtain ⟨h4l, h4u⟩ := h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `a ≥ 1.3231557`: on the C4-upper / C1-lower vertex
    by_contra hc
    have hc := not_le.mp hc
    have hbβ : 1.221760878358 ≤ b := by
      refine le_of_mul_le_mul_left ?_ (by norm_num : (0 : ℝ) < 1.3231557)
      calc (1.3231557 : ℝ) * 1.221760878358 ≤ 1.616579870237 := by norm_num
        _ ≤ a * b := hL
        _ ≤ 1.3231557 * b := mul_le_mul_of_nonneg_right hc.le hb0.le
    have hge := C4val_ge (aU := 1.3231557) (β := 1.221760878358) (by norm_num) hbβ hb2 ha
      hc.le (by norm_num)
    have hnum : (0.12036 : ℝ) <
        ((1.221760878358 : ℝ) - 1) ^ 3 * 1.3231557 ^ 5 /
          (4 * (1.3231557 - 1) ^ 3 * 1.221760878358 ^ 5) := by norm_num
    exact lt_irrefl _ (lt_of_lt_of_le hnum (hge.trans h4u))
  · -- `a ≤ 1.3265140`: on the C4-lower / C1-upper vertex
    by_contra hc
    have hc := not_le.mp hc
    have hbβ : b ≤ 1.219480501871 := by
      refine le_of_mul_le_mul_left ?_ (by norm_num : (0 : ℝ) < 1.3265140)
      calc (1.3265140 : ℝ) * b ≤ a * b := mul_le_mul_of_nonneg_right hc.le hb0.le
        _ ≤ 1.617657958458 := hU
        _ ≤ 1.3265140 * 1.219480501871 := by norm_num
    have hle := C4val_le (aL := 1.3265140) (β := 1.219480501871) (by norm_num) hc.le ha2 hb
      hbβ (by norm_num)
    have hnum : ((1.219480501871 : ℝ) - 1) ^ 3 * 1.3265140 ^ 5 /
        (4 * (1.3265140 - 1) ^ 3 * 1.219480501871 ^ 5) < 0.11564 := by norm_num
    exact lt_irrefl _ (lt_of_le_of_lt (h4l.trans hle) hnum)
  · -- `b ≥ 1.2191706`: on the C4-lower / C1-lower vertex
    by_contra hc
    have hc := not_le.mp hc
    have haα : 1.325966907532 ≤ a := by
      refine le_of_mul_le_mul_right ?_ (by norm_num : (0 : ℝ) < 1.2191706)
      calc (1.325966907532 : ℝ) * 1.2191706 ≤ 1.616579870237 := by norm_num
        _ ≤ a * b := hL
        _ ≤ a * 1.2191706 := mul_le_mul_of_nonneg_left hc.le ha0.le
    have hle := C4val_le (aL := 1.325966907532) (β := 1.2191706) (by norm_num) haα ha2 hb
      hc.le (by norm_num)
    have hnum : ((1.2191706 : ℝ) - 1) ^ 3 * 1.325966907532 ^ 5 /
        (4 * (1.325966907532 - 1) ^ 3 * 1.2191706 ^ 5) < 0.11564 := by norm_num
    exact lt_irrefl _ (lt_of_le_of_lt (h4l.trans hle) hnum)
  · -- `b ≤ 1.2220763`: on the C4-upper / C1-upper vertex
    by_contra hc
    have hc := not_le.mp hc
    have haα : a ≤ 1.323696366961 := by
      refine le_of_mul_le_mul_right ?_ (by norm_num : (0 : ℝ) < 1.2220763)
      calc a * 1.2220763 ≤ a * b := mul_le_mul_of_nonneg_left hc.le ha0.le
        _ ≤ 1.617657958458 := hU
        _ ≤ 1.323696366961 * 1.2220763 := by norm_num
    have hge := C4val_ge (aU := 1.323696366961) (β := 1.2220763) (by norm_num) hc.le hb2 ha
      haα (by norm_num)
    have hnum : (0.12036 : ℝ) <
        ((1.2220763 : ℝ) - 1) ^ 3 * 1.323696366961 ^ 5 /
          (4 * (1.323696366961 - 1) ^ 3 * 1.2220763 ^ 5) := by norm_num
    exact lt_irrefl _ (lt_of_lt_of_le hnum (hge.trans h4u))

/-- On the box, constraint 3 holds: `(b-1)a³/b⁴` is increasing in `a` and in `b` (`b ≤ 4/3`). -/
theorem C3_of_box {a b : ℝ} (hal : 1.3231557 ≤ a) (hau : a ≤ 1.3265140) (hbl : 1.2191706 ≤ b)
    (hbu : b ≤ 1.2220763) : C3 a b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hb4 : 0 < b ^ 4 := pow_pos hb0 4
  have hbm : 0 ≤ b - 1 := by linarith
  rw [C3_iff, C3val_eq ha0 hb0, le_div_iff₀ hb4, div_le_iff₀ hb4]
  have a3l : (1.3231557 : ℝ) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by norm_num) hal 3
  have a3u : a ^ 3 ≤ (1.3265140 : ℝ) ^ 3 := pow_le_pow_left₀ ha0.le hau 3
  -- `(1.2191706 - 1) b⁴ ≤ (b - 1) 1.2191706⁴` and `(b - 1) 1.2220763⁴ ≤ (1.2220763 - 1) b⁴`
  have gl := g3_cross (by norm_num) hbl (by linarith)
  have gu := g3_cross (by linarith) hbu (by norm_num)
  constructor
  · -- `0.2265858 b⁴ ≤ (b-1) a³`
    have k : (0.2265858 : ℝ) * 1.2191706 ^ 4 ≤ (1.2191706 - 1) * 1.3231557 ^ 3 := by norm_num
    have m1 : (b - 1) * 1.3231557 ^ 3 ≤ (b - 1) * a ^ 3 := mul_le_mul_of_nonneg_left a3l hbm
    refine le_of_mul_le_mul_right ?_ (by norm_num : (0 : ℝ) < 1.2191706 ^ 4)
    calc 0.2265858 * b ^ 4 * 1.2191706 ^ 4 = (0.2265858 * 1.2191706 ^ 4) * b ^ 4 := by ring
      _ ≤ ((1.2191706 - 1) * 1.3231557 ^ 3) * b ^ 4 := mul_le_mul_of_nonneg_right k hb4.le
      _ = 1.3231557 ^ 3 * ((1.2191706 - 1) * b ^ 4) := by ring
      _ ≤ 1.3231557 ^ 3 * ((b - 1) * 1.2191706 ^ 4) :=
          mul_le_mul_of_nonneg_left gl (by norm_num)
      _ = (b - 1) * 1.3231557 ^ 3 * 1.2191706 ^ 4 := by ring
      _ ≤ (b - 1) * a ^ 3 * 1.2191706 ^ 4 := mul_le_mul_of_nonneg_right m1 (by norm_num)
  · -- `(b-1) a³ ≤ 0.2358342 b⁴`
    have k : (1.2220763 - 1) * (1.3265140 : ℝ) ^ 3 ≤ 0.2358342 * 1.2220763 ^ 4 := by norm_num
    have m1 : (b - 1) * a ^ 3 ≤ (b - 1) * 1.3265140 ^ 3 := mul_le_mul_of_nonneg_left a3u hbm
    refine le_of_mul_le_mul_right ?_ (by norm_num : (0 : ℝ) < 1.2220763 ^ 4)
    calc (b - 1) * a ^ 3 * 1.2220763 ^ 4 ≤ (b - 1) * 1.3265140 ^ 3 * 1.2220763 ^ 4 :=
          mul_le_mul_of_nonneg_right m1 (by norm_num)
      _ = 1.3265140 ^ 3 * ((b - 1) * 1.2220763 ^ 4) := by ring
      _ ≤ 1.3265140 ^ 3 * ((1.2220763 - 1) * b ^ 4) :=
          mul_le_mul_of_nonneg_left gu (by norm_num)
      _ = ((1.2220763 - 1) * 1.3265140 ^ 3) * b ^ 4 := by ring
      _ ≤ (0.2358342 * 1.2220763 ^ 4) * b ^ 4 := mul_le_mul_of_nonneg_right k hb4.le
      _ = 0.2358342 * b ^ 4 * 1.2220763 ^ 4 := by ring

/-- On the box's `a`-interval, constraint 2 (helium) holds. -/
theorem C2_of_box {a : ℝ} (hal : 1.3231557 ≤ a) (hau : a ≤ 1.3265140) : C2 a := by
  rw [C2_iff]
  unfold lam
  have h1 : 1 / a ≤ 1 / 1.3231557 := one_div_le_one_div_of_le (by norm_num) hal
  have h2 : 1 / 1.3265140 ≤ 1 / a := one_div_le_one_div_of_le (by linarith) hau
  have n1 : (1 : ℝ) / 1.3231557 ≤ 0.759998 := by norm_num
  have n2 : (0.750202 : ℝ) ≤ 1 / 1.3265140 := by norm_num
  constructor <;> linarith

/-- **THREE COUPLINGS.** For all real `a`, `b` and every natural `p`: constraints 1, 3, 4 (the
three gauge-coupling windows, no helium, no τ/e) force `p = 15` and put `(a, b)` in the
outward-rounded box `[1.3231557, 1.3265140] × [1.2191706, 1.2220763]`, with `1 < b < a`. -/
theorem three_couplings (a b : ℝ) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b →
      p = 15 ∧ 1.3231557 ≤ a ∧ a ≤ 1.3265140 ∧ 1.2191706 ≤ b ∧ b ≤ 1.2220763 ∧ 1 < b ∧ b < a := by
  intro h1 h3 h4
  obtain ⟨ha, hb, hb43⟩ := near_of_C1_C3_C4 h1 h3 h4
  obtain ⟨hal, hau⟩ := a_of_C3_C4_of_le ha hb hb43 h3 h4
  obtain ⟨hbl, hbu⟩ := b_of_C4_wide hal hau hb (by linarith) h4
  have hp : p = 15 := p_of_C1_wide hal hau hbl hbu h1
  subst hp
  obtain ⟨x1, x2, x3, x4⟩ := box_of_C1_C4 ha hb h1 h4
  exact ⟨rfl, x1, x2, x3, x4, hb, by linarith⟩

/-- **THE EXACT SET.** Constraints 1, 3, 4 hold exactly when `p = 15`, `1 < a`, `1 < b` and
constraints 1 (at 15) and 4 hold: on `1 < a`, `1 < b`, constraint 3 follows from 1 and 4. -/
theorem three_couplings_iff (a b : ℝ) (p : ℕ) :
    (C1 a b p ∧ C3 a b ∧ C4 a b) ↔ (p = 15 ∧ 1 < a ∧ 1 < b ∧ C1 a b 15 ∧ C4 a b) := by
  constructor
  · rintro ⟨h1, h3, h4⟩
    have hp := (three_couplings a b p h1 h3 h4).1
    subst hp
    obtain ⟨ha, hb⟩ := one_lt_of_C3_C4 h3 h4
    exact ⟨rfl, ha, hb, h1, h4⟩
  · rintro ⟨hp, ha, hb, h1, h4⟩
    subst hp
    obtain ⟨x1, x2, x3, x4⟩ := box_of_C1_C4 ha hb h1 h4
    exact ⟨h1, C3_of_box x1 x2 x3 x4, h4⟩

/-- **HELIUM FOLLOWS.** Constraints 1, 3, 4 imply constraint 2, for all real `a`, `b`. -/
theorem helium_of_three_couplings (a b : ℝ) (p : ℕ) : C1 a b p → C3 a b → C4 a b → C2 a := by
  intro h1 h3 h4
  obtain ⟨_, x1, x2, _⟩ := three_couplings a b p h1 h3 h4
  exact C2_of_box x1 x2

#print axioms three_couplings
#print axioms three_couplings_iff
#print axioms helium_of_three_couplings

end ExclusionRegion
