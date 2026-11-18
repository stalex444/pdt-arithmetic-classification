module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.DefsGravity
public import ExclusionRegion.Brackets
public import ExclusionRegion.Converse
public import ExclusionRegion.Pass
public import ExclusionRegion.Unrestricted
public import ExclusionRegion.Gauge

@[expose] public section

namespace ExclusionRegion

open Real

/-! STAGE 2, GRAVITY. Constraint G is the screened form of F:510:
`(ab)^n (2b-1)/(π² b²)` within 2% of `TG = ħc/(α⁻¹·G·m_e²)` (CODATA 2022 decimals). The deposit's
tree-level row `(ab)^209/π²` is not used: against `TG` at `(ρ, Q)` it is off by +3.363% and fails a
2% window.

The windows force p = 15 and n = 209 separately. That 209 = 15² − 15 − 1, the dimension of a vector's stabilizer in sl(15) (F:254), is the derivation's account of the exponent (F:402, STANDING:65), cited here and not established by this theorem.

Route for `n`, with no 209th power: `(ab)^210 = ((ab)^15)^14` is bounded through constraint 1, and
`(ab)^208 = ((ab)^15)^14/(ab)^2`; the value is monotone in `n` because `ab > 1`. -/

theorem CG_iff {a b : ℝ} {n : ℕ} :
    CG a b n ↔ 0.98 * TG ≤ (a * b) ^ n * (2 * b - 1) / (π ^ 2 * b ^ 2) ∧
      (a * b) ^ n * (2 * b - 1) / (π ^ 2 * b ^ 2) ≤ 1.02 * TG := by
  unfold CG; rw [win]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem TG_pos : 0 < TG := by unfold TG; norm_num

/-- The gravity value split as `((ab)^n/π²) · ((2b-1)/b²)`. -/
theorem CGval_eq (a b : ℝ) (n : ℕ) :
    (a * b) ^ n * (2 * b - 1) / (π ^ 2 * b ^ 2) = (a * b) ^ n / π ^ 2 * ((2 * b - 1) / b ^ 2) := by
  ring

/-- `(2x-1)/x²` is nonincreasing on `[1, ∞)`. -/
theorem hq_anti {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (2 * y - 1) / y ^ 2 ≤ (2 * x - 1) / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rw [div_le_div_iff₀ (pow_pos hy0 2) (pow_pos hx0 2)]
  have e : (2 * x - 1) * y ^ 2 - (2 * y - 1) * x ^ 2 = (y - x) * (x * (y - 1) + y * (x - 1)) := by
    ring
  have h0 : 0 ≤ x * (y - 1) + y * (x - 1) :=
    add_nonneg (mul_nonneg hx0.le (by linarith)) (mul_nonneg hy0.le (by linarith))
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ y - x) h0
  linarith

theorem hq_le_one {x : ℝ} (hx : 0 < x) : (2 * x - 1) / x ^ 2 ≤ 1 := by
  rw [div_le_one (pow_pos hx 2)]
  nlinarith [sq_nonneg (x - 1)]

theorem hq_pos {x : ℝ} (hx : 1 ≤ x) : 0 < (2 * x - 1) / x ^ 2 :=
  div_pos (by linarith) (pow_pos (by linarith) 2)

/-- **The n-step.** With constraint 1 at 15, `b ∈ [1, 1.23]` and `ab ≥ 1.6`, constraint G admits
only `n = 209`, for every natural `n`. No 209th power is computed. -/
theorem n_of_CG {a b : ℝ} {n : ℕ} (hb1 : 1 ≤ b) (hbu : b ≤ 1.23) (hab : 1.6 ≤ a * b)
    (h1 : C1 a b 15) (hG : CG a b n) : n = 209 := by
  rw [C1_iff] at h1
  obtain ⟨y1, y2⟩ := h1
  rw [CG_iff, CGval_eq] at hG
  obtain ⟨g1, g2⟩ := hG
  set Y := (a * b) ^ 15 / π ^ 2 with hY
  have hpi : 0 < π ^ 2 := by positivity
  have hpl : (3.14 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d2.le 2
  have hpu : π ^ 2 ≤ (3.15 : ℝ) ^ 2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 2
  have hab1 : 1 ≤ a * b := by linarith
  have hb0 : 0 < b := by linarith
  have hq0 : 0 < (2 * b - 1) / b ^ 2 := hq_pos hb1
  have hql : (2 * 1.23 - 1) / (1.23 : ℝ) ^ 2 ≤ (2 * b - 1) / b ^ 2 := hq_anti hb1 hbu
  have hqu : (2 * b - 1) / b ^ 2 ≤ 1 := hq_le_one hb0
  have hTG := TG_pos
  -- `(ab)^210/π² = Y^14 (π²)^13`
  have e210 : (a * b) ^ 210 / π ^ 2 = Y ^ 14 * (π ^ 2) ^ 13 := by
    rw [hY, div_pow]
    field_simp
  have hY0 : 0 ≤ Y := by linarith
  by_contra hn
  rcases Nat.lt_or_ge n 209 with hlt | hge
  · -- `n ≤ 208`
    have e1 : (a * b) ^ n ≤ (a * b) ^ 208 := pow_le_pow_right₀ hab1 (by omega)
    have e208 : (a * b) ^ 208 / π ^ 2 * (a * b) ^ 2 = Y ^ 14 * (π ^ 2) ^ 13 := by
      rw [← e210]; ring
    have hY14 : Y ^ 14 ≤ (137.72118 : ℝ) ^ 14 := pow_le_pow_left₀ hY0 y2 14
    have hP13 : (π ^ 2) ^ 13 ≤ ((3.15 : ℝ) ^ 2) ^ 13 := pow_le_pow_left₀ hpi.le hpu 13
    have hM : Y ^ 14 * (π ^ 2) ^ 13 ≤ (137.72118 : ℝ) ^ 14 * ((3.15 : ℝ) ^ 2) ^ 13 :=
      mul_le_mul hY14 hP13 (by positivity) (by positivity)
    have hab2 : (2.56 : ℝ) ≤ (a * b) ^ 2 := by nlinarith
    have hW0 : 0 ≤ (a * b) ^ 208 / π ^ 2 := by positivity
    have hW : (a * b) ^ 208 / π ^ 2 * 2.56 ≤ (137.72118 : ℝ) ^ 14 * ((3.15 : ℝ) ^ 2) ^ 13 :=
      (mul_le_mul_of_nonneg_left hab2 hW0).trans (e208 ▸ hM)
    have hWn : (a * b) ^ n / π ^ 2 ≤ (a * b) ^ 208 / π ^ 2 := div_le_div_of_nonneg_right e1 hpi.le
    have hnum : (137.72118 : ℝ) ^ 14 * ((3.15 : ℝ) ^ 2) ^ 13 / 2.56 < 0.98 * TG := by
      unfold TG; norm_num
    have k1 : (a * b) ^ n / π ^ 2 * ((2 * b - 1) / b ^ 2) ≤ (a * b) ^ n / π ^ 2 :=
      mul_le_of_le_one_right (by positivity) hqu
    have k2 : (a * b) ^ 208 / π ^ 2 ≤ (137.72118 : ℝ) ^ 14 * ((3.15 : ℝ) ^ 2) ^ 13 / 2.56 := by
      rw [le_div_iff₀ (by norm_num)]; exact hW
    linarith
  · -- `n ≥ 210`
    have hge' : 210 ≤ n := by omega
    have e1 : (a * b) ^ 210 ≤ (a * b) ^ n := pow_le_pow_right₀ hab1 hge'
    have hY14 : (136.35082 : ℝ) ^ 14 ≤ Y ^ 14 := pow_le_pow_left₀ (by norm_num) y1 14
    have hP13 : ((3.14 : ℝ) ^ 2) ^ 13 ≤ (π ^ 2) ^ 13 := pow_le_pow_left₀ (by norm_num) hpl 13
    have hM : (136.35082 : ℝ) ^ 14 * ((3.14 : ℝ) ^ 2) ^ 13 ≤ Y ^ 14 * (π ^ 2) ^ 13 :=
      mul_le_mul hY14 hP13 (by positivity) (by positivity)
    have hWn : (a * b) ^ 210 / π ^ 2 ≤ (a * b) ^ n / π ^ 2 := div_le_div_of_nonneg_right e1 hpi.le
    have hnum : 1.02 * TG <
        (136.35082 : ℝ) ^ 14 * ((3.14 : ℝ) ^ 2) ^ 13 * ((2 * 1.23 - 1) / (1.23 : ℝ) ^ 2) := by
      unfold TG; norm_num
    have k1 : (136.35082 : ℝ) ^ 14 * ((3.14 : ℝ) ^ 2) ^ 13 * ((2 * 1.23 - 1) / (1.23 : ℝ) ^ 2) ≤
        (a * b) ^ n / π ^ 2 * ((2 * b - 1) / b ^ 2) :=
      mul_le_mul (hM.trans (e210 ▸ hWn)) hql (by norm_num) (by positivity)
    linarith

/-- **GRAVITY.** For all real `a`, `b` and all natural `p`, `n`: the three gauge-coupling windows
and gravity's window force `p = 15` and `n = 209`. -/
theorem gravity_exponent (a b : ℝ) (p n : ℕ) :
    C1 a b p → C3 a b → C4 a b → CG a b n → p = 15 ∧ n = 209 := by
  intro h1 h3 h4 hG
  obtain ⟨hp, hal, _, hbl, hbu, hb, _⟩ := three_couplings a b p h1 h3 h4
  subst hp
  have hab : 1.6 ≤ a * b := by
    have := mul_le_mul hal hbl (by norm_num) (by linarith)
    linarith
  exact ⟨rfl, n_of_CG hb.le (by linarith) hab h1 hG⟩

/-- **PASS.** At the roots (`a³ = a + 1`, `b > 1`, `b⁴ = b + 1`), constraints 1 (at 15), 3, 4 and
G (at 209) hold.

CG compares the alpha-link form (F:412, equal to α_L1/α_G) with the measured α/α_G (F:510's target): this is F:251's measured-α route. The theorem asserts window membership only; the −7.70 σ_G of F:510 is α's L1 residual expressed in G's uncertainty, not a deviation of G; the two routes are not mixed. -/
theorem gravity_pass (a b : ℝ) :
    a ^ 3 = a + 1 → 1 < b → b ^ 4 = b + 1 → C1 a b 15 ∧ C3 a b ∧ C4 a b ∧ CG a b 209 := by
  intro ha3 hb hb4
  obtain ⟨h1, _, h3, h4, _⟩ := converse a b (pass_strong a b ha3 hb hb4)
  refine ⟨h1, h3, h4, ?_⟩
  have ha := one_lt_of_cubic ha3
  obtain ⟨hal, hau⟩ := rho_bracket ha ha3
  obtain ⟨hbl, hbu⟩ := Q_bracket hb hb4
  have hpl : (3.141592 : ℝ) ^ 2 ≤ π ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_d6.le 2
  have hpu : π ^ 2 ≤ (3.141593 : ℝ) ^ 2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2
  have hpi : 0 < π ^ 2 := by positivity
  have hab_l : (1.32471 : ℝ) * 1.22074 ≤ a * b :=
    mul_le_mul hal.le hbl.le (by norm_num) (by linarith)
  have hab_u : a * b ≤ 1.32472 * 1.22075 := mul_le_mul hau.le hbu.le (by linarith) (by norm_num)
  have hab0 : 0 ≤ a * b := by linarith
  have hql : (2 * 1.22075 - 1) / (1.22075 : ℝ) ^ 2 ≤ (2 * b - 1) / b ^ 2 := hq_anti hb.le hbu.le
  have hqu : (2 * b - 1) / b ^ 2 ≤ (2 * 1.22074 - 1) / (1.22074 : ℝ) ^ 2 :=
    hq_anti (by norm_num) hbl.le
  have hq0 : 0 < (2 * b - 1) / b ^ 2 := hq_pos hb.le
  rw [CG_iff, CGval_eq]
  constructor
  · have w1 : ((1.32471 : ℝ) * 1.22074) ^ 209 / 3.141593 ^ 2 ≤ (a * b) ^ 209 / π ^ 2 :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hab_l 209) hpi hpu
    calc 0.98 * TG ≤ ((1.32471 : ℝ) * 1.22074) ^ 209 / 3.141593 ^ 2 *
          ((2 * 1.22075 - 1) / (1.22075 : ℝ) ^ 2) := by unfold TG; norm_num
      _ ≤ (a * b) ^ 209 / π ^ 2 * ((2 * b - 1) / b ^ 2) :=
          mul_le_mul w1 hql (by norm_num) (by positivity)
  · have w1 : (a * b) ^ 209 / π ^ 2 ≤ ((1.32472 : ℝ) * 1.22075) ^ 209 / 3.141592 ^ 2 :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ hab0 hab_u 209) (by norm_num) hpl
    calc (a * b) ^ 209 / π ^ 2 * ((2 * b - 1) / b ^ 2)
        ≤ ((1.32472 : ℝ) * 1.22075) ^ 209 / 3.141592 ^ 2 *
          ((2 * 1.22074 - 1) / (1.22074 : ℝ) ^ 2) :=
          mul_le_mul w1 hqu hq0.le (by positivity)
      _ ≤ 1.02 * TG := by unfold TG; norm_num

#print axioms CG_iff
#print axioms n_of_CG
#print axioms gravity_exponent
#print axioms gravity_pass

end ExclusionRegion
