module

public import Mathlib
public import ExclusionRegion.Defs

@[expose] public section

namespace ExclusionRegion

open Real

/-! General tools: windows as two-sided bounds, root brackets, power brackets, and the two
cross-multiplied monotonicity facts for `(x-1)/x^4` and `(x-1)^3/x^5`. -/

theorem win {x t w : ℝ} : |x - t| ≤ w ↔ t - w ≤ x ∧ x ≤ t + w := by
  rw [abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem C1_iff {a b : ℝ} {p : ℕ} :
    C1 a b p ↔ 136.35082 ≤ (a * b) ^ p / π ^ 2 ∧ (a * b) ^ p / π ^ 2 ≤ 137.72118 := by
  unfold C1 T1; rw [win]; norm_num

theorem C2_iff {a : ℝ} : C2 a ↔ 0.240002 ≤ lam a ∧ lam a ≤ 0.249798 := by
  unfold C2 T2; rw [win]; norm_num

theorem C3_iff {a b : ℝ} :
    C3 a b ↔ 0.2265858 ≤ lam b / (psi a b) ^ 3 ∧ lam b / (psi a b) ^ 3 ≤ 0.2358342 := by
  unfold C3 T3; rw [win]; norm_num

theorem C4_iff {a b : ℝ} :
    C4 a b ↔ 0.11564 ≤ (lam b) ^ 3 / (4 * (lam a) ^ 3 * (psi a b) ^ 2) ∧
      (lam b) ^ 3 / (4 * (lam a) ^ 3 * (psi a b) ^ 2) ≤ 0.12036 := by
  unfold C4 T4; rw [win]; norm_num

theorem C5_iff {a : ℝ} {k : ℕ} : C5 a k ↔ 3407.656 ≤ a ^ k ∧ a ^ k ≤ 3546.744 := by
  unfold C5 T5; rw [win]; norm_num

theorem A_iff {a b : ℝ} :
    A a b ↔ 3407.656 ≤ a ^ 29 ∧ a ^ 29 ≤ 3546.744 ∧
      136.35082 * π ^ 2 ≤ (a * b) ^ 15 ∧ (a * b) ^ 15 ≤ 137.72118 * π ^ 2 := by
  unfold A T1
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨h1, h2, ?_, ?_⟩ <;> linarith

/-- For `1 ≤ x ≤ y`, `y - x ≤ y^(n+1) - x^(n+1)`. -/
theorem sub_le_pow_sub {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    y - x ≤ y ^ (n + 1) - x ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 1 ≤ x ^ (n + 1) := one_le_pow₀ hx
    have hy : 0 ≤ y := by linarith
    have h1 : 0 ≤ y - x := by linarith
    have e : y ^ (n + 1 + 1) - x ^ (n + 1 + 1)
        = y * (y ^ (n + 1) - x ^ (n + 1)) + (y - x) * x ^ (n + 1) := by ring
    have p1 : 0 ≤ y * (y ^ (n + 1) - x ^ (n + 1)) := mul_nonneg hy (by linarith)
    have p2 : (y - x) * 1 ≤ (y - x) * x ^ (n + 1) := mul_le_mul_of_nonneg_left hxn h1
    rw [e]; linarith

/-- For `1 ≤ x < y` and `n ≥ 2`, `y - x < y^n - x^n`. -/
theorem sub_lt_pow_sub {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y) {n : ℕ} (hn : 2 ≤ n) :
    y - x < y ^ n - x ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have h := sub_le_pow_sub hx hxy.le m
  have hxn : 1 ≤ x ^ (m + 1) := one_le_pow₀ hx
  have hy : 0 < y := by linarith
  have h1 : 0 < y - x := by linarith
  have e : y ^ (m + 1 + 1) - x ^ (m + 1 + 1)
      = y * (y ^ (m + 1) - x ^ (m + 1)) + (y - x) * x ^ (m + 1) := by ring
  have p1 : y * (y - x) ≤ y * (y ^ (m + 1) - x ^ (m + 1)) := mul_le_mul_of_nonneg_left h hy.le
  have p2 : (y - x) * 1 ≤ (y - x) * x ^ (m + 1) := mul_le_mul_of_nonneg_left hxn h1.le
  have p3 : 0 < y * (y - x) := mul_pos hy h1
  rw [e]; linarith

/-- `x ↦ x^n - x - 1` is strictly increasing on `[1, ∞)` for `n ≥ 2`. -/
theorem strictMonoOn_pow_sub_sub_one {n : ℕ} (hn : 2 ≤ n) :
    StrictMonoOn (fun x : ℝ => x ^ n - x - 1) (Set.Ici 1) := by
  intro x hx y _ hxy
  have := sub_lt_pow_sub (Set.mem_Ici.mp hx) hxy hn
  show x ^ n - x - 1 < y ^ n - y - 1
  linarith

/-- Lower bracket for a root of `x^n = x + 1` above 1. -/
theorem root_gt {n : ℕ} (hn : 2 ≤ n) {x l : ℝ} (hx : 1 ≤ x) (hroot : x ^ n = x + 1)
    (hl' : l ^ n < l + 1) : l < x := by
  by_contra h
  have h := not_lt.mp h
  rcases eq_or_lt_of_le h with h | h
  · rw [h] at hroot; linarith
  · have := sub_lt_pow_sub hx h hn; linarith

/-- Upper bracket for a root of `x^n = x + 1` above 1. -/
theorem root_lt {n : ℕ} (hn : 2 ≤ n) {x u : ℝ} (hroot : x ^ n = x + 1)
    (hu : 1 ≤ u) (hu' : u + 1 < u ^ n) : x < u := by
  by_contra h
  have h := not_lt.mp h
  rcases eq_or_lt_of_le h with h | h
  · rw [h] at hu'; linarith
  · have := sub_lt_pow_sub hu h hn; linarith

theorem pos_of_pow29 {a : ℝ} (h : 3407.656 ≤ a ^ 29) : 0 < a :=
  (Odd.pow_pos_iff ⟨14, by norm_num⟩).mp (lt_of_lt_of_le (by norm_num) h)

/-- Bracket for `a` from the window on `a^29`, with numeric side conditions. -/
theorem pow29_bracket {a l u : ℝ} (hu0 : 0 ≤ u) (hl : l ^ 29 ≤ 3407.656)
    (hu : 3546.744 ≤ u ^ 29) (h1 : 3407.656 ≤ a ^ 29) (h2 : a ^ 29 ≤ 3546.744) :
    l ≤ a ∧ a ≤ u := by
  have ha := pos_of_pow29 h1
  constructor
  · by_contra hc
    have hc := not_le.mp hc
    have := pow_lt_pow_left₀ hc ha.le (by norm_num : (29 : ℕ) ≠ 0)
    linarith
  · by_contra hc
    have hc := not_le.mp hc
    have := pow_lt_pow_left₀ hc hu0 (by norm_num : (29 : ℕ) ≠ 0)
    linarith

/-- `(x-1)/x^4` is nondecreasing on `[1, 4/3]`, cross-multiplied. -/
theorem g3_cross {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 4 / 3) :
    (x - 1) * y ^ 4 ≤ (y - 1) * x ^ 4 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = 1 + u := ⟨x - 1, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, y = 1 + v := ⟨y - 1, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : v ≤ 1 / 3 := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hu3 : u ≤ 1 / 3 := by linarith
  have hw0 : 0 ≤ u * v := mul_nonneg hu hv0
  have hw : u * v ≤ 1 / 3 * (1 / 3) := mul_le_mul hu3 hv hv0 (by norm_num)
  have huu : u * u ≤ 1 / 3 * (1 / 3) := mul_le_mul hu3 hu3 hu (by norm_num)
  have hvv : v * v ≤ 1 / 3 * (1 / 3) := mul_le_mul hv hv hv0 (by norm_num)
  have hS : u + v ≤ 2 / 3 := by linarith
  have hS0 : 0 ≤ u + v := by linarith
  have hR : u ^ 2 + u * v + v ^ 2 ≤ 1 / 3 := by nlinarith
  have hR0 : 0 ≤ u ^ 2 + u * v + v ^ 2 := by nlinarith [sq_nonneg u, sq_nonneg v]
  have h1 : u * v * (u + v) ≤ 1 / 9 * (2 / 3) := mul_le_mul (by linarith) hS hS0 (by norm_num)
  have h2 : u * v * (u ^ 2 + u * v + v ^ 2) ≤ 1 / 9 * (1 / 3) :=
    mul_le_mul (by linarith) hR hR0 (by norm_num)
  have hG : 0 ≤ 1 - 6 * (u * v) - 4 * (u * v * (u + v)) - u * v * (u ^ 2 + u * v + v ^ 2) := by
    linarith
  have e : (1 + v - 1) * (1 + u) ^ 4 - (1 + u - 1) * (1 + v) ^ 4
      = (v - u) * (1 - 6 * (u * v) - 4 * (u * v * (u + v)) - u * v * (u ^ 2 + u * v + v ^ 2)) := by
    ring
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ v - u) hG
  linarith

/-- `(x-1)^3/x^5` is nondecreasing on `[1, 2]`, cross-multiplied. -/
theorem g4_cross {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2) :
    (x - 1) ^ 3 * y ^ 5 ≤ (y - 1) ^ 3 * x ^ 5 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = 1 + u := ⟨x - 1, by ring⟩
  obtain ⟨v, rfl⟩ : ∃ v, y = 1 + v := ⟨y - 1, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hv : v ≤ 1 := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hu1 : u ≤ 1 := by linarith
  have hw0 : 0 ≤ u * v := mul_nonneg hu hv0
  have hw1 : u * v ≤ 1 := by
    have := mul_le_mul hu1 hv hv0 (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hS : u + v ≤ 2 := by linarith
  have hS0 : 0 ≤ u + v := by linarith
  have hR0 : 0 ≤ u ^ 2 + u * v + v ^ 2 := by nlinarith [sq_nonneg u, sq_nonneg v]
  have hwS0 : 0 ≤ u * v * (u + v) := mul_nonneg hw0 hS0
  have hw2 : 0 ≤ (u * v) ^ 2 := sq_nonneg _
  have hw3 : (u * v) ^ 2 * (u * v) ≤ (u * v) ^ 2 * 1 := mul_le_mul_of_nonneg_left hw1 hw2
  have hw3' : 0 ≤ (u * v) ^ 3 := pow_nonneg hw0 3
  have hwS : (u * v) ^ 3 * (u + v) ≤ (u * v) ^ 3 * 2 := mul_le_mul_of_nonneg_left hS hw3'
  have hG : 0 ≤ (u ^ 2 + u * v + v ^ 2) + 5 * (u * v * (u + v)) + 10 * (u * v) ^ 2
      - 5 * (u * v) ^ 3 - (u * v) ^ 3 * (u + v) := by
    nlinarith
  have e : (1 + v - 1) ^ 3 * (1 + u) ^ 5 - (1 + u - 1) ^ 3 * (1 + v) ^ 5
      = (v - u) * ((u ^ 2 + u * v + v ^ 2) + 5 * (u * v * (u + v)) + 10 * (u * v) ^ 2
          - 5 * (u * v) ^ 3 - (u * v) ^ 3 * (u + v)) := by
    ring
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ v - u) hG
  linarith

/-- Closed form of the constraint-3 quantity. -/
theorem C3val_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    lam b / (psi a b) ^ 3 = (b - 1) * a ^ 3 / b ^ 4 := by
  unfold lam psi; field_simp

/-- Closed form of the constraint-4 quantity. -/
theorem C4val_eq {a b : ℝ} (ha : 1 < a) (hb : 0 < b) :
    (lam b) ^ 3 / (4 * (lam a) ^ 3 * (psi a b) ^ 2)
      = (b - 1) ^ 3 * a ^ 5 / (4 * (a - 1) ^ 3 * b ^ 5) := by
  have ha0 : 0 < a := by linarith
  have ha1 : a - 1 ≠ 0 := by intro h; linarith
  unfold lam psi; field_simp

theorem C3_poly {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : C3 a b) :
    0.2265858 * b ^ 4 ≤ (b - 1) * a ^ 3 ∧ (b - 1) * a ^ 3 ≤ 0.2358342 * b ^ 4 := by
  rw [C3_iff, C3val_eq ha hb, le_div_iff₀ (pow_pos hb 4), div_le_iff₀ (pow_pos hb 4)] at h
  exact h

theorem C4_den_pos {a b : ℝ} (ha : 1 < a) (hb : 0 < b) : 0 < 4 * (a - 1) ^ 3 * b ^ 5 :=
  mul_pos (mul_pos (by norm_num) (pow_pos (by linarith) 3)) (pow_pos hb 5)

theorem C4_poly {a b : ℝ} (ha : 1 < a) (hb : 0 < b) (h : C4 a b) :
    0.11564 * (4 * (a - 1) ^ 3 * b ^ 5) ≤ (b - 1) ^ 3 * a ^ 5 ∧
      (b - 1) ^ 3 * a ^ 5 ≤ 0.12036 * (4 * (a - 1) ^ 3 * b ^ 5) := by
  rw [C4_iff, C4val_eq ha hb, le_div_iff₀ (C4_den_pos ha hb), div_le_iff₀ (C4_den_pos ha hb)] at h
  exact h

/-- Upper bound for the constraint-4 quantity on `a ≥ aL`, `b ≤ β`. -/
theorem C4val_le {a b aL β : ℝ} (haL : 1 < aL) (ha : aL ≤ a) (ha2 : a ≤ 2)
    (hb : 1 < b) (hbβ : b ≤ β) (hβ : β ≤ 2) :
    (lam b) ^ 3 / (4 * (lam a) ^ 3 * (psi a b) ^ 2)
      ≤ (β - 1) ^ 3 * aL ^ 5 / (4 * (aL - 1) ^ 3 * β ^ 5) := by
  have ha1 : 1 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hβ0 : 0 < β := by linarith
  rw [C4val_eq ha1 hb0, div_le_div_iff₀ (C4_den_pos ha1 hb0) (C4_den_pos haL hβ0)]
  have h1 := g4_cross hb.le hbβ hβ
  have h2 := g4_cross haL.le ha ha2
  have n1 : 0 ≤ (aL - 1) ^ 3 * a ^ 5 :=
    mul_nonneg (pow_nonneg (by linarith) 3) (pow_nonneg (by linarith) 5)
  have n2 : 0 ≤ (β - 1) ^ 3 * b ^ 5 :=
    mul_nonneg (pow_nonneg (by linarith) 3) (pow_nonneg hb0.le 5)
  have h := mul_le_mul h1 h2 n1 n2
  calc (b - 1) ^ 3 * a ^ 5 * (4 * (aL - 1) ^ 3 * β ^ 5)
      = 4 * ((b - 1) ^ 3 * β ^ 5 * ((aL - 1) ^ 3 * a ^ 5)) := by ring
    _ ≤ 4 * ((β - 1) ^ 3 * b ^ 5 * ((a - 1) ^ 3 * aL ^ 5)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (β - 1) ^ 3 * aL ^ 5 * (4 * (a - 1) ^ 3 * b ^ 5) := by ring

/-- Lower bound for the constraint-4 quantity on `a ≤ aU`, `b ≥ β`. -/
theorem C4val_ge {a b aU β : ℝ} (hβ : 1 < β) (hβb : β ≤ b) (hb2 : b ≤ 2)
    (ha : 1 < a) (haU : a ≤ aU) (hU2 : aU ≤ 2) :
    (β - 1) ^ 3 * aU ^ 5 / (4 * (aU - 1) ^ 3 * β ^ 5)
      ≤ (lam b) ^ 3 / (4 * (lam a) ^ 3 * (psi a b) ^ 2) := by
  have hU1 : 1 < aU := by linarith
  have hb0 : 0 < b := by linarith
  have hβ0 : 0 < β := by linarith
  rw [C4val_eq ha hb0, div_le_div_iff₀ (C4_den_pos hU1 hβ0) (C4_den_pos ha hb0)]
  have h1 := g4_cross hβ.le hβb hb2
  have h2 := g4_cross ha.le haU hU2
  have n1 : 0 ≤ (a - 1) ^ 3 * aU ^ 5 :=
    mul_nonneg (pow_nonneg (by linarith) 3) (pow_nonneg (by linarith) 5)
  have n2 : 0 ≤ (b - 1) ^ 3 * β ^ 5 :=
    mul_nonneg (pow_nonneg (by linarith) 3) (pow_nonneg hβ0.le 5)
  have h := mul_le_mul h1 h2 n1 n2
  calc (β - 1) ^ 3 * aU ^ 5 * (4 * (a - 1) ^ 3 * b ^ 5)
      = 4 * ((β - 1) ^ 3 * b ^ 5 * ((a - 1) ^ 3 * aU ^ 5)) := by ring
    _ ≤ 4 * ((b - 1) ^ 3 * β ^ 5 * ((aU - 1) ^ 3 * a ^ 5)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (b - 1) ^ 3 * a ^ 5 * (4 * (aU - 1) ^ 3 * β ^ 5) := by ring

#print axioms strictMonoOn_pow_sub_sub_one
#print axioms root_gt
#print axioms root_lt
#print axioms pow29_bracket
#print axioms g3_cross
#print axioms g4_cross
#print axioms C4val_le
#print axioms C4val_ge

end ExclusionRegion
