module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.DefsGravity
public import ExclusionRegion.Gauge
public import ExclusionRegion.SliceC1
public import ExclusionRegion.Cell42
public import ExclusionRegion.Cell43
public import ExclusionRegion.Cell52
public import ExclusionRegion.UnitsForm

@[expose] public section

namespace ExclusionRegion

open Polynomial

/-! COROLLARIES of the window theorems. Route: `three_couplings` (F:520) puts `a` in the a-window
`[1.3231557, 1.3265140]`, `p = 15` and `1 < b`; the a-window theorem gives `a³ = a + 1`;
`slice_of_C1` puts `b` in the slice `S`; the S-window theorem gives `b⁴ = b + 1`.

The three-coupling form (constraints 1, 3, 4: no helium, no τ/e) is the content; the five-constraint
form and the form with gravity follow from it by dropping hypotheses — constraints 2, 5 and G are
not used in their proofs. Nothing here orders candidates beyond the stated sets. -/

/-- The route, for any two sets of integer polynomials whose a-window and S-window theorems hold. -/
theorem forced_of_windows {Sa Sb : Set ℤ[X]}
    (hwa : ∀ P ∈ Sa, ∀ x : ℝ, aeval x P = 0 → (1.3231557 : ℝ) ≤ x → x ≤ 1.3265140 → x ^ 3 = x + 1)
    (hwS : ∀ P ∈ Sb, ∀ x : ℝ, aeval x P = 0 →
      (1.22032003 : ℝ) ≤ x → x ≤ 1.22113387 → x ^ 4 = x + 1)
    {Pa Pb : ℤ[X]} (hPa : Pa ∈ Sa) (hPb : Pb ∈ Sb) {a b : ℝ} (ha : aeval a Pa = 0)
    (hb : aeval b Pb = 0) {p : ℕ} (h1 : C1 a b p) (h3 : C3 a b) (h4 : C4 a b) :
    a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b := by
  obtain ⟨hp, hal, hau, _, _, hb1, _⟩ := three_couplings a b p h1 h3 h4
  subst hp
  have ha3 : a ^ 3 = a + 1 := hwa Pa hPa a ha hal hau
  obtain ⟨hbl, hbu⟩ := slice_of_C1 a b ha3 (by linarith) h1
  exact ⟨ha3, hwS Pb hPb b hb hbl hbu, hb1⟩

/-- The equalities are with the unique real roots above 1. -/
theorem eq_of_forced {a b : ℝ} (h : a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b) :
    ∀ r s : ℝ, 1 < r → r ^ 3 = r + 1 → 1 < s → s ^ 4 = s + 1 → a = r ∧ b = s := by
  intro r s hr hr3 hs hs4
  obtain ⟨ha3, hb4, hb⟩ := h
  have ha : 1 < a := by
    by_contra hc
    have hc := not_lt.mp hc
    rcases le_or_gt 0 a with h0 | h0
    · nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr hc)) (by linarith : (0 : ℝ) ≤ a + 1)]
    · have h3 : a ^ 3 < 0 := Odd.pow_neg ⟨1, by norm_num⟩ h0
      have : a < -1 := by linarith
      nlinarith [mul_pos (mul_pos (neg_pos.mpr h0) (by linarith : (0 : ℝ) < 1 - a))
        (by linarith : (0 : ℝ) < -a - 1)]
  exact ⟨cubic_root_unique ha hr ha3 hr3, quartic_root_unique hb hs hb4 hs4⟩

/-! ### The cell (4, 2) -/

/-- **THREE COUPLINGS, cell42.** In the cell (4, 2): real roots `a`, `b` passing constraints 1, 3, 4 (the
three gauge-coupling windows) satisfy `a³ = a + 1`, `b⁴ = b + 1`, `1 < b`. -/
theorem cell42_three_couplings (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 4 2) (hPb : Pb ∈ cell 4 2) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h1 h3 h4 => forced_of_windows cell42_window_a cell42_window_S hPa hPb ha hb h1 h3 h4

/-- **FIVE CONSTRAINTS, cell42.** The same conclusion from the five constraints. -/
theorem cell42_five (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 4 2) (hPb : Pb ∈ cell 4 2) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p k : ℕ) :
    C1 a b p ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a k → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h => forced_of_windows cell42_window_a cell42_window_S hPa hPb ha hb h.1 h.2.2.1 h.2.2.2.1

/-- **WITH GRAVITY, cell42.** The same conclusion from constraints 1, 3, 4 and G. -/
theorem cell42_gravity (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 4 2) (hPb : Pb ∈ cell 4 2) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p n : ℕ) :
    C1 a b p → C3 a b → C4 a b → CG a b n → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h1 h3 h4 _ => forced_of_windows cell42_window_a cell42_window_S hPa hPb ha hb h1 h3 h4

/-- **THREE COUPLINGS, cell42, named roots.** `a` and `b` are THE real roots above 1 of
`x³ = x + 1` and `x⁴ = x + 1`. -/
theorem cell42_three_couplings_eq (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 4 2) (hPb : Pb ∈ cell 4 2) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b →
      ∀ r s : ℝ, 1 < r → r ^ 3 = r + 1 → 1 < s → s ^ 4 = s + 1 → a = r ∧ b = s :=
  fun h1 h3 h4 => eq_of_forced (forced_of_windows cell42_window_a cell42_window_S hPa hPb ha hb h1 h3 h4)

/-! ### The cell (4, 3) -/

/-- **THREE COUPLINGS, cell43.** In the cell (4, 3): real roots `a`, `b` passing constraints 1, 3, 4 (the
three gauge-coupling windows) satisfy `a³ = a + 1`, `b⁴ = b + 1`, `1 < b`. -/
theorem cell43_three_couplings (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 4 3) (hPb : Pb ∈ cell 4 3) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h1 h3 h4 => forced_of_windows cell43_window_a cell43_window_S hPa hPb ha hb h1 h3 h4

/-- **FIVE CONSTRAINTS, cell43.** The same conclusion from the five constraints. -/
theorem cell43_five (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 4 3) (hPb : Pb ∈ cell 4 3) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p k : ℕ) :
    C1 a b p ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a k → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h => forced_of_windows cell43_window_a cell43_window_S hPa hPb ha hb h.1 h.2.2.1 h.2.2.2.1

/-- **WITH GRAVITY, cell43.** The same conclusion from constraints 1, 3, 4 and G. -/
theorem cell43_gravity (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 4 3) (hPb : Pb ∈ cell 4 3) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p n : ℕ) :
    C1 a b p → C3 a b → C4 a b → CG a b n → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h1 h3 h4 _ => forced_of_windows cell43_window_a cell43_window_S hPa hPb ha hb h1 h3 h4

/-- **THREE COUPLINGS, cell43, named roots.** `a` and `b` are THE real roots above 1 of
`x³ = x + 1` and `x⁴ = x + 1`. -/
theorem cell43_three_couplings_eq (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 4 3) (hPb : Pb ∈ cell 4 3) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b →
      ∀ r s : ℝ, 1 < r → r ^ 3 = r + 1 → 1 < s → s ^ 4 = s + 1 → a = r ∧ b = s :=
  fun h1 h3 h4 => eq_of_forced (forced_of_windows cell43_window_a cell43_window_S hPa hPb ha hb h1 h3 h4)

/-! ### The cell (5, 2) -/

/-- **THREE COUPLINGS, cell52.** In the cell (5, 2): real roots `a`, `b` passing constraints 1, 3, 4 (the
three gauge-coupling windows) satisfy `a³ = a + 1`, `b⁴ = b + 1`, `1 < b`. -/
theorem cell52_three_couplings (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 5 2) (hPb : Pb ∈ cell 5 2) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h1 h3 h4 => forced_of_windows cell52_window_a cell52_window_S hPa hPb ha hb h1 h3 h4

/-- **FIVE CONSTRAINTS, cell52.** The same conclusion from the five constraints. -/
theorem cell52_five (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 5 2) (hPb : Pb ∈ cell 5 2) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p k : ℕ) :
    C1 a b p ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a k → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h => forced_of_windows cell52_window_a cell52_window_S hPa hPb ha hb h.1 h.2.2.1 h.2.2.2.1

/-- **WITH GRAVITY, cell52.** The same conclusion from constraints 1, 3, 4 and G. -/
theorem cell52_gravity (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 5 2) (hPb : Pb ∈ cell 5 2) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p n : ℕ) :
    C1 a b p → C3 a b → C4 a b → CG a b n → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h1 h3 h4 _ => forced_of_windows cell52_window_a cell52_window_S hPa hPb ha hb h1 h3 h4

/-- **THREE COUPLINGS, cell52, named roots.** `a` and `b` are THE real roots above 1 of
`x³ = x + 1` and `x⁴ = x + 1`. -/
theorem cell52_three_couplings_eq (Pa Pb : ℤ[X]) (hPa : Pa ∈ cell 5 2) (hPb : Pb ∈ cell 5 2) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b →
      ∀ r s : ℝ, 1 < r → r ^ 3 = r + 1 → 1 < s → s ^ 4 = s + 1 → a = r ∧ b = s :=
  fun h1 h3 h4 => eq_of_forced (forced_of_windows cell52_window_a cell52_window_S hPa hPb ha hb h1 h3 h4)

/-! ### The units form at height 10 (`a` a root of a monic cubic with constant term `±1`, `b` of a monic quartic with constant term `−1`, all coefficients at most 10 in absolute value) -/

/-- **THREE COUPLINGS, units10.** In the units form at height 10 (`a` a root of a monic cubic with constant term `±1`, `b` of a monic quartic with constant term `−1`, all coefficients at most 10 in absolute value): real roots `a`, `b` passing constraints 1, 3, 4 (the
three gauge-coupling windows) satisfy `a³ = a + 1`, `b⁴ = b + 1`, `1 < b`. -/
theorem units10_three_couplings (Pa Pb : ℤ[X]) (hPa : Pa ∈ cubicUnits 10) (hPb : Pb ∈ quarticNormNeg 10) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h1 h3 h4 => forced_of_windows cubicUnits10_window_a quarticNormNeg10_window_S hPa hPb ha hb h1 h3 h4

/-- **FIVE CONSTRAINTS, units10.** The same conclusion from the five constraints. -/
theorem units10_five (Pa Pb : ℤ[X]) (hPa : Pa ∈ cubicUnits 10) (hPb : Pb ∈ quarticNormNeg 10) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p k : ℕ) :
    C1 a b p ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a k → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h => forced_of_windows cubicUnits10_window_a quarticNormNeg10_window_S hPa hPb ha hb h.1 h.2.2.1 h.2.2.2.1

/-- **WITH GRAVITY, units10.** The same conclusion from constraints 1, 3, 4 and G. -/
theorem units10_gravity (Pa Pb : ℤ[X]) (hPa : Pa ∈ cubicUnits 10) (hPb : Pb ∈ quarticNormNeg 10) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p n : ℕ) :
    C1 a b p → C3 a b → C4 a b → CG a b n → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b :=
  fun h1 h3 h4 _ => forced_of_windows cubicUnits10_window_a quarticNormNeg10_window_S hPa hPb ha hb h1 h3 h4

/-- **THREE COUPLINGS, units10, named roots.** `a` and `b` are THE real roots above 1 of
`x³ = x + 1` and `x⁴ = x + 1`. -/
theorem units10_three_couplings_eq (Pa Pb : ℤ[X]) (hPa : Pa ∈ cubicUnits 10) (hPb : Pb ∈ quarticNormNeg 10) (a b : ℝ)
    (ha : aeval a Pa = 0) (hb : aeval b Pb = 0) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b →
      ∀ r s : ℝ, 1 < r → r ^ 3 = r + 1 → 1 < s → s ^ 4 = s + 1 → a = r ∧ b = s :=
  fun h1 h3 h4 => eq_of_forced (forced_of_windows cubicUnits10_window_a quarticNormNeg10_window_S hPa hPb ha hb h1 h3 h4)

#print axioms forced_of_windows
#print axioms eq_of_forced
#print axioms cell42_three_couplings
#print axioms cell42_five
#print axioms cell42_gravity
#print axioms cell42_three_couplings_eq
#print axioms cell43_three_couplings
#print axioms cell43_five
#print axioms cell43_gravity
#print axioms cell43_three_couplings_eq
#print axioms cell52_three_couplings
#print axioms cell52_five
#print axioms cell52_gravity
#print axioms cell52_three_couplings_eq
#print axioms units10_three_couplings
#print axioms units10_five
#print axioms units10_gravity
#print axioms units10_three_couplings_eq

end ExclusionRegion
