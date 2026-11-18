module

public import Mathlib
public import ExclusionRegion.Brackets
public import ExclusionRegion.NonVacuity
public import ExclusionRegion.WindowCheck
public import ExclusionRegion.WindowControls
public import ExclusionRegion.UnitsForm

@[expose] public section

namespace ExclusionRegion

open Polynomial

/-! NON-VACUITY and CONTROLS for the units form. Non-vacuity: `x³ − x − 1 ∈ cubicUnits 10` and
`x⁴ − x − 1 ∈ quarticNormNeg 10`, with a real root in the a-window, respectively the slice `S`.
Controls (each intruder root located by a sign change at rational endpoints):
- height: `x⁴ + 7x³ − 11x² + 2x − 1` (constant term `−1`, height 11) has a real root in `S` that is
  not a root of `x⁴ = x + 1`; so the quartic height bound 10 is load-bearing.
- norm: `x⁴ + 10x³ − 7x² − 9x + 1` (constant term `+1`, height 10) has a real root in `S` that is not
  a root of `x⁴ = x + 1`; so the constant-term condition `−1` is load-bearing.
- cubic height: `x³ − 17x² + 20x + 1` (constant term `+1`, height 20) has a real root in the
  a-window that is not a root of `x³ = x + 1`. (The scope gate's probe found no intruder below
  height 20 for the cubic; only height 10 is stated here.) -/

/-- A list with leading `1`: the polynomial is monic of degree `l.length`. -/
theorem ofList_snoc_one (l : List ℤ) :
    (ofList (l ++ [1])).Monic ∧ (ofList (l ++ [1])).natDegree = l.length := by
  have hc := coeff_ofList (l ++ [1])
  have htop : (l ++ [1]).getD l.length 0 = 1 := by simp [List.getD_eq_getElem?_getD]
  have hdeg : (ofList (l ++ [1])).natDegree = l.length := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hc, htop]; norm_num)
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hc, List.getD_eq_default]
    simp only [List.length_append, List.length_singleton]
    have : l.length < N := by exact_mod_cast hN
    omega
  exact ⟨by rw [Monic, leadingCoeff, hdeg, hc, htop], hdeg⟩

/-- Height of `ofList cs` from a bound on the list entries. -/
theorem ofList_height (cs : List ℤ) {H : ℤ} (h0 : 0 ≤ H) (hH : ∀ c ∈ cs, |c| ≤ H) (i : ℕ) :
    |(ofList cs).coeff i| ≤ H := by
  rw [coeff_ofList, List.getD_eq_getElem?_getD]
  cases h : cs[i]? with
  | none => simpa using h0
  | some v => exact hH v (List.mem_of_getElem? h)

/-! ## Non-vacuity -/

theorem f3_mem_cubicUnits10 : ofList f3L ∈ cubicUnits 10 := by
  have h := ofList_snoc_one [-1, -1, 0]
  refine ⟨h.1, h.2, ofList_height _ (by norm_num) (by decide), Or.inr ?_⟩
  rw [coeff_ofList]; decide

theorem f4_mem_quarticNormNeg10 : ofList f4L ∈ quarticNormNeg 10 := by
  have h := ofList_snoc_one [-1, -1, 0, 0]
  refine ⟨h.1, h.2, ofList_height _ (by norm_num) (by decide), ?_⟩
  rw [coeff_ofList]; decide

/-- NON-VACUITY (units, a): `x³ − x − 1 ∈ cubicUnits 10` has a real root in the a-window. -/
theorem units_window_a_nonvacuous : ∃ P ∈ cubicUnits 10, ∃ x : ℝ, aeval x P = 0 ∧
    (1.3231557 : ℝ) ≤ x ∧ x ≤ 1.3265140 ∧ x ^ 3 = x + 1 := by
  obtain ⟨a, ha, h3⟩ := exists_cubic_root
  refine ⟨ofList f3L, f3_mem_cubicUnits10, a, ?_, (rho_in_window ha h3).1,
    (rho_in_window ha h3).2, h3⟩
  rw [ofList_f3L]; simp; linarith

/-- NON-VACUITY (units, S): `x⁴ − x − 1 ∈ quarticNormNeg 10` has a real root in `S`. -/
theorem units_window_S_nonvacuous : ∃ P ∈ quarticNormNeg 10, ∃ x : ℝ, aeval x P = 0 ∧
    (1.22032003 : ℝ) ≤ x ∧ x ≤ 1.22113387 ∧ x ^ 4 = x + 1 := by
  obtain ⟨b, hb, h4⟩ := exists_quartic_root
  refine ⟨ofList f4L, f4_mem_quarticNormNeg10, b, ?_, (Q_in_S hb h4).1, (Q_in_S hb h4).2, h4⟩
  rw [ofList_f4L]; simp; linarith

/-! ## Controls -/

/-- `x⁴ + 7x³ − 11x² + 2x − 1` (height 11, constant term `−1`). -/
def U11 : List ℤ := [-1, 2, -11, 7, 1]
/-- `x⁴ + 10x³ − 7x² − 9x + 1` (height 10, constant term `+1`). -/
def U10p : List ℤ := [1, -9, -7, 10, 1]
/-- `x³ − 17x² + 20x + 1` (height 20, constant term `+1`). -/
def U20c : List ℤ := [1, 20, -17, 1]

theorem ofList_U11 : ofList U11 = X ^ 4 + 7 * X ^ 3 - 11 * X ^ 2 + 2 * X - 1 := by
  simp only [U11, ofList]; simp; ring

theorem ofList_U10p : ofList U10p = X ^ 4 + 10 * X ^ 3 - 7 * X ^ 2 - 9 * X + 1 := by
  simp only [U10p, ofList]; simp; ring

theorem ofList_U20c : ofList U20c = X ^ 3 - 17 * X ^ 2 + 20 * X + 1 := by
  simp only [U20c, ofList]; simp; ring

/-- No root of `x³ = x + 1` lies in `[1, 1.3247]`. -/
theorem not_cubic_root_below {x : ℝ} (h1 : 1 ≤ x) (hx : x ≤ 1.3247) : x ^ 3 ≠ x + 1 := by
  intro h3
  have := root_gt (by norm_num) h1 h3 (l := 1.3247) (by norm_num)
  linarith

/-- CONTROL (height, quartic): `x⁴ + 7x³ − 11x² + 2x − 1` is in `quarticNormNeg 11`, not in
`quarticNormNeg 10`, and has a real root in `S` that is not a root of `x⁴ = x + 1`. -/
theorem control_units_height_S : ofList U11 ∈ quarticNormNeg 11 ∧ ofList U11 ∉ quarticNormNeg 10 ∧
    ∃ x : ℝ, aeval x (ofList U11) = 0 ∧
      (1.22032003 : ℝ) ≤ x ∧ x ≤ 1.22113387 ∧ x ^ 4 ≠ x + 1 := by
  have h := ofList_snoc_one [-1, 2, -11, 7]
  refine ⟨⟨h.1, h.2, ofList_height _ (by norm_num) (by decide), ?_⟩, ?_, ?_⟩
  · rw [coeff_ofList]; decide
  · rintro ⟨-, -, hH, -⟩
    have := hH 2
    rw [coeff_ofList] at this
    revert this; decide
  · obtain ⟨x, hl, hu, h0⟩ := root_of_sign_change U11 (l := 1.22044) (u := 1.22045)
      (by norm_num) (Or.inl ⟨by simp only [U11, evR]; norm_num, by simp only [U11, evR]; norm_num⟩)
    exact ⟨x, by rw [aeval_ofList]; exact h0, by linarith, by linarith,
      not_quartic_root_below (by linarith) (by linarith)⟩

/-- CONTROL (norm): `x⁴ + 10x³ − 7x² − 9x + 1` is a monic quartic of height at most 10 with
constant term `+1` (it misses `quarticNormNeg 10` by its constant term alone), and has a real
root in `S` that is not a root of `x⁴ = x + 1`. -/
theorem control_units_norm_S : ((ofList U10p).Monic ∧ (ofList U10p).natDegree = 4 ∧
    (∀ i, |(ofList U10p).coeff i| ≤ (10 : ℤ)) ∧ (ofList U10p).coeff 0 = 1) ∧
    ∃ x : ℝ, aeval x (ofList U10p) = 0 ∧
      (1.22032003 : ℝ) ≤ x ∧ x ≤ 1.22113387 ∧ x ^ 4 ≠ x + 1 := by
  have h := ofList_snoc_one [1, -9, -7, 10]
  refine ⟨⟨h.1, h.2, ofList_height _ (by norm_num) (by decide), ?_⟩, ?_⟩
  · rw [coeff_ofList]; decide
  · obtain ⟨x, hl, hu, h0⟩ := root_of_sign_change U10p (l := 1.22096) (u := 1.22097)
      (by norm_num) (Or.inl ⟨by simp only [U10p, evR]; norm_num, by simp only [U10p, evR]; norm_num⟩)
    exact ⟨x, by rw [aeval_ofList]; exact h0, by linarith, by linarith,
      not_quartic_root_above (by linarith)⟩

/-- CONTROL (height, cubic): `x³ − 17x² + 20x + 1` is in `cubicUnits 20`, not in `cubicUnits 10`,
and has a real root in the a-window that is not a root of `x³ = x + 1`. -/
theorem control_units_height_a : ofList U20c ∈ cubicUnits 20 ∧ ofList U20c ∉ cubicUnits 10 ∧
    ∃ x : ℝ, aeval x (ofList U20c) = 0 ∧
      (1.3231557 : ℝ) ≤ x ∧ x ≤ 1.3265140 ∧ x ^ 3 ≠ x + 1 := by
  have h := ofList_snoc_one [1, 20, -17]
  refine ⟨⟨h.1, h.2, ofList_height _ (by norm_num) (by decide), Or.inl ?_⟩, ?_, ?_⟩
  · rw [coeff_ofList]; decide
  · rintro ⟨-, -, hH, -⟩
    have := hH 1
    rw [coeff_ofList] at this
    revert this; decide
  · obtain ⟨x, hl, hu, h0⟩ := root_of_sign_change U20c (l := 1.32401) (u := 1.32402)
      (by norm_num) (Or.inr ⟨by simp only [U20c, evR]; norm_num, by simp only [U20c, evR]; norm_num⟩)
    exact ⟨x, by rw [aeval_ofList]; exact h0, by linarith, by linarith,
      not_cubic_root_below (by linarith) (by linarith)⟩

/-! ## The checker is not vacuous: it REJECTS each control on its window, with exactly the
arguments of the units certificates. -/

theorem checker_rejects_U11 :
    winCheck f4L 10 122032003 122113387 100000000 2 U11 = false := by decide +kernel

theorem checker_rejects_U10p :
    winCheck f4L 10 122032003 122113387 100000000 2 U10p = false := by decide +kernel

theorem checker_rejects_U20c :
    winCheck f3L 10 13231557 13265140 10000000 2 U20c = false := by decide +kernel

#print axioms ofList_snoc_one
#print axioms ofList_height
#print axioms units_window_a_nonvacuous
#print axioms units_window_S_nonvacuous
#print axioms control_units_height_S
#print axioms control_units_norm_S
#print axioms control_units_height_a
#print axioms checker_rejects_U11
#print axioms checker_rejects_U10p
#print axioms checker_rejects_U20c

end ExclusionRegion
