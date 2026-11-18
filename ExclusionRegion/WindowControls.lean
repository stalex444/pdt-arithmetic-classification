module

public import Mathlib
public import ExclusionRegion.Brackets
public import ExclusionRegion.NonVacuity
public import ExclusionRegion.WindowCheck

@[expose] public section

namespace ExclusionRegion

open Polynomial

/-! NON-VACUITY and CONTROLS for the window theorems. Non-vacuity: `x³ − x − 1` and `x⁴ − x − 1`
are in the cell (4, 2) and have a real root in the a-window, respectively the slice `S`.
Controls: just outside the cell (4, 2) — in (5, 3) and (7, 2) — there are polynomials with a
real root in a window that is NOT a root of the target, so the cell bound carries weight. Each
intruder root is located by a sign change at rational endpoints (intermediate value theorem). -/

/-! ## Coefficient lists as polynomials -/

theorem coeff_ofList (cs : List ℤ) (i : ℕ) : (ofList cs).coeff i = cs.getD i 0 := by
  induction cs generalizing i with
  | nil => simp [ofList]
  | cons c cs ih =>
    cases i with
    | zero => simp [ofList]
    | succ n => simp only [ofList, coeff_add, coeff_C, coeff_X_mul, ih]; simp

/-- A list `l ++ [1]` meeting the cell conditions gives a polynomial of the cell. -/
theorem ofList_mem_cell (l : List ℤ) {D H : ℕ} (h2 : 2 ≤ l.length) (hD : l.length ≤ D)
    (hH : ∀ c ∈ l, |c| ≤ (H : ℤ)) (h1 : 1 ≤ H) (h0 : l.headD 0 ≠ 0) :
    ofList (l ++ [1]) ∈ cell D H := by
  have hc := coeff_ofList (l ++ [1])
  have htop : (l ++ [1]).getD l.length 0 = 1 := by simp [List.getD_eq_getElem?_getD]
  have hzero : ∀ N, l.length < N → (l ++ [1]).getD N 0 = 0 := by
    intro N hN
    rw [List.getD_eq_default]
    simp only [List.length_append, List.length_singleton]
    omega
  have hdeg : (ofList (l ++ [1])).natDegree = l.length := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hc, htop]; norm_num)
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hc]
    exact hzero N (by exact_mod_cast hN)
  refine ⟨?_, by omega, by omega, ?_, ?_⟩
  · rw [Monic, leadingCoeff, hdeg, hc, htop]
  · intro i
    rw [hc, List.getD_eq_getElem?_getD]
    cases h : (l ++ [1])[i]? with
    | none => simp
    | some v =>
      have hv := List.mem_of_getElem? h
      rw [List.mem_append, List.mem_singleton] at hv
      simp only [Option.getD_some]
      rcases hv with hv | rfl
      · exact hH v hv
      · simp; exact_mod_cast h1
  · rw [hc]
    cases l with
    | nil => simp at h2
    | cons a l => simpa using h0

/-- `evR` is continuous. -/
theorem continuous_evR (cs : List ℤ) : Continuous (fun x => evR cs x) := by
  induction cs with
  | nil => simp only [evR]; exact continuous_const
  | cons c cs ih => simp only [evR]; exact continuous_const.add (continuous_id.mul ih)

/-- A root from a sign change (either direction). -/
theorem root_of_sign_change (cs : List ℤ) {l u : ℝ} (hlu : l ≤ u)
    (h : (evR cs l ≤ 0 ∧ 0 ≤ evR cs u) ∨ (0 ≤ evR cs l ∧ evR cs u ≤ 0)) :
    ∃ x, l ≤ x ∧ x ≤ u ∧ evR cs x = 0 := by
  have hf := (continuous_evR cs).continuousOn (s := Set.Icc l u)
  rcases h with h | h
  · obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hlu hf h
    exact ⟨x, hx.1, hx.2, hx0⟩
  · obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hlu hf ⟨h.2, h.1⟩
    exact ⟨x, hx.1, hx.2, hx0⟩

/-! ## Non-vacuity -/

theorem f3_mem_cell42 : ofList f3L ∈ cell 4 2 :=
  ofList_mem_cell [-1, -1, 0] (by decide) (by decide) (by decide) (by decide) (by decide)

theorem f4_mem_cell42 : ofList f4L ∈ cell 4 2 :=
  ofList_mem_cell [-1, -1, 0, 0] (by decide) (by decide) (by decide) (by decide) (by decide)

theorem ofList_f3L : ofList f3L = X ^ 3 - X - 1 := by
  simp only [f3L, ofList]; simp; ring

theorem ofList_f4L : ofList f4L = X ^ 4 - X - 1 := by
  simp only [f4L, ofList]; simp; ring

/-- The real root of `x³ = x + 1` above 1 lies in the a-window `[1.3231557, 1.3265140]`. -/
theorem rho_in_window {a : ℝ} (ha : 1 < a) (h3 : a ^ 3 = a + 1) :
    (1.3231557 : ℝ) ≤ a ∧ a ≤ 1.3265140 :=
  ⟨(root_gt (by norm_num) ha.le h3 (by norm_num)).le,
    (root_lt (by norm_num) h3 (by norm_num) (by norm_num)).le⟩

/-- The real root of `x⁴ = x + 1` above 1 lies in the slice `S = [1.22032003, 1.22113387]`. -/
theorem Q_in_S {b : ℝ} (hb : 1 < b) (h4 : b ^ 4 = b + 1) :
    (1.22032003 : ℝ) ≤ b ∧ b ≤ 1.22113387 :=
  ⟨(root_gt (by norm_num) hb.le h4 (by norm_num)).le,
    (root_lt (by norm_num) h4 (by norm_num) (by norm_num)).le⟩

/-- NON-VACUITY (a): a polynomial of the cell (4, 2) has a real root in the a-window. -/
theorem window_a_nonvacuous : ∃ P ∈ cell 4 2, ∃ x : ℝ, aeval x P = 0 ∧
    (1.3231557 : ℝ) ≤ x ∧ x ≤ 1.3265140 ∧ x ^ 3 = x + 1 := by
  obtain ⟨a, ha, h3⟩ := exists_cubic_root
  refine ⟨ofList f3L, f3_mem_cell42, a, ?_, (rho_in_window ha h3).1, (rho_in_window ha h3).2, h3⟩
  rw [ofList_f3L]; simp; linarith

/-- NON-VACUITY (S): a polynomial of the cell (4, 2) has a real root in the slice `S`. -/
theorem window_S_nonvacuous : ∃ P ∈ cell 4 2, ∃ x : ℝ, aeval x P = 0 ∧
    (1.22032003 : ℝ) ≤ x ∧ x ≤ 1.22113387 ∧ x ^ 4 = x + 1 := by
  obtain ⟨b, hb, h4⟩ := exists_quartic_root
  refine ⟨ofList f4L, f4_mem_cell42, b, ?_, (Q_in_S hb h4).1, (Q_in_S hb h4).2, h4⟩
  rw [ofList_f4L]; simp; linarith

/-! ## Controls: intruders just outside the cell (4, 2) -/

/-- `x⁵ + 3x⁴ − 3x³ − 3x² − 2x + 3`, in the cell (5, 3). -/
def P53S : List ℤ := [3, -2, -3, -3, 3, 1]
/-- `x⁵ + 2x⁴ − 2x³ − 3x² + 2x − 3`, in the cell (5, 3). -/
def P53A : List ℤ := [-3, 2, -3, -2, 2, 1]
/-- `x⁷ + x⁶ − 2x⁵ − x² − 2x + 2`, in the cell (7, 2). -/
def P72S : List ℤ := [2, -2, -1, 0, 0, -2, 1, 1]

theorem ofList_P53S : ofList P53S = X ^ 5 + 3 * X ^ 4 - 3 * X ^ 3 - 3 * X ^ 2 - 2 * X + 3 := by
  simp only [P53S, ofList]; simp; ring

theorem ofList_P53A : ofList P53A = X ^ 5 + 2 * X ^ 4 - 2 * X ^ 3 - 3 * X ^ 2 + 2 * X - 3 := by
  simp only [P53A, ofList]; simp; ring

theorem ofList_P72S : ofList P72S = X ^ 7 + X ^ 6 - 2 * X ^ 5 - X ^ 2 - 2 * X + 2 := by
  simp only [P72S, ofList]; simp; ring

theorem P53S_mem : ofList P53S ∈ cell 5 3 :=
  ofList_mem_cell [3, -2, -3, -3, 3] (by decide) (by decide) (by decide) (by decide) (by decide)

theorem P53A_mem : ofList P53A ∈ cell 5 3 :=
  ofList_mem_cell [-3, 2, -3, -2, 2] (by decide) (by decide) (by decide) (by decide) (by decide)

theorem P72S_mem : ofList P72S ∈ cell 7 2 :=
  ofList_mem_cell [2, -2, -1, 0, 0, -2, 1] (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- No root of `x⁴ = x + 1` lies in `[1.2203, 1.2207]` with `x ≥ 1`. -/
theorem not_quartic_root_below {x : ℝ} (h1 : 1 ≤ x) (hx : x ≤ 1.2207) : x ^ 4 ≠ x + 1 := by
  intro h4
  have := root_gt (by norm_num) h1 h4 (l := 1.2207) (by norm_num)
  linarith

/-- No root of `x⁴ = x + 1` lies above `1.2208`. -/
theorem not_quartic_root_above {x : ℝ} (hx : 1.2208 ≤ x) : x ^ 4 ≠ x + 1 := by
  intro h4
  have := root_lt (by norm_num) h4 (u := 1.2208) (by norm_num) (by norm_num)
  linarith

/-- No root of `x³ = x + 1` lies above `1.3248`. -/
theorem not_cubic_root_above {x : ℝ} (hx : 1.3248 ≤ x) : x ^ 3 ≠ x + 1 := by
  intro h3
  have := root_lt (by norm_num) h3 (u := 1.3248) (by norm_num) (by norm_num)
  linarith

/-- CONTROL (5, 3), slice `S`: `x⁵ + 3x⁴ − 3x³ − 3x² − 2x + 3` is in the cell (5, 3) and has a real
root in `S` that is not a root of `x⁴ = x + 1`. -/
theorem control53_S : ofList P53S ∈ cell 5 3 ∧ ∃ x : ℝ, aeval x (ofList P53S) = 0 ∧
    (1.22032003 : ℝ) ≤ x ∧ x ≤ 1.22113387 ∧ x ^ 4 ≠ x + 1 := by
  refine ⟨P53S_mem, ?_⟩
  obtain ⟨x, hl, hu, h0⟩ := root_of_sign_change P53S (l := 1.22039) (u := 1.22040) (by norm_num)
    (Or.inl ⟨by simp only [P53S, evR]; norm_num, by simp only [P53S, evR]; norm_num⟩)
  exact ⟨x, by rw [aeval_ofList]; exact h0, by linarith, by linarith,
    not_quartic_root_below (by linarith) (by linarith)⟩

/-- CONTROL (5, 3), a-window: `x⁵ + 2x⁴ − 2x³ − 3x² + 2x − 3` is in the cell (5, 3) and has a
real root in `[1.3231557, 1.3265140]` that is not a root of `x³ = x + 1`. -/
theorem control53_a : ofList P53A ∈ cell 5 3 ∧ ∃ x : ℝ, aeval x (ofList P53A) = 0 ∧
    (1.3231557 : ℝ) ≤ x ∧ x ≤ 1.3265140 ∧ x ^ 3 ≠ x + 1 := by
  refine ⟨P53A_mem, ?_⟩
  obtain ⟨x, hl, hu, h0⟩ := root_of_sign_change P53A (l := 1.32618) (u := 1.32620) (by norm_num)
    (Or.inl ⟨by simp only [P53A, evR]; norm_num, by simp only [P53A, evR]; norm_num⟩)
  exact ⟨x, by rw [aeval_ofList]; exact h0, by linarith, by linarith,
    not_cubic_root_above (by linarith)⟩

/-- CONTROL (7, 2), slice `S`: `x⁷ + x⁶ − 2x⁵ − x² − 2x + 2` is in the cell (7, 2) and has a real
root in `S` that is not a root of `x⁴ = x + 1`. -/
theorem control72_S : ofList P72S ∈ cell 7 2 ∧ ∃ x : ℝ, aeval x (ofList P72S) = 0 ∧
    (1.22032003 : ℝ) ≤ x ∧ x ≤ 1.22113387 ∧ x ^ 4 ≠ x + 1 := by
  refine ⟨P72S_mem, ?_⟩
  obtain ⟨x, hl, hu, h0⟩ := root_of_sign_change P72S (l := 1.22107) (u := 1.22109) (by norm_num)
    (Or.inl ⟨by simp only [P72S, evR]; norm_num, by simp only [P72S, evR]; norm_num⟩)
  exact ⟨x, by rw [aeval_ofList]; exact h0, by linarith, by linarith,
    not_quartic_root_above (by linarith)⟩

/-! ## Non-divisibility of the (5, 3) intruders, through the checker: neither has a root in
a rational bracket of the target's root above 1. -/

theorem P53S_not_dvd : ¬ (X ^ 4 - X - 1 : ℤ[X]) ∣ ofList P53S := by
  rintro ⟨g, hg⟩
  obtain ⟨b, hb, h4⟩ := exists_quartic_root
  have hlo := root_gt (by norm_num) hb.le h4 (l := 1.2207) (by norm_num)
  have hhi := root_lt (by norm_num) h4 (u := 1.2208) (by norm_num) (by norm_num)
  have hne := noRootAux_sound 0 (L := 12207) (U := 12208) (D := 10000) (cs := P53S)
    (by decide +kernel) (by norm_num) (by norm_num) (x := b) (by push_cast; linarith)
    (by push_cast; linarith)
  apply hne
  rw [← aeval_ofList, hg, map_mul]
  simp [h4]

theorem P53A_not_dvd : ¬ (X ^ 3 - X - 1 : ℤ[X]) ∣ ofList P53A := by
  rintro ⟨g, hg⟩
  obtain ⟨a, ha, h3⟩ := exists_cubic_root
  have hlo := root_gt (by norm_num) ha.le h3 (l := 1.3247) (by norm_num)
  have hhi := root_lt (by norm_num) h3 (u := 1.3248) (by norm_num) (by norm_num)
  have hne := noRootAux_sound 0 (L := 13247) (U := 13248) (D := 10000) (cs := P53A)
    (by decide +kernel) (by norm_num) (by norm_num) (x := a) (by push_cast; linarith)
    (by push_cast; linarith)
  apply hne
  rw [← aeval_ofList, hg, map_mul]
  simp [h3]

/-! ## The checker is not vacuous: it REJECTS each intruder on its window. -/

theorem checker_rejects_P53S :
    winCheck f4L 10 122032003 122113387 100000000 2 P53S = false := by decide +kernel

theorem checker_rejects_P53A :
    winCheck f3L 10 13231557 13265140 10000000 2 P53A = false := by decide +kernel

theorem checker_rejects_P72S :
    winCheck f4L 10 122032003 122113387 100000000 2 P72S = false := by decide +kernel

#print axioms coeff_ofList
#print axioms ofList_mem_cell
#print axioms rho_in_window
#print axioms Q_in_S
#print axioms window_a_nonvacuous
#print axioms window_S_nonvacuous
#print axioms control53_S
#print axioms control53_a
#print axioms control72_S
#print axioms P53S_not_dvd
#print axioms P53A_not_dvd
#print axioms checker_rejects_P53S
#print axioms checker_rejects_P53A
#print axioms checker_rejects_P72S

end ExclusionRegion
