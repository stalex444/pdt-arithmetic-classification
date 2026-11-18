module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.DefsGravity
public import ExclusionRegion.NonVacuity
public import ExclusionRegion.Pass
public import ExclusionRegion.Converse
public import ExclusionRegion.Gravity
public import ExclusionRegion.WindowControls
public import ExclusionRegion.UnitsControls

@[expose] public section

namespace ExclusionRegion

open Polynomial

/-! NON-VACUITY of the corollaries' hypotheses: in the cell (4, 2) (hence in (4, 3) and (5, 2),
which contain it) and in the units form at height 10, there are polynomials `Pa`, `Pb` and real
roots `a`, `b` at which all six constraints hold (1 at 15, 2, 3, 4, 5 at 29, G at 209). So no
corollary is vacuously true. -/

theorem aeval_f3 {a : ℝ} (h : a ^ 3 = a + 1) : aeval a (ofList f3L) = 0 := by
  rw [ofList_f3L]; simp; linarith

theorem aeval_f4 {b : ℝ} (h : b ^ 4 = b + 1) : aeval b (ofList f4L) = 0 := by
  rw [ofList_f4L]; simp; linarith

/-- All six constraints at roots of `x³ − x − 1` and `x⁴ − x − 1`. -/
theorem six_at_roots : ∃ a b : ℝ, aeval a (ofList f3L) = 0 ∧ aeval b (ofList f4L) = 0 ∧
    C1 a b 15 ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a 29 ∧ CG a b 209 := by
  obtain ⟨a, _, ha⟩ := exists_cubic_root
  obtain ⟨b, hb, hb4⟩ := exists_quartic_root
  obtain ⟨h1, h2, h3, h4, h5⟩ := converse a b (pass_strong a b ha hb hb4)
  obtain ⟨-, -, -, hG⟩ := gravity_pass a b ha hb hb4
  exact ⟨a, b, aeval_f3 ha, aeval_f4 hb4, h1, h2, h3, h4, h5, hG⟩

/-- NON-VACUITY (cells): the hypotheses of `cell42_five`, `cell42_three_couplings` and
`cell42_gravity` hold together for some `Pa`, `Pb ∈ cell 4 2` and roots `a`, `b`. -/
theorem cell42_corollaries_nonvacuous : ∃ Pa ∈ cell 4 2, ∃ Pb ∈ cell 4 2, ∃ a b : ℝ,
    aeval a Pa = 0 ∧ aeval b Pb = 0 ∧
      C1 a b 15 ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a 29 ∧ CG a b 209 := by
  obtain ⟨a, b, h⟩ := six_at_roots
  exact ⟨_, f3_mem_cell42, _, f4_mem_cell42, a, b, h⟩

/-- NON-VACUITY (units): the same with `Pa ∈ cubicUnits 10`, `Pb ∈ quarticNormNeg 10`. -/
theorem units10_corollaries_nonvacuous : ∃ Pa ∈ cubicUnits 10, ∃ Pb ∈ quarticNormNeg 10,
    ∃ a b : ℝ, aeval a Pa = 0 ∧ aeval b Pb = 0 ∧
      C1 a b 15 ∧ C2 a ∧ C3 a b ∧ C4 a b ∧ C5 a 29 ∧ CG a b 209 := by
  obtain ⟨a, b, h⟩ := six_at_roots
  exact ⟨_, f3_mem_cubicUnits10, _, f4_mem_quarticNormNeg10, a, b, h⟩

#print axioms six_at_roots
#print axioms cell42_corollaries_nonvacuous
#print axioms units10_corollaries_nonvacuous

end ExclusionRegion
