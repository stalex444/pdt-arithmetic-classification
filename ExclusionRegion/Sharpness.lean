module

public import Mathlib
public import ExclusionRegion.Gauge
public import ExclusionRegion.Controls
public import ExclusionRegion.Pass
public import ExclusionRegion.NestedCheck
public import ExclusionRegion.WindowControls
public import ExclusionRegion.UnitsControls
public import ExclusionRegion.NormBridgeControls

@[expose] public section
/-!
# Sharpness: the conclusions of compared statements 3 and 4 fail one step beyond their sets

Not compared; cited by the scope account of `Challenge.lean`. Each `_conclusion_fails`,
`unit_pairs_height11` and `unit_pairs_norm_pos` theorem exhibits real numbers `a`, `b` that are
roots of polynomials of a set one step beyond a set proved in this repository (a compared set, or
`C(10, 1)`, proved here but not compared) and satisfy the three windows `C1 a b 15`, `C3 a b`,
`C4 a b`, while `b⁴ ≠ b + 1`. Each `_statement_false` theorem then shows that the compared
statement's hypotheses, over the larger set, do not imply even the first part of its conclusion
(`a³ = a + 1 ∧ b⁴ = b + 1 ∧ 1 < b`), so its full conclusion fails there too. In every case `a`
is the real root above 1 of `x³ − x − 1`, and `b` is a real root, located in an explicit rational
interval inside the `b`-window, of the polynomial named in the docstring. So the CONCLUSION of the
compared statement (not only the window theorem behind its proof) fails for the larger set:

* `cell53_conclusion_fails`, `cell53_statement_false`: the cell `C(5, 3)` (one step beyond
  `C(4, 3)` in degree);
* `cell72_conclusion_fails`, `cell72_statement_false`: the cell `C(7, 2)` (one step beyond
  `C(6, 2)` in degree);
* `cell63_statement_false`: the cell `C(6, 3)` (one step beyond `C(6, 2)` in height), since
  `C(5, 3) ⊆ C(6, 3)`;
* `cell102_statement_false`: the cell `C(10, 2)` (one step beyond `C(10, 1)`, which is proved here
  but not compared, in height), since `C(7, 2) ⊆ C(10, 2)`;
* `unit_pairs_height11`, `unit_pairs_statement_false_height11`: compared statement 4 with the
  height bound 10 replaced by 11 and every other hypothesis kept, irreducibility over `ℚ` of both
  polynomials and `N(ab) = −1` included (both proved here, not assumed). The height bound 10 is
  therefore sharp;
* `unit_pairs_norm_pos`, `unit_pairs_statement_false_without_norm`: at height 10, with both
  polynomials irreducible over `ℚ`, the element `ab` has norm `+1`, and the windows hold. So
  compared statement 4 is false without its norm hypothesis: that hypothesis carries weight.

These theorems bound the compared sets; they are statements about polynomials and windows only.
The helper theorems (`pass_of_bracket`, `irreducible_of_no_root_no_quadratic`, and the two
irreducibility theorems) are proved here for this module's use.
-/

namespace ExclusionRegion.Sharpness

open Polynomial IntermediateField

/-- `C1` (at 15), `C3`, `C4` at `(a, b)`, for `a` the real root above 1 of `x³ = x + 1` and `b`
in a rational interval `[bl, bu]` inside `[1.2191706, 1.2220763]`, from four numerical
inequalities on the interval ends. -/
theorem pass_of_bracket {a b bl bu : ℝ} (ha : 1 < a) (ha3 : a ^ 3 = a + 1)
    (hbl : bl ≤ b) (hbu : b ≤ bu) (hbl1 : 1.2191706 ≤ bl) (hbu1 : bu ≤ 1.2220763)
    (hC1l : 136.35082 * (3.141593 : ℝ) ^ 2 ≤ (1.32471 * bl) ^ 15)
    (hC1u : (1.32472 * bu) ^ 15 ≤ 137.72118 * (3.141592 : ℝ) ^ 2)
    (hC4l : 0.11564 ≤ (bl - 1) ^ 3 * (1.32472 : ℝ) ^ 5 / (4 * (1.32472 - 1) ^ 3 * bl ^ 5))
    (hC4u : (bu - 1) ^ 3 * (1.32471 : ℝ) ^ 5 / (4 * (1.32471 - 1) ^ 3 * bu ^ 5) ≤ 0.12036) :
    C1 a b 15 ∧ C3 a b ∧ C4 a b := by
  obtain ⟨hal, hau⟩ := rho_bracket ha ha3
  refine ⟨C1_of_rat ?_ ?_, C3_of_box (by linarith) (by linarith) (by linarith) (by linarith), ?_⟩
  · exact hC1l.trans (pow_le_pow_left₀ (mul_nonneg (by norm_num) (by linarith))
      (mul_le_mul hal.le hbl (by linarith) (by linarith)) 15)
  · exact (pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith))
      (mul_le_mul hau.le hbu (by linarith) (by linarith)) 15).trans hC1u
  · rw [C4_iff]
    exact ⟨hC4l.trans (C4val_ge (by linarith) hbl (by linarith) ha hau.le (by norm_num)),
      (C4val_le (by norm_num) hal.le (by linarith) (by linarith) hbu (by linarith)).trans hC4u⟩

/-- A real root of `x³ = x + 1` is a root of the coefficient-list polynomial `x³ − x − 1`. -/
theorem f3_aeval {a : ℝ} (ha3 : a ^ 3 = a + 1) : aeval a (ofList f3L) = 0 := by
  rw [ofList_f3L]; simp; linarith

/-! ## Compared statement 3, one step beyond each cell -/

/-- **Cell (5, 3).** The polynomials `x³ − x − 1` and `x⁵ + 3x⁴ − 3x³ − 3x² − 2x + 3` lie in
`C(5, 3)`; with `a` the real root above 1 of the first and `b ∈ [1.22039, 1.22040]` a real root of
the second, `C1 a b 15`, `C3 a b`, `C4 a b` hold and `b⁴ ≠ b + 1`. -/
theorem cell53_conclusion_fails : ∃ Pa ∈ cell 5 3, ∃ Pb ∈ cell 5 3, ∃ a b : ℝ,
    aeval a Pa = 0 ∧ aeval b Pb = 0 ∧ C1 a b 15 ∧ C3 a b ∧ C4 a b ∧ b ^ 4 ≠ b + 1 := by
  obtain ⟨a, ha, ha3⟩ := exists_cubic_root
  obtain ⟨b, hl, hu, h0⟩ := root_of_sign_change P53S (l := 1.22039) (u := 1.22040) (by norm_num)
    (Or.inl ⟨by simp only [P53S, evR]; norm_num, by simp only [P53S, evR]; norm_num⟩)
  obtain ⟨h1, h3, h4⟩ := pass_of_bracket ha ha3 hl hu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, cell_mono (by norm_num) (by norm_num) f3_mem_cell42, _, P53S_mem, a, b,
    f3_aeval ha3, by rw [aeval_ofList]; exact h0, h1, h3, h4,
    not_quartic_root_below (by linarith) (by linarith)⟩

/-- **Cell (7, 2).** The polynomials `x³ − x − 1` and `x⁷ + x⁶ − 2x⁵ − x² − 2x + 2` lie in
`C(7, 2)`; with `a` the real root above 1 of the first and `b ∈ [1.22107, 1.22109]` a real root of
the second, `C1 a b 15`, `C3 a b`, `C4 a b` hold and `b⁴ ≠ b + 1`. -/
theorem cell72_conclusion_fails : ∃ Pa ∈ cell 7 2, ∃ Pb ∈ cell 7 2, ∃ a b : ℝ,
    aeval a Pa = 0 ∧ aeval b Pb = 0 ∧ C1 a b 15 ∧ C3 a b ∧ C4 a b ∧ b ^ 4 ≠ b + 1 := by
  obtain ⟨a, ha, ha3⟩ := exists_cubic_root
  obtain ⟨b, hl, hu, h0⟩ := root_of_sign_change P72S (l := 1.22107) (u := 1.22109) (by norm_num)
    (Or.inl ⟨by simp only [P72S, evR]; norm_num, by simp only [P72S, evR]; norm_num⟩)
  obtain ⟨h1, h3, h4⟩ := pass_of_bracket ha ha3 hl hu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨_, cell_mono (by norm_num) (by norm_num) f3_mem_cell42, _, P72S_mem, a, b,
    f3_aeval ha3, by rw [aeval_ofList]; exact h0, h1, h3, h4,
    not_quartic_root_above (by linarith)⟩

/-- **Compared statement 3 is false for the cell (5, 3).** Its hypotheses over `C(5, 3)` do not
imply even the first part of its conclusion, `a³ = a + 1 ∧ b⁴ = b + 1 ∧ 1 < b`, so its full
conclusion fails there too (witness: `cell53_conclusion_fails`). -/
theorem cell53_statement_false : ¬ ∀ Pa ∈ cell 5 3, ∀ Pb ∈ cell 5 3, ∀ a b : ℝ,
    aeval a Pa = 0 → aeval b Pb = 0 → ∀ p : ℕ, C1 a b p → C3 a b → C4 a b →
      a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b := by
  intro h
  obtain ⟨Pa, hPa, Pb, hPb, a, b, ha, hb, h1, h3, h4, hne⟩ := cell53_conclusion_fails
  exact hne (h Pa hPa Pb hPb a b ha hb 15 h1 h3 h4).2.1

/-- **Compared statement 3 is false for the cell (7, 2)**: its hypotheses do not imply even the
first part of its conclusion, so the full conclusion fails (witness: `cell72_conclusion_fails`). -/
theorem cell72_statement_false : ¬ ∀ Pa ∈ cell 7 2, ∀ Pb ∈ cell 7 2, ∀ a b : ℝ,
    aeval a Pa = 0 → aeval b Pb = 0 → ∀ p : ℕ, C1 a b p → C3 a b → C4 a b →
      a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b := by
  intro h
  obtain ⟨Pa, hPa, Pb, hPb, a, b, ha, hb, h1, h3, h4, hne⟩ := cell72_conclusion_fails
  exact hne (h Pa hPa Pb hPb a b ha hb 15 h1 h3 h4).2.1

/-- **Compared statement 3 is false for the cell (6, 3)**, one step beyond `C(6, 2)` in height:
`C(5, 3) ⊆ C(6, 3)` (`cell_mono`), so the witness of `cell53_conclusion_fails` serves; as above,
not even the first part of the conclusion follows. -/
theorem cell63_statement_false : ¬ ∀ Pa ∈ cell 6 3, ∀ Pb ∈ cell 6 3, ∀ a b : ℝ,
    aeval a Pa = 0 → aeval b Pb = 0 → ∀ p : ℕ, C1 a b p → C3 a b → C4 a b →
      a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b := by
  intro h
  obtain ⟨Pa, hPa, Pb, hPb, a, b, ha, hb, h1, h3, h4, hne⟩ := cell53_conclusion_fails
  exact hne (h Pa (cell_mono (by norm_num) (by norm_num) hPa) Pb
    (cell_mono (by norm_num) (by norm_num) hPb) a b ha hb 15 h1 h3 h4).2.1

/-- **Compared statement 3 is false for the cell (10, 2)**, one step in height beyond `C(10, 1)`
(proved in this repository, not compared): `C(7, 2) ⊆ C(10, 2)` (`cell_mono`), so the witness of
`cell72_conclusion_fails` serves; not even the first part of the conclusion follows. -/
theorem cell102_statement_false : ¬ ∀ Pa ∈ cell 10 2, ∀ Pb ∈ cell 10 2, ∀ a b : ℝ,
    aeval a Pa = 0 → aeval b Pb = 0 → ∀ p : ℕ, C1 a b p → C3 a b → C4 a b →
      a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b := by
  intro h
  obtain ⟨Pa, hPa, Pb, hPb, a, b, ha, hb, h1, h3, h4, hne⟩ := cell72_conclusion_fails
  exact hne (h Pa (cell_mono (by norm_num) le_rfl hPa) Pb (cell_mono (by norm_num) le_rfl hPb)
    a b ha hb 15 h1 h3 h4).2.1

/-! ## Irreducibility over `ℚ` of the two control quartics -/

theorem monic_deg2_eq {q : ℤ[X]} (hq : q.Monic) (hd : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  conv_lhs => rw [hq.as_sum, hd]
  simp [Finset.sum_range_succ]
  ring

theorem quad_expand (u v s t : ℤ) :
    (X ^ 2 + C u * X + C v) * (X ^ 2 + C s * X + C t) =
      X ^ 4 + C (u + s) * X ^ 3 + C (v + u * s + t) * X ^ 2 + C (u * t + v * s) * X +
        C (v * t) := by
  simp only [C_add, C_mul]; ring

/-- A monic integer quartic with no integer root and no factorisation into two monic integer
quadratics is irreducible over `ℚ`. -/
theorem irreducible_of_no_root_no_quadratic {p : ℤ[X]} (hm : p.Monic) (hd : p.natDegree = 4)
    (hlin : ∀ c : ℤ, p.eval c ≠ 0)
    (hquad : ∀ u v s t : ℤ, p ≠ (X ^ 2 + C u * X + C v) * (X ^ 2 + C s * X + C t)) :
    Irreducible (p.map (Int.castRingHom ℚ)) := by
  rw [← IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive,
    hm.irreducible_iff_natDegree']
  refine ⟨fun h1 => by rw [h1, natDegree_one] at hd; omega, ?_⟩
  intro f g hf hg hfg hdeg
  rw [hd, Finset.mem_Ioc] at hdeg
  have hsum : f.natDegree + g.natDegree = 4 := by rw [← hf.natDegree_mul hg, hfg, hd]
  rcases (by omega : g.natDegree = 1 ∨ g.natDegree = 2) with hg1 | hg2
  · apply hlin (-g.coeff 0)
    rw [← hfg, eval_mul, hg.eq_X_add_C hg1]
    simp
  · have hf2 : f.natDegree = 2 := by omega
    apply hquad (f.coeff 1) (f.coeff 0) (g.coeff 1) (g.coeff 0)
    rw [← monic_deg2_eq hf hf2, ← monic_deg2_eq hg hg2, hfg]

/-- `x⁴ + 7x³ − 11x² + 2x − 1` (the height-11 control) is irreducible over `ℚ`. -/
theorem U11_irreducible :
    Irreducible ((X ^ 4 + 7 * X ^ 3 - 11 * X ^ 2 + 2 * X - 1 : ℤ[X]).map (Int.castRingHom ℚ)) := by
  refine irreducible_of_no_root_no_quadratic (by monicity!) (by compute_degree!) ?_ ?_
  · intro c h
    simp only [eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_one, eval_ofNat] at h
    have hc : c * (c ^ 3 + 7 * c ^ 2 - 11 * c + 2) = 1 := by linear_combination h
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hc with rfl | rfl <;> norm_num at h
  · intro u v s t h
    rw [quad_expand] at h
    have e : (X ^ 4 + C 7 * X ^ 3 + C (-11) * X ^ 2 + C 2 * X + C (-1) : ℤ[X]) =
        X ^ 4 + C (u + s) * X ^ 3 + C (v + u * s + t) * X ^ 2 + C (u * t + v * s) * X +
          C (v * t) := by
      rw [← h]; simp only [map_neg, map_ofNat, map_one]; ring
    have e0 := congrArg (coeff · 0) e
    have e1 := congrArg (coeff · 1) e
    have e3 := congrArg (coeff · 3) e
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at e0 e1 e3
    norm_num at e0 e1 e3
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one' e0.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-- `x⁴ + 10x³ − 7x² − 9x + 1` (the norm `+1` control) is irreducible over `ℚ`. -/
theorem U10p_irreducible :
    Irreducible ((X ^ 4 + 10 * X ^ 3 - 7 * X ^ 2 - 9 * X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) := by
  refine irreducible_of_no_root_no_quadratic (by monicity!) (by compute_degree!) ?_ ?_
  · intro c h
    simp only [eval_sub, eval_add, eval_pow, eval_mul, eval_X, eval_one, eval_ofNat] at h
    have hc : c * (-(c ^ 3) - 10 * c ^ 2 + 7 * c + 9) = 1 := by linear_combination -h
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hc with rfl | rfl <;> norm_num at h
  · intro u v s t h
    rw [quad_expand] at h
    have e : (X ^ 4 + C 10 * X ^ 3 + C (-7) * X ^ 2 + C (-9) * X + C 1 : ℤ[X]) =
        X ^ 4 + C (u + s) * X ^ 3 + C (v + u * s + t) * X ^ 2 + C (u * t + v * s) * X +
          C (v * t) := by
      rw [← h]; simp only [map_neg, map_ofNat, map_one]; ring
    have e0 := congrArg (coeff · 0) e
    have e1 := congrArg (coeff · 1) e
    have e3 := congrArg (coeff · 3) e
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C] at e0 e1 e3
    norm_num at e0 e1 e3
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' e0.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-! ## Compared statement 4: the height bound and the norm hypothesis -/

/-- `x³ − x − 1` is a monic integer cubic with constant term `±1` of every height `H ≥ 1`. -/
theorem selmer3_mem_cubicUnits_height (H : ℕ) (hH : 1 ≤ H) : (X ^ 3 - X - 1 : ℤ[X]) ∈ cubicUnits H := by
  obtain ⟨h1, h2, h3, h4⟩ := NormBridge.selmer3_mem_cubicUnits
  exact ⟨h1, h2, fun i => (h3 i).trans (by exact_mod_cast hH), h4⟩

/-- **Height 11: every hypothesis of compared statement 4 except the height bound, which is 11.**
`P = x³ − x − 1` and `P' = x⁴ + 7x³ − 11x² + 2x − 1` are monic, of degrees 3 and 4, of height at
most 11, and irreducible over `ℚ`; `a` is the real root above 1 of `P`, `b ∈ [1.22044, 1.22045]` a
real root of `P'`, `z` is `ab` in `ℚ⟮a, b⟯` and `N(z) = −1` (proved by the norm bridge). Then
`C1 a b 15`, `C3 a b`, `C4 a b` hold and `b⁴ ≠ b + 1`. -/
theorem unit_pairs_height11 : ∃ (P P' : ℤ[X]) (a b : ℝ) (z : ℚ⟮a, b⟯),
    P.Monic ∧ P.natDegree = 3 ∧ (∀ i, |P.coeff i| ≤ 11) ∧
      Irreducible (P.map (Int.castRingHom ℚ)) ∧
    P'.Monic ∧ P'.natDegree = 4 ∧ (∀ i, |P'.coeff i| ≤ 11) ∧
      Irreducible (P'.map (Int.castRingHom ℚ)) ∧
    aeval a P = 0 ∧ aeval b P' = 0 ∧ (z : ℝ) = a * b ∧ Algebra.norm ℚ z = -1 ∧
    C1 a b 15 ∧ C3 a b ∧ C4 a b ∧ b ^ 4 ≠ b + 1 := by
  obtain ⟨a, ha, ha3⟩ := exists_cubic_root
  obtain ⟨b, hl, hu, h0⟩ := root_of_sign_change U11 (l := 1.22044) (u := 1.22045) (by norm_num)
    (Or.inl ⟨by simp only [U11, evR]; norm_num, by simp only [U11, evR]; norm_num⟩)
  obtain ⟨h1, h3, h4⟩ := pass_of_bracket ha ha3 hl hu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨z, hz⟩ := NormBridge.exists_mul_mem_adjoin_pair a b
  have hP := selmer3_mem_cubicUnits_height 11 (by norm_num)
  have hP' := control_units_height_S.1
  have hirr' : Irreducible ((ofList U11).map (Int.castRingHom ℚ)) := by
    rw [ofList_U11]; exact U11_irreducible
  have hb : aeval b (ofList U11) = 0 := by rw [aeval_ofList]; exact h0
  have ha' : aeval a (X ^ 3 - X - 1 : ℤ[X]) = 0 := by simp; linarith
  refine ⟨X ^ 3 - X - 1, ofList U11, a, b, z, hP.1, hP.2.1, hP.2.2.1,
    NormBridge.selmer3_irreducible, hP'.1, hP'.2.1, hP'.2.2.1, hirr', ha', hb, hz,
    (NormBridge.real_norm_mul_eq_neg_one_of_mem hP hP' NormBridge.selmer3_irreducible hirr'
      ha' hb).2 z hz, h1, h3, h4, not_quartic_root_below (by linarith) (by linarith)⟩

/-- **Compared statement 4 is false at height 11** (all its other hypotheses kept), so its height
bound 10 is sharp (witness: `unit_pairs_height11`). -/
theorem unit_pairs_statement_false_height11 : ¬ ∀ (P P' : ℤ[X]), P.Monic → P.natDegree = 3 →
    (∀ i, |P.coeff i| ≤ 11) → Irreducible (P.map (Int.castRingHom ℚ)) →
    P'.Monic → P'.natDegree = 4 → (∀ i, |P'.coeff i| ≤ 11) →
    Irreducible (P'.map (Int.castRingHom ℚ)) → ∀ a b : ℝ, aeval a P = 0 → aeval b P' = 0 →
    ∀ z : ℚ⟮a, b⟯, (z : ℝ) = a * b → Algebra.norm ℚ z = -1 → ∀ p : ℕ,
    C1 a b p → C3 a b → C4 a b → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b := by
  intro h
  obtain ⟨P, P', a, b, z, hm, hd, hH, hirr, hm', hd', hH', hirr', ha, hb, hz, hN, h1, h3, h4,
    hne⟩ := unit_pairs_height11
  exact hne (h P P' hm hd hH hirr hm' hd' hH' hirr' a b ha hb z hz hN 15 h1 h3 h4).2.1

/-- **Height 10 with norm `+1`.** `P = x³ − x − 1` and `P' = x⁴ + 10x³ − 7x² − 9x + 1` are monic,
of degrees 3 and 4, of height at most 10, and irreducible over `ℚ`; `a` is the real root above 1
of `P`, `b ∈ [1.22096, 1.22097]` a real root of `P'`, `z` is `ab` in `ℚ⟮a, b⟯`, and `N(z) = +1`
(proved by the norm bridge). Then `C1 a b 15`, `C3 a b`, `C4 a b` hold and `b⁴ ≠ b + 1`. -/
theorem unit_pairs_norm_pos : ∃ (P P' : ℤ[X]) (a b : ℝ) (z : ℚ⟮a, b⟯),
    P.Monic ∧ P.natDegree = 3 ∧ (∀ i, |P.coeff i| ≤ 10) ∧
      Irreducible (P.map (Int.castRingHom ℚ)) ∧
    P'.Monic ∧ P'.natDegree = 4 ∧ (∀ i, |P'.coeff i| ≤ 10) ∧
      Irreducible (P'.map (Int.castRingHom ℚ)) ∧
    aeval a P = 0 ∧ aeval b P' = 0 ∧ (z : ℝ) = a * b ∧ Algebra.norm ℚ z = 1 ∧
    C1 a b 15 ∧ C3 a b ∧ C4 a b ∧ b ^ 4 ≠ b + 1 := by
  obtain ⟨a, ha, ha3⟩ := exists_cubic_root
  obtain ⟨b, hl, hu, h0⟩ := root_of_sign_change U10p (l := 1.22096) (u := 1.22097) (by norm_num)
    (Or.inl ⟨by simp only [U10p, evR]; norm_num, by simp only [U10p, evR]; norm_num⟩)
  obtain ⟨h1, h3, h4⟩ := pass_of_bracket ha ha3 hl hu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨z, hz⟩ := NormBridge.exists_mul_mem_adjoin_pair a b
  have hP := selmer3_mem_cubicUnits_height 10 (by norm_num)
  obtain ⟨⟨hm', hd', hH', hc0'⟩, -⟩ := control_units_norm_S
  have hirr' : Irreducible ((ofList U10p).map (Int.castRingHom ℚ)) := by
    rw [ofList_U10p]; exact U10p_irreducible
  have hb : aeval b (ofList U10p) = 0 := by rw [aeval_ofList]; exact h0
  have ha' : aeval a (X ^ 3 - X - 1 : ℤ[X]) = 0 := by simp; linarith
  have hN := (NormBridge.real_norm_mul_eq_coeff_pow hP.1 hP.2.1 NormBridge.selmer3_irreducible
    hm' hd' hirr' ha' hb).2 z hz
  have hc0 : (X ^ 3 - X - 1 : ℤ[X]).coeff 0 = -1 := by simp
  rw [hc0, hc0'] at hN
  refine ⟨X ^ 3 - X - 1, ofList U10p, a, b, z, hP.1, hP.2.1, hP.2.2.1,
    NormBridge.selmer3_irreducible, hm', hd', hH', hirr', ha', hb, hz, by rw [hN]; norm_num,
    h1, h3, h4, not_quartic_root_above (by linarith)⟩

/-- **Compared statement 4 is false without its norm hypothesis** (height 10, irreducibility and
every other hypothesis kept; witness: `unit_pairs_norm_pos`). -/
theorem unit_pairs_statement_false_without_norm : ¬ ∀ (P P' : ℤ[X]), P.Monic → P.natDegree = 3 →
    (∀ i, |P.coeff i| ≤ 10) → Irreducible (P.map (Int.castRingHom ℚ)) →
    P'.Monic → P'.natDegree = 4 → (∀ i, |P'.coeff i| ≤ 10) →
    Irreducible (P'.map (Int.castRingHom ℚ)) → ∀ a b : ℝ, aeval a P = 0 → aeval b P' = 0 →
    ∀ p : ℕ, C1 a b p → C3 a b → C4 a b → a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b := by
  intro h
  obtain ⟨P, P', a, b, -, hm, hd, hH, hirr, hm', hd', hH', hirr', ha, hb, -, -, h1, h3, h4,
    hne⟩ := unit_pairs_norm_pos
  exact hne (h P P' hm hd hH hirr hm' hd' hH' hirr' a b ha hb 15 h1 h3 h4).2.1

end ExclusionRegion.Sharpness
