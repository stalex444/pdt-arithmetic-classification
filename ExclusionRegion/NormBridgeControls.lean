module

public import Mathlib
public import ExclusionRegion.NormBridgeJoin
public import ExclusionRegion.NonVacuity

/-!
# The norm bridge: controls, non-vacuity, and the `(ρ, Q)` instance

* NON-VACUITY: `selmer3_irreducible`, `selmer4_irreducible` (from Mathlib's
  `Polynomial.X_pow_sub_X_sub_one_irreducible_rat`); `selmer3_mem_cubicUnits`,
  `selmer4_mem_quarticNormNeg` (height 1).
* THE `(ρ, Q)` INSTANCE (independent re-derivation of F:519's value inside the entry):
  `rhoQ_norm` — for any real `ρ`, `Q` with `ρ³ = ρ + 1`, `Q⁴ = Q + 1`, the field `ℚ⟮ρ, Q⟯ ⊆ ℝ` has
  degree 12 and the norm of `ρQ` over it is `−1`; `rhoQ_norm_nonvacuous`.
* DISJOINTNESS CONTROL (a NON-unit, as the scope gate requires): `control_sqrt2` — in
  `K = ℚ(√2)`, `x = y = √2`: `ℚ(x) ⊔ ℚ(y) = K` holds, `N_{K/ℚ}(x·y) = 4`, and the disjoint
  formula's right side is `16`. `control_sqrt2_not_linearDisjoint`: so `ℚ(x)`, `ℚ(x)` are not
  linearly disjoint (the hypothesis of `norm_mul_of_linearDisjoint` cannot be dropped).
* IRREDUCIBILITY CONTROLS (the join fails for reducible members of F:524's sets):
  `control_reducible_x4_sub_one` — `x⁴ − 1 ∈ quarticNormNeg 1`, `x³ − x − 1 ∈ cubicUnits 1`, real
  roots `a` (of the cubic) and `b = 1`: `[ℚ(a, b) : ℚ] = 3 ≠ 12` and `N(ab) = 1 ≠ −1`.
  `control_reducible_sextic` — `x⁴ − x² + 2x − 1 = (x² − x + 1)(x² + x − 1) ∈ quarticNormNeg 2`,
  complex roots `a` (of `x³ − x − 1`) and `b` (a root of `x² − x + 1`): `N_{ℚ(a,b)/ℚ}(ab) = 1 ≠ −1`.
-/

@[expose] public section

namespace ExclusionRegion.NormBridge

open IntermediateField Polynomial Module

/-! ## Non-vacuity -/

/-- `x³ − x − 1` is irreducible over `ℚ` (Mathlib, Selmer). -/
theorem selmer3_irreducible : Irreducible ((X ^ 3 - X - 1 : ℤ[X]).map (Int.castRingHom ℚ)) := by
  simpa using X_pow_sub_X_sub_one_irreducible_rat (n := 3) (by norm_num)

/-- `x⁴ − x − 1` is irreducible over `ℚ` (Mathlib, Selmer). -/
theorem selmer4_irreducible : Irreducible ((X ^ 4 - X - 1 : ℤ[X]).map (Int.castRingHom ℚ)) := by
  simpa using X_pow_sub_X_sub_one_irreducible_rat (n := 4) (by norm_num)

theorem selmer3_monic : (X ^ 3 - X - 1 : ℤ[X]).Monic := by monicity!

theorem selmer3_natDegree : (X ^ 3 - X - 1 : ℤ[X]).natDegree = 3 := by compute_degree!

theorem selmer4_monic : (X ^ 4 - X - 1 : ℤ[X]).Monic := by monicity!

theorem selmer4_natDegree : (X ^ 4 - X - 1 : ℤ[X]).natDegree = 4 := by compute_degree!

/-- `x³ − x − 1 ∈ cubicUnits 1`. -/
theorem selmer3_mem_cubicUnits : (X ^ 3 - X - 1 : ℤ[X]) ∈ cubicUnits 1 := by
  refine ⟨selmer3_monic, selmer3_natDegree, fun i => ?_, Or.inr (by simp)⟩
  simp only [coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- `x⁴ − x − 1 ∈ quarticNormNeg 1`. -/
theorem selmer4_mem_quarticNormNeg : (X ^ 4 - X - 1 : ℤ[X]) ∈ quarticNormNeg 1 := by
  refine ⟨selmer4_monic, selmer4_natDegree, fun i => ?_, by simp⟩
  simp only [coeff_sub, coeff_X_pow, coeff_X, coeff_one]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-! ## The `(ρ, Q)` instance -/

/-- **The `(ρ, Q)` instance.** For real `ρ`, `Q` with `ρ³ = ρ + 1` and `Q⁴ = Q + 1`:
`[ℚ(ρ, Q) : ℚ] = 12` and the norm of `ρQ` over `ℚ⟮ρ, Q⟯ ⊆ ℝ` is `−1` (F:519's value, re-derived
through the bridge). -/
theorem rhoQ_norm {ρ Q : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hQ : Q ^ 4 = Q + 1) :
    finrank ℚ ℚ⟮ρ, Q⟯ = 12 ∧ ∀ z : ℚ⟮ρ, Q⟯, (z : ℝ) = ρ * Q → Algebra.norm ℚ z = -1 :=
  real_norm_mul_eq_neg_one_of_mem selmer3_mem_cubicUnits selmer4_mem_quarticNormNeg
    selmer3_irreducible selmer4_irreducible
    (by simp only [map_sub, map_pow, aeval_X, map_one]; linarith)
    (by simp only [map_sub, map_pow, aeval_X, map_one]; linarith)

/-- Non-vacuity of `rhoQ_norm`: real `ρ`, `Q` exist, and the element `ρQ` of `ℚ⟮ρ, Q⟯` has
norm `−1`. -/
theorem rhoQ_norm_nonvacuous : ∃ (ρ Q : ℝ) (z : ℚ⟮ρ, Q⟯), 1 < ρ ∧ ρ ^ 3 = ρ + 1 ∧ 1 < Q ∧
    Q ^ 4 = Q + 1 ∧ (z : ℝ) = ρ * Q ∧ finrank ℚ ℚ⟮ρ, Q⟯ = 12 ∧ Algebra.norm ℚ z = -1 := by
  obtain ⟨ρ, hρ1, hρ⟩ := exists_cubic_root
  obtain ⟨Q, hQ1, hQ⟩ := exists_quartic_root
  obtain ⟨z, hz⟩ := exists_mul_mem_adjoin_pair ρ Q
  exact ⟨ρ, Q, z, hρ1, hρ, hQ1, hQ, hz, (rhoQ_norm hρ hQ).1, (rhoQ_norm hρ hQ).2 z hz⟩

/-- Non-vacuity of the abstract join (`norm_mul_eq_neg_one_of_mem`, hypothesis `ℚ⟮a, b⟯ = ⊤`):
inside `E = ℚ⟮ρ, Q⟯` (as a field in its own right) the elements `ρ`, `Q` generate `E`, and the join
gives `[E : ℚ] = 12` and `N_{E/ℚ}(ρQ) = −1`. -/
theorem rhoQ_join_top_nonvacuous {ρ Q : ℝ} (hρ : ρ ^ 3 = ρ + 1) (hQ : Q ^ 4 = Q + 1) :
    ∃ a b : ℚ⟮ρ, Q⟯, (a : ℝ) = ρ ∧ (b : ℝ) = Q ∧ ℚ⟮a, b⟯ = ⊤ ∧
      finrank ℚ ℚ⟮ρ, Q⟯ = 12 ∧ Algebra.norm ℚ (a * b) = -1 := by
  have ha : aeval ρ (X ^ 3 - X - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]; linarith
  have hb : aeval Q (X ^ 4 - X - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]; linarith
  let a : ℚ⟮ρ, Q⟯ := ⟨ρ, mem_adjoin_pair_left ρ Q⟩
  let b : ℚ⟮ρ, Q⟯ := ⟨Q, mem_adjoin_pair_right ρ Q⟩
  have ha' := aeval_sub_eq_zero a ha
  have hb' := aeval_sub_eq_zero b hb
  have hE : finrank ℚ ℚ⟮ρ, Q⟯ = 12 :=
    finrank_adjoin_pair selmer3_monic selmer3_natDegree selmer3_irreducible selmer4_monic
      selmer4_natDegree selmer4_irreducible ha hb
  have hK : finrank ℚ ℚ⟮a, b⟯ = 12 :=
    finrank_adjoin_pair selmer3_monic selmer3_natDegree selmer3_irreducible selmer4_monic
      selmer4_natDegree selmer4_irreducible ha' hb'
  have htop : ℚ⟮a, b⟯ = ⊤ := by
    apply finrank_eq_one_iff_eq_top.mp
    have h := Module.finrank_mul_finrank ℚ ℚ⟮a, b⟯ ℚ⟮ρ, Q⟯
    rw [hK, hE] at h
    omega
  refine ⟨a, b, rfl, rfl, htop, hE, ?_⟩
  exact (norm_mul_eq_neg_one_of_mem selmer3_mem_cubicUnits selmer4_mem_quarticNormNeg
    selmer3_irreducible selmer4_irreducible ha' hb' htop).2

/-! ## Disjointness control (non-unit) -/

/-- `X² − 2` is irreducible over `ℚ`. -/
theorem sq_sub_two_irreducible : Irreducible (X ^ 2 - C 2 : ℚ[X]) := by
  refine X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => ?_
  have h2 : Real.sqrt 2 = ((|b| : ℚ) : ℝ) := by
    rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs]
    congr 1
    exact_mod_cast hb.symm
  exact irrational_sqrt_two.ne_rat |b| h2

theorem minpoly_sqrt_two : minpoly ℚ (Real.sqrt 2) = X ^ 2 - C 2 :=
  (minpoly.eq_of_irreducible_of_monic sq_sub_two_irreducible
    (by rw [map_sub, map_pow, aeval_X, aeval_C]; simp) (by monicity!)).symm

theorem isIntegral_sqrt_two : IsIntegral ℚ (Real.sqrt 2) :=
  ⟨X ^ 2 - C 2, by monicity!, by simp⟩

/-- In `K = ℚ⟮√2⟯`, the generator `x = √2` has minimal polynomial `X² − 2`. -/
theorem minpoly_gen_sqrt_two :
    minpoly ℚ (AdjoinSimple.gen ℚ (Real.sqrt 2)) = X ^ 2 - C 2 := by
  rw [minpoly_gen, minpoly_sqrt_two]

theorem natDegree_sq_sub_two : (X ^ 2 - C 2 : ℚ[X]).natDegree = 2 := by compute_degree!

theorem finrank_sqrt_two : finrank ℚ ℚ⟮Real.sqrt 2⟯ = 2 := by
  rw [adjoin.finrank isIntegral_sqrt_two, minpoly_sqrt_two, natDegree_sq_sub_two]

/-- **Disjointness control (non-unit).** In `K = ℚ(√2)` with `x = y = √2`: the sup hypothesis
`ℚ(x) ⊔ ℚ(y) = K` holds, the true norm is `N_{K/ℚ}(x·y) = 4`, and the right side of the disjoint
formula `N_{ℚ(x)/ℚ}(x)^[ℚ(y):ℚ] · N_{ℚ(y)/ℚ}(y)^[ℚ(x):ℚ]` is `16`. -/
theorem control_sqrt2 :
    ℚ⟮AdjoinSimple.gen ℚ (Real.sqrt 2)⟯ ⊔ ℚ⟮AdjoinSimple.gen ℚ (Real.sqrt 2)⟯ = ⊤ ∧
    Algebra.norm ℚ (AdjoinSimple.gen ℚ (Real.sqrt 2) * AdjoinSimple.gen ℚ (Real.sqrt 2)) = 4 ∧
    Algebra.norm ℚ (AdjoinSimple.gen ℚ (AdjoinSimple.gen ℚ (Real.sqrt 2))) ^
        finrank ℚ ℚ⟮AdjoinSimple.gen ℚ (Real.sqrt 2)⟯ *
      Algebra.norm ℚ (AdjoinSimple.gen ℚ (AdjoinSimple.gen ℚ (Real.sqrt 2))) ^
        finrank ℚ ℚ⟮AdjoinSimple.gen ℚ (Real.sqrt 2)⟯ = 16 := by
  have := adjoin.finiteDimensional isIntegral_sqrt_two
  set x := AdjoinSimple.gen ℚ (Real.sqrt 2) with hxdef
  have hx : IsIntegral ℚ x := IsIntegral.of_finite ℚ x
  have hfx : finrank ℚ ℚ⟮x⟯ = 2 := by
    rw [adjoin.finrank hx, hxdef, minpoly_gen_sqrt_two, natDegree_sq_sub_two]
  have htop : ℚ⟮x⟯ = ⊤ := by
    apply finrank_eq_one_iff_eq_top.mp
    rw [finrank_adjoin_right_eq_div x hx, hxdef, minpoly_gen_sqrt_two, natDegree_sq_sub_two,
      finrank_sqrt_two]
  have hN : Algebra.norm ℚ (AdjoinSimple.gen ℚ x) = -2 := by
    rw [norm_gen_eq_coeff_zero x hx, hxdef, minpoly_gen_sqrt_two, natDegree_sq_sub_two]
    simp
  refine ⟨by rw [sup_idem, htop], ?_, ?_⟩
  · rw [norm_mul_eq_coeff_div x x hx hx, hxdef, minpoly_gen_sqrt_two, natDegree_sq_sub_two,
      finrank_sqrt_two]
    norm_num
  · rw [hN, hfx]
    norm_num

/-- The control is not vacuous against `norm_mul_of_linearDisjoint`: `ℚ(√2)` is not linearly
disjoint from itself, since the theorem would give `4 = 16`. -/
theorem control_sqrt2_not_linearDisjoint :
    ¬ ℚ⟮AdjoinSimple.gen ℚ (Real.sqrt 2)⟯.LinearDisjoint ℚ⟮AdjoinSimple.gen ℚ (Real.sqrt 2)⟯ := by
  intro hd
  obtain ⟨hs, h4, h16⟩ := control_sqrt2
  have := adjoin.finiteDimensional isIntegral_sqrt_two
  have hx : IsIntegral ℚ (AdjoinSimple.gen ℚ (Real.sqrt 2)) := IsIntegral.of_finite ℚ _
  have := norm_mul_of_linearDisjoint _ _ hx hx hd hs
  rw [h4, h16] at this
  norm_num at this

/-! ## Irreducibility controls -/

/-- `x⁴ − 1 ∈ quarticNormNeg 1` (reducible: root `1`). -/
theorem x4_sub_one_mem : (X ^ 4 - 1 : ℤ[X]) ∈ quarticNormNeg 1 := by
  refine ⟨by monicity!, by compute_degree!, fun i => ?_, by simp⟩
  simp only [coeff_sub, coeff_X_pow, coeff_one]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **Irreducibility control 1.** `x³ − x − 1 ∈ cubicUnits 1` and `x⁴ − 1 ∈ quarticNormNeg 1`,
yet for the real root `a` of the cubic and the root `b = 1` of the quartic,
`[ℚ(a, b) : ℚ] = 3` (not 12) and the norm of `ab` over `ℚ⟮a, b⟯` is `1` (not `−1`). -/
theorem control_reducible_x4_sub_one :
    (X ^ 3 - X - 1 : ℤ[X]) ∈ cubicUnits 1 ∧ (X ^ 4 - 1 : ℤ[X]) ∈ quarticNormNeg 1 ∧
    ∃ a b : ℝ, aeval a (X ^ 3 - X - 1 : ℤ[X]) = 0 ∧ aeval b (X ^ 4 - 1 : ℤ[X]) = 0 ∧
      finrank ℚ ℚ⟮a, b⟯ = 3 ∧ ∃ z : ℚ⟮a, b⟯, (z : ℝ) = a * b ∧ Algebra.norm ℚ z = 1 := by
  refine ⟨selmer3_mem_cubicUnits, x4_sub_one_mem, ?_⟩
  obtain ⟨a, -, ha3⟩ := exists_cubic_root
  have ha : aeval a (X ^ 3 - X - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]; linarith
  refine ⟨a, 1, ha, by simp, ?_, ?_⟩
  · rw [adjoin_pair_eq_sup, (adjoin_simple_eq_bot_iff (F := ℚ) (α := (1 : ℝ))).mpr (one_mem _),
      sup_bot_eq,
      finrank_adjoin_root selmer3_monic selmer3_irreducible ha, selmer3_natDegree]
  · let a' : ℚ⟮a, (1 : ℝ)⟯ := ⟨a, mem_adjoin_pair_left a 1⟩
    refine ⟨a', (mul_one a).symm, ?_⟩
    have ha' := aeval_sub_eq_zero a' ha
    rw [norm_eq_coeff_zero_pow a' (isIntegral_of_root selmer3_monic ha'),
      minpoly_eq_map selmer3_monic selmer3_irreducible ha', selmer3_monic.natDegree_map,
      selmer3_natDegree, coeff_map]
    simp
    norm_num

/-- The quartic `x⁴ − x² + 2x − 1 = (x² − x + 1)(x² + x − 1)`. -/
theorem sextic_factor :
    (X ^ 4 - X ^ 2 + C 2 * X - 1 : ℤ[X]) = (X ^ 2 - X + 1) * (X ^ 2 + X - 1) := by
  rw [show (C 2 : ℤ[X]) = 2 from rfl]
  ring

/-- `x⁴ − x² + 2x − 1 ∈ quarticNormNeg 2`. -/
theorem sextic_quartic_mem : (X ^ 4 - X ^ 2 + C 2 * X - 1 : ℤ[X]) ∈ quarticNormNeg 2 := by
  refine ⟨by monicity!, by compute_degree!, fun i => ?_, by simp⟩
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_one]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem quad_monic : (X ^ 2 - X + 1 : ℤ[X]).Monic := by monicity!

theorem quad_natDegree : (X ^ 2 - X + 1 : ℤ[X]).natDegree = 2 := by compute_degree!

/-- `x² − x + 1` is irreducible over `ℚ` (degree 2, no rational root). -/
theorem quad_irreducible : Irreducible ((X ^ 2 - X + 1 : ℤ[X]).map (Int.castRingHom ℚ)) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [quad_monic.natDegree_map, quad_natDegree]
    decide
  · intro x hx
    simp at hx
    nlinarith [sq_nonneg (x - 1 / 2)]

/-- **Irreducibility control 2.** `x³ − x − 1 ∈ cubicUnits 1` and
`x⁴ − x² + 2x − 1 = (x² − x + 1)(x² + x − 1) ∈ quarticNormNeg 2`, yet for a complex root `a` of the
cubic and a root `b` of the factor `x² − x + 1` (a primitive sixth root of unity), the norm of
`ab` over `ℚ⟮a, b⟯ ⊆ ℂ` is `1` (not `−1`). -/
theorem control_reducible_sextic :
    (X ^ 3 - X - 1 : ℤ[X]) ∈ cubicUnits 1 ∧
    (X ^ 4 - X ^ 2 + C 2 * X - 1 : ℤ[X]) ∈ quarticNormNeg 2 ∧
    ∃ a b : ℂ, aeval a (X ^ 3 - X - 1 : ℤ[X]) = 0 ∧
      aeval b (X ^ 4 - X ^ 2 + C 2 * X - 1 : ℤ[X]) = 0 ∧ aeval b (X ^ 2 - X + 1 : ℤ[X]) = 0 ∧
      ∃ z : ℚ⟮a, b⟯, (z : ℂ) = a * b ∧ Algebra.norm ℚ z = 1 := by
  refine ⟨selmer3_mem_cubicUnits, sextic_quartic_mem, ?_⟩
  have h3 : (X ^ 3 - X - 1 : ℂ[X]).natDegree = 3 := by compute_degree!
  have h2 : (X ^ 2 - X + 1 : ℂ[X]).natDegree = 2 := by compute_degree!
  obtain ⟨a, ha⟩ := Complex.exists_root (f := (X ^ 3 - X - 1 : ℂ[X]))
    (natDegree_pos_iff_degree_pos.mp (by rw [h3]; norm_num))
  obtain ⟨b, hb⟩ := Complex.exists_root (f := (X ^ 2 - X + 1 : ℂ[X]))
    (natDegree_pos_iff_degree_pos.mp (by rw [h2]; norm_num))
  simp only [IsRoot, eval_sub, eval_add, eval_pow, eval_X, eval_one] at ha hb
  have ha' : aeval a (X ^ 3 - X - 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_one]; exact ha
  have hb2 : aeval b (X ^ 2 - X + 1 : ℤ[X]) = 0 := by
    simp only [map_sub, map_add, map_pow, aeval_X, map_one]; exact hb
  have hb4 : aeval b (X ^ 4 - X ^ 2 + C 2 * X - 1 : ℤ[X]) = 0 := by
    rw [sextic_factor, map_mul, hb2, zero_mul]
  refine ⟨a, b, ha', hb4, hb2, ?_⟩
  obtain ⟨z, hz⟩ := exists_mul_mem_adjoin_pair a b
  refine ⟨z, hz, ?_⟩
  let a' : ℚ⟮a, b⟯ := ⟨a, mem_adjoin_pair_left a b⟩
  let b' : ℚ⟮a, b⟯ := ⟨b, mem_adjoin_pair_right a b⟩
  have hz' : z = a' * b' := Subtype.ext hz
  have ha'' := aeval_sub_eq_zero a' ha'
  have hb'' := aeval_sub_eq_zero b' hb2
  rw [hz', norm_mul_eq_coeff a' b' (isIntegral_of_root selmer3_monic ha'')
      (isIntegral_of_root quad_monic hb''),
    minpoly_eq_map selmer3_monic selmer3_irreducible ha'',
    minpoly_eq_map quad_monic quad_irreducible hb'', selmer3_monic.natDegree_map,
    selmer3_natDegree, quad_monic.natDegree_map, quad_natDegree, coeff_map, coeff_map]
  norm_num

end ExclusionRegion.NormBridge
