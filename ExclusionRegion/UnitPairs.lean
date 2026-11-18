module

public import Mathlib
public import ExclusionRegion.Defs
public import ExclusionRegion.Corollaries
public import ExclusionRegion.NormBridgeJoin
public import ExclusionRegion.NormBridgeControls
public import ExclusionRegion.Gravity

/-!
# Unit pairs at height 10: the three gauge-coupling windows pick out the roots

`P` a monic integer cubic and `P'` a monic integer quartic, each irreducible over `ℚ` (in the
form `Irreducible (P.map (Int.castRingHom ℚ))`), every coefficient of absolute value at most 10;
`a`, `b` real roots of `P`, `P'`; `z` the element `ab` of the field `ℚ⟮a, b⟯ ⊆ ℝ`, with
`N_{ℚ(a,b)/ℚ}(z) = −1`. If constraints 1, 3, 4 (`C1 a b p`, `C3 a b`, `C4 a b`) hold, then
`a³ = a + 1`, `b⁴ = b + 1`, `1 < b`, and `a`, `b` are the real roots above 1 of `x³ = x + 1` and
`x⁴ = x + 1`.

Route (one composition step): `real_mem_units_iff_norm_mul_eq_neg_one` (the norm bridge,
NormBridgeJoin.lean) turns the norm condition into `P ∈ cubicUnits 10 ∧ P' ∈ quarticNormNeg 10`;
`units10_three_couplings` and `units10_three_couplings_eq` (Corollaries.lean) conclude.

* `unit_pairs_three_couplings` : the statement.
* `unit_pairs_nonvacuous` : its hypotheses (with `p = 15`) hold at `P = x³ − x − 1`,
  `P' = x⁴ − x − 1`, `a`, `b` their real roots above 1.

The scope is the stated set only (degrees 3 and 4, height at most 10, irreducible, norm `−1`).
The window-level controls one step beyond it are in UnitsControls.lean:
`control_units_height_S` (a norm `−1` quartic of height 11 with a root in the `b`-window other
than the root of `x⁴ = x + 1`), `control_units_height_a` (the same for a unit cubic of height
20 and the `a`-window), `control_units_norm_S` (a height-10 quartic with constant term `+1` and
a root in the `b`-window).
-/

@[expose] public section

namespace ExclusionRegion

open Polynomial IntermediateField

/-- **UNIT PAIRS, height 10.** For a monic integer cubic `P` and a monic integer quartic `P'`,
each irreducible over `ℚ`, every coefficient of absolute value at most 10, with real roots `a`,
`b` such that the element `z = ab` of `ℚ⟮a, b⟯` has norm `−1` over `ℚ`: constraints 1, 3, 4 (the
three gauge-coupling windows) give `a³ = a + 1`, `b⁴ = b + 1`, `1 < b`, and `a`, `b` are THE
real roots above 1 of `x³ = x + 1` and `x⁴ = x + 1`. -/
theorem unit_pairs_three_couplings {P P' : ℤ[X]}
    (hm : P.Monic) (hd : P.natDegree = 3) (hH : ∀ i, |P.coeff i| ≤ 10)
    (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hm' : P'.Monic) (hd' : P'.natDegree = 4) (hH' : ∀ i, |P'.coeff i| ≤ 10)
    (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : ℝ} (ha : aeval a P = 0) (hb : aeval b P' = 0)
    (z : ℚ⟮a, b⟯) (hz : (z : ℝ) = a * b) (hN : Algebra.norm ℚ z = -1) (p : ℕ) :
    C1 a b p → C3 a b → C4 a b →
      (a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b) ∧
        ∀ r s : ℝ, 1 < r → r ^ 3 = r + 1 → 1 < s → s ^ 4 = s + 1 → a = r ∧ b = s := by
  intro h1 h3 h4
  have hH10 : ∀ i, |P.coeff i| ≤ ((10 : ℕ) : ℤ) := fun i => by exact_mod_cast hH i
  have hH10' : ∀ i, |P'.coeff i| ≤ ((10 : ℕ) : ℤ) := fun i => by exact_mod_cast hH' i
  obtain ⟨hP, hP'⟩ := (NormBridge.real_mem_units_iff_norm_mul_eq_neg_one hm hd hH10 hirr hm' hd'
    hH10' hirr' ha hb z hz).mpr hN
  exact ⟨units10_three_couplings P P' hP hP' a b ha hb p h1 h3 h4,
    units10_three_couplings_eq P P' hP hP' a b ha hb p h1 h3 h4⟩

/-- NON-VACUITY: the hypotheses of `unit_pairs_three_couplings` (with `p = 15`) hold together at
`P = x³ − x − 1`, `P' = x⁴ − x − 1` and their real roots `a`, `b` above 1. -/
theorem unit_pairs_nonvacuous : ∃ (P P' : ℤ[X]) (a b : ℝ) (z : ℚ⟮a, b⟯),
    P.Monic ∧ P.natDegree = 3 ∧ (∀ i, |P.coeff i| ≤ 10) ∧
      Irreducible (P.map (Int.castRingHom ℚ)) ∧
    P'.Monic ∧ P'.natDegree = 4 ∧ (∀ i, |P'.coeff i| ≤ 10) ∧
      Irreducible (P'.map (Int.castRingHom ℚ)) ∧
    aeval a P = 0 ∧ aeval b P' = 0 ∧ (z : ℝ) = a * b ∧ Algebra.norm ℚ z = -1 ∧
    1 < a ∧ 1 < b ∧ C1 a b 15 ∧ C3 a b ∧ C4 a b := by
  obtain ⟨a, ha1, ha3⟩ := exists_cubic_root
  obtain ⟨b, hb1, hb4⟩ := exists_quartic_root
  obtain ⟨z, hz⟩ := NormBridge.exists_mul_mem_adjoin_pair a b
  obtain ⟨-, -, hH, -⟩ := NormBridge.selmer3_mem_cubicUnits
  obtain ⟨-, -, hH', -⟩ := NormBridge.selmer4_mem_quarticNormNeg
  obtain ⟨h1, h3, h4, -⟩ := gravity_pass a b ha3 hb1 hb4
  refine ⟨X ^ 3 - X - 1, X ^ 4 - X - 1, a, b, z, NormBridge.selmer3_monic,
    NormBridge.selmer3_natDegree, fun i => (hH i).trans (by norm_num),
    NormBridge.selmer3_irreducible, NormBridge.selmer4_monic, NormBridge.selmer4_natDegree,
    fun i => (hH' i).trans (by norm_num), NormBridge.selmer4_irreducible, ?_, ?_, hz,
    (NormBridge.rhoQ_norm ha3 hb4).2 z hz, ha1, hb1, h1, h3, h4⟩
  · simp only [map_sub, map_pow, aeval_X, map_one]; linarith
  · simp only [map_sub, map_pow, aeval_X, map_one]; linarith

#print axioms unit_pairs_three_couplings
#print axioms unit_pairs_nonvacuous

end ExclusionRegion
