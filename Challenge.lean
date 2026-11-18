module

public import Mathlib

/-!
# Classification of bounded-height algebraic roots in three coupling windows

The two equivalences classify ordered triples. The last two theorems witness the limits
of the norm classification. The README gives the field, the quartics and the proof method.
-/

@[expose] public section

namespace ArithmeticClassification

open Real Polynomial IntermediateField

/-- Three closed relative windows. The exponent ranges over all natural numbers. -/
def Windows (a b : ℝ) (p : ℕ) : Prop :=
  |(a * b) ^ p / π ^ 2 - 137.036| ≤ 0.005 * 137.036 ∧
  |(1 - 1 / b) / (b / a) ^ 3 - 0.23121| ≤ 0.02 * 0.23121 ∧
  |(1 - 1 / b) ^ 3 / (4 * (1 - 1 / a) ^ 3 * (b / a) ^ 2) - 0.1180| ≤ 0.02 * 0.1180

/-- Monic integer polynomials of degrees 2 through D, with bounded coefficients. -/
def Cell (D H : ℕ) : Set ℤ[X] :=
  {P | P.Monic ∧ 2 ≤ P.natDegree ∧ P.natDegree ≤ D ∧
    (∀ i, |P.coeff i| ≤ (H : ℤ)) ∧ P.coeff 0 ≠ 0}

/-- Each coordinate is a root of a polynomial from the same cell. -/
def CellPair (D H : ℕ) (a b : ℝ) : Prop :=
  ∃ P ∈ Cell D H, ∃ R ∈ Cell D H, aeval a P = 0 ∧ aeval b R = 0

/-- A cubic root followed by a quartic root. The sign is the field norm of their product. -/
def NormPair (H : ℕ) (sign : ℚ) (a b : ℝ) : Prop :=
  ∃ (P R : ℤ[X]) (z : ℚ⟮a, b⟯),
    P.Monic ∧ P.natDegree = 3 ∧ (∀ i, |P.coeff i| ≤ (H : ℤ)) ∧
    Irreducible (P.map (Int.castRingHom ℚ)) ∧
    R.Monic ∧ R.natDegree = 4 ∧ (∀ i, |R.coeff i| ≤ (H : ℤ)) ∧
    Irreducible (R.map (Int.castRingHom ℚ)) ∧
    aeval a P = 0 ∧ aeval b R = 0 ∧ (z : ℝ) = a * b ∧ Algebra.norm ℚ z = sign

/-- The passing triples in each of the two polynomial families, in both directions. -/
theorem cell_classification (D H : ℕ) (hDH : (D = 4 ∧ H = 3) ∨ (D = 6 ∧ H = 2))
    (a b : ℝ) (p : ℕ) :
    CellPair D H a b ∧ Windows a b p ↔
      1 < a ∧ a ^ 3 = a + 1 ∧ 1 < b ∧ b ^ 4 = b + 1 ∧ p = 15 := by
  sorry

/-- At height ten the signed norm cuts out the same passing triple. -/
theorem norm_classification (a b : ℝ) (p : ℕ) :
    NormPair 10 (-1) a b ∧ Windows a b p ↔
      1 < a ∧ a ^ 3 = a + 1 ∧ 1 < b ∧ b ^ 4 = b + 1 ∧ p = 15 := by
  sorry

/-- Raising the height bound by one admits a different quartic root at the same norm. -/
theorem height_eleven_counterexample :
    ∃ a b : ℝ, NormPair 11 (-1) a b ∧ Windows a b 15 ∧ b ^ 4 ≠ b + 1 := by
  sorry

/-- Changing the norm sign admits a different quartic root at the same height. -/
theorem positive_norm_counterexample :
    ∃ a b : ℝ, NormPair 10 1 a b ∧ Windows a b 15 ∧ b ^ 4 ≠ b + 1 := by
  sorry

end ArithmeticClassification
