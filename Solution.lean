module

public import Mathlib
public import ExclusionRegion.Corollaries
public import ExclusionRegion.Cell62
public import ExclusionRegion.UnitPairs
public import ExclusionRegion.Stage3NonVacuity
public import ExclusionRegion.Sharpness

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
  constructor
  · rintro ⟨⟨P, hP, R, hR, ha, hb⟩, h1, h3, h4⟩
    have h : a ^ 3 = a + 1 ∧ b ^ 4 = b + 1 ∧ 1 < b := by
      rcases hDH with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ExclusionRegion.cell43_three_couplings P R hP hR a b ha hb p h1 h3 h4
      · exact ExclusionRegion.forced_of_windows ExclusionRegion.cell62_window_a
          ExclusionRegion.cell62_window_S (Pa := P) (Pb := R) hP hR ha hb h1 h3 h4
    obtain ⟨hp, hlow, _⟩ := ExclusionRegion.three_couplings a b p h1 h3 h4
    exact ⟨by linarith, h.1, h.2.2, h.2.1, hp⟩
  · rintro ⟨_, ha, hb, hb4, rfl⟩
    have hD : 4 ≤ D := by omega
    have hH : 2 ≤ H := by omega
    obtain ⟨h1, h3, h4, _⟩ := ExclusionRegion.gravity_pass a b ha hb hb4
    exact ⟨⟨_, ExclusionRegion.cell_mono hD hH ExclusionRegion.f3_mem_cell42,
      _, ExclusionRegion.cell_mono hD hH ExclusionRegion.f4_mem_cell42,
      ExclusionRegion.aeval_f3 ha, ExclusionRegion.aeval_f4 hb4⟩, h1, h3, h4⟩

/-- At height ten the signed norm cuts out the same passing triple. -/
theorem norm_classification (a b : ℝ) (p : ℕ) :
    NormPair 10 (-1) a b ∧ Windows a b p ↔
      1 < a ∧ a ^ 3 = a + 1 ∧ 1 < b ∧ b ^ 4 = b + 1 ∧ p = 15 := by
  constructor
  · rintro ⟨⟨P, R, z, hm, hd, hH, hi, hm', hd', hH', hi', ha, hb, hz, hN⟩, h1, h3, h4⟩
    obtain ⟨h, _⟩ := ExclusionRegion.unit_pairs_three_couplings hm hd hH hi hm' hd' hH' hi'
      ha hb z hz hN p h1 h3 h4
    obtain ⟨hp, hlow, _⟩ := ExclusionRegion.three_couplings a b p h1 h3 h4
    exact ⟨by linarith, h.1, h.2.2, h.2.1, hp⟩
  · rintro ⟨ha, ha3, hb, hb4, rfl⟩
    obtain ⟨P, R, u, v, z, hm, hd, hH, hi, hm', hd', hH', hi', hu, hv, hz, hN,
      _, _, h1, h3, h4⟩ := ExclusionRegion.unit_pairs_nonvacuous
    obtain ⟨_, identify⟩ := ExclusionRegion.unit_pairs_three_couplings hm hd hH hi hm' hd' hH' hi'
      hu hv z hz hN 15 h1 h3 h4
    obtain ⟨rfl, rfl⟩ := identify a b ha ha3 hb hb4
    exact ⟨⟨P, R, z, hm, hd, hH, hi, hm', hd', hH', hi', hu, hv, hz, hN⟩, h1, h3, h4⟩

/-- Raising the height bound by one admits a different quartic root at the same norm. -/
theorem height_eleven_counterexample :
    ∃ a b : ℝ, NormPair 11 (-1) a b ∧ Windows a b 15 ∧ b ^ 4 ≠ b + 1 := by
  obtain ⟨P, R, a, b, z, hm, hd, hH, hi, hm', hd', hH', hi', ha, hb, hz, hN,
    h1, h3, h4, hdiff⟩ := ExclusionRegion.Sharpness.unit_pairs_height11
  exact ⟨a, b, ⟨P, R, z, hm, hd, hH, hi, hm', hd', hH', hi', ha, hb, hz, hN⟩,
    ⟨h1, h3, h4⟩, hdiff⟩

/-- Changing the norm sign admits a different quartic root at the same height. -/
theorem positive_norm_counterexample :
    ∃ a b : ℝ, NormPair 10 1 a b ∧ Windows a b 15 ∧ b ^ 4 ≠ b + 1 := by
  obtain ⟨P, R, a, b, z, hm, hd, hH, hi, hm', hd', hH', hi', ha, hb, hz, hN,
    h1, h3, h4, hdiff⟩ := ExclusionRegion.Sharpness.unit_pairs_norm_pos
  exact ⟨a, b, ⟨P, R, z, hm, hd, hH, hi, hm', hd', hH', hi', ha, hb, hz, hN⟩,
    ⟨h1, h3, h4⟩, hdiff⟩

end ArithmeticClassification
