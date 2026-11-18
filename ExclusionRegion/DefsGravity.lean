module

public import Mathlib
public import ExclusionRegion.Defs

@[expose] public section

namespace ExclusionRegion

open Real

/-- Target for gravity, `α/α_G` for the electron: `ħc/(α⁻¹·G·m_e²)` with the CODATA 2022 decimals
`ħ = 1.054571817e-34`, `c = 299792458`, `α⁻¹ = 137.035999177`, `G = 6.67430e-11`,
`m_e = 9.1093837139e-31` (F:510's computed target, an exact rational; `4.16560875e42` is its
9-figure rounding). -/
noncomputable def TG : ℝ :=
  1.054571817e-34 * 299792458 / (137.035999177 * 6.67430e-11 * (9.1093837139e-31) ^ 2)

/-- Constraint G (gravity, screened form of F:510): `(ab)^n (2b-1)/(π² b²)` within 2% of `TG`. -/
def CG (a b : ℝ) (n : ℕ) : Prop := |(a * b) ^ n * (2 * b - 1) / (π ^ 2 * b ^ 2) - TG| ≤ 0.02 * TG

end ExclusionRegion
