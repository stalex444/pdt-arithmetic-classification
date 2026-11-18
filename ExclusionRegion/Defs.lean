module

public import Mathlib

@[expose] public section

namespace ExclusionRegion

open Real

/-- Target for the inverse fine-structure constant (window 0.5%). -/
noncomputable def T1 : ℝ := 137.036
/-- Target for the primordial helium fraction of Schramm and Turner (window 2%). -/
noncomputable def T2 : ℝ := 0.2449
/-- Target for the weak mixing angle (window 2%). -/
noncomputable def T3 : ℝ := 0.23121
/-- Target for the strong coupling (window 2%). -/
noncomputable def T4 : ℝ := 0.1180
/-- Target for the tau-to-electron mass ratio (window 2%). -/
noncomputable def T5 : ℝ := 3477.2

/-- `lam x = 1 - 1/x`, with real division as Lean has it (`1/0 = 0`). -/
noncomputable def lam (x : ℝ) : ℝ := 1 - 1 / x
/-- `psi a b = b/a`. -/
noncomputable def psi (a b : ℝ) : ℝ := b / a

/-- Constraint 1: `(ab)^p/π²` within 0.5% of `T1`. -/
def C1 (a b : ℝ) (p : ℕ) : Prop := |(a * b) ^ p / π ^ 2 - T1| ≤ 0.005 * T1
/-- Constraint 2: `lam a` within 2% of `T2`. -/
def C2 (a : ℝ) : Prop := |lam a - T2| ≤ 0.02 * T2
/-- Constraint 3: `lam b / psi³` within 2% of `T3`. -/
def C3 (a b : ℝ) : Prop := |lam b / (psi a b) ^ 3 - T3| ≤ 0.02 * T3
/-- Constraint 4: `lam b³ / (4 lam a³ psi²)` within 2% of `T4`. -/
def C4 (a b : ℝ) : Prop :=
  |(lam b) ^ 3 / (4 * (lam a) ^ 3 * (psi a b) ^ 2) - T4| ≤ 0.02 * T4
/-- Constraint 5: `a^k` within 2% of `T5`. -/
def C5 (a : ℝ) (k : ℕ) : Prop := |a ^ k - T5| ≤ 0.02 * T5

/-- The accepted set. -/
def A (a b : ℝ) : Prop :=
  3407.656 ≤ a ^ 29 ∧ a ^ 29 ≤ 3546.744 ∧
    0.995 * T1 * π ^ 2 ≤ (a * b) ^ 15 ∧ (a * b) ^ 15 ≤ 1.005 * T1 * π ^ 2

end ExclusionRegion
