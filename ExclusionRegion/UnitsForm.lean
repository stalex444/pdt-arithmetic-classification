module

public import Mathlib
public import ExclusionRegion.WindowCheck

@[expose] public section

namespace ExclusionRegion

open Polynomial

/-! UNITS FORM (F:511's exact conditions, height ≤ 10). `cubicUnits H`: monic integer cubics,
every coefficient of absolute value at most `H`, constant term `±1`. `quarticNormNeg H`: monic
integer quartics, every coefficient of absolute value at most `H`, constant term `−1`. Reducible
polynomials are included. The same window checker as the cells (WindowCheck.lean) runs over an
explicit enumeration of each set, and a proved coverage lemma carries every polynomial of the set
to its coefficient list in the enumeration.

Reading (a docstring remark, not a Lean claim): for an irreducible monic cubic with root `a` and an
irreducible monic quartic with root `b`, the degrees 3 and 4 are coprime, so `[ℚ(a, b) : ℚ] = 12`
and the field norm is `N(ab) = N(a)⁴ · N(b)³`, with `N(a) = −c₀(P_a)` and `N(b) = c₀(P_b)`. Hence
"`a` and `b` are units with `N(ab) = −1`" is the integer condition "cubic constant term `±1`,
quartic constant term `−1`" — F:511's unit and norm `−1` conditions. F:519 holds `N(ρQ) = −1` in
the kernel. The bridge from these integer conditions to the field norm is NOT formalized here. -/

/-- Monic integer cubics of height at most `H` with constant term `±1`. -/
def cubicUnits (H : ℕ) : Set ℤ[X] :=
  {P | P.Monic ∧ P.natDegree = 3 ∧ (∀ i, |P.coeff i| ≤ (H : ℤ)) ∧
    (P.coeff 0 = 1 ∨ P.coeff 0 = -1)}

/-- Monic integer quartics of height at most `H` with constant term `−1`. -/
def quarticNormNeg (H : ℕ) : Set ℤ[X] :=
  {P | P.Monic ∧ P.natDegree = 4 ∧ (∀ i, |P.coeff i| ≤ (H : ℤ)) ∧ P.coeff 0 = -1}

/-- Enumeration of `cubicUnits H`: `[c₀, c₁, c₂, 1]` with `c₀ = ±1`. -/
def cubicUnitsList (H : ℕ) : List (List ℤ) :=
  [1, -1].flatMap (fun c0 => (boxL H 2).map (fun l => c0 :: (l ++ [1])))

/-- Enumeration of `quarticNormNeg H`: `[−1, c₁, c₂, c₃, 1]`. -/
def quarticNormNegList (H : ℕ) : List (List ℤ) :=
  (boxL H 3).map (fun l => -1 :: (l ++ [1]))

/-- The coefficient list of a monic polynomial of degree `d + 1`. -/
theorem coeffList_succ {P : ℤ[X]} (hm : P.Monic) {d : ℕ} (hd : P.natDegree = d + 1) :
    coeffList P = P.coeff 0 :: ((List.range d).map (fun i => P.coeff (i + 1)) ++ [1]) := by
  have h1 : P.coeff (d + 1) = 1 := hd ▸ hm.coeff_natDegree
  rw [coeffList, hd, List.range_succ, List.map_append, List.range_succ_eq_map]
  simp [h1, Function.comp_def]

/-- COVERAGE (cubics): every polynomial of `cubicUnits H` has its coefficient list in the
enumeration. -/
theorem cubicUnits_mem {H : ℕ} {P : ℤ[X]} (hP : P ∈ cubicUnits H) :
    coeffList P ∈ cubicUnitsList H := by
  obtain ⟨hm, hd, hH, h0⟩ := hP
  rw [coeffList_succ hm (d := 2) hd, cubicUnitsList, List.mem_flatMap]
  refine ⟨P.coeff 0, by rcases h0 with h | h <;> simp [h], ?_⟩
  rw [List.mem_map]
  refine ⟨_, mem_boxL.mpr ⟨by simp, fun c hc => ?_⟩, rfl⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
  exact hH _

/-- COVERAGE (quartics): every polynomial of `quarticNormNeg H` has its coefficient list in the
enumeration. -/
theorem quarticNormNeg_mem {H : ℕ} {P : ℤ[X]} (hP : P ∈ quarticNormNeg H) :
    coeffList P ∈ quarticNormNegList H := by
  obtain ⟨hm, hd, hH, h0⟩ := hP
  rw [coeffList_succ hm (d := 3) hd, quarticNormNegList, List.mem_map, h0]
  refine ⟨_, mem_boxL.mpr ⟨by simp, fun c hc => ?_⟩, rfl⟩
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
  exact hH _

/-- The cubic enumeration at height 10 has 882 entries. -/
theorem cubicUnitsList10_length : (cubicUnitsList 10).length = 882 := by decide +kernel

/-- The quartic enumeration at height 10 has 9,261 entries. -/
theorem quarticNormNegList10_length : (quarticNormNegList 10).length = 9261 := by decide +kernel

/-- Kernel certificate, a-window: each of the 882 cubics is root-free in
`[13231557/10⁷, 13265140/10⁷]` or is `(x³ − x − 1)·q` with `q` root-free there. -/
theorem cubicUnits10_checkA :
    ∀ cs ∈ cubicUnitsList 10, winCheck f3L 10 13231557 13265140 10000000 2 cs = true := by
  decide +kernel

/-- Kernel certificate, slice `S`, nested by `c₁` (21 blocks of 441; a single flat list of
9,261 entries exceeds the kernel's recursion depth): each quartic `[−1, c₁, c₂, c₃, 1]` is
root-free in `[122032003/10⁸, 122113387/10⁸]` or is `(x⁴ − x − 1)·q` with `q` root-free there. -/
theorem quarticNormNeg10_checkS_nested :
    ∀ c ∈ intRange 10, ∀ l ∈ boxL 10 2,
      winCheck f4L 10 122032003 122113387 100000000 2 (-1 :: c :: (l ++ [1])) = true := by
  decide +kernel

/-- The same certificate over the flat enumeration of the 9,261 quartics. -/
theorem quarticNormNeg10_checkS :
    ∀ cs ∈ quarticNormNegList 10, winCheck f4L 10 122032003 122113387 100000000 2 cs = true := by
  intro cs hcs
  simp only [quarticNormNegList, List.mem_map] at hcs
  obtain ⟨l, hl, rfl⟩ := hcs
  rw [boxL, List.mem_flatMap] at hl
  obtain ⟨c, hc, hl⟩ := hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
  exact quarticNormNeg10_checkS_nested c hc l' hl'

/-- **UNITS WINDOW (a).** Every real root in `[1.3231557, 1.3265140]` of a monic integer cubic of
height at most 10 with constant term `±1` satisfies `x³ = x + 1`. -/
theorem cubicUnits10_window_a : ∀ P ∈ cubicUnits 10, ∀ x : ℝ, aeval x P = 0 →
    (1.3231557 : ℝ) ≤ x → x ≤ 1.3265140 → x ^ 3 = x + 1 := by
  intro P hP x h0 h1 h2
  rw [aeval_eq_evR] at h0
  apply evR_f3L
  refine winCheck_sound f3L 10 (L := 13231557) (U := 13265140) (D := 10000000) (by norm_num)
    (by norm_num) 2 (cubicUnits10_checkA _ (cubicUnits_mem hP)) ?_ ?_ h0
  · push_cast; linarith
  · push_cast; linarith

/-- **UNITS WINDOW (S).** Every real root in `[1.22032003, 1.22113387]` of a monic integer
quartic of height at most 10 with constant term `−1` satisfies `x⁴ = x + 1`. -/
theorem quarticNormNeg10_window_S : ∀ P ∈ quarticNormNeg 10, ∀ x : ℝ, aeval x P = 0 →
    (1.22032003 : ℝ) ≤ x → x ≤ 1.22113387 → x ^ 4 = x + 1 := by
  intro P hP x h0 h1 h2
  rw [aeval_eq_evR] at h0
  apply evR_f4L
  refine winCheck_sound f4L 10 (L := 122032003) (U := 122113387) (D := 100000000) (by norm_num)
    (by norm_num) 2 (quarticNormNeg10_checkS _ (quarticNormNeg_mem hP)) ?_ ?_ h0
  · push_cast; linarith
  · push_cast; linarith

#print axioms coeffList_succ
#print axioms cubicUnits_mem
#print axioms quarticNormNeg_mem
#print axioms cubicUnitsList10_length
#print axioms quarticNormNegList10_length
#print axioms cubicUnits10_checkA
#print axioms quarticNormNeg10_checkS_nested
#print axioms quarticNormNeg10_checkS
#print axioms cubicUnits10_window_a
#print axioms quarticNormNeg10_window_S

end ExclusionRegion
