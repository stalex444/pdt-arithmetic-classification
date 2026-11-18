module

public import Mathlib
public import ExclusionRegion.WindowCheck

@[expose] public section

namespace ExclusionRegion

open Polynomial

/-! CELL (4, 3): monic integer polynomials of degree 2, 3 or 4, every coefficient in `-3 … 3`,
nonzero constant term — 2,394 polynomials, reducible ones included. The windows are fixed by
containment, not by outcome: the a-window `[1.3231557, 1.3265140]` is the three-coupling box of
F:520, which contains the gravity box of F:520 and the box of F:518; the b-window
`S = [1.22032003, 1.22113387]` is the slice of F:518. Nothing here orders candidates beyond
the cell rule. -/

/-- The enumerated cell has 2,394 entries. -/
theorem cellList43_length : (cellList 4 3).length = 2394 := by decide +kernel

/-- Kernel certificate, a-window: each of the 2,394 coefficient lists is root-free in
`[13231557/10⁷, 13265140/10⁷]` or is `(x³ − x − 1)·q` with `q` root-free there. -/
theorem cell43_checkA :
    ∀ cs ∈ cellList 4 3, winCheck f3L 10 13231557 13265140 10000000 2 cs = true := by
  decide +kernel

/-- Kernel certificate, slice `S`: the same with `[122032003/10⁸, 122113387/10⁸]` and
`x⁴ − x − 1`. -/
theorem cell43_checkS :
    ∀ cs ∈ cellList 4 3, winCheck f4L 10 122032003 122113387 100000000 2 cs = true := by
  decide +kernel

/-- WINDOW (a): in the cell (4, 3), every real root in `[1.3231557, 1.3265140]` is a root of
`x³ = x + 1`. -/
theorem cell43_window_a : ∀ P ∈ cell 4 3, ∀ x : ℝ, aeval x P = 0 →
    (1.3231557 : ℝ) ≤ x → x ≤ 1.3265140 → x ^ 3 = x + 1 := by
  intro P hP x h0 h1 h2
  apply evR_f3L
  refine cell_window f3L 10 2 (L := 13231557) (U := 13265140) (Dn := 10000000)
    (by norm_num) (by norm_num) cell43_checkA hP h0 ?_ ?_
  · push_cast; linarith
  · push_cast; linarith

/-- WINDOW (S): in the cell (4, 3), every real root in `[1.22032003, 1.22113387]` is a root of
`x⁴ = x + 1`. -/
theorem cell43_window_S : ∀ P ∈ cell 4 3, ∀ x : ℝ, aeval x P = 0 →
    (1.22032003 : ℝ) ≤ x → x ≤ 1.22113387 → x ^ 4 = x + 1 := by
  intro P hP x h0 h1 h2
  apply evR_f4L
  refine cell_window f4L 10 2 (L := 122032003) (U := 122113387) (Dn := 100000000)
    (by norm_num) (by norm_num) cell43_checkS hP h0 ?_ ?_
  · push_cast; linarith
  · push_cast; linarith

#print axioms cellList43_length
#print axioms cell43_checkA
#print axioms cell43_checkS
#print axioms cell43_window_a
#print axioms cell43_window_S

end ExclusionRegion
