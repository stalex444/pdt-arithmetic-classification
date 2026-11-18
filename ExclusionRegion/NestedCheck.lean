module

public import Mathlib
public import ExclusionRegion.WindowCheck

@[expose] public section

namespace ExclusionRegion

open Polynomial

/-! NESTED ENUMERATION for the larger cells. A flat `∀ cs ∈ cellList D H, …` over tens of
thousands of entries exceeds the kernel's recursion depth (UnitsForm.lean met this at 9,261
entries). `allBox H n f` runs `f` over every list of length `n` with entries in `-H … H`, one
coefficient per nesting level, so each `List.all` it reduces has only `2H + 1` entries.
`cellCheck D H p` runs `p` over exactly the entries of `cellList D H`. Soundness of both, back to
the flat enumerations `boxL` and `cellList` of WindowCheck.lean, is proved here, so a cell
certificate stated with `cellCheck` gives the same `∀ cs ∈ cellList D H, …` that `cell_window`
takes. -/

/-- `f` holds on every list of length `n` with entries in `-H … H`, checked one coefficient per
nesting level. -/
def allBox (H : ℕ) : ℕ → (List ℤ → Bool) → Bool
  | 0, f => f []
  | n + 1, f => (intRange H).all (fun c => allBox H n (fun l => f (c :: l)))

/-- SOUNDNESS of `allBox` against the flat enumeration `boxL`. -/
theorem allBox_sound {H : ℕ} :
    ∀ (n : ℕ) (f : List ℤ → Bool), allBox H n f = true → ∀ l ∈ boxL H n, f l = true
  | 0, f, h, l, hl => by
    simp only [boxL, List.mem_singleton] at hl
    subst hl
    simpa [allBox] using h
  | n + 1, f, h, l, hl => by
    simp only [boxL, List.mem_flatMap, List.mem_map] at hl
    obtain ⟨c, hc, l', hl', rfl⟩ := hl
    simp only [allBox, List.all_eq_true] at h
    exact allBox_sound n (fun l => f (c :: l)) (h c hc) l' hl'

/-- `p` holds on every entry of `cellList D H`, checked through `allBox`. -/
def cellCheck (D H : ℕ) (p : List ℤ → Bool) : Bool :=
  (List.range' 2 (D - 1)).all
    (fun d => allBox H d (fun l => !(l.headD 0 != 0) || p (l ++ [1])))

/-- SOUNDNESS of `cellCheck` against the flat enumeration `cellList`. -/
theorem cellCheck_sound {D H : ℕ} {p : List ℤ → Bool} (h : cellCheck D H p = true) :
    ∀ cs ∈ cellList D H, p cs = true := by
  intro cs hcs
  simp only [cellList, List.mem_flatMap, List.mem_map, List.mem_filter] at hcs
  obtain ⟨d, hd, l, ⟨hl, h0⟩, rfl⟩ := hcs
  simp only [cellCheck, List.all_eq_true] at h
  have hb := allBox_sound d _ (h d hd) l hl
  rw [h0, Bool.not_true, Bool.false_or] at hb
  exact hb

/-- The cells are monotone in the degree bound and the height. -/
theorem cell_mono {D D' H H' : ℕ} (hD : D ≤ D') (hH : H ≤ H') : cell D H ⊆ cell D' H' := by
  rintro P ⟨hm, h2, hd, hc, h0⟩
  refine ⟨hm, h2, hd.trans hD, fun i => (hc i).trans (by exact_mod_cast hH), h0⟩

#print axioms allBox_sound
#print axioms cellCheck_sound
#print axioms cell_mono

end ExclusionRegion
