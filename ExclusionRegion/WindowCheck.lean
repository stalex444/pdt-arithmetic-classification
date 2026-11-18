module

public import Mathlib

@[expose] public section

namespace ExclusionRegion

open Polynomial

/-! WINDOW CHECKER. A coefficient list `cs = [c₀, c₁, …, c_n]` stands for `Σ cᵢ xⁱ`. A window
`[L/D, U/D]` with integers `0 ≤ L`, `0 < D` is cleared by a term-by-term enclosure: on the window
each `cᵢ xⁱ` lies between `cᵢ (L/D)ⁱ` and `cᵢ (U/D)ⁱ`, so (after scaling by a power of `D`, all in
integers) a positive sum of lower ends or a negative sum of upper ends excludes a root. Windows
that are not cleared are bisected (structural fuel). A polynomial divisible by a target `tgt`
(`x³ − x − 1` or `x⁴ − x − 1`) is handled by a cofactor computed by long division and CHECKED by
exact list multiplication; the cofactor is then certified in turn. Soundness: `winCheck_sound`. -/

/-- Real evaluation of a coefficient list, Horner form. -/
noncomputable def evR : List ℤ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * evR cs x

/-- The integer polynomial of a coefficient list. -/
noncomputable def ofList : List ℤ → ℤ[X]
  | [] => 0
  | c :: cs => C c + X * ofList cs

theorem aeval_ofList (cs : List ℤ) (x : ℝ) : aeval x (ofList cs) = evR cs x := by
  induction cs with
  | nil => simp [ofList, evR]
  | cons c cs ih => simp [ofList, evR, ih]

/-- Lower end of the term `c·(L/D)^i` vs `c·(U/D)^i`, scaled by `D^(i+k)`. -/
def tLo (L U D c : ℤ) (i k : ℕ) : ℤ :=
  if c * L ^ i * D ^ k ≤ c * U ^ i * D ^ k then c * L ^ i * D ^ k else c * U ^ i * D ^ k

/-- Upper end of the same term. -/
def tHi (L U D c : ℤ) (i k : ℕ) : ℤ :=
  if c * L ^ i * D ^ k ≤ c * U ^ i * D ^ k then c * U ^ i * D ^ k else c * L ^ i * D ^ k

/-- Sum of lower ends; the term at position `i` carries `D^(#later terms + 1)`. -/
def encLo (L U D : ℤ) : List ℤ → ℕ → ℤ
  | [], _ => 0
  | c :: cs, i => tLo L U D c i (cs.length + 1) + encLo L U D cs (i + 1)

/-- Sum of upper ends. -/
def encHi (L U D : ℤ) : List ℤ → ℕ → ℤ
  | [], _ => 0
  | c :: cs, i => tHi L U D c i (cs.length + 1) + encHi L U D cs (i + 1)

/-- One enclosure clears the window `[L/D, U/D]`. -/
def clears (L U D : ℤ) (cs : List ℤ) : Bool :=
  decide (0 < encLo L U D cs 0) || decide (encHi L U D cs 0 < 0)

/-- Enclosure with bisection, `fuel` levels deep. -/
def noRootAux : ℕ → ℤ → ℤ → ℤ → List ℤ → Bool
  | 0, L, U, D, cs => clears L U D cs
  | f + 1, L, U, D, cs =>
      clears L U D cs ||
        (noRootAux f (2 * L) (L + U) (2 * D) cs && noRootAux f (L + U) (2 * U) (2 * D) cs)

/-- The scaled real value the enclosure brackets (`y = x·D`). -/
noncomputable def tv (x : ℝ) (D : ℤ) : List ℤ → ℕ → ℝ
  | [], _ => 0
  | c :: cs, i => (c : ℝ) * (x * D) ^ i * (D : ℝ) ^ (cs.length + 1) + tv x D cs (i + 1)

theorem tv_eq (x : ℝ) (D : ℤ) (cs : List ℤ) (i : ℕ) :
    tv x D cs i = x ^ i * (D : ℝ) ^ (i + cs.length) * evR cs x := by
  induction cs generalizing i with
  | nil => simp [tv, evR]
  | cons c cs ih =>
    simp only [tv, evR, ih, List.length_cons]
    rw [mul_pow]
    ring

theorem term_between {L U y e : ℝ} (hL : 0 ≤ L) (hLy : L ≤ y) (hyU : y ≤ U) (he : 0 ≤ e)
    (c : ℝ) (i : ℕ) :
    (c * L ^ i * e ≤ c * y ^ i * e ∧ c * y ^ i * e ≤ c * U ^ i * e) ∨
      (c * U ^ i * e ≤ c * y ^ i * e ∧ c * y ^ i * e ≤ c * L ^ i * e) := by
  have h1 : L ^ i ≤ y ^ i := pow_le_pow_left₀ hL hLy i
  have h2 : y ^ i ≤ U ^ i := pow_le_pow_left₀ (hL.trans hLy) hyU i
  rcases le_total 0 c with hc | hc
  · exact Or.inl ⟨mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc) he,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hc) he⟩
  · exact Or.inr ⟨mul_le_mul_of_nonneg_right (mul_le_mul_of_nonpos_left h2 hc) he,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonpos_left h1 hc) he⟩

theorem tLo_le {L U D : ℤ} {x : ℝ} (hL : 0 ≤ L) (hD : 0 < D) (h1 : (L : ℝ) ≤ x * D)
    (h2 : x * D ≤ U) (c : ℤ) (i k : ℕ) :
    (tLo L U D c i k : ℝ) ≤ (c : ℝ) * (x * D) ^ i * (D : ℝ) ^ k ∧
      (c : ℝ) * (x * D) ^ i * (D : ℝ) ^ k ≤ (tHi L U D c i k : ℝ) := by
  have he : (0 : ℝ) ≤ (D : ℝ) ^ k := pow_nonneg (by exact_mod_cast hD.le) k
  have hb := term_between (by exact_mod_cast hL) h1 h2 he (c : ℝ) i
  unfold tLo tHi
  split_ifs with h
  · have h' : (c : ℝ) * (L : ℝ) ^ i * (D : ℝ) ^ k ≤ (c : ℝ) * (U : ℝ) ^ i * (D : ℝ) ^ k := by
      exact_mod_cast h
    push_cast
    rcases hb with hb | hb
    · exact hb
    · exact ⟨by linarith [hb.1, hb.2], by linarith [hb.1, hb.2]⟩
  · have h' : (c : ℝ) * (U : ℝ) ^ i * (D : ℝ) ^ k < (c : ℝ) * (L : ℝ) ^ i * (D : ℝ) ^ k := by
      exact_mod_cast (not_le.mp h)
    push_cast
    rcases hb with hb | hb
    · exact ⟨by linarith [hb.1, hb.2], by linarith [hb.1, hb.2]⟩
    · exact hb

theorem enc_bracket {L U D : ℤ} {x : ℝ} (hL : 0 ≤ L) (hD : 0 < D) (h1 : (L : ℝ) ≤ x * D)
    (h2 : x * D ≤ U) (cs : List ℤ) (i : ℕ) :
    (encLo L U D cs i : ℝ) ≤ tv x D cs i ∧ tv x D cs i ≤ (encHi L U D cs i : ℝ) := by
  induction cs generalizing i with
  | nil => simp [encLo, encHi, tv]
  | cons c cs ih =>
    have ht := tLo_le hL hD h1 h2 c i (cs.length + 1)
    have hr := ih (i + 1)
    simp only [encLo, encHi, tv]
    push_cast
    exact ⟨by linarith [ht.1, hr.1], by linarith [ht.2, hr.2]⟩

theorem clears_sound {L U D : ℤ} {cs : List ℤ} (h : clears L U D cs = true) (hL : 0 ≤ L)
    (hD : 0 < D) {x : ℝ} (h1 : (L : ℝ) ≤ x * D) (h2 : x * D ≤ U) : evR cs x ≠ 0 := by
  intro h0
  have hb := enc_bracket hL hD h1 h2 cs 0
  rw [tv_eq, h0, mul_zero] at hb
  unfold clears at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · have : (0 : ℝ) < encLo L U D cs 0 := by exact_mod_cast of_decide_eq_true h
    linarith [hb.1]
  · have : (encHi L U D cs 0 : ℝ) < 0 := by exact_mod_cast of_decide_eq_true h
    linarith [hb.2]

theorem noRootAux_sound (f : ℕ) {L U D : ℤ} {cs : List ℤ} (h : noRootAux f L U D cs = true)
    (hL : 0 ≤ L) (hD : 0 < D) {x : ℝ} (h1 : (L : ℝ) ≤ x * D) (h2 : x * D ≤ U) :
    evR cs x ≠ 0 := by
  induction f generalizing L U D with
  | zero => exact clears_sound h hL hD h1 h2
  | succ f ih =>
    simp only [noRootAux, Bool.or_eq_true_iff, Bool.and_eq_true] at h
    rcases h with h | ⟨ha, hb⟩
    · exact clears_sound h hL hD h1 h2
    · have hLU : (L : ℝ) ≤ U := h1.trans h2
      have hLU' : L ≤ U := by exact_mod_cast hLU
      rcases le_total (x * (2 * D : ℤ)) ((L + U : ℤ) : ℝ) with hm | hm
      · refine ih ha (by omega) (by omega) ?_ hm
        push_cast at hm ⊢; linarith
      · refine ih hb (by omega) (by omega) hm ?_
        push_cast at hm ⊢; linarith

/-! ## Exact list arithmetic for the cofactor check -/

/-- Coefficientwise sum (lists of unequal length padded by zeros). -/
def addL : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addL as bs

/-- Product of coefficient lists. -/
def mulL : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, q => addL (q.map (a * ·)) (0 :: mulL as q)

theorem evR_addL (as bs : List ℤ) (x : ℝ) : evR (addL as bs) x = evR as x + evR bs x := by
  induction as generalizing bs with
  | nil => simp [addL, evR]
  | cons a as ih =>
    cases bs with
    | nil => simp [addL, evR]
    | cons b bs => simp only [addL, evR, ih]; push_cast; ring

theorem evR_map_mul (a : ℤ) (q : List ℤ) (x : ℝ) : evR (q.map (a * ·)) x = a * evR q x := by
  induction q with
  | nil => simp [evR]
  | cons c q ih => simp only [List.map_cons, evR, ih]; push_cast; ring

theorem evR_mulL (p q : List ℤ) (x : ℝ) : evR (mulL p q) x = evR p x * evR q x := by
  induction p with
  | nil => simp [mulL, evR]
  | cons a p ih =>
    simp only [mulL, evR_addL, evR_map_mul, evR, ih]; push_cast; ring

/-- `p − c·d` on the leading positions (reversed lists, highest coefficient first). -/
def subPref : List ℤ → List ℤ → ℤ → List ℤ
  | p, [], _ => p
  | [], _, _ => []
  | a :: p, b :: d, c => (a - c * b) :: subPref p d c

/-- Long division by a monic divisor on reversed lists (quotient, highest first). Its
correctness is never used: the quotient is checked by exact multiplication. -/
def divRev : ℕ → List ℤ → List ℤ → List ℤ
  | 0, _, _ => []
  | f + 1, p, d =>
      if d.length ≤ p.length then
        match p with
        | [] => []
        | c :: _ => c :: divRev f (subPref p d c).tail d
      else []

/-- The candidate cofactor of `cs` by `tgt`. -/
def quo (cs tgt : List ℤ) : List ℤ := (divRev cs.length cs.reverse tgt.reverse).reverse

/-- The window check: `cs` is root-free in `[L/D, U/D]`, or `cs = tgt · q` exactly with `q`
passing the same check (up to `m` factors of `tgt`). -/
def winCheck (tgt : List ℤ) (fuel : ℕ) (L U D : ℤ) : ℕ → List ℤ → Bool
  | 0, cs => noRootAux fuel L U D cs
  | m + 1, cs =>
      noRootAux fuel L U D cs ||
        (decide (mulL tgt (quo cs tgt) = cs) && winCheck tgt fuel L U D m (quo cs tgt))

/-- SOUNDNESS: if the check passes, every root of `cs` in the window `[L/D, U/D]` is a root of
`tgt`. -/
theorem winCheck_sound (tgt : List ℤ) (fuel : ℕ) {L U D : ℤ} (hL : 0 ≤ L) (hD : 0 < D)
    (m : ℕ) {cs : List ℤ} (h : winCheck tgt fuel L U D m cs = true) {x : ℝ}
    (h1 : (L : ℝ) ≤ x * D) (h2 : x * D ≤ U) (h0 : evR cs x = 0) : evR tgt x = 0 := by
  induction m generalizing cs with
  | zero => exact absurd h0 (noRootAux_sound fuel h hL hD h1 h2)
  | succ m ih =>
    simp only [winCheck, Bool.or_eq_true_iff, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hq, hrest⟩
    · exact absurd h0 (noRootAux_sound fuel h hL hD h1 h2)
    · rw [← hq, evR_mulL] at h0
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact h0
      · exact ih hrest h0

/-! ## The cell and the bridge from `ℤ[X]` to coefficient lists -/

/-- The cell `C(D, H)`: monic integer polynomials of degree `2 … D`, every coefficient of
absolute value at most `H`, nonzero constant term. Reducible polynomials are included. -/
def cell (D H : ℕ) : Set ℤ[X] :=
  {P | P.Monic ∧ 2 ≤ P.natDegree ∧ P.natDegree ≤ D ∧ (∀ i, |P.coeff i| ≤ (H : ℤ)) ∧
    P.coeff 0 ≠ 0}

/-- The integers `-H … H`. -/
def intRange (H : ℕ) : List ℤ := (List.range (2 * H + 1)).map (fun i : ℕ => (i : ℤ) - H)

/-- All lists of length `n` with entries in `-H … H`. -/
def boxL (H : ℕ) : ℕ → List (List ℤ)
  | 0 => [[]]
  | n + 1 => (intRange H).flatMap (fun c => (boxL H n).map (c :: ·))

/-- The enumerated cell: for each degree `d = 2 … D`, the lower coefficients from `boxL H d`
with nonzero constant term, followed by the leading `1`. -/
def cellList (D H : ℕ) : List (List ℤ) :=
  (List.range' 2 (D - 1)).flatMap
    (fun d => ((boxL H d).filter (fun l => l.headD 0 != 0)).map (· ++ [1]))

theorem mem_intRange {H : ℕ} {c : ℤ} : c ∈ intRange H ↔ |c| ≤ (H : ℤ) := by
  rw [abs_le, intRange, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have := List.mem_range.mp hi
    omega
  · intro h
    exact ⟨(c + H).toNat, List.mem_range.mpr (by omega), by omega⟩

theorem mem_boxL {H n : ℕ} {l : List ℤ} :
    l ∈ boxL H n ↔ l.length = n ∧ ∀ c ∈ l, |c| ≤ (H : ℤ) := by
  induction n generalizing l with
  | zero => cases l <;> simp [boxL]
  | succ n ih =>
    cases l with
    | nil => simp [boxL]
    | cons a l =>
      simp only [boxL, List.mem_flatMap, List.mem_map, List.cons.injEq, List.length_cons,
        List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨c, hc, l', hl', rfl, rfl⟩
        exact ⟨(ih.mp hl').1, mem_intRange.mp hc, (ih.mp hl').2⟩
      · rintro ⟨hlen, ha, hl⟩
        exact ⟨a, mem_intRange.mpr ha, l, ih.mpr ⟨hlen, hl⟩, rfl, rfl⟩

/-- The coefficient list of a polynomial, `c₀ … c_deg`. -/
noncomputable def coeffList (P : ℤ[X]) : List ℤ := (List.range (P.natDegree + 1)).map P.coeff

theorem evR_append (a b : List ℤ) (x : ℝ) :
    evR (a ++ b) x = evR a x + x ^ a.length * evR b x := by
  induction a with
  | nil => simp [evR]
  | cons c a ih => simp only [List.cons_append, evR, ih, List.length_cons]; ring

theorem evR_range_map (f : ℕ → ℤ) (n : ℕ) (x : ℝ) :
    evR ((List.range n).map f) x = ∑ i ∈ Finset.range n, (f i : ℝ) * x ^ i := by
  induction n with
  | zero => simp [evR]
  | succ n ih =>
    rw [List.range_succ, List.map_append, evR_append, ih, Finset.sum_range_succ,
      List.length_map, List.length_range]
    simp [evR, mul_comm]

/-- BRIDGE (evaluation): a polynomial evaluates as its coefficient list. -/
theorem aeval_eq_evR (P : ℤ[X]) (x : ℝ) : aeval x P = evR (coeffList P) x := by
  rw [coeffList, evR_range_map, aeval_eq_sum_range]
  simp [zsmul_eq_mul]

/-- BRIDGE (membership): a polynomial of the cell has its coefficient list in `cellList`. -/
theorem coeffList_mem {D H : ℕ} {P : ℤ[X]} (hP : P ∈ cell D H) : coeffList P ∈ cellList D H := by
  obtain ⟨hm, hd2, hdD, hH, h0⟩ := hP
  set d := P.natDegree with hd
  have hsplit : coeffList P = (List.range d).map P.coeff ++ [1] := by
    rw [coeffList, ← hd, List.range_succ, List.map_append]
    simp [hd, hm.coeff_natDegree]
  rw [hsplit, cellList, List.mem_flatMap]
  refine ⟨d, ?_, ?_⟩
  · rw [List.mem_range'_1]; omega
  · rw [List.mem_map]
    refine ⟨(List.range d).map P.coeff, ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨mem_boxL.mpr ⟨by simp, fun c hc => ?_⟩, ?_⟩
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
      exact hH i
    · obtain ⟨k, hk⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      rw [hk, List.range_succ_eq_map]
      simpa using h0

/-- From the list-level check to the polynomial-level window statement. -/
theorem cell_window {D H : ℕ} (tgt : List ℤ) (fuel m : ℕ) {L U Dn : ℤ} (hL : 0 ≤ L)
    (hD : 0 < Dn) (hall : ∀ cs ∈ cellList D H, winCheck tgt fuel L U Dn m cs = true)
    {P : ℤ[X]} (hP : P ∈ cell D H) {x : ℝ} (h0 : aeval x P = 0) (h1 : (L : ℝ) ≤ x * Dn)
    (h2 : x * Dn ≤ U) : evR tgt x = 0 := by
  rw [aeval_eq_evR] at h0
  exact winCheck_sound tgt fuel hL hD m (hall _ (coeffList_mem hP)) h1 h2 h0

/-- `x³ − x − 1` as a coefficient list. -/
def f3L : List ℤ := [-1, -1, 0, 1]
/-- `x⁴ − x − 1` as a coefficient list. -/
def f4L : List ℤ := [-1, -1, 0, 0, 1]

theorem evR_f3L (x : ℝ) (h : evR f3L x = 0) : x ^ 3 = x + 1 := by
  simp only [f3L, evR] at h; push_cast at h; linear_combination h

theorem evR_f4L (x : ℝ) (h : evR f4L x = 0) : x ^ 4 = x + 1 := by
  simp only [f4L, evR] at h; push_cast at h; linear_combination h

#print axioms winCheck_sound
#print axioms cell_window

end ExclusionRegion
