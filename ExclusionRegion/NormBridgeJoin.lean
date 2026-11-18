module

public import Mathlib
public import ExclusionRegion.NormBridge
public import ExclusionRegion.UnitsForm

/-!
# The norm bridge: the join to F:524's sets

`P` a monic integer cubic and `P'` a monic integer quartic, each irreducible over `ℚ` in the
fixed form `Irreducible (P.map (Int.castRingHom ℚ))`; `a`, `b` roots of `P`, `P'` in a field `E`
of characteristic zero.

* `minpoly_eq_map` : `minpoly ℚ a = P.map (Int.castRingHom ℚ)`.
* `finrank_adjoin_pair` : `[ℚ(a, b) : ℚ] = 12`, the field `ℚ⟮a, b⟯` inside any `E`.
* `norm_mul_eq_coeff_pow` : if `ℚ⟮a, b⟯ = ⊤` (`E = ℚ(a, b)`), then `[E : ℚ] = 12` and
  `N_{E/ℚ}(ab) = c₀(P)⁴ · c₀(P')³`. (Sign conventions: `N_{ℚ(a)/ℚ}(a) = −c₀(P)`,
  `N_{ℚ(b)/ℚ}(b) = c₀(P')`; `norm_gen_cubic`, `norm_gen_quartic`.)
* `int_pow4_mul_pow3_eq_neg_one` : in `ℤ`, `c⁴ d³ = −1 ↔ (c = 1 ∨ c = −1) ∧ d = −1`.
* `norm_mul_eq_neg_one_iff` : `N_{E/ℚ}(ab) = −1 ↔ (c₀(P) = ±1 ∧ c₀(P') = −1)`.
* `mem_units_iff_norm_mul_eq_neg_one` : for `P`, `P'` of height at most `H`:
  `P ∈ cubicUnits H ∧ P' ∈ quarticNormNeg H ↔ N_{E/ℚ}(ab) = −1`.
* REAL-ROOT FORM (F:524's own terms: `a b : ℝ`, `aeval a P = 0`, `aeval b P' = 0`, the field
  `ℚ⟮a, b⟯` as an intermediate field of `ℝ`): `real_norm_mul_eq_coeff_pow`,
  `real_mem_units_iff_norm_mul_eq_neg_one`, `real_norm_mul_eq_neg_one_of_mem`.
-/

@[expose] public section

namespace ExclusionRegion.NormBridge

open IntermediateField Polynomial Module

/-- A root of a monic integer polynomial irreducible over `ℚ` has that polynomial (read over
`ℚ`) as its minimal polynomial. -/
theorem minpoly_eq_map {E : Type*} [Field E] [Algebra ℚ E] {P : ℤ[X]} (hm : P.Monic)
    (hirr : Irreducible (P.map (Int.castRingHom ℚ))) {a : E} (ha : aeval a P = 0) :
    minpoly ℚ a = P.map (Int.castRingHom ℚ) := by
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (hm.map _)).symm
  rw [← algebraMap_int_eq, aeval_map_algebraMap]
  exact ha

/-- A root of a monic integer polynomial is integral over `ℚ`. -/
theorem isIntegral_of_root {E : Type*} [Field E] [Algebra ℚ E] {P : ℤ[X]} (hm : P.Monic)
    {a : E} (ha : aeval a P = 0) : IsIntegral ℚ a :=
  IsIntegral.tower_top (A := ℚ) (⟨P, hm, ha⟩ : IsIntegral ℤ a)

/-- `[ℚ(a) : ℚ] = deg P` for a root `a` of a monic integer `P` irreducible over `ℚ`. -/
theorem finrank_adjoin_root {E : Type*} [Field E] [Algebra ℚ E] {P : ℤ[X]} (hm : P.Monic)
    (hirr : Irreducible (P.map (Int.castRingHom ℚ))) {a : E} (ha : aeval a P = 0) :
    finrank ℚ ℚ⟮a⟯ = P.natDegree := by
  rw [adjoin.finrank (isIntegral_of_root hm ha), minpoly_eq_map hm hirr ha, hm.natDegree_map]

/-- `N_{ℚ(a)/ℚ}(a) = −c₀(P)` for a root `a` of a monic irreducible integer cubic `P`. -/
theorem norm_gen_cubic {E : Type*} [Field E] [Algebra ℚ E] {P : ℤ[X]} (hm : P.Monic)
    (hd : P.natDegree = 3) (hirr : Irreducible (P.map (Int.castRingHom ℚ))) {a : E}
    (ha : aeval a P = 0) :
    Algebra.norm ℚ (AdjoinSimple.gen ℚ a) = -(P.coeff 0 : ℚ) := by
  have h := norm_gen_eq_coeff_zero (K := ℚ) a (isIntegral_of_root hm ha)
  rw [minpoly_eq_map hm hirr ha, hm.natDegree_map, hd, coeff_map, eq_intCast] at h
  convert h using 1
  · congr 2
    exact Subsingleton.elim _ _
  · ring

/-- `N_{ℚ(b)/ℚ}(b) = c₀(P')` for a root `b` of a monic irreducible integer quartic `P'`. -/
theorem norm_gen_quartic {E : Type*} [Field E] [Algebra ℚ E] {P : ℤ[X]} (hm : P.Monic)
    (hd : P.natDegree = 4) (hirr : Irreducible (P.map (Int.castRingHom ℚ))) {b : E}
    (hb : aeval b P = 0) :
    Algebra.norm ℚ (AdjoinSimple.gen ℚ b) = (P.coeff 0 : ℚ) := by
  have h := norm_gen_eq_coeff_zero (K := ℚ) b (isIntegral_of_root hm hb)
  rw [minpoly_eq_map hm hirr hb, hm.natDegree_map, hd, coeff_map, eq_intCast] at h
  convert h using 1
  · congr 2
    exact Subsingleton.elim _ _
  · ring

/-- `ℚ⟮a, b⟯ = ℚ⟮a⟯ ⊔ ℚ⟮b⟯`. -/
theorem adjoin_pair_eq_sup {E : Type*} [Field E] [Algebra ℚ E] (a b : E) :
    ℚ⟮a, b⟯ = ℚ⟮a⟯ ⊔ ℚ⟮b⟯ := by
  rw [Set.insert_eq, adjoin_union]

/-- **Degree 12.** For a root `a` of a monic irreducible integer cubic and a root `b` of a monic
irreducible integer quartic, in any field `E` of characteristic zero, `[ℚ(a, b) : ℚ] = 12`. -/
theorem finrank_adjoin_pair {E : Type*} [Field E] [Algebra ℚ E] {P P' : ℤ[X]}
    (hm : P.Monic) (hd : P.natDegree = 3) (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hm' : P'.Monic) (hd' : P'.natDegree = 4) (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : E} (ha : aeval a P = 0) (hb : aeval b P' = 0) :
    finrank ℚ ℚ⟮a, b⟯ = 12 := by
  have hfa := finrank_adjoin_root hm hirr ha
  have hfb := finrank_adjoin_root hm' hirr' hb
  rw [hd] at hfa
  rw [hd'] at hfb
  rw [adjoin_pair_eq_sup, finrank_sup_of_coprime (by rw [hfa, hfb]; decide), hfa, hfb]

/-- **Norm, degree form.** If `[E : ℚ] = 12`, then for roots `a`, `b` as above,
`N_{E/ℚ}(ab) = c₀(P)⁴ · c₀(P')³`. -/
theorem norm_mul_eq_coeff_pow_of_finrank {E : Type*} [Field E] [Algebra ℚ E] (hE : finrank ℚ E = 12)
    {P P' : ℤ[X]}
    (hm : P.Monic) (hd : P.natDegree = 3) (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hm' : P'.Monic) (hd' : P'.natDegree = 4) (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : E} (ha : aeval a P = 0) (hb : aeval b P' = 0) :
    Algebra.norm ℚ (a * b) = ((P.coeff 0 ^ 4 * P'.coeff 0 ^ 3 : ℤ) : ℚ) := by
  rw [norm_mul_eq_coeff_div a b (isIntegral_of_root hm ha) (isIntegral_of_root hm' hb),
    minpoly_eq_map hm hirr ha, minpoly_eq_map hm' hirr' hb, hm.natDegree_map, hm'.natDegree_map,
    hd, hd', hE, coeff_map, coeff_map, eq_intCast, eq_intCast]
  norm_num

/-- **THE JOIN.** For `P` a monic irreducible integer cubic and `P'` a monic irreducible integer
quartic with roots `a`, `b` in a field `E = ℚ(a, b)`: `[E : ℚ] = 12` and
`N_{E/ℚ}(ab) = c₀(P)⁴ · c₀(P')³`. -/
theorem norm_mul_eq_coeff_pow {E : Type*} [Field E] [Algebra ℚ E] {P P' : ℤ[X]}
    (hm : P.Monic) (hd : P.natDegree = 3) (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hm' : P'.Monic) (hd' : P'.natDegree = 4) (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : E} (ha : aeval a P = 0) (hb : aeval b P' = 0) (htop : ℚ⟮a, b⟯ = ⊤) :
    finrank ℚ E = 12 ∧
      Algebra.norm ℚ (a * b) = ((P.coeff 0 ^ 4 * P'.coeff 0 ^ 3 : ℤ) : ℚ) := by
  have hE : finrank ℚ E = 12 := by
    rw [← finrank_top', ← htop]
    exact finrank_adjoin_pair hm hd hirr hm' hd' hirr' ha hb
  exact ⟨hE, norm_mul_eq_coeff_pow_of_finrank hE hm hd hirr hm' hd' hirr' ha hb⟩

/-- In `ℤ`: `c⁴ · d³ = −1 ↔ (c = 1 ∨ c = −1) ∧ d = −1`. -/
theorem int_pow4_mul_pow3_eq_neg_one {c d : ℤ} :
    c ^ 4 * d ^ 3 = -1 ↔ (c = 1 ∨ c = -1) ∧ d = -1 := by
  constructor
  · intro h
    have hc4 : IsUnit (c ^ 4) := IsUnit.of_mul_eq_one (-(d ^ 3)) (by linear_combination -h)
    have hd3 : IsUnit (d ^ 3) := IsUnit.of_mul_eq_one (-(c ^ 4)) (by linear_combination -h)
    have hc : IsUnit c := (isUnit_pow_iff (by norm_num)).mp hc4
    have hd : IsUnit d := (isUnit_pow_iff (by norm_num)).mp hd3
    revert h
    rcases Int.isUnit_iff.mp hc with rfl | rfl <;> rcases Int.isUnit_iff.mp hd with rfl | rfl <;>
      norm_num
  · rintro ⟨rfl | rfl, rfl⟩ <;> norm_num

/-- **The iff.** Under the join's hypotheses, `N_{E/ℚ}(ab) = −1` exactly when the cubic's
constant term is `±1` and the quartic's is `−1`. -/
theorem norm_mul_eq_neg_one_iff {E : Type*} [Field E] [Algebra ℚ E] {P P' : ℤ[X]}
    (hm : P.Monic) (hd : P.natDegree = 3) (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hm' : P'.Monic) (hd' : P'.natDegree = 4) (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : E} (ha : aeval a P = 0) (hb : aeval b P' = 0) (htop : ℚ⟮a, b⟯ = ⊤) :
    Algebra.norm ℚ (a * b) = -1 ↔ (P.coeff 0 = 1 ∨ P.coeff 0 = -1) ∧ P'.coeff 0 = -1 := by
  rw [(norm_mul_eq_coeff_pow hm hd hirr hm' hd' hirr' ha hb htop).2,
    ← int_pow4_mul_pow3_eq_neg_one]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

/-- **The join to F:524's sets.** For monic irreducible integer `P` (cubic) and `P'` (quartic)
of height at most `H`, with roots `a`, `b` in `E = ℚ(a, b)`:
`P ∈ cubicUnits H ∧ P' ∈ quarticNormNeg H ↔ N_{E/ℚ}(ab) = −1`. -/
theorem mem_units_iff_norm_mul_eq_neg_one {E : Type*} [Field E] [Algebra ℚ E] {H : ℕ}
    {P P' : ℤ[X]}
    (hm : P.Monic) (hd : P.natDegree = 3) (hH : ∀ i, |P.coeff i| ≤ (H : ℤ))
    (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hm' : P'.Monic) (hd' : P'.natDegree = 4) (hH' : ∀ i, |P'.coeff i| ≤ (H : ℤ))
    (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : E} (ha : aeval a P = 0) (hb : aeval b P' = 0) (htop : ℚ⟮a, b⟯ = ⊤) :
    P ∈ cubicUnits H ∧ P' ∈ quarticNormNeg H ↔ Algebra.norm ℚ (a * b) = -1 := by
  rw [norm_mul_eq_neg_one_iff hm hd hirr hm' hd' hirr' ha hb htop]
  constructor
  · rintro ⟨⟨-, -, -, h0⟩, ⟨-, -, -, h0'⟩⟩
    exact ⟨h0, h0'⟩
  · rintro ⟨h0, h0'⟩
    exact ⟨⟨hm, hd, hH, h0⟩, ⟨hm', hd', hH', h0'⟩⟩

/-- Every irreducible member of `cubicUnits H × quarticNormNeg H`, with roots `a`, `b` in
`E = ℚ(a, b)`, gives `[E : ℚ] = 12` and `N_{E/ℚ}(ab) = −1`. -/
theorem norm_mul_eq_neg_one_of_mem {E : Type*} [Field E] [Algebra ℚ E] {H : ℕ} {P P' : ℤ[X]}
    (hP : P ∈ cubicUnits H) (hP' : P' ∈ quarticNormNeg H)
    (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : E} (ha : aeval a P = 0) (hb : aeval b P' = 0) (htop : ℚ⟮a, b⟯ = ⊤) :
    finrank ℚ E = 12 ∧ Algebra.norm ℚ (a * b) = -1 := by
  refine ⟨(norm_mul_eq_coeff_pow hP.1 hP.2.1 hirr hP'.1 hP'.2.1 hirr' ha hb htop).1, ?_⟩
  exact (mem_units_iff_norm_mul_eq_neg_one hP.1 hP.2.1 hP.2.2.1 hirr hP'.1 hP'.2.1 hP'.2.2.1
    hirr' ha hb htop).mp ⟨hP, hP'⟩

/-! ## Real-root form (F:524's own terms) -/

/-- `a` as an element of `ℚ⟮a, b⟯ ⊆ ℝ`. -/
theorem mem_adjoin_pair_left {E : Type*} [Field E] [Algebra ℚ E] (a b : E) : a ∈ ℚ⟮a, b⟯ :=
  subset_adjoin ℚ _ (Set.mem_insert a {b})

/-- `b` as an element of `ℚ⟮a, b⟯ ⊆ ℝ`. -/
theorem mem_adjoin_pair_right {E : Type*} [Field E] [Algebra ℚ E] (a b : E) : b ∈ ℚ⟮a, b⟯ :=
  subset_adjoin ℚ _ (Set.mem_insert_of_mem a (Set.mem_singleton b))

/-- The product `ab` lies in `ℚ⟮a, b⟯`: the element whose norm the real-root form takes. -/
theorem exists_mul_mem_adjoin_pair {E : Type*} [Field E] [Algebra ℚ E] (a b : E) :
    ∃ z : ℚ⟮a, b⟯, (z : E) = a * b :=
  ⟨⟨a * b, mul_mem (mem_adjoin_pair_left a b) (mem_adjoin_pair_right a b)⟩, rfl⟩

/-- A root in `E` of an integer polynomial is a root in any intermediate field containing it. -/
theorem aeval_sub_eq_zero {E : Type*} [Field E] [Algebra ℚ E] {K : IntermediateField ℚ E}
    {P : ℤ[X]} (a' : K) (ha : aeval (a' : E) P = 0) : aeval a' P = 0 := by
  apply (algebraMap K E).injective
  rw [← aeval_algebraMap_apply, map_zero]
  exact ha

/-- **THE JOIN, real-root form.** `a b : ℝ` roots of a monic irreducible integer cubic `P` and
quartic `P'`; the field `ℚ⟮a, b⟯ ⊆ ℝ` has degree 12 over `ℚ`, and the norm over it of the element
`ab` is `c₀(P)⁴ · c₀(P')³`. -/
theorem real_norm_mul_eq_coeff_pow {P P' : ℤ[X]}
    (hm : P.Monic) (hd : P.natDegree = 3) (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hm' : P'.Monic) (hd' : P'.natDegree = 4) (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : ℝ} (ha : aeval a P = 0) (hb : aeval b P' = 0) :
    finrank ℚ ℚ⟮a, b⟯ = 12 ∧ ∀ z : ℚ⟮a, b⟯, (z : ℝ) = a * b →
      Algebra.norm ℚ z = ((P.coeff 0 ^ 4 * P'.coeff 0 ^ 3 : ℤ) : ℚ) := by
  have hK := finrank_adjoin_pair hm hd hirr hm' hd' hirr' ha hb
  refine ⟨hK, fun z hz => ?_⟩
  let a' : ℚ⟮a, b⟯ := ⟨a, mem_adjoin_pair_left a b⟩
  let b' : ℚ⟮a, b⟯ := ⟨b, mem_adjoin_pair_right a b⟩
  have hz' : z = a' * b' := Subtype.ext hz
  rw [hz']
  exact norm_mul_eq_coeff_pow_of_finrank hK hm hd hirr hm' hd' hirr'
    (aeval_sub_eq_zero a' ha) (aeval_sub_eq_zero b' hb)

/-- **The join to F:524's sets, real-root form.** For monic irreducible integer `P` (cubic) and
`P'` (quartic) of height at most `H` with real roots `a`, `b`, and `z = ab` in `ℚ⟮a, b⟯`:
`P ∈ cubicUnits H ∧ P' ∈ quarticNormNeg H ↔ N_{ℚ(a,b)/ℚ}(ab) = −1`. -/
theorem real_mem_units_iff_norm_mul_eq_neg_one {H : ℕ} {P P' : ℤ[X]}
    (hm : P.Monic) (hd : P.natDegree = 3) (hH : ∀ i, |P.coeff i| ≤ (H : ℤ))
    (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hm' : P'.Monic) (hd' : P'.natDegree = 4) (hH' : ∀ i, |P'.coeff i| ≤ (H : ℤ))
    (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : ℝ} (ha : aeval a P = 0) (hb : aeval b P' = 0) (z : ℚ⟮a, b⟯) (hz : (z : ℝ) = a * b) :
    P ∈ cubicUnits H ∧ P' ∈ quarticNormNeg H ↔ Algebra.norm ℚ z = -1 := by
  rw [(real_norm_mul_eq_coeff_pow hm hd hirr hm' hd' hirr' ha hb).2 z hz]
  have key : ((P.coeff 0 ^ 4 * P'.coeff 0 ^ 3 : ℤ) : ℚ) = -1 ↔
      (P.coeff 0 = 1 ∨ P.coeff 0 = -1) ∧ P'.coeff 0 = -1 := by
    rw [← int_pow4_mul_pow3_eq_neg_one]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [key]
  constructor
  · rintro ⟨⟨-, -, -, h0⟩, ⟨-, -, -, h0'⟩⟩
    exact ⟨h0, h0'⟩
  · rintro ⟨h0, h0'⟩
    exact ⟨⟨hm, hd, hH, h0⟩, ⟨hm', hd', hH', h0'⟩⟩

/-- **Every irreducible member of `cubicUnits H × quarticNormNeg H`, real-root form**: for real
roots `a`, `b`, `[ℚ(a, b) : ℚ] = 12` and `N_{ℚ(a,b)/ℚ}(ab) = −1`. -/
theorem real_norm_mul_eq_neg_one_of_mem {H : ℕ} {P P' : ℤ[X]}
    (hP : P ∈ cubicUnits H) (hP' : P' ∈ quarticNormNeg H)
    (hirr : Irreducible (P.map (Int.castRingHom ℚ)))
    (hirr' : Irreducible (P'.map (Int.castRingHom ℚ)))
    {a b : ℝ} (ha : aeval a P = 0) (hb : aeval b P' = 0) :
    finrank ℚ ℚ⟮a, b⟯ = 12 ∧ ∀ z : ℚ⟮a, b⟯, (z : ℝ) = a * b → Algebra.norm ℚ z = -1 := by
  obtain ⟨hm, hd, hH, h0⟩ := hP
  obtain ⟨hm', hd', hH', h0'⟩ := hP'
  refine ⟨(real_norm_mul_eq_coeff_pow hm hd hirr hm' hd' hirr' ha hb).1, fun z hz => ?_⟩
  exact (real_mem_units_iff_norm_mul_eq_neg_one hm hd hH hirr hm' hd' hH' hirr' ha hb z hz).mp
    ⟨⟨hm, hd, hH, h0⟩, ⟨hm', hd', hH', h0'⟩⟩

end ExclusionRegion.NormBridge
