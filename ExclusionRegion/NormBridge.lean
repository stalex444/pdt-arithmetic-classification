module

public import Mathlib

/-!
# The norm bridge (general field theory)

For a field extension `E/K` and `x, y ∈ E`, the field norm of the product `xy` in terms of the
minimal polynomials of `x` and `y`. Mathlib only; no polynomial of this entry appears here.

* `norm_gen_eq_coeff_zero`, `norm_eq_coeff_zero_pow` : ported verbatim from F:519
  (NormRulerUnitPkg, `HeightT2.norm_gen_eq_coeff_zero`, `HeightT2.norm_eq_coeff_zero_pow`).
  `N_{K(x)/K}(x) = (−1)^deg · c₀` and `N_{E/K}(x) = ((−1)^deg · c₀)^[E : K(x)]`.
* `norm_mul_eq` : product form, meaningful for every FINITE extension (stated with no hypothesis;
  off the finite case both sides are Mathlib's conventional value 1):
  `N_{E/K}(xy) = N_{K(x)/K}(x)^[E : K(x)] · N_{K(y)/K}(y)^[E : K(y)]`.
* `norm_mul_eq_coeff` : the same with each sub-norm read off the minimal polynomial.
* `norm_mul_eq_coeff_div` : the same with the exponents `[E : K] / deg`.
* `linearDisjoint_of_coprime`, `finrank_sup_of_coprime` : WRAPPERS of Mathlib's
  `IntermediateField.LinearDisjoint.of_finrank_coprime` and `LinearDisjoint.finrank_sup`
  (coprime degrees give linear disjointness and the product degree). Not a new result.
* `norm_mul_of_linearDisjoint` : the disjoint form, `K(x) ⊔ K(y) = E`, linearly disjoint:
  `N_{E/K}(xy) = N_{K(x)/K}(x)^[K(y) : K] · N_{K(y)/K}(y)^[K(x) : K]`.
* `norm_mul_of_coprime` : the disjoint form with disjointness discharged by coprime degrees,
  in minimal-polynomial terms, together with `[E : K] = deg x · deg y`.
-/

@[expose] public section

namespace ExclusionRegion.NormBridge

open IntermediateField Polynomial Module

/-- (Port of F:519.) The norm of the generator of `K⟮x⟯` over `K` (degree `[K(x) : K]`). -/
theorem norm_gen_eq_coeff_zero {K E : Type*} [Field K] [Field E] [Algebra K E] (x : E)
    (hx : IsIntegral K x) :
    Algebra.norm K (AdjoinSimple.gen K x) =
      (-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0 := by
  rw [← adjoin.powerBasis_gen hx, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    adjoin.powerBasis_gen, minpoly_gen, adjoin.powerBasis_dim]

/-- (Port of F:519.) `N_{E/K}(x) = ((−1)^deg · c₀)^[E : K(x)]`, `c₀` the constant coefficient
of `minpoly K x`. -/
theorem norm_eq_coeff_zero_pow {K E : Type*} [Field K] [Field E] [Algebra K E] (x : E)
    (hx : IsIntegral K x) :
    Algebra.norm K x =
      ((-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^ Module.finrank K⟮x⟯ E := by
  rw [Algebra.norm_eq_norm_adjoin K x, norm_gen_eq_coeff_zero x hx]

/-- **Product form.** For every finite extension `E/K` and all `x, y ∈ E`:
`N_{E/K}(xy) = N_{K(x)/K}(x)^[E : K(x)] · N_{K(y)/K}(y)^[E : K(y)]`; no disjointness is needed.
The Lean statement carries no finiteness hypothesis, but off the finite case both sides are
Mathlib's conventional value 1 (`Algebra.norm` and `finrank` are junk there), so it says nothing
about infinite extensions. -/
theorem norm_mul_eq {K E : Type*} [Field K] [Field E] [Algebra K E] (x y : E) :
    Algebra.norm K (x * y) =
      Algebra.norm K (AdjoinSimple.gen K x) ^ finrank K⟮x⟯ E *
        Algebra.norm K (AdjoinSimple.gen K y) ^ finrank K⟮y⟯ E := by
  rw [map_mul, Algebra.norm_eq_norm_adjoin K x, Algebra.norm_eq_norm_adjoin K y]

/-- Product form, unconditional, with each sub-norm read off the minimal polynomial. -/
theorem norm_mul_eq_coeff {K E : Type*} [Field K] [Field E] [Algebra K E] (x y : E)
    (hx : IsIntegral K x) (hy : IsIntegral K y) :
    Algebra.norm K (x * y) =
      ((-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^ finrank K⟮x⟯ E *
        ((-1) ^ (minpoly K y).natDegree * (minpoly K y).coeff 0) ^ finrank K⟮y⟯ E := by
  rw [map_mul, norm_eq_coeff_zero_pow x hx, norm_eq_coeff_zero_pow y hy]

/-- `[E : K(x)] = [E : K] / deg(minpoly K x)` for integral `x` (tower law). -/
theorem finrank_adjoin_right_eq_div {K E : Type*} [Field K] [Field E] [Algebra K E] (x : E)
    (hx : IsIntegral K x) :
    finrank K⟮x⟯ E = finrank K E / (minpoly K x).natDegree := by
  rw [← Module.finrank_mul_finrank K K⟮x⟯ E, adjoin.finrank hx,
    Nat.mul_div_cancel_left _ (minpoly.natDegree_pos hx)]

/-- Product form, unconditional, with exponents `[E : K] / deg`. -/
theorem norm_mul_eq_coeff_div {K E : Type*} [Field K] [Field E] [Algebra K E] (x y : E)
    (hx : IsIntegral K x) (hy : IsIntegral K y) :
    Algebra.norm K (x * y) =
      ((-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^
          (finrank K E / (minpoly K x).natDegree) *
        ((-1) ^ (minpoly K y).natDegree * (minpoly K y).coeff 0) ^
          (finrank K E / (minpoly K y).natDegree) := by
  rw [norm_mul_eq_coeff x y hx hy, finrank_adjoin_right_eq_div x hx,
    finrank_adjoin_right_eq_div y hy]

/-- WRAPPER (Mathlib `IntermediateField.LinearDisjoint.of_finrank_coprime`): intermediate fields
of coprime degree are linearly disjoint. -/
theorem linearDisjoint_of_coprime {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (h : (finrank K A).Coprime (finrank K B)) :
    A.LinearDisjoint B :=
  LinearDisjoint.of_finrank_coprime h

/-- WRAPPER (Mathlib `LinearDisjoint.finrank_sup`): intermediate fields of coprime degree have
compositum of degree the product. -/
theorem finrank_sup_of_coprime {K E : Type*} [Field K] [Field E] [Algebra K E]
    {A B : IntermediateField K E} (h : (finrank K A).Coprime (finrank K B)) :
    finrank K ↥(A ⊔ B) = finrank K A * finrank K B :=
  (linearDisjoint_of_coprime h).finrank_sup

/-- **Product form, disjoint.** If `K(x)` and `K(y)` are linearly disjoint over `K` and
`K(x) ⊔ K(y) = E`, then `N_{E/K}(xy) = N_{K(x)/K}(x)^[K(y) : K] · N_{K(y)/K}(y)^[K(x) : K]`. -/
theorem norm_mul_of_linearDisjoint {K E : Type*} [Field K] [Field E] [Algebra K E] (x y : E)
    (hx : IsIntegral K x) (hy : IsIntegral K y) (hd : K⟮x⟯.LinearDisjoint K⟮y⟯)
    (hs : K⟮x⟯ ⊔ K⟮y⟯ = ⊤) :
    Algebra.norm K (x * y) =
      Algebra.norm K (AdjoinSimple.gen K x) ^ finrank K K⟮y⟯ *
        Algebra.norm K (AdjoinSimple.gen K y) ^ finrank K K⟮x⟯ := by
  have := adjoin.finiteDimensional hx
  have := adjoin.finiteDimensional hy
  rw [norm_mul_eq, hd.finrank_left_eq_finrank hs, hd.finrank_right_eq_finrank hs]

/-- **Product form, coprime degrees.** If `deg x` and `deg y` are coprime and
`K(x) ⊔ K(y) = E`, then `[E : K] = deg x · deg y` and
`N_{E/K}(xy) = ((−1)^{deg x} c₀(x))^{deg y} · ((−1)^{deg y} c₀(y))^{deg x}`. -/
theorem norm_mul_of_coprime {K E : Type*} [Field K] [Field E] [Algebra K E] (x y : E)
    (hx : IsIntegral K x) (hy : IsIntegral K y)
    (hc : (minpoly K x).natDegree.Coprime (minpoly K y).natDegree) (hs : K⟮x⟯ ⊔ K⟮y⟯ = ⊤) :
    finrank K E = (minpoly K x).natDegree * (minpoly K y).natDegree ∧
    Algebra.norm K (x * y) =
      ((-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0) ^ (minpoly K y).natDegree *
        ((-1) ^ (minpoly K y).natDegree * (minpoly K y).coeff 0) ^ (minpoly K x).natDegree := by
  have hd : K⟮x⟯.LinearDisjoint K⟮y⟯ :=
    linearDisjoint_of_coprime (by rwa [adjoin.finrank hx, adjoin.finrank hy])
  refine ⟨?_, ?_⟩
  · rw [← finrank_top', ← hs, hd.finrank_sup, adjoin.finrank hx, adjoin.finrank hy]
  · rw [norm_mul_of_linearDisjoint x y hx hy hd hs, norm_gen_eq_coeff_zero x hx,
      norm_gen_eq_coeff_zero y hy, adjoin.finrank hx, adjoin.finrank hy]

end ExclusionRegion.NormBridge
