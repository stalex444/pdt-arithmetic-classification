# Three gauge-coupling windows isolate the roots of x³ − x − 1 and x⁴ − x − 1 in bounded polynomial families

**Stephanie Alexander** · [ORCID 0009-0003-7727-2565](https://orcid.org/0009-0003-7727-2565)  
Dedicated to David N. Schramm (1945–1997).

Let ρ and Q be the real roots greater than one of x³ − x − 1 and x⁴ − x − 1, respectively. Consider an ordered pair of real algebraic integers (a,b) and a natural exponent p. Which triples satisfy three simultaneous inequalities motivated by the inverse fine-structure constant, the weak mixing angle and the strong coupling?

In each of two bounded families of monic integer polynomials, the **entire solution set is the singleton (ρ,Q,15)**. The same triple is the only solution for roots of irreducible monic cubics and quartics of height at most ten whose product has field norm −1. The height and the norm sign each matter. Raising the height to eleven admits a different quartic root with norm of the product still −1. At height ten a second quartic gives a passing pair with norm +1.

## The three inequalities

Write λ(x) = 1 − 1/x and ψ = b/a. The conditions are closed relative-error intervals. Each decimal below denotes an exact rational number.

| Expression | Centre | Relative half-width |
|---|---:|---:|
| (ab)ᵖ/π² | 137.036 | 0.5% |
| λ(b)/ψ³ | 0.23121 | 2% |
| λ(b)³/(4λ(a)³ψ²) | 0.1180 | 2% |

The classification ranges over every natural p, including zero. Lean uses its ordinary total real division. The two equivalences below imply that every passing triple in the stated families has both coordinates greater than one. The response to the three inequalities is the mathematical subject of the entry. Their interpretation as coupling formulas comes from Alexander’s physics paper.

## The four compared results

The **height** of a polynomial is the maximum of the absolute values of its coefficients. Let C(D,H) consist of monic integer polynomials of degree 2 through D, with height at most H and nonzero constant term. For the norm results, the field is always K = ℚ(a,b), and the sign refers to the field norm of ab from K to ℚ.

| Declaration in `ArithmeticClassification` | Statement |
|---|---|
| `cell_classification` | Choose C(4,3) or C(6,2). The set of triples (a,b,p) satisfying the windows, with each coordinate a real root of a witness polynomial from that same family, is exactly {(ρ,Q,15)}. Reducible witnesses are included. |
| `norm_classification` | Take a as a root of a monic integer cubic and b as a root of a monic integer quartic, both irreducible over ℚ, of height at most 10, with Nₖ/ℚ(ab) = −1. The passing triples in this class are precisely (ρ,Q,15). |
| `height_eleven_counterexample` | There exist roots in the same norm −1 class at height at most 11 satisfying all three windows at p = 15, with b⁴ ≠ b + 1. The construction keeps a = ρ and takes b between 1.22044 and 1.22045, a root of x⁴ + 7x³ − 11x² + 2x − 1. |
| `positive_norm_counterexample` | There exist roots of the same degrees at height at most 10, of product norm +1, satisfying all three windows at p = 15, with b⁴ ≠ b + 1. Here a = ρ and b lies between 1.22096 and 1.22097, a root of x⁴ + 10x³ − 7x² − 9x + 1. |

The equivalences identify **root values**. A value can have several admissible witness polynomials. The reverse implications put the distinguished triple in each family. The last two formal statements assert existence and failure of the quartic equation. Their proofs supply the displayed witness polynomials and intervals. The two competing quartic roots lie on opposite sides of Q ≈ 1.220744085. Sharpness at height ten concerns the irreducible cubic–quartic norm class. The two unrestricted cells have the specific degree and height bounds in the first row.

## How the proof works

1. **Localize every candidate.** The three inequalities first force p = 15 for real a,b and put a in [1.3231557, 1.3265140]. The natural-exponent condition excludes a second region allowed by the two rational expressions. This step is proved before any polynomial enumeration. [Gauge.lean](ExclusionRegion/Gauge.lean)
2. **Isolate two roots in succession.** A rational interval certificate checks all witness polynomials in the chosen family and forces a³ = a + 1. Substitution in the product inequality then confines b to [1.22032003, 1.22113387], where the second certificate forces b⁴ = b + 1. Certifying these two one-variable exclusions covers 2,394 polynomials in C(4,3) and 15,620 in C(6,2), without testing their Cartesian squares. [WindowCheck.lean](ExclusionRegion/WindowCheck.lean) · [Corollaries.lean](ExclusionRegion/Corollaries.lean) · [Cell62.lean](ExclusionRegion/Cell62.lean)
3. **Turn the norm into a finite coefficient condition.** The two irreducible degrees are coprime, so [K:ℚ] = 12. If P is the cubic and R the quartic, the tower law gives $N_{K/\mathbb Q}(ab)=P(0)^4R(0)^3$. Norm −1 forces P(0) = ±1 and R(0) = −1. One can then use separate interval certificates for the cubic and quartic families up to height ten. [NormBridgeJoin.lean](ExclusionRegion/NormBridgeJoin.lean) · [UnitPairs.lean](ExclusionRegion/UnitPairs.lean)
4. **Construct the boundary examples.** For each displayed quartic the proof establishes irreducibility, brackets a real root, verifies the three inequalities, and computes the product norm. The selected sign and height changes therefore give actual passing competitors. [Sharpness.lean](ExclusionRegion/Sharpness.lean)

## Mathematical context and provenance

For a researcher studying real algebraic integers of bounded height, the finite question is which other roots can enter a specified interval, and under which arithmetic restrictions. Borwein and Pinner study distances from a fixed algebraic number to roots of polynomials with coefficients in {−1,0,1}. Koleda studies how the number of real algebraic integers of fixed degree in an interval grows with the height bound. Here the output is an exact finite classification for a **pair** of coupled root intervals, including two witnesses for the limits of the norm restriction. These earlier results supply the mathematical context. [Borwein and Pinner, *Canadian Journal of Mathematics* (1997)](https://doi.org/10.4153/CJM-1997-047-3) · [Koleda, *Journal of Number Theory* (2020)](https://doi.org/10.1016/j.jnt.2019.09.017)

The formulas come from Table 2 of Alexander’s *Deriving Gravity from First Principles*. Her public companion program supplies the target decimals and the relative widths used here. Its finite numerical search used strict cutoffs. The Lean theorems use closed intervals, quantify over all natural exponents, and range over the polynomial families above. The experimental sources behind the three centres are CODATA 2022 for the inverse fine-structure constant, PDG 2022 for the MS-bar weak mixing angle at M_Z, and PDG 2024 for the strong coupling at M_Z. The widths define the arithmetic problem. [Paper](https://doi.org/10.5281/zenodo.20417378) · [Pinned companion program](https://github.com/stalex444/dimensional-origin-Newton/blob/18434bba7e2b8a1be63cddeb99b0fee90e5f38de/expanded_exclusion_test.py) · [CODATA](https://doi.org/10.1103/RevModPhys.97.025002) · [PDG 2022](https://pdg.lbl.gov/2022/reviews/rpp2022-rev-phys-constants.pdf) · [PDG 2024](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-phys-constants.pdf)

Alexander’s earlier formalizations establish uniqueness of the root above one of xⁿ = x + 1 for n ≥ 2, and give a unit certificate for ρQ and the degree of its compositum. The present comparison concerns which **other** roots can enter the three windows. Its methods build on standard field norms, interval arithmetic and certified root isolation. The package contains the substantive Lean proofs. Historical statement numbers in comments within the reused proof files refer to the earlier development. The four declarations selected for this entry are listed above. [Earlier root theorem](https://github.com/stalex444/golden-family-boundary/tree/fc43a62561b4d7846ca25273229a4f964dff7ae5) · [Earlier unit certificate](https://github.com/stalex444/mahler-minimizer-compositum/tree/84b364a5f98daefc1be387ae0aeb3d39866eca79) · [Milne, *Algebraic Number Theory*, Proposition 2.19](https://www.jmilne.org/math/CourseNotes/ANT.pdf) · [Certified real-root isolation in Isabelle/HOL](https://doi.org/10.1007/s10817-017-9424-6)

## Checking the entry

From this directory run `lake exe cache get` for the pinned Mathlib cache, then `lake build`. On a host with Palomar’s sandboxed Comparator available, run `lake comparator --config comparator.json`. The Challenge imports only Mathlib. Each of its four theorem bodies is a statement placeholder. The Solution supplies all four proofs and the configuration enables the independent NanoDa replay. [Challenge](Challenge.lean) · [Solution](Solution.lean) · [Comparator configuration](comparator.json) · [Registry metadata](formalization.yaml)

Local verification on 18 November 2026 used Lean 4.35.0-rc2 and Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The local Comparator accepted the selected Solution in NanoDa and in the Lean default kernel with the three permitted axioms recorded in its configuration. The Palomar submission checker at revision `14aa8d6b3c2f14a8540605e37144560b9a00e7e7` validated the metadata and inspected all 33 Lean source files.

The author directed the mathematical development. Anthropic Claude assisted with the original proofs. OpenAI Codex assembled this selection, proved the equivalence formulations from the existing results, and drafted the entry. The software is distributed under the MIT licence. [Licence](LICENSE)
