/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Calculus

/-!
# Geometric measure theory vocabulary

* `IsCountablyRectifiable n k S`: `S` is countably `ℋ^k`-rectifiable. Up to an
  `ℋ^k`-null set, `S` is covered by countably many Lipschitz images of `ℝ^k`.
* `IsGaussGreenPair Ω E μ ν`: `μ` is a Radon measure on `Ω` and `ν` a `μ`-a.e. unit vector field
  with `∫_E div φ = ∫ φ · ν dμ` for all `φ ∈ C^∞_c(Ω; ℝⁿ)`. By De Giorgi's structure theory
  `μ = |Dχ_E|⌊Ω` and `ν` is the measure-theoretic outer normal (Evans–Gariepy, Thm 5.1); moreover
  `μ = ℋ^{n-1}⌊(∂ᵉE ∩ Ω)` for measurable `E`, open `Ω` and `n ≥ 2`
  (`IsGaussGreenPair.eq_hausdorffN_restrict`).
* `HasLocallyFinitePerimeter Ω E`: a Gauss–Green pair exists.
* `reducedBoundary Ω E = ∂*E ∩ Ω` (De Giorgi; Evans–Gariepy, Def. 5.4).
* `HasDensity E x d`: `E` has Lebesgue density `d` at `x`.
* `essentialBoundary E = ∂ᵉE` (Federer's measure-theoretic boundary `∂_M E`; written
  `∂_* E` in Evans–Gariepy, Def. 5.7).
* `jonesBetaSq μ x r = β²_μ(x, r)`: the squared `L²` Jones number with respect to affine
  hyperplanes, normalized by `r^{n-1}` (codimension one).

## Remarks on faithfulness

* Lipschitz images of all of `ℝ^k` rather than of bounded subsets: each Lipschitz map on a subset
  of `ℝ^k` extends to a Lipschitz map on `ℝ^k` (McShane, componentwise), so the notions agree.
* The Gauss–Green pair is unique when it exists. The distribution `Dχ_E` determines the vector
  measure `ν μ` on `Ω`, and then `μ = |ν μ|` because `‖ν‖ = 1` `μ`-a.e. So `reducedBoundary` does
  not depend on which pair witnesses it. (The uniqueness lemma is `IsGaussGreenPair.unique`, in
  `Perimeter/GaussGreenPair/API.lean`.)
* `essentialBoundary`: Federer's `∂_M E` is the set of points where both `E` and `ℝⁿ \ E` have
  positive upper density. For measurable `E` the density ratios lie in `[0, 1]` and add up to one.
  So "upper density of `E` is `0`" is `HasDensity E x 0`, and "upper density of the complement is
  `0`" is `HasDensity E x 1`. Hence `x ∉ ∂_M E ⟺ HasDensity E x 0 ∨ HasDensity E x 1`.
* The definitions use open balls `ball x r`; Evans–Gariepy, and Mathlib's differentiation
  theorems, use closed balls. The resulting notions agree; the bridge lemmas are in `Perimeter/`.
* `jonesBetaSq` takes the infimum over affine hyperplanes `L = {y : ⟪y − p, ν⟫ = 0}`, `‖ν‖ = 1`,
  for which `dist(y, L) = |⟪y − p, ν⟫|`. It is valued in `ℝ≥0∞`. It is the codimension-one case
  of the displacement `D^k_μ` of Naber–Valtorta, Def. 3.1, with `ε_n = 0` (see
  `Statements/Reifenberg.lean`).

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
* H. Federer, *Geometric Measure Theory*, Grundlehren der mathematischen Wissenschaften 153,
  Springer, 1969.
* A. Naber, D. Valtorta, Rectifiable-Reifenberg and the regularity of stationary and minimizing
  harmonic maps, Ann. of Math. (2) 185 (2017), 131–227; arXiv:1504.02043.
-/

@[expose] public noncomputable section

namespace GMTFoundations

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

/-- `S ⊆ ℝⁿ` is countably `ℋ^k`-rectifiable: up to an `ℋ^k`-null set it is contained in a countable
union of Lipschitz images of `ℝ^k`. -/
def IsCountablyRectifiable (n k : ℕ) (S : Set (Rn n)) : Prop :=
  ∃ f : ℕ → Rn k → Rn n, (∀ i, ∃ C, LipschitzWith C (f i)) ∧
    hausdorffN n k (S \ ⋃ i, range (f i)) = 0

/-- A Gauss–Green pair for `E` in `Ω`. `μ` is a Radon measure concentrated on `Ω`, `ν` is a
measurable `μ`-a.e. unit vector field, and the Gauss–Green formula
`∫_E div φ = ∫ ⟪φ, ν⟫ dμ` holds for every `φ ∈ C^∞_c(Ω; ℝⁿ)`.
When it exists, `μ = |Dχ_E|⌊Ω` and `ν` is the outer normal. -/
structure IsGaussGreenPair (Ω E : Set (Rn n)) (μ : Measure (Rn n)) (ν : Rn n → Rn n) : Prop where
  /-- `μ` is concentrated on `Ω`. -/
  measure_compl : μ Ωᶜ = 0
  /-- `μ` is finite on compact subsets of `Ω`. -/
  lt_top_of_isCompact : ∀ K, IsCompact K → K ⊆ Ω → μ K < ∞
  /-- `ν` is measurable. -/
  measurable_normal : Measurable ν
  /-- `ν` is a unit vector `μ`-a.e. -/
  norm_normal : ∀ᵐ x ∂μ, ‖ν x‖ = 1
  /-- The Gauss–Green formula. -/
  integral_divergence : ∀ φ : Rn n → Rn n, IsSmoothTestField Ω φ →
    ∫ x in E, divergence φ x = ∫ x, ⟪φ x, ν x⟫ ∂μ

/-- `E` has locally finite perimeter in `Ω`: a Gauss–Green pair exists. -/
def HasLocallyFinitePerimeter (Ω E : Set (Rn n)) : Prop :=
  ∃ μ ν, IsGaussGreenPair Ω E μ ν

/-- The reduced boundary `∂*E ∩ Ω` (De Giorgi; Evans–Gariepy, Def. 5.4): the points `x ∈ Ω` of
`supp |Dχ_E|` at which the averages `⨍_{B_r(x)} ν d|Dχ_E|` converge, as `r → 0+`, to a unit vector.
The Gauss–Green pair is unique when it exists (module docstring), so the existential quantifier
does not affect the definition. -/
def reducedBoundary (Ω E : Set (Rn n)) : Set (Rn n) :=
  {x | x ∈ Ω ∧ ∃ μ ν, IsGaussGreenPair Ω E μ ν ∧ (∀ r, 0 < r → 0 < μ (ball x r)) ∧
    ∃ v : Rn n, ‖v‖ = 1 ∧
      Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0) (𝓝 v)}

/-- `E` has Lebesgue density `d` at `x`:
`|E ∩ B_r(x)| / |B_r(x)| → d` as `r → 0+`. -/
def HasDensity (E : Set (Rn n)) (x : Rn n) (d : ℝ) : Prop :=
  Tendsto (fun r => (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal) (𝓝[>] 0) (𝓝 d)

/-- The essential (measure-theoretic) boundary `∂ᵉE`: the points at which `E` has neither density
`0` nor density `1` (Federer's `∂_M E`; see the module docstring). -/
def essentialBoundary (E : Set (Rn n)) : Set (Rn n) :=
  {x | ¬ HasDensity E x 0 ∧ ¬ HasDensity E x 1}

/-- The squared Jones number
`β²_μ(x, r) = inf_L ∫_{B_r(x)} dist(y, L)² / r² dμ(y) / r^{n-1}`,
where the infimum ranges over affine hyperplanes `L = {y : ⟪y − p, ν⟫ = 0}`, `‖ν‖ = 1`. -/
def jonesBetaSq (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) : ℝ≥0∞ :=
  ⨅ (p : Rn n) (ν : Rn n) (_ : ‖ν‖ = 1),
    (∫⁻ y in ball x r, ENNReal.ofReal (⟪y - p, ν⟫ ^ 2 / r ^ 2) ∂μ) / ENNReal.ofReal (r ^ (n - 1))

end GMTFoundations
