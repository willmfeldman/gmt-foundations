/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.GMT

/-!
# Statements: sets of locally finite perimeter

Six headline statements about Gauss–Green pairs and sets of locally finite perimeter. Each is
proved in `Perimeter/*` as `theorem foo : FooStatement n`.

* `GaussGreenPairOfDivergenceBoundStatement`: a divergence bound gives a Gauss–Green pair
  (Evans–Gariepy, Thm 5.1). Proved as `exists_isGaussGreenPair_of_integral_divergence_le` in
  `Perimeter/GaussGreenPair.lean`.
* `LocallyFinitePerimeterOfLocalStatement`: local divergence bounds give a Gauss–Green pair on the
  whole open set (Evans–Gariepy, Thm 5.1 for `BV_loc`). Proved as
  `hasLocallyFinitePerimeter_of_local` in `Perimeter/Local.lean`.
* `HalfSpaceBlowUpStatement`: blow-up at reduced-boundary points (Evans–Gariepy, Thms 5.13, 5.14).
  Proved as `hasDensity_symmDiff_halfSpace` in `Perimeter/BlowUp.lean`.
* `RectifiableEssentialBoundaryStatement`: the essential boundary is countably
  `ℋ^{n-1}`-rectifiable and agrees with the reduced boundary up to an `ℋ^{n-1}`-null set
  (Evans–Gariepy, Thm 5.15 (i), Lemma 5.5). Proved as
  `HasLocallyFinitePerimeter.rectifiable_essentialBoundary` in `Perimeter/Structure.lean`.
* `GaussGreenMeasureEqHausdorffStatement`: the Gauss–Green measure is `ℋ^{n-1}` restricted to the
  essential boundary (Evans–Gariepy, Thms 5.15 (iii), 5.16). Proved as
  `IsGaussGreenPair.eq_hausdorffN_restrict` in `Perimeter/Structure.lean`.
* `TrivialOfNullEssentialBoundaryStatement`: a set whose essential boundary is `ℋ^{n-1}`-null in a
  ball is a.e. empty or a.e. full there (the null case of Evans–Gariepy, Thm 5.23). Proved as
  `ae_trivial_of_hausdorffN_essentialBoundary_inter_ball` in `Perimeter/Criterion.lean`.

Balls. Evans–Gariepy use closed balls `B(x, r)`; the definitions here (`reducedBoundary`,
`HasDensity`, the hypotheses below) use open balls `ball x r`. The limits involved are the same;
the bridge lemmas are proved in `Perimeter/`.

## Statement pattern

As in `Statements/Sobolev.lean`: `FooStatement n` is the `∀`-closure of the theorem over all its
binders except the dimension `n`. Unused binder names (such as `hn`) are kept, so the statement
reads like the theorem it abbreviates.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
* H. Federer, *Geometric Measure Theory*, Grundlehren der mathematischen Wissenschaften 153,
  Springer, 1969.
-/

@[expose] public noncomputable section

namespace GMTFoundations

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

set_option linter.unusedVariables false in
/-- **Gauss–Green pair from a divergence bound** (BV structure theorem). Let `E` be measurable
and `U` open. If `|∫_E div φ| ≤ C sup|φ|` for every `φ ∈ C^∞_c(U; ℝⁿ)`, then `E` has a Gauss–Green
pair in `U` with total mass `≤ C`. This is the Riesz representation of the vector distribution
`Dχ_E` (Evans–Gariepy, Thm 5.1). Proved as `exists_isGaussGreenPair_of_integral_divergence_le`. -/
def GaussGreenPairOfDivergenceBoundStatement (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) {U E : Set (Rn n)}
    (hU : IsOpen U) (hE : MeasurableSet E) (C : ℝ)
    (h : ∀ φ : Rn n → Rn n, IsSmoothTestField U φ →
      |∫ x in E, divergence φ x| ≤ C * ⨆ x, ‖φ x‖),
    ∃ μ ν, IsGaussGreenPair U E μ ν ∧ μ U ≤ ENNReal.ofReal C

set_option linter.unusedVariables false in
/-- **Local finite perimeter** (BV structure theorem, `BV_loc` form). If a measurable `E`
satisfies, near each point of the open set `U`, a bound `|∫_E div φ| ≤ C sup|φ|` for
`φ ∈ C^∞_c(B_r(x); ℝⁿ)`, then `E` has a Gauss–Green pair on all of `U`. This is Evans–Gariepy,
Thm 5.1, as stated there, for `χ_E ∈ BV_loc(U)`: a local bound near each point is equivalent to a
bound on every `V ⋐ U` (finite cover and a partition of unity). Proved as
`hasLocallyFinitePerimeter_of_local`. -/
def LocallyFinitePerimeterOfLocalStatement (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) {U E : Set (Rn n)} (hU : IsOpen U)
    (hE : MeasurableSet E)
    (h : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ C : ℝ, ∀ φ : Rn n → Rn n,
      IsSmoothTestField (ball x r) φ → |∫ y in E, divergence φ y| ≤ C * ⨆ y, ‖φ y‖),
    HasLocallyFinitePerimeter U E

set_option linter.unusedVariables false in
/-- **De Giorgi's blow-up theorem** at reduced-boundary points. Let `(μ, ν)` be a Gauss–Green
pair for `E` in `Ω` and let `x ∈ Ω` be a point of `supp μ` at which the averages of the outer
normal `ν` converge to a unit vector `v` (so `x ∈ ∂*E`). Then the blow-ups `(E − x)/r` converge in
`L¹_loc` to the half-space `{⟪z, v⟫ < 0}`: `E △ {y : ⟪y − x, v⟫ < 0}` has density `0` at `x`.
Evans–Gariepy, Thm 5.13 and Thm 5.14 (i), (ii), with open instead of closed balls. (The hypothesis
`2 ≤ n` is extra.) Proved as `hasDensity_symmDiff_halfSpace`. -/
def HalfSpaceBlowUpStatement (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) {Ω E : Set (Rn n)} (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν)
    {x : Rn n} (hx : x ∈ Ω) (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)),
    HasDensity (symmDiff E {y | ⟪y - x, v⟫ < 0}) x 0

set_option linter.unusedVariables false in
/-- **Rectifiability of the essential boundary** (De Giorgi–Federer). For a measurable set of
locally finite perimeter in `Ω`: the essential boundary in `Ω` is countably `ℋ^{n-1}`-rectifiable,
it differs from the reduced boundary by an `ℋ^{n-1}`-null set, and the reduced boundary is
contained in it (points of `∂*E` have density `1/2`). Evans–Gariepy, Thm 5.15 (i) and Lemma 5.5.

The proof follows steps 1–3 of the proof of Evans–Gariepy, Thm 5.15 (Egorov, Lusin and a cone
condition on compact pieces of `∂*E`). It replaces step 4 (Whitney extension and the implicit
function theorem) by: the cone condition makes each piece a Lipschitz graph over `ν(x)^⊥`, and a
McShane extension gives a Lipschitz map `ℝ^{n-1} → ℝⁿ`. Proved as
`HasLocallyFinitePerimeter.rectifiable_essentialBoundary`. -/
def RectifiableEssentialBoundaryStatement (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n)
    {Ω E : Set (Rn n)} (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : HasLocallyFinitePerimeter Ω E),
    IsCountablyRectifiable n (n - 1) (Ω ∩ essentialBoundary E) ∧
      hausdorffN n (n - 1) ((Ω ∩ essentialBoundary E) \ reducedBoundary Ω E) = 0 ∧
      reducedBoundary Ω E ⊆ essentialBoundary E

set_option linter.unusedVariables false in
/-- **The Gauss–Green measure is `ℋ^{n-1}` on the essential boundary.** The Gauss–Green measure
of a set of locally finite perimeter is `ℋ^{n-1}` restricted to the essential boundary:
`|Dχ_E|⌊Ω = ℋ^{n-1}⌊(∂ᵉE ∩ Ω)`. Evans–Gariepy, Thm 5.15 (iii), Lemma 5.5 (ii) and Thm 5.16.

Evans–Gariepy's step 5 of Thm 5.15 uses that a `C¹` hypersurface has density `1`. Here that step
is replaced by the density theorem for countably rectifiable sets (`GMT/Density.lean`) and
Besicovitch differentiation, so no area formula is needed. Proved as
`IsGaussGreenPair.eq_hausdorffN_restrict`. -/
def GaussGreenMeasureEqHausdorffStatement (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) {Ω E : Set (Rn n)}
    {μ : Measure (Rn n)} {ν : Rn n → Rn n} (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : IsGaussGreenPair Ω E μ ν),
    μ = (hausdorffN n (n - 1)).restrict (Ω ∩ essentialBoundary E)

set_option linter.unusedVariables false in
/-- **Null essential boundary implies triviality.** If the essential boundary of a measurable set
`E` is `ℋ^{n-1}`-null in a ball, then `E` is Lebesgue-a.e. empty or a.e. full in that ball.
Compare Federer's criterion (an `ℋ^{n-1}`-finite essential boundary gives locally finite
perimeter) and Evans–Gariepy, Thm 5.23.

The proof uses only the null case of Evans–Gariepy, Thm 5.23: the argument of its proof
(Claims #1 and #2), with the counting function `N(P | U ∩ ∂_*E, ·)` identically `0`, shows that
`∫_E div φ = 0` for every `φ ∈ C¹_c(B; ℝⁿ)`, i.e. `Dχ_E = 0` in the ball `B`. The argument is run
on the ball directly instead of on a cube (every line meets a convex set in an interval). So
`(0, 0)` is a Gauss–Green pair for `E` in `B`, and the relative isoperimetric inequality
in the form `min(|E ∩ B_r|, |B_r \ E|) ≤ C r |∂E|(B_r)` (compare Evans–Gariepy, Thm 5.11 (ii))
gives triviality. Proved as `ae_trivial_of_hausdorffN_essentialBoundary_inter_ball`. -/
def TrivialOfNullEssentialBoundaryStatement (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) {E : Set (Rn n)}
    (hE : MeasurableSet E) {c : Rn n} {r : ℝ}
    (h : hausdorffN n (n - 1) (essentialBoundary E ∩ ball c r) = 0),
    volume (E ∩ ball c r) = 0 ∨ volume (ball c r \ E) = 0

end GMTFoundations
