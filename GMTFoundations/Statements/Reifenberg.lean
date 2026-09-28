/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.GMT
public import Mathlib.Order.CompletePartialOrder

/-!
# Statements: Naber–Valtorta Reifenberg theorems in codimension one

Codimension-one (`k = n − 1`) cases of the Reifenberg-type theorems of Naber and Valtorta [NV].
All Reifenberg geometry in this library is specialized to hyperplanes: a plane is a pair `(p, ν)`
with `‖ν‖ = 1`.

* `DiscreteReifenbergStatement n`: [NV, Thm 3.4] with `ε_n = 0` ([NV, Remark 3.2]). Proved as
  `discrete_reifenberg` in `Reifenberg/Discrete.lean`, via Miśkiewicz's version [M, Thm 1.1]
  with `q = 2`, which does not require the square-function bound to be small, rather than via
  [NV, §5–6].
* `RectifiableReifenbergStatement n`: [NV, Thm 3.3], rectifiability part (2) only, with an added
  upper density bound (constant `C`, and `δ = δ(n, C)`). Proved as `rectifiable_reifenberg` in
  `Reifenberg/Rectifiable.lean`.

## Relation to the printed statements of [NV]

[NV, Def. 3.1] defines `D^k_μ(x, r) = inf_L r^{-(k+2)} ∫_{B_r(x)} d²(y, L) dμ` only when
`μ(B_r(x)) ≥ ε_n r^k`, and sets it to `0` otherwise. [NV, Remark 3.2] allows replacing `ε_n` by any
smaller bound, zero included. With `ε_n = 0`, `D^{n-1}_μ` is `jonesBetaSq μ` and the hypotheses are
required on *all* balls `B_r(x) ⊆ B_2`; this is stronger than [NV]'s hypothesis, which only
concerns balls of large measure. The discrete statement is for finite collections of balls. The
rectifiable statement additionally assumes `S` Borel and `ℋ^{n-1}(S) < ∞`, and it is weaker than
[NV, Thm 3.3] by design: it asserts rectifiability only, not the measure bound (3.8)
`λ^k(S ∩ B_r(x)) ≤ (1 + ε) ω_k r^k`, and it assumes the upper bound
`ℋ^{n-1}(S ∩ B_r(x)) ≤ C r^{n-1}` on every ball.

## Statement pattern

As in `Statements/Sobolev.lean`: `FooStatement n` is the `∀`-closure of the theorem over all its
binders except `n`. The `open scoped Classical in` line fixes the `Decidable` instance of the
filter `x j ∈ ball 0 1` in `DiscreteReifenbergStatement` to the classical one.

## References

* [NV] A. Naber, D. Valtorta, Rectifiable-Reifenberg and the regularity of stationary and
  minimizing harmonic maps, Ann. of Math. (2) 185 (2017), 131–227; arXiv:1504.02043.
* [M] M. Miśkiewicz, Discrete Reifenberg-type theorem, Ann. Acad. Sci. Fenn. Math. 43 (2018),
  3–19; arXiv:1612.02461.
-/

@[expose] public noncomputable section

namespace GMTFoundations

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

set_option linter.unusedVariables false in
open scoped Classical in
/-- **Discrete Reifenberg** ([NV, Thm 3.4], `k = n − 1`, `ε_n = 0` by [NV, Remark 3.2]). There
are `δ(n) > 0` and `D(n)` with the following property. Let `{B_{r_j}(x_j)}_{j ∈ J}` be a finite
collection of disjoint balls contained in `B_2`, and `μ = Σ_j ω_{n-1} r_j^{n-1} δ_{x_j}`. If for
every ball `B_s(y) ⊆ B_2`
`∫_{B_s(y)} ∫_0^s β²_μ(z, t) dt/t dμ(z) < δ² s^{n-1}`,
then `Σ_{x_j ∈ B_1} r_j^{n-1} < D`. Proved as `discrete_reifenberg`, via [M, Thm 1.1] with
`q = 2`. -/
def DiscreteReifenbergStatement (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n),
    ∃ δ : ℝ, 0 < δ ∧ ∃ D : ℝ, ∀ {ι : Type} (J : Finset ι) (x : ι → Rn n) (r : ι → ℝ),
      (∀ j ∈ J, 0 < r j) → (∀ j ∈ J, ball (x j) (r j) ⊆ ball 0 2) →
      (J : Set ι).Pairwise (fun i j => Disjoint (ball (x i) (r i)) (ball (x j) (r j))) →
      (∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball 0 2 →
        ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s,
            jonesBetaSq (∑ j ∈ J, ENNReal.ofReal (unitBallVolume (n - 1) * r j ^ (n - 1)) •
              Measure.dirac (x j)) z t / ENNReal.ofReal t)
          ∂(∑ j ∈ J, ENNReal.ofReal (unitBallVolume (n - 1) * r j ^ (n - 1)) •
              Measure.dirac (x j)) <
          ENNReal.ofReal (δ ^ 2 * s ^ (n - 1))) →
      ∑ j ∈ J with x j ∈ ball 0 1, r j ^ (n - 1) < D

set_option linter.unusedVariables false in
/-- **Rectifiable Reifenberg** ([NV, Thm 3.3 (2)], `k = n − 1`, `ε_n = 0` by [NV, Remark 3.2]),
rectifiability part only, under an upper density bound. For every `C` there is `δ(n, C) > 0` with
the following property. Let `S ⊆ B_2` be Borel with `ℋ^{n-1}(S) < ∞` and
`ℋ^{n-1}(S ∩ B_r(x)) ≤ C r^{n-1}` for every ball, and assume that for every ball `B_s(y) ⊆ B_2`
`∫_{S ∩ B_s(y)} ∫_0^s β²_{ℋ^{n-1}⌊S}(z, t) dt/t dℋ^{n-1}(z) < δ² s^{n-1}`.
Then `S ∩ B_1` is countably `ℋ^{n-1}`-rectifiable. Proved as `rectifiable_reifenberg`. -/
def RectifiableReifenbergStatement (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) (C : ℝ),
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Set (Rn n), MeasurableSet S → S ⊆ ball 0 2 →
      hausdorffN n (n - 1) S < ∞ →
      (∀ (x : Rn n) (r : ℝ), 0 < r →
        hausdorffN n (n - 1) (S ∩ ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) →
      (∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball 0 2 →
        ∫⁻ z in S ∩ ball y s, (∫⁻ t in Ioo 0 s,
            jonesBetaSq ((hausdorffN n (n - 1)).restrict S) z t / ENNReal.ofReal t)
          ∂hausdorffN n (n - 1) < ENNReal.ofReal (δ ^ 2 * s ^ (n - 1))) →
      IsCountablyRectifiable n (n - 1) (S ∩ ball 0 1)

end GMTFoundations
