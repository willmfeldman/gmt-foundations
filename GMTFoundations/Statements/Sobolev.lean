/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.GMT
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Statements: Rellich–Kondrachov with compact trace

* `RellichTraceStatement n`: Rellich–Kondrachov compactness with compact trace on the unit ball,
  for Lipschitz functions with bounded `H¹` norm (compare Evans–Gariepy, Thm 4.11 (compactness)
  and Thm 4.6 (traces)). Proved as `rellich_trace_weak_compactness` in
  `Sobolev/RellichTrace.lean`.

## Statement pattern

`FooStatement n` is the `∀`-closure of the theorem over all its binders except `n` and the
instance binders on `n`, which become parameters of the definition. Binder names, binder kinds
(explicit/implicit) and binder order are those of the theorem, so `theorem foo : FooStatement n`
is applied exactly like the unabbreviated theorem, e.g. `exact foo f C hLip hbd`. The hypothesis
binders are named (so that `intro` in the proof produces them); `linter.unusedVariables` is
switched off for these definitions because the names do not occur in the conclusions.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
-/

@[expose] public noncomputable section

namespace GMTFoundations

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

set_option linter.unusedVariables false in
/-- **Rellich–Kondrachov with compact trace** (compare Evans–Gariepy, Thms 4.11 and 4.6). Let
`f k` be Lipschitz on the closed unit ball with `∫_{B_1} (f_k² + |∇f_k|²) ≤ C`. Then along a
subsequence:
* `f_k → F` in `L²(B_1)`;
* the traces `f_k|_{∂B_1} → F_tr` in `L²(∂B_1)`;
* `∇f_k ⇀ G` weakly in `L²(B_1; ℝⁿ)`;
* `G` is the weak gradient of `F`: `∫ F div ψ = −∫ ⟪G, ψ⟫` for `ψ ∈ C^∞_c(B_1; ℝⁿ)`.

The limit trace `F_tr` is the trace of `F`; that relation is not part of the statement. No trace
operator on `W^{1,2}` is built: the proof combines local Rellich compactness on the open ball with
a ray estimate near the sphere (giving a Cauchy sequence in `L²(B_1)`) and a trace inequality for
Lipschitz functions along rays (giving a Cauchy sequence in `L²(∂B_1)`). Proved as
`rellich_trace_weak_compactness`. -/
def RellichTraceStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ (f : ℕ → Rn n → ℝ) (C : ℝ)
    (hLip : ∀ k, ∃ L, LipschitzOnWith L (f k) (closedBall 0 1))
    (hbd : ∀ k, ∫ y in ball (0 : Rn n) 1, (f k y ^ 2 + ‖gradient (f k) y‖ ^ 2) ≤ C),
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (F : Rn n → ℝ) (Ftr : sphere (0 : Rn n) 1 → ℝ)
      (G : Rn n → Rn n),
      MemLp F 2 (volume.restrict (ball 0 1)) ∧ MemLp Ftr 2 (sphereMeasure n) ∧
      MemLp G 2 (volume.restrict (ball 0 1)) ∧
      Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, (f (φ k) y - F y) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ ω, (f (φ k) (ω : Rn n) - Ftr ω) ^ 2 ∂sphereMeasure n) atTop (𝓝 0) ∧
      (∀ h : Rn n → Rn n, MemLp h 2 (volume.restrict (ball 0 1)) →
        Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, ⟪gradient (f (φ k)) y, h y⟫) atTop
          (𝓝 (∫ y in ball (0 : Rn n) 1, ⟪G y, h y⟫))) ∧
      (∀ ψ : Rn n → Rn n, IsSmoothTestField (ball 0 1) ψ →
        ∫ y in ball (0 : Rn n) 1, F y * divergence ψ y =
          -∫ y in ball (0 : Rn n) 1, ⟪G y, ψ y⟫)

end GMTFoundations
