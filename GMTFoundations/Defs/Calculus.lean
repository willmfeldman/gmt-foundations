/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Setup
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Distribution.DerivNotation
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Calculus vocabulary: divergence, test functions, test fields

* `divergence ξ x` is `tr (Dξ(x))`. At points where `ξ` is not differentiable Mathlib's `fderiv` is
  `0`, so the divergence is `0` there.
* `IsLipTestField Ω ξ` is the class `C^{0,1}_c(Ω; ℝⁿ)`.
* `IsSmoothTestField Ω ξ` is `C^∞_c(Ω; ℝⁿ)`.
* `IsTestFunction Ω φ` is `C^∞_c(Ω)`.

Smoothness is `ContDiff ℝ ∞` (with `open scoped ContDiff`); `⊤` would mean analytic.

The trace in `divergence` is taken of the coercion `(fderiv ℝ ξ x : Rn n →ₗ[ℝ] Rn n)`; this is the
same term as `LinearMap.trace ℝ (E d) (fderiv ℝ ξ x).toLinearMap`, so the same `divergence` also
serves the definitions of `Defs/BV.lean`, which are stated on `E d`.
-/

@[expose] public noncomputable section

namespace GMTFoundations

open MeasureTheory Metric Set Laplacian
open scoped ContDiff

variable {n : ℕ}

/-- The divergence `div ξ(x) = tr Dξ(x)` of a vector field `ξ : ℝⁿ → ℝⁿ`. It is `0` at points where
`ξ` is not differentiable, by Mathlib's convention for `fderiv`. -/
def divergence (ξ : Rn n → Rn n) (x : Rn n) : ℝ :=
  LinearMap.trace ℝ (Rn n) (fderiv ℝ ξ x : Rn n →ₗ[ℝ] Rn n)

/-- `ξ ∈ C^{0,1}_c(Ω; ℝⁿ)`: `ξ` is Lipschitz and has compact support contained in `Ω`. -/
def IsLipTestField (Ω : Set (Rn n)) (ξ : Rn n → Rn n) : Prop :=
  (∃ C, LipschitzWith C ξ) ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ Ω

/-- `ξ ∈ C^∞_c(Ω; ℝⁿ)`: `ξ` is smooth and has compact support contained in `Ω`. -/
def IsSmoothTestField (Ω : Set (Rn n)) (ξ : Rn n → Rn n) : Prop :=
  ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ Ω

/-- `φ ∈ C^∞_c(Ω)`: `φ` is smooth and has compact support contained in `Ω`. -/
def IsTestFunction (Ω : Set (Rn n)) (φ : Rn n → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

end GMTFoundations
