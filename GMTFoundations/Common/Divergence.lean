/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Calculus

/-!
# The divergence as a sum of partial derivatives

`GMTFoundations.divergence ξ x` is defined (`Defs/Calculus.lean`) as the trace of
`Dξ(x)`. This file computes the trace in the standard basis of `ℝⁿ`:

* `divergence_eq_sum`: `div ξ(x) = ∑ᵢ (Dξ(x) eᵢ)ᵢ`, with no differentiability assumption (both
  sides vanish where `ξ` is not differentiable).
* `fderiv_coord_apply`: at a point of differentiability, `D(ξᵢ)(x) v = (Dξ(x) v)ᵢ`.
* `divergence_eq_sum_fderiv_coord`: `div ξ(x) = ∑ᵢ ∂ᵢ ξᵢ(x)` at a point of differentiability.
-/

public section

namespace GMTFoundations

open MeasureTheory Metric Set

variable {n : ℕ}

/-- The divergence is the sum of the diagonal entries of `Dξ(x)` in the standard basis:
`div ξ(x) = ∑ᵢ (Dξ(x) eᵢ)ᵢ`. -/
theorem divergence_eq_sum (ξ : Rn n → Rn n) (x : Rn n) :
    divergence ξ x = ∑ i, fderiv ℝ ξ x (EuclideanSpace.single i 1) i := by
  rw [divergence, LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    Matrix.trace]
  simp [LinearMap.toMatrix_apply]

/-- The derivative of a coordinate of `ξ` is the coordinate of the derivative. -/
theorem fderiv_coord_apply {ξ : Rn n → Rn n} {x : Rn n} (h : DifferentiableAt ℝ ξ x)
    (i : Fin n) (v : Rn n) :
    fderiv ℝ (fun y => ξ y i) x v = fderiv ℝ ξ x v i := by
  have : ContinuousSMul ℝ (Rn n) := IsBoundedSMul.continuousSMul
  have := ((EuclideanSpace.proj i : Rn n →L[ℝ] ℝ).hasFDerivAt.comp x h.hasFDerivAt).fderiv
  simp only [EuclideanSpace.coe_proj, Function.comp_def] at this
  rw [this]
  simp

/-- **Divergence as a sum of partials**: `div ξ(x) = ∑ᵢ ∂ᵢ ξᵢ(x)` where `ξ` is differentiable. -/
theorem divergence_eq_sum_fderiv_coord {ξ : Rn n → Rn n} {x : Rn n}
    (h : DifferentiableAt ℝ ξ x) :
    divergence ξ x = ∑ i, fderiv ℝ (fun y => ξ y i) x (EuclideanSpace.single i 1) := by
  rw [divergence_eq_sum]
  exact Finset.sum_congr rfl fun i _ => (fderiv_coord_apply h i _).symm

end GMTFoundations
