/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Calculus
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Distribution.DerivNotation

/-!
# Weighted total variation

The (weighted) perimeter `∫_Ω η |∇χ|` is defined by duality:
`sup {∫_Ω χ div ψ : ψ ∈ C¹_c(Ω; ℝᵈ), |ψ| ≤ η}`. For `η = 1` this is the supremum in
Evans–Gariepy, Def. 5.1 (i).

* `weightedTV Ω η χ` on `ℝᵈ`, with admissible fields `IsTVTestField Ω η`.
* `totalVariationOn V χ = weightedTV V 1 χ`.
* `weightedTVₓ Ω η χ` on space-time `ℝᵈ × ℝ` with the *spatial* divergence `divₓ`, with admissible
  fields `IsTVTestFieldₓ Ω η`. The space-time operators `fderivₓ` and `divₓ` are used only by
  `weightedTVₓ`.

`divergence` is the one of `Defs/Calculus.lean`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
-/

@[expose] public noncomputable section

namespace GMTFoundations

section SpaceTime

open Set Filter Topology
open scoped Gradient Laplacian

variable {d : ℕ}

/-- Spatial derivative `D_xξ(x,t)` of a space-time vector field. -/
noncomputable def fderivₓ (ξ : E d × ℝ → E d) (p : E d × ℝ) : E d →L[ℝ] E d :=
  fderiv ℝ (fun y ↦ ξ (y, p.2)) p.1

/-- Spatial divergence `∇ₓ · ξ(x,t)` of a space-time vector field. -/
noncomputable def divₓ (ξ : E d × ℝ → E d) (p : E d × ℝ) : ℝ :=
  LinearMap.trace ℝ (E d) (fderivₓ ξ p).toLinearMap

end SpaceTime

open Set Filter Topology MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- Admissible test fields for `weightedTV Ω η`: `ψ ∈ C¹_c(Ω; ℝᵈ)` with `|ψ| ≤ η` pointwise. -/
def IsTVTestField (Ω : Set (E d)) (η : E d → ℝ) (ψ : E d → E d) : Prop :=
  ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω ∧ ∀ x, ‖ψ x‖ ≤ η x

/-- Weighted total variation `∫_Ω η |∇χ| := sup {∫_Ω χ div ψ : ψ ∈ C¹_c(Ω), |ψ| ≤ η}`. -/
noncomputable def weightedTV (Ω : Set (E d)) (η χ : E d → ℝ) : ℝ≥0∞ :=
  ⨆ (ψ : E d → E d) (_ : IsTVTestField Ω η ψ), ENNReal.ofReal (∫ x in Ω, χ x * divergence ψ x)

/-- Total variation `∫_V |∇χ|` of `χ` in `V` (`η = 1`). -/
noncomputable def totalVariationOn (V : Set (E d)) (χ : E d → ℝ) : ℝ≥0∞ :=
  weightedTV V 1 χ

/-- Admissible test fields for `weightedTVₓ Ω η`: `ψ ∈ C¹_c(Ω; ℝᵈ)` on space-time with
`|ψ| ≤ η` pointwise. -/
def IsTVTestFieldₓ (Ω : Set (E d × ℝ)) (η : E d × ℝ → ℝ) (ψ : E d × ℝ → E d) : Prop :=
  ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ω ∧ ∀ p, ‖ψ p‖ ≤ η p

/-- Space-time weighted total variation of `χ` in the *spatial* variables,
`∫_Ω η |∇ₓχ| dx dt := sup {∫_Ω χ divₓ ψ : ψ ∈ C¹_c(Ω; ℝᵈ), |ψ| ≤ η}`. -/
noncomputable def weightedTVₓ (Ω : Set (E d × ℝ)) (η χ : E d × ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (ψ : E d × ℝ → E d) (_ : IsTVTestFieldₓ Ω η ψ),
    ENNReal.ofReal (∫ p in Ω, χ p * divₓ ψ p)

end GMTFoundations
