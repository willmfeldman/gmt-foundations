/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Distribution.DerivNotation

/-!
# Foundational setup

The ambient space, the surface measure on the unit sphere, and the normalized Hausdorff measure.

* `Rn n`, `sphereMeasure n`, `sphereIntegral f x r`, `unitBallVolume n`, `hausdorffN n d`.
* `E d` and `CompactlyContained A B`.

`E d` and `Rn d` are the same type, `EuclideanSpace ℝ (Fin d)`: both are `abbrev`s, so they are
reducibly equal and statements written with either are interchangeable. The Sobolev and BV files
use `E d`, the geometric measure theory files use `Rn n`. In statements with a binder
`E : Set (Rn n)`, the binder shadows the global `E`.

Sphere integrals are defined through Mathlib's `Measure.toSphere` of Lebesgue measure. That this
is `ℋ^{n-1}` restricted to the unit sphere is proved in `GMT/SphereMeasure.lean`.

Only the Mathlib modules this file needs are imported. The statements were checked to elaborate
to the same terms as under `import Mathlib`.
-/

@[expose] public noncomputable section

namespace GMTFoundations

section Space

open MeasureTheory Metric Set

/-- The Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The surface measure `σ` on the unit sphere `S^{n-1} ⊆ ℝⁿ`, i.e. Mathlib's `toSphere`
of Lebesgue measure. Its total mass is `n * |B_1|`. -/
def sphereMeasure (n : ℕ) : Measure (sphere (0 : Rn n) 1) :=
  (volume : Measure (Rn n)).toSphere

/-- The sphere integral `∫_{∂B_r(x)} f dℋ^{n-1} := r^{n-1} ∫_{S^{n-1}} f(x + r ω) dσ(ω)`. -/
def sphereIntegral {n : ℕ} (f : Rn n → ℝ) (x : Rn n) (r : ℝ) : ℝ :=
  r ^ (n - 1) * ∫ ω, f (x + r • (ω : Rn n)) ∂sphereMeasure n

/-- `|B_1|`, the Lebesgue measure of the unit ball of `ℝⁿ`. -/
def unitBallVolume (n : ℕ) : ℝ :=
  (volume (ball (0 : Rn n) 1)).toReal

/-- The normalized `d`-dimensional Hausdorff measure on `ℝⁿ`, `ℋ^d = (ω_d / 2^d) μH[d]`,
where `ω_d = |B_1 ⊆ ℝ^d|`. With this normalization `ℋ^n = ℒ^n` and `ℋ^{n-1}` restricted to a
hyperplane is `(n-1)`-dimensional Lebesgue measure (`GMT/HausdorffLebesgue.lean`). -/
def hausdorffN (n d : ℕ) : Measure (Rn n) :=
  ENNReal.ofReal (unitBallVolume d / 2 ^ d) • (Measure.hausdorffMeasure (d : ℝ))

end Space

section Domains

open Set Filter Topology
open scoped Gradient Laplacian

/-- The ambient Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

section CompactlyContained

variable {X : Type*} [TopologicalSpace X]

/-- `A ⊂⊂ B`: the closure of `A` is compact and contained in `B`. -/
def CompactlyContained (A B : Set X) : Prop := IsCompact (closure A) ∧ closure A ⊆ B

end CompactlyContained

end Domains

end GMTFoundations
