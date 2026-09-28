import Mathlib

/-!
# Trusted statement: Rellich–Kondrachov compactness with compact boundary trace

This file imports Mathlib only. It is the complete trusted surface of the `rellich-trace`
challenge: `Challenge.lean` and `Solution.lean` both state `GMTChallenge.RellichTraceClaim`.

`RellichTraceClaim n` says: a sequence of functions that are Lipschitz on the closed unit ball
`B̄₁ ⊆ ℝⁿ` and bounded in `H¹(B₁)` has a subsequence that converges strongly in `L²(B₁)`, whose
boundary values converge strongly in `L²(∂B₁)`, and whose gradients converge weakly in
`L²(B₁; ℝⁿ)` to the weak gradient of the `L²` limit.

This combines Rellich–Kondrachov compactness (L. C. Evans and R. F. Gariepy, *Measure Theory and
Fine Properties of Functions*, revised edition, CRC Press, 2015, Theorem 4.11) with compactness of
the boundary trace (for traces see ibid., Theorem 4.6), for Lipschitz functions on the unit ball.

Vocabulary, all from Mathlib:
* `gradient` is Mathlib's gradient (defined through `fderiv`, and `0` where `f` is not
  differentiable). A function Lipschitz on `B̄₁` is differentiable a.e. in `B₁` (Rademacher), so
  it is the a.e. gradient.
* `sphereMeasure n` is Mathlib's surface measure on the unit sphere, `volume.toSphere`
  (normalized so that its total mass is `n |B₁|`).
* the weak gradient is expressed by integration by parts against smooth compactly supported
  vector fields.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace GMTChallenge

/-- The Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The surface measure `σ` on the unit sphere `S^{n-1} ⊆ ℝⁿ` (Mathlib's `Measure.toSphere`). -/
def sphereMeasure (n : ℕ) : Measure (sphere (0 : Rn n) 1) :=
  (volume : Measure (Rn n)).toSphere

/-- The divergence `div ξ(x) = tr Dξ(x)` of a vector field `ξ : ℝⁿ → ℝⁿ`. -/
def divergence {n : ℕ} (ξ : Rn n → Rn n) (x : Rn n) : ℝ :=
  LinearMap.trace ℝ (Rn n) (fderiv ℝ ξ x : Rn n →ₗ[ℝ] Rn n)

/-- `ξ ∈ C^∞_c(Ω; ℝⁿ)`: `ξ` is smooth and has compact support contained in `Ω`. -/
def IsSmoothTestField {n : ℕ} (Ω : Set (Rn n)) (ξ : Rn n → Rn n) : Prop :=
  ContDiff ℝ ∞ ξ ∧ HasCompactSupport ξ ∧ tsupport ξ ⊆ Ω

/-- Rellich–Kondrachov compactness with compact trace on the unit ball of `ℝⁿ`, `n ≥ 1`.

If each `f k` is Lipschitz on `B̄₁` and `∫_{B₁} (f_k² + |∇f_k|²) ≤ C`, then along a subsequence
`φ`: `f_{φ k} → F` in `L²(B₁)`; `f_{φ k}|_{∂B₁} → F_tr` in `L²(∂B₁)`; `∇f_{φ k} ⇀ G` weakly in
`L²(B₁; ℝⁿ)`; and `G` is the weak gradient of `F` in `B₁`. -/
def RellichTraceClaim (n : ℕ) [NeZero n] : Prop :=
  ∀ (f : ℕ → Rn n → ℝ) (C : ℝ),
    (∀ k, ∃ L, LipschitzOnWith L (f k) (closedBall 0 1)) →
    (∀ k, ∫ y in ball (0 : Rn n) 1, (f k y ^ 2 + ‖gradient (f k) y‖ ^ 2) ≤ C) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (F : Rn n → ℝ) (Ftr : sphere (0 : Rn n) 1 → ℝ)
      (G : Rn n → Rn n),
      MemLp F 2 (volume.restrict (ball 0 1)) ∧ MemLp Ftr 2 (sphereMeasure n) ∧
      MemLp G 2 (volume.restrict (ball 0 1)) ∧
      Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, (f (φ k) y - F y) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ p, (f (φ k) (p : Rn n) - Ftr p) ^ 2 ∂sphereMeasure n) atTop (𝓝 0) ∧
      (∀ h : Rn n → Rn n, MemLp h 2 (volume.restrict (ball 0 1)) →
        Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, ⟪gradient (f (φ k)) y, h y⟫) atTop
          (𝓝 (∫ y in ball (0 : Rn n) 1, ⟪G y, h y⟫))) ∧
      (∀ ψ : Rn n → Rn n, IsSmoothTestField (ball 0 1) ψ →
        ∫ y in ball (0 : Rn n) 1, F y * divergence ψ y =
          -∫ y in ball (0 : Rn n) 1, ⟪G y, ψ y⟫)

end GMTChallenge
