/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Setup

/-!
# Minimal Sobolev notions

* `HasWeakGradient U u G`, `MemH1 U u G`, `MemH1Loc U u G`: the weak gradient is carried as
  explicit data `G`, with `p = 2`. There is no `W^{1,p}` space type.
* `TendstoLpLoc` (strong `L^p_loc` convergence) and `TendstoWeakL2` (weak `L²` convergence).
-/

@[expose] public noncomputable section

namespace GMTFoundations

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff

variable {d : ℕ}

/-- `G` is a weak gradient of `u` in the open set `U`: `u` and `G` are locally
integrable on `U` and `∫_U u ∂_v φ = - ∫_U (G · v) φ` for every `φ ∈ C_c^∞(U)` and direction `v`. -/
def HasWeakGradient (U : Set (E d)) (u : E d → ℝ) (G : E d → E d) : Prop :=
  LocallyIntegrableOn u U ∧ LocallyIntegrableOn G U ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : E d,
      ∫ x in U, u x * fderiv ℝ φ x v = -∫ x in U, inner ℝ (G x) v * φ x

/-- `u ∈ H¹(U)` with weak gradient `G`: `u, G ∈ L²(U)` and `G` is a weak gradient of
`u` in `U`. -/
def MemH1 (U : Set (E d)) (u : E d → ℝ) (G : E d → E d) : Prop :=
  MemLp u 2 (volume.restrict U) ∧ MemLp G 2 (volume.restrict U) ∧ HasWeakGradient U u G

/-- `u ∈ H¹_loc(U)` with weak gradient `G`: `G` is a weak gradient of `u` in `U`
and `u, G ∈ L²(K)` for every compact `K ⊆ U`. -/
def MemH1Loc (U : Set (E d)) (u : E d → ℝ) (G : E d → E d) : Prop :=
  HasWeakGradient U u G ∧ ∀ K ⊆ U, IsCompact K →
    MemLp u 2 (volume.restrict K) ∧ MemLp G 2 (volume.restrict K)

section Convergence

variable {X F ι : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-- Strong `L^p_loc(Ω)` convergence `f i → f₀` along `l`: `‖f i - f₀‖_{L^p(K)} → 0` for every
compact `K ⊆ Ω`. -/
def TendstoLpLoc [NormedAddCommGroup F] (p : ℝ≥0∞) (μ : Measure X) (Ω : Set X)
    (f : ι → X → F) (f₀ : X → F) (l : Filter ι) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → Tendsto (fun i ↦ eLpNorm (f i - f₀) p (μ.restrict K)) l (𝓝 0)

/-- Weak `L²(Ω)` convergence `f i ⇀ f₀` along `l`: all functions are in `L²(Ω)` and
`∫_Ω ⟨f i, φ⟩ → ∫_Ω ⟨f₀, φ⟩` for every `φ ∈ L²(Ω)`. -/
def TendstoWeakL2 [NormedAddCommGroup F] [InnerProductSpace ℝ F] (μ : Measure X) (Ω : Set X)
    (f : ι → X → F) (f₀ : X → F) (l : Filter ι) : Prop :=
  (∀ i, MemLp (f i) 2 (μ.restrict Ω)) ∧ MemLp f₀ 2 (μ.restrict Ω) ∧
    ∀ φ : X → F, MemLp φ 2 (μ.restrict Ω) →
      Tendsto (fun i ↦ ∫ x in Ω, inner ℝ (f i x) (φ x) ∂μ) l
        (𝓝 (∫ x in Ω, inner ℝ (f₀ x) (φ x) ∂μ))

end Convergence

end GMTFoundations
