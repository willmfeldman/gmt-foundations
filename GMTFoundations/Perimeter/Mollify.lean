/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.GaussGreenPair.Basic
public import GMTFoundations.Perimeter.GaussGreenPair.API
public import GMTFoundations.Perimeter.GaussGreenPair.WeightedTV
public import GMTFoundations.Defs.Sobolev
import GMTFoundations.BV.TotalVariation
import GMTFoundations.BV.Compactness
import GMTFoundations.Sobolev.Mollify
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Total variation of sets and mollification

The total variation of a set `E` in an open set `Ω` is the duality functional
`totalVariationOn Ω χ_E = sup {∫_Ω χ_E div ψ : ψ ∈ C¹_c(Ω; ℝⁿ), |ψ| ≤ 1}` (`Defs/BV.lean`); we write
`TV(E; Ω)` for it. This file bridges it to Gauss–Green pairs and to the smooth-field supremum, and
proves the mollification estimate from the proof of Thm 5.3 of L. C. Evans, R. F. Gariepy, *Measure
Theory and Fine Properties of Functions*, rev. ed., CRC Press, 2015 (EG), in the form used by the
isoperimetric and Poincaré inequalities.

## Main results

* `ofReal_integral_divergence_le_totalVariationOn`, `abs_integral_divergence_le_totalVariationOn`:
  `|∫_E div φ| ≤ TV(E; Ω) sup|φ|` for `φ ∈ C^∞_c(Ω; ℝⁿ)`.
* `exists_isGaussGreenPair_of_totalVariationOn_ne_top`: `TV(E; Ω) < ∞` gives a Gauss–Green pair
  `(μ, ν)` on `Ω` with `μ Ω = TV(E; Ω)` (via `exists_isGaussGreenPair_of_bound`). With
  `IsGaussGreenPair.totalVariationOn_indicator_eq` this is the two-way bridge.
* `totalVariationOn_indicator_eq_iSup`: `TV(E; Ω)` is also the supremum over `C^∞_c` fields.
* `IsGaussGreenPair.sigmaFinite`: the measure of a pair on an open set is σ-finite.
* `mollify ρ f = f ⋆ ρ` (bump on the right), `contDiff_mollify`, `mollify_indicator_mem_Icc`.
* `fderiv_mollify_indicator_apply`: for a pair `(μ, ν)` of `E` on `Ω` and `B̄_R(x) ⊆ Ω`
  (`R = ρ.rOut`), `D(χ_E ⋆ ρ)(x) v = -∫ ρ(x - y) ⟪v, ν(y)⟫ dμ(y)`.
* `lintegral_norm_fderiv_mollify_indicator_le`: `∫_V |D(χ_E ⋆ ρ)| ≤ μ(V + B_R)`, and
  `lintegral_norm_fderiv_mollify_indicator_le_totalVariationOn`: `∫_V |D(χ_E ⋆ ρ)| ≤ TV(E; Ω)`
  whenever `B̄_R(x) ⊆ Ω` for `x ∈ V` (the estimate in the proof of EG Thm 5.3, for sets).
* `ae_tendsto_mollify`, `tendstoLpLoc_mollify`: `f ⋆ ρ_i → f` a.e. and in `L¹_loc`.
* `mollifierBump k`: a standard sequence of bumps, `rOut = 1/(k+1) → 0`, `rOut = 2 rIn`.
* `transitionKernel = σ'` for Mathlib's `Real.smoothTransition` `σ`, and the one-dimensional
  kernel `scaledKernel r ε`, a probability density on `[r, r + ε]`, with kernel Lebesgue
  differentiation `ae_tendsto_integral_scaledKernel_mul` (used by `Slicing` and `HalfSpace`).

## Route

The usual proof of `∫|∇u_ε| ≤ TV` goes by duality and an approximation of `∇u/|∇u|` by smooth
fields. We use a shorter route: if `TV(E; Ω) < ∞` then `E` has a pair `(μ, ν)` with `μ Ω = TV`, and
then `∇(χ_E ⋆ ρ)(x) = -∫ ρ(x - y) ν(y) dμ(y)` (Gauss–Green with the field `y ↦ ρ(x - y) v`), so
`|∇(χ_E ⋆ ρ)| ≤ ρ ⋆ μ` pointwise and Tonelli gives the bound. No duality argument is needed.
-/

open MeasureTheory Metric Set Filter Topology Function ContinuousLinearMap
open scoped NNReal ENNReal RealInnerProductSpace ContDiff Convolution

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### Divergence helpers (private duplicates of helpers in `GaussGreenPair/Basic.lean`) -/

private theorem divergence_const_smul (c : ℝ) {φ : Rn n → Rn n} (hφ : Differentiable ℝ φ) :
    divergence (c • φ) = c • divergence φ := by
  funext x
  simp only [divergence, Pi.smul_apply, fderiv_const_smul (hφ x), ContinuousLinearMap.coe_smul,
    map_smul, smul_eq_mul]

private theorem divergence_zero' : divergence (0 : Rn n → Rn n) = 0 := by
  funext x
  simp [divergence]

private theorem IsSmoothTestField.const_smul' {Ω : Set (Rn n)} {φ : Rn n → Rn n}
    (hφ : IsSmoothTestField Ω φ) (c : ℝ) : IsSmoothTestField Ω (c • φ) :=
  ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left (f := fun _ ↦ c),
    (tsupport_smul_subset_right (fun _ ↦ c) φ).trans hφ.2.2⟩

/-! ### Total variation of sets -/

section Bridges

variable {Ω E : Set (Rn n)}

/-- For a field supported in `V`, the set integral over `V` of `χ div ψ` is the full integral. -/
theorem setIntegral_mul_divergence_eq_integral {V : Set (Rn n)} (χ : Rn n → ℝ)
    {ψ : Rn n → Rn n} (hψV : tsupport ψ ⊆ V) :
    ∫ x in V, χ x * divergence ψ x = ∫ x, χ x * divergence ψ x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hψV (tsupport_divergence_subset ψ h')),
      mul_zero]

/-- The total variation is monotone in the open set. -/
theorem totalVariationOn_mono {V Ω : Set (Rn n)} (hVΩ : V ⊆ Ω) (χ : Rn n → ℝ) :
    totalVariationOn V χ ≤ totalVariationOn Ω χ := by
  unfold totalVariationOn weightedTV
  refine iSup₂_le fun ψ hψ ↦ ?_
  have hψ' : IsTVTestField Ω 1 ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.1.trans hVΩ, hψ.2.2.2⟩
  rw [setIntegral_mul_divergence_eq_integral χ hψ.2.2.1,
    ← setIntegral_mul_divergence_eq_integral χ hψ'.2.2.1]
  exact le_iSup₂ (f := fun ψ (_ : IsTVTestField Ω 1 ψ) ↦
    ENNReal.ofReal (∫ x in Ω, χ x * divergence ψ x)) ψ hψ'

/-- The total variation only depends on the a.e. class of the function. -/
theorem totalVariationOn_congr_ae {V : Set (Rn n)} {f g : Rn n → ℝ} (hfg : f =ᵐ[volume] g) :
    totalVariationOn V f = totalVariationOn V g := by
  unfold totalVariationOn weightedTV
  congr 1
  ext ψ
  congr 1
  ext _
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae (hfg.mono fun y hy ↦ by simp only [hy]))

/-- Each admissible smooth field gives `∫_E div φ ≤ TV(E; Ω)`. -/
theorem ofReal_integral_divergence_le_totalVariationOn (hE : MeasurableSet E) {φ : Rn n → Rn n}
    (hφ : IsSmoothTestField Ω φ) (hφ1 : ∀ x, ‖φ x‖ ≤ 1) :
    ENNReal.ofReal (∫ x in E, divergence φ x) ≤ totalVariationOn Ω (E.indicator 1) := by
  have ht : IsTVTestField Ω 1 φ :=
    ⟨hφ.1.of_le (by simp), hφ.2.1, hφ.2.2, fun x ↦ by simpa using hφ1 x⟩
  have := le_iSup₂ (f := fun ψ (_ : IsTVTestField Ω 1 ψ) ↦
    ENNReal.ofReal (∫ x in Ω, E.indicator (1 : Rn n → ℝ) x * divergence ψ x)) φ ht
  rwa [setIntegral_indicator_mul_divergence hE hφ.2.2] at this

/-- A bound `∫_E div φ ≤ T` over the unit ball of `C^∞_c(Ω; ℝⁿ)` gives
`|∫_E div φ| ≤ T sup|φ|`. -/
theorem abs_integral_divergence_le_of_forall {T : ℝ≥0∞} (hT : T ≠ ⊤)
    (hb : ∀ φ : Rn n → Rn n, IsSmoothTestField Ω φ → (∀ x, ‖φ x‖ ≤ 1) →
      ENNReal.ofReal (∫ x in E, divergence φ x) ≤ T)
    {φ : Rn n → Rn n} (hφ : IsSmoothTestField Ω φ) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) :
    |∫ x in E, divergence φ x| ≤ T.toReal * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rcases hM0.eq_or_lt with hM0 | hMpos
  · have : φ = 0 := funext fun x ↦ norm_le_zero_iff.1 (hM0 ▸ hM x)
    subst this
    rw [← hM0]
    simp [divergence_zero']
  have hdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have key : ∀ s : ℝ, |s| = 1 → s * ∫ x in E, divergence φ x ≤ T.toReal * M := by
    intro s hs
    have hψ1 : ∀ x, ‖((s / M) • φ) x‖ ≤ 1 := fun x ↦ by
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_div, hs, abs_of_pos hMpos,
        div_mul_eq_mul_div, one_mul, div_le_one hMpos]
      exact hM x
    have h1 := hb _ (hφ.const_smul' (s / M)) hψ1
    rw [divergence_const_smul _ hdiff] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    rw [integral_const_mul] at h1
    have h2 := (ENNReal.ofReal_le_iff_le_toReal hT).1 h1
    rw [div_mul_eq_mul_div, div_le_iff₀ hMpos] at h2
    linarith
  rw [abs_le]
  constructor
  · have := key (-1) (by simp)
    linarith
  · have := key 1 (by simp)
    linarith

/-- `|∫_E div φ| ≤ TV(E; Ω) sup|φ|` for `φ ∈ C^∞_c(Ω; ℝⁿ)`. -/
theorem abs_integral_divergence_le_totalVariationOn (hE : MeasurableSet E)
    (hT : totalVariationOn Ω (E.indicator 1) ≠ ⊤) {φ : Rn n → Rn n}
    (hφ : IsSmoothTestField Ω φ) {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) :
    |∫ x in E, divergence φ x| ≤ (totalVariationOn Ω (E.indicator 1)).toReal * M :=
  abs_integral_divergence_le_of_forall hT
    (fun _ hφ hφ1 ↦ ofReal_integral_divergence_le_totalVariationOn hE hφ hφ1) hφ hM

/-- **Bridge, TV to pairs.** If `TV(E; Ω) < ∞` then `E` has a Gauss–Green pair `(μ, ν)` on `Ω`
with `μ Ω = TV(E; Ω)`. (EG Thm 5.1; the converse is
`IsGaussGreenPair.totalVariationOn_indicator_eq`.) -/
theorem exists_isGaussGreenPair_of_totalVariationOn_ne_top (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) (hT : totalVariationOn Ω (E.indicator 1) ≠ ⊤) :
    ∃ μ ν, IsGaussGreenPair Ω E μ ν ∧ μ Ω = totalVariationOn Ω (E.indicator 1) := by
  obtain ⟨μ, ν, h⟩ := exists_isGaussGreenPair_of_bound hΩ (E := E) fun _ _ _ ↦
    ⟨(totalVariationOn Ω (E.indicator 1)).toReal, fun _ hφ _ _ hM ↦
      abs_integral_divergence_le_totalVariationOn hE hT hφ hM⟩
  exact ⟨μ, ν, h, (h.totalVariationOn_indicator_eq hE hΩ subset_rfl).symm⟩

/-- `TV(E; Ω) < ∞` implies that `E` has locally finite perimeter in `Ω`. -/
theorem hasLocallyFinitePerimeter_of_totalVariationOn_ne_top (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) (hT : totalVariationOn Ω (E.indicator 1) ≠ ⊤) :
    HasLocallyFinitePerimeter Ω E :=
  let ⟨μ, ν, h, _⟩ := exists_isGaussGreenPair_of_totalVariationOn_ne_top hΩ hE hT
  ⟨μ, ν, h⟩

/-- **Smooth fields suffice.** `TV(E; Ω)` (a supremum over `C¹_c` fields) equals the supremum over
`C^∞_c` fields. -/
theorem totalVariationOn_indicator_eq_iSup (hΩ : IsOpen Ω) (hE : MeasurableSet E) :
    totalVariationOn Ω (E.indicator 1) =
      ⨆ (φ : Rn n → Rn n) (_ : IsSmoothTestField Ω φ) (_ : ∀ x, ‖φ x‖ ≤ 1),
        ENNReal.ofReal (∫ x in E, divergence φ x) := by
  refine le_antisymm ?_ (iSup₂_le fun φ hφ ↦ iSup_le fun hφ1 ↦
    ofReal_integral_divergence_le_totalVariationOn hE hφ hφ1)
  set S := ⨆ (φ : Rn n → Rn n) (_ : IsSmoothTestField Ω φ) (_ : ∀ x, ‖φ x‖ ≤ 1),
    ENNReal.ofReal (∫ x in E, divergence φ x) with hS_def
  rcases eq_top_or_lt_top S with hS | hS
  · rw [hS]
    exact le_top
  have hb : ∀ φ : Rn n → Rn n, IsSmoothTestField Ω φ → (∀ x, ‖φ x‖ ≤ 1) →
      ENNReal.ofReal (∫ x in E, divergence φ x) ≤ S := fun φ hφ hφ1 ↦
    le_iSup₂_of_le φ hφ (le_iSup_of_le hφ1 le_rfl)
  obtain ⟨μ, ν, h⟩ := exists_isGaussGreenPair_of_bound hΩ (E := E) fun _ _ _ ↦
    ⟨S.toReal, fun _ hφ _ _ hM ↦ abs_integral_divergence_le_of_forall hS.ne hb hφ hM⟩
  rw [h.totalVariationOn_indicator_eq hE hΩ subset_rfl, h.measure_eq_iSup hΩ subset_rfl]

end Bridges

/-! ### Pairs: σ-finiteness and integrability -/

section PairAPI

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- The measure of a Gauss–Green pair on an open set is σ-finite. -/
theorem IsGaussGreenPair.sigmaFinite (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) :
    SigmaFinite μ := by
  haveI : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let K : ℕ → Set (Rn n) := fun k ↦ Subtype.val '' compactCovering Ω k ∪ Ωᶜ
  refine ⟨⟨{ set := K, set_mem := fun _ ↦ trivial, finite := fun k ↦ ?_, spanning := ?_ }⟩⟩
  · refine (measure_union_le _ _).trans_lt ?_
    rw [h.measure_compl, add_zero]
    exact h.lt_top_of_isCompact _ ((isCompact_compactCovering Ω k).image continuous_subtype_val)
      (Subtype.coe_image_subset _ _)
  · refine eq_univ_of_forall fun x ↦ ?_
    by_cases hx : x ∈ Ω
    · have hmem : (⟨x, hx⟩ : Ω) ∈ ⋃ k, compactCovering Ω k := by
        rw [iUnion_compactCovering]
        exact mem_univ _
      obtain ⟨k, hk⟩ := mem_iUnion.1 hmem
      exact mem_iUnion.2 ⟨k, Or.inl ⟨⟨x, hx⟩, hk, rfl⟩⟩
    · exact mem_iUnion.2 ⟨0, Or.inr hx⟩

/-- A continuous function with compact support in `Ω` is integrable against the measure of a
pair on `Ω`. -/
theorem IsGaussGreenPair.integrable_of_continuous (h : IsGaussGreenPair Ω E μ ν)
    {g : Rn n → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω) :
    Integrable g μ := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hT : μ (tsupport g) < ⊤ := h.lt_top_of_isCompact _ hgc hgΩ
  refine Integrable.mono' ((integrable_indicator_iff (isClosed_tsupport g).measurableSet).2
    (integrableOn_const hT.ne) : Integrable ((tsupport g).indicator fun _ ↦ C) μ)
    hg.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  by_cases hxT : x ∈ tsupport g
  · rw [indicator_of_mem hxT]
    exact hC x
  · simp [image_eq_zero_of_notMem_tsupport hxT, indicator_of_notMem hxT]

end PairAPI

/-! ### Mollification -/

section Mollify

/-- The mollification `f ⋆ ρ` of `f` by the normalized bump `ρ` (bump on the right):
`(f ⋆ ρ)(x) = ∫ f(y) ρ(x - y) dy`. -/
@[expose] noncomputable def mollify (ρ : ContDiffBump (0 : Rn n)) (f : Rn n → ℝ) : Rn n → ℝ :=
  f ⋆[lsmul ℝ ℝ, volume] ρ.normed volume

theorem mollify_apply (ρ : ContDiffBump (0 : Rn n)) (f : Rn n → ℝ) (x : Rn n) :
    mollify ρ f x = ∫ y, f y * ρ.normed volume (x - y) := by
  simp [mollify, convolution_def]

/-- The mollification with the bump on the left (Mathlib's convention in
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`). -/
theorem mollify_eq_normed_convolution (ρ : ContDiffBump (0 : Rn n)) (f : Rn n → ℝ) :
    mollify ρ f = ρ.normed volume ⋆[lsmul ℝ ℝ, volume] f := by
  funext x
  rw [mollify_apply, convolution_eq_swap]
  simp [mul_comm]

/-- Mollifications of locally integrable functions are smooth. -/
theorem contDiff_mollify (ρ : ContDiffBump (0 : Rn n)) {f : Rn n → ℝ}
    (hf : LocallyIntegrable f) : ContDiff ℝ ∞ (mollify ρ f) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_right (lsmul ℝ ℝ) hf ρ.contDiff_normed

/-- Mollifications of compactly supported functions have compact support. -/
theorem hasCompactSupport_mollify (ρ : ContDiffBump (0 : Rn n)) {f : Rn n → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (mollify ρ f) :=
  hf.convolution (lsmul ℝ ℝ) ρ.hasCompactSupport_normed

/-- The support of `y ↦ ρ(x - y)` is the ball `B_R(x)`. -/
theorem support_normed_sub_subset (ρ : ContDiffBump (0 : Rn n)) (x : Rn n) :
    support (fun y ↦ ρ.normed volume (x - y)) ⊆ ball x ρ.rOut := by
  intro y hy
  have : x - y ∈ support (ρ.normed volume) := hy
  rw [ρ.support_normed_eq, mem_ball, dist_zero_right] at this
  rwa [mem_ball, dist_eq_norm, ← norm_neg, neg_sub]

theorem integral_normed_sub (ρ : ContDiffBump (0 : Rn n)) (x : Rn n) :
    ∫ y, ρ.normed volume (x - y) = 1 := by
  rw [integral_sub_left_eq_self (ρ.normed volume) volume x, ρ.integral_normed]

theorem integrable_normed_sub (ρ : ContDiffBump (0 : Rn n)) (x : Rn n) :
    Integrable (fun y ↦ ρ.normed volume (x - y)) :=
  (ρ.integrable_normed (μ := volume)).comp_sub_left x

/-- The mollification of an indicator takes values in `[0, 1]`. -/
theorem mollify_indicator_mem_Icc (ρ : ContDiffBump (0 : Rn n)) {E : Set (Rn n)}
    (hE : MeasurableSet E) (x : Rn n) : mollify ρ (E.indicator 1) x ∈ Icc (0 : ℝ) 1 := by
  rw [mollify_apply]
  have hi : Integrable fun y ↦ E.indicator (1 : Rn n → ℝ) y * ρ.normed volume (x - y) :=
    (integrable_normed_sub ρ x).bdd_mul ((measurable_const.indicator hE).aestronglyMeasurable)
      (c := 1) (Eventually.of_forall fun y ↦ by
        by_cases hy : y ∈ E <;> simp [hy])
  constructor
  · exact integral_nonneg fun y ↦ mul_nonneg (by by_cases hy : y ∈ E <;> simp [hy])
      (ρ.nonneg_normed _)
  · calc ∫ y, E.indicator (1 : Rn n → ℝ) y * ρ.normed volume (x - y)
        ≤ ∫ y, ρ.normed volume (x - y) := integral_mono hi (integrable_normed_sub ρ x) fun y ↦ by
          by_cases hy : y ∈ E
          · simp [hy]
          · simp [hy, ρ.nonneg_normed]
      _ = 1 := integral_normed_sub ρ x

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- **Derivative of the mollified indicator.** For a Gauss–Green pair `(μ, ν)` of `E` on `Ω` and
`B̄_R(x) ⊆ Ω` (`R = ρ.rOut`): `D(χ_E ⋆ ρ)(x) v = -∫ ρ(x - y) ⟪v, ν(y)⟫ dμ(y)`. -/
theorem fderiv_mollify_indicator_apply (h : IsGaussGreenPair Ω E μ ν) (hE : MeasurableSet E)
    (ρ : ContDiffBump (0 : Rn n)) {x : Rn n} (hx : closedBall x ρ.rOut ⊆ Ω) (v : Rn n) :
    fderiv ℝ (mollify ρ (E.indicator 1)) x v =
      -∫ y, ρ.normed volume (x - y) * ⟪v, ν y⟫ ∂μ := by
  haveI : ContinuousSMul ℝ (Rn n) := IsBoundedSMul.continuousSMul
  set k := ρ.normed volume with hk_def
  have hk_cs : HasCompactSupport k := ρ.hasCompactSupport_normed
  have hk_cd : ContDiff ℝ ∞ k := ρ.contDiff_normed
  have hk_diff : Differentiable ℝ k := hk_cd.differentiable (by simp)
  have hli : LocallyIntegrable (E.indicator (1 : Rn n → ℝ)) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hE
  have hderiv := hk_cs.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hli (hk_cd.of_le (by simp)) x
  have step : fderiv ℝ (mollify ρ (E.indicator 1)) x v =
      ∫ y, E.indicator (1 : Rn n → ℝ) y * fderiv ℝ k (x - y) v := by
    rw [mollify, hderiv.fderiv, convolution_precompR_apply (lsmul ℝ ℝ) hli (hk_cs.fderiv ℝ)
      (hk_cd.continuous_fderiv (by simp)) x v, convolution_def]
    simp
  set Φ : Rn n → Rn n := fun y ↦ k (x - y) • v with hΦ_def
  have hsupp : support Φ ⊆ closedBall x ρ.rOut := fun y hy ↦ by
    have : k (x - y) ≠ 0 := fun h0 ↦ hy (by simp [hΦ_def, h0])
    exact ball_subset_closedBall (support_normed_sub_subset ρ x this)
  have htsupp : tsupport Φ ⊆ closedBall x ρ.rOut := closure_minimal hsupp isClosed_closedBall
  have hΦ : IsSmoothTestField Ω Φ :=
    ⟨(hk_cd.comp (contDiff_const.sub contDiff_id)).smul contDiff_const,
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x ρ.rOut) hsupp,
      htsupp.trans hx⟩
  have hdiv : ∀ y, divergence Φ y = -fderiv ℝ k (x - y) v := fun y ↦ by
    have hfd : HasFDerivAt (fun y ↦ k (x - y))
        ((fderiv ℝ k (x - y)).comp (-ContinuousLinearMap.id ℝ (Rn n))) y :=
      (hk_diff (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
    rw [hΦ_def, divergence_smul_const hfd.differentiableAt v, hfd.fderiv]
    simp
  have hgg := h.integral_divergence Φ hΦ
  rw [step]
  have hstep2 : ∫ y, E.indicator (1 : Rn n → ℝ) y * fderiv ℝ k (x - y) v =
      -∫ y in E, divergence Φ y := by
    rw [← integral_indicator hE, ← integral_neg]
    congr 1
    funext y
    by_cases hy : y ∈ E <;> simp [hy, hdiv]
  rw [hstep2, hgg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp [hΦ_def, real_inner_smul_left]

/-- `|D(χ_E ⋆ ρ)(x)| ≤ ∫ ρ(x - y) dμ(y)`. -/
theorem norm_fderiv_mollify_indicator_le (h : IsGaussGreenPair Ω E μ ν) (hE : MeasurableSet E)
    (ρ : ContDiffBump (0 : Rn n)) {x : Rn n} (hx : closedBall x ρ.rOut ⊆ Ω) :
    ‖fderiv ℝ (mollify ρ (E.indicator 1)) x‖ ≤ ∫ y, ρ.normed volume (x - y) ∂μ := by
  have hsupp : support (fun y ↦ ρ.normed volume (x - y)) ⊆ closedBall x ρ.rOut :=
    (support_normed_sub_subset ρ x).trans ball_subset_closedBall
  have hint : Integrable (fun y ↦ ρ.normed volume (x - y)) μ :=
    h.integrable_of_continuous (ρ.continuous_normed.comp (continuous_const.sub continuous_id))
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x ρ.rOut) hsupp)
      ((closure_minimal hsupp isClosed_closedBall).trans hx)
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun y ↦ ρ.nonneg_normed _)
    fun v ↦ ?_
  rw [fderiv_mollify_indicator_apply h hE ρ hx v, norm_neg, mul_comm, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.const_mul ‖v‖) ?_
  filter_upwards [h.norm_normal] with y hy
  rw [norm_mul, Real.norm_of_nonneg (ρ.nonneg_normed _), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (ρ.nonneg_normed _)
  exact (norm_inner_le_norm _ _).trans (by rw [hy, mul_one])

/-- **Mollification estimate (EG Thm 5.3 for sets).** For a pair `(μ, ν)` of `E` on an open `Ω`
and a measurable `V` with `B̄_R(x) ⊆ Ω` for `x ∈ V`: `∫_V |D(χ_E ⋆ ρ)| ≤ μ(V + B_R)`. -/
theorem lintegral_norm_fderiv_mollify_indicator_le (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) (hE : MeasurableSet E) (ρ : ContDiffBump (0 : Rn n)) {V : Set (Rn n)}
    (hV : MeasurableSet V) (hVΩ : ∀ x ∈ V, closedBall x ρ.rOut ⊆ Ω) :
    ∫⁻ x in V, ‖fderiv ℝ (mollify ρ (E.indicator 1)) x‖ₑ ≤ μ (thickening ρ.rOut V) := by
  haveI := h.sigmaFinite hΩ
  set k := ρ.normed volume with hk_def
  have hk0 : ∀ z, 0 ≤ k z := ρ.nonneg_normed
  have hmeas : Measurable fun p : Rn n × Rn n ↦ ENNReal.ofReal (k (p.1 - p.2)) :=
    (ρ.continuous_normed.comp continuous_sub).measurable.ennreal_ofReal
  calc ∫⁻ x in V, ‖fderiv ℝ (mollify ρ (E.indicator 1)) x‖ₑ
      ≤ ∫⁻ x in V, ∫⁻ y, ENNReal.ofReal (k (x - y)) ∂μ := by
        refine setLIntegral_mono' hV fun x hx ↦ ?_
        have hsupp : support (fun y ↦ k (x - y)) ⊆ closedBall x ρ.rOut :=
          (support_normed_sub_subset ρ x).trans ball_subset_closedBall
        have hint : Integrable (fun y ↦ k (x - y)) μ :=
          h.integrable_of_continuous (ρ.continuous_normed.comp
            (continuous_const.sub continuous_id))
            (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x ρ.rOut) hsupp)
            ((closure_minimal hsupp isClosed_closedBall).trans (hVΩ x hx))
        rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y ↦ hk0 _),
          ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (norm_fderiv_mollify_indicator_le h hE ρ (hVΩ x hx))
    _ = ∫⁻ y, (∫⁻ x in V, ENNReal.ofReal (k (x - y))) ∂μ :=
        lintegral_lintegral_swap (μ := volume.restrict V) (ν := μ)
          (f := fun x y ↦ ENNReal.ofReal (k (x - y))) hmeas.aemeasurable
    _ ≤ ∫⁻ y, (thickening ρ.rOut V).indicator 1 y ∂μ := by
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : y ∈ thickening ρ.rOut V
        · rw [indicator_of_mem hy, Pi.one_apply]
          calc ∫⁻ x in V, ENNReal.ofReal (k (x - y)) ≤ ∫⁻ x, ENNReal.ofReal (k (x - y)) :=
                setLIntegral_le_lintegral _ _
            _ = ∫⁻ x, ENNReal.ofReal (k x) := lintegral_sub_right_eq_self (μ := volume)
                (fun x ↦ ENNReal.ofReal (k x)) y
            _ = ENNReal.ofReal (∫ x, k x) :=
                (ofReal_integral_eq_lintegral_ofReal ρ.integrable_normed
                  (ae_of_all _ hk0)).symm
            _ = 1 := by rw [ρ.integral_normed, ENNReal.ofReal_one]
        · rw [indicator_of_notMem hy]
          refine le_of_eq (setLIntegral_eq_zero_iff' ?_ ?_ |>.2 ?_) <;> [exact hV;
            exact (hmeas.comp (measurable_id.prodMk measurable_const)).aemeasurable; skip]
          refine ae_of_all _ fun x hx ↦ ?_
          have : k (x - y) = 0 := by
            by_contra h0
            have h1 : x - y ∈ support k := h0
            rw [ρ.support_normed_eq, mem_ball, dist_zero_right] at h1
            exact hy (mem_thickening_iff.2 ⟨x, hx, by rwa [dist_eq_norm, ← norm_neg, neg_sub]⟩)
          simp [this]
    _ = μ (thickening ρ.rOut V) := lintegral_indicator_one isOpen_thickening.measurableSet

/-- **Mollification estimate, TV form.** For measurable `E`, open `Ω`, and measurable
`V` with `B̄_R(x) ⊆ Ω` for `x ∈ V` (`R = ρ.rOut`): `∫_V |D(χ_E ⋆ ρ)| ≤ TV(E; Ω)`. -/
theorem lintegral_norm_fderiv_mollify_indicator_le_totalVariationOn (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) (ρ : ContDiffBump (0 : Rn n)) {V : Set (Rn n)}
    (hV : MeasurableSet V) (hVΩ : ∀ x ∈ V, closedBall x ρ.rOut ⊆ Ω) :
    ∫⁻ x in V, ‖fderiv ℝ (mollify ρ (E.indicator 1)) x‖ₑ ≤
      totalVariationOn Ω (E.indicator 1) := by
  by_cases hT : totalVariationOn Ω (E.indicator 1) = ⊤
  · rw [hT]
    exact le_top
  obtain ⟨μ, ν, h, hμ⟩ := exists_isGaussGreenPair_of_totalVariationOn_ne_top hΩ hE hT
  calc _ ≤ μ (thickening ρ.rOut V) :=
        lintegral_norm_fderiv_mollify_indicator_le h hΩ hE ρ hV hVΩ
    _ ≤ μ Ω := measure_mono fun y hy ↦ by
        obtain ⟨x, hx, hxy⟩ := mem_thickening_iff.1 hy
        exact hVΩ x hx (mem_closedBall.2 hxy.le)
    _ = _ := hμ

end Mollify

/-! ### Convergence of mollifications -/

section Convergence

/-- A standard sequence of bumps: `rIn = 1/(2(k+1))`, `rOut = 1/(k+1)`. -/
@[expose] noncomputable def mollifierBump (k : ℕ) : ContDiffBump (0 : Rn n) :=
  ⟨1 / (2 * (k + 1)), 1 / (k + 1), by positivity, by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linarith⟩

theorem mollifierBump_rOut (k : ℕ) :
    (mollifierBump k : ContDiffBump (0 : Rn n)).rOut = 1 / (k + 1) :=
  rfl

theorem mollifierBump_rOut_le (k : ℕ) :
    (mollifierBump k : ContDiffBump (0 : Rn n)).rOut ≤
      2 * (mollifierBump k : ContDiffBump (0 : Rn n)).rIn := by
  change 1 / ((k : ℝ) + 1) ≤ 2 * (1 / (2 * (k + 1)))
  apply le_of_eq
  field_simp

theorem tendsto_mollifierBump_rOut :
    Tendsto (fun k ↦ (mollifierBump k : ContDiffBump (0 : Rn n)).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- **A.e. convergence of mollifications** (Lebesgue differentiation; Mathlib
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`). -/
theorem ae_tendsto_mollify {ι : Type*} {l : Filter ι} {ρ : ι → ContDiffBump (0 : Rn n)} {K : ℝ}
    (hρ : Tendsto (fun i ↦ (ρ i).rOut) l (𝓝 0)) (hK : ∀ᶠ i in l, (ρ i).rOut ≤ K * (ρ i).rIn)
    {f : Rn n → ℝ} (hf : LocallyIntegrable f) :
    ∀ᵐ x, Tendsto (fun i ↦ mollify (ρ i) f x) l (𝓝 (f x)) := by
  simpa only [mollify_eq_normed_convolution] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hρ hK hf

/-- **`L¹_loc` convergence of mollifications.** -/
theorem tendstoLpLoc_mollify {ρ : ℕ → ContDiffBump (0 : Rn n)}
    (hρ : Tendsto (fun i ↦ (ρ i).rOut) atTop (𝓝 0)) {f : Rn n → ℝ} (hf : LocallyIntegrable f)
    (Ω : Set (Rn n)) : TendstoLpLoc 1 volume Ω (fun i ↦ mollify (ρ i) f) f atTop := by
  intro K _ hK
  set S := cthickening 1 K with hS_def
  have hSc : IsCompact S := hK.cthickening
  set f' := S.indicator f with hf'_def
  have hf' : Integrable f' := (integrable_indicator_iff hSc.measurableSet).2
    (hf.integrableOn_isCompact hSc)
  -- on `K`, and for `rOut ≤ 1`, `f` and `f'` have the same mollification
  have hloc : ∀ i, (ρ i).rOut ≤ 1 → ∀ x ∈ K, mollify (ρ i) f x = mollify (ρ i) f' x := by
    intro i hi x hx
    rw [mollify_apply, mollify_apply]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ S
    · simp [hf'_def, indicator_of_mem hy]
    · have : (ρ i).normed volume (x - y) = 0 := by
        by_contra h0
        have h1 := support_normed_sub_subset (ρ i) x h0
        exact hy (mem_cthickening_of_dist_le y x 1 K hx
          ((mem_ball.1 h1).le.trans hi))
      simp [this]
  have hK' : ∀ x ∈ K, f x = f' x := fun x hx ↦ by
    rw [hf'_def, indicator_of_mem (self_subset_cthickening K hx)]
  have hconv := tendsto_integral_norm_normed_convolution_sub hρ hf'
  have hconv' : Tendsto (fun i ↦ ENNReal.ofReal
      (∫ x, ‖(mollify (ρ i) f') x - f' x‖)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    simpa only [mollify_eq_normed_convolution] using hconv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv'
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [(tendsto_order.1 hρ).2 1 one_pos] with i hi
  have hint : Integrable fun x ↦ mollify (ρ i) f' x - f' x := by
    rw [mollify_eq_normed_convolution]
    exact ((ρ i).integrable_normed.integrable_convolution _ hf').sub hf'
  calc eLpNorm ((fun x ↦ mollify (ρ i) f x) - f) 1 (volume.restrict K)
      = eLpNorm ((fun x ↦ mollify (ρ i) f' x) - f') 1 (volume.restrict K) := by
        refine eLpNorm_congr_ae ((ae_restrict_iff' hK.measurableSet).2
          (Eventually.of_forall fun x hx ↦ ?_))
        simp [hloc i hi.le x hx, hK' x hx]
    _ ≤ eLpNorm ((fun x ↦ mollify (ρ i) f' x) - f') 1 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = ENNReal.ofReal (∫ x, ‖mollify (ρ i) f' x - f' x‖) := by
        rw [eLpNorm_one_eq_lintegral_enorm, ofReal_integral_norm_eq_lintegral_enorm hint]
        rfl

end Convergence

/-! ### The transition kernel -/

section Kernel

/-- The kernel `κ = σ'`, where `σ = Real.smoothTransition`. -/
@[expose] noncomputable def transitionKernel (t : ℝ) : ℝ := deriv Real.smoothTransition t

theorem continuous_transitionKernel : Continuous transitionKernel :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

theorem hasDerivAt_smoothTransition (t : ℝ) :
    HasDerivAt Real.smoothTransition (transitionKernel t) t :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt

theorem transitionKernel_nonneg (t : ℝ) : 0 ≤ transitionKernel t :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem transitionKernel_eq_zero_of_notMem {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    transitionKernel t = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs using Real.smoothTransition.zero_of_nonpos hs.le
    simp [transitionKernel, this.deriv_eq]
  · have : Real.smoothTransition =ᶠ[𝓝 t] fun _ ↦ 1 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs using Real.smoothTransition.one_of_one_le hs.le
    simp [transitionKernel, this.deriv_eq]

theorem hasCompactSupport_transitionKernel : HasCompactSupport transitionKernel :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun _ ht ↦ by
    by_contra h
    exact ht (transitionKernel_eq_zero_of_notMem h)

theorem exists_transitionKernel_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, transitionKernel t ≤ C := by
  obtain ⟨C, hC⟩ :=
    continuous_transitionKernel.bounded_above_of_compact_support hasCompactSupport_transitionKernel
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun t ↦ (le_abs_self _).trans (hC t)⟩

theorem integral_transitionKernel : ∫ t, transitionKernel t = 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (0 : ℝ) 1)
    fun t ht ↦ transitionKernel_eq_zero_of_notMem ht, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  rw [show (fun t ↦ transitionKernel t) = deriv Real.smoothTransition from rfl,
    intervalIntegral.integral_deriv_eq_sub
      (fun t _ ↦ (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t)
      (continuous_transitionKernel.intervalIntegrable _ _)]
  simp

/-- The scaled kernel `ε⁻¹ κ((s - r)/ε)`, a probability density on `[r, r + ε]`. -/
@[expose] noncomputable def scaledKernel (r ε s : ℝ) : ℝ := ε⁻¹ * transitionKernel ((s - r) / ε)

theorem scaledKernel_nonneg {r ε : ℝ} (hε : 0 < ε) (s : ℝ) : 0 ≤ scaledKernel r ε s :=
  mul_nonneg (inv_nonneg.2 hε.le) (transitionKernel_nonneg _)

theorem scaledKernel_eq_zero {r ε s : ℝ} (hε : 0 < ε) (hs : s ∉ Icc r (r + ε)) :
    scaledKernel r ε s = 0 := by
  rw [scaledKernel, transitionKernel_eq_zero_of_notMem, mul_zero]
  intro h
  refine hs ⟨?_, ?_⟩
  · have := h.1
    rw [le_div_iff₀ hε, zero_mul] at this
    linarith
  · have := h.2
    rw [div_le_iff₀ hε, one_mul] at this
    linarith

theorem continuous_scaledKernel (r ε : ℝ) : Continuous (scaledKernel r ε) :=
  continuous_const.mul (continuous_transitionKernel.comp
    ((continuous_id.sub continuous_const).div_const ε))

theorem integral_scaledKernel {r ε : ℝ} (hε : 0 < ε) : ∫ s, scaledKernel r ε s = 1 := by
  simp only [scaledKernel]
  rw [integral_const_mul, integral_sub_right_eq_self (fun s ↦ transitionKernel (s / ε)) r,
    Measure.integral_comp_div, integral_transitionKernel, abs_of_pos hε, smul_eq_mul, mul_one,
    inv_mul_cancel₀ hε.ne']

/-- **Kernel Lebesgue differentiation.** For integrable `F : ℝ → ℝ` and a.e. `r`,
`∫ ε⁻¹ κ((s - r)/ε) F(s) ds → F(r)` as `ε → 0+`. -/
theorem ae_tendsto_integral_scaledKernel_mul {F : ℝ → ℝ} (hF : Integrable F) :
    ∀ᵐ r, Tendsto (fun ε ↦ ∫ s, scaledKernel r ε s * F s) (𝓝[>] 0) (𝓝 (F r)) := by
  obtain ⟨C, hC0, hC⟩ := exists_transitionKernel_le
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume
    hF.locallyIntegrable 1]
    with r hr
  have hav : Tendsto (fun ε ↦ ⨍ s in closedBall r ε, ‖F s - F r‖) (𝓝[>] 0) (𝓝 0) :=
    hr (fun _ ↦ r) id tendsto_id (eventually_mem_nhdsWithin.mono fun ε hε ↦ by
      rw [one_mul, id]; exact mem_closedBall_self (le_of_lt hε))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by have := hav.const_mul (2 * C); rwa [mul_zero] at this)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hKi : Integrable (scaledKernel r ε) :=
    (continuous_scaledKernel r ε).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun s hs ↦ by
        by_contra h; exact hs (scaledKernel_eq_zero hε h))
  have hKb : ∀ s, ‖scaledKernel r ε s‖ ≤ ε⁻¹ * C := fun s ↦ by
    rw [Real.norm_of_nonneg (scaledKernel_nonneg hε s), scaledKernel]
    exact mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.2 hε.le)
  have hKF : Integrable fun s ↦ scaledKernel r ε s * F s :=
    hF.bdd_mul (continuous_scaledKernel r ε).aestronglyMeasurable
      (Eventually.of_forall hKb)
  have hsplit : (∫ s, scaledKernel r ε s * F s) - F r =
      ∫ s, scaledKernel r ε s * (F s - F r) := by
    rw [show (fun s ↦ scaledKernel r ε s * (F s - F r)) =
        fun s ↦ scaledKernel r ε s * F s - scaledKernel r ε s * F r from
        funext fun s ↦ mul_sub _ _ _,
      integral_sub hKF (hKi.mul_const _), integral_mul_const, integral_scaledKernel hε, one_mul]
  have hvol : volume.real (closedBall r ε) = 2 * ε := by
    rw [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith)]
  have hloc : IntegrableOn (fun s ↦ ‖F s - F r‖) (closedBall r ε) :=
    (hF.integrableOn.sub (integrableOn_const (C := F r) measure_closedBall_lt_top.ne)).norm
  rw [hsplit, setAverage_eq, hvol, smul_eq_mul]
  calc ‖∫ s, scaledKernel r ε s * (F s - F r)‖
      ≤ ∫ s, (closedBall r ε).indicator (fun s ↦ ε⁻¹ * C * ‖F s - F r‖) s := by
        refine norm_integral_le_of_norm_le ((integrable_indicator_iff measurableSet_closedBall).2
          (hloc.const_mul _)) (Eventually.of_forall fun s ↦ ?_)
        by_cases hs : s ∈ Icc r (r + ε)
        · have hs' : s ∈ closedBall r ε := by
            rw [Real.closedBall_eq_Icc]
            exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
          rw [indicator_of_mem hs', norm_mul]
          exact mul_le_mul_of_nonneg_right (hKb s) (norm_nonneg _)
        · rw [scaledKernel_eq_zero hε hs, zero_mul, norm_zero]
          exact indicator_nonneg (fun _ _ ↦ by positivity) _
    _ = 2 * C * ((2 * ε)⁻¹ * ∫ s in closedBall r ε, ‖F s - F r‖) := by
        rw [integral_indicator measurableSet_closedBall, integral_const_mul]
        field_simp

/-- The kernel averages of a continuous function converge at every point. -/
theorem tendsto_integral_scaledKernel_mul_of_continuous {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (r : ℝ) : Tendsto (fun ε ↦ ∫ s, scaledKernel r ε s * Φ s) (𝓝[>] 0) (𝓝 (Φ r)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.continuous_iff.1 hΦ r (η / 2) (by positivity)
  refine ⟨δ, hδ, fun {ε} (hε : 0 < ε) hεδ ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos hε] at hεδ
  have hKc : HasCompactSupport (scaledKernel r ε) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun s hs ↦ by
      by_contra h; exact hs (scaledKernel_eq_zero hε h)
  have hKi : Integrable (scaledKernel r ε) :=
    (continuous_scaledKernel r ε).integrable_of_hasCompactSupport hKc
  have hKΦ : Integrable fun s ↦ scaledKernel r ε s * Φ s :=
    ((continuous_scaledKernel r ε).mul hΦ).integrable_of_hasCompactSupport hKc.mul_right
  have hsplit : (∫ s, scaledKernel r ε s * Φ s) - Φ r =
      ∫ s, scaledKernel r ε s * (Φ s - Φ r) := by
    rw [show (fun s ↦ scaledKernel r ε s * (Φ s - Φ r)) =
        fun s ↦ scaledKernel r ε s * Φ s - scaledKernel r ε s * Φ r from
        funext fun s ↦ mul_sub _ _ _,
      integral_sub hKΦ (hKi.mul_const _), integral_mul_const, integral_scaledKernel hε, one_mul]
  rw [dist_eq_norm, hsplit]
  calc ‖∫ s, scaledKernel r ε s * (Φ s - Φ r)‖ ≤ ∫ s, scaledKernel r ε s * (η / 2) := by
        refine norm_integral_le_of_norm_le (hKi.mul_const _) (Eventually.of_forall fun s ↦ ?_)
        rw [norm_mul, Real.norm_of_nonneg (scaledKernel_nonneg hε s)]
        by_cases hs : s ∈ Icc r (r + ε)
        · refine mul_le_mul_of_nonneg_left ?_ (scaledKernel_nonneg hε s)
          have : dist s r < δ := by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
          exact (hδΦ s this).le
        · rw [scaledKernel_eq_zero hε hs, zero_mul, zero_mul]
    _ = η / 2 := by rw [integral_mul_const, integral_scaledKernel hε, one_mul]
    _ < η := by linarith

end Kernel

end GMTFoundations
