/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.GaussGreenPair.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Gauss–Green pairs: uniqueness, restriction, complement, blow-ups

## Main results

* `IsGaussGreenPair.unique`: uniqueness of the pair (`μ₁ = μ₂`, `ν₁ = ν₂` `μ₁`-a.e.). This is
  what makes `reducedBoundary`, which quantifies existentially over Gauss–Green pairs,
  independent of the witness.
* `IsGaussGreenPair.restrict`, `IsGaussGreenPair.compl`, and `IsGaussGreenPair.blowup`
  (translation and dilation `(E - x)/r`, used for the blow-up at reduced-boundary points).

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*,
rev. ed., CRC Press, 2015 (EG).
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### Uniqueness, restriction, complement -/

section API

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- `⟪φ, ν⟫` is `μ`-integrable for continuous `φ` with compact support in `Ω`. -/
theorem IsGaussGreenPair.integrable_inner (h : IsGaussGreenPair Ω E μ ν) {φ : Rn n → Rn n}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω) :
    Integrable (fun x ↦ ⟪φ x, ν x⟫) μ := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hT : μ (tsupport φ) < ⊤ := h.lt_top_of_isCompact _ hφc hφΩ
  refine Integrable.mono' ((integrable_indicator_iff (isClosed_tsupport φ).measurableSet).2
    (integrableOn_const hT.ne) : Integrable ((tsupport φ).indicator fun _ ↦ C) μ)
    (hφ.measurable.inner h.measurable_normal).aestronglyMeasurable ?_
  filter_upwards [h.norm_normal] with x hx
  by_cases hxT : x ∈ tsupport φ
  · rw [indicator_of_mem hxT, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (by rw [hx, mul_one]; exact hC x)
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport hxT
    simp [this, indicator_of_notMem hxT]

/-- Two measures concentrated on the open set `Ω`, finite on its compact subsets and equal on its
open subsets, are equal. -/
private theorem measure_eq_of_isOpen (hΩ : IsOpen Ω) {μ₁ μ₂ : Measure (Rn n)}
    (h₁ : μ₁ Ωᶜ = 0) (h₂ : μ₂ Ωᶜ = 0) (hf₁ : ∀ K, IsCompact K → K ⊆ Ω → μ₁ K < ⊤)
    (hf₂ : ∀ K, IsCompact K → K ⊆ Ω → μ₂ K < ⊤)
    (h : ∀ V, IsOpen V → V ⊆ Ω → μ₁ V = μ₂ V) : μ₁ = μ₂ := by
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have hV : ∀ k, ∃ V, IsOpen V ∧ Subtype.val '' compactCovering Ω k ⊆ V ∧ closure V ⊆ Ω ∧
      IsCompact (closure V) := fun k ↦ exists_open_between_and_isCompact_closure
    ((isCompact_compactCovering Ω k).image continuous_subtype_val) hΩ
    (Subtype.coe_image_subset _ _)
  choose V hVo hCV hVΩ hVc using hV
  let s : Option ℕ → Set (Rn n) := fun o ↦ o.elim Ωᶜ V
  have hs : ⋃ o, s o = univ := by
    refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    by_cases hx : x ∈ Ω
    · have : (⟨x, hx⟩ : Ω) ∈ ⋃ k, compactCovering Ω k := by
        rw [iUnion_compactCovering]; exact mem_univ _
      obtain ⟨k, hk⟩ := mem_iUnion.1 this
      exact ⟨some k, hCV k ⟨⟨x, hx⟩, hk, rfl⟩⟩
    · exact ⟨none, hx⟩
  refine Measure.ext_of_iUnion_eq_univ hs fun o ↦ ?_
  cases o with
  | none =>
    simp only [s, Option.elim]
    rw [Measure.restrict_eq_zero.2 h₁, Measure.restrict_eq_zero.2 h₂]
  | some k =>
    simp only [s, Option.elim]
    have hVk : V k ⊆ Ω := subset_closure.trans (hVΩ k)
    have : IsFiniteMeasure (μ₁.restrict (V k)) := isFiniteMeasure_restrict.2
      ((measure_mono subset_closure).trans_lt (hf₁ _ (hVc k) (hVΩ k))).ne
    have : IsFiniteMeasure (μ₂.restrict (V k)) := isFiniteMeasure_restrict.2
      ((measure_mono subset_closure).trans_lt (hf₂ _ (hVc k) (hVΩ k))).ne
    have := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (μ₁.restrict (V k))
    have := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (μ₂.restrict (V k))
    refine Measure.OuterRegular.ext_isOpen fun W hW ↦ ?_
    rw [Measure.restrict_apply hW.measurableSet, Measure.restrict_apply hW.measurableSet]
    exact h _ (hW.inter (hVo k)) (inter_subset_right.trans hVk)

/-- **Uniqueness of the measure.** Two Gauss–Green pairs for `E` on the open set `Ω` have the same
measure (it is `|Dχ_E|⌊Ω`, by the total-variation formula). -/
theorem IsGaussGreenPair.measure_eq {μ₁ μ₂ : Measure (Rn n)} {ν₁ ν₂ : Rn n → Rn n}
    (h₁ : IsGaussGreenPair Ω E μ₁ ν₁) (h₂ : IsGaussGreenPair Ω E μ₂ ν₂) (hΩ : IsOpen Ω) :
    μ₁ = μ₂ :=
  measure_eq_of_isOpen hΩ h₁.measure_compl h₂.measure_compl h₁.lt_top_of_isCompact
    h₂.lt_top_of_isCompact fun V hV hVΩ ↦ by
      rw [h₁.measure_eq_iSup hV hVΩ, h₂.measure_eq_iSup hV hVΩ]

/-- **Uniqueness of the normal.** Two Gauss–Green pairs for `E` on `Ω` with the same measure have
`μ`-a.e. equal normals. -/
theorem IsGaussGreenPair.ae_eq_normal {ν₁ ν₂ : Rn n → Rn n} (h₁ : IsGaussGreenPair Ω E μ ν₁)
    (h₂ : IsGaussGreenPair Ω E μ ν₂) (hΩ : IsOpen Ω) : ν₁ =ᵐ[μ] ν₂ := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hloc : LocallyIntegrableOn (fun x ↦ ν₁ x - ν₂ x) Ω μ := by
    rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
    intro K hKΩ hK
    have : IsFiniteMeasure (μ.restrict K) :=
      isFiniteMeasure_restrict.2 (h₁.lt_top_of_isCompact K hK hKΩ).ne
    refine Integrable.mono' (integrable_const (2 : ℝ))
      (h₁.measurable_normal.sub h₂.measurable_normal).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae h₁.norm_normal, ae_restrict_of_ae h₂.norm_normal]
      with x hx1 hx2
    exact (norm_sub_le _ _).trans (by rw [hx1, hx2]; norm_num)
  have hc : ∀ᵐ x ∂μ, x ∈ Ω := by
    rw [ae_iff]
    simpa [compl_def] using h₁.measure_compl
  have hzero := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgΩ ↦ by
    have hφ : ∀ i, IsSmoothTestField Ω (fun x ↦ g x • b i) := fun i ↦
      IsTestFunction.smul_const ⟨hg, hgc, hgΩ⟩ (b i)
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hT : μ (tsupport g) < ⊤ := h₁.lt_top_of_isCompact _ hgc hgΩ
    have hvec : Integrable (fun x ↦ g x • (ν₁ x - ν₂ x)) μ := by
      refine Integrable.mono' ((integrable_indicator_iff (isClosed_tsupport g).measurableSet).2
        (integrableOn_const hT.ne) : Integrable ((tsupport g).indicator fun _ ↦ C * 2) μ)
        (hg.continuous.measurable.smul
          (h₁.measurable_normal.sub h₂.measurable_normal)).aestronglyMeasurable ?_
      filter_upwards [h₁.norm_normal, h₂.norm_normal] with x hx1 hx2
      by_cases hxT : x ∈ tsupport g
      · rw [indicator_of_mem hxT, norm_smul]
        exact mul_le_mul (hC x) ((norm_sub_le _ _).trans (by rw [hx1, hx2]; norm_num))
          (norm_nonneg _) ((norm_nonneg _).trans (hC x))
      · have : g x = 0 := image_eq_zero_of_notMem_tsupport hxT
        simp [this, indicator_of_notMem hxT]
    rw [← b.sum_repr' (∫ x, g x • (ν₁ x - ν₂ x) ∂μ)]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hpt : (fun x ↦ ⟪b i, g x • (ν₁ x - ν₂ x)⟫) =
        fun x ↦ ⟪g x • b i, ν₁ x⟫ - ⟪g x • b i, ν₂ x⟫ := by
      funext x
      rw [real_inner_smul_right, inner_sub_right, real_inner_smul_left, real_inner_smul_left]
      ring
    rw [← integral_inner hvec, hpt,
      integral_sub (h₁.integrable_inner (hφ i).1.continuous (hφ i).2.1 (hφ i).2.2)
        (h₂.integrable_inner (hφ i).1.continuous (hφ i).2.1 (hφ i).2.2),
      ← h₁.integral_divergence _ (hφ i), ← h₂.integral_divergence _ (hφ i), sub_self, zero_smul]
  filter_upwards [hzero, hc] with x hx hxΩ
  exact sub_eq_zero.1 (hx hxΩ)

/-- **Uniqueness of the Gauss–Green pair**: on an open set, `μ₁ = μ₂` and
`ν₁ = ν₂` `μ₁`-a.e. Consequently `reducedBoundary`, which quantifies existentially over
pairs, does not depend on the witness. -/
theorem IsGaussGreenPair.unique {μ₁ μ₂ : Measure (Rn n)} {ν₁ ν₂ : Rn n → Rn n}
    (h₁ : IsGaussGreenPair Ω E μ₁ ν₁) (h₂ : IsGaussGreenPair Ω E μ₂ ν₂) (hΩ : IsOpen Ω) :
    μ₁ = μ₂ ∧ ν₁ =ᵐ[μ₁] ν₂ := by
  have hμ := h₁.measure_eq h₂ hΩ
  subst hμ
  exact ⟨rfl, h₁.ae_eq_normal h₂ hΩ⟩

/-- **Restriction.** A pair on `Ω` restricts to a pair `(μ⌊Ω', ν)` on an open `Ω' ⊆ Ω`. -/
theorem IsGaussGreenPair.restrict (h : IsGaussGreenPair Ω E μ ν) {Ω' : Set (Rn n)}
    (hΩ' : IsOpen Ω') (hΩ'Ω : Ω' ⊆ Ω) : IsGaussGreenPair Ω' E (μ.restrict Ω') ν where
  measure_compl := by
    rw [Measure.restrict_apply hΩ'.measurableSet.compl, compl_inter_self, measure_empty]
  lt_top_of_isCompact K hK hKΩ' :=
    (Measure.restrict_apply_le _ _).trans_lt (h.lt_top_of_isCompact K hK (hKΩ'.trans hΩ'Ω))
  measurable_normal := h.measurable_normal
  norm_normal := ae_restrict_of_ae h.norm_normal
  integral_divergence φ hφ := by
    rw [h.integral_divergence φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hΩ'Ω⟩,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_]
    have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hx' ↦ hx (hφ.2.2 hx')
    simp [this]

/-- The total integral of the divergence of a `C¹` compactly supported field vanishes. -/
private theorem integral_divergence_eq_zero {φ : Rn n → Rn n} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) : ∫ x, divergence φ x = 0 := by
  have : ContinuousSMul ℝ (Rn n) := IsBoundedSMul.continuousSMul
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hcomp : ∀ i x, fderiv ℝ (fun y ↦ ⟪b i, φ y⟫) x = (innerSL ℝ (b i)).comp (fderiv ℝ φ x) :=
    fun i x ↦ ((innerSL ℝ (b i)).hasFDerivAt.comp x (hdiff x).hasFDerivAt).fderiv
  have hdiv : ∀ x, divergence φ x = ∑ i, fderiv ℝ (fun y ↦ ⟪b i, φ y⟫) x (b i) := by
    intro x
    rw [divergence, LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hcomp]
    rfl
  simp_rw [hdiv]
  have hgi : ∀ i, ContDiff ℝ 1 (fun y ↦ ⟪b i, φ y⟫) := fun i ↦ contDiff_const.inner ℝ hφ
  have hgc : ∀ i, HasCompactSupport (fun y ↦ ⟪b i, φ y⟫) := fun i ↦
    hφc.comp_left (inner_zero_right (b i))
  have hint : ∀ i, Integrable (fun x ↦ fderiv ℝ (fun y ↦ ⟪b i, φ y⟫) x (b i)) := fun i ↦
    (((hgi i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport
      (((hgc i).fderiv ℝ).comp_left (g := fun L : Rn n →L[ℝ] ℝ ↦ L (b i)) (by simp))
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (f := fun _ : Rn n ↦ (1 : ℝ)) (f' := fun _ ↦ 0) (g := fun y ↦ ⟪b i, φ y⟫)
    (g' := fun x ↦ fderiv ℝ (fun y ↦ ⟪b i, φ y⟫) x) (v := b i)
    (B := ContinuousLinearMap.mul ℝ ℝ) (by simp) (by simpa using hint i)
    (by simpa using (hgi i).continuous.integrable_of_hasCompactSupport (hgc i))
    (fun x _ ↦ hasFDerivAt_const _ _)
    (fun x _ ↦ ((hgi i).differentiable one_ne_zero x).hasFDerivAt)
  simpa using this

/-- **Complement.** If `(μ, ν)` is a pair for a measurable `E` on `Ω`, then `(μ, -ν)` is a pair for
`Eᶜ` on `Ω` (EG: `|D χ_{Eᶜ}| = |D χ_E|`, `ν_{Eᶜ} = -ν_E`). -/
theorem IsGaussGreenPair.compl (h : IsGaussGreenPair Ω E μ ν) (hE : MeasurableSet E) :
    IsGaussGreenPair Ω Eᶜ μ (-ν) where
  measure_compl := h.measure_compl
  lt_top_of_isCompact := h.lt_top_of_isCompact
  measurable_normal := h.measurable_normal.neg
  norm_normal := by filter_upwards [h.norm_normal] with x hx; simpa using hx
  integral_divergence φ hφ := by
    rw [setIntegral_compl hE hφ.integrable_divergence,
      integral_divergence_eq_zero (hφ.1.of_le (by simp)) hφ.2.1, h.integral_divergence φ hφ,
      zero_sub, ← integral_neg]
    simp [inner_neg_right]

end API

/-! ### Translation and dilation (blow-ups) -/

section BlowUp

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- The affine homeomorphism `z ↦ x + r • z`. -/
private noncomputable def affineHomeo (x : Rn n) {r : ℝ} (hr : 0 < r) : Rn n ≃ₜ Rn n :=
  (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x)

private theorem affineHomeo_apply (x : Rn n) {r : ℝ} (hr : 0 < r) (z : Rn n) :
    affineHomeo x hr z = x + r • z := rfl

private theorem affineHomeo_symm_apply (x : Rn n) {r : ℝ} (hr : 0 < r) (y : Rn n) :
    (affineHomeo x hr).symm y = r⁻¹ • (y - x) := by
  rw [Homeomorph.symm_apply_eq, affineHomeo_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
    add_sub_cancel]

/-- `div (φ' ∘ A⁻¹) = r⁻¹ (div φ') ∘ A⁻¹` for `A z = x + r z`. -/
private theorem divergence_comp_affineHomeo_symm (x : Rn n) {r : ℝ} (hr : 0 < r)
    {φ' : Rn n → Rn n} (hφ' : Differentiable ℝ φ') (y : Rn n) :
    divergence (φ' ∘ (affineHomeo x hr).symm) y =
      r⁻¹ * divergence φ' ((affineHomeo x hr).symm y) := by
  have : ContinuousSMul ℝ (Rn n) := IsBoundedSMul.continuousSMul
  have hA : HasFDerivAt (affineHomeo x hr).symm (r⁻¹ • ContinuousLinearMap.id ℝ (Rn n)) y := by
    have : (affineHomeo x hr).symm = fun y ↦ r⁻¹ • (y - x) :=
      funext (affineHomeo_symm_apply x hr)
    rw [this]
    exact ((hasFDerivAt_id y).sub_const x).const_smul r⁻¹
  have hcomp := ((hφ' _).hasFDerivAt.comp y hA).fderiv
  rw [divergence, divergence, hcomp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]

/-- **Translation and dilation.** If `(μ, ν)` is a Gauss–Green pair for `E` on `Ω`, then for
`x ∈ ℝⁿ` and `r > 0` the blown-up set `E_{x,r} = {z : x + r z ∈ E}` has the Gauss–Green pair
`(r^{-(n-1)} (z ↦ (z - x)/r)_# μ, ν(x + r ·))` on `Ω_{x,r} = {z : x + r z ∈ Ω}`. -/
theorem IsGaussGreenPair.blowup (hn : 1 ≤ n) (h : IsGaussGreenPair Ω E μ ν) (x : Rn n) {r : ℝ}
    (hr : 0 < r) :
    IsGaussGreenPair ((fun z ↦ x + r • z) ⁻¹' Ω) ((fun z ↦ x + r • z) ⁻¹' E)
      ((ENNReal.ofReal (r ^ (n - 1)))⁻¹ • μ.map fun y ↦ r⁻¹ • (y - x))
      (fun z ↦ ν (x + r • z)) := by
  set A := affineHomeo x hr with hA_def
  have hA : (fun z ↦ x + r • z) = ⇑A := rfl
  have hAs : (fun y ↦ r⁻¹ • (y - x)) = ⇑A.symm := (funext (affineHomeo_symm_apply x hr)).symm
  have hν : (fun z ↦ ν (x + r • z)) = ν ∘ A := rfl
  rw [hA, hAs, hν]
  set c : ℝ≥0∞ := (ENNReal.ofReal (r ^ (n - 1)))⁻¹ with hc
  have hc_top : c < ⊤ := by
    rw [hc, ENNReal.inv_lt_top, ENNReal.ofReal_pos]
    positivity
  have hemb := A.symm.measurableEmbedding
  have hpre : ∀ S : Set (Rn n), A.symm ⁻¹' (A ⁻¹' S) = S := fun S ↦ by
    ext y; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Measure.smul_apply, hemb.map_apply, ← preimage_compl, hpre, h.measure_compl, smul_zero]
  · intro K hK hKΩ
    rw [Measure.smul_apply, hemb.map_apply, Homeomorph.preimage_symm, smul_eq_mul]
    refine ENNReal.mul_lt_top hc_top (h.lt_top_of_isCompact _ (hK.image A.continuous) ?_)
    rintro _ ⟨z, hz, rfl⟩
    exact hKΩ hz
  · exact h.measurable_normal.comp A.continuous.measurable
  · refine Measure.ae_smul_measure ?_ c
    rw [hemb.ae_map_iff]
    filter_upwards [h.norm_normal] with y hy
    simpa using hy
  · intro φ' hφ'
    set φ := φ' ∘ A.symm with hφ_def
    have hφ : IsSmoothTestField Ω φ := by
      refine ⟨hφ'.1.comp ?_, hφ'.2.1.comp_homeomorph A.symm, ?_⟩
      · rw [← hAs]; fun_prop
      · rw [hφ_def, tsupport_comp_eq_preimage]
        intro y hy
        have := hφ'.2.2 hy
        simpa using this
    have hdiff : Differentiable ℝ φ' := hφ'.1.differentiable (by simp)
    -- right-hand side
    rw [integral_smul_measure, hemb.integral_map]
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    rw [show (fun y ↦ ⟪φ' (A.symm y), ν y⟫) = fun y ↦ ⟪φ y, ν y⟫ from rfl,
      ← h.integral_divergence φ hφ]
    -- left-hand side: change of variables `y = x + r z`
    have hdivφ : ∀ z, divergence φ' z = r * divergence φ (A z) := by
      intro z
      rw [hφ_def, divergence_comp_affineHomeo_symm x hr hdiff, Homeomorph.symm_apply_apply,
        ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    have hmapA : Measure.map A volume = ENNReal.ofReal |(r ^ n)⁻¹| • (volume : Measure (Rn n)) := by
      have h1 : ⇑A = (fun w ↦ x + w) ∘ fun z ↦ r • z := rfl
      rw [h1, ← Measure.map_map (measurable_const_add x) (measurable_const_smul r),
        Measure.map_addHaar_smul volume hr.ne', finrank_euclideanSpace_fin, Measure.map_smul,
        map_add_left_eq_self]
      exact (measurable_const_add x).aemeasurable
    have hLHS : ∫ z in A ⁻¹' E, divergence φ' z =
        (ENNReal.ofReal |(r ^ n)⁻¹|).toReal * (r * ∫ y in E, divergence φ y) := by
      have e1 : ∫ z in A ⁻¹' E, divergence φ' z = ∫ z in A ⁻¹' E, r * divergence φ (A z) :=
        integral_congr_ae (ae_of_all _ hdivφ)
      rw [e1, ← A.measurableEmbedding.integral_map (g := fun y ↦ r * divergence φ y),
        ← A.measurableEmbedding.restrict_map, hmapA, Measure.restrict_smul, integral_smul_measure,
        integral_const_mul, smul_eq_mul]
    rw [hLHS, hc, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (by positivity), abs_of_pos (by positivity), ← mul_assoc]
    congr 1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_sub_cancel_left, pow_add, pow_one]
    field_simp

end BlowUp

end GMTFoundations
