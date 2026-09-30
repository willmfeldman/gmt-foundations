/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.GaussGreenPair.Basic
public import GMTFoundations.Perimeter.GaussGreenPair.API
import GMTFoundations.BV.TotalVariation
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Gauss–Green pairs: `C¹` test fields and the bridge to `weightedTV`

## Main results

* `IsGaussGreenPair.integral_divergence_of_contDiff`: the Gauss–Green formula for
  `ψ ∈ C¹_c(Ω; ℝⁿ)`, by mollification.
* `IsGaussGreenPair.weightedTV_indicator_eq`, `IsGaussGreenPair.totalVariationOn_indicator_eq`:
  the bridge to the duality total variation, `weightedTV V η χ_E = ∫_V η dμ` for continuous
  `η ≥ 0` and `totalVariationOn V χ_E = μ V`, for open `V ⊆ Ω` and measurable `E`.
* `IsGaussGreenPair.exists_smooth_integral_norm_sub_le`: `1_K ν` is an `L¹(μ)`-limit of fields
  in `C^∞_c(V; ℝⁿ)` bounded by `1` (the approximation step in the proof of Thm 1.38 of
  L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed., CRC
  Press, 2015).
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### `C¹` test fields and the bridge to `weightedTV` -/

section WeightedTV

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- Mollification of a `C¹` compactly supported field: smooth, supported in the `η`-neighbourhood
of the support, and `ε`-close in `C¹` (uniformly). -/
private theorem exists_smooth_approx_of_contDiff_one {ψ : Rn n → Rn n} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ φ : Rn n → Rn n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
      support φ ⊆ Metric.thickening η (support ψ) ∧ (∀ x, ‖φ x - ψ x‖ ≤ ε) ∧
      ∀ x, ‖fderiv ℝ φ x - fderiv ℝ ψ x‖ ≤ ε := by
  have : ContinuousSMul ℝ (Rn n) := IsBoundedSMul.continuousSMul
  have : ContinuousSMul ℝ (Rn n →L[ℝ] Rn n) := IsBoundedSMul.continuousSMul
  have hψcont : Continuous ψ := hψ.continuous
  have hDcont : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hDc : HasCompactSupport (fderiv ℝ ψ) := hψc.fderiv ℝ
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.uniformContinuous_iff.1
    (hψc.uniformContinuous_of_continuous hψcont) ε hε
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.uniformContinuous_iff.1
    (hDc.uniformContinuous_of_continuous hDcont) ε hε
  set r := min (min r₁ r₂) η with hr_def
  have hr : 0 < r := lt_min (lt_min hr₁ hr₂) hη
  let ρ : ContDiffBump (0 : Rn n) := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨convolution (ρ.normed volume) ψ (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_, ?_⟩
  · exact ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed
      hψcont.locallyIntegrable
  · refine (support_convolution_subset _).trans ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    rw [ρ.support_normed_eq] at ha
    refine Metric.mem_thickening_iff.2 ⟨b, hb, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_right]
    have := mem_ball_zero_iff.1 ha
    exact this.trans_le ((min_le_right _ _).trans_eq' rfl)
  · intro x
    rw [← dist_eq_norm]
    refine ρ.dist_normed_convolution_le hψcont.aestronglyMeasurable fun y hy ↦ (h₁ ?_).le
    exact (mem_ball.1 hy).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  · intro x
    have hderiv := (hψc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (ρ.integrable_normed (μ := volume)).locallyIntegrable hψ x).fderiv
    have hconv : convolution (ρ.normed volume) (fderiv ℝ ψ)
        ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (Rn n)) volume x =
        convolution (ρ.normed volume) (fderiv ℝ ψ) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      rw [convolution_def, convolution_def]
      congr 1
    have : CompleteSpace (Rn n →L[ℝ] Rn n) := FiniteDimensional.complete ℝ _
    rw [hderiv, hconv, ← dist_eq_norm]
    refine ρ.dist_normed_convolution_le hDcont.aestronglyMeasurable fun y hy ↦ (h₂ ?_).le
    exact (mem_ball.1 hy).trans_le ((min_le_left _ _).trans (min_le_right _ _))

/-- The trace as a continuous linear functional. -/
private noncomputable def traceCLM : (Rn n →L[ℝ] Rn n) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace ℝ (Rn n)).comp (ContinuousLinearMap.coeLM ℝ))

private theorem divergence_eq_traceCLM (φ : Rn n → Rn n) (x : Rn n) :
    divergence φ x = traceCLM (fderiv ℝ φ x) := rfl

/-- `|∫ f - ∫ g| ≤ c m(K)` for functions vanishing off `K` with `|f - g| ≤ c`. -/
private theorem abs_integral_sub_le {m : Measure (Rn n)} {K : Set (Rn n)} (hK : MeasurableSet K)
    (hmK : m K < ⊤) {f g : Rn n → ℝ} (hf : Integrable f m) (hg : Integrable g m)
    (hfK : ∀ x ∉ K, f x = 0) (hgK : ∀ x ∉ K, g x = 0) {c : ℝ}
    (hc : ∀ᵐ x ∂m, |f x - g x| ≤ c) :
    |∫ x, f x ∂m - ∫ x, g x ∂m| ≤ c * m.real K := by
  rw [← integral_sub hf hg, ← Real.norm_eq_abs]
  have hind : Integrable (K.indicator fun _ ↦ c) m :=
    (integrable_indicator_iff hK).2 (integrableOn_const hmK.ne)
  refine (norm_integral_le_of_norm_le hind ?_).trans ?_
  · filter_upwards [hc] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, Real.norm_eq_abs]; exact hx
    · simp [indicator_of_notMem hxK, hfK x hxK, hgK x hxK]
  · rw [integral_indicator_const _ hK, smul_eq_mul, mul_comm]

/-- **Gauss–Green formula for `C¹` fields.** A Gauss–Green pair on `Ω` satisfies
`∫_E div ψ = ∫ ⟪ψ, ν⟫ dμ` also for `ψ ∈ C¹_c(Ω; ℝⁿ)` (mollification). -/
theorem IsGaussGreenPair.integral_divergence_of_contDiff (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) {ψ : Rn n → Rn n} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψΩ : tsupport ψ ⊆ Ω) : ∫ x in E, divergence ψ x = ∫ x, ⟪ψ x, ν x⟫ ∂μ := by
  obtain ⟨δ, hδ, hδΩ⟩ := hψc.exists_cthickening_subset_open hΩ hψΩ
  set K' := Metric.cthickening δ (tsupport ψ) with hK'
  have hK'c : IsCompact K' := hψc.cthickening
  have hK'm : MeasurableSet K' := Metric.isClosed_cthickening.measurableSet
  have hψK' : ∀ x ∉ K', ψ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h' ↦ hx (Metric.self_subset_cthickening _ h')
  have hvolK' : volume K' < ⊤ := hK'c.measure_lt_top
  have hμK' : μ K' < ⊤ := h.lt_top_of_isCompact K' hK'c hδΩ
  obtain ⟨A, hA_def⟩ : ∃ A, A = (volume.restrict E).real K' := ⟨_, rfl⟩
  obtain ⟨B, hB_def⟩ : ∃ B, B = μ.real K' := ⟨_, rfl⟩
  obtain ⟨T, hT_def⟩ : ∃ T, T = ‖(traceCLM : (Rn n →L[ℝ] Rn n) →L[ℝ] ℝ)‖ := ⟨_, rfl⟩
  have hA : 0 ≤ A := hA_def ▸ measureReal_nonneg
  have hB : 0 ≤ B := hB_def ▸ measureReal_nonneg
  have hT : 0 ≤ T := hT_def ▸ ContinuousLinearMap.opNorm_nonneg _
  refine eq_of_forall_dist_le fun ε' hε' ↦ ?_
  set ε := ε' / (T * A + B + 1)
  have hε : 0 < ε := by positivity
  obtain ⟨φ, hφs, hφsupp, hφ0, hφ1⟩ := exists_smooth_approx_of_contDiff_one hψ hψc hδ hε
  have hφK' : support φ ⊆ K' :=
    hφsupp.trans ((Metric.thickening_subset_cthickening _ _).trans
      (Metric.cthickening_subset_of_subset _ (subset_tsupport ψ)))
  have hφK'' : ∀ x ∉ K', φ x = 0 := fun x hx ↦ by by_contra hne; exact hx (hφK' hne)
  have hφtest : IsSmoothTestField Ω φ :=
    ⟨hφs, HasCompactSupport.of_support_subset_isCompact hK'c hφK',
      (closure_minimal hφK' Metric.isClosed_cthickening).trans hδΩ⟩
  have hGG := h.integral_divergence φ hφtest
  -- divergence estimate
  have hdivψ : ∀ x ∉ K', divergence ψ x = 0 := fun x hx ↦ by
    have : x ∉ tsupport (divergence ψ) := fun h' ↦
      hx (Metric.self_subset_cthickening _ (tsupport_divergence_subset ψ h'))
    exact image_eq_zero_of_notMem_tsupport this
  have hdivφ : ∀ x ∉ K', divergence φ x = 0 := fun x hx ↦ by
    have : x ∉ tsupport (divergence φ) := fun h' ↦
      hx ((closure_minimal hφK' Metric.isClosed_cthickening) (tsupport_divergence_subset φ h'))
    exact image_eq_zero_of_notMem_tsupport this
  have hint_divψ : Integrable (divergence ψ) :=
    (continuous_divergence hψ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hK'c fun x hx ↦ by
        by_contra hx'; exact hx (hdivψ x hx'))
  have e1 : |(∫ x in E, divergence ψ x) - ∫ x in E, divergence φ x| ≤ (T * ε) * A := by
    rw [hA_def]
    refine abs_integral_sub_le (m := volume.restrict E) (c := T * ε) hK'm
      ((Measure.restrict_apply_le _ _).trans_lt hvolK')
      hint_divψ.integrableOn hφtest.integrable_divergence.integrableOn hdivψ hdivφ
      (ae_of_all _ fun x ↦ ?_)
    rw [divergence_eq_traceCLM, divergence_eq_traceCLM, ← ContinuousLinearMap.map_sub,
      ← Real.norm_eq_abs, hT_def]
    refine (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left ?_ (ContinuousLinearMap.opNorm_nonneg _))
    rw [norm_sub_rev]; exact hφ1 x
  have e2 : |∫ x, ⟪φ x, ν x⟫ ∂μ - ∫ x, ⟪ψ x, ν x⟫ ∂μ| ≤ ε * B := by
    have hloc : ∀ᵐ x ∂μ, ‖ν x‖ = 1 := h.norm_normal
    -- work on the restriction to `K'`, where `‖ν‖ = 1` a.e.
    have hr : ∀ f : Rn n → Rn n, (∀ x ∉ K', f x = 0) →
        ∫ x, ⟪f x, ν x⟫ ∂μ = ∫ x, ⟪f x, K'.indicator ν x⟫ ∂μ := by
      intro f hf
      congr 1; funext x
      by_cases hx : x ∈ K'
      · rw [indicator_of_mem hx]
      · simp [hf x hx]
    rw [hr φ hφK'', hr ψ hψK']
    have hνK : ∀ᵐ x ∂μ, ‖K'.indicator ν x‖ ≤ 1 := by
      filter_upwards [hloc] with x hx
      by_cases hxK : x ∈ K'
      · rw [indicator_of_mem hxK, hx]
      · simp [indicator_of_notMem hxK]
    have hint : ∀ f : Rn n → Rn n, Continuous f → HasCompactSupport f → tsupport f ⊆ Ω →
        Integrable (fun x ↦ ⟪f x, K'.indicator ν x⟫) μ := by
      intro f hf hfc hfΩ
      refine (h.integrable_inner hf hfc hfΩ).mono
        (hf.measurable.inner (h.measurable_normal.indicator hK'm)).aestronglyMeasurable ?_
      filter_upwards [hloc] with x hx
      by_cases hxK : x ∈ K'
      · rw [indicator_of_mem hxK]
      · simp [indicator_of_notMem hxK]
    rw [hB_def]
    refine abs_integral_sub_le hK'm hμK' (hint φ hφs.continuous hφtest.2.1 hφtest.2.2)
      (hint ψ hψ.continuous hψc hψΩ) (fun x hx ↦ by simp [indicator_of_notMem hx])
      (fun x hx ↦ by simp [indicator_of_notMem hx]) (c := ε) ?_
    filter_upwards [hνK] with x hx
    rw [← inner_sub_left]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖φ x - ψ x‖ * ‖K'.indicator ν x‖ ≤ ε * 1 :=
          mul_le_mul (hφ0 x) hx (norm_nonneg _) hε.le
      _ = ε := mul_one ε
  have hsum : (T * ε) * A + ε * B ≤ ε' := by
    have : (T * ε) * A + ε * B = ε * (T * A + B) := by ring
    rw [this]
    calc ε * (T * A + B) ≤ ε * (T * A + B + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = ε' := div_mul_cancel₀ _ (by positivity)
  rw [Real.dist_eq]
  calc |(∫ x in E, divergence ψ x) - ∫ x, ⟪ψ x, ν x⟫ ∂μ|
      = |((∫ x in E, divergence ψ x) - ∫ x in E, divergence φ x) +
          (∫ x, ⟪φ x, ν x⟫ ∂μ - ∫ x, ⟪ψ x, ν x⟫ ∂μ)| := by rw [← hGG]; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ (T * ε) * A + ε * B := add_le_add e1 e2
    _ ≤ ε' := hsum

/-- A `C¹` minorant of a continuous `η ≥ 0` in absolute value: `|θ| ≤ η` and `η - 3δ ≤ θ`. -/
private theorem exists_contDiff_abs_le {η : Rn n → ℝ} (hη : Continuous η) (hη0 : ∀ x, 0 ≤ η x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ : Rn n → ℝ, ContDiff ℝ 1 θ ∧ (∀ x, |θ x| ≤ η x) ∧ ∀ x, η x - 3 * δ ≤ θ x := by
  obtain ⟨θ, hθ, hθa, hθs⟩ := ((by fun_prop) :
      Continuous fun x ↦ max (η x - 2 * δ) 0).exists_contDiff_approx (ε := fun _ ↦ δ) 1
      continuous_const (fun _ ↦ hδ)
  refine ⟨θ, by exact_mod_cast hθ, fun x ↦ ?_, fun x ↦ ?_⟩ <;>
  · have hx := hθa x
    rw [Real.dist_eq, abs_lt] at hx
    by_cases h0 : θ x = 0
    · rw [h0] at hx ⊢
      have := le_max_left (η x - 2 * δ) 0
      first | simpa using hη0 x | linarith
    · have hmax : max (η x - 2 * δ) 0 ≠ 0 := hθs h0
      have hpos : 0 < η x - 2 * δ := by
        by_contra hle
        exact hmax (max_eq_right (not_lt.1 hle))
      rw [max_eq_left hpos.le] at hx
      first | (rw [abs_le]; constructor <;> linarith) | linarith

/-- `∫_V χ_E div ψ = ∫_E div ψ` for a field `ψ` supported in `V`. -/
theorem setIntegral_indicator_mul_divergence {V E : Set (Rn n)} (hE : MeasurableSet E)
    {ψ : Rn n → Rn n} (hψV : tsupport ψ ⊆ V) :
    ∫ x in V, E.indicator (1 : Rn n → ℝ) x * divergence ψ x = ∫ x in E, divergence ψ x := by
  have h0 : ∀ x ∉ V, E.indicator (1 : Rn n → ℝ) x * divergence ψ x = 0 := fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hψV (tsupport_divergence_subset ψ h')),
      mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero h0, ← integral_indicator hE]
  congr 1
  funext x
  by_cases hx : x ∈ E <;> simp [hx]

/-- The `≤` half of the bridge, for a pair on `V` itself. -/
private theorem weightedTV_indicator_le_of_self {V : Set (Rn n)} (h : IsGaussGreenPair V E μ ν)
    (hV : IsOpen V) (hE : MeasurableSet E) (η : Rn n → ℝ) :
    weightedTV V η (E.indicator 1) ≤ ∫⁻ x, ENNReal.ofReal (η x) ∂μ := by
  refine iSup₂_le fun ψ hψ ↦ ?_
  obtain ⟨hψ1, hψc, hψV, hψη⟩ := hψ
  rw [setIntegral_indicator_mul_divergence hE hψV,
    h.integral_divergence_of_contDiff hV hψ1 hψc hψV]
  have hint := h.integrable_inner hψ1.continuous hψc hψV
  calc ENNReal.ofReal (∫ x, ⟪ψ x, ν x⟫ ∂μ) ≤ ENNReal.ofReal (∫ x, ‖⟪ψ x, ν x⟫‖ ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono hint hint.norm fun x ↦ Real.le_norm_self _)
    _ = ∫⁻ x, ENNReal.ofReal ‖⟪ψ x, ν x⟫‖ ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hint.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
    _ ≤ ∫⁻ x, ENNReal.ofReal (η x) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [h.norm_normal] with x hx
        refine ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans ?_)
        rw [hx, mul_one]
        exact hψη x

/-- The `≥` half of the bridge, for a pair on `V` itself. -/
private theorem lintegral_le_weightedTV_indicator_of_self {V : Set (Rn n)}
    (h : IsGaussGreenPair V E μ ν) (hV : IsOpen V) (hE : MeasurableSet E) {η : Rn n → ℝ}
    (hη : Continuous η) (hη0 : ∀ x, 0 ≤ η x) :
    ∫⁻ x, ENNReal.ofReal (η x) ∂μ ≤ weightedTV V η (E.indicator 1) := by
  have hVae : V ∈ ae μ := mem_ae_iff.2 h.measure_compl
  rw [← Measure.restrict_eq_self_of_ae_mem hVae, ← withDensity_apply _ hV.measurableSet]
  refine measure_le_of_forall_isCompact hV fun K hK hKV ↦ ?_
  rw [withDensity_apply _ hK.measurableSet]
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
  have hμK' : μ K' < ⊤ := h.lt_top_of_isCompact K' hK' hK'V
  have hKK'' : K ⊆ K' := hKK'.trans interior_subset
  have hμK : μ K < ⊤ := (measure_mono hKK'').trans_lt hμK'
  obtain ⟨M, hM⟩ := hK'.bddAbove_image hη.continuousOn
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hηM : ∀ x ∈ K', η x ≤ M' := fun x hx ↦ (hM (mem_image_of_mem η hx)).trans (le_max_left _ _)
  have hηK : IntegrableOn η K μ := by
    have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 hμK.ne
    refine Integrable.of_bound hη.aestronglyMeasurable M'
      (ae_restrict_of_forall_mem hK.measurableSet fun x hx ↦ ?_)
    rw [Real.norm_of_nonneg (hη0 x)]
    exact hηM x (hKK'' hx)
  rw [← ofReal_integral_eq_lintegral_ofReal hηK (ae_of_all _ fun x ↦ hη0 x)]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hε' : (0 : ℝ) < ε := hε
  set t := μ.real K with ht_def
  have ht : 0 ≤ t := measureReal_nonneg
  set δ := (ε : ℝ) / (6 * (t + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  set ε₁ := (ε : ℝ) / (6 * (M' + 1)) with hε₁_def
  have hε₁ : 0 < ε₁ := by positivity
  have hδt : 3 * δ * t ≤ ε / 2 := by
    calc 3 * δ * t = (ε / 2) * (t / (t + 1)) := by rw [hδ_def]; field_simp; ring
      _ ≤ (ε / 2) * 1 :=
        mul_le_mul_of_nonneg_left (div_le_one_of_le₀ (by linarith) (by linarith)) (half_pos hε').le
      _ = ε / 2 := mul_one _
  have hMε : M' * (3 * ε₁) ≤ ε / 2 := by
    calc M' * (3 * ε₁) = (ε / 2) * (M' / (M' + 1)) := by rw [hε₁_def]; field_simp; ring
      _ ≤ (ε / 2) * 1 :=
        mul_le_mul_of_nonneg_left (div_le_one_of_le₀ (by linarith) (by linarith)) (half_pos hε').le
      _ = ε / 2 := mul_one _
  obtain ⟨θ, hθ, hθη, hθlow⟩ := exists_contDiff_abs_le hη hη0 hδ
  obtain ⟨φ, hφ, hφ1, hint, hL1⟩ := h.exists_smooth_integral_norm_sub_le isOpen_interior
    (interior_subset.trans hK'V) hK hKK' hε₁
  obtain ⟨ψ, hψ_def⟩ : ∃ ψ : Rn n → Rn n, ψ = fun x ↦ θ x • φ x := ⟨_, rfl⟩
  have hφK' : tsupport φ ⊆ K' := hφ.2.2.trans interior_subset
  have hψsupp : tsupport ψ ⊆ K' := by
    rw [hψ_def]; exact (tsupport_smul_subset_right _ _).trans hφK'
  have hψ1 : ContDiff ℝ 1 ψ := by
    rw [hψ_def]; exact hθ.smul (hφ.1.of_le (by simp))
  have hψc : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact hK' ((subset_tsupport ψ).trans hψsupp)
  have hψη : ∀ x, ‖ψ x‖ ≤ η x := fun x ↦ by
    rw [hψ_def, norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hφ1 x)).trans (hθη x)
  have hψtest : IsTVTestField V η ψ := ⟨hψ1, hψc, hψsupp.trans hK'V, hψη⟩
  have hW : ENNReal.ofReal (∫ x, ⟪ψ x, ν x⟫ ∂μ) ≤ weightedTV V η (E.indicator 1) := by
    have := le_iSup₂ (f := fun ψ (_ : IsTVTestField V η ψ) ↦
      ENNReal.ofReal (∫ x in V, E.indicator (1 : Rn n → ℝ) x * divergence ψ x)) ψ hψtest
    change ENNReal.ofReal (∫ x in V, E.indicator (1 : Rn n → ℝ) x * divergence ψ x) ≤
      weightedTV V η (E.indicator 1) at this
    rwa [setIntegral_indicator_mul_divergence hE (hψsupp.trans hK'V),
      h.integral_divergence_of_contDiff hV hψ1 hψc (hψsupp.trans hK'V)] at this
  -- the pointwise lower bound
  have hpt : ∀ᵐ x ∂μ, K.indicator (fun x ↦ η x - 3 * δ) x - M' * ‖φ x - K.indicator ν x‖ ≤
      ⟪ψ x, ν x⟫ := by
    filter_upwards [h.norm_normal] with x hx
    rw [hψ_def]
    simp only [real_inner_smul_left]
    by_cases hxK' : x ∈ K'
    · have hθM : |θ x| ≤ M' := (hθη x).trans (hηM x hxK')
      have hsplit : θ x * ⟪φ x, ν x⟫ = θ x * ⟪K.indicator ν x, ν x⟫ +
          θ x * ⟪φ x - K.indicator ν x, ν x⟫ := by
        rw [← mul_add, ← inner_add_left, add_sub_cancel]
      have h1 : -(M' * ‖φ x - K.indicator ν x‖) ≤ θ x * ⟪φ x - K.indicator ν x, ν x⟫ := by
        have : |θ x * ⟪φ x - K.indicator ν x, ν x⟫| ≤ M' * ‖φ x - K.indicator ν x‖ := by
          rw [abs_mul]
          refine mul_le_mul hθM ((abs_real_inner_le_norm _ _).trans (by rw [hx, mul_one]))
            (abs_nonneg _) hM'0
        exact (neg_le_neg this).trans (neg_abs_le _)
      have h2 : K.indicator (fun x ↦ η x - 3 * δ) x ≤ θ x * ⟪K.indicator ν x, ν x⟫ := by
        by_cases hxK : x ∈ K
        · rw [indicator_of_mem hxK, indicator_of_mem hxK, real_inner_self_eq_norm_sq, hx]
          simpa using hθlow x
        · simp [indicator_of_notMem hxK]
      linarith
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hxK' (hφK' h')
      have hxK : x ∉ K := fun h' ↦ hxK' (hKK'' h')
      simp [hφx, indicator_of_notMem hxK]
  have hindK : Integrable (K.indicator fun x ↦ η x - 3 * δ) μ :=
    (integrable_indicator_iff hK.measurableSet).2 (hηK.sub (integrableOn_const hμK.ne))
  have hψint : Integrable (fun x ↦ ⟪ψ x, ν x⟫) μ :=
    h.integrable_inner hψ1.continuous hψc (hψsupp.trans hK'V)
  have hlow : ∫ x, (K.indicator (fun x ↦ η x - 3 * δ) x - M' * ‖φ x - K.indicator ν x‖) ∂μ ≤
      ∫ x, ⟪ψ x, ν x⟫ ∂μ := integral_mono_ae (hindK.sub (hint.const_mul M')) hψint hpt
  rw [integral_sub hindK (hint.const_mul M'), integral_const_mul,
    integral_indicator hK.measurableSet, integral_sub hηK (integrableOn_const hμK.ne),
    setIntegral_const, smul_eq_mul] at hlow
  have hL1' : M' * ∫ x, ‖φ x - K.indicator ν x‖ ∂μ ≤ M' * (3 * ε₁) :=
    mul_le_mul_of_nonneg_left hL1 hM'0
  have hmain : ∫ x in K, η x ∂μ ≤ ∫ x, ⟪ψ x, ν x⟫ ∂μ + ε := by
    rw [← ht_def] at hlow
    linarith
  calc ENNReal.ofReal (∫ x in K, η x ∂μ) ≤ ENNReal.ofReal (∫ x, ⟪ψ x, ν x⟫ ∂μ + ε) :=
        ENNReal.ofReal_le_ofReal hmain
    _ ≤ ENNReal.ofReal (∫ x, ⟪ψ x, ν x⟫ ∂μ) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ ≤ _ := by rw [ENNReal.ofReal_coe_nnreal]; exact add_le_add hW le_rfl

/-- **Bridge to `weightedTV`.** For a Gauss–Green pair of a measurable `E` on `Ω`, an open
`V ⊆ Ω` and a continuous `η ≥ 0`, `weightedTV V η χ_E = ∫_V η dμ`. -/
theorem IsGaussGreenPair.weightedTV_indicator_eq (h : IsGaussGreenPair Ω E μ ν)
    (hE : MeasurableSet E) {V : Set (Rn n)} (hV : IsOpen V) (hVΩ : V ⊆ Ω) {η : Rn n → ℝ}
    (hη : Continuous η) (hη0 : ∀ x, 0 ≤ η x) :
    weightedTV V η (E.indicator 1) = ∫⁻ x in V, ENNReal.ofReal (η x) ∂μ :=
  le_antisymm (weightedTV_indicator_le_of_self (h.restrict hV hVΩ) hV hE η)
    (lintegral_le_weightedTV_indicator_of_self (h.restrict hV hVΩ) hV hE hη hη0)

/-- **Bridge to `totalVariationOn`.** For a Gauss–Green pair of a measurable `E` on `Ω` and
an open `V ⊆ Ω`, `totalVariationOn V χ_E = μ V`. -/
theorem IsGaussGreenPair.totalVariationOn_indicator_eq (h : IsGaussGreenPair Ω E μ ν)
    (hE : MeasurableSet E) {V : Set (Rn n)} (hV : IsOpen V) (hVΩ : V ⊆ Ω) :
    totalVariationOn V (E.indicator 1) = μ V := by
  rw [totalVariationOn, h.weightedTV_indicator_eq (η := 1) hE hV hVΩ continuous_const
    fun _ ↦ zero_le_one]
  simp only [Pi.one_apply, ENNReal.ofReal_one, setLIntegral_one]

end WeightedTV

end GMTFoundations
