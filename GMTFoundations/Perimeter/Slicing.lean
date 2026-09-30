/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.Mollify
import GMTFoundations.GMT.Polar
import GMTFoundations.GMT.SphereMeasure
import GMTFoundations.GMT.Basic
import GMTFoundations.GMT.HausdorffLebesgue
import GMTFoundations.BV.TotalVariation
import GMTFoundations.BV.Compactness
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Slicing by spheres (EG Lemma 5.2)

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (EG). Throughout, `F_f(s) := sphereIntegral f x s
= s^{n-1} ∫_{S^{n-1}} f(x + sω) dσ(ω)` (`Defs/Setup.lean`).

**A gap in EG.** EG Lemma 5.2 holds for a fixed test field `φ` off a null set of radii that
depends on `φ`. The proof of EG Lemma 5.3, step 1, uses it for all `φ` with `|φ| ≤ 1` at once
"for a.e. `r`" to get `‖∂(E ∩ B_r)‖(ℝⁿ) ≤ ‖∂E‖(B_r) + ℋ^{n-1}(E ∩ ∂B_r)`; a supremum over an
uncountable family is taken after fixing `r`. The inequality is true, and (a) below proves it off a
null set that does not depend on any test field, by lower semicontinuity of the variation.

## Main results

* `IsGaussGreenPair.integral_divergence_inter_ball_ae` (EG Lemma 5.2): for a Gauss–Green
  pair `(μ, ν)` of a measurable `E` on an open `Ω` and `φ ∈ C¹_c(ℝⁿ; ℝⁿ)`, for a.e. `r > 0` with
  `B̄_r(x) ⊆ Ω`:
  `∫_{E∩B_r(x)} div φ = ∫_{B_r(x)} ⟪φ, ν⟫ dμ + F_{χ_E ⟪φ, (· - x)/r⟫}(r)`.
* `IsGaussGreenPair.totalVariationOn_inter_ball_le_ae` (a): for a.e. `r > 0` with `B̄_r(x) ⊆ Ω`,
  `TV(E ∩ B_r(x); ℝⁿ) ≤ μ(B_r(x)) + F_{χ_E}(r)`. The exceptional set does not depend on any test
  field (this repairs EG Lemma 5.3, step 1; see above).
* `hasDerivAt_volume_inter_ball_ae` (b): `r ↦ |E ∩ B_r(x)|` has derivative `F_{χ_E}(r)` at a.e.
  `r > 0`, and `volume_inter_ball_toReal_eq_integral`: `|E ∩ B_r(x)| = ∫_0^r F_{χ_E}`.
* `sphereIntegral_indicator_eq_hausdorffN`: `F_{χ_E}(r) = ℋ^{n-1}(E ∩ ∂B_r(x))` for `r > 0`, so
  (a) and (b) hold with `ℋ^{n-1}(E ∩ ∂B_r(x))` as in EG.

## Tools

* `transitionKernel = σ'` for Mathlib's `Real.smoothTransition` `σ`, and
  `scaledKernel r ε s = ε⁻¹ σ'((s - r)/ε)`, a probability density on `[r, r + ε]`.
* `ae_tendsto_integral_scaledKernel_mul`: kernel Lebesgue differentiation on `ℝ`.
* `radialCutoff x r ε = 1 - σ((|· - x| - r)/ε)`, a smooth cutoff for `B̄_r(x) ⊆ B_{r+ε}(x)`, with
  `D(radialCutoff) = -scaledKernel r ε (|y - x|) ⟪(y - x)/|y - x|, ·⟫`.
* `integral_radial_mul_eq`: `∫ K(|y - x|) g(y) dy = ∫_0^∞ K(s) F_g(s) ds` (polar coordinates).
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### The radial cutoff -/

section Cutoff

/-- The smooth radial cutoff `h(y) = 1 - σ((|y - x| - r)/ε)`: `1` on `B̄_r(x)`, `0` off
`B_{r+ε}(x)`. -/
@[expose] noncomputable def radialCutoff (x : Rn n) (r ε : ℝ) (y : Rn n) : ℝ :=
  1 - Real.smoothTransition ((‖y - x‖ - r) / ε)

variable {x : Rn n} {r ε : ℝ}

theorem radialCutoff_of_le (hε : 0 < ε) {y : Rn n} (hy : ‖y - x‖ ≤ r) :
    radialCutoff x r ε y = 1 := by
  rw [radialCutoff, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (by linarith) hε.le), sub_zero]

theorem radialCutoff_of_ge (hε : 0 < ε) {y : Rn n} (hy : r + ε ≤ ‖y - x‖) :
    radialCutoff x r ε y = 0 := by
  rw [radialCutoff, Real.smoothTransition.one_of_one_le, sub_self]
  rw [le_div_iff₀ hε, one_mul]
  linarith

theorem radialCutoff_nonneg (y : Rn n) : 0 ≤ radialCutoff x r ε y :=
  sub_nonneg.2 (Real.smoothTransition.le_one _)

theorem radialCutoff_le_one (y : Rn n) : radialCutoff x r ε y ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem support_radialCutoff_subset (hε : 0 < ε) :
    support (radialCutoff x r ε) ⊆ ball x (r + ε) := fun y hy ↦ by
  by_contra h
  rw [mem_ball, dist_eq_norm, not_lt] at h
  exact hy (radialCutoff_of_ge hε h)

theorem tsupport_radialCutoff_subset (hε : 0 < ε) :
    tsupport (radialCutoff x r ε) ⊆ closedBall x (r + ε) :=
  closure_minimal ((support_radialCutoff_subset hε).trans ball_subset_closedBall)
    isClosed_closedBall

private theorem hasFDerivAt_norm_sub {y : Rn n} (hy : y ≠ x) :
    HasFDerivAt (fun z ↦ ‖z - x‖) (‖y - x‖⁻¹ • innerSL ℝ (y - x)) y := by
  have hyx : y - x ≠ 0 := sub_ne_zero.2 hy
  have h0 : HasFDerivAt (fun z : Rn n ↦ z - x) (ContinuousLinearMap.id ℝ (Rn n)) y :=
    (hasFDerivAt_id y).sub_const x
  have h1 : HasFDerivAt (fun z ↦ ‖z - x‖ ^ 2) ((2 • innerSL ℝ (y - x)).comp
      (ContinuousLinearMap.id ℝ (Rn n))) y := by
    have := (hasStrictFDerivAt_norm_sq (y - x)).hasFDerivAt.comp y h0
    exact this
  have h2 := h1.sqrt (by positivity)
  have hfun : (fun z ↦ √(‖z - x‖ ^ 2)) = fun z ↦ ‖z - x‖ :=
    funext fun z ↦ Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at h2
  convert h2 using 1
  ext v
  simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_id', comp_apply, id_eq, smul_eq_mul,
    nsmul_eq_mul, Nat.cast_ofNat, Real.sqrt_sq (norm_nonneg _), Pi.mul_apply, Pi.ofNat_apply]
  have : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 hyx
  field_simp

theorem contDiff_radialCutoff (hr : 0 < r) (hε : 0 < ε) :
    ContDiff ℝ ∞ (radialCutoff x r ε) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases lt_or_ge ‖y - x‖ r with hy | hy
  · refine contDiffAt_const (c := (1 : ℝ)).congr_of_eventuallyEq ?_
    have : IsOpen {z : Rn n | ‖z - x‖ < r} :=
      isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
    filter_upwards [this.mem_nhds hy] with z hz using radialCutoff_of_le hε (le_of_lt hz)
  · have h0 : y - x ≠ 0 := fun h ↦ by rw [h, norm_zero] at hy; linarith
    exact contDiffAt_const.sub (Real.smoothTransition.contDiffAt.comp y
      ((((contDiffAt_id.sub contDiffAt_const).norm ℝ h0).sub contDiffAt_const).div_const ε))

/-- `D h(y) v = -ε⁻¹ κ((|y - x| - r)/ε) ⟪(y - x)/|y - x|, v⟫`. -/
theorem fderiv_radialCutoff_apply (hr : 0 < r) (hε : 0 < ε) (y v : Rn n) :
    fderiv ℝ (radialCutoff x r ε) y v =
      -(scaledKernel r ε ‖y - x‖ * ⟪‖y - x‖⁻¹ • (y - x), v⟫) := by
  have : ContinuousSMul ℝ (Rn n) := IsBoundedSMul.continuousSMul
  rcases lt_or_ge ‖y - x‖ r with hy | hy
  · have hloc : radialCutoff x r ε =ᶠ[𝓝 y] fun _ ↦ 1 := by
      have : IsOpen {z : Rn n | ‖z - x‖ < r} :=
        isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
      filter_upwards [this.mem_nhds hy] with z hz using radialCutoff_of_le hε (le_of_lt hz)
    rw [hloc.fderiv_eq, scaledKernel_eq_zero hε (fun h ↦ by linarith [h.1])]
    simp only [fderiv_const_apply, zero_apply, zero_mul, neg_zero]
  · have hyx : y ≠ x := fun h ↦ by rw [h, sub_self, norm_zero] at hy; linarith
    have hσ : HasDerivAt Real.smoothTransition (transitionKernel ((‖y - x‖ - r) / ε))
        ((‖y - x‖ - r) / ε) :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    have hin : HasFDerivAt (fun z ↦ (‖z - x‖ - r) / ε)
        (ε⁻¹ • (‖y - x‖⁻¹ • innerSL ℝ (y - x))) y := by
      have := ((hasFDerivAt_norm_sub hyx).sub_const r).const_mul ε⁻¹
      simpa only [div_eq_inv_mul] using this
    have hd := (hasFDerivAt_const (1 : ℝ) y).sub (hσ.comp_hasFDerivAt y hin)
    have hd' : HasFDerivAt (radialCutoff x r ε) (0 - transitionKernel ((‖y - x‖ - r) / ε) •
        ε⁻¹ • ‖y - x‖⁻¹ • innerSL ℝ (y - x)) y := hd
    rw [hd'.fderiv]
    simp only [zero_sub, neg_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul, scaledKernel, real_inner_smul_left]
    ring

end Cutoff

/-! ### Polar coordinates for radial weights -/

/-- `∫ K(|y - x|) g(y) dy = ∫_0^∞ K(s) F_g(s) ds`. -/
theorem integral_radial_mul_eq [NeZero n] {K : ℝ → ℝ} {g : Rn n → ℝ} (x : Rn n)
    (hint : Integrable fun y ↦ K ‖y - x‖ * g y) :
    ∫ y, K ‖y - x‖ * g y = ∫ s in Ioi (0 : ℝ), K s * sphereIntegral g x s := by
  have htr : ∫ y, K ‖y - x‖ * g y = ∫ y, K ‖y‖ * g (x + y) := by
    rw [← integral_add_left_eq_self (μ := volume) (fun y ↦ K ‖y - x‖ * g y) x]
    simp
  have hint' : Integrable fun y : Rn n ↦ K ‖y‖ * g (x + y) := by
    have := hint.comp_add_left x
    simpa [Function.comp_def] using this
  rw [htr, integral_eq_integral_Ioi_sphere hint']
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
  simp only [sphereIntegral, smul_eq_mul]
  have : ∀ w : sphere (0 : Rn n) 1, K ‖s • (w : Rn n)‖ * g (x + s • (w : Rn n)) =
      K s * g (x + s • (w : Rn n)) := fun w ↦ by rw [norm_smul_sphere (le_of_lt hs)]
  simp_rw [this, integral_const_mul]
  ring

/-! ### Lebesgue points of sphere integrals -/

/-- For `f` integrable on every ball about `x`, the kernel averages of `s ↦ F_f(s)` converge to
`F_f(r)` for a.e. `r > 0`. -/
theorem ae_tendsto_integral_scaledKernel_sphereIntegral [NeZero n] {f : Rn n → ℝ} (x : Rn n)
    (hf : ∀ R, IntegrableOn f (ball x R)) :
    ∀ᵐ r, 0 < r → Tendsto (fun ε ↦ ∫ s in Ioi (0 : ℝ), scaledKernel r ε s * sphereIntegral f x s)
      (𝓝[>] 0) (𝓝 (sphereIntegral f x r)) := by
  have hN : ∀ N : ℕ, ∀ᵐ r, Tendsto (fun ε ↦ ∫ s, scaledKernel r ε s *
      (Ioo 0 (N : ℝ)).indicator (sphereIntegral f x) s) (𝓝[>] 0)
      (𝓝 ((Ioo 0 (N : ℝ)).indicator (sphereIntegral f x) r)) := fun N ↦ by
    refine ae_tendsto_integral_scaledKernel_mul ?_
    have h1 := intervalIntegrable_sphereIntegral (Nat.cast_nonneg N) (hf N)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (Nat.cast_nonneg N)] at h1
    exact (integrable_indicator_iff measurableSet_Ioo).2 h1
  rw [← ae_all_iff] at hN
  filter_upwards [hN] with r hr hr0
  obtain ⟨N, hN⟩ := exists_nat_gt (r + 1)
  have hrN : r ∈ Ioo 0 (N : ℝ) := ⟨hr0, by linarith⟩
  have := hr N
  rw [indicator_of_mem hrN] at this
  refine this.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε
  rw [← integral_indicator measurableSet_Ioi]
  congr 1
  funext s
  by_cases hs : s ∈ Icc r (r + ε)
  · have hs1 : s ∈ Ioo 0 (N : ℝ) := ⟨by linarith [hs.1], by linarith [hs.2, hε.2]⟩
    rw [indicator_of_mem hs1, indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs1.1)]
  · by_cases hs0 : s ∈ Ioi (0 : ℝ) <;> simp [hs0, scaledKernel_eq_zero hε.1 hs]

/-! ### The Gauss–Green identity with a radial cutoff -/

section Pair

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- Spheres about `x` are `μ`-null for all but countably many radii. -/
theorem IsGaussGreenPair.ae_measure_sphere_eq_zero (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) (x : Rn n) : ∀ᵐ r, μ (sphere x r) = 0 := by
  have := h.sigmaFinite hΩ
  have hc : {r : ℝ | 0 < μ (sphere x r)}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun _ ↦ isClosed_sphere.measurableSet)
      fun r s hrs ↦ Set.disjoint_left.2 fun y h1 h2 ↦
        hrs ((mem_sphere.1 h1).symm.trans (mem_sphere.1 h2))
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hc.measure_zero volume)] with r hr
  simpa using hr

/-- `B̄_r(x) = B_r(x)` up to a null set when the sphere is null. -/
theorem closedBall_ae_eq_ball_of {m : Measure (Rn n)} {x : Rn n} {r : ℝ}
    (h : m (sphere x r) = 0) : closedBall x r =ᵐ[m] ball x r := by
  refine ae_eq_set.2 ⟨measure_mono_null (fun y hy ↦ ?_) h, by
    simp [sdiff_eq_empty.2 ball_subset_closedBall]⟩
  rw [← ball_union_sphere] at hy
  exact hy.1.resolve_left hy.2

/-- **Gauss–Green with a radial cutoff.** For `B̄_{r+ε}(x) ⊆ Ω` and `ψ ∈ C¹`:
`∫_E h div ψ + ∫_E Dh·ψ = ∫ h ⟪ψ, ν⟫ dμ`, `h = radialCutoff x r ε`. -/
theorem IsGaussGreenPair.setIntegral_radialCutoff_add (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) {x : Rn n} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hB : closedBall x (r + ε) ⊆ Ω) {ψ : Rn n → Rn n} (hψ : ContDiff ℝ 1 ψ) :
    (∫ y in E, radialCutoff x r ε y * divergence ψ y) +
        ∫ y in E, fderiv ℝ (radialCutoff x r ε) y (ψ y) =
      ∫ y, radialCutoff x r ε y * ⟪ψ y, ν y⟫ ∂μ := by
  set c := radialCutoff x r ε with hc_def
  have hc1 : ContDiff ℝ 1 c := (contDiff_radialCutoff hr hε).of_le (by simp)
  have htc : tsupport c ⊆ closedBall x (r + ε) := tsupport_radialCutoff_subset hε
  have hcc : HasCompactSupport c :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
      ((subset_tsupport _).trans htc)
  set Ψ : Rn n → Rn n := fun y ↦ c y • ψ y with hΨ_def
  have hΨ : ContDiff ℝ 1 Ψ := hc1.smul hψ
  have htΨ : tsupport Ψ ⊆ closedBall x (r + ε) := (tsupport_smul_subset_left _ _).trans htc
  have hΨc : HasCompactSupport Ψ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
      ((subset_tsupport _).trans htΨ)
  have hgg := h.integral_divergence_of_contDiff hΩ hΨ hΨc (htΨ.trans hB)
  have hdiv : ∀ y, divergence Ψ y = c y * divergence ψ y + fderiv ℝ c y (ψ y) := fun y ↦
    divergence_smul (hc1.differentiable one_ne_zero y) (hψ.differentiable one_ne_zero y)
  have ha : Integrable fun y ↦ c y * divergence ψ y :=
    (hc1.continuous.mul (continuous_divergence hψ)).integrable_of_hasCompactSupport
      (hcc.mul_right (f' := divergence ψ))
  have hb : Integrable fun y ↦ fderiv ℝ c y (ψ y) :=
    ((hc1.continuous_fderiv one_ne_zero).clm_apply hψ.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (r + ε))
        fun y hy ↦ htc (support_fderiv_subset ℝ fun h0 ↦ hy (by simp [h0])))
  rw [← integral_add ha.integrableOn hb.integrableOn]
  simp_rw [← hdiv]
  rw [hgg]
  congr 1
  funext y
  rw [hΨ_def, real_inner_smul_left]

/-- **Gauss–Green with a radial cutoff, polar form.** With
`f(y) = χ_E(y) ⟪ψ(y), (y - x)/|y - x|⟫`:
`∫_E h div ψ - ∫_0^∞ ε⁻¹ κ((s - r)/ε) F_f(s) ds = ∫ h ⟪ψ, ν⟫ dμ`. -/
theorem IsGaussGreenPair.integral_radialCutoff_eq [NeZero n] (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hB : closedBall x (r + ε) ⊆ Ω) {ψ : Rn n → Rn n} (hψ : ContDiff ℝ 1 ψ) :
    (∫ y in E, radialCutoff x r ε y * divergence ψ y) -
        ∫ s in Ioi (0 : ℝ), scaledKernel r ε s *
          sphereIntegral (fun y ↦ E.indicator 1 y * ⟪ψ y, ‖y - x‖⁻¹ • (y - x)⟫) x s =
      ∫ y, radialCutoff x r ε y * ⟪ψ y, ν y⟫ ∂μ := by
  set c := radialCutoff x r ε with hc_def
  set f : Rn n → ℝ := fun y ↦ E.indicator 1 y * ⟪ψ y, ‖y - x‖⁻¹ • (y - x)⟫ with hf_def
  have hc1 : ContDiff ℝ 1 c := (contDiff_radialCutoff hr hε).of_le (by simp)
  have htc : tsupport c ⊆ closedBall x (r + ε) := tsupport_radialCutoff_subset hε
  have hb : Integrable fun y ↦ fderiv ℝ c y (ψ y) :=
    ((hc1.continuous_fderiv one_ne_zero).clm_apply hψ.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (r + ε))
        fun y hy ↦ htc (support_fderiv_subset ℝ fun h0 ↦ hy (by simp [h0])))
  have hpt : ∀ y, E.indicator (fun y ↦ fderiv ℝ c y (ψ y)) y =
      -(scaledKernel r ε ‖y - x‖ * f y) := fun y ↦ by
    by_cases hy : y ∈ E
    · rw [indicator_of_mem hy, hc_def, fderiv_radialCutoff_apply hr hε, hf_def]
      simp only [indicator_of_mem hy, Pi.one_apply, one_mul]
      rw [real_inner_comm]
    · simp only [indicator_of_notMem hy, hf_def, zero_mul, mul_zero, neg_zero]
  have hint : Integrable fun y ↦ scaledKernel r ε ‖y - x‖ * f y := by
    have := (hb.indicator hE).neg
    refine this.congr (Eventually.of_forall fun y ↦ ?_)
    simp only [Pi.neg_apply, hpt y, neg_neg]
  have hE' : ∫ y in E, fderiv ℝ c y (ψ y) =
      -∫ s in Ioi (0 : ℝ), scaledKernel r ε s * sphereIntegral f x s := by
    rw [← integral_indicator hE, ← integral_radial_mul_eq x hint, ← integral_neg]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have := h.setIntegral_radialCutoff_add hΩ hr hε hB hψ
  rw [hE'] at this
  linarith

end Pair

/-! ### Slicing by spheres -/

section Slicing

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- `h_ε → 1_{B̄_r(x)}` pointwise as `ε → 0`. -/
theorem tendsto_radialCutoff {x : Rn n} {r : ℝ} {e : ℕ → ℝ} (he : ∀ k, 0 < e k)
    (he0 : Tendsto e atTop (𝓝 0)) (y : Rn n) :
    Tendsto (fun k ↦ radialCutoff x r (e k) y) atTop
      (𝓝 ((closedBall x r).indicator 1 y)) := by
  by_cases hy : ‖y - x‖ ≤ r
  · rw [indicator_of_mem (by rwa [mem_closedBall, dist_eq_norm]), Pi.one_apply]
    exact tendsto_const_nhds.congr fun k ↦ (radialCutoff_of_le (he k) hy).symm
  · rw [indicator_of_notMem (by rwa [mem_closedBall, dist_eq_norm])]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_order.1 he0).2 (‖y - x‖ - r) (by linarith)] with k hk
    exact (radialCutoff_of_ge (he k) (by linarith)).symm

/-- A sequence `e k ↓ 0` with `0 < e k ≤ δ`. -/
private theorem exists_seq_pos_tendsto {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : ℕ → ℝ, (∀ k, 0 < e k) ∧ (∀ k, e k ≤ δ) ∧ Antitone e ∧ Tendsto e atTop (𝓝 0) := by
  refine ⟨fun k ↦ δ * (1 / ((k : ℝ) + 1)), fun k ↦ by positivity, fun k ↦ ?_, fun i j hij ↦ ?_,
    ?_⟩
  · refine mul_le_of_le_one_right hδ.le ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  · refine mul_le_mul_of_nonneg_left ?_ hδ.le
    have : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    exact one_div_le_one_div_of_le (by positivity) this
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ

/-- **Slicing by spheres** (EG Lemma 5.2). For a Gauss–Green pair `(μ, ν)` of a
measurable `E` on an open `Ω`, a point `x`, and `φ ∈ C¹_c(ℝⁿ; ℝⁿ)`, for a.e. `r > 0` with
`B̄_r(x) ⊆ Ω`:
`∫_{E∩B_r(x)} div φ = ∫_{B_r(x)} ⟪φ, ν⟫ dμ + ∫_{E∩∂B_r(x)} ⟪φ, (y - x)/r⟫ dℋ^{n-1}(y)`,
the last term written as `sphereIntegral`. The exceptional set depends on `φ` (as in EG). -/
theorem IsGaussGreenPair.integral_divergence_inter_ball_ae [NeZero n]
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) (x : Rn n)
    {φ : Rn n → Rn n} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∀ᵐ r, 0 < r → closedBall x r ⊆ Ω →
      ∫ y in E ∩ ball x r, divergence φ y = (∫ y in ball x r, ⟪φ y, ν y⟫ ∂μ) +
        sphereIntegral (fun y ↦ E.indicator 1 y * ⟪φ y, r⁻¹ • (y - x)⟫) x r := by
  set f : Rn n → ℝ := fun y ↦ E.indicator 1 y * ⟪φ y, ‖y - x‖⁻¹ • (y - x)⟫ with hf_def
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hunit : ∀ y : Rn n, ‖‖y - x‖⁻¹ • (y - x)‖ ≤ 1 := fun y ↦ by
    rw [norm_smul, norm_inv, norm_norm]
    by_cases h0 : ‖y - x‖ = 0
    · simp [h0]
    · rw [inv_mul_cancel₀ h0]
  have hfb : ∀ y, ‖f y‖ ≤ C := fun y ↦ by
    rw [hf_def, norm_mul]
    calc ‖E.indicator (1 : Rn n → ℝ) y‖ * ‖⟪φ y, ‖y - x‖⁻¹ • (y - x)⟫‖ ≤ 1 * (C * 1) := by
          gcongr
          · by_cases hy : y ∈ E <;> simp [hy]
          · exact (norm_inner_le_norm _ _).trans (mul_le_mul (hC y) (hunit y) (norm_nonneg _) hC0)
      _ = C := by ring
  have hfm : Measurable f :=
    (measurable_const.indicator hE).mul (hφ.continuous.measurable.inner
      ((measurable_id.sub_const x).norm.inv.smul (measurable_id.sub_const x)))
  have hfi : ∀ R, IntegrableOn f (ball x R) := fun R ↦
    Measure.integrableOn_of_bounded measure_ball_lt_top.ne hfm.aestronglyMeasurable
      (ae_of_all _ hfb)
  filter_upwards [ae_tendsto_integral_scaledKernel_sphereIntegral x hfi,
    h.ae_measure_sphere_eq_zero hΩ x] with r hK hsph hr hB
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open hΩ hB
  rw [cthickening_closedBall hδ.le hr.le, add_comm] at hδΩ
  obtain ⟨e, he, heδ, -, he0⟩ := exists_seq_pos_tendsto hδ
  have he0' : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨he0, Eventually.of_forall he⟩
  have hBk : ∀ k, closedBall x (r + e k) ⊆ Ω := fun k ↦
    (closedBall_subset_closedBall (by linarith [heδ k])).trans hδΩ
  have hid := fun k ↦ h.integral_radialCutoff_eq hΩ hE hr (he k) (hBk k) hφ
  -- the three limits
  have hdivi : Integrable (divergence φ) :=
    (continuous_divergence hφ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hφc
        ((subset_tsupport _).trans (tsupport_divergence_subset φ)))
  have hvol0 : volume (sphere x r) = 0 := Measure.addHaar_sphere volume x r
  have hL1 : Tendsto (fun k ↦ ∫ y in E, radialCutoff x r (e k) y * divergence φ y) atTop
      (𝓝 (∫ y in E ∩ ball x r, divergence φ y)) := by
    have := tendsto_integral_of_dominated_convergence (μ := volume.restrict E)
      (F := fun k y ↦ radialCutoff x r (e k) y * divergence φ y)
      (f := fun y ↦ (closedBall x r).indicator 1 y * divergence φ y) (fun y ↦ ‖divergence φ y‖)
      (fun k ↦ ((contDiff_radialCutoff hr (he k)).continuous.mul
        (continuous_divergence hφ)).aestronglyMeasurable) hdivi.norm.integrableOn
      (fun k ↦ Eventually.of_forall fun y ↦ by
        rw [norm_mul, Real.norm_of_nonneg (radialCutoff_nonneg y)]
        exact mul_le_of_le_one_left (norm_nonneg _) (radialCutoff_le_one y))
      (Eventually.of_forall fun y ↦ (tendsto_radialCutoff he he0 y).mul_const _)
    have e1 : ∫ y in E, (closedBall x r).indicator 1 y * divergence φ y =
        ∫ y in E ∩ ball x r, divergence φ y := by
      have : (fun y ↦ (closedBall x r).indicator (1 : Rn n → ℝ) y * divergence φ y) =
          (closedBall x r).indicator (divergence φ) := by
        funext y
        by_cases hy : y ∈ closedBall x r <;> simp [hy]
      rw [this, setIntegral_indicator measurableSet_closedBall]
      exact setIntegral_congr_set
        ((EventuallyEqSet.refl _ E).inter (closedBall_ae_eq_ball_of hvol0))
    rw [← e1]
    exact this
  have hL2 : Tendsto (fun k ↦ ∫ s in Ioi (0 : ℝ), scaledKernel r (e k) s * sphereIntegral f x s)
      atTop (𝓝 (sphereIntegral f x r)) := (hK hr).comp he0'
  have hμB : μ (closedBall x (r + δ)) < ⊤ :=
    h.lt_top_of_isCompact _ (isCompact_closedBall _ _) hδΩ
  have hL3 : Tendsto (fun k ↦ ∫ y, radialCutoff x r (e k) y * ⟪φ y, ν y⟫ ∂μ) atTop
      (𝓝 (∫ y in ball x r, ⟪φ y, ν y⟫ ∂μ)) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun k y ↦ radialCutoff x r (e k) y * ⟪φ y, ν y⟫)
      (f := fun y ↦ (closedBall x r).indicator 1 y * ⟪φ y, ν y⟫)
      ((closedBall x (r + δ)).indicator fun _ ↦ C)
      (fun k ↦ ((contDiff_radialCutoff hr (he k)).continuous.measurable.mul
        (hφ.continuous.measurable.inner h.measurable_normal)).aestronglyMeasurable)
      ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hμB.ne))
      (fun k ↦ by
        filter_upwards [h.norm_normal] with y hy
        by_cases hyB : y ∈ closedBall x (r + δ)
        · rw [indicator_of_mem hyB, norm_mul, Real.norm_of_nonneg (radialCutoff_nonneg y)]
          calc radialCutoff x r (e k) y * ‖⟪φ y, ν y⟫‖ ≤ 1 * (C * 1) :=
                mul_le_mul (radialCutoff_le_one y) ((norm_inner_le_norm _ _).trans
                  (by rw [hy]; exact mul_le_mul_of_nonneg_right (hC y) zero_le_one))
                  (norm_nonneg _) zero_le_one
            _ = C := by ring
        · rw [indicator_of_notMem hyB, radialCutoff_of_ge (he k), zero_mul, norm_zero]
          rw [mem_closedBall, dist_eq_norm, not_le] at hyB
          linarith [heδ k])
      (Eventually.of_forall fun y ↦ (tendsto_radialCutoff he he0 y).mul_const _)
    have e1 : ∫ y, (closedBall x r).indicator 1 y * ⟪φ y, ν y⟫ ∂μ =
        ∫ y in ball x r, ⟪φ y, ν y⟫ ∂μ := by
      have : (fun y ↦ (closedBall x r).indicator (1 : Rn n → ℝ) y * ⟪φ y, ν y⟫) =
          (closedBall x r).indicator (fun y ↦ ⟪φ y, ν y⟫) := by
        funext y
        by_cases hy : y ∈ closedBall x r <;> simp [hy]
      rw [this, integral_indicator measurableSet_closedBall]
      exact setIntegral_congr_set (closedBall_ae_eq_ball_of hsph)
    rw [← e1]
    exact this
  have hlim := tendsto_nhds_unique ((hL1.sub hL2).congr fun k ↦ hid k) hL3
  have hFr : sphereIntegral f x r =
      sphereIntegral (fun y ↦ E.indicator 1 y * ⟪φ y, r⁻¹ • (y - x)⟫) x r := by
    simp only [sphereIntegral]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
    simp only [hf_def, add_sub_cancel_left, norm_smul_sphere hr.le]
  linarith

/-- **(a), uniform in the test field.** For a Gauss–Green pair `(μ, ν)` of a measurable `E` on an
open `Ω` and a point `x`, for a.e. `r > 0` with `B̄_r(x) ⊆ Ω`:
`TV(E ∩ B_r(x); ℝⁿ) ≤ μ(B_r(x)) + F_{χ_E}(r)`, where `F_{χ_E}(r) = ℋ^{n-1}(E ∩ ∂B_r(x))`.
Unlike EG (Lemma 5.3, step 1), the exceptional set does not depend on a test field: for each `ψ`
with `|ψ| ≤ 1`, the Gauss–Green formula with a smooth radial cutoff `h_ε` of `B_r` bounds
`TV(h_ε χ_E)` by `μ(B̄_{r+ε}) + ∫ K_ε F_{χ_E}`; then `h_ε χ_E → χ_{E ∩ B̄_r}` in `L¹_loc` and lower
semicontinuity of the variation gives the bound at every Lebesgue point `r` of `F_{χ_E}` off the
countable set of radii where `μ(∂B_r) > 0`. -/
theorem IsGaussGreenPair.totalVariationOn_inter_ball_le_ae [NeZero n]
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) (x : Rn n) :
    ∀ᵐ r, 0 < r → closedBall x r ⊆ Ω →
      totalVariationOn univ ((E ∩ ball x r).indicator 1) ≤
        μ (ball x r) + ENNReal.ofReal (sphereIntegral (E.indicator 1) x r) := by
  have hχE : ∀ y, ‖E.indicator (1 : Rn n → ℝ) y‖ ≤ 1 := fun y ↦ by
    by_cases hy : y ∈ E <;> simp [hy]
  have hfi : ∀ R, IntegrableOn (E.indicator (1 : Rn n → ℝ)) (ball x R) := fun R ↦
    Measure.integrableOn_of_bounded measure_ball_lt_top.ne
      (measurable_const.indicator hE).aestronglyMeasurable (ae_of_all _ hχE)
  filter_upwards [ae_tendsto_integral_scaledKernel_sphereIntegral x hfi,
    h.ae_measure_sphere_eq_zero hΩ x] with r hK hsph hr hB
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open hΩ hB
  rw [cthickening_closedBall hδ.le hr.le, add_comm] at hδΩ
  obtain ⟨e, he, heδ, heanti, he0⟩ := exists_seq_pos_tendsto hδ
  have he0' : Tendsto e atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨he0, Eventually.of_forall he⟩
  have hBk : ∀ k, closedBall x (r + e k) ⊆ Ω := fun k ↦
    (closedBall_subset_closedBall (by linarith [heδ k])).trans hδΩ
  set F := sphereIntegral (E.indicator (1 : Rn n → ℝ)) x with hF_def
  set χ : ℕ → Rn n → ℝ := fun k y ↦ radialCutoff x r (e k) y * E.indicator 1 y with hχ_def
  set χ₀ : Rn n → ℝ := (E ∩ closedBall x r).indicator 1 with hχ₀_def
  -- the bound for each `k`
  have hbound : ∀ k, totalVariationOn univ (χ k) ≤ μ (closedBall x (r + e k)) +
      ENNReal.ofReal (∫ s in Ioi (0 : ℝ), scaledKernel r (e k) s * F s) := by
    intro k
    have hμk : μ (closedBall x (r + e k)) ≠ ⊤ :=
      (h.lt_top_of_isCompact _ (isCompact_closedBall _ _) (hBk k)).ne
    unfold totalVariationOn weightedTV
    refine iSup₂_le fun ψ hψ ↦ ?_
    obtain ⟨hψ1, hψc, -, hψη⟩ := hψ
    have hψ1' : ∀ y, ‖ψ y‖ ≤ 1 := fun y ↦ by simpa using hψη y
    set c := radialCutoff x r (e k) with hc_def
    have hc1 : ContDiff ℝ 1 c := (contDiff_radialCutoff hr (he k)).of_le (by simp)
    have htc : tsupport c ⊆ closedBall x (r + e k) := tsupport_radialCutoff_subset (he k)
    have hid := h.setIntegral_radialCutoff_add hΩ hr (he k) (hBk k) hψ1
    have hL : ∫ y in univ, χ k y * divergence ψ y = ∫ y in E, c y * divergence ψ y := by
      rw [Measure.restrict_univ, ← integral_indicator hE]
      congr 1
      funext y
      by_cases hy : y ∈ E <;> simp [hχ_def, hc_def, hy]
    -- the `μ` term
    have hμint : Integrable (fun y ↦ c y * ⟪ψ y, ν y⟫) μ := by
      have htΨ : tsupport (fun y ↦ c y • ψ y) ⊆ closedBall x (r + e k) :=
        (tsupport_smul_subset_left _ _).trans htc
      have := h.integrable_inner (hc1.continuous.smul hψ1.continuous)
        (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
          ((subset_tsupport _).trans htΨ)) (htΨ.trans (hBk k))
      simpa only [Pi.smul_apply', real_inner_smul_left] using this
    have hμ : ∫ y, c y * ⟪ψ y, ν y⟫ ∂μ ≤ μ.real (closedBall x (r + e k)) := by
      rw [← integral_indicator_one measurableSet_closedBall]
      refine integral_mono_ae hμint ((integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const hμk)) ?_
      filter_upwards [h.norm_normal] with y hy
      by_cases hyB : y ∈ closedBall x (r + e k)
      · rw [indicator_of_mem hyB, Pi.one_apply]
        calc c y * ⟪ψ y, ν y⟫ ≤ c y * 1 :=
              mul_le_mul_of_nonneg_left ((real_inner_le_norm _ _).trans
                (by rw [hy, mul_one]; exact hψ1' y)) (radialCutoff_nonneg y)
          _ ≤ 1 := by rw [mul_one]; exact radialCutoff_le_one y
      · rw [indicator_of_notMem hyB, hc_def, radialCutoff_of_ge (he k), zero_mul]
        rw [mem_closedBall, dist_eq_norm, not_le] at hyB
        exact hyB.le
    -- the kernel term
    have hb : Integrable fun y ↦ fderiv ℝ c y (ψ y) :=
      ((hc1.continuous_fderiv one_ne_zero).clm_apply hψ1.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (r + e k))
          fun y hy ↦ htc (support_fderiv_subset ℝ fun h0 ↦ hy (by simp [h0])))
    have hKint : Integrable fun y ↦ scaledKernel r (e k) ‖y - x‖ * E.indicator 1 y := by
      have hKc : Continuous fun y : Rn n ↦ scaledKernel r (e k) ‖y - x‖ :=
        (continuous_scaledKernel r (e k)).comp (continuous_id.sub continuous_const).norm
      refine Integrable.bdd_mul (c := 1) ?_ (measurable_const.indicator hE).aestronglyMeasurable
          (ae_of_all _ hχE) |>.congr (Eventually.of_forall fun y ↦ mul_comm _ _)
      refine hKc.integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (r + e k))
          fun y hy ↦ ?_)
      by_contra hyB
      rw [mem_closedBall, dist_eq_norm, not_le] at hyB
      exact hy (scaledKernel_eq_zero (he k) fun hs ↦ by linarith [hs.2])
    have hk : -∫ y in E, fderiv ℝ c y (ψ y) ≤
        ∫ s in Ioi (0 : ℝ), scaledKernel r (e k) s * F s := by
      rw [hF_def, ← integral_radial_mul_eq x hKint, ← integral_neg, ← integral_indicator hE]
      refine integral_mono (hb.neg.indicator hE) hKint fun y ↦ ?_
      by_cases hy : y ∈ E
      · simp only [indicator_of_mem hy, Pi.one_apply, mul_one, hc_def,
          fderiv_radialCutoff_apply hr (he k), neg_neg]
        refine mul_le_of_le_one_right (scaledKernel_nonneg (he k) _) ?_
        refine (real_inner_le_norm _ _).trans ?_
        calc ‖‖y - x‖⁻¹ • (y - x)‖ * ‖ψ y‖ ≤ 1 * 1 := by
              refine mul_le_mul ?_ (hψ1' y) (norm_nonneg _) zero_le_one
              rw [norm_smul, norm_inv, norm_norm]
              by_cases h0 : ‖y - x‖ = 0
              · simp [h0]
              · rw [inv_mul_cancel₀ h0]
          _ = 1 := one_mul 1
      · simp [hy]
    rw [hL]
    calc ENNReal.ofReal (∫ y in E, c y * divergence ψ y)
        ≤ ENNReal.ofReal (μ.real (closedBall x (r + e k)) +
            ∫ s in Ioi (0 : ℝ), scaledKernel r (e k) s * F s) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (μ.real (closedBall x (r + e k))) +
            ENNReal.ofReal (∫ s in Ioi (0 : ℝ), scaledKernel r (e k) s * F s) :=
          ENNReal.ofReal_add_le
      _ = _ := by rw [measureReal_def, ENNReal.ofReal_toReal hμk]
  -- `L¹` convergence `χ k → χ₀`
  have hχ_lim : ∀ y, Tendsto (fun k ↦ χ k y) atTop (𝓝 (χ₀ y)) := fun y ↦ by
    have := (tendsto_radialCutoff (x := x) (r := r) he he0 y).mul_const (E.indicator 1 y)
    convert this using 2
    by_cases hy1 : y ∈ E <;> by_cases hy2 : y ∈ closedBall x r <;> simp [hχ₀_def, hy1, hy2]
  have hχmeas : ∀ k, Measurable (χ k) := fun k ↦
    (contDiff_radialCutoff hr (he k)).continuous.measurable.mul
      (measurable_const.indicator hE)
  have hχ₀meas : Measurable χ₀ := measurable_const.indicator (hE.inter measurableSet_closedBall)
  have hconv : TendstoLpLoc 1 volume univ χ χ₀ atTop := by
    intro K _ _
    have hdom := tendsto_lintegral_of_dominated_convergence (μ := volume)
      (F := fun k y ↦ ‖χ k y - χ₀ y‖ₑ) (f := fun _ ↦ 0)
      ((closedBall x (r + δ)).indicator 1)
      (fun k ↦ ((hχmeas k).sub hχ₀meas).enorm)
      (fun k ↦ Eventually.of_forall fun y ↦ by
        change ‖χ k y - χ₀ y‖ₑ ≤ (closedBall x (r + δ)).indicator 1 y
        by_cases hyB : y ∈ closedBall x (r + δ)
        · rw [indicator_of_mem hyB, Pi.one_apply, ← ofReal_norm, ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 0 ≤ χ k y ∧ χ k y ≤ 1 := by
            simp only [hχ_def]
            by_cases hy : y ∈ E
            · simp [hy, radialCutoff_nonneg, radialCutoff_le_one]
            · simp [hy]
          have h2 : 0 ≤ χ₀ y ∧ χ₀ y ≤ 1 := by
            by_cases hy : y ∈ E ∩ closedBall x r <;> simp [hχ₀_def, hy]
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        · have hyB' := hyB
          rw [mem_closedBall, dist_eq_norm, not_le] at hyB'
          have hge : r + e k ≤ ‖y - x‖ := by linarith [heδ k]
          have h1 : χ k y = 0 := by
            simp only [hχ_def, radialCutoff_of_ge (he k) hge, zero_mul]
          have h2 : χ₀ y = 0 := indicator_of_notMem (fun hy ↦ hyB
            (closedBall_subset_closedBall (by linarith) hy.2)) _
          simp [h1, h2])
      (by
        rw [lintegral_indicator_one measurableSet_closedBall]
        exact measure_closedBall_lt_top.ne)
      (Eventually.of_forall fun y ↦ by
        have := ((hχ_lim y).sub_const (χ₀ y)).enorm
        simpa using this)
    rw [lintegral_zero] at hdom
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdom
      (fun _ ↦ zero_le) fun k ↦ ?_
    rw [eLpNorm_one_eq_lintegral_enorm ((hχmeas k).sub hχ₀meas).aestronglyMeasurable]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hbdd : ∀ g : Rn n → ℝ, Measurable g → (∀ y, ‖g y‖ ≤ 1) → LocallyIntegrableOn g univ :=
    fun g hg hg1 ↦ (locallyIntegrable_iff.2 fun K hK ↦ Measure.integrableOn_of_bounded
      hK.measure_lt_top.ne hg.aestronglyMeasurable (ae_of_all _ hg1)).locallyIntegrableOn univ
  have hχb : ∀ k y, ‖χ k y‖ ≤ 1 := fun k y ↦ by
    simp only [hχ_def, norm_mul, Real.norm_of_nonneg (radialCutoff_nonneg y)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (radialCutoff_le_one y)).trans (hχE y)
  have hχ₀b : ∀ y, ‖χ₀ y‖ ≤ 1 := fun y ↦ by
    by_cases hy : y ∈ E ∩ closedBall x r <;> simp [hχ₀_def, hy]
  have hlsc := weightedTV_le_liminf (U := univ) 1 χ χ₀
    (fun k ↦ hbdd _ (hχmeas k) (hχb k)) (hbdd _ hχ₀meas hχ₀b) hconv
  -- the limit of the bounds
  have hlimB : Tendsto (fun k ↦ μ (closedBall x (r + e k))) atTop (𝓝 (μ (closedBall x r))) := by
    have hanti : Antitone fun k ↦ closedBall x (r + e k) := fun i j hij ↦
      closedBall_subset_closedBall (by linarith [heanti hij])
    have hinter : ⋂ k, closedBall x (r + e k) = closedBall x r := by
      refine Subset.antisymm (fun y hy ↦ ?_)
        (subset_iInter fun k ↦ closedBall_subset_closedBall (by linarith [he k]))
      rw [mem_iInter] at hy
      rw [mem_closedBall]
      have : Tendsto (fun k ↦ r + e k) atTop (𝓝 (r + 0)) := tendsto_const_nhds.add he0
      rw [add_zero] at this
      exact ge_of_tendsto this (Eventually.of_forall fun k ↦ mem_closedBall.1 (hy k))
    have := tendsto_measure_iInter_atTop (μ := μ)
      (fun k ↦ measurableSet_closedBall.nullMeasurableSet) hanti
      ⟨0, (h.lt_top_of_isCompact _ (isCompact_closedBall _ _) (hBk 0)).ne⟩
    rwa [hinter] at this
  have hlimK : Tendsto (fun k ↦ ENNReal.ofReal
      (∫ s in Ioi (0 : ℝ), scaledKernel r (e k) s * F s)) atTop (𝓝 (ENNReal.ofReal (F r))) :=
    ENNReal.tendsto_ofReal ((hK hr).comp he0')
  have hlim := hlimB.add hlimK
  have h1 : totalVariationOn univ χ₀ ≤ μ (closedBall x r) + ENNReal.ofReal (F r) := by
    refine hlsc.trans ?_
    rw [← hlim.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hbound)
  have h2 : totalVariationOn univ ((E ∩ ball x r).indicator 1) = totalVariationOn univ χ₀ :=
    totalVariationOn_congr_ae (indicator_ae_eq_of_ae_eq_set ((EventuallyEqSet.refl _ E).inter
      (closedBall_ae_eq_ball_of (Measure.addHaar_sphere volume x r)).symm))
  have h3 : μ (closedBall x r) = μ (ball x r) := measure_congr (closedBall_ae_eq_ball_of hsph)
  rw [h2, ← h3]
  exact h1

/-- **(b), integral form.** `|E ∩ B_r(x)| = ∫_0^r F_{χ_E}(s) ds` for `r ≥ 0` (polar
coordinates). -/
theorem volume_inter_ball_toReal_eq_integral [NeZero n] (hE : MeasurableSet E) (x : Rn n)
    {r : ℝ} (hr : 0 ≤ r) :
    (volume (E ∩ ball x r)).toReal = ∫ s in (0 : ℝ)..r, sphereIntegral (E.indicator 1) x s := by
  have hfi : IntegrableOn (E.indicator (1 : Rn n → ℝ)) (ball x r) :=
    Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne
      (measurable_const.indicator hE).aestronglyMeasurable
      (ae_of_all _ fun y ↦ by by_cases hy : y ∈ E <;> simp [hy])
  rw [← integral_ball_eq hr hfi, integral_indicator_one hE, measureReal_def,
    Measure.restrict_apply hE]

/-- **(b), derivative.** `r ↦ |E ∩ B_r(x)|` is differentiable with derivative
`F_{χ_E}(r) = ℋ^{n-1}(E ∩ ∂B_r(x))` at a.e. `r > 0` (EG Lemma 5.3, step 2). -/
theorem hasDerivAt_volume_inter_ball_ae [NeZero n] (hE : MeasurableSet E) (x : Rn n) :
    ∀ᵐ r, 0 < r → HasDerivAt (fun r ↦ (volume (E ∩ ball x r)).toReal)
      (sphereIntegral (E.indicator 1) x r) r := by
  have hfi : ∀ R, IntegrableOn (E.indicator (1 : Rn n → ℝ)) (ball x R) := fun R ↦
    Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne
      (measurable_const.indicator hE).aestronglyMeasurable
      (ae_of_all _ fun y ↦ by by_cases hy : y ∈ E <;> simp [hy])
  have hN : ∀ N : ℕ, ∀ᵐ r, r ∈ uIcc 0 (N : ℝ) → ∀ c ∈ uIcc 0 (N : ℝ),
      HasDerivAt (fun r ↦ ∫ t in c..r, sphereIntegral (E.indicator 1) x t)
        (sphereIntegral (E.indicator 1) x r) r := fun N ↦
    (intervalIntegrable_sphereIntegral (Nat.cast_nonneg N) (hfi N)).ae_hasDerivAt_integral
  rw [← ae_all_iff] at hN
  filter_upwards [hN] with r hr hr0
  obtain ⟨N, hN⟩ := exists_nat_gt r
  have hmem : r ∈ uIcc 0 (N : ℝ) := by
    rw [uIcc_of_le (Nat.cast_nonneg N)]
    exact ⟨hr0.le, hN.le⟩
  refine (hr N hmem 0 left_mem_uIcc).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hr0] with s hs
  exact volume_inter_ball_toReal_eq_integral hE x (le_of_lt hs)

end Slicing

/-! ### Sphere integrals of indicators are Hausdorff measures -/

/-- `F_{χ_E}(r) = ℋ^{n-1}(E ∩ ∂B_r(x))` for `r > 0` (the identification of the sphere measure
with `ℋ^{n-1}⌊S^{n-1}` in `GMT/SphereMeasure.lean`, and scaling). -/
theorem sphereIntegral_indicator_eq_hausdorffN [NeZero n] {E : Set (Rn n)} (hE : MeasurableSet E)
    (x : Rn n) {r : ℝ} (hr : 0 < r) :
    sphereIntegral (E.indicator 1) x r = (hausdorffN n (n - 1) (E ∩ sphere x r)).toReal := by
  set A : Set (Rn n) := {z | x + r • z ∈ E} with hA_def
  have hAm : MeasurableSet A := hE.preimage (by fun_prop)
  have hS1 : MeasurableSet (sphere (0 : Rn n) 1) := isClosed_sphere.measurableSet
  -- the sphere integral
  have h1 : ∫ w, E.indicator (1 : Rn n → ℝ) (x + r • (w : Rn n)) ∂sphereMeasure n =
      (hausdorffN n (n - 1)).real (A ∩ sphere (0 : Rn n) 1) := by
    have hind : ∀ z : Rn n, E.indicator (1 : Rn n → ℝ) (x + r • z) = A.indicator 1 z := fun z ↦ by
      by_cases hz : x + r • z ∈ E
      · rw [indicator_of_mem hz, indicator_of_mem (show z ∈ A from hz)]
        rfl
      · rw [indicator_of_notMem hz, indicator_of_notMem (show z ∉ A from hz)]
    simp_rw [hind]
    rw [show (∫ w, A.indicator (1 : Rn n → ℝ) (w : Rn n) ∂sphereMeasure n) =
        ∫ z, A.indicator 1 z ∂((sphereMeasure n).map Subtype.val) from
        (integral_map measurable_subtype_coe.aemeasurable
          (measurable_const.indicator hAm).aestronglyMeasurable).symm,
      GMT.map_sphereMeasure_eq_hausdorffN, integral_indicator_one hAm, measureReal_def,
      Measure.restrict_apply hAm, measureReal_def]
  -- scaling
  have h2 : hausdorffN n (n - 1) (E ∩ sphere x r) =
      ENNReal.ofReal (r ^ (n - 1)) * hausdorffN n (n - 1) (A ∩ sphere (0 : Rn n) 1) := by
    have hmap := GMT.map_smul_sub_euclideanHausdorffMeasure (n := n) (n - 1) x hr
    rw [← GMT.hausdorffN_eq_euclideanHausdorffMeasure'] at hmap
    have := congrArg (fun m : Measure (Rn n) ↦ m (A ∩ sphere (0 : Rn n) 1)) hmap
    simp only [Measure.smul_apply, smul_eq_mul] at this
    rw [Measure.map_apply (by fun_prop) (hAm.inter hS1)] at this
    rw [← this]
    congr 1
    ext y
    rw [mem_preimage, mem_inter_iff, mem_inter_iff, hA_def, mem_ofPred_eq,
      mem_sphere_zero_iff_norm, mem_sphere, dist_eq_norm, smul_smul, mul_inv_cancel₀ hr.ne',
      one_smul, add_sub_cancel, norm_smul, norm_inv, Real.norm_of_nonneg hr.le]
    constructor
    · rintro ⟨hy, hyr⟩
      exact ⟨hy, by rw [hyr, inv_mul_cancel₀ hr.ne']⟩
    · rintro ⟨hy, hyr⟩
      rw [inv_mul_eq_div, div_eq_one_iff_eq hr.ne'] at hyr
      exact ⟨hy, hyr⟩
  rw [sphereIntegral, h1, h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    measureReal_def]

end GMTFoundations
