/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.BV
public import GMTFoundations.Defs.Sobolev
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Order.LiminfLimsup
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Lower semicontinuity of the weighted total variation

The weighted total variation is defined by duality (no BV space type is built):
`weightedTV U η χ = sup {∫_U χ div ψ : ψ ∈ C¹_c(U; ℝᵈ), |ψ| ≤ η}`, a supremum of the functionals
`χ ↦ ofReal (∫_U χ div ψ)` over admissible test fields `ψ`. Each is continuous under `L¹_loc(U)`
convergence (`div ψ` is continuous with compact support in `U`), so the supremum is lower
semicontinuous. Same for the space-time version `weightedTVₓ` (spatial divergence). For `η = 1`
this is Evans–Gariepy, Thm 5.2.

## Main results

* `GMTFoundations.tendsto_setIntegral_mul_of_tendstoLpLoc`
* `GMTFoundations.weightedTV_le_liminf`
* `GMTFoundations.weightedTVₓ_le_liminf`

`IsTVTestField`, `weightedTV`, `IsTVTestFieldₓ`, `weightedTVₓ` and `divₓ` are defined in
`Defs/BV.lean`; the divergence is `GMTFoundations.divergence` (`Defs/Calculus.lean`).

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

@[expose] public noncomputable section

namespace GMTFoundations

/-- If `χ_i → χ₀` in `L¹_loc(Ω)` and `g` is continuous with compact support in `Ω`, then
`∫_Ω χ_i g → ∫_Ω χ₀ g`. -/
theorem tendsto_setIntegral_mul_of_tendstoLpLoc {X ι : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X] {μ : Measure X}
    [IsFiniteMeasureOnCompacts μ] {Ω : Set X} {l : Filter ι} {χ : ι → X → ℝ} {χ₀ : X → ℝ}
    (hχ : ∀ i, LocallyIntegrableOn (χ i) Ω μ) (hχ₀ : LocallyIntegrableOn χ₀ Ω μ)
    (hconv : TendstoLpLoc 1 μ Ω χ χ₀ l) {g : X → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ Ω) :
    Tendsto (fun i ↦ ∫ x in Ω, χ i x * g x ∂μ) l (𝓝 (∫ x in Ω, χ₀ x * g x ∂μ)) := by
  set K := tsupport g
  have hK : IsCompact K := hgc
  -- reduce both integrals to `K`
  have hred : ∀ f : X → ℝ, ∫ x in Ω, f x * g x ∂μ = ∫ x in K, f x * g x ∂μ := fun f ↦ by
    have hvan : ∀ x ∉ K, f x * g x = 0 := fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ hvan x fun h ↦ hx (hgΩ h),
      setIntegral_eq_integral_of_forall_compl_eq_zero hvan]
  simp_rw [hred]
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  have hint : ∀ {f : X → ℝ}, LocallyIntegrableOn f Ω μ →
      Integrable (fun x ↦ f x * g x) (μ.restrict K) := fun hf ↦
    (hf.integrableOn_compact_subset hgΩ hK).mul_bdd hg.aestronglyMeasurable
      (Eventually.of_forall hC)
  refine tendsto_integral_of_L1' _ (Eventually.of_forall fun i ↦ hint (hχ i)) ?_
  have hle : ∀ i, eLpNorm ((fun x ↦ χ i x * g x) - fun x ↦ χ₀ x * g x) 1 (μ.restrict K) ≤
      ENNReal.ofReal C * eLpNorm (χ i - χ₀) 1 (μ.restrict K) := fun i ↦ by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((hint (hχ i)).aestronglyMeasurable.sub (hint hχ₀).aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_) 1
    simp only [Pi.sub_apply, ← sub_mul, norm_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  have h0 := ENNReal.Tendsto.const_mul (hconv K hgΩ hK) (Or.inr (ENNReal.ofReal_ne_top (r := C)))
  rw [mul_zero] at h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ ↦ bot_le) hle

variable {d : ℕ}

theorem continuous_trace_clm :
    Continuous fun L : E d →L[ℝ] E d ↦ LinearMap.trace ℝ (E d) L.toLinearMap := by
  have : ContinuousSMul ℝ (E d) := IsBoundedSMul.continuousSMul
  have : ContinuousSMul ℝ (E d →L[ℝ] E d) := IsBoundedSMul.continuousSMul
  exact LinearMap.continuous_of_finiteDimensional
    ((LinearMap.trace ℝ (E d)).comp (ContinuousLinearMap.coeLM ℝ))

theorem continuous_divergence {ψ : E d → E d} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (divergence ψ) :=
  continuous_trace_clm.comp (hψ.continuous_fderiv one_ne_zero)

theorem tsupport_divergence_subset (ψ : E d → E d) : tsupport (divergence ψ) ⊆ tsupport ψ :=
  closure_minimal (fun x hx ↦ by
    by_contra h'
    exact hx (by simp [divergence, fderiv_of_notMem_tsupport ℝ h'])) (isClosed_tsupport _)

theorem fderivₓ_eq {ψ : E d × ℝ → E d} (hψ : Differentiable ℝ ψ) (p : E d × ℝ) :
    fderivₓ ψ p = (fderiv ℝ ψ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ) := by
  have : ContinuousSMul ℝ (E d) := IsBoundedSMul.continuousSMul
  have h : HasFDerivAt (fun y ↦ ψ (y, p.2))
      ((fderiv ℝ ψ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)) p.1 :=
    (hψ (p.1, p.2)).hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)
  exact h.fderiv

theorem continuous_divₓ {ψ : E d × ℝ → E d} (hψ : ContDiff ℝ 1 ψ) : Continuous (divₓ ψ) := by
  have h : divₓ ψ = fun p ↦ LinearMap.trace ℝ (E d)
      ((fderiv ℝ ψ p).comp (ContinuousLinearMap.inl ℝ (E d) ℝ)).toLinearMap := by
    funext p
    rw [divₓ, fderivₓ_eq (hψ.differentiable one_ne_zero)]
  rw [h]
  exact continuous_trace_clm.comp ((hψ.continuous_fderiv one_ne_zero).clm_comp continuous_const)

theorem tsupport_divₓ_subset {ψ : E d × ℝ → E d} (hψ : ContDiff ℝ 1 ψ) :
    tsupport (divₓ ψ) ⊆ tsupport ψ :=
  closure_minimal (fun p hp ↦ by
    by_contra h'
    exact hp (by simp [divₓ, fderivₓ_eq (hψ.differentiable one_ne_zero),
      fderiv_of_notMem_tsupport ℝ h'])) (isClosed_tsupport _)

/-- **Lower semicontinuity of the weighted total variation** under `L¹_loc` convergence
(Evans–Gariepy, Thm 5.2, for `η = 1`). -/
theorem weightedTV_le_liminf {ι : Type*} {l : Filter ι} {U : Set (E d)}
    (η : E d → ℝ) (χ : ι → E d → ℝ) (χ₀ : E d → ℝ) (hχ : ∀ i, LocallyIntegrableOn (χ i) U)
    (hχ₀ : LocallyIntegrableOn χ₀ U) (hconv : TendstoLpLoc 1 volume U χ χ₀ l) :
    weightedTV U η χ₀ ≤ liminf (fun i ↦ weightedTV U η (χ i)) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  refine iSup₂_le fun ψ hψ ↦ ?_
  obtain ⟨hψ1, hψc, hψU, hψη⟩ := hψ
  have hT := ENNReal.tendsto_ofReal (tendsto_setIntegral_mul_of_tendstoLpLoc hχ hχ₀ hconv
    (continuous_divergence hψ1) (hψc.mono' (subset_closure.trans (tsupport_divergence_subset ψ)))
    ((tsupport_divergence_subset ψ).trans hψU))
  rw [← hT.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun i ↦
    le_iSup₂ (f := fun ψ (_ : IsTVTestField U η ψ) ↦
      ENNReal.ofReal (∫ x in U, χ i x * divergence ψ x)) ψ ⟨hψ1, hψc, hψU, hψη⟩)

/-- **Lower semicontinuity of the space-time weighted spatial total variation** under
`L¹_loc` convergence. -/
theorem weightedTVₓ_le_liminf {ι : Type*} {l : Filter ι} {Ω : Set (E d × ℝ)}
    (η : E d × ℝ → ℝ) (χ : ι → E d × ℝ → ℝ) (χ₀ : E d × ℝ → ℝ)
    (hχ : ∀ i, LocallyIntegrableOn (χ i) Ω) (hχ₀ : LocallyIntegrableOn χ₀ Ω)
    (hconv : TendstoLpLoc 1 volume Ω χ χ₀ l) :
    weightedTVₓ Ω η χ₀ ≤ liminf (fun i ↦ weightedTVₓ Ω η (χ i)) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  refine iSup₂_le fun ψ hψ ↦ ?_
  obtain ⟨hψ1, hψc, hψΩ, hψη⟩ := hψ
  have hT := ENNReal.tendsto_ofReal (tendsto_setIntegral_mul_of_tendstoLpLoc hχ hχ₀ hconv
    (continuous_divₓ hψ1) (hψc.mono' (subset_closure.trans (tsupport_divₓ_subset hψ1)))
    ((tsupport_divₓ_subset hψ1).trans hψΩ))
  rw [← hT.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun i ↦
    le_iSup₂ (f := fun ψ (_ : IsTVTestFieldₓ Ω η ψ) ↦
      ENNReal.ofReal (∫ p in Ω, χ i p * divₓ ψ p)) ψ ⟨hψ1, hψc, hψΩ, hψη⟩)

end GMTFoundations
