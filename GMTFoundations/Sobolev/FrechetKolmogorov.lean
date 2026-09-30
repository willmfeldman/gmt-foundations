/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Fréchet–Kolmogorov, necessity

In a finite-dimensional real normed space with an additive Haar measure, an `L¹`-convergent
sequence is uniformly `L¹`-continuous under translations:
`sup_n ∫ |f_n(x + h) - f_n(x)| dx → 0` as `h → 0`.

Proof: continuity of translation in `L¹` for a single function (approximate by a continuous
compactly supported function, `Integrable.exists_hasCompactSupport_integral_sub_le`, and use
continuity of parametric integrals over a compact set); then the triangle inequality
`T(a, h) ≤ 2 ‖a - b‖₁ + T(b, h)` with `b = f₀` for large `n`, and finitely many `n` separately.

## Main results

* `GMTFoundations.tendsto_integral_abs_translate_sub`
* `GMTFoundations.frechetKolmogorov_uniform_translation`
-/

@[expose] public noncomputable section

namespace GMTFoundations

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Triangle inequality for the `L¹` translation modulus:
`∫ |a(x+h) - a(x)| ≤ 2 ∫ |a - b| + ∫ |b(x+h) - b(x)|`. -/
theorem integral_abs_translate_sub_le (μ : Measure V) [μ.IsAddRightInvariant] {a b : V → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (h : V) :
    ∫ x, |a (x + h) - a x| ∂μ ≤
      2 * ∫ x, |a x - b x| ∂μ + ∫ x, |b (x + h) - b x| ∂μ := by
  have hab : Integrable (fun x ↦ |a x - b x|) μ := (ha.sub hb).abs
  have hab' : Integrable (fun x ↦ |a (x + h) - b (x + h)|) μ := hab.comp_add_right h
  have hbb : Integrable (fun x ↦ |b (x + h) - b x|) μ := ((hb.comp_add_right h).sub hb).abs
  have hshift : ∫ x, |a (x + h) - b (x + h)| ∂μ = ∫ x, |a x - b x| ∂μ :=
    integral_add_right_eq_self (fun x ↦ |a x - b x|) h
  calc ∫ x, |a (x + h) - a x| ∂μ
      ≤ ∫ x, (|a (x + h) - b (x + h)| + |b (x + h) - b x| + |a x - b x|) ∂μ := by
        refine integral_mono ((ha.comp_add_right h).sub ha).abs ((hab'.add hbb).add hab)
          fun x ↦ ?_
        have e : a (x + h) - a x = (a (x + h) - b (x + h)) + (b (x + h) - b x) - (a x - b x) := by
          ring
        rw [e]
        exact (abs_sub _ _).trans (by gcongr; exact abs_add_le _ _)
    _ = 2 * ∫ x, |a x - b x| ∂μ + ∫ x, |b (x + h) - b x| ∂μ := by
        have h1 : Integrable (fun x ↦ |a (x + h) - b (x + h)| + |b (x + h) - b x|) μ :=
          hab'.add hbb
        rw [integral_add h1 hab, integral_add hab' hbb, hshift]
        ring

/-- Continuity of translation in `L¹` for continuous compactly supported functions. -/
theorem tendsto_integral_abs_translate_sub_of_hasCompactSupport (μ : Measure V)
    [IsLocallyFiniteMeasure μ] {k : V → ℝ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    Tendsto (fun h ↦ ∫ x, |k (x + h) - k x| ∂μ) (𝓝 0) (𝓝 0) := by
  set s := cthickening 1 (tsupport k)
  have hs : IsCompact s := hkc.isCompact.cthickening
  have hF : Continuous (Function.uncurry fun (h x : V) ↦ |k (x + h) - k x|) :=
    ((hk.comp (continuous_snd.add continuous_fst)).sub (hk.comp continuous_snd)).abs
  have hG := (continuous_parametric_integral_of_continuous (μ := μ) hF hs).tendsto 0
  simp only [add_zero, sub_self, abs_zero, integral_zero] at hG
  refine hG.congr' (eventually_of_mem (ball_mem_nhds 0 one_pos) fun h hh ↦ ?_)
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
  have hx0 : k x = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦
    hx (self_subset_cthickening _ h')
  have hxh : k (x + h) = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hx
    (mem_cthickening_of_dist_le x (x + h) 1 _ h' (by
      rw [dist_self_add_right]
      exact (mem_ball_zero_iff.1 hh).le))
  simp [hx0, hxh]

/-- **Continuity of translation in `L¹`**: for integrable `g`,
`∫ |g(x + h) - g(x)| dμ → 0` as `h → 0`. -/
theorem tendsto_integral_abs_translate_sub (μ : Measure V) [μ.IsAddHaarMeasure] {g : V → ℝ}
    (hg : Integrable g μ) :
    Tendsto (fun h ↦ ∫ x, |g (x + h) - g x| ∂μ) (𝓝 0) (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha ↦ Eventually.of_forall fun h ↦ ha.trans_le
    (integral_nonneg fun x ↦ abs_nonneg _), fun ε hε ↦ ?_⟩
  obtain ⟨k, hkc, hgk, hk, hki⟩ :=
    hg.exists_hasCompactSupport_integral_sub_le (by positivity : 0 < ε / 4)
  filter_upwards [(tendsto_order.1 (tendsto_integral_abs_translate_sub_of_hasCompactSupport μ hk
    hkc)).2 (ε / 4) (by positivity)] with h hh
  have := integral_abs_translate_sub_le μ hg hki h
  simp only [Real.norm_eq_abs] at hgk
  linarith

/-- **Fréchet–Kolmogorov, necessity.** If `f_n → f₀` in `L¹(μ)`, then
`sup_n ∫ |f_n(x + h) - f_n(x)| dμ → 0` as `h → 0`. -/
theorem frechetKolmogorov_uniform_translation (μ : Measure V) [μ.IsAddHaarMeasure]
    (f : ℕ → V → ℝ) (f₀ : V → ℝ) (hf : ∀ n, Integrable (f n) μ) (hf₀ : Integrable f₀ μ)
    (hconv : Tendsto (fun n ↦ eLpNorm (f n - f₀) 1 μ) atTop (𝓝 0)) :
    ∀ δ > 0, ∃ ρ > 0, ∀ n, ∀ h : V, ‖h‖ < ρ →
      ∫ x, |f n (x + h) - f n x| ∂μ < δ := by
  intro δ hδ
  -- `∫ |f n - f₀| → 0`
  have hL1 : Tendsto (fun n ↦ ∫ x, |f n x - f₀ x| ∂μ) atTop (𝓝 0) := by
    have e : ∀ n, ∫ x, |f n x - f₀ x| ∂μ = (eLpNorm (f n - f₀) 1 μ).toReal := fun n ↦ by
      rw [eLpNorm_one_eq_lintegral_enorm ((hf n).sub hf₀).aestronglyMeasurable,
        ← integral_norm_eq_lintegral_enorm ((hf n).sub hf₀).aestronglyMeasurable]
      rfl
    simp_rw [e]
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hL1).2 (δ / 4) (by positivity))
  have h₀ := (tendsto_order.1 (tendsto_integral_abs_translate_sub μ hf₀)).2 (δ / 4)
    (by positivity)
  have hsmall : ∀ᶠ h in 𝓝 (0 : V), ∀ n ∈ Finset.range N, ∫ x, |f n (x + h) - f n x| ∂μ < δ :=
    (Finset.eventually_all _).2 fun n _ ↦
      (tendsto_order.1 (tendsto_integral_abs_translate_sub μ (hf n))).2 δ hδ
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (h₀.and hsmall)
  refine ⟨ρ, hρ, fun n h hh ↦ ?_⟩
  have hh' : dist h 0 < ρ := by rwa [dist_zero_right]
  obtain ⟨h1, h2⟩ := hball hh'
  rcases lt_or_ge n N with hn | hn
  · exact h2 n (Finset.mem_range.2 hn)
  · have := integral_abs_translate_sub_le μ (hf n) hf₀ h
    have := hN n hn
    linarith

end GMTFoundations
