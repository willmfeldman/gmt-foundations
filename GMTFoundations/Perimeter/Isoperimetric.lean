/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.Mollify
import GMTFoundations.GMT.Polar
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The isoperimetric inequality

`volume_rpow_le_totalVariationOn` (Thm 5.11 (i) of L. C. Evans, R. F. Gariepy, *Measure Theory
and Fine Properties of Functions*, rev. ed., CRC Press, 2015 (EG), in total-variation form): for
`n ≥ 2` and a bounded measurable `F ⊆ ℝⁿ`,
`|F|^{(n-1)/n} ≤ C_n TV(F; ℝⁿ)`, where `TV(F; ℝⁿ) = totalVariationOn univ χ_F` and
`C_n = isoperimetricConst n` is Mathlib's Gagliardo–Nirenberg–Sobolev constant for `p = 1`.

## Proof (EG Thm 5.10 (i))

Let `u_k = χ_F ⋆ ρ_k` (`mollify`, `mollifierBump k`). Each `u_k` is smooth with compact support
(`F` is bounded), so Mathlib's GNS inequality `eLpNorm_le_eLpNorm_fderiv_one` gives
`‖u_k‖_{n/(n-1)} ≤ C_n ‖Du_k‖_{L¹}`, and `‖Du_k‖_{L¹} ≤ TV(F; ℝⁿ)` by the mollification estimate
(`lintegral_norm_fderiv_mollify_indicator_le_totalVariationOn`). Since `u_k → χ_F` a.e., Fatou
(`eLpNorm_lim_le_liminf_eLpNorm`) gives `‖χ_F‖_{n/(n-1)} ≤ C_n TV(F; ℝⁿ)`, and
`‖χ_F‖_{n/(n-1)} = |F|^{(n-1)/n}`.
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal ContDiff Convolution

public section

namespace GMTFoundations

variable {n : ℕ}

/-- The isoperimetric constant: Mathlib's Gagliardo–Nirenberg–Sobolev constant for `p = 1` on
`ℝⁿ`, with exponent `n/(n-1)`. -/
noncomputable def isoperimetricConst (n : ℕ) : ℝ≥0 :=
  eLpNormLESNormFDerivOneConst (volume : Measure (Rn n)) (NNReal.conjExponent n)

private theorem one_div_toReal_conjExponent (hn : 2 ≤ n) :
    1 / ((NNReal.conjExponent n : ℝ≥0) : ℝ≥0∞).toReal = ((n : ℝ) - 1) / n := by
  have h1 : (1 : ℝ≥0) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  rw [ENNReal.coe_toReal, NNReal.conjExponent, NNReal.coe_div, NNReal.coe_sub h1,
    NNReal.coe_natCast, NNReal.coe_one, one_div_div]

/-- **Isoperimetric inequality** (EG Thm 5.11 (i), TV form). For `n ≥ 2` and a bounded measurable
`F ⊆ ℝⁿ`: `|F|^{(n-1)/n} ≤ C_n TV(F; ℝⁿ)`. -/
theorem volume_rpow_le_totalVariationOn (hn : 2 ≤ n) {F : Set (Rn n)} (hF : MeasurableSet F)
    (hFb : Bornology.IsBounded F) :
    volume F ^ (((n : ℝ) - 1) / n) ≤
      isoperimetricConst n * totalVariationOn univ (F.indicator 1) := by
  set p : ℝ≥0 := NNReal.conjExponent n with hp_def
  have h1n : (1 : ℝ≥0) < n := by exact_mod_cast (by omega : 1 < n)
  have hp : NNReal.HolderConjugate (Module.finrank ℝ (Rn n)) p := by
    rw [finrank_Rn]
    exact NNReal.HolderConjugate.conjExponent h1n
  set u : ℕ → Rn n → ℝ := fun k ↦ mollify (mollifierBump k) (F.indicator 1) with hu_def
  have hli : LocallyIntegrable (F.indicator (1 : Rn n → ℝ)) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hF
  have hFc : HasCompactSupport (F.indicator (1 : Rn n → ℝ)) :=
    HasCompactSupport.of_support_subset_isCompact hFb.isCompact_closure
      (support_indicator_subset.trans subset_closure)
  have hbound : ∀ k, eLpNorm (u k) p volume ≤
      isoperimetricConst n * totalVariationOn univ (F.indicator 1) := by
    intro k
    have hcd : ContDiff ℝ 1 (u k) := (contDiff_mollify _ hli).of_le (by simp)
    have hcs : HasCompactSupport (u k) := hasCompactSupport_mollify _ hFc
    refine (eLpNorm_le_eLpNorm_fderiv_one volume hcd hcs hp).trans (mul_le_mul' (le_of_eq rfl) ?_)
    rw [eLpNorm_one_eq_lintegral_enorm (hcd.continuous_fderiv one_ne_zero).aestronglyMeasurable]
    have := lintegral_norm_fderiv_mollify_indicator_le_totalVariationOn isOpen_univ hF
      (mollifierBump k) MeasurableSet.univ (fun _ _ ↦ subset_univ _)
    rwa [Measure.restrict_univ] at this
  have hlim := ae_tendsto_mollify (l := atTop) tendsto_mollifierBump_rOut
    (Eventually.of_forall fun k ↦ mollifierBump_rOut_le k) hli
  have hmeas : ∀ k, AEStronglyMeasurable (u k) volume := fun k ↦
    (contDiff_mollify _ hli).continuous.aestronglyMeasurable
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := (p : ℝ≥0∞)) hmeas _
    (measurable_one.indicator hF).aestronglyMeasurable hlim
  have hind : eLpNorm (F.indicator (1 : Rn n → ℝ)) p volume =
      volume F ^ (((n : ℝ) - 1) / n) := by
    have hp0 : ((p : ℝ≥0∞)) ≠ 0 := by
      rw [ENNReal.coe_ne_zero]
      exact hp.symm.pos.ne'
    rw [show F.indicator (1 : Rn n → ℝ) = F.indicator fun _ ↦ (1 : ℝ) from rfl,
      eLpNorm_indicator_const hF.nullMeasurableSet hp0 ENNReal.coe_ne_top,
      one_div_toReal_conjExponent hn]
    simp
  rw [← hind]
  exact hFatou.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))

end GMTFoundations
