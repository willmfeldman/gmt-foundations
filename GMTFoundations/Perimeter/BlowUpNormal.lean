/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.BlowUpScaling
import GMTFoundations.Perimeter.Mollify
import GMTFoundations.Perimeter.HalfSpace
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered

/-!
# The normal of a blow-up limit is constant (EG Thm 5.13, Claim #1)

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

Let `(μ, ν)` be a Gauss–Green pair of a measurable `E` on the open `Ω`, `x ∈ Ω`, with
`⨍_{B_r(x)} ν dμ → v`, `‖v‖ = 1`, and with the upper density bound `μ(B_r(x)) ≤ A r^{n-1}` for
`0 < r < r₀` (EG Lemma 5.3 (iv)). Let `s_k → 0+` with `χ_{E_k} → χ_F` in `L¹_loc(ℝⁿ)`, where
`E_k = E_{x,s_k}` (`BlowUpScaling.lean`), and let `(μ_F, ν_F)` be a Gauss–Green pair of `F` on
`ℝⁿ`. Then `ν_F = v` `μ_F`-a.e. (`ae_normal_eq_of_blowup_tendsto`).

## Proof (smooth-cutoff variant of EG's Claim #1)

EG pass to the limit in `∫_{B_L} ν_j d‖∂E_j‖` for the radii `L` with `‖∂F‖(∂B_L) = 0` (weak-*
convergence of vector measures and a Portmanteau argument). We test with a `C¹` cutoff
`0 ≤ ψ ≤ 1` supported in `B_R` instead (`blowup_cutoff_core`). With `μ_k, ν_k` the blown-up pair:
* `∫ ψ ⟪v, ν_k⟫ dμ_k = ∫_{E_k} div(ψ v) → ∫_F div(ψ v) = ∫ ψ ⟪v, ν_F⟫ dμ_F` (Gauss–Green for the
  `C¹` field `ψ v`, and `L¹_loc` convergence);
* `0 ≤ ∫ ψ (1 - ⟪v, ν_k⟫) dμ_k ≤ μ_k(B_R) (1 - ⟪v, ⨍_{B_R} ν_k dμ_k⟫) → 0`, since the averages
  are scale invariant (`blowup_average_ball`) and converge to `v`, and `μ_k(B_R) ≤ A R^{n-1}`;
* hence `∫ ψ dμ_k → ∫ ψ ⟪v, ν_F⟫ dμ_F`, and lower semicontinuity of the weighted total variation
  (`weightedTV_le_liminf` through `weightedTV_indicator_eq`) gives
  `∫ ψ dμ_F ≤ ∫ ψ ⟪v, ν_F⟫ dμ_F`.
Since `⟪v, ν_F⟫ ≤ 1`, this forces `⟪v, ν_F⟫ = 1` `μ_F`-a.e. where `ψ = 1`; exhaust `ℝⁿ` by balls.
The same computation then gives the mass convergence `∫ ψ dμ_k → ∫ ψ dμ_F`
(`tendsto_blowup_integral_cutoff`), used for EG Thm 5.14 (iii).

No rotation to `v = e_n` is needed: everything is stated for a general unit vector `v`.

## Claim #2

`ae_eq_halfSpace_of_blowup_tendsto` composes Claim #1 with
`ae_eq_halfSpace_of_isGaussGreenPair` (`HalfSpace.lean`): `F` is a.e. `∅`, `ℝⁿ` or `{⟪y, v⟫ ≤ γ}`.
`exists_blowup_subseq_halfSpace` packages steps 2–5 of EG Thm 5.13 (extraction, the limit pair,
Claims #1 and #2) for an arbitrary sequence of scales. Claim #3 (`γ = 0`, and the cases `∅`, `ℝⁿ`
excluded) needs the lower volume bounds EG Lemma 5.3 (i), (ii) and is in `BlowUp.lean`.
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

public section

namespace GMTFoundations

variable {n : ℕ}

theorem isOpen_blowupSet {Ω : Set (Rn n)} (hΩ : IsOpen Ω) (x : Rn n) (r : ℝ) :
    IsOpen (blowupSet x r Ω) :=
  hΩ.preimage (by fun_prop)

/-! ### The excess `∫ ψ (1 - ⟪v, ν⟫) dμ` -/

section Excess

variable {m : Measure (Rn n)} {ν : Rn n → Rn n}

/-- For a unit vector field `ν` (`m`-a.e.), a unit `v`, `0 ≤ ψ ≤ 1` and `m(U) < ∞`:
`0 ≤ ∫_U ψ (1 - ⟪v, ν⟫) dm ≤ m(U) - ⟪v, ∫_U ν dm⟫`. -/
theorem setIntegral_mul_one_sub_inner_le (hνm : Measurable ν) (hν1 : ∀ᵐ y ∂m, ‖ν y‖ = 1)
    {U : Set (Rn n)} (hU : m U < ⊤) {ψ : Rn n → ℝ} (hψm : Measurable ψ)
    (hψ01 : ∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) {v : Rn n} (hv : ‖v‖ = 1) :
    0 ≤ ∫ y in U, ψ y * (1 - ⟪v, ν y⟫) ∂m ∧
      ∫ y in U, ψ y * (1 - ⟪v, ν y⟫) ∂m ≤ (m U).toReal - ⟪v, ∫ y in U, ν y ∂m⟫ := by
  haveI : IsFiniteMeasure (m.restrict U) := isFiniteMeasure_restrict.2 hU.ne
  have hin : ∀ᵐ y ∂m, |⟪v, ν y⟫| ≤ 1 := by
    filter_upwards [hν1] with y hy
    exact (abs_real_inner_le_norm _ _).trans (by rw [hv, hy, one_mul])
  have hνi : Integrable ν (m.restrict U) :=
    (integrable_const (1 : ℝ)).mono' hνm.aestronglyMeasurable
      (ae_restrict_of_ae (hν1.mono fun y hy ↦ hy.le))
  have hinner : Integrable (fun y ↦ ⟪v, ν y⟫) (m.restrict U) := hνi.const_inner v
  have hone : Integrable (fun y ↦ 1 - ⟪v, ν y⟫) (m.restrict U) :=
    (integrable_const 1).sub hinner
  have hψb : ∀ y, ‖ψ y‖ ≤ 1 := fun y ↦ by
    rw [Real.norm_of_nonneg (hψ01 y).1]; exact (hψ01 y).2
  have hprod : Integrable (fun y ↦ ψ y * (1 - ⟪v, ν y⟫)) (m.restrict U) :=
    hone.bdd_mul hψm.aestronglyMeasurable (Eventually.of_forall hψb)
  refine ⟨integral_nonneg_of_ae (ae_restrict_of_ae (hin.mono fun y hy ↦ ?_)), ?_⟩
  · exact mul_nonneg (hψ01 y).1 (by linarith [le_abs_self ⟪v, ν y⟫])
  · calc ∫ y in U, ψ y * (1 - ⟪v, ν y⟫) ∂m ≤ ∫ y in U, (1 - ⟪v, ν y⟫) ∂m :=
          integral_mono_ae hprod hone (ae_restrict_of_ae (hin.mono fun y hy ↦ by
            have h1 : 0 ≤ 1 - ⟪v, ν y⟫ := by linarith [le_abs_self ⟪v, ν y⟫]
            exact mul_le_of_le_one_left h1 (hψ01 y).2))
      _ = (m U).toReal - ⟪v, ∫ y in U, ν y ∂m⟫ := by
          rw [integral_sub (integrable_const 1) hinner, integral_const, smul_eq_mul, mul_one,
            integral_inner hνi, measureReal_restrict_apply_univ, Measure.real]

/-- `m(U) - ⟪v, ∫_U ν dm⟫ = m(U) (1 - ⟪v, ⨍_U ν dm⟫)` (also when `m(U) = 0`). -/
theorem toReal_sub_inner_setIntegral_eq {U : Set (Rn n)} (hU : m U < ⊤) (v : Rn n) :
    (m U).toReal - ⟪v, ∫ y in U, ν y ∂m⟫ =
      (m U).toReal * (1 - ⟪v, (m U).toReal⁻¹ • ∫ y in U, ν y ∂m⟫) := by
  by_cases h0 : (m U).toReal = 0
  · have hmU : m U = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
      · exact h
      · exact absurd h hU.ne
    rw [Measure.restrict_eq_zero.2 hmU, integral_zero_measure, h0]
    simp
  · rw [inner_smul_right, mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

end Excess

/-! ### The cutoff computation -/

section Core

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- **The cutoff computation** (EG Thm 5.13, Claim #1, smooth-cutoff variant). In the setting of the
module docstring, for a `C¹` cutoff `0 ≤ ψ ≤ 1` with compact support in `B_R`:
`∫_{B_R} ψ dμ_k → ∫_{B_R} ψ ⟪v, ν_F⟫ dμ_F` and `∫_{B_R} ψ dμ_F ≤ ∫_{B_R} ψ ⟪v, ν_F⟫ dμ_F`. -/
theorem blowup_cutoff_core (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v))
    {A r₀ : ℝ} (hr₀ : 0 < r₀)
    (hup : ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) {F : Set (Rn n)}
    (hF : MeasurableSet F)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (blowupSet x (s k) E).indicator (1 : Rn n → ℝ))
      (F.indicator 1) atTop)
    {μF : Measure (Rn n)} {νF : Rn n → Rn n} (hpF : IsGaussGreenPair univ F μF νF)
    {R : ℝ} (hR : 0 < R) {ψ : Rn n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψR : tsupport ψ ⊆ ball 0 R) (hψ01 : ∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) :
    Tendsto (fun k ↦ ∫ y in ball 0 R, ψ y ∂blowupMeasure μ x (s k)) atTop
        (𝓝 (∫ y in ball 0 R, ψ y * ⟪v, νF y⟫ ∂μF)) ∧
      ∫ y in ball 0 R, ψ y ∂μF ≤ ∫ y in ball 0 R, ψ y * ⟪v, νF y⟫ ∂μF := by
  set U : Set (Rn n) := ball 0 R with hU_def
  set μk : ℕ → Measure (Rn n) := fun k ↦ blowupMeasure μ x (s k) with hμk_def
  set νk : ℕ → Rn n → Rn n := fun k z ↦ ν (x + s k • z) with hνk_def
  set Ek : ℕ → Set (Rn n) := fun k ↦ blowupSet x (s k) E with hEk_def
  have hpair : ∀ k, IsGaussGreenPair (blowupSet x (s k) Ω) (Ek k) (μk k) (νk k) := fun k ↦
    h.blowup' hn x (hs0 k)
  have hEkm : ∀ k, MeasurableSet (Ek k) := fun k ↦ measurableSet_blowupSet hE x (s k)
  have hev := eventually_closedBall_subset_blowupSet hΩ hx hs0 hs R
  have hψcont : Continuous ψ := hψ.continuous
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y ↦ (hψ01 y).1
  have hψU0 : ∀ y ∉ U, ψ y = 0 := fun y hy ↦
    image_eq_zero_of_notMem_tsupport fun h' ↦ hy (hψR h')
  -- the field `φ = ψ v`
  set φ : Rn n → Rn n := fun y ↦ ψ y • v with hφ_def
  have hφ : ContDiff ℝ 1 φ := hψ.smul contDiff_const
  have hφc : HasCompactSupport φ := hψc.smul_right
  have hφU : tsupport φ ⊆ U := (tsupport_smul_subset_left _ _).trans hψR
  have hinnerφ : ∀ w : Rn n → Rn n, (fun y ↦ ⟪φ y, w y⟫) = fun y ↦ ψ y * ⟪v, w y⟫ := fun w ↦ by
    funext y
    rw [hφ_def, real_inner_smul_left]
  -- Gauss–Green, restricted to `U`
  have hGG : ∀ {Ω' S : Set (Rn n)} {m : Measure (Rn n)} {w : Rn n → Rn n},
      IsGaussGreenPair Ω' S m w → IsOpen Ω' → U ⊆ Ω' →
      ∫ y in S, divergence φ y = ∫ y in U, ψ y * ⟪v, w y⟫ ∂m := by
    intro Ω' S m w hp hΩ' hUΩ'
    rw [hp.integral_divergence_of_contDiff hΩ' hφ hφc (hφU.trans hUΩ'), hinnerφ,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by rw [hψU0 y hy, zero_mul]]
  -- (a) `∫_U ψ ⟪v, ν_k⟫ dμ_k → T := ∫_U ψ ⟪v, ν_F⟫ dμ_F`
  set T := ∫ y in U, ψ y * ⟪v, νF y⟫ ∂μF with hT_def
  have hli : ∀ {S : Set (Rn n)}, MeasurableSet S →
      LocallyIntegrableOn (S.indicator (1 : Rn n → ℝ)) univ volume := fun hS ↦
    ((locallyIntegrable_const (1 : ℝ)).indicator hS).locallyIntegrableOn _
  have hTk : Tendsto (fun k ↦ ∫ y in U, ψ y * ⟪v, νk k y⟫ ∂μk k) atTop (𝓝 T) := by
    have hdiv := tendsto_setIntegral_mul_of_tendstoLpLoc (fun k ↦ hli (hEkm k)) (hli hF) hconv
      (continuous_divergence hφ)
      (hφc.mono' (subset_closure.trans (tsupport_divergence_subset φ))) (subset_univ _)
    simp_rw [setIntegral_indicator_mul_divergence (hEkm _) (subset_univ (tsupport φ)),
      setIntegral_indicator_mul_divergence hF (subset_univ (tsupport φ))] at hdiv
    rw [hGG hpF isOpen_univ (subset_univ _)] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [hev] with k hk
    exact hGG (hpair k) (isOpen_blowupSet hΩ x (s k)) (ball_subset_closedBall.trans hk)
  -- integrability, eventually
  have hint : ∀ᶠ k in atTop, Integrable ψ ((μk k).restrict U) ∧
      Integrable (fun y ↦ ψ y * ⟪v, νk k y⟫) ((μk k).restrict U) ∧ μk k U < ⊤ := by
    filter_upwards [hev] with k hk
    have hsub : tsupport ψ ⊆ blowupSet x (s k) Ω := hψR.trans (ball_subset_closedBall.trans hk)
    refine ⟨((hpair k).integrable_of_continuous hψcont hψc hsub).integrableOn, ?_, ?_⟩
    · have := (hpair k).integrable_inner hφ.continuous hφc (hφU.trans
        (ball_subset_closedBall.trans hk))
      rw [hinnerφ] at this
      exact this.integrableOn
    · exact (measure_mono ball_subset_closedBall).trans_lt
        ((hpair k).lt_top_of_isCompact _ (isCompact_closedBall _ _) hk)
  -- (b) the excess `e_k = ∫_U ψ dμ_k - ∫_U ψ ⟪v, ν_k⟫ dμ_k → 0`
  set a : ℕ → Rn n := fun k ↦ (μk k U).toReal⁻¹ • ∫ y in U, νk k y ∂μk k with ha_def
  have ha : Tendsto a atTop (𝓝 v) := tendsto_blowup_average_ball hlim hs0 hs hR
  have ha1 : Tendsto (fun k ↦ |1 - ⟪v, a k⟫|) atTop (𝓝 0) := by
    have : Tendsto (fun k ↦ ⟪v, a k⟫) atTop (𝓝 ⟪v, v⟫) := tendsto_const_nhds.inner ha
    rw [real_inner_self_eq_norm_sq, hv, one_pow] at this
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub this).abs
  set M := max (A * R ^ (n - 1)) 0 with hM_def
  have hexc : Tendsto (fun k ↦ ∫ y in U, ψ y ∂μk k - ∫ y in U, ψ y * ⟪v, νk k y⟫ ∂μk k) atTop
      (𝓝 0) := by
    have hup' := ha1.const_mul M
    rw [mul_zero] at hup'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup' ?_ ?_
    · filter_upwards [hint, hev, eventually_blowupMeasure_ball_le hr₀ hup hs0 hs hR]
        with k hk hkΩ hkμ
      obtain ⟨hi1, hi2, hfin⟩ := hk
      rw [← integral_sub hi1 hi2]
      simp_rw [← mul_one_sub]
      exact (setIntegral_mul_one_sub_inner_le (hpair k).measurable_normal (hpair k).norm_normal
        hfin hψcont.measurable hψ01 hv).1
    · filter_upwards [hint, hev, eventually_blowupMeasure_ball_le hr₀ hup hs0 hs hR]
        with k hk hkΩ hkμ
      obtain ⟨hi1, hi2, hfin⟩ := hk
      rw [← integral_sub hi1 hi2]
      simp_rw [← mul_one_sub]
      refine (setIntegral_mul_one_sub_inner_le (hpair k).measurable_normal (hpair k).norm_normal
        hfin hψcont.measurable hψ01 hv).2.trans ?_
      rw [toReal_sub_inner_setIntegral_eq hfin v]
      have hm0 : 0 ≤ (μk k U).toReal := ENNReal.toReal_nonneg
      have hmM : (μk k U).toReal ≤ M :=
        (ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
          (hkμ.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))))
      calc (μk k U).toReal * (1 - ⟪v, a k⟫) ≤ (μk k U).toReal * |1 - ⟪v, a k⟫| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hm0
        _ ≤ M * |1 - ⟪v, a k⟫| := mul_le_mul_of_nonneg_right hmM (abs_nonneg _)
  -- (c) `∫_U ψ dμ_k → T`
  have hP : Tendsto (fun k ↦ ∫ y in U, ψ y ∂μk k) atTop (𝓝 T) := by
    have := hTk.add hexc
    rw [add_zero] at this
    exact this.congr fun k ↦ by ring
  refine ⟨hP, ?_⟩
  -- (d) lower semicontinuity
  have hT0 : 0 ≤ T :=
    ge_of_tendsto hP (Eventually.of_forall fun k ↦ integral_nonneg fun y ↦ hψ0 y)
  have hlsc := weightedTV_le_liminf (U := U) ψ (fun k ↦ (Ek k).indicator (1 : Rn n → ℝ))
    (F.indicator 1) (fun k ↦ (hli (hEkm k)).mono_set (subset_univ _))
    ((hli hF).mono_set (subset_univ _)) (fun K _ hK ↦ hconv K (subset_univ K) hK)
  rw [hpF.weightedTV_indicator_eq hF isOpen_ball (subset_univ _) hψcont hψ0,
    ← ofReal_integral_eq_lintegral_ofReal
      (hpF.integrable_of_continuous hψcont hψc (subset_univ _)).integrableOn
      (Eventually.of_forall hψ0)] at hlsc
  have hliminf : liminf (fun k ↦ weightedTV U ψ ((Ek k).indicator (1 : Rn n → ℝ))) atTop =
      ENNReal.ofReal T := by
    have h1 : (fun k ↦ weightedTV U ψ ((Ek k).indicator (1 : Rn n → ℝ))) =ᶠ[atTop]
        fun k ↦ ENNReal.ofReal (∫ y in U, ψ y ∂μk k) := by
      filter_upwards [hev, hint] with k hk hki
      rw [(hpair k).weightedTV_indicator_eq (hEkm k) isOpen_ball
        (ball_subset_closedBall.trans hk) hψcont hψ0,
        ← ofReal_integral_eq_lintegral_ofReal hki.1 (Eventually.of_forall hψ0)]
    rw [liminf_congr h1, (ENNReal.tendsto_ofReal hP).liminf_eq]
  rw [hliminf] at hlsc
  exact (ENNReal.ofReal_le_ofReal_iff hT0).1 hlsc

/-- **EG Thm 5.13, Claim #1: the normal of a blow-up limit is constant.** Let `(μ, ν)` be a
Gauss–Green pair of a measurable `E` on the open `Ω`, `x ∈ Ω`, with normal averages
`⨍_{B_r(x)} ν dμ → v`, `‖v‖ = 1`, and with the upper density bound
`μ(B_r(x)) ≤ A r^{n-1}` for `0 < r < r₀` (EG Lemma 5.3 (iv)). If `s_k → 0+`,
`χ_{E_{x,s_k}} → χ_F` in `L¹_loc(ℝⁿ)` and `(μ_F, ν_F)` is a Gauss–Green pair of `F` on `ℝⁿ`, then
`ν_F = v` `μ_F`-a.e. -/
theorem ae_normal_eq_of_blowup_tendsto (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v))
    (hup : ∃ A r₀, 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) {F : Set (Rn n)}
    (hF : MeasurableSet F)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (blowupSet x (s k) E).indicator (1 : Rn n → ℝ))
      (F.indicator 1) atTop)
    {μF : Measure (Rn n)} {νF : Rn n → Rn n} (hpF : IsGaussGreenPair univ F μF νF) :
    ∀ᵐ y ∂μF, νF y = v := by
  obtain ⟨A, r₀, hr₀, hup⟩ := hup
  -- `⟪v, ν_F⟫ = 1` a.e. on each ball `B_{m+1}`
  have hball : ∀ m : ℕ, ∀ᵐ y ∂μF.restrict (ball 0 ((m : ℝ) + 1)), ⟪v, νF y⟫ = 1 := by
    intro m
    set R : ℝ := (m : ℝ) + 3 with hR_def
    have hR : 0 < R := by positivity
    let ψ : ContDiffBump (0 : Rn n) := ⟨(m : ℝ) + 1, (m : ℝ) + 2, by positivity, by linarith⟩
    have hψR : tsupport ψ ⊆ ball 0 R := by
      rw [ψ.tsupport_eq]
      exact closedBall_subset_ball (by change (m : ℝ) + 2 < R; linarith)
    obtain ⟨-, hle⟩ := blowup_cutoff_core hn hΩ hE h hx hv hlim hr₀ hup hs0 hs hF hconv hpF hR
      ψ.contDiff ψ.hasCompactSupport hψR fun y ↦ ⟨ψ.nonneg, ψ.le_one⟩
    have hint : Integrable (fun y ↦ ψ y) (μF.restrict (ball 0 R)) :=
      (hpF.integrable_of_continuous ψ.continuous ψ.hasCompactSupport (subset_univ _)).integrableOn
    have hint2 : Integrable (fun y ↦ ψ y * ⟪v, νF y⟫) (μF.restrict (ball 0 R)) := by
      have := hpF.integrable_inner (φ := fun y ↦ ψ y • v) (ψ.continuous.smul continuous_const)
        ψ.hasCompactSupport.smul_right (subset_univ _)
      simp_rw [real_inner_smul_left] at this
      exact this.integrableOn
    have hnn : 0 ≤ᵐ[μF.restrict (ball 0 R)] fun y ↦ ψ y * (1 - ⟪v, νF y⟫) := by
      refine ae_restrict_of_ae (hpF.norm_normal.mono fun y hy ↦ ?_)
      have : ⟪v, νF y⟫ ≤ 1 :=
        (real_inner_le_norm _ _).trans (by rw [hv, hy, one_mul])
      exact mul_nonneg ψ.nonneg (by linarith)
    have hzero : ∫ y in ball 0 R, ψ y * (1 - ⟪v, νF y⟫) ∂μF = 0 := by
      refine le_antisymm ?_ (integral_nonneg_of_ae hnn)
      simp_rw [mul_one_sub]
      rw [integral_sub hint hint2]
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn (hint.sub hint2 |>.congr
      (Eventually.of_forall fun y ↦ by simp [mul_one_sub]))).1 hzero
    have hsub : ball (0 : Rn n) ((m : ℝ) + 1) ⊆ ball 0 R :=
      ball_subset_ball (by rw [hR_def]; linarith)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hae,
      ae_restrict_mem measurableSet_ball] with y hy hyB
    have hψ1 : ψ y = 1 := ψ.one_of_mem_closedBall (ball_subset_closedBall hyB)
    simp only [Pi.zero_apply, hψ1, one_mul] at hy
    linarith
  have hall : ∀ᵐ y ∂μF, ⟪v, νF y⟫ = 1 := by
    have hU : (⋃ m : ℕ, ball (0 : Rn n) ((m : ℝ) + 1)) = univ :=
      eq_univ_of_forall fun y ↦ mem_iUnion.2 ⟨⌈‖y‖⌉₊, by
        rw [mem_ball, dist_zero_right]
        exact (Nat.le_ceil _).trans_lt (lt_add_one _)⟩
    rw [← Measure.restrict_univ (μ := μF), ← hU, ae_restrict_iUnion_iff]
    exact hball
  filter_upwards [hall, hpF.norm_normal] with y hy hy1
  have : ‖νF y - v‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hy1, hv, real_inner_comm, hy]
    norm_num
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

/-- **Mass convergence against cutoffs** (EG Thm 5.13, end of Claim #1). In the setting of
`ae_normal_eq_of_blowup_tendsto`, for a `C¹` cutoff `0 ≤ ψ ≤ 1` with compact support in `B_R`:
`∫_{B_R} ψ dμ_{x,s_k} → ∫_{B_R} ψ dμ_F`. -/
theorem tendsto_blowup_integral_cutoff (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v))
    (hup : ∃ A r₀, 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) {F : Set (Rn n)}
    (hF : MeasurableSet F)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (blowupSet x (s k) E).indicator (1 : Rn n → ℝ))
      (F.indicator 1) atTop)
    {μF : Measure (Rn n)} {νF : Rn n → Rn n} (hpF : IsGaussGreenPair univ F μF νF)
    {R : ℝ} (hR : 0 < R) {ψ : Rn n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψR : tsupport ψ ⊆ ball 0 R) (hψ01 : ∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) :
    Tendsto (fun k ↦ ∫ y in ball 0 R, ψ y ∂blowupMeasure μ x (s k)) atTop
      (𝓝 (∫ y in ball 0 R, ψ y ∂μF)) := by
  have hνF := ae_normal_eq_of_blowup_tendsto hn hΩ hE h hx hv hlim hup hs0 hs hF hconv hpF
  obtain ⟨A, r₀, hr₀, hup'⟩ := hup
  have hlimit := (blowup_cutoff_core hn hΩ hE h hx hv hlim hr₀ hup' hs0 hs hF hconv hpF hR hψ hψc
    hψR hψ01).1
  convert hlimit using 2
  refine integral_congr_ae (ae_restrict_of_ae (hνF.mono fun y hy ↦ ?_))
  simp only [hy, real_inner_self_eq_norm_sq, hv, one_pow, mul_one]

/-- **EG Thm 5.13, Claim #2.** In the setting of `ae_normal_eq_of_blowup_tendsto`, the limit `F`
is a.e. empty, a.e. all of `ℝⁿ`, or a.e. a half-space `{⟪y, v⟫ ≤ γ}`
(`ae_eq_halfSpace_of_isGaussGreenPair`). EG's step 5 concludes `F = {y_n ≤ γ}` with `γ ∈ ℝ`,
but the argument also allows `F = ∅` or `F = ℝⁿ` (`γ = ±∞`), so we keep these cases. They and
`γ ≠ 0` are excluded by Claim #3, from the lower volume bounds EG Lemma 5.3 (i), (ii). -/
theorem ae_eq_halfSpace_of_blowup_tendsto (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v))
    (hup : ∃ A r₀, 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) {F : Set (Rn n)}
    (hF : MeasurableSet F)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (blowupSet x (s k) E).indicator (1 : Rn n → ℝ))
      (F.indicator 1) atTop)
    {μF : Measure (Rn n)} {νF : Rn n → Rn n} (hpF : IsGaussGreenPair univ F μF νF) :
    F =ᵐ[volume] (∅ : Set (Rn n)) ∨ F =ᵐ[volume] (univ : Set (Rn n)) ∨
      ∃ γ : ℝ, F =ᵐ[volume] {y : Rn n | ⟪y, v⟫ ≤ γ} :=
  ae_eq_halfSpace_of_isGaussGreenPair hpF hF hv
    (ae_normal_eq_of_blowup_tendsto hn hΩ hE h hx hv hlim hup hs0 hs hF hconv hpF)

/-- **Blow-up subsequences** (EG Thm 5.13, steps 2–5). Under the hypotheses of
`HalfSpaceBlowUpStatement` and the upper density bound (EG Lemma 5.3 (iv)), every sequence of
scales `s_k → 0+` has a subsequence along which `χ_{E_{x,s_k}}` converges in `L¹_loc(ℝⁿ)` to
`χ_F`, where `F` has a Gauss–Green pair on `ℝⁿ` with normal `v` and `F` is a.e. `∅`, `ℝⁿ` or a
half-space `{⟪y, v⟫ ≤ γ}`. -/
theorem exists_blowup_subseq_halfSpace (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v))
    (hup : ∃ A r₀, 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : Set (Rn n), MeasurableSet F ∧
      TendstoLpLoc 1 volume univ (fun k ↦ (blowupSet x (s (φ k)) E).indicator (1 : Rn n → ℝ))
        (F.indicator 1) atTop ∧
      (∃ μF νF, IsGaussGreenPair univ F μF νF ∧ (∀ᵐ y ∂μF, νF y = v)) ∧
      (F =ᵐ[volume] (∅ : Set (Rn n)) ∨ F =ᵐ[volume] (univ : Set (Rn n)) ∨
        ∃ γ : ℝ, F =ᵐ[volume] {y : Rn n | ⟪y, v⟫ ≤ γ}) := by
  obtain ⟨φ, hφ, F, hF, hconv⟩ := exists_blowup_subseq_tendstoLpLoc hn hΩ hE h hx hup hs0 hs
  have hs0' : ∀ k, 0 < (s ∘ φ) k := fun k ↦ hs0 _
  have hs' : Tendsto (s ∘ φ) atTop (𝓝 0) := hs.comp hφ.tendsto_atTop
  obtain ⟨A, r₀, hr₀, hup'⟩ := hup
  obtain ⟨μF, νF, hpF, -⟩ := exists_isGaussGreenPair_of_blowup_tendsto hn hΩ hE h hx hr₀ hup'
    hs0' hs' hF hconv
  refine ⟨φ, hφ, F, hF, hconv, ⟨μF, νF, hpF, ?_⟩, ?_⟩
  · exact ae_normal_eq_of_blowup_tendsto hn hΩ hE h hx hv hlim ⟨A, r₀, hr₀, hup'⟩ hs0' hs' hF
      hconv hpF
  · exact ae_eq_halfSpace_of_blowup_tendsto hn hΩ hE h hx hv hlim ⟨A, r₀, hr₀, hup'⟩ hs0' hs' hF
      hconv hpF

end Core

end GMTFoundations
