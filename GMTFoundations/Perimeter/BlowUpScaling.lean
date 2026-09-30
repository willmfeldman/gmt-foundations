/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.GaussGreenPair
public import GMTFoundations.BV.Compactness
import GMTFoundations.Perimeter.Mollify
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Blow-ups at a point: rescaling bookkeeping and compactness

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

EG Thm 5.13, steps 1–3. For a Gauss–Green pair `(μ, ν)` of `E` on `Ω`, a point `x`
and a scale `r > 0`, the blow-up `E_{x,r} = {z : x + r z ∈ E}` has the Gauss–Green pair
`(μ_{x,r}, ν(x + r ·))` on `Ω_{x,r}`, with `μ_{x,r} = r^{-(n-1)} (z ↦ (z - x)/r)_# μ`
(`IsGaussGreenPair.blowup`).

## Main results

* `blowupMeasure_ball`: `μ_{x,r}(B_L) = r^{-(n-1)} μ(B_{rL}(x))` (EG (⋆⋆⋆) in step 4 of the proof
  of Thm 5.13, first line).
* `blowupMeasure_ball_le`: an upper density bound `μ(B_s(x)) ≤ A s^{n-1}` for `s < r₀`
  (EG Lemma 5.3 (iv)) gives `μ_{x,r}(B_L) ≤ A L^{n-1}` for `rL < r₀`.
* `blowup_average_ball`: the normal averages are scale invariant,
  `⨍_{B_L} ν(x + r ·) dμ_{x,r} = ⨍_{B_{rL}(x)} ν dμ` (EG (⋆⋆⋆), second line), and
  `tendsto_blowup_average_ball`: along scales `s_k → 0` they converge to the limit `v` of the
  averages at `x`.
* `exists_blowup_subseq_tendstoLpLoc` (EG step 3): for scales `s_k → 0`, a subsequence of
  `χ_{E_{x,s_k}}` converges in `L¹_loc(ℝⁿ)` to the indicator of a measurable set `F`.

## The compactness step

EG bound `‖∂(E_r ∩ B_L)‖` through Lemma 5.3 (v) (slicing). We avoid slicing. For a fixed scale
`s_k`, the blow-up `E_k` is only controlled on `Ω_k ⊇ B_{ρ/s_k}`, so for a fixed bounded open `V`
finitely many terms of the sequence may have infinite total variation on `V`. We therefore apply
the BV compactness theorem (EG Thm 5.5; `exists_tendstoLpLoc_subseq_of_TV`) to `ζ_k χ_{E_k}`,
where `ζ_k` is a smooth bump equal to `1` on `B_{ρ/(2 s_k)}` with support in `B̄_{ρ/s_k}`:
* on `V ⊆ B_L`, `ζ_k χ_{E_k} = χ_{E_k}` once `ρ/(2 s_k) > L`, and then
  `TV_V = μ_k(V) ≤ A L^{n-1}`;
* each of the finitely many remaining terms has finite total variation
  (`totalVariationOn_mul_le`: `TV(ζχ) ≤ TV_W(χ) + ‖∇ζ‖_∞ |supp ζ|`).
The limit `χ₀` takes values in `{0, 1}` a.e. (a.e. convergence of a subsequence on each ball), so it
is the indicator of `F = {χ₀ = 1}`; and `ζ_k χ_{E_k} = χ_{E_k}` eventually on each compact set.
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### Blow-up measures -/

section Scaling

/-- The rescaled measure `μ_{x,r} = r^{-(n-1)} (y ↦ (y - x)/r)_# μ` of
`IsGaussGreenPair.blowup`. -/
@[expose] noncomputable def blowupMeasure (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) :
    Measure (Rn n) :=
  (ENNReal.ofReal (r ^ (n - 1)))⁻¹ • μ.map fun y ↦ r⁻¹ • (y - x)

/-- The blown-up set `E_{x,r} = {z : x + r z ∈ E}`. -/
@[expose] def blowupSet (x : Rn n) (r : ℝ) (E : Set (Rn n)) : Set (Rn n) :=
  (fun z ↦ x + r • z) ⁻¹' E

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- `IsGaussGreenPair.blowup`, in the notation of this file. -/
theorem IsGaussGreenPair.blowup' (hn : 1 ≤ n) (h : IsGaussGreenPair Ω E μ ν) (x : Rn n) {r : ℝ}
    (hr : 0 < r) :
    IsGaussGreenPair (blowupSet x r Ω) (blowupSet x r E) (blowupMeasure μ x r)
      (fun z ↦ ν (x + r • z)) :=
  h.blowup hn x hr

theorem measurableSet_blowupSet (hE : MeasurableSet E) (x : Rn n) (r : ℝ) :
    MeasurableSet (blowupSet x r E) :=
  (measurable_const_add x |>.comp (measurable_const_smul r)) hE

theorem mem_blowupSet {x : Rn n} {r : ℝ} {z : Rn n} : z ∈ blowupSet x r E ↔ x + r • z ∈ E :=
  Iff.rfl

/-- `B_L ⊆ Ω_{x,r}` as soon as `B_{rL}(x) ⊆ Ω`. -/
theorem ball_subset_blowupSet {x : Rn n} {r L : ℝ} (hr : 0 < r) (h : ball x (r * L) ⊆ Ω) :
    ball 0 L ⊆ blowupSet x r Ω := by
  intro z hz
  apply h
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
  rw [mem_ball, dist_zero_right] at hz
  exact mul_lt_mul_of_pos_left hz hr

theorem closedBall_subset_blowupSet {x : Rn n} {r L : ℝ} (hr : 0 < r)
    (h : closedBall x (r * L) ⊆ Ω) : closedBall 0 L ⊆ blowupSet x r Ω := by
  intro z hz
  apply h
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
  rw [mem_closedBall, dist_zero_right] at hz
  exact mul_le_mul_of_nonneg_left hz hr.le

theorem preimage_ball_blowup (x : Rn n) {r : ℝ} (hr : 0 < r) (L : ℝ) :
    (fun y ↦ r⁻¹ • (y - x)) ⁻¹' ball (0 : Rn n) L = ball x (r * L) := by
  ext y
  simp only [mem_preimage, mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr]
  rw [inv_mul_lt_iff₀ hr]

theorem measurable_blowupInv (x : Rn n) (r : ℝ) : Measurable fun y : Rn n ↦ r⁻¹ • (y - x) := by
  fun_prop

/-- `μ_{x,r}(B_L) = r^{-(n-1)} μ(B_{rL}(x))` (EG (⋆⋆⋆)). -/
theorem blowupMeasure_ball (μ : Measure (Rn n)) (x : Rn n) {r : ℝ} (hr : 0 < r) (L : ℝ) :
    blowupMeasure μ x r (ball 0 L) = (ENNReal.ofReal (r ^ (n - 1)))⁻¹ * μ (ball x (r * L)) := by
  rw [blowupMeasure, Measure.smul_apply, Measure.map_apply (measurable_blowupInv x r)
    measurableSet_ball, preimage_ball_blowup x hr, smul_eq_mul]

/-- **Upper bound for the blow-ups.** If `μ(B_s(x)) ≤ A s^{n-1}` for `0 < s < r₀` (EG Lemma 5.3
(iv)), then `μ_{x,r}(B_L) ≤ A L^{n-1}` whenever `0 < rL < r₀`. -/
theorem blowupMeasure_ball_le {x : Rn n} {A r₀ : ℝ}
    (hup : ∀ s, 0 < s → s < r₀ → μ (ball x s) ≤ ENNReal.ofReal (A * s ^ (n - 1)))
    {r L : ℝ} (hr : 0 < r) (hL : 0 < L) (hrL : r * L < r₀) :
    blowupMeasure μ x r (ball 0 L) ≤ ENNReal.ofReal (A * L ^ (n - 1)) := by
  rw [blowupMeasure_ball μ x hr]
  have hpos : 0 < ENNReal.ofReal (r ^ (n - 1)) := ENNReal.ofReal_pos.2 (by positivity)
  rw [ENNReal.inv_mul_le_iff hpos.ne' ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul (by positivity)]
  refine (hup _ (mul_pos hr hL) hrL).trans (le_of_eq ?_)
  congr 1
  rw [mul_pow]
  ring

/-- `∫_{B_L} ν(x + r ·) dμ_{x,r} = r^{-(n-1)} ∫_{B_{rL}(x)} ν dμ` (EG (⋆⋆⋆)). -/
theorem setIntegral_blowupMeasure_ball (μ : Measure (Rn n)) (ν : Rn n → Rn n) (x : Rn n) {r : ℝ}
    (hr : 0 < r) (L : ℝ) :
    ∫ z in ball 0 L, ν (x + r • z) ∂blowupMeasure μ x r =
      (r ^ (n - 1))⁻¹ • ∫ y in ball x (r * L), ν y ∂μ := by
  have hemb : MeasurableEmbedding fun y : Rn n ↦ r⁻¹ • (y - x) := by
    have : (fun y : Rn n ↦ r⁻¹ • (y - x)) =
        ⇑((Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))) := by
      funext y
      simp [sub_eq_add_neg]
    rw [this]
    exact Homeomorph.measurableEmbedding _
  rw [blowupMeasure, Measure.restrict_smul, integral_smul_measure,
    Measure.restrict_map (measurable_blowupInv x r) measurableSet_ball,
    hemb.integral_map, preimage_ball_blowup x hr, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity)]
  congr 2
  funext y
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]

/-- **The normal averages are scale invariant** (EG (⋆⋆⋆)):
`⨍_{B_L} ν(x + r ·) dμ_{x,r} = ⨍_{B_{rL}(x)} ν dμ`, in the `toReal⁻¹ • ∫` form used in
the definition of `reducedBoundary`. -/
theorem blowup_average_ball (μ : Measure (Rn n)) (ν : Rn n → Rn n) (x : Rn n) {r : ℝ}
    (hr : 0 < r) (L : ℝ) :
    (blowupMeasure μ x r (ball 0 L)).toReal⁻¹ •
        ∫ z in ball 0 L, ν (x + r • z) ∂blowupMeasure μ x r =
      (μ (ball x (r * L))).toReal⁻¹ • ∫ y in ball x (r * L), ν y ∂μ := by
  rw [blowupMeasure_ball μ x hr, setIntegral_blowupMeasure_ball μ ν x hr, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity), smul_smul, mul_inv, inv_inv]
  congr 1
  have : r ^ (n - 1) ≠ 0 := by positivity
  field_simp

/-- Along scales `s_k → 0+`, the blown-up normal averages over `B_L` converge to the limit `v` of
the normal averages at `x`. -/
theorem tendsto_blowup_average_ball {x v : Rn n}
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0) (𝓝 v))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) {L : ℝ} (hL : 0 < L) :
    Tendsto (fun k ↦ (blowupMeasure μ x (s k) (ball 0 L)).toReal⁻¹ •
      ∫ z in ball 0 L, ν (x + s k • z) ∂blowupMeasure μ x (s k)) atTop (𝓝 v) := by
  simp_rw [blowup_average_ball μ ν x (hs0 _) L]
  refine hlim.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ ?_⟩)
  · simpa using hs.mul_const L
  · exact mul_pos (hs0 k) hL

end Scaling

/-! ### Compactness of blow-ups -/

section Compactness

/-- `TV_V` only depends on the values on `V`. -/
theorem totalVariationOn_congr_of_eqOn {V : Set (Rn n)} (hV : MeasurableSet V) {f g : Rn n → ℝ}
    (hfg : EqOn f g V) : totalVariationOn V f = totalVariationOn V g := by
  unfold totalVariationOn weightedTV
  congr 1
  ext ψ
  congr 1
  ext _
  congr 1
  exact setIntegral_congr_fun hV fun y hy ↦ by simp only [hfg hy]

/-- **Total variation of a cut-off function.** For `|χ| ≤ 1`, a `C¹` cutoff `0 ≤ ζ ≤ 1` with
compact support in the open set `W` and `‖Dζ‖ ≤ Z`:
`TV_V(ζ χ) ≤ TV_W(χ) + Z |supp ζ|` for every `V` (`div(ζψ) = ζ div ψ + Dζ ψ`). -/
theorem totalVariationOn_mul_le {χ ζ : Rn n → ℝ} (hχm : AEStronglyMeasurable χ volume)
    (hχ1 : ∀ y, |χ y| ≤ 1) (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    (hζ01 : ∀ y, 0 ≤ ζ y ∧ ζ y ≤ 1) {W : Set (Rn n)} (hζW : tsupport ζ ⊆ W) {Z : ℝ}
    (hZ : ∀ y, ‖fderiv ℝ ζ y‖ ≤ Z) (V : Set (Rn n)) :
    totalVariationOn V (fun y ↦ ζ y * χ y) ≤
      totalVariationOn W χ + ENNReal.ofReal (Z * volume.real (tsupport ζ)) := by
  refine (totalVariationOn_mono (subset_univ V) _).trans ?_
  set T := tsupport ζ with hT_def
  have hT : IsCompact T := hζc
  have hTm : MeasurableSet T := hT.measurableSet
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
  have hζ0 : ∀ x ∉ T, ζ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hχb : ∀ x ∈ T, |χ x| ≤ 1 := fun x _ ↦ hχ1 x
  unfold totalVariationOn weightedTV
  refine iSup₂_le fun ψ hψ ↦ ?_
  obtain ⟨hψ1, hψc, -, hψη⟩ := hψ
  simp only [Pi.one_apply] at hψη
  set ζψ : Rn n → Rn n := fun y ↦ ζ y • ψ y with hζψ_def
  have hζψ : ContDiff ℝ 1 ζψ := hζ.smul hψ1
  have hζψT : tsupport ζψ ⊆ T := tsupport_smul_subset_left _ _
  have hdiv : ∀ x, ζ x * χ x * divergence ψ x =
      χ x * divergence ζψ x - χ x * fderiv ℝ ζ x (ψ x) := fun x ↦ by
    rw [divergence_smul (hζ.differentiable one_ne_zero x) (hψ1.differentiable one_ne_zero x)]
    ring
  have hdiv0 : ∀ x ∉ T, divergence ζψ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hζψT (tsupport_divergence_subset ζψ h))
  have hDζ0 : ∀ x ∉ T, fderiv ℝ ζ x (ψ x) = 0 := fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (tsupport_fderiv_subset ℝ h))]; rfl
  have hcDζ : Continuous fun x ↦ fderiv ℝ ζ x (ψ x) :=
    (hζ.continuous_fderiv one_ne_zero).clm_apply hψ1.continuous
  have i1 := integrable_mul_of_restrict hT hχm.restrict hχb (continuous_divergence hζψ) hdiv0
  have i2 := integrable_mul_of_restrict hT hχm.restrict hχb hcDζ hDζ0
  rw [Measure.restrict_univ]
  simp_rw [hdiv]
  rw [integral_sub i1 i2, sub_eq_add_neg]
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_)
  · -- the first term is bounded by `TV_W(χ)`
    have htest : IsTVTestField W 1 ζψ := by
      refine ⟨hζψ, hζc.smul_right, hζψT.trans hζW, fun x ↦ ?_⟩
      simp only [ζψ, Pi.one_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hζ01 x).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hζ01 x).2).trans (hψη x)
    rw [← setIntegral_mul_divergence_eq_integral χ (hζψT.trans hζW)]
    exact le_iSup₂ (f := fun ψ (_ : IsTVTestField W 1 ψ) ↦
      ENNReal.ofReal (∫ x in W, χ x * divergence ψ x)) ζψ htest
  · -- the second term is bounded by `Z |T|`
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ∀ x, |χ x * fderiv ℝ ζ x (ψ x)| ≤ T.indicator (fun _ ↦ Z) x := by
      intro x
      by_cases hx : x ∈ T
      · rw [indicator_of_mem hx, abs_mul]
        refine (mul_le_mul (hχ1 x) ?_ (abs_nonneg _) zero_le_one).trans (one_mul Z).le
        rw [← Real.norm_eq_abs]
        calc ‖fderiv ℝ ζ x (ψ x)‖ ≤ ‖fderiv ℝ ζ x‖ * ‖ψ x‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ Z * 1 := mul_le_mul (hZ x) (hψη x) (norm_nonneg _) hZ0
          _ = Z := mul_one Z
      · rw [indicator_of_notMem hx, hDζ0 x hx, mul_zero, abs_zero]
    calc -∫ x, χ x * fderiv ℝ ζ x (ψ x)
        ≤ |∫ x, χ x * fderiv ℝ ζ x (ψ x)| := neg_le_abs _
      _ ≤ ∫ x, |χ x * fderiv ℝ ζ x (ψ x)| := abs_integral_le_integral_abs
      _ ≤ ∫ x, T.indicator (fun _ ↦ Z) x :=
          integral_mono i2.abs
            ((integrable_indicator_iff hTm).2 (integrableOn_const hT.measure_lt_top.ne)) hb
      _ = Z * volume.real T := by
          rw [integral_indicator_const _ hTm, smul_eq_mul, mul_comm]

/-- A sequence in `ℝ≥0∞` with finite terms which is eventually bounded is bounded. -/
theorem exists_forall_le_ofReal_of_eventually {f : ℕ → ℝ≥0∞} (hf : ∀ k, f k ≠ ⊤) {B : ℝ}
    (hB : ∀ᶠ k in atTop, f k ≤ ENNReal.ofReal B) : ∃ P : ℝ, ∀ k, f k ≤ ENNReal.ofReal P := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hB
  refine ⟨max B (∑ k ∈ Finset.range N, (f k).toReal), fun k ↦ ?_⟩
  by_cases hk : N ≤ k
  · exact (hN k hk).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · rw [← ENNReal.ofReal_toReal (hf k)]
    refine ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans' ?_)
    exact Finset.single_le_sum (f := fun k ↦ (f k).toReal) (fun _ _ ↦ ENNReal.toReal_nonneg)
      (Finset.mem_range.2 (not_le.1 hk))

/-- **Limits of indicators are indicators.** If `χ_{S_k} → χ₀` in `L¹_loc(ℝⁿ)`, then
`χ₀ = χ_F` a.e. for the measurable set `F = {χ₀ = 1}`, so `χ_{S_k} → χ_F` in `L¹_loc(ℝⁿ)`. -/
theorem exists_measurableSet_tendstoLpLoc_indicator {S : ℕ → Set (Rn n)}
    (_hS : ∀ k, MeasurableSet (S k)) {χ₀ : Rn n → ℝ} (hχ₀ : Measurable χ₀)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (S k).indicator (1 : Rn n → ℝ)) χ₀ atTop) :
    ∃ F : Set (Rn n), MeasurableSet F ∧ F.indicator (1 : Rn n → ℝ) =ᵐ[volume] χ₀ ∧
      TendstoLpLoc 1 volume univ (fun k ↦ (S k).indicator (1 : Rn n → ℝ)) (F.indicator 1)
        atTop := by
  have h01 : ∀ᵐ y ∂(volume : Measure (Rn n)), χ₀ y ∈ ({0, 1} : Set ℝ) := by
    have hm : ∀ m : ℕ, ∀ᵐ y ∂(volume : Measure (Rn n)).restrict (closedBall 0 m),
        χ₀ y ∈ ({0, 1} : Set ℝ) := by
      intro m
      have hTIM : TendstoInMeasure ((volume : Measure (Rn n)).restrict (closedBall 0 m))
          (fun k ↦ (S k).indicator (1 : Rn n → ℝ)) atTop χ₀ :=
        tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
          (hconv _ (subset_univ _) (isCompact_closedBall 0 _))
      obtain ⟨ns, -, hae⟩ := hTIM.exists_seq_tendsto_ae
      filter_upwards [hae] with y hy
      refine (Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).mem_of_tendsto hy
        (Eventually.of_forall fun k ↦ ?_)
      by_cases hyk : y ∈ S (ns k) <;> simp [hyk]
    rw [← Measure.restrict_univ (μ := (volume : Measure (Rn n))), ← iUnion_closedBall_nat 0,
      ae_restrict_iUnion_iff]
    exact hm
  have hae : (χ₀ ⁻¹' {1}).indicator (1 : Rn n → ℝ) =ᵐ[volume] χ₀ := by
    filter_upwards [h01] with y hy
    rcases hy with hy | hy
    · simp [hy]
    · rw [mem_singleton_iff] at hy
      simp [hy]
  refine ⟨χ₀ ⁻¹' {1}, hχ₀ (measurableSet_singleton 1), hae, fun K hK hKc ↦ ?_⟩
  refine (hconv K hK hKc).congr fun k ↦ eLpNorm_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hae] with y hy
  simp [hy]

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- **Compactness of blow-ups** (EG Thm 5.13, step 3). Let `(μ, ν)` be a Gauss–Green pair of a
measurable `E` on the open `Ω`, `x ∈ Ω`, and assume the upper density bound
`μ(B_r(x)) ≤ A r^{n-1}` for `0 < r < r₀` (EG Lemma 5.3 (iv)). Then for all scales `s_k → 0+` a
subsequence of the blow-ups `χ_{E_{x,s_k}}` converges in `L¹_loc(ℝⁿ)` to the indicator of a
measurable set `F`. See the module docstring for the cutoff argument replacing EG's use of
Lemma 5.3 (v). -/
theorem exists_blowup_subseq_tendstoLpLoc (hn : 1 ≤ n) (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω)
    (hup : ∃ A r₀, 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : Set (Rn n), MeasurableSet F ∧
      TendstoLpLoc 1 volume univ (fun k ↦ (blowupSet x (s (φ k)) E).indicator (1 : Rn n → ℝ))
        (F.indicator 1) atTop := by
  obtain ⟨A, r₀, hr₀, hup⟩ := hup
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  set ρ := min (δ / 4) (r₀ / 2) with hρ_def
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρδ : ρ ≤ δ / 4 := min_le_left _ _
  have hρr : ρ ≤ r₀ / 2 := min_le_right _ _
  -- the cutoffs: `ζ_k = 1` on `B̄_{ρ/s_k}`, supported in `B̄_{2ρ/s_k}`
  let ζ : ℕ → ContDiffBump (0 : Rn n) := fun k ↦
    ⟨ρ / s k, 2 * ρ / s k, div_pos hρ (hs0 k), by
      rw [div_lt_div_iff_of_pos_right (hs0 k)]; linarith⟩
  set χ : ℕ → Rn n → ℝ := fun k ↦ (blowupSet x (s k) E).indicator 1 with hχ_def
  set χ' : ℕ → Rn n → ℝ := fun k y ↦ ζ k y * χ k y with hχ'_def
  have hpair : ∀ k, IsGaussGreenPair (blowupSet x (s k) Ω) (blowupSet x (s k) E)
      (blowupMeasure μ x (s k)) (fun z ↦ ν (x + s k • z)) := fun k ↦ h.blowup' hn x (hs0 k)
  have hEk : ∀ k, MeasurableSet (blowupSet x (s k) E) := fun k ↦
    measurableSet_blowupSet hE x (s k)
  have hχm : ∀ k, Measurable (χ k) := fun k ↦ measurable_const.indicator (hEk k)
  have hχ1 : ∀ k y, |χ k y| ≤ 1 := by
    intro k y
    by_cases hy : y ∈ blowupSet x (s k) E <;> simp [hχ_def, hy]
  have hζ1 : ∀ k y, y ∈ closedBall (0 : Rn n) (ρ / s k) → ζ k y = 1 := fun k y hy ↦
    (ζ k).one_of_mem_closedBall hy
  have hΩk : ∀ k, closedBall (0 : Rn n) (3 * ρ / s k) ⊆ blowupSet x (s k) Ω := by
    intro k
    refine closedBall_subset_blowupSet (hs0 k) ((closedBall_subset_ball ?_).trans hδΩ)
    have : s k * (3 * ρ / s k) = 3 * ρ := by field_simp [(hs0 k).ne']
    rw [this]
    linarith
  -- every term has finite total variation on every set
  have hfin : ∀ k V, totalVariationOn V (χ' k) ≠ ⊤ := by
    intro k V
    obtain ⟨Z, hZ⟩ := (((ζ k).contDiff (n := 1)).continuous_fderiv
      one_ne_zero).bounded_above_of_compact_support ((ζ k).hasCompactSupport.fderiv (𝕜 := ℝ))
    have hW : ball (0 : Rn n) (3 * ρ / s k) ⊆ blowupSet x (s k) Ω :=
      ball_subset_closedBall.trans (hΩk k)
    have hζW : tsupport (ζ k) ⊆ ball (0 : Rn n) (3 * ρ / s k) := by
      rw [(ζ k).tsupport_eq]
      refine closedBall_subset_ball ?_
      change 2 * ρ / s k < 3 * ρ / s k
      rw [div_lt_div_iff_of_pos_right (hs0 k)]
      linarith
    refine ne_top_of_le_ne_top ?_ (totalVariationOn_mul_le (hχm k).aestronglyMeasurable (hχ1 k)
      (ζ k).contDiff (ζ k).hasCompactSupport (fun y ↦ ⟨(ζ k).nonneg, (ζ k).le_one⟩) hζW hZ V)
    rw [(hpair k).totalVariationOn_indicator_eq (hEk k) isOpen_ball hW]
    exact ENNReal.add_ne_top.2 ⟨((measure_mono ball_subset_closedBall).trans_lt
      ((hpair k).lt_top_of_isCompact _ (isCompact_closedBall _ _) (hΩk k))).ne,
      ENNReal.ofReal_ne_top⟩
  -- on `V ⊆ B_L`, eventually `TV_V(ζ_k χ_k) = μ_k(V) ≤ A L^{n-1}`
  have hsL : ∀ {t : ℕ → ℝ}, Tendsto t atTop (𝓝 0) → ∀ L, ∀ᶠ k in atTop, t k * L < ρ := by
    intro t ht L
    have := ht.mul_const L
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hρ)
  have hev : ∀ L, 0 < L → ∀ V, V ⊆ ball 0 L → IsOpen V →
      ∀ᶠ k in atTop, totalVariationOn V (χ' k) ≤ ENNReal.ofReal (A * L ^ (n - 1)) := by
    intro L hL V hVL hV
    filter_upwards [hsL hs L] with k hk
    have hL' : L ≤ ρ / s k := by
      rw [le_div_iff₀ (hs0 k)]
      linarith
    have hBL : ball (0 : Rn n) L ⊆ blowupSet x (s k) Ω :=
      ball_subset_blowupSet (hs0 k) ((ball_subset_ball (by linarith : s k * L ≤ δ)).trans hδΩ)
    rw [totalVariationOn_congr_of_eqOn hV.measurableSet (g := χ k) (fun y hy ↦ by
        simp only [χ', hζ1 k y ((closedBall_subset_closedBall hL')
          (ball_subset_closedBall (hVL hy))), one_mul]),
      (hpair k).totalVariationOn_indicator_eq (hEk k) hV (hVL.trans hBL)]
    exact (measure_mono hVL).trans (blowupMeasure_ball_le hup (hs0 k) hL (by linarith))
  -- BV compactness
  obtain ⟨φ, hφ, χ₀, hχ₀, hconv⟩ := exists_tendstoLpLoc_subseq_of_TV isOpen_univ χ'
    (fun k ↦ ((ζ k).contDiff (n := 0)).continuous.measurable.mul (hχm k)
      |>.aestronglyMeasurable)
    ⟨1, fun k y _ ↦ by
      rw [abs_mul, abs_of_nonneg (ζ k).nonneg]
      exact (mul_le_of_le_one_left (abs_nonneg _) (ζ k).le_one).trans (hχ1 k y)⟩
    (fun V hV hVc ↦ by
      obtain ⟨L, hL, hsub⟩ := hVc.1.isBounded.subset_ball_lt 0 0
      exact exists_forall_le_ofReal_of_eventually (fun k ↦ hfin k V)
        (hev L hL V (subset_closure.trans hsub) hV))
  -- `ζ_k χ_k = χ_k` eventually on each compact set
  have hconv' : TendstoLpLoc 1 volume univ (fun k ↦ χ (φ k)) χ₀ atTop := by
    intro K _ hK
    obtain ⟨L, hL, hKL⟩ := hK.isBounded.subset_ball_lt 0 0
    refine (hconv K (subset_univ _) hK).congr' ?_
    filter_upwards [hsL (hs.comp hφ.tendsto_atTop) L] with k hk
    have hL' : L ≤ ρ / s (φ k) := by
      rw [le_div_iff₀ (hs0 _)]
      have : s (φ k) * L < ρ := hk
      linarith
    refine eLpNorm_congr_ae ((ae_restrict_iff' hK.measurableSet).2
      (Eventually.of_forall fun y hy ↦ ?_))
    simp only [Pi.sub_apply, χ', hζ1 (φ k) y ((closedBall_subset_closedBall hL')
      (ball_subset_closedBall (hKL hy))), one_mul]
  obtain ⟨F, hF, -, hFconv⟩ :=
    exists_measurableSet_tendstoLpLoc_indicator (fun k ↦ hEk (φ k)) hχ₀ hconv'
  exact ⟨φ, hφ, F, hF, hFconv⟩

/-- Along scales `s_k → 0`, eventually `B̄_L ⊆ Ω_{x,s_k}`. -/
theorem eventually_closedBall_subset_blowupSet (hΩ : IsOpen Ω) {x : Rn n} (hx : x ∈ Ω)
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) (L : ℝ) :
    ∀ᶠ k in atTop, closedBall (0 : Rn n) L ⊆ blowupSet x (s k) Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  have := hs.mul_const L
  rw [zero_mul] at this
  filter_upwards [this.eventually (gt_mem_nhds hδ)] with k hk
  exact closedBall_subset_blowupSet (hs0 k) ((closedBall_subset_ball hk).trans hδΩ)

/-- Along scales `s_k → 0`, eventually `μ_{x,s_k}(B_L) ≤ A L^{n-1}`. -/
theorem eventually_blowupMeasure_ball_le {x : Rn n} {A r₀ : ℝ} (hr₀ : 0 < r₀)
    (hup : ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) {L : ℝ} (hL : 0 < L) :
    ∀ᶠ k in atTop, blowupMeasure μ x (s k) (ball 0 L) ≤ ENNReal.ofReal (A * L ^ (n - 1)) := by
  have := hs.mul_const L
  rw [zero_mul] at this
  filter_upwards [this.eventually (gt_mem_nhds hr₀)] with k hk
  exact blowupMeasure_ball_le hup (hs0 k) hL hk

/-- **The limit set has locally finite perimeter** (EG Thm 5.13, step 3, and Thm 5.2). If
`χ_{S_k} → χ_F` in `L¹_loc(ℝⁿ)` and eventually `TV_{B_L}(χ_{S_k}) ≤ B(L)`, then `F` has a
Gauss–Green pair `(μ_F, ν_F)` on `ℝⁿ` with `μ_F(B_L) ≤ B(L)` (lower semicontinuity,
`weightedTV_le_liminf`, and the bridge `exists_isGaussGreenPair_of_bound`). -/
theorem exists_isGaussGreenPair_of_tendstoLpLoc {S : ℕ → Set (Rn n)}
    (hS : ∀ k, MeasurableSet (S k)) {F : Set (Rn n)} (hF : MeasurableSet F)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (S k).indicator (1 : Rn n → ℝ)) (F.indicator 1)
      atTop)
    {B : ℝ → ℝ} (hB : ∀ L, 0 < L → ∀ᶠ k in atTop,
      totalVariationOn (ball 0 L) ((S k).indicator (1 : Rn n → ℝ)) ≤ ENNReal.ofReal (B L)) :
    ∃ μF νF, IsGaussGreenPair univ F μF νF ∧
      ∀ L, 0 < L → μF (ball 0 L) ≤ ENNReal.ofReal (B L) := by
  have hli : ∀ {T : Set (Rn n)}, MeasurableSet T → ∀ L : ℝ,
      LocallyIntegrableOn (T.indicator (1 : Rn n → ℝ)) (ball 0 L) volume := fun hT L ↦
    ((locallyIntegrable_const (1 : ℝ)).indicator hT).locallyIntegrableOn _
  have hTV : ∀ L, 0 < L →
      totalVariationOn (ball 0 L) (F.indicator (1 : Rn n → ℝ)) ≤ ENNReal.ofReal (B L) := by
    intro L hL
    refine (weightedTV_le_liminf (U := ball (0 : Rn n) L) 1 (fun k ↦ (S k).indicator 1)
      (F.indicator 1) (fun k ↦ hli (hS k) L) (hli hF L)
      (fun K _ hKc ↦ hconv K (subset_univ K) hKc)).trans ?_
    exact liminf_le_of_frequently_le' (hB L hL).frequently
  obtain ⟨μF, νF, hp⟩ := exists_isGaussGreenPair_of_bound (E := F) isOpen_univ fun K hK _ ↦ by
    obtain ⟨L, hL, hKL⟩ := hK.isBounded.subset_ball_lt 0 0
    refine ⟨(totalVariationOn (ball 0 L) (F.indicator 1)).toReal, fun φ hφ hφK M hM ↦ ?_⟩
    exact abs_integral_divergence_le_totalVariationOn hF
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hTV L hL)) ⟨hφ.1, hφ.2.1, hφK.trans hKL⟩ hM
  refine ⟨μF, νF, hp, fun L hL ↦ ?_⟩
  rw [← hp.totalVariationOn_indicator_eq hF isOpen_ball (subset_univ _)]
  exact hTV L hL

/-- The limit `F` of blow-ups (`exists_blowup_subseq_tendstoLpLoc`) has a Gauss–Green pair on
`ℝⁿ` with `μ_F(B_L) ≤ A L^{n-1}`. -/
theorem exists_isGaussGreenPair_of_blowup_tendsto (hn : 1 ≤ n) (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω) {A r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (hup : ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) {F : Set (Rn n)}
    (hF : MeasurableSet F)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (blowupSet x (s k) E).indicator (1 : Rn n → ℝ))
      (F.indicator 1) atTop) :
    ∃ μF νF, IsGaussGreenPair univ F μF νF ∧
      ∀ L, 0 < L → μF (ball 0 L) ≤ ENNReal.ofReal (A * L ^ (n - 1)) := by
  refine exists_isGaussGreenPair_of_tendstoLpLoc (fun k ↦ measurableSet_blowupSet hE x (s k)) hF
    hconv fun L hL ↦ ?_
  filter_upwards [eventually_closedBall_subset_blowupSet hΩ hx hs0 hs L,
    eventually_blowupMeasure_ball_le hr₀ hup hs0 hs hL] with k hk hkμ
  rw [(h.blowup' hn x (hs0 k)).totalVariationOn_indicator_eq (measurableSet_blowupSet hE x (s k))
    isOpen_ball (ball_subset_closedBall.trans hk)]
  exact hkμ

end Compactness

end GMTFoundations
