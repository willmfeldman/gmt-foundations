/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.GMT.Polar
import GMTFoundations.Sobolev.Lipschitz
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# A trace inequality on the unit sphere, along rays

For `f` Lipschitz on the closed unit ball `B̄₁ ⊆ ℝⁿ` and `A = B₁ ∖ B_{1/2}`,

* `lintegral_sphere_sq_le`: `∫_{S^{n-1}} f² dσ ≤ 2ⁿ ∫_A (f² + 2|f| |∇f|)`;
* `lintegral_shell_sq_le`: for `δ ≤ 1/2`,
  `∫_{B₁ ∖ B̄_{1-δ}} f² ≤ δ 2ⁿ ∫_A (f² + 2|f| |∇f|)`.

Both follow from one estimate on `σ`-a.e. ray (`ae_sphere_sq_le_lintegral`): for `r ∈ [1/2, 1]`,
`f(rω)² ≤ 2ⁿ ∫_{1/2}^1 t^{n-1} (f² + 2|f||∇f|)(tω) dt`. Its proof is the one-dimensional
`mul_sq_le_of_ae_abs_deriv_le`: `γ(r)² = γ(t)² + ∫_t^r (γ²)'` for the Lipschitz (hence absolutely
continuous) function `γ(τ) = f(τω)`, averaged over `t ∈ [1/2, 1]`. The radial derivative is
`⟪∇f(tω), ω⟫` for a.e. `t` on `σ`-a.e. ray (`LipschitzOnWith.ae_sphere_ae_hasDerivAt`,
`GMT/Polar.lean`). The polar formula `lintegral_set_eq_lintegral_sphere` turns the ray estimates
into the integral estimates.

The measure-theoretic part is done for a globally Lipschitz `u` (McShane extension), and
transferred to `f`: the integrals only see `f` on `B̄₁` and `∇f` on `B₁`, where the gradient of
`f` is that of the extension (`gradient_eq_of_eqOn`).

Evans–Gariepy, Thm 4.6, proves the trace inequality by the Gauss–Green theorem on a Lipschitz
domain; on the ball we use the ray argument above instead.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
-/

public section

namespace GMTFoundations

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace Interval

variable {n : ℕ}

/-- Two functions that agree on an open set have the same gradient at every point of it. -/
theorem gradient_eq_of_eqOn {f g : Rn n → ℝ} {U : Set (Rn n)} (hU : IsOpen U) (h : EqOn f g U)
    {x : Rn n} (hx : x ∈ U) : gradient f x = gradient g x := by
  unfold gradient
  rw [(Filter.eventuallyEq_of_mem (hU.mem_nhds hx) h).fderiv_eq]

/-! ### One dimension -/

/-- **The one-dimensional estimate.** Let `γ` be Lipschitz on `[a, b]`, with `|γ'| ≤ D` a.e. on
`(a, b)` for an integrable `D`. Then for `r ∈ [a, b]`,
`(b - a) γ(r)² ≤ ∫_a^b γ² + (b - a) ∫_a^b 2|γ| D`. -/
theorem mul_sq_le_of_ae_abs_deriv_le {γ D : ℝ → ℝ} {a b r : ℝ} (hab : a < b) {K : ℝ≥0}
    (hγ : LipschitzOnWith K γ (Icc a b)) (hD : IntervalIntegrable D volume a b)
    (hd : ∀ᵐ s, s ∈ Ioo a b → |deriv γ s| ≤ D s) (hr : r ∈ Icc a b) :
    (b - a) * γ r ^ 2 ≤ (∫ t in a..b, γ t ^ 2) + (b - a) * ∫ s in a..b, 2 * |γ s| * D s := by
  have hγc : ContinuousOn γ (Icc a b) := hγ.continuousOn
  have hu : uIcc a b = Icc a b := uIcc_of_le hab.le
  have hBint : IntervalIntegrable (fun s => 2 * |γ s| * D s) volume a b := by
    have : ContinuousOn (fun s => 2 * |γ s|) (uIcc a b) := by
      rw [hu]; exact continuousOn_const.mul hγc.abs
    exact hD.continuousOn_mul this
  set B := ∫ s in a..b, 2 * |γ s| * D s with hBdef
  have hacab : AbsolutelyContinuousOnInterval γ a b := by
    refine LipschitzOnWith.absolutelyContinuousOnInterval (K := K) ?_
    rwa [hu]
  set F : ℝ → ℝ := fun x => deriv γ x * γ x + γ x * deriv γ x with hFdef
  have hFint : IntegrableOn F (Ioc a b) := by
    have h1 : IntervalIntegrable (fun x => deriv γ x * γ x) volume a b :=
      hacab.intervalIntegrable_deriv.mul_continuousOn (by rw [hu]; exact hγc)
    have h2 : IntervalIntegrable (fun x => γ x * deriv γ x) volume a b :=
      hacab.intervalIntegrable_deriv.continuousOn_mul (by rw [hu]; exact hγc)
    exact (h1.add h2).1
  have hFbd : ∀ᵐ s ∂(volume.restrict (Ioc a b)), ‖F s‖ ≤ 2 * |γ s| * D s := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hd, measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := b))]
      with s hs hsb hsI
    have hs' : s ∈ Ioo a b := ⟨hsI.1, lt_of_le_of_ne hsI.2 hsb⟩
    have h := hs hs'
    simp only [hFdef, Real.norm_eq_abs]
    rw [show deriv γ s * γ s + γ s * deriv γ s = 2 * (γ s * deriv γ s) by ring, abs_mul, abs_mul,
      abs_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (abs_nonneg _)) zero_le_two
  have hBnn : ∀ᵐ s ∂(volume.restrict (Ioc a b)), 0 ≤ 2 * |γ s| * D s :=
    hFbd.mono fun s hs => (norm_nonneg _).trans hs
  have key : ∀ t ∈ Icc a b, γ r ^ 2 ≤ γ t ^ 2 + B := by
    intro t ht
    have hsub : uIcc t r ⊆ Icc a b := uIcc_subset_Icc ht hr
    have hac : AbsolutelyContinuousOnInterval γ t r :=
      (hγ.mono hsub).absolutelyContinuousOnInterval
    have hftc := hac.integral_deriv_mul_eq_sub hac
    have hIoc : Ι t r ⊆ Ioc a b := by
      intro x hx
      rcases mem_uIoc.1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact ⟨by linarith [ht.1, hr.1], by linarith [ht.2, hr.2]⟩
    have hle : ∫ x in t..r, F x ≤ B := by
      calc ∫ x in t..r, F x ≤ ‖∫ x in t..r, F x‖ := Real.le_norm_self _
        _ = ‖∫ x in Ι t r, F x‖ := intervalIntegral.norm_integral_eq_norm_integral_uIoc F
        _ ≤ ∫ x in Ι t r, ‖F x‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ x in Ι t r, 2 * |γ x| * D x :=
          integral_mono_ae (hFint.mono_set hIoc).norm (hBint.1.mono_set hIoc)
            (ae_restrict_of_ae_restrict_of_subset hIoc hFbd)
        _ ≤ ∫ x in Ioc a b, 2 * |γ x| * D x :=
          setIntegral_mono_set hBint.1 hBnn hIoc.eventuallyLE
        _ = B := (intervalIntegral.integral_of_le hab.le).symm
    have e : γ r ^ 2 = γ t ^ 2 + ∫ x in t..r, F x := by
      rw [hFdef, hftc]; ring
    linarith
  have hγ2 : IntervalIntegrable (fun t => γ t ^ 2) volume a b :=
    (show ContinuousOn (fun t => γ t ^ 2) (uIcc a b) by
      rw [hu]; exact hγc.pow 2).intervalIntegrable
  have h := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
    (hγ2.add intervalIntegrable_const) key
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hγ2 intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at h
  linarith

/-! ### Polar coordinates for sets swept by radial intervals -/

/-- **Polar formula for a set swept by a radial interval.** If `t ω ∈ S ↔ t ∈ I` for all `t > 0`
and `ω ∈ S^{n-1}`, with `I ⊆ (0, ∞)`, then `∫_S g = ∫_{S^{n-1}} ∫_I t^{n-1} g(tω) dt dσ(ω)`. -/
theorem lintegral_set_eq_lintegral_sphere [NeZero n] {g : Rn n → ℝ≥0∞} (hg : Measurable g)
    {S : Set (Rn n)} (hS : MeasurableSet S) {I : Set ℝ} (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0)
    (hSI : ∀ t : ℝ, 0 < t → ∀ ω : sphere (0 : Rn n) 1, t • (ω : Rn n) ∈ S ↔ t ∈ I) :
    ∫⁻ y in S, g y = ∫⁻ ω, (∫⁻ t in I, ENNReal.ofReal (t ^ (n - 1)) * g (t • (ω : Rn n)))
      ∂sphereMeasure n := by
  have hm : Measurable fun p : sphere (0 : Rn n) 1 × Ioi (0 : ℝ) => (p.2 : ℝ) • (p.1 : Rn n) :=
    ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).measurable
  rw [← lintegral_indicator hS, lintegral_eq_lintegral_prod_polar,
    lintegral_prod
      (fun p : sphere (0 : Rn n) 1 × Ioi (0 : ℝ) => S.indicator g ((p.2 : ℝ) • (p.1 : Rn n)))
      (((hg.indicator hS).comp hm).aemeasurable)]
  refine lintegral_congr fun ω => ?_
  refine (lintegral_volumeIoiPow (n - 1) (fun t => S.indicator g (t • (ω : Rn n)))).trans ?_
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (g := I.indicator fun t => ENNReal.ofReal (t ^ (n - 1)) * g (t • (ω : Rn n))) (fun t ht => ?_),
    setLIntegral_indicator hI, inter_eq_left.2 hI0]
  by_cases htI : t ∈ I
  · rw [indicator_of_mem htI, indicator_of_mem ((hSI t ht ω).2 htI)]
  · rw [indicator_of_notMem htI, indicator_of_notMem (fun h => htI ((hSI t ht ω).1 h)), mul_zero]

/-! ### The estimate on a.e. ray -/

/-- **The estimate on `σ`-a.e. ray.** For `u` Lipschitz, `σ`-a.e. `ω` and all `r ∈ [1/2, 1]`,
`u(rω)² ≤ 2ⁿ ∫_{[1/2, 1)} t^{n-1} (u² + 2|u| |∇u|)(tω) dt`. -/
theorem ae_sphere_sq_le_lintegral [NeZero n] {u : Rn n → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ (ω : sphere (0 : Rn n) 1) ∂sphereMeasure n, ∀ r ∈ Icc (1 / 2 : ℝ) 1,
      ENNReal.ofReal (u (r • (ω : Rn n)) ^ 2) ≤ 2 ^ n * ∫⁻ t in Ico (1 / 2 : ℝ) 1,
        ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal (u (t • (ω : Rn n)) ^ 2 +
          2 * |u (t • (ω : Rn n))| * ‖gradient u (t • (ω : Rn n))‖) := by
  filter_upwards [(hu.lipschitzOnWith (s := ball (0 : Rn n) 1)).ae_sphere_ae_hasDerivAt]
    with ω hω r hr
  set γ : ℝ → ℝ := fun τ => u (τ • (ω : Rn n)) with hγdef
  set D : ℝ → ℝ := fun τ => ‖gradient u (τ • (ω : Rn n))‖ with hDdef
  have hray : LipschitzWith 1 (fun τ : ℝ => τ • (ω : Rn n)) :=
    LipschitzWith.of_dist_le_mul fun τ τ' => by
      rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, norm_eq_of_mem_sphere ω, mul_one,
        NNReal.coe_one, one_mul]
  have hγL : LipschitzWith (K * 1) γ := hu.comp hray
  have hDm : Measurable D :=
    (measurable_gradient u).norm.comp (measurable_id.smul_const (ω : Rn n))
  have hD : IntervalIntegrable D volume (1 / 2) 1 :=
    (intervalIntegrable_const (c := (K : ℝ))).mono_fun' hDm.aestronglyMeasurable
      (Eventually.of_forall fun τ => by
        simp only [hDdef, norm_norm]
        rw [norm_gradient_eq_norm_fderiv]
        exact norm_fderiv_le_of_lipschitz ℝ hu)
  have hd : ∀ᵐ s, s ∈ Ioo (1 / 2 : ℝ) 1 → |deriv γ s| ≤ D s := by
    filter_upwards [hω] with s hs hs'
    have h := (hs ⟨by linarith [hs'.1], hs'.2⟩).2
    simp only [zero_add] at h
    rw [show deriv γ s = _ from h.deriv]
    calc |⟪gradient u (s • (ω : Rn n)), (ω : Rn n)⟫|
        ≤ ‖gradient u (s • (ω : Rn n))‖ * ‖(ω : Rn n)‖ := abs_real_inner_le_norm _ _
      _ = D s := by rw [norm_eq_of_mem_sphere ω, mul_one]
  have h1 := mul_sq_le_of_ae_abs_deriv_le (by norm_num : (1 / 2 : ℝ) < 1)
    (hγL.lipschitzOnWith (s := Icc (1 / 2) 1)) hD hd hr
  set H : ℝ → ℝ := fun t => γ t ^ 2 + 2 * |γ t| * D t with hHdef
  have hγ2 : IntervalIntegrable (fun t => γ t ^ 2) volume (1 / 2) 1 :=
    (hγL.continuous.pow 2).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun t => 2 * |γ t| * D t) volume (1 / 2) 1 :=
    hD.continuousOn_mul (continuous_const.mul hγL.continuous.abs).continuousOn
  have hH : IntervalIntegrable H volume (1 / 2) 1 := hγ2.add hB
  have hwH : IntervalIntegrable (fun t => t ^ (n - 1) * H t) volume (1 / 2) 1 :=
    hH.continuousOn_mul (continuous_pow _).continuousOn
  have hHnn : ∀ t, 0 ≤ H t := fun t => by
    simp only [hHdef, hDdef]; positivity
  have hBnn : 0 ≤ ∫ t in (1 / 2 : ℝ)..1, 2 * |γ t| * D t :=
    intervalIntegral.integral_nonneg (by norm_num) fun t _ => by simp only [hDdef]; positivity
  have h2 : γ r ^ 2 ≤ 2 * ∫ t in (1 / 2 : ℝ)..1, H t := by
    rw [intervalIntegral.integral_add hγ2 hB]
    linarith
  have h3 : ∫ t in (1 / 2 : ℝ)..1, H t ≤
      2 ^ (n - 1) * ∫ t in (1 / 2 : ℝ)..1, t ^ (n - 1) * H t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by norm_num) hH (hwH.const_mul _) fun t ht => ?_
    have : 1 ≤ 2 ^ (n - 1) * t ^ (n - 1) := by
      rw [← mul_pow]; exact one_le_pow₀ (by linarith [ht.1])
    nlinarith [hHnn t]
  have h4 : γ r ^ 2 ≤ 2 ^ n * ∫ t in (1 / 2 : ℝ)..1, t ^ (n - 1) * H t := by
    have hn : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; congr 1; have := NeZero.pos n; omega
    rw [hn, mul_assoc]
    linarith
  have hconv : ENNReal.ofReal (∫ t in (1 / 2 : ℝ)..1, t ^ (n - 1) * H t) =
      ∫⁻ t in Ico (1 / 2 : ℝ) 1, ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal (H t) := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      ofReal_integral_eq_lintegral_ofReal hwH.1
        ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => mul_nonneg
          (pow_nonneg (by linarith [ht.1]) _) (hHnn t)),
      setLIntegral_congr (Ico_ae_eq_Ioc (a := (1 / 2 : ℝ)) (b := 1)).symm]
    refine setLIntegral_congr_fun measurableSet_Ico fun t ht => ?_
    exact ENNReal.ofReal_mul (pow_nonneg (by linarith [ht.1]) _)
  calc ENNReal.ofReal (u (r • (ω : Rn n)) ^ 2) = ENNReal.ofReal (γ r ^ 2) := rfl
    _ ≤ ENNReal.ofReal (2 ^ n * ∫ t in (1 / 2 : ℝ)..1, t ^ (n - 1) * H t) :=
      ENNReal.ofReal_le_ofReal h4
    _ = 2 ^ n * ENNReal.ofReal (∫ t in (1 / 2 : ℝ)..1, t ^ (n - 1) * H t) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
      norm_num
    _ = _ := by rw [hconv]

/-! ### The trace and shell estimates for globally Lipschitz functions -/

private lemma measurable_density {u : Rn n → ℝ} (hu : Measurable u) :
    Measurable fun y => ENNReal.ofReal (u y ^ 2 + 2 * |u y| * ‖gradient u y‖) :=
  ((hu.pow_const 2).add ((measurable_const.mul hu.abs).mul
    (measurable_gradient u).norm)).ennreal_ofReal

private lemma annulus_iff {t : ℝ} (ht : 0 < t) (ω : sphere (0 : Rn n) 1) :
    t • (ω : Rn n) ∈ ball (0 : Rn n) 1 \ ball 0 (1 / 2) ↔ t ∈ Ico (1 / 2 : ℝ) 1 := by
  simp only [Set.mem_sdiff, mem_ball_zero_iff, norm_smul_sphere ht.le, not_lt, mem_Ico]
  exact and_comm

private lemma lintegral_annulus_eq [NeZero n] {u : Rn n → ℝ} (hu : Measurable u) :
    ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
      ENNReal.ofReal (u y ^ 2 + 2 * |u y| * ‖gradient u y‖) =
    ∫⁻ ω, (∫⁻ t in Ico (1 / 2 : ℝ) 1, ENNReal.ofReal (t ^ (n - 1)) *
      ENNReal.ofReal (u (t • (ω : Rn n)) ^ 2 +
        2 * |u (t • (ω : Rn n))| * ‖gradient u (t • (ω : Rn n))‖)) ∂sphereMeasure n :=
  lintegral_set_eq_lintegral_sphere (measurable_density hu)
    (measurableSet_ball.diff measurableSet_ball) measurableSet_Ico
    (fun t ht => lt_of_lt_of_le (by norm_num) ht.1) (fun t ht ω => annulus_iff ht ω)

/-- The trace inequality for globally Lipschitz `u`. -/
theorem lintegral_sphere_sq_le_of_lipschitzWith [NeZero n] {u : Rn n → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) :
    ∫⁻ ω, ENNReal.ofReal (u ω ^ 2) ∂sphereMeasure n ≤
      2 ^ n * ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
        ENNReal.ofReal (u y ^ 2 + 2 * |u y| * ‖gradient u y‖) := by
  rw [lintegral_annulus_eq hu.continuous.measurable, ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_sphere_sq_le_lintegral hu] with ω hω
  have h := hω 1 ⟨by norm_num, le_rfl⟩
  rwa [one_smul] at h

/-- The shell estimate for globally Lipschitz `u`. -/
theorem lintegral_shell_sq_le_of_lipschitzWith [NeZero n] {u : Rn n → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) {δ : ℝ} (hδ : δ ≤ 1 / 2) :
    ∫⁻ y in ball (0 : Rn n) 1 \ closedBall 0 (1 - δ), ENNReal.ofReal (u y ^ 2) ≤
      ENNReal.ofReal δ * (2 ^ n * ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
        ENNReal.ofReal (u y ^ 2 + 2 * |u y| * ‖gradient u y‖)) := by
  have hum := hu.continuous.measurable
  have hshell : ∀ t : ℝ, 0 < t → ∀ ω : sphere (0 : Rn n) 1,
      t • (ω : Rn n) ∈ ball (0 : Rn n) 1 \ closedBall 0 (1 - δ) ↔ t ∈ Ioo (1 - δ) 1 := by
    intro t ht ω
    simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, norm_smul_sphere ht.le,
      not_le, mem_Ioo]
    exact and_comm
  rw [lintegral_set_eq_lintegral_sphere (hum.pow_const 2).ennreal_ofReal
      (measurableSet_ball.diff measurableSet_closedBall) measurableSet_Ioo
      (fun t ht => lt_of_lt_of_le (by linarith) (le_of_lt ht.1)) hshell,
    lintegral_annulus_eq hum, ← lintegral_const_mul' _ _ (by simp),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_sphere_sq_le_lintegral hu] with ω hω
  set R := ∫⁻ t in Ico (1 / 2 : ℝ) 1, ENNReal.ofReal (t ^ (n - 1)) *
      ENNReal.ofReal (u (t • (ω : Rn n)) ^ 2 +
        2 * |u (t • (ω : Rn n))| * ‖gradient u (t • (ω : Rn n))‖)
  calc ∫⁻ t in Ioo (1 - δ) 1, ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal (u (t • ω) ^ 2)
      ≤ ∫⁻ _t in Ioo (1 - δ) 1, 2 ^ n * R := by
        refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
        have ht0 : 0 ≤ t := by linarith [ht.1]
        calc ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal (u (t • ω) ^ 2)
            ≤ 1 * (2 ^ n * R) :=
              mul_le_mul' (ENNReal.ofReal_le_one.2 (pow_le_one₀ ht0 ht.2.le))
                (hω t ⟨by linarith [ht.1], ht.2.le⟩)
          _ = 2 ^ n * R := one_mul _
    _ = ENNReal.ofReal δ * (2 ^ n * R) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_sub_cancel, mul_comm]

/-! ### Transfer to functions Lipschitz on the closed ball -/

private lemma density_eqOn {f g : Rn n → ℝ} (hfg : EqOn f g (closedBall 0 1)) :
    EqOn (fun y => ENNReal.ofReal (f y ^ 2 + 2 * |f y| * ‖gradient f y‖))
      (fun y => ENNReal.ofReal (g y ^ 2 + 2 * |g y| * ‖gradient g y‖))
      (ball (0 : Rn n) 1 \ ball 0 (1 / 2)) := by
  intro y hy
  have hyb : y ∈ ball (0 : Rn n) 1 := hy.1
  simp only
  rw [hfg (ball_subset_closedBall hyb),
    gradient_eq_of_eqOn isOpen_ball (hfg.mono ball_subset_closedBall) hyb]

/-- **Trace inequality (Step 3).** For `f` Lipschitz on the closed unit ball,
`∫_{S^{n-1}} f² dσ ≤ 2ⁿ ∫_{B₁ ∖ B_{1/2}} (f² + 2|f| |∇f|)`. -/
theorem lintegral_sphere_sq_le [NeZero n] {f : Rn n → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (closedBall 0 1)) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂sphereMeasure n ≤
      2 ^ n * ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
        ENNReal.ofReal (f y ^ 2 + 2 * |f y| * ‖gradient f y‖) := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  rw [setLIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball) (density_eqOn hfg)]
  have hS : ∀ ω : sphere (0 : Rn n) 1, f ω = g ω := fun ω =>
    hfg (sphere_subset_closedBall ω.2)
  simp_rw [hS]
  exact lintegral_sphere_sq_le_of_lipschitzWith hg

/-- **Shell estimate.** For `f` Lipschitz on the closed unit ball and `δ ≤ 1/2`,
`∫_{B₁ ∖ B̄_{1-δ}} f² ≤ δ 2ⁿ ∫_{B₁ ∖ B_{1/2}} (f² + 2|f| |∇f|)`. -/
theorem lintegral_shell_sq_le [NeZero n] {f : Rn n → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (closedBall 0 1)) {δ : ℝ} (hδ : δ ≤ 1 / 2) :
    ∫⁻ y in ball (0 : Rn n) 1 \ closedBall 0 (1 - δ), ENNReal.ofReal (f y ^ 2) ≤
      ENNReal.ofReal δ * (2 ^ n * ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
        ENNReal.ofReal (f y ^ 2 + 2 * |f y| * ‖gradient f y‖)) := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  rw [setLIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball) (density_eqOn hfg),
    setLIntegral_congr_fun (measurableSet_ball.diff measurableSet_closedBall)
      (g := fun y => ENNReal.ofReal (g y ^ 2)) (fun y hy => by
        simp only
        rw [hfg (ball_subset_closedBall hy.1)])]
  exact lintegral_shell_sq_le_of_lipschitzWith hg hδ

end GMTFoundations
