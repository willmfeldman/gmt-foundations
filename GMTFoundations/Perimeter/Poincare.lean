/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.Mollify
import GMTFoundations.GMT.Polar
import Mathlib.Algebra.Order.Ring.Star

/-!
# The `L¹` Poincaré inequality on balls and the relative isoperimetric inequality

References: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (EG); D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of
Second Order*, Springer, Classics in Mathematics reprint, 2001 (GT).

Only the `L¹` form `min(|E ∩ B_r|, |B_r \ E|) ≤ C r ‖∂E‖(B_r)` of the relative isoperimetric
inequality is proved, not EG's form with the power `1 - 1/n` on the left (EG Thm 5.11 (ii)). The
`L¹` form is all that the proofs of EG Lemmas 5.3 and 5.5 use.

## Main results

* `lintegral_enorm_sub_setAverage_le` (EG Thm 4.9 with `p = 1` in `L¹` form; cf. GT
  Lemma 7.16): for `u ∈ C¹(ℝⁿ)`,
  `∫_{B_r(x)} |u - u_{x,r}| ≤ 2^{n+1} r ∫_{B_r(x)} |Du|`.
* `min_volume_le_totalVariationOn_ball` (EG Thm 5.11 (ii) in `L¹` form): for
  measurable `E`, `min(|E ∩ B_r(x)|, |B_r(x) \ E|) ≤ 2^{n+1} r TV(E; B_r(x))`, and its pair form
  `IsGaussGreenPair.min_volume_le_measure_ball`.
* `volume_inter_ball_eq_zero_or_of_totalVariationOn_eq_zero`: `TV(E; B_r(x)) = 0`
  implies `|E ∩ B_r(x)| = 0` or `|B_r(x) \ E| = 0`. This is the last step of the null case of
  the finite-perimeter criterion EG Thm 5.23 (`Perimeter/Criterion.lean`).

## Proofs

(a) Segment formula and a linear change of variables, instead of EG's polar coordinates (Lemma
4.1). For `y, z ∈ B = B_r(x)`,
`|u(y) - u(z)| ≤ |y - z| ∫₀¹ |Du(z + t(y - z))| dt ≤ 2r ∫₀¹ G(z + t(y - z)) dt`, with `G = 1_B |Du|`
(the segment lies in `B`). For fixed `t ∈ (0, 1]`, the map `y ↦ z + t(y - z)` has Jacobian `tⁿ`
and `z ↦ z + t(y - z)` has Jacobian `(1 - t)ⁿ`, and one of `t, 1 - t` is `≥ 1/2`; integrating in
that variable first gives `∫_B ∫_B G(z + t(y - z)) ≤ 2ⁿ |B| ∫ G`
(`lintegral_lintegral_comp_segment_le`). Hence `∫_B ∫_B |u(y) - u(z)| ≤ 2^{n+1} r |B| ∫_B |Du|`,
and `|u(y) - u_B| ≤ ⨍_B |u(y) - u(z)| dz`.

(b) For `s < r`, apply (a) on `B_s` to `u_k = χ_E ⋆ ρ_k` (`rOut < r - s`), whose gradient mass on
`B_s` is at most `TV(E; B_r)` (`Perimeter/Mollify.lean`). For every constant `c`,
`∫_{B_s} |χ_E - c| = |E ∩ B_s| |1 - c| + |B_s \ E| |c| ≥ min(|E ∩ B_s|, |B_s \ E|)`, and
`∫_{B_s} |χ_E - c_k| ≤ ‖χ_E - u_k‖_{L¹(B_s)} + ∫_{B_s} |u_k - c_k|`, where the first term tends to
`0`. So no convergence of the averages `c_k` is needed. Finally let `s ↑ r`.
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### Change of variables -/

/-- `∫ G(s y + c) dy ≤ 2ⁿ ∫ G` for `s ≥ 1/2` (Jacobian `sⁿ ≥ 2⁻ⁿ`). -/
theorem lintegral_comp_smul_add_le {G : Rn n → ℝ≥0∞} (hG : Measurable G) {s : ℝ}
    (hs : 1 / 2 ≤ s) (c : Rn n) : ∫⁻ y, G (s • y + c) ≤ 2 ^ n * ∫⁻ z, G z := by
  have hs0 : 0 < s := by linarith
  have hmap := Measure.map_addHaar_smul (volume : Measure (Rn n)) hs0.ne'
  rw [finrank_Rn] at hmap
  have hinv : (s ^ n)⁻¹ ≤ 2 ^ n := by
    rw [← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    rw [inv_le_comm₀ hs0 (by norm_num)]
    linarith
  calc ∫⁻ y, G (s • y + c) = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z, G (z + c) := by
        rw [← smul_eq_mul, ← lintegral_smul_measure, ← hmap,
          lintegral_map (f := fun a ↦ G (a + c)) (hG.comp (measurable_add_const c))
            (measurable_const_smul s)]
    _ = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z, G z := by
        rw [lintegral_add_right_eq_self (μ := volume) G c]
    _ ≤ 2 ^ n * ∫⁻ z, G z := by
        gcongr
        rw [abs_of_nonneg (by positivity)]
        calc ENNReal.ofReal (s ^ n)⁻¹ ≤ ENNReal.ofReal (2 ^ n) := ENNReal.ofReal_le_ofReal hinv
          _ = 2 ^ n := by rw [ENNReal.ofReal_pow (by norm_num)]; simp

/-- For fixed `t ∈ ℝ`: `∫_B ∫_B G(z + t(y - z)) dz dy ≤ 2ⁿ |B| ∫ G` (one of `t`, `1 - t` is
`≥ 1/2`). -/
theorem lintegral_lintegral_comp_segment_le {G : Rn n → ℝ≥0∞} (hG : Measurable G)
    (B : Set (Rn n)) (t : ℝ) :
    ∫⁻ y in B, ∫⁻ z in B, G (z + t • (y - z)) ≤ 2 ^ n * volume B * ∫⁻ w, G w := by
  have hmeas : Measurable fun p : Rn n × Rn n ↦ G (p.2 + t • (p.1 - p.2)) :=
    hG.comp (by fun_prop)
  have hrw : ∀ y z : Rn n, z + t • (y - z) = t • y + (1 - t) • z := fun y z ↦ by
    rw [smul_sub, sub_smul, one_smul]; abel
  rcases le_or_gt (1 / 2) t with ht2 | ht2
  · -- integrate in `y` first
    rw [lintegral_lintegral_swap (μ := volume.restrict B) (ν := volume.restrict B)
      (f := fun y z ↦ G (z + t • (y - z))) hmeas.aemeasurable]
    calc ∫⁻ z in B, ∫⁻ y in B, G (z + t • (y - z))
        ≤ ∫⁻ _ in B, 2 ^ n * ∫⁻ w, G w := by
          refine lintegral_mono fun z ↦ ?_
          calc ∫⁻ y in B, G (z + t • (y - z)) ≤ ∫⁻ y, G (z + t • (y - z)) :=
                setLIntegral_le_lintegral _ _
            _ = ∫⁻ y, G (t • y + (1 - t) • z) := by simp_rw [hrw]
            _ ≤ _ := lintegral_comp_smul_add_le hG ht2 _
      _ = 2 ^ n * volume B * ∫⁻ w, G w := by
          rw [setLIntegral_const]
          ring
  · -- integrate in `z` first
    calc ∫⁻ y in B, ∫⁻ z in B, G (z + t • (y - z))
        ≤ ∫⁻ _ in B, 2 ^ n * ∫⁻ w, G w := by
          refine lintegral_mono fun y ↦ ?_
          calc ∫⁻ z in B, G (z + t • (y - z)) ≤ ∫⁻ z, G (z + t • (y - z)) :=
                setLIntegral_le_lintegral _ _
            _ = ∫⁻ z, G ((1 - t) • z + t • y) := by simp_rw [hrw, add_comm]
            _ ≤ _ := lintegral_comp_smul_add_le hG (by linarith) _
      _ = 2 ^ n * volume B * ∫⁻ w, G w := by
          rw [setLIntegral_const]
          ring

/-! ### The segment estimate -/

/-- **Segment formula.** For `u ∈ C¹`:
`|u(y) - u(z)| ≤ |y - z| ∫_{(0,1]} |Du(z + t(y - z))| dt`. -/
theorem enorm_sub_le_lintegral_segment {u : Rn n → ℝ} (hu : ContDiff ℝ 1 u) (y z : Rn n) :
    ‖u y - u z‖ₑ ≤ ‖y - z‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ u (z + t • (y - z))‖ₑ := by
  have : ContinuousSMul ℝ (Rn n) := IsBoundedSMul.continuousSMul
  set γ : ℝ → Rn n := fun t ↦ z + t • (y - z) with hγ
  have hγc : Continuous γ := by fun_prop
  set f' : ℝ → ℝ := fun t ↦ fderiv ℝ u (γ t) (y - z) with hf'
  have hf'c : Continuous f' :=
    ((hu.continuous_fderiv one_ne_zero).comp hγc).clm_apply continuous_const
  have hderiv : ∀ t, HasDerivAt (fun t ↦ u (γ t)) (f' t) t := fun t ↦ by
    have h1 : HasDerivAt γ (y - z) t := by
      convert ((hasDerivAt_id t).smul_const (y - z)).const_add z using 1
      all_goals simp [hγ]
    exact (hu.differentiable one_ne_zero (γ t)).hasFDerivAt.comp_hasDerivAt t h1
  have hFTC : ∫ t in (0 : ℝ)..1, f' t = u y - u z := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
      (hf'c.intervalIntegrable _ _)]
    simp [hγ]
  have hint : IntegrableOn (fun t ↦ ‖f' t‖) (Ioc (0 : ℝ) 1) :=
    (hf'c.norm.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self
  calc ‖u y - u z‖ₑ = ENNReal.ofReal ‖∫ t in (0 : ℝ)..1, f' t‖ := by rw [hFTC, ofReal_norm]
    _ ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..1, ‖f' t‖) :=
        ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm zero_le_one)
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ‖f' t‖ₑ := by
        rw [intervalIntegral.integral_of_le zero_le_one,
          ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ norm_nonneg _)]
        simp_rw [ofReal_norm]
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ u (γ t)‖ₑ * ‖y - z‖ₑ := by
        refine lintegral_mono fun t ↦ ?_
        rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal ((fderiv ℝ u (γ t)).le_opNorm (y - z))
    _ = ‖y - z‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ u (γ t)‖ₑ := by
        rw [lintegral_mul_const' _ _ enorm_ne_top, mul_comm]

/-! ### Poincaré inequality on balls -/

/-- **Double-integral Poincaré inequality.** For `u ∈ C¹(ℝⁿ)` and `B = B_r(x)`:
`∫_B ∫_B |u(y) - u(z)| ≤ 2ⁿ (2r) |B| ∫_B |Du|`. -/
theorem lintegral_lintegral_enorm_sub_le {u : Rn n → ℝ} (hu : ContDiff ℝ 1 u) (x : Rn n)
    (r : ℝ) :
    ∫⁻ y in ball x r, ∫⁻ z in ball x r, ‖u y - u z‖ₑ ≤
      2 ^ n * ENNReal.ofReal (2 * r) * volume (ball x r) *
        ∫⁻ w in ball x r, ‖fderiv ℝ u w‖ₑ := by
  set B := ball x r with hB_def
  have hBm : MeasurableSet B := measurableSet_ball
  set g : Rn n → ℝ≥0∞ := fun w ↦ ‖fderiv ℝ u w‖ₑ with hg_def
  have hg : Measurable g := (hu.continuous_fderiv one_ne_zero).enorm.measurable
  set G := B.indicator g with hG_def
  have hG : Measurable G := hg.indicator hBm
  set F : Rn n → Rn n → ℝ → ℝ≥0∞ := fun y z t ↦ G (z + t • (y - z)) with hF_def
  have hFm : Measurable fun p : (Rn n × ℝ) × Rn n ↦ F p.1.1 p.2 p.1.2 := hG.comp (by fun_prop)
  -- pointwise segment bound
  have hpt : ∀ y ∈ B, ∀ z ∈ B,
      ‖u y - u z‖ₑ ≤ ENNReal.ofReal (2 * r) * ∫⁻ t in Ioc (0 : ℝ) 1, F y z t := by
    intro y hy z hz
    refine (enorm_sub_le_lintegral_segment hu y z).trans ?_
    gcongr ?_ * ?_
    · rw [← ofReal_norm, ← dist_eq_norm]
      refine ENNReal.ofReal_le_ofReal ((dist_triangle_right y z x).trans ?_)
      linarith [mem_ball.1 hy, mem_ball.1 hz]
    · refine (setLIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_).le
      change _ = B.indicator g _
      rw [indicator_of_mem ((convex_ball x r).add_smul_sub_mem hz hy (Ioc_subset_Icc_self ht))]
  calc ∫⁻ y in B, ∫⁻ z in B, ‖u y - u z‖ₑ
      ≤ ∫⁻ y in B, ∫⁻ z in B, ENNReal.ofReal (2 * r) * ∫⁻ t in Ioc (0 : ℝ) 1, F y z t :=
        setLIntegral_mono' hBm fun y hy ↦ setLIntegral_mono' hBm fun z hz ↦ hpt y hy z hz
    _ = ENNReal.ofReal (2 * r) * ∫⁻ y in B, ∫⁻ z in B, ∫⁻ t in Ioc (0 : ℝ) 1, F y z t := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        funext y
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (2 * r) * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in B, ∫⁻ z in B, F y z t := by
        congr 1
        have h1 : ∀ y, ∫⁻ z in B, ∫⁻ t in Ioc (0 : ℝ) 1, F y z t =
            ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in B, F y z t := fun y ↦
          lintegral_lintegral_swap (μ := volume.restrict B)
            (ν := volume.restrict (Ioc (0 : ℝ) 1)) (f := fun z t ↦ F y z t)
            ((hG.comp (by fun_prop) :
              Measurable fun p : Rn n × ℝ ↦ G (p.1 + p.2 • (y - p.1)))).aemeasurable
        simp_rw [h1]
        have hH : Measurable fun p : Rn n × ℝ ↦ ∫⁻ z in B, F p.1 z p.2 :=
          hFm.lintegral_prod_right'
        exact lintegral_lintegral_swap (μ := volume.restrict B)
          (ν := volume.restrict (Ioc (0 : ℝ) 1)) (f := fun y t ↦ ∫⁻ z in B, F y z t)
          hH.aemeasurable
    _ ≤ ENNReal.ofReal (2 * r) * ∫⁻ _ in Ioc (0 : ℝ) 1, 2 ^ n * volume B * ∫⁻ w, G w := by
        gcongr ENNReal.ofReal (2 * r) * ?_
        exact setLIntegral_mono' measurableSet_Ioc fun t ht ↦
          lintegral_lintegral_comp_segment_le hG B t
    _ = 2 ^ n * ENNReal.ofReal (2 * r) * volume B * ∫⁻ w in B, g w := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one,
          hG_def, lintegral_indicator hBm]
        ring

/-- `|u(y) - u_B| ≤ ⨍_B |u(y) - u(z)| dz` for continuous `u` on a ball of positive radius. -/
theorem enorm_sub_setAverage_le {u : Rn n → ℝ} (hu : Continuous u) (x : Rn n) {r : ℝ}
    (hr : 0 < r) (y : Rn n) :
    ‖u y - ⨍ z in ball x r, u z‖ₑ ≤
      (volume (ball x r))⁻¹ * ∫⁻ z in ball x r, ‖u y - u z‖ₑ := by
  set B := ball x r
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hBt : volume B ≠ ⊤ := measure_ball_lt_top.ne
  set V := (volume B).toReal with hV_def
  have hV : 0 < V := ENNReal.toReal_pos hB0 hBt
  have hint : IntegrableOn u B :=
    (hu.continuousOn.integrableOn_compact (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall
  have hint' : IntegrableOn (fun z ↦ u y - u z) B := (integrableOn_const (C := u y) hBt).sub hint
  have heq : u y - ⨍ z in B, u z = V⁻¹ * ∫ z in B, (u y - u z) := by
    rw [setAverage_eq, integral_sub (integrableOn_const (C := u y) hBt) hint, setIntegral_const,
      smul_eq_mul, smul_eq_mul]
    have hVr : volume.real B = V := rfl
    rw [hVr]
    field_simp
  rw [heq, ← ofReal_norm, norm_mul, Real.norm_of_nonneg (inv_nonneg.2 hV.le),
    ENNReal.ofReal_mul (inv_nonneg.2 hV.le), ENNReal.ofReal_inv_of_pos hV, hV_def,
    ENNReal.ofReal_toReal hBt]
  gcongr
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint']
  exact ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)

/-- **`L¹` Poincaré inequality on balls** (EG Thm 4.9 with `p = 1`, `L¹` form).
For `u ∈ C¹(ℝⁿ)`: `∫_{B_r(x)} |u - u_{x,r}| ≤ 2^{n+1} r ∫_{B_r(x)} |Du|`. -/
theorem lintegral_enorm_sub_setAverage_le {u : Rn n → ℝ} (hu : ContDiff ℝ 1 u) (x : Rn n)
    (r : ℝ) :
    ∫⁻ y in ball x r, ‖u y - ⨍ z in ball x r, u z‖ₑ ≤
      2 ^ (n + 1) * ENNReal.ofReal r * ∫⁻ y in ball x r, ‖fderiv ℝ u y‖ₑ := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  set B := ball x r
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume x hr).ne'
  have hBt : volume B ≠ ⊤ := measure_ball_lt_top.ne
  calc ∫⁻ y in B, ‖u y - ⨍ z in B, u z‖ₑ
      ≤ ∫⁻ y in B, (volume B)⁻¹ * ∫⁻ z in B, ‖u y - u z‖ₑ :=
        lintegral_mono fun y ↦ enorm_sub_setAverage_le hu.continuous x hr y
    _ = (volume B)⁻¹ * ∫⁻ y in B, ∫⁻ z in B, ‖u y - u z‖ₑ :=
        lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hB0)
    _ ≤ (volume B)⁻¹ * (2 ^ n * ENNReal.ofReal (2 * r) * volume B *
          ∫⁻ w in B, ‖fderiv ℝ u w‖ₑ) := by
        gcongr
        exact lintegral_lintegral_enorm_sub_le hu x r
    _ = 2 ^ (n + 1) * ENNReal.ofReal r * ∫⁻ y in B, ‖fderiv ℝ u y‖ₑ := by
        rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, pow_succ]
        calc (volume B)⁻¹ * (2 ^ n * (2 * ENNReal.ofReal r) * volume B *
              ∫⁻ w in B, ‖fderiv ℝ u w‖ₑ)
            = ((volume B)⁻¹ * volume B) * (2 ^ n * 2 * ENNReal.ofReal r *
              ∫⁻ w in B, ‖fderiv ℝ u w‖ₑ) := by ring
          _ = _ := by rw [ENNReal.inv_mul_cancel hB0 hBt, one_mul]

/-! ### Relative isoperimetric inequality -/

/-- For every real `c`: `min(|E ∩ A|, |A \ E|) ≤ ∫_A |χ_E - c|`. -/
theorem min_volume_le_lintegral_enorm_indicator_sub {E A : Set (Rn n)} (hE : MeasurableSet E)
    (hA : MeasurableSet A) (c : ℝ) :
    min (volume (E ∩ A)) (volume (A \ E)) ≤ ∫⁻ y in A, ‖E.indicator (1 : Rn n → ℝ) y - c‖ₑ := by
  rw [← lintegral_inter_add_sdiff _ A hE]
  have h1 : ∫⁻ y in A ∩ E, ‖E.indicator (1 : Rn n → ℝ) y - c‖ₑ =
      ‖1 - c‖ₑ * volume (E ∩ A) := by
    rw [setLIntegral_congr_fun (g := fun _ ↦ ‖1 - c‖ₑ) (hA.inter hE)
      (fun y hy ↦ by simp only; rw [indicator_of_mem hy.2, Pi.one_apply]),
      setLIntegral_const, inter_comm]
  have h2 : ∫⁻ y in A \ E, ‖E.indicator (1 : Rn n → ℝ) y - c‖ₑ = ‖c‖ₑ * volume (A \ E) := by
    rw [setLIntegral_congr_fun (g := fun _ ↦ ‖c‖ₑ) (hA.diff hE)
      (fun y hy ↦ by simp only; rw [indicator_of_notMem hy.2, zero_sub, enorm_neg]),
      setLIntegral_const]
  rw [h1, h2]
  have hsum : 1 ≤ ‖1 - c‖ₑ + ‖c‖ₑ := by
    calc (1 : ℝ≥0∞) = ‖(1 - c) + c‖ₑ := by simp
      _ ≤ _ := enorm_add_le _ _
  calc min (volume (E ∩ A)) (volume (A \ E))
      = 1 * min (volume (E ∩ A)) (volume (A \ E)) := (one_mul _).symm
    _ ≤ (‖1 - c‖ₑ + ‖c‖ₑ) * min (volume (E ∩ A)) (volume (A \ E)) := by gcongr
    _ = ‖1 - c‖ₑ * min (volume (E ∩ A)) (volume (A \ E)) +
          ‖c‖ₑ * min (volume (E ∩ A)) (volume (A \ E)) := add_mul _ _ _
    _ ≤ ‖1 - c‖ₑ * volume (E ∩ A) + ‖c‖ₑ * volume (A \ E) := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _

/-- The relative isoperimetric inequality on an inner ball `B_s(x)`, `s < r`. -/
private theorem min_volume_le_of_lt {E : Set (Rn n)} (hE : MeasurableSet E) (x : Rn n)
    {s r : ℝ} (hsr : s < r) :
    min (volume (E ∩ ball x s)) (volume (ball x s \ E)) ≤
      2 ^ (n + 1) * ENNReal.ofReal s * totalVariationOn (ball x r) (E.indicator 1) := by
  set K := 2 ^ (n + 1) * ENNReal.ofReal s * totalVariationOn (ball x r) (E.indicator 1)
  have hli : LocallyIntegrable (E.indicator (1 : Rn n → ℝ)) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hE
  have hL1 := tendstoLpLoc_mollify tendsto_mollifierBump_rOut hli univ (closedBall x s)
    (subset_univ _) (isCompact_closedBall x s)
  have hbound : ∀ᶠ k in atTop, min (volume (E ∩ ball x s)) (volume (ball x s \ E)) ≤
      eLpNorm (mollify (mollifierBump k) (E.indicator 1) - E.indicator 1) 1
        (volume.restrict (closedBall x s)) + K := by
    filter_upwards [(tendsto_order.1 tendsto_mollifierBump_rOut).2 (r - s) (by linarith)]
      with k hk
    set u := mollify (mollifierBump k : ContDiffBump (0 : Rn n)) (E.indicator 1) with hu_def
    set c := ⨍ z in ball x s, u z
    have hu1 : ContDiff ℝ 1 u := (contDiff_mollify _ hli).of_le (by simp)
    have hP := lintegral_enorm_sub_setAverage_le hu1 x s
    have hTV := lintegral_norm_fderiv_mollify_indicator_le_totalVariationOn isOpen_ball hE
      (mollifierBump k) (V := ball x s) measurableSet_ball fun y hy ↦
        closedBall_subset_ball' (show (mollifierBump k : ContDiffBump (0 : Rn n)).rOut +
          dist y x < r by rw [mem_ball] at hy; linarith)
    have hmeas : Measurable fun y ↦ ‖E.indicator (1 : Rn n → ℝ) y - u y‖ₑ :=
      ((measurable_const.indicator hE).sub (contDiff_mollify _ hli).continuous.measurable).enorm
    have h1 : ∫⁻ y in ball x s, ‖E.indicator (1 : Rn n → ℝ) y - u y‖ₑ ≤
        eLpNorm (u - E.indicator 1) 1 (volume.restrict (closedBall x s)) := by
      rw [eLpNorm_one_eq_lintegral_enorm (hu1.continuous.aestronglyMeasurable.sub
        (measurable_one.indicator hE).aestronglyMeasurable)]
      refine (lintegral_mono_set ball_subset_closedBall).trans (le_of_eq ?_)
      congr 1
      funext y
      rw [enorm_sub_rev]
      rfl
    calc min (volume (E ∩ ball x s)) (volume (ball x s \ E))
        ≤ ∫⁻ y in ball x s, ‖E.indicator (1 : Rn n → ℝ) y - c‖ₑ :=
          min_volume_le_lintegral_enorm_indicator_sub hE measurableSet_ball c
      _ ≤ ∫⁻ y in ball x s, (‖E.indicator (1 : Rn n → ℝ) y - u y‖ₑ + ‖u y - c‖ₑ) :=
          lintegral_mono fun y ↦ by
            rw [← sub_add_sub_cancel (E.indicator (1 : Rn n → ℝ) y) (u y) c]
            exact enorm_add_le _ _
      _ ≤ eLpNorm (u - E.indicator 1) 1 (volume.restrict (closedBall x s)) + K := by
          rw [lintegral_add_left hmeas]
          refine add_le_add h1 ?_
          convert hP.trans (mul_le_mul_right hTV _) using 1
  have hlim : Tendsto (fun k ↦ eLpNorm (mollify (mollifierBump k) (E.indicator 1) -
      E.indicator 1) 1 (volume.restrict (closedBall x s)) + K) atTop (𝓝 (0 + K)) :=
    hL1.add tendsto_const_nhds
  rw [zero_add] at hlim
  exact ge_of_tendsto hlim hbound

/-- **Relative isoperimetric inequality, `L¹` form** (EG Thm 5.11 (ii), with the power
`1 - 1/n` replaced by `1`, from the `L¹` Poincaré inequality). For measurable `E`:
`min(|E ∩ B_r(x)|, |B_r(x) \ E|) ≤ 2^{n+1} r TV(E; B_r(x))`. -/
theorem min_volume_le_totalVariationOn_ball {E : Set (Rn n)} (hE : MeasurableSet E) (x : Rn n)
    (r : ℝ) :
    min (volume (E ∩ ball x r)) (volume (ball x r \ E)) ≤
      2 ^ (n + 1) * ENNReal.ofReal r * totalVariationOn (ball x r) (E.indicator 1) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  set s : ℕ → ℝ := fun k ↦ r * (1 - 1 / ((k : ℝ) + 2)) with hs_def
  have hk2 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 2 := fun k ↦ by positivity
  have hsr : ∀ k, s k < r := fun k ↦ by
    have : 0 < r * (1 / ((k : ℝ) + 2)) := by have := hk2 k; positivity
    simp only [hs_def]
    nlinarith
  have hmono : Monotone s := fun i j hij ↦ by
    simp only [hs_def]
    refine mul_le_mul_of_nonneg_left ?_ hr.le
    have : ((i : ℝ) + 2) ≤ (j : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hij 2
    gcongr
  have hUnion : ⋃ k, ball x (s k) = ball x r := by
    refine Subset.antisymm (iUnion_subset fun k ↦ ball_subset_ball (hsr k).le) fun y hy ↦ ?_
    have hd : dist y x < r := hy
    obtain ⟨k, hk⟩ := exists_nat_gt (r / (r - dist y x))
    refine mem_iUnion.2 ⟨k, mem_ball.2 ?_⟩
    have hrd : 0 < r - dist y x := by linarith
    have h1 : r / (r - dist y x) < (k : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ hrd] at h1
    have h2 : r / ((k : ℝ) + 2) < r - dist y x := by
      rw [div_lt_iff₀ (hk2 k)]
      linarith
    simp only [hs_def, mul_sub, mul_one, mul_one_div]
    linarith
  have hA : Tendsto (fun k ↦ volume (E ∩ ball x (s k))) atTop
      (𝓝 (volume (E ∩ ball x r))) := by
    rw [← hUnion, inter_iUnion]
    exact tendsto_measure_iUnion_atTop fun i j hij ↦
      inter_subset_inter_right _ (ball_subset_ball (hmono hij))
  have hB : Tendsto (fun k ↦ volume (ball x (s k) \ E)) atTop (𝓝 (volume (ball x r \ E))) := by
    rw [← hUnion, iUnion_sdiff]
    exact tendsto_measure_iUnion_atTop fun i j hij ↦
      sdiff_subset_sdiff_left (ball_subset_ball (hmono hij))
  refine le_of_tendsto' (hA.min hB) fun k ↦ (min_volume_le_of_lt hE x (hsr k)).trans ?_
  gcongr
  exact (hsr k).le

/-- **Relative isoperimetric inequality, pair form.** For a Gauss–Green pair `(μ, ν)` of a
measurable `E` on `Ω` and `B_r(x) ⊆ Ω`: `min(|E ∩ B_r(x)|, |B_r(x) \ E|) ≤ 2^{n+1} r μ(B_r(x))`. -/
theorem IsGaussGreenPair.min_volume_le_measure_ball {Ω E : Set (Rn n)} {μ : Measure (Rn n)}
    {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν) (hE : MeasurableSet E) {x : Rn n} {r : ℝ}
    (hB : ball x r ⊆ Ω) :
    min (volume (E ∩ ball x r)) (volume (ball x r \ E)) ≤
      2 ^ (n + 1) * ENNReal.ofReal r * μ (ball x r) := by
  rw [← h.totalVariationOn_indicator_eq hE isOpen_ball hB]
  exact min_volume_le_totalVariationOn_ball hE x r

/-- **Zero variation in a ball.** If `TV(E; B_r(x)) = 0` then `E` is a.e. empty or a.e. full in
`B_r(x)`. This is the last step of the null case of EG Thm 5.23 (`Perimeter/Criterion.lean`). -/
theorem volume_inter_ball_eq_zero_or_of_totalVariationOn_eq_zero {E : Set (Rn n)}
    (hE : MeasurableSet E) {x : Rn n} {r : ℝ}
    (h : totalVariationOn (ball x r) (E.indicator 1) = 0) :
    volume (E ∩ ball x r) = 0 ∨ volume (ball x r \ E) = 0 := by
  have := min_volume_le_totalVariationOn_ball hE x r
  rw [h, mul_zero, nonpos_iff_eq_zero] at this
  rcases min_choice (volume (E ∩ ball x r)) (volume (ball x r \ E)) with hm | hm
  · exact Or.inl (hm ▸ this)
  · exact Or.inr (hm ▸ this)

end GMTFoundations
