/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.GMT.Isodiametric
public import GMTFoundations.GMT.Basic

/-!
# Hausdorff measure and Lebesgue measure

On `ℝ^d`, the `d`-dimensional Hausdorff measure `μH[d]` (Mathlib's normalization, without the
factor `ω_d / 2^d`) satisfies `ω_d • μH[d] = 2^d • volume`, where `ω_d = |B_1|`. Hence the
normalized Hausdorff measure `hausdorffN d d` is Lebesgue measure (Evans–Gariepy
Thm 2.5), and on an affine `d`-plane `p + L(ℝ^d)` of `ℝⁿ` the normalized `ℋ^d` is
the image of `d`-dimensional Lebesgue measure.

Since `μH[d]` is an additive Haar measure on `ℝ^d` (Mathlib), it is `c • volume`, and only the
constant has to be identified:

* `≥` (`two_pow_smul_volume_le_hausdorffMeasure`): the isodiametric inequality
  `2^d |s| ≤ ω_d (diam s)^d` fed into `Measure.le_hausdorffMeasure`.
* `≤` (`volume_ball_mul_hausdorffMeasure_ball_le`): a Besicovitch covering of almost all of the
  unit ball by disjoint small closed balls; the `δ`-approximating outer measure of such a ball is
  at most `(2r)^d = 2^d |B_r| / ω_d`, and the uncovered part is Lebesgue-null, hence `μH[d]`-null.

## Main statements

* `GMTFoundations.GMT.volume_ball_smul_hausdorffMeasure`: `ω_d • μH[d] = 2^d • volume`
  (this is the constant of Mathlib's `proof_wanted addHaarScalarFactor_hausdorffMeasure_eq`, in
  the Euclidean normalization).
* `GMTFoundations.GMT.hausdorffN_self_eq_volume`: `hausdorffN d d = volume`.
* `GMTFoundations.GMT.map_volume_add_linearIsometry_eq_hausdorffN`: for a linear isometric
  embedding `L : ℝ^d → ℝⁿ` and `p ∈ ℝⁿ`, `volume.map (p + L ·) = ℋ^d ⌊ (p + L(ℝ^d))`.
* `GMTFoundations.GMT.map_volume_affineIsometry_eq_hausdorffN`: the case `d = n - 1`
  (hyperplanes).

## References

* H. Federer, *Geometric Measure Theory*, Springer, 1969.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
-/

public section

open MeasureTheory Measure Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace GMTFoundations.GMT

variable {d : ℕ}

/-- `μH[d]` is absolutely continuous with respect to Lebesgue measure on `ℝ^d` (it is a Haar
measure). -/
theorem hausdorffMeasure_absolutelyContinuous_volume :
    (μH[d] : Measure (Rn d)) ≪ volume := by
  rw [isAddLeftInvariant_eq_smul (μH[d] : Measure (Rn d)) volume]
  exact AbsolutelyContinuous.smul_left AbsolutelyContinuous.rfl _

/-- Upper bound for `μH[d]` on `ℝ^d`: `ω_d μH[d](B_1) ≤ 2^d ω_d`. Almost all of `B_1` is covered by
countably many disjoint closed balls `B̄_{ρ_i}(x_i) ⊆ B_1` with `2ρ_i < δ` (Besicovitch); the
`δ`-approximating outer measure of each is at most `(2ρ_i)^d = 2^d |B̄_{ρ_i}| / ω_d`, and the
uncovered remainder is Lebesgue-null, hence `μH[d]`-null. -/
theorem volume_ball_mul_hausdorffMeasure_ball_le :
    volume (ball (0 : Rn d) 1) * μH[d] (ball (0 : Rn d) 1) ≤
      2 ^ d * volume (ball (0 : Rn d) 1) := by
  set U := ball (0 : Rn d) 1
  set ω := volume U
  set m : Set (Rn d) → ℝ≥0∞ := fun s => ediam s ^ (d : ℝ) with hm
  have hH : ∀ s, (μH[d] : Measure (Rn d)) s = OuterMeasure.mkMetric' m s := fun s => by
    rw [hausdorffMeasure, ← OuterMeasure.coe_mkMetric]; rfl
  rw [hH, OuterMeasure.mkMetric', OuterMeasure.iSup_apply, ENNReal.mul_iSup]
  refine iSup_le fun r => ?_
  rw [OuterMeasure.iSup_apply, ENNReal.mul_iSup]
  refine iSup_le fun hr => ?_
  set δ : ℝ := (min r 1).toReal with hδ
  have hδr : ENNReal.ofReal δ ≤ r := by
    rw [hδ, ENNReal.ofReal_toReal (by simp)]; exact min_le_left _ _
  have hδpos : 0 < δ := ENNReal.toReal_pos (by simp [hr.ne']) (by simp)
  have hδpos' : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδpos
  obtain ⟨t, ρ, htc, htU, hρ, hnull, hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae (volume : Measure (Rn d)) (fun _ => univ) U
      (fun x _ ε hε => ⟨ε / 2, trivial, by positivity, by linarith⟩)
      (fun x => min (δ / 2) (1 - ‖x‖))
      (fun x hx => lt_min (by positivity) (sub_pos.2 (mem_ball_zero_iff.1 hx)))
  set B := ⋃ x ∈ t, closedBall x (ρ x) with hB
  have hρpos : ∀ x ∈ t, 0 < ρ x := fun x hx => (hρ x hx).2.1
  have hBU : B ⊆ U := iUnion₂_subset fun x hx => by
    refine closedBall_subset_ball' ?_
    have := (hρ x hx).2.2
    have h1 : ρ x < 1 - ‖x‖ := this.trans_le (min_le_right _ _)
    rw [dist_zero_right]; linarith
  have hdiam : ∀ x ∈ t, ediam (closedBall x (ρ x)) ≤ ENNReal.ofReal (2 * ρ x) := fun x hx => by
    refine ediam_le_of_forall_dist_le fun a ha b hb => ?_
    have := dist_triangle_right a b x
    rw [mem_closedBall] at ha hb
    linarith
  have hsmall : ∀ x ∈ t, ENNReal.ofReal (2 * ρ x) ≤ ENNReal.ofReal δ := fun x hx => by
    have := (hρ x hx).2.2
    have h1 : ρ x < δ / 2 := this.trans_le (min_le_left _ _)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the pre-measure at scale `r` is dominated by the one at scale `δ`
  calc ω * OuterMeasure.mkMetric'.pre m r U
      ≤ ω * OuterMeasure.mkMetric'.pre m (ENNReal.ofReal δ) U := by
        gcongr; exact OuterMeasure.mkMetric'.mono_pre m hδr
    _ ≤ ω * (OuterMeasure.mkMetric'.pre m (ENNReal.ofReal δ) B +
          OuterMeasure.mkMetric'.pre m (ENNReal.ofReal δ) (U \ B)) := by
        gcongr
        exact (measure_mono (by simp)).trans (measure_union_le _ _)
    _ ≤ ω * (∑' x : t, ENNReal.ofReal (2 * ρ x) ^ d + 0) := by
        gcongr
        · refine (measure_biUnion_le _ htc _).trans (ENNReal.tsum_le_tsum fun x => ?_)
          refine (OuterMeasure.mkMetric'.pre_le ((hdiam x x.2).trans (hsmall x x.2))).trans ?_
          rw [hm, ← ENNReal.rpow_natCast]
          exact ENNReal.rpow_le_rpow (hdiam x x.2) (Nat.cast_nonneg d)
        · have h0 : (μH[d] : Measure (Rn d)) (U \ B) = 0 :=
            hausdorffMeasure_absolutelyContinuous_volume hnull
          rw [hH] at h0
          refine le_of_le_of_eq ?_ h0
          exact (le_iSup₂ (f := fun r (_ : 0 < r) => OuterMeasure.mkMetric'.pre m r)
            (ENNReal.ofReal δ) hδpos' : _) (U \ B)
    _ = 2 ^ d * ∑' x : t, volume (closedBall (x : Rn d) (ρ x)) := by
        rw [add_zero, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        congr 1 with x
        rw [Measure.addHaar_closedBall volume _ (hρpos x x.2).le, finrank_euclideanSpace_fin,
          ENNReal.ofReal_mul zero_le_two, mul_pow, ENNReal.ofReal_pow (hρpos x x.2).le,
          ENNReal.ofReal_ofNat]
        ring
    _ = 2 ^ d * volume B := by
        congr 1
        exact (measure_biUnion htc hdisj fun x _ => measurableSet_closedBall).symm
    _ ≤ 2 ^ d * ω := by gcongr; exact measure_mono hBU

/-- Lower bound for `μH[d]` on `ℝ^d`, from the isodiametric inequality:
`2^d • volume ≤ ω_d • μH[d]`. -/
theorem two_pow_smul_volume_le_hausdorffMeasure :
    (2 : ℝ≥0∞) ^ d • (volume : Measure (Rn d)) ≤
      volume (ball (0 : Rn d) 1) • (μH[d] : Measure (Rn d)) := by
  set ω := volume (ball (0 : Rn d) 1)
  have hω0 : ω ≠ 0 := (measure_ball_pos volume 0 zero_lt_one).ne'
  have hωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have h : (ω⁻¹ * 2 ^ d) • (volume : Measure (Rn d)) ≤ μH[d] := by
    refine le_hausdorffMeasure _ _ 1 zero_lt_one fun s _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.rpow_natCast, mul_assoc,
      ENNReal.inv_mul_le_iff hω0 hωt]
    exact two_pow_mul_volume_le_mul_ediam_pow s
  intro s
  have hs := h s
  rw [Measure.smul_apply, smul_eq_mul, mul_assoc] at hs
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  calc 2 ^ d * volume s = ω * (ω⁻¹ * (2 ^ d * volume s)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hω0 hωt, one_mul]
    _ ≤ ω * μH[d] s := by gcongr

/-- The Hausdorff normalization constant on `ℝ^d`: `ω_d • μH[d] = 2^d • volume`. -/
theorem volume_ball_smul_hausdorffMeasure :
    volume (ball (0 : Rn d) 1) • (μH[d] : Measure (Rn d)) = (2 : ℝ≥0∞) ^ d • volume := by
  set ω := volume (ball (0 : Rn d) 1)
  have hω0 : ω ≠ 0 := (measure_ball_pos volume 0 zero_lt_one).ne'
  have hωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  set c : ℝ≥0∞ := (addHaarScalarFactor (μH[d] : Measure (Rn d)) volume : ℝ≥0∞)
  have hc : (μH[d] : Measure (Rn d)) = c • volume := by
    conv_lhs => rw [isAddLeftInvariant_eq_smul (μH[d] : Measure (Rn d)) volume]
    rfl
  have hup : ω * c ≤ 2 ^ d := by
    have h := volume_ball_mul_hausdorffMeasure_ball_le (d := d)
    rw [hc, Measure.smul_apply, smul_eq_mul, ← mul_assoc] at h
    exact (ENNReal.mul_le_mul_iff_left hω0 hωt).1 h
  have hlow : 2 ^ d ≤ ω * c := by
    have h := two_pow_smul_volume_le_hausdorffMeasure (d := d) (ball 0 1)
    rw [hc, Measure.smul_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc] at h
    exact (ENNReal.mul_le_mul_iff_left hω0 hωt).1 h
  rw [hc, smul_smul, le_antisymm hup hlow]

/-- On `ℝ^d`, the normalized Hausdorff measure `ℋ^d` is Lebesgue measure. -/
theorem hausdorffN_self_eq_volume (d : ℕ) : hausdorffN d d = (volume : Measure (Rn d)) := by
  set ω := volume (ball (0 : Rn d) 1)
  have hωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have h2 : (2 : ℝ≥0∞) ^ d ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2t : (2 : ℝ≥0∞) ^ d ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hconst : ENNReal.ofReal (unitBallVolume d / 2 ^ d) = ((2 : ℝ≥0∞) ^ d)⁻¹ * ω := by
    rw [unitBallVolume, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_toReal hωt,
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm]
  rw [hausdorffN, hconst, ← smul_smul, volume_ball_smul_hausdorffMeasure, smul_smul,
    ENNReal.inv_mul_cancel h2 h2t, one_smul]

/-- For a linear isometric embedding `L : ℝ^d → ℝᵐ` and `p ∈ ℝᵐ`, the image of `d`-dimensional
Lebesgue measure under `y ↦ p + L y` is `ℋ^d` restricted to the affine plane `p + L(ℝ^d)`. -/
theorem map_volume_add_linearIsometry_eq_hausdorffN {m : ℕ} (L : Rn d →ₗᵢ[ℝ] Rn m) (p : Rn m) :
    (volume : Measure (Rn d)).map (fun y => p + L y) =
      (hausdorffN m d).restrict (range fun y => p + L y) := by
  have hf : Isometry fun y => p + L y := (isometry_add_left p).comp L.isometry
  rw [← hausdorffN_self_eq_volume, hausdorffN, hausdorffN, Measure.map_smul,
    hf.map_hausdorffMeasure (Or.inl (Nat.cast_nonneg d)), Measure.restrict_smul]
  exact hf.continuous.aemeasurable

/-- On a hyperplane `p + L(ℝ^{n-1})` of `ℝⁿ`, `ℋ^{n-1}` is the image of
`(n-1)`-dimensional Lebesgue measure. -/
theorem map_volume_affineIsometry_eq_hausdorffN {n : ℕ} (L : Rn (n - 1) →ₗᵢ[ℝ] Rn n) (p : Rn n) :
    (volume : Measure (Rn (n - 1))).map (fun y => p + L y) =
      (hausdorffN n (n - 1)).restrict (range fun y => p + L y) :=
  map_volume_add_linearIsometry_eq_hausdorffN L p

variable {n : ℕ} in
/-- **Unconditional form** of `hausdorffN_eq_euclideanHausdorffMeasure`: the hypothesis
`ℋ^d = ℒ^d` on `ℝ^d` is `hausdorffN_self_eq_volume`. -/
theorem hausdorffN_eq_euclideanHausdorffMeasure' {d : ℕ} : hausdorffN n d = μHE[d] :=
  hausdorffN_eq_euclideanHausdorffMeasure (hausdorffN_self_eq_volume d)

end GMTFoundations.GMT
