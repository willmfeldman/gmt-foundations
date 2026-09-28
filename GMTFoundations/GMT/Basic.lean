/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.GMT
public import GMTFoundations.GMT.Polar
public import GMTFoundations.Common.Hyperplane
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Basic facts on the normalized Hausdorff measure

We work with Mathlib's Euclidean Hausdorff measure `μHE[d]`
(`Mathlib/Geometry/Euclidean/Volume/Measure.lean`), a constant multiple of `μH[d]` that agrees with
Lebesgue measure on `d`-dimensional inner product spaces. The project's `hausdorffN n d` is another
constant multiple of `μH[d]`.

* `hausdorffN_eq_euclideanHausdorffMeasure`: if `hausdorffN d d = volume` (the normalization
  `ℋ^d = ℒ^d` on `ℝ^d`) then `hausdorffN n d = μHE[d]` on every `ℝⁿ`; the primed version
  (`GMT/HausdorffLebesgue.lean`) discharges the hypothesis with `hausdorffN_self_eq_volume`.
* `hausdorffN_eq_zero_iff`, `euclideanHausdorffMeasure_eq_zero_iff`, and the `< ∞` versions: null
  sets and sets of finite measure agree for all these measures (no normalization needed).
* `LipschitzOnWith.euclideanHausdorffMeasure_image_le`: `μHE[d] (f '' s) ≤ K^d μHE[d] s`.
* `hyperplane ν = {y | ⟪y, ν⟫ = 0}` and `euclideanHausdorffMeasure_hyperplane_inter_closedBall`:
  `μHE[n-1] (ν^⊥ ∩ B̄_r(p)) = ω_{n-1} r^{n-1}` for `p ∈ ν^⊥` (and the open-ball version).
* `lintegral_hyperplane_comp_smul_sub`: the blow-up `y ↦ r⁻¹ (y - p)` scales integrals over `ν^⊥`
  by `r^d`, for `p ∈ ν^⊥`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology Module
open scoped NNReal ENNReal RealInnerProductSpace Pointwise

noncomputable section

namespace GMTFoundations.GMT

variable {n : ℕ}

/-! ### Normalizations -/

theorem euclideanHausdorffMeasure_eq_smul {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (d : ℕ) :
    (μHE[d] : Measure X) =
      ((Measure.addHaarScalarFactor (volume : Measure (Rn d)) μH[d] : ℝ≥0) : ℝ≥0∞) •
        μH[(d : ℝ)] := by
  rw [Measure.euclideanHausdorffMeasure_def]
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]

theorem addHaarScalarFactor_hausdorffMeasure_ne_zero (d : ℕ) :
    ((Measure.addHaarScalarFactor (volume : Measure (Rn d)) μH[d] : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
  simpa using Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d

theorem hausdorffN_const_pos (d : ℕ) : 0 < ENNReal.ofReal (unitBallVolume d / 2 ^ d) :=
  ENNReal.ofReal_pos.2 (div_pos (unitBallVolume_pos d) (pow_pos two_pos d))

/-- **Normalization.** If `ℋ^d = ℒ^d` on `ℝ^d`, then
`hausdorffN n d` is Mathlib's Euclidean Hausdorff measure `μHE[d]` on every `ℝⁿ`. -/
theorem hausdorffN_eq_euclideanHausdorffMeasure {d : ℕ}
    (hHausVol : hausdorffN d d = (volume : Measure (Rn d))) : hausdorffN n d = μHE[d] := by
  set c : ℝ≥0∞ := ((Measure.addHaarScalarFactor (volume : Measure (Rn d)) μH[d] : ℝ≥0) : ℝ≥0∞)
  have hvol : (μHE[d] : Measure (Rn d)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume d
  have h := hHausVol.trans hvol.symm
  rw [hausdorffN, euclideanHausdorffMeasure_eq_smul] at h
  have hB := congrArg (fun μ : Measure (Rn d) => μ (ball 0 1)) h
  simp only [Measure.smul_apply, smul_eq_mul] at hB
  have h0 : (μH[(d : ℝ)] : Measure (Rn d)) (ball 0 1) ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have htop : (μH[(d : ℝ)] : Measure (Rn d)) (ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  have hc : ENNReal.ofReal (unitBallVolume d / 2 ^ d) = c :=
    (ENNReal.mul_left_inj h0 htop).1 hB
  rw [hausdorffN, euclideanHausdorffMeasure_eq_smul, hc]

theorem hausdorffN_apply (d : ℕ) (s : Set (Rn n)) :
    hausdorffN n d s = ENNReal.ofReal (unitBallVolume d / 2 ^ d) * μH[(d : ℝ)] s := by
  rw [hausdorffN, Measure.smul_apply, smul_eq_mul]

theorem hausdorffN_eq_zero_iff {d : ℕ} {s : Set (Rn n)} :
    hausdorffN n d s = 0 ↔ μH[(d : ℝ)] s = 0 := by
  rw [hausdorffN_apply, mul_eq_zero, or_iff_right (hausdorffN_const_pos d).ne']

theorem hausdorffN_lt_top_iff {d : ℕ} {s : Set (Rn n)} :
    hausdorffN n d s < ∞ ↔ μH[(d : ℝ)] s < ∞ := by
  rw [hausdorffN_apply, ENNReal.mul_lt_top_iff]
  constructor
  · rintro (⟨-, h⟩ | h | h)
    · exact h
    · exact absurd h (hausdorffN_const_pos d).ne'
    · exact h ▸ ENNReal.zero_lt_top
  · exact fun h => Or.inl ⟨ENNReal.ofReal_lt_top, h⟩

theorem euclideanHausdorffMeasure_apply {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (d : ℕ) (s : Set X) :
    (μHE[d] : Measure X) s =
      ((Measure.addHaarScalarFactor (volume : Measure (Rn d)) μH[d] : ℝ≥0) : ℝ≥0∞) *
        μH[(d : ℝ)] s := by
  rw [euclideanHausdorffMeasure_eq_smul, Measure.smul_apply, smul_eq_mul]

theorem euclideanHausdorffMeasure_eq_zero_iff {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {d : ℕ} {s : Set X} : (μHE[d] : Measure X) s = 0 ↔ μH[(d : ℝ)] s = 0 := by
  rw [euclideanHausdorffMeasure_apply, mul_eq_zero,
    or_iff_right (addHaarScalarFactor_hausdorffMeasure_ne_zero d)]

theorem euclideanHausdorffMeasure_lt_top_iff {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {d : ℕ} {s : Set X} : (μHE[d] : Measure X) s < ∞ ↔ μH[(d : ℝ)] s < ∞ := by
  rw [euclideanHausdorffMeasure_apply, ENNReal.mul_lt_top_iff]
  constructor
  · rintro (⟨-, h⟩ | h | h)
    · exact h
    · exact absurd h (addHaarScalarFactor_hausdorffMeasure_ne_zero d)
    · exact h ▸ ENNReal.zero_lt_top
  · exact fun h => Or.inl ⟨ENNReal.coe_lt_top, h⟩

theorem hausdorffN_eq_zero_iff_euclidean {d : ℕ} {s : Set (Rn n)} :
    hausdorffN n d s = 0 ↔ (μHE[d] : Measure (Rn n)) s = 0 := by
  rw [hausdorffN_eq_zero_iff, euclideanHausdorffMeasure_eq_zero_iff]

theorem hausdorffN_lt_top_iff_euclidean {d : ℕ} {s : Set (Rn n)} :
    hausdorffN n d s < ∞ ↔ (μHE[d] : Measure (Rn n)) s < ∞ := by
  rw [hausdorffN_lt_top_iff, euclideanHausdorffMeasure_lt_top_iff]

/-- A Lipschitz map increases `μHE[d]` by at most the factor `K ^ d`. -/
theorem _root_.LipschitzOnWith.euclideanHausdorffMeasure_image_le {X Y : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {K : ℝ≥0} {s : Set X} (h : LipschitzOnWith K f s) (d : ℕ) :
    (μHE[d] : Measure Y) (f '' s) ≤ (K : ℝ≥0∞) ^ d * (μHE[d] : Measure X) s := by
  rw [euclideanHausdorffMeasure_apply, euclideanHausdorffMeasure_apply, mul_left_comm]
  gcongr
  simpa [ENNReal.rpow_natCast] using h.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d)

/-! ### Hyperplanes -/

theorem hyperplane_eq_orthogonal (ν : Rn n) :
    hyperplane ν = (((ℝ ∙ ν)ᗮ : Submodule ℝ (Rn n)) : Set (Rn n)) := by
  ext y
  simp [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]

theorem isClosed_hyperplane (ν : Rn n) : IsClosed (hyperplane ν) :=
  isClosed_eq (continuous_id.inner continuous_const) continuous_const

theorem measurableSet_hyperplane (ν : Rn n) : MeasurableSet (hyperplane ν) :=
  (isClosed_hyperplane ν).measurableSet

theorem finrank_orthogonal_span_singleton' (hn : 1 ≤ n) {ν : Rn n} (hν : ν ≠ 0) :
    finrank ℝ ((ℝ ∙ ν)ᗮ : Submodule ℝ (Rn n)) = n - 1 := by
  have h := (ℝ ∙ ν).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hν, finrank_euclideanSpace_fin] at h
  omega

/-- `ω_d` from the Gamma-function formula for the volume of balls. -/
theorem unitBallVolume_eq {d : ℕ} (hd : 0 < d) :
    unitBallVolume d = √Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
  haveI : Nontrivial (Rn d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  rw [unitBallVolume, InnerProductSpace.volume_ball, finrank_euclideanSpace_fin,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal]
  positivity

/-- On the hyperplane `ν^⊥`, `μHE[n-1]` of a closed ball centred on it is `ω_{n-1} r^{n-1}`. -/
theorem euclideanHausdorffMeasure_hyperplane_inter_closedBall (hn : 2 ≤ n) {ν : Rn n}
    (hν : ν ≠ 0) {p : Rn n} (hp : p ∈ hyperplane ν) {r : ℝ} (hr : 0 ≤ r) :
    (μHE[n - 1] : Measure (Rn n)) (hyperplane ν ∩ closedBall p r) =
      ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)) := by
  set K : Submodule ℝ (Rn n) := (ℝ ∙ ν)ᗮ
  have hK : finrank ℝ K = n - 1 := finrank_orthogonal_span_singleton' (by omega) hν
  have hpK : p ∈ K := by rw [hyperplane_eq_orthogonal] at hp; exact hp
  haveI : Nontrivial K := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have himage : hyperplane ν ∩ closedBall p r =
      Subtype.val '' (closedBall (⟨p, hpK⟩ : K) r) := by
    ext y
    simp only [mem_inter_iff, mem_closedBall, mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, hyperplane_eq_orthogonal, SetLike.mem_coe]
    constructor
    · rintro ⟨hy, hyr⟩
      exact ⟨hy, hyr⟩
    · rintro ⟨hy, hyr⟩
      exact ⟨hy, hyr⟩
  have hvol : (μHE[n - 1] : Measure K) = volume := by
    have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := K)
    rwa [hK] at this
  rw [himage, isometry_subtype_coe.euclideanHausdorffMeasure_image, hvol,
    InnerProductSpace.volume_closedBall, hK, unitBallVolume_eq (by omega),
    ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hr, mul_comm]

/-- On the hyperplane `ν^⊥`, `μHE[n-1]` of an open ball centred on it is `ω_{n-1} r^{n-1}`. -/
theorem euclideanHausdorffMeasure_hyperplane_inter_ball (hn : 2 ≤ n) {ν : Rn n}
    (hν : ν ≠ 0) {p : Rn n} (hp : p ∈ hyperplane ν) {r : ℝ} (hr : 0 ≤ r) :
    (μHE[n - 1] : Measure (Rn n)) (hyperplane ν ∩ ball p r) =
      ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)) := by
  set K : Submodule ℝ (Rn n) := (ℝ ∙ ν)ᗮ
  have hK : finrank ℝ K = n - 1 := finrank_orthogonal_span_singleton' (by omega) hν
  have hpK : p ∈ K := by rw [hyperplane_eq_orthogonal] at hp; exact hp
  haveI : Nontrivial K := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have himage : hyperplane ν ∩ ball p r = Subtype.val '' (ball (⟨p, hpK⟩ : K) r) := by
    ext y
    simp only [mem_inter_iff, mem_ball, mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, hyperplane_eq_orthogonal, SetLike.mem_coe]
    constructor
    · rintro ⟨hy, hyr⟩
      exact ⟨hy, hyr⟩
    · rintro ⟨hy, hyr⟩
      exact ⟨hy, hyr⟩
  have hvol : (μHE[n - 1] : Measure K) = volume := by
    have := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := K)
    rwa [hK] at this
  rw [himage, isometry_subtype_coe.euclideanHausdorffMeasure_image, hvol,
    InnerProductSpace.volume_ball, hK, unitBallVolume_eq (by omega),
    ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow hr, mul_comm]

/-! ### Blow-ups -/

/-- The blow-up map `y ↦ r⁻¹ • (y - p)` pushes `μHE[d]` forward to `r^d μHE[d]`. -/
theorem map_smul_sub_euclideanHausdorffMeasure (d : ℕ) (p : Rn n) {r : ℝ} (hr : 0 < r) :
    (μHE[d] : Measure (Rn n)).map (fun y => r⁻¹ • (y - p)) =
      ENNReal.ofReal (r ^ d) • (μHE[d] : Measure (Rn n)) := by
  have hmeas : Measurable fun y : Rn n => r⁻¹ • (y - p) := by fun_prop
  ext A hA
  rw [Measure.map_apply hmeas hA, Measure.smul_apply, smul_eq_mul]
  have hpre : (fun y : Rn n => r⁻¹ • (y - p)) ⁻¹' A = (fun y => y + -p) ⁻¹' (r • A) := by
    ext y
    simp only [mem_preimage, ← sub_eq_add_neg]
    rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  rw [hpre, measure_preimage_add_right, Measure.euclideanHausdorffMeasure_smul₀ d hr.ne',
    ENNReal.smul_def, smul_eq_mul]
  congr 1
  rw [Real.nnnorm_of_nonneg hr.le, ENNReal.coe_pow, ENNReal.ofReal_pow hr.le]
  congr 1
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg hr.le]

/-- Blow-ups of integrals over the hyperplane `ν^⊥` at a point `p ∈ ν^⊥`. -/
theorem lintegral_hyperplane_comp_smul_sub (d : ℕ) {ν p : Rn n} (hp : p ∈ hyperplane ν)
    {r : ℝ} (hr : 0 < r) (g : Rn n → ℝ≥0∞) :
    ∫⁻ y in hyperplane ν, g (r⁻¹ • (y - p)) ∂μHE[d] =
      ENNReal.ofReal (r ^ d) * ∫⁻ y in hyperplane ν, g y ∂μHE[d] := by
  let T : Rn n ≃ᵐ Rn n :=
    (Homeomorph.addRight (-p)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
      |>.toMeasurableEquiv
  have hT : ∀ y, T y = r⁻¹ • (y - p) := fun y => by
    simp [T, sub_eq_add_neg]
  have hTH : ∀ y, T y ∈ hyperplane ν ↔ y ∈ hyperplane ν := by
    intro y
    rw [hT]
    simp only [mem_hyperplane, inner_smul_left, inner_sub_left, mem_hyperplane.1 hp, sub_zero,
      RCLike.conj_to_real, mul_eq_zero, inv_eq_zero, hr.ne', false_or]
  have hind : (hyperplane ν).indicator (fun y => g (r⁻¹ • (y - p))) =
      fun y => (hyperplane ν).indicator g (T y) := by
    ext y
    by_cases hy : y ∈ hyperplane ν
    · rw [indicator_of_mem hy, indicator_of_mem ((hTH y).2 hy), hT]
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h => hy ((hTH y).1 h))]
  rw [← lintegral_indicator (measurableSet_hyperplane ν), hind,
    ← lintegral_map_equiv _ T, show (T : Rn n → Rn n) = fun y => r⁻¹ • (y - p) from funext hT,
    map_smul_sub_euclideanHausdorffMeasure d p hr, lintegral_smul_measure,
    lintegral_indicator (measurableSet_hyperplane ν), smul_eq_mul]

end GMTFoundations.GMT
