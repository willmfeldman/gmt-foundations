/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.ReducedBoundary
public import GMTFoundations.GMT.Basic
import GMTFoundations.Perimeter.Slicing
import GMTFoundations.Perimeter.Isoperimetric
import GMTFoundations.Perimeter.Poincare
import GMTFoundations.GMT.Polar
import GMTFoundations.BV.TotalVariation
public import GMTFoundations.Perimeter.DensityEstimates.Lemma53
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Covering comparisons between `μ` and `ℋ^k`

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (EG), Lemma 5.4 and its proof.

* **Covering comparisons**:
  * (a) `mul_hausdorffMeasure_le_of_frequently`, `mul_hausdorffN_le_of_frequently`,
    `mul_hausdorffN_le_of_le_limsup`: if `μ(B_r(x)) > t r^k` for arbitrarily small `r` at every
    `x ∈ A` (e.g. `limsup_{r→0} μ(B_r(x))/r^k ≥ t`), then `t ℋ^k(A) ≤ C_k μ(U)` for every open
    `U ⊇ A` (EG Lemma 5.4 proof; EG uses `liminf`, only small radii matter).
    `hausdorffN_eq_zero_of_measure_eq_zero`: the null case inside an open `Ω` on whose compact
    subsets `μ` is finite (the setting of a Gauss–Green pair), via
    `exists_isOpen_subset_measure_le`.
  * (b) `measure_le_mul_hausdorffMeasure_of_forall_ball_le`,
    `measure_le_mul_hausdorffN_of_forall_ball_le`: if `μ(B_r(x)) ≤ t r^k` for all `x ∈ A` and
    `0 < r < r₀`, then `μ(A) ≤ t μH[k](A) = (2^k/ω_k) t ℋ^k(A)`.
  * (a), quantitative, division form: `hausdorffN_le_mul_measure_of_le_limsup`
    (`ℋ^k(A) ≤ (C_k/t) μ(U)`).
  * `exists_isOpen_subset_measure_le_add`: `μ(U) ≤ μ(A) + ε` for some open `A ⊆ U ⊆ Ω`, for a
    measure finite on compact subsets of `Ω` (outer regularity of `μ` on the subspace `Ω`).
  * (c) `IsGaussGreenPair.hausdorffN_le_mul_measure` (EG Lemma 5.4): `ℋ^{n-1}(B) ≤ C_n μ(B)`
    for every `B ⊆ ∂*E`, `C_n = reducedBoundaryHausdorffConst n`.

The results (a) and (b) are stated for general `k` (the application is `k = n - 1`) and a general
measure `μ` on `ℝⁿ`; no measurability of `A` is used. Balls are open, as in the definitions of this
library (EG's balls are closed).

## Constants

* (a): Mathlib's Vitali lemma for open balls
  (`Vitali.exists_disjoint_subfamily_covering_enlargement_ball`) needs an enlargement factor
  `τ > 3`; we take `τ = 4`, so the enlarged balls have diameter `≤ 8r`, and `C_k = 8^k` for
  `μH[k]`, `C_k = (ω_k/2^k) 8^k` for `ℋ^k = hausdorffN n k` (EG uses closed balls and
  factor 5).
* (b): constant `1` for `μH[k]` (each cover set `C` meeting `A` at `x` lies in `B_r(x)` for all
  `r > diam C`), i.e. `2^k/ω_k` for `ℋ^k`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ═══════════════════════════════════════════════════════════════════════════════════════════
### Covering comparisons between `μ` and `ℋ^k` (EG Lemma 5.4 and its proof)

(a) and (b) for general `μ`, `k`; then (c), the corollary for `B ⊆ ∂*E` (uses EG Lemma 5.3 (iii)).
═══════════════════════════════════════════════════════════════════════════════════════════ -/

section CoveringComparison

/-! #### (b) Upper density bound: `μ ≤ t μH[k]` -/

/-- One covering set: if `C` contains `x`, `ediam C < r₀` and `μ(B_r(x)) ≤ t r^k` for all
`0 < r < r₀`, then `μ(C) ≤ t (ediam C)^k` (let `r ↓ diam C`). -/
private theorem measure_le_of_forall_ball_le {k : ℕ} {μ : Measure (Rn n)} {C : Set (Rn n)}
    {t : ℝ≥0} {r₀ : ℝ} {x : Rn n} (hxC : x ∈ C)
    (hx : ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ t * ENNReal.ofReal (r ^ k))
    (hC : ediam C < ENNReal.ofReal r₀) :
    μ C ≤ t * ediam C ^ (k : ℝ) := by
  have hne : ediam C ≠ ∞ := hC.ne_top
  set d := diam C with hd
  have hd0 : 0 ≤ d := diam_nonneg
  have hdr₀ : d < r₀ := by
    rw [hd, diam, ← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hne]
    exact hC
  have hbdd : Bornology.IsBounded C := isBounded_iff_ediam_ne_top.2 hne
  have hbound : ∀ r, d < r → r < r₀ → μ C ≤ t * ENNReal.ofReal (r ^ k) := by
    intro r hdr hrr₀
    refine le_trans (measure_mono fun y hy => ?_) (hx r (hd0.trans_lt hdr) hrr₀)
    exact mem_ball.2 ((dist_le_diam_of_mem hbdd hy hxC).trans_lt hdr)
  have hlim : Tendsto (fun r : ℝ => (t : ℝ≥0∞) * ENNReal.ofReal (r ^ k)) (𝓝[>] d)
      (𝓝 ((t : ℝ≥0∞) * ENNReal.ofReal (d ^ k))) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.coe_ne_top)
    exact ((ENNReal.continuous_ofReal.comp (continuous_pow k)).tendsto d).mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ r in 𝓝[>] d, μ C ≤ t * ENNReal.ofReal (r ^ k) := by
    filter_upwards [Ioo_mem_nhdsGT hdr₀] with r hr using hbound r hr.1 hr.2
  have := ge_of_tendsto hlim hev
  rw [ENNReal.ofReal_pow hd0, hd, diam, ENNReal.ofReal_toReal hne] at this
  rwa [ENNReal.rpow_natCast]

/-- **(b), unnormalized.** If `μ(B_r(x)) ≤ t r^k` for every `x ∈ A` and every `0 < r < r₀`, then
`μ(A) ≤ t μH[k](A)`. -/
theorem measure_le_mul_hausdorffMeasure_of_forall_ball_le {k : ℕ} {μ : Measure (Rn n)}
    {A : Set (Rn n)} {t : ℝ≥0} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ x ∈ A, ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ t * ENNReal.ofReal (r ^ k)) :
    μ A ≤ t * μH[(k : ℝ)] A := by
  rcases eq_or_ne t 0 with rfl | ht0
  · -- `t = 0`: `A` is covered by countably many `μ`-null balls (Lindelöf).
    rw [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero]
    obtain ⟨T, hTA, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable A
      (fun x => ball x (r₀ / 2)) fun _ _ => isOpen_ball
    refine measure_mono_null (t := ⋃ x ∈ T, ball x (r₀ / 2)) (fun y hy => ?_)
      ((measure_biUnion_null_iff (s := fun x => ball x (r₀ / 2)) hTc).2 fun x hx => ?_)
    · rw [hTU]
      exact mem_biUnion hy (mem_ball_self (half_pos hr₀))
    · have := h x (hTA hx) (r₀ / 2) (half_pos hr₀) (half_lt_self hr₀)
      rwa [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at this
  · set R : ℝ≥0∞ := ENNReal.ofReal (r₀ / 2) with hR
    have hR0 : 0 < R := ENNReal.ofReal_pos.2 (half_pos hr₀)
    have hRr₀ : R < ENNReal.ofReal r₀ :=
      (ENNReal.ofReal_lt_ofReal_iff hr₀).2 (half_lt_self hr₀)
    have hcover : μ A / t ≤
        ⨅ (T : ℕ → Set (Rn n)) (_ : A ⊆ ⋃ i, T i) (_ : ∀ i, ediam (T i) ≤ R),
          ∑' i, ⨆ _ : (T i).Nonempty, ediam (T i) ^ (k : ℝ) := by
      refine le_iInf₂ fun T hAT => le_iInf fun hTR => ?_
      refine ENNReal.div_le_of_le_mul' ?_
      calc μ A ≤ μ (⋃ i, A ∩ T i) := by
            rw [← inter_iUnion]; exact measure_mono (subset_inter subset_rfl hAT)
        _ ≤ ∑' i, μ (A ∩ T i) := measure_iUnion_le _
        _ ≤ ∑' i, (t : ℝ≥0∞) * ⨆ _ : (T i).Nonempty, ediam (T i) ^ (k : ℝ) := by
            refine ENNReal.tsum_le_tsum fun i => ?_
            rcases (A ∩ T i).eq_empty_or_nonempty with he | ⟨x, hxA, hxT⟩
            · rw [he, measure_empty]; exact zero_le
            · rw [iSup_pos ⟨x, hxT⟩]
              exact (measure_mono inter_subset_right).trans
                (measure_le_of_forall_ball_le hxT (h x hxA) ((hTR i).trans_lt hRr₀))
        _ = (t : ℝ≥0∞) * ∑' i, ⨆ _ : (T i).Nonempty, ediam (T i) ^ (k : ℝ) :=
            ENNReal.tsum_mul_left
    have hle : μ A / t ≤ μH[(k : ℝ)] A := by
      refine hcover.trans ?_
      rw [Measure.hausdorffMeasure_apply]
      exact le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
        ⨅ (T : ℕ → Set (Rn n)) (_ : A ⊆ ⋃ i, T i) (_ : ∀ i, ediam (T i) ≤ r),
          ∑' i, ⨆ _ : (T i).Nonempty, ediam (T i) ^ (k : ℝ)) R hR0
    rwa [ENNReal.div_le_iff (ENNReal.coe_ne_zero.2 ht0) ENNReal.coe_ne_top, mul_comm] at hle

/-- **(b)**. If `μ(B_r(x)) ≤ t r^k` for every `x ∈ A` and every `0 < r < r₀`,
then `μ(A) ≤ (2^k/ω_k) · t · ℋ^k(A)`, where `ℋ^k = hausdorffN n k = (ω_k/2^k) μH[k]`. -/
theorem measure_le_mul_hausdorffN_of_forall_ball_le {k : ℕ} {μ : Measure (Rn n)}
    {A : Set (Rn n)} {t : ℝ≥0} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ x ∈ A, ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ t * ENNReal.ofReal (r ^ k)) :
    μ A ≤ (ENNReal.ofReal (unitBallVolume k / 2 ^ k))⁻¹ * t * hausdorffN n k A := by
  set c := ENNReal.ofReal (unitBallVolume k / 2 ^ k)
  have hc0 : c ≠ 0 := (GMT.hausdorffN_const_pos k).ne'
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  refine (measure_le_mul_hausdorffMeasure_of_forall_ball_le hr₀ h).trans (le_of_eq ?_)
  rw [GMT.hausdorffN_apply, mul_comm c⁻¹, mul_assoc, ← mul_assoc c⁻¹,
    ENNReal.inv_mul_cancel hc0 hctop, one_mul]

/-! #### (a) Lower density bound: `t ℋ^k ≤ C μ` -/

/-- **(a), unnormalized** (EG Lemma 5.4, proof). If for every `x ∈ A` there are arbitrarily small
`r > 0` with `t r^k < μ(B_r(x))`, then `t μH[k](A) ≤ 8^k μ(U)` for every open `U ⊇ A`.
Vitali's covering lemma with enlargement factor `4` (Mathlib's open-ball version needs `τ > 3`). -/
theorem mul_hausdorffMeasure_le_of_frequently {k : ℕ} {μ : Measure (Rn n)} {A U : Set (Rn n)}
    (hU : IsOpen U) (hAU : A ⊆ U) {t : ℝ≥0∞}
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0, t * ENNReal.ofReal (r ^ k) < μ (ball x r)) :
    t * μH[(k : ℝ)] A ≤ 8 ^ k * μ U := by
  rw [Measure.hausdorffMeasure_apply]
  simp only [ENNReal.mul_iSup]
  refine iSup₂_le fun R hR => ?_
  -- A radius bound `ρ > 0` with `8ρ ≤ R`.
  have hmin : min R 1 ≠ ∞ := ((min_le_right _ _).trans_lt ENNReal.one_lt_top).ne
  set ρ : ℝ := (min R 1).toReal / 8 with hρdef
  have hρ : 0 < ρ := div_pos (ENNReal.toReal_pos (lt_min hR one_pos).ne' hmin) (by norm_num)
  have hρR : ENNReal.ofReal (8 * ρ) ≤ R := by
    rw [hρdef, mul_div_cancel₀ _ (by norm_num : (8 : ℝ) ≠ 0), ENNReal.ofReal_toReal hmin]
    exact min_le_left _ _
  -- The Vitali family: balls centered in `A`, inside `U`, of radius `≤ ρ`, with large measure.
  set F : Set (Rn n × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ p.2 ≤ ρ ∧ ball p.1 p.2 ⊆ U ∧
    t * ENNReal.ofReal (p.2 ^ k) < μ (ball p.1 p.2)} with hFdef
  obtain ⟨u, huF, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball F
    (fun p => p.1) (fun p => p.2) ρ (fun p hp => hp.2.2.1) 4 (by norm_num)
  have hu_count : u.Countable := hudisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    fun p hp => nonempty_ball.2 (huF hp).2.1
  -- The enlarged balls cover `A`.
  have hAcov : A ⊆ ⋃ p : u, ball (p : Rn n × ℝ).1 (4 * (p : Rn n × ℝ).2) := by
    intro x hx
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x (hAU hx)
    obtain ⟨r, hr, hrI⟩ :=
      ((h x hx).and_eventually (Ioo_mem_nhdsGT (lt_min hρ hε))).exists
    have hp : (x, r) ∈ F := ⟨hx, hrI.1, (hrI.2.trans_le (min_le_left _ _)).le,
      (ball_subset_ball (hrI.2.trans_le (min_le_right _ _)).le).trans hεU, hr⟩
    obtain ⟨b, hbu, hsub⟩ := hucov (x, r) hp
    exact mem_iUnion.2 ⟨⟨b, hbu⟩, hsub (mem_ball_self hrI.1)⟩
  have : Encodable u := hu_count.toEncodable
  set T : ℕ → Set (Rn n) := fun i =>
    ⋃ p ∈ Encodable.decode₂ u i, ball (p : Rn n × ℝ).1 (4 * (p : Rn n × ℝ).2) with hTdef
  have hTcov : A ⊆ ⋃ i, T i := by
    simp only [hTdef]
    rw [Encodable.iUnion_decode₂]
    exact hAcov
  have hdiam : ∀ p : u, ediam (ball (p : Rn n × ℝ).1 (4 * (p : Rn n × ℝ).2)) ≤
      ENNReal.ofReal (8 * (p : Rn n × ℝ).2) := fun p =>
    ediam_le_of_forall_dist_le fun y hy z hz => by
      have := dist_triangle_right y z (p : Rn n × ℝ).1
      rw [mem_ball] at hy hz
      linarith
  have hTR : ∀ i, ediam (T i) ≤ R := fun i =>
    Encodable.iUnion_decode₂_cases (C := fun S => ediam S ≤ R) (by simp) fun p =>
      (hdiam p).trans ((ENNReal.ofReal_le_ofReal (by linarith [(huF p.2).2.2.1])).trans hρR)
  calc t * ⨅ (T : ℕ → Set (Rn n)) (_ : A ⊆ ⋃ i, T i) (_ : ∀ i, ediam (T i) ≤ R),
          ∑' i, ⨆ _ : (T i).Nonempty, ediam (T i) ^ (k : ℝ)
        ≤ t * ∑' i, ⨆ _ : (T i).Nonempty, ediam (T i) ^ (k : ℝ) := by
          gcongr
          exact (iInf₂_le T hTcov).trans (iInf_le _ hTR)
      _ = t * ∑' p : u, ⨆ _ : (ball (p : Rn n × ℝ).1 (4 * (p : Rn n × ℝ).2)).Nonempty,
            ediam (ball (p : Rn n × ℝ).1 (4 * (p : Rn n × ℝ).2)) ^ (k : ℝ) := by
          simp only [hTdef]
          rw [tsum_iUnion_decode₂ (fun S => ⨆ _ : S.Nonempty, ediam S ^ (k : ℝ)) (by simp)]
      _ ≤ ∑' p : u, 8 ^ k * μ (ball (p : Rn n × ℝ).1 (p : Rn n × ℝ).2) := by
          rw [← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun p => ?_
          have hp := huF p.2
          calc t * ⨆ _ : (ball (p : Rn n × ℝ).1 (4 * (p : Rn n × ℝ).2)).Nonempty,
                ediam (ball (p : Rn n × ℝ).1 (4 * (p : Rn n × ℝ).2)) ^ (k : ℝ)
              ≤ t * ENNReal.ofReal (8 * (p : Rn n × ℝ).2) ^ (k : ℝ) := by
                gcongr
                exact iSup_le fun _ => ENNReal.rpow_le_rpow (hdiam p) (Nat.cast_nonneg k)
            _ = 8 ^ k * (t * ENNReal.ofReal ((p : Rn n × ℝ).2 ^ k)) := by
                rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by linarith [hp.2.1]), mul_pow,
                  ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
                norm_num
                ring
            _ ≤ 8 ^ k * μ (ball (p : Rn n × ℝ).1 (p : Rn n × ℝ).2) := by
                gcongr
                exact hp.2.2.2.2.le
      _ = 8 ^ k * μ (⋃ p : u, ball (p : Rn n × ℝ).1 (p : Rn n × ℝ).2) := by
          rw [ENNReal.tsum_mul_left,
            measure_iUnion (hudisj.subtype _ _) fun _ => measurableSet_ball]
      _ ≤ 8 ^ k * μ U := by
          gcongr
          exact iUnion_subset fun p => (huF p.2).2.2.2.1

/-- **(a)** (frequent form). If for every `x ∈ A` there are arbitrarily small
`r > 0` with `t r^k < μ(B_r(x))`, then `t ℋ^k(A) ≤ (ω_k/2^k) 8^k μ(U)` for every open `U ⊇ A`. -/
theorem mul_hausdorffN_le_of_frequently {k : ℕ} {μ : Measure (Rn n)} {A U : Set (Rn n)}
    (hU : IsOpen U) (hAU : A ⊆ U) {t : ℝ≥0∞}
    (h : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0, t * ENNReal.ofReal (r ^ k) < μ (ball x r)) :
    t * hausdorffN n k A ≤ ENNReal.ofReal (unitBallVolume k / 2 ^ k) * 8 ^ k * μ U := by
  set c := ENNReal.ofReal (unitBallVolume k / 2 ^ k)
  calc t * hausdorffN n k A = c * (t * μH[(k : ℝ)] A) := by rw [GMT.hausdorffN_apply]; ring
    _ ≤ c * (8 ^ k * μ U) := by
        gcongr c * ?_
        exact mul_hausdorffMeasure_le_of_frequently hU hAU h
    _ = c * 8 ^ k * μ U := by ring

/-- **(a)** (EG Lemma 5.4 form). If `limsup_{r→0} μ(B_r(x))/r^k ≥ t` at every
`x ∈ A`, then `t ℋ^k(A) ≤ (ω_k/2^k) 8^k μ(U)` for every open `U ⊇ A`. -/
theorem mul_hausdorffN_le_of_le_limsup {k : ℕ} {μ : Measure (Rn n)} {A U : Set (Rn n)}
    (hU : IsOpen U) (hAU : A ⊆ U) {t : ℝ≥0}
    (h : ∀ x ∈ A, (t : ℝ≥0∞) ≤ limsup (fun r => μ (ball x r) / ENNReal.ofReal (r ^ k)) (𝓝[>] 0)) :
    (t : ℝ≥0∞) * hausdorffN n k A ≤ ENNReal.ofReal (unitBallVolume k / 2 ^ k) * 8 ^ k * μ U := by
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  -- Apply the frequent form with `t a` for every `a < 1`.
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  have hat : (t : ℝ≥0∞) * a < t := by
    simpa using ENNReal.mul_lt_mul_right (ENNReal.coe_ne_zero.2 ht0) ENNReal.coe_ne_top ha
  have hfreq : ∀ x ∈ A, ∃ᶠ r in 𝓝[>] 0, (t * a) * ENNReal.ofReal (r ^ k) < μ (ball x r) := by
    intro x hx
    refine (frequently_lt_of_lt_limsup (by isBoundedDefault) (hat.trans_le (h x hx))).mp ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r) hlt
    rwa [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 (pow_pos hr k)).ne')
      (Or.inl ENNReal.ofReal_ne_top)] at hlt
  calc a * ((t : ℝ≥0∞) * hausdorffN n k A) = (t * a) * hausdorffN n k A := by ring
    _ ≤ _ := mul_hausdorffN_le_of_frequently hU hAU hfreq

/-- **Outer approximation of null sets inside `Ω`.** If `μ` is finite on compact subsets of the
open set `Ω`, and `A ⊆ Ω` is `μ`-null, then for every `ε ≠ 0` there is an open `U` with
`A ⊆ U ⊆ Ω` and `μ(U) ≤ ε`. (A Gauss–Green measure need not be outer regular on `ℝⁿ`.) -/
theorem exists_isOpen_subset_measure_le {μ : Measure (Rn n)} {Ω A : Set (Rn n)} (hΩ : IsOpen Ω)
    (hμ : ∀ K, IsCompact K → K ⊆ Ω → μ K < ∞) (hAΩ : A ⊆ Ω) (hA : μ A = 0) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ U, IsOpen U ∧ A ⊆ U ∧ U ⊆ Ω ∧ μ U ≤ ε := by
  -- Countably many balls, compactly contained in `Ω`, cover `Ω`.
  have hball : ∀ z : Ω, ∃ ρ > 0, closedBall (z : Rn n) ρ ⊆ Ω := fun z => by
    obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩ z z.2
    exact ⟨ρ / 2, half_pos hρ, (closedBall_subset_ball (half_lt_self hρ)).trans hρΩ⟩
  choose ρ hρ hρΩ using hball
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : Ω => ball (z : Rn n) (ρ z)) fun z => isOpen_ball
  have : Countable T := hTc.to_subtype
  have hcover : Ω ⊆ ⋃ z : T, ball ((z : Ω) : Rn n) (ρ z) := by
    intro x hx
    have : x ∈ ⋃ z : Ω, ball (z : Rn n) (ρ z) := mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hρ _)⟩
    rw [← hTU] at this
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 this
    exact mem_iUnion.2 ⟨⟨z, hz⟩, hxz⟩
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.exists_pos_sum_of_countable hε T
  -- On each ball, `μ⌊V` is finite, hence outer regular.
  have hW : ∀ z : T, ∃ W, IsOpen W ∧ A ⊆ W ∧
      μ (W ∩ ball ((z : Ω) : Rn n) (ρ z)) < δ z := fun z => by
    set V := ball ((z : Ω) : Rn n) (ρ z)
    have hVfin : μ V ≠ ∞ := ne_top_of_le_ne_top
      (hμ _ (isCompact_closedBall _ _) (hρΩ z)).ne (measure_mono ball_subset_closedBall)
    have : IsFiniteMeasure (μ.restrict V) := isFiniteMeasure_restrict.2 hVfin
    have hA0 : μ.restrict V A < δ z := by
      rw [Measure.restrict_apply' measurableSet_ball, measure_mono_null inter_subset_left hA]
      exact ENNReal.coe_pos.2 (hδ0 z)
    obtain ⟨W, hAW, hWo, hWμ⟩ := A.exists_isOpen_lt_of_lt _ hA0
    refine ⟨W, hWo, hAW, ?_⟩
    rwa [Measure.restrict_apply hWo.measurableSet] at hWμ
  choose W hWo hAW hWμ using hW
  refine ⟨⋃ z : T, W z ∩ ball ((z : Ω) : Rn n) (ρ z),
    isOpen_iUnion fun z => (hWo z).inter isOpen_ball, fun x hx => ?_,
    iUnion_subset fun z => inter_subset_right.trans (ball_subset_closedBall.trans (hρΩ z)), ?_⟩
  · obtain ⟨z, hxz⟩ := mem_iUnion.1 (hcover (hAΩ hx))
    exact mem_iUnion.2 ⟨z, hAW z hx, hxz⟩
  · calc μ (⋃ z : T, W z ∩ ball ((z : Ω) : Rn n) (ρ z))
        ≤ ∑' z : T, μ (W z ∩ ball ((z : Ω) : Rn n) (ρ z)) := measure_iUnion_le _
      _ ≤ ∑' z : T, (δ z : ℝ≥0∞) := ENNReal.tsum_le_tsum fun z => (hWμ z).le
      _ ≤ ε := hδ.le

/-- **(a), null case** (EG Lemma 5.5 (ii) and Thm 5.15 use
it). Let `μ` be finite on compact subsets of the open set `Ω` (e.g. a Gauss–Green measure). If
`A ⊆ Ω`, `μ(A) = 0` and `limsup_{r→0} μ(B_r(x))/r^k > 0` at every `x ∈ A`, then `ℋ^k(A) = 0`. -/
theorem hausdorffN_eq_zero_of_measure_eq_zero {k : ℕ} {μ : Measure (Rn n)} {Ω A : Set (Rn n)}
    (hΩ : IsOpen Ω) (hμ : ∀ K, IsCompact K → K ⊆ Ω → μ K < ∞) (hAΩ : A ⊆ Ω) (hA : μ A = 0)
    (h : ∀ x ∈ A, 0 < limsup (fun r => μ (ball x r) / ENNReal.ofReal (r ^ k)) (𝓝[>] 0)) :
    hausdorffN n k A = 0 := by
  rw [GMT.hausdorffN_eq_zero_iff]
  -- Split `A` according to a lower bound `(j+1)⁻¹` on the upper density.
  set Aj : ℕ → Set (Rn n) := fun j => {x ∈ A | ((j : ℝ≥0∞) + 1)⁻¹ <
    limsup (fun r => μ (ball x r) / ENNReal.ofReal (r ^ k)) (𝓝[>] 0)}
  have hAU : A ⊆ ⋃ j, Aj j := by
    intro x hx
    obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt (h x hx).ne'
    refine mem_iUnion.2 ⟨j, hx, lt_of_le_of_lt ?_ hj⟩
    exact ENNReal.inv_le_inv.2 le_self_add
  refine measure_mono_null hAU (measure_iUnion_null fun j => ?_)
  set t : ℝ≥0∞ := ((j : ℝ≥0∞) + 1)⁻¹
  have ht0 : t ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
  have hfreq : ∀ x ∈ Aj j, ∃ᶠ r in 𝓝[>] 0, t * ENNReal.ofReal (r ^ k) < μ (ball x r) := by
    intro x hx
    refine (frequently_lt_of_lt_limsup (by isBoundedDefault) hx.2).mp ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r) hlt
    rwa [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 (pow_pos hr k)).ne')
      (Or.inl ENNReal.ofReal_ne_top)] at hlt
  -- `t μH(A_j) ≤ 8^k ε` for every `ε > 0`.
  have hbound : ∀ m : ℕ, t * μH[(k : ℝ)] (Aj j) ≤ 8 ^ k * (m : ℝ≥0∞)⁻¹ := by
    intro m
    obtain ⟨U, hUo, hAjU, -, hUμ⟩ := exists_isOpen_subset_measure_le hΩ hμ hAΩ hA
      (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
    have hAjA : Aj j ⊆ A := fun x hx => hx.1
    exact (mul_hausdorffMeasure_le_of_frequently hUo (hAjA.trans hAjU) hfreq).trans
      (by gcongr)
  have hlim : Tendsto (fun m : ℕ => (8 : ℝ≥0∞) ^ k * (m : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) : (0 : ℝ≥0∞) ≠ 0 ∨ (8 : ℝ≥0∞) ^ k ≠ ∞)
    rwa [mul_zero] at this
  have h0 : t * μH[(k : ℝ)] (Aj j) = 0 :=
    nonpos_iff_eq_zero.1 (ge_of_tendsto' hlim hbound)
  exact (mul_eq_zero.1 h0).resolve_left ht0

/-- **(a), quantitative** (EG Lemma 5.4 proof). If
`limsup_{r→0} μ(B_r(x))/r^k ≥ t > 0` at every `x ∈ A`, then
`ℋ^k(A) ≤ (C_k / t) μ(U)` for every open `U ⊇ A`, with `C_k = (ω_k/2^k) 8^k`. -/
theorem hausdorffN_le_mul_measure_of_le_limsup {k : ℕ} {μ : Measure (Rn n)} {A U : Set (Rn n)}
    (hU : IsOpen U) (hAU : A ⊆ U) {t : ℝ} (ht : 0 < t)
    (h : ∀ x ∈ A, ENNReal.ofReal t ≤
      limsup (fun r => μ (ball x r) / ENNReal.ofReal (r ^ k)) (𝓝[>] 0)) :
    hausdorffN n k A ≤ ENNReal.ofReal (unitBallVolume k / 2 ^ k * 8 ^ k / t) * μ U := by
  have key := mul_hausdorffN_le_of_le_limsup hU hAU (t := t.toNNReal) h
  change ENNReal.ofReal t * hausdorffN n k A ≤ _ at key
  have ht0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
  have hc : 0 ≤ unitBallVolume k / 2 ^ k := div_nonneg ENNReal.toReal_nonneg (by positivity)
  calc hausdorffN n k A = (ENNReal.ofReal t)⁻¹ * (ENNReal.ofReal t * hausdorffN n k A) :=
        (ENNReal.inv_mul_cancel_left ht0 ENNReal.ofReal_ne_top).symm
    _ ≤ (ENNReal.ofReal t)⁻¹ * (ENNReal.ofReal (unitBallVolume k / 2 ^ k) * 8 ^ k * μ U) := by
        gcongr
    _ = ENNReal.ofReal (unitBallVolume k / 2 ^ k * 8 ^ k / t) * μ U := by
        rw [ENNReal.ofReal_div_of_pos ht, ENNReal.ofReal_mul hc, ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, ENNReal.div_eq_inv_mul]
        ring

/-- **Outer approximation inside `Ω`.** If `μ` is finite on compact subsets of the open set `Ω`
and `A ⊆ Ω`, then for every `ε ≠ 0` there is an open `U` with `A ⊆ U ⊆ Ω` and
`μ(U) ≤ μ(A) + ε`. (A Gauss–Green measure need not be locally finite on `ℝⁿ`; its restriction
to the subspace `Ω` is, hence outer regular.) -/
theorem exists_isOpen_subset_measure_le_add {μ : Measure (Rn n)} {Ω A : Set (Rn n)}
    (hΩ : IsOpen Ω) (hμ : ∀ K, IsCompact K → K ⊆ Ω → μ K < ∞) (hAΩ : A ⊆ Ω) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) : ∃ U, IsOpen U ∧ A ⊆ U ∧ U ⊆ Ω ∧ μ U ≤ μ A + ε := by
  rcases eq_top_or_lt_top (μ A) with hA | hA
  · exact ⟨Ω, hΩ, hAΩ, subset_rfl, by simp [hA]⟩
  have hemb : MeasurableEmbedding (Subtype.val : Ω → Rn n) :=
    MeasurableEmbedding.subtype_coe hΩ.measurableSet
  set μΩ : Measure Ω := μ.comap Subtype.val
  have : IsLocallyFiniteMeasure μΩ := by
    refine ⟨fun z => ?_⟩
    obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩ z z.2
    refine ⟨Subtype.val ⁻¹' closedBall (z : Rn n) (ρ / 2),
      continuous_subtype_val.continuousAt.preimage_mem_nhds
        (closedBall_mem_nhds _ (half_pos hρ)), ?_⟩
    rw [hemb.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe]
    exact (measure_mono inter_subset_left).trans_lt (hμ _ (isCompact_closedBall _ _)
      ((closedBall_subset_ball (half_lt_self hρ)).trans hρΩ))
  have hlt : μΩ (Subtype.val ⁻¹' A) < μ A + ε := by
    rw [hemb.comap_apply, image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.2 hAΩ]
    exact ENNReal.lt_add_right hA.ne hε
  obtain ⟨V, hAV, hVo, hVμ⟩ := (Subtype.val ⁻¹' A).exists_isOpen_lt_of_lt _ hlt
  refine ⟨Subtype.val '' V, hΩ.isOpenMap_subtype_val V hVo,
    fun y hy => ⟨⟨y, hAΩ hy⟩, hAV hy, rfl⟩, image_subset_iff.2 fun y _ => y.2, ?_⟩
  rw [← hemb.comap_apply]
  exact hVμ.le

/-- The constant `C_n = (ω_{n-1}/2^{n-1}) 8^{n-1} / A₃` of EG Lemma 5.4
(`ℋ^{n-1}(B) ≤ C_n μ(B)` for `B ⊆ ∂*E`). -/
noncomputable def reducedBoundaryHausdorffConst (n : ℕ) : ℝ :=
  unitBallVolume (n - 1) / 2 ^ (n - 1) * 8 ^ (n - 1) / densityConstA₃ n

/-- **(c), EG Lemma 5.4**. For a Gauss–Green pair `(μ, ν)` of a measurable `E`
in the open set `Ω` and any `B ⊆ ∂*E = reducedBoundary Ω E` (no measurability of `B`),
`ℋ^{n-1}(B) ≤ C_n μ(B)`, `C_n = reducedBoundaryHausdorffConst n`.

Proof (EG): by Lemma 5.3 (iii) the upper density `limsup μ(B_r(x))/r^{n-1}` is `≥ A₃` on `B`;
(a) gives `ℋ^{n-1}(B) ≤ (C/A₃) μ(U)` for open `U ⊇ B`, and `U ⊆ Ω` can be chosen with
`μ(U) ≤ μ(B) + ε` (`exists_isOpen_subset_measure_le_add`). -/
theorem IsGaussGreenPair.hausdorffN_le_mul_measure (hn : 2 ≤ n) {Ω E : Set (Rn n)}
    {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) {B : Set (Rn n)}
    (hB : B ⊆ reducedBoundary Ω E) :
    hausdorffN n (n - 1) B ≤ ENNReal.ofReal (reducedBoundaryHausdorffConst n) * μ B := by
  have hA3 := densityConstA₃_pos (by omega : 1 ≤ n)
  have hlim : ∀ y ∈ B, ENNReal.ofReal (densityConstA₃ n) ≤
      limsup (fun r => μ (ball y r) / ENNReal.ofReal (r ^ (n - 1))) (𝓝[>] 0) := by
    intro y hy
    obtain ⟨r₀, hr₀, hbound⟩ :=
      h.exists_forall_measure_ball_ge_of_mem_reducedBoundary hn hΩ hE (hB hy)
    refine le_limsup_of_frequently_le (Eventually.frequently ?_) (by isBoundedDefault)
    filter_upwards [Ioo_mem_nhdsGT hr₀] with r hr
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 (pow_pos hr.1 _)).ne')
      (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul hA3.le]
    exact hbound r hr.1 hr.2
  set C := ENNReal.ofReal (reducedBoundaryHausdorffConst n)
  have hbd : ∀ m : ℕ, hausdorffN n (n - 1) B ≤ C * (μ B + (m : ℝ≥0∞)⁻¹) := fun m => by
    obtain ⟨U, hUo, hBU, -, hUμ⟩ := exists_isOpen_subset_measure_le_add hΩ h.lt_top_of_isCompact
      (hB.trans fun y hy => hy.1) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top m))
    exact (hausdorffN_le_mul_measure_of_le_limsup hUo hBU hA3 hlim).trans
      (mul_le_mul' (le_of_eq rfl) hUμ)
  have hlim' : Tendsto (fun m : ℕ => C * (μ B + (m : ℝ≥0∞)⁻¹)) atTop (𝓝 (C * (μ B + 0))) :=
    ENNReal.Tendsto.const_mul (tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero)
      (Or.inr ENNReal.ofReal_ne_top)
  rw [add_zero] at hlim'
  exact ge_of_tendsto' hlim' hbd

end CoveringComparison

end GMTFoundations
