/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.GMT.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Flat pieces and their blow-ups

A set `G ⊆ ℝⁿ` is an `ε`-flat piece with unit normal `ν` if `|⟪y - z, ν⟫| ≤ ε ‖y - z‖` for all
`y, z ∈ G`: every chord of `G` makes an angle at most `≈ ε` with the hyperplane `ν^⊥`. Rectifiable
sets are covered, up to null sets, by countably many flat pieces with arbitrarily small `ε`
(`GMT/Rectifiable.lean`). This file contains the measure theory of a single piece.

* `projH ν`: the orthogonal projection onto `ν^⊥`. On a flat piece it is injective with a
  `(1-ε)⁻¹`-Lipschitz inverse, so `μ⌊π(G) ≤ π_#(μ⌊G) ≤ (1-ε)^{-k} μ⌊π(G)`
  (`le_map_restrict`, `IsFlatPiece.map_restrict_le`).
* `IsFlatPiece.lintegral_le`: the upper blow-up bound, valid at every scale `r > 0`,
  `∫_G φ(r⁻¹(y - x)) ≤ (1-ε)^{-k} r^k (∫_{ν^⊥} φ + ω ℋ^k(ν^⊥ ∩ B̄_{2R}))`.
* `IsFlatPiece.le_lintegral`: the lower blow-up bound,
  `r^k ∫_{ν^⊥} φ ≤ ∫_G φ(r⁻¹(y - x)) + ω (1-ε)^{-k} r^k ℋ^k(ν^⊥ ∩ B̄_{2R})
    + M ℋ^k((ν^⊥ \ π(G)) ∩ B̄_{Rr}(π x))`.

Here `x ∈ G`, `0 ≤ φ ≤ M` vanishes outside `B̄_R`, and `ω` is the oscillation of `φ` at scale
`2εR`. The measure is any `μHE[k]`.

* `IsFlatPiece.measure_inter_closedBall_le`, `IsFlatPiece.le_measure_inter_closedBall`: the same
  comparison for `1_{B̄_r(x)}`, used for the density of rectifiable sets.
* `isFlatPiece_hyperplane`: `ν'^⊥` is a `‖ν - ν'‖`-flat piece with normal `ν`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace GMTFoundations.GMT

variable {n : ℕ}

/-- `G` is an `ε`-flat piece with normal `ν`: `|⟪y - z, ν⟫| ≤ ε ‖y - z‖` for `y, z ∈ G`. -/
def IsFlatPiece (ν : Rn n) (ε : ℝ) (G : Set (Rn n)) : Prop :=
  ∀ y ∈ G, ∀ z ∈ G, |⟪y - z, ν⟫| ≤ ε * ‖y - z‖

theorem IsFlatPiece.mono {ν : Rn n} {ε : ℝ} {G G' : Set (Rn n)} (h : IsFlatPiece ν ε G)
    (hG' : G' ⊆ G) : IsFlatPiece ν ε G' :=
  fun y hy z hz => h y (hG' hy) z (hG' hz)

/-! ### The projection onto `ν^⊥` (continued) -/

theorem continuous_projH (ν : Rn n) : Continuous (projH ν) :=
  continuous_id.sub (by fun_prop : Continuous fun y : Rn n => ⟪y, ν⟫ • ν)

theorem measurable_projH (ν : Rn n) : Measurable (projH ν) :=
  (continuous_projH ν).measurable

theorem lipschitzWith_projH {ν : Rn n} (hν : ‖ν‖ = 1) : LipschitzWith 1 (projH ν) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm, dist_eq_norm, ← projH_sub, NNReal.coe_one, one_mul]
  exact norm_projH_le hν _

/-- On a flat piece the projection is `(1-ε)`-co-Lipschitz. -/
theorem IsFlatPiece.norm_projH_sub_ge {ν : Rn n} {ε : ℝ} {G : Set (Rn n)}
    (h : IsFlatPiece ν ε G) (hν : ‖ν‖ = 1) {y z : Rn n} (hy : y ∈ G) (hz : z ∈ G) :
    (1 - ε) * ‖y - z‖ ≤ ‖projH ν y - projH ν z‖ := by
  rw [← projH_sub]
  have h1 := norm_sub_projH hν (y - z)
  have h2 := norm_sub_norm_le (y - z) (projH ν (y - z))
  have h3 := h y hy z hz
  linarith

theorem IsFlatPiece.injOn_projH {ν : Rn n} {ε : ℝ} {G : Set (Rn n)} (h : IsFlatPiece ν ε G)
    (hν : ‖ν‖ = 1) (hε : ε < 1) : InjOn (projH ν) G := by
  intro y hy z hz hyz
  have := h.norm_projH_sub_ge hν hy hz
  rw [hyz, sub_self, norm_zero] at this
  have h0 : ‖y - z‖ ≤ 0 := by
    by_contra h'
    push Not at h'
    linarith [mul_pos (sub_pos.2 hε) h']
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-! ### Measure comparison -/

section Measure

variable (k : ℕ)

/-- The constant `(1-ε)⁻¹` as an extended real. -/
def flatConst (ε : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1 - ε)⁻¹

theorem flatConst_ne_top (ε : ℝ) : flatConst ε ≠ ∞ := ENNReal.ofReal_ne_top

theorem measure_image_projH_le {ν : Rn n} (hν : ‖ν‖ = 1) (A : Set (Rn n)) :
    (μHE[k] : Measure (Rn n)) (projH ν '' A) ≤ μHE[k] A := by
  have := ((lipschitzWith_projH hν).lipschitzOnWith (s := A)).euclideanHausdorffMeasure_image_le k
  simpa using this

theorem IsFlatPiece.measure_le {ν : Rn n} {ε : ℝ} {G : Set (Rn n)} (h : IsFlatPiece ν ε G)
    (hν : ‖ν‖ = 1) (hε : ε < 1) {A : Set (Rn n)} (hA : A ⊆ G) :
    (μHE[k] : Measure (Rn n)) A ≤ flatConst ε ^ k * μHE[k] (projH ν '' A) := by
  have hinj : InjOn (projH ν) A := (h.injOn_projH hν hε).mono hA
  set g := Function.invFunOn (projH ν) A
  have hg : LeftInvOn g (projH ν) A := hinj.leftInvOn_invFunOn
  have hlip : LipschitzOnWith (Real.toNNReal (1 - ε)⁻¹) g (projH ν '' A) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    obtain ⟨y, hy, rfl⟩ := hp
    obtain ⟨z, hz, rfl⟩ := hq
    rw [hg hy, hg hz, dist_eq_norm, dist_eq_norm,
      Real.coe_toNNReal _ (inv_nonneg.2 (sub_nonneg.2 hε.le))]
    have := h.norm_projH_sub_ge hν (hA hy) (hA hz)
    rw [← div_eq_inv_mul, le_div_iff₀ (sub_pos.2 hε), mul_comm]
    exact this
  have := hlip.euclideanHausdorffMeasure_image_le k
  rwa [hg.image_image] at this

theorem IsFlatPiece.map_restrict_le {ν : Rn n} {ε : ℝ} {G : Set (Rn n)} (h : IsFlatPiece ν ε G)
    (hν : ‖ν‖ = 1) (hε : ε < 1) :
    ((μHE[k] : Measure (Rn n)).restrict G).map (projH ν) ≤
      flatConst ε ^ k • (μHE[k] : Measure (Rn n)).restrict (projH ν '' G) := by
  refine Measure.le_iff.2 fun B hB => ?_
  rw [Measure.map_apply (measurable_projH ν) hB, Measure.restrict_apply (measurable_projH ν hB),
    Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul, ← image_preimage_inter]
  exact h.measure_le k hν hε inter_subset_right

theorem le_map_restrict {ν : Rn n} (hν : ‖ν‖ = 1) (G : Set (Rn n)) :
    (μHE[k] : Measure (Rn n)).restrict (projH ν '' G) ≤
      ((μHE[k] : Measure (Rn n)).restrict G).map (projH ν) := by
  refine Measure.le_iff.2 fun B hB => ?_
  rw [Measure.map_apply (measurable_projH ν) hB, Measure.restrict_apply (measurable_projH ν hB),
    Measure.restrict_apply hB, ← image_preimage_inter]
  exact measure_image_projH_le k hν _

theorem IsFlatPiece.lintegral_comp_projH_le {ν : Rn n} {ε : ℝ} {G : Set (Rn n)}
    (h : IsFlatPiece ν ε G) (hν : ‖ν‖ = 1) (hε : ε < 1) {g : Rn n → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y in G, g (projH ν y) ∂μHE[k] ≤ flatConst ε ^ k * ∫⁻ p in projH ν '' G, g p ∂μHE[k] := by
  rw [← lintegral_map hg (measurable_projH ν), ← smul_eq_mul, ← lintegral_smul_measure]
  exact lintegral_mono' (h.map_restrict_le k hν hε) le_rfl

theorem lintegral_le_lintegral_comp_projH {ν : Rn n} (hν : ‖ν‖ = 1) (G : Set (Rn n))
    {g : Rn n → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p in projH ν '' G, g p ∂μHE[k] ≤ ∫⁻ y in G, g (projH ν y) ∂μHE[k] := by
  rw [← lintegral_map hg (measurable_projH ν)]
  exact lintegral_mono' (le_map_restrict k hν G) le_rfl

end Measure

/-! ### Blow-up bounds -/

/-- The pointwise comparison behind the blow-up bounds: if `‖u - v‖ ≤ ε ‖u‖`, `‖v‖ ≤ ‖u‖ ≤ 2 ‖v‖`,
`φ` vanishes outside `B̄_R` and oscillates by at most `ω` at scale `2εR`, then `φ u` and `φ v`
differ by at most `ω`, and both vanish unless `‖v‖ ≤ 2R`. -/
theorem abs_sub_le_of_near {φ : Rn n → ℝ} {R ε ω : ℝ} (hφR : ∀ u, R < ‖u‖ → φ u = 0)
    (hω : ∀ u v, ‖u - v‖ ≤ 2 * ε * R → |φ u - φ v| ≤ ω) (hε : 0 ≤ ε) (hω0 : 0 ≤ ω)
    {u v : Rn n} (huv : ‖u - v‖ ≤ ε * ‖u‖) (hvu : ‖v‖ ≤ ‖u‖) (huv2 : ‖u‖ ≤ 2 * ‖v‖) :
    |φ u - φ v| ≤ ω * (closedBall (0 : Rn n) (2 * R)).indicator 1 v := by
  by_cases hu : ‖u‖ ≤ 2 * R
  · have hv : v ∈ closedBall (0 : Rn n) (2 * R) := by
      rw [mem_closedBall, dist_zero_right]; linarith
    rw [indicator_of_mem hv, Pi.one_apply, mul_one]
    exact hω u v (huv.trans (by linarith [mul_le_mul_of_nonneg_left hu hε]))
  · push Not at hu
    rw [hφR u (by linarith [norm_nonneg v]), hφR v (by linarith), sub_zero, abs_zero]
    exact mul_nonneg hω0 (indicator_nonneg (fun _ _ => zero_le_one) _)

theorem IsFlatPiece.near {ν : Rn n} {ε : ℝ} {G : Set (Rn n)} (h : IsFlatPiece ν ε G)
    (hν : ‖ν‖ = 1) (hε : ε ≤ 1 / 2) {x y : Rn n} (hx : x ∈ G) (hy : y ∈ G) {r : ℝ} (hr : 0 < r) :
    ‖r⁻¹ • (y - x) - r⁻¹ • (projH ν y - projH ν x)‖ ≤ ε * ‖r⁻¹ • (y - x)‖ ∧
      ‖r⁻¹ • (projH ν y - projH ν x)‖ ≤ ‖r⁻¹ • (y - x)‖ ∧
      ‖r⁻¹ • (y - x)‖ ≤ 2 * ‖r⁻¹ • (projH ν y - projH ν x)‖ := by
  have hr' : 0 < r⁻¹ := inv_pos.2 hr
  rw [← smul_sub, norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hr'.le, ← projH_sub,
    norm_sub_projH hν]
  have h1 := h y hy x hx
  have h2 := norm_projH_le hν (y - x)
  have h3 := h.norm_projH_sub_ge hν hy hx
  rw [← projH_sub] at h3
  refine ⟨?_, ?_, ?_⟩
  · calc r⁻¹ * |⟪y - x, ν⟫| ≤ r⁻¹ * (ε * ‖y - x‖) := mul_le_mul_of_nonneg_left h1 hr'.le
      _ = ε * (r⁻¹ * ‖y - x‖) := by ring
  · exact mul_le_mul_of_nonneg_left h2 hr'.le
  · have : ‖y - x‖ ≤ 2 * ‖projH ν (y - x)‖ := by
      linarith [mul_le_mul_of_nonneg_right hε (norm_nonneg (y - x))]
    calc r⁻¹ * ‖y - x‖ ≤ r⁻¹ * (2 * ‖projH ν (y - x)‖) := mul_le_mul_of_nonneg_left this hr'.le
      _ = 2 * (r⁻¹ * ‖projH ν (y - x)‖) := by ring

section BlowUp

variable (k : ℕ) {ν : Rn n} {ε : ℝ} {G : Set (Rn n)} {φ : Rn n → ℝ} {R ω : ℝ}

theorem lintegral_hyperplane_add_indicator {ν : Rn n} (φ : Rn n → ℝ) (hφm : Measurable φ)
    (R ω : ℝ) :
    ∫⁻ p in hyperplane ν, (ENNReal.ofReal (φ p) +
        ENNReal.ofReal ω * (closedBall (0 : Rn n) (2 * R)).indicator 1 p) ∂μHE[k] =
      ∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[k] +
        ENNReal.ofReal ω * μHE[k] (hyperplane ν ∩ closedBall 0 (2 * R)) := by
  rw [lintegral_add_left hφm.ennreal_ofReal, lintegral_const_mul]
  · congr 2
    rw [lintegral_indicator_one measurableSet_closedBall,
      Measure.restrict_apply measurableSet_closedBall, inter_comm]
  · exact (measurable_const.indicator measurableSet_closedBall)

/-- **Upper blow-up bound** on a flat piece, at every scale. -/
theorem IsFlatPiece.lintegral_le (h : IsFlatPiece ν ε G) (hν : ‖ν‖ = 1) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (hGm : MeasurableSet G) {x : Rn n} (hx : x ∈ G) (hφm : Measurable φ)
    (hφR : ∀ u, R < ‖u‖ → φ u = 0)
    (hω : ∀ u v, ‖u - v‖ ≤ 2 * ε * R → |φ u - φ v| ≤ ω) (hω0 : 0 ≤ ω) {r : ℝ} (hr : 0 < r) :
    ∫⁻ y in G, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[k] ≤
      flatConst ε ^ k * (ENNReal.ofReal (r ^ k) *
        (∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[k] +
          ENNReal.ofReal ω * μHE[k] (hyperplane ν ∩ closedBall 0 (2 * R)))) := by
  set Φ : Rn n → ℝ≥0∞ := fun v => ENNReal.ofReal (φ v) +
    ENNReal.ofReal ω * (closedBall (0 : Rn n) (2 * R)).indicator 1 v with hΦ
  have hΦm : Measurable Φ := (ENNReal.measurable_ofReal.comp hφm).add
    (measurable_const.mul (measurable_const.indicator measurableSet_closedBall))
  set g : Rn n → ℝ≥0∞ := fun p => Φ (r⁻¹ • (p - projH ν x)) with hg
  have hgm : Measurable g := hΦm.comp ((measurable_const_smul _).comp (measurable_id.sub_const _))
  have hpt : ∀ y ∈ G, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ≤ g (projH ν y) := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := h.near hν hε hx hy hr
    have := abs_sub_le_of_near hφR hω hε0 hω0 h1 h2 h3
    simp only [hg, hΦ]
    calc ENNReal.ofReal (φ (r⁻¹ • (y - x)))
        ≤ ENNReal.ofReal (φ (r⁻¹ • (projH ν y - projH ν x)) +
            ω * (closedBall (0 : Rn n) (2 * R)).indicator 1 (r⁻¹ • (projH ν y - projH ν x))) :=
          ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 this).2])
      _ ≤ _ := by
          by_cases hm : r⁻¹ • (projH ν y - projH ν x) ∈ closedBall (0 : Rn n) (2 * R)
          · simp only [indicator_of_mem hm, Pi.one_apply, mul_one]
            exact ENNReal.ofReal_add_le
          · simp only [indicator_of_notMem hm, mul_zero, add_zero, le_refl]
  calc ∫⁻ y in G, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[k]
      ≤ ∫⁻ y in G, g (projH ν y) ∂μHE[k] := setLIntegral_mono' hGm hpt
    _ ≤ flatConst ε ^ k * ∫⁻ p in projH ν '' G, g p ∂μHE[k] :=
        h.lintegral_comp_projH_le k hν (by linarith) hgm
    _ ≤ flatConst ε ^ k * ∫⁻ p in hyperplane ν, g p ∂μHE[k] := by
        gcongr
        rintro _ ⟨y, -, rfl⟩
        exact projH_mem_hyperplane hν y
    _ = _ := by
        rw [hg, lintegral_hyperplane_comp_smul_sub k (projH_mem_hyperplane hν x) hr,
          lintegral_hyperplane_add_indicator k φ hφm R ω]

/-- `∫_H 1_{B̄_{2R}}(r⁻¹(p - p₀)) = r^k ℋ^k(H ∩ B̄_{2R})` for `p₀ ∈ H`. -/
theorem lintegral_hyperplane_indicator_comp {ν p₀ : Rn n} (hp₀ : p₀ ∈ hyperplane ν) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    ∫⁻ p in hyperplane ν, (closedBall (0 : Rn n) (2 * R)).indicator 1 (r⁻¹ • (p - p₀)) ∂μHE[k] =
      ENNReal.ofReal (r ^ k) * μHE[k] (hyperplane ν ∩ closedBall 0 (2 * R)) := by
  rw [lintegral_hyperplane_comp_smul_sub k hp₀ hr, lintegral_indicator_one measurableSet_closedBall,
    Measure.restrict_apply measurableSet_closedBall, inter_comm]

/-- **Lower blow-up bound** on a flat piece, at every scale. -/
theorem IsFlatPiece.le_lintegral (h : IsFlatPiece ν ε G) (hν : ‖ν‖ = 1) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 2) (hGm : MeasurableSet G) {x : Rn n} (hx : x ∈ G) (hφm : Measurable φ) {M : ℝ}
    (hφM : ∀ u, φ u ≤ M) (hφR : ∀ u, R < ‖u‖ → φ u = 0)
    (hω : ∀ u v, ‖u - v‖ ≤ 2 * ε * R → |φ u - φ v| ≤ ω) (hω0 : 0 ≤ ω) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (r ^ k) * ∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[k] ≤
      ∫⁻ y in G, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[k] +
        flatConst ε ^ k * (ENNReal.ofReal (r ^ k) *
          (ENNReal.ofReal ω * μHE[k] (hyperplane ν ∩ closedBall 0 (2 * R)))) +
        ENNReal.ofReal M *
          μHE[k] ((hyperplane ν \ projH ν '' G) ∩ closedBall (projH ν x) (R * r)) := by
  set p₀ := projH ν x
  have hp₀ : p₀ ∈ hyperplane ν := projH_mem_hyperplane hν x
  set g : Rn n → ℝ≥0∞ := fun p => ENNReal.ofReal (φ (r⁻¹ • (p - p₀))) with hg
  have hgm : Measurable g :=
    hφm.ennreal_ofReal.comp ((measurable_const_smul _).comp (measurable_id.sub_const _))
  set ind : Rn n → ℝ≥0∞ := fun p => (closedBall (0 : Rn n) (2 * R)).indicator 1 (r⁻¹ • (p - p₀))
    with hind
  have hindm : Measurable ind :=
    (measurable_const.indicator measurableSet_closedBall).comp
      ((measurable_const_smul _).comp (measurable_id.sub_const _))
  -- the part of `ν^⊥` outside the projected piece
  have hout : ∫⁻ p in hyperplane ν \ projH ν '' G, g p ∂μHE[k] ≤
      ENNReal.ofReal M *
        μHE[k] ((hyperplane ν \ projH ν '' G) ∩ closedBall p₀ (R * r)) := by
    calc ∫⁻ p in hyperplane ν \ projH ν '' G, g p ∂μHE[k]
        ≤ ∫⁻ p in hyperplane ν \ projH ν '' G,
            (closedBall p₀ (R * r)).indicator (fun _ => ENNReal.ofReal M) p ∂μHE[k] := by
          refine lintegral_mono fun p => ?_
          by_cases hp : p ∈ closedBall p₀ (R * r)
          · rw [indicator_of_mem hp]
            exact ENNReal.ofReal_le_ofReal (hφM _)
          · rw [indicator_of_notMem hp, hg]
            simp only
            rw [hφR, ENNReal.ofReal_zero]
            rw [mem_closedBall, dist_eq_norm, not_le] at hp
            rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul,
              lt_div_iff₀ hr]
            exact hp
      _ = _ := by
          rw [lintegral_indicator_const measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, inter_comm]
  -- pointwise comparison on the piece
  have hpt : ∀ y ∈ G, g (projH ν y) ≤
      ENNReal.ofReal (φ (r⁻¹ • (y - x))) + ENNReal.ofReal ω * ind (projH ν y) := by
    intro y hy
    obtain ⟨h1, h2, h3⟩ := h.near hν hε hx hy hr
    have := abs_sub_le_of_near hφR hω hε0 hω0 h1 h2 h3
    simp only [hg, hind]
    calc ENNReal.ofReal (φ (r⁻¹ • (projH ν y - p₀)))
        ≤ ENNReal.ofReal (φ (r⁻¹ • (y - x)) +
            ω * (closedBall (0 : Rn n) (2 * R)).indicator 1 (r⁻¹ • (projH ν y - p₀))) :=
          ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 this).1])
      _ ≤ _ := by
          by_cases hm : r⁻¹ • (projH ν y - p₀) ∈ closedBall (0 : Rn n) (2 * R)
          · simp only [indicator_of_mem hm, Pi.one_apply, mul_one]
            exact ENNReal.ofReal_add_le
          · simp only [indicator_of_notMem hm, mul_zero, add_zero, le_refl]
  have hind_le : ∫⁻ y in G, ind (projH ν y) ∂μHE[k] ≤
      flatConst ε ^ k *
        (ENNReal.ofReal (r ^ k) * μHE[k] (hyperplane ν ∩ closedBall 0 (2 * R))) := by
    calc ∫⁻ y in G, ind (projH ν y) ∂μHE[k]
        ≤ flatConst ε ^ k * ∫⁻ p in projH ν '' G, ind p ∂μHE[k] :=
          h.lintegral_comp_projH_le k hν (by linarith) hindm
      _ ≤ flatConst ε ^ k * ∫⁻ p in hyperplane ν, ind p ∂μHE[k] := by
          gcongr
          rintro _ ⟨y, -, rfl⟩
          exact projH_mem_hyperplane hν y
      _ = _ := by rw [hind, lintegral_hyperplane_indicator_comp k hp₀ hr R]
  calc ENNReal.ofReal (r ^ k) * ∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[k]
      = ∫⁻ p in hyperplane ν, g p ∂μHE[k] :=
        (lintegral_hyperplane_comp_smul_sub k hp₀ hr _).symm
    _ ≤ ∫⁻ p in projH ν '' G ∪ (hyperplane ν \ projH ν '' G), g p ∂μHE[k] := by
        refine lintegral_mono_set fun p hp => ?_
        by_cases hpG : p ∈ projH ν '' G
        · exact Or.inl hpG
        · exact Or.inr ⟨hp, hpG⟩
    _ ≤ ∫⁻ p in projH ν '' G, g p ∂μHE[k] +
          ∫⁻ p in hyperplane ν \ projH ν '' G, g p ∂μHE[k] := lintegral_union_le _ _ _
    _ ≤ ∫⁻ y in G, g (projH ν y) ∂μHE[k] +
          ENNReal.ofReal M *
            μHE[k] ((hyperplane ν \ projH ν '' G) ∩ closedBall p₀ (R * r)) :=
        add_le_add (lintegral_le_lintegral_comp_projH k hν G hgm) hout
    _ ≤ ∫⁻ y in G, (ENNReal.ofReal (φ (r⁻¹ • (y - x))) +
            ENNReal.ofReal ω * ind (projH ν y)) ∂μHE[k] +
          ENNReal.ofReal M *
            μHE[k] ((hyperplane ν \ projH ν '' G) ∩ closedBall p₀ (R * r)) := by
        gcongr ?_ + _
        exact setLIntegral_mono' hGm hpt
    _ ≤ _ := by
        have hm' : Measurable fun y => ind (projH ν y) := hindm.comp (measurable_projH ν)
        rw [lintegral_add_right (g := fun y => ENNReal.ofReal ω * ind (projH ν y)) _
          (measurable_const.mul hm'), lintegral_const_mul _ hm']
        calc _ ≤ ∫⁻ y in G, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[k] +
              ENNReal.ofReal ω * (flatConst ε ^ k *
                (ENNReal.ofReal (r ^ k) * μHE[k] (hyperplane ν ∩ closedBall 0 (2 * R)))) +
              ENNReal.ofReal M *
                μHE[k] ((hyperplane ν \ projH ν '' G) ∩ closedBall p₀ (R * r)) := by
              gcongr
          _ = _ := by ring

end BlowUp

/-! ### Measure bounds in balls -/

section Balls

variable (k : ℕ) {ν : Rn n} {ε : ℝ} {G : Set (Rn n)}

theorem norm_projH_sub_le {ν : Rn n} (hν : ‖ν‖ = 1) (y z : Rn n) :
    ‖projH ν y - projH ν z‖ ≤ ‖y - z‖ := by
  rw [← projH_sub]
  exact norm_projH_le hν _

/-- Upper bound for the measure of a flat piece in a ball. -/
theorem IsFlatPiece.measure_inter_closedBall_le (h : IsFlatPiece ν ε G) (hν : ‖ν‖ = 1)
    (hε : ε < 1) (x : Rn n) (r : ℝ) :
    (μHE[k] : Measure (Rn n)) (G ∩ closedBall x r) ≤
      flatConst ε ^ k * μHE[k] (hyperplane ν ∩ closedBall (projH ν x) r) := by
  refine (h.measure_le k hν hε inter_subset_left).trans ?_
  gcongr
  rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
  refine ⟨projH_mem_hyperplane hν y, ?_⟩
  rw [mem_closedBall, dist_eq_norm] at hy ⊢
  exact (norm_projH_sub_le hν y x).trans hy

/-- Lower bound for the measure of a flat piece in a ball. -/
theorem IsFlatPiece.le_measure_inter_closedBall (h : IsFlatPiece ν ε G) (hν : ‖ν‖ = 1)
    (hε : ε < 1) {x : Rn n} (hx : x ∈ G) (r : ℝ) :
    (μHE[k] : Measure (Rn n)) (hyperplane ν ∩ closedBall (projH ν x) ((1 - ε) * r)) ≤
      μHE[k] (G ∩ closedBall x r) +
        μHE[k] ((hyperplane ν \ projH ν '' G) ∩ closedBall (projH ν x) ((1 - ε) * r)) := by
  have hsub : hyperplane ν ∩ closedBall (projH ν x) ((1 - ε) * r) ⊆
      projH ν '' (G ∩ closedBall x r) ∪
        (hyperplane ν \ projH ν '' G) ∩ closedBall (projH ν x) ((1 - ε) * r) := by
    rintro p ⟨hpH, hpB⟩
    by_cases hpG : p ∈ projH ν '' G
    · obtain ⟨y, hy, rfl⟩ := hpG
      refine Or.inl ⟨y, ⟨hy, ?_⟩, rfl⟩
      rw [mem_closedBall, dist_eq_norm] at hpB ⊢
      have := h.norm_projH_sub_ge hν hy hx
      have h1 : 0 < 1 - ε := sub_pos.2 hε
      nlinarith
    · exact Or.inr ⟨⟨hpH, hpG⟩, hpB⟩
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add_left (measure_image_projH_le k hν _) _))

/-- A hyperplane is a flat piece for every nearby normal. -/
theorem isFlatPiece_hyperplane (ν ν' : Rn n) : IsFlatPiece ν ‖ν - ν'‖ (hyperplane ν') := by
  intro y hy z hz
  have h0 : ⟪y - z, ν'⟫ = 0 := by
    rw [inner_sub_left, mem_hyperplane.1 hy, mem_hyperplane.1 hz, sub_zero]
  have : ⟪y - z, ν⟫ = ⟪y - z, ν - ν'⟫ := by rw [inner_sub_right, h0, sub_zero]
  rw [this, mul_comm]
  exact abs_real_inner_le_norm _ _

end Balls

end GMTFoundations.GMT
