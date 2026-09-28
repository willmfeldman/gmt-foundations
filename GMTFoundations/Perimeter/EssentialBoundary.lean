/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.DensityEstimates.Lemma53
public import GMTFoundations.Perimeter.DensityEstimates.Covering
public import GMTFoundations.Perimeter.BlowUp
import GMTFoundations.Perimeter.Poincare
import GMTFoundations.Perimeter.HalfSpace

/-!
# Reduced versus essential boundary (EG Lemma 5.5)

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

The essential boundary `essentialBoundary E` (neither density `0` nor density `1`) is, for
measurable `E`, EG's measure-theoretic boundary `∂_*E` (EG Def 5.7, stated with `limsup`; see
`mem_essentialBoundary_iff_limsup`).

* `volume_halfSpace_inter_ball`, `volume_halfSpace_pos_inter_ball`: an open half-space through
  the center of a ball has half its volume.
* `reducedBoundary_subset_essentialBoundary` (EG Lemma 5.5 (i)): by the blow-up theorem
  (`hasDensity_symmDiff_halfSpace`, EG Thm 5.13) `E` has density `1/2` at every point of `∂*E`.
* `IsGaussGreenPair.limsup_measure_ball_pos` (EG Lemma 5.5 (ii), proof step 2, in a corrected
  form): at every `x ∈ Ω ∩ ∂ᵉE`, `limsup μ(B_r(x))/r^{n-1} > 0`. The density ratio is
  continuous in `r`, so the intermediate value theorem gives radii `r → 0` at which it lies in
  `[c, 1 - c]`; the relative isoperimetric inequality (in the `L¹` form
  `IsGaussGreenPair.min_volume_le_measure_ball`) then bounds `μ(B_r(x))` from below. EG instead
  claim radii `r_j → 0` at which `ℒⁿ(B(x,r_j) ∩ E)/(α(n) r_jⁿ)` equals one fixed `α ∈ (0,1)`, by
  continuity; this fails when the ratio converges to a limit in `(0,1)` without taking any fixed
  value along a sequence `r_j → 0`, so we use the two-sided bound instead.
* `IsGaussGreenPair.hausdorffN_eq_zero_of_subset_essentialBoundary` ("L-null"): a `μ`-null subset
  of `Ω ∩ ∂ᵉE` is `ℋ^{n-1}`-null (the covering lemma `hausdorffN_eq_zero_of_measure_eq_zero`,
  i.e. the "standard covering arguments" of EG).
* `IsGaussGreenPair.hausdorffN_essentialBoundary_diff_reducedBoundary` (EG Lemma 5.5 (ii)).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### Half-balls -/

/-- The three pieces of a ball cut by a hyperplane through its center. -/
private theorem volume_ball_le_halves {v : Rn n} (hv : v ≠ 0) (x : Rn n) (r : ℝ) :
    volume (ball x r) ≤ volume ({y | ⟪y - x, v⟫ < 0} ∩ ball x r) +
      volume ({y | 0 < ⟪y - x, v⟫} ∩ ball x r) := by
  have hZ : volume {y : Rn n | ⟪y - x, v⟫ = 0} = 0 := by
    have : {y : Rn n | ⟪y - x, v⟫ = 0} = {y | ⟪y, v⟫ = ⟪x, v⟫} := by
      ext y; simp [inner_sub_left, sub_eq_zero]
    rw [this]; exact volume_setOf_inner_eq hv _
  calc volume (ball x r)
      ≤ volume (({y | ⟪y - x, v⟫ < 0} ∩ ball x r ∪ {y | 0 < ⟪y - x, v⟫} ∩ ball x r) ∪
          {y : Rn n | ⟪y - x, v⟫ = 0}) := by
        refine measure_mono fun y hy => ?_
        rcases lt_trichotomy ⟪y - x, v⟫ 0 with h | h | h
        · exact Or.inl (Or.inl ⟨h, hy⟩)
        · exact Or.inr h
        · exact Or.inl (Or.inr ⟨h, hy⟩)
    _ ≤ volume ({y | ⟪y - x, v⟫ < 0} ∩ ball x r ∪ {y | 0 < ⟪y - x, v⟫} ∩ ball x r) +
          volume {y : Rn n | ⟪y - x, v⟫ = 0} := measure_union_le _ _
    _ ≤ _ := by rw [hZ, add_zero]; exact measure_union_le _ _

/-- The reflection `y ↦ 2x - y` swaps the two open half-balls. -/
private theorem volume_halfSpace_neg_eq_pos {v : Rn n} (x : Rn n) (r : ℝ) :
    volume ({y | ⟪y - x, v⟫ < 0} ∩ ball x r) = volume ({y | 0 < ⟪y - x, v⟫} ∩ ball x r) := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure (Rn n)) ((2 : ℝ) • x)
  have hpre : (fun y => (2 : ℝ) • x - y) ⁻¹' ({y | ⟪y - x, v⟫ < 0} ∩ ball x r) =
      {y | 0 < ⟪y - x, v⟫} ∩ ball x r := by
    ext y
    have h1 : (2 : ℝ) • x - y - x = -(y - x) := by rw [two_smul]; abel
    have h2 : dist ((2 : ℝ) • x - y) x = dist y x := by
      rw [dist_eq_norm, dist_eq_norm, h1, norm_neg]
    simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, mem_ball, h1, h2, inner_neg_left,
      neg_lt_zero]
  rw [← hpre, hmp.measure_preimage]
  exact ((measurableSet_lt ((continuous_id.sub continuous_const).inner
    continuous_const).measurable measurable_const).inter measurableSet_ball).nullMeasurableSet

/-- An open half-space through the center of a ball has half its volume. -/
theorem volume_halfSpace_inter_ball {v : Rn n} (hv : v ≠ 0) (x : Rn n) (r : ℝ) :
    volume ({y | ⟪y - x, v⟫ < 0} ∩ ball x r) = volume (ball x r) / 2 := by
  have hle := volume_ball_le_halves hv x r
  rw [← volume_halfSpace_neg_eq_pos] at hle
  have hge : volume ({y | ⟪y - x, v⟫ < 0} ∩ ball x r) +
      volume ({y | 0 < ⟪y - x, v⟫} ∩ ball x r) ≤ volume (ball x r) := by
    rw [← measure_union]
    · exact measure_mono (union_subset inter_subset_right inter_subset_right)
    · refine disjoint_left.2 fun y hy hy' => ?_
      simp only [mem_inter_iff, mem_setOf_eq] at hy hy'
      linarith [hy.1, hy'.1]
    · exact (measurableSet_lt measurable_const ((continuous_id.sub continuous_const).inner
        continuous_const).measurable).inter measurableSet_ball
  rw [← volume_halfSpace_neg_eq_pos] at hge
  have heq : volume ({y | ⟪y - x, v⟫ < 0} ∩ ball x r) * 2 = volume (ball x r) := by
    rw [mul_two]; exact le_antisymm hge hle
  rw [← heq, ENNReal.mul_div_cancel_right two_ne_zero ENNReal.ofNat_ne_top]

/-- The positive open half-space through the center of a ball has half its volume. -/
theorem volume_halfSpace_pos_inter_ball {v : Rn n} (hv : v ≠ 0) (x : Rn n) (r : ℝ) :
    volume ({y | 0 < ⟪y - x, v⟫} ∩ ball x r) = volume (ball x r) / 2 := by
  rw [← volume_halfSpace_neg_eq_pos, volume_halfSpace_inter_ball hv]

/-! ### Density `1/2` at reduced-boundary points (EG Lemma 5.5 (i)) -/

/-- If `E` is close to a half-space through `x` (density `0` of the symmetric difference), then
`E` has density `1/2` at `x`. -/
theorem hasDensity_half_of_hasDensity_symmDiff {E : Set (Rn n)} {x v : Rn n} (hv : v ≠ 0)
    (h : HasDensity (symmDiff E {y | ⟪y - x, v⟫ < 0}) x 0) : HasDensity E x (1 / 2) := by
  set H := {y : Rn n | ⟪y - x, v⟫ < 0}
  set Q := symmDiff E H
  unfold HasDensity at h ⊢
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (by simpa using h)
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hB0 : 0 < (volume (ball x r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne
  have hfin : ∀ S : Set (Rn n), volume (S ∩ ball x r) ≠ ∞ := fun S =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hH : (volume (H ∩ ball x r)).toReal = (volume (ball x r)).toReal / 2 := by
    rw [volume_halfSpace_inter_ball hv, ENNReal.toReal_div]; norm_num
  -- `E ∩ B ⊆ (H ∩ B) ∪ (Q ∩ B)` and `H ∩ B ⊆ (E ∩ B) ∪ (Q ∩ B)`
  have h1 : (volume (E ∩ ball x r)).toReal ≤
      (volume (H ∩ ball x r)).toReal + (volume (Q ∩ ball x r)).toReal := by
    rw [← ENNReal.toReal_add (hfin _) (hfin _)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩)
      ((measure_mono fun y hy => ?_).trans (measure_union_le _ _))
    by_cases hyH : y ∈ H
    · exact Or.inl ⟨hyH, hy.2⟩
    · exact Or.inr ⟨Or.inl ⟨hy.1, hyH⟩, hy.2⟩
  have h2 : (volume (H ∩ ball x r)).toReal ≤
      (volume (E ∩ ball x r)).toReal + (volume (Q ∩ ball x r)).toReal := by
    rw [← ENNReal.toReal_add (hfin _) (hfin _)]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩)
      ((measure_mono fun y hy => ?_).trans (measure_union_le _ _))
    by_cases hyE : y ∈ E
    · exact Or.inl ⟨hyE, hy.2⟩
    · exact Or.inr ⟨Or.inr ⟨hy.1, hyE⟩, hy.2⟩
  rw [hH] at h1 h2
  have hq : (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal - 1 / 2 =
      ((volume (E ∩ ball x r)).toReal - (volume (ball x r)).toReal / 2) /
        (volume (ball x r)).toReal := by
    rw [sub_div, div_right_comm, div_self hB0.ne']
  rw [hq, Real.norm_eq_abs, abs_div, abs_of_pos hB0]
  exact div_le_div_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) hB0.le

/-- Density `1/2` excludes densities `0` and `1`. -/
theorem mem_essentialBoundary_of_hasDensity_half {E : Set (Rn n)} {x : Rn n}
    (h : HasDensity E x (1 / 2)) : x ∈ essentialBoundary E := by
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · have := tendsto_nhds_unique h h0; norm_num at this
  · have := tendsto_nhds_unique h h1; norm_num at this

/-- **EG Lemma 5.5 (i).** The reduced boundary lies in the essential boundary. By the blow-up
theorem (`hasDensity_symmDiff_halfSpace`, EG Thm 5.13, applied to the pair witnessing membership)
`E` has density `1/2` at every point of `∂*E`. -/
theorem reducedBoundary_subset_essentialBoundary (hn : 2 ≤ n) {Ω E : Set (Rn n)} (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) : reducedBoundary Ω E ⊆ essentialBoundary E := by
  rintro x ⟨hxΩ, μ, ν, h, hpos, v, hv, hlim⟩
  have hv0 : v ≠ 0 := fun h0 => by rw [h0, norm_zero] at hv; exact zero_ne_one hv
  exact mem_essentialBoundary_of_hasDensity_half (hasDensity_half_of_hasDensity_symmDiff hv0
    (hasDensity_symmDiff_halfSpace hn hΩ hE h hxΩ hpos hv hlim))

/-! ### Positive upper density on the essential boundary (EG Lemma 5.5 (ii), step 2) -/

/-- The volume of `E ∩ B_r(x)` moves by at most the volume of the annulus. -/
private theorem volume_inter_ball_sub_le (E : Set (Rn n)) (x : Rn n) {s r : ℝ} (hsr : s ≤ r) :
    (volume (E ∩ ball x r)).toReal - (volume (E ∩ ball x s)).toReal ≤
      (volume (ball x r)).toReal - (volume (ball x s)).toReal := by
  have hfin : ∀ S : Set (Rn n), ∀ t, volume (S ∩ ball x t) ≠ ∞ := fun S t =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hBsub : ball x s ⊆ ball x r := ball_subset_ball hsr
  have hdiff : volume (ball x r \ ball x s) = volume (ball x r) - volume (ball x s) :=
    measure_diff hBsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
  have hle : volume (E ∩ ball x r) ≤ volume (E ∩ ball x s) + volume (ball x r \ ball x s) :=
    (measure_mono fun y hy => by
      by_cases hys : y ∈ ball x s
      · exact Or.inl ⟨hy.1, hys⟩
      · exact Or.inr ⟨hy.2, hys⟩).trans (measure_union_le _ _)
  rw [hdiff] at hle
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin E s,
    (ENNReal.sub_ne_top measure_ball_lt_top.ne)⟩) hle
  rw [ENNReal.toReal_add (hfin E s) (ENNReal.sub_ne_top measure_ball_lt_top.ne),
    ENNReal.toReal_sub_of_le (measure_mono hBsub) measure_ball_lt_top.ne] at this
  linarith

private theorem continuous_volume_ball_toReal (x : Rn n) :
    ContinuousOn (fun r => (volume (ball x r)).toReal) (Ioi 0) := by
  refine ContinuousOn.congr (f := fun r : ℝ => r ^ n * (volume (ball (0 : Rn n) 1)).toReal)
    (by fun_prop : Continuous fun r : ℝ => r ^ n * (volume (ball (0 : Rn n) 1)).toReal).continuousOn
    fun r (hr : r ∈ Ioi 0) => ?_
  rw [Measure.addHaar_ball_of_pos volume x (mem_Ioi.1 hr), finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (mem_Ioi.1 hr).le n)]

/-- `r ↦ |E ∩ B_r(x)|` is continuous on `(0, ∞)`. -/
theorem continuousOn_volume_inter_ball (E : Set (Rn n)) (x : Rn n) :
    ContinuousOn (fun r => (volume (E ∩ ball x r)).toReal) (Ioi 0) := by
  intro r₀ hr₀
  have hg := continuous_volume_ball_toReal x r₀ hr₀
  rw [Metric.continuousWithinAt_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := hg ε hε
  refine ⟨δ, hδ, fun {r} hr hrr₀ => ?_⟩
  have hgr := hδg hr hrr₀
  rw [Real.dist_eq] at hgr ⊢
  rcases le_total r r₀ with h | h
  · have h1 := volume_inter_ball_sub_le E x h
    have h2 : (volume (E ∩ ball x r)).toReal ≤ (volume (E ∩ ball x r₀)).toReal :=
      ENNReal.toReal_mono ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
        (measure_mono (inter_subset_inter_right _ (ball_subset_ball h)))
    have h3 : (volume (ball x r)).toReal ≤ (volume (ball x r₀)).toReal :=
      ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono (ball_subset_ball h))
    rw [abs_lt] at hgr ⊢; constructor <;> linarith
  · have h1 := volume_inter_ball_sub_le E x h
    have h2 : (volume (E ∩ ball x r₀)).toReal ≤ (volume (E ∩ ball x r)).toReal :=
      ENNReal.toReal_mono ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
        (measure_mono (inter_subset_inter_right _ (ball_subset_ball h)))
    have h3 : (volume (ball x r₀)).toReal ≤ (volume (ball x r)).toReal :=
      ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono (ball_subset_ball h))
    rw [abs_lt] at hgr ⊢; constructor <;> linarith

/-- The density ratio of `E` at `x` lies in `[0, 1]`. -/
private theorem densityRatio_mem_Icc (E : Set (Rn n)) (x : Rn n) (r : ℝ) :
    0 ≤ (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal ∧
      (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal ≤ 1 := by
  refine ⟨div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg, div_le_one_of_le₀ ?_
    ENNReal.toReal_nonneg⟩
  exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono inter_subset_right)

/-- **EG Lemma 5.5 (ii), proof step 2, corrected.** At a point of the essential boundary, the
density ratio of `E` lies in `[c, 1 - c]` for arbitrarily small radii. (EG claim that the ratio
takes one fixed value `α ∈ (0,1)` along a sequence `r_j → 0`; that can fail if the ratio
converges.) If the ratio
oscillates this follows from the intermediate value theorem; if it converges, the limit lies in
`(0, 1)`. -/
theorem exists_frequently_mem_Icc_of_mem_essentialBoundary {E : Set (Rn n)} {x : Rn n}
    (hx : x ∈ essentialBoundary E) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ r in 𝓝[>] (0 : ℝ),
      c ≤ (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal ∧
        (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal ≤ 1 - c := by
  set θ : ℝ → ℝ := fun r => (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal
  have hθ01 : ∀ r, 0 ≤ θ r ∧ θ r ≤ 1 := densityRatio_mem_Icc E x
  have hθc : ContinuousOn θ (Ioi 0) :=
    (continuousOn_volume_inter_ball E x).div (continuous_volume_ball_toReal x) fun r hr =>
      (ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne).ne'
  -- frequently `θ ≥ a` and frequently `θ ≤ 1 - b`
  obtain ⟨a, ha, hfa⟩ : ∃ a > 0, ∃ᶠ r in 𝓝[>] (0 : ℝ), a ≤ θ r := by
    have h0 := hx.1
    unfold HasDensity at h0
    rw [Metric.tendsto_nhds] at h0
    push Not at h0
    obtain ⟨a, ha, hfa⟩ := h0
    refine ⟨a, ha, hfa.mono fun r hr => ?_⟩
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hθ01 r).1] at hr
  obtain ⟨b, hb, hfb⟩ : ∃ b > 0, ∃ᶠ r in 𝓝[>] (0 : ℝ), θ r ≤ 1 - b := by
    have h1 := hx.2
    unfold HasDensity at h1
    rw [Metric.tendsto_nhds] at h1
    push Not at h1
    obtain ⟨b, hb, hfb⟩ := h1
    refine ⟨b, hb, hfb.mono fun r hr => ?_⟩
    rw [Real.dist_eq, abs_of_nonpos (by linarith [(hθ01 r).2])] at hr
    linarith
  refine ⟨min a b / 2, by positivity, ?_⟩
  set c := min a b / 2
  rw [(nhdsGT_basis (0 : ℝ)).frequently_iff] at hfa hfb ⊢
  intro r₀ hr₀
  obtain ⟨r₁, hr₁, h₁⟩ := hfa r₀ hr₀
  obtain ⟨r₂, hr₂, h₂⟩ := hfb r₀ hr₀
  have hca : c ≤ a / 2 := by have := min_le_left a b; simp only [c]; linarith
  have hcb : c ≤ b / 2 := by have := min_le_right a b; simp only [c]; linarith
  have ha1 : a ≤ 1 := h₁.trans (hθ01 r₁).2
  by_cases hc1 : θ r₁ ≤ 1 - c
  · exact ⟨r₁, hr₁, show c ≤ θ r₁ by linarith, hc1⟩
  by_cases hc2 : c ≤ θ r₂
  · exact ⟨r₂, hr₂, hc2, show θ r₂ ≤ 1 - c by linarith⟩
  push Not at hc1 hc2
  -- the intermediate value theorem between `r₁` and `r₂`
  have hsub : uIcc r₁ r₂ ⊆ Ioo 0 r₀ := by
    intro r hr
    rcases mem_uIcc.1 hr with h | h
    · exact ⟨hr₁.1.trans_le h.1, h.2.trans_lt hr₂.2⟩
    · exact ⟨hr₂.1.trans_le h.1, h.2.trans_lt hr₁.2⟩
  have hhalf : (1 / 2 : ℝ) ∈ uIcc (θ r₁) (θ r₂) :=
    mem_uIcc.2 (Or.inr ⟨by linarith, by linarith⟩)
  obtain ⟨r, hr, hθr⟩ := intermediate_value_uIcc
    (hθc.mono fun r hr => (hsub hr).1) hhalf
  refine ⟨r, hsub hr, ?_⟩
  change c ≤ θ r ∧ θ r ≤ 1 - c
  rw [hθr]
  constructor <;> linarith

/-- **Positive upper density on the essential boundary** (EG Lemma 5.5 (ii), step 2): at every
`x ∈ Ω ∩ ∂ᵉE`, `limsup_{r → 0} μ(B_r(x)) / r^{n-1} > 0`. -/
theorem IsGaussGreenPair.limsup_measure_ball_pos (hn : 2 ≤ n) {Ω E : Set (Rn n)}
    {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) {x : Rn n} (hxΩ : x ∈ Ω) (hx : x ∈ essentialBoundary E) :
    0 < limsup (fun r => μ (ball x r) / ENNReal.ofReal (r ^ (n - 1))) (𝓝[>] 0) := by
  obtain ⟨c, hc, hfr⟩ := exists_frequently_mem_Icc_of_mem_essentialBoundary hx
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x hxΩ
  set ω := volume (ball (0 : Rn n) 1)
  have hω0 : ω ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hωt : ω ≠ ∞ := measure_ball_lt_top.ne
  set t : ℝ≥0∞ := ENNReal.ofReal c * ω / 2 ^ (n + 1)
  have ht : 0 < t := ENNReal.div_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hc).ne' hω0)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  refine ht.trans_le (le_limsup_of_frequently_le ?_ (by isBoundedDefault))
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r < ε :=
    (Ioo_mem_nhdsGT hε)
  refine (hfr.and_eventually hsmall).mono fun r ⟨⟨h1, h2⟩, hr0, hrε⟩ => ?_
  have hB : ball x r ⊆ Ω := (ball_subset_ball hrε.le).trans hεΩ
  have hBpos : 0 < (volume (ball x r)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x hr0).ne' measure_ball_lt_top.ne
  have hfin : ∀ S : Set (Rn n), volume (S ∩ ball x r) ≠ ∞ := fun S =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  -- both `|E ∩ B|` and `|B ∖ E|` are at least `c |B|`
  have hEB : ENNReal.ofReal c * volume (ball x r) ≤ volume (E ∩ ball x r) := by
    rw [← ENNReal.ofReal_toReal measure_ball_lt_top.ne, ← ENNReal.ofReal_mul hc.le,
      ← ENNReal.ofReal_toReal (hfin E)]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hBpos).1 h1)
  have hBE : ENNReal.ofReal c * volume (ball x r) ≤ volume (ball x r \ E) := by
    have hd : volume (ball x r \ E) = volume (ball x r) - volume (E ∩ ball x r) := by
      rw [← measure_diff (inter_subset_right) (hE.inter measurableSet_ball).nullMeasurableSet
        (hfin E)]
      congr 1; ext y; simp
    have hdr : (volume (ball x r \ E)).toReal =
        (volume (ball x r)).toReal - (volume (E ∩ ball x r)).toReal := by
      rw [hd, ENNReal.toReal_sub_of_le (measure_mono inter_subset_right) measure_ball_lt_top.ne]
    rw [← ENNReal.ofReal_toReal measure_ball_lt_top.ne, ← ENNReal.ofReal_mul hc.le,
      ← ENNReal.ofReal_toReal ((measure_mono diff_subset).trans_lt measure_ball_lt_top).ne, hdr]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (div_le_iff₀ hBpos).1 h2
    linarith
  have hmin := h.min_volume_le_measure_ball hE hB
  have hlow : ENNReal.ofReal c * volume (ball x r) ≤
      2 ^ (n + 1) * ENNReal.ofReal r * μ (ball x r) :=
    (le_min hEB hBE).trans hmin
  -- `|B_r| = rⁿ ω = r · r^{n-1} ω`
  have hvol : volume (ball x r) = ENNReal.ofReal r * ENNReal.ofReal (r ^ (n - 1)) * ω := by
    rw [Measure.addHaar_ball_of_pos volume x hr0, finrank_euclideanSpace_fin,
      ← ENNReal.ofReal_mul hr0.le, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [hvol] at hlow
  have hr' : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr0).ne'
  have hlow' : ENNReal.ofReal c * ω * ENNReal.ofReal (r ^ (n - 1)) ≤
      2 ^ (n + 1) * μ (ball x r) := by
    have : ENNReal.ofReal r * (ENNReal.ofReal c * ω * ENNReal.ofReal (r ^ (n - 1))) ≤
        ENNReal.ofReal r * (2 ^ (n + 1) * μ (ball x r)) := by
      calc _ = ENNReal.ofReal c * (ENNReal.ofReal r * ENNReal.ofReal (r ^ (n - 1)) * ω) := by ring
        _ ≤ 2 ^ (n + 1) * ENNReal.ofReal r * μ (ball x r) := hlow
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_right hr' ENNReal.ofReal_ne_top).1 this
  have hrpow : ENNReal.ofReal (r ^ (n - 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hr0 _)).ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl hrpow) (Or.inl ENNReal.ofReal_ne_top)]
  calc t * ENNReal.ofReal (r ^ (n - 1))
      = ENNReal.ofReal c * ω * ENNReal.ofReal (r ^ (n - 1)) / 2 ^ (n + 1) := by
        simp only [t, ENNReal.div_eq_inv_mul]; ring
    _ ≤ μ (ball x r) := ENNReal.div_le_of_le_mul' hlow'

/-! ### `μ`-null subsets of the essential boundary are `ℋ^{n-1}`-null -/

/-- **L-null.** A `μ`-null subset of `Ω ∩ ∂ᵉE` is `ℋ^{n-1}`-null. This is the "standard covering
argument" of EG Lemma 5.5 (ii) (`hausdorffN_eq_zero_of_measure_eq_zero`) with the positive
upper density of `IsGaussGreenPair.limsup_measure_ball_pos`. -/
theorem IsGaussGreenPair.hausdorffN_eq_zero_of_subset_essentialBoundary (hn : 2 ≤ n)
    {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) (hE : MeasurableSet E) {A : Set (Rn n)} (hA : A ⊆ Ω ∩ essentialBoundary E)
    (hμA : μ A = 0) : hausdorffN n (n - 1) A = 0 :=
  hausdorffN_eq_zero_of_measure_eq_zero hΩ h.lt_top_of_isCompact (fun _ hx => (hA hx).1) hμA
    fun _ hx => h.limsup_measure_ball_pos hn hΩ hE (hA hx).1 (hA hx).2

/-- **EG Lemma 5.5 (ii).** `ℋ^{n-1}((Ω ∩ ∂ᵉE) ∖ ∂*E) = 0`. -/
theorem IsGaussGreenPair.hausdorffN_essentialBoundary_diff_reducedBoundary (hn : 2 ≤ n)
    {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) (hE : MeasurableSet E) :
    hausdorffN n (n - 1) ((Ω ∩ essentialBoundary E) \ reducedBoundary Ω E) = 0 :=
  h.hausdorffN_eq_zero_of_subset_essentialBoundary hn hΩ hE diff_subset
    (measure_mono_null (diff_subset_diff_left inter_subset_left)
      (h.measure_diff_reducedBoundary hΩ))

end GMTFoundations
