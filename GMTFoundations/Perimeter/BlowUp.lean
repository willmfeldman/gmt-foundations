/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Statements.Perimeter
public import GMTFoundations.Perimeter.BlowUpNormal
import GMTFoundations.Perimeter.HalfSpace
import GMTFoundations.Perimeter.ReducedBoundary
import GMTFoundations.Perimeter.DensityEstimates.Lemma53
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Blow-up at reduced-boundary points (EG Thms 5.13, 5.14)

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

Steps 1–5 of EG Thm 5.13 (rescaling, compactness, Claims #1 and #2) are in `BlowUpScaling.lean`
and `BlowUpNormal.lean`. This file has Claim #3, the passage from subsequences to the full limit,
the blow-up theorem `hasDensity_symmDiff_halfSpace`, and EG Thm 5.14 (iii).

## Main results

* `ae_eq_halfSpace_zero_of_measure_pos` (Claim #3): a set that is a.e. `∅`, `ℝⁿ` or
  `{⟪y, v⟫ ≤ γ}`, with positive measure inside and outside every ball `B_ρ(0)`, is a.e.
  `{⟪y, v⟫ ≤ 0}`.
* `exists_blowup_subseq_ae_eq_halfSpace`: EG Thm 5.13 along a subsequence of any sequence of
  scales, from the density estimates `hup`, `hin`, `hout` (EG Lemma 5.3 (iv), (i), (ii)) taken as
  hypotheses.
* `IsGaussGreenPair.blowup_densityEstimates`: the estimates of `Perimeter/DensityEstimates` in
  that shape.
* `IsGaussGreenPair.tendsto_blowup_halfSpace` (EG Thm 5.13):
  `χ_{E_{x,r}} → χ_{{⟪z, v⟫ < 0}}` in `L¹_loc(ℝⁿ)` as `r → 0+`.
* `hasDensity_symmDiff_halfSpace` (EG Thm 5.13, in density form; `HalfSpaceBlowUpStatement`).
* `IsGaussGreenPair.tendsto_measure_ball_div` (EG Thm 5.14 (iii)):
  `μ(B_r(x)) / (ω_{n-1} r^{n-1}) → 1`.

## Proof notes

Subsequences to the full limit: `tendsto_nhdsGT_zero_of_forall_subseq` (Mathlib's
`tendsto_of_subseq_tendsto`, after shifting a sequence tending to `0` within `(0, ∞)` so that all
terms are positive). Claim #3 transfers the lower volume bounds to the limit set
(`le_volume_inter_of_tendsto`). For 5.14 (iii) the limit pair of `F =ᵃᵉ {⟪y, v⟫ ≤ 0}` is not
identified by uniqueness: `μ_F(B_ρ) = TV(F; B_ρ) = TV(H⁻; B_ρ) = ω_{n-1} ρ^{n-1}` (via
`totalVariationOn_congr_ae` and `totalVariationOn_halfSpace_ball`). EG's squeeze between
`B_{1-η}` and `B_{1+η}` uses `ContDiffBump` cutoffs and the mass convergence
`tendsto_blowup_integral_cutoff`, so no `μ_F(∂B) = 0` argument is needed.
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace ContDiff symmDiff

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### Lebesgue measure of blow-ups -/

section Volume

theorem volume_preimage_affine (x : Rn n) {r : ℝ} (hr : r ≠ 0) (S : Set (Rn n)) :
    volume ((fun z ↦ x + r • z) ⁻¹' S) = ENNReal.ofReal |(r ^ n)⁻¹| * volume S := by
  have : (fun z : Rn n ↦ x + r • z) ⁻¹' S = (r • ·) ⁻¹' ((fun y ↦ x + y) ⁻¹' S) := rfl
  rw [this, Measure.addHaar_preimage_smul volume hr, finrank_euclideanSpace_fin,
    measure_preimage_add]

theorem volume_blowupSet (x : Rn n) {r : ℝ} (hr : 0 < r) (S : Set (Rn n)) :
    volume (blowupSet x r S) = ENNReal.ofReal ((r ^ n)⁻¹) * volume S := by
  rw [blowupSet, volume_preimage_affine x hr.ne', abs_of_pos (by positivity)]

theorem blowupSet_ball (x : Rn n) {r : ℝ} (hr : 0 < r) (L : ℝ) :
    blowupSet x r (ball x (r * L)) = ball 0 L := by
  ext z
  simp only [blowupSet, mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero,
    norm_smul, Real.norm_of_nonneg hr.le]
  exact mul_lt_mul_iff_right₀ hr

theorem blowupSet_halfSpace (x : Rn n) {r : ℝ} (hr : 0 < r) (v : Rn n) :
    blowupSet x r {y | ⟪y - x, v⟫ < 0} = {z | ⟪z, v⟫ < 0} := by
  ext z
  simp only [blowupSet, mem_preimage, mem_ofPred_eq, add_sub_cancel_left, real_inner_smul_left]
  constructor
  · intro h; by_contra h'; exact absurd h (not_lt.2 (mul_nonneg hr.le (not_lt.1 h')))
  · intro h; exact mul_neg_of_pos_of_neg hr h

/-- `|B_{rL}(x) ∩ S| = rⁿ |B_L ∩ S_{x,r}|`. -/
theorem volume_ball_inter_eq (x : Rn n) {r : ℝ} (hr : 0 < r) (L : ℝ) (S : Set (Rn n)) :
    volume (ball x (r * L) ∩ S) =
      ENNReal.ofReal (r ^ n) * volume (ball 0 L ∩ blowupSet x r S) := by
  have h := volume_blowupSet x hr (ball x (r * L) ∩ S)
  rw [show blowupSet x r (ball x (r * L) ∩ S) = blowupSet x r (ball x (r * L)) ∩ blowupSet x r S
    from rfl, blowupSet_ball x hr] at h
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
    ENNReal.ofReal_one, one_mul]

end Volume

/-! ### `L¹` distance of indicators -/

section Indicator

theorem eLpNorm_indicator_sub_indicator {A B K : Set (Rn n)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    eLpNorm (A.indicator (1 : Rn n → ℝ) - B.indicator 1) 1 (volume.restrict K) =
      volume (A ∆ B ∩ K) := by
  rw [eLpNorm_one_eq_lintegral_enorm
    ((measurable_one.indicator hA).sub (measurable_one.indicator hB)).aestronglyMeasurable]
  have hpt : ∀ y, ‖(A.indicator (1 : Rn n → ℝ) - B.indicator (1 : Rn n → ℝ)) y‖ₑ =
      (A ∆ B).indicator 1 y := by
    intro y
    by_cases hyA : y ∈ A <;> by_cases hyB : y ∈ B <;> simp [hyA, hyB, mem_symmDiff]
  simp_rw [hpt]
  rw [lintegral_indicator_one (hA.symmDiff hB), Measure.restrict_apply (hA.symmDiff hB)]

/-- `L¹_loc` convergence of indicators: `|(S_k ∆ F) ∩ K| → 0` for compact `K`. -/
theorem tendsto_volume_symmDiff_inter {ι : Type*} {l : Filter ι} {S : ι → Set (Rn n)}
    (hS : ∀ k, MeasurableSet (S k)) {F : Set (Rn n)} (hF : MeasurableSet F)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (S k).indicator (1 : Rn n → ℝ)) (F.indicator 1)
      l)
    {K : Set (Rn n)} (hK : IsCompact K) :
    Tendsto (fun k ↦ volume (S k ∆ F ∩ K)) l (𝓝 0) := by
  have := hconv K (subset_univ _) hK
  simp_rw [eLpNorm_indicator_sub_indicator (hS _) hF] at this
  exact this

/-- Lower bounds on `|B ∩ S_k|` pass to the `L¹_loc` limit. -/
theorem le_volume_inter_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {S : ι → Set (Rn n)}
    (hS : ∀ k, MeasurableSet (S k)) {F : Set (Rn n)} (hF : MeasurableSet F)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (S k).indicator (1 : Rn n → ℝ)) (F.indicator 1)
      l)
    {B K : Set (Rn n)} (hK : IsCompact K) (hBK : B ⊆ K) {a : ℝ≥0∞}
    (ha : ∀ᶠ k in l, a ≤ volume (B ∩ S k)) : a ≤ volume (B ∩ F) := by
  have hlim : Tendsto (fun k ↦ volume (B ∩ F) + volume (S k ∆ F ∩ K)) l
      (𝓝 (volume (B ∩ F))) := by
    simpa using tendsto_const_nhds.add (tendsto_volume_symmDiff_inter hS hF hconv hK)
  refine ge_of_tendsto hlim ?_
  filter_upwards [ha] with k hk
  refine hk.trans ((measure_mono ?_).trans (measure_union_le _ _))
  rintro y ⟨hyB, hyS⟩
  by_cases hyF : y ∈ F
  · exact Or.inl ⟨hyB, hyF⟩
  · exact Or.inr ⟨Or.inl ⟨hyS, hyF⟩, hBK hyB⟩

/-- Lower bounds on `|B ∖ S_k|` pass to the `L¹_loc` limit. -/
theorem le_volume_diff_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {S : ι → Set (Rn n)}
    (hS : ∀ k, MeasurableSet (S k)) {F : Set (Rn n)} (hF : MeasurableSet F)
    (hconv : TendstoLpLoc 1 volume univ (fun k ↦ (S k).indicator (1 : Rn n → ℝ)) (F.indicator 1)
      l)
    {B K : Set (Rn n)} (hK : IsCompact K) (hBK : B ⊆ K) {a : ℝ≥0∞}
    (ha : ∀ᶠ k in l, a ≤ volume (B \ S k)) : a ≤ volume (B \ F) := by
  have hlim : Tendsto (fun k ↦ volume (B \ F) + volume (S k ∆ F ∩ K)) l
      (𝓝 (volume (B \ F))) := by
    simpa using tendsto_const_nhds.add (tendsto_volume_symmDiff_inter hS hF hconv hK)
  refine ge_of_tendsto hlim ?_
  filter_upwards [ha] with k hk
  refine hk.trans ((measure_mono ?_).trans (measure_union_le _ _))
  rintro y ⟨hyB, hyS⟩
  by_cases hyF : y ∈ F
  · exact Or.inr ⟨Or.inr ⟨hyF, hyS⟩, hBK hyB⟩
  · exact Or.inl ⟨hyB, hyF⟩

end Indicator

/-! ### Claim #3 -/

section Claim3

/-- **EG Thm 5.13, Claim #3.** If `F` is a.e. `∅`, `ℝⁿ` or `{⟪y, v⟫ ≤ γ}` (Claim #2) and both `F`
and its complement have positive measure in every ball `B_ρ(0)`, then `F` is a.e.
`{⟪y, v⟫ ≤ 0}`. -/
theorem ae_eq_halfSpace_zero_of_measure_pos {F : Set (Rn n)} {v : Rn n} (hv : ‖v‖ = 1)
    (hF : F =ᵐ[volume] (∅ : Set (Rn n)) ∨ F =ᵐ[volume] (univ : Set (Rn n)) ∨
      ∃ γ : ℝ, F =ᵐ[volume] {y : Rn n | ⟪y, v⟫ ≤ γ})
    (hin : ∀ ρ, 0 < ρ → 0 < volume (ball (0 : Rn n) ρ ∩ F))
    (hout : ∀ ρ, 0 < ρ → 0 < volume (ball (0 : Rn n) ρ \ F)) :
    F =ᵐ[volume] {y : Rn n | ⟪y, v⟫ ≤ 0} := by
  have hinner : ∀ y : Rn n, |⟪y, v⟫| ≤ ‖y‖ := fun y ↦
    (abs_real_inner_le_norm y v).trans (by rw [hv, mul_one])
  rcases hF with hF | hF | ⟨γ, hF⟩
  · have := hin 1 one_pos
    rw [measure_congr ((EventuallyEqSet.refl _ (ball (0 : Rn n) 1)).inter hF), inter_empty,
      measure_empty] at this
    exact absurd this (lt_irrefl 0)
  · have := hout 1 one_pos
    rw [measure_congr ((EventuallyEqSet.refl _ (ball (0 : Rn n) 1)).diff hF), sdiff_univ,
      measure_empty] at this
    exact absurd this (lt_irrefl 0)
  rcases lt_trichotomy γ 0 with hγ | rfl | hγ
  · have := hin (-γ) (by linarith)
    rw [measure_congr ((EventuallyEqSet.refl _ (ball (0 : Rn n) (-γ))).inter hF)] at this
    have hempty : ball (0 : Rn n) (-γ) ∩ {y | ⟪y, v⟫ ≤ γ} = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_ball, dist_zero_right, mem_ofPred_eq, mem_empty_iff_false,
        iff_false, not_and, not_le]
      intro hy
      linarith [neg_abs_le ⟪y, v⟫, hinner y]
    rw [hempty, measure_empty] at this
    exact absurd this (lt_irrefl 0)
  · exact hF
  · have := hout γ hγ
    rw [measure_congr ((EventuallyEqSet.refl _ (ball (0 : Rn n) γ)).diff hF)] at this
    have hempty : ball (0 : Rn n) γ \ {y | ⟪y, v⟫ ≤ γ} = ∅ := by
      ext y
      simp only [Set.mem_sdiff, mem_ball, dist_zero_right, mem_ofPred_eq, mem_empty_iff_false,
        iff_false, not_and, not_not]
      intro hy
      linarith [le_abs_self ⟪y, v⟫, hinner y]
    rw [hempty, measure_empty] at this
    exact absurd this (lt_irrefl 0)

end Claim3

/-! ### The full blow-up limit (EG Thm 5.13) -/

section Limit

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- A lower volume bound `c rⁿ ≤ |B_r(x) ∩ S|` for `0 < r < r₀` rescales to
`c ρⁿ ≤ |B_ρ ∩ S_{x,s}|` for `sρ < r₀`. -/
theorem ofReal_le_volume_ball_inter_blowupSet {S : Set (Rn n)} {x : Rn n} {c r₀ : ℝ}
    (hlow : ∀ r, 0 < r → r < r₀ → ENNReal.ofReal (c * r ^ n) ≤ volume (ball x r ∩ S))
    {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) (hsρ : s * ρ < r₀) :
    ENNReal.ofReal (c * ρ ^ n) ≤ volume (ball 0 ρ ∩ blowupSet x s S) := by
  have h := hlow (s * ρ) (mul_pos hs hρ) hsρ
  rw [volume_ball_inter_eq x hs ρ S, show c * (s * ρ) ^ n = s ^ n * (c * ρ ^ n) by ring,
    ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (by positivity)).ne'
    ENNReal.ofReal_ne_top).1 h

/-- **Blow-up subsequences converge to the half-space** (EG Thm 5.13, steps 2–6). Under the
hypotheses of `HalfSpaceBlowUpStatement` and the density estimates `hup`, `hin`, `hout` (EG
Lemma 5.3 (iv), (i), (ii)), every sequence of scales `s_k → 0+` has a subsequence along which
`χ_{E_{x,s_k}}` converges in `L¹_loc(ℝⁿ)` to `χ_F` with `F` a.e. `{⟪y, v⟫ ≤ 0}`. -/
theorem exists_blowup_subseq_ae_eq_halfSpace (hn : 1 ≤ n) (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω) {v : Rn n}
    (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v))
    (hup : ∃ A r₀, 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    (hin : ∃ c r₀, 0 < c ∧ 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → ENNReal.ofReal (c * r ^ n) ≤ volume (ball x r ∩ E))
    (hout : ∃ c r₀, 0 < c ∧ 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → ENNReal.ofReal (c * r ^ n) ≤ volume (ball x r \ E))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : Set (Rn n), MeasurableSet F ∧
      TendstoLpLoc 1 volume univ (fun k ↦ (blowupSet x (s (φ k)) E).indicator (1 : Rn n → ℝ))
        (F.indicator 1) atTop ∧
      (∃ μF νF, IsGaussGreenPair univ F μF νF ∧ (∀ᵐ y ∂μF, νF y = v)) ∧
      F =ᵐ[volume] {y : Rn n | ⟪y, v⟫ ≤ 0} := by
  obtain ⟨φ, hφ, F, hF, hconv, hpair, hF3⟩ :=
    exists_blowup_subseq_halfSpace hn hΩ hE h hx hv hlim hup hs0 hs
  refine ⟨φ, hφ, F, hF, hconv, hpair, ae_eq_halfSpace_zero_of_measure_pos hv hF3 ?_ ?_⟩
  · obtain ⟨c, r₀, hc, hr₀, hin⟩ := hin
    intro ρ hρ
    refine (ENNReal.ofReal_pos.2 (by positivity : 0 < c * ρ ^ n)).trans_le ?_
    refine le_volume_inter_of_tendsto (fun k ↦ measurableSet_blowupSet hE x _) hF hconv
      (isCompact_closedBall 0 ρ) ball_subset_closedBall ?_
    have := (hs.comp hφ.tendsto_atTop).mul_const ρ
    rw [zero_mul] at this
    filter_upwards [this.eventually (gt_mem_nhds hr₀)] with k hk
    exact ofReal_le_volume_ball_inter_blowupSet hin (hs0 _) hρ hk
  · obtain ⟨c, r₀, hc, hr₀, hout⟩ := hout
    intro ρ hρ
    refine (ENNReal.ofReal_pos.2 (by positivity : 0 < c * ρ ^ n)).trans_le ?_
    refine le_volume_diff_of_tendsto (fun k ↦ measurableSet_blowupSet hE x _) hF hconv
      (isCompact_closedBall 0 ρ) ball_subset_closedBall ?_
    have := (hs.comp hφ.tendsto_atTop).mul_const ρ
    rw [zero_mul] at this
    filter_upwards [this.eventually (gt_mem_nhds hr₀)] with k hk
    have hout' : ∀ r, 0 < r → r < r₀ → ENNReal.ofReal (c * r ^ n) ≤ volume (ball x r ∩ Eᶜ) :=
      fun r hr hrr ↦ by rw [← sdiff_eq]; exact hout r hr hrr
    have := ofReal_le_volume_ball_inter_blowupSet hout' (hs0 (φ k)) hρ hk
    rw [sdiff_eq]
    exact this

theorem measurableSet_setOf_inner_lt (v : Rn n) : MeasurableSet {z : Rn n | ⟪z, v⟫ < 0} :=
  measurableSet_lt (continuous_id.inner continuous_const).measurable measurable_const

/-- The closed and open half-spaces agree a.e. -/
theorem halfSpace_ae_eq {v : Rn n} (hv : ‖v‖ = 1) :
    {z : Rn n | ⟪z, v⟫ ≤ 0} =ᵐ[volume] {z : Rn n | ⟪z, v⟫ < 0} := by
  have hv0 : v ≠ 0 := fun h0 ↦ by rw [h0, norm_zero] at hv; exact zero_ne_one hv
  refine ae_eq_set.2 ⟨measure_mono_null (fun z hz ↦ ?_) (volume_setOf_inner_eq hv0 0),
    measure_mono_null (fun z hz ↦ ?_) measure_empty⟩
  · simp only [Set.mem_sdiff, mem_ofPred_eq, not_lt] at hz
    exact le_antisymm hz.1 hz.2
  · simp only [Set.mem_sdiff, mem_ofPred_eq, not_le] at hz
    exact absurd hz.1.le (not_le.2 hz.2)

/-- **Sequential criterion on `𝓝[>] 0`.** If along every sequence of positive scales tending to
`0` some subsequence of `f` tends to `l'`, then `f → l'` as `r → 0+`. -/
theorem tendsto_nhdsGT_zero_of_forall_subseq {α : Type*} {f : ℝ → α} {l' : Filter α}
    (hf : ∀ s : ℕ → ℝ, (∀ k, 0 < s k) → Tendsto s atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, Tendsto (fun k ↦ f (s (φ k))) atTop l') :
    Tendsto f (𝓝[>] 0) l' := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨hns0, hnspos⟩ := tendsto_nhdsWithin_iff.1 hns
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnspos
  obtain ⟨φ, hφ⟩ := hf (fun k ↦ ns (k + N)) (fun k ↦ hN _ (Nat.le_add_left N k))
    (hns0.comp (tendsto_add_atTop_nat N))
  exact ⟨fun k ↦ φ k + N, hφ⟩

/-- The density estimates EG Lemma 5.3 (iv), (i), (ii) (`Perimeter/DensityEstimates`), in the shape
used in this file. -/
theorem IsGaussGreenPair.blowup_densityEstimates (hn : 2 ≤ n) (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n} (hx : x ∈ Ω)
    (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    (∃ A r₀, 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1))) ∧
    (∃ c r₀, 0 < c ∧ 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → ENNReal.ofReal (c * r ^ n) ≤ volume (ball x r ∩ E)) ∧
    (∃ c r₀, 0 < c ∧ 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → ENNReal.ofReal (c * r ^ n) ≤ volume (ball x r \ E)) := by
  obtain ⟨r₄, hr₄, h4⟩ := h.exists_forall_measure_ball_le (by omega) hΩ hE hx hpos hv hlim
  obtain ⟨r₁, hr₁, -, h1⟩ := h.exists_forall_volume_inter_ball_ge hn hΩ hE hx hpos hv hlim
  obtain ⟨r₂, hr₂, -, h2⟩ := h.exists_forall_volume_ball_diff_ge hn hΩ hE hx hpos hv hlim
  have hA := densityConstA₁_pos (n := n) (by omega)
  exact ⟨⟨_, r₄, hr₄, h4⟩, ⟨_, r₁, hA, hr₁, fun r hr hrr ↦ by rw [inter_comm]; exact h1 r hr hrr⟩,
    ⟨_, r₂, hA, hr₂, h2⟩⟩

/-- **EG Thm 5.13 (blow-up of the reduced boundary).** At a point of `∂*E` (in the Gauss–Green
pair form of `HalfSpaceBlowUpStatement`), `χ_{E_{x,r}} → χ_{{⟪z, v⟫ < 0}}` in `L¹_loc(ℝⁿ)` as
`r → 0+`. -/
theorem IsGaussGreenPair.tendsto_blowup_halfSpace (hn : 2 ≤ n) (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n} (hx : x ∈ Ω)
    (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    TendstoLpLoc 1 volume univ (fun r ↦ (blowupSet x r E).indicator (1 : Rn n → ℝ))
      ({z : Rn n | ⟪z, v⟫ < 0}.indicator 1) (𝓝[>] 0) := by
  obtain ⟨hup, hin, hout⟩ := h.blowup_densityEstimates hn hΩ hE hx hpos hv hlim
  intro K _ hK
  refine tendsto_nhdsGT_zero_of_forall_subseq fun s hs0 hs ↦ ?_
  obtain ⟨φ, -, F, hF, hconv, -, hFH⟩ :=
    exists_blowup_subseq_ae_eq_halfSpace (by omega) hΩ hE h hx hv hlim hup hin hout hs0 hs
  have hind : F.indicator (1 : Rn n → ℝ) =ᵐ[volume] {z : Rn n | ⟪z, v⟫ < 0}.indicator 1 :=
    indicator_ae_eq_of_ae_eq_set (hFH.trans (halfSpace_ae_eq hv))
  refine ⟨φ, (hconv K (subset_univ _) hK).congr fun k ↦ eLpNorm_congr_ae
    (ae_restrict_of_ae ?_)⟩
  filter_upwards [hind] with y hy
  simp only [Pi.sub_apply, hy]

end Limit

/-- **Blow-up at the reduced boundary** (EG Thm 5.13, in density form): at a point of `∂*E`, the
symmetric difference `E ∆ {⟪y - x, v⟫ < 0}` has density `0` at `x`. Balls are open; EG uses closed
balls, which have the same Lebesgue measure. The density estimates are EG Lemma 5.3
(`Perimeter/DensityEstimates`); `hpos` enters only through them. -/
theorem hasDensity_symmDiff_halfSpace : HalfSpaceBlowUpStatement n := by
  intro hn Ω E hΩ hE μ ν h x hx hpos v hv hlim
  rw [hasDensity_zero_iff_tendsto]
  have hT := tendsto_volume_symmDiff_inter (fun r ↦ measurableSet_blowupSet hE x r)
    (measurableSet_setOf_inner_lt v) (h.tendsto_blowup_halfSpace hn hΩ hE hx hpos hv hlim)
    (isCompact_closedBall (0 : Rn n) 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have h1 := volume_ball_inter_eq x hr 1 (E ∆ {y | ⟪y - x, v⟫ < 0})
  rw [mul_one, show blowupSet x r (E ∆ {y | ⟪y - x, v⟫ < 0}) =
      blowupSet x r E ∆ blowupSet x r {y | ⟪y - x, v⟫ < 0} from preimage_symmDiff _ _,
    blowupSet_halfSpace x hr v, inter_comm] at h1
  rw [h1, mul_comm, mul_div_assoc, ENNReal.div_self (ENNReal.ofReal_pos.2 (by positivity)).ne'
    ENNReal.ofReal_ne_top, mul_one, inter_comm]
  exact measure_mono (inter_subset_inter_right _ ball_subset_closedBall)

/-! ### EG Thm 5.14 (iii): the density of `μ` -/

section Mass

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- Along a blow-up subsequence (`exists_blowup_subseq_ae_eq_halfSpace`),
`μ_{x,s_k}(B_1) → ω_{n-1}` (EG Thm 5.14, step 2). The limit pair has
`μ_F(B_ρ) = TV(F; B_ρ) = TV(H⁻; B_ρ) = ω_{n-1} ρ^{n-1}`; squeeze `B_1` between `ContDiffBump`
cutoffs for `B_{1-η}` and `B_{1+2η}` and use `tendsto_blowup_integral_cutoff`. -/
theorem exists_subseq_tendsto_blowupMeasure_ball_one (hn : 2 ≤ n) (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω) {v : Rn n}
    (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v))
    (hup : ∃ A r₀, 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → μ (ball x r) ≤ ENNReal.ofReal (A * r ^ (n - 1)))
    (hin : ∃ c r₀, 0 < c ∧ 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → ENNReal.ofReal (c * r ^ n) ≤ volume (ball x r ∩ E))
    (hout : ∃ c r₀, 0 < c ∧ 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → ENNReal.ofReal (c * r ^ n) ≤ volume (ball x r \ E))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, Tendsto (fun k ↦ blowupMeasure μ x (s (φ k)) (ball 0 1)) atTop
      (𝓝 (ENNReal.ofReal (unitBallVolume (n - 1)))) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨φ, hφ, F, hF, hconv, ⟨μF, νF, hpF, -⟩, hFH⟩ :=
    exists_blowup_subseq_ae_eq_halfSpace hn1 hΩ hE h hx hv hlim hup hin hout hs0 hs
  refine ⟨φ, ?_⟩
  set wₙ := unitBallVolume (n - 1) with hw_def
  have hw : 0 < wₙ := unitBallVolume_pos _
  set t : ℕ → ℝ := fun k ↦ s (φ k) with ht_def
  have ht0 : ∀ k, 0 < t k := fun k ↦ hs0 _
  have ht : Tendsto t atTop (𝓝 0) := hs.comp hφ.tendsto_atTop
  set μk : ℕ → Measure (Rn n) := fun k ↦ blowupMeasure μ x (t k) with hμk_def
  have hpair : ∀ k, IsGaussGreenPair (blowupSet x (t k) Ω) (blowupSet x (t k) E) (μk k)
      (fun z ↦ ν (x + t k • z)) := fun k ↦ h.blowup' hn1 x (ht0 k)
  -- the mass of the limit pair on balls
  have hμF : ∀ ρ, 0 < ρ → μF (ball 0 ρ) = ENNReal.ofReal (wₙ * ρ ^ (n - 1)) := by
    intro ρ hρ
    rw [← hpF.totalVariationOn_indicator_eq hF isOpen_ball (subset_univ _),
      totalVariationOn_congr_ae (indicator_ae_eq_of_ae_eq_set hFH)]
    exact totalVariationOn_halfSpace_ball hn hv (by simp [GMT.hyperplane]) hρ.le
  have hμFr : ∀ ρ, 0 < ρ → μF.real (ball 0 ρ) = wₙ * ρ ^ (n - 1) := fun ρ hρ ↦ by
    rw [Measure.real, hμF ρ hρ, ENNReal.toReal_ofReal (by positivity)]
  -- finiteness of `μ_k` on balls, eventually
  have hfin : ∀ R, ∀ᶠ k in atTop, closedBall (0 : Rn n) R ⊆ blowupSet x (t k) Ω ∧
      μk k (ball 0 R) < ⊤ := fun R ↦ by
    filter_upwards [eventually_closedBall_subset_blowupSet hΩ hx ht0 ht R] with k hk
    exact ⟨hk, (measure_mono ball_subset_closedBall).trans_lt
      ((hpair k).lt_top_of_isCompact _ (isCompact_closedBall _ _) hk)⟩
  set m : ℕ → ℝ := fun k ↦ (μk k (ball 0 1)).toReal with hm_def
  have hcut := fun {R : ℝ} (hR : 0 < R) {ψ : Rn n → ℝ} (hψ : ContDiff ℝ 1 ψ)
      (hψc : HasCompactSupport ψ) (hψR : tsupport ψ ⊆ ball 0 R)
      (hψ01 : ∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) ↦
    tendsto_blowup_integral_cutoff hn1 hΩ hE h hx hv hlim hup ht0 ht hF hconv hpF hR hψ hψc hψR
      hψ01
  have hm : Tendsto m atTop (𝓝 wₙ) := by
    refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
    · -- lower bound, cutoff for `B_{1-η}` inside `B_1`
      have hg : Tendsto (fun η : ℝ ↦ wₙ * (1 - η) ^ (n - 1)) (𝓝[>] 0) (𝓝 wₙ) := by
        have : Continuous fun η : ℝ ↦ wₙ * (1 - η) ^ (n - 1) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨η, haη, hη⟩ := ((hg.eventually (lt_mem_nhds ha)).and
        (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
      let ψ : ContDiffBump (0 : Rn n) := ⟨1 - η, 1 - η / 2, by linarith [hη.2], by linarith [hη.1]⟩
      have hψR : tsupport ψ ⊆ ball 0 1 := by
        rw [ψ.tsupport_eq]
        exact closedBall_subset_ball (by change 1 - η / 2 < 1; linarith [hη.1])
      have hT := hcut one_pos ψ.contDiff ψ.hasCompactSupport hψR fun y ↦ ⟨ψ.nonneg, ψ.le_one⟩
      have hlow : wₙ * (1 - η) ^ (n - 1) ≤ ∫ y in ball 0 1, ψ y ∂μF := by
        have hρ : 0 < 1 - η := by linarith [hη.2]
        rw [← hμFr _ hρ, ← mul_one (μF.real _), ← smul_eq_mul, ← setIntegral_const,
          ← setIntegral_congr_fun measurableSet_ball (f := fun y ↦ ψ y) fun y hy ↦
            ψ.one_of_mem_closedBall (ball_subset_closedBall hy)]
        refine setIntegral_mono_set (hpF.integrable_of_continuous ψ.continuous
          ψ.hasCompactSupport (subset_univ _)).integrableOn
          (Eventually.of_forall fun y ↦ ψ.nonneg) (Eventually.of_forall ?_)
        exact ball_subset_ball (by linarith [hη.1])
      filter_upwards [hT.eventually (lt_mem_nhds (haη.trans_le hlow)), hfin 1] with k hk hkf
      refine hk.trans_le ?_
      have : IsFiniteMeasure ((μk k).restrict (ball 0 1)) := isFiniteMeasure_restrict.2 hkf.2.ne
      calc ∫ y in ball 0 1, ψ y ∂μk k ≤ ∫ _ in ball 0 1, (1 : ℝ) ∂μk k :=
            integral_mono_of_nonneg (Eventually.of_forall fun y ↦ ψ.nonneg) (integrable_const _)
              (Eventually.of_forall fun y ↦ ψ.le_one)
        _ = m k := by rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real]
    · -- upper bound, cutoff equal to `1` on `B_1`, inside `B_{1+2η}`
      have hg : Tendsto (fun η : ℝ ↦ wₙ * (1 + 2 * η) ^ (n - 1)) (𝓝[>] 0) (𝓝 wₙ) := by
        have : Continuous fun η : ℝ ↦ wₙ * (1 + 2 * η) ^ (n - 1) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨η, hbη, hη⟩ := ((hg.eventually (gt_mem_nhds hb)).and self_mem_nhdsWithin).exists
      have hη : (0 : ℝ) < η := hη
      set R : ℝ := 1 + 2 * η with hR_def
      have hR : 0 < R := by positivity
      let ψ : ContDiffBump (0 : Rn n) := ⟨1, 1 + η, one_pos, by linarith⟩
      have hψR : tsupport ψ ⊆ ball 0 R := by
        rw [ψ.tsupport_eq]
        exact closedBall_subset_ball (by change 1 + η < R; linarith)
      have hT := hcut hR ψ.contDiff ψ.hasCompactSupport hψR fun y ↦ ⟨ψ.nonneg, ψ.le_one⟩
      have hupF : ∫ y in ball 0 R, ψ y ∂μF ≤ wₙ * R ^ (n - 1) := by
        have : IsFiniteMeasure (μF.restrict (ball 0 R)) := isFiniteMeasure_restrict.2
          (by rw [hμF R hR]; exact ENNReal.ofReal_ne_top)
        calc ∫ y in ball 0 R, ψ y ∂μF ≤ ∫ _ in ball 0 R, (1 : ℝ) ∂μF :=
              integral_mono_of_nonneg (Eventually.of_forall fun y ↦ ψ.nonneg)
                (integrable_const _) (Eventually.of_forall fun y ↦ ψ.le_one)
          _ = wₙ * R ^ (n - 1) := by rw [setIntegral_const, smul_eq_mul, mul_one, hμFr R hR]
      filter_upwards [hT.eventually (gt_mem_nhds (hupF.trans_lt hbη)), hfin R] with k hk hkf
      refine lt_of_le_of_lt ?_ hk
      have hint : IntegrableOn ψ (ball 0 R) (μk k) :=
        ((hpair k).integrable_of_continuous ψ.continuous ψ.hasCompactSupport
          (hψR.trans (ball_subset_closedBall.trans hkf.1))).integrableOn
      calc m k = ∫ _ in ball 0 1, (1 : ℝ) ∂μk k := by
            rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real]
        _ = ∫ y in ball 0 1, ψ y ∂μk k :=
            setIntegral_congr_fun measurableSet_ball fun y hy ↦
              (ψ.one_of_mem_closedBall (ball_subset_closedBall hy)).symm
        _ ≤ ∫ y in ball 0 R, ψ y ∂μk k :=
            setIntegral_mono_set hint (Eventually.of_forall fun y ↦ ψ.nonneg)
              (Eventually.of_forall (ball_subset_ball (by linarith)))
  refine (ENNReal.tendsto_ofReal hm).congr' ?_
  filter_upwards [hfin 1] with k hk
  exact ENNReal.ofReal_toReal hk.2.ne

/-- **EG Thm 5.14 (iii)**. At a point of `∂*E` (in the Gauss–Green pair form of
`HalfSpaceBlowUpStatement`),
`μ(B_r(x)) / (ω_{n-1} r^{n-1}) → 1` as `r → 0+` (open balls, `ω_{n-1} = unitBallVolume (n - 1)`,
`ℝ≥0∞` ratio). -/
theorem IsGaussGreenPair.tendsto_measure_ball_div (hn : 2 ≤ n) {Ω E : Set (Rn n)}
    (hΩ : IsOpen Ω) (hE : MeasurableSet E) {μ : Measure (Rn n)} {ν : Rn n → Rn n}
    (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} (hx : x ∈ Ω)
    (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    Tendsto (fun r => μ (ball x r) / ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)))
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨hup, hin, hout⟩ := h.blowup_densityEstimates hn hΩ hE hx hpos hv hlim
  set wₙ := unitBallVolume (n - 1) with hw_def
  have hw : 0 < wₙ := unitBallVolume_pos _
  have hB : Tendsto (fun r ↦ blowupMeasure μ x r (ball 0 1)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal wₙ)) :=
    tendsto_nhdsGT_zero_of_forall_subseq fun s hs0 hs ↦
      exists_subseq_tendsto_blowupMeasure_ball_one hn hΩ hE h hx hv hlim hup hin hout hs0 hs
  have hw0 : ENNReal.ofReal wₙ ≠ 0 := (ENNReal.ofReal_pos.2 hw).ne'
  have hlim1 := ENNReal.Tendsto.div_const hB (Or.inr hw0)
  rw [ENNReal.div_self hw0 ENNReal.ofReal_ne_top] at hlim1
  refine hlim1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have ha0 : ENNReal.ofReal (r ^ (n - 1)) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rw [blowupMeasure_ball μ x hr, mul_one, ENNReal.ofReal_mul hw.le, mul_comm (ENNReal.ofReal wₙ),
    ← ENNReal.mul_div_mul_left _ _ ha0 ENNReal.ofReal_ne_top, ← mul_assoc,
    ENNReal.mul_inv_cancel ha0 ENNReal.ofReal_ne_top, one_mul]

end Mass

end GMTFoundations
