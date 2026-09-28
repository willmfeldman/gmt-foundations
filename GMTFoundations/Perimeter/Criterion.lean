/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Statements.Perimeter
public import GMTFoundations.Perimeter.CriterionClaims
public import GMTFoundations.Perimeter.CriterionLines
public import GMTFoundations.Perimeter.ReducedBoundary
public import GMTFoundations.Common.Divergence
public import GMTFoundations.Perimeter.Poincare
import Mathlib.Algebra.Order.Ring.Star

/-!
# Null essential boundary implies triviality

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

If `ℋ^{n-1}(∂ᵉE ∩ B) = 0` for a ball `B`, then `E` is a.e. empty or a.e. all of `B`. We prove this
through the null case of Federer's criterion for finite perimeter (EG Thm 5.23, steps 1–6 with
multiplicity `N ≡ 0`): the distributional gradient of `χ_E` vanishes in `B`, so `(0, 0)` is a
Gauss–Green pair for `E` in `B`, and the `L¹` form of the relative isoperimetric inequality then
forces `E` to be trivial in `B`. The proof has four steps:
1. a.e. line parallel to a coordinate axis misses `∂ᵉE ∩ B` (projection, `CriterionLines.lean`);
2. the sets `G(k)`, `H(k)` of EG step 2 and EG's **Claim #1** (EG step 3);
3. EG's **Claim #2** (EG step 5): on a.e. line the measure-theoretic interior `I` either
   contains or misses all of the line's points in `B`;
4. Fubini along lines: `∫_E ∂ᵢφ = 0` for every coordinate `i` (EG step 6).

## Main results

* `setIntegral_divergence_eq_zero_of_hausdorffN_essentialBoundary` (steps 1–4): if `E` is
  Lebesgue measurable, `U` is convex and `ℋ^{n-1}(∂ᵉE ∩ U) = 0`, then `∫_E div φ = 0` for every
  `φ ∈ C¹_c(U; ℝⁿ)`. So the distributional gradient of `χ_E` vanishes in `U`.
* `isGaussGreenPair_zero_of_hausdorffN_essentialBoundary`: equivalently `(0, 0)` is a Gauss–Green
  pair for `E` in `U`.
* `ae_trivial_of_hausdorffN_essentialBoundary_inter_ball_of`: the main statement, conditional
  on the implication "`Dχ_E = 0` in `B_r` ⇒ `E` trivial in `B_r`", passed as an explicit
  hypothesis.
* `ae_trivial_of_hausdorffN_essentialBoundary_inter_ball`: the statement
  `TrivialOfNullEssentialBoundaryStatement`, from the above, `totalVariationOn_indicator_eq_iSup`
  and `volume_inter_ball_eq_zero_or_of_totalVariationOn_eq_zero` (the `L¹` relative isoperimetric
  inequality).

## The sets of EG step 2

`lowDensitySet A c k` is the set of `x` with `|A ∩ B_ρ(x)| ≤ c ρⁿ` for `0 < ρ < 1/(k+1)`. EG's
`G(k)` is `lowDensitySet Eᶜ c k` and `H(k)` is `lowDensitySet E c k` (EG uses `O`, `I` in place of
`Eᶜ`, `E`, and `3/k`, `α(n-1)/3^{n+1}`; `|O ∩ E| = |I ∖ E| = 0` makes the choices equivalent up to
constants). They are increasing in `k`, closed (`isClosed_lowDensitySet`; EG assert this without
proof), disjoint for small `c`
(`disjoint_lowDensitySet`), and cover the density-`0` set of `A`
(`subset_iUnion_lowDensitySet`). EG's `G^±(k, m)`, `H^±(k, m)` are the points of these sets from
which the open ray of length `1/(l+1)` in direction `±eᵢ` stays in `O` (resp. `I`);
`volume_projCoord_rayPlus_eq_zero` and `volume_projCoord_rayMinus_eq_zero` are **Claim #1** for them
(via the abstract `volume_image_snd_eq_zero` of `CriterionClaims.lean`).

## Step 3, and convex domains in place of cubes

`ae_line_dichotomy` (EG **Claim #2**, via the abstract `exists_mem_Icc_not_mem_union`): for a.e.
line parallel to `eᵢ`, the measure-theoretic interior `I` either contains or misses all of the
line's points in `U`. We work directly on a **convex** `U` (e.g. the ball), whose line sections are
intervals. EG work on the cube `(-a, a)ⁿ`, which would force us to cover the ball by cubes and
glue with a partition of unity; but EG use the cube only because its lines have interval sections,
and every convex set has this property. EG state Claim #2 for one order of the interior and
exterior points on the line (`u < v`); both orders are proved here.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

@[expose] public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### The sets `G(k)`, `H(k)` of EG step 2 -/

/-- `x ∈ lowDensitySet A c k` iff `|A ∩ B_ρ(x)| ≤ c ρⁿ` for all `0 < ρ < 1/(k+1)`. EG's `G(k)` is
`lowDensitySet Eᶜ c k`, EG's `H(k)` is `lowDensitySet E c k`. -/
def lowDensitySet (A : Set (Rn n)) (c : ℝ≥0∞) (k : ℕ) : Set (Rn n) :=
  {x | ∀ ρ : ℝ, 0 < ρ → ρ < ((k : ℝ) + 1)⁻¹ →
    volume (A ∩ ball x ρ) ≤ c * ENNReal.ofReal (ρ ^ n)}

theorem lowDensitySet_mono (A : Set (Rn n)) (c : ℝ≥0∞) : Monotone (lowDensitySet A c) := by
  intro k k' hkk' x hx ρ hρ hρk
  refine hx ρ hρ (hρk.trans_le ?_)
  gcongr

theorem isClosed_lowDensitySet (A : Set (Rn n)) (c : ℝ≥0∞) (k : ℕ) :
    IsClosed (lowDensitySet A c k) := by
  refine isClosed_of_closure_subset fun x hx ρ hρ hρk => ?_
  obtain ⟨u, hu, hmono, hU⟩ := exists_seq_iUnion_closedBall_eq_ball x hρ
  have hAU : A ∩ ball x ρ = ⋃ j, A ∩ closedBall x (u j) := by rw [← inter_iUnion, hU]
  rw [hAU, Monotone.measure_iUnion fun i j hij => inter_subset_inter_right _ (hmono hij)]
  refine iSup_le fun j => ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ρ - u j) (by linarith [(hu j).2])
  refine (measure_mono (inter_subset_inter_right _ fun w hw => ?_)).trans (hy ρ hρ hρk)
  rw [mem_closedBall] at hw
  rw [mem_ball]
  calc dist w y ≤ dist w x + dist x y := dist_triangle _ _ _
    _ < ρ := by linarith

/-- Every density-`0` point of `A` lies in some `lowDensitySet A c k` (`c > 0`). -/
theorem subset_iUnion_lowDensitySet (A : Set (Rn n)) {c : ℝ≥0∞} (hc : c ≠ 0) :
    {x | HasDensity A x 0} ⊆ ⋃ k, lowDensitySet A c k := by
  intro x hx
  have h := ENNReal.tendsto_nhds_zero.1 (hasDensity_zero_iff_tendsto.1 hx) c
    (pos_iff_ne_zero.2 hc)
  obtain ⟨δ, hδ, hδU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (mem_Ioi.1 hδ)
  refine mem_iUnion.2 ⟨k, fun ρ hρ hρk => ?_⟩
  have := hδU ⟨hρ, hρk.trans (by simpa [one_div] using hk)⟩
  simp only [mem_setOf_eq] at this
  rwa [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 (pow_pos hρ n)).ne' ENNReal.ofReal_ne_top] at this

/-- `G(k) ∩ H(k) = ∅` when `2c < |B_1|`. -/
theorem disjoint_lowDensitySet (A : Set (Rn n)) {c : ℝ≥0∞}
    (hc : 2 * c < volume (ball (0 : Rn n) 1)) (k : ℕ) :
    Disjoint (lowDensitySet A c k) (lowDensitySet Aᶜ c k) := by
  refine Set.disjoint_left.2 fun x h1 h2 => ?_
  set ρ : ℝ := ((k : ℝ) + 1)⁻¹ / 2
  have hk : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
  have hρ : 0 < ρ := by positivity
  have hρk : ρ < ((k : ℝ) + 1)⁻¹ := half_lt_self hk
  have hball : volume (ball x ρ) = ENNReal.ofReal (ρ ^ n) * volume (ball (0 : Rn n) 1) := by
    rw [Measure.addHaar_ball_of_pos volume x hρ, finrank_euclideanSpace_fin]
  have hle : volume (ball x ρ) ≤ ENNReal.ofReal (ρ ^ n) * (2 * c) :=
    calc volume (ball x ρ) ≤ volume (ball x ρ ∩ A) + volume (ball x ρ \ A) :=
          measure_le_inter_add_diff _ _ _
      _ = volume (A ∩ ball x ρ) + volume (Aᶜ ∩ ball x ρ) := by
          rw [inter_comm, diff_eq, inter_comm (ball x ρ)]
      _ ≤ c * ENNReal.ofReal (ρ ^ n) + c * ENNReal.ofReal (ρ ^ n) :=
          add_le_add (h1 ρ hρ hρk) (h2 ρ hρ hρk)
      _ = ENNReal.ofReal (ρ ^ n) * (2 * c) := by ring
  rw [hball, ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (pow_pos hρ n)).ne'
    ENNReal.ofReal_ne_top] at hle
  exact absurd hc (not_lt.2 hle)

/-- `|{density 0 of A} ∩ A| = 0` (EG Lemma 5.9 (ii), via
`volume_diff_union_diff_setOf_hasDensity_one`). -/
theorem volume_setOf_hasDensity_zero_inter {A : Set (Rn n)} (hA : NullMeasurableSet A volume) :
    volume ({x | HasDensity A x 0} ∩ A) = 0 := by
  refine measure_mono_null (fun x hx => ?_) (volume_diff_union_diff_setOf_hasDensity_one hA)
  refine Or.inl ⟨hx.2, fun h1 => ?_⟩
  exact zero_ne_one (tendsto_nhds_unique hx.1 h1)

/-! ### Claim #1 for `G^±(k, l)` and `H^±(k, l)` -/

section Claim1

variable {m : ℕ}

/-- The box `[xᵢ - r, xᵢ + r] × B̄_{2r}(P_i x)` (split coordinates) around a point of
`lowDensitySet Aᶜ c k` meets the density-`0` set of `A` in measure `≤ c ((2m+2) r)^{m+1}`. -/
private theorem volume_box_le {A : Set (Rn (m + 1))} (hA : NullMeasurableSet A volume)
    (i : Fin (m + 1)) {c : ℝ≥0∞} {k : ℕ} {x : Rn (m + 1)} (hx : x ∈ lowDensitySet Aᶜ c k)
    {r : ℝ} (hr : 0 < r) (hrk : (2 * m + 2) * r < ((k : ℝ) + 1)⁻¹) :
    volume ((splitCoord i).symm ⁻¹' {y | HasDensity A y 0} ∩
        Icc ((splitCoord i x).1 - r) ((splitCoord i x).1 + r) ×ˢ
          closedBall (splitCoord i x).2 (2 * r)) ≤
      c * ENNReal.ofReal ((2 * m + 2 : ℝ) ^ (m + 1)) * ENNReal.ofReal r ^ (m + 1) := by
  set Φ := splitCoord i
  set Z := {y | HasDensity A y 0}
  set ρ := (2 * m + 2 : ℝ) * r
  have hρ : 0 < ρ := by positivity
  rw [← (measurePreserving_splitCoord i).measure_preimage_equiv]
  have hsub : Φ ⁻¹' (Φ.symm ⁻¹' Z ∩ Icc ((Φ x).1 - r) ((Φ x).1 + r) ×ˢ closedBall (Φ x).2 (2 * r))
      ⊆ Z ∩ ball x ρ := by
    intro y hy
    obtain ⟨hyZ, hy12, hy3⟩ := hy
    rw [mem_preimage, MeasurableEquiv.symm_apply_apply] at hyZ
    simp only [mem_Icc, mem_closedBall, Φ, splitCoord_apply] at hy12 hy3
    have hy : y ∈ Z ∧ (x i - r ≤ y i ∧ y i ≤ x i + r) ∧
        dist (projCoord i y) (projCoord i x) ≤ 2 * r := ⟨hyZ, hy12, hy3⟩
    refine ⟨hy.1, ?_⟩
    rw [mem_ball, dist_eq_norm]
    have h1 : |(y - x) i| ≤ r := by
      rw [PiLp.sub_apply, abs_le]
      constructor <;> linarith [hy.2.1.1, hy.2.1.2]
    have h2 : ‖projCoord i (y - x)‖ ≤ 2 * r := by
      have : projCoord i (y - x) = projCoord i y - projCoord i x := by
        funext j
        simp [projCoord]
      rw [this, ← dist_eq_norm]
      exact hy.2.2
    calc ‖y - x‖ ≤ |(y - x) i| + m * ‖projCoord i (y - x)‖ :=
          norm_le_abs_add_mul_norm_projCoord i _
      _ ≤ r + m * (2 * r) := by gcongr
      _ < ρ := by simp only [ρ]; linarith
  refine (measure_mono hsub).trans ?_
  have hsplit : Z ∩ ball x ρ ⊆ (Aᶜ ∩ ball x ρ) ∪ (Z ∩ A) := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inr ⟨hy.1, hyA⟩
    · exact Or.inl ⟨hyA, hy.2⟩
  calc volume (Z ∩ ball x ρ) ≤ volume (Aᶜ ∩ ball x ρ) + volume (Z ∩ A) :=
        (measure_mono hsplit).trans (measure_union_le _ _)
    _ = volume (Aᶜ ∩ ball x ρ) := by rw [volume_setOf_hasDensity_zero_inter hA, add_zero]
    _ ≤ c * ENNReal.ofReal (ρ ^ (m + 1)) := by
        have := hx ρ hρ hrk
        simpa using this
    _ = c * ENNReal.ofReal ((2 * m + 2 : ℝ) ^ (m + 1)) * ENNReal.ofReal r ^ (m + 1) := by
        rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr.le, mul_assoc]

/-- EG Thm 5.23 **Claim #1** for `G⁺(k, l)` (`A = E`) and `H⁺(k, l)` (`A = Eᶜ`): the points of
`lowDensitySet Aᶜ c k` from which the open ray of length `ℓ` in direction `+eᵢ` stays in the
density-`0` set of `A` project to an `ℒ^m`-null set. -/
theorem volume_projCoord_rayPlus_eq_zero {A : Set (Rn (m + 1))} (hA : NullMeasurableSet A volume)
    (i : Fin (m + 1)) {c : ℝ≥0∞}
    (hc : 4 * (c * ENNReal.ofReal ((2 * m + 2 : ℝ) ^ (m + 1))) ≤ 2 ^ m) (k : ℕ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    volume (projCoord i '' {x | x ∈ lowDensitySet Aᶜ c k ∧ ∀ s, 0 < s → s < ℓ →
      x + s • EuclideanSpace.single i 1 ∈ {y | HasDensity A y 0}}) = 0 := by
  set S := {x | x ∈ lowDensitySet Aᶜ c k ∧ ∀ s, 0 < s → s < ℓ →
      x + s • EuclideanSpace.single i 1 ∈ {y | HasDensity A y 0}}
  set Φ := splitCoord i
  set δ := min (ℓ / 2) (((k : ℝ) + 1)⁻¹ / (2 * m + 2))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have himg : projCoord i '' S = Prod.snd '' (Φ '' S) := by rw [image_image]; rfl
  rw [himg]
  refine volume_image_snd_eq_zero (O := Φ.symm ⁻¹' {y | HasDensity A y 0}) hδ hc ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ s hs hs'
    have hsℓ : s < ℓ := by linarith [min_le_left (ℓ / 2) (((k : ℝ) + 1)⁻¹ / (2 * m + 2))]
    have := hx.2 s hs hsℓ
    rw [mem_preimage, ← splitCoord_add_smul_single, MeasurableEquiv.symm_apply_apply]
    exact this
  · rintro _ ⟨x, hx, rfl⟩ r hr hrδ
    refine volume_box_le hA i hx.1 hr ?_
    have := hrδ.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity), mul_comm] at this

/-- EG Thm 5.23 **Claim #1** for `G⁻(k, l)` (`A = E`) and `H⁻(k, l)` (`A = Eᶜ`): the reflected
version of `volume_projCoord_rayPlus_eq_zero`, with rays in direction `-eᵢ`. -/
theorem volume_projCoord_rayMinus_eq_zero {A : Set (Rn (m + 1))} (hA : NullMeasurableSet A volume)
    (i : Fin (m + 1)) {c : ℝ≥0∞}
    (hc : 4 * (c * ENNReal.ofReal ((2 * m + 2 : ℝ) ^ (m + 1))) ≤ 2 ^ m) (k : ℕ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    volume (projCoord i '' {x | x ∈ lowDensitySet Aᶜ c k ∧ ∀ s, 0 < s → s < ℓ →
      x - s • EuclideanSpace.single i 1 ∈ {y | HasDensity A y 0}}) = 0 := by
  set S := {x | x ∈ lowDensitySet Aᶜ c k ∧ ∀ s, 0 < s → s < ℓ →
      x - s • EuclideanSpace.single i 1 ∈ {y | HasDensity A y 0}}
  set Φ := splitCoord i
  set δ := min (ℓ / 2) (((k : ℝ) + 1)⁻¹ / (2 * m + 2))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have himg : projCoord i '' S = Prod.snd '' (Φ '' S) := by rw [image_image]; rfl
  rw [himg]
  refine volume_image_snd_eq_zero' (O := Φ.symm ⁻¹' {y | HasDensity A y 0}) hδ hc ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ s hs hs'
    have hsℓ : s < ℓ := by linarith [min_le_left (ℓ / 2) (((k : ℝ) + 1)⁻¹ / (2 * m + 2))]
    have := hx.2 s hs hsℓ
    rw [sub_eq_add_neg, ← neg_smul] at this
    rw [mem_preimage, sub_eq_add_neg, ← splitCoord_add_smul_single,
      MeasurableEquiv.symm_apply_apply]
    exact this
  · rintro _ ⟨x, hx, rfl⟩ r hr hrδ
    refine volume_box_le hA i hx.1 hr ?_
    have := hrδ.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity), mul_comm] at this

/-- The constants: some `c > 0` makes `G(k) ∩ H(k) = ∅` and satisfies Claim #1's bound. -/
theorem exists_criterion_const (m : ℕ) : ∃ c : ℝ≥0∞, c ≠ 0 ∧
    2 * c < volume (ball (0 : Rn (m + 1)) 1) ∧
    4 * (c * ENNReal.ofReal ((2 * m + 2 : ℝ) ^ (m + 1))) ≤ 2 ^ m := by
  set ω := volume (ball (0 : Rn (m + 1)) 1)
  have hω0 : ω ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hωt : ω ≠ ∞ := measure_ball_lt_top.ne
  set K := ENNReal.ofReal ((2 * m + 2 : ℝ) ^ (m + 1))
  have hK0 : K ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hKt : K ≠ ∞ := ENNReal.ofReal_ne_top
  have h4K0 : 4 * K ≠ 0 := mul_ne_zero (by norm_num) hK0
  have h4Kt : 4 * K ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hKt
  refine ⟨min (ω / 4) (2 ^ m / (4 * K)), ?_, ?_, ?_⟩
  · refine (lt_min ?_ ?_).ne'
    · exact ENNReal.div_pos hω0 (by norm_num)
    · exact ENNReal.div_pos (by simp) h4Kt
  · have h4 : ω / 4 ≠ 0 := (ENNReal.div_pos hω0 (by norm_num)).ne'
    have h4t : ω / 4 ≠ ∞ := ENNReal.div_ne_top hωt (by norm_num)
    calc 2 * min (ω / 4) (2 ^ m / (4 * K)) ≤ 2 * (ω / 4) := by gcongr; exact min_le_left _ _
      _ < 4 * (ω / 4) := by
          rw [ENNReal.mul_lt_mul_iff_left h4 h4t]
          norm_num
      _ = ω := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  · calc 4 * (min (ω / 4) (2 ^ m / (4 * K)) * K) = min (ω / 4) (2 ^ m / (4 * K)) * (4 * K) := by
          ring
      _ ≤ 2 ^ m / (4 * K) * (4 * K) := by gcongr; exact min_le_right _ _
      _ = 2 ^ m := ENNReal.div_mul_cancel h4K0 h4Kt

end Claim1

/-! ### Step 3: EG Claim #2 on a.e. line -/

section Claim2

variable {m : ℕ}

/-- **Step 3** (EG Thm 5.23 Claim #2, null case). Let `E` be measurable and `U` convex with
`ℋ^m(∂ᵉE ∩ U) = 0` in `ℝ^{m+1}`. For a.e. `z ∈ ℝ^m`, the line `{P_i = z}` meets `U` either only
at points of density `1` of `E` or only at points where `E` does not have density `1`. -/
theorem ae_line_dichotomy {E : Set (Rn (m + 1))} (hE : NullMeasurableSet E volume)
    {U : Set (Rn (m + 1))} (hU : Convex ℝ U)
    (h : hausdorffN (m + 1) m (essentialBoundary E ∩ U) = 0) (i : Fin (m + 1)) :
    ∀ᵐ z ∂(volume : Measure (Fin m → ℝ)),
      (∀ t, (splitCoord i).symm (t, z) ∈ U → HasDensity E ((splitCoord i).symm (t, z)) 1) ∨
      (∀ t, (splitCoord i).symm (t, z) ∈ U → ¬ HasDensity E ((splitCoord i).symm (t, z)) 1) := by
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_criterion_const m
  set e : Rn (m + 1) := EuclideanSpace.single i 1
  set ZE := {y : Rn (m + 1) | HasDensity E y 0}
  set ZC := {y : Rn (m + 1) | HasDensity Eᶜ y 0}
  set ℓ : ℕ → ℝ := fun l => ((l : ℝ) + 1)⁻¹
  -- EG's `G^±(k, l)` and `H^±(k, l)`
  set Gp := fun k l => {x | x ∈ lowDensitySet Eᶜ c k ∧ ∀ s, 0 < s → s < ℓ l → x + s • e ∈ ZE}
  set Gm := fun k l => {x | x ∈ lowDensitySet Eᶜ c k ∧ ∀ s, 0 < s → s < ℓ l → x - s • e ∈ ZE}
  set Hp := fun k l => {x | x ∈ lowDensitySet Eᶜᶜ c k ∧ ∀ s, 0 < s → s < ℓ l → x + s • e ∈ ZC}
  set Hm := fun k l => {x | x ∈ lowDensitySet Eᶜᶜ c k ∧ ∀ s, 0 < s → s < ℓ l → x - s • e ∈ ZC}
  set N := projCoord i '' (essentialBoundary E ∩ U) ∪ ⋃ k, ⋃ l,
    (projCoord i '' Gp k l ∪ projCoord i '' Gm k l ∪ projCoord i '' Hp k l ∪
      projCoord i '' Hm k l)
  have hℓ : ∀ l, 0 < ℓ l := fun l => by positivity
  have hN : volume N = 0 := by
    refine measure_union_null (volume_projCoord_image_eq_zero i h)
      (measure_iUnion_null fun k => measure_iUnion_null fun l => ?_)
    refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_
    · exact volume_projCoord_rayPlus_eq_zero hE i hc2 k (hℓ l)
    · exact volume_projCoord_rayMinus_eq_zero hE i hc2 k (hℓ l)
    · exact volume_projCoord_rayPlus_eq_zero hE.compl i hc2 k (hℓ l)
    · exact volume_projCoord_rayMinus_eq_zero hE.compl i hc2 k (hℓ l)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with z hz
  simp only [N, mem_union, mem_iUnion, not_or, not_exists] at hz
  obtain ⟨hzB, hzR⟩ := hz
  -- the line through `z`
  set L : ℝ → Rn (m + 1) := fun t => (splitCoord i).symm (t, z)
  have hL : ∀ t, L t = L 0 + t • e := fun t => splitCoord_symm_eq_add_smul i t z
  have hLadd : ∀ t s, L (t + s) = L t + s • e := fun t s => by
    rw [hL (t + s), hL t, add_smul, add_assoc]
  have hLsub : ∀ t s, L (t - s) = L t - s • e := fun t s => by
    rw [hL (t - s), hL t, sub_smul, add_sub_assoc]
  have hLproj : ∀ t, projCoord i (L t) = z := fun t => projCoord_splitCoord_symm i t z
  have hLc : Continuous L := by
    rw [show L = fun t => L 0 + t • e from funext hL]
    fun_prop
  have hdens1 : ∀ y, HasDensity E y 1 ↔ y ∈ ZC := fun y => (hasDensity_compl_zero_iff hE).symm
  -- the line meets `∂ᵉE ∩ U` nowhere
  have hnoB : ∀ t, L t ∈ U → L t ∈ ZE ∨ L t ∈ ZC := by
    intro t htU
    by_contra hcon
    rw [not_or] at hcon
    refine hzB ⟨L t, ⟨⟨hcon.1, fun h1 => hcon.2 ((hdens1 _).1 h1)⟩, htU⟩, hLproj t⟩
  -- the traces of `G(k)`, `H(k)` on the line
  set Iz := {t | L t ∈ ZC}
  set Oz := {t | L t ∈ ZE}
  set Gz := fun k => L ⁻¹' lowDensitySet Eᶜ c k
  set Hz := fun k => L ⁻¹' lowDensitySet E c k
  have hGm : Monotone Gz := fun k k' hkk' => preimage_mono (lowDensitySet_mono _ c hkk')
  have hHm : Monotone Hz := fun k k' hkk' => preimage_mono (lowDensitySet_mono _ c hkk')
  have hGc : ∀ k, IsClosed (Gz k) := fun k => (isClosed_lowDensitySet _ c k).preimage hLc
  have hHc : ∀ k, IsClosed (Hz k) := fun k => (isClosed_lowDensitySet _ c k).preimage hLc
  have hGH : ∀ k, Disjoint (Gz k) (Hz k) := fun k =>
    ((disjoint_lowDensitySet E hc1 k).symm).preimage L
  have hIG : Iz ⊆ ⋃ k, Gz k := fun t ht => by
    simpa [Gz] using subset_iUnion_lowDensitySet Eᶜ hc0 ht
  have hOH : Oz ⊆ ⋃ k, Hz k := fun t ht => by
    simpa [Hz] using subset_iUnion_lowDensitySet E hc0 ht
  -- choose `l` with `1/(l+1) < ε`
  have hℓε : ∀ ε > 0, ∃ l, ℓ l < ε := fun ε hε => by
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt hε
    exact ⟨l, by simpa [ℓ, one_div] using hl⟩
  -- the four accumulation properties (the line avoids `G^±`, `H^±`)
  have hGr : ∀ k, ∀ t ∈ Gz k, ∀ ε > 0, ∃ y ∈ Ioo t (t + ε), y ∉ Oz := by
    intro k t ht ε hε
    obtain ⟨l, hl⟩ := hℓε ε hε
    have hnot : L t ∉ Gp k l := fun hmem => (hzR k l).1.1.1 ⟨L t, hmem, hLproj t⟩
    simp only [Gp, mem_setOf_eq, not_and, not_forall] at hnot
    obtain ⟨s, hs, hsl, hsO⟩ := hnot ht
    exact ⟨t + s, ⟨by linarith, by linarith⟩, by simpa [Oz, hLadd] using hsO⟩
  have hGl : ∀ k, ∀ t ∈ Gz k, ∀ ε > 0, ∃ y ∈ Ioo (t - ε) t, y ∉ Oz := by
    intro k t ht ε hε
    obtain ⟨l, hl⟩ := hℓε ε hε
    have hnot : L t ∉ Gm k l := fun hmem => (hzR k l).1.1.2 ⟨L t, hmem, hLproj t⟩
    simp only [Gm, mem_setOf_eq, not_and, not_forall] at hnot
    obtain ⟨s, hs, hsl, hsO⟩ := hnot ht
    exact ⟨t - s, ⟨by linarith, by linarith⟩, by simpa [Oz, hLsub] using hsO⟩
  have hHr : ∀ k, ∀ t ∈ Hz k, ∀ ε > 0, ∃ y ∈ Ioo t (t + ε), y ∉ Iz := by
    intro k t ht ε hε
    obtain ⟨l, hl⟩ := hℓε ε hε
    have hnot : L t ∉ Hp k l := fun hmem => (hzR k l).1.2 ⟨L t, hmem, hLproj t⟩
    simp only [Hp, compl_compl, mem_setOf_eq, not_and, not_forall] at hnot
    obtain ⟨s, hs, hsl, hsI⟩ := hnot ht
    exact ⟨t + s, ⟨by linarith, by linarith⟩, by simpa [Iz, hLadd] using hsI⟩
  have hHl : ∀ k, ∀ t ∈ Hz k, ∀ ε > 0, ∃ y ∈ Ioo (t - ε) t, y ∉ Iz := by
    intro k t ht ε hε
    obtain ⟨l, hl⟩ := hℓε ε hε
    have hnot : L t ∉ Hm k l := fun hmem => (hzR k l).2 ⟨L t, hmem, hLproj t⟩
    simp only [Hm, compl_compl, mem_setOf_eq, not_and, not_forall] at hnot
    obtain ⟨s, hs, hsl, hsI⟩ := hnot ht
    exact ⟨t - s, ⟨by linarith, by linarith⟩, by simpa [Iz, hLsub] using hsI⟩
  -- `U` is an interval on the line
  have hUline : ∀ a b, L a ∈ U → L b ∈ U → Icc a b ⊆ L ⁻¹' U := by
    intro a b ha hb
    set f : ℝ →ᵃ[ℝ] Rn (m + 1) := AffineMap.lineMap (L 0) (L 0 + e)
    have hf : ∀ t, f t = L t := fun t => by
      rw [AffineMap.lineMap_apply, hL t, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left]
      exact add_comm _ _
    have hpre : L ⁻¹' U = f ⁻¹' U := by
      ext t
      simp [hf]
    rw [hpre]
    exact ((hU.affine_preimage f).ordConnected).out (by rw [mem_preimage, hf]; exact ha)
      (by rw [mem_preimage, hf]; exact hb)
  -- conclusion
  by_contra hcon
  simp only [not_or, not_forall, not_not] at hcon
  obtain ⟨⟨t₁, ht₁U, ht₁⟩, ⟨t₂, ht₂U, ht₂⟩⟩ := hcon
  rw [hdens1] at ht₂ ht₁
  have ht₁O : t₁ ∈ Oz := (hnoB t₁ ht₁U).resolve_right ht₁
  have hfinish : ∀ a b, L a ∈ U → L b ∈ U → ∀ t ∈ Icc a b, t ∉ Iz ∪ Oz → False := by
    intro a b ha hb t ht htIO
    rcases hnoB t (hUline a b ha hb ht) with h' | h'
    · exact htIO (Or.inr h')
    · exact htIO (Or.inl h')
  rcases lt_trichotomy t₂ t₁ with hlt | heq | hgt
  · obtain ⟨t, ht, htIO⟩ := exists_mem_Icc_not_mem_union hGm hHm hGc hHc hGH hIG hOH hGr hHl
      hlt ht₂ ht₁O
    exact hfinish t₂ t₁ ht₂U ht₁U t ht htIO
  · subst heq
    exact ht₁ ht₂
  · obtain ⟨t, ht, htIO⟩ := exists_mem_Icc_not_mem_union hHm hGm hHc hGc
      (fun k => (hGH k).symm) hOH hIG hHr hGl hgt ht₁O ht₂
    exact hfinish t₁ t₂ ht₁U ht₂U t ht (by rwa [union_comm])

end Claim2

/-! ### Step 4: `Dχ_E = 0` in `U` -/

/-- **Steps 1–4** (EG Thm 5.23 with `N ≡ 0`). If `E` is Lebesgue measurable, `U` is
convex and `ℋ^{n-1}(∂ᵉE ∩ U) = 0`, then `∫_E div φ = 0` for every `φ ∈ C¹_c(U; ℝⁿ)`. -/
theorem setIntegral_divergence_eq_zero_of_hausdorffN_essentialBoundary (hn : 1 ≤ n)
    {E : Set (Rn n)} (hE : NullMeasurableSet E volume) {U : Set (Rn n)} (hU : Convex ℝ U)
    (h : hausdorffN n (n - 1) (essentialBoundary E ∩ U) = 0) {φ : Rn n → Rn n}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    ∫ x in E, divergence φ x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  set I := {x : Rn (m + 1) | HasDensity E x 1}
  have hI : MeasurableSet I := measurableSet_setOf_hasDensity_one E
  have hEI : E =ᵐ[volume] I := by
    have := volume_diff_union_diff_setOf_hasDensity_one hE
    rw [measure_union_null_iff] at this
    exact ae_eq_set.2 this
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  -- the coordinate functions
  have hgi : ∀ i, ContDiff ℝ 1 fun y => φ y i := fun i =>
    (EuclideanSpace.proj i : Rn (m + 1) →L[ℝ] ℝ).contDiff.comp hφ
  have hgc : ∀ i, HasCompactSupport fun y => φ y i := fun i =>
    hφc.comp_left (g := fun v : Rn (m + 1) => v i) (by simp)
  have hgU : ∀ i, tsupport (fun y => φ y i) ⊆ U := fun i =>
    (tsupport_comp_subset (g := fun v : Rn (m + 1) => v i) (by simp) φ).trans hφU
  have hint : ∀ i, Integrable fun x => fderiv ℝ (fun y => φ y i) x (EuclideanSpace.single i 1) :=
    fun i => (((hgi i).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport
      (((hgc i).fderiv ℝ).comp_left (g := fun T : Rn (m + 1) →L[ℝ] ℝ =>
        T (EuclideanSpace.single i 1)) (by simp))
  rw [setIntegral_congr_fun₀ hE (fun x _ => divergence_eq_sum_fderiv_coord (hdiff x)),
    integral_finsetSum _ fun i _ => (hint i).integrableOn]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [setIntegral_congr_set hEI]
  refine setIntegral_fderiv_single_eq_zero i hI (hgi i) (hgc i) ?_
  filter_upwards [ae_line_dichotomy hE hU h i] with z hz
  rcases hz with hin | hout
  · exact Or.inl fun t ht => hin t (hgU i ht)
  · exact Or.inr fun t ht => hout t (hgU i ht)

/-- `(0, 0)` is a Gauss–Green pair for `E` in `U` when `ℋ^{n-1}(∂ᵉE ∩ U) = 0` and `U` is convex:
`E` has locally finite perimeter in `U` with zero Gauss–Green measure. -/
theorem isGaussGreenPair_zero_of_hausdorffN_essentialBoundary (hn : 1 ≤ n) {E : Set (Rn n)}
    (hE : NullMeasurableSet E volume) {U : Set (Rn n)} (hU : Convex ℝ U)
    (h : hausdorffN n (n - 1) (essentialBoundary E ∩ U) = 0) :
    IsGaussGreenPair U E 0 0 where
  measure_compl := rfl
  lt_top_of_isCompact _ _ _ := by simp
  measurable_normal := measurable_const
  norm_normal := by simp
  integral_divergence φ hφ := by
    rw [setIntegral_divergence_eq_zero_of_hausdorffN_essentialBoundary hn hE hU h
      (hφ.1.of_le (by simp)) hφ.2.1 hφ.2.2]
    simp

/-- **Null essential boundary implies triviality, conditional form.** If `Dχ_E = 0` in a ball
forces `E` to be a.e. empty or a.e. full there ("`TV(E; B_r) = 0` ⇒ trivial", passed as the
hypothesis `hPoincare`), then `TrivialOfNullEssentialBoundaryStatement` holds. -/
theorem ae_trivial_of_hausdorffN_essentialBoundary_inter_ball_of
    (hPoincare : ∀ (_ : 2 ≤ n) {E : Set (Rn n)} (_ : MeasurableSet E) {c : Rn n} {r : ℝ},
      (∀ φ : Rn n → Rn n, IsSmoothTestField (ball c r) φ → ∫ x in E, divergence φ x = 0) →
        volume (E ∩ ball c r) = 0 ∨ volume (ball c r \ E) = 0) :
    TrivialOfNullEssentialBoundaryStatement n := by
  intro hn E hE c r h
  refine hPoincare hn hE fun φ hφ => ?_
  exact setIntegral_divergence_eq_zero_of_hausdorffN_essentialBoundary (by omega)
    hE.nullMeasurableSet (convex_ball c r) h (hφ.1.of_le (by simp)) hφ.2.1 hφ.2.2

/-- **Null essential boundary implies triviality** (the null case of Federer's criterion,
EG Thm 5.23): if `ℋ^{n-1}(∂ᵉE ∩ B_r(c)) = 0`, then `E` is a.e. empty or a.e. full in `B_r(c)`.
Steps 1–4 are `setIntegral_divergence_eq_zero_of_hausdorffN_essentialBoundary`; then
`TV(E; B_r) = 0` (`totalVariationOn_indicator_eq_iSup`) and
`volume_inter_ball_eq_zero_or_of_totalVariationOn_eq_zero` (the `L¹`-Poincaré form of the
relative isoperimetric inequality, EG Thm 5.11 (ii) in `L¹` form) give triviality. -/
theorem ae_trivial_of_hausdorffN_essentialBoundary_inter_ball :
    TrivialOfNullEssentialBoundaryStatement n := by
  refine ae_trivial_of_hausdorffN_essentialBoundary_inter_ball_of fun _ E hE c r h => ?_
  refine volume_inter_ball_eq_zero_or_of_totalVariationOn_eq_zero hE ?_
  rw [totalVariationOn_indicator_eq_iSup isOpen_ball hE]
  refine le_antisymm (iSup₂_le fun φ hφ => iSup_le fun _ => ?_) bot_le
  rw [h φ hφ, ENNReal.ofReal_zero]

end GMTFoundations
