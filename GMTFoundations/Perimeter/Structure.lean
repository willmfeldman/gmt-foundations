/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.ConeGraph
public import GMTFoundations.Statements.Perimeter
import GMTFoundations.Measure.Lusin
import GMTFoundations.GMT.Density
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# De Giorgi–Federer structure theorem

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

This file proves `HasLocallyFinitePerimeter.rectifiable_essentialBoundary` and
`IsGaussGreenPair.eq_hausdorffN_restrict`, the statements `RectifiableEssentialBoundaryStatement`
and `GaussGreenMeasureEqHausdorffStatement` of `Statements/Perimeter.lean`.

## Rectifiability of the essential boundary (EG Thm 5.15 (i), Lemma 5.5)

We prove countable `ℋ^{n-1}`-rectifiability only, not EG's `C¹`-hypersurface form. Steps 1–3 of
EG's proof (Egorov, Lusin, the cone condition) are kept; step 4 (Whitney's extension theorem and
the implicit function theorem) is replaced by "cone condition ⇒ Lipschitz graph" and a McShane
extension (`Perimeter/ConeGraph.lean`).

* `IsGaussGreenPair.exists_cone_pieces` (EG Thm 5.15, steps 1–2): Egorov plus Lusin give countably
  many compact pieces `K ⊆ Ω` exhausting `μ`, on which the normal `ν` is a continuous unit field and
  `E` is uniformly close to the half-spaces `{⟪y - x, ν x⟫ < 0}`. The a.e. input is the blow-up
  theorem (`hasDensity_symmDiff_halfSpace`, EG Thm 5.13) at the `μ`-a.e. points where the normal
  averages converge to `ν x`. EG's step 1 applies Egorov's theorem without checking
  measurability in `x`, and uses `ν_E`, which is only defined on `∂*E`. We use instead the Borel
  normal `ν` of the Gauss–Green pair (defined everywhere), and get measurability in `x` from
  section measures on `ℝⁿ × ℝⁿ`, along dyadic radii.
* The cone condition and the Lipschitz graphs (`Perimeter/ConeGraph.lean`) then cover each piece
  by countably many Lipschitz images of `ℝ^{n-1}`; what is left of `Ω ∩ ∂ᵉE` is `μ`-null, hence
  `ℋ^{n-1}`-null (`IsGaussGreenPair.hausdorffN_eq_zero_of_subset_essentialBoundary`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### A compact exhaustion of an open set -/

/-- `closedBall 0 m` minus the `1/(m+1)`-neighbourhood of `Ωᶜ`: compact subsets of `Ω` increasing
to `Ω` (for `Ω` open). -/
def exhaustOpen (Ω : Set (Rn n)) (m : ℕ) : Set (Rn n) :=
  closedBall 0 m \ thickening (1 / ((m : ℝ) + 1)) Ωᶜ

theorem isCompact_exhaustOpen (Ω : Set (Rn n)) (m : ℕ) : IsCompact (exhaustOpen Ω m) :=
  (isCompact_closedBall 0 _).diff isOpen_thickening

theorem exhaustOpen_subset (Ω : Set (Rn n)) (m : ℕ) : exhaustOpen Ω m ⊆ Ω := by
  intro x hx
  by_contra hxΩ
  exact hx.2 (self_subset_thickening (by positivity) _ hxΩ)

theorem measurableSet_exhaustOpen (Ω : Set (Rn n)) (m : ℕ) : MeasurableSet (exhaustOpen Ω m) :=
  (isCompact_exhaustOpen Ω m).isClosed.measurableSet

theorem iUnion_exhaustOpen {Ω : Set (Rn n)} (hΩ : IsOpen Ω) : ⋃ m, exhaustOpen Ω m = Ω := by
  refine Subset.antisymm (iUnion_subset (exhaustOpen_subset Ω)) fun x hx => ?_
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  obtain ⟨m₁, hm₁⟩ := exists_nat_ge ‖x‖
  obtain ⟨m₂, hm₂⟩ := exists_nat_one_div_lt hε
  refine mem_iUnion.2 ⟨max m₁ m₂, ?_, fun hxt => ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    exact hm₁.trans (by exact_mod_cast le_max_left m₁ m₂)
  · obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.1 hxt
    have hle : 1 / ((max m₁ m₂ : ℕ) + 1 : ℝ) ≤ 1 / ((m₂ : ℝ) + 1) := by
      gcongr; exact_mod_cast le_max_right m₁ m₂
    exact hz (hεΩ (by rw [mem_ball, dist_comm]; linarith))

/-! ### Measurability of the half-space discrepancy in `x` -/

/-- `x ↦ |(E △ {⟪y - x, ν x⟫ < 0}) ∩ B_r(x)|` is measurable: it is a section measure of a Borel
subset of `ℝⁿ × ℝⁿ` (EG Thm 5.15, step 1, applies Egorov's theorem without checking this). -/
theorem measurable_volume_symmDiff_halfSpace_inter_ball {E : Set (Rn n)} (hE : MeasurableSet E)
    {ν : Rn n → Rn n} (hν : Measurable ν) (r : ℝ) :
    Measurable fun x => volume (symmDiff E {y | ⟪y - x, ν x⟫ < 0} ∩ ball x r) := by
  set T : Set (Rn n × Rn n) :=
    symmDiff {p | p.2 ∈ E} {p | ⟪p.2 - p.1, ν p.1⟫ < 0} ∩ {p | dist p.2 p.1 < r}
  have hT : MeasurableSet T :=
    ((measurable_snd hE).symmDiff (measurableSet_lt ((measurable_snd.sub measurable_fst).inner
      (hν.comp measurable_fst)) measurable_const)).inter
      (measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const)
  convert measurable_measure_prodMk_left (ν := (volume : Measure (Rn n))) hT using 2

/-! ### Egorov and Lusin pieces (EG Thm 5.15, steps 1–2) -/

/-- At `μ`-a.e. point the normal is a unit vector and `E` is close to the half-space it defines
(the blow-up theorem `hasDensity_symmDiff_halfSpace` at the points where the normal averages
converge to `ν x`, which are `μ`-almost all points). -/
theorem IsGaussGreenPair.ae_hasDensity_symmDiff_normal (hn : 2 ≤ n) {Ω E : Set (Rn n)}
    {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) :
    ∀ᵐ x ∂μ, ‖ν x‖ = 1 ∧ HasDensity (symmDiff E {y | ⟪y - x, ν x⟫ < 0}) x 0 := by
  filter_upwards [h.ae_tendsto_average_normal hΩ, h.norm_normal] with x hx hν
  exact ⟨hν, hasDensity_symmDiff_halfSpace hn hΩ hE h hx.1 hx.2.1 hν hx.2.2⟩

/-- A radius `r < 2^{-J}` lies in a dyadic interval `[2^{-j-1}, 2^{-j})` with `j ≥ J`. -/
private theorem exists_dyadic_bracket {r : ℝ} (hr : 0 < r) {J : ℕ} (hrJ : r < (1 / 2 : ℝ) ^ J) :
    ∃ j, J ≤ j ∧ (1 / 2 : ℝ) ^ (j + 1) ≤ r ∧ r < (1 / 2 : ℝ) ^ j := by
  classical
  have hex : ∃ k, (1 / 2 : ℝ) ^ (k + 1) ≤ r := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨k, (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k)).trans hk.le⟩
  have hj : (1 / 2 : ℝ) ^ (Nat.find hex + 1) ≤ r := Nat.find_spec hex
  have hlt : r < (1 / 2 : ℝ) ^ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero]
      exact hrJ.trans_le (pow_le_one₀ (by norm_num) (by norm_num))
    · obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have := Nat.find_min hex (show j' < Nat.find hex by omega)
      rw [not_le] at this
      rwa [hj']
  refine ⟨Nat.find hex, ?_, hj, hlt⟩
  by_contra hJj
  push Not at hJj
  have : (1 / 2 : ℝ) ^ J ≤ (1 / 2) ^ (Nat.find hex + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith

/-- **One Egorov–Lusin piece.** Inside a measurable `s` of finite `μ`-measure there is a compact
`K`, exhausting `s` up to `ε`, on which `ν` is continuous and the half-space approximation is
uniform. -/
private theorem IsGaussGreenPair.exists_uniform_piece (hn : 2 ≤ n) {Ω E : Set (Rn n)}
    {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) {s : Set (Rn n)} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K ⊆ s, IsCompact K ∧ μ (s \ K) ≤ ENNReal.ofReal ε ∧ ContinuousOn ν K ∧
      ∀ η : ℝ, 0 < η → ∃ r₀ > 0, ∀ x ∈ K, ∀ r, 0 < r → r < r₀ →
        volume (symmDiff E {y | ⟪y - x, ν x⟫ < 0} ∩ ball x r) ≤
          ENNReal.ofReal η * volume (ball x r) := by
  set ρ : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j with hρ_def
  set Q : Rn n → Set (Rn n) := fun x => symmDiff E {y | ⟪y - x, ν x⟫ < 0}
  set f : ℕ → Rn n → ℝ := fun j x =>
    (volume (Q x ∩ ball x (ρ j))).toReal / (volume (ball x (ρ j))).toReal
  have hfm : ∀ j, StronglyMeasurable (f j) := fun j => by
    have : f j = fun x => (volume (Q x ∩ ball x (ρ j))).toReal /
        (volume (ball (0 : Rn n) (ρ j))).toReal := by
      ext x; simp only [f, Measure.addHaar_ball_center]
    rw [this]
    exact ((measurable_volume_symmDiff_halfSpace_inter_ball hE h.measurable_normal
      _).ennreal_toReal.div_const _).stronglyMeasurable
  have hρ : Tendsto ρ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall fun j => mem_Ioi.2 (by positivity : (0 : ℝ) < (1 / 2) ^ j)⟩
  have hae : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun j => f j x) atTop (𝓝 ((fun _ => (0 : ℝ)) x)) := by
    filter_upwards [h.ae_hasDensity_symmDiff_normal hn hΩ hE] with x hx _
    exact hx.2.comp hρ
  obtain ⟨t, hts, htm, hμt, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto hfm stronglyMeasurable_const hs hμs hae (half_pos hε)
  obtain ⟨K, hKst, hK, hμK, hcont⟩ := h.measurable_normal.exists_isCompact_continuousOn
    (μ := μ) (hs.diff htm) (ne_top_of_le_ne_top hμs (measure_mono diff_subset))
    (ENNReal.ofReal_pos.2 (half_pos hε)).ne'
  refine ⟨K, hKst.trans diff_subset, hK, ?_, hcont, ?_⟩
  · calc μ (s \ K) ≤ μ (t ∪ (s \ t) \ K) := measure_mono fun x ⟨hxs, hxK⟩ => by
          by_cases hxt : x ∈ t
          · exact Or.inl hxt
          · exact Or.inr ⟨⟨hxs, hxt⟩, hxK⟩
      _ ≤ μ t + μ ((s \ t) \ K) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hμt hμK.le
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  · intro η hη
    set W := (volume (ball (0 : Rn n) 1)).toReal
    have hvol : ∀ (c : Rn n) {r : ℝ}, 0 < r → (volume (ball c r)).toReal = r ^ n * W := by
      intro c r hr
      rw [Measure.addHaar_ball_of_pos volume c hr, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg hr.le n)]
    have hW : 0 < W :=
      ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
    have hfin : ∀ (S : Set (Rn n)) (c : Rn n) (r : ℝ), volume (S ∩ ball c r) ≠ ∞ := fun S c r =>
      ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hunif (η / 2 ^ n) (by positivity))
    refine ⟨ρ J, by positivity, fun x hxK r hr hrJ => ?_⟩
    obtain ⟨j, hJj, hj1, hj⟩ := exists_dyadic_bracket hr hrJ
    have hfj : f j x < η / 2 ^ n := by
      have := hJ j hJj x (hKst hxK)
      rwa [Real.dist_eq, zero_sub, abs_neg,
        abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)] at this
    have hρj : 0 < ρ j := by positivity
    have hBj : 0 < (volume (ball x (ρ j))).toReal := by rw [hvol x hρj]; positivity
    have h1 : (volume (Q x ∩ ball x (ρ j))).toReal <
        η / 2 ^ n * (volume (ball x (ρ j))).toReal :=
      (div_lt_iff₀ hBj).1 hfj
    have h2 : (volume (Q x ∩ ball x r)).toReal ≤ (volume (Q x ∩ ball x (ρ j))).toReal :=
      ENNReal.toReal_mono (hfin _ _ _)
        (measure_mono (inter_subset_inter_right _ (ball_subset_ball hj.le)))
    have h3 : (volume (ball x (ρ j))).toReal ≤ 2 ^ n * (volume (ball x r)).toReal := by
      rw [hvol x hρj, hvol x hr, ← mul_assoc, ← mul_pow]
      gcongr
      have : ρ j = 2 * (1 / 2 : ℝ) ^ (j + 1) := by simp only [ρ]; rw [pow_succ]; ring
      linarith
    have h4 : (volume (Q x ∩ ball x r)).toReal ≤ η * (volume (ball x r)).toReal := by
      calc (volume (Q x ∩ ball x r)).toReal
          ≤ η / 2 ^ n * (volume (ball x (ρ j))).toReal := h2.trans h1.le
        _ ≤ η / 2 ^ n * (2 ^ n * (volume (ball x r)).toReal) := by gcongr
        _ = η * (volume (ball x r)).toReal := by field_simp
    rw [← ENNReal.ofReal_toReal (hfin _ _ _), ← ENNReal.ofReal_toReal measure_ball_lt_top.ne,
      ← ENNReal.ofReal_mul hη.le]
    exact ENNReal.ofReal_le_ofReal h4

/-- **Egorov–Lusin pieces** (EG Thm 5.15, steps 1–2). Countably many compact `K ⊆ Ω` exhaust `μ`;
on each, `ν` is a continuous unit field and `E` is uniformly close to the half-spaces
`{⟪y - x, ν x⟫ < 0}`, `x ∈ K`. -/
theorem IsGaussGreenPair.exists_cone_pieces (hn : 2 ≤ n) {Ω E : Set (Rn n)} {μ : Measure (Rn n)}
    {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) :
    ∃ K : ℕ × ℕ → Set (Rn n), (∀ k, IsCompact (K k)) ∧ (∀ k, K k ⊆ Ω) ∧
      μ (Ω \ ⋃ k, K k) = 0 ∧ (∀ k, ∀ x ∈ K k, ‖ν x‖ = 1) ∧ (∀ k, ContinuousOn ν (K k)) ∧
      (∀ k, ∀ η : ℝ, 0 < η → ∃ r₀ > 0, ∀ x ∈ K k, ∀ r, 0 < r → r < r₀ →
        volume (symmDiff E {y | ⟪y - x, ν x⟫ < 0} ∩ ball x r) ≤
          ENNReal.ofReal η * volume (ball x r)) := by
  set s : ℕ → Set (Rn n) := fun m => exhaustOpen Ω m ∩ {x | ‖ν x‖ = 1}
  have hsm : ∀ m, MeasurableSet (s m) := fun m =>
    (measurableSet_exhaustOpen Ω m).inter
      (measurableSet_eq_fun h.measurable_normal.norm measurable_const)
  have hμs : ∀ m, μ (s m) ≠ ∞ := fun m =>
    (lt_of_le_of_lt (measure_mono inter_subset_left) (h.lt_top_of_isCompact _
      (isCompact_exhaustOpen Ω m) (exhaustOpen_subset Ω m))).ne
  choose K hKs hKc hμK hKcont hKunif using fun p : ℕ × ℕ =>
    h.exists_uniform_piece hn hΩ hE (hsm p.1) (hμs p.1) (Nat.one_div_pos_of_nat (n := p.2))
  refine ⟨K, hKc, fun p => (hKs p).trans (inter_subset_left.trans (exhaustOpen_subset Ω _)),
    ?_, fun p x hx => (hKs p hx).2, hKcont, hKunif⟩
  -- each `s m` is exhausted by the `K (m, i)`
  have hnull : ∀ m, μ (s m \ ⋃ i, K (m, i)) = 0 := by
    intro m
    have hlim : Tendsto (fun i : ℕ => ENNReal.ofReal (1 / ((i : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
    refine le_antisymm (ge_of_tendsto' hlim fun i => ?_) bot_le
    exact (measure_mono (diff_subset_diff_right (subset_iUnion (fun i => K (m, i)) i))).trans
      (hμK (m, i))
  have hcover : Ω \ ⋃ k, K k ⊆ (⋃ m, s m \ ⋃ i, K (m, i)) ∪ {x | ‖ν x‖ = 1}ᶜ := by
    rintro x ⟨hxΩ, hxK⟩
    by_cases hν : ‖ν x‖ = 1
    · left
      rw [← iUnion_exhaustOpen hΩ] at hxΩ
      obtain ⟨m, hm⟩ := mem_iUnion.1 hxΩ
      exact mem_iUnion.2 ⟨m, ⟨hm, hν⟩, fun hx => hxK (by
        obtain ⟨i, hi⟩ := mem_iUnion.1 hx
        exact mem_iUnion.2 ⟨(m, i), hi⟩)⟩
    · exact Or.inr hν
  refine measure_mono_null hcover (measure_union_null (measure_iUnion_null hnull) ?_)
  exact ae_iff.1 h.norm_normal

/-! ### Rectifiability of the essential boundary -/

/-- **Rectifiability of the essential boundary** (EG Thm 5.15 (i) with Lemma 5.5, via the cone
condition and Lipschitz graphs in place of EG's step 4). -/
theorem IsGaussGreenPair.isCountablyRectifiable_essentialBoundary (hn : 2 ≤ n) {Ω E : Set (Rn n)}
    {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) : IsCountablyRectifiable n (n - 1) (Ω ∩ essentialBoundary E) := by
  obtain ⟨K, -, -, hKμ, hKν, hKcont, hKunif⟩ := h.exists_cone_pieces hn hΩ hE
  have hcov : ∀ k, ∃ F : ℕ → Rn (n - 1) → Rn n, (∀ i, ∃ C, LipschitzWith C (F i)) ∧
      K k ⊆ ⋃ i, range (F i) := fun k => by
    obtain ⟨δ, hδ, hcone⟩ := abs_inner_le_of_uniform_halfSpace (by omega) (hKν k) (hKunif k)
      (ε := 1 / 4) (by norm_num) (by norm_num)
    exact exists_lipschitz_cover_of_cone (by omega) (hKν k) (hKcont k) hδ hcone
  choose F hFL hFK using hcov
  refine IsCountablyRectifiable.of_countable (fun p : (ℕ × ℕ) × ℕ => F p.1 p.2)
    (fun p => hFL _ _) ?_
  refine h.hausdorffN_eq_zero_of_subset_essentialBoundary hn hΩ hE diff_subset
    (measure_mono_null ?_ hKμ)
  rintro x ⟨⟨hxΩ, -⟩, hx⟩
  refine ⟨hxΩ, fun hxK => hx ?_⟩
  obtain ⟨k, hk⟩ := mem_iUnion.1 hxK
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hFK k hk)
  exact mem_iUnion.2 ⟨(k, i), hi⟩

/-- **De Giorgi–Federer structure theorem, rectifiability part** (EG Thm 5.15 (i), Lemma 5.5):
`Ω ∩ ∂ᵉE` is countably `ℋ^{n-1}`-rectifiable, `ℋ^{n-1}((Ω ∩ ∂ᵉE) ∖ ∂*E) = 0`, and
`∂*E ⊆ ∂ᵉE`. -/
theorem HasLocallyFinitePerimeter.rectifiable_essentialBoundary :
    RectifiableEssentialBoundaryStatement n := by
  intro hn Ω E hΩ hE ⟨μ, ν, h⟩
  exact ⟨h.isCountablyRectifiable_essentialBoundary hn hΩ hE,
    h.hausdorffN_essentialBoundary_diff_reducedBoundary hn hΩ hE,
    reducedBoundary_subset_essentialBoundary hn hΩ hE⟩

/-! ### The perimeter measure is `ℋ^{n-1}⌊∂ᵉE` (EG Thm 5.15 (iii), Thm 5.16)

EG's step 5 uses that a `C¹` hypersurface has `ℋ^{n-1}`-density `1` (and cites Thm 5.14 (ii)
where (iii) is meant). We avoid `C¹` hypersurfaces and the area formula: the density theorem for
countably rectifiable sets `GMT.eq_withDensity_upperDensity'` (`GMT/Density.lean`) together with
Besicovitch differentiation identifies the Radon–Nikodym density. That theorem needs one constant
`C` with `ρ(B_r(x)) ≤ C r^{n-1}` for all balls, which a Gauss–Green measure need not satisfy. So
a measurable, `μ`-full `S ⊆ ∂*E` is cut into the strata
`S ∩ {μ(B_r(x)) ≤ 2ω_{n-1} r^{n-1} for r < 1/(j+1)} ∩ exhaustOpen Ω j`, on which the bound is
uniform; on each, the density `μ(B_r(x))/(ω_{n-1} r^{n-1}) → 1` (EG Thm 5.14 (iii)) makes the
Radon–Nikodym density `1`. -/

theorem exhaustOpen_mono (Ω : Set (Rn n)) : Monotone (exhaustOpen Ω) := by
  intro i j hij x ⟨hx1, hx2⟩
  refine ⟨closedBall_subset_closedBall (by exact_mod_cast hij) hx1,
    fun hx => hx2 (thickening_mono ?_ _ hx)⟩
  exact one_div_le_one_div_of_le (by positivity) (by
    simp only [add_le_add_iff_right, Nat.cast_le]; exact hij)

/-- A ball of radius `1/(m+1) - 1/(m+2)` around a point of `exhaustOpen Ω m` stays in
`exhaustOpen Ω (m + 1)`. -/
theorem ball_subset_exhaustOpen_succ {Ω : Set (Rn n)} {m : ℕ} {x : Rn n}
    (hx : x ∈ exhaustOpen Ω m) :
    ball x (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) ⊆ exhaustOpen Ω (m + 1) := by
  intro z hz
  rw [mem_ball] at hz
  have hδ1 : 1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) ≤ 1 := by
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have h2 : 0 ≤ 1 / ((m : ℝ) + 2) := by positivity
    linarith
  refine ⟨?_, fun hzt => hx.2 ?_⟩
  · have hx1 := hx.1
    rw [mem_closedBall, dist_zero_right] at hx1 ⊢
    have := norm_sub_norm_le z x
    rw [← dist_eq_norm] at this
    push_cast
    linarith
  · obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.1 hzt
    refine mem_thickening_iff.2 ⟨w, hw, ?_⟩
    have hcast : ((m + 1 : ℕ) : ℝ) + 1 = (m : ℝ) + 2 := by push_cast; ring
    rw [hcast] at hzw
    calc dist x w ≤ dist x z + dist z w := dist_triangle _ _ _
      _ < (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) + 1 / ((m : ℝ) + 2) := by
          rw [dist_comm]; linarith
      _ = 1 / ((m : ℝ) + 1) := by ring

/-- The set of centers at which `μ(B_r(x)) ≤ c r^k` for all `r < a` is closed. -/
theorem isClosed_setOf_forall_measure_ball_le (μ : Measure (Rn n)) (a c : ℝ) (k : ℕ) :
    IsClosed {x | ∀ r, 0 < r → r < a → μ (ball x r) ≤ ENNReal.ofReal (c * r ^ k)} := by
  refine isClosed_of_closure_subset fun x hx r hr hra => ?_
  obtain ⟨u, hu, hmono, hU⟩ := exists_seq_iUnion_closedBall_eq_ball x hr
  rw [← hU]
  refine le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) fun i => ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (r - u i) (by linarith [(hu i).2])
  refine (measure_mono fun z hz => ?_).trans (hy r hr hra)
  rw [mem_closedBall] at hz
  rw [mem_ball]
  calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ < r := by linarith

/-- EG Thm 5.14 (iii) at a point of the reduced boundary
(`IsGaussGreenPair.tendsto_measure_ball_div` via `mem_reducedBoundary_iff`). -/
theorem IsGaussGreenPair.tendsto_measure_ball_div_of_mem_reducedBoundary (hn : 2 ≤ n)
    {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n} (hx : x ∈ reducedBoundary Ω E) :
    Tendsto (fun r => μ (ball x r) / ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)))
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨hxΩ, hpos, v, hv, hlim⟩ := (h.mem_reducedBoundary_iff hΩ).1 hx
  exact h.tendsto_measure_ball_div hn hΩ hE hxΩ hpos hv hlim

/-- **One stratum.** On a measurable `S ⊆ ∂*E ∩ exhaustOpen Ω j` on which
`μ(B_r(x)) ≤ 2 ω_{n-1} r^{n-1}` for `r < 1/(j+1)`, `μ⌊S = ℋ^{n-1}⌊S` (the density theorem
`GMT.eq_withDensity_upperDensity'`, with the density `1` from EG Thm 5.14 (iii)). -/
theorem IsGaussGreenPair.restrict_stratum_eq (hn : 2 ≤ n) {Ω E : Set (Rn n)} {μ : Measure (Rn n)}
    {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E)
    {S : Set (Rn n)} (hSm : MeasurableSet S) (hSb : S ⊆ reducedBoundary Ω E) (j : ℕ)
    (hSj : S ⊆ exhaustOpen Ω j)
    (hup : ∀ x ∈ S, ∀ r, 0 < r → r < 1 / ((j : ℝ) + 1) →
      μ (ball x r) ≤ ENNReal.ofReal (2 * unitBallVolume (n - 1) * r ^ (n - 1))) :
    μ.restrict S = (hausdorffN n (n - 1)).restrict S := by
  set ω := unitBallVolume (n - 1) with hω_def
  have hω : 0 < ω := unitBallVolume_pos _
  have hMfin : μ (exhaustOpen Ω j) ≠ ∞ :=
    (h.lt_top_of_isCompact _ (isCompact_exhaustOpen Ω j) (exhaustOpen_subset Ω j)).ne
  set M : ℝ := (μ (exhaustOpen Ω j)).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  set C : ℝ := max (2 ^ n * ω) (M * (2 * ((j : ℝ) + 1)) ^ (n - 1))
  have hSΩ : S ⊆ Ω := hSj.trans (exhaustOpen_subset Ω j)
  have hSess : S ⊆ Ω ∩ essentialBoundary E := fun x hx =>
    ⟨hSΩ hx, reducedBoundary_subset_essentialBoundary hn hΩ hE (hSb hx)⟩
  have hrect := (h.isCountablyRectifiable_essentialBoundary hn hΩ hE).mono hSess
  have hfin : ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ S) < ∞ := fun K hK hKΩ =>
    (h.hausdorffN_le_mul_measure hn hΩ hE (inter_subset_right.trans hSb)).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((measure_mono inter_subset_left).trans_lt (h.lt_top_of_isCompact K hK hKΩ)))
  have hρS : μ.restrict S Sᶜ = 0 := by
    rw [Measure.restrict_apply hSm.compl, compl_inter_self, measure_empty]
  -- one constant `C` for all balls: the stratum bound if `2r < 1/(j+1)`, else `μ(exhaustOpen Ω j)`
  have hbd : ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω →
      μ.restrict S (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)) := by
    intro x r hr _
    rw [Measure.restrict_apply measurableSet_ball]
    rcases (ball x r ∩ S).eq_empty_or_nonempty with h0 | ⟨y, hyB, hyS⟩
    · rw [h0, measure_empty]; exact zero_le
    by_cases h2r : 2 * r < 1 / ((j : ℝ) + 1)
    · have hsub : ball x r ∩ S ⊆ ball y (2 * r) := fun z hz => by
        rw [mem_ball] at hyB ⊢
        have := hz.1; rw [mem_ball] at this
        calc dist z y ≤ dist z x + dist y x := dist_triangle_right _ _ _
          _ < 2 * r := by linarith
      have hpow : 2 * ω * (2 * r) ^ (n - 1) = 2 ^ n * ω * r ^ (n - 1) := by
        have h2n : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
        rw [h2n, mul_pow]; ring
      calc μ (ball x r ∩ S) ≤ μ (ball y (2 * r)) := measure_mono hsub
        _ ≤ ENNReal.ofReal (2 * ω * (2 * r) ^ (n - 1)) := hup y hyS (2 * r) (by positivity) h2r
        _ ≤ ENNReal.ofReal (C * r ^ (n - 1)) := by
          rw [hpow]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · push Not at h2r
      have h1 : 1 ≤ 2 * ((j : ℝ) + 1) * r := by
        rw [div_le_iff₀ (by positivity)] at h2r; linarith
      calc μ (ball x r ∩ S) ≤ μ (exhaustOpen Ω j) := measure_mono (inter_subset_right.trans hSj)
        _ = ENNReal.ofReal M := (ENNReal.ofReal_toReal hMfin).symm
        _ ≤ ENNReal.ofReal (C * r ^ (n - 1)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc M = M * 1 := (mul_one M).symm
            _ ≤ M * (2 * ((j : ℝ) + 1) * r) ^ (n - 1) :=
                mul_le_mul_of_nonneg_left (one_le_pow₀ h1) hM
            _ = M * (2 * ((j : ℝ) + 1)) ^ (n - 1) * r ^ (n - 1) := by rw [mul_pow]; ring
            _ ≤ C * r ^ (n - 1) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hRN := GMT.eq_withDensity_upperDensity' hn hΩ hSm hSΩ hrect hfin hρS C hbd
  -- the density is `1`, `ℋ⌊S`-a.e. (Besicovitch differentiation and EG Thm 5.14 (iii))
  set V := exhaustOpen Ω (j + 1) with hV_def
  have hVfin : μ V < ∞ :=
    h.lt_top_of_isCompact _ (isCompact_exhaustOpen Ω (j + 1)) (exhaustOpen_subset Ω _)
  haveI : IsFiniteMeasure (μ.restrict V) := isFiniteMeasure_restrict.2 hVfin.ne
  have hSV : S ⊆ V := hSj.trans (exhaustOpen_mono Ω (Nat.le_succ j))
  have hdens := ae_tendsto_measure_inter_ball_div (μ.restrict V) S
  rw [Measure.restrict_restrict hSm, inter_eq_left.2 hSV] at hdens
  set N := {x | x ∈ S ∧ ¬ Tendsto (fun r => μ.restrict V (S ∩ ball x r) / μ.restrict V (ball x r))
    (𝓝[>] 0) (𝓝 1)}
  have hN : μ N = 0 := by
    have := ae_iff.1 ((ae_restrict_iff' hSm).1 hdens)
    refine measure_mono_null (fun x hx => ?_) this
    simp only [mem_setOf_eq, Classical.not_imp]
    exact hx
  have hNℋ : hausdorffN n (n - 1) N = 0 :=
    h.hausdorffN_eq_zero_of_subset_essentialBoundary hn hΩ hE (fun x hx => hSess hx.1) hN
  have hθ : (fun x => limsup (fun r => μ.restrict S (ball x r) /
      ENNReal.ofReal (ω * r ^ (n - 1))) (𝓝[>] 0)) =ᵐ[(hausdorffN n (n - 1)).restrict S] 1 := by
    refine (ae_restrict_iff' hSm).2 (ae_iff.2 (measure_mono_null (fun x hx => ?_) hNℋ))
    simp only [mem_setOf_eq, Classical.not_imp] at hx
    refine ⟨hx.1, fun hT => hx.2 ?_⟩
    have hxb := hSb hx.1
    have hDensOne := h.tendsto_measure_ball_div_of_mem_reducedBoundary hn hΩ hE hxb
    obtain ⟨-, hpos, -⟩ := (h.mem_reducedBoundary_iff hΩ).1 hxb
    have hδ : 0 < 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2) := by
      rw [sub_pos]; exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    have hsub := ball_subset_exhaustOpen_succ (hSj hx.1)
    have heq : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        μ.restrict V (S ∩ ball x r) / μ.restrict V (ball x r) *
          (μ (ball x r) / ENNReal.ofReal (ω * r ^ (n - 1))) =
        μ.restrict S (ball x r) / ENNReal.ofReal (ω * r ^ (n - 1)) := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
      have hB : ball x r ⊆ V := (ball_subset_ball hr.2.le).trans hsub
      have h1 : μ.restrict V (ball x r) = μ (ball x r) := by
        rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hB]
      have h2 : μ.restrict V (S ∩ ball x r) = μ.restrict S (ball x r) := by
        rw [Measure.restrict_apply (hSm.inter measurableSet_ball),
          Measure.restrict_apply measurableSet_ball,
          inter_eq_left.2 (inter_subset_right.trans hB), inter_comm]
      have h0 : μ (ball x r) ≠ 0 := (hpos r hr.1).ne'
      have htop : μ (ball x r) ≠ ∞ := ((measure_mono hB).trans_lt hVfin).ne
      rw [h1, h2]
      simp only [div_eq_mul_inv]
      rw [mul_assoc, ← mul_assoc (μ (ball x r))⁻¹, ENNReal.inv_mul_cancel h0 htop, one_mul]
    have hprod := ENNReal.Tendsto.mul hT (Or.inr ENNReal.one_ne_top) hDensOne (Or.inl one_ne_zero)
    rw [mul_one] at hprod
    exact (hprod.congr' heq).limsup_eq
  exact hRN.trans (by rw [withDensity_congr_ae hθ, withDensity_one])

/-- **EG Thm 5.15 (iii)**: `μ = ℋ^{n-1}⌊∂*E` (via the density theorem for rectifiable sets, not
EG's `C¹`-hypersurface argument). -/
theorem IsGaussGreenPair.eq_hausdorffN_reducedBoundary (hn : 2 ≤ n) {Ω E : Set (Rn n)}
    {μ : Measure (Rn n)} {ν : Rn n → Rn n} (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω)
    (hE : MeasurableSet E) : μ = (hausdorffN n (n - 1)).restrict (reducedBoundary Ω E) := by
  set ω := unitBallVolume (n - 1)
  -- a measurable, `μ`-full core `S ⊆ ∂*E`
  have hnm : NullMeasurableSet (reducedBoundary Ω E) μ := by
    simpa using (NullMeasurableSet.of_null (h.measure_compl_reducedBoundary hΩ)).compl
  obtain ⟨S, hSb, hSm, hSae⟩ := hnm.exists_measurable_subset_ae_eq
  have hdiff : μ (reducedBoundary Ω E \ S) = 0 := (ae_eq_set.1 hSae).2
  have hSc : μ Sᶜ = 0 := by
    refine measure_mono_null (fun x hx => ?_)
      (measure_union_null (h.measure_compl_reducedBoundary hΩ) hdiff)
    by_cases hx' : x ∈ reducedBoundary Ω E
    · exact Or.inr ⟨hx', hx⟩
    · exact Or.inl hx'
  -- strata
  set F : ℕ → Set (Rn n) := fun j => {x | ∀ r, 0 < r → r < 1 / ((j : ℝ) + 1) →
    μ (ball x r) ≤ ENNReal.ofReal (2 * ω * r ^ (n - 1))}
  set T : ℕ → Set (Rn n) := fun j => S ∩ F j ∩ exhaustOpen Ω j
  have hTm : ∀ j, MeasurableSet (T j) := fun j =>
    (hSm.inter (isClosed_setOf_forall_measure_ball_le μ _ _ _).measurableSet).inter
      (measurableSet_exhaustOpen Ω j)
  have hTU : ⋃ j, T j = S := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans inter_subset_left)
      fun x hx => ?_
    have hxb := hSb hx
    have hDensOne := h.tendsto_measure_ball_div_of_mem_reducedBoundary hn hΩ hE hxb
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        μ (ball x r) / ENNReal.ofReal (ω * r ^ (n - 1)) < 2 :=
      (tendsto_order.1 hDensOne).2 2 (by norm_num)
    obtain ⟨a, ha, hav⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hev
    obtain ⟨j₁, hj₁⟩ := exists_nat_one_div_lt ha
    have hxΩ : x ∈ ⋃ m, exhaustOpen Ω m := by rw [iUnion_exhaustOpen hΩ]; exact hxb.1
    obtain ⟨j₂, hj₂⟩ := mem_iUnion.1 hxΩ
    refine mem_iUnion.2 ⟨max j₁ j₂, ⟨hx, fun r hr hrj => ?_⟩,
      exhaustOpen_mono Ω (le_max_right j₁ j₂) hj₂⟩
    have hrj₁ : r < a := by
      have : 1 / ((max j₁ j₂ : ℕ) + 1 : ℝ) ≤ 1 / ((j₁ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by
          simp only [add_le_add_iff_right, Nat.cast_le]; exact le_max_left _ _)
      linarith
    have hlt := hav ⟨hr, hrj₁⟩
    have hpos : ENNReal.ofReal (ω * r ^ (n - 1)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by have := unitBallVolume_pos (n - 1); positivity)).ne'
    rw [ENNReal.div_lt_iff (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)] at hlt
    refine hlt.le.trans (le_of_eq ?_)
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num), mul_assoc]
  have hrestr : μ.restrict S = (hausdorffN n (n - 1)).restrict S := by
    rw [← hTU]
    exact Measure.restrict_iUnion_congr.2 fun j => h.restrict_stratum_eq hn hΩ hE (hTm j)
      (fun x hx => hSb hx.1.1) j (fun x hx => hx.2) (fun x hx => hx.1.2)
  have hμS : μ.restrict S = μ := Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hSc)
  have hℋ : (hausdorffN n (n - 1)).restrict S =
      (hausdorffN n (n - 1)).restrict (reducedBoundary Ω E) := by
    refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
    · rw [diff_eq_empty.2 hSb, measure_empty]
    · exact h.hausdorffN_eq_zero_of_subset_essentialBoundary hn hΩ hE
        (fun x hx => ⟨hx.1.1, reducedBoundary_subset_essentialBoundary hn hΩ hE hx.1⟩) hdiff
  rw [← hℋ, ← hrestr, hμS]

/-- **The perimeter measure is `ℋ^{n-1}` on the essential boundary** (EG Thms 5.15 (iii), 5.16):
`μ = ℋ^{n-1}⌊(Ω ∩ ∂ᵉE)`. -/
theorem IsGaussGreenPair.eq_hausdorffN_restrict :
    GaussGreenMeasureEqHausdorffStatement n := by
  intro hn Ω E μ ν hΩ hE h
  refine (h.eq_hausdorffN_reducedBoundary hn hΩ hE).trans
    (Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩))
  · refine measure_mono_null (fun x hx => ?_) measure_empty
    exact hx.2 ⟨hx.1.1, reducedBoundary_subset_essentialBoundary hn hΩ hE hx.1⟩
  · exact h.hausdorffN_essentialBoundary_diff_reducedBoundary hn hΩ hE

end GMTFoundations
