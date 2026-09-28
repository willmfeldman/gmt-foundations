/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.GaussGreenPair.Basic
public import GMTFoundations.Perimeter.GaussGreenPair.API
public import GMTFoundations.Perimeter.GaussGreenPair.WeightedTV
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The reduced boundary has full measure; open-ball differentiation; essential boundary

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (EG).

## Open-ball differentiation

The definitions of this library (`reducedBoundary`, `HasDensity`, `essentialBoundary`) use open
balls. EG's `B(x, r)` is the closed ball, and so is Mathlib's Besicovitch differentiation
(`Besicovitch.ae_tendsto_rnDeriv`, `VitaliFamily.ae_tendsto_average` with
`Besicovitch.tendsto_filterAt`). The bridge: for `r > 0` choose `s_k ↑ r`, so that
`ball x r = ⋃ₖ closedBall x s_k` and the open-ball quantity at `r` is a limit of closed-ball
quantities at radii `s_k < r`; closed neighbourhoods of the limit then pass from closed to open
balls (`tendsto_nhdsGT_of_forall_exists_seq`).

* `tendsto_measure_ball_div_of_closedBall`, `tendsto_average_ball_of_closedBall`: the pointwise
  bridges (no a.e. statement involved).
* `ae_tendsto_average_ball`: EG Thm 1.32 with open balls,
  `⨍_{B_r(x)} f dμ → f(x)` for `μ`-a.e. `x`, `μ` locally finite, `f ∈ L¹_loc(μ)`.
* `ae_tendsto_measure_ball_div`: `ρ(B_r(x))/μ(B_r(x)) → Dμρ(x)` `μ`-a.e.
* `ae_tendsto_measure_inter_ball_div`: `μ(s ∩ B_r(x))/μ(B_r(x)) → 1` for `μ`-a.e. `x ∈ s`.

## Full measure of the reduced boundary

* `IsGaussGreenPair.mem_reducedBoundary_iff`: `reducedBoundary` quantifies existentially over
  Gauss–Green pairs; by uniqueness of the pair (`IsGaussGreenPair.unique`), membership can be
  tested on *any* Gauss–Green pair of `E` on the open set `Ω`.
* `IsGaussGreenPair.ae_tendsto_average_normal`: `⨍_{B_r(x)} ν dμ → ν(x)` for `μ`-a.e. `x`.
* `IsGaussGreenPair.measure_diff_reducedBoundary`: `μ(Ω ∖ ∂*E) = 0` (EG, remark after Def 5.4);
  `IsGaussGreenPair.measure_compl_reducedBoundary`: `μ((∂*E)ᶜ) = 0`.

## Essential boundary

* `mem_essentialBoundary_iff_limsup`: for Lebesgue-measurable `E`, `essentialBoundary E`
  (neither density `0` nor density `1`, via limits over open balls) is EG's measure-theoretic
  boundary `∂_*E` (EG Def 5.7: both `limsup |B̄_r(x) ∩ E|/rⁿ` and `limsup |B̄_r(x) ∖ E|/rⁿ` are
  positive; EG's `B(x, r)` is closed).
* `measurableSet_setOf_hasDensity_zero`, `measurableSet_setOf_hasDensity_one`,
  `measurableSet_essentialBoundary`: EG Lemma 5.9 (i) (`O`, `I`, `∂_*E` are Borel), for arbitrary
  `E` (the measurable hull does not change densities). EG's proof does not justify that a limit
  over all radii `r → 0` defines a Borel set; here density `0` is rewritten along rational radii
  (losing a factor `2ⁿ`) and `x ↦ |E ∩ B_q(x)|` is measurable by the section-measure theorem.
* `volume_diff_union_diff_setOf_hasDensity_one`: EG Lemma 5.9 (ii), `|(E ∖ I) ∪ (I ∖ E)| = 0`.
* Supporting: `hasDensity_iff_tendsto_div`, `hasDensity_zero_iff_tendsto`,
  `hasDensity_compl_zero_iff` (`E` has density `1` iff `Eᶜ` has density `0`),
  `hasDensity_toMeasurable_iff`.

## Notes

The Gauss–Green measure `μ` is only finite on compact subsets of `Ω`; the differentiation theorem
is applied to its restrictions to balls compactly contained in `Ω` (countably many cover `Ω`).
Positivity `μ(B_r(x)) > 0` is not taken from a support lemma: if `μ(B_r(x)) = 0` the averages
vanish for small radii, contradicting convergence to the unit vector `ν(x)`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

public section

namespace GMTFoundations

/-! ### Open-ball bridges -/

section Bridge

/-- If `F(s) → L` as `s → 0+` and each `G(r)` is a limit of values `F(s_k)` with `s_k ∈ (0, r)`,
then `G(r) → L` as `r → 0+`. -/
theorem tendsto_nhdsGT_of_forall_exists_seq {α : Type*} [TopologicalSpace α] [RegularSpace α]
    {F G : ℝ → α} {L : α} (hF : Tendsto F (𝓝[>] 0) (𝓝 L))
    (hG : ∀ r, 0 < r → ∃ u : ℕ → ℝ, (∀ k, u k ∈ Ioo 0 r) ∧ Tendsto (F ∘ u) atTop (𝓝 (G r))) :
    Tendsto G (𝓝[>] 0) (𝓝 L) := by
  rw [(closed_nhds_basis L).tendsto_right_iff]
  rintro U ⟨hUL, hUc⟩
  obtain ⟨δ, hδ, hδU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hF hUL)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  obtain ⟨u, hu, hFu⟩ := hG r hr.1
  exact hUc.mem_of_tendsto hFu (Eventually.of_forall fun k =>
    hδU ⟨(hu k).1, (hu k).2.trans hr.2⟩)

/-- For `r > 0` there are radii `s_k ∈ (0, r)`, increasing to `r`, with
`ball x r = ⋃ₖ closedBall x s_k`. -/
theorem exists_seq_iUnion_closedBall_eq_ball {β : Type*} [MetricSpace β] (x : β) {r : ℝ}
    (hr : 0 < r) :
    ∃ u : ℕ → ℝ, (∀ k, u k ∈ Ioo 0 r) ∧ Monotone (fun k => closedBall x (u k)) ∧
      ⋃ k, closedBall x (u k) = ball x r := by
  obtain ⟨u, hmono, hu, hlim⟩ := exists_seq_strictMono_tendsto' hr
  refine ⟨u, hu, fun i j hij => closedBall_subset_closedBall (hmono.monotone hij), ?_⟩
  ext y
  simp only [mem_iUnion, mem_closedBall, mem_ball]
  constructor
  · rintro ⟨k, hk⟩
    exact hk.trans_lt (hu k).2
  · intro hy
    obtain ⟨k, hk⟩ := (hlim.eventually (lt_mem_nhds hy)).exists
    exact ⟨k, hk.le⟩

variable {β : Type*} [MetricSpace β] [MeasurableSpace β] [OpensMeasurableSpace β]
  [ProperSpace β]

omit [OpensMeasurableSpace β] in
/-- **Ratios, closed to open balls**. If `ρ(B̄_r(x))/μ(B̄_r(x)) → L` as `r → 0+`, then
`ρ(B_r(x))/μ(B_r(x)) → L`. Only `μ` needs to be finite on balls. -/
theorem tendsto_measure_ball_div_of_closedBall {ρ μ : Measure β} [IsFiniteMeasureOnCompacts μ]
    (x : β) {L : ℝ≥0∞}
    (h : Tendsto (fun r => ρ (closedBall x r) / μ (closedBall x r)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun r => ρ (ball x r) / μ (ball x r)) (𝓝[>] 0) (𝓝 L) := by
  refine tendsto_nhdsGT_of_forall_exists_seq h fun r hr => ?_
  obtain ⟨u, hu, hmono, hU⟩ := exists_seq_iUnion_closedBall_eq_ball x hr
  refine ⟨u, hu, ?_⟩
  have hρ := tendsto_measure_iUnion_atTop (μ := ρ) hmono
  have hμ := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU] at hρ hμ
  by_cases h0 : ρ (ball x r) = 0 ∧ μ (ball x r) = 0
  · have hk : ∀ k, ρ (closedBall x (u k)) = 0 ∧ μ (closedBall x (u k)) = 0 := fun k =>
      ⟨measure_mono_null (closedBall_subset_ball (hu k).2) h0.1,
        measure_mono_null (closedBall_subset_ball (hu k).2) h0.2⟩
    simp only [Function.comp_def, hk, h0.1, h0.2]
    exact tendsto_const_nhds
  · rw [not_and_or] at h0
    exact ENNReal.Tendsto.div hρ h0 hμ (Or.inl measure_ball_lt_top.ne)

/-- **Averages, closed to open balls**. If `⨍_{B̄_r(x)} f dμ → L` as `r → 0+`, then
`⨍_{B_r(x)} f dμ → L`. -/
theorem tendsto_average_ball_of_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure β} [IsFiniteMeasureOnCompacts μ] {f : β → E} (hf : LocallyIntegrable f μ)
    (x : β) {L : E}
    (h : Tendsto (fun r => ⨍ y in closedBall x r, f y ∂μ) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun r => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 L) := by
  refine tendsto_nhdsGT_of_forall_exists_seq h fun r hr => ?_
  obtain ⟨u, hu, hmono, hU⟩ := exists_seq_iUnion_closedBall_eq_ball x hr
  refine ⟨u, hu, ?_⟩
  have hμ := tendsto_measure_iUnion_atTop (μ := μ) hmono
  have hfr : IntegrableOn f (⋃ k, closedBall x (u k)) μ := by
    rw [hU]
    exact (hf.integrableOn_isCompact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hint := tendsto_setIntegral_of_monotone (μ := μ) (fun k => measurableSet_closedBall) hmono
    hfr
  rw [hU] at hμ hint
  simp only [Function.comp_def, setAverage_eq, measureReal_def]
  by_cases h0 : μ (ball x r) = 0
  · have hk : ∀ k, μ (closedBall x (u k)) = 0 := fun k =>
      measure_mono_null (closedBall_subset_ball (hu k).2) h0
    simp only [hk, h0, ENNReal.toReal_zero, inv_zero, zero_smul]
    exact tendsto_const_nhds
  · have hμr : Tendsto (fun k => (μ (closedBall x (u k))).toReal) atTop
        (𝓝 (μ (ball x r)).toReal) :=
      (ENNReal.tendsto_toReal measure_ball_lt_top.ne).comp hμ
    exact (hμr.inv₀ (ENNReal.toReal_ne_zero.2 ⟨h0, measure_ball_lt_top.ne⟩)).smul hint

end Bridge

/-! ### Differentiation with open balls (EG Thm 1.32) -/

section Differentiation

variable {β : Type*} [MetricSpace β] [MeasurableSpace β] [BorelSpace β] [ProperSpace β]
  [SecondCountableTopology β] [HasBesicovitchCovering β]

/-- **Lebesgue–Besicovitch differentiation with open balls** (EG Thm 1.32). For a locally
finite `μ` and `f ∈ L¹_loc(μ)`, `⨍_{B_r(x)} f dμ → f(x)` as `r → 0+` for `μ`-a.e. `x`. -/
theorem ae_tendsto_average_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {μ : Measure β} [IsLocallyFiniteMeasure μ] {f : β → E}
    (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average hf] with x hx
  exact tendsto_average_ball_of_closedBall hf x (hx.comp (Besicovitch.tendsto_filterAt μ x))

/-- **Differentiation of measures with open balls**. `ρ(B_r(x))/μ(B_r(x)) → (dρ/dμ)(x)`
as `r → 0+` for `μ`-a.e. `x`. -/
theorem ae_tendsto_measure_ball_div (ρ μ : Measure β) [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ρ] :
    ∀ᵐ x ∂μ, Tendsto (fun r => ρ (ball x r) / μ (ball x r)) (𝓝[>] 0) (𝓝 (ρ.rnDeriv μ x)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv ρ μ] with x hx
  exact tendsto_measure_ball_div_of_closedBall x hx

/-- **Density points with open balls**. For any set `s`,
`μ(s ∩ B_r(x))/μ(B_r(x)) → 1` as `r → 0+` for `μ`-a.e. `x ∈ s`. -/
theorem ae_tendsto_measure_inter_ball_div (μ : Measure β) [IsLocallyFiniteMeasure μ]
    (s : Set β) :
    ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun r => μ (s ∩ ball x r) / μ (ball x r)) (𝓝[>] 0) (𝓝 1) := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s] with x hx
  have key := tendsto_measure_ball_div_of_closedBall (ρ := μ.restrict s) (μ := μ) x (L := 1)
    (hx.congr fun r => by rw [Measure.restrict_apply measurableSet_closedBall, inter_comm])
  exact key.congr fun r => by rw [Measure.restrict_apply measurableSet_ball, inter_comm]

end Differentiation

/-! ### The reduced boundary has full measure (EG Def 5.4 and the remark after it) -/

section ReducedBoundary

variable {n : ℕ} {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- **Membership in the reduced boundary via a given pair**. On an open `Ω`,
`reducedBoundary`, which quantifies existentially over Gauss–Green pairs, may be tested on any
given pair `(μ, ν)`: the pair is unique (`IsGaussGreenPair.unique`). -/
theorem IsGaussGreenPair.mem_reducedBoundary_iff (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω)
    {x : Rn n} :
    x ∈ reducedBoundary Ω E ↔ x ∈ Ω ∧ (∀ r, 0 < r → 0 < μ (ball x r)) ∧
      ∃ v : Rn n, ‖v‖ = 1 ∧
        Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0) (𝓝 v) := by
  constructor
  · rintro ⟨hxΩ, μ', ν', h', hpos, v, hv, hlim⟩
    obtain ⟨hμ, hν⟩ := h'.unique h hΩ
    subst hμ
    refine ⟨hxΩ, hpos, v, hv, hlim.congr fun r => ?_⟩
    rw [integral_congr_ae (ae_restrict_of_ae hν)]
  · rintro ⟨hxΩ, hpos, v, hv, hlim⟩
    exact ⟨hxΩ, μ, ν, h, hpos, v, hv, hlim⟩

/-- Local form of the differentiation theorem for a Gauss–Green pair: for `μ`-a.e. `x` in a ball
`V` compactly contained in `Ω`, `x` is in the reduced boundary and the normal averages converge to
`ν(x)`. -/
private theorem IsGaussGreenPair.ae_restrict_ball (h : IsGaussGreenPair Ω E μ ν) {z : Rn n}
    {ε : ℝ} (hzΩ : closedBall z ε ⊆ Ω) :
    ∀ᵐ x ∂μ.restrict (ball z ε), x ∈ Ω ∧ (∀ r, 0 < r → 0 < μ (ball x r)) ∧
      Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
        (𝓝 (ν x)) := by
  set V := ball z ε
  have hVfin : μ V ≠ ∞ := ne_top_of_le_ne_top
    (h.lt_top_of_isCompact _ (isCompact_closedBall z ε) hzΩ).ne
    (measure_mono ball_subset_closedBall)
  haveI : IsFiniteMeasure (μ.restrict V) := isFiniteMeasure_restrict.2 hVfin
  have hint : Integrable ν (μ.restrict V) :=
    Integrable.of_bound h.measurable_normal.aestronglyMeasurable 1
      (by filter_upwards [ae_restrict_of_ae h.norm_normal] with x hx using hx.le)
  filter_upwards [ae_tendsto_average_ball hint.locallyIntegrable,
    ae_restrict_mem measurableSet_ball, ae_restrict_of_ae h.norm_normal] with x hx hxV hν
  -- For small `r`, averages over `B_r(x)` for `μ⌊V` and for `μ` coincide.
  obtain ⟨η, hη, hηV⟩ := Metric.isOpen_iff.1 isOpen_ball x hxV
  have heq : ∀ᶠ r in 𝓝[>] 0, ⨍ y in ball x r, ν y ∂(μ.restrict V) =
      (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ := by
    filter_upwards [Ioo_mem_nhdsGT hη] with r hr
    have hsub : ball x r ⊆ V := (ball_subset_ball hr.2.le).trans hηV
    rw [setAverage_eq, measureReal_def, Measure.restrict_apply measurableSet_ball,
      inter_eq_left.2 hsub, Measure.restrict_restrict measurableSet_ball, inter_eq_left.2 hsub]
  have hlim := hx.congr' heq
  refine ⟨hzΩ (ball_subset_closedBall hxV), fun r hr => ?_, hlim⟩
  -- Positivity: otherwise the averages vanish for small radii.
  by_contra hr0
  rw [not_lt, nonpos_iff_eq_zero] at hr0
  have hzero : ∀ᶠ s in 𝓝[>] 0, (μ (ball x s)).toReal⁻¹ • ∫ y in ball x s, ν y ∂μ = 0 := by
    filter_upwards [Ioo_mem_nhdsGT hr] with s hs
    rw [measure_mono_null (ball_subset_ball hs.2.le) hr0, ENNReal.toReal_zero, inv_zero,
      zero_smul]
  have : ν x = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm))
  rw [this, norm_zero] at hν
  exact zero_ne_one hν

/-- **Differentiation of the normal** (EG Thm 1.32 applied to `ν`, open balls). For `μ`-a.e. `x`,
`(μ(B_r(x)))⁻¹ ∫_{B_r(x)} ν dμ → ν(x)` as `r → 0+`. -/
theorem IsGaussGreenPair.ae_tendsto_average_normal (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) :
    ∀ᵐ x ∂μ, x ∈ Ω ∧ (∀ r, 0 < r → 0 < μ (ball x r)) ∧
      Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
        (𝓝 (ν x)) := by
  -- Cover `Ω` by countably many balls compactly contained in `Ω`.
  have hball : ∀ z : Ω, ∃ ε > 0, closedBall (z : Rn n) ε ⊆ Ω := fun z => by
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ z z.2
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεΩ⟩
  choose ε hε hεΩ using hball
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : Ω => ball (z : Rn n) (ε z)) fun z => isOpen_ball
  have hcover : Ω = ⋃ z ∈ T, ball (z : Rn n) (ε z) := by
    rw [hTU]
    refine subset_antisymm (fun x hx => ?_) (iUnion_subset fun z => ?_)
    · exact mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hε _)⟩
    · exact ball_subset_closedBall.trans (hεΩ z)
  have hΩae := (ae_restrict_biUnion_iff (μ := μ) _ hTc (fun x => x ∈ Ω ∧
      (∀ r, 0 < r → 0 < μ (ball x r)) ∧
      Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
        (𝓝 (ν x)))).2 fun z _ => h.ae_restrict_ball (hεΩ z)
  rw [← hcover] at hΩae
  have hμΩ : μ.restrict Ω = μ := by
    rw [Measure.restrict_eq_self_of_ae_mem]
    rw [ae_iff]
    simpa [compl_def] using h.measure_compl
  rwa [hμΩ] at hΩae

/-- **`μ`-almost every point is in the reduced boundary** (EG, remark after Def 5.4). -/
theorem IsGaussGreenPair.ae_mem_reducedBoundary (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) :
    ∀ᵐ x ∂μ, x ∈ reducedBoundary Ω E := by
  filter_upwards [h.ae_tendsto_average_normal hΩ, h.norm_normal] with x hx hν
  exact (h.mem_reducedBoundary_iff hΩ).2 ⟨hx.1, hx.2.1, ν x, hν, hx.2.2⟩

/-- **The reduced boundary has full measure** (EG, remark after Def 5.4): `μ((∂*E)ᶜ) = 0`. -/
theorem IsGaussGreenPair.measure_compl_reducedBoundary (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) : μ (reducedBoundary Ω E)ᶜ = 0 :=
  ae_iff.1 (h.ae_mem_reducedBoundary hΩ)

/-- **The reduced boundary has full measure** (EG, remark after Def 5.4): `μ(Ω ∖ ∂*E) = 0`. -/
theorem IsGaussGreenPair.measure_diff_reducedBoundary (h : IsGaussGreenPair Ω E μ ν)
    (hΩ : IsOpen Ω) : μ (Ω \ reducedBoundary Ω E) = 0 :=
  measure_mono_null (diff_subset_compl _ _) (h.measure_compl_reducedBoundary hΩ)

end ReducedBoundary

/-! ### The essential boundary (EG Def 5.7, Lemma 5.9) -/

section EssentialBoundary

variable {n : ℕ}

/-- `volume (E ∩ B_r(x)) / volume (B_r(x))`, the Lebesgue density ratio in `ℝ≥0∞`. -/
private theorem densityRatio_le_one (E : Set (Rn n)) (x : Rn n) (r : ℝ) :
    volume (E ∩ ball x r) / volume (ball x r) ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)

/-- `HasDensity` in terms of the `ℝ≥0∞`-valued ratio `volume (E ∩ B_r(x)) / volume (B_r(x))`. -/
theorem hasDensity_iff_tendsto_div {E : Set (Rn n)} {x : Rn n} {d : ℝ≥0∞} (hd : d ≠ ∞) :
    HasDensity E x d.toReal ↔
      Tendsto (fun r => volume (E ∩ ball x r) / volume (ball x r)) (𝓝[>] 0) (𝓝 d) := by
  rw [HasDensity, ← ENNReal.tendsto_toReal_iff (fun r => ne_top_of_le_ne_top ENNReal.one_ne_top
    (densityRatio_le_one E x r)) hd]
  simp only [ENNReal.toReal_div]

/-- `HasDensity` depends on `E` only through its measurable hull. -/
theorem hasDensity_toMeasurable_iff {E : Set (Rn n)} {x : Rn n} {d : ℝ} :
    HasDensity (toMeasurable volume E) x d ↔ HasDensity E x d := by
  simp only [HasDensity, Measure.measure_toMeasurable_inter_of_sFinite measurableSet_ball]

/-- `volume (B_r(x)) = ω_n rⁿ` with `ω_n = volume (B_1(0))`, for `r > 0`. -/
private theorem volume_ball_eq_ofReal_mul {x : Rn n} {r : ℝ} (hr : 0 < r) :
    volume (ball x r) = ENNReal.ofReal (r ^ n) * volume (ball (0 : Rn n) 1) := by
  rw [Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin]

/-- **Density `0`, normalized by `rⁿ`.** `E` has density `0` at `x` iff
`volume (E ∩ B_r(x)) / rⁿ → 0` as `r → 0+`. -/
theorem hasDensity_zero_iff_tendsto {E : Set (Rn n)} {x : Rn n} :
    HasDensity E x 0 ↔
      Tendsto (fun r => volume (E ∩ ball x r) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) (𝓝 0) := by
  set c := volume (ball (0 : Rn n) 1)
  have hc0 : c ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hctop : c ≠ ∞ := measure_ball_lt_top.ne
  -- For `r > 0`: `ratio = (volume (E ∩ B_r) / rⁿ) * c⁻¹`.
  have hratio : ∀ r, 0 < r → volume (E ∩ ball x r) / volume (ball x r) =
      volume (E ∩ ball x r) / ENNReal.ofReal (r ^ n) * c⁻¹ := by
    intro r hr
    have hrn : ENNReal.ofReal (r ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hr n)).ne'
    rw [volume_ball_eq_ofReal_mul hr, div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
      ENNReal.mul_inv (Or.inl hrn) (Or.inl ENNReal.ofReal_ne_top)]
  have h0 := hasDensity_iff_tendsto_div (E := E) (x := x) (d := 0) ENNReal.zero_ne_top
  rw [ENNReal.toReal_zero] at h0
  rw [h0]
  constructor
  · intro h
    have := ENNReal.Tendsto.mul_const h (Or.inr hctop)
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hratio r hr, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
  · intro h
    have := ENNReal.Tendsto.mul_const h (Or.inr (ENNReal.inv_ne_top.2 hc0))
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hratio r hr]

/-- **Density `1` of `E` is density `0` of the complement** (`E` null-measurable). -/
theorem hasDensity_compl_zero_iff {E : Set (Rn n)} (hE : NullMeasurableSet E volume)
    {x : Rn n} : HasDensity Eᶜ x 0 ↔ HasDensity E x 1 := by
  -- For `r > 0` the two real ratios add up to `1`.
  have hsum : ∀ r, 0 < r → (volume (Eᶜ ∩ ball x r)).toReal / (volume (ball x r)).toReal =
      1 - (volume (E ∩ ball x r)).toReal / (volume (ball x r)).toReal := by
    intro r hr
    have hB0 : (volume (ball x r)).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨(measure_ball_pos volume x hr).ne', measure_ball_lt_top.ne⟩
    have hadd := measure_inter_add_diff₀ (μ := volume) (ball x r) hE
    rw [inter_comm, diff_eq, inter_comm (ball x r) Eᶜ] at hadd
    have hadd' : (volume (E ∩ ball x r)).toReal + (volume (Eᶜ ∩ ball x r)).toReal =
        (volume (ball x r)).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne)
        (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne), hadd]
    field_simp
    linarith
  constructor
  · intro h
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hsum r hr]; ring
  · intro h
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    rw [sub_self] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [hsum r hr]

/-- A nonnegative extended-real function tends to `0` iff its `limsup` is `0`. -/
private theorem tendsto_zero_iff_limsup_eq_zero {u : ℝ → ℝ≥0∞} {l : Filter ℝ} [l.NeBot] :
    Tendsto u l (𝓝 0) ↔ limsup u l = 0 := by
  refine ⟨fun h => h.limsup_eq, fun h => ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_⟩
  exact (eventually_lt_of_limsup_lt (h ▸ hε)).mono fun _ h => h.le

/-- Open and closed balls carry the same Lebesgue measure of `E ∩ ·` for `r ≠ 0`. -/
private theorem volume_closedBall_inter_eq {E : Set (Rn n)} {x : Rn n} {r : ℝ} (hr : r ≠ 0) :
    volume (closedBall x r ∩ E) = volume (E ∩ ball x r) := by
  refine le_antisymm ?_ (measure_mono fun y ⟨hyE, hyB⟩ => ⟨ball_subset_closedBall hyB, hyE⟩)
  calc volume (closedBall x r ∩ E) ≤ volume (E ∩ ball x r ∪ sphere x r) := by
        refine measure_mono fun y ⟨hyB, hyE⟩ => ?_
        rw [← ball_union_sphere] at hyB
        rcases hyB with hyB | hyS
        · exact Or.inl ⟨hyE, hyB⟩
        · exact Or.inr hyS
    _ ≤ volume (E ∩ ball x r) + volume (sphere x r) := measure_union_le _ _
    _ = volume (E ∩ ball x r) := by
        rw [Measure.addHaar_sphere_of_ne_zero volume x hr, add_zero]

/-- EG's normalized closed-ball ratio tends to `0` iff density `0` (`HasDensity E x 0`) holds. -/
private theorem hasDensity_zero_iff_limsup {E : Set (Rn n)} {x : Rn n} :
    HasDensity E x 0 ↔
      limsup (fun r => volume (closedBall x r ∩ E) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) = 0 := by
  rw [hasDensity_zero_iff_tendsto, ← tendsto_zero_iff_limsup_eq_zero]
  refine tendsto_congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [volume_closedBall_inter_eq hr.ne']

/-- **The essential boundary is EG's measure-theoretic boundary** (EG Def 5.7). For a
Lebesgue-measurable `E`, `x ∈ ∂ᵉE` iff
`limsup_{r→0} |B̄_r(x) ∩ E|/rⁿ > 0` and `limsup_{r→0} |B̄_r(x) ∖ E|/rⁿ > 0`.
EG's `B(x, r)` is the closed ball; with open balls the ratios are the same for `r > 0`. -/
theorem mem_essentialBoundary_iff_limsup {E : Set (Rn n)} (hE : NullMeasurableSet E volume)
    {x : Rn n} :
    x ∈ essentialBoundary E ↔
      0 < limsup (fun r => volume (closedBall x r ∩ E) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) ∧
      0 < limsup (fun r => volume (closedBall x r \ E) / ENNReal.ofReal (r ^ n)) (𝓝[>] 0) := by
  simp only [essentialBoundary, mem_setOf_eq, pos_iff_ne_zero]
  rw [← hasDensity_compl_zero_iff hE, hasDensity_zero_iff_limsup, hasDensity_zero_iff_limsup]
  simp only [diff_eq]

/-- `rⁿ`-normalized characterization of density `0` along rational radii, for the Borel
measurability of the density-`0` set. -/
private theorem hasDensity_zero_iff_rat {E : Set (Rn n)} {x : Rn n} :
    HasDensity E x 0 ↔ ∀ k : ℕ, ∃ m : ℕ, ∀ q : ℚ, 0 < q → (q : ℝ) < ((m : ℝ) + 1)⁻¹ →
      volume (E ∩ ball x q) ≤ ((k : ℝ≥0∞) + 1)⁻¹ * ENNReal.ofReal ((q : ℝ) ^ n) := by
  rw [hasDensity_zero_iff_tendsto, ENNReal.tendsto_nhds_zero]
  constructor
  · intro h k
    have hk : (0 : ℝ≥0∞) < ((k : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
    obtain ⟨δ, hδ, hδU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (h _ hk)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (mem_Ioi.1 hδ)
    refine ⟨m, fun q hq hqm => ?_⟩
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have := hδU ⟨hq', hqm.trans (by simpa [one_div] using hm)⟩
    simp only [mem_setOf_eq] at this
    rwa [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 (pow_pos hq' n)).ne' ENNReal.ofReal_ne_top]
      at this
  · intro h ε hε
    have h2 : (0 : ℝ≥0∞) < 2 ^ n := by positivity
    have h2' : (2 : ℝ≥0∞) ^ n ≠ ∞ := by simp
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (ENNReal.div_pos hε.ne' h2').ne'
    obtain ⟨m, hm⟩ := h k
    have hm0 : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
    filter_upwards [Ioo_mem_nhdsGT (half_pos hm0)] with r hr
    obtain ⟨q, hrq, hq2r⟩ := exists_rat_btwn (show r < 2 * r by linarith [hr.1])
    have hq : (0 : ℝ) < q := hr.1.trans hrq
    have hqm : (q : ℝ) < ((m : ℝ) + 1)⁻¹ := by linarith [hr.2]
    have hbound := hm q (by exact_mod_cast hq) hqm
    rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 (pow_pos hr.1 n)).ne' ENNReal.ofReal_ne_top]
    have hkle : ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    calc volume (E ∩ ball x r) ≤ volume (E ∩ ball x q) :=
          measure_mono (inter_subset_inter_right _ (ball_subset_ball hrq.le))
      _ ≤ ((k : ℝ≥0∞) + 1)⁻¹ * ENNReal.ofReal ((q : ℝ) ^ n) := hbound
      _ ≤ (ε / 2 ^ n) * (2 ^ n * ENNReal.ofReal (r ^ n)) := by
          gcongr
          · exact hkle.trans hk.le
          · rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow zero_le_two,
              ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
            exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hq.le hq2r.le n)
      _ = ε * ENNReal.ofReal (r ^ n) := by
          rw [← mul_assoc, ENNReal.div_mul_cancel h2.ne' h2']

/-- `x ↦ volume (E ∩ B_q(x))` is measurable for measurable `E`. -/
private theorem measurable_volume_inter_ball {E : Set (Rn n)} (hE : MeasurableSet E) (q : ℝ) :
    Measurable fun x : Rn n => volume (E ∩ ball x q) := by
  have hS : MeasurableSet {p : Rn n × Rn n | p.2 ∈ E ∧ dist p.2 p.1 < q} :=
    (measurable_snd hE).inter (measurableSet_lt (measurable_snd.dist measurable_fst)
      measurable_const)
  exact measurable_measure_prodMk_left hS

/-- **The density-`0` set is Borel** (EG Lemma 5.9 (i), for the measure-theoretic exterior `O`),
for an arbitrary `E ⊆ ℝⁿ`. -/
theorem measurableSet_setOf_hasDensity_zero (E : Set (Rn n)) :
    MeasurableSet {x | HasDensity E x 0} := by
  set E' := toMeasurable volume E
  have hE' : MeasurableSet E' := measurableSet_toMeasurable _ _
  have hset : {x | HasDensity E x 0} = ⋂ k : ℕ, ⋃ m : ℕ, ⋂ q : ℚ,
      {x | 0 < q → (q : ℝ) < ((m : ℝ) + 1)⁻¹ →
        volume (E' ∩ ball x q) ≤ ((k : ℝ≥0∞) + 1)⁻¹ * ENNReal.ofReal ((q : ℝ) ^ n)} := by
    ext x
    simp only [mem_setOf_eq, mem_iInter, mem_iUnion]
    rw [← hasDensity_toMeasurable_iff, hasDensity_zero_iff_rat]
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun m =>
    MeasurableSet.iInter fun q => ?_
  by_cases hq : 0 < q ∧ (q : ℝ) < ((m : ℝ) + 1)⁻¹
  · simp only [hq.1, hq.2, forall_const]
    exact measurableSet_le (measurable_volume_inter_ball hE' q) measurable_const
  · have : {x : Rn n | 0 < q → (q : ℝ) < ((m : ℝ) + 1)⁻¹ →
        volume (E' ∩ ball x q) ≤ ((k : ℝ≥0∞) + 1)⁻¹ * ENNReal.ofReal ((q : ℝ) ^ n)} = univ := by
      ext x
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact fun h1 h2 => absurd ⟨h1, h2⟩ hq
    rw [this]
    exact MeasurableSet.univ

/-- **The density-`1` set is Borel** (EG Lemma 5.9 (i), for the measure-theoretic interior `I`),
for an arbitrary `E ⊆ ℝⁿ`. -/
theorem measurableSet_setOf_hasDensity_one (E : Set (Rn n)) :
    MeasurableSet {x | HasDensity E x 1} := by
  have hset : {x | HasDensity E x 1} = {x | HasDensity (toMeasurable volume E)ᶜ x 0} := by
    ext x
    simp only [mem_setOf_eq]
    rw [hasDensity_compl_zero_iff (measurableSet_toMeasurable _ _).nullMeasurableSet,
      hasDensity_toMeasurable_iff]
  rw [hset]
  exact measurableSet_setOf_hasDensity_zero _

/-- **The essential boundary is Borel** (EG Lemma 5.9 (i)), for an arbitrary `E ⊆ ℝⁿ`. -/
theorem measurableSet_essentialBoundary (E : Set (Rn n)) :
    MeasurableSet (essentialBoundary E) := by
  have : essentialBoundary E = ({x | HasDensity E x 0} ∪ {x | HasDensity E x 1})ᶜ := by
    ext x
    simp [essentialBoundary]
  rw [this]
  exact ((measurableSet_setOf_hasDensity_zero E).union
    (measurableSet_setOf_hasDensity_one E)).compl

/-- **`E` agrees a.e. with its measure-theoretic interior** (EG Lemma 5.9 (ii)): for a
Lebesgue-measurable `E` and `I := {x | HasDensity E x 1}`, `|(E ∖ I) ∪ (I ∖ E)| = 0`. -/
theorem volume_diff_union_diff_setOf_hasDensity_one {E : Set (Rn n)}
    (hE : NullMeasurableSet E volume) :
    volume ((E \ {x | HasDensity E x 1}) ∪ ({x | HasDensity E x 1} \ E)) = 0 := by
  have h1 : (1 : ℝ≥0∞).toReal = 1 := ENNReal.toReal_one
  -- a.e. point of `E` has density `1`
  have hE1 : ∀ᵐ x ∂volume, x ∈ E → HasDensity E x 1 := by
    refine (ae_restrict_iff'₀ hE).1 ?_
    filter_upwards [ae_tendsto_measure_inter_ball_div volume E] with x hx
    rw [← h1, hasDensity_iff_tendsto_div ENNReal.one_ne_top]
    exact hx
  -- a.e. point of `Eᶜ` has density `0`, hence not `1`
  have hEc : ∀ᵐ x ∂volume, x ∈ Eᶜ → ¬ HasDensity E x 1 := by
    refine (ae_restrict_iff'₀ hE.compl).1 ?_
    filter_upwards [ae_tendsto_measure_inter_ball_div volume Eᶜ] with x hx h
    have hc1 : HasDensity Eᶜ x 1 := by
      rw [← h1, hasDensity_iff_tendsto_div ENNReal.one_ne_top]
      exact hx
    have hc0 : HasDensity E x 0 := by
      have := (hasDensity_compl_zero_iff hE.compl (x := x)).2 hc1
      rwa [compl_compl] at this
    exact zero_ne_one (tendsto_nhds_unique hc0 h)
  refine measure_union_null ?_ ?_
  · exact measure_mono_null (fun x ⟨hxE, hxI⟩ => fun h => hxI (h hxE)) (ae_iff.1 hE1)
  · exact measure_mono_null (fun x ⟨hxI, hxE⟩ => fun h => h hxE hxI) (ae_iff.1 hEc)

end EssentialBoundary

end GMTFoundations
