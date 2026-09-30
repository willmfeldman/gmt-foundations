/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.GMT.Rectifiable
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Approximate tangent planes and density of rectifiable sets

Let `S ⊆ Ω` be a measurable, countably `(n-1)`-rectifiable set with locally finite `ℋ^{n-1}` measure
in the open set `Ω`. We work with `μ = μHE[n-1]`.

* `IsNegligibleAt k A x`: `μ(A ∩ B̄_r(x)) = o(r^k)`.
* `IsGoodPiece k S G ν ε x`: `x` lies in the measurable `ε`-flat piece `G ⊆ S` with normal `ν`,
  `S \ G` is negligible at `x`, and `ν^⊥ \ π(G)` is negligible at `π x`.
* `measure_not_forall_exists_isGoodPiece`: `μ`-a.e. `x ∈ S` has good pieces for every
  `ε = 1/(m+2)`. The proof uses Besicovitch's density theorem twice (for `μ⌊S` localized, and for
  `μ⌊ν^⊥`) and the flat-piece cover of `GMT/Rectifiable.lean`.
* `tendsto_measure_inter_closedBall_div`: at such points `μ(S ∩ B̄_r(x)) / (ω_{n-1} r^{n-1}) → 1`.
* `tendsto_integral_blowup`: at such points there is a unit `ν` such that
  `r^{1-n} ∫_S φ((y - x)/r) dμ → ∫_{ν^⊥} φ dμ` for every continuous compactly supported `φ`.
* `hausdorffN_not_approxTangent_eq_zero`: `ℋ^{n-1}`-a.e. point of `S` has an approximate tangent
  plane in this sense, assuming the normalization `ℋ^{n-1} = ℒ^{n-1}` on `ℝ^{n-1}`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace GMTFoundations.GMT

variable {n : ℕ}

/-- Countable rectifiability is monotone under `⊆`. -/
theorem _root_.GMTFoundations.IsCountablyRectifiable.mono {k : ℕ} {S T : Set (Rn n)}
    (h : IsCountablyRectifiable n k T) (hST : S ⊆ T) : IsCountablyRectifiable n k S := by
  obtain ⟨f, hf, hnull⟩ := h
  exact ⟨f, hf, measure_mono_null (sdiff_subset_sdiff_left hST) hnull⟩

/-! ### Negligible sets -/

/-- `A` is `k`-negligible at `x`: `μHE[k](A ∩ B̄_r(x)) = o(r^k)` as `r → 0+`. -/
def IsNegligibleAt (k : ℕ) (A : Set (Rn n)) (x : Rn n) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ r in 𝓝[>] (0 : ℝ),
    (μHE[k] : Measure (Rn n)) (A ∩ closedBall x r) ≤ ENNReal.ofReal (η * r ^ k)

theorem IsNegligibleAt.mono {k : ℕ} {A B : Set (Rn n)} {x : Rn n} (h : IsNegligibleAt k A x)
    (hBA : B ⊆ A) : IsNegligibleAt k B x :=
  fun η hη => (h η hη).mono fun _ hr => (measure_mono (inter_subset_inter_left _ hBA)).trans hr

theorem tendsto_const_mul_nhdsGT {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ => R * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun r (hr : 0 < r) =>
    mul_pos hR hr⟩
  have : Tendsto (fun r : ℝ => R * r) (𝓝 0) (𝓝 (R * 0)) := tendsto_const_nhds.mul tendsto_id
  rw [mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem IsNegligibleAt.scale {k : ℕ} {A : Set (Rn n)} {x : Rn n} (h : IsNegligibleAt k A x)
    {R : ℝ} (hR : 0 < R) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (μHE[k] : Measure (Rn n)) (A ∩ closedBall x (R * r)) ≤ ENNReal.ofReal (η * r ^ k) := by
  have := (tendsto_const_mul_nhdsGT hR).eventually (h (η / R ^ k) (by positivity))
  refine this.mono fun r hr => hr.trans_eq ?_
  congr 1
  rw [mul_pow]
  field_simp

/-- If `ν(T ∩ B̄_r)/ν(B̄_r) → 1` and `ν(T ∩ B̄_r) = O(r^k)`, then `B̄_r \ T` has `ν`-measure
`o(r^k)`. -/
theorem measure_closedBall_diff_le_of_tendsto {k : ℕ} {ν : Measure (Rn n)} {T : Set (Rn n)}
    (hT : MeasurableSet T) {x : Rn n} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hTb : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (T ∩ closedBall x r) ≤ c * ENNReal.ofReal (r ^ k))
    (hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (closedBall x r) ≠ ∞)
    (hlim : Tendsto (fun r => ν (T ∩ closedBall x r) / ν (closedBall x r)) (𝓝[>] 0) (𝓝 1))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (closedBall x r \ T) ≤ ENNReal.ofReal (η * r ^ k) := by
  set q := fun r => ν (T ∩ closedBall x r) / ν (closedBall x r) with hq_def
  have h1 : Tendsto (fun r => 2 * c * (1 - q r)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun r => 1 - q r) (𝓝[>] 0) (𝓝 (1 - 1)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds hlim (Or.inl ENNReal.one_ne_top)
    rw [tsub_self] at this
    simpa using ENNReal.Tendsto.const_mul this (Or.inr (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hc))
  have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * c * (1 - q r) < ENNReal.ofReal η :=
    (tendsto_order.1 h1).2 _ (ENNReal.ofReal_pos.2 hη)
  have h3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2⁻¹ < q r :=
    (tendsto_order.1 hlim).1 _ (ENNReal.inv_lt_one.2 (by norm_num))
  filter_upwards [hTb, hfin, h2, h3] with r hTbr hfinr h2r h3r
  set a := ν (T ∩ closedBall x r)
  set b := ν (closedBall x r)
  have hab : a ≤ b := measure_mono inter_subset_right
  have hb0 : b ≠ 0 := by
    intro hb
    have ha : a = 0 := le_antisymm (hb ▸ hab) (by simp)
    have : q r = 0 := by simp only [hq_def, a, b] at ha hb ⊢; rw [ha, hb, ENNReal.zero_div]
    rw [this] at h3r
    exact (not_lt_of_ge (by simp)) h3r
  have hq : q r * b = a := ENNReal.div_mul_cancel hb0 hfinr
  have hdiff : ν (closedBall x r \ T) = b - a := by
    rw [← sdiff_inter_self_eq_sdiff, measure_sdiff inter_subset_right
      (hT.inter measurableSet_closedBall).nullMeasurableSet (ne_top_of_le_ne_top hfinr hab)]
  have hb2 : b ≤ 2 * a := by
    have : 2⁻¹ * b ≤ a := ENNReal.mul_le_of_le_div h3r.le
    calc b = 2 * (2⁻¹ * b) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ ≤ 2 * a := by gcongr
  calc ν (closedBall x r \ T) = b - a := hdiff
    _ = b * (1 - q r) := by rw [ENNReal.mul_sub (fun _ _ => hfinr), mul_one, mul_comm, hq]
    _ ≤ (2 * a) * (1 - q r) := by gcongr
    _ ≤ (2 * (c * ENNReal.ofReal (r ^ k))) * (1 - q r) := by gcongr
    _ = 2 * c * (1 - q r) * ENNReal.ofReal (r ^ k) := by ring
    _ ≤ ENNReal.ofReal η * ENNReal.ofReal (r ^ k) := by gcongr
    _ = ENNReal.ofReal (η * r ^ k) := (ENNReal.ofReal_mul hη.le).symm

/-! ### Good pieces -/

/-- `G` is a good `ε`-flat piece of `S` at `x` with normal `ν`. -/
structure IsGoodPiece (k : ℕ) (S G : Set (Rn n)) (ν : Rn n) (ε : ℝ) (x : Rn n) : Prop where
  mem : x ∈ G
  subset : G ⊆ S
  measurableSet : MeasurableSet G
  norm_eq : ‖ν‖ = 1
  flat : IsFlatPiece ν ε G
  negligible_diff : IsNegligibleAt k (S \ G) x
  negligible_proj : IsNegligibleAt k (hyperplane ν \ projH ν '' G) (projH ν x)

theorem ne_zero_of_norm_eq_one {ν : Rn n} (hν : ‖ν‖ = 1) : ν ≠ 0 := by
  rintro rfl
  simp at hν

theorem measure_hyperplane_inter_closedBall (hn : 2 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1) {p : Rn n}
    (hp : p ∈ hyperplane ν) {r : ℝ} (hr : 0 ≤ r) :
    (μHE[n - 1] : Measure (Rn n)) (hyperplane ν ∩ closedBall p r) =
      ENNReal.ofReal (unitBallVolume (n - 1)) * ENNReal.ofReal (r ^ (n - 1)) := by
  rw [euclideanHausdorffMeasure_hyperplane_inter_closedBall hn (ne_zero_of_norm_eq_one hν) hp hr,
    ENNReal.ofReal_mul (unitBallVolume_pos _).le]

theorem isLocallyFiniteMeasure_restrict_hyperplane (hn : 2 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1) :
    IsLocallyFiniteMeasure ((μHE[n - 1] : Measure (Rn n)).restrict (hyperplane ν)) := by
  refine ⟨fun x => ⟨closedBall x 1, closedBall_mem_nhds x one_pos, ?_⟩⟩
  rw [Measure.restrict_apply measurableSet_closedBall]
  calc (μHE[n - 1] : Measure (Rn n)) (closedBall x 1 ∩ hyperplane ν)
      ≤ μHE[n - 1] (hyperplane ν ∩ closedBall (projH ν x) 1) := by
        refine measure_mono fun p ⟨hpB, hpH⟩ => ⟨hpH, ?_⟩
        rw [mem_closedBall, dist_eq_norm] at hpB ⊢
        calc ‖p - projH ν x‖ = ‖projH ν p - projH ν x‖ := by rw [projH_of_mem hpH]
          _ ≤ ‖p - x‖ := norm_projH_sub_le hν p x
          _ ≤ 1 := hpB
    _ < ∞ := by
        rw [measure_hyperplane_inter_closedBall hn hν (projH_mem_hyperplane hν x) zero_le_one]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem IsFlatPiece.measurableSet_image_projH {ν : Rn n} {ε : ℝ} {G : Set (Rn n)}
    (h : IsFlatPiece ν ε G) (hν : ‖ν‖ = 1) (hε : ε < 1) (hG : MeasurableSet G) :
    MeasurableSet (projH ν '' G) :=
  hG.image_of_continuousOn_injOn (continuous_projH ν).continuousOn (h.injOn_projH hν hε)

/-- Almost every point of a flat piece `G ⊆ S` (with `μ(S) < ∞`) is a good point. -/
theorem measure_not_isGoodPiece (hn : 2 ≤ n) {S G : Set (Rn n)}
    (hSfin : (μHE[n - 1] : Measure (Rn n)) S ≠ ∞) (hGm : MeasurableSet G) (hGS : G ⊆ S)
    {ν : Rn n} (hν : ‖ν‖ = 1) {ε : ℝ} (hε : ε < 1) (hflat : IsFlatPiece ν ε G) :
    (μHE[n - 1] : Measure (Rn n)) {x | x ∈ G ∧ ¬ IsGoodPiece (n - 1) S G ν ε x} = 0 := by
  set μ : Measure (Rn n) := μHE[n - 1]
  set k := n - 1
  have hsub : {x | x ∈ G ∧ ¬ IsGoodPiece k S G ν ε x} ⊆
      {x | x ∈ G ∧ ¬ IsNegligibleAt k (S \ G) x} ∪
        {x | x ∈ G ∧ ¬ IsNegligibleAt k (hyperplane ν \ projH ν '' G) (projH ν x)} := by
    rintro x ⟨hxG, hx⟩
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_and, not_not] at hc
    exact hx ⟨hxG, hGS, hGm, hν, hflat, hc.1 hxG, hc.2 hxG⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · -- `S \ G` is negligible: Besicovitch for `μ⌊S`
    have : IsFiniteMeasure (μ.restrict S) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hSfin.lt_top⟩
    have hae := Besicovitch.ae_tendsto_measure_inter_div (μ.restrict S) G
    rw [Measure.restrict_restrict hGm, inter_eq_left.2 hGS, ae_restrict_iff' hGm] at hae
    refine measure_mono_null ?_ (ae_iff.1 hae)
    rintro x ⟨hxG, hx⟩ hlim
    apply hx
    intro η hη
    have hTb : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ.restrict S (G ∩ closedBall x r) ≤
        (flatConst ε ^ k * ENNReal.ofReal (unitBallVolume k)) * ENNReal.ofReal (r ^ k) := by
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      calc μ.restrict S (G ∩ closedBall x r) ≤ μ (G ∩ closedBall x r) :=
            Measure.restrict_apply_le _ _
        _ ≤ flatConst ε ^ k * μ (hyperplane ν ∩ closedBall (projH ν x) r) :=
            hflat.measure_inter_closedBall_le k hν hε x r
        _ = _ := by
            rw [measure_hyperplane_inter_closedBall hn hν (projH_mem_hyperplane hν x) hr.le,
              mul_assoc]
    have := measure_closedBall_diff_le_of_tendsto hGm
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (flatConst_ne_top ε)) ENNReal.ofReal_ne_top) hTb
      (Eventually.of_forall fun r => measure_ne_top _ _) (hlim hxG) η hη
    refine this.mono fun r hr => le_trans (le_of_eq ?_) hr
    rw [Measure.restrict_apply (measurableSet_closedBall.diff hGm)]
    congr 1
    ext y
    simp only [mem_inter_iff, Set.mem_sdiff]
    tauto
  · -- `ν^⊥ \ π(G)` is negligible: Besicovitch for `μ⌊ν^⊥`
    have := isLocallyFiniteMeasure_restrict_hyperplane hn hν
    have hπm : MeasurableSet (projH ν '' G) := hflat.measurableSet_image_projH hν hε hGm
    have hπH : projH ν '' G ⊆ hyperplane ν := by
      rintro _ ⟨y, -, rfl⟩
      exact projH_mem_hyperplane hν y
    have hae := Besicovitch.ae_tendsto_measure_inter_div (μ.restrict (hyperplane ν)) (projH ν '' G)
    rw [Measure.restrict_restrict hπm, inter_eq_left.2 hπH, ae_restrict_iff' hπm] at hae
    set N := {p | ¬ (p ∈ projH ν '' G → Tendsto (fun r => μ.restrict (hyperplane ν)
      (projH ν '' G ∩ closedBall p r) / μ.restrict (hyperplane ν) (closedBall p r)) (𝓝[>] 0)
        (𝓝 1))}
    have hN : μ N = 0 := ae_iff.1 hae
    have hsub2 : {x | x ∈ G ∧ ¬ IsNegligibleAt k (hyperplane ν \ projH ν '' G) (projH ν x)} ⊆
        G ∩ projH ν ⁻¹' N := by
      rintro x ⟨hxG, hx⟩
      refine ⟨hxG, fun hlim => hx ?_⟩
      intro η hη
      have hp : projH ν x ∈ hyperplane ν := projH_mem_hyperplane hν x
      have hball : ∀ r, 0 ≤ r → μ.restrict (hyperplane ν) (closedBall (projH ν x) r) =
          ENNReal.ofReal (unitBallVolume k) * ENNReal.ofReal (r ^ k) := by
        intro r hr
        rw [Measure.restrict_apply measurableSet_closedBall, inter_comm,
          measure_hyperplane_inter_closedBall hn hν hp hr]
      have hTb : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ.restrict (hyperplane ν)
          (projH ν '' G ∩ closedBall (projH ν x) r) ≤
            ENNReal.ofReal (unitBallVolume k) * ENNReal.ofReal (r ^ k) := by
        filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
        exact (measure_mono inter_subset_right).trans (hball r hr.le).le
      have hfin : ∀ᶠ r in 𝓝[>] (0 : ℝ),
          μ.restrict (hyperplane ν) (closedBall (projH ν x) r) ≠ ∞ := by
        filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
        rw [hball r hr.le]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      have := measure_closedBall_diff_le_of_tendsto hπm ENNReal.ofReal_ne_top hTb hfin
        (hlim ⟨x, hxG, rfl⟩) η hη
      refine this.mono fun r hr => le_trans (le_of_eq ?_) hr
      rw [Measure.restrict_apply (measurableSet_closedBall.diff hπm)]
      congr 1
      ext y
      simp only [mem_inter_iff, Set.mem_sdiff]
      tauto
    refine measure_mono_null hsub2 ?_
    refine le_antisymm ((hflat.measure_le k hν hε inter_subset_left).trans ?_) (by simp)
    have : μ (projH ν '' (G ∩ projH ν ⁻¹' N)) = 0 :=
      measure_mono_null (image_subset_iff.2 inter_subset_right) hN
    rw [this, mul_zero]

/-- Almost every point of a rectifiable `S` with `μ(S) < ∞` has a good `ε`-flat piece. -/
theorem measure_not_exists_isGoodPiece_of_ne_top (hn : 2 ≤ n) {S : Set (Rn n)}
    (hS : MeasurableSet S) (hSfin : (μHE[n - 1] : Measure (Rn n)) S ≠ ∞)
    (hrect : IsCountablyRectifiable n (n - 1) S) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1) :
    (μHE[n - 1] : Measure (Rn n))
      {x | x ∈ S ∧ ¬ ∃ G ν, IsGoodPiece (n - 1) S G ν ε x} = 0 := by
  obtain ⟨G, ν, hGm, hν, hflat, hnull⟩ := hrect.exists_flatPiece_cover hn hε0
  refine measure_mono_null (t := (S \ ⋃ i, G i) ∪
      ⋃ i, {x | x ∈ G i ∩ S ∧ ¬ IsGoodPiece (n - 1) S (G i ∩ S) (ν i) ε x}) ?_
    (measure_union_null hnull (measure_iUnion_null fun i =>
      measure_not_isGoodPiece hn hSfin ((hGm i).inter hS) inter_subset_right (hν i) hε
        ((hflat i).mono inter_subset_left)))
  rintro x ⟨hxS, hx⟩
  by_cases hxG : x ∈ ⋃ i, G i
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hxG
    exact Or.inr (mem_iUnion.2 ⟨i, ⟨hi, hxS⟩, fun h => hx ⟨_, _, h⟩⟩)
  · exact Or.inl ⟨hxS, hxG⟩

/-- Almost every point of a rectifiable `S ⊆ Ω` with locally finite measure in `Ω` has a good
`ε`-flat piece. -/
theorem measure_not_exists_isGoodPiece (hn : 2 ≤ n) {Ω S : Set (Rn n)} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) (hrect : IsCountablyRectifiable n (n - 1) S)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → (μHE[n - 1] : Measure (Rn n)) (K ∩ S) ≠ ∞)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1) :
    (μHE[n - 1] : Measure (Rn n))
      {x | x ∈ S ∧ ¬ ∃ G ν, IsGoodPiece (n - 1) S G ν ε x} = 0 := by
  have hd : ∀ x ∈ Ω, ∃ d > 0, closedBall x (2 * d) ⊆ Ω := by
    intro x hx
    obtain ⟨e, he, hbe⟩ := Metric.isOpen_iff.1 hΩ x hx
    exact ⟨e / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hbe⟩
  choose! d hd0 hdΩ using hd
  obtain ⟨t, htS, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => ball x (d x)) (s := S)
    (fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hd0 x (hSΩ hx))))
  set T : Rn n → Set (Rn n) := fun x => S ∩ closedBall x (2 * d x)
  refine measure_mono_null (t := ⋃ x ∈ t,
      {y | y ∈ T x ∧ ¬ ∃ G ν, IsGoodPiece (n - 1) (T x) G ν ε y}) ?_
    ((measure_biUnion_null_iff htc).2 fun x hxt => ?_)
  · rintro y ⟨hyS, hy⟩
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcov hyS)
    have hdx := hd0 x (hSΩ (htS hxt))
    refine mem_iUnion₂.2 ⟨x, hxt, ⟨hyS, ?_⟩, ?_⟩
    · exact closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hyx)
    · rintro ⟨G, ν, hG⟩
      refine hy ⟨G, ν, hG.mem, hG.subset.trans inter_subset_left, hG.measurableSet, hG.norm_eq,
        hG.flat, fun η hη => ?_, hG.negligible_proj⟩
      filter_upwards [hG.negligible_diff η hη, Ioo_mem_nhdsGT hdx] with r hr hr'
      refine le_trans (le_of_eq ?_) hr
      congr 1
      ext z
      simp only [T, mem_inter_iff, Set.mem_sdiff, mem_closedBall]
      constructor
      · rintro ⟨⟨hzS, hzG⟩, hzr⟩
        refine ⟨⟨⟨hzS, ?_⟩, hzG⟩, hzr⟩
        have := dist_triangle z y x
        rw [mem_ball] at hyx
        linarith [hr'.2]
      · rintro ⟨⟨⟨hzS, -⟩, hzG⟩, hzr⟩
        exact ⟨⟨hzS, hzG⟩, hzr⟩
  · have hxΩ := hSΩ (htS hxt)
    refine measure_not_exists_isGoodPiece_of_ne_top hn (hS.inter measurableSet_closedBall) ?_
      (hrect.mono inter_subset_left) hε0 hε
    rw [inter_comm]
    exact hfin _ (isCompact_closedBall _ _) (hdΩ x hxΩ)

/-- Almost every point of a rectifiable `S ⊆ Ω` with locally finite measure in `Ω` has good
`1/(m+2)`-flat pieces for every `m`. -/
theorem measure_not_forall_exists_isGoodPiece (hn : 2 ≤ n) {Ω S : Set (Rn n)} (hΩ : IsOpen Ω)
    (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) (hrect : IsCountablyRectifiable n (n - 1) S)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → (μHE[n - 1] : Measure (Rn n)) (K ∩ S) ≠ ∞) :
    (μHE[n - 1] : Measure (Rn n))
      {x | x ∈ S ∧ ¬ ∀ m : ℕ, ∃ G ν, IsGoodPiece (n - 1) S G ν (1 / (m + 2)) x} = 0 := by
  refine measure_mono_null (t := ⋃ m : ℕ,
      {x | x ∈ S ∧ ¬ ∃ G ν, IsGoodPiece (n - 1) S G ν (1 / (m + 2)) x}) ?_
    (measure_iUnion_null fun m => measure_not_exists_isGoodPiece hn hΩ hS hSΩ hrect hfin
      (by positivity) ?_)
  · rintro x ⟨hxS, hx⟩
    push Not at hx
    obtain ⟨m, hm⟩ := hx
    exact mem_iUnion.2 ⟨m, hxS, fun ⟨G, ν, h⟩ => hm G ν h⟩
  · rw [div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-! ### Density one -/

theorem flatConst_pow (ε : ℝ) (hε : ε < 1) (k : ℕ) :
    flatConst ε ^ k = ENNReal.ofReal ((1 - ε)⁻¹ ^ k) := by
  rw [flatConst, ENNReal.ofReal_pow (inv_nonneg.2 (sub_nonneg.2 hε.le))]

/-- Measure bounds in balls from one good piece. -/
theorem IsGoodPiece.measure_bounds (hn : 2 ≤ n) {S G : Set (Rn n)} {ν x : Rn n} {ε : ℝ}
    (hG : IsGoodPiece (n - 1) S G ν ε x) (hε : ε < 1) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (μHE[n - 1] : Measure (Rn n)) (S ∩ closedBall x r) ≤
          ENNReal.ofReal (((1 - ε)⁻¹ ^ (n - 1) * unitBallVolume (n - 1) + η) * r ^ (n - 1)) ∧
        ENNReal.ofReal (((1 - ε) ^ (n - 1) * unitBallVolume (n - 1) - η) * r ^ (n - 1)) ≤
          (μHE[n - 1] : Measure (Rn n)) (S ∩ closedBall x r) := by
  set μ : Measure (Rn n) := μHE[n - 1]
  set k := n - 1
  have hω := unitBallVolume_pos k
  have h1ε : 0 < 1 - ε := sub_pos.2 hε
  filter_upwards [hG.negligible_diff η hη, hG.negligible_proj.scale h1ε η hη,
    self_mem_nhdsWithin] with r hr1 hr2 (hr : 0 < r)
  have hp := projH_mem_hyperplane hG.norm_eq x
  constructor
  · calc μ (S ∩ closedBall x r) ≤ μ (G ∩ closedBall x r ∪ (S \ G) ∩ closedBall x r) := by
          refine measure_mono fun y ⟨hyS, hyB⟩ => ?_
          by_cases hyG : y ∈ G
          · exact Or.inl ⟨hyG, hyB⟩
          · exact Or.inr ⟨⟨hyS, hyG⟩, hyB⟩
      _ ≤ μ (G ∩ closedBall x r) + μ ((S \ G) ∩ closedBall x r) := measure_union_le _ _
      _ ≤ flatConst ε ^ k * μ (hyperplane ν ∩ closedBall (projH ν x) r) +
            ENNReal.ofReal (η * r ^ k) :=
          add_le_add (hG.flat.measure_inter_closedBall_le k hG.norm_eq hε x r) hr1
      _ = _ := by
          rw [euclideanHausdorffMeasure_hyperplane_inter_closedBall hn
            (ne_zero_of_norm_eq_one hG.norm_eq) hp hr.le, flatConst_pow ε hε,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1
          ring
  · have hlow := hG.flat.le_measure_inter_closedBall k hG.norm_eq hε hG.mem r
    rw [euclideanHausdorffMeasure_hyperplane_inter_closedBall hn
      (ne_zero_of_norm_eq_one hG.norm_eq) hp (by positivity)] at hlow
    have hle : ENNReal.ofReal (unitBallVolume k * ((1 - ε) * r) ^ k) ≤
        μ (S ∩ closedBall x r) + ENNReal.ofReal (η * r ^ k) := by
      refine hlow.trans (add_le_add (measure_mono ?_) hr2)
      exact inter_subset_inter_left _ hG.subset
    calc ENNReal.ofReal (((1 - ε) ^ k * unitBallVolume k - η) * r ^ k)
        = ENNReal.ofReal (unitBallVolume k * ((1 - ε) * r) ^ k) - ENNReal.ofReal (η * r ^ k) := by
          rw [← ENNReal.ofReal_sub _ (by positivity)]
          congr 1
          rw [mul_pow]
          ring
      _ ≤ μ (S ∩ closedBall x r) := tsub_le_iff_right.2 hle

theorem tendsto_one_div_nat_add_two :
    Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem tendsto_inv_one_sub_pow {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun m => (1 - ε m)⁻¹ ^ k) atTop (𝓝 1) := by
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hε).inv₀ (by norm_num) |>.pow k
  simpa using this

theorem tendsto_one_sub_pow {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun m => (1 - ε m) ^ k) atTop (𝓝 1) := by
  have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hε).pow k
  simpa using this

theorem one_div_nat_add_two_lt_one (m : ℕ) : 1 / ((m : ℝ) + 2) < 1 := by
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- **Density one** at points with good pieces for every `ε = 1/(m+2)`. -/
theorem tendsto_measure_inter_closedBall_div (hn : 2 ≤ n) {S : Set (Rn n)} {x : Rn n}
    (h : ∀ m : ℕ, ∃ G ν, IsGoodPiece (n - 1) S G ν (1 / ((m : ℝ) + 2)) x) :
    Tendsto (fun r => (μHE[n - 1] : Measure (Rn n)) (S ∩ closedBall x r) /
      ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1))) (𝓝[>] 0) (𝓝 1) := by
  set k := n - 1
  set ω := unitBallVolume k
  have hω : 0 < ω := unitBallVolume_pos k
  choose G ν hG using h
  have hdiv : ∀ A r, 0 < r → ENNReal.ofReal (A * r ^ k) / ENNReal.ofReal (ω * r ^ k) =
      ENNReal.ofReal (A / ω) := by
    intro A r hr
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨t, ht0, hat, ht1⟩ := ENNReal.lt_iff_exists_real_btwn.1 ha
    have ht1' : t < 1 := ENNReal.ofReal_lt_one.1 ht1
    obtain ⟨m, hm⟩ := ((tendsto_one_sub_pow tendsto_one_div_nat_add_two k).eventually
      (lt_mem_nhds (show (1 + t) / 2 < 1 by linarith))).exists
    have hb := (hG m).measure_bounds hn (one_div_nat_add_two_lt_one m) (ω * (1 - t) / 2)
      (div_pos (mul_pos hω (sub_pos.2 ht1')) two_pos)
    filter_upwards [hb, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
    refine hat.trans_le ((ENNReal.ofReal_le_ofReal ?_).trans
      ((hdiv _ r hr0).symm.le.trans (ENNReal.div_le_div_right hr.2 _)))
    rw [le_div_iff₀ hω]
    nlinarith
  · obtain ⟨t, ht0, hat, ht1⟩ := ENNReal.lt_iff_exists_real_btwn.1 hb
    have ht1' : 1 < t := ENNReal.one_lt_ofReal.1 hat
    obtain ⟨m, hm⟩ := ((tendsto_inv_one_sub_pow tendsto_one_div_nat_add_two k).eventually
      (gt_mem_nhds (show 1 < (1 + t) / 2 by linarith))).exists
    have hb := (hG m).measure_bounds hn (one_div_nat_add_two_lt_one m) (ω * (t - 1) / 2)
      (div_pos (mul_pos hω (sub_pos.2 ht1')) two_pos)
    filter_upwards [hb, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
    refine lt_of_le_of_lt ((ENNReal.div_le_div_right hr.1 _).trans (hdiv _ r hr0).le) ?_
    refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) ht1
    rw [div_le_iff₀ hω]
    nlinarith

/-! ### Test functions -/

/-- The modulus of continuity `ω_φ(s) = sup {|φ u - φ v| : ‖u - v‖ ≤ s}` (junk if unbounded). -/
def modulus (φ : Rn n → ℝ) (s : ℝ) : ℝ :=
  sSup ((fun p : Rn n × Rn n => |φ p.1 - φ p.2|) '' {p | ‖p.1 - p.2‖ ≤ s})

theorem abs_sub_le_modulus {φ : Rn n → ℝ} {B : ℝ} (hB : ∀ u, |φ u| ≤ B) {u v : Rn n} {s : ℝ}
    (h : ‖u - v‖ ≤ s) : |φ u - φ v| ≤ modulus φ s := by
  refine le_csSup ⟨2 * B, ?_⟩ ⟨(u, v), h, rfl⟩
  rintro _ ⟨p, -, rfl⟩
  exact (abs_sub _ _).trans (by linarith [hB p.1, hB p.2])

theorem modulus_nonneg {φ : Rn n → ℝ} {B : ℝ} (hB : ∀ u, |φ u| ≤ B) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ modulus φ s :=
  (abs_nonneg _).trans (abs_sub_le_modulus hB (u := 0) (v := 0) (by simpa using hs))

theorem tendsto_modulus {φ : Rn n → ℝ} {B : ℝ} (hB : ∀ u, |φ u| ≤ B) (huc : UniformContinuous φ)
    {s : ℕ → ℝ} (hs0 : ∀ j, 0 ≤ s j) (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun j => modulus φ (s j)) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun τ hτ => ?_
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.1 huc (τ / 2) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hs δ hδ
  refine ⟨N, fun j hj => ?_⟩
  have hsj : s j < δ := by
    have := hN j hj
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hs0 j)] at this
  have hle : modulus φ (s j) ≤ τ / 2 := by
    refine csSup_le ⟨_, (0, 0), by simpa using hs0 j, rfl⟩ ?_
    rintro _ ⟨p, hp, rfl⟩
    have := hd (a := p.1) (b := p.2) (by rw [dist_eq_norm]; exact lt_of_le_of_lt hp hsj)
    rw [Real.dist_eq] at this
    exact this.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (modulus_nonneg hB (hs0 j))]
  linarith

theorem exists_radius_of_hasCompactSupport {φ : Rn n → ℝ} (hφs : HasCompactSupport φ) :
    ∃ R > 0, ∀ u, R < ‖u‖ → φ u = 0 := by
  obtain ⟨R, hR⟩ := hφs.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun u hu => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hR h
  rw [mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R 1]

/-- A set integral of a blow-up of `φ` over `A`, with `φ ≤ M` vanishing outside `B̄_R`. -/
theorem setLIntegral_ofReal_blowup_le (k : ℕ) (A : Set (Rn n)) {φ : Rn n → ℝ} {M R r : ℝ}
    (hr : 0 < r) (hφM : ∀ u, φ u ≤ M) (hφR : ∀ u, R < ‖u‖ → φ u = 0) (x : Rn n) :
    ∫⁻ y in A, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[k] ≤
      ENNReal.ofReal M * (μHE[k] : Measure (Rn n)) (A ∩ closedBall x (R * r)) := by
  calc ∫⁻ y in A, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[k]
      ≤ ∫⁻ y in A, (closedBall x (R * r)).indicator (fun _ => ENNReal.ofReal M) y ∂μHE[k] := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ closedBall x (R * r)
        · rw [indicator_of_mem hy]
          exact ENNReal.ofReal_le_ofReal (hφM _)
        · rw [indicator_of_notMem hy, hφR, ENNReal.ofReal_zero]
          rw [mem_closedBall, dist_eq_norm, not_le] at hy
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← div_eq_inv_mul,
            lt_div_iff₀ hr]
          exact hy
    _ = _ := by
        rw [lintegral_indicator_const measurableSet_closedBall,
          Measure.restrict_apply measurableSet_closedBall, inter_comm]

theorem lintegral_hyperplane_ne_top (hn : 2 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1) {φ : Rn n → ℝ}
    {M R : ℝ} (hR : 0 ≤ R) (hφM : ∀ u, φ u ≤ M) (hφR : ∀ u, R < ‖u‖ → φ u = 0) :
    ∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[n - 1] ≠ ∞ := by
  have := setLIntegral_ofReal_blowup_le (n - 1) (hyperplane ν) one_pos hφM hφR 0
  simp only [inv_one, one_smul, sub_zero, mul_one] at this
  refine ne_top_of_le_ne_top ?_ this
  rw [euclideanHausdorffMeasure_hyperplane_inter_closedBall hn (ne_zero_of_norm_eq_one hν)
    (by simp [mem_hyperplane]) hR]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- Comparison of the integrals of `φ` over two nearby hyperplanes. -/
theorem toReal_lintegral_hyperplane_le (hn : 2 ≤ n) {ν ν' : Rn n} (hν : ‖ν‖ = 1)
    (hδ : ‖ν - ν'‖ ≤ 1 / 2) {φ : Rn n → ℝ} (hφm : Measurable φ) {R ω : ℝ} (hR : 0 ≤ R)
    (hφR : ∀ u, R < ‖u‖ → φ u = 0)
    (hω : ∀ u v, ‖u - v‖ ≤ 2 * ‖ν - ν'‖ * R → |φ u - φ v| ≤ ω) (hω0 : 0 ≤ ω)
    (hfin : ∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[n - 1] ≠ ∞) :
    (∫⁻ p in hyperplane ν', ENNReal.ofReal (φ p) ∂μHE[n - 1]).toReal ≤
      (1 - ‖ν - ν'‖)⁻¹ ^ (n - 1) *
        ((∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[n - 1]).toReal +
          ω * (unitBallVolume (n - 1) * (2 * R) ^ (n - 1))) := by
  have := (isFlatPiece_hyperplane ν ν').lintegral_le (n - 1) hν (norm_nonneg _) hδ
    (measurableSet_hyperplane ν') (x := 0) (by simp [mem_hyperplane]) hφm hφR hω hω0 one_pos
  simp only [inv_one, one_smul, sub_zero, one_pow, ENNReal.ofReal_one, one_mul] at this
  have hub := (unitBallVolume_pos (n - 1)).le
  have hC : 0 ≤ ω * (unitBallVolume (n - 1) * (2 * R) ^ (n - 1)) :=
    mul_nonneg hω0 (mul_nonneg hub (pow_nonneg (by linarith) _))
  have hc : 0 ≤ (1 - ‖ν - ν'‖)⁻¹ ^ (n - 1) := pow_nonneg (inv_nonneg.2 (by linarith)) _
  rw [euclideanHausdorffMeasure_hyperplane_inter_closedBall hn (ne_zero_of_norm_eq_one hν)
    (by simp [mem_hyperplane]) (by linarith), flatConst_pow _ (by linarith),
    ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hω0, ← ENNReal.ofReal_add
    ENNReal.toReal_nonneg hC, ← ENNReal.ofReal_mul hc] at this
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hc (add_nonneg ENNReal.toReal_nonneg hC)) this

/-- Continuity of `ν ↦ ∫_{ν^⊥} φ`. -/
theorem tendsto_toReal_lintegral_hyperplane (hn : 2 ≤ n) {ν : Rn n} (hν : ‖ν‖ = 1)
    {νs : ℕ → Rn n} (hνs : ∀ j, ‖νs j‖ = 1) (hlim : Tendsto νs atTop (𝓝 ν)) {φ : Rn n → ℝ}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    Tendsto (fun j => (∫⁻ p in hyperplane (νs j), ENNReal.ofReal (φ p) ∂μHE[n - 1]).toReal)
      atTop (𝓝 (∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[n - 1]).toReal) := by
  set I : Rn n → ℝ := fun ν => (∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[n - 1]).toReal
  obtain ⟨B, hB⟩ := hφc.bounded_above_of_compact_support hφs
  have hB' : ∀ u, |φ u| ≤ B := fun u => by simpa [Real.norm_eq_abs] using hB u
  have hφM : ∀ u, φ u ≤ B := fun u => (le_abs_self _).trans (hB' u)
  obtain ⟨R, hR, hφR⟩ := exists_radius_of_hasCompactSupport hφs
  have huc := hφs.uniformContinuous_of_continuous hφc
  set k := n - 1
  set C := unitBallVolume k * (2 * R) ^ k
  have hC : 0 ≤ C := mul_nonneg (unitBallVolume_pos k).le (pow_nonneg (by linarith) _)
  set δ : ℕ → ℝ := fun j => ‖ν - νs j‖
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hlim)
    simpa [δ, norm_sub_rev] using this
  set ω : ℕ → ℝ := fun j => modulus φ (2 * δ j * R)
  have hω : Tendsto ω atTop (𝓝 0) := by
    refine tendsto_modulus hB' huc (fun j => by positivity) ?_
    simpa using ((tendsto_const_nhds (x := (2 : ℝ))).mul hδ).mul_const R
  have hω0 : ∀ j, 0 ≤ ω j := fun j => modulus_nonneg hB' (by positivity)
  have hc := tendsto_inv_one_sub_pow hδ k
  have hfin : ∀ ν' : Rn n, ‖ν'‖ = 1 →
      ∫⁻ p in hyperplane ν', ENNReal.ofReal (φ p) ∂μHE[n - 1] ≠ ∞ :=
    fun ν' hν' => lintegral_hyperplane_ne_top hn hν' hR.le hφM hφR
  have hδ2 : ∀ᶠ j in atTop, δ j ≤ 1 / 2 := hδ.eventually (ge_mem_nhds (by norm_num))
  -- upper bound
  have hup : ∀ᶠ j in atTop, I (νs j) ≤ (1 - δ j)⁻¹ ^ k * (I ν + ω j * C) := by
    filter_upwards [hδ2] with j hj
    exact toReal_lintegral_hyperplane_le hn hν hj hφc.measurable hR.le hφR
      (fun u v huv => abs_sub_le_modulus hB' huv) (hω0 j) (hfin ν hν)
  -- lower bound
  have hlow : ∀ᶠ j in atTop, I ν / (1 - δ j)⁻¹ ^ k - ω j * C ≤ I (νs j) := by
    filter_upwards [hδ2] with j hj
    have hj' : ‖νs j - ν‖ ≤ 1 / 2 := by rwa [norm_sub_rev]
    have := toReal_lintegral_hyperplane_le hn (hνs j) hj' hφc.measurable hR.le hφR
      (fun u v huv => abs_sub_le_modulus hB' (by rwa [norm_sub_rev (νs j)] at huv)) (hω0 j)
      (hfin _ (hνs j))
    rw [norm_sub_rev] at this
    have hpos : 0 < (1 - δ j)⁻¹ ^ k := by
      have : 0 < 1 - δ j := by linarith
      positivity
    rw [sub_le_iff_le_add, div_le_iff₀ hpos]
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ hlow hup
  · have := ((tendsto_const_nhds (x := I ν)).div hc one_ne_zero).sub (hω.mul_const C)
    simpa using this
  · have := hc.mul ((tendsto_const_nhds (x := I ν)).add (hω.mul_const C))
    simpa using this

/-! ### Blow-ups -/

/-- Blow-up bounds at every small scale from one good piece. -/
theorem IsGoodPiece.blowup_bounds (hn : 2 ≤ n) {S G : Set (Rn n)} {ν x : Rn n} {ε : ℝ}
    (hG : IsGoodPiece (n - 1) S G ν ε x) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) {φ : Rn n → ℝ}
    (hφm : Measurable φ) {M R ω : ℝ} (hM : 0 ≤ M) (hφM : ∀ u, φ u ≤ M) (hR : 0 < R)
    (hφR : ∀ u, R < ‖u‖ → φ u = 0)
    (hω : ∀ u v, ‖u - v‖ ≤ 2 * ε * R → |φ u - φ v| ≤ ω) (hω0 : 0 ≤ ω) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∫⁻ y in S, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[n - 1] ≠ ∞ ∧
      (r ^ (n - 1))⁻¹ * (∫⁻ y in S, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[n - 1]).toReal ≤
        (1 - ε)⁻¹ ^ (n - 1) * ((∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[n - 1]).toReal +
          ω * (unitBallVolume (n - 1) * (2 * R) ^ (n - 1))) + M * η ∧
      (∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[n - 1]).toReal ≤
        (r ^ (n - 1))⁻¹ * (∫⁻ y in S, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[n - 1]).toReal +
          (1 - ε)⁻¹ ^ (n - 1) * (ω * (unitBallVolume (n - 1) * (2 * R) ^ (n - 1))) + M * η := by
  set μ : Measure (Rn n) := μHE[n - 1]
  set k := n - 1
  set I := (∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μ).toReal
  set C := unitBallVolume k * (2 * R) ^ k
  set c := (1 - ε)⁻¹ ^ k
  have hC : 0 ≤ C := mul_nonneg (unitBallVolume_pos k).le (pow_nonneg (by linarith) _)
  have hc : 0 ≤ c := pow_nonneg (inv_nonneg.2 (by linarith)) _
  have hν := hG.norm_eq
  have hIfin : ∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μ ≠ ∞ :=
    lintegral_hyperplane_ne_top hn hν hR.le hφM hφR
  have hI : ∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μ = ENNReal.ofReal I :=
    (ENNReal.ofReal_toReal hIfin).symm
  have hball : μ (hyperplane ν ∩ closedBall 0 (2 * R)) = ENNReal.ofReal C :=
    euclideanHausdorffMeasure_hyperplane_inter_closedBall hn (ne_zero_of_norm_eq_one hν)
      (by simp [mem_hyperplane]) (by linarith)
  filter_upwards [hG.negligible_diff.scale hR η hη, hG.negligible_proj.scale hR η hη,
    self_mem_nhdsWithin] with r h1 h2 (hr : 0 < r)
  have hrk : 0 < r ^ k := pow_pos hr k
  have hsplit : ∫⁻ y in S, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μ =
      ∫⁻ y in G, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μ +
        ∫⁻ y in S \ G, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μ := by
    rw [← lintegral_inter_add_sdiff _ S hG.measurableSet, inter_eq_right.2 hG.subset]
  set F := ∫⁻ y in S, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μ
  set A := ∫⁻ y in G, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μ
  have hA : A ≤ ENNReal.ofReal (c * (r ^ k * (I + ω * C))) := by
    have := hG.flat.lintegral_le k hν hε0 hε hG.measurableSet hG.mem hφm hφR hω hω0 hr
    rwa [hI, hball, flatConst_pow _ (by linarith), ← ENNReal.ofReal_mul hω0,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg (mul_nonneg hω0 hC),
      ← ENNReal.ofReal_mul hrk.le, ← ENNReal.ofReal_mul hc] at this
  have hrest : ∫⁻ y in S \ G, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μ ≤
      ENNReal.ofReal (M * (η * r ^ k)) := by
    refine (setLIntegral_ofReal_blowup_le k _ hr hφM hφR x).trans ?_
    rw [ENNReal.ofReal_mul hM]
    gcongr
  have hFle : F ≤ ENNReal.ofReal (r ^ k * (c * (I + ω * C) + M * η)) := by
    rw [hsplit]
    refine (add_le_add hA hrest).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add
      (mul_nonneg hc (mul_nonneg hrk.le (add_nonneg ENNReal.toReal_nonneg (mul_nonneg hω0 hC))))
      (mul_nonneg hM (mul_nonneg hη.le hrk.le))]
    congr 1
    ring
  have hFfin : F ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFle
  refine ⟨hFfin, ?_, ?_⟩
  · have := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hrk.le (add_nonneg
      (mul_nonneg hc (add_nonneg ENNReal.toReal_nonneg (mul_nonneg hω0 hC))) (mul_nonneg hM hη.le)))
      hFle
    rw [inv_mul_le_iff₀ hrk]
    linarith
  · have hlow := hG.flat.le_lintegral k hν hε0 hε hG.measurableSet hG.mem hφm hφM hφR hω hω0 hr
    have hAF : A ≤ F := by rw [hsplit]; exact le_self_add
    have hb0 : 0 ≤ c * (r ^ k * (ω * C)) := mul_nonneg hc (mul_nonneg hrk.le (mul_nonneg hω0 hC))
    have hd0 : 0 ≤ M * (η * r ^ k) := mul_nonneg hM (mul_nonneg hη.le hrk.le)
    have h2' : μ ((hyperplane ν \ projH ν '' G) ∩ closedBall (projH ν x) (R * r)) ≤
        ENNReal.ofReal (η * r ^ k) := h2
    have : ENNReal.ofReal (r ^ k * I) ≤ ENNReal.ofReal (F.toReal + c * (r ^ k * (ω * C)) +
        M * (η * r ^ k)) := by
      calc ENNReal.ofReal (r ^ k * I)
          = ENNReal.ofReal (r ^ k) * ∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μ := by
            rw [hI, ENNReal.ofReal_mul hrk.le]
        _ ≤ _ := hlow
        _ ≤ F + ENNReal.ofReal (c * (r ^ k * (ω * C))) + ENNReal.ofReal (M * (η * r ^ k)) := by
            gcongr ?_ + ?_ + ?_
            · rw [hball, flatConst_pow _ (by linarith), ← ENNReal.ofReal_mul hω0,
                ← ENNReal.ofReal_mul hrk.le, ← ENNReal.ofReal_mul hc]
            · rw [ENNReal.ofReal_mul hM]
              gcongr
        _ = _ := by
            rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg hb0) hd0,
              ENNReal.ofReal_add ENNReal.toReal_nonneg hb0, ENNReal.ofReal_toReal hFfin]
    rw [ENNReal.ofReal_le_ofReal_iff (add_nonneg (add_nonneg ENNReal.toReal_nonneg hb0) hd0)]
      at this
    have key := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hrk.le)
    have e : (r ^ k)⁻¹ * (F.toReal + c * (r ^ k * (ω * C)) + M * (η * r ^ k)) =
        (r ^ k)⁻¹ * F.toReal + c * (ω * C) + M * η := by
      calc _ = (r ^ k)⁻¹ * F.toReal + ((r ^ k)⁻¹ * r ^ k) * (c * (ω * C)) +
            ((r ^ k)⁻¹ * r ^ k) * (M * η) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hrk.ne', one_mul, one_mul]
    rw [inv_mul_cancel_left₀ hrk.ne', e] at key
    exact key

/-- **Approximate tangent plane** (nonnegative test functions, lower integrals). -/
theorem exists_tendsto_lintegral_blowup (hn : 2 ≤ n) {S : Set (Rn n)} {x : Rn n}
    (h : ∀ m : ℕ, ∃ G ν, IsGoodPiece (n - 1) S G ν (1 / ((m : ℝ) + 2)) x) :
    ∃ ν : Rn n, ‖ν‖ = 1 ∧ ∀ φ : Rn n → ℝ, Continuous φ → HasCompactSupport φ → (∀ u, 0 ≤ φ u) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), ∫⁻ y in S, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[n - 1] ≠ ∞) ∧
      Tendsto (fun r => (r ^ (n - 1))⁻¹ *
          (∫⁻ y in S, ENNReal.ofReal (φ (r⁻¹ • (y - x))) ∂μHE[n - 1]).toReal) (𝓝[>] 0)
        (𝓝 (∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[n - 1]).toReal) := by
  choose G ν hG using h
  obtain ⟨ν₀, hν₀, ψ, hψ, hlim⟩ := (isCompact_sphere (0 : Rn n) 1).tendsto_subseq
    (x := ν) fun m => by simpa using (hG m).norm_eq
  rw [mem_sphere_zero_iff_norm] at hν₀
  refine ⟨ν₀, hν₀, fun φ hφc hφs hφ0 => ?_⟩
  set k := n - 1
  set I : Rn n → ℝ := fun ν => (∫⁻ p in hyperplane ν, ENNReal.ofReal (φ p) ∂μHE[n - 1]).toReal
  obtain ⟨B, hB⟩ := hφc.bounded_above_of_compact_support hφs
  have hB' : ∀ u, |φ u| ≤ B := fun u => by simpa [Real.norm_eq_abs] using hB u
  have hφM : ∀ u, φ u ≤ B := fun u => (le_abs_self _).trans (hB' u)
  have hM : 0 ≤ B := (hφ0 0).trans (hφM 0)
  obtain ⟨R, hR, hφR⟩ := exists_radius_of_hasCompactSupport hφs
  have huc := hφs.uniformContinuous_of_continuous hφc
  set C := unitBallVolume k * (2 * R) ^ k
  set ε : ℕ → ℝ := fun j => 1 / ((ψ j : ℝ) + 2)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_nat_add_two.comp hψ.tendsto_atTop
  have hε0 : ∀ j, 0 ≤ ε j := fun j => by positivity
  have hε2 : ∀ j, ε j ≤ 1 / 2 := fun j => by
    simp only [ε]
    gcongr
    linarith [(Nat.cast_nonneg (ψ j) : (0 : ℝ) ≤ ψ j)]
  set ω : ℕ → ℝ := fun j => modulus φ (2 * ε j * R)
  have hω : Tendsto ω atTop (𝓝 0) := by
    refine tendsto_modulus hB' huc (fun j => by positivity) ?_
    simpa using ((tendsto_const_nhds (x := (2 : ℝ))).mul hε).mul_const R
  have hω0 : ∀ j, 0 ≤ ω j := fun j => modulus_nonneg hB' (by positivity)
  have hIc : Tendsto (fun j => I (ν (ψ j))) atTop (𝓝 (I ν₀)) :=
    tendsto_toReal_lintegral_hyperplane hn hν₀ (fun j => (hG (ψ j)).norm_eq) hlim hφc hφs
  have hc := tendsto_inv_one_sub_pow hε k
  have hU : Tendsto (fun j => (1 - ε j)⁻¹ ^ k * (I (ν (ψ j)) + ω j * C)) atTop (𝓝 (I ν₀)) := by
    simpa using hc.mul (hIc.add (hω.mul_const C))
  have hV : Tendsto (fun j => I (ν (ψ j)) - (1 - ε j)⁻¹ ^ k * (ω j * C)) atTop (𝓝 (I ν₀)) := by
    simpa using hIc.sub (hc.mul (hω.mul_const C))
  have hbd := fun j η hη => (hG (ψ j)).blowup_bounds hn (hε0 j) (hε2 j) hφc.measurable hM hφM hR
    hφR (fun u v huv => abs_sub_le_modulus hB' huv) (hω0 j) η hη
  refine ⟨(hbd 0 1 one_pos).mono fun r hr => hr.1, Metric.tendsto_nhds.2 fun τ hτ => ?_⟩
  obtain ⟨j, hUj, hVj⟩ := ((hU.eventually (Metric.ball_mem_nhds _ (half_pos hτ))).and
    (hV.eventually (Metric.ball_mem_nhds _ (half_pos hτ)))).exists
  rw [Real.dist_eq, abs_lt] at hUj hVj
  have hη : 0 < τ / (4 * (B + 1)) := by positivity
  have hBη : B * (τ / (4 * (B + 1))) ≤ τ / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  filter_upwards [hbd j _ hη] with r hr
  obtain ⟨-, hup, hlow⟩ := hr
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### Signed test functions and approximate tangent planes -/

/-- `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻` when both lower integrals are finite. -/
theorem integral_eq_toReal_sub_toReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Measurable f) (h1 : ∫⁻ a, ENNReal.ofReal (max (f a) 0) ∂μ ≠ ∞)
    (h2 : ∫⁻ a, ENNReal.ofReal (max (-f a) 0) ∂μ ≠ ∞) :
    ∫ a, f a ∂μ = (∫⁻ a, ENNReal.ofReal (max (f a) 0) ∂μ).toReal -
      (∫⁻ a, ENNReal.ofReal (max (-f a) 0) ∂μ).toReal := by
  have hp : Measurable fun a => max (f a) 0 := hf.max measurable_const
  have hm : Measurable fun a => max (-f a) 0 := hf.neg.max measurable_const
  have i1 : Integrable (fun a => max (f a) 0) μ :=
    (integrable_toReal_of_lintegral_ne_top hp.ennreal_ofReal.aemeasurable h1).congr
      (Eventually.of_forall fun a => ENNReal.toReal_ofReal (le_max_right _ _))
  have i2 : Integrable (fun a => max (-f a) 0) μ :=
    (integrable_toReal_of_lintegral_ne_top hm.ennreal_ofReal.aemeasurable h2).congr
      (Eventually.of_forall fun a => ENNReal.toReal_ofReal (le_max_right _ _))
  have hfe : (fun a => f a) = fun a => max (f a) 0 - max (-f a) 0 :=
    funext fun a => (max_zero_sub_max_neg_zero_eq_self (f a)).symm
  rw [hfe, integral_sub i1 i2,
    integral_eq_lintegral_of_nonneg_ae (f := fun a => max (f a) 0)
      (Eventually.of_forall fun a => le_max_right _ _) hp.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (f := fun a => max (-f a) 0)
      (Eventually.of_forall fun a => le_max_right _ _) hm.aestronglyMeasurable]

/-- **Approximate tangent plane** at points with good pieces for every `ε = 1/(m+2)`:
`r^{1-n} ∫_S φ((y - x)/r) dℋ^{n-1} → ∫_{ν^⊥} φ dℋ^{n-1}` for every continuous compactly
supported `φ`. -/
theorem exists_tendsto_integral_blowup (hn : 2 ≤ n) {S : Set (Rn n)} {x : Rn n}
    (h : ∀ m : ℕ, ∃ G ν, IsGoodPiece (n - 1) S G ν (1 / ((m : ℝ) + 2)) x) :
    ∃ ν : Rn n, ‖ν‖ = 1 ∧ ∀ φ : Rn n → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun r => (r ^ (n - 1))⁻¹ * ∫ y in S, φ (r⁻¹ • (y - x)) ∂μHE[n - 1]) (𝓝[>] 0)
        (𝓝 (∫ y in hyperplane ν, φ y ∂μHE[n - 1])) := by
  obtain ⟨ν, hν, hT⟩ := exists_tendsto_lintegral_blowup hn h
  refine ⟨ν, hν, fun φ hφc hφs => ?_⟩
  obtain ⟨B, hB⟩ := hφc.bounded_above_of_compact_support hφs
  have hB' : ∀ u, |φ u| ≤ B := fun u => by simpa [Real.norm_eq_abs] using hB u
  obtain ⟨R, hR, hφR⟩ := exists_radius_of_hasCompactSupport hφs
  set φp : Rn n → ℝ := fun u => max (φ u) 0
  set φm : Rn n → ℝ := fun u => max (-φ u) 0
  have hsp : Function.support φp ⊆ Function.support φ := fun u hu h0 => hu (by simp [φp, h0])
  have hsm : Function.support φm ⊆ Function.support φ := fun u hu h0 => hu (by simp [φm, h0])
  obtain ⟨hfp, hTp⟩ := hT φp (hφc.max continuous_const) (hφs.mono hsp) (fun u => le_max_right _ _)
  obtain ⟨hfm, hTm⟩ := hT φm (hφc.neg.max continuous_const) (hφs.mono hsm)
    (fun u => le_max_right _ _)
  have hpM : ∀ u, φp u ≤ B := fun u =>
    max_le ((le_abs_self _).trans (hB' u)) ((abs_nonneg _).trans (hB' u))
  have hmM : ∀ u, φm u ≤ B := fun u =>
    max_le ((neg_le_abs _).trans (hB' u)) ((abs_nonneg _).trans (hB' u))
  have hpR : ∀ u, R < ‖u‖ → φp u = 0 := fun u hu => by simp [φp, hφR u hu]
  have hmR : ∀ u, R < ‖u‖ → φm u = 0 := fun u hu => by simp [φm, hφR u hu]
  rw [integral_eq_toReal_sub_toReal hφc.measurable (lintegral_hyperplane_ne_top hn hν hR.le hpM hpR)
    (lintegral_hyperplane_ne_top hn hν hR.le hmM hmR)]
  refine (hTp.sub hTm).congr' ?_
  filter_upwards [hfp, hfm] with r h1 h2
  have e := integral_eq_toReal_sub_toReal (μ := (μHE[n - 1] : Measure (Rn n)).restrict S)
    (f := fun y => φ (r⁻¹ • (y - x))) (hφc.measurable.comp (by fun_prop)) h1 h2
  beta_reduce at e
  rw [e, mul_sub]

/-- **Approximate tangent planes.** For a measurable, countably `(n-1)`-rectifiable `S ⊆ Ω` with
locally finite `ℋ^{n-1}` measure, `ℋ^{n-1}`-a.e. `x ∈ S` has a unit normal `ν` with
`r^{1-n} ∫_S φ((y - x)/r) dℋ^{n-1} → ∫_{ν^⊥} φ dℋ^{n-1}` for all continuous compactly supported
`φ`. The normalization `ℋ^{n-1} = ℒ^{n-1}` on `ℝ^{n-1}` is a hypothesis here (it is proved as
`GMT.hausdorffN_self_eq_volume`). -/
theorem hausdorffN_not_approxTangent_eq_zero (hn : 2 ≤ n)
    (hHausVol : hausdorffN (n - 1) (n - 1) = (volume : Measure (Rn (n - 1)))) {Ω S : Set (Rn n)}
    (hΩ : IsOpen Ω) (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (hrect : IsCountablyRectifiable n (n - 1) S)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ S) < ∞) :
    hausdorffN n (n - 1) {x | x ∈ S ∧ ¬ ∃ ν : Rn n, ‖ν‖ = 1 ∧
      ∀ φ : Rn n → ℝ, Continuous φ → HasCompactSupport φ →
        Tendsto (fun r => (r ^ (n - 1))⁻¹ * ∫ y in S, φ (r⁻¹ • (y - x)) ∂hausdorffN n (n - 1))
          (𝓝[>] 0) (𝓝 (∫ y in {y | ⟪y, ν⟫ = 0}, φ y ∂hausdorffN n (n - 1)))} = 0 := by
  rw [hausdorffN_eq_euclideanHausdorffMeasure hHausVol] at hfin ⊢
  refine measure_mono_null ?_ (measure_not_forall_exists_isGoodPiece hn hΩ hS hSΩ hrect
    fun K hK hKΩ => (hfin K hK hKΩ).ne)
  rintro x ⟨hxS, hx⟩
  refine ⟨hxS, fun h => hx ?_⟩
  exact exists_tendsto_integral_blowup hn h

end GMTFoundations.GMT
