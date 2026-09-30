/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.GMT.Basic
public import GMTFoundations.Reifenberg.Beta
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.CompletePartialOrder

/-!
# Exhaustion by Lipschitz images and rescaling (Step B)

The measure-theoretic half (Step B in `Rectifiable.lean`) of the rectifiable-Reifenberg theorem
`rectifiable_reifenberg`: a set of finite `ℋ^k` measure is exhausted by countably many Lipschitz
images up to a purely unrectifiable remainder, and the hypotheses of the theorem are invariant
under rescaling, so the big-pieces step (`BigPieces.lean`) can be run on a ball of radius one.

* `measurableSet_range_of_continuous`, `measurableSet_range_of_lipschitzWith`: a continuous image
  of `ℝ^k` is σ-compact, hence Borel.
* `exists_lipschitz_exhaustion`: for `ℋ^k(E) < ∞` there are countably many Lipschitz
  maps `f_i : ℝ^k → ℝⁿ` such that `P = E \ ⋃ range f_i` is purely unrectifiable,
  `ℋ^k(P ∩ range g) = 0` for every Lipschitz `g`. The family maximizes `ℋ^k(E ∩ ⋃ range f_i)`
  over countable Lipschitz families.
* `exists_linearIsometry_range_eq`: a linear isometry `ℝ^{n-1} → ℝⁿ` onto the hyperplane `ν^⊥`
  (the chart used to turn a Lipschitz map on a hyperplane into one on `ℝ^{n-1}`).
* `rescaleMeasure μ x r = r^{-(n-1)} · μ ∘ ψ` with `ψ z = x + r z`, and `rescaleMeasure_apply`
  (valid for every set, since `ψ` is a homeomorphism).
* `lintegral_Ioo_comp_mul_div`: the scale invariance of `dt/t` on `(0, s)`.
* Scale invariance of the hypotheses of `rectifiable_reifenberg`: `measure_ball_rescaleMeasure_le`
  (upper bound), `lintegral_rescaleMeasure_le` (square function; the hypothesis on the sub-balls of
  `B_{Rr}(x)` becomes the hypothesis on the sub-balls of `B_R(0)`), and `rescale_hyp`, which
  bundles them for `μ = ℋ^{n-1}⌊P` with `P ⊆ S` and the hypotheses of the theorem on `S` (`R = 16`
  is the region `B_{R₀}(0)` on which the Reifenberg construction uses them, `ledgerR0`).

No measurability of `P` or `S` is needed for the rescaling lemmas: all maps involved are
measurable embeddings and all balls are open (hence measurable).

## References

* [Miś] M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018);
  arXiv:1612.02461, §3, "Properties of β numbers" (scale invariance of β and `J`).
-/

public section

open MeasureTheory Metric Set Filter Topology Module
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace GMTFoundations

open GMT

variable {n : ℕ}

/-! ### The hyperplane chart -/

/-- A linear isometry from `ℝ^{n-1}` onto the hyperplane `ν^⊥ = (ℝ ∙ ν)ᗮ`, `ν ≠ 0`. -/
theorem exists_linearIsometry_range_eq (hn : 1 ≤ n) {ν : Rn n} (hν : ν ≠ 0) :
    ∃ L : Rn (n - 1) →ₗᵢ[ℝ] Rn n, range L = hyperplane ν := by
  set K : Submodule ℝ (Rn n) := (ℝ ∙ ν)ᗮ
  have hK : finrank ℝ K = n - 1 := finrank_orthogonal_span_singleton' hn hν
  let e : K ≃ₗᵢ[ℝ] Rn (n - 1) := ((stdOrthonormalBasis ℝ K).reindex (finCongr hK)).repr
  refine ⟨K.subtypeₗᵢ.comp e.symm.toLinearIsometry, ?_⟩
  rw [hyperplane_eq_orthogonal]
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact (e.symm z).2
  · intro hy
    exact ⟨e ⟨y, hy⟩, by simp⟩

/-! ### Exhaustion -/

/-- The range of a continuous map `ℝ^k → ℝⁿ` is σ-compact, hence measurable. -/
theorem measurableSet_range_of_continuous {k : ℕ} {f : Rn k → Rn n} (hf : Continuous f) :
    MeasurableSet (range f) := by
  have : range f = ⋃ m : ℕ, f '' closedBall 0 m := by
    ext y
    simp only [mem_range, mem_iUnion, mem_image, mem_closedBall, dist_zero_right]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨m, hm⟩ := exists_nat_ge ‖z‖
      exact ⟨m, z, hm, rfl⟩
    · rintro ⟨m, z, -, rfl⟩
      exact ⟨z, rfl⟩
  rw [this]
  exact MeasurableSet.iUnion fun m => ((isCompact_closedBall 0 (m : ℝ)).image hf).measurableSet

/-- The range of a Lipschitz map `ℝ^k → ℝⁿ` is measurable. -/
theorem measurableSet_range_of_lipschitzWith {k : ℕ} {f : Rn k → Rn n} {L : ℝ≥0}
    (hf : LipschitzWith L f) : MeasurableSet (range f) :=
  measurableSet_range_of_continuous hf.continuous

/-- **Exhaustion by Lipschitz images** (Step B). If `ℋ^k(E) < ∞`, there are countably
many Lipschitz maps `f_i : ℝ^k → ℝⁿ` whose ranges leave a purely unrectifiable remainder: every
Lipschitz image meets `E \ ⋃ range f_i` in an `ℋ^k`-null set. -/
theorem exists_lipschitz_exhaustion {k : ℕ} {E : Set (Rn n)} (hE : hausdorffN n k E ≠ ∞) :
    ∃ f : ℕ → Rn k → Rn n, (∀ i, ∃ L, LipschitzWith L (f i)) ∧
      ∀ g : Rn k → Rn n, (∃ L, LipschitzWith L g) →
        hausdorffN n k ((E \ ⋃ i, range (f i)) ∩ range g) = 0 := by
  classical
  set 𝓕 : Set (ℕ → Rn k → Rn n) := {f | ∀ i, ∃ L, LipschitzWith L (f i)} with h𝓕
  set V : (ℕ → Rn k → Rn n) → ℝ≥0∞ := fun f => hausdorffN n k (E ∩ ⋃ i, range (f i)) with hV
  have hne : (V '' 𝓕).Nonempty :=
    ⟨_, mem_image_of_mem V (show (fun _ _ => 0) ∈ 𝓕 from fun _ => ⟨0, LipschitzWith.const 0⟩)⟩
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hne (OrderTop.bddAbove _)
  choose f hf hfu using huS
  -- Merge the maximizing families into one.
  let F : ℕ → Rn k → Rn n := fun i => f (Nat.unpair i).1 (Nat.unpair i).2
  have hF : F ∈ 𝓕 := fun i => hf _ _
  have hsub : ∀ m, (⋃ j, range (f m j)) ⊆ ⋃ i, range (F i) := by
    intro m
    refine iUnion_subset fun j => subset_iUnion_of_subset (Nat.pair m j) ?_
    simp [F, Nat.unpair_pair]
  have hVF : sSup (V '' 𝓕) ≤ V F :=
    le_of_tendsto' hu fun m => (hfu m) ▸ measure_mono (inter_subset_inter_right _ (hsub m))
  refine ⟨F, hF, fun g hg => ?_⟩
  set U := ⋃ i, range (F i) with hUdef
  have hU : MeasurableSet U := MeasurableSet.iUnion fun i => by
    obtain ⟨L, hL⟩ := hF i
    exact measurableSet_range_of_lipschitzWith hL
  -- Append `g` to the family.
  let G : ℕ → Rn k → Rn n := fun i => Nat.casesOn i g F
  have hG : G ∈ 𝓕 := by
    intro i
    cases i with
    | zero => exact hg
    | succ i => exact hF i
  have hUG : ⋃ i, range (G i) = range g ∪ U := by
    ext y
    simp only [mem_iUnion, mem_union, hUdef]
    constructor
    · rintro ⟨i, hi⟩
      cases i with
      | zero => exact Or.inl hi
      | succ i => exact Or.inr ⟨i, hi⟩
    · rintro (hy | ⟨i, hi⟩)
      · exact ⟨0, hy⟩
      · exact ⟨i + 1, hi⟩
  have hVG : V G ≤ V F := (le_sSup (mem_image_of_mem V hG)).trans hVF
  have hsplit : V G = V F + hausdorffN n k ((E \ U) ∩ range g) := by
    change hausdorffN n k (E ∩ ⋃ i, range (G i)) = hausdorffN n k (E ∩ U) + _
    rw [← measure_inter_add_sdiff (E ∩ ⋃ i, range (G i)) hU, hUG]
    congr 2
    · ext y
      simp only [mem_inter_iff, mem_union]
      tauto
    · ext y
      simp only [mem_inter_iff, mem_union, Set.mem_sdiff]
      tauto
  have hVFfin : V F ≠ ∞ := ne_top_of_le_ne_top hE (measure_mono inter_subset_left)
  rw [hsplit] at hVG
  exact le_antisymm ((ENNReal.add_le_add_iff_left hVFfin).1 (by simpa using hVG)) zero_le

/-! ### Rescaling -/

/-- The rescaled measure `A ↦ r^{-(n-1)} μ(x + r A)`, i.e. `r^{-(n-1)} · μ ∘ ψ` with
`ψ z = x + r z`. It is the measure `μ_{x,r}` of `jonesBetaSq_smul_map`. -/
@[expose] def rescaleMeasure (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) : Measure (Rn n) :=
  ENNReal.ofReal ((r ^ (n - 1))⁻¹) • μ.map (fun y => r⁻¹ • (y - x))

/-- The blow-up `y ↦ r⁻¹ (y − x)` (the inverse of `ψ`) is a measurable embedding. -/
theorem measurableEmbedding_smul_sub {r : ℝ} (hr : r ≠ 0) (x : Rn n) :
    MeasurableEmbedding (fun y : Rn n => r⁻¹ • (y - x)) := by
  have := ((Homeomorph.addRight (-x)).trans
    (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))).measurableEmbedding
  convert this using 1
  ext y
  simp [sub_eq_add_neg]

/-- Preimages under the blow-up are images under `ψ z = x + r z`. -/
theorem preimage_smul_sub {r : ℝ} (hr : r ≠ 0) (x : Rn n) (A : Set (Rn n)) :
    (fun y : Rn n => r⁻¹ • (y - x)) ⁻¹' A = (fun z => x + r • z) '' A := by
  ext y
  simp only [mem_preimage, mem_image]
  constructor
  · intro hy
    refine ⟨_, hy, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  · rintro ⟨z, hz, rfl⟩
    rwa [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr, one_smul]

/-- The preimage of `B_s(y)` under `w ↦ r⁻¹ (w − x)` is the ball `B_{rs}(x + r y)`. -/
theorem preimage_smul_sub_ball {r : ℝ} (hr : 0 < r) (x y : Rn n) (s : ℝ) :
    (fun w : Rn n => r⁻¹ • (w - x)) ⁻¹' ball y s = ball (x + r • y) (r * s) := by
  ext w
  have : r⁻¹ • (w - x) - y = r⁻¹ • (w - (x + r • y)) := by
    rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]; abel
  simp only [mem_preimage, mem_ball, dist_eq_norm, this, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hr), inv_mul_lt_iff₀ hr]

/-- `rescaleMeasure μ x r A = r^{-(n-1)} μ(x + r A)` for **every** set `A`. -/
theorem rescaleMeasure_apply {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} (hr : 0 < r)
    (A : Set (Rn n)) :
    rescaleMeasure μ x r A = ENNReal.ofReal ((r ^ (n - 1))⁻¹) * μ ((fun z => x + r • z) '' A) := by
  rw [rescaleMeasure, Measure.smul_apply, smul_eq_mul,
    (measurableEmbedding_smul_sub hr.ne' x).map_apply, preimage_smul_sub hr.ne']

/-- `μ_{x,r}(B_s(y)) = r^{-(n-1)} μ(B_{rs}(x + r y))`. -/
theorem rescaleMeasure_ball {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} (hr : 0 < r) (y : Rn n)
    (s : ℝ) :
    rescaleMeasure μ x r (ball y s) =
      ENNReal.ofReal ((r ^ (n - 1))⁻¹) * μ (ball (x + r • y) (r * s)) := by
  rw [rescaleMeasure_apply hr, ← preimage_smul_sub hr.ne', preimage_smul_sub_ball hr]

instance isFiniteMeasure_rescaleMeasure (μ : Measure (Rn n)) [IsFiniteMeasure μ] (x : Rn n)
    (r : ℝ) : IsFiniteMeasure (rescaleMeasure μ x r) := by
  refine ⟨?_⟩
  rw [rescaleMeasure, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- β of the rescaled measure (`jonesBetaSq_smul_map`): `β_{μ_{x,r}}(z, t) = β_μ(x + r z, r t)`. -/
theorem jonesBetaSq_rescaleMeasure {r : ℝ} (hr : 0 < r) (μ : Measure (Rn n)) (x z : Rn n)
    (t : ℝ) : jonesBetaSq (rescaleMeasure μ x r) z t = jonesBetaSq μ (x + r • z) (r * t) :=
  jonesBetaSq_smul_map hr μ x z t

/-- Scale invariance of `dt/t`: `∫_0^s f(r t) dt/t = ∫_0^{rs} f(t) dt/t`. -/
theorem lintegral_Ioo_comp_mul_div (f : ℝ → ℝ≥0∞) {r : ℝ} (hr : 0 < r) (s : ℝ) :
    ∫⁻ t in Ioo 0 s, f (r * t) / ENNReal.ofReal t =
      ∫⁻ t in Ioo 0 (r * s), f t / ENNReal.ofReal t := by
  set h : ℝ → ℝ≥0∞ := (Ioo 0 (r * s)).indicator fun t => f t / ENNReal.ofReal t with hh
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have hpt : ∀ t, (Ioo 0 s).indicator (fun t => f (r * t) / ENNReal.ofReal t) t =
      ENNReal.ofReal r * h (r * t) := by
    intro t
    by_cases ht : t ∈ Ioo 0 s
    · have hrt : r * t ∈ Ioo 0 (r * s) :=
        ⟨mul_pos hr ht.1, (mul_lt_mul_iff_of_pos_left hr).2 ht.2⟩
      rw [indicator_of_mem ht, hh, indicator_of_mem hrt, ENNReal.ofReal_mul hr.le, ← mul_div_assoc,
        ENNReal.mul_div_mul_left _ _ hr0 ENNReal.ofReal_ne_top]
    · have hrt : r * t ∉ Ioo 0 (r * s) := fun h' =>
        ht ⟨pos_of_mul_pos_right h'.1 hr.le, (mul_lt_mul_iff_of_pos_left hr).1 h'.2⟩
      rw [indicator_of_notMem ht, hh, indicator_of_notMem hrt, mul_zero]
  have hmap : ∫⁻ t, h (r * t) = ENNReal.ofReal r⁻¹ * ∫⁻ t, h t := by
    have := (Homeomorph.mulLeft₀ r hr.ne').toMeasurableEquiv.measurableEmbedding.lintegral_map
      (μ := volume) h
    rw [show (⇑(Homeomorph.mulLeft₀ r hr.ne').toMeasurableEquiv) = (r * ·) from rfl,
      Real.map_volume_mul_left hr.ne', lintegral_smul_measure, abs_of_pos (inv_pos.2 hr),
      smul_eq_mul] at this
    exact this.symm
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmap, ← mul_assoc,
    ← ENNReal.ofReal_mul hr.le, mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one, one_mul]

/-! ### Scale invariance of the hypotheses -/

/-- The upper bound `μ(B_s(y)) ≤ C s^{n-1}` on all balls is invariant under rescaling. -/
theorem measure_ball_rescaleMeasure_le {μ : Measure (Rn n)} {C : ℝ}
    (hup : ∀ x r, 0 < r → μ (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) {x : Rn n} {r : ℝ}
    (hr : 0 < r) (y : Rn n) {s : ℝ} (hs : 0 < s) :
    rescaleMeasure μ x r (ball y s) ≤ ENNReal.ofReal (C * s ^ (n - 1)) := by
  rw [rescaleMeasure_ball hr]
  calc ENNReal.ofReal ((r ^ (n - 1))⁻¹) * μ (ball (x + r • y) (r * s))
      ≤ ENNReal.ofReal ((r ^ (n - 1))⁻¹) * ENNReal.ofReal (C * (r * s) ^ (n - 1)) := by
        gcongr
        exact hup _ _ (mul_pos hr hs)
    _ = ENNReal.ofReal (C * s ^ (n - 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : r ^ (n - 1) ≠ 0 := pow_ne_zero _ hr.ne'
        rw [mul_pow]
        field_simp

/-- The square-function hypothesis is invariant under rescaling: if it holds on every ball
`B_s(y) ⊆ B_{Rr}(x)`, the rescaled measure satisfies it on every ball `B_s(y) ⊆ B_R(0)`. -/
theorem lintegral_rescaleMeasure_le {μ : Measure (Rn n)} {J R : ℝ} {x : Rn n} {r : ℝ}
    (hr : 0 < r)
    (hsq : ∀ y s, 0 < s → ball y s ⊆ ball x (R * r) →
      ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s, jonesBetaSq μ z t / ENNReal.ofReal t) ∂μ ≤
        ENNReal.ofReal (J * s ^ (n - 1)))
    (y : Rn n) {s : ℝ} (hs : 0 < s) (hyR : ball y s ⊆ ball 0 R) :
    ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s,
        jonesBetaSq (rescaleMeasure μ x r) z t / ENNReal.ofReal t) ∂rescaleMeasure μ x r ≤
      ENNReal.ofReal (J * s ^ (n - 1)) := by
  set F : Rn n → ℝ≥0∞ := fun w =>
    ∫⁻ t in Ioo 0 (r * s), jonesBetaSq μ w t / ENNReal.ofReal t with hF
  have hemb := measurableEmbedding_smul_sub hr.ne' x
  -- The inner integral of the rescaled measure is `F ∘ ψ`.
  have hinner : ∀ z, ∫⁻ t in Ioo 0 s, jonesBetaSq (rescaleMeasure μ x r) z t / ENNReal.ofReal t =
      F (x + r • z) := by
    intro z
    simp_rw [jonesBetaSq_rescaleMeasure hr]
    exact lintegral_Ioo_comp_mul_div (fun t => jonesBetaSq μ (x + r • z) t) hr s
  simp_rw [hinner]
  -- Change variables in the outer integral.
  have houter : ∫⁻ z in ball y s, F (x + r • z) ∂rescaleMeasure μ x r =
      ENNReal.ofReal ((r ^ (n - 1))⁻¹) * ∫⁻ w in ball (x + r • y) (r * s), F w ∂μ := by
    rw [rescaleMeasure, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      hemb.restrict_map, hemb.lintegral_map, preimage_smul_sub_ball hr]
    congr 1
    refine lintegral_congr fun w => ?_
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  rw [houter]
  -- The image ball lies in `B_{Rr}(x)`.
  have hsub : ball (x + r • y) (r * s) ⊆ ball x (R * r) := by
    intro w hw
    rw [← preimage_smul_sub_ball hr] at hw
    have h2 : w ∈ (fun w : Rn n => r⁻¹ • (w - x)) ⁻¹' ball 0 R := hyR hw
    rwa [preimage_smul_sub_ball hr, smul_zero, add_zero, mul_comm] at h2
  calc ENNReal.ofReal ((r ^ (n - 1))⁻¹) * ∫⁻ w in ball (x + r • y) (r * s), F w ∂μ
      ≤ ENNReal.ofReal ((r ^ (n - 1))⁻¹) * ENNReal.ofReal (J * (r * s) ^ (n - 1)) := by
        gcongr
        exact hsq _ _ (mul_pos hr hs) hsub
    _ = ENNReal.ofReal (J * s ^ (n - 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : r ^ (n - 1) ≠ 0 := pow_ne_zero _ hr.ne'
        rw [mul_pow]
        field_simp

/-- The square-function hypothesis of `rectifiable_reifenberg` on `S` (outer integral over
`S ∩ B_s(y)` against `ℋ^{n-1}`, β of `ℋ^{n-1}⌊S`) passes to `μ_P = ℋ^{n-1}⌊P` for `P ⊆ S`, in
the measure form `∫_{B_s(y)} J_{μ_P}(z, s) dμ_P(z)` (β is monotone in μ,
`jonesBetaSq_mono_measure`). -/
theorem lintegral_restrict_le_of_subset {S P : Set (Rn n)} (hPS : P ⊆ S) (y : Rn n) (s : ℝ) :
    ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s,
        jonesBetaSq ((hausdorffN n (n - 1)).restrict P) z t / ENNReal.ofReal t)
        ∂(hausdorffN n (n - 1)).restrict P ≤
      ∫⁻ z in S ∩ ball y s, (∫⁻ t in Ioo 0 s,
        jonesBetaSq ((hausdorffN n (n - 1)).restrict S) z t / ENNReal.ofReal t)
        ∂hausdorffN n (n - 1) := by
  rw [Measure.restrict_restrict measurableSet_ball]
  have hsub : ball y s ∩ P ⊆ S ∩ ball y s := fun z hz => ⟨hPS hz.2, hz.1⟩
  refine (lintegral_mono_set hsub).trans' (lintegral_mono fun z => ?_)
  exact lintegral_mono fun t => ENNReal.div_le_div_right
    (jonesBetaSq_mono_measure (Measure.restrict_mono hPS le_rfl) z t) _

/-- **Transfer of the three hypotheses of `rectifiable_reifenberg`** to the rescaled frame. Let
`P ⊆ S`, where `S` satisfies the hypotheses of the theorem (finite `ℋ^{n-1}`, the upper bound
`C r^{n-1}` on all balls, and the square-function bound `< δ² s^{n-1}` on all `B_s(y) ⊆ B₂`), and
let `B_{Rr}(x) ⊆ B₂`. Then `μ' = rescaleMeasure (ℋ^{n-1}⌊P) x r` is finite, satisfies the upper
bound on all balls, and satisfies the square-function bound `≤ δ² s^{n-1}` on every
`B_s(y) ⊆ B_R(0)`. The proof of `rectifiable_reifenberg` applies it with `R = 16 = ledgerR0` (the
region on which the Reifenberg construction uses the hypotheses). -/
theorem rescale_hyp {C δ R : ℝ} {S P : Set (Rn n)} (hPS : P ⊆ S)
    (hfin : hausdorffN n (n - 1) S < ∞)
    (hup : ∀ (x : Rn n) (r : ℝ), 0 < r →
      hausdorffN n (n - 1) (S ∩ ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (hsq : ∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball 0 2 →
      ∫⁻ z in S ∩ ball y s, (∫⁻ t in Ioo 0 s,
          jonesBetaSq ((hausdorffN n (n - 1)).restrict S) z t / ENNReal.ofReal t)
        ∂hausdorffN n (n - 1) < ENNReal.ofReal (δ ^ 2 * s ^ (n - 1)))
    {x : Rn n} {r : ℝ} (hr : 0 < r) (hxr : ball x (R * r) ⊆ ball 0 2) :
    IsFiniteMeasure (rescaleMeasure ((hausdorffN n (n - 1)).restrict P) x r) ∧
    (∀ (y : Rn n) (s : ℝ), 0 < s →
      rescaleMeasure ((hausdorffN n (n - 1)).restrict P) x r (ball y s) ≤
        ENNReal.ofReal (C * s ^ (n - 1))) ∧
    (∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball 0 R →
      ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s,
          jonesBetaSq (rescaleMeasure ((hausdorffN n (n - 1)).restrict P) x r) z t /
            ENNReal.ofReal t) ∂rescaleMeasure ((hausdorffN n (n - 1)).restrict P) x r ≤
        ENNReal.ofReal (δ ^ 2 * s ^ (n - 1))) := by
  have hPfin : IsFiniteMeasure ((hausdorffN n (n - 1)).restrict P) :=
    isFiniteMeasure_restrict.2 (ne_top_of_le_ne_top hfin.ne (measure_mono hPS))
  refine ⟨inferInstance, fun y s hs => ?_, fun y s hs hyR => ?_⟩
  · refine measure_ball_rescaleMeasure_le (fun x' r' hr' => ?_) hr y hs
    rw [Measure.restrict_apply measurableSet_ball]
    have hsub : ball x' r' ∩ P ⊆ S ∩ ball x' r' := fun z hz => ⟨hPS hz.2, hz.1⟩
    exact (measure_mono hsub).trans (hup x' r' hr')
  · refine lintegral_rescaleMeasure_le hr (fun y' s' hs' hsub => ?_) y hs hyR
    exact (lintegral_restrict_le_of_subset hPS y' s').trans (hsq y' s' hs' (hsub.trans hxr)).le

end GMTFoundations
