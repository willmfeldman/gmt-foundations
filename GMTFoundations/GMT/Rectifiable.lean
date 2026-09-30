/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.GMT.FlatPiece
public import GMTFoundations.GMT.Packing
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Flat-piece covers of rectifiable sets

A countably `(n-1)`-rectifiable set `S ⊆ ℝⁿ` is covered, up to an `ℋ^{n-1}`-null set, by countably
many measurable `ε`-flat pieces (`IsFlatPiece`), for every `ε > 0`. This is the classical
decomposition of a Lipschitz image into pieces close to their tangent planes (see the
books of Federer and Mattila cited below).

For a Lipschitz map `f : ℝ^{n-1} → ℝⁿ` the domain splits into three parts.

* Non-differentiability points: Lebesgue-null by Rademacher (`LipschitzWith.ae_differentiableAt`),
  so their image is `ℋ^{n-1}`-null (`LipschitzWith.euclideanHausdorffMeasure_image_eq_zero`).
* Critical points, where `Df` is not injective: their image is `ℋ^{n-1}`-null
  (`LipschitzWith.euclideanHausdorffMeasure_image_critical`, Sard for Lipschitz maps). Near such a
  point the image of `B̄_r(a)` lies within `δ r` of an affine subspace of dimension `≤ n - 2`, so
  the tube-packing bound `NaberValtorta.card_mul_le_of_subset_thickening` covers it by `≲ δ^{2-n}`
  balls of radius `δ r`. A Besicovitch disjoint covering of the critical set then gives
  `ℋ^{n-1}(f(critical)) ≲ δ`.
* Regular points: they lie in countably many `regularPiece`s, on which `f` is close to a fixed
  injective linear map `T` at all pairs of points, so the image is flat with respect to the unit
  normal of `range T` (`isFlatPiece_image_regularPiece`).

* `exists_flatPiece_cover_range`: the statement for a single Lipschitz map (closed pieces).
* `IsCountablyRectifiable.exists_flatPiece_cover`: the statement for rectifiable sets.

## References

* H. Federer, *Geometric Measure Theory*, Springer, 1969.
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Cambridge University Press,
  1995.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace GMTFoundations.GMT

variable {n : ℕ}

/-! ### Preliminaries -/

theorem isFlatPiece_closure {ν : Rn n} {ε : ℝ} {G : Set (Rn n)} (h : IsFlatPiece ν ε G) :
    IsFlatPiece ν ε (_root_.closure G) := by
  intro y hy z hz
  have hc : Continuous fun q : Rn n × Rn n => ε * ‖q.1 - q.2‖ - |⟪q.1 - q.2, ν⟫| := by
    fun_prop
  have hmem : (y, z) ∈ _root_.closure (G ×ˢ G) := by
    rw [closure_prod_eq]
    exact ⟨hy, hz⟩
  have hsub : G ×ˢ G ⊆ {q : Rn n × Rn n | 0 ≤ ε * ‖q.1 - q.2‖ - |⟪q.1 - q.2, ν⟫|} := by
    rintro ⟨q1, q2⟩ ⟨h1, h2⟩
    simp only [mem_ofPred_eq, sub_nonneg]
    exact h q1 h1 q2 h2
  have := closure_minimal hsub (isClosed_le continuous_const hc) hmem
  simp only [mem_ofPred_eq, sub_nonneg] at this
  exact this

/-- A Lipschitz map `ℝ^k → ℝⁿ` maps Lebesgue-null sets to `μHE[k]`-null sets. -/
theorem _root_.LipschitzWith.euclideanHausdorffMeasure_image_eq_zero {k : ℕ} {f : Rn k → Rn n}
    {K : ℝ≥0} (hf : LipschitzWith K f) {N : Set (Rn k)} (hN : volume N = 0) :
    (μHE[k] : Measure (Rn n)) (f '' N) = 0 := by
  have h1 : (μHE[k] : Measure (Rn k)) N = 0 := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact hN
  have := (hf.lipschitzOnWith (s := N)).euclideanHausdorffMeasure_image_le k
  rw [h1, mul_zero] at this
  exact le_antisymm this (by positivity)

/-- The image of the non-differentiability points of a Lipschitz map is null (Rademacher). -/
theorem _root_.LipschitzWith.euclideanHausdorffMeasure_image_not_differentiableAt {k : ℕ}
    {f : Rn k → Rn n} {K : ℝ≥0} (hf : LipschitzWith K f) :
    (μHE[k] : Measure (Rn n)) (f '' {a | ¬ DifferentiableAt ℝ f a}) = 0 :=
  hf.euclideanHausdorffMeasure_image_eq_zero (ae_iff.1 (hf.ae_differentiableAt (μ := volume)))

/-- A non-injective linear map `ℝ^{n-1} → ℝⁿ` has rank at most `n - 2`. -/
theorem finrank_range_le_of_not_injective (hn : 2 ≤ n) {L : Rn (n - 1) →L[ℝ] Rn n}
    (hL : ¬ Function.Injective L) :
    Module.finrank ℝ (LinearMap.range (L : Rn (n - 1) →ₗ[ℝ] Rn n)) ≤ n - 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (L : Rn (n - 1) →ₗ[ℝ] Rn n)
  rw [finrank_euclideanSpace_fin] at h
  have hker : LinearMap.ker (L : Rn (n - 1) →ₗ[ℝ] Rn n) ≠ ⊥ := fun h0 =>
    hL (by simpa using LinearMap.ker_eq_bot.1 h0)
  have : 0 < Module.finrank ℝ (LinearMap.ker (L : Rn (n - 1) →ₗ[ℝ] Rn n)) :=
    Nat.pos_of_ne_zero fun h0 => hker (Submodule.finrank_eq_zero.1 h0)
  omega

/-- Arithmetic for the tube-packing bound. -/
theorem card_le_of_packing {c ω δ K r : ℝ} {N : ℕ} (hN : 2 ≤ N) (hω : 0 < ω) (hδ : 0 < δ)
    (hr : 0 < r)
    (h : c * (ω * (δ * r / 2) ^ N) ≤
      (2 * (δ * r) + δ * r) ^ 2 * (2 * (K * r) + δ * r) ^ (N - 2)) :
    c ≤ (3 * δ) ^ 2 * (2 * K + δ) ^ (N - 2) / (ω * (δ / 2) ^ N) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  simp only [Nat.add_sub_cancel] at h ⊢
  rw [le_div_iff₀ (by positivity)]
  have hrm : 0 < r ^ (m + 2) := by positivity
  refine le_of_mul_le_mul_right ?_ hrm
  calc c * (ω * (δ / 2) ^ (m + 2)) * r ^ (m + 2) = c * (ω * (δ * r / 2) ^ (m + 2)) := by ring
    _ ≤ _ := h
    _ = (3 * δ) ^ 2 * (2 * K + δ) ^ m * r ^ (m + 2) := by
        rw [show 2 * (K * r) + δ * r = r * (2 * K + δ) by ring, mul_pow]
        ring

/-- **Local covering at a critical point.** Near a point where the derivative of a Lipschitz map
`ℝ^{n-1} → ℝⁿ` is not injective, the image of `B̄_r(a)` lies close to an affine subspace of
dimension `≤ n - 2`, hence is covered by `≤ C(n, K) δ^{2-n}` balls of radius `δ r`. -/
theorem exists_local_cover_of_not_injective (hn : 2 ≤ n) {f : Rn (n - 1) → Rn n} {K : ℝ≥0}
    (hf : LipschitzWith K f) {a : Rn (n - 1)} (hda : DifferentiableAt ℝ f a)
    (hinj : ¬ Function.Injective (fderiv ℝ f a)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ra > 0, ∀ r, 0 < r → r ≤ ra → ∃ F : Finset (Rn n),
      (F.card : ℝ) ≤ (3 * δ) ^ 2 * (2 * K + δ) ^ (n - 2) / (unitBallVolume n * (δ / 2) ^ n) ∧
        f '' closedBall a r ⊆ ⋃ c ∈ F, ball c (δ * r) := by
  set L := fderiv ℝ f a
  have hL := finrank_range_le_of_not_injective hn hinj
  set P : AffineSubspace ℝ (Rn n) :=
    AffineSubspace.mk' (f a) (LinearMap.range (L : Rn (n - 1) →ₗ[ℝ] Rn n))
  have hPdir : Module.finrank ℝ P.direction ≤ n - 2 := by
    rw [AffineSubspace.direction_mk']
    exact hL
  have ho := hda.hasFDerivAt.isLittleO.def (c := δ / 2) (by positivity)
  obtain ⟨e, he, hball⟩ := Metric.eventually_nhds_iff.1 ho
  refine ⟨e / 2, by positivity, fun r hr hre => ?_⟩
  have hrδ : 0 < δ * r := mul_pos hδ hr
  suffices hN : ∀ F : Finset (Rn n), ↑F ⊆ f '' closedBall a r →
      (F : Set (Rn n)).Pairwise (fun y z => δ * r ≤ dist y z) →
      (F.card : ℝ) ≤ (3 * δ) ^ 2 * (2 * K + δ) ^ (n - 2) / (unitBallVolume n * (δ / 2) ^ n) by
    obtain ⟨F, -, hcard, hcov⟩ := exists_finset_subset_cover hrδ hN
    exact ⟨F, hcard, hcov⟩
  intro F hFA hFs
  have hFx : ↑F ⊆ closedBall (f a) (K * r) := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hFA hy
    rw [mem_closedBall] at hb ⊢
    exact (hf.dist_le_mul b a).trans (by gcongr)
  have hFL : ↑F ⊆ thickening (δ * r) (P : Set (Rn n)) := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hFA hy
    rw [mem_closedBall] at hb
    refine mem_thickening_iff.2 ⟨f a + L (b - a), ?_, ?_⟩
    · rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left]
      exact LinearMap.mem_range_self _ _
    · have := hball (show dist b a < e by linarith)
      rw [dist_eq_norm, sub_add_eq_sub_sub]
      calc ‖f b - f a - L (b - a)‖ ≤ δ / 2 * ‖b - a‖ := this
        _ ≤ δ / 2 * r := by rw [← dist_eq_norm]; gcongr
        _ < δ * r := by linarith
  have h := NaberValtorta.card_mul_le_of_subset_thickening hn hPdir hrδ (by positivity) hrδ.le
    hFx hFL hFs
  exact card_le_of_packing hn (unitBallVolume_pos _) hδ hr h

/-! ### Sard's theorem for Lipschitz maps `ℝ^{n-1} → ℝⁿ` -/

theorem packing_const_mul_eq {N : ℕ} (hN : 2 ≤ N) {ω K δ : ℝ} (hω : 0 < ω) (hδ : 0 < δ) :
    (3 * δ) ^ 2 * (2 * K + δ) ^ (N - 2) / (ω * (δ / 2) ^ N) * (2 * δ) ^ (N - 1) =
      9 * 2 ^ N * 2 ^ (N - 1) * (2 * K + δ) ^ (N - 2) * δ / ω := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
  rw [div_pow, mul_pow, mul_pow]
  field_simp
  ring

/-- The covering estimate behind Sard's theorem, at a fixed scale ratio `δ`. -/
theorem hausdorffMeasure_image_critical_le (hn : 2 ≤ n) {f : Rn (n - 1) → Rn n} {K : ℝ≥0}
    (hf : LipschitzWith K f) (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    μH[((n - 1 : ℕ) : ℝ)]
        (f '' ({a | DifferentiableAt ℝ f a ∧ ¬ Function.Injective (fderiv ℝ f a)} ∩
          ball 0 j)) ≤
      ENNReal.ofReal ((3 * δ) ^ 2 * (2 * K + δ) ^ (n - 2) / (unitBallVolume n * (δ / 2) ^ n) *
          (2 * δ) ^ (n - 1)) *
        (volume (ball (0 : Rn (n - 1)) (j + 1)) / volume (ball (0 : Rn (n - 1)) 1)) := by
  set Zj := {a | DifferentiableAt ℝ f a ∧ ¬ Function.Injective (fderiv ℝ f a)} ∩
    ball (0 : Rn (n - 1)) j
  set Bδ := (3 * δ) ^ 2 * (2 * K + δ) ^ (n - 2) / (unitBallVolume n * (δ / 2) ^ n)
  have hBδ : 0 ≤ Bδ :=
    div_nonneg (by positivity) (mul_nonneg (unitBallVolume_pos n).le (by positivity))
  set V1 := volume (ball (0 : Rn (n - 1)) 1)
  set Vj := volume (ball (0 : Rn (n - 1)) (j + 1))
  have hV1 : V1 ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hV1t : V1 ≠ ∞ := measure_ball_lt_top.ne
  have hloc : ∀ a ∈ Zj, ∃ ra > 0, ∀ r, 0 < r → r ≤ ra → ∃ F : Finset (Rn n),
      (F.card : ℝ) ≤ Bδ ∧ f '' closedBall a r ⊆ ⋃ c ∈ F, ball c (δ * r) :=
    fun a ha => exists_local_cover_of_not_injective hn hf ha.1.1 ha.1.2 hδ
  choose! ra hra0 hra using hloc
  choose! Fs hFcard hFcov using hra
  set ρ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hρ : ∀ m, 0 < ρ m := fun m => by positivity
  have hρ1 : ∀ m, ρ m ≤ 1 := fun m => by
    simp only [ρ]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hcov : ∀ m : ℕ, ∃ (t : Set (Rn (n - 1))) (r : Rn (n - 1) → ℝ), t.Countable ∧ t ⊆ Zj ∧
      (∀ x ∈ t, r x ∈ Ioc 0 (ra x) ∩ Ioo 0 (ρ m)) ∧
      volume (Zj \ ⋃ x ∈ t, closedBall x (r x)) = 0 ∧
      t.PairwiseDisjoint (fun x => closedBall x (r x)) := fun m =>
    Besicovitch.exists_disjoint_closedBall_covering_ae volume (fun x => Ioc 0 (ra x)) Zj
      (fun x hx ε hε => ⟨min (ra x) (ε / 2), ⟨lt_min (hra0 x hx) (by linarith), min_le_left _ _⟩,
        lt_min (hra0 x hx) (by linarith), (min_le_right _ _).trans_lt (by linarith)⟩)
      (fun _ => ρ m) (fun _ _ => hρ m)
  choose t r htc htZ htr htnull htdisj using hcov
  set N := ⋃ m, Zj \ ⋃ x ∈ t m, closedBall x (r m x)
  have hfN : μH[((n - 1 : ℕ) : ℝ)] (f '' N) = 0 := euclideanHausdorffMeasure_eq_zero_iff.1
    (hf.euclideanHausdorffMeasure_image_eq_zero (measure_iUnion_null htnull))
  -- the covers
  set ι : ℕ → Type _ := fun m => Σ x : t m, ((Fs x (r m x) : Finset (Rn n)) : Set (Rn n))
  have hι : ∀ m, Countable (ι m) := fun m => by
    have := (htc m).to_subtype
    infer_instance
  set T : ∀ m, ι m → Set (Rn n) := fun m i =>
    f '' closedBall (i.1 : Rn (n - 1)) (r m i.1) ∩ ball (i.2 : Rn n) (δ * r m i.1)
  have hdiam : ∀ m (i : ι m), ediam (T m i) ≤ ENNReal.ofReal (2 * δ * r m i.1) := fun m i =>
    Metric.ediam_le_of_forall_dist_le fun y hy z hz => by
      have h1 := hy.2
      have h2 := hz.2
      rw [mem_ball] at h1 h2
      have := dist_triangle_right y z (i.2 : Rn n)
      linarith
  have hsub : ∀ m, f '' (Zj \ N) ⊆ ⋃ i, T m i := by
    rintro m _ ⟨a, ⟨haZ, haN⟩, rfl⟩
    have ha : a ∈ ⋃ x ∈ t m, closedBall x (r m x) := by
      by_contra h
      exact haN (mem_iUnion.2 ⟨m, haZ, h⟩)
    obtain ⟨x, hx, hax⟩ := mem_iUnion₂.1 ha
    have hrx := htr m x hx
    have := hFcov x (htZ m hx) (r m x) hrx.1.1 hrx.1.2 ⟨a, hax, rfl⟩
    obtain ⟨c, hc, hfc⟩ := mem_iUnion₂.1 this
    exact mem_iUnion.2 ⟨⟨⟨x, hx⟩, ⟨c, hc⟩⟩, ⟨a, hax, rfl⟩, hfc⟩
  have hρlim : Tendsto (fun m => ENNReal.ofReal (2 * δ * ρ m)) atTop (𝓝 0) := by
    have : Tendsto (fun m : ℕ => 2 * δ * ρ m) atTop (𝓝 (2 * δ * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
    rw [mul_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  have hle := Measure.hausdorffMeasure_le_liminf_tsum ((n - 1 : ℕ) : ℝ) (f '' (Zj \ N)) (l := atTop)
    (fun m => ENNReal.ofReal (2 * δ * ρ m)) hρlim T
    (Eventually.of_forall fun m i => (hdiam m i).trans (ENNReal.ofReal_le_ofReal (by
      have := (htr m i.1 i.1.2).2.2
      nlinarith)))
    (Eventually.of_forall hsub)
  -- the sums
  have hsumr : ∀ m, ∑' x : t m, ENNReal.ofReal (r m x ^ (n - 1)) ≤ Vj / V1 := by
    intro m
    have hunion : ∑' x : t m, ENNReal.ofReal (r m x ^ (n - 1)) * V1 =
        volume (⋃ x ∈ t m, closedBall x (r m x)) := by
      rw [measure_biUnion (htc m) (htdisj m) (fun x _ => measurableSet_closedBall)]
      refine tsum_congr fun x => ?_
      rw [Measure.addHaar_closedBall volume _ (htr m x x.2).1.1.le, finrank_euclideanSpace_fin]
    have hsubj : (⋃ x ∈ t m, closedBall x (r m x)) ⊆ ball (0 : Rn (n - 1)) (j + 1) := by
      refine iUnion₂_subset fun x hx y hy => ?_
      have hxj := (htZ m hx).2
      rw [mem_ball, dist_zero_right] at hxj ⊢
      rw [mem_closedBall] at hy
      have := norm_le_norm_add_norm_sub' y x
      have hr := (htr m x hx).2.2
      have := hρ1 m
      rw [← dist_eq_norm] at *
      linarith
    rw [ENNReal.le_div_iff_mul_le (Or.inl hV1) (Or.inl hV1t), ← ENNReal.tsum_mul_right, hunion]
    exact measure_mono hsubj
  have hsum : ∀ m, ∑' i : ι m, ediam (T m i) ^ ((n - 1 : ℕ) : ℝ) ≤
      ENNReal.ofReal (Bδ * (2 * δ) ^ (n - 1)) * (Vj / V1) := by
    intro m
    calc ∑' i : ι m, ediam (T m i) ^ ((n - 1 : ℕ) : ℝ)
        ≤ ∑' i : ι m, ENNReal.ofReal ((2 * δ * r m i.1) ^ (n - 1)) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          rw [ENNReal.ofReal_pow (by have := (htr m i.1 i.1.2).1.1; positivity),
            ← ENNReal.rpow_natCast]
          exact ENNReal.rpow_le_rpow (hdiam m i) (Nat.cast_nonneg (n - 1))
      _ = ∑' x : t m, ∑' _c : ((Fs x (r m x) : Finset (Rn n)) : Set (Rn n)),
            ENNReal.ofReal ((2 * δ * r m x) ^ (n - 1)) := ENNReal.tsum_sigma' _
      _ = ∑' x : t m, ((Fs x (r m x)).card : ℝ≥0∞) *
            ENNReal.ofReal ((2 * δ * r m x) ^ (n - 1)) := by
          refine tsum_congr fun x => ?_
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ]
          simp only [Finset.coe_sort_coe, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ ∑' x : t m,
            ENNReal.ofReal (Bδ * (2 * δ) ^ (n - 1)) * ENNReal.ofReal (r m x ^ (n - 1)) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          have hr0 := (htr m x x.2).1.1
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_pow, show Bδ * (2 * δ) ^ (n - 1) * r m x ^ (n - 1) =
            Bδ * ((2 * δ) ^ (n - 1) * r m x ^ (n - 1)) by ring]
          exact mul_le_mul_of_nonneg_right (hFcard x (htZ m x.2) _ hr0 (htr m x x.2).1.2)
            (by positivity)
      _ = ENNReal.ofReal (Bδ * (2 * δ) ^ (n - 1)) * ∑' x : t m, ENNReal.ofReal (r m x ^ (n - 1)) :=
          ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact hsumr m
  calc μH[((n - 1 : ℕ) : ℝ)] (f '' Zj) ≤ μH[((n - 1 : ℕ) : ℝ)] (f '' (Zj \ N) ∪ f '' N) := by
        refine measure_mono ?_
        rw [← image_union, sdiff_union_self]
        exact image_mono subset_union_left
    _ ≤ μH[((n - 1 : ℕ) : ℝ)] (f '' (Zj \ N)) + μH[((n - 1 : ℕ) : ℝ)] (f '' N) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Bδ * (2 * δ) ^ (n - 1)) * (Vj / V1) := by
        rw [hfN, add_zero]
        exact hle.trans (liminf_le_of_frequently_le' (Eventually.of_forall hsum).frequently)

/-- **Sard's theorem for Lipschitz maps `ℝ^{n-1} → ℝⁿ`.** The image of the points where the
derivative is not injective is `ℋ^{n-1}`-null (Lipschitz case). -/
theorem _root_.LipschitzWith.euclideanHausdorffMeasure_image_critical (hn : 2 ≤ n)
    {f : Rn (n - 1) → Rn n} {K : ℝ≥0} (hf : LipschitzWith K f) :
    (μHE[n - 1] : Measure (Rn n))
      (f '' {a | DifferentiableAt ℝ f a ∧ ¬ Function.Injective (fderiv ℝ f a)}) = 0 := by
  set Z := {a | DifferentiableAt ℝ f a ∧ ¬ Function.Injective (fderiv ℝ f a)}
  rw [euclideanHausdorffMeasure_eq_zero_iff]
  have hZ : f '' Z ⊆ ⋃ j : ℕ, f '' (Z ∩ ball 0 j) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨j, hj⟩ := exists_nat_gt ‖a‖
    exact mem_iUnion.2 ⟨j, a, ⟨ha, by rwa [mem_ball, dist_zero_right]⟩, rfl⟩
  refine measure_mono_null hZ (measure_iUnion_null fun j => ?_)
  set W := volume (ball (0 : Rn (n - 1)) (j + 1)) / volume (ball (0 : Rn (n - 1)) 1)
  have hW : W ≠ ∞ := ENNReal.div_ne_top measure_ball_lt_top.ne
    (measure_ball_pos _ _ one_pos).ne'
  set g : ℝ → ℝ := fun δ => 9 * 2 ^ n * 2 ^ (n - 1) * (2 * K + δ) ^ (n - 2) * δ /
    unitBallVolume n
  have hg : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have : Continuous g := by fun_prop
    have h0 : g 0 = 0 := by simp [g]
    simpa [h0] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun δ => ENNReal.ofReal (g δ) * W) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hg) (Or.inr hW)
  refine le_antisymm (ge_of_tendsto hlim ?_) (by positivity)
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  have := hausdorffMeasure_image_critical_le hn hf j hδ
  rwa [packing_const_mul_eq hn (unitBallVolume_pos n) hδ] at this

/-! ### Regular points -/

/-- A linear map `ℝ^{n-1} → ℝⁿ` has a unit normal to its range. -/
theorem exists_unit_orthogonal_range (hn : 2 ≤ n) (T : Rn (n - 1) →L[ℝ] Rn n) :
    ∃ ν : Rn n, ‖ν‖ = 1 ∧ ∀ v, ⟪T v, ν⟫ = 0 := by
  set R := LinearMap.range (T : Rn (n - 1) →ₗ[ℝ] Rn n)
  have h1 : Module.finrank ℝ R ≤ n - 1 := by
    have := LinearMap.finrank_range_le (T : Rn (n - 1) →ₗ[ℝ] Rn n)
    rwa [finrank_euclideanSpace_fin] at this
  have h2 := R.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at h2
  have h3 : Rᗮ ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at h2
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  refine ⟨‖w‖⁻¹ • w, ?_, fun v => ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
  have := Submodule.inner_right_of_mem_orthogonal
    (LinearMap.mem_range_self (T : Rn (n - 1) →ₗ[ℝ] Rn n) v) hw
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [inner_smul_right, this, mul_zero]

/-- The pieces of the regular set: `λ`-co-Lipschitz model map `T`, derivative within `θλ` of `T`,
first-order Taylor expansion with error `θλ` on balls of radius `ρ`, and position within `ρ/3`
of the point `z`. -/
def regularPiece (f : Rn (n - 1) → Rn n) (T : Rn (n - 1) →L[ℝ] Rn n) (θ lam ρ : ℝ)
    (z : Rn (n - 1)) : Set (Rn (n - 1)) :=
  {a | (∀ v, lam * ‖v‖ ≤ ‖T v‖) ∧ ‖fderiv ℝ f a - T‖ ≤ θ * lam ∧
    (∀ b, dist b a ≤ ρ → ‖f b - f a - fderiv ℝ f a (b - a)‖ ≤ θ * lam * ‖b - a‖) ∧
    dist a z < ρ / 3}

/-- The image of a regular piece is flat. -/
theorem isFlatPiece_image_regularPiece {f : Rn (n - 1) → Rn n} {T : Rn (n - 1) →L[ℝ] Rn n}
    {ν : Rn n} (hν : ‖ν‖ = 1) (hνT : ∀ v, ⟪T v, ν⟫ = 0) {ε θ lam ρ : ℝ}
    (hθ : 2 * θ ≤ ε * (1 - 2 * θ)) (hε : 0 ≤ ε) (hlam : 0 < lam) (z : Rn (n - 1)) :
    IsFlatPiece ν ε (f '' regularPiece f T θ lam ρ z) := by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
  have hbc : dist b c ≤ ρ := by
    have := dist_triangle_right b c z
    linarith [hb.2.2.2, hc.2.2.2, dist_nonneg (x := b) (y := z)]
  set D := fderiv ℝ f c
  set err := f b - f c - T (b - c)
  have herr : ‖err‖ ≤ 2 * θ * lam * ‖b - c‖ := by
    have h1 := hc.2.2.1 b hbc
    have h2 : ‖(D - T) (b - c)‖ ≤ θ * lam * ‖b - c‖ :=
      ((D - T).le_opNorm _).trans (by gcongr; exact hc.2.1)
    have : err = (f b - f c - D (b - c)) + (D - T) (b - c) := by
      simp only [err, sub_apply]
      abel
    rw [this]
    exact (norm_add_le _ _).trans (by linarith)
  have hinner : ⟪f b - f c, ν⟫ = ⟪err, ν⟫ := by
    simp only [err, inner_sub_left, hνT, sub_zero]
  have hlow : (1 - 2 * θ) * (lam * ‖b - c‖) ≤ ‖f b - f c‖ := by
    have h1 := hb.1 (b - c)
    have h2 : ‖T (b - c)‖ ≤ ‖f b - f c‖ + ‖err‖ := by
      have : T (b - c) = (f b - f c) - err := by simp only [err]; abel
      rw [this]
      exact norm_sub_le _ _
    linarith
  rw [hinner]
  calc |⟪err, ν⟫| ≤ ‖err‖ * ‖ν‖ := abs_real_inner_le_norm _ _
    _ ≤ 2 * θ * (lam * ‖b - c‖) := by rw [hν, mul_one]; linarith
    _ ≤ ε * (1 - 2 * θ) * (lam * ‖b - c‖) := by gcongr
    _ ≤ ε * ‖f b - f c‖ := by rw [mul_assoc]; gcongr

/-- Every regular point lies in some regular piece. -/
theorem exists_mem_regularPiece {f : Rn (n - 1) → Rn n} {a : Rn (n - 1)}
    (hda : DifferentiableAt ℝ f a) (hinj : Function.Injective (fderiv ℝ f a))
    {T : ℕ → Rn (n - 1) →L[ℝ] Rn n} (hT : DenseRange T) {z : ℕ → Rn (n - 1)} (hz : DenseRange z)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ i : ℕ × ℕ × ℕ × ℕ, a ∈ regularPiece f (T i.1) θ (1 / ((i.2.1 : ℝ) + 1))
      (1 / ((i.2.2.1 : ℝ) + 1)) (z i.2.2.2) := by
  set L := fderiv ℝ f a
  obtain ⟨C, hC, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz (L : Rn (n - 1) →ₗ[ℝ] Rn n)).1 hinj
  have hCpos : (0 : ℝ) < C := hC
  have hLv : ∀ v, (C : ℝ)⁻¹ * ‖v‖ ≤ ‖L v‖ := fun v => by
    have := hanti.le_mul_dist v 0
    simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at this
    rw [inv_mul_le_iff₀ hCpos]
    exact this
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt (half_pos (inv_pos.2 hCpos))
  set lam := 1 / ((q : ℝ) + 1)
  have hlam : 0 < lam := by positivity
  obtain ⟨j, hj⟩ := hT.exists_dist_lt L (mul_pos hθ0 hlam)
  rw [dist_eq_norm] at hj
  have ho := hda.hasFDerivAt.isLittleO.def (c := θ * lam) (by positivity)
  obtain ⟨e, he, hball⟩ := Metric.eventually_nhds_iff.1 ho
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt he
  obtain ⟨p, hp⟩ := hz.exists_dist_lt a (show 0 < 1 / ((m : ℝ) + 1) / 3 by positivity)
  refine ⟨(j, q, m, p), fun v => ?_, hj.le, fun b hb => hball (lt_of_le_of_lt hb hm), hp⟩
  have h1 := hLv v
  have h2 : ‖(L - T j) v‖ ≤ θ * lam * ‖v‖ :=
    ((L - T j).le_opNorm v).trans (by gcongr)
  have h3 : ‖L v‖ ≤ ‖T j v‖ + ‖(L - T j) v‖ := by
    rw [sub_apply]
    have := norm_sub_norm_le (L v) (T j v)
    linarith
  have h4 : θ * lam * ‖v‖ ≤ lam * ‖v‖ := by
    have := norm_nonneg v
    linarith [mul_nonneg (sub_nonneg.2 hθ1) (mul_nonneg hlam.le this)]
  have h5 : 2 * lam * ‖v‖ ≤ (C : ℝ)⁻¹ * ‖v‖ := by
    linarith [mul_le_mul_of_nonneg_right hq.le (norm_nonneg v)]
  change lam * ‖v‖ ≤ ‖T j v‖
  linarith

/-- **Flat pieces of a Lipschitz image.** The image
of a Lipschitz map `ℝ^{n-1} → ℝⁿ` is covered, up to an `ℋ^{n-1}`-null set, by countably many
measurable `ε`-flat pieces. -/
theorem exists_flatPiece_cover_range (hn : 2 ≤ n) {f : Rn (n - 1) → Rn n} {K : ℝ≥0}
    (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (G : ℕ → Set (Rn n)) (ν : ℕ → Rn n), (∀ i, MeasurableSet (G i)) ∧ (∀ i, ‖ν i‖ = 1) ∧
      (∀ i, IsFlatPiece (ν i) ε (G i)) ∧
      (μHE[n - 1] : Measure (Rn n)) (range f \ ⋃ i, G i) = 0 := by
  set θ := min ε 1 / 8
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by have := min_le_right ε 1; simp only [θ]; linarith
  have hθ : 2 * θ ≤ ε * (1 - 2 * θ) := by
    have h1 := min_le_left ε 1
    have h2 := min_le_right ε 1
    simp only [θ]
    nlinarith
  obtain ⟨T, hT⟩ := TopologicalSpace.exists_dense_seq (Rn (n - 1) →L[ℝ] Rn n)
  obtain ⟨z, hz⟩ := TopologicalSpace.exists_dense_seq (Rn (n - 1))
  choose νT hνT1 hνT using fun j => exists_unit_orthogonal_range hn (T j)
  set E : ℕ × ℕ × ℕ × ℕ → Set (Rn (n - 1)) := fun i =>
    regularPiece f (T i.1) θ (1 / ((i.2.1 : ℝ) + 1)) (1 / ((i.2.2.1 : ℝ) + 1)) (z i.2.2.2)
  set e := Denumerable.eqv (ℕ × ℕ × ℕ × ℕ)
  refine ⟨fun i => _root_.closure (f '' E (e.symm i)), fun i => νT (e.symm i).1,
    fun i => isClosed_closure.measurableSet, fun i => hνT1 _, fun i => isFlatPiece_closure
      (isFlatPiece_image_regularPiece (hνT1 _) (hνT _) hθ hε.le (by positivity) _), ?_⟩
  refine measure_mono_null (t := f '' {a | ¬ DifferentiableAt ℝ f a} ∪
      f '' {a | DifferentiableAt ℝ f a ∧ ¬ Function.Injective (fderiv ℝ f a)}) ?_
    (measure_union_null hf.euclideanHausdorffMeasure_image_not_differentiableAt
      (hf.euclideanHausdorffMeasure_image_critical hn))
  rintro _ ⟨⟨a, rfl⟩, hG⟩
  by_cases hda : DifferentiableAt ℝ f a
  · by_cases hinj : Function.Injective (fderiv ℝ f a)
    · obtain ⟨i, hi⟩ := exists_mem_regularPiece hda hinj hT hz hθ0 hθ1
      refine absurd (mem_iUnion.2 ⟨e i, ?_⟩) hG
      rw [Equiv.symm_apply_apply]
      exact subset_closure ⟨a, hi, rfl⟩
    · exact Or.inr ⟨a, ⟨hda, hinj⟩, rfl⟩
  · exact Or.inl ⟨a, hda, rfl⟩

/-- A countably `(n-1)`-rectifiable set is covered, up to an `ℋ^{n-1}`-null set, by countably many
measurable `ε`-flat pieces. -/
theorem _root_.GMTFoundations.IsCountablyRectifiable.exists_flatPiece_cover (hn : 2 ≤ n)
    {S : Set (Rn n)} (hS : IsCountablyRectifiable n (n - 1) S) {ε : ℝ} (hε : 0 < ε) :
    ∃ (G : ℕ × ℕ → Set (Rn n)) (ν : ℕ × ℕ → Rn n), (∀ i, MeasurableSet (G i)) ∧
      (∀ i, ‖ν i‖ = 1) ∧ (∀ i, IsFlatPiece (ν i) ε (G i)) ∧
      (μHE[n - 1] : Measure (Rn n)) (S \ ⋃ i, G i) = 0 := by
  obtain ⟨f, hf, hnull⟩ := hS
  choose K hK using hf
  choose G ν hGm hν hflat hGnull using fun i => exists_flatPiece_cover_range hn (hK i) hε
  refine ⟨fun p => G p.1 p.2, fun p => ν p.1 p.2, fun p => hGm _ _, fun p => hν _ _,
    fun p => hflat _ _, ?_⟩
  refine measure_mono_null (t := (S \ ⋃ i, range (f i)) ∪ ⋃ i, (range (f i) \ ⋃ j, G i j))
    ?_ (measure_union_null (hausdorffN_eq_zero_iff_euclidean.1 hnull)
      (measure_iUnion_null hGnull))
  rintro x ⟨hxS, hxG⟩
  by_cases hx : x ∈ ⋃ i, range (f i)
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    refine Or.inr (mem_iUnion.2 ⟨i, hi, fun h => hxG ?_⟩)
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact mem_iUnion.2 ⟨(i, j), hj⟩
  · exact Or.inl ⟨hxS, hx⟩

end GMTFoundations.GMT
