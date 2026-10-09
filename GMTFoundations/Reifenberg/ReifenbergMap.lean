/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.Hyperplane
public import GMTFoundations.Reifenberg.PartitionOfUnity
public import GMTFoundations.GMT.FlatPiece
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Graphs over planes, Reifenberg maps, and the inverse-function device

The Reifenberg map of M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn.
Math. 43 (2018); arXiv:1612.02461 (Definition 3.1; hereafter Miś), for hyperplanes, together with
the graph and chart language used by the squash lemma (`Reifenberg/Squash.lean`), regraphing
(`Reifenberg/Regraph.lean`), and single-scale injectivity and the engine
(`Reifenberg/Engine.lean`). All Reifenberg geometry in this library is specialized to
hyperplanes (`k = n − 1`): planes are pairs `P = (p, ν)`, with `f_P(w) = ⟪w − p, ν⟫`,
`affPlane P = {f_P = 0}` and `affProj P w = w − f_P(w) ν` (`Reifenberg/Hyperplane.lean`).

Miś Definition 3.1 refers to points `p_i` that are not defined there (a leftover of the base
points of the planes in Definition 4.10 of A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the
regularity of stationary and minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227;
arXiv:1504.02043), and to a smooth partition of unity with properties (1)–(4) that is not
constructed. Here the planes carry their base points `p_c`, and
the partition of unity is the explicit Lipschitz one of `Reifenberg/PartitionOfUnity.lean`.

## Main definitions

* `graphOn P g = (x ↦ x + g x • ν) '' affPlane P`: the graph of a global `g : Rn n → ℝ` over the
  plane. Graphs are always of globally defined scalar functions; charts localize them to balls.
* `disc P c R = affPlane P ∩ ball (affProj P c) R`.
* `IsChart T P g c R r δ`: `T ∩ B_R(c) = graphOn P g ∩ B_R(c)`, with `|g| ≤ δ r` and `Lip g ≤ δ` on
  `disc P c R` (the max-form of Miś's normalized norm `r⁻¹ sup |g| + Lip g`, which is
  equivalent up to a factor 2).
* `reifenbergMap r Y Vp w = w − Σ_{c ∈ Y} λ_c(w) f_c(w) ν_c` (Miś Def 3.1).

## Main statements

* (G1) `mem_disc_of_add_smul_mem_ball`, Lemma G `IsChart.exists_global`, restriction
  `IsChart.mono`, rescaling `IsChart.rescale`.
* (2.1)–(2.3) `reifenbergMap_eq_self`, `norm_reifenbergMap_sub_le`, `reifenbergMap_of_subset`.
* `perturbId`: `id + H` with `H` `ℓ`-Lipschitz, `ℓ < 1`, `H ⊥ ν`, is a homeomorphism
  preserving `⟪·, ν⟫`.
* PL `norm_sum_smul_sub_le`, the product lemma.
-/

public noncomputable section

namespace GMTFoundations

open Metric Set
open scoped RealInnerProductSpace NNReal

variable {n : ℕ}

/-! ### Constants -/

/-- The squash constant `C_sq(n) = 9^{n+2}` (see `squash`). -/
@[expose] def C_sq (n : ℕ) : ℝ := 9 ^ (n + 2)

/-- The squash threshold `δ_sq(n) = 9^{-(n+2)} = 1 / C_sq(n)` on `δ₁`
(hypothesis (Hs) of `squash`). -/
@[expose] def δ_sq (n : ℕ) : ℝ := 1 / C_sq n

theorem C_sq_eq (n : ℕ) : C_sq n = 81 * 9 ^ n := by rw [C_sq, pow_add]; ring

theorem C_sq_pos (n : ℕ) : 0 < C_sq n := by rw [C_sq]; positivity

theorem one_le_C_sq (n : ℕ) : 1 ≤ C_sq n := by
  rw [C_sq_eq]; linarith [one_le_pow₀ (M₀ := ℝ) (a := 9) (by norm_num) (n := n)]

/-! ### Graphs, discs, charts -/

/-- The graph of `g : Rn n → ℝ` over the plane `P = (p, ν)`: `{x + g(x) ν | x ∈ affPlane P}`. -/
@[expose] def graphOn (P : Rn n × Rn n) (g : Rn n → ℝ) : Set (Rn n) :=
  (fun x => x + g x • P.2) '' affPlane P

/-- The disc `affPlane P ∩ B_R(π_P c)`. -/
@[expose] def disc (P : Rn n × Rn n) (c : Rn n) (R : ℝ) : Set (Rn n) :=
  affPlane P ∩ ball (affProj P c) R

/-- `IsChart T P g c R r δ`: on `B_R(c)`, `T` is the graph of `g` over `P`, and `‖g‖_{r} ≤ δ` on the
disc (max-form: `|g| ≤ δ r` and `Lip g ≤ δ`). -/
@[expose] def IsChart (T : Set (Rn n)) (P : Rn n × Rn n) (g : Rn n → ℝ) (c : Rn n) (R r δ : ℝ) :
    Prop :=
  T ∩ ball c R = graphOn P g ∩ ball c R ∧ (∀ x ∈ disc P c R, |g x| ≤ δ * r) ∧
    LipschitzOnWith (Real.toNNReal δ) g (disc P c R)

variable {P : Rn n × Rn n} {x x' w w' c c' : Rn n} {t : ℝ} {g g' : Rn n → ℝ} {T : Set (Rn n)}
  {R R' r δ δ' : ℝ}

theorem add_smul_mem_graphOn (hx : x ∈ affPlane P) : x + g x • P.2 ∈ graphOn P g :=
  ⟨x, hx, rfl⟩

theorem inner_sub_eq_zero_of_mem (hx : x ∈ affPlane P) (hx' : x' ∈ affPlane P) :
    ⟪x - x', P.2⟫ = 0 := by
  rw [show x - x' = (x - P.1) - (x' - P.1) by abel, inner_sub_left, mem_affPlane.1 hx,
    mem_affPlane.1 hx', sub_zero]

theorem inner_add_smul_sub_of_mem (hP : ‖P.2‖ = 1) (hx : x ∈ affPlane P) (t : ℝ) :
    ⟪x + t • P.2 - P.1, P.2⟫ = t := by
  rw [add_sub_right_comm, inner_add_left, mem_affPlane.1 hx, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hP]
  ring

theorem affProj_add_smul_of_mem (hP : ‖P.2‖ = 1) (hx : x ∈ affPlane P) (t : ℝ) :
    affProj P (x + t • P.2) = x := by
  rw [affProj, inner_add_smul_sub_of_mem hP hx, add_sub_cancel_right]

theorem affProj_add_inner_smul (P : Rn n × Rn n) (w : Rn n) :
    affProj P w + ⟪w - P.1, P.2⟫ • P.2 = w :=
  sub_add_cancel _ _

theorem inner_sub_sub (P : Rn n × Rn n) (w w' : Rn n) :
    ⟪w - w', P.2⟫ = ⟪w - P.1, P.2⟫ - ⟪w' - P.1, P.2⟫ := by
  rw [← inner_sub_left]
  congr 1
  abel

theorem affProj_sub_affProj (P : Rn n × Rn n) (w w' : Rn n) :
    affProj P w - affProj P w' = GMT.projH P.2 (w - w') := by
  simp only [affProj, GMT.projH, inner_sub_sub P w w', sub_smul]
  abel

theorem dist_affProj_le (hP : ‖P.2‖ = 1) (w w' : Rn n) :
    dist (affProj P w) (affProj P w') ≤ dist w w' := by
  rw [dist_eq_norm, affProj_sub_affProj, dist_eq_norm]
  exact GMT.norm_projH_le hP _

theorem lipschitzWith_affProj (hP : ‖P.2‖ = 1) : LipschitzWith 1 (affProj P) :=
  LipschitzWith.of_dist_le_mul fun w w' => by
    rw [NNReal.coe_one, one_mul]
    exact dist_affProj_le hP w w'

/-- `‖u + t ν‖² = ‖u‖² + t²` for `u ⊥ ν`, `‖ν‖ = 1`. -/
theorem norm_add_smul_sq {ν u : Rn n} (hν : ‖ν‖ = 1) (hu : ⟪u, ν⟫ = 0) (t : ℝ) :
    ‖u + t • ν‖ ^ 2 = ‖u‖ ^ 2 + t ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, hu, norm_smul, Real.norm_eq_abs, hν]
  simp [sq_abs]

/-- Pythagoras relative to a plane:
`‖w − w'‖² = ‖π_P w − π_P w'‖² + (f_P w − f_P w')²`. -/
theorem norm_sub_sq_eq (hP : ‖P.2‖ = 1) (w w' : Rn n) :
    ‖w - w'‖ ^ 2 = ‖affProj P w - affProj P w'‖ ^ 2 +
      (⟪w - P.1, P.2⟫ - ⟪w' - P.1, P.2⟫) ^ 2 := by
  have hid : w - w' = (affProj P w - affProj P w') +
      (⟪w - P.1, P.2⟫ - ⟪w' - P.1, P.2⟫) • P.2 := by
    simp only [affProj, sub_smul]
    abel
  rw [hid, norm_add_smul_sq hP]
  exact inner_sub_eq_zero_of_mem (affProj_mem_affPlane hP w) (affProj_mem_affPlane hP w')

/-- For points of a plane, `‖(x + t ν) − (x' + t' ν)‖² = ‖x − x'‖² + (t − t')²`. -/
theorem norm_add_smul_sub_add_smul_sq (hP : ‖P.2‖ = 1) (hx : x ∈ affPlane P)
    (hx' : x' ∈ affPlane P) (t t' : ℝ) :
    ‖(x + t • P.2) - (x' + t' • P.2)‖ ^ 2 = ‖x - x'‖ ^ 2 + (t - t') ^ 2 := by
  rw [show (x + t • P.2) - (x' + t' • P.2) = (x - x') + (t - t') • P.2 by
    rw [sub_smul]; abel]
  exact norm_add_smul_sq hP (inner_sub_eq_zero_of_mem hx hx') _

theorem norm_sub_le_norm_add_smul_sub (hP : ‖P.2‖ = 1) (hx : x ∈ affPlane P)
    (hx' : x' ∈ affPlane P) (t t' : ℝ) :
    ‖x - x'‖ ≤ ‖(x + t • P.2) - (x' + t' • P.2)‖ := by
  have h := norm_add_smul_sub_add_smul_sq hP hx hx' t t'
  have h2 : ‖x - x'‖ ^ 2 ≤ ‖(x + t • P.2) - (x' + t' • P.2)‖ ^ 2 := by
    linarith [sq_nonneg (t - t')]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/-- (G1) If `x ∈ affPlane P` and `x + t ν ∈ B_R(c)` then `x ∈ disc P c R`. -/
theorem mem_disc_of_add_smul_mem_ball (hP : ‖P.2‖ = 1) (hx : x ∈ affPlane P)
    (h : x + t • P.2 ∈ ball c R) : x ∈ disc P c R := by
  refine ⟨hx, ?_⟩
  rw [mem_ball, ← affProj_add_smul_of_mem hP hx t]
  exact (dist_affProj_le hP _ _).trans_lt h

theorem affProj_mem_disc (hP : ‖P.2‖ = 1) (h : w ∈ ball c R) : affProj P w ∈ disc P c R :=
  ⟨affProj_mem_affPlane hP w, (dist_affProj_le hP w c).trans_lt h⟩

/-- Two functions that agree on `disc P c R` have the same graph inside `B_R(c)`. -/
theorem graphOn_inter_ball_congr (hP : ‖P.2‖ = 1) (h : EqOn g g' (disc P c R)) :
    graphOn P g ∩ ball c R = graphOn P g' ∩ ball c R := by
  ext w
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hw⟩
    have hd := mem_disc_of_add_smul_mem_ball hP hx hw
    refine ⟨⟨x, hx, ?_⟩, hw⟩
    simp only [h hd]
  · rintro ⟨⟨x, hx, rfl⟩, hw⟩
    have hd := mem_disc_of_add_smul_mem_ball hP hx hw
    refine ⟨⟨x, hx, ?_⟩, hw⟩
    simp only [h hd]

theorem disc_subset_disc (hP : ‖P.2‖ = 1) (h : dist c' c + R' ≤ R) :
    disc P c' R' ⊆ disc P c R := by
  rintro u ⟨hu, hu'⟩
  refine ⟨hu, ?_⟩
  rw [mem_ball] at hu' ⊢
  calc dist u (affProj P c) ≤ dist u (affProj P c') + dist (affProj P c') (affProj P c) :=
        dist_triangle _ _ _
    _ < R' + dist c' c := add_lt_add_of_lt_of_le hu' (dist_affProj_le hP _ _)
    _ ≤ R := by linarith

/-- Restriction of a chart to a sub-ball. -/
theorem IsChart.mono (hP : ‖P.2‖ = 1) (h : IsChart T P g c R r δ) (hc : dist c' c + R' ≤ R) :
    IsChart T P g c' R' r δ := by
  have hb : ball c' R' ⊆ ball c R := ball_subset_ball' (by linarith)
  have hd := disc_subset_disc hP hc
  refine ⟨?_, fun u hu => h.2.1 u (hd hu), h.2.2.mono hd⟩
  have e : ball c R ∩ ball c' R' = ball c' R' := inter_eq_right.2 hb
  calc T ∩ ball c' R' = T ∩ ball c R ∩ ball c' R' := by rw [inter_assoc, e]
    _ = graphOn P g ∩ ball c R ∩ ball c' R' := by rw [h.1]
    _ = _ := by rw [inter_assoc, e]

/-- Rescaling: `‖g‖_{r'} ≤ (r / r') ‖g‖_r` for `0 < r' ≤ r`. -/
theorem IsChart.rescale (h : IsChart T P g c R r δ) (hδ : 0 ≤ δ) {r' : ℝ} (hr' : 0 < r')
    (hrr : r' ≤ r) : IsChart T P g c R r' (δ * r / r') := by
  refine ⟨h.1, fun u hu => ?_, h.2.2.weaken (Real.toNNReal_le_toNNReal ?_)⟩
  · rw [div_mul_cancel₀ _ hr'.ne']
    exact h.2.1 u hu
  · rw [le_div_iff₀ hr']
    exact mul_le_mul_of_nonneg_left hrr hδ

/-- Lemma G (globalize): a chart function may be replaced by a global one with
`|ĝ| ≤ δ r` and `Lip ĝ ≤ δ` on all of `Rn n`, agreeing with `g` on the disc. -/
theorem IsChart.exists_global (hP : ‖P.2‖ = 1) (h : IsChart T P g c R r δ) (hδ : 0 ≤ δ)
    (hr : 0 ≤ r) :
    ∃ ĝ : Rn n → ℝ, (∀ x, |ĝ x| ≤ δ * r) ∧ LipschitzWith (Real.toNNReal δ) ĝ ∧
      EqOn ĝ g (disc P c R) ∧ IsChart T P ĝ c R r δ := by
  obtain ⟨e, he, heq⟩ := h.2.2.extend_real
  set M := δ * r
  have hM : 0 ≤ M := mul_nonneg hδ hr
  have hlip : LipschitzWith (Real.toNNReal δ) (fun x => max (-M) (min M (e x))) :=
    (he.const_min M).const_max (-M)
  have hEq : EqOn (fun x => max (-M) (min M (e x))) g (disc P c R) := fun x hx => by
    have hg := h.2.1 x hx
    rw [abs_le] at hg
    simp only
    rw [← heq hx, min_eq_right hg.2, max_eq_right hg.1]
  refine ⟨fun x => max (-M) (min M (e x)), fun x => ?_, hlip, hEq, ?_, fun x hx => ?_,
    hlip.lipschitzOnWith⟩
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · rw [h.1, graphOn_inter_ball_congr hP hEq]
  · rw [hEq hx]
    exact h.2.1 x hx

/-! ### The Reifenberg map (Miś Def 3.1) -/

/-- The Reifenberg map at scale `r` for the centres `Y` and planes `Vp c = (p_c, ν_c)`:
`σ(w) = w − Σ_{c ∈ Y} λ_c(w) ⟪w − p_c, ν_c⟫ ν_c`. -/
@[expose] def reifenbergMap (r : ℝ) (Y : Finset (Rn n)) (Vp : Rn n → Rn n × Rn n) (w : Rn n) :
    Rn n :=
  w - ∑ c ∈ Y, (puLambda r Y c w * ⟪w - (Vp c).1, (Vp c).2⟫) • (Vp c).2

variable {Y Y' : Finset (Rn n)} {Vp : Rn n → Rn n × Rn n}

/-- (2.1) `σ = id` off `⋃_c B_{4r}(c)`. -/
theorem reifenbergMap_eq_self (hr : 0 < r) (h : ∀ c ∈ Y, 4 * r ≤ dist w c) :
    reifenbergMap r Y Vp w = w := by
  rw [reifenbergMap, Finset.sum_eq_zero, sub_zero]
  intro c hc
  rw [puLambda_eq_zero hr (h c hc), zero_mul, zero_smul]

/-- (2.2) `‖σ(w) − w‖ ≤ Σ_c λ_c(w) |f_c(w)|`. -/
theorem norm_reifenbergMap_sub_le (hVp : ∀ c ∈ Y, ‖(Vp c).2‖ = 1) (w : Rn n) :
    ‖reifenbergMap r Y Vp w - w‖ ≤
      ∑ c ∈ Y, puLambda r Y c w * |⟪w - (Vp c).1, (Vp c).2⟫| := by
  rw [reifenbergMap, sub_sub_cancel_left, norm_neg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c hc => ?_)
  rw [norm_smul, hVp c hc, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg puLambda_nonneg]

/-- (2.3) Localization: if every centre of `Y \ Y'` is at distance `≥ 4r` from `w`, the maps of
`Y'` and `Y` agree at `w`. -/
theorem reifenbergMap_of_subset (hr : 0 < r) (hY' : Y' ⊆ Y)
    (h : ∀ c ∈ Y, c ∉ Y' → 4 * r ≤ dist w c) :
    reifenbergMap r Y' Vp w = reifenbergMap r Y Vp w := by
  rw [reifenbergMap, reifenbergMap]
  congr 1
  rw [Finset.sum_congr rfl fun c _ => by rw [puLambda_of_subset hr hY' h c]]
  refine Finset.sum_subset hY' fun c hc hc' => ?_
  rw [puLambda_eq_zero hr (h c hc hc'), zero_mul, zero_smul]

/-! ### The product lemma PL -/

/-- **PL.** For `u, u' ≥ 0` with `Σ u' ≤ 1`, `|b_i| ≤ A` where `u_i > 0`, `|b'_i| ≤ A` where
`u'_i > 0`, and `|b_i − b'_i| ≤ B` where `u_i > 0`:
`‖Σ u_i b_i − Σ u'_i b'_i‖ ≤ A Σ |u_i − u'_i| + B`. -/
theorem norm_sum_smul_sub_le {ι E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) {u u' : ι → ℝ} {b b' : ι → E} {A B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hu' : ∀ i ∈ s, 0 ≤ u' i) (hsum : ∑ i ∈ s, u' i ≤ 1)
    (hb : ∀ i ∈ s, 0 < u i → ‖b i‖ ≤ A) (hb' : ∀ i ∈ s, 0 < u' i → ‖b' i‖ ≤ A)
    (hbb : ∀ i ∈ s, 0 < u i → ‖b i - b' i‖ ≤ B) :
    ‖∑ i ∈ s, u i • b i - ∑ i ∈ s, u' i • b' i‖ ≤ A * ∑ i ∈ s, |u i - u' i| + B := by
  have hterm : ∀ i ∈ s, ‖u i • b i - u' i • b' i‖ ≤ A * |u i - u' i| + u' i * B := by
    intro i hi
    rcases (hu i hi).lt_or_eq with hpos | hzero
    · have hid : u i • b i - u' i • b' i = (u i - u' i) • b i + u' i • (b i - b' i) := by
        rw [sub_smul, smul_sub]; abel
      rw [hid]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hb i hi hpos) (abs_nonneg _)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hu' i hi)]
        exact mul_le_mul_of_nonneg_left (hbb i hi hpos) (hu' i hi)
    · rw [← hzero, zero_smul, zero_sub, norm_neg, zero_sub, abs_neg]
      rcases (hu' i hi).lt_or_eq with hpos' | hzero'
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hu' i hi), mul_comm A]
        have := mul_le_mul_of_nonneg_left (hb' i hi hpos') (hu' i hi)
        linarith [mul_nonneg (hu' i hi) hB]
      · rw [← hzero', zero_smul, norm_zero, abs_zero, mul_zero, zero_mul, add_zero]
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  linarith [mul_le_of_le_one_left hB hsum]

/-- The companion sup bound: `‖Σ u_i b_i‖ ≤ A` if `u ≥ 0`, `Σ u ≤ 1` and `|b_i| ≤ A` where
`u_i > 0`. -/
theorem norm_sum_smul_le {ι E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) {u : ι → ℝ} {b : ι → E} {A : ℝ} (hA : 0 ≤ A)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hsum : ∑ i ∈ s, u i ≤ 1)
    (hb : ∀ i ∈ s, 0 < u i → ‖b i‖ ≤ A) : ‖∑ i ∈ s, u i • b i‖ ≤ A := by
  have hterm : ∀ i ∈ s, ‖u i • b i‖ ≤ u i * A := by
    intro i hi
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hu i hi)]
    rcases (hu i hi).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hb i hi hpos) (hu i hi)
    · rw [← hzero, zero_mul, zero_mul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul]
  exact mul_le_of_le_one_left hA hsum

/-! ### The inverse-function device `perturbId` -/

/-- **perturbId**. If `H : Rn n → Rn n` is `ℓ`-Lipschitz with `ℓ < 1` and
`⟪H w, ν⟫ = 0` for all `w`, then `id + H` is a homeomorphism of `Rn n`, `(1 − ℓ)⁻¹`-antilipschitz,
preserving `⟪·, ν⟫` (hence every level set of `⟪· − p, ν⟫`). Built with
`ApproximatesLinearOn.toHomeomorph` (`f' = id`). -/
theorem perturbId {ν : Rn n} {H : Rn n → Rn n} {ℓ : ℝ≥0} (hℓ : ℓ < 1) (hH : LipschitzWith ℓ H)
    (hHν : ∀ w, ⟪H w, ν⟫ = 0) :
    ∃ e : Rn n ≃ₜ Rn n, (⇑e = fun w => w + H w) ∧ AntilipschitzWith (1 - ℓ)⁻¹ e ∧
      ∀ w, ⟪e w, ν⟫ = ⟪w, ν⟫ := by
  set f' : Rn n ≃L[ℝ] Rn n := ContinuousLinearEquiv.refl ℝ (Rn n)
  have hA : ApproximatesLinearOn (fun w => w + H w) (f' : Rn n →L[ℝ] Rn n) univ ℓ := by
    refine LipschitzOnWith.approximatesLinearOn ?_
    have : (fun w => w + H w) - ⇑(f' : Rn n →L[ℝ] Rn n) = H := by
      funext w
      simp [f']
    rw [this]
    exact hH.lipschitzOnWith
  have hc : Subsingleton (Rn n) ∨ ℓ < ‖(f'.symm : Rn n →L[ℝ] Rn n)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial (Rn n) with h | h
    · exact Or.inl h
    · right
      simp only [f', ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
        ContinuousLinearMap.nnnorm_id, inv_one]
      exact hℓ
  refine ⟨hA.toHomeomorph _ hc, rfl, ?_, fun w => ?_⟩
  · refine AntilipschitzWith.of_le_mul_dist fun a b => ?_
    change dist a b ≤ ((1 - ℓ)⁻¹ : ℝ≥0) * dist (a + H a) (b + H b)
    have h1 : dist (H a) (H b) ≤ ℓ * dist a b := hH.dist_le_mul a b
    have h2 : dist a b ≤ dist (a + H a) (b + H b) + dist (H a) (H b) := by
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
      calc ‖a - b‖ = ‖(a + H a - (b + H b)) - (H a - H b)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have hℓ' : (ℓ : ℝ) < 1 := by exact_mod_cast hℓ
    have hpos : (0 : ℝ) < 1 - ℓ := by linarith
    rw [NNReal.coe_inv, NNReal.coe_sub hℓ.le, NNReal.coe_one, ← div_eq_inv_mul, le_div_iff₀ hpos]
    linarith
  · change ⟪w + H w, ν⟫ = ⟪w, ν⟫
    rw [inner_add_left, hHν, add_zero]

end GMTFoundations
