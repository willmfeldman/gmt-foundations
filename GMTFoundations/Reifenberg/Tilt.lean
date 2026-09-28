/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.BestPlane
public import GMTFoundations.Reifenberg.Hyperplane
public import GMTFoundations.GMT.Packing
import Mathlib.Data.Real.Hom
import Mathlib.Data.Real.StarOrdered

/-!
# Far points and the tilt between planes

Hyperplane case (`k = n − 1`) of Lemmas 3.2 and 3.3 of M. Miśkiewicz, *Discrete Reifenberg-type
theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018); arXiv:1612.02461 (Miś), which are the
counterparts of Lemmas 4.7 and 4.8 of A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the
regularity of stationary and minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227 (NV).
Miś gives only a sketch of Lemma 3.3; the proof here is complete and self-contained.

## Main definitions

* `farConst n = 529 · 2ⁿ · 3^{n−2} / ω_n`, the tube-packing constant `A_n`: in the proof of
  `exists_far_point`, the part of `B_r(x)` within `11s` of a codimension-two flat is covered by at
  most `A_n (r/s)^{n−2}` balls of radius `s = ρr`.

## Main statements

* `exists_far_point` (Miś Lemma 3.2): if `μ(B_r(x)) ≥ a r^{n−1}`, every ball `B_{ρr}(y)`
  with `y ∈ B_r(x)` has `μ`-mass `≤ b (ρr)^{n−1}`, and `ρ ≤ a / (2 A_n b)`, then for every affine
  subspace `W` of dimension `≤ n − 2` there is `y ∈ B_r(x)` at distance `> 10ρr` from `W` with
  `μ(B_{ρr}(y)) ≥ (a/2)(ρ/3)ⁿ r^{n−1}`.
* `planeDist_sq_le_of_mass` (core tilt lemma): under the same hypotheses and
  `μ(B_r(x)) < ∞`, for any two planes with unit normals,
  `planeDist x r P Q ² ≤ 48 · 3ⁿ ρ^{−(n+2)} (E_P + E_Q) / (a r^{n+1})`, with
  `E_P = ∫_{B_{(1+ρ)r}(x)} f_P² dμ`.
* `planeDist_bestPlane_sq_le_of_subset` (C1): the same for two best planes on balls containing
  `B_{(1+ρ)r}(x)`, in terms of their β-numbers.
* `dist_bestPlane_le` (C2, Miś Lemma 3.3 with `q = 2`, at a general centre and scale).

The constants depend on `n` and `ρ` only (and on `a`, `τ`, `M`, `κ` through the displayed
formulas); no constant depends on the measure.

## Comparison with the sources

* The core lemma is stated for an arbitrary ball `B_r(x)` and an arbitrary pair of planes, with
  the lower and upper mass constants `a`, `b` kept separate. This is what the discrete Reifenberg
  induction needs: in the proof of Miś Proposition 4.3, Lemma 3.3 is applied after rescaling
  `B_{2r_i}(z)` to `B₁`, so the radius ratio is `ρ/2` rather than `ρ` and the resulting plane is
  `V(y′, 2κr_{i+1})`; a second application at ratio `1/2` cannot bridge it to `V(y′, κr_{i+1})`.
  Comparing `V(z, 2κr_i)` and `V(y′, κr_{i+1})` directly by (C1) avoids this, at the cost of
  constants depending on `n` and `ρ` only.
* The proof does not follow the general-`k` route of NV Lemma 4.8 (`k + 1` effectively spanning
  far points, NV Lemma 4.6, and NV Lemma 4.2 for the reverse inclusion). For hyperplanes one far
  point, far from a codimension-two flat, suffices, and `planeDist` is symmetric.
* Miś Lemma 3.2 states the mass lower bound as `C(n, ρ)`; it also depends on the lower mass
  constant (here `(a/2)(ρ/3)ⁿ`).
* Miś Lemma 3.3 assumes `μ(B₁) ≥ τM` and `d(x, V) ≤ ρ/2`. The first is inherited from NV
  Lemma 4.8, where it keeps the measure above NV's cutoff `ε_n`; the second is needed only for the
  Hausdorff-distance form. Neither is needed for `planeDist`, so (C2) is at least as strong as
  Miś Lemma 3.3 for `q = 2`, `k = n − 1`.

## References

* [Miś] M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43
  (2018); arXiv:1612.02461, Lemmas 3.2, 3.3.
* [NV] A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and
  minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227, Lemmas 4.7, 4.8.
-/

public noncomputable section

namespace GMTFoundations

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

/-- `N_T · b s^{n−1} = A_n b ρ r^{n−1}` for `s = ρ r`, where
`N_T = (23 s)² (3 r)^{n−2} / (ω_n (s/2)ⁿ)` bounds the number of `s`-separated points in the tube. -/
private lemma tube_count_mul_eq (hn : 2 ≤ n) {ρ r b : ℝ} (hρ : 0 < ρ) (hr : 0 < r) :
    (23 * (ρ * r)) ^ 2 * (3 * r) ^ (n - 2) / (unitBallVolume n * (ρ * r / 2) ^ n) *
        (b * (ρ * r) ^ (n - 1)) = farConst n * b * ρ * r ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hω := unitBallVolume_pos (m + 2)
  simp only [farConst, Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega, div_pow]
  field_simp
  ring

/-- **Far point** (Miś Lemma 3.2, hyperplane case). Let `r > 0`, `0 < ρ ≤ 1`,
`a, b > 0` and `ρ ≤ a / (2 A_n b)`. Assume `μ(B_r(x)) ≥ a r^{n−1}` and `μ(B_{ρr}(y)) ≤ b (ρr)^{n−1}`
for every `y ∈ B_r(x)`. Then for every affine subspace `W` with `dim W ≤ n − 2` there is
`y ∈ B_r(x)` with `dist(y, w) > 10 ρ r` for all `w ∈ W` and `μ(B_{ρr}(y)) ≥ (a/2)(ρ/3)ⁿ r^{n−1}`.
No measurability or finiteness of `μ` is needed. -/
theorem exists_far_point (hn : 2 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r ρ a b : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hρ0 : ρ ≤ a / (2 * farConst n * b))
    (hlow : ENNReal.ofReal (a * r ^ (n - 1)) ≤ μ (ball x r))
    (hup : ∀ y ∈ ball x r, μ (ball y (ρ * r)) ≤ ENNReal.ofReal (b * (ρ * r) ^ (n - 1)))
    (W : AffineSubspace ℝ (Rn n)) (hW : Module.finrank ℝ W.direction ≤ n - 2) :
    ∃ y ∈ ball x r, (∀ w ∈ W, 10 * (ρ * r) < dist y w) ∧
      ENNReal.ofReal (a / 2 * (ρ / 3) ^ n * r ^ (n - 1)) ≤ μ (ball y (ρ * r)) := by
  classical
  have hs : 0 < ρ * r := mul_pos hρ hr
  have hω := unitBallVolume_pos n
  have hA := farConst_pos n
  have hrn : 0 < r ^ (n - 1) := pow_pos hr _
  set U : Set (Rn n) := thickening (11 * (ρ * r)) (W : Set (Rn n)) with hU
  -- Steps 1–3: the tube `T = B_r(x) ∩ U` has mass `≤ (a/2) r^{n−1}`.
  have hT : μ (ball x r ∩ U) ≤ ENNReal.ofReal (a / 2 * r ^ (n - 1)) := by
    set N : ℝ := (23 * (ρ * r)) ^ 2 * (3 * r) ^ (n - 2) / (unitBallVolume n * (ρ * r / 2) ^ n)
    have hN : ∀ F : Finset (Rn n), ↑F ⊆ ball x r ∩ U →
        (F : Set (Rn n)).Pairwise (fun y z => ρ * r ≤ dist y z) → (F.card : ℝ) ≤ N := by
      intro F hFT hF
      have h := NaberValtorta.card_mul_le_of_subset_thickening hn hW hs hr.le
        (by positivity : (0 : ℝ) ≤ 11 * (ρ * r))
        (hFT.trans (inter_subset_left.trans ball_subset_closedBall)) (hFT.trans inter_subset_right)
        hF
      rw [le_div_iff₀ (by positivity)]
      refine h.trans ?_
      have h1 : 2 * (11 * (ρ * r)) + ρ * r = 23 * (ρ * r) := by ring
      have h2 : 2 * r + ρ * r ≤ 3 * r := by
        linarith only [mul_le_mul_of_nonneg_right hρ1 hr.le]
      rw [h1]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith only [hr, hs]) h2 _) (sq_nonneg _)
    obtain ⟨F, hFT, hFN, hcov⟩ := GMT.exists_finset_subset_cover hs hN
    calc μ (ball x r ∩ U) ≤ μ (⋃ c ∈ F, ball c (ρ * r)) := measure_mono hcov
      _ ≤ ∑ c ∈ F, μ (ball c (ρ * r)) := measure_biUnion_finset_le F _
      _ ≤ ∑ _c ∈ F, ENNReal.ofReal (b * (ρ * r) ^ (n - 1)) :=
          Finset.sum_le_sum fun c hc => hup c (hFT hc).1
      _ = ENNReal.ofReal (F.card * (b * (ρ * r) ^ (n - 1))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (a / 2 * r ^ (n - 1)) := by
          apply ENNReal.ofReal_le_ofReal
          have hρ0' : ρ * (2 * farConst n * b) ≤ a := by
            rwa [le_div_iff₀ (by positivity)] at hρ0
          calc (F.card : ℝ) * (b * (ρ * r) ^ (n - 1)) ≤ N * (b * (ρ * r) ^ (n - 1)) :=
                mul_le_mul_of_nonneg_right hFN (by positivity)
            _ = farConst n * b * ρ * r ^ (n - 1) := tube_count_mul_eq hn hρ hr
            _ ≤ a / 2 * r ^ (n - 1) :=
                mul_le_mul_of_nonneg_right (by linarith only [hρ0']) hrn.le
  -- Step 4: the complement `O = B_r(x) \ U` has mass `≥ (a/2) r^{n−1}`.
  have hO : ENNReal.ofReal (a / 2 * r ^ (n - 1)) ≤ μ (ball x r \ U) := by
    have h1 := measure_le_inter_add_diff μ (ball x r) U
    have h2 : ENNReal.ofReal (a * r ^ (n - 1)) =
        ENNReal.ofReal (a / 2 * r ^ (n - 1)) + ENNReal.ofReal (a / 2 * r ^ (n - 1)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have h3 := hlow.trans (h1.trans (add_le_add_left hT _))
    rw [h2] at h3
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 h3
  -- Step 5: cover `O` by at most `(3/ρ)ⁿ` balls of radius `ρ r` centred in `O`.
  have hN' : ∀ F : Finset (Rn n), ↑F ⊆ ball x r \ U →
      (F : Set (Rn n)).Pairwise (fun y z => ρ * r ≤ dist y z) → (F.card : ℝ) ≤ (3 / ρ) ^ n := by
    intro F hFO hF
    refine (NaberValtorta.card_le_of_pairwise_le_dist hs hr.le
      (hFO.trans (diff_subset.trans ball_subset_closedBall)) hF).trans ?_
    have e : 2 * r / (ρ * r) = 2 / ρ := by field_simp
    have h1 : 1 ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
    have h3 : 3 / ρ = 2 / ρ + 1 / ρ := by ring
    rw [e]
    exact pow_le_pow_left₀ (by positivity) (by linarith) n
  obtain ⟨F, hFO, hFN, hcov⟩ := GMT.exists_finset_subset_cover hs hN'
  -- Step 7 (used below): every point of `O` is at distance `≥ 11 ρ r` from `W`.
  have hfar : ∀ y ∈ ball x r \ U, ∀ w ∈ W, 10 * (ρ * r) < dist y w := by
    intro y hy w hw
    by_contra hc
    push Not at hc
    exact hy.2 (mem_thickening_iff.2 ⟨w, hw, by linarith⟩)
  -- Step 6: pigeonhole.
  by_contra hcon
  push Not at hcon
  have hlt : ∀ z ∈ F, μ (ball z (ρ * r)) < ENNReal.ofReal (a / 2 * (ρ / 3) ^ n * r ^ (n - 1)) :=
    fun z hz => hcon z (hFO hz).1 (hfar z (hFO hz))
  have hpos : 0 < ENNReal.ofReal (a / 2 * r ^ (n - 1)) := ENNReal.ofReal_pos.2 (by positivity)
  rcases F.eq_empty_or_nonempty with hF0 | hFne
  · have : μ (ball x r \ U) = 0 := by
      refine measure_mono_null hcov ?_
      simp [hF0]
    rw [this] at hO
    exact absurd (hpos.trans_le hO) (lt_irrefl 0)
  have hsum := ENNReal.sum_lt_sum_of_nonempty hFne hlt
  rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hsum
  have hle : ENNReal.ofReal ((F.card : ℝ) * (a / 2 * (ρ / 3) ^ n * r ^ (n - 1))) ≤
      ENNReal.ofReal (a / 2 * r ^ (n - 1)) := by
    apply ENNReal.ofReal_le_ofReal
    calc (F.card : ℝ) * (a / 2 * (ρ / 3) ^ n * r ^ (n - 1))
        ≤ (3 / ρ) ^ n * (a / 2 * (ρ / 3) ^ n * r ^ (n - 1)) :=
          mul_le_mul_of_nonneg_right hFN (by positivity)
      _ = ((3 / ρ) * (ρ / 3)) ^ n * (a / 2 * r ^ (n - 1)) := by rw [mul_pow]; ring
      _ = a / 2 * r ^ (n - 1) := by
          rw [show 3 / ρ * (ρ / 3) = 1 by field_simp, one_pow, one_mul]
  have := (hO.trans (measure_mono hcov)).trans (measure_biUnion_finset_le F _)
  exact absurd ((this.trans_lt hsum).trans_le hle) (lt_irrefl _)

/-! ### The tilt lemma -/

/-- Two orthonormal vectors span a subspace whose orthogonal complement has dimension `n − 2`. -/
private lemma finrank_orthogonal_span_pair {e₁ e₂ : Rn n} (h : Orthonormal ℝ ![e₁, e₂]) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range ![e₁, e₂]))ᗮ ≤ n - 2 := by
  have hK : Module.finrank ℝ (Submodule.span ℝ (Set.range ![e₁, e₂])) = 2 := by
    rw [finrank_span_eq_card h.linearIndependent, Fintype.card_fin]
  have := (Submodule.span ℝ (Set.range ![e₁, e₂])).finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin, hK] at this
  omega

/-- A vector orthogonal to `e₁` and `e₂` lies in `(span {e₁, e₂})ᗮ`. -/
private lemma mem_orthogonal_span_pair {e₁ e₂ w : Rn n} (h₁ : ⟪e₁, w⟫ = 0) (h₂ : ⟪e₂, w⟫ = 0) :
    w ∈ (Submodule.span ℝ (Set.range ![e₁, e₂]))ᗮ := by
  have hle : Submodule.span ℝ (Set.range ![e₁, e₂]) ≤ (ℝ ∙ w)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    fin_cases i
    · exact h₁
    · exact h₂
  rw [Submodule.mem_orthogonal]
  intro k hk
  have := hle hk
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm] at this
  exact this

/-- `|f_P(y) − σ f_Q(y)| ≤ 2η` when `|f_P(y)|, |f_Q(y)| ≤ η` and `σ = ±1`. -/
private lemma abs_sub_sign_mul_le {A B σ η : ℝ} (hσ : σ = 1 ∨ σ = -1) (hA : |A| ≤ η)
    (hB : |B| ≤ η) : |A - σ * B| ≤ 2 * η := by
  have : |σ * B| = |B| := by rcases hσ with rfl | rfl <;> simp
  calc |A - σ * B| ≤ |A| + |σ * B| := abs_sub _ _
    _ ≤ 2 * η := by rw [this]; linarith

/-- **Geometric core of the tilt lemma** (steps 0 and 2–5 of the tilt estimate). Let `P, Q`
have unit normals, `0 < s ≤ r`, `η ≥ 0`, `‖x − p₀‖ ≤ r`, and `|f_P(p₀)|, |f_Q(p₀)| ≤ η`. Assume
that for every affine subspace `W` of dimension `≤ n − 2` there is a point `p₁` with
`|f_P(p₁)|, |f_Q(p₁)| ≤ η` and `dist(p₁, w) > 9s` for all `w ∈ W`. Then
`planeDist x r P Q ² ≤ 24 η² / s²`. -/
private lemma planeDist_sq_le_of_points {P Q : Rn n × Rn n} (hP : ‖P.2‖ = 1) (hQ : ‖Q.2‖ = 1)
    {x p₀ : Rn n} {r s η : ℝ} (hs : 0 < s) (hsr : s ≤ r) (hη : 0 ≤ η) (hx : ‖x - p₀‖ ≤ r)
    (hP₀ : |⟪p₀ - P.1, P.2⟫| ≤ η) (hQ₀ : |⟪p₀ - Q.1, Q.2⟫| ≤ η)
    (hfar : ∀ W : AffineSubspace ℝ (Rn n), Module.finrank ℝ W.direction ≤ n - 2 →
      ∃ p₁ : Rn n, |⟪p₁ - P.1, P.2⟫| ≤ η ∧ |⟪p₁ - Q.1, Q.2⟫| ≤ η ∧ ∀ w ∈ W, 9 * s < dist p₁ w) :
    planeDist x r P Q ^ 2 ≤ 24 * η ^ 2 / s ^ 2 := by
  have hr : 0 < r := hs.trans_le hsr
  -- Step 0: the sign `σ` with `σ ⟪ν₁, ν₂⟫ ≥ 0`, and `v = ν₁ − σ ν₂`.
  obtain ⟨σ, hσ, hσpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 ≤ σ * ⟪P.2, Q.2⟫ := by
    rcases le_total 0 ⟪P.2, Q.2⟫ with h | h
    · exact ⟨1, Or.inl rfl, by linarith⟩
    · exact ⟨-1, Or.inr rfl, by linarith⟩
  have habsσ : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  set v : Rn n := P.2 - σ • Q.2 with hv_def
  have hν₂' : ‖σ • Q.2‖ = 1 := by rw [norm_smul, Real.norm_eq_abs, habsσ, hQ, one_mul]
  have hc : 0 ≤ ⟪P.2, σ • Q.2⟫ := by rw [real_inner_smul_right]; exact hσpos
  have hv2 : ‖v‖ ^ 2 = 2 - 2 * ⟪P.2, σ • Q.2⟫ := by
    rw [hv_def, norm_sub_sq_real, hP, hν₂']
    ring
  have hvle : ‖v‖ ^ 2 ≤ 2 := by linarith only [hv2, hc]
  have hvν : ⟪v, P.2⟫ = ‖v‖ ^ 2 / 2 := by
    rw [hv_def, inner_sub_left, real_inner_self_eq_norm_sq, hP, real_inner_comm, hv2]
    ring
  have hvν0 : 0 ≤ ⟪v, P.2⟫ := by rw [hvν]; positivity
  have hvν1 : ⟪v, P.2⟫ ≤ 1 := by rw [hvν]; linarith only [hvle]
  -- `h = f_P − σ f_Q` is affine with linear part `⟪·, v⟫`.
  set H : Rn n → ℝ := fun y => ⟪y - P.1, P.2⟫ - σ * ⟪y - Q.1, Q.2⟫ with hH_def
  have hH : ∀ y y', H y - H y' = ⟪y - y', v⟫ := fun y y' => inner_sub_sign_sub P Q σ y' y
  have hHp₀ : |H p₀| ≤ 2 * η := abs_sub_sign_mul_le hσ hP₀ hQ₀
  -- Step 4: `‖v‖² ≤ 2 η² / s²`.
  have hclaim : ‖v‖ ^ 2 * s ^ 2 ≤ 2 * η ^ 2 := by
    rcases le_or_gt s η with hsη | hsη
    · have : s ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hs.le hsη 2
      exact mul_le_mul hvle this (sq_nonneg _) zero_le_two
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0, norm_zero]
      have := sq_nonneg η
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      linarith only [this]
    -- Step 3: the unit vector `u` in the tilt direction.
    set vT : Rn n := v - ⟪v, P.2⟫ • P.2 with hvT_def
    have hvT2 : ‖vT‖ ^ 2 = ‖v‖ ^ 2 - ⟪v, P.2⟫ ^ 2 := by
      rw [hvT_def, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hP,
        mul_one, sq_abs]
      ring
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hvT_ge : ‖v‖ ^ 2 / 2 ≤ ‖vT‖ ^ 2 := by
      rw [hvT2, hvν]
      linarith only [mul_le_mul_of_nonneg_left hvle (sq_nonneg ‖v‖)]
    have hvTpos : 0 < ‖vT‖ := by
      refine norm_pos_iff.2 fun h => ?_
      rw [h, norm_zero] at hvT_ge
      have : 0 < ‖v‖ ^ 2 / 2 := by positivity
      linarith only [this, hvT_ge]
    set u : Rn n := ‖vT‖⁻¹ • vT with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hvTpos.ne']
    have hvTν : ⟪vT, P.2⟫ = 0 := by
      rw [hvT_def, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hP]
      ring
    have huν : ⟪u, P.2⟫ = 0 := by rw [hu_def, real_inner_smul_left, hvTν, mul_zero]
    have hvT_eq : vT = ‖vT‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hvTpos.ne', one_smul]
    -- (★) `⟪w, v⟫ = ⟪v, ν₁⟫ ⟪w, ν₁⟫ + ‖v_T‖ ⟪w, u⟫`.
    have hstar : ∀ w : Rn n, ⟪w, v⟫ = ⟪v, P.2⟫ * ⟪w, P.2⟫ + ‖vT‖ * ⟪w, u⟫ := by
      intro w
      have hv' : v = ⟪v, P.2⟫ • P.2 + ‖vT‖ • u := by rw [← hvT_eq, hvT_def]; abel
      conv_lhs => rw [hv']
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    -- The codimension-two flat `W = p₀ + {ν₁, u}ᗮ`.
    have hon : Orthonormal ℝ ![P.2, u] := by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [hP, hu, huν, real_inner_comm u P.2]
    set K : Submodule ℝ (Rn n) := Submodule.span ℝ (Set.range ![P.2, u])
    set W : AffineSubspace ℝ (Rn n) := AffineSubspace.mk' p₀ Kᗮ
    have hWdim : Module.finrank ℝ W.direction ≤ n - 2 := by
      rw [AffineSubspace.direction_mk']
      exact finrank_orthogonal_span_pair hon
    obtain ⟨p₁, hP₁, hQ₁, hfar₁⟩ := hfar W hWdim
    set d : Rn n := p₁ - p₀ with hd_def
    set α : ℝ := ⟪d, P.2⟫ with hα_def
    set β : ℝ := ⟪d, u⟫ with hβ_def
    have hwst : p₁ - α • P.2 - β • u ∈ W := by
      rw [AffineSubspace.mem_mk', vsub_eq_sub]
      have he : p₁ - α • P.2 - β • u - p₀ = d - α • P.2 - β • u := by rw [hd_def]; abel
      rw [he]
      refine mem_orthogonal_span_pair ?_ ?_
      · rw [inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq, hP, real_inner_comm u P.2, huν, real_inner_comm, ← hα_def]
        ring
      · rw [inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq, hu, huν, real_inner_comm, ← hβ_def]
        ring
    have hdist : dist p₁ (p₁ - α • P.2 - β • u) ^ 2 = α ^ 2 + β ^ 2 := by
      rw [dist_eq_norm, show p₁ - (p₁ - α • P.2 - β • u) = α • P.2 + β • u by abel,
        norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm u P.2, huν, hP, hu, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one,
        sq_abs, sq_abs]
      ring
    have h9 := hfar₁ _ hwst
    have h81 : 81 * s ^ 2 < α ^ 2 + β ^ 2 := by
      rw [← hdist]
      linarith only [pow_lt_pow_left₀ h9 (by linarith only [hs]) two_ne_zero]
    have hα : |α| ≤ 2 * η := by
      have : α = ⟪p₁ - P.1, P.2⟫ - ⟪p₀ - P.1, P.2⟫ := by
        rw [hα_def, hd_def, ← inner_sub_left, sub_sub_sub_cancel_right]
      rw [this]
      exact (abs_sub _ _).trans ((add_le_add hP₁ hP₀).trans_eq (two_mul η).symm)
    have hα2 : α ^ 2 < 4 * s ^ 2 := by
      have : |α| < 2 * s := by linarith only [hα, hsη]
      calc α ^ 2 = |α| ^ 2 := (sq_abs α).symm
        _ < (2 * s) ^ 2 := pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
        _ = 4 * s ^ 2 := by ring
    have hβ2 : 77 * s ^ 2 < β ^ 2 := by linarith only [h81, hα2]
    -- Steps 4.4–4.5: `‖v_T‖ β = (h(p₁) − h(p₀)) − ⟪v, ν₁⟫ α`, so `|‖v_T‖ β| ≤ 6 η`.
    have hγ : ‖vT‖ * β = (H p₁ - H p₀) - ⟪v, P.2⟫ * α := by
      have e1 : H p₁ - H p₀ = ⟪d, v⟫ := hH p₁ p₀
      have e2 : ⟪d, v⟫ = ⟪v, P.2⟫ * α + ‖vT‖ * β := hstar d
      linarith only [e1, e2]
    have hHp₁ : |H p₁| ≤ 2 * η := abs_sub_sign_mul_le hσ hP₁ hQ₁
    have hγabs : |‖vT‖ * β| ≤ 6 * η := by
      rw [hγ]
      have h1 : |H p₁ - H p₀| ≤ 4 * η := (abs_sub _ _).trans (by linarith only [hHp₁, hHp₀])
      have h2 : |⟪v, P.2⟫ * α| ≤ 2 * η := by
        rw [abs_mul, abs_of_nonneg hvν0]
        calc ⟪v, P.2⟫ * |α| ≤ 1 * (2 * η) := mul_le_mul hvν1 hα (abs_nonneg _) zero_le_one
          _ = 2 * η := one_mul _
      exact (abs_sub _ _).trans (by linarith only [h1, h2])
    have hsq : ‖vT‖ ^ 2 * β ^ 2 ≤ 36 * η ^ 2 := by
      rw [← mul_pow]
      have := pow_le_pow_left₀ (abs_nonneg _) hγabs 2
      rw [sq_abs] at this
      linarith only [this]
    have hprod : ‖v‖ ^ 2 / 2 * (77 * s ^ 2) ≤ ‖vT‖ ^ 2 * β ^ 2 :=
      mul_le_mul hvT_ge hβ2.le (by positivity) (by positivity)
    linarith only [hprod, hsq, sq_nonneg η]
  -- Step 5: the offset, and the conclusion.
  have hD : planeDist x r P Q ≤ ‖v‖ + |H x| / r := planeDist_le_planeDistSign hσ
  have hHx : |H x| ≤ 2 * η + r * ‖v‖ := by
    have e : H x = H p₀ + ⟪x - p₀, v⟫ := by rw [← hH]; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add hHp₀ ?_)
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hD2 : planeDist x r P Q ≤ 2 * ‖v‖ + 2 * (η / s) := by
    have h1 : |H x| / r ≤ 2 * (η / r) + ‖v‖ := by
      calc |H x| / r ≤ (2 * η + r * ‖v‖) / r := div_le_div_of_nonneg_right hHx hr.le
        _ = 2 * (η / r) + ‖v‖ := by rw [add_div, mul_div_cancel_left₀ _ hr.ne']; ring
    have h2 : η / r ≤ η / s := div_le_div_of_nonneg_left hη hs hsr
    linarith only [hD, h1, h2]
  have hD0 : 0 ≤ planeDist x r P Q := planeDist_nonneg hr.le
  have hvs : ‖v‖ ^ 2 ≤ 2 * (η / s) ^ 2 := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
    exact hclaim
  have e24 : 24 * η ^ 2 / s ^ 2 = 24 * (η / s) ^ 2 := by rw [div_pow]; ring
  rw [e24]
  have h1 := pow_le_pow_left₀ hD0 hD2 2
  have h2 : (2 * ‖v‖ + 2 * (η / s)) ^ 2 =
      8 * ‖v‖ ^ 2 + 8 * (η / s) ^ 2 - 4 * (‖v‖ - η / s) ^ 2 := by ring
  linarith only [h1, h2, hvs, sq_nonneg (‖v‖ - η / s)]

/-- Jensen at the center of mass of a ball `B_t(c) ⊆ B'` of mass `≥ m > 0`: if
`∫_{B'} ⟪y − p, ν⟫² dμ ≤ E < ∞`, then `|⟪m_B − p, ν⟫| ≤ √(E / m)`. -/
private lemma abs_inner_centerOfMass_le {μ : Measure (Rn n)} {c : Rn n} {t m : ℝ}
    {B' : Set (Rn n)} (hm : 0 < m) (hsub : ball c t ⊆ B')
    (hlow : ENNReal.ofReal m ≤ μ (ball c t)) (hfin : μ (ball c t) ≠ ∞) {p ν : Rn n}
    {E : ℝ≥0∞} (hE : E ≠ ∞) (hI : ∫⁻ y in B', ENNReal.ofReal (⟪y - p, ν⟫ ^ 2) ∂μ ≤ E) :
    |⟪centerOfMass μ (ball c t) - p, ν⟫| ≤ Real.sqrt (E.toReal / m) := by
  have h0 : μ (ball c t) ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hm) hlow).ne'
  have hJ := sq_inner_centerOfMass_le measurableSet_ball ball_subset_closedBall hfin h0 p ν
  have h1 : ENNReal.ofReal (⟪centerOfMass μ (ball c t) - p, ν⟫ ^ 2 * m) ≤ E := by
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    have h2 : ENNReal.ofReal (⟪centerOfMass μ (ball c t) - p, ν⟫ ^ 2) * ENNReal.ofReal m ≤
        ENNReal.ofReal (⟪centerOfMass μ (ball c t) - p, ν⟫ ^ 2) * μ (ball c t) := by gcongr
    exact (h2.trans hJ).trans ((lintegral_mono_set hsub).trans hI)
  rw [ENNReal.ofReal_le_iff_le_toReal hE] at h1
  exact Real.abs_le_sqrt ((le_div_iff₀ hm).2 h1)

/-- `24 / (c_far r^{n−1} (ρr)²) = 48 · 3ⁿ / (ρ^{n+2} a r^{n+1})` with `c_far = (a/2)(ρ/3)ⁿ`. -/
private lemma tilt_const_eq (hn : 1 ≤ n) {a ρ r : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hr : 0 < r) :
    24 / (a / 2 * (ρ / 3) ^ n * r ^ (n - 1) * (ρ * r) ^ 2) =
      48 * 3 ^ n / (ρ ^ (n + 2) * a * r ^ (n + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, div_pow]
  field_simp
  ring

/-- **Core tilt lemma** (hyperplane form of Miś Lemma 3.3 / NV Lemma 4.8,
`q = 2`). Let `n ≥ 2`, `r > 0`, `0 < ρ ≤ 1`, `a, b > 0` with `ρ ≤ a / (2 A_n b)`, and assume
* (H0) `μ(B_r(x)) < ∞`;
* (H1) `μ(B_r(x)) ≥ a r^{n−1}`;
* (H2) `μ(B_{ρr}(y)) ≤ b (ρr)^{n−1}` for every `y ∈ B_r(x)`.

Then for any planes `P, Q` with unit normals,
`planeDist x r P Q ² ≤ C_core(n, ρ) (E_P + E_Q) / (a r^{n+1})`, with
`C_core(n, ρ) = 48 · 3ⁿ ρ^{−(n+2)}` and `E_P = ∫_{B_{(1+ρ)r}(x)} ⟪y − p_P, ν_P⟫² dμ`.
The constant depends on `n` and `ρ` only (and on `a` as displayed); `b` enters only through the
smallness condition on `ρ`. -/
theorem planeDist_sq_le_of_mass (hn : 2 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r ρ a b : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hρ0 : ρ ≤ a / (2 * farConst n * b)) (hfin : μ (ball x r) ≠ ∞)
    (hlow : ENNReal.ofReal (a * r ^ (n - 1)) ≤ μ (ball x r))
    (hup : ∀ y ∈ ball x r, μ (ball y (ρ * r)) ≤ ENNReal.ofReal (b * (ρ * r) ^ (n - 1)))
    {P Q : Rn n × Rn n} (hP : ‖P.2‖ = 1) (hQ : ‖Q.2‖ = 1) :
    ENNReal.ofReal (planeDist x r P Q ^ 2) ≤
      ENNReal.ofReal (48 * 3 ^ n / (ρ ^ (n + 2) * a * r ^ (n + 1))) *
        ((∫⁻ y in ball x ((1 + ρ) * r), ENNReal.ofReal (⟪y - P.1, P.2⟫ ^ 2) ∂μ) +
          ∫⁻ y in ball x ((1 + ρ) * r), ENNReal.ofReal (⟪y - Q.1, Q.2⟫ ^ 2) ∂μ) := by
  set IP := ∫⁻ y in ball x ((1 + ρ) * r), ENNReal.ofReal (⟪y - P.1, P.2⟫ ^ 2) ∂μ
  set IQ := ∫⁻ y in ball x ((1 + ρ) * r), ENNReal.ofReal (⟪y - Q.1, Q.2⟫ ^ 2) ∂μ
  set C := 48 * 3 ^ n / (ρ ^ (n + 2) * a * r ^ (n + 1)) with hC_def
  have hC : 0 < C := by positivity
  rcases eq_or_ne (IP + IQ) ∞ with hE | hE
  · rw [hE, ENNReal.mul_top (ENNReal.ofReal_pos.2 hC).ne']
    exact le_top
  have hs : 0 < ρ * r := mul_pos hρ hr
  have hsr : ρ * r ≤ r := by linarith [mul_le_mul_of_nonneg_right hρ1 hr.le]
  set m := a / 2 * (ρ / 3) ^ n * r ^ (n - 1) with hm_def
  have hm : 0 < m := by positivity
  have hma : m ≤ a * r ^ (n - 1) := by
    have : (ρ / 3) ^ n ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    have hrn : 0 < r ^ (n - 1) := pow_pos hr _
    rw [hm_def]
    apply mul_le_mul_of_nonneg_right _ hrn.le
    linarith only [ha, mul_le_mul_of_nonneg_left this (by linarith only [ha] : 0 ≤ a / 2)]
  set η := Real.sqrt ((IP + IQ).toReal / m) with hη_def
  have hIP : IP ≤ IP + IQ := le_add_right le_rfl
  have hIQ : IQ ≤ IP + IQ := le_add_left le_rfl
  -- Step 1: the base point `p₀`, center of mass of `μ⌊B_r(x)`.
  have hsub₀ : ball x r ⊆ ball x ((1 + ρ) * r) := ball_subset_ball (by linarith)
  have hlow₀ : ENNReal.ofReal m ≤ μ (ball x r) := (ENNReal.ofReal_le_ofReal hma).trans hlow
  set p₀ := centerOfMass μ (ball x r)
  have hx : ‖x - p₀‖ ≤ r := by
    rw [norm_sub_rev]
    exact norm_centerOfMass_sub_le measurableSet_ball ball_subset_closedBall hfin
      (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hm) hlow₀).ne'
  have hP₀ := abs_inner_centerOfMass_le hm hsub₀ hlow₀ hfin hE hIP (p := P.1) (ν := P.2)
  have hQ₀ := abs_inner_centerOfMass_le hm hsub₀ hlow₀ hfin hE hIQ (p := Q.1) (ν := Q.2)
  -- Step 3: far points (`exists_far_point`) and their centers of mass.
  have hfar : ∀ W : AffineSubspace ℝ (Rn n), Module.finrank ℝ W.direction ≤ n - 2 →
      ∃ p₁ : Rn n, |⟪p₁ - P.1, P.2⟫| ≤ η ∧ |⟪p₁ - Q.1, Q.2⟫| ≤ η ∧
        ∀ w ∈ W, 9 * (ρ * r) < dist p₁ w := by
    intro W hW
    obtain ⟨y₁, hy₁, hfar₁, hmass₁⟩ :=
      exists_far_point hn hr hρ hρ1 ha hb hρ0 hlow hup W hW
    have hfin₁ : μ (ball y₁ (ρ * r)) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup y₁ hy₁)
    have hsub₁ : ball y₁ (ρ * r) ⊆ ball x ((1 + ρ) * r) := by
      refine ball_subset_ball' ?_
      have := mem_ball.1 hy₁
      linarith only [this]
    have hp₁ := norm_centerOfMass_sub_le (μ := μ) measurableSet_ball
      (ball_subset_closedBall (x := y₁) (ε := ρ * r)) hfin₁
      (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hm) hmass₁).ne'
    refine ⟨centerOfMass μ (ball y₁ (ρ * r)),
      abs_inner_centerOfMass_le hm hsub₁ hmass₁ hfin₁ hE hIP,
      abs_inner_centerOfMass_le hm hsub₁ hmass₁ hfin₁ hE hIQ, fun w hw => ?_⟩
    have h10 := hfar₁ w hw
    have htri := dist_triangle y₁ (centerOfMass μ (ball y₁ (ρ * r))) w
    have hd : dist y₁ (centerOfMass μ (ball y₁ (ρ * r))) ≤ ρ * r := by
      rw [dist_comm, dist_eq_norm]
      exact hp₁
    linarith
  -- Steps 4–6.
  have hgeom := planeDist_sq_le_of_points hP hQ hs hsr (Real.sqrt_nonneg _) hx hP₀ hQ₀ hfar
  have hη2 : η ^ 2 = (IP + IQ).toReal / m := Real.sq_sqrt (by positivity)
  have hfinal : planeDist x r P Q ^ 2 ≤ C * (IP + IQ).toReal := by
    refine hgeom.trans (le_of_eq ?_)
    rw [hη2, hC_def, ← tilt_const_eq (by omega) ha hρ hr, ← hm_def]
    field_simp
  calc ENNReal.ofReal (planeDist x r P Q ^ 2) ≤ ENNReal.ofReal (C * (IP + IQ).toReal) :=
        ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal C * (IP + IQ) := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hE]

/-- **(C1) Two best planes on nested balls**. Under the hypotheses of
`planeDist_sq_le_of_mass`, if `B_{(1+ρ)r}(x) ⊆ B_{R₁}(z₁) ∩ B_{R₂}(z₂)` with `R_i > 0` and
`μ(B_{R_i}(z_i)) < ∞`, then
`planeDist x r V(z₁,R₁) V(z₂,R₂) ² ≤
  C_core(n,ρ) (R₁^{n+1} β²(z₁,R₁) + R₂^{n+1} β²(z₂,R₂)) / (a r^{n+1})`,
where `V(z, R) = bestPlane μ z R`. -/
theorem planeDist_bestPlane_sq_le_of_subset (hn : 2 ≤ n) {μ : Measure (Rn n)} {x : Rn n}
    {r ρ a b : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : 0 < a) (hb : 0 < b)
    (hρ0 : ρ ≤ a / (2 * farConst n * b)) (hfin : μ (ball x r) ≠ ∞)
    (hlow : ENNReal.ofReal (a * r ^ (n - 1)) ≤ μ (ball x r))
    (hup : ∀ y ∈ ball x r, μ (ball y (ρ * r)) ≤ ENNReal.ofReal (b * (ρ * r) ^ (n - 1)))
    {z₁ z₂ : Rn n} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (h₁ : ball x ((1 + ρ) * r) ⊆ ball z₁ R₁) (h₂ : ball x ((1 + ρ) * r) ⊆ ball z₂ R₂)
    (hfin₁ : μ (ball z₁ R₁) ≠ ∞) (hfin₂ : μ (ball z₂ R₂) ≠ ∞) :
    ENNReal.ofReal (planeDist x r (bestPlane μ z₁ R₁) (bestPlane μ z₂ R₂) ^ 2) ≤
      ENNReal.ofReal (48 * 3 ^ n / (ρ ^ (n + 2) * a * r ^ (n + 1))) *
        (ENNReal.ofReal (R₁ ^ (n + 1)) * jonesBetaSq μ z₁ R₁ +
          ENNReal.ofReal (R₂ ^ (n + 1)) * jonesBetaSq μ z₂ R₂) := by
  have hn1 : 1 ≤ n := by omega
  refine (planeDist_sq_le_of_mass hn hr hρ hρ1 ha hb hρ0 hfin hlow hup
    (norm_bestPlane_snd hn1 μ z₁ R₁) (norm_bestPlane_snd hn1 μ z₂ R₂)).trans ?_
  gcongr
  · exact (lintegral_mono_set h₁).trans (lintegral_bestPlane hn1 hR₁ hfin₁).le
  · exact (lintegral_mono_set h₂).trans (lintegral_bestPlane hn1 hR₂ hfin₂).le

/-- **(C2) Miś Lemma 3.3, `q = 2`, at a general centre and scale**. Let `τ, M > 0`,
`R > 0`, `0 < ρ ≤ 1/2`, `ρ ≤ τ / (2 A_n)`, `κ = 1/(1−ρ)`, `x ∈ B_R(z)` and `μ(B_{κR}(z)) < ∞`.
Assume `μ(B_{ρR}(x)) ≥ τM (ρR)^{n−1}` and `μ(B_{ρ²R}(y)) ≤ M (ρ²R)^{n−1}` for all `y ∈ B_{ρR}(x)`.
Then
`planeDist x (ρR) V(z,κR) V(x,κρR) ² ≤ 48 · 3ⁿ κ^{n+1} / (τ ρ^{2n+3} M) · (β²(z,κR) + β²(x,κρR))`.

Miś's hypotheses `μ(B₁) ≥ τM` and `d(x, V) ≤ ρ/2` are not needed, and the upper
mass bound is only required at centres in `B_{ρR}(x)`, so this is at least as strong as Miś 3.3. -/
theorem dist_bestPlane_le (hn : 2 ≤ n) {μ : Measure (Rn n)} {x z : Rn n} {R ρ τ M κ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (hτ : 0 < τ) (hM : 0 < M)
    (hρ0 : ρ ≤ τ / (2 * farConst n)) (hκ : κ = (1 - ρ)⁻¹) (hx : x ∈ ball z R)
    (hfin : μ (ball z (κ * R)) ≠ ∞)
    (hlow : ENNReal.ofReal (τ * M * (ρ * R) ^ (n - 1)) ≤ μ (ball x (ρ * R)))
    (hup : ∀ y ∈ ball x (ρ * R),
      μ (ball y (ρ ^ 2 * R)) ≤ ENNReal.ofReal (M * (ρ ^ 2 * R) ^ (n - 1))) :
    ENNReal.ofReal
        (planeDist x (ρ * R) (bestPlane μ z (κ * R)) (bestPlane μ x (κ * ρ * R)) ^ 2) ≤
      ENNReal.ofReal (48 * 3 ^ n * κ ^ (n + 1) / (τ * ρ ^ (2 * n + 3) * M)) *
        (jonesBetaSq μ z (κ * R) + jonesBetaSq μ x (κ * ρ * R)) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have hκpos : 0 < κ := by rw [hκ]; exact inv_pos.2 h1ρ
  have hκ1 : κ * (1 - ρ) = 1 := by rw [hκ, inv_mul_cancel₀ h1ρ.ne']
  have hκρ : 1 + ρ + ρ ^ 2 ≤ κ := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_right hcon h1ρ
    linarith [pow_pos hρ 3]
  have hdist : dist x z < R := mem_ball.1 hx
  have hA := farConst_pos n
  have hρR : 0 < ρ * R := mul_pos hρ hR
  have hκR := mul_le_mul_of_nonneg_right hκρ hR.le
  have hρ2R := mul_nonneg (sq_nonneg ρ) hR.le
  have hκR' : κ * R - κ * ρ * R = R := by linear_combination R * hκ1
  have hκ1ρ : 1 + ρ ≤ κ := by linarith [sq_nonneg ρ]
  have hsubx : ball x (ρ * R) ⊆ ball z (κ * R) := ball_subset_ball' (by linarith)
  have hsub₂ : ball x (κ * ρ * R) ⊆ ball z (κ * R) := ball_subset_ball' (by linarith)
  have key := planeDist_bestPlane_sq_le_of_subset (μ := μ) hn hρR hρ (by linarith)
    (mul_pos hτ hM) hM (by rw [mul_div_mul_right _ _ hM.ne']; exact hρ0)
    (ne_top_of_le_ne_top hfin (measure_mono hsubx)) hlow
    (fun y hy => by rw [show ρ * (ρ * R) = ρ ^ 2 * R by ring]; exact hup y hy)
    (mul_pos hκpos hR) (by positivity : 0 < κ * ρ * R)
    (ball_subset_ball' (by linarith))
    (ball_subset_ball (by linarith [mul_le_mul_of_nonneg_right hκ1ρ hρR.le]))
    hfin (ne_top_of_le_ne_top hfin (measure_mono hsub₂))
  refine key.trans ?_
  set C' := 48 * 3 ^ n * κ ^ (n + 1) / (τ * ρ ^ (2 * n + 3) * M) with hC'
  set C := 48 * 3 ^ n / (ρ ^ (n + 2) * (τ * M) * (ρ * R) ^ (n + 1)) with hC
  have hC0 : 0 ≤ C := by positivity
  have e1 : C * (κ * R) ^ (n + 1) = C' := by
    rw [hC, hC']
    field_simp
    ring
  have e2 : C * (κ * ρ * R) ^ (n + 1) = C' * ρ ^ (n + 1) := by
    rw [hC, hC']
    field_simp
    ring
  have hρn : ρ ^ (n + 1) ≤ 1 := pow_le_one₀ hρ.le (by linarith)
  have hC'0 : 0 ≤ C' := by positivity
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hC0,
    ← ENNReal.ofReal_mul hC0, e1, e2]
  gcongr
  exact mul_le_of_le_one_right hC'0 hρn

end GMTFoundations
