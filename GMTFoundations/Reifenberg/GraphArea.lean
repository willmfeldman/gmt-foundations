/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.ReifenbergMap
import GMTFoundations.GMT.Basic
import GMTFoundations.GMT.HausdorffLebesgue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Area bounds for plane pieces, graphs and Reifenberg maps

The area estimates behind (4.1), (4.2) and Proposition 4.3(b) of M. Miśkiewicz, *Discrete
Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018); arXiv:1612.02461 (Miś), used by
the discrete and the rectifiable Reifenberg theorems. Throughout `n ≥ 2`, `k = n − 1` and
`ℋ^k = hausdorffN n k` (which equals `μHE[k]`). All bounds are outer-measure bounds: no
measurability is needed.

In the proof of (4.2), Miś uses the lower bound `|T_i ∩ B/3| ≥ (1/10)(r/3)^k` for a graph piece
over a ball `B` of radius `r = r_{i+1}`. This is false for `k ≥ 9`: a flat plane at distance
`r/4` from the centre meets `B_{r/3}` in a `k`-disc of area `ω_k (√7 r/12)^k`, which is smaller
than `(1/10)(r/3)^k` for `k ≥ 9`. We use instead the correct bound (5c) with `c₀ = ω_k 15^{-k}`;
the constants of the discrete Reifenberg theorem change accordingly.

## Main statements

* (5a) `hausdorffN_affPlane_inter_ball` (`= ω_k R^k` for centres on the plane),
  `hausdorffN_disc`, `hausdorffN_affPlane_inter_ball_le` (any centre).
* (5b) `hausdorffN_inter_ball_le_of_graph`: `ℋ^k(T ∩ B_R(c)) ≤ (1 + L²)^{k/2} ω_k R^k` for a chart
  with `Lip g ≤ L` on the disc.
* (5c) `le_hausdorffN_inter_ball_of_graph`: `ℋ^k(T ∩ B_{r/3}(y)) ≥ ω_k (r/15)^k` when
  `|f_V(y)| ≤ r/4` and `|g| ≤ r/100` on `disc V y (r/15)`.
* (5d) `hausdorffN_image_le_sum`: `ℋ^k(σ(B)) ≤ Σ_s L_s^k ℋ^k(A_s) + ℋ^k(A_rest)` (replaces Miś's
  bound `|T_{i+1}| ≤ ∫_{T_i} Lip^k_{i+1}` in the proof of (4.1)).
* (5e) `hausdorffN_le_of_le_mul_dist`: `ℋ^k(A) ≤ L^k ℋ^k(σ(A))` if `|a − b| ≤ L |σa − σb|` on `A`.
-/

public noncomputable section

namespace GMTFoundations

open MeasureTheory Metric Set
open scoped RealInnerProductSpace NNReal ENNReal

variable {n : ℕ}

/-- A Lipschitz map increases `ℋ^k` by at most `K^k`. -/
theorem hausdorffN_image_le_of_lipschitzOnWith {f : Rn n → Rn n} {K : ℝ≥0} {s : Set (Rn n)}
    (h : LipschitzOnWith K f s) (k : ℕ) :
    hausdorffN n k (f '' s) ≤ (K : ℝ≥0∞) ^ k * hausdorffN n k s := by
  rw [GMT.hausdorffN_eq_euclideanHausdorffMeasure']
  exact h.euclideanHausdorffMeasure_image_le k

/-- Translations preserve `ℋ^k`. -/
theorem hausdorffN_image_add_left (k : ℕ) (c : Rn n) (s : Set (Rn n)) :
    hausdorffN n k ((fun v => c + v) '' s) = hausdorffN n k s := by
  rw [GMT.hausdorffN_apply, GMT.hausdorffN_apply,
    Isometry.hausdorffMeasure_image (Isometry.of_dist_eq fun x y => dist_add_left c x y)
      (Or.inl (Nat.cast_nonneg k))]

/-! ### (5a) Plane pieces -/

/-- (5a) `ℋ^{n-1}(affPlane P ∩ B_R(c)) = ω_{n-1} R^{n-1}` for `c` on the plane. -/
theorem hausdorffN_affPlane_inter_ball (hn : 2 ≤ n) {P : Rn n × Rn n} (hP : ‖P.2‖ = 1)
    {c : Rn n} (hc : c ∈ affPlane P) {R : ℝ} (hR : 0 ≤ R) :
    hausdorffN n (n - 1) (affPlane P ∩ ball c R) =
      ENNReal.ofReal (unitBallVolume (n - 1) * R ^ (n - 1)) := by
  have hν : P.2 ≠ 0 := by
    intro h; rw [h, norm_zero] at hP; exact zero_ne_one hP
  have himg : affPlane P ∩ ball c R = (fun v => c + v) '' (GMT.hyperplane P.2 ∩ ball 0 R) := by
    ext x
    simp only [mem_inter_iff, mem_affPlane, mem_ball, mem_image, GMT.mem_hyperplane]
    constructor
    · rintro ⟨hx, hxc⟩
      refine ⟨x - c, ⟨?_, ?_⟩, add_sub_cancel _ _⟩
      · rw [show x - c = (x - P.1) - (c - P.1) by abel, inner_sub_left, hx, mem_affPlane.1 hc,
          sub_zero]
      · rwa [dist_eq_norm, sub_zero, ← dist_eq_norm]
    · rintro ⟨v, ⟨hv, hvR⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [show c + v - P.1 = (c - P.1) + v by abel, inner_add_left, mem_affPlane.1 hc, hv,
          add_zero]
      · rwa [dist_eq_norm, add_sub_cancel_left, ← sub_zero v, ← dist_eq_norm]
  rw [himg, hausdorffN_image_add_left, GMT.hausdorffN_eq_euclideanHausdorffMeasure']
  exact GMT.euclideanHausdorffMeasure_hyperplane_inter_ball hn hν (by simp) hR

/-- (5a) The disc has `ℋ^{n-1}(disc P c R) = ω_{n-1} R^{n-1}`. -/
theorem hausdorffN_disc (hn : 2 ≤ n) {P : Rn n × Rn n} (hP : ‖P.2‖ = 1) (c : Rn n) {R : ℝ}
    (hR : 0 ≤ R) :
    hausdorffN n (n - 1) (disc P c R) = ENNReal.ofReal (unitBallVolume (n - 1) * R ^ (n - 1)) :=
  hausdorffN_affPlane_inter_ball hn hP (affProj_mem_affPlane hP c) hR

/-- (5a) `ℋ^{n-1}(affPlane P ∩ B_R(c)) ≤ ω_{n-1} R^{n-1}` for every centre `c`. -/
theorem hausdorffN_affPlane_inter_ball_le (hn : 2 ≤ n) {P : Rn n × Rn n} (hP : ‖P.2‖ = 1)
    (c : Rn n) {R : ℝ} (hR : 0 ≤ R) :
    hausdorffN n (n - 1) (affPlane P ∩ ball c R) ≤
      ENNReal.ofReal (unitBallVolume (n - 1) * R ^ (n - 1)) := by
  rw [← hausdorffN_disc hn hP c hR]
  refine measure_mono fun x hx => ⟨hx.1, ?_⟩
  rw [mem_ball, ← affProj_of_mem hx.1]
  exact (dist_affProj_le hP x c).trans_lt hx.2

/-! ### (5b) Graph upper bound -/

/-- The graph map `x ↦ x + g(x) ν` is `√(1 + L²)`-Lipschitz on the plane if `g` is `L`-Lipschitz
there. -/
theorem lipschitzOnWith_graphMap {P : Rn n × Rn n} (hP : ‖P.2‖ = 1) {g : Rn n → ℝ} {L : ℝ≥0}
    {s : Set (Rn n)} (hs : s ⊆ affPlane P) (hg : LipschitzOnWith L g s) :
    LipschitzOnWith (NNReal.sqrt (1 + L ^ 2)) (fun x => x + g x • P.2) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
  rw [Real.coe_sqrt, NNReal.coe_add, NNReal.coe_one, NNReal.coe_pow, dist_eq_norm,
    dist_eq_norm]
  have h1 := norm_add_smul_sub_add_smul_sq hP (hs hx) (hs hx') (g x) (g x')
  have h2 : |g x - g x'| ≤ L * ‖x - x'‖ := by
    have := hg.dist_le_mul x hx x' hx'
    rwa [Real.dist_eq, dist_eq_norm] at this
  have h3 : (g x - g x') ^ 2 ≤ (L * ‖x - x'‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : ‖x + g x • P.2 - (x' + g x' • P.2)‖ ^ 2 ≤ (√(1 + (L : ℝ) ^ 2) * ‖x - x'‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), h1]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

/-- (5b) If `T ∩ B_R(c) = graphOn P g ∩ B_R(c)` and `Lip g ≤ L` on `disc P c R`, then
`ℋ^{n-1}(T ∩ B_R(c)) ≤ (1 + L²)^{(n-1)/2} ω_{n-1} R^{n-1}`. -/
theorem hausdorffN_inter_ball_le_of_graph (hn : 2 ≤ n) {P : Rn n × Rn n} (hP : ‖P.2‖ = 1)
    {T : Set (Rn n)} {g : Rn n → ℝ} {c : Rn n} {R : ℝ} {L : ℝ≥0} (hR : 0 ≤ R)
    (hT : T ∩ ball c R = graphOn P g ∩ ball c R) (hg : LipschitzOnWith L g (disc P c R)) :
    hausdorffN n (n - 1) (T ∩ ball c R) ≤
      (NNReal.sqrt (1 + L ^ 2) : ℝ≥0∞) ^ (n - 1) *
        ENNReal.ofReal (unitBallVolume (n - 1) * R ^ (n - 1)) := by
  have hsub : T ∩ ball c R ⊆ (fun x => x + g x • P.2) '' disc P c R := by
    rw [hT]
    rintro _ ⟨⟨x, hx, rfl⟩, hw⟩
    exact ⟨x, mem_disc_of_add_smul_mem_ball hP hx hw, rfl⟩
  refine (measure_mono hsub).trans ?_
  refine (hausdorffN_image_le_of_lipschitzOnWith
    (lipschitzOnWith_graphMap hP (fun x hx => hx.1) hg) (n - 1)).trans ?_
  rw [hausdorffN_disc hn hP c hR]

/-! ### (5c) Graph lower bound -/

/-- (5c) If `|f_V(y)| ≤ r/4`, `T ∩ B_{r/3}(y) = graphOn V g ∩ B_{r/3}(y)` and `|g| ≤ r/100` on
`disc V y (r/15)`, then `ℋ^{n-1}(T ∩ B_{r/3}(y)) ≥ ω_{n-1} (r/15)^{n-1}` (the lower
bound behind Miś (4.2), with `c₀ = ω_{n-1} 15^{-(n-1)}`). -/
theorem le_hausdorffN_inter_ball_of_graph (hn : 2 ≤ n) {V : Rn n × Rn n} (hV : ‖V.2‖ = 1)
    {T : Set (Rn n)} {g : Rn n → ℝ} {y : Rn n} {r : ℝ} (hr : 0 < r)
    (hy : |⟪y - V.1, V.2⟫| ≤ r / 4) (hT : T ∩ ball y (r / 3) = graphOn V g ∩ ball y (r / 3))
    (hg : ∀ x ∈ disc V y (r / 15), |g x| ≤ r / 100) :
    ENNReal.ofReal (unitBallVolume (n - 1) * (r / 15) ^ (n - 1)) ≤
      hausdorffN n (n - 1) (T ∩ ball y (r / 3)) := by
  have hsub : disc V y (r / 15) ⊆ affProj V '' (T ∩ ball y (r / 3)) := by
    intro u hu
    refine ⟨u + g u • V.2, ?_, affProj_add_smul_of_mem hV hu.1 _⟩
    have hball : u + g u • V.2 ∈ ball y (r / 3) := by
      rw [mem_ball, dist_eq_norm]
      have hsq := norm_sub_sq_eq hV (u + g u • V.2) y
      rw [affProj_add_smul_of_mem hV hu.1, inner_add_smul_sub_of_mem hV hu.1] at hsq
      have h1 : ‖u - affProj V y‖ < r / 15 := by
        have := hu.2; rwa [mem_ball, dist_eq_norm] at this
      have h2 := hg u hu
      have h3 : |g u - ⟪y - V.1, V.2⟫| ≤ r / 100 + r / 4 := (abs_sub _ _).trans (by linarith)
      have h4 : (g u - ⟪y - V.1, V.2⟫) ^ 2 ≤ (r / 100 + r / 4) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
      have h5 : ‖u - affProj V y‖ ^ 2 < (r / 15) ^ 2 :=
        pow_lt_pow_left₀ h1 (norm_nonneg _) two_ne_zero
      have h6 : ‖u + g u • V.2 - y‖ ^ 2 < (r / 3) ^ 2 := by nlinarith
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h6
    have hgr : u + g u • V.2 ∈ graphOn V g ∩ ball y (r / 3) := ⟨⟨u, hu.1, rfl⟩, hball⟩
    rw [← hT] at hgr
    exact hgr
  rw [← hausdorffN_disc hn hV y (by positivity : (0 : ℝ) ≤ r / 15)]
  refine (measure_mono hsub).trans ?_
  have := hausdorffN_image_le_of_lipschitzOnWith
    ((lipschitzWith_affProj hV).lipschitzOnWith (s := T ∩ ball y (r / 3))) (n - 1)
  simpa using this

/-! ### (5d), (5e) Piecewise bounds for a map -/

/-- (5d) If `B ⊆ ⋃_{i ∈ s} A i ∪ A_rest`, `σ` is `L_i`-Lipschitz on `A i` and `σ = id` on
`A_rest`, then `ℋ^k(σ(B)) ≤ Σ_i L_i^k ℋ^k(A i) + ℋ^k(A_rest)`. -/
theorem hausdorffN_image_le_sum {ι : Type*} (k : ℕ) (s : Finset ι) (A : ι → Set (Rn n))
    {Arest B : Set (Rn n)} (L : ι → ℝ≥0) {σ : Rn n → Rn n}
    (hB : B ⊆ (⋃ i ∈ s, A i) ∪ Arest) (hL : ∀ i ∈ s, LipschitzOnWith (L i) σ (A i))
    (hid : ∀ x ∈ Arest, σ x = x) :
    hausdorffN n k (σ '' B) ≤ ∑ i ∈ s, (L i : ℝ≥0∞) ^ k * hausdorffN n k (A i) +
      hausdorffN n k Arest := by
  have hsub : σ '' B ⊆ (⋃ i ∈ s, σ '' A i) ∪ Arest := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hB hx with hx | hx
    · rw [mem_iUnion₂] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact Or.inl (mem_iUnion₂.2 ⟨i, hi, mem_image_of_mem σ hxi⟩)
    · rw [hid x hx]; exact Or.inr hx
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ le_rfl))
  refine (measure_biUnion_finset_le s _).trans (Finset.sum_le_sum fun i hi => ?_)
  exact hausdorffN_image_le_of_lipschitzOnWith (hL i hi) k

/-- (5e) If `|a − b| ≤ L |σa − σb|` on `A`, then `ℋ^k(A) ≤ L^k ℋ^k(σ(A))`. -/
theorem hausdorffN_le_of_le_mul_dist (k : ℕ) {σ : Rn n → Rn n} {A : Set (Rn n)} {L : ℝ≥0}
    (h : ∀ a ∈ A, ∀ b ∈ A, dist a b ≤ L * dist (σ a) (σ b)) :
    hausdorffN n k A ≤ (L : ℝ≥0∞) ^ k * hausdorffN n k (σ '' A) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  have : Nonempty (Rn n) := ⟨a₀⟩
  have hinj : InjOn σ A := fun a ha b hb hab => by
    have := h a ha b hb
    rw [hab, dist_self, mul_zero] at this
    exact dist_le_zero.1 this
  have hlip : LipschitzOnWith L (Function.invFunOn σ A) (σ '' A) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have ha' := Function.invFunOn_pos (f := σ) (s := A) ⟨a, ha, rfl⟩
    have hb' := Function.invFunOn_pos (f := σ) (s := A) ⟨b, hb, rfl⟩
    have := h _ ha'.1 _ hb'.1
    rwa [ha'.2, hb'.2] at this
  have himg : Function.invFunOn σ A '' (σ '' A) = A := hinj.invFunOn_image subset_rfl
  calc hausdorffN n k A = hausdorffN n k (Function.invFunOn σ A '' (σ '' A)) := by rw [himg]
    _ ≤ _ := hausdorffN_image_le_of_lipschitzOnWith hlip k

end GMTFoundations
