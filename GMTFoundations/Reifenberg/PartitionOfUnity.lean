/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Setup
import GMTFoundations.GMT.Packing
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# A piecewise linear partition of unity at one scale

The partition of unity with properties (1)–(4) stated before Definition 3.1 of M. Miśkiewicz,
*Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018); arXiv:1612.02461
(hereafter Miś). Miś asserts that a smooth partition of unity with these properties exists; here it
is constructed explicitly, piecewise linear and Lipschitz rather than smooth (Lipschitz bounds are
all that the Reifenberg construction uses). Fix `r > 0` and a finite `r`-separated set of
centres `Y`.

* `puBump r c z = φ(|z − c| / r)` with `φ(t) = min 1 (max 0 (4 − t))`: equal to `1` on `B̄_{3r}(c)`,
  positive exactly on `B_{4r}(c)`, and `1/r`-Lipschitz.
* `puSum r Y z = Σ_{c ∈ Y} puBump r c z`,
  `puLambda r Y c z = puBump r c z / max (puSum r Y z) 1`, and
  `puPsi r Y z = 1 − Σ_c puLambda r Y c z`.

## Main statements

* (1.0) `card_filter_dist_lt_four_le`: at most `9ⁿ` centres of `Y` lie within `4r` of any point.
* (1.1) `puLambda_nonneg`, `sum_puLambda_le_one`, `puPsi_nonneg`, `puPsi_eq_max`.
* (1.2) `puLambda_eq_zero` (off `B_{4r}(c)`); `sum_puLambda_eq_one`, `puPsi_eq_zero`
  (on `B̄_{3r}(c)`).
* (1.3) `sum_abs_puLambda_sub_le`: `Σ_c |λ_c(z) − λ_c(z')| ≤ 4·9ⁿ |z − z'| / r`, and the
  consequences `abs_puLambda_sub_le`, `abs_puPsi_sub_le`.
* (1.4) `puSum_of_subset`, `puLambda_of_subset`: localization to a subfamily.
-/

public noncomputable section

namespace GMTFoundations

open Metric

variable {n : ℕ}

/-- The bump `φ(|z − c|/r)` with `φ(t) = min 1 (max 0 (4 − t))`. -/
@[expose] def puBump (r : ℝ) (c z : Rn n) : ℝ := min 1 (max 0 (4 - dist z c / r))

/-- `Φ(z) = Σ_{c ∈ Y} φ_c(z)`. -/
@[expose] def puSum (r : ℝ) (Y : Finset (Rn n)) (z : Rn n) : ℝ := ∑ c ∈ Y, puBump r c z

/-- `λ_c(z) = φ_c(z) / max(Φ(z), 1)`. -/
@[expose] def puLambda (r : ℝ) (Y : Finset (Rn n)) (c z : Rn n) : ℝ :=
  puBump r c z / max (puSum r Y z) 1

/-- `ψ(z) = 1 − Σ_{c ∈ Y} λ_c(z)`. -/
@[expose] def puPsi (r : ℝ) (Y : Finset (Rn n)) (z : Rn n) : ℝ :=
  1 - ∑ c ∈ Y, puLambda r Y c z

variable {r : ℝ} {Y Y' : Finset (Rn n)} {c z z' : Rn n}

/-! ### The bump -/

theorem puBump_nonneg : 0 ≤ puBump r c z := le_min zero_le_one (le_max_left _ _)

theorem puBump_le_one : puBump r c z ≤ 1 := min_le_left _ _

theorem puBump_eq_zero (hr : 0 < r) (h : 4 * r ≤ dist z c) : puBump r c z = 0 := by
  have h4 : 4 ≤ dist z c / r := by rwa [le_div_iff₀ hr]
  rw [puBump, max_eq_left (by linarith), min_eq_right zero_le_one]

theorem dist_lt_of_puBump_pos (hr : 0 < r) (h : 0 < puBump r c z) : dist z c < 4 * r := by
  by_contra h'
  rw [puBump_eq_zero hr (not_lt.1 h')] at h
  exact lt_irrefl _ h

theorem puBump_eq_one (hr : 0 < r) (h : dist z c ≤ 3 * r) : puBump r c z = 1 := by
  have h3 : dist z c / r ≤ 3 := by rwa [div_le_iff₀ hr]
  rw [puBump, max_eq_right (by linarith), min_eq_left (by linarith)]

private theorem abs_clamp_sub_le (a b : ℝ) :
    |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (abs_nonneg _) ?_
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  exact max_le (abs_nonneg _) le_rfl

theorem abs_puBump_sub_le (hr : 0 < r) (c z z' : Rn n) :
    |puBump r c z - puBump r c z'| ≤ dist z z' / r := by
  refine (abs_clamp_sub_le _ _).trans ?_
  rw [show 4 - dist z c / r - (4 - dist z' c / r) = (dist z' c - dist z c) / r by ring, abs_div,
    abs_of_pos hr]
  gcongr
  rw [abs_sub_comm]
  exact abs_dist_sub_le z z' c

/-! ### (1.0) Overlap count -/

/-- (1.0) At most `9ⁿ` points of an `r`-separated set lie within `4r` of `z`. -/
theorem card_filter_dist_lt_four_le (hr : 0 < r)
    (hY : (Y : Set (Rn n)).Pairwise fun a b => r ≤ dist a b) (z : Rn n) :
    ((Y.filter fun c : Rn n => dist z c < 4 * r).card : ℝ) ≤ 9 ^ n := by
  have h := NaberValtorta.card_le_of_pairwise_le_dist
    (F := Y.filter fun c : Rn n => dist z c < 4 * r)
    (z := z) (ρ := 4 * r) hr (by positivity) ?_ ?_
  · rwa [show 2 * (4 * r) / r + 1 = 9 by field_simp; norm_num] at h
  · intro c hc
    rw [Finset.coe_filter, Set.mem_ofPred_eq] at hc
    rw [mem_closedBall, dist_comm]
    exact hc.2.le
  · exact hY.mono (Finset.coe_subset.2 (Finset.filter_subset _ Y))

/-- `Σ_c |φ_c(z) − φ_c(z')| ≤ 2·9ⁿ |z − z'| / r`. -/
theorem sum_abs_puBump_sub_le (hr : 0 < r)
    (hY : (Y : Set (Rn n)).Pairwise fun a b => r ≤ dist a b) (z z' : Rn n) :
    ∑ c ∈ Y, |puBump r c z - puBump r c z'| ≤ 2 * 9 ^ n * (dist z z' / r) := by
  classical
  set D := dist z z' / r
  have hD : 0 ≤ D := div_nonneg dist_nonneg hr.le
  have hterm : ∀ c ∈ Y, |puBump r c z - puBump r c z'| ≤
      ((if dist z c < 4 * r then (1 : ℝ) else 0) + (if dist z' c < 4 * r then (1 : ℝ) else 0)) *
        D := by
    intro c _
    by_cases h1 : dist z c < 4 * r
    · have h := abs_puBump_sub_le hr c z z'
      rw [ite_eq_left h1]
      split_ifs <;> nlinarith
    · by_cases h2 : dist z' c < 4 * r
      · have h := abs_puBump_sub_le hr c z z'
        rw [ite_eq_right h1, ite_eq_left h2]
        linarith
      · rw [puBump_eq_zero hr (not_lt.1 h1), puBump_eq_zero hr (not_lt.1 h2), sub_self, abs_zero]
        rw [ite_eq_right h1, ite_eq_right h2]
        simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
  have h1 := card_filter_dist_lt_four_le hr hY z
  have h2 := card_filter_dist_lt_four_le hr hY z'
  nlinarith

theorem abs_puSum_sub_le (hr : 0 < r)
    (hY : (Y : Set (Rn n)).Pairwise fun a b => r ≤ dist a b) (z z' : Rn n) :
    |puSum r Y z - puSum r Y z'| ≤ 2 * 9 ^ n * (dist z z' / r) := by
  rw [puSum, puSum, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_abs_puBump_sub_le hr hY z z')

/-! ### (1.1), (1.2) Algebra and supports -/

theorem puSum_nonneg : 0 ≤ puSum r Y z := Finset.sum_nonneg fun _ _ => puBump_nonneg

theorem one_le_max_puSum : 1 ≤ max (puSum r Y z) 1 := le_max_right _ _

theorem puLambda_nonneg : 0 ≤ puLambda r Y c z :=
  div_nonneg puBump_nonneg (zero_le_one.trans one_le_max_puSum)

theorem puLambda_le_one : puLambda r Y c z ≤ 1 :=
  (div_le_one (zero_lt_one.trans_le one_le_max_puSum)).2
    (puBump_le_one.trans one_le_max_puSum)

theorem sum_puLambda_eq : ∑ c ∈ Y, puLambda r Y c z = puSum r Y z / max (puSum r Y z) 1 := by
  rw [puSum, Finset.sum_div]
  rfl

theorem sum_puLambda_le_one : ∑ c ∈ Y, puLambda r Y c z ≤ 1 := by
  rw [sum_puLambda_eq]
  exact (div_le_one (zero_lt_one.trans_le one_le_max_puSum)).2 (le_max_left _ _)

theorem sum_puLambda_nonneg : 0 ≤ ∑ c ∈ Y, puLambda r Y c z :=
  Finset.sum_nonneg fun _ _ => puLambda_nonneg

theorem puPsi_nonneg : 0 ≤ puPsi r Y z := sub_nonneg.2 sum_puLambda_le_one

theorem puPsi_le_one : puPsi r Y z ≤ 1 := sub_le_self _ sum_puLambda_nonneg

theorem puPsi_add_sum : puPsi r Y z + ∑ c ∈ Y, puLambda r Y c z = 1 := sub_add_cancel _ _

/-- (1.1) `ψ = (1 − Φ)⁺`. -/
theorem puPsi_eq_max : puPsi r Y z = max (1 - puSum r Y z) 0 := by
  rw [puPsi, sum_puLambda_eq]
  rcases le_total (puSum r Y z) 1 with h | h
  · rw [max_eq_right h, div_one, max_eq_left (by linarith)]
  · rw [max_eq_left h, div_self (by linarith), sub_self, max_eq_right (by linarith)]

/-- (1.2) `λ_c = 0` off `B_{4r}(c)` (Miś (2)). -/
theorem puLambda_eq_zero (hr : 0 < r) (h : 4 * r ≤ dist z c) : puLambda r Y c z = 0 := by
  rw [puLambda, puBump_eq_zero hr h, zero_div]

theorem dist_lt_of_puLambda_pos (hr : 0 < r) (h : 0 < puLambda r Y c z) : dist z c < 4 * r := by
  by_contra h'
  rw [puLambda_eq_zero hr (not_lt.1 h')] at h
  exact lt_irrefl _ h

theorem one_le_puSum (hr : 0 < r) (hc : c ∈ Y) (h : dist z c ≤ 3 * r) : 1 ≤ puSum r Y z := by
  rw [← puBump_eq_one hr h, puSum]
  exact Finset.single_le_sum (f := fun c => puBump r c z) (fun _ _ => puBump_nonneg) hc

/-- (1.2) `ψ = 0` on `B̄_{3r}(c)`, `c ∈ Y`. -/
theorem puPsi_eq_zero (hr : 0 < r) (hc : c ∈ Y) (h : dist z c ≤ 3 * r) : puPsi r Y z = 0 := by
  rw [puPsi_eq_max, max_eq_right (by linarith [one_le_puSum hr hc h])]

/-- (1.2) `Σ_c λ_c = 1` on `B̄_{3r}(c)`, `c ∈ Y` (Miś (1)). -/
theorem sum_puLambda_eq_one (hr : 0 < r) (hc : c ∈ Y) (h : dist z c ≤ 3 * r) :
    ∑ c ∈ Y, puLambda r Y c z = 1 := by
  have := puPsi_add_sum (r := r) (Y := Y) (z := z)
  rw [puPsi_eq_zero hr hc h, zero_add] at this
  exact this

/-! ### (1.3) Lipschitz bounds -/

private theorem abs_div_sub_div_le {a a' m m' : ℝ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (ha' : 0 ≤ a') :
    |a / m - a' / m'| ≤ |a - a'| + a' / m' * |m - m'| := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hm0' : 0 < m' := zero_lt_one.trans_le hm'
  have hid : a / m - a' / m' = (a - a') / m + a' / m' * ((m' - m) / m) := by
    field_simp
    ring
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hm0]
    exact div_le_self (abs_nonneg _) hm
  · rw [abs_mul, abs_of_nonneg (div_nonneg ha' hm0'.le), abs_div, abs_of_pos hm0, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left (div_le_self (abs_nonneg _) hm) (div_nonneg ha' hm0'.le)

/-- (1.3) `Σ_c |λ_c(z) − λ_c(z')| ≤ L_n |z − z'| / r` with `L_n = 4·9ⁿ`. -/
theorem sum_abs_puLambda_sub_le (hr : 0 < r)
    (hY : (Y : Set (Rn n)).Pairwise fun a b => r ≤ dist a b) (z z' : Rn n) :
    ∑ c ∈ Y, |puLambda r Y c z - puLambda r Y c z'| ≤ 4 * 9 ^ n * (dist z z' / r) := by
  set m := max (puSum r Y z) 1
  set m' := max (puSum r Y z') 1
  have hS := sum_abs_puBump_sub_le hr hY z z'
  have hterm : ∀ c ∈ Y, |puLambda r Y c z - puLambda r Y c z'| ≤
      |puBump r c z - puBump r c z'| + puLambda r Y c z' * |m - m'| := fun c _ =>
    abs_div_sub_div_le one_le_max_puSum one_le_max_puSum puBump_nonneg
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hm : |m - m'| ≤ 2 * 9 ^ n * (dist z z' / r) :=
    (abs_max_sub_max_le_abs _ _ _).trans (abs_puSum_sub_le hr hY z z')
  have h1 : (∑ c ∈ Y, puLambda r Y c z') * |m - m'| ≤ |m - m'| :=
    mul_le_of_le_one_left (abs_nonneg _) sum_puLambda_le_one
  linarith

/-- (1.3) `|λ_c(z) − λ_c(z')| ≤ L_n |z − z'| / r` for `c ∈ Y` (Miś (3)). -/
theorem abs_puLambda_sub_le (hr : 0 < r)
    (hY : (Y : Set (Rn n)).Pairwise fun a b => r ≤ dist a b) (hc : c ∈ Y) (z z' : Rn n) :
    |puLambda r Y c z - puLambda r Y c z'| ≤ 4 * 9 ^ n * (dist z z' / r) :=
  (Finset.single_le_sum (f := fun c => |puLambda r Y c z - puLambda r Y c z'|)
    (fun _ _ => abs_nonneg _) hc).trans (sum_abs_puLambda_sub_le hr hY z z')

/-- (1.3) `|ψ(z) − ψ(z')| ≤ L_n |z − z'| / r` (Miś (4)). -/
theorem abs_puPsi_sub_le (hr : 0 < r)
    (hY : (Y : Set (Rn n)).Pairwise fun a b => r ≤ dist a b) (z z' : Rn n) :
    |puPsi r Y z - puPsi r Y z'| ≤ 4 * 9 ^ n * (dist z z' / r) := by
  rw [puPsi, puPsi, sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib, ← abs_neg,
    ← Finset.sum_neg_distrib]
  simp only [neg_sub]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_abs_puLambda_sub_le hr hY z z')

/-! ### (1.4) Localization -/

/-- (1.4) If every centre of `Y` outside `Y' ⊆ Y` is at distance `≥ 4r` from `z`, then
`Φ^{Y'}(z) = Φ^Y(z)`. -/
theorem puSum_of_subset (hr : 0 < r) (hY' : Y' ⊆ Y)
    (h : ∀ c ∈ Y, c ∉ Y' → 4 * r ≤ dist z c) : puSum r Y' z = puSum r Y z :=
  Finset.sum_subset hY' fun c hc hc' => puBump_eq_zero hr (h c hc hc')

/-- (1.4) Localization of `λ`. -/
theorem puLambda_of_subset (hr : 0 < r) (hY' : Y' ⊆ Y)
    (h : ∀ c ∈ Y, c ∉ Y' → 4 * r ≤ dist z c) (c : Rn n) :
    puLambda r Y' c z = puLambda r Y c z := by
  rw [puLambda, puLambda, puSum_of_subset hr hY' h]

end GMTFoundations
