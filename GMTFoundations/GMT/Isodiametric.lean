/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Setup
import GMTFoundations.Vendor.Isoperimetric.BrunnMinkowski
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The isodiametric inequality

Among all sets of a given diameter in `ℝ^d`, the ball has the largest Lebesgue measure:
`|s| ≤ |B_{diam s / 2}|` (Evans–Gariepy, Thm 2.4).

The proof is the Brunn–Minkowski route: for a compact set `K`, Brunn–Minkowski applied to `K`
and `-K` gives `2^d |K| ≤ |K - K|`, and `K - K ⊆ B̄_{diam K}(0)`. A general bounded set is replaced
by its closure, which has the same diameter. Brunn–Minkowski is the vendored
`GMTFoundations.Vendor.Isoperimetric.brunn_minkowski_euclideanSpace`.

## Main statements

* `GMTFoundations.GMT.two_pow_mul_volume_le_volume_add_neg`: `2^d |K| ≤ |K + (-K)|`, `K`
  compact.
* `GMTFoundations.GMT.two_pow_mul_volume_le_volume_closedBall_diam`:
  `2^d |s| ≤ |B̄_{diam s}(0)|`, `s` bounded.
* `GMTFoundations.GMT.volume_le_volume_closedBall_diam_div_two`: the isodiametric inequality
  `|s| ≤ |B̄_{diam s / 2}(0)|`, `s` bounded.
* `GMTFoundations.GMT.volume_le_volume_ball_diam_div_two`: the same with the open ball.
* `GMTFoundations.GMT.two_pow_mul_volume_le_mul_ediam_pow`: the form
  `2^d |s| ≤ |B_1| · (ediam s)^d` valid for all sets, used for the Hausdorff measure.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
* H. Federer, *Geometric Measure Theory*, Springer, 1969.
-/

public section

open MeasureTheory Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace GMTFoundations.GMT

variable {d : ℕ}

/-- Brunn–Minkowski for `K` and `-K`: `2^d |K| ≤ |K + (-K)|` for compact `K ⊆ ℝ^d`. -/
theorem two_pow_mul_volume_le_volume_add_neg {K : Set (Rn d)} (hK : IsCompact K) :
    2 ^ d * volume K ≤ volume (K + -K) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  cases d with
  | zero =>
    rw [pow_zero, one_mul]
    refine measure_mono fun x hx => ⟨x, hx, -x, by simpa using hx, Subsingleton.elim _ _⟩
  | succ d =>
    have hbm := Vendor.Isoperimetric.brunn_minkowski_euclideanSpace hne hK.measurableSet hne.neg
      hK.neg.measurableSet (hK.add hK.neg).measurableSet
    rw [Measure.measure_neg] at hbm
    set p : ℝ := (d : ℝ) + 1 with hp
    have hp0 : 0 < p := by positivity
    have key := ENNReal.rpow_le_rpow hbm hp0.le
    rw [← two_mul, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.rpow_inv_rpow hp0.ne',
      ENNReal.rpow_inv_rpow hp0.ne'] at key
    have h2 : (2 : ℝ≥0∞) ^ p = 2 ^ (d + 1) := by
      rw [hp, ← ENNReal.rpow_natCast]
      norm_num
    rwa [h2] at key

/-- For a bounded set `s ⊆ ℝ^d`, `2^d |s| ≤ |B̄_{diam s}(0)|`. -/
theorem two_pow_mul_volume_le_volume_closedBall_diam {s : Set (Rn d)}
    (hs : Bornology.IsBounded s) :
    2 ^ d * volume s ≤ volume (closedBall (0 : Rn d) (diam s)) := by
  have hK : IsCompact (closure s) := hs.isCompact_closure
  calc 2 ^ d * volume s ≤ 2 ^ d * volume (closure s) := by
        gcongr; exact subset_closure
    _ ≤ volume (closure s + -closure s) := two_pow_mul_volume_le_volume_add_neg hK
    _ ≤ volume (closedBall (0 : Rn d) (diam s)) := by
        refine measure_mono ?_
        rintro _ ⟨a, ha, b, hb, rfl⟩
        change a + b ∈ closedBall (0 : Rn d) (diam s)
        rw [mem_closedBall, dist_zero_right]
        rw [← sub_neg_eq_add, ← dist_eq_norm, ← diam_closure]
        exact dist_le_diam_of_mem hK.isBounded ha (by simpa using hb)

/-- **Isodiametric inequality** (Evans–Gariepy Thm 2.4): a bounded set `s ⊆ ℝ^d` has at most the
volume of a closed ball of diameter `diam s`. -/
theorem volume_le_volume_closedBall_diam_div_two {s : Set (Rn d)}
    (hs : Bornology.IsBounded s) :
    volume s ≤ volume (closedBall (0 : Rn d) (diam s / 2)) := by
  have h := two_pow_mul_volume_le_volume_closedBall_diam hs
  have hD : diam s = 2 * (diam s / 2) := by ring
  rw [hD, Measure.addHaar_closedBall_mul volume 0 zero_le_two (by positivity),
    finrank_euclideanSpace_fin, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat] at h
  exact (ENNReal.mul_le_mul_iff_right (by simp) (by simp)).1 h

/-- **Isodiametric inequality**, open-ball form: `|s| ≤ |B_{diam s / 2}(0)|` for bounded `s`.
(For `d = 0` it fails: `ball 0 0 = ∅`.) -/
theorem volume_le_volume_ball_diam_div_two (hd : 0 < d) {s : Set (Rn d)}
    (hs : Bornology.IsBounded s) :
    volume s ≤ volume (ball (0 : Rn d) (diam s / 2)) := by
  have : Nontrivial (Rn d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hd)
  refine (volume_le_volume_closedBall_diam_div_two hs).trans_eq ?_
  exact Measure.addHaar_closedBall_eq_addHaar_ball _ _ _

/-- The isodiametric inequality in the form used for Hausdorff measure, valid for every set
`s ⊆ ℝ^d`: `2^d |s| ≤ |B_1| · (ediam s)^d`. -/
theorem two_pow_mul_volume_le_mul_ediam_pow (s : Set (Rn d)) :
    2 ^ d * volume s ≤ volume (ball (0 : Rn d) 1) * ediam s ^ d := by
  rcases eq_or_ne (ediam s) ⊤ with htop | htop
  · cases d with
    | zero =>
      have : ball (0 : Rn 0) 1 = univ := by
        ext x; simp [Subsingleton.elim x 0]
      rw [pow_zero, pow_zero, one_mul, mul_one, this]
      exact measure_mono (subset_univ s)
    | succ d =>
      rw [htop, ENNReal.top_pow (Nat.succ_ne_zero d), ENNReal.mul_top]
      · exact le_top
      · exact (measure_ball_pos volume 0 zero_lt_one).ne'
  · have hs : Bornology.IsBounded s := isBounded_iff_ediam_ne_top.2 htop
    refine (two_pow_mul_volume_le_volume_closedBall_diam hs).trans_eq ?_
    rw [Measure.addHaar_closedBall volume 0 diam_nonneg, finrank_euclideanSpace_fin, mul_comm,
      ENNReal.ofReal_pow diam_nonneg, diam, ENNReal.ofReal_toReal htop]

end GMTFoundations.GMT
