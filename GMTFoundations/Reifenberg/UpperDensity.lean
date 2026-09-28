/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.GMT.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# Lower bound for the upper density of `ℋ^k` (Step A)

The lower half of Thm 2.7 of L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of
Functions*, rev. ed., CRC Press, 2015 (EG), p. 93 (proof of Claim #2, pp. 95–96), in the
uniform-scale form used by the rectifiable-Reifenberg theorem (Step A in `Rectifiable.lean`):

* `hausdorffN_eq_zero_of_forall_ball_le` (**Lemma A**): if `A ⊆ E`, `ℋ^k(A) < ∞`, `c < ω_k/2^k`
  and `ℋ^k(E ∩ B_r(x)) ≤ c r^k` for every `x ∈ A` and every `0 < r < r₀`, then `ℋ^k(A) = 0`.
* `exists_lt_hausdorffN_inter_ball` (Corollary A′): a set `E` with `0 < ℋ^k(E) < ∞` contains a
  point `x` with `c r^k < ℋ^k(E ∩ B_r(x))` for some `r < r₀`.

`hausdorffN n k = (ω_k/2^k) μH[k]` is EG's `ℋ^k` exactly. Balls are open. EG's `B(x, r)` is
closed and Claim #2 uses `C ⊆ B(x, diam C)`; we use `C ⊆ B_r(x)` for every `r > diam C` and let
`r ↓ diam C` instead, so no comparison of open and closed balls is needed. No measurability is
used: every step is an outer-measure inequality. The a.e. form of EG's Claim #2 is not needed and
not formalized.

## References

* [EG] L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
  CRC Press, 2015, Thm 2.7 (p. 93).
-/

public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace GMTFoundations.GMT

variable {n : ℕ}

/-- One covering set: if `t` meets `A` at `x`, `ediam t < r₀` and `ℋ^k(E ∩ B_r(x)) ≤ c r^k` for
all `0 < r < r₀`, then `ℋ^k(A ∩ t) ≤ c · (ediam t)^k` (let `r ↓ diam t`). -/
private theorem hausdorffN_inter_le_of_forall_ball_le {k : ℕ} {A E t : Set (Rn n)} (hAE : A ⊆ E)
    {c r₀ : ℝ} (hc : 0 ≤ c) {x : Rn n} (hxt : x ∈ t)
    (hx : ∀ r, 0 < r → r < r₀ → hausdorffN n k (E ∩ ball x r) ≤ ENNReal.ofReal (c * r ^ k))
    (ht : ediam t < ENNReal.ofReal r₀) :
    hausdorffN n k (A ∩ t) ≤ ENNReal.ofReal c * ediam t ^ (k : ℝ) := by
  have hne : ediam t ≠ ∞ := ht.ne_top
  set d := diam t with hd
  have hd0 : 0 ≤ d := diam_nonneg
  have hdr₀ : d < r₀ := by
    rw [hd, diam, ← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hne]
    exact ht
  have hbdd : Bornology.IsBounded t := isBounded_iff_ediam_ne_top.2 hne
  -- `ℋ(A ∩ t) ≤ c r^k` for every `r ∈ (d, r₀)`.
  have hbound : ∀ r, d < r → r < r₀ → hausdorffN n k (A ∩ t) ≤ ENNReal.ofReal (c * r ^ k) := by
    intro r hdr hrr₀
    refine le_trans (measure_mono ?_) (hx r (hd0.trans_lt hdr) hrr₀)
    rintro y ⟨hyA, hyt⟩
    exact ⟨hAE hyA, mem_ball.2 ((dist_le_diam_of_mem hbdd hyt hxt).trans_lt hdr)⟩
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (c * r ^ k)) (𝓝[>] d)
      (𝓝 (ENNReal.ofReal (c * d ^ k))) :=
    ((ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow k))).tendsto d).mono_left
      nhdsWithin_le_nhds
  have hev : ∀ᶠ r in 𝓝[>] d, hausdorffN n k (A ∩ t) ≤ ENNReal.ofReal (c * r ^ k) := by
    filter_upwards [Ioo_mem_nhdsGT hdr₀] with r hr using hbound r hr.1 hr.2
  have := ge_of_tendsto hlim hev
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_pow hd0, hd, diam, ENNReal.ofReal_toReal hne] at this
  rwa [ENNReal.rpow_natCast]

/-- **Lemma A** (EG Thm 2.7, lower half, in uniform-scale form; proof of Claim #2,
EG pp. 95–96). If
`c < ω_k/2^k` and `ℋ^k(E ∩ B_r(x)) ≤ c r^k` for every `x ∈ A ⊆ E` and every `0 < r < r₀`, then
the `ℋ^k`-finite set `A` is `ℋ^k`-null. -/
theorem hausdorffN_eq_zero_of_forall_ball_le {k : ℕ} {A E : Set (Rn n)} (hAE : A ⊆ E)
    (hA : hausdorffN n k A ≠ ∞) {c r₀ : ℝ} (hc : c < unitBallVolume k / 2 ^ k) (hr₀ : 0 < r₀)
    (h : ∀ x ∈ A, ∀ r, 0 < r → r < r₀ →
      hausdorffN n k (E ∩ ball x r) ≤ ENNReal.ofReal (c * r ^ k)) :
    hausdorffN n k A = 0 := by
  classical
  set ω : ℝ := unitBallVolume k / 2 ^ k with hω
  have hω0 : 0 < ω := div_pos (unitBallVolume_pos k) (pow_pos two_pos k)
  -- Replace `c` by a positive constant `c' ∈ [c, ω)`.
  set c' : ℝ := max c (ω / 2) with hc'
  have hc'0 : 0 < c' := lt_max_of_lt_right (half_pos hω0)
  have hc'ω : c' < ω := max_lt hc (half_lt_self hω0)
  have h' : ∀ x ∈ A, ∀ r, 0 < r → r < r₀ →
      hausdorffN n k (E ∩ ball x r) ≤ ENNReal.ofReal (c' * r ^ k) := fun x hx r hr hrr₀ =>
    (h x hx r hr hrr₀).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hc'ne : ENNReal.ofReal c' ≠ 0 := (ENNReal.ofReal_pos.2 hc'0).ne'
  -- Every cover at scale `r₀/2` bounds `ℋ(A) / c'`.
  set R : ℝ≥0∞ := ENNReal.ofReal (r₀ / 2) with hR
  have hR0 : 0 < R := ENNReal.ofReal_pos.2 (half_pos hr₀)
  have hRr₀ : R < ENNReal.ofReal r₀ :=
    (ENNReal.ofReal_lt_ofReal_iff hr₀).2 (half_lt_self hr₀)
  have hcover : hausdorffN n k A / ENNReal.ofReal c' ≤
      ⨅ (t : ℕ → Set (Rn n)) (_ : A ⊆ ⋃ i, t i) (_ : ∀ i, ediam (t i) ≤ R),
        ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (k : ℝ) := by
    refine le_iInf₂ fun t hAt => le_iInf fun htR => ?_
    refine ENNReal.div_le_of_le_mul' ?_
    calc hausdorffN n k A ≤ hausdorffN n k (⋃ i, A ∩ t i) := by
          rw [← inter_iUnion]; exact measure_mono (subset_inter subset_rfl hAt)
      _ ≤ ∑' i, hausdorffN n k (A ∩ t i) := measure_iUnion_le _
      _ ≤ ∑' i, ENNReal.ofReal c' * ⨆ _ : (t i).Nonempty, ediam (t i) ^ (k : ℝ) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          rcases (A ∩ t i).eq_empty_or_nonempty with he | ⟨x, hxA, hxt⟩
          · rw [he, measure_empty]; exact zero_le
          · rw [iSup_pos ⟨x, hxt⟩]
            exact hausdorffN_inter_le_of_forall_ball_le hAE hc'0.le hxt (h' x hxA)
              ((htR i).trans_lt hRr₀)
      _ = ENNReal.ofReal c' * ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (k : ℝ) :=
          ENNReal.tsum_mul_left
  have hle : hausdorffN n k A / ENNReal.ofReal c' ≤ μH[(k : ℝ)] A := by
    refine hcover.trans ?_
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) =>
      ⨅ (t : ℕ → Set (Rn n)) (_ : A ⊆ ⋃ i, t i) (_ : ∀ i, ediam (t i) ≤ r),
        ∑' i, ⨆ _ : (t i).Nonempty, ediam (t i) ^ (k : ℝ)) R hR0
  rw [ENNReal.div_le_iff_le_mul (Or.inl hc'ne) (Or.inl ENNReal.ofReal_ne_top),
    hausdorffN_apply] at hle
  -- `ω μH(A) ≤ c' μH(A)` with `c' < ω` and `μH(A) < ∞` forces `μH(A) = 0`.
  have hfin : μH[(k : ℝ)] A ≠ ∞ := by
    have := (hausdorffN_lt_top_iff (n := n) (d := k) (s := A)).1 (lt_top_iff_ne_top.2 hA)
    exact this.ne
  rw [hausdorffN_eq_zero_iff]
  by_contra h0
  have := (ENNReal.mul_le_mul_iff_left h0 hfin).1 (by simpa [mul_comm] using hle)
  exact absurd ((ENNReal.ofReal_le_ofReal_iff hc'0.le).1 this) (not_le.2 hc'ω)

/-- **Corollary A′** (what Step B uses). If `0 < ℋ^k(E) < ∞`, `c < ω_k/2^k` and `r₀ > 0`, then
some `x ∈ E` and `0 < r < r₀` have `c r^k < ℋ^k(E ∩ B_r(x))`. -/
theorem exists_lt_hausdorffN_inter_ball {k : ℕ} {E : Set (Rn n)} (hE : hausdorffN n k E ≠ ∞)
    (hE0 : hausdorffN n k E ≠ 0) {c r₀ : ℝ} (hc : c < unitBallVolume k / 2 ^ k) (hr₀ : 0 < r₀) :
    ∃ x ∈ E, ∃ r, 0 < r ∧ r < r₀ ∧ ENNReal.ofReal (c * r ^ k) < hausdorffN n k (E ∩ ball x r) := by
  by_contra hcon
  push Not at hcon
  exact hE0 (hausdorffN_eq_zero_of_forall_ball_le subset_rfl hE hc hr₀ hcon)

end GMTFoundations.GMT
