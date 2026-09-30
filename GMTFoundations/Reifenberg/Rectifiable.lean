/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Statements.Reifenberg
import GMTFoundations.Reifenberg.BigPieces
import GMTFoundations.Reifenberg.Exhaustion
import GMTFoundations.Reifenberg.UpperDensity

/-!
# Rectifiable-Reifenberg theorem

`rectifiable_reifenberg : RectifiableReifenbergStatement n`: the rectifiability part of the
rectifiable-Reifenberg theorem of A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity
of stationary and minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043
(NV), Thm 3.3 (2), for hyperplanes (`k = n − 1`).

The statement differs from NV Thm 3.3:
* It proves only rectifiability of `S ∩ B₁` (NV Thm 3.3 (2)); it does not claim the measure bound
  `λ^k(S ∩ B_r(x)) ≤ (1 + ε) ω_k r^k` of NV Thm 3.3 (1).
* It assumes the upper bound `ℋ^{n-1}(S ∩ B_r(x)) ≤ C r^{n-1}` on every ball, and `δ = δ(n, C)`.
* The square-function bound is assumed on every ball `B_s(y) ⊆ B₂`, whereas NV assume it only on
  balls with `λ^k(S ∩ B_r(x)) ≥ ε_n r^k`; the hypothesis here is stronger.

The proof does not follow NV §5.9 (which goes through `W^{1,p}` maps and NV Lemmas 2.19 and 2.20).
It runs the Reifenberg construction of the discrete Reifenberg theorem (M. Miśkiewicz, *Discrete
Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018); arXiv:1612.02461, §4) directly on
the continuous measure `ℋ^{n-1}⌊S`, with a stopping time on the measure side, to produce big
pieces of Lipschitz images, and concludes by exhaustion. It combines
* Step A, Corollary A′ (`GMT.exists_lt_hausdorffN_inter_ball`, `Reifenberg/UpperDensity.lean`): the
  upper density of `ℋ^{n-1}⌊P` is at least `2^{-(n-1)}` at `ℋ^{n-1}`-a.e. point of `P`, in a
  uniform-scale form (lower half of Thm 2.7 of L. C. Evans, R. F. Gariepy, *Measure Theory and Fine
  Properties of Functions*, rev. ed., CRC Press, 2015);
* Step B, the exhaustion by Lipschitz images and the rescaling (`exists_lipschitz_exhaustion`,
  `rescale_hyp`, `Reifenberg/Exhaustion.lean`);
* Step C, big pieces (`exists_bigPiece`, `Reifenberg/BigPieces.lean`, via
  `Reifenberg/LimitMap.lean` and `Reifenberg/StoppingTime.lean`).

`rectifiable_reifenberg` depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace GMTFoundations

variable {n : ℕ}

/-- **Rectifiable-Reifenberg theorem**, rectifiability part (NV Thm 3.3 (2), `k = n − 1`), under
an upper bound `ℋ^{n-1}(S ∩ B_r(x)) ≤ C r^{n-1}` on all balls and with the square-function bound
on every ball `B_s(y) ⊆ B₂`.

Take `δ = δ(n, C)` from Step C (`exists_bigPiece`), and let `f_i` be an exhaustion of
`S ∩ B₁` by Lipschitz images (`exists_lipschitz_exhaustion`) with remainder `P`. If
`ℋ^{n-1}(P) > 0`, Corollary A′ (`exists_lt_hausdorffN_inter_ball`) gives `x ∈ P` and `r < 1/16` with
`ℋ^{n-1}(P ∩ B_r(x)) > η r^{n-1}`, `η = ω_{n-1}/2^n`. The blow-up `μ'` of `ℋ^{n-1}⌊P` at `B_r(x)`
satisfies the hypotheses of Step C (`rescale_hyp`, since `B_{16r}(x) ⊆ B₂`), so some Lipschitz image
`F` has `μ'(range F) ≠ 0`, i.e. `ℋ^{n-1}(P ∩ range (x + r F)) ≠ 0`, contradicting the
exhaustion. -/
theorem rectifiable_reifenberg : RectifiableReifenbergStatement n := by
  intro hn C
  obtain ⟨δ, hδ, hbig⟩ := exists_bigPiece hn C
  refine ⟨δ, hδ, fun S _ _ hfin hup hsq => ?_⟩
  set E := S ∩ ball (0 : Rn n) 1 with hE
  have hEfin : hausdorffN n (n - 1) E ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt hfin).ne
  obtain ⟨f, hf, hP⟩ := exists_lipschitz_exhaustion hEfin
  refine ⟨f, hf, ?_⟩
  set P := E \ ⋃ i, range (f i) with hPdef
  by_contra hP0
  have hPfin : hausdorffN n (n - 1) P ≠ ∞ := ne_top_of_le_ne_top hEfin (measure_mono sdiff_subset)
  -- Step A: a ball `B_r(x)`, `r < 1/16`, carrying mass `> η r^{n-1}` of `P`.
  obtain ⟨x, hxP, r, hr, hr16, hmass⟩ := GMT.exists_lt_hausdorffN_inter_ball hPfin hP0
    (bigPieceMass_lt (by omega)) (show (0 : ℝ) < 1 / 16 by norm_num)
  have hPS : P ⊆ S := fun z hz => hz.1.1
  have hx1 : x ∈ ball (0 : Rn n) 1 := hxP.1.2
  have hxr : ball x (DiscreteReifenberg.ledgerR0 * r) ⊆ ball 0 2 := by
    refine ball_subset_ball' ?_
    have := mem_ball.1 hx1
    unfold DiscreteReifenberg.ledgerR0
    linarith
  -- Step B: the blow-up satisfies the hypotheses of Step C.
  obtain ⟨hμfin, hμup, hμsq⟩ := rescale_hyp hPS hfin hup hsq hr hxr
  set μ' := rescaleMeasure ((hausdorffN n (n - 1)).restrict P) x r with hμ'
  have hrk : ENNReal.ofReal ((r ^ (n - 1))⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.2 (pow_pos hr _))
  have hμmass : ENNReal.ofReal (bigPieceMass n) < μ' (ball 0 1) := by
    rw [hμ', rescaleMeasure_ball hr, smul_zero, add_zero, mul_one,
      Measure.restrict_apply measurableSet_ball, inter_comm]
    calc ENNReal.ofReal (bigPieceMass n)
        = ENNReal.ofReal ((r ^ (n - 1))⁻¹) *
            ENNReal.ofReal (bigPieceMass n * r ^ (n - 1)) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 (pow_pos hr _).le)]
          congr 1
          field_simp
      _ < ENNReal.ofReal ((r ^ (n - 1))⁻¹) * hausdorffN n (n - 1) (P ∩ ball x r) :=
          ENNReal.mul_lt_mul_right hrk ENNReal.ofReal_ne_top hmass
  -- Step C, and back to the original frame.
  obtain ⟨F, ⟨L, hF⟩, hFne⟩ := hbig μ' hμfin hμup hμsq hμmass
  set g : Rn (n - 1) → Rn n := fun z => x + r • F z with hg
  have hgL : LipschitzWith (Real.toNNReal r * L) g := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [hg, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr, NNReal.coe_mul,
      Real.coe_toNNReal _ hr.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hF.dist_le_mul a b) hr.le
  apply hFne
  rw [hμ', rescaleMeasure_apply hr, ← range_comp]
  change _ * (hausdorffN n (n - 1)).restrict P (range g) = 0
  rw [Measure.restrict_apply (measurableSet_range_of_lipschitzWith hgL), inter_comm,
    hP g ⟨_, hgL⟩, mul_zero]

end GMTFoundations
