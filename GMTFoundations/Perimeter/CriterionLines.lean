/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.GMT.Basic

/-!
# Lines parallel to a coordinate axis: projection and Fubini

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

Steps 1 and 4 of the null case of Federer's criterion for finite perimeter (see
`Perimeter/Criterion.lean`; EG Thm 5.23, steps 1 and 6).
For `i : Fin (m + 1)` we split `ℝ^{m+1} = ℝ × ℝ^m`, `x ↦ (xᵢ, P_i x)`, where `P_i` deletes the
`i`-th coordinate (EG Def 5.12, `P`, for a general coordinate).

* `splitCoord i : Rn (m + 1) ≃ᵐ ℝ × (Fin m → ℝ)` is volume preserving
  (`measurePreserving_splitCoord`); the factor `ℝ^m` carries the sup norm.
* `projCoord i` is `1`-Lipschitz (`lipschitzWith_projCoord`), so it does not increase `μH[m]`, and
  on `Fin m → ℝ` Mathlib's `μH[m]` is Lebesgue measure. Hence **Step 1**
  (`volume_projCoord_image_eq_zero`): if `ℋ^m(S) = 0` then `ℒ^m(P_i S) = 0`, i.e. a.e. line parallel
  to `eᵢ` misses `S`.
* **Step 4** (`setIntegral_fderiv_single_eq_zero`): if on a.e. line parallel to `eᵢ` the set `F`
  either contains or misses the whole trace of `tsupport g`, then `∫_F ∂ᵢ g = 0` for every
  `g ∈ C¹_c`. Proof: Fubini in the split coordinates (inner integral along the line first), and
  `∫_ℝ (d/dt) g(a + t eᵢ) dt = 0`.
* `norm_le_abs_add_mul_norm_projCoord`: `‖x‖ ≤ |xᵢ| + m ‖P_i x‖_∞`, used to put the boxes of
  Claim #1 into Euclidean balls.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

@[expose] public section

namespace GMTFoundations

variable {m : ℕ}

/-- Split coordinates `x ↦ (xᵢ, (x_{i.succAbove j})_j)` on `ℝ^{m+1}`. -/
noncomputable def splitCoord (i : Fin (m + 1)) : Rn (m + 1) ≃ᵐ ℝ × (Fin m → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i)

/-- The projection `P_i : ℝ^{m+1} → ℝ^m` deleting the `i`-th coordinate. -/
def projCoord (i : Fin (m + 1)) (x : Rn (m + 1)) (j : Fin m) : ℝ := x (i.succAbove j)

theorem splitCoord_apply (i : Fin (m + 1)) (x : Rn (m + 1)) :
    splitCoord i x = (x i, projCoord i x) := rfl

theorem projCoord_splitCoord_symm (i : Fin (m + 1)) (t : ℝ) (z : Fin m → ℝ) :
    projCoord i ((splitCoord i).symm (t, z)) = z := by
  have := (splitCoord i).apply_symm_apply (t, z)
  rw [splitCoord_apply] at this
  exact (Prod.ext_iff.1 this).2

theorem measurePreserving_splitCoord (i : Fin (m + 1)) :
    MeasurePreserving (splitCoord i) volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).trans
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) i)

/-- Translation along `eᵢ` in split coordinates. -/
theorem splitCoord_add_smul_single (i : Fin (m + 1)) (x : Rn (m + 1)) (s : ℝ) :
    splitCoord i (x + s • EuclideanSpace.single i 1) =
      ((splitCoord i x).1 + s, (splitCoord i x).2) := by
  simp only [splitCoord_apply]
  refine Prod.ext (by simp) (funext fun j => ?_)
  simp [projCoord, Fin.succAbove_ne i j]

/-- The points of the line `{P_i = z}` are `(splitCoord i).symm (0, z) + t eᵢ`. -/
theorem splitCoord_symm_eq_add_smul (i : Fin (m + 1)) (t : ℝ) (z : Fin m → ℝ) :
    (splitCoord i).symm (t, z) =
      (splitCoord i).symm (0, z) + t • EuclideanSpace.single i 1 := by
  apply (splitCoord i).injective
  rw [splitCoord_add_smul_single, MeasurableEquiv.apply_symm_apply,
    MeasurableEquiv.apply_symm_apply]
  simp

theorem lipschitzWith_projCoord (i : Fin (m + 1)) : LipschitzWith 1 (projCoord i) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have := PiLp.norm_apply_le (x - y) (i.succAbove j)
  simpa [projCoord] using this

theorem norm_le_abs_add_mul_norm_projCoord (i : Fin (m + 1)) (x : Rn (m + 1)) :
    ‖x‖ ≤ |x i| + m * ‖projCoord i x‖ := by
  have hx : x = ∑ k, x k • EuclideanSpace.single k (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  have h1 : ‖x‖ ≤ ∑ k, |x k| := by
    conv_lhs => rw [hx]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    simp [norm_smul]
  refine h1.trans ?_
  rw [Fin.sum_univ_succAbove _ i]
  gcongr
  calc ∑ j : Fin m, |x (i.succAbove j)| ≤ ∑ _j : Fin m, ‖projCoord i x‖ :=
        Finset.sum_le_sum fun j _ => by
          have := norm_le_pi_norm (projCoord i x) j
          simpa [projCoord] using this
    _ = m * ‖projCoord i x‖ := by simp

/-- **Step 1** (projection). If `ℋ^m(S) = 0` in `ℝ^{m+1}`, then `ℒ^m(P_i(S)) = 0`. -/
theorem volume_projCoord_image_eq_zero (i : Fin (m + 1)) {S : Set (Rn (m + 1))}
    (hS : hausdorffN (m + 1) m S = 0) : volume (projCoord i '' S) = 0 := by
  rw [GMT.hausdorffN_eq_zero_iff] at hS
  have h := (lipschitzWith_projCoord i).hausdorffMeasure_image_le (d := (m : ℝ))
    (Nat.cast_nonneg m) S
  rw [hS, mul_zero] at h
  have hvol : (volume : Measure (Fin m → ℝ)) = μH[(m : ℝ)] := by
    rw [← hausdorffMeasure_pi_real, Fintype.card_fin]
  rw [hvol]
  exact le_antisymm h bot_le

/-- **Step 4** (Fubini along lines parallel to `eᵢ`). Let `g ∈ C¹_c(ℝ^{m+1})` and `F` measurable.
If for a.e. `z ∈ ℝ^m` the line `{P_i = z}` meets `tsupport g` either only inside `F` or only
outside `F`, then `∫_F ∂ᵢ g = 0`. -/
theorem setIntegral_fderiv_single_eq_zero (i : Fin (m + 1)) {F : Set (Rn (m + 1))}
    (hF : MeasurableSet F) {g : Rn (m + 1) → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (hline : ∀ᵐ z ∂(volume : Measure (Fin m → ℝ)),
      (∀ t, (splitCoord i).symm (t, z) ∈ tsupport g → (splitCoord i).symm (t, z) ∈ F) ∨
      (∀ t, (splitCoord i).symm (t, z) ∈ tsupport g → (splitCoord i).symm (t, z) ∉ F)) :
    ∫ x in F, fderiv ℝ g x (EuclideanSpace.single i 1) = 0 := by
  have : ContinuousSMul ℝ (Rn (m + 1)) := IsBoundedSMul.continuousSMul
  set e : Rn (m + 1) := EuclideanSpace.single i 1
  set L := (splitCoord i).symm
  set h : Rn (m + 1) → ℝ := fun x => fderiv ℝ g x e
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hhc : Continuous h := (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hhs : HasCompactSupport h :=
    hgc.fderiv ℝ |>.comp_left (g := fun T : Rn (m + 1) →L[ℝ] ℝ => T e) (by simp)
  have hhi : Integrable h := hhc.integrable_of_hasCompactSupport hhs
  have hh0 : ∀ x, x ∉ tsupport g → h x = 0 := fun x hx => by
    simp only [h]
    rw [image_eq_zero_of_notMem_tsupport (fun hx' => hx (tsupport_fderiv_subset ℝ hx'))]
    rfl
  -- transport to split coordinates and apply Fubini (line integrals first)
  have hL : MeasurePreserving L volume volume := (measurePreserving_splitCoord i).symm
  rw [← integral_indicator hF]
  rw [← hL.integral_comp' (F.indicator h)]
  have hint : Integrable (fun p => F.indicator h (L p)) (volume : Measure (ℝ × (Fin m → ℝ))) :=
    (hL.integrable_comp_emb L.measurableEmbedding).2 (hhi.indicator hF)
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hline] with z hz
  rcases hz with hin | hout
  · -- the integrand is `∂ₜ g(L(t, z))`
    have hfun : (fun t => F.indicator h (L (t, z))) = fun t => h (L (t, z)) := by
      funext t
      by_cases ht : L (t, z) ∈ tsupport g
      · exact indicator_of_mem (hin t ht) _
      · rw [hh0 _ ht]
        exact indicator_apply_eq_zero.2 fun _ => hh0 _ ht
    simp only [Pi.zero_apply, hfun]
    have hline_eq : ∀ t, L (t, z) = L (0, z) + t • e := fun t =>
      splitCoord_symm_eq_add_smul i t z
    have hderiv : ∀ t, HasDerivAt (fun t => g (L (t, z))) (h (L (t, z))) t := by
      intro t
      have hlin : HasDerivAt (fun t : ℝ => L (0, z) + t • e) e t := by
        simpa using ((hasDerivAt_id t).smul_const e).const_add (L (0, z))
      have := (hgd (L (0, z) + t • e)).hasFDerivAt.comp_hasDerivAt t hlin
      simp only [Function.comp_def, ← hline_eq] at this
      exact this
    -- the line `t ↦ L(t, z)` is an isometric embedding, so both functions have compact support
    have hiso : Isometry fun t : ℝ => L (t, z) := by
      refine Isometry.of_dist_eq fun t s => ?_
      rw [hline_eq t, hline_eq s, dist_add_left, dist_eq_norm, dist_eq_norm, ← sub_smul,
        norm_smul]
      simp [e]
    have hcemb := hiso.isClosedEmbedding
    have hgi : Integrable (fun t => g (L (t, z))) :=
      (hg.continuous.comp hiso.continuous).integrable_of_hasCompactSupport
        (hgc.comp_isClosedEmbedding hcemb)
    have hhi' : Integrable (fun t => h (L (t, z))) :=
      (hhc.comp hiso.continuous).integrable_of_hasCompactSupport
        (hhs.comp_isClosedEmbedding hcemb)
    exact integral_eq_zero_of_hasDerivAt_of_integrable hderiv hhi' hgi
  · have hfun : (fun t => F.indicator h (L (t, z))) = fun _ => 0 := by
      funext t
      by_cases ht : L (t, z) ∈ tsupport g
      · exact indicator_of_notMem (hout t ht) _
      · exact indicator_apply_eq_zero.2 fun _ => hh0 _ ht
    simp [hfun]

end GMTFoundations
