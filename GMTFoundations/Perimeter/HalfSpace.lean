/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.Mollify
public import GMTFoundations.GMT.Basic
import GMTFoundations.GMT.SphereMeasure
import GMTFoundations.GMT.HausdorffLebesgue
import GMTFoundations.BV.TotalVariation
import GMTFoundations.BV.Compactness
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.Hom
import Mathlib.Data.Real.StarOrdered
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Half-spaces

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

## Main results

* `isGaussGreenPair_halfSpace`: `H⁻ = {⟪y, e⟫ ≤ 0}` has the Gauss–Green pair
  `(ℋ^{n-1}⌊e^⊥, e)` on `ℝⁿ`; `totalVariationOn_halfSpace_ball`: `TV(H⁻; B_r(p)) = ω_{n-1} r^{n-1}`
  for `p ∈ e^⊥`, `n ≥ 2`.
* `ae_eq_halfSpace_of_isGaussGreenPair` (EG Thm 5.13, Claim #2; used in
  `BlowUpNormal.lean`): if `F` has a
  Gauss–Green pair `(μ, ν)` on `ℝⁿ` whose normal is a.e. a constant unit vector `e`, then `F` is
  a.e. empty, a.e. everything, or a.e. the half-space `{⟪y, e⟫ ≤ γ}` for some `γ`.
* `volume_setOf_inner_eq`: affine hyperplanes are Lebesgue-null.

## Proof of the half-space pair

Rotate `e` to the north pole `e_{m+1}` by a linear isometry `T`
(`exists_linearIsometryEquiv_north`); then `z ↦ (z_{m+1}, z')` is volume preserving
(`measurePreserving_lastHead`) and `ℋ^{n-1}⌊e^⊥` is the image of Lebesgue measure on `ℝ^m` under
`y ↦ T⁻¹(y, 0)` (`map_volume_add_linearIsometry_eq_hausdorffN`). With the smoothed half-space
`g_ε = 1 - σ(⟪·, e⟫/ε)`, `∫ div(g_ε φ) = 0` gives
`∫ g_ε div φ = ∫ ε⁻¹κ(⟪y, e⟫/ε) ⟪φ, e⟫ = ∫_ℝ ε⁻¹κ(t/ε) Φ(t) dt`,
`Φ(t) = ∫_{ℝ^m} ⟪φ(T⁻¹(y', t)), e⟫ dy'`, which is continuous; let `ε → 0`. No coordinate
expansion of the divergence is needed.

## Proof of the characterization

Mollify: `u_k = χ_F ⋆ ρ_k`. By `fderiv_mollify_indicator_apply`,
`Du_k(x) v = -⟪v, e⟫ ∫ ρ_k(x - y) dμ(y)`. So `u_k` is constant along directions orthogonal to `e`
and nonincreasing along `e`; hence `u_k(y) ≥ u_k(y')` when `⟪y, e⟫ ≤ ⟪y', e⟫`. Let `G` be the
full-measure set where `u_k → χ_F`. For `y, y' ∈ G` with `⟪y, e⟫ ≤ ⟪y', e⟫` and `y' ∈ F`, also
`y ∈ F`. With `γ = sup {⟪y, e⟫ : y ∈ F ∩ G}` this gives `F = {⟪·, e⟫ ≤ γ}` off `Gᶜ` and the null
hyperplane `{⟪·, e⟫ = γ}`. No function of one variable has to be extracted.
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

public section

namespace GMTFoundations

variable {n : ℕ}

/-- Affine hyperplanes `{⟪y, e⟫ = γ}`, `e ≠ 0`, are Lebesgue-null. -/
theorem volume_setOf_inner_eq {e : Rn n} (he : e ≠ 0) (γ : ℝ) :
    volume {y : Rn n | ⟪y, e⟫ = γ} = 0 := by
  have h0 : volume (GMT.hyperplane e) = 0 := by
    rw [GMT.hyperplane_eq_orthogonal]
    refine Measure.addHaar_submodule volume _ fun htop ↦ ?_
    have : e ∈ ((ℝ ∙ e)ᗮ : Submodule ℝ (Rn n)) := by rw [htop]; exact Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at this
    exact he (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))
  have hset : {y : Rn n | ⟪y, e⟫ = γ} =
      (fun y ↦ y + -((γ / ‖e‖ ^ 2) • e)) ⁻¹' GMT.hyperplane e := by
    ext y
    have : ‖e‖ ^ 2 ≠ 0 := by positivity
    simp only [mem_setOf_eq, mem_preimage, GMT.mem_hyperplane, inner_add_left, inner_neg_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h; field_simp at h; linarith
  rw [hset, measure_preimage_add_right, h0]

section Characterization

variable {F : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- For a pair on `ℝⁿ` with a.e. constant normal `e`:
`D(χ_F ⋆ ρ)(x) v = -⟪v, e⟫ ∫ ρ(x - y) dμ(y)`. -/
theorem fderiv_mollify_indicator_apply_of_normal_eq (h : IsGaussGreenPair univ F μ ν)
    (hF : MeasurableSet F) {e : Rn n} (hν : ∀ᵐ y ∂μ, ν y = e) (ρ : ContDiffBump (0 : Rn n))
    (x v : Rn n) :
    fderiv ℝ (mollify ρ (F.indicator 1)) x v = -(⟪v, e⟫ * ∫ y, ρ.normed volume (x - y) ∂μ) := by
  rw [fderiv_mollify_indicator_apply h hF ρ (subset_univ _) v, ← integral_const_mul]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hν] with y hy
  rw [hy]
  ring

/-- **Monotonicity of the mollified indicator** for a pair with a.e. constant unit normal `e`:
`⟪y, e⟫ ≤ ⟪y', e⟫` implies `(χ_F ⋆ ρ)(y') ≤ (χ_F ⋆ ρ)(y)`. -/
theorem mollify_indicator_antitone_inner (h : IsGaussGreenPair univ F μ ν)
    (hF : MeasurableSet F) {e : Rn n} (he : ‖e‖ = 1) (hν : ∀ᵐ y ∂μ, ν y = e)
    (ρ : ContDiffBump (0 : Rn n)) {y y' : Rn n} (hyy' : ⟪y, e⟫ ≤ ⟪y', e⟫) :
    mollify ρ (F.indicator 1) y' ≤ mollify ρ (F.indicator 1) y := by
  haveI : ContinuousSMul ℝ (Rn n) := inferInstance
  set u := mollify ρ (F.indicator 1) with hu_def
  have hli : LocallyIntegrable (F.indicator (1 : Rn n → ℝ)) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hF
  have hdiff : Differentiable ℝ u := (contDiff_mollify ρ hli).differentiable (by simp)
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  -- `u` only depends on `⟪z, e⟫`
  have hproj : ∀ z, u z = u (⟪z, e⟫ • e) := by
    intro z
    set w := z - ⟪z, e⟫ • e with hw
    have hwe : ⟪w, e⟫ = 0 := by
      rw [hw, inner_sub_left, real_inner_smul_left, hee, mul_one, sub_self]
    set g : ℝ → ℝ := fun t ↦ u (⟪z, e⟫ • e + t • w) with hg
    have hgd : ∀ t, HasDerivAt g (fderiv ℝ u (⟪z, e⟫ • e + t • w) w) t := fun t ↦ by
      have h1 : HasDerivAt (fun t : ℝ ↦ ⟪z, e⟫ • e + t • w) w t := by
        simpa using ((hasDerivAt_id t).smul_const w).const_add (⟪z, e⟫ • e)
      exact (hdiff _).hasFDerivAt.comp_hasDerivAt t h1
    have hconst := is_const_of_deriv_eq_zero (f := g) (fun t ↦ (hgd t).differentiableAt)
      (fun t ↦ by
        rw [(hgd t).deriv, hu_def, fderiv_mollify_indicator_apply_of_normal_eq h hF hν, hwe]
        ring) 1 0
    simp only [hg, one_smul, zero_smul, add_zero] at hconst
    rw [← hconst, hw, add_sub_cancel]
  -- `t ↦ u (t e)` is antitone
  have hanti : Antitone fun t : ℝ ↦ u (t • e) := by
    have hgd : ∀ t, HasDerivAt (fun t : ℝ ↦ u (t • e)) (fderiv ℝ u (t • e) e) t := fun t ↦ by
      have h1 : HasDerivAt (fun t : ℝ ↦ t • e) e t := by
        simpa using (hasDerivAt_id t).smul_const e
      exact (hdiff _).hasFDerivAt.comp_hasDerivAt t h1
    refine antitone_of_deriv_nonpos (fun t ↦ (hgd t).differentiableAt) fun t ↦ ?_
    rw [(hgd t).deriv, hu_def, fderiv_mollify_indicator_apply_of_normal_eq h hF hν, hee, one_mul,
      neg_nonpos]
    exact integral_nonneg fun _ ↦ ρ.nonneg_normed _
  rw [hproj y, hproj y']
  exact hanti hyy'

/-- **Half-space characterization** (EG Thm 5.13, Claim #2). If `F` is measurable and has a
Gauss–Green pair `(μ, ν)` on `ℝⁿ` with `ν = e` `μ`-a.e. for a unit vector `e`, then `F` is a.e.
empty, a.e. all of `ℝⁿ`, or a.e. equal to a half-space `{⟪y, e⟫ ≤ γ}`. -/
theorem ae_eq_halfSpace_of_isGaussGreenPair (h : IsGaussGreenPair univ F μ ν)
    (hF : MeasurableSet F) {e : Rn n} (he : ‖e‖ = 1) (hν : ∀ᵐ y ∂μ, ν y = e) :
    F =ᵐ[volume] (∅ : Set (Rn n)) ∨ F =ᵐ[volume] (univ : Set (Rn n)) ∨
      ∃ γ : ℝ, F =ᵐ[volume] {y : Rn n | ⟪y, e⟫ ≤ γ} := by
  set u : ℕ → Rn n → ℝ := fun k ↦ mollify (mollifierBump k) (F.indicator 1) with hu_def
  have hli : LocallyIntegrable (F.indicator (1 : Rn n → ℝ)) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hF
  have hconv : ∀ᵐ y, Tendsto (fun k ↦ u k y) atTop (𝓝 (F.indicator 1 y)) :=
    ae_tendsto_mollify tendsto_mollifierBump_rOut
      (Eventually.of_forall fun k ↦ mollifierBump_rOut_le k) hli
  set G := {y : Rn n | Tendsto (fun k ↦ u k y) atTop (𝓝 (F.indicator 1 y))} with hG_def
  have hGc : volume Gᶜ = 0 := hconv
  -- downward closedness of `F` inside `G`
  have key : ∀ y ∈ G, ∀ y' ∈ G, y' ∈ F → ⟪y, e⟫ ≤ ⟪y', e⟫ → y ∈ F := by
    intro y hy y' hy' hy'F hyy'
    have h1 : F.indicator (1 : Rn n → ℝ) y' ≤ F.indicator 1 y :=
      le_of_tendsto_of_tendsto' hy' hy fun k ↦
        mollify_indicator_antitone_inner h hF he hν (mollifierBump k) hyy'
    rw [indicator_of_mem hy'F, Pi.one_apply] at h1
    by_contra hyF
    rw [indicator_of_notMem hyF] at h1
    linarith
  set S := (fun y : Rn n ↦ ⟪y, e⟫) '' (F ∩ G) with hS_def
  rcases (F ∩ G).eq_empty_or_nonempty with hFG | hFG
  · left
    refine ae_eq_empty.2 (measure_mono_null (fun y hyF ↦ ?_) hGc)
    intro hyG
    exact (eq_empty_iff_forall_notMem.1 hFG) y ⟨hyF, hyG⟩
  by_cases hbdd : BddAbove S
  · right; right
    refine ⟨sSup S, eventuallyEq_set.2 ?_⟩
    have he0 : e ≠ 0 := fun h0 ↦ by rw [h0, norm_zero] at he; exact zero_ne_one he
    have hplane : ∀ᵐ y, ⟪y, e⟫ ≠ sSup S :=
      measure_eq_zero_iff_ae_notMem.1 (volume_setOf_inner_eq he0 (sSup S))
    filter_upwards [hconv, hplane] with y hyG hyγ
    constructor
    · intro hyF
      exact le_csSup hbdd ⟨y, ⟨hyF, hyG⟩, rfl⟩
    · intro hle
      obtain ⟨s, ⟨y', hy', rfl⟩, hs⟩ :=
        exists_lt_of_lt_csSup (hFG.image _) (lt_of_le_of_ne hle hyγ)
      exact key y hyG y' hy'.2 hy'.1 hs.le
  · right; left
    refine ae_eq_univ.2 (measure_mono_null (fun y hyF ↦ ?_) hGc)
    intro hyG
    rw [not_bddAbove_iff] at hbdd
    obtain ⟨s, ⟨y', hy', rfl⟩, hs⟩ := hbdd ⟪y, e⟫
    exact hyF (key y hyG y' hy'.2 hy'.1 hs.le)

end Characterization

/-! ### The Gauss–Green pair of a half-space -/

section Pair

open GMT GMT.SphereMeasure

variable {m : ℕ}

/-- `y ↦ (y, 0)` as a linear isometry `ℝ^m → ℝ^{m+1}`. -/
private noncomputable def snocZero (m : ℕ) : Rn m →ₗᵢ[ℝ] Rn (m + 1) where
  toFun y := snocCoords y 0
  map_add' y z := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [snocCoords]
  map_smul' c y := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [snocCoords]
  norm_map' y := by
    have := norm_sq_snocCoords y 0
    rw [zero_pow two_ne_zero, add_zero] at this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

private theorem snocZero_apply (y : Rn m) : snocZero m y = snocCoords y 0 := rfl

private theorem snocCoords_eq_add (y : Rn m) (t : ℝ) :
    snocCoords y t = snocZero m y + t • north := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [snocZero_apply, north, snocCoords]

private theorem inner_north (z : Rn (m + 1)) : ⟪z, north⟫ = z (Fin.last m) := by
  rw [north, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_castSucc]
  simp [snocCoords]

/-- `z ↦ (z_{m+1}, z')` as a measurable equivalence `ℝ^{m+1} ≃ ℝ × ℝ^m`. -/
private noncomputable def lastHeadEquiv (m : ℕ) : Rn (m + 1) ≃ᵐ ℝ × Rn m :=
  (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) (Fin.last m)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin m → ℝ))))

private theorem lastHeadEquiv_apply (z : Rn (m + 1)) :
    lastHeadEquiv m z = (z (Fin.last m), headCoords z) := by
  refine Prod.ext rfl ?_
  ext i
  simp [lastHeadEquiv, headCoords, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodCongr,
    Fin.init]

private theorem lastHeadEquiv_symm_apply (t : ℝ) (y : Rn m) :
    (lastHeadEquiv m).symm (t, y) = snocCoords y t := by
  apply (lastHeadEquiv m).injective
  rw [MeasurableEquiv.apply_symm_apply, lastHeadEquiv_apply]
  simp

private theorem measurePreserving_lastHeadEquiv :
    MeasurePreserving (lastHeadEquiv m) := by
  convert (measurePreserving_lastHead (m := m)) using 1
  funext z
  exact lastHeadEquiv_apply z

/-- **Fubini across `e^⊥`.** For a linear isometry `T` with `T e = e_{m+1}`:
`∫ K(⟪y, e⟫) f(y) dy = ∫_ℝ K(t) ∫_{ℝ^m} f(T⁻¹(y', t)) dy' dt`. -/
private theorem integral_comp_inner_mul_eq {e : Rn (m + 1)}
    (T : Rn (m + 1) ≃ₗᵢ[ℝ] Rn (m + 1)) (hT : T e = north) {K : ℝ → ℝ}
    {f : Rn (m + 1) → ℝ} (hint : Integrable fun y ↦ K ⟪y, e⟫ * f y) :
    ∫ y, K ⟪y, e⟫ * f y = ∫ t, K t * ∫ y', f (T.symm (snocCoords y' t)) := by
  set G : Rn (m + 1) → ℝ := fun y ↦ K ⟪y, e⟫ * f y with hG
  have h1 : ∫ y, G y = ∫ z, G (T.symm z) :=
    ((T.symm.measurePreserving).integral_comp T.symm.toHomeomorph.measurableEmbedding G).symm
  have hGT : ∀ z, G (T.symm z) = K (z (Fin.last m)) * f (T.symm z) := fun z ↦ by
    have : ⟪T.symm z, e⟫ = ⟪z, north⟫ := by
      rw [← hT, ← T.inner_map_map, T.apply_symm_apply]
    rw [hG]
    simp only [this, inner_north]
  have hint' : Integrable fun z ↦ G (T.symm z) :=
    ((T.symm.measurePreserving).integrable_comp_emb
      T.symm.toHomeomorph.measurableEmbedding).2 hint
  set H : ℝ × Rn m → ℝ := fun p ↦ G (T.symm ((lastHeadEquiv m).symm p)) with hH
  have h2 : ∫ z, G (T.symm z) = ∫ p, H p := by
    rw [← (measurePreserving_lastHeadEquiv (m := m)).integral_comp' (g := H)]
    congr 1
    funext z
    simp [hH]
  have hHint : Integrable H volume := by
    have := (MeasurePreserving.symm (lastHeadEquiv m)
      (measurePreserving_lastHeadEquiv (m := m))).integrable_comp_emb
      (lastHeadEquiv m).symm.measurableEmbedding (g := fun z ↦ G (T.symm z))
    exact this.2 hint'
  rw [Measure.volume_eq_prod] at hHint
  rw [h1, h2, Measure.volume_eq_prod, integral_prod H hHint]
  congr 1
  funext t
  rw [← integral_const_mul]
  congr 1
  funext y'
  simp only [hH, lastHeadEquiv_symm_apply]
  rw [hGT, snocCoords_last]

/-- The linear isometry `L = T⁻¹ ∘ (· , 0) : ℝ^m → ℝ^{m+1}` parametrizes `e^⊥`. -/
private theorem range_symm_snocZero {e : Rn (m + 1)} (T : Rn (m + 1) ≃ₗᵢ[ℝ] Rn (m + 1))
    (hT : T e = north) :
    range (fun y ↦ (0 : Rn (m + 1)) + (T.symm.toLinearIsometry.comp (snocZero m)) y) =
      hyperplane e := by
  ext z
  simp only [zero_add, LinearIsometry.coe_comp, comp_apply, mem_range, mem_hyperplane,
    LinearIsometryEquiv.coe_toLinearIsometry, snocZero_apply]
  have hz : ⟪z, e⟫ = (T z) (Fin.last m) := by
    rw [← inner_north, ← hT, T.inner_map_map]
  rw [hz]
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro h
    refine ⟨headCoords (T z), ?_⟩
    apply T.injective
    rw [T.apply_symm_apply, ← h, snocCoords_headCoords]

/-- `(ℋ^{n-1}⌊e^⊥)(K) < ∞` for bounded `K`. -/
private theorem hausdorffN_hyperplane_lt_top {e : Rn (m + 1)}
    (T : Rn (m + 1) ≃ₗᵢ[ℝ] Rn (m + 1)) (hT : T e = north) {K : Set (Rn (m + 1))}
    (hK : Bornology.IsBounded K) : (hausdorffN (m + 1) m).restrict (hyperplane e) K < ⊤ := by
  set L := T.symm.toLinearIsometry.comp (snocZero m)
  have hmap := GMT.map_volume_add_linearIsometry_eq_hausdorffN L 0
  rw [range_symm_snocZero T hT] at hmap
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  refine (measure_mono hR).trans_lt ?_
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_closedBall]
  refine (measure_mono fun y hy ↦ ?_).trans_lt (measure_closedBall_lt_top (x := (0 : Rn m))
    (r := R))
  simp only [mem_preimage, zero_add, mem_closedBall, dist_zero_right] at hy ⊢
  rwa [L.norm_map] at hy

/-- The half-space pair in `ℝ^{m+1}`. -/
private theorem isGaussGreenPair_halfSpace_aux {e : Rn (m + 1)} (he : ‖e‖ = 1) :
    IsGaussGreenPair univ {y | ⟪y, e⟫ ≤ 0} ((hausdorffN (m + 1) m).restrict (hyperplane e))
      (fun _ ↦ e) := by
  haveI : ContinuousSMul ℝ (Rn (m + 1)) := inferInstance
  obtain ⟨T, hT⟩ := exists_linearIsometryEquiv_north he
  set L := T.symm.toLinearIsometry.comp (snocZero m) with hL_def
  have hmap := GMT.map_volume_add_linearIsometry_eq_hausdorffN L 0
  rw [range_symm_snocZero T hT] at hmap
  refine ⟨by simp, fun K hK _ ↦ hausdorffN_hyperplane_lt_top T hT hK.isBounded, measurable_const,
    ae_of_all _ fun _ ↦ he, fun φ hφ ↦ ?_⟩
  obtain ⟨hφs, hφc, -⟩ := hφ
  have hφ1 : ContDiff ℝ 1 φ := hφs.of_le (by simp)
  set H := {y : Rn (m + 1) | ⟪y, e⟫ ≤ 0} with hH_def
  -- right-hand side: an integral over `ℝ^m`
  have hRHS : ∫ y, ⟪φ y, e⟫ ∂((hausdorffN (m + 1) m).restrict (hyperplane e)) =
      ∫ y', ⟪φ (T.symm (snocCoords y' 0)), e⟫ := by
    rw [← hmap, integral_map (by fun_prop)
      (hφ1.continuous.inner continuous_const).aestronglyMeasurable]
    congr 1
    funext x
    simp [hL_def, snocZero_apply]
  clear hL_def
  -- `∫ div ψ = 0` for `ψ ∈ C¹_c` (from the Gauss–Green pair of `∅` on `ℝⁿ`)
  have h0 : ∀ ψ : Rn (m + 1) → Rn (m + 1), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      ∫ y, divergence ψ y = 0 := by
    intro ψ hψ hψc
    have hempty : IsGaussGreenPair (univ : Set (Rn (m + 1))) ∅ 0 (fun _ ↦ 0) :=
      ⟨by simp, fun _ _ _ ↦ by simp, measurable_const, by simp, fun _ _ ↦ by simp⟩
    have := (hempty.compl MeasurableSet.empty).integral_divergence_of_contDiff isOpen_univ hψ hψc
      (subset_univ _)
    simpa using this
  -- the smoothed half-space `g_ε(y) = 1 - σ(⟪y, e⟫/ε)`
  set g : ℝ → Rn (m + 1) → ℝ := fun ε y ↦ 1 - Real.smoothTransition (⟪y, e⟫ / ε) with hg_def
  have hgd : ∀ ε, 0 < ε → ∀ y, HasFDerivAt (g ε)
      (-(transitionKernel (⟪y, e⟫ / ε) • (ε⁻¹ • innerSL ℝ e))) y := by
    intro ε hε y
    have hσ := hasDerivAt_smoothTransition (⟪y, e⟫ / ε)
    have hin : HasFDerivAt (fun z : Rn (m + 1) ↦ ⟪z, e⟫ / ε) (ε⁻¹ • innerSL ℝ e) y := by
      have := ((innerSL ℝ e).hasFDerivAt (x := y)).const_mul ε⁻¹
      convert this using 1
      funext z
      rw [innerSL_apply_apply, real_inner_comm, div_eq_inv_mul]
    have := (hasFDerivAt_const (1 : ℝ) y).sub (hσ.comp_hasFDerivAt y hin)
    rw [zero_sub] at this
    exact this
  have hgc : ∀ ε, 0 < ε → ContDiff ℝ 1 (g ε) := fun ε _ ↦
    contDiff_const.sub ((Real.smoothTransition.contDiff (n := 1)).comp
      ((contDiff_id.inner ℝ contDiff_const).div_const ε))
  -- for each `ε`: `∫ g_ε div φ = ∫ ε⁻¹ κ(⟪y, e⟫/ε) ⟪φ, e⟫`
  have hid : ∀ ε, 0 < ε → ∫ y, g ε y * divergence φ y =
      ∫ y, scaledKernel 0 ε ⟪y, e⟫ * ⟪φ y, e⟫ := by
    intro ε hε
    have hΨ : ContDiff ℝ 1 fun y ↦ g ε y • φ y := (hgc ε hε).smul hφ1
    have hΨc : HasCompactSupport fun y ↦ g ε y • φ y :=
      HasCompactSupport.of_support_subset_isCompact hφc fun y hy ↦
        subset_tsupport φ fun h0 ↦ hy (by simp only [h0, smul_zero])
    have hdiv : ∀ y, divergence (fun y ↦ g ε y • φ y) y =
        g ε y * divergence φ y + fderiv ℝ (g ε) y (φ y) := fun y ↦
      divergence_smul ((hgd ε hε y).differentiableAt) (hφ1.differentiable one_ne_zero y)
    have hderiv : ∀ y, fderiv ℝ (g ε) y (φ y) = -(scaledKernel 0 ε ⟪y, e⟫ * ⟪φ y, e⟫) :=
      fun y ↦ by
        rw [(hgd ε hε y).fderiv]
        simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
          innerSL_apply_apply, smul_eq_mul, scaledKernel, sub_zero]
        rw [real_inner_comm (φ y) e]
        ring
    have hdivi : Integrable (divergence φ) :=
      (continuous_divergence hφ1).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hφc
          ((subset_tsupport _).trans (tsupport_divergence_subset φ)))
    have ha : Integrable fun y ↦ g ε y * divergence φ y :=
      ((hgc ε hε).continuous.mul (continuous_divergence hφ1)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hφc fun y hy ↦
          tsupport_divergence_subset φ (subset_tsupport _ (right_ne_zero_of_mul hy)))
    have hb : Integrable fun y ↦ fderiv ℝ (g ε) y (φ y) :=
      (((hgc ε hε).continuous_fderiv one_ne_zero).clm_apply hφ1.continuous
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact hφc
          fun y hy ↦ subset_tsupport φ fun h0 ↦ hy (by simp only [h0, map_zero]))
    have h00 := h0 _ hΨ hΨc
    simp_rw [hdiv] at h00
    rw [integral_add ha hb] at h00
    simp_rw [hderiv, integral_neg] at h00
    linarith
  -- the sequence `ε_k = 1/(k+1)`
  set ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hε_def
  have hεpos : ∀ k, 0 < ε k := fun k ↦ by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hε0' : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall hεpos⟩
  -- left-hand side limit
  have hdivi : Integrable (divergence φ) :=
    (continuous_divergence hφ1).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hφc
        ((subset_tsupport _).trans (tsupport_divergence_subset φ)))
  have hg01 : ∀ ε' y, 0 ≤ g ε' y ∧ g ε' y ≤ 1 := fun ε' y ↦
    ⟨sub_nonneg.2 (Real.smoothTransition.le_one _), sub_le_self _ (Real.smoothTransition.nonneg _)⟩
  have hglim : ∀ y, Tendsto (fun k ↦ g (ε k) y) atTop (𝓝 (H.indicator 1 y)) := by
    intro y
    by_cases hy : ⟪y, e⟫ ≤ 0
    · rw [indicator_of_mem (show y ∈ H from hy), Pi.one_apply]
      refine tendsto_const_nhds.congr fun k ↦ ?_
      simp only [hg_def]
      rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg hy (hεpos k).le), sub_zero]
    · rw [indicator_of_notMem (show y ∉ H from hy)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_order.1 hε0).2 ⟪y, e⟫ (by linarith)] with k hk
      simp only [hg_def]
      rw [Real.smoothTransition.one_of_one_le, sub_self]
      rw [le_div_iff₀ (hεpos k), one_mul]
      exact hk.le
  have hL : Tendsto (fun k ↦ ∫ y, g (ε k) y * divergence φ y) atTop
      (𝓝 (∫ y in H, divergence φ y)) := by
    have := tendsto_integral_of_dominated_convergence (fun y ↦ ‖divergence φ y‖)
      (fun k ↦ ((hgc (ε k) (hεpos k)).continuous.mul
        (continuous_divergence hφ1)).aestronglyMeasurable) hdivi.norm
      (fun k ↦ Eventually.of_forall fun y ↦ by
        change ‖g (ε k) y * divergence φ y‖ ≤ ‖divergence φ y‖
        rw [norm_mul, Real.norm_of_nonneg (hg01 _ y).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (hg01 _ y).2)
      (Eventually.of_forall fun y ↦ (hglim y).mul_const (divergence φ y))
    have hHm : MeasurableSet H := measurableSet_le (continuous_id.inner continuous_const).measurable
      measurable_const
    have e1 : ∫ y, H.indicator (divergence φ) y = ∫ y, H.indicator 1 y * divergence φ y :=
      integral_congr_ae (Eventually.of_forall fun y ↦ by by_cases hy : y ∈ H <;> simp [hy])
    rw [← integral_indicator hHm, e1]
    exact this
  -- right-hand side: Fubini across `e^⊥` and the kernel limit
  set f : Rn (m + 1) → ℝ := fun z ↦ ⟪φ z, e⟫ with hf_def
  have hfc : Continuous f := hφ1.continuous.inner continuous_const
  set Φ : ℝ → ℝ := fun t ↦ ∫ y', f (T.symm (snocCoords y' t)) with hΦ_def
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  have hΦeq : Φ = fun t ↦
      ∫ y' in closedBall (0 : Rn m) R, f (T.symm (snocZero m y' + t • north)) := by
    funext t
    rw [hΦ_def, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp_rw [snocCoords_eq_add]
    · intro y' hy'
      rw [mem_closedBall, dist_zero_right, not_le] at hy'
      have hnorm : ‖y'‖ ≤ ‖snocZero m y' + t • north‖ := by
        rw [← snocCoords_eq_add]
        have := norm_sq_snocCoords y' t
        exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
          (by rw [this]; exact le_add_of_nonneg_right (sq_nonneg t))
      have hz : T.symm (snocZero m y' + t • north) ∉ tsupport φ := fun hmem ↦ by
        have := mem_closedBall_zero_iff.1 (hR hmem)
        rw [T.symm.norm_map] at this
        linarith
      change ⟪φ (T.symm (snocZero m y' + t • north)), e⟫ = 0
      rw [image_eq_zero_of_notMem_tsupport hz, inner_zero_left]
  have hΦc : Continuous Φ := by
    rw [hΦeq]
    have hcont : Continuous fun p : ℝ × Rn m ↦ f (T.symm (snocZero m p.2 + p.1 • north)) :=
      hfc.comp (T.symm.continuous.comp (((snocZero m).continuous.comp continuous_snd).add
        (continuous_fst.smul continuous_const)))
    exact continuous_parametric_integral_of_continuous
      (f := fun t y' ↦ f (T.symm (snocZero m y' + t • north))) hcont (isCompact_closedBall _ _)
  have hR' : ∀ k, ∫ y, scaledKernel 0 (ε k) ⟪y, e⟫ * ⟪φ y, e⟫ =
      ∫ t, scaledKernel 0 (ε k) t * Φ t := fun k ↦ by
    refine integral_comp_inner_mul_eq T hT ?_
    refine ((((continuous_scaledKernel 0 (ε k)).comp (continuous_id.inner continuous_const)).mul
      hfc)).integrable_of_hasCompactSupport ?_
    exact HasCompactSupport.of_support_subset_isCompact hφc fun y hy ↦
      subset_tsupport φ fun h0 ↦ hy (by simp [hf_def, h0])
  have hR : Tendsto (fun k ↦ ∫ y, scaledKernel 0 (ε k) ⟪y, e⟫ * ⟪φ y, e⟫) atTop (𝓝 (Φ 0)) := by
    simp_rw [hR']
    exact (tendsto_integral_scaledKernel_mul_of_continuous hΦc 0).comp hε0'
  have hlim := tendsto_nhds_unique hL (hR.congr fun k ↦ (hid (ε k) (hεpos k)).symm)
  rw [hlim, hRHS]

/-- **The half-space pair**. For a unit vector `e`, the half-space
`H⁻ = {⟪y, e⟫ ≤ 0}` has the Gauss–Green pair `(ℋ^{n-1}⌊e^⊥, e)` on `ℝⁿ`: its outer normal is `e`
and its perimeter measure is `ℋ^{n-1}` on the hyperplane `e^⊥` (Fubini across `e^⊥` and the 1-D
fundamental theorem of calculus, in smoothed form). -/
theorem isGaussGreenPair_halfSpace [NeZero n] {e : Rn n} (he : ‖e‖ = 1) :
    IsGaussGreenPair univ {y | ⟪y, e⟫ ≤ 0} ((hausdorffN n (n - 1)).restrict (hyperplane e))
      (fun _ ↦ e) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  simpa using isGaussGreenPair_halfSpace_aux he

theorem measurableSet_halfSpace (e : Rn n) : MeasurableSet {y : Rn n | ⟪y, e⟫ ≤ 0} :=
  measurableSet_le (continuous_id.inner continuous_const).measurable measurable_const

/-- **Perimeter of a half-space in a ball**. For `n ≥ 2`, a unit vector `e`, and
`p ∈ e^⊥`: `TV(H⁻; B_r(p)) = ω_{n-1} r^{n-1}`. -/
theorem totalVariationOn_halfSpace_ball (hn : 2 ≤ n) {e : Rn n} (he : ‖e‖ = 1) {p : Rn n}
    (hp : p ∈ hyperplane e) {r : ℝ} (hr : 0 ≤ r) :
    totalVariationOn (ball p r) ({y : Rn n | ⟪y, e⟫ ≤ 0}.indicator 1) =
      ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)) := by
  haveI : NeZero n := ⟨by omega⟩
  have he0 : e ≠ 0 := fun h0 ↦ by rw [h0, norm_zero] at he; exact zero_ne_one he
  rw [(isGaussGreenPair_halfSpace he).totalVariationOn_indicator_eq (measurableSet_halfSpace e)
    isOpen_ball (subset_univ _), Measure.restrict_apply measurableSet_ball, inter_comm,
    hausdorffN_eq_euclideanHausdorffMeasure']
  exact euclideanHausdorffMeasure_hyperplane_inter_ball hn he0 hp hr

end Pair

end GMTFoundations
