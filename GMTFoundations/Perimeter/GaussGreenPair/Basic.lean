/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Statements.Perimeter
public import GMTFoundations.Perimeter.VectorRiesz
public import GMTFoundations.Defs.BV
import GMTFoundations.BV.TotalVariation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Gauss–Green pairs: existence and the total-variation formula

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*,
rev. ed., CRC Press, 2015 (EG).

## Main results

* `exists_isGaussGreenPair_of_integral_divergence_le`: EG Thm 5.1 (structure theorem for
  `BV_loc`) for `f = χ_E`, in the form: a bound on `∫_E div φ` gives a Gauss–Green pair. The
  statement is `GaussGreenPairOfDivergenceBoundStatement` (`Statements/Perimeter.lean`).
* `exists_isGaussGreenPair_of_bound`: a pair from bounds on each compact subset of `U` (used by
  the `BV_loc` form `hasLocallyFinitePerimeter_of_local` in `Perimeter/Local.lean`).
* `IsGaussGreenPair.measure_eq_iSup`: the total-variation formula
  `μ V = sup {∫_E div φ : φ ∈ C^∞_c(V; ℝⁿ), |φ| ≤ 1}` for open `V ⊆ Ω`.

## Sign convention

`IsGaussGreenPair` writes `∫_E div φ = ∫ ⟪φ, ν⟫ dμ`, so `ν` is the **outer** normal.
EG Thm 5.1 writes `∫ f div φ = -∫ φ · σ d‖Df‖` for `f = χ_E`; so our `ν` is EG's `-σ`
(EG's `ν_E := -σ`, the outer normal; remarks after EG Thm 5.1, and Def 5.4). No sign enters the
proofs below: the pair is produced directly in this convention by `exists_rieszPair`.

See `GMTFoundations.Perimeter.GaussGreenPair.API` and
`GMTFoundations.Perimeter.GaussGreenPair.WeightedTV` for uniqueness, restriction, blow-ups, and
the bridge to the duality total variation `weightedTV`.
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### Linearity of `φ ↦ ∫_E div φ` -/

section Divergence

private theorem divergence_add' {φ ψ : Rn n → Rn n} (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ) : divergence (φ + ψ) = divergence φ + divergence ψ := by
  funext x
  simp only [divergence, Pi.add_apply, fderiv_add (hφ x) (hψ x),
    ContinuousLinearMap.toLinearMap_add, map_add]

private theorem divergence_smul' (c : ℝ) {φ : Rn n → Rn n} (hφ : Differentiable ℝ φ) :
    divergence (c • φ) = c • divergence φ := by
  funext x
  simp only [divergence, Pi.smul_apply, fderiv_const_smul (hφ x),
    ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]

/-- Not private: reused in `GaussGreenPair/API.lean`. -/
theorem IsSmoothTestField.differentiable {U : Set (Rn n)} {φ : Rn n → Rn n}
    (hφ : IsSmoothTestField U φ) : Differentiable ℝ φ :=
  hφ.1.differentiable (by simp)

/-- Not private: reused in `GaussGreenPair/API.lean` and `GaussGreenPair/WeightedTV.lean`. -/
theorem IsSmoothTestField.integrable_divergence {U : Set (Rn n)} {φ : Rn n → Rn n}
    (hφ : IsSmoothTestField U φ) : Integrable (divergence φ) :=
  (continuous_divergence (hφ.1.of_le (by simp))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact hφ.2.1
      ((subset_tsupport _).trans (tsupport_divergence_subset φ)))

/-- `φ ↦ ∫_E div φ` is additive over finite sums of smooth test fields. -/
theorem integral_divergence_finsetSum {U E : Set (Rn n)} {ι : Type*} (s : Finset ι)
    {φ : ι → Rn n → Rn n} (hφ : ∀ i ∈ s, IsSmoothTestField U (φ i)) :
    ∫ x in E, divergence (∑ i ∈ s, φ i) x = ∑ i ∈ s, ∫ x in E, divergence (φ i) x := by
  classical
  have hdiv : divergence (∑ i ∈ s, φ i) = ∑ i ∈ s, divergence (φ i) := by
    induction s using Finset.induction_on with
    | empty =>
      funext x
      simp [divergence]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        divergence_add' (hφ a (Finset.mem_insert_self a s)).differentiable
          (IsSmoothTestField.sum s fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi)).differentiable,
        ih fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi)]
  rw [hdiv]
  simp only [Finset.sum_apply]
  exact integral_finsetSum _ fun i hi ↦ (hφ i hi).integrable_divergence.integrableOn

/-- The Gauss–Green functional is an order-zero distribution as soon as it is bounded on each
compact subset of `U`. -/
theorem isVecOrderZero_integral_divergence {U E : Set (Rn n)}
    (hbd : ∀ K, IsCompact K → K ⊆ U → ∃ C, ∀ φ, IsSmoothTestField U φ → tsupport φ ⊆ K →
      ∀ M, (∀ x, ‖φ x‖ ≤ M) → |∫ x in E, divergence φ x| ≤ C * M) :
    IsVecOrderZero U (fun φ ↦ ∫ x in E, divergence φ x) where
  map_add φ ψ hφ hψ := by
    simp only [divergence_add' hφ.differentiable hψ.differentiable, Pi.add_apply]
    exact integral_add hφ.integrable_divergence.integrableOn hψ.integrable_divergence.integrableOn
  map_smul c φ hφ := by
    simp only [divergence_smul' c hφ.differentiable, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  bound := hbd

end Divergence

/-! ### Existence -/

/-- A Gauss–Green pair on `U` from bounds on each compact subset of `U`. -/
theorem exists_isGaussGreenPair_of_bound {U E : Set (Rn n)} (hU : IsOpen U)
    (hbd : ∀ K, IsCompact K → K ⊆ U → ∃ C, ∀ φ, IsSmoothTestField U φ → tsupport φ ⊆ K →
      ∀ M, (∀ x, ‖φ x‖ ≤ M) → |∫ x in E, divergence φ x| ≤ C * M) :
    ∃ μ ν, IsGaussGreenPair U E μ ν := by
  obtain ⟨μ, ν, h1, h2, h3, h4, h5⟩ := exists_rieszPair hU (isVecOrderZero_integral_divergence hbd)
  exact ⟨μ, ν, ⟨h1, h2, h3, h4, h5⟩⟩

/-- A bound `|L| ≤ C sup |φ|` in the form of the statement implies `|L| ≤ max C 0 * M` whenever
`|φ| ≤ M`. -/
theorem abs_le_of_le_mul_iSup {C L : ℝ} {φ : Rn n → Rn n} (h : |L| ≤ C * ⨆ x, ‖φ x‖) {M : ℝ}
    (hM : ∀ x, ‖φ x‖ ≤ M) : |L| ≤ max C 0 * M := by
  have h0 : 0 ≤ ⨆ x, ‖φ x‖ := Real.iSup_nonneg fun x ↦ norm_nonneg _
  have h1 : (⨆ x, ‖φ x‖) ≤ M := ciSup_le hM
  calc |L| ≤ C * ⨆ x, ‖φ x‖ := h
    _ ≤ max C 0 * ⨆ x, ‖φ x‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max C 0 * M := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

/-! ### The total-variation formula -/

section TotalVariation

/-- The radial retraction `v ↦ v / max(1, |v|)` onto the closed unit ball. -/
private noncomputable def retract (v : Rn n) : Rn n := (max 1 ‖v‖)⁻¹ • v

private theorem max_one_norm_pos (v : Rn n) : 0 < max 1 ‖v‖ :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

private theorem norm_retract (v : Rn n) : ‖retract v‖ = ‖v‖ / max 1 ‖v‖ := by
  rw [retract, norm_smul, norm_inv, Real.norm_of_nonneg (max_one_norm_pos v).le, inv_mul_eq_div]

private theorem norm_retract_le_one (v : Rn n) : ‖retract v‖ ≤ 1 := by
  rw [norm_retract, div_le_one (max_one_norm_pos v)]
  exact le_max_right _ _

private theorem norm_retract_le (v : Rn n) : ‖retract v‖ ≤ ‖v‖ := by
  rw [norm_retract]
  exact div_le_self (norm_nonneg _) (le_max_left _ _)

private theorem continuous_retract : Continuous (retract : Rn n → Rn n) :=
  ((continuous_const.max continuous_norm).inv₀ fun v ↦ (max_one_norm_pos v).ne').smul
    continuous_id

/-- The retraction moves `v` by at most its distance to any unit vector. -/
private theorem norm_sub_retract_le {u v : Rn n} (hu : ‖u‖ = 1) : ‖v - retract v‖ ≤ ‖u - v‖ := by
  rcases le_total ‖v‖ 1 with h | h
  · simp [retract, max_eq_left h]
  · have hv : 0 < ‖v‖ := lt_of_lt_of_le one_pos h
    have hinv : ‖v‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
    calc ‖v - retract v‖ = ‖(1 - ‖v‖⁻¹) • v‖ := by
          rw [retract, max_eq_right h, sub_smul, one_smul]
      _ = (1 - ‖v‖⁻¹) * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      _ = ‖v‖ - ‖u‖ := by rw [hu]; field_simp
      _ ≤ ‖v - u‖ := norm_sub_norm_le v u
      _ = ‖u - v‖ := norm_sub_rev v u

private theorem inner_retract_ge {u v : Rn n} (hu : ‖u‖ = 1) :
    1 - 2 * ‖u - v‖ ≤ ⟪retract v, u⟫ := by
  have h1 : ‖v - retract v‖ ≤ ‖u - v‖ := norm_sub_retract_le hu
  have h2 : ⟪u - retract v, u⟫ ≤ ‖u - retract v‖ := by
    have := real_inner_le_norm (u - retract v) u
    rwa [hu, mul_one] at this
  have h3 : ‖u - retract v‖ ≤ ‖u - v‖ + ‖v - retract v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h4 : ⟪retract v, u⟫ = 1 - ⟪u - retract v, u⟫ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hu, real_inner_comm]; ring
  linarith

/-- Exhaustion of an open set by compact sets. Not private: reused in
`GaussGreenPair/WeightedTV.lean`. -/
theorem measure_le_of_forall_isCompact {μ : Measure (Rn n)} {V : Set (Rn n)}
    (hV : IsOpen V) {c : ℝ≥0∞} (h : ∀ K, IsCompact K → K ⊆ V → μ K ≤ c) : μ V ≤ c := by
  have : LocallyCompactSpace V := hV.locallyCompactSpace
  have hVeq : V = ⋃ k, Subtype.val '' compactCovering V k := by
    rw [← image_iUnion, iUnion_compactCovering, image_univ, Subtype.range_coe]
  rw [hVeq, Monotone.measure_iUnion fun a b hab ↦ image_mono (compactCovering_subset V hab)]
  exact iSup_le fun k ↦ h _ ((isCompact_compactCovering V k).image continuous_subtype_val)
    (Subtype.coe_image_subset _ _)

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- The approximation step (EG Thm 1.38, via `L¹` density of `C_c` and a smooth approximation):
on a compact `K ⊆ V`, the field `1_K ν` is the `L¹(μ)`-limit of fields `φ ∈ C^∞_c(V; ℝⁿ)` with
`|φ| ≤ 1`. -/
theorem IsGaussGreenPair.exists_smooth_integral_norm_sub_le (h : IsGaussGreenPair Ω E μ ν)
    {V : Set (Rn n)} (hV : IsOpen V) (hVΩ : V ⊆ Ω) {K : Set (Rn n)} (hK : IsCompact K)
    (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) : ∃ φ, IsSmoothTestField V φ ∧ (∀ x, ‖φ x‖ ≤ 1) ∧
      Integrable (fun x ↦ ‖φ x - K.indicator ν x‖) μ ∧
      ∫ x, ‖φ x - K.indicator ν x‖ ∂μ ≤ 3 * ε := by
  obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
  have hμK' : μ K' < ⊤ := h.lt_top_of_isCompact K' hK' (hK'V.trans hVΩ)
  set m := μ.restrict K' with hm
  have : IsFiniteMeasure m := isFiniteMeasure_restrict.2 hμK'.ne
  have : m.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure m
  have hν1 : ∀ᵐ x ∂m, ‖ν x‖ = 1 := ae_restrict_of_ae h.norm_normal
  -- `L¹(m)` approximation of `1_K ν` by a continuous compactly supported field
  set g : Rn n → Rn n := K.indicator ν with hg_def
  have hg : Integrable g m := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (h.measurable_normal.indicator hK.measurableSet).aestronglyMeasurable ?_
    filter_upwards [hν1] with x hx
    by_cases hxK : x ∈ K <;> simp [hg_def, hxK, hx]
  obtain ⟨ψ, -, hψint, hψcont, hψi⟩ := hg.exists_hasCompactSupport_integral_sub_le hε
  -- a continuous cutoff, `1` on `K`, supported in `K'`
  obtain ⟨χ, hχ0, hχ1, hχI⟩ := exists_continuous_zero_one_of_isClosed
    isOpen_interior.isClosed_compl hK.isClosed (disjoint_compl_left_iff_subset.2 hKK')
  set φ₀ : Rn n → Rn n := fun x ↦ χ x • retract (ψ x) with hφ₀
  have hφ₀cont : Continuous φ₀ := χ.continuous.smul (continuous_retract.comp hψcont)
  have hφ₀supp : support φ₀ ⊆ K' := by
    intro x hx
    by_contra hxK'
    have : χ x = 0 := hχ0 (fun hi ↦ hxK' (interior_subset hi))
    exact hx (by simp [hφ₀, this])
  have hφ₀norm : ∀ x, ‖φ₀ x‖ ≤ 1 := by
    intro x
    rw [hφ₀, norm_smul, Real.norm_of_nonneg (hχI x).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχI x).2).trans (norm_retract_le_one _)
  have hzero : ∀ f : Rn n → Rn n, support f ⊆ K' → ∀ x ∉ K', ⟪f x, ν x⟫ = 0 := by
    intro f hf x hx
    have : f x = 0 := by by_contra hne; exact hx (hf hne)
    simp [this]
  have hint_of : ∀ f : Rn n → Rn n, Continuous f → (∀ x, ‖f x‖ ≤ 1) →
      Integrable (fun x ↦ ⟪f x, ν x⟫) m := by
    intro f hf hf1
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (hf.measurable.inner h.measurable_normal).aestronglyMeasurable ?_
    filter_upwards [hν1] with x hx
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hx, mul_one]
    exact hf1 x
  -- `L¹` estimate for the continuous field `φ₀`
  have hpt₀ : ∀ᵐ x ∂m, ‖φ₀ x - g x‖ ≤ 2 * ‖g x - ψ x‖ := by
    filter_upwards [hν1] with x hx
    by_cases hxK : x ∈ K
    · have h1 := norm_sub_retract_le (v := ψ x) hx
      simp only [hφ₀, hχ1 hxK, Pi.one_apply, one_smul, hg_def, indicator_of_mem hxK]
      have h2 := norm_sub_rev (retract (ψ x)) (ψ x)
      have h3 := norm_sub_rev (ψ x) (ν x)
      have h4 := norm_sub_le_norm_sub_add_norm_sub (retract (ψ x)) (ψ x) (ν x)
      linarith
    · simp only [hg_def, indicator_of_notMem hxK, sub_zero, zero_sub, norm_neg]
      rw [hφ₀, norm_smul, Real.norm_of_nonneg (hχI x).1]
      have := (mul_le_of_le_one_left (norm_nonneg _) (hχI x).2).trans (norm_retract_le (ψ x))
      linarith [norm_nonneg (ψ x)]
  -- smooth approximation of `φ₀`, keeping `|φ| ≤ 1` and the support
  set t := (μ K').toReal
  have ht : 0 ≤ t := ENNReal.toReal_nonneg
  set δ := min (1 / 2) (ε / (2 * (t + 1))) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : 2 * δ * t ≤ ε := by
    have : δ ≤ ε / (2 * (t + 1)) := min_le_right _ _
    calc 2 * δ * t ≤ 2 * (ε / (2 * (t + 1))) * t := by gcongr
      _ = ε * (t / (t + 1)) := by field_simp
      _ ≤ ε * 1 := by gcongr; exact div_le_one_of_le₀ (by linarith) (by linarith)
      _ = ε := mul_one ε
  obtain ⟨φ, hφs, hφapprox, hφsupp⟩ :=
    (by fun_prop : Continuous fun x ↦ (1 - δ) • φ₀ x).exists_contDiff_approx
      (ε := fun _ ↦ δ) ⊤ continuous_const (fun _ ↦ hδpos)
  have hφsupp' : support φ ⊆ K' := hφsupp.trans
    ((support_const_smul_subset (1 - δ) φ₀).trans hφ₀supp)
  have hφts : tsupport φ ⊆ K' := closure_minimal hφsupp' hK'.isClosed
  have hφclose : ∀ x, ‖φ x - φ₀ x‖ ≤ 2 * δ := by
    intro x
    have h1 := (hφapprox x).le
    rw [dist_eq_norm] at h1
    have h2 : ‖φ₀ x - (1 - δ) • φ₀ x‖ ≤ δ := by
      rw [show φ₀ x - (1 - δ) • φ₀ x = δ • φ₀ x by rw [sub_smul, one_smul]; abel,
        norm_smul, Real.norm_of_nonneg hδpos.le]
      exact mul_le_of_le_one_right hδpos.le (hφ₀norm x)
    calc ‖φ x - φ₀ x‖ = ‖(φ x - (1 - δ) • φ₀ x) - (φ₀ x - (1 - δ) • φ₀ x)‖ := by abel_nf
      _ ≤ ‖φ x - (1 - δ) • φ₀ x‖ + ‖φ₀ x - (1 - δ) • φ₀ x‖ := norm_sub_le _ _
      _ ≤ 2 * δ := by linarith
  have hφnorm : ∀ x, ‖φ x‖ ≤ 1 := by
    intro x
    have h1 := (hφapprox x).le
    rw [dist_eq_norm] at h1
    have h2 : ‖(1 - δ) • φ₀ x‖ ≤ 1 - δ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      exact mul_le_of_le_one_right (by linarith) (hφ₀norm x)
    calc ‖φ x‖ = ‖(φ x - (1 - δ) • φ₀ x) + (1 - δ) • φ₀ x‖ := by abel_nf
      _ ≤ ‖φ x - (1 - δ) • φ₀ x‖ + ‖(1 - δ) • φ₀ x‖ := norm_add_le _ _
      _ ≤ 1 := by linarith
  have hφsupp_g : ∀ x ∉ K', ‖φ x - g x‖ = 0 := by
    intro x hx
    have h1 : φ x = 0 := by by_contra hne; exact hx (hφsupp' hne)
    have h2 : g x = 0 := by
      rw [hg_def, indicator_of_notMem fun hxK ↦ hx (hKK'.trans interior_subset hxK)]
    simp [h1, h2]
  have hmeas : AEStronglyMeasurable (fun x ↦ ‖φ x - g x‖) m :=
    ((hφs.continuous.measurable.sub
      (h.measurable_normal.indicator hK.measurableSet)).norm).aestronglyMeasurable
  have hbd2 : ∀ᵐ x ∂m, ‖φ x - g x‖ ≤ 2 * δ + 2 * ‖g x - ψ x‖ := by
    filter_upwards [hpt₀] with x hx
    calc ‖φ x - g x‖ ≤ ‖φ x - φ₀ x‖ + ‖φ₀ x - g x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * δ + 2 * ‖g x - ψ x‖ := add_le_add (hφclose x) hx
  have hdiff : Integrable (fun x ↦ ‖g x - ψ x‖) m := (hg.sub hψi).norm
  have hintm : Integrable (fun x ↦ ‖φ x - g x‖) m := by
    refine Integrable.mono' ((integrable_const (2 * δ)).add (hdiff.const_mul 2)) hmeas ?_
    filter_upwards [hbd2] with x hx
    rwa [Real.norm_of_nonneg (norm_nonneg _)]
  have hint : Integrable (fun x ↦ ‖φ x - g x‖) μ :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero hintm hφsupp_g
  refine ⟨φ, ⟨hφs, HasCompactSupport.of_support_subset_isCompact hK' hφsupp', hφts.trans hK'V⟩,
    hφnorm, hint, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hφsupp_g]
  have hmt : m.real univ = t := by
    rw [measureReal_def, hm, Measure.restrict_apply_univ]
  calc ∫ x, ‖φ x - g x‖ ∂m ≤ ∫ x, (2 * δ + 2 * ‖g x - ψ x‖) ∂m :=
        integral_mono_ae hintm ((integrable_const _).add (hdiff.const_mul 2)) hbd2
    _ = 2 * δ * t + 2 * ∫ x, ‖g x - ψ x‖ ∂m := by
        rw [integral_add (integrable_const _) (hdiff.const_mul 2), integral_const, smul_eq_mul,
          hmt, integral_const_mul]; ring
    _ ≤ ε + 2 * ε := add_le_add hδε (by linarith)
    _ = 3 * ε := by ring

/-- On a compact `K ⊆ V`, `μ K` is almost attained by `∫ ⟪φ, ν⟫ dμ` with `φ ∈ C^∞_c(V; ℝⁿ)`,
`|φ| ≤ 1`. -/
private theorem exists_smooth_of_isCompact (h : IsGaussGreenPair Ω E μ ν) {V : Set (Rn n)}
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) {K : Set (Rn n)} (hK : IsCompact K) (hKV : K ⊆ V) {ε : ℝ}
    (hε : 0 < ε) : ∃ φ, IsSmoothTestField V φ ∧ (∀ x, ‖φ x‖ ≤ 1) ∧
      (μ K).toReal - 3 * ε ≤ ∫ x, ⟪φ x, ν x⟫ ∂μ := by
  obtain ⟨φ, hφ, hφ1, hint, hL1⟩ := h.exists_smooth_integral_norm_sub_le hV hVΩ hK hKV hε
  refine ⟨φ, hφ, hφ1, ?_⟩
  have hμK : μ K < ⊤ := h.lt_top_of_isCompact K hK (hKV.trans hVΩ)
  have hgν : (fun x ↦ ⟪K.indicator ν x, ν x⟫) =ᵐ[μ] K.indicator (1 : Rn n → ℝ) := by
    filter_upwards [h.norm_normal] with x hx
    by_cases hxK : x ∈ K
    · simp [indicator_of_mem hxK, hx]
    · simp [indicator_of_notMem hxK]
  have hind : Integrable (K.indicator (1 : Rn n → ℝ)) μ :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hμK.ne)
  have hgint : Integrable (fun x ↦ ⟪K.indicator ν x, ν x⟫) μ := hind.congr hgν.symm
  have hdint : Integrable (fun x ↦ ⟪φ x - K.indicator ν x, ν x⟫) μ := by
    refine hint.mono' ((hφ.1.continuous.measurable.sub (h.measurable_normal.indicator
      hK.measurableSet)).inner h.measurable_normal).aestronglyMeasurable ?_
    filter_upwards [h.norm_normal] with x hx
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (by rw [hx, mul_one])
  have hsplit : ∫ x, ⟪φ x, ν x⟫ ∂μ =
      ∫ x, ⟪K.indicator ν x, ν x⟫ ∂μ + ∫ x, ⟪φ x - K.indicator ν x, ν x⟫ ∂μ := by
    rw [← integral_add hgint hdint]
    congr 1; funext x; rw [← inner_add_left, add_sub_cancel]
  have h1 : ∫ x, ⟪K.indicator ν x, ν x⟫ ∂μ = (μ K).toReal := by
    rw [integral_congr_ae hgν, integral_indicator_one hK.measurableSet, measureReal_def]
  have h2 : -(3 * ε) ≤ ∫ x, ⟪φ x - K.indicator ν x, ν x⟫ ∂μ := by
    have hn := norm_integral_le_of_norm_le hint
      (f := fun x ↦ ⟪φ x - K.indicator ν x, ν x⟫) (by
        filter_upwards [h.norm_normal] with x hx
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (by rw [hx, mul_one]))
    rw [Real.norm_eq_abs] at hn
    have := neg_abs_le (∫ x, ⟪φ x - K.indicator ν x, ν x⟫ ∂μ)
    linarith
  linarith

/-- **Total variation, `≤`.** For a Gauss–Green pair on `Ω` and an open `V ⊆ Ω`,
`μ V ≤ sup {∫_E div φ : φ ∈ C^∞_c(V; ℝⁿ), |φ| ≤ 1}`. -/
theorem IsGaussGreenPair.measure_le_iSup (h : IsGaussGreenPair Ω E μ ν) {V : Set (Rn n)}
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) :
    μ V ≤ ⨆ (φ : Rn n → Rn n) (_ : IsSmoothTestField V φ) (_ : ∀ x, ‖φ x‖ ≤ 1),
      ENNReal.ofReal (∫ x in E, divergence φ x) := by
  refine measure_le_of_forall_isCompact hV fun K hK hKV ↦ ?_
  have hμK : μ K < ⊤ := h.lt_top_of_isCompact K hK (hKV.trans hVΩ)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨φ, hφ, hφ1, hlow⟩ := exists_smooth_of_isCompact h hV hVΩ hK hKV
    (ε := (ε : ℝ) / 3) (by positivity)
  have hS : ENNReal.ofReal (∫ x in E, divergence φ x) ≤
      ⨆ (φ : Rn n → Rn n) (_ : IsSmoothTestField V φ) (_ : ∀ x, ‖φ x‖ ≤ 1),
        ENNReal.ofReal (∫ x in E, divergence φ x) :=
    le_iSup₂_of_le φ hφ (le_iSup_of_le hφ1 le_rfl)
  rw [h.integral_divergence φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVΩ⟩] at hS
  calc μ K = ENNReal.ofReal (μ K).toReal := (ENNReal.ofReal_toReal hμK.ne).symm
    _ ≤ ENNReal.ofReal (∫ x, ⟪φ x, ν x⟫ ∂μ + ε) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (∫ x, ⟪φ x, ν x⟫ ∂μ) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ ≤ _ := by rw [ENNReal.ofReal_coe_nnreal]; exact add_le_add hS le_rfl

/-- **Total variation, `≥`.** Each admissible `φ` gives `∫_E div φ ≤ μ V`. -/
theorem IsGaussGreenPair.ofReal_integral_divergence_le (h : IsGaussGreenPair Ω E μ ν)
    {V : Set (Rn n)} (hV : IsOpen V) (hVΩ : V ⊆ Ω) {φ : Rn n → Rn n}
    (hφ : IsSmoothTestField V φ) (hφ1 : ∀ x, ‖φ x‖ ≤ 1) :
    ENNReal.ofReal (∫ x in E, divergence φ x) ≤ μ V := by
  rcases eq_top_or_lt_top (μ V) with hμV | hμV
  · rw [hμV]; exact le_top
  rw [h.integral_divergence φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVΩ⟩]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  have hind : Integrable (V.indicator (1 : Rn n → ℝ)) μ :=
    (integrable_indicator_iff hV.measurableSet).2 (integrableOn_const hμV.ne)
  have := norm_integral_le_of_norm_le hind (f := fun x ↦ ⟪φ x, ν x⟫) (by
    filter_upwards [h.norm_normal] with x hx
    by_cases hxV : x ∈ V
    · rw [indicator_of_mem hxV, Pi.one_apply, Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [hx, mul_one]
      exact hφ1 x
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hx' ↦ hxV (hφ.2.2 hx')
      simp [this, indicator_of_notMem hxV])
  rw [integral_indicator_one hV.measurableSet] at this
  exact (le_abs_self _).trans (by rwa [← Real.norm_eq_abs])

/-- **Total-variation formula.** For a Gauss–Green pair on `Ω` and an open `V ⊆ Ω`,
`μ V = sup {∫_E div φ : φ ∈ C^∞_c(V; ℝⁿ), |φ| ≤ 1}`. In particular `μ` restricted to `Ω` depends
only on `E` (`IsGaussGreenPair.unique`). -/
theorem IsGaussGreenPair.measure_eq_iSup (h : IsGaussGreenPair Ω E μ ν) {V : Set (Rn n)}
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) :
    μ V = ⨆ (φ : Rn n → Rn n) (_ : IsSmoothTestField V φ) (_ : ∀ x, ‖φ x‖ ≤ 1),
      ENNReal.ofReal (∫ x in E, divergence φ x) :=
  le_antisymm (h.measure_le_iSup hV hVΩ)
    (iSup₂_le fun _ hφ ↦ iSup_le fun hφ1 ↦ h.ofReal_integral_divergence_le hV hVΩ hφ hφ1)

end TotalVariation

/-! ### Existence of the Gauss–Green pair (EG Thm 5.1) -/

/-- EG Thm 5.1 for `f = χ_E`. The Riesz pair of `φ ↦ ∫_E div φ` (`exists_rieszPair`),
with the mass bound from the total-variation formula. -/
theorem exists_isGaussGreenPair_of_integral_divergence_le :
    GaussGreenPairOfDivergenceBoundStatement n := by
  intro _ U E hU _ C h
  obtain ⟨μ, ν, hp⟩ := exists_isGaussGreenPair_of_bound hU (E := E)
    fun K _ _ ↦ ⟨max C 0, fun φ hφ _ M hM ↦ abs_le_of_le_mul_iSup (h φ hφ) hM⟩
  refine ⟨μ, ν, hp, (hp.measure_le_iSup hU subset_rfl).trans
    (iSup₂_le fun φ hφ ↦ iSup_le fun hφ1 ↦ ?_)⟩
  have h1 := abs_le_of_le_mul_iSup (h φ hφ) hφ1
  rw [mul_one] at h1
  calc ENNReal.ofReal (∫ x in E, divergence φ x) ≤ ENNReal.ofReal (max C 0) :=
        ENNReal.ofReal_le_ofReal ((le_abs_self _).trans h1)
    _ = ENNReal.ofReal C := by rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]

end GMTFoundations
