/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Calculus
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Vector Riesz representation for distributions of order zero

Let `U ⊆ ℝⁿ` be open and let `L` be a linear functional on `C^∞_c(U; ℝⁿ)` that is bounded in the
sup norm on each compact subset of `U`. Then there are a Radon measure `μ` on `U` and a
`μ`-measurable unit vector field `ν` with `L φ = ∫ ⟪φ, ν⟫ dμ` (`exists_rieszPair`). This is
Thm 1.38 (Riesz representation, vector form) of L. C. Evans, R. F. Gariepy, *Measure Theory and
Fine Properties of Functions*, rev. ed., CRC Press, 2015 (EG), in the form used by EG Thm 5.1.

## Route (differs from EG 1.38)

* **Step 1.** Each component `ℓᵢ f := L (f • eᵢ)` is a scalar functional on `C^∞_c(U)`, bounded
  on each compact. It extends uniquely to `C_c(U)` by uniform approximation
  (`Continuous.exists_contDiff_approx`, which keeps the support inside the support of `f`, so no
  mollifier and no support margin is needed).
* **Step 2.** Jordan decomposition on the lattice `C_c(U, ℝ≥0)`: `ℓ⁺ g := sup {ℓ h : 0 ≤ h ≤ g}` is
  additive (Riesz decomposition `h = h ⊓ g₁ + (h - h ⊓ g₁)`) and `ℓ = ℓ⁺ - (-ℓ)⁺`. RMK (Mathlib
  `NNRealRMK.rieszMeasure`) on the locally compact space `U` gives measures `μᵢ^±`. With
  `P := Σᵢ (μᵢ⁺ + μᵢ⁻)` and `σᵢ := dμᵢ⁺/dP - dμᵢ⁻/dP` we get `ℓᵢ f = ∫ f σᵢ dP`.
* The pair is `(|σ| P, σ/|σ|)`, pushed forward to `ℝⁿ`. Thus `|ν| = 1` holds by construction and
  no minimality of `P` (EG's `|σ| = 1` step) is needed. The mass identity
  `μ(V) = sup {L φ : |φ| ≤ 1}` is proved for *every* pair in `Perimeter/GaussGreenPair.lean`.

Conversions between `C_c(U, ℝ)` and functions on `ℝⁿ` with `tsupport ⊆ U` use
`Function.extend Subtype.val · 0` (`extendC`) and composition with `Subtype.val` (`restrictC`).
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped ContDiff NNReal ENNReal RealInnerProductSpace CompactlySupported

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### `C_c(U)` versus functions on `ℝⁿ` supported in `U` -/

section Conversion

variable {U : Set (Rn n)}

/-- Extension by zero of a compactly supported continuous function on the open set `U`. -/
@[expose] noncomputable def extendC (F : C_c(U, ℝ)) : Rn n → ℝ :=
  Subtype.val.extend F 0

theorem extendC_apply_val (F : C_c(U, ℝ)) (x : U) : extendC F x = F x :=
  Subtype.val_injective.extend_apply _ _ x

theorem extendC_apply_of_mem (F : C_c(U, ℝ)) {x : Rn n} (hx : x ∈ U) :
    extendC F x = F ⟨x, hx⟩ :=
  extendC_apply_val F ⟨x, hx⟩

theorem extendC_apply_of_notMem (F : C_c(U, ℝ)) {x : Rn n} (hx : x ∉ U) : extendC F x = 0 := by
  unfold extendC
  rw [extend_apply']
  · rfl
  · rintro ⟨y, rfl⟩
    exact hx y.2

theorem continuous_extendC (hU : IsOpen U) (F : C_c(U, ℝ)) : Continuous (extendC F) :=
  HasCompactSupport.continuous_extend_zero hU F.continuous F.hasCompactSupport

theorem hasCompactSupport_extendC (F : C_c(U, ℝ)) : HasCompactSupport (extendC F) :=
  F.hasCompactSupport.extend_zero continuous_subtype_val

theorem tsupport_extendC (F : C_c(U, ℝ)) :
    tsupport (extendC F) = Subtype.val '' tsupport F :=
  F.hasCompactSupport.tsupport_extend_zero continuous_subtype_val Subtype.val_injective

theorem tsupport_extendC_subset (F : C_c(U, ℝ)) : tsupport (extendC F) ⊆ U := by
  rw [tsupport_extendC]
  exact Subtype.coe_image_subset _ _

theorem extendC_add (F G : C_c(U, ℝ)) : extendC (F + G) = extendC F + extendC G := by
  ext x
  by_cases hx : x ∈ U
  · simp [extendC_apply_of_mem _ hx]
  · simp [extendC_apply_of_notMem _ hx]

theorem extendC_smul (c : ℝ) (F : C_c(U, ℝ)) : extendC (c • F) = c • extendC F := by
  ext x
  by_cases hx : x ∈ U
  · simp [extendC_apply_of_mem _ hx]
  · simp [extendC_apply_of_notMem _ hx]

theorem abs_extendC_le (F : C_c(U, ℝ)) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, |F x| ≤ M)
    (x : Rn n) : |extendC F x| ≤ M := by
  by_cases hx : x ∈ U
  · rw [extendC_apply_of_mem _ hx]; exact hM _
  · rw [extendC_apply_of_notMem _ hx, abs_zero]; exact hM0

/-- A compact subset of `ℝⁿ` contained in `U`, viewed in the subtype, is compact. -/
theorem isCompact_preimage_val {K : Set (Rn n)} (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompact ((Subtype.val : U → Rn n) ⁻¹' K) := by
  rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
    inter_eq_left.2 hKU]
  exact hK

/-- Restriction to `U` of a continuous function on `ℝⁿ` with compact support in `U`. -/
@[expose] noncomputable def restrictC (g : Rn n → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) : C_c(U, ℝ) where
  toFun x := g x
  continuous_toFun := hg.comp continuous_subtype_val
  hasCompactSupport' := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_preimage_val hgc hgU) ?_
    intro x hx
    exact subset_tsupport g hx

@[simp]
theorem restrictC_apply (g : Rn n → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) (x : U) : restrictC g hg hgc hgU x = g x := rfl

theorem extendC_restrictC (g : Rn n → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) : extendC (restrictC g hg hgc hgU) = g := by
  ext x
  by_cases hx : x ∈ U
  · rw [extendC_apply_of_mem _ hx]; rfl
  · rw [extendC_apply_of_notMem _ hx]
    exact (image_eq_zero_of_notMem_tsupport fun h ↦ hx (hgU h)).symm

end Conversion

/-! ### Step 1: scalar functionals of order zero and their extension to `C_c(U)` -/

section Extension

variable {U : Set (Rn n)}

theorem IsTestFunction.add {f g : Rn n → ℝ} (hf : IsTestFunction U f) (hg : IsTestFunction U g) :
    IsTestFunction U (f + g) :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩

theorem IsTestFunction.smul {f : Rn n → ℝ} (hf : IsTestFunction U f) (c : ℝ) :
    IsTestFunction U (c • f) :=
  ⟨hf.1.const_smul c, hf.2.1.smul_left (f := fun _ ↦ c),
    (tsupport_smul_subset_right (fun _ ↦ c) f).trans hf.2.2⟩

theorem IsTestFunction.sub {f g : Rn n → ℝ} (hf : IsTestFunction U f) (hg : IsTestFunction U g) :
    IsTestFunction U (f - g) :=
  ⟨hf.1.sub hg.1, hf.2.1.sub hg.2.1, (tsupport_sub f g).trans (union_subset hf.2.2 hg.2.2)⟩

/-- `ℓ` is a real distribution of order zero on `U`, given on `C^∞_c(U)`: it is linear and bounded
in the sup norm on the test functions supported in any fixed compact subset of `U`. -/
structure IsOrderZero (U : Set (Rn n)) (ℓ : (Rn n → ℝ) → ℝ) : Prop where
  map_add : ∀ f g, IsTestFunction U f → IsTestFunction U g → ℓ (f + g) = ℓ f + ℓ g
  map_smul : ∀ (c : ℝ) f, IsTestFunction U f → ℓ (c • f) = c * ℓ f
  bound : ∀ K, IsCompact K → K ⊆ U → ∃ C, ∀ f, IsTestFunction U f → tsupport f ⊆ K →
    ∀ M, (∀ x, |f x| ≤ M) → |ℓ f| ≤ C * M

namespace IsOrderZero

variable {ℓ : (Rn n → ℝ) → ℝ}

theorem map_sub (hℓ : IsOrderZero U ℓ) {f g : Rn n → ℝ} (hf : IsTestFunction U f)
    (hg : IsTestFunction U g) : ℓ (f - g) = ℓ f - ℓ g := by
  have h1 := hℓ.map_add f ((-1 : ℝ) • g) hf (hg.smul _)
  rw [hℓ.map_smul _ _ hg] at h1
  rw [sub_eq_add_neg, show -g = (-1 : ℝ) • g by simp, h1]
  ring

/-- The bound with a nonnegative constant. -/
theorem bound' (hℓ : IsOrderZero U ℓ) {K : Set (Rn n)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, 0 ≤ C ∧ ∀ f, IsTestFunction U f → tsupport f ⊆ K →
      ∀ M, (∀ x, |f x| ≤ M) → |ℓ f| ≤ C * M := by
  obtain ⟨C, hC⟩ := hℓ.bound K hK hKU
  refine ⟨max C 0, le_max_right _ _, fun f hf hfK M hM ↦ ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  exact (hC f hf hfK M hM).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0)

end IsOrderZero

private theorem exists_approx {f : Rn n → ℝ} (hf : Continuous f) (k : ℕ) :
    ∃ g : Rn n → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, |g x - f x| < 1 / (k + 1)) ∧
      support g ⊆ support f := by
  obtain ⟨g, hg, hgf, hs⟩ := hf.exists_contDiff_approx (ε := fun _ ↦ (1 : ℝ) / (k + 1)) ⊤
    continuous_const (fun _ ↦ by positivity)
  exact ⟨g, hg, fun x ↦ by simpa [Real.dist_eq] using hgf x, hs⟩

open Classical in
/-- Smooth approximants of a continuous function, within `1/(k+1)`, supported in its support. -/
private noncomputable def approxSeq (f : Rn n → ℝ) (k : ℕ) : Rn n → ℝ :=
  if hf : Continuous f then (exists_approx hf k).choose else 0

private theorem approxSeq_spec {f : Rn n → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) (k : ℕ) :
    IsTestFunction U (approxSeq f k) ∧ tsupport (approxSeq f k) ⊆ tsupport f ∧
      ∀ x, |approxSeq f k x - f x| ≤ 1 / (k + 1) := by
  have h := (exists_approx hf k).choose_spec
  simp only [approxSeq, hf, dite_true]
  have hts : tsupport (exists_approx hf k).choose ⊆ tsupport f := closure_mono h.2.2
  exact ⟨⟨h.1, hfc.mono h.2.2, hts.trans hfU⟩, hts, fun x ↦ (h.2.1 x).le⟩

/-- The extension of `ℓ` from `C^∞_c(U)` to `C_c(U)`: the limit of `ℓ` along the smooth
approximants. It is meaningful for continuous `f` with compact support in `U`. -/
noncomputable def extendFun (ℓ : (Rn n → ℝ) → ℝ) (f : Rn n → ℝ) : ℝ :=
  limUnder atTop fun k ↦ ℓ (approxSeq f k)

namespace IsOrderZero

variable {ℓ : (Rn n → ℝ) → ℝ}

/-- Two sequences of test functions supported in a fixed compact, uniformly close, have
asymptotically equal values. -/
theorem tendsto_sub (hℓ : IsOrderZero U ℓ) {K : Set (Rn n)} (hK : IsCompact K) (hKU : K ⊆ U)
    {b b' : ℕ → Rn n → ℝ} (hb : ∀ k, IsTestFunction U (b k)) (hb' : ∀ k, IsTestFunction U (b' k))
    (hbK : ∀ k, tsupport (b k) ⊆ K) (hb'K : ∀ k, tsupport (b' k) ⊆ K) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) (hbb : ∀ k x, |b k x - b' k x| ≤ δ k) :
    Tendsto (fun k ↦ ℓ (b k) - ℓ (b' k)) atTop (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := hℓ.bound' hK hKU
  refine squeeze_zero_norm (a := fun k ↦ C * δ k) (fun k ↦ ?_) (by simpa using hδ.const_mul C)
  rw [Real.norm_eq_abs, ← hℓ.map_sub (hb k) (hb' k)]
  exact hC _ ((hb k).sub (hb' k)) ((tsupport_sub _ _).trans (union_subset (hbK k) (hb'K k)))
    _ (fun x ↦ hbb k x)

private theorem cauchySeq_approxSeq (hℓ : IsOrderZero U ℓ) {f : Rn n → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    CauchySeq fun k ↦ ℓ (approxSeq f k) := by
  obtain ⟨C, hC0, hC⟩ := hℓ.bound' hfc hfU
  refine cauchySeq_of_le_tendsto_0 (fun N : ℕ ↦ C * (2 / (N + 1))) (fun k m N hk hm ↦ ?_) ?_
  · have hk' := approxSeq_spec hf hfc hfU k
    have hm' := approxSeq_spec hf hfc hfU m
    rw [Real.dist_eq, ← hℓ.map_sub hk'.1 hm'.1]
    refine (hC _ (hk'.1.sub hm'.1) ((tsupport_sub _ _).trans (union_subset hk'.2.1 hm'.2.1))
      (2 / (N + 1)) (fun x ↦ ?_))
    have h1 := hk'.2.2 x
    have h2 := hm'.2.2 x
    have hkN : (1 : ℝ) / (k + 1) ≤ 1 / (N + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hk)
    have hmN : (1 : ℝ) / (m + 1) ≤ 1 / (N + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hm)
    calc |(approxSeq f k - approxSeq f m) x|
        = |(approxSeq f k x - f x) - (approxSeq f m x - f x)| := by simp
      _ ≤ |approxSeq f k x - f x| + |approxSeq f m x - f x| := abs_sub _ _
      _ ≤ 2 / (N + 1) := by
        rw [show (2 : ℝ) / (N + 1) = 1 / (N + 1) + 1 / (N + 1) by ring]; linarith
  · have : Tendsto (fun N : ℕ ↦ (2 : ℝ) / (N + 1)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
      rw [mul_zero] at h
      exact h.congr fun N ↦ by ring
    simpa using this.const_mul C

/-- **Step 1.** Any sequence of test functions supported in a fixed compact of `U` and converging
uniformly to `f` has `ℓ`-values converging to `extendFun ℓ f`. -/
theorem tendsto_extendFun (hℓ : IsOrderZero U ℓ) {f : Rn n → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) {K : Set (Rn n)} (hK : IsCompact K)
    (hKU : K ⊆ U) {b : ℕ → Rn n → ℝ} (hb : ∀ k, IsTestFunction U (b k))
    (hbK : ∀ k, tsupport (b k) ⊆ K) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hbf : ∀ k x, |b k x - f x| ≤ δ k) :
    Tendsto (fun k ↦ ℓ (b k)) atTop (𝓝 (extendFun ℓ f)) := by
  have hlim : Tendsto (fun k ↦ ℓ (approxSeq f k)) atTop (𝓝 (extendFun ℓ f)) :=
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hℓ.cauchySeq_approxSeq hf hfc hfU))
  have hsub := hℓ.tendsto_sub (hK.union hfc) (union_subset hKU hfU) hb
    (fun k ↦ (approxSeq_spec hf hfc hfU k).1)
    (fun k ↦ (hbK k).trans subset_union_left)
    (fun k ↦ (approxSeq_spec hf hfc hfU k).2.1.trans subset_union_right)
    (δ := fun k ↦ δ k + 1 / (k + 1)) (by simpa using hδ.add tendsto_one_div_add_atTop_nhds_zero_nat)
    (fun k x ↦ by
      have h1 := hbf k x
      have h2 := (approxSeq_spec hf hfc hfU k).2.2 x
      calc |b k x - approxSeq f k x| = |(b k x - f x) - (approxSeq f k x - f x)| := by ring_nf
        _ ≤ |b k x - f x| + |approxSeq f k x - f x| := abs_sub _ _
        _ ≤ δ k + 1 / (k + 1) := add_le_add h1 h2)
  simpa using hsub.add hlim

theorem extendFun_eq (hℓ : IsOrderZero U ℓ) {f : Rn n → ℝ} (hf : IsTestFunction U f) :
    extendFun ℓ f = ℓ f :=
  tendsto_nhds_unique (hℓ.tendsto_extendFun hf.1.continuous hf.2.1 hf.2.2 hf.2.1 hf.2.2
    (b := fun _ ↦ f) (fun _ ↦ hf) (fun _ ↦ subset_rfl) (δ := fun _ ↦ 0) tendsto_const_nhds
    (fun _ _ ↦ by simp)) tendsto_const_nhds

theorem extendFun_add (hℓ : IsOrderZero U ℓ) {f g : Rn n → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    extendFun ℓ (f + g) = extendFun ℓ f + extendFun ℓ g := by
  have hf' := approxSeq_spec hf hfc hfU
  have hg' := approxSeq_spec hg hgc hgU
  have hz : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 := hℓ.tendsto_extendFun (hf.add hg) (hfc.add hgc)
    ((tsupport_add f g).trans (union_subset hfU hgU)) (hfc.union hgc) (union_subset hfU hgU)
    (b := fun k ↦ approxSeq f k + approxSeq g k) (fun k ↦ (hf' k).1.add (hg' k).1)
    (fun k ↦ (tsupport_add _ _).trans (union_subset_union (hf' k).2.1 (hg' k).2.1))
    (δ := fun k ↦ 1 / (k + 1) + 1 / (k + 1))
    (by simpa using hz.add hz)
    (fun k x ↦ by
      have h1 := (hf' k).2.2 x
      have h2 := (hg' k).2.2 x
      calc |(approxSeq f k + approxSeq g k) x - (f + g) x|
          = |(approxSeq f k x - f x) + (approxSeq g k x - g x)| := by simp; ring_nf
        _ ≤ |approxSeq f k x - f x| + |approxSeq g k x - g x| := abs_add_le _ _
        _ ≤ _ := add_le_add h1 h2)
  have h2 : Tendsto (fun k ↦ ℓ (approxSeq f k + approxSeq g k)) atTop
      (𝓝 (extendFun ℓ f + extendFun ℓ g)) := by
    simp_rw [fun k ↦ hℓ.map_add _ _ (hf' k).1 (hg' k).1]
    exact (hℓ.tendsto_extendFun hf hfc hfU hfc hfU (fun k ↦ (hf' k).1) (fun k ↦ (hf' k).2.1)
      tendsto_one_div_add_atTop_nhds_zero_nat (fun k x ↦ (hf' k).2.2 x)).add
      (hℓ.tendsto_extendFun hg hgc hgU hgc hgU (fun k ↦ (hg' k).1) (fun k ↦ (hg' k).2.1)
      tendsto_one_div_add_atTop_nhds_zero_nat (fun k x ↦ (hg' k).2.2 x))
  exact tendsto_nhds_unique h1 h2

theorem extendFun_smul (hℓ : IsOrderZero U ℓ) {f : Rn n → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) (c : ℝ) :
    extendFun ℓ (c • f) = c * extendFun ℓ f := by
  have hf' := approxSeq_spec hf hfc hfU
  have h1 := hℓ.tendsto_extendFun (hf.const_smul c) (hfc.smul_left (f := fun _ ↦ c))
    ((tsupport_smul_subset_right (fun _ ↦ c) f).trans hfU) hfc hfU
    (b := fun k ↦ c • approxSeq f k) (fun k ↦ (hf' k).1.smul c)
    (fun k ↦ (tsupport_smul_subset_right (fun _ ↦ c) _).trans (hf' k).2.1)
    (δ := fun k ↦ |c| * (1 / (k + 1)))
    (by simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul |c|)
    (fun k x ↦ by
      simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left ((hf' k).2.2 x) (abs_nonneg c))
  have h2 : Tendsto (fun k ↦ ℓ (c • approxSeq f k)) atTop (𝓝 (c * extendFun ℓ f)) := by
    simp_rw [fun k ↦ hℓ.map_smul c _ (hf' k).1]
    exact (hℓ.tendsto_extendFun hf hfc hfU hfc hfU (fun k ↦ (hf' k).1) (fun k ↦ (hf' k).2.1)
      tendsto_one_div_add_atTop_nhds_zero_nat (fun k x ↦ (hf' k).2.2 x)).const_mul c
  exact tendsto_nhds_unique h1 h2

/-- The extension obeys the same bound on each compact. -/
theorem abs_extendFun_le (hℓ : IsOrderZero U ℓ) {K : Set (Rn n)} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ C, 0 ≤ C ∧ ∀ f : Rn n → ℝ, Continuous f → tsupport f ⊆ K →
      ∀ M, (∀ x, |f x| ≤ M) → |extendFun ℓ f| ≤ C * M := by
  obtain ⟨C, hC0, hC⟩ := hℓ.bound' hK hKU
  refine ⟨C, hC0, fun f hf hfK M hM ↦ ?_⟩
  have hfc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hK
    (subset_tsupport f |>.trans hfK)
  have hf' := approxSeq_spec hf hfc (hfK.trans hKU)
  have hlim := hℓ.tendsto_extendFun hf hfc (hfK.trans hKU) hfc (hfK.trans hKU)
    (fun k ↦ (hf' k).1) (fun k ↦ (hf' k).2.1) tendsto_one_div_add_atTop_nhds_zero_nat
    (fun k x ↦ (hf' k).2.2 x)
  have hbd : Tendsto (fun k : ℕ ↦ C * (M + 1 / (k + 1))) atTop (𝓝 (C * M)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_add M).const_mul C
  refine le_of_tendsto_of_tendsto' hlim.abs hbd (fun k ↦ ?_)
  refine hC _ (hf' k).1 ((hf' k).2.1.trans hfK) _ (fun x ↦ ?_)
  have h1 := (hf' k).2.2 x
  have h2 := hM x
  calc |approxSeq f k x| = |(approxSeq f k x - f x) + f x| := by ring_nf
    _ ≤ |approxSeq f k x - f x| + |f x| := abs_add_le _ _
    _ ≤ M + 1 / (k + 1) := by linarith

end IsOrderZero

/-- **Step 1.** The extension of an order-zero functional on `C^∞_c(U)` to a linear functional on
`C_c(U)`. -/
noncomputable def IsOrderZero.extendLinear {ℓ : (Rn n → ℝ) → ℝ} (hU : IsOpen U)
    (hℓ : IsOrderZero U ℓ) : C_c(U, ℝ) →ₗ[ℝ] ℝ where
  toFun F := extendFun ℓ (extendC F)
  map_add' F G := by
    rw [extendC_add]
    exact hℓ.extendFun_add (continuous_extendC hU F) (hasCompactSupport_extendC F)
      (tsupport_extendC_subset F) (continuous_extendC hU G) (hasCompactSupport_extendC G)
      (tsupport_extendC_subset G)
  map_smul' c F := by
    rw [extendC_smul]
    exact hℓ.extendFun_smul (continuous_extendC hU F) (hasCompactSupport_extendC F)
      (tsupport_extendC_subset F) c

theorem IsOrderZero.extendLinear_apply {ℓ : (Rn n → ℝ) → ℝ} (hU : IsOpen U)
    (hℓ : IsOrderZero U ℓ) (F : C_c(U, ℝ)) : hℓ.extendLinear hU F = extendFun ℓ (extendC F) := by
  unfold IsOrderZero.extendLinear; rfl

end Extension

/-! ### Step 2 (scalar): Jordan decomposition on `C_c(X)` and RMK -/

section Jordan

variable {X : Type*} [TopologicalSpace X]

/-- The values `ℓ h`, `0 ≤ h ≤ g`. -/
def valuesBelow (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (g : C_c(X, ℝ≥0)) : Set ℝ :=
  (fun h : C_c(X, ℝ≥0) ↦ Λ h.toReal) '' Iic g

/-- `Λ` is bounded above on each order interval `[0, g]`. -/
def IsOrderBddAbove (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ g : C_c(X, ℝ≥0), BddAbove (valuesBelow Λ g)

/-- The positive part `Λ⁺ g = sup {Λ h : 0 ≤ h ≤ g}`. -/
noncomputable def posPartFun (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (g : C_c(X, ℝ≥0)) : ℝ :=
  sSup (valuesBelow Λ g)

variable {Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ}

private theorem nnreal_zero_le (g : C_c(X, ℝ≥0)) : 0 ≤ g :=
  CompactlySupportedContinuousMap.le_def.2 fun x ↦ by simp

private theorem nnreal_le_add_left (h h' : C_c(X, ℝ≥0)) : h' ≤ h + h' :=
  CompactlySupportedContinuousMap.le_def.2 fun x ↦ by simp

private theorem nnreal_le_add_right (h h' : C_c(X, ℝ≥0)) : h ≤ h + h' :=
  CompactlySupportedContinuousMap.le_def.2 fun x ↦ by simp

private theorem toReal_zero' : (0 : C_c(X, ℝ≥0)).toReal = 0 := by ext; simp

private theorem valuesBelow_nonempty (g : C_c(X, ℝ≥0)) : (valuesBelow Λ g).Nonempty :=
  ⟨_, 0, nnreal_zero_le g, rfl⟩

private theorem le_posPartFun (hb : IsOrderBddAbove Λ) {g h : C_c(X, ℝ≥0)} (hh : h ≤ g) :
    Λ h.toReal ≤ posPartFun Λ g :=
  le_csSup (hb g) ⟨h, hh, rfl⟩

private theorem posPartFun_le {g : C_c(X, ℝ≥0)} {c : ℝ} (H : ∀ h, h ≤ g → Λ h.toReal ≤ c) :
    posPartFun Λ g ≤ c :=
  csSup_le (valuesBelow_nonempty g) (by rintro _ ⟨h, hh, rfl⟩; exact H h hh)

private theorem posPartFun_nonneg (hb : IsOrderBddAbove Λ) (g : C_c(X, ℝ≥0)) :
    0 ≤ posPartFun Λ g := by
  have := le_posPartFun hb (nnreal_zero_le g)
  simpa [toReal_zero'] using this

private theorem toReal_sub_of_add {h h' g : C_c(X, ℝ≥0)} (hg : h + h' = g) :
    Λ h'.toReal = Λ g.toReal - Λ h.toReal := by
  rw [← hg, CompactlySupportedContinuousMap.toReal_add, map_add]; ring

private theorem posPartFun_add (hb : IsOrderBddAbove Λ) (g₁ g₂ : C_c(X, ℝ≥0)) :
    posPartFun Λ (g₁ + g₂) = posPartFun Λ g₁ + posPartFun Λ g₂ := by
  apply le_antisymm
  · refine posPartFun_le fun h hh ↦ ?_
    obtain ⟨h₂, hh₂⟩ := CompactlySupportedContinuousMap.exists_add_of_le (inf_le_left : h ⊓ g₁ ≤ h)
    have h₂le : h₂ ≤ g₂ := by
      intro x
      have hx := hh x
      have e := congrArg (fun F : C_c(X, ℝ≥0) ↦ F x) hh₂
      simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply,
        CompactlySupportedContinuousMap.inf_apply] at hx e
      rcases le_total (h x) (g₁ x) with hle | hle
      · rw [min_eq_left hle] at e
        have : h₂ x = 0 := by
          have := congrArg (· - h x) e
          simpa using this
        rw [this]; exact zero_le
      · rw [min_eq_right hle] at e
        rw [← e] at hx
        exact le_of_add_le_add_left hx
    rw [← hh₂, CompactlySupportedContinuousMap.toReal_add, map_add]
    exact add_le_add (le_posPartFun hb inf_le_right) (le_posPartFun hb h₂le)
  · have key : ∀ h₁, h₁ ≤ g₁ → ∀ h₂, h₂ ≤ g₂ →
        Λ h₁.toReal + Λ h₂.toReal ≤ posPartFun Λ (g₁ + g₂) := fun h₁ h₁le h₂ h₂le ↦ by
      rw [← map_add, ← CompactlySupportedContinuousMap.toReal_add]
      exact le_posPartFun hb (add_le_add h₁le h₂le)
    have hA : posPartFun Λ g₁ ≤ posPartFun Λ (g₁ + g₂) - posPartFun Λ g₂ :=
      posPartFun_le fun h₁ h₁le ↦ by
        have : posPartFun Λ g₂ ≤ posPartFun Λ (g₁ + g₂) - Λ h₁.toReal :=
          posPartFun_le fun h₂ h₂le ↦ by
            have := key h₁ h₁le h₂ h₂le
            linarith
        linarith
    linarith

private theorem posPartFun_smul (hb : IsOrderBddAbove Λ) (c : ℝ≥0) (g : C_c(X, ℝ≥0)) :
    posPartFun Λ (c • g) = c * posPartFun Λ g := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_smul, NNReal.coe_zero, zero_mul]
    apply le_antisymm
    · refine posPartFun_le fun h hh ↦ ?_
      have : h = 0 := le_antisymm hh (nnreal_zero_le h)
      simp [this, toReal_zero']
    · simpa [toReal_zero'] using le_posPartFun (Λ := Λ) hb (le_refl (0 : C_c(X, ℝ≥0)))
  · have hc' : (0 : ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
    apply le_antisymm
    · refine posPartFun_le fun h hh ↦ ?_
      have hle : c⁻¹ • h ≤ g := by
        intro x
        have := hh x
        simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [inv_mul_le_iff₀ (pos_iff_ne_zero.2 hc)]
        exact this
      have := le_posPartFun hb hle
      rw [CompactlySupportedContinuousMap.toReal_smul, NNReal.smul_def, map_smul,
        smul_eq_mul, NNReal.coe_inv] at this
      calc Λ h.toReal = (c : ℝ) * ((c : ℝ)⁻¹ * Λ h.toReal) := by field_simp
        _ ≤ c * posPartFun Λ g := mul_le_mul_of_nonneg_left this hc'.le
    · rw [← le_div_iff₀' hc']
      refine posPartFun_le fun h hh ↦ ?_
      rw [le_div_iff₀' hc']
      have hle : c • h ≤ c • g := by
        intro x
        have := hh x
        simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left this zero_le
      have := le_posPartFun hb hle
      rwa [CompactlySupportedContinuousMap.toReal_smul, NNReal.smul_def, map_smul,
        smul_eq_mul] at this

private theorem isOrderBddAbove_neg (hb : IsOrderBddAbove Λ) : IsOrderBddAbove (-Λ) := by
  intro g
  refine ⟨posPartFun Λ g - Λ g.toReal, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨h', hh'⟩ := CompactlySupportedContinuousMap.exists_add_of_le hh
  have := le_posPartFun hb (show h' ≤ g from hh' ▸ nnreal_le_add_left h h')
  rw [toReal_sub_of_add hh'] at this
  simp only [LinearMap.neg_apply]
  linarith

private theorem posPartFun_neg (hb : IsOrderBddAbove Λ) (g : C_c(X, ℝ≥0)) :
    posPartFun (-Λ) g = posPartFun Λ g - Λ g.toReal := by
  apply le_antisymm
  · refine posPartFun_le fun h hh ↦ ?_
    obtain ⟨h', hh'⟩ := CompactlySupportedContinuousMap.exists_add_of_le hh
    have := le_posPartFun hb (show h' ≤ g from hh' ▸ nnreal_le_add_left h h')
    rw [toReal_sub_of_add hh'] at this
    simp only [LinearMap.neg_apply]
    linarith
  · rw [sub_le_iff_le_add]
    refine posPartFun_le fun h' hh' ↦ ?_
    obtain ⟨h, hh⟩ := CompactlySupportedContinuousMap.exists_add_of_le hh'
    rw [add_comm] at hh
    have := le_posPartFun (isOrderBddAbove_neg hb) (show h ≤ g from hh ▸ nnreal_le_add_right h h')
    rw [toReal_sub_of_add hh]
    simp only [LinearMap.neg_apply] at this
    linarith

/-- The positive part `Λ⁺` as an `ℝ≥0`-linear functional on `C_c(X, ℝ≥0)`. -/
noncomputable def posPart (Λ : C_c(X, ℝ) →ₗ[ℝ] ℝ) (hb : IsOrderBddAbove Λ) :
    C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun g := ⟨posPartFun Λ g, posPartFun_nonneg hb g⟩
  map_add' g₁ g₂ := NNReal.eq (posPartFun_add hb g₁ g₂)
  map_smul' c g := NNReal.eq (posPartFun_smul hb c g)

private theorem coe_posPart (hb : IsOrderBddAbove Λ) (g : C_c(X, ℝ≥0)) :
    (posPart Λ hb g : ℝ) = posPartFun Λ g := rfl

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Signed RMK.** A linear functional on `C_c(X, ℝ)` bounded above on order intervals is the
difference of two Radon measures. -/
theorem exists_measures_of_isOrderBddAbove (hb : IsOrderBddAbove Λ) :
    ∃ μp μm : Measure X, μp.Regular ∧ μm.Regular ∧
      ∀ f : C_c(X, ℝ), Λ f = ∫ x, f x ∂μp - ∫ x, f x ∂μm := by
  have hb' := isOrderBddAbove_neg hb
  refine ⟨NNRealRMK.rieszMeasure (posPart Λ hb), NNRealRMK.rieszMeasure (posPart (-Λ) hb'),
    inferInstance, inferInstance, fun f ↦ ?_⟩
  have hg : ∀ g : C_c(X, ℝ≥0), Λ g.toReal =
      ∫ x, g.toReal x ∂NNRealRMK.rieszMeasure (posPart Λ hb) -
        ∫ x, g.toReal x ∂NNRealRMK.rieszMeasure (posPart (-Λ) hb') := by
    intro g
    simp only [CompactlySupportedContinuousMap.toReal_apply, NNRealRMK.integral_rieszMeasure,
      coe_posPart, posPartFun_neg hb]
    ring
  have hint : ∀ (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (g : C_c(X, ℝ)),
      Integrable (fun x ↦ g x) μ := fun μ _ g ↦
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  rw [← CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg f, map_sub, hg, hg]
  simp only [CompactlySupportedContinuousMap.coe_sub, Pi.sub_apply]
  rw [integral_sub (hint _ _) (hint _ _), integral_sub (hint _ _) (hint _ _)]
  ring

end Jordan

/-! ### Step 2 (scalar): Riesz representation of an order-zero functional on `U` -/

section ScalarRiesz

variable {U : Set (Rn n)} {ℓ : (Rn n → ℝ) → ℝ}

private theorem isOrderBddAbove_extendLinear (hU : IsOpen U) (hℓ : IsOrderZero U ℓ) :
    IsOrderBddAbove (hℓ.extendLinear hU) := by
  intro g
  set K : Set (Rn n) := Subtype.val '' tsupport g
  have hK : IsCompact K := g.hasCompactSupport.image continuous_subtype_val
  have hKU : K ⊆ U := Subtype.coe_image_subset _ _
  obtain ⟨C, hC0, hC⟩ := hℓ.abs_extendFun_le hK hKU
  obtain ⟨M₀, hM₀⟩ :=
    g.toReal.continuous.bounded_above_of_compact_support g.toReal.hasCompactSupport
  set M := max M₀ 0
  have hM : ∀ x, ‖g.toReal x‖ ≤ M := fun x ↦ (hM₀ x).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  refine ⟨C * M, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  change hℓ.extendLinear hU h.toReal ≤ C * M
  rw [IsOrderZero.extendLinear_apply]
  have hts : tsupport (extendC h.toReal) ⊆ K := by
    rw [tsupport_extendC]
    refine image_mono (closure_mono fun x hx ↦ ?_)
    simp only [mem_support, CompactlySupportedContinuousMap.toReal_apply, ne_eq,
      NNReal.coe_eq_zero] at hx ⊢
    intro hg
    have := hh x
    rw [hg] at this
    exact hx (le_antisymm this zero_le)
  refine (le_abs_self _).trans (hC _ (continuous_extendC hU _) hts M fun x ↦ ?_)
  refine abs_extendC_le _ hM0 (fun y ↦ ?_) x
  have h1 := hM y
  have h2 := hh y
  simp only [CompactlySupportedContinuousMap.toReal_apply, Real.norm_eq_abs, NNReal.abs_eq] at h1 ⊢
  exact (NNReal.coe_le_coe.2 h2).trans h1

/-- **Scalar Riesz.** An order-zero functional on `C^∞_c(U)` is `∫ f dμ⁺ - ∫ f dμ⁻` for two Radon
measures on the open set `U`. -/
theorem IsOrderZero.exists_measures (hU : IsOpen U) (hℓ : IsOrderZero U ℓ) :
    ∃ μp μm : Measure U, μp.Regular ∧ μm.Regular ∧
      ∀ f, IsTestFunction U f → ℓ f = ∫ x : U, f x ∂μp - ∫ x : U, f x ∂μm := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  obtain ⟨μp, μm, hp, hm, h⟩ :=
    exists_measures_of_isOrderBddAbove (isOrderBddAbove_extendLinear hU hℓ)
  refine ⟨μp, μm, hp, hm, fun f hf ↦ ?_⟩
  have := h (restrictC f hf.1.continuous hf.2.1 hf.2.2)
  rw [IsOrderZero.extendLinear_apply, extendC_restrictC, hℓ.extendFun_eq hf] at this
  simpa using this

end ScalarRiesz

/-! ### Step 2 (vector): the Riesz pair -/

section VectorRiesz

variable {U : Set (Rn n)}

theorem IsSmoothTestField.add {φ ψ : Rn n → Rn n} (hφ : IsSmoothTestField U φ)
    (hψ : IsSmoothTestField U ψ) : IsSmoothTestField U (φ + ψ) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)⟩

theorem IsSmoothTestField.smul {φ : Rn n → Rn n} (hφ : IsSmoothTestField U φ) (c : ℝ) :
    IsSmoothTestField U (c • φ) :=
  ⟨hφ.1.const_smul c, hφ.2.1.smul_left (f := fun _ ↦ c),
    (tsupport_smul_subset_right (fun _ ↦ c) φ).trans hφ.2.2⟩

theorem IsSmoothTestField.neg {φ : Rn n → Rn n} (hφ : IsSmoothTestField U φ) :
    IsSmoothTestField U (-φ) := by
  simpa using hφ.smul (-1)

theorem IsSmoothTestField.sub {φ ψ : Rn n → Rn n} (hφ : IsSmoothTestField U φ)
    (hψ : IsSmoothTestField U ψ) : IsSmoothTestField U (φ - ψ) := by
  simpa [sub_eq_add_neg] using hφ.add hψ.neg

theorem isSmoothTestField_zero : IsSmoothTestField U (0 : Rn n → Rn n) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

theorem IsSmoothTestField.sum {ι : Type*} (s : Finset ι) {φ : ι → Rn n → Rn n}
    (hφ : ∀ i ∈ s, IsSmoothTestField U (φ i)) : IsSmoothTestField U (∑ i ∈ s, φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSmoothTestField_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hφ a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi))

theorem IsTestFunction.smul_const {f : Rn n → ℝ} (hf : IsTestFunction U f) (v : Rn n) :
    IsSmoothTestField U (fun x ↦ f x • v) :=
  ⟨hf.1.smul contDiff_const, hf.2.1.smul_right,
    (tsupport_smul_subset_left f (fun _ ↦ v)).trans hf.2.2⟩

theorem IsSmoothTestField.inner_left {φ : Rn n → Rn n} (hφ : IsSmoothTestField U φ) (v : Rn n) :
    IsTestFunction U (fun x ↦ ⟪v, φ x⟫) :=
  ⟨contDiff_const.inner ℝ hφ.1, hφ.2.1.comp_left (inner_zero_right v),
    (tsupport_comp_subset (inner_zero_right v) φ).trans hφ.2.2⟩

/-- `L` is an `ℝⁿ`-valued distribution of order zero on `U`, given on `C^∞_c(U; ℝⁿ)`: linear, and
bounded in the sup norm on the test fields supported in any fixed compact subset of `U`. -/
structure IsVecOrderZero (U : Set (Rn n)) (L : (Rn n → Rn n) → ℝ) : Prop where
  map_add : ∀ φ ψ, IsSmoothTestField U φ → IsSmoothTestField U ψ → L (φ + ψ) = L φ + L ψ
  map_smul : ∀ (c : ℝ) φ, IsSmoothTestField U φ → L (c • φ) = c * L φ
  bound : ∀ K, IsCompact K → K ⊆ U → ∃ C, ∀ φ, IsSmoothTestField U φ → tsupport φ ⊆ K →
    ∀ M, (∀ x, ‖φ x‖ ≤ M) → |L φ| ≤ C * M

namespace IsVecOrderZero

variable {L : (Rn n → Rn n) → ℝ}

theorem map_zero (hL : IsVecOrderZero U L) : L 0 = 0 := by
  have := hL.map_smul 0 0 isSmoothTestField_zero
  simpa using this

theorem map_sum (hL : IsVecOrderZero U L) {ι : Type*} (s : Finset ι) {φ : ι → Rn n → Rn n}
    (hφ : ∀ i ∈ s, IsSmoothTestField U (φ i)) : L (∑ i ∈ s, φ i) = ∑ i ∈ s, L (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hL.map_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hL.map_add _ _ (hφ a (Finset.mem_insert_self a s))
        (IsSmoothTestField.sum s fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hφ i (Finset.mem_insert_of_mem hi)]

/-- The scalar components `f ↦ L (f • v)` are order-zero functionals. -/
theorem isOrderZero_comp_smul (hL : IsVecOrderZero U L) (v : Rn n) (hv : ‖v‖ ≤ 1) :
    IsOrderZero U (fun f ↦ L (fun x ↦ f x • v)) where
  map_add f g hf hg := by
    rw [← hL.map_add _ _ (hf.smul_const v) (hg.smul_const v)]
    congr 1; funext x; simp [add_smul]
  map_smul c f hf := by
    rw [← hL.map_smul _ _ (hf.smul_const v)]
    congr 1; funext x; simp [smul_smul]
  bound K hK hKU := by
    obtain ⟨C, hC⟩ := hL.bound K hK hKU
    refine ⟨max C 0, fun f hf hfK M hM ↦ ?_⟩
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    refine (hC _ (hf.smul_const v) ((tsupport_smul_subset_left f _).trans hfK) M
      fun x ↦ ?_).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM0)
    rw [norm_smul, Real.norm_eq_abs]
    calc |f x| * ‖v‖ ≤ M * 1 := mul_le_mul (hM x) hv (norm_nonneg _) hM0
      _ = M := mul_one M

end IsVecOrderZero

/-- **Vector Riesz representation (EG Thm 1.38).** An `ℝⁿ`-valued distribution of order zero
on the open set `U` is represented by a Radon measure `μ` concentrated on `U` and a measurable
`μ`-a.e. unit vector field `ν`: `L φ = ∫ ⟪φ, ν⟫ dμ` for all `φ ∈ C^∞_c(U; ℝⁿ)`. Only bounds on
compact subsets of `U` are assumed (this is what the `BV_loc` form of EG Thm 5.1,
`hasLocallyFinitePerimeter_of_local`, needs). -/
theorem exists_rieszPair (hU : IsOpen U) {L : (Rn n → Rn n) → ℝ} (hL : IsVecOrderZero U L) :
    ∃ (μ : Measure (Rn n)) (ν : Rn n → Rn n), μ Uᶜ = 0 ∧
      (∀ K, IsCompact K → K ⊆ U → μ K < ⊤) ∧ Measurable ν ∧ (∀ᵐ x ∂μ, ‖ν x‖ = 1) ∧
      ∀ φ, IsSmoothTestField U φ → L φ = ∫ x, ⟪φ x, ν x⟫ ∂μ := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hcomp : ∀ i, IsOrderZero U (fun f ↦ L (fun x ↦ f x • b i)) := fun i ↦
    hL.isOrderZero_comp_smul (b i) (b.norm_eq_one i).le
  choose μp μm hp hm hrep using fun i ↦ (hcomp i).exists_measures hU
  -- the dominating measure
  set P : Measure U := ∑ i, (μp i + μm i) with hP
  have hPK : ∀ K : Set U, IsCompact K → P K < ⊤ := by
    intro K hK
    rw [hP, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.2 fun i _ ↦ by
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩
  have : IsFiniteMeasureOnCompacts P := ⟨hPK⟩
  have hpP : ∀ i, μp i ≤ P := fun i ↦ Measure.le_iff'.2 fun s ↦ by
    rw [hP, Measure.finsetSum_apply]
    refine le_trans ?_ (Finset.single_le_sum (f := fun j ↦ (μp j + μm j) s)
      (fun j _ ↦ zero_le) (Finset.mem_univ i))
    simp only [Measure.add_apply]
    exact le_self_add
  have hmP : ∀ i, μm i ≤ P := fun i ↦ Measure.le_iff'.2 fun s ↦ by
    rw [hP, Measure.finsetSum_apply]
    refine le_trans ?_ (Finset.single_le_sum (f := fun j ↦ (μp j + μm j) s)
      (fun j _ ↦ zero_le) (Finset.mem_univ i))
    simp only [Measure.add_apply]
    exact le_add_self
  -- the densities
  set σc : Fin n → U → ℝ := fun i x ↦
    ((μp i).rnDeriv P x).toReal - ((μm i).rnDeriv P x).toReal with hσc
  have hσc_meas : ∀ i, Measurable (σc i) := fun i ↦
    ((μp i).measurable_rnDeriv P).ennreal_toReal.sub ((μm i).measurable_rnDeriv P).ennreal_toReal
  have hσc_bd : ∀ i, ∀ᵐ x ∂P, |σc i x| ≤ 1 := by
    intro i
    filter_upwards [Measure.rnDeriv_le_one_of_le (hpP i), Measure.rnDeriv_le_one_of_le (hmP i)]
      with x h1 h2
    have a1 : ((μp i).rnDeriv P x).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h1)
    have a2 : ((μm i).rnDeriv P x).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h2)
    have b1 := ENNReal.toReal_nonneg (a := (μp i).rnDeriv P x)
    have b2 := ENNReal.toReal_nonneg (a := (μm i).rnDeriv P x)
    rw [hσc, abs_le]
    constructor <;> linarith
  have hfint : ∀ f, IsTestFunction U f → ∀ (μ : Measure U) [IsFiniteMeasureOnCompacts μ],
      Integrable (fun x : U ↦ f x) μ := fun f hf μ _ ↦
    (restrictC f hf.1.continuous hf.2.1 hf.2.2).continuous.integrable_of_hasCompactSupport
      (restrictC f hf.1.continuous hf.2.1 hf.2.2).hasCompactSupport
  have hint_p : ∀ i f, IsTestFunction U f →
      Integrable (fun x : U ↦ ((μp i).rnDeriv P x).toReal • f x) P := fun i f hf ↦
    (integrable_rnDeriv_smul_iff (Measure.absolutelyContinuous_of_le (hpP i))).2
      (hfint f hf (μp i))
  have hint_m : ∀ i f, IsTestFunction U f →
      Integrable (fun x : U ↦ ((μm i).rnDeriv P x).toReal • f x) P := fun i f hf ↦
    (integrable_rnDeriv_smul_iff (Measure.absolutelyContinuous_of_le (hmP i))).2
      (hfint f hf (μm i))
  have hσc_int : ∀ i f, IsTestFunction U f → Integrable (fun x : U ↦ σc i x * f x) P := by
    intro i f hf
    refine ((hint_p i f hf).sub (hint_m i f hf)).congr (ae_of_all _ fun x ↦ ?_)
    simp only [hσc, smul_eq_mul, Pi.sub_apply]
    ring
  have hσc_rep : ∀ i f, IsTestFunction U f →
      L (fun x ↦ f x • b i) = ∫ x : U, σc i x * f x ∂P := by
    intro i f hf
    rw [hrep i f hf, ← integral_rnDeriv_smul (Measure.absolutelyContinuous_of_le (hpP i)),
      ← integral_rnDeriv_smul (Measure.absolutelyContinuous_of_le (hmP i)),
      ← integral_sub (hint_p i f hf) (hint_m i f hf)]
    congr 1; funext x
    simp only [hσc, smul_eq_mul]
    ring
  -- the vector density
  set σ : U → Rn n := fun x ↦ ∑ i, σc i x • b i with hσ
  have hσ_meas : Measurable σ :=
    Finset.measurable_sum _ fun i _ ↦ (hσc_meas i).smul_const (b i)
  have hσ_bd : ∀ᵐ x ∂P, ‖σ x‖ ≤ n := by
    filter_upwards [ae_all_iff.2 hσc_bd] with x hx
    calc ‖σ x‖ ≤ ∑ i, ‖σc i x • b i‖ := norm_sum_le _ _
      _ = ∑ i, |σc i x| := by simp [norm_smul, b.norm_eq_one]
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hx i
      _ = n := by simp
  set νU : U → Rn n := fun x ↦ ‖σ x‖⁻¹ • σ x with hνU
  have hνU_meas : Measurable νU := (hσ_meas.norm.inv).smul hσ_meas
  set m : Measure U := P.withDensity (fun x ↦ (‖σ x‖₊ : ℝ≥0∞)) with hm_def
  have hemb : MeasurableEmbedding (Subtype.val : U → Rn n) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  refine ⟨m.map Subtype.val, Subtype.val.extend νU 0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hemb.map_apply]
    convert measure_empty (μ := m)
    ext x; simp
  · intro K hK hKU
    rw [hemb.map_apply]
    have hKm : MeasurableSet ((Subtype.val : U → Rn n) ⁻¹' K) :=
      hK.isClosed.measurableSet.preimage measurable_subtype_coe
    rw [hm_def, withDensity_apply _ hKm]
    calc ∫⁻ x in Subtype.val ⁻¹' K, (‖σ x‖₊ : ℝ≥0∞) ∂P
        ≤ ∫⁻ _x in Subtype.val ⁻¹' K, (n : ℝ≥0∞) ∂P := by
          refine lintegral_mono_ae (ae_restrict_of_ae ?_)
          filter_upwards [hσ_bd] with x hx
          have : (‖σ x‖₊ : ℝ≥0) ≤ n := by rw [← NNReal.coe_le_coe]; simpa using hx
          exact_mod_cast this
      _ = n * P (Subtype.val ⁻¹' K) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top (by simp) (hPK _ (isCompact_preimage_val hK hKU))
  · exact hemb.measurable_extend hνU_meas measurable_const
  · rw [hemb.ae_map_iff]
    simp_rw [Subtype.val_injective.extend_apply]
    rw [hm_def, ae_withDensity_iff (by fun_prop)]
    refine ae_of_all _ fun x hx ↦ ?_
    have hσx : σ x ≠ 0 := by simpa using hx
    rw [hνU, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hσx)]
  · intro φ hφ
    rw [hemb.integral_map]
    simp_rw [Subtype.val_injective.extend_apply]
    rw [hm_def, integral_withDensity_eq_integral_smul hσ_meas.nnnorm]
    have hpt : ∀ x : U, (‖σ x‖₊ : ℝ≥0) • ⟪φ x, νU x⟫ = ∑ i, σc i x * ⟪b i, φ x⟫ := by
      intro x
      have h1 : (‖σ x‖₊ : ℝ≥0) • ⟪φ x, νU x⟫ = ⟪φ x, σ x⟫ := by
        rw [NNReal.smul_def, smul_eq_mul, coe_nnnorm, hνU, real_inner_smul_right]
        rcases eq_or_ne (σ x) 0 with h | h
        · simp [h]
        · field_simp
      rw [h1, hσ, inner_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [real_inner_smul_right, real_inner_comm]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ ↦ hσc_int i _ (hφ.inner_left (b i))]
    rw [← Finset.sum_congr rfl fun i _ ↦ hσc_rep i _ (hφ.inner_left (b i)),
      ← hL.map_sum _ fun i _ ↦ (hφ.inner_left (b i)).smul_const (b i)]
    congr 1
    funext x
    rw [Finset.sum_apply]
    exact (b.sum_repr' (φ x)).symm

end VectorRiesz

end GMTFoundations
