/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Statements.Perimeter
public import GMTFoundations.Perimeter.GaussGreenPair
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Sheaf.Basic

/-!
# Locally finite perimeter from local divergence bounds

`hasLocallyFinitePerimeter_of_local` proves `LocallyFinitePerimeterOfLocalStatement`
(`Statements/Perimeter.lean`): Thm 5.1 of L. C. Evans, R. F. Gariepy, *Measure Theory and Fine
Properties of Functions*, rev. ed., CRC Press, 2015 (EG), in its `BV_loc` form.

Proof: a finite cover of a compact `K ⊆ U` by the balls of the hypothesis and a smooth partition
of unity subordinate to it (Mathlib `SmoothPartitionOfUnity.exists_isSubordinate`) turn the local
bounds into a bound on `K` (`bound_of_local`). Then `exists_isGaussGreenPair_of_bound`
(`Perimeter/GaussGreenPair.lean`), whose Riesz construction (`exists_rieszPair`) needs only bounds
on compact subsets of `U`.
-/

open MeasureTheory Metric Set Filter Topology Function
open scoped NNReal ENNReal RealInnerProductSpace Manifold ContDiff

public section

namespace GMTFoundations

variable {n : ℕ}

/-- Local bounds on balls give a bound on each compact subset of `U` (finite cover and a smooth
partition of unity). -/
theorem bound_of_local {U E : Set (Rn n)}
    (h : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∃ C : ℝ, ∀ φ : Rn n → Rn n,
      IsSmoothTestField (ball x r) φ → |∫ y in E, divergence φ y| ≤ C * ⨆ y, ‖φ y‖)
    (K : Set (Rn n)) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ φ, IsSmoothTestField U φ → tsupport φ ⊆ K →
      ∀ M, (∀ x, ‖φ x‖ ≤ M) → |∫ x in E, divergence φ x| ≤ C * M := by
  classical
  choose! r hr hrU C hC using h
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K ↦ ball (x : Rn n) (r x))
    (fun _ ↦ isOpen_ball) (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr x (hKU hx))⟩)
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Rn n) hK.isClosed
    (fun i : t ↦ ball ((i : K) : Rn n) (r i)) (fun _ ↦ isOpen_ball)
    (by rw [iUnion_subtype]; exact ht)
  refine ⟨∑ i : t, max (C ((i : K) : Rn n)) 0, fun φ hφ hφK M hM ↦ ?_⟩
  have hfs : ∀ i : t, ContDiff ℝ ∞ (f i) := fun i ↦ contMDiff_iff_contDiff.1 (f i).contMDiff
  have hterm : ∀ i : t,
      IsSmoothTestField (ball ((i : K) : Rn n) (r i)) (fun x ↦ f i x • φ x) := by
    intro i
    refine ⟨(hfs i).smul hφ.1, ?_, ?_⟩
    · exact HasCompactSupport.smul_left (f := fun x ↦ f i x) hφ.2.1
    · exact (tsupport_smul_subset_left (fun x ↦ f i x) φ).trans (hf i)
  have hdecomp : φ = ∑ i : t, fun x ↦ f i x • φ x := by
    funext x
    rw [Finset.sum_apply, ← Finset.sum_smul]
    by_cases hx : x ∈ K
    · rw [← finsum_eq_sum_of_fintype, f.sum_eq_one hx, one_smul]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hφK h')
      simp [this]
  have hU' : ∀ i : t, IsSmoothTestField U (fun x ↦ f i x • φ x) := fun i ↦
    ⟨(hterm i).1, (hterm i).2.1, (hterm i).2.2.trans (hrU _ (hKU (i : K).2))⟩
  rw [hdecomp, integral_divergence_finsetSum _ fun i _ ↦ hU' i]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ abs_le_of_le_mul_iSup (hC _ (hKU (i : K).2) _ (hterm i))
    fun x ↦ ?_
  rw [norm_smul, Real.norm_of_nonneg (f.nonneg i x)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (f.le_one i x)).trans (hM x)

/-- EG Thm 5.1 (`BV_loc` form), for `f = χ_E`. -/
theorem hasLocallyFinitePerimeter_of_local :
    LocallyFinitePerimeterOfLocalStatement n := by
  intro _ U E hU _ h
  exact exists_isGaussGreenPair_of_bound hU (bound_of_local h)

end GMTFoundations
