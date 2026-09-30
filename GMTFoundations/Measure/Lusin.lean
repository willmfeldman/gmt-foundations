/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Lusin's theorem (continuity form)

Evans–Gariepy Thm 1.14: a measurable map `g` is continuous on a compact set that exhausts a set
`A` of finite measure up to `ε`. The pinned Mathlib has no statement of this form (only the
Lusin–Souslin theorem on images of Borel sets).

## Main results

* `Measurable.exists_isCompact_continuousOn`: for a measure `μ` that is inner regular with respect
  to compact sets on sets of finite measure (`μ.InnerRegularCompactLTTop`), a measurable
  `g : X → Y` into a second-countable space, a measurable `A` with `μ A ≠ ∞` and `ε ≠ 0`, there is
  a compact `K ⊆ A` with `μ (A \ K) < ε` and `ContinuousOn g K`.
* `AEMeasurable.exists_isCompact_continuousOn`: the same for `g` a.e.-measurable and `A`
  null-measurable (Evans–Gariepy's "µ-measurable").

On `ℝⁿ` (indeed on any complete second-countable pseudo-metrizable space) every Borel measure is
`InnerRegularCompactLTTop` (Mathlib instance
`instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace`), so no Radon hypothesis is
needed there; in particular these results apply to the measure of a Gauss–Green pair.

## Proof

Not Evans–Gariepy's proof (which partitions `ℝᵐ` into small Borel pieces and uses uniform
limits). Instead: for each set `V` of a countable basis of `Y`, choose compact `F_V ⊆ A ∩ g⁻¹ V` and
`G_V ⊆ A \ g⁻¹ V` exhausting these sets up to `δ_V`, with `∑ δ < ε`. On
`K := K₀ ∩ ⋂_V (F_V ∪ G_V)` one has `g⁻¹ V ∩ K = G_Vᶜ ∩ K`, which is relatively open, so `g` is
continuous on `K`. This is the standard proof of Lusin's theorem for second-countable targets.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

public section

section Lusin

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [μ.InnerRegularCompactLTTop]
  [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]

/-- **Lusin's theorem** (Evans–Gariepy Thm 1.14). A measurable map into a second-countable space
is continuous on a compact subset `K` of `A` with `μ (A \ K) < ε`, for any measurable `A` of finite
measure and any `ε ≠ 0`. -/
theorem Measurable.exists_isCompact_continuousOn {g : X → Y} (hg : Measurable g) {A : Set X}
    (hA : MeasurableSet A) (hμA : μ A ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ A, IsCompact K ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  classical
  set b := countableBasis Y
  have : Countable b := (countable_countableBasis Y).to_subtype
  -- The sets to approximate: `A`, and `A ∩ g⁻¹ V`, `A \ g⁻¹ V` for each basic open `V`.
  let S : Option (b × Bool) → Set X
    | none => A
    | some (V, true) => A ∩ g ⁻¹' (V : Set Y)
    | some (V, false) => A \ g ⁻¹' (V : Set Y)
  have hVm : ∀ V : b, MeasurableSet (g ⁻¹' (V : Set Y)) := fun V =>
    hg (isOpen_of_mem_countableBasis V.2).measurableSet
  have hSA : ∀ j, S j ⊆ A := by
    rintro (_ | ⟨V, _ | _⟩)
    exacts [subset_rfl, sdiff_subset, inter_subset_left]
  have hSm : ∀ j, MeasurableSet (S j) := by
    rintro (_ | ⟨V, _ | _⟩)
    exacts [hA, hA.diff (hVm V), hA.inter (hVm V)]
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.exists_pos_sum_of_countable hε (Option (b × Bool))
  have hK : ∀ j, ∃ K ⊆ S j, IsCompact K ∧ μ (S j \ K) < δ j := fun j =>
    (hSm j).exists_isCompact_sdiff_lt (ne_top_of_le_ne_top hμA (measure_mono (hSA j)))
      (ENNReal.coe_pos.2 (hδ0 j)).ne'
  choose C hCS hCc hCμ using hK
  set F : b → Set X := fun V => C (some (V, true))
  set G : b → Set X := fun V => C (some (V, false))
  refine ⟨C none ∩ ⋂ V : b, (F V ∪ G V), inter_subset_left.trans (hCS none),
    (hCc none).inter_right (isClosed_iInter fun V =>
      (hCc (some (V, true))).isClosed.union (hCc (some (V, false))).isClosed), ?_, ?_⟩
  · -- measure estimate
    have hsub : A \ (C none ∩ ⋂ V : b, (F V ∪ G V)) ⊆ ⋃ j, (S j \ C j) := by
      rintro x ⟨hxA, hxK⟩
      rw [mem_inter_iff, not_and_or, mem_iInter, not_forall] at hxK
      rcases hxK with hx0 | ⟨V, hxV⟩
      · exact mem_iUnion.2 ⟨none, hxA, hx0⟩
      · rw [mem_union, not_or] at hxV
        by_cases hgV : g x ∈ (V : Set Y)
        · exact mem_iUnion.2 ⟨some (V, true), ⟨hxA, hgV⟩, hxV.1⟩
        · exact mem_iUnion.2 ⟨some (V, false), ⟨hxA, hgV⟩, hxV.2⟩
    calc μ (A \ (C none ∩ ⋂ V : b, (F V ∪ G V))) ≤ μ (⋃ j, (S j \ C j)) := measure_mono hsub
      _ ≤ ∑' j, μ (S j \ C j) := measure_iUnion_le _
      _ ≤ ∑' j, (δ j : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j => (hCμ j).le
      _ < ε := hδ
  · -- continuity: `g⁻¹ t ∩ K = (⋃_{V ⊆ t} G_Vᶜ) ∩ K`
    rw [continuousOn_iff']
    intro t ht
    refine ⟨⋃ (V : b) (_ : (V : Set Y) ⊆ t), (G V)ᶜ,
      isOpen_iUnion fun V => isOpen_iUnion fun _ => (hCc (some (V, false))).isClosed.isOpen_compl,
      ?_⟩
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, mem_compl_iff, exists_prop]
    constructor
    · rintro ⟨hxt, hxK⟩
      obtain ⟨V, hVb, hxV, hVt⟩ := (isBasis_countableBasis Y).exists_subset_of_mem_open hxt ht
      refine ⟨⟨⟨V, hVb⟩, hVt, fun hxG => ?_⟩, hxK⟩
      exact (hCS (some (⟨V, hVb⟩, false)) hxG).2 hxV
    · rintro ⟨⟨V, hVt, hxG⟩, hxK⟩
      refine ⟨?_, hxK⟩
      have hxFG := mem_iInter.1 hxK.2 V
      rcases hxFG with hxF | hxG'
      · exact hVt (hCS (some (V, true)) hxF).2
      · exact absurd hxG' hxG

/-- **Lusin's theorem** (Evans–Gariepy Thm 1.14) for an a.e.-measurable map and a
null-measurable set `A` of finite measure. -/
theorem AEMeasurable.exists_isCompact_continuousOn
    {g : X → Y} (hg : AEMeasurable g μ) {A : Set X} (hA : NullMeasurableSet A μ) (hμA : μ A ≠ ∞)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ A, IsCompact K ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  -- A measurable `A' ⊆ A`, a.e. equal to `A`, on which `g` agrees with its measurable version.
  obtain ⟨A₀, hA₀A, hA₀m, hA₀ae⟩ := hA.exists_measurable_subset_ae_eq
  set N := toMeasurable μ {x | g x ≠ hg.mk g x}
  have hN0 : μ N = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.1 hg.ae_eq_mk
  set A' := A₀ \ N
  have hA'm : MeasurableSet A' := hA₀m.diff (measurableSet_toMeasurable _ _)
  obtain ⟨K, hKA', hKc, hKμ, hKg⟩ := hg.measurable_mk.exists_isCompact_continuousOn (μ := μ)
    hA'm (ne_top_of_le_ne_top hμA (measure_mono (sdiff_subset.trans hA₀A))) hε
  refine ⟨K, hKA'.trans (sdiff_subset.trans hA₀A), hKc, ?_, ?_⟩
  · calc μ (A \ K) ≤ μ ((A \ A₀) ∪ N ∪ (A' \ K)) := by
          refine measure_mono fun x ⟨hxA, hxK⟩ => ?_
          by_cases hx₀ : x ∈ A₀
          · by_cases hxN : x ∈ N
            · exact Or.inl (Or.inr hxN)
            · exact Or.inr ⟨⟨hx₀, hxN⟩, hxK⟩
          · exact Or.inl (Or.inl ⟨hxA, hx₀⟩)
      _ ≤ μ ((A \ A₀) ∪ N) + μ (A' \ K) := measure_union_le _ _
      _ ≤ μ (A \ A₀) + μ N + μ (A' \ K) := by gcongr; exact measure_union_le _ _
      _ = μ (A' \ K) := by
          rw [hN0, add_zero, ae_eq_set.1 hA₀ae.symm |>.1, zero_add]
      _ < ε := hKμ
  · refine hKg.congr fun x hx => ?_
    have hxN : x ∉ N := (hKA' hx).2
    by_contra hne
    exact hxN (subset_toMeasurable _ _ hne)

end Lusin
