/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.Beta
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Best planes, center of mass and Jensen

If `0 < r` and `μ(B_r(x)) < ∞`, the infimum defining `jonesBetaSq μ x r` is attained. The optimal
offset is the center of mass `m` of `μ⌊B_r(x)`: for every normal `ν`,
`∫_B ⟪y − p, ν⟫² = ∫_B ⟪y − m, ν⟫² + μ(B) ⟪m − p, ν⟫²` (`integral_inner_sq_eq`), so it suffices
to minimize the continuous function `ν ↦ ∫_B ⟪y − m, ν⟫²` over the compact unit sphere. (For
hyperplanes the compactness of the Grassmannian used in the sources becomes compactness of the unit
sphere of normals.)

## Main definitions

* `centerOfMass μ B = μ(B)⁻¹ ∫_B y dμ(y)`.
* `bestPlane μ x r : Rn n × Rn n`, a minimizing plane (defined by choice).

## Main statements

* `norm_centerOfMass_sub_le` (J1): `‖m − c‖ ≤ t` when `B ⊆ closedBall c t`.
* `sq_inner_centerOfMass_le` (J2): `⟪m − p, ν⟫² μ(B) ≤ ∫_B ⟪y − p, ν⟫² dμ` for every `p, ν`.
* `norm_bestPlane_snd`, `bestPlane_spec`, and (BP) `lintegral_bestPlane`:
  `∫_{B_r(x)} ⟪y − p, ν⟫² dμ = r^{n+1} β²(x, r)` for `(p, ν) = bestPlane μ x r`.
* `jonesBetaSq_ne_top`: `β²(x, r) < ∞` when `r > 0` and `μ(B_r(x)) < ∞`.

## References

* [NV] A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and
  minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227, §4.2 (best `L²` planes).
* [Miś] M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43
  (2018); arXiv:1612.02461, §3 (existence of `L^q`-best planes by compactness).
-/

public noncomputable section

namespace GMTFoundations

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

/-- The center of mass `μ(B)⁻¹ ∫_B y dμ(y)` of `μ⌊B`. -/
@[expose] def centerOfMass (μ : Measure (Rn n)) (B : Set (Rn n)) : Rn n :=
  (μ.real B)⁻¹ • ∫ y in B, y ∂μ

section CenterOfMass

variable {μ : Measure (Rn n)} {B : Set (Rn n)} {c : Rn n} {t : ℝ}

/-- Continuous functions are integrable on a bounded measurable set of finite measure. -/
private lemma integrableOn_of_continuous {E : Type*} [NormedAddCommGroup E] {f : Rn n → E}
    (hf : Continuous f) (hB : MeasurableSet B) (hsub : B ⊆ closedBall c t) (hfin : μ B ≠ ∞) :
    IntegrableOn f B μ := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall c t).exists_bound_of_continuousOn hf.continuousOn
  exact Measure.integrableOn_of_bounded hfin hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem hB fun y hy => hK y (hsub hy))

/-- `⟪m − p, ν⟫ μ(B) = ∫_B ⟪y − p, ν⟫ dμ(y)`: inner product with `ν` commutes with the average. -/
theorem inner_centerOfMass_sub_mul (hB : MeasurableSet B) (hsub : B ⊆ closedBall c t)
    (hfin : μ B ≠ ∞) (h0 : μ B ≠ 0) (p ν : Rn n) :
    ⟪centerOfMass μ B - p, ν⟫ * μ.real B = ∫ y in B, ⟪y - p, ν⟫ ∂μ := by
  have hpos : 0 < μ.real B := ENNReal.toReal_pos h0 hfin
  have hI : IntegrableOn (fun y : Rn n => y) B μ :=
    integrableOn_of_continuous continuous_id hB hsub hfin
  have h1 : ∫ y in B, ⟪y - p, ν⟫ ∂μ = ⟪∫ y in B, y ∂μ, ν⟫ - μ.real B * ⟪p, ν⟫ := by
    have hI1 : Integrable (fun y : Rn n => ⟪y, ν⟫) (μ.restrict B) := hI.inner_const ν
    have hI2 : Integrable (fun _ : Rn n => ⟪p, ν⟫) (μ.restrict B) := integrableOn_const hfin
    simp_rw [inner_sub_left]
    rw [integral_sub hI1 hI2, setIntegral_const, smul_eq_mul]
    congr 1
    simp_rw [real_inner_comm ν]
    exact integral_inner hI ν
  rw [h1, centerOfMass, inner_sub_left, real_inner_smul_left, sub_mul, mul_right_comm,
    inv_mul_cancel₀ hpos.ne', one_mul, mul_comm]

/-- (J1) If `B ⊆ closedBall c t`, the center of mass of `μ⌊B` lies in `closedBall c t`. -/
theorem norm_centerOfMass_sub_le (hB : MeasurableSet B) (hsub : B ⊆ closedBall c t)
    (hfin : μ B ≠ ∞) (h0 : μ B ≠ 0) : ‖centerOfMass μ B - c‖ ≤ t := by
  have hpos : 0 < μ.real B := ENNReal.toReal_pos h0 hfin
  have hI : IntegrableOn (fun y : Rn n => y) B μ :=
    integrableOn_of_continuous continuous_id hB hsub hfin
  have heq : centerOfMass μ B - c = (μ.real B)⁻¹ • ∫ y in B, (y - c) ∂μ := by
    rw [integral_sub hI (integrableOn_const (C := c) hfin), setIntegral_const, smul_sub, smul_smul,
      inv_mul_cancel₀ hpos.ne', one_smul, centerOfMass]
  have hbd : ‖∫ y in B, (y - c) ∂μ‖ ≤ t * μ.real B :=
    norm_setIntegral_le_of_norm_le_const hfin.lt_top fun y hy => mem_closedBall_iff_norm.1 (hsub hy)
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), inv_mul_le_iff₀ hpos,
    mul_comm]
  exact hbd

/-- Variance decomposition: for every plane `(p, ν)`,
`∫_B ⟪y − p, ν⟫² = ∫_B ⟪y − m, ν⟫² + μ(B) ⟪m − p, ν⟫²`, where `m` is the center of mass. -/
theorem integral_inner_sq_eq (hB : MeasurableSet B) (hsub : B ⊆ closedBall c t)
    (hfin : μ B ≠ ∞) (h0 : μ B ≠ 0) (p ν : Rn n) :
    ∫ y in B, ⟪y - p, ν⟫ ^ 2 ∂μ =
      ∫ y in B, ⟪y - centerOfMass μ B, ν⟫ ^ 2 ∂μ + μ.real B * ⟪centerOfMass μ B - p, ν⟫ ^ 2 := by
  set m := centerOfMass μ B
  have hsplit : ∀ y : Rn n, ⟪y - p, ν⟫ ^ 2 =
      (⟪y - m, ν⟫ ^ 2 + 2 * ⟪m - p, ν⟫ * ⟪y - m, ν⟫) + ⟪m - p, ν⟫ ^ 2 := by
    intro y
    have : y - p = (y - m) + (m - p) := by abel
    rw [this, inner_add_left]; ring
  have hg : ∫ y in B, ⟪y - m, ν⟫ ∂μ = 0 := by
    rw [← inner_centerOfMass_sub_mul hB hsub hfin h0, sub_self, inner_zero_left, zero_mul]
  have i1 : IntegrableOn (fun y : Rn n => ⟪y - m, ν⟫ ^ 2) B μ :=
    integrableOn_of_continuous (by fun_prop) hB hsub hfin
  have i2 : IntegrableOn (fun y : Rn n => 2 * ⟪m - p, ν⟫ * ⟪y - m, ν⟫) B μ :=
    integrableOn_of_continuous (by fun_prop) hB hsub hfin
  have i3 : IntegrableOn (fun _ : Rn n => ⟪m - p, ν⟫ ^ 2) B μ := integrableOn_const hfin
  rw [show (fun y : Rn n => ⟪y - p, ν⟫ ^ 2) = fun y =>
      (⟪y - m, ν⟫ ^ 2 + 2 * ⟪m - p, ν⟫ * ⟪y - m, ν⟫) + ⟪m - p, ν⟫ ^ 2 from funext hsplit]
  have i12 : Integrable (fun y : Rn n => ⟪y - m, ν⟫ ^ 2 + 2 * ⟪m - p, ν⟫ * ⟪y - m, ν⟫)
      (μ.restrict B) := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, setIntegral_const,
    integral_const_mul, hg, smul_eq_mul]
  ring

/-- `∫⁻_B ofReal (⟪y − p, ν⟫²) = ofReal (∫_B ⟪y − p, ν⟫²)` on bounded sets of finite measure. -/
theorem lintegral_inner_sq_eq_ofReal (hB : MeasurableSet B) (hsub : B ⊆ closedBall c t)
    (hfin : μ B ≠ ∞) (p ν : Rn n) :
    ∫⁻ y in B, ENNReal.ofReal (⟪y - p, ν⟫ ^ 2) ∂μ = ENNReal.ofReal (∫ y in B, ⟪y - p, ν⟫ ^ 2 ∂μ) :=
  (ofReal_integral_eq_lintegral_ofReal (integrableOn_of_continuous (by fun_prop) hB hsub hfin)
    (Eventually.of_forall fun _ => sq_nonneg _)).symm

/-- (J2) Jensen for the center of mass: `⟪m − p, ν⟫² μ(B) ≤ ∫_B ⟪y − p, ν⟫² dμ` for every `p` and
every vector `ν` (unit or not). -/
theorem sq_inner_centerOfMass_le (hB : MeasurableSet B) (hsub : B ⊆ closedBall c t)
    (hfin : μ B ≠ ∞) (h0 : μ B ≠ 0) (p ν : Rn n) :
    ENNReal.ofReal (⟪centerOfMass μ B - p, ν⟫ ^ 2) * μ B ≤
      ∫⁻ y in B, ENNReal.ofReal (⟪y - p, ν⟫ ^ 2) ∂μ := by
  rw [lintegral_inner_sq_eq_ofReal hB hsub hfin, integral_inner_sq_eq hB hsub hfin h0,
    ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (sq_nonneg _), ← Measure.real, mul_comm]
  exact ENNReal.ofReal_le_ofReal
    (le_add_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _))

end CenterOfMass

/-! ### Best planes -/

/-- The integral in `planeBetaSq` is finite on a ball of finite measure. -/
theorem planeBetaSq_ne_top (hn : 1 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} (hr : 0 < r)
    (hfin : μ (ball x r) ≠ ∞) (P : Rn n × Rn n) : planeBetaSq μ x r P ≠ ∞ := by
  rw [planeBetaSq_eq hn hr,
    lintegral_inner_sq_eq_ofReal measurableSet_ball ball_subset_closedBall hfin]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

private lemma exists_unit (hn : 1 ≤ n) : ∃ e : Rn n, ‖e‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩

/-- `β²(x, r) < ∞` when `r > 0` and `μ(B_r(x)) < ∞`. -/
theorem jonesBetaSq_ne_top (hn : 1 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} (hr : 0 < r)
    (hfin : μ (ball x r) ≠ ∞) : jonesBetaSq μ x r ≠ ∞ := by
  obtain ⟨e, he⟩ := exists_unit hn
  exact ne_top_of_le_ne_top (planeBetaSq_ne_top hn hr hfin (0, e))
    (jonesBetaSq_le_planeBetaSq (P := (0, e)) he)

/-- Attainment of the infimum defining `jonesBetaSq`. For `n ≥ 1` there is a unit plane
which, whenever `r > 0` and `μ(B_r(x)) < ∞`, realizes `β²(x, r)`. -/
theorem exists_bestPlane (hn : 1 ≤ n) (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) :
    ∃ P : Rn n × Rn n, ‖P.2‖ = 1 ∧
      (0 < r → μ (ball x r) ≠ ∞ → planeBetaSq μ x r P = jonesBetaSq μ x r) := by
  obtain ⟨e, he⟩ := exists_unit hn
  by_cases hr : 0 < r
  swap
  · exact ⟨(0, e), he, fun h => absurd h hr⟩
  by_cases hfin : μ (ball x r) = ∞
  · exact ⟨(0, e), he, fun _ h => absurd hfin h⟩
  by_cases h0 : μ (ball x r) = 0
  · refine ⟨(0, e), he, fun _ _ => le_antisymm ?_ (jonesBetaSq_le_planeBetaSq he)⟩
    have : planeBetaSq μ x r (0, e) = 0 := by
      simp [planeBetaSq, Measure.restrict_eq_zero.2 h0]
    rw [this]
    exact zero_le
  -- The main case `0 < μ(B) < ∞`.
  have hB : MeasurableSet (ball x r) := measurableSet_ball
  have hsub : ball x r ⊆ closedBall x r := ball_subset_closedBall
  set m := centerOfMass μ (ball x r) with hm_def
  have hm : ‖m - x‖ ≤ r := norm_centerOfMass_sub_le hB hsub hfin h0
  set Q : Rn n → ℝ := fun ν => ∫ y in ball x r, ⟪y - m, ν⟫ ^ 2 ∂μ with hQ_def
  have hQ : ContinuousOn Q (sphere 0 1) := by
    refine continuousOn_of_dominated (bound := fun _ => (2 * r) ^ 2) ?_ ?_ ?_ ?_
    · intro ν _
      exact (by fun_prop : Continuous fun y : Rn n => ⟪y - m, ν⟫ ^ 2).aestronglyMeasurable
    · intro ν hν
      refine ae_restrict_of_forall_mem hB fun y hy => ?_
      have hν1 : ‖ν‖ = 1 := by simpa using hν
      have hy' : ‖y - m‖ ≤ 2 * r := by
        have : ‖y - x‖ < r := by simpa [dist_eq_norm] using hy
        calc ‖y - m‖ = ‖(y - x) - (m - x)‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖m - x‖ := norm_sub_le _ _
          _ ≤ 2 * r := by linarith
      have hin : |⟪y - m, ν⟫| ≤ 2 * r := by
        calc |⟪y - m, ν⟫| ≤ ‖y - m‖ * ‖ν‖ := abs_real_inner_le_norm _ _
          _ ≤ 2 * r := by rw [hν1, mul_one]; exact hy'
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hin 2
    · exact integrableOn_const hfin
    · exact Eventually.of_forall fun y =>
        (by fun_prop : Continuous fun ν : Rn n => ⟪y - m, ν⟫ ^ 2).continuousOn
  obtain ⟨ν₀, hν₀, hmin⟩ :=
    (isCompact_sphere (0 : Rn n) 1).exists_isMinOn ⟨e, by simpa using he⟩ hQ
  have hν₀1 : ‖ν₀‖ = 1 := by simpa using hν₀
  refine ⟨(m, ν₀), hν₀1, fun _ _ => le_antisymm ?_ (jonesBetaSq_le_planeBetaSq hν₀1)⟩
  refine le_jonesBetaSq fun P hP => ?_
  rw [planeBetaSq_eq hn hr, planeBetaSq_eq hn hr]
  refine mul_le_mul_right ?_ _
  rw [lintegral_inner_sq_eq_ofReal hB hsub hfin, lintegral_inner_sq_eq_ofReal hB hsub hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∫ y in ball x r, ⟪y - m, ν₀⟫ ^ 2 ∂μ = Q ν₀ := rfl
    _ ≤ Q P.2 := isMinOn_iff.1 hmin _ (by simpa using hP)
    _ ≤ ∫ y in ball x r, ⟪y - P.1, P.2⟫ ^ 2 ∂μ := by
        rw [integral_inner_sq_eq hB hsub hfin h0 P.1 P.2]
        exact le_add_of_nonneg_right (by positivity)

open Classical in
/-- A best plane for `β²(x, r)`: a plane `(p, ν)` with `‖ν‖ = 1` attaining the infimum in
`jonesBetaSq μ x r` whenever `r > 0` and `μ(B_r(x)) < ∞` (`bestPlane_spec`). Defined by choice;
it is `0` only in the degenerate dimension `n = 0`. -/
def bestPlane (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) : Rn n × Rn n :=
  if h : ∃ P : Rn n × Rn n, ‖P.2‖ = 1 ∧
      (0 < r → μ (ball x r) ≠ ∞ → planeBetaSq μ x r P = jonesBetaSq μ x r) then
    h.choose
  else 0

private lemma bestPlane_prop (hn : 1 ≤ n) (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) :
    ‖(bestPlane μ x r).2‖ = 1 ∧
      (0 < r → μ (ball x r) ≠ ∞ → planeBetaSq μ x r (bestPlane μ x r) = jonesBetaSq μ x r) := by
  have h := exists_bestPlane hn μ x r
  rw [bestPlane, dif_pos h]
  exact h.choose_spec

/-- The normal of `bestPlane` is a unit vector. -/
theorem norm_bestPlane_snd (hn : 1 ≤ n) (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) :
    ‖(bestPlane μ x r).2‖ = 1 :=
  (bestPlane_prop hn μ x r).1

/-- `bestPlane μ x r` attains the infimum defining `β²(x, r)`. -/
theorem bestPlane_spec (hn : 1 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} (hr : 0 < r)
    (hfin : μ (ball x r) ≠ ∞) : planeBetaSq μ x r (bestPlane μ x r) = jonesBetaSq μ x r :=
  (bestPlane_prop hn μ x r).2 hr hfin

/-- (BP) `∫_{B_r(x)} ⟪y − p, ν⟫² dμ = r^{n+1} β²(x, r)` for `(p, ν) = bestPlane μ x r`. -/
theorem lintegral_bestPlane (hn : 1 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} (hr : 0 < r)
    (hfin : μ (ball x r) ≠ ∞) :
    ∫⁻ y in ball x r, ENNReal.ofReal (⟪y - (bestPlane μ x r).1, (bestPlane μ x r).2⟫ ^ 2) ∂μ =
      ENNReal.ofReal (r ^ (n + 1)) * jonesBetaSq μ x r := by
  rw [← bestPlane_spec hn hr hfin, planeBetaSq_eq hn hr, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_mul]

end GMTFoundations
