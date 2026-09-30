/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Setup
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Hyperplanes and the projection onto them

* `GMT.hyperplane ν = {y | ⟪y, ν⟫ = 0}` and `GMT.mem_hyperplane`;
* `GMT.projH ν y = y - ⟪y, ν⟫ ν`, the orthogonal projection onto `ν^⊥` for a unit vector `ν`, and
  its elementary algebra (`projH_sub`, `projH_smul`, `inner_projH`, `projH_mem_hyperplane`,
  `projH_of_mem`, `norm_sub_projH`, `norm_projH_le`);
* unit-vector algebra for unit `a, b` and `s = ±1` (used by `Reifenberg/Squash.lean` and
  `Reifenberg/Regraph.lean`): `norm_sub_smul_sq_eq`, `abs_sign_sub_inner_le`,
  `one_sub_inner_sq_le`, `abs_inner_le_one`.

(Split out of `GMT/Basic.lean`, `GMT/FlatPiece.lean` (which re-export it) and
`Reifenberg/Squash.lean`, so that `Reifenberg/Hyperplane.lean` depends on neither `GMT/Basic` nor
`GMT/FlatPiece`, and `Reifenberg/Regraph.lean` does not depend on `Reifenberg/Squash.lean`.)
-/

@[expose] public section

open scoped RealInnerProductSpace

noncomputable section

namespace GMTFoundations.GMT

variable {n : ℕ}

/-- The hyperplane `ν^⊥ = {y | ⟪y, ν⟫ = 0}`. -/
def hyperplane (ν : Rn n) : Set (Rn n) := {y | ⟪y, ν⟫ = 0}

@[simp] theorem mem_hyperplane {ν y : Rn n} : y ∈ hyperplane ν ↔ ⟪y, ν⟫ = 0 := Iff.rfl

/-! ### The projection onto `ν^⊥` -/

/-- The orthogonal projection onto `ν^⊥` (for a unit vector `ν`). -/
def projH (ν : Rn n) (y : Rn n) : Rn n := y - ⟪y, ν⟫ • ν

theorem projH_sub (ν y z : Rn n) : projH ν (y - z) = projH ν y - projH ν z := by
  simp only [projH, inner_sub_left, sub_smul]
  abel

theorem projH_smul (ν y : Rn n) (c : ℝ) : projH ν (c • y) = c • projH ν y := by
  simp only [projH, inner_smul_left, RCLike.conj_to_real, smul_sub, mul_smul]

theorem inner_projH {ν : Rn n} (hν : ‖ν‖ = 1) (y : Rn n) : ⟪projH ν y, ν⟫ = 0 := by
  simp only [projH, inner_sub_left, inner_smul_left, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq,
    hν]
  ring

theorem projH_mem_hyperplane {ν : Rn n} (hν : ‖ν‖ = 1) (y : Rn n) :
    projH ν y ∈ hyperplane ν :=
  inner_projH hν y

theorem projH_of_mem {ν y : Rn n} (hy : y ∈ hyperplane ν) : projH ν y = y := by
  simp [projH, mem_hyperplane.1 hy]

theorem norm_sub_projH {ν : Rn n} (hν : ‖ν‖ = 1) (y : Rn n) : ‖y - projH ν y‖ = |⟪y, ν⟫| := by
  simp [projH, norm_smul, hν]

theorem norm_projH_le {ν : Rn n} (hν : ‖ν‖ = 1) (y : Rn n) : ‖projH ν y‖ ≤ ‖y‖ := by
  have h : ‖projH ν y‖ ^ 2 = ‖y‖ ^ 2 - ⟪y, ν⟫ ^ 2 := by
    rw [projH, @norm_sub_sq_real, inner_smul_right, norm_smul, hν, Real.norm_eq_abs, mul_one,
      sq_abs]
    ring
  have h2 : ‖projH ν y‖ ^ 2 ≤ ‖y‖ ^ 2 := by rw [h]; linarith [sq_nonneg ⟪y, ν⟫]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

end GMTFoundations.GMT

/-! ### Unit-vector algebra -/

namespace GMTFoundations

variable {n : ℕ}

theorem norm_sub_smul_sq_eq {a b : Rn n} {s : ℝ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hs : s = 1 ∨ s = -1) : ‖a - s • b‖ ^ 2 = 2 - 2 * (s * ⟪b, a⟫) := by
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ha,
    hb, real_inner_comm]
  linear_combination hss

/-- (E3) `|s − ⟪b, a⟫| ≤ ‖a − s b‖² / 2` for unit `a, b` and `s = ±1`. -/
theorem abs_sign_sub_inner_le {a b : Rn n} {s : ℝ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hs : s = 1 ∨ s = -1) : |s - ⟪b, a⟫| ≤ ‖a - s • b‖ ^ 2 / 2 := by
  have h := norm_sub_smul_sq_eq ha hb hs
  have hk : |⟪b, a⟫| ≤ 1 := by
    have := abs_real_inner_le_norm b a
    rwa [ha, hb, mul_one] at this
  rcases hs with rfl | rfl
  · rw [abs_le] at hk ⊢; constructor <;> linarith
  · rw [abs_le] at hk ⊢; constructor <;> linarith

/-- `1 − ⟪b, a⟫² ≤ ‖a − s b‖²` for unit `a, b` and `s = ±1`. -/
theorem one_sub_inner_sq_le {a b : Rn n} {s : ℝ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hs : s = 1 ∨ s = -1) : 1 - ⟪b, a⟫ ^ 2 ≤ ‖a - s • b‖ ^ 2 := by
  have h := norm_sub_smul_sq_eq ha hb hs
  rcases hs with rfl | rfl <;> linarith [sq_nonneg (⟪b, a⟫ - 1), sq_nonneg (⟪b, a⟫ + 1)]

theorem abs_inner_le_one {a b : Rn n} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : |⟪a, b⟫| ≤ 1 := by
  have := abs_real_inner_le_norm a b
  rwa [ha, hb, mul_one] at this

end GMTFoundations
