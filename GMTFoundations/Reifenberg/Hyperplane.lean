/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Setup
public import GMTFoundations.Common.Hyperplane

/-!
# Hyperplanes: the normalized distance `planeDist`

The Reifenberg geometry of this library is specialized to hyperplanes (`k = n − 1`) throughout,
whereas M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018);
arXiv:1612.02461 (Miś), and A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of
stationary and minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227 (NV), work with
affine `k`-planes for general `k`.

A plane is a pair `P = (p, ν) : Rn n × Rn n`, with `‖ν‖ = 1` where needed. Its signed
distance function is `f_P(y) = ⟪y − p, ν⟫`. The normalized distance of two planes on `B_r(x)` is
`planeDist x r P Q = min_{s = ±1} (‖ν_P − s ν_Q‖ + |f_P(x) − s f_Q(x)| / r)`.
It depends only on the two geometric planes (changing `p` within the plane leaves `f_P`
unchanged; replacing `ν` by `−ν` swaps the two branches of the min). It is not the local Hausdorff
distance `d_{x,r}` of Miś/NV; an elementary computation (not formalized) shows that the two agree
up to absolute constants when one plane meets `B_{r/2}(x)`.

## Main definitions

* `planeDist x r P Q`.
* `planeDistSign x r P Q s = ‖ν_P − s ν_Q‖ + |f_P(x) − s f_Q(x)| / r`, one branch of the min.

## Main statements

* PD1 `planeDist_comm`; PD2 `planeDist_triangle`; PD3 `planeDist_le_of_center` (change of centre
  and scale); PD4 `exists_sign_of_planeDist_le` (pointwise form); PD8 `planeDist_nonneg`. None of
  these needs unit normals.
* `affPlane P = {x | ⟪x − p, ν⟫ = 0}` and the affine projection `affProj P w = w − f_P(w) ν_P`
  (a translate of the linear `GMT.hyperplane` of `GMT/FlatPiece`).
* PD5 `norm_affProj_sub_affProj_le` (affine projections), PD6 `norm_projH_sub_projH_le` (linear
  projections), with the linear projection `GMT.projH ν w = w − ⟪w, ν⟫ ν` of `GMT/FlatPiece`.
* The quadratic projection lemma (Miś Lemma 3.4, `‖π₁π₂ − id‖ ≤ Cδ²` on `V₁`). For hyperplanes
  it becomes an explicit identity for rank-one projections, with constant `C = 1`:
  (7a) `projH_projH_sub_eq`, `norm_projH_comp_projH_sub_le`;
  (7b) `affProj_affProj_sub_eq`, `norm_affProj_affProj_sub_le`.
-/

public noncomputable section

namespace GMTFoundations

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The normalized distance of the hyperplanes `P = (p₁, ν₁)` and `Q = (p₂, ν₂)` on `B_r(x)`
(pair form):
`min (‖ν₁ − ν₂‖ + |f_P(x) − f_Q(x)| / r) (‖ν₁ + ν₂‖ + |f_P(x) + f_Q(x)| / r)`,
with `f_P(y) = ⟪y − p₁, ν₁⟫`. -/
@[expose] def planeDist (x : Rn n) (r : ℝ) (P Q : Rn n × Rn n) : ℝ :=
  min (‖P.2 - Q.2‖ + |⟪x - P.1, P.2⟫ - ⟪x - Q.1, Q.2⟫| / r)
    (‖P.2 + Q.2‖ + |⟪x - P.1, P.2⟫ + ⟪x - Q.1, Q.2⟫| / r)

/-- One branch of `planeDist`, for the sign `s` (meant to be `±1`):
`‖ν_P − s ν_Q‖ + |f_P(x) − s f_Q(x)| / r`. -/
@[expose] def planeDistSign (x : Rn n) (r : ℝ) (P Q : Rn n × Rn n) (s : ℝ) : ℝ :=
  ‖P.2 - s • Q.2‖ + |⟪x - P.1, P.2⟫ - s * ⟪x - Q.1, Q.2⟫| / r

variable {x x' y : Rn n} {r r' δ s : ℝ} {P Q R : Rn n × Rn n}

theorem planeDist_eq_min_sign (x : Rn n) (r : ℝ) (P Q : Rn n × Rn n) :
    planeDist x r P Q = min (planeDistSign x r P Q 1) (planeDistSign x r P Q (-1)) := by
  rw [planeDist, planeDistSign, planeDistSign, one_smul, one_mul, neg_one_smul, neg_one_mul,
    sub_neg_eq_add, sub_neg_eq_add]

theorem planeDist_le_planeDistSign (hs : s = 1 ∨ s = -1) :
    planeDist x r P Q ≤ planeDistSign x r P Q s := by
  rw [planeDist_eq_min_sign]
  rcases hs with rfl | rfl
  exacts [min_le_left _ _, min_le_right _ _]

/-- The minimum in `planeDist` is attained at a sign `s = ±1`. -/
theorem exists_sign_planeDist_eq (x : Rn n) (r : ℝ) (P Q : Rn n × Rn n) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ planeDist x r P Q = planeDistSign x r P Q s := by
  rw [planeDist_eq_min_sign]
  rcases min_choice (planeDistSign x r P Q 1) (planeDistSign x r P Q (-1)) with h | h
  exacts [⟨1, Or.inl rfl, h⟩, ⟨-1, Or.inr rfl, h⟩]

theorem planeDistSign_nonneg (hr : 0 ≤ r) (s : ℝ) : 0 ≤ planeDistSign x r P Q s :=
  add_nonneg (norm_nonneg _) (div_nonneg (abs_nonneg _) hr)

/-- PD8: `planeDist ≥ 0` for `r ≥ 0`. -/
theorem planeDist_nonneg (hr : 0 ≤ r) : 0 ≤ planeDist x r P Q := by
  obtain ⟨s, -, h⟩ := exists_sign_planeDist_eq x r P Q
  rw [h]
  exact planeDistSign_nonneg hr s

/-- PD1: `planeDist` is symmetric. -/
theorem planeDist_comm (x : Rn n) (r : ℝ) (P Q : Rn n × Rn n) :
    planeDist x r P Q = planeDist x r Q P := by
  rw [planeDist, planeDist, norm_sub_rev, abs_sub_comm, add_comm P.2 Q.2,
    add_comm ⟪x - P.1, P.2⟫]

/-- The combination `f_P − s f_Q` is affine with linear part `⟪·, ν_P − s ν_Q⟫`. -/
theorem inner_sub_sign_sub (P Q : Rn n × Rn n) (s : ℝ) (x y : Rn n) :
    (⟪y - P.1, P.2⟫ - s * ⟪y - Q.1, Q.2⟫) - (⟪x - P.1, P.2⟫ - s * ⟪x - Q.1, Q.2⟫) =
      ⟪y - x, P.2 - s • Q.2⟫ := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_right]
  ring

/-- `|f_P(y) − s f_Q(y)| ≤ |f_P(x) − s f_Q(x)| + ‖y − x‖ ‖ν_P − s ν_Q‖`. -/
theorem abs_inner_sub_sign_le (P Q : Rn n × Rn n) (s : ℝ) (x y : Rn n) :
    |⟪y - P.1, P.2⟫ - s * ⟪y - Q.1, Q.2⟫| ≤
      |⟪x - P.1, P.2⟫ - s * ⟪x - Q.1, Q.2⟫| + ‖y - x‖ * ‖P.2 - s • Q.2‖ := by
  have h := inner_sub_sign_sub P Q s x y
  rw [sub_eq_iff_eq_add] at h
  rw [h, add_comm (⟪y - x, P.2 - s • Q.2⟫)]
  exact (abs_add_le _ _).trans (add_le_add_right (abs_real_inner_le_norm _ _) _)

/-- PD2 for fixed signs: `S_{s₁ s₂}(P, R) ≤ S_{s₁}(P, Q) + S_{s₂}(Q, R)` when `s₁ = ±1`. -/
theorem planeDistSign_mul_le (hr : 0 ≤ r) {s₁ : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (s₂ : ℝ) :
    planeDistSign x r P R (s₁ * s₂) ≤ planeDistSign x r P Q s₁ + planeDistSign x r Q R s₂ := by
  have habs : |s₁| = 1 := by rcases hs₁ with rfl | rfl <;> simp
  have hv : P.2 - (s₁ * s₂) • R.2 = (P.2 - s₁ • Q.2) + s₁ • (Q.2 - s₂ • R.2) := by
    rw [smul_sub, smul_smul]; abel
  have hf : ⟪x - P.1, P.2⟫ - s₁ * s₂ * ⟪x - R.1, R.2⟫ =
      (⟪x - P.1, P.2⟫ - s₁ * ⟪x - Q.1, Q.2⟫) + s₁ * (⟪x - Q.1, Q.2⟫ - s₂ * ⟪x - R.1, R.2⟫) := by
    ring
  have h1 : ‖P.2 - (s₁ * s₂) • R.2‖ ≤ ‖P.2 - s₁ • Q.2‖ + ‖Q.2 - s₂ • R.2‖ := by
    rw [hv]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, Real.norm_eq_abs, habs, one_mul]
  have h2 : |⟪x - P.1, P.2⟫ - s₁ * s₂ * ⟪x - R.1, R.2⟫| ≤
      |⟪x - P.1, P.2⟫ - s₁ * ⟪x - Q.1, Q.2⟫| + |⟪x - Q.1, Q.2⟫ - s₂ * ⟪x - R.1, R.2⟫| := by
    rw [hf]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, habs, one_mul]
  have h3 := div_le_div_of_nonneg_right h2 hr
  rw [add_div] at h3
  unfold planeDistSign
  linarith

/-- PD2: the triangle inequality for `planeDist` (no unit normals needed). -/
theorem planeDist_triangle (hr : 0 ≤ r) (P Q R : Rn n × Rn n) :
    planeDist x r P R ≤ planeDist x r P Q + planeDist x r Q R := by
  obtain ⟨s₁, hs₁, h₁⟩ := exists_sign_planeDist_eq x r P Q
  obtain ⟨s₂, hs₂, h₂⟩ := exists_sign_planeDist_eq x r Q R
  have hs : s₁ * s₂ = 1 ∨ s₁ * s₂ = -1 := by
    rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> norm_num
  rw [h₁, h₂]
  exact (planeDist_le_planeDistSign hs).trans (planeDistSign_mul_le hr hs₁ s₂)

/-- PD3 for a fixed sign. -/
theorem planeDistSign_le_of_center (hr : 0 < r) (hr' : 0 < r') (s : ℝ) :
    planeDistSign x' r' P Q s ≤ max (1 + ‖x - x'‖ / r') (r / r') * planeDistSign x r P Q s := by
  set A := ‖P.2 - s • Q.2‖
  set H := |⟪x - P.1, P.2⟫ - s * ⟪x - Q.1, Q.2⟫|
  set D := ‖x - x'‖
  set M := max (1 + D / r') (r / r')
  have hA : 0 ≤ A := norm_nonneg _
  have hH : 0 ≤ H / r := div_nonneg (abs_nonneg _) hr.le
  have h1 : |⟪x' - P.1, P.2⟫ - s * ⟪x' - Q.1, Q.2⟫| ≤ H + D * A := by
    have := abs_inner_sub_sign_le P Q s x x'
    rwa [norm_sub_rev] at this
  unfold planeDistSign
  calc A + |⟪x' - P.1, P.2⟫ - s * ⟪x' - Q.1, Q.2⟫| / r'
      ≤ A + (H + D * A) / r' := add_le_add le_rfl (div_le_div_of_nonneg_right h1 hr'.le)
    _ = (1 + D / r') * A + r / r' * (H / r) := by field_simp; ring
    _ ≤ M * A + M * (H / r) :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hA)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hH)
    _ = M * (A + H / r) := by ring

/-- PD3, change of centre and scale:
`planeDist x' r' P Q ≤ max (1 + ‖x − x'‖ / r') (r / r') · planeDist x r P Q`. -/
theorem planeDist_le_of_center (hr : 0 < r) (hr' : 0 < r') (P Q : Rn n × Rn n) :
    planeDist x' r' P Q ≤ max (1 + ‖x - x'‖ / r') (r / r') * planeDist x r P Q := by
  obtain ⟨s, hs, h⟩ := exists_sign_planeDist_eq x r P Q
  rw [h]
  exact (planeDist_le_planeDistSign hs).trans (planeDistSign_le_of_center hr hr' s)

/-- PD4, pointwise form: if `planeDist x r P Q ≤ δ` there is a sign `s = ±1` with
`‖ν_P − s ν_Q‖ ≤ δ` and `|f_P(y) − s f_Q(y)| ≤ (r + ‖y − x‖) δ` for all `y`. -/
theorem exists_sign_of_planeDist_le (hr : 0 < r) (h : planeDist x r P Q ≤ δ) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖P.2 - s • Q.2‖ ≤ δ ∧
      ∀ y : Rn n, |⟪y - P.1, P.2⟫ - s * ⟪y - Q.1, Q.2⟫| ≤ (r + ‖y - x‖) * δ := by
  obtain ⟨s, hs, hD⟩ := exists_sign_planeDist_eq x r P Q
  rw [hD, planeDistSign] at h
  set A := ‖P.2 - s • Q.2‖
  set H := |⟪x - P.1, P.2⟫ - s * ⟪x - Q.1, Q.2⟫|
  have hA : 0 ≤ A := norm_nonneg _
  have hH0 : 0 ≤ H / r := div_nonneg (abs_nonneg _) hr.le
  have hAδ : A ≤ δ := by linarith
  have hHδ : H ≤ r * δ := by
    have : H / r ≤ δ := by linarith
    rwa [div_le_iff₀ hr, mul_comm] at this
  refine ⟨s, hs, hAδ, fun y => ?_⟩
  calc |⟪y - P.1, P.2⟫ - s * ⟪y - Q.1, Q.2⟫| ≤ H + ‖y - x‖ * A := abs_inner_sub_sign_le P Q s x y
    _ ≤ r * δ + ‖y - x‖ * δ := add_le_add hHδ (mul_le_mul_of_nonneg_left hAδ (norm_nonneg _))
    _ = (r + ‖y - x‖) * δ := by ring

/-! ### Projections (PD5, PD6) and the quadratic projection lemma (7a), (7b) -/

/-- The plane `P = (p, ν)` as a set: `{x | ⟪x − p, ν⟫ = 0}`. -/
@[expose] def affPlane (P : Rn n × Rn n) : Set (Rn n) := {x | ⟪x - P.1, P.2⟫ = 0}

/-- The affine orthogonal projection onto the plane `P = (p, ν)` (for `‖ν‖ = 1`):
`affProj P w = w − f_P(w) ν`, with `f_P(w) = ⟪w − p, ν⟫`. -/
@[expose] def affProj (P : Rn n × Rn n) (w : Rn n) : Rn n := w - ⟪w - P.1, P.2⟫ • P.2

@[simp] theorem mem_affPlane {P : Rn n × Rn n} {x : Rn n} :
    x ∈ affPlane P ↔ ⟪x - P.1, P.2⟫ = 0 := Iff.rfl

theorem affProj_eq_add_projH (P : Rn n × Rn n) (y : Rn n) :
    affProj P y = P.1 + GMT.projH P.2 (y - P.1) := by
  simp only [affProj, GMT.projH]
  abel

theorem inner_affProj_sub {P : Rn n × Rn n} (hP : ‖P.2‖ = 1) (y : Rn n) :
    ⟪affProj P y - P.1, P.2⟫ = 0 := by
  rw [affProj_eq_add_projH, add_sub_cancel_left]
  exact GMT.inner_projH hP _

theorem affProj_mem_affPlane {P : Rn n × Rn n} (hP : ‖P.2‖ = 1) (y : Rn n) :
    affProj P y ∈ affPlane P :=
  inner_affProj_sub hP y

theorem affProj_of_mem {P : Rn n × Rn n} {y : Rn n} (hy : y ∈ affPlane P) : affProj P y = y := by
  rw [affProj, mem_affPlane.1 hy, zero_smul, sub_zero]

/-- If `‖ν₁‖ = 1`, `s = ±1` and `⟪v, ν₁⟫ = 0`, then `|⟪v, ν₂⟫| ≤ ‖ν₁ − s ν₂‖ ‖v‖`. -/
theorem abs_inner_le_of_inner_eq_zero {ν₁ ν₂ v : Rn n} {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hv : ⟪v, ν₁⟫ = 0) : |⟪v, ν₂⟫| ≤ ‖ν₁ - s • ν₂‖ * ‖v‖ := by
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have h : |⟪v, ν₂⟫| = |⟪v, ν₁ - s • ν₂⟫| := by
    rw [inner_sub_right, hv, zero_sub, abs_neg, real_inner_smul_right, abs_mul, habs, one_mul]
  rw [h, mul_comm]
  exact abs_real_inner_le_norm _ _

/-- If `‖ν₁‖ = 1` and `s = ±1`, then `‖projH ν₁ ν₂‖ ≤ ‖ν₁ − s ν₂‖`. -/
theorem norm_projH_le_of_sign {ν₁ ν₂ : Rn n} {s : ℝ} (h1 : ‖ν₁‖ = 1) (hs : s = 1 ∨ s = -1) :
    ‖GMT.projH ν₁ ν₂‖ ≤ ‖ν₁ - s • ν₂‖ := by
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have h11 : GMT.projH ν₁ ν₁ = 0 := by
    rw [GMT.projH, real_inner_self_eq_norm_sq, h1, one_pow, one_smul, sub_self]
  have h : GMT.projH ν₁ ν₂ = -s • GMT.projH ν₁ (ν₁ - s • ν₂) := by
    rw [GMT.projH_sub, GMT.projH_smul, h11, zero_sub, smul_neg, neg_smul, neg_neg, smul_smul]
    have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
    rw [hss, one_smul]
  rw [h, norm_smul, Real.norm_eq_abs, abs_neg, habs, one_mul]
  exact GMT.norm_projH_le h1 _

/-- (7a), identity (Miś Lemma 3.4, hyperplane form): if `⟪v, ν₁⟫ = 0`, then
`projH ν₁ (projH ν₂ v) − v = −⟪v, ν₂⟫ • projH ν₁ ν₂`. No unit normals are needed. -/
theorem projH_projH_sub_eq {ν₁ ν₂ v : Rn n} (hv : ⟪v, ν₁⟫ = 0) :
    GMT.projH ν₁ (GMT.projH ν₂ v) - v = -⟪v, ν₂⟫ • GMT.projH ν₁ ν₂ := by
  simp only [GMT.projH, inner_sub_left, real_inner_smul_left, hv]
  module

/-- (7a) (Miś Lemma 3.4, hyperplane form, constant 1): if `‖ν₁‖ = 1`, `s = ±1`,
`‖ν₁ − s ν₂‖ ≤ δ` and `⟪v, ν₁⟫ = 0`, then `‖projH ν₁ (projH ν₂ v) − v‖ ≤ δ² ‖v‖`. -/
theorem norm_projH_comp_projH_sub_le {ν₁ ν₂ v : Rn n} {s δ : ℝ} (h1 : ‖ν₁‖ = 1)
    (hs : s = 1 ∨ s = -1) (hδ : ‖ν₁ - s • ν₂‖ ≤ δ) (hv : ⟪v, ν₁⟫ = 0) :
    ‖GMT.projH ν₁ (GMT.projH ν₂ v) - v‖ ≤ δ ^ 2 * ‖v‖ := by
  rw [projH_projH_sub_eq hv, norm_smul, Real.norm_eq_abs, abs_neg]
  have ha := abs_inner_le_of_inner_eq_zero hs hv (ν₂ := ν₂)
  have hb := norm_projH_le_of_sign (ν₂ := ν₂) h1 hs
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  calc |⟪v, ν₂⟫| * ‖GMT.projH ν₁ ν₂‖ ≤ (δ * ‖v‖) * δ :=
        mul_le_mul (ha.trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))) (hb.trans hδ)
          (norm_nonneg _) (mul_nonneg hδ0 (norm_nonneg _))
    _ = δ ^ 2 * ‖v‖ := by ring

/-- (7b), identity: if `f_P(y) = 0`, then
`affProj P (affProj Q y) − y = −f_Q(y) • projH ν_P ν_Q`. No unit normals are needed. -/
theorem affProj_affProj_sub_eq {P Q : Rn n × Rn n} {y : Rn n} (h : ⟪y - P.1, P.2⟫ = 0) :
    affProj P (affProj Q y) - y = -⟪y - Q.1, Q.2⟫ • GMT.projH P.2 Q.2 := by
  have h' : ⟪y - ⟪y - Q.1, Q.2⟫ • Q.2 - P.1, P.2⟫ =
      ⟪y - P.1, P.2⟫ - ⟪y - Q.1, Q.2⟫ * ⟪Q.2, P.2⟫ := by
    rw [show y - ⟪y - Q.1, Q.2⟫ • Q.2 - P.1 = (y - P.1) - ⟪y - Q.1, Q.2⟫ • Q.2 by abel,
      inner_sub_left, real_inner_smul_left]
  simp only [affProj, GMT.projH]
  rw [h', h]
  module

/-- (7b) (used in the squash lemma, `Reifenberg/Squash.lean`): if `‖ν_P‖ = 1`, `f_P(y) = 0`
and `r > 0`, then `‖affProj P (affProj Q y) − y‖ ≤ (r + ‖y − x‖) · planeDist x r P Q ²`. -/
theorem norm_affProj_affProj_sub_le (hP : ‖P.2‖ = 1) (h : ⟪y - P.1, P.2⟫ = 0) (hr : 0 < r) :
    ‖affProj P (affProj Q y) - y‖ ≤ (r + ‖y - x‖) * planeDist x r P Q ^ 2 := by
  obtain ⟨s, hs, hν, hf⟩ := exists_sign_of_planeDist_le (x := x) hr (le_refl (planeDist x r P Q))
  have hsQ : |⟪y - Q.1, Q.2⟫| ≤ (r + ‖y - x‖) * planeDist x r P Q := by
    have := hf y
    rw [h, zero_sub, abs_neg, abs_mul] at this
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    rwa [habs, one_mul] at this
  rw [affProj_affProj_sub_eq h, norm_smul, Real.norm_eq_abs, abs_neg]
  have hb := (norm_projH_le_of_sign (ν₂ := Q.2) hP hs).trans hν
  calc |⟪y - Q.1, Q.2⟫| * ‖GMT.projH P.2 Q.2‖
      ≤ ((r + ‖y - x‖) * planeDist x r P Q) * planeDist x r P Q :=
        mul_le_mul hsQ hb (norm_nonneg _)
          (mul_nonneg (add_nonneg hr.le (norm_nonneg _)) (planeDist_nonneg hr.le))
    _ = (r + ‖y - x‖) * planeDist x r P Q ^ 2 := by ring

/-- For `r ≥ 0` there is a sign `s = ±1` with `‖ν_P − s ν_Q‖ ≤ planeDist x r P Q`. -/
theorem exists_sign_norm_sub_le_planeDist (hr : 0 ≤ r) (x : Rn n) (P Q : Rn n × Rn n) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖P.2 - s • Q.2‖ ≤ planeDist x r P Q := by
  obtain ⟨s, hs, h⟩ := exists_sign_planeDist_eq x r P Q
  refine ⟨s, hs, ?_⟩
  rw [h, planeDistSign]
  exact le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hr)

/-- PD6 for a fixed sign: for unit `ν₁, ν₂` and `s = ±1`,
`‖projH ν₁ w − projH ν₂ w‖ ≤ 2 ‖ν₁ − s ν₂‖ ‖w‖`. -/
theorem norm_projH_sub_projH_le_of_sign {ν₁ ν₂ : Rn n} {s : ℝ} (h1 : ‖ν₁‖ = 1) (h2 : ‖ν₂‖ = 1)
    (hs : s = 1 ∨ s = -1) (w : Rn n) :
    ‖GMT.projH ν₁ w - GMT.projH ν₂ w‖ ≤ 2 * ‖ν₁ - s • ν₂‖ * ‖w‖ := by
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  set ν' := s • ν₂ with hν'
  have hν'n : ‖ν'‖ = 1 := by rw [hν', norm_smul, Real.norm_eq_abs, habs, h2, one_mul]
  have hid : GMT.projH ν₁ w - GMT.projH ν₂ w = ⟪w, ν' - ν₁⟫ • ν' + ⟪w, ν₁⟫ • (ν' - ν₁) := by
    have hq : ⟪w, ν₂⟫ • ν₂ = ⟪w, ν'⟫ • ν' := by
      rw [hν', real_inner_smul_right, smul_smul, mul_comm s, mul_assoc, hss, mul_one]
    simp only [GMT.projH]
    rw [sub_sub_sub_cancel_left, hq, inner_sub_right]
    module
  rw [hid]
  have e1 : ‖ν' - ν₁‖ = ‖ν₁ - s • ν₂‖ := norm_sub_rev _ _
  calc ‖⟪w, ν' - ν₁⟫ • ν' + ⟪w, ν₁⟫ • (ν' - ν₁)‖
      ≤ ‖⟪w, ν' - ν₁⟫ • ν'‖ + ‖⟪w, ν₁⟫ • (ν' - ν₁)‖ := norm_add_le _ _
    _ = |⟪w, ν' - ν₁⟫| + |⟪w, ν₁⟫| * ‖ν₁ - s • ν₂‖ := by
        rw [norm_smul, norm_smul (⟪w, ν₁⟫), hν'n, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, e1]
    _ ≤ ‖w‖ * ‖ν₁ - s • ν₂‖ + ‖w‖ * ‖ν₁ - s • ν₂‖ := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        · rw [← e1]; exact abs_real_inner_le_norm _ _
        · have := abs_real_inner_le_norm w ν₁
          rwa [h1, mul_one] at this
    _ = 2 * ‖ν₁ - s • ν₂‖ * ‖w‖ := by ring

/-- PD6 (linear projections; unit normals, `r ≥ 0`):
`‖projH ν_P w − projH ν_Q w‖ ≤ 2 · planeDist x r P Q · ‖w‖`. -/
theorem norm_projH_sub_projH_le (hP : ‖P.2‖ = 1) (hQ : ‖Q.2‖ = 1) (hr : 0 ≤ r) (w : Rn n) :
    ‖GMT.projH P.2 w - GMT.projH Q.2 w‖ ≤ 2 * planeDist x r P Q * ‖w‖ := by
  obtain ⟨s, hs, h⟩ := exists_sign_norm_sub_le_planeDist hr x P Q
  exact (norm_projH_sub_projH_le_of_sign hP hQ hs w).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num)) (norm_nonneg _))

/-- PD5 (affine projections; `‖ν_Q‖ = 1`, `r > 0`): for all `y`,
`‖affProj P y − affProj Q y‖ ≤ (r + ‖y − x‖ + |f_P(y)|) · planeDist x r P Q`. -/
theorem norm_affProj_sub_affProj_le (hQ : ‖Q.2‖ = 1) (hr : 0 < r) (y : Rn n) :
    ‖affProj P y - affProj Q y‖ ≤ (r + ‖y - x‖ + |⟪y - P.1, P.2⟫|) * planeDist x r P Q := by
  obtain ⟨s, hs, hν, hf⟩ := exists_sign_of_planeDist_le (x := x) hr (le_refl (planeDist x r P Q))
  have habs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  set fP := ⟪y - P.1, P.2⟫
  set fQ := ⟪y - Q.1, Q.2⟫
  have hid : affProj P y - affProj Q y = (s * fQ - fP) • (s • Q.2) + fP • (s • Q.2 - P.2) := by
    have : fQ • Q.2 = (s * fQ) • (s • Q.2) := by
      rw [smul_smul, mul_comm s fQ, mul_assoc, hss, mul_one]
    simp only [affProj]
    rw [show y - fP • P.2 - (y - fQ • Q.2) = fQ • Q.2 - fP • P.2 by abel, this]
    module
  rw [hid]
  have hsQ : ‖s • Q.2‖ = 1 := by rw [norm_smul, Real.norm_eq_abs, habs, hQ, one_mul]
  calc ‖(s * fQ - fP) • (s • Q.2) + fP • (s • Q.2 - P.2)‖
      ≤ ‖(s * fQ - fP) • (s • Q.2)‖ + ‖fP • (s • Q.2 - P.2)‖ := norm_add_le _ _
    _ = |fP - s * fQ| + |fP| * ‖P.2 - s • Q.2‖ := by
        rw [norm_smul, norm_smul fP, hsQ, Real.norm_eq_abs, Real.norm_eq_abs, mul_one,
          abs_sub_comm, norm_sub_rev]
    _ ≤ (r + ‖y - x‖) * planeDist x r P Q + |fP| * planeDist x r P Q :=
        add_le_add (hf y) (mul_le_mul_of_nonneg_left hν (abs_nonneg _))
    _ = (r + ‖y - x‖ + |fP|) * planeDist x r P Q := by ring

end GMTFoundations
