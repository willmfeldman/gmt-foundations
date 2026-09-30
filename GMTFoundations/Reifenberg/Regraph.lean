/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.ReifenbergMap
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Regraphing over a nearby plane (Miśkiewicz Lemma 3.6)

Lemma 3.6 of M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43
(2018); arXiv:1612.02461 (hereafter Miś), for hyperplanes. Miś gives only a sketch; the proof here
is complete. Two points of the sketch are corrected: the new graph function is the height
`f_{V₂}` of the graph point over `V₂`, not the graph point `φ(x) + g₁(φ(x)) ∈ ℝⁿ` itself; and
the sup bound over a disc needs `d(y, V₁) ≲ r`, which Miś does not state (here `|f_{V₁}(y)| ≤ r/2`).

## Main statement

* `graph_over_near_plane`: if `planeDist y r V₁ V₂ ≤ δ ≤ 1/10`,
  `|f_{V₁}(y)| ≤ r/2` and `IsChart T V₁ g y R r δ` with `R ≤ 5r/2`, then
  `IsChart T V₂ g₂ y R r (6δ)` for some global `g₂` with `Lip g₂ ≤ 3δ` on all of `Rn n`.
  There is no shrinking of the ball: Miś's ratio `θ ∈ (1 − Cδ, 1)` is an artefact of graphs
  defined only on a ball, and disappears for globally defined chart functions.

## Proof outline

After globalizing `g` (Lemma G), the graph `Ĝ = graphOn V₁ ĝ` is a `2δ`-flat piece for `ν₂`
(Step 1), so `π_{V₂}` is injective on it with a `3/2`-Lipschitz inverse. Surjectivity of
`π_{V₂} : Ĝ → affPlane V₂` comes from `perturbId` applied to `w ↦ w − f_{V₂}(Ẑ w) projH ν₁ ν₂`
(Step 2), and `g₂ = f_{V₂} ∘ (π_{V₂}|_Ĝ)⁻¹ ∘ π_{V₂}` (Step 3).
-/

public noncomputable section

namespace GMTFoundations

open Metric Set
open scoped RealInnerProductSpace NNReal

variable {n : ℕ}

/-- `π_{V₁}` is injective on `affPlane V₂` when `⟪ν₂, ν₁⟫ ≠ 0`. -/
theorem affProj_injOn_affPlane {V₁ V₂ : Rn n × Rn n} (hk : ⟪V₂.2, V₁.2⟫ ≠ 0) :
    InjOn (affProj V₁) (affPlane V₂) := by
  intro a ha b hb hab
  have hid : a - b = (⟪a - V₁.1, V₁.2⟫ - ⟪b - V₁.1, V₁.2⟫) • V₁.2 := by
    calc a - b = (affProj V₁ a + ⟪a - V₁.1, V₁.2⟫ • V₁.2) -
          (affProj V₁ b + ⟪b - V₁.1, V₁.2⟫ • V₁.2) := by
          rw [affProj_add_inner_smul, affProj_add_inner_smul]
      _ = _ := by rw [hab, sub_smul]; abel
  have h0 : ⟪a - b, V₂.2⟫ = 0 := inner_sub_eq_zero_of_mem ha hb
  rw [hid, real_inner_smul_left] at h0
  have := (mul_eq_zero.1 h0).resolve_right fun h => hk (by rw [real_inner_comm]; exact h)
  rw [← sub_eq_zero, hid, this, zero_smul]

private theorem regraph_numeric {G A F R r δ : ℝ} (hr : 0 < r) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10)
    (hR : R ≤ 5 / 2 * r) (hG : 0 ≤ G) (e1 : G ≤ δ * r + (r + A) * δ) (e2 : A ≤ R + G + F)
    (e3 : F ≤ r / 2 + r * δ) : G ≤ 6 * δ * r := by
  have p1 := mul_le_mul_of_nonneg_left e2 hδ
  have p2 := mul_le_mul_of_nonneg_left e3 hδ
  have p3 := mul_le_mul_of_nonneg_left hR hδ
  have p4 : δ * (r * δ) ≤ δ * (r / 10) :=
    mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_left hδ' hr.le]) hδ
  have p5 : (1 - δ) * G ≤ δ * (51 / 10 * r) := by linarith
  have p6 : δ * G ≤ 1 / 10 * G := mul_le_mul_of_nonneg_right hδ' hG
  have p7 : 0 ≤ δ * r := mul_nonneg hδ hr.le
  linarith

/-- **Regraphing** (Miś Lemma 3.6). Let `V₁, V₂` have unit normals, `r > 0`,
`R ≤ 5r/2`, `0 ≤ δ ≤ 1/10`, `planeDist y r V₁ V₂ ≤ δ`, `|f_{V₁}(y)| ≤ r/2`, and
`IsChart T V₁ g y R r δ`. Then there is `g₂ : Rn n → ℝ`, `3δ`-Lipschitz on `Rn n`, with
`IsChart T V₂ g₂ y R r (6δ)` (so `C_rg = 6`, `δ_rg = 1/10`). -/
theorem graph_over_near_plane {V₁ V₂ : Rn n × Rn n} {T : Set (Rn n)} {y : Rn n} {g : Rn n → ℝ}
    {r R δ : ℝ} (hV₁ : ‖V₁.2‖ = 1) (hV₂ : ‖V₂.2‖ = 1) (hr : 0 < r) (hR : R ≤ 5 / 2 * r)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 10) (hd : planeDist y r V₁ V₂ ≤ δ)
    (hnear : |⟪y - V₁.1, V₁.2⟫| ≤ r / 2) (hchart : IsChart T V₁ g y R r δ) :
    ∃ g₂ : Rn n → ℝ, IsChart T V₂ g₂ y R r (6 * δ) ∧ LipschitzWith (Real.toNNReal (3 * δ)) g₂ := by
  -- Step 0
  obtain ⟨ĝ, hĝsup, hĝlip, -, hĝchart⟩ := hchart.exists_global hV₁ hδ hr.le
  have hĝlip' : ∀ x x', |ĝ x - ĝ x'| ≤ δ * dist x x' := fun x x' => by
    have := hĝlip.dist_le_mul x x'
    rwa [Real.coe_toNNReal _ hδ, Real.dist_eq] at this
  obtain ⟨s, hs, hν, hf⟩ := exists_sign_of_planeDist_le hr hd
  set ν₁ := V₁.2
  set ν₂ := V₂.2
  set f₁ : Rn n → ℝ := fun w => ⟪w - V₁.1, ν₁⟫ with hf₁
  set f₂ : Rn n → ℝ := fun w => ⟪w - V₂.1, ν₂⟫ with hf₂
  set Z : Rn n → Rn n := fun x => x + ĝ x • ν₁ with hZ
  set w₁₂ := GMT.projH ν₁ ν₂
  have hw₁₂ : ‖w₁₂‖ ≤ δ := (norm_projH_le_of_sign hV₁ hs).trans hν
  have hk : |s - ⟪ν₂, ν₁⟫| ≤ δ ^ 2 / 2 := by
    refine (abs_sign_sub_inner_le hV₁ hV₂ hs).trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hν 2
    linarith
  have hδsq : δ * δ ≤ 1 / 10 * (1 / 10) := mul_le_mul hδ' hδ' hδ (by norm_num)
  have hk0 : ⟪ν₂, ν₁⟫ ≠ 0 := by
    intro h0
    rw [h0, sub_zero] at hk
    have : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    linarith
  have hkabs : |⟪ν₂, ν₁⟫| ≤ 1 := abs_inner_le_one hV₂ hV₁
  -- Step 1: flatness
  have hflat1 : ∀ x ∈ affPlane V₁, ∀ x' ∈ affPlane V₁,
      |f₂ (Z x) - f₂ (Z x')| ≤ 2 * δ * ‖x - x'‖ := by
    intro x hx x' hx'
    have hid : f₂ (Z x) - f₂ (Z x') = ⟪x - x', ν₂⟫ + (ĝ x - ĝ x') * ⟪ν₂, ν₁⟫ := by
      simp only [hf₂, hZ]
      rw [← inner_sub_left, show x + ĝ x • ν₁ - V₂.1 - (x' + ĝ x' • ν₁ - V₂.1) =
        (x - x') + (ĝ x - ĝ x') • ν₁ by rw [sub_smul]; abel, inner_add_left,
        real_inner_smul_left, real_inner_comm ν₁]
    rw [hid]
    have h1 : |⟪x - x', ν₂⟫| ≤ δ * ‖x - x'‖ :=
      (abs_inner_le_of_inner_eq_zero hs (inner_sub_eq_zero_of_mem hx hx')).trans
        (mul_le_mul_of_nonneg_right hν (norm_nonneg _))
    have h2 : |(ĝ x - ĝ x') * ⟪ν₂, ν₁⟫| ≤ δ * ‖x - x'‖ := by
      rw [abs_mul, ← dist_eq_norm]
      exact (mul_le_mul (hĝlip' x x') hkabs (abs_nonneg _)
        ((abs_nonneg _).trans (hĝlip' x x'))).trans_eq (mul_one _)
    have := abs_add_le ⟪x - x', ν₂⟫ ((ĝ x - ĝ x') * ⟪ν₂, ν₁⟫)
    linarith
  have hflat2 : ∀ x ∈ affPlane V₁, ∀ x' ∈ affPlane V₁,
      ‖Z x - Z x'‖ ≤ 3 / 2 * ‖affProj V₂ (Z x) - affProj V₂ (Z x')‖ := by
    intro x hx x' hx'
    have h1 := hflat1 x hx x' hx'
    have h2 : ‖x - x'‖ ≤ ‖Z x - Z x'‖ := norm_sub_le_norm_add_smul_sub hV₁ hx hx' _ _
    have h3 := norm_sub_sq_eq hV₂ (Z x) (Z x')
    have h4 : (f₂ (Z x) - f₂ (Z x')) ^ 2 ≤ (2 * δ * ‖Z x - Z x'‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))) 2
    have h5 : ‖Z x - Z x'‖ ^ 2 ≤ (3 / 2 * ‖affProj V₂ (Z x) - affProj V₂ (Z x')‖) ^ 2 := by
      have hδ2 : 4 * δ ^ 2 ≤ 1 / 25 := by linarith
      have : ‖Z x - Z x'‖ ^ 2 * (1 - 4 * δ ^ 2) ≤
          ‖affProj V₂ (Z x) - affProj V₂ (Z x')‖ ^ 2 := by
        simp only [hf₂] at h4
        linarith
      have := mul_le_mul_of_nonneg_left hδ2 (sq_nonneg ‖Z x - Z x'‖)
      linarith [sq_nonneg ‖affProj V₂ (Z x) - affProj V₂ (Z x')‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h5
  -- Step 2: surjectivity via perturbId
  set H : Rn n → Rn n := fun w => -(f₂ (Z (affProj V₁ w)) • w₁₂) with hH
  have hHlip : LipschitzWith (Real.toNNReal (2 * δ ^ 2)) H := by
    refine LipschitzWith.of_dist_le' fun w w' => ?_
    simp only [hH]
    rw [dist_neg_neg, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
    have h1 := hflat1 _ (affProj_mem_affPlane hV₁ w) _ (affProj_mem_affPlane hV₁ w')
    have h2 : ‖affProj V₁ w - affProj V₁ w'‖ ≤ dist w w' := by
      rw [← dist_eq_norm]; exact dist_affProj_le hV₁ w w'
    have h3 : |f₂ (Z (affProj V₁ w)) - f₂ (Z (affProj V₁ w'))| ≤ 2 * δ * dist w w' :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    calc |f₂ (Z (affProj V₁ w)) - f₂ (Z (affProj V₁ w'))| * ‖w₁₂‖
        ≤ (2 * δ * dist w w') * δ := mul_le_mul h3 hw₁₂ (norm_nonneg _) (by positivity)
      _ = 2 * δ ^ 2 * dist w w' := by ring
  have hHlt : Real.toNNReal (2 * δ ^ 2) < 1 := by
    rw [Real.toNNReal_lt_one]; linarith
  have hHν : ∀ w, ⟪H w, ν₁⟫ = 0 := fun w => by
    simp only [hH, inner_neg_left, real_inner_smul_left, GMT.inner_projH hV₁, mul_zero, neg_zero,
      w₁₂]
  obtain ⟨e, he, -, heν⟩ := perturbId hHlt hHlip hHν
  -- `π₁ ∘ π₂ ∘ Z = e` on the plane
  have hΓ : ∀ x ∈ affPlane V₁, affProj V₁ (affProj V₂ (Z x)) = e x := by
    intro x hx
    have h1 : ⟪x + ĝ x • ν₁ - ⟪x + ĝ x • ν₁ - V₂.1, ν₂⟫ • ν₂ - V₁.1, ν₁⟫ =
        ĝ x - ⟪x + ĝ x • ν₁ - V₂.1, ν₂⟫ * ⟪ν₂, ν₁⟫ := by
      rw [show x + ĝ x • ν₁ - ⟪x + ĝ x • ν₁ - V₂.1, ν₂⟫ • ν₂ - V₁.1 =
        (x + ĝ x • ν₁ - V₁.1) - ⟪x + ĝ x • ν₁ - V₂.1, ν₂⟫ • ν₂ by abel, inner_sub_left,
        real_inner_smul_left, inner_add_smul_sub_of_mem hV₁ hx]
    rw [he]
    simp only [hH]
    rw [affProj_of_mem hx]
    simp only [affProj, hZ, w₁₂, GMT.projH, hf₂]
    rw [h1]
    module
  set ξ : Rn n → Rn n := fun u => e.symm (affProj V₁ u) with hξ
  have hξmem : ∀ u, ξ u ∈ affPlane V₁ := fun u => by
    have h1 := heν (ξ u)
    simp only [hξ, e.apply_symm_apply] at h1 ⊢
    rw [mem_affPlane, inner_sub_left, ← h1, ← inner_sub_left]
    exact affProj_mem_affPlane hV₁ u
  have hξproj : ∀ u ∈ affPlane V₂, affProj V₂ (Z (ξ u)) = u := by
    intro u hu
    refine affProj_injOn_affPlane hk0 (affProj_mem_affPlane hV₂ _) hu ?_
    rw [hΓ _ (hξmem u)]
    simp only [hξ, e.apply_symm_apply]
  -- Step 3: the function g₂
  set g₂ : Rn n → ℝ := fun u => f₂ (Z (ξ (affProj V₂ u))) with hg₂
  have hgraph : graphOn V₂ g₂ = graphOn V₁ ĝ := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨ξ u, hξmem u, ?_⟩
      have h1 := affProj_add_inner_smul V₂ (Z (ξ u))
      rw [hξproj u hu] at h1
      simp only [hg₂, affProj_of_mem hu]
      exact h1.symm
    · rintro ⟨x', hx', rfl⟩
      set u := affProj V₂ (Z x')
      have hu : u ∈ affPlane V₂ := affProj_mem_affPlane hV₂ _
      have heq : Z (ξ u) = Z x' := by
        have h1 := hflat2 _ (hξmem u) _ hx'
        rw [hξproj u hu, sub_self, norm_zero, mul_zero] at h1
        exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
      refine ⟨u, hu, ?_⟩
      simp only [hg₂, affProj_of_mem hu]
      rw [heq]
      exact affProj_add_inner_smul V₂ (Z x')
  have hlip : ∀ u u', |g₂ u - g₂ u'| ≤ 3 * δ * dist u u' := by
    intro u u'
    have ha := hξproj _ (affProj_mem_affPlane hV₂ u)
    have hb := hξproj _ (affProj_mem_affPlane hV₂ u')
    have h1 := hflat1 _ (hξmem (affProj V₂ u)) _ (hξmem (affProj V₂ u'))
    have h2 := hflat2 _ (hξmem (affProj V₂ u)) _ (hξmem (affProj V₂ u'))
    rw [ha, hb] at h2
    have h3 : ‖affProj V₂ u - affProj V₂ u'‖ ≤ dist u u' := by
      rw [← dist_eq_norm]; exact dist_affProj_le hV₂ u u'
    have h4 : ‖ξ (affProj V₂ u) - ξ (affProj V₂ u')‖ ≤
        ‖Z (ξ (affProj V₂ u)) - Z (ξ (affProj V₂ u'))‖ :=
      norm_sub_le_norm_add_smul_sub hV₁ (hξmem _) (hξmem _) _ _
    simp only [hg₂]
    calc |f₂ (Z (ξ (affProj V₂ u))) - f₂ (Z (ξ (affProj V₂ u')))|
        ≤ 2 * δ * ‖ξ (affProj V₂ u) - ξ (affProj V₂ u')‖ := h1
      _ ≤ 2 * δ * (3 / 2 * dist u u') := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = 3 * δ * dist u u' := by ring
  refine ⟨g₂, ⟨?_, fun u hu => ?_, ?_⟩, LipschitzWith.of_dist_le' fun u u' => ?_⟩
  · rw [hĝchart.1, hgraph]
  · -- the sup bound on the disc
    have hu2 : affProj V₂ u = u := affProj_of_mem hu.1
    set a := Z (ξ u)
    have hga : g₂ u = f₂ a := by simp only [hg₂, hu2, a]
    have hπa : affProj V₂ a = u := hξproj u hu.1
    have hf1a : f₁ a = ĝ (ξ u) := inner_add_smul_sub_of_mem hV₁ (hξmem u) _
    have hsabs : |s * f₂ a| = |f₂ a| := by rcases hs with rfl | rfl <;> simp
    have e1 : |f₂ a| ≤ δ * r + (r + ‖a - y‖) * δ := by
      have h1 : |⟪a - V₁.1, ν₁⟫ - s * f₂ a| ≤ (r + ‖a - y‖) * δ := hf a
      have h2 := abs_sub_abs_le_abs_sub (s * f₂ a) ⟪a - V₁.1, ν₁⟫
      rw [abs_sub_comm, hsabs] at h2
      have h3 : ⟪a - V₁.1, ν₁⟫ = ĝ (ξ u) := hf1a
      have h4 := hĝsup (ξ u)
      rw [h3] at h1 h2
      linarith
    have e2 : ‖a - y‖ ≤ R + |f₂ a| + |f₂ y| := by
      have hid : a - y = (affProj V₂ a - affProj V₂ y) + (f₂ a - f₂ y) • ν₂ := by
        have h1 := affProj_add_inner_smul V₂ a
        have h2 := affProj_add_inner_smul V₂ y
        simp only [hf₂]
        rw [sub_smul]
        nth_rewrite 1 [← h1, ← h2]
        abel
      rw [hid]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, hV₂, mul_one, Real.norm_eq_abs, hπa]
      have h3 : ‖u - affProj V₂ y‖ < R := by
        have := hu.2; rwa [mem_ball, dist_eq_norm] at this
      have := abs_sub (f₂ a) (f₂ y)
      linarith
    have e3 : |f₂ y| ≤ r / 2 + r * δ := by
      have h1 : |⟪y - V₁.1, ν₁⟫ - s * f₂ y| ≤ (r + ‖y - y‖) * δ := hf y
      rw [sub_self, norm_zero, add_zero] at h1
      have hsy : |s * f₂ y| = |f₂ y| := by rcases hs with rfl | rfl <;> simp
      have h2 := abs_sub_abs_le_abs_sub (s * f₂ y) ⟪y - V₁.1, ν₁⟫
      rw [abs_sub_comm, hsy] at h2
      linarith
    rw [hga]
    exact regraph_numeric hr hδ hδ' hR (abs_nonneg _) e1 e2 e3
  · exact (LipschitzWith.of_dist_le' fun u u' => by
      rw [Real.dist_eq]
      refine (hlip u u').trans ?_
      have := mul_nonneg hδ (dist_nonneg (x := u) (y := u'))
      linarith).lipschitzOnWith
  · rw [Real.dist_eq]; exact hlip u u'

end GMTFoundations
