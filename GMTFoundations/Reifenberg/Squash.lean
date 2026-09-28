/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.ReifenbergMap
import Mathlib.Data.Real.StarOrdered

/-!
# The squash lemma (Miśkiewicz Lemma 3.5)

The squash lemma of M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn.
Math. 43 (2018); arXiv:1612.02461 (Lemma 3.5; hereafter Miś), a modified version of the squash
lemma of A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and
minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043 (Lemma 4.12;
hereafter NV), specialized to hyperplanes. Miś's proof is partly a sketch; this file gives a
complete proof with explicit constants, which differs from the source as follows.

* The δ₀-independent bound in part (1) of Miś Lemma 3.5 (`‖g₁‖ ≤ C δ₁` near each centre, whatever
  `δ₀`) is only asserted in Miś's proof ("independent of δ₀, if only δ₀ ≤ 1"). It is essential:
  without it the chart bounds in the proof of Miś Proposition 4.3 compound geometrically from
  scale to scale. It is proved here as (1b), with `C_sq = 9^{n+2}`.
* Miś states the set identity as "`σ(G₀)` restricted to `4B_r(y)` is a graph"; it holds in the
  form `σ(G₀) ∩ B_{4r}(y) = graph(g₁) ∩ B_{4r}(y)` with `g₁` defined on all of the plane (1a).
  The corresponding statement for `σ(T)`, used in Miś Proposition 4.3, needs in addition that no
  point of `T` outside `B_{5r}(y)` is moved into `B_{4r}(y)`; this is (1a′).
* Miś assumes `δ₀ ≤ 1`; the set identity (1a) needs `δ₀ + 5δ₁ < 1` (points of the output graph
  in `B_{4r}(y)` must come from `B_{5r}(y)`), so here `δ₀ ≤ 1/2`.
* Miś's hypothesis `d(y, V) ≤ r/2` is not needed.

## Main statements

* `squash`: under `planeDist c r (Vp c) V ≤ δ₁` for the centres in `B_{10r}(y)` and a
  chart `IsChart T V g₀ y (5r) r δ₀`, with `δ₀ ≤ 1/2`, `δ₁ ≤ δ_sq n`:
  - (1a) `σ(T ∩ B_{5r}(y)) ∩ B_{4r}(y) = graphOn V g₁ ∩ B_{4r}(y)`, with `|g₁| ≤ C_sq(δ₀+δ₁) r` and
    `Lip g₁ ≤ C_sq(δ₀+δ₁)` globally;
  - (1b) the δ₀-free bound: `|g₁| ≤ C_sq δ₁ r` and `Lip g₁ ≤ C_sq δ₁` on
    `disc V c (5r/2)` for every centre `c ∈ Y ∩ B_{10r}(y)` with `|f_V(c)| ≤ r/2`;
  - (2) `|σ a − a| ≤ (δ₀ + 5δ₁) r` on `T ∩ B_{5r}(y)`;
  - (3) `σ` is `(1 + C_sq²(δ₀² + δ₁²))`-bi-Lipschitz on `T ∩ B_{5r}(y)`;
  - (1a′) the same set identity for `σ(T)` when points of `T` mapped into `B_{4r}(y)` come from
    `B_{5r}(y)`.

## Implementation

After globalizing `g₀` (Lemma G, `IsChart.exists_global`) and localizing `Y` to `Y ∩ B_{10r}(y)`
(`reifenbergMap_of_subset`), everything is proved for a finite family all of whose planes are
`δ₁`-close to `V` (the private `CoreHyp`). With `Z(x) = x + g(x) ν`,
`σ(Z x) = sqT x + sqN x • ν` exactly, where
`sqT x = x − Σ_c λ_c(Z x) f_c(Z x) projH ν ν_c` and `sqN x = g x − Σ_c λ_c(Z x) f_c(Z x) ⟪ν_c, ν⟫`.
The product lemma PL (`norm_sum_smul_sub_le`) gives `Lip(sqT − id) ≤ K₁ δ₁ (δ₀ + δ₁)` and
`Lip sqN ≤ K₁ (δ₀ + δ₁)`, with `K₁ = 32·9ⁿ + 1`; on `{ψ ∘ Z = 0}`,
`sqN = Σ λ_c (g − f_c ⟪ν_c, ν⟫)` has Lipschitz constant `O(δ₁)` (Step 7). `perturbId` inverts
`sqT` on the plane. Steps 0–8 label the sections and proof steps below.
-/

public noncomputable section

namespace GMTFoundations

open Metric Set
open scoped RealInnerProductSpace NNReal

variable {n : ℕ}

/-! ### The core: all planes close to `V`, global graph function -/

/-- Hypotheses of the core squash computation, after globalizing and localizing (Step 0). -/
private structure CoreHyp (r : ℝ) (Y : Finset (Rn n)) (Vp : Rn n → Rn n × Rn n)
    (V : Rn n × Rn n) (g : Rn n → ℝ) (δ₀ δ₁ : ℝ) : Prop where
  hr : 0 < r
  sep : (Y : Set (Rn n)).Pairwise fun a b => r ≤ dist a b
  unitV : ‖V.2‖ = 1
  unitVp : ∀ c ∈ Y, ‖(Vp c).2‖ = 1
  tilt : ∀ c ∈ Y, planeDist c r (Vp c) V ≤ δ₁
  gsup : ∀ x, |g x| ≤ δ₀ * r
  glip : ∀ x x', |g x - g x'| ≤ δ₀ * dist x x'
  h0 : 0 ≤ δ₀
  h0' : δ₀ ≤ 1 / 2
  h1 : 0 ≤ δ₁
  h1' : δ₁ * (81 * 9 ^ n) ≤ 1

/-- The graph point `Z(x) = x + g(x) ν`. -/
private def cZ (V : Rn n × Rn n) (g : Rn n → ℝ) (x : Rn n) : Rn n := x + g x • V.2

/-- The amplitude `a_c(x) = f_c(Z x)`. -/
private def cAmp (Vp : Rn n → Rn n × Rn n) (V : Rn n × Rn n) (g : Rn n → ℝ) (c x : Rn n) : ℝ :=
  ⟪cZ V g x - (Vp c).1, (Vp c).2⟫

/-- The tangential part `Σ_c λ_c(Z x) a_c(x) projH ν ν_c`. -/
private def cTan (r : ℝ) (Y : Finset (Rn n)) (Vp : Rn n → Rn n × Rn n) (V : Rn n × Rn n)
    (g : Rn n → ℝ) (x : Rn n) : Rn n :=
  ∑ c ∈ Y, puLambda r Y c (cZ V g x) • (cAmp Vp V g c x • GMT.projH V.2 (Vp c).2)

/-- The normal part `σ^⊥(x) = g x − Σ_c λ_c(Z x) a_c(x) ⟪ν_c, ν⟫` (Step 5). -/
private def cNor (r : ℝ) (Y : Finset (Rn n)) (Vp : Rn n → Rn n × Rn n) (V : Rn n × Rn n)
    (g : Rn n → ℝ) (x : Rn n) : ℝ :=
  g x - ∑ c ∈ Y, puLambda r Y c (cZ V g x) • (cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫)

variable {r δ₀ δ₁ : ℝ} {Y : Finset (Rn n)} {Vp : Rn n → Rn n × Rn n} {V : Rn n × Rn n}
  {g : Rn n → ℝ} {x x' c : Rn n}

/-- The exact splitting `σ(Z x) = F(x) + σ^⊥(x) ν`. -/
private theorem reifenbergMap_cZ (r : ℝ) (Y : Finset (Rn n)) (Vp : Rn n → Rn n × Rn n)
    (V : Rn n × Rn n) (g : Rn n → ℝ) (x : Rn n) :
    reifenbergMap r Y Vp (cZ V g x) = (x - cTan r Y Vp V g x) + cNor r Y Vp V g x • V.2 := by
  have hterm : ∀ c ∈ Y, puLambda r Y c (cZ V g x) • (cAmp Vp V g c x • GMT.projH V.2 (Vp c).2) =
      (puLambda r Y c (cZ V g x) * cAmp Vp V g c x) • (Vp c).2 -
        (puLambda r Y c (cZ V g x) • (cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫)) • V.2 := by
    intro c _
    simp only [GMT.projH, smul_eq_mul]
    module
  rw [cTan, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, cNor, sub_smul,
    Finset.sum_smul]
  simp only [reifenbergMap, cZ, cAmp]
  abel

private theorem inner_cTan (hV : ‖V.2‖ = 1) (x : Rn n) : ⟪cTan r Y Vp V g x, V.2⟫ = 0 := by
  rw [cTan, sum_inner]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [real_inner_smul_left, real_inner_smul_left, GMT.inner_projH hV, mul_zero, mul_zero]

private theorem sub_cTan_mem (hV : ‖V.2‖ = 1) (hx : x ∈ affPlane V) :
    x - cTan r Y Vp V g x ∈ affPlane V := by
  rw [mem_affPlane, sub_right_comm, inner_sub_left, mem_affPlane.1 hx, inner_cTan hV,
    sub_zero]

private theorem inner_cZ (hV : ‖V.2‖ = 1) (hx : x ∈ affPlane V) :
    ⟪cZ V g x - V.1, V.2⟫ = g x :=
  inner_add_smul_sub_of_mem hV hx _

/-! #### Per-centre facts -/

section CoreLemmas


private theorem one_le_q : (1 : ℝ) ≤ 9 ^ n := one_le_pow₀ (by norm_num)

private theorem CoreHyp.q_mul_δ₁ (h : CoreHyp r Y Vp V g δ₀ δ₁) : 9 ^ n * δ₁ ≤ 1 / 81 := by
  have := h.h1'; linarith

private theorem CoreHyp.δ₁_le (h : CoreHyp r Y Vp V g δ₀ δ₁) : δ₁ ≤ 1 / 81 := by
  have := h.q_mul_δ₁
  have := mul_le_mul_of_nonneg_right (one_le_q (n := n)) h.h1
  linarith

private theorem CoreHyp.disp_le_one (h : CoreHyp r Y Vp V g δ₀ δ₁) : δ₀ + 5 * δ₁ ≤ 1 := by
  have := h.δ₁_le; have := h.h0'; linarith

private theorem CoreHyp.sign (h : CoreHyp r Y Vp V g δ₀ δ₁) (hc : c ∈ Y) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖V.2 - s • (Vp c).2‖ ≤ δ₁ ∧
      ∀ w : Rn n, |⟪w - V.1, V.2⟫ - s * ⟪w - (Vp c).1, (Vp c).2⟫| ≤ (r + ‖w - c‖) * δ₁ := by
  have ht := h.tilt c hc
  rw [planeDist_comm] at ht
  exact exists_sign_of_planeDist_le h.hr ht

private theorem CoreHyp.norm_projH_le (h : CoreHyp r Y Vp V g δ₀ δ₁)
    (hc : c ∈ Y) : ‖GMT.projH V.2 (Vp c).2‖ ≤ δ₁ := by
  obtain ⟨s, hs, hν, -⟩ := h.sign hc
  exact (norm_projH_le_of_sign h.unitV hs).trans hν

/-- (E1) `|f_c(w)| ≤ |f_V(w)| + (r + |w − c|) δ₁`. -/
private theorem CoreHyp.abs_inner_le (h : CoreHyp r Y Vp V g δ₀ δ₁) (hc : c ∈ Y) (w : Rn n) :
    |⟪w - (Vp c).1, (Vp c).2⟫| ≤ |⟪w - V.1, V.2⟫| + (r + ‖w - c‖) * δ₁ := by
  obtain ⟨s, hs, -, hf⟩ := h.sign hc
  have habs : |s * ⟪w - (Vp c).1, (Vp c).2⟫| = |⟪w - (Vp c).1, (Vp c).2⟫| := by
    rcases hs with rfl | rfl <;> simp
  have := hf w
  rw [← habs]
  have h2 := abs_sub_abs_le_abs_sub (s * ⟪w - (Vp c).1, (Vp c).2⟫) ⟪w - V.1, V.2⟫
  rw [abs_sub_comm] at h2
  linarith

/-- Step 2: `|a_c(x)| ≤ (δ₀ + 5δ₁) r` where `λ_c(Z x) > 0`. -/
private theorem CoreHyp.abs_amp_le (h : CoreHyp r Y Vp V g δ₀ δ₁) (hc : c ∈ Y) (hx : x ∈ affPlane V)
    (hpos : 0 < puLambda r Y c (cZ V g x)) : |cAmp Vp V g c x| ≤ (δ₀ + 5 * δ₁) * r := by
  have hd := dist_lt_of_puLambda_pos h.hr hpos
  rw [dist_eq_norm] at hd
  have h1 := h.abs_inner_le hc (cZ V g x)
  rw [inner_cZ h.unitV hx] at h1
  have h2 := h.gsup x
  have h3 : (r + ‖cZ V g x - c‖) * δ₁ ≤ 5 * r * δ₁ :=
    mul_le_mul_of_nonneg_right (by linarith) h.h1
  unfold cAmp
  linarith

/-- Step 2: `|a_c(x) − a_c(x')| ≤ (δ₀ + δ₁) |x − x'|` on the plane. -/
private theorem CoreHyp.abs_amp_sub_le (h : CoreHyp r Y Vp V g δ₀ δ₁)
    (hc : c ∈ Y) (hx : x ∈ affPlane V) (hx' : x' ∈ affPlane V) :
    |cAmp Vp V g c x - cAmp Vp V g c x'| ≤ (δ₀ + δ₁) * dist x x' := by
  obtain ⟨s, hs, hν, -⟩ := h.sign hc
  have hid : cAmp Vp V g c x - cAmp Vp V g c x' =
      ⟪x - x', (Vp c).2⟫ + (g x - g x') * ⟪V.2, (Vp c).2⟫ := by
    simp only [cAmp, cZ]
    rw [← inner_sub_left, show x + g x • V.2 - (Vp c).1 - (x' + g x' • V.2 - (Vp c).1) =
      (x - x') + (g x - g x') • V.2 by rw [sub_smul]; abel, inner_add_left, real_inner_smul_left]
  rw [hid]
  have h1 : |⟪x - x', (Vp c).2⟫| ≤ δ₁ * dist x x' := by
    refine (abs_inner_le_of_inner_eq_zero hs (inner_sub_eq_zero_of_mem hx hx')).trans ?_
    rw [dist_eq_norm]
    exact mul_le_mul_of_nonneg_right hν (norm_nonneg _)
  have h2 : |(g x - g x') * ⟪V.2, (Vp c).2⟫| ≤ δ₀ * dist x x' := by
    rw [abs_mul]
    exact (mul_le_mul (h.glip x x') (abs_inner_le_one h.unitV (h.unitVp c hc)) (abs_nonneg _)
      ((abs_nonneg _).trans (h.glip x x'))).trans_eq (mul_one _)
  have := abs_add_le ⟪x - x', (Vp c).2⟫ ((g x - g x') * ⟪V.2, (Vp c).2⟫)
  linarith

private theorem CoreHyp.dist_cZ_le (h : CoreHyp r Y Vp V g δ₀ δ₁)
    (x x' : Rn n) : dist (cZ V g x) (cZ V g x') ≤ 3 / 2 * dist x x' := by
  rw [dist_eq_norm, dist_eq_norm, cZ, cZ,
    show x + g x • V.2 - (x' + g x' • V.2) = (x - x') + (g x - g x') • V.2 by rw [sub_smul]; abel]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, h.unitV, mul_one, Real.norm_eq_abs]
  have := h.glip x x'
  rw [dist_eq_norm] at this
  have := mul_le_mul_of_nonneg_right h.h0' (norm_nonneg (x - x'))
  linarith

private theorem CoreHyp.sum_abs_lam_sub_le (h : CoreHyp r Y Vp V g δ₀ δ₁) (x x' : Rn n) :
    ∑ c ∈ Y, |puLambda r Y c (cZ V g x) - puLambda r Y c (cZ V g x')| ≤
      6 * 9 ^ n * dist x x' / r := by
  refine (sum_abs_puLambda_sub_le h.hr h.sep _ _).trans ?_
  have := h.dist_cZ_le x x'
  have hr := h.hr
  have hq : (0 : ℝ) ≤ 9 ^ n := by positivity
  calc 4 * 9 ^ n * (dist (cZ V g x) (cZ V g x') / r) ≤ 4 * 9 ^ n * (3 / 2 * dist x x' / r) := by
        gcongr
    _ = 6 * 9 ^ n * dist x x' / r := by ring

private theorem CoreHyp.A0 (h : CoreHyp r Y Vp V g δ₀ δ₁) : 0 ≤ (δ₀ + 5 * δ₁) * r :=
  mul_nonneg (by linarith [h.h0, h.h1]) h.hr.le

private theorem CoreHyp.A1 (h : CoreHyp r Y Vp V g δ₀ δ₁) : 0 ≤ (δ₀ + 5 * δ₁) * r * δ₁ :=
  mul_nonneg h.A0 h.h1

/-! #### Step 3: the tangential part -/

/-- `ℓ_T = K₁ δ₁ (δ₀ + δ₁)`, `K₁ = 32·9ⁿ + 1`. -/
private theorem CoreHyp.norm_cTan_sub_le (h : CoreHyp r Y Vp V g δ₀ δ₁)
    (hx : x ∈ affPlane V) (hx' : x' ∈ affPlane V) :
    ‖cTan r Y Vp V g x - cTan r Y Vp V g x'‖ ≤
      (32 * 9 ^ n + 1) * δ₁ * (δ₀ + δ₁) * dist x x' := by
  have hPL := norm_sum_smul_sub_le Y (u := fun c => puLambda r Y c (cZ V g x))
    (u' := fun c => puLambda r Y c (cZ V g x'))
    (b := fun c => cAmp Vp V g c x • GMT.projH V.2 (Vp c).2)
    (b' := fun c => cAmp Vp V g c x' • GMT.projH V.2 (Vp c).2)
    (A := (δ₀ + 5 * δ₁) * r * δ₁) (B := (δ₀ + δ₁) * dist x x' * δ₁)
    (mul_nonneg (mul_nonneg (add_nonneg h.h0 h.h1) dist_nonneg) h.h1)
    (fun _ _ => puLambda_nonneg) (fun _ _ => puLambda_nonneg) sum_puLambda_le_one
    (fun c hc hpos => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (h.abs_amp_le hc hx hpos) (h.norm_projH_le hc) (norm_nonneg _)
        h.A0)
    (fun c hc hpos => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (h.abs_amp_le hc hx' hpos) (h.norm_projH_le hc) (norm_nonneg _)
        h.A0)
    (fun c hc _ => by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (h.abs_amp_sub_le hc hx hx') (h.norm_projH_le hc) (norm_nonneg _)
        (mul_nonneg (add_nonneg h.h0 h.h1) dist_nonneg))
  refine hPL.trans ?_
  have hS := h.sum_abs_lam_sub_le x x'
  have hr := h.hr
  have hA0 : 0 ≤ (δ₀ + 5 * δ₁) * r * δ₁ := h.A1
  calc (δ₀ + 5 * δ₁) * r * δ₁ *
        ∑ c ∈ Y, |puLambda r Y c (cZ V g x) - puLambda r Y c (cZ V g x')| +
        (δ₀ + δ₁) * dist x x' * δ₁
      ≤ (δ₀ + 5 * δ₁) * r * δ₁ * (6 * 9 ^ n * dist x x' / r) + (δ₀ + δ₁) * dist x x' * δ₁ :=
        add_le_add (mul_le_mul_of_nonneg_left hS hA0) le_rfl
    _ = (6 * 9 ^ n * (δ₀ + 5 * δ₁) + (δ₀ + δ₁)) * δ₁ * dist x x' := by
        rw [show (δ₀ + 5 * δ₁) * r * δ₁ * (6 * 9 ^ n * dist x x' / r) =
          (δ₀ + 5 * δ₁) * δ₁ * (6 * 9 ^ n * dist x x') * (r / r) by ring, div_self hr.ne', mul_one]
        ring
    _ ≤ (32 * 9 ^ n + 1) * δ₁ * (δ₀ + δ₁) * dist x x' := by
        have hq0 : (0 : ℝ) ≤ 9 ^ n := by positivity
        have hd := dist_nonneg (x := x) (y := x')
        have : 6 * 9 ^ n * (δ₀ + 5 * δ₁) + (δ₀ + δ₁) ≤ (32 * 9 ^ n + 1) * (δ₀ + δ₁) := by
          linarith [mul_nonneg hq0 h.h0, mul_nonneg hq0 h.h1]
        have := mul_le_mul_of_nonneg_right this (mul_nonneg h.h1 hd)
        linarith

private theorem CoreHyp.norm_cTan_le (h : CoreHyp r Y Vp V g δ₀ δ₁) (hx : x ∈ affPlane V) :
    ‖cTan r Y Vp V g x‖ ≤ (δ₀ + 5 * δ₁) * r * δ₁ :=
  norm_sum_smul_le Y h.A1 (fun _ _ => puLambda_nonneg)
    sum_puLambda_le_one fun c hc hpos => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (h.abs_amp_le hc hx hpos) (h.norm_projH_le hc) (norm_nonneg _) h.A0

/-- `ℓ_T ≤ 1/2` under (Hs). -/
private theorem CoreHyp.ellT_le (h : CoreHyp r Y Vp V g δ₀ δ₁)
    : (32 * 9 ^ n + 1) * δ₁ * (δ₀ + δ₁) ≤ 1 / 2 := by
  have h1 := h.q_mul_δ₁
  have h2 := h.δ₁_le
  have h3 := h.h0'
  have h4 : (32 * 9 ^ n + 1) * δ₁ ≤ 33 / 81 := by linarith
  have h5 : δ₀ + δ₁ ≤ 1 / 2 + 1 / 81 := by linarith
  exact (mul_le_mul h4 h5 (add_nonneg h.h0 h.h1) (by norm_num)).trans (by norm_num)

private theorem CoreHyp.ellT_nonneg (h : CoreHyp r Y Vp V g δ₀ δ₁)
    : 0 ≤ (32 * 9 ^ n + 1) * δ₁ * (δ₀ + δ₁) := by
  have := one_le_q (n := n); have := h.h1; have := h.h0; positivity

/-- `(1 − ℓ_T)|x − x'| ≤ |F x − F x'|`, hence `|x − x'| ≤ 2 |F x − F x'|`. -/
private theorem CoreHyp.dist_le_two_mul (h : CoreHyp r Y Vp V g δ₀ δ₁)
    (hx : x ∈ affPlane V) (hx' : x' ∈ affPlane V) :
    dist x x' ≤ 2 * dist (x - cTan r Y Vp V g x) (x' - cTan r Y Vp V g x') := by
  have h1 := h.norm_cTan_sub_le hx hx'
  have h2 := h.ellT_le
  rw [dist_eq_norm, dist_eq_norm] at *
  have h3 : ‖x - x'‖ ≤ ‖x - cTan r Y Vp V g x - (x' - cTan r Y Vp V g x')‖ +
      ‖cTan r Y Vp V g x - cTan r Y Vp V g x'‖ := by
    calc ‖x - x'‖ = ‖(x - cTan r Y Vp V g x - (x' - cTan r Y Vp V g x')) +
          (cTan r Y Vp V g x - cTan r Y Vp V g x')‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have := mul_le_mul_of_nonneg_right h2 (norm_nonneg (x - x'))
  linarith

/-! #### Step 5: the normal part -/

private theorem CoreHyp.abs_cNor_sub_le (h : CoreHyp r Y Vp V g δ₀ δ₁)
    (hx : x ∈ affPlane V) (hx' : x' ∈ affPlane V) :
    |cNor r Y Vp V g x - cNor r Y Vp V g x'| ≤ (32 * 9 ^ n + 1) * (δ₀ + δ₁) * dist x x' := by
  have hPL := norm_sum_smul_sub_le Y (u := fun c => puLambda r Y c (cZ V g x))
    (u' := fun c => puLambda r Y c (cZ V g x'))
    (b := fun c => cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫)
    (b' := fun c => cAmp Vp V g c x' * ⟪(Vp c).2, V.2⟫)
    (A := (δ₀ + 5 * δ₁) * r) (B := (δ₀ + δ₁) * dist x x')
    (mul_nonneg (add_nonneg h.h0 h.h1) dist_nonneg)
    (fun _ _ => puLambda_nonneg) (fun _ _ => puLambda_nonneg) sum_puLambda_le_one
    (fun c hc hpos => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (h.abs_amp_le hc hx hpos) (abs_inner_le_one (h.unitVp c hc) h.unitV)
        (abs_nonneg _) h.A0).trans_eq (mul_one _))
    (fun c hc hpos => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (h.abs_amp_le hc hx' hpos) (abs_inner_le_one (h.unitVp c hc) h.unitV)
        (abs_nonneg _) h.A0).trans_eq (mul_one _))
    (fun c hc _ => by
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
      exact (mul_le_mul (h.abs_amp_sub_le hc hx hx') (abs_inner_le_one (h.unitVp c hc) h.unitV)
        (abs_nonneg _) (mul_nonneg (add_nonneg h.h0 h.h1) dist_nonneg)).trans_eq (mul_one _))
  rw [Real.norm_eq_abs] at hPL
  have hS := h.sum_abs_lam_sub_le x x'
  have hg := h.glip x x'
  have hr := h.hr
  have hq := one_le_q (n := n)
  have h0 := h.h0
  have h1 := h.h1
  have hd := dist_nonneg (x := x) (y := x')
  have hsplit : cNor r Y Vp V g x - cNor r Y Vp V g x' = (g x - g x') -
      (∑ c ∈ Y, puLambda r Y c (cZ V g x) • (cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫) -
        ∑ c ∈ Y, puLambda r Y c (cZ V g x') • (cAmp Vp V g c x' * ⟪(Vp c).2, V.2⟫)) := by
    simp only [cNor]; ring
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  have hA : (δ₀ + 5 * δ₁) * r *
      ∑ c ∈ Y, |puLambda r Y c (cZ V g x) - puLambda r Y c (cZ V g x')| ≤
      (δ₀ + 5 * δ₁) * r * (6 * 9 ^ n * dist x x' / r) :=
    mul_le_mul_of_nonneg_left hS h.A0
  have hA' : (δ₀ + 5 * δ₁) * r * (6 * 9 ^ n * dist x x' / r) =
      6 * 9 ^ n * (δ₀ + 5 * δ₁) * dist x x' := by
    rw [show (δ₀ + 5 * δ₁) * r * (6 * 9 ^ n * dist x x' / r) =
      6 * 9 ^ n * (δ₀ + 5 * δ₁) * dist x x' * (r / r) by ring, div_self hr.ne', mul_one]
  have hc : 6 * 9 ^ n * (δ₀ + 5 * δ₁) + δ₀ + (δ₀ + δ₁) ≤ (32 * 9 ^ n + 1) * (δ₀ + δ₁) := by
    have hq0 : (0 : ℝ) ≤ 9 ^ n := by positivity
    linarith [mul_le_mul_of_nonneg_right hq h0, mul_nonneg hq0 h1]
  have := mul_le_mul_of_nonneg_right hc hd
  linarith

private theorem CoreHyp.abs_cNor_le (h : CoreHyp r Y Vp V g δ₀ δ₁) (hx : x ∈ affPlane V) :
    |cNor r Y Vp V g x| ≤ (2 * δ₀ + 5 * δ₁) * r := by
  have hS := norm_sum_smul_le Y (u := fun c => puLambda r Y c (cZ V g x))
    (b := fun c => cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫) (A := (δ₀ + 5 * δ₁) * r)
    h.A0 (fun _ _ => puLambda_nonneg) sum_puLambda_le_one
    (fun c hc hpos => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (h.abs_amp_le hc hx hpos) (abs_inner_le_one (h.unitVp c hc) h.unitV)
        (abs_nonneg _) h.A0).trans_eq (mul_one _))
  rw [Real.norm_eq_abs] at hS
  have := h.gsup x
  rw [cNor]
  refine (abs_sub _ _).trans ?_
  linarith

/-! #### Step 7: the δ₀-free bound on `{ψ ∘ Z = 0}` -/

/-- `b_c(x) = g x − a_c(x) ⟪ν_c, ν⟫`; on `{ψ(Z x) = 0}`, `σ^⊥(x) = Σ_c λ_c(Z x) b_c(x)`. -/
private theorem cNor_eq_of_psi (hψ : puPsi r Y (cZ V g x) = 0) :
    cNor r Y Vp V g x =
      ∑ c ∈ Y, puLambda r Y c (cZ V g x) • (g x - cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫) := by
  have hsum : ∑ c ∈ Y, puLambda r Y c (cZ V g x) = 1 := by
    have := puPsi_add_sum (r := r) (Y := Y) (z := cZ V g x)
    rw [hψ, zero_add] at this
    exact this
  simp only [smul_eq_mul, mul_sub, Finset.sum_sub_distrib, cNor]
  rw [← Finset.sum_mul, hsum, one_mul]

private theorem CoreHyp.abs_b_le (h : CoreHyp r Y Vp V g δ₀ δ₁) (hc : c ∈ Y) (hx : x ∈ affPlane V)
    (hpos : 0 < puLambda r Y c (cZ V g x)) :
    |g x - cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫| ≤ 6 * δ₁ * r := by
  obtain ⟨s, hs, hν, hf⟩ := h.sign hc
  have hd := dist_lt_of_puLambda_pos h.hr hpos
  rw [dist_eq_norm] at hd
  have he := hf (cZ V g x)
  rw [inner_cZ h.unitV hx] at he
  have he' : |g x - s * cAmp Vp V g c x| ≤ 5 * r * δ₁ :=
    he.trans (mul_le_mul_of_nonneg_right (by linarith) h.h1)
  have hk := abs_sign_sub_inner_le h.unitV (h.unitVp c hc) hs
  have hk' : |s - ⟪(Vp c).2, V.2⟫| ≤ δ₁ ^ 2 / 2 := by
    refine hk.trans ?_
    have := pow_le_pow_left₀ (norm_nonneg _) hν 2
    linarith
  have hA := h.abs_amp_le hc hx hpos
  have hid : g x - cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫ =
      (g x - s * cAmp Vp V g c x) + cAmp Vp V g c x * (s - ⟪(Vp c).2, V.2⟫) := by ring
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have hd1 := h.disp_le_one
  have hr := h.hr
  have h1 := h.h1
  have h1' := h.δ₁_le
  have : |cAmp Vp V g c x| ≤ r := by
    have := mul_le_mul_of_nonneg_right hd1 hr.le
    linarith
  have : |cAmp Vp V g c x| * |s - ⟪(Vp c).2, V.2⟫| ≤ r * (δ₁ ^ 2 / 2) :=
    mul_le_mul this hk' (abs_nonneg _) hr.le
  have : r * (δ₁ ^ 2 / 2) ≤ r * δ₁ := by
    apply mul_le_mul_of_nonneg_left _ hr.le
    have := mul_le_mul_of_nonneg_left h1' h1
    linarith
  linarith

private theorem CoreHyp.abs_b_sub_le (h : CoreHyp r Y Vp V g δ₀ δ₁)
    (hc : c ∈ Y) (hx : x ∈ affPlane V) (hx' : x' ∈ affPlane V) :
    |(g x - cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫) - (g x' - cAmp Vp V g c x' * ⟪(Vp c).2, V.2⟫)| ≤
      2 * δ₁ * dist x x' := by
  obtain ⟨s, hs, hν, -⟩ := h.sign hc
  set k := ⟪(Vp c).2, V.2⟫
  have hid : cAmp Vp V g c x - cAmp Vp V g c x' =
      ⟪x - x', (Vp c).2⟫ + (g x - g x') * k := by
    simp only [cAmp, cZ, k]
    rw [← inner_sub_left, show x + g x • V.2 - (Vp c).1 - (x' + g x' • V.2 - (Vp c).1) =
      (x - x') + (g x - g x') • V.2 by rw [sub_smul]; abel, inner_add_left, real_inner_smul_left,
      real_inner_comm V.2]
  have hid2 : (g x - cAmp Vp V g c x * k) - (g x' - cAmp Vp V g c x' * k) =
      (g x - g x') * (1 - k ^ 2) - ⟪x - x', (Vp c).2⟫ * k := by
    have : cAmp Vp V g c x = cAmp Vp V g c x' + (⟪x - x', (Vp c).2⟫ + (g x - g x') * k) := by
      rw [← hid]; ring
    rw [this]; ring
  rw [hid2]
  have h1 : |⟪x - x', (Vp c).2⟫| ≤ δ₁ * dist x x' := by
    refine (abs_inner_le_of_inner_eq_zero hs (inner_sub_eq_zero_of_mem hx hx')).trans ?_
    rw [dist_eq_norm]
    exact mul_le_mul_of_nonneg_right hν (norm_nonneg _)
  have hk1 : |k| ≤ 1 := abs_inner_le_one (h.unitVp c hc) h.unitV
  have hk2 : 1 - k ^ 2 ≤ δ₁ ^ 2 := by
    have := one_sub_inner_sq_le h.unitV (h.unitVp c hc) hs
    have := pow_le_pow_left₀ (norm_nonneg _) hν 2
    linarith
  have hk3 : 0 ≤ 1 - k ^ 2 := sub_nonneg.2 ((sq_le_one_iff_abs_le_one k).2 hk1)
  have hg := h.glip x x'
  have h0' := h.h0'
  have h1' := h.δ₁_le
  have hd := dist_nonneg (x := x) (y := x')
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hk3]
  have e1 : |g x - g x'| * (1 - k ^ 2) ≤ δ₀ * dist x x' * δ₁ ^ 2 :=
    mul_le_mul hg hk2 hk3 (mul_nonneg h.h0 hd)
  have e2 : |⟪x - x', (Vp c).2⟫| * |k| ≤ δ₁ * dist x x' :=
    (mul_le_mul h1 hk1 (abs_nonneg _) (mul_nonneg h.h1 hd)).trans_eq (mul_one _)
  have e3 : δ₀ * dist x x' * δ₁ ^ 2 ≤ δ₁ * dist x x' := by
    have : δ₀ * δ₁ ≤ 1 := by
      have := mul_le_mul h0' h1' h.h1 (by norm_num)
      linarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg h.h1 hd)
    linarith
  linarith

private theorem CoreHyp.abs_cNor_le_of_psi (h : CoreHyp r Y Vp V g δ₀ δ₁)
    (hx : x ∈ affPlane V) (hψ : puPsi r Y (cZ V g x) = 0) :
    |cNor r Y Vp V g x| ≤ 6 * δ₁ * r := by
  rw [cNor_eq_of_psi hψ]
  have := norm_sum_smul_le Y (u := fun c => puLambda r Y c (cZ V g x))
    (b := fun c => g x - cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫) (A := 6 * δ₁ * r)
    (mul_nonneg (mul_nonneg (by norm_num) h.h1) h.hr.le) (fun _ _ => puLambda_nonneg)
    sum_puLambda_le_one
    (fun c hc hpos => by rw [Real.norm_eq_abs]; exact h.abs_b_le hc hx hpos)
  rwa [Real.norm_eq_abs] at this

private theorem CoreHyp.abs_cNor_sub_le_of_psi (h : CoreHyp r Y Vp V g δ₀ δ₁)
    (hx : x ∈ affPlane V) (hx' : x' ∈ affPlane V)
    (hψ : puPsi r Y (cZ V g x) = 0) (hψ' : puPsi r Y (cZ V g x') = 0) :
    |cNor r Y Vp V g x - cNor r Y Vp V g x'| ≤ (36 * 9 ^ n + 2) * δ₁ * dist x x' := by
  rw [cNor_eq_of_psi hψ, cNor_eq_of_psi hψ']
  have hPL := norm_sum_smul_sub_le Y (u := fun c => puLambda r Y c (cZ V g x))
    (u' := fun c => puLambda r Y c (cZ V g x'))
    (b := fun c => g x - cAmp Vp V g c x * ⟪(Vp c).2, V.2⟫)
    (b' := fun c => g x' - cAmp Vp V g c x' * ⟪(Vp c).2, V.2⟫)
    (A := 6 * δ₁ * r) (B := 2 * δ₁ * dist x x')
    (mul_nonneg (mul_nonneg (by norm_num) h.h1) dist_nonneg)
    (fun _ _ => puLambda_nonneg) (fun _ _ => puLambda_nonneg) sum_puLambda_le_one
    (fun c hc hpos => by rw [Real.norm_eq_abs]; exact h.abs_b_le hc hx hpos)
    (fun c hc hpos => by rw [Real.norm_eq_abs]; exact h.abs_b_le hc hx' hpos)
    (fun c hc _ => by rw [Real.norm_eq_abs]; exact h.abs_b_sub_le hc hx hx')
  rw [Real.norm_eq_abs] at hPL
  refine hPL.trans ?_
  have hS := h.sum_abs_lam_sub_le x x'
  have hr := h.hr
  have h1 := h.h1
  calc 6 * δ₁ * r * ∑ c ∈ Y, |puLambda r Y c (cZ V g x) - puLambda r Y c (cZ V g x')| +
        2 * δ₁ * dist x x'
      ≤ 6 * δ₁ * r * (6 * 9 ^ n * dist x x' / r) + 2 * δ₁ * dist x x' :=
        add_le_add (mul_le_mul_of_nonneg_left hS
          (mul_nonneg (mul_nonneg (by norm_num) h1) hr.le)) le_rfl
    _ = (36 * 9 ^ n + 2) * δ₁ * dist x x' := by
        rw [show 6 * δ₁ * r * (6 * 9 ^ n * dist x x' / r) =
          36 * 9 ^ n * δ₁ * dist x x' * (r / r) by ring, div_self hr.ne', mul_one]
        ring

/-! #### Step 4: inverting `F = id − cTan` on the plane -/

private theorem CoreHyp.exists_inverse (h : CoreHyp r Y Vp V g δ₀ δ₁) :
    ∃ φ : Rn n → Rn n, ∀ u ∈ affPlane V, φ u ∈ affPlane V ∧ φ u - cTan r Y Vp V g (φ u) = u := by
  set ℓ := (32 * 9 ^ n + 1) * δ₁ * (δ₀ + δ₁)
  set H : Rn n → Rn n := fun w => -cTan r Y Vp V g (affProj V w)
  have hℓ0 : 0 ≤ ℓ := h.ellT_nonneg
  have hlip : LipschitzWith (Real.toNNReal ℓ) H := by
    refine LipschitzWith.of_dist_le' fun w w' => ?_
    simp only [H]
    rw [dist_neg_neg, dist_eq_norm]
    refine (h.norm_cTan_sub_le (affProj_mem_affPlane h.unitV w)
      (affProj_mem_affPlane h.unitV w')).trans ?_
    exact mul_le_mul_of_nonneg_left (dist_affProj_le h.unitV w w') hℓ0
  have hℓ1 : Real.toNNReal ℓ < 1 := by
    rw [Real.toNNReal_lt_one]; linarith [h.ellT_le]
  have hHν : ∀ w, ⟪H w, V.2⟫ = 0 := fun w => by
    simp only [H, inner_neg_left, inner_cTan h.unitV, neg_zero]
  obtain ⟨e, he, -, hinner⟩ := perturbId hℓ1 hlip hHν
  refine ⟨e.symm, fun u hu => ?_⟩
  have hmem : e.symm u ∈ affPlane V := by
    have h1 := hinner (e.symm u)
    rw [e.apply_symm_apply] at h1
    rw [mem_affPlane, inner_sub_left, ← h1, ← inner_sub_left]
    exact hu
  refine ⟨hmem, ?_⟩
  have h2 : e (e.symm u) = u := e.apply_symm_apply u
  rw [he] at h2
  simp only [H, affProj_of_mem hmem] at h2
  rw [sub_eq_add_neg]
  exact h2

/-! #### The numerics of Step 8 -/

/-- The numerics of Step 8 in abstract form: `ℓ = K δ₁ (δ₀ + δ₁)`, `D = δ₀ + δ₁`,
`E = δ₀² + δ₁²`, `C = (81·9ⁿ)²`. -/
private theorem bilip_numerics_core {K ℓ D E C δ₀ : ℝ} (hK0 : 0 ≤ K) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ 1 / 2) (hE0 : 0 ≤ E) (hδ : δ₀ ^ 2 ≤ E) (hD2 : D ^ 2 ≤ 2 * E)
    (hℓD : ℓ ≤ K * D ^ 2) (hK2 : 5 / 2 * K + K ^ 2 ≤ C) (hK4 : 4 * K + 1 ≤ C) :
    (1 + ℓ) ^ 2 + (K * D) ^ 2 ≤ (1 + C * E) ^ 2 ∧
    1 + δ₀ ^ 2 ≤ ((1 + C * E) * (1 - ℓ)) ^ 2 := by
  have hC0 : 0 ≤ C := by linarith
  have hCE0 : 0 ≤ C * E := mul_nonneg hC0 hE0
  have hℓE : ℓ ≤ 2 * K * E := by
    have := mul_le_mul_of_nonneg_left hD2 hK0
    linarith
  constructor
  · have e1 := mul_le_mul_of_nonneg_left hℓ hℓ0
    have e4 := mul_le_mul hK2 hD2 (sq_nonneg _) hC0
    have e5 := sq_nonneg (C * E)
    linarith
  · have f1 : 1 + E / 2 ≤ (1 + C * E) * (1 - ℓ) := by
      have a := mul_le_mul_of_nonneg_right hℓ hCE0
      have b := mul_le_mul_of_nonneg_right hK4 hE0
      linarith
    have f3 := pow_le_pow_left₀ (by linarith) f1 2
    have e5 := sq_nonneg E
    linarith

private theorem CoreHyp.bilip_numerics (h : CoreHyp r Y Vp V g δ₀ δ₁) :
    (1 + (32 * 9 ^ n + 1) * δ₁ * (δ₀ + δ₁)) ^ 2 + ((32 * 9 ^ n + 1) * (δ₀ + δ₁)) ^ 2 ≤
      (1 + (81 * 9 ^ n) ^ 2 * (δ₀ ^ 2 + δ₁ ^ 2)) ^ 2 ∧
    1 + δ₀ ^ 2 ≤ ((1 + (81 * 9 ^ n) ^ 2 * (δ₀ ^ 2 + δ₁ ^ 2)) *
      (1 - (32 * 9 ^ n + 1) * δ₁ * (δ₀ + δ₁))) ^ 2 := by
  have hq : (1 : ℝ) ≤ 9 ^ n := one_le_q
  have h0 := h.h0
  have h1 := h.h1
  have hK0 : (0 : ℝ) ≤ 32 * 9 ^ n + 1 := by linarith
  have hq2 := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 9 ^ n)
  refine bilip_numerics_core hK0 h.ellT_nonneg h.ellT_le (by positivity)
    (le_add_of_nonneg_right (sq_nonneg δ₁)) (by linarith [sq_nonneg (δ₀ - δ₁)]) ?_
    (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left (show δ₁ ≤ δ₀ + δ₁ by linarith)
    (mul_nonneg hK0 (add_nonneg h0 h1))
  linarith

/-! #### Assembling the core (Steps 5–8) -/

/-- (1b) containment: for `c ∈ Y` with `|f_V(c)| ≤ r/2` and `u ∈ disc V c (5r/2)`, the graph point
over `φ(u)` lies in `B̄_{3r}(c)`, so `ψ = 0` there. -/
private theorem CoreHyp.psi_eq_zero (h : CoreHyp r Y Vp V g δ₀ δ₁) {φ : Rn n → Rn n}
    (hφ : ∀ u ∈ affPlane V, φ u ∈ affPlane V ∧ φ u - cTan r Y Vp V g (φ u) = u)
    (hc : c ∈ Y) (hfc : |⟪c - V.1, V.2⟫| ≤ r / 2) {u : Rn n} (hu : u ∈ disc V c (5 / 2 * r)) :
    puPsi r Y (cZ V g (φ u)) = 0 := by
  obtain ⟨hm, he⟩ := hφ u hu.1
  refine puPsi_eq_zero h.hr hc ?_
  set x := φ u
  have hsq := norm_sub_sq_eq h.unitV (cZ V g x) c
  rw [cZ, affProj_add_smul_of_mem h.unitV hm, ← cZ, inner_cZ h.unitV hm] at hsq
  have h1 : ‖x - u‖ ≤ r / 81 := by
    have : x - u = cTan r Y Vp V g x := by rw [← he]; abel
    rw [this]
    refine (h.norm_cTan_le hm).trans ?_
    have : (δ₀ + 5 * δ₁) * r ≤ r :=
      (mul_le_mul_of_nonneg_right h.disp_le_one h.hr.le).trans_eq (one_mul r)
    have := mul_le_mul this h.δ₁_le h.h1 h.hr.le
    linarith
  have h2 : ‖u - affProj V c‖ < 5 / 2 * r := by
    have := hu.2; rwa [mem_ball, dist_eq_norm] at this
  have h3 : ‖x - affProj V c‖ ≤ (5 / 2 + 1 / 81) * r := by
    have := norm_sub_le_norm_sub_add_norm_sub x u (affProj V c)
    linarith
  have h4 : |g x - ⟪c - V.1, V.2⟫| ≤ r := by
    have := h.gsup x
    have := mul_le_mul_of_nonneg_right h.h0' h.hr.le
    have := abs_sub (g x) ⟪c - V.1, V.2⟫
    linarith
  have hr := h.hr
  have h5 : ‖cZ V g x - c‖ ^ 2 ≤ (3 * r) ^ 2 := by
    rw [hsq]
    have := pow_le_pow_left₀ (norm_nonneg _) h3 2
    have := sq_le_sq' (abs_le.1 h4).1 (abs_le.1 h4).2
    linarith [sq_nonneg r]
  rw [dist_eq_norm]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h5

/-- The core squash lemma (Steps 1–8) for a family all of whose planes are close to
`V`, and a global graph function. -/
private theorem CoreHyp.main (h : CoreHyp r Y Vp V g δ₀ δ₁) :
    ∃ g₁ : Rn n → ℝ,
      reifenbergMap r Y Vp '' graphOn V g = graphOn V g₁ ∧
      (∀ u, |g₁ u| ≤ (2 * δ₀ + 5 * δ₁) * r) ∧
      (∀ u u', |g₁ u - g₁ u'| ≤ 2 * (32 * 9 ^ n + 1) * (δ₀ + δ₁) * dist u u') ∧
      (∀ c ∈ Y, |⟪c - V.1, V.2⟫| ≤ r / 2 → ∀ u ∈ disc V c (5 / 2 * r),
        |g₁ u| ≤ 6 * δ₁ * r ∧ ∀ u' ∈ disc V c (5 / 2 * r),
          |g₁ u - g₁ u'| ≤ 2 * (36 * 9 ^ n + 2) * δ₁ * dist u u') ∧
      (∀ a ∈ graphOn V g, dist (reifenbergMap r Y Vp a) a ≤ (δ₀ + 5 * δ₁) * r) ∧
      (∀ a ∈ graphOn V g, ∀ b ∈ graphOn V g,
        dist (reifenbergMap r Y Vp a) (reifenbergMap r Y Vp b) ≤
          (1 + (81 * 9 ^ n) ^ 2 * (δ₀ ^ 2 + δ₁ ^ 2)) * dist a b ∧
        dist a b ≤ (1 + (81 * 9 ^ n) ^ 2 * (δ₀ ^ 2 + δ₁ ^ 2)) *
          dist (reifenbergMap r Y Vp a) (reifenbergMap r Y Vp b)) := by
  obtain ⟨φ, hφ⟩ := h.exists_inverse
  have hφF : ∀ x ∈ affPlane V, φ (x - cTan r Y Vp V g x) = x := by
    intro x hx
    obtain ⟨hm, he⟩ := hφ _ (sub_cTan_mem h.unitV hx)
    have := h.dist_le_two_mul hm hx
    rw [he, dist_self, mul_zero] at this
    exact dist_le_zero.1 this
  have hφmem : ∀ u, φ (affProj V u) ∈ affPlane V := fun u =>
    (hφ _ (affProj_mem_affPlane h.unitV u)).1
  have hφdist : ∀ u u', dist (φ (affProj V u)) (φ (affProj V u')) ≤ 2 * dist u u' := by
    intro u u'
    refine (h.dist_le_two_mul (hφmem u) (hφmem u')).trans ?_
    rw [(hφ _ (affProj_mem_affPlane h.unitV u)).2, (hφ _ (affProj_mem_affPlane h.unitV u')).2]
    have := dist_affProj_le h.unitV u u'
    linarith
  refine ⟨fun u => cNor r Y Vp V g (φ (affProj V u)), ?_, fun u => ?_, fun u u' => ?_, ?_, ?_, ?_⟩
  · -- (★) the image identity
    ext w
    constructor
    · rintro ⟨a, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x - cTan r Y Vp V g x, sub_cTan_mem h.unitV hx, ?_⟩
      simp only
      rw [affProj_of_mem (sub_cTan_mem h.unitV hx), hφF x hx]
      exact (reifenbergMap_cZ r Y Vp V g x).symm
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨hm, he⟩ := hφ u hu
      refine ⟨cZ V g (φ u), ⟨φ u, hm, rfl⟩, ?_⟩
      simp only
      rw [reifenbergMap_cZ, he, affProj_of_mem hu]
  · exact h.abs_cNor_le (hφmem u)
  · refine (h.abs_cNor_sub_le (hφmem u) (hφmem u')).trans ?_
    have := hφdist u u'
    have : 0 ≤ (32 * 9 ^ n + 1) * (δ₀ + δ₁) := by
      have := h.h0; have := h.h1; positivity
    have := mul_le_mul_of_nonneg_left (hφdist u u') this
    linarith
  · intro c hc hfc u hu
    have hu1 : affProj V u = u := affProj_of_mem hu.1
    refine ⟨?_, fun u' hu' => ?_⟩
    · simp only [hu1]
      exact h.abs_cNor_le_of_psi (hφ u hu.1).1 (h.psi_eq_zero hφ hc hfc hu)
    · have hu2 : affProj V u' = u' := affProj_of_mem hu'.1
      have := h.abs_cNor_sub_le_of_psi (hφ u hu.1).1 (hφ u' hu'.1).1
        (h.psi_eq_zero hφ hc hfc hu) (h.psi_eq_zero hφ hc hfc hu')
      have hd := hφdist u u'
      simp only [hu1, hu2] at hd ⊢
      have : 0 ≤ (36 * 9 ^ n + 2) * δ₁ := by have := h.h1; positivity
      have := mul_le_mul_of_nonneg_left hd this
      linarith
  · -- (2) displacement
    rintro _ ⟨x, hx, rfl⟩
    rw [dist_eq_norm]
    refine (norm_reifenbergMap_sub_le h.unitVp _).trans ?_
    have hterm : ∀ c ∈ Y, puLambda r Y c (cZ V g x) * |⟪cZ V g x - (Vp c).1, (Vp c).2⟫| ≤
        puLambda r Y c (cZ V g x) * ((δ₀ + 5 * δ₁) * r) := by
      intro c hc
      rcases puLambda_nonneg.lt_or_eq with hpos | hzero
      · exact mul_le_mul_of_nonneg_left (h.abs_amp_le hc hx hpos) puLambda_nonneg
      · rw [← hzero, zero_mul, zero_mul]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_of_le_one_left h.A0 sum_puLambda_le_one
  · -- (3) bi-Lipschitz (Step 8)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    set ℓ := (32 * 9 ^ n + 1) * δ₁ * (δ₀ + δ₁)
    set L := 1 + (81 * 9 ^ n) ^ 2 * (δ₀ ^ 2 + δ₁ ^ 2)
    obtain ⟨hn1, hn2⟩ := h.bilip_numerics
    have hL0 : 0 ≤ L := by positivity
    have hℓ0 : 0 ≤ ℓ := h.ellT_nonneg
    have hℓ1 : ℓ ≤ 1 / 2 := h.ellT_le
    have hT := h.norm_cTan_sub_le hx hx'
    have hN := h.abs_cNor_sub_le hx hx'
    have hg := h.glip x x'
    have hFx := sub_cTan_mem (r := r) (Y := Y) (Vp := Vp) (g := g) h.unitV hx
    have hFx' := sub_cTan_mem (r := r) (Y := Y) (Vp := Vp) (g := g) h.unitV hx'
    have e1 : dist (reifenbergMap r Y Vp (cZ V g x)) (reifenbergMap r Y Vp (cZ V g x')) ^ 2 =
        ‖(x - cTan r Y Vp V g x) - (x' - cTan r Y Vp V g x')‖ ^ 2 +
          (cNor r Y Vp V g x - cNor r Y Vp V g x') ^ 2 := by
      rw [reifenbergMap_cZ, reifenbergMap_cZ, dist_eq_norm]
      exact norm_add_smul_sub_add_smul_sq h.unitV hFx hFx' _ _
    have e2 : dist (cZ V g x) (cZ V g x') ^ 2 = dist x x' ^ 2 + (g x - g x') ^ 2 := by
      rw [dist_eq_norm, dist_eq_norm]
      exact norm_add_smul_sub_add_smul_sq h.unitV hx hx' _ _
    have hsplit : (x - cTan r Y Vp V g x) - (x' - cTan r Y Vp V g x') =
        (x - x') - (cTan r Y Vp V g x - cTan r Y Vp V g x') := by abel
    have e3 : ‖(x - cTan r Y Vp V g x) - (x' - cTan r Y Vp V g x')‖ ≤ (1 + ℓ) * dist x x' := by
      rw [hsplit]
      refine (norm_sub_le _ _).trans ?_
      rw [← dist_eq_norm]
      linarith
    have e4 : (1 - ℓ) * dist x x' ≤ ‖(x - cTan r Y Vp V g x) - (x' - cTan r Y Vp V g x')‖ := by
      rw [hsplit]
      have := norm_sub_norm_le (x - x') (cTan r Y Vp V g x - cTan r Y Vp V g x')
      rw [← dist_eq_norm] at this
      linarith
    have hd := dist_nonneg (x := x) (y := x')
    have hNsq : (cNor r Y Vp V g x - cNor r Y Vp V g x') ^ 2 ≤
        ((32 * 9 ^ n + 1) * (δ₀ + δ₁) * dist x x') ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hN 2
    have hgsq : (g x - g x') ^ 2 ≤ (δ₀ * dist x x') ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hg 2
    constructor
    · have hup : dist (reifenbergMap r Y Vp (cZ V g x)) (reifenbergMap r Y Vp (cZ V g x')) ^ 2 ≤
          (L * dist (cZ V g x) (cZ V g x')) ^ 2 := by
        rw [e1, mul_pow, e2]
        have h3 := pow_le_pow_left₀ (norm_nonneg _) e3 2
        have hmain : ((1 + ℓ) * dist x x') ^ 2 + ((32 * 9 ^ n + 1) * (δ₀ + δ₁) * dist x x') ^ 2
            ≤ L ^ 2 * dist x x' ^ 2 := by
          have := mul_le_mul_of_nonneg_right hn1 (sq_nonneg (dist x x'))
          calc _ = ((1 + ℓ) ^ 2 + ((32 * 9 ^ n + 1) * (δ₀ + δ₁)) ^ 2) * dist x x' ^ 2 := by ring
            _ ≤ _ := this
        have h4 : 0 ≤ L ^ 2 * (g x - g x') ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
        rw [mul_add]
        linarith
      exact (pow_le_pow_iff_left₀ dist_nonneg (mul_nonneg hL0 dist_nonneg) two_ne_zero).1 hup
    · have hlow : dist (cZ V g x) (cZ V g x') ^ 2 ≤
          (L * dist (reifenbergMap r Y Vp (cZ V g x)) (reifenbergMap r Y Vp (cZ V g x'))) ^ 2 := by
        have f1 : dist (cZ V g x) (cZ V g x') ^ 2 ≤ (1 + δ₀ ^ 2) * dist x x' ^ 2 := by
          rw [e2]
          have : (δ₀ * dist x x') ^ 2 = δ₀ ^ 2 * dist x x' ^ 2 := by ring
          linarith
        have f2 : (1 + δ₀ ^ 2) * dist x x' ^ 2 ≤ (L * ((1 - ℓ) * dist x x')) ^ 2 := by
          have := mul_le_mul_of_nonneg_right hn2 (sq_nonneg (dist x x'))
          calc _ ≤ _ := this
            _ = _ := by ring
        have f3 : (1 - ℓ) * dist x x' ≤
            dist (reifenbergMap r Y Vp (cZ V g x)) (reifenbergMap r Y Vp (cZ V g x')) := by
          refine e4.trans ?_
          refine (pow_le_pow_iff_left₀ (norm_nonneg _) dist_nonneg two_ne_zero).1 ?_
          rw [e1]
          exact le_add_of_nonneg_right (sq_nonneg _)
        have f4 : 0 ≤ (1 - ℓ) * dist x x' := mul_nonneg (by linarith) hd
        have f5 := mul_le_mul_of_nonneg_left f3 hL0
        have f6 := pow_le_pow_left₀ (mul_nonneg hL0 f4) f5 2
        linarith
      exact (pow_le_pow_iff_left₀ dist_nonneg (mul_nonneg hL0 dist_nonneg) two_ne_zero).1 hlow

end CoreLemmas


/-! ### The squash lemma -/

private theorem nine_pow_ge_one (n : ℕ) : (1 : ℝ) ≤ 9 ^ n := one_le_pow₀ (by norm_num)

/-- **Squash lemma** (Miś Lemma 3.5, NV Lemma 4.12).

Let `σ = reifenbergMap r Y Vp` for an `r`-separated finite `Y` with unit normals, let `V` be a
plane with unit normal, `y` a point, and suppose
* (H1) `planeDist c r (Vp c) V ≤ δ₁` for every `c ∈ Y` with `|c − y| < 10r`;
* (H0) `IsChart T V g₀ y (5r) r δ₀`;
* (Hs) `0 ≤ δ₀ ≤ 1/2`, `0 ≤ δ₁ ≤ δ_sq n = 9^{-(n+2)}`.

Then there is a global `g₁ : Rn n → ℝ` with
* (1a) `σ(T ∩ B_{5r}(y)) ∩ B_{4r}(y) = graphOn V g₁ ∩ B_{4r}(y)`, `|g₁| ≤ C_sq(δ₀+δ₁) r` and
  `Lip g₁ ≤ C_sq(δ₀+δ₁)` on all of `Rn n`;
* (1b) (δ₀-free) for every `c ∈ Y` with `|c − y| < 10r` and `|f_V(c)| ≤ r/2`:
  `|g₁| ≤ C_sq δ₁ r` and `Lip g₁ ≤ C_sq δ₁` on `disc V c (5r/2)`;
* (2) `|σ a − a| ≤ (δ₀ + 5δ₁) r` on `T ∩ B_{5r}(y)`;
* (3) `σ` is `(1 + C_sq²(δ₀² + δ₁²))`-bi-Lipschitz on `T ∩ B_{5r}(y)`;
* (1a′) if every `a ∈ T` with `σ a ∈ B_{4r}(y)` lies in `B_{5r}(y)`, then
  `σ(T) ∩ B_{4r}(y) = graphOn V g₁ ∩ B_{4r}(y)`.

The hypothesis `d(y, V) ≤ r/2` of Miś is not needed; `δ₀ ≤ 1/2` replaces Miś's `δ₀ ≤ 1`, which
does not leave room for the displacement `(δ₀ + 5δ₁) r` in the set identity (1a). Miś proves the
δ₀-free bound (1b) only in a sketch. -/
theorem squash {r δ₀ δ₁ : ℝ} {Y : Finset (Rn n)} {Vp : Rn n → Rn n × Rn n} {V : Rn n × Rn n}
    {T : Set (Rn n)} {y : Rn n} {g₀ : Rn n → ℝ}
    (hr : 0 < r) (hY : (Y : Set (Rn n)).Pairwise fun a b => r ≤ dist a b)
    (hVp : ∀ c ∈ Y, ‖(Vp c).2‖ = 1) (hV : ‖V.2‖ = 1)
    (htilt : ∀ c ∈ Y, dist c y < 10 * r → planeDist c r (Vp c) V ≤ δ₁)
    (hchart : IsChart T V g₀ y (5 * r) r δ₀)
    (hδ₀ : 0 ≤ δ₀) (hδ₀' : δ₀ ≤ 1 / 2) (hδ₁ : 0 ≤ δ₁) (hδ₁' : δ₁ ≤ δ_sq n) :
    ∃ g₁ : Rn n → ℝ,
      reifenbergMap r Y Vp '' (T ∩ ball y (5 * r)) ∩ ball y (4 * r) =
        graphOn V g₁ ∩ ball y (4 * r) ∧
      (∀ u, |g₁ u| ≤ C_sq n * (δ₀ + δ₁) * r) ∧
      LipschitzWith (Real.toNNReal (C_sq n * (δ₀ + δ₁))) g₁ ∧
      (∀ c ∈ Y, dist c y < 10 * r → |⟪c - V.1, V.2⟫| ≤ r / 2 →
        (∀ u ∈ disc V c (5 / 2 * r), |g₁ u| ≤ C_sq n * δ₁ * r) ∧
        LipschitzOnWith (Real.toNNReal (C_sq n * δ₁)) g₁ (disc V c (5 / 2 * r))) ∧
      (∀ a ∈ T ∩ ball y (5 * r), dist (reifenbergMap r Y Vp a) a ≤ (δ₀ + 5 * δ₁) * r) ∧
      (∀ a ∈ T ∩ ball y (5 * r), ∀ b ∈ T ∩ ball y (5 * r),
        dist (reifenbergMap r Y Vp a) (reifenbergMap r Y Vp b) ≤
          (1 + C_sq n ^ 2 * (δ₀ ^ 2 + δ₁ ^ 2)) * dist a b ∧
        dist a b ≤ (1 + C_sq n ^ 2 * (δ₀ ^ 2 + δ₁ ^ 2)) *
          dist (reifenbergMap r Y Vp a) (reifenbergMap r Y Vp b)) ∧
      ((∀ a ∈ T, reifenbergMap r Y Vp a ∈ ball y (4 * r) → a ∈ ball y (5 * r)) →
        reifenbergMap r Y Vp '' T ∩ ball y (4 * r) = graphOn V g₁ ∩ ball y (4 * r)) := by
  classical
  -- Step 0: globalize and localize
  obtain ⟨ĝ, hĝsup, hĝlip, -, hĝchart⟩ := hchart.exists_global hV hδ₀ hr.le
  set Y' := Y.filter (fun c => dist c y < 10 * r) with hY'
  have hY'sub : Y' ⊆ Y := Finset.filter_subset _ _
  have hloc : ∀ w ∈ ball y (5 * r), reifenbergMap r Y' Vp w = reifenbergMap r Y Vp w := by
    intro w hw
    refine reifenbergMap_of_subset hr hY'sub fun c hc hc' => ?_
    have h10 : 10 * r ≤ dist c y := by
      by_contra hlt
      exact hc' (Finset.mem_filter.2 ⟨hc, not_le.1 hlt⟩)
    have := dist_triangle c w y
    rw [mem_ball] at hw
    rw [dist_comm w c]
    linarith
  have hq := nine_pow_ge_one n
  have hC : C_sq n = 81 * 9 ^ n := C_sq_eq n
  have h1' : δ₁ * (81 * 9 ^ n) ≤ 1 := by
    have := hδ₁'
    rwa [δ_sq, le_div_iff₀ (C_sq_pos n), hC] at this
  have hH : CoreHyp r Y' Vp V ĝ δ₀ δ₁ :=
    { hr := hr
      sep := hY.mono (Finset.coe_subset.2 hY'sub)
      unitV := hV
      unitVp := fun c hc => hVp c (hY'sub hc)
      tilt := fun c hc => htilt c (hY'sub hc) (Finset.mem_filter.1 hc).2
      gsup := hĝsup
      glip := fun x x' => by
        have := hĝlip.dist_le_mul x x'
        rwa [Real.coe_toNNReal _ hδ₀, Real.dist_eq] at this
      h0 := hδ₀
      h0' := hδ₀'
      h1 := hδ₁
      h1' := h1' }
  obtain ⟨g₁, himg, hsup, hlip, h1b, hdisp, hbil⟩ := hH.main
  have hG : T ∩ ball y (5 * r) = graphOn V ĝ ∩ ball y (5 * r) := hĝchart.1
  have hq₀ := mul_le_mul_of_nonneg_right hq hδ₀
  have hq₁ := mul_le_mul_of_nonneg_right hq hδ₁
  have hsmall : (δ₀ + 5 * δ₁) * r < r := by
    have : δ₁ ≤ 1 / 81 := by linarith
    exact (mul_lt_mul_of_pos_right (by linarith) hr).trans_eq (one_mul r)
  -- (1a) set identity
  have h1a : reifenbergMap r Y Vp '' (T ∩ ball y (5 * r)) ∩ ball y (4 * r) =
      graphOn V g₁ ∩ ball y (4 * r) := by
    ext w
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hw⟩
      refine ⟨?_, hw⟩
      rw [← hloc a ha.2, ← himg]
      rw [hG] at ha
      exact ⟨a, ha.1, rfl⟩
    · rintro ⟨hw1, hw4⟩
      rw [← himg] at hw1
      obtain ⟨a, ha, rfl⟩ := hw1
      have hd := hdisp a ha
      have ha5 : a ∈ ball y (5 * r) := by
        rw [mem_ball] at hw4 ⊢
        have := dist_triangle a (reifenbergMap r Y' Vp a) y
        rw [dist_comm] at hd
        linarith
      refine ⟨⟨a, ?_, (hloc a ha5).symm⟩, hw4⟩
      rw [hG]
      exact ⟨ha, ha5⟩
  refine ⟨g₁, h1a, fun u => ?_, ?_, fun c hc hcy hfc => ?_, fun a ha => ?_, fun a ha b hb => ?_,
    fun hT => ?_⟩
  · refine (hsup u).trans ?_
    rw [hC]
    have : 2 * δ₀ + 5 * δ₁ ≤ 81 * 9 ^ n * (δ₀ + δ₁) := by linarith
    exact mul_le_mul_of_nonneg_right this hr.le
  · refine LipschitzWith.of_dist_le' fun u u' => ?_
    rw [Real.dist_eq]
    refine (hlip u u').trans ?_
    rw [hC]
    have := dist_nonneg (x := u) (y := u')
    have : 2 * (32 * 9 ^ n + 1) * (δ₀ + δ₁) ≤ 81 * 9 ^ n * (δ₀ + δ₁) := by linarith
    exact mul_le_mul_of_nonneg_right this dist_nonneg
  · have hcY' : c ∈ Y' := Finset.mem_filter.2 ⟨hc, hcy⟩
    refine ⟨fun u hu => ((h1b c hcY' hfc u hu).1).trans ?_,
      LipschitzOnWith.of_dist_le' fun u hu u' hu' => ?_⟩
    · rw [hC]
      have : 6 * δ₁ ≤ 81 * 9 ^ n * δ₁ := by linarith
      exact mul_le_mul_of_nonneg_right this hr.le
    · rw [Real.dist_eq]
      refine ((h1b c hcY' hfc u hu).2 u' hu').trans ?_
      rw [hC]
      have := dist_nonneg (x := u) (y := u')
      have : 2 * (36 * 9 ^ n + 2) * δ₁ ≤ 81 * 9 ^ n * δ₁ := by linarith
      exact mul_le_mul_of_nonneg_right this dist_nonneg
  · rw [← hloc a ha.2]
    rw [hG] at ha
    exact hdisp a ha.1
  · rw [← hloc a ha.2, ← hloc b hb.2, hC]
    rw [hG] at ha hb
    exact hbil a ha.1 b hb.1
  · rw [← h1a]
    ext w
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hw⟩
      exact ⟨⟨a, ⟨ha, hT a ha hw⟩, rfl⟩, hw⟩
    · rintro ⟨⟨a, ha, rfl⟩, hw⟩
      exact ⟨⟨a, ha.1, rfl⟩, hw⟩

end GMTFoundations
