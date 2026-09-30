/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.Induction
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Discrete Reifenberg: one engine run and its mass bound

The inductive step in the proof of Theorem 1.1 of M. Miśkiewicz, *Discrete Reifenberg-type
theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018); arXiv:1612.02461 (§4: Proposition 4.3, the
estimates (4.1)–(4.3) and "Derivation of the bound"; hereafter Miś), for `q = 2`, `k = n − 1`.

Everything here is stated for a general covering run `D : CoverData n` under
`D.EngineHyp κ Λ J`, with no reference to atoms, levels of a finite family or the specific
constants of the discrete theorem: a general finite measure `D.μ`, a general scale ratio
`ρ = D.ρ`, a general threshold `θ = D.θ`, the upper bound `hup` (hypothesis (H2) of the tilt
lemma `planeDist_sq_le_of_mass`, constant `Λ`) as a hypothesis, and bounds for every depth `N`
(no termination). This lets both the discrete theorem and the rectifiable-Reifenberg argument use
it. The discrete instance (`Discrete.lean`) supplies `hup` by the upper-bound lemma
`levMeasure_ball_mul_le_of_claimAt_succ` plus the inductive hypothesis.

Deviations from Miś's proof of Proposition 4.3 and (4.1)–(4.2):
* Miś compares the best planes at `y′` and at the parent `z` by Lemma 3.3 at radius ratios `ρ/2`
  and `1/2` rather than `ρ` (via the intermediate plane `V(z, 2κr_i)`), without checking the
  near-plane hypothesis of Lemma 3.3. Here the tilt lemma `planeDist_sq_le_of_mass` is stated for
  an arbitrary ball and needs no near-plane hypothesis; the constants change by a factor `C(n, ρ)`.
* The tilt estimate is proved for all good centers `y′` within `10 r_{i+1}` of `y`, the range
  required by the squash lemma (Miś's proof considers `|y − y′| ≤ 5r_{i+1}`).
* In the comparison (4.2), Miś's lower bound `|T_i ∩ B/3| ≥ (1/10)(r_{i+1}/3)^k` is false for
  `k ≥ 9`, even for a flat plane at distance `r_{i+1}/4` from the center; so are the resulting
  constants `C₁ = 20·3^k` and `τ = 80^{−1}6^{−n}`. Here the lower bound is
  `ω_k (r_{i+1}/15)^k`, giving `C₁ = 2·15^k/ω_k` (and `τ = 1/(16·15^k)`, `ledgerTau`).
* Miś's (4.1) starts from `|T₀| = ω_k`, but `T₀` is a whole hyperplane. The area bound is
  localized to the nested windows `W_i` of `Induction.lean`.
* For the area bound of `T_i` on `5B_{r_{i+1}}(y_s)` Miś cites Proposition 4.3(b), which is about
  `T_{i+1}`; the graph property of `T_i` at the previous scale is what is used here.

## Main statements

* `EngineHyp.planeDist_sq_le`: the tilt estimate
  `planeDist² ≤ C_t θ⁻¹ (β²(c, κr_{i+1}) + β²(z, κr_i) + β²(z, 2κr_i))`.
* `EngineHyp.beta_rough`, `EngineHyp.tilt_le_small`, `EngineHyp.surfHyp`: with the rough bound
  the tilts are `≤ η`, so the surface construction of `Induction.lean` runs at every scale.
* `EngineHyp.sum_tilt_sq_le`, `EngineHyp.sum_eps_le`: the Carleson packing of the tilts and of the
  bi-Lipschitz excesses.
* `EngineHyp.hausdorffN_surf_le'` (**(4.1)**): `ℋ^k(T_N ∩ W_N) ≤ ω_k((1+ρ)r_j)^k + C_A J r_j^k/θ²`.
* `EngineHyp.measure_ball_leaf_le` (**(4.2)**): `μ(B_{r_l}(y)) ≤ θ C₁ ℋ^k(T_N ∩ B_{r_l/2}(y))` for
  bad and final leaves.
* `EngineHyp.engine_mass`: for every `N ≥ j`,
  `μ(P) ≤ θ C₁ ℋ^k(T_N ∩ W_N) + μ(⋃_{l ≤ N} E_l) + μ(⋃_{y ∈ Good_N} B_{r_N}(y))`.
-/

@[expose] public noncomputable section

namespace GMTFoundations.DiscreteReifenberg

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

/-! ### Constants of the step, as functions of `(n, ρ, κ)` -/

/-- The core tilt constant with the ratio `2κ/ρ` built in:
`K₀ = 48 · 3ⁿ (2κ/ρ)^{n+1} / ρ^{n+2}`. -/
def tiltK0 (n : ℕ) (ρ κ : ℝ) : ℝ := 48 * 3 ^ n * (2 * κ / ρ) ^ (n + 1) / ρ ^ (n + 2)

/-- The tilt constant of `EngineHyp.planeDist_sq_le`:
`planeDist² ≤ tiltConst · θ⁻¹ · (β² + β² + β²)`. -/
def tiltConst (n : ℕ) (ρ κ : ℝ) : ℝ := 2 * (1 + 4 / ρ ^ 2) * tiltK0 n ρ κ

/-- The rough-bound constant: `β²(z, s r_i) ≤ roughC · J / θ` for `s ≤ 2κ`. -/
def roughC (n : ℕ) (κ : ℝ) : ℝ := roughConst n * (8 * κ) ^ (n - 1)

/-- The engine smallness constant (in the form `J ≤ ε θ²`): it makes every tilt
`≤ η = smallConst n ρ`. -/
def smallEps (n : ℕ) (ρ κ : ℝ) : ℝ :=
  smallConst n ρ ^ 2 / (3 * tiltConst n ρ κ * roughC n κ)

section Constants

variable {ρ κ : ℝ}

theorem tiltK0_pos (hρ : 0 < ρ) (hκ : 0 < κ) : 0 < tiltK0 n ρ κ := by
  unfold tiltK0; positivity

theorem tiltConst_pos (hρ : 0 < ρ) (hκ : 0 < κ) : 0 < tiltConst n ρ κ := by
  have := tiltK0_pos (n := n) hρ hκ
  unfold tiltConst; positivity

theorem roughC_pos (hκ : 0 < κ) : 0 < roughC n κ := by
  have := roughConst_pos n
  unfold roughC; positivity

theorem smallEps_pos (hn : 1 ≤ n) (hρ : 0 < ρ) (hκ : 0 < κ) : 0 < smallEps n ρ κ := by
  have := smallConst_pos hn hρ
  have := tiltConst_pos (n := n) hρ hκ
  have := roughC_pos (n := n) hκ
  unfold smallEps; positivity

end Constants

namespace CoverData

/-- **The hypotheses of one engine run**, for a general covering
run `D` with planes `V i y = bestPlane μ y (κ ρ^i)`:
* `est`: the covering estimates' hypotheses (finite measure, good top ball, (1.3) with constant `J`
  on `B_{R₀ r_j}(p)`);
* `tilt_mass`, `hup`: the hypotheses of the tilt lemma `planeDist_sq_le_of_mass` (the smallness
  `ρ ≤ θ / (2 A_n Λ)` and the upper bound (H2) with constant `Λ`) at every good center of every
  scale `i ≥ j` (discrete case: the upper-bound lemma plus the inductive hypothesis; rectifiable
  case: the given upper density bound);
* `J_small`: the engine smallness `J ≤ ε θ²`;
* `fin_le`: final balls are not heavier than the threshold (vacuous when there are none). -/
structure EngineHyp (D : CoverData n) (κ Λ J : ℝ) : Prop where
  est : D.EstHyp κ J
  two_le_n : 2 ≤ n
  one_add_ρ_le_κ : 1 + D.ρ ≤ κ
  Λ_pos : 0 < Λ
  tilt_mass : D.ρ ≤ D.θ / (2 * farConst n * Λ)
  hup : ∀ i, D.j ≤ i → ∀ z ∈ D.good i, ∀ w ∈ ball z (D.ρ ^ i),
    D.μ (ball w (D.ρ * D.ρ ^ i)) ≤ ENNReal.ofReal (Λ * (D.ρ * D.ρ ^ i) ^ (n - 1))
  J_small : J ≤ smallEps n D.ρ κ * D.θ ^ 2
  fin_le : ∀ l, D.j < l → ∀ y ∈ D.fin l,
    D.μ (ball y (D.ρ ^ l)) ≤ ENNReal.ofReal (D.θ * (D.ρ ^ l) ^ (n - 1))

variable {D : CoverData n} {κ Λ J : ℝ}

private lemma two_term_le {C c₁ c₂ K β₁ β₂ : ℝ≥0∞} (h1 : C * c₁ ≤ K) (h2 : C * c₂ ≤ K) :
    C * (c₁ * β₁ + c₂ * β₂) ≤ K * (β₁ + β₂) := by
  rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc]
  gcongr

/-- `ofReal (C / (ρ^{n+2} θ r^{n+1})) · ofReal (R^{n+1}) ≤ ofReal (C q^{n+1} / (ρ^{n+2} θ))` when
`R ≤ q r`. -/
private lemma coeff_le {C ρ θ r R q : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ) (hθ : 0 < θ) (hr : 0 < r)
    (hR : 0 ≤ R) (hRq : R ≤ q * r) :
    ENNReal.ofReal (C / (ρ ^ (n + 2) * θ * r ^ (n + 1))) * ENNReal.ofReal (R ^ (n + 1)) ≤
      ENNReal.ofReal (C * q ^ (n + 1) / (ρ ^ (n + 2) * θ)) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hq : 0 ≤ q := by
    by_contra hq
    have := mul_neg_of_neg_of_pos (not_le.1 hq) hr
    linarith
  have h1 : R ^ (n + 1) ≤ q ^ (n + 1) * r ^ (n + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hR hRq _
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ C * (ρ ^ (n + 2) * θ) := by positivity
  calc C * R ^ (n + 1) * (ρ ^ (n + 2) * θ) = C * (ρ ^ (n + 2) * θ) * R ^ (n + 1) := by ring
    _ ≤ C * (ρ ^ (n + 2) * θ) * (q ^ (n + 1) * r ^ (n + 1)) := by gcongr
    _ = _ := by ring

/-- The coefficient of the tilt lemma `planeDist_sq_le_of_mass` at radius `t`, with the enlarged
plane radius `R ≤ 2κ t/ρ`, is at most `K₀ / θ`. -/
private lemma tilt_coeff_le {ρ κ θ t R : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) (hθ : 0 < θ) (ht : 0 < t)
    (hR : 0 ≤ R) (hRt : R ≤ 2 * κ / ρ * t) :
    ENNReal.ofReal (48 * 3 ^ n / (ρ ^ (n + 2) * θ * t ^ (n + 1))) *
      ENNReal.ofReal (R ^ (n + 1)) ≤ ENNReal.ofReal (tiltK0 n ρ κ / θ) := by
  refine (coeff_le (by positivity) hρ hθ ht hR hRt).trans (le_of_eq ?_)
  congr 1
  unfold tiltK0
  field_simp

section EngineHyp

variable (h : D.EngineHyp κ Λ J)
include h

theorem EngineHyp.hyp : D.Hyp := h.est.hyp

theorem EngineHyp.ρ_pos : 0 < D.ρ := h.est.ρ_pos

theorem EngineHyp.one_le_n : 1 ≤ n := le_trans (by norm_num) h.two_le_n

theorem EngineHyp.θ_pos : 0 < D.θ := h.est.θ_pos

theorem EngineHyp.κ_pos : 0 < κ := zero_lt_one.trans_le h.est.one_le_κ

theorem EngineHyp.J_nonneg : 0 ≤ J := h.est.J_nonneg

theorem EngineHyp.fin (x : Rn n) (r : ℝ) : D.μ (ball x r) ≠ ∞ := h.est.fin x r

/-- The parent of a good center at scale `i + 1` (`exists_parent`). -/
theorem EngineHyp.par_spec {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    D.par i y ∈ D.good i ∧ y ∈ ball (D.par i y) (D.ρ ^ i) ∧
      |⟪y - (D.V i (D.par i y)).1, (D.V i (D.par i y)).2⟫| < D.ρ ^ (i + 1) / 4 :=
  CoverData.par_spec hi (mem_avail_of_mem_succ h.hyp hi
    (Finset.mem_union_left _ (Finset.mem_union_left _ hy)))

/-- Step (A) of the tilt estimate: the tilt lemma at `(c, r_{i+1})`, comparing
`V(c, κ r_{i+1})` with `W = V(z, 2κ r_i)`. -/
theorem EngineHyp.tilt_A {i : ℕ} (hi : D.j ≤ i) {c z : Rn n} (hc : c ∈ D.good (i + 1))
    (hcz : dist c z < D.ρ ^ i + 10 * D.ρ ^ (i + 1)) :
    ENNReal.ofReal (planeDist c (D.ρ ^ (i + 1)) (bestPlane D.μ c (κ * D.ρ ^ (i + 1)))
        (bestPlane D.μ z (2 * κ * D.ρ ^ i)) ^ 2) ≤
      ENNReal.ofReal (tiltK0 n D.ρ κ / D.θ) *
        (jonesBetaSq D.μ c (κ * D.ρ ^ (i + 1)) + jonesBetaSq D.μ z (2 * κ * D.ρ ^ i)) := by
  have hρ0 := h.ρ_pos
  have hρ1 : D.ρ ≤ 1 / 100 := h.est.ρ_le
  have hκ := h.κ_pos
  have hκ1 := h.one_add_ρ_le_κ
  have hθ := h.θ_pos
  have hr' : 0 < D.ρ ^ i := pow_pos hρ0 i
  have hr : 0 < D.ρ ^ (i + 1) := pow_pos hρ0 (i + 1)
  have hrr : D.ρ ^ (i + 1) = D.ρ * D.ρ ^ i := pow_succ' _ _
  have hlow := le_measure_of_mem_good h.est (i := i + 1) (by omega) hc
  have hup := h.hup (i + 1) (by omega) c hc
  have hA := planeDist_bestPlane_sq_le_of_subset h.two_le_n (μ := D.μ) (x := c)
    (r := D.ρ ^ (i + 1)) (ρ := D.ρ) (a := D.θ) (b := Λ) hr hρ0 (by linarith) hθ h.Λ_pos
    h.tilt_mass (h.fin _ _) hlow hup (z₁ := c) (z₂ := z) (R₁ := κ * D.ρ ^ (i + 1))
    (R₂ := 2 * κ * D.ρ ^ i) (by positivity) (by positivity)
    (ball_subset_ball (mul_le_mul_of_nonneg_right hκ1 hr.le))
    (ball_subset_ball' (by
      rw [hrr] at hcz ⊢
      linarith [mul_le_mul_of_nonneg_right hρ1 hr'.le, mul_le_mul_of_nonneg_right hκ1 hr'.le,
        mul_le_mul_of_nonneg_right hρ1 (mul_pos hρ0 hr').le]))
    (h.fin _ _) (h.fin _ _)
  refine hA.trans (two_term_le ?_ ?_)
  · refine tilt_coeff_le hρ0 hκ hθ hr (by positivity) ?_
    have : 1 ≤ 2 / D.ρ := by rw [le_div_iff₀ hρ0]; linarith
    have : κ ≤ 2 * κ / D.ρ := by
      calc κ = κ * 1 := (mul_one κ).symm
        _ ≤ κ * (2 / D.ρ) := mul_le_mul_of_nonneg_left this hκ.le
        _ = 2 * κ / D.ρ := by ring
    exact mul_le_mul_of_nonneg_right this hr.le
  · refine tilt_coeff_le hρ0 hκ hθ hr (by positivity) (le_of_eq ?_)
    rw [hrr]; field_simp

/-- Step (B) of the tilt estimate: the tilt lemma at `(z, r_i)`, comparing
`W = V(z, 2κ r_i)` with `V(z, κ r_i)`. -/
theorem EngineHyp.tilt_B {i : ℕ} (hi : D.j ≤ i) {z : Rn n} (hz : z ∈ D.good i) :
    ENNReal.ofReal (planeDist z (D.ρ ^ i) (bestPlane D.μ z (2 * κ * D.ρ ^ i))
        (bestPlane D.μ z (κ * D.ρ ^ i)) ^ 2) ≤
      ENNReal.ofReal (tiltK0 n D.ρ κ / D.θ) *
        (jonesBetaSq D.μ z (2 * κ * D.ρ ^ i) + jonesBetaSq D.μ z (κ * D.ρ ^ i)) := by
  have hρ0 := h.ρ_pos
  have hρ1 : D.ρ ≤ 1 / 100 := h.est.ρ_le
  have hκ := h.κ_pos
  have hκ1 := h.one_add_ρ_le_κ
  have hθ := h.θ_pos
  have hr' : 0 < D.ρ ^ i := pow_pos hρ0 i
  have hlow := le_measure_of_mem_good h.est hi hz
  have hup := h.hup i hi z hz
  have hB := planeDist_bestPlane_sq_le_of_subset h.two_le_n (μ := D.μ) (x := z) (r := D.ρ ^ i)
    (ρ := D.ρ) (a := D.θ) (b := Λ) hr' hρ0 (by linarith) hθ h.Λ_pos h.tilt_mass (h.fin _ _)
    hlow hup (z₁ := z) (z₂ := z) (R₁ := 2 * κ * D.ρ ^ i) (R₂ := κ * D.ρ ^ i) (by positivity)
    (by positivity)
    (ball_subset_ball (by linarith [mul_le_mul_of_nonneg_right hκ1 hr'.le, mul_pos hκ hr']))
    (ball_subset_ball (mul_le_mul_of_nonneg_right hκ1 hr'.le))
    (h.fin _ _) (h.fin _ _)
  have h1ρ : 1 ≤ 1 / D.ρ := by rw [le_div_iff₀ hρ0]; linarith
  refine hB.trans (two_term_le ?_ ?_)
  · refine tilt_coeff_le hρ0 hκ hθ hr' (by positivity) ?_
    have : 2 * κ * D.ρ ^ i ≤ 2 * κ * D.ρ ^ i * (1 / D.ρ) :=
      le_mul_of_one_le_right (by positivity) h1ρ
    calc 2 * κ * D.ρ ^ i ≤ 2 * κ * D.ρ ^ i * (1 / D.ρ) := this
      _ = 2 * κ / D.ρ * D.ρ ^ i := by ring
  · refine tilt_coeff_le hρ0 hκ hθ hr' (by positivity) ?_
    have : 1 ≤ 2 / D.ρ := by rw [le_div_iff₀ hρ0]; linarith
    have : κ ≤ 2 * κ / D.ρ := by
      calc κ = κ * 1 := (mul_one κ).symm
        _ ≤ κ * (2 / D.ρ) := mul_le_mul_of_nonneg_left this hκ.le
        _ = 2 * κ / D.ρ := by ring
    exact mul_le_mul_of_nonneg_right this hr'.le

omit h in
/-- The real part of the tilt estimate: PD3 (`planeDist_le_of_center`) with factor `2/ρ` and
`(a + b)² ≤ 2a² + 2b²`. -/
private lemma pd_sq_le {ρ pd pdA pdB F : ℝ} (hρ : 0 < ρ) (hpd0 : 0 ≤ pd)
    (hB0 : 0 ≤ pdB) (hF : F ≤ 2 / ρ) (htri : pd ≤ pdA + F * pdB) :
    pd ^ 2 ≤ 2 * pdA ^ 2 + 8 / ρ ^ 2 * pdB ^ 2 := by
  have htri' : pd ≤ pdA + 2 / ρ * pdB :=
    htri.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hF hB0))
  have : pd ^ 2 ≤ (pdA + 2 / ρ * pdB) ^ 2 := pow_le_pow_left₀ hpd0 htri' 2
  have e : 8 / ρ ^ 2 * pdB ^ 2 = 2 * (2 / ρ * pdB) ^ 2 := by field_simp; ring
  rw [e]
  linarith [sq_nonneg (pdA - 2 / ρ * pdB)]

omit h in
private lemma ennreal_combine {pdA pdB K θ ρ : ℝ} {X Y1 Y2 : ℝ≥0∞} (hK : 0 ≤ K) (hθ : 0 < θ)
    (hρ : 0 < ρ)
    (hA : ENNReal.ofReal (pdA ^ 2) ≤ ENNReal.ofReal (K / θ) * (X + Y2))
    (hB : ENNReal.ofReal (pdB ^ 2) ≤ ENNReal.ofReal (K / θ) * (Y2 + Y1)) :
    ENNReal.ofReal (2 * pdA ^ 2 + 8 / ρ ^ 2 * pdB ^ 2) ≤
      ENNReal.ofReal (2 * (1 + 4 / ρ ^ 2) * K / θ) * (X + (Y1 + Y2)) := by
  set a := ENNReal.ofReal (2 * (K / θ))
  set b := ENNReal.ofReal (8 / ρ ^ 2 * (K / θ))
  have hab : a + b = ENNReal.ofReal (2 * (1 + 4 / ρ ^ 2) * K / θ) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc ENNReal.ofReal (2 * pdA ^ 2 + 8 / ρ ^ 2 * pdB ^ 2)
      = ENNReal.ofReal 2 * ENNReal.ofReal (pdA ^ 2) +
          ENNReal.ofReal (8 / ρ ^ 2) * ENNReal.ofReal (pdB ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (K / θ) * (X + Y2)) +
          ENNReal.ofReal (8 / ρ ^ 2) * (ENNReal.ofReal (K / θ) * (Y2 + Y1)) := by
        gcongr
    _ = a * (X + Y2) + b * (Y2 + Y1) := by
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ (a + b) * (X + (Y1 + Y2)) := by
        have e : (a + b) * (X + (Y1 + Y2)) = (a * (X + Y2) + b * (Y2 + Y1)) + (b * X + a * Y1) :=
          by ring
        rw [e]
        exact le_self_add
    _ = _ := by rw [hab]

/-- **The tilt estimate** (Miś, proof of Proposition 4.3, with `10 r_{i+1}` for `5 r_{i+1}`). For
`y, c ∈ Good_{i+1}` with `|c − y| < 10 r_{i+1}` and `z = par y`:
`planeDist(c, r_{i+1}; V(c, κr_{i+1}), V(z, κr_i))² ≤ tiltConst θ⁻¹
  (β²(c, κr_{i+1}) + β²(z, κr_i) + β²(z, 2κr_i))`. -/
theorem EngineHyp.planeDist_sq_le {i : ℕ} (hi : D.j ≤ i) {y c : Rn n}
    (hy : y ∈ D.good (i + 1)) (hc : c ∈ D.good (i + 1)) (hcy : dist c y < 10 * D.ρ ^ (i + 1)) :
    ENNReal.ofReal (planeDist c (D.ρ ^ (i + 1)) (D.V (i + 1) c) (D.V i (D.par i y)) ^ 2) ≤
      ENNReal.ofReal (tiltConst n D.ρ κ / D.θ) *
        (jonesBetaSq D.μ c (κ * D.ρ ^ (i + 1)) +
          (jonesBetaSq D.μ (D.par i y) (κ * D.ρ ^ i) +
            jonesBetaSq D.μ (D.par i y) (2 * κ * D.ρ ^ i))) := by
  rw [h.est.V_eq, h.est.V_eq]
  obtain ⟨hz, hyz, -⟩ := h.par_spec hi hy
  set z := D.par i y
  have hρ0 := h.ρ_pos
  have hρ1 : D.ρ ≤ 1 / 100 := h.est.ρ_le
  have hr' : 0 < D.ρ ^ i := pow_pos hρ0 i
  have hr : 0 < D.ρ ^ (i + 1) := pow_pos hρ0 (i + 1)
  have hrr : D.ρ ^ (i + 1) = D.ρ * D.ρ ^ i := pow_succ' _ _
  have hcz : dist c z < D.ρ ^ i + 10 * D.ρ ^ (i + 1) := by
    have := dist_triangle c y z
    have := mem_ball.1 hyz
    linarith
  have hA := h.tilt_A hi hc hcz
  have hB := h.tilt_B hi hz
  set W := bestPlane D.μ z (2 * κ * D.ρ ^ i)
  have hPD3 := planeDist_le_of_center (x := z) (x' := c) hr' hr W (bestPlane D.μ z (κ * D.ρ ^ i))
  have hfac : max (1 + ‖z - c‖ / D.ρ ^ (i + 1)) (D.ρ ^ i / D.ρ ^ (i + 1)) ≤ 2 / D.ρ := by
    have hzc : ‖z - c‖ = dist c z := by rw [dist_comm, dist_eq_norm]
    rw [hzc]
    rw [hrr] at hcz ⊢
    refine max_le ?_ ?_
    · have key : dist c z / (D.ρ * D.ρ ^ i) + 1 ≤ 2 / D.ρ := by
        rw [div_add_one (by positivity), div_le_div_iff₀ (by positivity) hρ0]
        linarith [mul_lt_mul_of_pos_left hcz hρ0,
          mul_le_mul_of_nonneg_right hρ1 (mul_pos hρ0 hr').le]
      linarith
    · rw [div_le_div_iff₀ (by positivity) hρ0]
      linarith [mul_pos hρ0 hr']
  have htri := planeDist_triangle (x := c) hr.le (bestPlane D.μ c (κ * D.ρ ^ (i + 1))) W
    (bestPlane D.μ z (κ * D.ρ ^ i))
  have hsq := pd_sq_le hρ0 (planeDist_nonneg hr.le) (planeDist_nonneg hr'.le) hfac
    (htri.trans (add_le_add le_rfl hPD3))
  refine (ENNReal.ofReal_le_ofReal hsq).trans ?_
  have := ennreal_combine (tiltK0_pos hρ0 h.κ_pos).le h.θ_pos hρ0 hA hB
  refine this.trans (le_of_eq ?_)
  rfl

/-- **Rough bound** at a good center: `β²(z, s r_i) ≤ roughC J / θ` for
`1 ≤ s ≤ 2κ`. -/
theorem EngineHyp.beta_rough {i : ℕ} (hi : D.j ≤ i) {z : Rn n} (hz : z ∈ D.good i) {s : ℝ}
    (hs1 : 1 ≤ s) (hs : s ≤ 2 * κ) :
    jonesBetaSq D.μ z (s * D.ρ ^ i) ≤ ENNReal.ofReal (roughC n κ * J / D.θ) := by
  have hρ0 := h.ρ_pos
  have hri : 0 < D.ρ ^ i := pow_pos hρ0 i
  have hθ := h.θ_pos
  have hκ := h.est.κ_le
  have hrj : D.ρ ^ i ≤ D.ρ ^ D.j := h.est.pow_le_pow hi
  have hlow := le_measure_of_mem_good h.est hi hz
  have hlow' : ENNReal.ofReal (D.θ * (D.ρ ^ i) ^ (n - 1)) ≤ D.μ (ball z (s * D.ρ ^ i)) :=
    hlow.trans (measure_mono (ball_subset_ball (le_mul_of_one_le_left hri.le hs1)))
  have hzp := mem_ball.1 (mem_ball_of_mem_good h.est hi hz)
  have h4 : ball z (4 * (s * D.ρ ^ i)) ⊆ ball D.p (ledgerR0 * D.ρ ^ D.j) := by
    refine ball_subset_ball' ?_
    rw [ledgerR0]
    linarith [mul_le_mul_of_nonneg_right hs hri.le, mul_le_mul_of_nonneg_right hκ hri.le]
  refine (jonesBetaSq_le_rough h.one_le_n h.est.beta (by positivity) h4 (by positivity)
    hlow').trans (ENNReal.ofReal_le_ofReal ?_)
  have hJ := h.J_nonneg
  have h4s : (4 * s) ^ (n - 1) ≤ (8 * κ) ^ (n - 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have e : roughConst n * J * (4 * (s * D.ρ ^ i)) ^ (n - 1) / (D.θ * (D.ρ ^ i) ^ (n - 1)) =
      roughConst n * J * (4 * s) ^ (n - 1) / D.θ := by
    rw [show 4 * (s * D.ρ ^ i) = 4 * s * D.ρ ^ i by ring, mul_pow]
    field_simp
  rw [e, roughC]
  have := roughConst_pos n
  refine div_le_div_of_nonneg_right ?_ hθ.le
  calc roughConst n * J * (4 * s) ^ (n - 1)
      ≤ roughConst n * J * (8 * κ) ^ (n - 1) := by gcongr
    _ = roughConst n * (8 * κ) ^ (n - 1) * J := by ring

/-- The tilt estimate with the rough bound: `planeDist² ≤ 3 tiltConst roughC J / θ²`. -/
theorem EngineHyp.planeDist_sq_le_rough {i : ℕ} (hi : D.j ≤ i) {y c : Rn n}
    (hy : y ∈ D.good (i + 1)) (hc : c ∈ D.good (i + 1)) (hcy : dist c y < 10 * D.ρ ^ (i + 1)) :
    planeDist c (D.ρ ^ (i + 1)) (D.V (i + 1) c) (D.V i (D.par i y)) ^ 2 ≤
      3 * tiltConst n D.ρ κ * roughC n κ * J / D.θ ^ 2 := by
  have hθ := h.θ_pos
  have hJ := h.J_nonneg
  have hκ1 := h.est.one_le_κ
  have hz := (h.par_spec hi hy).1
  have hT := tiltConst_pos (n := n) h.ρ_pos h.κ_pos
  have hR := roughC_pos (n := n) h.κ_pos
  have hA := h.planeDist_sq_le hi hy hc hcy
  have hb1 := h.beta_rough (i := i + 1) (s := κ) (by omega) hc hκ1 (by linarith)
  have hb2 := h.beta_rough (s := κ) hi hz hκ1 (by linarith)
  have hb3 := h.beta_rough (s := 2 * κ) hi hz (by linarith) le_rfl
  have key : ENNReal.ofReal (planeDist c (D.ρ ^ (i + 1)) (D.V (i + 1) c)
      (D.V i (D.par i y)) ^ 2) ≤
      ENNReal.ofReal (3 * tiltConst n D.ρ κ * roughC n κ * J / D.θ ^ 2) := by
    refine hA.trans ?_
    set B := ENNReal.ofReal (roughC n κ * J / D.θ)
    calc _ ≤ ENNReal.ofReal (tiltConst n D.ρ κ / D.θ) * (B + (B + B)) := by gcongr
      _ = ENNReal.ofReal (tiltConst n D.ρ κ / D.θ) *
            ENNReal.ofReal (3 * (roughC n κ * J / D.θ)) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp only [B]
          rw [show (ENNReal.ofReal 3) = 3 by simp]
          ring
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

/-- **Smallness of the tilts** (from the engine smallness `J_small`): every tilt is `≤ η`. -/
theorem EngineHyp.tilt_le_small {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    D.tilt i y ≤ smallConst n D.ρ := by
  have hη := smallConst_pos h.one_le_n h.ρ_pos
  refine tilt_le hη.le fun c hc hcy => ?_
  have h1 := h.planeDist_sq_le_rough hi hy hc hcy
  have hθ := h.θ_pos
  have hT := tiltConst_pos (n := n) h.ρ_pos h.κ_pos
  have hR := roughC_pos (n := n) h.κ_pos
  have h2 : 3 * tiltConst n D.ρ κ * roughC n κ * J / D.θ ^ 2 ≤ smallConst n D.ρ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hJ := h.J_small
    unfold smallEps at hJ
    have e : smallConst n D.ρ ^ 2 / (3 * tiltConst n D.ρ κ * roughC n κ) * D.θ ^ 2 *
        (3 * tiltConst n D.ρ κ * roughC n κ) = smallConst n D.ρ ^ 2 * D.θ ^ 2 := by
      field_simp
    have := mul_le_mul_of_nonneg_right hJ (by positivity : (0 : ℝ) ≤ 3 * tiltConst n D.ρ κ *
      roughC n κ)
    linarith
  exact (pow_le_pow_iff_left₀ (planeDist_nonneg (pow_pos h.ρ_pos _).le) hη.le
    two_ne_zero).1 (h1.trans h2)

/-- The surface construction's hypotheses hold for every engine run. -/
theorem EngineHyp.surfHyp : D.SurfHyp where
  hyp := h.hyp
  two_le_n := h.two_le_n
  ρ_le := h.est.ρ_le
  unit := fun i y => by rw [h.est.V_eq]; exact norm_bestPlane_snd h.one_le_n _ _ _
  small := fun _ hi _ hy => h.tilt_le_small hi hy

end EngineHyp

/-! ### The Carleson packing of the tilts and of the excesses -/

/-- The number of `Good_{i+1}` centers `y` with `z ∈ B_{r_i}(y)`, `⌈(2/ρ + 1)ⁿ⌉` (the children of
one parent). -/
def parConst (n : ℕ) (ρ : ℝ) : ℕ := ⌈(2 / ρ + 1) ^ n⌉₊

/-- `(sup_c (f c)⁺)² ≤ Σ_c (f c)²`. -/
theorem ofReal_sup_sq_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal ((((s.sup fun c => (f c).toNNReal : ℝ≥0)) : ℝ) ^ 2) ≤
      ∑ c ∈ s, ENNReal.ofReal (f c ^ 2) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · obtain ⟨c, hc, hsup⟩ := Finset.exists_mem_eq_sup s hs fun c => (f c).toNNReal
    rw [hsup]
    refine le_trans ?_ (Finset.single_le_sum (f := fun c => ENNReal.ofReal (f c ^ 2))
      (fun _ _ => bot_le) hc)
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_total 0 (f c) with h0 | h0
    · rw [Real.coe_toNNReal _ h0]
    · rw [Real.toNNReal_of_nonpos h0]
      simp only [NNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity

section Packing

variable (h : D.EngineHyp κ Λ J)
include h

open scoped Classical in
/-- A parent has at most `parConst` children. -/
theorem EngineHyp.card_filter_par_le {i : ℕ} (hi : D.j ≤ i) (z : Rn n) :
    ((D.good (i + 1)).filter fun y => z ∈ ball y (D.ρ ^ i)).card ≤ parConst n D.ρ := by
  have hρ0 := h.ρ_pos
  have hcard := card_good_le h.est (i := i + 1) (by omega) (Finset.filter_subset _ _) (w := z)
    (R := D.ρ ^ i) (pow_pos hρ0 i).le (fun y hy => by
      rw [Finset.coe_filter] at hy
      rw [mem_closedBall, dist_comm]
      exact (mem_ball.1 hy.2).le)
  have e : 2 * D.ρ ^ i / D.ρ ^ (i + 1) = 2 / D.ρ := by
    rw [pow_succ]; field_simp
  rw [e] at hcard
  unfold parConst
  exact_mod_cast hcard.trans (Nat.le_ceil _)

open scoped Classical in
/-- At most `21ⁿ` good centers of one scale lie within `10 r` of a point. -/
theorem EngineHyp.card_filter_ten_le {i : ℕ} (hi : D.j ≤ i) (w : Rn n) :
    ((D.good i).filter fun y => dist w y < 10 * D.ρ ^ i).card ≤ 21 ^ n := by
  have := card_filter_good_le h.est hi w (s := 10) (by norm_num) (c := 21 ^ n) (by norm_num)
  simpa only [mem_ball] using this

open scoped Classical in
/-- The tilts of one scale, packed: with `a_i = r_i^k`,
`Σ_{y ∈ Good_{i+1}} a_{i+1} δ₁(y)² ≤ C_t θ⁻¹ 21ⁿ (Σ_{c ∈ Good_{i+1}} a_{i+1} β²(c, κr_{i+1}) +
parConst Σ_{z ∈ Good_i} a_i (β²(z, κr_i) + β²(z, 2κr_i)))`. -/
theorem EngineHyp.sum_tilt_sq_scale_le {i : ℕ} (hi : D.j ≤ i) :
    ∑ y ∈ D.good (i + 1), ENNReal.ofReal ((D.ρ ^ (i + 1)) ^ (n - 1)) *
        ENNReal.ofReal (D.tilt i y ^ 2) ≤
      ENNReal.ofReal (tiltConst n D.ρ κ / D.θ) * ((21 ^ n : ℕ) *
        (∑ c ∈ D.good (i + 1), ENNReal.ofReal ((D.ρ ^ (i + 1)) ^ (n - 1)) *
            jonesBetaSq D.μ c (κ * D.ρ ^ (i + 1)) +
          parConst n D.ρ * ∑ z ∈ D.good i, ENNReal.ofReal ((D.ρ ^ i) ^ (n - 1)) *
            (jonesBetaSq D.μ z (κ * D.ρ ^ i) + jonesBetaSq D.μ z (2 * κ * D.ρ ^ i)))) := by
  set a := ENNReal.ofReal ((D.ρ ^ (i + 1)) ^ (n - 1))
  set a' := ENNReal.ofReal ((D.ρ ^ i) ^ (n - 1))
  set C := ENNReal.ofReal (tiltConst n D.ρ κ / D.θ)
  set B : Rn n → ℝ≥0∞ := fun c => jonesBetaSq D.μ c (κ * D.ρ ^ (i + 1))
  set G : Rn n → ℝ≥0∞ := fun z =>
    jonesBetaSq D.μ z (κ * D.ρ ^ i) + jonesBetaSq D.μ z (2 * κ * D.ρ ^ i)
  set F : Rn n → Finset (Rn n) := fun y =>
    (D.good (i + 1)).filter fun c => dist c y < 10 * D.ρ ^ (i + 1)
  have hρ0 := h.ρ_pos
  have haa : a ≤ a' := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (pow_pos hρ0 _).le
    (h.est.pow_le_pow (Nat.le_succ i)) _)
  -- one center
  have h1 : ∀ y ∈ D.good (i + 1), a * ENNReal.ofReal (D.tilt i y ^ 2) ≤
      C * (∑ c ∈ F y, a * B c + (F y).card * (a' * G (D.par i y))) := by
    intro y hy
    have hsup := ofReal_sup_sq_le (F y) fun c =>
      planeDist c (D.ρ ^ (i + 1)) (D.V (i + 1) c) (D.V i (D.par i y))
    calc a * ENNReal.ofReal (D.tilt i y ^ 2)
        ≤ a * ∑ c ∈ F y, ENNReal.ofReal
            (planeDist c (D.ρ ^ (i + 1)) (D.V (i + 1) c) (D.V i (D.par i y)) ^ 2) := by
          gcongr
          exact hsup
      _ ≤ a * ∑ c ∈ F y, C * (B c + G (D.par i y)) := by
          gcongr with c hc
          obtain ⟨hc1, hc2⟩ := Finset.mem_filter.1 hc
          exact h.planeDist_sq_le hi hy hc1 hc2
      _ = C * (∑ c ∈ F y, a * B c + ∑ c ∈ F y, a * G (D.par i y)) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          ring
      _ ≤ C * (∑ c ∈ F y, a * B c + (F y).card * (a' * G (D.par i y))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
  -- the two counting arguments
  have h2 : ∑ y ∈ D.good (i + 1), ∑ c ∈ F y, a * B c ≤
      (21 ^ n : ℕ) * ∑ c ∈ D.good (i + 1), a * B c :=
    sum_sum_filter_le (D.good (i + 1)) (D.good (i + 1)) (fun y c => dist c y < 10 * D.ρ ^ (i + 1))
      (fun c => a * B c) (21 ^ n) fun c _ => by
        have := h.card_filter_ten_le (i := i + 1) (by omega) c
        exact this
  have h3 : ∑ y ∈ D.good (i + 1), ((F y).card : ℝ≥0∞) * (a' * G (D.par i y)) ≤
      (21 ^ n : ℕ) * (parConst n D.ρ * ∑ z ∈ D.good i, a' * G z) := by
    calc ∑ y ∈ D.good (i + 1), ((F y).card : ℝ≥0∞) * (a' * G (D.par i y))
        ≤ ∑ y ∈ D.good (i + 1), ((21 ^ n : ℕ) : ℝ≥0∞) * (a' * G (D.par i y)) := by
          gcongr with y hy
          have := h.card_filter_ten_le (i := i + 1) (by omega) y
          have e : F y = (D.good (i + 1)).filter fun c => dist y c < 10 * D.ρ ^ (i + 1) := by
            simp only [F, dist_comm]
          rw [e]
          exact_mod_cast this
      _ = (21 ^ n : ℕ) * ∑ y ∈ D.good (i + 1), a' * G (D.par i y) := by rw [Finset.mul_sum]
      _ ≤ _ := by
          gcongr
          refine sum_comp_le (D.good (i + 1)) (D.good i) (fun y z => z ∈ ball y (D.ρ ^ i))
            (fun z => a' * G z) (D.par i) (fun y hy => ?_) (parConst n D.ρ)
            fun z _ => h.card_filter_par_le hi z
          obtain ⟨hz, hyz, -⟩ := h.par_spec hi hy
          exact ⟨hz, mem_ball_comm.1 hyz⟩
  calc ∑ y ∈ D.good (i + 1), a * ENNReal.ofReal (D.tilt i y ^ 2)
      ≤ ∑ y ∈ D.good (i + 1), C * (∑ c ∈ F y, a * B c + (F y).card * (a' * G (D.par i y))) :=
        Finset.sum_le_sum h1
    _ = C * (∑ y ∈ D.good (i + 1), ∑ c ∈ F y, a * B c +
          ∑ y ∈ D.good (i + 1), ((F y).card : ℝ≥0∞) * (a' * G (D.par i y))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ C * ((21 ^ n : ℕ) * ∑ c ∈ D.good (i + 1), a * B c +
          (21 ^ n : ℕ) * (parConst n D.ρ * ∑ z ∈ D.good i, a' * G z)) := by
        gcongr
    _ = _ := by ring

/-- The tilts of all scales `j ≤ i < N`, packed (Miś §4, the sums leading to (4.1)):
`Σ_i Σ_{y ∈ Good_{i+1}} r_{i+1}^k δ₁(y)² ≤ C_t θ⁻¹ 21ⁿ (1 + 2 parConst) C_pack J r_j^k / θ`. -/
theorem EngineHyp.sum_tilt_sq_le (N : ℕ) :
    ∑ i ∈ Finset.Ico D.j N, ∑ y ∈ D.good (i + 1), ENNReal.ofReal ((D.ρ ^ (i + 1)) ^ (n - 1)) *
        ENNReal.ofReal (D.tilt i y ^ 2) ≤
      ENNReal.ofReal (tiltConst n D.ρ κ / D.θ) * ((21 ^ n : ℕ) * ((1 + 2 * parConst n D.ρ : ℕ) *
        ENNReal.ofReal (packConst n D.ρ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ))) := by
  set PB := ENNReal.ofReal (packConst n D.ρ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ)
  set C := ENNReal.ofReal (tiltConst n D.ρ κ / D.θ)
  set Fb : ℝ → ℕ → ℝ≥0∞ := fun s i =>
    ∑ c ∈ D.good i, ENNReal.ofReal ((D.ρ ^ i) ^ (n - 1)) * jonesBetaSq D.μ c (s * D.ρ ^ i)
  have hκ1 := h.est.one_le_κ
  have hκ2 := h.est.κ_le
  have hP : ∀ s, 1 ≤ s → s ≤ 3 → ∑ i ∈ Finset.Ico D.j N, Fb s i ≤ PB := fun s hs1 hs3 =>
    (Finset.sum_le_sum_of_subset Finset.Ico_subset_Icc_self).trans
      (sum_sum_beta_le h.est hs1 hs3 N)
  have hP1 : ∑ i ∈ Finset.Ico D.j N, Fb κ (i + 1) ≤ PB := by
    rw [Finset.sum_Ico_add' (fun i => Fb κ i) D.j N 1]
    refine (Finset.sum_le_sum_of_subset ?_).trans (sum_sum_beta_le h.est hκ1 (by linarith) N)
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_Icc]
    omega
  calc _ ≤ ∑ i ∈ Finset.Ico D.j N, C * ((21 ^ n : ℕ) *
          (Fb κ (i + 1) + parConst n D.ρ * (Fb κ i + Fb (2 * κ) i))) := by
        refine Finset.sum_le_sum fun i hi => (h.sum_tilt_sq_scale_le (Finset.mem_Ico.1 hi).1).trans
          (le_of_eq ?_)
        simp only [Fb, mul_add, Finset.sum_add_distrib]
        rfl
    _ = C * ((21 ^ n : ℕ) * (∑ i ∈ Finset.Ico D.j N, Fb κ (i + 1) + parConst n D.ρ *
          (∑ i ∈ Finset.Ico D.j N, Fb κ i + ∑ i ∈ Finset.Ico D.j N, Fb (2 * κ) i))) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_add_distrib]
    _ ≤ C * ((21 ^ n : ℕ) * (PB + parConst n D.ρ * (PB + PB))) :=
        mul_le_mul_right (mul_le_mul_right (add_le_add hP1 (mul_le_mul_right
          (add_le_add (hP κ hκ1 (by linarith)) (hP (2 * κ) (by linarith) (by linarith))) _)) _) _
    _ = _ := by push_cast; ring

end Packing

/-- A sequence vanishing at `j`: `Σ_{j ≤ i < N} f i ≤ Σ_{j ≤ i < N} f (i + 1)`. -/
theorem sum_Ico_le_sum_Ico_succ {f : ℕ → ℝ≥0∞} {j N : ℕ} (hf : f j = 0) :
    ∑ i ∈ Finset.Ico j N, f i ≤ ∑ i ∈ Finset.Ico j N, f (i + 1) := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  cases N - j with
  | zero => simp
  | succ L =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ, add_zero, hf, add_zero]
    exact le_add_right le_rfl

/-- `δ₁²` of the good centers of scale `i`, weighted by `r_i^k`. -/
def d1Sum (D : CoverData n) (i : ℕ) : ℝ≥0∞ :=
  ∑ z ∈ D.good i, ENNReal.ofReal ((D.ρ ^ i) ^ (n - 1)) * ENNReal.ofReal (D.d1 i z ^ 2)

theorem d1Sum_top : D.d1Sum D.j = 0 := by
  unfold d1Sum
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [d1_of_le le_rfl]
  simp

section Packing

variable (h : D.EngineHyp κ Λ J)
include h

/-- The `δ₁` sums of all scales `j < i ≤ N` are the packed tilts. -/
theorem EngineHyp.sum_d1Sum_succ_le (N : ℕ) :
    ∑ i ∈ Finset.Ico D.j N, D.d1Sum (i + 1) ≤
      ENNReal.ofReal (tiltConst n D.ρ κ / D.θ) * ((21 ^ n : ℕ) * ((1 + 2 * parConst n D.ρ : ℕ) *
        ENNReal.ofReal (packConst n D.ρ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ))) := by
  refine le_trans (le_of_eq ?_) (h.sum_tilt_sq_le N)
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun y _ => ?_
  rw [d1_succ (Finset.mem_Ico.1 hi).1]

open scoped Classical in
/-- **Carleson packing of the bi-Lipschitz excesses**:
`Σ_{j ≤ i < N} Σ_{y ∈ Good_{i+1}} ε(y) r_{i+1}^k ≤ C_sq²((6C_sq/ρ)² parConst + 1)
Σ_{j ≤ i < N} d1Sum (i+1)`. -/
theorem EngineHyp.sum_eps_le (N : ℕ) :
    ∑ i ∈ Finset.Ico D.j N, ∑ y ∈ D.good (i + 1),
        ENNReal.ofReal (D.eps i y) * ENNReal.ofReal ((D.ρ ^ (i + 1)) ^ (n - 1)) ≤
      ENNReal.ofReal (C_sq n ^ 2 * ((6 * C_sq n / D.ρ) ^ 2 * parConst n D.ρ + 1)) *
        ∑ i ∈ Finset.Ico D.j N, D.d1Sum (i + 1) := by
  have hρ0 := h.ρ_pos
  set A := C_sq n ^ 2 * (6 * C_sq n / D.ρ) ^ 2
  set B := C_sq n ^ 2
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := by positivity
  -- one center
  have h1 : ∀ i, D.j ≤ i → ∀ y ∈ D.good (i + 1),
      ENNReal.ofReal (D.eps i y) * ENNReal.ofReal ((D.ρ ^ (i + 1)) ^ (n - 1)) ≤
        ENNReal.ofReal A * (ENNReal.ofReal ((D.ρ ^ i) ^ (n - 1)) *
            ENNReal.ofReal (D.d1 i (D.par i y) ^ 2)) +
          ENNReal.ofReal B * (ENNReal.ofReal ((D.ρ ^ (i + 1)) ^ (n - 1)) *
            ENNReal.ofReal (D.d1 (i + 1) y ^ 2)) := by
    intro i hi y hy
    have hr : (D.ρ ^ (i + 1)) ^ (n - 1) ≤ (D.ρ ^ i) ^ (n - 1) :=
      pow_le_pow_left₀ (pow_pos hρ0 _).le (h.est.pow_le_pow (Nat.le_succ i)) _
    rw [← ENNReal.ofReal_mul (eps_nonneg _ _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : D.eps i y * (D.ρ ^ (i + 1)) ^ (n - 1) =
        A * (D.d1 i (D.par i y) ^ 2 * (D.ρ ^ (i + 1)) ^ (n - 1)) +
          B * ((D.ρ ^ (i + 1)) ^ (n - 1) * D.d1 (i + 1) y ^ 2) := by
      simp only [eps, delta0, A, B]
      ring
    rw [e]
    have : D.d1 i (D.par i y) ^ 2 * (D.ρ ^ (i + 1)) ^ (n - 1) ≤
        (D.ρ ^ i) ^ (n - 1) * D.d1 i (D.par i y) ^ 2 := by
      rw [mul_comm]; gcongr
    gcongr
  -- the parents
  have h2 : ∀ i, D.j ≤ i → ∑ y ∈ D.good (i + 1), ENNReal.ofReal ((D.ρ ^ i) ^ (n - 1)) *
      ENNReal.ofReal (D.d1 i (D.par i y) ^ 2) ≤ parConst n D.ρ * D.d1Sum i := by
    intro i hi
    refine sum_comp_le (D.good (i + 1)) (D.good i) (fun y z => z ∈ ball y (D.ρ ^ i))
      (fun z => ENNReal.ofReal ((D.ρ ^ i) ^ (n - 1)) * ENNReal.ofReal (D.d1 i z ^ 2)) (D.par i)
      (fun y hy => ?_) (parConst n D.ρ) fun z _ => h.card_filter_par_le hi z
    obtain ⟨hz, hyz, -⟩ := h.par_spec hi hy
    exact ⟨hz, mem_ball_comm.1 hyz⟩
  have hshift := sum_Ico_le_sum_Ico_succ (f := D.d1Sum) (N := N) d1Sum_top
  calc _ ≤ ∑ i ∈ Finset.Ico D.j N, (ENNReal.ofReal A * (parConst n D.ρ * D.d1Sum i) +
          ENNReal.ofReal B * D.d1Sum (i + 1)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := (Finset.mem_Ico.1 hi).1
        refine (Finset.sum_le_sum (h1 i hi')).trans ?_
        rw [Finset.sum_add_distrib]
        refine add_le_add ?_ (le_of_eq ?_)
        · rw [← Finset.mul_sum]
          exact mul_le_mul_right (h2 i hi') _
        · rw [d1Sum, Finset.mul_sum]
    _ = ENNReal.ofReal A * parConst n D.ρ * ∑ i ∈ Finset.Ico D.j N, D.d1Sum i +
          ENNReal.ofReal B * ∑ i ∈ Finset.Ico D.j N, D.d1Sum (i + 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          mul_assoc]
    _ ≤ ENNReal.ofReal A * parConst n D.ρ * ∑ i ∈ Finset.Ico D.j N, D.d1Sum (i + 1) +
          ENNReal.ofReal B * ∑ i ∈ Finset.Ico D.j N, D.d1Sum (i + 1) := by gcongr
    _ = _ := by
        rw [← add_mul]
        congr 1
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hA,
          ← ENNReal.ofReal_add (by positivity) hB]
        congr 1
        simp only [A, B]
        ring

end Packing

/-! ### (4.1), (4.2) and the mass bound -/

/-- The constant of (4.1): `C_A = 2k ω_k 10^k · C_sq²((6C_sq/ρ)² parConst + 1) · C_t ·
21ⁿ (1 + 2 parConst) · C_pack`, so that `ℋ^k(T_N ∩ W_N) ≤ ω_k((1+ρ)r_j)^k + C_A J r_j^k / θ²`. -/
def areaConst (n : ℕ) (ρ κ : ℝ) : ℝ :=
  2 * ((n - 1 : ℕ) : ℝ) * unitBallVolume (n - 1) * 10 ^ (n - 1) *
    (C_sq n ^ 2 * ((6 * C_sq n / ρ) ^ 2 * parConst n ρ + 1)) * tiltConst n ρ κ *
      (21 ^ n * (1 + 2 * parConst n ρ)) * packConst n ρ

theorem areaConst_nonneg {ρ κ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hκ : 0 < κ) :
    0 ≤ areaConst n ρ κ := by
  have := unitBallVolume_pos (n - 1)
  have := tiltConst_pos (n := n) hρ0 hκ
  have := packConst_nonneg (n := n) hρ0 hρ1
  unfold areaConst
  positivity

open scoped Classical in
/-- The bad and final leaves of the scales `j < l ≤ N` (the first part of `leaves N`). -/
def badLeaves (D : CoverData n) (N : ℕ) : Finset (ℕ × Rn n) :=
  (Finset.Ioc D.j N).biUnion fun l => (D.bad l ∪ D.fin l).image fun y => (l, y)

theorem mem_badLeaves {N : ℕ} {q : ℕ × Rn n} :
    q ∈ D.badLeaves N ↔ D.j < q.1 ∧ q.1 ≤ N ∧ q.2 ∈ D.bad q.1 ∪ D.fin q.1 := by
  classical
  obtain ⟨l, y⟩ := q
  simp only [badLeaves, Finset.mem_biUnion, Finset.mem_Ioc, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨l', hl', y', hy', rfl, rfl⟩
    exact ⟨hl'.1, hl'.2, hy'⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨l, ⟨h1, h2⟩, y, h3, rfl, rfl⟩

theorem badLeaves_subset_leaves (N : ℕ) : D.badLeaves N ⊆ D.leaves N := fun _ hq =>
  mem_leaves.2 (Or.inl (mem_badLeaves.1 hq))

/-- **Claim 4.2 (a)** with the bad and final leaves: `P ⊆ ⋃_{Good_N} B_{r_N}(y) ∪
⋃_{badLeaves N} B_{r_l}(y) ∪ ⋃_{j ≤ l ≤ N} E_l`. -/
theorem subset_cover_badLeaves (hD : D.Hyp) {N : ℕ} (hN : D.j ≤ N) :
    D.P ⊆ (⋃ y ∈ D.good N, ball y (D.ρ ^ N)) ∪ (⋃ q ∈ D.badLeaves N, ball q.2 (D.ρ ^ q.1)) ∪
      ⋃ l ∈ Finset.Icc D.j N, D.excessUnion l (D.good l) := by
  intro x hx
  rcases subset_cover hD hN hx with h | h
  · exact Or.inl (Or.inl h)
  · rw [rem_eq hN] at h
    rcases h with h | h
    · obtain ⟨l, hl, h⟩ := mem_iUnion₂.1 h
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 h
      have hl' := Finset.mem_Ioc.1 hl
      exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨(l, y), mem_badLeaves.2 ⟨hl'.1, hl'.2, hy⟩, hxy⟩))
    · exact Or.inr h

section Mass

variable (h : D.EngineHyp κ Λ J)
include h

/-- **(4.1)** (Miś (4.1) at `q = 2`, localized to the windows `W_N`), for every `N ≥ j`:
`ℋ^k(T_N ∩ W_N) ≤ ω_k((1+ρ) r_j)^k + C_A J r_j^k / θ²`. -/
theorem EngineHyp.hausdorffN_surf_le' {N : ℕ} (hN : D.j ≤ N) :
    hausdorffN n (n - 1) (D.surf N ∩ ball D.p (D.window N)) ≤
      ENNReal.ofReal (unitBallVolume (n - 1) * ((1 + D.ρ) * D.ρ ^ D.j) ^ (n - 1)) +
        ENNReal.ofReal (areaConst n D.ρ κ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ ^ 2) := by
  refine (hausdorffN_surf_le h.surfHyp hN).trans (add_le_add le_rfl ?_)
  have hρ0 := h.ρ_pos
  have hθ := h.θ_pos
  have hJ := h.J_nonneg
  have hω := unitBallVolume_pos (n - 1)
  set c := 2 * ((n - 1 : ℕ) : ℝ) * unitBallVolume (n - 1) * 10 ^ (n - 1) with hc
  have hc0 : 0 ≤ c := by positivity
  have hterm : ∀ i y, ENNReal.ofReal (2 * ((n - 1 : ℕ) : ℝ) * D.eps i y) *
      ENNReal.ofReal (unitBallVolume (n - 1) * (10 * D.ρ ^ (i + 1)) ^ (n - 1)) =
      ENNReal.ofReal c *
        (ENNReal.ofReal (D.eps i y) * ENNReal.ofReal ((D.ρ ^ (i + 1)) ^ (n - 1))) := by
    intro i y
    have := eps_nonneg (D := D) i y
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, hc]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  set E := C_sq n ^ 2 * ((6 * C_sq n / D.ρ) ^ 2 * parConst n D.ρ + 1)
  have hE : 0 ≤ E := by positivity
  have hT := tiltConst_pos (n := n) hρ0 h.κ_pos
  have hP := packConst_nonneg (n := n) hρ0 h.est.ρ_le_one
  calc ENNReal.ofReal c * ∑ i ∈ Finset.Ico D.j N, ∑ y ∈ D.good (i + 1),
        ENNReal.ofReal (D.eps i y) * ENNReal.ofReal ((D.ρ ^ (i + 1)) ^ (n - 1))
      ≤ ENNReal.ofReal c * (ENNReal.ofReal E * (ENNReal.ofReal (tiltConst n D.ρ κ / D.θ) *
          ((21 ^ n : ℕ) * ((1 + 2 * parConst n D.ρ : ℕ) *
            ENNReal.ofReal (packConst n D.ρ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ))))) := by
        gcongr
        exact (h.sum_eps_le N).trans (mul_le_mul_right (h.sum_d1Sum_succ_le N) _)
    _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [areaConst, hc, E]
        push_cast
        ring

/-- **(4.2)** in mass form (Miś (4.2), with the corrected constant `C₁`): a bad or final ball
`B_{r_l}(y)`, `j < l ≤ N`, has `μ(B_{r_l}(y)) ≤ θ C₁ ℋ^k(T_N ∩ B_{r_l/2}(y))`, `C₁ = 2·15^k/ω_k`. -/
theorem EngineHyp.measure_ball_leaf_le {l N : ℕ} (hl : D.j < l) (hlN : l ≤ N) {y : Rn n}
    (hy : y ∈ D.bad l ∪ D.fin l) :
    D.μ (ball y (D.ρ ^ l)) ≤
      ENNReal.ofReal (D.θ * ledgerC1 n) *
        hausdorffN n (n - 1) (D.surf N ∩ ball y (D.ρ ^ l / 2)) := by
  have hmass : D.μ (ball y (D.ρ ^ l)) ≤ ENNReal.ofReal (D.θ * (D.ρ ^ l) ^ (n - 1)) := by
    rcases Finset.mem_union.1 hy with hb | hf
    · obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
      exact (measure_lt_of_mem_bad_succ (by omega) hb).le
    · exact h.fin_le l hl y hf
  refine hmass.trans ?_
  have h42 := le_hausdorffN_surf_leaf h.surfHyp hl hlN hy
  have hω := unitBallVolume_pos (n - 1)
  have hθ := h.θ_pos
  have hr := pow_pos h.ρ_pos l
  calc ENNReal.ofReal (D.θ * (D.ρ ^ l) ^ (n - 1))
      = ENNReal.ofReal (D.θ * 15 ^ (n - 1) / unitBallVolume (n - 1)) *
          ENNReal.ofReal (unitBallVolume (n - 1) * (D.ρ ^ l / 15) ^ (n - 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [div_pow]
        field_simp
    _ ≤ ENNReal.ofReal (D.θ * 15 ^ (n - 1) / unitBallVolume (n - 1)) *
          (2 * hausdorffN n (n - 1) (D.surf N ∩ ball y (D.ρ ^ l / 2))) := by gcongr
    _ = _ := by
        rw [← mul_assoc]
        congr 1
        rw [show D.θ * ledgerC1 n = D.θ * 15 ^ (n - 1) / unitBallVolume (n - 1) * 2 by
          unfold ledgerC1; ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]

/-- **The mass bound of one engine run** (Miś §4, "Derivation of the bound"), for every
`N ≥ j`: `μ(P) ≤ θ C₁ ℋ^k(T_N ∩ W_N) + μ(⋃_{j ≤ l ≤ N} E_l) + μ(⋃_{y ∈ Good_N} B_{r_N}(y))`. -/
theorem EngineHyp.engine_mass {N : ℕ} (hN : D.j ≤ N) :
    D.μ D.P ≤ ENNReal.ofReal (D.θ * ledgerC1 n) *
        hausdorffN n (n - 1) (D.surf N ∩ ball D.p (D.window N)) +
      D.μ (⋃ l ∈ Finset.Icc D.j N, D.excessUnion l (D.good l)) +
      D.μ (⋃ y ∈ D.good N, ball y (D.ρ ^ N)) := by
  have hρ0 := h.ρ_pos
  set ν := (hausdorffN n (n - 1)).restrict (D.surf N)
  set L := D.badLeaves N
  have hB : D.μ (⋃ q ∈ L, ball q.2 (D.ρ ^ q.1)) ≤ ENNReal.ofReal (D.θ * ledgerC1 n) *
      hausdorffN n (n - 1) (D.surf N ∩ ball D.p (D.window N)) := by
    have hdisj : (L : Set (ℕ × Rn n)).PairwiseDisjoint fun q => ball q.2 (D.ρ ^ q.1 / 2) :=
      (pairwiseDisjoint_halfBalls h.hyp hN).subset (Finset.coe_subset.2 (badLeaves_subset_leaves N))
    have hsub : (⋃ q ∈ L, ball q.2 (D.ρ ^ q.1 / 2)) ⊆ ball D.p (D.window N) := by
      refine iUnion₂_subset fun q hq => ?_
      obtain ⟨hl, hlN, hy⟩ := mem_badLeaves.1 hq
      obtain ⟨i, hi⟩ : ∃ i, q.1 = i + 1 := ⟨q.1 - 1, by omega⟩
      have hyp : q.2 ∈ ball D.p (D.ρ ^ D.j) := by
        rw [hi] at hy
        refine mem_ball_top_of_mem_succ h.hyp (i := i) (by omega) ?_
        rw [Finset.union_assoc]
        exact Finset.mem_union_right _ hy
      have h1 : D.ρ ^ q.1 ≤ D.ρ * D.ρ ^ D.j := by
        rw [← pow_succ']
        exact h.est.pow_le_pow (by omega)
      have h2 := le_window h.surfHyp N
      refine ball_subset_ball' ?_
      have := mem_ball.1 hyp
      linarith
    calc D.μ (⋃ q ∈ L, ball q.2 (D.ρ ^ q.1))
        ≤ ∑ q ∈ L, D.μ (ball q.2 (D.ρ ^ q.1)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ q ∈ L, ENNReal.ofReal (D.θ * ledgerC1 n) * ν (ball q.2 (D.ρ ^ q.1 / 2)) := by
          refine Finset.sum_le_sum fun q hq => ?_
          obtain ⟨hl, hlN, hy⟩ := mem_badLeaves.1 hq
          rw [Measure.restrict_apply measurableSet_ball, inter_comm]
          exact h.measure_ball_leaf_le hl hlN hy
      _ = ENNReal.ofReal (D.θ * ledgerC1 n) * ν (⋃ q ∈ L, ball q.2 (D.ρ ^ q.1 / 2)) := by
          rw [← Finset.mul_sum, measure_biUnion_finset hdisj fun _ _ => measurableSet_ball]
      _ ≤ ENNReal.ofReal (D.θ * ledgerC1 n) * ν (ball D.p (D.window N)) := by
          gcongr
      _ = _ := by rw [Measure.restrict_apply measurableSet_ball, inter_comm]
  calc D.μ D.P
      ≤ D.μ ((⋃ y ∈ D.good N, ball y (D.ρ ^ N)) ∪ (⋃ q ∈ L, ball q.2 (D.ρ ^ q.1)) ∪
          ⋃ l ∈ Finset.Icc D.j N, D.excessUnion l (D.good l)) :=
        measure_mono (subset_cover_badLeaves h.hyp hN)
    _ ≤ D.μ (⋃ y ∈ D.good N, ball y (D.ρ ^ N)) + D.μ (⋃ q ∈ L, ball q.2 (D.ρ ^ q.1)) +
          D.μ (⋃ l ∈ Finset.Icc D.j N, D.excessUnion l (D.good l)) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := by
        rw [add_comm (D.μ (⋃ y ∈ D.good N, ball y (D.ρ ^ N))), add_assoc, add_assoc]
        refine add_le_add hB ?_
        rw [add_comm]

end Mass

end CoverData

end GMTFoundations.DiscreteReifenberg
