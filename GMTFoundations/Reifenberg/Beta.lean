/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.GMT
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# β-numbers: invariance, comparison and discretization

The calculus of the squared Jones number `jonesBetaSq μ x r` used by the discrete and the
rectifiable Reifenberg theorems. The β-numbers go back to P. W. Jones, *Rectifiable sets and the
traveling salesman problem*, Invent. Math. 102 (1990), 1–15; we use the `L²` version of
M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018);
arXiv:1612.02461 (cited as Miś; numbering of arXiv v2), and of A. Naber, D. Valtorta,
*Rectifiable-Reifenberg and the regularity of stationary and minimizing harmonic maps*, Ann. of
Math. 185 (2017), 131–227; arXiv:1504.02043 (cited as NV).

Throughout, the approximating planes are hyperplanes (`k = n − 1`), represented as pairs
`(p, ν)` with `‖ν‖ = 1`. Everything is `ℝ≥0∞`-valued, balls are open, and `μ` is an arbitrary
measure unless stated otherwise.

## Main definitions

* `planeBetaSq μ x r P`: the quantity whose infimum over unit planes `P = (p, ν)` is
  `jonesBetaSq μ x r`.
* `deltaSq μ x r = r^{-(n-1)} ∫_{B_r(x)} β²(y, r) dμ(y)` (Miś (3.2), `q = 2`).

## Main statements

* Invariance: `jonesBetaSq_mono_measure`, `jonesBetaSq_restrict_of_subset`,
  `jonesBetaSq_restrict_ball`, `jonesBetaSq_smul_map` (translation and dilation; the scale
  invariance noted after (1.2) in Miś §3 and in NV Remark 3.3).
* Comparisons: `jonesBetaSq_le_of_ball_subset` (`β²(x,r) ≤ (R/r)^{n+1} β²(y,R)` when
  `B_r(x) ⊆ B_R(y)`), `jonesBetaSq_le_two_pow_mul` (Miś (3.1)), `measure_mul_jonesBetaSq_le` and
  `jonesBetaSq_le_average` (averaged form), `jonesBetaSq_le_deltaSq` (Miś (3.3)),
  `deltaSq_le_of_ball_subset` (monotonicity of `δ²`).
* Discretization (Miś Remark 3.1 with exact ranges of scales), labelled (3a)–(3c) here and in
  later files: (3a) `sum_beta_le_integral` (sum ≤ integral), (3b) `integral_le_sum_beta`
  (integral ≤ sum), (3c) `beta_le_integral_window` (the single-scale window), and the
  combination `tsum_beta_le_integral_two_mul` of (3a) and (3c) used in the Carleson packing
  estimates of the discrete Reifenberg theorem.

## Remarks on the sources

* Miś (3.3) is printed with `=`; since `δ²(x, 2r)` integrates over `B_{2r}(x) ⊋ B_r(x)`, the
  correct relation is `≤`, with constant `4^n / τ` for `k = n − 1`, `q = 2`
  (`jonesBetaSq_le_deltaSq`).
* Miś Remark 3.1 compares `J_q(x, r)` with `Σ_{r_α ≤ 2r} β²(x, r_α)`. The proof actually bounds
  `∫_0^r` by the sum over `ρ^α < r/ρ` and the sum over `ρ^α ≤ ρr` by `∫_0^r`; the range `2r` is
  right only for `ρ ≥ 1/2`, and the constants depend on `n` as well as on ρ
  (`ρ^{-(n+1)}`, `log ρ⁻¹`). We prove the estimates with these exact ranges and constants.

## References

* [Miś] M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43
  (2018); arXiv:1612.02461, §3: (3.1)–(3.4), Remark 3.1.
* [NV] A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and
  minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227, Remarks 3.3–3.5.
* [Jones] P. W. Jones, *Rectifiable sets and the traveling salesman problem*, Invent. Math. 102
  (1990), 1–15.
-/

public noncomputable section

namespace GMTFoundations

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace Function

variable {n : ℕ}

/-! ### The plane functional -/

/-- The normalized squared distance of `μ⌊B_r(x)` from the plane `P = (p, ν)`,
`r^{-(n-1)} ∫_{B_r(x)} ⟪y − p, ν⟫² / r² dμ(y)`. Its infimum over unit normals is `jonesBetaSq`
(`jonesBetaSq_eq_iInf`). -/
@[expose] def planeBetaSq (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) (P : Rn n × Rn n) : ℝ≥0∞ :=
  (∫⁻ y in ball x r, ENNReal.ofReal (⟪y - P.1, P.2⟫ ^ 2 / r ^ 2) ∂μ) / ENNReal.ofReal (r ^ (n - 1))

theorem jonesBetaSq_eq_iInf (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) :
    jonesBetaSq μ x r = ⨅ P : {P : Rn n × Rn n // ‖P.2‖ = 1}, planeBetaSq μ x r P := by
  simp only [jonesBetaSq, planeBetaSq, iInf_subtype, iInf_prod]

theorem jonesBetaSq_le_planeBetaSq {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} {P : Rn n × Rn n}
    (hP : ‖P.2‖ = 1) : jonesBetaSq μ x r ≤ planeBetaSq μ x r P := by
  rw [jonesBetaSq_eq_iInf]
  exact iInf_le_of_le ⟨P, hP⟩ le_rfl

theorem le_jonesBetaSq {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} {c : ℝ≥0∞}
    (h : ∀ P : Rn n × Rn n, ‖P.2‖ = 1 → c ≤ planeBetaSq μ x r P) : c ≤ jonesBetaSq μ x r := by
  rw [jonesBetaSq_eq_iInf]
  exact le_iInf fun P => h P.1 P.2

/-- For `r > 0` (and `n ≥ 1`), `planeBetaSq μ x r P = r^{-(n+1)} ∫_{B_r(x)} ⟪y − p, ν⟫² dμ`. -/
theorem planeBetaSq_eq (hn : 1 ≤ n) {r : ℝ} (hr : 0 < r) (μ : Measure (Rn n)) (x : Rn n)
    (P : Rn n × Rn n) :
    planeBetaSq μ x r P = ENNReal.ofReal ((r ^ (n + 1))⁻¹) *
      ∫⁻ y in ball x r, ENNReal.ofReal (⟪y - P.1, P.2⟫ ^ 2) ∂μ := by
  have h1 : ∀ y : Rn n, ENNReal.ofReal (⟪y - P.1, P.2⟫ ^ 2 / r ^ 2) =
      ENNReal.ofReal ((r ^ 2)⁻¹) * ENNReal.ofReal (⟪y - P.1, P.2⟫ ^ 2) := by
    intro y
    rw [← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
  simp_rw [planeBetaSq, h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, div_eq_mul_inv,
    ← ENNReal.ofReal_inv_of_pos (by positivity), mul_comm, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← mul_inv, ← pow_add]
  congr 4
  omega

/-! ### Monotonicity, restriction, translation and dilation -/

theorem planeBetaSq_mono_measure {μ μ' : Measure (Rn n)} (h : μ ≤ μ') (x : Rn n) (r : ℝ)
    (P : Rn n × Rn n) : planeBetaSq μ x r P ≤ planeBetaSq μ' x r P :=
  ENNReal.div_le_div_right (lintegral_mono' (Measure.restrict_mono subset_rfl h) le_rfl) _

/-- `jonesBetaSq` is monotone in the measure (NV Remark 3.4). -/
theorem jonesBetaSq_mono_measure {μ μ' : Measure (Rn n)} (h : μ ≤ μ') (x : Rn n) (r : ℝ) :
    jonesBetaSq μ x r ≤ jonesBetaSq μ' x r := by
  simp only [jonesBetaSq_eq_iInf]
  exact iInf_mono fun P => planeBetaSq_mono_measure h x r P

theorem planeBetaSq_restrict_of_subset {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} {A : Set (Rn n)}
    (h : ball x r ⊆ A) (P : Rn n × Rn n) :
    planeBetaSq (μ.restrict A) x r P = planeBetaSq μ x r P := by
  simp only [planeBetaSq, Measure.restrict_restrict measurableSet_ball, inter_eq_left.2 h]

/-- Restricting `μ` to a set containing `B_r(x)` does not change `β(x, r)`. -/
theorem jonesBetaSq_restrict_of_subset {μ : Measure (Rn n)} {x : Rn n} {r : ℝ} {A : Set (Rn n)}
    (h : ball x r ⊆ A) : jonesBetaSq (μ.restrict A) x r = jonesBetaSq μ x r := by
  simp only [jonesBetaSq_eq_iInf, planeBetaSq_restrict_of_subset h]

/-- Restricting `μ` to `B_r(x)` does not change `β(x, r)`. -/
theorem jonesBetaSq_restrict_ball (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) :
    jonesBetaSq (μ.restrict (ball x r)) x r = jonesBetaSq μ x r :=
  jonesBetaSq_restrict_of_subset subset_rfl

theorem planeBetaSq_smul_map {a : ℝ} (ha : 0 < a) (μ : Measure (Rn n)) (x₀ z : Rn n) (r : ℝ)
    (P : Rn n × Rn n) :
    planeBetaSq (ENNReal.ofReal ((a ^ (n - 1))⁻¹) • μ.map (fun y => a⁻¹ • (y - x₀))) z r P =
      planeBetaSq μ (x₀ + a • z) (a * r) (x₀ + a • P.1, P.2) := by
  have hpre : (fun y : Rn n => a⁻¹ • (y - x₀)) ⁻¹' ball z r = ball (x₀ + a • z) (a * r) := by
    ext y
    have : a⁻¹ • (y - x₀) - z = a⁻¹ • (y - (x₀ + a • z)) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]; abel
    simp only [mem_preimage, mem_ball, dist_eq_norm, this, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 ha), inv_mul_lt_iff₀ ha]
  have hint : ∀ y : Rn n, ⟪a⁻¹ • (y - x₀) - P.1, P.2⟫ ^ 2 / r ^ 2 =
      ⟪y - (x₀ + a • P.1), P.2⟫ ^ 2 / (a * r) ^ 2 := by
    intro y
    have : a⁻¹ • (y - x₀) - P.1 = a⁻¹ • (y - (x₀ + a • P.1)) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]; abel
    rw [this, real_inner_smul_left]
    field_simp
  unfold planeBetaSq
  rw [Measure.restrict_smul, lintegral_smul_measure,
    setLIntegral_map measurableSet_ball (by fun_prop) (by fun_prop), hpre]
  simp_rw [hint]
  rw [smul_eq_mul, mul_pow a r (n - 1), ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a ^ (n - 1)),
    ENNReal.ofReal_inv_of_pos (by positivity), div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 (by positivity)).ne')
      (Or.inl ENNReal.ofReal_ne_top)]
  ring

/-- Translation and dilation (the scale invariance in Miś §3): with
`μ_{x₀,a}(A) = a^{-(n-1)} μ(x₀ + aA)`, `β_{μ_{x₀,a}}(z, r) = β_μ(x₀ + a z, a r)`. -/
theorem jonesBetaSq_smul_map {a : ℝ} (ha : 0 < a) (μ : Measure (Rn n)) (x₀ z : Rn n) (r : ℝ) :
    jonesBetaSq (ENNReal.ofReal ((a ^ (n - 1))⁻¹) • μ.map (fun y => a⁻¹ • (y - x₀))) z r =
      jonesBetaSq μ (x₀ + a • z) (a * r) := by
  apply le_antisymm
  · refine le_jonesBetaSq fun Q hQ => ?_
    have hQ' : Q = (x₀ + a • (a⁻¹ • (Q.1 - x₀)), Q.2) := by
      rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul, add_sub_cancel]
    rw [hQ', ← planeBetaSq_smul_map ha μ x₀ z r (a⁻¹ • (Q.1 - x₀), Q.2)]
    exact jonesBetaSq_le_planeBetaSq hQ
  · refine le_jonesBetaSq fun P hP => ?_
    rw [planeBetaSq_smul_map ha]
    exact jonesBetaSq_le_planeBetaSq hP

/-! ### Comparisons -/

/-- Nested balls: if `B_r(x) ⊆ B_R(y)` then `β²_P(x, r) ≤ (R/r)^{n+1} β²_P(y, R)` for every
plane `P`. -/
theorem planeBetaSq_le_of_ball_subset (hn : 1 ≤ n) {μ : Measure (Rn n)} {x y : Rn n} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (h : ball x r ⊆ ball y R) (P : Rn n × Rn n) :
    planeBetaSq μ x r P ≤ ENNReal.ofReal ((R / r) ^ (n + 1)) * planeBetaSq μ y R P := by
  rw [planeBetaSq_eq hn hr, planeBetaSq_eq hn hR, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have : (R / r) ^ (n + 1) * (R ^ (n + 1))⁻¹ = (r ^ (n + 1))⁻¹ := by
    rw [div_pow]; field_simp
  rw [this]
  exact mul_le_mul_right (lintegral_mono_set h) _

/-- If `B_r(x) ⊆ B_R(y)` then `β²(x, r) ≤ (R/r)^{n+1} β²(y, R)`. -/
theorem jonesBetaSq_le_of_ball_subset (hn : 1 ≤ n) {μ : Measure (Rn n)} {x y : Rn n} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (h : ball x r ⊆ ball y R) :
    jonesBetaSq μ x r ≤ ENNReal.ofReal ((R / r) ^ (n + 1)) * jonesBetaSq μ y R := by
  rw [jonesBetaSq_eq_iInf μ y R,
    ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top]
  exact le_iInf fun P =>
    (jonesBetaSq_le_planeBetaSq P.2).trans (planeBetaSq_le_of_ball_subset hn hr hR h P)

/-- Radius monotonicity at a fixed centre: `β²(x, r) ≤ (R/r)^{n+1} β²(x, R)` for `r ≤ R`. -/
theorem jonesBetaSq_le_of_le (hn : 1 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    jonesBetaSq μ x r ≤ ENNReal.ofReal ((R / r) ^ (n + 1)) * jonesBetaSq μ x R :=
  jonesBetaSq_le_of_ball_subset hn hr (hr.trans_le hrR) (ball_subset_ball hrR)

/-- Miś (3.1) (`k = n − 1`, `q = 2`): for `y ∈ B_r(x)`, `β²(x, r) ≤ 2^{n+1} β²(y, 2r)`. -/
theorem jonesBetaSq_le_two_pow_mul (hn : 1 ≤ n) {μ : Measure (Rn n)} {x y : Rn n} {r : ℝ}
    (hr : 0 < r) (hy : y ∈ ball x r) :
    jonesBetaSq μ x r ≤ 2 ^ (n + 1) * jonesBetaSq μ y (2 * r) := by
  have h := jonesBetaSq_le_of_ball_subset hn (μ := μ) hr (by positivity : (0 : ℝ) < 2 * r)
    (ball_subset_ball' (by rw [mem_ball, dist_comm] at hy; linarith) : ball x r ⊆ ball y (2 * r))
  rwa [mul_div_assoc, div_self hr.ne', mul_one, ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat] at h

/-- Integrated form of Miś (3.1):
`μ(B_r(x)) β²(x, r) ≤ 2^{n+1} ∫_{B_r(x)} β²(y, 2r) dμ(y)`. No finiteness is needed. -/
theorem measure_mul_jonesBetaSq_le (hn : 1 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r : ℝ}
    (hr : 0 < r) :
    μ (ball x r) * jonesBetaSq μ x r ≤
      2 ^ (n + 1) * ∫⁻ y in ball x r, jonesBetaSq μ y (2 * r) ∂μ := by
  rw [← lintegral_const_mul' _ _ (by simp), mul_comm, ← setLIntegral_const]
  exact setLIntegral_mono' measurableSet_ball fun y hy => jonesBetaSq_le_two_pow_mul hn hr hy

/-- Averaged form of Miś (3.1): if `0 < μ(B_r(x)) < ∞`, then
`β²(x, r) ≤ 2^{n+1} μ(B_r(x))⁻¹ ∫_{B_r(x)} β²(y, 2r) dμ(y)`. -/
theorem jonesBetaSq_le_average (hn : 1 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r : ℝ}
    (hr : 0 < r) (h0 : μ (ball x r) ≠ 0) (hfin : μ (ball x r) ≠ ∞) :
    jonesBetaSq μ x r ≤
      2 ^ (n + 1) * (∫⁻ y in ball x r, jonesBetaSq μ y (2 * r) ∂μ) / μ (ball x r) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hfin), mul_comm]
  exact measure_mul_jonesBetaSq_le hn hr

/-- A helper for dividing out a positive real factor. -/
private lemma le_ofReal_div_mul {b I : ℝ≥0∞} {K c : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (h : b * ENNReal.ofReal c ≤ ENNReal.ofReal K * I) : b ≤ ENNReal.ofReal (K / c) * I := by
  calc b = b * ENNReal.ofReal c * ENNReal.ofReal c⁻¹ := by
        rw [mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_inv_cancel₀ hc.ne', ENNReal.ofReal_one,
          mul_one]
    _ ≤ ENNReal.ofReal K * I * ENNReal.ofReal c⁻¹ := by gcongr
    _ = ENNReal.ofReal (K / c) * I := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul hK]; ring

/-- Miś's `δ²(x, r) = r^{-(n-1)} ∫_{B_r(x)} β²(y, r) dμ(y)` ((3.2), `k = n − 1`, `q = 2`). -/
@[expose] def deltaSq (μ : Measure (Rn n)) (x : Rn n) (r : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in ball x r, jonesBetaSq μ y r ∂μ) / ENNReal.ofReal (r ^ (n - 1))

theorem deltaSq_eq {r : ℝ} (hr : 0 < r) (μ : Measure (Rn n)) (x : Rn n) :
    deltaSq μ x r =
      ENNReal.ofReal ((r ^ (n - 1))⁻¹) * ∫⁻ y in ball x r, jonesBetaSq μ y r ∂μ := by
  rw [deltaSq, div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (by positivity), mul_comm]

/-- Miś (3.3)/(3.4) at `q = 2`, `k = n − 1`: under the lower mass bound
`μ(B_r(x)) ≥ τ M r^{n-1}`, `β²(x, r) ≤ 4^n (τ M)⁻¹ δ²(x, 2r)`. Miś (3.3) writes `=` where `≤` is
meant. -/
theorem jonesBetaSq_le_deltaSq (hn : 1 ≤ n) {μ : Measure (Rn n)} {x : Rn n} {r τ M : ℝ}
    (hr : 0 < r) (hτ : 0 < τ) (hM : 0 < M)
    (hlow : ENNReal.ofReal (τ * M * r ^ (n - 1)) ≤ μ (ball x r)) :
    jonesBetaSq μ x r ≤ ENNReal.ofReal (4 ^ n / (τ * M)) * deltaSq μ x (2 * r) := by
  have h2r : (0 : ℝ) < 2 * r := by positivity
  have key : jonesBetaSq μ x r * ENNReal.ofReal (τ * M * r ^ (n - 1)) ≤
      ENNReal.ofReal (2 ^ (n + 1) * (2 * r) ^ (n - 1)) * deltaSq μ x (2 * r) := by
    calc jonesBetaSq μ x r * ENNReal.ofReal (τ * M * r ^ (n - 1))
        ≤ μ (ball x r) * jonesBetaSq μ x r := by rw [mul_comm]; gcongr
      _ ≤ 2 ^ (n + 1) * ∫⁻ y in ball x r, jonesBetaSq μ y (2 * r) ∂μ :=
          measure_mul_jonesBetaSq_le hn hr
      _ ≤ 2 ^ (n + 1) * ∫⁻ y in ball x (2 * r), jonesBetaSq μ y (2 * r) ∂μ := by
          refine mul_le_mul_right (lintegral_mono_set (ball_subset_ball ?_)) _
          linarith
      _ = ENNReal.ofReal (2 ^ (n + 1) * (2 * r) ^ (n - 1)) * deltaSq μ x (2 * r) := by
          rw [deltaSq_eq h2r, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            mul_assoc (2 ^ (n + 1) : ℝ),
            mul_inv_cancel₀ (by positivity : ((2 : ℝ) * r) ^ (n - 1) ≠ 0), mul_one,
            ENNReal.ofReal_pow zero_le_two,
            ENNReal.ofReal_ofNat]
  have h := le_ofReal_div_mul (by positivity) (by positivity) key
  convert h using 3
  rw [mul_pow, show (4 : ℝ) ^ n = 2 ^ (n + 1) * 2 ^ (n - 1) by
    rw [← pow_add, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; congr 1; omega]
  field_simp

/-- Monotonicity of `δ²`: if `B_{r₁}(x₁) ⊆ B_{r₂}(x₂)` and `0 < r₁ ≤ r₂`, then
`δ²(x₁, r₁) ≤ (r₂/r₁)^{2n} δ²(x₂, r₂)`. -/
theorem deltaSq_le_of_ball_subset (hn : 1 ≤ n) {μ : Measure (Rn n)} {x₁ x₂ : Rn n} {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr : r₁ ≤ r₂) (h : ball x₁ r₁ ⊆ ball x₂ r₂) :
    deltaSq μ x₁ r₁ ≤ ENNReal.ofReal ((r₂ / r₁) ^ (2 * n)) * deltaSq μ x₂ r₂ := by
  have hr₂ : 0 < r₂ := hr₁.trans_le hr
  rw [deltaSq_eq hr₁, deltaSq_eq hr₂, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal ((r₁ ^ (n - 1))⁻¹) * ∫⁻ y in ball x₁ r₁, jonesBetaSq μ y r₁ ∂μ
      ≤ ENNReal.ofReal ((r₁ ^ (n - 1))⁻¹) *
          ∫⁻ y in ball x₁ r₁, ENNReal.ofReal ((r₂ / r₁) ^ (n + 1)) * jonesBetaSq μ y r₂ ∂μ := by
        gcongr with y
        exact jonesBetaSq_le_of_le hn hr₁ hr
    _ ≤ ENNReal.ofReal ((r₁ ^ (n - 1))⁻¹) *
          ∫⁻ y in ball x₂ r₂, ENNReal.ofReal ((r₂ / r₁) ^ (n + 1)) * jonesBetaSq μ y r₂ ∂μ := by
        exact mul_le_mul_right (lintegral_mono_set h) _
    _ = ENNReal.ofReal ((r₂ / r₁) ^ (2 * n) * (r₂ ^ (n - 1))⁻¹) *
          ∫⁻ y in ball x₂ r₂, jonesBetaSq μ y r₂ ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, div_pow]
        field_simp
        ring

/-! ### Discretization (Miś Remark 3.1) -/

/-- `∫_{(a, b]} dt/t = log(b/a)`. -/
theorem lintegral_Ioc_inv_ofReal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ t in Ioc a b, (ENNReal.ofReal t)⁻¹ = ENNReal.ofReal (Real.log (b / a)) := by
  rw [setLIntegral_congr_fun measurableSet_Ioc
    (g := fun t => ENNReal.ofReal t⁻¹)
    (fun t ht => (ENNReal.ofReal_inv_of_pos (ha.trans ht.1)).symm)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha (ha.trans_le hab)]
  · exact ((continuousOn_inv₀.mono fun t ht => (ha.trans_le ht.1).ne').integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact inv_nonneg.2 (ha.trans ht.1).le

theorem lintegral_Ioo_inv_ofReal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ t in Ioo a b, (ENNReal.ofReal t)⁻¹ = ENNReal.ofReal (Real.log (b / a)) := by
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, lintegral_Ioc_inv_ofReal ha hab]

theorem lintegral_Ico_inv_ofReal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ t in Ico a b, (ENNReal.ofReal t)⁻¹ = ENNReal.ofReal (Real.log (b / a)) := by
  rw [setLIntegral_congr Ico_ae_eq_Ioc, lintegral_Ioc_inv_ofReal ha hab]

private lemma measurable_inv_ofReal : Measurable fun t : ℝ => (ENNReal.ofReal t)⁻¹ :=
  ENNReal.measurable_ofReal.inv

/-- (3c), the single-scale window:
`β²(z, s) ≤ (2^{n+1} / log 2) ∫_{(s, 2s)} β²(z, t) dt/t`. -/
theorem beta_le_integral_window (hn : 1 ≤ n) (μ : Measure (Rn n)) (z : Rn n) {s : ℝ}
    (hs : 0 < s) :
    jonesBetaSq μ z s ≤ ENNReal.ofReal (2 ^ (n + 1) / Real.log 2) *
      ∫⁻ t in Ioo s (2 * s), jonesBetaSq μ z t / ENNReal.ofReal t := by
  refine le_ofReal_div_mul (by positivity) (Real.log_pos one_lt_two) ?_
  have h2 : Real.log 2 = Real.log (2 * s / s) := by rw [mul_div_assoc, div_self hs.ne', mul_one]
  rw [h2, ← lintegral_Ioo_inv_ofReal hs (by linarith),
    ← lintegral_const_mul _ measurable_inv_ofReal,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
  rw [div_eq_mul_inv, ← mul_assoc]
  gcongr
  calc jonesBetaSq μ z s ≤ ENNReal.ofReal ((t / s) ^ (n + 1)) * jonesBetaSq μ z t :=
        jonesBetaSq_le_of_le hn hs ht.1.le
    _ ≤ ENNReal.ofReal (2 ^ (n + 1)) * jonesBetaSq μ z t := by
        have h1 : t / s ≤ 2 := by rw [div_le_iff₀ hs]; linarith [ht.2]
        have h2 : 0 ≤ t / s := div_nonneg (hs.trans ht.1).le hs.le
        gcongr

/-- (3a), sum ≤ integral (Miś Remark 3.1 with exact ranges): for
`0 < ρ < 1` and `c > 0`,
`Σ_{α ≥ 0} β²(z, cρ^{α+1}) ≤ (ρ^{-(n+1)} / log ρ⁻¹) ∫_{(0, c)} β²(z, t) dt/t`. -/
theorem sum_beta_le_integral (hn : 1 ≤ n) (μ : Measure (Rn n)) (z : Rn n) {ρ c : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    ∑' α : ℕ, jonesBetaSq μ z (c * ρ ^ (α + 1)) ≤
      ENNReal.ofReal (ρ⁻¹ ^ (n + 1) / Real.log ρ⁻¹) *
        ∫⁻ t in Ioo 0 c, jonesBetaSq μ z t / ENNReal.ofReal t := by
  set f : ℕ → ℝ := fun α => c * ρ ^ α with hf
  have hanti : Antitone f := fun a b hab =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0.le hρ1.le hab) hc.le
  have hdisj : Pairwise (Disjoint on fun α : ℕ => Ico (f (α + 1)) (f α)) := by
    simpa [Order.succ_eq_add_one] using hanti.pairwise_disjoint_on_Ico_succ
  have hfpos : ∀ α, 0 < f α := fun α => by positivity
  have hsub : (⋃ α, Ico (f (α + 1)) (f α)) ⊆ Ioo 0 c := by
    refine iUnion_subset fun α t ht => ⟨(hfpos _).trans_le ht.1, ht.2.trans_le ?_⟩
    simpa [hf] using hanti (Nat.zero_le α)
  have hlog : 0 < Real.log ρ⁻¹ := Real.log_pos (one_lt_inv₀ hρ0 |>.2 hρ1)
  have hpiece : ∀ α, jonesBetaSq μ z (f (α + 1)) ≤ ENNReal.ofReal (ρ⁻¹ ^ (n + 1) / Real.log ρ⁻¹) *
      ∫⁻ t in Ico (f (α + 1)) (f α), jonesBetaSq μ z t / ENNReal.ofReal t := by
    intro α
    have hratio : f α / f (α + 1) = ρ⁻¹ := by
      simp only [hf, pow_succ]; field_simp
    refine le_ofReal_div_mul (by positivity) hlog ?_
    rw [← hratio, ← lintegral_Ico_inv_ofReal (hfpos _) (hanti (Nat.le_succ α)),
      ← lintegral_const_mul _ measurable_inv_ofReal,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ico fun t ht => ?_
    rw [div_eq_mul_inv (jonesBetaSq μ z t), ← mul_assoc]
    gcongr
    calc jonesBetaSq μ z (f (α + 1))
        ≤ ENNReal.ofReal ((t / f (α + 1)) ^ (n + 1)) * jonesBetaSq μ z t :=
          jonesBetaSq_le_of_le hn (hfpos _) ht.1
      _ ≤ ENNReal.ofReal ((f α / f (α + 1)) ^ (n + 1)) * jonesBetaSq μ z t := by
          have h1 : 0 ≤ t / f (α + 1) := div_nonneg ((hfpos _).le.trans ht.1) (hfpos _).le
          have h2 : t ≤ f α := ht.2.le
          gcongr
  calc ∑' α : ℕ, jonesBetaSq μ z (c * ρ ^ (α + 1))
      ≤ ∑' α : ℕ, ENNReal.ofReal (ρ⁻¹ ^ (n + 1) / Real.log ρ⁻¹) *
          ∫⁻ t in Ico (f (α + 1)) (f α), jonesBetaSq μ z t / ENNReal.ofReal t :=
        ENNReal.tsum_le_tsum hpiece
    _ = ENNReal.ofReal (ρ⁻¹ ^ (n + 1) / Real.log ρ⁻¹) *
          ∫⁻ t in ⋃ α, Ico (f (α + 1)) (f α), jonesBetaSq μ z t / ENNReal.ofReal t := by
        rw [ENNReal.tsum_mul_left, lintegral_iUnion (fun _ => measurableSet_Ico) hdisj]
    _ ≤ _ := mul_le_mul_right (lintegral_mono_set hsub) _

/-- (3b), integral ≤ sum (Miś Remark 3.1 with exact ranges): for
`0 < ρ < 1` and `c > 0`,
`∫_{(0, c)} β²(z, t) dt/t ≤ ρ^{-(n+1)} log ρ⁻¹ Σ_{α ≥ 0} β²(z, cρ^α)`. -/
theorem integral_le_sum_beta (hn : 1 ≤ n) (μ : Measure (Rn n)) (z : Rn n) {ρ c : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    ∫⁻ t in Ioo 0 c, jonesBetaSq μ z t / ENNReal.ofReal t ≤
      ENNReal.ofReal (ρ⁻¹ ^ (n + 1) * Real.log ρ⁻¹) * ∑' α : ℕ, jonesBetaSq μ z (c * ρ ^ α) := by
  set f : ℕ → ℝ := fun α => c * ρ ^ α with hf
  have hanti : Antitone f := fun a b hab =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0.le hρ1.le hab) hc.le
  have hfpos : ∀ α, 0 < f α := fun α => by positivity
  have hcover : Ioo 0 c ⊆ ⋃ α, Ioc (f (α + 1)) (f α) := by
    intro t ht
    obtain ⟨α, h1, h2⟩ := exists_nat_pow_near_of_lt_one (div_pos ht.1 hc)
      ((div_le_one hc).2 ht.2.le) hρ0 hρ1
    refine mem_iUnion.2 ⟨α, ?_, ?_⟩
    · simp only [hf]; rw [lt_div_iff₀ hc] at h1; linarith
    · simp only [hf]; rw [div_le_iff₀ hc] at h2; linarith
  have hlog : 0 ≤ Real.log ρ⁻¹ := (Real.log_pos (one_lt_inv₀ hρ0 |>.2 hρ1)).le
  have hpiece : ∀ α, ∫⁻ t in Ioc (f (α + 1)) (f α), jonesBetaSq μ z t / ENNReal.ofReal t ≤
      ENNReal.ofReal (ρ⁻¹ ^ (n + 1) * Real.log ρ⁻¹) * jonesBetaSq μ z (f α) := by
    intro α
    have hratio : f α / f (α + 1) = ρ⁻¹ := by
      simp only [hf, pow_succ]; field_simp
    calc ∫⁻ t in Ioc (f (α + 1)) (f α), jonesBetaSq μ z t / ENNReal.ofReal t
        ≤ ∫⁻ t in Ioc (f (α + 1)) (f α),
            (ENNReal.ofReal (ρ⁻¹ ^ (n + 1)) * jonesBetaSq μ z (f α)) * (ENNReal.ofReal t)⁻¹ := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          rw [div_eq_mul_inv]
          gcongr
          have ht0 : 0 < t := (hfpos _).trans ht.1
          calc jonesBetaSq μ z t ≤ ENNReal.ofReal ((f α / t) ^ (n + 1)) * jonesBetaSq μ z (f α) :=
                jonesBetaSq_le_of_le hn ht0 ht.2
            _ ≤ ENNReal.ofReal (ρ⁻¹ ^ (n + 1)) * jonesBetaSq μ z (f α) := by
                gcongr
                rw [← hratio]
                exact div_le_div_of_nonneg_left (hfpos _).le (hfpos _) ht.1.le
      _ = ENNReal.ofReal (ρ⁻¹ ^ (n + 1) * Real.log ρ⁻¹) * jonesBetaSq μ z (f α) := by
          rw [lintegral_const_mul _ measurable_inv_ofReal,
            lintegral_Ioc_inv_ofReal (hfpos _) (hanti (Nat.le_succ α)), hratio,
            ENNReal.ofReal_mul (by positivity)]
          ring
  calc ∫⁻ t in Ioo 0 c, jonesBetaSq μ z t / ENNReal.ofReal t
      ≤ ∫⁻ t in ⋃ α, Ioc (f (α + 1)) (f α), jonesBetaSq μ z t / ENNReal.ofReal t :=
        lintegral_mono_set hcover
    _ ≤ ∑' α, ∫⁻ t in Ioc (f (α + 1)) (f α), jonesBetaSq μ z t / ENNReal.ofReal t :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' α, ENNReal.ofReal (ρ⁻¹ ^ (n + 1) * Real.log ρ⁻¹) * jonesBetaSq μ z (f α) :=
        ENNReal.tsum_le_tsum hpiece
    _ = _ := ENNReal.tsum_mul_left

/-- The form used by the discrete Reifenberg estimates: the full sum from scale `c` down is
controlled by the integral up to `2c`. Combines (3c) at `s = c` with (3a):
`Σ_{α ≥ 0} β²(z, cρ^α) ≤ (2^{n+1}/log 2 + ρ^{-(n+1)}/log ρ⁻¹) ∫_{(0, 2c)} β²(z, t) dt/t`.
Apply it with `c := c ρ^m` to bound `Σ_{l ≥ m} β²(z, c ρ^l)`. -/
theorem tsum_beta_le_integral_two_mul (hn : 1 ≤ n) (μ : Measure (Rn n)) (z : Rn n) {ρ c : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    ∑' α : ℕ, jonesBetaSq μ z (c * ρ ^ α) ≤
      ENNReal.ofReal (2 ^ (n + 1) / Real.log 2 + ρ⁻¹ ^ (n + 1) / Real.log ρ⁻¹) *
        ∫⁻ t in Ioo 0 (2 * c), jonesBetaSq μ z t / ENNReal.ofReal t := by
  set A : ℝ := 2 ^ (n + 1) / Real.log 2
  set B : ℝ := ρ⁻¹ ^ (n + 1) / Real.log ρ⁻¹
  have hA : 0 ≤ A := div_nonneg (by positivity) (Real.log_nonneg one_le_two)
  have hB : 0 ≤ B := div_nonneg (by positivity)
    (Real.log_nonneg (one_le_inv₀ hρ0 |>.2 hρ1.le))
  set I₁ := ∫⁻ t in Ioo c (2 * c), jonesBetaSq μ z t / ENNReal.ofReal t
  set I₂ := ∫⁻ t in Ioo 0 c, jonesBetaSq μ z t / ENNReal.ofReal t
  have h1 : jonesBetaSq μ z (c * ρ ^ 0) ≤ ENNReal.ofReal A * I₁ := by
    rw [pow_zero, mul_one]
    exact beta_le_integral_window hn μ z hc
  have h2 := sum_beta_le_integral hn μ z hρ0 hρ1 hc
  have hunion : I₁ + I₂ ≤ ∫⁻ t in Ioo 0 (2 * c), jonesBetaSq μ z t / ENNReal.ofReal t := by
    rw [add_comm, ← lintegral_union measurableSet_Ioo
      (Set.disjoint_left.2 fun _ h h' => lt_asymm h.2 h'.1)]
    exact lintegral_mono_set (union_subset (Ioo_subset_Ioo_right (by linarith))
      (Ioo_subset_Ioo_left hc.le))
  rw [tsum_eq_zero_add' ENNReal.summable]
  calc jonesBetaSq μ z (c * ρ ^ 0) + ∑' α : ℕ, jonesBetaSq μ z (c * ρ ^ (α + 1))
      ≤ ENNReal.ofReal A * I₁ + ENNReal.ofReal B * I₂ := add_le_add h1 h2
    _ ≤ ENNReal.ofReal (A + B) * I₁ + ENNReal.ofReal (A + B) * I₂ := by
        gcongr <;> linarith
    _ = ENNReal.ofReal (A + B) * (I₁ + I₂) := by ring
    _ ≤ _ := mul_le_mul_right hunion _

end GMTFoundations
