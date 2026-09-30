/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Statements.Reifenberg
public import GMTFoundations.Reifenberg.Beta
public import GMTFoundations.GMT.FlatPiece
public import GMTFoundations.GMT.Packing
import GMTFoundations.GMT.Polar
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Discrete Reifenberg: constants, reductions and the statement bridge

This file fixes the interfaces of the proof of the discrete Reifenberg theorem
(`DiscreteReifenbergStatement`; A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity
of stationary and minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227, Thm 3.4). We
prove it via M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43
(2018); arXiv:1612.02461 (Miś), Thm 1.1 with `q = 2`, `k = n − 1`, rather than via NV §5–§6.2:
Miś's hypothesis (1.3) with `J = δ²` is exactly the hypothesis of `DiscreteReifenbergStatement`,
it has no lower-mass cutoff `ε_n`, and `J` need not be small.

Miś's §4 begins with several reductions "without loss of generality" (rounding the radii to powers
of `ρ`, supporting `μ` in `B₁`, finite truncation); each changes constants, and each is proved
here as a separate lemma (R0–R6 below). Miś proves Claim 4.1 for `j = A, …, 0`, but the step
`j = 0` uses β-numbers on balls far outside `B₂`, where (1.3) gives no information. We prove the
claim only for `j ≥ 1` and replace the last step by a covering argument (R5).

## Main definitions

* The constants of the proof: `ledgerK` (`K = 3ⁿ + 1`), `ledgerC0` (`c₀ = ω_k 15^{-k}`),
  `ledgerC1` (`C₁ = 2/c₀`), `ledgerTau` (`τ = 1/(16·15^k)`), `ledgerTau0` (`τ₀ = τ/K`),
  `ledgerR0` (`R₀ = 16`), `ledgerRho` (`ρ`), `ledgerKappa` (`κ = 1/(1−ρ)`), `ledgerMass`
  (`M(J)`, parametrized by the engine constants `C₂, C₃, ε_eng` fixed in `Discrete.lean`) and
  `ledgerD` (`D`). Each is defined only from constants listed before it, so there is no circular
  dependence between `ρ`, the mass constant `M` and `δ`.
* `atomMeasure S x w = Σ_{i∈S} w_i δ_{x_i}`, `ballFamilyMeasure S x r` (the measure of
  `DiscreteReifenbergStatement`), and `levMeasure ρ Z lev = Σ_{z∈Z} ω_k ρ^{k·lev z} δ_z` (a rounded
  family indexed by its centers).
* `BetaHyp μ J`: Miś (1.3) with constant `J` on all balls `B_s(y) ⊆ B₂`.
* `MiskiewiczBound n`: Miś Thm 1.1 at `q = 2` (the "Miś form").
* `IsReducedFamily ρ Z lev`: the family after R1–R3 (radii `ρ^{lev z}`, `lev ≥ 1`, centers in `B₁`,
  disjoint balls).
* `ClaimAt ρ M Z lev j`: the centered Claim(j): `μ(B_{ρ^j}(p)) ≤ M (ρ^j)^k` for every center `p` of
  level `> j`. `MisClaimAt`: Miś's form of Claim 4.1 (balls disjoint from the centers of level
  `≤ j`); the two are equivalent up to a factor `3ⁿ` (R6).
* `ClaimOneStatement n ρ M`: Claim(1) for all reduced families (what the downward induction in
  `Discrete.lean` yields).

## Main statements

* Bridge: `discreteReifenbergStatement_of_miskiewiczBound`.
* R0 `BetaHyp.mono`; R1 `roundLevel` with `pow_roundLevel_le`, `le_pow_roundLevel`,
  `ballFamilyMeasure_le_of_radius_le`, `ballFamilyMeasure_apply_le_of_radius`;
  R2 `ballFamilyMeasure_filter_le`,
  `ballFamilyMeasure_filter_apply_of_subset`; R3 `claimAt_of_sup_le`; R5
  `levMeasure_ball_one_le_of_claimAt_one`; R6 `ClaimAt.of_misClaimAt`, `MisClaimAt.of_claimAt`.
* `miskiewiczBound_of_claimOne`: `ClaimOneStatement ⇒ MiskiewiczBound` (R1, R2, R3, R5 chained).
* `discreteReifenbergStatement_of_claimOne`: with the above `ρ` and `M(J)`,
  `ClaimOneStatement` implies `DiscreteReifenbergStatement n` (`δ = 1`, `D = ledgerD`).
* `levMeasure_inter_le_of_claimAt`: the covering bound shared by the upper-bound lemma, R5 and
  R6. The upper-bound lemma (`levMeasure_ball_le_of_claimAt_succ` in `Covering.lean`; it is not in
  Miś) is the upper-bound transfer: if Claim(l+1) holds and `M ≥ ω_k ρ^{−k}`, then
  `μ(B_{ρ^{l+1}}(w)) ≤ K M (ρ^{l+1})^k` for every `w` within `ρ^l` of a center of level `> l`,
  with `K = 3ⁿ + 1` independent of `ρ`. It supplies the upper mass hypothesis of the tilt lemma,
  which Miś's proof of Proposition 4.3 uses without checking.

Miś's rescaling of each ball of the induction to `B₁` (R4 in this numbering) is not needed: every
step of the induction is stated at absolute scales in the original coordinates.
-/

@[expose] public noncomputable section

namespace GMTFoundations.DiscreteReifenberg

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

/-! ### The constants of the proof -/

/-- `K = 3ⁿ + 1`, the factor in the upper-bound lemma: the tilt lemma's upper mass constant is
`K·M`. It does not depend on `ρ`. -/
def ledgerK (n : ℕ) : ℝ := 3 ^ n + 1

/-- `c₀ = ω_k 15^{-k}`, the lower area of a graph piece (`le_hausdorffN_inter_ball_of_graph`). -/
def ledgerC0 (n : ℕ) : ℝ := unitBallVolume (n - 1) / 15 ^ (n - 1)

/-- `C₁ = 2/c₀ = 2·15^k/ω_k`, the constant of Miś (4.2). It depends on `n` only. -/
def ledgerC1 (n : ℕ) : ℝ := 2 * 15 ^ (n - 1) / unitBallVolume (n - 1)

/-- `τ = 1/(16·15^k)`, so that `ω_k C₁ τ = 1/8`. Miś takes `τ = 80^{-1} 6^{-n}` and
`C₁ = 20·3^k`, but his lower area bound behind that `C₁` fails for `k ≥ 9` (see
`le_hausdorffN_inter_ball_of_graph`); our `τ` is smaller. -/
def ledgerTau (n : ℕ) : ℝ := 1 / (16 * 15 ^ (n - 1))

/-- `τ₀ = τ/K`, the ratio of the lower mass constant `a = τM` to the upper mass
constant `b = KM` in the tilt lemma `planeDist_sq_le_of_mass`. -/
def ledgerTau0 (n : ℕ) : ℝ := ledgerTau n / ledgerK n

/-- `R₀ = 16`, the radius factor of the hypothesis region `B_{R₀ r_j}(p)`. -/
def ledgerR0 : ℝ := 16

/-- `ρ = min(τ₀/(2A_n), 1/100, 1/(20n))`, with `A_n = farConst n` (`Reifenberg/Tilt.lean`). -/
def ledgerRho (n : ℕ) : ℝ :=
  min (ledgerTau0 n / (2 * farConst n)) (min (1 / 100) (1 / (20 * (n : ℝ))))

/-- `κ = 1/(1 − ρ)`; best planes are taken at radius `κ r_i`. -/
def ledgerKappa (n : ℕ) : ℝ := 1 / (1 - ledgerRho n)

/-- `M(J) = max(ω_k/τ, ω_kρ^{−k}, √(C₂J/(Kτ)), √(2C₃J/τ), √(J/(ε K τ)))`,
parametrized by the engine constants `C₂` ((4.1)), `C₃` ((4.3)) and the engine smallness
`ε = ε_eng`, which are functions of `n` (`engC2`, `engC3`, `engEps` in `Discrete.lean`). It is
`C(n)·max(1, J^{1/2})` (`ledgerMass_le`). `M` is chosen after `ρ`, so the term `ω_kρ^{−k}` creates
no circularity. -/
def ledgerMass (n : ℕ) (C₂ C₃ ε J : ℝ) : ℝ :=
  max (max (max (max (unitBallVolume (n - 1) / ledgerTau n)
    (unitBallVolume (n - 1) / ledgerRho n ^ (n - 1)))
    (√(C₂ * J / (ledgerK n * ledgerTau n)))) (√(2 * C₃ * J / ledgerTau n)))
    (√(J / (ε * ledgerK n * ledgerTau n)))

/-- The constant `D = 2^{k+1} 3ⁿ ρ^{−n} M(1)/ω_k + 1` of `DiscreteReifenbergStatement`
(`2^{k+1} = 2ⁿ`), with `δ = 1`: from `μ(B₁) ≤ (2/ρ)^k · 2 (3/ρ)ⁿ ρ^k M(J)` (R1, R5) and
`Σ_{x_j ∈ B₁} r_j^k = μ(B₁)/ω_k`. -/
def ledgerD (n : ℕ) (C₂ C₃ ε : ℝ) : ℝ :=
  2 ^ n * (3 / ledgerRho n) ^ n * ledgerMass n C₂ C₃ ε 1 / unitBallVolume (n - 1) + 1

theorem ledgerK_pos (n : ℕ) : 0 < ledgerK n := by unfold ledgerK; positivity

theorem one_le_ledgerK (n : ℕ) : 1 ≤ ledgerK n := by
  unfold ledgerK; have : (0 : ℝ) < 3 ^ n := by positivity
  linarith

theorem ledgerC0_pos (n : ℕ) : 0 < ledgerC0 n := by
  have := unitBallVolume_pos (n - 1); unfold ledgerC0; positivity

theorem ledgerC1_pos (n : ℕ) : 0 < ledgerC1 n := by
  have := unitBallVolume_pos (n - 1); unfold ledgerC1; positivity

theorem ledgerC1_mul_ledgerC0 (n : ℕ) : ledgerC1 n * ledgerC0 n = 2 := by
  have := (unitBallVolume_pos (n - 1)).ne'
  unfold ledgerC1 ledgerC0; field_simp

theorem ledgerTau_pos (n : ℕ) : 0 < ledgerTau n := by unfold ledgerTau; positivity

theorem ledgerTau_le_one (n : ℕ) : ledgerTau n ≤ 1 := by
  unfold ledgerTau
  rw [div_le_one (by positivity)]
  have : (1 : ℝ) ≤ 15 ^ (n - 1) := one_le_pow₀ (by norm_num)
  linarith

/-- `ω_k C₁ τ = 1/8`. -/
theorem omega_mul_ledgerC1_mul_ledgerTau (n : ℕ) :
    unitBallVolume (n - 1) * ledgerC1 n * ledgerTau n = 1 / 8 := by
  have := (unitBallVolume_pos (n - 1)).ne'
  unfold ledgerC1 ledgerTau; field_simp; ring

theorem ledgerTau0_pos (n : ℕ) : 0 < ledgerTau0 n :=
  div_pos (ledgerTau_pos n) (ledgerK_pos n)

theorem ledgerRho_pos (hn : 1 ≤ n) : 0 < ledgerRho n := by
  have h1 : 0 < ledgerTau0 n / (2 * farConst n) :=
    div_pos (ledgerTau0_pos n) (mul_pos two_pos (farConst_pos n))
  have h2 : (0 : ℝ) < 1 / (20 * (n : ℝ)) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  unfold ledgerRho
  exact lt_min h1 (lt_min (by norm_num) h2)

/-- The tilt lemma's condition `(Hρ)`: `ρ ≤ τ₀/(2A_n)`. -/
theorem ledgerRho_le_tilt (n : ℕ) : ledgerRho n ≤ ledgerTau0 n / (2 * farConst n) :=
  min_le_left _ _

theorem ledgerRho_le_hundredth (n : ℕ) : ledgerRho n ≤ 1 / 100 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem ledgerRho_le_inv_twenty_mul (n : ℕ) : ledgerRho n ≤ 1 / (20 * (n : ℝ)) :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem ledgerRho_le_half (n : ℕ) : ledgerRho n ≤ 1 / 2 :=
  (ledgerRho_le_hundredth n).trans (by norm_num)

theorem ledgerRho_lt_one (n : ℕ) : ledgerRho n < 1 :=
  (ledgerRho_le_hundredth n).trans_lt (by norm_num)

/-- `ρ ≤ 1/R₀`, so `B_{R₀ ρ^j}(p) ⊆ B₂` for `p ∈ B₁`, `j ≥ 1` (R5). -/
theorem ledgerRho_le_inv_R0 (n : ℕ) : ledgerRho n ≤ 1 / ledgerR0 :=
  (ledgerRho_le_hundredth n).trans (by norm_num [ledgerR0])

/-- The tilt lemma's condition in the form used with `a = τM` (goodness) and `b = KM`
(the upper-bound lemma): `ρ ≤ a / (2 A_n b)`. -/
theorem ledgerRho_le_tilt_mass {M : ℝ} (hM : 0 < M) :
    ledgerRho n ≤ ledgerTau n * M / (2 * farConst n * (ledgerK n * M)) := by
  have h : ledgerTau n * M / (2 * farConst n * (ledgerK n * M)) =
      ledgerTau0 n / (2 * farConst n) := by
    have := (farConst_pos n).ne'
    have := (ledgerK_pos n).ne'
    unfold ledgerTau0; field_simp
  rw [h]
  exact ledgerRho_le_tilt n

/-- `(1 + ρ)^k ≤ 2` (from `ρ ≤ 1/(20n)`; used in the final bound of the inductive step). -/
theorem one_add_ledgerRho_pow_le_two (hn : 1 ≤ n) : (1 + ledgerRho n) ^ (n - 1) ≤ 2 := by
  have hρ0 := (ledgerRho_pos hn).le
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk : ((n - 1 : ℕ) : ℝ) * ledgerRho n ≤ 1 / 20 := by
    have h1 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    calc ((n - 1 : ℕ) : ℝ) * ledgerRho n ≤ n * (1 / (20 * n)) :=
          mul_le_mul h1 (ledgerRho_le_inv_twenty_mul n) hρ0 (by positivity)
      _ = 1 / 20 := by field_simp
  calc (1 + ledgerRho n) ^ (n - 1) ≤ Real.exp (ledgerRho n) ^ (n - 1) := by
        gcongr
        linarith [Real.add_one_le_exp (ledgerRho n)]
    _ = Real.exp (((n - 1 : ℕ) : ℝ) * ledgerRho n) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log 2) := by
        gcongr
        linarith [Real.log_two_gt_d9]
    _ = 2 := Real.exp_log two_pos

theorem one_sub_ledgerRho_pos (n : ℕ) : 0 < 1 - ledgerRho n := by
  linarith [ledgerRho_lt_one n]

theorem ledgerKappa_pos (n : ℕ) : 0 < ledgerKappa n :=
  div_pos one_pos (one_sub_ledgerRho_pos n)

theorem one_le_ledgerKappa (hn : 1 ≤ n) : 1 ≤ ledgerKappa n := by
  unfold ledgerKappa
  rw [le_div_iff₀ (one_sub_ledgerRho_pos n)]
  linarith [ledgerRho_pos hn]

theorem ledgerKappa_le (n : ℕ) : ledgerKappa n ≤ 100 / 99 := by
  unfold ledgerKappa
  rw [div_le_iff₀ (one_sub_ledgerRho_pos n)]
  linarith [ledgerRho_le_hundredth n]

theorem ledgerKappa_mul_one_sub (n : ℕ) : ledgerKappa n * (1 - ledgerRho n) = 1 := by
  unfold ledgerKappa; field_simp [(one_sub_ledgerRho_pos n).ne']

section Mass

variable {C₂ C₃ ε J : ℝ}

theorem omega_div_tau_le_ledgerMass :
    unitBallVolume (n - 1) / ledgerTau n ≤ ledgerMass n C₂ C₃ ε J :=
  le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))

theorem omega_div_rho_pow_le_ledgerMass :
    unitBallVolume (n - 1) / ledgerRho n ^ (n - 1) ≤ ledgerMass n C₂ C₃ ε J :=
  le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))

theorem sqrt_C₂_le_ledgerMass :
    √(C₂ * J / (ledgerK n * ledgerTau n)) ≤ ledgerMass n C₂ C₃ ε J :=
  le_max_of_le_left (le_max_of_le_left (le_max_right _ _))

theorem sqrt_C₃_le_ledgerMass : √(2 * C₃ * J / ledgerTau n) ≤ ledgerMass n C₂ C₃ ε J :=
  le_max_of_le_left (le_max_right _ _)

theorem sqrt_eps_le_ledgerMass :
    √(J / (ε * ledgerK n * ledgerTau n)) ≤ ledgerMass n C₂ C₃ ε J :=
  le_max_right _ _

theorem ledgerMass_pos : 0 < ledgerMass n C₂ C₃ ε J :=
  (div_pos (unitBallVolume_pos _) (ledgerTau_pos n)).trans_le omega_div_tau_le_ledgerMass

/-- Final balls are "bad": `ω_k ≤ τM` (engine hypothesis `EngineHyp.fin_le`). -/
theorem omega_le_ledgerTau_mul_ledgerMass :
    unitBallVolume (n - 1) ≤ ledgerTau n * ledgerMass n C₂ C₃ ε J := by
  have h := (div_le_iff₀' (ledgerTau_pos n)).1 (omega_div_tau_le_ledgerMass (C₂ := C₂)
    (C₃ := C₃) (ε := ε) (J := J) (n := n))
  exact h

theorem omega_le_ledgerMass : unitBallVolume (n - 1) ≤ ledgerMass n C₂ C₃ ε J := by
  have h := omega_le_ledgerTau_mul_ledgerMass (n := n) (C₂ := C₂) (C₃ := C₃) (ε := ε) (J := J)
  have := ledgerTau_le_one n
  have := (ledgerMass_pos (n := n) (C₂ := C₂) (C₃ := C₃) (ε := ε) (J := J)).le
  nlinarith

/-- `M ≥ ω_k ρ^{−k}`, the hypothesis of the upper-bound lemma (in the multiplied-out form used
there). -/
theorem omega_le_ledgerMass_mul_rho_pow (hn : 1 ≤ n) :
    unitBallVolume (n - 1) ≤ ledgerMass n C₂ C₃ ε J * ledgerRho n ^ (n - 1) :=
  (div_le_iff₀ (pow_pos (ledgerRho_pos hn) _)).1 omega_div_rho_pow_le_ledgerMass

private lemma le_sq_of_sqrt_le {x M : ℝ} (h : √x ≤ M) : x ≤ M ^ 2 := by
  have hM : 0 ≤ M := (Real.sqrt_nonneg x).trans h
  exact (Real.sqrt_le_left hM).1 h

/-- The (4.1) condition `C₂ (Λθ)^{-1} J ≤ 1`, with `Λθ = KτM²`. -/
theorem C₂_mul_le_ledgerMass :
    C₂ * J ≤ ledgerK n * ledgerTau n * ledgerMass n C₂ C₃ ε J ^ 2 := by
  have hKτ := mul_pos (ledgerK_pos n) (ledgerTau_pos n)
  have h := le_sq_of_sqrt_le (sqrt_C₂_le_ledgerMass (n := n) (C₂ := C₂)
    (C₃ := C₃) (ε := ε) (J := J))
  rw [div_le_iff₀ hKτ] at h
  linarith

/-- The (4.3) condition `C₃ J/(τM²) ≤ 1/2`. -/
theorem C₃_mul_le_ledgerMass :
    2 * C₃ * J ≤ ledgerTau n * ledgerMass n C₂ C₃ ε J ^ 2 := by
  have h := le_sq_of_sqrt_le
    (sqrt_C₃_le_ledgerMass (n := n) (C₂ := C₂) (C₃ := C₃) (ε := ε) (J := J))
  rw [div_le_iff₀ (ledgerTau_pos n)] at h
  linarith

/-- The engine smallness `J ≤ ε_eng · Λθ` (`EngineHyp.J_small`), with `Λθ = KτM²`. -/
theorem J_le_eps_mul_ledgerMass (hε : 0 < ε) :
    J ≤ ε * (ledgerK n * ledgerTau n * ledgerMass n C₂ C₃ ε J ^ 2) := by
  have hKτ := mul_pos (mul_pos hε (ledgerK_pos n)) (ledgerTau_pos n)
  have h := le_sq_of_sqrt_le
    (sqrt_eps_le_ledgerMass (n := n) (C₂ := C₂) (C₃ := C₃) (ε := ε) (J := J))
  rw [div_le_iff₀ hKτ] at h
  linarith

/-- `M(J) ≤ M(1)·max(1, J^{1/2})`: `M` is `C(n) max(1, J^{1/2})` (Miś Thm 1.1 at `q = 2`). -/
theorem ledgerMass_le (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hε : 0 < ε) :
    ledgerMass n C₂ C₃ ε J ≤ ledgerMass n C₂ C₃ ε 1 * max 1 √J := by
  set M₁ := ledgerMass n C₂ C₃ ε 1
  have hM₁ : 0 < M₁ := ledgerMass_pos
  have hmax : 1 ≤ max 1 √J := le_max_left _ _
  have hconst : ∀ t, t ≤ M₁ → t ≤ M₁ * max 1 √J := fun t ht =>
    ht.trans (le_mul_of_one_le_right hM₁.le hmax)
  have hsq : ∀ c : ℝ, 0 ≤ c → √(c * 1) ≤ M₁ → √(c * J) ≤ M₁ * max 1 √J := by
    intro c hc h
    rw [mul_one] at h
    rw [Real.sqrt_mul hc]
    exact mul_le_mul h (le_max_right _ _) (Real.sqrt_nonneg _) hM₁.le
  have hKτ := mul_pos (ledgerK_pos n) (ledgerTau_pos n)
  have hτ := ledgerTau_pos n
  unfold ledgerMass
  refine max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_
  · exact hconst _ omega_div_tau_le_ledgerMass
  · exact hconst _ omega_div_rho_pow_le_ledgerMass
  · have := hsq (C₂ / (ledgerK n * ledgerTau n)) (by positivity)
      (by rw [show C₂ / (ledgerK n * ledgerTau n) * 1 = C₂ * 1 / (ledgerK n * ledgerTau n) by
        ring]; exact sqrt_C₂_le_ledgerMass)
    rwa [show C₂ / (ledgerK n * ledgerTau n) * J = C₂ * J / (ledgerK n * ledgerTau n) by
      ring] at this
  · have := hsq (2 * C₃ / ledgerTau n) (by positivity)
      (by rw [show 2 * C₃ / ledgerTau n * 1 = 2 * C₃ * 1 / ledgerTau n by ring]
          exact sqrt_C₃_le_ledgerMass)
    rwa [show 2 * C₃ / ledgerTau n * J = 2 * C₃ * J / ledgerTau n by ring] at this
  · have hεKτ := mul_pos (mul_pos hε (ledgerK_pos n)) hτ
    have := hsq (1 / (ε * ledgerK n * ledgerTau n)) (by positivity)
      (by rw [show 1 / (ε * ledgerK n * ledgerTau n) * 1 = 1 / (ε * ledgerK n * ledgerTau n) by
        ring]; exact sqrt_eps_le_ledgerMass)
    rwa [show 1 / (ε * ledgerK n * ledgerTau n) * J = J / (ε * ledgerK n * ledgerTau n) by
      ring] at this

end Mass

/-! ### Atomic measures -/

/-- The atomic measure `Σ_{i ∈ S} w_i δ_{x_i}`. -/
def atomMeasure {ι : Type*} (S : Finset ι) (x : ι → Rn n) (w : ι → ℝ≥0∞) : Measure (Rn n) :=
  ∑ i ∈ S, w i • Measure.dirac (x i)

/-- The measure `Σ_{j ∈ S} ω_{n-1} r_j^{n-1} δ_{x_j}` of a family of balls; it is definitionally
the measure in `DiscreteReifenbergStatement`. -/
def ballFamilyMeasure {ι : Type*} (S : Finset ι) (x : ι → Rn n) (r : ι → ℝ) : Measure (Rn n) :=
  atomMeasure S x fun j => ENNReal.ofReal (unitBallVolume (n - 1) * r j ^ (n - 1))

/-- A rounded family indexed by its centers: `Σ_{z ∈ Z} ω_k (ρ^{lev z})^k δ_z`. -/
def levMeasure (ρ : ℝ) (Z : Finset (Rn n)) (lev : Rn n → ℕ) : Measure (Rn n) :=
  ballFamilyMeasure Z id fun z => ρ ^ lev z

section Atom

variable {ι : Type*} {S : Finset ι} {x : ι → Rn n} {w : ι → ℝ≥0∞}

theorem atomMeasure_apply (A : Set (Rn n)) [DecidablePred fun i => x i ∈ A] :
    atomMeasure S x w A = ∑ i ∈ S with x i ∈ A, w i := by
  simp only [atomMeasure, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
    smul_eq_mul, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : x i ∈ A <;> simp [h]

/-- An atomic measure only sees its atoms: `μ(A) ≤ μ(B)` as soon as every atom in `A` is in `B`. -/
theorem atomMeasure_mono_of_atoms {A B : Set (Rn n)} (h : ∀ i ∈ S, x i ∈ A → x i ∈ B) :
    atomMeasure S x w A ≤ atomMeasure S x w B := by
  classical
  rw [atomMeasure_apply, atomMeasure_apply]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => bot_le
  intro i hi
  simp only [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, h i hi.1 hi.2⟩

theorem atomMeasure_le_of_le {S' : Finset ι} {w' : ι → ℝ≥0∞} (hS : S' ⊆ S)
    (hw : ∀ i ∈ S', w' i ≤ w i) : atomMeasure S' x w' ≤ atomMeasure S x w := by
  classical
  rw [Measure.le_iff']
  intro A
  rw [atomMeasure_apply, atomMeasure_apply]
  calc ∑ i ∈ S' with x i ∈ A, w' i ≤ ∑ i ∈ S' with x i ∈ A, w i :=
        Finset.sum_le_sum fun i hi => hw i (Finset.mem_filter.1 hi).1
    _ ≤ ∑ i ∈ S with x i ∈ A, w i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hS)
          fun _ _ _ => bot_le

open scoped Classical in
theorem atomMeasure_filter_apply {U A : Set (Rn n)} (hA : A ⊆ U) :
    atomMeasure (S.filter fun i => x i ∈ U) x w A = atomMeasure S x w A := by
  rw [atomMeasure_apply, atomMeasure_apply, Finset.filter_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hA h.2, h.2⟩⟩

theorem ballFamilyMeasure_apply {r : ι → ℝ} (A : Set (Rn n)) [DecidablePred fun i => x i ∈ A] :
    ballFamilyMeasure S x r A =
      ∑ i ∈ S with x i ∈ A, ENNReal.ofReal (unitBallVolume (n - 1) * r i ^ (n - 1)) :=
  atomMeasure_apply A

end Atom

/-! ### The hypothesis and the Miś form -/

/-- Miś (1.3) at `q = 2` with constant `J`: `∫_{B_s(y)} ∫_0^s β²_μ(z,t) dt/t dμ(z) ≤ J s^{n-1}` for
every ball `B_s(y) ⊆ B₂`. The hypothesis of `DiscreteReifenbergStatement` is `BetaHyp μ δ²` with
`<`. -/
def BetaHyp (μ : Measure (Rn n)) (J : ℝ) : Prop :=
  ∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball 0 2 →
    ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s, jonesBetaSq μ z t / ENNReal.ofReal t) ∂μ ≤
      ENNReal.ofReal (J * s ^ (n - 1))

/-- **The Miś form** (Miśkiewicz, Thm 1.1, `q = 2`, `k = n − 1`). There is `C(n)` such
that for every `J ≥ 0` and every finite family of disjoint balls `B_{r_i}(x_i) ⊆ B₂` whose measure
`μ = Σ ω_k r_i^k δ_{x_i}` satisfies (1.3) with constant `J`, `μ(B₁) ≤ C max(1, J^{1/2})`.
`discreteReifenbergStatement_of_miskiewiczBound` turns it into `DiscreteReifenbergStatement`. -/
def MiskiewiczBound (n : ℕ) : Prop :=
  ∃ C : ℝ, ∀ J : ℝ, 0 ≤ J → ∀ {ι : Type} (S : Finset ι) (x : ι → Rn n) (r : ι → ℝ),
    (∀ i ∈ S, 0 < r i) → (∀ i ∈ S, ball (x i) (r i) ⊆ ball 0 2) →
    (S : Set ι).Pairwise (fun i j => Disjoint (ball (x i) (r i)) (ball (x j) (r j))) →
    BetaHyp (ballFamilyMeasure S x r) J →
      ballFamilyMeasure S x r (ball 0 1) ≤ ENNReal.ofReal (C * max 1 √J)

/-- **Statement bridge**: the Miś form implies `DiscreteReifenbergStatement`, with `δ = 1` and
`D = max(C, 0)/ω_{n-1} + 1`. -/
theorem discreteReifenbergStatement_of_miskiewiczBound (h : 2 ≤ n → MiskiewiczBound n) :
    DiscreteReifenbergStatement n := by
  classical
  intro hn
  obtain ⟨C, hC⟩ := h hn
  have hω := unitBallVolume_pos (n - 1)
  refine ⟨1, one_pos, max C 0 / unitBallVolume (n - 1) + 1, ?_⟩
  intro ι S x r hr hB hdisj hyp
  have hμ := hC 1 zero_le_one S x r hr hB hdisj fun y s hs hys => by
    have := hyp y s hs hys
    rw [one_pow] at this
    exact this.le
  rw [Real.sqrt_one, max_self, mul_one, ballFamilyMeasure_apply,
    ← ENNReal.ofReal_sum_of_nonneg fun i hi => by
      have := hr i (Finset.mem_filter.1 hi).1; positivity] at hμ
  have hsum : unitBallVolume (n - 1) * ∑ i ∈ S with x i ∈ ball 0 1, r i ^ (n - 1) ≤ max C 0 := by
    rw [Finset.mul_sum]
    exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 (hμ.trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have : ∑ i ∈ S with x i ∈ ball 0 1, r i ^ (n - 1) ≤ max C 0 / unitBallVolume (n - 1) := by
    rw [le_div_iff₀ hω]; linarith
  linarith

/-! ### R0: monotonicity of the hypothesis -/

/-- **R0**: `ν ≤ μ` and (1.3) for `μ` imply (1.3) for `ν`, with the same constant
(`jonesBetaSq` is monotone in the measure, `jonesBetaSq_mono_measure`). -/
theorem BetaHyp.mono {μ ν : Measure (Rn n)} {J : ℝ} (h : BetaHyp μ J) (hνμ : ν ≤ μ) :
    BetaHyp ν J := by
  intro y s hs hys
  refine le_trans ?_ (h y s hs hys)
  calc ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s, jonesBetaSq ν z t / ENNReal.ofReal t) ∂ν
      ≤ ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s, jonesBetaSq μ z t / ENNReal.ofReal t) ∂ν :=
        lintegral_mono fun z => lintegral_mono fun t =>
          ENNReal.div_le_div_right (jonesBetaSq_mono_measure hνμ z t) _
    _ ≤ _ := lintegral_mono' (Measure.restrict_mono subset_rfl hνμ) le_rfl

/-! ### R1: rounding radii to powers of `ρ` -/

open scoped Classical in
/-- `roundLevel ρ r = min {m ≥ 1 : ρ^m ≤ r}` (R1, the first reduction in
Miś §4); `1` if there is no such `m`. -/
def roundLevel (ρ r : ℝ) : ℕ :=
  if h : ∃ m : ℕ, 1 ≤ m ∧ ρ ^ m ≤ r then Nat.find h else 1

theorem exists_pow_le_of_pos {ρ r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hr : 0 < r) :
    ∃ m : ℕ, 1 ≤ m ∧ ρ ^ m ≤ r := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr hρ1
  exact ⟨m + 1, by omega, (pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)).trans hm.le⟩

theorem one_le_roundLevel (ρ r : ℝ) : 1 ≤ roundLevel ρ r := by
  unfold roundLevel
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact le_rfl

/-- **R1** (i): the rounded radius is at most the original one. -/
theorem pow_roundLevel_le {ρ r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hr : 0 < r) :
    ρ ^ roundLevel ρ r ≤ r := by
  have h := exists_pow_le_of_pos hρ0 hρ1 hr
  unfold roundLevel
  rw [dite_eq_left h]
  exact (Nat.find_spec h).2

/-- **R1** (ii): for `r ≤ 2`, `r ≤ (2/ρ) ρ^{m(r)}`. -/
theorem le_pow_roundLevel {ρ r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hr : 0 < r) (hr2 : r ≤ 2) :
    r ≤ 2 / ρ * ρ ^ roundLevel ρ r := by
  have h := exists_pow_le_of_pos hρ0 hρ1 hr
  unfold roundLevel
  rw [dite_eq_left h]
  have hm1 : 1 ≤ Nat.find h := (Nat.find_spec h).1
  rcases eq_or_lt_of_le hm1 with h1 | h1
  · rw [← h1, pow_one, div_mul_cancel₀ _ hρ0.ne']
    exact hr2
  · have hmin := Nat.find_min h (show Nat.find h - 1 < Nat.find h by omega)
    have hlt : r < ρ ^ (Nat.find h - 1) := by
      by_contra hle
      exact hmin ⟨by omega, not_lt.1 hle⟩
    have hpow : ρ ^ Nat.find h = ρ ^ (Nat.find h - 1) * ρ := by
      rw [← pow_succ]; congr 1; omega
    have hp : 0 < ρ ^ (Nat.find h - 1) := pow_pos hρ0 _
    rw [hpow, show 2 / ρ * (ρ ^ (Nat.find h - 1) * ρ) = 2 * ρ ^ (Nat.find h - 1) by
      field_simp]
    linarith

/-- **R1** (ii′): `r^k ≤ (2/ρ)^k (ρ^{m(r)})^k`, the constant change of the conclusion. -/
theorem pow_le_pow_roundLevel {ρ r : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hr : 0 < r) (hr2 : r ≤ 2)
    (k : ℕ) : r ^ k ≤ (2 / ρ) ^ k * (ρ ^ roundLevel ρ r) ^ k := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ hr.le (le_pow_roundLevel hρ0 hρ1 hr hr2) k

section Family

variable {ι : Type*} {S : Finset ι} {x : ι → Rn n}

/-- **R1** (iii), hypothesis side: shrinking the radii decreases `ballFamilyMeasure` (then R0
applies). Miś says that rounding changes the constants in both (1.3) and (1.4); by R0 only (1.4)
changes. -/
theorem ballFamilyMeasure_le_of_radius_le {r r' : ι → ℝ} (h : ∀ i ∈ S, 0 ≤ r' i ∧ r' i ≤ r i) :
    ballFamilyMeasure S x r' ≤ ballFamilyMeasure S x r :=
  atomMeasure_le_of_le subset_rfl fun i hi => ENNReal.ofReal_le_ofReal <|
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h i hi).1 (h i hi).2 _)
      (unitBallVolume_pos _).le

/-- **R1** (iv), conclusion side: if `r_i^k ≤ c r_i'^k`, then `μ_r(A) ≤ c μ_{r'}(A)`. -/
theorem ballFamilyMeasure_apply_le_of_radius {r r' : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i ∈ S, r i ^ (n - 1) ≤ c * r' i ^ (n - 1)) (A : Set (Rn n)) :
    ballFamilyMeasure S x r A ≤ ENNReal.ofReal c * ballFamilyMeasure S x r' A := by
  classical
  rw [ballFamilyMeasure_apply, ballFamilyMeasure_apply, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  have hω := (unitBallVolume_pos (n - 1)).le
  calc unitBallVolume (n - 1) * r i ^ (n - 1)
      ≤ unitBallVolume (n - 1) * (c * r' i ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left (h i (Finset.mem_filter.1 hi).1) hω
    _ = c * (unitBallVolume (n - 1) * r' i ^ (n - 1)) := by ring

open scoped Classical in
/-- **R2** (hypothesis side): restricting to `x_i ∈ U` decreases `ballFamilyMeasure`. -/
theorem ballFamilyMeasure_filter_le (r : ι → ℝ) (U : Set (Rn n)) :
    ballFamilyMeasure (S.filter fun i => x i ∈ U) x r ≤ ballFamilyMeasure S x r :=
  atomMeasure_le_of_le (Finset.filter_subset _ _) fun _ _ => le_rfl

open scoped Classical in
/-- **R2** (conclusion side, exact): the restricted measure agrees on subsets of `U`. -/
theorem ballFamilyMeasure_filter_apply_of_subset (r : ι → ℝ) {U A : Set (Rn n)} (hA : A ⊆ U) :
    ballFamilyMeasure (S.filter fun i => x i ∈ U) x r A = ballFamilyMeasure S x r A :=
  atomMeasure_filter_apply hA

/-- Positive radii and pairwise disjoint balls force distinct centers. -/
theorem injOn_of_pairwise_disjoint {r : ι → ℝ} (hr : ∀ i ∈ S, 0 < r i)
    (hdisj : (S : Set ι).Pairwise fun i j => Disjoint (ball (x i) (r i)) (ball (x j) (r j))) :
    Set.InjOn x S := by
  intro i hi j hj hij
  by_contra hne
  have := hdisj hi hj hne
  exact Set.disjoint_left.1 this (mem_ball_self (hr i hi)) (hij ▸ mem_ball_self (hr j hj))

end Family

/-- A ball of radius `r` inside `B₂` has `r ≤ 2` (`n ≥ 1`). -/
theorem radius_le_two_of_ball_subset (hn : 1 ≤ n) {y : Rn n} {r : ℝ}
    (h : ball y r ⊆ ball (0 : Rn n) 2) : r ≤ 2 := by
  refine le_of_not_gt fun hr => ?_
  set v : Rn n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
  have hv : ‖v‖ = 1 := by simp [v]
  have h₁ : y + (2 : ℝ) • v ∈ ball (0 : Rn n) 2 := h (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv]; norm_num; linarith)
  have h₂ : y - (2 : ℝ) • v ∈ ball (0 : Rn n) 2 := h (by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hv]; norm_num
    linarith)
  rw [mem_ball_zero_iff] at h₁ h₂
  have h4 : ‖(y + (2 : ℝ) • v) - (y - (2 : ℝ) • v)‖ = 4 := by
    rw [show (y + (2 : ℝ) • v) - (y - (2 : ℝ) • v) = (4 : ℝ) • v by module, norm_smul, hv]
    norm_num
  linarith [norm_sub_le (y + (2 : ℝ) • v) (y - (2 : ℝ) • v)]

/-! ### Reduced families and the centered claim -/

/-- The family after R1–R3, indexed by its centers: radii `ρ^{lev z}` with `lev z ≥ 1`,
centers in `B₁`, pairwise disjoint balls. Its measure is `levMeasure ρ Z lev`. -/
structure IsReducedFamily (ρ : ℝ) (Z : Finset (Rn n)) (lev : Rn n → ℕ) : Prop where
  one_le : ∀ z ∈ Z, 1 ≤ lev z
  mem_ball : ∀ z ∈ Z, z ∈ ball (0 : Rn n) 1
  disjoint : (Z : Set (Rn n)).Pairwise fun a b => Disjoint (ball a (ρ ^ lev a)) (ball b (ρ ^ lev b))

/-- **Claim(j)**, centered form: every center `p` of level `> j` has
`μ(B_{ρ^j}(p)) ≤ M (ρ^j)^k`. -/
def ClaimAt (ρ M : ℝ) (Z : Finset (Rn n)) (lev : Rn n → ℕ) (j : ℕ) : Prop :=
  ∀ p ∈ Z, j < lev p →
    levMeasure ρ Z lev (ball p (ρ ^ j)) ≤ ENNReal.ofReal (M * (ρ ^ j) ^ (n - 1))

/-- Miś's Claim 4.1 at scale `j`: every ball `B_{ρ^j}(y) ⊆ B₂` containing no center of
level `≤ j` has `μ ≤ M (ρ^j)^k`. Only used through R6. -/
def MisClaimAt (ρ M : ℝ) (Z : Finset (Rn n)) (lev : Rn n → ℕ) (j : ℕ) : Prop :=
  ∀ y : Rn n, ball y (ρ ^ j) ⊆ ball 0 2 → (∀ z ∈ Z, lev z ≤ j → z ∉ ball y (ρ ^ j)) →
    levMeasure ρ Z lev (ball y (ρ ^ j)) ≤ ENNReal.ofReal (M * (ρ ^ j) ^ (n - 1))

/-- Claim(1) for every reduced family satisfying (1.3) with constant `J`, with `M = M(J)`. This is
what the downward induction in `Discrete.lean` delivers (Claim(j) for `j = A, …, 1`);
`miskiewiczBound_of_claimOne` turns it into the Miś form. -/
def ClaimOneStatement (n : ℕ) (ρ : ℝ) (M : ℝ → ℝ) : Prop :=
  ∀ J : ℝ, 0 ≤ J → ∀ (Z : Finset (Rn n)) (lev : Rn n → ℕ), IsReducedFamily ρ Z lev →
    BetaHyp (levMeasure ρ Z lev) J → ClaimAt ρ (M J) Z lev 1

section Reduced

variable {ρ M : ℝ} {Z : Finset (Rn n)} {lev : Rn n → ℕ}

theorem levMeasure_apply (A : Set (Rn n)) [DecidablePred fun z : Rn n => z ∈ A] :
    levMeasure ρ Z lev A =
      ∑ z ∈ Z with z ∈ A, ENNReal.ofReal (unitBallVolume (n - 1) * (ρ ^ lev z) ^ (n - 1)) :=
  ballFamilyMeasure_apply A

/-- The atoms of a family with disjoint balls are separated by the sum of their radii. -/
theorem add_le_dist_of_disjoint (hρ0 : 0 < ρ)
    (hdisj : (Z : Set (Rn n)).Pairwise fun a b =>
      Disjoint (ball a (ρ ^ lev a)) (ball b (ρ ^ lev b)))
    {a b : Rn n} (ha : a ∈ Z) (hb : b ∈ Z) (hab : a ≠ b) : ρ ^ lev a + ρ ^ lev b ≤ dist a b :=
  (disjoint_ball_ball_iff (pow_pos hρ0 _) (pow_pos hρ0 _)).1 (hdisj ha hb hab)

/-- **R3** (base case of the induction): Claim(j) is vacuous once `j` is at least
the top level `A = sup lev`. -/
theorem claimAt_of_sup_le {j : ℕ} (h : Z.sup lev ≤ j) : ClaimAt ρ M Z lev j := by
  intro p hp hlt
  exact absurd ((Finset.le_sup hp).trans h) (not_le.2 hlt)

/-- Claim(j) is monotone in `M`. -/
theorem ClaimAt.mono_const {M' : ℝ} {j : ℕ} (h : ClaimAt ρ M Z lev j) (hM : M ≤ M')
    (hρ : 0 ≤ ρ) : ClaimAt ρ M' Z lev j := fun p hp hlt =>
  (h p hp hlt).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hM (by positivity)))

private lemma card_mul_ofReal_le {N : ℕ} {c y : ℝ} (hN : (N : ℝ) ≤ c) :
    (N : ℝ≥0∞) * ENNReal.ofReal y ≤ ENNReal.ofReal (c * y) := by
  rcases le_or_gt y 0 with hy | hy
  · rw [ENNReal.ofReal_of_nonpos hy, mul_zero]; exact bot_le
  · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hN hy.le)

/-- **Covering bound from Claim(j)** (shared by the upper-bound lemma, R5 and R6). If
`A ⊆ B̄_R(c)`, the atoms of level `> j` in `A` carry mass at most `(2R/ρ^j + 1)ⁿ M (ρ^j)^k`: a
maximal `ρ^j`-separated subset of them has at most `(2R/ρ^j + 1)ⁿ` points, and the balls
`B_{ρ^j}(q)` around it cover them. -/
theorem levMeasure_inter_le_of_claimAt (hρ0 : 0 < ρ) {j : ℕ} (hclaim : ClaimAt ρ M Z lev j)
    {A : Set (Rn n)} {c : Rn n} {R : ℝ} (hR : 0 ≤ R) (hA : A ⊆ closedBall c R) :
    levMeasure ρ Z lev (A ∩ {z | j < lev z}) ≤
      ENNReal.ofReal ((2 * R / ρ ^ j + 1) ^ n * (M * (ρ ^ j) ^ (n - 1))) := by
  set a := ρ ^ j with ha_def
  have ha : 0 < a := pow_pos hρ0 j
  set F : Set (Rn n) := (Z : Set (Rn n)) ∩ (A ∩ {z | j < lev z}) with hF
  have hFc : F ⊆ closedBall c R := fun z hz => hA hz.2.1
  obtain ⟨hQF, hQsep, hQcov⟩ := NaberValtorta.net_spec hFc ha
  set Q := NaberValtorta.net F a
  have hcard : (Q.card : ℝ) ≤ (2 * R / a + 1) ^ n :=
    NaberValtorta.card_le_of_pairwise_le_dist ha hR (hQF.trans hFc) hQsep
  calc levMeasure ρ Z lev (A ∩ {z | j < lev z})
      ≤ levMeasure ρ Z lev (⋃ q ∈ Q, ball q a) := by
        unfold levMeasure ballFamilyMeasure
        refine atomMeasure_mono_of_atoms fun z hz hzA => ?_
        exact hQcov ⟨hz, hzA⟩
    _ ≤ ∑ q ∈ Q, levMeasure ρ Z lev (ball q a) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ Q, ENNReal.ofReal (M * a ^ (n - 1)) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq' := hQF hq
        exact hclaim q hq'.1 hq'.2.2
    _ = (Q.card : ℝ≥0∞) * ENNReal.ofReal (M * a ^ (n - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := card_mul_ofReal_le hcard

/-- **R5** (replaces Miś's Claim 4.1 at `j = 0`): for a reduced family with Claim(1) and `M ≥ ω_k`,
`μ(B₁) ≤ 2 (3/ρ)ⁿ ρ^k M`. Level-1 atoms number at most `(1/ρ + 1)ⁿ`; the finer ones are covered
by at most `(2/ρ + 1)ⁿ` balls `B_ρ(q)` with `q` of level `> 1`. -/
theorem levMeasure_ball_one_le_of_claimAt_one (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hred : IsReducedFamily ρ Z lev) (hM : unitBallVolume (n - 1) ≤ M)
    (h1 : ClaimAt ρ M Z lev 1) :
    levMeasure ρ Z lev (ball 0 1) ≤ ENNReal.ofReal (2 * (3 / ρ) ^ n * (M * ρ ^ (n - 1))) := by
  classical
  have hρk : 0 < ρ ^ (n - 1) := pow_pos hρ0 _
  have hM0 : 0 ≤ M := (unitBallVolume_pos _).le.trans hM
  have hsplit : ball (0 : Rn n) 1 ⊆ (ball 0 1 ∩ {z | lev z ≤ 1}) ∪ (ball 0 1 ∩ {z | 1 < lev z}) :=
    fun z hz => by
      rcases le_or_gt (lev z) 1 with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
  -- coarse atoms: level exactly one, `2ρ`-separated
  have hcoarse : levMeasure ρ Z lev (ball 0 1 ∩ {z | lev z ≤ 1}) ≤
      ENNReal.ofReal ((1 / ρ + 1) ^ n * (M * ρ ^ (n - 1))) := by
    rw [levMeasure_apply]
    suffices H : ∀ F : Finset (Rn n), (∀ z ∈ F, z ∈ Z ∧ z ∈ ball (0 : Rn n) 1 ∩ {z | lev z ≤ 1}) →
        ∑ z ∈ F, ENNReal.ofReal (unitBallVolume (n - 1) * (ρ ^ lev z) ^ (n - 1)) ≤
          ENNReal.ofReal ((1 / ρ + 1) ^ n * (M * ρ ^ (n - 1))) from
      H _ fun z hz => Finset.mem_filter.1 hz
    intro F hF
    have hlev : ∀ z ∈ F, lev z = 1 := fun z hz =>
      le_antisymm (hF z hz).2.2 (hred.one_le z (hF z hz).1)
    have hsep : (F : Set (Rn n)).Pairwise fun a b => 2 * ρ ≤ dist a b := by
      intro a ha b hb hab
      have := add_le_dist_of_disjoint hρ0 hred.disjoint (hF a ha).1 (hF b hb).1 hab
      rw [hlev a ha, hlev b hb, pow_one] at this
      linarith
    have hFc : ↑F ⊆ closedBall (0 : Rn n) 1 := fun z hz =>
      ball_subset_closedBall (hF z hz).2.1
    have hcard := NaberValtorta.card_le_of_pairwise_le_dist (by positivity) zero_le_one hFc hsep
    rw [show 2 * 1 / (2 * ρ) = 1 / ρ by field_simp] at hcard
    refine (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal (M * ρ ^ (n - 1))) fun z hz => ?_).trans ?_
    · refine ENNReal.ofReal_le_ofReal ?_
      rw [hlev z hz, pow_one]
      exact mul_le_mul_of_nonneg_right hM hρk.le
    · rw [nsmul_eq_mul]
      exact card_mul_ofReal_le hcard
  have hfine := levMeasure_inter_le_of_claimAt hρ0 h1 (A := ball 0 1) (c := 0) zero_le_one
    ball_subset_closedBall
  rw [pow_one, mul_one] at hfine
  calc levMeasure ρ Z lev (ball 0 1)
      ≤ levMeasure ρ Z lev (ball 0 1 ∩ {z | lev z ≤ 1}) +
          levMeasure ρ Z lev (ball 0 1 ∩ {z | 1 < lev z}) :=
        (measure_mono hsplit).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal ((1 / ρ + 1) ^ n * (M * ρ ^ (n - 1))) +
          ENNReal.ofReal ((2 / ρ + 1) ^ n * (M * ρ ^ (n - 1))) := add_le_add hcoarse hfine
    _ = ENNReal.ofReal ((1 / ρ + 1) ^ n * (M * ρ ^ (n - 1)) +
          (2 / ρ + 1) ^ n * (M * ρ ^ (n - 1))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h3 : 1 / ρ + 1 ≤ 3 / ρ := by
          rw [div_add_one hρ0.ne', div_le_div_iff_of_pos_right hρ0]; linarith
        have h3' : 2 / ρ + 1 ≤ 3 / ρ := by
          rw [div_add_one hρ0.ne', div_le_div_iff_of_pos_right hρ0]; linarith
        have hMρ : 0 ≤ M * ρ ^ (n - 1) := by positivity
        have e1 := pow_le_pow_left₀ (by positivity) h3 n
        have e2 := pow_le_pow_left₀ (by positivity) h3' n
        nlinarith [mul_le_mul_of_nonneg_right e1 hMρ, mul_le_mul_of_nonneg_right e2 hMρ]

/-- **R6** (a): Miś's Claim 4.1 at scale `j` implies the centered Claim(j) with the same
`M` (for `ρ ≤ 1`, centers in `B₁`). -/
theorem ClaimAt.of_misClaimAt (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hred : IsReducedFamily ρ Z lev)
    {j : ℕ} (h : MisClaimAt ρ M Z lev j) : ClaimAt ρ M Z lev j := by
  intro p hp hlt
  refine h p ?_ fun z hz hzj hzb => ?_
  · refine ball_subset_ball' ?_
    have := mem_ball_zero_iff.1 (hred.mem_ball p hp)
    rw [dist_zero_right]
    have : ρ ^ j ≤ 1 := pow_le_one₀ hρ0.le hρ1
    linarith
  · have hne : z ≠ p := by rintro rfl; omega
    have hd := add_le_dist_of_disjoint hρ0 hred.disjoint hz hp hne
    have h1 : ρ ^ j ≤ ρ ^ lev z := pow_le_pow_of_le_one hρ0.le hρ1 hzj
    have h2 : 0 < ρ ^ lev p := pow_pos hρ0 _
    have := mem_ball.1 hzb
    linarith

/-- **R6** (b): the centered Claim(j) implies Miś's Claim 4.1 at scale `j` with `M`
replaced by `3ⁿ M`. -/
theorem MisClaimAt.of_claimAt (hρ0 : 0 < ρ) {j : ℕ} (h : ClaimAt ρ M Z lev j) :
    MisClaimAt ρ (3 ^ n * M) Z lev j := by
  intro y _ hy
  have ha : 0 < ρ ^ j := pow_pos hρ0 j
  calc levMeasure ρ Z lev (ball y (ρ ^ j))
      ≤ levMeasure ρ Z lev (ball y (ρ ^ j) ∩ {z | j < lev z}) := by
        unfold levMeasure ballFamilyMeasure
        refine atomMeasure_mono_of_atoms fun z hz hzb => ⟨hzb, ?_⟩
        by_contra hle
        exact hy z hz (not_lt.1 hle) hzb
    _ ≤ ENNReal.ofReal ((2 * ρ ^ j / ρ ^ j + 1) ^ n * (M * (ρ ^ j) ^ (n - 1))) :=
        levMeasure_inter_le_of_claimAt hρ0 h ha.le ball_subset_closedBall
    _ = ENNReal.ofReal (3 ^ n * M * (ρ ^ j) ^ (n - 1)) := by
        rw [mul_div_assoc, div_self ha.ne']; ring_nf

end Reduced

private lemma chain_const_eq (hn : 1 ≤ n) {ρ M : ℝ} (hρ0 : 0 < ρ) :
    (2 / ρ) ^ (n - 1) * (2 * (3 / ρ) ^ n * (M * ρ ^ (n - 1))) = 2 ^ n * (3 / ρ) ^ n * M := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [div_pow 2 ρ k, pow_succ 2 k]
  field_simp

/-- **Reductions chained** (R2, R1, R3, then R5). If Claim(1) holds for every reduced
family (`ClaimOneStatement`), with `ω_k ≤ M(J) ≤ C_M max(1, J^{1/2})`, then the Miś form holds with
`C = 2ⁿ (3/ρ)ⁿ C_M`. The constant changes are: R2 none, R1 `(2/ρ)^k` on the conclusion (none on the
hypothesis, by R0), R3 none, R5 `2 (3/ρ)ⁿ ρ^k`. -/
theorem miskiewiczBound_of_claimOne (hn : 1 ≤ n) {ρ CM : ℝ} {M : ℝ → ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hMω : ∀ J, 0 ≤ J → unitBallVolume (n - 1) ≤ M J)
    (hMC : ∀ J, 0 ≤ J → M J ≤ CM * max 1 √J) (h : ClaimOneStatement n ρ M) :
    MiskiewiczBound n := by
  classical
  refine ⟨2 ^ n * (3 / ρ) ^ n * CM, fun J hJ ι S x r hr hB hdisj hyp => ?_⟩
  -- R2: restrict to centers in `B₁`
  set S₁ := S.filter fun i => x i ∈ ball (0 : Rn n) 1 with hS₁
  have hS₁S : ∀ {i}, i ∈ S₁ → i ∈ S := fun hi => (Finset.mem_filter.1 hi).1
  -- R1: round the radii
  have hr2 : ∀ i ∈ S, r i ≤ 2 := fun i hi => radius_le_two_of_ball_subset hn (hB i hi)
  have hinj : Set.InjOn x S := injOn_of_pairwise_disjoint hr hdisj
  have hinj₁ : Set.InjOn x S₁ := hinj.mono fun i hi => hS₁S hi
  -- R3: pass to the (finite) family indexed by its centers
  obtain ⟨lev, hlev⟩ : ∃ lev : Rn n → ℕ, ∀ i ∈ S₁, lev (x i) = roundLevel ρ (r i) := by
    refine ⟨fun z => if hz : ∃ i ∈ S₁, x i = z then roundLevel ρ (r hz.choose) else 1,
      fun i hi => ?_⟩
    have hz : ∃ i' ∈ S₁, x i' = x i := ⟨i, hi, rfl⟩
    simp only [dite_eq_left hz]
    rw [hinj₁ hz.choose_spec.1 hi hz.choose_spec.2]
  set Z := S₁.image x
  have hμ' : levMeasure ρ Z lev = ballFamilyMeasure S₁ x fun i => ρ ^ roundLevel ρ (r i) := by
    unfold levMeasure ballFamilyMeasure atomMeasure
    rw [Finset.sum_image fun i hi j hj hij => hinj₁ hi hj hij]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [id, hlev i hi]
  have hred : IsReducedFamily ρ Z lev := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
      rw [hlev i hi]
      exact one_le_roundLevel _ _
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
      exact (Finset.mem_filter.1 hi).2
    · intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
      have hij : i ≠ j := fun h => hab (h ▸ rfl)
      rw [hlev i hi, hlev j hj]
      exact (hdisj (hS₁S hi) (hS₁S hj) hij).mono
        (ball_subset_ball (pow_roundLevel_le hρ0 hρ1 (hr i (hS₁S hi))))
        (ball_subset_ball (pow_roundLevel_le hρ0 hρ1 (hr j (hS₁S hj))))
  -- R0: the hypothesis passes to the reduced family
  have hbeta : BetaHyp (levMeasure ρ Z lev) J := by
    refine hyp.mono ?_
    rw [hμ']
    refine (ballFamilyMeasure_le_of_radius_le fun i hi => ⟨(pow_pos hρ0 _).le,
      pow_roundLevel_le hρ0 hρ1 (hr i (hS₁S hi))⟩).trans ?_
    exact ballFamilyMeasure_filter_le r _
  -- the induction's output and R5
  have hR5 := levMeasure_ball_one_le_of_claimAt_one hρ0 hρ1.le hred (hMω J hJ)
    (h J hJ Z lev hred hbeta)
  rw [hμ'] at hR5
  have hk : (0 : ℝ) ≤ (2 / ρ) ^ (n - 1) := by positivity
  calc ballFamilyMeasure S x r (ball 0 1) = ballFamilyMeasure S₁ x r (ball 0 1) :=
        (ballFamilyMeasure_filter_apply_of_subset r subset_rfl).symm
    _ ≤ ENNReal.ofReal ((2 / ρ) ^ (n - 1)) *
          ballFamilyMeasure S₁ x (fun i => ρ ^ roundLevel ρ (r i)) (ball 0 1) :=
        ballFamilyMeasure_apply_le_of_radius hk (fun i hi => pow_le_pow_roundLevel hρ0 hρ1
          (hr i (hS₁S hi)) (hr2 i (hS₁S hi)) _) _
    _ ≤ ENNReal.ofReal ((2 / ρ) ^ (n - 1)) *
          ENNReal.ofReal (2 * (3 / ρ) ^ n * (M J * ρ ^ (n - 1))) := by gcongr
    _ = ENNReal.ofReal (2 ^ n * (3 / ρ) ^ n * M J) := by
        rw [← ENNReal.ofReal_mul hk, chain_const_eq hn hρ0]
    _ ≤ ENNReal.ofReal (2 ^ n * (3 / ρ) ^ n * CM * max 1 √J) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc (2 ^ n * (3 / ρ) ^ n)]
        exact mul_le_mul_of_nonneg_left (hMC J hJ) (by positivity)

/-- **What the induction has to prove.** With `ρ = ledgerRho n` and
`M(J) = ledgerMass n C₂ C₃ ε J` (for engine constants `C₂, C₃ ≥ 0`, `ε > 0`), Claim(1) for all
reduced families implies `DiscreteReifenbergStatement`, with
`δ = 1` and `D = ledgerD n C₂ C₃ ε` (up to the `max · 0`, which is inactive). -/
theorem discreteReifenbergStatement_of_claimOne {C₂ C₃ ε : ℝ} (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hε : 0 < ε) (h : 2 ≤ n → ClaimOneStatement n (ledgerRho n) (ledgerMass n C₂ C₃ ε)) :
    DiscreteReifenbergStatement n :=
  discreteReifenbergStatement_of_miskiewiczBound fun hn =>
    miskiewiczBound_of_claimOne (by omega) (ledgerRho_pos (by omega)) (ledgerRho_lt_one n)
      (fun _ _ => omega_le_ledgerMass) (fun J _ => ledgerMass_le hC₂ hC₃ hε) (h hn)


end GMTFoundations.DiscreteReifenberg
