/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Statements.Reifenberg
public import GMTFoundations.Reifenberg.EngineMass
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered

/-!
# Discrete Reifenberg theorem

The discrete Reifenberg theorem `discrete_reifenberg : DiscreteReifenbergStatement n`, a version of
A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and minimizing
harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043 (NV), Thm 3.4, for
hyperplanes (`k = n − 1`). The proof follows M. Miśkiewicz, *Discrete Reifenberg-type theorem*,
Ann. Acad. Sci. Fenn. Math. 43 (2018); arXiv:1612.02461 (Miś), Thm 1.1 with `q = 2`, rather than
NV §5 and §6.2. Miś's hypothesis (1.3) with `J = δ²` is implied by the hypothesis of the statement;
it has no `ε_n` cutoff and `J` need not be small. Miś's conclusion
`Σ ω_k r_j^k ≤ C(n) max(1, J^{1/2})` gives the constant `D` of the statement (`ledgerD`).

Where Miś §4 only sketches a step, or where the argument as printed has a gap, the proof here is
complete. The main differences from Miś §4:
* Miś applies the tilt lemma (Lemma 3.3) in the proof of Proposition 4.3 without checking its
  hypothesis that `μ(B_{ρ²}(y)) ≤ M ρ^{2k}` for all `y`; for an atomic measure this does not follow
  from Claim 4.1, and taken literally it creates a circular dependence between `ρ` and `M`. Here it
  is supplied by the upper-bound lemma `levMeasure_ball_mul_le_of_claimAt_succ` (constant
  `(3ⁿ + 1) M`, valid once `M ≥ ω_k ρ^{-k}`; `M` is chosen after `ρ`).
* The step `j = 0` of Miś's induction (after "without loss of generality `supp μ ⊆ B₁`") uses
  β-numbers on balls not contained in `B₂`, where (1.3) says nothing. Here Claim 4.1 is proved only
  for `j ≥ 1` and the bound on `μ(B₁)` follows by a final covering argument
  (`levMeasure_ball_one_le_of_claimAt_one` in `Reductions.lean`).
* The first surface `T₀` is a whole hyperplane, so Miś's `|T₀| = ω_k` does not hold literally; the
  area bound (4.1) is localized to nested windows (`Induction.lean`).
* The lower area bound behind (4.2), `|T_i ∩ B/3| ≥ (1/10)(r/3)^k`, fails for `k ≥ 9` even for a
  flat plane. The constants are therefore `c₀ = ω_k 15^{-k}`, `C₁ = 2/c₀`, `τ = 1/(16·15^k)`
  (`ledgerC0`, `ledgerC1`, `ledgerTau`) instead of Miś's `C₁ = 20·3^k`, `τ = 80^{-1}6^{-n}`.

This file instantiates the generic engine of `EngineMass.lean` with the atomic measure
`levMeasure ρ Z lev` of a reduced family, the constants `ledgerRho`, `ledgerKappa`, `ledgerTau`,
`ledgerK` of `Reductions.lean`, and the inductive hypothesis, and runs the downward induction of
Claim 4.1.

## The inductive step (Miś §4)

`StepData n Z lev J M p j` collects the situation of the step for Claim(j) at the center `p`
(reduced family, (1.3), Claim(l) for all `l > j`, the top ball is good). The covering run is
`stepCover = CoverData.ofFamily ρ κ (τM) Z lev p j`.

* `StepData.hup`: the upper-bound lemma plus the inductive hypothesis give hypothesis (H2) of the
  tilt lemma `planeDist_sq_le_of_mass` with `Λ = K M`.
* `StepData.engineHyp`: the engine hypotheses (`CoverData.EngineHyp`) for this run.
* `StepData.claim_le`: the final bound `μ(B_{r_j}(p)) ≤ M r_j^k` (Miś §4, "Derivation of the
  bound"), from `EngineHyp.engine_mass` at a depth `N` beyond the top level (termination,
  `good N = ∅`).

## The theorem

`claimAt_of_reduced` is the downward induction (Claim(j) for all `j ≥ 1`); `claimOne` proves
`ClaimOneStatement n (ledgerRho n) (ledgerMass n (engC2 n) (engC3 n) (engEps n))`; then
`discrete_reifenberg` follows from `discreteReifenbergStatement_of_claimOne`.
-/

@[expose] public noncomputable section

namespace GMTFoundations

namespace DiscreteReifenberg

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open CoverData

variable {n : ℕ}

/-! ### The engine constants of the discrete run -/

/-- The smallness constant, in the form of `StepData.J_small`: `J ≤ ε_eng K τ M²` gives the engine
smallness `J ≤ smallEps θ²` with `θ = τM` (`ε_eng = smallEps · τ / K`). -/
def engEps (n : ℕ) : ℝ := smallEps n (ledgerRho n) (ledgerKappa n) * ledgerTau n / ledgerK n

/-- The constant `C₂ = 4 K C₁ C_A`, so that `C₂ J ≤ K τ M²` makes the (4.1) error term of the
final bound `≤ M r_j^k / 4`. -/
def engC2 (n : ℕ) : ℝ := 4 * ledgerK n * ledgerC1 n * areaConst n (ledgerRho n) (ledgerKappa n)

/-- The constant `C₃`, the constant of (4.3) (`excessConst`). -/
def engC3 (n : ℕ) : ℝ := excessConst n (ledgerRho n) (ledgerKappa n)

theorem engEps_pos (hn : 1 ≤ n) : 0 < engEps n := by
  have := smallEps_pos hn (ledgerRho_pos hn) (ledgerKappa_pos n)
  have := ledgerTau_pos n
  have := ledgerK_pos n
  unfold engEps
  positivity

theorem engC2_nonneg (hn : 1 ≤ n) : 0 ≤ engC2 n := by
  have := areaConst_nonneg (n := n) (ledgerRho_pos hn) (ledgerRho_lt_one n).le (ledgerKappa_pos n)
  have := ledgerK_pos n
  have := ledgerC1_pos n
  unfold engC2
  positivity

theorem engC3_nonneg (hn : 1 ≤ n) : 0 ≤ engC3 n := by
  have := packConst_nonneg (n := n) (ledgerRho_pos hn) (ledgerRho_lt_one n).le
  have := ledgerKappa_pos n
  have := ledgerRho_pos hn
  unfold engC3 excessConst
  positivity

theorem one_add_ledgerRho_le_ledgerKappa (n : ℕ) : 1 + ledgerRho n ≤ ledgerKappa n := by
  unfold ledgerKappa
  rw [le_div_iff₀ (one_sub_ledgerRho_pos n)]
  nlinarith [sq_nonneg (ledgerRho n)]

/-! ### The data of the inductive step -/

/-- The situation of the inductive step for Claim(j) at the center `p`: a
reduced family satisfying (1.3) with constant `J`, the lower bounds on `M` required by the proof,
Claim(l) for every `l > j`, and a good top ball. -/
structure StepData (n : ℕ) (Z : Finset (Rn n)) (lev : Rn n → ℕ) (J M : ℝ) (p : Rn n) (j : ℕ) :
    Prop where
  two_le_n : 2 ≤ n
  red : IsReducedFamily (ledgerRho n) Z lev
  J_nonneg : 0 ≤ J
  beta : BetaHyp (levMeasure (ledgerRho n) Z lev) J
  M_tau : unitBallVolume (n - 1) ≤ ledgerTau n * M
  M_rho : unitBallVolume (n - 1) ≤ M * ledgerRho n ^ (n - 1)
  J_small : J ≤ engEps n * (ledgerK n * ledgerTau n * M ^ 2)
  p_mem : p ∈ Z
  one_le_j : 1 ≤ j
  lev_p : j < lev p
  claim : ∀ l, j < l → ClaimAt (ledgerRho n) M Z lev l
  top : ENNReal.ofReal (ledgerTau n * M * (ledgerRho n ^ j) ^ (n - 1)) ≤
    levMeasure (ledgerRho n) Z lev (ball p (ledgerRho n ^ j))

/-- The covering run of the step: `CoverData.ofFamily ρ κ (τ M) Z lev p j`. -/
def stepCover (Z : Finset (Rn n)) (lev : Rn n → ℕ) (M : ℝ) (p : Rn n) (j : ℕ) : CoverData n :=
  CoverData.ofFamily (ledgerRho n) (ledgerKappa n) (ledgerTau n * M) Z lev p j

section StepData

variable {Z : Finset (Rn n)} {lev : Rn n → ℕ} {J M : ℝ} {p : Rn n} {j : ℕ}

@[simp] theorem stepCover_μ : (stepCover Z lev M p j).μ = levMeasure (ledgerRho n) Z lev := rfl
@[simp] theorem stepCover_ρ : (stepCover Z lev M p j).ρ = ledgerRho n := rfl
@[simp] theorem stepCover_θ : (stepCover Z lev M p j).θ = ledgerTau n * M := rfl
@[simp] theorem stepCover_p : (stepCover Z lev M p j).p = p := rfl
@[simp] theorem stepCover_j : (stepCover Z lev M p j).j = j := rfl
@[simp] theorem stepCover_P :
    (stepCover Z lev M p j).P = (Z : Set (Rn n)) ∩ ball p (ledgerRho n ^ j) := rfl
theorem stepCover_V (i : ℕ) (y : Rn n) : (stepCover Z lev M p j).V i y =
    bestPlane (levMeasure (ledgerRho n) Z lev) y (ledgerKappa n * ledgerRho n ^ i) := rfl
@[simp] theorem stepCover_lev (z : Rn n) : (stepCover Z lev M p j).lev z = (lev z : ℕ∞) := rfl
@[simp] theorem stepCover_good_top : (stepCover Z lev M p j).good j = {p} :=
  CoverData.good_top _

/-- The atomic measure is finite on every set. -/
theorem levMeasure_ne_top (ρ : ℝ) (Z : Finset (Rn n)) (lev : Rn n → ℕ) (A : Set (Rn n)) :
    levMeasure ρ Z lev A ≠ ∞ := by
  classical
  rw [levMeasure_apply]
  exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top

/-- An atom of level `l` carries all the mass of its own ball: `μ(B_{ρ^l}(y)) ≤ ω_k ρ^{lk}`. -/
theorem levMeasure_ball_self_le {ρ : ℝ} (hρ0 : 0 < ρ) (hred : IsReducedFamily ρ Z lev) {y : Rn n}
    (hy : y ∈ Z) :
    levMeasure ρ Z lev (ball y (ρ ^ lev y)) ≤
      ENNReal.ofReal (unitBallVolume (n - 1) * (ρ ^ lev y) ^ (n - 1)) := by
  classical
  rw [levMeasure_apply]
  have hF : (Z.filter fun z => z ∈ ball y (ρ ^ lev y)) ⊆ {y} := by
    intro z hz
    obtain ⟨hzZ, hzb⟩ := Finset.mem_filter.1 hz
    rw [Finset.mem_singleton]
    by_contra hne
    have := add_le_dist_of_disjoint hρ0 hred.disjoint hzZ hy hne
    have := pow_pos hρ0 (lev z)
    rw [mem_ball] at hzb
    linarith
  refine (Finset.sum_le_sum_of_subset hF).trans ?_
  rw [Finset.sum_singleton]

variable (h : StepData n Z lev J M p j)
include h

theorem StepData.one_le_n : 1 ≤ n := le_trans (by norm_num) h.two_le_n

theorem StepData.ρ_pos : 0 < ledgerRho n := ledgerRho_pos h.one_le_n

theorem StepData.M_pos : 0 < M := by
  have hω := unitBallVolume_pos (n - 1)
  have hτ := ledgerTau_pos n
  have := hω.trans_le h.M_tau
  by_contra hM
  have : ledgerTau n * M ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ.le (not_lt.1 hM)
  linarith

theorem StepData.θ_pos : 0 < ledgerTau n * M := mul_pos (ledgerTau_pos n) h.M_pos

theorem StepData.hyp : (stepCover Z lev M p j).Hyp :=
  CoverData.ofFamily_hyp h.ρ_pos (ledgerRho_lt_one n).le h.red.disjoint h.p_mem h.lev_p

theorem StepData.estHyp : (stepCover Z lev M p j).EstHyp (ledgerKappa n) J where
  hyp := h.hyp
  one_le_n := h.one_le_n
  θ_pos := h.θ_pos
  ρ_le := ledgerRho_le_hundredth n
  fin := fun x r => levMeasure_ne_top _ _ _ _
  top := h.top
  one_le_κ := one_le_ledgerKappa h.one_le_n
  κ_le := (ledgerKappa_le n).trans (by norm_num)
  V_eq := fun _ _ => rfl
  beta := h.beta.locBetaHyp (ball_subset_ball' (by
    have hp := mem_ball.1 (h.red.mem_ball p h.p_mem)
    have h1 : ledgerRho n ^ j ≤ 1 / 100 :=
      (pow_le_pow_of_le_one h.ρ_pos.le (ledgerRho_lt_one n).le h.one_le_j).trans
        (by rw [pow_one]; exact ledgerRho_le_hundredth n)
    simp only [stepCover_ρ, stepCover_p, stepCover_j, ledgerR0]
    linarith))
  J_nonneg := h.J_nonneg

/-- Good centers are atoms of level `> i`. -/
theorem StepData.mem_Z_of_mem_good {i : ℕ} (hi : j ≤ i) {z : Rn n}
    (hz : z ∈ (stepCover Z lev M p j).good i) : z ∈ Z ∧ i < lev z := by
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [stepCover_good_top, Finset.mem_singleton] at hz
    subst hz
    exact ⟨h.p_mem, h.lev_p⟩
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hP := CoverData.mem_P_of_mem_succ h.hyp (i := i') (by simp; omega)
      (Finset.mem_union_left _ (Finset.mem_union_left _ hz))
    have hlev := CoverData.lev_of_mem_good_succ (i := i') (by simp; omega) hz
    simp only [stepCover_lev, Nat.cast_lt] at hlev
    exact ⟨hP.1, hlev⟩

/-- The upper-bound lemma `levMeasure_ball_mul_le_of_claimAt_succ` in the form of hypothesis
(H2) of the tilt lemma `planeDist_sq_le_of_mass`, at a good center of scale `i ≥ j`. -/
theorem StepData.hup {i : ℕ} (hi : j ≤ i) {z : Rn n}
    (hz : z ∈ (stepCover Z lev M p j).good i) :
    ∀ w ∈ ball z (ledgerRho n ^ i), levMeasure (ledgerRho n) Z lev
        (ball w (ledgerRho n * ledgerRho n ^ i)) ≤
      ENNReal.ofReal (ledgerK n * M * (ledgerRho n * ledgerRho n ^ i) ^ (n - 1)) := by
  obtain ⟨hzZ, hlt⟩ := h.mem_Z_of_mem_good hi hz
  exact levMeasure_ball_mul_le_of_claimAt_succ h.ρ_pos (ledgerRho_le_half n) h.red.disjoint
    h.M_rho (h.claim (i + 1) (by omega)) hzZ hlt

/-- The discrete run satisfies the engine hypotheses, with `κ = ledgerKappa n`, `Λ = K M` and the
threshold `θ = τ M`. -/
theorem StepData.engineHyp :
    (stepCover Z lev M p j).EngineHyp (ledgerKappa n) (ledgerK n * M) J where
  est := h.estHyp
  two_le_n := h.two_le_n
  one_add_ρ_le_κ := one_add_ledgerRho_le_ledgerKappa n
  Λ_pos := mul_pos (ledgerK_pos n) h.M_pos
  tilt_mass := ledgerRho_le_tilt_mass h.M_pos
  hup := fun _ hi _ hz => h.hup hi hz
  J_small := by
    have hJ := h.J_small
    have hK := (ledgerK_pos n).ne'
    simp only [stepCover_ρ, stepCover_θ]
    refine hJ.trans (le_of_eq ?_)
    unfold engEps
    field_simp
  fin_le := by
    intro l hl y hy
    obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
    have hlev := CoverData.lev_of_mem_fin_succ h.hyp (i := i) (by simp at hl ⊢; omega) hy
    have hyZ := (CoverData.mem_P_of_mem_succ h.hyp (i := i) (by simp at hl ⊢; omega)
      (Finset.mem_union_right _ hy)).1
    simp only [stepCover_lev, Nat.cast_inj] at hlev
    simp only [stepCover_μ, stepCover_ρ, stepCover_θ]
    have := levMeasure_ball_self_le h.ρ_pos h.red hyZ
    rw [hlev] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have := pow_pos (pow_pos h.ρ_pos (i + 1)) (n - 1)
    exact mul_le_mul_of_nonneg_right h.M_tau this.le

omit h in
/-- The real arithmetic of the final bound (Miś §4, "Derivation of the bound"):
`θC₁ ω_k (1+ρ)^k R + θ C₁ C_A J R / θ² + C₃ J R / θ ≤ M R` for `θ = τM`. -/
private lemma final_arith (hn : 1 ≤ n) {M J R : ℝ} (hM : 0 < M) (hR : 0 < R)
    (hC2 : engC2 n * J ≤ ledgerK n * ledgerTau n * M ^ 2)
    (hC3 : 2 * engC3 n * J ≤ ledgerTau n * M ^ 2) :
    ledgerTau n * M * ledgerC1 n * (unitBallVolume (n - 1) * ((1 + ledgerRho n) ^ (n - 1) * R)) +
        ledgerTau n * M * ledgerC1 n *
          (areaConst n (ledgerRho n) (ledgerKappa n) * J * R / (ledgerTau n * M) ^ 2) +
      excessConst n (ledgerRho n) (ledgerKappa n) * J * R / (ledgerTau n * M) ≤ M * R := by
  have hτ := ledgerTau_pos n
  have hK := ledgerK_pos n
  have hC1 := ledgerC1_pos n
  have hA := areaConst_nonneg (n := n) (ledgerRho_pos hn) (ledgerRho_lt_one n).le
    (ledgerKappa_pos n)
  have hωCτ := omega_mul_ledgerC1_mul_ledgerTau n
  have h2 := one_add_ledgerRho_pow_le_two hn
  have hθ : 0 < ledgerTau n * M := mul_pos hτ hM
  -- term 1
  have t1 : ledgerTau n * M * ledgerC1 n *
      (unitBallVolume (n - 1) * ((1 + ledgerRho n) ^ (n - 1) * R)) ≤ M * R / 4 := by
    have e : ledgerTau n * M * ledgerC1 n *
        (unitBallVolume (n - 1) * ((1 + ledgerRho n) ^ (n - 1) * R)) =
        (unitBallVolume (n - 1) * ledgerC1 n * ledgerTau n) * (M * R) *
          (1 + ledgerRho n) ^ (n - 1) := by ring
    rw [e, hωCτ]
    have : 0 < M * R := mul_pos hM hR
    nlinarith
  -- term 2
  have t2 : ledgerTau n * M * ledgerC1 n *
      (areaConst n (ledgerRho n) (ledgerKappa n) * J * R / (ledgerTau n * M) ^ 2) ≤ M * R / 4 := by
    have e : ledgerTau n * M * ledgerC1 n *
        (areaConst n (ledgerRho n) (ledgerKappa n) * J * R / (ledgerTau n * M) ^ 2) =
        ledgerC1 n * areaConst n (ledgerRho n) (ledgerKappa n) * J * R / (ledgerTau n * M) := by
      field_simp
    rw [e, div_le_iff₀ hθ]
    have : 4 * (ledgerC1 n * areaConst n (ledgerRho n) (ledgerKappa n) * J) ≤
        ledgerTau n * M ^ 2 := by
      have e2 : engC2 n * J = ledgerK n * (4 * (ledgerC1 n *
          areaConst n (ledgerRho n) (ledgerKappa n) * J)) := by unfold engC2; ring
      have h' : ledgerK n * (4 * (ledgerC1 n * areaConst n (ledgerRho n) (ledgerKappa n) * J)) ≤
          ledgerK n * (ledgerTau n * M ^ 2) := by
        rw [← e2]; linarith
      exact le_of_mul_le_mul_left h' hK
    nlinarith
  -- term 3
  have t3 : excessConst n (ledgerRho n) (ledgerKappa n) * J * R / (ledgerTau n * M) ≤
      M * R / 2 := by
    rw [div_le_iff₀ hθ]
    unfold engC3 at hC3
    nlinarith
  linarith

/-- **The final bound of the step** (Miś §4, "Derivation of the bound"):
`μ(B_{r_j}(p)) ≤ M r_j^k`. -/
theorem StepData.claim_le (hC2 : engC2 n * J ≤ ledgerK n * ledgerTau n * M ^ 2)
    (hC3 : 2 * engC3 n * J ≤ ledgerTau n * M ^ 2) :
    levMeasure (ledgerRho n) Z lev (ball p (ledgerRho n ^ j)) ≤
      ENNReal.ofReal (M * (ledgerRho n ^ j) ^ (n - 1)) := by
  classical
  set D := stepCover Z lev M p j
  have hE := h.engineHyp
  set N := max (j + 1) (Z.sup lev)
  have hjN : j < N := lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_left _ _)
  have hgood : D.good N = ∅ := by
    refine CoverData.good_eq_empty h.hyp (by simpa using hjN) fun x hx => ?_
    have : lev x ≤ N := (Finset.le_sup hx.1).trans (le_max_right _ _)
    simpa using this
  have hmass := hE.engine_mass (N := N) (by simpa using hjN.le)
  rw [hgood] at hmass
  simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, measure_empty, add_zero]
    at hmass
  have hP : levMeasure (ledgerRho n) Z lev (ball p (ledgerRho n ^ j)) ≤ D.μ D.P :=
    atomMeasure_mono_of_atoms (S := Z) (x := id) fun z hz hzb => ⟨hz, hzb⟩
  have harea := hE.hausdorffN_surf_le' (N := N) (by simpa using hjN.le)
  have hexc := CoverData.measure_biUnion_excess_le h.estHyp N
  have hρ0 := h.ρ_pos
  have hM := h.M_pos
  have hJ := h.J_nonneg
  have hR : 0 < (ledgerRho n ^ j) ^ (n - 1) := pow_pos (pow_pos hρ0 j) _
  have hθ : 0 < ledgerTau n * M := h.θ_pos
  have hC1 := ledgerC1_pos n
  have hω := unitBallVolume_pos (n - 1)
  have hA := areaConst_nonneg (n := n) hρ0 (ledgerRho_lt_one n).le (ledgerKappa_pos n)
  have hX := packConst_nonneg (n := n) hρ0 (ledgerRho_lt_one n).le
  have hexc0 : 0 ≤ excessConst n (ledgerRho n) (ledgerKappa n) := by
    have := ledgerKappa_pos n; unfold excessConst; positivity
  refine hP.trans (hmass.trans ((add_le_add (mul_le_mul_right harea _) hexc).trans ?_))
  simp only [stepCover_ρ, stepCover_θ, stepCover_j]
  set a := unitBallVolume (n - 1) * ((1 + ledgerRho n) * ledgerRho n ^ j) ^ (n - 1)
  set b := areaConst n (ledgerRho n) (ledgerKappa n) * J * (ledgerRho n ^ j) ^ (n - 1) /
    (ledgerTau n * M) ^ 2
  set c := excessConst n (ledgerRho n) (ledgerKappa n) * J * (ledgerRho n ^ j) ^ (n - 1) /
    (ledgerTau n * M)
  set t := ledgerTau n * M * ledgerC1 n
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hc : 0 ≤ c := by positivity
  have ht : 0 ≤ t := by positivity
  rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_mul ht,
    ← ENNReal.ofReal_add (by positivity) hc]
  refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans
    (final_arith h.one_le_n hM hR hC2 hC3))
  simp only [a, b, c, t]
  rw [mul_pow]
  ring

end StepData

/-! ### Claim 4.1: the downward induction -/

/-- The mass constant `M(J) = ledgerMass` with the engine constants of the discrete run. -/
abbrev discreteMass (n : ℕ) (J : ℝ) : ℝ := ledgerMass n (engC2 n) (engC3 n) (engEps n) J

/-- **Claim 4.1** (centered form, `ClaimAt`): for a reduced family satisfying (1.3) with constant
`J`, Claim(j) holds for every `j ≥ 1` with `M = M(J)`. Downward induction from the top level
`A = sup lev` (reduction R3, `claimAt_of_sup_le`), each step by `StepData.claim_le`. -/
theorem claimAt_of_reduced (hn : 2 ≤ n) {J : ℝ} (hJ : 0 ≤ J) {Z : Finset (Rn n)}
    {lev : Rn n → ℕ} (hred : IsReducedFamily (ledgerRho n) Z lev)
    (hbeta : BetaHyp (levMeasure (ledgerRho n) Z lev) J) :
    ∀ j, 1 ≤ j → ClaimAt (ledgerRho n) (discreteMass n J) Z lev j := by
  have hn1 : 1 ≤ n := by omega
  set M := discreteMass n J
  have hM : 0 < M := ledgerMass_pos
  suffices H : ∀ d j, 1 ≤ j → Z.sup lev ≤ j + d → ClaimAt (ledgerRho n) M Z lev j from
    fun j hj => H (Z.sup lev) j hj (by omega)
  intro d
  induction d with
  | zero => exact fun j _ hA => claimAt_of_sup_le hA
  | succ d ih =>
    intro j hj hA p hp hlev
    by_cases htop : ENNReal.ofReal (ledgerTau n * M * (ledgerRho n ^ j) ^ (n - 1)) ≤
        levMeasure (ledgerRho n) Z lev (ball p (ledgerRho n ^ j))
    · have hS : StepData n Z lev J M p j :=
        { two_le_n := hn
          red := hred
          J_nonneg := hJ
          beta := hbeta
          M_tau := omega_le_ledgerTau_mul_ledgerMass
          M_rho := omega_le_ledgerMass_mul_rho_pow hn1
          J_small := J_le_eps_mul_ledgerMass (engEps_pos hn1)
          p_mem := hp
          one_le_j := hj
          lev_p := hlev
          claim := fun l hl => ih l (by omega) (by omega)
          top := htop }
      exact hS.claim_le C₂_mul_le_ledgerMass C₃_mul_le_ledgerMass
    · refine (not_le.1 htop).le.trans (ENNReal.ofReal_le_ofReal ?_)
      have hR := pow_pos (pow_pos (ledgerRho_pos hn1) j) (n - 1)
      have := ledgerTau_le_one n
      have hMR := mul_pos hM hR
      nlinarith

/-- **Claim(1)** for all reduced families (`ClaimOneStatement`), with
`M(J) = ledgerMass n (engC2 n) (engC3 n) (engEps n) J`. -/
theorem claimOne (hn : 2 ≤ n) :
    ClaimOneStatement n (ledgerRho n) (ledgerMass n (engC2 n) (engC3 n) (engEps n)) :=
  fun _ hJ _ _ hred hbeta => claimAt_of_reduced hn hJ hred hbeta 1 le_rfl

end DiscreteReifenberg

variable {n : ℕ}

/-- **Discrete Reifenberg theorem** (NV Thm 3.4 for hyperplanes; proved as Miś Thm 1.1 with
`q = 2`): Claim 4.1 by downward induction (`DiscreteReifenberg.claimOne`), then the reductions
R1–R6 of `Reductions.lean` and the statement bridge
(`DiscreteReifenberg.discreteReifenbergStatement_of_claimOne`), with `δ = 1` and
`D = ledgerD n C₂ C₃ ε`. -/
theorem discrete_reifenberg : DiscreteReifenbergStatement n := by
  intro hn
  have hn1 : 1 ≤ n := by omega
  exact DiscreteReifenberg.discreteReifenbergStatement_of_claimOne
    (DiscreteReifenberg.engC2_nonneg hn1) (DiscreteReifenberg.engC3_nonneg hn1)
    (DiscreteReifenberg.engEps_pos hn1) (fun _ => DiscreteReifenberg.claimOne hn) hn

end GMTFoundations
