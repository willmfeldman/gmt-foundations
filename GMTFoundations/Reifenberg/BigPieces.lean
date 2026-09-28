/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.StoppingTime
public import GMTFoundations.Reifenberg.LimitMap
import GMTFoundations.Reifenberg.Exhaustion
import Mathlib.Algebra.Order.Ring.Star

/-!
# Big pieces of Lipschitz images (Step C)

The core of the rectifiable-Reifenberg theorem (`Rectifiable.lean`, Steps A–C there), in the
rescaled frame of `Exhaustion.lean` (top ball `B₁(0)`). It replaces the rectifiability argument of
A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and minimizing
harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043 (NV), §5.9, which goes through
`W^{1,p}` maps and NV Lemmas 2.19 and 2.20; here the conclusion is a single Lipschitz image. The
construction is the one of M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci.
Fenn. Math. 43 (2018); arXiv:1612.02461 (Miś), §4, run on the continuous measure.

* `bigPieceMass n = ω_{n-1}/2^n` (the mass threshold `η`) on `B₁(0)`.
  It is below the density threshold `ω_{n-1}/2^{n-1}` of the upper-density lemma
  (`bigPieceMass_lt`), so Step A supplies balls with this much mass.
* `exists_bigPiece` (**Step C**): for every `C` there is `δ = δ(n, C) > 0` such that a finite
  measure `μ` with the upper bound `μ(B_s(y)) ≤ C s^{n-1}` on all balls, the square-function bound
  `∫_{B_s(y)} ∫_0^s β²_μ(z,t) dt/t dμ(z) ≤ δ² s^{n-1}` on every ball `B_s(y) ⊆ B_{R₀}(0)`
  (`R₀ = 16 = ledgerR0`, the region where the construction uses the hypothesis) and mass
  `μ(B₁(0)) > ω_{n-1}/2^n` charges the range of a Lipschitz map `ℝ^{n-1} → ℝⁿ`.

**Proof** (with the stopping function of `StoppingTime.lean`). Run the Reifenberg construction of
the discrete Reifenberg theorem on the continuous measure `μ` (`CoverData.ofMeasure`: `lev ≡ ⊤`, top
ball `B₁(0)`, threshold `θ`, planes `bestPlane μ y (κ ρ^i)`), with the constants below; there is no
discretization. The removed region `⋃_N R_{≤N}` carries mass `≤ η/4 + η/8 + η/8` (Miś (4.1)–(4.3),
uniformly in `N`), and the stopped set `{A > 1}` mass `≤ η/8` (Markov). On the rest,
`G = G_∞ ∩ {A ≤ 1}`, every point is `φ_∞(u)` with `u ∈ T₀` (`exists_limitMap_eq`), and `φ_∞` is
`(5/4)e`-Lipschitz on these preimages (Lemma L, `dist_limitMap_le_of_stopFun`). McShane
(`LipschitzOnWith.extend_finite_dimension`) and a linear isometry `ℝ^{n-1} ≅ T₀ − p` give the
Lipschitz `F` with `range F ⊇ G`, and `μ(G) ≥ μ(B₁) − 5η/8 > 0`.

## Constants

With `k = n − 1`, `ω = ω_k`, `η = bigPieceMass n = ω/2^n`:
* `θ = bigPieceTheta n = η/(16·15^k)` (so `θ C₁ ω (1+ρ)^k ≤ 4·15^k θ = η/4`, `C₁ = ledgerC1 n`);
* `Λ = max C 1`;
* `ρ = bigPieceRho n C = min(1/100, θ/(2 A_n Λ), 1/(2n))` (`A_n = farConst n`; the condition of the
  tilt lemma `planeDist_sq_le_of_mass`, the construction's `ρ ≤ 1/100`, and `(1+ρ)^k ≤ 2`);
* `κ = 1 + ρ`;
* `J = δ² = bigPieceJ n C = min(ε_eng θ², η θ²/(8 K))` with `ε_eng = smallEps n ρ κ` and
  `K = θ C₁ C_A + C₃ θ + Λ 6^k C_S + 1` (`C_A = areaConst`, `C₃ = excessConst`,
  `C_S = stopConst`), so that each of the three `J`-terms is `≤ η/8`;
* `δ = bigPieceDelta n C = √J`; the stopping level is `a = 1` and the Lipschitz constant of
  Lemma L is `(5/4)e`.

The threshold `θ` plays the role of NV's `γ_k`. With NV's value `γ_k = ω_k 40^{-k}` the numerical
inequality (5.114)–(5.115) fails for small `k` (at `k = 1`, `2^{-k-1} − 4^{-k} < 2^{-k-2}`); the
smaller threshold here avoids this.

## References

* [NV] A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and
  minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043, §5.
* [Miś] M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018);
  arXiv:1612.02461, §4.
-/

public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace GMTFoundations

open DiscreteReifenberg

variable {n : ℕ}

/-- The mass threshold `η = ω_{n-1}/2^n` of Step C on `B₁(0)`. -/
@[expose] def bigPieceMass (n : ℕ) : ℝ := unitBallVolume (n - 1) / 2 ^ n

theorem bigPieceMass_pos (n : ℕ) : 0 < bigPieceMass n :=
  div_pos (unitBallVolume_pos _) (pow_pos two_pos _)

/-- `η = ω_k/2^{k+1} < ω_k/2^k` (`k = n − 1`): Step A's threshold exceeds Step C's. -/
theorem bigPieceMass_lt (hn : 1 ≤ n) : bigPieceMass n < unitBallVolume (n - 1) / 2 ^ (n - 1) := by
  have hω := unitBallVolume_pos (n - 1)
  unfold bigPieceMass
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Nat.add_sub_cancel, pow_succ]
  exact div_lt_div_of_pos_left hω (pow_pos two_pos k) (by linarith [pow_pos (two_pos (α := ℝ)) k])

/-- The threshold `θ = η/(16·15^k)` (the analogue of NV's `γ_k`). -/
def bigPieceTheta (n : ℕ) : ℝ := bigPieceMass n / (16 * 15 ^ (n - 1))

/-- The scale ratio `ρ = min(1/100, θ/(2 A_n Λ), 1/(2n))`, `Λ = max C 1`. -/
def bigPieceRho (n : ℕ) (C : ℝ) : ℝ :=
  min (1 / 100) (min (bigPieceTheta n / (2 * farConst n * max C 1)) (1 / (2 * n)))

/-- The coefficient `K = θ C₁ C_A + C₃ θ + Λ 6^k C_S + 1` of `J/θ²` in the losses. -/
def bigPieceK (n : ℕ) (C : ℝ) : ℝ :=
  bigPieceTheta n * ledgerC1 n * CoverData.areaConst n (bigPieceRho n C) (1 + bigPieceRho n C) +
    CoverData.excessConst n (bigPieceRho n C) (1 + bigPieceRho n C) * bigPieceTheta n +
    max C 1 * 6 ^ (n - 1) * CoverData.stopConst n (bigPieceRho n C) (1 + bigPieceRho n C) + 1

/-- The square-function bound `J = δ² = min(ε_eng θ², η θ²/(8K))`. -/
def bigPieceJ (n : ℕ) (C : ℝ) : ℝ :=
  min (smallEps n (bigPieceRho n C) (1 + bigPieceRho n C) * bigPieceTheta n ^ 2)
    (bigPieceMass n * bigPieceTheta n ^ 2 / (8 * bigPieceK n C))

/-- The constant `δ = √J`. -/
def bigPieceDelta (n : ℕ) (C : ℝ) : ℝ := Real.sqrt (bigPieceJ n C)

/-- **Step C: big pieces of Lipschitz images** (the analogue of the rectifiability part of NV
§5.9). For every `C` there is `δ = δ(n, C) > 0` with the following property. Let `μ` be a finite
measure on `ℝⁿ` with
* (U) `μ(B_s(y)) ≤ C s^{n-1}` for every ball;
* (Q) `∫_{B_s(y)} ∫_0^s β²_μ(z, t) dt/t dμ(z) ≤ δ² s^{n-1}` for every ball `B_s(y) ⊆ B_{16}(0)`;
* (M) `μ(B₁(0)) > ω_{n-1}/2^n`.

Then some Lipschitz `F : ℝ^{n-1} → ℝⁿ` has `μ(range F) ≠ 0` (the proof gives
`μ(range F) ≥ μ(B₁(0)) − 5η/8`). `δ = bigPieceDelta n C`. -/
theorem exists_bigPiece (hn : 2 ≤ n) (C : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : Measure (Rn n), IsFiniteMeasure μ →
      (∀ (x : Rn n) (r : ℝ), 0 < r → μ (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) →
      (∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball 0 ledgerR0 →
        ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s, jonesBetaSq μ z t / ENNReal.ofReal t) ∂μ ≤
          ENNReal.ofReal (δ ^ 2 * s ^ (n - 1))) →
      ENNReal.ofReal (bigPieceMass n) < μ (ball 0 1) →
      ∃ F : Rn (n - 1) → Rn n, (∃ L, LipschitzWith L F) ∧ μ (range F) ≠ 0 := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  -- the constants
  set η := bigPieceMass n with hη_def
  set θ := bigPieceTheta n with hθ_def
  set Λ := max C 1 with hΛ_def
  set ρ := bigPieceRho n C with hρ_def
  set κ := 1 + ρ with hκ_def
  set K := bigPieceK n C with hK_def
  set J := bigPieceJ n C with hJ_def
  have hη : 0 < η := bigPieceMass_pos n
  have hθ : 0 < θ := by rw [hθ_def, bigPieceTheta]; positivity
  have hθη : θ ≤ η := by
    rw [hθ_def, bigPieceTheta, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ 15 ^ (n - 1) := one_le_pow₀ (by norm_num)
    rw [← hη_def]
    linarith [mul_le_mul_of_nonneg_left this hη.le]
  have hΛ : 0 < Λ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCΛ : C ≤ Λ := le_max_left _ _
  have hA := farConst_pos n
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hρ0 : 0 < ρ := by
    rw [hρ_def, bigPieceRho]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hρ : ρ ≤ 1 / 100 := by rw [hρ_def, bigPieceRho]; exact min_le_left _ _
  have htilt : ρ ≤ θ / (2 * farConst n * Λ) := by
    rw [hρ_def, bigPieceRho]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hρn : ρ ≤ 1 / (2 * n) := by
    rw [hρ_def, bigPieceRho]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hκ0 : 0 < κ := by rw [hκ_def]; linarith
  have hρ1 : ρ ≤ 1 := hρ.trans (by norm_num)
  have hAC := CoverData.areaConst_nonneg (n := n) hρ0 hρ1 hκ0
  have hEC : 0 ≤ CoverData.excessConst n ρ κ := by
    have := CoverData.packConst_nonneg (n := n) hρ0 hρ1
    unfold CoverData.excessConst; positivity
  have hSC := CoverData.stopConst_nonneg (n := n) hρ0 hρ1 hκ0
  have hC1 := ledgerC1_pos n
  have hKs : 0 ≤ Λ * 6 ^ (n - 1) * CoverData.stopConst n ρ κ := by positivity
  have hKa : 0 ≤ θ * ledgerC1 n * CoverData.areaConst n ρ κ := by positivity
  have hKe : 0 ≤ CoverData.excessConst n ρ κ * θ := by positivity
  have hKdef : K = θ * ledgerC1 n * CoverData.areaConst n ρ κ +
      CoverData.excessConst n ρ κ * θ + Λ * 6 ^ (n - 1) * CoverData.stopConst n ρ κ + 1 := rfl
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    linarith
  have hJ0 : 0 < J := by
    rw [hJ_def, bigPieceJ]
    exact lt_min (mul_pos (smallEps_pos hn1 hρ0 hκ0) (by positivity)) (by positivity)
  have hJsmall : J ≤ smallEps n ρ κ * θ ^ 2 := by rw [hJ_def, bigPieceJ]; exact min_le_left _ _
  have hJK : K * J / θ ^ 2 ≤ η / 8 := by
    have h1 : J ≤ η * θ ^ 2 / (8 * K) := by rw [hJ_def, bigPieceJ]; exact min_le_right _ _
    rw [div_le_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  refine ⟨bigPieceDelta n C, Real.sqrt_pos.2 hJ0, fun μ hμ hU hQ hM => ?_⟩
  have hδ : bigPieceDelta n C ^ 2 = J := Real.sq_sqrt hJ0.le
  simp_rw [hδ] at hQ
  -- the engine run
  have hUΛ : ∀ (x : Rn n) (r : ℝ), 0 < r → μ (ball x r) ≤ ENNReal.ofReal (Λ * r ^ (n - 1)) :=
    fun x r hr => (hU x r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCΛ (by positivity)))
  have htop : ENNReal.ofReal θ ≤ μ (ball 0 1) :=
    (ENNReal.ofReal_le_ofReal hθη).trans hM.le
  set D := CoverData.ofMeasure μ ρ κ θ with hD_def
  have hE : D.EngineHyp κ Λ J :=
    CoverData.ofMeasure_engineHyp hn hρ0 hρ rfl hθ htop hΛ htilt hUΛ hQ hJ0.le hJsmall
  have hS : D.SurfHyp := hE.surfHyp
  have hj : D.j = 0 := rfl
  -- the losses
  have hrem := CoverData.measure_iUnion_rem_le hE hj
  have hint := CoverData.lintegral_stopFun_le hE hj hUΛ
  have hmark := CoverData.measure_stopFun_lt_le (D := D) one_pos
  have eρ : D.ρ = ρ := rfl
  have eθ : D.θ = θ := rfl
  rw [eρ, eθ] at hrem hint
  set G := D.goodLimit ∩ {x | D.stopFun x ≤ ENNReal.ofReal 1} with hG_def
  have hcov : ball (0 : Rn n) 1 ⊆
      (⋃ N, D.rem N) ∪ {x | ENNReal.ofReal 1 < D.stopFun x} ∪ G := by
    intro x hx
    by_cases hr : x ∈ ⋃ N, D.rem N
    · exact Or.inl (Or.inl hr)
    · by_cases hA : D.stopFun x ≤ ENNReal.ofReal 1
      · exact Or.inr ⟨⟨hx, hr⟩, hA⟩
      · exact Or.inl (Or.inr (not_le.1 hA))
  -- the arithmetic of the losses
  have hk2 : (1 + ρ) ^ (n - 1) ≤ 2 := by
    have hm : 2 * ((n - 1 : ℕ) : ℝ) * ρ ≤ 1 := by
      have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      rw [le_div_iff₀ (by positivity)] at hρn
      linarith [mul_le_mul_of_nonneg_right this hρ0.le]
    have := one_add_pow_le hρ0.le hm
    linarith
  have hbad : θ * ledgerC1 n * (unitBallVolume (n - 1) * (1 + ρ) ^ (n - 1)) ≤ η / 4 := by
    have hω := unitBallVolume_pos (n - 1)
    have e : θ * ledgerC1 n * (unitBallVolume (n - 1) * (1 + ρ) ^ (n - 1)) =
        2 * 15 ^ (n - 1) * θ * (1 + ρ) ^ (n - 1) := by
      unfold ledgerC1; field_simp
    have e2 : 2 * 15 ^ (n - 1) * θ * 2 = η / 4 := by
      rw [hθ_def, bigPieceTheta]; field_simp; ring
    rw [e, ← e2]
    have : (0 : ℝ) ≤ 2 * 15 ^ (n - 1) * θ := by positivity
    exact mul_le_mul_of_nonneg_left hk2 this
  have hK_A : θ * ledgerC1 n * (CoverData.areaConst n ρ κ * J / θ ^ 2) ≤ η / 8 := by
    have e : θ * ledgerC1 n * (CoverData.areaConst n ρ κ * J / θ ^ 2) =
        θ * ledgerC1 n * CoverData.areaConst n ρ κ * J / θ ^ 2 := by ring
    rw [e]
    refine le_trans ?_ hJK
    have : θ * ledgerC1 n * CoverData.areaConst n ρ κ ≤ K := by
      rw [hKdef]
      linarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hJ0.le) (by positivity)
  have hK_E : CoverData.excessConst n ρ κ * J / θ ≤ η / 8 := by
    have e : CoverData.excessConst n ρ κ * J / θ =
        CoverData.excessConst n ρ κ * θ * J / θ ^ 2 := by field_simp
    rw [e]
    refine le_trans ?_ hJK
    have : CoverData.excessConst n ρ κ * θ ≤ K := by
      rw [hKdef]
      linarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hJ0.le) (by positivity)
  have hK_S : Λ * 6 ^ (n - 1) * CoverData.stopConst n ρ κ * J / θ ^ 2 ≤ η / 8 := by
    refine le_trans ?_ hJK
    have : Λ * 6 ^ (n - 1) * CoverData.stopConst n ρ κ ≤ K := by
      rw [hKdef]
      linarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hJ0.le) (by positivity)
  have hloss : D.μ (⋃ N, D.rem N) + D.μ {x | ENNReal.ofReal 1 < D.stopFun x} ≤
      ENNReal.ofReal (5 * η / 8) := by
    have h1 : D.μ (⋃ N, D.rem N) ≤ ENNReal.ofReal (η / 4 + η / 8 + η / 8) := by
      refine hrem.trans ?_
      have hω := unitBallVolume_pos (n - 1)
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      change θ * ledgerC1 n * _ + _ ≤ _
      rw [mul_add]
      linarith
    have h2 : D.μ {x | ENNReal.ofReal 1 < D.stopFun x} ≤ ENNReal.ofReal (η / 8) := by
      refine hmark.trans ?_
      rw [ENNReal.ofReal_one, div_one]
      exact hint.trans (ENNReal.ofReal_le_ofReal hK_S)
    refine (add_le_add h1 h2).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hG : μ G ≠ 0 := by
    intro h0
    have : μ (ball 0 1) ≤ ENNReal.ofReal (5 * η / 8) := by
      refine (measure_mono hcov).trans ((measure_union_le _ _).trans ?_)
      rw [h0, add_zero]
      exact (measure_union_le _ _).trans hloss
    have h58 : ENNReal.ofReal (5 * η / 8) < ENNReal.ofReal η :=
      (ENNReal.ofReal_lt_ofReal_iff hη).2 (by linarith)
    exact absurd (hM.trans_le this) (not_lt.2 h58.le)
  -- Lemma L on the preimages, McShane, and the plane chart
  set Ahat := {u ∈ D.surf 0 | D.stopFun (D.limitMap u) ≤ ENNReal.ofReal 1} with hAhat
  have hLip : LipschitzOnWith (Real.toNNReal (5 / 4 * Real.exp 1)) D.limitMap Ahat := by
    refine LipschitzOnWith.of_dist_le_mul fun u hu u' hu' => ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    exact CoverData.dist_limitMap_le_of_stopFun hS hj hu.1 hu'.1 zero_le_one hu.2
  obtain ⟨Ψ, hΨ, hEq⟩ := hLip.extend_finite_dimension
  set V := D.V 0 0 with hV_def
  have hV : ‖V.2‖ = 1 := hS.unit 0 0
  obtain ⟨L, hL⟩ := exists_linearIsometry_range_eq hn1 (ν := V.2)
    (fun h0 => by rw [h0, norm_zero] at hV; exact zero_ne_one hV)
  have hι : LipschitzWith 1 fun z : Rn (n - 1) => V.1 + L z :=
    LipschitzWith.of_dist_le_mul fun z z' => by
      rw [dist_add_left, L.isometry.dist_eq, NNReal.coe_one, one_mul]
  refine ⟨fun z => Ψ (V.1 + L z), ⟨_, hΨ.comp hι⟩, fun h0 => hG (measure_mono_null ?_ h0)⟩
  rintro x ⟨hxG, hxA⟩
  obtain ⟨u, hu, hux⟩ := CoverData.exists_limitMap_eq hS hj hxG
  have hu' : u - V.1 ∈ range L := by
    rw [hL]
    exact hu
  obtain ⟨z, hz⟩ := hu'
  refine ⟨z, ?_⟩
  change Ψ (V.1 + L z) = x
  rw [hz, add_sub_cancel, ← hEq ⟨hu, by rw [hux]; exact hxA⟩, hux]

end GMTFoundations
