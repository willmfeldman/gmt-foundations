/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.EngineMass
public import GMTFoundations.Reifenberg.Flow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered

/-!
# The limit map of the Reifenberg flow and the mass accounting

The first part of the big-pieces step of the rectifiable-Reifenberg argument (`BigPieces.lean`).
The Reifenberg construction of the discrete Reifenberg theorem (the generic layer `Covering`,
`Estimates`, `Induction`, `EngineMass`) is run directly on a continuous measure, with no
discretization; this plays the role of the maps and manifolds of A. Naber, D. Valtorta,
*Rectifiable-Reifenberg and the regularity of stationary and minimizing harmonic maps*, Ann. of
Math. 185 (2017), 131–227; arXiv:1504.02043 (NV), §5.5 and §5.9.

* `CoverData.ofMeasure μ ρ κ θ`: the covering construction on a measure `μ` with no
  atoms (`lev ≡ ⊤`), all of `B₁(0)` as the center set, planes `V i y = bestPlane μ y (κ ρ^i)`, top
  ball `B₁(0)` (`p = 0`, `j = 0`). `ofMeasure_hyp`, `ofMeasure_fin` (no final balls) and
  `ofMeasure_engineHyp` (`CoverData.EngineHyp`, with the oracle `hup` from the global upper bound).
* The flow `Φ_i = σ_i ∘ ⋯ ∘ σ_1` (`CoverData.flow`) and the limit map `φ_∞ = lim Φ_i`
  (`CoverData.limitMap`): `Φ_i` maps `T₀` onto `T_i` (`surf_eq_image_flow`),
  `|φ_∞ a − Φ_i a| ≤ ρ^{i+1}/9` on `T₀` (`dist_flow_limitMap_le`), and `φ_∞` is continuous on `T₀`
  (`continuousOn_limitMap`, via `continuous_reifenbergMap`).
* Mass accounting: `measure_rem_le` bounds `μ(R_{≤N})` uniformly in `N` by the estimates
  (4.1)–(4.3) of M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43
  (2018); arXiv:1612.02461, §4, and `measure_iUnion_rem_le` passes to `⋃_N R_{≤N}` (continuity
  from below; no measurability).
* `goodLimit` (`G_∞ = B₁ \ ⋃_N R_{≤N}`) and `exists_limitMap_eq`: every
  point of `G_∞` is `φ_∞(a)` for some `a ∈ T₀` (charts at every scale, compactness, continuity).

Everything except `ofMeasure*` is stated for a general run `D` with `D.SurfHyp` and top scale
`D.j = 0` (the mass bounds under `D.EngineHyp`).

## References

* [NV] A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and
  minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043, §5.5, §5.9.
* [Miś] M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018);
  arXiv:1612.02461, §4.
-/

@[expose] public noncomputable section

namespace GMTFoundations.DiscreteReifenberg

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

namespace CoverData

/-! ### The covering construction on a continuous measure -/

/-- The covering construction on a measure `μ`: no atoms (`lev ≡ ⊤`), center set
`B₁(0)`, planes `V i y = bestPlane μ y (κ ρ^i)`, top ball `B₁(0)` (`p = 0`, `j = 0`). -/
def ofMeasure (μ : Measure (Rn n)) (ρ κ θ : ℝ) : CoverData n where
  μ := μ
  ρ := ρ
  θ := θ
  P := ball 0 1
  lev := fun _ => ⊤
  V i y := bestPlane μ y (κ * ρ ^ i)
  p := 0
  j := 0

variable {μ : Measure (Rn n)} {ρ κ θ : ℝ}

theorem ofMeasure_hyp (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) : (ofMeasure μ ρ κ θ).Hyp where
  ρ_pos := hρ0
  ρ_le_one := hρ1
  P_subset := by simp [ofMeasure]
  lev_gt := fun _ _ => by simp [ofMeasure]
  sep := fun _ _ _ _ _ a ha => absurd ha (by simp [ofMeasure])

/-- There are no final balls (`lev ≡ ⊤`). -/
theorem ofMeasure_fin (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (i : ℕ) : (ofMeasure μ ρ κ θ).fin i = ∅ := by
  cases i with
  | zero => exact fin_top _
  | succ i =>
    rw [← Finset.coe_eq_empty, coe_fin_succ (ofMeasure_hyp hρ0 hρ1) (Nat.zero_le i)]
    refine eq_empty_of_forall_notMem fun x hx => ?_
    exact absurd hx.2 (ENat.top_ne_coe (i + 1))

/-- **The engine hypotheses for the continuous instance.** The oracle `hup` is the global upper
bound `μ(B_t(y)) ≤ Λ t^k` on all balls; the square-function hypothesis is required on the balls
contained in `B_{16}(0)`. -/
theorem ofMeasure_engineHyp [IsFiniteMeasure μ] {Λ J : ℝ} (hn : 2 ≤ n) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ 1 / 100) (hκ : κ = 1 + ρ) (hθ : 0 < θ)
    (htop : ENNReal.ofReal θ ≤ μ (ball 0 1)) (hΛ : 0 < Λ)
    (htilt : ρ ≤ θ / (2 * farConst n * Λ))
    (hU : ∀ (x : Rn n) (r : ℝ), 0 < r → μ (ball x r) ≤ ENNReal.ofReal (Λ * r ^ (n - 1)))
    (hQ : ∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball 0 ledgerR0 →
      ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s, jonesBetaSq μ z t / ENNReal.ofReal t) ∂μ ≤
        ENNReal.ofReal (J * s ^ (n - 1)))
    (hJ0 : 0 ≤ J) (hJ : J ≤ smallEps n ρ κ * θ ^ 2) :
    (ofMeasure μ ρ κ θ).EngineHyp κ Λ J where
  est :=
    { hyp := ofMeasure_hyp hρ0 (hρ.trans (by norm_num))
      one_le_n := le_trans (by norm_num) hn
      θ_pos := hθ
      ρ_le := hρ
      fin := fun x r => measure_ne_top μ (ball x r)
      top := by simpa [ofMeasure] using htop
      one_le_κ := by rw [hκ]; linarith
      κ_le := by rw [hκ]; linarith
      V_eq := fun _ _ => rfl
      beta := fun y s hs hys => hQ y s hs (by simpa [ofMeasure] using hys)
      J_nonneg := hJ0 }
  two_le_n := hn
  one_add_ρ_le_κ := hκ.ge
  Λ_pos := hΛ
  tilt_mass := htilt
  hup := fun _ _ _ _ w _ => hU w _ (by
    change 0 < ρ * ρ ^ _
    positivity)
  J_small := hJ
  fin_le := fun l _ y hy => by
    rw [ofMeasure_fin hρ0 (hρ.trans (by norm_num))] at hy
    exact absurd hy (Finset.notMem_empty y)

end CoverData

namespace CoverData

variable {D : CoverData n}

/-! ### Mass accounting -/

/-- The good limit set `G_∞ = P \ ⋃_N R_{≤N}`. -/
def goodLimit (D : CoverData n) : Set (Rn n) := D.P \ ⋃ N, D.rem N

section Mass

variable {κ Λ J : ℝ} (h : D.EngineHyp κ Λ J)
include h

/-- The bad and final balls up to scale `N` carry `μ`-mass at most `θ C₁ ℋ^k(T_N ∩ W_N)` ((4.2) plus
disjointness of the half-balls; the first half of `EngineHyp.engine_mass`). -/
theorem measure_biUnion_badLeaves_le {N : ℕ} (hN : D.j ≤ N) :
    D.μ (⋃ q ∈ D.badLeaves N, ball q.2 (D.ρ ^ q.1)) ≤ ENNReal.ofReal (D.θ * ledgerC1 n) *
      hausdorffN n (n - 1) (D.surf N ∩ ball D.p (D.window N)) := by
  set ν := (hausdorffN n (n - 1)).restrict (D.surf N)
  set L := D.badLeaves N
  have hρ0 := h.ρ_pos
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

omit h in
/-- `R_{≤N}` is covered by the bad and final balls and the excess sets up to scale `N`. -/
theorem rem_subset {N : ℕ} (hN : D.j ≤ N) :
    D.rem N ⊆ (⋃ q ∈ D.badLeaves N, ball q.2 (D.ρ ^ q.1)) ∪
      ⋃ l ∈ Finset.Icc D.j N, D.excessUnion l (D.good l) := by
  intro x hx
  rw [rem_eq hN] at hx
  rcases hx with hx | hx
  · obtain ⟨l, hl, hx⟩ := mem_iUnion₂.1 hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
    have hl' := Finset.mem_Ioc.1 hl
    exact Or.inl (mem_iUnion₂.2 ⟨(l, y), mem_badLeaves.2 ⟨hl'.1, hl'.2, hy⟩, hxy⟩)
  · exact Or.inr hx

/-- **Mass of the removed region** (from (4.1)–(4.3)), uniformly in `N ≥ j`:
`μ(R_{≤N}) ≤ θ C₁ (ω_k((1+ρ) r_j)^k + C_A J r_j^k/θ²) + C₃ J r_j^k/θ`. -/
theorem measure_rem_le {N : ℕ} (hN : D.j ≤ N) :
    D.μ (D.rem N) ≤ ENNReal.ofReal (D.θ * ledgerC1 n) *
        (ENNReal.ofReal (unitBallVolume (n - 1) * ((1 + D.ρ) * D.ρ ^ D.j) ^ (n - 1)) +
          ENNReal.ofReal (areaConst n D.ρ κ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ ^ 2)) +
      ENNReal.ofReal (excessConst n D.ρ κ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ) := by
  refine (measure_mono (rem_subset hN)).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
  · exact (measure_biUnion_badLeaves_le h hN).trans
      (mul_le_mul_right (h.hausdorffN_surf_le' hN) _)
  · exact measure_biUnion_excess_le h.est N

/-- The same bound for `⋃_N R_{≤N}` (continuity from below; `R_{≤N}` is increasing). -/
theorem measure_iUnion_rem_le (hj : D.j = 0) :
    D.μ (⋃ N, D.rem N) ≤ ENNReal.ofReal (D.θ * ledgerC1 n) *
        (ENNReal.ofReal (unitBallVolume (n - 1) * (1 + D.ρ) ^ (n - 1)) +
          ENNReal.ofReal (areaConst n D.ρ κ * J / D.θ ^ 2)) +
      ENNReal.ofReal (excessConst n D.ρ κ * J / D.θ) := by
  have hmono : Monotone D.rem := fun i l hil => rem_mono (by omega) hil
  rw [hmono.measure_iUnion]
  refine iSup_le fun N => ?_
  simpa [hj] using measure_rem_le h (N := N) (by omega)

end Mass

/-! ### Every point of `G_∞` lies on `φ_∞(T₀)` -/

section Surjective

variable (h : D.SurfHyp) (hj : D.j = 0)
include h hj

/-- **A surface point near a point of `G_∞`**: if `x ∈ P` is not removed at scale
`N`, some `q ∈ T_N` has `|q − x| < ρ^{N+1}/3`. -/
theorem exists_surf_near {N : ℕ} {x : Rn n} (hx : x ∈ D.P) (hxN : x ∉ D.rem N) :
    ∃ q ∈ D.surf N, dist q x < D.ρ ^ (N + 1) / 3 := by
  have hN : D.j ≤ N := by omega
  have hρ0 := h.ρ_pos
  have hρ1 := h.ρ_le
  have hr := pow_pos hρ0 N
  have hrr : D.ρ ^ (N + 1) = D.ρ * D.ρ ^ N := pow_succ' _ _
  obtain ⟨z, hz, hxz⟩ : ∃ z ∈ D.good N, x ∈ ball z (D.ρ ^ N) := by
    rcases subset_cover h.hyp hN hx with h1 | h1
    · simpa only [mem_iUnion, exists_prop] using h1
    · exact absurd h1 hxN
  set V := D.V N z
  have hV : ‖V.2‖ = 1 := h.unit N z
  have hfx : |⟪x - V.1, V.2⟫| < D.ρ ^ (N + 1) / 4 := by
    by_contra hle
    refine hxN (excessUnion_subset_rem hN ?_)
    exact mem_biUnion (x := z) (Finset.mem_coe.2 hz) ⟨hxz, not_lt.1 hle⟩
  obtain ⟨g, hg⟩ := chartInv h hN z hz
  have hsmall := six_C_sq_mul_le h.one_le_n hρ0 (d1_le_small h hN hz)
  have hx5 : x ∈ ball z (5 / 2 * D.ρ ^ N) := ball_subset_ball (by linarith) hxz
  set u := affProj V x
  have hu : u ∈ disc V z (5 / 2 * D.ρ ^ N) := affProj_mem_disc hV hx5
  have hgu : |g u| ≤ D.ρ ^ (N + 1) / 100 := by
    refine (hg.2.1 u hu).trans ?_
    rw [hrr]
    linarith [mul_le_mul_of_nonneg_right hsmall hr.le]
  set q := u + g u • V.2
  have hqx : dist q x < D.ρ ^ (N + 1) / 3 := by
    have hx' : x = u + ⟪x - V.1, V.2⟫ • V.2 := (affProj_add_inner_smul V x).symm
    have e : q - x = (g u - ⟪x - V.1, V.2⟫) • V.2 := by
      calc q - x = (u + g u • V.2) - (u + ⟪x - V.1, V.2⟫ • V.2) := by rw [← hx']
        _ = (g u - ⟪x - V.1, V.2⟫) • V.2 := by rw [sub_smul]; abel
    rw [dist_eq_norm, e, norm_smul, hV, mul_one, Real.norm_eq_abs]
    have h1 := abs_le.1 hgu
    have h2 := abs_lt.1 hfx
    have := pow_pos hρ0 (N + 1)
    rw [abs_lt]
    constructor <;> linarith
  refine ⟨q, ?_, hqx⟩
  have hqz : q ∈ ball z (5 / 2 * D.ρ ^ N) := by
    rw [mem_ball]
    have := dist_triangle q x z
    have := mem_ball.1 hxz
    rw [hrr] at hqx
    linarith [mul_le_mul_of_nonneg_right hρ1 hr.le]
  have hmem : q ∈ graphOn V g ∩ ball z (5 / 2 * D.ρ ^ N) := ⟨add_smul_mem_graphOn hu.1, hqz⟩
  rw [← hg.1] at hmem
  exact hmem.1

/-- **Every point of `G_∞` is on the limit surface**: `x = φ_∞(a)` with `a ∈ T₀`. -/
theorem exists_limitMap_eq {x : Rn n} (hx : x ∈ D.goodLimit) :
    ∃ a ∈ D.surf 0, D.limitMap a = x := by
  obtain ⟨hxP, hxrem⟩ := hx
  have hnot : ∀ N, x ∉ D.rem N := fun N hN => hxrem (mem_iUnion.2 ⟨N, hN⟩)
  have hρ0 := h.ρ_pos
  have hρ1 := h.ρ_le
  choose q hq hqx using fun N => exists_surf_near h hj hxP (hnot N)
  have hpre : ∀ N, ∃ a ∈ D.surf 0, D.flow N a = q N := fun N => by
    have := hq N
    rw [surf_eq_image_flow hj N] at this
    exact this
  choose a ha hflow using hpre
  -- the preimages stay in a compact set
  have hK : IsCompact (D.surf 0 ∩ closedBall x 1) := by
    refine (isCompact_closedBall x 1).inter_left ?_
    rw [surf_of_le (by omega)]
    exact isClosed_eq (by fun_prop) continuous_const
  have haK : ∀ N, a N ∈ D.surf 0 ∩ closedBall x 1 := fun N => by
    refine ⟨ha N, ?_⟩
    rw [mem_closedBall]
    have h1 := dist_flow_le h hj (ha N) N
    have h2 := hqx N
    have h3 : D.ρ ^ (N + 1) ≤ D.ρ := by
      rw [pow_succ']
      exact mul_le_of_le_one_right hρ0.le (pow_le_one₀ hρ0.le h.hyp.ρ_le_one)
    have := dist_triangle (a N) (D.flow N (a N)) x
    rw [hflow N] at this h1
    linarith
  obtain ⟨a₀, ha₀, φ, hφ, hlim⟩ := hK.tendsto_subseq haK
  refine ⟨a₀, ha₀.1, ?_⟩
  -- `φ_∞(a_N) → x`
  have hφx : Tendsto (fun N => D.limitMap (a N)) atTop (𝓝 x) := by
    have ht : Tendsto (fun N : ℕ => D.ρ ^ (N + 1) / 9 + D.ρ ^ (N + 1) / 3) atTop (𝓝 0) := by
      have h0 := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le
        (hρ1.trans_lt (by norm_num))).comp (tendsto_add_atTop_nat 1)
      have := (h0.div_const 9).add (h0.div_const 3)
      simpa using this
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun N => ?_) ht)
    have h1 := dist_flow_limitMap_le h hj (ha N) N
    rw [hflow N, dist_comm] at h1
    have := dist_triangle (D.limitMap (a N)) (q N) x
    have := hqx N
    linarith
  -- `φ_∞(a_{φ m}) → φ_∞(a₀)` by continuity
  have hcont : Tendsto (fun m => D.limitMap (a (φ m))) atTop (𝓝 (D.limitMap a₀)) := by
    refine ((continuousOn_limitMap h hj) a₀ ha₀.1).tendsto.comp ?_
    exact tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun m => ha (φ m)⟩
  exact tendsto_nhds_unique hcont (hφx.comp hφ.tendsto_atTop)

end Surjective

end CoverData

end GMTFoundations.DiscreteReifenberg
