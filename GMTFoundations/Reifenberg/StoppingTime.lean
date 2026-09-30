/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.EngineMass
public import GMTFoundations.Reifenberg.Flow
import Mathlib.Algebra.Order.Ring.Star

/-!
# The μ-side stopping time and Lemma L

The stopping-time step of the rectifiable-Reifenberg argument (`BigPieces.lean`). In A. Naber,
D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and minimizing harmonic
maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043 (NV), §5.9, the limit map `φ_∞` is
shown to be Lipschitz off a small set via the function `f` of (5.103) on `T₀` and the bound (5.104)
`∫_{T₀} f ≤ cδ²`, which NV justify only by "the usual double-induction argument". Comparing that
integral over `T₀` with the areas of the later surfaces requires a lower Jacobian bound for the
maps `Φ_i`, which is what the stopping time is meant to provide. Here the stopping time is
instead taken on the measure side: the stopping function lives on `ℝⁿ`, its `μ`-integral is
bounded by the Carleson packing of the discrete Reifenberg construction and the global upper bound
`μ(B_t(y)) ≤ Λ t^k`, and Markov's inequality bounds the stopped set. The stopping function is
built from the construction's own bi-Lipschitz excesses rather than from β-numbers at the point.

* `chartWeight D s x = Σ_{y ∈ Good_{s+1}, |x − y| < 6 r_{s+1}} ε_s(y)` (with
  `ε_s(y) = C_sq²(δ₀(y)² + δ₁(y)²)`, `CoverData.eps`), and the stopping function
  `stopFun D x = Σ_s chartWeight D s x` (the μ-side analogue of NV's `f`, (5.103)). It is a
  countable sum of finite sums of indicators of balls, so it is measurable with no analytic input
  (`measurable_stopFun`); in particular no measurability of `jonesBetaSq` in the center is needed.
* `lintegral_stopFun_le` (Tonelli plus the given upper bound): with
  `μ(B_t(y)) ≤ Λ t^k` on all balls, `∫ stopFun dμ ≤ Λ 6^k C_S J / θ²`, by the Carleson packing of
  the excesses (`EngineHyp.sum_eps_le`, `sum_d1Sum_succ_le`); `C_S = stopConst n ρ κ`.
* `measure_stopFun_lt_le`: Markov.
* **Lemma L** (`dist_limitMap_le_of_stopFun`): if `stopFun (φ_∞ u) ≤ a`, then
  `|φ_∞ u − φ_∞ u'| ≤ (5/4) e^a |u − u'|` for every `u' ∈ T₀` (compare NV (5.107)). Two regimes
  (chart regime `d < r_{s+1}`: the chart bi-Lipschitz bound, output (O3) of `reifenbergStep`, via
  `dist_lt_cases`; large regime: the displacement bound `|σ a − a| ≤ r_{s+1}/10`) are combined in
  one induction. Only the upper bound is proved; the lower bound is not needed for
  rectifiability.

## References

* [NV] A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and
  minimizing harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043, §5.9,
  (5.103)–(5.110).
-/

@[expose] public noncomputable section

namespace GMTFoundations.DiscreteReifenberg

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

namespace CoverData

/-- The constant of the stopping-function integral: `C_S = C_sq²((6C_sq/ρ)² parConst + 1) · C_t ·
21ⁿ(1 + 2 parConst) · C_pack` (`areaConst = 2k ω_k 10^k C_S`). -/
def stopConst (n : ℕ) (ρ κ : ℝ) : ℝ :=
  C_sq n ^ 2 * ((6 * C_sq n / ρ) ^ 2 * parConst n ρ + 1) * tiltConst n ρ κ *
    (21 ^ n * (1 + 2 * parConst n ρ)) * packConst n ρ

theorem stopConst_nonneg {ρ κ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hκ : 0 < κ) :
    0 ≤ stopConst n ρ κ := by
  have := tiltConst_pos (n := n) hρ0 hκ
  have := packConst_nonneg (n := n) hρ0 hρ1
  unfold stopConst
  positivity

variable {D : CoverData n}

/-- The chart weight at scale `s + 1` near `x`: `Σ_{y ∈ Good_{s+1}, |x − y| < 6 r_{s+1}} ε_s(y)`. -/
def chartWeight (D : CoverData n) (s : ℕ) (x : Rn n) : ℝ :=
  ∑ y ∈ D.good (s + 1), (ball y (6 * D.ρ ^ (s + 1))).indicator (fun _ => D.eps s y) x

/-- The stopping function `A(x) = Σ_s chartWeight s x` (μ side). -/
def stopFun (D : CoverData n) (x : Rn n) : ℝ≥0∞ := ∑' s, ENNReal.ofReal (D.chartWeight s x)

theorem chartWeight_nonneg (s : ℕ) (x : Rn n) : 0 ≤ D.chartWeight s x :=
  Finset.sum_nonneg fun y _ => indicator_nonneg (fun _ _ => eps_nonneg s y) x

theorem eps_le_chartWeight {s : ℕ} {y x : Rn n} (hy : y ∈ D.good (s + 1))
    (hx : x ∈ ball y (6 * D.ρ ^ (s + 1))) : D.eps s y ≤ D.chartWeight s x := by
  have := Finset.single_le_sum
    (f := fun y => (ball y (6 * D.ρ ^ (s + 1))).indicator (fun _ => D.eps s y) x)
    (fun y _ => indicator_nonneg (fun _ _ => eps_nonneg s y) x) hy
  unfold CoverData.chartWeight
  simpa only [indicator_of_mem hx] using this

theorem measurable_chartWeight (s : ℕ) : Measurable (D.chartWeight s) :=
  Finset.measurable_sum _ fun _ _ => measurable_const.indicator measurableSet_ball

theorem measurable_stopFun : Measurable D.stopFun := by
  unfold stopFun
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact .iSup fun s => s.measurable_fun_sum fun i _ =>
    ENNReal.measurable_ofReal.comp (measurable_chartWeight i)

theorem lintegral_ofReal_chartWeight (s : ℕ) :
    ∫⁻ x, ENNReal.ofReal (D.chartWeight s x) ∂D.μ =
      ∑ y ∈ D.good (s + 1), ENNReal.ofReal (D.eps s y) * D.μ (ball y (6 * D.ρ ^ (s + 1))) := by
  have e : ∀ x, ENNReal.ofReal (D.chartWeight s x) = ∑ y ∈ D.good (s + 1),
      (ball y (6 * D.ρ ^ (s + 1))).indicator (fun _ => ENNReal.ofReal (D.eps s y)) x := by
    intro x
    rw [chartWeight, ENNReal.ofReal_sum_of_nonneg fun y _ =>
      indicator_nonneg (fun _ _ => eps_nonneg s y) x]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hx : x ∈ ball y (6 * D.ρ ^ (s + 1))
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, ENNReal.ofReal_zero]
  simp_rw [e]
  rw [lintegral_finsetSum _ fun y _ => measurable_const.indicator measurableSet_ball]
  exact Finset.sum_congr rfl fun y _ => lintegral_indicator_const measurableSet_ball _

/-- **The stopping function is integrable** (Tonelli plus the upper bound
`μ(B_t(y)) ≤ Λ t^k` on all balls):
`∫ A dμ ≤ Λ 6^k C_S J / θ²`. -/
theorem lintegral_stopFun_le {κ Λ J : ℝ} (h : D.EngineHyp κ Λ J) (hj : D.j = 0)
    (hU : ∀ (x : Rn n) (r : ℝ), 0 < r → D.μ (ball x r) ≤ ENNReal.ofReal (Λ * r ^ (n - 1))) :
    ∫⁻ x, D.stopFun x ∂D.μ ≤
      ENNReal.ofReal (Λ * 6 ^ (n - 1) * stopConst n D.ρ κ * J / D.θ ^ 2) := by
  have hρ0 := h.ρ_pos
  have hθ := h.θ_pos
  have hJ := h.J_nonneg
  have hΛ := h.Λ_pos
  have hT := tiltConst_pos (n := n) hρ0 h.κ_pos
  have hP := packConst_nonneg (n := n) hρ0 h.est.ρ_le_one
  simp only [stopFun]
  rw [lintegral_tsum (f := fun s x => ENNReal.ofReal (D.chartWeight s x)) fun s =>
    (ENNReal.measurable_ofReal.comp (measurable_chartWeight s)).aemeasurable]
  simp_rw [lintegral_ofReal_chartWeight]
  refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
  set E := C_sq n ^ 2 * ((6 * C_sq n / D.ρ) ^ 2 * parConst n D.ρ + 1)
  have hE : 0 ≤ E := by positivity
  have hsum := (h.sum_eps_le N).trans (mul_le_mul_right (h.sum_d1Sum_succ_le N) _)
  rw [hj, ← Finset.range_eq_Ico] at hsum
  calc ∑ s ∈ Finset.range N, ∑ y ∈ D.good (s + 1),
        ENNReal.ofReal (D.eps s y) * D.μ (ball y (6 * D.ρ ^ (s + 1)))
      ≤ ∑ s ∈ Finset.range N, ∑ y ∈ D.good (s + 1),
          ENNReal.ofReal (Λ * 6 ^ (n - 1)) *
            (ENNReal.ofReal (D.eps s y) * ENNReal.ofReal ((D.ρ ^ (s + 1)) ^ (n - 1))) := by
        refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun y _ => ?_
        have he := eps_nonneg (D := D) s y
        calc ENNReal.ofReal (D.eps s y) * D.μ (ball y (6 * D.ρ ^ (s + 1)))
            ≤ ENNReal.ofReal (D.eps s y) *
                ENNReal.ofReal (Λ * (6 * D.ρ ^ (s + 1)) ^ (n - 1)) :=
              mul_le_mul_right (hU _ _ (by positivity)) _
          _ = _ := by
              rw [← ENNReal.ofReal_mul he, ← ENNReal.ofReal_mul he,
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [mul_pow]
              ring
    _ = ENNReal.ofReal (Λ * 6 ^ (n - 1)) * ∑ s ∈ Finset.range N, ∑ y ∈ D.good (s + 1),
          ENNReal.ofReal (D.eps s y) * ENNReal.ofReal ((D.ρ ^ (s + 1)) ^ (n - 1)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Λ * 6 ^ (n - 1)) * (ENNReal.ofReal E *
          (ENNReal.ofReal (tiltConst n D.ρ κ / D.θ) * ((21 ^ n : ℕ) *
            ((1 + 2 * parConst n D.ρ : ℕ) *
              ENNReal.ofReal (packConst n D.ρ * J * (D.ρ ^ 0) ^ (n - 1) / D.θ))))) :=
        mul_le_mul_right hsum _
    _ = _ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [stopConst, E, pow_zero, one_pow, mul_one]
        push_cast
        field_simp

/-- **Markov** for the stopping function. -/
theorem measure_stopFun_lt_le {a : ℝ} (ha : 0 < a) :
    D.μ {x | ENNReal.ofReal a < D.stopFun x} ≤ (∫⁻ x, D.stopFun x ∂D.μ) / ENNReal.ofReal a :=
  (measure_mono (s := {x | ENNReal.ofReal a < D.stopFun x})
    (t := {x | ENNReal.ofReal a ≤ D.stopFun x})
    fun x (hx : ENNReal.ofReal a < D.stopFun x) => show ENNReal.ofReal a ≤ D.stopFun x from
      le_of_lt hx).trans
    (meas_ge_le_lintegral_div measurable_stopFun.aemeasurable
      (ENNReal.ofReal_pos.2 ha).ne' ENNReal.ofReal_ne_top)

/-! ### Lemma L -/

section LemmaL

variable (h : D.SurfHyp) (hj : D.j = 0)
include h hj

/-- One scale in the chart regime: pairs at distance `< r_{s+1}` grow by at most the factor
`1 + chartWeight s x`, where `x = φ_∞ u`. -/
theorem dist_flow_succ_le_chart {u u' : Rn n} (hu : u ∈ D.surf 0) (hu' : u' ∈ D.surf 0) (s : ℕ)
    (hd : dist (D.flow s u) (D.flow s u') < D.ρ ^ (s + 1)) :
    dist (D.flow (s + 1) u) (D.flow (s + 1) u') ≤
      (1 + D.chartWeight s (D.limitMap u)) * dist (D.flow s u) (D.flow s u') := by
  have hi : D.j ≤ s := by omega
  have hr := pow_pos h.ρ_pos (s + 1)
  have hw := chartWeight_nonneg (D := D) s (D.limitMap u)
  have hd0 := dist_nonneg (x := D.flow s u) (y := D.flow s u')
  have hid : ∀ z, (∀ y ∈ D.good (s + 1), 4 * D.ρ ^ (s + 1) ≤ dist z y) → D.sigma (s + 1) z = z :=
    fun z hz => reifenbergMap_eq_self hr hz
  rw [flow_succ, flow_succ]
  rcases dist_lt_cases hid hd with ⟨y, hy, hay, hby⟩ | ⟨hfa, hfb⟩
  · have hb := (sigma_bilip h hi hy ⟨flow_mem_surf hj hu s, hay⟩
      ⟨flow_mem_surf hj hu' s, hby⟩).1
    have hx : D.limitMap u ∈ ball y (6 * D.ρ ^ (s + 1)) := by
      rw [mem_ball]
      have h1 := dist_flow_limitMap_le h hj hu s
      have h2 := mem_ball.1 hay
      have := dist_triangle (D.limitMap u) (D.flow s u) y
      rw [dist_comm] at h1
      linarith
    have he := eps_le_chartWeight hy hx
    refine hb.trans ?_
    gcongr
  · rw [hfa, hfb]
    exact le_mul_of_one_le_left hd0 (by linarith)

/-- One scale in any regime: `|d_{s+1} − d_s| ≤ r_{s+1}/5` (displacement `≤ r_{s+1}/10`). -/
theorem abs_dist_flow_succ_sub_le {u u' : Rn n} (hu : u ∈ D.surf 0) (hu' : u' ∈ D.surf 0)
    (s : ℕ) :
    |dist (D.flow (s + 1) u) (D.flow (s + 1) u') - dist (D.flow s u) (D.flow s u')| ≤
      D.ρ ^ (s + 1) / 5 := by
  have hi : D.j ≤ s := by omega
  rw [flow_succ, flow_succ]
  have := abs_dist_sub_dist_le (σ := D.sigma (s + 1)) (T := D.surf s) (ε := 1 / 10)
    (r := D.ρ ^ (s + 1)) (fun a ha => (dist_sigma_le h hi ha).trans (le_of_eq (by ring)))
    (flow_mem_surf hj hu s) (flow_mem_surf hj hu' s)
  exact this.trans (le_of_eq (by ring))

/-- **Lemma L** (upper bound): if the stopping function at `x = φ_∞ u` is at most
`a`, then `|φ_∞ u − φ_∞ u'| ≤ (5/4) e^a |u − u'|` for every `u' ∈ T₀`. -/
theorem dist_limitMap_le_of_stopFun {u u' : Rn n} (hu : u ∈ D.surf 0) (hu' : u' ∈ D.surf 0)
    {a : ℝ} (ha : 0 ≤ a) (hA : D.stopFun (D.limitMap u) ≤ ENNReal.ofReal a) :
    dist (D.limitMap u) (D.limitMap u') ≤ 5 / 4 * Real.exp a * dist u u' := by
  have hρ0 := h.ρ_pos
  have hρ1 := h.ρ_le
  set x := D.limitMap u
  set w : ℕ → ℝ := fun t => D.chartWeight t x
  set d : ℕ → ℝ := fun s => dist (D.flow s u) (D.flow s u')
  set c : ℕ → ℝ := fun s => (∏ t ∈ Finset.range s, (1 + w t)) * d 0
  have hw : ∀ t, 0 ≤ w t := fun t => chartWeight_nonneg t x
  have hd0 : ∀ s, 0 ≤ d s := fun s => dist_nonneg
  have hc0 : ∀ s, 0 ≤ c s := fun s =>
    mul_nonneg (Finset.prod_nonneg fun t _ => by linarith [hw t]) (hd0 0)
  have hcs : ∀ s, c (s + 1) = (1 + w s) * c s := fun s => by
    simp only [c, Finset.prod_range_succ]
    ring
  have hcmono : ∀ s, c s ≤ c (s + 1) := fun s => by
    rw [hcs]
    exact le_mul_of_one_le_left (hc0 s) (by linarith [hw s])
  have hchart : ∀ s, d s < D.ρ ^ (s + 1) → d (s + 1) ≤ (1 + w s) * d s :=
    fun s hds => dist_flow_succ_le_chart h hj hu hu' s hds
  have hlarge : ∀ s, |d (s + 1) - d s| ≤ D.ρ ^ (s + 1) / 5 :=
    fun s => abs_dist_flow_succ_sub_le h hj hu hu' s
  -- the two-regime invariant
  have hinv : ∀ s, (d s < D.ρ ^ (s + 1) ∧ d s ≤ c s) ∨
      (D.ρ ^ (s + 1) ≤ d s ∧ d s + D.ρ ^ (s + 1) / 4 ≤ 5 / 4 * c s) := by
    intro s
    induction s with
    | zero =>
      have e : c 0 = d 0 := by simp [c]
      rw [zero_add, pow_one, e]
      rcases lt_or_ge (d 0) D.ρ with h0 | h0
      · exact Or.inl ⟨h0, le_rfl⟩
      · exact Or.inr ⟨h0, by linarith⟩
    | succ s ih =>
      have hr := pow_pos hρ0 (s + 1)
      have hrr : D.ρ ^ (s + 1 + 1) = D.ρ * D.ρ ^ (s + 1) := pow_succ' _ _
      rcases ih with ⟨hds, hdc⟩ | ⟨hrd, hdc⟩
      · have h1 : d (s + 1) ≤ c (s + 1) := by
          rw [hcs]
          exact (hchart s hds).trans (mul_le_mul_of_nonneg_left hdc (by linarith [hw s]))
        rcases lt_or_ge (d (s + 1)) (D.ρ ^ (s + 1 + 1)) with h2 | h2
        · exact Or.inl ⟨h2, h1⟩
        · exact Or.inr ⟨h2, by linarith⟩
      · have h1 := abs_le.1 (hlarge s)
        have hρr := mul_le_mul_of_nonneg_right hρ1 hr.le
        have h2 : D.ρ ^ (s + 1 + 1) ≤ d (s + 1) := by
          rw [hrr]
          linarith
        refine Or.inr ⟨h2, ?_⟩
        have := hcmono s
        rw [hrr]
        linarith
  have hdc : ∀ s, d s ≤ 5 / 4 * c s := fun s => by
    rcases hinv s with ⟨-, h1⟩ | ⟨-, h1⟩
    · linarith [hc0 s]
    · linarith [pow_pos hρ0 (s + 1)]
  -- the product of the chart factors is at most `e^a`
  have hprod : ∀ s, ∏ t ∈ Finset.range s, (1 + w t) ≤ Real.exp a := by
    intro s
    have hsum : ∑ t ∈ Finset.range s, w t ≤ a := by
      rw [← ENNReal.ofReal_le_ofReal_iff ha, ENNReal.ofReal_sum_of_nonneg fun t _ => hw t]
      exact (ENNReal.sum_le_tsum _).trans hA
    calc ∏ t ∈ Finset.range s, (1 + w t) ≤ ∏ t ∈ Finset.range s, Real.exp (w t) :=
          Finset.prod_le_prod₀ (fun t _ => by linarith [hw t])
            fun t _ => by linarith [Real.add_one_le_exp (w t)]
      _ = Real.exp (∑ t ∈ Finset.range s, w t) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp a := Real.exp_le_exp.2 hsum
  have hbound : ∀ s, d s ≤ 5 / 4 * Real.exp a * dist u u' := fun s => by
    refine (hdc s).trans ?_
    have : c s ≤ Real.exp a * d 0 := mul_le_mul_of_nonneg_right (hprod s) (hd0 0)
    have e : d 0 = dist u u' := rfl
    rw [e] at this
    linarith
  exact le_of_tendsto' ((tendsto_flow h hj hu).dist (tendsto_flow h hj hu')) hbound

end LemmaL

end CoverData

end GMTFoundations.DiscreteReifenberg
