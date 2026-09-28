/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.Induction
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered

/-!
# The Reifenberg flow and its limit map

The flow `Φ_i = σ_i ∘ ⋯ ∘ σ_1` (`CoverData.flow`) and the limit map `φ_∞ = lim Φ_i`
(`CoverData.limitMap`) of a run `D` with `D.SurfHyp` and top scale `D.j = 0`: `Φ_i` maps `T₀` onto
`T_i` (`surf_eq_image_flow`), `|φ_∞ a − Φ_i a| ≤ ρ^{i+1}/9` on `T₀` (`dist_flow_limitMap_le`), and
`φ_∞` is continuous on `T₀` (`continuousOn_limitMap`, via `continuous_reifenbergMap`).

(Split out of `Reifenberg/LimitMap.lean`, which re-exports it, so that
`Reifenberg/StoppingTime.lean` does not wait for the mass accounting of `LimitMap`.)
-/

@[expose] public noncomputable section

namespace GMTFoundations.DiscreteReifenberg

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

/-! ### Continuity of the Reifenberg map -/

theorem continuous_puBump (r : ℝ) (c : Rn n) : Continuous fun z => puBump r c z := by
  unfold puBump
  fun_prop

theorem continuous_puSum (r : ℝ) (Y : Finset (Rn n)) : Continuous fun z => puSum r Y z := by
  unfold puSum
  exact continuous_finsetSum _ fun c _ => continuous_puBump r c

theorem continuous_puLambda (r : ℝ) (Y : Finset (Rn n)) (c : Rn n) :
    Continuous fun z => puLambda r Y c z := by
  unfold puLambda
  refine (continuous_puBump r c).div ((continuous_puSum r Y).max continuous_const) fun z => ?_
  exact (zero_lt_one.trans_le (le_max_right _ _)).ne'

/-- The Reifenberg map is continuous. -/
theorem continuous_reifenbergMap (r : ℝ) (Y : Finset (Rn n)) (Vp : Rn n → Rn n × Rn n) :
    Continuous (reifenbergMap r Y Vp) := by
  unfold reifenbergMap
  refine continuous_id.sub (continuous_finsetSum _ fun c _ => ?_)
  exact ((continuous_puLambda r Y c).mul
    ((continuous_id.sub continuous_const).inner continuous_const)).smul continuous_const

/-! ### The flow and the limit map -/

namespace CoverData

variable {D : CoverData n}

/-- The flow `Φ_0 = id`, `Φ_{i+1} = σ_{i+1} ∘ Φ_i`. -/
def flow (D : CoverData n) : ℕ → Rn n → Rn n
  | 0 => id
  | i + 1 => D.sigma (i + 1) ∘ D.flow i

/-- The limit map `φ_∞ = lim_i Φ_i`. -/
def limitMap (D : CoverData n) (a : Rn n) : Rn n := limUnder atTop fun i => D.flow i a

theorem flow_zero (a : Rn n) : D.flow 0 a = a := rfl

theorem flow_succ (i : ℕ) (a : Rn n) : D.flow (i + 1) a = D.sigma (i + 1) (D.flow i a) := rfl

theorem continuous_flow (i : ℕ) : Continuous (D.flow i) := by
  induction i with
  | zero => exact continuous_id
  | succ i ih => exact (continuous_reifenbergMap _ _ _).comp ih

section Flow

theorem flow_mem_surf (hj : D.j = 0) {a : Rn n} (ha : a ∈ D.surf 0) (i : ℕ) :
    D.flow i a ∈ D.surf i := by
  induction i with
  | zero => exact ha
  | succ i ih =>
    rw [surf_succ (by omega)]
    exact ⟨_, ih, rfl⟩

/-- `Φ_i` maps `T₀` onto `T_i`. -/
theorem surf_eq_image_flow (hj : D.j = 0) (i : ℕ) : D.surf i = D.flow i '' D.surf 0 := by
  induction i with
  | zero => exact (image_id _).symm
  | succ i ih =>
    rw [surf_succ (by omega), ih, image_image]
    rfl

variable (h : D.SurfHyp) (hj : D.j = 0)
include h hj

theorem dist_flow_succ_le {a : Rn n} (ha : a ∈ D.surf 0) (i : ℕ) :
    dist (D.flow i a) (D.flow (i + 1) a) ≤ D.ρ / 10 * D.ρ ^ i := by
  rw [dist_comm, flow_succ]
  refine (dist_sigma_le h (by omega) (flow_mem_surf hj ha i)).trans (le_of_eq ?_)
  ring

theorem tendsto_flow {a : Rn n} (ha : a ∈ D.surf 0) :
    Tendsto (fun i => D.flow i a) atTop (𝓝 (D.limitMap a)) := by
  have hρ1 : D.ρ < 1 := h.ρ_le.trans_lt (by norm_num)
  have hc := cauchySeq_of_le_geometric D.ρ (D.ρ / 10) hρ1 (dist_flow_succ_le h hj ha)
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc)

/-- `|Φ_i a − φ_∞ a| ≤ ρ^{i+1}/9` on `T₀`. -/
theorem dist_flow_limitMap_le {a : Rn n} (ha : a ∈ D.surf 0) (i : ℕ) :
    dist (D.flow i a) (D.limitMap a) ≤ D.ρ ^ (i + 1) / 9 := by
  have hρ0 := h.ρ_pos
  have hρ1 := h.ρ_le
  refine (dist_le_of_le_geometric_of_tendsto D.ρ (D.ρ / 10) (hρ1.trans_lt (by norm_num))
    (dist_flow_succ_le h hj ha) (tendsto_flow h hj ha) i).trans ?_
  rw [div_le_div_iff₀ (by linarith) (by norm_num), pow_succ]
  have := pow_pos hρ0 i
  linarith [mul_pos this hρ0, mul_le_mul_of_nonneg_right hρ1 (mul_pos this hρ0).le]

theorem dist_limitMap_le {a : Rn n} (ha : a ∈ D.surf 0) : dist a (D.limitMap a) ≤ D.ρ / 9 := by
  simpa using dist_flow_limitMap_le h hj ha 0

theorem dist_flow_le {a : Rn n} (ha : a ∈ D.surf 0) (i : ℕ) : dist a (D.flow i a) ≤ D.ρ / 4 := by
  have h1 := dist_limitMap_le h hj ha
  have h2 := dist_flow_limitMap_le h hj ha i
  have h3 : D.ρ ^ (i + 1) ≤ D.ρ := by
    rw [pow_succ']
    exact mul_le_of_le_one_right h.ρ_pos.le (pow_le_one₀ h.ρ_pos.le h.hyp.ρ_le_one)
  have := dist_triangle a (D.limitMap a) (D.flow i a)
  rw [dist_comm (D.flow i a)] at h2
  have := h.ρ_pos
  linarith

theorem tendstoUniformlyOn_flow :
    TendstoUniformlyOn D.flow D.limitMap atTop (D.surf 0) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hρ0 := h.ρ_pos
  have hρ1 : D.ρ < 1 := h.ρ_le.trans_lt (by norm_num)
  have ht : Tendsto (fun i : ℕ => D.ρ ^ (i + 1) / 9) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp (tendsto_add_atTop_nat 1)
    simpa using this.div_const 9
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with i hi a ha
  rw [dist_comm]
  exact (dist_flow_limitMap_le h hj ha i).trans_lt hi

/-- `φ_∞` is continuous on `T₀` (uniform limit of continuous maps). -/
theorem continuousOn_limitMap : ContinuousOn D.limitMap (D.surf 0) :=
  (tendstoUniformlyOn_flow h hj).continuousOn
    (Frequently.of_forall fun i => (continuous_flow i).continuousOn)

end Flow

end CoverData

end GMTFoundations.DiscreteReifenberg
