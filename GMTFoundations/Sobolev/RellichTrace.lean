/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Statements.Sobolev
import GMTFoundations.Common.Divergence
import GMTFoundations.Sobolev.Lipschitz
import GMTFoundations.Sobolev.TraceInequality
import GMTFoundations.Sobolev.Rellich
import GMTFoundations.Sobolev.WeakL2
import GMTFoundations.Sobolev.L2Inner
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Rellich–Kondrachov with compact trace on the unit ball

This file proves `rellich_trace_weak_compactness`, i.e. `RellichTraceStatement n` from
`Statements/Sobolev.lean`: a sequence of functions Lipschitz on `B̄₁` with bounded `H¹(B₁)` energy
has a subsequence converging strongly in `L²(B₁)`, with traces converging strongly in `L²(∂B₁)`
and gradients converging weakly in `L²(B₁; ℝⁿ)` to the weak gradient of the limit. This combines
the compactness theorem (Evans–Gariepy, Thm 4.11) with the trace theorem (Evans–Gariepy,
Thm 4.6) on the ball.

The route differs from Evans–Gariepy. No trace operator on `W^{1,2}` is built, and there is no
extension across the sphere. Local Rellich compactness on the open ball gives `L²_loc(B₁)`
convergence. A ray estimate near the sphere (`lintegral_shell_sq_le`) then makes the subsequence
Cauchy in `L²(B₁)`, and a trace inequality for Lipschitz functions along rays
(`lintegral_sphere_sq_le`), applied to differences, makes the traces Cauchy in `L²(∂B₁)`.

## Main results

* `integral_mul_divergence_eq_neg`: integration by parts `∫_U f div ψ = -∫_U ⟪∇f, ψ⟫` for `f`
  locally Lipschitz on the open set `U` and `ψ ∈ C^∞_c(U; ℝⁿ)` (Step 1).
* `rellich_trace_weak_compactness`: Rellich–Kondrachov with compact trace. The trace inequality
  and the shell estimate it uses are in `Sobolev/TraceInequality.lean`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  CRC Press, Boca Raton, 2015.
-/

public section

namespace GMTFoundations

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace ContDiff

variable {n : ℕ}

/-! ### Step 1: the gradient on the ball, integration by parts -/

/-- A function that is a.e.-strongly measurable and bounded on a compact set `K` and vanishes
outside `K` is integrable. -/
private lemma integrable_of_bound_of_isCompact {g : Rn n → ℝ} {K : Set (Rn n)} (hK : IsCompact K)
    (hgm : AEStronglyMeasurable g (volume.restrict K)) (C : ℝ) (hC : ∀ x ∈ K, ‖g x‖ ≤ C)
    (h0 : ∀ x ∉ K, g x = 0) : Integrable g := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have : IntegrableOn g K :=
    (MemLp.of_bound hgm C ((ae_restrict_mem hK.measurableSet).mono hC)).integrable le_top
  exact this.integrable_of_forall_notMem_eq_zero h0

/-- A function continuous on a compact set `K` and vanishing outside `K` is integrable. -/
private lemma integrable_of_continuousOn_of_isCompact {g : Rn n → ℝ} {K : Set (Rn n)}
    (hK : IsCompact K) (hg : ContinuousOn g K) (h0 : ∀ x ∉ K, g x = 0) : Integrable g :=
  (hg.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero h0

/-- `⟪∇f(y), w⟫ = ∑ᵢ Df(y) eᵢ · wᵢ`. -/
private lemma inner_gradient_eq_sum (f : Rn n → ℝ) (y w : Rn n) :
    ⟪gradient f y, w⟫ = ∑ i, fderiv ℝ f y (EuclideanSpace.single i 1) * w i := by
  simp_rw [← inner_gradient_left_eq_fderiv, EuclideanSpace.inner_single_right, PiLp.inner_apply]
  simp [mul_comm]

/-- **Step 1: integration by parts for locally Lipschitz functions.** For `f` locally Lipschitz
on the open set `U` and `ψ ∈ C^∞_c(U; ℝⁿ)`, `∫_U f div ψ = -∫_U ⟪∇f, ψ⟫`. Proof:
`integral_fderiv_mul_eq_neg` for each coordinate `ψᵢ` in the direction `eᵢ`, summed with
`divergence_eq_sum_fderiv_coord`. -/
theorem integral_mul_divergence_eq_neg {U : Set (Rn n)} (hU : IsOpen U) {f : Rn n → ℝ}
    (hf : LocallyLipschitzOn U f) {ψ : Rn n → Rn n} (hψ : IsSmoothTestField U ψ) :
    ∫ y in U, f y * divergence ψ y = -∫ y in U, ⟪gradient f y, ψ y⟫ := by
  obtain ⟨hψs, hψc, hψU⟩ := hψ
  set K := tsupport ψ with hKdef
  have hK : IsCompact K := hψc
  set e : Fin n → Rn n := fun i => EuclideanSpace.single i 1 with hedef
  have hcomp : ∀ i : Fin n, ContDiff ℝ ∞ (fun y => ψ y i) := fun i =>
    (EuclideanSpace.proj i : Rn n →L[ℝ] ℝ).contDiff.comp hψs
  have hsupp : ∀ i : Fin n, tsupport (fun y => ψ y i) ⊆ K := fun i =>
    tsupport_comp_subset (g := fun v : Rn n => v i) (by simp) ψ
  have hcc : ∀ i : Fin n, HasCompactSupport (fun y => ψ y i) := fun i =>
    hψc.comp_left (g := fun v : Rn n => v i) (by simp)
  have hdiff : ∀ y, DifferentiableAt ℝ ψ y := fun y =>
    (hψs.differentiable (by simp)).differentiableAt
  have hibp : ∀ i : Fin n, ∫ y in U, fderiv ℝ f y (e i) * ψ y i =
      -∫ y in U, f y * fderiv ℝ (fun y => ψ y i) y (e i) := fun i =>
    integral_fderiv_mul_eq_neg hU hf ((hcomp i).of_le (by simp)) (hcc i) ((hsupp i).trans hψU) _
  obtain ⟨Cf, hCf⟩ := exists_bound_fderiv_of_locallyLipschitzOn hU hf hK hψU
  have hψ0 : ∀ i : Fin n, ∀ y ∉ K, ψ y i = 0 := fun i y hy =>
    image_eq_zero_of_notMem_tsupport (f := fun y => ψ y i) fun h => hy (hsupp i h)
  have hdψ0 : ∀ i : Fin n, ∀ y ∉ K, fderiv ℝ (fun y => ψ y i) y (e i) = 0 := fun i y hy => by
    rw [fderiv_of_notMem_tsupport ℝ fun h => hy (hsupp i h)]
    rfl
  have hint1 : ∀ i : Fin n, Integrable (fun y => fderiv ℝ f y (e i) * ψ y i) := by
    intro i
    obtain ⟨M, hM⟩ := (hcomp i).continuous.bounded_above_of_compact_support (hcc i)
    refine integrable_of_bound_of_isCompact hK
      (((measurable_fderiv_apply_const ℝ f (e i)).aestronglyMeasurable).mul
        (hcomp i).continuous.aestronglyMeasurable) (Cf * ‖e i‖ * M) (fun y hy => ?_)
      (fun y hy => by simp [hψ0 i y hy])
    rw [norm_mul]
    exact mul_le_mul (((fderiv ℝ f y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hCf y hy) (norm_nonneg _))) (hM y) (norm_nonneg _)
      (by nlinarith [norm_nonneg (fderiv ℝ f y), hCf y hy, norm_nonneg (e i)])
  have hint2 : ∀ i : Fin n, Integrable (fun y => f y * fderiv ℝ (fun y => ψ y i) y (e i)) := by
    intro i
    have hc : Continuous fun y => fderiv ℝ (fun y => ψ y i) y (e i) :=
      ((hcomp i).continuous_fderiv (by simp)).clm_apply continuous_const
    exact integrable_of_continuousOn_of_isCompact hK
      ((hf.continuousOn.mono hψU).mul hc.continuousOn) (fun y hy => by simp [hdψ0 i y hy])
  have eL : ∫ y in U, f y * divergence ψ y =
      ∑ i, ∫ y in U, f y * fderiv ℝ (fun y => ψ y i) y (e i) := by
    rw [← integral_finsetSum _ fun i _ => (hint2 i).integrableOn]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [divergence_eq_sum_fderiv_coord (hdiff y), Finset.mul_sum, hedef]
  have eR : ∫ y in U, ⟪gradient f y, ψ y⟫ = ∑ i, ∫ y in U, fderiv ℝ f y (e i) * ψ y i := by
    rw [← integral_finsetSum _ fun i _ => (hint1 i).integrableOn]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [inner_gradient_eq_sum, hedef]
  rw [eL, eR, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [hibp i, neg_neg]

/-! ### `L²` bookkeeping -/

section L2

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}

/-- `‖g‖²_{L²} = ∫ |g|²`, as extended reals. -/
private lemma sq_eLpNorm_two (g : α → F) (hg : AEStronglyMeasurable g μ) :
    eLpNorm g 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := μ) (p := 2) two_ne_zero hg
  have e1 : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := rfl
  have e2 : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
  rw [e1, e2, ENNReal.rpow_two] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- `‖g‖²_{L²} = ∫ g²` for real `g`, as extended reals. -/
private lemma sq_eLpNorm_two_real (g : α → ℝ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm g 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ := by
  rw [sq_eLpNorm_two _ hg]
  simp_rw [Real.norm_eq_abs, sq_abs]

/-- `∫ g² = ‖g‖²_{L²}` for real `g`. -/
private lemma integral_sq_eq (g : α → ℝ) (hg : AEStronglyMeasurable g μ) :
    ∫ x, g x ^ 2 ∂μ = (eLpNorm g 2 μ).toReal ^ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _) (hg.pow 2),
    ← sq_eLpNorm_two_real _ hg, ENNReal.toReal_pow]

/-- From `a² ≤ C` to `a ≤ √C`. -/
private lemma le_ofReal_sqrt {a : ℝ≥0∞} {C : ℝ} (hC : 0 ≤ C) (h : a ^ 2 ≤ ENNReal.ofReal C) :
    a ≤ ENNReal.ofReal √C := by
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt hC]
  exact h

/-- **Completeness of `L²`**, in the form used below: a sequence that is Cauchy for `∫ (f_j - f_k)²`
converges in `L²` to some `F`. -/
private lemma exists_memLp_tendsto_integral_sq (f : ℕ → α → ℝ) (hf : ∀ k, MemLp (f k) 2 μ)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ j ≥ N, ∀ k ≥ N,
      ∫⁻ x, ENNReal.ofReal ((f j x - f k x) ^ 2) ∂μ ≤ ENNReal.ofReal ε) :
    ∃ F : α → ℝ, MemLp F 2 μ ∧ Tendsto (fun k => ∫ x, (f k x - F x) ^ 2 ∂μ) atTop (𝓝 0) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set v : ℕ → Lp ℝ 2 μ := fun k => (hf k).toLp (f k) with hvdef
  have hdist : ∀ j k, dist (v j) (v k) ^ 2 =
      (∫⁻ x, ENNReal.ofReal ((f j x - f k x) ^ 2) ∂μ).toReal := by
    intro j k
    rw [Lp.dist_def, ← ENNReal.toReal_pow,
      sq_eLpNorm_two_real _ ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [(hf j).coeFn_toLp, (hf k).coeFn_toLp] with x h1 h2
    simp only [hvdef, Pi.sub_apply, h1, h2]
  have hcs : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε ^ 2 / 4) (by positivity)
    refine ⟨N, fun j hj k hk => ?_⟩
    have h2 : dist (v j) (v k) ^ 2 ≤ ε ^ 2 / 4 := by
      rw [hdist]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hN j hj k hk)
    nlinarith [dist_nonneg (x := v j) (y := v k)]
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨w, Lp.memLp w, ?_⟩
  have e : ∀ k, ∫ x, (f k x - w x) ^ 2 ∂μ = dist (v k) w ^ 2 := by
    intro k
    rw [integral_sq_eq (fun x => f k x - w x)
      ((hf k).aestronglyMeasurable.sub (Lp.aestronglyMeasurable w)), Lp.dist_def]
    congr 2
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hf k).coeFn_toLp] with x h1
    simp only [hvdef, Pi.sub_apply, h1]
  simp_rw [e]
  have := ((tendsto_iff_dist_tendsto_zero.1 hw).pow 2)
  simpa using this

/-- Strong `L²` convergence `u_k → F` passes to `∫ u_k d → ∫ F d` for `d ∈ L²`. -/
private lemma tendsto_integral_mul {u : ℕ → α → ℝ} {F d : α → ℝ} (hu : ∀ k, MemLp (u k) 2 μ)
    (hF : MemLp F 2 μ) (hd : MemLp d 2 μ)
    (h : Tendsto (fun k => ∫ x, (u k x - F x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, u k x * d x ∂μ) atTop (𝓝 (∫ x, F x * d x ∂μ)) := by
  have hint : ∀ {g : α → ℝ}, MemLp g 2 μ → Integrable (fun x => g x * d x) μ := fun hg => by
    simpa only [Real.inner_apply] using integrable_inner_of_memLp hg hd
  have hsq : Tendsto (fun k => √(∫ x, (u k x - F x) ^ 2 ∂μ)) atTop (𝓝 0) := by
    have h' : Tendsto (fun k => √(∫ x, (u k x - F x) ^ 2 ∂μ)) atTop (𝓝 √0) :=
      (Real.continuous_sqrt.tendsto 0).comp h
    simpa using h'
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun k => norm_nonneg _)
    (fun k => ?_) (by simpa using hsq.mul_const (eLpNorm d 2 μ).toReal))
  have hdiff : MemLp (fun x => u k x - F x) 2 μ := (hu k).sub hF
  rw [← integral_sub (hint (hu k)) (hint hF), Real.norm_eq_abs]
  have e : ∫ x, (u k x * d x - F x * d x) ∂μ = ∫ x, (u k x - F x) * d x ∂μ := by
    congr 1; funext x; ring
  rw [e]
  refine (abs_integral_mul_le_L2 hdiff hd).trans (le_of_eq ?_)
  rw [integral_sq_eq _ hdiff.aestronglyMeasurable, Real.sqrt_sq ENNReal.toReal_nonneg]

end L2

/-! ### Facts about functions Lipschitz on the closed ball -/

private lemma locallyLipschitzOn_ball {f : Rn n → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (closedBall 0 1)) : LocallyLipschitzOn (ball (0 : Rn n) 1) f :=
  fun _ _ => ⟨K, ball 0 1, self_mem_nhdsWithin, hf.mono ball_subset_closedBall⟩

private lemma ae_differentiableAt_ball {f : Rn n → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (closedBall 0 1)) :
    ∀ᵐ y, y ∈ ball (0 : Rn n) 1 → DifferentiableAt ℝ f y := by
  filter_upwards [(hf.mono ball_subset_closedBall).ae_differentiableWithinAt_of_mem
    (μ := volume)] with y hy hyb
  exact (hy hyb).differentiableAt (isOpen_ball.mem_nhds hyb)

/-- `∇(f - g) = ∇f - ∇g` a.e. on the ball. -/
private lemma ae_gradient_sub {f g : Rn n → ℝ} {Kf Kg : ℝ≥0}
    (hf : LipschitzOnWith Kf f (closedBall 0 1)) (hg : LipschitzOnWith Kg g (closedBall 0 1)) :
    ∀ᵐ y ∂(volume.restrict (ball (0 : Rn n) 1)),
      gradient (fun x => f x - g x) y = gradient f y - gradient g y := by
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [ae_differentiableAt_ball hf, ae_differentiableAt_ball hg] with y h1 h2 hy
  unfold gradient
  rw [fderiv_fun_sub (h1 hy) (h2 hy), LinearIsometryEquiv.map_sub]

/-- The per-function facts: `f, ∇f ∈ L²(B₁)`, and the energy bound as extended reals. -/
private lemma ball_facts {f : Rn n → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (closedBall 0 1))
    {C : ℝ} (hb : ∫ y in ball (0 : Rn n) 1, (f y ^ 2 + ‖gradient f y‖ ^ 2) ≤ C) :
    MemLp f 2 (volume.restrict (ball (0 : Rn n) 1)) ∧
      MemLp (gradient f) 2 (volume.restrict (ball (0 : Rn n) 1)) ∧
      ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (f y ^ 2) ≤ ENNReal.ofReal C ∧
      ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (‖gradient f y‖ ^ 2) ≤ ENNReal.ofReal C := by
  have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Rn n) 1).exists_bound_of_continuousOn
    hf.continuousOn
  have hfm : AEStronglyMeasurable f (volume.restrict (ball (0 : Rn n) 1)) :=
    (hf.continuousOn.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball
  have hgb : ∀ y ∈ ball (0 : Rn n) 1, ‖gradient f y‖ ≤ K := fun y hy => by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hy)
      (hf.mono ball_subset_closedBall)
  have hf2 : MemLp f 2 (volume.restrict (ball (0 : Rn n) 1)) :=
    MemLp.of_bound hfm M ((ae_restrict_mem measurableSet_ball).mono fun y hy =>
      hM y (ball_subset_closedBall hy))
  have hg2 : MemLp (gradient f) 2 (volume.restrict (ball (0 : Rn n) 1)) :=
    MemLp.of_bound (measurable_gradient f).aestronglyMeasurable K
      ((ae_restrict_mem measurableSet_ball).mono hgb)
  have hint : Integrable (fun y => f y ^ 2 + ‖gradient f y‖ ^ 2)
      (volume.restrict (ball (0 : Rn n) 1)) :=
    hf2.integrable_sq.add ((memLp_two_iff_integrable_sq_norm hg2.aestronglyMeasurable).1 hg2)
  have hle : ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (f y ^ 2 + ‖gradient f y‖ ^ 2) ≤
      ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => by positivity)]
    exact ENNReal.ofReal_le_ofReal hb
  refine ⟨hf2, hg2, (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_).trans hle,
    (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_).trans hle⟩
  · linarith [sq_nonneg ‖gradient f y‖]
  · linarith [sq_nonneg (f y)]

/-- Energy bounds for a difference `f - g`. -/
private lemma pair_energy {f g : Rn n → ℝ} {Kf Kg : ℝ≥0}
    (hf : LipschitzOnWith Kf f (closedBall 0 1)) (hg : LipschitzOnWith Kg g (closedBall 0 1))
    {C : ℝ}
    (hf1 : ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (f y ^ 2) ≤ ENNReal.ofReal C)
    (hf2 : ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (‖gradient f y‖ ^ 2) ≤ ENNReal.ofReal C)
    (hg1 : ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (g y ^ 2) ≤ ENNReal.ofReal C)
    (hg2 : ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (‖gradient g y‖ ^ 2) ≤ ENNReal.ofReal C) :
    ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal ((f y - g y) ^ 2) ≤ ENNReal.ofReal (4 * C) ∧
      ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (‖gradient (fun x => f x - g x) y‖ ^ 2) ≤
        ENNReal.ofReal (4 * C) := by
  have h4 : ENNReal.ofReal (4 * C) = 2 * ENNReal.ofReal C + 2 * ENNReal.ofReal C := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring
  have h2x : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      ENNReal.ofReal (2 * x + 2 * y) = 2 * ENNReal.ofReal x + 2 * ENNReal.ofReal y :=
    fun x y hx hy => by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hsq : ∀ a b : ℝ, ENNReal.ofReal ((a - b) ^ 2) ≤
      2 * ENNReal.ofReal (a ^ 2) + 2 * ENNReal.ofReal (b ^ 2) := fun a b => by
    rw [← h2x _ _ (sq_nonneg _) (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by linarith [sq_nonneg (a + b)])
  have hnsq : ∀ a b : Rn n, ENNReal.ofReal (‖a - b‖ ^ 2) ≤
      2 * ENNReal.ofReal (‖a‖ ^ 2) + 2 * ENNReal.ofReal (‖b‖ ^ 2) := fun a b => by
    rw [← h2x _ _ (sq_nonneg _) (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := norm_sub_le a b
    nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]
  have hgm : AEMeasurable (fun y => 2 * ENNReal.ofReal (g y ^ 2))
      (volume.restrict (ball (0 : Rn n) 1)) :=
    (((hg.continuousOn.mono ball_subset_closedBall).aemeasurable measurableSet_ball).pow_const
      2).ennreal_ofReal.const_mul 2
  have hggm : AEMeasurable (fun y => 2 * ENNReal.ofReal (‖gradient g y‖ ^ 2))
      (volume.restrict (ball (0 : Rn n) 1)) :=
    (((measurable_gradient g).norm.pow_const 2).ennreal_ofReal.const_mul 2).aemeasurable
  constructor
  · calc ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal ((f y - g y) ^ 2)
        ≤ ∫⁻ y in ball (0 : Rn n) 1,
            (2 * ENNReal.ofReal (f y ^ 2) + 2 * ENNReal.ofReal (g y ^ 2)) :=
          lintegral_mono fun y => hsq _ _
      _ = 2 * (∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (f y ^ 2)) +
          2 * ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (g y ^ 2) := by
          rw [lintegral_add_right' _ hgm, lintegral_const_mul' _ _ (by simp),
            lintegral_const_mul' _ _ (by simp)]
      _ ≤ ENNReal.ofReal (4 * C) := by rw [h4]; gcongr
  · calc ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (‖gradient (fun x => f x - g x) y‖ ^ 2)
        ≤ ∫⁻ y in ball (0 : Rn n) 1, (2 * ENNReal.ofReal (‖gradient f y‖ ^ 2) +
            2 * ENNReal.ofReal (‖gradient g y‖ ^ 2)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_gradient_sub hf hg] with y hy
          rw [hy]
          exact hnsq _ _
      _ = 2 * (∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (‖gradient f y‖ ^ 2)) +
          2 * ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (‖gradient g y‖ ^ 2) := by
          rw [lintegral_add_right' _ hggm, lintegral_const_mul' _ _ (by simp),
            lintegral_const_mul' _ _ (by simp)]
      _ ≤ ENNReal.ofReal (4 * C) := by rw [h4]; gcongr

/-- The density of the trace inequality, bounded by `(1 + λ) g² + λ⁻¹ |∇g|²` on the ball. -/
private lemma annulus_density_le {g : Rn n → ℝ} {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
        ENNReal.ofReal (g y ^ 2 + 2 * |g y| * ‖gradient g y‖) ≤
      ENNReal.ofReal (1 + lam) * (∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (g y ^ 2)) +
        ENNReal.ofReal lam⁻¹ * ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal (‖gradient g y‖ ^ 2) := by
  have hpt : ∀ a b : ℝ, 0 ≤ b → ENNReal.ofReal (a ^ 2 + 2 * |a| * b) ≤
      ENNReal.ofReal (1 + lam) * ENNReal.ofReal (a ^ 2) +
        ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (b ^ 2) := fun a b hb => by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := mul_nonneg (inv_nonneg.2 hlam.le) (sq_nonneg (lam * |a| - b))
    have e : lam⁻¹ * (lam * |a| - b) ^ 2 = lam * |a| ^ 2 - 2 * |a| * b + lam⁻¹ * b ^ 2 := by
      field_simp
      ring
    rw [e, sq_abs] at h
    linarith
  have hm : AEMeasurable (fun y => ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (‖gradient g y‖ ^ 2))
      (volume.restrict (ball (0 : Rn n) 1 \ ball 0 (1 / 2))) :=
    (((measurable_gradient g).norm.pow_const 2).ennreal_ofReal.const_mul _).aemeasurable
  calc ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
        ENNReal.ofReal (g y ^ 2 + 2 * |g y| * ‖gradient g y‖)
      ≤ ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
          (ENNReal.ofReal (1 + lam) * ENNReal.ofReal (g y ^ 2) +
            ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (‖gradient g y‖ ^ 2)) :=
        lintegral_mono fun y => hpt _ _ (norm_nonneg _)
    _ = ENNReal.ofReal (1 + lam) *
          (∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2), ENNReal.ofReal (g y ^ 2)) +
        ENNReal.ofReal lam⁻¹ *
          ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2), ENNReal.ofReal (‖gradient g y‖ ^ 2) := by
        rw [lintegral_add_right' _ hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
        gcongr <;> exact sdiff_subset

/-- The traces of a function Lipschitz on the closed ball are in `L²(σ)`. -/
private lemma memLp_sphere {f : Rn n → ℝ} {K : ℝ≥0} (hf : LipschitzOnWith K f (closedBall 0 1)) :
    MemLp (fun z : sphere (0 : Rn n) 1 => f z) 2 (sphereMeasure n) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Rn n) 1).exists_bound_of_continuousOn
    hf.continuousOn
  have hc : Continuous fun z : sphere (0 : Rn n) 1 => f z :=
    hf.continuousOn.comp_continuous continuous_subtype_val fun z => sphere_subset_closedBall z.2
  exact MemLp.of_bound hc.aestronglyMeasurable M
    (ae_of_all _ fun z => hM _ (sphere_subset_closedBall z.2))

/-- A continuous compactly supported function is in `L²(B₁)`. -/
private lemma memLp_two_ball {F : Type*} [NormedAddCommGroup F] {g : Rn n → F}
    (hc : Continuous g) (hs : HasCompactSupport g) :
    MemLp g 2 (volume.restrict (ball (0 : Rn n) 1)) := by
  have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  exact MemLp.of_bound hc.aestronglyMeasurable M (ae_of_all _ hM)

private lemma continuous_divergence {ψ : Rn n → Rn n} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (divergence ψ) := by
  have e : divergence ψ = fun x => ∑ i, fderiv ℝ ψ x (EuclideanSpace.single i 1) i :=
    funext fun x => divergence_eq_sum ψ x
  have hc := hψ.continuous_fderiv (by simp)
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    (EuclideanSpace.proj i : Rn n →L[ℝ] ℝ).continuous.comp (hc.clm_apply continuous_const)

private lemma hasCompactSupport_divergence {ψ : Rn n → Rn n} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (divergence ψ) :=
  HasCompactSupport.intro hψ fun x hx => by
    rw [divergence, fderiv_of_notMem_tsupport ℝ hx]
    simp

/-! ### Assembly -/

/-- **Rellich–Kondrachov with compact trace** (compare Evans–Gariepy, Thms 4.11 and 4.6). The
proof has no extension across the sphere:
* strong `L²(B₁)` convergence: local Rellich on the open ball gives `L²_loc(B₁)` convergence,
  and the shell estimate `lintegral_shell_sq_le` makes the sequence Cauchy in `L²(B₁)`;
* strong `L²(σ)` convergence of the traces: the trace inequality `lintegral_sphere_sq_le` applied
  to differences makes them Cauchy in `L²(σ)`;
* weak `L²(B₁)` convergence of the gradients: `exists_tendstoWeakL2_subseq`;
* the weak-gradient identity: integration by parts for Lipschitz functions
  (`integral_mul_divergence_eq_neg`), passed to the limit.

It does not identify `Ftr` with the trace of `F` (not part of the statement). -/
theorem rellich_trace_weak_compactness [NeZero n] :
    RellichTraceStatement n := by
  intro f C hLip hbd
  choose L hL using hLip
  have : IsFiniteMeasure (volume.restrict (ball (0 : Rn n) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hC0 : 0 ≤ C := (integral_nonneg fun y => by positivity).trans (hbd 0)
  have hfacts := fun k => ball_facts (hL k) (hbd k)
  have hfL2 : ∀ k, eLpNorm (f k) 2 (volume.restrict (ball (0 : Rn n) 1)) ≤ ENNReal.ofReal √C :=
    fun k => le_ofReal_sqrt hC0 (by
      rw [sq_eLpNorm_two_real _ (hfacts k).1.aestronglyMeasurable]; exact (hfacts k).2.2.1)
  have hgL2 : ∀ k, eLpNorm (gradient (f k)) 2 (volume.restrict (ball (0 : Rn n) 1)) ≤
      ENNReal.ofReal √C :=
    fun k => le_ofReal_sqrt hC0 (by
      rw [sq_eLpNorm_two _ (hfacts k).2.1.aestronglyMeasurable]; exact (hfacts k).2.2.2)
  -- Step 2: `L²_loc(B₁)` convergence (local Rellich on the open ball).
  obtain ⟨φ₁, hφ₁, u₀, hu₀, hconv⟩ := exists_tendstoLpLoc_subseq_of_H1Loc isOpen_ball f
    (fun k => gradient (f k))
    (fun k => memH1Loc_gradient_of_locallyLipschitzOn isOpen_ball (locallyLipschitzOn_ball (hL k)))
    (fun K hK _ => ⟨√C, fun k =>
      ⟨(eLpNorm_mono_measure _ (Measure.restrict_mono hK le_rfl)).trans (hfL2 k),
        (eLpNorm_mono_measure _ (Measure.restrict_mono hK le_rfl)).trans (hgL2 k)⟩⟩)
  have hpair := fun j k => pair_energy (hL j) (hL k) (hfacts j).2.2.1 (hfacts j).2.2.2
    (hfacts k).2.2.1 (hfacts k).2.2.2
  -- Step 2: the subsequence is Cauchy in `L²(B₁)` (shell estimate near the sphere).
  have hballC : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ j ≥ N, ∀ k ≥ N,
      ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal ((f (φ₁ j) y - f (φ₁ k) y) ^ 2) ≤
        ENNReal.ofReal ε := by
    intro ε hε
    set δ : ℝ := min (1 / 2) (ε / (2 * (2 ^ n * (12 * C) + 1))) with hδdef
    have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
    have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
    have hδε : δ * (2 ^ n * (12 * C)) ≤ ε / 2 := by
      have h1 : δ ≤ ε / (2 * (2 ^ n * (12 * C) + 1)) := min_le_right _ _
      have hpos : 0 < 2 * (2 ^ n * (12 * C) + 1) := by positivity
      rw [le_div_iff₀ hpos] at h1
      linarith [(by positivity : (0 : ℝ) ≤ 2 ^ n * (12 * C))]
    set K := closedBall (0 : Rn n) (1 - δ) with hKdef
    have hKsub : K ⊆ ball 0 1 := closedBall_subset_ball (by linarith)
    have hKc : IsCompact K := isCompact_closedBall _ _
    set η : ℝ := min 1 (ε / 8) with hηdef
    have hη0 : 0 < η := lt_min one_pos (by positivity)
    have hηε : (2 * η) ^ 2 ≤ ε / 2 := by
      have h1 : η ≤ 1 := min_le_left _ _
      have h2 : η ≤ ε / 8 := min_le_right _ _
      nlinarith
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1
      (hconv K hKsub hKc)) (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη0))
    refine ⟨N, fun j hj k hk => ?_⟩
    set g : Rn n → ℝ := fun y => f (φ₁ j) y - f (φ₁ k) y with hgdef
    have hgL : LipschitzOnWith (L (φ₁ j) + L (φ₁ k)) g (closedBall 0 1) :=
      (hL (φ₁ j)).sub (hL (φ₁ k))
    have hKpart : ∫⁻ y in K, ENNReal.ofReal (g y ^ 2) ≤ ENNReal.ofReal (ε / 2) := by
      have hm : ∀ i, AEStronglyMeasurable (f (φ₁ i) - u₀) (volume.restrict K) := fun i =>
        (((hL _).continuousOn.mono (hKsub.trans ball_subset_closedBall)).aestronglyMeasurable
          hKc.measurableSet).sub hu₀.aestronglyMeasurable
      have hsplit : g = (f (φ₁ j) - u₀) - (f (φ₁ k) - u₀) := by
        funext y; simp [hgdef]
      have hle : eLpNorm g 2 (volume.restrict K) ≤ ENNReal.ofReal (2 * η) := by
        rw [hsplit]
        refine (eLpNorm_sub_le (by norm_num)).trans
          ((add_le_add (hN j hj) (hN k hk)).trans_eq ?_)
        rw [← ENNReal.ofReal_add hη0.le hη0.le]
        ring_nf
      rw [← sq_eLpNorm_two_real _ (by rw [hsplit]; exact (hm j).sub (hm k))]
      calc eLpNorm g 2 (volume.restrict K) ^ 2 ≤ ENNReal.ofReal (2 * η) ^ 2 :=
            pow_le_pow_left₀ bot_le hle 2
        _ = ENNReal.ofReal ((2 * η) ^ 2) := (ENNReal.ofReal_pow (by positivity) 2).symm
        _ ≤ ENNReal.ofReal (ε / 2) := ENNReal.ofReal_le_ofReal hηε
    have hshell : ∫⁻ y in ball (0 : Rn n) 1 \ K, ENNReal.ofReal (g y ^ 2) ≤
        ENNReal.ofReal (ε / 2) := by
      refine (lintegral_shell_sq_le hgL hδ2).trans ?_
      have hA : ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
          ENNReal.ofReal (g y ^ 2 + 2 * |g y| * ‖gradient g y‖) ≤ ENNReal.ofReal (12 * C) := by
        refine (annulus_density_le one_pos).trans ?_
        obtain ⟨h1, h2⟩ := hpair (φ₁ j) (φ₁ k)
        calc _ ≤ ENNReal.ofReal (1 + 1) * ENNReal.ofReal (4 * C) +
              ENNReal.ofReal 1⁻¹ * ENNReal.ofReal (4 * C) := by gcongr
          _ = ENNReal.ofReal (12 * C) := by
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 + 1),
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1⁻¹),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1
            ring
      calc ENNReal.ofReal δ * (2 ^ n * ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
            ENNReal.ofReal (g y ^ 2 + 2 * |g y| * ‖gradient g y‖))
          ≤ ENNReal.ofReal δ * (2 ^ n * ENNReal.ofReal (12 * C)) := by gcongr
        _ = ENNReal.ofReal (δ * (2 ^ n * (12 * C))) := by
          rw [ENNReal.ofReal_mul hδ0.le, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n),
            ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        _ ≤ ENNReal.ofReal (ε / 2) := ENNReal.ofReal_le_ofReal hδε
    calc ∫⁻ y in ball (0 : Rn n) 1, ENNReal.ofReal ((f (φ₁ j) y - f (φ₁ k) y) ^ 2)
        = ∫⁻ y in K ∪ (ball 0 1 \ K), ENNReal.ofReal (g y ^ 2) := by
          rw [union_sdiff_cancel hKsub]
      _ ≤ (∫⁻ y in K, ENNReal.ofReal (g y ^ 2)) +
          ∫⁻ y in ball 0 1 \ K, ENNReal.ofReal (g y ^ 2) := lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hKpart hshell
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  -- Step 4: the traces are Cauchy in `L²(σ)` (trace inequality applied to differences).
  have htrC : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ j ≥ N, ∀ k ≥ N,
      ∫⁻ z, ENNReal.ofReal ((f (φ₁ j) (z : Rn n) - f (φ₁ k) (z : Rn n)) ^ 2) ∂sphereMeasure n ≤
        ENNReal.ofReal ε := by
    intro ε hε
    set lam : ℝ := 2 ^ (n + 3) * C / ε + 1 with hlamdef
    have hlam0 : 0 < lam := by positivity
    have hlamε : 2 ^ n * (lam⁻¹ * (4 * C)) ≤ ε / 2 := by
      have key : lam * (ε / 2) = 2 ^ n * (4 * C) + ε / 2 := by
        rw [hlamdef, pow_add]; field_simp; ring
      calc 2 ^ n * (lam⁻¹ * (4 * C)) = lam⁻¹ * (2 ^ n * (4 * C)) := by ring
        _ ≤ lam⁻¹ * (lam * (ε / 2)) :=
          mul_le_mul_of_nonneg_left (by rw [key]; linarith) (inv_nonneg.2 hlam0.le)
        _ = ε / 2 := by field_simp
    set ε' : ℝ := ε / (2 * (2 ^ n * (1 + lam))) with hε'def
    have hε' : 0 < ε' := by positivity
    have he1 : 2 ^ n * ((1 + lam) * ε') = ε / 2 := by
      rw [hε'def]; field_simp
    obtain ⟨N, hN⟩ := hballC ε' hε'
    refine ⟨N, fun j hj k hk => ?_⟩
    have hgL : LipschitzOnWith (L (φ₁ j) + L (φ₁ k)) (fun y => f (φ₁ j) y - f (φ₁ k) y)
        (closedBall 0 1) := (hL (φ₁ j)).sub (hL (φ₁ k))
    obtain ⟨-, h2⟩ := hpair (φ₁ j) (φ₁ k)
    calc ∫⁻ z, ENNReal.ofReal ((f (φ₁ j) (z : Rn n) - f (φ₁ k) (z : Rn n)) ^ 2) ∂sphereMeasure n
        ≤ 2 ^ n * ∫⁻ y in ball (0 : Rn n) 1 \ ball 0 (1 / 2),
            ENNReal.ofReal ((f (φ₁ j) y - f (φ₁ k) y) ^ 2 + 2 * |f (φ₁ j) y - f (φ₁ k) y| *
              ‖gradient (fun x => f (φ₁ j) x - f (φ₁ k) x) y‖) := lintegral_sphere_sq_le hgL
      _ ≤ 2 ^ n * (ENNReal.ofReal (1 + lam) * ENNReal.ofReal ε' +
            ENNReal.ofReal lam⁻¹ * ENNReal.ofReal (4 * C)) := by
          gcongr
          refine (annulus_density_le hlam0).trans ?_
          gcongr
          exact hN j hj k hk
      _ = ENNReal.ofReal (2 ^ n * ((1 + lam) * ε' + lam⁻¹ * (4 * C))) := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n),
            ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ (1 + lam) * ε') (by positivity),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 + lam),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ lam⁻¹)]
      _ ≤ ENNReal.ofReal ε := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_add, he1]
          linarith
  obtain ⟨F, hFm, hFt⟩ := exists_memLp_tendsto_integral_sq
    (μ := volume.restrict (ball (0 : Rn n) 1)) (fun k => f (φ₁ k)) (fun k => (hfacts (φ₁ k)).1)
    hballC
  obtain ⟨Ftr, hTm, hTt⟩ := exists_memLp_tendsto_integral_sq (μ := sphereMeasure n)
    (fun k (z : sphere (0 : Rn n) 1) => f (φ₁ k) z) (fun k => memLp_sphere (hL (φ₁ k))) htrC
  -- Step 5: weak `L²` limit of the gradients.
  obtain ⟨φ₂, hφ₂, G, hGw⟩ := exists_tendstoWeakL2_subseq volume (ball (0 : Rn n) 1)
    (fun k => gradient (f (φ₁ k))) √C (fun k => (hfacts (φ₁ k)).2.1) (fun k => hgL2 (φ₁ k))
  refine ⟨fun k => φ₁ (φ₂ k), hφ₁.comp hφ₂, F, Ftr, G, hFm, hTm, hGw.2.1,
    hFt.comp hφ₂.tendsto_atTop, hTt.comp hφ₂.tendsto_atTop, hGw.2.2, ?_⟩
  intro ψ hψ
  have hψm : MemLp ψ 2 (volume.restrict (ball (0 : Rn n) 1)) :=
    memLp_two_ball hψ.1.continuous hψ.2.1
  have hdiv : MemLp (divergence ψ) 2 (volume.restrict (ball (0 : Rn n) 1)) :=
    memLp_two_ball (continuous_divergence (hψ.1.of_le (by simp)))
      (hasCompactSupport_divergence hψ.2.1)
  have hIBP : ∀ k, ∫ y in ball (0 : Rn n) 1, f (φ₁ (φ₂ k)) y * divergence ψ y =
      -∫ y in ball (0 : Rn n) 1, ⟪gradient (f (φ₁ (φ₂ k))) y, ψ y⟫ := fun k =>
    integral_mul_divergence_eq_neg isOpen_ball (locallyLipschitzOn_ball (hL _)) hψ
  have hlimL : Tendsto (fun k => ∫ y in ball (0 : Rn n) 1, f (φ₁ (φ₂ k)) y * divergence ψ y)
      atTop (𝓝 (∫ y in ball (0 : Rn n) 1, F y * divergence ψ y)) :=
    tendsto_integral_mul (fun k => (hfacts (φ₁ (φ₂ k))).1) hFm hdiv
      (hFt.comp hφ₂.tendsto_atTop)
  have hlimR : Tendsto (fun k => -∫ y in ball (0 : Rn n) 1, ⟪gradient (f (φ₁ (φ₂ k))) y, ψ y⟫)
      atTop (𝓝 (-∫ y in ball (0 : Rn n) 1, ⟪G y, ψ y⟫)) :=
    (hGw.2.2 ψ hψm).neg
  exact tendsto_nhds_unique (Tendsto.congr hIBP hlimL) hlimR

end GMTFoundations
