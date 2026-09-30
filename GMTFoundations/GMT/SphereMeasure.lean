/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Setup
import GMTFoundations.GMT.HausdorffLebesgue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The sphere measure is normalized Hausdorff measure

`map_sphereMeasure_eq_hausdorffN_of`: the surface measure `sphereMeasure n = volume.toSphere`,
pushed forward to `ℝⁿ`, is the normalized Hausdorff measure `ℋ^{n-1}⌊S^{n-1}`.

It takes the normalization `ℋ^{n-1} = ℒ^{n-1}` on `ℝ^{n-1}`
(`hausdorffN (n - 1) (n - 1) = volume`) as a hypothesis; `map_sphereMeasure_eq_hausdorffN`
discharges it with `hausdorffN_self_eq_volume`. The auxiliary declarations are in the namespace
`GMTFoundations.GMT.SphereMeasure`.

## Proof

Write `n = m + 1`, `σ` for the pushed-forward sphere measure, `τ = ℋ^m⌊S^m` and
`x = (x', x_n) ∈ ℝ^m × ℝ`. For `0 < r < 1` let `h = 1 - r²/2`, `ρ = √(1 - h²)` and
`V = |B̄_ρ^m|`. The cap `S ∩ B̄_r(e_n)` is `{ω ∈ S : ω_n ≥ h}`.

1. *Cap bounds for `τ`.* The projection `x ↦ x'` is `1`-Lipschitz and maps the cap onto
   `B̄_ρ^m`. The graph map `y ↦ (y, √(1 - |y|²))` is `1/h`-Lipschitz on `B̄_ρ^m` and maps it onto
   the cap. Since `ℋ^m = ℒ^m` on `ℝ^m`: `V ≤ τ(cap) ≤ h^{-m} V`.
2. *Cap bounds for `σ`.* `σ(A) = (m+1) |(0,1) · (A ∩ S)|`. The cone over the cap contains
   `{0 < x_n < h, |x'| < (ρ/h) x_n}` and lies in `{0 < x_n < 1, |x'| ≤ (ρ/h) x_n}`, whose volumes
   are computed by Fubini. This gives `h V ≤ σ(cap) ≤ h^{-m} V`.
3. *Rotations.* A reflection maps any `x ∈ S` to `e_n`, and both measures are invariant under
   linear isometries. So the bounds hold for caps around every point of `S`.
4. *Comparison.* For `a < 1` and every `x`, `a σ(B̄(x,r)) ≤ τ(B̄(x,r))` and
   `a τ(B̄(x,r)) ≤ σ(B̄(x,r))` for small `r`. The Besicovitch Vitali family
   (`VitaliFamily.measure_le_of_frequently_le`) turns this into `σ ≤ τ` and `τ ≤ σ`.

No uniqueness theorem for rotation-invariant measures is needed. The case `n = 1` is covered by
the same argument (`ℝ⁰` is a point).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace GMTFoundations.GMT

/-! Auxiliary declarations live in `GMTFoundations.GMT.SphereMeasure`. -/

namespace SphereMeasure

variable {m : ℕ}

/-! ### Coordinates `ℝ^{m+1} = ℝ^m × ℝ` -/

/-- The first `m` coordinates of a point of `ℝ^{m+1}`. -/
def headCoords (x : Rn (m + 1)) : Rn m := WithLp.toLp 2 fun i => x (Fin.castSucc i)

/-- The point `(y, t) ∈ ℝ^{m+1}`. -/
def snocCoords (y : Rn m) (t : ℝ) : Rn (m + 1) := WithLp.toLp 2 (Fin.snoc (fun i => y i) t)

@[simp] lemma headCoords_apply (x : Rn (m + 1)) (i : Fin m) :
    headCoords x i = x i.castSucc := rfl

@[simp] lemma headCoords_snocCoords (y : Rn m) (t : ℝ) : headCoords (snocCoords y t) = y := by
  ext i; simp [snocCoords]

@[simp] lemma snocCoords_last (y : Rn m) (t : ℝ) : snocCoords y t (Fin.last m) = t := by
  simp [snocCoords]

@[simp] lemma headCoords_sub (x y : Rn (m + 1)) :
    headCoords (x - y) = headCoords x - headCoords y := by
  ext i; simp

@[simp] lemma headCoords_smul (a : ℝ) (x : Rn (m + 1)) :
    headCoords (a • x) = a • headCoords x := by
  ext i; simp

lemma snocCoords_headCoords (x : Rn (m + 1)) :
    snocCoords (headCoords x) (x (Fin.last m)) = x := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [snocCoords]

lemma norm_sq_eq_headCoords (x : Rn (m + 1)) :
    ‖x‖ ^ 2 = ‖headCoords x‖ ^ 2 + x (Fin.last m) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  rfl

lemma norm_sq_snocCoords (y : Rn m) (t : ℝ) : ‖snocCoords y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  simpa using norm_sq_eq_headCoords (snocCoords y t)

lemma norm_headCoords_le (x : Rn (m + 1)) : ‖headCoords x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_headCoords x
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by linarith [sq_nonneg (x (Fin.last m))])

lemma lipschitzWith_headCoords : LipschitzWith 1 (headCoords : Rn (m + 1) → Rn m) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa [dist_eq_norm] using norm_headCoords_le (x - y)

/-- `x ↦ (x_n, x')` is volume preserving from `ℝ^{m+1}` to `ℝ × ℝ^m`. -/
lemma measurePreserving_lastHead :
    MeasurePreserving (fun x : Rn (m + 1) => (x (Fin.last m), headCoords x)) := by
  have h1 := PiLp.volume_preserving_ofLp (Fin (m + 1))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin m))
  convert (h3.comp h2).comp h1 using 1
  funext x
  refine Prod.ext rfl ?_
  ext i
  simp [headCoords, MeasurableEquiv.piFinSuccAbove, Fin.init]

/-! ### Volumes of cones -/

/-- Fubini in the last coordinate. -/
lemma volume_setOf_last_head {a : ℝ} (S : ℝ → Set (Rn m))
    (hK : MeasurableSet {p : ℝ × Rn m | p.1 ∈ Ioo 0 a ∧ p.2 ∈ S p.1}) :
    volume {x : Rn (m + 1) | x (Fin.last m) ∈ Ioo 0 a ∧ headCoords x ∈ S (x (Fin.last m))} =
      ∫⁻ t in Ioo 0 a, volume (S t) := by
  have hpre : {x : Rn (m + 1) | x (Fin.last m) ∈ Ioo 0 a ∧ headCoords x ∈ S (x (Fin.last m))} =
      (fun x : Rn (m + 1) => (x (Fin.last m), headCoords x)) ⁻¹'
        {p : ℝ × Rn m | p.1 ∈ Ioo 0 a ∧ p.2 ∈ S p.1} := rfl
  rw [hpre, measurePreserving_lastHead.measure_preimage hK.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply hK, ← lintegral_indicator measurableSet_Ioo]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ Ioo 0 a
  · rw [indicator_of_mem ht]
    congr 1
    ext y
    exact ⟨fun hy => hy.2, fun hy => ⟨ht, hy⟩⟩
  · rw [indicator_of_notMem ht]
    convert measure_empty (μ := (volume : Measure (Rn m)))
    ext y
    exact ⟨fun hy => (ht hy.1).elim, fun hy => hy.elim⟩

lemma lintegral_Ioo_mul_pow {k a : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a) :
    ∫⁻ t in Ioo 0 a, ENNReal.ofReal ((k * t) ^ m) =
      ENNReal.ofReal (k ^ m * a ^ (m + 1) / (m + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ha]
    simp [mul_pow, integral_pow]
    ring
  · exact (by fun_prop : Continuous fun t : ℝ => (k * t) ^ m).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  · exact ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => by
      have := ht.1.le
      positivity

/-- Volume of the open cone `{0 < x_n < a, |x'| < k x_n}`. -/
lemma volume_cone_ball {k a : ℝ} (hk : 0 < k) (ha : 0 ≤ a) :
    volume {x : Rn (m + 1) | x (Fin.last m) ∈ Ioo 0 a ∧
        headCoords x ∈ ball 0 (k * x (Fin.last m))} =
      ENNReal.ofReal (k ^ m * a ^ (m + 1) / (m + 1)) * volume (ball (0 : Rn m) 1) := by
  rw [volume_setOf_last_head (fun t => ball 0 (k * t))]
  · rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun t =>
        ENNReal.ofReal ((k * t) ^ m) * volume (ball (0 : Rn m) 1)) fun t ht => by
      rw [Measure.addHaar_ball_of_pos _ _ (mul_pos hk ht.1), finrank_euclideanSpace_fin]]
    rw [lintegral_mul_const _ (by fun_prop), lintegral_Ioo_mul_pow hk.le ha]
  · convert ((measurableSet_Ioo (a := (0 : ℝ)) (b := a)).preimage measurable_fst).inter
      (measurableSet_lt (f := fun p : ℝ × Rn m => ‖p.2‖) (g := fun p => k * p.1)
        (by fun_prop) (by fun_prop)) using 1
    ext p
    simp

/-- Volume of the closed cone `{0 < x_n < a, |x'| ≤ k x_n}`. -/
lemma volume_cone_closedBall {k a : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a) :
    volume {x : Rn (m + 1) | x (Fin.last m) ∈ Ioo 0 a ∧
        headCoords x ∈ closedBall 0 (k * x (Fin.last m))} =
      ENNReal.ofReal (k ^ m * a ^ (m + 1) / (m + 1)) * volume (ball (0 : Rn m) 1) := by
  rw [volume_setOf_last_head (fun t => closedBall 0 (k * t))]
  · rw [setLIntegral_congr_fun measurableSet_Ioo (g := fun t =>
        ENNReal.ofReal ((k * t) ^ m) * volume (ball (0 : Rn m) 1)) fun t ht => by
      rw [Measure.addHaar_closedBall _ _ (mul_nonneg hk ht.1.le), finrank_euclideanSpace_fin]]
    rw [lintegral_mul_const _ (by fun_prop), lintegral_Ioo_mul_pow hk ha]
  · convert ((measurableSet_Ioo (a := (0 : ℝ)) (b := a)).preimage measurable_fst).inter
      (measurableSet_le (f := fun p : ℝ × Rn m => ‖p.2‖) (g := fun p => k * p.1)
        (by fun_prop) (by fun_prop)) using 1
    ext p
    simp

/-! ### Caps around the north pole -/

/-- The north pole `e_n`. -/
def north : Rn (m + 1) := snocCoords 0 1

/-- The cap `{ω ∈ S^m : ω_n ≥ h}`. -/
def cap (m : ℕ) (h : ℝ) : Set (Rn (m + 1)) := {ω | ‖ω‖ = 1 ∧ h ≤ ω (Fin.last m)}

lemma sphere_inter_closedBall_north {r : ℝ} (hr : 0 ≤ r) :
    sphere (0 : Rn (m + 1)) 1 ∩ closedBall north r = cap m (1 - r ^ 2 / 2) := by
  ext ω
  simp only [mem_inter_iff, mem_sphere_zero_iff_norm, mem_closedBall, dist_eq_norm, cap,
    mem_ofPred_eq]
  refine and_congr_right fun hω => ?_
  have h1 := norm_sq_eq_headCoords ω
  have h2 := norm_sq_eq_headCoords (ω - north)
  simp only [headCoords_sub, north, headCoords_snocCoords, sub_zero, PiLp.sub_apply,
    snocCoords_last] at h2
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero]
  unfold north
  rw [h2]
  rw [hω] at h1
  constructor <;> intro h <;> linarith

/-- The upper hemisphere as a graph over the unit ball of `ℝ^m`. -/
def graphUp (y : Rn m) : Rn (m + 1) := snocCoords y (√(1 - ‖y‖ ^ 2))

section CapGeometry

variable {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
include hh0 hh1

lemma sqrt_one_sub_sq_sq : √(1 - h ^ 2) ^ 2 = 1 - h ^ 2 :=
  Real.sq_sqrt (sub_nonneg.2 (pow_le_one₀ hh0.le hh1.le))

lemma graphUp_mapsTo : MapsTo graphUp (closedBall (0 : Rn m) √(1 - h ^ 2)) (cap m h) := by
  intro y hy
  rw [mem_closedBall_zero_iff] at hy
  have hρ := sqrt_one_sub_sq_sq hh0 hh1
  have hy2 : ‖y‖ ^ 2 ≤ 1 - h ^ 2 := by
    rw [← hρ]; exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hs : 0 ≤ 1 - ‖y‖ ^ 2 := by linarith [sq_nonneg h]
  refine ⟨?_, ?_⟩
  · have := norm_sq_snocCoords y (√(1 - ‖y‖ ^ 2))
    rw [Real.sq_sqrt hs] at this
    have h' : ‖graphUp y‖ ^ 2 = 1 ^ 2 := by rw [graphUp, this]; ring
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h'
  · simp only [graphUp, snocCoords_last]
    rw [show h = √(h ^ 2) from (Real.sqrt_sq hh0.le).symm]
    exact Real.sqrt_le_sqrt (by linarith)

lemma cap_subset_image_graphUp :
    cap m h ⊆ graphUp '' closedBall (0 : Rn m) √(1 - h ^ 2) := by
  rintro ω ⟨hω, hωh⟩
  have h1 := norm_sq_eq_headCoords ω
  rw [hω] at h1
  refine ⟨headCoords ω, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  · rw [graphUp, show 1 - ‖headCoords ω‖ ^ 2 = ω (Fin.last m) ^ 2 by linarith,
      Real.sqrt_sq (by linarith), snocCoords_headCoords]

lemma closedBall_subset_image_headCoords :
    closedBall (0 : Rn m) √(1 - h ^ 2) ⊆ headCoords '' cap m h :=
  fun y hy => ⟨graphUp y, graphUp_mapsTo hh0 hh1 hy, headCoords_snocCoords _ _⟩

lemma lipschitzOnWith_graphUp :
    LipschitzOnWith (Real.toNNReal (1 / h)) graphUp (closedBall (0 : Rn m) √(1 - h ^ 2)) := by
  have hρ := sqrt_one_sub_sq_sq hh0 hh1
  have hρ0 : 0 ≤ √(1 - h ^ 2) := Real.sqrt_nonneg _
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  have hφy' : h ≤ √(1 - ‖y‖ ^ 2) := by
    have := (graphUp_mapsTo hh0 hh1 hy).2
    rwa [graphUp, snocCoords_last] at this
  have hφz' : h ≤ √(1 - ‖z‖ ^ 2) := by
    have := (graphUp_mapsTo hh0 hh1 hz).2
    rwa [graphUp, snocCoords_last] at this
  rw [mem_closedBall_zero_iff] at hy hz
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  have hsq := norm_sq_eq_headCoords (graphUp y - graphUp z)
  have hG0 := norm_nonneg (graphUp y - graphUp z)
  generalize ‖graphUp y - graphUp z‖ = G at hsq hG0 ⊢
  simp only [headCoords_sub, graphUp, headCoords_snocCoords, PiLp.sub_apply,
    snocCoords_last] at hsq
  have hy2 : ‖y‖ ^ 2 ≤ 1 - h ^ 2 := by rw [← hρ]; exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hz2 : ‖z‖ ^ 2 ≤ 1 - h ^ 2 := by rw [← hρ]; exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hφy : √(1 - ‖y‖ ^ 2) ^ 2 = 1 - ‖y‖ ^ 2 := Real.sq_sqrt (by linarith [sq_nonneg h])
  have hφz : √(1 - ‖z‖ ^ 2) ^ 2 = 1 - ‖z‖ ^ 2 := Real.sq_sqrt (by linarith [sq_nonneg h])
  generalize √(1 - ‖y‖ ^ 2) = φy at *
  generalize √(1 - ‖z‖ ^ 2) = φz at *
  generalize √(1 - h ^ 2) = ρ at *
  -- `h |φy - φz| ≤ ρ ‖y - z‖`
  have hdiff : |‖z‖ - ‖y‖| ≤ ‖y - z‖ := by
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le y z
  have key : h * |φy - φz| ≤ ρ * ‖y - z‖ := by
    have e1 : (φy - φz) * (φy + φz) = (‖z‖ - ‖y‖) * (‖z‖ + ‖y‖) := by
      linear_combination hφy - hφz
    have e2 : |φy - φz| * (φy + φz) = |‖z‖ - ‖y‖| * (‖z‖ + ‖y‖) := by
      rw [← abs_of_nonneg (show 0 ≤ φy + φz by linarith), ← abs_mul, e1, abs_mul,
        abs_of_nonneg (show 0 ≤ ‖z‖ + ‖y‖ by positivity)]
    have e3 : |‖z‖ - ‖y‖| * (‖z‖ + ‖y‖) ≤ ‖y - z‖ * (2 * ρ) :=
      mul_le_mul hdiff (by linarith) (by positivity) (norm_nonneg _)
    linarith [mul_le_mul_of_nonneg_left (by linarith : 2 * h ≤ φy + φz) (abs_nonneg (φy - φz))]
  have hkey2 : h ^ 2 * (φy - φz) ^ 2 ≤ ρ ^ 2 * ‖y - z‖ ^ 2 := by
    have := mul_self_le_mul_self (by positivity) key
    rw [← sq_abs (φy - φz)]
    linarith [show h ^ 2 * |φy - φz| ^ 2 = h * |φy - φz| * (h * |φy - φz|) by ring,
      show ρ ^ 2 * ‖y - z‖ ^ 2 = ρ * ‖y - z‖ * (ρ * ‖y - z‖) by ring]
  have hfin : (h * G) ^ 2 ≤ ‖y - z‖ ^ 2 := by
    have e : (h * G) ^ 2 = h ^ 2 * ‖y - z‖ ^ 2 + h ^ 2 * (φy - φz) ^ 2 := by
      rw [mul_pow, hsq]; ring
    have e' : ρ ^ 2 * ‖y - z‖ ^ 2 = (1 - h ^ 2) * ‖y - z‖ ^ 2 := by rw [hρ]
    rw [e]
    linarith
  have : h * G ≤ ‖y - z‖ :=
    (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hfin
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hh0]
  linarith

/-- The open cone over the cap contains `{0 < x_n < h, |x'| < (ρ/h) x_n}`. -/
lemma cone_ball_subset :
    {x : Rn (m + 1) | x (Fin.last m) ∈ Ioo 0 h ∧
        headCoords x ∈ ball 0 (√(1 - h ^ 2) / h * x (Fin.last m))} ⊆
      Ioo (0 : ℝ) 1 • cap m h := by
  rintro x ⟨⟨ht0, hth⟩, hx⟩
  rw [mem_ball_zero_iff] at hx
  have hρ := sqrt_one_sub_sq_sq hh0 hh1
  set t := x (Fin.last m)
  set ρ := √(1 - h ^ 2)
  have h1 := norm_sq_eq_headCoords x
  have hx' : h * ‖headCoords x‖ < ρ * t := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hh0] at hx; linarith
  have hx2 : h ^ 2 * ‖headCoords x‖ ^ 2 < ρ ^ 2 * t ^ 2 := by
    have := mul_self_lt_mul_self (by positivity) hx'
    linarith
  have hxt : t ≤ ‖x‖ := (le_abs_self t).trans
    (abs_le_of_sq_le_sq (by linarith [sq_nonneg ‖headCoords x‖]) (norm_nonneg x))
  have hx0 : 0 < ‖x‖ := ht0.trans_le hxt
  have hhx : h * ‖x‖ < t := by
    rw [hρ] at hx2
    have : (h * ‖x‖) ^ 2 < t ^ 2 := by rw [mul_pow, h1]; linarith
    exact (pow_lt_pow_iff_left₀ (by positivity) ht0.le two_ne_zero).1 this
  refine Set.mem_smul.2 ⟨‖x‖, ⟨hx0, ?_⟩, ‖x‖⁻¹ • x, ⟨?_, ?_⟩, ?_⟩
  · exact lt_of_mul_lt_mul_left (by linarith : h * ‖x‖ < h * 1) hh0.le
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne']
  · rw [PiLp.smul_apply, smul_eq_mul, inv_mul_eq_div, le_div_iff₀ hx0]
    linarith
  · rw [smul_inv_smul₀ hx0.ne']

/-- The open cone over the cap lies in `{0 < x_n < 1, |x'| ≤ (ρ/h) x_n}`. -/
lemma cone_subset_closedBall :
    Ioo (0 : ℝ) 1 • cap m h ⊆
      {x : Rn (m + 1) | x (Fin.last m) ∈ Ioo 0 1 ∧
        headCoords x ∈ closedBall 0 (√(1 - h ^ 2) / h * x (Fin.last m))} := by
  rintro _ ⟨a, ⟨ha0, ha1⟩, ω, ⟨hω, hωh⟩, rfl⟩
  have hρ := sqrt_one_sub_sq_sq hh0 hh1
  have h1 := norm_sq_eq_headCoords ω
  rw [hω] at h1
  have hωn : ω (Fin.last m) ≤ 1 := (le_abs_self _).trans
    (abs_le_of_sq_le_sq (by linarith [sq_nonneg ‖headCoords ω‖]) zero_le_one)
  have hhead : ‖headCoords ω‖ ≤ √(1 - h ^ 2) :=
    Real.le_sqrt_of_sq_le (by linarith [pow_le_pow_left₀ hh0.le hωh 2])
  simp only [mem_ofPred_eq, PiLp.smul_apply, smul_eq_mul, headCoords_smul,
    mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha0, mem_Ioo]
  refine ⟨⟨mul_pos ha0 (hh0.trans_le hωh), (mul_le_of_le_one_right ha0.le hωn).trans_lt ha1⟩, ?_⟩
  rw [div_mul_eq_mul_div, le_div_iff₀ hh0]
  have := mul_le_mul hhead hωh hh0.le (Real.sqrt_nonneg _)
  linarith [mul_le_mul_of_nonneg_left this ha0.le]

end CapGeometry

/-! ### The two measures -/

/-- The sphere measure pushed forward to `ℝ^{m+1}`. -/
abbrev sigmaN (m : ℕ) : Measure (Rn (m + 1)) := (sphereMeasure (m + 1)).map Subtype.val

/-- Normalized `ℋ^m` restricted to the unit sphere of `ℝ^{m+1}`. -/
abbrev tauN (m : ℕ) : Measure (Rn (m + 1)) :=
  (hausdorffN (m + 1) m).restrict (sphere (0 : Rn (m + 1)) 1)

lemma sigmaN_apply {A : Set (Rn (m + 1))} (hA : MeasurableSet A) :
    sigmaN m A = ((m : ℝ≥0∞) + 1) * volume (Ioo (0 : ℝ) 1 • (sphere (0 : Rn (m + 1)) 1 ∩ A)) := by
  rw [sigmaN, Measure.map_apply measurable_subtype_coe hA, sphereMeasure,
    Measure.toSphere_apply' _ (measurable_subtype_coe hA), Subtype.image_preimage_coe,
    finrank_euclideanSpace_fin]
  push_cast
  rfl

lemma tauN_apply (A : Set (Rn (m + 1))) :
    tauN m A = hausdorffN (m + 1) m (sphere (0 : Rn (m + 1)) 1 ∩ A) := by
  rw [tauN, Measure.restrict_apply' isClosed_sphere.measurableSet, inter_comm]

lemma natCast_add_one_mul_ofReal_div (X : ℝ) :
    ((m : ℝ≥0∞) + 1) * ENNReal.ofReal (X / (m + 1)) = ENNReal.ofReal X := by
  rw [show ((m : ℝ≥0∞) + 1) = ENNReal.ofReal ((m : ℝ) + 1) by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]; simp,
    ← ENNReal.ofReal_mul (by positivity), mul_div_cancel₀ _ (by positivity)]

lemma hausdorffN_apply (n d : ℕ) (s : Set (Rn n)) :
    hausdorffN n d s =
      ENNReal.ofReal (unitBallVolume d / 2 ^ d) * Measure.hausdorffMeasure (d : ℝ) s := by
  rw [hausdorffN, Measure.smul_apply, smul_eq_mul]

section CapBounds

variable {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
include hh0 hh1

omit hh0 hh1 in
lemma volume_closedBall_sqrt :
    volume (closedBall (0 : Rn m) √(1 - h ^ 2)) =
      ENNReal.ofReal (√(1 - h ^ 2) ^ m) * volume (ball (0 : Rn m) 1) := by
  rw [Measure.addHaar_closedBall _ _ (Real.sqrt_nonneg _), finrank_euclideanSpace_fin]

lemma ofReal_mul_le_volume_cone :
    ENNReal.ofReal h * volume (closedBall (0 : Rn m) √(1 - h ^ 2)) ≤
      ((m : ℝ≥0∞) + 1) * volume (Ioo (0 : ℝ) 1 • cap m h) := by
  have hρ : 0 < √(1 - h ^ 2) := Real.sqrt_pos.2 (sub_pos.2 (pow_lt_one₀ hh0.le hh1 two_ne_zero))
  calc ENNReal.ofReal h * volume (closedBall (0 : Rn m) √(1 - h ^ 2))
      = ((m : ℝ≥0∞) + 1) * (ENNReal.ofReal ((√(1 - h ^ 2) / h) ^ m * h ^ (m + 1) / (m + 1)) *
          volume (ball (0 : Rn m) 1)) := by
        rw [volume_closedBall_sqrt, ← mul_assoc, ← mul_assoc,
          natCast_add_one_mul_ofReal_div, ← ENNReal.ofReal_mul hh0.le]
        congr 2
        rw [div_pow]
        field_simp
        ring
    _ = ((m : ℝ≥0∞) + 1) * volume {x : Rn (m + 1) | x (Fin.last m) ∈ Ioo 0 h ∧
          headCoords x ∈ ball 0 (√(1 - h ^ 2) / h * x (Fin.last m))} := by
        rw [volume_cone_ball (by positivity) hh0.le]
    _ ≤ _ := by gcongr; exact cone_ball_subset hh0 hh1

lemma volume_cone_le :
    ((m : ℝ≥0∞) + 1) * volume (Ioo (0 : ℝ) 1 • cap m h) ≤
      ENNReal.ofReal (h ^ m)⁻¹ * volume (closedBall (0 : Rn m) √(1 - h ^ 2)) := by
  calc ((m : ℝ≥0∞) + 1) * volume (Ioo (0 : ℝ) 1 • cap m h)
      ≤ ((m : ℝ≥0∞) + 1) * volume {x : Rn (m + 1) | x (Fin.last m) ∈ Ioo 0 1 ∧
          headCoords x ∈ closedBall 0 (√(1 - h ^ 2) / h * x (Fin.last m))} := by
        gcongr; exact cone_subset_closedBall hh0 hh1
    _ = ((m : ℝ≥0∞) + 1) * (ENNReal.ofReal ((√(1 - h ^ 2) / h) ^ m * 1 ^ (m + 1) / (m + 1)) *
          volume (ball (0 : Rn m) 1)) := by
        rw [volume_cone_closedBall (by positivity) zero_le_one]
    _ = _ := by
        rw [volume_closedBall_sqrt, ← mul_assoc, ← mul_assoc,
          natCast_add_one_mul_ofReal_div, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [one_pow, mul_one, div_pow, div_eq_inv_mul]

lemma volume_closedBall_le_hausdorffN_cap (h02 : hausdorffN m m = (volume : Measure (Rn m))) :
    volume (closedBall (0 : Rn m) √(1 - h ^ 2)) ≤ hausdorffN (m + 1) m (cap m h) := by
  calc volume (closedBall (0 : Rn m) √(1 - h ^ 2))
      = hausdorffN m m (closedBall (0 : Rn m) √(1 - h ^ 2)) := by rw [h02]
    _ ≤ hausdorffN m m (headCoords '' cap m h) :=
        measure_mono (closedBall_subset_image_headCoords hh0 hh1)
    _ ≤ hausdorffN (m + 1) m (cap m h) := by
        rw [hausdorffN_apply, hausdorffN_apply]
        gcongr
        refine (lipschitzWith_headCoords.hausdorffMeasure_image_le (Nat.cast_nonneg _) _).trans ?_
        simp

lemma hausdorffN_cap_le (h02 : hausdorffN m m = (volume : Measure (Rn m))) :
    hausdorffN (m + 1) m (cap m h) ≤
      ENNReal.ofReal (h ^ m)⁻¹ * volume (closedBall (0 : Rn m) √(1 - h ^ 2)) := by
  calc hausdorffN (m + 1) m (cap m h)
      ≤ hausdorffN (m + 1) m (graphUp '' closedBall (0 : Rn m) √(1 - h ^ 2)) :=
        measure_mono (cap_subset_image_graphUp hh0 hh1)
    _ ≤ ENNReal.ofReal (h ^ m)⁻¹ * hausdorffN m m (closedBall (0 : Rn m) √(1 - h ^ 2)) := by
        rw [hausdorffN_apply, hausdorffN_apply, mul_left_comm]
        gcongr
        refine ((lipschitzOnWith_graphUp hh0 hh1).hausdorffMeasure_image_le
          (Nat.cast_nonneg _)).trans (le_of_eq ?_)
        congr 1
        rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by positivity),
          ← ENNReal.ofReal_pow (by positivity), one_div, inv_pow]
    _ = _ := by rw [h02]

end CapBounds

/-! ### Invariance under linear isometries -/

lemma sigmaN_image (T : Rn (m + 1) ≃ₗᵢ[ℝ] Rn (m + 1)) {A : Set (Rn (m + 1))}
    (hA : MeasurableSet A) : sigmaN m (T '' A) = sigmaN m A := by
  have hTA : MeasurableSet (T '' A) := by
    rw [T.image_eq_preimage_symm]; exact T.symm.continuous.measurable hA
  rw [sigmaN_apply hTA, sigmaN_apply hA]
  congr 1
  have hS : sphere (0 : Rn (m + 1)) 1 ∩ T '' A = T '' (sphere 0 1 ∩ A) := by
    rw [image_inter T.injective, T.image_sphere, map_zero]
  have hsmul : ∀ X : Set (Rn (m + 1)), Ioo (0 : ℝ) 1 • T '' X = T '' (Ioo (0 : ℝ) 1 • X) := by
    intro X
    ext z
    simp only [Set.mem_smul, mem_image]
    constructor
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a • x, ⟨a, ha, x, hx, rfl⟩, map_smul T a x⟩
    · rintro ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, T x, ⟨x, hx, rfl⟩, (map_smul T a x).symm⟩
  rw [hS, hsmul, T.image_eq_preimage_symm,
    T.symm.measurePreserving.measure_preimage_emb T.symm.toHomeomorph.measurableEmbedding]

lemma tauN_image (T : Rn (m + 1) ≃ₗᵢ[ℝ] Rn (m + 1)) (A : Set (Rn (m + 1))) :
    tauN m (T '' A) = tauN m A := by
  rw [tauN_apply, tauN_apply, show sphere (0 : Rn (m + 1)) 1 ∩ T '' A = T '' (sphere 0 1 ∩ A) by
      rw [image_inter T.injective, T.image_sphere, map_zero],
    hausdorffN_apply, hausdorffN_apply,
    T.isometry.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _))]

/-- Every point of the sphere is mapped to the north pole by some linear isometry. -/
lemma exists_linearIsometryEquiv_north {x : Rn (m + 1)} (hx : ‖x‖ = 1) :
    ∃ T : Rn (m + 1) ≃ₗᵢ[ℝ] Rn (m + 1), T x = north := by
  refine ⟨Submodule.reflection (ℝ ∙ (x - north))ᗮ, Submodule.reflection_sub ?_⟩
  have := norm_sq_snocCoords (0 : Rn m) 1
  rw [hx]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, one_pow,
    zero_add] at this
  rw [north]
  exact ((pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [this]; ring)).symm

/-! ### Cap bounds at every point of the sphere -/

lemma cap_param {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 0 < 1 - r ^ 2 / 2 ∧ 1 - r ^ 2 / 2 < 1 := by
  exact ⟨by linarith [pow_lt_one₀ hr0.le hr1 two_ne_zero], by linarith [pow_pos hr0 2]⟩

lemma tauN_closedBall_bounds (h02 : hausdorffN m m = (volume : Measure (Rn m)))
    {x : Rn (m + 1)} (hx : ‖x‖ = 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    volume (closedBall (0 : Rn m) √(1 - (1 - r ^ 2 / 2) ^ 2)) ≤ tauN m (closedBall x r) ∧
      tauN m (closedBall x r) ≤ ENNReal.ofReal ((1 - r ^ 2 / 2) ^ m)⁻¹ *
        volume (closedBall (0 : Rn m) √(1 - (1 - r ^ 2 / 2) ^ 2)) := by
  obtain ⟨T, hT⟩ := exists_linearIsometryEquiv_north hx
  obtain ⟨hh0, hh1⟩ := cap_param hr0 hr1
  have hB : closedBall north r = T '' closedBall x r := by rw [T.image_closedBall, hT]
  rw [← tauN_image T, ← hB, tauN_apply, sphere_inter_closedBall_north hr0.le]
  exact ⟨volume_closedBall_le_hausdorffN_cap hh0 hh1 h02, hausdorffN_cap_le hh0 hh1 h02⟩

lemma sigmaN_closedBall_bounds {x : Rn (m + 1)} (hx : ‖x‖ = 1) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) :
    ENNReal.ofReal (1 - r ^ 2 / 2) * volume (closedBall (0 : Rn m) √(1 - (1 - r ^ 2 / 2) ^ 2)) ≤
        sigmaN m (closedBall x r) ∧
      sigmaN m (closedBall x r) ≤ ENNReal.ofReal ((1 - r ^ 2 / 2) ^ m)⁻¹ *
        volume (closedBall (0 : Rn m) √(1 - (1 - r ^ 2 / 2) ^ 2)) := by
  obtain ⟨T, hT⟩ := exists_linearIsometryEquiv_north hx
  obtain ⟨hh0, hh1⟩ := cap_param hr0 hr1
  have hB : closedBall north r = T '' closedBall x r := by rw [T.image_closedBall, hT]
  rw [← sigmaN_image T isClosed_closedBall.measurableSet, ← hB,
    sigmaN_apply isClosed_closedBall.measurableSet, sphere_inter_closedBall_north hr0.le]
  exact ⟨ofReal_mul_le_volume_cone hh0 hh1, volume_cone_le hh0 hh1⟩

/-! ### Comparison of measures through the Besicovitch Vitali family -/

/-- If `a μ(B̄(x,r)) ≤ ν(B̄(x,r))` for arbitrarily small `r`, at every `x` and for every
`a < 1`, then `μ ≤ ν`. -/
theorem le_of_frequently_mul_closedBall_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ ν : Measure E}
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (h : ∀ a : ℝ≥0, a < 1 → ∀ x, ∃ᶠ r in 𝓝[>] 0,
      (a : ℝ≥0∞) * μ (closedBall x r) ≤ ν (closedBall x r)) :
    μ ≤ ν := by
  refine Measure.le_iff'.2 fun s => ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  lift a to ℝ≥0 using (ha.trans ENNReal.one_lt_top).ne
  have ha' : a < 1 := by exact_mod_cast ha
  let v := Besicovitch.vitaliFamily (μ + ν)
  have hac : a • μ ≪ μ + ν := (Measure.AbsolutelyContinuous.rfl.add_right ν).smul_left a
  have := v.measure_le_of_frequently_le ν hac s fun x _ =>
    (Besicovitch.tendsto_filterAt (μ + ν) x).frequently ((h a ha' x).mono fun r hr => by
      simpa [Measure.smul_apply] using hr)
  simpa [Measure.smul_apply] using this

/-! ### The main theorem -/

lemma tauN_compl_sphere : tauN m (sphere (0 : Rn (m + 1)) 1)ᶜ = 0 := by
  rw [tauN_apply, inter_compl_self, measure_empty]

lemma sigmaN_compl_sphere : sigmaN m (sphere (0 : Rn (m + 1)) 1)ᶜ = 0 := by
  rw [sigmaN, Measure.map_apply measurable_subtype_coe isClosed_sphere.measurableSet.compl]
  convert measure_empty (μ := sphereMeasure (m + 1))
  ext ω
  simp

lemma isLocallyFiniteMeasure_tauN (h02 : hausdorffN m m = (volume : Measure (Rn m))) :
    IsLocallyFiniteMeasure (tauN m) := by
  refine ⟨fun x => ?_⟩
  by_cases hx : ‖x‖ = 1
  · refine ⟨closedBall x (1 / 2), closedBall_mem_nhds x (by norm_num), ?_⟩
    refine ((tauN_closedBall_bounds h02 hx (by norm_num) (by norm_num)).2).trans_lt ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  · have hx' : x ∈ (sphere (0 : Rn (m + 1)) 1)ᶜ := by simpa using hx
    refine ⟨(sphere (0 : Rn (m + 1)) 1)ᶜ,
      (isClosed_sphere (x := (0 : Rn (m + 1))) (ε := 1)).isOpen_compl.mem_nhds hx', ?_⟩
    rw [tauN_compl_sphere]
    exact ENNReal.zero_lt_top

/-- Eventually as `r → 0+`, `r ∈ (0, 1)` and `a ≤ (1 - r²/2)^{m+1}`. -/
lemma eventually_cap_param {a : ℝ} (ha : a < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo 0 1 ∧ a ≤ (1 - r ^ 2 / 2) ^ (m + 1) := by
  have hc : Tendsto (fun r : ℝ => (1 - r ^ 2 / 2) ^ (m + 1)) (𝓝 0) (𝓝 1) := by
    simpa using ((by fun_prop : Continuous fun r : ℝ => (1 - r ^ 2 / 2) ^ (m + 1)).tendsto 0)
  exact Filter.Eventually.and (Ioo_mem_nhdsGT zero_lt_one)
    (nhdsWithin_le_nhds ((hc.eventually (lt_mem_nhds ha)).mono fun _ h => h.le))

lemma ofReal_mul_inv_pow_le {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (hah : a ≤ h ^ (m + 1)) :
    ENNReal.ofReal a * ENNReal.ofReal (h ^ m)⁻¹ ≤ ENNReal.ofReal h := by
  rw [← ENNReal.ofReal_mul ha]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), ← pow_succ']
  exact hah

/-- For `a < 1`, eventually both `a σ(B̄(x,r)) ≤ τ(B̄(x,r))` and `a τ(B̄(x,r)) ≤ σ(B̄(x,r))`. -/
lemma eventually_mul_closedBall_le (h02 : hausdorffN m m = (volume : Measure (Rn m)))
    {a : ℝ≥0} (ha : a < 1) (x : Rn (m + 1)) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (a : ℝ≥0∞) * sigmaN m (closedBall x r) ≤ tauN m (closedBall x r) ∧
        (a : ℝ≥0∞) * tauN m (closedBall x r) ≤ sigmaN m (closedBall x r) := by
  by_cases hx : ‖x‖ = 1
  · filter_upwards [eventually_cap_param (m := m) (a := a) (by exact_mod_cast ha)] with r ⟨hr, hah⟩
    obtain ⟨hh0, -⟩ := cap_param hr.1 hr.2
    obtain ⟨hτ1, hτ2⟩ := tauN_closedBall_bounds h02 hx hr.1 hr.2
    obtain ⟨hσ1, hσ2⟩ := sigmaN_closedBall_bounds hx hr.1 hr.2
    have hk := ofReal_mul_inv_pow_le a.coe_nonneg hh0 hah
    rw [← ENNReal.ofReal_coe_nnreal]
    constructor
    · calc ENNReal.ofReal a * sigmaN m (closedBall x r)
          ≤ ENNReal.ofReal a * (ENNReal.ofReal ((1 - r ^ 2 / 2) ^ m)⁻¹ *
              volume (closedBall (0 : Rn m) √(1 - (1 - r ^ 2 / 2) ^ 2))) := by gcongr
        _ ≤ ENNReal.ofReal (1 - r ^ 2 / 2) *
              volume (closedBall (0 : Rn m) √(1 - (1 - r ^ 2 / 2) ^ 2)) := by
            rw [← mul_assoc]; gcongr
        _ ≤ 1 * volume (closedBall (0 : Rn m) √(1 - (1 - r ^ 2 / 2) ^ 2)) := by
            gcongr; exact ENNReal.ofReal_le_one.2 (by nlinarith)
        _ ≤ _ := by rw [one_mul]; exact hτ1
    · calc ENNReal.ofReal a * tauN m (closedBall x r)
          ≤ ENNReal.ofReal a * (ENNReal.ofReal ((1 - r ^ 2 / 2) ^ m)⁻¹ *
              volume (closedBall (0 : Rn m) √(1 - (1 - r ^ 2 / 2) ^ 2))) := by gcongr
        _ ≤ ENNReal.ofReal (1 - r ^ 2 / 2) *
              volume (closedBall (0 : Rn m) √(1 - (1 - r ^ 2 / 2) ^ 2)) := by
            rw [← mul_assoc]; gcongr
        _ ≤ _ := hσ1
  · have hx' : x ∈ (sphere (0 : Rn (m + 1)) 1)ᶜ := by simpa using hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
      (isClosed_sphere (x := (0 : Rn (m + 1))) (ε := 1)).isOpen_compl x hx'
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    have hsub : closedBall x r ⊆ (sphere (0 : Rn (m + 1)) 1)ᶜ :=
      (closedBall_subset_ball hr.2).trans hball
    have hτ : tauN m (closedBall x r) = 0 := measure_mono_null hsub tauN_compl_sphere
    have hσ : sigmaN m (closedBall x r) = 0 := measure_mono_null hsub sigmaN_compl_sphere
    simp [hτ, hσ]

/-- The sphere measure is `ℋ^m⌊S^m` in `ℝ^{m+1}`, given `ℋ^m = ℒ^m` on `ℝ^m`. -/
theorem sigmaN_eq_tauN (h02 : hausdorffN m m = (volume : Measure (Rn m))) :
    sigmaN m = tauN m := by
  have := isLocallyFiniteMeasure_tauN h02
  have : IsFiniteMeasure (sphereMeasure (m + 1)) := by unfold sphereMeasure; infer_instance
  refine le_antisymm (le_of_frequently_mul_closedBall_le fun a ha x => ?_)
    (le_of_frequently_mul_closedBall_le fun a ha x => ?_)
  · exact ((eventually_mul_closedBall_le h02 ha x).mono fun _ h => h.1).frequently
  · exact ((eventually_mul_closedBall_le h02 ha x).mono fun _ h => h.2).frequently

end SphereMeasure

open SphereMeasure in
/-- **Sphere measure.** The surface measure `sphereMeasure n = volume.toSphere` on `S^{n-1}`,
pushed forward to `ℝⁿ`, is the normalized Hausdorff measure `ℋ^{n-1}⌊S^{n-1}`. The hypothesis
`h02` is the normalization `ℋ^{n-1} = ℒ^{n-1}` on `ℝ^{n-1}` (`hausdorffN_self_eq_volume`). -/
theorem map_sphereMeasure_eq_hausdorffN_of {n : ℕ} [NeZero n]
    (h02 : hausdorffN (n - 1) (n - 1) = (volume : Measure (Rn (n - 1)))) :
    (sphereMeasure n).map (Subtype.val) =
      (hausdorffN n (n - 1)).restrict (sphere (0 : Rn n) 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  exact sigmaN_eq_tauN h02

/-- **Unconditional form** of `map_sphereMeasure_eq_hausdorffN_of`: the hypothesis is
`hausdorffN_self_eq_volume` (`GMT/HausdorffLebesgue.lean`). -/
theorem map_sphereMeasure_eq_hausdorffN {n : ℕ} [NeZero n] :
    (sphereMeasure n).map (Subtype.val) =
      (hausdorffN n (n - 1)).restrict (sphere (0 : Rn n) 1) :=
  map_sphereMeasure_eq_hausdorffN_of (hausdorffN_self_eq_volume (n - 1))

/-- The statement follows in one line from the normalization `ℋ^d = ℒ^d` in every dimension. -/
example {n : ℕ} [NeZero n] (h02 : ∀ d, hausdorffN d d = (volume : Measure (Rn d))) :
    (sphereMeasure n).map (Subtype.val) =
      (hausdorffN n (n - 1)).restrict (sphere (0 : Rn n) 1) :=
  map_sphereMeasure_eq_hausdorffN_of (h02 _)

end GMTFoundations.GMT
