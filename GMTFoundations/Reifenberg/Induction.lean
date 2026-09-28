/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.Estimates
public import GMTFoundations.Reifenberg.Engine
import Mathlib.Algebra.Order.Ring.Star

/-!
# Discrete Reifenberg: the surfaces `T_i`, Prop 4.3, (4.1) and (4.2)

The approximating surfaces of M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci.
Fenn. Math. 43 (2018); arXiv:1612.02461 ("Miś"), §4 ("Construction of the approximating surface",
Proposition 4.3, "Estimates on the approximating surfaces", "Comparison of μ and λ^k⌊T_i"), with
`q = 2` and `k = n − 1`. Miś only sketches parts of this; the proofs here are complete.

Everything here is stated for a general covering run `D : CoverData n` under `D.SurfHyp`, whose
only analytic input is the smallness of the tilts (`SurfHyp.small`). The discrete instance
(`Discrete.lean`) verifies it from the tilt lemma `planeDist_sq_le_of_mass` and the inductive
hypothesis; the rectifiable-Reifenberg argument (`LimitMap.lean`) from the given upper bound.

Differences from Miś §4:
* Miś's Proposition 4.3 (d) is missing a square root: the proof gives a chart norm of order
  `δ₁ = (C M^{-2} δ²)^{1/2}` (at `q = 2`), which is the form proved here.
* The squash lemma (Miś Lemma 3.5) needs the planes of all good centers within `10 r_{i+1}` of `y`
  to be close to the parent plane; Miś checks only `|y − y′| ≤ 5 r_{i+1}`. The tilt `δ₁` below is
  a maximum over the larger set.
* Miś asserts that `σ_{i+1} : T_i → T_{i+1}` is globally bi-Lipschitz (Proposition 4.3 (c))
  without proof. It is not needed here: (4.1) uses only subadditivity and the chart-wise
  bi-Lipschitz bounds, and (4.2) uses a single chart.
* Miś uses `|T₀| = ω_k`, but `T₀` is a whole hyperplane. The area bound (4.1) is localized to
  nested windows `W_i = B_{w_i}(p)` (`window`).
* The lower area bound behind (4.2) is `ℋ^k(T ∩ B/3) ≥ ω_k (r/15)^k`; Miś's
  `|T_i ∩ B/3| ≥ (1/10)(r/3)^k` is false for `k ≥ 9`, even for a flat plane.

## Definitions

* `par i y`: the parent `z ∈ Good_i` of a center `y` at scale `i + 1` (with
  `d(y, V(z, κ r_i)) < r_{i+1}/4`, `CoverData.exists_parent`).
* `tilt i y`: `δ₁(y) = max {planeDist c r_{i+1} (V_{i+1} c) (V_i (par y)) : c ∈ Good_{i+1},
  |c − y| < 10 r_{i+1}}` (proof of Miś Prop 4.3; the `10B` of Lemma 3.5).
* `d1 i y`: `δ₁` at scale `i` (`0` at the top scale, where `T_j` is a plane).
* `sigma i = reifenbergMap (ρ^i) (Good_i) (V_i)`, and the surfaces `surf j = V(p, κ r_j)`,
  `surf (i+1) = σ_{i+1}(surf i)` (Miś §4).
* `chartFn`, `delta0`: the old chart and `δ₀(y) = 6 C_sq δ₁(par y) / ρ` fed to the one-scale
  step `reifenbergStep` (no compounding: `δ₀` depends only on the parent's `δ₁`).

## Main statements

* `CoverData.chartInv` (**Prop 4.3 (d)**, square-root form): for every `i ≥ j` and
  `z ∈ Good_i`, `surf i ∩ B_{5r_i/2}(z)` is a graph over `V_i z` with norm `≤ 6 C_sq δ₁(z)`.
* `CoverData.stepHyp`: the hypotheses of `reifenbergStep` at every scale (Prop 4.3 (a)–(c)
  then follow from its outputs: `dist_sigma_le`, `sigma_bilip`).
* `CoverData.hausdorffN_surf_le` (**(4.1)**, localized to the windows `W_i`).
* `CoverData.le_hausdorffN_surf_leaf` (**(4.2)**: `ℋ^k(T_N ∩ B/2) ≥ c₀ r^k / 2` for a
  bad or final ball `B` of radius `r`; one chart suffices).
-/

@[expose] public noncomputable section

namespace GMTFoundations.DiscreteReifenberg

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

/-- The smallness threshold for the tilts: `η = ρ / (10⁴ n C_sq²)`. It implies every smallness
condition of the one-scale step `reifenbergStep`. -/
def smallConst (n : ℕ) (ρ : ℝ) : ℝ := ρ / (10 ^ 4 * n * C_sq n ^ 2)

section SmallConst

variable {ρ d d' : ℝ}

private lemma C_sq_ge (n : ℕ) : 81 ≤ C_sq n := by
  rw [C_sq_eq]
  have : (1 : ℝ) ≤ 9 ^ n := one_le_pow₀ (by norm_num)
  linarith

theorem smallConst_pos (hn : 1 ≤ n) (hρ : 0 < ρ) : 0 < smallConst n ρ := by
  unfold smallConst
  have := C_sq_pos n
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  positivity

theorem smallConst_mul (hn : 1 ≤ n) (ρ : ℝ) :
    smallConst n ρ * (10 ^ 4 * n * C_sq n ^ 2) = ρ := by
  unfold smallConst
  have := C_sq_pos n
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  field_simp

/-- `6 C_sq η ≤ ρ / 100` (graph height for (4.2)). -/
theorem six_C_sq_mul_le (hn : 1 ≤ n) (hρ : 0 < ρ) (hd : d ≤ smallConst n ρ) :
    6 * C_sq n * d ≤ ρ / 100 := by
  have hC := C_sq_ge n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := smallConst_mul hn ρ
  have hη := smallConst_pos hn hρ
  generalize smallConst n ρ = η at *
  have h1 : 0 ≤ η * C_sq n * (10 ^ 4 * n * C_sq n - 600) := by
    have : 0 ≤ 10 ^ 4 * (n : ℝ) * C_sq n - 600 := by
      linarith [mul_le_mul hn' hC (by norm_num) (by linarith)]
    have := C_sq_pos n
    positivity
  have h2 : 6 * C_sq n * d ≤ 6 * C_sq n * η :=
    mul_le_mul_of_nonneg_left hd (by linarith)
  linarith

/-- `δ₀ = 6 C_sq δ₁′ / ρ ≤ 1/1000`. -/
theorem delta0_le (hn : 1 ≤ n) (hρ : 0 < ρ) (hd' : d' ≤ smallConst n ρ) :
    6 * C_sq n * d' / ρ ≤ 1 / 1000 := by
  rw [div_le_iff₀ hρ]
  have hC := C_sq_ge n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := smallConst_mul hn ρ
  have hη := smallConst_pos hn hρ
  generalize smallConst n ρ = η at *
  have h1 : 0 ≤ η * C_sq n * (10 ^ 4 * n * C_sq n - 6000) := by
    have : 0 ≤ 10 ^ 4 * (n : ℝ) * C_sq n - 6000 := by
      linarith [mul_le_mul hn' hC (by norm_num) (by linarith)]
    have := C_sq_pos n
    positivity
  have h2 : 6 * C_sq n * d' ≤ 6 * C_sq n * η :=
    mul_le_mul_of_nonneg_left hd' (by linarith)
  linarith

theorem smallConst_le_delta_step (hn : 1 ≤ n) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    smallConst n ρ ≤ δ_step n := by
  have hC := C_sq_ge n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := smallConst_mul hn ρ
  have hη := smallConst_pos hn hρ
  rw [δ_step, le_div_iff₀ (by positivity)]
  generalize smallConst n ρ = η at *
  have h1 : 0 ≤ η * C_sq n * (10 ^ 4 * n * C_sq n - 10) := by
    have : 0 ≤ 10 ^ 4 * (n : ℝ) * C_sq n - 10 := by
      linarith [mul_le_mul hn' hC (by norm_num) (by linarith)]
    have := C_sq_pos n
    positivity
  linarith

/-- The bi-Lipschitz excess `ε = C_sq²(δ₀² + δ₁²)` is `≤ 1/(2n)`. -/
theorem eps_le (hn : 1 ≤ n) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hd0 : 0 ≤ d) (hd : d ≤ smallConst n ρ)
    (hd0' : 0 ≤ d') (hd' : d' ≤ smallConst n ρ) :
    C_sq n ^ 2 * ((6 * C_sq n * d' / ρ) ^ 2 + d ^ 2) ≤ 1 / (2 * n) := by
  have hC := C_sq_ge n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := smallConst_mul hn ρ
  have hη := smallConst_pos hn hρ
  set η := smallConst n ρ
  have hq0 : 0 ≤ 6 * C_sq n * d' / ρ := by positivity
  -- `C_sq · δ₀ ≤ 6/(10⁴ n)` and `C_sq · δ₁ ≤ 1/(10⁴ n)`
  have h1 : C_sq n * (6 * C_sq n * d' / ρ) ≤ 6 / (10 ^ 4 * n) := by
    rw [le_div_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hρ]
    have : C_sq n * (6 * C_sq n * d') * (10 ^ 4 * n) ≤
        C_sq n * (6 * C_sq n * η) * (10 ^ 4 * n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hd' (by linarith)) (by linarith)) (by positivity)
    have e : C_sq n * (6 * C_sq n * η) * (10 ^ 4 * n) = 6 * ρ := by rw [← h]; ring
    linarith
  have h2 : C_sq n * d ≤ 1 / (10 ^ 4 * n) := by
    rw [le_div_iff₀ (by positivity)]
    have : C_sq n * d * (10 ^ 4 * n) ≤ C_sq n * η * (10 ^ 4 * n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by linarith)) (by positivity)
    have e : C_sq n * η * (10 ^ 4 * n) * C_sq n = ρ := by rw [← h]; ring
    have : C_sq n * η * (10 ^ 4 * n) ≤ 1 := by
      have hX : 0 ≤ C_sq n * η * (10 ^ 4 * n) := by positivity
      linarith [mul_le_mul_of_nonneg_left hC hX]
    linarith
  have h1' : (C_sq n * (6 * C_sq n * d' / ρ)) ^ 2 ≤ (6 / (10 ^ 4 * n)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h2' : (C_sq n * d) ^ 2 ≤ (1 / (10 ^ 4 * n)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have e : C_sq n ^ 2 * ((6 * C_sq n * d' / ρ) ^ 2 + d ^ 2) =
      (C_sq n * (6 * C_sq n * d' / ρ)) ^ 2 + (C_sq n * d) ^ 2 := by ring
  rw [e]
  have h3 : (6 / (10 ^ 4 * (n : ℝ))) ^ 2 + (1 / (10 ^ 4 * n)) ^ 2 ≤ 1 / (2 * n) := by
    rw [div_pow, div_pow, ← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hn' (by linarith : (0 : ℝ) ≤ n)]
  linarith

end SmallConst

namespace CoverData

variable (D : CoverData n)

/-! ### Definitions -/

open scoped Classical in
/-- The parent at scale `i` of a center `y` at scale `i + 1` (`exists_parent`); `p` if none. -/
def par (i : ℕ) (y : Rn n) : Rn n :=
  if h : ∃ z ∈ D.good i, y ∈ ball z (D.ρ ^ i) ∧
      |⟪y - (D.V i z).1, (D.V i z).2⟫| < D.ρ ^ (i + 1) / 4 then h.choose else D.p

open scoped Classical in
/-- The tilt `δ₁(y)` at scale `i + 1`: the largest `planeDist c r_{i+1} (V_{i+1} c) (V_i z)` over
the good centers `c` with `|c − y| < 10 r_{i+1}`, where `z = par i y` (Miś, proof of Prop 4.3). -/
def tilt (i : ℕ) (y : Rn n) : ℝ :=
  ((((D.good (i + 1)).filter fun c => dist c y < 10 * D.ρ ^ (i + 1)).sup fun c =>
    (planeDist c (D.ρ ^ (i + 1)) (D.V (i + 1) c) (D.V i (D.par i y))).toNNReal : ℝ≥0) : ℝ)

/-- `δ₁` at scale `i`: `tilt (i-1)` for `i > j`, and `0` at scales `≤ j`. -/
def d1 : ℕ → Rn n → ℝ
  | 0, _ => 0
  | i + 1, y => if D.j ≤ i then D.tilt i y else 0

/-- The Reifenberg map of scale `i` (`reifenbergMap` on `Good_i` with planes `V_i`). -/
def sigma (i : ℕ) : Rn n → Rn n := reifenbergMap (D.ρ ^ i) (D.good i) (D.V i)

/-- The surfaces: `surf i = V(p, κ r_j)` for `i ≤ j`, `surf (i+1) = σ_{i+1}(surf i)` (Miś §4). -/
def surf : ℕ → Set (Rn n)
  | 0 => affPlane (D.V D.j D.p)
  | i + 1 => if i + 1 ≤ D.j then affPlane (D.V D.j D.p) else D.sigma (i + 1) '' surf i

/-- **Prop 4.3 (d)**, the chart invariant at scale `i` (the form of output (O4) of
`reifenbergStep`). -/
def ChartInv (i : ℕ) : Prop :=
  ∀ z ∈ D.good i, ∃ g : Rn n → ℝ,
    IsChart (D.surf i) (D.V i z) g z (5 / 2 * D.ρ ^ i) (D.ρ ^ i) (6 * C_sq n * D.d1 i z)

open scoped Classical in
/-- A chart function of `surf i` at `z` (chosen when `ChartInv` provides one). -/
def chartFn (i : ℕ) (z : Rn n) : Rn n → ℝ :=
  if h : ∃ g : Rn n → ℝ,
      IsChart (D.surf i) (D.V i z) g z (5 / 2 * D.ρ ^ i) (D.ρ ^ i) (6 * C_sq n * D.d1 i z) then
    h.choose else 0

/-- `δ₀(y) = 6 C_sq δ₁(par y) / ρ`: the old chart's norm at scale `r_{i+1}`. -/
def delta0 (i : ℕ) (y : Rn n) : ℝ := 6 * C_sq n * D.d1 i (D.par i y) / D.ρ

/-- The bi-Lipschitz excess of `σ_{i+1}` on the chart at `y ∈ Good_{i+1}` (output (O3) of
`reifenbergStep`). -/
def eps (i : ℕ) (y : Rn n) : ℝ := C_sq n ^ 2 * (D.delta0 i y ^ 2 + D.d1 (i + 1) y ^ 2)

/-- The hypotheses of the surface construction. -/
structure SurfHyp : Prop where
  hyp : D.Hyp
  two_le_n : 2 ≤ n
  ρ_le : D.ρ ≤ 1 / 100
  unit : ∀ i y, ‖(D.V i y).2‖ = 1
  small : ∀ i, D.j ≤ i → ∀ y ∈ D.good (i + 1), D.tilt i y ≤ smallConst n D.ρ

/-! ### Basic properties -/

variable {D}

theorem par_spec {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.avail i (D.state i)) :
    D.par i y ∈ D.good i ∧ y ∈ ball (D.par i y) (D.ρ ^ i) ∧
      |⟪y - (D.V i (D.par i y)).1, (D.V i (D.par i y)).2⟫| < D.ρ ^ (i + 1) / 4 := by
  classical
  have h := exists_parent hi hy
  rw [par, dif_pos h]
  exact h.choose_spec

theorem tilt_nonneg (i : ℕ) (y : Rn n) : 0 ≤ D.tilt i y := NNReal.coe_nonneg _

theorem le_tilt {i : ℕ} {y c : Rn n} (hc : c ∈ D.good (i + 1))
    (hcy : dist c y < 10 * D.ρ ^ (i + 1)) :
    planeDist c (D.ρ ^ (i + 1)) (D.V (i + 1) c) (D.V i (D.par i y)) ≤ D.tilt i y := by
  classical
  refine (Real.le_coe_toNNReal _).trans ?_
  unfold tilt
  exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun c =>
    (planeDist c (D.ρ ^ (i + 1)) (D.V (i + 1) c) (D.V i (D.par i y))).toNNReal)
    (Finset.mem_filter.2 ⟨hc, hcy⟩))

theorem tilt_le {i : ℕ} {y : Rn n} {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ c ∈ D.good (i + 1), dist c y < 10 * D.ρ ^ (i + 1) →
      planeDist c (D.ρ ^ (i + 1)) (D.V (i + 1) c) (D.V i (D.par i y)) ≤ η) :
    D.tilt i y ≤ η := by
  classical
  unfold tilt
  rw [← Real.coe_toNNReal η hη, NNReal.coe_le_coe]
  refine Finset.sup_le fun c hc => ?_
  obtain ⟨hc1, hc2⟩ := Finset.mem_filter.1 hc
  exact Real.toNNReal_le_toNNReal (h c hc1 hc2)

theorem d1_of_le {i : ℕ} (hi : i ≤ D.j) (y : Rn n) : D.d1 i y = 0 := by
  cases i with
  | zero => rfl
  | succ i => simp only [d1]; rw [if_neg (by omega)]

theorem d1_succ {i : ℕ} (hi : D.j ≤ i) (y : Rn n) : D.d1 (i + 1) y = D.tilt i y := by
  simp only [d1]; rw [if_pos hi]

theorem d1_nonneg (i : ℕ) (y : Rn n) : 0 ≤ D.d1 i y := by
  cases i with
  | zero => exact le_rfl
  | succ i =>
    simp only [d1]
    split_ifs
    · exact tilt_nonneg i y
    · exact le_rfl

theorem sigma_eq (i : ℕ) : D.sigma i = reifenbergMap (D.ρ ^ i) (D.good i) (D.V i) := rfl

theorem surf_of_le {i : ℕ} (hi : i ≤ D.j) : D.surf i = affPlane (D.V D.j D.p) := by
  cases i with
  | zero => rfl
  | succ i => simp only [surf]; rw [if_pos hi]

theorem surf_succ {i : ℕ} (hi : D.j ≤ i) : D.surf (i + 1) = D.sigma (i + 1) '' D.surf i := by
  simp only [surf]; rw [if_neg (by omega)]

theorem delta0_nonneg (i : ℕ) (y : Rn n) (hρ : 0 < D.ρ) : 0 ≤ D.delta0 i y := by
  unfold delta0
  have := d1_nonneg (D := D) i (D.par i y)
  have := C_sq_pos n
  positivity

theorem eps_nonneg (i : ℕ) (y : Rn n) : 0 ≤ D.eps i y := by
  unfold eps; positivity

/-- The top chart: a plane is the graph of `0` over itself. -/
theorem isChart_affPlane {P : Rn n × Rn n} (c : Rn n) (R r : ℝ) :
    IsChart (affPlane P) P 0 c R r 0 := by
  refine ⟨?_, fun x _ => by simp, ?_⟩
  · congr 1
    ext x
    simp [graphOn]
  · rw [Real.toNNReal_zero]
    exact (LipschitzWith.const (α := Rn n) (0 : ℝ)).lipschitzOnWith

section SurfHyp

variable (h : D.SurfHyp)
include h

theorem SurfHyp.ρ_pos : 0 < D.ρ := h.hyp.ρ_pos

theorem SurfHyp.pow_pos (i : ℕ) : 0 < D.ρ ^ i := _root_.pow_pos h.ρ_pos i

theorem SurfHyp.one_le_n : 1 ≤ n := le_trans (by norm_num) h.two_le_n

/-- `δ₁ ≤ η` at every good center of every scale `i ≥ j`. -/
theorem d1_le_small {i : ℕ} (hi : D.j ≤ i) {z : Rn n} (hz : z ∈ D.good i) :
    D.d1 i z ≤ smallConst n D.ρ := by
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [d1_of_le le_rfl]
    exact (smallConst_pos h.one_le_n h.ρ_pos).le
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [d1_succ (by omega)]
    exact h.small i' (by omega) z hz

theorem pairwise_good_succ {i : ℕ} (hi : D.j ≤ i) :
    ((D.good (i + 1) : Set (Rn n))).Pairwise fun a b => D.ρ ^ (i + 1) ≤ dist a b :=
  fun _ ha _ hb hne => pow_le_dist_of_mem_succ h.hyp hi
    (Finset.mem_union_left _ (Finset.mem_union_left _ ha))
    (Finset.mem_union_left _ (Finset.mem_union_left _ hb)) hne

theorem par_spec_good {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    D.par i y ∈ D.good i ∧ y ∈ ball (D.par i y) (D.ρ ^ i) ∧
      |⟪y - (D.V i (D.par i y)).1, (D.V i (D.par i y)).2⟫| < D.ρ ^ (i + 1) / 4 :=
  par_spec hi (mem_avail_of_mem_succ h.hyp hi
    (Finset.mem_union_left _ (Finset.mem_union_left _ hy)))

theorem delta0_le_small {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    D.delta0 i y ≤ 1 / 1000 :=
  delta0_le h.one_le_n h.ρ_pos (d1_le_small h hi (par_spec_good h hi hy).1)

omit h in
/-- The chart invariant at the top scale: `surf j` is the plane `V_j p`. -/
theorem chartInv_top : D.ChartInv D.j := by
  intro z hz
  rw [good_top, Finset.mem_singleton] at hz
  subst hz
  refine ⟨0, ?_⟩
  rw [surf_of_le le_rfl, d1_of_le le_rfl, mul_zero]
  exact isChart_affPlane _ _ _

/-- **The hypotheses of the one-scale step `reifenbergStep` at scale `i → i + 1`**, given the
chart invariant at scale `i` (Miś, proof of Prop 4.3). -/
theorem stepHyp {i : ℕ} (hi : D.j ≤ i) (hc : D.ChartInv i) :
    ReifenbergStepHyp (D.ρ ^ (i + 1)) (D.good (i + 1)) (D.V (i + 1)) (D.surf i)
      (fun y => D.V i (D.par i y)) (fun y => D.chartFn i (D.par i y)) (D.delta0 i)
      (D.d1 (i + 1)) where
  hr := h.pow_pos _
  sep := pairwise_good_succ h hi
  unitVp := fun c _ => h.unit _ _
  unitVpar := fun y _ => h.unit _ _
  near := fun y hy => by
    have := (par_spec_good h hi hy).2.2
    have := h.pow_pos (i + 1)
    linarith
  tilt := fun y _ c hc hcy => by
    rw [d1_succ hi]
    exact le_tilt hc hcy
  chart := fun y hy => by
    classical
    obtain ⟨hz, hyz, -⟩ := par_spec_good h hi hy
    set z := D.par i y
    have hex := hc z hz
    have hspec : IsChart (D.surf i) (D.V i z) (D.chartFn i z) z (5 / 2 * D.ρ ^ i) (D.ρ ^ i)
        (6 * C_sq n * D.d1 i z) := by
      rw [chartFn, dif_pos hex]
      exact hex.choose_spec
    have hρ := h.ρ_pos
    have hri := h.pow_pos i
    have hδ : 0 ≤ 6 * C_sq n * D.d1 i z := by
      have := d1_nonneg (D := D) i z; have := C_sq_pos n; positivity
    have hρρ := mul_le_mul_of_nonneg_left h.ρ_le hri.le
    have h1 := hspec.mono (c' := y) (R' := 5 * D.ρ ^ (i + 1)) (h.unit _ _) (by
      rw [pow_succ]
      have := mem_ball.1 hyz
      linarith)
    have h2 := h1.rescale hδ (h.pow_pos (i + 1)) (by
      rw [pow_succ]; linarith)
    have e : 6 * C_sq n * D.d1 i z * D.ρ ^ i / D.ρ ^ (i + 1) = D.delta0 i y := by
      change _ = 6 * C_sq n * D.d1 i z / D.ρ
      rw [pow_succ]
      field_simp
    rwa [e] at h2
  small0 := fun y hy => ⟨delta0_nonneg i y h.ρ_pos,
    (delta0_le_small h hi hy).trans (by norm_num)⟩
  small1 := fun y hy => ⟨d1_nonneg _ _, by
    rw [d1_succ hi]
    exact (h.small i hi y hy).trans (smallConst_le_delta_step h.one_le_n h.ρ_pos h.hyp.ρ_le_one)⟩

/-- **Prop 4.3 (d)** at every scale (induction on `i`; output (O4) of `reifenbergStep` is
δ₀-free, so the norms do not compound from scale to scale). -/
theorem chartInv {i : ℕ} (hi : D.j ≤ i) : D.ChartInv i := by
  induction i, hi using Nat.le_induction with
  | base => exact chartInv_top
  | succ i hi ih =>
    have hs := reifenbergStep (stepHyp h hi ih)
    intro y hy
    obtain ⟨g, hg⟩ := hs.2.2.2.2.1 y hy
    refine ⟨g, ?_⟩
    rw [surf_succ hi, sigma_eq]
    exact hg

end SurfHyp

/-! ### Consequences of the step at every scale (Prop 4.3 (a)–(c)) -/

section Consequences

variable (h : D.SurfHyp)
include h

theorem d1_succ_le_small {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    D.d1 (i + 1) y ≤ smallConst n D.ρ :=
  d1_le_small h (by omega) hy

/-- **Displacement** (Prop 4.3 (b)): `|σ_{i+1}(a) − a| ≤ r_{i+1}/10` on `T_i`. -/
theorem dist_sigma_le {i : ℕ} (hi : D.j ≤ i) {a : Rn n} (ha : a ∈ D.surf i) :
    dist (D.sigma (i + 1) a) a ≤ D.ρ ^ (i + 1) / 10 := by
  have hs := reifenbergStep (stepHyp h hi (chartInv h hi))
  have hr := h.pow_pos (i + 1)
  by_cases hex : ∃ y ∈ D.good (i + 1), dist a y < 4 * D.ρ ^ (i + 1)
  · obtain ⟨y, hy, hay⟩ := hex
    have h1 := hs.2.1 y hy a ⟨ha, mem_ball.2 hay⟩
    have h0 := delta0_le_small h hi hy
    have h2 := d1_succ_le_small h hi hy
    have h3 := smallConst_le_delta_step h.one_le_n h.ρ_pos h.hyp.ρ_le_one
    have h4 := δ_step_le n
    have h5 : D.delta0 i y + 5 * D.d1 (i + 1) y ≤ 1 / 10 := by linarith
    rw [sigma_eq]
    calc _ ≤ (D.delta0 i y + 5 * D.d1 (i + 1) y) * D.ρ ^ (i + 1) := h1
      _ ≤ 1 / 10 * D.ρ ^ (i + 1) := mul_le_mul_of_nonneg_right h5 hr.le
      _ = _ := by ring
  · have hex' : ∀ y ∈ D.good (i + 1), 4 * D.ρ ^ (i + 1) ≤ dist a y := fun y hy =>
      not_lt.1 fun hlt => hex ⟨y, hy, hlt⟩
    rw [sigma_eq, hs.1 a hex', dist_self]
    positivity

/-- The bi-Lipschitz excess is small: `ε ≤ 1/(2n)`. -/
theorem eps_le_small {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    D.eps i y ≤ 1 / (2 * n) :=
  eps_le h.one_le_n h.ρ_pos h.hyp.ρ_le_one (d1_nonneg _ _) (d1_succ_le_small h hi hy)
    (d1_nonneg _ _) (d1_le_small h hi (par_spec_good h hi hy).1)

/-- `(1 + ε)^k ≤ 1 + 2kε ≤ 2`. -/
theorem one_add_eps_pow_le {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    (1 + D.eps i y) ^ (n - 1) ≤ 1 + 2 * ((n - 1 : ℕ) : ℝ) * D.eps i y := by
  refine one_add_pow_le (eps_nonneg _ _) ?_
  have he := eps_le_small h hi hy
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.one_le_n
  have hk : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have h0 := eps_nonneg (D := D) i y
  calc 2 * ((n - 1 : ℕ) : ℝ) * D.eps i y ≤ 2 * n * (1 / (2 * n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) he h0 (by positivity)
    _ = 1 := by field_simp

theorem one_add_eps_pow_le_two {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    (1 + D.eps i y) ^ (n - 1) ≤ 2 := by
  have h1 := one_add_eps_pow_le h hi hy
  have he := eps_le_small h hi hy
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.one_le_n
  have hk : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
  have h0 := eps_nonneg (D := D) i y
  have : 2 * ((n - 1 : ℕ) : ℝ) * D.eps i y ≤ 1 := by
    calc 2 * ((n - 1 : ℕ) : ℝ) * D.eps i y ≤ 2 * n * (1 / (2 * n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) he h0 (by positivity)
      _ = 1 := by field_simp
  linarith

/-- **Chart bi-Lipschitz** (Prop 4.3 (c)): on `T_i ∩ B_{5r_{i+1}}(y)`, `y ∈ Good_{i+1}`,
`σ_{i+1}` is `(1 + ε)`-bi-Lipschitz. -/
theorem sigma_bilip {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) {a b : Rn n}
    (ha : a ∈ D.surf i ∩ ball y (5 * D.ρ ^ (i + 1)))
    (hb : b ∈ D.surf i ∩ ball y (5 * D.ρ ^ (i + 1))) :
    dist (D.sigma (i + 1) a) (D.sigma (i + 1) b) ≤ (1 + D.eps i y) * dist a b ∧
      dist a b ≤ (1 + D.eps i y) * dist (D.sigma (i + 1) a) (D.sigma (i + 1) b) :=
  (reifenbergStep (stepHyp h hi (chartInv h hi))).2.2.2.1 y hy a ha b hb

/-- The area of one chart: `ℋ^k(T_i ∩ B_{5r_{i+1}}(y)) ≤ ω_k (10 r_{i+1})^k`
(`hausdorffN_inter_ball_le_of_graph`; the chart has Lipschitz constant `δ₀ ≤ 1`). -/
theorem hausdorffN_surf_inter_ball_le {i : ℕ} (hi : D.j ≤ i) {y : Rn n}
    (hy : y ∈ D.good (i + 1)) :
    hausdorffN n (n - 1) (D.surf i ∩ ball y (5 * D.ρ ^ (i + 1))) ≤
      ENNReal.ofReal (unitBallVolume (n - 1) * (10 * D.ρ ^ (i + 1)) ^ (n - 1)) := by
  have hc := (stepHyp h hi (chartInv h hi)).chart y hy
  have hr := h.pow_pos (i + 1)
  have hb := hausdorffN_inter_ball_le_of_graph h.two_le_n (h.unit _ _) (by positivity) hc.1 hc.2.2
  refine hb.trans ?_
  have hδ0 := delta0_le_small h hi hy
  have hδ := delta0_nonneg i y h.ρ_pos
  have hsq : (NNReal.sqrt (1 + (D.delta0 i y).toNNReal ^ 2) : ℝ≥0∞) ≤ 2 := by
    have : NNReal.sqrt (1 + (D.delta0 i y).toNNReal ^ 2) ≤ 2 := by
      rw [NNReal.sqrt_le_iff_le_sq]
      have : (D.delta0 i y).toNNReal ≤ 1 := by
        rw [Real.toNNReal_le_one]; linarith
      have : (D.delta0 i y).toNNReal ^ 2 ≤ 1 := pow_le_one₀ (by positivity) this
      calc 1 + (D.delta0 i y).toNNReal ^ 2 ≤ 1 + 1 := add_le_add le_rfl this
        _ ≤ 2 ^ 2 := by norm_num
    exact_mod_cast this
  calc (NNReal.sqrt (1 + (D.delta0 i y).toNNReal ^ 2) : ℝ≥0∞) ^ (n - 1) *
        ENNReal.ofReal (unitBallVolume (n - 1) * (5 * D.ρ ^ (i + 1)) ^ (n - 1))
      ≤ 2 ^ (n - 1) * ENNReal.ofReal (unitBallVolume (n - 1) * (5 * D.ρ ^ (i + 1)) ^ (n - 1)) := by
        gcongr
    _ = _ := by
        rw [show (2 : ℝ≥0∞) ^ (n - 1) = ENNReal.ofReal (2 ^ (n - 1)) by
          rw [ENNReal.ofReal_pow zero_le_two]; simp, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [show (10 : ℝ) * D.ρ ^ (i + 1) = 2 * (5 * D.ρ ^ (i + 1)) by ring,
          mul_pow (2 : ℝ) (5 * D.ρ ^ (i + 1))]
        ring

end Consequences

/-! ### (4.1): the area of the surfaces in the windows -/

/-- The window radius `w_i = (1 + ρ/2) r_j + r_{i+1} / (10 (1 − ρ))`: `w_i = w_{i+1} +
r_{i+1}/10`, `w_i ≥ (1 + ρ/2) r_j`, and `w_j ≤ (1 + ρ) r_j`. -/
def window (D : CoverData n) (i : ℕ) : ℝ :=
  (1 + D.ρ / 2) * D.ρ ^ D.j + D.ρ ^ (i + 1) / (10 * (1 - D.ρ))

section Area

variable (h : D.SurfHyp)
include h

theorem window_succ (i : ℕ) : D.window i = D.window (i + 1) + D.ρ ^ (i + 1) / 10 := by
  have hρ1 : D.ρ < 1 := h.ρ_le.trans_lt (by norm_num)
  have : 1 - D.ρ ≠ 0 := by linarith
  unfold window
  rw [pow_succ D.ρ (i + 1)]
  field_simp
  ring

theorem le_window (i : ℕ) : (1 + D.ρ / 2) * D.ρ ^ D.j ≤ D.window i := by
  have hρ1 : D.ρ < 1 := h.ρ_le.trans_lt (by norm_num)
  have := h.pow_pos (i + 1)
  unfold window
  have : 0 < 1 - D.ρ := by linarith
  have : 0 ≤ D.ρ ^ (i + 1) / (10 * (1 - D.ρ)) := by positivity
  linarith

theorem window_top_le : D.window D.j ≤ (1 + D.ρ) * D.ρ ^ D.j := by
  have hρ := h.ρ_pos
  have hρ1 := h.ρ_le
  have hr := h.pow_pos D.j
  unfold window
  have h1 : D.ρ ^ (D.j + 1) / (10 * (1 - D.ρ)) ≤ D.ρ / 2 * D.ρ ^ D.j := by
    rw [div_le_iff₀ (by linarith), pow_succ]
    linarith [mul_pos hr hρ, mul_le_mul_of_nonneg_right hρ1 (mul_pos hr hρ).le]
  linarith

/-- One step of (4.1): `ℋ^k(T_{i+1} ∩ W_{i+1}) ≤ ℋ^k(T_i ∩ W_i) +
Σ_{y ∈ Good_{i+1}} 2kε(y) ω_k (10 r_{i+1})^k`. -/
theorem hausdorffN_surf_succ_le {i : ℕ} (hi : D.j ≤ i) :
    hausdorffN n (n - 1) (D.surf (i + 1) ∩ ball D.p (D.window (i + 1))) ≤
      hausdorffN n (n - 1) (D.surf i ∩ ball D.p (D.window i)) +
        ∑ y ∈ D.good (i + 1), ENNReal.ofReal (2 * ((n - 1 : ℕ) : ℝ) * D.eps i y) *
          ENNReal.ofReal (unitBallVolume (n - 1) * (10 * D.ρ ^ (i + 1)) ^ (n - 1)) := by
  have hs := reifenbergStep (stepHyp h hi (chartInv h hi))
  have hr := h.pow_pos (i + 1)
  set σ := D.sigma (i + 1)
  set B := D.surf i ∩ ball D.p (D.window i)
  have hsub : D.surf (i + 1) ∩ ball D.p (D.window (i + 1)) ⊆ σ '' B := by
    rintro b ⟨hb, hbp⟩
    rw [surf_succ hi] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    have h1 := dist_sigma_le h hi ha
    rw [mem_ball] at hbp ⊢
    rw [window_succ h i]
    calc dist a D.p ≤ dist a (σ a) + dist (σ a) D.p := dist_triangle _ _ _
      _ < D.ρ ^ (i + 1) / 10 + D.window (i + 1) := by
          rw [dist_comm]; exact add_lt_add_of_le_of_lt h1 hbp
      _ = _ := by ring
  set L : Rn n → ℝ≥0 := fun y => (1 + D.eps i y).toNNReal
  have htel := hausdorffN_image_le_add_sum (n - 1) (σ := σ) (R := 4 * D.ρ ^ (i + 1)) L
    (D.good (i + 1)) B (fun x hx hY => by
      change reifenbergMap (D.ρ ^ (i + 1)) (D.good (i + 1)) (D.V (i + 1)) x = x
      refine hs.1 x fun y hy => ?_
      have := hY y hy
      rw [mem_ball, not_lt] at this
      exact this)
    (fun y hy => by
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      have hsub5 : ∀ x ∈ B ∩ ball y (4 * D.ρ ^ (i + 1)),
          x ∈ D.surf i ∩ ball y (5 * D.ρ ^ (i + 1)) := fun x hx =>
        ⟨hx.1.1, ball_subset_ball (by linarith) hx.2⟩
      have := (sigma_bilip h hi hy (hsub5 a ha) (hsub5 b hb)).1
      simp only [L]
      rw [Real.coe_toNNReal _ (by linarith [eps_nonneg (D := D) i y])]
      exact this)
  refine (measure_mono hsub).trans (htel.trans (add_le_add le_rfl (Finset.sum_le_sum ?_)))
  intro y hy
  have he0 := eps_nonneg (D := D) i y
  gcongr
  · -- `(1 + ε)^k − 1 ≤ 2kε`
    change ENNReal.ofReal (1 + D.eps i y) ^ (n - 1) - 1 ≤ _
    rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ zero_le_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have := one_add_eps_pow_le h hi hy
    linarith
  · refine le_trans (measure_mono ?_) (hausdorffN_surf_inter_ball_le h hi hy)
    exact fun x hx => ⟨hx.1.1, ball_subset_ball (by linarith) hx.2⟩

/-- **(4.1)** (localized to the windows; Miś §4, estimate (4.1)): for every `N ≥ j`,
`ℋ^k(T_N ∩ W_N) ≤ ω_k ((1+ρ) r_j)^k +
  Σ_{j ≤ i < N} Σ_{y ∈ Good_{i+1}} 2kε(y) ω_k (10 r_{i+1})^k`. -/
theorem hausdorffN_surf_le {N : ℕ} (hN : D.j ≤ N) :
    hausdorffN n (n - 1) (D.surf N ∩ ball D.p (D.window N)) ≤
      ENNReal.ofReal (unitBallVolume (n - 1) * ((1 + D.ρ) * D.ρ ^ D.j) ^ (n - 1)) +
        ∑ i ∈ Finset.Ico D.j N, ∑ y ∈ D.good (i + 1),
          ENNReal.ofReal (2 * ((n - 1 : ℕ) : ℝ) * D.eps i y) *
            ENNReal.ofReal (unitBallVolume (n - 1) * (10 * D.ρ ^ (i + 1)) ^ (n - 1)) := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.Ico_self, Finset.sum_empty, add_zero, surf_of_le le_rfl]
    refine (hausdorffN_affPlane_inter_ball_le h.two_le_n (h.unit _ _) _
      (by linarith [le_window h D.j, h.pow_pos D.j, mul_pos h.ρ_pos (h.pow_pos D.j)])).trans ?_
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (unitBallVolume_pos _).le)
    refine pow_le_pow_left₀ ?_ (window_top_le h) _
    linarith [le_window h D.j, h.pow_pos D.j, mul_pos h.ρ_pos (h.pow_pos D.j)]
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN]
    refine (hausdorffN_surf_succ_le h hN).trans ?_
    rw [← add_assoc]
    exact add_le_add ih le_rfl

end Area

/-! ### (4.2): the surfaces have large area in the half-balls of the leaves -/

section Leaf

variable (h : D.SurfHyp)
include h

/-- Later maps fix the half-ball of a bad or final ball: the good centers of scales
`> l` avoid `B_{r_l}(y)`, so `σ_{s+1} = id` on `B_{r_l/2}(y)` for `s ≥ l`. -/
theorem surf_inter_halfBall_subset_succ {l s : ℕ} (hl : D.j < l) (hls : l ≤ s) {y : Rn n}
    (hy : y ∈ D.bad l ∪ D.fin l) :
    D.surf s ∩ ball y (D.ρ ^ l / 2) ⊆ D.surf (s + 1) ∩ ball y (D.ρ ^ l / 2) := by
  rintro a ⟨ha, hay⟩
  refine ⟨?_, hay⟩
  rw [surf_succ (by omega)]
  refine ⟨a, ha, ?_⟩
  rw [sigma_eq]
  refine reifenbergMap_eq_self (h.pow_pos _) fun c hc => ?_
  have hd := pow_le_dist_of_mem_bad_fin h.hyp hl (by omega : l < s + 1) hy
    (Finset.mem_union_left _ (Finset.mem_union_left _ hc))
  have h1 : D.ρ ^ (s + 1) ≤ D.ρ * D.ρ ^ l := by
    rw [← pow_succ']
    exact pow_le_pow_of_le_one h.ρ_pos.le h.hyp.ρ_le_one (by omega)
  have h2 := mem_ball.1 hay
  have h3 := dist_triangle y a c
  rw [dist_comm y a] at h3
  linarith [h.pow_pos l, mul_le_mul_of_nonneg_right h.ρ_le (h.pow_pos l).le]

theorem surf_inter_halfBall_subset {l s N : ℕ} (hl : D.j < l) (hls : l ≤ s) (hsN : s ≤ N)
    {y : Rn n} (hy : y ∈ D.bad l ∪ D.fin l) :
    D.surf s ∩ ball y (D.ρ ^ l / 2) ⊆ D.surf N ∩ ball y (D.ρ ^ l / 2) := by
  induction N, hsN using Nat.le_induction with
  | base => exact subset_rfl
  | succ N hsN ih =>
    exact ih.trans (surf_inter_halfBall_subset_succ h hl (hls.trans hsN) hy)

/-- **(4.2)** (Miś §4, "Comparison of μ and λ^k⌊T_i", with the corrected constant
`c₀ = ω_k 15^{−k}` in place of Miś's `(1/10) 3^{−k}`, which fails for `k ≥ 9`):
for a bad or final ball `B_{r_l}(y)`, `j < l ≤ N`,
`ω_k (r_l/15)^k ≤ 2 ℋ^k(T_N ∩ B_{r_l/2}(y))`. One chart suffices (no global injectivity). -/
theorem le_hausdorffN_surf_leaf {l N : ℕ} (hl : D.j < l) (hlN : l ≤ N) {y : Rn n}
    (hy : y ∈ D.bad l ∪ D.fin l) :
    ENNReal.ofReal (unitBallVolume (n - 1) * (D.ρ ^ l / 15) ^ (n - 1)) ≤
      2 * hausdorffN n (n - 1) (D.surf N ∩ ball y (D.ρ ^ l / 2)) := by
  obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
  have hi : D.j ≤ i := by omega
  have hav : y ∈ D.avail i (D.state i) := by
    refine mem_avail_of_mem_succ h.hyp hi ?_
    rcases Finset.mem_union.1 hy with hy | hy
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hy)
    · exact Finset.mem_union_right _ hy
  obtain ⟨hz, hyz, hnear⟩ := par_spec hi hav
  set z := D.par i y
  obtain ⟨g, hg⟩ := chartInv h hi z hz
  have hρ := h.ρ_pos
  have hρ1 := h.ρ_le
  have hri := h.pow_pos i
  have hr := h.pow_pos (i + 1)
  have hrr : D.ρ ^ (i + 1) = D.ρ * D.ρ ^ i := pow_succ' _ _
  set r := D.ρ ^ (i + 1) with hr_def
  have hV := h.unit i z
  -- the chart of `T_i` at the parent, restricted to `B_{r/3}(y)`
  have hρρ := mul_le_mul_of_nonneg_right hρ1 hri.le
  have hg3 := hg.mono (c' := y) (R' := r / 3) hV (by
    have := mem_ball.1 hyz
    linarith)
  have hsmall := six_C_sq_mul_le h.one_le_n hρ (d1_le_small h hi hz)
  have hlow : ENNReal.ofReal (unitBallVolume (n - 1) * (r / 15) ^ (n - 1)) ≤
      hausdorffN n (n - 1) (D.surf i ∩ ball y (r / 3)) := by
    refine le_hausdorffN_inter_ball_of_graph h.two_le_n hV hr hnear.le hg3.1 fun x hx => ?_
    have hx' : x ∈ disc (D.V i z) y (r / 3) :=
      disc_subset_disc hV (by rw [dist_self]; linarith only [hr]) hx
    refine (hg3.2.1 x hx').trans ?_
    rw [hrr]
    linarith [mul_le_mul_of_nonneg_right hsmall hri.le]
  -- `σ_{i+1}` loses at most a factor `2` on `A = T_i ∩ B_{r/3}(y)`
  set A := D.surf i ∩ ball y (r / 3)
  set σ := D.sigma (i + 1)
  have hA2 : hausdorffN n (n - 1) A ≤ 2 * hausdorffN n (n - 1) (σ '' A) := by
    by_cases hex : ∃ c ∈ D.good (i + 1), dist y c < 4 * r + r / 3
    · obtain ⟨c, hc, hyc⟩ := hex
      have hsub : ∀ x ∈ A, x ∈ D.surf i ∩ ball c (5 * r) := fun x hx => by
        refine ⟨hx.1, ?_⟩
        rw [mem_ball]
        calc dist x c ≤ dist x y + dist y c := dist_triangle _ _ _
          _ < r / 3 + (4 * r + r / 3) := add_lt_add (mem_ball.1 hx.2) hyc
          _ ≤ 5 * r := by linarith
      have he0 := eps_nonneg (D := D) i c
      have hL := hausdorffN_le_of_le_mul_dist (n - 1) (σ := σ) (A := A)
        (L := (1 + D.eps i c).toNNReal) fun a ha b hb => by
          rw [Real.coe_toNNReal _ (by linarith)]
          exact (sigma_bilip h hi hc (hsub a ha) (hsub b hb)).2
      refine hL.trans ?_
      gcongr
      change ENNReal.ofReal (1 + D.eps i c) ^ (n - 1) ≤ 2
      rw [← ENNReal.ofReal_pow (by linarith)]
      calc ENNReal.ofReal ((1 + D.eps i c) ^ (n - 1)) ≤ ENNReal.ofReal 2 :=
            ENNReal.ofReal_le_ofReal (one_add_eps_pow_le_two h hi hc)
        _ = 2 := by simp
    · have hfix : ∀ x ∈ A, σ x = x := fun x hx => by
        change reifenbergMap (D.ρ ^ (i + 1)) (D.good (i + 1)) (D.V (i + 1)) x = x
        refine reifenbergMap_eq_self hr fun c hc => ?_
        have h1 := not_lt.1 fun hlt => hex ⟨c, hc, hlt⟩
        have h2 := mem_ball.1 hx.2
        have h3 := dist_triangle y x c
        rw [dist_comm y x] at h3
        linarith
      have : σ '' A = A := by
        ext x
        constructor
        · rintro ⟨a, ha, rfl⟩
          rw [hfix a ha]
          exact ha
        · intro hx
          exact ⟨x, hx, hfix x hx⟩
      rw [this]
      exact le_mul_of_one_le_left bot_le (by norm_num)
  -- `σ_{i+1}(A) ⊆ T_{i+1} ∩ B_{r/2}(y)`
  have hsub2 : σ '' A ⊆ D.surf (i + 1) ∩ ball y (r / 2) := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨by rw [surf_succ hi]; exact ⟨a, ha.1, rfl⟩, ?_⟩
    have h1 := dist_sigma_le h hi ha.1
    have h2 := mem_ball.1 ha.2
    rw [mem_ball]
    calc dist (σ a) y ≤ dist (σ a) a + dist a y := dist_triangle _ _ _
      _ < r / 10 + r / 3 := add_lt_add_of_le_of_lt h1 h2
      _ ≤ r / 2 := by linarith
  calc ENNReal.ofReal (unitBallVolume (n - 1) * (r / 15) ^ (n - 1))
      ≤ hausdorffN n (n - 1) A := hlow
    _ ≤ 2 * hausdorffN n (n - 1) (σ '' A) := hA2
    _ ≤ 2 * hausdorffN n (n - 1) (D.surf N ∩ ball y (r / 2)) := by
        gcongr
        exact hsub2.trans (surf_inter_halfBall_subset h hl le_rfl hlN hy)

end Leaf

end CoverData

end GMTFoundations.DiscreteReifenberg
