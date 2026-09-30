/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.Covering
public import GMTFoundations.Reifenberg.GraphArea
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Discrete Reifenberg: general estimates

Estimates from §4 of M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn.
Math. 43 (2018); arXiv:1612.02461 (hereafter Miś), in the case `q = 2`, `k = n − 1`: the paragraphs
"Estimates on the approximating surfaces" and "Estimates on the excess set", leading to (4.1) and
(4.3). The equation numbers (1.3), (3.3), (4.1)–(4.3) are Miś's.

This file holds the estimates of the inductive step that do not involve the surfaces `T_i`:

* elementary tools: `one_add_pow_le` (`(1+x)^m ≤ 1 + 2mx` for `2mx ≤ 1`), the double-sum swap
  `sum_sum_filter_le`, the overlap bound for integrals `sum_setLIntegral_le`, and the area growth
  of a map that is the identity off finitely many balls, `hausdorffN_image_le_add_sum` (in the
  telescoping form used by (4.1));
* `jonesBetaSq_le_rough`: the rough bound `β²(x, t) ≲ J (4t)^k / μ(B_t(x))` from (1.3), (3.3) and
  the single-scale window `beta_le_integral_window`;
* `measure_excess_le`: Markov's inequality for Miś's excess sets;
* the Carleson-type packing `CoverData.sum_sum_beta_le` for the covering construction
  (`Σ_{i ≥ j} Σ_{y ∈ Good_i} r_i^k β²(y, s r_i) ≲ θ^{-1} J r_j^k`), and from it
  the excess bound (4.3), `CoverData.measure_excess_le`.
-/

@[expose] public noncomputable section

namespace GMTFoundations.DiscreteReifenberg

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

/-! ### Elementary tools -/

/-- `(1 + x)^m ≤ 1 + 2 m x` for `0 ≤ x` and `2 m x ≤ 1`. -/
theorem one_add_pow_le {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 2 * m * x ≤ 1) :
    (1 + x) ^ m ≤ 1 + 2 * m * x := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast at hm ⊢
    have hm' : 2 * (m : ℝ) * x ≤ 1 := by nlinarith
    have h1 := ih hm'
    have h2 : (1 + x) ^ m * (1 + x) ≤ (1 + 2 * m * x) * (1 + x) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    rw [pow_succ]
    nlinarith

/-- Swapping a double sum over a relation: if every `z` is related to at most `N` elements of
`Y`, then `Σ_{y ∈ Y} Σ_{z ∈ Z, R y z} f z ≤ N Σ_{z ∈ Z} f z`. -/
theorem sum_sum_filter_le {α β : Type*} (Y : Finset α) (Z : Finset β) (R : α → β → Prop)
    [∀ a b, Decidable (R a b)] (f : β → ℝ≥0∞) (N : ℕ)
    (hN : ∀ z ∈ Z, (Y.filter fun y => R y z).card ≤ N) :
    ∑ y ∈ Y, ∑ z ∈ Z with R y z, f z ≤ N * ∑ z ∈ Z, f z := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  gcongr
  exact_mod_cast hN z hz

/-- `Σ_{y ∈ Y} f (g y) ≤ N Σ_{z ∈ Z} f z` when `g y ∈ Z` is related to `y` and every `z` is related
to at most `N` elements of `Y`. -/
theorem sum_comp_le {α β : Type*} (Y : Finset α) (Z : Finset β) (R : α → β → Prop)
    [∀ a b, Decidable (R a b)] (f : β → ℝ≥0∞) (g : α → β) (hg : ∀ y ∈ Y, g y ∈ Z ∧ R y (g y))
    (N : ℕ) (hN : ∀ z ∈ Z, (Y.filter fun y => R y z).card ≤ N) :
    ∑ y ∈ Y, f (g y) ≤ N * ∑ z ∈ Z, f z := by
  refine le_trans (Finset.sum_le_sum fun y hy => ?_) (sum_sum_filter_le Y Z R f N hN)
  exact Finset.single_le_sum (f := f) (fun _ _ => bot_le)
    (Finset.mem_filter.2 ⟨(hg y hy).1, (hg y hy).2⟩)

/-- `Σ ∫⁻ ≤ ∫⁻ Σ` for finite sums (no measurability needed). -/
theorem sum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp_rw [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

open scoped Classical in
/-- **Bounded overlap for integrals.** If the balls `B_s(c_i)`, `i ∈ Y`, lie in the measurable set
`U` and every point lies in at most `N` of them, then `Σ_i ∫_{B_s(c_i)} f ≤ N ∫_U f`. -/
theorem sum_setLIntegral_le {ι : Type*} (μ : Measure (Rn n)) (Y : Finset ι) (c : ι → Rn n)
    (s : ℝ) {U : Set (Rn n)} (hUm : MeasurableSet U) (hU : ∀ i ∈ Y, ball (c i) s ⊆ U) (N : ℕ)
    (hN : ∀ w, (Y.filter fun i => w ∈ ball (c i) s).card ≤ N) (f : Rn n → ℝ≥0∞) :
    ∑ i ∈ Y, ∫⁻ w in ball (c i) s, f w ∂μ ≤ N * ∫⁻ w in U, f w ∂μ := by
  classical
  simp_rw [← lintegral_indicator measurableSet_ball]
  refine (sum_lintegral_le μ Y _).trans ?_
  rw [← lintegral_indicator hUm, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)]
  refine lintegral_mono fun w => ?_
  simp_rw [indicator_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  by_cases hw : w ∈ U
  · rw [ite_eq_left hw]
    gcongr
    exact_mod_cast hN w
  · have : (Y.filter fun i => w ∈ ball (c i) s) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun i hi hwi => hw (hU i hi hwi)
    rw [this]
    simp

/-! ### Area growth of a map that is the identity off finitely many balls -/

/-- **Telescoping area bound**. If `σ = id` on `B` off `⋃_{y ∈ Y} B_R(y)`
and `σ` is `L_y`-Lipschitz on `B ∩ B_R(y)`, then
`ℋ^k(σ(B)) ≤ ℋ^k(B) + Σ_y (L_y^k − 1) ℋ^k(B ∩ B_R(y))`. -/
theorem hausdorffN_image_le_add_sum (k : ℕ) {σ : Rn n → Rn n} {R : ℝ} (L : Rn n → ℝ≥0) :
    ∀ (Y : Finset (Rn n)) (B : Set (Rn n)),
      (∀ x ∈ B, (∀ y ∈ Y, x ∉ ball y R) → σ x = x) →
      (∀ y ∈ Y, LipschitzOnWith (L y) σ (B ∩ ball y R)) →
      hausdorffN n k (σ '' B) ≤ hausdorffN n k B +
        ∑ y ∈ Y, ((L y : ℝ≥0∞) ^ k - 1) * hausdorffN n k (B ∩ ball y R) := by
  classical
  intro Y
  induction Y using Finset.induction_on with
  | empty =>
    intro B hid _
    have : σ '' B = B := by
      ext x
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hid x hx (by simp)]
        exact hx
      · intro hx
        exact ⟨x, hx, hid x hx (by simp)⟩
    simp [this]
  | insert a Y ha ih =>
    intro B hid hL
    set B₁ := B ∩ ball a R
    set B₂ := B \ ball a R
    have h1 : hausdorffN n k (σ '' B₁) ≤ (L a : ℝ≥0∞) ^ k * hausdorffN n k B₁ :=
      hausdorffN_image_le_of_lipschitzOnWith (hL a (Finset.mem_insert_self _ _)) k
    have h2 := ih B₂ (fun x hx hY => hid x hx.1 fun y hy => by
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hx.2
        · exact hY y hy)
      (fun y hy => (hL y (Finset.mem_insert_of_mem hy)).mono
        (inter_subset_inter_left _ sdiff_subset))
    have hsplit : hausdorffN n k B₁ + hausdorffN n k B₂ = hausdorffN n k B :=
      measure_inter_add_sdiff B measurableSet_ball
    have himg : σ '' B ⊆ σ '' B₁ ∪ σ '' B₂ := by
      rw [← image_union, inter_union_sdiff]
    have hsum2 : ∑ y ∈ Y, ((L y : ℝ≥0∞) ^ k - 1) * hausdorffN n k (B₂ ∩ ball y R) ≤
        ∑ y ∈ Y, ((L y : ℝ≥0∞) ^ k - 1) * hausdorffN n k (B ∩ ball y R) :=
      Finset.sum_le_sum fun y _ => by
        gcongr
        exact sdiff_subset
    have hL1 : (L a : ℝ≥0∞) ^ k ≤ 1 + ((L a : ℝ≥0∞) ^ k - 1) := le_add_tsub
    rw [Finset.sum_insert ha]
    calc hausdorffN n k (σ '' B)
        ≤ hausdorffN n k (σ '' B₁) + hausdorffN n k (σ '' B₂) :=
          (measure_mono himg).trans (measure_union_le _ _)
      _ ≤ (1 + ((L a : ℝ≥0∞) ^ k - 1)) * hausdorffN n k B₁ + (hausdorffN n k B₂ +
            ∑ y ∈ Y, ((L y : ℝ≥0∞) ^ k - 1) * hausdorffN n k (B ∩ ball y R)) :=
          add_le_add (h1.trans (by gcongr)) (h2.trans (add_le_add le_rfl hsum2))
      _ = (hausdorffN n k B₁ + hausdorffN n k B₂) +
            (((L a : ℝ≥0∞) ^ k - 1) * hausdorffN n k B₁ +
              ∑ y ∈ Y, ((L y : ℝ≥0∞) ^ k - 1) * hausdorffN n k (B ∩ ball y R)) := by ring
      _ = _ := by rw [hsplit]

/-! ### Markov's inequality for the excess sets -/

/-- Markov: `μ(B_t(y) ∩ {a ≤ |f_P|}) ≤ a^{-2} ∫_{B_t(y)} f_P² dμ`. -/
theorem measure_ball_inter_le_lintegral {μ : Measure (Rn n)} (y : Rn n) (t : ℝ) {a : ℝ}
    (ha : 0 < a) (P : Rn n × Rn n) :
    μ (ball y t ∩ {x | a ≤ |⟪x - P.1, P.2⟫|}) ≤
      ENNReal.ofReal (1 / a ^ 2) * ∫⁻ x in ball y t, ENNReal.ofReal (⟪x - P.1, P.2⟫ ^ 2) ∂μ := by
  have hf : Measurable fun x : Rn n => ENNReal.ofReal (⟪x - P.1, P.2⟫ ^ 2) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    fun_prop
  have hM := mul_meas_ge_le_lintegral₀ (μ := μ.restrict (ball y t)) hf.aemeasurable
    (ENNReal.ofReal (a ^ 2))
  have hsub : ball y t ∩ {x | a ≤ |⟪x - P.1, P.2⟫|} ⊆
      {x | ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal (⟪x - P.1, P.2⟫ ^ 2)} ∩ ball y t := by
    rintro x ⟨hx, hxa⟩
    refine ⟨ENNReal.ofReal_le_ofReal ?_, hx⟩
    rw [← sq_abs (⟪x - P.1, P.2⟫)]
    exact pow_le_pow_left₀ ha.le hxa 2
  rw [Measure.restrict_apply' measurableSet_ball] at hM
  have ha2 : ENNReal.ofReal (1 / a ^ 2) * ENNReal.ofReal (a ^ 2) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ (by positivity),
      ENNReal.ofReal_one]
  calc μ (ball y t ∩ {x | a ≤ |⟪x - P.1, P.2⟫|})
      ≤ μ ({x | ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal (⟪x - P.1, P.2⟫ ^ 2)} ∩ ball y t) :=
        measure_mono hsub
    _ = ENNReal.ofReal (1 / a ^ 2) * (ENNReal.ofReal (a ^ 2) *
          μ ({x | ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal (⟪x - P.1, P.2⟫ ^ 2)} ∩ ball y t)) := by
        rw [← mul_assoc, ha2, one_mul]
    _ ≤ _ := by gcongr

/-! ### The rough bound for β -/

/-- The single-window constant `C_w = 2^{n+1} · 2^{n+1} / log 2` of the rough bound. -/
def roughConst (n : ℕ) : ℝ := 2 ^ (n + 1) * (2 ^ (n + 1) / Real.log 2)

theorem roughConst_pos (n : ℕ) : 0 < roughConst n := by
  unfold roughConst
  have := Real.log_pos one_lt_two
  positivity

/-- (1.3) localized to the ball `B_R(c)`: `∫_{B_s(y)} ∫_0^s β²_μ(z,t) dt/t dμ(z) ≤ J s^{n-1}` for
every ball `B_s(y) ⊆ B_R(c)`. The engine only uses this form (with `R = R₀ r_j`), so that the
rectifiable-Reifenberg argument can supply it on its own region. -/
def LocBetaHyp (μ : Measure (Rn n)) (J : ℝ) (c : Rn n) (R : ℝ) : Prop :=
  ∀ (y : Rn n) (s : ℝ), 0 < s → ball y s ⊆ ball c R →
    ∫⁻ z in ball y s, (∫⁻ t in Ioo 0 s, jonesBetaSq μ z t / ENNReal.ofReal t) ∂μ ≤
      ENNReal.ofReal (J * s ^ (n - 1))

theorem BetaHyp.locBetaHyp {μ : Measure (Rn n)} {J : ℝ} (h : BetaHyp μ J) {c : Rn n} {R : ℝ}
    (hc : ball c R ⊆ ball 0 2) : LocBetaHyp μ J c R :=
  fun y s hs hys => h y s hs (hys.trans hc)

/-- **Rough bound** ((3.3), the single-scale window `beta_le_integral_window`, and (1.3)). Let `μ`
satisfy (1.3) with constant `J` on `B_R(c)`, `B_{4t}(x) ⊆ B_R(c)`, and `μ(B_t(x)) ≥ m > 0`. Then
`β²(x, t) ≤ C_w J (4t)^k / m`. -/
theorem jonesBetaSq_le_rough (hn : 1 ≤ n) {μ : Measure (Rn n)} {J : ℝ} {c : Rn n} {R : ℝ}
    (hJ : LocBetaHyp μ J c R) {x : Rn n} {t m : ℝ} (ht : 0 < t)
    (h4t : ball x (4 * t) ⊆ ball c R) (hm : 0 < m) (hlow : ENNReal.ofReal m ≤ μ (ball x t)) :
    jonesBetaSq μ x t ≤ ENNReal.ofReal (roughConst n * J * (4 * t) ^ (n - 1) / m) := by
  set Cw : ℝ := 2 ^ (n + 1) / Real.log 2 with hCw
  have hCw0 : 0 ≤ Cw := div_nonneg (by positivity) (Real.log_nonneg one_le_two)
  have hB := hJ x (4 * t) (by positivity) h4t
  -- `μ(B_t(x)) β²(x,t) ≤ 2^{n+1} ∫_{B_t(x)} β²(w, 2t) dμ`
  have h1 := measure_mul_jonesBetaSq_le hn (μ := μ) (x := x) ht
  -- each `β²(w, 2t) ≤ C_w ∫_{(2t, 4t)} ≤ C_w J(w, 4t)`
  have h2 : ∀ w, jonesBetaSq μ w (2 * t) ≤ ENNReal.ofReal Cw *
      ∫⁻ s in Ioo 0 (4 * t), jonesBetaSq μ w s / ENNReal.ofReal s := by
    intro w
    refine (beta_le_integral_window hn μ w (by positivity : (0 : ℝ) < 2 * t)).trans ?_
    exact mul_le_mul_right (lintegral_mono_set (Ioo_subset_Ioo (by positivity) (by linarith))) _
  have h3 : ∫⁻ w in ball x t, jonesBetaSq μ w (2 * t) ∂μ ≤
      ENNReal.ofReal Cw * ENNReal.ofReal (J * (4 * t) ^ (n - 1)) := by
    calc ∫⁻ w in ball x t, jonesBetaSq μ w (2 * t) ∂μ
        ≤ ∫⁻ w in ball x t, ENNReal.ofReal Cw *
            (∫⁻ s in Ioo 0 (4 * t), jonesBetaSq μ w s / ENNReal.ofReal s) ∂μ :=
          lintegral_mono fun w => h2 w
      _ = ENNReal.ofReal Cw * ∫⁻ w in ball x t,
            (∫⁻ s in Ioo 0 (4 * t), jonesBetaSq μ w s / ENNReal.ofReal s) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Cw * ∫⁻ w in ball x (4 * t),
            (∫⁻ s in Ioo 0 (4 * t), jonesBetaSq μ w s / ENNReal.ofReal s) ∂μ := by
          exact mul_le_mul_right (lintegral_mono_set (ball_subset_ball (by linarith))) _
      _ ≤ _ := by gcongr
  have key : ENNReal.ofReal m * jonesBetaSq μ x t ≤
      ENNReal.ofReal (roughConst n * J * (4 * t) ^ (n - 1)) := by
    calc ENNReal.ofReal m * jonesBetaSq μ x t ≤ μ (ball x t) * jonesBetaSq μ x t := by gcongr
      _ ≤ 2 ^ (n + 1) * ∫⁻ w in ball x t, jonesBetaSq μ w (2 * t) ∂μ := h1
      _ ≤ 2 ^ (n + 1) * (ENNReal.ofReal Cw * ENNReal.ofReal (J * (4 * t) ^ (n - 1))) := by
          gcongr
      _ = ENNReal.ofReal (roughConst n * J * (4 * t) ^ (n - 1)) := by
          rcases le_or_gt 0 J with hJ0 | hJ0
          · rw [← ENNReal.ofReal_mul hCw0, show (2 : ℝ≥0∞) ^ (n + 1) =
              ENNReal.ofReal (2 ^ (n + 1)) by rw [ENNReal.ofReal_pow zero_le_two]; simp,
              ← ENNReal.ofReal_mul (by positivity), roughConst]
            congr 1
            ring
          · have h0 : J * (4 * t) ^ (n - 1) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hJ0.le (by positivity)
            have h0' : roughConst n * J * (4 * t) ^ (n - 1) ≤ 0 := by
              rw [mul_assoc]
              exact mul_nonpos_of_nonneg_of_nonpos (roughConst_pos n).le h0
            rw [ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_of_nonpos h0', mul_zero, mul_zero]
  have hm' : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.2 hm).ne'
  calc jonesBetaSq μ x t = ENNReal.ofReal (1 / m) * (ENNReal.ofReal m * jonesBetaSq μ x t) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hm.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (1 / m) * ENNReal.ofReal (roughConst n * J * (4 * t) ^ (n - 1)) := by
        gcongr
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

/-! ### The covering construction: goodness, separation, packing -/

namespace CoverData

/-- Hypotheses of the covering estimates, stated for a general covering so that both the discrete
and the rectifiable-Reifenberg argument can use them. The discrete instance (`Discrete.lean`) has
`κ = ledgerKappa n`, `D = CoverData.ofFamily …`, `μ = levMeasure ρ Z lev`. -/
structure EstHyp (D : CoverData n) (κ J : ℝ) : Prop where
  hyp : D.Hyp
  one_le_n : 1 ≤ n
  θ_pos : 0 < D.θ
  ρ_le : D.ρ ≤ 1 / 100
  fin : ∀ x r, D.μ (ball x r) ≠ ∞
  top : ENNReal.ofReal (D.θ * (D.ρ ^ D.j) ^ (n - 1)) ≤ D.μ (ball D.p (D.ρ ^ D.j))
  one_le_κ : 1 ≤ κ
  κ_le : κ ≤ 3 / 2
  V_eq : ∀ i y, D.V i y = bestPlane D.μ y (κ * D.ρ ^ i)
  /-- (1.3) on the hypothesis region `B_{R₀ r_j}(p)`, `R₀ = 16`. -/
  beta : LocBetaHyp D.μ J D.p (ledgerR0 * D.ρ ^ D.j)
  J_nonneg : 0 ≤ J

variable {D : CoverData n} {κ J : ℝ}

section EstHyp

variable (h : D.EstHyp κ J)
include h

theorem EstHyp.ρ_pos : 0 < D.ρ := h.hyp.ρ_pos

theorem EstHyp.ρ_le_one : D.ρ ≤ 1 := h.hyp.ρ_le_one

theorem EstHyp.pow_pos (i : ℕ) : 0 < D.ρ ^ i := _root_.pow_pos h.ρ_pos i

theorem EstHyp.pow_le_pow {i l : ℕ} (hil : i ≤ l) : D.ρ ^ l ≤ D.ρ ^ i :=
  pow_le_pow_of_le_one h.ρ_pos.le h.ρ_le_one hil

/-- Good balls at every scale `i ≥ j` have mass `≥ θ ρ^{ik}`. -/
theorem le_measure_of_mem_good {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good i) :
    ENNReal.ofReal (D.θ * (D.ρ ^ i) ^ (n - 1)) ≤ D.μ (ball y (D.ρ ^ i)) := by
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [good_top, Finset.mem_singleton] at hy
    subst hy
    exact h.top
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact le_measure_of_mem_good_succ (by omega) hy

/-- Good centers lie in the top ball. -/
theorem mem_ball_of_mem_good {i : ℕ} (hi : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good i) :
    y ∈ ball D.p (D.ρ ^ D.j) := by
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [good_top, Finset.mem_singleton] at hy
    subst hy
    exact mem_ball_self (h.pow_pos _)
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact h.hyp.P_subset (mem_P_of_mem_succ h.hyp (by omega)
      (Finset.mem_union_left _ (Finset.mem_union_left _ hy)))

/-- Good centers at one scale `i ≥ j` are `ρ^i`-separated. -/
theorem pow_le_dist_of_mem_good {i : ℕ} (hi : D.j ≤ i) {y y' : Rn n} (hy : y ∈ D.good i)
    (hy' : y' ∈ D.good i) (hne : y ≠ y') : D.ρ ^ i ≤ dist y y' := by
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [good_top, Finset.mem_singleton] at hy hy'
    exact absurd (hy.trans hy'.symm) hne
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact pow_le_dist_of_mem_succ h.hyp (by omega)
      (Finset.mem_union_left _ (Finset.mem_union_left _ hy))
      (Finset.mem_union_left _ (Finset.mem_union_left _ hy')) hne

theorem pairwise_good {i : ℕ} (hi : D.j ≤ i) :
    ((D.good i : Set (Rn n))).Pairwise fun a b => D.ρ ^ i ≤ dist a b :=
  fun _ ha _ hb hne => pow_le_dist_of_mem_good h hi ha hb hne

/-- Packing count: a subfamily of `Good_i` inside a closed ball `B̄_R(w)` has at most
`(2R/ρ^i + 1)ⁿ` elements. -/
theorem card_good_le {i : ℕ} (hi : D.j ≤ i) {F : Finset (Rn n)} (hF : F ⊆ D.good i) {w : Rn n}
    {R : ℝ} (hR : 0 ≤ R) (hFw : ↑F ⊆ closedBall w R) :
    (F.card : ℝ) ≤ (2 * R / D.ρ ^ i + 1) ^ n :=
  NaberValtorta.card_le_of_pairwise_le_dist (h.pow_pos i) hR hFw
    fun _ ha _ hb hne => pow_le_dist_of_mem_good h hi (hF ha) (hF hb) hne

open scoped Classical in
/-- The packing count with an integer bound: `#{y ∈ Good_i : w ∈ B_{s ρ^i}(y)} ≤ c` whenever
`(2s + 1)ⁿ ≤ c`. -/
theorem card_filter_good_le {i : ℕ} (hi : D.j ≤ i) (w : Rn n) {s : ℝ} (hs : 0 ≤ s) {c : ℕ}
    (hc : (2 * s + 1) ^ n ≤ c) :
    ((D.good i).filter fun y => w ∈ ball y (s * D.ρ ^ i)).card ≤ c := by
  have hcard := card_good_le h hi (Finset.filter_subset _ _) (w := w)
    (R := s * D.ρ ^ i) (by have := h.pow_pos i; positivity) (fun y hy => by
      rw [Finset.coe_filter] at hy
      rw [mem_closedBall, dist_comm]
      exact (mem_ball.1 hy.2).le)
  rw [mul_div_assoc, mul_div_assoc, div_self (h.pow_pos i).ne', mul_one] at hcard
  exact_mod_cast hcard.trans hc

end EstHyp

/-- The constant of the packing sum: `2^{n+1} 7ⁿ C_W 12^k`, with the window constant
`C_W = 2^{n+1}/log 2 + ρ^{−(n+1)}/log ρ⁻¹` of `tsum_beta_le_integral_two_mul`. -/
def packConst (n : ℕ) (ρ : ℝ) : ℝ :=
  2 ^ (n + 1) * 7 ^ n * (2 ^ (n + 1) / Real.log 2 + ρ⁻¹ ^ (n + 1) / Real.log ρ⁻¹) * 12 ^ (n - 1)

theorem packConst_nonneg {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) : 0 ≤ packConst n ρ := by
  unfold packConst
  have h1 := Real.log_nonneg one_le_two
  have h2 : 0 ≤ Real.log ρ⁻¹ := Real.log_nonneg (one_le_inv₀ hρ0 |>.2 hρ1)
  have : 0 ≤ 2 ^ (n + 1) / Real.log 2 + ρ⁻¹ ^ (n + 1) / Real.log ρ⁻¹ :=
    add_nonneg (div_nonneg (by positivity) h1) (div_nonneg (by positivity) h2)
  positivity

/-- **Carleson packing of the β-numbers** (Miś §4, the sums behind (4.1) and (4.3), with
Remark 3.1 in the factor-2 window form `tsum_beta_le_integral_two_mul`). For `1 ≤ s ≤ 3` and
every `N`:
`Σ_{j ≤ i ≤ N} Σ_{y ∈ Good_i} ρ^{ik} β²(y, s ρ^i) ≤ C_pack J ρ^{jk} / θ`. -/
theorem sum_sum_beta_le (h : D.EstHyp κ J) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (N : ℕ) :
    ∑ i ∈ Finset.Icc D.j N, ∑ y ∈ D.good i,
        ENNReal.ofReal ((D.ρ ^ i) ^ (n - 1)) * jonesBetaSq D.μ y (s * D.ρ ^ i) ≤
      ENNReal.ofReal (packConst n D.ρ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ) := by
  set ρ := D.ρ with hρdef
  set μ := D.μ with hμdef
  set θ := D.θ with hθdef
  set j := D.j with hjdef
  have hn := h.one_le_n
  have hρ0 : 0 < ρ := h.ρ_pos
  have hρ1 : ρ < 1 := h.ρ_le.trans_lt (by norm_num)
  have hθ : 0 < θ := h.θ_pos
  set U : Set (Rn n) := ball D.p (4 * ρ ^ j) with hU
  set f : ℕ → Rn n → ℝ≥0∞ := fun i w => jonesBetaSq μ w (2 * (s * ρ ^ i)) with hf
  set CW : ℝ := 2 ^ (n + 1) / Real.log 2 + ρ⁻¹ ^ (n + 1) / Real.log ρ⁻¹ with hCW
  have hCW0 : 0 ≤ CW := by
    have h1 := Real.log_nonneg one_le_two
    have h2 : 0 ≤ Real.log ρ⁻¹ := Real.log_nonneg (one_le_inv₀ hρ0 |>.2 hρ1.le)
    exact add_nonneg (div_nonneg (by positivity) h1) (div_nonneg (by positivity) h2)
  -- (a) one term, by goodness and (3.3)
  have ha : ∀ i ∈ Finset.Icc j N, ∀ y ∈ D.good i,
      ENNReal.ofReal ((ρ ^ i) ^ (n - 1)) * jonesBetaSq μ y (s * ρ ^ i) ≤
        ENNReal.ofReal (1 / θ) * (2 ^ (n + 1) * ∫⁻ w in ball y (s * ρ ^ i), f i w ∂μ) := by
    intro i hi y hy
    have hi' := (Finset.mem_Icc.1 hi).1
    have hr := h.pow_pos i
    have hlow := le_measure_of_mem_good h hi' hy
    have hmono : μ (ball y (ρ ^ i)) ≤ μ (ball y (s * ρ ^ i)) :=
      measure_mono (ball_subset_ball (by nlinarith))
    have h33 := measure_mul_jonesBetaSq_le hn (μ := μ) (x := y) (by positivity : 0 < s * ρ ^ i)
    calc ENNReal.ofReal ((ρ ^ i) ^ (n - 1)) * jonesBetaSq μ y (s * ρ ^ i)
        = ENNReal.ofReal (1 / θ) * (ENNReal.ofReal (θ * (ρ ^ i) ^ (n - 1)) *
            jonesBetaSq μ y (s * ρ ^ i)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp
      _ ≤ ENNReal.ofReal (1 / θ) * (μ (ball y (s * ρ ^ i)) * jonesBetaSq μ y (s * ρ ^ i)) := by
          gcongr
          exact hlow.trans hmono
      _ ≤ _ := by gcongr
  -- (b) bounded overlap at one scale
  have hb : ∀ i ∈ Finset.Icc j N,
      ∑ y ∈ D.good i, ∫⁻ w in ball y (s * ρ ^ i), f i w ∂μ ≤
        ((7 ^ n : ℕ) : ℝ≥0∞) * ∫⁻ w in U, f i w ∂μ := by
    intro i hi
    have hi' := (Finset.mem_Icc.1 hi).1
    refine sum_setLIntegral_le μ (D.good i) id (s * ρ ^ i) measurableSet_ball ?_ (7 ^ n) ?_ _
    · intro y hy
      refine ball_subset_ball' ?_
      have h1 := mem_ball.1 (mem_ball_of_mem_good h hi' hy)
      have h2 : ρ ^ i ≤ ρ ^ j := h.pow_le_pow hi'
      have h3 : s * ρ ^ i ≤ 3 * ρ ^ j := by nlinarith [h.pow_pos i]
      simp only [id]
      linarith
    · intro w
      refine card_filter_good_le h hi' w (by linarith) ?_
      push_cast
      exact pow_le_pow_left₀ (by linarith) (by linarith) n
  -- (c) the scales, by the factor-2 window
  have hc : ∀ w, ∑ i ∈ Finset.Icc j N, f i w ≤ ENNReal.ofReal CW *
      ∫⁻ t in Ioo 0 (2 * (2 * (s * ρ ^ j))), jonesBetaSq μ w t / ENNReal.ofReal t := by
    intro w
    have hre : ∑ i ∈ Finset.Icc j N, f i w =
        ∑ α ∈ Finset.range (N + 1 - j), jonesBetaSq μ w (2 * (s * ρ ^ j) * ρ ^ α) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr rfl fun α _ => ?_
      simp only [hf, pow_add]
      congr 1
      ring
    rw [hre]
    exact (ENNReal.sum_le_tsum _).trans
      (tsum_beta_le_integral_two_mul hn μ w hρ0 hρ1 (by have := h.pow_pos j; positivity))
  -- (d) the hypothesis (1.3) on `B_{12 ρ^j}(p) ⊆ B_{R₀ ρ^j}(p)`
  have hd : ∫⁻ w in U, (∫⁻ t in Ioo 0 (2 * (2 * (s * ρ ^ j))),
      jonesBetaSq μ w t / ENNReal.ofReal t) ∂μ ≤ ENNReal.ofReal (J * (12 * ρ ^ j) ^ (n - 1)) := by
    have hr := h.pow_pos j
    have hsub : ball D.p (12 * ρ ^ j) ⊆ ball D.p (ledgerR0 * ρ ^ j) :=
      ball_subset_ball (by rw [ledgerR0]; linarith)
    refine le_trans ?_ (h.beta D.p (12 * ρ ^ j) (by positivity) hsub)
    calc ∫⁻ w in U, (∫⁻ t in Ioo 0 (2 * (2 * (s * ρ ^ j))),
          jonesBetaSq μ w t / ENNReal.ofReal t) ∂μ
        ≤ ∫⁻ w in U, (∫⁻ t in Ioo 0 (12 * ρ ^ j), jonesBetaSq μ w t / ENNReal.ofReal t) ∂μ :=
          lintegral_mono fun w => lintegral_mono_set (Ioo_subset_Ioo le_rfl (by nlinarith))
      _ ≤ _ := lintegral_mono_set (ball_subset_ball (by linarith))
  -- assembly
  have hsum_a : ∑ i ∈ Finset.Icc j N, ∑ y ∈ D.good i,
      ENNReal.ofReal ((ρ ^ i) ^ (n - 1)) * jonesBetaSq μ y (s * ρ ^ i) ≤
        ENNReal.ofReal (1 / θ) * (2 ^ (n + 1) * ∑ i ∈ Finset.Icc j N,
          ∑ y ∈ D.good i, ∫⁻ w in ball y (s * ρ ^ i), f i w ∂μ) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun y hy => ha i hi y hy
  have hsum_b : ∑ i ∈ Finset.Icc j N, ∑ y ∈ D.good i,
      ∫⁻ w in ball y (s * ρ ^ i), f i w ∂μ ≤
        ((7 ^ n : ℕ) : ℝ≥0∞) * ∫⁻ w in U, ∑ i ∈ Finset.Icc j N, f i w ∂μ := by
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    gcongr
    exact sum_lintegral_le _ _ _
  have hsum_c : ∫⁻ w in U, ∑ i ∈ Finset.Icc j N, f i w ∂μ ≤
      ENNReal.ofReal CW * ENNReal.ofReal (J * (12 * ρ ^ j) ^ (n - 1)) := by
    calc ∫⁻ w in U, ∑ i ∈ Finset.Icc j N, f i w ∂μ
        ≤ ∫⁻ w in U, ENNReal.ofReal CW * (∫⁻ t in Ioo 0 (2 * (2 * (s * ρ ^ j))),
            jonesBetaSq μ w t / ENNReal.ofReal t) ∂μ := lintegral_mono hc
      _ = ENNReal.ofReal CW * ∫⁻ w in U, (∫⁻ t in Ioo 0 (2 * (2 * (s * ρ ^ j))),
            jonesBetaSq μ w t / ENNReal.ofReal t) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  have hJ0 := h.J_nonneg
  have hr := h.pow_pos j
  calc _ ≤ ENNReal.ofReal (1 / θ) * (2 ^ (n + 1) * (((7 ^ n : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal CW * ENNReal.ofReal (J * (12 * ρ ^ j) ^ (n - 1))))) := by
        refine hsum_a.trans ?_
        gcongr
        exact hsum_b.trans (by gcongr)
    _ = _ := by
        rw [show (2 : ℝ≥0∞) ^ (n + 1) = ENNReal.ofReal (2 ^ (n + 1)) by
            rw [ENNReal.ofReal_pow zero_le_two]; simp,
          show ((7 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal (7 ^ n) by
            rw [ENNReal.ofReal_pow (by norm_num)]; simp,
          ← ENNReal.ofReal_mul hCW0, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [packConst, mul_pow, hCW]
        field_simp

/-- One excess set (Markov + `lintegral_bestPlane`):
`μ(E(y, r_l)) ≤ 16 κ^{n+1} ρ^{−2} r_l^k β²(y, κ r_l)`. -/
theorem measure_excess_le (h : D.EstHyp κ J) (l : ℕ) (y : Rn n) :
    D.μ (D.excess l y) ≤ ENNReal.ofReal (16 * κ ^ (n + 1) / D.ρ ^ 2) *
      (ENNReal.ofReal ((D.ρ ^ l) ^ (n - 1)) * jonesBetaSq D.μ y (κ * D.ρ ^ l)) := by
  have hn := h.one_le_n
  have hr := h.pow_pos l
  have hρ0 := h.ρ_pos
  have hκ : 0 < κ := zero_lt_one.trans_le h.one_le_κ
  have ha : 0 < D.ρ ^ (l + 1) / 4 := by have := h.pow_pos (l + 1); positivity
  have hM := measure_ball_inter_le_lintegral (μ := D.μ) y (D.ρ ^ l) ha (D.V l y)
  have hbp := lintegral_bestPlane hn (μ := D.μ) (x := y) (r := κ * D.ρ ^ l) (by positivity)
    (h.fin _ _)
  rw [← h.V_eq] at hbp
  refine (le_of_eq_of_le rfl hM).trans ?_
  calc ENNReal.ofReal (1 / (D.ρ ^ (l + 1) / 4) ^ 2) *
        ∫⁻ x in ball y (D.ρ ^ l), ENNReal.ofReal (⟪x - (D.V l y).1, (D.V l y).2⟫ ^ 2) ∂D.μ
      ≤ ENNReal.ofReal (1 / (D.ρ ^ (l + 1) / 4) ^ 2) *
        ∫⁻ x in ball y (κ * D.ρ ^ l), ENNReal.ofReal (⟪x - (D.V l y).1, (D.V l y).2⟫ ^ 2) ∂D.μ :=
        mul_le_mul_right (lintegral_mono_set (ball_subset_ball (by nlinarith [h.one_le_κ]))) _
    _ = _ := by
        rw [hbp, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ, mul_pow]
        field_simp
        ring

/-- The excess constant `C₃ = 16 κ^{n+1} ρ^{−2} C_pack` of (4.3). -/
def excessConst (n : ℕ) (ρ κ : ℝ) : ℝ := 16 * κ ^ (n + 1) / ρ ^ 2 * packConst n ρ

/-- **(4.3)** (Miś (4.3) at `q = 2`): the excess sets of the scales `j ≤ l ≤ N` carry
`μ`-mass at most `C₃ J ρ^{jk} / θ`. -/
theorem measure_biUnion_excess_le (h : D.EstHyp κ J) (N : ℕ) :
    D.μ (⋃ l ∈ Finset.Icc D.j N, D.excessUnion l (D.good l)) ≤
      ENNReal.ofReal (excessConst n D.ρ κ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ) := by
  have hρ0 := h.ρ_pos
  have hκ : 0 < κ := zero_lt_one.trans_le h.one_le_κ
  have hQ := sum_sum_beta_le h h.one_le_κ (h.κ_le.trans (by norm_num)) N
  calc D.μ (⋃ l ∈ Finset.Icc D.j N, D.excessUnion l (D.good l))
      ≤ ∑ l ∈ Finset.Icc D.j N, D.μ (D.excessUnion l (D.good l)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ l ∈ Finset.Icc D.j N, ∑ y ∈ D.good l, D.μ (D.excess l y) :=
        Finset.sum_le_sum fun l _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ l ∈ Finset.Icc D.j N, ∑ y ∈ D.good l, ENNReal.ofReal (16 * κ ^ (n + 1) / D.ρ ^ 2) *
          (ENNReal.ofReal ((D.ρ ^ l) ^ (n - 1)) * jonesBetaSq D.μ y (κ * D.ρ ^ l)) :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun y _ => measure_excess_le h l y
    _ = ENNReal.ofReal (16 * κ ^ (n + 1) / D.ρ ^ 2) * ∑ l ∈ Finset.Icc D.j N, ∑ y ∈ D.good l,
          ENNReal.ofReal ((D.ρ ^ l) ^ (n - 1)) * jonesBetaSq D.μ y (κ * D.ρ ^ l) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (16 * κ ^ (n + 1) / D.ρ ^ 2) *
          ENNReal.ofReal (packConst n D.ρ * J * (D.ρ ^ D.j) ^ (n - 1) / D.θ) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), excessConst]
        congr 1
        ring

end CoverData

end GMTFoundations.DiscreteReifenberg
