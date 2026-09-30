/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Sobolev
public import GMTFoundations.Sobolev.Lattice
public import GMTFoundations.Sobolev.Cutoff
public import GMTFoundations.DeGiorgi.Iteration
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Caccioppoli inequalities and De Giorgi classes

* `caccioppoli_of_step`: hole filling. If `F ≥ 0` satisfies the one-step inequality
  `∫_{B_t} |∇F|² ≤ ∫_{B_t} |(1 - η)∇F - F∇η|² + E |{F > 0} ∩ B_t|` for all cutoffs `η`
  supported in `B_t`, then
  `∫_{B_ρ} |∇F|² ≤ C (R - ρ)⁻² ∫_{B_R} F² + 128 E |{F > 0} ∩ B_R|`
  (via the iteration lemma).
* `IsDeGiorgiAt`: the (boundary) De Giorgi class `DG⁺` of Giaquinta–Giusti on balls centred at
  a fixed point, for all levels above a threshold.
* `integrableOn_norm_sq_of_memH1Loc`, `integrableOn_sq_of_memH1Loc`: local square-integrability
  of an `H¹_loc` function and of its weak gradient on compact subsets.

## References

* M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic
  Systems*, Annals of Mathematics Studies 105, Princeton University Press, 1983.
* M. Giaquinta, E. Giusti, Quasi-minima, Ann. Inst. H. Poincaré Anal. Non Linéaire 1 (1984),
  79–107.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public noncomputable section

namespace GMTFoundations

variable {d : ℕ}

/-! ### Local integrability from `MemH1Loc` -/

theorem integrableOn_norm_sq_of_memH1Loc {U K : Set (E d)} {w : E d → ℝ} {G : E d → E d}
    (hw : MemH1Loc U w G) (hK : K ⊆ U) (hKc : IsCompact K) :
    IntegrableOn (fun x ↦ ‖G x‖ ^ 2) K :=
  (memLp_two_iff_integrable_sq_norm (hw.2 K hK hKc).2.aestronglyMeasurable).1 (hw.2 K hK hKc).2

theorem integrableOn_sq_of_memH1Loc {U K : Set (E d)} {w : E d → ℝ} {G : E d → E d}
    (hw : MemH1Loc U w G) (hK : K ⊆ U) (hKc : IsCompact K) :
    IntegrableOn (fun x ↦ w x ^ 2) K := by
  have := (memLp_two_iff_integrable_sq_norm (hw.2 K hK hKc).1.aestronglyMeasurable).1
    (hw.2 K hK hKc).1
  rw [IntegrableOn]
  simpa [Real.norm_eq_abs, sq_abs] using this

/-! ### The De Giorgi classes -/

/-- **De Giorgi class at a point** (Giaquinta–Giusti `DG⁺`, on balls centred at `z`): for every
level `k ≥ K` and `0 < ρ < R ≤ R₀`,
`∫_{B_ρ(z)} |∇(f - k)₊|² ≤ C₀ (R - ρ)⁻² ∫_{B_R(z)} (f - k)₊² + C₁ |{f > k} ∩ B_R(z)|`. -/
def IsDeGiorgiAt (f : E d → ℝ) (G : E d → E d) (z : E d) (R₀ K C₀ C₁ : ℝ) : Prop :=
  ∀ k, K ≤ k → ∀ ρ R, 0 < ρ → ρ < R → R ≤ R₀ →
    ∫ x in ball z ρ, ‖{y | k < f y}.indicator G x‖ ^ 2 ≤
      C₀ / (R - ρ) ^ 2 * (∫ x in ball z R, (max (f x - k) 0) ^ 2) +
        C₁ * (volume ({x | k < f x} ∩ ball z R)).toReal

/-! ### Hole filling -/

theorem norm_sub_sq_le_two (a b : E d) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_sub_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]

theorem volume_inter_ball_ne_top (S : Set (E d)) (z : E d) (r : ℝ) :
    volume (S ∩ ball z r) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right)

/-- **Caccioppoli inequality from the one-step inequality (hole filling).** If `F` satisfies
`∫_{B_t} |∇F|² ≤ ∫_{B_t} |(1 - η)∇F - F∇η|² + E |{F > 0} ∩ B_t|` for every smooth `0 ≤ η ≤ 1`
vanishing with its gradient off `B_t`, then for `0 < ρ < R ≤ R₀`
`∫_{B_ρ} |∇F|² ≤ 256 C² (R - ρ)⁻² ∫_{B_R} F² + 128 E |{F > 0} ∩ B_R|`,
`C = cutoffConst`. -/
theorem caccioppoli_of_step {F : E d → ℝ} {GF : E d → E d} {z : E d} {R₀ Er : ℝ} (hEr : 0 ≤ Er)
    (hGF : IntegrableOn (fun x ↦ ‖GF x‖ ^ 2) (ball z R₀))
    (hF : IntegrableOn (fun x ↦ F x ^ 2) (ball z R₀))
    (hstep : ∀ t, 0 < t → t ≤ R₀ → ∀ η : E d → ℝ, ContDiff ℝ ∞ η →
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) → (∀ x ∉ ball z t, η x = 0 ∧ ∇ η x = 0) →
      ∫ x in ball z t, ‖GF x‖ ^ 2 ≤ (∫ x in ball z t, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2) +
        Er * (volume ({x | 0 < F x} ∩ ball z t)).toReal)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ R₀) :
    ∫ x in ball z ρ, ‖GF x‖ ^ 2 ≤ 256 * cutoffConst ^ 2 / (R - ρ) ^ 2 *
      (∫ x in ball z R, F x ^ 2) + 128 * Er * (volume ({x | 0 < F x} ∩ ball z R)).toReal := by
  set Φ : ℝ → ℝ := fun σ ↦ ∫ x in ball z σ, ‖GF x‖ ^ 2 with hΦ
  set S := ∫ x in ball z R, F x ^ 2 with hS
  set V := (volume ({x | 0 < F x} ∩ ball z R)).toReal with hV
  set C := cutoffConst with hC
  have hC0 : 0 < C := cutoffConst_pos
  have hGFσ : ∀ σ ≤ R₀, IntegrableOn (fun x ↦ ‖GF x‖ ^ 2) (ball z σ) := fun σ hσ ↦
    hGF.mono_set (ball_subset_ball hσ)
  have hFσ : ∀ σ ≤ R₀, IntegrableOn (fun x ↦ F x ^ 2) (ball z σ) := fun σ hσ ↦
    hF.mono_set (ball_subset_ball hσ)
  have hΦmono : ∀ σ₁ σ₂, σ₁ ≤ σ₂ → σ₂ ≤ R₀ → Φ σ₁ ≤ Φ σ₂ := fun σ₁ σ₂ h h2 ↦
    setIntegral_mono_set (hGFσ σ₂ h2) (ae_of_all _ fun x ↦ sq_nonneg _)
      (ball_subset_ball h).eventuallyLE
  have hS0 : 0 ≤ S := setIntegral_nonneg measurableSet_ball fun x _ ↦ sq_nonneg _
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVt : ∀ t ≤ R, (volume ({x | 0 < F x} ∩ ball z t)).toReal ≤ V := fun t ht ↦
    ENNReal.toReal_mono (volume_inter_ball_ne_top _ z R)
      (measure_mono (inter_subset_inter_right _ (ball_subset_ball ht)))
  have key : ∀ s t, ρ ≤ s → s < t → t < R →
      Φ s ≤ 1 / 2 * Φ t + C ^ 2 * S / (t - s) ^ 2 + Er * V / 2 := by
    intro s t hs hst htR
    have ht0 : 0 < t := by linarith
    have htR₀ : t ≤ R₀ := by linarith
    have hts : 0 < t - s := by linarith
    obtain ⟨η, hη, hη01, hη1, hη0, -, -, hηg⟩ := exists_cutoff z (by linarith : 0 ≤ s) hst
    have h1 := hstep t ht0 htR₀ η hη hη01 hη0
    set g : E d → ℝ := fun x ↦ 2 * ((closedBall z s)ᶜ.indicator (fun x ↦ ‖GF x‖ ^ 2) x) +
      2 * (C / (t - s)) ^ 2 * F x ^ 2 with hg
    have hpt : ∀ x, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2 ≤ g x := by
      intro x
      refine (norm_sub_sq_le_two _ _).trans ?_
      have ha : ‖(1 - η x) • GF x‖ ^ 2 ≤ (closedBall z s)ᶜ.indicator (fun x ↦ ‖GF x‖ ^ 2) x := by
        by_cases hx : x ∈ closedBall z s
        · rw [hη1 x hx, sub_self, zero_smul, norm_zero,
            indicator_of_notMem (show x ∉ (closedBall z s)ᶜ from fun h ↦ h hx)]
          norm_num
        · rw [indicator_of_mem (show x ∈ (closedBall z s)ᶜ from hx), norm_smul, mul_pow]
          have h01 := hη01 x
          have : ‖1 - η x‖ ^ 2 ≤ 1 := by
            rw [Real.norm_eq_abs, sq_abs]
            exact pow_le_one₀ (sub_nonneg.2 h01.2) (by linarith [h01.1])
          exact mul_le_of_le_one_left (sq_nonneg _) this
      have hb : ‖F x • ∇ η x‖ ^ 2 ≤ (C / (t - s)) ^ 2 * F x ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hηg x) 2) (sq_nonneg _)
      simp only [hg]
      linarith
    have hint_ind : IntegrableOn (fun x ↦ (closedBall z s)ᶜ.indicator (fun x ↦ ‖GF x‖ ^ 2) x)
        (ball z t) :=
      (hGFσ t htR₀).indicator measurableSet_closedBall.compl
    have hint_rhs : IntegrableOn g (ball z t) :=
      (hint_ind.const_mul 2).add ((hFσ t htR₀).const_mul _)
    have h2 : ∫ x in ball z t, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2 ≤ ∫ x in ball z t, g x :=
      integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _) hint_rhs (ae_of_all _ hpt)
    have h3 : ∫ x in ball z t, g x = 2 * (∫ x in ball z t ∩ (closedBall z s)ᶜ, ‖GF x‖ ^ 2) +
        2 * (C / (t - s)) ^ 2 * ∫ x in ball z t, F x ^ 2 := by
      simp only [hg]
      rw [integral_add (hint_ind.const_mul 2) ((hFσ t htR₀).const_mul _), integral_const_mul,
        integral_const_mul, setIntegral_indicator measurableSet_closedBall.compl]
    have h4 : ∫ x in ball z t ∩ (closedBall z s)ᶜ, ‖GF x‖ ^ 2 ≤ Φ t - Φ s := by
      have e : ∫ x in ball z t \ ball z s, ‖GF x‖ ^ 2 = Φ t - Φ s :=
        setIntegral_sdiff measurableSet_ball (hGFσ t htR₀) (ball_subset_ball hst.le)
      rw [← e]
      refine setIntegral_mono_set ((hGFσ t htR₀).mono_set sdiff_subset)
        (ae_of_all _ fun _ ↦ sq_nonneg _) (Eventually.of_forall fun x hx ↦ ?_)
      exact ⟨hx.1, fun h ↦ hx.2 (ball_subset_closedBall h)⟩
    have h5 : ∫ x in ball z t, F x ^ 2 ≤ S :=
      setIntegral_mono_set (hFσ R hR) (ae_of_all _ fun _ ↦ sq_nonneg _)
        (ball_subset_ball htR.le).eventuallyLE
    have h6 := hVt t htR.le
    have hct : 0 ≤ (C / (t - s)) ^ 2 := sq_nonneg _
    have hmain : Φ t ≤ 2 * (Φ t - Φ s) + 2 * (C / (t - s)) ^ 2 * S + Er * V := by
      have hEV : Er * (volume ({x | 0 < F x} ∩ ball z t)).toReal ≤ Er * V :=
        mul_le_mul_of_nonneg_left h6 hEr
      have hCS : (C / (t - s)) ^ 2 * ∫ x in ball z t, F x ^ 2 ≤ (C / (t - s)) ^ 2 * S :=
        mul_le_mul_of_nonneg_left h5 hct
      calc Φ t ≤ (∫ x in ball z t, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2) +
            Er * (volume ({x | 0 < F x} ∩ ball z t)).toReal := h1
        _ ≤ (2 * (∫ x in ball z t ∩ (closedBall z s)ᶜ, ‖GF x‖ ^ 2) +
            2 * (C / (t - s)) ^ 2 * ∫ x in ball z t, F x ^ 2) + Er * V := by
            rw [← h3]; exact add_le_add h2 hEV
        _ ≤ 2 * (Φ t - Φ s) + 2 * (C / (t - s)) ^ 2 * S + Er * V := by linarith
    have e : (C / (t - s)) ^ 2 * S = C ^ 2 * S / (t - s) ^ 2 := by rw [div_pow]; ring
    linarith
  have hit := iteration_lemma (f := Φ) (M := Φ R) (A := C ^ 2 * S) (B := Er * V / 2) hρR
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (by positivity) (by positivity)
    (fun t _ htR ↦ hΦmono t R htR.le hR) key
  have e : (16 : ℝ) / (1 - 1 / 2) ^ 4 * (C ^ 2 * S / (R - ρ) ^ 2 + Er * V / 2) =
      256 * C ^ 2 / (R - ρ) ^ 2 * S + 128 * Er * V := by
    have hRρ : 0 < R - ρ := by linarith
    have : (R - ρ) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [e] at hit
  exact hit

end GMTFoundations
