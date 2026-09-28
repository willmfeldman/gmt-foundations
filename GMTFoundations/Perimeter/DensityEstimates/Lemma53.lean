/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.ReducedBoundary
public import GMTFoundations.GMT.Basic
import GMTFoundations.Perimeter.Slicing
import GMTFoundations.Perimeter.Isoperimetric
import GMTFoundations.Perimeter.Poincare
import GMTFoundations.GMT.Polar
import GMTFoundations.BV.TotalVariation
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Density estimates at the reduced boundary (EG Lemma 5.3 (i)–(iv))

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (EG), §5.7.

* **Density estimates at `∂*E`** (EG Lemma 5.3 (i)–(iv)): for a
  Gauss–Green pair `(μ, ν)` of a measurable `E` in an open `Ω` and a reduced-boundary point `x`
  (hypotheses `x ∈ Ω`, `μ(B_r(x)) > 0`, `⨍_{B_r(x)} ν dμ → v`, `‖v‖ = 1`, as in EG Def 5.4), there
  is `r₀ > 0` such that for `0 < r < r₀`:
  (i) `A₁ rⁿ ≤ |E ∩ B_r(x)|` (`IsGaussGreenPair.exists_forall_volume_inter_ball_ge`),
  (ii) `A₁ rⁿ ≤ |B_r(x) ∖ E|` (`IsGaussGreenPair.exists_forall_volume_ball_diff_ge`),
  (iii) `A₃ r^{n-1} ≤ μ(B_r(x))` (`IsGaussGreenPair.exists_forall_measure_ball_ge`),
  (iv) `μ(B_r(x)) ≤ A₄ r^{n-1}` (`IsGaussGreenPair.exists_forall_measure_ball_le`);
  combined: `IsGaussGreenPair.exists_densityEstimates`; `…_of_mem_reducedBoundary` variants take
  `x ∈ reducedBoundary Ω E`. Constants `densityConstA₁`, `densityConstA₃`, `densityConstA₄`
  (depending only on `n`; `A₂ = A₁`). `n ≥ 2` for (i)–(iii) (isoperimetric inequality).

See `Perimeter/DensityEstimates/Covering.lean` for the covering comparisons between `μ`
and `ℋ^k`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ═══════════════════════════════════════════════════════════════════════════════════════════
### Density estimates at the reduced boundary (EG Lemma 5.3 (i)–(iv))

Fix a Gauss–Green pair `(μ, ν)` of a measurable `E` in the open set `Ω` and a point `x ∈ Ω` with
`μ(B_r(x)) > 0` for all `r > 0` at which the normal averages `⨍_{B_r(x)} ν dμ` converge to a unit
vector `v` (i.e. `x ∈ ∂*E`, `IsGaussGreenPair.mem_reducedBoundary_iff`). Write
`g(r) = |E ∩ B_r(x)|` and `F(r) = F_{χ_E}(r) = sphereIntegral (E.indicator 1) x r
= ℋ^{n-1}(E ∩ ∂B_r(x))` (`sphereIntegral_indicator_eq_hausdorffN`).

* (⋆⋆⋆) `IsGaussGreenPair.exists_ae_measure_ball_le_sphereIntegral`: `μ(B_r) ≤ 2 F(r)` for a.e.
  small `r` (Gauss–Green on `E ∩ B_r` for a field `≡ v` near `x`,
  `integral_divergence_inter_ball_ae`; its exceptional set depends on the single field `φ`,
  which is harmless here). EG's step 5 derives (iv) for *all* small `r` from (⋆⋆⋆), which holds
  only for a.e. small `r`; the missing step is supplied in (iv).
* (iv) `μ(B_r) ≤ A₄ r^{n-1}` with `A₄ = 2 n ω_n`: (⋆⋆⋆) and `F(r) ≤ |∂B_r| = n ω_n r^{n-1}`,
  extended from a.e. `r` to every `r` by monotonicity of `r ↦ μ(B_r)` and continuity of
  `r ↦ r^{n-1}`.
* (i) `|E ∩ B_r| ≥ A₁ rⁿ` with `A₁ = (n K_n)^{-n}`, `K_n = 3(C_iso + 1)`: (⋆⋆⋆), the slicing
  inequality `TV(E ∩ B_r) ≤ μ(B_r) + F(r)` (`IsGaussGreenPair.totalVariationOn_inter_ball_le_ae`,
  whose exceptional set is independent of the test field, unlike EG's step 1) and the
  isoperimetric inequality give
  `g^{(n-1)/n} ≤ K_n F = K_n g'` a.e.; the ODE step `pow_le_of_rpow_le_mul_integral` integrates
  it (via `g(b) - g(a) = ∫_a^b F` and a right-slope comparison argument, no absolute continuity
  API needed).
* (ii) `|B_r ∖ E| ≥ A₁ rⁿ`: (i) for the complementary pair `(μ, -ν)` of `Eᶜ` (EG step 3).
* (iii) `μ(B_r) ≥ A₃ r^{n-1}` with `A₃ = A₁ / 2^{n+1}`: (i), (ii) and the `L¹` relative
  isoperimetric inequality `min(|E ∩ B_r|, |B_r ∖ E|) ≤ 2^{n+1} r μ(B_r)` (EG uses the
  `(n-1)/n` form, EG Thm 5.11 (ii); the `L¹` form changes only the constant).

EG states the estimates as `liminf`/`limsup` bounds; we give the equivalent explicit form "for
`0 < r < r₀(x)`", which is how EG's proof produces them. Lemma 5.3 (v) is not formalized (the
blow-up argument uses local bounds from (iv) instead).
═══════════════════════════════════════════════════════════════════════════════════════════ -/

section DensityEstimatesAtBoundary

/-! #### Constants -/

/-- `K_n = 3 (C_iso + 1)`, the constant in `|E ∩ B_r|^{(n-1)/n} ≤ K_n ℋ^{n-1}(E ∩ ∂B_r)` (EG
Lemma 5.3, step 2, `C₁`), where `C_iso = isoperimetricConst n`. -/
noncomputable def densityConstK (n : ℕ) : ℝ := 3 * ((isoperimetricConst n : ℝ) + 1)

/-- `A₁ = A₂ = (n K_n)^{-n}`, the lower density constant of EG Lemma 5.3 (i), (ii). -/
noncomputable def densityConstA₁ (n : ℕ) : ℝ := ((n : ℝ) * densityConstK n)⁻¹ ^ n

/-- `A₃ = A₁ / 2^{n+1}`, the lower perimeter-density constant of EG Lemma 5.3 (iii). -/
noncomputable def densityConstA₃ (n : ℕ) : ℝ := densityConstA₁ n / 2 ^ (n + 1)

/-- `A₄ = 2 n ω_n = 2 |∂B_1|`, the upper perimeter-density constant of EG Lemma 5.3 (iv). -/
noncomputable def densityConstA₄ (n : ℕ) : ℝ := 2 * n * unitBallVolume n

theorem densityConstK_pos (n : ℕ) : 0 < densityConstK n := by
  unfold densityConstK
  have := (isoperimetricConst n).2
  positivity

theorem densityConstA₁_pos {n : ℕ} (hn : 1 ≤ n) : 0 < densityConstA₁ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := densityConstK_pos n
  unfold densityConstA₁
  positivity

theorem densityConstA₃_pos {n : ℕ} (hn : 1 ≤ n) : 0 < densityConstA₃ n := by
  have := densityConstA₁_pos hn
  unfold densityConstA₃
  positivity

theorem densityConstA₄_pos {n : ℕ} (hn : 1 ≤ n) : 0 < densityConstA₄ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := unitBallVolume_pos n
  unfold densityConstA₄
  positivity

/-! #### Real-variable lemmas -/

/-- A property holding for a.e. `s ∈ ℝ` holds somewhere in every nonempty open interval. -/
theorem exists_mem_Ioo_of_ae {p : ℝ → Prop} (hp : ∀ᵐ s, p s) {a b : ℝ} (hab : a < b) :
    ∃ s ∈ Ioo a b, p s := by
  by_contra hcon
  push Not at hcon
  have h0 : volume (Ioo a b) = 0 := measure_mono_null (fun s hs => hcon s hs) (ae_iff.1 hp)
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  linarith

/-- From a.e. `s` to every `r`: if `f` is monotone, `G` continuous and `f s ≤ G s` for a.e.
`s ∈ (0, r₀)`, then `f r ≤ G r` for every `r ∈ (0, r₀)`. -/
theorem le_ofReal_of_ae_le_of_monotone {f : ℝ → ℝ≥0∞} (hf : Monotone f) {G : ℝ → ℝ}
    (hG : Continuous G) {r₀ : ℝ} (h : ∀ᵐ s, 0 < s → s < r₀ → f s ≤ ENNReal.ofReal (G s))
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀) : f r ≤ ENNReal.ofReal (G r) := by
  refine le_of_forall_gt fun c hc => ?_
  have hcont : Tendsto (fun s => ENNReal.ofReal (G s)) (𝓝 r) (𝓝 (ENNReal.ofReal (G r))) :=
    (ENNReal.continuous_ofReal.comp hG).tendsto r
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds hc))
  obtain ⟨s, hs, hps⟩ := exists_mem_Ioo_of_ae h
    (show r < min (r + ε) r₀ from lt_min (by linarith) hrr₀)
  have hs1 := hs.2.trans_le (min_le_left _ _)
  have hs2 := hs.2.trans_le (min_le_right _ _)
  calc f r ≤ f s := hf hs.1.le
    _ ≤ ENNReal.ofReal (G s) := hps (hr.trans hs.1) hs2
    _ < c := hεs (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1])

/-- `bⁿ - aⁿ ≤ n b^{n-1} (b - a)` for `0 ≤ a ≤ b`. -/
theorem pow_sub_pow_le_mul {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) :
    b ^ n - a ^ n ≤ n * b ^ (n - 1) * (b - a) := by
  rw [← geom_sum₂_mul]
  refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 hab)
  calc ∑ i ∈ Finset.range n, b ^ i * a ^ (n - 1 - i)
      ≤ ∑ _i ∈ Finset.range n, b ^ (n - 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i + (n - 1 - i) = n - 1 := by
          have := Finset.mem_range.1 hi
          omega
        calc b ^ i * a ^ (n - 1 - i) ≤ b ^ i * b ^ (n - 1 - i) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _) (pow_nonneg (ha.trans hab) _)
          _ = b ^ (n - 1) := by rw [← pow_add, hi']
    _ = n * b ^ (n - 1) := by simp

/-- **The ODE step of EG Lemma 5.3 (i)** (step 2). Let `g` be continuous, monotone and positive
on `(0, r₀)`, with `g(b) - g(a) = ∫_a^b F` for `0 < a ≤ b < r₀`, and
`g^{(n-1)/n} ≤ K F` a.e. on `(0, r₀)`. Then `g(r) ≥ (r / (n K))ⁿ` on `(0, r₀)`.

Proof: `h = g^{1/n}` satisfies `h(z) - h(t) ≥ (z - t) (h(t)/h(z))^{n-1} / (nK)` for
`0 < t < z < r₀`, so its lower right Dini derivative is `≥ 1/(nK)`; a comparison argument
(`image_le_of_liminf_slope_right_le_deriv_boundary`) gives `h(r) ≥ h(ε) + (r - ε)/(nK)`,
and `ε → 0`. -/
theorem pow_le_of_rpow_le_mul_integral {n : ℕ} (hn : 1 ≤ n) {g F : ℝ → ℝ} {K r₀ : ℝ}
    (hK : 0 < K) (hcont : ContinuousOn g (Ioo 0 r₀)) (hmono : MonotoneOn g (Ioo 0 r₀))
    (hpos : ∀ t ∈ Ioo 0 r₀, 0 < g t)
    (hint : ∀ a b, 0 < a → a ≤ b → b < r₀ →
      IntervalIntegrable F volume a b ∧ g b - g a = ∫ s in a..b, F s)
    (hF : ∀ᵐ s, s ∈ Ioo 0 r₀ → g s ^ (((n : ℝ) - 1) / n) ≤ K * F s) :
    ∀ r ∈ Ioo 0 r₀, (r / (n * K)) ^ n ≤ g r := by
  set m := n - 1 with hm
  set h : ℝ → ℝ := fun t => g t ^ ((n : ℝ)⁻¹) with hh
  set c : ℝ := ((n : ℝ) * K)⁻¹ with hc_def
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := inv_pos.2 (mul_pos hnpos hK)
  have hexp : 0 ≤ ((n : ℝ) - 1) / n :=
    div_nonneg (sub_nonneg.2 (by exact_mod_cast hn)) hnpos.le
  have hpow : ∀ t ∈ Ioo 0 r₀, h t ^ n = g t := fun t ht =>
    Real.rpow_inv_natCast_pow (hpos t ht).le hn0
  have hpowm : ∀ t ∈ Ioo 0 r₀, g t ^ (((n : ℝ) - 1) / n) = h t ^ m := fun t ht => by
    rw [hh, ← Real.rpow_natCast, ← Real.rpow_mul (hpos t ht).le, hm, Nat.cast_sub hn,
      Nat.cast_one]
    congr 1
    field_simp
  have hhpos : ∀ t ∈ Ioo 0 r₀, 0 < h t := fun t ht => Real.rpow_pos_of_pos (hpos t ht) _
  have hhcont : ContinuousOn h (Ioo 0 r₀) :=
    hcont.rpow_const fun t ht => Or.inl (hpos t ht).ne'
  have hhmono : ∀ t z, t ∈ Ioo 0 r₀ → z ∈ Ioo 0 r₀ → t ≤ z → h t ≤ h z := fun t z ht hz htz =>
    Real.rpow_le_rpow (hpos t ht).le (hmono ht hz htz) (inv_nonneg.2 hnpos.le)
  -- Step 1: `K⁻¹ (z - t) h(t)^{n-1} ≤ h(z)ⁿ - h(t)ⁿ`.
  have hstep : ∀ t z, 0 < t → t < z → z < r₀ → K⁻¹ * (z - t) * h t ^ m ≤ h z ^ n - h t ^ n := by
    intro t z ht htz hz
    have htI : t ∈ Ioo 0 r₀ := ⟨ht, htz.trans hz⟩
    obtain ⟨hFi, heq⟩ := hint t z ht htz.le hz
    rw [hpow z ⟨ht.trans htz, hz⟩, hpow t htI, heq, ← hpowm t htI]
    have hconst : ∫ _s in t..z, K⁻¹ * g t ^ (((n : ℝ) - 1) / n) =
        K⁻¹ * (z - t) * g t ^ (((n : ℝ) - 1) / n) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_ae_restrict htz.le intervalIntegrable_const hFi ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hF] with s hs hsI
    have hsI' : s ∈ Ioo 0 r₀ := ⟨ht.trans_le hsI.1, hsI.2.trans_lt hz⟩
    have h2 : g t ^ (((n : ℝ) - 1) / n) ≤ g s ^ (((n : ℝ) - 1) / n) :=
      Real.rpow_le_rpow (hpos t htI).le (hmono htI hsI' hsI.1) hexp
    rw [inv_mul_le_iff₀ hK]
    exact h2.trans (hs hsI')
  -- Step 2: `c (z - t) (h(t)/h(z))^{n-1} ≤ h(z) - h(t)`.
  have hslope : ∀ t z, 0 < t → t < z → z < r₀ →
      c * (h t / h z) ^ m ≤ slope h t z := by
    intro t z ht htz hz
    have htI : t ∈ Ioo 0 r₀ := ⟨ht, htz.trans hz⟩
    have hzI : z ∈ Ioo 0 r₀ := ⟨ht.trans htz, hz⟩
    have hzt : 0 < z - t := sub_pos.2 htz
    have hhz := hhpos z hzI
    have h1 := hstep t z ht htz hz
    have h2 := pow_sub_pow_le_mul (hhpos t htI).le (hhmono t z htI hzI htz.le) n
    rw [slope_def_field, le_div_iff₀ hzt]
    have hzm : 0 < h z ^ m := pow_pos hhz m
    have hkey : K⁻¹ * (z - t) * h t ^ m ≤ n * h z ^ m * (h z - h t) := h1.trans h2
    have hnz : 0 < (n : ℝ) * h z ^ m := mul_pos hnpos hzm
    have hK0 : K ≠ 0 := hK.ne'
    have hn0' : (n : ℝ) ≠ 0 := hnpos.ne'
    have hz0 : h z ≠ 0 := hhz.ne'
    calc c * (h t / h z) ^ m * (z - t) = (K⁻¹ * (z - t) * h t ^ m) / (n * h z ^ m) := by
          rw [hc_def, div_pow]
          field_simp
      _ ≤ (n * h z ^ m * (h z - h t)) / (n * h z ^ m) := by gcongr
      _ = h z - h t := by field_simp
  -- Step 3: the lower right Dini derivative of `h` is `≥ c`.
  have hdini : ∀ t ∈ Ioo 0 r₀, ∀ ρ < c, ∀ᶠ z in 𝓝[>] t, ρ < slope h t z := by
    intro t ht ρ hρ
    have hca : ContinuousAt h t := hhcont.continuousAt (Ioo_mem_nhds ht.1 ht.2)
    have hlim : Tendsto (fun z => c * (h t / h z) ^ m) (𝓝[>] t) (𝓝 (c * (h t / h t) ^ m)) :=
      (((tendsto_const_nhds.div hca.tendsto (hhpos t ht).ne').pow m).const_mul c).mono_left
        nhdsWithin_le_nhds
    rw [div_self (hhpos t ht).ne', one_pow, mul_one] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds hρ), Ioo_mem_nhdsGT ht.2] with z hz hzI
    exact hz.trans_le (hslope t z ht.1 hzI.1 hzI.2)
  -- Step 4: comparison on `[ε, r]`.
  have hcomp : ∀ r ∈ Ioo 0 r₀, ∀ ε ∈ Ioo 0 r, c * (r - ε) ≤ h r := by
    intro r hr ε hε
    have hsub : Icc ε r ⊆ Ioo 0 r₀ := fun t ht => ⟨hε.1.trans_le ht.1, ht.2.trans_lt hr.2⟩
    have key := image_le_of_liminf_slope_right_le_deriv_boundary (f := fun t => -h t)
      (a := ε) (b := r) (hhcont.mono hsub).neg (B := fun t => -h ε - c * (t - ε))
      (B' := fun _ => -c) (by simp) (by fun_prop)
      (fun t _ => by
        have := (((hasDerivAt_id t).sub_const ε).const_mul c).const_sub (-h ε)
        simpa using this.hasDerivWithinAt)
      (fun t ht ρ hρ => by
        have := hdini t (hsub (Ico_subset_Icc_self ht)) (-ρ) (by linarith [show -c < ρ from hρ])
        refine (this.mono fun z hz => ?_).frequently
        rw [slope_neg]
        linarith)
      (right_mem_Icc.2 hε.2.le)
    have hhε := hhpos ε (hsub (left_mem_Icc.2 hε.2.le))
    simp only at key
    linarith
  -- Step 5: `ε → 0`.
  intro r hr
  have hcr : c * r ≤ h r := by
    have hlim : Tendsto (fun ε => c * (r - ε)) (𝓝[>] 0) (𝓝 (c * (r - 0))) :=
      ((tendsto_const_nhds.sub tendsto_id).const_mul c).mono_left nhdsWithin_le_nhds
    rw [sub_zero] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hr.1] with ε hε using hcomp r hr ε hε
  rw [← hpow r hr, div_eq_inv_mul, ← hc_def]
  exact pow_le_pow_left₀ (mul_pos hc hr.1).le hcr n

/-! #### Sphere integrals of indicators -/

theorem sphereIntegral_indicator_nonneg (E : Set (Rn n)) (x : Rn n) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ sphereIntegral (E.indicator 1) x s :=
  mul_nonneg (pow_nonneg hs _)
    (integral_nonneg fun _ => indicator_nonneg (fun _ _ => zero_le_one) _)

/-- `ℋ^{n-1}(E ∩ ∂B_s(x)) ≤ |∂B_s| = n ω_n s^{n-1}`. -/
theorem sphereIntegral_indicator_le (E : Set (Rn n)) (x : Rn n) {s : ℝ} (hs : 0 ≤ s) :
    sphereIntegral (E.indicator 1) x s ≤ n * unitBallVolume n * s ^ (n - 1) := by
  rw [← sphereIntegral_one x s, sphereIntegral, sphereIntegral]
  refine mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
    (ae_of_all _ fun _ => indicator_nonneg (fun _ _ => zero_le_one) _) (integrable_const 1)
    (ae_of_all _ fun ω => ?_)) (pow_nonneg hs _)
  exact indicator_le_self' (fun _ _ => zero_le_one) _

/-- `|∫_{∂B_r(x)} χ_E f| ≤ ℋ^{n-1}(E ∩ ∂B_r(x))` when `|f| ≤ 1` on `∂B_r(x)`. -/
theorem abs_sphereIntegral_indicator_mul_le {E : Set (Rn n)} (hE : MeasurableSet E) (x : Rn n)
    {r : ℝ} (hr : 0 ≤ r) {f : Rn n → ℝ} (hf : ∀ y ∈ sphere x r, |f y| ≤ 1) :
    |sphereIntegral (fun y => E.indicator 1 y * f y) x r| ≤ sphereIntegral (E.indicator 1) x r := by
  rw [sphereIntegral, sphereIntegral, abs_mul, abs_of_nonneg (pow_nonneg hr _)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr _)
  have hmeas : Measurable fun ω : sphere (0 : Rn n) 1 => x + r • (ω : Rn n) := by fun_prop
  have hint : Integrable (fun ω : sphere (0 : Rn n) 1 => E.indicator (1 : Rn n → ℝ)
      (x + r • (ω : Rn n))) (sphereMeasure n) :=
    Integrable.of_bound ((measurable_const.indicator hE).comp hmeas).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by
        by_cases h : x + r • (ω : Rn n) ∈ E <;> simp [h])
  refine (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le hint (ae_of_all _ fun ω => ?_))
  have hmem : x + r • (ω : Rn n) ∈ sphere x r := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul_sphere hr]
  rw [Real.norm_eq_abs, abs_mul]
  by_cases h : x + r • (ω : Rn n) ∈ E
  · simp only [indicator_of_mem h, Pi.one_apply, abs_one, one_mul]
    exact hf _ hmem
  · simp [indicator_of_notMem h]

/-! #### The pair-level estimates -/

variable {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n}

/-- `μ(B_r(x)) > 0` forces `|E ∩ B_r(x)| > 0` when `B_r(x) ⊆ Ω`: otherwise `∫_E div φ = 0` for
every test field `φ` in `B_r(x)`, so `μ(B_r(x)) = 0` (`IsGaussGreenPair.measure_le_iSup`). -/
theorem IsGaussGreenPair.volume_inter_ball_pos (h : IsGaussGreenPair Ω E μ ν)
    (hE : MeasurableSet E) {x : Rn n} {r : ℝ} (hB : ball x r ⊆ Ω) (hμ : 0 < μ (ball x r)) :
    0 < volume (E ∩ ball x r) := by
  refine pos_iff_ne_zero.2 fun h0 => hμ.ne' (nonpos_iff_eq_zero.1 ?_)
  refine (h.measure_le_iSup isOpen_ball hB).trans (iSup₂_le fun φ hφ => iSup_le fun _ => ?_)
  have hae : ∀ᵐ y, y ∉ E ∩ ball x r := measure_eq_zero_iff_ae_notMem.1 h0
  have : ∫ y in E, divergence φ y = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [EventuallyEq, ae_restrict_iff' hE]
    filter_upwards [hae] with y hy hyE
    have hyB : y ∉ ball x r := fun hyB => hy ⟨hyE, hyB⟩
    exact image_eq_zero_of_notMem_tsupport fun h' => hyB (hφ.2.2 (tsupport_divergence_subset φ h'))
  rw [this, ENNReal.ofReal_zero]

/-- **EG Lemma 5.3, (⋆⋆⋆).** Let `x ∈ Ω` with `μ(B_r(x)) > 0` for all `r > 0` and
`⨍_{B_r(x)} ν dμ → v`, `‖v‖ = 1`. Then there is `r₀ > 0` with `B̄_{r₀}(x) ⊆ Ω` such that
`μ(B_r(x)) ≤ 2 ℋ^{n-1}(E ∩ ∂B_r(x)) = 2 F_{χ_E}(r)` for a.e. `r ∈ (0, r₀)`.

Proof (EG step 1, (⋆⋆)): Gauss–Green on `E ∩ B_r(x)` (`integral_divergence_inter_ball_ae`) for a
field `φ ≡ v` on `B̄_{r₀}(x)` gives `0 = ⟪v, ∫_{B_r} ν dμ⟫ + ∫_{E ∩ ∂B_r} ⟪v, (y - x)/r⟫`, and
`⟪v, ⨍_{B_r} ν dμ⟫ > 1/2` for small `r`. -/
theorem IsGaussGreenPair.exists_ae_measure_ball_le_sphereIntegral [NeZero n]
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n}
    (hx : x ∈ Ω) (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    ∃ r₀ > 0, closedBall x r₀ ⊆ Ω ∧ ∀ᵐ r, 0 < r → r < r₀ →
      (μ (ball x r)).toReal ≤ 2 * sphereIntegral (E.indicator 1) x r := by
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  -- `⟪v, ⨍_{B_r} ν dμ⟫ > 1/2` for small `r`.
  have hinner : Tendsto (fun r => ⟪v, (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ⟫)
      (𝓝[>] 0) (𝓝 ⟪v, v⟫) :=
    tendsto_const_nhds.inner hlim
  rw [real_inner_self_eq_norm_sq, hv, one_pow] at hinner
  obtain ⟨r₁, hr₁, hr₁s⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hinner.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) / 2 < 1)))
  set r₀ := min r₁ (ρ / 2) with hr₀_def
  have hr₀ : 0 < r₀ := lt_min hr₁ (half_pos hρ)
  have hr₀Ω : closedBall x r₀ ⊆ Ω :=
    (closedBall_subset_closedBall (min_le_right _ _)).trans
      ((closedBall_subset_ball (half_lt_self hρ)).trans hρΩ)
  refine ⟨r₀, hr₀, hr₀Ω, ?_⟩
  -- The field `φ = c • v` with a cutoff `c ≡ 1` on `B̄_{r₀}(x)`.
  set φ : Rn n → Rn n := fun y => radialCutoff x r₀ 1 y • v with hφ_def
  have hφc1 : ContDiff ℝ 1 φ :=
    ((contDiff_radialCutoff hr₀ one_pos).of_le (by simp)).smul contDiff_const
  have hφcs : HasCompactSupport φ :=
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (r₀ + 1))
      ((support_radialCutoff_subset one_pos).trans ball_subset_closedBall)).smul_right
      (f' := fun _ => v)
  have hφv : ∀ y, ‖y - x‖ ≤ r₀ → φ y = v := fun y hy => by
    simp [hφ_def, radialCutoff_of_le one_pos hy]
  have hφnorm : ∀ y, ‖φ y‖ ≤ 1 := fun y => by
    rw [hφ_def, norm_smul, hv, mul_one, Real.norm_of_nonneg (radialCutoff_nonneg y)]
    exact radialCutoff_le_one y
  filter_upwards [h.integral_divergence_inter_ball_ae hΩ hE x hφc1 hφcs] with r hr hr0 hrr₀
  have hrr₁ : r < r₁ := hrr₀.trans_le (min_le_left _ _)
  have hB : closedBall x r ⊆ Ω := (closedBall_subset_closedBall hrr₀.le).trans hr₀Ω
  have hμfin : μ (ball x r) < ∞ := (measure_mono ball_subset_closedBall).trans_lt
    (h.lt_top_of_isCompact _ (isCompact_closedBall x r) hB)
  have hid := hr hr0 hB
  -- The left side vanishes: `φ` is constant near `B_r(x)`.
  have hdiv0 : ∫ y in E ∩ ball x r, divergence φ y = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hyr₀ : y ∈ ball x r₀ := ball_subset_ball hrr₀.le hy.2
    have hloc : φ =ᶠ[𝓝 y] fun _ => v := by
      filter_upwards [isOpen_ball.mem_nhds hyr₀] with z hz
      exact hφv z (by rw [← dist_eq_norm]; exact (mem_ball.1 hz).le)
    simp [divergence, hloc.fderiv_eq]
  -- The `μ` term is `⟪v, ∫_{B_r} ν dμ⟫`.
  have hνint : Integrable ν (μ.restrict (ball x r)) :=
    Measure.integrableOn_of_bounded (M := 1) hμfin.ne h.measurable_normal.aestronglyMeasurable
      (ae_restrict_of_ae (h.norm_normal.mono fun y hy => hy.le))
  have hμterm : ∫ y in ball x r, ⟪φ y, ν y⟫ ∂μ = ⟪v, ∫ y in ball x r, ν y ∂μ⟫ := by
    rw [← integral_inner hνint v]
    refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
    rw [hφv y ((by rw [← dist_eq_norm]; exact (mem_ball.1 hy).le : ‖y - x‖ ≤ r).trans hrr₀.le)]
  -- The sphere term is bounded by `F(r)`.
  have hsph := abs_sphereIntegral_indicator_mul_le hE x hr0.le
    (f := fun y => ⟪φ y, r⁻¹ • (y - x)⟫) fun y hy => by
      have h1 : ‖r⁻¹ • (y - x)‖ = 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le), ← dist_eq_norm,
          mem_sphere.1 hy, inv_mul_cancel₀ hr0.ne']
      calc |⟪φ y, r⁻¹ • (y - x)⟫| ≤ ‖φ y‖ * ‖r⁻¹ • (y - x)‖ := abs_real_inner_le_norm _ _
        _ = ‖φ y‖ := by rw [h1, mul_one]
        _ ≤ 1 := hφnorm y
  rw [hdiv0, hμterm] at hid
  -- `μ(B_r)/2 < ⟪v, ∫ ν⟫ = -(sphere term) ≤ F(r)`.
  have hm : 0 < (μ (ball x r)).toReal := ENNReal.toReal_pos (hpos r hr0).ne' hμfin.ne
  have h12 := hr₁s ⟨hr0, hrr₁⟩
  simp only [mem_setOf_eq, real_inner_smul_right] at h12
  rw [lt_inv_mul_iff₀ hm] at h12
  have := neg_abs_le (sphereIntegral (fun y => E.indicator 1 y * ⟪φ y, r⁻¹ • (y - x)⟫) x r)
  linarith

/-- `μ(B_r(x)) < ∞` when `B̄_r(x) ⊆ Ω`. -/
theorem IsGaussGreenPair.measure_ball_ne_top (h : IsGaussGreenPair Ω E μ ν) {x : Rn n} {r : ℝ}
    (hB : closedBall x r ⊆ Ω) : μ (ball x r) ≠ ∞ :=
  ((measure_mono ball_subset_closedBall).trans_lt
    (h.lt_top_of_isCompact _ (isCompact_closedBall x r) hB)).ne

/-- **EG Lemma 5.3 (iv)**. At a reduced-boundary point `x` (for the pair
`(μ, ν)`: `x ∈ Ω`, `μ(B_r(x)) > 0` for all `r > 0`, `⨍_{B_r(x)} ν dμ → v`, `‖v‖ = 1`), there is
`r₀ > 0` with `μ(B_r(x)) ≤ A₄ r^{n-1}` for all `0 < r < r₀`, `A₄ = 2 n ω_n`. -/
theorem IsGaussGreenPair.exists_forall_measure_ball_le (hn : 1 ≤ n)
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n}
    (hx : x ∈ Ω) (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      μ (ball x r) ≤ ENNReal.ofReal (densityConstA₄ n * r ^ (n - 1)) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨r₀, hr₀, hr₀Ω, hae⟩ :=
    h.exists_ae_measure_ball_le_sphereIntegral hΩ hE hx hpos hv hlim
  refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
  refine le_ofReal_of_ae_le_of_monotone (f := fun r => μ (ball x r))
    (fun a b hab => measure_mono (ball_subset_ball hab))
    (G := fun r => densityConstA₄ n * r ^ (n - 1)) (by fun_prop) ?_ hr hrr₀
  filter_upwards [hae] with s hs hs0 hsr₀
  rw [← ENNReal.ofReal_toReal
    (h.measure_ball_ne_top ((closedBall_subset_closedBall hsr₀.le).trans hr₀Ω))]
  refine ENNReal.ofReal_le_ofReal ((hs hs0 hsr₀).trans ?_)
  have := sphereIntegral_indicator_le E x hs0.le
  calc 2 * sphereIntegral (E.indicator 1) x s ≤ 2 * (n * unitBallVolume n * s ^ (n - 1)) := by
        linarith
    _ = densityConstA₄ n * s ^ (n - 1) := by unfold densityConstA₄; ring

/-- **EG Lemma 5.3 (i)**. At a reduced-boundary point `x` (for the pair
`(μ, ν)`), there is `r₀ > 0` with `B̄_{r₀}(x) ⊆ Ω` and `|E ∩ B_r(x)| ≥ A₁ rⁿ` for all
`0 < r < r₀`, `A₁ = (n K_n)^{-n}`. -/
theorem IsGaussGreenPair.exists_forall_volume_inter_ball_ge (hn : 2 ≤ n)
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n}
    (hx : x ∈ Ω) (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    ∃ r₀ > 0, closedBall x r₀ ⊆ Ω ∧ ∀ r, 0 < r → r < r₀ →
      ENNReal.ofReal (densityConstA₁ n * r ^ n) ≤ volume (E ∩ ball x r) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨r₀, hr₀, hr₀Ω, hae⟩ :=
    h.exists_ae_measure_ball_le_sphereIntegral hΩ hE hx hpos hv hlim
  refine ⟨r₀, hr₀, hr₀Ω, fun r hr hrr₀ => ?_⟩
  set g : ℝ → ℝ := fun t => (volume (E ∩ ball x t)).toReal with hg
  set F : ℝ → ℝ := fun s => sphereIntegral (E.indicator 1) x s with hF_def
  have hfi : ∀ R, IntegrableOn (E.indicator (1 : Rn n → ℝ)) (ball x R) := fun R =>
    Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne
      (measurable_const.indicator hE).aestronglyMeasurable
      (ae_of_all _ fun y => by by_cases hy : y ∈ E <;> simp [hy])
  have hFi : IntervalIntegrable F volume 0 r₀ := intervalIntegrable_sphereIntegral hr₀.le (hfi r₀)
  have hFi' : ∀ a b, 0 ≤ a → a ≤ b → b ≤ r₀ → IntervalIntegrable F volume a b :=
    fun a b ha hab hb => hFi.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le hr₀.le]; exact Icc_subset_Icc ha hb)
  have hgF : ∀ t, 0 ≤ t → g t = ∫ s in (0 : ℝ)..t, F s := fun t ht =>
    volume_inter_ball_toReal_eq_integral hE x ht
  have hvolfin : ∀ t, volume (E ∩ ball x t) ≠ ∞ := fun t =>
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right)
  have hcont : ContinuousOn g (Ioo 0 r₀) := by
    have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := F)
      (a := 0) (b := r₀) (by
        rw [uIcc_of_le hr₀.le]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hr₀.le).1 hFi)
    rw [uIcc_of_le hr₀.le] at hc
    exact (hc.mono Ioo_subset_Icc_self).congr fun t ht => hgF t ht.1.le
  have hmono : MonotoneOn g (Ioo 0 r₀) := fun a _ b _ hab =>
    ENNReal.toReal_mono (hvolfin b)
      (measure_mono (inter_subset_inter_right _ (ball_subset_ball hab)))
  have hgpos : ∀ t ∈ Ioo 0 r₀, 0 < g t := fun t ht =>
    ENNReal.toReal_pos (h.volume_inter_ball_pos hE (ball_subset_closedBall.trans
      ((closedBall_subset_closedBall ht.2.le).trans hr₀Ω)) (hpos t ht.1)).ne' (hvolfin t)
  have hint : ∀ a b, 0 < a → a ≤ b → b < r₀ →
      IntervalIntegrable F volume a b ∧ g b - g a = ∫ s in a..b, F s := fun a b ha hab hb =>
    ⟨hFi' a b ha.le hab hb.le, by
      rw [hgF b (ha.le.trans hab), hgF a ha.le, intervalIntegral.integral_interval_sub_left
        (hFi' 0 b le_rfl (ha.le.trans hab) hb.le) (hFi' 0 a le_rfl ha.le (hab.trans hb.le))]⟩
  have hae' : ∀ᵐ s, s ∈ Ioo 0 r₀ → g s ^ (((n : ℝ) - 1) / n) ≤ densityConstK n * F s := by
    filter_upwards [hae, h.totalVariationOn_inter_ball_le_ae hΩ hE x] with s hs1 hs2 hsI
    have hsΩ : closedBall x s ⊆ Ω := (closedBall_subset_closedBall hsI.2.le).trans hr₀Ω
    have hF0 : 0 ≤ F s := sphereIntegral_indicator_nonneg E x hsI.1.le
    have hμle : μ (ball x s) ≤ ENNReal.ofReal (2 * F s) := by
      rw [← ENNReal.ofReal_toReal (h.measure_ball_ne_top hsΩ)]
      exact ENNReal.ofReal_le_ofReal (hs1 hsI.1 hsI.2)
    have htv : totalVariationOn univ ((E ∩ ball x s).indicator 1) ≤ ENNReal.ofReal (3 * F s) := by
      refine (hs2 hsI.1 hsΩ).trans ?_
      rw [show 3 * F s = 2 * F s + F s by ring, ENNReal.ofReal_add (by linarith) hF0]
      gcongr
    have hiso := volume_rpow_le_totalVariationOn hn (F := E ∩ ball x s)
      (hE.inter measurableSet_ball) (isBounded_ball.subset inter_subset_right)
    have h3 : volume (E ∩ ball x s) ^ (((n : ℝ) - 1) / n) ≤
        (isoperimetricConst n : ℝ≥0∞) * ENNReal.ofReal (3 * F s) := hiso.trans (by gcongr)
    have h4 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) h3
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (by linarith)] at h4
    refine h4.trans ?_
    have hC := (isoperimetricConst n).2
    unfold densityConstK
    nlinarith
  have key := pow_le_of_rpow_le_mul_integral (by omega) (densityConstK_pos n) hcont hmono hgpos
    hint hae' r ⟨hr, hrr₀⟩
  have hA : densityConstA₁ n * r ^ n = (r / (n * densityConstK n)) ^ n := by
    rw [densityConstA₁, div_eq_inv_mul, mul_pow]
  rw [hA, ← ENNReal.ofReal_toReal (hvolfin r)]
  exact ENNReal.ofReal_le_ofReal key

/-- **EG Lemma 5.3 (ii)**. At a reduced-boundary point `x` (for the pair
`(μ, ν)`), there is `r₀ > 0` with `B̄_{r₀}(x) ⊆ Ω` and `|B_r(x) ∖ E| ≥ A₁ rⁿ` for all
`0 < r < r₀`. Proof: (i) for the complementary pair `(μ, -ν)` of `Eᶜ` (EG step 3). -/
theorem IsGaussGreenPair.exists_forall_volume_ball_diff_ge (hn : 2 ≤ n)
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n}
    (hx : x ∈ Ω) (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    ∃ r₀ > 0, closedBall x r₀ ⊆ Ω ∧ ∀ r, 0 < r → r < r₀ →
      ENNReal.ofReal (densityConstA₁ n * r ^ n) ≤ volume (ball x r \ E) := by
  have hlim' : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, (-ν) y ∂μ)
      (𝓝[>] 0) (𝓝 (-v)) := by
    simpa only [Pi.neg_apply, integral_neg, smul_neg] using hlim.neg
  obtain ⟨r₀, hr₀, hr₀Ω, hb⟩ := (h.compl hE).exists_forall_volume_inter_ball_ge hn hΩ hE.compl
    hx hpos (by rwa [norm_neg]) hlim'
  refine ⟨r₀, hr₀, hr₀Ω, fun r hr hrr₀ => ?_⟩
  rw [diff_eq_compl_inter]
  exact hb r hr hrr₀

/-- **EG Lemma 5.3 (iii)**. At a reduced-boundary point `x` (for the pair
`(μ, ν)`), there is `r₀ > 0` with `μ(B_r(x)) ≥ A₃ r^{n-1}` for all `0 < r < r₀`,
`A₃ = A₁ / 2^{n+1}`. Proof: (i), (ii) and the `L¹` relative isoperimetric inequality
`min(|E ∩ B_r|, |B_r ∖ E|) ≤ 2^{n+1} r μ(B_r)`. -/
theorem IsGaussGreenPair.exists_forall_measure_ball_ge (hn : 2 ≤ n)
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n}
    (hx : x ∈ Ω) (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      ENNReal.ofReal (densityConstA₃ n * r ^ (n - 1)) ≤ μ (ball x r) := by
  obtain ⟨r₁, hr₁, hr₁Ω, h1⟩ := h.exists_forall_volume_inter_ball_ge hn hΩ hE hx hpos hv hlim
  obtain ⟨r₂, hr₂, -, h2⟩ := h.exists_forall_volume_ball_diff_ge hn hΩ hE hx hpos hv hlim
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun r hr hrr => ?_⟩
  have hr1 := hrr.trans_le (min_le_left _ _)
  have hr2 := hrr.trans_le (min_le_right _ _)
  have hB : ball x r ⊆ Ω :=
    ball_subset_closedBall.trans ((closedBall_subset_closedBall hr1.le).trans hr₁Ω)
  have hlow : ENNReal.ofReal (densityConstA₁ n * r ^ n) ≤
      2 ^ (n + 1) * ENNReal.ofReal r * μ (ball x r) :=
    (le_min (h1 r hr hr1) (h2 r hr hr2)).trans (h.min_volume_le_measure_ball hE hB)
  have hA1 := (densityConstA₁_pos (by omega : 1 ≤ n)).le
  have hfac : ENNReal.ofReal (densityConstA₁ n * r ^ n) =
      2 ^ (n + 1) * ENNReal.ofReal r * ENNReal.ofReal (densityConstA₃ n * r ^ (n - 1)) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hrn : r ^ n = r * r ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h2 : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    rw [hrn, densityConstA₃]
    field_simp
  rw [hfac] at hlow
  exact (ENNReal.mul_le_mul_iff_right
    (mul_ne_zero (pow_ne_zero _ two_ne_zero) (ENNReal.ofReal_pos.2 hr).ne')
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) ENNReal.ofReal_ne_top)).1 hlow

/-- **EG Lemma 5.3 (i)–(iv)**, combined. At a reduced-boundary point `x` (for the
pair `(μ, ν)`: `x ∈ Ω`, `μ(B_r(x)) > 0` for `r > 0`, `⨍_{B_r(x)} ν dμ → v`, `‖v‖ = 1`), there is
`r₀ > 0` with `B̄_{r₀}(x) ⊆ Ω` such that for all `0 < r < r₀`:
(i) `|E ∩ B_r(x)| ≥ A₁ rⁿ`, (ii) `|B_r(x) ∖ E| ≥ A₁ rⁿ`, (iii) `μ(B_r(x)) ≥ A₃ r^{n-1}`,
(iv) `μ(B_r(x)) ≤ A₄ r^{n-1}`. The constants depend only on `n`. -/
theorem IsGaussGreenPair.exists_densityEstimates (hn : 2 ≤ n)
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n}
    (hx : x ∈ Ω) (hpos : ∀ r, 0 < r → 0 < μ (ball x r)) {v : Rn n} (hv : ‖v‖ = 1)
    (hlim : Tendsto (fun r => (μ (ball x r)).toReal⁻¹ • ∫ y in ball x r, ν y ∂μ) (𝓝[>] 0)
      (𝓝 v)) :
    ∃ r₀ > 0, closedBall x r₀ ⊆ Ω ∧ ∀ r, 0 < r → r < r₀ →
      ENNReal.ofReal (densityConstA₁ n * r ^ n) ≤ volume (E ∩ ball x r) ∧
      ENNReal.ofReal (densityConstA₁ n * r ^ n) ≤ volume (ball x r \ E) ∧
      ENNReal.ofReal (densityConstA₃ n * r ^ (n - 1)) ≤ μ (ball x r) ∧
      μ (ball x r) ≤ ENNReal.ofReal (densityConstA₄ n * r ^ (n - 1)) := by
  obtain ⟨r₁, hr₁, hr₁Ω, h1⟩ := h.exists_forall_volume_inter_ball_ge hn hΩ hE hx hpos hv hlim
  obtain ⟨r₂, hr₂, -, h2⟩ := h.exists_forall_volume_ball_diff_ge hn hΩ hE hx hpos hv hlim
  obtain ⟨r₃, hr₃, h3⟩ := h.exists_forall_measure_ball_ge hn hΩ hE hx hpos hv hlim
  obtain ⟨r₄, hr₄, h4⟩ := h.exists_forall_measure_ball_le (by omega) hΩ hE hx hpos hv hlim
  refine ⟨min (min r₁ r₂) (min r₃ r₄), lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄),
    (closedBall_subset_closedBall ((min_le_left _ _).trans (min_le_left _ _))).trans hr₁Ω,
    fun r hr hrr => ⟨h1 r hr ?_, h2 r hr ?_, h3 r hr ?_, h4 r hr ?_⟩⟩
  · exact hrr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  · exact hrr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  · exact hrr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  · exact hrr.trans_le ((min_le_right _ _).trans (min_le_right _ _))

/-- **EG Lemma 5.3 (i)–(iv)** at `x ∈ ∂*E = reducedBoundary Ω E`, for any Gauss–Green pair
`(μ, ν)` of `E` (by uniqueness, `IsGaussGreenPair.mem_reducedBoundary_iff`). -/
theorem IsGaussGreenPair.exists_densityEstimates_of_mem_reducedBoundary (hn : 2 ≤ n)
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n}
    (hx : x ∈ reducedBoundary Ω E) :
    ∃ r₀ > 0, closedBall x r₀ ⊆ Ω ∧ ∀ r, 0 < r → r < r₀ →
      ENNReal.ofReal (densityConstA₁ n * r ^ n) ≤ volume (E ∩ ball x r) ∧
      ENNReal.ofReal (densityConstA₁ n * r ^ n) ≤ volume (ball x r \ E) ∧
      ENNReal.ofReal (densityConstA₃ n * r ^ (n - 1)) ≤ μ (ball x r) ∧
      μ (ball x r) ≤ ENNReal.ofReal (densityConstA₄ n * r ^ (n - 1)) := by
  obtain ⟨hxΩ, hpos, v, hv, hlim⟩ := (h.mem_reducedBoundary_iff hΩ).1 hx
  exact h.exists_densityEstimates hn hΩ hE hxΩ hpos hv hlim

/-- **EG Lemma 5.3 (iii)** at `x ∈ reducedBoundary Ω E`. -/
theorem IsGaussGreenPair.exists_forall_measure_ball_ge_of_mem_reducedBoundary (hn : 2 ≤ n)
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n}
    (hx : x ∈ reducedBoundary Ω E) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      ENNReal.ofReal (densityConstA₃ n * r ^ (n - 1)) ≤ μ (ball x r) := by
  obtain ⟨hxΩ, hpos, v, hv, hlim⟩ := (h.mem_reducedBoundary_iff hΩ).1 hx
  exact h.exists_forall_measure_ball_ge hn hΩ hE hxΩ hpos hv hlim

/-- **EG Lemma 5.3 (iv)** at `x ∈ reducedBoundary Ω E`, in the plain local form
`μ(B_r(x)) ≤ A₄ r^{n-1}` for `0 < r < r₀`. -/
theorem IsGaussGreenPair.exists_forall_measure_ball_le_of_mem_reducedBoundary (hn : 1 ≤ n)
    (h : IsGaussGreenPair Ω E μ ν) (hΩ : IsOpen Ω) (hE : MeasurableSet E) {x : Rn n}
    (hx : x ∈ reducedBoundary Ω E) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      μ (ball x r) ≤ ENNReal.ofReal (densityConstA₄ n * r ^ (n - 1)) := by
  obtain ⟨hxΩ, hpos, v, hv, hlim⟩ := (h.mem_reducedBoundary_iff hΩ).1 hx
  exact h.exists_forall_measure_ball_le hn hΩ hE hxΩ hpos hv hlim

end DensityEstimatesAtBoundary

end GMTFoundations
