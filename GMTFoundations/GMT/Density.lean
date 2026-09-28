/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.GMT.ApproxTangent
import GMTFoundations.GMT.HausdorffLebesgue
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Density theorem and Radon–Nikodym for measures dominated by `ℋ^{n-1}⌊S`

Let `S ⊆ Ω` be a measurable, countably `(n-1)`-rectifiable set with locally
finite `ℋ^{n-1}` measure in the open set `Ω`, and let `ρ` be concentrated on `S` with
`ρ(B_r(x)) ≤ C r^{n-1}` whenever `B̄_{2r}(x) ⊆ Ω`. Then `ρ = θ ℋ^{n-1}⌊S` with
`θ(x) = limsup_{r→0} ρ(B_r(x)) / (ω_{n-1} r^{n-1})`.

* `measure_eq_zero_of_hausdorffMeasure_eq_zero`: the upper bound on `ρ` gives `ρ ≪ ℋ^{n-1}`
  (directly from the definition of `μH`).
* `limsup_measure_ball_div_eq`: a limit of `ρ(B̄_r)/(ω r^k)` over closed balls is also the limsup
  over open balls.
* `eq_withDensity_upperDensity`: the representation `ρ = θ ℋ^{n-1}⌊S`. Localize to balls deep
  in `Ω`, apply Radon–Nikodym and Besicovitch differentiation (`Besicovitch.ae_tendsto_rnDeriv`),
  and use the density one theorem (`tendsto_measure_inter_closedBall_div`) to replace
  `ℋ^{n-1}⌊S(B̄_r)` by `ω_{n-1} r^{n-1}`.

## References

* H. Federer, *Geometric Measure Theory*, Springer, 1969.
-/

public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace GMTFoundations.GMT

variable {n : ℕ}

/-! ### Absolute continuity -/

/-- Closed balls, including the degenerate radius `0`, obey the upper bound. -/
theorem measure_closedBall_le_of_bound {k : ℕ} (hk : 1 ≤ k) {Ω : Set (Rn n)}
    {ρ : Measure (Rn n)} {C : ℝ}
    (hbd : ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω → ρ (ball x r) ≤ ENNReal.ofReal (C * r ^ k))
    {y : Rn n} {d s : ℝ} (hs : 0 < s) (hd : 0 ≤ d) (h4 : 4 * d ≤ s) (hyΩ : closedBall y s ⊆ Ω) :
    ρ (closedBall y d) ≤ ENNReal.ofReal (C * (2 * d) ^ k) := by
  rcases hd.lt_or_eq with hd | rfl
  · refine (measure_mono (closedBall_subset_ball (by linarith))).trans
      (hbd y (2 * d) (by positivity) ((closedBall_subset_closedBall (by linarith)).trans hyΩ))
  · have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (C * t ^ k)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => C * t ^ k) (𝓝 0) (𝓝 (C * 0 ^ k)) :=
        tendsto_const_nhds.mul (tendsto_id.pow k)
      rw [zero_pow (by omega), mul_zero] at this
      simpa using (ENNReal.tendsto_ofReal this).mono_left nhdsWithin_le_nhds
    have : ρ (closedBall y 0) ≤ 0 := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsGT (half_pos hs)] with t ht
      exact (measure_mono (closedBall_subset_ball ht.1)).trans
        (hbd y t ht.1 ((closedBall_subset_closedBall (by linarith [ht.2])).trans hyΩ))
    exact this.trans (by positivity)

/-- **Absolute continuity from an upper density bound.**
A measure with `ρ(B_r(x)) ≤ C r^k` on balls deep in `Ω` vanishes on
`μH[k]`-null subsets of `Ω`. -/
theorem measure_eq_zero_of_hausdorffMeasure_eq_zero {k : ℕ} (hk : 1 ≤ k) {Ω : Set (Rn n)}
    (hΩ : IsOpen Ω) {ρ : Measure (Rn n)} {C : ℝ}
    (hbd : ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω → ρ (ball x r) ≤ ENNReal.ofReal (C * r ^ k))
    {E : Set (Rn n)} (hEΩ : E ⊆ Ω) (hE : μH[(k : ℝ)] E = 0) : ρ E = 0 := by
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hbd' : ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω →
      ρ (ball x r) ≤ ENNReal.ofReal (C' * r ^ k) := fun x r hr hx =>
    (hbd x r hr hx).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
  set E' : ℕ → Set (Rn n) := fun j => {x | x ∈ E ∧ closedBall x (1 / ((j : ℝ) + 1)) ⊆ Ω}
  have hEcov : E ⊆ ⋃ j, E' j := by
    intro x hx
    obtain ⟨e, he, hbe⟩ := Metric.isOpen_iff.1 hΩ x (hEΩ hx)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt he
    exact mem_iUnion.2 ⟨j, hx, (closedBall_subset_ball hj).trans hbe⟩
  refine measure_mono_null hEcov (measure_iUnion_null fun j => ?_)
  set s : ℝ := 1 / ((j : ℝ) + 1)
  have hs : 0 < s := by positivity
  set K : ℝ≥0∞ := ENNReal.ofReal (C' * 2 ^ k)
  have hbound : ∀ τ : ℝ≥0∞, τ ≠ 0 → ρ (E' j) ≤ K * τ := by
    intro τ hτ
    have hE'0 : μH[(k : ℝ)] (E' j) = 0 := measure_mono_null (fun x hx => hx.1) hE
    rw [Measure.hausdorffMeasure_apply] at hE'0
    have hδ : (0 : ℝ≥0∞) < ENNReal.ofReal (s / 4) := ENNReal.ofReal_pos.2 (by positivity)
    have h0 := (le_iSup₂ (f := fun (r : ℝ≥0∞) (_ : 0 < r) => ⨅ (t : ℕ → Set (Rn n))
      (_ : E' j ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ r),
        ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ (k : ℝ)) _ hδ).trans hE'0.le
    obtain ⟨t, h0⟩ := iInf_lt_iff.1 (h0.trans_lt (pos_iff_ne_zero.2 hτ))
    obtain ⟨hcov, h0⟩ := iInf_lt_iff.1 h0
    obtain ⟨hdiam, hsum⟩ := iInf_lt_iff.1 h0
    have hpiece : ∀ i, ρ (t i ∩ E' j) ≤
        K * ⨆ _ : (t i).Nonempty, Metric.ediam (t i) ^ (k : ℝ) := by
      intro i
      rcases (t i ∩ E' j).eq_empty_or_nonempty with he | ⟨y, hyt, hyE⟩
      · rw [he, measure_empty]
        positivity
      have hfin : Metric.ediam (t i) ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam i)
      set d := (Metric.ediam (t i)).toReal
      have hd4 : 4 * d ≤ s := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam i)
        rw [ENNReal.toReal_ofReal (by positivity)] at this
        linarith
      have hsub : t i ∩ E' j ⊆ closedBall y d := by
        rintro z ⟨hzt, -⟩
        rw [mem_closedBall, dist_edist]
        exact ENNReal.toReal_mono hfin (Metric.edist_le_ediam_of_mem hzt hyt)
      calc ρ (t i ∩ E' j) ≤ ρ (closedBall y d) := measure_mono hsub
        _ ≤ ENNReal.ofReal (C' * (2 * d) ^ k) :=
          measure_closedBall_le_of_bound hk hbd' hs ENNReal.toReal_nonneg hd4 hyE.2
        _ = K * Metric.ediam (t i) ^ (k : ℝ) := by
          rw [ENNReal.rpow_natCast, mul_pow, ← mul_assoc, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]
        _ ≤ _ := by
          gcongr
          exact le_iSup_of_le ⟨y, hyt⟩ le_rfl
    calc ρ (E' j) ≤ ρ (⋃ i, t i ∩ E' j) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hx)
          exact mem_iUnion.2 ⟨i, hi, hx⟩
      _ ≤ ∑' i, ρ (t i ∩ E' j) := measure_iUnion_le _
      _ ≤ ∑' i, K * ⨆ _ : (t i).Nonempty, Metric.ediam (t i) ^ (k : ℝ) :=
        ENNReal.tsum_le_tsum hpiece
      _ = K * ∑' i, ⨆ _ : (t i).Nonempty, Metric.ediam (t i) ^ (k : ℝ) := ENNReal.tsum_mul_left
      _ ≤ K * τ := by gcongr
  have hlim : Tendsto (fun m : ℕ => K * (m : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr ENNReal.ofReal_ne_top)
  exact le_antisymm (ge_of_tendsto' hlim fun m => hbound _ (ENNReal.inv_ne_zero.2
    (ENNReal.natCast_ne_top m))) (by positivity)

/-! ### Open versus closed balls -/

/-- If `ρ(B̄_r(x)) / (ω r^k)` converges to `h`, then `limsup ρ(B_r(x)) / (ω r^k) = h`. -/
theorem limsup_measure_ball_div_eq {ρ : Measure (Rn n)} {x : Rn n} {k : ℕ} {ω : ℝ}
    {h : ℝ≥0∞}
    (hlim : Tendsto (fun r => ρ (closedBall x r) / ENNReal.ofReal (ω * r ^ k)) (𝓝[>] 0) (𝓝 h)) :
    limsup (fun r => ρ (ball x r) / ENNReal.ofReal (ω * r ^ k)) (𝓝[>] 0) = h := by
  refine le_antisymm ?_ ?_
  · rw [← hlim.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall fun r =>
      ENNReal.div_le_div_right (measure_mono ball_subset_closedBall) _)
  · -- `t^k h ≤ limsup` for every `t ∈ (0, 1)`
    have ht : ∀ t : ℝ, 0 < t → t < 1 → ENNReal.ofReal (t ^ k) * h ≤
        limsup (fun r => ρ (ball x r) / ENNReal.ofReal (ω * r ^ k)) (𝓝[>] 0) := by
      intro t ht0 ht1
      have hlim' := ENNReal.Tendsto.const_mul (hlim.comp (tendsto_const_mul_nhdsGT ht0))
        (a := ENNReal.ofReal (t ^ k)) (Or.inr ENNReal.ofReal_ne_top)
      rw [← hlim'.limsup_eq]
      refine limsup_le_limsup ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      simp only [Function.comp_apply]
      have hmono : ρ (closedBall x (t * r)) ≤ ρ (ball x r) :=
        measure_mono (closedBall_subset_ball (by nlinarith))
      have he : ENNReal.ofReal (ω * (t * r) ^ k) =
          ENNReal.ofReal (t ^ k) * ENNReal.ofReal (ω * r ^ k) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      have ht0' : ENNReal.ofReal (t ^ k) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
      rw [he, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ ht0' ENNReal.ofReal_ne_top]
      exact ENNReal.div_le_div_right hmono _
    have hlim1 : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ k) * h) (𝓝[<] 1) (𝓝 h) := by
      have : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ k)) (𝓝[<] 1) (𝓝 1) := by
        have := ENNReal.tendsto_ofReal ((tendsto_id (x := 𝓝 (1 : ℝ))).pow k)
        simpa using this.mono_left nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const this (Or.inl one_ne_zero)
    refine le_of_tendsto hlim1 ?_
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht'
    exact ht t ht'.1 ht'.2

/-! ### Density representation -/

/-- **Density representation** (density theorem plus Radon–Nikodym): `ρ = θ ℋ^{n-1}⌊S` with `θ`
the upper density of `ρ`, assuming the normalization `ℋ^{n-1} = ℒ^{n-1}` on `ℝ^{n-1}`. -/
theorem eq_withDensity_upperDensity (hn : 2 ≤ n)
    (hHausVol : hausdorffN (n - 1) (n - 1) = (volume : Measure (Rn (n - 1)))) {Ω S : Set (Rn n)}
    (hΩ : IsOpen Ω) (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (hrect : IsCountablyRectifiable n (n - 1) S)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ S) < ∞)
    {ρ : Measure (Rn n)} (hρS : ρ Sᶜ = 0) (C : ℝ)
    (hbd : ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω →
      ρ (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) :
    ρ = ((hausdorffN n (n - 1)).restrict S).withDensity fun x =>
      limsup (fun r => ρ (ball x r) / ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)))
        (𝓝[>] 0) := by
  rw [hausdorffN_eq_euclideanHausdorffMeasure hHausVol] at hfin ⊢
  set μ : Measure (Rn n) := μHE[n - 1]
  set k := n - 1
  set ω := unitBallVolume k
  have hω : 0 < ω := unitBallVolume_pos k
  set σ := μ.restrict S
  set θ : Rn n → ℝ≥0∞ := fun x =>
    limsup (fun r => ρ (ball x r) / ENNReal.ofReal (ω * r ^ k)) (𝓝[>] 0)
  -- (1) absolute continuity
  have hac : ∀ A, σ A = 0 → ρ A = 0 := by
    intro A hA
    rw [Measure.restrict_apply' hS] at hA
    have h1 : ρ (A ∩ S) = 0 := measure_eq_zero_of_hausdorffMeasure_eq_zero (by omega) hΩ hbd
      (inter_subset_right.trans hSΩ) (euclideanHausdorffMeasure_eq_zero_iff.1 hA)
    have h2 : ρ (A \ S) = 0 := measure_mono_null (fun x hx => hx.2) hρS
    rw [← measure_inter_add_diff A hS, h1, h2, add_zero]
  -- (2) density one, `σ`-a.e.
  have hdens : ∀ᵐ x ∂σ,
      Tendsto (fun r => σ (closedBall x r) / ENNReal.ofReal (ω * r ^ k)) (𝓝[>] 0) (𝓝 1) := by
    refine (ae_restrict_iff' hS).2 (measure_mono_null ?_ (measure_not_forall_exists_isGoodPiece hn
      hΩ hS hSΩ hrect fun K hK hKΩ => (hfin K hK hKΩ).ne))
    intro x hx
    by_contra hc
    apply hx
    intro hxS
    have h : ∀ m : ℕ, ∃ G ν, IsGoodPiece (n - 1) S G ν (1 / ((m : ℝ) + 2)) x := by
      by_contra h'
      exact hc ⟨hxS, h'⟩
    refine (tendsto_measure_inter_closedBall_div hn h).congr fun r => ?_
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
  -- (3) both sides vanish outside `Ω`
  have hρΩ : ρ Ωᶜ = 0 := measure_mono_null (compl_subset_compl.2 hSΩ) hρS
  have hσΩ : σ Ωᶜ = 0 := by
    rw [Measure.restrict_apply' hS, show Ωᶜ ∩ S = ∅ from
      eq_empty_of_forall_notMem fun x hx => hx.1 (hSΩ hx.2), measure_empty]
  have hWΩ : (σ.withDensity θ) Ωᶜ = 0 := withDensity_absolutelyContinuous σ θ hσΩ
  -- (4) a countable cover of `Ω` by balls deep in `Ω`
  have hd : ∀ x ∈ Ω, ∃ d > 0, closedBall x (2 * d) ⊆ Ω := by
    intro x hx
    obtain ⟨e, he, hbe⟩ := Metric.isOpen_iff.1 hΩ x hx
    exact ⟨e / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hbe⟩
  choose! d hd0 hdΩ using hd
  obtain ⟨t, htΩ, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x => ball x (d x)) (s := Ω)
    (fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hd0 x hx)))
  haveI := htc.to_subtype
  have hΩU : Ω = ⋃ q : t, ball (q : Rn n) (d q) := by
    refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun q => ?_)
    · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 (hcov hx)
      exact mem_iUnion.2 ⟨⟨q, hq⟩, hxq⟩
    · exact ball_subset_closedBall.trans ((closedBall_subset_closedBall (by
        linarith [hd0 q (htΩ q.2)])).trans (hdΩ q (htΩ q.2)))
  rw [← Measure.restrict_eq_self_of_ae_mem (μ := ρ) (s := Ω) (measure_mono_null
      (fun x hx => hx) hρΩ),
    ← Measure.restrict_eq_self_of_ae_mem (μ := σ.withDensity θ) (s := Ω) (measure_mono_null
      (fun x hx => hx) hWΩ), hΩU]
  refine Measure.restrict_iUnion_congr.2 fun q => ?_
  -- (5) the local statement on `B = B_d(q)`
  set B := ball (q : Rn n) (d q)
  have hq := hd0 q (htΩ q.2)
  have hBm : MeasurableSet B := measurableSet_ball
  haveI : IsFiniteMeasure (ρ.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (hbd q (d q) hq (hdΩ q (htΩ q.2))).trans_lt ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure (σ.restrict B) := ⟨by
    rw [Measure.restrict_apply_univ, Measure.restrict_apply hBm]
    refine (measure_mono (inter_subset_inter_left _ ball_subset_closedBall)).trans_lt
      (hfin _ (isCompact_closedBall _ _) ?_)
    exact (closedBall_subset_closedBall (by linarith)).trans (hdΩ q (htΩ q.2))⟩
  have hacB : ρ.restrict B ≪ σ.restrict B := fun A hA => by
    rw [Measure.restrict_apply' hBm] at hA ⊢
    exact hac _ hA
  haveI : (ρ.restrict B).HaveLebesgueDecomposition (σ.restrict B) :=
    Measure.haveLebesgueDecomposition_of_sigmaFinite _ _
  have hRN := Measure.withDensity_rnDeriv_eq _ _ hacB
  have hBes := Besicovitch.ae_tendsto_rnDeriv (ρ.restrict B) (σ.restrict B)
  have hθ : (ρ.restrict B).rnDeriv (σ.restrict B) =ᵐ[σ.restrict B] θ := by
    filter_upwards [hBes, ae_restrict_of_ae hdens, ae_restrict_mem hBm] with x h1 h2 hxB
    obtain ⟨e, he, hbe⟩ := Metric.isOpen_iff.1 isOpen_ball x hxB
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall x r ⊆ B := by
      filter_upwards [Ioo_mem_nhdsGT he] with r hr
      exact (closedBall_subset_ball hr.2).trans hbe
    have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2⁻¹ < σ (closedBall x r) / ENNReal.ofReal (ω * r ^ k) :=
      (tendsto_order.1 h2).1 _ (ENNReal.inv_lt_one.2 (by norm_num))
    have hprod := ENNReal.Tendsto.mul h1 (Or.inr ENNReal.one_ne_top) h2 (Or.inl one_ne_zero)
    rw [mul_one] at hprod
    refine (limsup_measure_ball_div_eq (hprod.congr' ?_)).symm
    filter_upwards [hsmall, hpos] with r hr hr'
    rw [Measure.restrict_apply measurableSet_closedBall, Measure.restrict_apply
      measurableSet_closedBall, inter_eq_left.2 hr]
    have h0 : σ (closedBall x r) ≠ 0 := by
      intro h0
      rw [h0, ENNReal.zero_div] at hr'
      exact (not_lt_of_ge (by positivity)) hr'
    have htop : σ (closedBall x r) ≠ ∞ := by
      refine ne_top_of_le_ne_top (measure_ne_top (σ.restrict B) univ) ?_
      rw [Measure.restrict_apply_univ]
      exact measure_mono (hr.trans subset_rfl)
    simp only [div_eq_mul_inv]
    rw [mul_assoc, ← mul_assoc (σ (closedBall x r))⁻¹, ENNReal.inv_mul_cancel h0 htop, one_mul]
  rw [restrict_withDensity hBm, ← withDensity_congr_ae hθ, hRN]

/-- **Unconditional form** of `eq_withDensity_upperDensity`: the hypothesis
`ℋ^{n-1} = ℒ^{n-1}` on `ℝ^{n-1}` is `hausdorffN_self_eq_volume` (`GMT/HausdorffLebesgue.lean`). -/
theorem eq_withDensity_upperDensity' (hn : 2 ≤ n) {Ω S : Set (Rn n)}
    (hΩ : IsOpen Ω) (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (hrect : IsCountablyRectifiable n (n - 1) S)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω → hausdorffN n (n - 1) (K ∩ S) < ∞)
    {ρ : Measure (Rn n)} (hρS : ρ Sᶜ = 0) (C : ℝ)
    (hbd : ∀ x r, 0 < r → closedBall x (2 * r) ⊆ Ω →
      ρ (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) :
    ρ = ((hausdorffN n (n - 1)).restrict S).withDensity fun x =>
      limsup (fun r => ρ (ball x r) / ENNReal.ofReal (unitBallVolume (n - 1) * r ^ (n - 1)))
        (𝓝[>] 0) :=
  eq_withDensity_upperDensity hn (hausdorffN_self_eq_volume (n - 1)) hΩ hS hSΩ hrect hfin hρS C hbd

end GMTFoundations.GMT
