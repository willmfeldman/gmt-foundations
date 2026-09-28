/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Claims #1 and #2 of Evans–Gariepy Thm 5.23, in abstract form

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

This file isolates the two combinatorial/measure-theoretic claims in the proof of the criterion
for finite perimeter (EG Thm 5.23, steps 3 and 5) from the concrete sets `G(k)`, `H(k)` of EG
step 2; the concrete instances are in `Perimeter/Criterion.lean`, where they are used for the
null case of the criterion.

Points of `ℝⁿ` are written in split coordinates `(t, z) ∈ ℝ × ℝ^{n-1}`, with the line direction
first (`MeasurableEquiv.piFinSuccAbove`). The factor `ℝ^{n-1}` is `Fin m → ℝ` with the sup norm, so
that its closed balls are cubes of volume `(2r)^m` (`Real.volume_pi_closedBall`).

* **Lebesgue density** (`volume_eq_zero_of_frequently_le_half`): a set `A ⊆ ℝ^m` at each of whose
  points `|A ∩ B̄_r(z)| ≤ ½ |B̄_r(z)|` for arbitrarily small `r` is null. `A` need not be
  measurable (Mathlib's `Besicovitch.ae_tendsto_measure_inter_div` is for arbitrary sets); this is
  the "limsup ≤ 2/3 forces measure 0" step at the end of EG Claim #1.
* **Claim #1** (`volume_image_snd_eq_zero`, `volume_image_snd_eq_zero'`): let `T, O ⊆ ℝ × ℝ^m`.
  If from every point `p ∈ T` the open ray of length `2δ` in the `+t` direction (resp. `−t`) lies in
  `O`, and `O` has small measure in the boxes `[p₁ - r, p₁ + r] × B̄_{2r}(p₂)` (`p ∈ T`, `r < δ`),
  then the projection `Prod.snd '' T` is null. This is EG's Claim #1 for `G⁺(k, m)` (resp. `G⁻`);
  `H^±` is the same statement with `I` in place of `O`.
* **Claim #2** (`exists_mem_Icc_not_mem_union`): on a single line, parametrized by `ℝ`, with
  increasing closed disjoint families `G k`, `H k` covering `I`, `O`, such that non-`O` points
  accumulate at every point of `G k` from the right and non-`I` points accumulate at every point
  of `H k` from the left: if `u < v`, `u ∈ I`, `v ∈ O`, then some `t ∈ [u, v]` lies outside
  `I ∪ O`. This is EG's nested-interval argument.

## Deviations from EG (constants and bookkeeping only)

* EG takes slabs `{(j-1)/m ≤ xₙ < j/m}` and rays of length `3/m`; we take slabs of width `δ` and
  rays of length `2δ`, and EG's ball `B(b, 3r)` becomes the box `[b₁ - r, b₁ + r] × B̄_{2r}(b₂)`
  (the concrete file puts the box in a Euclidean ball of radius `(2m + 2) r`).
* The density bound is `|A ∩ B̄_r(z)| ≤ 2c/2^m · |B̄_r(z)| ≤ ½ |B̄_r(z)|` (hypothesis `4c ≤ 2^m`)
  instead of EG's `2/3`.
* In EG's proof of Claim #1, `sup{xₙ | x ∈ G_j ∩ P⁻¹(B(x, r))}` should read `B(z, r)`, and the
  measurability of `P(G_j)` and of the products used is not checked. We state Claim #1 for
  arbitrary sets and work with outer measure (the product formula `Measure.prod_prod` and the
  Besicovitch density theorem hold for arbitrary sets), so no measurability is needed.
* In Claim #2, EG's contradiction hypothesis "`(z, t) ∈ O ∪ I` for `u < t < v`" is used at each
  step to turn "non-`O`" into "`I`" (and "non-`I`" into "`O`"); the final point is shown to lie
  outside `⋃ₖ G k ∪ H k ⊇ I ∪ O` directly, without EG's `limsup ≥ α(n-1)/3^{n+1}` computation.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

public section

namespace GMTFoundations

/-! ### Lebesgue density for arbitrary sets in `ℝ^m` (sup norm) -/

/-- If at every point `z ∈ A` the relative measure `|A ∩ B̄_r(z)| / |B̄_r(z)|` is at most `1/2`
for arbitrarily small `r > 0`, then `A` is null. `A` is arbitrary (outer measure). -/
theorem volume_eq_zero_of_frequently_le_half {m : ℕ} {A : Set (Fin m → ℝ)}
    (h : ∀ z ∈ A, ∃ᶠ r in 𝓝[>] (0 : ℝ),
      volume (A ∩ closedBall z r) ≤ 2⁻¹ * volume (closedBall z r)) :
    volume A = 0 := by
  have hae := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Fin m → ℝ)) A
  rw [ae_iff] at hae
  refine le_antisymm ?_ bot_le
  rw [← hae, ← Measure.restrict_apply_self]
  refine measure_mono fun z hz ht => ?_
  have hlt : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      2⁻¹ < volume (A ∩ closedBall z r) / volume (closedBall z r) :=
    ht.eventually (lt_mem_nhds hlt)
  obtain ⟨r, hr1, hr2, hr3⟩ := ((h z hz).and_eventually (hev.and self_mem_nhdsWithin)).exists
  have hpos : volume (closedBall z r) ≠ 0 := (measure_closedBall_pos _ _ hr3).ne'
  have hfin : volume (closedBall z r) ≠ ∞ := measure_closedBall_lt_top.ne
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hpos) (Or.inl hfin)] at hr2
  exact absurd hr1 (not_le.2 hr2)

/-! ### Claim #1 -/

/-- EG Thm 5.23, **Claim #1**, on one slab `a ≤ t < a + δ`. -/
theorem volume_image_snd_eq_zero_of_slab {m : ℕ} {T O : Set (ℝ × (Fin m → ℝ))} {a δ : ℝ}
    {c : ℝ≥0∞} (hc : 4 * c ≤ 2 ^ m) (hT : ∀ p ∈ T, a ≤ p.1 ∧ p.1 < a + δ)
    (hray : ∀ p ∈ T, ∀ s, 0 < s → s < 2 * δ → (p.1 + s, p.2) ∈ O)
    (hdens : ∀ p ∈ T, ∀ r, 0 < r → r < δ →
      volume (O ∩ Icc (p.1 - r) (p.1 + r) ×ˢ closedBall p.2 (2 * r)) ≤
        c * ENNReal.ofReal r ^ (m + 1)) :
    volume (Prod.snd '' T) = 0 := by
  set A := Prod.snd '' T
  refine volume_eq_zero_of_frequently_le_half fun z _ => Eventually.frequently ?_
  have hδ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ ∨ δ ≤ 0 := by
    rcases lt_or_ge 0 δ with hδ | hδ
    · filter_upwards [Ioo_mem_nhdsGT hδ] with r hr using Or.inl hr.2
    · exact Eventually.of_forall fun _ => Or.inr hδ
  filter_upwards [hδ, self_mem_nhdsWithin] with r hrδ (hr : 0 < r)
  -- the points of `T` over `B̄_r(z)`
  set Tr := {p ∈ T | p.2 ∈ closedBall z r}
  rcases (Prod.fst '' Tr).eq_empty_or_nonempty with he | hne
  · have : A ∩ closedBall z r = ∅ := by
      ext w
      simp only [A, mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨p, hp, rfl⟩ hw
      exact (eq_empty_iff_forall_notMem.1 he) p.1 ⟨p, ⟨hp, hw⟩, rfl⟩
    rw [this, measure_empty]
    exact bot_le
  obtain ⟨_, p₀, hp₀, rfl⟩ := hne
  have hrδ : r < δ := hrδ.resolve_right fun h => by
    have := hT p₀ hp₀.1
    linarith
  have hbdd : BddAbove (Prod.fst '' Tr) := ⟨a + δ, by
    rintro _ ⟨p, hp, rfl⟩
    exact (hT p hp.1).2.le⟩
  set M := sSup (Prod.fst '' Tr)
  obtain ⟨_, ⟨b, hb, rfl⟩, hbM⟩ :=
    exists_lt_of_lt_csSup (⟨p₀.1, p₀, hp₀, rfl⟩ : (Prod.fst '' Tr).Nonempty)
      (show M - r / 2 < M by linarith)
  -- the box `[b₁ + r/2, b₁ + r] × (A ∩ B̄_r(z))` lies in `O` and in the box around `b`
  have hbox : Icc (b.1 + r / 2) (b.1 + r) ×ˢ (A ∩ closedBall z r) ⊆
      O ∩ Icc (b.1 - r) (b.1 + r) ×ˢ closedBall b.2 (2 * r) := by
    rintro ⟨s, w⟩ ⟨hs, ⟨p, hp, rfl⟩, hw⟩
    have hpM : p.1 ≤ M := le_csSup hbdd ⟨p, ⟨hp, hw⟩, rfl⟩
    have hpa := hT p hp
    have hba := hT b hb.1
    refine ⟨?_, ⟨by linarith [hs.1], hs.2⟩, ?_⟩
    · have := hray p hp (s - p.1) (by linarith [hs.1]) (by linarith [hs.2])
      simpa using this
    · rw [mem_closedBall] at hw ⊢
      have := hb.2
      rw [mem_closedBall] at this
      calc dist p.2 b.2 ≤ dist p.2 z + dist z b.2 := dist_triangle _ _ _
        _ ≤ r + r := add_le_add hw (by rw [dist_comm]; exact this)
        _ = 2 * r := by ring
  have hmeas := (measure_mono hbox).trans (hdens b hb.1 r hr hrδ)
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    show b.1 + r - (b.1 + r / 2) = r / 2 by ring] at hmeas
  rw [Real.volume_pi_closedBall _ hr.le, Fintype.card_fin]
  -- arithmetic: `(r/2) X ≤ c r^{m+1}` and `4c ≤ 2^m` give `X ≤ ½ (2r)^m`
  set R := ENNReal.ofReal r
  have hR0 : R ≠ 0 := by simpa [R] using hr
  have hRt : R ≠ ∞ := ENNReal.ofReal_ne_top
  have hr2 : ENNReal.ofReal (r / 2) = R / 2 :=
    ENNReal.ofReal_div_of_pos two_pos |>.trans (by simp [R])
  rw [hr2] at hmeas
  have h2R0 : R / 2 ≠ 0 := by simp [hR0]
  have h2Rt : R / 2 ≠ ∞ := ENNReal.div_ne_top hRt two_ne_zero
  rw [← ENNReal.mul_le_mul_iff_right h2R0 h2Rt]
  refine hmeas.trans ?_
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
    mul_pow, pow_succ]
  calc c * (R ^ m * R) = R / 2 * 2⁻¹ * (4 * c) * R ^ m := by
        rw [ENNReal.div_eq_inv_mul]
        rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
        have h2 : (2 : ℝ≥0∞)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
        calc c * (R ^ m * R) = ((2⁻¹ * 2) * (2⁻¹ * 2)) * c * R ^ m * R := by rw [h2]; ring
          _ = _ := by ring
    _ ≤ R / 2 * 2⁻¹ * 2 ^ m * R ^ m := by gcongr
    _ = R / 2 * (2⁻¹ * (2 ^ m * R ^ m)) := by ring

/-- EG Thm 5.23, **Claim #1** (`G⁺`): if `O` contains the open ray `{(p₁ + s, p₂) : 0 < s < 2δ}`
from every point `p ∈ T`, and `O` has measure `≤ c r^{m+1}` in the boxes
`[p₁ - r, p₁ + r] × B̄_{2r}(p₂)` for `p ∈ T`, `0 < r < δ`, with `4c ≤ 2^m`, then the projection
of `T` to `ℝ^m` is null. -/
theorem volume_image_snd_eq_zero {m : ℕ} {T O : Set (ℝ × (Fin m → ℝ))} {δ : ℝ} (hδ : 0 < δ)
    {c : ℝ≥0∞} (hc : 4 * c ≤ 2 ^ m)
    (hray : ∀ p ∈ T, ∀ s, 0 < s → s < 2 * δ → (p.1 + s, p.2) ∈ O)
    (hdens : ∀ p ∈ T, ∀ r, 0 < r → r < δ →
      volume (O ∩ Icc (p.1 - r) (p.1 + r) ×ˢ closedBall p.2 (2 * r)) ≤
        c * ENNReal.ofReal r ^ (m + 1)) :
    volume (Prod.snd '' T) = 0 := by
  have hT : T = ⋃ j : ℤ, T ∩ {p | j * δ ≤ p.1 ∧ p.1 < j * δ + δ} := by
    ext p
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    refine ⟨fun hp => ⟨⌊p.1 / δ⌋, hp, ?_, ?_⟩, fun ⟨_, hp, _⟩ => hp⟩
    · have := Int.floor_le (p.1 / δ)
      rwa [le_div_iff₀ hδ] at this
    · have := Int.lt_floor_add_one (p.1 / δ)
      rw [div_lt_iff₀ hδ] at this
      linarith
  rw [hT, image_iUnion]
  refine measure_iUnion_null fun j => volume_image_snd_eq_zero_of_slab (a := j * δ) hc
    (fun p hp => hp.2) (fun p hp => hray p hp.1) (fun p hp => hdens p hp.1)

/-- EG Thm 5.23, **Claim #1** (`G⁻`): the reflected version of `volume_image_snd_eq_zero`, with
the rays `{(p₁ - s, p₂) : 0 < s < 2δ}`. -/
theorem volume_image_snd_eq_zero' {m : ℕ} {T O : Set (ℝ × (Fin m → ℝ))} {δ : ℝ} (hδ : 0 < δ)
    {c : ℝ≥0∞} (hc : 4 * c ≤ 2 ^ m)
    (hray : ∀ p ∈ T, ∀ s, 0 < s → s < 2 * δ → (p.1 - s, p.2) ∈ O)
    (hdens : ∀ p ∈ T, ∀ r, 0 < r → r < δ →
      volume (O ∩ Icc (p.1 - r) (p.1 + r) ×ˢ closedBall p.2 (2 * r)) ≤
        c * ENNReal.ofReal r ^ (m + 1)) :
    volume (Prod.snd '' T) = 0 := by
  set ρ : (ℝ × (Fin m → ℝ)) ≃ᵐ (ℝ × (Fin m → ℝ)) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.neg ℝ) (MeasurableEquiv.refl _)
  have hρ : MeasurePreserving ρ volume volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _)
  have hρapp : ∀ p, ρ p = (-p.1, p.2) := fun _ => rfl
  have himg : Prod.snd '' (ρ ⁻¹' T) = Prod.snd '' T := by
    ext w
    simp only [mem_image, mem_preimage, hρapp]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(-p.1, p.2), by simpa using hp, rfl⟩
  rw [← himg]
  refine volume_image_snd_eq_zero (O := ρ ⁻¹' O) hδ hc (fun p hp s hs hs' => ?_)
    (fun p hp r hr hr' => ?_)
  · simp only [mem_preimage, hρapp] at hp ⊢
    have := hray _ hp s hs hs'
    rwa [show -(p.1 + s) = -p.1 - s by ring]
  · simp only [mem_preimage, hρapp] at hp
    have hpre : ρ ⁻¹' (O ∩ Icc (-p.1 - r) (-p.1 + r) ×ˢ closedBall p.2 (2 * r)) =
        ρ ⁻¹' O ∩ Icc (p.1 - r) (p.1 + r) ×ˢ closedBall p.2 (2 * r) := by
      ext q
      simp only [mem_preimage, mem_inter_iff, mem_prod, mem_Icc, hρapp]
      constructor
      · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
        exact ⟨h1, ⟨by linarith, by linarith⟩, h4⟩
      · rintro ⟨h1, ⟨h2, h3⟩, h4⟩
        exact ⟨h1, ⟨by linarith, by linarith⟩, h4⟩
    rw [← hpre, hρ.measure_preimage_equiv]
    exact hdens _ hp r hr hr'

/-! ### Claim #2 -/

/-- EG Thm 5.23, **Claim #2**, on one line parametrized by `ℝ`. Let `G k`, `H k` be increasing,
closed and pairwise disjoint (`G k ∩ H k = ∅`), with `I ⊆ ⋃ₖ G k` and `O ⊆ ⋃ₖ H k`. Suppose that
at every point of `G k` there are points outside `O` arbitrarily close on the right, and at every
point of `H k` there are points outside `I` arbitrarily close on the left (the line avoids the
projections of `G⁺(k, m)` and `H⁻(k, m)`). If `u < v`, `u ∈ I`, `v ∈ O`, then some `t ∈ [u, v]` lies
outside `I ∪ O`. -/
theorem exists_mem_Icc_not_mem_union {I O : Set ℝ} {G H : ℕ → Set ℝ}
    (hGm : Monotone G) (hHm : Monotone H) (hGc : ∀ k, IsClosed (G k))
    (hHc : ∀ k, IsClosed (H k)) (hGH : ∀ k, Disjoint (G k) (H k))
    (hIG : I ⊆ ⋃ k, G k) (hOH : O ⊆ ⋃ k, H k)
    (hG : ∀ k, ∀ x ∈ G k, ∀ ε > 0, ∃ y ∈ Ioo x (x + ε), y ∉ O)
    (hH : ∀ k, ∀ x ∈ H k, ∀ ε > 0, ∃ y ∈ Ioo (x - ε) x, y ∉ I)
    {u v : ℝ} (huv : u < v) (hu : u ∈ I) (hv : v ∈ O) :
    ∃ t ∈ Icc u v, t ∉ I ∪ O := by
  by_contra! hall
  -- states `(k, s, t)` with `u ≤ s < t ≤ v`, `s ∈ I`, `t ∈ O`
  let P : ℕ × ℝ × ℝ → Prop := fun x => u ≤ x.2.1 ∧ x.2.1 < x.2.2 ∧ x.2.2 ≤ v ∧
    x.2.1 ∈ I ∧ x.2.2 ∈ O
  let R : ℕ × ℝ × ℝ → ℕ × ℝ × ℝ → Prop := fun x y => x.1 < y.1 ∧ x.2.1 ≤ y.2.1 ∧
    y.2.2 ≤ x.2.2 ∧ ∀ w ∈ Icc y.2.1 y.2.2, w ∉ G y.1 ∧ w ∉ H y.1
  have step : ∀ x, P x → ∃ y, P y ∧ R x y := by
    rintro ⟨k, s, t⟩ ⟨hus, hst, htv, hs, ht⟩
    simp only at hus hst htv hs ht ⊢
    obtain ⟨k₁, hk₁⟩ := mem_iUnion.1 (hIG hs)
    obtain ⟨k₂, hk₂⟩ := mem_iUnion.1 (hOH ht)
    set k₀ := max (k + 1) (max k₁ k₂)
    have hsG : s ∈ G k₀ := hGm (le_max_of_le_right (le_max_left _ _)) hk₁
    have htH : t ∈ H k₀ := hHm (le_max_of_le_right (le_max_right _ _)) hk₂
    -- `u₀`: the last point of `G k₀` in `[s, t]`
    have hSG : IsClosed (G k₀ ∩ Icc s t) := (hGc k₀).inter isClosed_Icc
    have hSGne : (G k₀ ∩ Icc s t).Nonempty := ⟨s, hsG, le_rfl, hst.le⟩
    have hSGb : BddAbove (G k₀ ∩ Icc s t) := ⟨t, fun y hy => hy.2.2⟩
    set u₀ := sSup (G k₀ ∩ Icc s t)
    have hu₀ : u₀ ∈ G k₀ ∩ Icc s t := hSG.csSup_mem hSGne hSGb
    have hsu₀ : s ≤ u₀ := le_csSup hSGb ⟨hsG, le_rfl, hst.le⟩
    have hu₀t : u₀ < t := lt_of_le_of_ne hu₀.2.2 fun h =>
      Set.disjoint_left.1 (hGH k₀) (by rw [← h]; exact hu₀.1) htH
    have hnoG : ∀ y ∈ Ioc u₀ t, y ∉ G k₀ := fun y hy hyG =>
      absurd (le_csSup hSGb ⟨hyG, hsu₀.trans hy.1.le, hy.2⟩) (not_le.2 hy.1)
    -- `v₀`: the first point of `H k₀` in `[u₀, t]`
    have hSH : IsClosed (H k₀ ∩ Icc u₀ t) := (hHc k₀).inter isClosed_Icc
    have hSHne : (H k₀ ∩ Icc u₀ t).Nonempty := ⟨t, htH, hu₀t.le, le_rfl⟩
    have hSHb : BddBelow (H k₀ ∩ Icc u₀ t) := ⟨u₀, fun y hy => hy.2.1⟩
    set v₀ := sInf (H k₀ ∩ Icc u₀ t)
    have hv₀ : v₀ ∈ H k₀ ∩ Icc u₀ t := hSH.csInf_mem hSHne hSHb
    have hv₀t : v₀ ≤ t := csInf_le hSHb ⟨htH, hu₀t.le, le_rfl⟩
    have hu₀v₀ : u₀ < v₀ := lt_of_le_of_ne hv₀.2.1 fun h =>
      Set.disjoint_left.1 (hGH k₀) (by rw [← h]; exact hu₀.1) hv₀.1
    have hnoH : ∀ y ∈ Ico u₀ v₀, y ∉ H k₀ := fun y hy hyH =>
      absurd (csInf_le hSHb ⟨hyH, hy.1, (hy.2.trans_le hv₀t).le⟩) (not_le.2 hy.2)
    -- an `I`-point just right of `u₀` and an `O`-point just left of `v₀`
    set ε := (v₀ - u₀) / 2 with hεdef
    have hε : 0 < ε := by linarith
    have hsu₀' := hsu₀
    have hv₀t' := hv₀t
    obtain ⟨s', hs'1, hs'2⟩ := hG k₀ u₀ hu₀.1 ε hε
    obtain ⟨t', ht'1, ht'2⟩ := hH k₀ v₀ hv₀.1 ε hε
    have hs'I : s' ∈ I := by
      have := hall s' ⟨by linarith [hs'1.1], by linarith [hs'1.2]⟩
      rcases this with h | h
      · exact h
      · exact absurd h hs'2
    have ht'O : t' ∈ O := by
      have := hall t' ⟨by linarith [ht'1.1], by linarith [ht'1.2]⟩
      rcases this with h | h
      · exact absurd h ht'2
      · exact h
    refine ⟨(k₀, s', t'), ⟨by linarith [hs'1.1], by linarith [hs'1.2, ht'1.1],
      by linarith [ht'1.2], hs'I, ht'O⟩, ⟨lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_left _ _),
      by linarith [hs'1.1], by linarith [ht'1.2], fun w hw => ⟨?_, ?_⟩⟩⟩
    · exact hnoG w ⟨by linarith [hw.1, hs'1.1], by linarith [hw.2, ht'1.2]⟩
    · exact hnoH w ⟨by linarith [hw.1, hs'1.1], by linarith [hw.2, ht'1.2]⟩
  -- iterate
  let g : {x // P x} → {x // P x} := fun x =>
    ⟨Classical.choose (step x.1 x.2), (Classical.choose_spec (step x.1 x.2)).1⟩
  have hg : ∀ x, R x.1 (g x).1 := fun x => (Classical.choose_spec (step x.1 x.2)).2
  let x₀ : {x // P x} := ⟨(0, u, v), le_rfl, huv, le_rfl, hu, hv⟩
  let f : ℕ → ℕ × ℝ × ℝ := fun j => (g^[j] x₀).1
  have hf : ∀ j, R (f j) (f (j + 1)) := fun j => by
    simp only [f, Function.iterate_succ_apply']
    exact hg _
  have hfP : ∀ j, P (f j) := fun j => (g^[j] x₀).2
  have hsmono : Monotone fun j => (f j).2.1 := monotone_nat_of_le_succ fun j => (hf j).2.1
  have htanti : Antitone fun j => (f j).2.2 := antitone_nat_of_succ_le fun j => (hf j).2.2.1
  have hkmono : StrictMono fun j => (f j).1 := strictMono_nat_of_lt_succ fun j => (hf j).1
  have hst : ∀ i j, (f i).2.1 ≤ (f j).2.2 := fun i j =>
    (hsmono (le_max_left i j)).trans ((hfP _).2.1.le.trans (htanti (le_max_right i j)))
  have hbdd : BddAbove (range fun j => (f j).2.1) := ⟨(f 0).2.2, by
    rintro _ ⟨i, rfl⟩
    exact hst i 0⟩
  set t := ⨆ j, (f j).2.1
  have hts : ∀ j, (f j).2.1 ≤ t := fun j => le_ciSup hbdd j
  have htt : ∀ j, t ≤ (f j).2.2 := fun j => ciSup_le fun i => hst i j
  have htI : t ∈ Icc u v := ⟨hts 0, htt 0⟩
  rcases hall t htI with h | h
  · obtain ⟨k, hk⟩ := mem_iUnion.1 (hIG h)
    have hle : k ≤ (f (k + 1)).1 := (Nat.le_succ k).trans (hkmono.id_le (k + 1))
    exact ((hf k).2.2.2 t ⟨hts _, htt _⟩).1 (hGm hle hk)
  · obtain ⟨k, hk⟩ := mem_iUnion.1 (hOH h)
    have hle : k ≤ (f (k + 1)).1 := (Nat.le_succ k).trans (hkmono.id_le (k + 1))
    exact ((hf k).2.2.2 t ⟨hts _, htt _⟩).2 (hHm hle hk)

end GMTFoundations
