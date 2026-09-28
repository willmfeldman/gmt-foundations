/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.Squash
public import GMTFoundations.Reifenberg.Regraph

/-!
# The one-scale Reifenberg engine

One scale of the surface construction in the proof of Theorem 1.1 of M. Miśkiewicz, *Discrete
Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018); arXiv:1612.02461 (§4,
Proposition 4.3; hereafter Miś). Both the discrete Reifenberg theorem (Miś Proposition 4.3) and the
rectifiable-Reifenberg argument call one lemma per scale: `reifenbergStep`, whose hypotheses are
bundled in `ReifenbergStepHyp`.

Miś Proposition 4.3(c) asserts that `σ_{i+1} : T_i → T_{i+1}` is bi-Lipschitz, but only local
(per-ball) bi-Lipschitz bounds are proved there; the passage from local to global injectivity is
not written. Here it is proved at a single scale (`injOn_of_charts`), from the global displacement
bound `|σ a − a| < r/2`.

## Main statements

* `injOn_of_charts`: if `σ = id` off `⋃ B_{4r}(y)`,
  `|σ a − a| ≤ ε r` on `T` with `ε < 1/2`, and `σ` is bi-Lipschitz on each chart `T ∩ B_{5r}(y)`,
  then `σ` is injective on `T`; pairs at distance `< r` lie in one chart or are both fixed
  (`dist_lt_cases`), and all pairs satisfy `||σa − σb| − |a − b|| ≤ 2εr`.
* `reifenbergStep`: outputs (O1)–(O6). (O7), the area bounds, are the separate
  lemmas of `Reifenberg/GraphArea.lean`.

The constants: `C_sq n = 9^{n+2}` and `δ_step n = 1 / (10 C_sq n)`.
-/

public noncomputable section

namespace GMTFoundations

open Metric Set
open scoped RealInnerProductSpace NNReal

variable {n : ℕ}

/-! ### Single-scale injectivity -/

section Injectivity

variable {σ : Rn n → Rn n} {T : Set (Rn n)} {Y : Finset (Rn n)} {r ε : ℝ}

/-- Pairs of points of `T` at distance `< r` lie in a common chart ball `B_{5r}(y)`, `y ∈ Y`, or are
both fixed by `σ`. -/
theorem dist_lt_cases (hid : ∀ z, (∀ y ∈ Y, 4 * r ≤ dist z y) → σ z = z) {a b : Rn n}
    (hab : dist a b < r) :
    (∃ y ∈ Y, a ∈ ball y (5 * r) ∧ b ∈ ball y (5 * r)) ∨ (σ a = a ∧ σ b = b) := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hab
  by_cases ha : ∃ y ∈ Y, dist a y < 4 * r
  · obtain ⟨y, hy, hay⟩ := ha
    refine Or.inl ⟨y, hy, ?_, ?_⟩
    · rw [mem_ball]; linarith
    · rw [mem_ball]
      have := dist_triangle b a y
      rw [dist_comm] at hab
      linarith
  · by_cases hb : ∃ y ∈ Y, dist b y < 4 * r
    · obtain ⟨y, hy, hby⟩ := hb
      refine Or.inl ⟨y, hy, ?_, ?_⟩
      · rw [mem_ball]
        have := dist_triangle a b y
        linarith
      · rw [mem_ball]; linarith
    · simp only [not_exists, not_and, not_lt] at ha hb
      exact Or.inr ⟨hid a ha, hid b hb⟩

/-- Pairs move by at most `2εr` relative to each other. -/
theorem abs_dist_sub_dist_le (hdisp : ∀ a ∈ T, dist (σ a) a ≤ ε * r) {a b : Rn n} (ha : a ∈ T)
    (hb : b ∈ T) : |dist (σ a) (σ b) - dist a b| ≤ 2 * ε * r := by
  have h1 : dist a (σ a) ≤ ε * r := by rw [dist_comm]; exact hdisp a ha
  have h2 := hdisp b hb
  have h1' := hdisp a ha
  have h2' : dist b (σ b) ≤ ε * r := by rw [dist_comm]; exact hdisp b hb
  have t1 := dist_triangle4 a (σ a) (σ b) b
  have t2 := dist_triangle4 (σ a) a b (σ b)
  rw [abs_le]
  constructor <;> linarith

/-- **Single-scale injectivity**. -/
theorem injOn_of_charts {L : Rn n → ℝ} (hε : ε < 1 / 2) (hr : 0 < r)
    (hid : ∀ z, (∀ y ∈ Y, 4 * r ≤ dist z y) → σ z = z)
    (hdisp : ∀ a ∈ T, dist (σ a) a ≤ ε * r)
    (hchart : ∀ y ∈ Y, ∀ a ∈ T ∩ ball y (5 * r), ∀ b ∈ T ∩ ball y (5 * r),
      dist a b ≤ L y * dist (σ a) (σ b)) :
    InjOn σ T := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_ge (dist a b) r with hlt | hge
  · rcases dist_lt_cases hid hlt with ⟨y, hy, hay, hby⟩ | ⟨hfa, hfb⟩
    · have := hchart y hy a ⟨ha, hay⟩ b ⟨hb, hby⟩
      rw [hab, dist_self, mul_zero] at this
      exact hne (dist_le_zero.1 this)
    · exact hne (by rw [← hfa, ← hfb, hab])
  · have := abs_dist_sub_dist_le hdisp ha hb
    rw [hab, dist_self, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] at this
    linarith [mul_lt_mul_of_pos_right hε hr]

/-- Scale-aware bi-Lipschitz bound at one scale: with a uniform chart constant
`L ≥ 1`, pairs at distance `< r` are `L`-bi-Lipschitz. -/
theorem bilipschitz_of_charts {L : ℝ} (hL : 1 ≤ L)
    (hid : ∀ z, (∀ y ∈ Y, 4 * r ≤ dist z y) → σ z = z)
    (hchart : ∀ y ∈ Y, ∀ a ∈ T ∩ ball y (5 * r), ∀ b ∈ T ∩ ball y (5 * r),
      dist (σ a) (σ b) ≤ L * dist a b ∧ dist a b ≤ L * dist (σ a) (σ b))
    {a b : Rn n} (ha : a ∈ T) (hb : b ∈ T) (hab : dist a b < r) :
    dist (σ a) (σ b) ≤ L * dist a b ∧ dist a b ≤ L * dist (σ a) (σ b) := by
  rcases dist_lt_cases hid hab with ⟨y, hy, hay, hby⟩ | ⟨hfa, hfb⟩
  · exact hchart y hy a ⟨ha, hay⟩ b ⟨hb, hby⟩
  · rw [hfa, hfb]
    exact ⟨le_mul_of_one_le_left dist_nonneg hL, le_mul_of_one_le_left dist_nonneg hL⟩

end Injectivity

/-! ### The engine -/

/-- `δ_step n = 1 / (10 C_sq n)`: the engine threshold on `δ₁` (`≤ δ_sq n`, and `C_sq δ₁ ≤ 1/10`
for regraphing). -/
@[expose] def δ_step (n : ℕ) : ℝ := 1 / (10 * C_sq n)

theorem δ_step_pos (n : ℕ) : 0 < δ_step n := by
  rw [δ_step]; have := C_sq_pos n; positivity

theorem δ_step_le_δ_sq (n : ℕ) : δ_step n ≤ δ_sq n := by
  rw [δ_step, δ_sq]
  have := C_sq_pos n
  exact one_div_le_one_div_of_le this (by linarith)

theorem C_sq_mul_δ_step (n : ℕ) : C_sq n * δ_step n = 1 / 10 := by
  rw [δ_step]; have := C_sq_pos n; field_simp

theorem δ_step_le (n : ℕ) : δ_step n ≤ 1 / 810 := by
  rw [δ_step, C_sq_eq]
  have : (1 : ℝ) ≤ 9 ^ n := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- Hypotheses of one Reifenberg step at scale `r`.
* `Y`: the `r`-separated centres; `Vp c`: the new planes; `Vpar y`: the plane of the old chart at
  `y`; `g₀ y`: the old chart function at `y`.
* `near`: `d(y, Vpar y) ≤ r/2`; `tilt`: new planes near `y` are `δ₁(y)`-close to `Vpar y`;
  `chart`: `IsChart T (Vpar y) (g₀ y) y (5r) r (δ₀ y)`. -/
structure ReifenbergStepHyp (r : ℝ) (Y : Finset (Rn n)) (Vp : Rn n → Rn n × Rn n)
    (T : Set (Rn n)) (Vpar : Rn n → Rn n × Rn n) (g₀ : Rn n → Rn n → ℝ) (δ₀ δ₁ : Rn n → ℝ) :
    Prop where
  hr : 0 < r
  sep : (Y : Set (Rn n)).Pairwise fun a b => r ≤ dist a b
  unitVp : ∀ c ∈ Y, ‖(Vp c).2‖ = 1
  unitVpar : ∀ y ∈ Y, ‖(Vpar y).2‖ = 1
  near : ∀ y ∈ Y, |⟪y - (Vpar y).1, (Vpar y).2⟫| ≤ r / 2
  tilt : ∀ y ∈ Y, ∀ c ∈ Y, dist c y < 10 * r → planeDist c r (Vp c) (Vpar y) ≤ δ₁ y
  chart : ∀ y ∈ Y, IsChart T (Vpar y) (g₀ y) y (5 * r) r (δ₀ y)
  small0 : ∀ y ∈ Y, 0 ≤ δ₀ y ∧ δ₀ y ≤ 1 / 4
  small1 : ∀ y ∈ Y, 0 ≤ δ₁ y ∧ δ₁ y ≤ δ_step n

/-- **One Reifenberg step** (Miś Proposition 4.3 at one scale). With `σ = reifenbergMap r Y Vp`:
* (O1) `σ = id` off `⋃_{y ∈ Y} B_{4r}(y)`;
* (O2) `|σ a − a| ≤ (δ₀ y + 5δ₁ y) r` on `T ∩ B_{4r}(y)`, and `|σ a − a| ≤ r/2` on `T`;
* (O3) `σ` is `(1 + C_sq²(δ₀² + δ₁²))`-bi-Lipschitz on each chart `T ∩ B_{5r}(y)`;
* (O4) new-plane chart (δ₀-free, the input of the next scale):
  `IsChart (σ '' T) (Vp y) g₂ y (5r/2) r (6 C_sq δ₁ y)`;
* (O5) old-plane chart: `IsChart (σ '' T) (Vpar y) g₁ y (4r) r (C_sq (δ₀ y + δ₁ y))` and, with the
  same `g₁`, `IsChart (σ '' T) (Vpar y) g₁ y (5r/2) r (C_sq δ₁ y)`;
* (O6) `σ` is injective on `T`, and pairs at distance `≥ r` satisfy
  `||σa − σb| − |a − b|| ≤ (1/2 + 10 δ_step) r`. -/
theorem reifenbergStep {r : ℝ} {Y : Finset (Rn n)} {Vp : Rn n → Rn n × Rn n} {T : Set (Rn n)}
    {Vpar : Rn n → Rn n × Rn n} {g₀ : Rn n → Rn n → ℝ} {δ₀ δ₁ : Rn n → ℝ}
    (h : ReifenbergStepHyp r Y Vp T Vpar g₀ δ₀ δ₁) :
    -- (O1) support
    (∀ z, (∀ y ∈ Y, 4 * r ≤ dist z y) → reifenbergMap r Y Vp z = z) ∧
    -- (O2) displacement, per chart and global
    (∀ y ∈ Y, ∀ a ∈ T ∩ ball y (4 * r),
      dist (reifenbergMap r Y Vp a) a ≤ (δ₀ y + 5 * δ₁ y) * r) ∧
    (∀ a ∈ T, dist (reifenbergMap r Y Vp a) a ≤ r / 2) ∧
    -- (O3) chart bi-Lipschitz
    (∀ y ∈ Y, ∀ a ∈ T ∩ ball y (5 * r), ∀ b ∈ T ∩ ball y (5 * r),
      dist (reifenbergMap r Y Vp a) (reifenbergMap r Y Vp b) ≤
        (1 + C_sq n ^ 2 * (δ₀ y ^ 2 + δ₁ y ^ 2)) * dist a b ∧
      dist a b ≤ (1 + C_sq n ^ 2 * (δ₀ y ^ 2 + δ₁ y ^ 2)) *
        dist (reifenbergMap r Y Vp a) (reifenbergMap r Y Vp b)) ∧
    -- (O4) new-plane chart (δ₀-free): input to the next scale
    (∀ y ∈ Y, ∃ g₂ : Rn n → ℝ,
      IsChart (reifenbergMap r Y Vp '' T) (Vp y) g₂ y (5 / 2 * r) r (6 * C_sq n * δ₁ y)) ∧
    -- (O5) old-plane chart (global bound + δ₀-free disc bound)
    (∀ y ∈ Y, ∃ g₁ : Rn n → ℝ,
      IsChart (reifenbergMap r Y Vp '' T) (Vpar y) g₁ y (4 * r) r (C_sq n * (δ₀ y + δ₁ y)) ∧
      IsChart (reifenbergMap r Y Vp '' T) (Vpar y) g₁ y (5 / 2 * r) r (C_sq n * δ₁ y)) ∧
    -- (O6) global injectivity, scale-aware bi-Lipschitz
    InjOn (reifenbergMap r Y Vp) T ∧
    (∀ a ∈ T, ∀ b ∈ T, r ≤ dist a b →
      dist a b - (1 / 2 + 10 * δ_step n) * r ≤
        dist (reifenbergMap r Y Vp a) (reifenbergMap r Y Vp b) ∧
      dist (reifenbergMap r Y Vp a) (reifenbergMap r Y Vp b) ≤
        dist a b + (1 / 2 + 10 * δ_step n) * r) := by
  set σ := reifenbergMap r Y Vp with hσ
  have hr := h.hr
  have hCpos := C_sq_pos n
  have hC1 := one_le_C_sq n
  have hstep := δ_step_le n
  -- the squash lemma at every centre
  have hsq : ∀ y ∈ Y, ∃ g₁ : Rn n → ℝ,
      σ '' (T ∩ ball y (5 * r)) ∩ ball y (4 * r) = graphOn (Vpar y) g₁ ∩ ball y (4 * r) ∧
      (∀ u, |g₁ u| ≤ C_sq n * (δ₀ y + δ₁ y) * r) ∧
      LipschitzWith (Real.toNNReal (C_sq n * (δ₀ y + δ₁ y))) g₁ ∧
      (∀ c ∈ Y, dist c y < 10 * r → |⟪c - (Vpar y).1, (Vpar y).2⟫| ≤ r / 2 →
        (∀ u ∈ disc (Vpar y) c (5 / 2 * r), |g₁ u| ≤ C_sq n * δ₁ y * r) ∧
        LipschitzOnWith (Real.toNNReal (C_sq n * δ₁ y)) g₁ (disc (Vpar y) c (5 / 2 * r))) ∧
      (∀ a ∈ T ∩ ball y (5 * r), dist (σ a) a ≤ (δ₀ y + 5 * δ₁ y) * r) ∧
      (∀ a ∈ T ∩ ball y (5 * r), ∀ b ∈ T ∩ ball y (5 * r),
        dist (σ a) (σ b) ≤ (1 + C_sq n ^ 2 * (δ₀ y ^ 2 + δ₁ y ^ 2)) * dist a b ∧
        dist a b ≤ (1 + C_sq n ^ 2 * (δ₀ y ^ 2 + δ₁ y ^ 2)) * dist (σ a) (σ b)) ∧
      ((∀ a ∈ T, σ a ∈ ball y (4 * r) → a ∈ ball y (5 * r)) →
        σ '' T ∩ ball y (4 * r) = graphOn (Vpar y) g₁ ∩ ball y (4 * r)) := fun y hy =>
    squash hr h.sep h.unitVp (h.unitVpar y hy) (fun c hc hcy => h.tilt y hy c hc hcy)
      (h.chart y hy) (h.small0 y hy).1 (by linarith [(h.small0 y hy).2]) (h.small1 y hy).1
      ((h.small1 y hy).2.trans (δ_step_le_δ_sq n))
  -- (O1)
  have hO1 : ∀ z, (∀ y ∈ Y, 4 * r ≤ dist z y) → σ z = z := fun z hz =>
    reifenbergMap_eq_self hr hz
  -- (O2) per chart
  have hO2 : ∀ y ∈ Y, ∀ a ∈ T ∩ ball y (4 * r), dist (σ a) a ≤ (δ₀ y + 5 * δ₁ y) * r := by
    intro y hy a ha
    obtain ⟨g₁, -, -, -, -, hdisp, -⟩ := hsq y hy
    exact hdisp a ⟨ha.1, ball_subset_ball (by linarith) ha.2⟩
  -- the global displacement bound with `ε = 1/4 + 5 δ_step`
  have hε : ∀ a ∈ T, dist (σ a) a ≤ (1 / 4 + 5 * δ_step n) * r := by
    intro a ha
    by_cases hin : ∃ y ∈ Y, dist a y < 4 * r
    · obtain ⟨y, hy, hay⟩ := hin
      refine (hO2 y hy a ⟨ha, hay⟩).trans ?_
      have h0 := (h.small0 y hy).2
      have h1 := (h.small1 y hy).2
      exact mul_le_mul_of_nonneg_right (by linarith) hr.le
    · simp only [not_exists, not_and, not_lt] at hin
      rw [hO1 a hin, dist_self]
      have := δ_step_pos n
      positivity
  have hO2' : ∀ a ∈ T, dist (σ a) a ≤ r / 2 := fun a ha =>
    (hε a ha).trans (by linarith only [hr, mul_le_mul_of_nonneg_right hstep hr.le])
  -- (O5)
  have hO5 : ∀ y ∈ Y, ∃ g₁ : Rn n → ℝ,
      IsChart (σ '' T) (Vpar y) g₁ y (4 * r) r (C_sq n * (δ₀ y + δ₁ y)) ∧
      IsChart (σ '' T) (Vpar y) g₁ y (5 / 2 * r) r (C_sq n * δ₁ y) := by
    intro y hy
    obtain ⟨g₁, -, hsup, hlip, h1b, -, -, h1a'⟩ := hsq y hy
    have hset : σ '' T ∩ ball y (4 * r) = graphOn (Vpar y) g₁ ∩ ball y (4 * r) := by
      refine h1a' fun a ha hσa => ?_
      rw [mem_ball] at hσa ⊢
      have h1 : dist a (σ a) ≤ r / 2 := by rw [dist_comm]; exact hO2' a ha
      have := dist_triangle a (σ a) y
      linarith
    have hc4 : IsChart (σ '' T) (Vpar y) g₁ y (4 * r) r (C_sq n * (δ₀ y + δ₁ y)) :=
      ⟨hset, fun u _ => hsup u, hlip.lipschitzOnWith⟩
    refine ⟨g₁, hc4, ?_⟩
    have hmono := hc4.mono (h.unitVpar y hy) (c' := y) (R' := 5 / 2 * r)
      (by rw [dist_self]; linarith)
    obtain ⟨hb1, hb2⟩ := h1b y hy (by rw [dist_self]; positivity) (h.near y hy)
    exact ⟨hmono.1, hb1, hb2⟩
  refine ⟨hO1, hO2, hO2', fun y hy => ?_, fun y hy => ?_, hO5, ?_, ?_⟩
  · obtain ⟨g₁, -, -, -, -, -, hbil, -⟩ := hsq y hy
    exact hbil
  · -- (O4): regraph the δ₀-free old-plane chart at `y`
    obtain ⟨g₁, -, hc⟩ := hO5 y hy
    have hδ1 := h.small1 y hy
    have hδ : C_sq n * δ₁ y ≤ 1 / 10 := by
      rw [← C_sq_mul_δ_step n]
      exact mul_le_mul_of_nonneg_left hδ1.2 hCpos.le
    have hpd : planeDist y r (Vpar y) (Vp y) ≤ C_sq n * δ₁ y := by
      rw [planeDist_comm]
      exact (h.tilt y hy y hy (by rw [dist_self]; positivity)).trans
        (le_mul_of_one_le_left hδ1.1 hC1)
    obtain ⟨g₂, hg₂, -⟩ := graph_over_near_plane (h.unitVpar y hy) (h.unitVp y hy) hr le_rfl
      (mul_nonneg hCpos.le hδ1.1) hδ hpd (h.near y hy) hc
    refine ⟨g₂, ?_⟩
    rw [mul_assoc]
    exact hg₂
  · -- (O6) injectivity
    refine injOn_of_charts (ε := 1 / 4 + 5 * δ_step n)
      (L := fun y => 1 + C_sq n ^ 2 * (δ₀ y ^ 2 + δ₁ y ^ 2)) (by linarith) hr hO1 hε ?_
    intro y hy a ha b hb
    obtain ⟨g₁, -, -, -, -, -, hbil, -⟩ := hsq y hy
    exact (hbil a ha b hb).2
  · intro a ha b hb _
    have := abs_dist_sub_dist_le hε ha hb
    rw [abs_le] at this
    constructor <;> linarith only [this.1, this.2]

end GMTFoundations
