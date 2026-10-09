/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Reifenberg.Reductions
public import GMTFoundations.Reifenberg.Tilt
public import GMTFoundations.Reifenberg.BestPlane
public import GMTFoundations.GMT.Packing
import GMTFoundations.GMT.Polar
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Discrete Reifenberg: the upper-bound lemma and the covering construction

The covering construction in the proof of Theorem 1.1 of M. Miśkiewicz, *Discrete Reifenberg-type
theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018); arXiv:1612.02461 (§4, Claim 4.2 and the
paragraphs "Excess set" and "Construction of the covering"; hereafter Miś), and an upper-bound
lemma that is not in Miś.

## The upper-bound lemma

`levMeasure_ball_le_of_claimAt_succ`: if Claim(l+1) (`ClaimAt`, the centered form of Miś's
Claim 4.1) holds and `M ≥ ω_k ρ^{−k}`, then for every
center `x` of level `> l` and every `w ∈ B_{ρ^l}(x)`, `μ(B_{ρ^{l+1}}(w)) ≤ K M ρ^{(l+1)k}` with
`K = 3ⁿ + 1` (`ledgerK`). `levMeasure_ball_mul_le_of_claimAt_succ` is the same bound in the exact
shape of hypothesis (H2) of the tilt lemma `planeDist_sq_le_of_mass` in `Reifenberg/Tilt.lean`
(with `r = ρ^l`, sub-radius `ρ r`).

This repairs a gap in Miś. In the proof of Proposition 4.3, Miś applies Lemma 3.3 without checking
its hypothesis `μ(B_{ρ²}(y)) ≤ M ρ^{2k}` for all `y ∈ B_κ` (rescaled to the ball of the
comparison). For an atomic measure that hypothesis does not follow from Claim 4.1: a ball of that
radius may contain an atom of a coarser level, and Claim 4.1 only controls balls disjoint from the
coarse centers. Taken literally, the hypothesis creates a circular dependence between `ρ` and
`M`. Here the upper bound is supplied on balls of the grid radius
`ρ^{l+1}` with the constant `K M`, where `K` does not depend on `ρ`; the extra requirement
`M ≥ ω_k ρ^{−k}` is harmless because `M` is chosen after `ρ`.

## The covering construction (Miś §4)

`CoverData n` collects a measure `μ`, the scale ratio `ρ`, the threshold `θ` (good iff
`μ(B_{ρ^i}(y)) ≥ θ ρ^{ik}`), a center set `P ⊆ B_{ρ^j}(p)` with levels `lev : Rn n → ℕ∞`
(`⊤` = no atom, as in the rectifiable-Reifenberg argument), the plane choice `V i y` (in the
discrete case `bestPlane μ y (κ ρ^i)`), the top center
`p` and the top scale `j`. The construction is a recursion on the absolute scale `i ∈ ℕ`, producing
`Finset` families with explicit centers:

* `good i`, `bad i`, `fin i : Finset (Rn n)` (Miś's `Good_i`, `Bad_i`, `Fin_i`);
* `rem i : Set (Rn n)`, Miś's `R_{≤i}` (`rem_eq`: the bad/final balls of scales `(j, i]` and the
  excess sets of scales `[j, i]`);
* `excess i y = B_{ρ^i}(y) ∩ {x : d(x, V i y) ≥ ρ^{i+1}/4}` (Miś's `E(y, r_i)`).

At scale `j`: `good j = {p}`, `bad j = fin j = ∅`, `rem j = excess j p`. From scale `i ≥ j` to
`i+1`, with `A_i = P ∩ (⋃_{z ∈ good i} B_{ρ^i}(z) \ rem i)`: `fin (i+1)` is the set of centers of
level `i+1` in `A_i`; `good (i+1) ∪ bad (i+1)` is a maximal `ρ^{i+1}`-separated subset
(`NaberValtorta.net`) of the centers of level `> i+1` in `A_i`, split by the threshold.

## Claim 4.2

Below, (a), (b), (c) label the three assertions of Miś Claim 4.2, in Miś's order.

* `subset_cover`: `P ⊆ ⋃_{y ∈ good N} B_{ρ^N}(y) ∪ rem N` for `N ≥ j` (covering).
* `pairwiseDisjoint_halfBalls`: the half-balls `B_{ρ^l/2}(y)` of the leaves
  (`bad l`, `fin l` for `j < l ≤ N`, and `good N`) are pairwise disjoint.
* `not_mem_ball_good_of_lev_le`: good balls at scale `i` contain no center of level `≤ i`.
* `good_eq_empty`: termination.
* `exists_parent`: every center at scale `i + 1` has a good parent `z` at scale `i` and lies within
  `ρ^{i+1}/4` of the plane `V i z` (the `near` hypothesis of `reifenbergStep`).

`CoverData.ofFamily` is the instance used for the discrete Reifenberg theorem (`Discrete.lean`),
and `CoverData.ofFamily_hyp` verifies its hypotheses.
-/

@[expose] public noncomputable section

namespace GMTFoundations.DiscreteReifenberg

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

variable {n : ℕ}

/-! ### The upper-bound lemma -/

section LemmaU

variable {ρ M : ℝ} {Z : Finset (Rn n)} {lev : Rn n → ℕ}

/-- **The upper-bound lemma** (not in Miś). Let the balls `B_{ρ^{lev z}}(z)` be disjoint, `ρ ≤ 1/2`,
`M ρ^k ≥ ω_k`, and assume Claim(l+1). For a center `x` of level `> l` and `w ∈ B_{ρ^l}(x)`:
`μ(B_{ρ^{l+1}}(w)) ≤ (3ⁿ + 1) M (ρ^{l+1})^k`. At most one atom of level `≤ l+1` lies in the ball,
and its level is `≥ l`; the finer atoms are covered by `≤ 3ⁿ` balls of Claim(l+1). -/
theorem levMeasure_ball_le_of_claimAt_succ (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 2)
    (hdisj : (Z : Set (Rn n)).Pairwise fun a b =>
      Disjoint (ball a (ρ ^ lev a)) (ball b (ρ ^ lev b)))
    (hM : unitBallVolume (n - 1) ≤ M * ρ ^ (n - 1)) {l : ℕ} (hclaim : ClaimAt ρ M Z lev (l + 1))
    {x : Rn n} (hx : x ∈ Z) (hlx : l < lev x) {w : Rn n} (hw : w ∈ ball x (ρ ^ l)) :
    levMeasure ρ Z lev (ball w (ρ ^ (l + 1))) ≤
      ENNReal.ofReal (ledgerK n * M * (ρ ^ (l + 1)) ^ (n - 1)) := by
  classical
  have hρ1 : ρ ≤ 1 := hρ.trans (by norm_num)
  have hω := unitBallVolume_pos (n - 1)
  have hρk := pow_pos hρ0 (n - 1)
  have hM0 : 0 < M := by
    have := hω.trans_le hM
    nlinarith
  have hr : 0 < ρ ^ (l + 1) := pow_pos hρ0 _
  have hMr : 0 ≤ M * (ρ ^ (l + 1)) ^ (n - 1) := by positivity
  -- the coarse atoms
  have hcoarse : levMeasure ρ Z lev (ball w (ρ ^ (l + 1)) ∩ {z | lev z ≤ l + 1}) ≤
      ENNReal.ofReal (M * (ρ ^ (l + 1)) ^ (n - 1)) := by
    rw [levMeasure_apply]
    suffices H : ∀ F : Finset (Rn n),
        (∀ z ∈ F, z ∈ Z ∧ z ∈ ball w (ρ ^ (l + 1)) ∩ {z | lev z ≤ l + 1}) →
        ∑ z ∈ F, ENNReal.ofReal (unitBallVolume (n - 1) * (ρ ^ lev z) ^ (n - 1)) ≤
          ENNReal.ofReal (M * (ρ ^ (l + 1)) ^ (n - 1)) from
      H _ fun z hz => Finset.mem_filter.1 hz
    intro F hF
    have hsep : (F : Set (Rn n)).Pairwise fun a b => 2 * ρ ^ (l + 1) ≤ dist a b := by
      intro a ha b hb hab
      have hd := add_le_dist_of_disjoint hρ0 hdisj (hF a ha).1 (hF b hb).1 hab
      have h1 : ρ ^ (l + 1) ≤ ρ ^ lev a := pow_le_pow_of_le_one hρ0.le hρ1 (hF a ha).2.2
      have h2 : ρ ^ (l + 1) ≤ ρ ^ lev b := pow_le_pow_of_le_one hρ0.le hρ1 (hF b hb).2.2
      linarith
    have hcard : F.card ≤ 1 := NaberValtorta.card_le_one_of_pairwise_le_dist le_rfl
      (fun z hz => (hF z hz).2.1) hsep
    have hmass : ∀ z ∈ F, ENNReal.ofReal (unitBallVolume (n - 1) * (ρ ^ lev z) ^ (n - 1)) ≤
        ENNReal.ofReal (M * (ρ ^ (l + 1)) ^ (n - 1)) := by
      intro z hz
      have hlz : l ≤ lev z := by
        by_contra hlt
        rw [not_le] at hlt
        have hzx : z ≠ x := by rintro rfl; omega
        have hd := add_le_dist_of_disjoint hρ0 hdisj (hF z hz).1 hx hzx
        obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
        have hl1 : ρ ^ m ≤ ρ ^ lev z := pow_le_pow_of_le_one hρ0.le hρ1 (by omega)
        have hdzx : dist z x < ρ ^ (m + 1 + 1) + ρ ^ (m + 1) :=
          (dist_triangle z w x).trans_lt
            (add_lt_add (mem_ball.1 (hF z hz).2.1) (mem_ball.1 hw))
        have hkey : ρ ^ (m + 1 + 1) + ρ ^ (m + 1) ≤ ρ ^ m := by
          have hp := pow_pos hρ0 m
          have h3 : ρ * ρ + ρ ≤ 1 := by nlinarith
          have h4 := mul_le_mul_of_nonneg_left h3 hp.le
          rw [pow_succ, pow_succ]
          linarith
        have := pow_pos hρ0 (lev x)
        linarith
      refine ENNReal.ofReal_le_ofReal ?_
      calc unitBallVolume (n - 1) * (ρ ^ lev z) ^ (n - 1)
          ≤ unitBallVolume (n - 1) * (ρ ^ l) ^ (n - 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
              (pow_le_pow_of_le_one hρ0.le hρ1 hlz) _) hω.le
        _ ≤ (M * ρ ^ (n - 1)) * (ρ ^ l) ^ (n - 1) :=
            mul_le_mul_of_nonneg_right hM (by positivity)
        _ = M * (ρ ^ (l + 1)) ^ (n - 1) := by rw [pow_succ, mul_pow]; ring
    calc ∑ z ∈ F, ENNReal.ofReal (unitBallVolume (n - 1) * (ρ ^ lev z) ^ (n - 1))
        ≤ F.card • ENNReal.ofReal (M * (ρ ^ (l + 1)) ^ (n - 1)) :=
          Finset.sum_le_card_nsmul _ _ _ hmass
      _ ≤ ENNReal.ofReal (M * (ρ ^ (l + 1)) ^ (n - 1)) := by
          rw [nsmul_eq_mul]
          exact mul_le_of_le_one_left bot_le (by exact_mod_cast hcard)
  -- the finer atoms
  have hfine := levMeasure_inter_le_of_claimAt hρ0 hclaim (A := ball w (ρ ^ (l + 1))) (c := w)
    hr.le ball_subset_closedBall
  rw [mul_div_assoc, div_self hr.ne'] at hfine
  have hsplit : ball w (ρ ^ (l + 1)) ⊆ (ball w (ρ ^ (l + 1)) ∩ {z | lev z ≤ l + 1}) ∪
      (ball w (ρ ^ (l + 1)) ∩ {z | l + 1 < lev z}) := fun z hz => by
    rcases le_or_gt (lev z) (l + 1) with h | h
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  calc levMeasure ρ Z lev (ball w (ρ ^ (l + 1)))
      ≤ levMeasure ρ Z lev (ball w (ρ ^ (l + 1)) ∩ {z | lev z ≤ l + 1}) +
          levMeasure ρ Z lev (ball w (ρ ^ (l + 1)) ∩ {z | l + 1 < lev z}) :=
        (measure_mono hsplit).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (M * (ρ ^ (l + 1)) ^ (n - 1)) +
          ENNReal.ofReal ((2 * 1 + 1) ^ n * (M * (ρ ^ (l + 1)) ^ (n - 1))) :=
        add_le_add hcoarse hfine
    _ = ENNReal.ofReal (ledgerK n * M * (ρ ^ (l + 1)) ^ (n - 1)) := by
        rw [← ENNReal.ofReal_add hMr (by positivity)]
        congr 1
        unfold ledgerK
        ring

/-- The upper-bound lemma in the shape of hypothesis (H2) of the tilt lemma
`planeDist_sq_le_of_mass` at `(x, r) = (x, ρ^l)` with `b = K M`:
`∀ y ∈ B_r(x), μ(B_{ρr}(y)) ≤ b (ρr)^k`. This is the only form in which the inductive hypothesis
enters the inductive step. -/
theorem levMeasure_ball_mul_le_of_claimAt_succ (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 2)
    (hdisj : (Z : Set (Rn n)).Pairwise fun a b =>
      Disjoint (ball a (ρ ^ lev a)) (ball b (ρ ^ lev b)))
    (hM : unitBallVolume (n - 1) ≤ M * ρ ^ (n - 1)) {l : ℕ} (hclaim : ClaimAt ρ M Z lev (l + 1))
    {x : Rn n} (hx : x ∈ Z) (hlx : l < lev x) :
    ∀ y ∈ ball x (ρ ^ l), levMeasure ρ Z lev (ball y (ρ * ρ ^ l)) ≤
      ENNReal.ofReal (ledgerK n * M * (ρ * ρ ^ l) ^ (n - 1)) := by
  intro y hy
  rw [← pow_succ']
  exact levMeasure_ball_le_of_claimAt_succ hρ0 hρ hdisj hM hclaim hx hlx hy

end LemmaU

/-! ### The covering construction -/

/-- The data of one run of the covering construction (Miś §4) at the top ball
`B_{ρ^j}(p)`; see the module docstring. -/
structure CoverData (n : ℕ) where
  /-- The measure (discrete case: `levMeasure ρ Z lev`). -/
  μ : Measure (Rn n)
  /-- The scale ratio; scale `i` has radius `ρ^i`. -/
  ρ : ℝ
  /-- The good/bad threshold (discrete case: `θ = τM`). -/
  θ : ℝ
  /-- The centers to be covered, inside `B_{ρ^j}(p)`. -/
  P : Set (Rn n)
  /-- The levels of the centers (`⊤`: not an atom). -/
  lev : Rn n → ℕ∞
  /-- The plane `(point, unit normal)` attached to a good center at scale `i`. -/
  V : ℕ → Rn n → Rn n × Rn n
  /-- The top center. -/
  p : Rn n
  /-- The top scale. -/
  j : ℕ

/-- The state of the construction at one scale. -/
structure CoverState (n : ℕ) where
  /-- Good centers (`μ(B) ≥ θ r^k`). -/
  good : Finset (Rn n)
  /-- Bad centers (`μ(B) < θ r^k`). -/
  bad : Finset (Rn n)
  /-- Final centers (atoms of exactly this level). -/
  fin : Finset (Rn n)
  /-- The removed region `R_{≤i}`. -/
  rem : Set (Rn n)

namespace CoverData

variable (D : CoverData n)

/-- The hypotheses under which the construction satisfies Claim 4.2. -/
structure Hyp : Prop where
  ρ_pos : 0 < D.ρ
  ρ_le_one : D.ρ ≤ 1
  P_subset : D.P ⊆ ball D.p (D.ρ ^ D.j)
  lev_gt : ∀ x ∈ D.P, (D.j : ℕ∞) < D.lev x
  /-- An atom of level `a` is at distance `≥ ρ^a` from every other center (discrete case:
  disjoint balls; vacuous when `lev ≡ ⊤`). -/
  sep : ∀ x ∈ D.P, ∀ y ∈ D.P, x ≠ y → ∀ a : ℕ, D.lev x = a → D.ρ ^ a ≤ dist x y

/-- Miś's excess set `E(y, r_i) = B_{ρ^i}(y) ∩ {x : d(x, V i y) ≥ ρ^{i+1}/4}`. -/
def excess (i : ℕ) (y : Rn n) : Set (Rn n) :=
  ball y (D.ρ ^ i) ∩ {x | D.ρ ^ (i + 1) / 4 ≤ |⟪x - (D.V i y).1, (D.V i y).2⟫|}

/-- The excess set of scale `i`, `E_i = ⋃_{y ∈ G} E(y, r_i)` (with `G = good i`). -/
def excessUnion (i : ℕ) (G : Finset (Rn n)) : Set (Rn n) := ⋃ y ∈ G, D.excess i y

/-- The state at the top scale `j`. -/
def init : CoverState n := ⟨{D.p}, ∅, ∅, D.excess D.j D.p⟩

/-- The region available at scale `i + 1`: `P ∩ (⋃_{z ∈ good i} B_{ρ^i}(z) \ R_{≤i})`. -/
def avail (i : ℕ) (s : CoverState n) : Set (Rn n) :=
  D.P ∩ ((⋃ z ∈ s.good, ball z (D.ρ ^ i)) \ s.rem)

/-- The candidates for final balls at scale `i + 1`: atoms of level exactly `i + 1`. -/
def finCand (i : ℕ) (s : CoverState n) : Set (Rn n) :=
  D.avail i s ∩ {x | D.lev x = ((i + 1 : ℕ) : ℕ∞)}

/-- The candidates for good/bad centers at scale `i + 1`: centers of level `> i + 1`. -/
def sepCand (i : ℕ) (s : CoverState n) : Set (Rn n) :=
  D.avail i s ∩ {x | ((i + 1 : ℕ) : ℕ∞) < D.lev x}

open scoped Classical in
/-- One step of the construction, from scale `i` to scale `i + 1` (Miś §4). -/
def step (i : ℕ) (s : CoverState n) : CoverState n :=
  let Y := NaberValtorta.net (D.sepCand i s) (D.ρ ^ (i + 1))
  let G := Y.filter fun y =>
    ENNReal.ofReal (D.θ * (D.ρ ^ (i + 1)) ^ (n - 1)) ≤ D.μ (ball y (D.ρ ^ (i + 1)))
  let B := Y.filter fun y =>
    ¬ ENNReal.ofReal (D.θ * (D.ρ ^ (i + 1)) ^ (n - 1)) ≤ D.μ (ball y (D.ρ ^ (i + 1)))
  let F := NaberValtorta.net (D.finCand i s) (D.ρ ^ (i + 1))
  ⟨G, B, F, s.rem ∪ (⋃ y ∈ B ∪ F, ball y (D.ρ ^ (i + 1))) ∪ D.excessUnion (i + 1) G⟩

/-- The state at every absolute scale `i` (equal to `init` for `i ≤ j`). -/
def state : ℕ → CoverState n
  | 0 => D.init
  | i + 1 => if i + 1 ≤ D.j then D.init else D.step i (state i)

/-- `Good_i`. -/
def good (i : ℕ) : Finset (Rn n) := (D.state i).good
/-- `Bad_i`. -/
def bad (i : ℕ) : Finset (Rn n) := (D.state i).bad
/-- `Fin_i`. -/
def fin (i : ℕ) : Finset (Rn n) := (D.state i).fin
/-- `R_{≤i}`. -/
def rem (i : ℕ) : Set (Rn n) := (D.state i).rem

/-- The leaves up to scale `N`: `(l, y)` with `y ∈ bad l ∪ fin l`, `j < l ≤ N`, and `(N, y)` with
`y ∈ good N`. -/
def leaves (N : ℕ) : Finset (ℕ × Rn n) :=
  ((Finset.Ioc D.j N).biUnion fun l => (D.bad l ∪ D.fin l).image fun y => (l, y)) ∪
    (D.good N).image fun y => (N, y)

/-! #### Unfolding the recursion -/

theorem state_of_le {i : ℕ} (h : i ≤ D.j) : D.state i = D.init := by
  cases i with
  | zero => rfl
  | succ i => simp only [state, ite_eq_left h]

theorem state_succ {i : ℕ} (h : D.j ≤ i) : D.state (i + 1) = D.step i (D.state i) := by
  simp only [state, ite_eq_right (show ¬ i + 1 ≤ D.j by omega)]

theorem good_top : D.good D.j = {D.p} := by simp [good, state_of_le D le_rfl, init]
theorem fin_top : D.fin D.j = ∅ := by simp [fin, state_of_le D le_rfl, init]
theorem rem_top : D.rem D.j = D.excess D.j D.p := by simp [rem, state_of_le D le_rfl, init]

open scoped Classical in
theorem good_succ {i : ℕ} (h : D.j ≤ i) : D.good (i + 1) =
    (NaberValtorta.net (D.sepCand i (D.state i)) (D.ρ ^ (i + 1))).filter fun y =>
      ENNReal.ofReal (D.θ * (D.ρ ^ (i + 1)) ^ (n - 1)) ≤ D.μ (ball y (D.ρ ^ (i + 1))) := by
  rw [good, state_succ D h]; rfl

open scoped Classical in
theorem bad_succ {i : ℕ} (h : D.j ≤ i) : D.bad (i + 1) =
    (NaberValtorta.net (D.sepCand i (D.state i)) (D.ρ ^ (i + 1))).filter fun y =>
      ¬ ENNReal.ofReal (D.θ * (D.ρ ^ (i + 1)) ^ (n - 1)) ≤ D.μ (ball y (D.ρ ^ (i + 1))) := by
  rw [bad, state_succ D h]; rfl

theorem fin_succ {i : ℕ} (h : D.j ≤ i) :
    D.fin (i + 1) = NaberValtorta.net (D.finCand i (D.state i)) (D.ρ ^ (i + 1)) := by
  rw [fin, state_succ D h]; rfl

theorem rem_succ {i : ℕ} (h : D.j ≤ i) : D.rem (i + 1) =
    D.rem i ∪ (⋃ y ∈ D.bad (i + 1) ∪ D.fin (i + 1), ball y (D.ρ ^ (i + 1))) ∪
      D.excessUnion (i + 1) (D.good (i + 1)) := by
  rw [rem, bad, fin, good, state_succ D h]; rfl

theorem avail_eq (i : ℕ) : D.avail i (D.state i) =
    D.P ∩ ((⋃ z ∈ D.good i, ball z (D.ρ ^ i)) \ D.rem i) := rfl

/-! #### Claim 4.2 and the structure of the families -/

section Claim42

variable {D}

theorem mem_avail_iff {i : ℕ} {x : Rn n} : x ∈ D.avail i (D.state i) ↔
    x ∈ D.P ∧ (∃ z ∈ D.good i, x ∈ ball z (D.ρ ^ i)) ∧ x ∉ D.rem i := by
  simp only [avail_eq, mem_inter_iff, Set.mem_sdiff, mem_iUnion, exists_prop]

theorem avail_subset_P (i : ℕ) (s : CoverState n) : D.avail i s ⊆ D.P := fun _ hx => hx.1

theorem sepCand_subset_avail (i : ℕ) (s : CoverState n) : D.sepCand i s ⊆ D.avail i s :=
  fun _ hx => hx.1

theorem finCand_subset_avail (i : ℕ) (s : CoverState n) : D.finCand i s ⊆ D.avail i s :=
  fun _ hx => hx.1

theorem good_succ_union_bad_succ {i : ℕ} (h : D.j ≤ i) :
    D.good (i + 1) ∪ D.bad (i + 1) =
      NaberValtorta.net (D.sepCand i (D.state i)) (D.ρ ^ (i + 1)) := by
  classical
  rw [good_succ D h, bad_succ D h]
  convert Finset.filter_union_filter_not_eq _ _

/-- Good balls at scale `i + 1` have mass `≥ θ ρ^{(i+1)k}`. -/
theorem le_measure_of_mem_good_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    ENNReal.ofReal (D.θ * (D.ρ ^ (i + 1)) ^ (n - 1)) ≤ D.μ (ball y (D.ρ ^ (i + 1))) := by
  classical
  rw [good_succ D h] at hy
  exact (Finset.mem_filter.1 hy).2

/-- Bad balls at scale `i + 1` have mass `< θ ρ^{(i+1)k}`. -/
theorem measure_lt_of_mem_bad_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n} (hy : y ∈ D.bad (i + 1)) :
    D.μ (ball y (D.ρ ^ (i + 1))) < ENNReal.ofReal (D.θ * (D.ρ ^ (i + 1)) ^ (n - 1)) := by
  classical
  rw [bad_succ D h] at hy
  exact not_le.1 (Finset.mem_filter.1 hy).2

theorem rem_mono {i l : ℕ} (hi : D.j ≤ i) (hil : i ≤ l) : D.rem i ⊆ D.rem l := by
  induction l, hil using Nat.le_induction with
  | base => exact subset_rfl
  | succ l hil ih =>
    rw [rem_succ D (hi.trans hil)]
    exact ih.trans (subset_union_left.trans subset_union_left)

theorem ball_subset_rem {l : ℕ} (hl : D.j < l) {y : Rn n} (hy : y ∈ D.bad l ∪ D.fin l) :
    ball y (D.ρ ^ l) ⊆ D.rem l := by
  obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 := ⟨l - 1, by omega⟩
  rw [rem_succ D (by omega)]
  exact (subset_biUnion_of_mem (u := fun y => ball y (D.ρ ^ (i + 1))) (Finset.mem_coe.2 hy)).trans
    (subset_union_right.trans subset_union_left)

theorem mem_leaves {N : ℕ} {q : ℕ × Rn n} : q ∈ D.leaves N ↔
    (D.j < q.1 ∧ q.1 ≤ N ∧ q.2 ∈ D.bad q.1 ∪ D.fin q.1) ∨ (q.1 = N ∧ q.2 ∈ D.good N) := by
  obtain ⟨l, y⟩ := q
  simp only [leaves, Finset.mem_union, Finset.mem_biUnion, Finset.mem_Ioc, Finset.mem_image,
    Prod.mk.injEq]
  constructor
  · rintro (⟨l', hl', y', hy', rfl, rfl⟩ | ⟨y', hy', rfl, rfl⟩)
    · exact Or.inl ⟨hl'.1, hl'.2, hy'⟩
    · exact Or.inr ⟨rfl, hy'⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨rfl, h⟩)
    · exact Or.inl ⟨l, ⟨h1, h2⟩, y, h3, rfl, rfl⟩
    · exact Or.inr ⟨y, h, rfl, rfl⟩

theorem mem_sepCand_of_mem_good_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    y ∈ D.sepCand i (D.state i) := by
  have : y ∈ D.good (i + 1) ∪ D.bad (i + 1) := Finset.mem_union_left _ hy
  rw [good_succ_union_bad_succ h] at this
  exact NaberValtorta.net_subset _ _ this

theorem mem_sepCand_of_mem_bad_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n} (hy : y ∈ D.bad (i + 1)) :
    y ∈ D.sepCand i (D.state i) := by
  have : y ∈ D.good (i + 1) ∪ D.bad (i + 1) := Finset.mem_union_right _ hy
  rw [good_succ_union_bad_succ h] at this
  exact NaberValtorta.net_subset _ _ this

theorem lev_of_mem_good_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n} (hy : y ∈ D.good (i + 1)) :
    ((i + 1 : ℕ) : ℕ∞) < D.lev y := (mem_sepCand_of_mem_good_succ h hy).2

/-- `R_{≤N}` explicitly: the bad and final balls of the scales `(j, N]` and the excess sets of the
scales `[j, N]`. -/
theorem rem_eq {N : ℕ} (hN : D.j ≤ N) : D.rem N =
    (⋃ l ∈ Finset.Ioc D.j N, ⋃ y ∈ D.bad l ∪ D.fin l, ball y (D.ρ ^ l)) ∪
      ⋃ l ∈ Finset.Icc D.j N, D.excessUnion l (D.good l) := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [rem_top, Finset.Ioc_self, Finset.Icc_self, Finset.set_biUnion_singleton, good_top]
    simp [excessUnion]
  | succ N hN ih =>
    rw [rem_succ D hN, ih, ← Finset.insert_Ioc_right_eq_Ioc_add_one hN,
      ← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.set_biUnion_insert,
      Finset.set_biUnion_insert]
    ext x
    simp only [mem_union]
    tauto

/-- The excess set of scale `i` is removed: `E_i ⊆ R_{≤i}`. -/
theorem excessUnion_subset_rem {i : ℕ} (hi : D.j ≤ i) : D.excessUnion i (D.good i) ⊆ D.rem i := by
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [rem_top, good_top]
    simp [excessUnion]
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [rem_succ D (by omega)]
    exact subset_union_right

/-- **Parent and near-plane property** (Miś §4, proof of Proposition 4.3; the `near` hypothesis of
`reifenbergStep`): a center `y` at scale
`i + 1` lies in `B_{ρ^i}(z)` for a good `z` at scale `i` with `|⟪y − V_1, V_2⟫| < ρ^{i+1}/4`,
`V = V i z` (because `y ∉ E(z, ρ^i) ⊆ R_{≤i}`). -/
theorem exists_parent {i : ℕ} (hi : D.j ≤ i) {y : Rn n}
    (hy : y ∈ D.avail i (D.state i)) : ∃ z ∈ D.good i, y ∈ ball z (D.ρ ^ i) ∧
      |⟪y - (D.V i z).1, (D.V i z).2⟫| < D.ρ ^ (i + 1) / 4 := by
  obtain ⟨-, ⟨z, hz, hyz⟩, hrem⟩ := mem_avail_iff.1 hy
  refine ⟨z, hz, hyz, not_le.1 fun hle => hrem (excessUnion_subset_rem hi ?_)⟩
  exact mem_biUnion (x := z) (Finset.mem_coe.2 hz) ⟨hyz, hle⟩

variable (hD : D.Hyp)
include hD

theorem sepCand_subset_closedBall (i : ℕ) (s : CoverState n) :
    D.sepCand i s ⊆ closedBall D.p (D.ρ ^ D.j) := fun _ hx =>
  ball_subset_closedBall (hD.P_subset (avail_subset_P i s (sepCand_subset_avail i s hx)))

theorem finCand_subset_closedBall (i : ℕ) (s : CoverState n) :
    D.finCand i s ⊆ closedBall D.p (D.ρ ^ D.j) := fun _ hx =>
  ball_subset_closedBall (hD.P_subset (avail_subset_P i s (finCand_subset_avail i s hx)))

/-- `Fin_{i+1}` is exactly the set of atoms of level `i + 1` in the available region. -/
theorem coe_fin_succ {i : ℕ} (h : D.j ≤ i) :
    (D.fin (i + 1) : Set (Rn n)) = D.finCand i (D.state i) := by
  rw [fin_succ D h]
  have hr : 0 < D.ρ ^ (i + 1) := pow_pos hD.ρ_pos _
  obtain ⟨hsub, -, hcov⟩ := NaberValtorta.net_spec (finCand_subset_closedBall hD i (D.state i)) hr
  refine Subset.antisymm hsub fun x hx => ?_
  obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 (hcov hx)
  by_cases hxq' : x = q
  · exact hxq' ▸ hq
  · have hqc := hsub hq
    have hd := hD.sep x (avail_subset_P _ _ (finCand_subset_avail _ _ hx)) q
      (avail_subset_P _ _ (finCand_subset_avail _ _ hqc)) hxq' (i + 1) hx.2
    exact absurd (mem_ball.1 hxq) (not_lt.2 hd)

theorem mem_finCand_of_mem_fin_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n} (hy : y ∈ D.fin (i + 1)) :
    y ∈ D.finCand i (D.state i) := by
  rw [← coe_fin_succ hD h]; exact hy

/-- Every center at scale `i + 1` lies in the available region `A_i`. -/
theorem mem_avail_of_mem_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n}
    (hy : y ∈ D.good (i + 1) ∪ D.bad (i + 1) ∪ D.fin (i + 1)) : y ∈ D.avail i (D.state i) := by
  rcases Finset.mem_union.1 hy with hy | hy
  · rcases Finset.mem_union.1 hy with hy | hy
    · exact sepCand_subset_avail _ _ (mem_sepCand_of_mem_good_succ h hy)
    · exact sepCand_subset_avail _ _ (mem_sepCand_of_mem_bad_succ h hy)
  · exact finCand_subset_avail _ _ (mem_finCand_of_mem_fin_succ hD h hy)

theorem mem_P_of_mem_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n}
    (hy : y ∈ D.good (i + 1) ∪ D.bad (i + 1) ∪ D.fin (i + 1)) : y ∈ D.P :=
  avail_subset_P _ _ (mem_avail_of_mem_succ hD h hy)

theorem lev_of_mem_fin_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n} (hy : y ∈ D.fin (i + 1)) :
    D.lev y = ((i + 1 : ℕ) : ℕ∞) := (mem_finCand_of_mem_fin_succ hD h hy).2

/-- The centers at one scale `i + 1` are `ρ^{i+1}`-separated. -/
theorem pow_le_dist_of_mem_succ {i : ℕ} (h : D.j ≤ i) {y y' : Rn n}
    (hy : y ∈ D.good (i + 1) ∪ D.bad (i + 1) ∪ D.fin (i + 1))
    (hy' : y' ∈ D.good (i + 1) ∪ D.bad (i + 1) ∪ D.fin (i + 1)) (hne : y ≠ y') :
    D.ρ ^ (i + 1) ≤ dist y y' := by
  have hP := mem_P_of_mem_succ hD h hy
  have hP' := mem_P_of_mem_succ hD h hy'
  rcases Finset.mem_union.1 hy with hy1 | hyF
  · rcases Finset.mem_union.1 hy' with hy1' | hyF'
    · rw [good_succ_union_bad_succ h] at hy1 hy1'
      exact NaberValtorta.net_pairwise _ _ hy1 hy1' hne
    · rw [dist_comm]
      exact hD.sep y' hP' y hP hne.symm (i + 1) (lev_of_mem_fin_succ hD h hyF')
  · exact hD.sep y hP y' hP' hne (i + 1) (lev_of_mem_fin_succ hD h hyF)

/-- Centers at a later scale avoid the balls of earlier bad and final centers. -/
theorem pow_le_dist_of_mem_bad_fin {l N : ℕ} (hl : D.j < l) (hlN : l < N) {y y' : Rn n}
    (hy : y ∈ D.bad l ∪ D.fin l) (hy' : y' ∈ D.good N ∪ D.bad N ∪ D.fin N) :
    D.ρ ^ l ≤ dist y y' := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have hav := mem_avail_iff.1 (mem_avail_of_mem_succ hD (by omega) hy')
  have hnot : y' ∉ ball y (D.ρ ^ l) := fun hb =>
    hav.2.2 (rem_mono hl.le (by omega) (ball_subset_rem hl hy hb))
  rw [mem_ball, not_lt, dist_comm] at hnot
  exact hnot

/-- **Claim 4.2 (c)**: a good ball at scale `i` contains no center of level `≤ i`. -/
theorem not_mem_ball_good_of_lev_le {i : ℕ} (hi : D.j ≤ i) {y x : Rn n} (hy : y ∈ D.good i)
    (hx : x ∈ D.P) (hlev : D.lev x ≤ i) : x ∉ ball y (D.ρ ^ i) := by
  rcases eq_or_lt_of_le hi with rfl | hlt
  · exact absurd hlev (not_le.2 (hD.lev_gt x hx))
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hyP := mem_P_of_mem_succ hD (by omega) (Finset.mem_union_left _ (Finset.mem_union_left _ hy))
  have hly := lev_of_mem_good_succ (by omega) hy
  have hne : x ≠ y := by rintro rfl; exact absurd hlev (not_le.2 hly)
  obtain ⟨a, ha, hai⟩ := ENat.le_natCast_iff.1 hlev
  have hd := hD.sep x hx y hyP hne a ha
  have : D.ρ ^ (i' + 1) ≤ D.ρ ^ a := pow_le_pow_of_le_one hD.ρ_pos.le hD.ρ_le_one hai
  rw [mem_ball, not_lt]
  linarith

theorem lt_lev_of_mem_avail {i : ℕ} (hi : D.j ≤ i) {x : Rn n} (hx : x ∈ D.avail i (D.state i)) :
    (i : ℕ∞) < D.lev x := by
  obtain ⟨hxP, ⟨z, hz, hxz⟩, -⟩ := mem_avail_iff.1 hx
  by_contra hle
  exact not_mem_ball_good_of_lev_le hD hi hz hxP (not_lt.1 hle) hxz

/-- **Claim 4.2 (a)** (covering): `P ⊆ ⋃_{y ∈ good N} B_{ρ^N}(y) ∪ R_{≤N}` for every `N ≥ j`. -/
theorem subset_cover {N : ℕ} (hN : D.j ≤ N) :
    D.P ⊆ (⋃ y ∈ D.good N, ball y (D.ρ ^ N)) ∪ D.rem N := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [good_top]
    intro x hx
    exact Or.inl (by simpa using hD.P_subset hx)
  | succ N hN ih =>
    intro x hx
    rcases ih hx with hx' | hx'
    · by_cases hrem : x ∈ D.rem N
      · exact Or.inr (by rw [rem_succ D hN]; exact Or.inl (Or.inl hrem))
      have hav : x ∈ D.avail N (D.state N) := by
        refine mem_avail_iff.2 ⟨hx, ?_, hrem⟩
        simpa only [mem_iUnion, exists_prop] using hx'
      have hlt := lt_lev_of_mem_avail hD hN hav
      have hle : ((N + 1 : ℕ) : ℕ∞) ≤ D.lev x := by
        rw [Nat.cast_add, Nat.cast_one]
        exact (ENat.add_one_le_iff (ENat.natCast_ne_top N)).2 hlt
      rcases eq_or_lt_of_le hle with heq | hlt'
      · -- a final center
        have hxF : x ∈ D.fin (i := N + 1) := by
          rw [← Finset.mem_coe, coe_fin_succ hD hN]
          exact ⟨hav, heq.symm⟩
        refine Or.inr ?_
        rw [rem_succ D hN]
        refine Or.inl (Or.inr ?_)
        exact mem_biUnion (x := x) (Finset.mem_coe.2 (Finset.mem_union_right _ hxF))
          (mem_ball_self (pow_pos hD.ρ_pos _))
      · -- covered by a good or bad ball
        have hr : 0 < D.ρ ^ (N + 1) := pow_pos hD.ρ_pos _
        have hcov := NaberValtorta.subset_net (sepCand_subset_closedBall hD N (D.state N)) hr
          (show x ∈ D.sepCand N (D.state N) from ⟨hav, hlt'⟩)
        obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 hcov
        rw [← good_succ_union_bad_succ hN] at hq
        rcases Finset.mem_union.1 hq with hq | hq
        · exact Or.inl (mem_biUnion (x := q) (Finset.mem_coe.2 hq) hxq)
        · refine Or.inr ?_
          rw [rem_succ D hN]
          exact Or.inl (Or.inr (mem_biUnion (x := q)
            (Finset.mem_coe.2 (Finset.mem_union_left _ hq)) hxq))
    · exact Or.inr (rem_mono hN (Nat.le_succ N) hx')

/-- **Termination**: if all centers have level `≤ N` and `N > j`, then
`good N = ∅`. -/
theorem good_eq_empty {N : ℕ} (hjN : D.j < N) (hlev : ∀ x ∈ D.P, D.lev x ≤ N) :
    D.good N = ∅ := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  refine Finset.eq_empty_of_forall_notMem fun y hy => ?_
  have hyP := mem_P_of_mem_succ hD (by omega) (Finset.mem_union_left _ (Finset.mem_union_left _ hy))
  exact absurd (hlev y hyP) (not_le.2 (lev_of_mem_good_succ (by omega) hy))

/-- **Claim 4.2 (b)**: the half-balls `B_{ρ^l/2}(y)` of the leaves up to scale `N` are pairwise
disjoint. -/
theorem pairwiseDisjoint_halfBalls {N : ℕ} (hN : D.j ≤ N) :
    (D.leaves N : Set (ℕ × Rn n)).PairwiseDisjoint fun q => ball q.2 (D.ρ ^ q.1 / 2) := by
  -- every leaf `(l, y)` has `y` at scale `l`, and `l > j` unless it is the good leaf `(j, p)`
  have hscale : ∀ q ∈ D.leaves N, q.1 ≤ N ∧
      (q.1 = D.j ∨ (D.j < q.1 ∧ q.2 ∈ D.good q.1 ∪ D.bad q.1 ∪ D.fin q.1)) ∧
      (q.1 < N → D.j < q.1 ∧ q.2 ∈ D.bad q.1 ∪ D.fin q.1) := by
    intro q hq
    rcases mem_leaves.1 hq with ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
    · refine ⟨h2, Or.inr ⟨h1, ?_⟩, fun _ => ⟨h1, h3⟩⟩
      rw [Finset.union_assoc]; exact Finset.mem_union_right _ h3
    · refine ⟨h1.le, ?_, fun h => absurd h1 h.ne⟩
      rcases eq_or_lt_of_le hN with hjN | hjN
      · exact Or.inl (h1.trans hjN.symm)
      · exact Or.inr ⟨h1 ▸ hjN, h1 ▸ Finset.mem_union_left _ (Finset.mem_union_left _ h3)⟩
  have hρ0 := hD.ρ_pos
  have hρ1 := hD.ρ_le_one
  -- the key separation
  have key : ∀ q ∈ D.leaves N, ∀ q' ∈ D.leaves N, q ≠ q' → q.1 ≤ q'.1 →
      D.ρ ^ q.1 ≤ dist q.2 q'.2 := by
    intro q hq q' hq' hne hle
    obtain ⟨hqN, hq1, hq2⟩ := hscale q hq
    obtain ⟨hqN', hq1', -⟩ := hscale q' hq'
    rcases eq_or_lt_of_le hle with heq | hlt
    · -- same scale
      have hy : q.2 ≠ q'.2 := fun h => hne (Prod.ext heq h)
      rcases hq1 with hj | ⟨hj, hmem⟩
      · -- scale `j`: only the leaf `(j, p)`
        exfalso
        have hq'j : q'.1 = D.j := heq ▸ hj
        have e1 : q.2 = D.p := by
          rcases mem_leaves.1 hq with ⟨h1, -, -⟩ | ⟨h1, h3⟩
          · omega
          · rw [← h1, hj, good_top] at h3; exact Finset.mem_singleton.1 h3
        have e2 : q'.2 = D.p := by
          rcases mem_leaves.1 hq' with ⟨h1, -, -⟩ | ⟨h1, h3⟩
          · omega
          · rw [← h1, hq'j, good_top] at h3; exact Finset.mem_singleton.1 h3
        exact hy (e1.trans e2.symm)
      · obtain ⟨i, hi⟩ : ∃ i, q.1 = i + 1 := ⟨q.1 - 1, by omega⟩
        have hmem' : q'.2 ∈ D.good q'.1 ∪ D.bad q'.1 ∪ D.fin q'.1 := by
          rcases hq1' with hj' | ⟨-, h⟩
          · omega
          · exact h
        rw [hi] at hmem ⊢
        rw [← heq, hi] at hmem'
        exact pow_le_dist_of_mem_succ hD (by omega) hmem hmem' hy
    · -- `q.1 < q'.1`: `q` is a bad or final leaf
      obtain ⟨hj, hmem⟩ := hq2 (hlt.trans_le hqN')
      have hmem' : q'.2 ∈ D.good q'.1 ∪ D.bad q'.1 ∪ D.fin q'.1 := by
        rcases hq1' with hj' | ⟨-, h⟩
        · omega
        · exact h
      exact pow_le_dist_of_mem_bad_fin hD hj hlt hmem hmem'
  intro q hq q' hq' hne
  refine ball_disjoint_ball ?_
  rcases le_total q.1 q'.1 with hle | hle
  · have h1 := key q hq q' hq' hne hle
    have h2 : D.ρ ^ q'.1 ≤ D.ρ ^ q.1 := pow_le_pow_of_le_one hρ0.le hρ1 hle
    linarith
  · have h1 := key q' hq' q hq (Ne.symm hne) hle
    have h2 : D.ρ ^ q.1 ≤ D.ρ ^ q'.1 := pow_le_pow_of_le_one hρ0.le hρ1 hle
    rw [dist_comm] at h1
    linarith

/-- All centers of the construction lie in the top ball. -/
theorem mem_ball_top_of_mem_succ {i : ℕ} (h : D.j ≤ i) {y : Rn n}
    (hy : y ∈ D.good (i + 1) ∪ D.bad (i + 1) ∪ D.fin (i + 1)) : y ∈ ball D.p (D.ρ ^ D.j) :=
  hD.P_subset (mem_P_of_mem_succ hD h hy)

end Claim42

/-! #### The discrete instance -/

/-- The instance of the construction for the discrete Reifenberg theorem: centers
`Z ∩ B_{ρ^j}(p)` with levels `lev`, the measure `levMeasure ρ Z lev`, planes
`V i y = bestPlane μ y (κ ρ^i)`. -/
def ofFamily (ρ κ θ : ℝ) (Z : Finset (Rn n)) (lev : Rn n → ℕ) (p : Rn n) (j : ℕ) :
    CoverData n where
  μ := levMeasure ρ Z lev
  ρ := ρ
  θ := θ
  P := (Z : Set (Rn n)) ∩ ball p (ρ ^ j)
  lev z := (lev z : ℕ∞)
  V i y := bestPlane (levMeasure ρ Z lev) y (κ * ρ ^ i)
  p := p
  j := j

/-- The discrete instance satisfies the hypotheses of Claim 4.2 when the balls are disjoint and the
top center `p ∈ Z` has level `> j`. -/
theorem ofFamily_hyp {ρ κ θ : ℝ} {Z : Finset (Rn n)} {lev : Rn n → ℕ} {p : Rn n} {j : ℕ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hdisj : (Z : Set (Rn n)).Pairwise fun a b =>
      Disjoint (ball a (ρ ^ lev a)) (ball b (ρ ^ lev b)))
    (hp : p ∈ Z) (hpj : j < lev p) : (ofFamily ρ κ θ Z lev p j).Hyp where
  ρ_pos := hρ0
  ρ_le_one := hρ1
  P_subset := inter_subset_right
  lev_gt := by
    rintro x ⟨hxZ, hxb⟩
    change ((j : ℕ) : ℕ∞) < ((lev x : ℕ) : ℕ∞)
    rw [ENat.natCast_lt_natCast]
    by_contra hle
    rw [not_lt] at hle
    have hne : x ≠ p := by rintro rfl; omega
    have hd := add_le_dist_of_disjoint hρ0 hdisj hxZ hp hne
    have h1 : ρ ^ j ≤ ρ ^ lev x := pow_le_pow_of_le_one hρ0.le hρ1 hle
    have h2 := pow_pos hρ0 (lev p)
    have h3 := mem_ball.1 hxb
    change ρ ^ lev x + ρ ^ lev p ≤ dist x p at hd
    change dist x p < ρ ^ j at h3
    linarith
  sep := by
    rintro x ⟨hxZ, -⟩ y ⟨hyZ, -⟩ hne a ha
    change ((lev x : ℕ) : ℕ∞) = (a : ℕ∞) at ha
    have ha' : lev x = a := by exact_mod_cast ha
    have hd := add_le_dist_of_disjoint hρ0 hdisj hxZ hyZ hne
    have := pow_pos hρ0 (lev y)
    change ρ ^ a ≤ dist x y
    rw [← ha']
    linarith

end CoverData

end GMTFoundations.DiscreteReifenberg
