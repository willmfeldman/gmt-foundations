/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Perimeter.EssentialBoundary
public import GMTFoundations.GMT.FlatPiece
import GMTFoundations.Reifenberg.Exhaustion
import Mathlib.Data.Real.StarOrdered

/-!
# The cone condition and Lipschitz graphs (EG Thm 5.15 step 3)

Reference: L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
CRC Press, 2015 (cited as EG; numbering of the revised edition).

For the rectifiability of `∂*E` we follow EG Thm 5.15 steps 1–3 (Egorov, Lusin, the cone
condition) and then replace step 4 (Whitney's extension theorem and the implicit function theorem,
which produce `C¹` hypersurfaces) by an elementary argument: the cone condition makes small pieces
of `K` Lipschitz graphs over `ν(x)^⊥`, which extend to Lipschitz maps `ℝ^{n-1} → ℝⁿ` by McShane.
Only countable `ℋ^{n-1}`-rectifiability is proved, not the `C¹` statement of EG Thm 5.15 (i).

* `abs_inner_le_of_uniform_halfSpace` (EG Thm 5.15 step 3, Claim): if `E` is uniformly close to
  the half-spaces `{⟪y - x, ν x⟫ < 0}` at the points `x ∈ K`, in the sense that
  `|(E △ H⁻(x)) ∩ B_r(x)| ≤ η |B_r(x)|` for `r < r₀(η)`, then chords of `K` are almost orthogonal
  to `ν`: `|⟪y - x, ν x⟫| ≤ ε ‖y - x‖` for `x, y ∈ K` close together. EG's volume contradiction,
  with `η = ε^n / 2^{n+2}` (EG's constant) and `δ = r₀/2`. EG state (⋆⋆⋆) for `r < 2δ` but use it at
  `r = 2|x - y|` with `|x - y| ≤ δ`, i.e. at the excluded endpoint; we take `|x - y| < δ`.
* `isFlatPiece_inter_ball_of_cone`: with `ν` continuous on `K`, the cone condition at `ε = 1/4`
  and the oscillation `‖ν z - ν x₀‖ ≤ 1/4` make `K ∩ B_ρ(x₀)` a `1/2`-flat piece with normal `ν x₀`.
* `GMT.IsFlatPiece.exists_lipschitzWith_range_superset`: a flat piece lies in the range
  of a Lipschitz map `ℝ^{n-1} → ℝⁿ` (inverse of the projection `projH`, which is
  `(1 - ε)⁻¹`-Lipschitz, composed with an isometry `ℝ^{n-1} ≅ ν^⊥` and extended by McShane).
  This replaces EG's Whitney extension and implicit function theorem (step 4).
* `exists_lipschitz_cover_of_cone`: a set with the cone condition and continuous unit `ν` is
  covered by countably many Lipschitz images of `ℝ^{n-1}`.
* `IsCountablyRectifiable.mono`, `IsCountablyRectifiable.of_countable`: bookkeeping.
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

public section

namespace GMTFoundations

variable {n : ℕ}

/-! ### Countable rectifiability: bookkeeping -/

/-- Countable rectifiability passes to subsets. -/
theorem IsCountablyRectifiable.mono {k : ℕ} {S T : Set (Rn n)} (h : IsCountablyRectifiable n k T)
    (hST : S ⊆ T) : IsCountablyRectifiable n k S := by
  obtain ⟨f, hf, h0⟩ := h
  exact ⟨f, hf, measure_mono_null (diff_subset_diff_left hST) h0⟩

/-- Countable rectifiability from a cover indexed by any countable type. -/
theorem IsCountablyRectifiable.of_countable {k : ℕ} {ι : Type*} [Countable ι] {S : Set (Rn n)}
    (f : ι → Rn k → Rn n) (hf : ∀ i, ∃ C, LipschitzWith C (f i))
    (h : hausdorffN n k (S \ ⋃ i, range (f i)) = 0) : IsCountablyRectifiable n k S := by
  obtain ⟨e, he⟩ := exists_surjective_nat (Option ι)
  refine ⟨fun m => (e m).elim (fun _ => 0) f, fun m => ?_, measure_mono_null ?_ h⟩
  · dsimp only
    rcases h : e m with _ | i
    · exact ⟨0, by simp [Option.elim]⟩
    · simpa [Option.elim] using hf i
  · refine diff_subset_diff_right (iUnion_subset fun i => ?_)
    obtain ⟨m, hm⟩ := he (some i)
    refine (subset_of_eq ?_).trans (subset_iUnion _ m)
    simp [hm]

/-! ### The cone condition (EG Thm 5.15 step 3) -/

/-- **Cone condition** (EG Thm 5.15, step 3, Claim). If `E` is uniformly close to the half-spaces
`H⁻(x) = {⟪y - x, ν x⟫ < 0}` at the points of `K`, then for `x, y ∈ K` close together
`|⟪y - x, ν x⟫| ≤ ε ‖y - x‖`. -/
theorem abs_inner_le_of_uniform_halfSpace (hn : 1 ≤ n) {E K : Set (Rn n)} {ν : Rn n → Rn n}
    (hν : ∀ x ∈ K, ‖ν x‖ = 1)
    (hunif : ∀ η : ℝ, 0 < η → ∃ r₀ > 0, ∀ x ∈ K, ∀ r, 0 < r → r < r₀ →
      volume (symmDiff E {y | ⟪y - x, ν x⟫ < 0} ∩ ball x r) ≤ ENNReal.ofReal η * volume (ball x r))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y ∈ K, dist y x < δ → |⟪y - x, ν x⟫| ≤ ε * ‖y - x‖ := by
  set W := (volume (ball (0 : Rn n) 1)).toReal
  have hW : 0 < W :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hvol : ∀ (c : Rn n) {ρ : ℝ}, 0 < ρ → (volume (ball c ρ)).toReal = ρ ^ n * W := by
    intro c ρ hρ
    rw [Measure.addHaar_ball_of_pos volume c hρ, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ.le n)]
  have hfin : ∀ (S : Set (Rn n)) (c : Rn n) (ρ : ℝ), volume (S ∩ ball c ρ) ≠ ∞ := fun S c ρ =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  set η : ℝ := ε ^ n / (2 ^ n * 4) with hη_def
  have hη : 0 < η := by positivity
  have hηlt : η < 1 / 4 := by
    have h1 : ε ^ n < 1 := pow_lt_one₀ hε.le hε1 (by omega)
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    rw [hη_def, div_lt_iff₀ (by positivity)]
    linarith
  obtain ⟨r₀, hr₀, hU⟩ := hunif η hη
  have hUr : ∀ z ∈ K, ∀ r, 0 < r → r < r₀ →
      (volume (symmDiff E {y | ⟪y - z, ν z⟫ < 0} ∩ ball z r)).toReal ≤ η * (r ^ n * W) := by
    intro z hz r hr hrr
    rw [← hvol z hr, ← ENNReal.toReal_ofReal hη.le, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
      (hU z hz r hr hrr)
  refine ⟨r₀ / 2, half_pos hr₀, fun x hx y hy hxy => ?_⟩
  by_contra hcon
  push Not at hcon
  set d := ‖y - x‖ with hd_def
  have hd : 0 < d := by
    refine (norm_nonneg _).lt_of_ne fun h0 => ?_
    have hyx : y - x = 0 := norm_eq_zero.1 h0.symm
    have hd0 : d = 0 := by rw [hd_def]; exact h0.symm
    rw [hyx, inner_zero_left, abs_zero, hd0, mul_zero] at hcon
    exact lt_irrefl _ hcon
  have hdr : d < r₀ / 2 := by rwa [dist_eq_norm] at hxy
  set s := ε * d with hs_def
  have hs : 0 < s := mul_pos hε hd
  have hsd : s < d := by rw [hs_def]; nlinarith
  have hνx := hν x hx
  have hνy := hν y hy
  have hνy0 : ν y ≠ 0 := fun h0 => by rw [h0, norm_zero] at hνy; exact zero_ne_one hνy
  -- points of `B_s(y)`: distance to `x` and the inner product with `ν x`
  have hball : ∀ z ∈ ball y s, dist z x < 2 * d ∧
      |⟪z - x, ν x⟫ - ⟪y - x, ν x⟫| < s := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    refine ⟨?_, ?_⟩
    · calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ < s + d := by rw [dist_eq_norm, dist_eq_norm]; linarith
        _ < 2 * d := by linarith
    · have : ⟪z - x, ν x⟫ - ⟪y - x, ν x⟫ = ⟪z - y, ν x⟫ := by
        rw [← inner_sub_left]; congr 1; abel
      rw [this]
      calc |⟪z - y, ν x⟫| ≤ ‖z - y‖ * ‖ν x‖ := abs_real_inner_le_norm _ _
        _ < s := by rw [hνx, mul_one]; exact hz
  have hQx := hUr x hx (2 * d) (by positivity) (by linarith)
  have hQy := hUr y hy s hs (by linarith)
  -- half of `B_s(y)` is covered by `A₁ ∪ (Q(y) ∩ B_s(y))`
  have hhalf : ∀ (S A₁ : Set (Rn n)), volume S = volume (ball y s) / 2 →
      S ⊆ A₁ ∪ symmDiff E {w | ⟪w - y, ν y⟫ < 0} ∩ ball y s → volume A₁ ≠ ∞ →
      s ^ n * W / 2 ≤ (volume A₁).toReal + η * (s ^ n * W) := by
    intro S A₁ hS hSA hA₁
    have h1 : (volume S).toReal = s ^ n * W / 2 := by
      rw [hS, ENNReal.toReal_div, hvol y hs]; norm_num
    rw [← h1]
    refine le_trans ?_ (add_le_add le_rfl hQy)
    rw [← ENNReal.toReal_add hA₁ (hfin _ _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hA₁, hfin _ _ _⟩)
      ((measure_mono hSA).trans (measure_union_le _ _))
  obtain ⟨A, hA1, hA2⟩ : ∃ A : Set (Rn n), (volume A).toReal ≤ η * ((2 * d) ^ n * W) ∧
      s ^ n * W / 2 ≤ (volume A).toReal + η * (s ^ n * W) := by
    rcases lt_abs.1 hcon with h1 | h1
    · -- `⟪y - x, ν x⟫ > ε d`: `B_s(y)` lies in `{⟪z - x, ν x⟫ > 0}`, so `E ∩ B_s(y)` is small
      refine ⟨E ∩ ball y s, le_trans (ENNReal.toReal_mono (hfin _ _ _) (measure_mono ?_)) hQx,
        hhalf _ _ (volume_halfSpace_inter_ball hνy0 y s) ?_ (hfin _ _ _)⟩
      · rintro z ⟨hzE, hz⟩
        obtain ⟨hzx, hzi⟩ := hball z hz
        refine ⟨Or.inl ⟨hzE, ?_⟩, hzx⟩
        simp only [mem_setOf_eq, not_lt]
        rw [abs_lt] at hzi
        linarith [hzi.1]
      · rintro z ⟨hzH, hz⟩
        by_cases hzE : z ∈ E
        · exact Or.inl ⟨hzE, hz⟩
        · exact Or.inr ⟨Or.inr ⟨hzH, hzE⟩, hz⟩
    · -- `⟪y - x, ν x⟫ < -ε d`: `B_s(y)` lies in `H⁻(x)`, so `B_s(y) ∖ E` is small
      refine ⟨ball y s \ E, le_trans (ENNReal.toReal_mono ?_ (measure_mono ?_)) hQx,
        hhalf _ _ (volume_halfSpace_pos_inter_ball hνy0 y s) ?_ ?_⟩
      · exact hfin _ _ _
      · rintro z ⟨hz, hzE⟩
        obtain ⟨hzx, hzi⟩ := hball z hz
        refine ⟨Or.inr ⟨?_, hzE⟩, hzx⟩
        simp only [mem_setOf_eq]
        rw [abs_lt] at hzi
        linarith [hzi.2]
      · rintro z ⟨hzH, hz⟩
        by_cases hzE : z ∈ E
        · refine Or.inr ⟨Or.inl ⟨hzE, ?_⟩, hz⟩
          simp only [mem_setOf_eq, not_lt]
          exact le_of_lt hzH
        · exact Or.inl ⟨hz, hzE⟩
      · exact ((measure_mono diff_subset).trans_lt measure_ball_lt_top).ne
  -- the volume contradiction: `½ ≤ η (2/ε)ⁿ + η = ¼ + η < ½`
  have hcomb : s ^ n * W / 2 ≤ η * ((2 * d) ^ n * W) + η * (s ^ n * W) := by linarith
  set X := ε ^ n * d ^ n * W with hX_def
  have hX : 0 < X := by positivity
  have hsX : s ^ n * W = X := by rw [hs_def, mul_pow]
  have h2X : η * ((2 * d) ^ n * W) = X / 4 := by
    rw [hη_def, hX_def, mul_pow]
    field_simp
  rw [hsX, h2X] at hcomb
  linarith [mul_lt_mul_of_pos_right hηlt hX]

/-! ### Cone condition ⇒ flat pieces ⇒ Lipschitz graphs -/

/-- With `ν` continuous on `K` and the cone condition at `ε = 1/4`, a small ball around
`x₀ ∈ K` cuts out a `1/2`-flat piece of `K` with normal `ν x₀`
(`1/4` from the cone condition plus `1/4` from the oscillation of `ν`). -/
theorem isFlatPiece_inter_ball_of_cone {K : Set (Rn n)} {ν : Rn n → Rn n} {x₀ : Rn n}
    (hx₀ : x₀ ∈ K) (hc : ContinuousOn ν K) {δ : ℝ} (hδ : 0 < δ)
    (hcone : ∀ x ∈ K, ∀ y ∈ K, dist y x < δ → |⟪y - x, ν x⟫| ≤ (1 / 4) * ‖y - x‖) :
    ∃ ρ > 0, GMT.IsFlatPiece (ν x₀) (1 / 2) (K ∩ ball x₀ ρ) := by
  obtain ⟨δ₂, hδ₂, hosc⟩ := Metric.continuousOn_iff.1 hc x₀ hx₀ (1 / 4) (by norm_num)
  refine ⟨min δ δ₂ / 2, by positivity, fun y ⟨hyK, hy⟩ z ⟨hzK, hz⟩ => ?_⟩
  rw [mem_ball] at hy hz
  have hmin1 := min_le_left δ δ₂
  have hmin2 := min_le_right δ δ₂
  have hyz : dist y z < δ := by
    calc dist y z ≤ dist y x₀ + dist z x₀ := dist_triangle_right _ _ _
      _ < δ := by linarith
  have hνz : ‖ν x₀ - ν z‖ ≤ 1 / 4 := by
    rw [← dist_eq_norm, dist_comm]
    exact (hosc z hzK (by linarith)).le
  have hsplit : ⟪y - z, ν x₀⟫ = ⟪y - z, ν z⟫ + ⟪y - z, ν x₀ - ν z⟫ := by
    rw [inner_sub_right]; ring
  rw [hsplit]
  calc |⟪y - z, ν z⟫ + ⟪y - z, ν x₀ - ν z⟫|
      ≤ |⟪y - z, ν z⟫| + |⟪y - z, ν x₀ - ν z⟫| := abs_add_le _ _
    _ ≤ (1 / 4) * ‖y - z‖ + ‖y - z‖ * ‖ν x₀ - ν z‖ :=
        add_le_add (hcone z hzK y hyK hyz) (abs_real_inner_le_norm _ _)
    _ ≤ (1 / 4) * ‖y - z‖ + ‖y - z‖ * (1 / 4) := by gcongr
    _ = (1 / 2) * ‖y - z‖ := by ring

/-- **Flat pieces are Lipschitz graphs**. An `ε`-flat piece (`ε < 1`) with unit normal
`ν` lies in the range of a Lipschitz map `ℝ^{n-1} → ℝⁿ`: the inverse of `projH ν` on the piece is
`(1 - ε)⁻¹`-Lipschitz; compose it with an isometry `ℝ^{n-1} ≅ ν^⊥` and extend (McShane). -/
theorem GMT.IsFlatPiece.exists_lipschitzWith_range_superset (hn : 1 ≤ n) {ν : Rn n}
    (hν : ‖ν‖ = 1) {ε : ℝ} (hε : ε < 1) {G : Set (Rn n)} (hG : GMT.IsFlatPiece ν ε G) :
    ∃ F : Rn (n - 1) → Rn n, (∃ C, LipschitzWith C F) ∧ G ⊆ range F := by
  have hν0 : ν ≠ 0 := fun h0 => by rw [h0, norm_zero] at hν; exact zero_ne_one hν
  obtain ⟨L, hL⟩ := exists_linearIsometry_range_eq hn hν0
  set P := GMT.projH ν
  set g := Function.invFunOn P G
  have hg : ∀ a ∈ P '' G, g a ∈ G ∧ P (g a) = a := by
    rintro a ⟨y, hy, rfl⟩
    exact ⟨Function.invFunOn_mem ⟨y, hy, rfl⟩, Function.invFunOn_eq ⟨y, hy, rfl⟩⟩
  have h1ε : 0 < 1 - ε := by linarith
  set s := L ⁻¹' (P '' G)
  have hlip : LipschitzOnWith (Real.toNNReal (1 - ε)⁻¹) (g ∘ L) s := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    obtain ⟨hga, hPa⟩ := hg _ ha
    obtain ⟨hgb, hPb⟩ := hg _ hb
    have h := hG.norm_projH_sub_ge hν hga hgb
    change (1 - ε) * _ ≤ ‖P _ - P _‖ at h
    rw [hPa, hPb] at h
    rw [Real.coe_toNNReal _ (inv_nonneg.2 h1ε.le), Function.comp_apply, Function.comp_apply,
      dist_eq_norm, ← L.isometry.dist_eq, dist_eq_norm, inv_mul_eq_div, le_div_iff₀ h1ε,
      mul_comm]
    exact h
  obtain ⟨F, hF, hEq⟩ := hlip.extend_finite_dimension
  refine ⟨F, ⟨_, hF⟩, fun y hy => ?_⟩
  have hPy : P y ∈ range L := by rw [hL]; exact GMT.projH_mem_hyperplane hν y
  obtain ⟨a, ha⟩ := hPy
  have has : a ∈ s := by change L a ∈ P '' G; rw [ha]; exact ⟨y, hy, rfl⟩
  refine ⟨a, ?_⟩
  rw [← hEq has, Function.comp_apply, ha]
  obtain ⟨hgy, hPgy⟩ := hg (P y) ⟨y, hy, rfl⟩
  exact hG.injOn_projH hν hε hgy hy hPgy

/-- A set `K` with continuous unit normal field satisfying the cone condition at `ε = 1/4` is
covered by countably many Lipschitz images of `ℝ^{n-1}`. -/
theorem exists_lipschitz_cover_of_cone (hn : 1 ≤ n) {K : Set (Rn n)} {ν : Rn n → Rn n}
    (hν : ∀ x ∈ K, ‖ν x‖ = 1) (hc : ContinuousOn ν K) {δ : ℝ} (hδ : 0 < δ)
    (hcone : ∀ x ∈ K, ∀ y ∈ K, dist y x < δ → |⟪y - x, ν x⟫| ≤ (1 / 4) * ‖y - x‖) :
    ∃ F : ℕ → Rn (n - 1) → Rn n, (∀ i, ∃ C, LipschitzWith C (F i)) ∧ K ⊆ ⋃ i, range (F i) := by
  choose! ρ hρ hflat using fun x₀ (hx₀ : x₀ ∈ K) => isFlatPiece_inter_ball_of_cone hx₀ hc hδ hcone
  choose! F hFL hFG using fun x₀ (hx₀ : x₀ ∈ K) =>
    (hflat x₀ hx₀).exists_lipschitzWith_range_superset hn (hν x₀ hx₀) (by norm_num)
  obtain ⟨T, hTK, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable K (fun x => ball x (ρ x))
    fun _ _ => isOpen_ball
  have hcov : ∀ x ∈ K, ∃ t ∈ T, x ∈ K ∩ ball t (ρ t) := by
    intro x hx
    have : x ∈ ⋃ i ∈ K, ball i (ρ i) := mem_biUnion hx (mem_ball_self (hρ x hx))
    rw [← hTU] at this
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 this
    exact ⟨t, ht, hx, hxt⟩
  rcases T.eq_empty_or_nonempty with hT | hT
  · refine ⟨fun _ _ => 0, fun _ => ⟨0, LipschitzWith.const _⟩, fun x hx => ?_⟩
    obtain ⟨t, ht, -⟩ := hcov x hx
    rw [hT] at ht; exact ht.elim
  obtain ⟨e, he⟩ := hTc.exists_eq_range hT
  refine ⟨fun i => F (e i), fun i => hFL _ (hTK (he ▸ mem_range_self i)), fun x hx => ?_⟩
  obtain ⟨t, ht, hxt⟩ := hcov x hx
  rw [he] at ht
  obtain ⟨i, rfl⟩ := ht
  exact mem_iUnion.2 ⟨i, hFG _ (hTK (he ▸ mem_range_self i)) hxt⟩

end GMTFoundations
