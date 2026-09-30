import Statement
import GMTFoundations

/-!
# Solution: structure theory of sets of locally finite perimeter

The trusted vocabulary of `Statement.lean` agrees with the library's: `hausdorffN`, `divergence`,
`IsSmoothTestField`, `IsCountablyRectifiable`, `HasDensity` and `essentialBoundary` are
definitionally equal to their `GMTFoundations` counterparts; `IsGaussGreenPair` has the same
fields (`isGaussGreenPair_iff`), hence the two `reducedBoundary` sets agree; and
`GMTChallenge.HasLocallyFinitePerimeter` is the hypothesis of
`GMTFoundations.hasLocallyFinitePerimeter_of_local`, whose conclusion is the library's
`HasLocallyFinitePerimeter` (existence of a Gauss–Green pair).
-/

open MeasureTheory

namespace GMTChallenge.Bridge

variable {n : ℕ}

theorem isGaussGreenPair_iff {Ω E : Set (Rn n)} {μ : Measure (Rn n)} {ν : Rn n → Rn n} :
    IsGaussGreenPair Ω E μ ν ↔ GMTFoundations.IsGaussGreenPair Ω E μ ν :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩

theorem reducedBoundary_eq (Ω E : Set (Rn n)) :
    reducedBoundary Ω E = GMTFoundations.reducedBoundary Ω E := by
  ext x
  simp only [reducedBoundary, GMTFoundations.reducedBoundary, Set.mem_ofPred_eq,
    isGaussGreenPair_iff]

theorem exists_isGaussGreenPair_iff {Ω E : Set (Rn n)} :
    (∃ μ ν, IsGaussGreenPair Ω E μ ν) ↔ GMTFoundations.HasLocallyFinitePerimeter Ω E := by
  simp only [isGaussGreenPair_iff, GMTFoundations.HasLocallyFinitePerimeter]

end GMTChallenge.Bridge

open GMTChallenge GMTChallenge.Bridge

theorem challenge_gauss_green_pair_of_divergence_bound (n : ℕ) :
    GaussGreenPairOfDivergenceBoundClaim n := by
  intro hn U E hU hE C h
  obtain ⟨μ, ν, hp, hμ⟩ :=
    GMTFoundations.exists_isGaussGreenPair_of_integral_divergence_le hn hU hE C h
  exact ⟨μ, ν, isGaussGreenPair_iff.2 hp, hμ⟩

theorem challenge_gauss_green_pair_of_locally_finite_perimeter (n : ℕ) :
    GaussGreenPairOfLocallyFinitePerimeterClaim n := by
  intro hn U E hU hE h
  exact exists_isGaussGreenPair_iff.2 (GMTFoundations.hasLocallyFinitePerimeter_of_local hn hU hE h)

theorem challenge_half_space_blow_up (n : ℕ) : HalfSpaceBlowUpClaim n := by
  intro hn Ω E hΩ hE μ ν h x hx hpos v hv hlim
  exact GMTFoundations.hasDensity_symmDiff_halfSpace hn hΩ hE (isGaussGreenPair_iff.1 h) hx hpos
    hv hlim

theorem challenge_rectifiable_essential_boundary (n : ℕ) :
    RectifiableEssentialBoundaryClaim n := by
  intro hn Ω E hΩ hE h
  rw [reducedBoundary_eq]
  exact GMTFoundations.HasLocallyFinitePerimeter.rectifiable_essentialBoundary hn hΩ hE
    (GMTFoundations.hasLocallyFinitePerimeter_of_local hn hΩ hE h)

theorem challenge_perimeter_measure_eq_hausdorff (n : ℕ) :
    GaussGreenMeasureEqHausdorffClaim n := by
  intro hn Ω E μ ν hΩ hE h
  exact GMTFoundations.IsGaussGreenPair.eq_hausdorffN_restrict hn hΩ hE (isGaussGreenPair_iff.1 h)

theorem challenge_trivial_of_null_essential_boundary (n : ℕ) :
    TrivialOfNullEssentialBoundaryClaim n := by
  intro hn E hE c r h
  exact GMTFoundations.ae_trivial_of_hausdorffN_essentialBoundary_inter_ball hn hE h
