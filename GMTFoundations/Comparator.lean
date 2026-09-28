/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations

/-!
# Comparator

A small API-regression smoke test for the public import.

This file restates the nine headline theorems of `GMTFoundations` through the public import only,
and discharges each by `exact` from the library. It guards against an accidental rename, signature
drift, or a `Statements/*` file dropping out of the import graph.

The standalone comparator challenge workspaces in `challenges/` restate the same nine statements
inline over `Mathlib` only, for an independent check; see `challenges/README.md` and
`formalization.yaml`.

References:
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
  CRC Press, 2015 (EG).
* A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and minimizing
  harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043 (NV).
* M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018);
  arXiv:1612.02461.
-/

@[expose] public noncomputable section

namespace GMTFoundations.Comparator

open GMTFoundations

variable {n : ℕ}

/-- Challenge: Rellich–Kondrachov compactness with compact trace on the unit ball. -/
theorem challenge_rellich_trace_weak_compactness [NeZero n] : RellichTraceStatement n :=
  rellich_trace_weak_compactness

/-- Challenge: the discrete Reifenberg upper bound for hyperplanes (NV Thm 3.4, via Miśkiewicz
Thm 1.1 with `q = 2`). -/
theorem challenge_discrete_reifenberg : DiscreteReifenbergStatement n :=
  discrete_reifenberg

/-- Challenge: rectifiable-Reifenberg for hyperplanes, rectifiability part of NV Thm 3.3, under an
upper density bound on every ball. -/
theorem challenge_rectifiable_reifenberg : RectifiableReifenbergStatement n :=
  rectifiable_reifenberg

/-- Challenge: a Gauss–Green pair from an integral-divergence bound (EG Thm 5.1). -/
theorem challenge_exists_isGaussGreenPair_of_integral_divergence_le :
    GaussGreenPairOfDivergenceBoundStatement n :=
  exists_isGaussGreenPair_of_integral_divergence_le

/-- Challenge: the `BV_loc` structure theorem for sets (EG Thm 5.1). -/
theorem challenge_hasLocallyFinitePerimeter_of_local : LocallyFinitePerimeterOfLocalStatement n :=
  hasLocallyFinitePerimeter_of_local

/-- Challenge: De Giorgi's blow-up theorem at reduced-boundary points (EG Thm 5.13). -/
theorem challenge_hasDensity_symmDiff_halfSpace : HalfSpaceBlowUpStatement n :=
  hasDensity_symmDiff_halfSpace

/-- Challenge: rectifiability of the essential boundary (De Giorgi–Federer; EG Thm 5.15,
Lemma 5.5). -/
theorem challenge_rectifiable_essentialBoundary : RectifiableEssentialBoundaryStatement n :=
  HasLocallyFinitePerimeter.rectifiable_essentialBoundary

/-- Challenge: the Gauss–Green measure equals `ℋ^{n-1}⌊∂ᵉE` (EG Thms 5.15, 5.16). -/
theorem challenge_eq_hausdorffN_restrict : GaussGreenMeasureEqHausdorffStatement n :=
  IsGaussGreenPair.eq_hausdorffN_restrict

/-- Challenge: triviality in a ball under an `ℋ^{n-1}`-null essential boundary (null case of
Federer's criterion, EG Thm 5.23). -/
theorem challenge_ae_trivial_of_hausdorffN_essentialBoundary_inter_ball :
    TrivialOfNullEssentialBoundaryStatement n :=
  ae_trivial_of_hausdorffN_essentialBoundary_inter_ball

end GMTFoundations.Comparator
