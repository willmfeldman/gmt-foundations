/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import GMTFoundations.Defs.Setup
public import GMTFoundations.Defs.Calculus
public import GMTFoundations.Defs.GMT
public import GMTFoundations.Defs.Sobolev
public import GMTFoundations.Defs.BV
public import GMTFoundations.Statements.Sobolev
public import GMTFoundations.Statements.Reifenberg
public import GMTFoundations.Statements.Perimeter
public import GMTFoundations.Common.Divergence
public import GMTFoundations.Common.Hyperplane
public import GMTFoundations.Sobolev.L2Inner
public import GMTFoundations.Sobolev.WeakCompactness
public import GMTFoundations.Sobolev.WeakL2
public import GMTFoundations.Sobolev.Lipschitz
public import GMTFoundations.Sobolev.Cutoff
public import GMTFoundations.Sobolev.Mollify
public import GMTFoundations.Sobolev.Lattice
public import GMTFoundations.Sobolev.BallAverage
public import GMTFoundations.Sobolev.FrechetKolmogorov
public import GMTFoundations.Sobolev.FrechetKolmogorovCompact
public import GMTFoundations.Sobolev.LocalCompactness
public import GMTFoundations.Sobolev.TranslationEstimate
public import GMTFoundations.Sobolev.Rellich
public import GMTFoundations.Sobolev.PolarCoord
public import GMTFoundations.Sobolev.RayPoincare
public import GMTFoundations.Sobolev.AnnulusPoincare
public import GMTFoundations.Sobolev.SobolevInequality
public import GMTFoundations.Sobolev.SobolevOne
public import GMTFoundations.Sobolev.TraceInequality
public import GMTFoundations.Sobolev.RellichTrace
public import GMTFoundations.Vendor.Isoperimetric.Basic
public import GMTFoundations.Vendor.Isoperimetric.PrekopaLeindler
public import GMTFoundations.Vendor.Isoperimetric.BrunnMinkowski
public import GMTFoundations.GMT.Polar
public import GMTFoundations.GMT.Isodiametric
public import GMTFoundations.GMT.HausdorffLebesgue
public import GMTFoundations.GMT.Basic
public import GMTFoundations.GMT.SphereMeasure
public import GMTFoundations.GMT.FlatPiece
public import GMTFoundations.GMT.Packing
public import GMTFoundations.GMT.Rectifiable
public import GMTFoundations.GMT.ApproxTangent
public import GMTFoundations.GMT.Density
public import GMTFoundations.BV.TotalVariation
public import GMTFoundations.BV.Compactness
public import GMTFoundations.DeGiorgi.DeGiorgiSeq
public import GMTFoundations.DeGiorgi.Iteration
public import GMTFoundations.DeGiorgi.Caccioppoli
public import GMTFoundations.DeGiorgi.DeGiorgi
public import GMTFoundations.DeGiorgi.BoundaryPoincare
public import GMTFoundations.DeGiorgi.Oscillation
public import GMTFoundations.Measure.Lusin
public import GMTFoundations.Perimeter.VectorRiesz
public import GMTFoundations.Perimeter.GaussGreenPair.Basic
public import GMTFoundations.Perimeter.GaussGreenPair.API
public import GMTFoundations.Perimeter.GaussGreenPair.WeightedTV
public import GMTFoundations.Perimeter.GaussGreenPair
public import GMTFoundations.Perimeter.ReducedBoundary
public import GMTFoundations.Perimeter.DensityEstimates.Lemma53
public import GMTFoundations.Perimeter.DensityEstimates.Covering
public import GMTFoundations.Perimeter.DensityEstimates
public import GMTFoundations.Perimeter.Local
public import GMTFoundations.Perimeter.Mollify
public import GMTFoundations.Perimeter.Isoperimetric
public import GMTFoundations.Perimeter.Poincare
public import GMTFoundations.Perimeter.Slicing
public import GMTFoundations.Perimeter.HalfSpace
public import GMTFoundations.Perimeter.BlowUpScaling
public import GMTFoundations.Perimeter.BlowUpNormal
public import GMTFoundations.Perimeter.BlowUp
public import GMTFoundations.Perimeter.EssentialBoundary
public import GMTFoundations.Perimeter.ConeGraph
public import GMTFoundations.Perimeter.Structure
public import GMTFoundations.Perimeter.CriterionClaims
public import GMTFoundations.Perimeter.CriterionLines
public import GMTFoundations.Perimeter.Criterion
public import GMTFoundations.Reifenberg.Beta
public import GMTFoundations.Reifenberg.BestPlane
public import GMTFoundations.Reifenberg.Hyperplane
public import GMTFoundations.Reifenberg.Tilt
public import GMTFoundations.Reifenberg.Reductions
public import GMTFoundations.Reifenberg.Covering
public import GMTFoundations.Reifenberg.Estimates
public import GMTFoundations.Reifenberg.Induction
public import GMTFoundations.Reifenberg.EngineMass
public import GMTFoundations.Reifenberg.Discrete
public import GMTFoundations.Reifenberg.Rectifiable
public import GMTFoundations.Reifenberg.UpperDensity
public import GMTFoundations.Reifenberg.Exhaustion
public import GMTFoundations.Reifenberg.Flow
public import GMTFoundations.Reifenberg.LimitMap
public import GMTFoundations.Reifenberg.StoppingTime
public import GMTFoundations.Reifenberg.BigPieces
public import GMTFoundations.Reifenberg.PartitionOfUnity
public import GMTFoundations.Reifenberg.ReifenbergMap
public import GMTFoundations.Reifenberg.Squash
public import GMTFoundations.Reifenberg.GraphArea
public import GMTFoundations.Reifenberg.Regraph
public import GMTFoundations.Reifenberg.Engine

/-!
# GMTFoundations

Root module: `public import`s every public module of the library.

The nine headline theorems, each stated as `theorem foo : FooStatement n` with the `Prop`
`FooStatement` defined in `GMTFoundations/Statements/`, are:

* `rellich_trace_weak_compactness`: Rellich–Kondrachov compactness with compact trace on the unit
  ball (`Sobolev/RellichTrace`);
* `discrete_reifenberg`: the discrete Reifenberg upper bound for hyperplanes (Naber–Valtorta
  Thm 3.4, proved via Miśkiewicz Thm 1.1 with `q = 2`) (`Reifenberg/Discrete`);
* `rectifiable_reifenberg`: a β-square-function bound together with an upper density bound implies
  countable `(n-1)`-rectifiability (rectifiability part of Naber–Valtorta Thm 3.3)
  (`Reifenberg/Rectifiable`);
* `exists_isGaussGreenPair_of_integral_divergence_le`: a variation bound gives a Gauss–Green pair
  (Evans–Gariepy Thm 5.1) (`Perimeter/GaussGreenPair`);
* `hasLocallyFinitePerimeter_of_local`: a divergence bound near each point of an open set `U`
  gives locally finite perimeter in `U` (Evans–Gariepy Thm 5.1, `BV_loc` form) (`Perimeter/Local`);
* `hasDensity_symmDiff_halfSpace`: De Giorgi's blow-up to a half-space at reduced-boundary points
  (Evans–Gariepy Thm 5.13) (`Perimeter/BlowUp`);
* `HasLocallyFinitePerimeter.rectifiable_essentialBoundary`: the essential boundary of a set of
  locally finite perimeter is countably `(n-1)`-rectifiable (Evans–Gariepy Thm 5.15, Lemma 5.5)
  (`Perimeter/Structure`);
* `IsGaussGreenPair.eq_hausdorffN_restrict`: the Gauss–Green measure equals `ℋ^{n-1}⌊∂ᵉE`
  (Evans–Gariepy Thms 5.15, 5.16) (`Perimeter/Structure`);
* `ae_trivial_of_hausdorffN_essentialBoundary_inter_ball`: if `ℋ^{n-1}(∂ᵉE ∩ B) = 0` then `E` is
  a.e. empty or a.e. all of the ball `B` (null case of Federer's criterion, Evans–Gariepy Thm 5.23)
  (`Perimeter/Criterion`).

References:
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, rev. ed.,
  CRC Press, 2015.
* A. Naber, D. Valtorta, *Rectifiable-Reifenberg and the regularity of stationary and minimizing
  harmonic maps*, Ann. of Math. 185 (2017), 131–227; arXiv:1504.02043.
* M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018);
  arXiv:1612.02461.
-/
