# GMT Foundations

A Lean 4 / Mathlib formalization of results in geometric measure theory and Sobolev spaces: the
De Giorgi–Federer structure theory of sets of locally finite perimeter, following L. C. Evans and
R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition, CRC Press,
2015; the discrete and rectifiable Reifenberg theorems of A. Naber and D. Valtorta,
*Rectifiable-Reifenberg and the regularity of stationary and minimizing harmonic maps*, Ann. of
Math. (2) 185 (2017), 131–227 (arXiv:1504.02043), for hyperplanes; and Rellich–Kondrachov
compactness with compact boundary trace on the unit ball.

The library has about 34,000 lines of Lean. It is sorry-free, and each of the nine headline
theorems below depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`
(`#print axioms`, checked in CI).

## Headline theorems

Each theorem is stated as `theorem foo : FooStatement n`, where `FooStatement` is a named `Prop`
in `GMTFoundations/Statements/`. `EG` is Evans–Gariepy (revised edition, 2015) and `NV` is
Naber–Valtorta (2017); the theorem numbers are theirs.

| # | Result | Lean name (namespace `GMTFoundations`) | Source |
|---|---|---|---|
| 1 | Rellich–Kondrachov compactness with compact trace on the unit ball | `rellich_trace_weak_compactness` | EG Thms 4.11, 4.6 |
| 2 | Discrete Reifenberg theorem for hyperplanes | `discrete_reifenberg` | NV Thm 3.4; Miśkiewicz Thm 1.1 |
| 3 | Rectifiable-Reifenberg theorem for hyperplanes (rectifiability) | `rectifiable_reifenberg` | NV Thm 3.3 (2) |
| 4 | Gauss–Green measure from a divergence bound | `exists_isGaussGreenPair_of_integral_divergence_le` | EG Thm 5.1 |
| 5 | Gauss–Green pair for sets of locally finite perimeter | `hasLocallyFinitePerimeter_of_local` | EG Thm 5.1 |
| 6 | De Giorgi's blow-up at reduced-boundary points | `hasDensity_symmDiff_halfSpace` | EG Thm 5.13 |
| 7 | Rectifiability of the essential boundary | `HasLocallyFinitePerimeter.rectifiable_essentialBoundary` | EG Thm 5.15 (i), Lemma 5.5 |
| 8 | Perimeter measure `= ℋ^{n-1}⌊∂_*E` | `IsGaussGreenPair.eq_hausdorffN_restrict` | EG Thm 5.15 (iii), Lemma 5.5 |
| 9 | Federer's criterion, null case | `ae_trivial_of_hausdorffN_essentialBoundary_inter_ball` | EG Thms 5.23, 5.11 |

Miśkiewicz is M. Miśkiewicz, *Discrete Reifenberg-type theorem*, Ann. Acad. Sci. Fenn. Math. 43
(2018) (arXiv:1612.02461). `formalization.yaml` states each theorem in words.

For example, theorem 9, quoted from `GMTFoundations/Statements/Perimeter.lean` and
`GMTFoundations/Perimeter/Criterion.lean` (inside `namespace GMTFoundations`):

```lean
def TrivialOfNullEssentialBoundaryStatement (n : ℕ) : Prop :=
  ∀ (hn : 2 ≤ n) {E : Set (Rn n)}
    (hE : MeasurableSet E) {c : Rn n} {r : ℝ}
    (h : hausdorffN n (n - 1) (essentialBoundary E ∩ ball c r) = 0),
    volume (E ∩ ball c r) = 0 ∨ volume (ball c r \ E) = 0

theorem ae_trivial_of_hausdorffN_essentialBoundary_inter_ball :
    TrivialOfNullEssentialBoundaryStatement n
```

Here `Rn n` is `EuclideanSpace ℝ (Fin n)`, `hausdorffN n d` is the `d`-dimensional Hausdorff
measure normalized as in EG, and `essentialBoundary E` is the measure-theoretic boundary (points
where `E` has neither density `0` nor density `1`). These definitions are in
`GMTFoundations/Defs/`.

## Status

All nine headline theorems are proved, with no `sorry`, `admit`, `axiom` declarations or
`native_decide` anywhere in the library. Where the formal statements differ from the textbook
ones:

- The Reifenberg theorems are the codimension-one case (`k = n − 1`), with the mass threshold
  `ε_n` of NV Definition 3.1 set to `0` (NV Remark 3.2). The discrete theorem is stated for
  finite collections of balls. The rectifiable theorem gives the rectifiability conclusion only,
  and assumes in addition that `S` is Borel with `ℋ^{n-1}(S) < ∞` and satisfies an upper density
  bound `ℋ^{n-1}(S ∩ B_r(x)) ≤ C r^{n-1}`; its `δ` depends on `C`.
- The perimeter theorems are for `n ≥ 2`, on open sets `Ω ⊆ ℝⁿ`, with open balls. A set has
  locally finite perimeter in `Ω` when it has a Gauss–Green pair `(μ, ν)` there (a Radon measure
  and a `μ`-a.e. unit normal satisfying the Gauss–Green formula); theorems 4 and 5 derive this
  from the distributional definition. Federer's criterion is proved in its null case, localized
  to a ball.
- In theorem 1 the boundary values converge in `L²(∂B₁)` to some limit; the statement does not
  identify that limit as the trace of the `L²` limit.

## Proof routes

- **Discrete Reifenberg** follows Miśkiewicz's proof (Theorem 1.1 with `q = 2`), a
  Reifenberg-type construction of approximating surfaces with a squash lemma, specialized to
  hyperplanes.
- **Rectifiable Reifenberg** runs the same construction on the measure `ℋ^{n-1}⌊S`, uses a
  stopping time to find big pieces of Lipschitz images, and exhausts `S` by them.
- **Gauss–Green pairs** come from a vector-valued Riesz representation of the distribution
  `Dχ_E` (EG Theorem 5.1).
- **Blow-up** follows EG Theorem 5.13: density estimates at the reduced boundary (EG Lemma 5.3),
  BV compactness, and constancy of the normal of a blow-up limit.
- **Structure theorem**: Egorov, Lusin and the cone condition (EG Theorem 5.15, steps 1–3) give
  Lipschitz graphs over the normal hyperplanes, which are extended to Lipschitz maps on `ℝ^{n-1}`
  (McShane). A density theorem for rectifiable sets and Besicovitch differentiation then identify
  the perimeter measure with `ℋ^{n-1}⌊∂_*E`, without the area formula.
- **Federer's criterion, null case**: the line-slicing argument of EG Theorem 5.23 shows that
  the total variation of `χ_E` vanishes in the ball, and an `L¹` Poincaré inequality on balls
  gives triviality.
- **Rellich with trace**: local Rellich compactness on compact subsets of the ball, plus an
  `L²` estimate along rays near the sphere, give strong `L²(B₁)` convergence; a trace inequality
  along rays in polar coordinates gives convergence in `L²(∂B₁)`.

Supporting material includes the isodiametric inequality and `ℋⁿ = ℒⁿ`, the surface measure of
the sphere as normalized Hausdorff measure, Jones β-numbers, Fréchet–Kolmogorov compactness in
`Lᵖ`, weak `L²` compactness, BV compactness and lower semicontinuity of total variation, the
isoperimetric and relative isoperimetric inequalities, and a De Giorgi iteration toolkit
(Caccioppoli inequalities, the De Giorgi `L^∞` lemma, oscillation decay).

## Build

The project uses Lean `v4.34.1` and Mathlib `v4.34.1`
([leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)), as pinned in
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. Mathlib is the only dependency.

```bash
lake exe cache get
lake build
```

`lake build` builds the root module `GMTFoundations`, which imports every module of the library.
`lake build GMTFoundationsComparator` builds the API smoke-test target
(`GMTFoundations/Comparator.lean`).

The workflow `.github/workflows/ci.yml` runs on every push and pull request. It fetches the Mathlib
cache and builds the library, treating warnings as errors; builds the smoke-test target; scans the
library sources (comments and strings masked) for `sorry`, `admit`, `axiom` and `native_decide`;
checks that no source file reaches 1000 lines and that every file is a Lean module; validates
`formalization.yaml`, resolves its Lean names and checks that each headline theorem depends on
exactly `propext`, `Classical.choice`, `Quot.sound`; and elaborates every challenge workspace.

## Formalization metadata and comparator challenges

`formalization.yaml` records the nine headline theorems (Lean names, files, sources and
plain-language statements), the pinned toolchain, the expected axioms, the AI-assistance
disclosure and the comparator challenge inventory.

`challenges/` contains three standalone [Comparator](https://github.com/leanprover/comparator)
workspaces covering the nine theorems. In each, `Statement.lean` imports Mathlib only and states
the theorems with every notion defined inline, `Challenge.lean` states them with `sorry`, and
`Solution.lean` proves them from the library. Ordinary CI only elaborates these files. Exact
statement equality and the permitted-axiom check are established by the release workflow
`.github/workflows/release-comparator.yml`, which runs Comparator with pinned tool revisions and
uploads an attestation. See `challenges/README.md`, which also records a review of the challenges.

## Layout

- `GMTFoundations/Defs/`: the vocabulary (Euclidean space, normalized Hausdorff and sphere
  measures, divergence and test fields, Gauss–Green pairs, reduced and essential boundaries,
  rectifiability, Jones numbers, weak gradients, total variation).
- `GMTFoundations/Statements/`: the headline statements as named `Prop`s.
- `GMTFoundations/Sobolev/`: Sobolev and `Lᵖ` tools, local Rellich compactness, and the Rellich
  theorem with trace.
- `GMTFoundations/Reifenberg/`: β-numbers, the Reifenberg construction, and the discrete and
  rectifiable Reifenberg theorems.
- `GMTFoundations/Perimeter/`: Gauss–Green pairs, density estimates, blow-ups, the structure
  theorem, and Federer's criterion.
- `GMTFoundations/GMT/`: Hausdorff measure, the isodiametric inequality, the sphere measure,
  densities and rectifiable sets.
- `GMTFoundations/BV/`: BV compactness and lower semicontinuity of total variation.
- `GMTFoundations/DeGiorgi/`: Caccioppoli inequalities and De Giorgi iteration.
- `GMTFoundations/Measure/`, `GMTFoundations/Common/`: Lusin's theorem; divergence as a sum of
  partial derivatives.
- `GMTFoundations/Vendor/Isoperimetric/`: vendored Brunn–Minkowski and Prékopa–Leindler
  inequalities.
- `GMTFoundations/Comparator.lean`: the API smoke-test target.
- `challenges/`: comparator challenge workspaces.
- `scripts/`: the manifest, integrity, challenge and release-comparator checks used by CI.

## Credits

The mathematics follows Evans–Gariepy (revised edition, CRC Press, 2015) for the structure theory
of sets of finite perimeter and for Sobolev compactness; Naber–Valtorta, Ann. of Math. (2) 185
(2017), 131–227, for the Reifenberg theorems; and M. Miśkiewicz, *Discrete Reifenberg-type
theorem*, Ann. Acad. Sci. Fenn. Math. 43 (2018) (arXiv:1612.02461), for the proof of the discrete
Reifenberg theorem. The measure-theoretic boundary and the criterion for finite perimeter go back
to H. Federer, *Geometric Measure Theory*, Springer, 1969.

Some files contain code adapted from other Apache-2.0 Lean projects: TauCeti
(<https://github.com/TauCetiProject/TauCeti>), EllipticPDE
(<https://github.com/alejandro-soto-franco/EllipticPDE>) and hojonathanho/isoperimetric
(<https://github.com/hojonathanho/isoperimetric>). Each such file keeps the upstream copyright
line and has a `## Provenance` section; `THIRD_PARTY_NOTICES.md` lists them.

The Lean proofs were written by AI coding agents (Claude, by Anthropic) under the author's
mathematical direction and review. The theorem statements and proof routes were reviewed by the
author. Correctness rests on Lean's kernel check, together with the comparator challenges in
`challenges/`.

## License

Apache License 2.0; see `LICENSE`.

## Citation

If you use this formalization, please cite it using the metadata in `CITATION.cff`.
