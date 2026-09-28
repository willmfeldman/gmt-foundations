# Comparator challenges

This directory contains standalone [Comparator](https://github.com/leanprover/comparator)
workspaces for the nine headline theorems of `GMTFoundations`. Comparator checks that a solution
proves exactly the statement of a trusted challenge, passes the kernel, and uses only permitted
axioms.

Every workspace has:

- `Statement.lean`: the trusted mathematical claims, importing Mathlib only. Every notion the
  claims use (normalized Hausdorff measure, divergence, test fields, Gauss–Green pairs, reduced
  and essential boundaries, Jones numbers, rectifiability, ...) is defined in this file from
  Mathlib, so a reader can check the meaning of each claim without reading the library;
- `Challenge.lean`: the trusted wrapper, importing `Statement` only and stating each claim with
  `sorry`;
- `Solution.lean`: the untrusted proof, importing `Statement` and `GMTFoundations` and proving
  the same theorems from the library;
- `config.json`: the theorem names and the permitted axioms `propext`, `Quot.sound`,
  `Classical.choice`; and
- `lakefile.toml`: a Lake workspace whose default targets are the trusted modules `Statement`
  and `Challenge` only.

The trusted files are `Statement.lean`, `Challenge.lean`, `config.json` and `lakefile.toml`.
`Solution.lean` is not trusted. Keeping the claims in `Statement.lean` gives both wrappers one
statement surface; Comparator is still the authority on statement equality.

| Workspace | Challenge theorems | Library theorems |
|---|---|---|
| `rellich-trace` | `challenge_rellich_trace` | `GMTFoundations.rellich_trace_weak_compactness` |
| `reifenberg` | `challenge_discrete_reifenberg`, `challenge_rectifiable_reifenberg` | `GMTFoundations.discrete_reifenberg`, `GMTFoundations.rectifiable_reifenberg` |
| `perimeter-structure` | `challenge_gauss_green_pair_of_divergence_bound`, `challenge_gauss_green_pair_of_locally_finite_perimeter`, `challenge_half_space_blow_up`, `challenge_rectifiable_essential_boundary`, `challenge_perimeter_measure_eq_hausdorff`, `challenge_trivial_of_null_essential_boundary` | `GMTFoundations.exists_isGaussGreenPair_of_integral_divergence_le`, `GMTFoundations.hasLocallyFinitePerimeter_of_local`, `GMTFoundations.hasDensity_symmDiff_halfSpace`, `GMTFoundations.HasLocallyFinitePerimeter.rectifiable_essentialBoundary`, `GMTFoundations.IsGaussGreenPair.eq_hausdorffN_restrict`, `GMTFoundations.ae_trivial_of_hausdorffN_essentialBoundary_inter_ball` |

The theorems are grouped by subject so that each vocabulary (Sobolev, Reifenberg, perimeter) is
defined once. `formalization.yaml` lists the nine targets and their challenge theorems.

## What ordinary CI establishes

`.github/workflows/ci.yml` builds `Statement`, `Challenge` and `Solution` in every workspace on
every push and pull request. This catches syntax, elaboration and missing-proof regressions only.
It does not check that the challenge and the solution state the same theorems: exact statement
equality and the permitted-axiom check are established only by the release comparator workflow.

The in-library target `GMTFoundationsComparator` (`GMTFoundations/Comparator.lean`) is an API
smoke test: it checks that the root import exposes the nine theorems. It imports the library, so
it is not a comparator challenge.

## Development path

In a trusted checkout, after `lake exe cache get && lake build` at the repository root:

```sh
cd challenges/<workspace>
lake build Statement Challenge Solution
```

Every workspace sets `packagesDir = "../../.lake/packages"`, so it shares the root workspace's
dependency checkouts and builds; its `lake-manifest.json` locks the same revisions as the root
manifest.

## Release verification path

The release gate is `.github/workflows/release-comparator.yml` (manual `workflow_dispatch`), on a
fresh GitHub-hosted Linux runner (`ubuntu-latest`). It:

1. checks out the exact release commit;
2. fetches the Mathlib cache and builds the trusted library;
3. validates the challenge inventory against `formalization.yaml`
   (`scripts/check-formalization-manifest.rb --metadata-only`);
4. installs the pinned tools (`scripts/release-comparator.sh install`);
5. builds only the trusted `Challenge` target of each workspace, outside the sandbox (Comparator's
   sandbox cannot write the shared dependency folder);
6. runs Comparator on every `challenges/*/config.json` (`scripts/release-comparator.sh run`),
   failing on any statement mismatch or unpermitted axiom; and
7. uploads the attestation artifact `comparator-attestation-<commit>`.

Do not run `lake build Solution`, or otherwise compile `Solution.lean`, in the release workspace
before Comparator has processed it. This ordering follows Comparator's documented threat model.

Pinned release tools:

- Lean and Mathlib: `v4.30.0` (Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`);
- Comparator: `d03acab154d269c06e60e4de7e4cc85deebff94b`;
- `lean4export`: `a3e35a584f59b390667db7269cd37fca8575e4bf`, built with this repository's
  `lean-toolchain`; and
- `landrun`: `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f`.

Comparator runs under `landrun` without the additional `systemd-run` containment that upstream
recommends for a full adversarial guarantee. A passing run establishes Comparator's statement,
kernel and permitted-axiom checks, not that stronger sandbox claim.

The attestation artifact contains `attestation.json` (tested commit and tree SHA, Lean and
Mathlib revisions, the three tool revisions, and each configuration with its result and axiom
check) and the complete per-configuration logs. Before a version tag, dispatch the workflow on
the exact release commit, require it to pass, and attach the artifact to the GitHub release.

## Acceptance record

No Comparator run has been recorded yet. The first release run will be summarized here (date,
commit, tool revisions, per-workspace result).

Local checks at the time of writing: all three workspaces build `Statement`, `Challenge` and
`Solution`, and `#print axioms` on every solution theorem gives exactly `propext`,
`Classical.choice` and `Quot.sound`.

## Review against the challenge-design checklist

Each workspace was reviewed for the usual ways in which a challenge can certify less than it
advertises.

**Trusted surface.** `Statement.lean` imports Mathlib only and `Challenge.lean` imports
`Statement` only (CI checks both). The claims are stated with Mathlib's integrals, `gradient`,
`fderiv`, `MemLp`, Hausdorff measure, `Measure.toSphere` and `LipschitzWith`; the few derived
notions are short definitions in the same file.

**No tautologies.** Each claim uses standard notions built from Mathlib, not a repackaging of an
interface invented by the library. The solutions are short because the library states its
theorems in the same vocabulary; the proofs are in the library.

**No packaged hypotheses.** Every hypothesis is a condition of the source theorem, written out in
the file. In `perimeter-structure`, "locally finite perimeter" is the distributional bound
`|∫_E div φ| ≤ C sup|φ|` near each point, which is implied by the `BV_loc` definition of
Evans–Gariepy. It is not the existence of a Gauss–Green pair (the library's definition), so the
rectifiability claim also exercises the structure theorem. The claims about a Gauss–Green pair
`(μ, ν)` assume the defining properties of the perimeter measure and the outer normal, as the
source statements do.

**Degenerate parameters.** The dimension is constrained (`n ≥ 1` for `rellich-trace`, `n ≥ 2`
otherwise). The constants and objects in the conclusions (`δ > 0`, `D`, the subsequence, the
limits, the pair `(μ, ν)`) are existentially quantified with the required properties, not left
free. The Bochner integrals in the hypotheses and conclusions are of integrable functions
(Lipschitz or compactly supported smooth data, `L²` functions, finite measures on balls), so no
condition holds only because Lean assigns the value `0` to a non-integrable integral.

**Variants stated honestly.** Where the formal statement differs from the textbook one, the
difference is in the statement's docstring and in `formalization.yaml`:

- `rellich-trace` asserts convergence of the boundary values to some `F_tr ∈ L²(∂B₁)`; it does
  not assert that `F_tr` is the trace of `F`.
- `reifenberg` is the codimension-one case with the mass threshold of Naber–Valtorta set to `0`,
  and the discrete theorem is for finite collections of balls. The rectifiable theorem gives
  rectifiability only, under an added upper density bound, with `δ` depending on that bound.
- `perimeter-structure` is stated for `n ≥ 2`, open sets `Ω ⊆ ℝⁿ` and open balls. The null case
  of Federer's criterion is localized to a ball.

**Coverage.** All nine targets are covered, one challenge theorem each. The two Gauss–Green
existence claims overlap; the global one adds the mass bound `μ(U) ≤ C`.

**Not covered.** There are no model-case or non-vacuity challenges (for example a half-space or a
ball as a set of locally finite perimeter, with its Gauss–Green pair). Such an instance would
guard against a hypothesis that no interesting object satisfies.
