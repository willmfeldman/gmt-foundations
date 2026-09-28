# Third-party code

This project is released under the Apache License 2.0 (`LICENSE`). A few files contain code adapted
from other Apache-2.0 Lean projects. Each of those files keeps the upstream copyright holder on its
header's copyright line, and its module docstring has a `## Provenance` section that names the
upstream file and commit, lists the declarations taken, and says what was changed (Apache-2.0
§4(b)). None of the upstream projects ships a `NOTICE` file.

| Upstream | Commit | License | Upstream copyright | Files here |
|---|---|---|---|---|
| TauCeti, https://github.com/TauCetiProject/TauCeti | `91f66a0514e6523efdccddb9e35fb82c96dd6405` | Apache-2.0 | © 2026 The Tau Ceti contributors | `GMTFoundations/Sobolev/BallAverage.lean` (adapted from `TauCeti/MeasureTheory/Function/Lp/BallAverage.lean`), `GMTFoundations/Sobolev/FrechetKolmogorovCompact.lean` (adapted from `TauCeti/MeasureTheory/Function/Lp/FrechetKolmogorov.lean`), `GMTFoundations/Sobolev/PolarCoord.lean` (adapted from `TauCeti/MeasureTheory/Constructions/HaarToSphere.lean`) |
| EllipticPDE, https://github.com/alejandro-soto-franco/EllipticPDE | `eaf821d31b200bb6ea235f19eecc50cf0f38c294` | Apache-2.0 | © 2026 Alejandro Soto Franco | `GMTFoundations/Sobolev/Mollify.lean` (adapted from `lean/EllipticPdes/Embedding/Convolution.lean` and `lean/EllipticPdes/Embedding/Morrey.lean`), `GMTFoundations/Sobolev/Lattice.lean` (adapted from `lean/EllipticPdes/Embedding/ChainRule.lean`) |
| isoperimetric, https://github.com/hojonathanho/isoperimetric | `29768f8beeaf17295cdf3853d37da35d7e2b0a5f` | Apache-2.0 | © 2025 Jonathan Ho | `GMTFoundations/Vendor/Isoperimetric/Basic.lean`, `GMTFoundations/Vendor/Isoperimetric/PrekopaLeindler.lean`, `GMTFoundations/Vendor/Isoperimetric/BrunnMinkowski.lean` (vendored whole, from `Isoperimetric/*.lean`); the upstream license text and notes are in `GMTFoundations/Vendor/Isoperimetric/LICENSE-NOTICE.md` |

The upstream isoperimetric repository has no per-file copyright headers and leaves the copyright
line of its LICENSE appendix unfilled; the holder above is taken from its README and git history.

Everything else is original to this project. Mathlib is used as a Lake dependency (a normal
library; no code copied).
