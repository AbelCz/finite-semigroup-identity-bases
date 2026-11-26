# Finite identity bases for finite semigroups

Ábel Czupor, with Codex assistance. Independent human review is pending.

[Project page and manuscript](https://czupor.me/research/finite-semigroup-identity-bases/) · [Zenodo preprint and DOI](https://doi.org/10.5281/zenodo.24567351) · [License scope](LICENSES.md)

This package contains the Lean sources for a negative answer to the finite identity basis decision problem for finite semigroup multiplication tables. The final statement quantifies over partial recursive Boolean procedures on numeric matrices. It requires termination and a correct answer on every nonempty finite associative multiplication table. A finite basis consists of equations in terms built solely from variables and binary multiplication.

The endpoint is `finite_semigroup_finite_basis_undecidable` in `Proof/Problem455Undecidability.lean`. This module also proves the primitive-recursive table construction, its isomorphism to the monoid in the reduction, the blank-tape halting equivalence, and the existence of a single finite machine that writes the presentation.

## Reproduce the build

Use Python 3.10 or newer, Git and Lean 4.19.0. The included `lean-toolchain` selects the Lean release when using elan. The required mathlib4 revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Its transitive dependency revisions are recorded in `mathlib-lake-manifest.json`.

Run these commands from the extracted source directory. They use a fresh sibling directory for mathlib.

```sh
git clone https://github.com/leanprover-community/mathlib4.git ../mathlib4
git -C ../mathlib4 checkout --detach c44e0c8ee63ca166450922a373c7409c5d26b00b
(cd ../mathlib4 && lake exe cache get)
python3 check.py --mathlib ../mathlib4
```

An existing built checkout at that revision can be supplied directly. If the prebuilt cache is unavailable, run `lake build Mathlib` from the pinned mathlib directory. The checker accepts the Lean executable through `LEAN`. Use `--jobs 1` if memory is limited.

The checker verifies the file hashes, toolchain version, mathlib lock file and all dependency revisions. Each invocation compiles all 235 project modules in a new temporary directory with warnings as errors. It then loads the results with Lean's `--trust=0` option and checks the transitive axioms of all 4,446 theorem declarations in those modules. It expects exactly `propext`, `Classical.choice` and `Quot.sound`. The expanded matrix formulation and the restriction to monoid inputs are rechecked separately. The small executable examples exercise encoding conventions and table validation.

## Package contents

- `Proof/` contains the complete project modules, retaining their original Lean import names.
- `checks/` contains the kernel audit, two additional formulations and executable examples.
- `check.py` runs the build and verification using Python's standard library.
- `lean-toolchain` and `mathlib-lake-manifest.json` identify the toolchain and dependencies.
- `SHA256SUMS` gives SHA-256 for every other file, relative to this directory.
