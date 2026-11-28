# Tarski’s finite basis problem for finite semigroups: Lean 4.33.1 port

Ábel Czupor. This is a compatibility port of the Lean formalization accompanying the [candidate undecidability proof](https://doi.org/10.5281/zenodo.24567351) for Volkov’s Problem 2.1. It is not a new result or an independent review. The original Lean 4.19.0 release remains on the default branch.

`TarskiFiniteBasis.lean` is the single-file port. Its endpoint is
`P455Undecidability.finite_semigroup_finite_basis_undecidable`, which rules out a partial recursive Boolean procedure that terminates and decides finite basability for every nonempty finite associative multiplication table. The identities use variables and binary multiplication only.

With Git and elan installed, from this branch’s repository root run:

```sh
lake exe cache get
lake env lean --trust=0 TarskiFiniteBasis.lean
```

The project pins Lean 4.33.1 and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. If mathlib’s caches are unavailable, run `lake build TarskiFiniteBasis` first to build the prerequisites, then rerun the `--trust=0` check.

The final line of the source prints the endpoint’s axioms. The expected set is `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project-specific axioms. The port currently emits non-fatal compatibility and lint warnings.

[Original manuscript and research page](https://czupor.me/research/finite-semigroup-identity-bases/) · [Preprint DOI](https://doi.org/10.5281/zenodo.24567351)
