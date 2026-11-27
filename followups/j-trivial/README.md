# Finite identity bases for finite J-trivial monoids

Ábel Czupor, with AI assistance. Lean-checked follow-up to the [finite semigroup candidate](https://doi.org/10.5281/zenodo.24567351). Independent mathematical review and priority are pending. This note leaves the original release unchanged.

**Result.** No partial recursive Boolean procedure can halt and correctly decide finite basedness on every multiplication table presenting a finite J-trivial monoid. The identities use variables and multiplication only, with no identity constant, inverse, or involution symbol. J-triviality means that two elements generating the same principal two-sided ideal must be equal.

**What changes.** The earlier reduction constructs a direct product of bounded word quotients. Every nonzero class in a factor has a well-defined word length, because every allowed move preserves all letter counts. If a product stays nonzero, its length is the sum of the input lengths. If two nonzero classes divide each other on both sides, their lengths agree and the surrounding factors have length zero. This forces the classes to agree. Zero forms a singleton class too. Coordinatewise application gives J-triviality of the product; the checked table representation transfers it to multiplication tables. A primitive-recursive test restricts arbitrary machine inputs to the promise and leaves the diagonal instances unchanged.

**Scope.** This is a restriction of the existing reduction, not an independent proof of the original undecidability result. It does not resolve Sapir's narrower question about plain word-factor monoids, where distinct surviving words are not identified. See [Volkov, Problems 2.1 and 4.1](https://csseminar.kmath.ru/MATHJAP_revisited.pdf).

## Replay

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b` as documented in the repository README. From the repository root:

```sh
python3 followups/j-trivial/check.py --mathlib /path/to/mathlib4
```

The script verifies the original source manifest, rebuilds the original modules, checks the follow-up with `--trust=0` and warnings treated as errors, and audits the final theorem’s transitive axioms. The final declaration is `JTrivialFollowup.finite_j_trivial_monoid_finite_basis_undecidable` in `RestrictedDecision.lean`. `JTrivialExamples.lean` checks three positive and two negative examples for the promise test.

The Lean additions are MIT-licensed, consistent with the original project. No claim of priority is made.
