# One-and-a-half Johnson bound — local Lean formalization

**All numbered results are covered under the agreed conditional scope.**

This project formalizes Kominers, Thaler, and Zheng,
[*The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes*](https://eprint.iacr.org/2026/1894).
The downloaded source is pinned in [paper/source.json](paper/source.json).
The repository is public at https://github.com/GUJustin/one_and_a_half_johnson.
Validation runs locally; no CI workflow is configured.

The agreed initial scope permits two external premises:

- Adriaensen–Denaux's low-weight incidence-code classification.
- Hamada's binary incidence-rank formula, specialized to PG(4,512).

Their concrete Lean propositions are in
[Targets/External.lean](formalization/OneAndAHalfJohnson/Targets/External.lean).
They are explicit theorem arguments, not custom axioms. Supporting proofs discharge all other hypotheses needed for the numbered conclusions. Some internal arguments differ from the paper; see [PROOF_NOTES.md](PROOF_NOTES.md).

Completed numbered results: Theorems 1.1/3.1, Corollary 1.2, Lemma 3.2,
and Lemma 3.4 conditional on AD21, and Lemma 3.5 unconditionally. Theorem 3.3
is the accepted AD21 external input. Theorem 4.1 is proved conditional on AD21 and Hamada in [MainTheorems/Concrete.lean](formalization/OneAndAHalfJohnson/MainTheorems/Concrete.lean).

[RESULTS.md](RESULTS.md) maps every numbered result to its Lean declaration.

## Status and navigation

[ROADMAP.md](ROADMAP.md) is the execution plan and coverage ledger.
[PAPER_AUDIT.md](PAPER_AUDIT.md) inventories all eight numbered statements and
substantial supporting claims. [REVIEW.md](REVIEW.md) records independent reviews.

The verified library includes actual projective incidence coordinates and counts,
incidence independence, scalar extension and shortening, dimension preservation,
syndrome normalization and counting, dense subfield-line extraction, deterministic
amplification consequences, radius comparisons, and exact concrete arithmetic.
Intermediate statements retain clearly documented mathematical hypotheses.

[Targets/Main.lean](formalization/OneAndAHalfJohnson/Targets/Main.lean),
[Targets/Base.lean](formalization/OneAndAHalfJohnson/Targets/Base.lean), and
[Targets/Conditional.lean](formalization/OneAndAHalfJohnson/Targets/Conditional.lean)
contain concrete quantitative proof obligations. Compiling these definitions
is **not** a proof of the requested existence theorems. The proved
`uniqueDecoding_of_main` is a reduction; the completed conditional main
and corollary proofs are in [MainTheorems/Main.lean](formalization/OneAndAHalfJohnson/MainTheorems/Main.lean).

## Build and trust checks

Install elan, then run from this directory:

```sh
python3 scripts/check_axioms.py
```

Latest validation: **72 modules built; all 485 named declarations passed the standard-axiom audit.** All 20 dependency checkouts match their pins and have no tracked changes. The checker controls also confirm that `sorryAx` and missing audit output are rejected.

The script runs local Lake builds and audits every explicitly named project
definition and theorem. Receipts are in [validation/axioms.json](validation/axioms.json)
and [validation/lean.log](validation/lean.log). The receipt includes source hashes,
all dependency pins, and each declaration's transitive axioms. An imported ArkLib
module currently emits an admission warning; the project endpoints are separately
checked and must not depend on that admission.

For a quick ordinary library build:

```sh
cd formalization
LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true lake build
```

Toolchain: Lean 4.34.0. ArkLib revision:
`fa14552d40e793f2ea26e65c440306aae0c08a26`.
All dependencies have remote pinned specifications; the local package cache was
initialized by a separate copy of already available packages. Builds do not write
to the binary-fields project. The cache is excluded from version control.
