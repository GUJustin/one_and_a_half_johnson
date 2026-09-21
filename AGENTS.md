# Local conditional formalization

The user requests all results of ePrint 2026/1894 formalized and has authorized
a public GitHub repository and push. Do not use GitHub CI. The user and Kai
explicitly permit conditional results using exactly these two external inputs:
`Targets.AD21LowWeight` and `Targets.HamadaBinaryRank`.

Read README.md, ROADMAP.md, PAPER_AUDIT.md, and REVIEW.md before changing scope.
The paper snapshot and its source hash are in paper/. The binary-fields
project is a separate active project: do not modify its files or dependencies.

## Proof boundary

- Definitions must have complete bodies. Supporting proofs have no admissions.
- Target proposition definitions are proof obligations, not completed results.
- Only the two named external mathematical premises may remain in final
  paper-facing conditional theorems. Intermediate reductions may have ordinary
  hypotheses, but do not report them as final conditional theorem proofs.
- No custom axioms, `sorry`, `native_decide`, or weakened conclusion to close work.
- Check fixed code/word quantifiers before exceptional challenges, strict degree
  and distance inequalities, distinct counts, uniform asymptotic constants,
  finite-field embeddings, and concrete dimensions.
- Keep main theorem assemblies separate from reusable supporting mathematics.
- Use independent bounded proof agents and an independent reviewer for substantial
  changes, with disjoint file ownership. One integrator owns project builds.
- Preserve pinned dependencies. Do not update Lake just to repair a proof.

## Validation

From the project root run `python3 scripts/check_axioms.py`. It builds locally,
compiles an inventory of all named local declarations, and rejects transitive
axioms other than `propext`, `Classical.choice`, `Quot.sound`.
Keep declaration syntax compatible with the fail-closed inventory, or extend
it explicitly with validation. A successful target-definition check does not
prove the proposition true. Record exact coverage and outstanding obligations.
