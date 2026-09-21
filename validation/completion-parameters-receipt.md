# Completion parameters: local proof receipt

Source: `formalization/OneAndAHalfJohnson/CompletionParameters.lean`.
SHA-256: `fe6e95891b5d20beac9f9b848c3bdda870bf3b2866e38413a12217926f46907f`.

The source, followed by explicit `#print axioms` commands for the ten roots below, was copied to `/tmp/one_half_asymptotic_completion_audit.lean` and checked from `formalization` with:

```sh
/Users/jthaler/.elan/bin/lake env lean /tmp/one_half_asymptotic_completion_audit.lean
```

Result: exit 0, no warnings or errors. This is an individual source/kernel check, not a replacement for the integrator's whole-project declaration inventory and build.

Checked roots in namespace `OneAndAHalfJohnson`:

- `completion_cardinality_of_defect_power`
- `exists_completion_defect_eq_min`
- `exists_completion_defect_le`
- `rate_eq_one_sub_distance_add_defect`
- `rate_error_le_of_defect_le`
- `concrete_completion_defect_power`
- `asymptoticCompletionDefect_exponent`
- `asymptoticCompletionDefect_power`
- `asymptoticCompletionDefect_rate_bound`
- `exists_completion_rate_error_le_six_div`

The first root reports only `propext` and `Quot.sound`; every other listed root reports only `propext`, `Classical.choice`, and `Quot.sound`. No custom axioms or admissions occur.

Mathematical scope: the actual-code completion theorem retains the initial minimum distance, both strict absolute word-distance bounds, and supercode inclusion. For alphabet cardinality `p^s` with `p≥2` and length `N≥s≥1`, it guarantees rate error at most `6/s`. The integer defect choice `(N+3)/s+1` replaces the paper's logarithmic choice without changing the claimed uniform asymptotic conclusion. The initial code, its nonzero witness, word separation, and `b<d` must still be furnished by the base/amplification constructions. No main existence theorem is asserted by this receipt.

This receipt is written by the proof author. Independent mathematical review and centralized validation remain separate tasks.
