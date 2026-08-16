# O32 — Idempotence normalizer comparison separator

## Frozen question
After O29/O30/O31, does the compiled quotient-normalizer route extend directly from reassociation to a theory whose normalization requires detecting duplicate normalized subterms?

Target theory:

`x ◇ x = x`.

## Rival explanations

- **H32-A — normalizer route remains representation-free:** a constructive canonical normalizer exists uniformly for every codomain variable type, so O29 can supply context-wide quotient sections exactly as for associativity.
- **H32-B — computational comparison boundary:** the obvious canonicalizer must compare normalized subterms and therefore requires computational equality data on the codomain/term representation. The O29 compiler remains valid, but normalizer acquisition is now the residual.
- **H32-C — obvious normalizer is wrong/incomplete:** recursive duplicate-child collapse does not characterize the full idempotence congruence; failure should be classified as a normal-form hypothesis failure, not an equality-data failure.

## Smallest separator
1. Define the obvious recursive duplicate-child normalizer under `[DecidableEq β]`.
2. Prove every term reduces derivably to it.
3. Test whether derivability preserves that normal form.
4. If 2 passes but 3 fails, reject the proposed normal form (H32-C).
5. If both pass only under `[DecidableEq β]`, retain a scoped normalizer and name `NORMALIZER_COMPARISON_DATA` as the surviving residual; do not infer generic impossibility.
6. Do not broaden the derivation representation unless the residual survives this split.

## Scientific role
This is intentionally source-distinct from projection and associativity:
- projection: information collapse to one endpoint;
- associativity: shape quotient, ordered leaves preserved;
- idempotence: normalization potentially requires detecting equality of structured subterms.

A failure is useful if it decides which of those mechanisms is responsible.
