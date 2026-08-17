# O35 — idempotence normalizer reverse-strength separator

Status: FROZEN CANDIDATE. Do not count as evidence unless O32 first passes its kernel and axiom gates.

## Question
If the idempotence quotient admits a computational normalizer/section, what comparison principle does that data expose?

## Why this follows from O32
O32's obvious normalizer recursively normalizes both children and contracts them exactly when the normalized subtrees are equal. It is implemented under `[DecidableEq β]`. A successful O32 would establish sufficiency only; it would not establish that equality comparison is intrinsic.

## Rival explanations
R1 — `DecidableEq β` is merely an implementation convenience of this tree normalizer.

R2 — any sufficiently explicit computational normalizer/section for the free idempotent magma carries a weaker comparison resource, but not full `DecidableEq β`.

R3 — computational normalization of the idempotence quotient is already strong enough, on a small two-variable separator, to recover `DecidableEq β` or an equivalent Type-valued equality discriminator.

## Smallest separator
Work first over the two-variable fragment. Compare the quotient behavior of `Lf a ⋆ Lf b`, `Lf a`, and `Lf b` under a hypothetical explicit normalizer/section. Do not assume equality on β in the theorem statement.

The first target should remain in `Prop` if possible. Only attempt a Type-valued decision object in a separate theorem, preserving the Prop/Type distinction learned in O12/O14/O17/O18.

## Verdict discipline
- If only Prop-level equality separation follows: name that exact boundary; do not claim `DecidableEq`.
- If Type-valued `DecidableEq` follows from the computational normalizer data: classify the O32 equality requirement as reverse-strength evidence, scoped to the formalized data interface.
- If neither follows: reject the necessity story and search for a different idempotence representation before broadening.
- No result here proves generic quotient normalization requires equality in other theories.

## Method check
This experiment exists because the updated controller says: after a successful broadened construction, reverse-test whether the added resource was necessary or only sufficient. Split before broadening again.
