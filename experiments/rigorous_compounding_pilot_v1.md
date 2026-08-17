# Rigorous Compounding Benchmark — Pilot v1

## Purpose
Prospectively test whether the accumulated verified controller/lawbook can acquire a source-distinct historical Lean repair without consulting the accepted patch, while preserving a failure/infrastructure record.

This pilot validates benchmark mechanics and gives a capitalized acquisition datapoint. It is **not** a causal Cold-vs-Memory-vs-Capitalized result because all reasoning in this chat is produced by one model instance that already knows the accumulated controller. A proper three-arm comparison requires independent model instances/sessions.

## Frozen task
Historical upstream PR: teorth/equational_theories#1162, `Fix : 1729 sorries from Eq 1729 Equiv usage`.

Frozen pre-merge base commit:
`3508ec064d070ddac9c82abdfe1f733122972948`

Changed historical file:
`equational_theories/ManuallyProved/Equation1729/SmallMagma.lean`

The accepted PR patch was not opened until after the capitalized branch passed.

The frozen source contained eight holes in the `ExtOpsWithProps` construction inside `reduce_to_new_axioms`:
- `L`
- `R`
- `left_map_SM`
- `right_map_SM`
- `axiom_1`
- `axiom_3`
- `axiom_6`
- `axiom_7`

## Arms frozen
All from the same base commit:
- `bench/1162-cold`
- `bench/1162-memory`
- `bench/1162-capital`

Cold and Memory-only arms were intentionally not scored in this chat after recognizing same-model contamination.

## Scoring discipline
Count semantic acquisition attempts only after:
1. the historical dependency manifest is preserved;
2. the benchmark wrapper itself elaborates sufficiently to reach target proof obligations.

Exclude:
- dependency/provisioning failures;
- environment migration distortions;
- wrapper-only namespace/typeclass mistakes.

Count a semantic failed branch when Lean reaches the reconstructed theorem and rejects a proposed target proof.

## Infrastructure residual discovered
The first workflow used `lake update`, which updated the historical 2025 checkout to current dependencies and caused unrelated Mathlib/API failures before the target theorem. Verdict: `INFRASTRUCTURE_DISTORTION`, excluded from semantic score.

Verifier was corrected to use the historical manifest and `lake exe cache get` without `lake update`.

A later `Magma SM` synthesis failure came from the benchmark wrapper omitting the source file's `open AddToMagma`; verdict: `WRAPPER_PLUMBING`, excluded.

## Capitalized acquisition
The controller first inspected the target structure and existing local lemmas rather than searching broadly.

Initial decomposition:
- reuse existing `L`/`R` equivalences;
- discharge `left_map_SM`/`right_map_SM` definitionally;
- reuse `h_iii'` for `axiom_3`;
- reuse `h_vi'` for `axiom_6`;
- transform `h_vii'` directly into `axiom_7`;
- isolate `axiom_1` as the only nontrivial algebraic residual.

### Semantic attempt 1
Lean reached the target theorem. Only `axiom_1` failed; the other seven reconstructed holes survived elaboration.

Residual: function-level proof supplied where `axiom_1` demanded pointwise equality.

### Semantic attempt 2
Converted `axiom_1` to a pointwise proof using the already-existing law
`axiom_i' : L₀' ∘ L₀' = (R' 0).symm`.

Failure remained localized to `axiom_1`: incorrect cancellation/orientation introduced an extra `(R' a).symm` layer.

### Semantic attempt 3
Split the inner identity explicitly:
`(R' 0).symm (L₀' (R' 0 v)) = L₀' v`, derived by two applications of `axiom_i'`, then transported that equality through `(R' a).symm`.

Result: **PASS** under the frozen historical Lean/Mathlib environment.

## Pilot score
Capitalized arm:
- target solved: YES
- semantic attempts: 3
- semantic failures: 2
- distinct semantic residuals after initial decomposition: 1 (`axiom_1`)
- broad representation changes: 0
- hidden accepted patch consulted during acquisition: NO

Historical accepted PR metadata:
- commits: 3
- changed files: 1
- additions: 36
- deletions: 16

These historical commit counts are contextual only, not a matched search-cost baseline.

## Post-hoc patch comparison
Only after the capitalized branch passed, the accepted patch was opened.

The accepted proof and the independent capitalized proof converge on the same high-level decomposition:
- use the pre-existing `L` and `R`;
- prove left/right map fields by simplification;
- reduce axioms 3, 6, and 7 to their supplied hypotheses;
- isolate `axiom_1` as the only nontrivial local algebraic proof.

The `axiom_1` proof is not the same proof: the accepted patch uses `L₀'_R'0_L₀'_eq_id` plus a locally named `y`; the capitalized proof derives the needed inner equality directly from two applications of `axiom_i'` and transports it through `(R' a).symm`.

## Verdict
`PILOT_MECHANICS_VALIDATED`

`PROSPECTIVE_CAPITALIZED_SOURCE_DISTINCT_ACQUISITION_PASS`

Not established by this pilot:
- causal advantage over a cold model;
- advantage over solved-result memory alone;
- sequentially increasing returns;
- general compounding.

## Next deciding experiment
Run the frozen three-arm protocol with independent model instances/sessions on multiple source-distinct Lean tasks. Keep the exact same task ordering and verifier environment across arms. The decisive evidence is a lower acquisition-cost trajectory for the Capitalized arm, especially if the advantage grows across sequential episodes and disappears under controller/lawbook ablation.
