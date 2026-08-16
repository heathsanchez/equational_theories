# Rigorous Lean Flywheel v1

## Question
Can natural Lean repairs be converted into reusable capability capital so that later proof acquisition pays less repeated search cost and exposes the next abstraction automatically?

## Frozen historical sequence

- Base fork commit: `b1cc1756202d7f44e07bd4069b5df16901a36938`.
- Natural episode E1: upstream PR #1467, Law46, merged 2026-08-13.
- Natural episode E2: upstream PR #1461, Law43, merged 2026-08-14.

The ordering is historical. E2 is not treated as caused by E1.

## O1 — evaluation on support

Both accepted repairs require the same structural fact:

> Evaluation of a `FreeMagma` depends only on values assigned to variables that occur in the term.

E1 introduced this as `FreeMagma.evalInMagma_congr` inside `Definability/Law46.lean`.
E2 independently rebuilt the same recursive induction locally as `eval_eq_on_mem`.

Intervention: `equational_theories/FreeMagmaEvalCongr.lean`.

Evidence:
- repeated mechanism: OBSERVED;
- source-level later-search compression on Law43: CANDIDATE;
- kernel/build verdict: PENDING;
- compounding: NOT CLAIMED.

## O2 — FreeMagma evaluator to term-definability

Residual exposed after O1: Law43 and Law46 still hand-built the bridge from a `FreeMagma` expression to a first-order `Set.TermDefinable` witness. Tarski543 contained a third independent instance.

Intervention: `equational_theories/Definability/FreeMagmaTerm.lean`.

Capability:

> Any `FreeMagma (Fin 2)` evaluator is automatically term-definable in the underlying magma language.

Candidate consumers: Law43, Law46, Tarski543.

Evidence:
- repeated semantic mechanism across three sites: OBSERVED;
- cross-site source-level reuse: CANDIDATE PASS;
- first-order witness boilerplate compression: PASS at source level;
- kernel/build verdict: PENDING;
- natural developmental dependence: NOT TESTED.

## O3 — mapped-variable term-definability

Residual exposed after O2: Law43 and Law46 still separately mapped source variables into binary arguments before invoking O2.

Derived capability: `FreeMagma.eval_comp_termDefinable`.

> For any `t : FreeMagma α` and `σ : α → Fin 2`, the evaluator `v ↦ t ⬝ (v ∘ σ)` is term-definable.

O3 is obtained by composing `fmapHom`, O2, and `evalInMagma_fmapHom`; Law43 and Law46 now invoke O3 directly.

Verdict: `CANDIDATE_RECURSIVE_ACQUISITION_COST_REDUCTION_O2_TO_O3`.

The reason is structural: before O2, O3 would require another first-order witness proof; after O2, it is a small composition of existing capital.

## Live source-distinct target: open issue #499

The next target was deliberately moved outside the definability repair family: upstream open issue #499 asks whether the use of choice in the completeness proof can be removed.

The existing proof uses `PhiAsSubst_aux` to lift an entire arbitrary quotient-valued valuation `φ : β → FreeMagmaWithLaws γ Γ` to representatives `σ : β → FreeMagma γ` using `Classical.axiomOfChoice`.

Residual classification after inspection:

`REPRESENTATION / SCOPE FAILURE`, not search failure.

The law being checked only evaluates finitely many variables, but the proof asks for representatives of every variable in the valuation. This is a global-state lift for a finite-support observation.

That distinction is exactly what O1 records.

## O4 — finite-support quotient lifting

New candidate file:

`equational_theories/CompletenessFiniteSupport.lean`

Main ingredients:

1. `PhiAsSubst_onLawSupport`: for a single law with decidable variable equality, collect only the variables in `lhs.elems ∪ rhs.elems`, choose representatives for that finite list using repeated `Quotient.exists_rep`, and use one obtained representative as the default outside support.
2. `FreeMagmaWithLaws.isModel_decidableVars`: use O1 (`evalInMagma_congr`) to replace the original quotient valuation by the finite-support substitution only where each side of the law can observe it.
3. `Completeness'_decidableVars`: Type-0 completeness for contexts whose variable language has `DecidableEq`, without invoking the global `PhiAsSubst` step.
4. `Completeness_decidableVars` and `CompletenessNat_noGlobalChoice`: same-language and project-standard Nat specializations.

## Why O4 matters to the flywheel

This is the first source-distinct transfer where accumulated capability materially changes problem formulation:

`O1 support law` → notice global valuation lifting is unnecessary → replace infinite/global choice-shaped obligation with finite support lifting → candidate solution to a live open metatheorem problem under a scoped assumption.

Without O1, the obvious route is to keep trying to construct the global representative function. With O1 installed, values outside support are formally irrelevant and can be forgotten.

Candidate verdict:

`CANDIDATE_SOURCE_DISTINCT_TRANSFER_O1_TO_COMPLETENESS`

`CANDIDATE_O4_FINITE_SUPPORT_QUOTIENT_LIFT`

This still does NOT close issue #499 in full generality: the new result assumes decidable equality on the context variable type and currently targets Type-0 completeness. The fully general quotient formulation may genuinely retain a choice-shaped obstruction; that has not been proved impossible.

## Infrastructure residual

GitHub reports zero Actions runs for the experiment branch. The available integration receives HTTP 403 when querying repository Actions permissions. Therefore the absence of CI is classified strictly as infrastructure/verification unavailable, not as semantic success or failure.

No O1/O2/O3/O4 theorem is ADMITTED until Lean kernel/build validation is obtained.

## Required next separators

1. Kernel/build the experiment branch, especially:
   - `FreeMagmaEvalCongr.lean`;
   - `Definability/FreeMagmaTerm.lean`;
   - Law43 / Law46 / Tarski543 consumers;
   - `CompletenessFiniteSupport.lean`.
2. Run an axiom audit on `Completeness'_decidableVars` / `Completeness_decidableVars` to determine whether `Classical.choice` is absent from the transitive theorem dependencies.
3. If O4 survives, compare cold versus O1-enabled acquisition on the frozen #499 target or a matched synthetic reconstruction where the solution text is hidden.
4. Only after that test a new natural problem with O1–O4 installed.

## Current verdicts

`RETAIN_CANDIDATE_O1_SUPPORT_CONGRUENCE`

`RETAIN_CANDIDATE_O2_FREEMAGMA_TERM_BRIDGE`

`RETAIN_CANDIDATE_O3_MAPPED_TERM_BRIDGE`

`CANDIDATE_RECURSIVE_ACQUISITION_COST_REDUCTION_O2_TO_O3`

`CANDIDATE_SOURCE_DISTINCT_TRANSFER_O1_TO_COMPLETENESS`

`RETAIN_CANDIDATE_O4_FINITE_SUPPORT_QUOTIENT_LIFT`

No frontier-expansion or natural compounding claim is licensed yet.
