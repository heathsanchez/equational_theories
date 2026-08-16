# Rigorous Lean Flywheel v1

## Question
Can natural Lean repairs be converted into reusable capability capital so that later proof acquisition pays less repeated search cost and exposes the next abstraction automatically?

## Frozen historical seed

- Base fork commit: `b1cc1756202d7f44e07bd4069b5df16901a36938`.
- Natural episode E1: upstream PR #1467, Law46, merged 2026-08-13.
- Natural episode E2: upstream PR #1461, Law43, merged 2026-08-14.

The ordering is historical. E2 is not treated as caused by E1.

## O1 — evaluation on support

Both accepted repairs required the same structural fact:

> Evaluation of a `FreeMagma` depends only on values assigned to variables that occur in the term.

E1 introduced this locally as `FreeMagma.evalInMagma_congr` inside Law46. E2 independently rebuilt essentially the same recursive induction as `eval_eq_on_mem`.

Compiled intervention: `equational_theories/FreeMagmaEvalCongr.lean`.

### Verification

GitHub Actions targeted build: PASS.

Axiom audit:

`FreeMagma.evalInMagma_congr` — no axioms.

Verdict: `ADMITTED_O1_SUPPORT_CONGRUENCE` for the theorem/capability itself.

The historical counterfactual claim remains narrower: O1 would remove a repeated induction from the later Law43 proof, but this alone is not a natural compounding result.

## O2 — FreeMagma evaluator to term-definability

Residual exposed after O1: Law43 and Law46 still hand-built the bridge from a `FreeMagma` binary expression to a first-order `Set.TermDefinable` witness. Tarski543 contained a third independent instance.

Compiled intervention: `equational_theories/Definability/FreeMagmaTerm.lean`.

Capability:

> Any `FreeMagma (Fin 2)` evaluator is automatically term-definable in the underlying magma language.

Consumers on the experiment branch: Law43, Law46, Tarski543.

### Verification

Target module and all three consumer modules kernel-build: PASS.

Axiom audit:

`FreeMagma.eval_termDefinable` — `[propext, Quot.sound]`.

Verdict: `ADMITTED_O2_FREEMAGMA_TERM_BRIDGE` as a verified reusable theorem.

## O3 — mapped-variable term-definability

Residual exposed after O2: Law43 and Law46 still separately mapped source variables into binary arguments before invoking O2.

Derived capability:

`FreeMagma.eval_comp_termDefinable`.

> For any `t : FreeMagma α` and `σ : α → Fin 2`, the evaluator `v ↦ t ⬝ (v ∘ σ)` is term-definable.

O3 is obtained by composing `fmapHom`, O2, and `evalInMagma_fmapHom`; Law43 and Law46 invoke O3 directly.

### Verification

Kernel build: PASS.

Axiom audit:

`FreeMagma.eval_comp_termDefinable` — `[propext, Quot.sound]`.

Verdict: `ADMITTED_O3_MAPPED_TERM_BRIDGE` as a theorem.

Developmental interpretation remains `CANDIDATE_RECURSIVE_ACQUISITION_COST_REDUCTION_O2_TO_O3`: once O2 existed, O3 became a small composition rather than another first-order witness proof. A matched cold/ablation acquisition experiment is still required before upgrading that causal claim.

## Live source-distinct target — upstream issue #499

The experiment next moved outside the definability repair family. Upstream open issue #499 asks whether the use of choice in the completeness proof can be removed.

Baseline implementation:

`FreeMagmaWithLaws.isModel` / `Completeness'` use a global `PhiAsSubst_aux` that obtains representatives for an arbitrary quotient-valued valuation with `Classical.axiomOfChoice`.

Residual classification after applying O1:

`REPRESENTATION / SCOPE FAILURE`.

A single law only observes finitely many variables, but the baseline proof lifts representatives for every variable in the valuation. O1 licenses forgetting everything outside the term support.

## O4 — finite-support quotient lifting

File: `equational_theories/CompletenessFiniteSupport.lean`.

Components:

1. `PhiAsSubst_onLawSupport` lifts representatives only for variables occurring in `lhs` or `rhs`, using repeated `Quotient.exists_rep` on that finite list and one obtained representative as the off-support default.
2. `FreeMagmaWithLaws.isModel_decidableVars` uses O1 to replace the original quotient valuation by the finite-support substitution only where each side can observe it.
3. `Completeness'_decidableVars` gives Type-0 completeness for contexts whose variable language has `DecidableEq`.
4. `Completeness_decidableVars` gives the same-variable-language form.
5. `CompletenessNat_noGlobalChoice` gives the project-standard Nat specialization.

### Hard verification

Targeted GitHub Actions build: PASS for `CompletenessFiniteSupport`.

Baseline axiom audit:

- `FreeMagmaWithLaws.isModel` — `[propext, Classical.choice, Quot.sound]`.
- `Completeness'` — `[propext, Classical.choice, Quot.sound]`.

Finite-support axiom audit:

- `FreeMagmaWithLaws.isModel_decidableVars` — `[propext, Quot.sound]`.
- `Completeness'_decidableVars` — `[propext, Quot.sound]`.
- `Completeness_decidableVars` — `[propext, Quot.sound]`.
- `CompletenessNat_noGlobalChoice` — `[propext, Quot.sound]`.

No `Classical.choice`. No `sorryAx`.

Verdict: `VERIFIED_SCOPED_O4_FINITE_SUPPORT_QUOTIENT_LIFT`.

This is a real source-distinct capability transfer: O1 changed the representation of a live metatheorem residual and yielded a kernel-valid theorem family with a strictly smaller axiom dependency set.

It does not yet close issue #499 in full generality. The current theorem assumes decidable equality on the context variable type and Type-0 completeness. The remaining question is whether that assumption is merely an adapter limitation or reflects a genuine constructive obstruction to producing a total substitution for arbitrary variable types.

## Verification history

A targeted workflow `.github/workflows/rigorous-lean-flywheel.yml` was added.

Run 1: failed semantically at a Law43 extensional adapter mismatch; O1 and O2 had already built.

Intervention: add the missing `apply_ite` normalization.

Run 2: all target modules built; first axiom audit showed the O4 results lacked `Classical.choice`, but O2/O3 audit names were missing their import.

Audit harness was hardened with the missing import, `pipefail`, baseline declarations, and failure checks.

Run 3 first attempt: infrastructure-only SSL reset during `lake update`.

Run 3 rerun: PASS. All targets built and the hardened baseline-vs-intervention axiom audit passed.

This sequence is itself classified correctly as residual → intervention → verifier rather than hiding failed runs.

## Current evidence levels

`ADMITTED_O1_SUPPORT_CONGRUENCE`

`ADMITTED_O2_FREEMAGMA_TERM_BRIDGE`

`ADMITTED_O3_MAPPED_TERM_BRIDGE`

`CANDIDATE_RECURSIVE_ACQUISITION_COST_REDUCTION_O2_TO_O3`

`VERIFIED_SOURCE_DISTINCT_TRANSFER_O1_TO_COMPLETENESS`

`VERIFIED_SCOPED_O4_FINITE_SUPPORT_QUOTIENT_LIFT`

Still NOT established:

- matched-budget natural developmental dependence;
- frontier expansion caused by prior capability state;
- open-ended compounding;
- full choice-free completeness for arbitrary variable types.

## Next separators

1. Determine whether the `DecidableEq` assumption can be removed without reintroducing `Classical.choice`, or isolate a formal obstruction showing why a total substitution requires an equality/selection principle.
2. Freeze a new natural theorem residual before solution inspection and compare cold / O1 / O1+O2 / O1+O2+O3 / accumulated-state arms under matched proof-search budget.
3. Treat O4 as installed capital only within its verified scope; do not generalize the result beyond decidable variable languages.
