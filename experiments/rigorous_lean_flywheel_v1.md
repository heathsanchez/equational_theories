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

It does not yet close issue #499 in full generality. The current theorem assumes decidable equality on the context variable type and Type-0 completeness.

## O5 residual — what exactly does finite override require?

After O4, the next question was whether `[DecidableEq α]` was accidental implementation scaffolding.

Repository inspection isolated two distinct uses:

1. `FreeMagma.elems` itself requires `[DecidableEq α]` to deduplicate the finite variable support.
2. More importantly, `derive'.SubstAx` requires a *total* substitution `α → FreeMagma β`. O4 therefore takes finitely many chosen support representatives and extends them to a total function by repeated point overrides.

A first attempted obstruction theorem claimed that a uniform one-point override primitive already implies `DecidableEq`. Under Rigorous review this was rejected as too strong constructively: the attempted proof used contradiction to turn `¬¬(a=b)` into `a=b`, silently adding classical stability.

Corrected candidate file:

`equational_theories/FiniteOverrideObstruction.lean`.

Corrected statements:

- `weakEqDecision_of_onePointOverride`: a one-point Boolean override with exact at-key behavior and preserved off-key default yields, for each `a b`, either `a ≠ b` or `¬¬(a = b)`.
- `decidableEq_of_onePointOverride_of_stableEq`: if equality is additionally stable (`¬¬(a=b) → a=b`), the same override primitive yields full `DecidableEq`.

This correction matters: O5 is not evidence that arbitrary equality is constructively decidable. It identifies the exact logical gap the total-override adapter exposes.

Current O5 verdict: `PENDING_KERNEL_AND_AXIOM_AUDIT`.

## Architectural residual exposed by O5

The strongest remaining obstruction is no longer evaluation. It is the derivation representation:

`derive'.SubstAx` asks for a total substitution on the original variable type even though the axiom term can only observe its support.

This suggests a possible next representation change:

`TOTAL_SUBSTITUTION` → `SUPPORT_LOCAL_SUBSTITUTION`.

A support-local constructor would take assignments only for variables carrying a proof that they occur in the current law. Such a representation can state consistency through the subtype itself and does not need to enumerate all variables or assign off-support values.

However, this must not be confused with solving issue #499. A new support-local calculus would need two separate proofs:

1. semantic soundness / completeness for the new calculus;
2. a conservativity or translation theorem back to the existing `derive'` calculus.

The second translation is exactly where total-function extension may reintroduce the equality/selection obstruction. Therefore a support-local calculus is currently a representation experiment, not yet a replacement proof of the existing completeness theorem.

## Verification history

A targeted workflow `.github/workflows/rigorous-lean-flywheel.yml` was added.

Run 1: failed semantically at a Law43 extensional adapter mismatch; O1 and O2 had already built.

Intervention: add the missing `apply_ite` normalization.

Run 2: all target modules built; first axiom audit showed the O4 results lacked `Classical.choice`, but O2/O3 audit names were missing their import.

Audit harness was hardened with the missing import, `pipefail`, baseline declarations, and failure checks.

Run 3 first attempt: infrastructure-only SSL reset during `lake update`.

Run 3 rerun: PASS. All targets built and the hardened baseline-vs-intervention axiom audit passed.

O5 branch adds a retrying dependency restore because repeated CI runs exposed network resets as an infrastructure residual.

This sequence is classified as residual → intervention → verifier; failed infrastructure or rejected constructive claims are retained rather than hidden.

## Current evidence levels

`ADMITTED_O1_SUPPORT_CONGRUENCE`

`ADMITTED_O2_FREEMAGMA_TERM_BRIDGE`

`ADMITTED_O3_MAPPED_TERM_BRIDGE`

`CANDIDATE_RECURSIVE_ACQUISITION_COST_REDUCTION_O2_TO_O3`

`VERIFIED_SOURCE_DISTINCT_TRANSFER_O1_TO_COMPLETENESS`

`VERIFIED_SCOPED_O4_FINITE_SUPPORT_QUOTIENT_LIFT`

`PENDING_O5_WEAK_EQUALITY_OVERRIDE_OBSTRUCTION`

Still NOT established:

- matched-budget natural developmental dependence;
- frontier expansion caused by prior capability state;
- open-ended compounding;
- full choice-free completeness for arbitrary variable types;
- impossibility of a different constructive proof of generic completeness.

## Next separators

1. Kernel-build and axiom-audit the corrected O5 weak equality obstruction.
2. If O5 passes, treat the current total-override route as logically characterized, not globally impossible.
3. Prototype a support-local substitution calculus and test semantic soundness separately from conservativity back to `derive'`.
4. Freeze a new natural theorem residual before solution inspection and compare cold / O1 / O1+O2 / O1+O2+O3 / accumulated-state arms under matched proof-search budget.
5. Treat O4 as installed capital only within its verified scope; do not generalize the result beyond decidable variable languages.
