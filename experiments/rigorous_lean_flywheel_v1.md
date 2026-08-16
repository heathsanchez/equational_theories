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

## O5 — finite-override / equality boundary

After O4, the next question was whether `[DecidableEq α]` was accidental implementation scaffolding.

Repository inspection isolated two implementation uses:

1. `FreeMagma.elems` requires `[DecidableEq α]` to deduplicate variable support. This part is avoidable in principle because `FreeMagma.toList` can enumerate occurrences with duplicates constructively.
2. The deeper use is `derive'.SubstAx`, which requires a *total* substitution `α → FreeMagma β`. O4 therefore has to extend finitely many support representatives to a total function by repeated point overrides. The semantic side mirrors this: `satisfies` quantifies over total valuations `α → G`.

This exposed three separate problems that should not be conflated:

`SUPPORT EXTRACTION` → `SUPPORT COHERENCE` → `TOTAL-MAP EXTRACTION`.

O1 solves the semantic support problem. O4 solves support coherence and total-map construction when equality is decidable. O5 characterizes what remains when equality is not assumed decidable.

### Rejected O5 claim 1

The first candidate theorem claimed that a uniform one-point override primitive already implies `DecidableEq α`.

Rigorous review rejected the proof before admission: the argument silently converted `¬¬(a=b)` to `a=b`, i.e. used equality stability / classical reasoning.

### Verified O5 theorem 1

File: `equational_theories/FiniteOverrideObstruction.lean`.

`weakEqDecision_of_onePointOverride` states that a Boolean one-point override satisfying exact at-key behavior and preserving the default off-key yields, for every `a b`,

`(a ≠ b) ∨ ¬¬(a = b)`.

Kernel build: PASS.

Axiom audit:

`weakEqDecision_of_onePointOverride` — no axioms.

This is the strongest equality separator earned directly from the override behavior without adding equality stability.

### Rejected O5 claim 2

A second candidate added equality stability `¬¬(a=b) → a=b` and attempted to return Type-valued `DecidableEq α`.

Kernel verdict: FAIL.

Lean rejected elimination of the proof-level `Or` into `Decidable (a=b)`, because `Or.casesOn` may eliminate only into `Prop`. This isolates a second gap: even a proof of `(a=b) ∨ (a≠b)` is not automatically computational `Decidable (a=b)` data.

### Verified O5 theorem 2

The corrected theorem `eqOrNe_of_onePointOverride_of_stableEq` stays in `Prop`:

with the same override primitive plus stable equality, it yields

`(a = b) ∨ (a ≠ b)`.

Kernel build: PASS.

Axiom audit:

`eqOrNe_of_onePointOverride_of_stableEq` — no axioms.

### O5 verdict

`VERIFIED_O5_WEAK_EQUALITY_OVERRIDE_BOUNDARY`.

Strict interpretation:

- the current override route does **not** constructively yield `DecidableEq`;
- it does yield inequality versus double-negated equality with no axioms;
- stable equality upgrades this to a proposition-level equality split with no axioms;
- extracting Type-valued decidability is an additional computational/logical step;
- this does **not** prove generic completeness without `DecidableEq` impossible.

The result characterizes the present representation route rather than globally ruling out a different constructive completeness proof.

## Architectural residual exposed by O5

The strongest remaining obstruction is no longer FreeMagma evaluation. It is a matched syntax/semantics representation pair:

- `derive'.SubstAx` asks for a total substitution on the original variable type;
- `satisfies` quantifies over total valuations on that type;
- a law itself observes only finitely many occurrences.

A tempting next move is:

`TOTAL_SUBSTITUTION / TOTAL_VALUATION` → `SUPPORT_LOCAL_SUBSTITUTION / SUPPORT_LOCAL_VALUATION`.

But per-occurrence representatives create a new coherence obligation: repeated occurrences carrying the same variable label must receive compatible representatives. Choosing a canonical occurrence requires either equality discrimination or a route through proof-level membership that cannot in general be eliminated into Type-valued data.

Therefore the next named residual is:

`SUPPORT_COHERENCE_AND_EXTRACTION`.

A support-local calculus remains a legitimate representation experiment, but it would require two distinct proofs:

1. soundness/completeness for the support-local semantics and calculus;
2. conservativity / translation back to the existing `derive'` calculus.

The second step is precisely where total-map extraction may reappear. No claim of full issue #499 closure is licensed from O5.

## Verification history

A targeted workflow `.github/workflows/rigorous-lean-flywheel.yml` was added.

O1–O4 history:

- first semantic failure: Law43 extensional adapter mismatch;
- intervention: add the missing `apply_ite` normalization;
- subsequent target builds: PASS;
- first O4 audit had missing imports for O2/O3 names;
- hardened baseline-vs-intervention audit: PASS;
- one `lake update` SSL reset was classified infrastructure-only and passed on rerun.

O5 history:

- first overstrong `DecidableEq` argument rejected for hidden double-negation elimination;
- corrected weak separator introduced;
- first attempted stable-equality → `DecidableEq` theorem failed in the kernel because proof-level `Or` cannot eliminate into Type-valued `Decidable`;
- corrected stable-equality theorem kept the conclusion in `Prop`;
- both corrected O5 theorems kernel-built;
- hardened axiom audit: both corrected O5 theorems depend on no axioms;
- CI dependency restoration now retries transient network failures;
- O5 verification was reduced to the O4/O5 dependency cone;
- workflow concurrency now cancels superseded same-branch runs to avoid repeated verification cost.

This history is retained as residual → intervention → verifier; neither semantic failures nor infrastructure failures are hidden.

## Current evidence levels

`ADMITTED_O1_SUPPORT_CONGRUENCE`

`ADMITTED_O2_FREEMAGMA_TERM_BRIDGE`

`ADMITTED_O3_MAPPED_TERM_BRIDGE`

`CANDIDATE_RECURSIVE_ACQUISITION_COST_REDUCTION_O2_TO_O3`

`VERIFIED_SOURCE_DISTINCT_TRANSFER_O1_TO_COMPLETENESS`

`VERIFIED_SCOPED_O4_FINITE_SUPPORT_QUOTIENT_LIFT`

`VERIFIED_O5_WEAK_EQUALITY_OVERRIDE_BOUNDARY`

Still NOT established:

- matched-budget natural developmental dependence;
- frontier expansion caused by prior capability state;
- open-ended compounding;
- full choice-free completeness for arbitrary variable types;
- impossibility of a different constructive proof of generic completeness.

## Next separators

1. Test whether a support-local syntax/semantics pair can avoid `TOTAL-MAP EXTRACTION` without merely moving the same coherence problem elsewhere.
2. Separate support occurrence enumeration (constructive via `toList`) from variable-identity coherence, so `[DecidableEq]` is not blamed for work it is not actually doing.
3. If a support-local calculus is viable, test conservativity back to `derive'` independently from its internal soundness/completeness.
4. Freeze a new natural theorem residual before solution inspection and compare cold / O1 / O1+O2 / O1+O2+O3 / accumulated-state arms under matched proof-search budget.
5. Treat O4 and O5 as installed capital only within their verified scopes; do not upgrade to generic choice-free completeness or compounding without the corresponding separators.
