# Rigorous Lean Flywheel v1

## Question
Can natural Lean repairs be converted into reusable capability capital so that later proof acquisition pays less repeated search cost and exposes the next abstraction automatically?

## Frozen historical seed
- Base fork commit: `b1cc1756202d7f44e07bd4069b5df16901a36938`.
- Natural episode E1: upstream PR #1467, Law46, merged 2026-08-13.
- Natural episode E2: upstream PR #1461, Law43, merged 2026-08-14.

Historical ordering is not treated as causal dependence.

## O1 — support-sensitive evaluation
`FreeMagma.evalInMagma_congr`: evaluation depends only on values assigned to variables that occur in the term.

- Kernel: PASS.
- Axioms: none.
- Verdict: `ADMITTED_O1_SUPPORT_CONGRUENCE`.

E1 and E2 independently paid for this mechanism. O1 would remove repeated proof work, but that historical counterfactual alone is not a compounding result.

## O2 — FreeMagma evaluator → term-definability
`FreeMagma.eval_termDefinable` compiles a `FreeMagma (Fin 2)` evaluator into a first-order `Set.TermDefinable` witness. Reused by Law43, Law46, and Tarski543.

- Kernel and consumers: PASS.
- Axioms: `[propext, Quot.sound]`.
- Verdict: `ADMITTED_O2_FREEMAGMA_TERM_BRIDGE`.

## O3 — mapped-variable term-definability
`FreeMagma.eval_comp_termDefinable` handles `t ⬝ (v ∘ σ)` by composing O2 with `fmapHom` laws.

- Kernel: PASS.
- Axioms: `[propext, Quot.sound]`.
- Verdict: `ADMITTED_O3_MAPPED_TERM_BRIDGE`.
- Causal claim remains `CANDIDATE_RECURSIVE_ACQUISITION_COST_REDUCTION_O2_TO_O3`; matched cold/ablation acquisition is still required.

## Source-distinct target — upstream issue #499
Issue #499 asks whether the use of choice in `Completeness` can be removed. Baseline `PhiAsSubst_aux` chooses a representative for every coordinate of an arbitrary quotient-valued valuation.

Baseline audits:
- `FreeMagmaWithLaws.isModel`: `[propext, Classical.choice, Quot.sound]`.
- `Completeness'`: `[propext, Classical.choice, Quot.sound]`.

The issue comments additionally note that the referenced Abel Agda argument works with setoids, where representative recovery is identity; it therefore does not directly settle the quotient-type problem.

## O4 — finite-support quotient lifting
File: `CompletenessFiniteSupport.lean`.

O1 licenses forgetting off-support values. `PhiAsSubst_onLawSupport` lifts representatives only where one law can observe them; the resulting model/completeness theorem family assumes `[DecidableEq α]`.

Audits:
- `isModel_decidableVars`: `[propext, Quot.sound]`.
- `Completeness'_decidableVars`: `[propext, Quot.sound]`.
- `Completeness_decidableVars`: `[propext, Quot.sound]`.
- `CompletenessNat_noGlobalChoice`: `[propext, Quot.sound]`.

No `Classical.choice`, no `sorryAx`.

Verdicts:
- `VERIFIED_SOURCE_DISTINCT_TRANSFER_O1_TO_COMPLETENESS`.
- `VERIFIED_SCOPED_O4_FINITE_SUPPORT_QUOTIENT_LIFT`.

This does not close #499 generically.

## O5 — finite override / equality boundary
File: `FiniteOverrideObstruction.lean`.

Rejected claim 1: a uniform one-point override primitive implies `DecidableEq α`. The attempted proof silently used double-negation elimination.

Verified:
- `weakEqDecision_of_onePointOverride`: `(a ≠ b) ∨ ¬¬(a = b)`, no axioms.
- with stable equality, `eqOrNe_of_onePointOverride_of_stableEq`: `(a = b) ∨ (a ≠ b)` in `Prop`, no axioms.

Rejected claim 2: proposition-level equality split plus stability yields Type-valued `Decidable`. Lean rejected elimination of `Or` into `Decidable`; `Or.casesOn` can eliminate only into `Prop`.

Verdict: `VERIFIED_O5_WEAK_EQUALITY_OVERRIDE_BOUNDARY`.

## O6 — occurrence-local quotient lifting
File: `OccurrenceLift.lean`.

`OccurrenceLift Γ φ t u` allows an independent representative at each leaf occurrence. It does not deduplicate variable labels or construct a total substitution.

Verified:
- `occurrenceLift_exists`.
- `occurrenceLift_eval_eq_embed`.
- `eval_has_occurrence_rep`.
- `occurrence_representatives_derivably_equal`.

All audit `[propext, Quot.sound]`; no choice or decidable equality.

Verdict: `VERIFIED_O6_OCCURRENCE_LOCAL_LIFT_AND_PROOF_COHERENCE`.

Result: finite representative acquisition and proof-level repeated-variable coherence are not the obstruction.

## O7 — generic function-space lifting separator
A generic operation that lifts every family through every surjection was formalized and shown propositionally equivalent to a Type-valued choice schema.

- Generic equivalence: no axioms.
- `embed Γ` individually surjective: `[propext, Quot.sound]`.
- baseline `PhiAsSubst_aux`: `[propext, Classical.choice, Quot.sound]`.

Verdict: `VERIFIED_O7_GENERIC_FAMILY_LIFT_EQ_CHOICE`.

Strict scope: this characterizes the generic lifting operation; it does not prove the special quotient completeness theorem impossible constructively.

## O8 — support-local derivation representation
File: `SupportLocalDerivation.lean`.

`FreeMagma.supportSubst` and `deriveSupport'` replace the axiom rule's total substitution by a function defined only on variables accompanied by proof that they occur in the axiom.

Verified clean core:
- support substitution structural laws: no choice.
- proof-irrelevance coherence of repeated membership proofs: no choice.
- `deriveSupport'_of_derive'`: constructive.
- reverse translation under `[DecidableEq α]`: `[propext, Quot.sound]`.

Important negative: the repository's existing `MagmaLaw.finEquiv` route imports `Classical.choice`; it is disqualified as a constructive support-reification bridge.

Verdict: `VERIFIED_O8_SUPPORT_LOCAL_DERIVATION_CORE`; `REJECTED_O8_FINEQUIV_AS_CHOICE_FREE_BRIDGE`.

## O9 — semantic support boundary
File: `SupportSemanticBoundary.lean`.

`SupportRetract E` asserts that the support inclusion has a retraction. `SupportValuationExtension` asks that support valuations extend to ambient valuations.

Verified:
- `supportRetract_iff_allValuationExtensions`: no axioms.
- support/ambient satisfaction bridge under the corresponding extension resource: no `Classical.choice`; semantic theorems use at most `[propext, Quot.sound]`.

Result: global `DecidableEq` is not the intrinsic semantic requirement; support retractability is.

Verdict: `VERIFIED_O9_SUPPORT_RETRACTION_SEMANTIC_BOUNDARY`.

## O10 — resource-factored completeness
File: `CompletenessSupportResources.lean`.

Defined `SupportQuotientLift Γ E`: representative selection only on one law's support.

Verified:
- `totalSubst_of_supportResources`.
- `FreeMagmaWithLaws.isModel_supportResources`.
- `Completeness'_supportResources`.
- O4's decidable-variable construction factors through these resources.

All audit exactly `[propext, Quot.sound]`; no `Classical.choice`.

Verdict: `VERIFIED_O10_RESOURCE_FACTORED_COMPLETENESS`.

The exact per-law resources are now separated:
1. choose representatives on support;
2. retract/totalize support back to the old ambient interface.

## O11 — singleton-support scope expansion
File: `CompletenessSingletonSupport.lean`.

For a law whose support is propositionally one variable, a constant support retraction and one quotient representative suffice. No ambient equality decision is required.

Audits:
- `supportRetract_of_singletonSupport`: no axioms.
- quotient-lift/context/model/completeness results: `[propext, Quot.sound]`.

Verdict: `VERIFIED_O11_SINGLETON_SUPPORT_COMPLETENESS_NO_DECIDABLE_EQ`.

This is the first concrete Type-0 completeness class beyond O4's global `[DecidableEq α]` scope.

## O12 — computational retraction data / proof-object boundary
File: `SupportLocalConservativity.lean`.

First attempt: translate `deriveSupport' → derive'` using mere `SupportRetract E : Prop`. Kernel rejected elimination of the existential retraction from `Prop` into the Type-valued `derive'` proof object. This is retained as a real negative separator.

Corrected resource:
`SupportRetractionData E : Type`, carrying the actual retraction and its on-support law.

Verified:
- `SupportRetractionData.toSupportRetract`: no axioms.
- `totalizeSupportAssignment_of_data_agree`: no axioms.
- `derive'_of_deriveSupport'_retractionData`: no axioms.
- `totalization_merely_exists_of_retract`: no axioms.
- decidable-equality adapters: `[propext, Quot.sound]`.

Verdict: `VERIFIED_O12_PROP_VS_TYPE_RETRACTION_BOUNDARY`.

Result: proposition-level retraction existence and computational retraction data are distinct resources when the target is a proof object in `Type`.

## O13 — explicit computational finite support indexing
File: `CompletenessIndexedSupport.lean`.

`SupportIndexing E` supplies an explicit equivalence from the support subtype to `Fin n`; `RetractableSupportIndexing` additionally supplies the support retraction as data.

Verified:
- `chooseFinFamily`: `[propext]`.
- `supportQuotientLift_of_indexing`: `[propext, Quot.sound]`.
- indexed resource/model/completeness results: `[propext, Quot.sound]`.

Verdict: `VERIFIED_O13_EXPLICIT_INDEXED_SUPPORT_COMPLETENESS`.

Interpretation: finite Type-valued choice itself is constructive. The failed O8 `finEquiv` route was failing at *recovering computational finite support indexing from syntax*, not at choosing over `Fin n` once that indexing is supplied.

## O14 — existential conservativity from mere retraction
File: `SupportLocalExistentialConservativity.lean`.

Prediction from O12: because `Nonempty (derive' ...)` lives in `Prop`, mere proposition-level `SupportRetract` should suffice even though it cannot produce a direct Type-valued proof translator.

Verified:
- `nonempty_derive'_of_deriveSupport'_retractable`: no axioms.
- `nonempty_deriveSupport'_iff_nonempty_derive'_of_retractable`: no axioms.

Verdict: `VERIFIED_O14_EXISTENTIAL_CONSERVATIVITY_PROP_RETRACTION`.

This operationally confirms the O12 Prop/Type boundary.

## Current resource hierarchy
The original apparent choice problem has decomposed into:

`GLOBAL FUNCTION-SPACE REPRESENTATIVE CHOICE`
→ `FINITE OBSERVABLE SYNTAX`
→ `OCCURRENCE-LOCAL REPRESENTATIVES`
→ `VARIABLE-INDEXED SUPPORT ASSIGNMENT`
→ `SUPPORT RETRACTION / TOTALIZATION`
→ `PROP EXISTENCE VS TYPE DATA`
→ `COMPUTATIONAL SUPPORT INDEXING`.

The current cumulative branch through O14 kernel-builds as one dependency cone and passes the widened transitive axiom audit.

## Current unresolved residual
The remaining generic bottleneck is no longer simply "finite support" or "choice".

`FreeMagma.Mem` and `MagmaLaw.Mem` encode occurrence information in `Prop` using equality and `Or`. A support-local assignment, however, returns terms in `Type`. Eliminating an `Or`-shaped membership proof into a computational leaf/index is therefore not generally available. `toList` can enumerate occurrences constructively, but assigning one computational representative per *variable label* still requires a bridge from variable identity to occurrence identity.

Named residual:

`PROP_MEMBERSHIP_TO_COMPUTATIONAL_OCCURRENCE_MATERIALIZATION`.

O15 is testing this directly with a Type-valued occurrence-position representation. It is not yet admitted in this ledger.

## External consistency check: issue #499
The upstream issue itself records a closely related distinction: Abel's referenced proof uses setoids rather than quotient types, so representative recovery is identity there. That does not solve the quotient theorem automatically, but it independently supports treating representation as the central separator.

## Still NOT established
- full generic choice-free completeness for arbitrary variable types;
- impossibility of another constructive proof of generic completeness;
- matched-budget natural developmental dependence of O2/O3;
- frontier expansion caused by prior capability state under a frozen acquisition protocol;
- open-ended compounding.

## Verification discipline
- semantic failures are not reclassified as infrastructure;
- stale theorem names in audit scripts are repaired but never counted as theorem failure;
- transitive axiom audits reject hidden `Classical.choice` or `sorryAx` in scoped targets;
- failed stronger claims remain in the ledger;
- transient dependency restoration retries and branch concurrency prevent duplicated CI cost.

## Next separators
1. O15: Type-valued occurrence positions versus Prop-valued `Mem`, with a direct structural search arm under `[DecidableEq α]` that does not use `elems` or `finEquiv`.
2. If O15 passes, test whether computational occurrence materialization plus computational support retraction is sufficient to build O10's `SupportQuotientLift`, avoiding the stronger `support ≃ Fin n` assumption from O13.
3. Only after that separator, test an occurrence-indexed axiom calculus; keep its conservativity back to ordinary `derive'` as an independent gate.
4. Separately run the frozen matched-budget natural acquisition experiment before upgrading any compounding claim.
