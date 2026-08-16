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

Intervention:

`equational_theories/FreeMagmaEvalCongr.lean`

Law46 and Law43 now consume that shared capability.

Evidence state:

- OBSERVED: same mechanism was independently paid for in E1 and E2.
- CAUSAL-COST candidate: installing O1 removes the local recursive congruence proof from the E2 construction.
- TRANSFER SEARCH: no clean source-distinct third consumer has yet been found.
- NOT YET ADMITTED: the branch has not received a Lean kernel/build verdict in this environment.
- NOT COMPOUNDING: no later natural frontier expansion is licensed from O1.

## Residual exposed after O1

After removing the duplicated evaluation-congruence induction, Law43 and Law46 still independently hand-build essentially the same first-order witness:

1. start with a `FreeMagma` expression over two arguments;
2. translate it to the first-order magma language;
3. use that term as the witness for `Set.TermDefinable`;
4. prove realization agrees with free-magma evaluation.

Tarski543 contains a third, independently written instance of this same bridge in its private `termDef` lemma.

This repeated cost became the candidate next capability.

## O2 — FreeMagma evaluator to term-definability bridge

Intervention:

`equational_theories/Definability/FreeMagmaTerm.lean`

Capability:

> Any `FreeMagma (Fin 2)` evaluator is automatically term-definable in the underlying magma language.

Current consumers on the experiment branch:

- Law43: remap the relevant natural-number variables to `Fin 2`, then invoke O2.
- Law46: map every variable of `L.lhs` to argument 0, then invoke O2.
- Tarski543: represent `x ◇ ((x ◇ x) ◇ y)` as a `FreeMagma (Fin 2)`, then invoke O2.

The old Tarski543 witness explicitly constructed nested `Functions.apply₂` syntax and simplified its realization. O2 reduces that to the mathematical expression plus one reusable theorem application.

## O2 evidence state

- REPEATED-MECHANISM: PASS at source level; the same semantic bridge occurs in three proof sites.
- CROSS-SITE REUSE: candidate PASS; the branch now routes all three sites through one constructor.
- REPRESENTATION COMPRESSION: PASS at source level; first-order syntax construction is no longer repeated at each consumer.
- KERNEL VALIDATION: PENDING. No claim of Lean acceptance until the branch receives a build/kernel verdict.
- NATURAL DEVELOPMENTAL DEPENDENCE: NOT TESTED. Tarski543 is an existing proof, not a later natural acquisition episode caused by O2.
- COMPOUNDING: NOT CLAIMED.

## Required next separator

The next useful test is not another cleanup. Find a natural live proof residual E3 for which O2 is available before acquisition.

Compare under matched proof/search budgets:

1. cold base without O1/O2;
2. base + O1 only;
3. base + O1 + O2;
4. sham helpers of similar context/size;
5. O2 present but disabled.

A developmental positive requires that O2 changes acquisition, not merely final source length: for example E3 is solved only with O2, is found materially earlier with O2, or O2 changes which next abstraction is discovered under the same budget.

## Fail conditions

- O1/O2 merely shorten source code after proofs are already known.
- Either capability is semantically redundant with an existing imported theorem.
- Gains arise from extra context or search budget.
- The abstraction does not survive source-distinct transfer.
- Kernel/build verification fails.

## Current verdict

`RETAIN_CANDIDATE_O1_SUPPORT_CONGRUENCE`

`RETAIN_CANDIDATE_O2_FREEMAGMA_TERM_BRIDGE`

The branch now demonstrates two successive compression steps: solving exposed duplicated evaluation reasoning; compiling that exposed a second repeated term-witness construction; compiling the second gives three candidate consumers. This is flywheel-shaped behavior, but not yet evidence of natural compounding or frontier expansion.
