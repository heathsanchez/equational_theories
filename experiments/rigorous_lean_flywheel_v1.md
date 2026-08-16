# Rigorous Lean Flywheel v1

## Question
Can a proof mechanism discovered in one natural Lean repair be compiled into reusable capability capital that reduces the acquisition cost of a later natural repair?

## Frozen historical sequence

- Base fork commit: `b1cc1756202d7f44e07bd4069b5df16901a36938`.
- Natural episode E1: upstream PR #1467, Law46, merged 2026-08-13.
- Natural episode E2: upstream PR #1461, Law43, merged 2026-08-14.

The ordering is historical. E2 is not treated as caused by E1.

## Repeated mechanism

Both accepted repairs require the same structural fact:

> Evaluation of a `FreeMagma` depends only on values assigned to variables that occur in the term.

E1 introduced this as `FreeMagma.evalInMagma_congr` inside `Definability/Law46.lean`.
E2 independently rebuilt the same recursive induction locally as `eval_eq_on_mem`.

## Intervention O1

Compile the repeated mechanism once at the generic `FreeMagma` layer:

`equational_theories/FreeMagmaEvalCongr.lean`

Then make Law46 and Law43 consume that shared capability.

## Current evidence state

- OBSERVED: same mechanism was independently paid for in E1 and E2.
- CAUSAL-COST candidate: installing O1 removes the local recursive congruence proof from the E2 construction.
- NOT YET ADMITTED: the branch has not received a Lean kernel/build verdict in this environment.
- NOT COMPOUNDING: no third natural episode has yet been shown to become solvable or materially cheaper because O1 is installed.

## Required next separator

Find a source-distinct natural theorem or historical repair E3 with a residual that requires agreement of evaluations on the variables occurring in a `FreeMagma` term.

Compare under a matched proof/search budget:

1. cold base without O1;
2. base + O1;
3. sham helper of similar size but irrelevant semantics;
4. O1 present but disabled.

A positive result requires either:

- E3 is not reached/solved cold but is reached/solved with O1; or
- E3 is solved in both arms but O1 materially reduces acquisition cost under a precommitted measure.

## Fail conditions

- O1 merely shortens source code after the proof is already known.
- O1 is semantically redundant with an existing imported theorem.
- A gain comes from extra context/search budget rather than capability state.
- The abstraction only applies to Law43/Law46 and does not transfer.

## Current verdict

`RETAIN_CANDIDATE_O1_EVAL_ON_SUPPORT_CONGRUENCE`

The intervention has demonstrated a real repeated-search opportunity and a plausible cost-saving compilation, but no frontier-expansion claim is licensed yet.
