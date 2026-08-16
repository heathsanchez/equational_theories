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
- third natural consumer: NOT FOUND;
- kernel/build verdict: PENDING;
- compounding: NOT CLAIMED.

## Residual exposed after O1

Law43 and Law46 still independently hand-built the bridge from a `FreeMagma` expression to a first-order `Set.TermDefinable` witness. Tarski543 contained a third independently written instance of the same bridge in its private `termDef` lemma.

## O2 — FreeMagma evaluator to term-definability

Intervention: `equational_theories/Definability/FreeMagmaTerm.lean`.

Capability:

> Any `FreeMagma (Fin 2)` evaluator is automatically term-definable in the underlying magma language.

Candidate consumers:
- Law43;
- Law46;
- Tarski543.

The previous Tarski543 proof explicitly constructed nested first-order function syntax and simplified its realization. O2 reduces that to the mathematical FreeMagma expression plus one bridge application.

Evidence:
- repeated semantic mechanism across three sites: OBSERVED;
- cross-site source-level reuse: CANDIDATE PASS;
- first-order witness boilerplate compression: PASS at source level;
- kernel/build verdict: PENDING;
- natural developmental dependence: NOT TESTED;
- compounding: NOT CLAIMED.

## Residual exposed after O2

Law43 and Law46 still separately performed the same adapter step:

`FreeMagma α` → map each source variable to argument 0 or 1 → `FreeMagma (Fin 2)` → O2.

Because O2 already exists, this adapter can be acquired by composition rather than by constructing another first-order witness proof.

## O3 — mapped-variable term-definability

Derived capability in `Definability/FreeMagmaTerm.lean`:

`FreeMagma.eval_comp_termDefinable`.

Statement:

> For any `t : FreeMagma α` and any map `σ : α → Fin 2`, the binary evaluator `v ↦ t ⬝ (v ∘ σ)` is term-definable.

Construction cost with O2 installed is essentially one composition:

`fmapHom σ t` + O2 + `evalInMagma_fmapHom`.

Law43 and Law46 now invoke O3 directly rather than explicitly constructing the mapped `FreeMagma (Fin 2)` and invoking O2 themselves.

## O2 → O3 developmental signature

This is the first recursive-cost candidate in the branch:

- before O2, proving O3 directly would require reconstructing the first-order witness bridge;
- after O2, O3 is a small derived theorem obtained by composition with an existing FreeMagma law;
- O3 then compresses two existing consumers.

Verdict: `CANDIDATE_RECURSIVE_ACQUISITION_COST_REDUCTION`.

This is not yet `COMPOUNDING` because:
- the branch has no Lean kernel/build verdict;
- O3 was deliberately sought from the residual exposed by O2 rather than arising in a frozen later natural episode;
- no matched cold/sham/disabled acquisition experiment has been run.

## Infrastructure residual

GitHub reports zero Actions runs for the experiment branch. The available integration receives HTTP 403 when querying repository Actions permissions. Therefore the absence of CI is classified strictly as infrastructure/verification unavailable, not as semantic success or failure.

## Required next separator

Find or generate a live natural proof residual E3 before inspecting its proof solution and run matched acquisition arms:

1. cold base;
2. O1 only;
3. O1 + O2;
4. O1 + O2 + O3;
5. sham helpers with matched context/size;
6. O3 present but disabled.

A developmental positive requires that the accumulated capability state changes acquisition under a frozen budget: solve/no-solve, calls/tokens/attempts, time-to-first-kernel-valid proof, or which next reusable abstraction is discovered.

## Current verdicts

`RETAIN_CANDIDATE_O1_SUPPORT_CONGRUENCE`

`RETAIN_CANDIDATE_O2_FREEMAGMA_TERM_BRIDGE`

`RETAIN_CANDIDATE_O3_MAPPED_TERM_BRIDGE`

`CANDIDATE_RECURSIVE_ACQUISITION_COST_REDUCTION_O2_TO_O3`

No frontier-expansion or natural compounding claim is licensed yet.
