# Verified Compounding Causal Benchmark v1

## The only deciding question
Does accumulated verified structural capital causally reduce the cost of acquiring genuinely new verifier-backed capabilities, beyond ordinary memory of prior solved results?

## Primary hypothesis
Across a frozen sequence of unseen Lean repair episodes, matched independent model instances satisfy:

C_capital(n) < C_memory(n) < C_cold(n)

with the stronger compounding signature that the capitalized advantage grows across sequential episodes as newly verified laws from earlier capitalized episodes are admitted into its controller/lawbook.

## Arms
### COLD
Independent fresh model instance/session. Receives only:
- frozen repository/task checkout;
- target proof obligation(s);
- verifier/build command;
- fixed acquisition budget.

No prior solved episodes, controller rules, residual taxonomy, or lawbook.

### MEMORY_ONLY
Independent fresh model instance/session. Receives COLD materials plus prior *successful final proof/results only* from earlier benchmark episodes.

It does NOT receive:
- failed attempts;
- residual splits;
- obstruction names;
- route-selection rules;
- negative-result lawbook entries;
- method/controller updates.

### CAPITALIZED
Independent fresh model instance/session. Receives COLD materials plus the frozen verified structural capital available before that episode, including admitted controller rules, reusable capabilities, negative-result constraints, residual/obstruction taxonomy, route-selection and invariant-preservation rules.

After each episode, only externally verified new capital earned by this arm may enter the next capitalized episode.

## Independence requirement
The three arms MUST be separate model processes/sessions with no shared hidden conversation state. A single already-capitalized model role-playing COLD or MEMORY_ONLY is invalid.

Use the same model/version/configuration for all arms if possible. Random seeds may differ, but model family/configuration, tool access, verifier and acquisition budget must match.

## Task-selection rules
Tasks are historical accepted Lean repairs used only because their pre-merge source and external accepted verifier outcome are recoverable.

For every scored task:
1. Freeze the exact pre-merge base commit before any accepted patch is read.
2. Freeze changed target file(s) by metadata only.
3. Do NOT open PR diff/patch/review explanation before every arm is locked and complete.
4. Target must contain a genuine proof obligation / sorry / rejected proof at the frozen base.
5. Prefer source-distinct tasks and avoid tasks used to derive the controller.
6. Preserve the historical Lean/lake manifest. Never run `lake update` unless that was part of the historical environment.

## Banned / contaminated tasks
These are not eligible for causal scoring:
- teorth/equational_theories#1162 — used for benchmark mechanics pilot and solved in the capitalized session.
- teorth/equational_theories#1467 — accepted patch accidentally exposed during candidate inspection.
- teorth/equational_theories#1054 — accepted patch accidentally exposed during candidate inspection.
- teorth/equational_theories#1461 — previously known Law43 work used in controller development.

## First clean candidate
- Verified-zkEVM/ArkLib#686
- Title: `prove a bunch in sigma.lean`
- pre-merge base SHA: `646fb08582d0254b6eedd238dcb2ba9a13153fcb`
- changed Lean file: `ArkLib/Data/Fin/Sigma.lean`
- accepted patch: UNOPENED at benchmark freeze
- PR metadata body: empty

Additional tasks must be frozen by the same procedure before their patches are opened.

## Acquisition budget
Per arm, per episode, count only semantic acquisition work after the historical environment and benchmark wrapper are valid.

Default cap:
- 8 semantic verifier attempts; or
- equivalent fixed model-call/token budget if the independent runner exposes those metrics.

Whichever cap is reached first ends the episode.

## Cost metrics
Record per arm/episode:
- solved / unsolved;
- semantic verifier attempts;
- semantic failures;
- number of distinct residual classes encountered;
- repeated dead-end attempts;
- broad representation changes;
- model calls and tokens where available;
- wall-clock verifier cost separately from model search cost;
- new verified reusable capability objects admitted.

Exclude from semantic score:
- dependency/provisioning failures;
- environment migration distortion;
- benchmark-wrapper mistakes that occur before the target obligation is reached.
But record these separately.

## Primary statistics
For episode n:

R_search(n) = C_cold(n) / C_capital(n)

R_memory(n) = C_memory(n) / C_capital(n)

DeadBranchReturn(n) = dead_ends_cold(n) - dead_ends_capital(n)

CapitalFormation(n) = verified reusable capability objects admitted after episode n

The decisive flywheel signal is not merely mean advantage. It is a positive sequential trend in:

DeltaC(n) = C_cold(n) - C_capital(n)

or the analogous MEMORY_ONLY difference, with the advantage depending on prior admitted structural capital and disappearing/reducing under ablation.

## Required ablation
At least once after the capitalized arm has accumulated new benchmark-derived capital, rerun an unseen episode with:
- all prior final solved proofs/results available;
- controller/lawbook structural objects removed.

This distinguishes retrieval/example memory from executable epistemic structure.

## Promotion rule
Do NOT claim VERIFIED_COMPOUNDING from:
- one successful capitalized episode;
- retrospective explanation;
- same-session cold simulation;
- solved-count advantage without matched budgets;
- a task whose accepted patch was exposed before arm completion.

Minimum promotion requires multiple independent matched episodes and evidence that structural capital reduces acquisition cost beyond MEMORY_ONLY. Strong promotion additionally requires sequentially increasing returns or a preregistered test showing prior capital causally changes later acquisition.

## Current status
- PILOT_MECHANICS_VALIDATED on historical #1162.
- One prospective source-distinct capitalized acquisition passed (#1162), but no causal arm comparison was possible in the same already-capitalized conversation.
- CAUSAL_BENCHMARK_FROZEN.
- INDEPENDENT_MODEL_RUNNER_REQUIRED.
