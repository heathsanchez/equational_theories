# Route Selection Benchmark v1

Purpose: measure whether the evolving Rigorous controller changes search economics, not merely whether it can explain successes afterward.

## Measurement discipline
For each target record:
- whether route choice was retrospective or frozen prospectively;
- admitted routes considered before implementation;
- production route selected;
- information route, if separately run;
- new strong assumptions introduced;
- semantic build failures before first green target theorem;
- whether the chosen route reused admitted capability;
- whether a more expensive route was later shown to require stronger resources;
- final kernel/axiom verdict.

This is descriptive evidence until enough matched cases exist. It is not yet a causal controller ablation.

## Case A — idempotence (retrospective route comparison)
Target: choice-free completeness for idempotence.

Initial information route:
- O32 leaf-preserving quotient normalizer.
- Required explicit `[DecidableEq β]`.
- Several semantic/interface repair iterations before green.
- O35 reverse-strength test then proved that, for the leaf-fixed computational normalizer interface, normalizer existence is inter-derivable at `Nonempty` level with `DecidableEq β`.

Alternative production route discovered by REUSE CHECK / ROUTE SELECT:
- O11 singleton-support completeness.
- O36 instantiated it over ambient `PUnit ⊕ κ` with arbitrary `κ`.
- No `[DecidableEq κ]`; no `[DecidableEq β]`.
- Kernel and axiom audit: PASS.

Lesson: resource necessity was route-relative, not target-relative. The expensive normalizer route remained scientifically useful as an information route.

## Case B — commutativity (prospective route selection)
Target: choice-free completeness for commutativity embedded over `Bool ⊕ κ`, arbitrary `κ`.

Frozen route decision before implementation:
- obvious canonical-normalizer route would require ordering/comparison machinery to canonicalize permutations;
- admitted O10 support-resource route only needs resources on the two visible axiom variables;
- controller selected O10 as production route and deliberately did not build a commutativity normalizer.

Implementation O37:
- direct structural `SupportRetract` for the two visible variables;
- direct `SupportQuotientLift` by two quotient representative eliminations;
- reused `Completeness'_supportResources`.

Result:
- first targeted route implementation: PASS;
- no semantic repair iteration before green;
- no `[DecidableEq κ]` or target-variable comparison assumption;
- axiom audit: at most `[propext, Quot.sound]`; no `Classical.choice`, no `sorryAx`.

Status: `FIRST_PROSPECTIVE_POSITIVE_ROUTE_SELECTION_CASE`.

## What would count as stronger evidence
- several additional frozen prospective targets where route-selected acquisition uses fewer semantic iterations / weaker resources than a predeclared alternative;
- a matched cold-controller arm that does not receive the accumulated route library/controller updates;
- fixed budgets and target ordering;
- ablation showing the benefit disappears when route knowledge is removed.

Until then, route selection is an earned controller hypothesis with one prospective success, not a demonstrated compounding law.
