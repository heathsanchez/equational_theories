# Rigorous Method Review — O45–O47

Status: evidence-backed controller review; supplements `rigorous_method_controller_v2.md` without rewriting prior history.

## Evidence

### O45 — existential hiding did not remove proof-to-data uniformization
For one axiom, one support-local assignment, and a final goal wrapped in `Nonempty`, Prop-level excluded middle could construct pointwise `Nonempty (Decidable (E.Mem a))`, but Lean still rejected construction of the function-valued total substitution. The matched Type-valued decision-oracle control succeeded and audited without `Classical.choice`.

Earned residual: `PROOF_TO_DATA_UNIFORMIZATION` survives even under existential hiding when a function's values must be constructed.

### O46 — over-localization destroyed a useful invariant
After O43 localized axiom instantiation successfully to the axiom's support, O46 tried to localize semantics per conclusion law as well. This failed structurally under composition: in `Trans`, premise laws can contain intermediate variables absent from the conclusion's support. A conclusion-local valuation therefore cannot be reused for each premise without constructing new support-indexed data.

The previous global valuation interface was doing two jobs:
1. imposing an expensive totalization/data demand at axiom instantiation;
2. preserving one coherent variable interpretation across `Sym/Trans/Cong` composition.

Removing the first by deleting the whole global interface also deleted the second.

## Controller update — INVARIANT AUDIT

Before broadening by replacing or localizing an interface that has been identified as the source of a residual:

`LOCALIZE DATA DEMAND → INVARIANT AUDIT → REPLACE SMALLEST OFFENDING PART WHILE PRESERVING REQUIRED GLOBAL INVARIANTS`.

Invariant audit asks:
- What useful coherence, identity, causality, provenance, monotonicity, or compositional property does the current interface guarantee?
- Which part of the interface creates the residual, and which part merely carries a necessary invariant?
- Can the data demand be changed without weakening the invariant?
- What downstream rules rely on information not visible in the current local residual?

Negative criterion: if a proposed local representation makes an inference rule require reconstruction of information that the old global representation carried automatically, reject the broad localization and split again.

## O47 licensed representation move

O46 sharpens the desired replacement:
- retain one global valuation so variable coherence survives inference composition;
- remove representative extraction by changing the equality representation rather than the valuation domain.

This licenses the setoid experiment O47: raw terms remain representatives by construction, derivability becomes the equality relation, and global valuations remain ordinary functions.

The upstream issue #499 discussion independently notes the same setoid/quotient distinction in Andreas Abel's constructive proof. O47 must therefore be interpreted carefully: even a successful setoid completeness theorem is not yet a solution to the stronger quotient-model formulation. The bridge back is a separate residual.

## Updated compact fragment

`SPLIT → SHARPEN → REUSE CHECK → ROUTE SELECT → LOCALIZE DATA DEMAND → INVARIANT AUDIT → [BROADEN only at smallest licensed boundary] → VERIFY`.
