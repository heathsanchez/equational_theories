# O38 — occurrence-coherent axiom separator

Status: FROZEN before theorem implementation.

## Question
Can the current generic choice residual be moved strictly below variable-indexed substitution by representing one axiom instance using representatives chosen per syntax occurrence, together with proof-level coherence for repeated occurrences?

## Inputs already admitted
- O6: every finite `FreeMagma` term evaluated under a quotient-valued valuation has an occurrence-local representative, constructively.
- O6: representatives chosen independently for two occurrences of the same source variable are derivably equal from Γ.
- O8: support-local substitution avoids off-support values, but still asks for a Type-valued function indexed by source-variable identity.
- O19: universal extension of that support-local function to an ambient total substitution is exactly `SupportRetract`.
- O35/O36/O37: resource requirements are route-relative; do not infer problem-level necessity from one calculus architecture.

## Small separator
For a single axiom `E ∈ Γ` and quotient valuation `φ`:

1. Construct occurrence lifts of `E.lhs` and `E.rhs` independently.
2. Package the resulting representative terms plus their evaluation equations.
3. Prove that any two leaf representatives in the package carrying the same source label are propositionally coherent (derivably equal under Γ).
4. Attempt to derive equality of the two representative whole terms **without** constructing either:
   - a total substitution `α → FreeMagma β`, or
   - a support-indexed substitution `(a : α) → E.Mem a → FreeMagma β`.

## Decision tree
- If 1–3 pass but 4 fails at exactly the need for one literal representative per repeated variable, name `OCCURRENCE_COHERENCE_TO_UNIFORM_SUBSTITUTION` as the sharpened residual. Do not broaden further automatically.
- If 4 passes constructively, use it to prove the quotient model satisfies one axiom and only then consider compiling it into a new derivation/completeness route.
- If occurrence coherence itself is insufficient or misstated, reject the representation before creating a new calculus.

## Scope discipline
This experiment does not claim generic choice-free completeness. It is an information route testing whether the current total/support substitution interface is the remaining obstruction.
