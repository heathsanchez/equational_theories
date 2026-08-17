#!/usr/bin/env python3
"""Run the frozen verified-compounding causal benchmark with isolated model calls.

Requires OPENAI_API_KEY in the execution environment. This runner intentionally
creates a fresh Responses API call for every arm/task pair and never passes one
arm's transcript to another.

The Lean verifier remains the source of truth for semantic success; model text
alone is never scored as solved.
"""

import json
import os
from pathlib import Path
from openai import OpenAI

MODEL = os.environ.get("RIGOROUS_BENCH_MODEL", "gpt-5.6-sol")
REASONING_EFFORT = os.environ.get("RIGOROUS_BENCH_REASONING", "high")
ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results"
OUT.mkdir(exist_ok=True)

client = OpenAI()

CONTROLLER = r'''
RIGOROUS CONTROLLER CAPITAL
- Freeze the task and evidence boundary before search.
- On failure: classify infrastructure vs semantic residual.
- Split the semantic residual into rival explanations before broadening.
- Run the smallest deciding separator; prune falsified branches.
- REUSE CHECK before inventing new proof machinery.
- ROUTE SELECT: compare admitted proof architectures and resource costs.
- INVARIANT AUDIT before replacing a global interface.
- Treat Prop-to-Type / proof-to-data uniformization as a named residual.
- Localize data requirements to the smallest constructor/interface imposing them.
- Retain negative results and exact scopes; do not convert heuristics into law without verification.
- Periodically zoom out over verified episodes, compress recurring structure into reusable operators, then transfer-test/ablate before installing.
- Lean/kernel results are hard evidence; prose plausibility is not.
'''.strip()

MEMORY_ONLY = r'''
VERIFIED PRIOR RESULTS MEMORY
Previous verified work found reusable patterns involving support-sensitive evaluation,
term-definability bridges, quotient/setoid representation differences, finite-support
reasoning, canonical normalizers, and multiple Lean proof-repair episodes. Previous
successful proofs and outcomes may be relevant. Use them as examples, but no explicit
controller or residual-management policy is supplied.
'''.strip()

COLD = r'''
You are solving a Lean proof task from its frozen pre-merge source. Find a correct,
minimal repair. Use only the supplied source/context and verifier feedback. Do not look
up the accepted historical patch or PR diff.
'''.strip()

ARM_PREFIX = {
    "cold": COLD,
    "memory": COLD + "\n\n" + MEMORY_ONLY,
    "capital": COLD + "\n\n" + MEMORY_ONLY + "\n\n" + CONTROLLER,
}

# Tasks are intentionally stored as source manifests, not accepted patches.
# Add only tasks whose accepted diff has not been exposed to any arm before scoring.
TASKS = json.loads((ROOT / "tasks.json").read_text())


def call_model(arm: str, task: dict) -> dict:
    prompt = f"""{ARM_PREFIX[arm]}

FROZEN TASK MANIFEST
Repository: {task['repository']}
Base commit: {task['base_sha']}
Target file: {task['path']}
Target declaration(s): {task['targets']}
Budget: {task['budget']}

SOURCE / GOAL CONTEXT
{task['context']}

Return only a proposed Lean patch/replacement plus a short residual note. Do not claim
success without verifier evidence. Do not use or infer the historical accepted patch.
"""
    response = client.responses.create(
        model=MODEL,
        reasoning={"effort": REASONING_EFFORT},
        input=prompt,
    )
    return {
        "arm": arm,
        "task_id": task["id"],
        "model": MODEL,
        "reasoning_effort": REASONING_EFFORT,
        "output": response.output_text,
        "usage": getattr(response, "usage", None).model_dump() if getattr(response, "usage", None) else None,
    }


def main():
    if not os.environ.get("OPENAI_API_KEY"):
        raise SystemExit("OPENAI_API_KEY is required; fail closed rather than run non-independent pseudo-arms")
    for task in TASKS:
        for arm in ("cold", "memory", "capital"):
            result = call_model(arm, task)
            p = OUT / f"{task['id']}__{arm}.json"
            p.write_text(json.dumps(result, indent=2, default=str))
            print(p)


if __name__ == "__main__":
    main()
