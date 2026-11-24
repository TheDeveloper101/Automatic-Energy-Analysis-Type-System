# CLAUDE.md — Ripple Lean Formalization

## Project Purpose

This project mechanizes the Heliod type system found in the parent folder, currently written in latex.
The goal of the type system is to allow fairly precise compile-time cost analysis of programs with stateful peripherals. It combines type state and automatic amortized resource analysis techniques. 

## Ground Truth and Sources

| Source | Status |
|---|---|
| `../writeup.tex`| a short paper explaining the purpose of the type system
| `../*.tex` | First-attempt pen-and-paper formalization. Useful as a guide for how to structure things, but *not* infallible—it may be incomplete or ambiguous. |
| Lean source files | The *actual* formal model. When the original paper formulation is underspecified or ambiguous, we make explicit design choices that must be documented in comments. |


## Correctness Properties

### Type safety
- standard notion. In particular, a well typed program always has the resourced to take a step (or reduce 
to a final state/value)

### Completeness of accounted resources
- each peripheral must have its cost accounted for (whether active or in the background) at 
each logical program step. It should not have its cost double counted. 

## Workflow

The user prefers an **interactive workflow** — do not get too far ahead.

- Work in reviewable steps.  Prove or change **one thing at a time**, then pause so the
  user can look at it before moving on, unless the user as already prompted to prove a larger step to completion.
- After finishing a discrete piece (a lemma, a helper, a fix), **report** rather than
  silently chaining into the next task.  Let the user steer what comes next.
- When the mathematical argument or design is non-obvious, **lay out the plan and check in**
  before writing a large block of tactics or code.
- Prefer confirming direction over batching many changes.  A short round-trip is better than a
  large diff the user has to unwind.

## Coding Conventions

### Proof comments
Every `theorem` and `lemma` **must** have a `/--` docstring or inline comment explaining its
role in the overall argument — not just what it says, but *why* it matters.  Helper lemmas
are fine, but their purpose relative to the main theorem should be clear.

### No hidden holes
**Never claim a theorem is proved if `sorry`s remain or if it relies on unproven premises.**
A theorem with a `sorry` is a placeholder, not a result.  When asked about open proof
obligations, update `TODO.md` honestly.  Helper lemmas with `sorry` are fine as scaffolding,
but must be flagged as such.

### Proof structure first
Before writing Lean tactics, **think through the mathematical argument**: what cases arise,
what the key invariant is, why the induction terminates, where the contradictions come from.
Write this out in a comment or in the conversation before touching the tactic block.

### Build configuration must exercise the active components

Whatever the **default** build command is (`lake build` with no target), it must elaborate every part of
the project currently being worked on.  If a module can be edited but is not in the default target's
import closure, a bare build reports success without ever checking it — a false green that can hide broken
proofs for an entire session.

- Every *leaf* library (one nothing else imports) belongs in the default target.  Leaves transitively pull
  in the rest, so marking leaves is sufficient and stays correct as the graph grows.
- A new file added under an existing directory is **not** automatically built — declare it.
- When adding a component, verify the default build actually covers it: break something in the new file on
  purpose, confirm a bare build fails, then restore.  Job-count changes are a useful smoke signal.

### The `lean-prover` skill
The `lean:lean-proof` skill is installed.  Use it: one tactic at a time, check diagnostics,
work on the hardest case first, clean up after getting a proof to work.


### Style
- Lean 4 idioms: `rcases`, `obtain`, `simp only [...]`, `omega` for arithmetic.
- Keep `private` everything that is not part of the public interface.
- Prefer `mutual ... end` over manually unrolled mutual recursion.
- Do not use `decide` for non-trivial propositions.
- Avoid `simp` without `only` in performance-sensitive proof paths.

## Session Tracking

When asked for remaining tasks or proof gaps, write results to **`TODO.md`** (create or
update it) so context is not lost between sessions.  
