# TSL-MT Faithful Decomposition (Paper-Exact Notes)

This note fixes the exact behaviors to implement for Algorithm 1 (Syntactic Decomposition) and Section 4.2 (Consistency Checking) of **Choi et al., PLDI’22**. The goal is *paper-faithful* behavior with **no shortcuts**.

These rules are extracted from the paper text and the Algorithm 1 pseudocode (confirmed via OCR on page 6 of the PDF).

## Definitions

- **NNF (Negation Normal Form)**: push negations down to predicate literals only. Derived operators are rewritten; the resulting NNF may use **`Next` (◯)**, **`Until` (U)**, and **`Release` (R)** (the standard LTL dual of `U`).
- **Predicate literal**: a predicate term in NNF with polarity (positive `p` or negated `¬p`). Negations are part of the literal set.
- **Temporal atom**: for a predicate literal, the *maximal* subformula containing that literal connected only by logical connectives (`And`, `Or`, `Not`) and atomic formulae (predicate checks or updates). Temporal operators are **not** included in a temporal atom.

## Algorithm 1 (Syntactic Decomposition) — Exact Steps

### 1) Predicate literals
From the NNF formula, collect **all predicate literals with polarity**.

### 2) Postconditions via temporal-atom traversal
For each predicate literal `p`:

1. Compute its **temporal atom** `A`.
2. Set `numNext = 0`.
3. Traverse upward from `A` toward the root, stopping at the first temporal operator encountered at each step.

At each traversal step:

- **If parent is `◯` (Next)**:
  - `numNext++`
  - Append postcondition **`◯^{numNext} p`**.
  - Continue traversal upward.

- **If parent is `U` (Until)**:
  - If the temporal atom is the **right-hand side** of `U`, append postcondition **`◇ p`** (eventually `p`).
  - If the temporal atom is the **left-hand side** of `U`, append postcondition **`◯ p`** (next `p`).
  - **Break** traversal (stop climbing further).

- **If parent is `R` (Release)** (dual of `U`):
  - If the temporal atom is the **right-hand side** of `R`, append postcondition **`◯ p`** (since the RHS must persist until release).
  - If the temporal atom is the **left-hand side** of `R`, append postcondition **`◇ p`** (release condition can be reached eventually).
  - **Break** traversal.

- **If root is reached**: stop.

> OCR of the paper’s Algorithm 1 indicates `postconditions.append(◇ p)` for RHS of `U`, and `postconditions.append(◯ p)` for LHS of `U`. The text explanation (“model must be able to produce p” for RHS; “p → ◯p as long as RHS is false” for LHS) aligns with this.

### 3) Temporal operator for postcondition *conjunctions*
Postconditions are combined via powerset. For any postcondition conjunction, the **temporal operator** for the entire postcondition is chosen as:

- **`◇` if any conjunct is eventual**, else
- the **maximum** number of `◯` operators among the conjuncts.

This rule is directly stated in the paper: “the maximum time (i.e., a ◇, or if none exists, the maximum number of ◯ operators) of a postcondition is assigned as its temporal operator.”

### 4) DTO generation (powerset)
Let:
- `preconditions = predicate literals`
- `postconditions = temporalized literals from Step 2`

Then:
- For **every** conjunction `Ppre` in `POWERSET(preconditions)`
- For **every** conjunction `Ppost` in `POWERSET(postconditions)`
- Append DTO `(Ppre, Ppost)`.

**No truncation.** The full powerset is used.

## Section 4.2 (Consistency Checking) — Exact Steps

- Enumerate the **powerset of all predicate literals (with polarity)**.
- For each conjunction `p` in the powerset, check SMT satisfiability.
- If unsatisfiable, add assumption **`G ¬p`** to the TSL spec.

**No caps, no pair-only shortcuts, no skipping on errors.**

## Implementation Constraints (Hard Requirements)

- The NNF conversion must fully normalize temporal operators into `◯` and `U` before decomposition.
- Derived operators (F, G, R, W, etc.) must be rewritten exactly by their standard LTL equivalences.
- DTO generation and consistency checking must use **full powersets**.
- No solver depth/time limits or assumption skipping are allowed in these stages (even if runtime increases).
