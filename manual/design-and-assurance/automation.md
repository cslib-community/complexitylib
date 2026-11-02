# Proof automation and client interfaces

The automation layer searches for proofs of explicit mathematical contracts. It generally reuses named certificates and compositional rules; it is not a compiler that can assign a polynomial bound to an arbitrary Lean program. In particular, a short tactic call hides a checked derivation, but the model, algorithm and invariant still have to be right. [complexitylib][complexitylib]

## Named certificates and polynomial time

[`program_certificate`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/PolyTime/Init.lean#L17) indexes a theorem by its efficiency predicate and the head constant of its program, with an encoding flag. The predicate index prevents a RAM certificate from accidentally solving a Turing-machine goal. Looking up a named routine before unfolding its body keeps clients abstract and controls search. The same annotation registers with `fun_prop`, reusing an existing registration when present; parameterized `IsPPT` certificates are normalized to `IsPPTOn` for the shared encoded-input interface.

[`polytime`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/PolyTime.lean#L25) combines these certificates with `fun_prop` composition and the Aesop `PolyTime` rules. Loops use Hoare-style iteration theorems plus bounds on state growth and iteration count. A bounded number of calls to individually efficient routines is insufficient if intermediate data grows exponentially; the growth hypotheses are part of the proof obligation. Ordinary search failure can expose a failed compositional attempt as a diagnostic, not as evidence of noncomputability.

Plain and internal tidy predicates have separate search rules at this snapshot. The preferred plain tactic does not change the user's goal to tidy computability or silently restate hypotheses. Machine-level proofs may still use tidy witnesses internally. This is the implemented direction even where older prose or issues describe a stronger prohibition on tidy use inside proofs.

## Other resource predicates

| Tactic/interface | Input contract and strategy | Boundary |
|---|---|---|
| [`logspace`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/LogSpace.lean#L15) | Named certificates, recomputation-based composition, bounded output vectors and loop rules | Arbitrarily long intermediate output cannot simply be retained in logarithmic workspace |
| [`ppt`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/PPT.lean#L18) | Closed strict fair-coin program certificates, deterministic calls, supported sampling, bounded-growth iteration | Arbitrary ideal PMFs and open oracle programs need additional realization theorems |
| [`stateful`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/Stateful.lean#L14) | Local semantic/operation-cost Hoare contracts and Aesop rules | Intermediate assertions and implementations for bind/link are supplied explicitly; total machine time remains separate |
| [`wordram`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/WordRAM.lean#L16) | Registered controller/refinement and polynomial-time certificates | Width, basis and fixed-code realization matter; host-language continuation work is not automatically free |

This is a family of focused proof tools, not one universal automatic complexity analyzer. Their common interface makes reusable algorithms easier to recognize without conflating the predicates they prove.

## Circuit construction

[`synthesis_step`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/Synthesis.lean#L13) applies an explicitly supplied synthesis rule and locates its required wires among available values. `Synthesis.Builder` retains earlier wires and accumulates certified cost. Membership search itself adds no gates. Reusing a computed value preserves sharing; invoking a new construction charges its bound. A final budget check verifies the chosen construction fits the target, but does not search globally for an optimal circuit.

This contract answers a recurrent concern in the transcript: removing proof bookkeeping must not silently introduce gates. The [circuit case study](../development-history/case-studies.md) connects that concern to PR #520 and to the subsequent decision not to pursue general budget-guided synthesis in that session. The present tactic source is the authority for its current capabilities.

## Logical descriptions

[`FirstOrder.lean`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/FirstOrder.lean) provides `fo_qf`, `fo_iso_closed`, `fo_simp` and `fo_reduction`. They separate syntactic obligations and structural semantic rewrites from the mathematical proof that a reduction expresses the intended property. High-level composition lemmas avoid expanding every pullback into raw syntax.

[`FOOperator.lean`](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/FOOperator.lean#L14) similarly synthesizes a single uniform formula for a family through `fo_definable`, with `fo_wf` handling supported well-formedness/positivity obligations. This does not mean a different formula may be selected separately for each structure. Fixed-point operators, positivity and interpretation legality remain mathematical constraints. The [logic survey](../circuits-logic-and-other-models/index.md) records the distinction between interpretation, quantifier-free reduction and projection.

## Proof style as interface maintenance

The project asks for nonterminal `simp only` where later steps depend on the resulting normal form, forbids global simplification attributes on machine transitions, and requires comments and reviewed allowlisting for unusually large heartbeat bounds. These policies address predictable search explosions and fragile proofs. They complement semantic lemmas and named certificates; they do not prove maintainability by themselves. [Proof hygiene](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/AGENTS.md#proof-hygiene)

Readable `do` notation, named intermediate circuit values and named state fields are recurring client-facing priorities. Inspect representative source clients and before/after PRs to assess these benefits; a raw tactic count does not demonstrate usability. The historical study does not measure an automation success rate: such a rate would need a denominator of attempted goals, failures, manual repairs and timeouts.

[complexitylib]: ../sources.md#complexitylib
