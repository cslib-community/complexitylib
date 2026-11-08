# Using the manual

This manual assumes basic Lean familiarity. Its workflows use the current checkout and ordinary editor, Git, Python and Lake commands. Start with installation and the complete first-client exercise, then choose the model appropriate to your claim. [The manual entry page](../README.md) links the current maintenance and build procedures.

## Reading route

1. [Get oriented and build](getting-started.md): imports, namespaces, the checkout’s toolchain and the first validation loop.
2. [Choose a model and state a contract](choosing-models.md): encodings, resource measures, uniformity and the bridge needed to move between models.
3. [Prove deterministic resource bounds](deterministic-workflows.md): plain polynomial-time proofs, composition, loops and an NP-completeness client.
4. [Work with randomized and oracle programs](probabilistic-workflows.md): free syntax, semantics, native efficiency and oracle costs.
5. [Find and apply a result](finding-results.md): source search, checked abstracts, hypotheses and model-specific theorem routes.
6. [Diagnose proof and build failures](troubleshooting.md): failed automation, missing imports, stale outputs and semantic mismatches.
7. [Contribute and review](contributing.md): placement, source credit, validation, review and upstream coordination.
8. [Coordinate implementation and review](agent-operations.md): participant ownership, isolated work, evidence and review handoffs.

For human direction of agents, use the separate [Agent Operator’s Manual](../AGENT_OPERATORS.md).

The full model/theorem survey follows these workflows as reference chapters. The development study and model inventory remain available in the same volume.

## Known limitations

Examples are contextual excerpts from source clients, with their unique text checked against the current source; open the linked client for its complete imports and local context. The editorial checks do not independently compile rearranged snippets. The quoted Lean clients are by Samuel Schlesinger, under the source repository’s Apache 2.0 license. Desktop transcript records remain unavailable in the historical dataset. The source inventory and review do not certify every mathematical definition or proof.

## Use this book by task

Read the opening workflows once, then use the model chapters as a reference. For a first deterministic proof, follow getting started, model selection and deterministic workflows. For a randomized or oracle routine, continue to the probabilistic chapter. For a circuit, finite-model or RAM application, begin with the model-selection table and follow its checked client and bridge. Use the troubleshooting chapter at the first unexplained obligation, and the contribution and coordination chapters when preparing a change or handing work to another person or agent.

The reference chapters preserve the survey’s model descriptions, theorem boundaries, design rationale and source credit. The history is a dated observational record: it explains earlier decisions and failures but is not a substitute for the current contribution policy. The [full inventory and evidence index](../index.md) links supporting scripts and data; the [original paper plan](../paper-plan.md) preserves the earlier academic framing.
