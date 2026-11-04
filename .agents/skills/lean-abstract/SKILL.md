---
name: lean-abstract
description: >-
  Create or revise a human-readable Lean formal abstract with minimal definitions
  and main theorems in *Abstract.lean, proved through *Bridge.lean and audited by
  #check_abstract. Use when adding or updating self-contained formal abstracts for
  headline theorems in Complexitylib or maintaining the curated headline catalogue.
---

# Lean Abstract (`complexitylib`)

Write the formal equivalent of a paper abstract: a short, self-contained Lean file whose mathematical statements a human referee can understand and audit without reading proof implementation details, with proofs mechanically checked against the library via a bridge module and audited by `#check_abstract`.

Adapted from Erik Demaine's [`lean-abstract`](https://github.com/edemaine/agents-config/blob/main/skills/lean-abstract/SKILL.md) workflow for `complexitylib`.

---

## Placement and Naming in `complexitylib`

Formal abstracts and their bridges live in the dedicated `ComplexityAbstracts` Lean library under `abstracts/ComplexityAbstracts/`, with `srcDir = "abstracts"`. They are project scaffolding, outside the upstreamable `Complexity/` library:

- **Bridge module**: `abstracts/ComplexityAbstracts/<Topic>Bridge.lean`
- **Abstract module**: `abstracts/ComplexityAbstracts/<Topic>Abstract.lean`
- **Audit helper**: [Check.lean](../../../abstracts/ComplexityAbstracts/Check.lean) (`#check_abstract`)

Import new `*Abstract.lean` modules from [ComplexityAbstracts.lean](../../../abstracts/ComplexityAbstracts.lean). The test driver imports that library, so `lake test --wfail --iofail` builds and audits every abstract in CI. Keep regression tests in `ComplexityTests/Abstracts/`; Lake's `ComplexityTests.+` glob discovers new modules automatically. Existing abstracts retain their `ComplexityTests.Abstracts.*` declaration namespaces for compatibility; new abstracts may use `ComplexityAbstracts.*`. Catalogue entries specify `namespace` when it differs from their module name. List each selected entry in the top-level `README.md` selected results and in the table of `abstracts/README.md`; `scripts/check_hygiene.py` checks that both READMEs link exactly the catalogue's abstract modules.

---

## Choose the Public Definitions

Inspect the main theorem statements, their hypotheses, and the selected claim and scope in `abstracts/catalogue.json`. Identify only the concepts needed to state the requested results. The abstract may use simpler, more direct representations than the internal proof, provided the bridge proves the correspondence without weakening or strengthening the intended claims.

Outside implementation references are allowed **only in theorem proofs**. Every reference in a public definition, type, or theorem statement must resolve to:
1. A declaration within the abstract namespace itself, defined in the abstract file (`#check_abstract` rejects declarations that another module, such as the bridge, places in the abstract namespace),
2. An upstream background library (`Init`, `Std`, `Lean`, `Batteries`, `Mathlib`, or upstream `Cslib`), or
3. An explicitly allowlisted `Complexity.*`, `ComplexityAbstracts.*` or `ComplexityTests.*` module when using `#check_abstract ... allowing [...]`.

This requirement applies transitively: an alias or wrapper around an internal declaration does not make it self-contained, and `#check_abstract` will reject it. The audit also traverses the statements and definition bodies of allowlisted declarations, so an allowlist must be closed under their dependencies. For the library's complexity classes this closure includes the tidy-machine modules, so prefer restating the classes over plain upstream machines (Pattern A) to allowlisting them.

### Readability Guidelines
- **No top-level `open` in the public abstract**: Use explicit namespace prefixes (e.g., `Cslib.PolynomiallyBounded`, `Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`) so readers can immediately distinguish local abstract definitions from background libraries. `open` may be used locally inside `by` proofs or in the bridge.
- **Everything in one namespace**: Put every declaration of `*Abstract.lean`, in particular every headline theorem, inside the audited namespace. `#check_abstract` audits that namespace only; other declarations in the file are checked only when an audited declaration uses them.
- **No new instances of background classes**: Do not declare instances of background classes on background types (e.g. a new `LE ℕ`), even inside the abstract namespace; they silently change the meaning of standard notation.
- **No notation, macros, local instances, or shadowing**: `#check_abstract` audits elaborated declarations, not syntax, so it cannot see how the file *reads*. Do not declare `notation`, `infix`, `macro`, `syntax`, `local instance`/`attribute [local instance]`, `set_option` that changes elaboration or pretty-printing, or `open ... renaming`/`open ... hiding`, and do not give abstract declarations names that shadow background-library names a reader would expect (`Nat`, `List.sum`, …). A reader must be able to take every symbol in the abstract at its standard meaning.
- **One canonical definition per concept**: Avoid duplicate theorem formulations or multiple equivalent predicates unless the headline result itself compares them.
- **Prefer ordinary types and quantifiers**: Prefer functions, `List`, `Fin n → α`, quantifiers, membership, and equalities over custom interfaces, typeclasses, or implementation-specific dependent records.
- **Use `Fin n → α` for homogeneous tuples**: For more than two homogeneous components, prefer `Fin n → α` over nested cross products, with short descriptive aliases for indices.
- **Explicit encodings**: When a theorem depends on a binary encoding (such as `encCNF` or binary tree encodings), either spell out the encoding combinators (`frame`, `encodePair`, `encodeList`, `Nat.bits`) directly in the abstract or explicitly allow the foundational encoding module. When packaging an encoding function `encodeX : X → List Bool` into an embedding `def encX : X ↪ List Bool := ⟨encodeX, encodeX_injective⟩`, declare `theorem encodeX_injective : Function.Injective encodeX := Bridge.encodeX_injective` as a local `theorem` before `def encX`: `#check_abstract` traverses the `value?` of non-theorem `def`s and stops at `theorem` proof boundaries, and `scripts/abstract_to_tex.py` elides undocumented `*_injective` helper theorems following a definition block (and only those).
- **Share foundations, keep semantics visible**: Use the small audited `ComplexityAbstracts.Encoding` and `ComplexityAbstracts.Computation` modules for common serialization and polynomial-time conventions. Keep complexity-class, game and problem definitions in each abstract. Import every used foundation explicitly, allow it in `#check_abstract`, and list the complete foundation import closure in the catalogue entry's `foundations`. The renderer includes these definitions in each standalone PDF and once at the end of the combined catalogue.
- **Lead with the mathematics**: Put encoding and machine representation details in a `## Representation details` module-doc section. The renderer moves that section and its following declarations to an appendix, ending at the next level-two section. Do not put headline or selected supporting theorems there. Explain every resource-significant convention in the main text, including unary versus binary sizes, uniformity and clock semantics. Moving a definition does not excuse hiding its meaning.
- **Migrate clients to canonical names**: Extract shared definitions without deprecated aliases and update all in-repository clients, following `AGENTS.md`.
- **State plain machine bounds where possible**: `Complexitylib` uses `ComputableTidilyInPolyTime` internally for compositional closure (`@[fun_prop]`), and proves it equivalent to plain upstream `Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength` with `Cslib.PolynomiallyBounded`. Using the plain upstream notion in the abstract lets a reader verify the theorem statement without needing to inspect tidy-machine invariants.

---

## Split Statements from Proof Machinery

Keep the import graph acyclic: **`*Abstract.lean` imports `*Bridge.lean`, so `*Bridge.lean` cannot import `*Abstract.lean`.**

Use one of two bridge patterns depending on whether `*Abstract.lean` defines fresh `inductive`/`structure` types:

**Bridges must not change syntax.** A `*Bridge.lean` (and anything it imports) must not declare global notation, `macro_rules`, elaborators or unification hints: they would change how the abstract elaborates without appearing in it. Reviewers check this, since `#check_abstract` cannot.

### Pattern A: Unfolded Types / `abbrev` (Default)
When `*Abstract.lean` defines problem inputs using type aliases over standard types (e.g., `abbrev Formula := List (List (ℕ × Bool))`):
1. `*Bridge.lean` states the transferred theorem over the unfolded type (`List (List (ℕ × Bool))`) and proves equivalence with the library's internal definitions (e.g., via `Cslib.Complexity.mem_NP_iff_exists_computableInTimeAndSpaceOfLength` and `Turing.MultiTapeTM.ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength`).
2. `*Abstract.lean` defines readable `abbrev` and `def` declarations whose unfoldings are definitionally equal to the bridge's parameters, so each `theorem` proof in `*Abstract.lean` is a 1-line call `exact <Topic>Bridge.<thm>`.

### Pattern B: Polymorphic `Presentation` + `Laws` (`lean-canny` style)
When `*Abstract.lean` introduces fresh `inductive` types (e.g., `inductive Term`, `inductive Formula`) for readability:
1. `*Bridge.lean` defines a `structure Presentation` (packaging abstract types, constructors, induction principles `@Term.rec`, evaluation, and encoding functions) and `structure Laws (S : Presentation) : Prop` (their equational specification).
2. `*Bridge.lean` proves the transfer theorem for any `(S : Presentation) (h : Laws S)` by structural induction using `S.term_induction`.
3. `*Abstract.lean` defines its `inductive` types and functions, then proves the headline theorem by instantiating `Presentation` and discharging `Laws` via `(by constructor <;> intros <;> rfl)`.

---

## Write Mathematical Comments

Start each conceptual block's docstring (`/-- ... -/` or `/-! ... -/`) with a concise mathematical definition or statement in plain English, then briefly note how the Lean expression represents it where non-obvious.

- Explain unfamiliar `Mathlib` or `Cslib` predicates (e.g., `Nat.bits`, `Function.Embedding`, `Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`) by their mathematical meaning before naming the Lean symbol.
- State totality, halting, and answer-preservation guarantees explicitly when describing reductions or verifiers.
- In the module docstring (`/-! # ... -/`), explain that a reader only needs to inspect the definitions and theorem statements in `*Abstract.lean` and its displayed shared foundations to verify that the formalization proves the intended mathematical claim; Lean verifies the proofs through `*Bridge.lean` and `#check_abstract` audits the dependency boundary.

---

## Verify and Integrate

1. **Add `#check_abstract` at the end of `*Abstract.lean`**, wrapped in `#guard_msgs` so the success report (number of root declarations) is pinned and the `hashCommand` linter is satisfied (the transitive dependency count is logged as silent information so it is not pinned by `#guard_msgs`):
   ```lean
   /--
   info: abstract audit passed for `ComplexityAbstracts.<Topic>Abstract`: <n> root
   declarations
   -/
   #guard_msgs (whitespace := lax) in
   #check_abstract ComplexityAbstracts.<Topic>Abstract
   ```
   Or, if deliberately referencing `Complexity.*` declarations, list every module in the transitive closure of their statements and definitions:
   ```lean
   #check_abstract ComplexityAbstracts.<Topic>Abstract allowing [
     Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
   ]
   ```
   Validate with `lake test --wfail --iofail` (as CI does). Do not rely on `-DwarningAsError=true`: under that option the `hashCommand` linter reports an unguarded `#check_abstract` as an info, not a warning, so the problem goes unnoticed.
2. **Compile and check**:
   ```bash
   lake build --wfail --iofail ComplexityAbstracts.<Topic>Abstract
   ```
3. **Render and test TeX / Markdown generation**:
   ```bash
   python3 scripts/abstract_to_tex.py abstracts/ComplexityAbstracts/<Topic>Abstract.lean --format markdown
   python3 scripts/abstract_to_tex.py abstracts/ComplexityAbstracts/<Topic>Abstract.lean --format tex
   python3 -m unittest discover -s scripts -p "test_abstract_to_tex.py" -v
   python3 -B scripts/build_abstracts.py --check
   ```
   The renderer separates declarations at unindented Lean commands, not blank lines, using the
   statement scanner shared with `scripts/proof_lengths.py`. It fails rather than omit unrecognized
   unindented text after a theorem, and `--check` requires each selected statement to be displayed
   in full.

---

## Reference Examples in `complexitylib`

Consult these concrete implementations in `abstracts/ComplexityAbstracts/`:

- **Pattern A (Unfolded types, shared audited foundations)**:
  [CookLevinAbstract.lean](../../../abstracts/ComplexityAbstracts/CookLevinAbstract.lean) and [CookLevinBridge.lean](../../../abstracts/ComplexityAbstracts/CookLevinBridge.lean) (`SAT` and `ExactThreeSAT` are `NP`-complete, `UNSAT` is `coNP`-complete).
- **Pattern B (Fresh `inductive` syntax + polymorphic `Presentation` / `Laws`, shared audited foundations)**:
  [TQBFAbstract.lean](../../../abstracts/ComplexityAbstracts/TQBFAbstract.lean) and [TQBFBridge.lean](../../../abstracts/ComplexityAbstracts/TQBFBridge.lean) (`TQBF` is `PSPACE`-complete).
- **Pattern A reusing another bridge**:
  [SubsetSumAbstract.lean](../../../abstracts/ComplexityAbstracts/SubsetSumAbstract.lean) and [SubsetSumBridge.lean](../../../abstracts/ComplexityAbstracts/SubsetSumBridge.lean) (`SubsetSum` is `NP`-complete with numbers in binary; the bridge reuses the plain `NP` transfer lemmas of `CookLevinBridge`).
- **Audit regression tests, including allowlist mode**:
  [CheckTests.lean](../../../ComplexityTests/Abstracts/CheckTests.lean).
