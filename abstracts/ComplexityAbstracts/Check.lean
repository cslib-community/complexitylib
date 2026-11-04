/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

/-!
# Mechanical audit for formal abstracts

A formal abstract (`*Abstract.lean`) introduces self-contained definitions and headline theorem
statements whose proofs delegate to a bridge module (`*Bridge.lean`). The command
`#check_abstract Namespace` verifies that a reader only needs to inspect the abstract file itself:

1. Every declaration in `Namespace` must be defined in the current file. A declaration placed in
   `Namespace` by an imported module (for example a bridge) is rejected.
2. Every declaration in `Namespace` is a root, including private declarations, generated
   auxiliaries (equation lemmas, matchers, structure-field defaults) and user declarations with
   internal-looking names. The audit traverses the roots transitively, following `type` for all
   declarations, `value?` for non-theorems and the constructors of inductive types.
3. A dependency defined in the current file must lie in `Namespace`. A dependency from an imported
   `Complexity.*`, `ComplexityAbstracts.*` or `ComplexityTests.*` module is rejected unless its
   module is allowlisted with `allowing [...]`. The audit keeps traversing allowlisted declarations,
   so the allowlist must cover their transitive dependencies as well. Traversal stops at every other
   module: the background libraries `Init`, `Std`, `Lean`, `Batteries`, `Mathlib` and upstream
   `Cslib`, and the dependencies they bring in (`Aesop`, `Qq`, `Plausible`, `ProofWidgets`, …).
4. Every declaration in `Namespace` is checked with `collectAxioms` to depend only on `propext`,
   `Classical.choice` and `Quot.sound`.
5. Declarations in `Namespace` whose user-facing names are not internal may not be `opaque`,
   `partial` or `unsafe`, nor may dependencies defined in the current file.

On success the command logs the number of audited roots in its guarded status message and logs the
number of transitive dependencies checked as unguarded silent information. Both counts include
compiler-generated declarations, so they may change with the Lean toolchain.

### Scope

The audit is semantic: it inspects elaborated declarations, not syntax. A reader of an abstract
must still check the following, which the `lean-abstract` skill requires:

* every headline theorem lies in the audited namespace, and the file declares nothing outside it
  (declarations of the current file outside `Namespace` are only checked when a root uses them);
* the file declares no notation, macros, instances of background classes, local instances or
  `open` renamings that change how it reads;
* the imported bridge declares no global syntax extensions, elaborators or unification hints.

Adapted from `scripts/CheckAbstract.lean` in `edemaine/lean-canny` (commit `2a50a2ee`), by Erik
Demaine.
-/

namespace ComplexityTests.Abstracts

open Lean Elab Command

/-- Recover the user-facing name of a declaration, stripping any `_private.<mod>.0.` prefix
added by Lean for `private` definitions or equation-compiler matchers. -/
def userFacingName (name : Name) : Name :=
  privateToUserName name

/-- Determine whether `name` (after stripping any `_private` prefix) lies inside `ns`. -/
def inAbstractNamespace (ns name : Name) : Bool :=
  ns.isPrefixOf (userFacingName name)

/-- The constants that `info` mentions in its statement and, unless it is a theorem, in its
body; for an inductive type, also its constructors. -/
def statementDependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut deps := info.type.getUsedConstants
  if let .inductInfo val := info then
    deps := deps ++ val.ctors.toArray
  if !info.isTheorem then
    if let some value := info.value? (allowOpaque := true) then
      deps := deps ++ value.getUsedConstants
  return deps

/-- Audit all declarations in `abstractNamespace` as described in the module docstring:
require them to be defined in the current file, reject transitive dependencies on
non-allowlisted `Complexity.*`, `ComplexityAbstracts.*` or `ComplexityTests.*` modules in
definitions and theorem statements, and reject non-standard axioms. On success, log the number of
audited roots and, as silent information not pinned by `#guard_msgs`, the number of transitive
dependencies checked. -/
def checkAbstract (abstractNamespace : Name) (allowedModules : Array Name := #[]) :
    CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  -- Sort the namespace's declarations so that the reported error does not depend on the
  -- iteration order of the environment.
  let members := (env.constants.toList.filter fun (name, _) =>
    inAbstractNamespace abstractNamespace name).toArray.qsort fun a b => a.1.lt b.1
  if let some (name, _) := members.find? fun (name, _) => (env.getModuleIdxFor? name).isSome then
    let owner := env.header.moduleNames[(env.getModuleIdxFor? name).get!.toNat]!
    throwError "abstract audit: `{userFacingName name}` lies in `{abstractNamespace}` but is \
      defined in imported module `{owner}`, not in the current file"
  let mut pending : Array (Name × Name) := #[]
  for (name, info) in members do
    for ax in ← collectAxioms name do
      unless allowedAxioms.contains ax do
        throwError "abstract audit: `{userFacingName name}` depends on disallowed axiom `{ax}`"
    -- Generated helpers such as `_unsafe_rec` are exempt; `partial` and `unsafe` declarations
    -- themselves are caught through their user-facing names.
    unless (userFacingName name).isInternalDetail do
      if info.isUnsafe || info matches .opaqueInfo _ then
        throwError
          "abstract audit: `{userFacingName name}` is `opaque`, `partial`, or `unsafe`"
    -- Every member is a root, so private and internal-looking declarations are audited even
    -- when nothing else in the namespace refers to them.
    for c in statementDependencies info do
      pending := pending.push (name, c)
  let roots := members.size
  if roots == 0 then
    throwError "abstract audit: no declarations found in namespace `{abstractNamespace}`"
  -- Process roots in sorted order: `pending` is a stack.
  pending := pending.reverse
  let mut visited : Std.HashSet Name := {}
  while !pending.isEmpty do
    let (root, name) := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    match env.getModuleIdxFor? name with
    | none =>
      unless inAbstractNamespace abstractNamespace name do
        throwError
          "abstract audit: `{userFacingName root}` depends on declaration `{userFacingName name}` \
           outside `{abstractNamespace}`"
      if let some info := env.find? name then
        if info.isUnsafe || info matches .opaqueInfo _ then
          throwError
            "abstract audit: `{userFacingName root}` depends on `opaque`, `partial`, or `unsafe` \
             declaration `{userFacingName name}`"
        for c in statementDependencies info do
          pending := pending.push (root, c)
    | some idx =>
      let owner := env.header.moduleNames[idx.toNat]!
      let isLocalRepo := (`Complexity).isPrefixOf owner || (`ComplexityTests).isPrefixOf owner ||
        (`ComplexityAbstracts).isPrefixOf owner
      if isLocalRepo then
        unless allowedModules.contains owner do
          throwError
            "abstract audit: `{userFacingName root}` depends on implementation declaration \
             `{userFacingName name}` from `{owner}`"
        -- An allowlisted declaration is part of what the reader inspects, so its own statement
        -- and body must again stay within the allowlist.
        if let some info := env.find? name then
          for c in statementDependencies info do
            pending := pending.push (root, c)
  logInfo m!"abstract audit passed for `{abstractNamespace}`: {roots} root declarations"
  log m!"abstract audit for `{abstractNamespace}`: {visited.size} dependencies checked"
    (severity := .information) (isSilent := true)

/-- `#check_abstract Namespace` verifies that every declaration in `Namespace` is defined in the
current file, that its statement and (for non-theorems) body reference only `Namespace` and the
background libraries (`Init`, `Std`, `Lean`, `Batteries`, `Mathlib`, upstream `Cslib`), and that it
depends only on the standard axioms. On success it logs the number of audited roots and, as silent
information not pinned by `#guard_msgs`, the number of transitive dependencies checked.

`#check_abstract Namespace allowing [Mod1, Mod2]` additionally permits references to the listed
`Complexity.*`, `ComplexityAbstracts.*` or `ComplexityTests.*` modules. The audit traverses
allowlisted declarations too, so the list must be closed under their transitive statement and
definition dependencies. -/
syntax (name := checkAbstractCmd)
  "#check_abstract " ident (" allowing " "[" ident,* "]")? : command

@[command_elab checkAbstractCmd, inherit_doc checkAbstractCmd]
def elabCheckAbstract : CommandElab
  | `(#check_abstract $ns:ident) =>
    checkAbstract ns.getId #[]
  | `(#check_abstract $ns:ident allowing [$[$mods:ident],*]) =>
    checkAbstract ns.getId (mods.map (·.getId))
  | _ => throwUnsupportedSyntax

end ComplexityTests.Abstracts
