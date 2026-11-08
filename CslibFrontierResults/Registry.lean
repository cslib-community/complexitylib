/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: local-only (result registry tooling)
import Lean

/-!
# Checked declarations for the result registry

`register_result` stores human-readable result and source metadata alongside resolved Lean
identifiers. Ordinary name resolution provides editor navigation and compilation failures for
missing imports and declarations. Source theorem names/numbers and section/page locators are
separate fields; `unverified` marks information not yet collected from the cited source.

The command rejects private names, non-propositions and duplicate IDs or theorem references.
The existing compiled-output audit additionally checks original theorem kind: under Lean's
module system an imported theorem and an unexposed proof definition can both appear as axioms
in the exported environment. Bibliography keys are validated against `references.bib` by CI.
-/

namespace ComplexityResults

open Lean Elab Command

/-- A citation recorded from repository documentation, without claiming a new source audit. -/
structure Source where
  /-- Key in the authoritative bibliography. -/
  bibKey : String
  /-- The source theorem's name or number, if collected. -/
  sourceTheorem : Option String
  /-- Additional section/page locator, if collected. -/
  locator : Option String
  deriving Inhabited

/-- One named result group; declaration names and their defining module are elaborated. -/
structure Entry where
  /-- Stable registry identifier. -/
  id : String
  /-- Human-readable result title. -/
  title : String
  /-- Subject classification. -/
  topic : String
  /-- Defining module shared by the registered declarations. -/
  moduleName : Name
  /-- Fully resolved declaration identifiers. -/
  theorems : Array Name
  /-- Recorded source correspondences. -/
  sources : Array Source
  /-- Hypotheses, model and quantitative limitations. -/
  scope : String
  deriving Inhabited

/-- Registry records persist across ordinary imports. -/
initialize entries : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun imported => imported.foldl (· ++ ·) #[]
  }

/-- Optional source information must be explicit, rather than omitted or guessed. -/
declare_syntax_cat resultSourceInfo
/-- A recorded source theorem identifier or locator. -/
syntax str : resultSourceInfo
/-- Source information that has not yet been collected. -/
syntax "unverified" : resultSourceInfo

/-- A bibliography key, source theorem name/number, and additional locator. -/
declare_syntax_cat resultSource
/-- A structured source citation with independently recorded identifier and locator. -/
syntax "{" "paper" ":=" ident "," "theorem" ":=" resultSourceInfo
  "," "locator" ":=" resultSourceInfo "}" : resultSource

/-- A human-readable result whose theorem identifiers are checked by elaboration. -/
syntax (name := registerResult) "register_result " str "where"
  "title" ":=" str "topic" ":=" str
  "sources" ":=" "[" resultSource,* "]"
  "theorems" ":=" "[" ident,* "]"
  "scope" ":=" str : command

private def sourceInfo : Syntax → CommandElabM (Option String)
  | `(resultSourceInfo| unverified) => pure none
  | `(resultSourceInfo| $value:str) => do
    if value.getString.trimAscii.isEmpty then
      throwErrorAt value "source information must be nonempty or unverified"
    pure (some value.getString)
  | _ => throwUnsupportedSyntax

private def parseSource : Syntax → CommandElabM Source
  | `(resultSource| { paper := $key:ident, theorem := $number:resultSourceInfo,
      locator := $sourceLoc:resultSourceInfo }) => do
    pure ⟨key.getId.toString, ← sourceInfo number, ← sourceInfo sourceLoc⟩
  | _ => throwUnsupportedSyntax

@[command_elab registerResult] private def elabRegisterResult : CommandElab
  | `(register_result $id:str where
      title := $resultTitle:str topic := $resultTopic:str
      sources := [$sourceList:resultSource,*]
      theorems := [$declList:ident,*] scope := $resultScope:str) => do
    let env ← getEnv
    let previous := entries.getState env
    let idValue := id.getString
    unless !idValue.isEmpty && idValue.toList.all (fun c =>
        ('a' ≤ c && c ≤ 'z') || c.isDigit || c == '-') &&
        (idValue.splitOn "-").all (!·.isEmpty) do
      throwErrorAt id "result ID must contain lowercase letters, digits or hyphens"
    if previous.any (·.id == idValue) then
      throwErrorAt id "duplicate result ID: {idValue}"
    for field in #[resultTitle, resultTopic, resultScope] do
      if field.getString.trimAscii.isEmpty then
        throwErrorAt field "result metadata must be nonempty"
    if declList.getElems.isEmpty then
      throwError "a result needs at least one theorem"
    let mut names : Array Name := #[]
    let mut owner : Option Name := none
    for decl in declList.getElems do
      let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
      if isPrivateName name then
        throwErrorAt decl "private declarations cannot be registered"
      let info ← getConstInfo name
      unless ← liftTermElabM <| Meta.isProp info.type do
        throwErrorAt decl "registered declarations must be propositions"
      if names.contains name || previous.any (·.theorems.contains name) then
        throwErrorAt decl "duplicate registered theorem: {name}"
      let some index := env.getModuleIdxFor? name
        | throwErrorAt decl "register an imported declaration, not a local declaration"
      let moduleName := env.header.moduleNames[index.toNat]!
      if let some expected := owner then
        unless expected == moduleName do
          throwErrorAt decl "result declarations must share one defining module"
      owner := some moduleName
      names := names.push name
    let references ← sourceList.getElems.mapM parseSource
    if references.isEmpty then
      throwError "a recorded result needs a source reference"
    let mut keys : Array String := #[]
    for reference in references do
      if keys.contains reference.bibKey then
        throwError "duplicate source reference: {reference.bibKey}"
      keys := keys.push reference.bibKey
    let entry : Entry := ⟨idValue, resultTitle.getString, resultTopic.getString, owner.getD .anonymous,
      names, references, resultScope.getString⟩
    modifyEnv (entries.addEntry · entry)
  | _ => throwUnsupportedSyntax

/-- Generated machine-readable representation consumed by the Python catalogue adapter. -/
def Source.json (source : Source) : Json := Json.mkObj [
  ("bib_key", toJson source.bibKey), ("source_theorem", toJson source.sourceTheorem),
  ("locator", toJson source.locator)]

/-- Module and theorem strings are generated from resolved identifiers, never authored copies. -/
def Entry.json (entry : Entry) : Json := Json.mkObj [
  ("id", toJson entry.id), ("title", toJson entry.title), ("topic", toJson entry.topic),
  ("module", toJson entry.moduleName.toString),
  ("theorems", toJson (entry.theorems.map Name.toString)),
  ("sources", Json.arr (entry.sources.map Source.json)),
  ("source_review", toJson ("recorded" : String)), ("scope", toJson entry.scope)]

end ComplexityResults
