/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (project validation tooling)
import Lean

/-!
# Declaration data for `scripts/quality_report.py`

Run as `lake env lean --run scripts/QualityReport.lean <lib-dir> [<pairs>] < modules.txt`, with one
module name per line on standard input. For every module it reads the three parts of the built
`.olean` (exported, server and private) without importing them, and prints one JSON line per
constant:

* `n`, `m`: the constant and its module;
* `k`: its kind in the private part (`def`, `thm`, `induct`, `ctor`, `rec`, `opaque`, `quot`,
  `axiom`); `e`: its kind in the exported part, or `""` when it is not exported. Under the module
  system a public theorem is exported as an `axiom` (statement only), a definition whose body is not
  exposed as an `axiom`, and an exposed definition as a `def`;
* `doc`: whether it has a docstring (Markdown, Verso or `@[inherit_doc]`);
* `tidy`: the constants named `ComputableTidily…`, `ComputesTidily…` or `IsTidy…` in its type;
  `tb`: for an exported definition, those in its exposed body outside proofs. Proofs are the
  subterms whose type is a proposition, together with the statements of proof-local `have`s (a
  `let` whose type is a proposition): tidy computability is allowed there (#456). Telling them
  apart needs types, so the modules of the definitions whose body mentions a tidy constant are
  imported (at the exported level) for this, and their rows are printed last;
* `u`: for an exported constant, the other constants of the same module that its exported
  statement or exposed body mentions (these cannot become private while it stays public);
* `r`: its declaration range `[line, column, endLine, endColumn, selLine, selColumn, selEndLine,
  selEndColumn]`, with 1-based lines and code-point columns, when one is recorded.

An optional second argument, comma-separated `tidy=plain` pairs of predicate names (used by
`scripts/tidy_sweep.py`), adds two fields. `ph`, for an exported constant: a hash of its type with
universe parameters renamed positionally and each listed tidy or plain predicate replaced by its
plain one, so that a statement and its plain transport hash alike. `sg`, for a constant whose type
mentions a listed tidy predicate: `[[[binderInfo, flag], ...], flag]` for the leading binders and
the conclusion, with binder info `0` explicit, `1` implicit, `2` strict implicit, `3` instance, and
flag `1` when the type is an application of a listed tidy predicate, `2` when it mentions a tidy
constant otherwise, and `0` when it mentions none.

Run as `lake env lean --run scripts/QualityReport.lean --names <module>...`, it instead prints
every name the given modules and their transitive imports export (constants and `export`
aliases), one per line, then a line `--tokens--` and the parser tokens they declare (global and
scoped notations, syntax and macros), for the name resolution of `scripts/tidy_sweep.py`.

It then prints `{"dup": [...], "k": ...}` lines grouping exported constants of different modules
whose types are alpha-equivalent (`k = "thm"`), or whose types and exposed bodies are
(`k = "def"`). Universe parameters are renamed positionally before comparing.
-/

open Lean

namespace ComplexityScripts.QualityReport

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def isTidy (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "ComputableTidily" || s.startsWith "ComputesTidily" ||
      s.startsWith "IsTidy"
  | _ => false

def mentionsTidy (e : Expr) : Bool :=
  e.getUsedConstants.any isTidy

/-- Add to `found` the tidy constants of `e` outside proofs: subterms whose type is a proposition,
and the type and value of a `let` or `have` whose type is a proposition. A subterm whose type
cannot be inferred counts as a non-proof. -/
partial def tidyOutsideProofs (found : IO.Ref NameSet) (e : Expr) : MetaM Unit := do
  unless mentionsTidy e do return
  if ← (try Meta.isProof e catch _ => pure false) then return
  match e with
  | .const n _ => if isTidy n then found.modify (·.insert n)
  | .app f a => tidyOutsideProofs found f; tidyOutsideProofs found a
  | .mdata _ b | .proj _ _ b => tidyOutsideProofs found b
  | .lam n t b bi | .forallE n t b bi =>
    tidyOutsideProofs found t
    Meta.withLocalDecl n bi t fun x => tidyOutsideProofs found (b.instantiate1 x)
  | .letE n t v b _ =>
    unless ← (try Meta.isProp t catch _ => pure false) do
      tidyOutsideProofs found t
      tidyOutsideProofs found v
    Meta.withLetDecl n t v fun x => tidyOutsideProofs found (b.instantiate1 x)
  | _ => pure ()

/-- `tidyOutsideProofs` for the exposed bodies of the definitions `names` of `modules`, which are
imported (at the exported level, as by a client) from the search path of `lake env` and
`libDir`. -/
unsafe def tidyBodies (libDir : System.FilePath) (modules : Array Name) (names : Array Name) :
    IO (NameMap (Array String)) := do
  if names.isEmpty then return {}
  initSearchPath (← findSysroot) [libDir]
  let env ← importModules (modules.map ({ module := · })) {} (level := .exported)
  let ctx : Core.Context := { fileName := "<QualityReport>", fileMap := default }
  let mut result : NameMap (Array String) := {}
  for n in names do
    let some (.defnInfo v) := env.find? n
      | throw <| IO.userError s!"cannot find the exposed body of {n}"
    let found ← IO.mkRef {}
    discard <| (tidyOutsideProofs found v.value).toIO ctx { env }
    result := result.insert n ((← found.get).toArray.map toString)
  return result

/-- The declarations named by entries of the extensions whose names end in one of `suffixes`.
Every such extension is a `MapDeclarationExtension`, whose entries are pairs headed by a name. -/
unsafe def entryNames (entries : Array (Name × Array EnvExtensionEntry)) (suffixes : List String) :
    NameSet := Id.run do
  let mut names : NameSet := {}
  for (ext, es) in entries do
    if let .str _ s := ext then
      if suffixes.contains s then
        for e in es do
          names := names.insert (unsafeCast e : Name × Unit).1
  return names

unsafe def declRanges (entries : Array (Name × Array EnvExtensionEntry)) :
    NameMap DeclarationRanges := Id.run do
  let mut ranges : NameMap DeclarationRanges := {}
  for (ext, es) in entries do
    if ext == `Lean.declRangeExt then
      for e in es do
        let (n, r) := (unsafeCast e : Name × DeclarationRanges)
        ranges := ranges.insert n r
  return ranges

def rangeJson (r : DeclarationRanges) : Json :=
  let a := r.range
  let s := r.selectionRange
  toJson #[a.pos.line, a.pos.column, a.endPos.line, a.endPos.column,
    s.pos.line, s.pos.column, s.endPos.line, s.endPos.column]

/-- Rename universe parameters positionally, so that alpha-equivalence ignores their names. -/
def normalize (c : ConstantInfo) (e : Expr) : Expr :=
  let us := c.levelParams.length.fold (fun i _ acc => acc.push (Level.param (.num `u i))) #[]
  e.instantiateLevelParams c.levelParams us.toList

/-- Replace each predicate of `canon` by its plain counterpart, without universe levels. -/
def canonicalize (canon : NameMap Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n _ => (canon.find? n).map (Expr.const · [])
    | _ => none

/-- `1` for an application of a listed tidy predicate, `2` for another mention of a tidy constant,
`0` otherwise. -/
def tidyFlag (preds : NameSet) (t : Expr) : Nat :=
  match t.consumeMData.getAppFn with
  | .const n _ => if preds.contains n then 1 else if t.getUsedConstants.any isTidy then 2 else 0
  | _ => if t.getUsedConstants.any isTidy then 2 else 0

def binderCode : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

/-- The flags of the leading binders and of the conclusion of a type. -/
partial def signature (preds : NameSet) (e : Expr) (acc : Array Json := #[]) : Json :=
  match e with
  | .forallE _ t b bi => signature preds b (acc.push (toJson #[binderCode bi, tidyFlag preds t]))
  | .mdata _ b => signature preds b acc
  | _ => Json.arr #[Json.arr acc, toJson (tidyFlag preds e)]

/-- Parse `tidy=plain,…` into the map sending both names to the plain one. -/
def parseCanon (arg : String) : NameMap Name × NameSet := Id.run do
  let mut canon : NameMap Name := {}
  let mut preds : NameSet := {}
  for pair in arg.splitOn "," do
    if let [tidy, plain] := pair.splitOn "=" then
      canon := (canon.insert tidy.toName plain.toName).insert plain.toName plain.toName
      preds := preds.insert tidy.toName
  return (canon, preds)

unsafe def run (libDir : System.FilePath) (pairs : Option String := none) : IO Unit := do
  let (canon, preds) := parseCanon (pairs.getD "")
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut theorems : Std.HashMap Expr (Array (String × Name)) := {}
  let mut defs : Std.HashMap (Expr × Expr) (Array (String × Name)) := {}
  -- The mapped regions must stay alive while `theorems` and `defs` refer to their expressions.
  let mut regions : Array CompactedRegion := #[]
  -- Rows of exposed definitions whose body mentions a tidy constant wait for `tidyBodies`.
  let mut deferred : Array (Name × List (String × Json)) := #[]
  let mut bodyModules : NameSet := {}
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let mod := line.trimAscii.toString
    if mod.isEmpty then continue
    let base := (libDir / System.FilePath.mk (mod.replace "." "/")).addExtension "olean"
    -- Ordinary test/guide-style imports without `module` use one complete .olean, whereas
    -- the library's `module` files split exported/server/private parts. Do not silently accept
    -- a partially missing split output as a classic module.
    let split ← (base.addExtension "private").pathExists
    let server ← (base.addExtension "server").pathExists
    unless split == server do
      throw <| IO.userError s!"incomplete split module outputs for {base}"
    let paths := if split then #[base, base.addExtension "server", base.addExtension "private"]
      else #[base]
    let parts ← readModuleDataParts paths
    let some (exportedData, r0) := parts[0]? | throw <| IO.userError s!"cannot read {base}"
    unless exportedData.isModule == split do
      throw <| IO.userError s!"incomplete split module outputs for {base}"
    let some (fullData, r2) := parts[if split then 2 else 0]? |
      throw <| IO.userError s!"cannot read private data of {base}"
    regions := regions ++ #[r0, r2]
    let mut exported : Std.HashMap Name ConstantInfo := {}
    for c in exportedData.constants do
      exported := exported.insert c.name c
    let docs := entryNames fullData.entries
      ["docStringExt", "versoDocStringExt", "inheritDocStringExt"]
    let ranges := declRanges fullData.entries
    let sameModule : NameSet := fullData.constNames.foldl (·.insert ·) {}
    for c in fullData.constants do
      let e := exported[c.name]?
      let tidy := c.type.getUsedConstants.filter isTidy |>.map (·.toString)
      let uses := match e with
        | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some ec => ec.type.getUsedConstants
        | none => #[]
      let uses := uses.filter (fun n => n != c.name && sameModule.contains n) |>.toList.eraseDups
      let mut row : List (String × Json) := [
        ("n", c.name.toString), ("m", mod), ("k", kindOf c), ("e", (e.map kindOf).getD ""),
        ("doc", docs.contains c.name), ("tidy", toJson tidy),
        ("u", toJson (uses.map (·.toString))),
        ("r", (ranges.find? c.name).map rangeJson |>.getD .null)]
      if pairs.isSome then
        if let some ec := e then
          let hash := (canonicalize canon (normalize ec ec.type)).hash
          row := row ++ [("ph", toJson (toString hash))]
        if c.type.getUsedConstants.any preds.contains then
          row := row ++ [("sg", signature preds c.type)]
      let tidyBody := match e with
        | some (.defnInfo v) => mentionsTidy v.value
        | _ => false
      if tidyBody then
        deferred := deferred.push (c.name, row)
        bodyModules := bodyModules.insert mod.toName
      else
        stdout.putStrLn <| Json.compress <| Json.mkObj (row ++ [("tb", Json.arr #[])])
      if let some ec := e then
        unless c.name.isInternalDetail do
          match c, ec with
          | .thmInfo _, _ =>
            let key := normalize ec ec.type
            theorems := theorems.insert key ((theorems.getD key #[]).push (mod, c.name))
          | .defnInfo _, .defnInfo v =>
            let key := (normalize ec ec.type, normalize ec v.value)
            defs := defs.insert key ((defs.getD key #[]).push (mod, c.name))
          | _, _ => pure ()
  let bodies ← tidyBodies libDir bodyModules.toArray (deferred.map (·.1))
  for (n, row) in deferred do
    let tb := (bodies.find? n).getD #[]
    stdout.putStrLn <| Json.compress <| Json.mkObj (row ++ [("tb", toJson tb)])
  let emit (kind : String) (group : Array (String × Name)) : IO Unit := do
    if (group.map (·.1)).toList.eraseDups.length > 1 then
      stdout.putStrLn <| Json.compress <| Json.mkObj [
        ("dup", toJson (group.map fun (m, n) => #[m, n.toString])), ("k", kind)]
  for (_, group) in theorems do emit "thm" group
  for (_, group) in defs do emit "def" group
  -- Keep the regions reachable until every expression has been used.
  if regions.isEmpty then stdout.flush

/-- Print the exported constants and `export` aliases of `roots` and their transitive imports,
found through the search path that `lake env` sets, then `--tokens--` and their parser tokens. -/
unsafe def names (roots : List Name) : IO Unit := do
  initSearchPath (← findSysroot)
  let stdout ← IO.getStdout
  let mut seen : NameSet := {}
  let mut todo := roots.toArray
  -- The mapped regions stay alive until the end of the program.
  let mut regions : Array CompactedRegion := #[]
  let mut tokens : Std.HashSet String := {}
  while h : todo.size > 0 do
    let mod := todo.back
    todo := todo.pop
    if seen.contains mod then continue
    seen := seen.insert mod
    let (data, region) ← readModuleData (← findOLean mod)
    regions := regions.push region
    for i in data.imports do
      unless seen.contains i.module do todo := todo.push i.module
    for n in data.constNames do
      unless n.isInternalDetail do stdout.putStrLn n.toString
    for (ext, es) in data.entries do
      if ext == `Lean.aliasExtension then
        for e in es do
          stdout.putStrLn (unsafeCast e : Name × Name).1.toString
      if ext == `Lean.Parser.parserExtension then
        for e in es do
          let entry :=
            match (unsafeCast e : ScopedEnvExtension.Entry Parser.ParserExtension.OLeanEntry) with
            | .global a => a
            | .scoped _ a => a
          if let .token t := entry then tokens := tokens.insert t
  stdout.putStrLn "--tokens--"
  for t in tokens do stdout.putStrLn t
  if regions.isEmpty then stdout.flush

end ComplexityScripts.QualityReport

unsafe def main (args : List String) : IO Unit :=
  if args.head? == some "--names" then
    ComplexityScripts.QualityReport.names (args.drop 1 |>.map String.toName)
  else
    ComplexityScripts.QualityReport.run (args.headD ".lake/build/lib/lean") args[1]?
