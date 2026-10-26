/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (project validation tooling)
import Lean

/-!
# Candidate parallel definitions for `scripts/parallel_defs.py`

Run as `lake env lean --run scripts/ParallelDefs.lean <lib-dir> <min-size> <max-shared>`, with one
request per line on standard input:

* `env M`: read module `M` from `<lib-dir>` as part of the environment;
* `lines M a-b,c-d`: read `M`, and examine its declarations whose code (from the line of the
  declared name to the end, so not the docstring) overlaps one of the 1-based line ranges;
  `lines M *` examines the whole module;
* `decl N`: examine the declaration `N`, wherever it is in the environment.

It reads the built `.olean` files (all three parts of a split module) without importing them. The
environment is every `def`, `abbrev`, `structure`, `class` and `inductive` of the listed modules,
private ones included; instances, structure projections, deprecated declarations and constants
that Lean generates are left out. The declarations examined through `lines` are its public ones.

The *body* of a definition is its value, and that of an inductive type is the list of its
constructors' types, with the type itself replaced by a placeholder. Bodies are anonymized: bound
and free variables, universe levels, binder names, the types of `fun` and `let` binders and
metadata are erased, so two bodies that differ in their carrier types, variable names or argument
order can still share large subterms.

For each examined declaration `a` and each other declaration `b` of the environment, the tool
finds the largest subterm, of at least `<min-size>` nodes counted as a tree, that both anonymized
bodies contain and that at most `<max-shared>` declarations of the environment contain in all, so
that common plumbing is ignored. It skips pairs where one body mentions the other or a constructor
or field of it (a wrapper or a specialization, which is how reuse looks) and pairs where one name
extends the other. It prints, by decreasing size, one JSON line per remaining pair:
`{"pair": size, "a": …, "am": module, "al": line, "b": …, "bm": …, "bl": …, "bp": b is private,
"bx": b is examined too, "as": size of a's body, "bs": size of b's body,
"c": [constants of the shared subterm]}`. Names are printed without their private prefix, and
lines are those of the declared names.

Before the pairs, it prints `{"alias": a, "am": …, "al": …, "b": …, "bm": …, "bl": …, "bp": …}` for
each examined definition whose body, after its leading `fun`s, is another declaration `b` of the
environment applied to bound variables only, such as `abbrev MCSPAt s := GapMCSP.yesSet s`: a
second name for an existing notion. The last line is
`{"examined": n, "modules": m, "missing": [requested modules without build outputs]}`.
-/
open Lean

namespace ComplexityScripts.ParallelDefs

/-- Last name components of the definitions that Lean generates for a declaration. -/
def generatedSuffixes : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow", "noConfusion",
    "noConfusionType", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "mk", "sizeOf_spec",
    "proxyType", "proxyTypeEquiv", "eq_def", "eq_unfold"]

/-- Whether a name, without its private prefix, is one Lean generates. -/
def isGenerated (n : Name) : Bool :=
  let n := privateToUserName n
  n.isInternalDetail || n.hasMacroScopes ||
    match n with
    | .str _ s => generatedSuffixes.contains s
    | _ => false

/-- Erase variables, universe levels, binder names, the types of `fun` and `let` binders and
metadata, keeping the sharing of `e`. Constants in `self` (an inductive type's own names) become
`_self`. -/
unsafe def anon (self : NameSet) (e : Expr) : StateM (Std.HashMap USize Expr) Expr := do
  let key := ptrAddrUnsafe e
  if let some r := (← get)[key]? then return r
  let r ← match e with
    | .bvar _ | .fvar _ | .mvar _ => pure (.bvar 0)
    | .sort _ => pure (.sort .zero)
    | .const n _ => pure (.const (if self.contains n then `_self else n) [])
    | .app f a => do pure (.app (← anon self f) (← anon self a))
    | .lam _ _ b _ => do pure (.lam `x (.bvar 0) (← anon self b) .default)
    | .forallE _ t b _ => do pure (.forallE `x (← anon self t) (← anon self b) .default)
    | .letE _ _ v b _ => do pure (.letE `x (.bvar 0) (← anon self v) (← anon self b) false)
    | .lit l => pure (.lit l)
    | .mdata _ b => anon self b
    | .proj s i b => do pure (.proj s i (← anon self b))
  modify (·.insert key r)
  return r

/-- Tree sizes of the subterms of an anonymized body, computed once per shared node, and the
subterms of at least `minSize` nodes by hash. -/
structure Sizes where
  memo : Std.HashMap USize Nat := {}
  big : Std.HashMap UInt64 (Nat × Expr) := {}

unsafe def sizes (minSize : Nat) (e : Expr) : StateM Sizes Nat := do
  let key := ptrAddrUnsafe e
  if let some n := (← get).memo[key]? then return n
  let n ← match e with
    | .app f a => do pure (1 + (← sizes minSize f) + (← sizes minSize a))
    | .lam _ t b _ | .forallE _ t b _ => do pure (1 + (← sizes minSize t) + (← sizes minSize b))
    | .letE _ t v b _ => do
      pure (1 + (← sizes minSize t) + (← sizes minSize v) + (← sizes minSize b))
    | .proj _ _ b => do pure (1 + (← sizes minSize b))
    | _ => pure 1
  modify fun s => { s with
    memo := s.memo.insert key n
    big := if n ≥ minSize then s.big.insert e.hash (n, e) else s.big }
  return n

/-- The size of an anonymized body and its subterms of at least `minSize` nodes, by hash. -/
unsafe def bigSubterms (minSize : Nat) (self : NameSet) (body : Expr) :
    Nat × Std.HashMap UInt64 (Nat × Expr) :=
  let (a, _) := (anon self body).run {}
  let (n, s) := (sizes minSize a).run {}
  (n, s.big)

/-- The constant `c` when `e` is, after its leading `fun`s, `c` applied to bound variables. -/
partial def aliasTarget? : Expr → Option Name
  | .lam _ _ b _ => aliasTarget? b
  | .mdata _ b => aliasTarget? b
  | e => match e.getAppFn with
    | .const c _ => if e.getAppArgs.all (·.consumeMData.isBVar) then some c else none
    | _ => none

/-- A declaration of the environment. -/
structure Decl where
  name : Name
  module : String
  line : Nat
  priv : Bool
  examined : Bool
  self : NameSet
  body : Expr
  uses : NameSet
  size : Nat := 0
  deriving Inhabited

/-- Whether one of two declarations is built from the other: one body mentions the other (or a
constructor or field of it), or one name extends the other. -/
def related (a b : Decl) : Bool :=
  a.name.isPrefixOf b.name || b.name.isPrefixOf a.name ||
    a.uses.contains b.name || b.uses.contains a.name ||
    a.uses.any (b.name.isPrefixOf ·) || b.uses.any (a.name.isPrefixOf ·)

/-- Parse `a-b,c-d` into line ranges, or `*` into `none` (the whole module). -/
def parseRanges (spec : String) : Option (Array (Nat × Nat)) :=
  if spec == "*" then none else
  some <| (spec.splitOn ",").toArray.filterMap fun r =>
    match r.splitOn "-" with
    | [a, b] => do pure (← a.toNat?, ← b.toNat?)
    | [a] => a.toNat?.map fun a => (a, a)
    | _ => none

unsafe def declRanges (entries : Array (Name × Array EnvExtensionEntry)) :
    NameMap DeclarationRanges := Id.run do
  let mut ranges : NameMap DeclarationRanges := {}
  for (ext, es) in entries do
    if ext == `Lean.declRangeExt then
      for e in es do
        let (n, r) := (unsafeCast e : Name × DeclarationRanges)
        ranges := ranges.insert n r
  return ranges

/-- The instances, structure projections and deprecated declarations of a module. -/
unsafe def skipped (entries : Array (Name × Array EnvExtensionEntry)) : NameSet := Id.run do
  let mut out : NameSet := {}
  for (ext, es) in entries do
    if ext == `Lean.projectionFnInfoExt then
      for e in es do
        out := out.insert (unsafeCast e : Name × ProjectionFunctionInfo).1
    if ext == `Lean.Meta.instanceExtension then
      for e in es do
        let entry := match (unsafeCast e : ScopedEnvExtension.Entry Meta.InstanceEntry) with
          | .global a => a
          | .scoped _ a => a
        if let some n := entry.globalName? then out := out.insert n
    if ext == `Lean.Linter.deprecatedAttr then
      for e in es do
        out := out.insert (unsafeCast e : Name × Linter.DeprecationEntry).1
  return out

def nameJson (n : Name) : Json := toJson (privateToUserName n).toString

unsafe def run (libDir : System.FilePath) (minSize maxShared : Nat) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut modules : Array String := #[]
  let mut lineRequests : Std.HashMap String (Option (Array (Nat × Nat))) := {}
  let mut wanted : NameSet := {}
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match (line.trimAscii.toString.splitOn " ").filter (· ≠ "") with
    | ["env", m] => modules := modules.push m
    | ["lines", m, spec] =>
      modules := modules.push m
      lineRequests := lineRequests.insert m (parseRanges spec)
    | ["decl", n] => wanted := wanted.insert n.toName
    | [] => pure ()
    | _ => throw <| IO.userError s!"cannot parse the request {line.trimAscii}"
  -- The mapped regions must stay alive while the declarations refer to their expressions.
  let mut regions : Array CompactedRegion := #[]
  let mut missing : Array String := #[]
  let mut decls : Array Decl := #[]
  for mod in modules do
    let base := (libDir / System.FilePath.mk (mod.replace "." "/")).addExtension "olean"
    unless ← base.pathExists do
      missing := missing.push mod
      continue
    let split ← (base.addExtension "private").pathExists
    let paths := if split then #[base, base.addExtension "server", base.addExtension "private"]
      else #[base]
    let parts ← readModuleDataParts paths
    regions := regions ++ parts.map (·.2)
    let some (data, _) := parts[if split then 2 else 0]? |
      throw <| IO.userError s!"cannot read {base}"
    let ranges := declRanges data.entries
    let skip := skipped data.entries
    let request := lineRequests[mod]?
    let mut consts : Std.HashMap Name ConstantInfo := {}
    for c in data.constants do
      consts := consts.insert c.name c
    for c in data.constants do
      -- Instances, projections and deprecated declarations, with definitions generated in them.
      let skipped := skip.contains c.name || skip.contains c.name.getPrefix
      if isGenerated c.name || (skipped && !wanted.contains c.name) then continue
      let (body, self) ← match c with
        | .defnInfo v => pure (v.value, ({} : NameSet))
        | .inductInfo v =>
          let types := v.ctors.filterMap fun n => (consts[n]?).map (·.type)
          pure (mkAppN (.const `_ctors []) types.toArray, v.all.foldl (·.insert ·) {})
        | _ => continue
      let range := ranges.find? c.name
      let priv := isPrivateName c.name
      let inLines := match request, range with
        | some none, _ => true
        | some (some rs), some r =>
          rs.any fun (lo, hi) => lo ≤ r.range.endPos.line && r.selectionRange.pos.line ≤ hi
        | _, _ => false
      let examined := wanted.contains c.name || (inLines && !priv)
      let uses := match c with
        | .inductInfo v => v.ctors.foldl (init := {}) fun s n =>
            ((consts[n]?).map (·.type.getUsedConstants) |>.getD #[]).foldl (·.insert ·) s
        | _ => body.getUsedConstants.foldl (·.insert ·) {}
      decls := decls.push {
        name := c.name, module := mod, priv, examined, self, body, uses
        line := (range.map (·.selectionRange.pos.line)).getD 0 }
  -- The large subterms of the examined bodies, with the examined declarations containing them.
  let mut table : Std.HashMap UInt64 (Nat × Expr × Array Nat) := {}
  let mut examinedCount := 0
  let mut index : Std.HashMap Name Nat := {}
  for i in [0:decls.size] do
    index := index.insert decls[i]!.name i
  for i in [0:decls.size] do
    let d := decls[i]!
    unless d.examined do continue
    examinedCount := examinedCount + 1
    if let some t := (aliasTarget? d.body).bind (index[·]?) then
      let dt := decls[t]!
      unless d.name.isPrefixOf dt.name do
        stdout.putStrLn <| Json.compress <| Json.mkObj [("alias", nameJson d.name),
          ("am", toJson d.module), ("al", toJson d.line), ("b", nameJson dt.name),
          ("bm", toJson dt.module), ("bl", toJson dt.line), ("bp", toJson dt.priv)]
    let (n, big) := bigSubterms minSize d.self d.body
    decls := decls.set! i { d with size := n }
    for (h, (sz, e)) in big do
      let (s0, e0, ds) := table.getD h (sz, e, #[])
      table := table.insert h (s0, e0, ds.push i)
  -- Every declaration of the environment containing one of those subterms.
  let mut occurrences : Std.HashMap UInt64 (Array Nat) := {}
  if !table.isEmpty then
    for i in [0:decls.size] do
      let d := decls[i]!
      let (n, big) := bigSubterms minSize d.self d.body
      decls := decls.set! i { d with size := n }
      for (h, _) in big do
        if table.contains h then
          occurrences := occurrences.insert h ((occurrences.getD h #[]).push i)
  -- For each pair, the largest subterm shared by few enough declarations.
  let mut best : Std.HashMap (Nat × Nat) (Nat × Expr) := {}
  for (h, (sz, e, examined)) in table do
    let occs := occurrences.getD h #[]
    if occs.size < 2 || occs.size > maxShared then continue
    for a in examined do
      for b in occs do
        if a == b || (decls[b]!.examined && b < a) then continue
        if related decls[a]! decls[b]! then continue
        if sz > ((best.get? (a, b)).map (·.1)).getD 0 then
          best := best.insert (a, b) (sz, e)
  let pairs := best.toArray.qsort fun ((a, b), (s, _)) ((a', b'), (s', _)) =>
    s > s' || (s == s' && (a < a' || (a == a' && b < b')))
  for ((a, b), (sz, e)) in pairs do
    let da := decls[a]!
    let db := decls[b]!
    let consts := e.getUsedConstants.filter fun n => n != `_self
    stdout.putStrLn <| Json.compress <| Json.mkObj [("pair", toJson sz),
      ("a", nameJson da.name), ("am", toJson da.module), ("al", toJson da.line),
      ("b", nameJson db.name), ("bm", toJson db.module), ("bl", toJson db.line),
      ("bp", toJson db.priv), ("bx", toJson db.examined),
      ("as", toJson da.size), ("bs", toJson db.size),
      ("c", toJson (consts.map (·.toString)))]
  stdout.putStrLn <| Json.compress <| Json.mkObj [("examined", toJson examinedCount),
    ("modules", toJson (modules.size - missing.size)), ("missing", toJson missing)]
  -- Keep the regions reachable until every expression has been used.
  if regions.isEmpty then stdout.flush

end ComplexityScripts.ParallelDefs

unsafe def main (args : List String) : IO Unit := do
  let libDir := args.headD ".lake/build/lib/lean"
  let minSize := (args[1]?.bind String.toNat?).getD 300
  let maxShared := (args[2]?.bind String.toNat?).getD 8
  ComplexityScripts.ParallelDefs.run libDir minSize maxShared
