/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (project validation tooling)
import Lean

/-!
# Candidate parallel definitions and duplicate statements for `scripts/parallel_defs.py`

Run as `lake env lean --run scripts/ParallelDefs.lean <lib-dir> <min-size> <max-shared>`, with one
request per line on standard input:

* `env M`: read module `M` from `<lib-dir>` as part of the environment;
* `lines M a-b,c-d`: read `M`, and examine its declarations whose code (from the line of the
  declared name to the end, so not the docstring) overlaps one of the 1-based line ranges;
  `lines M *` examines the whole module;
* `decl N`: examine the declaration `N`, wherever it is in the environment;
* `theorems`: compare the statements of theorems instead of the bodies of definitions (see
  "Duplicate statements" below);
* `external`: with `theorems`, also compare with the theorems of every module that the listed
  modules import, directly or not, and that is not listed itself: Lean core, Batteries, Mathlib,
  cslib and the other dependencies, found through `LEAN_PATH`.

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

## Duplicate statements

With `theorems`, the environment is every theorem of the listed modules, private ones included;
instances, deprecated theorems and the theorems that Lean generates (equation lemmas, `injEq`,
`induct`, …) are left out, and the theorems examined through `lines` include the private ones.
Two theorems state the same thing when their *statement keys* are equal. The key of a statement
(its type) is the type with

* binder names and kinds, universe levels (only whether a sort is `Prop` is kept) and metadata
  erased; bound variables keep their de Bruijn indices, so `∀ a b, a ≤ b` and `∀ a b, b ≤ a` stay
  apart;
* the binders of the leading `∀`s reordered (`canonicalBinders`): the premises, which nothing
  after them depends on, last, and each other instance-implicit binder as early as the binders it
  depends on allow, so that the order of hypotheses and of instance arguments does not matter;
* the notations `a ≥ b`, `a > b` and `a ≠ b` unfolded into `b ≤ a`, `b < a` and `¬ a = b`, as
  Lean defines them, the two sides of each `=` and `↔` put in a fixed order, and the default
  values of `optParam` and `autoParam` arguments dropped.

It prints one line per group of two or more theorems with the same key, at least one of them
examined, by decreasing size of the key: `{"group": size of the key (nodes counted as a tree),
"exact": whether the types are equal up to the first point alone, "thms": [{"n": name,
"m": module, "l": line, "p": private, "x": examined, "al": c or null}], "ext": [{"n": name,
"m": module}]}`. Here `al` is `c` when the proof is just the constant `c` applied to bound
variables (an alias), and `ext` lists at most five public theorems of the imported modules with
the same key. The last line is
`{"examined": n, "theorems": t, "modules": m, "external": e, "missing": […]}`, where `e` counts
the imported modules read.
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

/-- Last name components of the theorems that Lean generates for a declaration, besides those
that `isGenerated` recognizes. -/
def generatedTheoremSuffixes : List String :=
  ["injEq", "inj", "induct", "induct_unfolding", "mutual_induct", "fun_cases",
    "fun_cases_unfolding", "congr_simp"]

/-- Whether a theorem name, without its private prefix, is one Lean generates. -/
def isGeneratedTheorem (n : Name) : Bool :=
  isGenerated n ||
    match privateToUserName n with
    | .str _ s => generatedTheoremSuffixes.contains s
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

/-- The requests on standard input. -/
structure Requests where
  modules : Array String := #[]
  lineRequests : Std.HashMap String (Option (Array (Nat × Nat))) := {}
  wanted : NameSet := {}
  theorems : Bool := false
  external : Bool := false

def readRequests : IO Requests := do
  let stdin ← IO.getStdin
  let mut r : Requests := {}
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match (line.trimAscii.toString.splitOn " ").filter (· ≠ "") with
    | ["env", m] => r := { r with modules := r.modules.push m }
    | ["lines", m, spec] =>
      r := { r with modules := r.modules.push m
                    lineRequests := r.lineRequests.insert m (parseRanges spec) }
    | ["decl", n] => r := { r with wanted := r.wanted.insert n.toName }
    | ["theorems"] => r := { r with theorems := true }
    | ["external"] => r := { r with external := true }
    | [] => pure ()
    | _ => throw <| IO.userError s!"cannot parse the request {line.trimAscii}"
  return r

/-- A listed module read from its build outputs: the part holding all its declarations, their
ranges, and the declarations to leave out. -/
structure Module where
  name : String
  data : ModuleData
  ranges : NameMap DeclarationRanges
  skip : NameSet

/-- Read the listed modules, and the names of those without build outputs. The mapped regions must
stay alive while the declarations refer to their expressions, so they are returned too. -/
unsafe def readModules (libDir : System.FilePath) (modules : Array String) :
    IO (Array Module × Array String × Array CompactedRegion) := do
  let mut regions : Array CompactedRegion := #[]
  let mut missing : Array String := #[]
  let mut out : Array Module := #[]
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
    out := out.push
      { name := mod, data, ranges := declRanges data.entries, skip := skipped data.entries }
  return (out, missing, regions)

/-- Whether a declaration's code, from its declared name to its end, overlaps the lines requested
for its module. -/
def inLines (request : Option (Option (Array (Nat × Nat)))) (range : Option DeclarationRanges) :
    Bool :=
  match request, range with
  | some none, _ => true
  | some (some rs), some r =>
    rs.any fun (lo, hi) => lo ≤ r.range.endPos.line && r.selectionRange.pos.line ≤ hi
  | _, _ => false

unsafe def runDefs (req : Requests) (libDir : System.FilePath) (minSize maxShared : Nat) :
    IO Unit := do
  let stdout ← IO.getStdout
  let wanted := req.wanted
  let (mods, missing, regions) ← readModules libDir req.modules
  let mut decls : Array Decl := #[]
  for m in mods do
    let request := req.lineRequests[m.name]?
    let mut consts : Std.HashMap Name ConstantInfo := {}
    for c in m.data.constants do
      consts := consts.insert c.name c
    for c in m.data.constants do
      -- Instances, projections and deprecated declarations, with definitions generated in them.
      let skipped := m.skip.contains c.name || m.skip.contains c.name.getPrefix
      if isGenerated c.name || (skipped && !wanted.contains c.name) then continue
      let (body, self) ← match c with
        | .defnInfo v => pure (v.value, ({} : NameSet))
        | .inductInfo v =>
          let types := v.ctors.filterMap fun n => (consts[n]?).map (·.type)
          pure (mkAppN (.const `_ctors []) types.toArray, v.all.foldl (·.insert ·) {})
        | _ => continue
      let range := m.ranges.find? c.name
      let priv := isPrivateName c.name
      let examined := wanted.contains c.name || (inLines request range && !priv)
      let uses := match c with
        | .inductInfo v => v.ctors.foldl (init := {}) fun s n =>
            ((consts[n]?).map (·.type.getUsedConstants) |>.getD #[]).foldl (·.insert ·) s
        | _ => body.getUsedConstants.foldl (·.insert ·) {}
      decls := decls.push {
        name := c.name, module := m.name, priv, examined, self, body, uses
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
    ("modules", toJson mods.size), ("missing", toJson missing)]
  -- Keep the regions reachable until every expression has been used.
  if regions.isEmpty then stdout.flush

/-! ### Statement keys -/

namespace Statement

/-- `Type`, standing for every sort that is not `Prop`. -/
def typeSort : Expr := .sort (.succ .zero)

/-- An application with `≥`, `>` and `≠` unfolded, the sides of `=` and `↔` in a fixed order, and
the default value of an `optParam` or `autoParam` dropped. -/
def unfold (f : Expr) (args : Array Expr) : Expr :=
  match f, args with
  | .const ``GE.ge _, #[α, i, a, b] => mkApp4 (.const ``LE.le []) α i b a
  | .const ``GT.gt _, #[α, i, a, b] => mkApp4 (.const ``LT.lt []) α i b a
  | .const ``Ne _, #[α, a, b] => .app (.const ``Not []) (eq α a b)
  | .const ``Eq _, #[α, a, b] => eq α a b
  | .const ``Iff _, #[a, b] => if b.lt a then mkApp2 f b a else mkApp2 f a b
  | .const ``optParam _, #[α, _] => α
  | .const ``autoParam _, #[α, _] => α
  | _, _ => mkAppN f args
where
  eq (α a b : Expr) : Expr :=
    if b.lt a then mkApp3 (.const ``Eq []) α b a else mkApp3 (.const ``Eq []) α a b

/-- Erase binder names, binder kinds, universe levels (keeping whether a sort is `Prop`) and
metadata, keeping bound variables and the sharing of `e`. With `norm`, also `unfold` every
application. -/
unsafe def erase (norm : Bool) (e : Expr) : StateM (Std.HashMap USize Expr) Expr := do
  let key := ptrAddrUnsafe e
  if let some r := (← get)[key]? then return r
  let r ← match e with
    | .sort l => pure (if l.normalize.isZero then .sort .zero else typeSort)
    | .const n _ => pure (.const n [])
    | .app .. => do
      let f ← erase norm e.getAppFn
      let args ← e.getAppArgs.mapM (erase norm)
      pure (if norm then unfold f args else mkAppN f args)
    | .lam _ t b _ => do pure (.lam `x (← erase norm t) (← erase norm b) .default)
    | .forallE _ t b _ => do pure (.forallE `x (← erase norm t) (← erase norm b) .default)
    | .letE _ t v b _ => do
      pure (.letE `x (← erase norm t) (← erase norm v) (← erase norm b) false)
    | .mdata _ b => erase norm b
    | .proj s i b => do pure (.proj s i (← erase norm b))
    | e => pure e
  modify (·.insert key r)
  return r

/-- A binder of a `∀`. -/
structure Binder where
  name : Name
  type : Expr
  info : BinderInfo
  deriving Inhabited

/-- The binders of the leading `∀`s of `e`, and what follows them. -/
partial def telescope (e : Expr) (bs : Array Binder := #[]) : Array Binder × Expr :=
  match e with
  | .forallE name type b info => telescope b (bs.push { name, type, info })
  | .mdata _ b => telescope b bs
  | e => (bs, e)

/-- `e` with the binders of its leading `∀`s in a canonical order. The *premises*, the binders that
no later binder and nothing after the binders depends on (hypotheses, mostly), come last, ordered
by their erased types. Each other instance-implicit binder comes as early as the binders it
depends on allow, those that become available together ordered by their erased types. The other
binders keep their order. Ties keep the original order. -/
unsafe def canonicalBinders (e : Expr) : Expr := Id.run do
  let (bs, body) := telescope e
  let n := bs.size
  if n < 2 then return e
  let xs : Array Expr := (Array.range n).map fun i => .fvar ⟨.num `_x i⟩
  let types := (Array.range n).map fun i => bs[i]!.type.instantiateRevRange 0 i xs
  let deps := (Array.range n).map fun i =>
    (Array.range i).filter fun j => bs[i]!.type.hasLooseBVar (i - 1 - j)
  let premise := (Array.range n).map fun i =>
    !body.hasLooseBVar (n - 1 - i) && !deps.any (·.contains i)
  let float := (Array.range n).map fun i => bs[i]!.info.isInstImplicit && !premise[i]!
  let premises := (Array.range n).filter (premise[·]!)
  let mut pos : Array (Option Nat) := Array.replicate n none
  let mut order : Array Nat := #[]
  let mut nextSpine := 0
  -- The type of binder `i` written over the positions of the binders placed so far, compared
  -- erased.
  let keyOf (pos : Array (Option Nat)) (i : Nat) : Expr :=
    let marks := pos.map fun p => Expr.fvar ⟨.num `_p (p.getD n)⟩
    (erase true (types[i]!.replaceFVars xs marks)).run' {}
  for _ in [0:n - premises.size] do
    -- The available instance binder with the least type, otherwise the next other binder, whose
    -- dependencies are then all placed.
    let mut pick : Option (Nat × Expr) := none
    for i in [0:n] do
      if !float[i]! || pos[i]!.isSome || !deps[i]!.all (pos[·]!.isSome) then continue
      let key := keyOf pos i
      if pick.all fun (_, k) => key.lt k then pick := some (i, key)
    let mut i := 0
    match pick with
    | some (j, _) => i := j
    | none =>
      while float[nextSpine]! || premise[nextSpine]! do nextSpine := nextSpine + 1
      i := nextSpine
      nextSpine := nextSpine + 1
    pos := pos.set! i (some order.size)
    order := order.push i
  -- The premises depend only on placed binders.
  let keyed := premises.map fun i => (i, keyOf pos i)
  order := order ++ (keyed.qsort fun (i, k) (j, l) => k.lt l || (!l.lt k && i < j)).map (·.1)
  if order == Array.range n then return e
  let ys := order.map (xs[·]!)
  let mut r := (body.instantiateRev xs).abstract ys
  for k' in [0:n] do
    let k := n - 1 - k'
    let b := bs[order[k]!]!
    r := .forallE b.name (types[order[k]!]!.abstractRange k ys) r b.info
  return r

/-- The key of a statement up to binder names and kinds, universe levels and metadata only. -/
unsafe def exactKey (type : Expr) : Expr := (erase false type).run' {}

/-- The statement key (see the module documentation). -/
unsafe def key (type : Expr) : Expr := (erase true (canonicalBinders type)).run' {}

/-- `e` with every `optParam` and `autoParam` replaced by its type, dropping the default value as
`unfold` does. -/
partial def dropDefaults (e : Expr) : Expr :=
  e.replace fun e =>
    if e.isAppOfArity ``optParam 2 || e.isAppOfArity ``autoParam 2 then
      some (dropDefaults e.appFn!.appArg!)
    else none

/-- A hash of the constants of a statement, with `≥`, `>` and `≠` counted as what they unfold to
and the default values of arguments left out: equal for statements with equal keys, and cheap to
compute. -/
def fingerprint (type : Expr) : UInt64 :=
  let s : NameSet := (dropDefaults type).getUsedConstants.foldl (init := {}) fun s c =>
    if c == ``GE.ge then s.insert ``LE.le
    else if c == ``GT.gt then s.insert ``LT.lt
    else if c == ``Ne then (s.insert ``Not).insert ``Eq
    else s.insert c
  s.foldl (fun h c => mixHash h (hash c)) 7

/-- The tree size of an expression, computed once per shared node. -/
unsafe def treeSize (e : Expr) : StateM (Std.HashMap USize Nat) Nat := do
  let key := ptrAddrUnsafe e
  if let some n := (← get)[key]? then return n
  let n ← match e with
    | .app f a => do pure (1 + (← treeSize f) + (← treeSize a))
    | .lam _ t b _ | .forallE _ t b _ => do pure (1 + (← treeSize t) + (← treeSize b))
    | .letE _ t v b _ => do pure (1 + (← treeSize t) + (← treeSize v) + (← treeSize b))
    | .proj _ _ b => do pure (1 + (← treeSize b))
    | _ => pure 1
  modify (·.insert key n)
  return n

end Statement

/-- A theorem of the listed modules. -/
structure Thm where
  name : Name
  module : String
  line : Nat
  examined : Bool
  type : Expr
  proof : Expr
  fingerprint : UInt64
  deriving Inhabited

/-- A theorem of an imported module with the key of a group. -/
structure External where
  name : Name
  module : Name
  exact : Expr

/-- The module data of an imported module, or `none` when it cannot be found or read. -/
def readImported (mod : Name) : IO (Option (ModuleData × CompactedRegion)) := do
  try
    return some (← readModuleData (← findOLean mod))
  catch _ =>
    return none

/-- Read the modules that `roots` import, directly or not, other than those in `listed`, and pass
each of their public theorems whose fingerprint is in `fingerprints` to `found`, with its module
and type. Returns the number of modules read and their regions. -/
unsafe def scanImports (roots : Array Import) (listed : NameSet)
    (fingerprints : Std.HashSet UInt64) (found : Name → Name → Expr → IO Unit) :
    IO (Nat × Array CompactedRegion) := do
  initSearchPath (← findSysroot)
  let mut queue := roots
  let mut seen := listed
  let mut regions : Array CompactedRegion := #[]
  repeat
    let some imp := queue.back? | break
    queue := queue.pop
    if seen.contains imp.module then continue
    seen := seen.insert imp.module
    let some (data, region) ← readImported imp.module | continue
    regions := regions.push region
    queue := queue ++ data.imports
    let skip := skipped data.entries
    for c in data.constants do
      -- The public part of a module exports its theorems as axioms.
      unless c matches .thmInfo _ | .axiomInfo _ do continue
      if isPrivateName c.name || isGeneratedTheorem c.name || skip.contains c.name then continue
      if fingerprints.contains (Statement.fingerprint c.type) then
        found c.name imp.module c.type
  return (regions.size, regions)

unsafe def runTheorems (req : Requests) (libDir : System.FilePath) : IO Unit := do
  let stdout ← IO.getStdout
  let (mods, missing, regions) ← readModules libDir req.modules
  let mut thms : Array Thm := #[]
  for m in mods do
    let request := req.lineRequests[m.name]?
    for c in m.data.constants do
      let .thmInfo v := c | continue
      let wanted := req.wanted.contains (privateToUserName c.name)
      if isGeneratedTheorem c.name || (m.skip.contains c.name && !wanted) then continue
      let range := m.ranges.find? c.name
      thms := thms.push {
        name := c.name, module := m.name, examined := wanted || inLines request range
        line := (range.map (·.selectionRange.pos.line)).getD 0
        type := v.type, proof := v.value, fingerprint := Statement.fingerprint v.type }
  -- Theorems with the key of an examined one have its fingerprint; only those are keyed.
  let examined := thms.filter (·.examined)
  let fingerprints : Std.HashSet UInt64 := examined.foldl (·.insert ·.fingerprint) {}
  let mut groups : Std.HashMap Expr (Array Nat) := {}
  let mut exact : Std.HashMap Nat Expr := {}
  for i in [0:thms.size] do
    let t := thms[i]!
    unless fingerprints.contains t.fingerprint do continue
    let key := Statement.key t.type
    groups := groups.insert key ((groups.getD key #[]).push i)
    exact := exact.insert i (Statement.exactKey t.type)
  -- Only the groups with an examined theorem are reported.
  groups := groups.filter fun _ is => is.any (thms[·]!.examined)
  let found ← IO.mkRef ({} : Std.HashMap Expr (Array External))
  let mut externalCount := 0
  let mut externalRegions : Array CompactedRegion := #[]
  if req.external then
    let roots := mods.foldl (fun acc m => acc ++ m.data.imports) #[]
    let listed := req.modules.foldl (fun s m => s.insert m.toName) {}
    let (count, rs) ← scanImports roots listed fingerprints fun name module type => do
      let key := Statement.key type
      if groups.contains key then
        found.modify fun m => m.insert key
          ((m.getD key #[]).push { name, module, exact := Statement.exactKey type })
    externalCount := count
    externalRegions := rs
  let externals ← found.get
  let mut rows : Array (Nat × String × Json) := #[]
  for (key, is) in groups do
    let ext := externals.getD key #[]
    if is.size + ext.size < 2 then continue
    let exact0 := exact[is[0]!]!
    let isExact := is.all (exact[·]! == exact0) && ext.all (·.exact == exact0)
    let size : Nat := (Statement.treeSize key).run' {}
    let members := is.map fun i =>
      let t := thms[i]!
      Json.mkObj [("n", nameJson t.name), ("m", toJson t.module), ("l", toJson t.line),
        ("p", toJson (isPrivateName t.name)), ("x", toJson t.examined),
        ("al", match aliasTarget? t.proof with | some a => nameJson a | none => Json.null)]
    let ext := (ext.extract 0 5).map fun x =>
      Json.mkObj [("n", nameJson x.name), ("m", toJson x.module.toString)]
    rows := rows.push (size, (privateToUserName thms[is[0]!]!.name).toString,
      Json.mkObj [("group", toJson size), ("exact", toJson isExact), ("thms", toJson members),
        ("ext", toJson ext)])
  let sorted := rows.qsort fun (s, n, _) (s', n', _) => s > s' || (s == s' && n < n')
  for (_, _, row) in sorted do
    stdout.putStrLn row.compress
  stdout.putStrLn <| Json.compress <| Json.mkObj [("examined", toJson examined.size),
    ("theorems", toJson thms.size), ("modules", toJson mods.size),
    ("external", toJson externalCount), ("missing", toJson missing)]
  -- Keep the regions reachable until every expression has been used.
  if regions.isEmpty && externalRegions.isEmpty then stdout.flush

unsafe def run (libDir : System.FilePath) (minSize maxShared : Nat) : IO Unit := do
  let req ← readRequests
  if req.theorems then runTheorems req libDir else runDefs req libDir minSize maxShared

end ComplexityScripts.ParallelDefs

unsafe def main (args : List String) : IO Unit := do
  let libDir := args.headD ".lake/build/lib/lean"
  let minSize := (args[1]?.bind String.toNat?).getD 300
  let maxShared := (args[2]?.bind String.toNat?).getD 8
  ComplexityScripts.ParallelDefs.run libDir minSize maxShared
