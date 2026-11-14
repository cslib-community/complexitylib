/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (project validation tooling)
import Lean

/-!
# Security premises about constructed objects, for `scripts/check_security_premises.py`

Run as `lake env lean --run scripts/SecurityPremises.lean <lib-dir> < modules.txt`, with one module
name per line on standard input. It reads the built `.olean` files (all three parts of a split
module) without importing them, so it sees elaborated statements: notation, `do` blocks, dot
notation and coercions are already resolved.

The scanned theorems are the public theorems of the listed modules, other than instances and
those Lean generates, that lie under `CslibFrontier.Crypto` or in the namespace `Cslib.Crypto`.

**Claims.** A hypothesis's *claim atoms* are what remains after its own `∀`s and premises, split
at `∧`, `∃` and `∀ᶠ`. An atom is a *security claim* of one of these kinds:

* `negligible`: `Negligible …`;
* `advantage`: an inequality `a ≤ b`, `a < b`, `a ≥ b` or `a > b` one of whose sides mentions an
  advantage, that is a constant whose last name component is `advantage` or `succProbability` or
  ends in `Advantage`;
* `member`: a membership `x ∈ S`, the shape of an adversary class `𝒟`, unless `S` is a support,
  range or interval (`ignoredContainers`), or a bound predicate applied to arguments, the shape of
  an abstract admissibility class `Admissible x`;
* `efficiency`: a predicate whose last name component starts with `IsPPT` or `IsOraclePPT`;
* `indistinguishable`: a predicate whose last name component contains `Indistinguishable`.

Its *subjects* are the explicit arguments of the predicate (all arguments when the predicate is not
a constant of the listed modules), both sides of the inequality, the element of the membership, or
the arguments of the bound predicate.
An atom of no kind headed by a Prop-valued definition of the listed modules is unfolded, at most
three times; there, only the constructed constants of the definition's arguments count (`unfolded`
kinds). So a notion applied to a constructed object, such as `Secure (reduction A)`, is seen, while
a named assumption such as `F.DDH setup` is not flagged, nor is a notion whose own definition builds
a fixed object of the framework (the dummy adversary of UC emulation).

**Constructed constants.** A constant `c` occurring in a subject, applied to `k` arguments, is
*constructed* when it is a definition (or opaque constant) of the scope above that is not a
structure projection, an instance or generated, whose last name component does not contain `game`
or `experiment` (any case) nor name an advantage, and whose type after `k` arguments, with type
synonyms of the listed modules unfolded, is

* a value whose type is not a distribution or game (`PMF`, `Game`), a number, `Bool`, a sort, `Set`
  or an embedding: so a program, a scheme or adversary structure, or a key;
* or a function whose final result is none of a number, `Bool`, `Prop` or an embedding (a
  predicate, test, numeric function or family of encodings), and which is not an ensemble or game
  family, a function of security parameters `ℕ → … → PMF _` or `→ Game`;
* or a distribution, game, ensemble or game family as above, when one of its `k` arguments is
  explicit and its domain is an *object type*: a type other than a sort, a type variable, a
  function type, a number, `Bool`, `Set`, `PMF` or `Game`, such as an adversary or scheme
  structure. So `simulatorView A`, with `simulatorView : Adversary → ℕ → PMF Bool`, is
  constructed.

Reductions, distinguishers (including `PMF`-valued and `Experiment`-valued ones), simulators,
extractors, key generators, schemes and adapters are constructed; games, experiments, advantages,
ideal laws, predicates and encodings are not. Bound variables (the input adversary, generic
components supplied by the caller) are never constants, so they never count.

**Known gaps.** Review covers these; the fixture in `scripts/test_check_security_premises.py`
pins each one.

* A distribution applied only to numbers or functions counts as infrastructure: a key law at
  fixed parameters (`keyLawOf 3`), or one applied to an adversary given as a function rather than
  a structure.
* A bound that mentions no advantage-named constant, such as `forgeExperiment (reduction A) 0 ≤ ε`,
  is not a security claim.
* A premise whose own definition builds the constructed object in its body, rather than taking it
  as an argument, is not seen.
* A caller-supplied object whose existence is what the theorem should prove (the extractor of a
  proof of knowledge) is a bound variable, so it never counts.
* A realization (below) stated other than as an equation, such as an inequality, a predicate of
  the library or a bundled certified program, or whose constructed side applies the constructed
  constant to no other variable of the theorem, is not seen.

Conversely, a named assumption instantiated at an object of the library, such as `DDH G` for a
group family `G` that the library defines, is flagged through its unfolding. Such a premise is
allowed by the rule and belongs in the baseline with its justification.

A *flagged premise* is a hypothesis with a security claim whose subjects mention a constructed
constant. The conclusion is flagged (as the binder `⊢`) when, under an `∃` reached through `∀` and
`∧`, an advantage inequality applies a constructed constant to an `∃`-bound variable, as in
`∃ m₀ m₁, Adv(A) ≤ Adv(B A m₀ m₁)`: the bound holds only for parameters chosen after the
adversary, so it is not a uniform reduction.

**Realizations.** A premise is also flagged, with the kind `realization`, when the theorem takes
the reduction from the caller as a variable `x` and assumes that `x` realizes the constructed
object. Another premise *certifies* `x`: it has an efficiency or membership claim whose subject is
`x` or a function that applies it (`hD : IsOraclePPT encBool D`, `IsPPTOn … (fun p => test p.1
p.2)`, `D ∈ 𝒟`). The flagged premise is an equation, under its own `∀`s, `∧`, `∃` and `∀ᶠ`, one
side of which mentions `x`; the other side does not, and applies a constructed constant to
another variable of the theorem, such as the adversary, whether or not another premise certifies
that variable too. For example, the Carter–Wegman theorems that #5347 deleted took `hreal : eval
(prfRealGame family D n) = (prfFnDist family n).bind (nonceFnDistinguisher (seed n) (hash n)
(forger n))` beside `hD`, which is flagged with the constant `nonceFnDistinguisher`. An equation
between variables only, such as a word program computing a caller's typed simulator, is not.

It prints one JSON line per theorem with a flagged premise or conclusion,
`{"n": theorem, "m": module, "l": line, "h": [{"b": binder, "k": [kinds], "c": [constructed
constants]}]}`, and finally `{"theorems": scanned, "modules": read, "missing": [modules without
build outputs]}`.
-/
open Lean

namespace CslibFrontierScripts.SecurityPremises

/-- The last component of a name, or `""`. -/
def last (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => ""

/-- Whether `s` is `pre` followed by digits, such as `eq_1`. -/
def numbered (pre s : String) : Bool :=
  s.startsWith pre && s.length > pre.length && (s.drop pre.length).all Char.isDigit

/-- Whether a name, without its private prefix, is one Lean generates. -/
def isGenerated (n : Name) : Bool :=
  let n := privateToUserName n
  let s := last n
  n.isInternalDetail || n.hasMacroScopes || numbered "match_" s || numbered "proof_" s ||
    numbered "eq_" s ||
    ["eq_def", "eq_unfold", "injEq", "inj", "induct", "induct_unfolding", "mutual_induct",
      "fun_cases", "fun_cases_unfolding", "congr_simp", "sizeOf_spec"].contains s

/-- Whether a constant of a module is in scope: under `CslibFrontier.Crypto`, or named in the
namespace `Cslib.Crypto`. -/
def inScope (module : Name) (n : Name) : Bool :=
  (`CslibFrontier.Crypto).isPrefixOf module || (`Cslib.Crypto).isPrefixOf (privateToUserName n)

/-- Whether a last name component names an efficiency predicate. -/
def efficiencyName (s : String) : Bool :=
  s.startsWith "IsPPT" || s.startsWith "IsOraclePPT"

/-- Whether a last name component names an advantage. -/
def advantageName (s : String) : Bool :=
  s == "advantage" || s == "succProbability" || s.endsWith "Advantage"

/-- Type heads of infrastructure values: distributions and games, numbers, truth values, sets,
encodings and sorts. -/
def infrastructure : NameSet :=
  [`PMF, `Cslib.Crypto.Game, `Real, `NNReal, `ENNReal, `Nat, `Int, `Rat, `Bool, `Prop, `Set,
    `Function.Embedding].foldl (·.insert ·) {}

/-- Result types of infrastructure functions: predicates, tests and numeric functions. -/
def infrastructureCodomain : NameSet :=
  [`Real, `NNReal, `ENNReal, `Nat, `Int, `Rat, `Bool, `Prop, `Function.Embedding].foldl
    (·.insert ·) {}

/-- Result types of ensembles and game families when indexed by the security parameter alone. -/
def ensembleCodomain : NameSet :=
  [`PMF, `Cslib.Crypto.Game].foldl (·.insert ·) {}

/-- Containers of a membership that are not adversary classes. -/
def ignoredContainers : NameSet :=
  [`PMF.support, `Set.range, `Finset.range, `List.range, `Finset.univ, `Set.univ,
    `Finset.Icc, `Finset.Ico, `Set.Icc, `Set.Ico, `Set.Iio, `Set.Ioi].foldl (·.insert ·) {}

/-- A binder's name, or `#i` for the `i`-th binder when its name is inaccessible, as for a premise
written with an arrow. -/
def binderLabel (n : Name) (i : Nat) : String :=
  if n.hasMacroScopes || n.isAnonymous then s!"#{i}" else n.toString

/-- The domains of the leading `∀`s of `e`. -/
partial def forallDomains : Expr → Array Expr
  | .forallE _ t b _ => #[t] ++ forallDomains b
  | .mdata _ b => forallDomains b
  | _ => #[]

/-- The leading `∀`s of `e` stripped (with loose bound variables left in place). -/
partial def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | .mdata _ b => stripForall b
  | e => e

/-- `e` with its first `k` leading `∀`s stripped. -/
def dropForall : Nat → Expr → Expr
  | k + 1, .forallE _ _ b _ => dropForall k b
  | k, .mdata _ b => dropForall k b
  | _, e => e

/-- The environment: every constant of the listed modules, with its module. -/
structure Env where
  consts : Std.HashMap Name ConstantInfo := {}
  moduleOf : Std.HashMap Name Name := {}
  skip : NameSet := {}

/-- `type` with type synonyms of the environment at its head unfolded (`fuel` times at most). -/
partial def unfoldSynonyms (env : Env) (fuel : Nat) (type : Expr) : Expr :=
  match fuel, type.consumeMData.getAppFn with
  | fuel + 1, .const c _ =>
    if infrastructure.contains c then type else
    match env.consts[c]? with
    | some (.defnInfo v) =>
      match stripForall v.type with
      | .sort _ =>
        unfoldSynonyms env fuel (v.value.beta type.consumeMData.getAppArgs).headBeta
      | _ => type
    | _ => type
  | _, _ => type

/-- The head of a type after unfolding type synonyms: a constant, or `Prop` for a sort. -/
def typeHead (env : Env) (type : Expr) : Option Name :=
  match (unfoldSynonyms env 8 type).consumeMData.getAppFn with
  | .sort _ => some `Prop
  | .const c _ => some c
  | _ => none

/-- Whether a binder domain is an object type, such as an adversary or a scheme: not a sort, a
type variable, a function, a number, truth value, set, distribution or game. -/
def objectDomain (env : Env) (domain : Expr) : Bool :=
  match (unfoldSynonyms env 8 domain).consumeMData with
  | .sort _ | .forallE .. => false
  | d =>
    match typeHead env d with
    | some h => !infrastructure.contains h
    | none => false

/-- Whether one of the first `k` binders of `type` is explicit with an object domain. -/
def objectArgument (env : Env) (type : Expr) : Nat → Bool
  | k + 1 =>
    match type.consumeMData with
    | .forallE _ d b bi => bi.isExplicit && objectDomain env d || objectArgument env b k
    | _ => false
  | 0 => false

/-- Whether the constant `c`, applied to `k` arguments, is a constructed object (see the module
docstring): a value of an algorithmic type (a program, a structure such as a scheme or adversary),
a function other than a predicate, test or numeric function, or a distribution, ensemble or game
applied to an object. -/
def constructedAt (env : Env) (c : Name) (k : Nat) : Bool := Id.run do
  let some info := env.consts[c]? | return false
  let some m := env.moduleOf[c]? | return false
  unless inScope m c do return false
  if env.skip.contains c || isGenerated c then return false
  match info with
  | .defnInfo _ | .opaqueInfo _ => pure ()
  | _ => return false
  let s := (last c).toLower
  if s.contains "game" || s.contains "experiment" || advantageName (last c) then return false
  let rest := unfoldSynonyms env 8 (dropForall k info.type)
  -- A distribution, ensemble or game applied to an object, such as `simulatorView A`.
  let derived := objectArgument env info.type k
  match rest.consumeMData with
  | .forallE .. =>
    match typeHead env (stripForall rest) with
    | some h =>
      if ensembleCodomain.contains h &&
          (forallDomains rest).all (·.consumeMData.isConstOf `Nat) then derived
      else !infrastructureCodomain.contains h
    | none => true
  | .sort _ => false
  | r =>
    match typeHead env r with
    | some h => !infrastructure.contains h || ensembleCodomain.contains h && derived
    | none => true

/-- The constructed constants of `e`, each judged at the number of arguments it is applied to. -/
partial def constructedIn (env : Env) (e : Expr) : StateM NameSet Unit := do
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ => if constructedAt env c args.size then modify (·.insert c)
    | _ => constructedIn env f
    args.forM (constructedIn env)
  | .const c _ => if constructedAt env c 0 then modify (·.insert c)
  | .lam _ t b _ | .forallE _ t b _ => constructedIn env t; constructedIn env b
  | .letE _ t v b _ => constructedIn env t; constructedIn env v; constructedIn env b
  | .mdata _ b | .proj _ _ b => constructedIn env b
  | _ => pure ()

/-- The constructed constants of the expressions `es`. -/
def constructedOf (env : Env) (es : Array Expr) : NameSet :=
  ((es.forM (constructedIn env)).run {}).2

/-- Whether `e` mentions an advantage. -/
def mentionsAdvantage (e : Expr) : Bool :=
  e.getUsedConstants.any fun c => advantageName (last c)

/-- The claim atoms of a hypothesis type: through its own `∀`s and premises, `∧`, `∃`, `∀ᶠ` and
metadata. -/
partial def atoms (e : Expr) : Array Expr :=
  match e with
  | .forallE _ _ b _ => atoms b
  | .mdata _ b => atoms b
  | .lam _ _ b _ => atoms b
  | e =>
    if e.isAppOfArity ``And 2 then atoms e.appFn!.appArg! ++ atoms e.appArg!
    else if e.isAppOfArity ``Exists 2 then atoms e.appArg!
    else if e.isAppOfArity `Filter.Eventually 3 then atoms e.appFn!.appArg!
    else #[e]

/-- The explicit arguments of an application of `f`, when the environment has `f`; otherwise all
of them. -/
def explicitArgs (env : Env) (f : Name) (args : Array Expr) : Array Expr := Id.run do
  let some info := env.consts[f]? | return args
  let mut type := info.type
  let mut out := #[]
  for a in args do
    match type.consumeMData with
    | .forallE _ _ b bi =>
      if bi.isExplicit then out := out.push a
      type := b
    | _ => out := out.push a
  return out

/-- The kind and subjects of a security atom, or `none`. -/
def classify (env : Env) (e : Expr) : Option (String × Array Expr) :=
  match e.getAppFn with
  | .const f _ =>
    let s := last f
    let all := e.getAppArgs
    let args := explicitArgs env f all
    if s == "Negligible" then some ("negligible", args)
    else if (f == ``LE.le || f == ``LT.lt || f == ``GE.ge || f == ``GT.gt) && all.size == 4 then
      if mentionsAdvantage all[2]! || mentionsAdvantage all[3]! then
        some ("advantage", #[all[2]!, all[3]!])
      else none
    else if f == ``Membership.mem && all.size == 5 then
      match all[3]!.getAppFn with
      | .const g _ => if ignoredContainers.contains g then none else some ("member", #[all[4]!])
      | _ => some ("member", #[all[4]!])
    else if efficiencyName s then some ("efficiency", args)
    else if s.contains "Indistinguishable" then some ("indistinguishable", args)
    else none
  -- A bound predicate, such as an abstract admissibility class `Admissible B`.
  | .bvar _ | .fvar _ => if e.getAppNumArgs > 0 then some ("member", e.getAppArgs) else none
  | _ => none

/-- Unfold a Prop-valued definition of the environment heading `e`, once. -/
def unfoldProp? (env : Env) (e : Expr) : Option Expr := do
  let .const c _ := e.getAppFn | none
  let .defnInfo v ← env.consts[c]? | none
  let .sort .zero := stripForall v.type | none
  some (v.value.beta e.getAppArgs).headBeta

/-- The security atoms of a hypothesis type that mention a constructed object, as
`(kind, constructed constants)`. Within an unfolded definition, only the constructed constants of
its arguments (`allowed`) count: the objects that a notion's own definition builds, such as the
dummy adversary of UC emulation, are part of the notion. -/
partial def findings (env : Env) (fuel : Nat) (allowed : Option NameSet) (e : Expr) :
    Array (String × Array Name) :=
  (atoms e).foldl (init := #[]) fun acc a =>
    match classify env a with
    | some (k, subjects) =>
      let cs := (constructedOf env subjects).toArray.filter fun c =>
        allowed.all (·.contains c)
      if cs.isEmpty then acc else acc.push (k, cs)
    | none =>
      match fuel, unfoldProp? env a with
      | fuel + 1, some u =>
        let args := constructedOf env a.getAppArgs
        let allowed := some (allowed.elim args fun s => args.filter s.contains)
        if args.isEmpty then acc else
        acc ++ (findings env fuel allowed u).map fun (k, cs) => ("unfolded " ++ k, cs)
      | _, _ => acc

/-- The constructed constants of `e` applied to an argument that mentions one of `vars`. -/
partial def constructedWith (env : Env) (vars : Array FVarId) (e : Expr) :
    StateM NameSet Unit := do
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ =>
      if constructedAt env c args.size &&
          args.any (·.hasAnyFVar (vars.contains ·)) then
        modify (·.insert c)
    | _ => constructedWith env vars f
    args.forM (constructedWith env vars)
  | .lam _ t b _ | .forallE _ t b _ => constructedWith env vars t; constructedWith env vars b
  | .letE _ t v b _ =>
    constructedWith env vars t; constructedWith env vars v; constructedWith env vars b
  | .mdata _ b | .proj _ _ b => constructedWith env vars b
  | _ => pure ()

/-- Advantage bounds in a conclusion that hold only for some existentially chosen parameters of
a constructed reduction, such as `∃ m₀ m₁, … ≤ Adv(B A m₀ m₁)`: the constructed constants applied
to an `∃`-bound variable in an advantage inequality under the `∃`. The textbook reduction chooses
such parameters itself (by sampling), so the bound does not give a uniform reduction. -/
partial def existentialFindings (env : Env) (vars : Array FVarId) (fresh : Nat) (e : Expr) :
    Array Name :=
  match e with
  | .forallE _ _ b _ | .mdata _ b => existentialFindings env vars fresh b
  | e =>
    if e.isAppOfArity ``And 2 then
      existentialFindings env vars fresh e.appFn!.appArg! ++
        existentialFindings env vars fresh e.appArg!
    else if e.isAppOfArity ``Exists 2 then
      match e.appArg!.consumeMData with
      | .lam _ _ body _ =>
        let x : FVarId := ⟨.num `_exists fresh⟩
        existentialFindings env (vars.push x) (fresh + 1) (body.instantiate1 (.fvar x))
      | _ => #[]
    else if vars.isEmpty then #[]
    else
      match classify env e with
      | some ("advantage", subjects) =>
        (((subjects.forM (constructedWith env vars)).run {}).2).toArray
      | _ => #[]

/-- Whether `e`, under its `fun`s, is the variable `x` or an application of it. -/
partial def headedBy (x : FVarId) (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ b _ => headedBy x b
  | e => e.getAppFn.consumeMData.isFVarOf x

/-- The variables among `vars` to which the hypothesis type `premise` gives an efficiency or
class-membership claim, whose subject is the variable or a function that applies it, as in
`hD : IsOraclePPT encBool D`, `IsPPTOn … (fun p => test p.1 p.2)` or `D ∈ 𝒟`. -/
def certifiedBy (env : Env) (vars : Array FVarId) (premise : Expr) : Array FVarId :=
  (atoms premise).foldl (init := #[]) fun acc a =>
    match classify env a with
    | some ("efficiency", subjects) | some ("member", subjects) =>
      acc ++ vars.filter fun x => subjects.any (headedBy x)
    | _ => acc

/-- Realization premises: an equation one side of which mentions a variable `x` of `certified`
and the other side does not, but applies a constructed constant to another of the theorem's
variables `vars`. With `x`'s efficiency premise, it assumes that the constructed object has an
efficient realization, as in `hreal : eval (prfRealGame family D n) = … (nonceFnDistinguisher
(seed n) (hash n) (forger n))` beside `hD : IsOraclePPT encBool D`. Only `x` is excluded on the
other side, and it does not occur there: the other variable may be certified too, as the input
adversary is in `D.run n = (reduction A).run n` beside `hA : A.IsPPT` and `hD : D.IsPPT`.
Returns the constructed constants of the other side. -/
def realizations (env : Env) (certified vars : Array FVarId) (premise : Expr) : Array Name :=
  (atoms premise).foldl (init := #[]) fun acc a =>
    if a.isAppOfArity ``Eq 3 then
      let side (s t : Expr) : Array Name :=
        if certified.any fun x => s.containsFVar x && !t.containsFVar x then
          ((constructedWith env vars t).run {}).2.toArray
        else #[]
      acc ++ side a.appFn!.appArg! a.appArg! ++ side a.appArg! a.appFn!.appArg!
    else acc

unsafe def declRanges (entries : Array (Name × Array EnvExtensionEntry)) :
    NameMap DeclarationRanges := Id.run do
  let mut ranges : NameMap DeclarationRanges := {}
  for (ext, es) in entries do
    if ext == `Lean.declRangeExt then
      for e in es do
        let (n, r) := (unsafeCast e : Name × DeclarationRanges)
        ranges := ranges.insert n r
  return ranges

/-- The instances and structure projections of a module. -/
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
  return out

unsafe def run (libDir : System.FilePath) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut regions : Array CompactedRegion := #[]
  let mut missing : Array String := #[]
  let mut env : Env := {}
  let mut mods : Array (Name × ModuleData) := #[]
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let mod := line.trimAscii.toString
    if mod.isEmpty then continue
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
    let m := mod.toName
    mods := mods.push (m, data)
    for c in data.constants do
      env := { env with consts := env.consts.insert c.name c,
                        moduleOf := env.moduleOf.insert c.name m }
    env := { env with skip := (skipped data.entries).foldl (·.insert ·) env.skip }
  let mut scanned := 0
  for (m, data) in mods do
    let ranges := declRanges data.entries
    for c in data.constants do
      let .thmInfo v := c | continue
      if isPrivateName c.name || isGenerated c.name || env.skip.contains c.name then continue
      unless inScope m c.name do continue
      scanned := scanned + 1
      let mut hyps : Array Json := #[]
      let mut t := v.type
      let mut index := 0
      -- The theorem's variables, and its premises as `(binder label, type)`.
      let mut vars : Array FVarId := #[]
      let mut premises : Array (String × Expr) := #[]
      repeat
        match t with
        | .mdata _ b => t := b
        | .forallE n ty b bi =>
          index := index + 1
          unless bi.isInstImplicit do
            premises := premises.push (binderLabel n index, ty)
            let fs := findings env 3 none ty
            unless fs.isEmpty do
              let kinds := (fs.map (·.1)).toList.eraseDups
              let cs := (fs.foldl (fun acc (_, cs) => acc ++ cs) #[]).toList.eraseDups
              hyps := hyps.push <| Json.mkObj [("b", toJson (binderLabel n index)),
                ("k", toJson kinds), ("c", toJson (cs.map (privateToUserName · |>.toString)))]
          let x : FVarId := ⟨.num `_binder index⟩
          vars := vars.push x
          t := b.instantiate1 (.fvar x)
        | _ => break
      let certified := premises.foldl (fun acc (_, ty) => acc ++ certifiedBy env vars ty) #[]
      unless certified.isEmpty do
        for (label, ty) in premises do
          let cs := (realizations env certified vars ty).toList.eraseDups
          unless cs.isEmpty do
            hyps := hyps.push <| Json.mkObj [("b", toJson label), ("k", toJson ["realization"]),
              ("c", toJson (cs.map (privateToUserName · |>.toString)))]
      let cs := (existentialFindings env #[] 0 t).toList.eraseDups
      unless cs.isEmpty do
        hyps := hyps.push <| Json.mkObj [("b", toJson "⊢"),
          ("k", toJson ["exists advantage"]),
          ("c", toJson (cs.map (privateToUserName · |>.toString)))]
      unless hyps.isEmpty do
        let line := ((ranges.find? c.name).map (·.selectionRange.pos.line)).getD 0
        stdout.putStrLn <| Json.compress <| Json.mkObj [("n", toJson c.name.toString),
          ("m", toJson m.toString), ("l", toJson line), ("h", Json.arr hyps)]
  stdout.putStrLn <| Json.compress <| Json.mkObj [("theorems", toJson scanned),
    ("modules", toJson mods.size), ("missing", toJson missing)]
  -- Keep the regions reachable until every expression has been used.
  if regions.isEmpty then stdout.flush

end CslibFrontierScripts.SecurityPremises

unsafe def main (args : List String) : IO Unit :=
  match args with
  | [] => CslibFrontierScripts.SecurityPremises.run ".lake/build/lib/lean"
  | [libDir] => CslibFrontierScripts.SecurityPremises.run libDir
  | _ => throw <| IO.userError "usage: SecurityPremises [<lib-dir>] < modules.txt"
