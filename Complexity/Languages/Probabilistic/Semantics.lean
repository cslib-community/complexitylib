/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Simulation
public import Complexity.Languages.Probabilistic.Sum

/-!
# Semantics of oracle programs

A program `program : OracleComp spec α` is a tree of oracle calls. It has a meaning once its calls
are answered, and this module gives that meaning once, for every interface `spec`, relative to the
answers:

* `OracleComp.evalWith h program` is the output distribution when each call `q` is answered by an
  independent sample of `h q : PMF (spec q)`. It is `OracleComp.interpret` into `PMF`.
* `OracleComp.supportWith possible program` is the set of results reached when each call `q` may be
  answered by any element of `possible q`. It is defined by recursion on the tree of calls, so it
  needs no distribution on the replies. With every reply possible it is `OracleComp.support`, the
  results at the leaves of the tree.
* `OracleComp.runWith oracle program s` is the joint law of the result and the final state when
  each call is answered by a stateful probabilistic oracle
  `oracle : (q : ι) → StateT σ PMF (spec q)` from the state `s`. It is `OracleComp.interpret` into
  `StateT σ PMF`.

The three agree: the support of `evalWith h program` is `supportWith` of the supports of `h`
(`support_evalWith`), a result of a stateful run is reached along replies the oracle can give
(`mem_supportWith_of_mem_support_runWith`), and a memoryless oracle run with state is `evalWith`
with the state unchanged (`runWith_lift`). On the sum `spec₁ ⊕ₒ spec₂`, a handler is a
`sumHandler`, and an embedded program sees only its own side (`evalWith_sumHandler_liftLeft`,
`supportWith_sumHandler_liftLeft`, `runWith_sumHandler_liftLeft`).

The library's semantics are instances. `ProbComp.eval` is `evalWith ProbComp.unifOracle`
(`ProbComp.eval_eq_evalWith`), and since every uniform reply has positive probability, the
possible results of a closed program are its results for any replies (`ProbComp.support_eval`).
A program with private coins and external calls, `ProbOracleComp spec`, is a program over
`unifSpec ⊕ₒ spec`: its run against a stateful oracle is `runWith` of the sum of the lifted uniform
handler and that oracle (`ProbOracleComp.runWith`), and its possible results are `support`.

## Algorithms are programs

Probabilistic algorithms, such as key generation, signing, provers, verifiers, simulators,
extractors and samplers, are `ProbComp` or `OracleComp` programs. `PMF` is reserved for their
semantics, `evalWith` and its instances, and for genuinely semantic objects such as ideal
distributions and the laws compared in a statistical argument. A program can be run against
different oracles, budgeted (`OracleComp.IsCostBounded`), realized by a machine, and substituted
into a reduction, while a bare `PMF` can do none of these. Exact theorems stay exact, as statements
about `evalWith`.

## Main definitions

* `Cslib.OracleComp.evalWith`: the output distribution for independent answers.
* `Cslib.OracleComp.supportWith`: the results for answers in given sets.
* `Cslib.OracleComp.support`: the results for any answers.
* `Cslib.OracleComp.runWith`: the joint law of the result and final state of a stateful oracle.

## Main results

* `Cslib.OracleComp.evalWith_bind`, `.mem_supportWith_bind_iff`, `.runWith_bind`,
  `.bind_congr_on_support`, and the `pure`, `map` and `query` rules: the structural rules of each
  semantics.
* `Cslib.OracleComp.isMonadHom_evalWith`: `evalWith h` is a monad morphism.
* `Cslib.OracleComp.evalWith_interpret`, `.supportWith_interpret`: replacing calls by programs
  composes with the semantics.
* `Cslib.OracleComp.support_evalWith`: evaluation and support agree.
* `Cslib.OracleComp.mem_supportWith_of_mem_support_runWith`: stateful runs reach possible results.
* `Cslib.OracleComp.runWith_lift`: memoryless oracles leave the state unchanged.
* `Cslib.OracleComp.support_liftLeft`, `.support_liftRight`: embedding into a sum keeps the
  possible results.
* `Cslib.ProbComp.eval_eq_evalWith`, `Cslib.ProbComp.support_eval`,
  `Cslib.ProbComp.support_nonempty`, `Cslib.ProbComp.mem_support_unifFin`: closed probabilistic
  programs are the instance with uniform answers.
* `Cslib.ProbComp.isMonadHom_eval`, `Cslib.ProbComp.eval_interpret`: the instances of
  `isMonadHom_evalWith` and `evalWith_interpret`.

## References

The design follows Devon Tuma, Quang Dao, and collaborators'
[VCVio](https://github.com/Verified-zkEVM/VCVio), whose programs carry their distribution and
possible outputs relative to an interpretation of the oracle calls.
-/

@[expose] public section

namespace Cslib

open Probability

namespace OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type v}

/-! ### Distributions for independent answers -/

/-- The output distribution of `program` when each call `q` is answered by an independent sample
of `h q`. -/
noncomputable def evalWith (h : (q : ι) → PMF (spec q)) (program : OracleComp spec α) : PMF α :=
  interpret h program

section EvalWith

variable (h : (q : ι) → PMF (spec q))

/-- A returned value has a point distribution. -/
@[simp] theorem evalWith_pure (a : α) : evalWith h (pure a : OracleComp spec α) = PMF.pure a :=
  rfl

/-- Evaluating a sequence draws a result of the first program and evaluates the continuation at
it. -/
@[simp] theorem evalWith_bind (program : OracleComp spec α) (next : α → OracleComp spec β) :
    evalWith h (program >>= next) = (evalWith h program).bind fun a => evalWith h (next a) :=
  interpret_bind _ _ _

/-- Postprocessing maps the distribution. -/
@[simp] theorem evalWith_map (f : α → β) (program : OracleComp spec α) :
    evalWith h (f <$> program) = (evalWith h program).map f :=
  interpret_map _ _ _

/-- A single call has the distribution of its answer. -/
@[simp] theorem evalWith_query (q : ι) : evalWith h (query (spec := spec) q) = h q :=
  interpret_query _ _

/-- Evaluation is a monad morphism into `PMF`. -/
theorem isMonadHom_evalWith : IsMonadHom (OracleComp spec) PMF (evalWith h) :=
  PFunctor.FreeM.isMonadHom_liftM (P := ⟨ι, spec⟩) h

end EvalWith

/-- Evaluating a program whose calls were replaced by programs over another interface evaluates
the original calls by the distributions of their replacements. -/
theorem evalWith_interpret {κ : Type u} {target : OracleSpec.{u, v} κ}
    (handler : (q : ι) → OracleComp target (spec q)) (h : (q : κ) → PMF (target q))
    (program : OracleComp spec α) :
    evalWith h (interpret handler program) =
      evalWith (fun q => evalWith h (handler q)) program :=
  interpret_interpret _ _ _

/-! ### Possible results -/

/-- The results of `program` when each call `q` may be answered by any element of `possible q`:
the results at the leaves of its tree of calls reached along such answers. -/
def supportWith (possible : (q : ι) → Set (spec q)) : OracleComp spec α → Set α
  | .pure a => {a}
  | .liftBind q cont => ⋃ a ∈ possible q, supportWith possible (cont a)

section SupportWith

variable (possible : (q : ι) → Set (spec q))

/-- A returned value is the only possible result. -/
@[simp] theorem supportWith_pure (a : α) :
    supportWith possible (pure a : OracleComp spec α) = {a} :=
  rfl

variable {possible} in
/-- A possible result of a sequence is a possible result of a continuation at a possible first
result. -/
@[simp] theorem mem_supportWith_bind_iff {program : OracleComp spec α}
    {next : α → OracleComp spec β} {b : β} :
    b ∈ supportWith possible (program >>= next) ↔
      ∃ a ∈ supportWith possible program, b ∈ supportWith possible (next a) := by
  induction program with
  | pure a =>
    constructor
    · exact fun hb => ⟨a, rfl, hb⟩
    · rintro ⟨a', rfl, hb⟩
      exact hb
  | liftBind q cont ih =>
    change b ∈ ⋃ x ∈ possible q, supportWith possible (cont x >>= next) ↔
      ∃ a ∈ ⋃ x ∈ possible q, supportWith possible (cont x), _
    simp only [Set.mem_iUnion, exists_prop, ih]
    constructor
    · rintro ⟨x, hx, a, ha, hb⟩
      exact ⟨a, ⟨x, hx, ha⟩, hb⟩
    · rintro ⟨a, ⟨x, hx, ha⟩, hb⟩
      exact ⟨x, hx, a, ha, hb⟩

/-- The possible results of a sequence, as a union over the possible first results. -/
theorem supportWith_bind (program : OracleComp spec α) (next : α → OracleComp spec β) :
    supportWith possible (program >>= next) =
      ⋃ a ∈ supportWith possible program, supportWith possible (next a) := by
  ext b
  simp only [mem_supportWith_bind_iff, Set.mem_iUnion, exists_prop]

variable {possible} in
/-- A possible mapped result is the image of a possible result. -/
@[simp] theorem mem_supportWith_map_iff {f : α → β} {program : OracleComp spec α} {b : β} :
    b ∈ supportWith possible (f <$> program) ↔ ∃ a ∈ supportWith possible program, f a = b := by
  rw [← bind_pure_comp, mem_supportWith_bind_iff]
  simp only [supportWith_pure, Set.mem_singleton_iff, eq_comm]

/-- The possible results of a mapped program are the image of its possible results. -/
theorem supportWith_map (f : α → β) (program : OracleComp spec α) :
    supportWith possible (f <$> program) = f '' supportWith possible program := by
  ext b
  simp only [mem_supportWith_map_iff, Set.mem_image]

/-- A single call may return any of its possible answers. -/
@[simp] theorem supportWith_query (q : ι) :
    supportWith possible (query (spec := spec) q) = possible q :=
  Set.biUnion_of_singleton (possible q)

end SupportWith

/-- Allowing more answers allows more results. -/
theorem supportWith_mono {possible possible' : (q : ι) → Set (spec q)}
    (hpossible : ∀ q, possible q ⊆ possible' q) (program : OracleComp spec α) :
    supportWith possible program ⊆ supportWith possible' program := by
  induction program using OracleComp.induction with
  | pure a => exact subset_rfl
  | query_bind q cont ih =>
    intro b hb
    obtain ⟨a, ha, hb⟩ := mem_supportWith_bind_iff.mp hb
    rw [supportWith_query] at ha
    exact mem_supportWith_bind_iff.mpr
      ⟨a, by rw [supportWith_query]; exact hpossible q ha, ih a hb⟩

/-- Replacing calls by programs over another interface: the possible results are those of the
original program, with each call answered by a possible result of its replacement. -/
theorem supportWith_interpret {κ : Type u} {target : OracleSpec.{u, v} κ}
    (handler : (q : ι) → OracleComp target (spec q)) (possible : (q : κ) → Set (target q))
    (program : OracleComp spec α) :
    supportWith possible (interpret handler program) =
      supportWith (fun q => supportWith possible (handler q)) program := by
  induction program using OracleComp.induction with
  | pure a => rfl
  | query_bind q cont ih =>
    ext b
    simp only [interpret_bind, interpret_query, mem_supportWith_bind_iff, supportWith_query, ih]

/-- A returned value is the only possible result. -/
theorem eq_of_mem_supportWith_pure {possible : (q : ι) → Set (spec q)} {a b : α}
    (h : b ∈ supportWith possible (pure a : OracleComp spec α)) : b = a :=
  h

/-- The results of `program` for any replies to its calls: the results at the leaves of its tree
of calls. It is `supportWith` with every reply possible, and the rules of `supportWith` apply. -/
abbrev support (program : OracleComp spec α) : Set α :=
  supportWith (fun _ => Set.univ) program

/-- Two continuations that agree on every possible output of `program` have identical `>>=` in
`OracleComp`. -/
theorem bind_congr_on_support {program : OracleComp spec α}
    {f g : α → OracleComp spec β} (h : ∀ a ∈ program.support, f a = g a) :
    program >>= f = program >>= g := by
  induction program using OracleComp.induction with
  | pure a =>
    simpa only [pure_bind] using h a rfl
  | query_bind q cont ih =>
    simp only [bind_assoc]
    exact congrArg (query q >>= ·) (funext fun r => ih r fun a ha =>
      h a (mem_supportWith_bind_iff.mpr ⟨r, by simp, ha⟩))

/-! ### Evaluation and support -/

/-- The results with positive probability are the results reached along answers with positive
probability. -/
theorem support_evalWith (h : (q : ι) → PMF (spec q)) (program : OracleComp spec α) :
    (evalWith h program).support = supportWith (fun q => (h q).support) program := by
  induction program using OracleComp.induction with
  | pure a => simp only [evalWith_pure, PMF.support_pure, supportWith_pure]
  | query_bind q cont ih =>
    ext b
    simp only [evalWith_bind, evalWith_query, PMF.mem_support_bind_iff,
      mem_supportWith_bind_iff, supportWith_query, ih]

/-! ### Stateful oracles -/

section RunWith

variable {σ : Type v} (oracle : (q : ι) → StateT σ PMF (spec q))

/-- The joint law of the result of `program` and the final state of the stateful oracle answering
its calls, starting from the state `s`. -/
noncomputable def runWith (program : OracleComp spec α) (s : σ) : PMF (α × σ) :=
  (interpret oracle program).run s

/-- A returned value leaves the state unchanged. -/
@[simp] theorem runWith_pure (a : α) (s : σ) :
    runWith oracle (pure a : OracleComp spec α) s = PMF.pure (a, s) :=
  rfl

/-- Running a sequence runs the first program, then the continuation at its result from the state
it reached. -/
@[simp] theorem runWith_bind (program : OracleComp spec α) (next : α → OracleComp spec β)
    (s : σ) :
    runWith oracle (program >>= next) s =
      (runWith oracle program s).bind fun x => runWith oracle (next x.1) x.2 :=
  run_interpret_bind _ _ _ _

/-- Postprocessing maps the result and keeps the final state. -/
@[simp] theorem runWith_map (f : α → β) (program : OracleComp spec α) (s : σ) :
    runWith oracle (f <$> program) s = (runWith oracle program s).map (Prod.map f id) :=
  run_interpret_map _ _ _ _

/-- A single call is answered by the oracle from the current state. -/
@[simp] theorem runWith_query (q : ι) (s : σ) :
    runWith oracle (query (spec := spec) q) s = oracle q s :=
  run_interpret_query _ _ _

/-- Every result of a stateful run is reached along replies the oracle can give: if each reply of
the oracle to `q`, from any state, lies in `possible q`, every result is in
`supportWith possible`. -/
theorem mem_supportWith_of_mem_support_runWith {possible : (q : ι) → Set (spec q)}
    (hpossible : ∀ q s a s', (a, s') ∈ (oracle q s).support → a ∈ possible q)
    {program : OracleComp spec α} {s s' : σ} {a : α}
    (h : (a, s') ∈ (runWith oracle program s).support) : a ∈ supportWith possible program := by
  induction program using OracleComp.induction generalizing s s' with
  | pure b =>
    rw [runWith_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
    exact h.1
  | query_bind q cont ih =>
    rw [runWith_bind, runWith_query, PMF.mem_support_bind_iff] at h
    obtain ⟨⟨b, middle⟩, hb, h⟩ := h
    exact mem_supportWith_bind_iff.mpr
      ⟨b, by rw [supportWith_query]; exact hpossible q s b middle hb, ih b h⟩

end RunWith

/-- A memoryless oracle run with state leaves the state unchanged, and the result has the law of
`evalWith`. -/
@[simp] theorem runWith_lift {σ : Type v} (h : (q : ι) → PMF (spec q))
    (program : OracleComp spec α) (s : σ) :
    runWith (fun q => StateT.lift (h q)) program s = (evalWith h program).map (·, s) :=
  run_interpret_lift h program s

/-! ### Sums of interfaces -/

section Sum

variable {ι₁ ι₂ : Type u} {spec₁ : OracleSpec.{u, v} ι₁} {spec₂ : OracleSpec.{u, v} ι₂}

/-- An embedded left program is evaluated by the left handler alone. -/
@[simp] theorem evalWith_sumHandler_liftLeft (left : (q : ι₁) → PMF (spec₁ q))
    (right : (q : ι₂) → PMF (spec₂ q)) (program : OracleComp spec₁ α) :
    evalWith (sumHandler left right) (liftLeft program) = evalWith left program :=
  interpret_sumHandler_liftLeft _ _ _

/-- An embedded right program is evaluated by the right handler alone. -/
@[simp] theorem evalWith_sumHandler_liftRight (left : (q : ι₁) → PMF (spec₁ q))
    (right : (q : ι₂) → PMF (spec₂ q)) (program : OracleComp spec₂ α) :
    evalWith (sumHandler left right) (liftRight program) = evalWith right program :=
  interpret_sumHandler_liftRight _ _ _

/-- Evaluation distributes over the two sides of a handler by programs. -/
theorem evalWith_sumHandler {κ : Type u} {target : OracleSpec.{u, v} κ}
    (h : (q : κ) → PMF (target q)) (left : (q : ι₁) → OracleComp target (spec₁ q))
    (right : (q : ι₂) → OracleComp target (spec₂ q)) :
    (fun q => evalWith h (sumHandler left right q)) =
      sumHandler (fun q => evalWith h (left q)) (fun q => evalWith h (right q)) :=
  interpret_sumHandler h left right

/-- The supports of the answers of a sum handler are the sum of the supports. -/
theorem support_sumHandler (left : (q : ι₁) → PMF (spec₁ q))
    (right : (q : ι₂) → PMF (spec₂ q)) :
    (fun q => (sumHandler left right q).support) =
      sumHandler (fun q => (left q).support) (fun q => (right q).support) := by
  funext q
  cases q <;> rfl

/-- An embedded left program has the possible results allowed by the left answers alone. -/
@[simp] theorem supportWith_sumHandler_liftLeft (left : (q : ι₁) → Set (spec₁ q))
    (right : (q : ι₂) → Set (spec₂ q)) (program : OracleComp spec₁ α) :
    supportWith (sumHandler left right) (liftLeft program) = supportWith left program := by
  rw [liftLeft, supportWith_interpret]
  congr 1
  funext q
  exact supportWith_query _ _

/-- An embedded right program has the possible results allowed by the right answers alone. -/
@[simp] theorem supportWith_sumHandler_liftRight (left : (q : ι₁) → Set (spec₁ q))
    (right : (q : ι₂) → Set (spec₂ q)) (program : OracleComp spec₂ α) :
    supportWith (sumHandler left right) (liftRight program) = supportWith right program := by
  rw [liftRight, supportWith_interpret]
  congr 1
  funext q
  exact supportWith_query _ _

/-- An embedded left program has the same possible results for any replies. -/
@[simp] theorem support_liftLeft (program : OracleComp spec₁ α) :
    support (liftLeft (spec₂ := spec₂) program) = support program := by
  have huniv : (fun _ => Set.univ : (q : ι₁ ⊕ ι₂) → Set ((spec₁ ⊕ₒ spec₂) q)) =
      sumHandler (fun _ => Set.univ) (fun _ => Set.univ) := by
    funext q
    cases q <;> rfl
  rw [support, huniv, supportWith_sumHandler_liftLeft]

/-- An embedded right program has the same possible results for any replies. -/
@[simp] theorem support_liftRight (program : OracleComp spec₂ α) :
    support (liftRight (spec₁ := spec₁) program) = support program := by
  have huniv : (fun _ => Set.univ : (q : ι₁ ⊕ ι₂) → Set ((spec₁ ⊕ₒ spec₂) q)) =
      sumHandler (fun _ => Set.univ) (fun _ => Set.univ) := by
    funext q
    cases q <;> rfl
  rw [support, huniv, supportWith_sumHandler_liftRight]

/-- An embedded left program is run by the left oracle alone, which keeps the whole state. -/
@[simp] theorem runWith_sumHandler_liftLeft {σ : Type v}
    (left : (q : ι₁) → StateT σ PMF (spec₁ q)) (right : (q : ι₂) → StateT σ PMF (spec₂ q))
    (program : OracleComp spec₁ α) (s : σ) :
    runWith (sumHandler left right) (liftLeft program) s = runWith left program s :=
  congrArg (StateT.run · s) (interpret_sumHandler_liftLeft left right program)

/-- An embedded right program is run by the right oracle alone, which keeps the whole state. -/
@[simp] theorem runWith_sumHandler_liftRight {σ : Type v}
    (left : (q : ι₁) → StateT σ PMF (spec₁ q)) (right : (q : ι₂) → StateT σ PMF (spec₂ q))
    (program : OracleComp spec₂ α) (s : σ) :
    runWith (sumHandler left right) (liftRight program) s = runWith right program s :=
  congrArg (StateT.run · s) (interpret_sumHandler_liftRight left right program)

end Sum

end OracleComp

namespace ProbComp

variable {α : Type}

/-- Evaluating a closed probabilistic program is `evalWith` of the uniform handler. -/
theorem eval_eq_evalWith (program : ProbComp α) :
    eval program = OracleComp.evalWith unifOracle program :=
  rfl

/-- The possible results of a closed probabilistic program are its results for any replies, since
every uniform reply has positive probability. -/
theorem support_eval (program : ProbComp α) :
    (eval program).support = OracleComp.support program := by
  rw [eval_eq_evalWith, OracleComp.support_evalWith]
  congr 1
  funext n
  exact Set.eq_univ_of_forall fun a => by simp [unifOracle, PMF.mem_support_iff]

/-- Every closed probabilistic program has at least one possible result. -/
theorem support_nonempty (program : ProbComp α) : program.support.Nonempty := by
  rw [← support_eval]
  exact (eval program).support_nonempty

/-- Every value in `Fin (n + 1)` is a possible output of `unifFin n`. -/
@[simp]
theorem mem_support_unifFin (n : ℕ) (k : Fin (n + 1)) : k ∈ (unifFin n).support := by
  simp [unifFin, OracleComp.support]

/-- Evaluating a closed probabilistic program is a monad morphism into `PMF`. -/
theorem isMonadHom_eval : IsMonadHom ProbComp PMF (@eval) :=
  OracleComp.isMonadHom_evalWith unifOracle

/-- Evaluating an interpreted oracle program is interpreting each call by its evaluated
sampler. -/
theorem eval_interpret {ι : Type} {spec : ι → Type} (handler : (q : ι) → ProbComp (spec q))
    (program : OracleComp spec α) :
    eval (OracleComp.interpret handler program) =
      OracleComp.interpret (fun q => eval (handler q)) program :=
  OracleComp.evalWith_interpret handler unifOracle program

end ProbComp

end Cslib
