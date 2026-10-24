/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Probabilistic.Oracle
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Polynomial time relative to an oracle language

An oracle language `A : Set (List Bool)` answers a word request `w` with the one-bit word
`[decide (w ∈ A)]` (`Cslib.Complexity.languageOracle`). A deterministic oracle algorithm is a
program `WordQueryComp Unit β`: a `PFunctor.FreeM` program whose calls are word requests and
whose later requests may depend on earlier replies. Run against `A`, it returns
`OracleComp.interpret (m := Id) (languageOracle A) program`.

`f` is computable in polynomial time relative to `A`
(`Cslib.Complexity.ComputableInPolyTimeWithOracle`) when one deterministic program computes `f`
against `A` and the program is strict oracle PPT (`Cslib.Probability.IsOraclePPTOn`) with one
channel: one finite-control machine, under one polynomial clock in the encoded input length,
reproduces the program's complete interaction with every stateful oracle. This is the oracle
Turing machine of [Arora and Barak, Section 3.4][AroraBarak09] on the common machine
(`Turing.MultiTapeMachine` with oracle channels): each request symbol is written onto the query
buffer at the cost of one instruction, submitting a request costs one instruction, and the reply
bit is the first cell of the answer tape, read by the answer head with no further instruction.
The oracle's own computation is not charged. The certificate quantifies over every handler, not
only language oracles, so the program, not the oracle, determines which requests are made; the
machine's clock also bounds their number and length
(`Cslib.Probability.IsOraclePPTOn.query_bounds`).

The classes relativize `P` and `NP` by this one substitution: `PWithOracle A enc` and
`NPWithOracle A enc` are `Cslib.Complexity.P` and `Cslib.Complexity.NP` with
`ComputableInPolyTime` replaced by `ComputableInPolyTimeWithOracle A`. Hence `NPWithOracle`
uses verifiers with an oracle and certificates of exactly polynomial length. When the oracle is a
promise problem or an encoded class of oracles (`PWithSharpPOracle`, `PWithPPOracle`,
`RPWithPromiseOracle`), `Cslib.Complexity.PolyTimeOracleProgram` asks for one deterministic
polynomial-time oracle program whose function against every admissible oracle language satisfies a
given specification.

For a deterministic program and an answer function, `OracleComp.queriesWith` lists the requests
made. Only their answers matter (`OracleComp.interpret_id_congr`), which is the locality on which
oracle constructions rest.

## Main definitions

* `Cslib.OracleComp.queriesWith`: the requests a deterministic program makes under given answers.
* `Cslib.Complexity.WordQueryComp`: deterministic programs making word requests.
* `Cslib.Complexity.languageOracle`: the replies of an oracle language.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle`: polynomial time relative to an oracle.
* `Cslib.Complexity.PolyTimeOracleProgram`: one polynomial-time oracle program satisfying a
  specification across every admissible oracle language.
* `Cslib.Complexity.PWithOracle`, `Cslib.Complexity.NPWithOracle`: `P` and `NP` relative to an
  oracle language.

## Main results

* `Cslib.OracleComp.interpret_id_congr`: answers to requests that are not made do not matter.
* `Turing.MultiTapeTM.ComputableInPolyTime.computableInPolyTimeWithOracle`: polynomial time
  is polynomial time relative to every oracle.
* `Cslib.Complexity.PolyTimeOracleProgram.of_polyTime`,
  `Cslib.Complexity.PolyTimeOracleProgram.exists_computableInPolyTimeWithOracle`,
  `Cslib.Complexity.PolyTimeOracleProgram.of_computableInPolyTimeWithOracle`.
* `Cslib.Complexity.P_subset_PWithOracle`, `Cslib.Complexity.NP_subset_NPWithOracle`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib

namespace OracleComp

variable {ι α β : Type} {spec : OracleSpec.{0, 0} ι}

/-- The requests made by `program`, in order, when every call `q` is answered by `answer q`. -/
def queriesWith (answer : (q : ι) → spec q) : OracleComp spec α → List ι
  | .pure _ => []
  | .liftBind q next => q :: queriesWith answer (next (answer q))

@[simp] theorem queriesWith_pure (answer : (q : ι) → spec q) (a : α) :
    queriesWith answer (pure a : OracleComp spec α) = [] := rfl

@[simp] theorem queriesWith_query (answer : (q : ι) → spec q) (q : ι) :
    queriesWith answer (query q) = [q] := rfl

@[simp] theorem queriesWith_query_bind (answer : (q : ι) → spec q) (q : ι)
    (next : spec q → OracleComp spec α) :
    queriesWith answer (query q >>= next) = q :: queriesWith answer (next (answer q)) := rfl

/-- Answering the first call and continuing. -/
@[simp] theorem interpret_id_query_bind (answer : (q : ι) → spec q) (q : ι)
    (next : spec q → OracleComp spec α) :
    interpret (m := Id) answer (query q >>= next) = interpret (m := Id) answer (next (answer q)) :=
  rfl

/-- A sequence makes the requests of its first part, then those of the continuation selected by
the first result. -/
private theorem queriesWith_bind (answer : (q : ι) → spec q) (program : OracleComp spec α)
    (next : α → OracleComp spec β) :
    queriesWith answer (program >>= next) = queriesWith answer program ++
      queriesWith answer (next (interpret (m := Id) answer program)) := by
  induction program using PFunctor.FreeM.induction with
  | pure a => rfl
  | lift_bind q cont ih =>
    exact congrArg (q :: ·) (ih (answer q))

/-- Postprocessing the result makes no request. -/
@[simp] theorem queriesWith_map (answer : (q : ι) → spec q) (f : α → β)
    (program : OracleComp spec α) :
    queriesWith answer (f <$> program) = queriesWith answer program := by
  rw [← bind_pure_comp, queriesWith_bind, queriesWith_pure, List.append_nil]

/-- **Locality.** Answer functions that agree on the requests made under one of them give the
same result and the same requests. -/
theorem interpret_id_congr (answer answer' : (q : ι) → spec q) (program : OracleComp spec α)
    (h : ∀ q ∈ queriesWith answer program, answer' q = answer q) :
    interpret (m := Id) answer' program = interpret (m := Id) answer program ∧
      queriesWith answer' program = queriesWith answer program := by
  induction program using PFunctor.FreeM.induction with
  | pure a => exact ⟨rfl, rfl⟩
  | lift_bind q cont ih =>
    have hq : answer' q = answer q := h q (List.mem_cons_self ..)
    have hrest := ih (answer q) fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    change interpret (m := Id) answer' (cont (answer' q)) =
        interpret (m := Id) answer (cont (answer q)) ∧
      q :: queriesWith answer' (cont (answer' q)) = q :: queriesWith answer (cont (answer q))
    rw [hq]
    exact ⟨hrest.1, congrArg (q :: ·) hrest.2⟩

end OracleComp

namespace Complexity

open Probability Turing.MultiTapeTM

variable {Operation α β : Type}

/-- Deterministic programs whose calls are word requests on the channels `Operation`, answered by
words. -/
abbrev WordQueryComp (Operation β : Type) :=
  OracleComp (fun _ : Operation × List Bool => List Bool) β

open Classical in
/-- The oracle language `A` answers a request `(op, w)` with the one-bit word
`[decide (w ∈ A)]`, on every channel `op`. -/
noncomputable def languageOracle (A : Set (List Bool)) (q : Operation × List Bool) : List Bool :=
  [decide (q.2 ∈ A)]

open Classical in
theorem languageOracle_apply (A : Set (List Bool)) (q : Operation × List Bool) :
    languageOracle A q = [decide (q.2 ∈ A)] := rfl

/-- Language oracles that agree on every word requested by `program` under one of them give the
same run. -/
theorem interpret_languageOracle_congr {A B : Set (List Bool)} (program : WordQueryComp Operation α)
    (h : ∀ q ∈ OracleComp.queriesWith (languageOracle A) program, q.2 ∈ B ↔ q.2 ∈ A) :
    OracleComp.interpret (m := Id) (languageOracle B) program =
        OracleComp.interpret (m := Id) (languageOracle A) program ∧
      OracleComp.queriesWith (languageOracle B) program =
        OracleComp.queriesWith (languageOracle A) program :=
  OracleComp.interpret_id_congr _ _ program fun q hq =>
    congrArg (· :: []) (decide_eq_decide.mpr (h q hq))

/-- `f` is computable in polynomial time relative to the oracle language `A`: a deterministic
word-query program computes `f` against `A`, and one finite machine under one polynomial clock
realizes the program against every stateful oracle, charging request construction and reply
access. This is the oracle Turing machine of [Arora and Barak, Section 3.4][AroraBarak09]. -/
@[fun_prop]
def ComputableInPolyTimeWithOracle (A : Set (List Bool)) (f : α → β) (input : α ↪ List Bool)
    (output : β ↪ List Bool) : Prop :=
  ∃ program : α → WordQueryComp Unit β,
    IsOraclePPTOn input output (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
      ∀ a, OracleComp.interpret (m := Id) (languageOracle A) (program a) = f a

/-- A polynomial-time computation makes no request, so it is polynomial time relative to every
oracle. -/
@[fun_prop]
theorem _root_.Turing.MultiTapeTM.ComputableInPolyTime.computableInPolyTimeWithOracle
    {f : α → β} {input : α ↪ List Bool} {output : β ↪ List Bool}
    (h : ComputableInPolyTime f input output) (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracle A f input output := by
  have h := h.tidy
  exact ⟨fun a => pure (f a), h.isOraclePPTOn, fun _ => rfl⟩

/-- One deterministic polynomial-time oracle program whose function against every oracle language
satisfying `Admissible` satisfies `Spec`. The program is fixed before the oracle language, so
answers on words unconstrained by `Admissible` may be arbitrary. -/
def PolyTimeOracleProgram (input : α ↪ List Bool) (output : β ↪ List Bool)
    (Admissible : Set (List Bool) → Prop) (Spec : (α → β) → Prop) : Prop :=
  ∃ program : α → WordQueryComp Unit β,
    IsOraclePPTOn input output (fun a => OracleComp.interpret ProbOracleComp.query (program a)) ∧
      ∀ A : Set (List Bool), Admissible A →
        Spec (fun a => OracleComp.interpret (m := Id) (languageOracle A) (program a))

/-- `ComputableInPolyTimeWithOracle` is `PolyTimeOracleProgram` for a single oracle language and a
single target function. -/
theorem computableInPolyTimeWithOracle_iff_polyTimeOracleProgram {A : Set (List Bool)}
    {f : α → β} {input : α ↪ List Bool} {output : β ↪ List Bool} :
    ComputableInPolyTimeWithOracle A f input output ↔
      PolyTimeOracleProgram input output (· = A) (· = f) :=
  exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun h _ hA => hA ▸ funext h, fun h a => congrFun (h A rfl) a⟩

/-- A polynomial-time function makes no oracle request, so it satisfies `Spec` against every
admissible oracle language whenever `g` does. -/
theorem PolyTimeOracleProgram.of_polyTime {g : α → β} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {Admissible : Set (List Bool) → Prop} {Spec : (α → β) → Prop}
    (hg : ComputableInPolyTime g input output) (hSpec : ∀ A, Admissible A → Spec g) :
    PolyTimeOracleProgram input output Admissible Spec :=
  ⟨fun a => pure (g a), hg.tidy.isOraclePPTOn, hSpec⟩

/-- Evaluating a `PolyTimeOracleProgram` against any admissible oracle language `A` yields a
function computable in polynomial time relative to `A` satisfying `Spec`. -/
theorem PolyTimeOracleProgram.exists_computableInPolyTimeWithOracle
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    {Admissible : Set (List Bool) → Prop} {Spec : (α → β) → Prop}
    (h : PolyTimeOracleProgram input output Admissible Spec)
    {A : Set (List Bool)} (hA : Admissible A) :
    ∃ g : α → β, ComputableInPolyTimeWithOracle A g input output ∧ Spec g :=
  let ⟨program, hprogram, hSpec⟩ := h
  ⟨_, ⟨program, hprogram, fun _ => rfl⟩, hSpec A hA⟩

/-- A function computable in polynomial time relative to a single oracle language `A` witnesses
`PolyTimeOracleProgram` whenever `A` is the unique admissible oracle language. -/
theorem PolyTimeOracleProgram.of_computableInPolyTimeWithOracle {A : Set (List Bool)}
    {g : α → β} {input : α ↪ List Bool} {output : β ↪ List Bool}
    {Admissible : Set (List Bool) → Prop} {Spec : (α → β) → Prop}
    (hg : ComputableInPolyTimeWithOracle A g input output)
    (hSpec : ∀ A', Admissible A' → A' = A ∧ Spec g) :
    PolyTimeOracleProgram input output Admissible Spec := by
  obtain ⟨program, hcert, hprogram⟩ := hg
  refine ⟨program, hcert, fun A' hA' => ?_⟩
  obtain ⟨rfl, h⟩ := hSpec A' hA'
  simpa only [funext hprogram] using h

/-- The problems decidable in polynomial time relative to the oracle language `A`, with respect to
the encoding `enc` of instances: `Cslib.Complexity.P` with an oracle
[Arora and Barak, Section 3.4][AroraBarak09]. -/
def PWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ f : α → Bool, ComputableInPolyTimeWithOracle A f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true}

theorem mem_PWithOracle {A : Set (List Bool)} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ PWithOracle A enc ↔ ∃ f : α → Bool,
      ComputableInPolyTimeWithOracle A f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true :=
  Iff.rfl

/-- The problems with verifiers computable in polynomial time relative to the oracle language `A`
and polynomially long certificates: `Cslib.Complexity.NP` with an oracle
[Arora and Barak, Section 3.4][AroraBarak09]. -/
def NPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool ∧ IsVerifier enc p V L}

theorem mem_NPWithOracle {A : Set (List Bool)} {enc : α ↪ List Bool} {L : Set α} :
    L ∈ NPWithOracle A enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool ∧ IsVerifier enc p V L :=
  Iff.rfl

attribute [local fun_prop] ComputableInPolySpace.tidy in
attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Every problem in `P` is in `P` relative to every oracle. -/
theorem P_subset_PWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    P enc ⊆ PWithOracle A enc := fun _ ⟨f, hf, h⟩ =>
  ⟨f, hf.computableInPolyTimeWithOracle A, h⟩

attribute [local fun_prop] ComputableInPolySpace.tidy in
attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- Every problem in `NP` is in `NP` relative to every oracle. -/
theorem NP_subset_NPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    NP enc ⊆ NPWithOracle A enc := fun _ ⟨p, V, hV, h⟩ =>
  ⟨p, V, hV.computableInPolyTimeWithOracle A, h⟩

end Complexity

end Cslib
