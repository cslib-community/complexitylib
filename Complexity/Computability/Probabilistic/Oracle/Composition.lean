/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle.Normalization
public import Complexity.Computability.Probabilistic.PPT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Composing strict oracle PPT programs

Strict oracle PPT certificates compose like closed ones: by monadic `bind`, with captured input,
deterministic pre- and postprocessing, conditionals and bounded adaptive loops. Every rule
quantifies over all shared stateful oracles and arbitrarily long replies, and preserves the
complete joint law of the result and the external oracle state.

Each rule first replaces its premises by clean realizations
(`Cslib.Probability.IsOraclePPTOn.isTidyOraclePPTOn`), so a later phase never sees partial
requests or stale storage left by an earlier one, and then composes those. Conditionals execute
only the selected branch: an unselected branch makes no external call. The only primitive
external operation is `query_take`, which returns a charged prefix of one reply; returning a full
unbounded reply is not oracle PPT (`ComplexityTests.OraclePPT`).

## Main results

* `Cslib.Probability.IsOraclePPTOn.query_take`: one external call returning a reply prefix.
* `Cslib.Probability.IsPPTOn.isOraclePPTOn`: closed PPT programs are oracle PPT via `sample`.
* `Cslib.Probability.IsOraclePPTOn.isPPTOn`: conversely, a sampled closed program certified
  without external channels is closed PPT.
* `Cslib.Probability.IsOraclePPTOn.bind`, `.bind_with`, `.pair`, `.keep_input`, `.map`,
  `.map_with`, `.preprocess`: composition with charged intermediate data.
* `Cslib.Probability.IsOraclePPTOn.cond`, `.ite`, `.finite_cases`: dispatch to one branch.
* `Cslib.Probability.IsOraclePPTOn.iterate_spec`, `.iterateWith_spec`,
  `.iterateWith_of_bounded_growth`, `.iterate_of_bounded_growth`: bounded adaptive loops.
* `Cslib.Probability.IsOraclePPTOn.query_take'`, `.pair'`, `.preprocess'`, `.map'`,
  `.map_with'`, `.cond'`, `.ite'`, `.finite_cases'`, `.iterate_spec'`, `.iterateWith_spec'`,
  `.iterateWith_of_bounded_growth'`, `.iterate_of_bounded_growth'`: the same rules with plain
  `ComputableInPolyTime` side conditions. These primed names are transitional (#608, #862): once
  the remaining callers migrate, the unprimed names are restated with plain hypotheses and the
  primed ones are removed.

## References

Adapts the closed composition rules of Computability/Probabilistic/Composition.lean and
Computability/Probabilistic/Adaptive.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to strict oracle PPT.
-/

@[expose] public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

variable {Operation α β γ σ : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
  {stateEncoding : σ ↪ List Bool}

namespace IsOraclePPTOn

/-- One external call on channel `op` with an efficiently computed request, returning at most an
efficiently computed number of reply bits. Building the request and reading the prefix are
charged; the remainder of an arbitrarily long reply is never read. -/
@[fun_prop]
theorem query_take [Finite Operation] (op : Operation) {request : α → List Bool}
    {limit : α → ℕ} (hrequest : ComputableTidilyInPolyTime request input encBits)
    (hlimit : ComputableTidilyInPolyTime limit input encUnary) :
    IsOraclePPTOn input encBits (fun a => List.take (limit a) <$>
      ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
        (op, request a)) :=
  ((IsTidyOraclePPTOn.query_take op).preprocess (.of_tidy (hrequest.prod hlimit))).isOraclePPTOn

/-- `Cslib.Probability.IsOraclePPTOn.query_take` with plain polynomial-time request and limit. -/
@[fun_prop]
theorem query_take' [Finite Operation] (op : Operation) {request : α → List Bool}
    {limit : α → ℕ} (hrequest : ComputableInPolyTime request input encBits)
    (hlimit : ComputableInPolyTime limit input encUnary) :
    IsOraclePPTOn input encBits (fun a => List.take (limit a) <$>
      ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
        (op, request a)) :=
  ((IsTidyOraclePPTOn.query_take op).preprocess (hrequest.prod hlimit)).isOraclePPTOn

/-- Sequence two strict oracle PPT programs. The intermediate output length bounds the
continuation's clock, and every effect of both phases on the shared oracle is retained. -/
@[fun_prop]
theorem bind {first : α → WordOracleComp Operation β} {second : β → WordOracleComp Operation γ}
    (hfirst : IsOraclePPTOn input middle first) (hsecond : IsOraclePPTOn middle output second) :
    IsOraclePPTOn input output (fun a => do
      let b ← first a
      second b) :=
  (hfirst.isTidyOraclePPTOn.bind hsecond.isTidyOraclePPTOn).isOraclePPTOn

/-- Retain efficiently computed input data beside an oracle result. -/
@[fun_prop]
theorem pair {program : α → WordOracleComp Operation γ} {f : α → β}
    (hprogram : IsOraclePPTOn input output program)
    (hf : ComputableTidilyInPolyTime f input middle) :
    IsOraclePPTOn input (encPair middle output) (fun a => (fun b => (f a, b)) <$> program a) :=
  (hprogram.isTidyOraclePPTOn.pair (.of_tidy hf)).isOraclePPTOn

/-- `Cslib.Probability.IsOraclePPTOn.pair` with a plain polynomial-time certificate. -/
@[fun_prop]
theorem pair' {program : α → WordOracleComp Operation γ} {f : α → β}
    (hprogram : IsOraclePPTOn input output program)
    (hf : ComputableInPolyTime f input middle) :
    IsOraclePPTOn input (encPair middle output) (fun a => (fun b => (f a, b)) <$> program a) :=
  (hprogram.isTidyOraclePPTOn.pair hf).isOraclePPTOn

/-- Keep the original argument available to a later computation, charging its encoded copy. -/
theorem keep_input {program : α → WordOracleComp Operation β}
    (hprogram : IsOraclePPTOn input middle program) :
    IsOraclePPTOn input (encPair input middle) (fun a => (fun b => (a, b)) <$> program a) :=
  hprogram.pair' ComputableInPolyTime.id'

/-- A continuation may use both the caller's input and the first result. -/
@[fun_prop]
theorem bind_with {first : α → WordOracleComp Operation β}
    {second : α → β → WordOracleComp Operation γ}
    (hfirst : IsOraclePPTOn input middle first)
    (hsecond : IsOraclePPTOn (encPair input middle) output (fun pair => second pair.1 pair.2)) :
    IsOraclePPTOn input output (fun a => do
      let b ← first a
      second a b) :=
  (hfirst.isTidyOraclePPTOn.bind_with hsecond.isTidyOraclePPTOn).isOraclePPTOn

/-- Efficiently prepare the argument of a strict oracle PPT program. -/
@[fun_prop]
theorem preprocess {program : β → WordOracleComp Operation γ} {prepare : α → β}
    (hprogram : IsOraclePPTOn middle output program)
    (hprepare : ComputableTidilyInPolyTime prepare input middle) :
    IsOraclePPTOn input output (fun a => program (prepare a)) :=
  (hprogram.isTidyOraclePPTOn.preprocess (.of_tidy hprepare)).isOraclePPTOn

/-- `Cslib.Probability.IsOraclePPTOn.preprocess` with a plain polynomial-time preparation. -/
@[fun_prop]
theorem preprocess' {program : β → WordOracleComp Operation γ} {prepare : α → β}
    (hprogram : IsOraclePPTOn middle output program)
    (hprepare : ComputableInPolyTime prepare input middle) :
    IsOraclePPTOn input output (fun a => program (prepare a)) :=
  (hprogram.isTidyOraclePPTOn.preprocess hprepare).isOraclePPTOn

/-- Efficient deterministic postprocessing of every result preserves strict oracle PPT. -/
@[fun_prop]
theorem map {program : α → WordOracleComp Operation β} {f : β → γ}
    (hprogram : IsOraclePPTOn input middle program)
    (hf : ComputableTidilyInPolyTime f middle output) :
    IsOraclePPTOn input output (fun a => f <$> program a) :=
  (hprogram.isTidyOraclePPTOn.map (.of_tidy hf)).isOraclePPTOn

/-- `Cslib.Probability.IsOraclePPTOn.map` with a plain polynomial-time postprocessing. -/
@[fun_prop]
theorem map' {program : α → WordOracleComp Operation β} {f : β → γ}
    (hprogram : IsOraclePPTOn input middle program)
    (hf : ComputableInPolyTime f middle output) :
    IsOraclePPTOn input output (fun a => f <$> program a) :=
  (hprogram.isTidyOraclePPTOn.map hf).isOraclePPTOn

/-- A deterministic callback may capture the original argument. -/
@[fun_prop]
theorem map_with {program : α → WordOracleComp Operation β} {f : α → β → γ}
    (hprogram : IsOraclePPTOn input middle program)
    (hf : ComputableTidilyInPolyTime (fun pair => f pair.1 pair.2) (encPair input middle) output) :
    IsOraclePPTOn input output (fun a => f a <$> program a) :=
  (hprogram.isTidyOraclePPTOn.map_with (.of_tidy hf)).isOraclePPTOn

/-- `Cslib.Probability.IsOraclePPTOn.map_with` with a plain polynomial-time callback. -/
@[fun_prop]
theorem map_with' {program : α → WordOracleComp Operation β} {f : α → β → γ}
    (hprogram : IsOraclePPTOn input middle program)
    (hf : ComputableInPolyTime (fun pair => f pair.1 pair.2) (encPair input middle) output) :
    IsOraclePPTOn input output (fun a => f a <$> program a) :=
  (hprogram.isTidyOraclePPTOn.map_with hf).isOraclePPTOn

/-- Select a branch with an efficient Boolean condition. Only the selected branch runs: the other
branch makes no external call and cannot change the oracle state. -/
@[fun_prop]
theorem cond {condition : α → Bool} {yes no : α → WordOracleComp Operation γ}
    (hcondition : ComputableTidilyInPolyTime condition input encBool)
    (hyes : IsOraclePPTOn input output yes) (hno : IsOraclePPTOn input output no) :
    IsOraclePPTOn input output (fun a => if condition a then yes a else no a) :=
  (hyes.isTidyOraclePPTOn.cond (.of_tidy hcondition) hno.isTidyOraclePPTOn).isOraclePPTOn

/-- `Cslib.Probability.IsOraclePPTOn.cond` with a plain polynomial-time condition. -/
@[fun_prop]
theorem cond' {condition : α → Bool} {yes no : α → WordOracleComp Operation γ}
    (hcondition : ComputableInPolyTime condition input encBool)
    (hyes : IsOraclePPTOn input output yes) (hno : IsOraclePPTOn input output no) :
    IsOraclePPTOn input output (fun a => if condition a then yes a else no a) :=
  (hyes.isTidyOraclePPTOn.cond hcondition hno.isTidyOraclePPTOn).isOraclePPTOn

/-- Select a branch with an efficiently decidable condition, executing only that branch. -/
@[fun_prop]
theorem ite {condition : α → Prop} [∀ a, Decidable (condition a)]
    {yes no : α → WordOracleComp Operation γ}
    (hcondition : ComputableTidilyInPolyTime (fun a => decide (condition a)) input encBool)
    (hyes : IsOraclePPTOn input output yes) (hno : IsOraclePPTOn input output no) :
    IsOraclePPTOn input output (fun a => if condition a then yes a else no a) :=
  (hyes.isTidyOraclePPTOn.ite (.of_tidy hcondition) hno.isTidyOraclePPTOn).isOraclePPTOn

/-- `Cslib.Probability.IsOraclePPTOn.ite` with a plain polynomial-time decision. -/
@[fun_prop]
theorem ite' {condition : α → Prop} [∀ a, Decidable (condition a)]
    {yes no : α → WordOracleComp Operation γ}
    (hcondition : ComputableInPolyTime (fun a => decide (condition a)) input encBool)
    (hyes : IsOraclePPTOn input output yes) (hno : IsOraclePPTOn input output no) :
    IsOraclePPTOn input output (fun a => if condition a then yes a else no a) :=
  (hyes.isTidyOraclePPTOn.ite hcondition hno.isTidyOraclePPTOn).isOraclePPTOn

/-- A computed finite tag selects one certified branch, which alone is executed. -/
theorem finite_cases {Tag : Type} [Finite Tag] {tagEncoding : Tag ↪ List Bool} {tag : α → Tag}
    {branch : Tag → α → WordOracleComp Operation γ} [Finite Operation]
    (htag : ComputableTidilyInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, IsOraclePPTOn input output (branch choice)) :
    IsOraclePPTOn input output (fun a => branch (tag a) a) :=
  (IsTidyOraclePPTOn.finite_cases (.of_tidy htag) fun choice =>
    (hbranch choice).isTidyOraclePPTOn).isOraclePPTOn

/-- `Cslib.Probability.IsOraclePPTOn.finite_cases` with a plain polynomial-time tag. -/
theorem finite_cases' {Tag : Type} [Finite Tag] {tagEncoding : Tag ↪ List Bool} {tag : α → Tag}
    {branch : Tag → α → WordOracleComp Operation γ} [Finite Operation]
    (htag : ComputableInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, IsOraclePPTOn input output (branch choice)) :
    IsOraclePPTOn input output (fun a => branch (tag a) a) :=
  (IsTidyOraclePPTOn.finite_cases htag fun choice =>
    (hbranch choice).isTidyOraclePPTOn).isOraclePPTOn

/-- A bounded adaptive loop is strict oracle PPT when one invariant bounds every reachable
state. The invariant holds for every possible result under every stateful oracle, and it is also
established for the final state. Every iteration may query the shared oracle. -/
theorem iterate_spec {initial : α → σ} {count : α → ℕ}
    {step : σ → WordOracleComp Operation σ}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : IsOraclePPTOn stateEncoding stateEncoding step)
    (invariant : α → ℕ → σ → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ OracleComp.support (step state), invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    IsOraclePPTOn input stateEncoding
        (fun a => OracleComp.iterate (count a) step (initial a)) ∧
      ∀ a, ∀ state ∈ OracleComp.support (OracleComp.iterate (count a) step (initial a)),
        invariant a (count a) state :=
  let h := IsTidyOraclePPTOn.iterate_spec (.of_tidy hcount) (.of_tidy hinitial)
    hstep.isTidyOraclePPTOn invariant hbase hpreserve hsize hbound
  ⟨h.1.isOraclePPTOn, h.2⟩

/-- `Cslib.Probability.IsOraclePPTOn.iterate_spec` with plain polynomial-time count and initial
state. -/
theorem iterate_spec' {initial : α → σ} {count : α → ℕ}
    {step : σ → WordOracleComp Operation σ}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsOraclePPTOn stateEncoding stateEncoding step)
    (invariant : α → ℕ → σ → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ OracleComp.support (step state), invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    IsOraclePPTOn input stateEncoding
        (fun a => OracleComp.iterate (count a) step (initial a)) ∧
      ∀ a, ∀ state ∈ OracleComp.support (OracleComp.iterate (count a) step (initial a)),
        invariant a (count a) state :=
  let h := IsTidyOraclePPTOn.iterate_spec hcount hinitial
    hstep.isTidyOraclePPTOn invariant hbase hpreserve hsize hbound
  ⟨h.1.isOraclePPTOn, h.2⟩

/-- The loop body may capture the original input; the invariant describes the changing state. -/
theorem iterateWith_spec {initial : α → σ} {count : α → ℕ}
    {step : α → σ → WordOracleComp Operation σ}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : IsOraclePPTOn (encPair input stateEncoding) stateEncoding
      (fun pair => step pair.1 pair.2))
    (invariant : α → ℕ → σ → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ OracleComp.support (step a state), invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    IsOraclePPTOn input stateEncoding
        (fun a => OracleComp.iterate (count a) (step a) (initial a)) ∧
      ∀ a, ∀ state ∈ OracleComp.support (OracleComp.iterate (count a) (step a) (initial a)),
        invariant a (count a) state :=
  let h := IsTidyOraclePPTOn.iterateWith_spec (.of_tidy hcount) (.of_tidy hinitial)
    hstep.isTidyOraclePPTOn invariant hbase hpreserve hsize hbound
  ⟨h.1.isOraclePPTOn, h.2⟩

/-- `Cslib.Probability.IsOraclePPTOn.iterateWith_spec` with plain polynomial-time count and
initial state. -/
theorem iterateWith_spec' {initial : α → σ} {count : α → ℕ}
    {step : α → σ → WordOracleComp Operation σ}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsOraclePPTOn (encPair input stateEncoding) stateEncoding
      (fun pair => step pair.1 pair.2))
    (invariant : α → ℕ → σ → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ OracleComp.support (step a state), invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    IsOraclePPTOn input stateEncoding
        (fun a => OracleComp.iterate (count a) (step a) (initial a)) ∧
      ∀ a, ∀ state ∈ OracleComp.support (OracleComp.iterate (count a) (step a) (initial a)),
        invariant a (count a) state :=
  let h := IsTidyOraclePPTOn.iterateWith_spec hcount hinitial
    hstep.isTidyOraclePPTOn invariant hbase hpreserve hsize hbound
  ⟨h.1.isOraclePPTOn, h.2⟩

/-- Captured-input steps may grow by a polynomially bounded amount depending on that input, for
every possible next state under every stateful oracle. -/
theorem iterateWith_of_bounded_growth {initial : α → σ} {count : α → ℕ}
    {step : α → σ → WordOracleComp Operation σ}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : IsOraclePPTOn (encPair input stateEncoding) stateEncoding
      (fun pair => step pair.1 pair.2))
    {growth : α → ℕ} (hpoly : PolyBounded (fun a => (input a).length) growth)
    (hgrowth : ∀ a state, ∀ next ∈ OracleComp.support (step a state),
      (stateEncoding next).length ≤ (stateEncoding state).length + growth a) :
    IsOraclePPTOn input stateEncoding
      (fun a => OracleComp.iterate (count a) (step a) (initial a)) :=
  (IsTidyOraclePPTOn.iterateWith_of_bounded_growth (.of_tidy hcount) (.of_tidy hinitial)
    hstep.isTidyOraclePPTOn hpoly hgrowth).isOraclePPTOn

/-- `Cslib.Probability.IsOraclePPTOn.iterateWith_of_bounded_growth` with plain polynomial-time
count and initial state. -/
theorem iterateWith_of_bounded_growth' {initial : α → σ} {count : α → ℕ}
    {step : α → σ → WordOracleComp Operation σ}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsOraclePPTOn (encPair input stateEncoding) stateEncoding
      (fun pair => step pair.1 pair.2))
    {growth : α → ℕ} (hpoly : PolyBounded (fun a => (input a).length) growth)
    (hgrowth : ∀ a state, ∀ next ∈ OracleComp.support (step a state),
      (stateEncoding next).length ≤ (stateEncoding state).length + growth a) :
    IsOraclePPTOn input stateEncoding
      (fun a => OracleComp.iterate (count a) (step a) (initial a)) :=
  (IsTidyOraclePPTOn.iterateWith_of_bounded_growth hcount hinitial
    hstep.isTidyOraclePPTOn hpoly hgrowth).isOraclePPTOn

/-- A strict oracle PPT step with constant growth can be repeated a polynomial number of times. -/
theorem iterate_of_bounded_growth {initial : α → σ} {count : α → ℕ}
    {step : σ → WordOracleComp Operation σ}
    (hcount : ComputableTidilyInPolyTime count input encUnary)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : IsOraclePPTOn stateEncoding stateEncoding step)
    {growth : ℕ} (hgrowth : ∀ state, ∀ next ∈ OracleComp.support (step state),
      (stateEncoding next).length ≤ (stateEncoding state).length + growth) :
    IsOraclePPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) :=
  iterateWith_of_bounded_growth (step := fun _ => step) hcount hinitial
    (hstep.preprocess (ComputableTidilyInPolyTime.snd input stateEncoding))
    (.const growth) (fun _ => hgrowth)

/-- `Cslib.Probability.IsOraclePPTOn.iterate_of_bounded_growth` with plain polynomial-time count
and initial state. -/
theorem iterate_of_bounded_growth' {initial : α → σ} {count : α → ℕ}
    {step : σ → WordOracleComp Operation σ}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsOraclePPTOn stateEncoding stateEncoding step)
    {growth : ℕ} (hgrowth : ∀ state, ∀ next ∈ OracleComp.support (step state),
      (stateEncoding next).length ≤ (stateEncoding state).length + growth) :
    IsOraclePPTOn input stateEncoding (fun a => OracleComp.iterate (count a) step (initial a)) :=
  iterateWith_of_bounded_growth' (step := fun _ => step) hcount hinitial
    (hstep.preprocess' (ComputableInPolyTime.snd input stateEncoding))
    (.const growth) (fun _ => hgrowth)

end IsOraclePPTOn

/-- A closed strict PPT program is strict oracle PPT when sampled privately: its machine never
uses an external channel, so every external oracle state is preserved. -/
@[fun_prop]
theorem IsPPTOn.isOraclePPTOn [Finite Operation] {program : α → ProbComp γ}
    (h : IsPPTOn input output program) :
    IsOraclePPTOn (Operation := Operation) input output
      (fun a => ProbOracleComp.sample (program a)) := by
  obtain ⟨k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨inferInstance, k, Control, hfinite, ofClosed machine, c, d,
    fun a State oracle s => ?_⟩
  rw [run_interpret_runOracle_ofClosed, ← h a, ← ProbOracleComp.sample_map,
    ProbOracleComp.run_interpret_sample, ProbComp.eval_map]

/-- A sampled closed program certified without external channels is closed strict PPT: the
realizing machine has no channels, so it is a closed machine with the same output law. -/
theorem IsOraclePPTOn.isPPTOn {program : α → ProbComp γ}
    (h : IsOraclePPTOn (Operation := Empty) input output
      (fun a => ProbOracleComp.sample (program a))) :
    IsPPTOn input output program := by
  obtain ⟨_, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨k, Control, hfinite, machine, c, d, fun a => ?_⟩
  have h := congrArg (PMF.map Prod.fst) (h a Unit (fun q => q.1.elim) ())
  rw [← ProbOracleComp.sample_map, ProbOracleComp.run_interpret_sample,
    runOracle_eq_sample_runClosed, ProbOracleComp.run_interpret_sample,
    PMF.map_comp, PMF.map_comp, ProbComp.eval_map] at h
  have hid : (Prod.fst ∘ fun word : List Bool => (word, ())) = id := rfl
  rwa [hid, PMF.map_id, PMF.map_id] at h

end Cslib.Probability
