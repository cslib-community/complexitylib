/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Tidy
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Foundations.Data.List.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Tidy realizations of oracle PPT programs

`IsTidyOraclePPTOn` strengthens `IsOraclePPTOn` by requiring one finite machine that halts
within a polynomial clock as a clean phase: it starts with blank work tapes and empty query
buffers, works for arbitrary retained answer tapes, and finishes with blank work tapes, empty
query buffers and its input head restored. Its output is appended to the output tape, and the
complete joint law of that output and every external oracle state is exact.

Clean phases compose. This module gives the shared core of the open calculus: deterministic
programs, the bounded-prefix query, fair bits, captured data, monadic composition and branching.
Only the selected branch of a conditional is executed, so unselected branches make no external
call. An unbounded oracle reply is never copied for free: `query_take` charges its prefix length.

Deterministic parts are given by plain certificates (`Turing.MultiTapeTM.ComputableInPolyTime`).
A clean deterministic phase is the tidy normal form of the plain machine
(`Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy`), run with its coin bits ignored,
so no deterministic tidy certificate is needed.

## Main definitions

* `Cslib.Probability.IsTidyOraclePPTOn`: a uniform polynomial-time clean-phase realization.

## Main results

* `Cslib.Probability.IsTidyOraclePPTOn.isOraclePPTOn`: clean realizations are oracle PPT.
* `Cslib.Probability.IsTidyOraclePPTOn.of_computableInPolyTime`: plain deterministic programs are
  clean phases.
* `Cslib.Probability.IsTidyOraclePPTOn.query_take`: one external call returning a reply prefix.
* `Cslib.Probability.IsTidyOraclePPTOn.bind`, `.bind_with`, `.pair`, `.map`, `.preprocess`:
  composition, charging every intermediate word.
* `Cslib.Probability.IsTidyOraclePPTOn.cond`, `.finite_cases`: dispatch executing only the
  selected branch.

## References

The clean-phase combinators adapt the tidy deterministic calculus of cslib (Christian
Reitwiessner) to the probabilistic oracle machines of the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

/-- One finite machine computes the encoded program as a clean phase within a uniform polynomial
clock, preserving the joint law of the output and every shared stateful oracle. -/
def IsTidyOraclePPTOn {Operation α β : Type} [DecidableEq Operation]
    (input : α ↪ List Bool) (output : β ↪ List Bool)
    (program : α → WordOracleComp Operation β) : Prop :=
  Finite Operation ∧ ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
    (machine : MultiTapePTM k Bool Control Operation) (c d : ℕ),
    ∀ a, machine.ComputesTidily (input a) (c * ((input a).length + 1) ^ d) (output <$> program a)

namespace IsTidyOraclePPTOn

variable {Operation α β γ : Type} [DecidableEq Operation]
  {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}

/-- A fixed finite machine with a polynomially bounded clean-phase clock is a certificate. -/
theorem of_polyBounded [Finite Operation] {k : ℕ} {Control : Type} [Finite Control]
    {program : α → WordOracleComp Operation γ}
    (machine : MultiTapePTM k Bool Control Operation) {time : α → ℕ}
    (htime : PolyBounded (fun a => (input a).length) time)
    (h : ∀ a, machine.ComputesTidily (input a) (time a) (output <$> program a)) :
    IsTidyOraclePPTOn input output program := by
  obtain ⟨c, d, htime⟩ := htime.exists_le
  exact ⟨inferInstance, k, Control, inferInstance, machine, c, d, fun a => (h a).mono (htime a)⟩

/-- A clean realization is in particular a strict oracle PPT certificate. -/
theorem isOraclePPTOn {program : α → WordOracleComp Operation γ}
    (h : IsTidyOraclePPTOn input output program) : IsOraclePPTOn input output program := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  exact ⟨hops, k, Control, hfinite, machine, c, d,
    fun a State oracle s => ((h a).runOracle oracle s).symm⟩

/-- Equality of the complete stateful semantics preserves a clean realization. -/
theorem congr {program program' : α → WordOracleComp Operation γ}
    (h : IsTidyOraclePPTOn input output program)
    (heq : ∀ a (State : Type) (oracle : Operation × List Bool → StateT State PMF (List Bool)) s,
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program a)).run s =
      (OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program' a)).run s) :
    IsTidyOraclePPTOn input output program' := by
  obtain ⟨hops, k, Control, hfinite, machine, c, d, h⟩ := h
  refine ⟨hops, k, Control, hfinite, machine, c, d, fun a => (h a).congr ?_⟩
  intro State oracle s
  simp only [OracleComp.interpret_map, StateT.run_map, heq]

/-- A program returning its declared encoding has the same clean realizations. -/
theorem iff_encoded {program : α → WordOracleComp Operation γ} :
    IsTidyOraclePPTOn input output program ↔
      IsTidyOraclePPTOn input encBits (fun a => output <$> program a) := by
  simp only [IsTidyOraclePPTOn, encBits, Function.Embedding.coe_refl, id_map]

/-- Every supported encoded output has polynomial length, independently of all oracle replies. -/
theorem length_le {program : α → WordOracleComp Operation γ}
    (h : IsTidyOraclePPTOn input output program) :
    ∃ c d : ℕ, ∀ a (State : Type)
      (oracle : Operation × List Bool → StateT State PMF (List Bool)) s s' result,
      (result, s') ∈ ((OracleComp.interpret
        (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n)) oracle)
          (program a)).run s).support →
      (output result).length ≤ c * ((input a).length + 1) ^ d :=
  h.isOraclePPTOn.length_le

/-- One external call submits `query` on channel `op` and returns at most `limit` reply bits.
Unframing the request, the call and scanning the unary limit are all charged. -/
theorem query_take [Finite Operation] (op : Operation) :
    IsTidyOraclePPTOn (encPair encBits encUnary) encBits (fun request : List Bool × ℕ =>
      List.take request.2 <$>
        ProbOracleComp.query (spec := fun _ : Operation × List Bool => List Bool)
          (op, request.1)) := by
  refine ⟨inferInstance, 0, QueryTakeState ⊕ RewindState, inferInstance, queryTakePTM op, 4, 1,
    fun request => ?_⟩
  have hlength : (encPair encBits encUnary request).length =
      2 * request.1.length + 1 + request.2 := by
    simp [encPair_apply, encBits_apply, encUnary_apply]
  refine ((computesTidily_queryTakePTM op request.1 request.2).mono ?_).congr ?_
  · rw [hlength]
    lia
  · intro State oracle s
    simp only [encBits, Function.Embedding.coe_refl, id_map]

/-- A fair private bit leaves every external oracle state unchanged. -/
theorem uniform_bool [Finite Operation] (input : α ↪ List Bool) :
    IsTidyOraclePPTOn (Operation := Operation) input encBool
      (fun _ => ProbOracleComp.sample (ProbComp.uniform Bool)) :=
  ⟨inferInstance, 0, Unit, inferInstance, coinMachine, 1, 0, fun a => by
    simpa only [pow_zero, Nat.mul_one] using computesTidily_coinMachine (input a)⟩

/-- **Efficient deterministic programs are clean phases** that make no external call. A plain
certificate is made tidy by the tidy normal form of its machine
(`Turing.MultiTapeTM.ComputesInTimeAndSpace.computesTidily_tidy`), within time `2 t + 3 s + O(1)`
for a plain machine within time `t` and space `s`. -/
theorem of_computableInPolyTime [Finite Operation] {f : α → γ}
    (h : ComputableInPolyTime f input output) :
    IsTidyOraclePPTOn (Operation := Operation) input output (fun a => pure (f a)) := by
  obtain ⟨t, s, ht, hs, k, State, hfinite, machine, hmachine⟩ := h
  refine of_polyBounded (ofDeterministic (tidy false true machine))
    (time := fun a => 2 * t (input a).length + 3 * s (input a).length + 2 * k + 4)
    (.of_polynomiallyBounded (fun a => (input a).length)
      (bound := fun n => 2 * t n + 3 * s n + 2 * k + 4) (by fun_prop)) fun a => ?_
  simpa only [map_pure] using ComputesTidily.of_deterministic (Operation := Operation)
    ((hmachine a).computesTidily_tidy Bool.false_ne_true)

/-- The machine and clock of a clean deterministic phase, for composing it with others. -/
private theorem exists_computesTidily_pure [Finite Operation] {f : α → γ}
    (h : ComputableInPolyTime f input output) :
    ∃ (k : ℕ) (Control : Type) (_ : Finite Control)
      (machine : MultiTapePTM k Bool Control Operation) (c d : ℕ),
      ∀ a, machine.ComputesTidily (input a) (c * ((input a).length + 1) ^ d)
        (pure (output (f a))) :=
  let ⟨_, k, Control, hfinite, machine, c, d, hmachine⟩ :=
    of_computableInPolyTime (Operation := Operation) h
  ⟨k, Control, hfinite, machine, c, d, fun a => by simpa only [map_pure] using hmachine a⟩

/-- Retain efficiently computed data beside a probabilistic oracle result. -/
theorem pair {program : α → WordOracleComp Operation γ} {f : α → β}
    (hprogram : IsTidyOraclePPTOn input output program)
    (hf : ComputableInPolyTime f input middle) :
    IsTidyOraclePPTOn input (encPair middle output)
      (fun a => (fun b => (f a, b)) <$> program a) := by
  have := hprogram.1
  have hframe := ComputableInPolyTime.bitsFrame middle
  obtain ⟨kp, Prepare, hfiniteP, prepare, cp, dp, hprepare⟩ :=
    exists_computesTidily_pure (Operation := Operation) (hframe.comp hf)
  obtain ⟨hops, k, Control, hfinite, source, c, d, hsource⟩ := hprogram
  refine of_polyBounded (appendPTM prepare source)
    (time := fun a => cp * ((input a).length + 1) ^ dp + c * ((input a).length + 1) ^ d)
    ((PolyBounded.of_forall_le cp dp fun _ => le_rfl).add
      (.of_forall_le c d fun _ => le_rfl)) fun a => ?_
  have h := (hprepare a).append fun _ _ _ _ _ _ => hsource a
  simp only [encBits, Function.Embedding.coe_refl, id_eq, pure_bind] at h
  rw [Functor.map_map] at h ⊢
  exact h

/-- Sequence two clean realizations. The first output length bounds the continuation's clock,
and transferring the intermediate word is charged. -/
theorem bind {first : α → WordOracleComp Operation β} {second : β → WordOracleComp Operation γ}
    (hfirst : IsTidyOraclePPTOn input middle first)
    (hsecond : IsTidyOraclePPTOn middle output second) :
    IsTidyOraclePPTOn input output (fun a => first a >>= second) := by
  classical
  obtain ⟨hops, k₁, Control₁, hfinite₁, source, c₁, d₁, hsource⟩ := hfirst
  obtain ⟨_, k₂, Control₂, hfinite₂, target, c₂, d₂, htarget⟩ := hsecond
  let firstTime := fun length => c₁ * (length + 1) ^ d₁
  let secondTime := fun length => c₂ * (firstTime length + 1) ^ d₂
  let continuation : List Bool → WordOracleComp Operation (List Bool) :=
    Function.extend middle (fun b => output <$> second b) (fun _ => pure [])
  have hcontinuation (b : β) : continuation (middle b) = output <$> second b :=
    middle.injective.extend_apply _ _ b
  have hpoly : Cslib.PolynomiallyBounded
      (fun length => 5 * firstTime length + secondTime length + 9) := by
    fun_prop
  refine of_polyBounded (target.tidyComp source true)
    (.of_polynomiallyBounded (fun a => (input a).length) hpoly) fun a => ?_
  have hcomp := (hsource a).comp true (prog₂ := continuation) (t₂ := secondTime (input a).length)
    (fun word State oracle s s' hword => by
      have hlength := (hsource a).length_output_le oracle s hword
      rw [OracleComp.interpret_map, StateT.run_map, PMF.monad_map_eq_map,
        PMF.mem_support_map_iff] at hword
      obtain ⟨⟨b, s₁⟩, _, heq⟩ := hword
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [hcontinuation]
      exact (htarget b).mono (Nat.mul_le_mul_left c₂
        (Nat.pow_le_pow_left (Nat.add_le_add_right hlength 1) d₂)))
  simpa only [bind_map_left, hcontinuation, map_bind] using hcomp

/-- A continuation may use both the caller's input and the first result. -/
theorem bind_with {first : α → WordOracleComp Operation β}
    {second : α → β → WordOracleComp Operation γ}
    (hfirst : IsTidyOraclePPTOn input middle first)
    (hsecond : IsTidyOraclePPTOn (encPair input middle) output
      (fun pair => second pair.1 pair.2)) :
    IsTidyOraclePPTOn input output (fun a => first a >>= second a) := by
  simpa only [bind_map_left] using
    (hfirst.pair (ComputableInPolyTime.id' (encIn := input))).bind hsecond

/-- Efficiently prepare the argument of a clean realization. -/
theorem preprocess {program : β → WordOracleComp Operation γ} {prepare : α → β}
    (hprogram : IsTidyOraclePPTOn middle output program)
    (hprepare : ComputableInPolyTime prepare input middle) :
    IsTidyOraclePPTOn input output (fun a => program (prepare a)) := by
  have := hprogram.1
  simpa only [pure_bind] using (of_computableInPolyTime hprepare).bind hprogram

/-- Efficient deterministic postprocessing of every result preserves clean realization. -/
theorem map {program : α → WordOracleComp Operation β} {f : β → γ}
    (hprogram : IsTidyOraclePPTOn input middle program)
    (hf : ComputableInPolyTime f middle output) :
    IsTidyOraclePPTOn input output (fun a => f <$> program a) := by
  have := hprogram.1
  simpa only [bind_pure_comp] using hprogram.bind (of_computableInPolyTime hf)

/-- A deterministic callback may capture the original argument. -/
theorem map_with {program : α → WordOracleComp Operation β} {f : α → β → γ}
    (hprogram : IsTidyOraclePPTOn input middle program)
    (hf : ComputableInPolyTime (fun pair => f pair.1 pair.2) (encPair input middle) output) :
    IsTidyOraclePPTOn input output (fun a => f a <$> program a) := by
  have := hprogram.1
  simpa only [bind_pure_comp] using
    hprogram.bind_with (second := fun a b => pure (f a b)) (of_computableInPolyTime hf)

/-- Select a branch with an efficient Boolean condition. Only the selected branch runs, so an
unselected branch makes no external call and cannot change any oracle state. -/
theorem cond {condition : α → Bool} {yes no : α → WordOracleComp Operation γ}
    (hcondition : ComputableInPolyTime condition input encBool)
    (hyes : IsTidyOraclePPTOn input output yes) (hno : IsTidyOraclePPTOn input output no) :
    IsTidyOraclePPTOn input output (fun a => if condition a then yes a else no a) := by
  have := hyes.1
  let test (a : α) : List Bool := if condition a then [true] else []
  have htest : ComputableInPolyTime test input encBits :=
    (ComputableInPolyTime.of_finite (encIn := encBool) (encOut := encBits)
      (fun b : Bool => if b then [true] else [])).comp hcondition
  obtain ⟨kt, Test, hfiniteT, tester, ct, dt, htester⟩ :=
    exists_computesTidily_pure (Operation := Operation) htest
  obtain ⟨hops, k₁, Control₁, hfinite₁, yesMachine, c₁, d₁, hyesMachine⟩ := hyes
  obtain ⟨_, k₂, Control₂, hfinite₂, noMachine, c₂, d₂, hnoMachine⟩ := hno
  refine of_polyBounded (itePTM tester yesMachine noMachine)
    (((((PolyBounded.of_forall_le ct dt fun _ => le_rfl).add
      (.of_forall_le c₁ d₁ fun _ => le_rfl)).add (.of_forall_le c₂ d₂ fun _ => le_rfl))).add
        (.const 10)) fun a => ?_
  have hite := ComputesTidily.ite (w := test a) (htester a)
    (fun _ => hyesMachine a) (fun _ => hnoMachine a)
  cases hc : condition a with
  | false =>
    simp only [test, hc, Bool.false_eq_true, ↓reduceIte, List.length_nil] at hite ⊢
    exact hite.mono (by lia)
  | true =>
    simp only [test, hc, ↓reduceIte, reduceCtorEq, List.length_singleton] at hite ⊢
    exact hite.mono (by lia)

/-- Select a branch with an efficiently decidable condition, executing only that branch. -/
theorem ite {condition : α → Prop} [∀ a, Decidable (condition a)]
    {yes no : α → WordOracleComp Operation γ}
    (hcondition : ComputableInPolyTime (fun a => decide (condition a)) input encBool)
    (hyes : IsTidyOraclePPTOn input output yes) (hno : IsTidyOraclePPTOn input output no) :
    IsTidyOraclePPTOn input output (fun a => if condition a then yes a else no a) := by
  simpa only [decide_eq_true_eq] using hyes.cond hcondition hno

/-- A computed finite tag selects one certified branch, which alone is executed. -/
theorem finite_cases {Tag : Type} [Finite Tag] {tagEncoding : Tag ↪ List Bool} {tag : α → Tag}
    {branch : Tag → α → WordOracleComp Operation γ} [Finite Operation]
    (htag : ComputableInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, IsTidyOraclePPTOn input output (branch choice)) :
    IsTidyOraclePPTOn input output (fun a => branch (tag a) a) := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    apply (of_computableInPolyTime (Operation := Operation)
      (ComputableInPolyTime.of_finite (encIn := input) (encOut := output)
        (fun a : α => isEmptyElim a))).congr
    intro a
    exact isEmptyElim a
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : IsTidyOraclePPTOn input output (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih =>
        exact IsTidyOraclePPTOn.ite
          (ComputableInPolyTime.decide_eq' htag (.const choice)) (hbranch choice) ih
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

end IsTidyOraclePPTOn

end Cslib.Probability
