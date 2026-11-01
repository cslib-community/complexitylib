/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle.Tidy
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IterateWhile
public import Complexity.Languages.Probabilistic.Iteration
public import Complexity.Languages.Probabilistic.Oracle.Support
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Bounded adaptive loops of clean oracle phases

A loop of clean phases is a clean phase when one invariant bounds the encoded size of every
reachable state. Unlike closed loops, an adaptive loop with an external oracle cannot presample
its randomness: every iteration may query the shared stateful oracle, and its replies may be
arbitrarily long. The loop therefore runs the step machine itself, once per iteration, with a
unary counter stored beside the state; the counter stops the loop after exactly the requested
number of steps and the final round executes no step.

The invariant quantifies over every result possible for some stateful handler, so it holds for
every shared oracle. Storage growth is controlled by the client's size bound, not assumed.

## Main results

* `Cslib.Probability.IsTidyOraclePPTOn.iterate_spec`: certify a bounded loop and its final
  supported invariant.
* `Cslib.Probability.IsTidyOraclePPTOn.iterateWith_spec`: the step may capture the input.

## References

Adapts Computability/Probabilistic/Adaptive.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8` to open oracles, running the probabilistic oracle
version of the tidy `iterateWhile` loop instead of presampled coins.
-/

@[expose] public section

namespace Cslib.Probability

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM

variable {Operation α σ : Type} [DecidableEq Operation] {input : α ↪ List Bool}
  {stateEncoding : σ ↪ List Bool}

namespace IsTidyOraclePPTOn

omit [DecidableEq Operation] in
/-- Counting down a stored counter commutes the word loop with the state loop. -/
private theorem iterate_countdown {β : Type} (encode : ℕ × σ → β)
    (step : σ → WordOracleComp Operation σ) (wordStep : β → WordOracleComp Operation β)
    (hstep : ∀ c state, wordStep (encode (c + 1, state)) =
      (fun next => encode (c, next)) <$> step state) (c count : ℕ) (state : σ) :
    OracleComp.iterate count wordStep (encode (c + count, state)) =
      (fun final => encode (c, final)) <$> OracleComp.iterate count step state := by
  induction count generalizing state with
  | zero => simp
  | succ count ih =>
    rw [OracleComp.iterate_succ_bind, OracleComp.iterate_succ_bind, ← Nat.add_assoc, hstep,
      bind_map_left, map_bind]
    simp only [ih]

/-- A bounded loop of a clean step is clean when one invariant bounds every reachable state.
The invariant holds for every possible result under every stateful oracle, and it is also
established for the final state. -/
theorem iterate_spec {initial : α → σ} {count : α → ℕ}
    {step : σ → WordOracleComp Operation σ}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsTidyOraclePPTOn stateEncoding stateEncoding step)
    (invariant : α → ℕ → σ → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ OracleComp.support (step state), invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    IsTidyOraclePPTOn input stateEncoding
        (fun a => OracleComp.iterate (count a) step (initial a)) ∧
      ∀ a, ∀ state ∈ OracleComp.support (OracleComp.iterate (count a) step (initial a)),
        invariant a (count a) state := by
  classical
  refine ⟨?_, fun a => OracleComp.iterate_invariant (invariant a) (hbase a)
    (fun i state hi hstate => hpreserve a i state hi hstate)⟩
  have hops := hstep.1
  let encode : ℕ × σ ↪ List Bool := encPair encUnary stateEncoding
  let body (pair : ℕ × σ) : WordOracleComp Operation (List Bool) :=
    if pair.1 = 0 then pure [] else (fun next => encode (pair.1 - 1, next)) <$> step pair.2
  have hbody : IsTidyOraclePPTOn encode encBits body := by
    apply ite (ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.fst encUnary stateEncoding) (.const 0))
    · exact of_computableInPolyTime (.const [])
    · apply (hstep.preprocess (ComputableInPolyTime.snd encUnary stateEncoding)).map_with
      exact (ComputableInPolyTime.of_eq (encIn := encode) (encOut := encBits) (f := encode)
        fun _ => rfl).comp
        ((ComputableInPolyTime.unary_sub.comp
          (((ComputableInPolyTime.fst encUnary stateEncoding).comp
            (ComputableInPolyTime.fst encode stateEncoding)).prod (.const 1))).prod
          (ComputableInPolyTime.snd encode stateEncoding))
  obtain ⟨_, kB, Body, hfiniteB, machine, cB, dB, hmachine⟩ := hbody
  let wordStep : List Bool → WordOracleComp Operation (List Bool) :=
    Function.extend encode body (fun _ => pure [])
  have hwordStep (pair : ℕ × σ) : wordStep (encode pair) = body pair :=
    encode.injective.extend_apply _ _ pair
  have hencode (pair : ℕ × σ) :
      (encode pair).length = 2 * pair.1 + 1 + (stateEncoding pair.2).length := by
    simp only [encode, length_encPair, encUnary_apply, List.length_replicate]
  have hloop (c count : ℕ) (state : σ) :
      OracleComp.iterate count wordStep (encode (c + count, state)) =
        (fun final => encode (c, final)) <$> OracleComp.iterate count step state :=
    iterate_countdown encode step wordStep (fun c state => by
      rw [hwordStep]
      simp only [body, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]) c count state
  obtain ⟨_, kp, Prepare, hfiniteP, prepare, cp, dp, hprepare⟩ :=
    of_computableInPolyTime (Operation := Operation)
      ((ComputableInPolyTime.of_eq (encIn := encode) (encOut := encBits) (f := encode)
        fun _ => rfl).comp (hcount.prod hinitial))
  let tp (a : α) : ℕ := cp * ((input a).length + 1) ^ dp
  have htp : PolyBounded (fun a => (input a).length) tp := .of_forall_le cp dp fun _ => le_rfl
  have hcountPoly := Turing.MultiTapeTM.ComputableInPolyTime.polyBounded hcount
  let bound (a : α) : ℕ := 2 * count a + 1 + size a
  let roundTime (a : α) : ℕ := cB * (bound a + 1) ^ dB
  let loopTime (a : α) : ℕ := (count a + 1) * (roundTime a + 10 * bound a + 23) + 8 * bound a + 17
  have hboundPoly : PolyBounded (fun a => (input a).length) bound :=
    ((PolyBounded.const 2).mul hcountPoly |>.add (.const 1)).add hsize
  have hroundPoly : PolyBounded (fun a => (input a).length) roundTime :=
    PolyBounded.comp (size' := id) (v := fun n => cB * (n + 1) ^ dB)
      (.of_forall_le cB dB fun _ => le_rfl) hboundPoly
  have hloopPoly : PolyBounded (fun a => (input a).length) loopTime :=
    (((hcountPoly.add (.const 1)).mul
      ((hroundPoly.add ((PolyBounded.const 10).mul hboundPoly)).add (.const 23))).add
        ((PolyBounded.const 8).mul hboundPoly)).add (.const 17)
  have hfinal : IsTidyOraclePPTOn input encode
      (fun a => (fun final => (0, final)) <$> OracleComp.iterate (count a) step (initial a)) := by
    refine of_polyBounded ((machine.iterateWhile true).tidyComp prepare true)
      (((PolyBounded.const 5).mul htp).add hloopPoly |>.add (.const 9)) fun a => ?_
    let start := encode (count a, initial a)
    have hrun : (machine.iterateWhile true).ComputesTidily start (loopTime a)
        (OracleComp.iterate (count a) wordStep start) := by
      refine ComputesTidily.iterateWhile true
        (fun n word => ∃ state, word = encode (count a - n, state) ∧ invariant a n state)
        ⟨initial a, by simp [start], hbase a⟩ ?_ ?_ ?_ ?_
      · rintro n hn word ⟨state, rfl, hstate⟩
        rw [hwordStep]
        have hlength := hencode (count a - n, state)
        have hsize := hbound a n state hn.le hstate
        refine ((hmachine (count a - n, state)).mono ?_).congr fun State oracle s => ?_
        · exact Nat.mul_le_mul_left cB (Nat.pow_le_pow_left (by dsimp only [bound]; lia) dB)
        · simp only [encBits, Function.Embedding.coe_refl, id_map]
      · rintro n hn word ⟨state, rfl, hstate⟩ State oracle s s' next hnext
        rw [hwordStep] at hnext
        have hpositive : count a - n ≠ 0 := by lia
        simp only [body, hpositive, ↓reduceIte] at hnext
        have hnext' := ProbOracleComp.mem_support_of_mem oracle hnext
        obtain ⟨final, hfinal, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext'
        refine ⟨⟨final, by rw [Nat.sub_sub], hpreserve a n state hn hstate final hfinal⟩, ?_⟩
        simp [encode, encPair_apply, frame]
      · rintro word ⟨state, rfl, hstate⟩
        have hlength := hencode (count a - count a, state)
        have hsize := hbound a (count a) state le_rfl hstate
        refine ((hmachine (count a - count a, state)).mono ?_).congr fun State oracle s => ?_
        · exact Nat.mul_le_mul_left cB (Nat.pow_le_pow_left (by dsimp only [bound]; lia) dB)
        · simp only [body, Nat.sub_self, ↓reduceIte, encBits, Function.Embedding.coe_refl,
            id_map]
      · rintro n hn word ⟨state, rfl, hstate⟩
        rw [hencode]
        have := hbound a n state hn hstate
        dsimp only [bound]
        lia
    have hprepare' : prepare.ComputesTidily (input a) (tp a) (pure start) := by
      simpa only [encBits, Function.Embedding.coe_refl, id_eq, map_pure, Function.comp_apply]
        using hprepare a
    have hcomp := hprepare'.comp true
      (prog₂ := fun _ => OracleComp.iterate (count a) wordStep start)
      (t₂ := loopTime a) (fun word State oracle s s' hword => by
        simp only [OracleComp.interpret_pure, StateT.run_pure, Probability.PMF.monad_pure_eq_pure,
          PMF.mem_support_pure_iff] at hword
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hword
        exact hrun)
    have hstart : start = encode (0 + count a, initial a) := by simp [start]
    rw [pure_bind, hstart, hloop] at hcomp
    simpa only [Functor.map_map] using hcomp
  simpa only [Functor.map_map, id_map'] using
    hfinal.map (ComputableInPolyTime.snd encUnary stateEncoding)

/-- The loop body may capture the original input. The joint step certificate charges for both
that input and the changing state; the client invariant describes only the changing state. -/
theorem iterateWith_spec {initial : α → σ} {count : α → ℕ}
    {step : α → σ → WordOracleComp Operation σ}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsTidyOraclePPTOn (encPair input stateEncoding) stateEncoding
      (fun pair => step pair.1 pair.2))
    (invariant : α → ℕ → σ → Prop) (hbase : ∀ a, invariant a 0 (initial a))
    (hpreserve : ∀ a i state, i < count a → invariant a i state →
      ∀ next ∈ OracleComp.support (step a state), invariant a (i + 1) next)
    {size : α → ℕ} (hsize : PolyBounded (fun a => (input a).length) size)
    (hbound : ∀ a i state, i ≤ count a → invariant a i state →
      (stateEncoding state).length ≤ size a) :
    IsTidyOraclePPTOn input stateEncoding
        (fun a => OracleComp.iterate (count a) (step a) (initial a)) ∧
      ∀ a, ∀ state ∈ OracleComp.support (OracleComp.iterate (count a) (step a) (initial a)),
        invariant a (count a) state := by
  refine ⟨?_, fun a => OracleComp.iterate_invariant (invariant a) (hbase a)
    (fun i state hi hstate => hpreserve a i state hi hstate)⟩
  let packedStep (pair : α × σ) : WordOracleComp Operation (α × σ) :=
    (fun next => (pair.1, next)) <$> step pair.1 pair.2
  have hpacked := (iterate_spec (step := packedStep) hcount
    (ComputableInPolyTime.id'.prod hinitial)
    (hstep.pair (ComputableInPolyTime.fst input stateEncoding))
    (fun a i pair => pair.1 = a ∧ invariant a i pair.2) (fun a => ⟨rfl, hbase a⟩)
    (by
      rintro a i ⟨captured, state⟩ hi ⟨rfl, hstate⟩ next hnext
      obtain ⟨value, hvalue, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      exact ⟨rfl, hpreserve captured i state hi hstate value hvalue⟩)
    (size := fun a => 2 * (input a).length + size a + 1)
    ((((PolyBounded.const 2).mul .self).add hsize).add (.const 1))
    (by
      rintro a i ⟨captured, state⟩ hi ⟨rfl, hstate⟩
      simp only [length_encPair]
      have := hbound captured i state hi hstate
      lia)).1
  refine (hpacked.map (ComputableInPolyTime.snd input stateEncoding)).congr ?_
  intro a State oracle s
  rw [OracleComp.iterate_map (count a) (step a) packedStep (fun state => (a, state))
    (fun _ => rfl) (initial a)]
  simp only [Functor.map_map, id_map']

/-- Captured-input steps may grow by a polynomially bounded amount depending on that input,
for every possible next state under every stateful oracle. -/
theorem iterateWith_of_bounded_growth {initial : α → σ} {count : α → ℕ}
    {step : α → σ → WordOracleComp Operation σ}
    (hcount : ComputableInPolyTime count input encUnary)
    (hinitial : ComputableInPolyTime initial input stateEncoding)
    (hstep : IsTidyOraclePPTOn (encPair input stateEncoding) stateEncoding
      (fun pair => step pair.1 pair.2))
    {growth : α → ℕ} (hpoly : PolyBounded (fun a => (input a).length) growth)
    (hgrowth : ∀ a state, ∀ next ∈ OracleComp.support (step a state),
      (stateEncoding next).length ≤ (stateEncoding state).length + growth a) :
    IsTidyOraclePPTOn input stateEncoding
      (fun a => OracleComp.iterate (count a) (step a) (initial a)) := by
  refine (iterateWith_spec hcount hinitial hstep
    (fun a i state => (stateEncoding state).length ≤
      (stateEncoding (initial a)).length + i * growth a)
    (by simp) ?_ (hinitial.polyBounded_length.add
      ((Turing.MultiTapeTM.ComputableInPolyTime.polyBounded hcount).mul hpoly)) ?_).1
  · intro a i state _ hstate next hnext
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
      (hgrowth a state next hnext).trans (Nat.add_le_add_right hstate _)
  · intro a i state hi hstate
    exact hstate.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _)

end IsTidyOraclePPTOn

end Cslib.Probability
