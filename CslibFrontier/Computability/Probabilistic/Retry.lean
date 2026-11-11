/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Languages.Probabilistic.Iteration
public import CslibFrontier.Languages.Probabilistic.Retry
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Probabilistic.Adaptive
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Strict PPT bounded retries

`Cslib.OracleComp.retry good program fuel` runs `program` at most `fuel` times and returns the first
result satisfying `good`. It is strict probabilistic polynomial time when `program` is, `good` is
decided in polynomial time and `fuel` is computed in unary: the loop is a bounded iteration whose
state is the optional result found so far (`Cslib.Probability.IsPPTOn.iterateWith_spec'`), and
every reachable state is `none` or a possible result of one run.

## Main definitions

* `Cslib.OracleComp.retryStep`: one run of the loop on the optional result found so far.

## Main results

* `Cslib.OracleComp.retry_eq_iterate`: the loop is `fuel` iterations of `retryStep` from `none`.
* `Cslib.Probability.IsPPTOn.retry`: bounded retries of a strict PPT program are strict PPT.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u

variable {ι : Type u} {spec : OracleSpec.{u, 0} ι} {α : Type}

/-- One run of the retry loop: keep a result already found, otherwise run `program` and keep its
result when it is good. -/
def retryStep (good : α → Bool) (program : OracleComp spec α) (o : Option α) :
    OracleComp spec (Option α) :=
  if o.isSome then pure o else (fun a => if good a then some a else none) <$> program

theorem retryStep_some (good : α → Bool) (program : OracleComp spec α) (a : α) :
    retryStep good program (some a) = pure (some a) := rfl

theorem iterate_retryStep_some (good : α → Bool) (program : OracleComp spec α) (n : ℕ) (a : α) :
    iterate n (retryStep good program) (some a) = pure (some a) :=
  iterate_eq_pure n _ _ (retryStep_some good program a)

/-- **The retry loop as an iteration**: `fuel` runs of `retryStep` from `none`. -/
theorem retry_eq_iterate (good : α → Bool) (program : OracleComp spec α) (fuel : ℕ) :
    retry (fun a => good a) program fuel = iterate fuel (retryStep good program) none := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hnone : retryStep good program none =
        (fun a => if good a then some a else none) <$> program := rfl
    rw [retry_succ, iterate_succ_bind, hnone, bind_map_left]
    refine congrArg (program >>= ·) (funext fun a => ?_)
    by_cases ha : good a
    · simp only [ha, ↓reduceIte, iterate_retryStep_some]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, ih]

end Cslib.OracleComp

namespace Cslib.Probability

open Turing.MultiTapeTM

variable {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}

/-- **Bounded retries are strict PPT.** If `program` is strict PPT, `good` is decided in
polynomial time and the fuel is computed in unary, then running `program` at most `fuel a` times
and returning the first good result is strict PPT, with the optional result encoded by
`encOption`. -/
@[program_certificate]
theorem IsPPTOn.retry {program : α → ProbComp β} {good : β → Bool} {fuel : α → ℕ}
    (hprogram : IsPPTOn input output program) (hgood : ComputableInPolyTime good output encBool)
    (hfuel : ComputableInPolyTime fuel input encUnary) :
    IsPPTOn input (encOption output)
      (fun a => OracleComp.retry (fun b => good b) (program a) (fuel a)) := by
  obtain ⟨c, d, hlen⟩ := hprogram.length_le
  have hinitial : ComputableInPolyTime (fun _ : α => (none : Option β)) input
      (encOption output) := ComputableInPolyTime.const none
  have hkeep : ComputableInPolyTime (fun b : β => if good b then some b else none) output
      (encOption output) := by
    fun_prop
  have hcond : ComputableInPolyTime (fun pair : α × Option β => pair.2.isSome)
      (encPair input (encOption output)) encBool := by
    fun_prop
  have hyes : IsPPTOn (encPair input (encOption output)) (encOption output)
      (fun pair : α × Option β => pure pair.2) :=
    (ComputableInPolyTime.snd input (encOption output)).isPPTOn
  have hno : IsPPTOn (encPair input (encOption output)) (encOption output)
      (fun pair : α × Option β => (fun b => if good b then some b else none) <$>
        program pair.1) :=
    (hprogram.preprocess (ComputableInPolyTime.fst input (encOption output))).map hkeep
  have hstep : IsPPTOn (encPair input (encOption output)) (encOption output)
      (fun pair : α × Option β => OracleComp.retryStep good (program pair.1) pair.2) :=
    IsPPTOn.cond' hcond hyes hno
  have hloop := IsPPTOn.iterateWith_spec' (input := input) (stateEncoding := encOption output)
    (step := fun a => OracleComp.retryStep good (program a)) hfuel hinitial hstep
    (fun a _ o => ∀ b, o = some b → b ∈ (ProbComp.eval (program a)).support)
    (fun a b hb => nomatch hb)
    (fun a i o _ ho o' ho' => by
      cases o with
      | some b =>
        rw [OracleComp.retryStep_some, ProbComp.eval_pure, PMF.support_pure,
          Set.mem_singleton_iff] at ho'
        subst ho'
        exact ho
      | none =>
        intro b' hb'
        subst hb'
        simp only [OracleComp.retryStep, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          ProbComp.eval_map, PMF.support_map, Set.mem_image] at ho'
        obtain ⟨b, hb, hbb⟩ := ho'
        by_cases hg : good b
        · simp only [hg, ↓reduceIte, Option.some.injEq] at hbb
          exact hbb ▸ hb
        · simp [hg] at hbb)
    (size := fun a => c * ((input a).length + 1) ^ d + 1)
    (PolyBounded.of_forall_le (c + 1) d fun a => by
      have : 1 ≤ ((input a).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      rw [add_mul, one_mul]
      omega)
    (fun a i o _ ho => by
      cases o with
      | none => simp [encOption_none]
      | some b =>
        rw [encOption_some, List.length_cons]
        exact Nat.succ_le_succ (hlen a b (ho b rfl)))
  exact hloop.1.congr fun a => by rw [OracleComp.retry_eq_iterate]

end Cslib.Probability
