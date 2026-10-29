/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.Simulation
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# From Mathlib TM2 computations to CSLib polynomial time

Mathlib counts one fixed stack-machine statement per transition. The simulation certifies each
statement using CSLib's list and finite-table calculus, then iterates it for the source polynomial
clock. Encoded configurations have linear growth in source time. The resulting certificate is for
an actual tidy binary multi-tape Turing machine, with polynomial time and space.

Input and output words use `encList (encFinite _)`. Their alphabets may differ or be empty.
Typed encoders must be injective, as required by CSLib. Every working alphabet must be finite;
Mathlib's `FinTM2` alone only guarantees finiteness of the input alphabet.

## Main results

* `Turing.TM2ComputableInPolyTime.computableInPolyTime_encList`: transfer a typed Mathlib
  polynomial-time certificate to CSLib.

This is the forward bridge. `TM2.Reverse.Transfer` supplies a direct reverse compiler and
polynomial-time equivalence, including explicit conversions for these word encodings.

## References

The source model and runtime convention are Mathlib's
`Mathlib.Computability.TuringMachine.Computable` and
`Mathlib.Computability.TuringMachine.StackTuringMachine`. This is a direct proof,
independent of the TM2-to-TM0 compiler in
[Complexitylib PR #72](https://github.com/SamuelSchlesinger/complexitylib/pull/72).
-/

@[expose] public section

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin
  Turing.FinTM2.Γk₀Fin

namespace Turing.TM2

open MultiTapeTM ComputableInPolyTime

/-- A source clock may continue after halting without changing the result. -/
theorem stepTotal_of_step {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) (cfg : Cfg Γ Λ σ) :
    stepTotal M cfg = (step M cfg).getD cfg := by
  cases cfg with | mk label v store => cases label <;> rfl

private theorem iterate_bind_none {α : Type} (f : α → Option α) (n : ℕ) :
    (fun value : Option α => value.bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', ih, Option.bind_none]

private theorem iterate_getD_of_bind {α : Type} (f : α → Option α) (n : ℕ) (a b : α)
    (h : (fun value : Option α => value.bind f)^[n] (some a) = some b) :
    (fun value => (f value).getD value)^[n] a = b := by
  induction n generalizing a with
  | zero => exact Option.some.inj h
  | succ n ih =>
    rw [Function.iterate_succ_apply, Option.bind_some] at h
    rw [Function.iterate_succ_apply]
    cases hf : f a with
    | none => rw [hf, iterate_bind_none] at h; contradiction
    | some c => simpa only [hf, Option.getD_some] using ih c (by simpa only [hf] using h)

/-- Bounded partial execution to a halted configuration agrees with the padded total clock. -/
theorem iterate_stepTotal_of_evals (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (time : ℕ)
    (h : TM2OutputsInTime tm input (some output) time) :
    (stepTotal tm.m)^[time] (initList tm input) = haltList tm output := by
  change StateTransition.EvalsToInTime tm.step (initList tm input)
    (some (haltList tm output)) time at h
  have hexact : (stepTotal tm.m)^[h.steps] (initList tm input) = haltList tm output := by
    rw [show stepTotal tm.m = (fun cfg => (tm.step cfg).getD cfg) from
      funext (stepTotal_of_step tm.m)]
    exact iterate_getD_of_bind tm.step h.steps _ _ h.evals_in_steps
  have hhalt : stepTotal tm.m (haltList tm output) = haltList tm output := rfl
  rw [← Nat.sub_add_cancel h.steps_le_m]
  exact (Function.iterate_add_apply (stepTotal tm.m) _ _ _).trans
    ((congrArg ((stepTotal tm.m)^[time - h.steps]) hexact).trans
      (Function.iterate_fixed hhalt _))

/-- Initialization copies the source input and supplies empty auxiliary stacks. -/
theorem initList_polyTime (tm : FinTM2) [∀ k, Finite (tm.Γ k)] :
    ComputableInPolyTime (initList tm) (encList (encFinite (tm.Γ tm.k₀))) encCfg := by
  apply cfg_mk (const (some tm.main)) (const tm.initialState)
  apply dpi
  intro k
  by_cases hk : k = tm.k₀
  · subst k
    simpa [initList] using
      (id' : ComputableInPolyTime id
        (encList (encFinite (tm.Γ tm.k₀))) (encList (encFinite (tm.Γ tm.k₀))))
  · simpa [initList, hk] using
      (const (encIn := encList (encFinite (tm.Γ tm.k₀)))
        (encOut := encList (encFinite (tm.Γ k))) [])

/-- Polynomially many source steps have polynomially bounded encoded intermediate states. -/
theorem run_polyTime (tm : FinTM2) [∀ k, Finite (tm.Γ k)] (p : Polynomial ℕ) :
    ComputableInPolyTime
      (fun input => (stepTotal tm.m)^[p.eval input.length] (initList tm input))
      (encList (encFinite (tm.Γ tm.k₀))) encCfg := by
  have hlength := length_list (encFinite (tm.Γ tm.k₀))
  have hcount := (unary_eval p).comp hlength
  obtain ⟨C, hC⟩ := stepTotal_stack_bound tm.m
  obtain ⟨A, hA⟩ := length_encCfg_le (Γ := tm.Γ) (Λ := tm.Λ) (σ := tm.σ)
  apply iterate hcount (initList_polyTime tm) (stepTotal_polyTime tm.m)
    ((PolyBounded.const A).mul
      ((hlength.polyBounded.add ((PolyBounded.const C).mul hcount.polyBounded)).add
        (PolyBounded.const 1)))
  intro input i hi
  apply hA
  have hstacks : ∀ i k,
      (((stepTotal tm.m)^[i] (initList tm input)).stk k).length ≤ input.length + C * i := by
    intro i
    induction i with
    | zero =>
      intro k
      by_cases hk : k = tm.k₀
      · subst k; simp [initList]
      · simp [initList, hk]
    | succ i ih =>
      intro k
      calc
        _ = ((stepTotal tm.m ((stepTotal tm.m)^[i] (initList tm input))).stk k).length :=
          congrArg (fun cfg : Cfg tm.Γ tm.Λ tm.σ => (cfg.stk k).length)
            (Function.iterate_succ_apply' (stepTotal tm.m) i (initList tm input))
        _ ≤ input.length + C * i + C := hC _ (input.length + C * i) ih k
        _ = input.length + C * (i + 1) := by ring
  intro k
  exact (hstacks i k).trans (Nat.add_le_add_left (Nat.mul_le_mul_left C hi) _)

end Turing.TM2

namespace Turing.TM2ComputableInPolyTime

open MultiTapeTM MultiTapeTM.ComputableInPolyTime

/-- A finite-alphabet Mathlib certificate gives CSLib polynomial-time computation under
the standard binary encodings of its input and output words. -/
theorem computableInPolyTime_encList {α β αΓ βΓ : Type} [Finite αΓ]
    {encA : αΓ ↪ List Bool} {encB : βΓ ↪ List Bool}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) [∀ k, Finite (h.tm.Γ k)]
    (ha : Function.Injective ea) (hb : Function.Injective eb) :
    ComputableInPolyTime f
      ((⟨ea, ha⟩ : α ↪ List αΓ).trans (encList encA))
      ((⟨eb, hb⟩ : β ↪ List βΓ).trans (encList encB)) := by
  have hinput : ComputableInPolyTime ea
      ((⟨ea, ha⟩ : α ↪ List αΓ).trans (encList encA))
      (encList encA) := of_eq fun _ => rfl
  have hmap := (map (of_finite h.inputAlphabet.symm
    (encOut := encFinite (h.tm.Γ h.tm.k₀)))).comp hinput
  have hrun := (TM2.run_polyTime h.tm h.time).comp hmap
  have hstacks := TM2.cfg_stacks.comp hrun
  have hout := (dpi_apply (fun k => encList (encFinite (h.tm.Γ k))) h.tm.k₁).comp hstacks
  have hword := (map (of_finite h.outputAlphabet (encOut := encB))).comp hout
  apply hword.of_enc_eq
  intro a
  have heval := TM2.iterate_stepTotal_of_evals h.tm _ _ _ (h.outputsFun a)
  have houtput := congrArg (fun cfg : TM2.Cfg h.tm.Γ h.tm.Λ h.tm.σ =>
    List.map h.outputAlphabet (cfg.stk h.tm.k₁)) heval
  have hresult : List.map h.outputAlphabet
      (((TM2.stepTotal h.tm.m)^[h.time.eval (ea a).length]
        (initList h.tm (List.map h.inputAlphabet.symm (ea a)))).stk h.tm.k₁) = eb (f a) := by
    simpa [haltList] using houtput
  dsimp only [Function.comp_def, Function.Embedding.trans_apply]
  simp only [List.length_map]
  exact congrArg (encList encB) hresult.symm

end Turing.TM2ComputableInPolyTime
