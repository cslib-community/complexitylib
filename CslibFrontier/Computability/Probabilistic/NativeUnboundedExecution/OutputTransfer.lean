/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution
import CslibFrontier.Probability.PMF.Bind

/-!
# Native selection provenance under derived output/memory laws

## Main results

* `selectionOnly_of_output_memory_bind`, `selectionOnly_of_output_memory`: transfer
  successful-output provenance between
  actual native programs once their full output/oracle-memory laws are proved.

The lemma does not construct a machine representation. Compiler applications must
derive its law premise from actual execution, as the residual cost selector does.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeUnboundedExecution
open Turing NativeOpenExecution
variable {Operation Private Control Control' J : Type} {k k' : ℕ}
variable {input input' : List Bool} [DecidableEq Operation] [DecidableEq J]

/-- Successful selection provenance depends only on terminal output bytes and
full oracle memory. Divergent mass is preserved by the law equality as well. -/
theorem selectionOnly_of_output_memory_bind {I : Type}
    (machine : MultiTapePTM k Bool Control Operation) (env : Environment Operation Private)
    (μ : PMF I) (other : MultiTapePTM k' Bool Control' Operation)
    (env' : I → Environment Operation Private)
    (parse : Operation → List Bool → List Bool → Finset J)
    (decode : List Bool → Option (Finset J)) (accept : Finset J → Bool)
    (world : World k Control Operation Private input)
    (start : I → World k' Control' Operation Private input')
    (hlaw : (terminal machine env world).map
      (Option.map fun w => (w.config.tapes.output, w.memory)) =
      μ.bind fun i => (terminal other (env' i) (start i)).map
        (Option.map fun w => (w.config.tapes.output, w.memory)))
    (hadmit : ∀ i ∈ μ.support, SelectionOnly other (env' i) parse decode accept (start i)) :
    SelectionOnly machine env parse decode accept world := by
  intro fuel next hn C hc ha
  have hh : halted next := by
    unfold NativeOpenSelection.result at hc
    split_ifs at hc with h
    exact Option.isNone_iff_eq_none.mp h
  have ht := (terminal_support machine env world next).mpr ⟨hh, fuel, hn⟩
  have hm : some (next.config.tapes.output, next.memory) ∈
      ((terminal machine env world).map
        (Option.map fun w => (w.config.tapes.output, w.memory))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨some next, ht, rfl⟩
  rw [hlaw] at hm
  obtain ⟨i, hi, hm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hm
  obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  cases result with
  | none => cases he
  | some before =>
    obtain ⟨ho, hm⟩ := Prod.mk.inj (Option.some.inj he)
    obtain ⟨hb, t, ht⟩ := (terminal_support other (env' i) (start i) before).mp hr
    have hc' : NativeOpenSelection.result decode before = some C := by
      have hh' : next.config.tapes.state = none := hh
      have hb' : before.config.tapes.state = none := hb
      simpa only [NativeOpenSelection.result, hh', hb', Option.isNone_none, ite_true, ho] using hc
    have hp := hadmit i hi t before ht C hc' ha
    simpa only [hm] using hp

/-- Successful selection provenance depends only on terminal output bytes and
full oracle memory. Divergent mass is preserved by the law equality as well. -/
theorem selectionOnly_of_output_memory
    (machine : MultiTapePTM k Bool Control Operation) (env : Environment Operation Private)
    (other : MultiTapePTM k' Bool Control' Operation) (env' : Environment Operation Private)
    (parse : Operation → List Bool → List Bool → Finset J)
    (decode : List Bool → Option (Finset J)) (accept : Finset J → Bool)
    (world : World k Control Operation Private input)
    (start : World k' Control' Operation Private input')
    (hlaw : (terminal machine env world).map
      (Option.map fun w => (w.config.tapes.output, w.memory)) =
      (terminal other env' start).map (Option.map fun w => (w.config.tapes.output, w.memory)))
    (hadmit : SelectionOnly other env' parse decode accept start) :
    SelectionOnly machine env parse decode accept world := by
  apply selectionOnly_of_output_memory_bind machine env (PMF.pure ()) other (fun _ => env')
    parse decode accept world (fun _ => start)
  · simpa only [PMF.pure_bind] using hlaw
  · intro _ _
    exact hadmit

end Cslib.Probability.NativeUnboundedExecution
