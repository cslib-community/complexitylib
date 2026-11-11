/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.OTCommitment.Serial
public import Complexity.Crypto.Protocols.MPC.OTCommitment.Program

/-!
# Honest sender and corrupted receiver in the serial world

The existing receiver recursion supplies closed receiver-local callbacks. After it chooses an
index, the honest sender samples a fresh mask and submits one table; only then is the receiver's
selection delivered to the common world. The release decision sees only the commit transcript
and receiver state. Opening is sent by the honest sender at that explicit later boundary.

## Main definitions

* `exchange`: one serial table submission and receiver selection through the common world.
* `receiverCommitAdapter`: the existing receiver recursion with that serial backend.
* `receiverAdapter`: the complete schedule, retaining the actual raw opening read.

## Main results

* `eval_receiverCommitAdapter`: exact joint commit law, including internal sender masks.
* `eval_receiverAdapter`: exact existing receiver experiment with its raw opening retained.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment.Serial

open Probability Crypto.Protocols.Commitment

/-- Submit one private sender row and then consume it through the receiver interface. The
fallback is used only on rejected serial calls; the execution bridge proves it is not used on
this scheduler's supported commit runs. -/
def exchange (values : Fin 4 → Bool) (index : Fin 4) :
    ProbOracleComp (senderSpec ⊕ₒ receiverSpec) ((i : Fin 2) → ot14Spec.Answer () i) := do
  let _ ← Interactive.liftProver
    (ProbOracleComp.query (spec := senderSpec) (.table values, []))
  let value ← Interactive.liftVerifier
    (ProbOracleComp.query (spec := receiverSpec) (.select index))
  return Fin.cases () (fun _ => value.getD false)

/-- The common receiver recursion executes both party calls through the serial world. Neither
receiver callback receives the sender mask or access to a party oracle. The returned masks are
internal joint-execution data, not part of the corrupted receiver observation. -/
noncomputable def receiverCommitAdapter {State : Type}
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (n : ℕ) (st : State) :
    ProbOracleComp (senderSpec ⊕ₒ receiverSpec)
      ((Fin n → Bool) × (Fin n → Fin 4 × Bool) × State) :=
  receiverCommitWith (fun k s => ProbOracleComp.sample (choose k s))
    (fun s answer => ProbOracleComp.sample (receive s answer))
    (ProbOracleComp.sample (ProbComp.uniform Bool)) exchange b n st

/-- Complete fixed-schedule receiver execution. The release plan sees only the commit view;
the sender opens or aborts at that boundary. The continuation receives the actual observed bit,
parsed opening and receiver state. The raw opening read is retained separately in the result. -/
noncomputable def receiverAdapter {State Later Output : Type}
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State)
    (plan : (Fin k → Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : (Fin k → Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (Opening k) → ProbComp Output) :
    ProbOracleComp (senderSpec ⊕ₒ receiverSpec)
      (Phased.Observation × Phased.Observation × (Fin k → Fin 4 × Bool) ×
        State × Later × Option (Bool × List Bool) × Output) := do
  let (masks, transcript, final) ← receiverCommitAdapter choose receive b k st
  let _ ← Interactive.liftProver (ProbOracleComp.query (spec := senderSpec) (.seal, []))
  let (received, _) ← Interactive.liftVerifier (ProbOracleComp.query (spec := receiverSpec) .poll)
  let (release, later) ← ProbOracleComp.sample (plan transcript final)
  let _ ← Interactive.liftProver (ProbOracleComp.query (spec := senderSpec)
    (if release then (.open b, openingWord (opening b masks)) else (.abort, [])))
  let (_, observed) ← Interactive.liftVerifier (ProbOracleComp.query (spec := receiverSpec) .poll)
  let raw ← Interactive.liftVerifier (ProbOracleComp.query (spec := receiverSpec) .readOpening)
  let pairs := (decodeOpening k (({ submission := raw } : Session).opening k)).map Prod.snd
  let out ← ProbOracleComp.sample (finish transcript final later observed pairs)
  return (received, observed, transcript, final, later, raw, out)

private theorem run_exchange (k : ℕ) (s : Store) (values : Fin 4 → Bool) (index : Fin 4)
    (hstop : s.session.stopped = false) (hseal : s.session.sealed = false)
    (hpending : s.pending = none) (hlen : s.session.tables.length < k) :
    ProbOracleComp.runWith (world k).impl (exchange values index) s =
      pure (Fin.cases () (fun _ => values index),
        { s with
          session := { s.session with tables := s.session.tables ++ [values] }
          pending := none
          receipts := s.receipts ++ [(index, values index)] }) := by
  simp only [Nat.reduceAdd, world, handler, OracleComp.sumHandler, Store.send, Session.advance,
    Bool.or_eq_true, ot14World, Fin.isValue, bind_pure_comp, map_pure, ot14Answer, exchange,
    Interactive.liftProver, ProbOracleComp.interpret_query, Interactive.liftVerifier,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, hstop, Bool.false_eq_true,
    ite_false, hseal, hpending, hlen, ite_true, ProbComp.eval_pure, ProbOracleComp.runWith_map,
    PMF.pure_bind, or_self, PMF.pure_map, Prod.map_apply, id_eq, PMF.monad_pure_eq_pure]
  rfl

private def extendStore {n : ℕ} (s : Store) (b : Bool) (masks : Fin n → Bool)
    (transcript : Fin n → Fin 4 × Bool) : Store :=
  { s with
    session := { s.session with
      tables := s.session.tables ++ List.ofFn (fun i => table b (masks i)) }
    pending := none
    receipts := s.receipts ++ List.ofFn transcript }

private theorem run_receiverCommitAdapter {State : Type}
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (n : ℕ) (st : State)
    (k : ℕ) (s : Store) (hstop : s.session.stopped = false)
    (hseal : s.session.sealed = false) (hpending : s.pending = none)
    (hlen : s.session.tables.length + n ≤ k) :
    ProbOracleComp.runWith (world k).impl (receiverCommitAdapter choose receive b n st) s =
      (ProbComp.eval (receiverCommitProgram choose receive b n st)).map
        (fun (masks, transcript, final) =>
          ((masks, transcript, final), extendStore s b masks transcript)) := by
  induction n generalizing st s with
  | zero =>
      simp only [receiverCommitAdapter, receiverCommitProgram, receiverCommitWith,
        ProbOracleComp.runWith_pure, ProbComp.eval_pure, PMF.pure_map, extendStore,
        List.ofFn_zero, List.append_nil]
      rcases s with ⟨⟨tables, sealed, stopped, submission⟩, pending, receipts⟩
      simp_all
  | succ n ih =>
      have hbudget : s.session.tables.length < k := by omega
      simp only [receiverCommitAdapter, receiverCommitWith, receiverCommitProgram,
        ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
        ProbOracleComp.runWith_pure, ProbComp.eval_bind, ProbComp.eval_pure,
        ProbComp.eval_uniform, PMF.bind_map, PMF.map_bind, PMF.pure_map,
        ot14World, PMF.pure_bind, Function.comp_def]
      apply congrArg ((ProbComp.eval (choose n st)).bind)
      funext chosen
      rcases chosen with ⟨index, next⟩
      apply congrArg ((PMF.uniformOfFintype Bool).bind)
      funext mask
      rw [run_exchange k s _ _ hstop hseal hpending hbudget]
      simp only [PMF.monad_pure_eq_pure, PMF.pure_bind]
      change (ProbComp.eval (receive next (table b mask index))).bind _ =
        (ProbComp.eval (receive next (table b mask index))).bind _
      apply congrArg ((ProbComp.eval (receive next (table b mask index))).bind)
      funext after
      let nextStore : Store :=
        { s with
          session := { s.session with tables := s.session.tables ++ [table b mask] }
          pending := none
          receipts := s.receipts ++ [(index, table b mask index)] }
      change (ProbOracleComp.runWith (world k).impl
        (receiverCommitAdapter choose receive b n after) nextStore).bind
          (fun ((masks, transcript, final), last) => pure
            (((Fin.cons mask masks : Fin (n + 1) → Bool),
              (Fin.cons (index, table b mask index) transcript : Fin (n + 1) → Fin 4 × Bool),
              final), last)) =
        (ProbComp.eval (receiverCommitProgram choose receive b n after)).bind
          (fun (masks, transcript, final) => pure
            (((Fin.cons mask masks : Fin (n + 1) → Bool),
              (Fin.cons (index, table b mask index) transcript : Fin (n + 1) → Fin 4 × Bool),
              final),
              extendStore s b ((Fin.cons mask masks : Fin (n + 1) → Bool))
                ((Fin.cons (index, table b mask index) transcript : Fin (n + 1) → Fin 4 × Bool))))
      rw [ih after nextStore hstop hseal rfl (by
        dsimp only [nextStore]
        simp only [List.length_append, List.length_singleton]
        omega)]
      simp [PMF.bind_map, extendStore, nextStore, List.ofFn_succ, List.append_assoc,
        Function.comp_def]

/-- The common serial world preserves the existing joint commit law, including the honest
sender masks used internally for the later opening. Those masks are not receiver observations. -/
theorem eval_receiverCommitAdapter {State : Type}
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State) :
    (world k).eval (receiverCommitAdapter choose receive b k st) =
      ProbComp.eval (receiverCommitProgram choose receive b k st) := by
  rw [Interactive.World.eval, run_receiverCommitAdapter choose receive b k st k {} rfl rfl rfl
    (by simp [Session.initial])]
  rw [PMF.map_comp]
  exact PMF.map_id _

/-- The explicit honest-sender schedule gives the existing receiver experiment, with the raw
opening additionally retained in its output. This is an equality for this schedule, not arbitrary
interleavings of the two party interfaces. -/
theorem eval_receiverAdapter {State Later Output : Type}
    (choose : ℕ → State → ProbComp (Fin 4 × State))
    (receive : State → Bool → ProbComp State) (b : Bool) (k : ℕ) (st : State)
    (plan : (Fin k → Fin 4 × Bool) → State → ProbComp (Bool × Later))
    (finish : (Fin k → Fin 4 × Bool) → State → Later → Phased.Observation →
      Option (Opening k) → ProbComp Output) :
    (world k).eval (receiverAdapter choose receive b k st plan finish) =
      receiverReal (receiverOfPrograms choose receive) b k st
        (fun transcript final => ProbComp.eval (plan transcript final))
        (fun transcript final later observed pairs => do
          let out ← ProbComp.eval (finish transcript final later observed pairs)
          let raw := match observed, pairs with
            | .opened bit, some o => some (bit, openingWord o)
            | _, _ => none
          return (raw, out)) := by
  unfold Interactive.World.eval receiverAdapter
  rw [ProbOracleComp.runWith_bind,
    run_receiverCommitAdapter choose receive b k st k {} rfl rfl rfl
      (by simp [Session.initial]), PMF.bind_map, PMF.map_bind, eval_receiverCommitProgram]
  unfold receiverReal
  apply PMF.bind_congr_on_support
  rintro ⟨masks, transcript, final⟩ h
  have ha : Accepts (fun i => (fin4ToBoolPair (transcript i).1).2)
      (fun i => (transcript i).2) b (opening b masks) := by
    rw [opening_eq_equivocate_of_mem_support _ _ _ _ h]
    exact equivocate_accepts b transcript
  have hc : openPairs (List.ofFn fun i => (fin4ToBoolPair (transcript i).1).2)
      (List.ofFn fun i => (transcript i).2)
      (({ submission := some (b, openingWord (opening b masks)) } : Session).opening k) =
      some b := by
    rw [openPairs_decodeOpening, decodeOpening_openingWord]
    simp [openResult, ha]
  simp only [Function.comp_def, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_pure,
    Interactive.liftProver, Interactive.liftVerifier, ProbOracleComp.interpret_query,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_sample,
    world, handler, OracleComp.sumHandler, ProbComp.eval_pure,
    PMF.pure_bind, PMF.map_bind, PMF.pure_map, PMF.bind_map]
  simp only [extendStore, Session.initial, List.nil_append, Store.send, Session.advance,
    Bool.false_eq_true, ite_false, ite_true, List.length_ofFn,
    Store.observations, Session.receipt, Session.observation]
  apply congrArg ((ProbComp.eval (plan transcript final)).bind)
  funext planned
  rcases planned with ⟨release, later⟩
  have hc' : openPairs ((List.ofFn transcript).map fun r => (fin4ToBoolPair r.1).2)
      ((List.ofFn transcript).map Prod.snd)
      (({ submission := some (b, openingWord (opening b masks)) } : Session).opening k) =
      some b := by
    simpa only [List.map_ofFn, Function.comp_def] using hc
  cases release with
  | false => simp [Store.readOpening, Session.opening, openPairs, decodeOpening]
  | true =>
      simp only [ite_true, Store.readOpening, Bool.true_and,
        decodeOpening_openingWord, Option.map_some]
      erw [hc']
      simp

end Cslib.Crypto.Protocols.MPC.OTCommitment.Serial
