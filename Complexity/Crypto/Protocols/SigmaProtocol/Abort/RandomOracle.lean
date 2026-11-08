/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SigmaProtocol.FiatShamir
public import Complexity.Crypto.Protocols.SigmaProtocol.Abort.FiatShamir
public import Complexity.Crypto.Protocols.SigmaProtocol.Abort.View
public import Complexity.Probability.IID
import Complexity.Languages.Probabilistic.Norm

/-!
# Bounded aborting Fiat–Shamir signing in the shared random oracle

The signer executes every attempt, including attempts after the first success. Consequently
all attempted hash inputs affect the shared cache. Only the returned signature selects the
first success. `fiatShamirAbortSign` executes the one-attempt commitment-hash-response step
directly without requiring a key generator, while `fiatShamirAbort` packages it with `keyGen`
as a `ROMSignature.Scheme`.

## Main definitions

* `fiatShamirAbortSign`: all-attempt oracle program.
* `fiatShamirAbort`: canonical optional-signature scheme with a fixed attempt budget.

## Main results

* `fiatShamirAbortSign_queryBound`: the program makes at most the attempt budget of hash calls.
* `fiatShamirAbort_sign_fixedHash`: fixed-hash output law equals the existing bounded signer.
* `fiatShamir_sign_run_eq_of_transcript_eq`: one-attempt stateful witness invariance.
* `fiatShamirAbortSign_run_eq_of_transcript_eq`: sequential stateful witness invariance.
* `fiatShamirAbort_world_eq_of_transcript_eq`: equality of the canonical shared-cache worlds.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF OracleComp ROMSignature

variable {X Y T C Z M : Type}

/-- Execute all attempts and return the first success. Even when the first attempt succeeds,
the recursive call runs and retains its oracle effects. -/
noncomputable def fiatShamirAbortSign (P : SigmaProtocol X Y T C (Option Z))
    (sk : X × Y) (msg : M) :
    (K : ℕ) → (Fin K → T × P.State) → OracleComp (fun _ : M × T => C) (Option (T × Z))
  | 0, _ => pure none
  | K + 1, coins => do
      let view ← (fun c => ((coins 0).1, P.respond sk.1 sk.2 (coins 0).2 c)) <$>
        OracleComp.query (spec := fun _ : M × T => C) (msg, (coins 0).1)
      let later ← fiatShamirAbortSign P sk msg K (Fin.tail coins)
      return (view.2.map fun z => (view.1, z)).orElse fun _ => later

/-- An aborting Fiat–Shamir scheme with exactly `K` attempted hash calls per signing request.
The `none` reply is an abort and never verifies. No total correctness assertion is made. -/
noncomputable def fiatShamirAbort (P : SigmaProtocol X Y T C (Option Z))
    (keyGen : PMF (X × Y)) (K : ℕ) : Scheme Y (X × Y) M (Option (T × Z)) (M × T) C where
  keyGen := (fiatShamir (Function.Embedding.refl (M × T)) P keyGen).keyGen
  SignCoins := Fin K → T × P.State
  signCoins sk _ := iid (P.commit sk.1 sk.2) K
  sign sk msg coins := fiatShamirAbortSign P sk msg K coins
  verify y msg
    | none => pure false
    | some (w, z) => (fiatShamir (Function.Embedding.refl _) P keyGen).verify y msg (w, some z)

/-- Every branch of the all-attempt signer has at most `K` hash calls. This counts queries,
not running time. -/
theorem fiatShamirAbortSign_queryBound (P : SigmaProtocol X Y T C (Option Z))
    (sk : X × Y) (msg : M) (K : ℕ)
    (coins : Fin K → T × P.State) :
    IsQueryBounded (fiatShamirAbortSign P sk msg K coins) K := by
  induction K with
  | zero => exact .pure _ _
  | succ K ih =>
    unfold fiatShamirAbortSign
    simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    apply IsCostBounded.liftBind
    intro c
    simpa only [Nat.add_zero] using
      (ih (Fin.tail coins)).bind (fun _ => IsCostBounded.pure _ 0)

/-- With a fixed hash, the oracle program returns the first successful deterministic step. -/
theorem fiatShamirAbortSign_fixedHash (P : SigmaProtocol X Y T C (Option Z))
    (hash : M × T → C) (x : X) (y : Y) (msg : M)
    (K : ℕ) (coins : Fin K → T × P.State) :
    interpret (fun q => PMF.pure (hash q)) (fiatShamirAbortSign P (x, y) msg K coins) =
      PMF.pure ((((List.ofFn coins).map (fsAbortSignStep P hash x y msg)).find?
        Option.isSome).getD none) := by
  induction K with
  | zero => simp [fiatShamirAbortSign]
  | succ K ih =>
    simp only [pmf_norm, fiatShamirAbortSign, interpret_bind, interpret_map, interpret_query, ih,
      interpret_pure, List.ofFn_succ, List.map_cons]
    simp only [show Fin.tail coins = (fun i => coins i.succ) from rfl]
    cases hr : P.respond x y (coins 0).2 (hash (msg, (coins 0).1)) <;>
      simp [fsAbortSignStep, hr]

/-- Averaging the canonical all-attempt program with a fixed hash recovers the existing
bounded signer exactly. This identifies the output law, not a stopped oracle-cache trace. -/
theorem fiatShamirAbort_sign_fixedHash (P : SigmaProtocol X Y T C (Option Z))
    (keyGen : PMF (X × Y)) (hash : M × T → C) (x : X) (y : Y) (msg : M) (K : ℕ) :
    (((fiatShamirAbort P keyGen K).signCoins (x, y) msg).bind fun coins =>
      interpret (fun q => PMF.pure (hash q))
        ((fiatShamirAbort P keyGen K).sign (x, y) msg coins)) =
      fsAbortSignBounded P hash K x y msg := by
  simp only [fiatShamirAbort, fiatShamirAbortSign_fixedHash]
  have h := (fsAbortSignBounded_map_eq_iid P hash id K x y msg).symm
  simp only [Option.map_id, id_eq, PMF.map_id, fsAbortSignAttempt, iid_map, PMF.map_comp,
    Function.comp_def] at h
  simpa only [PMF.map, Function.comp_def, List.map_ofFn] using h

section View

/-- The complete one-attempt reply and external state have the same law for witnesses with
equal full transcripts. The stateful answering kernel and hash-point map are common to both
witnesses. -/
theorem fiatShamir_sign_run_eq_of_transcript_eq {Query R : Type}
    (hashPoint : M × T → Query) (P : SigmaProtocol X Y T C Z)
    (answer : (q : Query) → StateT R PMF C) {x x' : X} {y : Y}
    (h : ∀ c, P.transcript x y c = P.transcript x' y c) (msg : M) (state : R) :
    ((P.commit x y).bind fun coin =>
      (interpret answer
        ((fun c => (coin.1, P.respond x y coin.2 c)) <$>
          OracleComp.query (hashPoint (msg, coin.1)))).run state) =
    (P.commit x' y).bind fun coin =>
      (interpret answer
        ((fun c => (coin.1, P.respond x' y coin.2 c)) <$>
          OracleComp.query (hashPoint (msg, coin.1)))).run state := by
  have hk := bind_respond_challenge_eq_of_transcript_eq P h
    (fun w => (answer (hashPoint (msg, w))).run state)
  simpa only [pmf_norm, interpret_map, interpret_query, StateT.run_map] using
    congrArg (PMF.map fun view => ((view.1, view.2.2.1), view.2.2.2)) hk

variable {R : Type} (P : SigmaProtocol X Y T C (Option Z))
  (answer : (q : M × T) → StateT R PMF C)

/-- Sampling coins in advance agrees with executing the first attempt, then sampling and
executing the remaining attempts from its updated state. -/
theorem fiatShamirAbortSign_run_succ (x : X) (y : Y) (msg : M) (K : ℕ) (state : R) :
    ((iid (P.commit x y) (K + 1)).bind fun coins =>
      (interpret answer (fiatShamirAbortSign P (x, y) msg (K + 1) coins)).run state) =
    ((P.commit x y).bind fun coin =>
      (interpret answer
        ((fun c => (coin.1, P.respond x y coin.2 c)) <$>
          OracleComp.query (msg, coin.1))).run state).bind
      fun first =>
    ((iid (P.commit x y) K).bind fun coins =>
      (interpret answer (fiatShamirAbortSign P (x, y) msg K coins)).run first.2).map
      fun later =>
        ((first.1.2.map fun z => (first.1.1, z)).orElse (fun _ => later.1), later.2) := by
  simp only [pmf_norm, iid, Fin.cons_zero, Fin.tail_cons, fiatShamirAbortSign, run_interpret_bind,
    run_interpret_pure, PMF.map]
  congr 1
  funext coin
  exact PMF.bind_comm _ _ _

/-- Sequential witness invariance retains the complete final external state of all attempts.
It applies in particular to a memoizing random oracle, including aborts and repeated inputs. -/
theorem fiatShamirAbortSign_run_eq_of_transcript_eq {x x' : X} {y : Y}
    (h : ∀ c, P.transcript x y c = P.transcript x' y c) (msg : M) (K : ℕ) (state : R) :
    ((iid (P.commit x y) K).bind fun coins =>
      (interpret answer (fiatShamirAbortSign P (x, y) msg K coins)).run state) =
    (iid (P.commit x' y) K).bind fun coins =>
      (interpret answer (fiatShamirAbortSign P (x', y) msg K coins)).run state := by
  induction K generalizing state with
  | zero => simp [iid, fiatShamirAbortSign]
  | succ K ih =>
    rw [fiatShamirAbortSign_run_succ, fiatShamirAbortSign_run_succ,
      fiatShamir_sign_run_eq_of_transcript_eq (fun x => x) P answer h msg state]
    congr 1
    funext first
    rw [ih]

end View

section Adaptive

variable [DecidableEq M] [DecidableEq T] [Fintype C] [Nonempty C]

/-- The canonical signing/hash handler, including its message log and shared cache, is
witness-invariant. Failed signing requests are logged just like successful requests. -/
theorem fiatShamirAbort_handler_eq_of_transcript_eq
    (P : SigmaProtocol X Y T C (Option Z)) (keyGen : PMF (X × Y)) (K : ℕ)
    {x x' : X} {y : Y} (h : ∀ c, P.transcript x y c = P.transcript x' y c) :
    handler (fiatShamirAbort (M := M) P keyGen K) (x, y) =
      handler (fiatShamirAbort (M := M) P keyGen K) (x', y) := by
  funext request state
  cases request with
  | inl msg =>
    simp only [handler, fiatShamirAbort, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      ← PMF.bind_bind]
    rw [fiatShamirAbortSign_run_eq_of_transcript_eq P (oracle C) h]
  | inr query => rfl

/-- Every common adaptive forger program has the same joint output, hash cache and queried
message log for witnesses with equal transcripts. This is a single-run law, not a paired
execution that shares private signing coins between different witnesses. -/
theorem fiatShamirAbort_forger_run_eq_of_transcript_eq
    (P : SigmaProtocol X Y T C (Option Z)) (keyGen : PMF (X × Y)) (K : ℕ)
    {x x' : X} {y : Y} (h : ∀ c, P.transcript x y c = P.transcript x' y c)
    {α : Type} (program : OracleComp (ForgerSpec M (M × T) (Option (T × Z)) C) α)
    (state : List ((M × T) × C) × List M) :
    (interpret (handler (fiatShamirAbort P keyGen K) (x, y)) program).run state =
      (interpret (handler (fiatShamirAbort P keyGen K) (x', y)) program).run state := by
  rw [fiatShamirAbort_handler_eq_of_transcript_eq P keyGen K h]

/-- The canonical shared-cache worlds agree when the full transcript laws agree. This
identity also covers probabilistic forgers and final verification through `worldRealize`;
the public key and verification program are unchanged. -/
theorem fiatShamirAbort_world_eq_of_transcript_eq
    (P : SigmaProtocol X Y T C (Option Z)) (keyGen : PMF (X × Y)) (K : ℕ)
    {x x' : X} {y : Y} (h : ∀ c, P.transcript x y c = P.transcript x' y c) :
    world (fiatShamirAbort (M := M) P keyGen K) (x, y) =
      world (fiatShamirAbort (M := M) P keyGen K) (x', y) := by
  have hImpl : forgerWorldImpl (fiatShamirAbort (M := M) P keyGen K) (x, y) =
      forgerWorldImpl (fiatShamirAbort (M := M) P keyGen K) (x', y) := by
    funext request cache
    cases request with
    | inl msg =>
      exact fiatShamirAbortSign_run_eq_of_transcript_eq P (oracle C) h msg K cache
    | inr query => rfl
  simp only [world, hImpl]

end Adaptive

end Cslib.Crypto.Protocols.SigmaProtocol
