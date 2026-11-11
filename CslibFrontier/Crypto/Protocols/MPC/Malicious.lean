/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Composition
import CslibFrontier.Languages.Probabilistic.Norm

/-!
# Malicious Ideal Wrappers

This module formalizes the malicious ideal execution with abort for general $m$-party
functionalities, generalizing the commitment-specific world from
`CslibFrontier/Crypto/Protocols/MPC/OTCommitment/World.lean`.
It proves the equivalence of explicit abort and wrapper-based abort for ideal functionalities
and formalizes the classic counterexample showing that naive without-abort composition
fails when the adversary can abort, as noted in #3673 M12 (Goldreich).

## Main definitions
* `Cslib.Crypto.Protocols.MPC.maliciousIdeal`: Ideal execution without abort where the adversary
  supplies corrupted inputs, receives their outputs, and produces a view.
* `Cslib.Crypto.Protocols.MPC.maliciousIdealWithAbort`: Ideal execution where the adversary
  supplies corrupted inputs, receives their outputs, and then decides whether to abort or release
  the honest outputs.

## Main results
* `Cslib.Crypto.Protocols.MPC.adversaryAborts_characterization`:
  The equivalence of malicious ideal execution with abort and the adversary-aborts wrapper.
* `Cslib.Crypto.Protocols.MPC.naive_without_abort_failure`: Counterexample to naive without-abort
  composition.
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Probability Cslib.ProbComp

/-- Malicious ideal execution without abort. -/
@[expose] public def maliciousIdeal {m : ℕ} {In Out : Fin m → Type} {View : Type}
    (f : Functionality m In Out) (I : Finset (Fin m))
    (x : (i : Fin m) → In i)
    (S : ((i : I) → In i) → ProbComp (((i : I) → In i) × (((i : I) → Out i) → View))) :
    ProbComp (View × ((i : Fin m) → Out i)) := do
  let (x_I_prime, S_out) ← S (I.restrict x)
  let x_prime := fun i => if h : i ∈ I then x_I_prime ⟨i, h⟩ else x i
  let y ← f x_prime
  let v := S_out (I.restrict y)
  return (v, y)

/-- Malicious ideal execution with abort. The adversary `S` provides inputs for `I`,
then given the outputs for `I`, decides whether to continue (`true`) or abort (`false`),
and outputs a view. Honest parties receive `some y` if continue, or `none` if abort. -/
@[expose] public def maliciousIdealWithAbort {m : ℕ} {In Out : Fin m → Type} {View : Type}
    (f : Functionality m In Out) (I : Finset (Fin m))
    (x : (i : Fin m) → In i)
    (S : ((i : I) → In i) → ProbComp (((i : I) → In i) × (((i : I) → Out i) → Bool × View))) :
    ProbComp (View × ((i : Fin m) → Option (Out i))) := do
  let (x_I_prime, S_out) ← S (I.restrict x)
  let x_prime := fun i => if h : i ∈ I then x_I_prime ⟨i, h⟩ else x i
  let y ← f x_prime
  let (cont, v) := S_out (I.restrict y)
  let y_final := fun i => if cont || (i ∈ I) then some (y i) else none
  return (v, y_final)

/-- An adversary-aborts wrapper around a functionality, explicitly modeling the abort phase
within a standard functionality, avoiding the need for a custom ideal execution definition. -/
@[expose] public def adversaryAborts {m : ℕ} {In Out : Fin m → Type}
    (f : Functionality m In Out) (I : Finset (Fin m)) :
    Functionality m (fun i => In i × (i ∈ I → ((j : I) → Out j) → Bool))
      (fun i => Option (Out i)) :=
  fun x => do
    let y ← f (fun i => (x i).1)
    let cont := ∀ i : I, (x i.1).2 i.2 (fun j => y j.1)
    return fun i => if cont || (i ∈ I) then some (y i) else none

@[simp] private theorem fst_dite {α β} (c : Prop) [Decidable c] (t : c → α × β) (e : ¬c → α × β) :
  (if h : c then t h else e h).1 = if h : c then (t h).1 else (e h).1 := by
  split_ifs <;> rfl

@[simp] private theorem snd_dite {α β} (c : Prop) [Decidable c] (t : c → α × β) (e : ¬c → α × β) :
  (if h : c then t h else e h).2 = if h : c then (t h).2 else (e h).2 := by
  split_ifs <;> rfl

private theorem pmf_bind_congr {α β} {p q : PMF α} {f g : α → PMF β} (hpq : p = q)
    (hfg : ∀ x, f x = g x) :
  p.bind f = q.bind g := by
  cases hpq
  congr 1
  funext x
  exact hfg x

/--
The equivalence of malicious ideal execution with abort and the adversary-aborts wrapper.
## References
* Goldreich 2004 (abort equivalence concept)
-/
theorem adversaryAborts_characterization {m : ℕ} {In Out : Fin m → Type} {View : Type}
    [Inhabited View]
    (f : Functionality m In Out) (I : Finset (Fin m)) (hI : I.Nonempty)
    (x : (i : Fin m) → In i)
    (S : ((i : I) → In i) → ProbComp (((i : I) → In i) × (((i : I) → Out i) → Bool × View))) :
    ProbComp.eval (maliciousIdealWithAbort f I x S) =
      ProbComp.eval (maliciousIdeal (adversaryAborts f I) I (fun i => (x i, fun _ _ => true))
        (fun x_I => do
          let (x_I_prime, S_out) ← S (fun i => (x_I i).1)
          return (fun i => (x_I_prime i, fun _ y_I => (S_out y_I).1), fun y_I =>
            if h : ∀ i, (y_I i).isSome then
              (S_out (fun i => Option.get _ (h i))).2
            else default))) := by
  dsimp [maliciousIdealWithAbort, maliciousIdeal, adversaryAborts]
  simp only [fst_dite, eval_bind, eval_pure, PMF.bind_bind, PMF.pure_bind]
  apply pmf_bind_congr
  · rfl
  · intro ⟨x_I_prime, S_out⟩
    apply pmf_bind_congr
    · rfl
    · intro y
      congr 1
      have H_true : ∀ i : I, (decide (∀ i_1 : I,
        ((if ↑i_1 ∈ I then (x_I_prime i_1, fun x y_I => (S_out y_I).1)
          else (x ↑i_1, fun x x_1 => true)).2
          i_1.2 fun j => y ↑j) = true) || decide (↑i ∈ I)) = true := by
        intro i
        have hi := i.2
        simp [hi]
      apply Prod.ext
      · dsimp
        have H_isSome : ∀ i : I, (Finset.restrict I (fun i_1 =>
          if (decide (∀ i_1 : I, ((if ↑i_1 ∈ I then (x_I_prime i_1, fun x y_I => (S_out y_I).1)
            else (x ↑i_1, fun x x_1 => true)).2 i_1.2 fun j => y ↑j) = true)
            || decide (i_1 ∈ I)) = true
          then some (y i_1) else none) i).isSome = true := by
          intro i
          have hi := H_true i
          simp [Finset.restrict]
        simp; rfl
      · ext i
        dsimp
        have h_Sout : ∀ i_1 : I, ((if ↑i_1 ∈ I then (x_I_prime i_1, fun x y_I => (S_out y_I).1)
          else (x ↑i_1, fun x x_1 => true)).2 i_1.2 fun j => y ↑j) = (S_out (I.restrict y)).1 := by
          intro i_1
          have hi1 := i_1.2
          simp [hi1]; rfl
        simp_rw [h_Sout]
        have h_all : (∀ a : I, (S_out (I.restrict y)).1 = true) ↔
          (S_out (I.restrict y)).1 = true := by
          constructor
          · intro h
            rcases hI with ⟨x, hx⟩
            exact h ⟨x, hx⟩
          · intro h _
            exact h
        simp_rw [h_all]
        simp

/-- In the ideal model without abort, the honest party's output is independent
if the functionality provides no output to the adversary. -/
noncomputable def coinTossPrivateFunc : Functionality 2 (fun _ => Unit)
  (fun i => if i = 0 then Unit else Bool) :=
  fun _ => do
    let b ← uniform Bool
    return fun i => if h : i = 0 then cast (by simp [h]) () else cast (by simp [h]) b

/-- The set of corrupted parties containing only party 0. -/
def I0 : Finset (Fin 2) := {0}

/-- The biased coin toss distribution where party 1 aborts on false. -/
noncomputable def coinTossBiasedDist :
  ProbComp (Unit × ((i : Fin 2) → Option (if i = 0 then Unit else Bool))) := do
  let b ← uniform Bool
  if b then
    return ((), fun i => if h : i = 0 then cast (by simp [h]) (some ())
      else cast (by simp [h]) (some true))
  else
    return ((), fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none)

theorem naive_without_abort_failure :
  ¬ (∃ S, ProbComp.eval (do
            let (v, y) ← maliciousIdeal coinTossPrivateFunc I0 (fun _ => ()) S
            return (v, fun i => some (y i))) = 
          ProbComp.eval coinTossBiasedDist) := by
  intro ⟨S, h⟩
  have H := congr_arg (fun (p : PMF _)
    => p ((), fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none)) h
  have h_rhs : ProbComp.eval coinTossBiasedDist
      ((), fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none) = 1/2 := by
    dsimp [coinTossBiasedDist]
    simp only [eval_bind, eval_uniform, PMF.bind_apply, PMF.uniformOfFintype_apply]
    have h_true : ((fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none) :
        (i : Fin 2) → Option (if i = 0 then Unit else Bool)) ≠ 
      (fun i => if h : i = 0 then cast (by simp [h]) (some ())
        else cast (by simp [h]) (some true)) := by
      intro heq
      have h2 := congr_fun heq 1
      have h1 : (1 : Fin 2) ≠ 0 := by decide
      revert h2
      simp [h1]
    simp [h_true]
  have h_lhs : ProbComp.eval (do
            let (v, y) ← maliciousIdeal coinTossPrivateFunc I0 (fun _ => ()) S
            return (v, fun i => some (y i)))
      ((), fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none) = 0 := by
    simp only [PMF.map_apply, bind_pure_comp, eval_map, tsum_eq_zero_iff]
    intro a
    split_ifs with h
    · have h_false
        : ((fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none)
          : (i : Fin 2) → Option (if i = 0 then Unit else Bool)) ≠ fun i => some (a.2 i) := by
        intro heq2
        have h2 := congr_fun heq2 1
        have h1 : (1 : Fin 2) ≠ 0 := by decide
        revert h2
        simp [h1]
      have heq2
        : ((fun i => if h : i = 0 then cast (by simp [h]) (some ()) else none)
          : (i : Fin 2) → Option (if i = 0 then Unit else Bool)) = fun i => some (a.2 i) := by
        have h_snd := congr_arg Prod.snd h
        exact h_snd
      contradiction
    · rfl
  rw [h_rhs, h_lhs] at H
  apply_fun ENNReal.toReal at H
  revert H
  norm_num

end Cslib.Crypto.Protocols.MPC
