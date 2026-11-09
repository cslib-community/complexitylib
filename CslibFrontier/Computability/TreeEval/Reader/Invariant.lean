/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Reader.Correct
public import Mathlib.NumberTheory.Bertrand

/-!
# An invariant of the Tree Evaluation read machine

The invariant of `Cslib.TreeEval.Reader.machine` follows each phase separately: the header
phases bound the parameters read so far, and the search phase bounds the candidate prime.
After initialization, the machine has the correct parameters, well-formed registers,
at most `h` frames with bounded rounds, and bounded counters. `RunInv` records bounds
on the modulus `p`, not primality; the chosen prime is at most `4ℓ + 2`.

## Main definitions

* `Cslib.TreeEval.Reader.Inv`: the invariant.

## Main results

* `Cslib.TreeEval.Reader.primeFor_le`: by Bertrand's postulate, the prime is at most `4ℓ + 2`.
* `Cslib.TreeEval.Reader.inv_run`: every state reached on the encoding satisfies the invariant.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Iter Turing

/-- **Bertrand's postulate** bounds the prime: `primeFor ℓ ≤ 4ℓ + 2`. -/
theorem primeFor_le (ℓ : ℕ) : primeFor ℓ ≤ 4 * ℓ + 2 := by
  obtain ⟨q, hq, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * ℓ + 1) (by omega)
  have := Nat.find_min' (Nat.exists_infinite_primes (2 * ℓ + 2)) ⟨by omega, hq⟩
  rw [← primeFor] at this
  omega

/-- The invariant of the procedure: the parameters read, a bounded modulus, well-formed registers, a
stack of bounded depth with rounds below the modulus, and bounded counters. -/
def RunInv (ℓ H : ℕ) (s : State) : Prop :=
  s.ell = ℓ ∧ s.height = H ∧ 2 ≤ s.p ∧ s.p ≤ primeFor ℓ ∧ s.regs.WF s.p ℓ ∧
    s.stack.length ≤ H ∧ (∀ fr ∈ s.stack, fr.round < s.p) ∧
    match s.ctl with
    | .leaf i => i ≤ ℓ
    | .scan k acc => k ≤ tableLength ℓ ∧ acc.length = ℓ ∧ ∀ v ∈ acc, v < s.p
    | .run | .done => True
    | _ => False

/-- **The invariant** of the machine on an instance of value length `ℓ` and height `H`. -/
def Inv (ℓ H : ℕ) (s : State) : Prop :=
  match s.ctl with
  | .hdrLength n => s = ⟨0, 0, 0, ([], [], []), [], .ret, .hdrLength n⟩ ∧ n ≤ ℓ
  | .hdrHeight n => s = ⟨ℓ, 0, 0, ([], [], []), [], .ret, .hdrHeight n⟩ ∧ n ≤ H
  | .prime q d => s = ⟨ℓ, H, 0, ([], [], []), [], .ret, .prime q d⟩ ∧ 2 * ℓ + 2 ≤ q ∧
      q ≤ primeFor ℓ ∧ 2 ≤ d ∧ d ≤ q
  | _ => RunInv ℓ H s

private theorem inv_init (ℓ H : ℕ) : Inv ℓ H init := ⟨rfl, Nat.zero_le _⟩

variable {ℓ H : ℕ} (T : Tree ℓ H)

/-- **A step keeps the invariant.** -/
private theorem inv_step {s : State} (hs : Inv ℓ H s) (hh : machine.halt s = false) :
    Inv ℓ H (machine.step s (machine.readBit T.encode s)).1 := by
  obtain ⟨e, h, p, R, st, m, c⟩ := s
  cases c with
  | hdrLength n =>
    obtain ⟨heq, hn⟩ := hs
    simp only [State.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := heq
    rcases Nat.lt_or_ge n ℓ with hlt | hge
    · have hb := getElem?_encode_lt_ell (T := T) hlt
      simp only [machine, step, addr, ReadMachine.readBit, List.getD_eq_getElem?_getD, hb,
        Option.getD_some, ↓reduceIte]
      exact ⟨rfl, by omega⟩
    · obtain rfl : n = ℓ := by omega
      have hb := getElem?_encode_ell (T := T)
      simp only [machine, step, addr, ReadMachine.readBit, List.getD_eq_getElem?_getD, hb,
        Option.getD_some, Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, Nat.zero_le _⟩
  | hdrHeight n =>
    obtain ⟨heq, hn⟩ := hs
    simp only [State.mk.injEq] at heq
    obtain ⟨he, rfl, rfl, rfl, rfl, rfl, -⟩ := heq
    subst e
    rcases Nat.lt_or_ge n H with hlt | hge
    · have hb := getElem?_encode_height (T := T) hlt
      simp only [machine, step, addr, ReadMachine.readBit, List.getD_eq_getElem?_getD, hb,
        Option.getD_some, ↓reduceIte]
      exact ⟨rfl, by omega⟩
    · obtain rfl : n = H := by omega
      have hb := getElem?_encode_height_end (T := T)
      simp only [machine, step, addr, ReadMachine.readBit, List.getD_eq_getElem?_getD, hb,
        Option.getD_some, Bool.false_eq_true, ↓reduceIte]
      exact ⟨rfl, le_rfl, le_primeFor ℓ, le_rfl, by omega⟩
  | prime q d =>
    obtain ⟨heq, hq, hqp, hd, hdq⟩ := hs
    simp only [State.mk.injEq] at heq
    obtain ⟨he, hh₁, rfl, rfl, rfl, rfl, -⟩ := heq
    subst e h
    by_cases hlt : d < q
    · by_cases hmod : q % d = 0
      · have hne : q ≠ primeFor ℓ := fun he => by
          have := (Nat.prime_def_lt'.mp (he ▸ primeFor_prime ℓ)).2 d hd hlt
          exact this (Nat.dvd_of_mod_eq_zero hmod)
        simp only [machine, step, hlt, hmod, ↓reduceIte]
        exact ⟨rfl, by omega, by omega, le_rfl, by omega⟩
      · simp only [machine, step, hlt, hmod, ↓reduceIte]
        exact ⟨rfl, hq, hqp, by omega, by omega⟩
    · simp only [machine, step, hlt, ↓reduceIte]
      refine ⟨rfl, rfl, by dsimp only; omega, hqp, fun r => ?_, by simp, by simp, trivial⟩
      fin_cases r <;> simp [Regs.get] <;> omega
  | run =>
    dsimp only [Inv, RunInv] at hs
    obtain ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, -⟩ := hs
    have hp : 0 < p := by omega
    rcases m with ⟨neg, t⟩ | _
    · by_cases hlen : st.length = h
      · simp only [machine, step, runStep, hlen, ↓reduceIte]
        exact ⟨rfl, rfl, hp2, hpp, hR, by omega, hrd, Nat.zero_le _⟩
      · simp only [machine, step, runStep, hlen, ↓reduceIte]
        exact ⟨rfl, rfl, hp2, hpp, hR.scale hp _ _, by simp; omega,
          List.forall_mem_cons.2 ⟨by simp; omega, hrd⟩, trivial⟩
    · rcases st with _ | ⟨⟨j, ph, ng, tg⟩, st⟩
      · simp only [machine, step, runStep]
        exact ⟨rfl, rfl, hp2, hpp, hR, by simp, by simp, trivial⟩
      · obtain ⟨hj, hrd'⟩ := List.forall_mem_cons.1 hrd
        simp only [List.length_cons] at hst
        fin_cases ph
        · simp only [machine, step, runStep]
          exact ⟨rfl, rfl, hp2, hpp, hR.scale hp _ _, by simp; omega,
            List.forall_mem_cons.2 ⟨hj, hrd'⟩, trivial⟩
        · simp only [machine, step, runStep]
          refine ⟨rfl, rfl, hp2, hpp, hR, by simp; omega, hrd, by simp [tableLength], by simp,
            fun v hv => ?_⟩
          rw [(List.mem_replicate.mp hv).2]; exact hp
        · simp only [machine, step, runStep]
          exact ⟨rfl, rfl, hp2, hpp, hR.scale hp _ _, by simp; omega,
            List.forall_mem_cons.2 ⟨hj, hrd'⟩, trivial⟩
        · by_cases hnext : j + 1 < p - 1
          · simp only [machine, step, runStep, hnext, ↓reduceIte]
            exact ⟨rfl, rfl, hp2, hpp, (hR.scale hp _ _).scale hp _ _, by simp; omega,
              List.forall_mem_cons.2 ⟨by simp; omega, hrd'⟩, trivial⟩
          · simp only [machine, step, runStep, hnext, ↓reduceIte]
            exact ⟨rfl, rfl, hp2, hpp, hR.scale hp _ _, by dsimp only; omega, hrd', trivial⟩
  | leaf i =>
    dsimp only [Inv, RunInv] at hs
    obtain ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, hi⟩ := hs
    have hp : 0 < p := by omega
    rcases m with ⟨neg, t⟩ | _
    · by_cases hlt : i < e
      · simp only [machine, step, hlt, ↓reduceIte]
        exact ⟨rfl, rfl, hp2, hpp, hR.set_modifyAt hp _ _ _, hst, hrd, by omega⟩
      · simp only [machine, step, hlt, ↓reduceIte]
        exact ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, trivial⟩
    · simp only [machine, step]
      exact ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, hi⟩
  | scan k acc =>
    dsimp only [Inv, RunInv] at hs
    obtain ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, hk, hacc, hacc'⟩ := hs
    have hp : 0 < p := by omega
    rcases st with _ | ⟨fr, st⟩
    · simp only [machine, step]
      exact ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, hk, hacc, hacc'⟩
    · by_cases hlt : k < tableLength e
      · cases hb : machine.readBit T.encode ⟨e, h, p, R, fr :: st, m, .scan k acc⟩
        · simp only [machine, step, hlt, ↓reduceIte, Bool.false_eq_true]
          exact ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, by omega, hacc, hacc'⟩
        · simp only [machine, step, hlt, ↓reduceIte]
          obtain ⟨h₁, h₂⟩ := modifyAt_addMod_wf hp hacc' (k % e)
            (weight p e (k / e) (R.get (fr.target + 1)) (R.get (fr.target + 2)))
          exact ⟨rfl, rfl, hp2, hpp, hR, hst, hrd, by omega, by rw [h₁, hacc], h₂⟩
      · simp only [machine, step, hlt, ↓reduceIte]
        obtain ⟨hj, hrd'⟩ := List.forall_mem_cons.1 hrd
        exact ⟨rfl, rfl, hp2, hpp, hR.subtractSums hp _ _ _, by simpa using hst,
          List.forall_mem_cons.2 ⟨hj, hrd'⟩, trivial⟩
  | done => simp [machine] at hh

/-- **Every state reached on the encoding satisfies the invariant.** -/
theorem inv_run (j : ℕ) : Inv ℓ H (machine.run T.encode j).state := by
  induction j with
  | zero => exact inv_init ℓ H
  | succ j ih =>
    rw [ReadMachine.run_add, ReadMachine.runFrom_one]
    by_cases hh : machine.halt (machine.run T.encode j).state
    · simp only [ReadMachine.next, hh, ↓reduceIte]; exact ih
    · rw [ReadMachine.next_of_not_halt _ _ (by simpa using hh)]
      exact inv_step T ih (by simpa using hh)

end Reader

end Cslib.TreeEval
