/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Uniform physical storage for sequential schedule search

All candidate executions share one evaluator allowance `A N b q`, independent of the schedule
number. The first excluded schedule number occurs only in mathematical bounds: the machine's
actual guard streams schedule rows. Only one suspended caller and one evaluator are retained at
any clock.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleSearch

open MultiTapeTM

/-- Actual search arguments and a binary counter through the first excluded schedule number. -/
@[expose] noncomputable def callerSpace (k : ℕ) (args : Args) : ℕ :=
  let (_, _, q) := args
  8 * ((encArgs args).length + 2 * (k + 1) * q + 1)

/-- One retained caller plus one evaluator within allowance `A N b q`, with call framing. -/
@[expose] noncomputable def space (k : ℕ) (A : ℕ → ℕ → ℕ → ℕ) (N b q : ℕ) : ℕ :=
  2 * callerSpace k (N, b, q) + A N b q + 2

/-- The complete schedule counter uses only linearly many horizon bits. -/
theorem counter_encoding_le (k q σ : ℕ) (hσ : σ ≤ 3 ^ ((k + 1) * q)) :
    (encNat σ).length ≤ 2 * (k + 1) * q + 1 := by
  have h := (Nat.size_le_size hσ).trans (Nat.size_pow_le 3 ((k + 1) * q))
  have hthree : Nat.size 3 = 2 := rfl
  rw [hthree] at h
  rw [length_encNat_eq_size]
  nlinarith

/-- Every possible decision payload and every in-range cursor fit the same caller allowance. -/
theorem caller_encoding_le (k N b q σ : ℕ) (result : Option Bool)
    (hσ : σ ≤ 3 ^ ((k + 1) * q)) :
    (encCaller ((N, b, q), σ, result)).length ≤ callerSpace k (N, b, q) := by
  have hc := counter_encoding_le k q σ hσ
  have hr : (encOption encBool result).length ≤ 2 := by
    cases result <;> simp only [encOption_none, encOption_some, List.length_nil,
      List.length_cons, encBool_apply] <;> omega
  simp only [encCaller, length_encPair, callerSpace]
  omega

/-- Resumption cannot pass the first excluded schedule number. -/
theorem resume_counter_le {k : ℕ} (E : Evaluator)
    (N b q σ : ℕ) (result : Option Bool) (returned : E.State)
    (hpending : pending k ((N, b, q), σ, result) = true) :
    cursor (resume E ((N, b, q), σ, result) returned) ≤ 3 ^ ((k + 1) * q) := by
  have hp := hpending
  simp only [pending, Bool.and_eq_true] at hp
  have hv : ScheduleCounter.valid k (σ, q) = true := hp.2
  have hσ := ScheduleCounter.succ_le_bound hv
  cases ho : E.outcome ((N, b, q), returned) <;>
    simp only [resume, ho, cursor] <;> omega

/-- Each physical prefix of one candidate stores just one caller and the actual callee. -/
theorem runFrom_one_encoding_le {k : ℕ} (E : Evaluator) (A : ℕ → ℕ → ℕ → ℕ)
    (N b q σ : ℕ) (result : Option Bool) (w : List Bool) (T : ℕ)
    (hpending : pending k ((N, b, q), σ, result) = true)
    (hpre : ∀ u < T, E.machine.halted (E.machine.runFrom w (E.start (N, b, σ, q)) u) = false)
    (hhalt : E.machine.halted (E.machine.runFrom w (E.start (N, b, σ, q)) T) = true)
    (hsize : ∀ u ≤ T, (E.encState (E.machine.runFrom w (E.start (N, b, σ, q)) u)).length ≤
      A N b q)
    (t : ℕ) (ht : t ≤ T + 2) :
    (encState E ((machine E k).runFrom w (.inl ((N, b, q), σ, result)) t)).length ≤
      space k A N b q := by
  let c : CallerState := ((N, b, q), σ, result)
  let start := E.start (N, b, σ, q)
  have hp := hpending
  simp only [pending, Bool.and_eq_true] at hp
  have hv : ScheduleCounter.valid k (σ, q) = true := hp.2
  have hσ := (ScheduleCounter.valid_eq_true_iff k σ q).mp hv
  have hcaller := caller_encoding_le k N b q σ result hσ.le
  have hnext : (encCaller (resume E c (E.machine.runFrom w start T))).length ≤
      callerSpace k (N, b, q) := by
    change (encCaller (match E.outcome ((N, b, q), E.machine.runFrom w start T) with
      | some answer => ((N, b, q), σ, some answer)
      | none => ((N, b, q), σ + 1, none))).length ≤ _
    cases ho : E.outcome ((N, b, q), E.machine.runFrom w start T) <;>
      apply caller_encoding_le <;> omega
  have hreq : request E k c = some start := by
    simp only [request, c, hpending, ↓reduceIte, start]
  have hlive : (caller k).halted c = false := by
    simp only [caller, c, hpending, Bool.not_true]
  exact QueryMachine.withCalls_runFrom_call_encoding_le (caller k) E.machine (request E k)
    (resume E) w encCaller E.encState hlive hreq hpre hhalt hcaller hnext hsize t ht

end Turing.MultiTapePTM.BlockComputation.ScheduleSearch
