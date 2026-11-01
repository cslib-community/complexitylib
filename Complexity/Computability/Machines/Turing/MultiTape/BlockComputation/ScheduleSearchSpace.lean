/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearch
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitializedEvaluatorCorrect
import Complexity.Foundations.Data.Nat.BinarySize

/-!
# Uniform physical storage for sequential schedule search

All candidate executions share one allowance evaluated at the first excluded schedule number.
This power occurs only in mathematical bounds: the machine's actual guard streams schedule rows.
Only one suspended caller and one concrete initialized evaluator are retained at any clock.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleSearch

open MultiTapeTM Cslib.TreeEval.Ary.Packed
open QueryReplay

/-- Actual search arguments and a binary counter through the first excluded schedule number. -/
@[expose] noncomputable def callerSpace (k : ℕ) (args : Args) : ℕ :=
  let (_, _, q) := args
  8 * ((encArgs args).length + 2 * (k + 1) * q + 1)

/-- One candidate allowance, uniformly enlarged to the first excluded schedule metadata. -/
@[expose] noncomputable def candidateSpace (k s : ℕ) (Q : Type) (N b q : ℕ) : ℕ :=
  InitializedEvaluator.allowance k s Q N b (3 ^ ((k + 1) * q)) q

/-- One retained caller plus one initialized concrete evaluator, with call framing. -/
@[expose] noncomputable def space (k s : ℕ) (Q : Type) (N b q : ℕ) : ℕ :=
  2 * callerSpace k (N, b, q) + candidateSpace k s Q N b q + 2

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

/-- Schedule metadata enters the candidate allowance only through its binary encoded size. -/
theorem allowance_schedule_mono (k s : ℕ) (Q : Type) (N b q σ τ : ℕ) (hστ : σ ≤ τ) :
    InitializedEvaluator.allowance k s Q N b σ q ≤
      InitializedEvaluator.allowance k s Q N b τ q := by
  have h := length_encNat_mono hστ
  simp only [InitializedEvaluator.allowance, Initializer.space, Initializer.prepare,
    Initializer.bankCells, parameters, Initializer.encMetadata, Initializer.encArgs,
    encParameters, RawController.Query.queryStateBound, ConcreteSupplier.encContext,
    ConcreteSupplier.replySpace, ConcreteSupplier.gateSpace, ConcreteSupplier.metadataSpace,
    QueryGate.encParams, Interpolation.encContext, encNat3, length_encPair]
  omega

/-- Every accepted schedule's concrete execution allowance fits the uniform candidate bound. -/
theorem candidate_allowance_le (k s : ℕ) (Q : Type) (N b q σ : ℕ)
    (hσ : σ ≤ 3 ^ ((k + 1) * q)) :
    InitializedEvaluator.allowance k s Q N b σ q ≤ candidateSpace k s Q N b q :=
  allowance_schedule_mono k s Q N b q σ _ hσ

/-- Resumption cannot pass the first excluded schedule number. -/
theorem resume_counter_le {k s : ℕ} {Q : Type} (e : Q ≃ Fin s)
    (N b q σ : ℕ) (result : Option Bool) (returned : InitializedEvaluator.State k Q)
    (hpending : pending k ((N, b, q), σ, result) = true) :
    cursor (resume e ((N, b, q), σ, result) returned) ≤ 3 ^ ((k + 1) * q) := by
  have hp := hpending
  simp only [pending, Bool.and_eq_true] at hp
  have hv : ScheduleCounter.valid k (σ, q) = true := hp.2
  have hσ := ScheduleCounter.succ_le_bound hv
  cases ho : outcome e ((N, b, q), returned) <;>
    simp only [resume, ho, cursor] <;> omega

/-- Each physical prefix of one candidate stores just one caller and the actual callee. -/
theorem runFrom_one_encoding_le {k s : ℕ} {Q : Type} [Finite Q]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (N b q σ : ℕ) (result : Option Bool)
    (w : List Bool) (T : ℕ)
    (hpending : pending k ((N, b, q), σ, result) = true)
    (hpre : ∀ u < T, (InitializedEvaluator.machine M e).halted
      ((InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (N, b, σ, q)) u) = false)
    (hhalt : (InitializedEvaluator.machine M e).halted
      ((InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (N, b, σ, q)) T) = true)
    (hsize : ∀ u ≤ T, (InitializedEvaluator.encState
      ((InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (N, b, σ, q)) u)).length ≤ candidateSpace k s Q N b q)
    (t : ℕ) (ht : t ≤ T + 2) :
    (encState ((machine M e).runFrom w (.inl ((N, b, q), σ, result)) t)).length ≤
      space k s Q N b q := by
  let c : CallerState := ((N, b, q), σ, result)
  let start := InitializedEvaluator.start (Q := Q) k s (N, b, σ, q)
  have hp := hpending
  simp only [pending, Bool.and_eq_true] at hp
  have hv : ScheduleCounter.valid k (σ, q) = true := hp.2
  have hσ := (ScheduleCounter.valid_eq_true_iff k σ q).mp hv
  have hcaller := caller_encoding_le k N b q σ result hσ.le
  have hnext : (encCaller (resume e c
      ((InitializedEvaluator.machine M e).runFrom w start T))).length ≤
      callerSpace k (N, b, q) := by
    change (encCaller (match outcome e ((N, b, q),
      (InitializedEvaluator.machine M e).runFrom w start T) with
      | some answer => ((N, b, q), σ, some answer)
      | none => ((N, b, q), σ + 1, none))).length ≤ _
    cases ho : outcome e ((N, b, q), (InitializedEvaluator.machine M e).runFrom w start T) <;>
      apply caller_encoding_le <;> omega
  have hreq : request (Q := Q) k s c = some start := by
    simp only [request, c, hpending, ↓reduceIte, start]
  have hlive : (caller k).halted c = false := by
    simp only [caller, c, hpending, Bool.not_true]
  by_cases hzero : t = 0
  · subst t
    change (encCaller c).length + 1 ≤ _
    dsimp only [space, c, start] at hnext ⊢
    omega
  by_cases hfinal : t = T + 2
  · subst t
    rw [show (machine M e).runFrom w (.inl c) (T + 2) =
        .inl (resume e c ((InitializedEvaluator.machine M e).runFrom w start T)) from
      QueryMachine.withCalls_runFrom_call (caller k) (InitializedEvaluator.machine M e)
        (request k s) (resume e) w c start T hlive hreq hpre hhalt]
    change (encCaller (resume e c
      ((InitializedEvaluator.machine M e).runFrom w start T))).length + 1 ≤ _
    dsimp only [space, c, start] at hnext ⊢
    omega
  have hentry : (machine M e).runFrom w (.inl c) 1 = .inr (c, start) :=
    QueryMachine.withCalls_step_call (caller k) (InitializedEvaluator.machine M e)
      (request k s) (resume e) w c start hlive hreq
  rw [show t = 1 + (t - 1) by omega, QueryMachine.runFrom_add, hentry]
  have hpref := QueryMachine.withCalls_runFrom_subroutine_prefix (caller k)
    (InitializedEvaluator.machine M e) (request k s) (resume e) w c start (t - 1)
    (fun u hu => hpre u (by omega))
  rw [show (machine M e).runFrom w (.inr (c, start)) (t - 1) =
      .inr (c, (InitializedEvaluator.machine M e).runFrom w start (t - 1)) from hpref]
  have hcallee := hsize (t - 1) (by omega)
  change (encSum encCaller (encPair encCaller InitializedEvaluator.encState)
    (.inr (c, (InitializedEvaluator.machine M e).runFrom w start (t - 1)))).length ≤ _
  rw [QueryMachine.withCalls_encoding_inr_length]
  dsimp only [space, c, start] at hcallee ⊢
  omega

end Turing.MultiTapePTM.BlockComputation.ScheduleSearch
