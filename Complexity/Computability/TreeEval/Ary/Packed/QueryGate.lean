/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.Executable
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Call

/-!
# Packed interpolation using same-input table calls

The assignment loop of `interpolateGrid` is a query-machine caller. Its state contains the
parameters, one assignment index and one modular accumulator. Each iteration requests a table
entry from a subroutine on the same original input, then adds its weighted contribution.
The table is never materialized. An explicit context carries the address of the gate or output
chunk needed by the supplier; no tree or truth table is built into this construction.

The supplied loop limit must equal `s^n` for the interpolation theorem. Computing that limit and
the native costs of supplier initialization, its computation and extracting its answer are
separate charged operations. The callee returns a state, not its output stream.
-/

@[expose] public section

namespace Cslib.TreeEval.Ary.Packed.QueryGate

open Turing Cslib.BitString

/-- Supplier context, modulus, alphabet size, coordinate count, point and assignment limit. -/
abbrev Params (γ : Type) := γ × (ℕ × ℕ × ℕ) × List ℕ × ℕ

/-- Parameters, the current assignment index and the sum accumulator. -/
abbrev State (γ : Type) := Params γ × ℕ × ℕ

variable {γ τ : Type}

/-- The fixed parameters with fresh assignment and sum counters. -/
def initial (q : Params γ) : State γ := (q, 0, 0)

/-- One local sum update after the table subroutine returns. -/
def resume (answer : τ → ℕ) (q : State γ) (t : τ) : State γ :=
  (q.1, gridSumStep q.1.2.1.1 q.1.2.1.2.1 q.1.2.1.2.2
    (fun _ => answer t) q.1.2.2.1 q.2)

/-- Request one entry whenever the assignment index is below the explicit loop limit. -/
def request (start : State γ → τ) (q : State γ) : Option τ :=
  if q.2.1 < q.1.2.2.2 then some (start q) else none

/-- The controller only advances when its table subroutine returns. -/
def controller (q : Params γ) : QueryMachine (State γ) where
  init := initial q
  query _ := 0
  next := Prod.fst
  emit _ := []
  halted st := decide (st.1.2.2.2 ≤ st.2.1)
  finish _ := []

/-- The complete assignment loop and its same-original-input table subroutine. -/
def machine (q : Params γ) (N : QueryMachine τ) (start : State γ → τ)
    (answer : τ → ℕ) : QueryMachine (State γ ⊕ (State γ × τ)) :=
  (controller q).withCalls N (request start) (resume answer)

/-- Pure assignment-loop states, used only to state the simulation invariant. -/
def sumState (q : Params γ) (table : ℕ → ℕ) (j : ℕ) : State γ :=
  (q, (gridSumStep q.2.1.1 q.2.1.2.1 q.2.1.2.2 table q.2.2.1)^[j] (0, 0))

@[simp] theorem sumState_zero (q : Params γ) (table : ℕ → ℕ) :
    sumState q table 0 = initial q := rfl

/-- The assignment counter advances by one after each returned entry. -/
theorem sumState_counter (q : Params γ) (table : ℕ → ℕ) (j : ℕ) :
    (sumState q table j).2.1 = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [sumState, Function.iterate_succ_apply']
    change ((gridSumStep q.2.1.1 q.2.1.2.1 q.2.1.2.2 table q.2.2.1)
      ((gridSumStep q.2.1.1 q.2.1.2.1 q.2.1.2.2 table q.2.2.1)^[j] (0, 0))).1 = j + 1
    change ((gridSumStep q.2.1.1 q.2.1.2.1 q.2.1.2.2 table q.2.2.1)^[j]
      (0, 0)).1 = j at ih
    change ((gridSumStep q.2.1.1 q.2.1.2.1 q.2.1.2.2 table q.2.2.1)^[j]
      (0, 0)).1 + 1 = j + 1
    exact congrArg (· + 1) ih

/-- Every caller-prefix accumulator is reduced; no earlier table values are retained. -/
theorem sumState_acc_lt (q : Params γ) (table : ℕ → ℕ) (j : ℕ)
    (hp : 0 < q.2.1.1) : (sumState q table j).2.2 < q.2.1.1 := by
  cases j with
  | zero => exact hp
  | succ j =>
    rw [sumState, Function.iterate_succ_apply']
    simp only [gridSumStep, hp.ne', ↓reduceIte]
    exact Nat.mod_lt _ hp

/-- A correct returned table value performs precisely the next existing sum step. -/
theorem resume_sumState (q : Params γ) (table : ℕ → ℕ) (j : ℕ)
    (answer : τ → ℕ) (t : τ) (ht : answer t = table j) :
    resume answer (sumState q table j) t = sumState q table (j + 1) := by
  have hc := sumState_counter q table j
  have hstep : gridSumStep q.2.1.1 q.2.1.2.1 q.2.1.2.2
      (fun _ => answer t) q.2.2.1 (sumState q table j).2 =
      gridSumStep q.2.1.1 q.2.1.2.1 q.2.1.2.2 table q.2.2.1
        (sumState q table j).2 := by
    simp only [gridSumStep, hc, ht]
  change (q, gridSumStep q.2.1.1 q.2.1.2.1 q.2.1.2.2
    (fun _ => answer t) q.2.2.1 (sumState q table j).2) = _
  rw [hstep]
  simp only [sumState, Function.iterate_succ_apply']

/-- One table call implements one sum iteration, with one entry and one return step. -/
theorem runFrom_one (q : Params γ) (N : QueryMachine τ) (start : State γ → τ)
    (answer : τ → ℕ) (w : List Bool) (table : ℕ → ℕ) (j T : ℕ)
    (hj : j < q.2.2.2)
    (hpre : ∀ i < T, N.halted (N.runFrom w (start (sumState q table j)) i) = false)
    (hhalt : N.halted (N.runFrom w (start (sumState q table j)) T) = true)
    (hanswer : answer (N.runFrom w (start (sumState q table j)) T) = table j) :
    (machine q N start answer).runFrom w (.inl (sumState q table j)) (T + 2) =
      .inl (sumState q table (j + 1)) := by
  have hc := sumState_counter q table j
  rw [← resume_sumState q table j answer _ hanswer]
  apply QueryMachine.withCalls_runFrom_call
  · change decide (q.2.2.2 ≤ (sumState q table j).2.1) = false
    rw [hc]
    exact decide_eq_false (by omega)
  · change (if (sumState q table j).2.1 < q.2.2.2 then
      some (start (sumState q table j)) else none) = _
    rw [hc]
    simp only [hj, ↓reduceIte]
  · exact hpre
  · exact hhalt

/-- Every finite prefix of the assignment loop is realized by finitely many same-input calls.
The supplier contract is required at each actual requested state, including the current sum. -/
theorem exists_runFrom_sumState (q : Params γ) (N : QueryMachine τ)
    (start : State γ → τ) (answer : τ → ℕ) (w : List Bool) (table : ℕ → ℕ)
    (hsupplier : ∀ j < q.2.2.2, ∃ T,
      (∀ i < T, N.halted (N.runFrom w (start (sumState q table j)) i) = false) ∧
      N.halted (N.runFrom w (start (sumState q table j)) T) = true ∧
      answer (N.runFrom w (start (sumState q table j)) T) = table j)
    (j : ℕ) (hj : j ≤ q.2.2.2) :
    ∃ T, (machine q N start answer).runFrom w (.inl (initial q)) T =
      .inl (sumState q table j) := by
  induction j with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    obtain ⟨T, hT⟩ := ih (by omega)
    obtain ⟨U, hpre, hhalt, hans⟩ := hsupplier j (by omega)
    refine ⟨T + (U + 2), ?_⟩
    rw [QueryMachine.runFrom_add, hT]
    exact runFrom_one q N start answer w table j U (by omega) hpre hhalt hans

/-- With the full grid limit, the same-input caller returns the existing streamed interpolation.
Its final accumulator, rather than the deliberately empty output stream, is the result. -/
theorem exists_runFrom_interpolateGrid (q : Params γ) (N : QueryMachine τ)
    (start : State γ → τ) (answer : τ → ℕ) (w : List Bool) (table : ℕ → ℕ)
    (hlimit : q.2.2.2 = q.2.1.2.1 ^ q.2.1.2.2)
    (hsupplier : ∀ j < q.2.2.2, ∃ T,
      (∀ i < T, N.halted (N.runFrom w (start (sumState q table j)) i) = false) ∧
      N.halted (N.runFrom w (start (sumState q table j)) T) = true ∧
      answer (N.runFrom w (start (sumState q table j)) T) = table j) :
    ∃ T, (machine q N start answer).runFrom w (.inl (initial q)) T =
      .inl (q, q.2.2.2,
        interpolateGrid q.2.1.1 q.2.1.2.1 q.2.1.2.2 table q.2.2.1) := by
  obtain ⟨T, hT⟩ := exists_runFrom_sumState q N start answer w table hsupplier q.2.2.2 le_rfl
  refine ⟨T, hT.trans ?_⟩
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact sumState_counter q table q.2.2.2
    · simp only [sumState, interpolateGrid, hlimit]

/-- The one-entry table consumed by the existing counter gate extension. -/
def gateTable {s b d r : ℕ} (hs : 0 < s)
    (encode : (Fin b → Bool) → Fin r → Fin s)
    (decode : (Fin r → Fin s) → Fin b → Bool) (f : Gate d b) (i : Fin r) : ℕ → ℕ :=
  fun k => (encode (f fun j => decode (blocksEquiv (fun a : Fin (d * r) =>
    (⟨gridDigit s k a, Nat.mod_lt _ hs⟩ : Fin s)) j)) i).val

/-- Parameters for one output coordinate of the existing packed extension. -/
def gateParams {p s d r : ℕ} (context : γ) (x : Fin d → Fin r → ZMod p) : Params γ :=
  (context, (p, s, d * r),
    List.ofFn (fun a : Fin (d * r) => (blocksEquiv.symm x a).val), s ^ (d * r))

/-- A table supplier with the explicit same-input contract realizes the actual packed gate
extension used by the iterative evaluator, rather than a separate interpolation specification. -/
theorem exists_runFrom_counterGateExtension {p s b d r : ℕ} (hs : 0 < s)
    (context : γ) (encode : (Fin b → Bool) → Fin r → Fin s)
    (decode : (Fin r → Fin s) → Fin b → Bool) (f : Gate d b)
    (x : Fin d → Fin r → ZMod p) (i : Fin r)
    (N : QueryMachine τ) (start : State γ → τ) (answer : τ → ℕ) (w : List Bool)
    (hsupplier : ∀ j < s ^ (d * r), ∃ T,
      (∀ k < T, N.halted (N.runFrom w
        (start (sumState (gateParams (s := s) context x) (gateTable hs encode decode f i) j))
          k) = false) ∧
      N.halted (N.runFrom w
        (start (sumState (gateParams (s := s) context x) (gateTable hs encode decode f i) j))
          T) = true ∧
      answer (N.runFrom w
        (start (sumState (gateParams (s := s) context x) (gateTable hs encode decode f i) j))
          T) = gateTable hs encode decode f i j) :
    ∃ T z, (machine (gateParams (s := s) context x) N start answer).runFrom w
        (.inl (initial (gateParams (s := s) context x))) T =
        .inl (gateParams (s := s) context x, s ^ (d * r), z) ∧
      (z : ZMod p) = counterGateExtension hs encode decode f x i := by
  obtain ⟨T, hT⟩ := exists_runFrom_interpolateGrid (gateParams (s := s) context x)
    N start answer w (gateTable hs encode decode f i) rfl hsupplier
  exact ⟨T, _, hT, rfl⟩

end Cslib.TreeEval.Ary.Packed.QueryGate
