/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of same-input packed interpolation)

public import Complexity.Computability.TreeEval.Ary.Packed.QueryGateInit

/-!
# Packed interpolation with an actual input-reading supplier

The table subroutine reads the requested bit from the original input. Two calls produce the
interpolated value without retaining a table. Its native certificates use binary indices and
finite bit decoding, and include initialization of the full assignment limit.
-/

@[expose] public section

namespace ComplexityTests.TreeEvalQueryGate

open Turing MultiTapeTM Cslib.TreeEval.Ary.Packed
open Cslib.TreeEval.Ary.Packed.QueryGate

abbrev Entry := ℕ × Bool × ℕ
abbrev encEntry : Entry ↪ List Bool := encPair encNat (encPair encBool encNat)

/-- Return the requested original-input bit in a numeric accumulator. -/
def supplier : QueryMachine Entry where
  init := (0, false, 0)
  query := Prod.fst
  next p := (p.1.1, true, if p.2.getD false then 1 else 0)
  emit _ := [true]
  halted s := s.2.1
  finish _ := [true]

def start (q : State Unit) : Entry := (q.2.1, false, 0)
def answer (t : Entry) := t.2.2

/-- Two Boolean assignments, evaluated at the field point three modulo five. -/
def input : Input Unit := ((), (5, 2, 1), [3])
def params := prepare input

def loop := machine params supplier start answer

example : params.2.2.2 = 2 := rfl
example : loop.run [true, false] 6 = .inl (params, 2, 3) := by rfl
example : loop.run [false, true] 6 = .inl (params, 2, 3) := by rfl
example : loop.run [true, true] 6 = .inl (params, 2, 1) := by rfl
example : loop.run [] 6 = .inl (params, 2, 0) := by rfl
example : loop.halted (loop.run [true, false] 6) = true := by rfl
example : loop.output [true, false] 6 = [] := by decide

/-- Every lookup contract is witnessed by one actual input query. -/
example (w : List Bool) :
    ∃ T, loop.runFrom w (.inl (initial params)) T =
      .inl (params, 2, interpolateGrid 5 2 1
        (fun j => if w[j]?.getD false then 1 else 0) [3]) := by
  apply exists_runFrom_interpolateGrid params supplier start answer w
  · rfl
  · intro j hj
    refine ⟨1, ?_, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      subst i
      rfl
    · rfl
    · simp only [QueryMachine.runFrom_succ, QueryMachine.runFrom_zero,
        QueryMachine.step, QueryMachine.read, supplier, start, answer, sumState_counter]
      rfl

private theorem query_native :
    ComputableInSpace supplier.query encEntry encNat (fun t => (encEntry t).length) :=
  ComputableInSpace.fst _ _

private theorem halt_native :
    ComputableInSpace supplier.halted encEntry encBool (fun t => (encEntry t).length) :=
  ComputableInSpace.fst' (ComputableInSpace.snd encNat (encPair encBool encNat))

private theorem next_native :
    ComputableInSpace supplier.next (encPair encEntry (encOption encBool)) encEntry
      (fun t => (encPair encEntry (encOption encBool) t).length) := by
  open ComputableInSpace in
    exact budget_prod (fst' (fst encEntry (encOption encBool)))
      (budget_prod (budget_const true (.refl _))
        (budget_finite (encC := encNat) (fun b : Option Bool => if b.getD false then 1 else 0)
          (snd encEntry (encOption encBool))))

private theorem start_native :
    ComputableInSpace start (encState encUnit) encEntry
      (fun q => (encState encUnit q).length) := by
  open ComputableInSpace in
    exact budget_prod (fst' (snd (encParams encUnit) (encPair encNat encNat)))
      (budget_prod (budget_const false (.refl _)) (budget_const 0 (.refl _)))

private theorem answer_native :
    ComputableInSpace answer encEntry encNat (fun t => (encEntry t).length) :=
  ComputableInSpace.snd' (ComputableInSpace.snd encNat (encPair encBool encNat))

example : ComputableInSpace loop.next
    (encPair (encMachineState encUnit encEntry) (encOption encBool))
    (encMachineState encUnit encEntry)
    (fun t => (encPair (encMachineState encUnit encEntry) (encOption encBool) t).length) :=
  machine_next_inSpace encUnit encEntry params supplier start answer
    next_native halt_native start_native answer_native

example : ComputableInSpace (fun q : Input Unit => initial (prepare q))
    (encInput encUnit) (encState encUnit) (initializationSpace encUnit) :=
  initial_prepare_inSpace encUnit

private theorem supplier_peak (w : List Bool) (k i : ℕ) (hk : k < 2) (hi : i ≤ 1) :
    (encEntry (supplier.runFrom w (k, false, 0) i)).length ≤ 7 := by
  have hk' : k = 0 ∨ k = 1 := by omega
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hk' with rfl | rfl <;> rcases hi' with rfl | rfl
  · norm_num [QueryMachine.runFrom_zero, encEntry]
  · cases h : w[0]?.getD false <;> simp [QueryMachine.runFrom_succ,
      QueryMachine.runFrom_zero, QueryMachine.step, QueryMachine.read, supplier,
      encEntry, encBool_apply, h]
  · norm_num [QueryMachine.runFrom_zero, encEntry]
  · cases h : w[1]?.getD false <;> simp [QueryMachine.runFrom_succ,
      QueryMachine.runFrom_zero, QueryMachine.step, QueryMachine.read, supplier,
      encEntry, encBool_apply, h]

/-- A concrete supplier also satisfies the full physical-prefix space contract. -/
example (w : List Bool) :
    ∃ T, loop.runFrom w (.inl (initial params)) T =
      .inl (sumState params (fun j => if w[j]?.getD false then 1 else 0) 2) ∧
      ∀ i ≤ T, (encMachineState encUnit encEntry
        (loop.runFrom w (.inl (initial params)) i)).length ≤
          16 * ((encParams encUnit params).length + 1) + 7 + 2 := by
  apply exists_runFrom_sumState_encoding_le encUnit encEntry params supplier start answer w
    _ 7 (by decide) _ 2 (by decide)
  intro j hj
  refine ⟨1, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst i
    rfl
  · rfl
  · simp only [QueryMachine.runFrom_succ, QueryMachine.runFrom_zero,
      QueryMachine.step, QueryMachine.read, supplier, start, answer, sumState_counter]
    rfl
  · intro i hi
    change (encEntry (supplier.runFrom w
      ((sumState params _ j).2.1, false, 0) i)).length ≤ 7
    rw [sumState_counter]
    exact supplier_peak w j i hj hi

end ComplexityTests.TreeEvalQueryGate
