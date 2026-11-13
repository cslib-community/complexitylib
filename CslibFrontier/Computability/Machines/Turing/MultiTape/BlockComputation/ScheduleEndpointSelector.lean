/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.UnaryDispatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelOnWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelNormalForm

/-!
# Runtime work-head and port selectors

`decode` accepts exactly the selectors below `3*k`, preserving the linear index `3*h+d` for
finite native dispatch. The finite-support compiler reads canonical binary selectors and emits
a bounded unary tag in constant time for each fixed tape count. It can reject an arbitrarily
long selector after a prefix that already rules out all valid choices.

`exists_prepare` places this tag on a work tape while preserving the original binary selector
and previous output and restoring every head. `UnaryDispatch.machine` then enters the selected
finite native continuation with constant overhead. These operations do not inspect a schedule
or decide whether a requested interval exists.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointSelector

/-- The runtime linear selector is valid exactly below the fixed number of outgoing ports. -/
@[expose] def decode (k selector : ℕ) : Option (Fin (3 * k)) :=
  if h : selector < 3 * k then some ⟨selector, h⟩ else none

/-- Valid selectors retain their index; invalid selectors have no finite continuation index. -/
theorem decode_eq_some_iff (k selector : ℕ) (j : Fin (3 * k)) :
    decode k selector = some j ↔ selector = j.val := by
  simp only [decode]
  split_ifs with h
  · simp [Fin.ext_iff]
  · simp only [false_iff]
    intro he
    have := j.isLt
    omega

/-- The rejection case includes every out-of-range selector, regardless of its bit length. -/
theorem decode_eq_none_iff (k selector : ℕ) : decode k selector = none ↔ 3 * k ≤ selector := by
  simp [decode]

/-- Work-head component of the runtime linear selector. -/
@[expose] def head {k : ℕ} (j : Fin (3 * k)) : Fin k :=
  (j.cast (Nat.mul_comm 3 k)).divNat

/-- Outgoing-port component of the runtime linear selector. -/
@[expose] def port {k : ℕ} (j : Fin (3 * k)) : Fin 3 :=
  (j.cast (Nat.mul_comm 3 k)).modNat

/-- The native family components reconstruct the original linear selector. -/
theorem head_port {k : ℕ} (j : Fin (3 * k)) :
    3 * (head j).val + (port j).val = j.val := by
  simp [head, port, Nat.div_add_mod]

/-- The tag consumed by the finite native dispatcher: empty on rejection, otherwise selector+1
true bits. Its length is bounded by the fixed number of outgoing ports. -/
@[expose] def word (k selector : ℕ) : List Bool := UnaryDispatch.code (decode k selector)

/-- The selector tag has constant bounded length for each fixed machine tape count. -/
theorem length_word_le (k selector : ℕ) : (word k selector).length ≤ 3 * k :=
  UnaryDispatch.length_code_le _

/-- Constant-time native selector decoding, using the finite-support compiler with default
empty output. Canonical binary encodings are the input contract. -/
theorem computable_constant (k : ℕ) :
    ∃ c, ComputableInTimeAndSpace (word k) encNat encBits (fun _ => c) (fun _ => 0) := by
  refine ⟨_, computableInTimeAndSpace_almostConstTime (word k) (Finset.range (3 * k)) [] ?_⟩
  intro selector hs
  have h : ¬ selector < 3 * k := by simpa using hs
  simp [word, decode, h, UnaryDispatch.code]

/-- One finite native machine prepares a dispatch tag from a binary selector on a work tape.
It preserves the selector and old output and restores all heads. The constant depends on the
fixed tape count, never on the runtime selector value or width. -/
theorem exists_prepare (k : ℕ) :
    ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q)
      (source target : Fin K) (c : ℕ), source ≠ target ∧
      ∀ (input out : List Bool) (selector : ℕ),
      RunsBetween tm
        (tapesCfg input (Function.update (fun _ => []) source selector.bits) 0 0 out)
        (tapesCfg input
          (Function.update (Function.update (fun _ => []) source selector.bits)
            target (word k selector)) 0 0 out)
        c (K * (c + 1)) := by
  classical
  obtain ⟨c, tapes, Q, hQ, tm, htm⟩ := computable_constant k
  let normal := tidy false true tm
  let time := 2 * c + 2 * tapes + 4
  let clock := time + 3 * k + 6
  refine ⟨tapes + tapes + 1 + 2, _, inferInstance, normal.onWords true,
    Fin.natAdd (tapes + tapes + 1) 0, (Fin.last (tapes + tapes)).castAdd 2, clock,
    (Fin.castAdd_ne_natAdd _ _).symm, ?_⟩
  intro input out selector
  have ht := (htm selector).computesTidily_tidy Bool.false_ne_true
  have ht' := ht.onWords true
  obtain ⟨ws', emitted, ⟨hw, he⟩, hr⟩ := RunsBetween.of_transformsTapes
    (input := input) ht' (ws := Function.update (fun _ => [])
      (Fin.natAdd (tapes + tapes + 1) 0) selector.bits) rfl 0 out
  rw [hw, he, List.append_nil] at hr
  have hlen := length_word_le k selector
  have htime : 2 * c + 3 * 0 + 2 * tapes + 4 + (word k selector).length + 6 ≤ clock := by
    dsimp [clock, time]
    omega
  exact (RunsBetween.of_runFrom hr.1).mono htime
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right htime 1))

end Turing.MultiTapeTM.ScheduleEndpointSelector
