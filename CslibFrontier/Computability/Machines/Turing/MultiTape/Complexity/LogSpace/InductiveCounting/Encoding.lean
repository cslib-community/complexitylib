/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.InductiveCounting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Binary storage for the inductive-counting controller

The controller stores ten binary natural registers, a finite instruction label and two bits.
The choice history used in its semantic proofs is absent from the encoding.

## Main definitions

* `Turing.InductiveCounting.encState`: the fixed encoding of a controller state.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

@[expose] public section

namespace Turing.InductiveCounting

open MultiTapeTM Cslib.InductiveCounting

/-- Fixed labels for the controller's finite phases. -/
def phaseCode : Phase → ℕ
  | .round => 0
  | .target => 1
  | .candidate => 2
  | .walk => 3
  | .guess => 4
  | .edge => 5
  | .observe => 6
  | .done => 7
  | .accept => 8
  | .reject => 9

theorem phaseCode_injective : Function.Injective phaseCode := by
  intro p q h
  cases p <;> cases q <;> simp_all [phaseCode]

/-- Only ten binary registers are stored; there is no stored walk or round list. -/
def registers (s : State) : List ℕ :=
  [s.round, s.count, s.target, s.nextCount, s.candidate, s.selected, s.remaining,
    s.current, s.guess, s.bits]

/-- The fixed data represented by a controller state. -/
def stateData (s : State) : ℕ × List ℕ × Bool × Bool :=
  (phaseCode s.phase, registers s, s.hit, s.finalScan)

theorem stateData_injective : Function.Injective stateData := by
  intro s t h
  cases s
  cases t
  simp only [stateData, registers, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨hp, ⟨hr, hc, ht, hn, hu, hd, hk, hv, hg, hb⟩, hh, hf⟩ := h
  have hp' := phaseCode_injective hp
  cases hp'
  cases hr
  cases hc
  cases ht
  cases hn
  cases hu
  cases hd
  cases hk
  cases hv
  cases hg
  cases hb
  cases hh
  cases hf
  rfl

/-- The encoded finite phase, binary registers and flags. -/
def encState : State ↪ List Bool :=
  ⟨fun s => encPair encNat (encPair (encList encNat) (encPair encBool encBool)) (stateData s),
    fun _ _ h => stateData_injective
      ((encPair encNat (encPair (encList encNat) (encPair encBool encBool))).injective h)⟩

@[simp] theorem length_registers (s : State) : (registers s).length = 10 := rfl

theorem mem_registers_lt {N width : ℕ} {s : State} (h : Bounded N width s) :
    ∀ r ∈ registers s, r < registerBound N width := by
  rcases h with ⟨hr, hc, ht, hn, hu, hd, hk, hv, hg, hb⟩
  intro r hm
  simp only [registers, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- A uniform bit bound on each of the ten registers bounds the complete stored state. -/
theorem length_encState_le {s : State} {L : ℕ}
    (h : ∀ r ∈ registers s, (encNat r).length ≤ L) :
    (encState s).length ≤ 40 * (L + 1) := by
  have hphase : phaseCode s.phase ≤ 9 := by cases s.phase <;> decide
  have hlabel : (encNat (phaseCode s.phase)).length ≤ 4 :=
    (length_encNat_le_log2 hphase).trans (by decide)
  have hregs := length_encList_le encNat (registers s) h
  rw [length_registers] at hregs
  change (encPair encNat (encPair (encList encNat) (encPair encBool encBool))
    (stateData s)).length ≤ _
  simp only [stateData, length_encPair, encBool_apply, List.length_singleton]
  omega

/-- Every bounded controller state has logarithmic size in its register bound. -/
theorem length_encState_le_log {N width : ℕ} {s : State} (h : Bounded N width s) :
    (encState s).length ≤ 40 * (Nat.log2 (registerBound N width) + 2) :=
  length_encState_le fun r hr => length_encNat_le_log2 (mem_registers_lt h r hr).le

/-- Polynomial register bounds give native logarithmic-space storage, including on rejecting
branches. This estimate concerns the state alone, not a supplied choice history. -/
theorem length_encState_le_of_registerBound_le {N width n A D : ℕ} {s : State}
    (h : Bounded N width s) (hbound : registerBound N width ≤ A * (n + 1) ^ D) :
    (encState s).length ≤ 40 * (Nat.size A + 2 * D + 2) * (Nat.log2 n + 1) := by
  have hsize := length_encState_le fun r hr =>
    length_encNat_le_of_le_mul_pow ((mem_registers_lt h r hr).le.trans hbound)
  nlinarith [Nat.zero_le (Nat.log2 n)]

end Turing.InductiveCounting
