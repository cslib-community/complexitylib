/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation
public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Space
import CslibFrontier.Computability.Complexity.Classes.EXP.Padding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.Marking
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Alternating space: `APSPACE` and `AL`

The class `Cslib.Complexity.APSPACE` consists of the problems decided within polynomial space by
alternating machines (`Turing.MultiTapeATM`) with a binary alphabet and finitely many states, and
`Cslib.Complexity.AL` of those decided within logarithmic space `c * (log₂ n + 1)`
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]. Deciding within space (`Turing.MultiTapeATM.DecidesInSpace`)
bounds the space of every computation path of the nondeterministic machine of the table, and asks
every branch to halt. Like `Cslib.Complexity.AP`, the classes are relative to the encoding of
instances. A time bound gives a space bound
(`Turing.MultiTapeATM.DecidesInTime.decidesInSpace`), so `AP ⊆ APSPACE`, and `AL ⊆ APSPACE`.
In terms of the parametric classes `Cslib.Complexity.ASPACE`, `APSPACE` is the union of the
classes `ASPACE (n ^ k)` (`Cslib.Complexity.mem_APSPACE_iff_exists_mem_ASPACE`) and `AL` is
`ASPACE (log₂ n)` (`Cslib.Complexity.AL_eq_ASPACE`).

A space-bounded alternating machine is simulated deterministically by evaluating its configuration
graph bottom-up (`Turing.MultiTapeATM.boundedAccepts`). Under space `s`, at most
`2 ^ (2 * coreLengthBound k State n s + 1) = 2 ^ O(log n + s)` views are reachable, and marking
them decides acceptance. Acceptance (`Turing.MultiTapeATM.Accepts`) is the least fixed point of the
labelling, acceptance within some finite number of moves, so an infinite branch never helps a
configuration accept. The marking rounds compute exactly this least fixed point
(`Turing.MultiTapeATM.markAccepts_iff`), so the simulation needs no halting assumption, and it
applies to recognizers (`Turing.MultiTapeATM.RecognizesInSpace`), whose branches may run forever.
Under logarithmic space there are polynomially many views and the simulation is polynomial-time
(`Turing.MultiTapeATM.RecognizesInSpace.mem_P`). Under polynomial space it is polynomial-time in
the instance padded by the exponential number of views, so in exponential time
(`Turing.MultiTapeATM.RecognizesInSpace.mem_EXP`). Hence `AL ⊆ P` and `APSPACE ⊆ EXP`, the
simulation halves of `AL = P` and `APSPACE = EXP`.

## Main definitions

* `Cslib.Complexity.APSPACE`: alternating polynomial space.
* `Cslib.Complexity.AL`: alternating logarithmic space.

## Main results

* `Cslib.Complexity.mem_APSPACE_iff_exists_mem_ASPACE`: `APSPACE` is the union of the classes
  `ASPACE (n ^ k)`.
* `Cslib.Complexity.AL_eq_ASPACE`: `AL` is `ASPACE (log₂ n)`.
* `Cslib.Complexity.AP_subset_APSPACE`, `Cslib.Complexity.AL_subset_APSPACE`: alternating
  polynomial time and logarithmic space are within alternating polynomial space.
* `Turing.MultiTapeATM.RecognizesInSpace.mem_P`: alternating logspace recognizers are within
  polynomial time.
* `Turing.MultiTapeATM.RecognizesInSpace.mem_EXP`: alternating polynomial-space recognizers are
  within exponential time.
* `Cslib.Complexity.AL_subset_P`: `AL ⊆ P`.
* `Cslib.Complexity.APSPACE_subset_EXP`: `APSPACE ⊆ EXP`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*,
  Section 3][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 10.3][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Alternating polynomial space** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: the problems decided within polynomial space by an alternating
machine with a binary alphabet and finitely many states, with respect to the encoding `enc` of
instances. -/
def APSPACE (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (atm : MultiTapeATM k Bool State) (s : α → ℕ),
    PolyBounded (fun a => (enc a).length) s ∧ atm.DecidesInSpace enc A s}

/-- **Alternating logarithmic space** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: the problems decided within space `c * (log₂ n + 1)`, where `n`
is the length of the encoded instance, by an alternating machine with a binary alphabet and
finitely many states. -/
def AL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (atm : MultiTapeATM k Bool State) (c : ℕ),
    atm.DecidesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)}

/-- **`APSPACE` is the union of the classes `ASPACE (n ^ k)`** [Chandra, Kozen and Stockmeyer,
Section 3][ChandraKozenStockmeyer1981] [Sipser, Section 10.3][Sipser2013]. -/
theorem mem_APSPACE_iff_exists_mem_ASPACE {A : Set α} :
    A ∈ APSPACE enc ↔ ∃ k, A ∈ ASPACE enc (· ^ k) := by
  constructor
  · rintro ⟨k, State, hfin, atm, s, hs, hA⟩
    obtain ⟨c, d, hle⟩ := hs.exists_le
    exact ⟨d, k, State, hfin, atm, c * 2 ^ d, c,
      hA.mono fun a => (hle a).trans (Nat.mul_add_one_pow_le_two_pow c d _)⟩
  · rintro ⟨d, k, State, hfin, atm, c₁, c₂, hA⟩
    exact ⟨k, State, hfin, atm, _, by growth_poly, hA⟩

/-- **`AL` is `ASPACE(log₂ n)`** [Sipser, Section 10.3][Sipser2013]: the bounds `c * (log₂ n + 1)`
and `c₁ * log₂ n + c₂` give the same problems. -/
theorem AL_eq_ASPACE : AL enc = ASPACE enc Nat.log2 := by
  ext A
  constructor
  · rintro ⟨k, State, hfin, atm, c, hA⟩
    exact ⟨k, State, hfin, atm, c, c, hA.mono fun a => by rw [Nat.mul_add, Nat.mul_one]⟩
  · rintro ⟨k, State, hfin, atm, c₁, c₂, hA⟩
    exact ⟨k, State, hfin, atm, c₁ + c₂, hA.mono fun a => by nlinarith⟩

/-- **Alternating polynomial time is within alternating polynomial space**: a decider within time
`t` decides within space `k * (t + 1)`. -/
theorem AP_subset_APSPACE : AP enc ⊆ APSPACE enc := by
  rintro A ⟨t, ht, k, State, _, atm, h⟩
  exact ⟨k, State, inferInstance, atm, _, (PolyBounded.const k).mul (ht.add (.const 1)),
    h.decidesInSpace⟩

/-- **Alternating logarithmic space is within alternating polynomial space.** -/
theorem AL_subset_APSPACE : AL enc ⊆ APSPACE enc := by
  rintro A ⟨k, State, _, atm, c, h⟩
  exact ⟨k, State, inferInstance, atm, _, polyBounded_log (fun a => (enc a).length) c, h⟩

end Cslib.Complexity

namespace Turing.MultiTapeATM

open MultiTapeTM Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {k : ℕ} {State : Type} [Finite State]
  {atm : MultiTapeATM k Bool State} {A : Set α}

/-- **Alternating logspace recognizers are within polynomial time**
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]: a problem recognized by
an alternating machine within logarithmic space, whose branches need not halt, is in `P`, by
marking the polynomially many reachable views. This is the alternating analogue of
`Cslib.Complexity.mem_P_of_recognizesInSpace`. The bound must have the shape
`c * (Nat.log2 n + 1)`; a smaller bound is first raised with `RecognizesInSpace.mono`. -/
theorem RecognizesInSpace.mem_P {c : ℕ}
    (h : atm.RecognizesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1)) :
    A ∈ P enc := by
  -- the number of reachable views is at most `N a`, a polynomial
  set D := 2 * (8 + 2 * Nat.card (Option State) + 200 * k) * (c + 1)
  set N : α → ℕ := fun a => polyClock D (enc a).length
  have hN : ComputableInPolyTime N enc encUnary := by
    simp only [N, polyClock]
    fun_prop
  have hΨ := (computableInPolyTime_boundedAccepts (fun a => (h a).1)
    (polyBounded_log (fun a => (enc a).length) c)).comp (ComputableInPolyTime.id'.prod hN)
  refine ⟨_, hΨ, fun a => (h a).2.trans ?_⟩
  exact (boundedAccepts_iff (h a).1
    (MultiTapeNTM.two_pow_coreLengthBound_log_le k State c _)).symm

/-- **Alternating polynomial-space recognizers are within exponential time**
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]: a problem recognized by
an alternating machine within polynomial space, whose branches need not halt, is in `EXP`, by
marking the exponentially many reachable views. -/
theorem RecognizesInSpace.mem_EXP {s : α → ℕ} (hs : PolyBounded (fun a => (enc a).length) s)
    (h : atm.RecognizesInSpace enc A s) : A ∈ EXP enc := by
  obtain ⟨c, d, hcd⟩ := hs.exists_le
  -- the number of reachable views is at most `2 ^ L a`, with `L` a polynomial
  set B := 8 + 2 * Nat.card (Option State) + 200 * k
  set L : α → ℕ := fun a => 2 * B * (c + 2) * ((enc a).length + 1) ^ (d + 1) + 1
  have hL : ComputableInPolyTime L enc encUnary := by
    simp only [L]
    fun_prop
  have hbound (a : α) :
      2 ^ (2 * MultiTapeNTM.coreLengthBound k State (enc a).length (s a) + 1) ≤ 2 ^ L a := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have hlog := Nat.log2_le_self (enc a).length
    have hsa := hcd a
    have hpow : (enc a).length + 1 ≤ ((enc a).length + 1) ^ (d + 1) :=
      Nat.le_self_pow (by omega) _
    have hpow' : ((enc a).length + 1) ^ d ≤ ((enc a).length + 1) ^ (d + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hX : Nat.log2 (enc a).length + s a + 1 ≤ (c + 2) * ((enc a).length + 1) ^ (d + 1) := by
      nlinarith
    calc 2 * MultiTapeNTM.coreLengthBound k State (enc a).length (s a) + 1
        = 2 * (B * (Nat.log2 (enc a).length + s a + 1)) + 1 := rfl
      _ ≤ 2 * (B * ((c + 2) * ((enc a).length + 1) ^ (d + 1))) + 1 := by gcongr
      _ = L a := by simp only [L]; ring
  have hA : A = {a | atm.boundedAccepts (enc a) (2 ^ L a) = true} := by
    ext a
    exact (h a).2.trans (boundedAccepts_iff (h a).1 (hbound a)).symm
  rw [hA]
  exact setOf_mem_EXP_of_computableInPolyTime_pad
    (computableInPolyTime_boundedAccepts (fun a => (h a).1) hs) hL

end Turing.MultiTapeATM

namespace Cslib.Complexity

open _root_.Turing

variable {α : Type} {enc : α ↪ List Bool}

/-- **`AL ⊆ P`** [Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: alternating logarithmic space is within polynomial time. -/
theorem AL_subset_P : AL enc ⊆ P enc := by
  rintro A ⟨k, State, _, atm, c, h⟩
  exact h.recognizesInSpace.mem_P

/-- **`APSPACE ⊆ EXP`** [Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: alternating polynomial space is within exponential time. -/
theorem APSPACE_subset_EXP : APSPACE enc ⊆ EXP enc := by
  rintro A ⟨k, State, _, atm, s, hs, h⟩
  exact h.recognizesInSpace.mem_EXP hs

end Cslib.Complexity
