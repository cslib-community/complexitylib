/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.CircuitCounting
public import Complexity.Computability.Circuit.Boolean.Iteration.InputTime
public import Complexity.Computability.Circuit.Boolean.Iteration.ModulusCounter.Basic
public import Complexity.Computability.Circuit.Boolean.Iteration.Remainder
import Mathlib.Tactic.Linarith

/-!
# Modular-counter remainders, short-exponent circuits, and variable-time equivalence

Computing `ModulusCounter.power T` on `2 k` bits is equivalent up to `O(k)` gates to computing the
fixed-integer remainder `x ↦ T % x` on `k`-bit moduli (`ModulusCounter.remainder_of_power`,
`ModulusCounter.power_of_remainder`, `counter_powers_compute_remainders`). Likewise, variable-time
iteration of `counterStep k` for an `m`-bit input time is equivalent up to `O(k)` gates to `m`-bit
division remainder (`variable_time_counter_iff_remainder`).

Hardwiring `m` numerator bits into the streaming remainder circuit of `Remainder.lean` shows that
any exponent `T < 2 ^ m` has a power circuit of size at most `110 * (m + 1) * (k + 1)`
(`ModulusCounter.short_power_circuit`). Consequently, every hard power requires an exponent of
binary length `m = Ω(2 ^ k / k ^ 2)` (`ModulusCounter.hard_power_requires_long_exponent`,
`ModulusCounter.hard_power_exponent_capacity`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.remainder`: fixed-integer remainder on `k`-bit
  words.
* `Cslib.Circuits.Boolean.Iteration.counterInput`, `Cslib.Circuits.Boolean.Iteration.counterOutput`:
  input packing and state extraction for remainder reductions.
* `Cslib.Circuits.Boolean.Iteration.inputTimeRemainder`: two-input remainder on `m` numerator bits
  and `k` modulus bits.

## Main results

* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.remainder_of_power`,
  `Cslib.Circuits.Boolean.Iteration.ModulusCounter.power_of_remainder`,
  `Cslib.Circuits.Boolean.Iteration.counter_powers_compute_remainders`: equivalence between
  fixed-exponent counter powers and fixed-integer remainders.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.short_remainder_circuit`,
  `Cslib.Circuits.Boolean.Iteration.ModulusCounter.short_power_circuit`: linear-in-`m * k` circuits
  for exponents `T < 2 ^ m`.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.hard_power_requires_long_exponent`,
  `Cslib.Circuits.Boolean.Iteration.ModulusCounter.hard_power_exponent_capacity`: exponential lower
  bound on the binary length of hard exponents.
* `Cslib.Circuits.Boolean.Iteration.variable_time_counter_iff_remainder`: equivalence between
  variable-time counter iteration and two-input remainder.

## References

* Adapted from lean/Proofs/{CounterRemainders,ExponentLength}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.Circuits.Boolean

namespace ModulusCounter

variable {k : ℕ}

/-! ### Fixed-integer remainders and equivalence with counter powers -/

/-- Fixed-integer remainder `x ↦ T % x` on `k`-bit words, with `0` on modulus `0`. -/
def remainder (T : ℕ) (x : BitString k) : BitString k :=
  fun i => (BitVec.ofNat k (if (word x).toNat = 0 then 0 else T % (word x).toNat)).getLsbD i.val

/-- Packing `remainder T x` into a `BitVec k` gives `T % (word x).toNat` (or `0` when
`(word x).toNat = 0`). -/
theorem remainder_word (T : ℕ) (x : BitString k) :
    word (remainder T x) =
      BitVec.ofNat k (if (word x).toNat = 0 then 0 else T % (word x).toNat) := word_getLsbD _

/-- When `r` encodes `T % a.toNat` for positive `a`, `addResidue a b r` encodes
`advance a.toNat b.toNat T`. -/
theorem addResidue_spec (a b r : BitVec k) (T : ℕ)
    (hr : 0 < a.toNat → r.toNat = T % a.toNat) :
    addResidue a b r = BitVec.ofNat k (advance a.toNat b.toNat T) := by
  by_cases h : b.toNat < a.toNat
  · have ha : 0 < a.toNat := by omega
    have hrlt : r.toNat < a.toNat := by rw [hr ha]; exact Nat.mod_lt _ ha
    apply BitVec.eq_of_toNat_eq
    rw [toNat_addResidue a b r h hrlt, hr ha]
    simp only [advance, ha, h, and_self, ↓reduceIte, BitVec.toNat_ofNat, Nat.add_mod_mod,
      Nat.mod_eq_of_lt ((Nat.mod_lt _ ha).trans a.isLt)]
  · simp [addResidue, BitVec.ult, h, advance]

/-- A circuit for `power T` yields a circuit for `remainder T` with at most one extra gate. -/
theorem remainder_of_power (T : ℕ) (c : Circuit signature (k + k) (k + k))
    (hc : c.Computes interpretation (power T)) :
    ∃ out : Circuit signature k k,
      out.Computes interpretation (remainder T) ∧ out.size ≤ c.size + 1 := by
  let s := inputs k ∪ {fun _ : BitString k => false}
  let init := fun x : BitString k => pack (word x) (0 : BitVec k)
  have hi (i : Fin (k + k)) : (fun x => init x i) ∈ s := by
    induction i using Fin.addCases with
    | left i => simpa only [init, pack, Fin.append_left, getLsbD_word] using
        (show (fun x : BitString k => x i) ∈ s from Or.inl ⟨i, rfl⟩)
    | right i =>
      right
      funext x
      simp only [init, pack, Fin.append_right]
      simp
  have h := (Synthesis.const (s := inputs k) false).trans
    (Synthesis.circuit (I := interpretation) (s := s) c (fun i x => init x i) hi)
  have hout : wires (remainder (k := k) T) ⊆
      wires (fun x => c.eval interpretation (init x)) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨Fin.natAdd k i, ?_⟩
    funext x
    change c.eval interpretation (init x) (Fin.natAdd k i) = remainder T x i
    rw [hc (init x)]
    dsimp only [power, init]
    rw [leftWord_pack, rightWord_pack]
    rw [show (0 : BitVec k).toNat = 0 by simp]
    simp only [pack, Fin.append_right]
    by_cases hz : (word x).toNat = 0
    · simp only [advance, remainder, hz, lt_self_iff_false, and_self, ite_false, ite_true]
    · simp only [advance, remainder, hz, Nat.pos_of_ne_zero hz, and_self, ite_true, ite_false,
        Nat.zero_add]
  obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by nlinarith⟩

/-- A circuit for `remainder T` yields a circuit for `power T` with at most `100 * (k + 1)` extra
gates. -/
theorem power_of_remainder (T : ℕ) (c : Circuit signature k k)
    (hc : c.Computes interpretation (remainder T)) :
    ∃ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (power T) ∧ out.size ≤ c.size + 100 * (k + 1) := by
  let a := fun x : BitString (k + k) => leftWord x
  let b := fun x : BitString (k + k) => rightWord x
  let init := fun x : BitString (k + k) => fun i : Fin k => x (Fin.castAdd k i)
  let r := fun x => word (c.eval interpretation (init x))
  let s := inputs (k + k) ∪ wires (fun x => c.eval interpretation (init x))
  have ha : wordWires a ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [a, leftWord, getLsbD_word] using
      (show (fun x : BitString (k + k) => x (Fin.castAdd k i)) ∈ s from Or.inl ⟨_, rfl⟩)
  have hb : wordWires b ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [b, rightWord, getLsbD_word] using
      (show (fun x : BitString (k + k) => x (Fin.natAdd k i)) ∈ s from Or.inl ⟨_, rfl⟩)
  have hr : wordWires r ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [r, getLsbD_word] using
      (show (fun x => c.eval interpretation (init x) i) ∈ s from Or.inr ⟨i, rfl⟩)
  have hs := synthesis_addResidue s a b r ha hb hr
  have hcirc := Synthesis.circuit (I := interpretation)
    (s := inputs (k + k)) c (fun i x => init x i) (fun i => ⟨Fin.castAdd k i, rfl⟩)
  have h : Synthesis interpretation (inputs (k + k))
      (s ∪ wordWires (fun x => addResidue (a x) (b x) (r x))) (c.size + 100 * (k + 1)) := by
    simpa only [s, wires, Set.union_assoc, Nat.zero_add] using
      (Synthesis.of_subset (I := interpretation)
        (s := inputs (k + k)) (t := inputs (k + k)) Set.Subset.rfl).union (hcirc.comp hs)
  have hspec (x : BitString (k + k)) : addResidue (a x) (b x) (r x) =
      BitVec.ofNat k (advance (a x).toNat (b x).toNat T) := by
    apply addResidue_spec
    intro ha
    change (word (c.eval interpretation (init x))).toNat = _
    rw [hc (init x), remainder_word]
    simp only [show word (init x) = a x from rfl,
      Nat.ne_of_gt ha, ite_false, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ((Nat.mod_lt _ ha).trans (a x).isLt)]
  have hout : wires (power (k := k) T) ⊆
      s ∪ wordWires (fun x => addResidue (a x) (b x) (r x)) := by
    rintro _ ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i =>
      left
      simpa only [power, pack, Fin.append_left] using ha ⟨i, rfl⟩
    | right i =>
      right
      refine ⟨i, ?_⟩
      funext x
      simp only [hspec, power, pack, Fin.append_right, a, b]
  obtain ⟨out, ho, hsize⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by simpa only [Nat.zero_add] using hsize⟩

/-! ### Short-exponent upper bounds and exponent-length lower bounds -/

/-- Hardwiring `m` numerator bits into `bounded_modulus_remainder` and masking modulus zero gives a
circuit for `remainder T` of size linear in `m * (k + 1)`. -/
theorem short_remainder_circuit (k m T : ℕ) (hT : T < 2 ^ m) :
    ∃ out : Circuit signature k k,
      out.Computes interpretation (remainder T) ∧
      out.size ≤ m * (51 * (k + 1) + 4) + 10 * (k + 1) := by
  obtain ⟨rem, hrem, hsize⟩ := bounded_modulus_remainder m k
  let constants : Set (BooleanFunction k) := {fun _ => false, fun _ => true}
  let s := inputs k ∪ constants
  have hc (b : Bool) : (fun _ : BitString k => b) ∈ s := by cases b <;> simp [s, constants]
  let bits := fun i : Fin m => (BitVec.ofNat m T).getLsbD i.val
  let init := fun x : BitString k => Fin.append bits x
  let r := fun x => word (rem.eval interpretation (init x))
  have hi (i : Fin (m + k)) : (fun x => init x i) ∈ s := by
    induction i using Fin.addCases with
    | left i => simpa only [init, Fin.append_left] using hc (bits i)
    | right i => simpa only [init, Fin.append_right] using
        (show (fun x : BitString k => x i) ∈ s from Or.inl ⟨i, rfl⟩)
  have hr := Synthesis.circuit (I := interpretation) (s := s) rem (fun i x => init x i) hi
  have hz := Synthesis.word_eq_const (s := s) (fun x : BitString k => word x)
    (fun i => by simpa only [getLsbD_word] using
      (show (fun x : BitString k => x i) ∈ s from Or.inl ⟨i, rfl⟩)) 0
  let s1 := s ∪ (wires (fun x => rem.eval interpretation (init x)) ∪
    {fun x => decide (word x = (0 : BitVec k))})
  have hm := Synthesis.word_mux (s := s1) (fun _ => (0 : BitVec k)) r
    (fun x => decide (word x = (0 : BitVec k))) (Or.inr (Or.inr rfl))
    (fun _ => Or.inl (hc _)) (fun i => by
      simpa only [r, getLsbD_word] using
        (show (fun x => rem.eval interpretation (init x) i) ∈ s1 from
          Or.inr (Or.inl ⟨i, rfl⟩)))
  have hconst : Synthesis interpretation (inputs k) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have h := hconst.trans ((hr.union hz).trans hm)
  have hval (x : BitString k) :
      (if decide (word x = (0 : BitVec k)) then (0 : BitVec k) else r x) =
        word (remainder T x) := by
    rw [remainder_word]
    have hzero : word x = (0 : BitVec k) ↔ (word x).toNat = 0 := by
      rw [← BitVec.toNat_inj]
      simp
    simp only [decide_eq_true_eq, hzero]
    split_ifs with h0
    · simp
    · have hp : 0 < (word x).toNat := Nat.pos_of_ne_zero h0
      have hspec := hrem (init x)
      simp only [init, Fin.append_right, Fin.append_left, bits, word_getLsbD,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hT] at hspec
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.mod_lt _ hp).trans (word x).isLt)]
      exact hspec hp
  have hout : wires (remainder (k := k) T) ⊆
      wordWires (fun x => if decide (word x = (0 : BitVec k)) then 0 else r x) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨i, ?_⟩
    funext x
    simp only [hval, getLsbD_word]
  obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
  exact ⟨out, ho, by nlinarith⟩

/-- A fixed exponent `T < 2 ^ m` gives a circuit for `power T` of size at most
`110 * (m + 1) * (k + 1)`. -/
theorem short_power_circuit (k m T : ℕ) (hT : T < 2 ^ m) :
    ∃ out : Circuit signature (k + k) (k + k),
      out.Computes interpretation (power T) ∧
      out.size ≤ 110 * (m + 1) * (k + 1) := by
  obtain ⟨rem, hr, hs⟩ := short_remainder_circuit k m T hT
  obtain ⟨out, ho, hb⟩ := power_of_remainder T rem hr
  refine ⟨out, ho, ?_⟩
  have hm : 4 * m ≤ 4 * m * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-- Any exponent whose counter power requires more than `lowerBudget k` gates needs
`lowerBudget k < 110 * (m + 1) * (k + 1)`. -/
theorem hard_power_requires_long_exponent (k m T : ℕ) (hT : T < 2 ^ m)
    (hard : ∀ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (power T) → lowerBudget k < c.size) :
    lowerBudget k < 110 * (m + 1) * (k + 1) := by
  obtain ⟨out, ho, hs⟩ := short_power_circuit k m T hT
  exact (hard out ho).trans_le hs

/-- Explicit exponential lower bound on the binary length `m` of any hard exponent `T < 2 ^ m`. -/
theorem hard_power_exponent_capacity (k m T : ℕ) (hT : T < 2 ^ m)
    (hard : ∀ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (power T) → lowerBudget k < c.size) :
    2 ^ k < 112640 * (m + 1) * (k + 1) ^ 2 := by
  have h := hard_power_requires_long_exponent k m T hT hard
  change 2 ^ k / (1024 * (k + 1)) < _ at h
  have hn := (Nat.div_lt_iff_lt_mul (by positivity : 0 < 1024 * (k + 1))).mp h
  nlinarith

end ModulusCounter

/-! ### Remainder helpers and variable-time equivalence -/

variable {k : ℕ}

/-- Pack a `k`-bit modulus `x` with initial counter state `0`. -/
def counterInput (x : BitString k) : BitString (k + k) :=
  ModulusCounter.pack (word x) 0

/-- Extract the `k`-bit counter state from a `2 k`-bit state. -/
def counterOutput (y : BitString (k + k)) : BitString k :=
  fun i => y (Fin.natAdd k i)

/-- The modulus word of `counterInput x` has natural value `(word x).toNat`. -/
@[simp] theorem counterInput_modulus_toNat (x : BitString k) :
    (ModulusCounter.leftWord (counterInput x)).toNat = (word x).toNat := by
  simp [counterInput]

/-- The initial counter state word of `counterInput x` has natural value `0`. -/
@[simp] theorem counterInput_state_toNat (x : BitString k) :
    (ModulusCounter.rightWord (counterInput x)).toNat = 0 := by
  simp [counterInput]

private theorem counterRemainder_spec (T : ℕ) (x : BitString k) :
    counterOutput ((counterStep k)^[T] (counterInput x)) = ModulusCounter.remainder T x := by
  rw [counterStep, ModulusCounter.iterate_power]
  funext i
  dsimp only [counterOutput, counterInput, ModulusCounter.power]
  rw [ModulusCounter.leftWord_pack, ModulusCounter.rightWord_pack]
  simp only [ModulusCounter.pack, Fin.append_right]
  by_cases hz : (word x).toNat = 0
  · simp [ModulusCounter.advance, ModulusCounter.remainder, hz]
  · simp [ModulusCounter.advance, ModulusCounter.remainder, hz,
      Nat.pos_of_ne_zero hz]

/-- Computing `ModulusCounter.power T` and computing `ModulusCounter.remainder T` are equivalent up
to linear additive overhead. -/
theorem counter_powers_compute_remainders (k T : ℕ) :
    (∀ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (ModulusCounter.power T) →
      ∃ out : Circuit signature k k,
        out.Computes interpretation (ModulusCounter.remainder T) ∧ out.size ≤ c.size + 1) ∧
    (∀ c : Circuit signature k k,
      c.Computes interpretation (ModulusCounter.remainder T) →
      ∃ out : Circuit signature (k + k) (k + k),
        out.Computes interpretation (ModulusCounter.power T) ∧
          out.size ≤ c.size + 100 * (k + 1)) :=
  ⟨ModulusCounter.remainder_of_power T, ModulusCounter.power_of_remainder T⟩

/-- Two-input remainder function on `m` numerator bits followed by `k` modulus bits, returning `0`
when the modulus is `0`. -/
def inputTimeRemainder (m k : ℕ) (x : BitString (m + k)) : BitString k :=
  ModulusCounter.remainder
    (word fun j : Fin m => x (Fin.castAdd k j)).toNat
    (fun i : Fin k => x (Fin.natAdd m i))

/-- Variable-time iteration of `counterStep k` for an `m`-bit input time is equivalent up to
`O(k)` gates to computing the `m`-bit remainder `inputTimeRemainder m k`. -/
theorem variable_time_counter_iff_remainder (m k : ℕ) :
    (∀ c : Circuit signature ((k + k) + m) (k + k),
      c.Computes interpretation (inputTimeIterate (counterStep k) m) →
      ∃ out : Circuit signature (m + k) k,
        out.Computes interpretation (inputTimeRemainder m k) ∧ out.size ≤ c.size + 1) ∧
    (∀ c : Circuit signature (m + k) k,
      c.Computes interpretation (inputTimeRemainder m k) →
      ∃ out : Circuit signature ((k + k) + m) (k + k),
        out.Computes interpretation (inputTimeIterate (counterStep k) m) ∧
          out.size ≤ c.size + 100 * (k + 1)) := by
  constructor
  · intro c hc
    let s := inputs (m + k) ∪ {fun _ : BitString (m + k) => false}
    let init := fun x : BitString (m + k) =>
      Fin.append (counterInput fun i : Fin k => x (Fin.natAdd m i))
        (fun j : Fin m => x (Fin.castAdd k j))
    have hi (i : Fin ((k + k) + m)) : (fun x => init x i) ∈ s := by
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i =>
          simpa only [init, Fin.append_left, counterInput, ModulusCounter.pack, getLsbD_word] using
            (show (fun x : BitString (m + k) => x (Fin.natAdd m i)) ∈ s from Or.inl ⟨_, rfl⟩)
        | right i =>
          right
          funext x
          simp only [init, Fin.append_left, counterInput, ModulusCounter.pack, Fin.append_right]
          simp
      | right j =>
        simpa only [init, Fin.append_right] using
          (show (fun x : BitString (m + k) => x (Fin.castAdd k j)) ∈ s from Or.inl ⟨_, rfl⟩)
    have h := (Synthesis.const (s := inputs (m + k)) false).trans
      (Synthesis.circuit (I := interpretation) (s := s) c (fun i x => init x i) hi)
    have hout : wires (inputTimeRemainder m k) ⊆
        wires (fun x => c.eval interpretation (init x)) := by
      rintro _ ⟨i, rfl⟩
      refine ⟨Fin.natAdd k i, ?_⟩
      funext x
      change c.eval interpretation (init x) (Fin.natAdd k i) =
        inputTimeRemainder m k x i
      rw [hc (init x)]
      simp only [inputTimeIterate, init, Fin.append_right, Fin.append_left]
      exact congrFun (counterRemainder_spec
        (word fun j : Fin m => x (Fin.castAdd k j)).toNat
        (fun i : Fin k => x (Fin.natAdd m i))) i
    obtain ⟨out, ho, hs⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
    exact ⟨out, ho, by omega⟩
  · intro c hc
    let a := fun x : BitString ((k + k) + m) =>
      ModulusCounter.leftWord fun i => x (Fin.castAdd m i)
    let b := fun x : BitString ((k + k) + m) =>
      ModulusCounter.rightWord fun i => x (Fin.castAdd m i)
    let init := fun x : BitString ((k + k) + m) =>
      Fin.append (fun j : Fin m => x (Fin.natAdd (k + k) j))
        (fun i : Fin k => x (Fin.castAdd m (Fin.castAdd k i)))
    let r := fun x => word (c.eval interpretation (init x))
    let s := inputs ((k + k) + m) ∪ wires (fun x => c.eval interpretation (init x))
    have ha : wordWires a ⊆ s := by
      rintro _ ⟨i, rfl⟩
      simpa only [a, ModulusCounter.leftWord, getLsbD_word] using
        (show (fun x : BitString ((k + k) + m) => x (Fin.castAdd m (Fin.castAdd k i))) ∈ s from
          Or.inl ⟨_, rfl⟩)
    have hb : wordWires b ⊆ s := by
      rintro _ ⟨i, rfl⟩
      simpa only [b, ModulusCounter.rightWord, getLsbD_word] using
        (show (fun x : BitString ((k + k) + m) => x (Fin.castAdd m (Fin.natAdd k i))) ∈ s from
          Or.inl ⟨_, rfl⟩)
    have hr : wordWires r ⊆ s := by
      rintro _ ⟨i, rfl⟩
      simpa only [r, getLsbD_word] using
        (show (fun x => c.eval interpretation (init x) i) ∈ s from Or.inr ⟨i, rfl⟩)
    have hs := synthesis_addResidue s a b r ha hb hr
    have hhi (i : Fin (m + k)) : (fun x => init x i) ∈ inputs ((k + k) + m) := by
      induction i using Fin.addCases with
      | left j =>
        exact ⟨Fin.natAdd (k + k) j, funext fun x => by simp [init]⟩
      | right i =>
        exact ⟨Fin.castAdd m (Fin.castAdd k i), funext fun x => by simp [init]⟩
    have hcirc := Synthesis.circuit (I := interpretation)
      (s := inputs ((k + k) + m)) c (fun i x => init x i) hhi
    have h : Synthesis interpretation (inputs ((k + k) + m))
        (s ∪ wordWires (fun x => addResidue (a x) (b x) (r x)))
        (c.size + 100 * (k + 1)) := by
      simpa only [s, wires, Set.union_assoc, Nat.zero_add] using
        (Synthesis.of_subset (I := interpretation)
          (s := inputs ((k + k) + m)) (t := inputs ((k + k) + m)) Set.Subset.rfl).union
          (hcirc.comp hs)
    have hspec (x : BitString ((k + k) + m)) :
        addResidue (a x) (b x) (r x) =
          BitVec.ofNat k (ModulusCounter.advance (a x).toNat (b x).toNat
            (word fun j : Fin m => x (Fin.natAdd (k + k) j)).toNat) := by
      apply ModulusCounter.addResidue_spec
      intro hpos
      change (word (c.eval interpretation (init x))).toNat = _
      rw [hc (init x), inputTimeRemainder, ModulusCounter.remainder_word]
      have hinit_m : (fun j : Fin m => init x (Fin.castAdd k j)) =
          fun j : Fin m => x (Fin.natAdd (k + k) j) := by
        funext j; simp [init]
      have hinit_k : word (fun i : Fin k => init x (Fin.natAdd m i)) = a x := by
        congr 1; funext i; simp [init]
      rw [hinit_m, hinit_k]
      simp only [Nat.ne_of_gt hpos, ite_false, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt ((Nat.mod_lt _ hpos).trans (a x).isLt)]
    have hout : wires (inputTimeIterate (counterStep k) m) ⊆
        s ∪ wordWires (fun x => addResidue (a x) (b x) (r x)) := by
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i =>
        left
        simpa only [inputTimeIterate, counterStep, ModulusCounter.iterate_power,
          ModulusCounter.power, ModulusCounter.pack, Fin.append_left] using ha ⟨i, rfl⟩
      | right i =>
        right
        refine ⟨i, ?_⟩
        funext x
        simp only [hspec, inputTimeIterate, counterStep, ModulusCounter.iterate_power,
          ModulusCounter.power, ModulusCounter.pack, Fin.append_right, a, b]
    obtain ⟨out, ho, hsize⟩ := (h.mono Set.Subset.rfl hout le_rfl).exists_circuit_outputs
    exact ⟨out, ho, by simpa only [Nat.zero_add] using hsize⟩

end Cslib.Circuits.Boolean.Iteration
