/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration.InputTime
public import Complexity.Computability.Circuit.Boolean.Iteration.ResidueAdd
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# The modular-counter permutation: state, period, and linear-size step circuit

On `2 k` bits split into a `k`-bit modulus `a` (`leftWord`) and a `k`-bit state `b` (`rightWord`),
`ModulusCounter.power T` advances `b` to `(b + T) % a` whenever `0 < a` and `b < a`, and fixes all
other states (`advance`). For `T = 1`, this defines a permutation `counterStep k =
ModulusCounter.power 1` computed by a native De Morgan circuit of linear size at most `50 * k + 20`
(`counterStep_circuit`, `ModulusCounter.exists_linear_circuit`).

Every active modulus `1 ≤ a ≤ 2 ^ k - 1` divides `ModulusCounter.period k = lcm(1, …, 2 ^ k - 1)`,
and distinct exponents below `ModulusCounter.period k` give distinct Boolean functions
(`ModulusCounter.powers_injective`, `counter_power_ne`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.advance`: advance `b` by `T` modulo `a` when
  `0 < a` and `b < a`.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.leftWord`,
  `Cslib.Circuits.Boolean.Iteration.ModulusCounter.rightWord`,
  `Cslib.Circuits.Boolean.Iteration.ModulusCounter.pack`: split and pack `k`-bit modulus and state
  words in `BitString (k + k)`.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.power`: `T`-step modular counter map on
  `BitString (k + k)`.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.period`: `Nat.lcmUpto (2 ^ k - 1)`.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.stepValue`: next counter word after one step.
* `Cslib.Circuits.Boolean.Iteration.counterModulus`,
  `Cslib.Circuits.Boolean.Iteration.counterStepValue`,
  `Cslib.Circuits.Boolean.Iteration.counterStep`,
  `Cslib.Circuits.Boolean.Iteration.counterNextBits`: top-level single-step modular counter
  permutation and helpers.

## Main results

* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.power_bijective`: the single-step counter map is
  a bijection.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.powers_injective`: powers below `period k` are
  pairwise distinct.
* `Cslib.Circuits.Boolean.Iteration.ModulusCounter.exists_linear_circuit`,
  `Cslib.Circuits.Boolean.Iteration.counterStep_circuit`: `counterStep k` has a De Morgan circuit of
  size at most `50 * k + 20`.

## References

* Adapted from lean/Proofs/{ModulusCounter,CounterCircuit}.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.Circuits Cslib.Circuits.Boolean

namespace ModulusCounter

/-! ### Modular counter semantics and period -/

/-- Advance `b` by `T` modulo `a` when `0 < a` and `b < a`; inactive pairs are fixed. -/
def advance (a b T : ℕ) : ℕ := if 0 < a ∧ b < a then (b + T) % a else b

/-- Advancing by `0` steps leaves the state unchanged. -/
@[simp] theorem advance_zero (a b : ℕ) : advance a b 0 = b := by
  by_cases h : 0 < a ∧ b < a
  · simp [advance, h, Nat.mod_eq_of_lt h.2]
  · simp [advance, h]

/-- If both `a` and `b` are strictly below `U`, then `advance a b T` is strictly below `U`. -/
theorem advance_lt {a b U T : ℕ} (ha : a < U) (hb : b < U) : advance a b T < U := by
  unfold advance
  split_ifs with h
  · exact (Nat.mod_lt _ h.1).trans ha
  · exact hb

/-- Advancing by `S` steps and then by `T` steps is equivalent to advancing by `S + T` steps. -/
theorem advance_add (a b S T : ℕ) :
    advance a (advance a b S) T = advance a b (S + T) := by
  by_cases h : 0 < a ∧ b < a
  · simp only [advance, h, and_self, ite_true, Nat.mod_lt _ h.1]
    rw [Nat.mod_add_mod, Nat.add_assoc]
  · simp [advance, h]

variable {k : ℕ}

/-- The `k`-bit modulus word in the first `k` coordinates. -/
def leftWord (x : BitString (k + k)) : BitVec k := word fun i => x (Fin.castAdd k i)

/-- The `k`-bit counter state word in the last `k` coordinates. -/
def rightWord (x : BitString (k + k)) : BitVec k := word fun i => x (Fin.natAdd k i)

/-- Pack a `k`-bit modulus word and a `k`-bit counter state word into `BitString (k + k)`. -/
def pack (a b : BitVec k) : BitString (k + k) :=
  Fin.append (fun i : Fin k => a.getLsbD i.val) (fun i : Fin k => b.getLsbD i.val)

/-- Extracting the left word of `pack a b` recovers `a`. -/
@[simp] theorem leftWord_pack (a b : BitVec k) : leftWord (pack a b) = a := by
  simp only [leftWord, pack, Fin.append_left, word_getLsbD]

/-- Extracting the right word of `pack a b` recovers `b`. -/
@[simp] theorem rightWord_pack (a b : BitVec k) : rightWord (pack a b) = b := by
  simp only [rightWord, pack, Fin.append_right, word_getLsbD]

/-- Repacking the left and right words of `x` recovers `x`. -/
@[simp] theorem pack_words (x : BitString (k + k)) : pack (leftWord x) (rightWord x) = x := by
  funext bit
  induction bit using Fin.addCases with
  | left i => simp only [pack, leftWord, Fin.append_left, getLsbD_word]
  | right i => simp only [pack, rightWord, Fin.append_right, getLsbD_word]

/-- The `T`-step modular counter map on `BitString (k + k)`. -/
def power (T : ℕ) (x : BitString (k + k)) : BitString (k + k) :=
  pack (leftWord x) (BitVec.ofNat k (advance (leftWord x).toNat (rightWord x).toNat T))

/-- The `0`-step counter map is the identity. -/
@[simp] theorem power_zero (x : BitString (k + k)) : power 0 x = x := by
  simp [power]

/-- Composing `power S` with `power T` yields `power (S + T)`. -/
theorem power_add (S T : ℕ) (x : BitString (k + k)) :
    power T (power S x) = power (S + T) x := by
  simp only [power, leftWord_pack, rightWord_pack, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (advance_lt (BitVec.isLt _) (BitVec.isLt _)), advance_add]

/-- Iterating the single-step counter map `power 1` for `T` steps yields `power T`. -/
theorem iterate_power (T : ℕ) : (power (k := k) 1)^[T] = power T := by
  funext x
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Function.iterate_succ_apply', ih, power_add]

/-- The order `lcm(1, …, 2 ^ k - 1)` common to every active `k`-bit modular counter. -/
def period (k : ℕ) : ℕ := Nat.lcmUpto (2 ^ k - 1)

private theorem modulus_dvd_period {a : ℕ} (ha : 0 < a) (haU : a < 2 ^ k) : a ∣ period k := by
  change a ∣ (Finset.Icc 1 (2 ^ k - 1)).lcm id
  apply Finset.dvd_lcm
  simpa only [Finset.mem_Icc] using (show 1 ≤ a ∧ a ≤ 2 ^ k - 1 by omega)

private theorem power_period (x : BitString (k + k)) : power (period k) x = x := by
  unfold power advance
  split_ifs with h
  · have hd := modulus_dvd_period h.1 (BitVec.isLt (leftWord x))
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, Nat.add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt h.2]
    simp
  · simp

/-- The single-step modular counter map `power 1` is a bijection on `BitString (k + k)`. -/
theorem power_bijective : Function.Bijective (power (k := k) 1) := by
  have hpos : 0 < period k := Nat.lcmUpto_pos _
  constructor
  · intro x y he
    have h := congrArg (power (period k - 1)) he
    simpa only [power_add, show 1 + (period k - 1) = period k by omega, power_period] using h
  · intro y
    exact ⟨power (period k - 1) y, by
      rw [power_add, Nat.sub_add_cancel hpos, power_period]⟩

/-- Different residues modulo `period k` give different Boolean functions. -/
theorem powers_injective :
    Function.Injective (fun T : Fin (period k) => power (k := k) T.val) := by
  intro S T he
  have hmod (a : ℕ) (ha : 0 < a) (haU : a < 2 ^ k) : S.val % a = T.val % a := by
    have hx := congrArg (fun f => (rightWord (f
      (pack (BitVec.ofNat k a) (BitVec.ofNat k 0)))).toNat) he
    have hslt := (Nat.mod_lt S.val ha).trans haU
    have htlt := (Nat.mod_lt T.val ha).trans haU
    simpa [power, advance, Nat.mod_eq_of_lt haU, ha, Nat.mod_eq_of_lt hslt,
      Nat.mod_eq_of_lt htlt] using hx
  have helper (S T : ℕ) (hST : S ≤ T)
      (hmod : ∀ a, 0 < a → a < 2 ^ k → S % a = T % a) : period k ∣ T - S := by
    change (Finset.Icc 1 (2 ^ k - 1)).lcm id ∣ T - S
    apply Finset.lcm_dvd
    intro a ha
    have ha' : 1 ≤ a ∧ a ≤ 2 ^ k - 1 := Finset.mem_Icc.mp ha
    have hm : Nat.ModEq a S T := hmod a (by omega) (by have := Nat.one_le_two_pow (n := k); omega)
    exact (Nat.modEq_iff_dvd' hST).mp hm
  apply Fin.ext
  rcases le_total S.val T.val with h | h
  · have hd := helper S.val T.val h hmod
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by have := T.isLt; omega)
    omega
  · have hd := helper T.val S.val h (fun a ha hU => (hmod a ha hU).symm)
    have hz := Nat.eq_zero_of_dvd_of_lt hd (by have := S.isLt; omega)
    omega

/-! ### Linear-size step circuit -/

/-- Next counter word after one step: increment `b` modulo `a` when `b < a`. -/
def stepValue (a b : BitVec k) : BitVec k :=
  if b.ult a then if b + 1 = a then 0 else b + 1 else b

/-- `stepValue a b` encodes `advance a.toNat b.toNat 1` as a `k`-bit vector. -/
theorem stepValue_spec (a b : BitVec k) :
    stepValue a b = BitVec.ofNat k (advance a.toNat b.toNat 1) := by
  by_cases h : b.toNat < a.toNat
  · have ha : 0 < a.toNat := by omega
    have hs : b.toNat + 1 < 2 ^ k := by have := a.isLt; omega
    have hn : 1 < 2 ^ k := by have := a.isLt; omega
    have hsum : (b + 1).toNat = b.toNat + 1 := by
      simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hs]
    have he : b + 1 = a ↔ b.toNat + 1 = a.toNat := by
      rw [← BitVec.toNat_inj, hsum]
    simp only [stepValue, BitVec.ult, decide_eq_true_eq, h, ite_true, he, advance,
      ha, and_self]
    split_ifs with heq
    · apply BitVec.eq_of_toNat_eq
      simp [heq]
    · have hlt : b.toNat + 1 < a.toNat := by omega
      apply BitVec.eq_of_toNat_eq
      simp only [hsum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hs]
  · simp only [stepValue, BitVec.ult, decide_eq_true_eq, h, ite_false, advance,
      and_false]
    simp

/-- Equality of two available `k`-bit words costs at most `6 * k + 1` gates. -/
private theorem synthesis_word_eq {n : ℕ} (s : Set (BooleanFunction n))
    (a b : BitString n → BitVec k)
    (ha : ∀ i : Fin k, (fun x => (a x).getLsbD i.val) ∈ s)
    (hb : ∀ i : Fin k, (fun x => (b x).getLsbD i.val) ∈ s) :
    Synthesis interpretation s {fun x => decide (a x = b x)} (6 * k + 1) := by
  have h := synthesis_bits_eq s (fun x i => (a x).getLsbD i.val)
    (fun x i => (b x).getLsbD i.val)
    (by rintro _ ⟨i, rfl⟩; exact ha i) (by rintro _ ⟨i, rfl⟩; exact hb i)
  have heq (x : BitString n) :
      ((fun i : Fin k => (a x).getLsbD i.val) = fun i : Fin k => (b x).getLsbD i.val) ↔
        a x = b x :=
    ⟨fun h => BitVec.eq_of_getLsbD_eq fun i hi => congrFun h ⟨i, hi⟩,
      fun h => funext fun i => congrArg (fun v => v.getLsbD i.val) h⟩
  simpa only [heq] using h

/-- Synthesizing `stepValue (a x) (b x)` from available words and constants costs at most
`50 * k + 18` gates. -/
theorem synthesis_stepValue {n : ℕ} (src : Set (BooleanFunction n))
    (a b : BitString n → BitVec k)
    (ha : ∀ i : Fin k, (fun x => (a x).getLsbD i.val) ∈ src)
    (hb : ∀ i : Fin k, (fun x => (b x).getLsbD i.val) ∈ src)
    (hc : ∀ v : Bool, (fun _ : BitString n => v) ∈ src) :
    Synthesis interpretation src (wordWires fun x => stepValue (a x) (b x))
      (50 * k + 18) := by
  let inc := fun x => b x + 1
  have hadd := Synthesis.word_add (s := src) b (fun _ => (1 : BitVec k)) hb (fun _ => hc _)
  let src1 := src ∪ wordWires inc
  have hi (i : Fin k) : (fun x => (inc x).getLsbD i.val) ∈ src1 := Or.inr ⟨i, rfl⟩
  let equal := fun x => decide (inc x = a x)
  let active := fun x => (b x).ult (a x)
  have heq := synthesis_word_eq src1 inc a hi (fun i => Or.inl (ha i))
  have hlt := Synthesis.word_ult (s := src1) b a (fun i => Or.inl (hb i)) (fun i => Or.inl (ha i))
  let src2 := src1 ∪ ({equal} ∪ {active})
  let next := fun x => if equal x then (0 : BitVec k) else inc x
  have hm := Synthesis.word_mux (s := src2) (fun _ => (0 : BitVec k)) inc equal
    (Or.inr (Or.inl rfl)) (fun _ => Or.inl (Or.inl (hc _))) (fun i => Or.inl (hi i))
  let src3 := src2 ∪ wordWires next
  have hm' := Synthesis.word_mux (s := src3) next b active
    (Or.inl (Or.inr (Or.inr rfl))) (fun i => Or.inr ⟨i, rfl⟩)
    (fun i => Or.inl (Or.inl (Or.inl (hb i))))
  have hout := hadd.trans ((heq.union hlt).trans (hm.trans hm'))
  refine hout.mono Set.Subset.rfl ?_ (by omega)
  rintro _ ⟨i, rfl⟩
  refine ⟨i, ?_⟩
  funext x
  simp only [stepValue, active, next, equal, inc, decide_eq_true_eq]

/-- The single-step modular counter `power 1` has a De Morgan circuit of size at most
`50 * k + 20`. -/
theorem exists_linear_circuit (k : ℕ) :
    ∃ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (power (k := k) 1) ∧ c.size ≤ 50 * k + 20 := by
  let a := fun x : BitString (k + k) => leftWord x
  let b := fun x : BitString (k + k) => rightWord x
  let constants : Set (BooleanFunction (k + k)) := {fun _ => false, fun _ => true}
  let src := inputs (k + k) ∪ constants
  have hc (v : Bool) : (fun _ : BitString (k + k) => v) ∈ src := by
    cases v <;> simp [src, constants]
  have ha (i : Fin k) : (fun x => (a x).getLsbD i.val) ∈ src := by
    simpa only [a, leftWord, getLsbD_word] using
      (show (fun x : BitString (k + k) => x (Fin.castAdd k i)) ∈ src from Or.inl ⟨_, rfl⟩)
  have hb (i : Fin k) : (fun x => (b x).getLsbD i.val) ∈ src := by
    simpa only [b, rightWord, getLsbD_word] using
      (show (fun x : BitString (k + k) => x (Fin.natAdd k i)) ∈ src from Or.inl ⟨_, rfl⟩)
  have hconst : Synthesis interpretation (inputs (k + k)) constants 2 :=
    (Synthesis.const false).union (Synthesis.const true)
  have hstep := synthesis_stepValue src a b ha hb hc
  have hout := hconst.trans hstep
  have hall := (Synthesis.of_subset (I := interpretation)
    (s := inputs (k + k)) (t := inputs (k + k)) Set.Subset.rfl).union hout
  have hs : Synthesis interpretation (inputs (k + k))
      (wires (power (k := k) 1)) (50 * k + 20) := by
    apply hall.mono Set.Subset.rfl ?_ (by omega)
    rintro _ ⟨bit, rfl⟩
    induction bit using Fin.addCases with
    | left i =>
      left
      exact ⟨Fin.castAdd k i, by
        funext x
        simp only [power, pack, Fin.append_left, leftWord, getLsbD_word]⟩
    | right i =>
      right
      refine ⟨i, ?_⟩
      funext x
      simp only [power, pack, Fin.append_right]
      rw [← stepValue_spec]
  exact hs.exists_circuit_outputs

end ModulusCounter

/-! ### Top-level counter definitions -/

variable {k : ℕ}

/-- The modulus as a natural number. -/
def counterModulus (x : BitString (k + k)) : ℕ := (ModulusCounter.leftWord x).toNat

/-- Single-step modular counter transition on natural numbers. -/
def counterStepValue (a b : ℕ) : ℕ := ModulusCounter.advance a b 1

/-- Single-step modular counter permutation on `BitString (k + k)`. -/
def counterStep (k : ℕ) : BitString (k + k) → BitString (k + k) :=
  ModulusCounter.power (k := k) 1

/-- Coordinate bits of
`ModulusCounter.stepValue (ModulusCounter.leftWord x) (ModulusCounter.rightWord x)`. -/
def counterNextBits (x : BitString (k + k)) : BitString k :=
  fun i =>
    (ModulusCounter.stepValue (ModulusCounter.leftWord x) (ModulusCounter.rightWord x)).getLsbD
      i.val

/-- `counterModulus` depends only on the first `k` coordinates of the `2 k`-bit state. -/
theorem counterModulus_eq_of_eq {x y : BitString (k + k)}
    (h : (fun i => x (Fin.castAdd k i)) = fun i => y (Fin.castAdd k i)) :
    counterModulus x = counterModulus y :=
  congrArg (fun z => (word z).toNat) h

/-- `counterStep k` preserves the modulus stored in the first `k` coordinates. -/
theorem counterStep_preserve_modulus (x : BitString (k + k)) :
    counterModulus (counterStep k x) = counterModulus x := by
  simp [counterModulus, counterStep, ModulusCounter.power]

/-- Iterating `counterStepValue a` for `T` steps on `b` equals `ModulusCounter.advance a b T`. -/
theorem counterStepValue_iterate (a b T : ℕ) :
    (counterStepValue a)^[T] b = ModulusCounter.advance a b T := by
  induction T generalizing b with
  | zero => simp [ModulusCounter.advance_zero]
  | succ T ih =>
    rw [Function.iterate_succ_apply, ih, counterStepValue, ModulusCounter.advance_add,
      Nat.add_comm 1 T]

/-- After `T` steps of `counterStep k`, the right word has natural value
`ModulusCounter.advance (leftWord x).toNat (rightWord x).toNat T`. -/
theorem counterStep_iterate_toNat (T : ℕ) (x : BitString (k + k)) :
    (ModulusCounter.rightWord ((counterStep k)^[T] x)).toNat =
      ModulusCounter.advance
        (ModulusCounter.leftWord x).toNat (ModulusCounter.rightWord x).toNat T := by
  rw [counterStep, ModulusCounter.iterate_power]
  simp only [ModulusCounter.power, ModulusCounter.rightWord_pack, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (ModulusCounter.advance_lt (BitVec.isLt _) (BitVec.isLt _))

/-- Distinct exponents below `ModulusCounter.period k` produce distinct counter powers. -/
theorem counter_power_ne {S T : ℕ} (hS : S < ModulusCounter.period k)
    (hT : T < ModulusCounter.period k) (hne : S ≠ T) :
    (counterStep k)^[S] ≠ (counterStep k)^[T] := by
  intro h
  rw [counterStep, ModulusCounter.iterate_power, ModulusCounter.iterate_power] at h
  exact hne (Fin.val_eq_of_eq (ModulusCounter.powers_injective
    (a₁ := ⟨S, hS⟩) (a₂ := ⟨T, hT⟩) h))

/-- There are `ModulusCounter.period k` distinct counter power functions for exponents below
`ModulusCounter.period k`. -/
theorem counter_family_card (k : ℕ) :
    (Finset.univ.image (fun T : Fin (ModulusCounter.period k) =>
      ModulusCounter.power (k := k) T.val)).card = ModulusCounter.period k := by
  rw [Finset.card_image_of_injective _ ModulusCounter.powers_injective, Finset.card_univ,
    Fintype.card_fin]

/-- The single-step modular counter `counterStep k` has a De Morgan circuit of size at most
`50 * k + 20`. -/
theorem counterStep_circuit (k : ℕ) :
    ∃ c : Circuit signature (k + k) (k + k),
      c.Computes interpretation (counterStep k) ∧ c.size ≤ 50 * k + 20 :=
  ModulusCounter.exists_linear_circuit k

end Cslib.Circuits.Boolean.Iteration
