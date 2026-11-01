/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Decode
public import Complexity.Foundations.Data.List.Append
import Complexity.Foundations.Data.Nat.Bits
import Mathlib.Data.Nat.Size

/-!
# The padded satisfiability problem of Ladner's theorem

Ladner's theorem is proved by padding satisfiable formulas with a number of ones growing slowly
but, unless `P = NP`, faster than any polynomial [Arora and Barak, Theorem 3.3][AroraBarak09].
Along an exponent function `e`, a formula `φ` whose encoding has length `m` is padded to the word
`pad (encCNF φ) (m ^ e m)`: the encoding followed by `false` and `m ^ e m` ones
(`Cslib.Complexity.Ladner.padSAT`). Ladner's language `Cslib.Complexity.Ladner.SATH` takes the
exponent `Cslib.Complexity.Ladner.H` defined here.

`H n` is the least index `i < log₂ (log₂ n)` of a machine agreeing with the language itself on the
words with indices below `n`, or `log₂ (log₂ n)` if there is none. Words are indexed by `ℕ`
(`Cslib.Complexity.Ladner.word`); the words with indices below `n` have length at most `log₂ n` and
include every word whose length `l` satisfies `2 ^ (l + 1) ≤ n + 1`. The machine with index `i`
is the one described at the start of the `i`-th word (`Turing.MultiTapeTM.Universal.decodeDesc`),
run by the universal function, so every machine has arbitrarily large indices. On a word of
length `l` it is allowed `(2 * l + 2) ^ i` steps, a clock exceeding every polynomial time bound at
large enough indices, but never more than `n`. Arora and Barak allow `i * l ^ i` steps and estimate
the cost; capping the clock at `n` keeps the computation of `H n` polynomial in `n` without any
asymptotic estimate, and for every fixed machine and word the cap stops mattering once `n` is
large.

Whether a word with index below `n` belongs to the language depends only on the values `H m` with
`m < n`. `H` is therefore defined by recursion on tables of its earlier values
(`Cslib.Complexity.Ladner.Hstep`, `Cslib.Complexity.Ladner.Htable`), and characterised by
`Cslib.Complexity.Ladner.H_le_of_agrees` and `Cslib.Complexity.Ladner.agrees_H`.

## Main definitions

* `Cslib.Complexity.Ladner.word`, `Cslib.Complexity.Ladner.index`: words by index.
* `Cslib.Complexity.Ladner.pad`, `Cslib.Complexity.Ladner.unpad`: padding with ones.
* `Cslib.Complexity.Ladner.padSAT`: satisfiable formulas padded along an exponent function.
* `Cslib.Complexity.Ladner.runIndexed`, `Cslib.Complexity.Ladner.clock`,
  `Cslib.Complexity.Ladner.Agrees`: the indexed machines, their clocks, and agreement with a padded
  language.
* `Cslib.Complexity.Ladner.Hstep`, `Cslib.Complexity.Ladner.Htable`, `Cslib.Complexity.Ladner.H`:
  the exponent function.
* `Cslib.Complexity.Ladner.SATH`: Ladner's language.

## Main results

* `Cslib.Complexity.Ladner.word_index`, `Cslib.Complexity.Ladner.two_pow_length_word_le`: every word
  has an index, and the word with index `j` has length at most `log₂ (j + 1)`.
* `Cslib.Complexity.Ladner.unpad_pad`, `Cslib.Complexity.Ladner.pad_unpad`: padding is undone.
* `Cslib.Complexity.Ladner.Htable_eq`: the tables hold the values of `H`.
* `Cslib.Complexity.Ladner.H_le`, `Cslib.Complexity.Ladner.H_le_of_agrees`,
  `Cslib.Complexity.Ladner.agrees_H`: `H n` is the least index below `log₂ (log₂ n)` of a machine
  agreeing with `SATH` on the words with indices below `n`, or `log₂ (log₂ n)`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.Ladner

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-! ### Words by index -/

/-- The word with index `j`: the binary digits of `j + 1`, least significant first, without the
final `true`. -/
def word (j : ℕ) : List Bool := (j + 1).bits.dropLast

/-- The index of a word: one less than the number whose binary digits are the word followed by
`true`. -/
def index (w : List Bool) : ℕ := w.foldr Nat.bit 1 - 1

/-- **Every word has an index.** -/
@[simp]
theorem word_index (w : List Bool) : word (index w) = w := by
  rw [word, index, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.foldr_bit_one_ne_zero w)),
    Nat.bits_foldr_bit_one, List.dropLast_concat]

/-- The index of a word of length `l` is less than `2 ^ (l + 1) - 1`. -/
theorem index_add_two_le (w : List Bool) : index w + 2 ≤ 2 ^ (w.length + 1) := by
  have h₁ := Nat.foldr_bit_one_lt w
  have h₂ := Nat.foldr_bit_one_ne_zero w
  rw [index]
  omega

/-- **The word with index `j` has length at most `log₂ (j + 1)`.** -/
theorem two_pow_length_word_le (j : ℕ) : 2 ^ (word j).length ≤ j + 1 := by
  rw [word, List.length_dropLast, Nat.size_eq_bits_len]
  exact Nat.lt_size.mp (Nat.sub_lt (Nat.size_pos.mpr (Nat.succ_pos j)) Nat.one_pos)

private theorem length_word_lt (j : ℕ) : (word j).length < j + 1 :=
  (Nat.lt_two_pow_self).trans_le (two_pow_length_word_le j)

/-! ### Padding -/

/-- The word `u` padded with `k` ones after a separating zero. -/
def pad (u : List Bool) (k : ℕ) : List Bool := u ++ false :: List.replicate k true

/-- Splits a word at its last `false`: the word before it and the number of `true`s after it. If
the word has no `false`, the second component is its length. -/
def unpad (y : List Bool) : List Bool × ℕ :=
  (y.take (y.length - (y.reverse.idxOf false + 1)), y.reverse.idxOf false)

@[simp]
theorem length_pad (u : List Bool) (k : ℕ) : (pad u k).length = u.length + 1 + k := by
  simp only [pad, List.length_append, List.length_cons, List.length_replicate]
  omega

/-- **Padding is undone.** -/
@[simp]
theorem unpad_pad (u : List Bool) (k : ℕ) : unpad (pad u k) = (u, k) := by
  have hrev : (pad u k).reverse = List.replicate k true ++ false :: u.reverse := by
    simp [pad]
  rw [unpad, hrev, List.idxOf_false_replicate_append, length_pad,
    show u.length + 1 + k - (k + 1) = u.length by omega, pad, List.take_left' rfl]

theorem pad_inj {u u' : List Bool} {k k' : ℕ} : pad u k = pad u' k' ↔ u = u' ∧ k = k' :=
  ⟨fun h => by simpa using congrArg unpad h, fun ⟨hu, hk⟩ => hu ▸ hk ▸ rfl⟩

/-- **A word with a `false` is its padded split.** -/
theorem pad_unpad {y : List Bool} (hy : (unpad y).2 < y.length) :
    pad (unpad y).1 (unpad y).2 = y := by
  have hmem : false ∈ y.reverse :=
    List.idxOf_lt_length_iff.mp (by simpa [unpad] using hy)
  obtain ⟨v, k, rfl⟩ : ∃ v k, y = pad v k := by
    refine ⟨(y.reverse.drop (y.reverse.idxOf false + 1)).reverse, y.reverse.idxOf false, ?_⟩
    conv_lhs => rw [← List.reverse_reverse y, List.eq_replicate_idxOf_false hmem]
    simp [pad]
  rw [unpad_pad]

/-! ### Padded satisfiability -/

/-- **Satisfiable formulas padded along an exponent function.** A formula `φ` whose encoding has
length `m` is padded with `m ^ e m` ones. -/
def padSAT (e : ℕ → ℕ) : Set (List Bool) :=
  {y | ∃ φ ∈ SAT, y = pad (encCNF φ) ((encCNF φ).length ^ e (encCNF φ).length)}

theorem pad_mem_padSAT_iff {e : ℕ → ℕ} {φ : Logic.PL.CNF ℕ} {k : ℕ} :
    pad (encCNF φ) k ∈ padSAT e ↔ φ ∈ SAT ∧ k = (encCNF φ).length ^ e (encCNF φ).length := by
  constructor
  · rintro ⟨ψ, hψ, h⟩
    obtain ⟨h₁, rfl⟩ := pad_inj.mp h
    obtain rfl := encCNF.injective h₁
    exact ⟨hψ, rfl⟩
  · rintro ⟨hφ, rfl⟩
    exact ⟨φ, hφ, rfl⟩

/-- Membership of `y` depends only on the exponents of lengths below the length of `y`. -/
theorem mem_padSAT_congr {e e' : ℕ → ℕ} {y : List Bool} (h : ∀ m < y.length, e m = e' m) :
    y ∈ padSAT e ↔ y ∈ padSAT e' := by
  constructor <;> rintro ⟨φ, hφ, rfl⟩ <;> refine ⟨φ, hφ, ?_⟩
  · rw [h _ (by rw [length_pad]; omega)]
  · rw [h _ (by rw [length_pad]; omega)]

/-! ### The indexed machines -/

/-- The run of the machine with index `i` on `w` for `t` steps: the universal function on the
description at the start of the `i`-th word, and `w` under the coding `false ↦ 0`, `true ↦ 1`. -/
def runIndexed (i : ℕ) (w : List Bool) (t : ℕ) : List ℕ × Bool :=
  universal (decodeDesc (unframe (word i)), w.map eBit, t)

/-- The clock of the machine with index `i` on inputs of length `l`. -/
def clock (i l : ℕ) : ℕ := (2 * l + 2) ^ i

theorem one_le_clock (i l : ℕ) : 1 ≤ clock i l := Nat.one_le_pow _ _ (by omega)

/-- The machine with index `i`, allowed `clock i l` steps on a word of length `l` but never more
than `cap`, halts on the `j`-th word with output `[b]` where `b` decides membership in
`padSAT e`. -/
def Agrees (e : ℕ → ℕ) (cap i j : ℕ) : Prop :=
  ∃ b : Bool, runIndexed i (word j) (min (clock i (word j).length) cap) = ([eBit b], true) ∧
    (b = true ↔ word j ∈ padSAT e)

/-- Agreement on the `j`-th word depends only on the exponents of lengths below `j`. -/
theorem agrees_congr {e e' : ℕ → ℕ} {cap i j : ℕ} (h : ∀ m < j, e m = e' m) :
    Agrees e cap i j ↔ Agrees e' cap i j := by
  have h' : ∀ m < (word j).length, e m = e' m := fun m hm =>
    h m (hm.trans_le (Nat.lt_succ_iff.mp (length_word_lt j)))
  simp only [Agrees, mem_padSAT_congr h']

/-! ### The exponent function -/

/-- The value of the exponent at `T.length` from the table `T` of its earlier values: the least
index below `log₂ (log₂ T.length)` of a machine agreeing with `padSAT` on the words with indices
below `T.length`, or `log₂ (log₂ T.length)`. The clocks are capped at `T.length`. -/
noncomputable def Hstep (T : List ℕ) : ℕ :=
  sInf {i | i = Nat.log 2 (Nat.log 2 T.length) ∨
    ∀ j < T.length, Agrees (fun m => T.getD m 0) T.length i j}

/-- The table of the first `n` values of the exponent function. -/
noncomputable def Htable : ℕ → List ℕ
  | 0 => []
  | n + 1 => Htable n ++ [Hstep (Htable n)]

/-- **The exponent function of Ladner's language.** -/
noncomputable def H (n : ℕ) : ℕ := Hstep (Htable n)

/-- **Ladner's language**: satisfiable formulas padded along `H`. -/
noncomputable def SATH : Set (List Bool) := padSAT H

/-- **The tables hold the values of `H`.** -/
theorem Htable_eq (n : ℕ) : Htable n = (List.range n).map H := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Htable, List.range_succ, List.map_append, ← ih]; rfl

@[simp]
theorem length_Htable (n : ℕ) : (Htable n).length = n := by
  simp [Htable_eq]

theorem agrees_Htable_iff {n i j : ℕ} (hj : j < n) :
    Agrees (fun m => (Htable n).getD m 0) n i j ↔ Agrees H n i j :=
  agrees_congr fun m hm => by
    rw [Htable_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl

theorem H_eq (n : ℕ) :
    H n = sInf {i | i = Nat.log 2 (Nat.log 2 n) ∨ ∀ j < n, Agrees H n i j} := by
  rw [H, Hstep, length_Htable]
  congr 1
  ext i
  simp only [Set.mem_ofPred_eq]
  exact or_congr_right (forall₂_congr fun j hj => agrees_Htable_iff hj)

/-- **`H` grows slowly**: `H n ≤ log₂ (log₂ n)`. -/
theorem H_le (n : ℕ) : H n ≤ Nat.log 2 (Nat.log 2 n) := by
  rw [H_eq]
  exact Nat.sInf_le (Or.inl rfl)

theorem H_le_self (n : ℕ) : H n ≤ n :=
  (H_le n).trans ((Nat.log_le_self 2 _).trans (Nat.log_le_self 2 n))

/-- **`H n` is at most the index of every machine agreeing with `SATH` below `n`.** -/
theorem H_le_of_agrees {n i : ℕ} (h : ∀ j < n, Agrees H n i j) : H n ≤ i := by
  rw [H_eq]
  exact Nat.sInf_le (Or.inr h)

/-- **If `H n < log₂ (log₂ n)`, the machine with index `H n` agrees with `SATH` below `n`.** -/
theorem agrees_H {n : ℕ} (h : H n < Nat.log 2 (Nat.log 2 n)) : ∀ j < n, Agrees H n (H n) j := by
  have hmem : H n ∈ {i | i = Nat.log 2 (Nat.log 2 n) ∨ ∀ j < n, Agrees H n i j} := by
    rw [H_eq]
    exact Nat.sInf_mem ⟨_, Or.inl rfl⟩
  exact hmem.resolve_left h.ne

end Cslib.Complexity.Ladner
