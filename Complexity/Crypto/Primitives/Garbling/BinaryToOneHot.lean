/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Primitives.Garbling.OneHot
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Abel

/-!
# Garbled binary-to-one-hot conversion

The one-hot garbling gadget of Heath and Kolesnikov [HeathKolesnikov2021], which the
lookup-table garbling scheme `logrow` of Heath, Kolesnikov and Ng [HeathKolesnikovNg2024] uses
through the interface of its Figure 1. Wire labels live in an additive group `L` of
characteristic two (over `GF(2)^λ`, addition is XOR) with a Free-XOR global offset `Δ`
[KolesnikovSchneider2008]: the label of bit `b` on a wire with zero-label `X` is
`X + bitOffset Δ b`. From one label on each of `n + 1` input wires and `n` ciphertexts of one
label each, the evaluator obtains Free-XOR labels of the one-hot vector of its input, a vector of
`2 ^ (n + 1)` bits. With the paper's `n` equal to `n + 1` here, this is the `(n - 1) κ` term of
the `logrow` material size ([HeathKolesnikovNg2024], Theorem 1). The construction below follows a
reconstruction of the gadget; it was checked against the interface and cost stated in
[HeathKolesnikovNg2024], not against the text of [HeathKolesnikov2021].

Positions of the one-hot vector over `t + 1` input bits are bit vectors `j : Fin (t + 1) → Bool`;
the position `Fin.snoc j c` of the next vector extends `j` by the next input bit `c`. Over one
input bit, the zero-labels are `X` at position `true` and `X + Δ` at position `false`, and the
evaluator holding the label `X + bitOffset Δ x₀` uses it at both positions; no ciphertext is
needed. A doubling step (`garbleStep`) hashes each zero-label `G j` to `y j`, keeps `G j + y j`
at position `Fin.snoc j false` and `y j` at `Fin.snoc j true`, and sends the ciphertext
`b + ∑ j, y j`, where `b` is the zero-label of the new input bit. The evaluator (`evalStep`)
knows the hot position `x` but not the zero-label at `x`. It recomputes `y j` at every other
position, and recovers `y x + bitOffset Δ c` from its label `b + bitOffset Δ c` of the new bit
and the ciphertext.

Hashes are a tweakable function `H : L → T → L`; step `t` hashes position `j` with tweak `tw t j`.
Correctness (`evaluate_garble`) holds for every `H`, `tw`, `Δ`, choice of zero-labels and
input. In `logrow` the evaluator's index is the input masked by the garbler's permutation bits,
which it reads from its labels; this file takes that index as given. Combined with the
truth-table product, the evaluator obtains Free-XOR labels of the row of any public table at its
index (`tableMul_evaluate_garble`). Obliviousness is in
`Complexity.Crypto.Primitives.Garbling.BinaryToOneHotObliviousness`.

## Main definitions

* `Cslib.Crypto.Garbling.BinaryToOneHot.garbleStep`, `.evalStep`: one doubling step.
* `Cslib.Crypto.Garbling.BinaryToOneHot.garble`: zero-labels of the one-hot vector and the
  `n` ciphertexts, from the zero-labels of `n + 1` input wires.
* `Cslib.Crypto.Garbling.BinaryToOneHot.evaluate`: the evaluator.

## Main results

* `Cslib.Crypto.Garbling.BinaryToOneHot.evalStep_garbleStep`: one step preserves one-hot labels.
* `Cslib.Crypto.Garbling.BinaryToOneHot.evaluate_garble`: correctness.
* `Cslib.Crypto.Garbling.BinaryToOneHot.tableMul_evaluate_garble`: labels of a selected row.

## References

* [D. Heath, V. Kolesnikov, *One Hot Garbling*][HeathKolesnikov2021]
* [D. Heath, V. Kolesnikov, L. K. L. Ng, *Garbled Circuit Lookup Tables with Logarithmic Number
  of Ciphertexts*][HeathKolesnikovNg2024]
* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
-/

@[expose] public section

namespace Cslib.Crypto.Garbling.BinaryToOneHot

variable {L T : Type} [AddCommGroup L]

/-- One doubling step of the garbler, from `t + 1` to `t + 2` input bits. `h j` hashes the
zero-label of position `j`, `b` is the zero-label of the new input bit and `G` the current
zero-labels. Returns the new zero-labels and the step's ciphertext `b + ∑ j, h j (G j)`. -/
def garbleStep {t : ℕ} (h : (Fin (t + 1) → Bool) → L → L) (b : L)
    (G : (Fin (t + 1) → Bool) → L) : ((Fin (t + 2) → Bool) → L) × L :=
  (fun j => if j (Fin.last _) then h (Fin.init j) (G (Fin.init j))
      else G (Fin.init j) + h (Fin.init j) (G (Fin.init j)),
    b + ∑ j, h j (G j))

/-- One doubling step of the evaluator, who knows the hot position `x`, holds the label `a` of the
new input bit and the current labels `E`, and receives the ciphertext `ct`. It hashes every label
but the one at `x`, and recovers the hash at `x`, masked by the new bit, from `a` and `ct`. -/
def evalStep {t : ℕ} (h : (Fin (t + 1) → Bool) → L → L) (x : Fin (t + 1) → Bool) (a ct : L)
    (E : (Fin (t + 1) → Bool) → L) : (Fin (t + 2) → Bool) → L :=
  let y : (Fin (t + 1) → Bool) → L := fun j =>
    if j = x then a + ct + ∑ i ∈ Finset.univ.erase x, h i (E i) else h j (E j)
  fun j => if j (Fin.last _) then y (Fin.init j) else E (Fin.init j) + y (Fin.init j)

/-- The hash of doubling step `t`: position `j` is hashed with tweak `tw t j`. -/
def hashAt (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (t : ℕ) :
    (Fin (t + 1) → Bool) → L → L :=
  fun j g => H g (tw t j)

/-- The garbler with global offset `Δ`, from the zero-labels `X` of `n + 1` input wires: the
zero-labels of the one-hot vector and one ciphertext for each of the `n` doubling steps. -/
def garble (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (Δ : L) :
    (n : ℕ) → (Fin (n + 1) → L) → ((Fin (n + 1) → Bool) → L) × (Fin n → L)
  | 0, X => (fun j => if j 0 then X 0 else X 0 + Δ, Fin.elim0)
  | n + 1, X =>
    let prev := garble H tw Δ n (Fin.init X)
    let step := garbleStep (hashAt H tw n) (X (Fin.last (n + 1))) prev.1
    (step.1, Fin.snoc prev.2 step.2)

/-- The evaluator, from the index `x`, one label `A` on each input wire and the ciphertexts `ct`:
its labels of the one-hot vector. -/
def evaluate (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) :
    (n : ℕ) → (Fin (n + 1) → Bool) → (Fin (n + 1) → L) → (Fin n → L) →
      (Fin (n + 1) → Bool) → L
  | 0, _, A, _ => fun _ => A 0
  | n + 1, x, A, ct =>
    evalStep (hashAt H tw n) (Fin.init x) (A (Fin.last (n + 1))) (ct (Fin.last n))
      (evaluate H tw n (Fin.init x) (Fin.init A) (Fin.init ct))

variable [Module (ZMod 2) L]

/-- **One doubling step is correct**: if the evaluator holds the labels of the one-hot vector of
`x` with zero-labels `G` and the label of bit `c` of the new input wire, it obtains the labels of
the one-hot vector of `Fin.snoc x c` with the new zero-labels. -/
theorem evalStep_garbleStep {t : ℕ} (h : (Fin (t + 1) → Bool) → L → L) (Δ b : L)
    (G : (Fin (t + 1) → Bool) → L) (x : Fin (t + 1) → Bool) (c : Bool) :
    evalStep h x (b + bitOffset Δ c) (garbleStep h b G).2
        (fun j => G j + bitOffset Δ (oneHot x j)) =
      fun j => (garbleStep h b G).1 j + bitOffset Δ (oneHot (Fin.snoc x c) j) := by
  have hE : ∀ i, i ≠ x → G i + bitOffset Δ (oneHot x i) = G i := fun i hi => by
    rw [oneHot_of_ne hi, bitOffset_false, add_zero]
  have hrest : ∑ i ∈ Finset.univ.erase x, h i (G i + bitOffset Δ (oneHot x i)) =
      ∑ i ∈ Finset.univ.erase x, h i (G i) :=
    Finset.sum_congr rfl fun i hi => by rw [hE i (Finset.ne_of_mem_erase hi)]
  -- The evaluator's masked hash at the hot position.
  have hyx : b + bitOffset Δ c + (b + ∑ i, h i (G i)) +
      ∑ i ∈ Finset.univ.erase x, h i (G i + bitOffset Δ (oneHot x i)) =
      h x (G x) + bitOffset Δ c := by
    rw [hrest, ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    rw [show b + bitOffset Δ c + (b + (h x (G x) + ∑ i ∈ Finset.univ.erase x, h i (G i))) +
        ∑ i ∈ Finset.univ.erase x, h i (G i) =
        (b + b) + ((∑ i ∈ Finset.univ.erase x, h i (G i)) +
          ∑ i ∈ Finset.univ.erase x, h i (G i)) + (h x (G x) + bitOffset Δ c) by abel,
      ZModModule.add_self, ZModModule.add_self, zero_add, zero_add]
  funext j
  obtain ⟨j', c', rfl⟩ : ∃ (j' : Fin (t + 1) → Bool) (c' : Bool), Fin.snoc j' c' = j :=
    ⟨Fin.init j, j (Fin.last _), Fin.snoc_init_self j⟩
  have hoh : oneHot (Fin.snoc x c) (Fin.snoc j' c' : Fin (t + 2) → Bool) =
      (decide (j' = x) && decide (c' = c)) := by
    simp only [oneHot, Fin.snoc_injective2.eq_iff, Bool.decide_and]
  simp only [evalStep, garbleStep, Fin.init_snoc, Fin.snoc_last, hoh]
  by_cases hx : j' = x
  · subst hx
    simp only [ite_true, decide_true, Bool.true_and, oneHot_self, bitOffset_true]
    rw [hyx]
    cases c' <;> cases c
    · simp only [Bool.false_eq_true, ite_false, decide_true, bitOffset_true, bitOffset_false,
        add_zero]
      abel
    · simp only [Bool.false_eq_true, ite_false, decide_false, bitOffset_true, bitOffset_false,
        add_zero]
      rw [show G j' + Δ + (h j' (G j') + Δ) = G j' + h j' (G j') + (Δ + Δ) by abel,
        ZModModule.add_self, add_zero]
    · simp only [ite_true, Bool.true_eq_false, decide_false, bitOffset_false, add_zero]
    · simp only [ite_true, decide_true, bitOffset_true]
  · simp only [hx, ite_false, decide_false, Bool.false_and, bitOffset_false, add_zero, hE _ hx]

/-- **Correctness**: on the labels of its input bits and the garbled ciphertexts, the evaluator
obtains the labels of the one-hot vector of its input, for every hash, tweaks, offset and
zero-labels. -/
theorem evaluate_garble (H : L → T → L) (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (Δ : L)
    (n : ℕ) (X : Fin (n + 1) → L) (x : Fin (n + 1) → Bool) :
    evaluate H tw n x (fun t => X t + bitOffset Δ (x t)) (garble H tw Δ n X).2 =
      fun j => (garble H tw Δ n X).1 j + bitOffset Δ (oneHot x j) := by
  induction n with
  | zero =>
    funext j
    have hj : oneHot x j = decide (j 0 = x 0) := decide_eq_decide.mpr
      ⟨fun h => congrFun h 0, fun h => funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩
    simp only [evaluate, garble, hj]
    clear hj
    cases j 0 <;> cases x 0 <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, ite_false, ite_true, decide_true,
        decide_false, bitOffset_true, bitOffset_false, add_zero, add_assoc, ZModModule.add_self]
  | succ n ih =>
    have hA : (Fin.init fun t => X t + bitOffset Δ (x t)) =
        fun t => Fin.init X t + bitOffset Δ (Fin.init x t) := rfl
    have hct : Fin.init (garble H tw Δ (n + 1) X).2 = (garble H tw Δ n (Fin.init X)).2 := by
      simp only [garble, Fin.init_snoc]
    have hlast : (garble H tw Δ (n + 1) X).2 (Fin.last n) =
        (garbleStep (hashAt H tw n) (X (Fin.last (n + 1)))
          (garble H tw Δ n (Fin.init X)).1).2 := by
      simp only [garble, Fin.snoc_last]
    simp only [evaluate]
    rw [hA, hct, ih (Fin.init X) (Fin.init x), hlast, evalStep_garbleStep, Fin.snoc_init_self]
    rfl

/-- **Labels of a selected row.** With the labels the evaluator obtains, the product with any
public table `T` gives, at each output `u`, the label of bit `T x u` with zero-label
`tableMul T G u`, where `G` are the garbler's one-hot zero-labels. -/
theorem tableMul_evaluate_garble {κ : Type} (H : L → T → L)
    (tw : (t : ℕ) → (Fin (t + 1) → Bool) → T) (Δ : L) (n : ℕ) (X : Fin (n + 1) → L)
    (x : Fin (n + 1) → Bool) (Tab : (Fin (n + 1) → Bool) → κ → Bool) :
    tableMul Tab (evaluate H tw n x (fun t => X t + bitOffset Δ (x t)) (garble H tw Δ n X).2) =
      fun u => tableMul Tab (garble H tw Δ n X).1 u + bitOffset Δ (Tab x u) := by
  rw [evaluate_garble, tableMul_oneHotLabels]

end Cslib.Crypto.Garbling.BinaryToOneHot
