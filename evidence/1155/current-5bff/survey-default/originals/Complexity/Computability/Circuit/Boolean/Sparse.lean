/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PPoly

/-!
# Sparse and unary languages have circuits of polynomial size

A slice with at most `k` words of length `n` is the disjunction of the minterms of its words, so it
has a circuit of `k (2 n + 2) + 1` gates (`complexity_slice_le_of_card_le`). A language with
polynomially many words of each length, a *sparse* language, is therefore in `P/poly`
(`PPoly.of_sparse`). A *unary* language, whose words consist only of `true`s, has at most one word
of each length, and its slice at `n` is a constant or the conjunction of the `n` inputs, so it has
circuits of `n + 1` gates (`mem_SIZE_of_unary`). Since the circuits at different lengths need not be
related, unary languages that no machine decides are in `P/poly` [Arora and Barak, Section
6.1][AroraBarak09].

## Main results

* `Cslib.Circuits.Boolean.complexity_slice_le_of_card_le`: a slice with few words has a small
  circuit.
* `Cslib.Circuits.Boolean.PPoly.of_sparse`: sparse languages are in `P/poly`.
* `Cslib.Circuits.Boolean.mem_SIZE_of_unary`, `Cslib.Circuits.Boolean.PPoly.of_unary`: unary
  languages have circuits of `n + 1` gates, so they are in `P/poly`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset

variable {L : Language Bool}

/-- A slice with at most `k` words of length `n` has a circuit of `k (2 n + 2) + 1` gates: the
disjunction of the minterms of its words. -/
theorem complexity_slice_le_of_card_le {n k : ℕ}
    (h : #{x : BitString n | L.slice n x = true} ≤ k) :
    complexity interpretation (single (L.slice n)) ≤ k * (2 * n + 2) + 1 := by
  set W := ({x : BitString n | L.slice n x = true} : Finset (BitString n))
  have hs := Synthesis.exists_mem W (fun w x => decide ((fun i => x (id i)) = w))
    (fun _ => 2 * n + 1) fun w _ => synthesis_minterm id w
  have hfun : (fun x => decide (∃ w ∈ W, decide ((fun i => x (id i)) = w) = true)) =
      L.slice n := by
    funext x
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    simp [W]
  rw [hfun, sum_const, smul_eq_mul] at hs
  exact hs.complexity_le.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) 1)

/-- **Sparse languages are in P/poly.** A language with at most `s n` words of each length `n`,
for a polynomially bounded `s`, has circuits of polynomial size. -/
theorem PPoly.of_sparse {s : ℕ → ℕ} (hs : PolynomiallyBounded s)
    (h : ∀ n, #{x : BitString n | L.slice n x = true} ≤ s n) : L ∈ PPoly :=
  PolynomiallyBounded.mono_of_le (g := fun n => s n * (2 * n + 2) + 1) (by fun_prop)
    fun n => complexity_slice_le_of_card_le (h n)

/-- The word of length `n` is all `true` exactly when every one of its bits is. -/
private theorem ofFn_eq_replicate_true_iff {n : ℕ} {x : BitString n} :
    List.ofFn x = List.replicate n true ↔ ∀ i, x i = true := by
  simp [List.eq_replicate_iff, List.mem_ofFn]

/-- **Unary languages have linear-size circuits.** A language whose words consist only of `true`s
has, at every length `n`, a circuit of `n + 1` gates: a constant when the word of length `n` is not
in the language, and the conjunction of the inputs otherwise. -/
theorem mem_SIZE_of_unary (hL : ∀ w ∈ L, ∀ b ∈ w, b = true) : L ∈ SIZE fun n => n + 1 := by
  intro n
  have hmem (x : BitString n) :
      List.ofFn x ∈ L ↔ List.replicate n true ∈ L ∧ ∀ i, x i = true := by
    refine ⟨fun hx => ?_, fun ⟨hn, hx⟩ => by rwa [ofFn_eq_replicate_true_iff.mpr hx]⟩
    have hx' : ∀ i, x i = true := fun i => hL _ hx _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact ⟨ofFn_eq_replicate_true_iff.mpr hx' ▸ hx, hx'⟩
  by_cases hn : List.replicate n true ∈ L
  · have hslice : L.slice n = fun x => decide (∀ i ∈ univ, x i = true) := by
      funext x
      rw [Bool.eq_iff_iff]
      simp [hmem, hn]
    have hc := (Synthesis.forall_mem (s := inputs n) univ (fun i (x : BitString n) => x i)
      (fun _ => 0) fun i _ => Synthesis.of_mem ⟨i, rfl⟩).complexity_le
    simpa [hslice] using hc
  · have hslice : L.slice n = fun _ => false := by
      funext x
      rw [Bool.eq_iff_iff]
      simp [hmem, hn]
    rw [hslice]
    exact (Synthesis.const false).complexity_le.trans (Nat.le_add_left 1 n)

/-- **Unary languages are in P/poly**, including those that no machine decides. -/
theorem PPoly.of_unary (hL : ∀ w ∈ L, ∀ b ∈ w, b = true) : L ∈ PPoly :=
  mem_PPoly_iff_exists_mem_SIZE.2 ⟨2, SIZE_mono (fun n => by
    have := Nat.le_self_pow two_ne_zero (n + 1)
    dsimp only
    omega) (mem_SIZE_of_unary hL)⟩

end Cslib.Circuits.Boolean
