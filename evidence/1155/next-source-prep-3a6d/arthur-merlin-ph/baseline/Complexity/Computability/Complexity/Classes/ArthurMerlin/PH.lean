/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ArthurMerlin.Amplification
public import Complexity.Computability.Complexity.Classes.PH
public import Complexity.Foundations.Data.BitString.Basic

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Combinatorics.Lautemann
import Complexity.Foundations.Data.BitString.List.Operations
import Mathlib.Data.List.GetD

/-!
# MA and AM in the second level of the polynomial hierarchy

`MA ⊆ Σ₂ ∩ Π₂` and `AM ⊆ Π₂` [Babai][Babai1985], [Babai and Moran][BabaiMoran1988],
[Arora and Barak, Section 8.2][AroraBarak09], by Lautemann's covering argument
([Lautemann][Lautemann1983], `Complexity.Foundations.Combinatorics.Lautemann`), as in the
Sipser–Gács–Lautemann theorem `BPP ⊆ Σ₂ ∩ Π₂` (`Cslib.Complexity.BPP_subset_SigmaP_two`).
Write `n` for the length of the encoded instance.

First reduce the error to `2 ^ (-e(n))`, with random strings of `m(n) = 12 e(n) p(n)` bits, where
`p(n)` is the original random-string length; then `k(n) = e(n) = 12 p(n) + 1` shifts satisfy
`m(n) < e(n) k(n)` and `k(n) < 2 ^ e(n)`. For a set `S` of random strings, with xor as addition:

* if `S` misses at most a `2 ^ (-e(n))` fraction of the strings, some `k(n)` shifts `u i` carry
  every string `r` into `S` for some `i`
  (`Cslib.BitString.exists_forall_exists_add_mem_of_two_pow_mul_card_compl_le`);
* if `S` is at most such a fraction, for all `k(n)` shifts some `r` has every `r + u i` outside `S`
  (`Cslib.BitString.exists_forall_add_notMem_of_two_pow_mul_card_le`).

For `MA ⊆ Σ₂`, `S` is the set of random strings accepted with a proof `y`, and
`a ∈ A ↔ ∃ y u, ∀ r, ∃ i, V (a, y ++ (r + u i))`; Merlin's proof and the shifts form one existential
block (`Cslib.Complexity.ArthurMerlin.sigmaTwoVerifier`). For `AM ⊆ Π₂`, `S` is the set of random
strings with an accepted reply, and `a ∈ A ↔ ∀ u, ∃ r Y, ∀ i, V (a, (r + u i) ++ Y i)`; the
random string and the `k(n)` replies form one existential block
(`Cslib.Complexity.ArthurMerlin.piTwoVerifier`). `MA ⊆ Π₂` follows from `MA ⊆ AM`.

## Main definitions

* `Cslib.Complexity.ArthurMerlin.sigmaTwoVerifier`: the `Σ₂` verifier of a Merlin–Arthur verifier.
* `Cslib.Complexity.ArthurMerlin.piTwoVerifier`: the `Π₂` verifier of an Arthur–Merlin verifier.

## Main results

* `Cslib.Complexity.ArthurMerlin.isAlternatingVerifier_sigmaTwoVerifier`,
  `Cslib.Complexity.ArthurMerlin.isAlternatingVerifier_piTwoVerifier`: correctness for verifiers
  with small error.
* `Cslib.Complexity.MA_subset_SigmaP_two`, `Cslib.Complexity.AM_subset_PiP_two`,
  `Cslib.Complexity.MA_subset_PiP_two`, `Cslib.Complexity.MA_subset_SigmaP_two_inter_PiP_two`.
* `Cslib.Complexity.AM_subset_PH`.

## References

* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [L. Babai, S. Moran, *Arthur–Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
* [C. Lautemann, *BPP and the polynomial hierarchy*][Lautemann1983]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

namespace ArthurMerlin

/-! ### The `Σ₂` verifier of a Merlin–Arthur verifier -/

/-- The `Σ₂` verifier of a Merlin–Arthur verifier `W` with proofs of length `q` and random strings
of length `p`, with `k` shifts, all evaluated at the length of the encoded instance. The existential
block is a proof `y` followed by `k` shifts of the random string, the universal block is a random
string `r`, and the verifier accepts when `W` accepts the proof with `r` xor some shift. Bits
missing from a short string read as `false` (`Cslib.BitString.listRow`). -/
def sigmaTwoVerifier (enc : α ↪ List Bool) (q k p : Polynomial ℕ) (W : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  let Q := q.eval (enc x.1).length
  let K := k.eval (enc x.1).length
  let m := p.eval (enc x.1).length
  (List.range K).any fun i => W (x.1, x.2.take Q ++
    List.zipWith Bool.xor (BitString.listRow m 0 (x.2.drop (Q + K * m)))
      (BitString.listRow m i (x.2.drop Q)))

/-- The `Σ₂` verifier of a polynomial-time Merlin–Arthur verifier takes polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_sigmaTwoVerifier {W : α × List Bool → Bool}
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool) (q k p : Polynomial ℕ) :
    ComputableInPolyTime (sigmaTwoVerifier enc q k p W) (encPair enc encBits) encBool := by
  unfold sigmaTwoVerifier
  fun_prop

/-- On a proof followed by the shifts and then a random string `r`, the `Σ₂` verifier accepts iff
`W` accepts the proof with `r` xor some shift. -/
private theorem sigmaTwoVerifier_append_ofFn {q k p : Polynomial ℕ} {W : α × List Bool → Bool}
    {a : α}
    {w : List Bool}
    (hw : w.length = q.eval (enc a).length + k.eval (enc a).length * p.eval (enc a).length)
    (r : BitString (p.eval (enc a).length)) :
    sigmaTwoVerifier enc q k p W (a, w ++ List.ofFn r) = true ↔
      ∃ i : Fin (k.eval (enc a).length), W (a, w.take (q.eval (enc a).length) ++
        List.ofFn (r + BitString.block (BitString.ofList
          (k.eval (enc a).length * p.eval (enc a).length) (w.drop (q.eval (enc a).length))) i)) =
          true := by
  simp only [sigmaTwoVerifier, List.any_eq_true, List.mem_range]
  rw [List.take_append_of_le_length (by omega), List.drop_left' hw,
    List.drop_append_of_le_length (by omega)]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    rwa [BitString.listRow_eq_ofFn (count := k.eval (enc a).length) _ ⟨i, hi⟩,
      BitString.ofList_append_of_le (by simp [hw]), BitString.listRow_zero, BitString.ofList_ofFn,
      ← BitString.ofFn_add] at h
  · rintro ⟨i, h⟩
    refine ⟨i, i.2, ?_⟩
    rwa [BitString.listRow_eq_ofFn (count := k.eval (enc a).length) _ i,
      BitString.ofList_append_of_le (by simp [hw]), BitString.listRow_zero, BitString.ofList_ofFn,
      ← BitString.ofFn_add]

/-- **Merlin–Arthur verifiers in `Σ₂`.** If `W` is a Merlin–Arthur verifier for `A` with error at
most `2 ^ (-e(n))` and random strings of `p(n)` bits, and `k(n)` shifts satisfy `p(n) < e(n) k(n)`
and `k(n) < 2 ^ e(n)`, then `sigmaTwoVerifier enc q k p W` verifies `A` with an existential block
of `q + k p` bits, a proof and the shifts, followed by a universal block of `p` bits. -/
theorem isAlternatingVerifier_sigmaTwoVerifier {e q k p : Polynomial ℕ} {W : α × List Bool → Bool}
    (h : IsMerlinArthurVerifierWithErrorExponent enc e q p W A)
    (hcover : ∀ n, p.eval n < e.eval n * k.eval n) (hshifts : ∀ n, k.eval n < 2 ^ e.eval n) :
    IsAlternatingVerifier enc true [q + k * p, p] (sigmaTwoVerifier enc q k p W) A := by
  intro a
  simp only [List.map_cons, List.map_nil, Polynomial.eval_add, Polynomial.eval_mul,
    alternation_true_cons, alternation_false_cons, alternation_nil, List.append_nil]
  constructor
  · -- some shifts cover the random strings accepted with the good proof
    intro ha
    obtain ⟨y, hy⟩ := (h a).1 ha
    have hS : 2 ^ e.eval (enc a).length * #(univ.filter fun r : BitString (p.eval (enc a).length) =>
        W (a, List.ofFn y ++ List.ofFn r) = true)ᶜ ≤ 2 ^ p.eval (enc a).length := by
      simpa only [compl_filter, Bool.not_eq_true] using hy
    obtain ⟨u, hu⟩ := BitString.exists_forall_exists_add_mem_of_two_pow_mul_card_compl_le _ hS
      (hcover _)
    refine ⟨List.ofFn y ++ List.ofFn (BitString.blocksEquiv.symm u), by simp, fun w hw => ?_⟩
    rw [← BitString.ofFn_ofList hw, sigmaTwoVerifier_append_ofFn (by simp),
      List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn, BitString.ofList_ofFn,
      BitString.block_blocksEquiv_symm]
    obtain ⟨i, hi⟩ := hu (BitString.ofList _ w)
    exact ⟨i, (mem_filter.1 hi).2⟩
  · -- no shifts cover the random strings accepted with any proof
    rintro ⟨w, hw, hall⟩
    by_contra ha
    have hy : List.ofFn (BitString.ofList (q.eval (enc a).length)
        (w.take (q.eval (enc a).length))) = w.take (q.eval (enc a).length) :=
      BitString.ofFn_ofList (by simp [hw])
    obtain ⟨r, hr⟩ := BitString.exists_forall_add_notMem_of_two_pow_mul_card_le _
      ((h a).2 ha (BitString.ofList _ (w.take (q.eval (enc a).length)))) (hshifts _)
      (BitString.block (BitString.ofList (k.eval (enc a).length * p.eval (enc a).length)
        (w.drop (q.eval (enc a).length))))
    obtain ⟨i, hi⟩ := (sigmaTwoVerifier_append_ofFn hw r).1 (hall _ List.length_ofFn)
    exact hr i (mem_filter.2 ⟨mem_univ _, by rwa [hy]⟩)

/-! ### The `Π₂` verifier of an Arthur–Merlin verifier -/

/-- The `Π₂` verifier of an Arthur–Merlin verifier `W` with random strings of length `p` and replies
of length `q`, with `k` shifts, all evaluated at the length of the encoded instance. The universal
block is `k` shifts of the random string, the existential block a random string `r` followed by
`k` replies, and the verifier accepts when `W` accepts `r` xor each shift with its reply. Bits
missing from a short string read as `false` (`Cslib.BitString.listRow`). -/
def piTwoVerifier (enc : α ↪ List Bool) (k p q : Polynomial ℕ) (W : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  let K := k.eval (enc x.1).length
  let m := p.eval (enc x.1).length
  let l := q.eval (enc x.1).length
  (List.range K).all fun i => W (x.1,
    List.zipWith Bool.xor (BitString.listRow m 0 (x.2.drop (K * m))) (BitString.listRow m i x.2) ++
      BitString.listRow l i (x.2.drop (K * m + m)))

/-- The `Π₂` verifier of a polynomial-time Arthur–Merlin verifier takes polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_piTwoVerifier {W : α × List Bool → Bool}
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool) (k p q : Polynomial ℕ) :
    ComputableInPolyTime (piTwoVerifier enc k p q W) (encPair enc encBits) encBool := by
  have hW := hW.tidy
  refine .of_tidy ?_
  unfold piTwoVerifier
  fun_prop

/-- On the shifts followed by any word `v`, the `Π₂` verifier accepts iff `W` accepts, for each
shift, the first `p(n)` bits of `v` xor the shift with the corresponding reply read from the rest
of `v`. -/
private theorem piTwoVerifier_append {k p q : Polynomial ℕ} {W : α × List Bool → Bool} {a : α}
    {u : List Bool} (hu : u.length = k.eval (enc a).length * p.eval (enc a).length)
    (v : List Bool) :
    piTwoVerifier enc k p q W (a, u ++ v) = true ↔
      ∀ i : Fin (k.eval (enc a).length), W (a, List.ofFn (BitString.ofList _ v +
        BitString.block (BitString.ofList (k.eval (enc a).length * p.eval (enc a).length) u) i) ++
          List.ofFn (BitString.block (BitString.ofList
            (k.eval (enc a).length * q.eval (enc a).length) (v.drop (p.eval (enc a).length))) i)) =
          true := by
  simp only [piTwoVerifier, List.all_eq_true, List.mem_range]
  rw [List.drop_left' hu, ← List.drop_drop, List.drop_left' hu]
  constructor
  · intro h i
    have h := h i i.2
    rwa [BitString.listRow_eq_ofFn (count := k.eval (enc a).length) _ i,
      BitString.listRow_eq_ofFn (count := k.eval (enc a).length) _ i,
      BitString.ofList_append_of_le (by simp [hu]), BitString.listRow_zero,
      ← BitString.ofFn_add] at h
  · intro h i hi
    rw [BitString.listRow_eq_ofFn (count := k.eval (enc a).length) _ ⟨i, hi⟩,
      BitString.listRow_eq_ofFn (count := k.eval (enc a).length) _ ⟨i, hi⟩,
      BitString.ofList_append_of_le (by simp [hu]), BitString.listRow_zero, ← BitString.ofFn_add]
    exact h ⟨i, hi⟩

/-- **Arthur–Merlin verifiers in `Π₂`.** If `W` is an Arthur–Merlin verifier for `A` with error at
most `2 ^ (-e(n))`, random strings of `p(n)` bits and replies of `q(n)` bits, and `k(n)` shifts
satisfy `p(n) < e(n) k(n)` and `k(n) < 2 ^ e(n)`, then `piTwoVerifier enc k p q W` verifies `A`
with a universal block of `k p` bits, the shifts, followed by an existential block of `p + k q`
bits, a random string and the replies. -/
theorem isAlternatingVerifier_piTwoVerifier {e k p q : Polynomial ℕ} {W : α × List Bool → Bool}
    (h : IsArthurMerlinVerifierWithErrorExponent enc e p q W A)
    (hcover : ∀ n, p.eval n < e.eval n * k.eval n) (hshifts : ∀ n, k.eval n < 2 ^ e.eval n) :
    IsAlternatingVerifier enc false [k * p, p + k * q] (piTwoVerifier enc k p q W) A := by
  intro a
  simp only [List.map_cons, List.map_nil, Polynomial.eval_add, Polynomial.eval_mul,
    alternation_true_cons, alternation_false_cons, alternation_nil, List.append_nil]
  constructor
  · -- against any shifts, some random string has an accepted reply after every shift
    intro ha w hw
    have hS : 2 ^ e.eval (enc a).length * #(univ.filter fun r : BitString (p.eval (enc a).length) =>
        ∃ y : BitString (q.eval (enc a).length), W (a, List.ofFn r ++ List.ofFn y) = true)ᶜ ≤
        2 ^ p.eval (enc a).length := by
      simpa only [compl_filter, not_exists, Bool.not_eq_true] using (h a).1 ha
    obtain ⟨r, hr⟩ := BitString.exists_forall_add_notMem_of_two_pow_mul_card_le _ hS (hshifts _)
      (BitString.block (BitString.ofList (k.eval (enc a).length * p.eval (enc a).length) w))
    have hY (i : Fin (k.eval (enc a).length)) : ∃ y : BitString (q.eval (enc a).length),
        W (a, List.ofFn (r + BitString.block (BitString.ofList
          (k.eval (enc a).length * p.eval (enc a).length) w) i) ++ List.ofFn y) = true := by
      simpa only [mem_compl, mem_filter, mem_univ, true_and, not_not] using hr i
    choose Y hY using hY
    refine ⟨List.ofFn r ++ List.ofFn (BitString.blocksEquiv.symm Y), by simp, ?_⟩
    rw [piTwoVerifier_append hw, BitString.ofList_append_of_le (by simp), BitString.ofList_ofFn,
      List.drop_left' List.length_ofFn, BitString.ofList_ofFn, BitString.block_blocksEquiv_symm]
    exact hY
  · -- some shifts carry every random string outside the strings with an accepted reply
    intro hall
    by_contra ha
    have hS : 2 ^ e.eval (enc a).length *
        #(univ.filter fun r : BitString (p.eval (enc a).length) =>
          ∃ y : BitString (q.eval (enc a).length), W (a, List.ofFn r ++ List.ofFn y) = true)ᶜᶜ ≤
        2 ^ p.eval (enc a).length := by
      rw [compl_compl]
      exact (h a).2 ha
    obtain ⟨u, hu⟩ := BitString.exists_forall_exists_add_mem_of_two_pow_mul_card_compl_le _ hS
      (hcover _)
    obtain ⟨v, -, hacc⟩ := hall (List.ofFn (BitString.blocksEquiv.symm u)) (by simp)
    rw [piTwoVerifier_append (by simp), BitString.ofList_ofFn,
      BitString.block_blocksEquiv_symm] at hacc
    obtain ⟨i, hi⟩ := hu (BitString.ofList _ v)
    exact (mem_compl.1 hi) (mem_filter.2 ⟨mem_univ _, _, hacc i⟩)

/-- The number of shifts and the error exponent `12 p + 1` cover random strings of
`12 (12 p + 1) p` bits. -/
private theorem eval_lt_mul (p : Polynomial ℕ) (n : ℕ) :
    (12 * (12 * p + 1) * p).eval n < (12 * p + 1).eval n * (12 * p + 1).eval n := by
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  nlinarith

end ArthurMerlin

open ArthurMerlin

/-- **`MA ⊆ Σ₂`** [Babai][Babai1985], [Arora and Barak, Section 8.2][AroraBarak09]: Merlin sends his
proof together with Lautemann's shifts. -/
theorem MA_subset_SigmaP_two : MA enc ⊆ SigmaP 2 enc := by
  rintro A ⟨q, p, V, hV, h⟩
  exact ⟨[q + (12 * p + 1) * (12 * (12 * p + 1) * p), 12 * (12 * p + 1) * p],
    sigmaTwoVerifier enc q (12 * p + 1) (12 * (12 * p + 1) * p)
      (merlinArthurRepeat enc q (6 * (12 * p + 1)) p V), rfl,
    (computableInPolyTime_sigmaTwoVerifier
      (computableInPolyTime_merlinArthurRepeat hV _ _ _) _ _ _),
    isAlternatingVerifier_sigmaTwoVerifier (h.repeatMajority _) (eval_lt_mul p)
      fun _ => Nat.lt_two_pow_self⟩

/-- **`AM ⊆ Π₂`** [Babai][Babai1985], [Babai and Moran][BabaiMoran1988],
[Arora and Barak, Section 8.2][AroraBarak09]: against any of Lautemann's shifts, Merlin exhibits a
random string and replies to all of its shifts. -/
theorem AM_subset_PiP_two : AM enc ⊆ PiP 2 enc := by
  rintro A ⟨p, q, V, hV, h⟩
  exact ⟨[(12 * p + 1) * (12 * (12 * p + 1) * p),
      12 * (12 * p + 1) * p + (12 * p + 1) * (12 * (12 * p + 1) * q)],
    piTwoVerifier enc (12 * p + 1) (12 * (12 * p + 1) * p) (12 * (12 * p + 1) * q)
      (arthurMerlinRepeat enc (6 * (12 * p + 1)) p q V), rfl,
    (computableInPolyTime_piTwoVerifier
      (computableInPolyTime_arthurMerlinRepeat hV _ _ _) _ _ _),
    isAlternatingVerifier_piTwoVerifier (h.repeatMajority _) (eval_lt_mul p)
      fun _ => Nat.lt_two_pow_self⟩

/-- **`MA ⊆ Π₂`**, from `MA ⊆ AM ⊆ Π₂`. -/
theorem MA_subset_PiP_two : MA enc ⊆ PiP 2 enc := MA_subset_AM.trans AM_subset_PiP_two

/-- **`MA ⊆ Σ₂ ∩ Π₂`** [Babai][Babai1985], [Arora and Barak, Section 8.2][AroraBarak09]. -/
theorem MA_subset_SigmaP_two_inter_PiP_two : MA enc ⊆ SigmaP 2 enc ∩ PiP 2 enc :=
  Set.subset_inter MA_subset_SigmaP_two MA_subset_PiP_two

/-- Every problem in `AM` lies in the polynomial hierarchy. -/
theorem AM_subset_PH : AM enc ⊆ PH enc := AM_subset_PiP_two.trans (PiP_subset_PH 2)

end Cslib.Complexity
