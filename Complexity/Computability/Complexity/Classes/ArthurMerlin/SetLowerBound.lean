/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ArthurMerlin
public import Complexity.Computability.Complexity.Classes.SBP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Probability.BitString.AffineHash

import Complexity.Computability.Complexity.Classes.ArthurMerlin.Amplification
import Complexity.Computability.Complexity.Classes.SharpP.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Probabilistic.LinearHash
import Complexity.Foundations.Data.BitString.List.Operations
import Complexity.Foundations.Data.BitString.WordCount

/-!
# The set lower bound protocol and `SBP ⊆ AM`

The set lower bound protocol of Goldwasser and Sipser [GoldwasserSipser1986]
[Arora and Barak, Section 8.2][AroraBarak09] lets Merlin convince Arthur that a set `S` with
membership certificates is large. Write `n` for the length of the encoded instance `a`, and let
`S a` be the strings `x` of `N(n)` bits with a certificate `z` of `c(n)` bits accepted by a
polynomial-time test, `R (a, x ++ z) = true` (`Cslib.Complexity.certifiedSet`). If a
polynomial-time threshold `K a > 0`, computed in binary, satisfies `K a ≤ #(S a)` on members and
`2 #(S a) ≤ K a` on non-members, then the problem is in `AM`
(`Cslib.Complexity.mem_AM_of_card_certifiedSet`).

The protocol:

* **Gap amplification.** Five copies of `S a` have at least `K a ^ 5` elements on members and at
  most `K a ^ 5 / 32` on non-members.
* **Normalisation.** With `ℓ = ⌊log₂ (K a ^ 5)⌋` and a polynomial `T(n) ≥ ℓ + 4`, appending
  `T(n)` bits whose first `ℓ` are `false` multiplies the size by `2 ^ (T(n) - ℓ)`
  (`Cslib.Complexity.SetLowerBound.card_amplifiedSet`): at least `2 ^ T(n)` elements on members
  and fewer than `2 ^ T(n) / 16` on non-members.
* **Hashing.** Arthur sends a random affine hash `h` to `m(n) = T(n) - 2` bits
  (`Cslib.BitString.LinearHash.affineHash`), and Merlin answers with an element `e` of the
  amplified set, the five certificates, and `h e = 0`. By pairwise independence, `0` is hit for at
  least three quarters of the hashes on members and for at most a quarter on non-members
  (`Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_notMem_image_le`,
  `Cslib.Probability.IsPairwiseIndependentHash.four_mul_card_filter_mem_image_le`).

With no certificates, `S a` is the set counted by a `#P` function, so `SBP ⊆ AM`
(`Cslib.Complexity.SBP_subset_AM`) [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006].

## Main definitions

* `Cslib.Complexity.certifiedSet`: the strings with an accepted certificate.
* `Cslib.Complexity.SetLowerBound.amplifiedSet`: five copies followed by normalising padding.
* `Cslib.Complexity.SetLowerBound.verifier`: the Arthur–Merlin verifier of the protocol.

## Main results

* `Cslib.Complexity.SetLowerBound.card_amplifiedSet`: the size of the amplified set.
* `Cslib.Complexity.SetLowerBound.exists_verifier_iff`: Merlin has an accepted answer exactly when
  the amplified set meets the kernel of Arthur's hash.
* `Cslib.Complexity.mem_AM_of_card_certifiedSet`: **the set lower bound protocol**.
* `Cslib.Complexity.SBP_subset_AM`.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [E. Böhler, C. Glaßer, D. Meister, *Error-bounded probabilistic computations between
  MA and AM*][BoehlerGlasserMeister2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM Cslib.Probability

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- The strings of `N(n)` bits that have a certificate of `c(n)` bits accepted by `R`, where `n`
is the length of the encoded instance. -/
def certifiedSet (enc : α ↪ List Bool) (N c : Polynomial ℕ) (R : α × List Bool → Bool) (a : α) :
    Finset (BitString (N.eval (enc a).length)) :=
  univ.filter fun x => ∃ z : BitString (c.eval (enc a).length),
    R (a, List.ofFn x ++ List.ofFn z) = true

namespace SetLowerBound

/-! ### Amplification and normalisation -/

/-- Five elements of `S`, followed by `T` bits whose first `ℓ` bits are `false`. -/
def amplifiedSet {N : ℕ} (S : Finset (BitString N)) (T ℓ : ℕ) :
    Finset (BitString (5 * N + T)) :=
  univ.filter fun e =>
    (∀ i, BitString.block (BitString.ofList (5 * N) ((List.ofFn e).take (5 * N))) i ∈ S) ∧
      (!(((List.ofFn e).drop (5 * N)).take ℓ).any fun b => b) = true

/-- **The size of the amplified set**: `#S ^ 5 ⬝ 2 ^ (T - ℓ)`. -/
theorem card_amplifiedSet {N : ℕ} (S : Finset (BitString N)) {T ℓ : ℕ} (h : ℓ ≤ T) :
    #(amplifiedSet S T ℓ) = #S ^ 5 * 2 ^ (T - ℓ) := by
  have key := BitString.card_filter_ofFn_add (5 * N) T fun u w =>
    (∀ i, BitString.block (BitString.ofList (5 * N) u) i ∈ S) ∧
      (!(w.take ℓ).any fun b => b) = true
  rw [amplifiedSet, key]
  have hpad : #{w : BitString T | (!((List.ofFn w).take ℓ).any fun b => b) = true} =
      2 ^ (T - ℓ) := by
    rw [BitString.card_filter_take h fun w => (!w.any fun b => b) = true,
      BitString.card_filter_not_any, mul_one]
  have hblocks : #{u : BitString (5 * N) | ∀ i, BitString.block u i ∈ S} = #S ^ 5 := by
    rw [show #S ^ 5 = ∏ _i : Fin 5, #S by simp, ← Fintype.card_piFinset]
    exact card_equiv BitString.blocksEquiv fun u => by simp [Fintype.mem_piFinset]
  simp only [BitString.ofList_ofFn]
  rw [← hblocks, card_filter, sum_mul]
  refine sum_congr rfl fun u _ => ?_
  by_cases hu : ∀ i, BitString.block u i ∈ S
  · simp only [hu, implies_true, true_and, ↓reduceIte, one_mul]
    exact hpad
  · simp [hu]

/-! ### The verifier -/

/-- The seed of an affine hash to `m` bits of strings of `M` bits, read from `m * M + m` bits: the
rows of the matrix, then the offset. -/
def seedEquiv (m M : ℕ) : BitString (m * M + m) ≃ (Fin m → BitString M) × BitString m :=
  (Fin.appendEquiv (m * M) m).symm.trans (BitString.blocksEquiv.prodCongr (Equiv.refl _))

/-- The Arthur–Merlin verifier of the set lower bound protocol, with element length `N`,
certificate length `c`, hash length `m`, padding length `T` and padding threshold `ℓ`, where `n` is
the length of the encoded instance. The string is Arthur's hash seed of `m(n) M(n) + m(n)` bits,
with `M(n) = 5 N(n) + T(n)`, followed by Merlin's element of `M(n)` bits and five certificates of
`c(n)` bits. The verifier accepts when the five blocks of the element have accepted certificates,
the first `ℓ` padding bits are `false` and the element hashes to zero
(`Cslib.BitString.LinearHash.wordHash`). Bits missing from a short string read as `false`. -/
def verifier (enc : α ↪ List Bool) (N c m T : Polynomial ℕ) (ℓ : α → ℕ)
    (R : α × List Bool → Bool) (x : α × List Bool) : Bool :=
  let n := (enc x.1).length
  let M := 5 * N.eval n + T.eval n
  let P := m.eval n * M + m.eval n
  let e := (x.2.drop P).take M
  ((List.range 5).all fun i => R (x.1, BitString.listRow (N.eval n) i (e.take (5 * N.eval n)) ++
      BitString.listRow (c.eval n) i (x.2.drop (P + M)))) &&
    (!((e.drop (5 * N.eval n)).take (ℓ x.1)).any fun b => b) &&
    !(List.zipWith Bool.xor (BitString.LinearHash.wordHash (m.eval n) (x.2.take P) e)
      (BitString.listRow (m.eval n) M (x.2.take P))).any fun b => b

/-- The verifier of the set lower bound protocol is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier {N c m T : Polynomial ℕ} {ℓ : α → ℕ}
    {R : α × List Bool → Bool} (hℓ : ComputableInPolyTime ℓ enc encUnary)
    (hR : ComputableInPolyTime R (encPair enc encBits) encBool) :
    ComputableInPolyTime (verifier enc N c m T ℓ R) (encPair enc encBits) encBool := by
  unfold verifier
  dsimp only
  fun_prop

/-- On a seed, an element and five certificates, the verifier accepts exactly when the blocks of
the element have accepted certificates, the padding starts with `ℓ` bits `false` and the affine
hash given by the seed sends the element to zero. -/
private theorem verifier_ofFn_append {N c m T : Polynomial ℕ} {ℓ : α → ℕ} {R : α × List Bool → Bool}
    (a : α) (r : BitString (m.eval (enc a).length * (5 * N.eval (enc a).length +
      T.eval (enc a).length) + m.eval (enc a).length))
    (e : BitString (5 * N.eval (enc a).length + T.eval (enc a).length))
    (z : BitString (5 * c.eval (enc a).length)) :
    verifier enc N c m T ℓ R (a, List.ofFn r ++ (List.ofFn e ++ List.ofFn z)) = true ↔
      (∀ i : Fin 5, R (a, List.ofFn (BitString.block (BitString.ofList (5 * N.eval (enc a).length)
        ((List.ofFn e).take (5 * N.eval (enc a).length))) i) ++
          List.ofFn (BitString.block z i)) = true) ∧
      (!(((List.ofFn e).drop (5 * N.eval (enc a).length)).take (ℓ a)).any fun b => b) = true ∧
      BitString.LinearHash.affineHash (seedEquiv _ _ r) e = 0 := by
  simp only [verifier, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  generalize (enc a).length = n at r e z ⊢
  have hdrop : (List.ofFn r ++ (List.ofFn e ++ List.ofFn z)).drop
      (m.eval n * (5 * N.eval n + T.eval n) + m.eval n) = List.ofFn e ++ List.ofFn z :=
    List.drop_left' List.length_ofFn
  have hdrop' : (List.ofFn r ++ (List.ofFn e ++ List.ofFn z)).drop
      (m.eval n * (5 * N.eval n + T.eval n) + m.eval n + (5 * N.eval n + T.eval n)) =
        List.ofFn z := by
    rw [← List.append_assoc]
    exact List.drop_left' (by simp)
  have htake : (List.ofFn r ++ (List.ofFn e ++ List.ofFn z)).take
      (m.eval n * (5 * N.eval n + T.eval n) + m.eval n) = List.ofFn r :=
    List.take_left' List.length_ofFn
  have hoffset : BitString.listRow (m.eval n) (5 * N.eval n + T.eval n) (List.ofFn r) =
      List.ofFn ((Fin.appendEquiv _ _).symm r).2 := by
    rw [List.ofFn_add, BitString.listRow, Nat.mul_comm (5 * N.eval n + T.eval n),
      List.drop_left' List.length_ofFn, List.take_left' List.length_ofFn]
    rfl
  have hhash : BitString.LinearHash.wordHash (m.eval n) (List.ofFn r) (List.ofFn e) =
      List.ofFn (BitString.LinearHash.hash
        (BitString.block ((Fin.appendEquiv _ _).symm r).1) e) := by
    rw [BitString.LinearHash.wordHash_eq_ofFn, List.ofFn_add, BitString.ofList_ofFn_append]
    rfl
  rw [hdrop, hdrop', htake, List.take_left' List.length_ofFn, hhash, hoffset,
    ← BitString.ofFn_add, BitString.not_any_ofFn_eq_true_iff, and_assoc]
  refine and_congr ⟨fun h i => ?_, fun h i hi => ?_⟩ Iff.rfl
  · have := h i i.2
    rwa [BitString.listRow_eq_ofFn (count := 5) _ i, BitString.listRow_eq_ofFn (count := 5) _ i,
      BitString.ofList_ofFn] at this
  · rw [BitString.listRow_eq_ofFn (count := 5) _ ⟨i, hi⟩,
      BitString.listRow_eq_ofFn (count := 5) _ ⟨i, hi⟩, BitString.ofList_ofFn]
    exact h ⟨i, hi⟩

/-- **Merlin's answers**: some answer is accepted exactly when the amplified set meets the kernel of
the affine hash given by Arthur's seed. -/
theorem exists_verifier_iff {N c m T : Polynomial ℕ} {ℓ : α → ℕ} {R : α × List Bool → Bool}
    (a : α) (r : BitString (m.eval (enc a).length * (5 * N.eval (enc a).length +
      T.eval (enc a).length) + m.eval (enc a).length)) :
    (∃ y : BitString (5 * N.eval (enc a).length + T.eval (enc a).length +
        5 * c.eval (enc a).length),
      verifier enc N c m T ℓ R (a, List.ofFn r ++ List.ofFn y) = true) ↔
      0 ∈ (amplifiedSet (certifiedSet enc N c R a) (T.eval (enc a).length) (ℓ a)).image
        (BitString.LinearHash.affineHash (seedEquiv _ _ r)) := by
  rw [mem_image]
  constructor
  · rintro ⟨y, hy⟩
    rw [List.ofFn_add (f := y), verifier_ofFn_append] at hy
    obtain ⟨hrows, hpad, hzero⟩ := hy
    refine ⟨_, mem_filter.2 ⟨mem_univ _, fun i => mem_filter.2 ⟨mem_univ _, _, hrows i⟩, hpad⟩,
      hzero⟩
  · rintro ⟨e, he, hzero⟩
    obtain ⟨-, hblocks, hpad⟩ := mem_filter.1 he
    have hz (i : Fin 5) := (mem_filter.1 (hblocks i)).2
    choose z hz using hz
    refine ⟨Fin.append e (BitString.blocksEquiv.symm z), ?_⟩
    rw [List.ofFn_fin_append, verifier_ofFn_append]
    refine ⟨fun i => ?_, hpad, hzero⟩
    rw [BitString.block_blocksEquiv_symm]
    exact hz i

/-- All certificates are rejected by `verifier` on `r` if and only if `0` is not in the image of
`amplifiedSet` under the affine hash seeded by `r`. -/
private theorem forall_verifier_eq_false_iff (N c m T : Polynomial ℕ) (ℓ : α → ℕ)
    (R : α × List Bool → Bool) (a : α)
    (r : BitString (m.eval (enc a).length * (5 * N.eval (enc a).length +
      T.eval (enc a).length) + m.eval (enc a).length)) :
    (∀ y : BitString (5 * N.eval (enc a).length + T.eval (enc a).length +
      5 * c.eval (enc a).length), verifier enc N c m T ℓ R (a, List.ofFn r ++ List.ofFn y) =
        false) ↔
      0 ∉ (amplifiedSet (certifiedSet enc N c R a) (T.eval (enc a).length) (ℓ a)).image
        (BitString.LinearHash.affineHash (seedEquiv _ _ r)) := by
  rw [← exists_verifier_iff]
  simp

/-- Lower and upper bounds on `#(amplifiedSet S T (Nat.log 2 (K ^ 5)))` for a positive threshold `K`
when `T = m + 2` and `Nat.log 2 (K ^ 5) ≤ T`. -/
private theorem card_amplifiedSet_bounds {N m T K : ℕ} (S : Finset (BitString N)) (hKpos : 0 < K)
    (hTm : T = m + 2) (hℓT : Nat.log 2 (K ^ 5) ≤ T) :
    (K ≤ #S → 4 * Fintype.card (BitString m) ≤ #(amplifiedSet S T (Nat.log 2 (K ^ 5)))) ∧
      (2 * #S ≤ K → 4 * #(amplifiedSet S T (Nat.log 2 (K ^ 5))) ≤ Fintype.card (BitString m)) := by
  set ℓ := Nat.log 2 (K ^ 5)
  have hcard := card_amplifiedSet S hℓT
  have hY : Fintype.card (BitString m) = 2 ^ m := BitString.card
  have hKℓ : 2 ^ ℓ ≤ K ^ 5 := Nat.pow_log_le_self 2 (pow_ne_zero 5 hKpos.ne')
  have hKℓ' : K ^ 5 < 2 ^ (ℓ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hsplit : 2 ^ T = 2 ^ ℓ * 2 ^ (T - ℓ) := by
    rw [← pow_add, Nat.add_sub_cancel' hℓT]
  have h4 : 2 ^ T = 4 * 2 ^ m := by
    rw [hTm, pow_add]
    ring
  refine ⟨fun hmem => ?_, fun hnot => ?_⟩
  · rw [hY, hcard, ← h4, hsplit]
    exact Nat.mul_le_mul_right _ (hKℓ.trans (Nat.pow_le_pow_left hmem 5))
  · have h32 : 32 * #S ^ 5 ≤ K ^ 5 := by
      have := Nat.pow_le_pow_left hnot 5
      rw [mul_pow] at this
      simpa using this
    have h16 : 16 * #S ^ 5 < 2 ^ ℓ := by
      have h2 : 2 ^ (ℓ + 1) = 2 ^ ℓ * 2 := pow_succ 2 ℓ
      omega
    rw [hY, hcard]
    have := Nat.mul_le_mul_right (2 ^ (T - ℓ)) h16.le
    rw [← hsplit, h4] at this
    nlinarith

end SetLowerBound

open SetLowerBound

/-- **The set lower bound protocol** of Goldwasser and Sipser [GoldwasserSipser1986]
[Arora and Barak, Section 8.2][AroraBarak09]. Let `R` be a polynomial-time test, `N` and `c`
polynomials, and `K` a polynomial-time threshold in binary with `K a > 0`. If the set of strings
of `N(n)` bits with a certificate of `c(n)` bits accepted by `R` has at least `K a` elements for
every member `a` of `A`, and at most `K a / 2` for every non-member, then `A ∈ AM`. -/
theorem mem_AM_of_card_certifiedSet {N c : Polynomial ℕ} {R : α × List Bool → Bool} {K : α → ℕ}
    (hR : ComputableInPolyTime R (encPair enc encBits) encBool)
    (hK : ComputableInPolyTime K enc encNat) (hKpos : ∀ a, 0 < K a)
    (hmem : ∀ a ∈ A, K a ≤ #(certifiedSet enc N c R a))
    (hnot : ∀ a ∉ A, 2 * #(certifiedSet enc N c R a) ≤ K a) : A ∈ AM enc := by
  -- normalise the threshold `K a ^ 5` to a power of two
  set ℓ : α → ℕ := fun a => Nat.log 2 (K a ^ 5) with hℓdef
  have hℓ : ComputableInPolyTime ℓ enc encUnary :=
    ComputableInPolyTime.binary_log_two.comp
      (hK.binary_pow' (ComputableInPolyTime.const 5))
  obtain ⟨B, hB⟩ := hℓ.polyBounded.exists_polynomial
  set m : Polynomial ℕ := B + 2 with hm
  set T : Polynomial ℕ := B + 4 with hT
  refine ⟨m * (5 * N + T) + m, 5 * N + T + 5 * c, verifier enc N c m T ℓ R,
    (computableInPolyTime_verifier hℓ hR), fun a => ?_⟩
  have hP : (m * (5 * N + T) + m).eval (enc a).length = m.eval (enc a).length *
      (5 * N.eval (enc a).length + T.eval (enc a).length) + m.eval (enc a).length := by simp
  have hQ : (5 * N + T + 5 * c).eval (enc a).length = 5 * N.eval (enc a).length +
      T.eval (enc a).length + 5 * c.eval (enc a).length := by simp
  rw [hP, hQ]
  simp only [forall_verifier_eq_false_iff, exists_verifier_iff]
  set n := (enc a).length
  have hh := (BitString.LinearHash.isPairwiseIndependentHash_affineHash
    (m.eval n) (5 * N.eval n + T.eval n)).comp_seedEquiv (seedEquiv _ _)
  have hbnds := card_amplifiedSet_bounds (certifiedSet enc N c R a) (hKpos a)
    (show T.eval n = m.eval n + 2 by simp [hT, hm])
    (by simp only [hT, Polynomial.eval_add, Polynomial.eval_ofNat]; linarith [hB a])
  constructor
  · -- members: the amplified set has at least `4 ⬝ 2 ^ m(n)` elements
    intro ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
      hh.four_mul_card_filter_notMem_image_le (hbnds.1 (hmem a ha)) 0
  · -- non-members: the amplified set has at most `2 ^ m(n) / 4` elements
    intro ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, not_not] using
      hh.four_mul_card_filter_mem_image_le (hbnds.2 (hnot a ha)) 0

/-- **`SBP ⊆ AM`** [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006]: the set counted by the
`#P` function of an `SBP` problem needs no certificates, and the set lower bound protocol applies
to it with the `SBP` threshold. -/
theorem SBP_subset_AM : SBP enc ⊆ AM enc := by
  intro A hA
  obtain ⟨f, ⟨s, W, hW, hf⟩, k, hk, hkpos, hA⟩ := mem_SBP_iff_exists_pos_threshold.mp hA
  have hcount (a : α) : #(certifiedSet enc s 0
      (fun x => W (x.1, x.2.take (s.eval (enc x.1).length))) a) = f a := by
    rw [hf a, acceptCount]
    congr 1
    refine filter_congr fun x _ => ?_
    simp only [List.take_left' List.length_ofFn]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun _ => false, h⟩⟩
  refine mem_AM_of_card_certifiedSet (N := s) (c := 0)
    (R := fun x => W (x.1, x.2.take (s.eval (enc x.1).length)))
    ((hW.comp ((ComputableInPolyTime.fst enc encBits).prod
      (ComputableInPolyTime.bitsTakeWithInput (.snd enc encBits)
        (((ComputableInPolyTime.unary_eval s).comp
          (ComputableInPolyTime.encoding_length enc)).comp (.fst enc encBits))))))
    hk hkpos (fun a ha => ?_) fun a ha => ?_
  · rw [hcount]
    exact (hA a).1 ha
  · rw [hcount]
    exact ((hA a).2 ha).le

end Cslib.Complexity
