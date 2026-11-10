/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: candidate
public import CslibFrontier.Crypto.Primitives.BlockCipher.CBCMAC
public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Probability.Uniform
/-!
# Length-Prepended CBC-MAC for Variable-Length Messages

Basic CBC-MAC is secure only for messages of one fixed length ([KatzLindell2020], Section 4.4.1,
Theorem 4.10). One fix described in [KatzLindell2020] (Section 4.4.1, p. 122, Figure 4.2) prepends
the length of the message, encoded as an `n`-bit block, and then computes basic CBC-MAC on the
result. The book derives its security from the prefix-free analysis of Section 4.4.2: the
length-prepended encoding is prefix-free ([KatzLindell2020], Exercise 4.18), and CBC-MAC on
prefix-free inputs is a pseudorandom function ([KatzLindell2020], Theorems 4.11 and 4.12).

This file carries out that argument for block-aligned messages of `0` to `L` blocks, where the
length block encodes the number of blocks. Every adaptive distinguisher that asks such messages is
translated into a distinguisher against basic CBC-MAC on inputs of at most `L + 1` blocks, whose
queries are prefix-free whenever the length encoding is injective. The prefix-free bound of
`abs_cbcRealSuccess_sub_cbcIdealSuccess_le` then gives the variable-length bound
`q ^ 2 * (L + 1) ^ 2 / 2 ^ n`.

## Main definitions

* `LengthPrependedInput`, `lengthPrependedBlocks`: block-aligned messages of at most `L` blocks.
* `prependLength`, `lengthPrependedCbcMac`: prepend the encoded block count and run basic
  CBC-MAC.
* `blockCountBlock`: the block count `k` written as an `n`-bit block, injective when `L < 2 ^ n`.
* `LengthPrependedSpec`, `prependLengthQueries`, `lengthPrependedRealSuccess`,
  `lengthPrependedIdealSuccess`: adaptive variable-length distinguishers, their translation into
  CBC-MAC distinguishers, and real/ideal acceptance probabilities.

## Main results

* `prependLength_injective`, `not_isPrefix_prependLength`, `cbcPrefixFree_of_forall_mem_range`:
  length prepending is injective and, for an injective length encoding, prefix-free
  ([KatzLindell2020], Exercise 4.18).
* `cbcRealSuccess_map_prependLengthQueries`, `cbcIdealSuccess_map_prependLengthQueries`: the
  translated distinguisher has the same real and ideal acceptance probabilities.
* `abs_lengthPrependedRealSuccess_sub_lengthPrependedIdealSuccess_le`: variable-length security
  of length-prepended CBC-MAC with a random function,
  `|real - ideal| ≤ q ^ 2 * (L + 1) ^ 2 / 2 ^ n` ([KatzLindell2020], Section 4.4.2,
  Theorems 4.11 and 4.12).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 4.4 (pp. 120–125) and Exercise 4.18 (p. 143).
-/
public section
namespace Cslib.Crypto
open Cslib.Probability
open scoped ENNReal
variable {n : ℕ}
/-! ### Section 1: The Length-Prepended Encoding Is Prefix-Free -/
/-- Block-aligned messages of at most `L` blocks: a block count `k ≤ L` and `k` blocks of `n`
  bits. The empty message is included. -/
abbrev LengthPrependedInput (n L : ℕ) := Σ k : Fin (L + 1), Fin k.val → BitString n
/-- Decidable equality on `LengthPrependedInput n L`, transported from the sigma type. -/
instance instDecidableEqLengthPrependedInput {L : ℕ} : DecidableEq (LengthPrependedInput n L) :=
  inferInstanceAs (DecidableEq (Σ k : Fin (L + 1), Fin k.val → BitString n))
/-- The list of blocks of a block-aligned message. -/
@[expose]
def lengthPrependedBlocks {L : ℕ} (x : LengthPrependedInput n L) : List (BitString n) :=
  List.ofFn x.2
@[simp] theorem length_lengthPrependedBlocks {L : ℕ} (x : LengthPrependedInput n L) :
    (lengthPrependedBlocks x).length = x.1.val :=
  List.length_ofFn
/-- A block-aligned message is determined by its list of blocks. -/
theorem lengthPrependedBlocks_injective {L : ℕ} :
    Function.Injective (lengthPrependedBlocks (n := n) (L := L)) := by
  rintro ⟨k, f⟩ ⟨k', f'⟩ h
  have hk : k = k' := Fin.ext (by simpa using congrArg List.length h)
  subst hk
  have hf : f = f' := List.ofFn_injective h
  rw [hf]
/-- Prepend the encoded block count `encodeLength x.1` to a block-aligned message `x`, giving a
  nonempty CBC-MAC input of `x.1 + 1 ≤ L + 1` blocks. -/
@[expose]
def prependLength {L : ℕ} (encodeLength : Fin (L + 1) → BitString n)
    (x : LengthPrependedInput n L) : CBCInput n (L + 1) :=
  ⟨x.1, Fin.cons (encodeLength x.1) x.2⟩
@[simp] theorem cbcInputBlocks_prependLength {L : ℕ} (encodeLength : Fin (L + 1) → BitString n)
    (x : LengthPrependedInput n L) :
    cbcInputBlocks (prependLength encodeLength x) =
      encodeLength x.1 :: lengthPrependedBlocks x :=
  List.ofFn_cons _ _
/-- Length-prepended CBC-MAC ([KatzLindell2020], Section 4.4.1, p. 122, Figure 4.2): basic
  CBC-MAC of the encoded block count followed by the message blocks. -/
@[expose]
def lengthPrependedCbcMac {L : ℕ} (g : BitString n → BitString n)
    (encodeLength : Fin (L + 1) → BitString n) (x : LengthPrependedInput n L) : BitString n :=
  cbcMacFinite g (prependLength encodeLength x)
/-- Length-prepended CBC-MAC chains the message blocks starting from `g (encodeLength x.1)`. -/
theorem lengthPrependedCbcMac_eq {L : ℕ} (g : BitString n → BitString n)
    (encodeLength : Fin (L + 1) → BitString n) (x : LengthPrependedInput n L) :
    lengthPrependedCbcMac g encodeLength x =
      cbcMacBlocks g (g (encodeLength x.1)) (lengthPrependedBlocks x) := by
  rw [lengthPrependedCbcMac, cbcMacFinite, cbcInputBlocks_prependLength, cbcMacBlocks_cons,
    zero_add]
/-- Prepending the block count is injective, for any length encoding. -/
theorem prependLength_injective {L : ℕ} (encodeLength : Fin (L + 1) → BitString n) :
    Function.Injective (prependLength encodeLength) := by
  intro x y h
  have h' := congrArg cbcInputBlocks h
  rw [cbcInputBlocks_prependLength, cbcInputBlocks_prependLength] at h'
  exact lengthPrependedBlocks_injective (List.cons_eq_cons.mp h').2
/-- **Length prepending is prefix-free ([KatzLindell2020], Exercise 4.18, p. 143)**: with an
  injective length encoding, no length-prepended input is a prefix of a different one. -/
theorem not_isPrefix_prependLength {L : ℕ} {encodeLength : Fin (L + 1) → BitString n}
    (he : Function.Injective encodeLength) {x y : LengthPrependedInput n L} (hxy : x ≠ y) :
    ¬(cbcInputBlocks (prependLength encodeLength x)).IsPrefix
      (cbcInputBlocks (prependLength encodeLength y)) := by
  rw [cbcInputBlocks_prependLength, cbcInputBlocks_prependLength, List.cons_prefix_cons]
  rintro ⟨hk, hp⟩
  refine hxy (lengthPrependedBlocks_injective (hp.eq_of_length ?_))
  rw [length_lengthPrependedBlocks, length_lengthPrependedBlocks, he hk]
/-- Every list of length-prepended inputs is prefix-free, for an injective length encoding. -/
theorem cbcPrefixFree_of_forall_mem_range {L : ℕ} {encodeLength : Fin (L + 1) → BitString n}
    (he : Function.Injective encodeLength) {queries : List (CBCInput n (L + 1))}
    (hq : ∀ z ∈ queries, z ∈ Set.range (prependLength encodeLength)) :
    CBCPrefixFree queries := by
  intro x hx y hy hxy
  obtain ⟨x', rfl⟩ := hq x hx
  obtain ⟨y', rfl⟩ := hq y hy
  exact not_isPrefix_prependLength he fun h => hxy (congrArg _ h)
/-- The block count `k ≤ L` written as the `n`-bit block with binary value `k`. [KatzLindell2020]
  prepend the bit length `|m|`; for block-aligned messages the block count carries the same
  information, and any injective encoding works. This one is injective when `L < 2 ^ n`. -/
@[expose]
def blockCountBlock {L : ℕ} (h : L < 2 ^ n) (k : Fin (L + 1)) : BitString n :=
  (BitString.equivFin n).symm (Fin.castLE h k)
theorem blockCountBlock_injective {L : ℕ} (h : L < 2 ^ n) :
    Function.Injective (blockCountBlock h) :=
  (BitString.equivFin n).symm.injective.comp (Fin.castLE_injective h)
/-! ### Section 2: Adaptive Variable-Length Distinguishers -/
/-- The oracle interface of variable-length distinguishers: a query is a block-aligned message of
  at most `L` blocks, answered by an `n`-bit tag. -/
abbrev LengthPrependedSpec (n L : ℕ) : OracleSpec (LengthPrependedInput n L) :=
  fun _ => BitString n
/-- Translate a variable-length distinguisher into a CBC-MAC distinguisher that asks the
  length-prepended version of each query. -/
@[expose]
def prependLengthQueries {L : ℕ} {α : Type} (encodeLength : Fin (L + 1) → BitString n)
    (program : OracleComp (LengthPrependedSpec n L) α) :
    OracleComp (CBCOracleSpec n (L + 1)) α :=
  OracleComp.interpret
    (fun x => OracleComp.query (spec := CBCOracleSpec n (L + 1)) (prependLength encodeLength x))
    program
@[simp] theorem prependLengthQueries_pure {L : ℕ} {α : Type}
    (encodeLength : Fin (L + 1) → BitString n) (a : α) :
    prependLengthQueries encodeLength (pure a : OracleComp (LengthPrependedSpec n L) α) =
      pure a :=
  OracleComp.interpret_pure _ _
@[simp] theorem prependLengthQueries_query_bind {L : ℕ} {α : Type}
    (encodeLength : Fin (L + 1) → BitString n) (x : LengthPrependedInput n L)
    (next : BitString n → OracleComp (LengthPrependedSpec n L) α) :
    prependLengthQueries encodeLength (OracleComp.query x >>= next) =
      OracleComp.query (spec := CBCOracleSpec n (L + 1)) (prependLength encodeLength x) >>=
        fun y => prependLengthQueries encodeLength (next y) := by
  simp only [prependLengthQueries, OracleComp.interpret_bind, OracleComp.interpret_query]
/-- Answering the translated program with a CBC-MAC oracle is answering the original program with
  the oracle precomposed with `prependLength`. -/
theorem interpret_prependLengthQueries {L : ℕ} {α : Type} {m : Type → Type*} [Monad m]
    [LawfulMonad m] (encodeLength : Fin (L + 1) → BitString n)
    (oracle : CBCInput n (L + 1) → m (BitString n))
    (program : OracleComp (LengthPrependedSpec n L) α) :
    OracleComp.interpret oracle (prependLengthQueries encodeLength program) =
      OracleComp.interpret (fun x => oracle (prependLength encodeLength x)) program := by
  rw [prependLengthQueries, OracleComp.interpret_interpret]
  simp only [OracleComp.interpret_query]
/-- Every query that the translated program asks is length-prepended, and a program that asks
  at most `q` queries leads to at most `q` CBC-MAC queries. -/
theorem cbcQueryRun_prependLengthQueries {L q : ℕ} (encodeLength : Fin (L + 1) → BitString n)
    {program : OracleComp (LengthPrependedSpec n L) Bool}
    (hq : OracleComp.IsQueryBounded program q) (oracle : CBCInput n (L + 1) → BitString n) :
    (∀ z ∈ (cbcQueryRun oracle (prependLengthQueries encodeLength program)).2,
        z ∈ Set.range (prependLength encodeLength)) ∧
      (cbcQueryRun oracle (prependLengthQueries encodeLength program)).2.length ≤ q := by
  unfold OracleComp.IsQueryBounded at hq
  induction hq with
  | pure a k => simp
  | liftBind x cont k hcont ih =>
    rw [prependLengthQueries_query_bind, cbcQueryRun_query_bind]
    obtain ⟨hrange, hlength⟩ := ih (oracle (prependLength encodeLength x))
    refine ⟨fun z hz => ?_, ?_⟩
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨x, rfl⟩
      · exact hrange z hz
    · rw [List.length_cons]
      omega
/-- Real-world acceptance probability of a distribution `D` over variable-length distinguishers
  interacting with `lengthPrependedCbcMac g encodeLength` for a uniform random function
  `g : BitString n → BitString n`. -/
@[expose]
noncomputable def lengthPrependedRealSuccess {L : ℕ} (encodeLength : Fin (L + 1) → BitString n)
    (D : PMF (OracleComp (LengthPrependedSpec n L) Bool)) : ℝ :=
  ((do
    let g ← PMF.uniformOfFintype (BitString n → BitString n)
    let tree ← D
    return OracleComp.interpret (m := Id) (lengthPrependedCbcMac g encodeLength) tree :
      PMF Bool) true).toReal
/-- Ideal-world acceptance probability of a distribution `D` over variable-length distinguishers
  interacting with a uniform random function `f : LengthPrependedInput n L → BitString n`. -/
@[expose]
noncomputable def lengthPrependedIdealSuccess (n L : ℕ)
    (D : PMF (OracleComp (LengthPrependedSpec n L) Bool)) : ℝ :=
  ((do
    let f ← PMF.uniformOfFintype (LengthPrependedInput n L → BitString n)
    let tree ← D
    return OracleComp.interpret (m := Id) f tree : PMF Bool) true).toReal
private theorem bind_map_bind_pure {G X Y : Type} (U : PMF G) (D : PMF X) (P : X → Y)
    (h : G → Y → Bool) :
    (do let g ← U; let t ← D.map P; return h g t : PMF Bool) =
      (do let g ← U; let t ← D; return h g (P t) : PMF Bool) := by
  change U.bind (fun g => (D.map P).bind fun t => PMF.pure (h g t)) =
    U.bind (fun g => D.bind fun t => PMF.pure (h g (P t)))
  simp only [PMF.bind_map]
  rfl
/-- Precomposing a uniform random function with an injective map gives a uniform random
  function. -/
private theorem uniformOfFintype_map_comp {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] {φ : X → Y} (hφ : Function.Injective φ) :
    (PMF.uniformOfFintype (Y → BitString n)).map (fun f => f ∘ φ) =
      PMF.uniformOfFintype (X → BitString n) :=
  PMF.uniformOfFintype_map_addHom
    { toFun := fun f => f ∘ φ, map_zero' := rfl, map_add' := fun _ _ => rfl }
    fun g => ⟨Function.extend φ g 0, funext fun x => hφ.extend_apply g 0 x⟩
/-- The translated distinguisher has the same real-world acceptance probability. -/
theorem cbcRealSuccess_map_prependLengthQueries {L : ℕ}
    (encodeLength : Fin (L + 1) → BitString n)
    (D : PMF (OracleComp (LengthPrependedSpec n L) Bool)) :
    cbcRealSuccess n (L + 1) (D.map (prependLengthQueries encodeLength)) =
      lengthPrependedRealSuccess encodeLength D := by
  unfold cbcRealSuccess lengthPrependedRealSuccess
  rw [bind_map_bind_pure _ D (prependLengthQueries encodeLength)
    (fun g t => (cbcQueryRun (cbcMacFinite g) t).1)]
  simp only [cbcQueryRun_fst, interpret_prependLengthQueries]
  rfl
/-- The translated distinguisher has the same ideal-world acceptance probability: a uniform
  random function on CBC-MAC inputs, precomposed with the injective map `prependLength`, is a
  uniform random function on block-aligned messages. -/
theorem cbcIdealSuccess_map_prependLengthQueries {L : ℕ}
    (encodeLength : Fin (L + 1) → BitString n)
    (D : PMF (OracleComp (LengthPrependedSpec n L) Bool)) :
    cbcIdealSuccess n (L + 1) (D.map (prependLengthQueries encodeLength)) =
      lengthPrependedIdealSuccess n L D := by
  unfold cbcIdealSuccess lengthPrependedIdealSuccess
  rw [bind_map_bind_pure _ D (prependLengthQueries encodeLength)
    (fun f t => (cbcQueryRun f t).1),
    ← uniformOfFintype_map_comp (prependLength_injective encodeLength)]
  simp only [cbcQueryRun_fst, interpret_prependLengthQueries]
  change _ = ((PMF.map _ _).bind _ _).toReal
  rw [PMF.bind_map]
  rfl
/-- **Variable-length security of length-prepended CBC-MAC ([KatzLindell2020], Section 4.4.2,
  Theorems 4.11 and 4.12, pp. 123–124, with Exercise 4.18)**: for an injective length encoding
  and every distribution `D` over distinguishers that ask at most `q` block-aligned messages of at
  most `L` blocks, length-prepended CBC-MAC with a uniform random function is
  `q ^ 2 * (L + 1) ^ 2 / 2 ^ n`-close to a uniform random function on such messages. -/
theorem abs_lengthPrependedRealSuccess_sub_lengthPrependedIdealSuccess_le (n q L : ℕ)
    {encodeLength : Fin (L + 1) → BitString n} (he : Function.Injective encodeLength)
    (D : PMF (OracleComp (LengthPrependedSpec n L) Bool))
    (hD : ∀ tree, D tree ≠ 0 → OracleComp.IsQueryBounded tree q) :
    |lengthPrependedRealSuccess encodeLength D - lengthPrependedIdealSuccess n L D| ≤
      (q : ℝ) ^ 2 * ((L : ℝ) + 1) ^ 2 / (2 : ℝ) ^ n := by
  rw [← cbcRealSuccess_map_prependLengthQueries,
    ← cbcIdealSuccess_map_prependLengthQueries encodeLength D]
  have h := abs_cbcRealSuccess_sub_cbcIdealSuccess_le n q (L + 1)
    (D.map (prependLengthQueries encodeLength)) fun tree htree oracle => by
      obtain ⟨T, hT, rfl⟩ :=
        (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr htree)
      obtain ⟨hrange, hlength⟩ := cbcQueryRun_prependLengthQueries encodeLength
        (hD T ((PMF.mem_support_iff _ _).mp hT)) oracle
      exact ⟨cbcPrefixFree_of_forall_mem_range he hrange, hlength⟩
  push_cast at h
  exact h
end Cslib.Crypto
