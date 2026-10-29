/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Languages.Probabilistic.QueryCount
public import Complexity.Languages.Probabilistic.RandomPermutation
public import Complexity.Languages.Probabilistic.Sum
public import Mathlib.Data.Fintype.Perm
import Complexity.Languages.Probabilistic.Simulation
import Complexity.Probability.BitString
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Even–Mansour cipher in the ideal-permutation model

The Even–Mansour construction ([BonehShoup2023], Section 4.7; [EvenMansour1997]) builds a block
cipher from a single public permutation `π : Equiv.Perm G` on a finite group `G` by XORing (or
adding in `G`) independent pre-whitening and post-whitening keys `(k₀, k₁) ∈ G × G`:
$$E((k_0, k_1), x) = \pi(x + k_0) + k_1, \qquad D((k_0, k_1), y) = \pi^{-1}(y - k_1) - k_0.$$
In the single-key variant ([DunkelmanKellerShamir2012]), `k₀ = k₁ = k`.

We formalize four aspects of the Even–Mansour construction:

1. **Algebraic structure and one-query secrecy**: `evenMansourEquiv π k₀ k₁ : Equiv.Perm G`
   bundles encryption and decryption as a permutation of `G`, satisfies the inverse-cipher
   conjugation law `(evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm (-k₁) (-k₀)` (which
   swaps `k₀` and `k₁` over any group of exponent two such as `BitString n`), acts as a bijection
   on `Equiv.Perm G` for every fixed key pair (`evenMansourPermEquiv`), and achieves perfect
   one-query secrecy for any fixed `π` (`map_prod_evenMansourEncrypt_uniformOfFintype`).
2. **Necessity of both whitening keys ([BonehShoup2023], Section 4.7)**: omitting post-whitening
   (`preWhitenEquiv π k₀ x = π (x + k₀)`) or pre-whitening (`postWhitenEquiv π k₁ x = π x + k₁`)
   allows an explicit 2-query adversary (making `1` cipher query and `1` primitive permutation
   query, `IsCallBounded _ 1 1`) to recover the secret key with probability `1` and achieve
   key-recovery game advantage `1 - |G|⁻¹` against an independent uniform permutation and uniform
   target key (`advantage_preWhitenKeyRecoveryGame_eq`, `advantage_postWhitenKeyRecoveryGame_eq`).
3. **One-sided query security and lazy ideal-permutation equivalence**: because
   `evenMansourPermEquiv k₀ k₁` is a bijection on `Equiv.Perm G`, any adversary that queries only
   the cipher oracle (`liftLeft`) or only the primitive permutation oracle (`liftRight`) has zero
   distinguishing advantage between the real Even–Mansour game and two independent uniform
   permutations (`advantage_evenMansourRealGame_liftLeft_eq_zero`,
   `advantage_evenMansourRealGame_liftRight_eq_zero`). Moreover, `evenMansourIdealGame` is
   identically distributed to running two independent lazy bidirectional permutation samplers
   (`idealLazyHandler`) from empty caches (`evenMansourIdealGame_eq_lazy`).
4. **Bad-key transcript intersection bound ([BonehShoup2023], Theorem 4.10)**: given a cipher
   transcript `T_e : List (G × G)` and a primitive permutation transcript `T_π : List (G × G)`, a
   key `(k₀, k₁)` is bad (`isBadEvenMansourKey T_e T_π k`) when some `(x, y) ∈ T_e` and
   `(u, v) ∈ T_π` collide on the internal permutation input (`x + k₀ = u`) or output
   (`y - k₁ = v`). Outside this bad set, the internal permutation queries made through the cipher
   are disjoint in both domain and range from the direct queries to `π`
   (`disjoint_of_isBadEvenMansourKey_eq_false`), and when `T_e` and `T_π` are consistent with
   `evenMansourEquiv π k₀ k₁` and `π`, output collisions reduce to input collisions
   (`isBadKeyPair_eq_decide_of_evenMansourEquiv`). Under a uniform two-key `(k₀, k₁)` or single
   key `k`, the bad-key probability is at most `2 * |T_e| * |T_π| / |G|`
    (`toOuterMeasure_isBadEvenMansourKey_toReal_le`,
    `toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le`). For any adaptive distinguisher satisfying
    `IsCallBounded program Q_e Q_π`, `OracleComp.IsCostBounded.transcript_cost_le` bounds every
    supported transcript by `|T_e| ≤ Q_e` and `|T_π| ≤ Q_π`, yielding the `2 * Q_e * Q_π / |G|`
    bad-key bound on every supported execution path (`IsCallBounded.badEvenMansourKey_toReal_le`,
    `IsCallBounded.badSingleKeyEvenMansour_toReal_le`). Coupling `idealLazyHandler` to a single
    key-shifted lazy permutation cache bounds the distinguishing advantage of any adaptive
    (`Q_e`, `Q_π`)-query adversary against both two-key and single-key Even–Mansour by
    `2 * Q_e * Q_π / |G|` (`advantage_evenMansourRealGame_evenMansourIdealGame_le`,
    `advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le`).

## Main definitions

* `Cslib.Crypto.EvenMansour.evenMansourEncrypt`, `evenMansourDecrypt`, `evenMansourEquiv`,
  `singleKeyEvenMansourEquiv`: Even–Mansour encryption, decryption, and bundled permutations.
* `Cslib.Crypto.EvenMansour.preWhitenEquiv`, `postWhitenEquiv`, `preWhitenKeyRecoveryAttack`,
  `postWhitenKeyRecoveryAttack`: single-whitening variants and 2-query key-recovery attacks.
* `Cslib.Crypto.EvenMansour.EvenMansourSpec`, `IsCallBounded`:
  bidirectional cipher and primitive permutation oracle interface and separate query budgets.
* `Cslib.Crypto.EvenMansour.evenMansourRealGame`, `singleKeyEvenMansourRealGame`,
  `evenMansourIdealGame`, `idealLazyHandler`, `realLazyHandler`: real and ideal bidirectional
  permutation games and lazy two-cache and single-cache handlers.
* `Cslib.Crypto.EvenMansour.isBadKeyPair`, `isBadEvenMansourKey`, `isBadSingleKeyEvenMansour`,
  `transcriptCipher`, `transcriptPerm`: bad-key collision predicates and transcript projections.

## Main results

* `Cslib.Crypto.EvenMansour.map_prod_evenMansourEncrypt_uniformOfFintype`: one-query perfect
  secrecy and independence from the pre-whitening key `k₀`.
* `Cslib.Crypto.EvenMansour.advantage_preWhitenKeyRecoveryGame_eq`,
  `Cslib.Crypto.EvenMansour.advantage_postWhitenKeyRecoveryGame_eq`: 2-query attacks achieve
  key-recovery game advantage `1 - |G|⁻¹` when either whitening key is omitted.
* `Cslib.Crypto.EvenMansour.evenMansourIdealGame_eq_lazy`,
  `Cslib.Crypto.EvenMansour.run_idealLazyHandler_good_le_realLazyHandler`,
  `Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_liftLeft_eq_zero`,
  `Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_liftRight_eq_zero`: lazy two-permutation
  equivalence for `evenMansourIdealGame`, lazy coupling inequality, and zero advantage when
  queries are restricted to one oracle.
* `Cslib.Crypto.EvenMansour.toOuterMeasure_isBadEvenMansourKey_toReal_le`,
  `Cslib.Crypto.EvenMansour.toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le`,
  `Cslib.Crypto.EvenMansour.IsCallBounded.badEvenMansourKey_toReal_le`,
  `Cslib.Crypto.EvenMansour.IsCallBounded.badSingleKeyEvenMansour_toReal_le`:
  Boneh–Shoup Theorem 4.10 bad-key probability bound `2 * Q_e * Q_π / |G|`.
* `Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_evenMansourIdealGame_le`,
  `Cslib.Crypto.EvenMansour.advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le`:
  end-to-end PRP security bound `2 * Q_e * Q_π / |G|` in the ideal-permutation model.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 4.7 (Theorem 4.10).
* [S. Even, Y. Mansour, *A Construction of a Cipher from a Single Pseudorandom
  Permutation*][EvenMansour1997].
* [O. Dunkelman, N. Keller, A. Shamir, *Minimalism in Cryptography: The Even–Mansour Scheme
  Revisited*][DunkelmanKellerShamir2012].
-/

@[expose] public section

namespace Cslib.Crypto.EvenMansour

open Probability OracleComp RandomPermutation
open scoped ENNReal NNReal BigOperators

/-! ### Algebraic Even–Mansour cipher over an additive group -/

section Algebraic

variable {G : Type*} [AddGroup G]

/-- Even–Mansour encryption ([BonehShoup2023], Section 4.7; [EvenMansour1997]): pre-whiten by adding
`k₀`, apply the public permutation `π`, and post-whiten by adding `k₁`. -/
def evenMansourEncrypt (π : G → G) (k₀ k₁ x : G) : G :=
  π (x + k₀) + k₁

/-- Even–Mansour decryption: remove post-whitening key `k₁`, apply the inverse permutation `π_inv`,
and remove pre-whitening key `k₀`. -/
def evenMansourDecrypt (π_inv : G → G) (k₀ k₁ y : G) : G :=
  π_inv (y - k₁) - k₀

/-- Decryption inverts encryption whenever `π_inv` is a left inverse of `π`. -/
@[simp] theorem evenMansourDecrypt_evenMansourEncrypt {π π_inv : G → G}
    (h : Function.LeftInverse π_inv π) (k₀ k₁ x : G) :
    evenMansourDecrypt π_inv k₀ k₁ (evenMansourEncrypt π k₀ k₁ x) = x := by
  simp [evenMansourEncrypt, evenMansourDecrypt, h (x + k₀)]

/-- Encryption inverts decryption whenever `π_inv` is a right inverse of `π`. -/
@[simp] theorem evenMansourEncrypt_evenMansourDecrypt {π π_inv : G → G}
    (h : Function.RightInverse π_inv π) (k₀ k₁ y : G) :
    evenMansourEncrypt π k₀ k₁ (evenMansourDecrypt π_inv k₀ k₁ y) = y := by
  simp [evenMansourEncrypt, evenMansourDecrypt, h (y - k₁)]

/-- The Even–Mansour cipher bundled as a permutation `Equiv.Perm G`. -/
def evenMansourEquiv (π : Equiv.Perm G) (k₀ k₁ : G) : Equiv.Perm G where
  toFun := evenMansourEncrypt π k₀ k₁
  invFun := evenMansourDecrypt π.symm k₀ k₁
  left_inv := evenMansourDecrypt_evenMansourEncrypt π.left_inv k₀ k₁
  right_inv := evenMansourEncrypt_evenMansourDecrypt π.right_inv k₀ k₁

@[simp] theorem evenMansourEquiv_apply (π : Equiv.Perm G) (k₀ k₁ x : G) :
    evenMansourEquiv π k₀ k₁ x = π (x + k₀) + k₁ := rfl

@[simp] theorem evenMansourEquiv_symm_apply (π : Equiv.Perm G) (k₀ k₁ y : G) :
    (evenMansourEquiv π k₀ k₁).symm y = π.symm (y - k₁) - k₀ := rfl

/-- With zero whitening keys, the Even–Mansour cipher is the underlying permutation `π`. -/
@[simp] theorem evenMansourEquiv_zero (π : Equiv.Perm G) :
    evenMansourEquiv π 0 0 = π := by
  ext x
  simp

/-- Composing two Even–Mansour wrappers with the same permutation adds the whitening keys. -/
theorem evenMansourEquiv_evenMansourEquiv (π : Equiv.Perm G) (k₀ k₁ k₀' k₁' : G) :
    evenMansourEquiv (evenMansourEquiv π k₀ k₁) k₀' k₁' =
      evenMansourEquiv π (k₀' + k₀) (k₁ + k₁') := by
  ext x
  simp [add_assoc]

/-- The inverse of an Even–Mansour cipher with keys `(k₀, k₁)` and permutation `π` is an
Even–Mansour cipher with keys `(-k₁, -k₀)` and inverse permutation `π.symm`. -/
theorem evenMansourEquiv_symm (π : Equiv.Perm G) (k₀ k₁ : G) :
    (evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm (-k₁) (-k₀) := by
  ext y
  simp [sub_eq_add_neg]

/-- Single-key Even–Mansour cipher (`k₀ = k₁ = k`, [DunkelmanKellerShamir2012]). -/
abbrev singleKeyEvenMansourEquiv (π : Equiv.Perm G) (k : G) : Equiv.Perm G :=
  evenMansourEquiv π k k

/-- Over a group of exponent two (`∀ x : G, -x = x`), Even–Mansour decryption is encryption under
the inverse permutation with the two keys swapped. -/
theorem evenMansourDecrypt_eq_of_neg_eq_self (hneg : ∀ x : G, -x = x) (π_inv : G → G)
    (k₀ k₁ y : G) :
    evenMansourDecrypt π_inv k₀ k₁ y = evenMansourEncrypt π_inv k₁ k₀ y := by
  simp [evenMansourDecrypt, evenMansourEncrypt, sub_eq_add_neg, hneg]

/-- Over a group of exponent two (`∀ x : G, -x = x`), inverting the Even–Mansour permutation swaps
the pre-whitening and post-whitening keys. -/
theorem evenMansourEquiv_symm_eq_of_neg_eq_self (hneg : ∀ x : G, -x = x) (π : Equiv.Perm G)
    (k₀ k₁ : G) :
    (evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm k₁ k₀ := by
  rw [evenMansourEquiv_symm, hneg, hneg]

/-- Over `BitString n`, inverting the Even–Mansour permutation swaps `k₀` and `k₁`. -/
theorem evenMansourEquiv_symm_bitString {n : ℕ} (π : Equiv.Perm (BitString n))
    (k₀ k₁ : BitString n) :
    (evenMansourEquiv π k₀ k₁).symm = evenMansourEquiv π.symm k₁ k₀ :=
  evenMansourEquiv_symm_eq_of_neg_eq_self
    (fun x => neg_eq_iff_add_eq_zero.mpr (BitString.add_self x)) π k₀ k₁

/-- For any fixed keys `(k₀, k₁)`, wrapping a permutation `π` in Even–Mansour is a bijection on
`Equiv.Perm G`. -/
def evenMansourPermEquiv (k₀ k₁ : G) : Equiv.Perm (Equiv.Perm G) where
  toFun π := evenMansourEquiv π k₀ k₁
  invFun π := evenMansourEquiv π (-k₀) (-k₁)
  left_inv π := by
    dsimp
    rw [evenMansourEquiv_evenMansourEquiv, neg_add_cancel, add_neg_cancel, evenMansourEquiv_zero]
  right_inv π := by
    dsimp
    rw [evenMansourEquiv_evenMansourEquiv, add_neg_cancel, neg_add_cancel, evenMansourEquiv_zero]

@[simp] theorem evenMansourPermEquiv_apply (k₀ k₁ : G) (π : Equiv.Perm G) :
    evenMansourPermEquiv k₀ k₁ π = evenMansourEquiv π k₀ k₁ := rfl

/-! ### One-query perfect secrecy -/

/-- For any fixed function `π : G → G` and input `x : G`, the map `(k₀, k₁) ↦ (k₀, π(x + k₀) + k₁)`
is a bijection on `G × G`. -/
def oneQueryKeyEquiv (π : G → G) (x : G) : Equiv.Perm (G × G) where
  toFun k := (k.1, evenMansourEncrypt π k.1 k.2 x)
  invFun p := (p.1, -π (x + p.1) + p.2)
  left_inv k := by
    ext <;> simp [evenMansourEncrypt]
  right_inv p := by
    ext <;> simp [evenMansourEncrypt]

/-- **One-query perfect secrecy**: for any fixed `π : G → G` and plaintext `x : G`, under uniform
independent keys `(k₀, k₁)`, the pre-whitening key `k₀` and the ciphertext
`evenMansourEncrypt π k₀ k₁ x` are independent and uniformly distributed on `G × G`. -/
theorem map_prod_evenMansourEncrypt_uniformOfFintype [Fintype G] [Nonempty G]
    (π : G → G) (x : G) :
    (PMF.uniformOfFintype (G × G)).map (fun k => (k.1, evenMansourEncrypt π k.1 k.2 x)) =
      PMF.uniformOfFintype (G × G) :=
  PMF.uniformOfFintype_map_equiv (oneQueryKeyEquiv π x)

/-- Under uniform independent keys `(k₀, k₁)`, a single Even–Mansour encryption of `x` is uniformly
distributed on `G` for every fixed `π : G → G`. -/
theorem map_evenMansourEncrypt_uniformOfFintype [Fintype G] [Nonempty G]
    (π : G → G) (x : G) :
    (PMF.uniformOfFintype (G × G)).map (fun k => evenMansourEncrypt π k.1 k.2 x) =
      PMF.uniformOfFintype G := by
  have h := congrArg (PMF.map Prod.snd) (map_prod_evenMansourEncrypt_uniformOfFintype π x)
  rw [PMF.map_comp] at h
  calc (PMF.uniformOfFintype (G × G)).map (fun k => evenMansourEncrypt π k.1 k.2 x)
      = (PMF.uniformOfFintype (G × G)).map Prod.snd := h
    _ = (PMF.uniformOfFintype (G × G)).map (Prod.fst ∘ Equiv.prodComm G G) := rfl
    _ = ((PMF.uniformOfFintype (G × G)).map (Equiv.prodComm G G)).map Prod.fst := by
        rw [PMF.map_comp]
    _ = PMF.uniformOfFintype G := by
        rw [PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_prod_map_fst]

/-! ### Necessity of both whitening keys (algebraic recovery) -/

/-- Even–Mansour with pre-whitening only (`k₁ = 0`): `E(k₀, x) = π(x + k₀)`
([BonehShoup2023], Section 4.7). -/
abbrev preWhitenEquiv (π : Equiv.Perm G) (k₀ : G) : Equiv.Perm G :=
  evenMansourEquiv π k₀ 0

/-- Even–Mansour with post-whitening only (`k₀ = 0`): `E(k₁, x) = π(x) + k₁`
([BonehShoup2023], Section 4.7). -/
abbrev postWhitenEquiv (π : Equiv.Perm G) (k₁ : G) : Equiv.Perm G :=
  evenMansourEquiv π 0 k₁

/-- Key recovery for `preWhitenEquiv`: given `y = E(k₀, x)` and `u = π⁻¹(y)`, recover
`k₀ = -x + u`. -/
def preWhitenKeyRecovery (pi_inv_enc_x x : G) : G :=
  -x + pi_inv_enc_x

/-- A single encryption query `y = preWhitenEquiv π k₀ x` and inverse permutation query `π.symm y`
recover `k₀` deterministically. -/
theorem preWhitenKeyRecovery_spec (π : Equiv.Perm G) (k₀ x : G) :
    preWhitenKeyRecovery (π.symm (preWhitenEquiv π k₀ x)) x = k₀ := by
  simp [preWhitenKeyRecovery, preWhitenEquiv]

/-- Key recovery for `postWhitenEquiv`: given `y = E(k₁, x)` and `v = π(x)`, recover
`k₁ = -v + y`. -/
def postWhitenKeyRecovery (enc_x pi_x : G) : G :=
  -pi_x + enc_x

/-- A single encryption query `y = postWhitenEquiv π k₁ x` and forward permutation query `π x`
recover `k₁` deterministically. -/
theorem postWhitenKeyRecovery_spec (π : Equiv.Perm G) (k₁ x : G) :
    postWhitenKeyRecovery (postWhitenEquiv π k₁ x) (π x) = k₁ := by
  simp [postWhitenKeyRecovery, postWhitenEquiv]

end Algebraic

/-! ### Bidirectional ideal-permutation oracle interface and games -/

/-- The combined oracle interface in the Even–Mansour security experiment ([BonehShoup2023],
Section 4.7): left queries (`.inl`) call the cipher permutation `E` and right queries (`.inr`)
call the public primitive permutation `π`. -/
abbrev EvenMansourSpec (G : Type) : OracleSpec (PermQuery G ⊕ PermQuery G) :=
  PermOracleSpec G ⊕ₒ PermOracleSpec G

/-- Cost function counting cipher oracle calls (`1` for `.inl`, `0` for `.inr`). -/
def cipherCost {G : Type} : PermQuery G ⊕ PermQuery G → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Cost function counting primitive permutation oracle calls (`0` for `.inl`, `1` for `.inr`). -/
def permCost {G : Type} : PermQuery G ⊕ PermQuery G → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- An adversary `program` makes at most `Q_e` cipher queries and at most `Q_π` primitive
permutation queries on every execution path. -/
def IsCallBounded {G α : Type} (program : OracleComp (EvenMansourSpec G) α) (Q_e Q_π : ℕ) :
    Prop :=
  IsCostBounded cipherCost program Q_e ∧ IsCostBounded permCost program Q_π

/-- A program making at most `Q_e` cipher queries and `Q_π` primitive queries makes at most
`Q_e + Q_π` total queries. -/
theorem IsCallBounded.isQueryBounded {G α : Type} {program : OracleComp (EvenMansourSpec G) α}
    {Q_e Q_π : ℕ} (h : IsCallBounded program Q_e Q_π) :
    IsQueryBounded program (Q_e + Q_π) :=
  (h.1.add h.2).of_le fun q => by cases q <;> simp [cipherCost, permCost]

/-- Query the cipher permutation in the forward direction (`x ↦ E(x)`). -/
def queryCipherForward {G : Type} (x : G) : OracleComp (EvenMansourSpec G) G :=
  liftLeft (query (spec := PermOracleSpec G) (.forward x))

/-- Query the cipher permutation in the inverse direction (`y ↦ E⁻¹(y)`). -/
def queryCipherInverse {G : Type} (y : G) : OracleComp (EvenMansourSpec G) G :=
  liftLeft (query (spec := PermOracleSpec G) (.inverse y))

/-- Query the public primitive permutation in the forward direction (`u ↦ π(u)`). -/
def queryPermForward {G : Type} (u : G) : OracleComp (EvenMansourSpec G) G :=
  liftRight (query (spec := PermOracleSpec G) (.forward u))

/-- Query the public primitive permutation in the inverse direction (`v ↦ π⁻¹(v)`). -/
def queryPermInverse {G : Type} (v : G) : OracleComp (EvenMansourSpec G) G :=
  liftRight (query (spec := PermOracleSpec G) (.inverse v))

theorem isCallBounded_queryCipherForward {G : Type} (x : G) :
    IsCallBounded (queryCipherForward x) 1 0 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.forward x)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.forward x))⟩

theorem isCallBounded_queryCipherInverse {G : Type} (y : G) :
    IsCallBounded (queryCipherInverse y) 1 0 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.inverse y)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inl (.inverse y))⟩

theorem isCallBounded_queryPermForward {G : Type} (u : G) :
    IsCallBounded (queryPermForward u) 0 1 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.forward u)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.forward u))⟩

theorem isCallBounded_queryPermInverse {G : Type} (v : G) :
    IsCallBounded (queryPermInverse v) 0 1 :=
  ⟨IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.inverse v)),
    IsCostBounded.query (spec := EvenMansourSpec G) (Sum.inr (.inverse v))⟩

/-- Deterministically evaluate a program against cipher permutation `E` and primitive permutation
`π`. -/
def evalTwoPerms {G α : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansourSpec G) α) : α :=
  (interpret (sumHandler (fun q => (evalPerm E q : Id G)) (fun q => (evalPerm π q : Id G)))
    program).run

@[simp] theorem evalTwoPerms_pure {G α : Type} (E π : Equiv.Perm G) (a : α) :
    evalTwoPerms E π (pure a) = a := rfl

@[simp] theorem evalTwoPerms_map {G α β : Type} (E π : Equiv.Perm G)
    (f : α → β) (program : OracleComp (EvenMansourSpec G) α) :
    evalTwoPerms E π (f <$> program) = f (evalTwoPerms E π program) := by
  simp [evalTwoPerms]

@[simp] theorem evalTwoPerms_bind {G α β : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansourSpec G) α)
    (next : α → OracleComp (EvenMansourSpec G) β) :
    evalTwoPerms E π (program >>= next) =
      evalTwoPerms E π (next (evalTwoPerms E π program)) := by
  simp [evalTwoPerms]

@[simp] theorem evalTwoPerms_queryCipherForward {G : Type} (E π : Equiv.Perm G) (x : G) :
    evalTwoPerms E π (queryCipherForward x) = E x := rfl

@[simp] theorem evalTwoPerms_queryCipherInverse {G : Type} (E π : Equiv.Perm G) (y : G) :
    evalTwoPerms E π (queryCipherInverse y) = E.symm y := rfl

@[simp] theorem evalTwoPerms_queryPermForward {G : Type} (E π : Equiv.Perm G) (u : G) :
    evalTwoPerms E π (queryPermForward u) = π u := rfl

@[simp] theorem evalTwoPerms_queryPermInverse {G : Type} (E π : Equiv.Perm G) (v : G) :
    evalTwoPerms E π (queryPermInverse v) = π.symm v := rfl

theorem evalTwoPerms_liftLeft {G α : Type} (E π π' : Equiv.Perm G)
    (program : OracleComp (PermOracleSpec G) α) :
    evalTwoPerms E π (liftLeft program) = evalTwoPerms E π' (liftLeft program) := by
  simp [evalTwoPerms]

theorem evalTwoPerms_liftRight {G α : Type} (E E' π : Equiv.Perm G)
    (program : OracleComp (PermOracleSpec G) α) :
    evalTwoPerms E π (liftRight program) = evalTwoPerms E' π (liftRight program) := by
  simp [evalTwoPerms]

/-- Deterministically evaluate a program in the real Even–Mansour world with public permutation `π`
and keys `(k₀, k₁)`. -/
def evalEvenMansour {G α : Type} [AddGroup G] (π : Equiv.Perm G) (k₀ k₁ : G)
    (program : OracleComp (EvenMansourSpec G) α) : α :=
  evalTwoPerms (evenMansourEquiv π k₀ k₁) π program

section Attacks

variable {G : Type} [AddGroup G]

/-- Oracle attack recovering `k₀` from `preWhitenEquiv π k₀` in `1` cipher query and `1` primitive
query: query `y ← E(x)` and `u ← π⁻¹(y)`, then return `-x + u`. -/
def preWhitenKeyRecoveryAttack (x : G) : OracleComp (EvenMansourSpec G) G := do
  let y ← queryCipherForward x
  let u ← queryPermInverse y
  return preWhitenKeyRecovery u x

/-- `preWhitenKeyRecoveryAttack x` makes at most `1` cipher query and `1` primitive query. -/
theorem isCallBounded_preWhitenKeyRecoveryAttack (x : G) :
    IsCallBounded (preWhitenKeyRecoveryAttack x) 1 1 := by
  constructor
  · simpa [preWhitenKeyRecoveryAttack] using
      (isCallBounded_queryCipherForward x).1.bind fun y =>
        (isCallBounded_queryPermInverse y).1.bind fun u => IsCostBounded.pure _ 0
  · simpa [preWhitenKeyRecoveryAttack] using
      (isCallBounded_queryCipherForward x).2.bind fun y =>
        (isCallBounded_queryPermInverse y).2.bind fun u => IsCostBounded.pure _ 0

/-- Against `preWhitenEquiv π k₀` and `π`, `preWhitenKeyRecoveryAttack x` deterministically returns
`k₀`. -/
@[simp] theorem evalTwoPerms_preWhitenKeyRecoveryAttack (π : Equiv.Perm G) (k₀ x : G) :
    evalTwoPerms (preWhitenEquiv π k₀) π (preWhitenKeyRecoveryAttack x) = k₀ := by
  simp [preWhitenKeyRecoveryAttack, preWhitenKeyRecovery]

/-- Oracle attack recovering `k₁` from `postWhitenEquiv π k₁` in `1` cipher query and `1` primitive
query: query `y ← E(x)` and `v ← π(x)`, then return `-v + y`. -/
def postWhitenKeyRecoveryAttack (x : G) : OracleComp (EvenMansourSpec G) G := do
  let y ← queryCipherForward x
  let v ← queryPermForward x
  return postWhitenKeyRecovery y v

/-- `postWhitenKeyRecoveryAttack x` makes at most `1` cipher query and `1` primitive query. -/
theorem isCallBounded_postWhitenKeyRecoveryAttack (x : G) :
    IsCallBounded (postWhitenKeyRecoveryAttack x) 1 1 := by
  constructor
  · simpa [postWhitenKeyRecoveryAttack] using
      (isCallBounded_queryCipherForward x).1.bind fun y =>
        (isCallBounded_queryPermForward x).1.bind fun v => IsCostBounded.pure _ 0
  · simpa [postWhitenKeyRecoveryAttack] using
      (isCallBounded_queryCipherForward x).2.bind fun y =>
        (isCallBounded_queryPermForward x).2.bind fun v => IsCostBounded.pure _ 0

/-- Against `postWhitenEquiv π k₁` and `π`, `postWhitenKeyRecoveryAttack x` deterministically
returns `k₁`. -/
@[simp] theorem evalTwoPerms_postWhitenKeyRecoveryAttack (π : Equiv.Perm G) (k₁ x : G) :
    evalTwoPerms (postWhitenEquiv π k₁) π (postWhitenKeyRecoveryAttack x) = k₁ := by
  simp [postWhitenKeyRecoveryAttack, postWhitenKeyRecovery]

end Attacks

section Games

variable {G : Type} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]

/-- The real Even–Mansour security experiment ([BonehShoup2023], Section 4.7): sample a uniform
permutation `π ← Equiv.Perm G` and uniform independent keys `(k₀, k₁) ← G × G`, and run `program`
against `evenMansourEquiv π k₀ k₁` and `π`. -/
noncomputable def evenMansourRealGame (program : OracleComp (EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype (G × G)
  return evalEvenMansour π k.1 k.2 program

/-- The single-key Even–Mansour security experiment ([DunkelmanKellerShamir2012]): sample a uniform
permutation `π ← Equiv.Perm G` and a single uniform key `k ← G`, and run `program` against
`singleKeyEvenMansourEquiv π k` and `π`. -/
noncomputable def singleKeyEvenMansourRealGame
    (program : OracleComp (EvenMansourSpec G) Bool) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k ← PMF.uniformOfFintype G
  return evalEvenMansour π k k program

/-- The ideal Even–Mansour security experiment: sample two independent uniform permutations
`E, π ← Equiv.Perm G` and run `program` against `E` and `π`. -/
noncomputable def evenMansourIdealGame (program : OracleComp (EvenMansourSpec G) Bool) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  return evalTwoPerms E π program

/-- Lazy bidirectional two-permutation handler for `evenMansourIdealGame`: left (cipher) queries
are answered lazily from `cache_e` and right (primitive permutation) queries are answered lazily
from `cache_π` via `RandomPermutation.answer`. -/
noncomputable def idealLazyHandler (q : PermQuery G ⊕ PermQuery G) :
    StateT (RandomPermutation.Cache G × RandomPermutation.Cache G) PMF (EvenMansourSpec G q) :=
  fun (cache_e, cache_π) =>
    match q with
    | .inl qe =>
      (RandomPermutation.answer qe cache_e).map fun (y, cache_e') => (y, (cache_e', cache_π))
    | .inr qπ =>
      (RandomPermutation.answer qπ cache_π).map fun (v, cache_π') => (v, (cache_e, cache_π'))

omit [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] in
private theorem pure_evalTwoPerms {α : Type} (E π : Equiv.Perm G)
    (program : OracleComp (EvenMansourSpec G) α) :
    (PMF.pure (evalTwoPerms E π program) : PMF α) =
      OracleComp.interpret
        (sumHandler (fun q => PMF.pure (evalPerm E q)) (fun q => PMF.pure (evalPerm π q)))
        program := by
  induction program with
  | pure a => rfl
  | liftBind q cont ih =>
    change PMF.pure (evalTwoPerms E π (OracleComp.query q >>= cont)) =
      OracleComp.interpret
        (sumHandler (fun q => PMF.pure (evalPerm E q)) (fun q => PMF.pure (evalPerm π q)))
        (OracleComp.query q >>= cont)
    cases q <;>
      · simp only [evalTwoPerms, sumHandler, OracleComp.interpret_bind, OracleComp.interpret_query,
          Id.run_bind, PMF.monad_bind_eq_bind, PMF.pure_bind]
        exact ih _

omit [AddGroup G] in
/-- **Ideal Even–Mansour game equals lazy bidirectional two-permutation sampling**: sampling two
independent uniform permutations `E, π ← PMF.uniformOfFintype (Equiv.Perm G)` has the exact same
output distribution as running `idealLazyHandler` from `([], [])`. -/
theorem evenMansourIdealGame_eq_lazy (program : OracleComp (EvenMansourSpec G) Bool) :
    evenMansourIdealGame program =
      (((OracleComp.interpret idealLazyHandler program).run ([], [])).map Prod.fst) := by
  let sim (st : RandomPermutation.Cache G × RandomPermutation.Cache G) :
      PMF (Equiv.Perm G × Equiv.Perm G) :=
    (RandomPermutation.complete st.1).bind fun E => (RandomPermutation.complete st.2).map (E, ·)
  let inv (st : RandomPermutation.Cache G × RandomPermutation.Cache G) : Prop :=
    RandomPermutation.IsPartialBijection st.1 ∧ RandomPermutation.IsPartialBijection st.2
  let readH (q : PermQuery G ⊕ PermQuery G) (p : Equiv.Perm G × Equiv.Perm G) :
      PMF (EvenMansourSpec G q) :=
    sumHandler (fun q => PMF.pure (evalPerm p.1 q)) (fun q => PMF.pure (evalPerm p.2 q)) q
  have hpres : ∀ q st, inv st →
      ∀ a st', (a, st') ∈ (idealLazyHandler q st).support → inv st' := by
    rintro (qe | qπ) ⟨c_e, c_π⟩ ⟨he, hπ⟩ a ⟨c_e', c_π'⟩ hmem
    · simp only [idealLazyHandler, PMF.mem_support_map_iff] at hmem
      obtain ⟨⟨a₀, ce₀⟩, hmem₀, hpair⟩ := hmem
      cases hpair
      exact ⟨RandomPermutation.answer_preserve_isPartialBijection qe c_e he a₀ ce₀ hmem₀, hπ⟩
    · simp only [idealLazyHandler, PMF.mem_support_map_iff] at hmem
      obtain ⟨⟨a₀, cπ₀⟩, hmem₀, hpair⟩ := hmem
      cases hpair
      exact ⟨he, RandomPermutation.answer_preserve_isPartialBijection qπ c_π hπ a₀ cπ₀ hmem₀⟩
  have hstep : ∀ q st, inv st →
      (do let (a, st') ← idealLazyHandler q st; (a, ·) <$> sim st') =
      (do let p ← sim st; let y ← (·, p) <$> readH q p; pure y) := by
    rintro (qe | qπ) ⟨c_e, c_π⟩ ⟨he, hπ⟩
    · have h1 := congrArg
        (fun m : PMF (G × Equiv.Perm G) =>
          m.bind fun (y, E) => (RandomPermutation.complete c_π).map fun π => (y, (E, π)))
        (RandomPermutation.answer_complete qe c_e he)
      simpa only [idealLazyHandler, sim, readH, sumHandler, PMF.monad_bind_eq_bind,
        PMF.monad_map_eq_map, PMF.monad_pure_eq_pure, PMF.bind_map, PMF.map_bind,
        PMF.bind_bind, PMF.pure_map, PMF.pure_bind, PMF.map_comp, PMF.map,
        Function.comp_def] using h1
    · have h2 := congrArg
        (fun m : PMF (G × Equiv.Perm G) =>
          (RandomPermutation.complete c_e).bind fun E =>
            m.map fun (v, π) => (v, (E, π)))
        (RandomPermutation.answer_complete qπ c_π hπ)
      simp only [idealLazyHandler, sim, readH, sumHandler, PMF.monad_bind_eq_bind,
        PMF.monad_map_eq_map, PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def] at h2 ⊢
      rw [PMF.bind_comm]
      exact h2
  have hsim := OracleComp.run_interpret_simulation_of_invariant idealLazyHandler
    (fun q p => (·, p) <$> readH q p) sim inv hpres hstep program ([], [])
    ⟨RandomPermutation.isPartialBijection_nil, RandomPermutation.isPartialBijection_nil⟩
  have hsim' := congrArg (PMF.map Prod.fst) hsim
  simp only [sim, RandomPermutation.complete_nil, PMF.monad_map_eq_map,
    PMF.map, Function.comp_def, PMF.bind_bind,
    PMF.pure_bind, PMF.bind_const] at hsim'
  refine Eq.trans ?_ hsim'.symm
  simp only [evenMansourIdealGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine congrArg ((PMF.uniformOfFintype (Equiv.Perm G)).bind) (funext fun E => ?_)
  refine congrArg ((PMF.uniformOfFintype (Equiv.Perm G)).bind) (funext fun π => ?_)
  rw [pure_evalTwoPerms]
  simpa only [readH, PMF.monad_map_eq_map, PMF.map_comp, PMF.map, Function.comp_def,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_pure] using
    (congrArg (PMF.map Prod.fst) (OracleComp.run_interpret_readOnly readH program (E, π))).symm

/-- For any adversary `program` that queries only the cipher oracle (`liftLeft program`), the real
Even–Mansour game is identically distributed to the ideal game. -/
theorem evenMansourRealGame_liftLeft_eq_ideal (program : OracleComp (PermOracleSpec G) Bool) :
    evenMansourRealGame (liftLeft program) = evenMansourIdealGame (liftLeft program) := by
  have hkey (k₀ k₁ : G) :
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        PMF.pure (evalTwoPerms (evenMansourEquiv π k₀ k₁) (1 : Equiv.Perm G) (liftLeft program))) =
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun E =>
        PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := by
    have h1 : ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        PMF.pure (evalTwoPerms (evenMansourEquiv π k₀ k₁) (1 : Equiv.Perm G) (liftLeft program))) =
      ((PMF.uniformOfFintype (Equiv.Perm G)).map (evenMansourPermEquiv k₀ k₁)).bind (fun E =>
        PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := by
      rw [PMF.bind_map]
      rfl
    rw [h1, PMF.uniformOfFintype_map_equiv]
  simp only [evenMansourRealGame, evenMansourIdealGame, evalEvenMansour,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm]
  calc (PMF.uniformOfFintype (G × G)).bind (fun k =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
          PMF.pure (evalTwoPerms (evenMansourEquiv π k.1 k.2) π (liftLeft program)))
      = (PMF.uniformOfFintype (G × G)).bind (fun k =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
          PMF.pure (evalTwoPerms (evenMansourEquiv π k.1 k.2) (1 : Equiv.Perm G)
            (liftLeft program))) := by
        congr 1; funext k; congr 1; funext π
        rw [evalTwoPerms_liftLeft _ π 1 program]
    _ = (PMF.uniformOfFintype (G × G)).bind (fun _ =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun E =>
          PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := by
        congr 1; funext k
        exact hkey k.1 k.2
    _ = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun E =>
          PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := PMF.bind_const _ _
    _ = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun E =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
          PMF.pure (evalTwoPerms E π (liftLeft program))) := by
        congr 1; funext E
        symm
        calc (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun π =>
              PMF.pure (evalTwoPerms E π (liftLeft program)))
            = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun _ =>
              PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program))) := by
              congr 1; funext π
              rw [evalTwoPerms_liftLeft E π 1 program]
          _ = PMF.pure (evalTwoPerms E (1 : Equiv.Perm G) (liftLeft program)) :=
              PMF.bind_const _ _

/-- Any adversary that queries only the cipher oracle (`liftLeft`) has zero advantage between the
real Even–Mansour game and the ideal game. -/
@[simp] theorem advantage_evenMansourRealGame_liftLeft_eq_zero
    (program : OracleComp (PermOracleSpec G) Bool) :
    Game.advantage (evenMansourRealGame (liftLeft program))
      (evenMansourIdealGame (liftLeft program)) = 0 := by
  rw [evenMansourRealGame_liftLeft_eq_ideal, Game.advantage_self]

/-- For any adversary `program` that queries only the primitive permutation oracle
(`liftRight program`), the real Even–Mansour game is identically distributed to the ideal game. -/
theorem evenMansourRealGame_liftRight_eq_ideal (program : OracleComp (PermOracleSpec G) Bool) :
    evenMansourRealGame (liftRight program) = evenMansourIdealGame (liftRight program) := by
  simp only [evenMansourRealGame, evenMansourIdealGame, evalEvenMansour,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  calc (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun π =>
        (PMF.uniformOfFintype (G × G)).bind fun k =>
          PMF.pure (evalTwoPerms (evenMansourEquiv π k.1 k.2) π (liftRight program)))
      = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun π =>
        (PMF.uniformOfFintype (G × G)).bind fun _ =>
          PMF.pure (evalTwoPerms (1 : Equiv.Perm G) π (liftRight program))) := by
        congr 1; funext π; congr 1; funext k
        rw [evalTwoPerms_liftRight _ 1 π program]
    _ = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun π =>
          PMF.pure (evalTwoPerms (1 : Equiv.Perm G) π (liftRight program))) := by
        simp [PMF.bind_const]
    _ = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun E =>
        (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
          PMF.pure (evalTwoPerms E π (liftRight program))) := by
        symm
        calc (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun E =>
              (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
                PMF.pure (evalTwoPerms E π (liftRight program)))
            = (PMF.uniformOfFintype (Equiv.Perm G)).bind (fun _ =>
              (PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
                PMF.pure (evalTwoPerms (1 : Equiv.Perm G) π (liftRight program))) := by
              congr 1; funext E; congr 1; funext π
              rw [evalTwoPerms_liftRight E 1 π program]
          _ = _ := PMF.bind_const _ _

/-- Any adversary that queries only the primitive permutation oracle (`liftRight`) has zero
advantage between the real Even–Mansour game and the ideal game. -/
@[simp] theorem advantage_evenMansourRealGame_liftRight_eq_zero
    (program : OracleComp (PermOracleSpec G) Bool) :
    Game.advantage (evenMansourRealGame (liftRight program))
      (evenMansourIdealGame (liftRight program)) = 0 := by
  rw [evenMansourRealGame_liftRight_eq_ideal, Game.advantage_self]

/-! ### 2-query oracle attacks when either whitening key is omitted -/

/-- Key-recovery game for pre-whitening-only Even–Mansour: draw `π ← Equiv.Perm G` and
`k₀ ← G`, run `preWhitenKeyRecoveryAttack x` against `preWhitenEquiv π k₀` and `π`, and test
whether it outputs `k₀`. -/
noncomputable def preWhitenKeyRecoveryRealGame (x : G) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₀ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms (preWhitenEquiv π k₀) π (preWhitenKeyRecoveryAttack x) = k₀)

/-- Ideal comparison game for `preWhitenKeyRecoveryAttack`: draw independent uniform permutations
`E, π ← Equiv.Perm G` and a uniform target key `k₀ ← G`, and test whether
`preWhitenKeyRecoveryAttack x` outputs `k₀`. -/
noncomputable def preWhitenKeyRecoveryIdealGame (x : G) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₀ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀)

/-- In the real pre-whitened game, `preWhitenKeyRecoveryAttack x` succeeds with probability `1`. -/
@[simp] theorem preWhitenKeyRecoveryRealGame_eq_pure_true (x : G) :
    preWhitenKeyRecoveryRealGame x = PMF.pure true := by
  simp [preWhitenKeyRecoveryRealGame, PMF.bind_const]

/-- In the ideal game, `preWhitenKeyRecoveryAttack x` outputs the uniform target `k₀` with
probability `|G|⁻¹`. -/
theorem preWhitenKeyRecoveryIdealGame_true_toReal (x : G) :
    (preWhitenKeyRecoveryIdealGame x true).toReal = (Fintype.card G : ℝ)⁻¹ := by
  simp only [preWhitenKeyRecoveryIdealGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hconst (E π : Equiv.Perm G) :
      ((PMF.uniformOfFintype G).bind fun k₀ =>
        PMF.pure (decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀))) true =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
    classical
    have hmap : ((PMF.uniformOfFintype G).bind fun k₀ =>
        PMF.pure (decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀))) =
      (PMF.uniformOfFintype G).map (fun k₀ =>
        decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀)) :=
      (PMF.bind_pure_comp _ _).symm
    rw [hmap, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_uniformOfFintype]
    have hfilter : Finset.univ.filter (fun k₀ : G =>
        k₀ ∈ (fun k₀ => decide (evalTwoPerms E π (preWhitenKeyRecoveryAttack x) = k₀)) ⁻¹'
          ({true} : Set Bool)) = {evalTwoPerms E π (preWhitenKeyRecoveryAttack x)} := by
      ext k₀
      simp [eq_comm]
    rw [hfilter, Finset.card_singleton, Nat.cast_one, one_mul]
  rw [PMF.bind_apply_of_forall _ fun E => PMF.bind_apply_of_forall _ fun π => hconst E π,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **2-query break of pre-whitening-only Even–Mansour** ([BonehShoup2023], Section 4.7):
omitting post-whitening (`k₁ = 0`) allows a 2-query attack (`1` cipher query + `1` primitive query)
to achieve key-recovery game advantage `1 - |G|⁻¹`. -/
theorem advantage_preWhitenKeyRecoveryGame_eq (x : G) :
    (Game.advantage (preWhitenKeyRecoveryRealGame x) (preWhitenKeyRecoveryIdealGame x) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability,
    preWhitenKeyRecoveryRealGame_eq_pure_true, preWhitenKeyRecoveryIdealGame_true_toReal]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
  have hle : (Fintype.card G : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)
  exact abs_of_nonneg (by linarith)

/-- Key-recovery game for post-whitening-only Even–Mansour: draw `π ← Equiv.Perm G` and
`k₁ ← G`, run `postWhitenKeyRecoveryAttack x` against `postWhitenEquiv π k₁` and `π`, and test
whether it outputs `k₁`. -/
noncomputable def postWhitenKeyRecoveryRealGame (x : G) : Game := do
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₁ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms (postWhitenEquiv π k₁) π (postWhitenKeyRecoveryAttack x) = k₁)

/-- Ideal comparison game for `postWhitenKeyRecoveryAttack`: draw independent uniform permutations
`E, π ← Equiv.Perm G` and a uniform target key `k₁ ← G`, and test whether
`postWhitenKeyRecoveryAttack x` outputs `k₁`. -/
noncomputable def postWhitenKeyRecoveryIdealGame (x : G) : Game := do
  let E ← PMF.uniformOfFintype (Equiv.Perm G)
  let π ← PMF.uniformOfFintype (Equiv.Perm G)
  let k₁ ← PMF.uniformOfFintype G
  return decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁)

/-- In the real post-whitened game, `postWhitenKeyRecoveryAttack x` succeeds with probability
`1`. -/
@[simp] theorem postWhitenKeyRecoveryRealGame_eq_pure_true (x : G) :
    postWhitenKeyRecoveryRealGame x = PMF.pure true := by
  simp [postWhitenKeyRecoveryRealGame, PMF.bind_const]

/-- In the ideal game, `postWhitenKeyRecoveryAttack x` outputs the uniform target `k₁` with
probability `|G|⁻¹`. -/
theorem postWhitenKeyRecoveryIdealGame_true_toReal (x : G) :
    (postWhitenKeyRecoveryIdealGame x true).toReal = (Fintype.card G : ℝ)⁻¹ := by
  simp only [postWhitenKeyRecoveryIdealGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hconst (E π : Equiv.Perm G) :
      ((PMF.uniformOfFintype G).bind fun k₁ =>
        PMF.pure (decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁))) true =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
    classical
    have hmap : ((PMF.uniformOfFintype G).bind fun k₁ =>
        PMF.pure (decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁))) =
      (PMF.uniformOfFintype G).map (fun k₁ =>
        decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁)) :=
      (PMF.bind_pure_comp _ _).symm
    rw [hmap, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_uniformOfFintype]
    have hfilter : Finset.univ.filter (fun k₁ : G =>
        k₁ ∈ (fun k₁ => decide (evalTwoPerms E π (postWhitenKeyRecoveryAttack x) = k₁)) ⁻¹'
          ({true} : Set Bool)) = {evalTwoPerms E π (postWhitenKeyRecoveryAttack x)} := by
      ext k₁
      simp [eq_comm]
    rw [hfilter, Finset.card_singleton, Nat.cast_one, one_mul]
  rw [PMF.bind_apply_of_forall _ fun E => PMF.bind_apply_of_forall _ fun π => hconst E π,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **2-query break of post-whitening-only Even–Mansour** ([BonehShoup2023], Section 4.7):
omitting pre-whitening (`k₀ = 0`) allows a 2-query attack (`1` cipher query + `1` primitive query)
to achieve key-recovery game advantage `1 - |G|⁻¹`. -/
theorem advantage_postWhitenKeyRecoveryGame_eq (x : G) :
    (Game.advantage (postWhitenKeyRecoveryRealGame x) (postWhitenKeyRecoveryIdealGame x) : ℝ) =
      1 - (Fintype.card G : ℝ)⁻¹ := by
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability,
    postWhitenKeyRecoveryRealGame_eq_pure_true, postWhitenKeyRecoveryIdealGame_true_toReal]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
  have hle : (Fintype.card G : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Fintype.card_pos)
  exact abs_of_nonneg (by linarith)

end Games

/-! ### Bad-key transcript intersection analysis (Boneh–Shoup Theorem 4.10) -/

section BadKeys

variable {G : Type} [AddGroup G] [DecidableEq G]

/-- A key pair `k = (k₀, k₁)` is bad for a cipher input-output pair `e = (x, y)` and a primitive
permutation input-output pair `p = (u, v)` if the internal permutation input `x + k₀` collides with
`u` or the internal permutation output `y - k₁` collides with `v`
([BonehShoup2023], Section 4.7, Theorem 4.10). -/
def isBadKeyPair (e p : G × G) (k : G × G) : Bool :=
  decide (e.1 + k.1 = p.1) || decide (e.2 - k.2 = p.2)

/-- A key pair `k = (k₀, k₁)` is bad for a cipher transcript `T_e : List (G × G)` and a primitive
permutation transcript `T_π : List (G × G)` if some `e ∈ T_e` and `p ∈ T_π` collide on the
internal permutation input or output ([BonehShoup2023], Section 4.7, Theorem 4.10). -/
def isBadEvenMansourKey (T_e T_π : List (G × G)) (k : G × G) : Bool :=
  T_e.any fun e => T_π.any fun p => isBadKeyPair e p k

/-- Single-key specialization (`k₀ = k₁ = k`, [DunkelmanKellerShamir2012]) of the Even–Mansour
bad-key predicate. -/
def isBadSingleKeyEvenMansour (T_e T_π : List (G × G)) (k : G) : Bool :=
  isBadEvenMansourKey T_e T_π (k, k)

/-- Input-only bad-key predicate (`x + k₀ = u` for some `(x, y) ∈ T_e` and `(u, v) ∈ T_π`), which
captures all collisions in the real Even–Mansour world where `y = π(x + k₀) + k₁` and
`v = π(u)`. -/
def isBadInputKey (T_e T_π : List (G × G)) (k₀ : G) : Bool :=
  T_e.any fun e => T_π.any fun p => decide (e.1 + k₀ = p.1)

@[simp] theorem isBadKeyPair_eq_true_iff (e p k : G × G) :
    isBadKeyPair e p k = true ↔ e.1 + k.1 = p.1 ∨ e.2 - k.2 = p.2 := by
  simp [isBadKeyPair]

@[simp] theorem isBadEvenMansourKey_eq_true_iff (T_e T_π : List (G × G)) (k : G × G) :
    isBadEvenMansourKey T_e T_π k = true ↔
      ∃ e ∈ T_e, ∃ p ∈ T_π, e.1 + k.1 = p.1 ∨ e.2 - k.2 = p.2 := by
  simp [isBadEvenMansourKey]

/-- **Domain and range disjointness outside bad keys**: when
`isBadEvenMansourKey T_e T_π k = false`, every cipher pair `(x, y) ∈ T_e` has internal permutation
input `x + k₀` distinct from every primitive query input `u` in `T_π`, and internal permutation
output `y - k₁` distinct from every primitive query output `v` in `T_π`. -/
theorem disjoint_of_isBadEvenMansourKey_eq_false {T_e T_π : List (G × G)} {k : G × G}
    (hgood : isBadEvenMansourKey T_e T_π k = false) {e p : G × G}
    (he : e ∈ T_e) (hp : p ∈ T_π) :
    e.1 + k.1 ≠ p.1 ∧ e.2 - k.2 ≠ p.2 := by
  have hnot : ¬isBadEvenMansourKey T_e T_π k = true := by simp [hgood]
  rw [isBadEvenMansourKey_eq_true_iff] at hnot
  push Not at hnot
  exact hnot e he p hp

omit [DecidableEq G] in
/-- When `e = (x, y)` is consistent with `evenMansourEquiv π k₀ k₁` (`π (x + k₀) + k₁ = y`) and
`p = (u, v)` is consistent with `π` (`π u = v`), an output collision `y - k₁ = v` is equivalent to
an input collision `x + k₀ = u`. -/
theorem input_collision_iff_output_collision (π : Equiv.Perm G) (k : G × G) {e p : G × G}
    (he : evenMansourEquiv π k.1 k.2 e.1 = e.2) (hp : π p.1 = p.2) :
    e.1 + k.1 = p.1 ↔ e.2 - k.2 = p.2 := by
  have he' : e.2 - k.2 = π (e.1 + k.1) := by
    rw [← he, evenMansourEquiv_apply, add_sub_cancel_right]
  rw [he', ← hp, π.injective.eq_iff]

/-- On a pair `(e, p)` consistent with `evenMansourEquiv π k.1 k.2` and `π`, `isBadKeyPair e p k`
reduces to the input collision `decide (e.1 + k.1 = p.1)`. -/
theorem isBadKeyPair_eq_decide_of_evenMansourEquiv (π : Equiv.Perm G) (k : G × G) {e p : G × G}
    (he : evenMansourEquiv π k.1 k.2 e.1 = e.2) (hp : π p.1 = p.2) :
    isBadKeyPair e p k = decide (e.1 + k.1 = p.1) := by
  rw [Bool.eq_iff_iff, isBadKeyPair_eq_true_iff, decide_eq_true_eq,
    ← input_collision_iff_output_collision π k he hp, or_self]

/-- On transcripts `T_e` and `T_π` consistent with `evenMansourEquiv π k.1 k.2` and `π`,
`isBadEvenMansourKey T_e T_π k` equals `isBadInputKey T_e T_π k.1`. -/
theorem isBadEvenMansourKey_eq_isBadInputKey_of_evenMansourEquiv (π : Equiv.Perm G) (k : G × G)
    {T_e T_π : List (G × G)} (hT_e : ∀ e ∈ T_e, evenMansourEquiv π k.1 k.2 e.1 = e.2)
    (hT_π : ∀ p ∈ T_π, π p.1 = p.2) :
    isBadEvenMansourKey T_e T_π k = isBadInputKey T_e T_π k.1 := by
  rw [Bool.eq_iff_iff]
  simp only [isBadEvenMansourKey, isBadInputKey, List.any_eq_true]
  refine exists_congr fun e => and_congr_right fun he => ?_
  refine exists_congr fun p => and_congr_right fun hp => ?_
  rw [isBadKeyPair_eq_decide_of_evenMansourEquiv π k (hT_e e he) (hT_π p hp)]

/-! ### Exact single-pair collision probabilities and multi-query union bounds -/

variable [Fintype G] [Nonempty G]

/-- Under a uniform key `k₀ ← G`, the probability of an input collision `x + k₀ = u` is exactly
`|G|⁻¹`. -/
private theorem toOuterMeasure_input_collision (x u : G) :
    (PMF.uniformOfFintype G).toOuterMeasure {k₀ : G | decide (x + k₀ = u) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_uniformOfFintype]
  have hfilter : Finset.univ.filter (· ∈ {k₀ : G | decide (x + k₀ = u) = true}) = {-x + u} := by
    ext k₀
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      decide_eq_true_eq, Finset.mem_singleton]
    exact ⟨fun h => by rw [← h, neg_add_cancel_left], fun h => by rw [h, add_neg_cancel_left]⟩
  rw [hfilter, Finset.card_singleton, Nat.cast_one, one_mul]

/-- Under a uniform key `k₁ ← G`, the probability of an output collision `y - k₁ = v` is exactly
`|G|⁻¹`. -/
private theorem toOuterMeasure_output_collision (y v : G) :
    (PMF.uniformOfFintype G).toOuterMeasure {k₁ : G | decide (y - k₁ = v) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  rw [PMF.toOuterMeasure_uniformOfFintype]
  have hfilter : Finset.univ.filter (· ∈ {k₁ : G | decide (y - k₁ = v) = true}) = {-v + y} := by
    ext k₁
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
      decide_eq_true_eq, Finset.mem_singleton]
    rw [← neg_inj, neg_sub, sub_eq_iff_eq_add]
  rw [hfilter, Finset.card_singleton, Nat.cast_one, one_mul]

/-- Under uniform independent keys `(k₀, k₁) ← G × G`, the probability of an input collision
`e.1 + k.1 = p.1` is `|G|⁻¹`. -/
private theorem toOuterMeasure_prod_input_collision (e p : G × G) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k : G × G | decide (e.1 + k.1 = p.1) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hpre : {k : G × G | decide (e.1 + k.1 = p.1) = true} =
      Prod.fst ⁻¹' {k₀ : G | decide (e.1 + k₀ = p.1) = true} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply, PMF.uniformOfFintype_prod_map_fst,
    toOuterMeasure_input_collision]

/-- Under uniform independent keys `(k₀, k₁) ← G × G`, the probability of an output collision
`e.2 - k.2 = p.2` is `|G|⁻¹`. -/
private theorem toOuterMeasure_prod_output_collision (e p : G × G) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k : G × G | decide (e.2 - k.2 = p.2) = true} =
      (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hsnd : (PMF.uniformOfFintype (G × G)).map Prod.snd = PMF.uniformOfFintype G := by
    calc (PMF.uniformOfFintype (G × G)).map Prod.snd
        = ((PMF.uniformOfFintype (G × G)).map (Equiv.prodComm G G)).map Prod.fst := by
          rw [PMF.map_comp]; rfl
      _ = PMF.uniformOfFintype G := by
          rw [PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_prod_map_fst]
  have hpre : {k : G × G | decide (e.2 - k.2 = p.2) = true} =
      Prod.snd ⁻¹' {k₁ : G | decide (e.2 - k₁ = p.2) = true} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply, hsnd, toOuterMeasure_output_collision]

/-- For a single pair `(e, p)`, a uniform key pair `k ← G × G` satisfies `isBadKeyPair e p k` with
probability at most `2 * |G|⁻¹`. -/
theorem toOuterMeasure_isBadKeyPair_le (e p : G × G) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k | isBadKeyPair e p k = true} ≤
      2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hset : {k | isBadKeyPair e p k = true} =
      {k : G × G | decide (e.1 + k.1 = p.1) = true} ∪
        {k : G × G | decide (e.2 - k.2 = p.2) = true} := by
    ext k
    simp [isBadKeyPair]
  rw [hset]
  exact (MeasureTheory.measure_union_le _ _).trans_eq (by
    rw [toOuterMeasure_prod_input_collision, toOuterMeasure_prod_output_collision, two_mul])

/-- For a single pair `(e, p)`, a single uniform key `k ← G` satisfies `isBadKeyPair e p (k, k)`
with probability at most `2 * |G|⁻¹`. -/
theorem toOuterMeasure_isBadKeyPair_singleKey_le (e p : G × G) :
    (PMF.uniformOfFintype G).toOuterMeasure {k | isBadKeyPair e p (k, k) = true} ≤
      2 * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hset : {k | isBadKeyPair e p (k, k) = true} =
      {k : G | decide (e.1 + k = p.1) = true} ∪
        {k : G | decide (e.2 - k = p.2) = true} := by
    ext k
    simp [isBadKeyPair]
  rw [hset]
  exact (MeasureTheory.measure_union_le _ _).trans_eq (by
    rw [toOuterMeasure_input_collision, toOuterMeasure_output_collision, two_mul])

/-- **Boneh–Shoup Theorem 4.10 bad-key union bound (`ℝ≥0∞`)**: for any cipher transcript `T_e` and
primitive permutation transcript `T_π`, a uniform key pair `(k₀, k₁) ← G × G` is bad with
probability at most `2 * |T_e| * |T_π| * |G|⁻¹`. -/
theorem toOuterMeasure_isBadEvenMansourKey_le (T_e T_π : List (G × G)) :
    (PMF.uniformOfFintype (G × G)).toOuterMeasure {k | isBadEvenMansourKey T_e T_π k = true} ≤
      2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hset : {k | isBadEvenMansourKey T_e T_π k = true} =
      ⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | isBadKeyPair x.1 x.2 k = true} := by
    ext k
    simp only [Set.mem_ofPred_eq, isBadEvenMansourKey_eq_true_iff, Set.mem_iUnion,
      Finset.mem_product, List.mem_toFinset, isBadKeyPair_eq_true_iff, Prod.exists, exists_prop]
    exact ⟨fun ⟨a, b, hab, c, d, hcd, h⟩ => ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩,
      fun ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩ => ⟨a, b, hab, c, d, hcd, h⟩⟩
  rw [hset]
  calc (PMF.uniformOfFintype (G × G)).toOuterMeasure
        (⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | isBadKeyPair x.1 x.2 k = true})
      ≤ ∑ x ∈ T_e.toFinset ×ˢ T_π.toFinset,
          (PMF.uniformOfFintype (G × G)).toOuterMeasure {k | isBadKeyPair x.1 x.2 k = true} :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ (T_e.toFinset ×ˢ T_π.toFinset).card • (2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ => toOuterMeasure_isBadKeyPair_le x.1 x.2
    _ = (T_e.toFinset.card : ℝ≥0∞) * T_π.toFinset.card * (2 * (Fintype.card G : ℝ≥0∞)⁻¹) := by
        rw [Finset.card_product, nsmul_eq_mul, Nat.cast_mul]
    _ ≤ (T_e.length : ℝ≥0∞) * T_π.length * (2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        mul_le_mul' (mul_le_mul' (Nat.cast_le.mpr (List.toFinset_card_le T_e))
          (Nat.cast_le.mpr (List.toFinset_card_le T_π))) le_rfl
    _ = 2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by ring

/-- **Boneh–Shoup Theorem 4.10 bad-key union bound (`ℝ`)**: for any cipher transcript `T_e` and
primitive permutation transcript `T_π`, a uniform key pair `(k₀, k₁) ← G × G` is bad with real
probability at most `2 * |T_e| * |T_π| / |G|`. -/
theorem toOuterMeasure_isBadEvenMansourKey_toReal_le (T_e T_π : List (G × G)) :
    ((PMF.uniformOfFintype (G × G)).toOuterMeasure
      {k | isBadEvenMansourKey T_e T_π k = true}).toReal ≤
      2 * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) := by
  have h := toOuterMeasure_isBadEvenMansourKey_le T_e T_π
  have hne : (2 : ℝ≥0∞) * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top _)) (ENNReal.natCast_ne_top _)) ?_
    simp [Fintype.card_ne_zero]
  have hreal := ENNReal.toReal_mono hne h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv] using hreal

/-- **Single-key Even–Mansour bad-key union bound (`ℝ≥0∞`, [DunkelmanKellerShamir2012])**: for any
cipher transcript `T_e` and primitive permutation transcript `T_π`, a single uniform key `k ← G` is
bad with probability at most `2 * |T_e| * |T_π| * |G|⁻¹`. -/
theorem toOuterMeasure_isBadSingleKeyEvenMansour_le (T_e T_π : List (G × G)) :
    (PMF.uniformOfFintype G).toOuterMeasure {k | isBadSingleKeyEvenMansour T_e T_π k = true} ≤
      2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by
  have hset : {k | isBadSingleKeyEvenMansour T_e T_π k = true} =
      ⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | isBadKeyPair x.1 x.2 (k, k) = true} := by
    ext k
    simp only [Set.mem_ofPred_eq, isBadSingleKeyEvenMansour, isBadEvenMansourKey_eq_true_iff,
      Set.mem_iUnion, Finset.mem_product, List.mem_toFinset, isBadKeyPair_eq_true_iff, Prod.exists,
      exists_prop]
    exact ⟨fun ⟨a, b, hab, c, d, hcd, h⟩ => ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩,
      fun ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩ => ⟨a, b, hab, c, d, hcd, h⟩⟩
  rw [hset]
  calc (PMF.uniformOfFintype G).toOuterMeasure
        (⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k | isBadKeyPair x.1 x.2 (k, k) = true})
      ≤ ∑ x ∈ T_e.toFinset ×ˢ T_π.toFinset,
          (PMF.uniformOfFintype G).toOuterMeasure {k | isBadKeyPair x.1 x.2 (k, k) = true} :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ (T_e.toFinset ×ˢ T_π.toFinset).card • (2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ => toOuterMeasure_isBadKeyPair_singleKey_le x.1 x.2
    _ = (T_e.toFinset.card : ℝ≥0∞) * T_π.toFinset.card * (2 * (Fintype.card G : ℝ≥0∞)⁻¹) := by
        rw [Finset.card_product, nsmul_eq_mul, Nat.cast_mul]
    _ ≤ (T_e.length : ℝ≥0∞) * T_π.length * (2 * (Fintype.card G : ℝ≥0∞)⁻¹) :=
        mul_le_mul' (mul_le_mul' (Nat.cast_le.mpr (List.toFinset_card_le T_e))
          (Nat.cast_le.mpr (List.toFinset_card_le T_π))) le_rfl
    _ = 2 * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ := by ring

/-- **Single-key Even–Mansour bad-key union bound (`ℝ`, [DunkelmanKellerShamir2012])**: for any
cipher transcript `T_e` and primitive permutation transcript `T_π`, a single uniform key `k ← G` is
bad with real probability at most `2 * |T_e| * |T_π| / |G|`. -/
theorem toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le (T_e T_π : List (G × G)) :
    ((PMF.uniformOfFintype G).toOuterMeasure
      {k | isBadSingleKeyEvenMansour T_e T_π k = true}).toReal ≤
      2 * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) := by
  have h := toOuterMeasure_isBadSingleKeyEvenMansour_le T_e T_π
  have hne : (2 : ℝ≥0∞) * T_e.length * T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top _)) (ENNReal.natCast_ne_top _)) ?_
    simp [Fintype.card_ne_zero]
  have hreal := ENNReal.toReal_mono hne h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv] using hreal

/-- **Input-collision union bound (`ℝ`)**: for any cipher transcript `T_e` and primitive transcript
`T_π`, a uniform pre-whitening key `k₀ ← G` triggers an input collision `isBadInputKey T_e T_π k₀`
with real probability at most `|T_e| * |T_π| / |G|`. -/
theorem toOuterMeasure_isBadInputKey_toReal_le (T_e T_π : List (G × G)) :
    ((PMF.uniformOfFintype G).toOuterMeasure {k₀ | isBadInputKey T_e T_π k₀ = true}).toReal ≤
      (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card G : ℝ) := by
  have hset : {k₀ | isBadInputKey T_e T_π k₀ = true} =
      ⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k₀ | decide (x.1.1 + k₀ = x.2.1) = true} := by
    ext k₀
    simp only [Set.mem_ofPred_eq, isBadInputKey, List.any_eq_true, Set.mem_iUnion,
      Finset.mem_product, List.mem_toFinset, Prod.exists, exists_prop]
    exact ⟨fun ⟨a, b, hab, c, d, hcd, h⟩ => ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩,
      fun ⟨a, b, c, d, ⟨hab, hcd⟩, h⟩ => ⟨a, b, hab, c, d, hcd, h⟩⟩
  have h : (PMF.uniformOfFintype G).toOuterMeasure {k₀ | isBadInputKey T_e T_π k₀ = true} ≤
      T_e.length * (T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹) := by
    rw [hset]
    calc (PMF.uniformOfFintype G).toOuterMeasure
          (⋃ x ∈ T_e.toFinset ×ˢ T_π.toFinset, {k₀ | decide (x.1.1 + k₀ = x.2.1) = true})
        ≤ ∑ x ∈ T_e.toFinset ×ˢ T_π.toFinset,
            (PMF.uniformOfFintype G).toOuterMeasure {k₀ | decide (x.1.1 + k₀ = x.2.1) = true} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ (T_e.toFinset ×ˢ T_π.toFinset).card • (Fintype.card G : ℝ≥0∞)⁻¹ :=
          Finset.sum_le_card_nsmul _ _ _ fun x _ => (toOuterMeasure_input_collision x.1.1 x.2.1).le
      _ = (T_e.toFinset.card : ℝ≥0∞) * (T_π.toFinset.card * (Fintype.card G : ℝ≥0∞)⁻¹) := by
          rw [Finset.card_product, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
      _ ≤ (T_e.length : ℝ≥0∞) * (T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹) :=
          mul_le_mul' (Nat.cast_le.mpr (List.toFinset_card_le T_e))
            (mul_le_mul' (Nat.cast_le.mpr (List.toFinset_card_le T_π)) le_rfl)
  have hne : (T_e.length : ℝ≥0∞) * (T_π.length * (Fintype.card G : ℝ≥0∞)⁻¹) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _) ?_)
    simp [Fintype.card_ne_zero]
  have hreal := ENNReal.toReal_mono hne h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_assoc] using hreal

end BadKeys

/-! ### Adaptive distinguisher transcript bounds via `IsCallBounded` -/

section TranscriptBounds

/-- Project a logged `EvenMansourSpec G` query-response entry onto its cipher input-output pair
`(x, y)` (turning `.inverse y` with answer `x` into `(x, y)`), or `none` for primitive queries. -/
def transcriptCipherEntry {G : Type}
    (entry : (q : PermQuery G ⊕ PermQuery G) × EvenMansourSpec G q) : Option (G × G) :=
  match entry.1, entry.2 with
  | .inl (.forward x), y => some (x, y)
  | .inl (.inverse y), x => some (x, y)
  | .inr _, _ => none

/-- Project a logged `EvenMansourSpec G` query-response entry onto its primitive permutation
input-output pair `(u, v)` (turning `.inverse v` with answer `u` into `(u, v)`), or `none` for
cipher queries. -/
def transcriptPermEntry {G : Type}
    (entry : (q : PermQuery G ⊕ PermQuery G) × EvenMansourSpec G q) : Option (G × G) :=
  match entry.1, entry.2 with
  | .inl _, _ => none
  | .inr (.forward u), v => some (u, v)
  | .inr (.inverse v), u => some (u, v)

/-- The list of cipher input-output pairs recorded in a bidirectional interaction transcript. -/
def transcriptCipher {G : Type} (T : Transcript (EvenMansourSpec G)) : List (G × G) :=
  T.filterMap transcriptCipherEntry

/-- The list of primitive permutation input-output pairs recorded in a bidirectional interaction
transcript. -/
def transcriptPerm {G : Type} (T : Transcript (EvenMansourSpec G)) : List (G × G) :=
  T.filterMap transcriptPermEntry

/-- The length of `transcriptCipher T` equals the total `cipherCost` of `T`. -/
@[simp] theorem length_transcriptCipher_eq_sum_cipherCost {G : Type}
    (T : Transcript (EvenMansourSpec G)) :
    (transcriptCipher T).length = (T.map fun entry => cipherCost entry.1).sum := by
  induction T with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨(x | y) | (u | v), ans⟩ <;>
      simpa [transcriptCipher, transcriptCipherEntry, List.filterMap_cons, cipherCost,
        Nat.add_comm] using ih

/-- The length of `transcriptPerm T` equals the total `permCost` of `T`. -/
@[simp] theorem length_transcriptPerm_eq_sum_permCost {G : Type}
    (T : Transcript (EvenMansourSpec G)) :
    (transcriptPerm T).length = (T.map fun entry => permCost entry.1).sum := by
  induction T with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨(x | y) | (u | v), ans⟩ <;>
      simpa [transcriptPerm, transcriptPermEntry, List.filterMap_cons, permCost,
        Nat.add_comm] using ih

/-- Against any stateful bidirectional oracle, a supported run of `program` with
`IsCallBounded program Q_e Q_π` records at most `Q_e` cipher pairs. -/
theorem IsCallBounded.length_transcriptCipher_le {G State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    (transcriptCipher T).length ≤ Q_e := by
  rw [length_transcriptCipher_eq_sum_cipherCost]
  exact h.1.transcript_cost_le oracle hmem

/-- Against any stateful bidirectional oracle, a supported run of `program` with
`IsCallBounded program Q_e Q_π` records at most `Q_π` primitive permutation pairs. -/
theorem IsCallBounded.length_transcriptPerm_le {G State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    (transcriptPerm T).length ≤ Q_π := by
  rw [length_transcriptPerm_eq_sum_permCost]
  exact h.2.transcript_cost_le oracle hmem

variable {G : Type} [AddGroup G] [DecidableEq G] [Fintype G] [Nonempty G]

/-- **Boneh–Shoup Theorem 4.10 for adaptive call-bounded distinguishers (two-key)**: on any
supported transcript `T` of a distinguisher satisfying `IsCallBounded program Q_e Q_π`, a uniform
key pair `(k₀, k₁) ← G × G` is bad with real probability at most `2 * Q_e * Q_π / |G|`. -/
theorem IsCallBounded.badEvenMansourKey_toReal_le {State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    ((PMF.uniformOfFintype (G × G)).toOuterMeasure
      {k | isBadEvenMansourKey (transcriptCipher T) (transcriptPerm T) k = true}).toReal ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  have hlen_e : ((transcriptCipher T).length : ℝ) ≤ Q_e :=
    Nat.cast_le.mpr (h.length_transcriptCipher_le oracle hmem)
  have hlen_π : ((transcriptPerm T).length : ℝ) ≤ Q_π :=
    Nat.cast_le.mpr (h.length_transcriptPerm_le oracle hmem)
  refine (toOuterMeasure_isBadEvenMansourKey_toReal_le (transcriptCipher T)
    (transcriptPerm T)).trans ?_
  gcongr

/-- **Boneh–Shoup Theorem 4.10 for adaptive call-bounded distinguishers (single-key)**: on any
supported transcript `T` of a distinguisher satisfying `IsCallBounded program Q_e Q_π`, a single
uniform key `k ← G` is bad with real probability at most `2 * Q_e * Q_π / |G|`. -/
theorem IsCallBounded.badSingleKeyEvenMansour_toReal_le {State γ : Type}
    {program : OracleComp (EvenMansourSpec G) γ} {Q_e Q_π : ℕ}
    (h : IsCallBounded program Q_e Q_π)
    (oracle : (q : PermQuery G ⊕ PermQuery G) → StateT State PMF (EvenMansourSpec G q))
    {s s' : State} {result : γ} {T : Transcript (EvenMansourSpec G)}
    (hmem : (result, s', T) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    ((PMF.uniformOfFintype G).toOuterMeasure
      {k | isBadSingleKeyEvenMansour (transcriptCipher T) (transcriptPerm T) k = true}).toReal ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  have hlen_e : ((transcriptCipher T).length : ℝ) ≤ Q_e :=
    Nat.cast_le.mpr (h.length_transcriptCipher_le oracle hmem)
  have hlen_π : ((transcriptPerm T).length : ℝ) ≤ Q_π :=
    Nat.cast_le.mpr (h.length_transcriptPerm_le oracle hmem)
  refine (toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le (transcriptCipher T)
    (transcriptPerm T)).trans ?_
  gcongr

end TranscriptBounds

/-! ### Key-shifted lazy permutation coupling and end-to-end advantage bound -/

section Coupling

variable {G : Type} [AddGroup G] [DecidableEq G] [Fintype G] [Nonempty G]

/-- Translate an `EvenMansourSpec G` query under key `k = (k₀, k₁)` into the underlying query on the
primitive permutation `π`. -/
def toPermQuery (k : G × G) : PermQuery G ⊕ PermQuery G → PermQuery G
  | .inl (.forward x) => .forward (x + k.1)
  | .inl (.inverse y) => .inverse (y - k.2)
  | .inr qπ => qπ

/-- Post-process the primitive permutation's answer to recover the Even–Mansour oracle answer under
key `k = (k₀, k₁)`. -/
def fromPermAnswer (k : G × G) : (q : PermQuery G ⊕ PermQuery G) → G → EvenMansourSpec G q
  | .inl (.forward _) => (· + k.2)
  | .inl (.inverse _) => (· - k.1)
  | .inr _ => id

/-- Translate an `EvenMansourSpec G` program under key `k = (k₀, k₁)` into a single-permutation
`PermOracleSpec G` program on `π`. -/
def toPermProgram (k : G × G) {α : Type} (program : OracleComp (EvenMansourSpec G) α) :
    OracleComp (PermOracleSpec G) α :=
  OracleComp.interpret
    (fun q => fromPermAnswer k q <$> OracleComp.query (spec := PermOracleSpec G) (toPermQuery k q))
    program

/-- Lazy single-cache handler for the real Even–Mansour world with fixed key `k = (k₀, k₁)`:
translate each query via `toPermQuery k`, answer lazily against a single
`RandomPermutation.Cache G`, and post-process the answer via `fromPermAnswer k`. -/
noncomputable def realLazyHandler (k : G × G) (q : PermQuery G ⊕ PermQuery G) :
    StateT (RandomPermutation.Cache G) PMF (EvenMansourSpec G q) := fun cache =>
  (RandomPermutation.answer (toPermQuery k q) cache).map fun (ans, cache') =>
    (fromPermAnswer k q ans, cache')

omit [DecidableEq G] [Fintype G] [Nonempty G] in
private theorem interpret_evalPerm_toPermProgram {α : Type} (π : Equiv.Perm G) (k : G × G)
    (program : OracleComp (EvenMansourSpec G) α) :
    OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) (toPermProgram k program) =
      PMF.pure (evalEvenMansour π k.1 k.2 program) := by
  rw [toPermProgram, OracleComp.interpret_interpret, evalEvenMansour, pure_evalTwoPerms]
  congr 1
  funext q
  rcases q with (x | y) | (u | v) <;>
    simp [toPermQuery, fromPermAnswer, sumHandler, PMF.monad_map_eq_map]

private theorem run_interpret_answer_toPermProgram {α : Type} (k : G × G)
    (program : OracleComp (EvenMansourSpec G) α) (cache : RandomPermutation.Cache G) :
    (OracleComp.interpret RandomPermutation.answer (toPermProgram k program)).run cache =
      (OracleComp.interpret (realLazyHandler k) program).run cache := by
  rw [toPermProgram, OracleComp.interpret_interpret]
  congr 2

/-- For a fixed key pair `k = (k₀, k₁)`, sampling a uniform permutation `π` and evaluating
`evalEvenMansour π k.1 k.2 program` has the exact same distribution as running `realLazyHandler k`
from the empty cache `[]`. -/
theorem realGameForKey_eq_lazy (k : G × G) (program : OracleComp (EvenMansourSpec G) Bool) :
    ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
      PMF.pure (evalEvenMansour π k.1 k.2 program)) =
    (((OracleComp.interpret (realLazyHandler k) program).run []).map Prod.fst) := by
  have h := RandomPermutation.uniform_interpret_eq_lazy (toPermProgram k program)
  simp only [PMF.monad_bind_eq_bind, interpret_evalPerm_toPermProgram,
    run_interpret_answer_toPermProgram] at h
  exact h

/-- Map a primitive permutation pair `(u, v)` to the corresponding cipher pair `(u - k₀, v + k₁)`
under key `k = (k₀, k₁)`. -/
def unshiftPair (k : G × G) (p : G × G) : G × G :=
  (p.1 - k.1, p.2 + k.2)

/-- Shift a cipher pair `(x, y)` to its internal permutation pair `(x + k₀, y - k₁)` under key
`k = (k₀, k₁)`. -/
def shiftPair (k : G × G) (e : G × G) : G × G :=
  (e.1 + k.1, e.2 - k.2)

omit [DecidableEq G] [Fintype G] [Nonempty G] in
@[simp] theorem unshiftPair_shiftPair (k e : G × G) : unshiftPair k (shiftPair k e) = e := by
  rcases e with ⟨x, y⟩
  simp [unshiftPair, shiftPair]

omit [DecidableEq G] [Fintype G] [Nonempty G] in
@[simp] theorem shiftPair_unshiftPair (k p : G × G) : shiftPair k (unshiftPair k p) = p := by
  rcases p with ⟨u, v⟩
  simp [unshiftPair, shiftPair]

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem lookup_eq_some_iff_mem {cache : Cache G} (hc : IsPartialBijection cache)
    {x y : G} :
    cache.lookup x = some y ↔ (x, y) ∈ cache := by
  refine ⟨mem_of_lookup_eq_some, fun hmem => ?_⟩
  obtain ⟨π, hπ⟩ := hc
  cases h : cache.lookup x with
  | none => exact False.elim (lookup_eq_none_iff.mp h (x, y) hmem rfl)
  | some y' =>
    have hy' : π x = y' := hπ.apply_of_lookup_eq_some h
    have hy : π x = y := hπ (x, y) hmem
    exact congrArg some (hy'.symm.trans hy)

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem invLookup_eq_some_iff_mem {cache : Cache G} (hc : IsPartialBijection cache)
    {y x : G} :
    invLookup cache y = some x ↔ (x, y) ∈ cache := by
  refine ⟨mem_of_invLookup_eq_some, fun hmem => ?_⟩
  obtain ⟨π, hπ⟩ := hc
  cases h : invLookup cache y with
  | none => exact False.elim (invLookup_eq_none_iff.mp h (x, y) hmem rfl)
  | some x' =>
    have hx' : π.symm y = x' := hπ.symm_apply_of_invLookup_eq_some h
    have hx : π.symm y = x := π.symm_apply_eq.mpr (hπ (x, y) hmem).symm
    exact congrArg some (hx'.symm.trans hx)

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem lookup_eq_none_iff_forall {cache : Cache G} {x : G} :
    cache.lookup x = none ↔ ∀ y, (x, y) ∉ cache := by
  rw [lookup_eq_none_iff]
  exact ⟨fun h y hy => h (x, y) hy rfl, fun h ⟨a, b⟩ hab heq => h b (heq ▸ hab)⟩

omit [AddGroup G] [Fintype G] [Nonempty G] in
private theorem invLookup_eq_none_iff_forall {cache : Cache G} {y : G} :
    invLookup cache y = none ↔ ∀ x, (x, y) ∉ cache := by
  rw [invLookup_eq_none_iff]
  exact ⟨fun h x hx => h (x, y) hx rfl, fun h ⟨a, b⟩ hab heq => h a (heq ▸ hab)⟩

/-- Coupling invariant between the ideal caches `(c_e, c_π)` and the single real permutation cache
`c` under key `k = (k₀, k₁)`: all three caches are partial bijections, `(c_e, c_π)` has not
triggered `isBadEvenMansourKey`, and `c` contains exactly the key-shifted pairs of `c_e` together
with the pairs of `c_π`. -/
structure CacheRel (k : G × G) (c_e c_π c : Cache G) : Prop where
  partial_e : IsPartialBijection c_e
  partial_π : IsPartialBijection c_π
  partial_c : IsPartialBijection c
  good : isBadEvenMansourKey c_e c_π k = false
  mem_iff : ∀ p : G × G, p ∈ c ↔ unshiftPair k p ∈ c_e ∨ p ∈ c_π

omit [Fintype G] [Nonempty G] in
private theorem cacheRel_nil (k : G × G) : CacheRel k [] [] [] where
  partial_e := isPartialBijection_nil
  partial_π := isPartialBijection_nil
  partial_c := isPartialBijection_nil
  good := rfl
  mem_iff _ := by simp

omit [Nonempty G] in
private theorem CacheRel.map_unusedRange_subset_e {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) :
    (unusedRange c).map (Equiv.addRight k.2).toEmbedding ⊆ unusedRange c_e := by
  intro y hy
  rw [Finset.mem_map] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  rw [mem_unusedRange_iff, invLookup_eq_none_iff_forall] at hv ⊢
  intro x hx
  have hmem : (x + k.1, v) ∈ c := (hrel.mem_iff (x + k.1, v)).mpr
    (Or.inl (by simpa [unshiftPair] using hx))
  exact hv (x + k.1) hmem

omit [Nonempty G] in
private theorem CacheRel.map_unusedDomain_subset_e {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) :
    (unusedDomain c).map (Equiv.subRight k.1).toEmbedding ⊆ unusedDomain c_e := by
  intro x hx
  rw [Finset.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [mem_unusedDomain_iff, lookup_eq_none_iff_forall] at hu ⊢
  intro y hy
  have hmem : (u, y - k.2) ∈ c := (hrel.mem_iff (u, y - k.2)).mpr
    (Or.inl (by simpa [unshiftPair] using hy))
  exact hu (y - k.2) hmem

omit [Nonempty G] in
private theorem CacheRel.unusedRange_subset_π {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) :
    unusedRange c ⊆ unusedRange c_π := by
  intro v hv
  rw [mem_unusedRange_iff, invLookup_eq_none_iff_forall] at hv ⊢
  intro u hu
  exact hv u ((hrel.mem_iff (u, v)).mpr (Or.inr hu))

omit [Nonempty G] in
private theorem CacheRel.unusedDomain_subset_π {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) :
    unusedDomain c ⊆ unusedDomain c_π := by
  intro u hu
  rw [mem_unusedDomain_iff, lookup_eq_none_iff_forall] at hu ⊢
  intro v hv
  exact hu v ((hrel.mem_iff (u, v)).mpr (Or.inr hv))

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.lookup_c_of_lookup_e {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {x y : G} (h : c_e.lookup x = some y) :
    c.lookup (x + k.1) = some (y - k.2) := by
  rw [lookup_eq_some_iff_mem hrel.partial_c, hrel.mem_iff]
  exact Or.inl (by simpa [unshiftPair] using mem_of_lookup_eq_some h)

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.invLookup_c_of_invLookup_e {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {y x : G} (h : invLookup c_e y = some x) :
    invLookup c (y - k.2) = some (x + k.1) := by
  rw [invLookup_eq_some_iff_mem hrel.partial_c, hrel.mem_iff]
  exact Or.inl (by simpa [unshiftPair] using mem_of_invLookup_eq_some h)

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.lookup_c_of_lookup_π {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {u v : G} (h : c_π.lookup u = some v) :
    c.lookup u = some v := by
  rw [lookup_eq_some_iff_mem hrel.partial_c, hrel.mem_iff]
  exact Or.inr (mem_of_lookup_eq_some h)

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.invLookup_c_of_invLookup_π {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {v u : G} (h : invLookup c_π v = some u) :
    invLookup c v = some u := by
  rw [invLookup_eq_some_iff_mem hrel.partial_c, hrel.mem_iff]
  exact Or.inr (mem_of_invLookup_eq_some h)

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.cons_cipher {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {x y : G} (hx : c_e.lookup x = none)
    (hy : invLookup c_e y = none) (hgood' : isBadEvenMansourKey ((x, y) :: c_e) c_π k = false) :
    c.lookup (x + k.1) = none ∧ invLookup c (y - k.2) = none ∧
      CacheRel k ((x, y) :: c_e) c_π ((x + k.1, y - k.2) :: c) := by
  have hxc : c.lookup (x + k.1) = none := by
    rw [lookup_eq_none_iff_forall]
    intro v hv
    rcases (hrel.mem_iff (x + k.1, v)).mp hv with he | hπ
    · simp only [unshiftPair, add_sub_cancel_right] at he
      exact lookup_eq_none_iff_forall.mp hx (v + k.2) he
    · exact (disjoint_of_isBadEvenMansourKey_eq_false hgood' List.mem_cons_self hπ).1 rfl
  have hyc : invLookup c (y - k.2) = none := by
    rw [invLookup_eq_none_iff_forall]
    intro u hu
    rcases (hrel.mem_iff (u, y - k.2)).mp hu with he | hπ
    · simp only [unshiftPair, sub_add_cancel] at he
      exact invLookup_eq_none_iff_forall.mp hy (u - k.1) he
    · exact (disjoint_of_isBadEvenMansourKey_eq_false hgood' List.mem_cons_self hπ).2 rfl
  refine ⟨hxc, hyc, ?_⟩
  refine
    { partial_e := hrel.partial_e.cons_of_lookup_eq_none hx hy
      partial_π := hrel.partial_π
      partial_c := hrel.partial_c.cons_of_lookup_eq_none hxc hyc
      good := hgood'
      mem_iff := fun p => ?_ }
  have hhead : p = (x + k.1, y - k.2) ↔ unshiftPair k p = (x, y) := by
    constructor
    · rintro rfl; simp [unshiftPair]
    · intro hp
      have h := congrArg (shiftPair k) hp
      rw [shiftPair_unshiftPair] at h
      exact h
  rw [List.mem_cons, List.mem_cons, hrel.mem_iff, hhead, or_assoc]

omit [Fintype G] [Nonempty G] in
private theorem CacheRel.cons_perm {k : G × G} {c_e c_π c : Cache G}
    (hrel : CacheRel k c_e c_π c) {u v : G} (hu : c_π.lookup u = none)
    (hv : invLookup c_π v = none) (hgood' : isBadEvenMansourKey c_e ((u, v) :: c_π) k = false) :
    c.lookup u = none ∧ invLookup c v = none ∧
      CacheRel k c_e ((u, v) :: c_π) ((u, v) :: c) := by
  have huc : c.lookup u = none := by
    rw [lookup_eq_none_iff_forall]
    intro v' hv'
    rcases (hrel.mem_iff (u, v')).mp hv' with he | hπ
    · exact (disjoint_of_isBadEvenMansourKey_eq_false hgood' he List.mem_cons_self).1
        (sub_add_cancel u k.1)
    · exact lookup_eq_none_iff_forall.mp hu v' hπ
  have hvc : invLookup c v = none := by
    rw [invLookup_eq_none_iff_forall]
    intro u' hu'
    rcases (hrel.mem_iff (u', v)).mp hu' with he | hπ
    · exact (disjoint_of_isBadEvenMansourKey_eq_false hgood' he List.mem_cons_self).2
        (add_sub_cancel_right v k.2)
    · exact invLookup_eq_none_iff_forall.mp hv u' hπ
  refine ⟨huc, hvc, ?_⟩
  refine
    { partial_e := hrel.partial_e
      partial_π := hrel.partial_π.cons_of_lookup_eq_none hu hv
      partial_c := hrel.partial_c.cons_of_lookup_eq_none huc hvc
      good := hgood'
      mem_iff := fun p => ?_ }
  rw [List.mem_cons, List.mem_cons, hrel.mem_iff]
  tauto

omit [AddGroup G] in
private theorem mem_of_mem_answer_support {q : PermQuery G} {cache cache' : Cache G} {a : G}
    (hmem : (a, cache') ∈ (RandomPermutation.answer q cache).support) :
    ∀ e ∈ cache, e ∈ cache' := by
  cases q with
  | forward x =>
    dsimp [RandomPermutation.answer] at hmem
    cases hx : cache.lookup x with
    | some y =>
      rw [hx, PMF.mem_support_pure_iff] at hmem
      obtain ⟨_, rfl⟩ := Prod.mk.inj hmem
      exact fun _ h => h
    | none =>
      rw [hx] at hmem
      split_ifs at hmem with hne <;>
        · rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨_, _, heq⟩ := hmem
          obtain ⟨_, rfl⟩ := Prod.mk.inj heq
          exact fun _ h => List.mem_cons_of_mem _ h
  | inverse y =>
    dsimp [RandomPermutation.answer] at hmem
    cases hy : RandomPermutation.invLookup cache y with
    | some x =>
      rw [hy, PMF.mem_support_pure_iff] at hmem
      obtain ⟨_, rfl⟩ := Prod.mk.inj hmem
      exact fun _ h => h
    | none =>
      rw [hy] at hmem
      split_ifs at hmem with hne <;>
        · rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨_, _, heq⟩ := hmem
          obtain ⟨_, rfl⟩ := Prod.mk.inj heq
          exact fun _ h => List.mem_cons_of_mem _ h

omit [AddGroup G] in
private theorem length_le_of_mem_answer_support {q : PermQuery G} {cache cache' : Cache G} {a : G}
    (hmem : (a, cache') ∈ (RandomPermutation.answer q cache).support) :
    cache'.length ≤ cache.length + 1 := by
  cases q with
  | forward x =>
    dsimp [RandomPermutation.answer] at hmem
    cases hx : cache.lookup x with
    | some y =>
      rw [hx, PMF.mem_support_pure_iff] at hmem
      obtain ⟨_, rfl⟩ := Prod.mk.inj hmem
      exact Nat.le_succ _
    | none =>
      rw [hx] at hmem
      split_ifs at hmem with hne <;>
        · rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨_, _, heq⟩ := hmem
          obtain ⟨_, rfl⟩ := Prod.mk.inj heq
          exact le_rfl
  | inverse y =>
    dsimp [RandomPermutation.answer] at hmem
    cases hy : RandomPermutation.invLookup cache y with
    | some x =>
      rw [hy, PMF.mem_support_pure_iff] at hmem
      obtain ⟨_, rfl⟩ := Prod.mk.inj hmem
      exact Nat.le_succ _
    | none =>
      rw [hy] at hmem
      split_ifs at hmem with hne <;>
        · rw [PMF.mem_support_map_iff] at hmem
          obtain ⟨_, _, heq⟩ := hmem
          obtain ⟨_, rfl⟩ := Prod.mk.inj heq
          exact le_rfl

omit [Fintype G] [Nonempty G] in
private theorem isBadEvenMansourKey_mono {c_e c_e' c_π c_π' : Cache G} {k : G × G}
    (he : ∀ e ∈ c_e, e ∈ c_e') (hπ : ∀ p ∈ c_π, p ∈ c_π')
    (hbad : isBadEvenMansourKey c_e c_π k = true) :
    isBadEvenMansourKey c_e' c_π' k = true := by
  rw [isBadEvenMansourKey_eq_true_iff] at hbad ⊢
  obtain ⟨e, he_mem, p, hp_mem, hcol⟩ := hbad
  exact ⟨e, he e he_mem, p, hπ p hp_mem, hcol⟩

private theorem isBadEvenMansourKey_of_run_idealLazyHandler {α : Type}
    (program : OracleComp (EvenMansourSpec G) α) {c_e c_π : Cache G} {k : G × G}
    (hbad : isBadEvenMansourKey c_e c_π k = true) {res : α × (Cache G × Cache G)}
    (hmem : res ∈ ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).support) :
    isBadEvenMansourKey res.2.1 res.2.2 k = true := by
  induction program generalizing c_e c_π with
  | pure a =>
    change res ∈ (PMF.pure (a, (c_e, c_π))).support at hmem
    rw [PMF.mem_support_pure_iff] at hmem
    subst hmem
    exact hbad
  | liftBind q cont ih =>
    change res ∈ ((idealLazyHandler q (c_e, c_π)).bind fun p =>
      (OracleComp.interpret idealLazyHandler (cont p.1)).run p.2).support at hmem
    rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨ans, c_e₁, c_π₁⟩, hstep, hcont⟩ := hmem
    refine ih ans ?_ hcont
    cases q with
    | inl qe =>
      simp only [idealLazyHandler, PMF.mem_support_map_iff] at hstep
      obtain ⟨⟨a₀, ce₀⟩, hmem₀, heq⟩ := hstep
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj heq).2
      exact isBadEvenMansourKey_mono (mem_of_mem_answer_support hmem₀) (fun _ h => h) hbad
    | inr qπ =>
      simp only [idealLazyHandler, PMF.mem_support_map_iff] at hstep
      obtain ⟨⟨a₀, cπ₀⟩, hmem₀, heq⟩ := hstep
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj heq).2
      exact isBadEvenMansourKey_mono (fun _ h => h) (mem_of_mem_answer_support hmem₀) hbad

private theorem toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad {α : Type}
    (program : OracleComp (EvenMansourSpec G) α) (P : α → Prop) {c_e c_π : Cache G} {k : G × G}
    (hbad : isBadEvenMansourKey c_e c_π k = true) :
    ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).toOuterMeasure
      {res | P res.1 ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro res hmem hS
  have h1 := isBadEvenMansourKey_of_run_idealLazyHandler program hbad hmem
  exact Bool.false_ne_true (hS.2.symm.trans h1)

omit [AddGroup G] [DecidableEq G] [Fintype G] [Nonempty G] in
private theorem toOuterMeasure_uniformOfFinset_bind {U : Finset G} (hU : U.Nonempty)
    {β : Type} (H : G → PMF β) (S : Set β) :
    ((PMF.uniformOfFinset U hU).bind H).toOuterMeasure S =
      ∑ z ∈ U, (U.card : ℝ≥0∞)⁻¹ * (H z).toOuterMeasure S := by
  classical
  rw [PMF.toOuterMeasure_bind_apply,
    tsum_eq_sum (s := U) fun z hz => by simp [PMF.uniformOfFinset_apply, hz]]
  exact Finset.sum_congr rfl fun z hz => by simp [PMF.uniformOfFinset_apply, hz]

omit [AddGroup G] [DecidableEq G] [Fintype G] [Nonempty G] in
/-- Compare the uniform continuation sums after discarding bad samples and relabeling the
remaining samples by an equivalence. -/
private theorem sum_uniform_le_of_good (U V : Finset G) (e : G ≃ G) (bad : G → Bool)
    (f g : G → ℝ≥0∞) (hsub : V.map e.toEmbedding ⊆ U)
    (hzero : ∀ x, bad x = true → f x = 0)
    (hgood : ∀ x ∈ U, bad x = false → e.symm x ∈ V ∧ f x ≤ g (e.symm x)) :
    ∑ x ∈ U, (U.card : ℝ≥0∞)⁻¹ * f x ≤ ∑ y ∈ V, (V.card : ℝ≥0∞)⁻¹ * g y := by
  have hcard : (U.card : ℝ≥0∞)⁻¹ ≤ (V.card : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (by simpa using Finset.card_le_card hsub))
  have hout : ∀ x ∈ U, x ∉ V.map e.toEmbedding → (U.card : ℝ≥0∞)⁻¹ * f x = 0 := by
    intro x hx hnot
    by_cases hb : bad x = true
    · rw [hzero x hb, mul_zero]
    · exact False.elim (hnot (Finset.mem_map.mpr
        ⟨e.symm x, (hgood x hx (Bool.eq_false_iff.mpr hb)).1, e.apply_symm_apply x⟩))
  rw [← Finset.sum_subset hsub hout, Finset.sum_map]
  refine Finset.sum_le_sum fun y hy => ?_
  simp only [Equiv.toEmbedding_apply]
  by_cases hb : bad (e y) = true
  · rw [hzero (e y) hb, mul_zero]
    exact zero_le
  · simpa only [Equiv.symm_apply_apply] using mul_le_mul' hcard
      (hgood (e y) (hsub (Finset.mem_map_of_mem _ hy)) (Bool.eq_false_iff.mpr hb)).2

/-- **Lazy coupling inequality**: starting from any cache triple `(c_e, c_π, c)` satisfying
`CacheRel k c_e c_π c`, the probability that `idealLazyHandler` produces an output satisfying `P`
without triggering `isBadEvenMansourKey` is at most the probability that `realLazyHandler k`
produces an output satisfying `P`. -/
theorem run_idealLazyHandler_good_le_realLazyHandler {α : Type}
    (program : OracleComp (EvenMansourSpec G) α) (P : α → Prop) (k : G × G)
    {c_e c_π c : Cache G} (hrel : CacheRel k c_e c_π c) :
    ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).toOuterMeasure
      {res | P res.1 ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} ≤
    ((OracleComp.interpret (realLazyHandler k) program).run c).toOuterMeasure
      {res | P res.1} := by
  induction program generalizing c_e c_π c with
  | pure a =>
    change (PMF.pure (a, (c_e, c_π))).toOuterMeasure
        {res | P res.1 ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} ≤
      (PMF.pure (a, c)).toOuterMeasure {res | P res.1}
    by_cases hP : P a <;> simp [PMF.toOuterMeasure_pure_apply, hP, hrel.good]
  | liftBind q cont ih =>
    let S_ideal : Set (α × (Cache G × Cache G)) :=
      {res | P res.1 ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false}
    let S_real : Set (α × Cache G) := {res | P res.1}
    let cont_ideal (p : EvenMansourSpec G q × (Cache G × Cache G)) :=
      (OracleComp.interpret idealLazyHandler (cont p.1)).run p.2
    let cont_real (p : EvenMansourSpec G q × Cache G) :=
      (OracleComp.interpret (realLazyHandler k) (cont p.1)).run p.2
    change ((idealLazyHandler q (c_e, c_π)).bind cont_ideal).toOuterMeasure S_ideal ≤
      ((realLazyHandler k q c).bind cont_real).toOuterMeasure S_real
    rcases q with (x | y) | (u | v)
    · -- Case 1: .inl (.forward x)
      dsimp [idealLazyHandler, realLazyHandler, toPermQuery, fromPermAnswer,
        RandomPermutation.answer]
      cases hx : c_e.lookup x with
      | some y =>
        rw [hrel.lookup_c_of_lookup_e hx]
        simp only [PMF.pure_map, PMF.pure_bind, sub_add_cancel]
        exact ih y hrel
      | none =>
        have hne_e := hrel.partial_e.unusedRange_nonempty hx
        simp only [dite_eq_left hne_e, PMF.map_comp, Function.comp_def, PMF.bind_map,
          toOuterMeasure_uniformOfFinset_bind]
        by_cases hxc : c.lookup (x + k.1) = none
        · have hne_c := hrel.partial_c.unusedRange_nonempty hxc
          simp only [hxc, dite_eq_left hne_c, Function.comp_def, PMF.bind_map,
            toOuterMeasure_uniformOfFinset_bind]
          refine sum_uniform_le_of_good _ _ (Equiv.subRight k.2).symm
            (fun y => isBadEvenMansourKey ((x, y) :: c_e) c_π k) _ _
            hrel.map_unusedRange_subset_e
            (fun y hbad => toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont y) P hbad) ?_
          intro y hy hgood
          obtain ⟨_, hyc, hrel'⟩ := hrel.cons_cipher hx (mem_unusedRange_iff.mp hy) hgood
          refine ⟨mem_unusedRange_iff.mpr hyc, ?_⟩
          simpa using ih y hrel'
        · refine (le_of_eq (Finset.sum_eq_zero fun y hy => ?_)).trans zero_le
          have hbad := Bool.eq_true_of_not_eq_false fun hgood =>
            hxc (hrel.cons_cipher hx (mem_unusedRange_iff.mp hy) hgood).1
          rw [toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont y) P hbad, mul_zero]
    · -- Case 2: .inl (.inverse y)
      dsimp [idealLazyHandler, realLazyHandler, toPermQuery, fromPermAnswer,
        RandomPermutation.answer]
      cases hy : invLookup c_e y with
      | some x =>
        rw [hrel.invLookup_c_of_invLookup_e hy]
        simp only [PMF.pure_map, PMF.pure_bind, add_sub_cancel_right]
        exact ih x hrel
      | none =>
        have hne_e := hrel.partial_e.unusedDomain_nonempty hy
        simp only [dite_eq_left hne_e, PMF.map_comp, Function.comp_def, PMF.bind_map,
          toOuterMeasure_uniformOfFinset_bind]
        by_cases hyc : invLookup c (y - k.2) = none
        · have hne_c := hrel.partial_c.unusedDomain_nonempty hyc
          simp only [hyc, dite_eq_left hne_c, Function.comp_def, PMF.bind_map,
            toOuterMeasure_uniformOfFinset_bind]
          refine sum_uniform_le_of_good _ _ (Equiv.subRight k.1)
            (fun x => isBadEvenMansourKey ((x, y) :: c_e) c_π k) _ _
            hrel.map_unusedDomain_subset_e
            (fun x hbad => toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont x) P hbad) ?_
          intro x hx hgood
          obtain ⟨hxc, _, hrel'⟩ := hrel.cons_cipher (mem_unusedDomain_iff.mp hx) hy hgood
          refine ⟨mem_unusedDomain_iff.mpr hxc, ?_⟩
          simpa [Equiv.subRight] using ih x hrel'
        · refine (le_of_eq (Finset.sum_eq_zero fun x hx => ?_)).trans zero_le
          have hbad := Bool.eq_true_of_not_eq_false fun hgood =>
            hyc (hrel.cons_cipher (mem_unusedDomain_iff.mp hx) hy hgood).2.1
          rw [toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont x) P hbad, mul_zero]
    · -- Case 3: .inr (.forward u)
      dsimp [idealLazyHandler, realLazyHandler, toPermQuery, fromPermAnswer,
        RandomPermutation.answer]
      cases hu : c_π.lookup u with
      | some v =>
        rw [hrel.lookup_c_of_lookup_π hu]
        simp only [PMF.pure_map, PMF.pure_bind]
        exact ih v hrel
      | none =>
        have hne_π := hrel.partial_π.unusedRange_nonempty hu
        simp only [dite_eq_left hne_π, PMF.map_comp, Function.comp_def, PMF.bind_map,
          toOuterMeasure_uniformOfFinset_bind]
        by_cases huc : c.lookup u = none
        · have hne_c := hrel.partial_c.unusedRange_nonempty huc
          simp only [huc, dite_eq_left hne_c, Function.comp_def, PMF.bind_map,
            toOuterMeasure_uniformOfFinset_bind]
          refine sum_uniform_le_of_good _ _ (Equiv.refl G)
            (fun v => isBadEvenMansourKey c_e ((u, v) :: c_π) k) _ _
            (by simpa using hrel.unusedRange_subset_π)
            (fun v hbad => toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont v) P hbad) ?_
          intro v hv hgood
          obtain ⟨_, hvc, hrel'⟩ := hrel.cons_perm hu (mem_unusedRange_iff.mp hv) hgood
          exact ⟨mem_unusedRange_iff.mpr hvc, ih v hrel'⟩
        · refine (le_of_eq (Finset.sum_eq_zero fun v hv => ?_)).trans zero_le
          have hbad := Bool.eq_true_of_not_eq_false fun hgood =>
            huc (hrel.cons_perm hu (mem_unusedRange_iff.mp hv) hgood).1
          rw [toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont v) P hbad, mul_zero]
    · -- Case 4: .inr (.inverse v)
      dsimp [idealLazyHandler, realLazyHandler, toPermQuery, fromPermAnswer,
        RandomPermutation.answer]
      cases hv : invLookup c_π v with
      | some u =>
        rw [hrel.invLookup_c_of_invLookup_π hv]
        simp only [PMF.pure_map, PMF.pure_bind]
        exact ih u hrel
      | none =>
        have hne_π := hrel.partial_π.unusedDomain_nonempty hv
        simp only [dite_eq_left hne_π, PMF.map_comp, Function.comp_def, PMF.bind_map,
          toOuterMeasure_uniformOfFinset_bind]
        by_cases hvc : invLookup c v = none
        · have hne_c := hrel.partial_c.unusedDomain_nonempty hvc
          simp only [hvc, dite_eq_left hne_c, Function.comp_def, PMF.bind_map,
            toOuterMeasure_uniformOfFinset_bind]
          refine sum_uniform_le_of_good _ _ (Equiv.refl G)
            (fun u => isBadEvenMansourKey c_e ((u, v) :: c_π) k) _ _
            (by simpa using hrel.unusedDomain_subset_π)
            (fun u hbad => toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont u) P hbad) ?_
          intro u hu hgood
          obtain ⟨huc, _, hrel'⟩ := hrel.cons_perm (mem_unusedDomain_iff.mp hu) hv hgood
          exact ⟨mem_unusedDomain_iff.mpr huc, ih u hrel'⟩
        · refine (le_of_eq (Finset.sum_eq_zero fun u hu => ?_)).trans zero_le
          have hbad := Bool.eq_true_of_not_eq_false fun hgood =>
            hvc (hrel.cons_perm (mem_unusedDomain_iff.mp hu) hv hgood).2.1
          rw [toOuterMeasure_run_idealLazyHandler_eq_zero_of_bad (cont u) P hbad, mul_zero]

omit [AddGroup G] in
private theorem length_fst_idealLazyHandler_le {α : Type}
    {program : OracleComp (EvenMansourSpec G) α} {Q_e : ℕ}
    (h : IsCostBounded cipherCost program Q_e) {c_e c_π : Cache G}
    {res : α × (Cache G × Cache G)}
    (hmem : res ∈ ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).support) :
    res.2.1.length ≤ c_e.length + Q_e := by
  induction h generalizing c_e c_π with
  | pure a n =>
    change res ∈ (PMF.pure (a, (c_e, c_π))).support at hmem
    rw [PMF.mem_support_pure_iff] at hmem
    subst hmem
    exact Nat.le_add_right _ _
  | liftBind q cont n hcost ih =>
    change res ∈ ((idealLazyHandler q (c_e, c_π)).bind fun p =>
      (OracleComp.interpret idealLazyHandler (cont p.1)).run p.2).support at hmem
    rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨ans, c_e₁, c_π₁⟩, hstep, hcont⟩ := hmem
    cases q with
    | inl qe =>
      simp only [idealLazyHandler, PMF.mem_support_map_iff] at hstep
      obtain ⟨⟨a₀, ce₀⟩, hmem₀, heq⟩ := hstep
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj heq).2
      have hlen := length_le_of_mem_answer_support hmem₀
      have hih := ih ans hcont
      dsimp [cipherCost] at *
      omega
    | inr qπ =>
      simp only [idealLazyHandler, PMF.mem_support_map_iff] at hstep
      obtain ⟨⟨a₀, cπ₀⟩, _, heq⟩ := hstep
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj heq).2
      have hih := ih ans hcont
      dsimp [cipherCost] at *
      omega

omit [AddGroup G] in
private theorem length_snd_idealLazyHandler_le {α : Type}
    {program : OracleComp (EvenMansourSpec G) α} {Q_π : ℕ}
    (h : IsCostBounded permCost program Q_π) {c_e c_π : Cache G}
    {res : α × (Cache G × Cache G)}
    (hmem : res ∈ ((OracleComp.interpret idealLazyHandler program).run (c_e, c_π)).support) :
    res.2.2.length ≤ c_π.length + Q_π := by
  induction h generalizing c_e c_π with
  | pure a n =>
    change res ∈ (PMF.pure (a, (c_e, c_π))).support at hmem
    rw [PMF.mem_support_pure_iff] at hmem
    subst hmem
    exact Nat.le_add_right _ _
  | liftBind q cont n hcost ih =>
    change res ∈ ((idealLazyHandler q (c_e, c_π)).bind fun p =>
      (OracleComp.interpret idealLazyHandler (cont p.1)).run p.2).support at hmem
    rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨ans, c_e₁, c_π₁⟩, hstep, hcont⟩ := hmem
    cases q with
    | inl qe =>
      simp only [idealLazyHandler, PMF.mem_support_map_iff] at hstep
      obtain ⟨⟨a₀, ce₀⟩, _, heq⟩ := hstep
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj heq).2
      have hih := ih ans hcont
      dsimp [permCost] at *
      omega
    | inr qπ =>
      simp only [idealLazyHandler, PMF.mem_support_map_iff] at hstep
      obtain ⟨⟨a₀, cπ₀⟩, hmem₀, heq⟩ := hstep
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj heq).2
      have hlen := length_le_of_mem_answer_support hmem₀
      have hih := ih ans hcont
      dsimp [permCost] at *
      omega

private theorem idealGame_apply_le_realGame_add_of_keyDist (keyDist : PMF (G × G))
    {program : OracleComp (EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsCallBounded program Q_e Q_π) {ε : ℝ≥0∞}
    (hbad_le : ∀ c_e c_π : Cache G, c_e.length ≤ Q_e → c_π.length ≤ Q_π →
      keyDist.toOuterMeasure {k | isBadEvenMansourKey c_e c_π k = true} ≤ ε)
    (b : Bool) :
    evenMansourIdealGame program b ≤
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        keyDist.bind fun k => PMF.pure (evalEvenMansour π k.1 k.2 program)) b + ε := by
  let M_ideal := (OracleComp.interpret idealLazyHandler program).run ([], [])
  have hpoint (k : G × G) :
      evenMansourIdealGame program b ≤
        (((OracleComp.interpret (realLazyHandler k) program).run []).map Prod.fst) b +
          M_ideal.toOuterMeasure {res | isBadEvenMansourKey res.2.1 res.2.2 k = true} := by
    rw [evenMansourIdealGame_eq_lazy, ← PMF.toOuterMeasure_apply_singleton,
      ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_map_apply]
    have hsub : Prod.fst ⁻¹' ({b} : Set Bool) ⊆
        {res : Bool × (Cache G × Cache G) |
          res.1 = b ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} ∪
        {res : Bool × (Cache G × Cache G) | isBadEvenMansourKey res.2.1 res.2.2 k = true} := by
      intro res hres
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hres
      cases hbad : isBadEvenMansourKey res.2.1 res.2.2 k
      · exact Or.inl ⟨hres, hbad⟩
      · exact Or.inr hbad
    calc M_ideal.toOuterMeasure (Prod.fst ⁻¹' {b})
        ≤ M_ideal.toOuterMeasure
            ({res | res.1 = b ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} ∪
              {res | isBadEvenMansourKey res.2.1 res.2.2 k = true}) :=
          MeasureTheory.measure_mono hsub
      _ ≤ M_ideal.toOuterMeasure
            {res | res.1 = b ∧ isBadEvenMansourKey res.2.1 res.2.2 k = false} +
          M_ideal.toOuterMeasure {res | isBadEvenMansourKey res.2.1 res.2.2 k = true} :=
          MeasureTheory.measure_union_le _ _
      _ ≤ ((OracleComp.interpret (realLazyHandler k) program).run []).toOuterMeasure
            (Prod.fst ⁻¹' {b}) +
          M_ideal.toOuterMeasure {res | isBadEvenMansourKey res.2.1 res.2.2 k = true} :=
          add_le_add
            (run_idealLazyHandler_good_le_realLazyHandler program (· = b) k (cacheRel_nil k))
            le_rfl
  have hsum_ideal : ∑' k : G × G, keyDist k * evenMansourIdealGame program b =
      evenMansourIdealGame program b := by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hsum_real : (∑' k : G × G,
      keyDist k * (((OracleComp.interpret (realLazyHandler k) program).run []).map Prod.fst) b) =
      ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
        keyDist.bind fun k => PMF.pure (evalEvenMansour π k.1 k.2 program)) b := by
    rw [PMF.bind_comm]
    simp_rw [← realGameForKey_eq_lazy]
    rw [PMF.bind_apply]
  have hsum_bad : (∑' k : G × G,
      keyDist k * M_ideal.toOuterMeasure {res | isBadEvenMansourKey res.2.1 res.2.2 k = true}) ≤
      ε := by
    have hcomm : (keyDist.bind fun k =>
        M_ideal.map fun res => isBadEvenMansourKey res.2.1 res.2.2 k) true =
      (M_ideal.bind fun res =>
        keyDist.map fun k => isBadEvenMansourKey res.2.1 res.2.2 k) true := by
      simp only [PMF.map, Function.comp_def]
      rw [PMF.bind_comm]
    have hleft : (keyDist.bind fun k =>
        M_ideal.map fun res => isBadEvenMansourKey res.2.1 res.2.2 k) true =
      ∑' k : G × G,
        keyDist k *
          M_ideal.toOuterMeasure {res | isBadEvenMansourKey res.2.1 res.2.2 k = true} := by
      rw [PMF.bind_apply]
      congr 1; funext k; congr 1
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
      rfl
    have hright : (M_ideal.bind fun res =>
        keyDist.map fun k => isBadEvenMansourKey res.2.1 res.2.2 k) true =
      ∑' res : Bool × (Cache G × Cache G),
        M_ideal res *
          keyDist.toOuterMeasure {k | isBadEvenMansourKey res.2.1 res.2.2 k = true} := by
      rw [PMF.bind_apply]
      congr 1; funext res; congr 1
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
      rfl
    rw [← hleft, hcomm, hright]
    calc (∑' res : Bool × (Cache G × Cache G),
          M_ideal res * keyDist.toOuterMeasure {k | isBadEvenMansourKey res.2.1 res.2.2 k = true})
        ≤ ∑' res : Bool × (Cache G × Cache G), M_ideal res * ε := by
          refine tsum_le_tsum fun res => ?_
          by_cases hmem : res ∈ M_ideal.support
          · refine mul_le_mul_of_nonneg_left (hbad_le res.2.1 res.2.2 ?_ ?_) zero_le
            · simpa using length_fst_idealLazyHandler_le hcall.1 hmem
            · simpa using length_snd_idealLazyHandler_le hcall.2 hmem
          · rw [PMF.mem_support_iff, not_not] at hmem
            simp [hmem]
      _ = ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [← hsum_ideal, ← hsum_real]
  calc (∑' k : G × G, keyDist k * evenMansourIdealGame program b)
      ≤ ∑' k : G × G, keyDist k *
          ((((OracleComp.interpret (realLazyHandler k) program).run []).map Prod.fst) b +
            M_ideal.toOuterMeasure {res | isBadEvenMansourKey res.2.1 res.2.2 k = true}) :=
        tsum_le_tsum fun k => mul_le_mul_of_nonneg_left (hpoint k) zero_le
    _ = (∑' k : G × G,
          keyDist k *
            (((OracleComp.interpret (realLazyHandler k) program).run []).map Prod.fst) b) +
        (∑' k : G × G,
          keyDist k *
            M_ideal.toOuterMeasure {res | isBadEvenMansourKey res.2.1 res.2.2 k = true}) := by
        simp_rw [mul_add, tsum_add]
    _ ≤ _ := add_le_add le_rfl hsum_bad

private theorem advantage_le_of_forall_bool_le {g₁ g₂ : Game} {ε : ℝ≥0∞} (hε : ε ≠ ⊤)
    (hle : ∀ b : Bool, g₂ b ≤ g₁ b + ε) :
    (Game.advantage g₁ g₂ : ℝ) ≤ ε.toReal := by
  have htoReal (b : Bool) : (g₂ b).toReal ≤ (g₁ b).toReal + ε.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top g₁ b, hε⟩) (hle b)
    rwa [ENNReal.toReal_add (PMF.apply_ne_top g₁ b) hε] at h
  have h1 := PMF.sum_toReal g₁
  have h2 := PMF.sum_toReal g₂
  rw [Fintype.sum_bool] at h1 h2
  have ht := htoReal true
  have hf := htoReal false
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- **Even–Mansour PRP security in the ideal-permutation model** ([BonehShoup2023], Section 4.7,
Theorem 4.10; [EvenMansour1997]): for any adaptive distinguisher `program` making at most `Q_e`
cipher queries and at most `Q_π` primitive permutation queries (`IsCallBounded program Q_e Q_π`),
the distinguishing advantage between `evenMansourRealGame program` and
`evenMansourIdealGame program` is at most `2 * Q_e * Q_π / |G|`. -/
theorem advantage_evenMansourRealGame_evenMansourIdealGame_le
    {program : OracleComp (EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsCallBounded program Q_e Q_π) :
    (Game.advantage (evenMansourRealGame program) (evenMansourIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  let ε : ℝ≥0∞ := 2 * Q_e * Q_π * (Fintype.card G : ℝ≥0∞)⁻¹
  have hε : ε ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top _)) (ENNReal.natCast_ne_top _)) ?_
    simp [Fintype.card_ne_zero]
  have hle (b : Bool) :
      evenMansourIdealGame program b ≤ evenMansourRealGame program b + ε := by
    refine idealGame_apply_le_realGame_add_of_keyDist (PMF.uniformOfFintype (G × G)) hcall
      (fun c_e c_π he hπ => ?_) b
    exact (toOuterMeasure_isBadEvenMansourKey_le c_e c_π).trans
      (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr he))
        (Nat.cast_le.mpr hπ)) le_rfl)
  have hadv := advantage_le_of_forall_bool_le hε hle
  simpa [ε, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv] using hadv

/-- **Single-key Even–Mansour PRP security in the ideal-permutation model**
([DunkelmanKellerShamir2012]): for any adaptive distinguisher `program` making at most `Q_e` cipher
queries and at most `Q_π` primitive permutation queries (`IsCallBounded program Q_e Q_π`), the
distinguishing advantage between `singleKeyEvenMansourRealGame program` and
`evenMansourIdealGame program` is at most `2 * Q_e * Q_π / |G|`. -/
theorem advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le
    {program : OracleComp (EvenMansourSpec G) Bool} {Q_e Q_π : ℕ}
    (hcall : IsCallBounded program Q_e Q_π) :
    (Game.advantage (singleKeyEvenMansourRealGame program) (evenMansourIdealGame program) : ℝ) ≤
      2 * (Q_e : ℝ) * (Q_π : ℝ) / (Fintype.card G : ℝ) := by
  let ε : ℝ≥0∞ := 2 * Q_e * Q_π * (Fintype.card G : ℝ≥0∞)⁻¹
  have hε : ε ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.natCast_ne_top _)) (ENNReal.natCast_ne_top _)) ?_
    simp [Fintype.card_ne_zero]
  let keyDist : PMF (G × G) := (PMF.uniformOfFintype G).map fun k => (k, k)
  have hgame : ((PMF.uniformOfFintype (Equiv.Perm G)).bind fun π =>
      keyDist.bind fun k => PMF.pure (evalEvenMansour π k.1 k.2 program)) =
      singleKeyEvenMansourRealGame program := by
    simp only [keyDist, singleKeyEvenMansourRealGame, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.bind_map, Function.comp_def]
  have hle (b : Bool) :
      evenMansourIdealGame program b ≤ singleKeyEvenMansourRealGame program b + ε := by
    rw [← hgame]
    refine idealGame_apply_le_realGame_add_of_keyDist keyDist hcall (fun c_e c_π he hπ => ?_) b
    rw [PMF.toOuterMeasure_map_apply]
    exact (toOuterMeasure_isBadSingleKeyEvenMansour_le c_e c_π).trans
      (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (Nat.cast_le.mpr he))
        (Nat.cast_le.mpr hπ)) le_rfl)
  have hadv := advantage_le_of_forall_bool_le hε hle
  simpa [ε, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv] using hadv

end Coupling

end Cslib.Crypto.EvenMansour
