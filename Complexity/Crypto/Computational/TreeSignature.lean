/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.IndexedSignature.Seeded
public import Complexity.Crypto.Computational.Signature
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import Complexity.Languages.Probabilistic.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Probability.PMF.Bind

/-!
# Stateless tree signatures from an indexed signature scheme

The stateless Merkle signature system of [BonehShoup2023], Section 14.6.3 (Fig. 14.7), over an
indexed signature scheme used at indices `0` and `1`. The signer owns a binary tree of depth
`depth n`. Every node `a ∈ {0, 1}^{< depth n}` holds a key pair of the indexed scheme derived from
a coin function `coins k`: the node's coins are `coins k (keyInput a) budget`, and the coins of the
signature at its index `u` are `coins k (signInput a u) budget`. Deriving both from the secret key
`k` makes every key pair and every internal signature a deterministic function of `k`, so repeated
signatures reuse them ([BonehShoup2023], Section 14.6.2, "The key management problem" and
"Generating internal keys using a PRF"); the indexed scheme's own randomized signer is run on
derived coins through `IndexedSignatureScheme.Seeded` (Exercise 13.6).

To sign `msg`, the signer checks that `msg` has length `n` (returning `[]` otherwise, matching
`SignatureScheme`'s `n`-bit message space), samples a uniform leaf `a₁ ⋯ a_d`, and certifies the
path: the node `a₁ ⋯ a_{i-1}` signs the public key of its child `a₁ ⋯ a_i` at index `a_i` for
`i < d`, and the node `a₁ ⋯ a_{d-1}` signs `msg` at index `a_d`. The signature is the leaf, the
`d - 1` certified child keys with their signatures, and the final signature. Verification
recomputes the chain from the root, checking that the leaf has length `depth n` and the chain
`depth n - 1` certificates. The public key is `(n, root public key)` and the secret key `(n, k)`
with `k` uniform of length `keyLen n`.

The scheme differs from Fig. 14.7 in four labelled ways: the root key pair is derived from `k`
like every other node, rather than sampled by key generation and stored in the secret key; the
tree is binary, using only the indices `0` and `1` of the indexed scheme; the public key carries
`n`, from which verification fixes the depth, which the source leaves to global parameters; and
verification checks the leaf length and the certificate count explicitly. The coins of a node's
signature depend on the node and the index only, not on what is signed.

The coin function is a parameter with a polynomial-time certificate. This module provides the
scheme, its completeness and its efficiency; its security ([BonehShoup2023], Theorem 14.6)
instantiates the coins with a pseudorandom function and is a separate development.

## Main definitions

* `Cslib.Crypto.TreeSignature.nodeKey`, `Cslib.Crypto.TreeSignature.signAt`: node keys and
  signatures from derived coins.
* `Cslib.Crypto.TreeSignature.certify`, `Cslib.Crypto.TreeSignature.signWithLeaf`: the
  certification chain and the signature at a leaf.
* `Cslib.Crypto.TreeSignature.keyGen`, `Cslib.Crypto.TreeSignature.sign`,
  `Cslib.Crypto.TreeSignature.verify`, `Cslib.Crypto.TreeSignature.scheme`: the algorithms and
  the signature scheme.

## Main results

* `Cslib.Crypto.TreeSignature.certify_spec`, `Cslib.Crypto.TreeSignature.verify_signWithLeaf`,
  `Cslib.Crypto.TreeSignature.verify_sign`: completeness.
* `Cslib.Crypto.TreeSignature.computableInPolyTime_certify`,
  `Cslib.Crypto.TreeSignature.isPPTOn_keyGen`, `Cslib.Crypto.TreeSignature.isPPTOn_sign`,
  `Cslib.Crypto.TreeSignature.computableInPolyTime_verify`: efficiency.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Sections 14.6.2 and 14.6.3.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace TreeSignature

variable (S : IndexedSignatureScheme) (T : S.Seeded)
  (coins : List Bool → List Bool → ℕ → List Bool) (keyLen depth : ℕ → ℕ)

/-! ### Derived keys and signatures -/

/-- The coin request of the key pair at node `path`. -/
def keyInput (path : List Bool) : List Bool := encPair encBool encBits (false, path)

/-- The coin request of the signature at index `u` of node `path`. -/
def signInput (path : List Bool) (u : ℕ) : List Bool :=
  encPair encBool (encPair encBits encUnary) (true, path, u)

/-- The key pair of node `path` at parameter `n` under the secret key `k`. -/
def nodeKey (n : ℕ) (k path : List Bool) : List Bool × List Bool :=
  T.keyGenWith n (coins k (keyInput path) (T.keyGenBudget n))

/-- The signature of `msg` at index `u` by node `path` holding the secret key `sk`, on the coins
derived from `k`. -/
def signAt (k path sk : List Bool) (u : ℕ) (msg : List Bool) : List Bool :=
  T.signWith sk u msg (coins k (signInput path u) (T.signBudget sk u msg))

/-! ### The certification chain -/

/-- The state of the certification chain: the current node, its key pair and the certificates
issued so far, each a child public key with its signature. -/
abbrev CertState := List Bool × (List Bool × List Bool) × List (List Bool × List Bool)

/-- One step of the chain: derive the child at `a`, sign its public key at index `a`, and move
to it. -/
def certifyStep (n : ℕ) (k : List Bool) (state : CertState) (a : Bool) : CertState :=
  let (node, (_, sk), certs) := state
  let child := nodeKey S T coins n k (node ++ [a])
  (node ++ [a], child, certs ++ [(child.1, signAt S T coins k node sk a.toNat child.1)])

/-- Certify the path `bits` from the root. -/
def certify (n : ℕ) (k bits : List Bool) : CertState :=
  bits.foldl (certifyStep S T coins n k) ([], nodeKey S T coins n k [], [])

/-- A tree signature: the leaf, the certified child keys with their signatures, and the final
signature on the message. -/
def encodeSignature (leaf : List Bool) (certs : List (List Bool × List Bool))
    (last : List Bool) : List Bool :=
  encPair encBits (encPair (encList (encPair encBits encBits)) encBits) (leaf, certs, last)

/-- Read the leaf, the certificates and the final signature of a signature word. -/
def signatureDecoder :
    Decoder (encPair encBits (encPair (encList (encPair encBits encBits)) encBits)) :=
  Decoder.bits.pair ((Decoder.bits.pair Decoder.bits).list.pair Decoder.bits)

/-- Read the parameter and the word of a key: the public key is `(n, root public key)` and the
secret key `(n, k)`. -/
def keyDecoder : Decoder (encPair encUnary encBits) := Decoder.unary.pair Decoder.bits

/-- Sign `msg` at the leaf `leaf`: certify the path to the leaf's parent, which signs `msg` at the
leaf's last bit. -/
def signWithLeaf (n : ℕ) (k leaf msg : List Bool) : List Bool :=
  let (node, (_, sk), certs) := certify S T coins n k leaf.dropLast
  encodeSignature leaf certs (signAt S T coins k node sk (leaf.getLastD false).toNat msg)

/-! ### The algorithms -/

include keyLen in
/-- Key generation: a uniform secret `k` of length `keyLen n`; the public key is the root's. -/
noncomputable def keyGen (n : ℕ) : ProbComp (List Bool × List Bool) := do
  let k ← BitString.sampleList (keyLen n)
  return (encPair encUnary encBits (n, (nodeKey S T coins n k []).1),
    encPair encUnary encBits (n, k))

include depth in
/-- Signing: when `msg` has length `n`, sample a uniform leaf of the depth-`depth n` tree and sign
there; otherwise return `[]`. -/
noncomputable def sign (sk msg : List Bool) : ProbComp (List Bool) :=
  let p := keyDecoder.decode sk
  if msg.length = p.1 then do
    let leaf ← BitString.sampleList (depth p.1)
    return signWithLeaf S T coins p.1 p.2 leaf msg
  else
    pure []

/-- One verification step: check the certificate `(pk', σ)` of the child at `a` under the current
public key, and move to the child. -/
def verifyStep (state : Bool × List Bool) (e : Bool × (List Bool × List Bool)) :
    Bool × List Bool :=
  let cert := e.2
  (state.1 && S.verify state.2 e.1.toNat cert.1 cert.2, cert.1)

/-- Verification: the leaf has length `depth n` with `depth n - 1` certificates, the certificates
chain from the root along the leaf's prefix, and the last certified key signs `msg` at the leaf's
last bit. -/
def verify (pk msg sig : List Bool) : Bool :=
  let p := keyDecoder.decode pk
  let (leaf, certs, last) := signatureDecoder.decode sig
  let r := (leaf.dropLast.zip certs).foldl (verifyStep S) (true, p.2)
  (leaf.length == depth p.1) && (certs.length + 1 == depth p.1) && r.1 &&
    S.verify r.2 (leaf.getLastD false).toNat msg last

/-! ### Completeness -/

variable {S T coins keyLen depth}

theorem certify_append (n : ℕ) (k bits : List Bool) (a : Bool) :
    certify S T coins n k (bits ++ [a]) =
      certifyStep S T coins n k (certify S T coins n k bits) a :=
  List.foldl_concat _ _ _ _

/-- The chain reaches the node `bits` with its key, issues one certificate per bit, and its
certificates verify from the root when both indices are below the capacity. -/
theorem certify_spec (n : ℕ) (hcap : 2 ≤ S.capacity n) (k bits : List Bool) :
    let (node, keys, certs) := certify S T coins n k bits
    node = bits ∧
      keys = nodeKey S T coins n k bits ∧
      certs.length = bits.length ∧
      (bits.zip certs).foldl (verifyStep S)
        (true, (nodeKey S T coins n k []).1) = (true, (nodeKey S T coins n k bits).1) := by
  induction bits using List.reverseRecOn with
  | nil => simp [certify]
  | append_singleton bits a ih =>
    obtain ⟨hpath, hkey, hlen, hchain⟩ := ih
    simp only [← certify.eq_1] at hpath hkey hlen hchain
    rw [certify_append]
    simp only [certifyStep, hpath, hkey, true_and]
    refine ⟨by simp [hlen], ?_⟩
    rw [List.zip_append hlen.symm, List.foldl_append, hchain]
    simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil, verifyStep,
      Bool.true_and]
    have hu : a.toNat < S.capacity n := by cases a <;> simp <;> omega
    have hv := S.verify_sign n (nodeKey S T coins n k bits) (T.keyGenWith_mem_support n _) a.toNat
      hu (nodeKey S T coins n k (bits ++ [a])).1
      (signAt S T coins k bits (nodeKey S T coins n k bits).2 a.toNat
        (nodeKey S T coins n k (bits ++ [a])).1) (T.signWith_mem_support _ _ _ _)
    rw [hv]

/-- **Completeness at a leaf**: a signature at a leaf of length `depth n ≥ 1` verifies under the
public key of the root. -/
theorem verify_signWithLeaf (n : ℕ) (hcap : 2 ≤ S.capacity n) (hdepth : 1 ≤ depth n)
    (k leaf : List Bool) (hleaf : leaf.length = depth n) (msg : List Bool) :
    verify S depth (encPair encUnary encBits (n, (nodeKey S T coins n k []).1)) msg
      (signWithLeaf S T coins n k leaf msg) = true := by
  obtain ⟨hpath, hkey, hlen, hchain⟩ :=
    certify_spec (T := T) (coins := coins) n hcap k leaf.dropLast
  simp only [← certify.eq_1] at hpath hkey hlen hchain
  have hu : (leaf.getLastD false).toNat < S.capacity n := by
    cases leaf.getLastD false <;> simp <;> omega
  have hv := S.verify_sign n (nodeKey S T coins n k leaf.dropLast) (T.keyGenWith_mem_support n _)
    _ hu msg (signAt S T coins k leaf.dropLast (nodeKey S T coins n k leaf.dropLast).2
      (leaf.getLastD false).toNat msg) (T.signWith_mem_support _ _ _ _)
  simp only [verify, signWithLeaf, encodeSignature, signatureDecoder.decode_enc,
    keyDecoder.decode_enc, hchain, hpath, hkey, hleaf, beq_self_eq_true, Bool.true_and]
  rw [hlen, List.length_dropLast, hleaf, Nat.sub_add_cancel hdepth, beq_self_eq_true, Bool.true_and,
    hv, Bool.and_self]

/-- Every supported key pair is `((n, root public key), (n, k))` for a `k` of length
`keyLen n`. -/
theorem mem_support_keyGen {n : ℕ} {keys : List Bool × List Bool}
    (h : keys ∈ (ProbComp.eval (keyGen S T coins keyLen n)).support) :
    ∃ k, k.length = keyLen n ∧
      keys = (encPair encUnary encBits (n, (nodeKey S T coins n k []).1),
        encPair encUnary encBits (n, k)) := by
  simp only [keyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff, BitString.eval_sampleList] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, BitString.length_of_mem_support_uniformList hk, rfl⟩

/-- **Completeness**: every honest signature on an `n`-bit message verifies, when the indexed
scheme has at least two indices and the tree has depth at least one. -/
theorem verify_sign (hcap : ∀ n, 2 ≤ S.capacity n) (hdepth : ∀ n, 1 ≤ depth n) (n : ℕ)
    (keys : List Bool × List Bool)
    (hkeys : keys ∈ (ProbComp.eval (keyGen S T coins keyLen n)).support)
    (msg : List Bool) (hmsg : msg.length = n) (sig : List Bool)
    (hsig : sig ∈ (ProbComp.eval (sign S T coins depth keys.2 msg)).support) :
    verify S depth keys.1 msg sig = true := by
  obtain ⟨k, -, rfl⟩ := mem_support_keyGen hkeys
  simp only [sign, keyDecoder.decode_enc, hmsg, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, BitString.eval_sampleList] at hsig
  obtain ⟨leaf, hleaf, rfl⟩ := hsig
  exact verify_signWithLeaf n (hcap n) (hdepth n) k leaf
    (BitString.length_of_mem_support_uniformList hleaf) msg

/-! ### Efficiency -/

section Efficiency

/-- The encoding of a chain state. -/
local notation "encCertState" =>
  encPair encBits (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))

@[local fun_prop] private theorem verify_fp {α : Type} {enc : α ↪ List Bool}
    {pk : α → List Bool} {u : α → ℕ} {msg sig : α → List Bool}
    (hpk : ComputableInPolyTime pk enc encBits) (hu : ComputableInPolyTime u enc encUnary)
    (hmsg : ComputableInPolyTime msg enc encBits) (hsig : ComputableInPolyTime sig enc encBits) :
    ComputableInPolyTime (fun x => S.verify (pk x) (u x) (msg x) (sig x)) enc encBool :=
  S.verify_polyTime.comp (hpk.prod (hu.prod (hmsg.prod hsig)))
@[local fun_prop] private theorem getLastD_fp {α : Type} {enc : α ↪ List Bool}
    {l : α → List Bool} (d : Bool) (hl : ComputableInPolyTime l enc encBits) :
    ComputableInPolyTime (fun x => (l x).getLastD d) enc encBool := by
  have heq : (fun x => (l x).getLastD d) = fun x => (l x).getD ((l x).length - 1) d := by
    funext x; rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  rw [heq]; fun_prop

attribute [local fun_prop] ComputableInPolyTime.bool_and' ComputableInPolyTime.sampleList
  IndexedSignatureScheme.Seeded.keyGenBudget_polyTime

variable (hcoins : ComputableInPolyTime
    (fun p : List Bool × List Bool × ℕ => coins p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encUnary)) encBits)

include hcoins in
/-- Node keys are computable in polynomial time from the parameter, the secret and the path. -/
theorem computableInPolyTime_nodeKey :
    ComputableInPolyTime
      (fun (((n, k), path) : (ℕ × List Bool) × List Bool) => nodeKey S T coins n k path)
      (encPair (encPair encUnary encBits) encBits) (encPair encBits encBits) := by
  have h1 : ComputableInPolyTime
      (fun x : (ℕ × List Bool) × List Bool => (x.1.2, keyInput x.2, T.keyGenBudget x.1.1))
      (encPair (encPair encUnary encBits) encBits)
      (encPair encBits (encPair encBits encUnary)) := by unfold keyInput; fun_prop
  exact T.keyGenWith_polyTime.comp
    ((ComputableInPolyTime.fst' (ComputableInPolyTime.fst' .id')).prod (hcoins.comp h1))

include hcoins in
/-- Node signatures are computable in polynomial time. -/
theorem computableInPolyTime_signAt :
    ComputableInPolyTime
      (fun (((k, path, sk), u, msg) : (List Bool × List Bool × List Bool) × ℕ × List Bool) =>
        signAt S T coins k path sk u msg)
      (encPair (encPair encBits (encPair encBits encBits)) (encPair encUnary encBits)) encBits := by
  have h2 : ComputableInPolyTime
      (fun x : (List Bool × List Bool × List Bool) × ℕ × List Bool => (x.1.2.2, x.2.1, x.2.2))
      (encPair (encPair encBits (encPair encBits encBits)) (encPair encUnary encBits))
      (encPair encBits (encPair encUnary encBits)) := by fun_prop
  have h1 : ComputableInPolyTime
      (fun x : (List Bool × List Bool × List Bool) × ℕ × List Bool =>
        (x.1.1, signInput x.1.2.1 x.2.1, T.signBudget x.1.2.2 x.2.1 x.2.2))
      (encPair (encPair encBits (encPair encBits encBits)) (encPair encUnary encBits))
      (encPair encBits (encPair encBits encUnary)) := by unfold signInput; fun_prop
  exact T.signWith_polyTime.comp (h2.prod (hcoins.comp h1))

include hcoins in
@[local fun_prop] private theorem nodeKey_fp {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {k path : α → List Bool} (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encBits) (hpath : ComputableInPolyTime path enc encBits) :
    ComputableInPolyTime (fun x => nodeKey S T coins (n x) (k x) (path x))
      enc (encPair encBits encBits) :=
  (computableInPolyTime_nodeKey (T := T) hcoins).comp ((hn.prod hk).prod hpath)

include hcoins in
@[local fun_prop] private theorem signAt_fp {α : Type} {enc : α ↪ List Bool}
    {k path sk : α → List Bool} {u : α → ℕ} {msg : α → List Bool}
    (hk : ComputableInPolyTime k enc encBits) (hpath : ComputableInPolyTime path enc encBits)
    (hsk : ComputableInPolyTime sk enc encBits) (hu : ComputableInPolyTime u enc encUnary)
    (hmsg : ComputableInPolyTime msg enc encBits) :
    ComputableInPolyTime (fun x => signAt S T coins (k x) (path x) (sk x) (u x) (msg x))
      enc encBits :=
  (computableInPolyTime_signAt (T := T) hcoins).comp
    ((hk.prod (hpath.prod hsk)).prod (hu.prod hmsg))

include hcoins in
/-- One chain step is computable in polynomial time. -/
theorem computableInPolyTime_certifyStep :
    ComputableInPolyTime
      (fun ((((n, k), state), a) : ((ℕ × List Bool) × CertState) × Bool) =>
        certifyStep S T coins n k state a)
      (encPair (encPair (encPair encUnary encBits) encCertState) encBool) encCertState := by
  dsimp only [certifyStep]
  fun_prop

/-- The encoding of the chain's input: the parameter, the secret and the path. -/
private abbrev encChainInput : (ℕ × List Bool) × List Bool ↪ List Bool :=
  encPair (encPair encUnary encBits) encBits

omit hcoins in
private theorem length_le_encChainInput (x : (ℕ × List Bool) × List Bool) :
    x.1.1 ≤ (encChainInput x).length ∧ x.1.2.length ≤ (encChainInput x).length ∧
      x.2.length ≤ (encChainInput x).length := by
  simp only [encChainInput, length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
  omega

include hcoins in
/-- The chain is computable in polynomial time: every node key and signature on the path is
polynomially bounded, and the chain has one certificate per bit. -/
theorem computableInPolyTime_certify :
    ComputableInPolyTime
      (fun (((n, k), bits) : (ℕ × List Bool) × List Bool) => certify S T coins n k bits)
      (encPair (encPair encUnary encBits) encBits) encCertState := by
  obtain ⟨ck, dk, hnodeLen⟩ :=
    (computableInPolyTime_nodeKey (T := T) hcoins).polyBounded_length.exists_le
  obtain ⟨cs, ds, hsignLen⟩ :=
    (computableInPolyTime_signAt (T := T) hcoins).polyBounded_length.exists_le
  let Bk (x : (ℕ × List Bool) × List Bool) : ℕ := ck * ((encChainInput x).length + 1) ^ dk
  let Bs (x : (ℕ × List Bool) × List Bool) : ℕ :=
    cs * (8 * (encChainInput x).length + 3 * Bk x + 11) ^ ds
  have hBk : PolyBounded (fun x => (encChainInput x).length) Bk :=
    PolyBounded.of_forall_le ck dk fun _ => le_rfl
  have hBs : PolyBounded (fun x => (encChainInput x).length) Bs :=
    (PolyBounded.const cs).mul (((((PolyBounded.const 8).mul .self).add
      ((PolyBounded.const 3).mul hBk)).add (.const 11)).pow ds)
  have hkeyLe (x : (ℕ × List Bool) × List Bool) {path : List Bool}
      (hpath : path.length ≤ x.2.length) :
      (nodeKey S T coins x.1.1 x.1.2 path).1.length ≤ Bk x ∧
        (nodeKey S T coins x.1.1 x.1.2 path).2.length ≤ Bk x := by
    have hle : (encChainInput (x.1, path)).length ≤ (encChainInput x).length := by
      simp only [encChainInput, length_encPair, encBits_apply]; omega
    have h := (hnodeLen (x.1, path)).trans
      (Nat.mul_le_mul_left ck (Nat.pow_le_pow_left (Nat.add_le_add_right hle 1) dk))
    exact ⟨(length_le_encPair_left encBits encBits _).trans h,
      (length_le_encPair_right encBits encBits _).trans h⟩
  have hsigLe (x : (ℕ × List Bool) × List Bool) {path sk msg : List Bool} {u : ℕ}
      (hpath : path.length ≤ x.2.length) (hsk : sk.length ≤ Bk x) (hu : u ≤ 1)
      (hmsg : msg.length ≤ Bk x) :
      (signAt S T coins x.1.2 path sk u msg).length ≤ Bs x := by
    have h := hsignLen ((x.1.2, path, sk), u, msg)
    simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate] at h
    have hx := length_le_encChainInput x
    exact h.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by omega) ds))
  refine ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.foldlWith_spec
    (encP := encPair encUnary encBits) (encA := encBool) (encL := encBits)
    (par := fun x : (ℕ × List Bool) × List Bool => x.1) (list := fun x => x.2)
    (init := fun x => (([], nodeKey S T coins x.1.1 x.1.2 [], []) : CertState))
    (step := fun par state a => certifyStep S T coins par.1 par.2 state a)
    (ComputableTidilyInPolyTime.fst _ _) (ComputableTidilyInPolyTime.snd _ _)
    (by apply ComputableInPolyTime.tidy; fun_prop)
    (computableInPolyTime_certifyStep (T := T) hcoins).tidy
    (fun x consumed state => state.1 = consumed ∧
      state.2.1 = nodeKey S T coins x.1.1 x.1.2 consumed ∧
      state.2.2.length = consumed.length ∧
      ∀ e ∈ state.2.2, e.1.length ≤ Bk x ∧ e.2.length ≤ Bs x)
    (fun x => ⟨rfl, rfl, rfl, by simp⟩) ?_
    (size := fun x => 2 * x.2.length + 6 * Bk x + 5 + x.2.length * (4 * Bk x + 2 * Bs x + 3))
    ?_ ?_).1
  · rintro x consumed ⟨path, key, certs⟩ a hprefix ⟨hpath, hkey, hlen, hcerts⟩
    have hconsumed : consumed.length + 1 ≤ x.2.length := by simpa using hprefix.length_le
    simp only at hpath hkey hlen; subst hpath hkey
    refine ⟨rfl, rfl, by simp [certifyStep, hlen], fun e he => ?_⟩
    simp only [certifyStep, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hcerts e he
    · exact ⟨(hkeyLe x (by simp; omega)).1,
        hsigLe x (by omega) (hkeyLe x (by omega)).2 (by cases a <;> simp)
          (hkeyLe x (by simp; omega)).1⟩
  · have hx2 : PolyBounded (fun x => (encChainInput x).length) fun x => x.2.length :=
      PolyBounded.self.mono fun x => (length_le_encChainInput x).2.2
    exact ((((PolyBounded.const 2).mul hx2).add ((PolyBounded.const 6).mul hBk)).add (.const 5)).add
      (hx2.mul ((((PolyBounded.const 4).mul hBk).add ((PolyBounded.const 2).mul hBs)).add
        (.const 3)))
  · rintro x consumed ⟨path, key, certs⟩ hprefix ⟨hpath, hkey, hlen, hcerts⟩
    simp only at hpath hkey hlen
    have hconsumed : consumed.length ≤ x.2.length := hprefix.length_le
    have hk := hkeyLe x hconsumed
    have hlist : (encList (encPair encBits encBits) certs).length ≤
        certs.length * (2 * (2 * Bk x + 1 + Bs x) + 1) :=
      length_encList_le _ _ fun e he => by
        have := hcerts e he; simp only [length_encPair, encBits_apply]; omega
    simp only [length_encPair, encBits_apply, hpath, hkey]
    rw [hlen] at hlist
    have := Nat.mul_le_mul hconsumed
      (show 2 * (2 * Bk x + 1 + Bs x) + 1 ≤ 4 * Bk x + 2 * Bs x + 3 by omega)
    omega

include hcoins in
@[local fun_prop] private theorem certify_fp {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {k bits : α → List Bool} (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encBits) (hb : ComputableInPolyTime bits enc encBits) :
    ComputableInPolyTime (fun x => certify S T coins (n x) (k x) (bits x)) enc encCertState :=
  (computableInPolyTime_certify (T := T) hcoins).comp ((hn.prod hk).prod hb)

include hcoins in
/-- Signing at a given leaf is computable in polynomial time. -/
theorem computableInPolyTime_signWithLeaf :
    ComputableInPolyTime
      (fun (((n, k), leaf, msg) : (ℕ × List Bool) × List Bool × List Bool) =>
        signWithLeaf S T coins n k leaf msg)
      (encPair (encPair encUnary encBits) (encPair encBits encBits)) encBits := by
  unfold signWithLeaf encodeSignature
  simpa only [List.dropLast_eq_take] using (by fun_prop :
    ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List Bool × List Bool =>
        let c := certify S T coins p.1.1 p.1.2 (p.2.1.take (p.2.1.length - 1))
        encPair encBits (encPair (encList (encPair encBits encBits)) encBits)
          (p.2.1, c.2.2, signAt S T coins p.1.2 c.1 c.2.1.2 (p.2.1.getLastD false).toNat p.2.2))
      (encPair (encPair encUnary encBits) (encPair encBits encBits)) encBits)

include hcoins in
@[local fun_prop] private theorem signWithLeaf_fp {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {k leaf msg : α → List Bool} (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encBits) (hl : ComputableInPolyTime leaf enc encBits)
    (hm : ComputableInPolyTime msg enc encBits) :
    ComputableInPolyTime (fun x => signWithLeaf S T coins (n x) (k x) (leaf x) (msg x))
      enc encBits :=
  (computableInPolyTime_signWithLeaf (T := T) hcoins).comp ((hn.prod hk).prod (hl.prod hm))

variable (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
  (hdepth : ComputableInPolyTime depth encUnary encUnary)

include hcoins hkeyLen in
/-- Key generation is uniformly strict PPT. -/
theorem isPPTOn_keyGen :
    IsPPTOn encUnary (encPair encBits encBits) (keyGen S T coins keyLen) := by
  unfold keyGen; fun_prop

include hcoins hdepth in
/-- Signing is uniformly strict PPT. -/
theorem isPPTOn_sign :
    IsPPTOn (encPair encBits encBits) encBits
      (fun p => sign S T coins depth p.1 p.2) := by
  have hyes : IsPPTOn (encPair encBits encBits) encBits
      (fun p : List Bool × List Bool => do
        let leaf ← BitString.sampleList (depth (keyDecoder.decode p.1).1)
        return signWithLeaf S T coins (keyDecoder.decode p.1).1 (keyDecoder.decode p.1).2 leaf
          p.2) := by fun_prop
  apply IsOraclePPTOn.isPPTOn
  simpa only [sign, apply_ite] using IsOraclePPTOn.ite'
    (condition := fun p : List Bool × List Bool => p.2.length = (keyDecoder.decode p.1).1)
    (by fun_prop) (hyes.isOraclePPTOn (Operation := Empty))
    (((ComputableInPolyTime.const []).isPPTOn).isOraclePPTOn (Operation := Empty))

variable (S) in
/-- The chain check of `verify`: fold the certificates along the leaf's prefix from `root`. -/
private def chainCheck (root leaf : List Bool) (certs : List (List Bool × List Bool)) :
    Bool × List Bool :=
  ((leaf.take (leaf.length - 1)).zip certs).foldl (verifyStep S) (true, root)

omit hcoins in
private theorem computableInPolyTime_chainCheck :
    ComputableInPolyTime
      (fun q : List Bool × List Bool × List (List Bool × List Bool) =>
        chainCheck S q.1 q.2.1 q.2.2)
      (encPair encBits (encPair encBits (encList (encPair encBits encBits))))
      (encPair encBool encBits) := by
  let encIn := encPair encBits (encPair encBits (encList (encPair encBits encBits)))
  have hzip : ComputableInPolyTime
      (fun q : List Bool × List Bool × List (List Bool × List Bool) =>
        (q.2.1.take (q.2.1.length - 1)).zip q.2.2)
      encIn (encList (encPair encBool (encPair encBits encBits))) :=
    (ComputableInPolyTime.zip encBool (encPair encBits encBits)).comp
      ((ComputableInPolyTime.bitsToList.comp (by fun_prop)).prod (by fun_prop))
  have hstep' : ComputableInPolyTime
      (fun p : (Bool × (Bool × List Bool)) × (Bool × (List Bool × List Bool)) =>
        verifyStep S p.1.2 p.2)
      (encPair (encPair encBool (encPair encBool encBits))
        (encPair encBool (encPair encBits encBits)))
      (encPair encBool encBits) := by dsimp only [verifyStep]; fun_prop
  refine ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (encP := encBool) (encA := encPair encBool (encPair encBits encBits))
    (encL := encList (encPair encBool (encPair encBits encBits)))
    (par := fun _ => false)
    (list := fun q : List Bool × List Bool × List (List Bool × List Bool) =>
      (q.2.1.take (q.2.1.length - 1)).zip q.2.2)
    (init := fun q => (true, q.1))
    (step := fun _ state e => verifyStep S state e)
    (.const false) hzip.tidy (by apply ComputableInPolyTime.tidy; fun_prop) hstep'.tidy
    (growth := fun q => (encIn q).length + 3)
    (PolyBounded.self.add (.const 3)) ?_)
  intro q state e he
  have hmem := length_le_encList_of_mem (encPair encBits encBits) (List.of_mem_zip he).2
  have hle : (encList (encPair encBits encBits) q.2.2).length ≤ (encIn q).length := by
    simp only [encIn, length_encPair]; omega
  simp only [verifyStep, length_encPair, encBits_apply, encBool_apply, List.length_singleton]
    at hmem ⊢
  omega

omit hcoins in
@[local fun_prop] private theorem chainCheck_fp {α : Type} {enc : α ↪ List Bool}
    {root leaf : α → List Bool} {certs : α → List (List Bool × List Bool)}
    (hr : ComputableInPolyTime root enc encBits) (hl : ComputableInPolyTime leaf enc encBits)
    (hc : ComputableInPolyTime certs enc (encList (encPair encBits encBits))) :
    ComputableInPolyTime (fun x => chainCheck S (root x) (leaf x) (certs x))
      enc (encPair encBool encBits) :=
  (computableInPolyTime_chainCheck (S := S)).comp (hr.prod (hl.prod hc))

omit hcoins in
include hdepth in
/-- Verification is computable in polynomial time. -/
theorem computableInPolyTime_verify :
    ComputableInPolyTime
      (fun ((pk, msg, sig) : List Bool × List Bool × List Bool) => verify S depth pk msg sig)
      (encPair encBits (encPair encBits encBits)) encBool := by
  dsimp only [verify]
  simpa only [chainCheck, List.dropLast_eq_take] using (by fun_prop :
    ComputableInPolyTime
      (fun p : List Bool × List Bool × List Bool =>
        let (n, root) := keyDecoder.decode p.1
        let (leaf, certs, lastSig) := signatureDecoder.decode p.2.2
        let (ok, cur) := chainCheck S root leaf certs
        (leaf.length == depth n) && (certs.length + 1 == depth n) && ok &&
          S.verify cur (leaf.getLastD false).toNat p.2.1 lastSig)
      (encPair encBits (encPair encBits encBits)) encBool)

end Efficiency

variable (S T coins keyLen depth) in
/-- **The stateless tree signature scheme** ([BonehShoup2023], Section 14.6.3, Fig. 14.7) over an
indexed scheme `S` with at least two indices, seeded by `T`, with node coins from `coins`, secrets
of length `keyLen n` and trees of depth `depth n ≥ 1`. -/
noncomputable def scheme
    (hcoins : ComputableInPolyTime
      (fun ((k, input, length) : List Bool × List Bool × ℕ) => coins k input length)
      (encPair encBits (encPair encBits encUnary)) encBits)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcap : ∀ n, 2 ≤ S.capacity n) (hdepth_pos : ∀ n, 1 ≤ depth n) : SignatureScheme where
  keyGen := keyGen S T coins keyLen
  sign := sign S T coins depth
  verify := verify S depth
  keyGen_ppt := isPPTOn_keyGen hcoins hkeyLen
  sign_ppt := isPPTOn_sign hcoins hdepth
  verify_polyTime := computableInPolyTime_verify hdepth
  verify_sign n keys hkeys msg hmsg sig hsig :=
    verify_sign hcap hdepth_pos n keys hkeys msg hmsg sig hsig

end TreeSignature

end Cslib.Crypto
