/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Basic
public import Complexity.Languages.Probabilistic.Repeat
public import Complexity.Languages.Probabilistic.Traverse
import Mathlib.Data.List.GetD

/-!
# Acyclic chains of encrypted secret keys

The sampler generates one more key pair than the requested depth, then encrypts each secret
key under the next public key. This is the acyclic construction of [Gentry2009, Section 2],
indexed in evaluation order. Sampling and support are explicit; no security claim is made here.
The returned key pairs retain the secret keys as private correctness witnesses. Public evaluation
uses only the public-key projection and encrypted links. Acyclicity refers to positions in the
chain; sampled key values may coincide.

## Main definitions

* `Cslib.Crypto.Homomorphic.Scheme.generateKeys`: independently sample the key pairs.
* `Cslib.Crypto.Homomorphic.Scheme.encryptKeyLinks`: encrypt secrets between adjacent keys.
* `Cslib.Crypto.Homomorphic.Scheme.generateKeyChain`: sample the keys and their encrypted links.
* `Cslib.Crypto.Homomorphic.Scheme.ValidLinks`: the links are pointwise fresh encryptions.

## Main results

* `Cslib.Crypto.Homomorphic.Scheme.mem_support_generateKeyChain_iff`: exact supported keys,
  key count, and encrypted links of the actual sampler.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*][Gentry2009]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Scheme

variable (E : Scheme)

/-- Independently sample one key pair for each level, including the initial level. -/
def generateKeys (n depth : ℕ) : ProbComp (List (List Bool × List Bool)) :=
  OracleComp.replicate (depth + 1) (E.keyGen n)

/-- Encrypt each old secret key under the next public key. Empty and singleton lists have no
links. -/
def encryptKeyLinks (n : ℕ) (keys : List (List Bool × List Bool)) :
    ProbComp (List (List (List Bool))) :=
  (keys.zip keys.tail).mapM (fun adjacent => E.encryptBits n adjacent.2.1 adjacent.1.2)

/-- Sample all key pairs before encrypting their adjacent secret-key links. The result retains
private secret-key witnesses and is not the public key artifact. -/
def generateKeyChain (n depth : ℕ) :
    ProbComp (List (List Bool × List Bool) × List (List (List Bool))) := do
  let keys ← E.generateKeys n depth
  let links ← E.encryptKeyLinks n keys
  pure (keys, links)

/-- Each link freshly encrypts the preceding secret key under the following public key. -/
def ValidLinks (n : ℕ) (keys : List (List Bool × List Bool))
    (links : List (List (List Bool))) : Prop :=
  List.Forall₂ (fun adjacent ek => E.FreshInputs n adjacent.2.1 adjacent.1.2 ek)
    (keys.zip keys.tail) links

/-- Sampling the keys fixes their number and requires exactly pointwise key-generation support. -/
theorem mem_support_generateKeys_iff (n depth : ℕ) (keys : List (List Bool × List Bool)) :
    keys ∈ (ProbComp.eval (E.generateKeys n depth)).support ↔
      keys.length = depth + 1 ∧ ∀ key ∈ keys, key ∈ (ProbComp.eval (E.keyGen n)).support :=
  ProbComp.mem_support_replicate_iff (depth + 1) (E.keyGen n) keys

/-- Supported outputs of the link sampler are exactly the valid links. -/
theorem mem_support_encryptKeyLinks_iff (n : ℕ) (keys : List (List Bool × List Bool))
    (links : List (List (List Bool))) :
    links ∈ (ProbComp.eval (E.encryptKeyLinks n keys)).support ↔ E.ValidLinks n keys links := by
  simp only [encryptKeyLinks, ProbComp.mem_support_mapM_iff, mem_support_encryptBits_iff,
    ValidLinks]

variable {E} in
/-- A valid chain has one fewer encrypted link than key pairs. -/
theorem ValidLinks.length_eq {n : ℕ} {keys : List (List Bool × List Bool)}
    {links : List (List (List Bool))} (h : E.ValidLinks n keys links) :
    links.length = keys.length - 1 := by
  have hlength := List.Forall₂.length_eq h
  simpa only [List.length_zip, List.length_tail, Nat.min_eq_right (Nat.sub_le _ _)]
    using hlength.symm

variable {E} in
/-- Dropping a prefix of keys and links preserves link validity on the remaining suffix. -/
theorem ValidLinks.drop {n : ℕ} {keys : List (List Bool × List Bool)}
    {links : List (List (List Bool))} (h : E.ValidLinks n keys links) (start : ℕ) :
    E.ValidLinks n (keys.drop start) (links.drop start) := by
  induction start generalizing keys links with
  | zero => exact h
  | succ start ih =>
    rcases keys with _ | ⟨k₁, _ | ⟨k₂, ks⟩⟩ <;> cases h
    · simp [ValidLinks]
    · simp [ValidLinks]
    · rename_i htail
      exact ih htail

variable {E} in
/-- At each link index, the link freshly encrypts that level's secret under the next public key.
The bounds ensure that none of the default values is used. -/
theorem ValidLinks.getD {n : ℕ} {keys : List (List Bool × List Bool)}
    {links : List (List (List Bool))} (h : E.ValidLinks n keys links)
    {i : ℕ} (hi : i < links.length) :
    E.FreshInputs n (keys.getD (i + 1) ([], [])).1 (keys.getD i ([], [])).2
      (links.getD i []) := by
  have hlength := h.length_eq
  have hfirst : i < keys.length := by omega
  have hnext : i + 1 < keys.length := by omega
  have hadjacent : i < (keys.zip keys.tail).length := by
    simp only [List.length_zip, List.length_tail]
    omega
  have hget := List.Forall₂.get h hadjacent hi
  simpa only [List.get_eq_getElem, List.getElem_zip, List.getElem_tail,
    List.getD_eq_getElem keys _ hfirst, List.getD_eq_getElem keys _ hnext,
    List.getD_eq_getElem links _ hi] using hget

/-- The actual key-chain sampler produces exactly supported keys and valid encrypted links. -/
theorem mem_support_generateKeyChain_iff (n depth : ℕ)
    (keys : List (List Bool × List Bool)) (links : List (List (List Bool))) :
    (keys, links) ∈ (ProbComp.eval (E.generateKeyChain n depth)).support ↔
      keys.length = depth + 1 ∧
      (∀ key ∈ keys, key ∈ (ProbComp.eval (E.keyGen n)).support) ∧
      E.ValidLinks n keys links := by
  simp only [generateKeyChain, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  constructor
  · rintro ⟨keys', hkeys, links', hlinks, hpair⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact ⟨((E.mem_support_generateKeys_iff n depth keys).1 hkeys).1,
      ((E.mem_support_generateKeys_iff n depth keys).1 hkeys).2,
      (E.mem_support_encryptKeyLinks_iff n keys links).1 hlinks⟩
  · rintro ⟨hcount, hkeys, hlinks⟩
    exact ⟨keys, (E.mem_support_generateKeys_iff n depth keys).2 ⟨hcount, hkeys⟩,
      links, (E.mem_support_encryptKeyLinks_iff n keys links).2 hlinks, rfl⟩

/-- Every supported key chain has the requested number of transitions and one additional key. -/
theorem lengths_of_mem_support_generateKeyChain {n depth : ℕ}
    {keys : List (List Bool × List Bool)} {links : List (List (List Bool))}
    (h : (keys, links) ∈ (ProbComp.eval (E.generateKeyChain n depth)).support) :
    keys.length = depth + 1 ∧ links.length = depth := by
  obtain ⟨hkeys, _, hlinks⟩ := (E.mem_support_generateKeyChain_iff n depth keys links).1 h
  exact ⟨hkeys, by simpa only [hkeys, Nat.add_sub_cancel] using hlinks.length_eq⟩

/-- Every position through the final level of a generated chain is a supported base key pair.
The index bound ensures that the default pair is never used. -/
theorem key_mem_support_of_generatedChain {n depth : ℕ}
    {keys : List (List Bool × List Bool)} {links : List (List (List Bool))}
    (h : (keys, links) ∈ (ProbComp.eval (E.generateKeyChain n depth)).support)
    {i : ℕ} (hi : i ≤ depth) :
    keys.getD i ([], []) ∈ (ProbComp.eval (E.keyGen n)).support := by
  obtain ⟨hlength, hkeys, _⟩ := (E.mem_support_generateKeyChain_iff n depth keys links).1 h
  have hindex : i < keys.length := by omega
  exact hkeys _ (by rw [List.getD_eq_getElem _ _ hindex]; exact List.getElem_mem _)

end Cslib.Crypto.Homomorphic.Scheme
