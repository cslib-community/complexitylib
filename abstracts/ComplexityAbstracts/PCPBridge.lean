/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.SubsetSumBridge
import Complexity.Computability.PCP.Completeness

/-! # Transfer of the explicit PCP verifier contract to the certified gap construction -/

namespace ComplexityTests.Abstracts.PCPBridge

/-- Frame each bit as `[true, b]` and terminate the word with `[false]`. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Encode a pair by framing its first component and appending its second component. -/
def encodePair {α β : Type} (a : α → List Bool) (b : β → List Bool) (p : α × β) :
    List Bool := frame (a p.1) ++ b p.2

/-- Encode a list by concatenating its framed elements. -/
def encodeList {α : Type} (enc : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (frame ∘ enc)

theorem encodePair_injective {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    Function.Injective (encodePair a b) := CookLevinBridge.encodePair_injective a b

theorem encodeList_injective {α : Type} (enc : α ↪ List Bool) :
    Function.Injective (encodeList enc) := SubsetSumBridge.encodeList_injective enc

theorem bits_injective : Function.Injective Nat.bits := SubsetSumBridge.bits_injective

/-- Natural numbers are encoded by their canonical little-endian binary digits. -/
def encNat : ℕ ↪ List Bool := ⟨Nat.bits, bits_injective⟩

/-- Pair encoding; `↪` records injectivity. -/
def encPair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair a b, encodePair_injective a b⟩

/-- List encoding. -/
def encList {α : Type} (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨encodeList enc, encodeList_injective enc⟩

/-- A Boolean is encoded by a single bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- Bitstrings encode themselves. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

/-- A single finite-state binary multi-tape machine computes `f` on every encoded input,
within polynomial time and work space. Inputs are read-only; outputs are write-only.
`Cslib.PolynomiallyBounded` means bounded above by some polynomial. -/
def ComputableInPolyTime {α β : Type} (f : α → β)
    (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f a b t s

/-- NP consists of problems with a polynomial-time deterministic verifier and binary
certificates of an exact polynomial length. The verifier halts on every input pair. -/
def NP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
    ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true}

/-- Read a finite proof at the queried addresses. Positions beyond its end read as false. -/
def proofAnswers (proof : List Bool) (positions : List ℕ) : List Bool :=
  positions.map (fun i => proof.getD i false)

/-- The number of `n`-bit random strings on which the verifier accepts a fixed proof. -/
def acceptCount {α : Type} (queries : α × List Bool → List ℕ)
    (verdict : (α × List Bool) × List Bool → Bool) (a : α) (proof : List Bool) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun r : Fin n → Bool =>
    verdict ((a, List.ofFn r), proofAnswers proof (queries (a, List.ofFn r))) = true).card

/-- Nonadaptive probabilistically checkable proofs: one fixed polynomial-time algorithm
computes the number of random bits, the list of binary proof addresses and the final verdict.
For constants `c,d`, it uses at most `c*r(n)` random bits and `d*q(n)` queries. A yes-instance
has a finite proof accepted for every random string; on a no-instance every finite proof is
accepted on at most half of the random strings. -/
def PCP {α : Type} (r q : ℕ → ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (coins : α → ℕ) (queries : α × List Bool → List ℕ)
      (verdict : (α × List Bool) × List Bool → Bool) (c d : ℕ),
    ComputableInPolyTime coins enc encNat ∧
    ComputableInPolyTime queries (encPair enc encBits) (encList encNat) ∧
    ComputableInPolyTime verdict (encPair (encPair enc encBits) encBits) encBool ∧
    (∀ a, coins a ≤ c * r (enc a).length) ∧
    (∀ a ρ, ρ.length = coins a → (queries (a, ρ)).length ≤ d * q (enc a).length) ∧
    (∀ a ∈ A, ∃ proof : List Bool, ∀ ρ, ρ.length = coins a →
      verdict ((a, ρ), proofAnswers proof (queries (a, ρ))) = true) ∧
    ∀ a ∉ A, ∀ proof, 2 * acceptCount queries verdict a proof (coins a) ≤ 2 ^ coins a}

theorem pcp_eq {α : Type} (r q : ℕ → ℕ) (enc : α ↪ List Bool) :
    PCP r q enc = Cslib.Complexity.PCP r q enc := by
  ext A
  constructor
  · rintro ⟨coins, queries, verdict, c, d, hc, hq, hv, hbound, hquery, hyes, hno⟩
    exact ⟨⟨coins, queries, verdict⟩, c, d,
      ⟨hc, hq, hv⟩,
      hbound, hquery, hyes, hno⟩
  · rintro ⟨⟨coins, queries, verdict⟩, c, d, ⟨hc, hq, hv⟩, hbound, hquery, hyes, hno⟩
    exact ⟨coins, queries, verdict, c, d,
      hc, hq, hv, hbound, hquery, hyes, hno⟩

theorem pcp_theorem {α : Type} (enc : α ↪ List Bool) :
    NP enc = PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) enc := by
  rw [pcp_eq]
  have hNP : NP enc = Cslib.Complexity.NP enc := Set.ext fun _ => CookLevinBridge.mem_NP_iff
  rw [hNP]
  exact Cslib.Complexity.NP_eq_PCP_log enc

end ComplexityTests.Abstracts.PCPBridge
