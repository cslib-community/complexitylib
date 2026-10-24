/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Mathlib.Data.List.GetD

/-!
# The classes PCP(r, q)

A probabilistically checkable proof system for a problem `A` [Arora and Safra][AroraSafra1998],
[Arora and Barak, Chapter 11][AroraBarak09] is a verifier that, on an instance `a`, reads a random
string `ρ`, computes from `a` and `ρ` a list of positions in a proof `π`, reads the bits of `π` at
those positions, and accepts or rejects. Every member of `A` has a proof that is accepted for every
random string (completeness), and for a non-member every proof is rejected for at least half of the
random strings (soundness).

A verifier (`PCPVerifier`) consists of three functions: the number of random bits it uses on an
instance, the positions it queries, and its verdict on the instance, the random string and the
bits read. It is nonadaptive, as in Arora and Barak: the positions depend on the instance and the
random string, not on the bits read. A proof is a finite string, and a position past its end reads
as `false`. The verifier is polynomial-time (`PCPVerifier.PolyTime`) when all three functions are
computable in polynomial time, the numbers in binary. Time is measured in the length of the whole
input of each function, which includes the random string; when `r` is bounded by a polynomial, as
for all the usual classes, this is time polynomial in the length of the encoded instance.

`PCP r q enc` follows Arora and Barak in allowing constant factors: a problem is in it when, for
some constants `c` and `d`, a polynomial-time verifier uses at most `c * r n` random bits and at
most `d * q n` queries on instances whose encoding has length `n`. The verifier computes the number
of random bits it uses itself, and `r` only bounds it. (If the verifier were handed exactly
`c * r n` random bits, an uncomputable `r` could smuggle information into the length of the random
string and put undecidable problems into the class.)

The PCP theorem, `NP = PCP(log n, 1)`, is proved as `Cslib.Complexity.NP_eq_PCP_log` in
`Computability/PCP/Completeness`. Its construction and Dinur's combinatorial argument are in
`Cslib.PCP`.

## Main definitions

* `Cslib.Complexity.PCPVerifier`, with `PCPVerifier.accepts` and `PCPVerifier.PolyTime`.
* `Cslib.Complexity.IsPCPVerifier`: completeness, soundness and the bound on queries.
* `Cslib.Complexity.PCP`.

## Main results

* `Cslib.Complexity.PCP_mono_randomness`, `Cslib.Complexity.PCP_mono_queries`: more randomness or
  more queries give a larger class.

## References

* [S. Arora, S. Safra, *Probabilistic checking of proofs*][AroraSafra1998]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- A nonadaptive verifier of probabilistically checkable proofs for instances of type `α`. -/
structure PCPVerifier (α : Type) where
  /-- The number of random bits used on an instance. -/
  coins : α → ℕ
  /-- The positions of the proof read on an instance and a random string. -/
  queries : α × List Bool → List ℕ
  /-- The verdict on an instance, a random string, and the bits read at the queried positions. -/
  verdict : (α × List Bool) × List Bool → Bool

namespace PCPVerifier

/-- The bits of the proof `π` at the positions `is`; a position past the end of `π` reads as
`false`. -/
def answers (π : List Bool) (is : List ℕ) : List Bool := is.map fun i => π.getD i false

/-- Reading every position of a proof below its length recovers the proof. -/
theorem answers_range_length (π : List Bool) : answers π (List.range π.length) = π := by
  apply List.ext_getElem (by simp [answers])
  intro i _ h
  simp [answers, List.getElem?_eq_getElem h]

/-- The verdict of `V` on the instance `a` with the proof `π` and the random string `ρ`. -/
def accepts (V : PCPVerifier α) (a : α) (π ρ : List Bool) : Bool :=
  V.verdict ((a, ρ), answers π (V.queries (a, ρ)))

/-- A verifier is polynomial-time, with respect to the encoding `enc` of instances, when its
number of random bits, its queries and its verdict are computable in polynomial time, the numbers
in binary. -/
def PolyTime (enc : α ↪ List Bool) (V : PCPVerifier α) : Prop :=
  ComputableInPolyTime V.coins enc encNat ∧
    ComputableInPolyTime V.queries (encPair enc encBits) (encList encNat) ∧
    ComputableInPolyTime V.verdict (encPair (encPair enc encBits) encBits) encBool

end PCPVerifier

/-- `V` is a verifier for `A` using at most `r n` random bits and at most `q n` queries on instances
whose encoding has length `n`: every member of `A` has a proof that is accepted for every random
string, and for every non-member, every proof is accepted for at most half of the random strings.
The random strings on an instance `a` are those of length `V.coins a`. -/
def IsPCPVerifier (enc : α ↪ List Bool) (r q : ℕ → ℕ) (V : PCPVerifier α) (A : Set α) : Prop :=
  (∀ a, V.coins a ≤ r (enc a).length) ∧
    (∀ a (ρ : List Bool), ρ.length = V.coins a → (V.queries (a, ρ)).length ≤ q (enc a).length) ∧
    (∀ a ∈ A, ∃ π : List Bool, ∀ ρ : List Bool, ρ.length = V.coins a → V.accepts a π ρ = true) ∧
    ∀ a ∉ A, ∀ π : List Bool,
      2 * acceptCount (fun x => V.accepts x.1 π x.2) a (V.coins a) ≤ 2 ^ V.coins a

/-- The class `PCP(r, q)` with respect to the encoding `enc` of instances: the problems with a
polynomial-time verifier using `O(r n)` random bits and `O(q n)` queries on instances whose
encoding has length `n` [Arora and Safra][AroraSafra1998],
[Arora and Barak, Chapter 11][AroraBarak09]. -/
def PCP (r q : ℕ → ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (V : PCPVerifier α) (c d : ℕ), V.PolyTime enc ∧
    IsPCPVerifier enc (fun n => c * r n) (fun n => d * q n) V A}

variable {enc : α ↪ List Bool}

theorem mem_PCP {r q : ℕ → ℕ} {A : Set α} : A ∈ PCP r q enc ↔
    ∃ (V : PCPVerifier α) (c d : ℕ), V.PolyTime enc ∧
      IsPCPVerifier enc (fun n => c * r n) (fun n => d * q n) V A :=
  Iff.rfl

theorem IsPCPVerifier.mono_randomness {r r' q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α}
    (hr : ∀ n, r n ≤ r' n) (h : IsPCPVerifier enc r q V A) : IsPCPVerifier enc r' q V A :=
  ⟨fun a => (h.1 a).trans (hr _), h.2⟩

theorem IsPCPVerifier.mono_queries {r q q' : ℕ → ℕ} {V : PCPVerifier α} {A : Set α}
    (hq : ∀ n, q n ≤ q' n) (h : IsPCPVerifier enc r q V A) : IsPCPVerifier enc r q' V A :=
  ⟨h.1, fun a ρ hρ => (h.2.1 a ρ hρ).trans (hq _), h.2.2⟩

/-- More randomness gives a larger class. -/
theorem PCP_mono_randomness {r r' q : ℕ → ℕ} (hr : ∀ n, r n ≤ r' n) :
    PCP r q enc ⊆ PCP r' q enc :=
  fun _ ⟨V, c, d, hV, h⟩ => ⟨V, c, d, hV, h.mono_randomness fun n => Nat.mul_le_mul_left c (hr n)⟩

/-- More queries give a larger class. -/
theorem PCP_mono_queries {r q q' : ℕ → ℕ} (hq : ∀ n, q n ≤ q' n) : PCP r q enc ⊆ PCP r q' enc :=
  fun _ ⟨V, c, d, hV, h⟩ => ⟨V, c, d, hV, h.mono_queries fun n => Nat.mul_le_mul_left d (hq n)⟩

end Cslib.Complexity
