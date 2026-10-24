/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The class NP

`NP` is defined through polynomial-time verifiers [Arora and Barak, Definition 2.1][AroraBarak09]:
`A ∈ NP enc` when there are a polynomial `p` and a function `V : α × List Bool → Bool`, computable
in polynomial time on inputs `encPair enc encBits (a, w) = frame (enc a) ++ w`, such that `a ∈ A`
exactly when some certificate `w` of length `p (enc a).length` makes `V (a, w)` true.

Two details follow the textbook and matter for reductions. The certificate length is fixed, so the
input length of the verifier is a function of the instance alone. And `p` is a polynomial, not
merely a polynomially bounded function: a reduction from an `NP` problem must be able to compute
where the certificate ends, which an arbitrary bound would not allow.

`NP` is exactly the class of problems decided in polynomial time by nondeterministic machines
with a binary alphabet and finitely many states (`Cslib.Complexity.mem_NP_iff_decidableInPolyTime`
in `Complexity.Computability.Complexity.Classes.NP.Nondeterministic`): such a machine guesses a
certificate and verifies it, and conversely a verifier checks an encoded accepting computation.

Verifiers are usually built from short certificates padded with `false` to the prescribed length
(`Cslib.Complexity.IsVerifier.of_padding`); `Complexity.Computability.Complexity.Classes.NP.Witness`
builds them from polynomial-time witness relations.

The verifier's efficiency can equally be stated in upstream terms: some machine computes it, in the
sense of `Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`, within time and space bounded by
polynomially bounded functions of the length of its encoded input, which pairs the instance with
the certificate (`Cslib.Complexity.mem_NP_iff_exists_computableInTimeAndSpaceOfLength`).

## Main definitions

* `Cslib.Complexity.IsVerifier`: the verifier condition.
* `Cslib.Complexity.NP`, `Cslib.Complexity.coNP`.

## Main results

* `Cslib.Complexity.mem_NP_iff_exists_computableInTimeAndSpaceOfLength`: `NP` with verifiers
  computed in the sense of upstream `Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`.
* `Cslib.Complexity.IsVerifier.of_padding`: a verifier that accepts certificates of exactly the
  prescribed length only for members, and accepts for every member some short prefix whatever
  padding by `false` follows it, verifies with certificates of exactly that length.
* `Cslib.Complexity.IsVerifier.guard`: guarding a verifier by a test on instances verifies the
  members that pass the test.
* `Cslib.Complexity.NP_eq_coNP_iff_coNP_subset_NP`: `NP = coNP` exactly when `coNP ⊆ NP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- `V` verifies `A` with certificates whose length is `p` evaluated at the length of the encoded
instance: `a ∈ A` iff some such certificate is accepted. -/
def IsVerifier (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool) (A : Set α) :
    Prop :=
  ∀ a, a ∈ A ↔ ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true

/-- The problems with polynomial-time verifiers and polynomially long certificates, with respect to
the encoding `enc` of instances [Arora and Barak, Definition 2.1][AroraBarak09]. -/
def NP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsVerifier enc p V A}

theorem mem_NP {enc : α ↪ List Bool} {A : Set α} :
    A ∈ NP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsVerifier enc p V A :=
  Iff.rfl

/-- **`NP` in upstream terms:** `A ∈ NP enc` exactly when, for a polynomial `p`, some verifier for
`A` with certificates of length `p` is computed by a machine with a binary alphabet and finitely
many states within time and space bounded by polynomially bounded functions of the length of the
encoded pair of an instance and a certificate. -/
theorem mem_NP_iff_exists_computableInTimeAndSpaceOfLength {enc : α ↪ List Bool} {A : Set α} :
    A ∈ NP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool) (t s : ℕ → ℕ),
      PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
        ComputableInTimeAndSpaceOfLength V (encPair enc encBits) encBool t s ∧
          IsVerifier enc p V A :=
  ⟨fun ⟨p, V, ⟨t, s, ht, hs, hV⟩, hA⟩ => ⟨p, V, t, s, ht, hs, hV, hA⟩,
    fun ⟨p, V, t, s, ht, hs, hV, hA⟩ => ⟨p, V, ⟨t, s, ht, hs, hV⟩, hA⟩⟩

/-! ### Padded certificates -/

section Padding

variable {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool} {A : Set α}

/-- **Padded certificates.** A verifier verifies `A` with certificates of length exactly
`p (enc a).length` if it accepts certificates of that length only for members of `A`, and every
member has a prefix `u` of at most that length which is accepted whatever padding by `false`
follows it. -/
theorem IsVerifier.of_padding
    (sound : ∀ a w, w.length = p.eval (enc a).length → V (a, w) = true → a ∈ A)
    (complete : ∀ a ∈ A, ∃ u : List Bool, u.length ≤ p.eval (enc a).length ∧
      ∀ k, V (a, u ++ List.replicate k false) = true) :
    IsVerifier enc p V A := fun a =>
  ⟨fun ha =>
    let ⟨u, hu, hV⟩ := complete a ha
    ⟨u ++ List.replicate (p.eval (enc a).length - u.length) false, by
      rw [List.length_append, List.length_replicate, Nat.add_sub_cancel' hu], hV _⟩,
    fun ⟨w, hw, hV⟩ => sound a w hw hV⟩

/-- Guarding a verifier by a test `c` on instances verifies the members of `A` that pass the
test. -/
theorem IsVerifier.guard {c : α → Bool} (h : IsVerifier enc p V A) :
    IsVerifier enc p (fun x => c x.1 && V x) {a | c a = true ∧ a ∈ A} := fun a => by
  simp only [Set.mem_ofPred_eq, Bool.and_eq_true, h a]
  exact ⟨fun ⟨hc, w, hw, hV⟩ => ⟨w, hw, hc, hV⟩, fun ⟨w, hw, hc, hV⟩ => ⟨hc, w, hw, hV⟩⟩

end Padding

/-- The problems whose complements are in `NP` [Arora and Barak, Section 2.6][AroraBarak09]. -/
def coNP (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ NP enc}

theorem mem_coNP {enc : α ↪ List Bool} {A : Set α} : A ∈ coNP enc ↔ Aᶜ ∈ NP enc := Iff.rfl

theorem coNP_eq_preimage_compl_NP (enc : α ↪ List Bool) : coNP enc = compl ⁻¹' NP enc := rfl

/-- `NP = coNP`, for problems with every encoding of their instances, exactly when `coNP ⊆ NP`
for all of them. -/
theorem NP_eq_coNP_iff_coNP_subset_NP :
    (∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) ↔
      ∀ {γ : Type} (encC : γ ↪ List Bool), coNP encC ⊆ NP encC := by
  refine ⟨fun h _ encC => (h encC).ge, fun h _ encC => ?_⟩
  refine Set.Subset.antisymm (fun A hA => ?_) (h encC)
  rw [mem_coNP]
  exact h encC (by rwa [mem_coNP, compl_compl])

end Cslib.Complexity
