/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.UP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomially bounded ambiguity

`FewP` allows a polynomial number of accepting certificates on each input, extending the one-witness
condition of `UP`; see [Allender and Rubinstein][AllenderRubinstein1988] and the explicit
acceptance-set definition in
[Borchert, Hemaspaandra and Rothe, Section 1][BorchertHemaspaandraRothe2000].
This file uses exact-length verifier counts. `Classes.FewP.Machine` proves the equivalent native
finite-machine characterization, with a polynomial bound on accepting occurrence traces.

The containments and closures below are elementary consequences of the definition and the
existing `SharpP` algebra: addition adds the ambiguity bounds, multiplication multiplies them,
and polynomial-time precomposition composes a bound with a polynomially bounded output length.

## Main definitions

* `Cslib.Complexity.FewP`: NP with polynomially bounded accepting counts.

## Main results

* `Cslib.Complexity.UP_subset_FewP`, `Cslib.Complexity.FewP_subset_NP`.
* `Cslib.Complexity.union_mem_FewP`, `Cslib.Complexity.inter_mem_FewP`,
  `Cslib.Complexity.PolyTimeReducible.mem_FewP`.

## References

* [E. Allender, R. Rubinstein, *P-printable sets*][AllenderRubinstein1988]
* [B. Borchert, L. Hemaspaandra, J. Rothe,
  *Restrictive acceptance suffices for equivalence problems*][BorchertHemaspaandraRothe2000]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- A language in NP with a polynomial bound on the number of accepting certificates on every
input [Allender and Rubinstein][AllenderRubinstein1988]. The bound is in the encoded input length,
not in the certificate length. -/
def FewP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpP enc, ∃ p : Polynomial ℕ,
    (∀ a, f a ≤ p.eval (enc a).length) ∧ ∀ a, a ∈ A ↔ 0 < f a}

/-- A verifier characterization with a separate polynomial bound on its accepting count. -/
theorem mem_FewP : A ∈ FewP enc ↔ ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
    (∀ a, acceptCount V a (p.eval (enc a).length) ≤ q.eval (enc a).length) ∧
    ∀ a, a ∈ A ↔ 0 < acceptCount V a (p.eval (enc a).length) := by
  have this : A ∈ FewP enc ↔ ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      (∀ a, acceptCount V a (p.eval (enc a).length) ≤ q.eval (enc a).length) ∧ ∀ a, a ∈ A ↔ 0 <
      acceptCount V a (p.eval (enc a).length) := by
    constructor
    · rintro ⟨f, ⟨p, V, hV, hf⟩, q, hle, hA⟩
      exact ⟨p, q, V, hV.tidy, fun a => hf a ▸ hle a, fun a => by rw [hA a, hf a]⟩
    · rintro ⟨p, q, V, hV, hle, hA⟩
      exact ⟨_, ⟨p, V, .of_tidy hV, fun _ => rfl⟩, q, hle, hA⟩
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

/-- A bound of one is a polynomial ambiguity bound. -/
theorem UP_subset_FewP : UP enc ⊆ FewP enc := by
  rintro A ⟨f, hf, hle, hA⟩
  refine ⟨f, hf, 1, by simpa using hle, fun a => ?_⟩
  rw [hA a]
  have := hle a
  omega

/-- Forgetting the ambiguity bound gives NP membership. -/
theorem FewP_subset_NP : FewP enc ⊆ NP enc := by
  rintro A ⟨f, hf, -, -, hA⟩
  exact mem_NP_iff_exists_SharpP.mpr ⟨f, hf, hA⟩

/-- Union adds the two polynomial ambiguity bounds. -/
theorem union_mem_FewP (hA : A ∈ FewP enc) (hB : B ∈ FewP enc) : A ∪ B ∈ FewP enc := by
  obtain ⟨f, hf, p, hp, hA⟩ := hA
  obtain ⟨g, hg, q, hq, hB⟩ := hB
  exact ⟨f + g, SharpP.add_mem hf hg, p + q,
    fun a => by simpa using Nat.add_le_add (hp a) (hq a), fun a => by simp [hA a, hB a]⟩

/-- Intersection multiplies the two polynomial ambiguity bounds. -/
theorem inter_mem_FewP (hA : A ∈ FewP enc) (hB : B ∈ FewP enc) : A ∩ B ∈ FewP enc := by
  obtain ⟨f, hf, p, hp, hA⟩ := hA
  obtain ⟨g, hg, q, hq, hB⟩ := hB
  exact ⟨f * g, SharpP.mul_mem hf hg, p * q,
    fun a => by simpa using Nat.mul_le_mul (hp a) (hq a), fun a => by simp [hA a, hB a]⟩

/-- Polynomial-time reductions preserve a polynomial ambiguity bound. -/
theorem PolyTimeReducible.mem_FewP {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ FewP encB) : A ∈ FewP enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, hf, p, hp, hB⟩ := hB
  have hlen : ComputableTidilyInPolyTime (fun a => p.eval (encB (g a)).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval p).comp
      ((ComputableTidilyInPolyTime.encoding_length encB).comp hg.tidy)
  obtain ⟨q, hle⟩ := hlen.polyBounded.exists_polynomial
  exact ⟨f ∘ g, SharpP.comp_mem hf hg, q,
    fun a => (hp (g a)).trans (hle a), fun a => (hAB a).trans (hB (g a))⟩

end Cslib.Complexity
