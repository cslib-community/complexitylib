/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Closure
public import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Complexity.Classes.Oracle.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Counting functions relative to a language oracle

`SharpPWithOracle A enc` counts accepted Boolean witnesses of a fixed polynomial length using
`ComputableInPolyTimeWithOracle A`. Its deterministic word-query program is fixed before the
witness and oracle replies. The certificate realizes that program under one polynomial clock
against every stateful word oracle, charging query construction and reply access. Correctness
of the Boolean verifier is required against the fixed, stateless `languageOracle A`.

`GapPWithOracle` consists of differences of two such counts. These definitions reuse the ordinary
verifier counting semantics; equivalence with nondeterministic oracle-machine counting is not
claimed. Ignoring an oracle embeds the ordinary classes, and the existing certified simulation
eliminates every polynomial-time decidable oracle. Oracle lowness for other classes is separate.

## Main definitions

* `Cslib.Complexity.SharpPWithOracle`: fixed-length counting with an oracle verifier.
* `Cslib.Complexity.GapPWithOracle`: differences of relativized counting functions.

## Main results

* `Cslib.Complexity.SharpP_subset_SharpPWithOracle`,
  `Cslib.Complexity.GapP_subset_GapPWithOracle`: ignore the oracle.
* `Cslib.Complexity.SharpPWithOracle_eq_SharpP`,
  `Cslib.Complexity.GapPWithOracle_eq_GapP`: eliminate an oracle in P.
* `Cslib.Complexity.computableInPolyTimeWithOracle_andVerifier`,
  `Cslib.Complexity.computableInPolyTimeWithOracle_selectVerifier`: reuse verifier combinators.
* `Cslib.Complexity.SharpPWithOracle.add_mem`,
  `Cslib.Complexity.SharpPWithOracle.mul_mem`,
  `Cslib.Complexity.SharpPWithOracle.natCast_mem_GapPWithOracle`: additive and multiplicative
  closure of `SharpPWithOracle` and embedding into `GapPWithOracle`.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994].
* [L. Fortnow, *Counting Complexity*][Fortnow1997], Lemma 3.6.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 3.4.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

/-- Count witnesses of exactly `p(|enc a|)` bits with a strict polynomial-time oracle verifier.
The oracle is fixed for correctness; its resource certificate applies to arbitrary replies. -/
def SharpPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTimeWithOracle A V (encPair enc encBits) encBool ∧
      ∀ a, f a = acceptCount V a (p.eval (enc a).length)}

/-- Integer differences of two counting functions relative to the same language oracle. -/
def GapPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) : Set (α → ℤ) :=
  {g | ∃ f₁ ∈ SharpPWithOracle A enc, ∃ f₂ ∈ SharpPWithOracle A enc,
    ∀ a, g a = (f₁ a : ℤ) - f₂ a}

/-- Ordinary counting verifiers can ignore every oracle. -/
theorem SharpP_subset_SharpPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    SharpP enc ⊆ SharpPWithOracle A enc := fun _ ⟨p, V, hV, hf⟩ =>
  ⟨p, V, hV.computableInPolyTimeWithOracle A, hf⟩

/-- Ordinary gap functions can ignore every oracle. -/
theorem GapP_subset_GapPWithOracle (A : Set (List Bool)) (enc : α ↪ List Bool) :
    GapP enc ⊆ GapPWithOracle A enc := fun _ ⟨f₁, h₁, f₂, h₂, hg⟩ =>
  ⟨f₁, SharpP_subset_SharpPWithOracle A enc h₁,
    f₂, SharpP_subset_SharpPWithOracle A enc h₂, hg⟩

/-- A polynomial-time oracle adds no counting functions. -/
theorem SharpPWithOracle_eq_SharpP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    SharpPWithOracle A enc = SharpP enc :=
  Set.Subset.antisymm (fun _ ⟨p, V, hV, hf⟩ =>
    ⟨p, V, hV.computableInPolyTime hA, hf⟩) (SharpP_subset_SharpPWithOracle A enc)

/-- A polynomial-time oracle adds no gap functions. -/
theorem GapPWithOracle_eq_GapP (hA : A ∈ P encBits) (enc : α ↪ List Bool) :
    GapPWithOracle A enc = GapP enc := by
  simp only [GapPWithOracle, SharpPWithOracle_eq_SharpP hA, GapP]

/-- Oracle verifiers can run on disjoint parts of a witness and conjoin their results. -/
theorem computableInPolyTimeWithOracle_andVerifier {k : α → ℕ}
    {V₁ V₂ : α × List Bool → Bool} (hk : ComputableInPolyTime k enc encUnary)
    (h₁ : ComputableInPolyTimeWithOracle A V₁ (encPair enc encBits) encBool)
    (h₂ : ComputableInPolyTimeWithOracle A V₂ (encPair enc encBits) encBool) :
    ComputableInPolyTimeWithOracle A (andVerifier k V₁ V₂) (encPair enc encBits) encBool := by
  unfold andVerifier
  exact ((h₁.preprocess (input := encPair enc encBits)
      (g := fun x : α × List Bool => (x.1, x.2.take (k x.1))) (by fun_prop)).prod
    (h₂.preprocess (input := encPair enc encBits)
      (g := fun x : α × List Bool => (x.1, x.2.drop (k x.1))) (by fun_prop))).map
      (g := fun b => b.1 && b.2) (output := encBool) (by fun_prop)

/-- The first witness bit selects between two oracle verifier results. Both certified programs
may be run sequentially, so the resource bound remains valid for arbitrary stateful replies. -/
theorem computableInPolyTimeWithOracle_selectVerifier {V₀ V₁ : α × List Bool → Bool}
    (h₀ : ComputableInPolyTimeWithOracle A V₀ (encPair enc encBits) encBool)
    (h₁ : ComputableInPolyTimeWithOracle A V₁ (encPair enc encBits) encBool) :
    ComputableInPolyTimeWithOracle A (selectVerifier V₀ V₁) (encPair enc encBits) encBool := by
  unfold selectVerifier
  exact (((h₀.prod h₁).preprocess (input := encPair enc encBits)
      (g := fun x : α × List Bool => (x.1, x.2.tail)))
    (by fun_prop)).map_with (g := fun x b => if x.2.headD false then b.2 else b.1)
      (output := encBool) (.of_tidy (by fun_prop))

namespace SharpPWithOracle

/-- The zero function is in `SharpPWithOracle A enc`. -/
theorem zero_mem : (0 : α → ℕ) ∈ SharpPWithOracle A enc :=
  SharpP_subset_SharpPWithOracle A enc SharpP.zero_mem

/-- **`SharpPWithOracle` is closed under addition**: the first bit of a certificate chooses the
verifier, and the bits that the chosen verifier does not read must be `false`. -/
theorem add_mem {f₁ f₂ : α → ℕ} (h₁ : f₁ ∈ SharpPWithOracle A enc)
    (h₂ : f₂ ∈ SharpPWithOracle A enc) :
    f₁ + f₂ ∈ SharpPWithOracle A enc := by
  obtain ⟨p₁, V₁, hV₁, hf₁⟩ := h₁
  obtain ⟨p₂, V₂, hV₂, hf₂⟩ := h₂
  have hfalse : ComputableInPolyTimeWithOracle A (allFalseVerifier (α := α))
      (encPair enc encBits) encBool :=
    computableInPolyTime_allFalseVerifier.computableInPolyTimeWithOracle A
  refine ⟨p₁ + p₂ + 1, selectVerifier
      (andVerifier (fun a => p₁.eval (enc a).length) V₁ allFalseVerifier)
      (andVerifier (fun a => p₂.eval (enc a).length) V₂ allFalseVerifier),
    computableInPolyTimeWithOracle_selectVerifier
      (computableInPolyTimeWithOracle_andVerifier (.of_tidy (by fun_prop)) hV₁ hfalse)
      (computableInPolyTimeWithOracle_andVerifier (.of_tidy (by fun_prop)) hV₂ hfalse),
    fun a => ?_⟩
  have e₁ := acceptCount_andVerifier_allFalseVerifier (fun a => p₁.eval (enc a).length) V₁ a
    (p₂.eval (enc a).length)
  have e₂ := acceptCount_andVerifier_allFalseVerifier (fun a => p₂.eval (enc a).length) V₂ a
    (p₁.eval (enc a).length)
  rw [Nat.add_comm (p₂.eval _)] at e₂
  rw [Pi.add_apply, hf₁ a, hf₂ a, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_one,
    acceptCount_selectVerifier, e₁, e₂]

/-- **`SharpPWithOracle` is closed under multiplication**: the two verifiers read disjoint parts of
the certificate. -/
theorem mul_mem {f₁ f₂ : α → ℕ} (h₁ : f₁ ∈ SharpPWithOracle A enc)
    (h₂ : f₂ ∈ SharpPWithOracle A enc) :
    f₁ * f₂ ∈ SharpPWithOracle A enc := by
  obtain ⟨p₁, V₁, hV₁, hf₁⟩ := h₁
  obtain ⟨p₂, V₂, hV₂, hf₂⟩ := h₂
  refine ⟨p₁ + p₂, andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂,
    computableInPolyTimeWithOracle_andVerifier (.of_tidy (by fun_prop)) hV₁ hV₂,
    fun a => ?_⟩
  rw [Pi.mul_apply, hf₁ a, hf₂ a, Polynomial.eval_add, acceptCount_andVerifier]

/-- A function in `SharpPWithOracle`, cast to the integers, is in `GapPWithOracle`. -/
theorem natCast_mem_GapPWithOracle {f : α → ℕ} (hf : f ∈ SharpPWithOracle A enc) :
    (fun a => (f a : ℤ)) ∈ GapPWithOracle A enc :=
  ⟨f, hf, 0, zero_mem, fun _ => by simp⟩

end SharpPWithOracle

end Cslib.Complexity
