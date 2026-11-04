/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.AcceptCount
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Fintype.Pi

/-!
# The counting classes #P and GapP

`#P` is defined through polynomial-time verifiers, like `NP` (`Cslib.Complexity.NP`)
[Valiant][Valiant1979], [Arora and Barak, Chapter 17][AroraBarak09]: `f ∈ SharpP enc` when there
are a polynomial `p` and a function `V : α × List Bool → Bool`, computable in polynomial time on
inputs `encPair enc encBits (a, w) = frame (enc a) ++ w`, such that `f a` is the number of strings
`w` of length `p (enc a).length` with `V (a, w) = true`, the count `Cslib.Complexity.acceptCount`
of `Complexity.Computability.Complexity.AcceptCount`. The problems in `NP` are exactly the sets
where functions in `#P` are nonzero (`mem_NP_iff_exists_SharpP`).

`GapP` consists of the differences of two functions in `#P`. Fenner, Fortnow and Kurtz define it
through the differences between the numbers of accepting and rejecting paths of nondeterministic
machines, and show that this gives the differences of functions in `#P`
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]; here that characterisation is the
definition. `Classes.SharpP.Machine` proves that both polynomial-clock terminal counts of a
fixed finite-control list-choice machine are in `#P`, and their difference is in `GapP`.
`Classes.SharpP.Characterization` supplies the actual reverse verifier construction and the
bidirectional `#P` machine characterization. `Classes.SharpP.GapMachine` supplies balanced
signed routing and the corresponding bidirectional `GapP` characterization.

## Main definitions

* `Cslib.Complexity.SharpP`, `Cslib.Complexity.GapP`.

## Main results

* `Cslib.Complexity.mem_NP_iff_exists_SharpP`: `NP` consists of the supports of functions in `#P`.
* `Cslib.Complexity.SharpP.exists_le_two_pow`: functions in `#P` are at most exponential.
* `Cslib.Complexity.GapP.exists_abs_le_two_pow`: every `GapP` function is bounded in absolute value
  by `2 ^ p(|x|)` for a polynomial `p`.
* `Cslib.Complexity.GapP.neg_mem`: `GapP` is closed under negation.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- The functions counting the certificates that a polynomial-time verifier accepts, with
certificates of polynomial length, with respect to the encoding `enc` of instances. -/
def SharpP (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a, f a = acceptCount V a (p.eval (enc a).length)}

/-- The differences of two functions in `#P`, with respect to the encoding `enc` of instances. -/
def GapP (enc : α ↪ List Bool) : Set (α → ℤ) :=
  {g | ∃ f₁ ∈ SharpP enc, ∃ f₂ ∈ SharpP enc, ∀ a, g a = f₁ a - f₂ a}

variable {enc : α ↪ List Bool}

theorem mem_SharpP {f : α → ℕ} : f ∈ SharpP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a, f a = acceptCount V a (p.eval (enc a).length) :=
  Iff.rfl

theorem mem_GapP {g : α → ℤ} :
    g ∈ GapP enc ↔ ∃ f₁ ∈ SharpP enc, ∃ f₂ ∈ SharpP enc, ∀ a, g a = f₁ a - f₂ a :=
  Iff.rfl

/-- **`NP` consists of the supports of functions in `#P`**: a problem is in `NP` exactly when it
is the set of instances where some function in `#P` is nonzero. -/
theorem mem_NP_iff_exists_SharpP {A : Set α} :
    A ∈ NP enc ↔ ∃ f ∈ SharpP enc, ∀ a, a ∈ A ↔ 0 < f a := by
  constructor
  · rintro ⟨p, V, hV, h⟩
    exact ⟨_, ⟨p, V, hV, fun _ => rfl⟩, fun a => (h a).trans acceptCount_pos_iff.symm⟩
  · rintro ⟨f, ⟨p, V, hV, hf⟩, h⟩
    exact ⟨p, V, hV, fun a => by rw [h a, hf a, acceptCount_pos_iff]⟩

namespace SharpP

/-- The zero function is in `#P`: no certificate is accepted. -/
theorem zero_mem : (0 : α → ℕ) ∈ SharpP enc :=
  ⟨0, fun _ => false, .const false, fun a => (acceptCount_false a _).symm⟩

/-- A function in `#P` is at most exponential in the length of the encoded instance. -/
theorem exists_le_two_pow {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ∃ p : Polynomial ℕ, ∀ a, f a ≤ 2 ^ p.eval (enc a).length :=
  let ⟨p, _, _, h⟩ := hf
  ⟨p, fun a => (h a).trans_le acceptCount_le_two_pow⟩

end SharpP

namespace GapP

/-- Every function in `GapP` is bounded in absolute value by `2 ^ p(|x|)` for a polynomial `p`. -/
theorem exists_abs_le_two_pow {g : α → ℤ} (hg : g ∈ GapP enc) :
    ∃ p : Polynomial ℕ, ∀ a, |g a| ≤ (2 : ℤ) ^ p.eval (enc a).length := by
  obtain ⟨f₁, hf₁, f₂, hf₂, h⟩ := hg
  obtain ⟨p₁, hp₁⟩ := SharpP.exists_le_two_pow hf₁
  obtain ⟨p₂, hp₂⟩ := SharpP.exists_le_two_pow hf₂
  refine ⟨p₁ + p₂, fun a => ?_⟩
  have h₁ : (f₁ a : ℤ) ≤ (2 : ℤ) ^ (p₁ + p₂).eval (enc a).length := by
    exact_mod_cast (hp₁ a).trans (Nat.pow_le_pow_right (by omega)
      (by simp only [Polynomial.eval_add]; omega))
  have h₂ : (f₂ a : ℤ) ≤ (2 : ℤ) ^ (p₁ + p₂).eval (enc a).length := by
    exact_mod_cast (hp₂ a).trans (Nat.pow_le_pow_right (by omega)
      (by simp only [Polynomial.eval_add]; omega))
  have hf₁_nonneg : (0 : ℤ) ≤ f₁ a := Int.natCast_nonneg _
  have hf₂_nonneg : (0 : ℤ) ≤ f₂ a := Int.natCast_nonneg _
  rw [h a, abs_le]
  omega

/-- The difference of two functions in `#P`, cast to the integers, is in `GapP`. -/
theorem natCast_sub_natCast_mem {f₁ f₂ : α → ℕ} (hf₁ : f₁ ∈ SharpP enc)
    (hf₂ : f₂ ∈ SharpP enc) : (fun a => (f₁ a : ℤ) - f₂ a) ∈ GapP enc :=
  ⟨f₁, hf₁, f₂, hf₂, fun _ => rfl⟩

/-- `GapP` is closed under negation: exchange the two functions in `#P`. -/
theorem neg_mem {g : α → ℤ} (hg : g ∈ GapP enc) : -g ∈ GapP enc :=
  let ⟨f₁, hf₁, f₂, hf₂, h⟩ := hg
  ⟨f₂, hf₂, f₁, hf₁, fun a => by rw [Pi.neg_apply, h a, neg_sub]⟩

end GapP

end Cslib.Complexity
