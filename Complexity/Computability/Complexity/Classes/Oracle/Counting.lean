/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle
public import Complexity.Computability.Complexity.Classes.SharpP
import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial time with a `#P` oracle

The oracle classes of `Cslib.Complexity.PWithOracle` query languages. The values of a function
`f : β → ℕ` are queried bit by bit: the *code* `encPair encβ encNat (b, i)` asks for bit `i` of
`f b`, under an encoding `encβ` of the arguments of `f`. An oracle language *answers the bits*
of `f` (`Cslib.Complexity.AnswersBits`) when it contains every code exactly when the requested
bit is `1`; it may answer other words arbitrarily. The bit graph of `f`
(`Cslib.Complexity.bitGraph`), which contains the codes of the bits `1` and nothing else,
answers the bits of `f`.

`P^#P` relative to the encoding `enc` of instances (`Cslib.Complexity.PWithSharpPOracle`)
consists of the problems `L` decided by one deterministic oracle program, strict oracle PPT as
in `Cslib.Complexity.ComputableInPolyTimeWithOracle`, that is correct against every oracle
language answering the bits of some function `f ∈ #P`, for some encoded type of arguments of
`f`. As for `Cslib.Complexity.RPWithPromiseOracle`, the program is fixed before the oracle, and
the answers on words that are not codes are arbitrary, so the program only learns bits of `f`;
in particular the oracle does not reveal which words are codes, however hard that is to decide.
Taking the bit graph as the oracle language, such a problem is in polynomial time relative to
the bit graph of a function in `#P` (`Cslib.Complexity.mem_PWithOracle_bitGraph`). The class
does not count queries; it contains `P` (`Cslib.Complexity.P_subset_PWithSharpPOracle`), and a
problem decided by one bit, at a polynomial position, of a function in `#P` on its own instances
is in it, by a program making one query
(`Cslib.Complexity.mem_PWithSharpPOracle_of_testBit`).

## Main definitions

* `Cslib.Complexity.AnswersBits`: an oracle language answering the bits of a function.
* `Cslib.Complexity.bitGraph`: the bits of a function, as an oracle language.
* `Cslib.Complexity.PWithSharpPOracle`: polynomial time with a `#P` oracle.

## Main results

* `Cslib.Complexity.answersBits_bitGraph`: the bit graph answers the bits.
* `Cslib.Complexity.mem_PWithOracle_bitGraph`: `P^#P` lies in polynomial time relative to the
  bit graph of a function in `#P`.
* `Cslib.Complexity.P_subset_PWithSharpPOracle`: `P ⊆ P^#P`.
* `Cslib.Complexity.mem_PWithSharpPOracle_of_testBit`: one bit of a `#P` value is in `P^#P`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α β : Type}

/-- The oracle language `A` **answers the bits** of `f : β → ℕ` under the encoding `encβ`: the
code `encPair encβ encNat (b, i)` is in `A` exactly when bit `i` of `f b` is `1`. Words that are
not codes may be in `A` or not. -/
def AnswersBits (encβ : β ↪ List Bool) (f : β → ℕ) (A : Set (List Bool)) : Prop :=
  ∀ b i, encPair encβ encNat (b, i) ∈ A ↔ (f b).testBit i

/-- The bit graph of `f : β → ℕ`: the codes `encPair encβ encNat (b, i)` such that bit `i` of
`f b` is `1`, and no other word. -/
def bitGraph (encβ : β ↪ List Bool) (f : β → ℕ) : Set (List Bool) :=
  encPair encβ encNat '' {x | (f x.1).testBit x.2}

/-- The bit graph answers the bits. -/
theorem answersBits_bitGraph (encβ : β ↪ List Bool) (f : β → ℕ) :
    AnswersBits encβ f (bitGraph encβ f) := fun _ _ =>
  (encPair encβ encNat).injective.mem_set_image

open Classical in
/-- **`P^#P`** [Arora and Barak, Chapter 17][AroraBarak09]: the problems `L` such that, for some
type `β` with encoding `encβ` and some `f ∈ SharpP encβ`, one deterministic oracle program, strict
oracle PPT on the encoding `enc` of instances, decides `L` against every oracle language answering
the bits of `f`. Answers on words that are not codes are arbitrary. -/
def PWithSharpPOracle (enc : α ↪ List Bool) : Set (Set α) :=
  {L | ∃ (β : Type) (encβ : β ↪ List Bool) (f : β → ℕ), f ∈ SharpP encβ ∧
    PolyTimeOracleProgram enc encBool (AnswersBits encβ f) (fun g => ∀ a, a ∈ L ↔ g a = true)}

variable {enc : α ↪ List Bool} {L : Set α}

/-- **`P^#P` lies in polynomial time relative to a `#P` bit graph**: against the bit graph of its
function, the program of a problem in `P^#P` decides it. -/
theorem mem_PWithOracle_bitGraph (hL : L ∈ PWithSharpPOracle enc) :
    ∃ (β : Type) (encβ : β ↪ List Bool) (f : β → ℕ), f ∈ SharpP encβ ∧
      L ∈ PWithOracle (bitGraph encβ f) enc := by
  classical
  obtain ⟨β, encβ, f, hf, hL⟩ := hL
  exact ⟨β, encβ, f, hf, hL.exists_computableInPolyTimeWithOracle (answersBits_bitGraph encβ f)⟩

/-- **`P ⊆ P^#P`**: a polynomial-time decider makes no query. -/
theorem P_subset_PWithSharpPOracle : P enc ⊆ PWithSharpPOracle enc := by
  rintro L ⟨g, hg, hL⟩
  exact ⟨α, enc, 0, SharpP.zero_mem, .of_polyTime hg fun _ _ => hL⟩

/-- **One bit of a `#P` value is in `P^#P`**: a problem decided by the bit at a polynomial
position of a function in `#P` on its own instances is in `P^#P`. The program asks for that bit,
with one query. -/
theorem mem_PWithSharpPOracle_of_testBit {f : α → ℕ} (hf : f ∈ SharpP enc)
    {p : Polynomial ℕ} (h : ∀ a, a ∈ L ↔ (f a).testBit (p.eval (enc a).length)) :
    L ∈ PWithSharpPOracle enc := by
  classical
  have hq : ComputableInPolyTime (fun a => encPair enc encNat (a, p.eval (enc a).length))
      enc encBits :=
    ComputableInPolyTime.encoding_comp (f := fun a => (a, p.eval (enc a).length))
      (ComputableInPolyTime.id'.prod
        (ComputableInPolyTime.unary_to_binary.comp (f := fun n : ℕ => n)
          (g := fun a => p.eval (enc a).length) (by fun_prop)))
  exact ⟨α, enc, f, hf, .of_query hq fun A hA a =>
    (h a).trans ((hA a (p.eval (enc a).length)).symm.trans decide_eq_true_iff.symm)⟩

end Cslib.Complexity
