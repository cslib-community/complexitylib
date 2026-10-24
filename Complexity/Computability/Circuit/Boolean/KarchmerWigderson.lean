/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.BinaryCost
public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Computability.Communication.KarchmerWigderson

/-!
# The Karchmer–Wigderson theorem

In the *Karchmer–Wigderson game* of a Boolean function `f`, Alice holds an input `x` with
`f x = 1`, Bob holds an input `y` with `f y = 0`, and they must find a bit where `x` and `y`
differ (`Communication.DiffersAt`). **Karchmer and Wigderson** showed that the least depth of a
De Morgan formula for `f`, with negations free, is the communication complexity of this game
(`formulaDepth_eq_ecomplexity`) [KarchmerWigderson1990], [Jukna, Section 3.3][Jukna2012],
[Kushilevitz and Nisan, Chapter 10][KushilevitzNisan1997].

A formula gives a protocol (`Formula.kwProtocol`): at an AND gate, the player holding the input
where the gate is false says which argument is false there; at an OR gate, the player holding the
input where it is true says which argument is true; a negation exchanges the roles; an input leaf
names its bit. Conversely a protocol gives a formula (`Protocol.kwFormula`), with an OR at each of
Alice's nodes, an AND at each of Bob's, and at each leaf the literal that separates the inputs of
the two players that reach it, so with negations only at the leaves. The monotone counterparts
are `Formula.monotoneKWProtocol` and `Protocol.monotoneKWFormula`.

The round protocols of Korten's top-down lower bounds give Alice the input where `f` is false
instead (`Communication.RoundProtocol.SolvesKW`); exchanging the players translates
(`Communication.RoundProtocol.solvesKW_swapPlayers_ofProtocol`).

## Main definitions

* `Cslib.Circuits.Formula.kwProtocol`: the protocol of a formula.
* `Cslib.Communication.Protocol.kwFormula`: the formula of a protocol.

## Main results

* `Cslib.Circuits.Boolean.formulaDepth_eq_ecomplexity`: the Karchmer–Wigderson theorem.

## References

* [M. Karchmer and A. Wigderson, *Monotone circuits for connectivity require super-logarithmic
  depth*][KarchmerWigderson1990]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Circuits

open Boolean Cslib.Communication

variable {n : ℕ}

/-- The protocol of a De Morgan formula for the Karchmer–Wigderson game, when the formula is
`onAlice` on Alice's input: the player holding the input where an AND gate is false, or where an
OR gate is true, says which argument witnesses it. Constant subformulas, which never separate the
two inputs, output the bit `0`. -/
def Formula.kwProtocol [NeZero n] : Formula signature n → Bool → KWProtocol (Fin n)
  | .input i, _ => .output i
  | .gate op args, onAlice =>
    match op, args with
    | .const _, _ => .output 0
    | .not, args => (args 0).kwProtocol !onAlice
    | .and, args =>
      cond onAlice
        (.bob (fun y => (args 0).eval interpretation y) ((args 0).kwProtocol onAlice)
          ((args 1).kwProtocol onAlice))
        (.alice (fun x => (args 0).eval interpretation x) ((args 0).kwProtocol onAlice)
          ((args 1).kwProtocol onAlice))
    | .or, args =>
      cond onAlice
        (.alice (fun x => (args 0).eval interpretation x) ((args 1).kwProtocol onAlice)
          ((args 0).kwProtocol onAlice))
        (.bob (fun y => (args 0).eval interpretation y) ((args 1).kwProtocol onAlice)
          ((args 0).kwProtocol onAlice))

namespace Formula

/-- The protocol of a formula finds a bit where Alice's and Bob's inputs differ, when the formula
is `onAlice` on Alice's input and `!onAlice` on Bob's. -/
private theorem differsAt_run_kwProtocol [NeZero n] (F : Formula signature n) (onAlice : Bool)
    {x y : BitString n} (hx : F.eval interpretation x = onAlice)
    (hy : F.eval interpretation y = !onAlice) :
    DiffersAt x y ((F.kwProtocol onAlice).run x y) := by
  induction F generalizing onAlice with
  | input i =>
    simp only [eval_input] at hx hy
    simp [kwProtocol, DiffersAt, hx, hy]
  | gate op args ih =>
    cases op with
    | const c =>
      simp only [eval_gate, interpretation] at hx hy
      cases onAlice <;> simp_all
    | not =>
      exact ih 0 (!onAlice) (by simpa [interpretation] using hx)
        (by simpa [interpretation] using hy)
    | and =>
      simp only [eval_gate, interpretation] at hx hy
      cases onAlice
      · simp only [Bool.and_eq_false_iff, Bool.not_false, Bool.and_eq_true] at hx hy
        cases h : (args 0).eval interpretation x
        · simpa [kwProtocol, h] using ih 0 false h hy.1
        · simpa [kwProtocol, h] using ih 1 false (hx.resolve_left (by simp [h])) hy.2
      · simp only [Bool.and_eq_true, Bool.not_true, Bool.and_eq_false_iff] at hx hy
        cases h : (args 0).eval interpretation y
        · simpa [kwProtocol, h] using ih 0 true hx.1 h
        · simpa [kwProtocol, h] using ih 1 true hx.2 (hy.resolve_left (by simp [h]))
    | or =>
      simp only [eval_gate, interpretation] at hx hy
      cases onAlice
      · simp only [Bool.or_eq_false_iff, Bool.not_false, Bool.or_eq_true] at hx hy
        cases h : (args 0).eval interpretation y
        · simpa [kwProtocol, h] using ih 1 false hx.2 (hy.resolve_left (by simp [h]))
        · simpa [kwProtocol, h] using ih 0 false hx.1 h
      · simp only [Bool.or_eq_true, Bool.not_true, Bool.or_eq_false_iff] at hx hy
        cases h : (args 0).eval interpretation x
        · simpa [kwProtocol, h] using ih 1 true (hx.resolve_left (by simp [h])) hy.2
        · simpa [kwProtocol, h] using ih 0 true h hy.1

/-- The protocol of a formula sends at most as many bits as the formula has AND and OR gates on a
path. -/
theorem depth_kwProtocol_le [NeZero n] (F : Formula signature n) (onAlice : Bool) :
    (F.kwProtocol onAlice).depth ≤ F.depthWith binaryCost := by
  induction F generalizing onAlice with
  | input i => simp [kwProtocol]
  | gate op args ih =>
    have hle (j : Fin (signature.Arity op)) :
        (args j).depthWith binaryCost ≤ Finset.univ.sup fun j => (args j).depthWith binaryCost :=
      Finset.le_sup (f := fun j => (args j).depthWith binaryCost) (Finset.mem_univ j)
    cases op with
    | const c => simp [kwProtocol]
    | not => exact (ih 0 _).trans ((hle 0).trans (by simp))
    | and =>
      have h₀ := (ih 0 onAlice).trans (hle 0)
      have h₁ := (ih 1 onAlice).trans (hle 1)
      cases onAlice <;> simp only [kwProtocol, Bool.cond_false, Bool.cond_true,
        Protocol.depth_alice, Protocol.depth_bob, depthWith_gate, binaryCost_and] <;>
        exact Nat.add_le_add_right (max_le h₀ h₁) 1
    | or =>
      have h₀ := (ih 0 onAlice).trans (hle 0)
      have h₁ := (ih 1 onAlice).trans (hle 1)
      cases onAlice <;> simp only [kwProtocol, Bool.cond_false, Bool.cond_true,
        Protocol.depth_alice, Protocol.depth_bob, depthWith_gate, binaryCost_or] <;>
        exact Nat.add_le_add_right (max_le h₁ h₀) 1

end Formula

end Cslib.Circuits

namespace Cslib.Communication.Protocol

open Cslib.Circuits Cslib.Circuits.Boolean

variable {n : ℕ}

open Classical in
/-- The formula of a protocol for the Karchmer–Wigderson game on `A × B`: an OR at each of Alice's
nodes, an AND at each of Bob's, and at each leaf a literal true on the inputs of `A` and false on
those of `B` that reach it, or a constant if one side is empty. -/
noncomputable def kwFormula : KWProtocol (Fin n) → Set (BitString n) → Set (BitString n) →
    Formula signature n
  | .output i, A, B =>
    if A = ∅ then .const false
    else if B = ∅ then .const true
    else if ∃ x ∈ A, x i = true then .input i else (Formula.input i).not
  | .alice send p₀ p₁, A, B =>
    (p₀.kwFormula {x ∈ A | send x = false} B).or (p₁.kwFormula {x ∈ A | send x = true} B)
  | .bob send p₀ p₁, A, B =>
    (p₀.kwFormula A {y ∈ B | send y = false}).and (p₁.kwFormula A {y ∈ B | send y = true})

/-- The formula of a protocol solving the Karchmer–Wigderson game on `A × B` is true on `A` and
false on `B`. -/
private theorem eval_kwFormula (p : KWProtocol (Fin n))
    {A B : Set (BitString n)} (hp : p.Solves DiffersAt A B) :
    (∀ x ∈ A, (p.kwFormula A B).eval interpretation x = true) ∧
      ∀ y ∈ B, (p.kwFormula A B).eval interpretation y = false := by
  induction p generalizing A B with
  | output i =>
    simp only [Solves, Communication.Solves, run_output, DiffersAt] at hp
    by_cases hA : A = ∅
    · simp [kwFormula, hA]
    by_cases hB : B = ∅
    · simp [kwFormula, hA, hB]
    obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hA
    obtain ⟨y₀, hy₀⟩ := Set.nonempty_iff_ne_empty.2 hB
    by_cases h : ∃ x ∈ A, x i = true
    · obtain ⟨x₁, hx₁, hx₁i⟩ := h
      have hy₀i : y₀ i = false := by simpa [hx₁i] using (hp x₁ hx₁ y₀ hy₀).symm
      simp only [kwFormula, hA, hB, ↓reduceIte, show ∃ x ∈ A, x i = true from ⟨x₁, hx₁, hx₁i⟩,
        Formula.eval_input]
      exact ⟨fun x hx => by simpa [hy₀i] using hp x hx y₀ hy₀,
        fun y hy => by simpa [hx₁i] using (hp x₁ hx₁ y hy).symm⟩
    · push Not at h
      simp only [kwFormula, hA, hB, ↓reduceIte, show ¬∃ x ∈ A, x i = true from by simpa using h,
        Formula.eval_not, Formula.eval_input]
      exact ⟨fun x hx => by simp [h x hx],
        fun y hy => by simpa [h x₀ hx₀] using (hp x₀ hx₀ y hy).symm⟩
  | alice send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀ (A := {x ∈ A | send x = false}) (B := B) fun x hx y hy => by
      simpa [hx.2] using hp x hx.1 y hy
    have h₁ := ih₁ (A := {x ∈ A | send x = true}) (B := B) fun x hx y hy => by
      simpa [hx.2] using hp x hx.1 y hy
    refine ⟨fun x hx => ?_, fun y hy => by simp [kwFormula, h₀.2 y hy, h₁.2 y hy]⟩
    cases h : send x
    · simp [kwFormula, h₀.1 x ⟨hx, h⟩]
    · simp [kwFormula, h₁.1 x ⟨hx, h⟩]
  | bob send p₀ p₁ ih₀ ih₁ =>
    have h₀ := ih₀ (A := A) (B := {y ∈ B | send y = false}) fun x hx y hy => by
      simpa [hy.2] using hp x hx y hy.1
    have h₁ := ih₁ (A := A) (B := {y ∈ B | send y = true}) fun x hx y hy => by
      simpa [hy.2] using hp x hx y hy.1
    refine ⟨fun x hx => by simp [kwFormula, h₀.1 x hx, h₁.1 x hx], fun y hy => ?_⟩
    cases h : send y
    · simp [kwFormula, h₀.2 y ⟨hy, h⟩]
    · simp [kwFormula, h₁.2 y ⟨hy, h⟩]

/-- The formula of a protocol has as many AND and OR gates on a path as the protocol sends
bits. -/
theorem depthWith_kwFormula_le (p : KWProtocol (Fin n))
    (A B : Set (BitString n)) : (p.kwFormula A B).depthWith binaryCost ≤ p.depth := by
  induction p generalizing A B with
  | output i =>
    simp only [kwFormula]
    split_ifs <;> simp
  | alice send p₀ p₁ ih₀ ih₁ =>
    rw [kwFormula, Formula.depthWith_or, binaryCost_or, depth_alice]
    exact Nat.add_le_add_right (max_le_max (ih₀ _ _) (ih₁ _ _)) 1
  | bob send p₀ p₁ ih₀ ih₁ =>
    rw [kwFormula, Formula.depthWith_and, binaryCost_and, depth_bob]
    exact Nat.add_le_add_right (max_le_max (ih₀ _ _) (ih₁ _ _)) 1

/-- The formula of a protocol solving the Karchmer–Wigderson game on `A × B` is true on `A`. -/
theorem eval_kwFormula_of_mem_left {p : KWProtocol (Fin n)} {A B : Set (BitString n)}
    (hp : p.Solves DiffersAt A B) {x : BitString n} (hx : x ∈ A) :
    (p.kwFormula A B).eval interpretation x = true :=
  (p.eval_kwFormula hp).1 x hx

/-- The formula of a protocol solving the Karchmer–Wigderson game on `A × B` is false on `B`. -/
theorem eval_kwFormula_of_mem_right {p : KWProtocol (Fin n)} {A B : Set (BitString n)}
    (hp : p.Solves DiffersAt A B) {y : BitString n} (hy : y ∈ B) :
    (p.kwFormula A B).eval interpretation y = false :=
  (p.eval_kwFormula hp).2 y hy

end Cslib.Communication.Protocol

namespace Cslib.Circuits.Boolean

open Cslib.Communication

variable {n : ℕ}

/-- A formula computing `f` gives a protocol for its Karchmer–Wigderson game, with at most as
many bits as the formula has AND and OR gates on a path. -/
theorem exists_kwProtocol_of_computes [NeZero n] {f : BooleanFunction n}
    {F : Formula signature n} (hF : F.Computes interpretation f) :
    ∃ p : KWProtocol (Fin n), p.Solves DiffersAt {x | f x = true} {y | f y = false} ∧
      p.depth ≤ F.depthWith binaryCost :=
  ⟨F.kwProtocol true, fun x hx y hy => F.differsAt_run_kwProtocol true ((hF x).trans hx)
    ((hF y).trans hy), F.depth_kwProtocol_le true⟩

/-- A protocol for the Karchmer–Wigderson game of `f` gives a formula computing `f`, with at most
as many AND and OR gates on a path as the protocol sends bits. -/
private theorem exists_formula_of_solves {f : BooleanFunction n} {p : KWProtocol (Fin n)}
    (hp : p.Solves DiffersAt {x | f x = true} {y | f y = false}) :
    ∃ F : Formula signature n, F.Computes interpretation f ∧ F.depthWith binaryCost ≤ p.depth := by
  refine ⟨p.kwFormula {x | f x = true} {y | f y = false}, fun x => ?_,
    p.depthWith_kwFormula_le _ _⟩
  cases h : f x
  · exact Protocol.eval_kwFormula_of_mem_right hp h
  · exact Protocol.eval_kwFormula_of_mem_left hp h

/-- **The Karchmer–Wigderson theorem.** The least depth of a De Morgan formula for a function of at
least one bit, with negations free, is the communication complexity of its Karchmer–Wigderson
game. -/
theorem formulaDepth_eq_ecomplexity [NeZero n] (f : BooleanFunction n) :
    (formulaDepth f : ℕ∞) =
      Protocol.ecomplexity DiffersAt {x | f x = true} {y | f y = false} := by
  refine le_antisymm (Protocol.le_ecomplexity_iff.2 fun p hp => ?_) ?_
  · obtain ⟨F, hF, hd⟩ := exists_formula_of_solves hp
    exact_mod_cast (formulaDepth_le hF).trans hd
  · obtain ⟨F, hF, hd⟩ := exists_computes_depthWith_eq_formulaDepth f
    obtain ⟨p, hp, hpd⟩ := exists_kwProtocol_of_computes hF
    exact (Protocol.ecomplexity_le_depth hp).trans (by exact_mod_cast hpd.trans hd.le)

end Cslib.Circuits.Boolean
