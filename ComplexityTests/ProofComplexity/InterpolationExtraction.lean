/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.Interpolation.PolyTime
import Complexity.Computability.Circuit.Boolean.EvaluationTime

/-!
# Tests: extracting interpolants from resolution refutations

The split formula of `ComplexityTests.ProofComplexity.Interpolation`, with natural-number shared
variables: `A(x, y) = y ∧ (y → x)` and `B(x, z) = z ∧ (z → ¬x)`, refuted in seven lines. The only
interpolant is `x`. The extracted code is checked by `decide`: it has `28` gates, decodes to a
circuit with one input, and the circuit computes `x`. The correctness theorem then applies.

With the polarities swapped, the only interpolant is `¬x`, and the extracted circuit computes it.
A list without an empty line gives a code that does not decode, and a line without justification
gets the constant `false`. Finally, extracting the interpolant of a refutation and evaluating it on
an input is computable in polynomial time.

The monotone builder is checked on the same refutations. In the first formula `x` occurs only
positively in `A`, so Pudlák's gate `(x ∨ c₁) ∧ c₂` is used; the code has `14` gates and computes
`x`, and the correctness theorem applies. Adding to `A` a clause with `¬x₁` breaks that polarity
while `x₀` still occurs only negatively in `B`, so the dual gate `(x₀ ∧ c₂) ∨ c₁` is used; the code
computes `x₀`. In the swapped formula neither polarity holds: the code still has `14` gates and
decodes, but it computes the constant `true`, which is not an interpolant, since the only one is
`¬x`.
-/

namespace ComplexityTests.ProofComplexity.InterpolationExtraction

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Logic.PL Turing.MultiTapeTM

/-- `A(x, y) = y ∧ (¬y ∨ x)`, which forces `x`. -/
private def A : CNF (ℕ ⊕ Unit) := [[(.inr (), true)], [(.inr (), false), (.inl 0, true)]]

/-- `B(x, z) = z ∧ (¬z ∨ ¬x)`, which forces `¬x`. -/
private def B : CNF (ℕ ⊕ Unit) := [[(.inr (), true)], [(.inr (), false), (.inl 0, false)]]

private abbrev x : ℕ ⊕ (Unit ⊕ Unit) := .inl 0
private abbrev y : ℕ ⊕ (Unit ⊕ Unit) := .inr (.inl ())
private abbrev z : ℕ ⊕ (Unit ⊕ Unit) := .inr (.inr ())

/-- The seven lines, from the last to the first: resolve on `y` to `x`, on `z` to `¬x`, and on `x`
to the empty clause. -/
private def lines : List (Clause (ℕ ⊕ (Unit ⊕ Unit))) :=
  [[], [(x, false)], [(x, true)], [(z, false), (x, false)], [(z, true)],
    [(y, false), (x, true)], [(y, true)]]

private theorem isProof : (A.appendShared B).IsProof lines := by
  have h₄ : (A.appendShared B).IsProof
      [[(z, false), (x, false)], [(z, true)], [(y, false), (x, true)], [(y, true)]] :=
    (((CNF.IsProof.nil.mem (by decide)).mem (by decide)).mem (by decide)).mem (by decide)
  have h₅ := h₄.resolvent (c₁ := [(y, true)]) (c₂ := [(y, false), (x, true)]) y (by decide)
    (by decide) (by decide) (by decide)
  have h₆ := h₅.resolvent (c₁ := [(z, true)]) (c₂ := [(z, false), (x, false)]) z (by decide)
    (by decide) (by decide) (by decide)
  exact h₆.resolvent (c₁ := [(x, true)]) (c₂ := [(x, false)]) x (by decide) (by decide)
    (by decide) (by decide)

/-- The extracted code: four gates per line. The clauses of `A` get `false`, those of `B` get
`true`, the resolutions on `y` and `z` a disjunction and a conjunction, and the last line the
selector on `x`. The output is the wire of the last line. -/
example : CNF.interpolantCode 1 A B lines =
    ([(.const false, []), (.const false, []), (.const false, []), (.const false, []),
      (.const false, []), (.const false, []), (.const false, []), (.const false, []),
      (.const true, []), (.const true, []), (.const true, []), (.const true, []),
      (.const true, []), (.const true, []), (.const true, []), (.const true, []),
      (.const false, []), (.const false, []), (.const false, []), (.or, [4, 8]),
      (.const false, []), (.const false, []), (.const false, []), (.and, [12, 16]),
      (.not, [0]), (.and, [25, 20]), (.and, [0, 24]), (.or, [26, 27])],
     [28]) := by
  decide

/-- The code decodes to a circuit with one input and one output. -/
example : (Circuit.ofCode 1 1 (CNF.interpolantCode 1 A B lines) :
    Option (Circuit signature 1 1)).isSome := by
  decide

/-- Evaluating the code at its output wire gives `x`. -/
example : ∀ b : Bool, evalOutput [b] (CNF.interpolantCode 1 A B lines).1 28 = b := by
  decide

/-- The correctness theorem applies: the decoded circuit has `28` gates and computes an
interpolant, which is `x`, since assignments with `x` extend to models of `A` and those with
`¬x` to models of `B`. -/
example : ∃ C : Circuit signature 1 1,
    Circuit.ofCode 1 1 (CNF.interpolantCode 1 A B lines) = some C ∧
      C.size = 28 ∧ ∀ a, C.eval interpretation a 0 = a 0 := by
  obtain ⟨C, hC, hsize, hint⟩ := isProof.ofCode_interpolantCode (n := 1) (by decide)
    (by simp [A]) (by simp [B])
  refine ⟨C, hC, hsize, fun a => ?_⟩
  have key (b : Bool) : C.eval interpretation (fun _ => b) 0 = b := by
    cases b
    · exact hint.2 (fun _ => false) (fun _ => true) (by decide)
    · exact hint.1 (fun _ => true) (fun _ => true) (by decide)
  have ha : a = fun _ => a 0 := funext fun i => by rw [Subsingleton.elim i 0]
  rw [ha]
  exact key (a 0)

/-! ### Swapped polarities -/

/-- `A'(x, y) = y ∧ (¬y ∨ ¬x)`, which forces `¬x`. -/
private def A' : CNF (ℕ ⊕ Unit) := [[(.inr (), true)], [(.inr (), false), (.inl 0, false)]]

/-- `B'(x, z) = z ∧ (¬z ∨ x)`, which forces `x`. -/
private def B' : CNF (ℕ ⊕ Unit) := [[(.inr (), true)], [(.inr (), false), (.inl 0, true)]]

/-- The refutation of the swapped formula, from the last line to the first: resolve on `z` to `x`,
on `y` to `¬x`, and on `x` to the empty clause. -/
private def lines' : List (Clause (ℕ ⊕ (Unit ⊕ Unit))) :=
  [[], [(x, false)], [(x, true)], [(y, false), (x, false)], [(y, true)],
    [(z, false), (x, true)], [(z, true)]]

/-- The extracted circuit computes `¬x`. -/
example : ∀ b : Bool, evalOutput [b] (CNF.interpolantCode 1 A' B' lines').1 28 = !b := by
  decide

/-! ### Invalid input -/

/-- Without an empty line the output wire is past the last gate, and the code does not decode. -/
example : (Circuit.ofCode 1 1 (CNF.interpolantCode 1 A B lines.tail) :
    Option (Circuit signature 1 1)) = none := by
  decide

/-- A line with no justification gets the constant `false`; the code still has four gates per
line and decodes. -/
example : CNF.interpolantCode 1 A B [[]] =
    ([(.const false, []), (.const false, []), (.const false, []), (.const false, [])], [4]) := by
  decide
/-! ### Polynomial time -/

/-- Extracting the interpolant circuit of a refutation and evaluating it on an input is
polynomial-time, with natural-number private variables in binary. -/
example : ComputableInPolyTime
    (fun p : (ℕ × (CNF (ℕ ⊕ ℕ) × CNF (ℕ ⊕ ℕ)) × List (Clause (ℕ ⊕ (ℕ ⊕ ℕ)))) × List Bool =>
      evalOutput p.2 (CNF.interpolantCode p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2).1
        ((CNF.interpolantCode p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2).2.headD 0))
    (encPair (encPair encUnary (encPair (encPair
      (encList (encList (encPair (encSum encNat encNat) encBool)))
      (encList (encList (encPair (encSum encNat encNat) encBool))))
      (encList (encList (encPair (encSum encNat (encSum encNat encNat)) encBool))))) encBits)
    encBool := by
  have h := (CNF.computableInPolyTime_interpolantCode encNat encNat).comp
    (ComputableInPolyTime.fst _ encBits)
  exact computableInPolyTime_evalOutput (ComputableInPolyTime.snd _ _) h.fst'
    ((ComputableInPolyTime.headD 0).comp h.snd')

/-! ### The monotone interpolant -/

/-- The value of wire `w` of a monotone code on the input `x`. -/
private def monotoneValue (x : List Bool) (code : List (Monotone.Op × List ℕ) × List ℕ) (w : ℕ) :
    Bool :=
  (evalCode Monotone.interpretation false x code.1).getD w false

/-- The shared variable occurs only positively in `A`. -/
example : MonotoneInterpolant.positive A = true := by
  decide

/-- The extracted monotone code: two gates per line. The resolutions on `y` and `z` get a
disjunction and a conjunction, and the last line Pudlák's gate `(x ∨ c₁) ∧ c₂`. -/
example : CNF.monotoneInterpolantCode 1 A B lines =
    ([(.const false, []), (.const false, []), (.const false, []), (.const false, []),
      (.const true, []), (.const true, []), (.const true, []), (.const true, []),
      (.const false, []), (.or, [2, 4]), (.const false, []), (.and, [6, 8]),
      (.or, [0, 10]), (.and, [13, 12])],
     [14]) := by
  decide

/-- The monotone code decodes, and evaluating it at its output wire gives `x`. -/
example : (Circuit.ofCode 1 1 (CNF.monotoneInterpolantCode 1 A B lines) :
    Option (Circuit Monotone.signature 1 1)).isSome ∧
      ∀ b : Bool, monotoneValue [b] (CNF.monotoneInterpolantCode 1 A B lines) 14 = b := by
  decide

/-- The correctness theorem applies: the decoded monotone circuit has `14` gates and computes `x`.
-/
example : ∃ C : Circuit Monotone.signature 1 1,
    Circuit.ofCode 1 1 (CNF.monotoneInterpolantCode 1 A B lines) = some C ∧
      C.size = 14 ∧ ∀ a, C.eval Monotone.interpretation a 0 = a 0 := by
  obtain ⟨C, hC, hsize, hint⟩ := isProof.ofCode_monotoneInterpolantCode (n := 1) (by decide)
    (by simp [A]) (by simp [B]) (Or.inl (MonotoneInterpolant.positive_eq_true_iff.1 (by decide)))
  refine ⟨C, hC, hsize, fun a => ?_⟩
  have key (b : Bool) : C.eval Monotone.interpretation (fun _ => b) 0 = b := by
    cases b
    · exact hint.2 (fun _ => false) (fun _ => true) (by decide)
    · exact hint.1 (fun _ => true) (fun _ => true) (by decide)
  have ha : a = fun _ => a 0 := funext fun i => by rw [Subsingleton.elim i 0]
  rw [ha]
  exact key (a 0)

/-- `A` with the extra clause `¬x₁ ∨ y`, so that the shared variables no longer occur only
positively in it. -/
private def A₂ : CNF (ℕ ⊕ Unit) := A ++ [[(.inl 1, false), (.inr (), true)]]

private theorem isProof₂ : (A₂.appendShared B).IsProof lines := by
  have h₄ : (A₂.appendShared B).IsProof
      [[(z, false), (x, false)], [(z, true)], [(y, false), (x, true)], [(y, true)]] :=
    (((CNF.IsProof.nil.mem (by decide)).mem (by decide)).mem (by decide)).mem (by decide)
  have h₅ := h₄.resolvent (c₁ := [(y, true)]) (c₂ := [(y, false), (x, true)]) y (by decide)
    (by decide) (by decide) (by decide)
  have h₆ := h₅.resolvent (c₁ := [(z, true)]) (c₂ := [(z, false), (x, false)]) z (by decide)
    (by decide) (by decide) (by decide)
  exact h₆.resolvent (c₁ := [(x, true)]) (c₂ := [(x, false)]) x (by decide) (by decide)
    (by decide) (by decide)

/-- With two inputs and `A₂`, the last line gets the dual gate `(x₀ ∧ c₂) ∨ c₁`, and the code
computes `x₀`. -/
example : MonotoneInterpolant.positive A₂ = false ∧
    (CNF.monotoneInterpolantCode 2 A₂ B lines).1.drop 12 =
      [(.and, [0, 13]), (.or, [14, 11])] ∧
    ∀ b c : Bool, monotoneValue [b, c] (CNF.monotoneInterpolantCode 2 A₂ B lines) 15 = b := by
  decide

/-- The correctness theorem applies through the negative polarity of `B`. -/
example : ∃ C : Circuit Monotone.signature 2 1,
    Circuit.ofCode 2 1 (CNF.monotoneInterpolantCode 2 A₂ B lines) = some C ∧ C.size = 14 :=
  let ⟨C, hC, hsize, _⟩ := isProof₂.ofCode_monotoneInterpolantCode (n := 2) (by decide)
    (by simp [A₂, A]) (by simp [B]) (Or.inr (by simp [B]))
  ⟨C, hC, hsize⟩

/-- In the swapped formula neither polarity holds. The code still has `14` gates and decodes, but
it computes the constant `true`, which is not an interpolant: the only one is `¬x`. -/
example : (Circuit.ofCode 1 1 (CNF.monotoneInterpolantCode 1 A' B' lines') :
    Option (Circuit Monotone.signature 1 1)).isSome ∧
      ∀ b : Bool, monotoneValue [b] (CNF.monotoneInterpolantCode 1 A' B' lines') 14 = true := by
  decide

/-- Without an empty line the monotone code does not decode, and a line with no justification
gets the constant `false`. -/
example : (Circuit.ofCode 1 1 (CNF.monotoneInterpolantCode 1 A B lines.tail) :
      Option (Circuit Monotone.signature 1 1)) = none ∧
    CNF.monotoneInterpolantCode 1 A B [[]] = ([(.const false, []), (.const false, [])], [2]) := by
  decide

/-- Extracting the monotone interpolant circuit of a refutation is polynomial-time, with
natural-number private variables in binary. -/
example : ComputableInPolyTime
    (fun ((n, (A, B), ls) : ℕ × (CNF (ℕ ⊕ ℕ) × CNF (ℕ ⊕ ℕ)) × List (Clause (ℕ ⊕ (ℕ ⊕ ℕ)))) =>
      CNF.monotoneInterpolantCode n A B ls)
    (encPair encUnary (encPair (encPair
      (encList (encList (encPair (encSum encNat encNat) encBool)))
      (encList (encList (encPair (encSum encNat encNat) encBool))))
      (encList (encList (encPair (encSum encNat (encSum encNat encNat)) encBool)))))
    Monotone.encCode :=
  CNF.computableInPolyTime_monotoneInterpolantCode encNat encNat

end ComplexityTests.ProofComplexity.InterpolationExtraction
