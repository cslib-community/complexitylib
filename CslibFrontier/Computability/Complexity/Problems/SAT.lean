/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Logics.Propositional.CNF

/-!
# The satisfiability problem

`SAT` is the set of satisfiable formulas in conjunctive normal form over variables numbered by `ℕ`,
encoded as lists of lists of literals with the framed encodings of lists and pairs
(`Cslib.Complexity.encCNF`). `UNSAT` is the set of unsatisfiable ones. Instances are formulas, not
words, so `UNSAT` is exactly the complement of `SAT`; there are no ill-formed encodings to assign
to either side.

The Cook–Levin theorem says that `SAT` is `NP`-complete [Arora and Barak, Theorem
2.10][AroraBarak09]. The verifier's correctness is proved here (`SAT.isVerifier`, through
`Cslib.Complexity.IsVerifier.of_padding`, which handles the certificate length), its
polynomial-time bound and `SAT ∈ NP` are proved in
`CslibFrontier/Computability/Complexity/Problems/SAT/PolyTime.lean`, and the tableau
reduction and `NP`-completeness are proved in `CookLevin/`.

## Main definitions

* `Cslib.Complexity.SAT`, `Cslib.Complexity.UNSAT`, `Cslib.Complexity.encCNF`.
* `Cslib.Complexity.SAT.verifier`: evaluation of a formula under the assignment a certificate
  describes.

## Main results

* `Cslib.Complexity.SAT.assignment_vars_map_append`: the values of an assignment listed along the
  occurrences of a formula, followed by any padding, form a certificate describing it.
* `Cslib.Complexity.SAT.isVerifier`: the verifier is correct, with certificates as long as the
  encoded formula.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The satisfiable CNF formulas over variables numbered by natural numbers [Karp1972],
[Arora and Barak, Section 2.3][AroraBarak09]. -/
def SAT : Set (CNF ℕ) := {φ | φ.Satisfiable}

theorem mem_SAT {φ : CNF ℕ} : φ ∈ SAT ↔ φ.Satisfiable := Iff.rfl

/-- The unsatisfiable CNF formulas over variables numbered by natural numbers. -/
def UNSAT : Set (CNF ℕ) := {φ | ¬φ.Satisfiable}

theorem mem_UNSAT {φ : CNF ℕ} : φ ∈ UNSAT ↔ ¬φ.Satisfiable := Iff.rfl

theorem compl_SAT : SATᶜ = UNSAT := rfl

/-- Formulas encoded as lists of clauses, clauses as lists of literals, and a literal `(v, b)` as
the framed binary digits of `v` followed by `b`. -/
def encCNF : CNF ℕ ↪ List Bool := encList (encList (encPair encNat encBool))

namespace SAT

/-! ### The verifier -/

/-- The assignment described by a certificate `w` for `φ`: each variable takes the bit of `w` at
the position of its first occurrence in `φ`. Variables are numbered arbitrarily, so a certificate
cannot simply list the values of variables `0, 1, 2, …`; it lists them in order of occurrence
instead, which needs at most as many bits as `φ` has literals. -/
def assignment (φ : CNF ℕ) (w : List Bool) (v : ℕ) : Bool := w.getD (φ.vars.idxOf v) false

/-- The values of `σ` listed along the occurrences of `φ`, followed by any bits, form a
certificate describing `σ` on the variables of `φ`. -/
theorem assignment_vars_map_append (φ : CNF ℕ) (σ : ℕ → Bool) (w : List Bool) {v : ℕ}
    (hv : v ∈ φ.vars) : assignment φ (φ.vars.map σ ++ w) v = σ v := by
  simp [assignment, List.getD_eq_getElem?_getD, List.getElem?_append_left,
    List.idxOf_lt_length_iff.2 hv]

/-- The values of `σ` listed along the occurrences of `φ` form a certificate describing `σ` on
the variables of `φ`. -/
theorem assignment_vars_map (φ : CNF ℕ) (σ : ℕ → Bool) {v : ℕ} (hv : v ∈ φ.vars) :
    assignment φ (φ.vars.map σ) v = σ v :=
  List.append_nil (φ.vars.map σ) ▸ assignment_vars_map_append φ σ [] hv

/-- The verifier for `SAT`: evaluate the formula under the assignment the certificate describes. -/
def verifier (x : CNF ℕ × List Bool) : Bool := x.1.eval (assignment x.1 x.2)

/-- A formula has no more literals than the length of its encoding. -/
theorem length_vars_le (φ : CNF ℕ) : φ.vars.length ≤ (encCNF φ).length := by
  rw [CNF.length_vars]
  calc (φ.map List.length).sum
      ≤ (φ.map fun c => (encList (encPair encNat encBool) c).length).sum :=
        List.sum_le_sum fun c _ => length_le_length_encList _ c
    _ ≤ (encCNF φ).length := sum_length_le_length_encList _ φ

/-- `SAT.verifier` verifies `SAT` with certificates as long as the encoded formula: a satisfying
assignment, listed in order of first occurrence, is a prefix the verifier accepts whatever padding
follows it. -/
theorem isVerifier : IsVerifier encCNF Polynomial.X verifier SAT := by
  refine IsVerifier.of_padding (fun φ w _ h => ⟨_, h⟩) fun φ ⟨τ, hτ⟩ => ?_
  exact ⟨φ.vars.map τ, by simpa using length_vars_le φ, fun k =>
    (CNF.eval_congr fun _ hv => assignment_vars_map_append φ τ _ hv).trans hτ⟩

end SAT

end Cslib.Complexity
