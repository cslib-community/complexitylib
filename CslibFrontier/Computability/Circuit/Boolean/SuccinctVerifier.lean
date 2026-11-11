/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.Boolean.Synthesis
public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Computability.Complexity.Problems.CircuitSAT
public import CslibFrontier.Foundations.Data.BitString.Enumeration
import Mathlib.Data.Bool.Basic

/-!
# Verifying a succinct satisfying assignment by circuit unsatisfiability

A circuit `D` on `q` inputs describes `2 ^ q` clauses of three literals on `2 ^ r` variables.
Its outputs are three consecutive blocks of `r + 1` bits: the address of a variable, followed
by its sign. `toCNF D` expands those clauses into the existing `CNF` representation, with
variables of type `BitString r`. Every address has a clause, so padding addresses must describe
tautologies rather than be ignored. Repeated variables and clauses are allowed.

Given a circuit `W` on `r` inputs, `badClause D W` computes whether the clause addressed by its
input is false under the assignment `fun y => W.eval interpretation y 0`. The decoder is used
once and the witness circuit three times. The result has exactly the original `q` input bits
and `D.size + 3 * W.size + 17` De Morgan gates, constants included. It is unsatisfiable exactly
when the truth table of `W` satisfies the expanded CNF.

This is the witness-verification step in the proof of [Williams2010, Theorem 3.2, p. 10 of the
author's May 4, 2010 version]. The source uses a negation bit; here a sign is the value required
by a literal, as in `Literal.eval`. The exact seventeen-gate overhead is a library variant of
the source's asymptotic bound. This module proves an actual circuit construction and its
semantics and gate count.
It does not assert the easy-witness lemma, efficient construction of a tableau decoder, a
machine running time, or the resulting separation of complexity classes.

## Main definitions

* `Cslib.Circuits.Boolean.SuccinctVerifier.addressWire`,
  `Cslib.Circuits.Boolean.SuccinctVerifier.signWire`: the layout of a decoded literal.
* `Cslib.Circuits.Boolean.SuccinctVerifier.clause`,
  `Cslib.Circuits.Boolean.SuccinctVerifier.toCNF`: the represented clauses and formula.
* `Cslib.Circuits.Boolean.SuccinctVerifier.violationTest`: the fixed three-literal test.
* `Cslib.Circuits.Boolean.SuccinctVerifier.badClause`: the circuit finding a violated clause.

## Main results

* `Cslib.Circuits.Boolean.SuccinctVerifier.size_badClause`: the exact gate count.
* `Cslib.Circuits.Boolean.SuccinctVerifier.eval_badClause`: correctness on each clause address.
* `Cslib.Circuits.Boolean.SuccinctVerifier.not_mem_CircuitSAT_badClause_iff`: correctness of
  verification by circuit unsatisfiability.
* `Cslib.Circuits.Boolean.SuccinctVerifier.exists_small_witness_iff`: the size-bounded
  correspondence between satisfying assignments and accepted witness circuits.

## References

* [R. Williams, *Improving exhaustive search implies superpolynomial lower bounds*][Williams2010]
-/

public section

namespace Cslib.Circuits.Boolean.SuccinctVerifier

open Cslib.Logic.PL

variable {q r : ℕ}

/-- Bit `i` of literal `j`'s variable address in the interleaved address/sign layout. -/
@[expose] def addressWire (r : ℕ) (j : Fin 3) (i : Fin r) : Fin (3 * (r + 1)) :=
  ⟨j * (r + 1) + i, by
    have := Nat.mul_le_mul_right (r + 1) j.isLt
    rw [Nat.succ_mul] at this
    omega⟩

/-- Literal `j`'s sign, immediately following its `r` address bits. -/
@[expose] def signWire (r : ℕ) (j : Fin 3) : Fin (3 * (r + 1)) :=
  ⟨j * (r + 1) + r, by
    have := Nat.mul_le_mul_right (r + 1) j.isLt
    rw [Nat.succ_mul] at this
    omega⟩

/-- The clause at address `x`: three variable addresses and their required truth values. -/
@[expose] def clause (D : Circuit signature q (3 * (r + 1))) (x : BitString q) :
    Clause (BitString r) :=
  List.ofFn fun j : Fin 3 =>
    (fun i => D.eval interpretation x (addressWire r j i),
      D.eval interpretation x (signWire r j))

/-- Expand every `q`-bit clause address, in binary order. This expansion has exponential length;
the verification circuit below does not construct it. -/
@[expose] def toCNF (D : Circuit signature q (3 * (r + 1))) : CNF (BitString r) :=
  (BitString.enum q).map (clause D)

/-- Every represented clause has three literals, including repetitions. -/
@[simp] theorem length_clause (D : Circuit signature q (3 * (r + 1))) (x : BitString q) :
    (clause D x).length = 3 := by
  simp [clause]

/-- The formula contains exactly one clause per input to its decoder. -/
@[simp] theorem length_toCNF (D : Circuit signature q (3 * (r + 1))) :
    (toCNF D).length = 2 ^ q := by
  simp [toCNF]

/-- A clause holds precisely when one of its three addressed variables has the decoded sign. -/
theorem eval_clause_eq_true_iff (D : Circuit signature q (3 * (r + 1)))
    (a : BitString r → Bool) (x : BitString q) :
    (clause D x).eval a = true ↔ ∃ j : Fin 3,
      a (fun i => D.eval interpretation x (addressWire r j i)) =
        D.eval interpretation x (signWire r j) := by
  rw [Clause.eval_eq_true_iff]
  constructor
  · rintro ⟨l, hl, h⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
    exact ⟨j, h⟩
  · rintro ⟨j, h⟩
    exact ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩, h⟩

/-- The expanded formula holds exactly when every clause address is satisfied. -/
theorem eval_toCNF_eq_true_iff (D : Circuit signature q (3 * (r + 1)))
    (a : BitString r → Bool) :
    (toCNF D).eval a = true ↔ ∀ x : BitString q, (clause D x).eval a = true := by
  simp [toCNF, CNF.eval_map_eq_true_iff]

/-- On six input wires, the first three are assignment values and the last three are signs.
The test returns true exactly when all three values differ from their signs. -/
@[expose] def violationTest : Formula signature 6 :=
  ((Formula.input 0).xor (.input 3)).and
    (((Formula.input 1).xor (.input 4)).and ((Formula.input 2).xor (.input 5)))

/-- The fixed violation test uses seventeen De Morgan gates. -/
@[simp] theorem size_violationTest : violationTest.size = 17 := by
  simp [violationTest]

/-- Evaluate the fixed test on the three values followed by the three signs. -/
theorem eval_violationTest (values signs : Fin 3 → Bool) :
    violationTest.eval interpretation (Fin.append values signs) =
      ((values 0 ^^ signs 0) && ((values 1 ^^ signs 1) && (values 2 ^^ signs 2))) := by
  simp [violationTest, Fin.append, Fin.addCases]

/-- **The bad-clause circuit.** Run the decoder once, query the proposed witness circuit on
each decoded variable address, and test whether all three literals are false. Its inputs are
the decoder's original clause-address bits. -/
@[expose] def badClause (D : Circuit signature q (3 * (r + 1)))
    (W : Circuit signature r 1) : Circuit signature q 1 :=
  (violationTest.toCircuit.comp
    ((Circuit.pi fun j : Fin 3 => W.comp (Circuit.wiring signature (addressWire r j))).append
      (Circuit.wiring signature (signWire r)))).comp D

/-- **Exact size of the bad-clause circuit.** The decoder is shared by the three witness copies;
wire selection and designated outputs cost no gates. -/
@[simp] theorem size_badClause (D : Circuit signature q (3 * (r + 1)))
    (W : Circuit signature r 1) :
    (badClause D W).size = D.size + 3 * W.size + 17 := by
  simp [badClause, Finset.sum_const, Nat.mul_comm, Nat.add_assoc]

/-- **Pointwise correctness.** The output is the negation of the addressed clause under the
assignment given by the truth table of the proposed witness circuit. -/
theorem eval_badClause (D : Circuit signature q (3 * (r + 1)))
    (W : Circuit signature r 1) (x : BitString q) :
    (badClause D W).eval interpretation x 0 =
      !(clause D x).eval (fun y => W.eval interpretation y 0) := by
  simp only [badClause, Circuit.eval_comp, Formula.eval_toCircuit, Circuit.eval_append,
    Circuit.eval_pi, Circuit.eval_wiring, eval_violationTest, Function.comp_def]
  simp only [clause, List.ofFn_succ, List.ofFn_zero, Clause.eval_cons, Clause.eval_nil,
    Literal.eval_mk, Bool.or_false]
  simp only [← Bool.bne_eq_xor, bne, Bool.not_or, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]

/-- **Verification by unsatisfiability.** The bad-clause circuit has no satisfying input exactly
when the proposed witness's truth table satisfies the entire represented formula. -/
theorem not_mem_CircuitSAT_badClause_iff (D : Circuit signature q (3 * (r + 1)))
    (W : Circuit signature r 1) :
    (⟨q, badClause D W⟩ ∉ Cslib.Complexity.CircuitSAT) ↔
      (toCNF D).eval (fun y => W.eval interpretation y 0) = true := by
  simp [Cslib.Complexity.mem_CircuitSAT, eval_badClause, eval_toCNF_eq_true_iff]

/-- **The size-bounded witness correspondence.** There is a satisfying assignment of circuit
complexity at most `s` precisely when a circuit of at most `s` gates passes verification.
This is a finite equivalence and assumes no easy-witness theorem. -/
theorem exists_small_witness_iff (D : Circuit signature q (3 * (r + 1))) (s : ℕ) :
    (∃ a : BitString r → Bool, (toCNF D).eval a = true ∧
      complexity interpretation (single a) ≤ s) ↔
    ∃ W : Circuit signature r 1, W.size ≤ s ∧
      ⟨q, badClause D W⟩ ∉ Cslib.Complexity.CircuitSAT := by
  constructor
  · rintro ⟨a, ha, hsize⟩
    obtain ⟨W, hW, hsizeW⟩ := complexity_le_iff.mp hsize
    refine ⟨W, hsizeW, (not_mem_CircuitSAT_badClause_iff D W).2 ?_⟩
    have heq : (fun y => W.eval interpretation y 0) = a :=
      funext ((Circuit.computes_single_iff).mp hW)
    rw [heq]
    exact ha
  · rintro ⟨W, hsize, hW⟩
    refine ⟨fun y => W.eval interpretation y 0,
      (not_mem_CircuitSAT_badClause_iff D W).1 hW, ?_⟩
    exact (complexity_le_of_computes W ((Circuit.computes_single_iff).2 fun _ => rfl)).trans
      hsize

end Cslib.Circuits.Boolean.SuccinctVerifier
