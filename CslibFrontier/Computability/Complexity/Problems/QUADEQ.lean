/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.Propositional.CSP.Quadratic
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# QUADEQ is NP-complete

`QUADEQ` is the language of satisfiable systems of quadratic equations
$\sum_{i,j} a_{ij} u_i u_j = b$ over `𝔽₂` in 0/1 variables
[Arora and Barak, draft, Exercise 2§18][AroraBarak07]. An instance is a list of
`Cslib.Logic.PL.QuadEquation`s whose variables are natural-number labels written in binary
(`encNat`), as in `SAT` and `XORSAT`; an equation lists the monomials `(i, j)` with
$a_{ij} = 1$, repeated monomials cancelling in pairs. No bound on the labels is imposed, so the
number of variables `n` of the source is the number of distinct labels that occur.

Membership in `NP` checks the equations under the assignment that reads each variable at its first
occurrence, as `SAT.assignment` does, so certificates are no longer than the encoded instance.
Hardness follows the hint of the exercise and reduces `SAT`: `toQUADEQ` writes, for each clause,
the chain of products $z_{t+1} = z_t \cdot \lnot\ell_t$ of `Cslib.Logic.PL.CNF.toQuadSystem` and
numbers its variables with `splitVarToNat`. Chapter 18's Walsh–Hadamard PCP starts from this
language.

## Main definitions

* `Cslib.Complexity.encQuadEquation`: the encoding of an equation.
* `Cslib.Complexity.QUADEQ.encoding`, `Cslib.Complexity.QUADEQ`: instances and the language.
* `Cslib.Complexity.QUADEQ.verifier`: the `NP` verifier.
* `Cslib.Complexity.toQUADEQ`: the reduction from `SAT`.

## Main results

* `Cslib.Complexity.QUADEQ.mem_NP`: `QUADEQ ∈ NP`.
* `Cslib.Complexity.mem_QUADEQ_toQUADEQ_iff`, `Cslib.Complexity.computableInPolyTime_toQUADEQ`:
  correctness and polynomial-time computability of the reduction.
* `Cslib.Complexity.polyTimeReducible_SAT_QUADEQ`, `Cslib.Complexity.QUADEQ_npHard`,
  `Cslib.Complexity.QUADEQ_npComplete`: `QUADEQ` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, draft][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

variable {V : Type}

/-- Encoding of a quadratic equation: its framed list of monomials, each a pair of variables, then
its right-hand side bit. -/
enc_structure encQuadEquation (encV : V ↪ List Bool) : QuadEquation V where
  terms : (encList (encPair encV encV)), rhs : encBool

/-- Systems of quadratic equations over binary natural-number labels, as framed lists of
equations. -/
@[expose] def QUADEQ.encoding : QuadSystem ℕ ↪ List Bool := encList (encQuadEquation encNat)

/-- **QUADEQ**: the satisfiable systems of quadratic equations over `𝔽₂` in 0/1 variables
[Arora and Barak, draft, Exercise 2§18][AroraBarak07]. -/
@[expose] def QUADEQ : Set (QuadSystem ℕ) := {F | F.Satisfiable}

/-- A system is in `QUADEQ` exactly when it is satisfiable. -/
theorem mem_QUADEQ {F : QuadSystem ℕ} : F ∈ QUADEQ ↔ F.Satisfiable := Iff.rfl

namespace QUADEQ

/-! ### The verifier -/

/-- The assignment described by a certificate `w` for `F`: each variable takes the bit of `w` at
the position of its first occurrence in `F`. -/
@[expose] def assignment (F : QuadSystem ℕ) (w : List Bool) (v : ℕ) : Bool :=
  w.getD (F.vars.idxOf v) false

/-- Evaluate an equation under an assignment: the exclusive or of the monomials, compared with the
right-hand side. -/
@[expose] def evalEquation (a : ℕ → Bool) (e : QuadEquation ℕ) : Bool :=
  (e.terms.map fun p => a p.1 && a p.2).foldl xor false == e.rhs

/-- The verifier for `QUADEQ`: every equation holds under the assignment the certificate
describes. -/
@[expose] def verifier (x : QuadSystem ℕ × List Bool) : Bool :=
  x.1.all (evalEquation (assignment x.1 x.2))

/-- `evalEquation` decides `QuadEquation.Holds`. -/
theorem evalEquation_eq_true_iff (a : ℕ → Bool) (e : QuadEquation ℕ) :
    evalEquation a e = true ↔ e.Holds a := by
  simp only [evalEquation, QuadEquation.Holds, beq_iff_eq, List.sum_eq_foldl]
  rfl

/-- The verifier accepts exactly when the certificate's assignment satisfies the system. -/
theorem verifier_eq_true_iff (F : QuadSystem ℕ) (w : List Bool) :
    verifier (F, w) = true ↔ F.Holds (assignment F w) := by
  simp only [verifier, List.all_eq_true, evalEquation_eq_true_iff, QuadSystem.Holds]

/-- The values of `a` listed along the occurrences of `F`, followed by any bits, describe `a` on
the variables of `F`. -/
theorem assignment_vars_map_append (F : QuadSystem ℕ) (a : ℕ → Bool) (w : List Bool) {v : ℕ}
    (hv : v ∈ F.vars) : assignment F (F.vars.map a ++ w) v = a v := by
  simp [assignment, List.getD_eq_getElem?_getD, List.getElem?_append_left,
    List.idxOf_lt_length_iff.2 hv]

/-- A system has no more variable occurrences than its encoding has bits: each monomial names two
variables, and its framed encoding takes at least two bits. -/
theorem length_vars_le (F : QuadSystem ℕ) : F.vars.length ≤ (encoding F).length := by
  have hterms (l : List (ℕ × ℕ)) : (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
    induction l with
    | nil => rfl
    | cons p l ih =>
      simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]
      omega
  have he (e : QuadEquation ℕ) : e.vars.length ≤ (encQuadEquation encNat e).length := by
    have := length_le_length_encList (encPair encNat encNat) e.terms
    simp only [QuadEquation.vars, hterms, encQuadEquation_apply, encQuadEquationFields,
      length_encPair]
    omega
  calc F.vars.length = (F.map fun e => e.vars.length).sum := by
        simp only [QuadSystem.vars, List.length_flatMap]
    _ ≤ (F.map fun e => (encQuadEquation encNat e).length).sum := List.sum_le_sum fun e _ => he e
    _ ≤ (encoding F).length := sum_length_le_length_encList _ F

/-- `QUADEQ.verifier` verifies `QUADEQ` with certificates as long as the encoded system: a
satisfying assignment, listed along the occurrences, is a prefix the verifier accepts whatever
padding follows it. -/
theorem isVerifier : IsVerifier encoding Polynomial.X verifier QUADEQ := by
  refine IsVerifier.of_padding (fun F w _ h => ⟨_, (verifier_eq_true_iff F w).1 h⟩)
    fun F ⟨a, ha⟩ => ?_
  refine ⟨F.vars.map a, by simpa using length_vars_le F, fun k => (verifier_eq_true_iff ..).2 ?_⟩
  exact (QuadSystem.holds_congr fun _ hv => assignment_vars_map_append F a _ hv).2 ha

/-- The `QUADEQ` verifier is polynomial-time, including on certificates of arbitrary length. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encoding encBits) encBool := by
  unfold verifier evalEquation assignment QuadSystem.vars QuadEquation.vars encoding
  fun_prop

/-- `QUADEQ` belongs to `NP`. -/
theorem mem_NP : QUADEQ ∈ NP encoding :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end QUADEQ

/-! ### The reduction from SAT -/

/-- The reduction from `SAT` to `QUADEQ`: the chained clause equations of
`Cslib.Logic.PL.CNF.toQuadSystem`, with variables numbered by `splitVarToNat`. -/
@[expose] def toQUADEQ (φ : CNF ℕ) : QuadSystem ℕ := φ.toQuadSystem.relabel splitVarToNat

/-- **Correctness of the reduction**: `toQUADEQ φ` is in `QUADEQ` exactly when `φ` is in `SAT`. -/
theorem mem_QUADEQ_toQUADEQ_iff (φ : CNF ℕ) : toQUADEQ φ ∈ QUADEQ ↔ φ ∈ SAT :=
  (QuadSystem.satisfiable_relabel splitVarToNat_injective _).trans (CNF.satisfiable_toQuadSystem φ)

/-- Encoding of the variables of `Cslib.Logic.PL.CNF.toQuadSystem`: a tag bit, then either a
formula variable in binary or a framed pair of unary clause and position indices. -/
abbrev encQuadVar : ℕ ⊕ ℕ × ℕ ↪ List Bool := encSum encNat (encPair encUnary encUnary)

section PolyTime

variable {γ : Type} {input : γ ↪ List Bool}

/-- Building the equation $z_{i,t} = c$ is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_auxEq {i t : γ → ℕ} {c : γ → Bool}
    (hi : ComputableInPolyTime i input encUnary) (ht : ComputableInPolyTime t input encUnary)
    (hc : ComputableInPolyTime c input encBool) :
    ComputableInPolyTime (fun x => CNF.auxEq (V := ℕ) (i x) (t x) (c x)) input
      (encQuadEquation encQuadVar) := by
  unfold CNF.auxEq CNF.auxVar
  fun_prop

/-- Building the equation $z_{i,t+1} = z_{i,t}\cdot\lnot\ell$ is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_stepEq {i t : γ → ℕ} {l : γ → Literal ℕ}
    (hi : ComputableInPolyTime i input encUnary) (ht : ComputableInPolyTime t input encUnary)
    (hl : ComputableInPolyTime l input (encPair encNat encBool)) :
    ComputableInPolyTime (fun x => CNF.stepEq (i x) (t x) (l x)) input
      (encQuadEquation encQuadVar) := by
  unfold CNF.stepEq CNF.auxVar
  fun_prop

/-- Building the equations of a clause is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_clauseQuadSystem {i : γ → ℕ} {c : γ → Clause ℕ}
    (hi : ComputableInPolyTime i input encUnary)
    (hc : ComputableInPolyTime c input (encList (encPair encNat encBool))) :
    ComputableInPolyTime (fun x => CNF.clauseQuadSystem (i x) (c x)) input
      (encList (encQuadEquation encQuadVar)) := by
  unfold CNF.clauseQuadSystem
  fun_prop

end PolyTime

/-- The quadratic system of a formula is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toQuadSystem :
    ComputableInPolyTime (CNF.toQuadSystem (V := ℕ)) encCNF
      (encList (encQuadEquation encQuadVar)) := by
  unfold CNF.toQuadSystem encCNF
  fun_prop

/-- Relabelling a system by a polynomial-time map is polynomial-time. -/
theorem computableInPolyTime_relabel {W : Type} {encV : V ↪ List Bool} {encW : W ↪ List Bool}
    {f : V → W} (hf : ComputableInPolyTime f encV encW) :
    ComputableInPolyTime (QuadSystem.relabel f) (encList (encQuadEquation encV))
      (encList (encQuadEquation encW)) := by
  unfold QuadSystem.relabel QuadEquation.relabel Prod.map
  fun_prop

/-- The reduction `toQUADEQ` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toQUADEQ :
    ComputableInPolyTime toQUADEQ encCNF QUADEQ.encoding :=
  (computableInPolyTime_relabel computableInPolyTime_splitVarToNat).comp
    computableInPolyTime_toQuadSystem

/-- `SAT` reduces to `QUADEQ` in polynomial time via `toQUADEQ`. -/
theorem polyTimeReducible_SAT_QUADEQ : PolyTimeReducible encCNF QUADEQ.encoding SAT QUADEQ :=
  ⟨toQUADEQ, computableInPolyTime_toQUADEQ, fun φ => (mem_QUADEQ_toQUADEQ_iff φ).symm⟩

/-- `QUADEQ` is `NP`-hard. -/
theorem QUADEQ_npHard : NPHard QUADEQ.encoding QUADEQ :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_QUADEQ

/-- **QUADEQ is NP-complete** [Arora and Barak, draft, Exercise 2§18][AroraBarak07]. -/
theorem QUADEQ_npComplete : NPComplete QUADEQ.encoding QUADEQ :=
  ⟨QUADEQ.mem_NP, QUADEQ_npHard⟩

end Cslib.Complexity
