/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.ToCNF.Count
public import Complexity.Logics.Propositional.CNF.UnsatVal
public import Complexity.Computability.PolyTime.CSP.ToCNF

/-!
# The four-clause reduction from three-variable XOR constraints to exact three-CNF

An existing `CSP Bool V` represents a system of parity equations: `(b, [x, y, z])` asks that
`σ x ^^ σ y ^^ σ z = b`. Specializing the existing forbidden-pattern compiler produces exactly
four clauses per equation. Every assignment falsifies exactly one clause for each equation it
violates, so the unsatisfied fraction falls by exactly a factor of four. No auxiliary variables
are introduced. Repeated variables are allowed; distinct scopes give three distinct variables in
each output clause.

This is the elementary reduction in the proof of [Håstad, Theorem 6.1, p. 831][Hastad2001].
His sign-product equation `xyz = 1` corresponds to XOR `false` here. The local counting argument
is applied to entire systems, with a plain polynomial-time certificate over framed encodings.
This module does not establish hardness of MAX-E3LIN, small-soundness Label Cover, or the
perfect-completeness hardness theorem for MAX-E3SAT.

## Main definitions

* `Cslib.Logic.PL.CSP.paritySem`: the Boolean relation alphabet selecting even or odd parity.

## Main results

* `Cslib.Logic.PL.CSP.length_toCNFBounded_parity`: exactly four clauses per equation.
* `Cslib.Logic.PL.CSP.proportion_countUnsat_toCNFBounded_parity`: exact quarter-factor loss.
* `Cslib.Logic.PL.CSP.le_unsatVal_toCNFBounded_parity_iff`: transfer of universal gap bounds.
* `Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded_parity`: certified polynomial runtime.

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001], proof of Theorem 6.1, p. 831.
-/

@[expose] public section

namespace Cslib.Logic.PL.CSP

variable {V : Type*}

/-- The relation symbol `b` asks that the XOR of the local bits equal `b`. This semantics works
at every arity; the three-variable reduction explicitly assumes scopes of length three. -/
def paritySem (b : Bool) (bits : List Bool) : Bool :=
  bits.foldl Bool.xor false == b

/-- On three bits, `paritySem` is precisely the three-variable XOR equation. -/
@[simp]
theorem paritySem_three (b x y z : Bool) :
    paritySem b [x, y, z] = ((x ^^ y ^^ z) == b) := by
  cases x <;> rfl

private theorem length_constraint_toCNF_parity (c : Constraint Bool V) (hc : c.2.length = 3) :
    (Constraint.toCNF paritySem c).length = 4 := by
  simp only [Constraint.toCNF, List.length_map, hc]
  cases c.1 <;> decide

/-- A system of three-variable parity equations produces exactly four clauses per equation. -/
theorem length_toCNFBounded_parity {F : CSP Bool V} (hF : ∀ c ∈ F, c.2.length = 3) :
    (F.toCNFBounded 3 paritySem).length = 4 * F.length := by
  rw [toCNFBounded_eq_toCNF fun c hc => (hF c hc).le]
  induction F with
  | nil => rfl
  | cons c F ih =>
    have hc := hF c List.mem_cons_self
    have hrest := ih fun d hd => hF d (List.mem_cons_of_mem _ hd)
    simp only [toCNF, List.flatMap_cons, List.length_append, List.length_cons,
      length_constraint_toCNF_parity c hc, Nat.mul_succ] at hrest ⊢
    omega

/-- Every clause produced from a three-variable parity system has exactly three literals. -/
theorem length_clause_mem_toCNFBounded_parity {F : CSP Bool V}
    (hF : ∀ c ∈ F, c.2.length = 3) {cl : Clause V}
    (hcl : cl ∈ F.toCNFBounded 3 paritySem) : cl.length = 3 := by
  rw [toCNFBounded_eq_toCNF fun c hc => (hF c hc).le] at hcl
  obtain ⟨c, hc, hcl⟩ := List.mem_flatMap.mp hcl
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcl
  have hwlen := BitString.length_of_mem_enumList (List.mem_filter.mp hw).1
  rw [Constraint.length_forbidClause, hwlen, Nat.min_self, hF c hc]

/-- Three distinct variables in every input scope give three distinct variables in every output
clause. -/
theorem isExactThreeDistinct_toCNFBounded_parity {F : CSP Bool V}
    (hF : ∀ c ∈ F, c.2.length = 3 ∧ c.2.Nodup) :
    (F.toCNFBounded 3 paritySem).IsExactThreeDistinct := by
  intro cl hcl
  refine ⟨length_clause_mem_toCNFBounded_parity (fun c hc => (hF c hc).1) hcl, ?_⟩
  rw [toCNFBounded_eq_toCNF fun c hc => (hF c hc).1.le] at hcl
  obtain ⟨c, hc, hcl⟩ := List.mem_flatMap.mp hcl
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hcl
  have hwlen := BitString.length_of_mem_enumList (List.mem_filter.mp hw).1
  have hvars : (Constraint.forbidClause c.2 w).map Prod.fst = c.2 := by
    simpa only [Constraint.forbidClause, List.map_map, Function.comp_def] using
      (List.map_fst_zip hwlen.ge)
  rw [hvars]
  exact (hF c hc).2

/-- The compiler preserves satisfiability, including the empty system and repeated variables. -/
theorem satisfiable_toCNFBounded_parity {F : CSP Bool V}
    (hF : ∀ c ∈ F, c.2.length = 3) :
    (F.toCNFBounded 3 paritySem).Satisfiable ↔ F.Satisfiable paritySem := by
  rw [toCNFBounded_eq_toCNF fun c hc => (hF c hc).le, satisfiable_toCNF]

/-- For each assignment, the fraction of falsified output clauses is exactly one quarter of the
fraction of violated input equations. Both fractions are zero for the empty system. -/
theorem proportion_countUnsat_toCNFBounded_parity {F : CSP Bool V}
    (hF : ∀ c ∈ F, c.2.length = 3) (σ : V → Bool) :
    ((F.toCNFBounded 3 paritySem).countUnsat σ : ℝ) /
        (F.toCNFBounded 3 paritySem).length =
      (F.countP (fun c => !Constraint.eval paritySem σ c) : ℝ) / F.length / 4 := by
  rw [countUnsat_toCNFBounded paritySem (fun c hc => (hF c hc).le) σ,
    length_toCNFBounded_parity hF, Nat.cast_mul]
  ring

/-- A universal lower bound on the fraction of violated equations transfers with the exact factor
four. No nonempty-system assumption is hidden in this equivalence. -/
theorem le_unsatVal_toCNFBounded_parity_iff {F : CSP Bool V}
    (hF : ∀ c ∈ F, c.2.length = 3) (ε : ℝ) :
    ε / 4 ≤ (F.toCNFBounded 3 paritySem).unsatVal ↔
      ∀ σ : V → Bool, ε ≤
        (F.countP (fun c => !Constraint.eval paritySem σ c) : ℝ) / F.length := by
  rw [CNF.le_unsatVal_iff]
  simp only [proportion_countUnsat_toCNFBounded_parity hF,
    div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)]

end Cslib.Logic.PL.CSP

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Three-variable XOR-to-CNF compilation is polynomial-time under the existing framed CSP and
CNF encodings. The total compiler discards scopes longer than three; the semantic guarantees
above assume that every scope has exactly three entries. -/
@[fun_prop]
theorem computableInPolyTime_toCNFBounded_parity {V : Type} (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.toCNFBounded 3 CSP.paritySem)
      (encCSP encBool encV) (encList (encList (encPair encV encBool))) :=
  computableInPolyTime_toCNFBounded_of_finite encBool encV 3 CSP.paritySem

end Cslib.Complexity.CSP
