/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.ExactThreeSAT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# MAX 2-SAT is NP-complete

`MaxTwoSAT` consists of instances `x : MaxTwoSATInstance` (`Cslib.Complexity.encMaxTwoSAT`) pairing
a formula `x.formula` in conjunctive normal form with at most two literals per clause and a target
`x.target` such that some assignment satisfies at least `x.target` clauses of `x.formula`, counted
with multiplicity. Garey, Johnson and Stockmeyer proved it `NP`-complete
[Garey, Johnson and Stockmeyer][GareyJohnsonStockmeyer1976] (attribution from secondary sources;
the theorem number is not checked against the paper), although 2-satisfiability itself is in `NL`
(`Cslib.Complexity.TwoSAT.mem_NL`).

The reduction is their ten-clause gadget. For a clause `a ∨ b ∨ c` and a fresh variable `w`, the
formula `MaxTwoSAT.gadget a b c w` has the ten clauses
`a, b, c, w, ¬a ∨ ¬b, ¬a ∨ ¬c, ¬b ∨ ¬c, a ∨ ¬w, b ∨ ¬w, c ∨ ¬w`. Every assignment satisfies at
most seven of them; some value of `w` reaches seven exactly when the assignment satisfies
`a ∨ b ∨ c`, and otherwise at most six are satisfied (`MaxTwoSAT.gadgetScore`). The table depends
only on the truth values of `a`, `b`, `c`, so repeated literals are harmless. The reduction
`toMaxTwoSAT` starts from `ExactThreeSAT`, doubles the source variables so that the odd numbers
are fresh, puts one gadget on each clause, and asks for seven satisfied clauses per gadget; a
formula with a clause of another width becomes a fixed no-instance. Composed with the padding
`toExactThreeSAT`, which repeats a literal of every clause of one or two literals, this reduces
`ThreeSAT` to `MaxTwoSAT`.

## Main definitions

* `Cslib.Complexity.MaxTwoSATInstance`, `Cslib.Complexity.encMaxTwoSAT`.
* `Cslib.Complexity.MaxTwoSAT`: the decision version of maximum 2-satisfiability.
* `Cslib.Complexity.MaxTwoSAT.gadget`: the ten-clause gadget of one clause.
* `Cslib.Complexity.toMaxTwoSAT`: the reduction from `ExactThreeSAT`.

## Main results

* `Cslib.Complexity.MaxTwoSAT.mem_NP`: `MaxTwoSAT ∈ NP encMaxTwoSAT`.
* `Cslib.Complexity.MaxTwoSAT.countP_gadget`: the satisfied clauses of one gadget, counted by
  `MaxTwoSAT.gadgetScore`.
* `Cslib.Complexity.MaxTwoSAT.gadgetScore_le`, `Cslib.Complexity.MaxTwoSAT.gadgetScore_majority`,
  `Cslib.Complexity.MaxTwoSAT.gadgetScore_false_le`: at most seven, seven when the clause holds and
  the fresh variable is the majority, at most six when the clause fails.
* `Cslib.Complexity.mem_MaxTwoSAT_toMaxTwoSAT_iff`: correctness of the reduction.
* `Cslib.Complexity.polyTimeReducible_ExactThreeSAT_MaxTwoSAT`,
  `Cslib.Complexity.polyTimeReducible_ThreeSAT_MaxTwoSAT`: `ExactThreeSAT` and `ThreeSAT` reduce
  to `MaxTwoSAT`.
* `Cslib.Complexity.MaxTwoSAT_npComplete`: `MaxTwoSAT` is `NP`-complete.

## References

* [M. R. Garey, D. S. Johnson, L. Stockmeyer, *Some simplified NP-complete graph
  problems*][GareyJohnsonStockmeyer1976]
* [M. R. Garey, D. S. Johnson, *Computers and Intractability*][GareyJohnson1979], Problem LO5
  (locator from secondary sources)
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 9.2 (locator from
  secondary sources)
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- An instance `(formula, target)` of **MAX 2-SAT**. -/
@[ext]
structure MaxTwoSATInstance where
  /-- The formula in conjunctive normal form, with at most two literals per clause. -/
  formula : CNF ℕ
  /-- The minimum number of clauses that must be satisfied. -/
  target : ℕ
  deriving DecidableEq, Repr

/-- Encoding of `MaxTwoSATInstance` as `(formula, target)` with `target` in binary. -/
enc_structure encMaxTwoSAT : MaxTwoSATInstance where
  formula : encCNF,
  target : encNat

attribute [fun_prop] encMaxTwoSAT_formula_polyTime encMaxTwoSAT_target_polyTime
  encMaxTwoSAT_mk_polyTime

/-- Maximum 2-satisfiability: the instances `x : MaxTwoSATInstance` such that every clause of
`x.formula` has at most two literals and some assignment satisfies at least `x.target` clauses of
`x.formula`, counted with multiplicity. -/
@[expose]
def MaxTwoSAT : Set MaxTwoSATInstance :=
  {x | (∀ c ∈ x.formula, c.length ≤ 2) ∧
    ∃ σ : ℕ → Bool, x.target ≤ x.formula.countP (Clause.eval σ)}

/-- Membership in `MaxTwoSAT`, unfolded. -/
@[simp]
theorem mem_MaxTwoSAT_iff {φ : CNF ℕ} {K : ℕ} :
    (⟨φ, K⟩ : MaxTwoSATInstance) ∈ MaxTwoSAT ↔
      (∀ c ∈ φ, c.length ≤ 2) ∧ ∃ σ : ℕ → Bool, K ≤ φ.countP (Clause.eval σ) :=
  Iff.rfl

namespace MaxTwoSAT


/-! ### Membership in NP -/

/-- The verifier for `MaxTwoSAT`: check that every clause has at most two literals and count the
clauses satisfied by the certificate assignment of `SAT.assignment`. -/
@[expose]
def verifier (x : MaxTwoSATInstance × List Bool) : Bool :=
  (x.1.formula.all fun c => decide (c.length ≤ 2)) &&
    decide (x.1.target ≤ x.1.formula.countP (Clause.eval (SAT.assignment x.1.formula x.2)))

/-- `MaxTwoSAT.verifier` verifies `MaxTwoSAT` with certificates as long as the encoded instance:
the certificate lists the values of the variables in order of first occurrence. -/
theorem isVerifier : IsVerifier encMaxTwoSAT Polynomial.X verifier MaxTwoSAT := by
  refine IsVerifier.of_padding (fun x w _ h => ?_) fun x hx => ?_
  · simp only [verifier, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, _, h.2⟩
  · obtain ⟨hlen, σ, hσ⟩ := hx
    have hvars : x.formula.vars.length ≤ (encMaxTwoSAT x).length :=
      (SAT.length_vars_le x.formula).trans
        (by rw [encMaxTwoSAT_apply]
            exact length_le_encPair_left encCNF encNat (x.formula, x.target))
    refine ⟨x.formula.vars.map σ, by simpa using hvars, fun k => ?_⟩
    simp only [verifier, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨hlen, hσ.trans (CNF.countP_eval_congr fun v hv => ?_).le⟩
    have hlt : x.formula.vars.idxOf v < x.formula.vars.length := List.idxOf_lt_length_iff.2 hv
    have hlt' : x.formula.vars.idxOf v < (x.formula.vars.map σ).length := by simpa using hlt
    rw [SAT.assignment, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt',
      List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]
    rfl

/-- Checking the clause widths and counting the satisfied clauses is polynomial-time: the count
is computed in unary and compared with the binary target. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encMaxTwoSAT encBits) encBool := by
  have hφ : ComputableInPolyTime (fun x : MaxTwoSATInstance × List Bool => x.1.formula)
      (encPair encMaxTwoSAT encBits) (encList (encList (encPair encNat encBool))) :=
    encMaxTwoSAT_formula_polyTime (fst _ _)
  have hcount : ComputableInPolyTime
      (fun x : MaxTwoSATInstance × List Bool =>
        x.1.formula.countP (Clause.eval (SAT.assignment x.1.formula x.2)))
      (encPair encMaxTwoSAT encBits) encNat :=
    unary_to_binary.comp (countPWithInput hφ (SAT.computableInPolyTime_clause.comp
      (((hφ.comp (fst _ _)).prod ((snd _ _).comp (fst _ _))).prod (snd _ _))))
  have hwidth : ComputableInPolyTime
      (fun x : MaxTwoSATInstance × List Bool => x.1.formula.all fun c => decide (c.length ≤ 2))
      (encPair encMaxTwoSAT encBits) encBool :=
    (show ComputableInPolyTime (fun φ : CNF ℕ => φ.all fun c => decide (c.length ≤ 2))
      encCNF encBool by unfold encCNF; fun_prop).comp (encMaxTwoSAT_formula_polyTime (fst _ _))
  exact bool_and' hwidth (binary_le' (encMaxTwoSAT_target_polyTime (fst _ _)) hcount)

/-- `MaxTwoSAT` belongs to `NP`. -/
theorem mem_NP : MaxTwoSAT ∈ NP encMaxTwoSAT :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

/-! ### The gadget -/

/-- The ten-clause gadget of Garey, Johnson and Stockmeyer for the clause `a ∨ b ∨ c`, with the
variable `w`: the unit clauses `a`, `b`, `c`, `w`, the clauses `¬a ∨ ¬b`, `¬a ∨ ¬c`, `¬b ∨ ¬c`, and
the clauses `a ∨ ¬w`, `b ∨ ¬w`, `c ∨ ¬w`. -/
@[expose]
def gadget (a b c : Literal ℕ) (w : ℕ) : CNF ℕ :=
  [[a], [b], [c], [(w, true)], [a.negate, b.negate], [a.negate, c.negate], [b.negate, c.negate],
    [a, (w, false)], [b, (w, false)], [c, (w, false)]]

/-- The number of satisfied clauses of a gadget whose literals take the values `x`, `y`, `z` and
whose variable takes the value `q`. -/
@[expose]
def gadgetScore (x y z q : Bool) : ℕ :=
  x.toNat + y.toNat + z.toNat + q.toNat + (!x || !y).toNat + (!x || !z).toNat +
    (!y || !z).toNat + (x || !q).toNat + (y || !q).toNat + (z || !q).toNat

/-- The number of satisfied clauses of a gadget depends only on the values of its literals and of
its variable. -/
theorem countP_gadget (σ : ℕ → Bool) (a b c : Literal ℕ) (w : ℕ) :
    (gadget a b c w).countP (Clause.eval σ) =
      gadgetScore (Literal.eval σ a) (Literal.eval σ b) (Literal.eval σ c) (σ w) := by
  simp only [gadget, gadgetScore, List.countP_cons, List.countP_nil, Clause.eval_cons,
    Clause.eval_nil, Literal.eval_negate, Literal.eval_mk, Bool.or_false]
  cases Literal.eval σ a <;> cases Literal.eval σ b <;> cases Literal.eval σ c <;> cases σ w <;>
    rfl

/-- A gadget never has more than seven satisfied clauses. -/
theorem gadgetScore_le (x y z q : Bool) : gadgetScore x y z q ≤ 7 := by
  cases x <;> cases y <;> cases z <;> cases q <;> decide

/-- The majority of three truth values. -/
def majority (x y z : Bool) : Bool := x && y || x && z || y && z

/-- If the clause holds, setting the variable to the majority of its literals satisfies seven
clauses of the gadget. -/
theorem gadgetScore_majority {x y z : Bool} (h : (x || y || z) = true) :
    gadgetScore x y z (majority x y z) = 7 := by
  cases x <;> cases y <;> cases z <;> simp_all [gadgetScore, majority]

/-- If the clause fails, the gadget has at most six satisfied clauses. -/
theorem gadgetScore_false_le (q : Bool) : gadgetScore false false false q ≤ 6 := by
  cases q <;> decide

/-- Every clause of a gadget has at most two literals. -/
private theorem length_le_of_mem_gadget {a b c : Literal ℕ} {w : ℕ} {d : Clause ℕ}
    (hd : d ∈ gadget a b c w) : d.length ≤ 2 := by
  simp only [gadget, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end MaxTwoSAT

/-! ### The reduction -/

open MaxTwoSAT

/-- Double the variable of a literal; the odd variables are then free for the gadgets. -/
@[expose]
def MaxTwoSAT.doubleLiteral (l : Literal ℕ) : Literal ℕ := (2 * l.1, l.2)

/-- The gadget of the clause numbered `i`, whose first three literals are doubled, with the fresh
variable `2 i + 1`. -/
@[expose]
def MaxTwoSAT.clauseGadget (c : Clause ℕ) (i : ℕ) : CNF ℕ :=
  gadget (doubleLiteral (c.headD (0, true))) (doubleLiteral (c.tail.headD (0, true)))
    (doubleLiteral (c.tail.tail.headD (0, true))) (2 * i + 1)

/-- The reduction from `ExactThreeSAT` to `MaxTwoSAT`: a formula all of whose clauses have three
literals becomes the gadgets of its clauses, with target seven satisfied clauses per gadget. Any
other formula becomes the formula with one empty clause and target one, a fixed no-instance: no
assignment satisfies the empty clause. -/
@[expose]
def toMaxTwoSAT (φ : CNF ℕ) : MaxTwoSATInstance :=
  if φ.all fun c => c.length == 3 then
    ⟨φ.zipIdx.flatMap fun c => clauseGadget c.1 c.2, 7 * φ.length⟩
  else ⟨[[]], 1⟩

/-- The satisfied clauses of the reduced formula are the sum of the satisfied clauses of the
gadgets. -/
private theorem MaxTwoSAT.countP_flatMap_clauseGadget (σ : ℕ → Bool) (φ : CNF ℕ) :
    (φ.zipIdx.flatMap fun c => clauseGadget c.1 c.2).countP (Clause.eval σ) =
      (φ.zipIdx.map fun c => (clauseGadget c.1 c.2).countP (Clause.eval σ)).sum := by
  rw [List.countP_flatMap]
  rfl

/-- On a clause of three literals, the gadget score under `σ` is that of the three literal values
under any `τ` with `τ v = σ (2 v)`. -/
private theorem MaxTwoSAT.countP_clauseGadget (σ τ : ℕ → Bool) (hτ : ∀ v, τ v = σ (2 * v))
    (a b c : Literal ℕ) (i : ℕ) :
    (clauseGadget [a, b, c] i).countP (Clause.eval σ) =
      gadgetScore (Literal.eval τ a) (Literal.eval τ b) (Literal.eval τ c) (σ (2 * i + 1)) := by
  have hτ' : τ = fun v => σ (2 * v) := funext hτ
  subst hτ'
  rw [clauseGadget, countP_gadget]
  rfl

/-- A formula is in `ExactThreeSAT` exactly when its image under `toMaxTwoSAT` is in
`MaxTwoSAT`. -/
theorem mem_MaxTwoSAT_toMaxTwoSAT_iff (φ : CNF ℕ) :
    toMaxTwoSAT φ ∈ MaxTwoSAT ↔ φ ∈ ExactThreeSAT := by
  by_cases hall : (φ.all fun c => c.length == 3) = true
  · have h3 : ∀ c ∈ φ, c.length = 3 := by simpa using hall
    have hzip : ∀ c j, (c, j) ∈ φ.zipIdx → ∃ a b d : Literal ℕ, c = [a, b, d] := fun c j hp =>
      List.length_eq_three.1 (h3 c (List.fst_mem_of_mem_zipIdx hp))
    simp only [toMaxTwoSAT, hall, ↓reduceIte, mem_MaxTwoSAT_iff, countP_flatMap_clauseGadget]
    constructor
    · rintro ⟨-, σ, hσ⟩
      refine ⟨h3, fun v => σ (2 * v), (CNF.eval_eq_true_iff _ _).2 fun c hc => ?_⟩
      by_contra hfalse
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
      have hmem : (φ[i], i) ∈ φ.zipIdx :=
        List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hi)
      refine absurd hσ (not_le.2 ?_)
      have hlt := List.sum_lt_sum (l := φ.zipIdx)
        (fun p => (clauseGadget p.1 p.2).countP (Clause.eval σ)) (fun _ => 7)
        (fun ⟨c, j⟩ hp => by
          obtain ⟨a, b, d, rfl⟩ := hzip c j hp
          rw [countP_clauseGadget σ _ fun _ => rfl]
          exact gadgetScore_le _ _ _ _)
        ⟨(φ[i], i), hmem, by
          obtain ⟨a, b, d, hp⟩ := hzip _ _ hmem
          dsimp only
          rw [hp, countP_clauseGadget σ _ fun _ => rfl]
          rw [hp] at hfalse
          simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false, Bool.not_eq_true,
            Bool.or_eq_false_iff] at hfalse
          obtain ⟨ha, hb, hd⟩ := hfalse
          rw [ha, hb, hd]
          exact Nat.lt_of_le_of_lt (gadgetScore_false_le _) (by norm_num)⟩
      simpa [List.map_const', List.sum_replicate, List.length_zipIdx, mul_comm] using hlt
    · rintro ⟨-, τ, hτ⟩
      refine ⟨fun d hd => ?_, fun n => if n % 2 = 0 then τ (n / 2) else
        majority (Literal.eval τ ((φ.getD (n / 2) []).headD (0, true)))
          (Literal.eval τ ((φ.getD (n / 2) []).tail.headD (0, true)))
          (Literal.eval τ ((φ.getD (n / 2) []).tail.tail.headD (0, true))), ?_⟩
      · obtain ⟨p, -, hd⟩ := List.mem_flatMap.1 hd
        exact length_le_of_mem_gadget hd
      · refine le_of_eq ?_
        rw [List.map_congr_left (g := fun _ => 7) fun p hp => ?_]
        · simp [List.map_const', List.sum_replicate, List.length_zipIdx, mul_comm]
        obtain ⟨c, j⟩ := p
        obtain ⟨a, b, d, rfl⟩ := hzip c j hp
        have hget : φ[j]? = some [a, b, d] := List.mem_zipIdx_iff_getElem?.1 hp
        have hc : Clause.eval τ [a, b, d] = true :=
          (CNF.eval_eq_true_iff _ _).1 hτ _ (List.mem_of_getElem? hget)
        dsimp only
        rw [countP_clauseGadget _ τ fun v => by simp]
        have hodd : ¬(2 * j + 1) % 2 = 0 := by omega
        have hdiv : (2 * j + 1) / 2 = j := by omega
        simp only [hodd, hdiv, ↓reduceIte, List.getD_eq_getElem?_getD, hget, Option.getD_some,
          List.headD_cons, List.tail_cons]
        simp only [Clause.eval_cons, Clause.eval_nil, Bool.or_false] at hc
        exact gadgetScore_majority (by simpa [Bool.or_assoc] using hc)
  · simp only [toMaxTwoSAT, hall, Bool.false_eq_true, ↓reduceIte]
    refine iff_of_false (fun ⟨_, σ, hσ⟩ => ?_) fun ⟨h3, _⟩ => hall ?_
    · simp at hσ
    · simpa using h3

/-! ### Polynomial time -/

/-- Doubling the variable of a literal is polynomial-time. -/
private theorem computableInPolyTime_doubleLiteral :
    ComputableInPolyTime doubleLiteral (encPair encNat encBool) (encPair encNat encBool) := by
  unfold doubleLiteral
  fun_prop

/-- Negating a literal is polynomial-time. -/
private theorem computableInPolyTime_negate :
    ComputableInPolyTime (Std.Sat.Literal.negate (α := ℕ)) (encPair encNat encBool)
      (encPair encNat encBool) := by
  unfold Std.Sat.Literal.negate
  fun_prop

/-- The gadget of a numbered clause, with the number in unary, is polynomial-time. -/
private theorem computableInPolyTime_clauseGadget :
    ComputableInPolyTime (fun p : CNF ℕ × Clause ℕ × ℕ => clauseGadget p.2.1 p.2.2)
      (encPair encCNF (encPair (encList (encPair encNat encBool)) encUnary)) encCNF := by
  have hodd : ComputableInPolyTime (fun i : ℕ => 2 * i + 1) encUnary encNat :=
    unary_to_binary.comp (by fun_prop)
  have hd := computableInPolyTime_doubleLiteral
  have hn := computableInPolyTime_negate
  unfold clauseGadget gadget encCNF
  fun_prop

private theorem computableInPolyTime_zipIdx_cnf :
    ComputableInPolyTime (List.zipIdx (α := Clause ℕ)) encCNF
      (encList (encPair (encList (encPair encNat encBool)) encUnary)) := by
  unfold encCNF
  fun_prop

private theorem computableInPolyTime_allThree :
    ComputableInPolyTime (fun φ : CNF ℕ => φ.all fun c => c.length == 3) encCNF encBool := by
  unfold encCNF
  fun_prop

private theorem computableInPolyTime_target :
    ComputableInPolyTime (fun φ : CNF ℕ => 7 * φ.length) encCNF encNat :=
  unary_to_binary.comp (by fun_prop)

private theorem computableInPolyTime_gadgets :
    ComputableInPolyTime (fun φ : CNF ℕ => φ.zipIdx.flatMap fun c => clauseGadget c.1 c.2) encCNF
      encCNF := by
  exact flatMapWithInput computableInPolyTime_zipIdx_cnf computableInPolyTime_clauseGadget

/-- The reduction `toMaxTwoSAT` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toMaxTwoSAT :
    ComputableInPolyTime toMaxTwoSAT encCNF encMaxTwoSAT :=
  ite' computableInPolyTime_allThree
    (encMaxTwoSAT_mk_polyTime computableInPolyTime_gadgets computableInPolyTime_target)
    (const _)

/-- `ExactThreeSAT` reduces to `MaxTwoSAT` in polynomial time via `toMaxTwoSAT`. -/
theorem polyTimeReducible_ExactThreeSAT_MaxTwoSAT :
    PolyTimeReducible encCNF encMaxTwoSAT ExactThreeSAT MaxTwoSAT :=
  ⟨toMaxTwoSAT, computableInPolyTime_toMaxTwoSAT,
    fun φ => (mem_MaxTwoSAT_toMaxTwoSAT_iff φ).symm⟩

/-- `ThreeSAT` reduces to `MaxTwoSAT` in polynomial time: pad every clause to three literals by
repetition (`toExactThreeSAT`), then apply `toMaxTwoSAT`. -/
theorem polyTimeReducible_ThreeSAT_MaxTwoSAT :
    PolyTimeReducible encCNF encMaxTwoSAT ThreeSAT MaxTwoSAT :=
  polyTimeReducible_ThreeSAT_ExactThreeSAT.trans polyTimeReducible_ExactThreeSAT_MaxTwoSAT

/-- `MaxTwoSAT` is `NP`-hard. -/
theorem MaxTwoSAT_npHard : NPHard encMaxTwoSAT MaxTwoSAT :=
  ExactThreeSAT_npHard.trans polyTimeReducible_ExactThreeSAT_MaxTwoSAT

/-- **MAX 2-SAT is NP-complete** [Garey, Johnson and Stockmeyer][GareyJohnsonStockmeyer1976]
(attribution from secondary sources). The target `K` is in binary, and clauses of one literal are
allowed. -/
theorem MaxTwoSAT_npComplete : NPComplete encMaxTwoSAT MaxTwoSAT :=
  ⟨MaxTwoSAT.mem_NP, MaxTwoSAT_npHard⟩

end Cslib.Complexity
