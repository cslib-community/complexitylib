/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.EvaluationTime
public import Complexity.Computability.Circuit.Boolean.OpValue
public import Complexity.Logics.Propositional.CNF
import Mathlib.Data.List.GetD

/-!
# The Tseitin formula of a De Morgan circuit

Tseitin's encoding turns a circuit into a formula in conjunctive normal form with one variable
per wire [Tseitin][Tseitin1983], [Arora and Barak, Section 6.1][AroraBarak09]. A gate
`w = op(a, b)` contributes the clauses `tseitinClause op w a b`, which hold together exactly when
`w` carries the value `Op.value op a b` of the gate (`forall_eval_tseitinClause_iff`). The clauses
of the gates of a De Morgan gate list (`Cslib.Circuits.Program.code`) form `tseitinCNF n gates`,
with gate `g` at wire `n + g`; an assignment satisfies it exactly when it is the evaluation of the
list on its own values at the inputs (`eval_tseitinCNF_eq_true_iff_evalCode`).

`tseitinSatCNF x n gates o` adds unit clauses that fix the first inputs to the bits of `x` and
the wire `o` to `true`. It is satisfiable exactly when some input extending `x` makes wire `o`
true (`satisfiable_tseitinSatCNF_iff`); for `x = []` and the output of a circuit, this is circuit
satisfiability (`satisfiable_tseitinSatCNF_circuit_iff`).

The formula is laid out uniformly: every gate has exactly three clauses, and every clause has
exactly three literals (`length_of_mem_tseitinSatCNF`), shorter clauses being padded by repeating a
literal. Clause `j` of a gate depends only on its operation, on `j` and on the variables of the
gate, so a circuit that computes a clause from its number (a succinct description of the formula)
has a fixed output width. The frontier compiler (`Cslib.Circuits.Frontier.Compiler.toCNF`)
instead numbers only the reachable wires, which preserves the number of models but is not
uniform.

## Main definitions

* `Cslib.Circuits.Boolean.tseitinClause`: the three clauses of a gate.
* `Cslib.Circuits.Boolean.tseitinCNF`: the clauses of a gate list.
* `Cslib.Circuits.Boolean.tseitinSatCNF`: the clauses of a gate list, with unit clauses fixing an
  input prefix and an output wire.

## Main results

* `Cslib.Circuits.Boolean.forall_eval_tseitinClause_iff`: the semantics of the clauses of a gate.
* `Cslib.Circuits.Boolean.eval_tseitinCNF_eq_true_iff`,
  `Cslib.Circuits.Boolean.eval_tseitinCNF_eq_true_iff_evalCode`: the assignments satisfying the
  Tseitin formula are those consistent with every gate, which are the evaluations of the list.
* `Cslib.Circuits.Boolean.satisfiable_tseitinSatCNF_iff`: satisfiability with a fixed input prefix.
* `Cslib.Circuits.Boolean.satisfiable_tseitinSatCNF_circuit_iff`: the same for circuits.
* `Cslib.Circuits.Boolean.length_of_mem_tseitinSatCNF`,
  `Cslib.Circuits.Boolean.length_tseitinSatCNF`: every clause has three literals, and there are
  `1 + x.length + 3 * gates.length` clauses.

## References

* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Cslib.Logic.PL

variable {V : Type*}

/-! ### The clauses of a gate -/

/-- A gate code with as many arguments as its arity computes its operation on the values of its
first two listed arguments. -/
theorem interpretation_eq_value (gate : Op × List ℕ) (h : gate.2.length = signature.Arity gate.1)
    (f : ℕ → Bool) (d : Bool) :
    interpretation gate.1 (fun i => gate.2[i.val]?.elim d f) =
      gate.1.value (f (gate.2.getD 0 0)) (f (gate.2.getD 1 0)) := by
  obtain ⟨op, args⟩ := gate
  cases op <;> rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, args⟩⟩⟩ <;>
    simp only [List.length_nil, List.length_cons] at h <;> first | rfl | omega

/-- **The Tseitin clauses of a gate** `w = op(a, b)`: three clauses of exactly three literals,
which hold together exactly when `w` carries the value of the gate
(`forall_eval_tseitinClause_iff`). A constant mentions only `w`, and a negation only `w` and
`a`; shorter clauses are padded by repeating a literal. -/
def tseitinClause (op : Op) (w a b : V) (j : Fin 3) : Clause V :=
  match op, j.val with
  | .const v, _ => [(w, v), (w, v), (w, v)]
  | .not, 1 => [(w, false), (a, false), (a, false)]
  | .not, _ => [(w, true), (a, true), (a, true)]
  | .and, 0 => [(w, false), (a, true), (a, true)]
  | .and, 1 => [(w, false), (b, true), (b, true)]
  | .and, _ => [(w, true), (a, false), (b, false)]
  | .or, 0 => [(w, true), (a, false), (a, false)]
  | .or, 1 => [(w, true), (b, false), (b, false)]
  | .or, _ => [(w, false), (a, true), (b, true)]

/-- Every clause of a gate has three literals. -/
@[simp] theorem length_tseitinClause (op : Op) (w a b : V) (j : Fin 3) :
    (tseitinClause op w a b j).length = 3 := by
  fin_cases j <;> cases op <;> rfl

/-- **The clauses of a gate hold** exactly when its output carries its value. -/
theorem forall_eval_tseitinClause_iff (op : Op) (w a b : V) (σ : V → Bool) :
    (∀ j, (tseitinClause op w a b j).eval σ = true) ↔ σ w = op.value (σ a) (σ b) := by
  have h₃ : (∀ j, (tseitinClause op w a b j).eval σ = true) ↔
      (tseitinClause op w a b 0).eval σ = true ∧ (tseitinClause op w a b 1).eval σ = true ∧
        (tseitinClause op w a b 2).eval σ = true :=
    ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h₀, h₁, h₂⟩ j => by fin_cases j <;> assumption⟩
  rw [h₃]
  rcases op with v | _ | _ | _ <;>
    simp only [tseitinClause, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
      Clause.eval_cons, Clause.eval_nil, Literal.eval_mk, Op.value] <;>
    cases σ w <;> cases σ a <;> cases σ b <;> (try cases v) <;> decide

/-- Relabelling the clauses of a gate relabels its variables. -/
@[simp] theorem relabel_tseitinClause {W : Type*} (f : V → W) (op : Op) (w a b : V) (j : Fin 3) :
    (tseitinClause op w a b j).relabel f = tseitinClause op (f w) (f a) (f b) j := by
  fin_cases j <;> cases op <;> rfl

/-! ### The Tseitin formula of a gate list -/

/-- The clauses of a gate code `gate` at the wire `w`, reading its first two listed arguments. -/
def gateClauses (w : ℕ) (gate : Op × List ℕ) : CNF ℕ :=
  List.ofFn (tseitinClause gate.1 w (gate.2.getD 0 0) (gate.2.getD 1 0))

/-- **The Tseitin formula of a De Morgan gate list** on `n` inputs: the clauses of gate `g` say
that wire `n + g` carries its value. -/
def tseitinCNF (n : ℕ) (gates : List (Op × List ℕ)) : CNF ℕ :=
  (List.finRange gates.length).flatMap fun g : Fin gates.length => gateClauses (n + g) gates[g]

/-- The clauses of a gate code hold exactly when its wire carries its value. -/
theorem eval_gateClauses_eq_true_iff (w : ℕ) (gate : Op × List ℕ) (σ : ℕ → Bool) :
    (gateClauses w gate).eval σ = true ↔
      σ w = gate.1.value (σ (gate.2.getD 0 0)) (σ (gate.2.getD 1 0)) := by
  rw [← forall_eval_tseitinClause_iff, gateClauses, CNF.eval_eq_true_iff]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]

/-- **An assignment satisfies the Tseitin formula** exactly when every gate wire carries the value
of its gate. -/
theorem eval_tseitinCNF_eq_true_iff (n : ℕ) (gates : List (Op × List ℕ)) (σ : ℕ → Bool) :
    (tseitinCNF n gates).eval σ = true ↔ ∀ g (hg : g < gates.length),
      σ (n + g) = gates[g].1.value (σ (gates[g].2.getD 0 0)) (σ (gates[g].2.getD 1 0)) := by
  simp only [tseitinCNF, CNF.eval_flatMap_eq_true_iff, List.mem_finRange, true_implies,
    eval_gateClauses_eq_true_iff]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.isLt⟩

/-- The listed arguments of a well-formed gate within its arity read earlier wires. -/
private theorem getD_lt_of_isCodeFrom {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) {g : ℕ} (hg : g < gates.length) :
    (1 ≤ signature.Arity gates[g].1 → gates[g].2.getD 0 0 < n + g) ∧
      (2 ≤ signature.Arity gates[g].1 → gates[g].2.getD 1 0 < n + g) := by
  obtain ⟨hlen, hlt⟩ := h.getElem g hg
  refine ⟨fun h₁ => ?_, fun h₂ => ?_⟩
  · have h₀ : 0 < gates[g].2.length := by omega
    rw [List.getD_eq_getElem _ _ h₀]
    simpa using hlt _ (List.getElem_mem h₀)
  · have h₀ : 1 < gates[g].2.length := by omega
    rw [List.getD_eq_getElem _ _ h₀]
    simpa using hlt _ (List.getElem_mem h₀)

/-- **The satisfying assignments of the Tseitin formula** of a well-formed gate list are its
evaluations: every wire carries the value that the list computes from the inputs. -/
theorem eval_tseitinCNF_eq_true_iff_evalCode {n : ℕ} {gates : List (Op × List ℕ)}
    (h : Program.IsCodeFrom signature n 0 gates) (σ : ℕ → Bool) :
    (tseitinCNF n gates).eval σ = true ↔ ∀ w < n + gates.length, σ w =
      (evalCode interpretation false (List.ofFn fun i : Fin n => σ i) gates).getD w false := by
  rw [eval_tseitinCNF_eq_true_iff]
  set x : List Bool := List.ofFn fun i : Fin n => σ i with hx
  have hxlen : x.length = n := by simp [hx]
  set vals := evalCode interpretation false x gates with hvals
  have hgate (g : ℕ) (hg : g < gates.length) : vals.getD (n + g) false =
      gates[g].1.value (vals.getD (gates[g].2.getD 0 0) false)
        (vals.getD (gates[g].2.getD 1 0) false) := by
    have := getD_evalCode interpretation false x (hxlen ▸ h) (List.getElem?_eq_getElem hg)
    rw [hxlen] at this
    rw [hvals, this, interpretation_eq_value _ (h.getElem g hg).1]
  have hin (w : ℕ) (hw : w < n) : vals.getD w false = σ w := by
    obtain ⟨r, hr⟩ := prefix_evalCode interpretation false x gates
    rw [hvals, ← hr, List.getD_append _ _ _ _ (by omega), hx, List.getD_eq_getElem _ _ (by simpa),
      List.getElem_ofFn]
  constructor
  · intro hσ w hw
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hwn : w < n
      · exact (hin w hwn).symm
      · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
        have hg : g < gates.length := by omega
        have hargs := getD_lt_of_isCodeFrom h hg
        rw [hσ g hg, hgate g hg]
        exact Op.value_congr _ (fun h₁ => ih _ (hargs.1 h₁) (by omega))
          (fun h₂ => ih _ (hargs.2 h₂) (by omega))
  · intro hσ g hg
    have hargs := getD_lt_of_isCodeFrom h hg
    rw [hσ (n + g) (by omega), hgate g hg]
    exact Op.value_congr _ (fun h₁ => (hσ _ (by have := hargs.1 h₁; omega)).symm)
      (fun h₂ => (hσ _ (by have := hargs.2 h₂; omega)).symm)

/-! ### Satisfiability with a fixed input prefix -/

/-- The unit clause of a literal, padded to three literals. -/
def unitClause (l : Literal V) : Clause V := [l, l, l]

/-- The unit clause of a literal holds when the literal does. -/
@[simp] theorem eval_unitClause (σ : V → Bool) (l : Literal V) :
    (unitClause l).eval σ = l.eval σ := by
  simp [unitClause]

/-- **Circuit satisfiability with a fixed input prefix**, as a formula: unit clauses fix the wire
`o` to `true` and the inputs `i < x.length` to `x[i]`, and the Tseitin clauses of `gates` follow. -/
def tseitinSatCNF (x : List Bool) (n : ℕ) (gates : List (Op × List ℕ)) (o : ℕ) : CNF ℕ :=
  unitClause (o, true) :: (x.mapIdx fun i b => unitClause (i, b)) ++ tseitinCNF n gates

/-- The unit clauses fixing the inputs `i < x.length` to `x[i]`. -/
theorem eval_mapIdx_unitClause_eq_true_iff (x : List Bool) (σ : ℕ → Bool) :
    CNF.eval σ (x.mapIdx fun i b => unitClause (i, b)) = true ↔
      ∀ i (hi : i < x.length), σ i = x[i] := by
  rw [CNF.eval_eq_true_iff]
  simp only [List.mem_mapIdx, forall_exists_index]
  constructor
  · intro h i hi
    simpa using h _ i hi rfl
  · rintro h c i hi rfl
    simpa using h i hi

/-- An assignment satisfies `tseitinSatCNF` when it makes wire `o` true, agrees with `x` on the
first inputs and satisfies the Tseitin formula. -/
theorem eval_tseitinSatCNF_eq_true_iff (x : List Bool) (n : ℕ) (gates : List (Op × List ℕ))
    (o : ℕ) (σ : ℕ → Bool) :
    (tseitinSatCNF x n gates o).eval σ = true ↔
      σ o = true ∧ (∀ i (hi : i < x.length), σ i = x[i]) ∧ (tseitinCNF n gates).eval σ = true := by
  simp only [tseitinSatCNF, List.cons_append, CNF.eval_cons, CNF.eval_append, Bool.and_eq_true,
    eval_unitClause, Literal.eval_eq_true_iff, eval_mapIdx_unitClause_eq_true_iff]

/-- **Satisfiability with a fixed input prefix**: for a well-formed gate list on `n` inputs and a
wire `o` of it, `tseitinSatCNF x n gates o` is satisfiable exactly when some input of length `n`
extending `x` makes wire `o` true. -/
theorem satisfiable_tseitinSatCNF_iff {x : List Bool} {n : ℕ} {gates : List (Op × List ℕ)}
    {o : ℕ} (h : Program.IsCodeFrom signature n 0 gates) (hx : x.length ≤ n)
    (ho : o < n + gates.length) :
    (tseitinSatCNF x n gates o).Satisfiable ↔
      ∃ y : List Bool, y.length = n ∧ x <+: y ∧ evalOutput y gates o = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨hσo, hσx, hσφ⟩ := (eval_tseitinSatCNF_eq_true_iff x n gates o σ).1 hσ
    have hval := (eval_tseitinCNF_eq_true_iff_evalCode h σ).1 hσφ
    refine ⟨List.ofFn fun i : Fin n => σ i, by simp, ?_, ?_⟩
    · rw [List.prefix_iff_eq_take]
      refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
      simpa using (hσx i h₁).symm
    · rw [evalOutput, ← hval o ho, hσo]
  · rintro ⟨y, hy, hxy, hout⟩
    set σ : ℕ → Bool := fun w => (evalCode interpretation false y gates).getD w false with hσ
    have hσy (i : ℕ) (hi : i < n) : σ i = y[i]'(by omega) := by
      obtain ⟨r, hr⟩ := prefix_evalCode interpretation false y gates
      change (evalCode interpretation false y gates).getD i false = _
      rw [← hr, List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem]
    have hyσ : (List.ofFn fun i : Fin n => σ i) = y :=
      List.ext_getElem (by simp [hy]) fun i h₁ h₂ => by simp [hσy i (by simpa using h₁)]
    refine ⟨σ, (eval_tseitinSatCNF_eq_true_iff x n gates o σ).2 ⟨hout, fun i hi => ?_, ?_⟩⟩
    · rw [hσy i (by omega), hxy.getElem hi]
    · rw [eval_tseitinCNF_eq_true_iff_evalCode h, hyσ]
      exact fun _ _ => rfl

/-- **Circuit satisfiability as a formula**: the Tseitin formula of a single-output De Morgan
circuit, with the output fixed to `true` and the inputs fixed to the bits of `x`, is satisfiable
exactly when some input extending `x` makes the circuit output `true`. -/
theorem satisfiable_tseitinSatCNF_circuit_iff {n : ℕ} (c : Circuit signature n 1)
    {x : List Bool} (hx : x.length ≤ n) :
    (tseitinSatCNF x n c.code.1 (c.outputs 0).toNat).Satisfiable ↔
      ∃ y : BitString n, x <+: List.ofFn y ∧ c.eval interpretation y 0 = true := by
  have hcode := (Circuit.isSome_ofCode_iff (n := n) (m := 1) (code := c.code)).1
    (by simp [Circuit.ofCode_code])
  rw [satisfiable_tseitinSatCNF_iff hcode.1 hx
    (by simpa using hcode.2.2 _ (by simp [Circuit.code]))]
  constructor
  · rintro ⟨y, hy, hxy, hout⟩
    refine ⟨fun i => y[i.val]'(by omega), ?_, ?_⟩
    · have : (List.ofFn fun i : Fin n => y[i.val]'(by omega)) = y :=
        List.ext_getElem (by simp [hy]) fun i _ _ => by simp
      rwa [this]
    · rw [Circuit.eval_eq_evalOutput]
      have : (List.ofFn fun i : Fin n => y[i.val]'(by omega)) = y :=
        List.ext_getElem (by simp [hy]) fun i _ _ => by simp
      rwa [this]
  · rintro ⟨y, hxy, hout⟩
    exact ⟨List.ofFn y, by simp, hxy, by rwa [← Circuit.eval_eq_evalOutput]⟩

/-! ### Size -/

/-- **Every clause of `tseitinSatCNF` has exactly three literals.** -/
theorem length_of_mem_tseitinSatCNF {x : List Bool} {n : ℕ} {gates : List (Op × List ℕ)} {o : ℕ}
    {C : Clause ℕ} (hC : C ∈ tseitinSatCNF x n gates o) : C.length = 3 := by
  simp only [tseitinSatCNF, List.cons_append, List.mem_cons, List.mem_append, List.mem_mapIdx,
    tseitinCNF, List.mem_flatMap, gateClauses, List.mem_ofFn] at hC
  rcases hC with rfl | ⟨i, -, rfl⟩ | ⟨g, -, j, rfl⟩
  · rfl
  · rfl
  · exact length_tseitinClause _ _ _ _ _

/-- `tseitinSatCNF` has one clause for the output, one for each fixed input and three for each
gate. -/
theorem length_tseitinSatCNF (x : List Bool) (n : ℕ) (gates : List (Op × List ℕ)) (o : ℕ) :
    (tseitinSatCNF x n gates o).length = 1 + x.length + 3 * gates.length := by
  simp only [tseitinSatCNF, tseitinCNF, gateClauses, List.cons_append, List.length_cons,
    List.length_append, List.length_mapIdx, List.length_flatMap, List.length_ofFn,
    List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]
  omega

end Cslib.Circuits.Boolean
