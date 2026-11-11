/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.Boolean.Oracle

/-!
# Oracle formulas and local formula classes

An *oracle formula* is a formula over the De Morgan basis with oracle gates
(`Cslib.Circuits.Boolean.oracleSignature`). Under the oracle `O`, a gate with `q` arguments answers
whether the word formed by its arguments is in `O` (`oracleInterpretation O`).

Chen, Hirahara, Oliveira, Pich, Rajgopal and Santhanam measure the oracle gates of such a device in
three ways [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.5, Definition 11, p. 13]:
- their *quantity*, the number of oracle gates (`OracleFormula.queryCount`);
- their *locality*, the largest fan-in of an oracle gate (`OracleFormula.maxQueryArity`);
- their *adaptivity*, the largest number of oracle gates on a path from an input to the output
  (`OracleFormula.adaptivity`).
`LocalFormulaClass q ℓ a S Yes No` is their class `[q, ℓ, a]–Formula[S]` for the promise problem
with yes-instances `Yes` and no-instances `No`. A single oracle language serves every input length,
and at each length `m` some formula of at most `S m` leaves, with at most `q m` oracle gates of
fan-in at most `ℓ m` and at most `a m` oracle gates on any path, accepts the yes-instances and
rejects the no-instances of length `m`.

`OracleFormula.query fs` is the oracle gate whose arguments are the De Morgan formulas `fs`, and
`OracleFormula.all` is the conjunction of a list of oracle formulas. These are the shapes that
hardness magnification produces: oracle gates applied to cheap projections of the input, combined
by a formula.

## Main definitions

* `Cslib.Circuits.Boolean.OracleFormula`: formulas with oracle gates.
* `Cslib.Circuits.Boolean.OracleFormula.queryCount`, `OracleFormula.maxQueryArity`,
  `OracleFormula.adaptivity`: the quantity, locality and adaptivity of the oracle gates.
* `Cslib.Circuits.Boolean.OracleFormula.query`, `OracleFormula.and`, `OracleFormula.all`: an
  oracle gate on De Morgan formulas, and conjunctions.
* `Cslib.Circuits.Boolean.LocalFormulaClass`: the local formula classes `[q, ℓ, a]–Formula[S]`.

## Main results

* `Cslib.Circuits.Boolean.OracleFormula.queryCount_mapOp_toOracle` and its companions: a De Morgan
  formula has no oracle gates.
* `Cslib.Circuits.Boolean.OracleFormula.eval_query_eq_true_iff`, `OracleFormula.eval_all`: the
  semantics of oracle gates on De Morgan formulas and of conjunctions, with the measures of both.
* `Cslib.Circuits.Boolean.LocalFormulaClass.mono`, `LocalFormulaClass.anti`: the classes grow with
  their parameters and shrink with their promise sets.

## References

* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal, R. Santhanam, *Beyond Natural
  Proofs: Hardness Magnification and Locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.Circuits.Boolean

/-- Formulas over the De Morgan basis with oracle gates. -/
abbrev OracleFormula (n : ℕ) : Type := Formula oracleSignature n

namespace OracleFormula

variable {n : ℕ}

/-- The quantity of the oracle gates: their number. -/
def queryCount (F : OracleFormula n) : ℕ :=
  F.cost OracleOp.queryWeight

/-- The adaptivity of the oracle gates: the largest number of oracle gates on a path from a leaf to
the root. -/
def adaptivity (F : OracleFormula n) : ℕ :=
  F.depthWith OracleOp.queryWeight

/-- The locality of the oracle gates: the largest fan-in of an oracle gate, or zero when there is
none. -/
def maxQueryArity : OracleFormula n → ℕ
  | .input _ => 0
  | .gate op args => max op.queryArity (Finset.univ.sup fun j => maxQueryArity (args j))

@[simp] theorem queryCount_input (i : Fin n) : queryCount (.input i : OracleFormula n) = 0 := by
  simp only [queryCount, Formula.cost]

@[simp] theorem queryCount_gate (op : OracleOp) (args : Fin (oracleSignature.Arity op) →
    OracleFormula n) :
    queryCount (.gate op args : OracleFormula n) = (∑ j, queryCount (args j)) + op.queryWeight := by
  simp only [queryCount, Formula.cost]

@[simp] theorem adaptivity_input (i : Fin n) : adaptivity (.input i : OracleFormula n) = 0 := by
  simp only [adaptivity, Formula.depthWith_input]

@[simp] theorem adaptivity_gate (op : OracleOp) (args : Fin (oracleSignature.Arity op) →
    OracleFormula n) :
    adaptivity (.gate op args : OracleFormula n) =
      (Finset.univ.sup fun j => adaptivity (args j)) + op.queryWeight := by
  simp only [adaptivity, Formula.depthWith_gate]

@[simp] theorem maxQueryArity_input (i : Fin n) :
    maxQueryArity (.input i : OracleFormula n) = 0 := by
  simp only [maxQueryArity]

@[simp] theorem maxQueryArity_gate (op : OracleOp) (args : Fin (oracleSignature.Arity op) →
    OracleFormula n) :
    maxQueryArity (.gate op args : OracleFormula n) =
      max op.queryArity (Finset.univ.sup fun j => maxQueryArity (args j)) := by
  simp only [maxQueryArity]

/-! ### De Morgan formulas have no oracle gates -/

@[simp] theorem queryCount_mapOp_toOracle (F : Formula signature n) :
    queryCount (F.mapOp toOracle) = 0 := by
  induction F with
  | input i => simp
  | gate op args ih =>
    rw [Formula.mapOp_gate, queryCount_gate]
    simp only [toOracle, DFunLike.coe, OracleOp.queryWeight_base, add_zero]
    exact Finset.sum_eq_zero fun j _ => ih _

@[simp] theorem adaptivity_mapOp_toOracle (F : Formula signature n) :
    adaptivity (F.mapOp toOracle) = 0 := by
  induction F with
  | input i => simp
  | gate op args ih =>
    rw [Formula.mapOp_gate, adaptivity_gate]
    simp only [toOracle, DFunLike.coe, OracleOp.queryWeight_base, add_zero]
    exact le_antisymm (Finset.sup_le fun j _ => (ih _).le) (Nat.zero_le _)

@[simp] theorem maxQueryArity_mapOp_toOracle (F : Formula signature n) :
    maxQueryArity (F.mapOp toOracle) = 0 := by
  induction F with
  | input i => simp
  | gate op args ih =>
    rw [Formula.mapOp_gate, maxQueryArity_gate]
    simp only [toOracle, DFunLike.coe, OracleOp.queryArity_base, zero_max]
    exact le_antisymm (Finset.sup_le fun j _ => (ih _).le) (Nat.zero_le _)

/-! ### Oracle gates on De Morgan formulas -/

/-- The oracle gate whose arguments are the De Morgan formulas `fs`, in order. -/
def query (fs : List (Formula signature n)) : OracleFormula n :=
  .gate (.query fs.length) fun i : Fin fs.length => fs[i].mapOp toOracle

/-- Under the oracle `O`, the oracle gate on `fs` answers whether the word of values of `fs` is in
`O`. -/
@[simp] theorem eval_query_eq_true_iff {O : Language Bool} {fs : List (Formula signature n)}
    {x : Fin n → Bool} :
    (query fs).eval (oracleInterpretation O) x = true ↔ fs.map (·.eval interpretation x) ∈ O := by
  simp only [query, Formula.eval_gate, oracleInterpretation_query, Language.slice_eq_true_iff]
  have h : (List.ofFn fun i : Fin fs.length =>
      (fs[i].mapOp toOracle).eval (oracleInterpretation O) x) =
        fs.map (·.eval interpretation x) := by
    refine List.ext_getElem (by simp) fun i _ _ => ?_
    simp only [List.getElem_ofFn, List.getElem_map]
    exact Formula.eval_mapOp (I := interpretation) _ x
  rw [h]

@[simp] theorem queryCount_query (fs : List (Formula signature n)) :
    queryCount (query fs) = 1 := by
  simp [query]

@[simp] theorem adaptivity_query (fs : List (Formula signature n)) :
    adaptivity (query fs) = 1 := by
  simp [query]

@[simp] theorem maxQueryArity_query (fs : List (Formula signature n)) :
    maxQueryArity (query fs) = fs.length := by
  simp [query]

/-- The leaves of an oracle gate are those of its arguments. -/
@[simp] theorem leafSize_query (fs : List (Formula signature n)) :
    (query fs).leafSize = (fs.map Formula.leafSize).sum := by
  simp only [query, Formula.leafSize_gate, Formula.leafSize_mapOp]
  exact Fin.sum_univ_fun_getElem fs Formula.leafSize

/-- An oracle gate on formulas of at most one leaf each has at most as many leaves as
arguments. -/
theorem leafSize_query_le {fs : List (Formula signature n)} (hfs : ∀ F ∈ fs, F.leafSize ≤ 1) :
    (query fs).leafSize ≤ fs.length := by
  rw [leafSize_query]
  refine (List.sum_le_length_nsmul _ 1 ?_).trans (by simp)
  simpa using hfs

/-! ### Conjunctions -/

/-- The constant true. -/
def tt : OracleFormula n :=
  .gate (.base (.const true)) Fin.elim0

/-- The conjunction of two oracle formulas. -/
def and (F G : OracleFormula n) : OracleFormula n :=
  Formula.gate₂ (.base .and) rfl F G

/-- The conjunction of a list of oracle formulas. -/
def all : List (OracleFormula n) → OracleFormula n
  | [] => tt
  | F :: Fs => and F (all Fs)

@[simp] theorem eval_tt (O : Language Bool) (x : Fin n → Bool) :
    (tt : OracleFormula n).eval (oracleInterpretation O) x = true := by
  simp only [tt, Formula.eval_gate, oracleInterpretation_base, interpretation]

@[simp] theorem eval_and (O : Language Bool) (F G : OracleFormula n) (x : Fin n → Bool) :
    (and F G).eval (oracleInterpretation O) x =
      (F.eval (oracleInterpretation O) x && G.eval (oracleInterpretation O) x) := by
  simp only [and, Formula.eval_gate₂, oracleInterpretation_base, interpretation]; rfl

@[simp] theorem queryCount_tt : queryCount (tt : OracleFormula n) = 0 := by
  simp [tt]

@[simp] theorem adaptivity_tt : adaptivity (tt : OracleFormula n) = 0 := by
  simp [tt]

@[simp] theorem maxQueryArity_tt : maxQueryArity (tt : OracleFormula n) = 0 := by
  simp [tt]

@[simp] theorem leafSize_tt : (tt : OracleFormula n).leafSize = 0 := by
  simp [tt]

@[simp] theorem queryCount_and (F G : OracleFormula n) :
    queryCount (and F G) = queryCount F + queryCount G := by
  simp only [and, queryCount, Formula.cost_gate₂, OracleOp.queryWeight_base, add_zero]

@[simp] theorem adaptivity_and (F G : OracleFormula n) :
    adaptivity (and F G) = max (adaptivity F) (adaptivity G) := by
  simp only [and, adaptivity, Formula.depthWith_gate₂, OracleOp.queryWeight_base, add_zero]

@[simp] theorem maxQueryArity_and (F G : OracleFormula n) :
    maxQueryArity (and F G) = max (maxQueryArity F) (maxQueryArity G) := by
  simp [and, Formula.gate₂, Fin.univ_succ]

@[simp] theorem leafSize_and (F G : OracleFormula n) :
    (and F G).leafSize = F.leafSize + G.leafSize :=
  Formula.leafSize_gate₂ F G

/-- The conjunction of `Fs` is true exactly when every formula of `Fs` is. -/
@[simp] theorem eval_all (O : Language Bool) (Fs : List (OracleFormula n)) (x : Fin n → Bool) :
    (all Fs).eval (oracleInterpretation O) x =
      decide (∀ F ∈ Fs, F.eval (oracleInterpretation O) x = true) := by
  induction Fs with
  | nil => simp [all]
  | cons F Fs ih => simp [all, ih]

@[simp] theorem queryCount_all (Fs : List (OracleFormula n)) :
    queryCount (all Fs) = (Fs.map queryCount).sum := by
  induction Fs with
  | nil => simp [all]
  | cons F Fs ih => simp [all, ih]

@[simp] theorem leafSize_all (Fs : List (OracleFormula n)) :
    (all Fs).leafSize = (Fs.map Formula.leafSize).sum := by
  induction Fs with
  | nil => simp [all]
  | cons F Fs ih => simp [all, ih]

/-- A conjunction adds no oracle gate to any path. -/
theorem adaptivity_all_le {a : ℕ} {Fs : List (OracleFormula n)} (h : ∀ F ∈ Fs, adaptivity F ≤ a) :
    adaptivity (all Fs) ≤ a := by
  induction Fs with
  | nil => simp [all]
  | cons F Fs ih =>
    simp only [all, adaptivity_and, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact max_le h.1 (ih h.2)

/-- A conjunction adds no oracle gate. -/
theorem maxQueryArity_all_le {ℓ : ℕ} {Fs : List (OracleFormula n)}
    (h : ∀ F ∈ Fs, maxQueryArity F ≤ ℓ) : maxQueryArity (all Fs) ≤ ℓ := by
  induction Fs with
  | nil => simp [all]
  | cons F Fs ih =>
    simp only [all, maxQueryArity_and, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact max_le h.1 (ih h.2)

end OracleFormula

/-- **Local formula classes** [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.5,
Definition 11, p. 13], for formulas and promise problems: the promise problem with yes-instances
`Yes` and no-instances `No` is in `[q, ℓ, a]–Formula[S]` when there is one oracle language `O` such
that, for every input length `m`, some oracle formula on `m` inputs with
- at most `S m` leaves,
- at most `q m` oracle gates (quantity), each of fan-in at most `ℓ m` (locality),
- at most `a m` oracle gates on any path from a leaf to the root (adaptivity),
answers `true` on the yes-instances and `false` on the no-instances of length `m` under `O`.

Only input leaves count towards `S m`: constant leaves are free here, while the source's
`Formula[s]` counts constant leaves too [ChenHiraharaOliveiraPichRajgopalSanthanam2020, Section 2.1,
p. 12], so for a fixed `S` this class can be larger than the source's. Paths ending at constants
count towards the adaptivity, so the adaptivity here is at least the source's, which counts only
paths from inputs. -/
@[expose] def LocalFormulaClass (q ℓ a S : ℕ → ℕ) (Yes No : Language Bool) : Prop :=
  ∃ O : Language Bool, ∀ m, ∃ E : OracleFormula m,
    E.leafSize ≤ S m ∧ OracleFormula.queryCount E ≤ q m ∧ OracleFormula.maxQueryArity E ≤ ℓ m ∧
      OracleFormula.adaptivity E ≤ a m ∧
      (∀ x : Fin m → Bool, List.ofFn x ∈ Yes → E.eval (oracleInterpretation O) x = true) ∧
      (∀ x : Fin m → Bool, List.ofFn x ∈ No → E.eval (oracleInterpretation O) x = false)

/-- The local formula classes grow with their parameters. -/
theorem LocalFormulaClass.mono {q ℓ a S q' ℓ' a' S' : ℕ → ℕ} {Yes No : Language Bool}
    (h : LocalFormulaClass q ℓ a S Yes No) (hq : q ≤ q') (hℓ : ℓ ≤ ℓ') (ha : a ≤ a')
    (hS : S ≤ S') : LocalFormulaClass q' ℓ' a' S' Yes No := by
  obtain ⟨O, hO⟩ := h
  refine ⟨O, fun m => ?_⟩
  obtain ⟨E, hS', hq', hℓ', ha', hyes, hno⟩ := hO m
  exact ⟨E, hS'.trans (hS m), hq'.trans (hq m), hℓ'.trans (hℓ m), ha'.trans (ha m), hyes, hno⟩

/-- Shrinking the yes- and no-instances keeps a promise problem in a local formula class. -/
theorem LocalFormulaClass.anti {q ℓ a S : ℕ → ℕ} {Yes No Yes' No' : Language Bool}
    (h : LocalFormulaClass q ℓ a S Yes No) (hY : Yes' ≤ Yes) (hN : No' ≤ No) :
    LocalFormulaClass q ℓ a S Yes' No' := by
  obtain ⟨O, hO⟩ := h
  refine ⟨O, fun m => ?_⟩
  obtain ⟨E, hS, hq, hℓ, ha, hyes, hno⟩ := hO m
  exact ⟨E, hS, hq, hℓ, ha, fun x hx => hyes x (hY hx), fun x hx => hno x (hN hx)⟩

end Cslib.Circuits.Boolean
