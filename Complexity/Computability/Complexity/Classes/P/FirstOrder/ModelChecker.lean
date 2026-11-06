/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.LeastFixedPoint
public import Complexity.Logics.FirstOrder.Ordered.Query
public import Complexity.Logics.FirstOrder.Encoding

/-!
# A finite model checker for ordered FO(LFP)

The formula is fixed while the finite input structure varies. Each least fixed point is computed
by iterating its body `n ^ k` times on a truth table, where `n` is the universe size and `k` is
the relation arity. Outer assignments and relation tables remain fixed throughout the iteration.
Nested fixed points use the same evaluator recursively.

The evaluator is defined on raw syntax and all encoded inputs. Its agreement with least-fixed-point
semantics requires the formula's formation certificate and a universe of size at least two, as
in the library's canonical ordered structures. Malformed input tables are dealt with separately
by the final decision procedure.

## Main results

* `Cslib.Logic.FO.LFP.ModelChecker.eval_eq_true_iff`: bounded evaluation agrees with realization
  of every well-formed formula, including nested fixed points and captured parameters.
* `Cslib.Logic.FO.LFP.ModelChecker.getD_tableOf`: tabulation uses the same tuple numbering as
  encoded input relations.

## References

* [N. Immerman, *Relational queries computable in polynomial time*][Immerman1986],
  Section 2, Fact 2.1, for the finite iteration bound.
-/

public section

universe u v w

open FirstOrder Language

namespace Cslib.Logic.FO.LFP.ModelChecker

variable {L : Language.{u, v}} [L.IsRelational]

/-- The index of a scoped relation variable in the stack of truth tables. -/
@[expose] def relIndex {Γ : List ℕ} {k : ℕ} : Operator.RelVar Γ k → ℕ
  | .here => 0
  | .there r => relIndex r + 1

/-- A term's numerical value. Input vocabularies are relational; numeric functions are constants. -/
@[expose] def termValue {α : Type w} (n : ℕ) (σ : α → ℕ) :
    (Ordered.language L).Term α → ℕ
  | .var x => σ x
  | .func (.inl f) _ => isEmptyElim f
  | .func (.inr c) _ => c.index n

/-- The colexicographic truth-table index of a tuple of natural-number coordinates. -/
@[expose] def valuesIndex (n : ℕ) : {k : ℕ} → (Fin k → ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, xs => xs 0 + n * valuesIndex n (fun j => xs j.succ)

/-- Input atoms read the supplied tables; order and BIT are computed from natural indices. -/
@[expose] def relBit (v : Vocabulary L) (a : EncodedStructure) {k : ℕ}
    (r : (Ordered.language L).Relations k) (xs : Fin k → ℕ) : Bool :=
  match r with
  | .inl r => (v.table a ⟨_, r⟩).getD (valuesIndex a.1 xs) false
  | .inr .le => decide (xs 0 ≤ xs 1)
  | .inr .bit => (xs 0).testBit (xs 1)

/-- Evaluate an ordinary bounded formula with separate free and bound assignments. -/
@[expose] def foEval (v : Vocabulary L) (a : EncodedStructure) {α : Type w} (σ : α → ℕ) :
    {k : ℕ} → (Ordered.language L).BoundedFormula α k → (Fin k → ℕ) → Bool
  | _, .falsum, _ => false
  | _, .equal s t, xs =>
    termValue a.1 (Sum.elim σ xs) s == termValue a.1 (Sum.elim σ xs) t
  | _, .rel r ts, xs =>
    relBit v a r (fun j => termValue a.1 (Sum.elim σ xs) (ts j))
  | _, .imp φ ψ, xs => !foEval v a σ φ xs || foEval v a σ ψ xs
  | _, .all φ, xs => (List.range a.1).all (fun x => foEval v a σ φ (Fin.snoc xs x))

/-- Tabulate a Boolean predicate over all tuples, with coordinate zero the least significant. -/
@[expose] def tableOf (n k : ℕ) (f : (Fin k → ℕ) → Bool) : List Bool :=
  (List.range (n ^ k)).map (fun i => f (fun j => i / n ^ (j : ℕ) % n))

/-- A raw FO(LFP) evaluator. Bounded iteration gives a total algorithm even for invalid syntax. -/
@[expose] def eval (v : Vocabulary L) : {Γ : List ℕ} → {α : Type w} →
    RawFormula (Ordered.language L) Γ α → EncodedStructure → List (List Bool) → (α → ℕ) → Bool
  | _, _, .ofFO φ, a, _, σ => foEval v a σ φ Fin.elim0
  | _, _, .rel r ts, a, tables, σ =>
    (tables.getD (relIndex r) []).getD
      (valuesIndex a.1 (fun j => termValue a.1 σ (ts j))) false
  | _, _, .neg φ, a, tables, σ => !eval v φ a tables σ
  | _, _, .conj φ ψ, a, tables, σ => eval v φ a tables σ && eval v ψ a tables σ
  | _, _, .ex φ, a, tables, σ =>
    (List.range a.1).any (fun x => eval v φ a tables (Option.elim · x σ))
  | _, _, .op k body ts, a, tables, σ =>
    let step := fun table : List Bool =>
      tableOf a.1 k (fun xs => eval v (body 0) a (table :: tables) (Sum.elim σ xs))
    ((step^[a.1 ^ k]) []).getD
      (valuesIndex a.1 (fun j => termValue a.1 σ (ts j))) false

/-- Read one relation table using the standard tuple numbering. -/
@[expose] def tableRelation (n k : ℕ) (table : List Bool) : Set (Fin k → Fin n) :=
  {xs | table.getD (tupleIndex xs) false = true}

/-- Interpret a stack of relation tables at the arities of a scoped context. -/
@[expose] def relations (Γ : List ℕ) (n : ℕ) (tables : List (List Bool)) :
    Operator.RelEnv Γ (Fin n) :=
  fun {k} r => tableRelation n k (tables.getD (relIndex r) [])

/-- An empty table denotes the empty relation, including nullary relations. -/
@[simp] theorem tableRelation_nil (n k : ℕ) : tableRelation n k [] = ∅ := by
  ext xs
  simp [tableRelation]

/-- Extending the table stack agrees with the typed relation binder. -/
theorem relations_cons (Γ : List ℕ) (n k : ℕ) (table : List Bool) (tables : List (List Bool)) :
    @relations (k :: Γ) n (table :: tables) =
      @Operator.RelEnv.cons Γ (Fin n) k (tableRelation n k table) (@relations Γ n tables) := by
  funext l r
  cases r with
  | here => rfl
  | there r => simp [relations, relIndex, Operator.RelEnv.cons]

/-- A tabulation always has exactly one bit per tuple, including for arity zero. -/
@[simp] theorem length_tableOf (n k : ℕ) (f : (Fin k → ℕ) → Bool) :
    (tableOf n k f).length = n ^ k := by
  simp [tableOf]

/-- Reading a tabulated predicate recovers its value on the given tuple. -/
theorem getD_tableOf {n k : ℕ} (f : (Fin k → ℕ) → Bool) (xs : Fin k → Fin n) :
    (tableOf n k f).getD (tupleIndex xs) false = f (fun j => (xs j : ℕ)) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [length_tableOf] using tupleIndex_lt xs)]
  simp only [tableOf, List.getElem_map, List.getElem_range]
  congr 1
  funext j
  simpa only [tupleIndex, Equiv.symm_apply_apply] using
    (finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv xs) j).symm

/-- Natural coordinates give the standard truth-table index. -/
theorem valuesIndex_val {n k : ℕ} (xs : Fin k → Fin n) :
    valuesIndex n (fun j => (xs j : ℕ)) = tupleIndex xs := by
  induction k with
  | zero => simp [valuesIndex, tupleIndex_apply]
  | succ k ih =>
    rw [valuesIndex, ih, tupleIndex_apply, tupleIndex_apply, Fin.sum_univ_succ,
      Fin.val_zero, pow_zero, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.val_succ, pow_succ]
    ring

section Correctness

variable (v : Vocabulary L) {a : EncodedStructure}
  [L.Structure (Fin a.1)] [Fact (2 ≤ a.1)]
  (hinput : ∀ {k} (r : L.Relations k) (xs : Fin k → Fin a.1),
    (v.table a ⟨k, r⟩).getD (tupleIndex xs) false = true ↔ Language.Structure.RelMap r xs)

/-- Ordered term evaluation agrees with native Mathlib realization. -/
private theorem termValue_eq {α : Type w} (σ : α → Fin a.1) (t : (Ordered.language L).Term α) :
    termValue a.1 (fun x => (σ x : ℕ)) t = Fin.val (t.realize σ) := by
  cases t with
  | var x => rfl
  | func f ts =>
    cases f with
    | inl f => exact isEmptyElim f
    | inr c => rfl

include hinput

omit [L.IsRelational] in
/-- Atoms read exactly the decoded input relations and canonical numeric relations. -/
private theorem relBit_eq_true_iff {k : ℕ} (r : (Ordered.language L).Relations k)
    (xs : Fin k → Fin a.1) :
    relBit v a r (fun j => (xs j : ℕ)) = true ↔ Language.Structure.RelMap r xs := by
  cases r with
  | inl r =>
    change (v.table a ⟨k, r⟩).getD (valuesIndex a.1 (fun j => (xs j : ℕ))) false = true ↔
      Language.Structure.RelMap r xs
    rw [valuesIndex_val]
    exact hinput r xs
  | inr r =>
    cases r with
    | le => change decide ((xs 0).val ≤ (xs 1).val) = true ↔ xs 0 ≤ xs 1; simp
    | bit => rfl

/-- The first-order evaluator decides Mathlib's bounded-formula semantics. -/
private theorem foEval_eq_true_iff {α : Type w} (σ : α → Fin a.1) {k : ℕ}
    (φ : (Ordered.language L).BoundedFormula α k) (xs : Fin k → Fin a.1) :
    foEval v a (fun x => (σ x : ℕ)) φ (fun j => (xs j : ℕ)) = true ↔
      φ.Realize σ xs := by
  induction φ with
  | falsum => simp [foEval, BoundedFormula.Realize]
  | equal s t =>
    have hσ : Sum.elim (fun x => (σ x : ℕ)) (fun j => (xs j : ℕ)) =
        fun x => Fin.val (Sum.elim σ xs x) := by funext x; cases x <;> rfl
    simp only [foEval, hσ, termValue_eq, beq_iff_eq, Fin.val_inj,
      BoundedFormula.Realize]
  | rel r ts =>
    have hσ : Sum.elim (fun x => (σ x : ℕ)) (fun j => (xs j : ℕ)) =
        fun x => Fin.val (Sum.elim σ xs x) := by funext x; cases x <;> rfl
    simp only [foEval, hσ, termValue_eq, relBit_eq_true_iff v hinput,
      BoundedFormula.Realize]
  | imp φ ψ ihφ ihψ =>
    simp only [foEval, Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, ihφ, ihψ,
      BoundedFormula.realize_imp]
    tauto
  | all φ ih =>
    simp only [foEval, List.all_eq_true, List.mem_range, BoundedFormula.realize_all]
    constructor
    · intro h x
      apply (ih (Fin.snoc xs x)).mp
      convert h x x.isLt using 1
      congr 1
      funext i
      exact (Fin.lastCases (by simp) (fun j => by simp) i)
    · intro h x hx
      have := (ih (Fin.snoc xs ⟨x, hx⟩)).mpr (h ⟨x, hx⟩)
      convert this using 1
      congr 1
      funext i
      exact (Fin.lastCases (by simp) (fun j => by simp) i)

/-- The bounded evaluator agrees with the semantics of every well-formed, possibly nested LFP
formula. Relation variables are interpreted by the supplied truth-table stack. -/
private theorem eval_correct {Γ : List ℕ} {α : Type w}
    (φ : RawFormula (Ordered.language L) Γ α) (hφ : φ.wellFormed policy = true)
    (tables : List (List Bool)) (σ : α → Fin a.1) :
    eval v φ a tables (fun x => (σ x : ℕ)) = true ↔
      φ.Realize interpretation (relations Γ a.1 tables) σ := by
  induction φ generalizing tables with
  | ofFO φ =>
    have h := foEval_eq_true_iff v hinput σ φ Fin.elim0
    have hzero : (fun j : Fin 0 => (Fin.elim0 j : Fin a.1).val) = Fin.elim0 :=
      Subsingleton.elim _ _
    have hdefault : (default : Fin 0 → Fin a.1) = Fin.elim0 := Subsingleton.elim _ _
    simpa only [eval, Operator.Formula.realize_ofFO, FirstOrder.Language.Formula.Realize,
      hzero, hdefault] using h
  | rel r ts =>
    simp only [eval, termValue_eq, valuesIndex_val, Operator.Formula.realize_rel,
      relations, tableRelation, Set.mem_ofPred_eq]
  | neg φ ih =>
    simpa only [eval, Bool.not_eq_true', ← Bool.not_eq_true, Operator.Formula.realize_neg]
      using not_congr (ih hφ tables σ)
  | conj φ ψ ihφ ihψ =>
    have ⟨hφ, hψ⟩ : φ.wellFormed policy = true ∧ ψ.wellFormed policy = true := by
      simpa only [Operator.Formula.wellFormed, Bool.and_eq_true] using hφ
    simpa only [eval, Bool.and_eq_true, Operator.Formula.realize_conj] using
      and_congr (ihφ hφ tables σ) (ihψ hψ tables σ)
  | ex φ ih =>
    simp only [eval, List.any_eq_true, List.mem_range, Operator.Formula.realize_ex]
    constructor
    · rintro ⟨x, hx, heval⟩
      refine ⟨⟨x, hx⟩, (ih hφ tables (Option.elim · ⟨x, hx⟩ σ)).mp ?_⟩
      convert heval using 1
      congr 1
      funext y
      cases y <;> rfl
    · rintro ⟨x, hx⟩
      refine ⟨x, x.isLt, ?_⟩
      have := (ih hφ tables (Option.elim · x σ)).mpr hx
      convert this using 1
      congr 1
      funext y
      cases y <;> rfl
  | @op Γ α k body ts ih =>
    have hop : Operator.Formula.op k body ts = lfp (body 0) ts := by
      unfold lfp
      congr 1
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst i
      rfl
    rw [hop] at hφ ⊢
    obtain ⟨hbody, hpos⟩ := (wellFormed_lfp (body 0) ts).mp hφ
    let tableStep := fun table : List Bool =>
      tableOf a.1 k (fun xs => eval v (body 0) a (table :: tables)
        (Sum.elim (fun x => (σ x : ℕ)) xs))
    have hstep (table : List Bool) :
        tableRelation a.1 k (tableStep table) =
          step (body 0) (relations Γ a.1 tables) σ (tableRelation a.1 k table) := by
      ext xs
      change (tableStep table).getD (tupleIndex xs) false = true ↔ _
      rw [show tableStep table = tableOf a.1 k (fun ys =>
        eval v (body 0) a (table :: tables) (Sum.elim (fun x => (σ x : ℕ)) ys)) from rfl,
        getD_tableOf]
      have hσ : Sum.elim (fun x => (σ x : ℕ)) (fun j => (xs j : ℕ)) =
          fun x => Fin.val (Sum.elim σ xs x) := by funext x; cases x <;> rfl
      rw [hσ, ih 0 hbody (table :: tables) (Sum.elim σ xs)]
      exact iff_of_eq (congrArg
        (fun ρ : Operator.RelEnv (k :: Γ) (Fin a.1) =>
          (body 0).Realize interpretation ρ (Sum.elim σ xs))
        (relations_cons Γ a.1 k table tables))
    have hiter (i : ℕ) :
        tableRelation a.1 k (tableStep^[i] []) =
          (step (body 0) (relations Γ a.1 tables) σ)^[i] ∅ := by
      induction i with
      | zero => exact tableRelation_nil _ _
      | succ i hi => rw [Function.iterate_succ_apply', hstep, hi,
          Function.iterate_succ_apply']
    rw [realize_lfp (body 0) hpos]
    change (tableStep^[a.1 ^ k] []).getD
      (valuesIndex a.1 (fun j => termValue a.1 (fun x => (σ x : ℕ)) (ts j))) false = true ↔ _
    simp only [termValue_eq, valuesIndex_val]
    change (fun j => (ts j).realize σ) ∈ tableRelation a.1 k (tableStep^[a.1 ^ k] []) ↔ _
    rw [hiter]
    have hfinite := iterate_card_pow_eq_lfp (body 0) hpos (relations Γ a.1 tables) σ
    rw [show (step (body 0) (relations Γ a.1 tables) σ)^[a.1 ^ k] ∅ =
      (stepHom (body 0) hpos (relations Γ a.1 tables) σ).lfp by
        simpa only [Fintype.card_fin] using hfinite]

end Correctness

/-- The bounded evaluator decides the standard realization of every checked formula in the
canonical ordered expansion of a decoded input. -/
theorem eval_eq_true_iff (v : Vocabulary L) {a : EncodedStructure} (hn : 2 ≤ a.1)
    {Γ : List ℕ} {α : Type w} (φ : RawFormula (Ordered.language L) Γ α)
    (hφ : φ.wellFormed policy = true) (tables : List (List Bool)) (σ : α → Fin a.1) :
    letI := v.decode a
    letI : Fact (2 ≤ a.1) := ⟨hn⟩
    eval v φ a tables (fun x => (σ x : ℕ)) = true ↔
      φ.Realize interpretation (relations Γ a.1 tables) σ := by
  let _ := v.decode a
  let _ : Fact (2 ≤ a.1) := ⟨hn⟩
  exact eval_correct v (fun _ _ => Iff.rfl) φ hφ tables σ

end Cslib.Logic.FO.LFP.ModelChecker
