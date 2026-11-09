/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.DNF
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Two-boundary counting

The construction of [ChenJiangZhu2027], Theorem 1.1 (PDF pp. 4–5), proved in
Section 4.1 (PDF p. 12). The path has `r + 1` edges and `r` new variables.
`query` constructs ordinary lists of clauses in the existing `CNF` syntax, substituting
both boundary constants and discarding tautological clauses. All variables of `V ⊕ Fin r`
are declared, including unused ones. With $n=|V|$ and $h=r+1$, their number is
exactly $n+h-1$. A DNF predicate is an explicit list of conjunctions of literals.
Empty terms are true, and empty term lists are false.

## Main results

* `counting_identity`: the number of solutions of the base CNF and every predicate
  is the difference of the two unweighted query counts.
* `query_width`, `query_length`, `declared_variables`: the bounds of Theorem 1.1.
* `extensions_cancel`: the explicit suffix-flip bijection at any failed edge.

The count is expressed as the cardinality of satisfying assignments on the entire declared
finite variable type. This agrees with the declared-variable convention, rather than
counting only variables occurring in clauses. The CNF construction traverses explicit
lists; no native-machine polynomial-time implementation is claimed here. The zero-predicate
case uses the base CNF itself. This endpoint does not import or formalize the paper's
external subexponential SAT theorem, row-selection algorithm or exact-one applications.

## Main definitions

* `query`: ordinary CNF boundary queries over the existing `DNF` syntax.

## References

* [ChenJiangZhu2027], Theorem 1.1 and Section 4.1, PDF pp. 4–5 and 12.
-/

public section

namespace Cslib.Logic.PL.TwoBoundary

variable {V W : Type*} {r : ℕ}

/-- A variable or a Boolean constant. -/
@[expose] def atomEval (σ : W → Bool) : Bool ⊕ W → Bool := Sum.elim id σ

/-- Substitute constants into a clause, omitting the whole clause if it becomes true. -/
@[expose] def lowerClause (c : List ((Bool ⊕ W) × Bool)) : CNF W :=
  if c.any (fun l => match l.1 with | .inl b => b == l.2 | .inr _ => false) then []
  else [c.filterMap fun l => match l.1 with | .inl _ => none | .inr w => some (w, l.2)]

/-- Constant substitution has the expected disjunctive semantics. -/
theorem lowerClause_eval (σ : W → Bool) (c : List ((Bool ⊕ W) × Bool)) :
    (lowerClause c).eval σ = c.any (fun l => atomEval σ l.1 == l.2) := by
  induction c with
  | nil => simp [lowerClause, CNF.eval, Clause.eval]
  | cons l c ih =>
    rcases l with ⟨a, b⟩
    cases a with
    | inl t =>
      cases t <;> cases b
      · simp [lowerClause, atomEval, CNF.eval]
      · exact ih
      · exact ih
      · simp [lowerClause, atomEval, CNF.eval]
    | inr w =>
      cases h : c.any (fun l => match l.1 with | .inl b => b == l.2 | .inr _ => false) <;>
        simp_all +decide [lowerClause, atomEval, CNF.eval, Clause.eval, Literal.eval]

/-- Endpoint substitution: full path indices are zero through `r + 1`. -/
@[expose] def port (r : ℕ) (β : Bool) (i : Fin (r + 2)) : Bool ⊕ (V ⊕ Fin r) :=
  if h0 : i.val = 0 then .inl false
  else if hl : i.val = r + 1 then .inl β
  else .inr (.inr ⟨i.val - 1, by have := i.isLt; omega⟩)

/-- The clauses for one term: if it holds, the two incident path bits must agree. -/
@[expose] def termClauses (r : ℕ) (β : Bool) (j : Fin (r + 1)) (t : List (Literal V)) :
    CNF (V ⊕ Fin r) :=
  let neg := t.map fun l => (Sum.inr (Sum.inl l.1), !l.2)
  lowerClause (neg ++ [(port r β j.castSucc, false), (port r β j.succ, true)]) ++
    lowerClause (neg ++ [(port r β j.castSucc, true), (port r β j.succ, false)])

/-- Ordinary unweighted CNF after substituting both boundary constants. -/
@[expose] def query (B : CNF V) (r : ℕ) (P : Fin (r + 1) → DNF V)
    (β : Bool) : CNF (V ⊕ Fin r) :=
  B.relabel Sum.inl ++ (List.finRange (r + 1)).flatMap fun j =>
    (P j).flatMap (termClauses r β j)

/-- Each term's clauses express exactly the activated path equality. -/
theorem termClauses_eval (r : ℕ) (β : Bool) (j : Fin (r + 1))
    (t : List (Literal V)) (σ : V ⊕ Fin r → Bool) :
    (termClauses r β j t).eval σ = true ↔
      Term.eval (fun v => σ (.inl v)) t = true →
      atomEval σ (port r β j.castSucc) = atomEval σ (port r β j.succ) := by
  simp only [termClauses, CNF.eval_append, Bool.and_eq_true, lowerClause_eval,
    List.any_append, List.any_map, List.any_cons, List.any_nil]
  have hn :
      t.any (fun l => atomEval σ (.inr (.inl l.1)) == !l.2) =
      !(Term.eval (fun v => σ (.inl v)) t) := by
    simpa only [Term.negate, Clause.eval, List.any_map, Literal.eval, atomEval,
      Function.comp_def, Sum.elim_inr] using Term.eval_negate (fun v => σ (.inl v)) t
  simp only [Function.comp_def] at *
  rw [hn]
  cases Term.eval (fun v => σ (.inl v)) t <;>
    cases atomEval σ (port r β j.castSucc) <;>
    cases atomEval σ (port r β j.succ) <;> decide

/-- The full query is the base CNF and precisely the activated path equalities. -/
theorem query_eval (B : CNF V) (r : ℕ) (P : Fin (r + 1) → DNF V)
    (β : Bool) (σ : V ⊕ Fin r → Bool) :
    (query B r P β).eval σ = true ↔
      B.eval (fun v => σ (.inl v)) = true ∧
      ∀ j, DNF.eval (fun v => σ (.inl v)) (P j) = true →
        atomEval σ (port r β j.castSucc) = atomEval σ (port r β j.succ) := by
  simp only [query, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel, Function.comp_def]
  apply and_congr_right
  intro _
  rw [CNF.eval_eq_true_iff]
  simp only [List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · intro h j hj
    obtain ⟨t, ht, htrue⟩ := (DNF.eval_eq_true_iff _ _).mp hj
    exact (termClauses_eval r β j t σ).mp
      ((CNF.eval_eq_true_iff _ _).mpr fun c hc => h c ⟨j, t, ht, hc⟩) htrue
  · intro h
    rintro c ⟨j, t, ht, hc⟩
    exact (CNF.eval_eq_true_iff _ _).mp
      ((termClauses_eval r β j t σ).mpr fun htrue =>
        h j (List.any_eq_true.mpr ⟨t, ht, htrue⟩)) c hc

/-- Flip the internal suffix following edge `j`. -/
@[expose] def flip (j : Fin (r + 1)) (z : Fin r → Bool) (i : Fin r) : Bool :=
  if j.val ≤ i.val then !(z i) else z i

/-- The suffix map is an involution. -/
theorem flip_flip (j : Fin (r + 1)) (z : Fin r → Bool) : flip j (flip j z) = z := by
  funext i
  simp only [flip]
  split_ifs <;> simp

/-- Completing the path commutes with flipping its suffix and right boundary. -/
theorem port_flip (x : V → Bool) (z : Fin r → Bool) (β : Bool)
    (j : Fin (r + 1)) (i : Fin (r + 2)) :
    atomEval (Sum.elim x (flip j z)) (port r (!β) i) =
      if j.val < i.val then !(atomEval (Sum.elim x z) (port r β i))
      else atomEval (Sum.elim x z) (port r β i) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold port
  split_ifs with h0 hl hji hji
  all_goals simp_all [atomEval, flip]
  all_goals omega

/-- An unrestricted edge makes the two boundary extension sets equinumerous. -/
theorem query_flip (B : CNF V) (P : Fin (r + 1) → DNF V)
    (x : V → Bool) (z : Fin r → Bool) (β : Bool) (j : Fin (r + 1))
    (hj : DNF.eval x (P j) = false) :
    (query B r P (!β)).eval (Sum.elim x (flip j z)) = true ↔
      (query B r P β).eval (Sum.elim x z) = true := by
  simp only [query_eval, Sum.elim_inl]
  apply and_congr_right
  intro _
  constructor
  all_goals intro h e he
  all_goals
    have hne : e ≠ j := by intro heq; subst e; simp_all
    have hs : (j.val < e.castSucc.val) ↔ (j.val < e.succ.val) := by
      have : e.val ≠ j.val := fun hv => hne (Fin.ext hv)
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
  · have hh := h e he
    rw [port_flip, port_flip] at hh
    by_cases hj' : j.val < e.castSucc.val
    · simp only [ite_eq_left hj', ite_eq_left (hs.mp hj')] at hh
      simpa only [Bool.not_not] using congrArg Bool.not hh
    · simpa only [ite_eq_right hj', ite_eq_right (fun hh => hj' (hs.mpr hh))] using hh
  · have hh := h e he
    rw [port_flip, port_flip]
    by_cases hj' : j.val < e.castSucc.val
    · simp only [ite_eq_left hj', ite_eq_left (hs.mp hj'), hh]
    · simp only [ite_eq_right hj', ite_eq_right (fun hh => hj' (hs.mpr hh)), hh]

/-- Fixed-input extension count, retaining every internal variable even if unused. -/
noncomputable def extensions (B : CNF V)
    (P : Fin (r + 1) → DNF V) (x : V → Bool) (β : Bool) : ℕ :=
  Fintype.card {z : Fin r → Bool // (query B r P β).eval (Sum.elim x z) = true}

/-- Suffix-flip cancellation, including empty term lists and the zero-internal-bit case. -/
theorem extensions_cancel (B : CNF V)
    (P : Fin (r + 1) → DNF V) (x : V → Bool) (β : Bool)
    (j : Fin (r + 1)) (hj : DNF.eval x (P j) = false) :
    extensions B P x (!β) = extensions B P x β := by
  classical
  apply Fintype.card_congr
  exact
    { toFun := fun z => ⟨flip j z.1, by
        simpa only [Bool.not_not] using (query_flip B P x z.1 (!β) j hj).mpr z.2⟩
      invFun := fun z => ⟨flip j z.1, (query_flip B P x z.1 β j hj).mpr z.2⟩
      left_inv := fun z => Subtype.ext (flip_flip j z.1)
      right_inv := fun z => Subtype.ext (flip_flip j z.1) }

/-- When every predicate holds, the path is forced to its left boundary. -/
theorem query_all (B : CNF V) (P : Fin (r + 1) → DNF V)
    (x : V → Bool) (z : Fin r → Bool) (β : Bool)
    (hp : ∀ j, DNF.eval x (P j) = true) :
    (query B r P β).eval (Sum.elim x z) = true ↔
      B.eval x = true ∧ β = false ∧ z = fun _ => false := by
  rw [query_eval]
  simp only [Sum.elim_inl]
  constructor
  · rintro ⟨hb, h⟩
    have hz : ∀ i, atomEval (Sum.elim x z) (port r β i) = false := by
      intro i
      induction i using Fin.induction with
      | zero => simp [port, atomEval]
      | succ i ih => exact (h i (hp i)).symm.trans ih
    have hβ := hz (Fin.last (r + 1))
    have hβ' : β = false := by simpa [port, atomEval] using hβ
    refine ⟨hb, hβ', ?_⟩
    funext i
    have hi := i.isLt
    have hzi := hz ⟨i.val + 1, by omega⟩
    simpa [port, atomEval, show i.val ≠ r by omega] using hzi
  · rintro ⟨hb, rfl, rfl⟩
    refine ⟨hb, fun j _ => ?_⟩
    have hz (i : Fin (r + 2)) :
        atomEval (Sum.elim x (fun _ : Fin r => false)) (port r false i) = false := by
      unfold port
      split_ifs <;> rfl
    rw [hz, hz]

/-- If all predicates hold, the unique zero-boundary extension is the all-zero assignment. -/
theorem extensions_all (B : CNF V)
    (P : Fin (r + 1) → DNF V) (x : V → Bool) (β : Bool)
    (hp : ∀ j, DNF.eval x (P j) = true) :
    extensions B P x β = if B.eval x = true ∧ β = false then 1 else 0 := by
  classical
  unfold extensions
  simp only [Fintype.card_subtype]
  simp_rw [query_all B P x _ β hp]
  by_cases hb : B.eval x = true <;> cases β <;> simp [hb, Finset.filter_eq']

/-- Fixed-input cancellation identity before summing over the original assignments. -/
theorem extensions_identity (B : CNF V)
    (P : Fin (r + 1) → DNF V) (x : V → Bool) :
    extensions B P x false =
      (if B.eval x = true ∧ ∀ j, DNF.eval x (P j) = true then 1 else 0) +
        extensions B P x true := by
  classical
  by_cases hp : ∀ j, DNF.eval x (P j) = true
  · rw [extensions_all B P x false hp, extensions_all B P x true hp]
    by_cases hb : B.eval x = true <;> simp [hb, hp]
  · obtain ⟨j, hj⟩ := not_forall.mp hp
    have hj' : DNF.eval x (P j) = false := Bool.eq_false_iff.mpr hj
    have hc := extensions_cancel B P x true j hj'
    simpa [hp] using hc

/-- Counting all declared query variables is the sum of the fixed-input extension counts. -/
theorem query_count [Fintype V] [DecidableEq V] (B : CNF V)
    (P : Fin (r + 1) → DNF V) (β : Bool) :
    Fintype.card {σ : V ⊕ Fin r → Bool // (query B r P β).eval σ = true} =
      ∑ x : V → Bool, extensions B P x β := by
  classical
  have heta (σ : V ⊕ Fin r → Bool) :
      Sum.elim (fun v => σ (.inl v)) (fun i => σ (.inr i)) = σ := by
    funext a
    cases a <;> rfl
  let e : {σ : V ⊕ Fin r → Bool // (query B r P β).eval σ = true} ≃
      (Σ x : V → Bool,
        {z : Fin r → Bool // (query B r P β).eval (Sum.elim x z) = true}) :=
    { toFun := fun σ => ⟨fun v => σ.1 (.inl v),
        ⟨fun i => σ.1 (.inr i), by simpa only [heta] using σ.2⟩⟩
      invFun := fun x => ⟨Sum.elim x.1 x.2.1, x.2.2⟩
      left_inv := fun σ => Subtype.ext (heta σ.1)
      right_inv := fun x => by cases x; rfl }
  simpa only [Fintype.card_sigma, extensions] using Fintype.card_congr e

/-- The exact unweighted two-query count identity; every declared variable is counted. -/
theorem counting_identity [Fintype V] [DecidableEq V] (B : CNF V)
    (P : Fin (r + 1) → DNF V) :
    Fintype.card {x : V → Bool // B.eval x = true ∧ ∀ j, DNF.eval x (P j) = true} =
      Fintype.card {σ : V ⊕ Fin r → Bool // (query B r P false).eval σ = true} -
      Fintype.card {σ : V ⊕ Fin r → Bool // (query B r P true).eval σ = true} := by
  classical
  rw [query_count, query_count]
  have h := Finset.sum_congr (rfl : (Finset.univ : Finset (V → Bool)) = Finset.univ)
    (fun x _ => extensions_identity B P x)
  rw [Finset.sum_add_distrib] at h
  have hc : (∑ x : V → Bool,
      if B.eval x = true ∧ ∀ j, DNF.eval x (P j) = true then 1 else 0) =
      Fintype.card {x : V → Bool // B.eval x = true ∧ ∀ j, DNF.eval x (P j) = true} := by
    simp [Fintype.card_subtype]
  rw [hc] at h
  omega

/-- The variable budget is exactly the original number plus the internal path length. -/
theorem declared_variables [Fintype V] :
    Fintype.card (V ⊕ Fin r) = Fintype.card V + (r + 1) - 1 := by
  simp

/-- Substitution can only discard clauses. -/
theorem lowerClause_length (c : List ((Bool ⊕ W) × Bool)) :
    (lowerClause c).length ≤ 1 := by
  unfold lowerClause
  split_ifs <;> simp

/-- Substitution can only discard literals. -/
theorem lowerClause_width (c : List ((Bool ⊕ W) × Bool)) (a : Clause W)
    (ha : a ∈ lowerClause c) : a.length ≤ c.length := by
  unfold lowerClause at ha
  split_ifs at ha
  · simp at ha
  · have heq := List.mem_singleton.mp ha
    subst a
    exact List.length_filterMap_le _ _

/-- A term contributes at most two ordinary clauses. -/
theorem termClauses_length (r : ℕ) (β : Bool) (j : Fin (r + 1))
    (t : List (Literal V)) : (termClauses r β j t).length ≤ 2 := by
  unfold termClauses
  rw [List.length_append]
  have h1 := lowerClause_length
    (t.map (fun l => (Sum.inr (Sum.inl l.1), !l.2)) ++
      [(port r β j.castSucc, false), (port r β j.succ, true)])
  have h2 := lowerClause_length
    (t.map (fun l => (Sum.inr (Sum.inl l.1), !l.2)) ++
      [(port r β j.castSucc, true), (port r β j.succ, false)])
  omega

/-- Term length plus two bounds every generated clause, before or after substitution. -/
theorem termClauses_width (r : ℕ) (β : Bool) (j : Fin (r + 1))
    (t : List (Literal V)) (c : Clause (V ⊕ Fin r)) (hc : c ∈ termClauses r β j t) :
    c.length ≤ t.length + 2 := by
  simp only [termClauses, List.mem_append] at hc
  rcases hc with hc | hc
  all_goals have h := lowerClause_width _ c hc
  all_goals simpa only [List.length_append, List.length_map, List.length_cons,
    List.length_nil] using h

/-- The common width bound of the two queries. -/
theorem query_width (B : CNF V) (P : Fin (r + 1) → DNF V)
    (b d : ℕ) (hb : ∀ c ∈ B, c.length ≤ b)
    (hp : ∀ j t, t ∈ P j → t.length ≤ d) (β : Bool)
    (c : Clause (V ⊕ Fin r)) (hc : c ∈ query B r P β) :
    c.length ≤ max b (d + 2) := by
  simp only [query, List.mem_append, CNF.relabel, List.mem_map, List.mem_flatMap] at hc
  rcases hc with ⟨a, ha, rfl⟩ | ⟨j, _, t, ht, hc⟩
  · simpa only [Clause.relabel, List.length_map] using (hb a ha).trans (le_max_left _ _)
  · exact (termClauses_width r β j t c hc).trans
      ((Nat.add_le_add_right (hp j t ht) 2).trans (le_max_right _ _))

/-- The clause budget counts terms, with no additional variables or endpoint clauses. -/
theorem query_length (B : CNF V) (P : Fin (r + 1) → DNF V) (β : Bool) :
    (query B r P β).length ≤ B.length + 2 * ∑ j : Fin (r + 1), (P j).length := by
  have ht (j : Fin (r + 1)) (ts : DNF V) :
      (ts.flatMap (termClauses r β j)).length ≤ 2 * ts.length := by
    induction ts with
    | nil => simp
    | cons t ts ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have := termClauses_length r β j t
      omega
  have hl (js : List (Fin (r + 1))) :
      (js.flatMap fun j => (P j).flatMap (termClauses r β j)).length ≤
        2 * (js.map fun j => (P j).length).sum := by
    induction js with
    | nil => simp
    | cons j js ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      have := ht j (P j)
      omega
  have h := hl (List.finRange (r + 1))
  simpa [query, CNF.relabel, List.length_append, List.length_map,
    List.finRange, List.map_ofFn, List.sum_ofFn, Fin.sum_univ_succ] using
      Nat.add_le_add_left h B.length

end Cslib.Logic.PL.TwoBoundary
