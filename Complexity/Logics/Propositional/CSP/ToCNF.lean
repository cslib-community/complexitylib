/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Enumeration
public import Complexity.Logics.Propositional.CSP

/-!
# Forbidden-pattern compilation from Boolean CSPs to CNF

Every Boolean constraint `(R, vs) : Constraint Rel V` of scope length `r = vs.length ≤ k` has at
most `2 ^ r ≤ 2 ^ k` forbidden local assignments `w ∈ BitString.enumList r` with `sem R w = false`.
Emitting one width-`r` clause `Constraint.forbidClause vs w` per forbidden assignment translates a
Boolean CSP instance `F : CSP Rel V` into an equivalent `k`-CNF formula `F.toCNF sem` on a subset
of the same variables, with no auxiliary variables and therefore multiplicative factor `1` on
satisfying assignments:
* `(F.toCNF sem).eval σ = F.eval sem σ` for every assignment `σ : V → Bool`;
* `(F.toCNF sem).modelCountOn S = F.modelCountOn sem S` for every declared variable set `S`;
* `(F.toCNF sem).length ≤ 2 ^ k * F.length` and every generated clause has width `≤ k`.

## Main definitions

* `Cslib.Logic.PL.Constraint.forbidClause`: the clause forbidding a local bit pattern on a scope.
* `Cslib.Logic.PL.Constraint.toCNF`, `Cslib.Logic.PL.Constraint.toCNFBounded`: compile a Boolean
  constraint to CNF by forbidding falsifying patterns.
* `Cslib.Logic.PL.CSP.toCNF`, `Cslib.Logic.PL.CSP.toCNFBounded`: compile a Boolean CSP instance to
  CNF.

## Main results

* `Cslib.Logic.PL.Constraint.eval_forbidClause`, `Cslib.Logic.PL.Constraint.eval_toCNF`,
  `Cslib.Logic.PL.CSP.eval_toCNF`: exact evaluation equivalence of the compiled CNF formula.
* `Cslib.Logic.PL.CSP.satisfiable_toCNF`, `Cslib.Logic.PL.CSP.modelCountOn_toCNF`: satisfiability
  and declared-variable model counts are preserved with multiplicity `1`.
* `Cslib.Logic.PL.CSP.length_clause_mem_toCNFBounded`,
  `Cslib.Logic.PL.CSP.validDeclaredInput_toCNFBounded`: clause-width and declared-variable bounds.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C (p. 52).
-/

@[expose] public section

namespace Cslib.Logic.PL

namespace Constraint

variable {Rel V W : Type*}

/-- The clause on scope `vs` forbidding the local bit pattern `w` by negating each bit of `w`. -/
def forbidClause (vs : List V) (w : List Bool) : Clause V :=
  (vs.zip w).map fun p => (p.1, !p.2)

/-- Consing a variable and a bit prepends the negated literal to `forbidClause`. -/
@[simp]
theorem forbidClause_cons (v : V) (vs : List V) (b : Bool) (w : List Bool) :
    forbidClause (v :: vs) (b :: w) = (v, !b) :: forbidClause vs w :=
  rfl

/-- The length of `forbidClause vs w` is `min vs.length w.length`. -/
@[simp]
theorem length_forbidClause (vs : List V) (w : List Bool) :
    (forbidClause vs w).length = min vs.length w.length := by
  simp [forbidClause]

/-- `forbidClause vs w` has at most `vs.length` literals. -/
theorem length_forbidClause_le (vs : List V) (w : List Bool) :
    (forbidClause vs w).length ≤ vs.length := by
  rw [length_forbidClause]
  exact Nat.min_le_left _ _

/-- Every variable in `forbidClause vs w` belongs to `vs`. -/
theorem mem_vars_forbidClause {vs : List V} {w : List Bool} {l : Literal V}
    (hl : l ∈ forbidClause vs w) : l.1 ∈ vs := by
  simp only [forbidClause, List.mem_map] at hl
  rcases hl with ⟨⟨v, b⟩, hmem, rfl⟩
  exact (List.of_mem_zip hmem).1

/-- Relabeling `forbidClause vs w` maps `f` over the scope `vs`. -/
theorem relabel_forbidClause (f : V → W) (vs : List V) (w : List Bool) :
    (forbidClause vs w).relabel f = forbidClause (vs.map f) w := by
  induction vs generalizing w with
  | nil => rfl
  | cons v vs ih =>
    cases w with
    | nil => rfl
    | cons b w =>
      simp only [forbidClause_cons, List.map_cons, Clause.relabel]
      exact congrArg _ (ih w)

/-- `forbidClause vs w` evaluates to `false` under `σ` if and only if `vs.map σ = w` (even when
`vs` contains repeated variables). -/
theorem eval_forbidClause (vs : List V) {w : List Bool} (hw : w.length = vs.length)
    (σ : V → Bool) :
    (forbidClause vs w).eval σ = !(vs.map σ == w) := by
  induction vs generalizing w with
  | nil =>
    cases w with
    | nil => rfl
    | cons _ _ => simp at hw
  | cons v vs ih =>
    cases w with
    | nil => simp at hw
    | cons b w =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hw
      rw [forbidClause_cons, Clause.eval, List.any_cons, ← Clause.eval, ih hw]
      simp only [Literal.eval, List.map_cons]
      cases σ v <;> cases b <;> simp

/-- Compile a Boolean constraint `c = (R, vs)` to a CNF formula by emitting `forbidClause vs w` for
every forbidden local assignment `w ∈ BitString.enumList vs.length` with `sem R w = false`. -/
def toCNF (sem : Rel → List Bool → Bool) (c : Constraint Rel V) : CNF V :=
  ((BitString.enumList c.2.length).filter fun w => !sem c.1 w).map (forbidClause c.2)

/-- Width-guarded compilation: emits `toCNF sem c` when `c.2.length ≤ k` and `[]` otherwise. -/
def toCNFBounded (k : ℕ) (sem : Rel → List Bool → Bool) (c : Constraint Rel V) : CNF V :=
  if c.2.length ≤ k then toCNF sem c else []

/-- When `c.2.length ≤ k`, `toCNFBounded k sem c` agrees with `toCNF sem c`. -/
theorem toCNFBounded_eq_toCNF {k : ℕ} {sem : Rel → List Bool → Bool} {c : Constraint Rel V}
    (hc : c.2.length ≤ k) :
    toCNFBounded k sem c = toCNF sem c := by
  simp [toCNFBounded, hc]

/-- Every clause in `c.toCNF sem` has length at most `c.2.length`. -/
theorem length_clause_mem_toCNF {sem : Rel → List Bool → Bool} {c : Constraint Rel V}
    {cl : Clause V} (hcl : cl ∈ toCNF sem c) :
    cl.length ≤ c.2.length := by
  simp only [toCNF, List.mem_map] at hcl
  rcases hcl with ⟨w, _, rfl⟩
  exact length_forbidClause_le c.2 w

/-- Every clause in `c.toCNFBounded k sem` has length at most `k`. -/
theorem length_clause_mem_toCNFBounded {k : ℕ} {sem : Rel → List Bool → Bool}
    {c : Constraint Rel V} {cl : Clause V} (hcl : cl ∈ toCNFBounded k sem c) :
    cl.length ≤ k := by
  unfold toCNFBounded at hcl
  split_ifs at hcl with hc
  · exact (length_clause_mem_toCNF hcl).trans hc
  · simp at hcl

/-- `c.toCNF sem` contains at most `2 ^ c.2.length` clauses. -/
theorem length_toCNF_le (sem : Rel → List Bool → Bool) (c : Constraint Rel V) :
    (toCNF sem c).length ≤ 2 ^ c.2.length := by
  simp only [toCNF, List.length_map]
  exact (List.length_filter_le _ _).trans (by rw [BitString.length_enumList])

/-- Every variable occurring in `c.toCNF sem` belongs to the constraint scope `c.2`. -/
theorem mem_vars_toCNF {sem : Rel → List Bool → Bool} {c : Constraint Rel V} {v : V}
    (hv : v ∈ (toCNF sem c).vars) : v ∈ c.2 := by
  simp only [CNF.vars, List.mem_map, List.mem_flatten] at hv
  rcases hv with ⟨l, ⟨cl, hcl, hl⟩, rfl⟩
  simp only [toCNF, List.mem_map] at hcl
  rcases hcl with ⟨w, _, rfl⟩
  exact mem_vars_forbidClause hl

/-- Every variable occurring in `c.toCNFBounded k sem` belongs to the constraint scope `c.2`. -/
theorem mem_vars_toCNFBounded {k : ℕ} {sem : Rel → List Bool → Bool} {c : Constraint Rel V}
    {v : V} (hv : v ∈ (toCNFBounded k sem c).vars) : v ∈ c.2 := by
  unfold toCNFBounded at hv
  split_ifs at hv
  · exact mem_vars_toCNF hv
  · simp [CNF.vars] at hv

/-- Relabeling commutes with `Constraint.toCNF`. -/
theorem relabel_toCNF (sem : Rel → List Bool → Bool) (f : V → W) (c : Constraint Rel V) :
    (toCNF sem c).relabel f = toCNF sem (relabel f c) := by
  simp only [toCNF, relabel, CNF.relabel, List.length_map, List.map_map, Function.comp_def,
    relabel_forbidClause]

/-- Relabeling commutes with `Constraint.toCNFBounded`. -/
theorem relabel_toCNFBounded (k : ℕ) (sem : Rel → List Bool → Bool) (f : V → W)
    (c : Constraint Rel V) :
    (toCNFBounded k sem c).relabel f = toCNFBounded k sem (relabel f c) := by
  simp only [toCNFBounded, relabel, List.length_map]
  split_ifs
  · exact relabel_toCNF sem f c
  · rfl

/-- The forbidden-assignment CNF compilation of a constraint has the exact same truth value under
every assignment `σ : V → Bool` as the constraint itself. -/
@[simp]
theorem eval_toCNF (sem : Rel → List Bool → Bool) (c : Constraint Rel V) (σ : V → Bool) :
    (toCNF sem c).eval σ = eval sem σ c := by
  rw [Bool.eq_iff_iff, CNF.eval_eq_true_iff]
  simp only [toCNF, List.mem_map, List.mem_filter, BitString.mem_enumList, Bool.not_eq_true']
  constructor
  · intro h
    by_contra hfalse
    simp only [eval, Bool.not_eq_true] at hfalse
    have hw : (c.2.map σ).length = c.2.length := List.length_map _
    have hcl := h (forbidClause c.2 (c.2.map σ)) ⟨c.2.map σ, ⟨hw, hfalse⟩, rfl⟩
    rw [eval_forbidClause c.2 hw σ] at hcl
    simp at hcl
  · rintro h cl ⟨w, ⟨hw, hsem⟩, rfl⟩
    rw [eval_forbidClause c.2 hw σ, Bool.not_eq_true', beq_eq_false_iff_ne]
    intro heq
    rw [eval, heq, hsem] at h
    exact Bool.false_ne_true h

end Constraint

namespace CSP

variable {Rel V W : Type*}

/-- Compile a Boolean CSP instance `F` to a CNF formula by concatenating the forbidden-assignment
clauses of each constraint. -/
def toCNF (sem : Rel → List Bool → Bool) (F : CSP Rel V) : CNF V :=
  F.flatMap (Constraint.toCNF sem)

/-- Width-guarded compilation of `F` to a `k`-CNF formula. -/
def toCNFBounded (k : ℕ) (sem : Rel → List Bool → Bool) (F : CSP Rel V) : CNF V :=
  F.flatMap (Constraint.toCNFBounded k sem)

/-- When all constraint scopes in `F` have length `≤ k`, `F.toCNFBounded k sem = F.toCNF sem`. -/
theorem toCNFBounded_eq_toCNF {k : ℕ} {sem : Rel → List Bool → Bool} {F : CSP Rel V}
    (hF : ∀ c ∈ F, c.2.length ≤ k) :
    F.toCNFBounded k sem = F.toCNF sem :=
  List.flatMap_congr fun c hc => Constraint.toCNFBounded_eq_toCNF (hF c hc)

/-- Every clause in `F.toCNFBounded k sem` has length at most `k`. -/
theorem length_clause_mem_toCNFBounded {k : ℕ} {sem : Rel → List Bool → Bool} {F : CSP Rel V}
    {cl : Clause V} (hcl : cl ∈ F.toCNFBounded k sem) :
    cl.length ≤ k := by
  rcases List.mem_flatMap.mp hcl with ⟨c, _, hcl'⟩
  exact Constraint.length_clause_mem_toCNFBounded hcl'

/-- When all constraint scopes in `F` have length `≤ k`, every clause in `F.toCNF sem` has length
at most `k`. -/
theorem length_clause_mem_toCNF {k : ℕ} {sem : Rel → List Bool → Bool} {F : CSP Rel V}
    (hF : ∀ c ∈ F, c.2.length ≤ k) {cl : Clause V} (hcl : cl ∈ F.toCNF sem) :
    cl.length ≤ k := by
  rw [← toCNFBounded_eq_toCNF hF] at hcl
  exact length_clause_mem_toCNFBounded hcl

/-- When all constraint scopes in `F` have length `≤ k`, `F.toCNF sem` has at most
`2 ^ k * F.length` clauses. -/
theorem length_toCNF_le {k : ℕ} (sem : Rel → List Bool → Bool) {F : CSP Rel V}
    (hF : ∀ c ∈ F, c.2.length ≤ k) :
    (F.toCNF sem).length ≤ 2 ^ k * F.length := by
  induction F with
  | nil => simp [toCNF]
  | cons c F ih =>
    simp only [toCNF, List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have hc : (Constraint.toCNF sem c).length ≤ 2 ^ k :=
      (Constraint.length_toCNF_le sem c).trans
        (Nat.pow_le_pow_right (by decide) (hF c List.mem_cons_self))
    have hrest : (List.flatMap (Constraint.toCNF sem) F).length ≤ 2 ^ k * F.length :=
      ih fun c' hc' => hF c' (List.mem_cons_of_mem c hc')
    omega

/-- Every variable occurring in `F.toCNF sem` occurs in `F.vars`. -/
theorem mem_vars_toCNF {sem : Rel → List Bool → Bool} {F : CSP Rel V} {v : V}
    (hv : v ∈ (F.toCNF sem).vars) : v ∈ F.vars := by
  simp only [toCNF, CNF.vars, List.mem_map, List.mem_flatten, List.mem_flatMap] at hv
  rcases hv with ⟨l, ⟨cl, ⟨c, hc, hcl⟩, hl⟩, rfl⟩
  rw [vars, List.mem_flatMap]
  refine ⟨c, hc, Constraint.mem_vars_toCNF (sem := sem) ?_⟩
  simp only [CNF.vars, List.mem_map, List.mem_flatten]
  exact ⟨l, ⟨cl, hcl, hl⟩, rfl⟩

/-- Every variable occurring in `F.toCNFBounded k sem` occurs in `F.vars`. -/
theorem mem_vars_toCNFBounded {k : ℕ} {sem : Rel → List Bool → Bool} {F : CSP Rel V} {v : V}
    (hv : v ∈ (F.toCNFBounded k sem).vars) : v ∈ F.vars := by
  simp only [toCNFBounded, CNF.vars, List.mem_map, List.mem_flatten, List.mem_flatMap] at hv
  rcases hv with ⟨l, ⟨cl, ⟨c, hc, hcl⟩, hl⟩, rfl⟩
  rw [vars, List.mem_flatMap]
  refine ⟨c, hc, Constraint.mem_vars_toCNFBounded (k := k) (sem := sem) ?_⟩
  simp only [CNF.vars, List.mem_map, List.mem_flatten]
  exact ⟨l, ⟨cl, hcl, hl⟩, rfl⟩

/-- Relabeling commutes with `CSP.toCNF`. -/
theorem relabel_toCNF (sem : Rel → List Bool → Bool) (f : V → W) (F : CSP Rel V) :
    (F.toCNF sem).relabel f = (F.relabel f).toCNF sem := by
  simp only [toCNF, relabel, CNF.relabel, List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun c _ => ?_
  exact Constraint.relabel_toCNF sem f c

/-- Relabeling commutes with `CSP.toCNFBounded`. -/
theorem relabel_toCNFBounded (k : ℕ) (sem : Rel → List Bool → Bool) (f : V → W) (F : CSP Rel V) :
    (F.toCNFBounded k sem).relabel f = (F.relabel f).toCNFBounded k sem := by
  simp only [toCNFBounded, relabel, CNF.relabel, List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun c _ => ?_
  exact Constraint.relabel_toCNFBounded k sem f c

/-- The compiled CNF formula `F.toCNF sem` evaluates identically to `F` under every assignment. -/
@[simp]
theorem eval_toCNF (sem : Rel → List Bool → Bool) (F : CSP Rel V) (σ : V → Bool) :
    (F.toCNF sem).eval σ = F.eval sem σ := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    change ((Constraint.toCNF sem c ++ toCNF sem F).eval σ) =
      (Constraint.eval sem σ c && eval sem σ F)
    rw [CNF.eval_append, ih, Constraint.eval_toCNF]

/-- `F.toCNF sem` is satisfiable if and only if `F` is satisfiable under `sem`. -/
@[simp]
theorem satisfiable_toCNF (sem : Rel → List Bool → Bool) (F : CSP Rel V) :
    (F.toCNF sem).Satisfiable ↔ F.Satisfiable sem := by
  simp [CNF.Satisfiable, Satisfiable]

variable [DecidableEq V]

/-- Forbidden-assignment CNF compilation preserves declared-variable model counts on every finite
variable set `declared` with multiplicity `1` (no auxiliary variables). -/
@[simp]
theorem modelCountOn_toCNF (sem : Rel → List Bool → Bool) (F : CSP Rel V) (declared : Finset V) :
    (F.toCNF sem).modelCountOn declared = F.modelCountOn sem declared := by
  simp only [CNF.modelCountOn, modelCountOn, eval_toCNF]
  rfl

/-- If `F` passes `validDeclaredCSP k N`, then `F.toCNFBounded k sem` passes
`CNF.validDeclaredInput k N`. -/
theorem validDeclaredInput_toCNFBounded {k N : ℕ} (sem : Rel → List Bool → Bool) {F : CSP Rel ℕ}
    (hv : validDeclaredCSP k N F = true) :
    CNF.validDeclaredInput k N (F.toCNFBounded k sem) = true := by
  obtain ⟨_, hsub⟩ := validDeclaredCSP_eq_true_iff.mp hv
  refine CNF.validDeclaredInput_eq_true_iff.mpr
    ⟨fun cl hcl => length_clause_mem_toCNFBounded hcl, ?_⟩
  intro v hv'
  exact hsub (List.mem_toFinset.mpr (mem_vars_toCNFBounded (List.mem_toFinset.mp hv')))

end CSP

end Cslib.Logic.PL
