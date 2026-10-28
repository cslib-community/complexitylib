/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.CountingNativeEndpoint
public import Complexity.Computability.Complexity.FineGrained.CountingEndpoint
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Exact subexponential counting and decision for bounded-arity Boolean `#CSP`

A Boolean constraint satisfaction instance `F : CSP Rel V` over a relation alphabet `Rel` and
variable type `V` is a list of constraints `(R, vs) : Rel × List V`, interpreted under a family of
Boolean relations `sem : Rel → List Bool → Bool` by requiring `sem R (vs.map σ) = true` for every
`(R, vs) ∈ F`.

Every constraint `(R, vs)` of arity `r = vs.length ≤ k` has at most `2 ^ r ≤ 2 ^ k` forbidden local
assignments `w ∈ {false, true} ^ r` with `sem R w = false`. Emitting one width-`r` clause
`Constraint.forbidClause vs w` per forbidden assignment translates `F` into an equivalent `k`-CNF
formula `F.toCNF sem` on a subset of the same variables, with no auxiliary variables and therefore
multiplicative factor `1` on satisfying assignments:
- `(F.toCNF sem).eval σ = F.eval sem σ` for every assignment `σ : V → Bool`;
- `(F.toCNF sem).modelCountOn S = F.modelCountOn sem S` for every declared variable set `S`;
- `(F.toCNF sem).length ≤ 2 ^ k * F.length` and every generated clause has width `≤ k`.

When `Rel` is finite (`[Finite Rel]`) and the arity bound `k` is fixed, the bounded compiler
`CSP.toCNFBounded k sem` runs in polynomial time for any relation family `sem` (since the forbidden
patterns of length `≤ k` for each symbol `R : Rel` form a finite table). Composing with
`CountingNativeEndpoint.exists_declaredCounter k` yields:
1. Exact declared-variable counting (`CSP.exists_declaredCounter`) in time
   `O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial space;
2. Exact occurring-variable counting (`CSP.exists_modelCounter`) in time
   `O(2 ^ (A * interpolationScale F.numVars) * (|F| + 1) ^ e)` and polynomial space via dense
   variable relabeling;
3. Subexponential-time decision (`CSP.decidableInSubexpTime_KCSP`) for `CSP.KCSP k sem` with respect
   to `CSP.numVars`.

## Main definitions

* `Cslib.Complexity.Constraint`, `Cslib.Complexity.CSP`: Boolean constraints and `#CSP` instances.
* `Cslib.Complexity.encConstraint`, `Cslib.Complexity.encCSP`: standard binary encodings.
* `Cslib.Complexity.Constraint.toCNF`, `Cslib.Complexity.CSP.toCNF`,
  `Cslib.Complexity.CSP.toCNFBounded`: forbidden-assignment compilation to CNF.
* `Cslib.Complexity.CSP.modelCountOn`, `Cslib.Complexity.CSP.modelCount`: declared-variable and
  occurring-variable model counts.
* `Cslib.Complexity.CSP.KCSP`: the bounded-arity Boolean CSP decision problem.

## Main results

* `Cslib.Complexity.CSP.eval_toCNF`, `Cslib.Complexity.CSP.modelCountOn_toCNF`: exact equivalence
  and multiplicity-`1` count preservation of the forbidden-assignment CNF compilation.
* `Cslib.Complexity.CSP.computableInPolyTime_toCNFBounded`: polynomial-time compilation over any
  finite relation alphabet.
* `Cslib.Complexity.CSP.exists_declaredCounter`, `Cslib.Complexity.CSP.exists_modelCounter`:
  exact subexponential counting at `interpolationScale` in polynomial space.
* `Cslib.Complexity.CSP.decidableInSubexpTime_KCSP`: subexponential-time decision for bounded-arity
  Boolean CSP.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 6.4 and Appendix C.
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-! ### Enumerating fixed-length Boolean lists -/

/-- All Boolean lists of length `r`, ordered lexicographically by head bit. -/
def enumBoolLists : ℕ → List (List Bool)
  | 0 => [[]]
  | r + 1 => (enumBoolLists r).flatMap fun w => [false :: w, true :: w]

@[simp]
theorem mem_enumBoolLists {r : ℕ} {w : List Bool} :
    w ∈ enumBoolLists r ↔ w.length = r := by
  induction r generalizing w with
  | zero =>
    simp only [enumBoolLists, List.mem_singleton, List.length_eq_zero_iff]
  | succ r ih =>
    simp only [enumBoolLists, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨u, hu, rfl | rfl⟩ <;> simp [ih.mp hu]
    · cases w with
      | nil => simp
      | cons b u =>
        intro h
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h
        refine ⟨u, ih.mpr h, ?_⟩
        cases b <;> simp

@[simp]
theorem length_enumBoolLists (r : ℕ) :
    (enumBoolLists r).length = 2 ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [enumBoolLists, List.length_flatMap, List.length_cons, List.length_nil,
      List.map_const', List.sum_replicate, smul_eq_mul, ih, Nat.pow_succ']
    omega

/-! ### Boolean constraints and forbidden-assignment clauses -/

/-- A Boolean constraint over relation alphabet `Rel` and variable type `V` pairs a relation symbol
with its scope of variables. -/
abbrev Constraint (Rel V : Type*) : Type _ := Rel × List V

/-- A Boolean CSP instance over relation alphabet `Rel` and variable type `V` is a conjunction
(list) of constraints. -/
abbrev CSP (Rel V : Type*) : Type _ := List (Constraint Rel V)

/-- Binary encoding of a constraint `(R, vs)`. -/
abbrev encConstraint {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    Constraint Rel V ↪ List Bool :=
  encPair encRel (encList encV)

/-- Binary encoding of a CSP instance. -/
abbrev encCSP {Rel V : Type} (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    CSP Rel V ↪ List Bool :=
  encList (encConstraint encRel encV)

namespace Constraint

variable {Rel V W : Type*}

/-- Evaluate a constraint `(R, vs)` under assignment `σ : V → Bool` and semantics
`sem : Rel → List Bool → Bool`. -/
def eval (sem : Rel → List Bool → Bool) (σ : V → Bool) (c : Constraint Rel V) : Bool :=
  sem c.1 (c.2.map σ)

/-- Rename variables in a constraint's scope. -/
def relabel (f : V → W) (c : Constraint Rel V) : Constraint Rel W :=
  (c.1, c.2.map f)

@[simp]
theorem eval_relabel (sem : Rel → List Bool → Bool) (f : V → W) (σ : W → Bool)
    (c : Constraint Rel V) :
    eval sem σ (relabel f c) = eval sem (σ ∘ f) c := by
  simp [eval, relabel, List.map_map]

theorem eval_congr {sem : Rel → List Bool → Bool} {c : Constraint Rel V} {σ τ : V → Bool}
    (h : ∀ v ∈ c.2, σ v = τ v) :
    eval sem σ c = eval sem τ c := by
  simp only [eval]
  congr 1
  exact List.map_congr_left h

/-- The clause on scope `vs` forbidding the local bit pattern `w` by negating each bit of `w`. -/
def forbidClause (vs : List V) (w : List Bool) : Clause V :=
  (vs.zip w).map fun p => (p.1, !p.2)

@[simp]
theorem forbidClause_cons (v : V) (vs : List V) (b : Bool) (w : List Bool) :
    forbidClause (v :: vs) (b :: w) = (v, !b) :: forbidClause vs w :=
  rfl

@[simp]
theorem length_forbidClause (vs : List V) (w : List Bool) :
    (forbidClause vs w).length = min vs.length w.length := by
  simp [forbidClause]

theorem length_forbidClause_le (vs : List V) (w : List Bool) :
    (forbidClause vs w).length ≤ vs.length := by
  rw [length_forbidClause]
  exact Nat.min_le_left _ _

theorem mem_vars_forbidClause {vs : List V} {w : List Bool} {l : Literal V}
    (hl : l ∈ forbidClause vs w) : l.1 ∈ vs := by
  simp only [forbidClause, List.mem_map] at hl
  rcases hl with ⟨⟨v, b⟩, hmem, rfl⟩
  exact (List.of_mem_zip hmem).1

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

/-- Compile a constraint `c = (R, vs)` to a CNF formula by emitting `forbidClause vs w` for every
forbidden local assignment `w ∈ enumBoolLists vs.length` with `sem R w = false`. -/
def toCNF (sem : Rel → List Bool → Bool) (c : Constraint Rel V) : CNF V :=
  ((enumBoolLists c.2.length).filter fun w => !sem c.1 w).map (forbidClause c.2)

/-- Width-guarded compilation: emits `toCNF sem c` when `c.2.length ≤ k` and `[]` otherwise. -/
def toCNFBounded (k : ℕ) (sem : Rel → List Bool → Bool) (c : Constraint Rel V) : CNF V :=
  if c.2.length ≤ k then toCNF sem c else []

theorem toCNFBounded_eq_toCNF {k : ℕ} {sem : Rel → List Bool → Bool} {c : Constraint Rel V}
    (hc : c.2.length ≤ k) :
    toCNFBounded k sem c = toCNF sem c := by
  simp [toCNFBounded, hc]

theorem length_clause_mem_toCNF {sem : Rel → List Bool → Bool} {c : Constraint Rel V}
    {cl : Clause V} (hcl : cl ∈ toCNF sem c) :
    cl.length ≤ c.2.length := by
  simp only [toCNF, List.mem_map] at hcl
  rcases hcl with ⟨w, _, rfl⟩
  exact length_forbidClause_le c.2 w

theorem length_clause_mem_toCNFBounded {k : ℕ} {sem : Rel → List Bool → Bool}
    {c : Constraint Rel V} {cl : Clause V} (hcl : cl ∈ toCNFBounded k sem c) :
    cl.length ≤ k := by
  unfold toCNFBounded at hcl
  split_ifs at hcl with hc
  · exact (length_clause_mem_toCNF hcl).trans hc
  · simp at hcl

theorem length_toCNF_le (sem : Rel → List Bool → Bool) (c : Constraint Rel V) :
    (toCNF sem c).length ≤ 2 ^ c.2.length := by
  simp only [toCNF, List.length_map]
  exact (List.length_filter_le _ _).trans (by rw [length_enumBoolLists])

theorem mem_vars_toCNF {sem : Rel → List Bool → Bool} {c : Constraint Rel V} {v : V}
    (hv : v ∈ (toCNF sem c).vars) : v ∈ c.2 := by
  simp only [CNF.vars, List.mem_map, List.mem_flatten] at hv
  rcases hv with ⟨l, ⟨cl, hcl, hl⟩, rfl⟩
  simp only [toCNF, List.mem_map] at hcl
  rcases hcl with ⟨w, _, rfl⟩
  exact mem_vars_forbidClause hl

theorem mem_vars_toCNFBounded {k : ℕ} {sem : Rel → List Bool → Bool} {c : Constraint Rel V}
    {v : V} (hv : v ∈ (toCNFBounded k sem c).vars) : v ∈ c.2 := by
  unfold toCNFBounded at hv
  split_ifs at hv
  · exact mem_vars_toCNF hv
  · simp [CNF.vars] at hv

theorem relabel_toCNF (sem : Rel → List Bool → Bool) (f : V → W) (c : Constraint Rel V) :
    (toCNF sem c).relabel f = toCNF sem (relabel f c) := by
  simp only [toCNF, relabel, CNF.relabel, List.length_map, List.map_map, Function.comp_def,
    relabel_forbidClause]

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
  simp only [toCNF, List.mem_map, List.mem_filter, mem_enumBoolLists, Bool.not_eq_true']
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

/-! ### Boolean CSP instances, model counts, and CNF compilation -/

namespace CSP

variable {Rel V W : Type*}

/-- Evaluate a Boolean CSP instance under assignment `σ : V → Bool`. -/
def eval (sem : Rel → List Bool → Bool) (σ : V → Bool) (F : CSP Rel V) : Bool :=
  F.all (Constraint.eval sem σ)

/-- A Boolean CSP instance is satisfiable if some assignment satisfies all its constraints. -/
def Satisfiable (sem : Rel → List Bool → Bool) (F : CSP Rel V) : Prop :=
  ∃ σ : V → Bool, F.eval sem σ = true

/-- All variable occurrences across the constraint scopes of `F`, in order. -/
def vars (F : CSP Rel V) : List V :=
  F.flatMap Prod.snd

/-- Rename variables across all constraints in `F`. -/
def relabel (f : V → W) (F : CSP Rel V) : CSP Rel W :=
  F.map (Constraint.relabel f)

@[simp]
theorem vars_relabel (f : V → W) (F : CSP Rel V) :
    (F.relabel f).vars = F.vars.map f := by
  simp [vars, relabel, Constraint.relabel, List.flatMap_map, List.map_flatMap]

@[simp]
theorem eval_relabel (sem : Rel → List Bool → Bool) (f : V → W) (σ : W → Bool) (F : CSP Rel V) :
    (F.relabel f).eval sem σ = F.eval sem (σ ∘ f) := by
  simp [eval, relabel, List.all_map, Function.comp_def]

theorem eval_congr {sem : Rel → List Bool → Bool} {F : CSP Rel V} {σ τ : V → Bool}
    (h : ∀ v ∈ F.vars, σ v = τ v) :
    F.eval sem σ = F.eval sem τ := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    change (Constraint.eval sem σ c && eval sem σ F) =
      (Constraint.eval sem τ c && eval sem τ F)
    have hc := Constraint.eval_congr (sem := sem) (c := c) fun v hv =>
      h v (List.mem_flatMap.mpr ⟨c, List.mem_cons_self, hv⟩)
    have hF := ih fun v hv => by
      rcases List.mem_flatMap.mp hv with ⟨c', hc', hv'⟩
      exact h v (List.mem_flatMap.mpr ⟨c', List.mem_cons_of_mem c hc', hv'⟩)
    rw [hc, hF]

/-- Compile a Boolean CSP instance `F` to a CNF formula by concatenating the forbidden-assignment
clauses of each constraint. -/
def toCNF (sem : Rel → List Bool → Bool) (F : CSP Rel V) : CNF V :=
  F.flatMap (Constraint.toCNF sem)

/-- Width-guarded compilation of `F` to a `k`-CNF formula. -/
def toCNFBounded (k : ℕ) (sem : Rel → List Bool → Bool) (F : CSP Rel V) : CNF V :=
  F.flatMap (Constraint.toCNFBounded k sem)

theorem toCNFBounded_eq_toCNF {k : ℕ} {sem : Rel → List Bool → Bool} {F : CSP Rel V}
    (hF : ∀ c ∈ F, c.2.length ≤ k) :
    F.toCNFBounded k sem = F.toCNF sem :=
  List.flatMap_congr fun c hc => Constraint.toCNFBounded_eq_toCNF (hF c hc)

theorem length_clause_mem_toCNFBounded {k : ℕ} {sem : Rel → List Bool → Bool} {F : CSP Rel V}
    {cl : Clause V} (hcl : cl ∈ F.toCNFBounded k sem) :
    cl.length ≤ k := by
  rcases List.mem_flatMap.mp hcl with ⟨c, _, hcl'⟩
  exact Constraint.length_clause_mem_toCNFBounded hcl'

theorem length_clause_mem_toCNF {k : ℕ} {sem : Rel → List Bool → Bool} {F : CSP Rel V}
    (hF : ∀ c ∈ F, c.2.length ≤ k) {cl : Clause V} (hcl : cl ∈ F.toCNF sem) :
    cl.length ≤ k := by
  rw [← toCNFBounded_eq_toCNF hF] at hcl
  exact length_clause_mem_toCNFBounded hcl

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

theorem mem_vars_toCNF {sem : Rel → List Bool → Bool} {F : CSP Rel V} {v : V}
    (hv : v ∈ (F.toCNF sem).vars) : v ∈ F.vars := by
  simp only [toCNF, CNF.vars, List.mem_map, List.mem_flatten, List.mem_flatMap] at hv
  rcases hv with ⟨l, ⟨cl, ⟨c, hc, hcl⟩, hl⟩, rfl⟩
  rw [vars, List.mem_flatMap]
  refine ⟨c, hc, Constraint.mem_vars_toCNF (sem := sem) ?_⟩
  simp only [CNF.vars, List.mem_map, List.mem_flatten]
  exact ⟨l, ⟨cl, hcl, hl⟩, rfl⟩

theorem mem_vars_toCNFBounded {k : ℕ} {sem : Rel → List Bool → Bool} {F : CSP Rel V} {v : V}
    (hv : v ∈ (F.toCNFBounded k sem).vars) : v ∈ F.vars := by
  simp only [toCNFBounded, CNF.vars, List.mem_map, List.mem_flatten, List.mem_flatMap] at hv
  rcases hv with ⟨l, ⟨cl, ⟨c, hc, hcl⟩, hl⟩, rfl⟩
  rw [vars, List.mem_flatMap]
  refine ⟨c, hc, Constraint.mem_vars_toCNFBounded (k := k) (sem := sem) ?_⟩
  simp only [CNF.vars, List.mem_map, List.mem_flatten]
  exact ⟨l, ⟨cl, hcl, hl⟩, rfl⟩

theorem relabel_toCNF (sem : Rel → List Bool → Bool) (f : V → W) (F : CSP Rel V) :
    (F.toCNF sem).relabel f = (F.relabel f).toCNF sem := by
  simp only [toCNF, relabel, CNF.relabel, List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun c _ => ?_
  exact Constraint.relabel_toCNF sem f c

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

@[simp]
theorem satisfiable_toCNF (sem : Rel → List Bool → Bool) (F : CSP Rel V) :
    (F.toCNF sem).Satisfiable ↔ F.Satisfiable sem := by
  simp [CNF.Satisfiable, Satisfiable]

/-! ### Variable accounting, dense relabeling, and model counts -/

/-- Auxiliary positive-clause CNF sharing the exact variable-occurrence list `F.vars`. -/
def varCNF (F : CSP Rel V) : CNF V :=
  F.map fun c => c.2.map fun v => (v, true)

@[simp]
theorem vars_varCNF (F : CSP Rel V) :
    (F.varCNF).vars = F.vars := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    simp only [varCNF, List.map_cons, CNF.vars, List.flatten_cons, List.map_append,
      List.map_map, Function.comp_def, List.map_id', vars, List.flatMap_cons]
    exact congrArg (c.2 ++ ·) ih

variable [DecidableEq V] [DecidableEq W]

/-- Number of distinct variables occurring in `F`. -/
def numVars (F : CSP Rel V) : ℕ :=
  F.vars.toFinset.card

/-- Distinct variables of `F` in order of first occurrence. -/
def distinctVars (F : CSP Rel V) : List V :=
  selectDistinct F.vars (List.replicate F.vars.length true)

@[simp]
theorem numVars_varCNF (F : CSP Rel V) :
    F.varCNF.numVars = F.numVars := by
  simp [CNF.numVars, numVars]

@[simp]
theorem distinctVars_varCNF (F : CSP Rel V) :
    F.varCNF.distinctVars = F.distinctVars := by
  simp [CNF.distinctVars, distinctVars]

theorem mem_distinctVars {F : CSP Rel V} {v : V} :
    v ∈ F.distinctVars ↔ v ∈ F.vars :=
  mem_selectDistinct_replicate

theorem length_distinctVars (F : CSP Rel V) :
    F.distinctVars.length = F.numVars :=
  length_selectDistinct_replicate F.vars

/-- Rename each variable occurring in `F` by its first-occurrence index in `F.distinctVars`. -/
def denseRelabel (F : CSP Rel V) : CSP Rel ℕ :=
  F.relabel F.distinctVars.idxOf

@[simp]
theorem vars_denseRelabel_toFinset (F : CSP Rel V) :
    F.denseRelabel.vars.toFinset = Finset.range F.numVars := by
  have h := CNF.vars_dense_relabel F.varCNF
  simpa only [CNF.vars_relabel, vars_varCNF, distinctVars_varCNF, numVars_varCNF,
    denseRelabel, vars_relabel] using h

@[simp]
theorem numVars_denseRelabel (F : CSP Rel V) :
    F.denseRelabel.numVars = F.numVars := by
  rw [numVars, vars_denseRelabel_toFinset, Finset.card_range]

theorem all_length_le_denseRelabel {k : ℕ} (F : CSP Rel V) :
    (∀ c ∈ F.denseRelabel, c.2.length ≤ k) ↔ ∀ c ∈ F, c.2.length ≤ k := by
  simp only [denseRelabel, relabel, List.mem_map]
  constructor
  · intro h c hc
    have := h (Constraint.relabel F.distinctVars.idxOf c) ⟨c, hc, rfl⟩
    simpa [Constraint.relabel] using this
  · rintro h _ ⟨c, hc, rfl⟩
    simpa [Constraint.relabel] using h c hc

/-- Count assignments to `declared : Finset V` (extended by `false` outside `declared`) that satisfy
`F` under `sem`. -/
def modelCountOn (sem : Rel → List Bool → Bool) (F : CSP Rel V) (declared : Finset V) : ℕ :=
  (Finset.univ.filter fun σ : declared → Bool =>
    F.eval sem (fun v => if h : v ∈ declared then σ ⟨v, h⟩ else false) = true).card

/-- Count satisfying assignments on the occurring variables `F.vars.toFinset`. -/
def modelCount (sem : Rel → List Bool → Bool) (F : CSP Rel V) : ℕ :=
  F.modelCountOn sem F.vars.toFinset

/-- Forbidden-assignment CNF compilation preserves declared-variable model counts on every finite
variable set `declared` with multiplicity `1` (no auxiliary variables). -/
@[simp]
theorem modelCountOn_toCNF (sem : Rel → List Bool → Bool) (F : CSP Rel V) (declared : Finset V) :
    (F.toCNF sem).modelCountOn declared = F.modelCountOn sem declared := by
  simp [CNF.modelCountOn, modelCountOn]

/-- Dense variable relabeling preserves the occurring-variable model count on
`Finset.range F.numVars`. -/
theorem modelCountOn_denseRelabel (sem : Rel → List Bool → Bool) (F : CSP Rel V) :
    F.denseRelabel.modelCountOn sem (Finset.range F.numVars) = F.modelCount sem := by
  classical
  let S := F.vars.toFinset
  let R := Finset.range F.numVars
  have hinj : ∀ v ∈ S, ∀ w ∈ S, F.distinctVars.idxOf v = F.distinctVars.idxOf w → v = w := by
    intro v hv w _ h
    exact (List.idxOf_inj (mem_distinctVars.mpr (List.mem_toFinset.mp hv))).mp h
  have hmem_range : ∀ v ∈ S, F.distinctVars.idxOf v ∈ R := by
    intro v hv
    rw [Finset.mem_range, ← length_distinctVars]
    exact List.idxOf_lt_length_iff.mpr (mem_distinctVars.mpr (List.mem_toFinset.mp hv))
  have hsurj : ∀ i ∈ R, ∃ v, ∃ hv : v ∈ S, F.distinctVars.idxOf v = i := by
    intro i hi
    have hi' : i ∈ F.denseRelabel.vars.toFinset := by
      rwa [vars_denseRelabel_toFinset]
    rw [denseRelabel, vars_relabel, List.mem_toFinset, List.mem_map] at hi'
    rcases hi' with ⟨v, hv, rfl⟩
    exact ⟨v, List.mem_toFinset.mpr hv, rfl⟩
  let eVar : S ≃ R := Equiv.ofBijective
    (fun v => ⟨F.distinctVars.idxOf v.1, hmem_range v.1 v.2⟩)
    ⟨fun v w h => Subtype.ext (hinj v.1 v.2 w.1 w.2 (Subtype.mk.inj h)),
     fun i => by
       obtain ⟨v, hv, hvi⟩ := hsurj i.1 i.2
       exact ⟨⟨v, hv⟩, Subtype.ext hvi⟩⟩
  have heVar (v : V) (hvS : v ∈ S) :
      eVar ⟨v, hvS⟩ = ⟨F.distinctVars.idxOf v, hmem_range v hvS⟩ := rfl
  rw [modelCount, modelCountOn, modelCountOn]
  refine Finset.card_bij (fun (σ : R → Bool) _ => fun v : S => σ (eVar v))
    (fun σ hσ => ?_)
    (fun σ₁ _ σ₂ _ h => funext fun i => by
      have := congrFun h (eVar.symm i)
      simpa using this)
    (fun τ hτ => ⟨fun i => τ (eVar.symm i), ?_, funext fun v => by simp⟩)
  · rw [Finset.mem_filter] at hσ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [denseRelabel, eval_relabel] at hσ
    refine (eval_congr fun v hv => ?_).trans hσ.2
    have hvS : v ∈ S := List.mem_toFinset.mpr hv
    have hvR : F.distinctVars.idxOf v ∈ R := hmem_range v hvS
    change (if h : v ∈ S then σ (eVar ⟨v, h⟩) else false) =
      (if h : F.distinctVars.idxOf v ∈ R then σ ⟨F.distinctVars.idxOf v, h⟩ else false)
    simp only [hvS, hvR, dite_true, heVar]
  · rw [Finset.mem_filter] at hτ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [denseRelabel, eval_relabel]
    refine (eval_congr fun v hv => ?_).trans hτ.2
    have hvS : v ∈ S := List.mem_toFinset.mpr hv
    have hvR : F.distinctVars.idxOf v ∈ R := hmem_range v hvS
    change (if h : F.distinctVars.idxOf v ∈ R then
        τ (eVar.symm ⟨F.distinctVars.idxOf v, h⟩) else false) =
      (if h : v ∈ S then τ ⟨v, h⟩ else false)
    simp only [hvR, hvS, dite_true, ← heVar v hvS, Equiv.symm_apply_apply]

theorem modelCount_pos_iff {sem : Rel → List Bool → Bool} {F : CSP Rel V} :
    0 < F.modelCount sem ↔ F.Satisfiable sem := by
  rw [modelCount, modelCountOn, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨σ, -, hσ⟩
    exact ⟨_, hσ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨fun v => σ v.1, Finset.mem_univ _, ?_⟩
    refine (eval_congr fun v hv => ?_).trans hσ
    have hv' : v ∈ F.vars.toFinset := List.mem_toFinset.mpr hv
    simp [hv']

/-- Guard checking that every constraint scope in `F` has length `≤ k` and every occurring variable
lies in `< N`. -/
def validDeclaredCSP (k N : ℕ) (F : CSP Rel ℕ) : Bool :=
  (F.all fun c => decide (c.2.length ≤ k)) && (F.vars.all fun v => decide (v < N))

theorem validDeclaredCSP_eq_true_iff {k N : ℕ} {F : CSP Rel ℕ} :
    validDeclaredCSP k N F = true ↔
      (∀ c ∈ F, c.2.length ≤ k) ∧ F.vars.toFinset ⊆ Finset.range N := by
  simp only [validDeclaredCSP, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact and_congr_right' ⟨fun h _ hv => Finset.mem_range.mpr (h _ (List.mem_toFinset.mp hv)),
    fun h _ hv => Finset.mem_range.mp (h (List.mem_toFinset.mpr hv))⟩

theorem validDeclaredInput_toCNFBounded {k N : ℕ} (sem : Rel → List Bool → Bool) {F : CSP Rel ℕ}
    (hv : validDeclaredCSP k N F = true) :
    CNF.validDeclaredInput k N (F.toCNFBounded k sem) = true := by
  obtain ⟨_, hsub⟩ := validDeclaredCSP_eq_true_iff.mp hv
  refine CNF.validDeclaredInput_eq_true_iff.mpr
    ⟨fun cl hcl => length_clause_mem_toCNFBounded hcl, ?_⟩
  intro v hv'
  exact hsub (List.mem_toFinset.mpr (mem_vars_toCNFBounded (List.mem_toFinset.mp hv')))

/-- The bounded-arity Boolean CSP decision problem over relation semantics `sem`. -/
def KCSP (k : ℕ) (sem : Rel → List Bool → Bool) : Set (CSP Rel V) :=
  {F | (∀ c ∈ F, c.2.length ≤ k) ∧ F.Satisfiable sem}

/-! ### Polynomial-time compilation and subexponential counting/decision -/

section Complexity

variable {Rel V : Type}

open ComputableTidilyInPolyTime

private theorem computableTidilyInPolyTime_forbidClause (encV : V ↪ List Bool) :
    ComputableTidilyInPolyTime
      (fun p : List V × List Bool => Constraint.forbidClause p.1 p.2)
      (encPair (encList encV) (encList encBool))
      (encList (encPair encV encBool)) := by
  unfold Constraint.forbidClause
  fun_prop

private theorem computableTidilyInPolyTime_toCNFAt [Finite Rel] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (sem : Rel → List Bool → Bool) (r : ℕ) :
    ComputableTidilyInPolyTime
      (fun c : Constraint Rel V =>
        ((enumBoolLists r).filter fun w => !sem c.1 w).map (Constraint.forbidClause c.2))
      (encConstraint encRel encV)
      (encList (encList (encPair encV encBool))) := by
  have hforb : ComputableTidilyInPolyTime
      (fun c : Constraint Rel V => (enumBoolLists r).filter fun w => !sem c.1 w)
      (encConstraint encRel encV) (encList (encList encBool)) :=
    (of_finite (fun R : Rel => (enumBoolLists r).filter fun w => !sem R w)).comp
      (fst encRel (encList encV))
  have hbody : ComputableTidilyInPolyTime
      (fun p : Constraint Rel V × List Bool => Constraint.forbidClause p.1.2 p.2)
      (encPair (encConstraint encRel encV) (encList encBool))
      (encList (encPair encV encBool)) :=
    (computableTidilyInPolyTime_forbidClause encV).comp
      (((snd encRel (encList encV)).comp (fst _ _)).prod (snd _ _))
  exact mapWithInput hforb hbody

private theorem computableTidilyInPolyTime_constraintToCNFBounded [Finite Rel]
    (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool) :
    ComputableTidilyInPolyTime (Constraint.toCNFBounded k sem)
      (encConstraint encRel encV)
      (encList (encList (encPair encV encBool))) := by
  induction k with
  | zero =>
    have htest : ComputableTidilyInPolyTime
        (fun c : Constraint Rel V => decide (c.2.length = 0))
        (encConstraint encRel encV) encBool := by
      fun_prop
    refine (htest.cond (computableTidilyInPolyTime_toCNFAt encRel encV sem 0)
      (const [])).of_enc_eq fun c => ?_
    simp only [Constraint.toCNFBounded, Constraint.toCNF, Nat.le_zero]
    by_cases h : c.2.length = 0 <;> simp [h]
  | succ k ih =>
    have htest : ComputableTidilyInPolyTime
        (fun c : Constraint Rel V => decide (c.2.length = k + 1))
        (encConstraint encRel encV) encBool := by
      fun_prop
    refine (htest.cond (computableTidilyInPolyTime_toCNFAt encRel encV sem (k + 1))
      ih).of_enc_eq fun c => ?_
    simp only [Constraint.toCNFBounded, Constraint.toCNF]
    by_cases h1 : c.2.length = k + 1
    · simp [h1]
    · have hle : (c.2.length ≤ k + 1) ↔ (c.2.length ≤ k) := by omega
      simp [h1, hle]

/-- Width-guarded compilation of a Boolean CSP instance to a `k`-CNF formula is computable in
polynomial time for any finite relation alphabet `Rel` and any relation semantics `sem`. -/
@[fun_prop]
theorem computableInPolyTime_toCNFBounded [Finite Rel] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool) :
    ComputableInPolyTime (CSP.toCNFBounded k sem)
      (encCSP encRel encV)
      (encList (encList (encPair encV encBool))) := by
  refine .of_tidy ?_
  have hc := computableTidilyInPolyTime_constraintToCNFBounded encRel encV k sem
  exact (flatten (encList (encPair encV encBool))).comp (map hc)

@[fun_prop]
theorem computableInPolyTime_vars (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.vars (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList encV) := by
  refine .of_tidy ?_
  unfold CSP.vars
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
@[fun_prop]
theorem computableInPolyTime_varCNF (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.varCNF (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList (encList (encPair encV encBool))) := by
  refine .of_tidy ?_
  unfold CSP.varCNF
  fun_prop

attribute [local fun_prop] ComputableInPolyTime.tidy in
@[fun_prop]
theorem computableInPolyTime_distinctVars [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.distinctVars (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList encV) := by
  have heq : (CSP.distinctVars (Rel := Rel) (V := V)) = fun F => F.varCNF.distinctVars := by
    funext F
    exact (distinctVars_varCNF F).symm
  rw [heq]
  exact (CNF.computableInPolyTime_distinctVars encV).comp
    (computableInPolyTime_varCNF encRel encV)

attribute [local fun_prop] ComputableInPolyTime.tidy in
@[fun_prop]
theorem computableInPolyTime_numVars [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.numVars (Rel := Rel) (V := V))
      (encCSP encRel encV) encUnary := by
  have heq : (CSP.numVars (Rel := Rel) (V := V)) = fun F => F.varCNF.numVars := by
    funext F
    exact (numVars_varCNF F).symm
  rw [heq]
  exact (CNF.computableInPolyTime_numVars encV).comp
    (computableInPolyTime_varCNF encRel encV)

attribute [local fun_prop] ComputableInPolyTime.tidy in
@[fun_prop]
theorem computableInPolyTime_denseRelabel [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.denseRelabel (Rel := Rel) (V := V))
      (encCSP encRel encV) (encCSP encRel encNat) := by
  have hd : ComputableTidilyInPolyTime (CSP.distinctVars (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList encV) :=
    (computableInPolyTime_distinctVars encRel encV).tidy
  have hunary : ComputableTidilyInPolyTime (CSP.denseRelabel (Rel := Rel) (V := V))
      (encCSP encRel encV) (encCSP encRel encUnary) := by
    unfold CSP.denseRelabel CSP.relabel Constraint.relabel
    fun_prop
  have hbin : ComputableTidilyInPolyTime
      (CSP.relabel (Rel := Rel) (V := ℕ) (W := ℕ) (fun n => n))
      (encCSP encRel encUnary) (encCSP encRel encNat) := by
    unfold CSP.relabel Constraint.relabel
    fun_prop
  have heq : (CSP.denseRelabel (Rel := Rel) (V := V)) =
      fun F => (CSP.denseRelabel F).relabel (fun n => n) := by
    have hid : ∀ G : CSP Rel ℕ, G.relabel (fun n => n) = G := by
      intro G
      induction G with
      | nil => rfl
      | cons c G ih =>
        rcases c with ⟨r, vs⟩
        simp only [CSP.relabel, List.map_cons, Constraint.relabel, List.map_id']
        exact congrArg ((r, vs) :: ·) ih
    funext F
    exact (hid F.denseRelabel).symm
  rw [heq]
  exact .of_tidy (hbin.comp hunary)

attribute [local fun_prop] ComputableInPolyTime.tidy in
private theorem computableInPolyTime_validDeclaredCSP (encRel : Rel ↪ List Bool) (k : ℕ) :
    ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => validDeclaredCSP k x.1 x.2)
      (encPair encUnary (encCSP encRel encNat)) encBool := by
  have hN := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.fst encUnary (encCSP encRel encNat))
  have hlt : ComputableInPolyTime
      (fun p : (ℕ × CSP Rel ℕ) × ℕ => decide (p.2 < p.1.1))
      (encPair (encPair encUnary (encCSP encRel encNat)) encNat) encBool :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_lt).comp
      ((ComputableInPolyTime.snd _ _).prod (hN.comp (ComputableInPolyTime.fst _ _)))
  have hvars : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => x.2.vars.all fun v => decide (v < x.1))
      (encPair encUnary (encCSP encRel encNat)) encBool :=
    ComputableInPolyTime.allWithInput
      ((computableInPolyTime_vars encRel encNat).comp (ComputableInPolyTime.snd _ _)) hlt
  have hwidth : ComputableInPolyTime
      (fun x : ℕ × CSP Rel ℕ => x.2.all fun c => decide (c.2.length ≤ k))
      (encPair encUnary (encCSP encRel encNat)) encBool := by
    refine .of_tidy ?_
    fun_prop
  unfold validDeclaredCSP
  fun_prop

/-- General composition of `CountingNativeEndpoint.exists_declaredCounter` with any polynomial-time
reduction `g : α → ℕ × CNF ℕ` and polynomial-time validity guard `valid : α → Bool`. -/
theorem exists_counter_of_polyTime_toDeclared {α : Type} {encA : α ↪ List Bool} (k : ℕ)
    {g : α → ℕ × CNF ℕ} (hg : ComputableInPolyTime g encA (encPair encUnary encCNF))
    {valid : α → Bool} (hvalid : ComputableInPolyTime valid encA encBool)
    (hvalid_imp : ∀ x, valid x = true → CNF.validDeclaredInput k (g x).1 (g x).2 = true) :
    ∃ (count : α → ℕ) (T S : α → ℕ) (A c e a b : ℕ),
      ComputableInO count encA encNat T S ∧
      (∀ x, count x = if valid x then (g x).2.modelCountOn (Finset.range (g x).1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale (g x).1) *
        (((encA x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encA x).length + 1) ^ b) := by
  obtain ⟨count₀, T₀, S₀, A, c₀, e₀, a₀, b₀, hcount₀, hspec₀, hT₀, hS₀⟩ :=
    CountingNativeEndpoint.exists_declaredCounter k
  obtain ⟨dg, _, hdg⟩ := hg.tidy.exists_degree
  obtain ⟨dv, _, hdv⟩ := hvalid.tidy.exists_degree
  obtain ⟨p, q, hp⟩ := hg.polyBounded_length.exists_le
  have hcomp := hcount₀.comp (ComputableInO.of_tidy hdg.inO)
  have hite := (ComputableInO.of_tidy hdv.inO).ite hcomp (ComputableInO.const (encIn := encA) 0)
  let P (x : α) := ((encA x).length + 1) ^ dv + ((encA x).length + 1) ^ dg + (encA x).length
  let T (x : α) := P x + T₀ (g x)
  let S (x : α) := P x + S₀ (g x)
  refine ⟨fun x => if valid x then count₀ (g x) else 0, T, S, A,
    3 + c₀ * (p + 1) ^ e₀, dv + dg + 1 + q * e₀,
    3 + a₀ * (p + 1) ^ b₀, dv + dg + 1 + q * b₀,
    (hite.mono 1 (fun x => ?_) (fun x => ?_)).of_enc_eq (fun _ => rfl),
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · dsimp only [T, P]
    split_ifs <;> omega
  · dsimp only [S, P]
    split_ifs <;> omega
  · dsimp only
    split_ifs with hx
    · have hvalid' := hvalid_imp x hx
      simp [hspec₀ (g x), hvalid']
    · rfl
  · let Y : ℕ := (encA x).length + 1
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hlen : (encPair encUnary encCNF (g x)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encPair encUnary encCNF (g x)).length ≤ p * Y ^ q := hp x
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow _ _ hY1
      nlinarith
    have hpow : ((encPair encUnary encCNF (g x)).length + 1) ^ e₀ ≤
        (p + 1) ^ e₀ * Y ^ (q * e₀) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ e₀ := Nat.pow_le_pow_left hlen e₀
        _ = _ := by rw [mul_pow, pow_mul]
    let E := dv + dg + 1 + q * e₀
    have hP_le : P x ≤ 3 * Y ^ E := by
      have h1 : Y ^ dv ≤ Y ^ E := Nat.pow_le_pow_right hY1 (by dsimp [E]; omega)
      have h2 : Y ^ dg ≤ Y ^ E := Nat.pow_le_pow_right hY1 (by dsimp [E]; omega)
      have hE0 : E ≠ 0 := by dsimp [E]; omega
      have h3 : (encA x).length ≤ Y ^ E :=
        (Nat.le_succ _).trans (Nat.le_self_pow hE0 Y)
      change Y ^ dv + Y ^ dg + (encA x).length ≤ 3 * Y ^ E
      omega
    have hqe : Y ^ (q * e₀) ≤ Y ^ E := Nat.pow_le_pow_right hY1 (by dsimp [E]; omega)
    let X : ℝ := (2 : ℝ) ^ ((A : ℝ) * interpolationScale (g x).1)
    let YR : ℝ := ((encA x).length : ℝ) + 1
    have hYR_eq : (Y : ℝ) = YR := by dsimp [Y, YR]; push_cast; rfl
    have hX1 : (1 : ℝ) ≤ X :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg _))
    have hT₀_le : (T₀ (g x) : ℝ) ≤
        ((c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) * (X * YR ^ E) + c₀ := by
      have h0 := hT₀ (g x)
      have hpow_le : ((encPair encUnary encCNF (g x)).length + 1) ^ e₀ ≤
          (p + 1) ^ e₀ * Y ^ E := hpow.trans (Nat.mul_le_mul_left _ hqe)
      have hpowR : (((encPair encUnary encCNF (g x)).length : ℝ) + 1) ^ e₀ ≤
          (((p + 1) ^ e₀ : ℕ) : ℝ) * YR ^ E := by
        rw [← hYR_eq]
        exact_mod_cast hpow_le
      have h1 := mul_le_mul_of_nonneg_left hpowR (by positivity : (0 : ℝ) ≤ X)
      have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg c₀)
      have hcast : ((c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) = (c₀ : ℝ) * (((p + 1) ^ e₀ : ℕ) : ℝ) := by
        push_cast; rfl
      rw [hcast]
      linarith
    have hP_R : (P x : ℝ) ≤ 3 * (X * YR ^ E) := by
      have hPR : (P x : ℝ) ≤ 3 * YR ^ E := by
        rw [← hYR_eq]
        exact_mod_cast hP_le
      have hYR_nonneg : (0 : ℝ) ≤ YR ^ E := by dsimp [YR]; positivity
      have hXY : YR ^ E ≤ X * YR ^ E := le_mul_of_one_le_left hYR_nonneg hX1
      linarith
    have hc_le : (c₀ : ℝ) ≤ ((3 + c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) := by
      have : 1 ≤ (p + 1) ^ e₀ := Nat.one_le_pow _ _ (Nat.le_add_left 1 p)
      exact_mod_cast (by nlinarith : c₀ ≤ 3 + c₀ * (p + 1) ^ e₀)
    have hadd : (3 : ℝ) + ((c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) = ((3 + c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) := by
      push_cast; rfl
    change ((P x + T₀ (g x) : ℕ) : ℝ) ≤
      ((3 + c₀ * (p + 1) ^ e₀ : ℕ) : ℝ) * (X * YR ^ E) + ((3 + c₀ * (p + 1) ^ e₀ : ℕ) : ℝ)
    rw [Nat.cast_add, ← hadd, add_mul]
    linarith
  · let Y : ℕ := (encA x).length + 1
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hlen : (encPair encUnary encCNF (g x)).length + 1 ≤ (p + 1) * Y ^ q := by
      have h1 : (encPair encUnary encCNF (g x)).length ≤ p * Y ^ q := hp x
      have h2 : 1 ≤ Y ^ q := Nat.one_le_pow _ _ hY1
      nlinarith
    have hpow : ((encPair encUnary encCNF (g x)).length + 1) ^ b₀ ≤
        (p + 1) ^ b₀ * Y ^ (q * b₀) := by
      calc _ ≤ ((p + 1) * Y ^ q) ^ b₀ := Nat.pow_le_pow_left hlen b₀
        _ = _ := by rw [mul_pow, pow_mul]
    let B := dv + dg + 1 + q * b₀
    have hP_le : P x ≤ 3 * Y ^ B := by
      have h1 : Y ^ dv ≤ Y ^ B := Nat.pow_le_pow_right hY1 (by dsimp [B]; omega)
      have h2 : Y ^ dg ≤ Y ^ B := Nat.pow_le_pow_right hY1 (by dsimp [B]; omega)
      have hB0 : B ≠ 0 := by dsimp [B]; omega
      have h3 : (encA x).length ≤ Y ^ B :=
        (Nat.le_succ _).trans (Nat.le_self_pow hB0 Y)
      change Y ^ dv + Y ^ dg + (encA x).length ≤ 3 * Y ^ B
      omega
    have hqb : Y ^ (q * b₀) ≤ Y ^ B := Nat.pow_le_pow_right hY1 (by dsimp [B]; omega)
    have hS₀_le : S₀ (g x) ≤ a₀ * (p + 1) ^ b₀ * Y ^ B := by
      calc S₀ (g x) ≤ a₀ * ((encPair encUnary encCNF (g x)).length + 1) ^ b₀ := hS₀ (g x)
        _ ≤ a₀ * ((p + 1) ^ b₀ * Y ^ B) :=
            Nat.mul_le_mul_left a₀ (hpow.trans (Nat.mul_le_mul_left _ hqb))
        _ = a₀ * (p + 1) ^ b₀ * Y ^ B := by rw [Nat.mul_assoc]
    change P x + S₀ (g x) ≤ (3 + a₀ * (p + 1) ^ b₀) * Y ^ B
    rw [Nat.add_mul]
    omega

/-- **Declared-variable exact counting for bounded-arity Boolean `#CSP`.** For any finite relation
alphabet `Rel`, relation semantics `sem`, and arity bound `k`, one machine computes the exact
guarded declared-variable model count `F.modelCountOn sem (Finset.range N)` on every input
`(N, F) : ℕ × CSP Rel ℕ` in time `O(2 ^ (A * interpolationScale N) * (|x| + 1) ^ e)` and polynomial
space. -/
public theorem exists_declaredCounter [Finite Rel] (encRel : Rel ↪ List Bool) (k : ℕ)
    (sem : Rel → List Bool → Bool) :
    ∃ (count : ℕ × CSP Rel ℕ → ℕ) (T S : ℕ × CSP Rel ℕ → ℕ) (A c e a b : ℕ),
      ComputableInO count (encPair encUnary (encCSP encRel encNat)) encNat T S ∧
      (∀ x, count x = if validDeclaredCSP k x.1 x.2 then
        x.2.modelCountOn sem (Finset.range x.1) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale x.1) *
        (((encPair encUnary (encCSP encRel encNat) x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encPair encUnary (encCSP encRel encNat) x).length + 1) ^ b) := by
  let g (x : ℕ × CSP Rel ℕ) : ℕ × CNF ℕ := (x.1, x.2.toCNFBounded k sem)
  have hg : ComputableInPolyTime g
      (encPair encUnary (encCSP encRel encNat)) (encPair encUnary encCNF) := by
    have h1 := ComputableInPolyTime.fst encUnary (encCSP encRel encNat)
    have h2 := (computableInPolyTime_toCNFBounded encRel encNat k sem).comp
      (ComputableInPolyTime.snd encUnary (encCSP encRel encNat))
    exact h1.prod h2
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ :=
    exists_counter_of_polyTime_toDeclared k hg (computableInPolyTime_validDeclaredCSP encRel k)
      (fun x hx => validDeclaredInput_toCNFBounded sem hx)
  refine ⟨count, T, S, A, c, e, a, b, hcount, fun x => ?_, hT, hS⟩
  rw [hspec x]
  split_ifs with hx
  · obtain ⟨hw, _⟩ := validDeclaredCSP_eq_true_iff.mp hx
    simp only [g, toCNFBounded_eq_toCNF hw, modelCountOn_toCNF]
  · rfl

/-- **Occurring-variable exact counting for bounded-arity Boolean `#CSP`.** For any finite relation
alphabet `Rel`, variable encoding `encV`, relation semantics `sem`, and arity bound `k`, one
machine computes `F.modelCount sem` on every instance `F : CSP Rel V` of constraint arity `≤ k` in
time `O(2 ^ (A * interpolationScale F.numVars) * (|F| + 1) ^ e)` and polynomial space. -/
public theorem exists_modelCounter [Finite Rel] [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool) :
    ∃ (count : CSP Rel V → ℕ) (T S : CSP Rel V → ℕ) (A c e a b : ℕ),
      ComputableInO count (encCSP encRel encV) encNat T S ∧
      (∀ F : CSP Rel V, (∀ c ∈ F, c.2.length ≤ k) → count F = F.modelCount sem) ∧
      (∀ F : CSP Rel V, (T F : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale F.numVars) *
        (((encCSP encRel encV F).length : ℝ) + 1) ^ e) + c) ∧
      (∀ F : CSP Rel V, S F ≤ a * ((encCSP encRel encV F).length + 1) ^ b) := by
  let g (F : CSP Rel V) : ℕ × CNF ℕ :=
    (F.numVars, F.denseRelabel.toCNFBounded k sem)
  have hg : ComputableInPolyTime g (encCSP encRel encV) (encPair encUnary encCNF) :=
    (computableInPolyTime_numVars encRel encV).prod
      ((computableInPolyTime_toCNFBounded encRel encNat k sem).comp
        (computableInPolyTime_denseRelabel encRel encV))
  let valid (F : CSP Rel V) : Bool := F.all fun c => decide (c.2.length ≤ k)
  have hvalid : ComputableInPolyTime valid (encCSP encRel encV) encBool := by
    refine .of_tidy ?_
    unfold valid
    fun_prop
  have hvalid_imp (F : CSP Rel V) (hF : valid F = true) :
      CNF.validDeclaredInput k (g F).1 (g F).2 = true := by
    apply validDeclaredInput_toCNFBounded sem
    rw [validDeclaredCSP_eq_true_iff]
    simp only [valid, List.all_eq_true, decide_eq_true_eq] at hF
    exact ⟨(all_length_le_denseRelabel F).mpr hF, by rw [vars_denseRelabel_toFinset]⟩
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ :=
    exists_counter_of_polyTime_toDeclared k hg hvalid hvalid_imp
  refine ⟨count, T, S, A, c, e, a, b, hcount, fun F hF => ?_, hT, hS⟩
  have hv : valid F = true := by
    simp only [valid, List.all_eq_true, decide_eq_true_eq]
    exact hF
  have hd : ∀ c ∈ F.denseRelabel, c.2.length ≤ k := (all_length_le_denseRelabel F).mpr hF
  simp only [hspec F, hv, ite_true, g, toCNFBounded_eq_toCNF hd, modelCountOn_toCNF,
    modelCountOn_denseRelabel]

/-- **Subexponential-time decision for bounded-arity Boolean `CSP`.** For any finite relation
alphabet `Rel`, variable encoding `encV`, relation semantics `sem`, and arity bound `k`,
`CSP.KCSP k sem` is decidable in subexponential time in the number of occurring variables
`CSP.numVars`. -/
public theorem decidableInSubexpTime_KCSP [Finite Rel] [DecidableEq V] (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) (k : ℕ) (sem : Rel → List Bool → Bool) :
    DecidableInSubexpTime (KCSP k sem) (encCSP encRel encV) CSP.numVars := by
  let f (F : CSP Rel V) : CNF ℕ := (F.toCNFBounded k sem).denseRelabel
  have hf : ComputableInPolyTime f (encCSP encRel encV) encCNF :=
    (CNF.computableInPolyTime_denseRelabel encV).comp
      (computableInPolyTime_toCNFBounded encRel encV k sem)
  have hB : DecidableInSubexpTime {F : CSP Rel V | f F ∈ KSAT k}
      (encCSP encRel encV) CSP.numVars :=
    (CountingNativeEndpoint.decidableInSubexpTime_KSAT k).of_reduction hf (fun _ => Iff.rfl)
      (c := 1) fun F => by
        have hsub : (F.toCNFBounded k sem).vars.toFinset ⊆ F.vars.toFinset := by
          intro v hv
          exact List.mem_toFinset.mpr (mem_vars_toCNFBounded (List.mem_toFinset.mp hv))
        have hle : (F.toCNFBounded k sem).numVars ≤ F.numVars := Finset.card_le_card hsub
        simp only [f, CNF.numVars_denseRelabel]
        omega
  have hwidth : ComputableInPolyTime
      (fun F : CSP Rel V => F.all fun c => decide (c.2.length ≤ k))
      (encCSP encRel encV) encBool := by
    refine .of_tidy ?_
    fun_prop
  intro δ hδ
  have hKCSP_eq : KCSP k sem =
      {F : CSP Rel V | (F.all fun c => decide (c.2.length ≤ k)) = true} ∩
      {F : CSP Rel V | f F ∈ KSAT k} := by
    ext F
    simp only [KCSP, f, KSAT, Set.mem_inter_iff, Set.mem_ofPred_eq,
      CNF.all_length_le_denseRelabel, CNF.satisfiable_denseRelabel,
      List.all_eq_true, decide_eq_true_eq]
    refine and_congr_right fun hF => ?_
    rw [toCNFBounded_eq_toCNF hF, satisfiable_toCNF]
    exact ⟨fun hsat => ⟨fun cl hcl => length_clause_mem_toCNF hF hcl, hsat⟩, And.right⟩
  rw [hKCSP_eq]
  exact (hB δ hδ).inter hwidth hδ.le

end Complexity

end CSP

end Cslib.Complexity
