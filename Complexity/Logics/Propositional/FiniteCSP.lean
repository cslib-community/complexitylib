/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Nat.Log
public import Complexity.Logics.Propositional.CNF
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared

/-!
# Finite-domain constraint satisfaction problems

This module formalizes constraint satisfaction problems (CSPs) over fixed finite domains
and their canonical reduction to conjunctive normal form (CNF) via binary encoding of variables
([OpenAI2026ETH], Corollary C.2).

Each variable in a domain of size `q` is encoded by `b = max 1 (Nat.clog 2 q)` Boolean variables.
Unused bit patterns in `[q, 2^b)` are ruled out by unused-code clauses of width `b`. Each forbidden
domain tuple of arity `r` is translated to a clause of width `r * b`. When every constraint has
arity at most `k`, the compiled CNF formula has clause width bounded by `max 1 k * b`, and the
number of satisfying assignments on declared variables is exactly preserved.

## Main definitions

* `Cslib.Logic.PL.FiniteCSP.Constraint`: a local constraint specifying scoped variables,
  forbidden value tuples, and arity.
* `Cslib.Logic.PL.FiniteCSP.CSP`: a finite collection of constraints over a variable type `V`.
* `Cslib.Logic.PL.FiniteCSP.bitWidth`: the number of bits `b = max 1 (Nat.clog 2 q)` for domain `q`.
* `Cslib.Logic.PL.FiniteCSP.bitsToNat`, `Cslib.Logic.PL.FiniteCSP.natToBits`: little-endian binary
  conversion for natural numbers.
* `Cslib.Logic.PL.FiniteCSP.toCNF`: canonical polynomial-time compilation of a finite-domain CSP
  with `n` variables into a CNF formula.
* `Cslib.Logic.PL.FiniteCSP.modelCountOn`: count of domain assignments on a declared finite set
  of variables that satisfy the CSP.

## Main results

* `Cslib.Logic.PL.FiniteCSP.all_length_le_toCNF`: clause width bound `max 1 k * bitWidth q`.
* `Cslib.Logic.PL.FiniteCSP.vars_toCNF_subset`: variables bounded by `n * bitWidth q`.
* `Cslib.Logic.PL.FiniteCSP.validDeclaredInput_toCNF`: compiled formula satisfies the native
  declared-variable counting guard `validDeclaredInput`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.2, Corollary C.2.
-/

@[expose] public section

namespace Cslib.Logic.PL.FiniteCSP

open Cslib.Logic.PL

/-- A local constraint over variables in `V` with domain values in `ℕ`. -/
structure Constraint (V : Type*) where
  /-- Scoped variable list. -/
  vars : List V
  /-- Forbidden tuples of domain values. -/
  forbidden : List (List ℕ)
  /-- Arity of the constraint. -/
  arity : Nat
  /-- Every forbidden tuple has length equal to the arity. -/
  valid : ∀ α ∈ forbidden, α.length = arity

/-- A constraint satisfaction problem is a list of local constraints. -/
abbrev CSP (V : Type*) := List (Constraint V)

/-- Evaluate a constraint under a variable assignment `τ : V → ℕ`. -/
def Constraint.eval {V : Type*} (c : Constraint V) (τ : V → ℕ) : Bool :=
  decide ((c.vars.map τ) ∉ c.forbidden)

/-- Evaluate a CSP under a variable assignment `τ : V → ℕ`. -/
def CSP.eval {V : Type*} (φ : CSP V) (τ : V → ℕ) : Bool :=
  φ.all (·.eval τ)

/-- A constraint is valid for domain size `q` if all forbidden values are `< q` and the variable
scope has length matching the arity. -/
def Constraint.Valid {V : Type*} (q : ℕ) (c : Constraint V) : Prop :=
  (∀ α ∈ c.forbidden, ∀ x ∈ α, x < q) ∧ c.vars.length = c.arity

/-- A CSP is valid for domain size `q` if every constraint is valid. -/
def CSP.Valid {V : Type*} (q : ℕ) (φ : CSP V) : Prop :=
  ∀ c ∈ φ, c.Valid q

/-- A constraint has width at most `k` if its arity is at most `k`. -/
def Constraint.HasWidth {V : Type*} (k : ℕ) (c : Constraint V) : Prop :=
  c.arity ≤ k

/-- A CSP has width at most `k` if every constraint has width at most `k`. -/
def CSP.HasWidth {V : Type*} (k : ℕ) (φ : CSP V) : Prop :=
  ∀ c ∈ φ, c.HasWidth k

/-- Count assignments of `declared` into `Fin q` satisfying `φ`, extending by 0 outside
the declared set. -/
def CSP.modelCountOn {V : Type*} [DecidableEq V] (φ : CSP V) (q : ℕ) (declared : Finset V) : ℕ :=
  (Finset.univ.filter fun σ : declared → Fin q =>
    φ.eval (fun v => if h : v ∈ declared then (σ ⟨v, h⟩).val else 0) = true).card

/-! ### Binary encoding and conversions -/

/-- The number of bits needed to encode a domain of size `q`. Always at least 1. -/
def bitWidth (q : ℕ) : ℕ := max 1 (Nat.clog 2 q)

theorem one_le_bitWidth (q : ℕ) : 1 ≤ bitWidth q :=
  le_max_left 1 (Nat.clog 2 q)

theorem le_two_pow_bitWidth (q : ℕ) : q ≤ 2 ^ bitWidth q := by
  dsimp [bitWidth]
  cases q with
  | zero => decide
  | succ q' =>
    have hle : Nat.clog 2 (q' + 1) ≤ max 1 (Nat.clog 2 (q' + 1)) := le_max_right _ _
    exact (Nat.le_pow_clog (by decide) (q' + 1)).trans (Nat.pow_le_pow_right (by decide) hle)

/-- Decode a little-endian bit list to a natural number. -/
def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

/-- Encode a natural number to a little-endian bit list of specified length `b`. -/
def natToBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | b + 1, x => (x % 2 == 1) :: natToBits b (x / 2)

@[simp]
theorem natToBits_length (b x : ℕ) : (natToBits b x).length = b := by
  induction b generalizing x with
  | zero => rfl
  | succ b ih => simp [natToBits, ih]

theorem bitsToNat_lt_two_pow (l : List Bool) : bitsToNat l < 2 ^ l.length := by
  induction l with
  | nil => decide
  | cons b bs ih =>
    dsimp [bitsToNat, List.length]
    have h : (if b then 1 else 0) ≤ 1 := by split <;> decide
    omega

theorem natToBits_bitsToNat (l : List Bool) : natToBits l.length (bitsToNat l) = l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    dsimp [bitsToNat, List.length, natToBits]
    have hmod : ((if b then 1 else 0) + 2 * bitsToNat bs) % 2 = if b then 1 else 0 := by
      rw [Nat.add_comm, Nat.mul_add_mod]
      split <;> decide
    have hdiv : ((if b then 1 else 0) + 2 * bitsToNat bs) / 2 = bitsToNat bs := by
      rw [Nat.add_comm, Nat.mul_add_div (by decide)]
      have : (if b then 1 else 0) / 2 = 0 := by split <;> decide
      omega
    have hbool : (((if b then 1 else 0) + 2 * bitsToNat bs) % 2 == 1) = b := by
      rw [hmod]
      cases b <;> decide
    rw [hbool, hdiv, ih]

theorem bitsToNat_natToBits {b x : ℕ} (hx : x < 2 ^ b) : bitsToNat (natToBits b x) = x := by
  induction b generalizing x with
  | zero =>
    have : x = 0 := by omega
    subst this; rfl
  | succ b ih =>
    dsimp [natToBits, bitsToNat]
    have hlt : x / 2 < 2 ^ b := by
      rw [Nat.pow_succ, Nat.mul_comm] at hx
      exact Nat.div_lt_of_lt_mul hx
    rw [ih hlt]
    have hcond : (if (x % 2 == 1) then 1 else 0) = x % 2 := by
      have : x % 2 < 2 := Nat.mod_lt x (by decide)
      cases h : x % 2 with
      | zero => decide
      | succ n =>
        cases n with
        | zero => decide
        | succ n => omega
    rw [hcond]
    omega

theorem natToBits_inj {b x y : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b)
    (h : natToBits b x = natToBits b y) : x = y := by
  have hx' := bitsToNat_natToBits hx
  have hy' := bitsToNat_natToBits hy
  rw [← hx', ← hy', h]

/-! ### CNF compilation -/

/-- Clause forbidding an exact truth assignment `α` on `vars`. -/
def forbiddenClause {V : Type*} (vars : List V) (α : List Bool) : Clause V :=
  (vars.zip α).map (fun (v, b) => (v, !b))

theorem forbiddenClause_length {V : Type*} (vars : List V) (α : List Bool)
    (h : vars.length = α.length) : (forbiddenClause vars α).length = vars.length := by
  simp [forbiddenClause, h]

theorem mem_of_mem_zip {α β : Type*} {l1 : List α} {l2 : List β} {x : α} {y : β}
    (h : (x, y) ∈ l1.zip l2) : x ∈ l1 := by
  induction l1 generalizing l2 with
  | nil => cases h
  | cons a as ih =>
    cases l2 with
    | nil => cases h
    | cons b bs =>
      simp only [List.zip_cons_cons, List.mem_cons] at h ⊢
      cases h with
      | inl heq => injection heq with hx _; left; exact hx
      | inr hmem => right; exact ih hmem

theorem mem_vars_forbiddenClause {V : Type*} {vars : List V} {α : List Bool} {v : V} {b : Bool}
    (h : (v, b) ∈ forbiddenClause vars α) : v ∈ vars := by
  simp only [forbiddenClause, List.mem_map] at h
  obtain ⟨⟨x, y⟩, hxy, heq⟩ := h
  dsimp at heq
  injection heq with hx _
  subst hx
  exact mem_of_mem_zip hxy

theorem forbiddenClause_eval_eq_false_iff {V : Type*} (σ : V → Bool)
    (vars : List V) (α : List Bool) (hlen : vars.length = α.length) :
    Clause.eval σ (forbiddenClause vars α) = false ↔ vars.map σ = α := by
  induction vars generalizing α with
  | nil =>
    cases α with
    | nil => simp [forbiddenClause, Clause.eval]
    | cons a as => contradiction
  | cons v vars ih =>
    cases α with
    | nil => contradiction
    | cons a as =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [forbiddenClause, List.zip_cons_cons, List.map_cons, Clause.eval,
        List.any_cons, Bool.or_eq_false_iff, List.map_cons, List.cons.injEq]
      dsimp [Literal.eval]
      have hlit : (σ v == !a) = false ↔ σ v = a := by
        cases σ v <;> cases a <;> decide
      have hih := ih as hlen
      dsimp [Clause.eval, forbiddenClause] at hih
      rw [hlit, hih]

/-- The `b` bit variables corresponding to a domain variable `v`. -/
def varBits (v : ℕ) (b : ℕ) : List ℕ :=
  (List.range b).map (fun j => v * b + j)

@[simp]
theorem varBits_length (v b : ℕ) : (varBits v b).length = b := by
  simp [varBits]

theorem mem_varBits_iff (v b : ℕ) (x : ℕ) :
    x ∈ varBits v b ↔ ∃ j < b, x = v * b + j := by
  simp only [varBits, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

/-- Unused-code clauses for variable `v`: forbids bit patterns in `[q, 2^b)`. -/
def unusedCodeClauses (v : ℕ) (q : ℕ) (b : ℕ) : CNF ℕ :=
  ((List.range (2 ^ b - q)).map (fun i => q + i)).map (fun u =>
    forbiddenClause (varBits v b) (natToBits b u))

theorem unusedCodeClauses_all_length_le (v q b : ℕ) :
    ∀ c ∈ unusedCodeClauses v q b, c.length ≤ b := by
  intro c hc
  simp only [unusedCodeClauses, List.mem_map] at hc
  obtain ⟨u, _, rfl⟩ := hc
  rw [forbiddenClause_length]
  · simp
  · rw [varBits_length, natToBits_length]

/-- Compile all unused code clauses for variables in `range n`. -/
def allUnusedCodeClauses (n : ℕ) (q : ℕ) (b : ℕ) : CNF ℕ :=
  (List.range n).flatMap (fun v => unusedCodeClauses v q b)

theorem allUnusedCodeClauses_all_length_le (n q b : ℕ) :
    ∀ c ∈ allUnusedCodeClauses n q b, c.length ≤ b := by
  intro c hc
  simp only [allUnusedCodeClauses, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨v, _, hv⟩ := hc
  exact unusedCodeClauses_all_length_le v q b c hv

/-- Compile a single constraint into CNF clauses. -/
def constraintToCNF (c : Constraint ℕ) (b : ℕ) : CNF ℕ :=
  let scopeBits := c.vars.flatMap (fun v => varBits v b)
  c.forbidden.map (fun tuple =>
    forbiddenClause scopeBits (tuple.flatMap (fun val => natToBits b val)))

theorem length_flatMap_const {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ x ∈ l, (f x).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hx : (f x).length = k := h x (List.mem_cons.mpr (Or.inl rfl))
    have hxs : (xs.flatMap f).length = xs.length * k :=
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))
    rw [hx, hxs, Nat.add_comm, Nat.add_mul, Nat.one_mul]

theorem constraintToCNF_all_length_le (c : Constraint ℕ) (b : ℕ)
    (hvalid : c.vars.length = c.arity) :
    ∀ cl ∈ constraintToCNF c b, cl.length = c.arity * b := by
  intro cl hcl
  simp only [constraintToCNF, List.mem_map] at hcl
  obtain ⟨tuple, htuple, rfl⟩ := hcl
  rw [forbiddenClause_length]
  · rw [length_flatMap_const _ (fun v => varBits v b) b (fun _ _ => varBits_length _ _), hvalid]
  · rw [length_flatMap_const _ (fun v => varBits v b) b (fun _ _ => varBits_length _ _),
      length_flatMap_const _ (fun v => natToBits b v) b (fun _ _ => natToBits_length _ _),
      c.valid tuple htuple, hvalid]

/-- Compile a finite-domain CSP with `n` variables and domain size `q` into CNF. -/
def toCNF (φ : CSP ℕ) (q : ℕ) (n : ℕ) : CNF ℕ :=
  let b := bitWidth q
  allUnusedCodeClauses n q b ++ φ.flatMap (fun c => constraintToCNF c b)

theorem all_length_le_toCNF (φ : CSP ℕ) (q : ℕ) (n : ℕ) (k : ℕ) (hφ : φ.HasWidth k)
    (hvalid : ∀ c ∈ φ, c.vars.length = c.arity) :
    ∀ c ∈ toCNF φ q n, c.length ≤ max 1 k * bitWidth q := by
  intro c hc
  simp only [toCNF, List.mem_append, List.mem_flatMap] at hc
  rcases hc with h | ⟨constr, hconstr, hcl⟩
  · have hle := allUnusedCodeClauses_all_length_le n q (bitWidth q) c h
    have h1 : 1 ≤ max 1 k := le_max_left 1 k
    have h2 : bitWidth q ≤ max 1 k * bitWidth q := by
      calc bitWidth q = 1 * bitWidth q := by rw [Nat.one_mul]
      _ ≤ max 1 k * bitWidth q := Nat.mul_le_mul_right (bitWidth q) h1
    exact hle.trans h2
  · have hlen := constraintToCNF_all_length_le constr (bitWidth q) (hvalid constr hconstr) c hcl
    rw [hlen]
    have har : constr.arity ≤ max 1 k := (hφ constr hconstr).trans (le_max_right 1 k)
    exact Nat.mul_le_mul_right (bitWidth q) har

theorem vars_toCNF_subset (φ : CSP ℕ) (q : ℕ) (n : ℕ)
    (hvars : ∀ c ∈ φ, ∀ v ∈ c.vars, v < n) :
    ∀ v ∈ (toCNF φ q n).vars, v < n * bitWidth q := by
  intro v hv
  rw [CNF.mem_vars] at hv
  obtain ⟨c, hc, b, hb⟩ := hv
  simp only [toCNF, List.mem_append, List.mem_flatMap] at hc
  cases hc with
  | inl hc =>
    simp only [allUnusedCodeClauses, List.mem_flatMap, List.mem_range] at hc
    obtain ⟨u, hu, hcu⟩ := hc
    simp only [unusedCodeClauses, List.mem_map] at hcu
    obtain ⟨val, _, rfl⟩ := hcu
    have hv_varBits := mem_vars_forbiddenClause hb
    simp only [varBits, List.mem_map, List.mem_range] at hv_varBits
    obtain ⟨j, hj, rfl⟩ := hv_varBits
    have hu_le : u + 1 ≤ n := hu
    have h1 : (u + 1) * bitWidth q ≤ n * bitWidth q := Nat.mul_le_mul_right (bitWidth q) hu_le
    have h2 : u * bitWidth q + j < (u + 1) * bitWidth q := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left hj _
    exact h2.trans_le h1
  | inr hc =>
    obtain ⟨constr, hconstr, hcl⟩ := hc
    simp only [constraintToCNF, List.mem_map] at hcl
    obtain ⟨tuple, _, rfl⟩ := hcl
    have hv_scope := mem_vars_forbiddenClause hb
    simp only [List.mem_flatMap] at hv_scope
    obtain ⟨u, hu, hv_varBits⟩ := hv_scope
    simp only [varBits, List.mem_map, List.mem_range] at hv_varBits
    obtain ⟨j, hj, rfl⟩ := hv_varBits
    have hu' := hvars constr hconstr u hu
    have hu_le : u + 1 ≤ n := hu'
    have h1 : (u + 1) * bitWidth q ≤ n * bitWidth q := Nat.mul_le_mul_right (bitWidth q) hu_le
    have h2 : u * bitWidth q + j < (u + 1) * bitWidth q := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left hj _
    exact h2.trans_le h1

theorem validDeclaredInput_toCNF (φ : CSP ℕ) (q : ℕ) (n : ℕ) (k : ℕ)
    (hφ : φ.HasWidth k) (hvalid : ∀ c ∈ φ, c.vars.length = c.arity)
    (hvars : ∀ c ∈ φ, ∀ v ∈ c.vars, v < n) :
    CNF.validDeclaredInput (max 1 k * bitWidth q) (n * bitWidth q) (toCNF φ q n) = true := by
  rw [CNF.validDeclaredInput_eq_true_iff]
  refine ⟨all_length_le_toCNF φ q n k hφ hvalid, ?_⟩
  intro v hv
  rw [Finset.mem_range]
  exact vars_toCNF_subset φ q n hvars v (List.mem_toFinset.mp hv)

end Cslib.Logic.PL.FiniteCSP
