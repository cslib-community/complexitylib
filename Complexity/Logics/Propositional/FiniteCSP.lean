/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Nat.Log
public import Complexity.Logics.Propositional.CSP

/-!
# Finite-domain constraint satisfaction problems and Boolean reduction

This module formalizes the canonical reduction from finite-domain constraint satisfaction
problems (CSPs) over domain size `q` to Boolean CSPs ([OpenAI2026ETH], Corollary C.2).

Each domain variable in a domain of size `q` is encoded by `b = max 1 (Nat.clog 2 q)` Boolean
variables. Unused bit patterns in `[q, 2^b)` are ruled out by domain-validity constraints of
scope length `b` for each declared variable `v < N`. Original constraints of arity `r` are
translated to Boolean constraints of scope length `r * b`. When every constraint has arity at
most `k`, the compiled Boolean CSP has constraint scope lengths bounded by `max 1 k * b`, and
the number of satisfying assignments on declared variables is exactly preserved.

## Main definitions

* `Cslib.Logic.PL.FiniteCSP.bitWidth`: the number of bits `b = max 1 (Nat.clog 2 q)` for domain `q`.
* `Cslib.Logic.PL.FiniteCSP.bitsToNat`, `Cslib.Logic.PL.FiniteCSP.natToBits`: little-endian binary
  conversion for natural numbers.
* `Cslib.Logic.PL.FiniteCSP.bitScope`: the list of `b` Boolean variables representing domain
  variable `v`.
* `Cslib.Logic.PL.FiniteCSP.decodeChunks`: extract decoded natural numbers from chunked bit lists.
* `Cslib.Logic.PL.FiniteCSP.toFin`: clamped conversion of natural numbers into `Fin q`.
* `Cslib.Logic.PL.FiniteCSP.semBoolean`: the Boolean semantics evaluating domain-validity (`none`)
  and original relation (`some R`) constraints.
* `Cslib.Logic.PL.FiniteCSP.toBooleanCSP`: compilation of a finite-domain CSP on declared
  variables `0, …, N - 1` into an equivalent Boolean CSP.

## Main results

* `Cslib.Logic.PL.FiniteCSP.all_length_le_toBooleanCSP`: constraint scope length bound
  `max 1 k * bitWidth q`.
* `Cslib.Logic.PL.FiniteCSP.vars_toBooleanCSP_subset`: all variables bounded by `N * bitWidth q`.
* `Cslib.Logic.PL.FiniteCSP.modelCountOn_toBooleanCSP`: exact equality of declared-variable model
  counts between the finite-domain CSP and its Boolean compilation.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.2, Corollary C.2.
-/

@[expose] public section

namespace Cslib.Logic.PL.FiniteCSP

open Cslib.Logic.PL

variable {Rel : Type*}

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

/-! ### Variable scopes and chunk decoding -/

/-- The `b` Boolean variables representing domain variable `v`. -/
def bitScope (b : ℕ) (v : ℕ) : List ℕ :=
  (List.range b).map (fun j => v * b + j)

@[simp]
theorem bitScope_length (b v : ℕ) : (bitScope b v).length = b := by
  simp [bitScope]

theorem mem_bitScope_iff (b v x : ℕ) :
    x ∈ bitScope b v ↔ ∃ j < b, x = v * b + j := by
  simp only [bitScope, List.mem_map, List.mem_range, eq_comm]

theorem bitScope_subset_range {b v N : ℕ} (hv : v < N) :
    ∀ x ∈ bitScope b v, x < N * b := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := (mem_bitScope_iff b v x).mp hx
  have h1 : (v + 1) * b ≤ N * b := Nat.mul_le_mul_right b (by omega)
  have h2 : v * b + j < (v + 1) * b := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  exact h2.trans_le h1

/-- Decode a list of bits into `r` natural numbers by taking successive chunks of width `b`. -/
def decodeChunks (b : ℕ) : ℕ → List Bool → List ℕ
  | 0, _ => []
  | r + 1, bs => bitsToNat (bs.take b) :: decodeChunks b r (bs.drop b)

@[simp]
theorem decodeChunks_zero (b : ℕ) (bs : List Bool) : decodeChunks b 0 bs = [] := rfl

@[simp]
theorem decodeChunks_length (b : ℕ) (r : ℕ) (bs : List Bool) :
    (decodeChunks b r bs).length = r := by
  induction r generalizing bs with
  | zero => rfl
  | succ r ih => simp [decodeChunks, ih]

theorem decodeChunks_flatMap (b : ℕ) {α : Type*} (vs : List α) (f : α → List Bool)
    (hf : ∀ v ∈ vs, (f v).length = b) :
    decodeChunks b vs.length (vs.flatMap f) = vs.map (bitsToNat ∘ f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hfv : (f v).length = b := hf v (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ w ∈ vs, (f w).length = b := fun w hw => hf w (List.mem_cons.mpr (Or.inr hw))
    simp only [List.flatMap_cons, List.length_cons, decodeChunks, List.map_cons,
      Function.comp_apply]
    rw [List.take_append_of_le_length (le_of_eq hfv.symm),
      List.drop_append_of_le_length (le_of_eq hfv.symm)]
    have htake : List.take b (f v) = f v := by rw [← hfv, List.take_length]
    have hdrop : List.drop b (f v) = [] := by rw [← hfv, List.drop_length]
    rw [htake, hdrop, List.nil_append, ih hrest]

/-- Clamped conversion from natural numbers into `Fin q`. -/
def toFin (q : ℕ) (hq : 0 < q) (x : ℕ) : Fin q :=
  if h : x < q then ⟨x, h⟩ else ⟨0, hq⟩

@[simp]
theorem toFin_val_of_lt {q : ℕ} (hq : 0 < q) {x : ℕ} (h : x < q) :
    (toFin q hq x).val = x := by
  simp [toFin, h]

@[simp]
theorem toFin_of_val {q : ℕ} (hq : 0 < q) (x : Fin q) :
    toFin q hq x.val = x := by
  simp [toFin, x.is_lt]

/-! ### Boolean reduction for finite-domain CSP -/

/-- Boolean semantics for compiled finite-domain constraints:
* `none`: domain-validity constraint asserting length `b` and `bitsToNat bs < q`.
* `some R`: relation constraint decoding `bs` into $r$ chunks of length `b` and evaluating `sem R`.
-/
def semBoolean (q : ℕ) (sem : Rel → List (Fin q) → Bool) :
    Option Rel → List Bool → Bool
  | none, bs => decide (bs.length = bitWidth q ∧ bitsToNat bs < q)
  | some R, bs =>
    let b := bitWidth q
    if hq : 0 < q then
      let r := bs.length / b
      let vals := decodeChunks b r bs
      (bs.length % b == 0) && vals.all (decide <| · < q) && sem R (vals.map (toFin q hq))
    else false

/-- Compile a finite-domain CSP on declared variables `0, …, N - 1` into an equivalent Boolean CSP.
Emits a domain-validity constraint `(none, bitScope b v)` for every `v < N`, and translates each
constraint `(R, vs)` to `(some R, vs.flatMap (bitScope b))`. -/
def toBooleanCSP (q : ℕ) (N : ℕ) (F : CSP Rel ℕ) : CSP (Option Rel) ℕ :=
  let b := bitWidth q
  (List.range N).map (fun v => (none, bitScope b v)) ++
  F.map (fun c => (some c.1, c.2.flatMap (bitScope b)))

theorem length_flatMap_bitScope (b : ℕ) (l : List ℕ) :
    (l.flatMap (bitScope b)).length = l.length * b := by
  induction l with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, bitScope_length, List.length_cons, ih]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem all_length_le_toBooleanCSP {k q N : ℕ} {F : CSP Rel ℕ}
    (hF : ∀ c ∈ F, c.2.length ≤ k) :
    ∀ c ∈ toBooleanCSP q N F, c.2.length ≤ max 1 k * bitWidth q := by
  let b := bitWidth q
  intro c hc
  simp only [toBooleanCSP, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨v, _, rfl⟩ | ⟨c₀, hc₀, rfl⟩
  · simp only [bitScope_length]
    have : 1 * b ≤ max 1 k * b := Nat.mul_le_mul_right b (le_max_left 1 k)
    simpa using this
  · dsimp only
    rw [length_flatMap_bitScope]
    have hle : c₀.2.length ≤ max 1 k := (hF c₀ hc₀).trans (le_max_right 1 k)
    exact Nat.mul_le_mul_right b hle

theorem vars_toBooleanCSP_subset {q N : ℕ} {F : CSP Rel ℕ}
    (hvars : ∀ v ∈ F.vars, v < N) :
    ∀ x ∈ (toBooleanCSP q N F).vars, x < N * bitWidth q := by
  let b := bitWidth q
  intro x hx
  simp only [CSP.vars, toBooleanCSP, List.flatMap_append, List.mem_append,
    List.mem_flatMap, List.mem_map] at hx
  rcases hx with ⟨c, ⟨v, hv, rfl⟩, hxc⟩ | ⟨c, ⟨c₀, hc₀, rfl⟩, hxc⟩
  · rw [List.mem_range] at hv
    exact bitScope_subset_range hv x hxc
  · simp only [List.mem_flatMap] at hxc
    obtain ⟨v, hv, hxv⟩ := hxc
    have hv_vars : v ∈ F.vars := by
      simp only [CSP.vars, List.mem_flatMap]
      exact ⟨c₀, hc₀, hv⟩
    exact bitScope_subset_range (hvars v hv_vars) x hxv

theorem validDeclaredCSP_toBooleanCSP {k q N : ℕ} {F : CSP Rel ℕ}
    (hw : ∀ c ∈ F, c.2.length ≤ k) (hvars : ∀ v ∈ F.vars, v < N) :
    CSP.validDeclaredCSP (max 1 k * bitWidth q) (N * bitWidth q) (toBooleanCSP q N F) = true := by
  rw [CSP.validDeclaredCSP_eq_true_iff]
  refine ⟨all_length_le_toBooleanCSP hw, ?_⟩
  intro v hv
  have : v ∈ (toBooleanCSP q N F).vars := List.mem_toFinset.mp hv
  exact Finset.mem_range.mpr (vars_toBooleanCSP_subset hvars v this)

/-! ### Model count equivalence -/

/-- Encode an assignment `τ : Finset.range N → Fin q` into a Boolean assignment on
`Finset.range (N * bitWidth q)`. -/
def encodeAssign (q N : ℕ) (τ : Finset.range N → Fin q) :
    Finset.range (N * bitWidth q) → Bool := fun ⟨x, hx⟩ =>
  let b := bitWidth q
  have hx_lt : x < N * b := Finset.mem_range.mp hx
  have hv : x / b < N := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  (natToBits b (τ ⟨x / b, Finset.mem_range.mpr hv⟩).val).getD (x % b) false

/-- Decode a Boolean assignment on `Finset.range (N * bitWidth q)` into an assignment
`Finset.range N → Fin q`. -/
def decodeAssign (q N : ℕ) (hq : 0 < q) (σ : Finset.range (N * bitWidth q) → Bool) :
    Finset.range N → Fin q := fun ⟨v, _⟩ =>
  let b := bitWidth q
  let bits := (List.range b).map fun j =>
    if h : v * b + j < N * b then σ ⟨v * b + j, Finset.mem_range.mpr h⟩ else false
  toFin q hq (bitsToNat bits)

theorem div_mul_add (v b j : ℕ) (hj : j < b) : (v * b + j) / b = v := by
  have hb : 0 < b := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hj, Nat.zero_add]

theorem mod_mul_add (v b j : ℕ) (hj : j < b) : (v * b + j) % b = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem getD_eq_getElem {α : Type*} (l : List α) (n : ℕ) (d : α) (h : n < l.length) :
    l.getD n d = l[n] := by
  dsimp [List.getD]
  rw [List.getElem?_eq_getElem h]
  rfl

theorem decodeAssign_encodeAssign (q N : ℕ) (hq : 0 < q)
    (τ : Finset.range N → Fin q) :
    decodeAssign q N hq (encodeAssign q N τ) = τ := by
  let b := bitWidth q
  funext ⟨v, hv⟩
  dsimp only [decodeAssign]
  have hv_lt : v < N := Finset.mem_range.mp hv
  have hbits : (List.range b).map (fun j =>
      if h : v * b + j < N * b then encodeAssign q N τ ⟨v * b + j, Finset.mem_range.mpr h⟩
      else false) = natToBits b (τ ⟨v, hv⟩).val := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, natToBits_length]
    · intro j hj1 hj2
      rw [List.length_map, List.length_range] at hj1
      simp only [List.getElem_map, List.getElem_range]
      have hj_range : v * b + j < N * b := by
        have h1 : (v + 1) * b ≤ N * b := Nat.mul_le_mul_right b (by omega)
        have h2 : v * b + j < (v + 1) * b := by rw [Nat.add_mul, Nat.one_mul]; omega
        exact h2.trans_le h1
      simp only [hj_range, dite_true]
      dsimp only [encodeAssign]
      have hdiv : (v * b + j) / b = v := div_mul_add v b j hj1
      have hmod : (v * b + j) % b = j := mod_mul_add v b j hj1
      have hsub : (⟨(v * b + j) / b, Finset.mem_range.mpr (by rw [hdiv]; exact hv_lt)⟩ :
          Finset.range N) = ⟨v, hv⟩ := Subtype.ext hdiv
      rw [hsub, hmod]
      have hlen : j < (natToBits b (τ ⟨v, hv⟩).val).length := by
        rw [natToBits_length]; exact hj1
      exact getD_eq_getElem _ _ _ hlen
  rw [hbits]
  have hlt : (τ ⟨v, hv⟩).val < 2 ^ b := (τ ⟨v, hv⟩).is_lt.trans_le (le_two_pow_bitWidth q)
  rw [bitsToNat_natToBits hlt]
  exact toFin_of_val hq (τ ⟨v, hv⟩)

theorem map_extend_encodeAssign_bitScope (q N : ℕ) (τ : Finset.range N → Fin q)
    {v : ℕ} (hv : v < N) :
    (bitScope (bitWidth q) v).map (fun x =>
      if h : x ∈ Finset.range (N * bitWidth q) then encodeAssign q N τ ⟨x, h⟩ else false) =
    natToBits (bitWidth q) (τ ⟨v, Finset.mem_range.mpr hv⟩).val := by
  let b := bitWidth q
  rw [bitScope, List.map_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, natToBits_length]
  · intro j hj1 hj2
    simp only [List.length_map, List.length_range] at hj1
    have hj_range : v * bitWidth q + j < N * bitWidth q := by
      have h1 : (v + 1) * b ≤ N * b := Nat.mul_le_mul_right b (by omega)
      have h2 : v * b + j < (v + 1) * b := by rw [Nat.add_mul, Nat.one_mul]; omega
      exact h2.trans_le h1
    simp only [Function.comp_apply, List.getElem_map, List.getElem_range,
      Finset.mem_range, hj_range, dite_true]
    dsimp only [encodeAssign]
    have hdiv : (v * b + j) / b = v := div_mul_add v b j hj1
    have hmod : (v * b + j) % b = j := mod_mul_add v b j hj1
    have hsub : (⟨(v * b + j) / b, Finset.mem_range.mpr (by rw [hdiv]; exact hv)⟩ :
        Finset.range N) = ⟨v, Finset.mem_range.mpr hv⟩ := Subtype.ext hdiv
    rw [hsub, hmod]
    have hlen : j < (natToBits b (τ ⟨v, Finset.mem_range.mpr hv⟩).val).length := by
      rw [natToBits_length]; exact hj1
    exact getD_eq_getElem _ _ _ hlen

theorem eval_none_constraint_encodeAssign (q N : ℕ) (sem : Rel → List (Fin q) → Bool)
    (τ : Finset.range N → Fin q) {v : ℕ} (hv : v < N) :
    Constraint.eval (semBoolean q sem)
      (fun x => if h : x ∈ Finset.range (N * bitWidth q) then encodeAssign q N τ ⟨x, h⟩ else false)
      (none, bitScope (bitWidth q) v) = true := by
  dsimp only [Constraint.eval, semBoolean]
  rw [map_extend_encodeAssign_bitScope q N τ hv]
  simp only [natToBits_length, decide_eq_true_eq]
  have hlt : (τ ⟨v, Finset.mem_range.mpr hv⟩).val < 2 ^ (bitWidth q) :=
    (τ ⟨v, Finset.mem_range.mpr hv⟩).is_lt.trans_le (le_two_pow_bitWidth q)
  rw [bitsToNat_natToBits hlt]
  exact ⟨trivial, (τ ⟨v, Finset.mem_range.mpr hv⟩).is_lt⟩

theorem map_extend_encodeAssign_flatMap_bitScope (q N : ℕ) (τ : Finset.range N → Fin q)
    (vs : List ℕ) (hvs : ∀ v ∈ vs, v < N) :
    (vs.flatMap (bitScope (bitWidth q))).map (fun x =>
      if h : x ∈ Finset.range (N * bitWidth q) then encodeAssign q N τ ⟨x, h⟩ else false) =
    vs.flatMap (fun v => natToBits (bitWidth q) (if h : v < N then
      (τ ⟨v, Finset.mem_range.mpr h⟩).val else 0)) := by
  let σ := fun x => if h : x ∈ Finset.range (N * bitWidth q) then
    encodeAssign q N τ ⟨x, h⟩ else false
  rw [List.map_flatMap]
  refine List.flatMap_congr fun v hv => ?_
  have hv_lt := hvs v hv
  simp only [hv_lt, dite_true]
  exact map_extend_encodeAssign_bitScope q N τ hv_lt

theorem length_flatMap_of_forall_length_eq {α β : Type*} (b : ℕ) (vs : List α) (g : α → List β)
    (hg : ∀ x ∈ vs, (g x).length = b) :
    (vs.flatMap g).length = vs.length * b := by
  induction vs with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons v vs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hv : (g v).length = b := hg v List.mem_cons_self
    have hrest : ∀ x ∈ vs, (g x).length = b := fun x hx => hg x (List.mem_cons_of_mem v hx)
    rw [hv, ih hrest, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem eval_some_constraint_encodeAssign (q N : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (τ : Finset.range N → Fin q)
    (c : Constraint Rel ℕ) (hscope : ∀ v ∈ c.2, v < N) :
    Constraint.eval (semBoolean q sem)
      (fun x => if h : x ∈ Finset.range (N * bitWidth q) then encodeAssign q N τ ⟨x, h⟩ else false)
      (some c.1, c.2.flatMap (bitScope (bitWidth q))) =
    Constraint.eval sem
      (fun v => if h : v ∈ Finset.range N then τ ⟨v, h⟩ else ⟨0, hq⟩) c := by
  let b := bitWidth q
  have hb : 0 < b := one_le_bitWidth q
  dsimp only [Constraint.eval, semBoolean]
  simp only [hq, ↓reduceDIte]
  rw [map_extend_encodeAssign_flatMap_bitScope q N τ c.2 hscope]
  let g := fun v : ℕ => natToBits b (if h : v < N then
    (τ ⟨v, Finset.mem_range.mpr h⟩).val else 0)
  have hg_len : ∀ v ∈ c.2, (g v).length = b := fun _ _ => natToBits_length _ _
  have hbs_len : (c.2.flatMap g).length = c.2.length * b :=
    length_flatMap_of_forall_length_eq b c.2 g hg_len
  have hr : (c.2.flatMap g).length / b = c.2.length := by
    rw [hbs_len, Nat.mul_div_cancel _ hb]
  have hmod : (c.2.flatMap g).length % b = 0 := by
    rw [hbs_len]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_mul_left b c.2.length)
  have hmod_b : ((c.2.flatMap g).length % b == 0) = true := by
    rw [hmod]
    rfl
  have hdec : decodeChunks b ((c.2.flatMap g).length / b) (c.2.flatMap g) =
      c.2.map (fun v => if h : v < N then (τ ⟨v, Finset.mem_range.mpr h⟩).val else 0) := by
    rw [hr, decodeChunks_flatMap b c.2 g hg_len]
    apply List.map_congr_left
    intro v hv
    dsimp only [Function.comp_apply, g]
    have hv_lt := hscope v hv
    simp only [hv_lt, dite_true]
    have hlt : (τ ⟨v, Finset.mem_range.mpr hv_lt⟩).val < 2 ^ b :=
      (τ ⟨v, Finset.mem_range.mpr hv_lt⟩).is_lt.trans_le (le_two_pow_bitWidth q)
    exact bitsToNat_natToBits hlt
  have hall : (c.2.map (fun v => if h : v < N then
      (τ ⟨v, Finset.mem_range.mpr h⟩).val else 0)).all (fun x => decide (x < q)) = true := by
    rw [List.all_eq_true]
    intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨v, hv, rfl⟩
    have hv_lt := hscope v hv
    simp only [hv_lt, dite_true, decide_eq_true_eq]
    exact (τ ⟨v, Finset.mem_range.mpr hv_lt⟩).is_lt
  change (((c.2.flatMap g).length % b == 0 &&
      (decodeChunks b ((c.2.flatMap g).length / b) (c.2.flatMap g)).all
        (fun x => decide (x < q))) &&
      sem c.1 ((decodeChunks b ((c.2.flatMap g).length / b) (c.2.flatMap g)).map
        (toFin q hq))) =
    sem c.1 (c.2.map (fun v => if h : v ∈ Finset.range N then τ ⟨v, h⟩ else ⟨0, hq⟩))
  rw [hmod_b, hdec, hall]
  simp only [Bool.true_and]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro v hv
  have hv_lt := hscope v hv
  simp only [Function.comp_apply, hv_lt, dite_true, Finset.mem_range.mpr hv_lt]
  exact toFin_of_val hq (τ ⟨v, Finset.mem_range.mpr hv_lt⟩)

theorem eval_toBooleanCSP_encodeAssign (q N : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel ℕ) (hvars : ∀ v ∈ F.vars, v < N)
    (τ : Finset.range N → Fin q) :
    (toBooleanCSP q N F).eval (semBoolean q sem)
      (fun x => if h : x ∈ Finset.range (N * bitWidth q) then
        encodeAssign q N τ ⟨x, h⟩ else false) =
    F.eval sem (fun v => if h : v ∈ Finset.range N then τ ⟨v, h⟩ else ⟨0, hq⟩) := by
  let σ := fun x => if h : x ∈ Finset.range (N * bitWidth q) then
    encodeAssign q N τ ⟨x, h⟩ else false
  let τ_ext := fun v => if h : v ∈ Finset.range N then τ ⟨v, h⟩ else ⟨0, hq⟩
  dsimp only [toBooleanCSP, CSP.eval]
  rw [List.all_append]
  have hnone : ((List.range N).map (fun v => (none, bitScope (bitWidth q) v))).all
      (Constraint.eval (semBoolean q sem) σ) = true := by
    rw [List.all_eq_true]
    intro c hc
    simp only [List.mem_map, List.mem_range] at hc
    rcases hc with ⟨v, hv, rfl⟩
    exact eval_none_constraint_encodeAssign q N sem τ hv
  have hsome : (F.map (fun c => (some c.1, c.2.flatMap (bitScope (bitWidth q))))).all
      (Constraint.eval (semBoolean q sem) σ) = F.all (Constraint.eval sem τ_ext) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro h c hc
      have hscope : ∀ v ∈ c.2, v < N := fun v hv => hvars v (by
        simp only [CSP.vars, List.mem_flatMap]
        exact ⟨c, hc, hv⟩)
      have h1 := h (some c.1, c.2.flatMap (bitScope (bitWidth q))) c hc rfl
      have h2 := eval_some_constraint_encodeAssign q N hq sem τ c hscope
      rwa [h2] at h1
    · intro h _ c hc rfl
      have hscope : ∀ v ∈ c.2, v < N := fun v hv => hvars v (by
        simp only [CSP.vars, List.mem_flatMap]
        exact ⟨c, hc, hv⟩)
      have h1 := h c hc
      have h2 := eval_some_constraint_encodeAssign q N hq sem τ c hscope
      rwa [← h2] at h1
  rw [hnone, Bool.true_and, hsome]

theorem encodeAssign_decodeAssign_of_eval (q N : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel ℕ)
    (σ : Finset.range (N * bitWidth q) → Bool)
    (h_eval : (toBooleanCSP q N F).eval (semBoolean q sem)
      (fun x => if h : x ∈ Finset.range (N * bitWidth q) then σ ⟨x, h⟩ else false) = true) :
    encodeAssign q N (decodeAssign q N hq σ) = σ := by
  let b := bitWidth q
  let σ_ext := fun x => if h : x ∈ Finset.range (N * b) then σ ⟨x, h⟩ else false
  have hnone : ∀ v < N, Constraint.eval (semBoolean q sem) σ_ext (none, bitScope b v) = true := by
    intro v hv
    have hmem : (none, bitScope b v) ∈ toBooleanCSP q N F := by
      simp only [toBooleanCSP, List.mem_append, List.mem_map]
      left
      exact ⟨v, List.mem_range.mpr hv, rfl⟩
    have := List.all_eq_true.mp (by exact h_eval) (none, bitScope b v) hmem
    exact this
  have hbits_lt : ∀ v (hv : v < N),
      bitsToNat ((List.range b).map (fun j =>
        if h : v * b + j < N * b then σ ⟨v * b + j, Finset.mem_range.mpr h⟩ else false)) < q := by
    intro v hv
    have hc := hnone v hv
    dsimp only [Constraint.eval, semBoolean] at hc
    simp only [decide_eq_true_eq] at hc
    have hmap : (bitScope b v).map σ_ext = (List.range b).map (fun j =>
        if h : v * b + j < N * b then σ ⟨v * b + j, Finset.mem_range.mpr h⟩ else false) := by
      rw [bitScope, List.map_map]
      apply List.ext_getElem
      · simp only [List.length_map, List.length_range]
      · intro j hj1 hj2
        simp only [List.length_map, List.length_range] at hj1
        have hj_range : v * b + j < N * b := by
          have h1 : (v + 1) * b ≤ N * b := Nat.mul_le_mul_right b (by omega)
          have h2 : v * b + j < (v + 1) * b := by rw [Nat.add_mul, Nat.one_mul]; omega
          exact h2.trans_le h1
        simp only [Function.comp_apply, List.getElem_map, List.getElem_range,
          Finset.mem_range, hj_range, dite_true, σ_ext]
    rw [hmap] at hc
    exact hc.2
  funext ⟨x, hx⟩
  dsimp only [encodeAssign]
  have hx_lt : x < N * b := Finset.mem_range.mp hx
  have hb_pos : 0 < b := one_le_bitWidth q
  have hv : x / b < N := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  dsimp only [decodeAssign]
  let chunk := (List.range b).map fun j =>
    if h : (x / b) * b + j < N * b then σ ⟨(x / b) * b + j, Finset.mem_range.mpr h⟩ else false
  have hval : (toFin q hq (bitsToNat chunk)).val = bitsToNat chunk := by
    apply toFin_val_of_lt
    exact hbits_lt (x / b) hv
  rw [hval]
  have hlen : chunk.length = b := by
    simp only [chunk, List.length_map, List.length_range]
  have hinv := natToBits_bitsToNat chunk
  rw [hlen] at hinv
  rw [hinv]
  have hj_lt : x % b < b := Nat.mod_lt x hb_pos
  have hget := getD_eq_getElem chunk (x % b) false (by rw [hlen]; exact hj_lt)
  rw [hget]
  simp only [chunk, List.getElem_map, List.getElem_range]
  have hdivmod : (x / b) * b + x % b = x := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod x b
  have hj_range : (x / b) * b + x % b < N * b := by rw [hdivmod]; exact hx_lt
  simp only [hj_range, dite_true]
  congr 1
  exact Subtype.ext hdivmod

theorem eval_congr_default {D Rel : Type*} [Inhabited D] (sem : Rel → List D → Bool)
    (F : CSP Rel ℕ) {N : ℕ} (hvars : ∀ v ∈ F.vars, v < N) (τ : Finset.range N → D) (d : D) :
    F.eval sem (fun v => if h : v ∈ Finset.range N then τ ⟨v, h⟩ else default) =
    F.eval sem (fun v => if h : v ∈ Finset.range N then τ ⟨v, h⟩ else d) := by
  apply CSP.eval_congr
  intro v hv
  have hv_lt := hvars v hv
  simp only [Finset.mem_range.mpr hv_lt, dite_true]

/-- **Count-preserving bijection for finite-domain CSP to Boolean CSP.**
The declared-variable model count of a finite-domain CSP on `0, …, N - 1` equals the
declared-variable model count of its compiled Boolean CSP on `0, …, N * bitWidth q - 1`. -/
theorem modelCountOn_toBooleanCSP (q : ℕ) [Inhabited (Fin q)] (N : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel ℕ) (hvars : ∀ v ∈ F.vars, v < N) :
    (toBooleanCSP q N F).modelCountOn (semBoolean q sem)
      (Finset.range (N * bitWidth q)) =
    F.modelCountOn sem (Finset.range N) := by
  let b := bitWidth q
  dsimp only [CSP.modelCountOn]
  have hdef_bool : (default : Bool) = false := rfl
  refine (Finset.card_bij (fun τ _ => encodeAssign q N τ) (fun τ hτ => ?_)
    (fun τ₁ _ τ₂ _ h => ?_) (fun σ hσ => ?_)).symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    have hdef := eval_congr_default sem F hvars τ ⟨0, hq⟩
    rw [hdef] at hτ
    have heval := eval_toBooleanCSP_encodeAssign q N hq sem F hvars τ
    rw [hdef_bool, heval, hτ]
  · have h1 := congrArg (decodeAssign q N hq) h
    rw [decodeAssign_encodeAssign q N hq τ₁, decodeAssign_encodeAssign q N hq τ₂] at h1
    exact h1
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [hdef_bool] at hσ
    have hinv := encodeAssign_decodeAssign_of_eval q N hq sem F σ hσ
    refine ⟨decodeAssign q N hq σ, ?_, hinv⟩
    have heval := eval_toBooleanCSP_encodeAssign q N hq sem F hvars (decodeAssign q N hq σ)
    have hdef := eval_congr_default sem F hvars (decodeAssign q N hq σ) ⟨0, hq⟩
    rw [hdef, ← heval, hinv]
    exact hσ

end Cslib.Logic.PL.FiniteCSP
