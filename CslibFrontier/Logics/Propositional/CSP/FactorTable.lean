/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import CslibFrontier.Logics.Propositional.CSP.PartitionFunction.Properties
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Explicit array factor tables and tensor-network correspondence

This module provides a concrete array-backed representation `FactorTable R V` of weighted
finite-domain constraints, together with exact bridges to both `Cslib.Logic.PL.CSP` (over any
finite domain `D` of size `d`) and `Cslib.Circuits.Frontier.ExplicitTensorNetwork` /
`Cslib.Circuits.Frontier.TensorNetwork` (at domain size `d = 2`).

Constraint scopes are arbitrary lists of variables: repeated variables inside a scope (for example
`[v, v]`), empty scopes (`[]`), isolated declared variables, and disconnected constraint components
are all handled uniformly by evaluating mixed-radix least-significant-digit indices
(`Nat.ofDigits`) against an assignment `σ : V → ℕ`.

## Main definitions

* `Cslib.Logic.PL.CSP.lsbDecode`: fixed-width least-significant-digit mixed-radix decoding from
  indices `< d ^ len` to `List ℕ` tuples below `d`, paired with Mathlib's `Nat.ofDigits`.
* `Cslib.Logic.PL.CSP.FactorTable`: factor table pairing `scope : List V` with `entries : Array R`.
* `Cslib.Logic.PL.CSP.FactorTable.contractionOn`, `Cslib.Logic.PL.CSP.FactorTable.contraction`:
  partition functions of lists of factor tables over declared or occurring variables.
* `Cslib.Logic.PL.CSP.FactorTable.ofCSP`: compile `CSP Rel V` into well-formed `FactorTable`s.
* `Cslib.Logic.PL.CSP.FactorTable.toExplicitTensorNetwork`,
  `Cslib.Logic.PL.CSP.FactorTable.ofExplicitTensorNetwork`: round-trip conversions with
  `ExplicitTensorNetwork`.

## Main results

* `Cslib.Logic.PL.CSP.lsbDecode_ofDigits`, `Cslib.Logic.PL.CSP.ofDigits_lsbDecode`: radix
  round-trip identities; `ofDigits_two_eq_lsbValue` recovers `Cslib.BitString.lsbValue`.
* `Cslib.Logic.PL.CSP.FactorTable.contractionOn_ofCSP`,
  `Cslib.Logic.PL.CSP.FactorTable.contraction_ofCSP`: exact agreement with
  `CSP.partitionFunctionOn` and `CSP.partitionFunction` over any finite domain.
* `Cslib.Logic.PL.CSP.FactorTable.contraction_toExplicitTensorNetwork`,
  `Cslib.Logic.PL.CSP.FactorTable.contractionOn_ofExplicitTensorNetwork`: exact agreement at
  `d = 2` with `ExplicitTensorNetwork.contraction` (including repeated ports, empty scopes,
  isolated edges, and disconnected vertices).
-/

public section

namespace Cslib.Logic.PL.CSP

open Cslib.Circuits.Frontier

/-! ### Mixed-radix least-significant-digit indexing -/

section Radix

/-- Decode `idx` into `len` base-`d` digits in least-significant-digit-first order. -/
@[expose] def lsbDecode (d : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | len + 1, idx => (idx % d) :: lsbDecode d len (idx / d)

/-- Evaluating `Nat.ofDigits` on an all-zero coordinate tuple yields `0`. -/
theorem ofDigits_map_zero {V : Type*} (d : ℕ) (xs : List V) :
    Nat.ofDigits d (xs.map fun _ => 0) = 0 := by
  rw [List.map_const', Nat.ofDigits_replicate_zero]

@[simp]
theorem length_lsbDecode (d len idx : ℕ) : (lsbDecode d len idx).length = len := by
  induction len generalizing idx with
  | zero => rfl
  | succ len ih => simp [lsbDecode, ih]

/-- Every decoded digit is strictly below a positive radix `d`. -/
theorem mem_lsbDecode_lt {d : ℕ} (hd : 0 < d) (len idx x : ℕ)
    (hx : x ∈ lsbDecode d len idx) : x < d := by
  induction len generalizing idx with
  | zero => simp [lsbDecode] at hx
  | succ len ih =>
      simp only [lsbDecode, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Nat.mod_lt _ hd
      · exact ih _ hx

/-- `Nat.ofDigits d xs` is strictly below `d ^ xs.length` for every `d` (including degenerate
bases `d ≤ 1`) whenever every digit is below `d`. -/
theorem ofDigits_lt_pow_length {d : ℕ} (xs : List ℕ) (h : ∀ x ∈ xs, x < d) :
    Nat.ofDigits d xs < d ^ xs.length := by
  rcases lt_trichotomy d 1 with hd0 | rfl | hd1
  · cases xs with
    | nil => simp
    | cons x _ =>
        have hx := h x (by simp)
        omega
  · have hz : xs = List.replicate xs.length 0 :=
      List.eq_replicate_iff.mpr ⟨rfl, fun x hx => Nat.lt_one_iff.mp (h x hx)⟩
    rw [hz, Nat.ofDigits_replicate_zero, one_pow]
    exact Nat.zero_lt_one
  · exact Nat.ofDigits_lt_base_pow_length hd1 h

/-- Decoding `Nat.ofDigits d xs` at length `xs.length` recovers `xs` when digits are below `d`. -/
theorem lsbDecode_ofDigits {d : ℕ} :
    ∀ xs : List ℕ, (∀ x ∈ xs, x < d) → lsbDecode d xs.length (Nat.ofDigits d xs) = xs
  | [], _ => rfl
  | x :: xs, h => by
      have hx : x < d := h x (by simp)
      have hxs : ∀ y ∈ xs, y < d := fun y hy => h y (by simp [hy])
      have hdiv : (x + d * Nat.ofDigits d xs) / d = Nat.ofDigits d xs := by
        rw [Nat.mul_comm, Nat.add_mul_div_right _ _ (lt_of_le_of_lt (Nat.zero_le x) hx),
          Nat.div_eq_of_lt hx, Nat.zero_add]
      have hmod : (x + d * Nat.ofDigits d xs) % d = x := by
        rw [Nat.mul_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      simp [lsbDecode, Nat.ofDigits_cons, hmod, hdiv, lsbDecode_ofDigits xs hxs]

/-- Encoding the first `len` decoded digits recovers `idx` when `idx < d ^ len`. -/
theorem ofDigits_lsbDecode {d len idx : ℕ} (h : idx < d ^ len) :
    Nat.ofDigits d (lsbDecode d len idx) = idx := by
  induction len generalizing idx with
  | zero =>
      simp only [pow_zero] at h
      have : idx = 0 := by omega
      subst this
      rfl
  | succ len ih =>
      have hdiv : idx / d < d ^ len := by
        rw [pow_succ'] at h
        by_cases hd : d = 0
        · subst hd; simp at h
        · exact Nat.div_lt_of_lt_mul h
      rw [lsbDecode, Nat.ofDigits_cons, ih hdiv]
      exact Nat.mod_add_div idx d

/-- At radix `2`, `Nat.ofDigits` on `Bool.toNat` digits equals `Cslib.BitString.lsbValue`. -/
theorem ofDigits_two_eq_lsbValue : ∀ bs : List Bool,
    Nat.ofDigits 2 (bs.map Bool.toNat) = BitString.lsbValue bs
  | [] => rfl
  | b :: bs => by
      rw [List.map_cons, Nat.ofDigits_cons, ofDigits_two_eq_lsbValue bs, BitString.lsbValue]

end Radix

/-! ### Explicit factor tables -/

/-- A weighted constraint factor represented by an ordered variable scope and an explicit table
of ring entries indexed in base-`d` least-significant-digit order. -/
structure FactorTable (R V : Type*) where
  /-- Ordered variable list of the factor (may contain duplicates or be empty). -/
  scope : List V
  /-- Flat array of weights of expected length `d ^ scope.length`. -/
  entries : Array R
  deriving DecidableEq, Repr

namespace FactorTable

section Evaluation

variable {R V W : Type*}

/-- A factor table is well-formed at domain size `d` when it stores all `d ^ scope.length`
entries. -/
@[expose] def WellFormed (d : ℕ) (f : FactorTable R V) : Prop :=
  f.entries.size = d ^ f.scope.length

/-- Evaluate a factor table at a `ℕ`-valued assignment `σ`, looking up its LSB base-`d` index
with `0` outside bounds. -/
@[expose] def evalAt (d : ℕ) [Zero R] (f : FactorTable R V) (σ : V → ℕ) : R :=
  f.entries.getD (Nat.ofDigits d (f.scope.map σ)) 0

/-- All variables occurring in a list of factor tables. -/
@[expose] def vars [DecidableEq V] (factors : List (FactorTable R V)) : Finset V :=
  (factors.flatMap FactorTable.scope).toFinset

/-- Contract a list of factor tables over domain `{0, ..., d - 1}` for declared variables
`declared`, fixing variables outside `declared` to `0`. -/
@[expose] def contractionOn [Semiring R] [DecidableEq V] (d : ℕ)
    (factors : List (FactorTable R V)) (declared : Finset V) : R :=
  ∑ σ : declared → Fin d,
    (factors.map fun f => f.evalAt d fun v => if h : v ∈ declared then (σ ⟨v, h⟩).1 else 0).prod

/-- Contract a list of factor tables over its occurring variables `FactorTable.vars`. -/
@[expose] def contraction [Semiring R] [DecidableEq V] (d : ℕ)
    (factors : List (FactorTable R V)) : R :=
  contractionOn d factors (vars factors)

/-- Factor evaluation depends only on values assigned to `f.scope`. -/
theorem evalAt_congr {d : ℕ} [Zero R] {f : FactorTable R V} {σ τ : V → ℕ}
    (h : ∀ v ∈ f.scope, σ v = τ v) : f.evalAt d σ = f.evalAt d τ := by
  simp only [evalAt]
  congr 2
  exact List.map_congr_left h

private theorem prod_map_evalAt_congr {d : ℕ} [Monoid R] [Zero R]
    {factors : List (FactorTable R V)} {σ τ : V → ℕ}
    (h : ∀ f ∈ factors, ∀ v ∈ f.scope, σ v = τ v) :
    (factors.map fun f => f.evalAt d σ).prod = (factors.map fun f => f.evalAt d τ).prod := by
  congr 1
  exact List.map_congr_left fun f hf => evalAt_congr (h f hf)

/-- The empty factor list contracts to `d ^ declared.card` over `declared`. -/
theorem contractionOn_nil [Semiring R] [DecidableEq V] (d : ℕ) (declared : Finset V) :
    contractionOn d ([] : List (FactorTable R V)) declared = (d : R) ^ declared.card := by
  simp only [contractionOn, List.map_nil, List.prod_nil, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul, mul_one, Nat.cast_pow]

/-- Enlarging the declared universe multiplies `contractionOn` by `d ^ (T \ S).card` whenever
all factor variables already lie in `S`. -/
theorem contractionOn_eq_card_pow_mul_of_subset [Semiring R] [DecidableEq V] (d : ℕ)
    {factors : List (FactorTable R V)} {S T : Finset V}
    (hvars : vars factors ⊆ S) (hST : S ⊆ T) :
    contractionOn d factors T = ((d : R) ^ (T \ S).card) * contractionOn d factors S := by
  classical
  let eSplit := sdiffPiEquiv (D := Fin d) hST
  rw [contractionOn, contractionOn]
  calc ∑ σ : T → Fin d,
          (factors.map fun f => f.evalAt d fun v => if h : v ∈ T then (σ ⟨v, h⟩).1 else 0).prod
      = ∑ p : (S → Fin d) × ((T \ S : Finset V) → Fin d),
          (factors.map fun f =>
            f.evalAt d fun v => if h : v ∈ T then (eSplit.symm p ⟨v, h⟩).1 else 0).prod :=
        Fintype.sum_equiv eSplit _ (fun p => _) (fun σ => by
          congr 1; refine List.map_congr_left fun f _ => evalAt_congr fun v _ => ?_
          by_cases hv : v ∈ T <;> simp [hv, Equiv.symm_apply_apply])
    _ = ∑ p : (S → Fin d) × ((T \ S : Finset V) → Fin d),
          (factors.map fun f =>
            f.evalAt d fun v => if h : v ∈ S then (p.1 ⟨v, h⟩).1 else 0).prod := by
        refine Finset.sum_congr rfl fun p _ => prod_map_evalAt_congr fun f hf v hv => ?_
        have hvS : v ∈ S := hvars (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨f, hf, hv⟩))
        have hvT : v ∈ T := hST hvS
        simp [eSplit, hvS, hvT]
    _ = ∑ _ : (T \ S : Finset V) → Fin d, ∑ σ₁ : S → Fin d,
          (factors.map fun f =>
            f.evalAt d fun v => if h : v ∈ S then (σ₁ ⟨v, h⟩).1 else 0).prod := by
        rw [Fintype.sum_prod_type_right]
    _ = (Fintype.card ((T \ S : Finset V) → Fin d) : R) *
          ∑ σ₁ : S → Fin d,
            (factors.map fun f =>
              f.evalAt d fun v => if h : v ∈ S then (σ₁ ⟨v, h⟩).1 else 0).prod := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ((d : R) ^ (T \ S).card) *
          ∑ σ₁ : S → Fin d,
            (factors.map fun f =>
              f.evalAt d fun v => if h : v ∈ S then (σ₁ ⟨v, h⟩).1 else 0).prod := by
        simp [Nat.cast_pow]

/-- Disconnected lists of factor tables multiply over a commutative semiring. -/
theorem contractionOn_append_of_disjoint [CommSemiring R] [DecidableEq V] (d : ℕ)
    {fs₁ fs₂ : List (FactorTable R V)} {d₁ d₂ : Finset V}
    (hdisj : Disjoint d₁ d₂) (h₁ : vars fs₁ ⊆ d₁) (h₂ : vars fs₂ ⊆ d₂) :
    contractionOn d (fs₁ ++ fs₂) (d₁ ∪ d₂) =
      contractionOn d fs₁ d₁ * contractionOn d fs₂ d₂ := by
  let eSplit := (Equiv.piFinsetUnion (fun _ => Fin d) hdisj).symm
  rw [contractionOn, contractionOn, contractionOn]
  calc ∑ σ : (d₁ ∪ d₂ : Finset V) → Fin d,
          ((fs₁ ++ fs₂).map fun f =>
            f.evalAt d fun v => if h : v ∈ d₁ ∪ d₂ then (σ ⟨v, h⟩).1 else 0).prod
      = ∑ p : (d₁ → Fin d) × (d₂ → Fin d),
          ((fs₁ ++ fs₂).map fun f =>
            f.evalAt d fun v =>
              if h : v ∈ d₁ ∪ d₂ then (eSplit.symm p ⟨v, h⟩).1 else 0).prod :=
        Fintype.sum_equiv eSplit _ (fun p => _) (fun σ => by
          congr 1; refine List.map_congr_left fun f _ => evalAt_congr fun v _ => ?_
          by_cases hv : v ∈ d₁ ∪ d₂ <;> simp [hv, Equiv.symm_apply_apply])
    _ = ∑ p : (d₁ → Fin d) × (d₂ → Fin d),
          (fs₁.map fun f => f.evalAt d fun v => if h : v ∈ d₁ then (p.1 ⟨v, h⟩).1 else 0).prod *
          (fs₂.map fun f =>
            f.evalAt d fun v => if h : v ∈ d₂ then (p.2 ⟨v, h⟩).1 else 0).prod := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [List.map_append, List.prod_append]
        congr 1
        · refine prod_map_evalAt_congr fun f hf v hv => ?_
          have hv₁ : v ∈ d₁ := h₁ (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨f, hf, hv⟩))
          have hvu : v ∈ d₁ ∪ d₂ := Finset.mem_union_left d₂ hv₁
          have hleft := congrArg Fin.val
            (Equiv.piFinsetUnion_left (fun _ => Fin d) hdisj (f := p.1) (g := p.2) hv₁ hvu)
          simpa [eSplit, hv₁, hvu] using hleft
        · refine prod_map_evalAt_congr fun f hf v hv => ?_
          have hv₂ : v ∈ d₂ := h₂ (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨f, hf, hv⟩))
          have hvu : v ∈ d₁ ∪ d₂ := Finset.mem_union_right d₁ hv₂
          have hright := congrArg Fin.val
            (Equiv.piFinsetUnion_right (fun _ => Fin d) hdisj (f := p.1) (g := p.2) hv₂ hvu)
          simpa [eSplit, hv₂, hvu] using hright
    _ = (∑ σ₁ : d₁ → Fin d,
          (fs₁.map fun f => f.evalAt d fun v => if h : v ∈ d₁ then (σ₁ ⟨v, h⟩).1 else 0).prod) *
          (∑ σ₂ : d₂ → Fin d,
          (fs₂.map fun f =>
            f.evalAt d fun v => if h : v ∈ d₂ then (σ₂ ⟨v, h⟩).1 else 0).prod) := by
        rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Disconnected factor tables multiply over `contraction`. -/
theorem contraction_append_of_disjoint [CommSemiring R] [DecidableEq V] (d : ℕ)
    {fs₁ fs₂ : List (FactorTable R V)} (hdisj : Disjoint (vars fs₁) (vars fs₂)) :
    contraction d (fs₁ ++ fs₂) = contraction d fs₁ * contraction d fs₂ := by
  have hvars : vars (fs₁ ++ fs₂) = vars fs₁ ∪ vars fs₂ := by
    ext v; simp [vars]
  rw [contraction, hvars, contraction, contraction]
  exact contractionOn_append_of_disjoint d hdisj Finset.Subset.rfl Finset.Subset.rfl

/-- Relabeling factor scopes through a variable equivalence preserves `contractionOn`. -/
@[expose] def relabel (e : V → W) (f : FactorTable R V) : FactorTable R W :=
  { scope := f.scope.map e, entries := f.entries }

@[simp]
theorem relabel_scope (e : V → W) (f : FactorTable R V) :
    (relabel e f).scope = f.scope.map e := rfl

@[simp]
theorem relabel_entries (e : V → W) (f : FactorTable R V) :
    (relabel e f).entries = f.entries := rfl

theorem contractionOn_relabel_equiv [Semiring R] [DecidableEq V] [DecidableEq W] (d : ℕ)
    (e : V ≃ W) (factors : List (FactorTable R V)) (declared : Finset V) :
    contractionOn d (factors.map (relabel e)) (declared.map e.toEmbedding) =
      contractionOn d factors declared := by
  let eDom : declared ≃ declared.map e.toEmbedding :=
    { toFun := fun v => ⟨e v.1, Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
      invFun := fun w => ⟨e.symm w.1, by
        rcases Finset.mem_map.mp w.2 with ⟨v, hv, hvw⟩
        simpa [← hvw] using hv⟩
      left_inv := fun v => Subtype.ext (e.symm_apply_apply v.1)
      right_inv := fun w => Subtype.ext (e.apply_symm_apply w.1) }
  let eAssign : (declared.map e.toEmbedding → Fin d) ≃ (declared → Fin d) :=
    Equiv.piCongrLeft' (fun _ => Fin d) eDom.symm
  rw [contractionOn, contractionOn]
  refine Fintype.sum_equiv eAssign _ _ fun σ => ?_
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun f _ => ?_
  simp only [Function.comp_def, evalAt, relabel, List.map_map]
  congr 2
  refine List.map_congr_left fun v _ => ?_
  by_cases hv : v ∈ declared
  · have hev : e v ∈ declared.map e.toEmbedding := Finset.mem_map.mpr ⟨v, hv, rfl⟩
    simp only [hv, hev, dite_true, eAssign]
    simp [eDom]
  · simp [hv]

end Evaluation

/-! ### Bridge from `CSP` over any finite domain -/

section CSPBridge

variable {Rel V D R : Type*}

/-- Compile one constraint into an explicit factor table at domain size `d` using bijection
`e : D ≃ Fin d`. -/
@[expose] def ofConstraint [Inhabited D] (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → R)
    (c : Constraint Rel V) : FactorTable R V :=
  { scope := c.scope
    entries := Array.ofFn fun i : Fin (d ^ c.scope.length) =>
      let args := (lsbDecode d c.scope.length i.1).map fun k =>
        if hk : k < d then e.symm ⟨k, hk⟩ else default
      wt c.rel args }

/-- Compile an entire CSP instance into a list of explicit factor tables. -/
@[expose] def ofCSP [Inhabited D] (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → R)
    (F : CSP Rel V) : List (FactorTable R V) :=
  F.map (ofConstraint d e wt)

theorem wellFormed_ofConstraint [Inhabited D] (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → R)
    (c : Constraint Rel V) : (ofConstraint d e wt c).WellFormed d := by
  simp [WellFormed, ofConstraint]

@[simp]
theorem vars_ofCSP [DecidableEq V] [Inhabited D] (d : ℕ) (e : D ≃ Fin d)
    (wt : Rel → List D → R) (F : CSP Rel V) :
    vars (ofCSP d e wt F) = F.vars.toFinset := by
  ext v
  simp only [vars, ofCSP, List.mem_toFinset, List.mem_flatMap, List.mem_map, CSP.vars]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, hv⟩
    exact ⟨c, hc, hv⟩
  · rintro ⟨c, hc, hv⟩
    exact ⟨ofConstraint d e wt c, ⟨c, hc, rfl⟩, hv⟩

/-- Evaluating `ofConstraint` at `fun v => (e (σ v)).1` recovers the original constraint weight,
preserving arbitrary repeated variables and empty scopes. -/
theorem evalAt_ofConstraint [Zero R] [Inhabited D] (d : ℕ) (e : D ≃ Fin d)
    (wt : Rel → List D → R) (c : Constraint Rel V) (σ : V → D) :
    (ofConstraint d e wt c).evalAt d (fun v => (e (σ v)).1) = wt c.rel (c.scope.map σ) := by
  have hlt : ∀ x ∈ c.scope.map (fun v => (e (σ v)).1), x < d := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨v, _, rfl⟩
    exact (e (σ v)).2
  have hidx : Nat.ofDigits d (c.scope.map fun v => (e (σ v)).1) < d ^ c.scope.length := by
    simpa [List.length_map] using ofDigits_lt_pow_length _ hlt
  have hdec : lsbDecode d c.scope.length (Nat.ofDigits d (c.scope.map fun v => (e (σ v)).1)) =
      c.scope.map fun v => (e (σ v)).1 := by
    have := lsbDecode_ofDigits (c.scope.map fun v => (e (σ v)).1) hlt
    simpa [List.length_map] using this
  rw [evalAt, ofConstraint, Array.getD]
  dsimp only
  split_ifs with hsz
  · change (Array.ofFn fun i : Fin (d ^ c.scope.length) =>
        let args := (lsbDecode d c.scope.length i.1).map fun k =>
          if hk : k < d then e.symm ⟨k, hk⟩ else default
        wt c.rel args)[Nat.ofDigits d (c.scope.map fun v => (e (σ v)).1)]'(by simpa using hidx) =
      wt c.rel (c.scope.map σ)
    rw [Array.getElem_ofFn]
    dsimp only
    rw [hdec, List.map_map]
    congr 1
    refine List.map_congr_left fun v _ => ?_
    have hvlt : (e (σ v)).1 < d := (e (σ v)).2
    simp [hvlt]
  · exact absurd (by simpa using hidx) hsz

/-- Contracting `ofCSP` over `declared` (containing `F.vars.toFinset`) equals
`F.partitionFunctionOn wt declared`. -/
theorem contractionOn_ofCSP [Semiring R] [DecidableEq V] [Fintype D] [Inhabited D]
    (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → R) {F : CSP Rel V} {declared : Finset V}
    (hvars : F.vars.toFinset ⊆ declared) :
    contractionOn d (ofCSP d e wt F) declared = F.partitionFunctionOn wt declared := by
  let eAssign : (declared → Fin d) ≃ (declared → D) :=
    Equiv.piCongrRight fun _ => e.symm
  rw [contractionOn, partitionFunctionOn]
  refine Fintype.sum_equiv eAssign _ _ fun σ => ?_
  rw [ofCSP, List.map_map]
  change (F.map fun c => (ofConstraint d e wt c).evalAt d
    (fun v => if h : v ∈ declared then (σ ⟨v, h⟩).1 else 0)).prod =
    F.weight wt (fun v => if h : v ∈ declared then e.symm (σ ⟨v, h⟩) else default)
  rw [CSP.weight]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  have hcvar : ∀ v ∈ c.scope, v ∈ declared := fun v hv =>
    hvars (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨c, hc, hv⟩))
  have hcongr : (ofConstraint d e wt c).evalAt d
      (fun v => if h : v ∈ declared then (σ ⟨v, h⟩).1 else 0) =
      (ofConstraint d e wt c).evalAt d
      (fun v => (e (if h : v ∈ declared then e.symm (σ ⟨v, h⟩) else default)).1) := by
    refine evalAt_congr fun v hv => ?_
    have hvd : v ∈ declared := hcvar v hv
    simp [hvd]
  rw [hcongr, evalAt_ofConstraint]

/-- Contracting `ofCSP` over its occurring variables equals `F.partitionFunction wt`. -/
theorem contraction_ofCSP [Semiring R] [DecidableEq V] [Fintype D] [Inhabited D]
    (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → R) (F : CSP Rel V) :
    contraction d (ofCSP d e wt F) = F.partitionFunction wt := by
  rw [contraction, vars_ofCSP, partitionFunction_eq_partitionFunctionOn]
  exact contractionOn_ofCSP d e wt Finset.Subset.rfl

end CSPBridge

/-! ### Bridge to `ExplicitTensorNetwork` and `TensorNetwork` at `d = 2` -/

section TensorBridge

variable {R : Type*}

/-- Convert a list of factor tables on `ℕ`-named variables into an `ExplicitTensorNetwork R`
with `m` declared edges `0, ..., m - 1`. -/
@[expose] def toExplicitTensorNetwork (m : ℕ) (factors : List (FactorTable R ℕ)) :
    ExplicitTensorNetwork R :=
  { numEdges := m
    vertices := factors.map fun f => (f.scope, f.entries.toList) }

/-- Convert an `ExplicitTensorNetwork R` into a list of `FactorTable R ℕ` tables. -/
@[expose] def ofExplicitTensorNetwork (net : ExplicitTensorNetwork R) : List (FactorTable R ℕ) :=
  net.vertices.map fun v => { scope := v.1, entries := v.2.toArray }

private theorem list_toArray_getD [Zero R] (l : List R) (i : ℕ) :
    l.toArray.getD i 0 = l.getD i 0 := by
  simp only [Array.getD, List.getD, List.size_toArray]
  by_cases h : i < l.length
  · simp [h]
  · simp [h]

/-- A vertex entry of an explicit tensor network matches `FactorTable.evalAt 2`. -/
private theorem entry_eq_evalAt_two [Zero R] (ports : List ℕ) (table : List R)
    (assign : ℕ → Bool) :
    ExplicitTensorNetwork.entry table (ports.map assign) =
      FactorTable.evalAt 2 { scope := ports, entries := table.toArray }
        (fun i => (assign i).toNat) := by
  rw [ExplicitTensorNetwork.entry, FactorTable.evalAt, list_toArray_getD]
  have hl : BitString.lsbValue (ports.map assign) =
      Nat.ofDigits 2 (ports.map fun i => (assign i).toNat) := by
    rw [← ofDigits_two_eq_lsbValue, List.map_map]
    rfl
  rw [hl]

/-- Contracting an `ExplicitTensorNetwork R` equals `FactorTable.contractionOn 2` of
`ofExplicitTensorNetwork` on `Finset.range net.numEdges`. -/
theorem contractionOn_ofExplicitTensorNetwork [CommSemiring R]
    (net : ExplicitTensorNetwork R) :
    contractionOn 2 (ofExplicitTensorNetwork net) (Finset.range net.numEdges) =
      net.contraction := by
  let eDom : Fin net.numEdges ≃ Finset.range net.numEdges :=
    { toFun := fun i => ⟨i.1, Finset.mem_range.mpr i.2⟩
      invFun := fun i => ⟨i.1, Finset.mem_range.mp i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eAssign : (Finset.range net.numEdges → Fin 2) ≃ (Fin net.numEdges → Bool) :=
    (Equiv.piCongrLeft' (fun _ => Fin 2) eDom.symm).trans
      (Equiv.piCongrRight fun _ => finTwoEquiv)
  rw [contractionOn, ExplicitTensorNetwork.contraction]
  refine Fintype.sum_equiv eAssign _ _ fun σ => ?_
  rw [ofExplicitTensorNetwork, List.map_map]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_def]
  have hbits : net.portBits (eAssign σ) v.1 =
      v.1.map fun i => if h : i < net.numEdges then (eAssign σ) ⟨i, h⟩ else false := rfl
  rw [hbits, entry_eq_evalAt_two]
  refine evalAt_congr fun i _ => ?_
  by_cases hi : i < net.numEdges
  · have hir : i ∈ Finset.range net.numEdges := Finset.mem_range.mpr hi
    simp only [hi, hir, dite_true]
    have hassign : (eAssign σ ⟨i, hi⟩).toNat = (σ ⟨i, hir⟩).1 := by
      change (finTwoEquiv (σ ⟨i, hir⟩)).toNat = (σ ⟨i, hir⟩).1
      rcases σ ⟨i, hir⟩ with ⟨_ | _ | k, hk⟩
      · rfl
      · rfl
      · omega
    exact hassign.symm
  · have hir : i ∉ Finset.range net.numEdges := by simpa [Finset.mem_range] using hi
    simp [hi, hir]

/-- Contracting `toExplicitTensorNetwork m factors` equals `FactorTable.contractionOn 2` on
`Finset.range m`. -/
theorem contraction_toExplicitTensorNetwork [CommSemiring R] (m : ℕ)
    (factors : List (FactorTable R ℕ)) :
    (toExplicitTensorNetwork m factors).contraction =
      contractionOn 2 factors (Finset.range m) := by
  have h := (contractionOn_ofExplicitTensorNetwork (toExplicitTensorNetwork m factors)).symm
  rw [h]
  congr 1
  simp only [ofExplicitTensorNetwork, toExplicitTensorNetwork, List.map_map]
  have hmap : ∀ fs : List (FactorTable R ℕ), fs.map
      ((fun v => ({ scope := v.1, entries := v.2.toArray } : FactorTable R ℕ)) ∘
        fun f => (f.scope, f.entries.toList)) = fs := by
    intro fs
    induction fs with
    | nil => rfl
    | cons f fs ih =>
        cases f
        simp only [List.map_cons, Function.comp_def, Array.toArray_toList]
        exact congrArg (_ :: ·) ih
  exact hmap factors

/-- Contracting a `DescribedNetwork T` whose vertex evaluator `eval` agrees with table lookup
matches `FactorTable.contractionOn 2`. -/
theorem contractionOn_ofDescribedNetwork {T : Type*} [CommSemiring R]
    (eval : T → List Bool → R) (net : DescribedNetwork T)
    (heval : ∀ v ∈ net.vertices, ∀ bs : List Bool, bs.length = v.1.length →
      eval v.2 bs = (Array.ofFn fun i : Fin (2 ^ v.1.length) =>
        eval v.2 ((lsbDecode 2 v.1.length i.1).map fun k => decide (k ≠ 0))).getD
          (BitString.lsbValue bs) 0) :
    contractionOn 2
      (net.vertices.map fun v =>
        ({ scope := v.1
           entries := Array.ofFn fun i : Fin (2 ^ v.1.length) =>
             eval v.2 ((lsbDecode 2 v.1.length i.1).map fun k => decide (k ≠ 0)) } :
          FactorTable R ℕ))
      (Finset.range net.numEdges) =
    DescribedNetwork.contraction eval net := by
  let netExp : ExplicitTensorNetwork R :=
    { numEdges := net.numEdges
      vertices := net.vertices.map fun v =>
        (v.1, (Array.ofFn fun i : Fin (2 ^ v.1.length) =>
          eval v.2 ((lsbDecode 2 v.1.length i.1).map fun k => decide (k ≠ 0))).toList) }
  have h1 : contractionOn 2
      (net.vertices.map fun v =>
        ({ scope := v.1
           entries := Array.ofFn fun i : Fin (2 ^ v.1.length) =>
             eval v.2 ((lsbDecode 2 v.1.length i.1).map fun k => decide (k ≠ 0)) } :
          FactorTable R ℕ))
      (Finset.range net.numEdges) =
      contractionOn 2 (ofExplicitTensorNetwork netExp) (Finset.range netExp.numEdges) := by
    congr 1
    simp [netExp, ofExplicitTensorNetwork, List.map_map]
  rw [h1, contractionOn_ofExplicitTensorNetwork, ExplicitTensorNetwork.contraction,
    DescribedNetwork.contraction]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [netExp, List.map_map]
  congr 1
  refine List.map_congr_left fun v hv => ?_
  have hword : netExp.portBits x v.1 = DescribedNetwork.wordBits (List.ofFn x) v.1 := by
    rw [ExplicitTensorNetwork.portBits, DescribedNetwork.wordBits]
    refine List.map_congr_left fun i _ => ?_
    by_cases hi : i < net.numEdges
    · simp [netExp, hi]
    · have hge : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_lt hi
      simp [netExp, hi, List.getD]
  dsimp only [Function.comp_def]
  rw [hword, ExplicitTensorNetwork.entry,
    heval v hv _ (by simp [DescribedNetwork.wordBits]), ← list_toArray_getD]

/-- Contracting an arbitrary `TensorNetwork R Bool V E` matches `FactorTable.contractionOn 2`
of its explicit table representation. -/
theorem contraction_tensorNetwork_eq_factorTable {V E : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [DecidableEq E] [CommSemiring R] {n m : ℕ}
    (N : TensorNetwork R Bool V E) (ev : V ≃ Fin n) (ee : E ≃ Fin m) :
    N.contraction =
      contractionOn 2 (ofExplicitTensorNetwork (N.toExplicit ev ee)) (Finset.range m) := by
  rw [← TensorNetwork.contraction_toExplicit N ev ee]
  exact (contractionOn_ofExplicitTensorNetwork (N.toExplicit ev ee)).symm

end TensorBridge

end FactorTable

end Cslib.Logic.PL.CSP
