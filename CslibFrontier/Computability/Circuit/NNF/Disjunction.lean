/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.NNF.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum

/-!
# Disjunctions of NNF circuits

The disjunction of two NNF circuits (`NNF.disj`) is their disjoint union with a new `∨` output:
its nodes are `Option (N₁ ⊕ N₂)`, so its size is the sum of their sizes plus one
(`NNF.size_disj`). It computes the disjunction of their functions (`NNF.toFun_disj`), is a DNNF
when both are (`NNF.isDecomposable_disj`), and is a d-DNNF when moreover the two functions are
never true together (`NNF.isDeterministic_disj`).

Copies of a circuit inside a larger one compute the same values
(`NNF.eval_eq_of_gate_map`, `NNF.vars_eq_of_gate_map`).

## Main definitions

* `Cslib.Circuits.NNF.Gate.map`: relabelling the children of a gate.
* `Cslib.Circuits.NNF.disj`: the disjunction of two circuits.

## Main results

* `Cslib.Circuits.NNF.toFun_disj`, `Cslib.Circuits.NNF.isDecomposable_disj`,
  `Cslib.Circuits.NNF.isDeterministic_disj`, `Cslib.Circuits.NNF.size_disj`.
-/

@[expose] public section

namespace Cslib.Circuits.NNF

variable {ι N N' N₁ N₂ : Type*}

/-- Relabel the children of a gate. -/
def Gate.map (f : N → N') : Gate ι N → Gate ι N'
  | .lit i b => .lit i b
  | .const b => .const b
  | .and l r => .and (f l) (f r)
  | .or l r => .or (f l) (f r)

/-- **Copies compute the same values.** If `f` maps each node of `C` to a node of `C'` whose gate
is that of the node with its children mapped by `f`, then `f` preserves values. -/
theorem eval_eq_of_gate_map {C : NNF ι N} {C' : NNF ι N'} (f : N → N')
    (hf : ∀ v, C'.gate (f v) = (C.gate v).map f) (x : ι → Bool) (v : N) :
    C'.eval x (f v) = C.eval x v := by
  induction v using C.induction_on with
  | h v ih =>
    cases hg : C.gate v with
    | lit i b => rw [eval_lit (C := C') (by rw [hf, hg]; rfl), eval_lit hg]
    | const b => rw [eval_const (C := C') (by rw [hf, hg]; rfl), eval_const hg]
    | and l r =>
      rw [eval_and (C := C') (by rw [hf, hg]; rfl), eval_and hg, ih l (C.and_lt v l r hg).1,
        ih r (C.and_lt v l r hg).2]
    | or l r =>
      rw [eval_or (C := C') (by rw [hf, hg]; rfl), eval_or hg, ih l (C.or_lt v l r hg).1,
        ih r (C.or_lt v l r hg).2]

/-- Copies mention the same variables. -/
theorem vars_eq_of_gate_map [DecidableEq ι] {C : NNF ι N} {C' : NNF ι N'} (f : N → N')
    (hf : ∀ v, C'.gate (f v) = (C.gate v).map f) (v : N) : C'.vars (f v) = C.vars v := by
  induction v using C.induction_on with
  | h v ih =>
    cases hg : C.gate v with
    | lit i b => rw [vars_lit (C := C') (by rw [hf, hg]; rfl), vars_lit hg]
    | const b => rw [vars_const (C := C') (by rw [hf, hg]; rfl), vars_const hg]
    | and l r =>
      rw [vars_and (C := C') (by rw [hf, hg]; rfl), vars_and hg, ih l (C.and_lt v l r hg).1,
        ih r (C.and_lt v l r hg).2]
    | or l r =>
      rw [vars_or (C := C') (by rw [hf, hg]; rfl), vars_or hg, ih l (C.or_lt v l r hg).1,
        ih r (C.or_lt v l r hg).2]

/-- The gate at a node of the disjunction of two circuits. -/
def disjGate (C₁ : NNF ι N₁) (C₂ : NNF ι N₂) : Option (N₁ ⊕ N₂) → Gate ι (Option (N₁ ⊕ N₂))
  | none => .or (some (.inl C₁.root)) (some (.inr C₂.root))
  | some (.inl v) => (C₁.gate v).map (some ∘ .inl)
  | some (.inr v) => (C₂.gate v).map (some ∘ .inr)

/-- The rank of a node of the disjunction of two circuits. -/
def disjRank (C₁ : NNF ι N₁) (C₂ : NNF ι N₂) : Option (N₁ ⊕ N₂) → ℕ
  | none => C₁.rank C₁.root + C₂.rank C₂.root + 1
  | some (.inl v) => C₁.rank v
  | some (.inr v) => C₂.rank v

/-- The **disjunction** of two circuits: their disjoint union with a new `∨` output. -/
def disj (C₁ : NNF ι N₁) (C₂ : NNF ι N₂) : NNF ι (Option (N₁ ⊕ N₂)) where
  gate := disjGate C₁ C₂
  rank := disjRank C₁ C₂
  and_lt v l r h := by
    rcases v with _ | v | v
    · cases h
    · cases hv : C₁.gate v <;> simp only [disjGate, hv, Gate.map, reduceCtorEq,
        Gate.and.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact C₁.and_lt v _ _ hv
    · cases hv : C₂.gate v <;> simp only [disjGate, hv, Gate.map, reduceCtorEq,
        Gate.and.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact C₂.and_lt v _ _ hv
  or_lt v l r h := by
    rcases v with _ | v | v
    · simp only [disjGate, Gate.or.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [disjRank]
      omega
    · cases hv : C₁.gate v <;> simp only [disjGate, hv, Gate.map, reduceCtorEq,
        Gate.or.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact C₁.or_lt v _ _ hv
    · cases hv : C₂.gate v <;> simp only [disjGate, hv, Gate.map, reduceCtorEq,
        Gate.or.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact C₂.or_lt v _ _ hv
  root := none

variable (C₁ : NNF ι N₁) (C₂ : NNF ι N₂)

theorem eval_disj_inl (x : ι → Bool) (v : N₁) : (disj C₁ C₂).eval x (some (.inl v)) = C₁.eval x v :=
  eval_eq_of_gate_map (C' := disj C₁ C₂) (some ∘ .inl) (fun _ => rfl) x v

theorem eval_disj_inr (x : ι → Bool) (v : N₂) : (disj C₁ C₂).eval x (some (.inr v)) = C₂.eval x v :=
  eval_eq_of_gate_map (C' := disj C₁ C₂) (some ∘ .inr) (fun _ => rfl) x v

theorem vars_disj_inl [DecidableEq ι] (v : N₁) : (disj C₁ C₂).vars (some (.inl v)) = C₁.vars v :=
  vars_eq_of_gate_map (C' := disj C₁ C₂) (some ∘ .inl) (fun _ => rfl) v

theorem vars_disj_inr [DecidableEq ι] (v : N₂) : (disj C₁ C₂).vars (some (.inr v)) = C₂.vars v :=
  vars_eq_of_gate_map (C' := disj C₁ C₂) (some ∘ .inr) (fun _ => rfl) v

/-- The disjunction computes the disjunction of the two functions. -/
theorem toFun_disj (x : ι → Bool) : (disj C₁ C₂).toFun x = (C₁.toFun x || C₂.toFun x) := by
  rw [toFun, eval_or (C := disj C₁ C₂) rfl, eval_disj_inl, eval_disj_inr]
  rfl

variable {C₁ C₂}

/-- The disjunction of two DNNFs is a DNNF. -/
theorem isDecomposable_disj [DecidableEq ι] (h₁ : C₁.IsDecomposable) (h₂ : C₂.IsDecomposable) :
    (disj C₁ C₂).IsDecomposable := by
  rintro (_ | v | v) l r hg
  · cases hg
  · cases hv : C₁.gate v <;> simp only [disj, disjGate, hv, Gate.map, reduceCtorEq,
      Gate.and.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    rw [Function.comp_apply, Function.comp_apply, vars_disj_inl, vars_disj_inl]
    exact h₁ v _ _ hv
  · cases hv : C₂.gate v <;> simp only [disj, disjGate, hv, Gate.map, reduceCtorEq,
      Gate.and.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    rw [Function.comp_apply, Function.comp_apply, vars_disj_inr, vars_disj_inr]
    exact h₂ v _ _ hv

/-- The disjunction of two d-DNNFs computing functions that are never true together is a
d-DNNF. -/
theorem isDeterministic_disj (h₁ : C₁.IsDeterministic) (h₂ : C₂.IsDeterministic)
    (hex : ∀ x, ¬(C₁.toFun x = true ∧ C₂.toFun x = true)) : (disj C₁ C₂).IsDeterministic := by
  rintro (_ | v | v) l r hg x
  · simp only [disj, disjGate, Gate.or.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    rw [eval_disj_inl, eval_disj_inr]
    exact hex x
  · cases hv : C₁.gate v <;> simp only [disj, disjGate, hv, Gate.map, reduceCtorEq,
      Gate.or.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    simp only [Function.comp_apply, eval_disj_inl]
    exact h₁ v _ _ hv x
  · cases hv : C₂.gate v <;> simp only [disj, disjGate, hv, Gate.map, reduceCtorEq,
      Gate.or.injEq] at hg
    obtain ⟨rfl, rfl⟩ := hg
    simp only [Function.comp_apply, eval_disj_inr]
    exact h₂ v _ _ hv x

/-- The size of a disjunction. -/
theorem size_disj [Fintype N₁] [Fintype N₂] :
    (disj C₁ C₂).size = C₁.size + C₂.size + 1 := by
  simp only [size, Fintype.card_option, Fintype.card_sum]

end Cslib.Circuits.NNF
