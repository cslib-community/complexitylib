/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SemiCircuit.Gate
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.SymmDiff
import Mathlib.Data.Finset.SymmDiff

/-!
# Equations over `𝔽₂`

The equations of the affine system of a fair semi-circuit (`Cslib.Circuits.Boolean.SemiCircuit`):
an equation states that the sum over `𝔽₂` of the values of its terms, a finite set of internal
values, is a constant. Rerouting a term to a literal (`Equation.subst`) preserves the truth of the
equation on assignments giving the term the value of the literal (`Equation.holds_subst`) and does
not add terms (`Equation.card_subst_le`). An affine gate becomes an equation with at most three
terms (`affEqn`, `affEqn_holds`).

## Main definitions

* `Cslib.Circuits.Boolean.SemiCircuit.Equation`: equations, with `Equation.Holds` and
  `Equation.subst`.
* `Cslib.Circuits.Boolean.SemiCircuit.affEqn`: the equation of an affine gate.

## Main results

* `Cslib.Circuits.Boolean.SemiCircuit.Equation.holds_subst`: rerouting preserves equations.
* `Cslib.Circuits.Boolean.SemiCircuit.affEqn_holds`: the equation of an affine gate holds exactly
  when the gate takes its value.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
* [M. G. Find, A. Golovnev, E. A. Hirsch and A. S. Kulikov, *A better-than-3n lower bound for the
  circuit complexity of an explicit function*][FindGolovnevHirschKulikov2016]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.SemiCircuit

open Finset
open scoped symmDiff

/-! ### Equations -/

/-- An equation of the affine system: the sum over `𝔽₂` of the values of its terms is `rhs`. -/
structure Equation where
  /-- The internal values occurring in the equation. -/
  terms : Finset ℕ
  /-- The right-hand side. -/
  rhs : Bool

/-- Adding `t` to a set of terms over `𝔽₂` removes it if present and inserts it otherwise. -/
private theorem symmDiff_singleton_eq (s : Finset ℕ) (t : ℕ) :
    s ∆ {t} = if t ∈ s then s.erase t else insert t s := by
  ext z
  by_cases hz : z = t
  · subst hz
    split_ifs with h <;> simp [Finset.mem_symmDiff, h]
  · split_ifs <;> simp [Finset.mem_symmDiff, hz]

private theorem sum_symmDiff_singleton (s : Finset ℕ) (t : ℕ) (val : ℕ → Bool) :
    ∑ i ∈ s ∆ {t}, val i = ∑ i ∈ s, val i + val t := by
  rw [symmDiff_singleton_eq]
  split_ifs with ht
  · rw [← Finset.add_sum_erase s val ht, add_comm (val t), add_assoc, BooleanRing.add_self,
      add_zero]
  · rw [Finset.sum_insert ht, add_comm]

theorem mem_symmDiff_singleton {s : Finset ℕ} {t z : ℕ} : z ∈ s ∆ {t} ↔ (z ∈ s ↔ z ≠ t) := by
  rw [symmDiff_singleton_eq]
  by_cases hz : z = t
  · subst hz
    split_ifs with ht <;> simp [ht]
  · split_ifs with ht <;> simp [hz]

private theorem card_symmDiff_singleton_le (s : Finset ℕ) (t : ℕ) :
    (s ∆ {t}).card ≤ s.card + 1 := by
  rw [symmDiff_singleton_eq]
  split_ifs with h
  · exact (Finset.card_erase_le).trans (Nat.le_succ _)
  · exact Finset.card_insert_le _ _

namespace Equation

/-- The equation holds under an assignment of the internal values. -/
def Holds (E : Equation) (val : ℕ → Bool) : Prop :=
  ∑ i ∈ E.terms, val i = E.rhs

instance (E : Equation) (val : ℕ → Bool) : Decidable (E.Holds val) :=
  inferInstanceAs (Decidable (_ = _))

/-- Reroute the term `v` of an equation to the literal `ℓ`. -/
def subst (E : Equation) (v : ℕ) (ℓ : Lit) : Equation :=
  if v ∈ E.terms then
    match ℓ.arg with
    | .const b => ⟨E.terms.erase v, E.rhs ^^ b ^^ ℓ.neg⟩
    | .node t => ⟨E.terms.erase v ∆ {t}, E.rhs ^^ ℓ.neg⟩
  else E

/-- Rerouting `v` to a literal with the value of `v` preserves the truth of every equation. -/
theorem holds_subst {E : Equation} {v : ℕ} {ℓ : Lit} {val : ℕ → Bool}
    (h : val v = ℓ.eval val) : (E.subst v ℓ).Holds val ↔ E.Holds val := by
  unfold subst
  split_ifs with hv
  · unfold Holds
    rw [← Finset.add_sum_erase E.terms val hv, h]
    obtain ⟨a, c⟩ := ℓ
    clear h
    cases a with
    | const b =>
      simp only [Lit.eval, Arg.eval_const]
      generalize ∑ i ∈ E.terms.erase v, val i = S
      generalize E.rhs = r
      revert S r b c; decide
    | node t =>
      simp only [Lit.eval, Arg.eval_node, sum_symmDiff_singleton]
      generalize ∑ i ∈ E.terms.erase v, val i = S
      generalize E.rhs = r
      generalize val t = x
      revert S r x c; decide
  · exact Iff.rfl

theorem mem_subst_of_ne {E : Equation} {v : ℕ} {ℓ : Lit} {z : ℕ} (hzv : z ≠ v)
    (hzℓ : ℓ.arg ≠ .node z) : z ∈ (E.subst v ℓ).terms ↔ z ∈ E.terms := by
  unfold subst
  split_ifs with hv
  · rcases ℓ with ⟨_ | t, c⟩
    · simp [Finset.mem_erase, hzv]
    · have hzt : z ≠ t := fun h => hzℓ (by simp [h])
      simp only [mem_symmDiff_singleton, Finset.mem_erase, ne_eq, hzv, not_false_eq_true, true_and]
      exact ⟨fun h => h.2 hzt, fun h => ⟨fun _ => hzt, fun _ => h⟩⟩
  · exact Iff.rfl

theorem mem_of_mem_subst {E : Equation} {v : ℕ} {ℓ : Lit} {z : ℕ}
    (h : z ∈ (E.subst v ℓ).terms) : z ∈ E.terms ∨ (v ∈ E.terms ∧ ℓ.arg = .node z) := by
  unfold subst at h
  split_ifs at h with hv
  · rcases ℓ with ⟨_ | t, c⟩
    · exact Or.inl (Finset.mem_of_mem_erase h)
    · by_cases hzt : z = t
      · exact Or.inr ⟨hv, by simp [hzt]⟩
      · exact Or.inl (Finset.mem_of_mem_erase ((mem_symmDiff_singleton.1 h).2 hzt))
  · exact Or.inl h

theorem card_subst_le {E : Equation} {v : ℕ} {ℓ : Lit} :
    (E.subst v ℓ).terms.card ≤ E.terms.card := by
  unfold subst
  split_ifs with hv
  · rcases ℓ with ⟨_ | t, c⟩
    · exact Finset.card_erase_le
    · have h := Finset.card_erase_of_mem hv
      have hpos : 0 < E.terms.card := Finset.card_pos.2 ⟨v, hv⟩
      calc (E.terms.erase v ∆ {t}).card ≤ (E.terms.erase v).card + 1 :=
            card_symmDiff_singleton_le _ _
        _ = E.terms.card := by omega
  · exact le_rfl

theorem notMem_subst {E : Equation} {v : ℕ} {ℓ : Lit} (hℓ : ℓ.arg ≠ .node v) :
    v ∉ (E.subst v ℓ).terms := by
  intro h
  unfold subst at h
  split_ifs at h with hv
  · rcases ℓ with ⟨_ | t, c⟩
    · exact Finset.notMem_erase v _ h
    · have ht : v ≠ t := fun h' => hℓ (by simp [h'])
      exact Finset.notMem_erase v _ ((mem_symmDiff_singleton.1 h).2 ht)
  · exact hv h

theorem subst_of_notMem {E : Equation} {v : ℕ} {ℓ : Lit} (h : v ∉ E.terms) : E.subst v ℓ = E := by
  unfold subst
  rw [ite_eq_right h]

theorem holds_congr {E : Equation} {val val' : ℕ → Bool} (h : ∀ i ∈ E.terms, val i = val' i) :
    E.Holds val ↔ E.Holds val' := by
  unfold Holds
  rw [Finset.sum_congr rfl h]

/-- An equation with `v` rerouted to a literal not reading `v` holds exactly when the equation
holds on the assignment giving `v` the value of the literal. -/
theorem holds_subst_update {E : Equation} {v : ℕ} {ℓ : Lit} (hℓ : ℓ.arg ≠ .node v)
    (val : ℕ → Bool) : (E.subst v ℓ).Holds val ↔ E.Holds (Function.update val v (ℓ.eval val)) := by
  have hℓu : ℓ.eval (Function.update val v (ℓ.eval val)) = ℓ.eval val :=
    Lit.eval_congr fun i hi => Function.update_of_ne (by rintro rfl; exact hℓ hi) _ _
  rw [← holds_subst (E := E) (show Function.update val v (ℓ.eval val) v = _ by
    rw [hℓu]; exact Function.update_self _ _ _)]
  exact holds_congr fun i hi =>
    (Function.update_of_ne (by rintro rfl; exact notMem_subst hℓ hi) _ _).symm

/-- Once `p = r + c`, the equation `v + p + r = rhs` reads `v = rhs + c`. -/
theorem holds_update_iff {E : Equation} {v p r : ℕ} (hterms : E.terms = {v, p, r})
    (hvp : v ≠ p) (hvr : v ≠ r) (hpr : p ≠ r) (val : ℕ → Bool) (c : Bool) :
    E.Holds (Function.update val p (val r ^^ c)) ↔ val v = (E.rhs ^^ c) := by
  rw [Equation.Holds, hterms, Finset.sum_insert (by simp [hvp, hvr]), Finset.sum_pair hpr]
  simp only [Function.update_self, Function.update_of_ne hvp, Function.update_of_ne hpr.symm]
  generalize val v = a; generalize val r = b; generalize E.rhs = d
  revert a b c d; decide

end Equation

/-! ### Moving affine gates into the affine system -/

/-- Add the argument `a` with coefficient `b` to the terms and right-hand side of an
equation. -/
def addArg (p : Finset ℕ × Bool) (b : Bool) (a : Arg) : Finset ℕ × Bool :=
  if b then
    match a with
    | .node t => (p.1 ∆ {t}, p.2)
    | .const v => (p.1, p.2 ^^ v)
  else p

private theorem sum_addArg (p : Finset ℕ × Bool) (b : Bool) (a : Arg) (val : ℕ → Bool) :
    ∑ i ∈ (addArg p b a).1, val i + (addArg p b a).2 =
      ∑ i ∈ p.1, val i + p.2 + (b && a.eval val) := by
  unfold addArg
  cases b
  · exact (add_zero _).symm
  · cases a with
    | node t =>
      simp only [ite_true, sum_symmDiff_singleton, Arg.eval_node, Bool.true_and]
      generalize ∑ i ∈ p.1, val i = s; generalize val t = v; generalize p.2 = r
      revert s v r; decide
    | const v =>
      simp only [ite_true, Arg.eval_const, Bool.true_and]
      generalize ∑ i ∈ p.1, val i = s; generalize p.2 = r
      revert s v r; decide

theorem mem_addArg {p : Finset ℕ × Bool} {b : Bool} {a : Arg} {z : ℕ}
    (h : z ∈ (addArg p b a).1) : z ∈ p.1 ∨ a = .node z := by
  unfold addArg at h
  cases b
  · exact Or.inl h
  · cases a with
    | node t =>
      by_cases hzt : z = t
      · exact Or.inr (by rw [hzt])
      · exact Or.inl ((mem_symmDiff_singleton.1 h).2 hzt)
    | const v => exact Or.inl h

private theorem card_addArg_le (p : Finset ℕ × Bool) (b : Bool) (a : Arg) :
    (addArg p b a).1.card ≤ p.1.card + 1 := by
  unfold addArg
  cases b
  · exact Nat.le_succ _
  · cases a with
    | node t => exact card_symmDiff_singleton_le _ _
    | const v => exact Nat.le_succ _

/-- The equation `J + b₁ t₁ + b₂ t₂ = c` replacing the affine gate
`J = b₁ t₁ + b₂ t₂ + c`. -/
def affEqn (g : Gate) (J : ℕ) : Equation :=
  let c₀ := g.op false false
  let p := addArg (addArg ({J}, c₀) (g.op true false ^^ c₀) g.left) (g.op false true ^^ c₀)
    g.right
  ⟨p.1, p.2⟩

theorem affEqn_holds {g : Gate} (hg : IsAffineOp g.op) (J : ℕ) (val : ℕ → Bool) :
    (affEqn g J).Holds val ↔ val J = g.eval val := by
  unfold affEqn Equation.Holds
  dsimp only
  have h1 := sum_addArg ({J}, g.op false false) (g.op true false ^^ g.op false false) g.left val
  have h2 := sum_addArg (addArg ({J}, g.op false false) (g.op true false ^^ g.op false false)
    g.left) (g.op false true ^^ g.op false false) g.right val
  rw [Finset.sum_singleton] at h1
  dsimp only at h1
  rw [h1] at h2
  unfold Gate.eval
  unfold IsAffineOp at hg
  generalize ∑ i ∈ (addArg (addArg ({J}, g.op false false) (g.op true false ^^ g.op false false)
    g.left) (g.op false true ^^ g.op false false) g.right).1, val i = s at h2 ⊢
  generalize (addArg (addArg ({J}, g.op false false) (g.op true false ^^ g.op false false)
    g.left) (g.op false true ^^ g.op false false) g.right).2 = r at h2 ⊢
  generalize g.left.eval val = l at h2 ⊢
  generalize g.right.eval val = rr at h2 ⊢
  generalize val J = j at h2 ⊢
  cases l <;> cases rr <;>
  · revert h2 hg
    generalize g.op false false = a
    generalize g.op true false = b
    generalize g.op false true = c
    generalize g.op true true = d
    revert s r j a b c d; decide

theorem mem_affEqn {g : Gate} {J z : ℕ} (h : z ∈ (affEqn g J).terms) : z = J ∨ g.Reads z := by
  unfold affEqn at h
  rcases mem_addArg h with h | h
  · rcases mem_addArg h with h | h
    · exact Or.inl (Finset.mem_singleton.1 h)
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem card_affEqn_le (g : Gate) (J : ℕ) : (affEqn g J).terms.card ≤ 3 := by
  unfold affEqn
  have h1 := card_addArg_le ({J}, g.op false false) (g.op true false ^^ g.op false false) g.left
  have h2 := card_addArg_le (addArg ({J}, g.op false false)
    (g.op true false ^^ g.op false false) g.left) (g.op false true ^^ g.op false false) g.right
  simp only [Finset.card_singleton] at h1
  exact h2.trans (by omega)

end Cslib.Circuits.Boolean.SemiCircuit
