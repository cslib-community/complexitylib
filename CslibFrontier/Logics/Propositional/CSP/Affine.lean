/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Polymorphism
public import CslibFrontier.Foundations.Data.BitString.Parity
import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.FinCases

/-!
# Affine Boolean relations

An affine equation is a list of variables and a Boolean right-hand side. Evaluation sums the
listed bits in the existing Boolean ring, so repeated occurrences cancel in pairs. Empty lists
express both constant equations, including the inconsistent equation `0 = 1`.

For any finite coordinate type, preservation by ternary parity is equivalent to definability by
a finite conjunction of these equations, without auxiliary variables. This is the normal-form
claim of [Chen2006CSP], Theorem 4.3, printed pp. 15–16 (arXiv version 1), including empty and
nullary relations. The proof uses linear separation of the subgroup obtained by translating a
nonempty relation, rather than Chen's induction on coordinates. No algorithmic complexity claim
is made in this module.

## Main definitions

* `Cslib.Logic.PL.AffineEquation`: an affine parity equation with repeated variables allowed.
* `Cslib.Logic.PL.AffineEquation.Holds`: satisfaction of one equation.
* `Cslib.Logic.PL.AffineSystem.Holds`: satisfaction of a conjunction of equations.

## Main results

* `Cslib.Logic.PL.isPolymorphism_parity_iff_exists_affineSystem`: the finite Boolean affine
  normal-form characterization.
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*}

/-- An affine parity equation: a list of variables, with repetitions, and its right-hand side. -/
abbrev AffineEquation (V : Type*) := List V × Bool

/-- A finite conjunction of affine parity equations. -/
abbrev AffineSystem (V : Type*) := List (AffineEquation V)

/-- The sum of the listed bits equals the right-hand side in the Boolean ring. -/
@[expose] def AffineEquation.Holds (e : AffineEquation V) (a : V → Bool) : Prop :=
  (e.1.map a).sum = e.2

/-- Every equation in the system holds. -/
@[expose] def AffineSystem.Holds (F : AffineSystem V) (a : V → Bool) : Prop :=
  ∀ e ∈ F, e.Holds a

/-- Two occurrences of the same variable cancel, with no condition on the remaining list. -/
theorem AffineEquation.holds_cons_cons (v : V) (vs : List V) (b : Bool) (a : V → Bool) :
    AffineEquation.Holds (v :: v :: vs, b) a ↔ AffineEquation.Holds (vs, b) a := by
  simp [Holds, ← add_assoc, BooleanRing.add_self]

/-- Ternary parity on the existing Boolean cube is coordinatewise addition of three tuples. -/
theorem isPolymorphism_parity_iff {R : Set (V → Bool)} :
    IsPolymorphism (Cslib.parity 3) R ↔
      ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x + y + z ∈ R := by
  have hp (a : Fin 3 → Bool) : Cslib.parity 3 a = a 0 + a 1 + a 2 := by
    simp [Cslib.parity, Cslib.parityOn_eq_sum, Fin.sum_univ_succ, add_assoc]
  constructor
  · intro h x hx y hy z hz
    have ht := h ![x, y, z] (by intro j; fin_cases j <;> assumption)
    convert ht using 1
    funext i
    simp [hp]
  · intro h a ha
    convert h (a 0) (ha 0) (a 1) (ha 1) (a 2) (ha 2) using 1
    funext i
    exact hp _

/-- Every affine equation is preserved by ternary parity. -/
theorem AffineEquation.isPolymorphism_parity (e : AffineEquation V) :
    IsPolymorphism (Cslib.parity 3) {a | e.Holds a} := by
  rw [isPolymorphism_parity_iff]
  intro x hx y hy z hz
  have hadd (x y : V → Bool) : (e.1.map (x + y)).sum =
      (e.1.map x).sum + (e.1.map y).sum := by
    induction e.1 with
    | nil => simp
    | cons v vs ih => simp only [List.map_cons, List.sum_cons, Pi.add_apply, ih]; abel
  change (e.1.map (x + y + z)).sum = e.2
  rw [hadd, hadd, hx, hy, hz, BooleanRing.add_self, zero_add]

/-- Every conjunction of affine equations is preserved by ternary parity. -/
theorem AffineSystem.isPolymorphism_parity (F : AffineSystem V) :
    IsPolymorphism (Cslib.parity 3) {a | F.Holds a} := by
  intro a ha e he
  exact e.isPolymorphism_parity a (fun j => ha j e he)

/-- A tuple outside a finite parity-preserved relation can be separated by an affine equation.
The empty relation is separated by the inconsistent constant equation. -/
theorem exists_separating_affineEquation [Finite V] {R : Set (V → Bool)}
    (hR : IsPolymorphism (Cslib.parity 3) R) {a : V → Bool} (ha : a ∉ R) :
    ∃ e : AffineEquation V, (∀ b ∈ R, e.Holds b) ∧ ¬e.Holds a := by
  classical
  let _ := Fintype.ofFinite V
  by_cases hne : R.Nonempty
  · obtain ⟨c, hc⟩ := hne
    have hclosed := isPolymorphism_parity_iff.mp hR
    let H : AddSubgroup (V → Bool) :=
      { carrier := {x | x + c ∈ R}
        zero_mem' := by simpa using hc
        add_mem' := by
          intro x y hx hy
          have h := hclosed (x + c) hx (y + c) hy c hc
          change (x + y) + c ∈ R
          have heq : x + c + (y + c) + c = (x + y) + c := by
            rw [show x + c + (y + c) + c = (x + y) + c + (c + c) by abel,
              BitString.add_self, add_zero]
          rwa [heq] at h
        neg_mem' := by
          intro x hx
          change -x + c ∈ R
          have heq : -x = x := by funext i; exact Bool.neg_eq_id _
          rwa [heq] }
    let : Module (ZMod 2) (V → Bool) :=
      AddCommGroup.zmodModule (fun x => (two_nsmul x).trans (BitString.add_self x))
    let W := AddSubgroup.toZModSubmodule 2 H
    have hnot : a + c ∉ W := by
      change ¬(a + c) + c ∈ R
      simpa only [add_assoc, BitString.add_self, add_zero] using ha
    obtain ⟨f, hf, hker⟩ :=
      Submodule.exists_le_ker_of_notMem (K := ZMod 2) (p := W) hnot
    let g : (V → Bool) → Bool := fun x => decide (f x ≠ 0)
    have hadd : ∀ x y, g (x + y) = (g x ^^ g y) := by
      intro x y
      change decide (f (x + y) ≠ 0) = _
      rw [map_add]
      have h (s t : ZMod 2) : decide (s + t ≠ 0) =
          (decide (s ≠ 0) ^^ decide (t ≠ 0)) := by
        fin_cases s <;> fin_cases t <;> decide
      exact h _ _
    obtain ⟨S, hS⟩ := Cslib.BitString.exists_eq_parityOn_iff.mpr hadd
    have hg (b : V → Bool) (hb : b ∈ R) : g b = g c := by
      have hmem : b + c ∈ W := by
        change (b + c) + c ∈ R
        simpa only [add_assoc, BitString.add_self, add_zero] using hb
      have hz : g (b + c) = false := by
        simp [g, LinearMap.mem_ker.mp (hker hmem)]
      rw [hadd] at hz
      cases hb' : g b <;> cases hc' : g c <;> simp_all
    refine ⟨(S.toList, Cslib.parityOn S c), ?_, ?_⟩
    · intro b hb
      change (S.toList.map b).sum = Cslib.parityOn S c
      rw [Finset.sum_map_toList, ← Cslib.parityOn_eq_sum]
      exact (congrFun hS b).symm.trans ((hg b hb).trans (congrFun hS c))
    · intro he
      have hgc : g a = g c := by
        rw [hS]
        simpa only [AffineEquation.Holds, Finset.sum_map_toList,
          ← Cslib.parityOn_eq_sum] using he
      have hgac : g (a + c) = false := by rw [hadd, hgc, Bool.xor_self]
      have : g (a + c) = true := by simpa [g] using hf
      exact Bool.false_ne_true (hgac.symm.trans this)
  · exact ⟨([], true), fun b hb => (hne ⟨b, hb⟩).elim, by simp [AffineEquation.Holds]⟩

/-- **Parity preservation iff affine definability.** Empty and nullary relations are included;
there are no auxiliary variables. The defining system is finite, with no claimed size bound. -/
theorem isPolymorphism_parity_iff_exists_affineSystem [Finite V] (R : Set (V → Bool)) :
    IsPolymorphism (Cslib.parity 3) R ↔
      ∃ F : AffineSystem V, ∀ a, a ∈ R ↔ F.Holds a := by
  classical
  let _ := Fintype.ofFinite V
  constructor
  · intro hR
    have hex (a : V → Bool) : ∃ e : AffineEquation V,
        (∀ b ∈ R, e.Holds b) ∧ (a ∉ R → ¬e.Holds a) := by
      by_cases ha : a ∈ R
      · exact ⟨([], false), by simp [AffineEquation.Holds, Bool.zero_eq_false],
          fun h => (h ha).elim⟩
      · obtain ⟨e, he, hbad⟩ := exists_separating_affineEquation hR ha
        exact ⟨e, he, fun _ => hbad⟩
    choose e he hbad using hex
    let F := (Finset.univ.toList : List (V → Bool)).map e
    refine ⟨F, fun a => ⟨?_, ?_⟩⟩
    · intro ha q hq
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hq
      exact he b a ha
    · intro hF
      by_contra ha
      exact hbad a ha (hF _ (List.mem_map.mpr ⟨a, by simp, rfl⟩))
  · rintro ⟨F, hF⟩
    have hset : R = {a | F.Holds a} := Set.ext hF
    rw [hset]
    exact F.isPolymorphism_parity

end Cslib.Logic.PL
