/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Flip
public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment
public import CslibFrontier.Logics.Propositional.DNF
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# Normal forms for parity

An input `x` of a Boolean function `g` is an *isolated true input* when `g x` is true and `g` is
false at every neighbour of `x`. A term of a formula in disjunctive normal form computing `g` that
holds at an isolated true input mentions every variable, since flipping an unmentioned variable
would keep it true; so it holds at no other input. Hence such a formula has at least as many terms
as `g` has isolated true inputs (`DNF.card_isolatedInputs_le_length`), and dually a formula in
conjunctive normal form has at least as many clauses as isolated false inputs. Every input is
isolated for parity, so its normal forms on `n ≥ 1` bits have at least `2 ^ (n - 1)` terms or
clauses (`DNF.two_pow_le_length_of_eval_eq_parity`, `CNF.two_pow_le_length_of_eval_eq_parity`).
The same flip shows that a formula in disjunctive normal form whose terms have fewer literals than
a partial assignment has free bits does not compute the parity of the bits it fills in, up to
negation (`DNF.not_forall_eval_eq_parity_fill_bne`); this ends Håstad's argument for circuits of
constant depth.

ORs of formulas in conjunctive normal form for parity, of depth three, are in
`CslibFrontier/Logics/Propositional/Parity/DepthThree.lean`.

## Main results

* `Cslib.Logic.PL.DNF.card_isolatedInputs_le_length`,
  `Cslib.Logic.PL.CNF.card_isolatedInputs_le_length`: normal forms have a term or clause per
  isolated input.
* `Cslib.Logic.PL.DNF.two_pow_le_length_of_eval_eq_parity`,
  `Cslib.Logic.PL.CNF.two_pow_le_length_of_eval_eq_parity`: normal forms of parity have at least
  `2 ^ (n - 1)` terms or clauses.
* `Cslib.Logic.PL.DNF.not_forall_eval_eq_parity_fill_bne`: narrow formulas in disjunctive normal
  form do not compute restricted parity.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Function

variable {n : ℕ}

/-- **A formula in disjunctive normal form has a term per isolated true input** of the function it
computes. -/
theorem DNF.card_isolatedInputs_le_length {g : BitString n → Bool} {D : DNF (Fin n)}
    (hD : ∀ x, D.eval x = g x) :
    #(BitString.isolatedInputs g true) ≤ D.length := by
  set S := BitString.isolatedInputs g true
  -- an isolated true input chooses a term holding there
  have hchoose : ∀ x ∈ S, ∃ t ∈ D, t.eval x = true :=
    fun x hx => (DNF.eval_eq_true_iff x D).1 ((hD x).trans (BitString.mem_isolatedInputs.1 hx).1)
  choose! T hT hTx using hchoose
  -- such a term mentions every variable, so it determines the input
  have hall : ∀ x ∈ S, ∀ i : Fin n, ∃ b, (i, b) ∈ T x := fun x hx i => by
    by_contra h'
    have h := not_exists.1 h'
    have hflip : (T x).eval (update x i !x i) = true :=
      (Term.eval_update_of_forall_ne (fun l hl hli => h l.2 (hli ▸ hl)) x _).trans (hTx x hx)
    have h1 := (hD _).symm.trans ((DNF.eval_eq_true_iff _ D).2 ⟨T x, hT x hx, hflip⟩)
    rw [(BitString.mem_isolatedInputs.1 hx).2 i] at h1
    exact Bool.false_ne_true h1
  have hinj : Set.InjOn T S := by
    intro x hx y hy hxy
    funext i
    obtain ⟨b, hb⟩ := hall x hx i
    have h₁ := (Term.eval_eq_true_iff x _).1 (hTx x hx) _ hb
    have h₂ := (Term.eval_eq_true_iff y _).1 (hTx y hy) _ (hxy ▸ hb)
    exact h₁.trans h₂.symm
  calc #S
      = #(S.image T) := (card_image_of_injOn hinj).symm
    _ ≤ #D.toFinset := card_le_card fun t ht => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 ht
        exact List.mem_toFinset.2 (hT x hx)
    _ ≤ D.length := List.toFinset_card_le D

/-- **A formula in conjunctive normal form has a clause per isolated false input** of the function
it computes: its negation is a formula in disjunctive normal form for the negated function. -/
theorem CNF.card_isolatedInputs_le_length {g : BitString n → Bool} {φ : CNF (Fin n)}
    (hφ : ∀ x, φ.eval x = g x) :
    #(BitString.isolatedInputs g false) ≤ φ.length := by
  have h := DNF.card_isolatedInputs_le_length (g := fun x => !g x) (D := φ.negate) fun x => by
    rw [CNF.eval_negate, hφ]
  rw [CNF.negate, List.length_map, BitString.isolatedInputs_not] at h
  exact h

/-- **Formulas in disjunctive normal form for parity** of `n ≥ 1` bits have at least
`2 ^ (n - 1)` terms. -/
theorem DNF.two_pow_le_length_of_eval_eq_parity (hn : 1 ≤ n) {D : DNF (Fin n)}
    (hD : ∀ x, D.eval x = parity n x) : 2 ^ (n - 1) ≤ D.length := by
  refine le_of_eq_of_le ?_ (DNF.card_isolatedInputs_le_length hD)
  rw [← card_filter_parity_eq_true hn]
  congr 1
  ext x
  simp +contextual [parity_update_not]

/-- **Formulas in conjunctive normal form for parity** of `n ≥ 1` bits have at least
`2 ^ (n - 1)` clauses. -/
theorem CNF.two_pow_le_length_of_eval_eq_parity (hn : 1 ≤ n) {φ : CNF (Fin n)}
    (hφ : ∀ x, φ.eval x = parity n x) : 2 ^ (n - 1) ≤ φ.length := by
  refine le_of_eq_of_le ?_ (CNF.card_isolatedInputs_le_length hφ)
  rw [← card_filter_parity_eq_false hn]
  congr 1
  ext x
  simp +contextual [parity_update_not]

/-- **Narrow formulas in disjunctive normal form miss restricted parity.** If every term of `D` has
fewer literals than `ρ` has free bits, and `ρ` has a free bit, then `D` does not compute the parity
of the bits filled in by `ρ`, up to negation: a satisfied term misses a free bit, and flipping it
keeps the term satisfied but flips the parity. -/
theorem DNF.not_forall_eval_eq_parity_fill_bne {ρ : BitString.PartialAssignment (Fin n)}
    {D : DNF (Fin n)} (hD : ∀ t ∈ D, t.length < #ρ.free) (hρ : ρ.free.Nonempty) (c : Bool) :
    ¬ ∀ y, DNF.eval y D = (parity n (ρ.fill y) != c) := by
  intro h
  -- flipping a free bit flips restricted parity
  have hflip : ∀ y i, i ∈ ρ.free → parity n (ρ.fill (update y i !y i)) = !parity n (ρ.fill y) :=
    fun y i hi => by
      have hρi := BitString.PartialAssignment.mem_free.1 hi
      rw [BitString.PartialAssignment.fill_update_of_eq_none hρi,
        ← BitString.PartialAssignment.fill_of_eq_none hρi y, parity_update_not]
  -- some input makes the right side true
  obtain ⟨i₀, hi₀⟩ := hρ
  obtain ⟨y, hy⟩ : ∃ y, (parity n (ρ.fill y) != c) = true := by
    by_cases h0 : (parity n (ρ.fill fun _ => false) != c) = true
    · exact ⟨_, h0⟩
    · refine ⟨update (fun _ => false) i₀ (!false), ?_⟩
      rw [hflip _ i₀ hi₀]
      revert h0
      cases parity n (ρ.fill fun _ => false) <;> cases c <;> simp
  obtain ⟨t, ht, hty⟩ := (DNF.eval_eq_true_iff y D).1 ((h y).trans hy)
  -- the term misses a free bit, and stays true when it flips
  obtain ⟨i, hi, hit⟩ : ∃ i ∈ ρ.free, i ∉ t.map Prod.fst := by
    by_contra! hsub
    have hle : #ρ.free ≤ t.length :=
      (card_le_card fun i hi => List.mem_toFinset.2 (hsub i hi)).trans
        ((List.toFinset_card_le _).trans_eq (by simp))
    exact absurd (hD t ht) (by omega)
  have hty' : t.eval (update y i !y i) = true :=
    (Term.eval_update_of_forall_ne (fun l hl hli => hit (List.mem_map.2 ⟨l, hl, hli⟩)) y _).trans
      hty
  have h1 := (h _).symm.trans ((DNF.eval_eq_true_iff _ D).2 ⟨t, ht, hty'⟩)
  rw [hflip y i hi] at h1
  revert hy h1
  cases parity n (ρ.fill y) <;> cases c <;> simp

end Cslib.Logic.PL
