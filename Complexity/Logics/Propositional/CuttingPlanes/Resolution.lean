/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CuttingPlanes
public import Complexity.Logics.Propositional.Resolution.Proof
import Mathlib.Tactic.Abel

/-!
# Cutting planes simulate resolution

Every resolution proof translates line by line into a cutting planes proof [Cook, Coullard and
Turán][CookCoullardTuran1987] [Jukna, Section 19.2][Jukna2012]. For a resolution step from
`C₁ = A ∨ v` and `C₂ = B ∨ ¬v` to `A ∨ B`
(`Cslib.Logic.PL.CuttingPlanes.derivableInSize_toIneq_resolvent`):

1. adding the inequalities of `C₁` and `C₂` cancels `v`, leaving `A + B ≥ 1` in the notation of
   `Cslib.Logic.PL.Clause.toIneq`, where a literal shared by `A` and `B` occurs with coefficient
   `2` and every other literal with coefficient `1`;
2. adding the axiom `ℓ ≥ 0` (`Cslib.Logic.PL.Literal.toIneq`) for each literal `ℓ` in exactly one
   of `A` and `B` gives `2 (A ∪ B) ≥ 1`;
3. dividing by `2` rounds the bound up to give `A ∪ B ≥ 1`, the inequality of the resolvent.

Resolution in this library has no weakening rule, and the resolvent of `C₁` and `C₂` is the union of
the two remaining parts. Step 2 is therefore needed to equalize coefficients, and it costs one
line per such literal; a resolution step costs at most `2 w₁ + 2 w₂` cutting planes lines, where
`wᵢ` is the width of `Cᵢ`. Jukna's constant-cost simulation instead resolves clauses that agree
outside the pivot, after weakening. A resolution proof of `s` lines of width at most `w` thus
becomes a cutting planes proof of at most `(4 w + 1) s` lines
(`Cslib.Logic.PL.CNF.IsProof.cuttingPlanes`), and a resolution refutation of `s` lines of a CNF on
`N` variables a cutting planes refutation of at most `(8 N + 1) s` lines
(`Cslib.Logic.PL.CNF.RefutableInSize.cuttingPlanes`). Sizes count lines; coefficient sizes are not
measured.

As a consequence, cutting planes refute exactly the unsatisfiable CNFs
(`Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_iff_not_satisfiable`).

## Main results

* `Cslib.Logic.PL.CuttingPlanes.derivableInSize_toIneq_resolvent`: one resolution step.
* `Cslib.Logic.PL.CNF.IsProof.cuttingPlanes`, `Cslib.Logic.PL.CNF.RefutableInSize.cuttingPlanes`:
  cutting planes simulate resolution.
* `Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_iff_not_satisfiable`: refutation
  completeness of cutting planes for CNFs.

## References

* [W. Cook, C. R. Coullard, Gy. Turán, *On the complexity of cutting-plane
  proofs*][CookCoullardTuran1987]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Section 19.2][Jukna2012]
-/

public section

open Finset

namespace Cslib.Logic.PL

open Ineq CuttingPlanes

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Halving `0 ≥ 1` plus twice `I` gives `0 ≥ 1` plus `I`. -/
private theorem div_two_contra_add_two_nsmul (I : Ineq V) :
    (contra + 2 • I).div 2 = contra + I := by
  refine div_eq_of Nat.two_pos ?_ ?_ ?_
  · ext v
    simp only [coeff_add, coeff_contra, coeff_nsmul, zero_add, Finsupp.smul_apply, smul_eq_mul,
      nsmul_eq_mul, Nat.cast_ofNat]
  · simp only [bound_add, bound_contra, bound_nsmul, nsmul_eq_mul]
    push_cast
    omega
  · simp only [bound_add, bound_contra, bound_nsmul, nsmul_eq_mul]
    push_cast
    omega

private theorem toFinset_resolvent {c₁ c₂ : Clause V} {v : V} :
    (c₁.resolvent c₂ v).toFinset = c₁.toFinset.erase (v, true) ∪ c₂.toFinset.erase (v, false) := by
  ext l
  simp only [List.mem_toFinset, Clause.mem_resolvent, mem_union, mem_erase]
  tauto

/-- **One resolution step in cutting planes**: the inequality of the resolvent of `c₁` and `c₂` on
`v` is derivable from the inequalities of `c₁` and `c₂` in at most `2 w₁ + 2 w₂` lines, where `wᵢ`
is the width of `cᵢ`. Adding the two inequalities cancels `v`, adding an axiom `ℓ ≥ 0` for each
literal in one of the remaining parts but not the other doubles every coefficient, and dividing by
two rounds the bound up. -/
theorem CuttingPlanes.derivableInSize_toIneq_resolvent {c₁ c₂ : Clause V} {v : V}
    (hv₁ : (v, true) ∈ c₁) (hv₂ : (v, false) ∈ c₂) :
    DerivableInSize {c₁.toIneq, c₂.toIneq} (c₁.resolvent c₂ v).toIneq
      (2 * c₁.width + 2 * c₂.width) := by
  set A := c₁.toFinset.erase (v, true)
  set B := c₂.toFinset.erase (v, false)
  set D := (A ∪ B) \ (A ∩ B)
  have h₁ : c₁.toIneq = contra + (nonneg v + ∑ l ∈ A, l.toIneq) := by
    rw [Clause.toIneq, ← Literal.toIneq_true, add_sum_erase _ _ (List.mem_toFinset.2 hv₁)]
  have h₂ : c₂.toIneq = contra + (leOne v + ∑ l ∈ B, l.toIneq) := by
    rw [Clause.toIneq, ← Literal.toIneq_false, add_sum_erase _ _ (List.mem_toFinset.2 hv₂)]
  have hsum : ∑ l ∈ A, l.toIneq + ∑ l ∈ B, l.toIneq + ∑ l ∈ D, l.toIneq =
      2 • ∑ l ∈ A ∪ B, l.toIneq := by
    rw [← sum_union_inter, add_assoc, add_comm (∑ l ∈ A ∩ B, _),
      sum_sdiff inter_subset_union, two_nsmul]
  have heq : c₁.toIneq + c₂.toIneq + ∑ l ∈ D, l.toIneq =
      contra + 2 • ∑ l ∈ A ∪ B, l.toIneq := by
    rw [← hsum, h₁, h₂]
    have := nonneg_add_leOne v
    calc contra + (nonneg v + ∑ l ∈ A, l.toIneq) + (contra + (leOne v + ∑ l ∈ B, l.toIneq)) +
          ∑ l ∈ D, l.toIneq
        = contra + (nonneg v + leOne v) + contra + (∑ l ∈ A, l.toIneq + ∑ l ∈ B, l.toIneq +
          ∑ l ∈ D, l.toIneq) := by abel
      _ = _ := by rw [this]; abel
  have hd := ((DerivableInSize.hyp (Γ := {c₁.toIneq, c₂.toIneq}) (Set.mem_insert _ _)).add
    (DerivableInSize.hyp (Set.mem_insert_of_mem _ rfl))).add_sum D
    (fun l _ => DerivableInSize.literal l)
  rw [heq] at hd
  have hdiv := hd.div 2 Nat.two_pos fun v => by
    simp only [coeff_add, coeff_contra, coeff_nsmul, zero_add, Finsupp.smul_apply]
    exact ⟨_, rfl⟩
  rw [div_two_contra_add_two_nsmul, ← toFinset_resolvent, ← Clause.toIneq] at hdiv
  refine hdiv.mono ?_
  have hD : #D ≤ #A + #B := (card_le_card sdiff_subset).trans (card_union_le A B)
  have hA : #A + 1 = c₁.width := card_erase_add_one (List.mem_toFinset.2 hv₁)
  have hB : #B + 1 = c₂.width := card_erase_add_one (List.mem_toFinset.2 hv₂)
  omega

/-- **Cutting planes simulate resolution** [Cook, Coullard and Turán][CookCoullardTuran1987]: a
resolution proof from `φ` of `s` lines, each of width at most `w`, becomes a cutting planes proof
from the inequalities of `φ` of at most `(4 w + 1) s` lines, among which are the inequalities of all
lines of the resolution proof. -/
theorem CNF.IsProof.cuttingPlanes {φ : CNF V} {ls : List (Clause V)} (h : φ.IsProof ls) {w : ℕ}
    (hw : ∀ c ∈ ls, c.width ≤ w) :
    ∃ ls', CuttingPlanes.IsProof φ.toIneqs ls' ∧ (∀ c ∈ ls, c.toIneq ∈ ls') ∧
      ls'.length ≤ (4 * w + 1) * ls.length := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | @mem ls c _ hc ih =>
    obtain ⟨ls', h', hmem, hlen⟩ := ih fun d hd => hw d (List.mem_cons_of_mem _ hd)
    refine ⟨_ :: ls', h'.hyp (CNF.toIneq_mem_toIneqs hc), fun d hd => ?_, ?_⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      exacts [List.mem_cons_self, List.mem_cons_of_mem _ (hmem d hd)]
    · rw [List.length_cons, List.length_cons, Nat.mul_succ]
      omega
  | @resolvent ls c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨ls', h', hmem, hlen⟩ := ih fun d hd => hw d (List.mem_cons_of_mem _ hd)
    obtain ⟨ls'', h'', hR, hlen''⟩ := (derivableInSize_toIneq_resolvent hv₁ hv₂).extend h'
      fun J hJ => Or.inr (by rcases hJ with rfl | rfl; exacts [hmem _ h₁, hmem _ h₂])
    refine ⟨ls'' ++ ls', h'', fun d hd => ?_, ?_⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      exacts [hR, List.mem_append_right _ (hmem d hd)]
    · have hw₁ := hw c₁ (List.mem_cons_of_mem _ h₁)
      have hw₂ := hw c₂ (List.mem_cons_of_mem _ h₂)
      rw [List.length_append, List.length_cons, Nat.mul_succ]
      omega

/-- **Cutting planes simulate resolution**, by size [Cook, Coullard and
Turán][CookCoullardTuran1987]: a resolution refutation of `s` lines of a CNF with `N` variables
gives a cutting planes refutation of its inequalities of at most `(8 N + 1) s` lines. -/
theorem CNF.RefutableInSize.cuttingPlanes {φ : CNF V} {s : ℕ} (h : φ.RefutableInSize s) :
    CuttingPlanes.RefutableInSize φ.toIneqs ((8 * #φ.vars.toFinset + 1) * s) := by
  obtain ⟨ls, hp, hnil, hlen⟩ := h
  obtain ⟨ls', h', hmem, hlen'⟩ := hp.cuttingPlanes fun c hc => hp.width_le hc
  refine ⟨ls', h', by simpa using hmem _ hnil, hlen'.trans ?_⟩
  rw [← mul_assoc]
  exact Nat.mul_le_mul_left _ hlen

/-- **Cutting planes refute exactly the unsatisfiable CNFs.** -/
theorem CuttingPlanes.exists_refutableInSize_iff_not_satisfiable {φ : CNF V} :
    (∃ s, CuttingPlanes.RefutableInSize φ.toIneqs s) ↔ ¬ φ.Satisfiable :=
  ⟨fun ⟨_, h⟩ => h.not_satisfiable, fun h =>
    let ⟨_, hs⟩ := CNF.exists_refutableInSize_iff_not_satisfiable.2 h
    ⟨_, hs.cuttingPlanes⟩⟩

end Cslib.Logic.PL
