/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Clique
public import Complexity.Computability.Circuit.FanIn
public import Cslib.Computability.Circuit.Complexity
public import Complexity.Computability.Circuit.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Every edge is essential to the clique function

For `2 ≤ k ≤ n`, removing one edge from the complete graph on a `k`-set through it destroys every
`k`-clique, so the `k`-clique function depends on every edge (`essentialAt_clique`). A monotone
circuit has fan-in at most two, so it has at least `n.choose 2 - 1` gates
(`edgeCount_le_succ_size`). This settles small clique sizes, where the method of approximations
says nothing.

It also records that monotone circuits compute the clique function at all, as the disjunction over
the `k`-sets of the conjunction of their edges (`exists_computes_clique`), so that the lower bounds
for it are not vacuous.

## Main results

* `Cslib.Circuits.Monotone.exists_computes_clique`: some monotone circuit computes `k`-clique.
* `Cslib.Circuits.Monotone.essentialAt_clique`: every edge is essential to `k`-clique.
* `Cslib.Circuits.Monotone.edgeCount_le_succ_size`,
  `Cslib.Circuits.Monotone.edgeCount_le_two_pow_depth`: the resulting size and depth bounds.
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

open Cslib.Circuits.Clique Finset

variable {n k : ℕ}

/-- Monotone programs have fan-in at most two. -/
private theorem program_fanInAtMost_two {g : ℕ} (p : Program signature n g) : p.FanInAtMost 2 := by
  induction p with
  | empty => trivial
  | gate p line ih => exact ⟨ih, by cases line.op <;> simp⟩

private theorem fold_and_eq_true {ι : Type*} (t : Finset ι) (f : ι → Bool) :
    t.fold (· && ·) true f = true ↔ ∀ i ∈ t, f i = true := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => simp [Finset.fold_insert hi, ih]

private theorem fold_or_eq_true {ι : Type*} (t : Finset ι) (f : ι → Bool) :
    t.fold (· || ·) false f = true ↔ ∃ i ∈ t, f i = true := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => simp [Finset.fold_insert hi, ih]

/-- **Monotone circuits compute cliques**: the disjunction over the `k`-sets of the conjunction
of their edges. -/
theorem exists_computes_clique (n k : ℕ) :
    ∃ C : Circuit signature (edgeCount n) 1, C.Computes interpretation (single (clique n k)) := by
  classical
  have hand (f g : BooleanFunction (edgeCount n)) :
      Synthesis interpretation {f, g} {fun x => f x && g x} 1 := by
    simpa [interpretation] using Synthesis.gate (I := interpretation) (s := {f, g}) Op.and
      (fun i => if (i : ℕ) = 0 then f else g) fun i => by split <;> simp
  have hor (f g : BooleanFunction (edgeCount n)) :
      Synthesis interpretation {f, g} {fun x => f x || g x} 1 := by
    simpa [interpretation] using Synthesis.gate (I := interpretation) (s := {f, g}) Op.or
      (fun i => if (i : ℕ) = 0 then f else g) fun i => by split <;> simp
  have hconst (b : Bool) : Synthesis interpretation (inputs (edgeCount n)) {fun _ => b} 1 := by
    simpa [interpretation] using Synthesis.nullary (I := interpretation)
      (s := inputs (edgeCount n)) (.const b) rfl
  have h := Synthesis.finset_fold (· || ·) 1 hor ((univ : Finset (Fin n)).powersetCard k)
    (f := fun t x => (univ.filter fun e : Edge n => e.1.toFinset ⊆ t).fold (· && ·) true
      fun e => x (edgeEquiv n e)) (hconst false) fun t _ =>
      Synthesis.finset_fold (· && ·) 1 hand _ (hconst true) fun e _ =>
        Synthesis.of_mem ⟨edgeEquiv n e, rfl⟩
  obtain ⟨C, hC, -⟩ := h.exists_circuit
  refine ⟨C, fun x => (hC x).trans (funext fun _ => ?_)⟩
  change (univ.powersetCard k).fold (· || ·) false (fun t =>
    (univ.filter fun e : Edge n => e.1.toFinset ⊆ t).fold (· && ·) true
      fun e => x (edgeEquiv n e)) = clique n k x
  rw [Bool.eq_iff_iff, fold_or_eq_true, clique, decide_eq_true_iff]
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, (mem_powersetCard.1 ht).2, fun e he =>
      (fold_and_eq_true _ _).1 h e (mem_filter.2 ⟨mem_univ _, he⟩)⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, mem_powersetCard.2 ⟨subset_univ _, ht⟩,
      (fold_and_eq_true _ _).2 fun e he => h e (mem_filter.1 he).2⟩

/-- The monotone circuit complexity of `k`-clique is finite. -/
theorem ecomplexity_clique_ne_top (n k : ℕ) :
    ecomplexity interpretation (single (clique n k)) ≠ ⊤ :=
  ecomplexity_ne_top_iff.2 (exists_computes_clique n k)

/-- For `2 ≤ k ≤ n`, every edge is essential to `k`-clique. -/
theorem essentialAt_clique (hk : 2 ≤ k) (hkn : k ≤ n) (i : Fin (edgeCount n)) :
    EssentialAt (single (clique n k)) i := by
  let e := (edgeEquiv n).symm i
  have he : e.1.toFinset.card ≤ k := by
    rw [Sym2.card_toFinset_of_not_isDiag _ e.2]
    exact hk
  obtain ⟨s, hes, -, hs⟩ := exists_subsuperset_card_eq (subset_univ _) he (by simpa using hkn)
  refine ⟨ofFinset s, Function.update (ofFinset s) i false,
    fun j hj => (Function.update_of_ne hj _ _).symm, fun h => ?_⟩
  have h0 := congrFun h 0
  simp only [single, clique_ofFinset hs] at h0
  obtain ⟨t, ht, hyt⟩ := of_decide_eq_true h0.symm
  have hxt : Contains (ofFinset s) t := fun e' he' => by
    have := hyt e' he'
    by_cases hi : edgeEquiv n e' = i
    · rw [hi, Function.update_self] at this
      exact absurd this Bool.false_ne_true
    · rwa [Function.update_of_ne hi] at this
  have hts : t = s :=
    eq_of_subset_of_card_le (subset_of_contains_ofFinset (by omega) hxt) (by omega)
  have := hyt e (hts ▸ hes)
  rw [show edgeEquiv n e = i from Equiv.apply_symm_apply _ _, Function.update_self] at this
  exact Bool.false_ne_true this

/-- For `2 ≤ k ≤ n`, a monotone circuit computing `k`-clique has at least `n.choose 2 - 1`
gates. -/
theorem edgeCount_le_succ_size (hk : 2 ≤ k) (hkn : k ≤ n) {C : Circuit signature (edgeCount n) 1}
    (hC : C.Computes interpretation (single (clique n k))) : edgeCount n ≤ 1 + C.size := by
  simpa using C.essential_le_size hC (selected := univ) (fun i _ => essentialAt_clique hk hkn i)
    (program_fanInAtMost_two C.program)

/-- For `2 ≤ k ≤ n`, a monotone circuit computing `k`-clique has depth at least `log₂ C(n, 2)`. -/
theorem edgeCount_le_two_pow_depth (hk : 2 ≤ k) (hkn : k ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : C.Computes interpretation (single (clique n k))) : edgeCount n ≤ 2 ^ C.depth := by
  simpa using C.essential_le_depth hC (selected := univ) (fun i _ => essentialAt_clique hk hkn i)
    (program_fanInAtMost_two C.program)

/-- There are at least `(n / 2) ^ 2` possible edges. -/
theorem sq_half_le_edgeCount (n : ℕ) : (n / 2) ^ 2 ≤ edgeCount n := by
  rw [edgeCount_eq_choose, Nat.choose_two_right, Nat.le_div_iff_mul_le (by decide)]
  have h := Nat.div_mul_le_self n 2
  set m := n / 2
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · nlinarith [Nat.sub_add_cancel (show 1 ≤ n by omega)]

end Cslib.Circuits.Monotone
