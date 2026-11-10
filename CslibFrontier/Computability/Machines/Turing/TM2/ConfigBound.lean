/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.TM2.PolyTime
import Mathlib.Data.Nat.Find

/-!
# Exponential clocks for space-bounded Mathlib TM2 computations

A terminating deterministic computation cannot revisit a configuration before its first halted
configuration. A bound on every stack bounds the complete binary configuration encoding linearly;
there are fewer than exponentially many words of bounded length. Thus exponential padding
suffices to reach the output of any terminating computation with the supplied stack bound.

## Main results

* `Turing.TM2.exists_exponential_clock`: every terminating source run with bounded stacks has
  an exponential clock depending only on the machine and stack bound.

## References

The standard configuration-counting argument for deterministic space bounds; see
[AroraBarak09]. Source configurations and executions are Mathlib's
`Mathlib.Computability.TuringMachine.Computable`.
-/

@[expose] public section

namespace Turing.TM2

private def boundedWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => insert []
    (((boundedWords n).image (List.cons false)) ∪ ((boundedWords n).image (List.cons true)))

private theorem mem_boundedWords (word : List Bool) (width : ℕ) (h : word.length ≤ width) :
    word ∈ boundedWords width := by
  induction width generalizing word with
  | zero =>
    have hword : word = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst word
    exact Finset.mem_singleton_self _
  | succ width ih =>
    cases word with
    | nil => exact Finset.mem_insert_self _ _
    | cons bit word =>
      have hword := ih word (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using h)
      apply Finset.mem_insert_of_mem
      cases bit
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hword)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hword)

private theorem card_boundedWords_lt (width : ℕ) :
    (boundedWords width).card < 2 ^ (width + 1) := by
  induction width with
  | zero => decide
  | succ width ih =>
    have hcard := Finset.card_insert_le ([] : List Bool)
      (((boundedWords width).image (List.cons false)) ∪
        ((boundedWords width).image (List.cons true)))
    have hunion := Finset.card_union_le
      ((boundedWords width).image (List.cons false))
      ((boundedWords width).image (List.cons true))
    have hfalse : ((boundedWords width).image (List.cons false)).card ≤
        (boundedWords width).card := Finset.card_image_le
    have htrue : ((boundedWords width).image (List.cons true)).card ≤
        (boundedWords width).card := Finset.card_image_le
    simp only [boundedWords, pow_succ] at *
    omega

private theorem iterate_eq_of_bounded_encoding {α : Type} (f : α → α) (enc : α ↪ List Bool)
    (initial final : α) (width : ℕ) (hfinal : f final = final)
    (hterm : ∃ n, f^[n] initial = final)
    (hsize : ∀ n, (enc (f^[n] initial)).length ≤ width) :
    f^[2 ^ (width + 1)] initial = final := by
  classical
  let first := Nat.find hterm
  have hfirst : f^[first] initial = final := Nat.find_spec hterm
  have hmin : ∀ n < first, f^[n] initial ≠ final := fun n hn => Nat.find_min hterm hn
  have hinj : Set.InjOn (fun n => enc (f^[n] initial)) (Finset.range (first + 1)) := by
    intro i hi j hj heq
    have hi' : i ≤ first := by
      simpa only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff] using hi
    have hj' : j ≤ first := by
      simpa only [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff] using hj
    have hcfg : f^[i] initial = f^[j] initial := enc.injective heq
    suffices hle : ∀ i j, i < j → j ≤ first → f^[i] initial = f^[j] initial → False by
      rcases lt_trichotomy i j with h | h | h
      · exact False.elim (hle i j h hj' hcfg)
      · exact h
      · exact False.elim (hle j i h hi' hcfg.symm)
    intro i j hij hj hcfg
    have hearlier : f^[first - j + i] initial = final := by
      rw [Function.iterate_add_apply, hcfg, ← Function.iterate_add_apply,
        Nat.sub_add_cancel hj]
      exact hfirst
    exact hmin _ (by omega) hearlier
  have hcard : first + 1 ≤ (boundedWords width).card := by
    simpa only [Finset.card_range] using
      Finset.card_le_card_of_injOn (fun n => enc (f^[n] initial))
        (fun n _ => mem_boundedWords _ width (hsize n)) hinj
  have hclock : first ≤ 2 ^ (width + 1) := by
    have := card_boundedWords_lt width
    omega
  rw [← Nat.sub_add_cancel hclock, Function.iterate_add_apply, hfirst]
  exact Function.iterate_fixed hfinal _

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

/-- A fixed finite-alphabet TM2 has a uniform exponential clock for all terminating runs whose
stacks, including the initial input and final output, satisfy the supplied bound at every step. -/
theorem exists_exponential_clock (tm : FinTM2) [∀ k, Finite (tm.Γ k)] : ∃ C : ℕ,
    ∀ (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (space : ℕ),
      TM2Outputs tm input (some output) →
      (∀ i k, (((stepTotal tm.m)^[i] (initList tm input)).stk k).length ≤ space) →
      (stepTotal tm.m)^[2 ^ (C * (space + 1) + 1)] (initList tm input) = haltList tm output := by
  obtain ⟨C, hC⟩ := length_encCfg_le (Γ := tm.Γ) (Λ := tm.Λ) (σ := tm.σ)
  refine ⟨C, ?_⟩
  intro input output space hterm hspace
  have htime : TM2OutputsInTime tm input (some output) hterm.steps :=
    ⟨hterm, le_rfl⟩
  exact iterate_eq_of_bounded_encoding (stepTotal tm.m) encCfg
    (initList tm input) (haltList tm output) (C * (space + 1)) rfl
    ⟨hterm.steps, iterate_stepTotal_of_evals tm input output hterm.steps htime⟩
    (fun i => hC _ space (hspace i))

end Turing.TM2
