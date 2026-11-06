/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic

/-!
# Executable weighted greedy multicover

[Wang2027], Theorem 4, Section 5 (PDF pp. 10–11): select an oracle of
positive marginal gain minimizing cost divided by gain, allowing repetition.
The finite universe is explicit and costs are rational, so the selector uses
decidable exact comparisons. Residual requirements store the source's
`max (r - d_e) 0`; `gain` counts the unsatisfied elements in an oracle's set.

`choose_spec` proves minimum-ratio selection; `batch_spec` proves termination
and multicover completion within `n*r` calls. `run_bill_le` and `batch_bill_le`
prove the harmonic comparison with every feasible benchmark batch.
This concerns deterministic batch construction. The iteration bound is not a
binary machine time/space certificate. Response-law, latency and hardness
claims are separate; `PartialCoverGreedy` connects the risk and cost bounds.

## Main definitions

* `choose`: exact minimum-ratio positive-marginal oracle selection.
* `batch`: executable repeated-set greedy multicover for uniform demands.

## Main results

* `batch_spec`: at most `n*r` calls and zero residual demand.
* `batch_bill_le`: harmonic comparison with every feasible benchmark batch.
-/

public section
namespace Cslib.Algorithms.Lean.Multicover
open Finset
variable {E : Type*} [DecidableEq E] [Fintype E]

/-- An oracle's known eligibility set and rational upper bound on its token cost. -/
structure Oracle (E : Type*) where
  /-- Elements that each call has a certified chance to cover. -/
  eligible : Finset E
  /-- Exact rational cost used by the selector. -/
  cost : ℚ
  deriving DecidableEq

/-- Unmet element requirements, allowing nonuniform demands. -/
abbrev Demand (E : Type*) := E → ℕ

/-- Number of unmet requirements. -/
@[expose] def remaining (d : Demand E) : ℕ := ∑ e, d e

/-- One call removes one requirement at each eligible, still unsatisfied element. -/
@[expose] def reduce (d : Demand E) (a : Oracle E) : Demand E :=
  fun e => if e ∈ a.eligible then d e - 1 else d e

/-- Marginal increase in the capped coverage potential. -/
@[expose] def gain (d : Demand E) (a : Oracle E) : ℕ :=
  (a.eligible.filter fun e => 0 < d e).card

/-- Cost per newly met requirement, used only at positive gain. -/
@[expose] def ratio (d : Demand E) (a : Oracle E) : ℚ := a.cost / gain d a

/-- Scan all oracles; ties retain the earlier oracle. Zero-gain oracles are ignored. -/
@[expose] def choose (d : Demand E) : List (Oracle E) → Option (Oracle E)
  | [] => none
  | a :: as =>
    if gain d a = 0 then choose d as
    else match choose d as with
      | none => some a
      | some b => some (if ratio d a ≤ ratio d b then a else b)

omit [DecidableEq E] [Fintype E] in
/-- The selected oracle belongs to the input, has positive gain, and minimizes the
actual ratio over all positive-gain input oracles. -/
theorem choose_spec (d : Demand E) (as : List (Oracle E)) :
    (choose d as = none ↔ ∀ a ∈ as, gain d a = 0) ∧
    (∀ a, choose d as = some a → a ∈ as ∧ 0 < gain d a ∧
      ∀ b ∈ as, 0 < gain d b → ratio d a ≤ ratio d b) := by
  induction as with
  | nil => simp [choose]
  | cons a as ih =>
    by_cases ha : gain d a = 0
    · simp only [choose, ha, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · simp [ih.1, ha]
      · intro b hb
        obtain ⟨hbmem, hbg, hbmin⟩ := ih.2 b hb
        refine ⟨List.mem_cons_of_mem _ hbmem, hbg, ?_⟩
        intro c hc hcg
        rcases List.mem_cons.mp hc with rfl | hc
        · omega
        · exact hbmin c hc hcg
    · simp only [choose, ha, ↓reduceIte]
      cases htail : choose d as with
      | none =>
        have hz := ih.1.mp htail
        refine ⟨?_, ?_⟩
        · constructor
          · intro hn; cases hn
          · intro hz; exact False.elim (ha (hz a List.mem_cons_self))
        intro b hb
        cases Option.some.inj hb
        refine ⟨List.mem_cons_self, Nat.pos_of_ne_zero ha, ?_⟩
        intro c hc hcg
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_rfl
        · have := hz c hc; omega
      | some b =>
        obtain ⟨hbmem, hbg, hbmin⟩ := ih.2 b htail
        refine ⟨?_, ?_⟩
        · constructor
          · intro hn; cases hn
          · intro hz; exact False.elim (ha (hz a List.mem_cons_self))
        dsimp only
        split_ifs with hab
        · intro c hc; cases Option.some.inj hc
          refine ⟨List.mem_cons_self, Nat.pos_of_ne_zero ha, ?_⟩
          intro c hc hcg
          rcases List.mem_cons.mp hc with rfl | hc
          · exact le_rfl
          · exact hab.trans (hbmin c hc hcg)
        · intro c hc; cases Option.some.inj hc
          refine ⟨List.mem_cons_of_mem _ hbmem, hbg, ?_⟩
          intro c hc hcg
          rcases List.mem_cons.mp hc with rfl | hc
          · exact (lt_of_not_ge hab).le
          · exact hbmin c hc hcg

/-- Exact accounting: the remaining demand drops by precisely the chosen marginal. -/
theorem remaining_reduce (d : Demand E) (a : Oracle E) :
    remaining (reduce d a) + gain d a = remaining d := by
  have hg : gain d a = ∑ e : E, if e ∈ a.eligible ∧ 0 < d e then 1 else 0 := by
    rw [gain, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.sum_subset (Finset.subset_univ a.eligible)
      (by intro e _ he; simp [he])]
    apply Finset.sum_congr rfl
    intro e he
    simp [he]
  change (∑ e, reduce d a e) + gain d a = ∑ e, d e
  rw [hg]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  clear hg
  by_cases he : e ∈ a.eligible
  · by_cases hd : 0 < d e
    · simp only [reduce, he, hd, and_self, ↓reduceIte]; omega
    · simp [reduce, he, Nat.eq_zero_of_not_pos hd]
  · simp [reduce, he]

omit [DecidableEq E] [Fintype E] in
/-- Diminishing returns holds coordinatewise, including at repeated selections. -/
theorem gain_antitone {d d' : Demand E} (h : ∀ e, d e ≤ d' e) (a : Oracle E) :
    gain d a ≤ gain d' a := by
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  exact ⟨he.1, lt_of_lt_of_le he.2 (h e)⟩

/-- Emit a list of calls. The fuel bounds the number of selected oracles. -/
@[expose] def run (as : List (Oracle E)) : ℕ → Demand E → List (Oracle E)
  | 0, _ => []
  | t + 1, d => match choose d as with
    | none => []
    | some a => a :: run as t (reduce d a)

/-- Apply a whole emitted batch to the residual requirements. -/
@[expose] def residual : Demand E → List (Oracle E) → Demand E
  | d, [] => d
  | d, a :: as => residual (reduce d a) as

omit [Fintype E] in
/-- Every selected call belongs to the supplied list, even when selected repeatedly. -/
theorem run_mem (as : List (Oracle E)) (t : ℕ) (d : Demand E) :
    ∀ a ∈ run as t d, a ∈ as := by
  induction t generalizing d with
  | zero => simp [run]
  | succ t ih =>
    simp only [run]
    cases hc : choose d as with
    | none => simp
    | some a =>
      intro b hb
      rcases List.mem_cons.mp hb with hba | hb
      · subst b; exact ((choose_spec d as).2 a hc).1
      · exact ih _ _ hb

omit [Fintype E] in
/-- At most one call is emitted per iteration. -/
theorem run_length_le (as : List (Oracle E)) (t : ℕ) (d : Demand E) :
    (run as t d).length ≤ t := by
  induction t generalizing d with
  | zero => simp [run]
  | succ t ih =>
    simp only [run]
    cases choose d as with
    | none => simp
    | some a => simpa using Nat.succ_le_succ (ih (reduce d a))

/-- If the listed eligibility sets cover the universe, the actual selector meets
all requirements after at most their sum many iterations. No performance
hypothesis is imposed on the choice function. -/
theorem run_complete (as : List (Oracle E))
    (hcover : ∀ e : E, ∃ a ∈ as, e ∈ a.eligible) (t : ℕ) (d : Demand E)
    (ht : remaining d ≤ t) : ∀ e, residual d (run as t d) e = 0 := by
  induction t generalizing d with
  | zero =>
    intro e
    have he := Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    simp only [remaining] at ht
    simpa [run, residual] using Nat.eq_zero_of_le_zero (he.trans ht)
  | succ t ih =>
    simp only [run]
    cases hc : choose d as with
    | none =>
      have hz := (choose_spec d as).1.mp hc
      intro e
      obtain ⟨a, ha, he⟩ := hcover e
      have hd : d e = 0 := by
        by_contra hn
        have hm : e ∈ a.eligible.filter (fun e => 0 < d e) :=
          Finset.mem_filter.mpr ⟨he, Nat.pos_of_ne_zero hn⟩
        have hp := Finset.card_pos.mpr ⟨e, hm⟩
        have := hz a ha
        unfold gain at this
        omega
      exact hd
    | some a =>
      have hp := ((choose_spec d as).2 a hc).2.1
      have hr := remaining_reduce d a
      exact ih (reduce d a) (by omega)

/-- Uniform-demand executable greedy batch. -/
@[expose] def batch (as : List (Oracle E)) (r : ℕ) : List (Oracle E) :=
  run as (Fintype.card E * r) (fun _ => r)

/-- The batch contains at most `n*r` calls and discharges every element demand. -/
theorem batch_spec (as : List (Oracle E))
    (hcover : ∀ e : E, ∃ a ∈ as, e ∈ a.eligible) (r : ℕ) :
    (batch as r).length ≤ Fintype.card E * r ∧
      ∀ e, residual (fun _ => r) (batch as r) e = 0 := by
  refine ⟨run_length_le _ _ _, run_complete as hcover _ _ ?_⟩
  simp [remaining]

omit [Fintype E] in
/-- Reducing demands preserves their coordinatewise order. -/
theorem reduce_mono {d d' : Demand E} (h : ∀ e, d e ≤ d' e) (a : Oracle E) :
    ∀ e, reduce d a e ≤ reduce d' a e := by
  intro e
  simp only [reduce]
  have := h e
  split_ifs <;> omega

omit [Fintype E] in
/-- Executing the same calls preserves coordinatewise order. -/
theorem residual_mono {d d' : Demand E} (h : ∀ e, d e ≤ d' e)
    (bs : List (Oracle E)) : ∀ e, residual d bs e ≤ residual d' bs e := by
  induction bs generalizing d d' with
  | nil => exact h
  | cons b bs ih => exact ih (reduce_mono h b)

/-- Frozen initial marginal gains upper-bound what any benchmark batch can discharge. -/
theorem remaining_le_gains (d : Demand E) (bs : List (Oracle E)) :
    remaining d ≤ remaining (residual d bs) + (bs.map (gain d)).sum := by
  induction bs generalizing d with
  | nil => simp [residual]
  | cons b bs ih =>
    have hi := ih (reduce d b)
    have hg : (bs.map (gain (reduce d b))).sum ≤ (bs.map (gain d)).sum := by
      apply List.sum_le_sum
      intro a ha
      exact gain_antitone (fun e => by simp only [reduce]; split_ifs <;> omega) a
    have hr := remaining_reduce d b
    simp only [residual, List.map_cons, List.sum_cons]
    omega

/-- The sum of the known call-cost upper bounds, counting repeated calls. -/
@[expose] def bill (bs : List (Oracle E)) : ℚ := (bs.map Oracle.cost).sum

omit [DecidableEq E] [Fintype E] in
/-- Nonnegative call bounds give a nonnegative batch bound. -/
theorem bill_nonneg (bs : List (Oracle E)) (h : ∀ b ∈ bs, 0 ≤ b.cost) : 0 ≤ bill bs := by
  unfold bill
  apply List.sum_nonneg
  intro x hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact h b hb

/-- Greedy's actual chosen call obeys the benchmark charging inequality.
The benchmark is any list meeting the current demands, not an assumed optimum. -/
theorem choose_charge (as bs : List (Oracle E)) (d : Demand E) (a : Oracle E)
    (ha : choose d as = some a) (hcost : ∀ b ∈ as, 0 ≤ b.cost)
    (hsub : ∀ b ∈ bs, b ∈ as) (hfull : ∀ e, residual d bs e = 0) :
    a.cost * remaining d ≤ (gain d a : ℚ) * bill bs := by
  obtain ⟨hamem, hag, hmin⟩ := (choose_spec d as).2 a ha
  have hcross : ∀ b ∈ bs, a.cost * (gain d b : ℚ) ≤ (gain d a : ℚ) * b.cost := by
    intro b hb
    by_cases hg : gain d b = 0
    · simp only [hg, Nat.cast_zero, mul_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (hcost b (hsub b hb))
    · have hm := hmin b (hsub b hb) (Nat.pos_of_ne_zero hg)
      unfold ratio at hm
      have hx := (div_le_div_iff₀ (by exact_mod_cast hag)
        (by exact_mod_cast Nat.pos_of_ne_zero hg)).mp hm
      simpa only [mul_comm] using hx
  have hsum : a.cost * ((bs.map (gain d)).sum : ℚ) ≤ (gain d a : ℚ) * bill bs := by
    have hs : ∀ cs : List (Oracle E),
        (∀ b ∈ cs, a.cost * (gain d b : ℚ) ≤ (gain d a : ℚ) * b.cost) →
        a.cost * ((cs.map (gain d)).sum : ℚ) ≤ (gain d a : ℚ) * bill cs := by
      intro cs hh
      induction cs with
      | nil => simp [bill]
      | cons b cs ih =>
        have hb := hh b List.mem_cons_self
        have hi := ih (fun b hb => hh b (List.mem_cons_of_mem _ hb))
        simp only [bill, List.map_cons, List.sum_cons, Nat.cast_add, mul_add] at *
        linarith
    exact hs bs hcross
  have hcapacity := remaining_le_gains d bs
  have hr : remaining (residual d bs) = 0 := by simp [remaining, hfull]
  rw [hr, zero_add] at hcapacity
  exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcapacity)
    (hcost a hamem)).trans hsum

private theorem harmonic_block (m s : ℕ) :
    (s : ℚ) / (m + s) ≤ harmonic (m + s) - harmonic m := by
  simp only [harmonic, Finset.sum_range_add, add_sub_cancel_left]
  have hterm : ∀ i ∈ Finset.range s,
      (m + s : ℚ)⁻¹ ≤ ((m + i + 1 : ℕ) : ℚ)⁻¹ := by
    intro i hi
    have his : i < s := Finset.mem_range.mp hi
    apply (inv_le_inv₀ (by exact_mod_cast (show 0 < m + s by omega))
      (by positivity)).mpr
    exact_mod_cast (show m + i + 1 ≤ m + s by omega)
  have hsum := Finset.sum_le_sum hterm
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_eq_mul_inv,
    Nat.cast_add, Nat.cast_one, add_assoc] using hsum

/-- Harmonic charging bound for the actual greedy execution, against every
nonnegative-cost batch meeting the initial requirements. Selection quality is
proved by `choose_spec`, rather than supplied as an algorithm hypothesis. -/
theorem run_bill_le (as bs : List (Oracle E)) (t : ℕ) (d : Demand E)
    (hcost : ∀ b ∈ as, 0 ≤ b.cost) (hsub : ∀ b ∈ bs, b ∈ as)
    (hfull : ∀ e, residual d bs e = 0) :
    bill (run as t d) ≤ harmonic (remaining d) * bill bs := by
  have hbn : 0 ≤ bill bs := bill_nonneg bs (fun b hb => hcost b (hsub b hb))
  have hhn : ∀ n, (0 : ℚ) ≤ harmonic n := fun n =>
    Finset.sum_nonneg (fun i _ => by positivity)
  induction t generalizing d with
  | zero => simpa [run, bill] using mul_nonneg (hhn _) hbn
  | succ t ih =>
    simp only [run]
    cases hc : choose d as with
    | none => simpa [bill] using mul_nonneg (hhn (remaining d)) hbn
    | some a =>
      have hp := ((choose_spec d as).2 a hc).2.1
      have hr := remaining_reduce d a
      have hpos : (0 : ℚ) < remaining d := by exact_mod_cast (by omega : 0 < remaining d)
      have hcharge := choose_charge as bs d a hc hcost hsub hfull
      have hstep : a.cost ≤ (gain d a : ℚ) / remaining d * bill bs := by
        rw [div_mul_eq_mul_div]
        exact (le_div_iff₀ hpos).mpr hcharge
      have hblock := harmonic_block (remaining (reduce d a)) (gain d a)
      have hcast : (remaining (reduce d a) : ℚ) + gain d a = remaining d := by
        exact_mod_cast hr
      rw [hr, hcast] at hblock
      have hsmall : ∀ e, residual (reduce d a) bs e = 0 := by
        intro e
        apply Nat.eq_zero_of_le_zero
        rw [← hfull e]
        exact residual_mono (fun e => by simp only [reduce]; split_ifs <;> omega) bs e
      have hi := ih (reduce d a) hsmall
      change a.cost + bill (run as t (reduce d a)) ≤ _
      have hb := mul_le_mul_of_nonneg_right hblock hbn
      nlinarith

/-- Uniform-demand greedy is a harmonic approximation to every feasible batch. -/
theorem batch_bill_le (as bs : List (Oracle E)) (r : ℕ)
    (hcost : ∀ b ∈ as, 0 ≤ b.cost) (hsub : ∀ b ∈ bs, b ∈ as)
    (hfull : ∀ e, residual (fun _ => r) bs e = 0) :
    bill (batch as r) ≤ harmonic (Fintype.card E * r) * bill bs := by
  have h := run_bill_le as bs (Fintype.card E * r) (fun _ => r) hcost hsub hfull
  simpa [batch, remaining] using h

end Cslib.Algorithms.Lean.Multicover
