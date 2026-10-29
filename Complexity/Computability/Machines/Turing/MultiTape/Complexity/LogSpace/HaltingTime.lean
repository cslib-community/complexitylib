/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Configurations
public import Cslib.Foundations.Relation.RelatesInSteps

/-!
# Halting within the number of reachable views

A nondeterministic machine whose computation paths all halt, and whose computation prefixes all
stay within space `s`, halts within as many steps as it has reachable views: at most
`2 ^ (2 * coreLengthBound k State n s + 1)` on an input of length `n`
(`Turing.MultiTapeNTM.runsInTime_of_runsInSpace`). Under a logarithmic space bound this is
polynomial in `n` (`Turing.MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log`), so for
logarithmic-space machines "every branch halts" already gives a polynomial clock.

The argument is the classical one [Sipser, Section 8.4][Sipser2013]: the views along a
computation path form a walk of views (`Turing.MultiTapeNTM.ViewRep.step`); a running path longer
than the number of reachable views repeats a running view, and repeating the cycle gives running
walks of every length, which lift back to computation paths of the same length
(`Turing.MultiTapeNTM.ViewRep`), contradicting that every path halts.

## Main results

* `Turing.MultiTapeNTM.runsInTime_of_runsInSpace`: halting on every path within some time implies
  halting within the number of reachable views.
* `Turing.MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log`: under a logarithmic
  space bound, halting on every path implies halting within a polynomial time bound.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State : Type} {ntm : MultiTapeNTM k Bool State} {input : List Bool}

/-- **Pumping a cycle.** A path to `b` followed by any number of rounds of a cycle at `b`. -/
private theorem relatesInSteps_pump {α : Type*} {r : α → α → Prop} {i m : ℕ} {a b : α}
    (h : Relation.RelatesInSteps r a b i) (hcycle : Relation.RelatesInSteps r b b m)
    (rounds : ℕ) : Relation.RelatesInSteps r a b (i + rounds * m) := by
  induction rounds with
  | zero => simpa using h
  | succ rounds ih =>
    have := ih.trans hcycle
    rwa [Nat.add_assoc, ← Nat.succ_mul] at this

/-- **Views along a computation path.** A computation path has a chain of views from the initial
view, one view per configuration, each representing its configuration. -/
theorem exists_viewChain (p : ntm.RunPath input) (hp : p.head = ntm.initCfg input) :
    ∃ views : List (FiniteCfg k Bool State), ∃ _ : views.length = p.length + 1,
      views.IsChain ntm.ViewStep ∧ views.head? = some (ntm.initView input) ∧
      ∀ i (hi : i < views.length), ViewRep views[i] (p ⟨i, by omega⟩) := by
  induction p using RelSeries.inductionOn' with
  | singleton c =>
    simp only [RelSeries.head_singleton] at hp
    subst hp
    refine ⟨[ntm.initView input], rfl, .singleton _, rfl, fun i hi => ?_⟩
    obtain rfl : i = 0 := by simpa using hi
    exact viewRep_init input
  | snoc p c hc ih =>
    obtain ⟨views, hlen, hchain, hhead, hrep⟩ := ih (by simpa using hp)
    have hne : views ≠ [] := by rintro rfl; simp at hlen
    have hlast : ViewRep (views.getLast hne) p.last := by
      have := hrep (views.length - 1) (by omega)
      rw [List.getLast_eq_getElem]
      rw [RelSeries.last]
      convert this using 2
      ext; simp; omega
    change ntm.Step p.last c at hc
    -- the next view
    obtain ⟨next, hstep, hnext⟩ : ∃ next, ntm.ViewStep (views.getLast hne) next ∧
        ViewRep next c := by
      rcases hs : p.last.state with _ | state
      · rw [(step_of_halt hs).mp hc]
        refine ⟨views.getLast hne, ?_, hlast⟩
        simp only [ViewStep, hlast.state.trans hs]
      · simp only [Step, hs] at hc
        obtain ⟨action, htr, rfl⟩ := hc
        obtain ⟨hin, hwork⟩ := hlast.symbols
        refine ⟨_, ?_, hlast.step action⟩
        simp only [ViewStep, hlast.state.trans hs]
        exact ⟨action, by rwa [hin, hwork], rfl⟩
    refine ⟨views ++ [next], by simp [hlen], ?_, ?_, fun i hi => ?_⟩
    · exact hchain.append (.singleton _) (by
        intro x hx y hy
        simp only [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some.injEq] at hx
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hx hy
        exact hstep)
    · cases views with
      | nil => contradiction
      | cons => simpa using hhead
    · rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp (by simpa using hi)) with hi' | rfl
      · rw [List.getElem_append_left hi']
        have e : (p.snoc c hc) ⟨i, by simp; omega⟩ = p ⟨i, by omega⟩ := by
          rw [← RelSeries.snoc_cast_castSucc p c hc ⟨i, by omega⟩]; rfl
        exact (congrArg _ e).mpr (hrep i hi')
      · rw [List.getElem_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        have e : (p.snoc c hc) ⟨views.length, by simp; omega⟩ = c :=
          (congrArg (p.snoc c hc) (Fin.ext (by simp [hlen]))).trans (RelSeries.last_snoc p c hc)
        exact (congrArg _ e).mpr hnext

/-- **Counted view walks lift to computation paths** of the same length. -/
theorem exists_computationPath_of_relatesInSteps {n : ℕ} {finite : FiniteCfg k Bool State}
    (h : Relation.RelatesInSteps ntm.ViewStep (ntm.initView input) finite n) :
    ∃ p : ntm.ComputationPath input, p.time = n ∧ ViewRep finite p.last := by
  induction h with
  | refl =>
    exact ⟨⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩, rfl, viewRep_init input⟩
  | tail view next n _ hstep ih =>
    obtain ⟨p, hp, hrep⟩ := ih
    rcases hs : view.state with _ | state
    · simp only [ViewStep, hs] at hstep
      subst hstep
      have hnative : ntm.Step p.last p.last := by simp [Step, ← hrep.state, hs]
      exact ⟨⟨p.toRunPath.snoc _ hnative, by simpa using p.head_eq⟩,
        by simp [ComputationPath.time, RunPath.time, ← hp], by simpa using hrep⟩
    · simp only [ViewStep, hs] at hstep
      obtain ⟨action, htr, rfl⟩ := hstep
      obtain ⟨hin, hwork⟩ := hrep.symbols
      have hnative : ntm.Step p.last (action.apply p.last) := by
        simp only [Step, ← hrep.state, hs]
        exact ⟨action, by rwa [← hin, ← hwork], rfl⟩
      exact ⟨⟨p.toRunPath.snoc _ hnative, by simpa using p.head_eq⟩,
        by simp [ComputationPath.time, RunPath.time, ← hp], by simpa using hrep.step action⟩

variable [Finite State]

/-- **Halting within the number of reachable views.** If every computation path stays within
space `s` and every computation path halts within some time `t`, then every computation path
halts within `2 ^ (2 * coreLengthBound k State n s + 1)` steps, the bound on the number of
reachable views. -/
theorem runsInTime_of_runsInSpace {s t : ℕ} (hs : ntm.RunsInSpace input s)
    (ht : ntm.RunsInTime input t) :
    ntm.RunsInTime input (2 ^ (2 * coreLengthBound k State input.length s + 1)) := by
  set B := 2 ^ (2 * coreLengthBound k State input.length s + 1)
  intro p hp
  by_contra hlast
  -- every configuration on the path is running: halted configurations stay put
  have hrun : ∀ i, ¬ (p.toRunPath i).Halted := fun i hi =>
    hlast (RunPath.last_eq_of_halted p.toRunPath i hi ▸ hi)
  obtain ⟨views, hlen, hchain, hhead, hrep⟩ := exists_viewChain p.toRunPath p.head_eq
  have hne : views ≠ [] := by rintro rfl; simp at hlen
  have h0 : views[0]'(by omega) = ntm.initView input := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
    exact Option.some.inj hhead
  -- every view on the chain is reachable
  have hreach : ∀ finite ∈ views,
      Relation.ReflTransGen ntm.ViewStep (ntm.initView input) finite := by
    intro finite hf
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
    have := (hchain.relatesInSteps_getElem 0 j (by omega)).reflTransGen
    simp only [Nat.zero_add, h0] at this
    exact this
  -- more views than reachable views: some view repeats
  have hnotnodup : ¬ views.Nodup := fun hnodup => by
    have := length_le_of_nodup_reachable hs hnodup hreach
    simp only [ComputationPath.time, RunPath.time] at hp
    omega
  obtain ⟨i, j, hij, hj, heq⟩ : ∃ i j, ∃ _ : i < j, ∃ hj : j < views.length,
      views[i]'(by omega) = views[j] := by
    rw [List.nodup_iff_injective_get] at hnotnodup
    simp only [Function.Injective, not_forall] at hnotnodup
    obtain ⟨a, b, hab, hne'⟩ := hnotnodup
    rcases lt_or_gt_of_ne (fun h => hne' (Fin.ext h)) with h | h
    · exact ⟨a, b, h, b.2, hab⟩
    · exact ⟨b, a, h, a.2, hab.symm⟩
  -- the cycle at the repeated view, pumped to length at least `t`
  have hpre :
      Relation.RelatesInSteps ntm.ViewStep (ntm.initView input) (views[i]'(by omega)) i := by
    have := hchain.relatesInSteps_getElem 0 i (by omega)
    simp only [Nat.zero_add, h0] at this
    exact this
  have hcycle : Relation.RelatesInSteps ntm.ViewStep (views[i]'(by omega)) (views[i]'(by omega))
      (j - i) := by
    have := hchain.relatesInSteps_getElem i (j - i) (by omega)
    simp only [Nat.add_sub_cancel' hij.le] at this
    rwa [← heq] at this
  have hlong := relatesInSteps_pump hpre hcycle t
  obtain ⟨q, hq, hqrep⟩ := exists_computationPath_of_relatesInSteps hlong
  have hhalt := ht q (by rw [hq]; nlinarith [Nat.sub_pos_of_lt hij])
  -- the repeated view is running
  have hstate := (hrep i (by omega)).state
  exact hrun ⟨i, by omega⟩ (hstate.symm.trans (hqrep.state.trans hhalt))

/-- The polynomial clock of `exists_runsInTime_polynomial_of_runsInSpace_log`, with its exponent
spelled out. -/
private theorem runsInTime_polynomial_of_runsInSpace_log {c t : ℕ}
    (hs : ntm.RunsInSpace input (c * (Nat.log2 input.length + 1)))
    (ht : ntm.RunsInTime input t) :
    ntm.RunsInTime input (2 * (2 * (input.length + 1)) ^
      (2 * (8 + 2 * Nat.card (Option State) + 200 * k) * (c + 1))) := by
  refine (runsInTime_of_runsInSpace hs ht).mono ?_
  set K := 8 + 2 * Nat.card (Option State) + 200 * k
  set L := Nat.log2 input.length
  have hlog : 2 ^ L ≤ input.length + 1 := by
    rcases Nat.eq_zero_or_pos input.length with h | h
    · simp [L, h]
    · rw [show L = Nat.log 2 input.length from Nat.log2_eq_log_two]
      exact (Nat.pow_log_le_self 2 h.ne').trans (Nat.le_succ _)
  have hcore : coreLengthBound k State input.length (c * (L + 1)) = K * (c + 1) * (L + 1) := by
    simp only [coreLengthBound, K, L]
    ring
  have hbase : 2 ^ (L + 1) ≤ 2 * (input.length + 1) := by rw [pow_succ]; omega
  calc 2 ^ (2 * coreLengthBound k State input.length (c * (L + 1)) + 1)
      = 2 * (2 ^ (L + 1)) ^ (2 * K * (c + 1)) := by rw [hcore, ← pow_mul, pow_succ]; ring_nf
    _ ≤ 2 * (2 * (input.length + 1)) ^ (2 * K * (c + 1)) := by gcongr

/-- **Logarithmic space gives a polynomial clock.** For every space constant `c` there is an
exponent `d` such that on every input of length `n`, if every computation path stays within space
`c * (log₂ n + 1)` and every computation path halts within some time, then every computation path
halts within `2 * (2 * (n + 1)) ^ d` steps. -/
theorem exists_runsInTime_polynomial_of_runsInSpace_log (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) : ∃ d, ∀ {input : List Bool} {t : ℕ},
      ntm.RunsInSpace input (c * (Nat.log2 input.length + 1)) → ntm.RunsInTime input t →
        ntm.RunsInTime input (2 * (2 * (input.length + 1)) ^ d) :=
  ⟨_, fun hs ht => runsInTime_polynomial_of_runsInSpace_log hs ht⟩

end Turing.MultiTapeNTM
