/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.Reverse.Program
public import Complexity.Computability.Machines.Turing.TM2.Simulation

/-!
# Canonical cleanup for the multi-tape to TM2 compiler

Cleanup discards the input and work stacks, reverses the accumulated output onto the output
stack, and resets finite control. Existing output is retained as a suffix.

## Main definitions

* `StateTransition.EvalsToInTime.cons`, `.mono`: prepend one transition or enlarge the
  clock of a bounded partial execution.
* `Turing.MultiTapeTM.ToTM2.auxiliaryLength`: storage discarded by cleanup.
* `Turing.MultiTapeTM.ToTM2.totalStackLength`: storage on all stacks, including input and output.

## Main results

* `Turing.MultiTapeTM.ToTM2.cleanupEvals`: canonical halting with an explicit linear clock.
* `Turing.MultiTapeTM.ToTM2.cleanup_stack_bound`: cleanup never increases total stack storage.

## References

* [C. Papadimitriou, *Computational Complexity*, Chapter 2][Papadimitriou94]
-/

public section

namespace StateTransition.EvalsToInTime

/-- Prepend one transition to a bounded execution. -/
def cons {α : Type} {f : α → Option α} {a b c : α} {n : ℕ}
    (hs : f a = some b) (h : EvalsToInTime f b (some c) n) :
    EvalsToInTime f a (some c) (n + 1) where
  steps := h.steps + 1
  evals_in_steps := by
    rw [Function.iterate_succ_apply]
    change (flip bind f)^[h.steps] (f a) = some c
    rw [hs]
    exact h.evals_in_steps
  steps_le_m := Nat.add_le_add_right h.steps_le_m 1

/-- Increase the clock of a bounded execution. -/
def mono {α : Type} {f : α → Option α} {a c : α} {m n : ℕ}
    (h : EvalsToInTime f a (some c) m) (hmn : m ≤ n) :
    EvalsToInTime f a (some c) n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hmn⟩

end StateTransition.EvalsToInTime

namespace Turing.MultiTapeTM.ToTM2

noncomputable section

variable {k : ℕ} {State : Type}

/-- Exactly the stacks other than the two output stacks are discarded. -/
@[simp] theorem mem_auxiliaries (s : Stack k) :
    s ∈ auxiliaries k ↔ s ≠ .output ∧ s ≠ .reversed := by
  cases s with
  | work i b => cases b <;> simp [auxiliaries]
  | _ => simp [auxiliaries]

/-- Each auxiliary is popped exactly once in a cleanup round. -/
theorem auxiliaries_nodup (k : ℕ) : (auxiliaries k).Nodup := by
  have hp : List.Pairwise (Function.onFun List.Disjoint
      (fun i : Fin k => [Stack.work i false, Stack.work i true])) (List.finRange k) := by
    apply (List.nodup_finRange k).imp
    intro i j hij
    simp [Function.onFun, List.disjoint_left, hij]
  simpa [auxiliaries, List.nodup_append, List.nodup_flatMap, List.disjoint_left] using hp

/-- Pop each named stack once; the list is assumed duplicate-free when used operationally. -/
private def poppedStore (ss : List (Stack k)) (store : ∀ s : Stack k, List (Alphabet s)) :
    ∀ s : Stack k, List (Alphabet s) :=
  fun s => if s ∈ ss then (store s).tail else store s

private theorem poppedStore_cons (s : Stack k) (ss : List (Stack k))
    (store : ∀ s : Stack k, List (Alphabet s)) (h : s ∉ ss) :
    poppedStore ss (Function.update store s (store s).tail) = poppedStore (s :: ss) store := by
  funext t
  by_cases ht : t = s
  · subst t
    simp [poppedStore, h]
  · simp [poppedStore, ht]

private theorem any_update (s : Stack k) (ss : List (Stack k))
    (store : ∀ s : Stack k, List (Alphabet s)) (h : s ∉ ss) :
    ss.any (fun t => ((Function.update store s (store s).tail) t).head?.isSome) =
      ss.any (fun t => (store t).head?.isSome) := by
  induction ss with
  | nil => rfl
  | cons t ss ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.any_cons, Function.update_of_ne (Ne.symm h.1), ih h.2]

/-- The straight-line discard statement records whether a stack was nonempty before popping. -/
private theorem stepAux_discard (ss : List (Stack k)) (hss : ss.Nodup)
    (next : Statement k State) (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux (ss.foldr discard next) v store =
      TM2.stepAux next
        { v with busy := v.busy || ss.any (fun s => (store s).head?.isSome) }
        (poppedStore ss store) := by
  induction ss generalizing v store with
  | nil =>
    have hs : poppedStore [] store = store := by funext s; simp [poppedStore]
    simp only [List.foldr_nil, List.any_nil, Bool.or_false, hs]
  | cons s ss ih =>
    rw [List.nodup_cons] at hss
    simp only [List.foldr_cons, discard, TM2.stepAux]
    rw [ih hss.2, poppedStore_cons s ss store hss.1, any_update s ss store hss.1]
    simp [Bool.or_assoc]

/-- Total auxiliary storage before a cleanup round. -/
def auxiliaryLength (store : ∀ s : Stack k, List (Alphabet s)) : ℕ :=
  ∑ s : Stack k, if s ∈ auxiliaries k then (store s).length else 0

/-- Total stack storage, counting both output stacks and all auxiliary stacks. -/
@[expose] def totalStackLength (cfg : TM2.Cfg (Alphabet (k := k)) Label (Control k State)) : ℕ :=
  ∑ s : Stack k, (cfg.stk s).length

/-- Every stack contributes exactly once to the storage accounting. -/
theorem totalStackLength_eq (cfg : TM2.Cfg (Alphabet (k := k)) Label (Control k State)) :
    totalStackLength cfg = auxiliaryLength cfg.stk +
      (cfg.stk .reversed).length + (cfg.stk .output).length := by
  classical
  calc
    _ = ∑ s : Stack k, ((if s ∈ auxiliaries k then (cfg.stk s).length else 0) +
        (if s = .reversed then (cfg.stk s).length else 0) +
        (if s = .output then (cfg.stk s).length else 0)) := by
      apply Finset.sum_congr rfl
      intro s hs
      cases s <;> simp
    _ = _ := by simp [auxiliaryLength, Finset.sum_add_distrib]

/-- Whether a cleanup round encounters a nonempty auxiliary stack. -/
private def auxiliaryBusy (store : ∀ s : Stack k, List (Alphabet s)) : Bool :=
  (auxiliaries k).any (fun s => (store s).head?.isSome)

/-- A round pops all auxiliaries, preserving both output stacks. -/
private theorem stepAux_clean (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux clean v store =
      ⟨some (if auxiliaryBusy store then .clean else .reverse),
        { v with busy := auxiliaryBusy store }, poppedStore (auxiliaries k) store⟩ := by
  simp only [clean, TM2.stepAux]
  rw [stepAux_discard _ (auxiliaries_nodup k)]
  simp only [Bool.false_or, TM2.stepAux]
  simp only [auxiliaryBusy]
  by_cases hb : (auxiliaries k).any (fun s => (store s).head?.isSome) = true
  · simp only [hb, Bool.cond_true, ↓reduceIte]
  · have hf := Bool.eq_false_iff.mpr hb
    simp only [hf, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]

/-- No auxiliary is busy precisely when all of them are empty. -/
private theorem auxiliaryBusy_eq_false_iff (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryBusy store = false ↔ ∀ s ∈ auxiliaries k, store s = [] := by
  simp [auxiliaryBusy, List.any_eq_false]

/-- Zero auxiliary storage is equivalent to emptiness of every auxiliary stack. -/
theorem auxiliaryLength_eq_zero_iff (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryLength store = 0 ↔ ∀ s ∈ auxiliaries k, store s = [] := by
  simp [auxiliaryLength, Finset.sum_eq_zero_iff]

/-- Popping auxiliary stacks cannot increase their total length. -/
private theorem auxiliaryLength_popped_le (store : ∀ s : Stack k, List (Alphabet s)) :
    auxiliaryLength (poppedStore (auxiliaries k) store) ≤ auxiliaryLength store := by
  apply Finset.sum_le_sum
  intro s hs
  by_cases h : s ∈ auxiliaries k
  · simp only [poppedStore, h, ↓reduceIte, List.length_tail]
    exact Nat.sub_le _ _
  · simp [h]

/-- A busy round strictly decreases auxiliary storage. -/
private theorem auxiliaryLength_popped_lt (store : ∀ s : Stack k, List (Alphabet s))
    (hb : auxiliaryBusy store = true) :
    auxiliaryLength (poppedStore (auxiliaries k) store) < auxiliaryLength store := by
  have hex : ∃ s, s ∈ auxiliaries k ∧ store s ≠ [] := by
    by_contra! h
    have := (auxiliaryBusy_eq_false_iff store).2 h
    simp [hb] at this
  obtain ⟨s, hs, hne⟩ := hex
  apply Finset.sum_lt_sum
  · intro t ht
    by_cases h : t ∈ auxiliaries k
    · simp only [poppedStore, h, ↓reduceIte, List.length_tail]
      exact Nat.sub_le _ _
    · simp [h]
  · refine ⟨s, Finset.mem_univ s, ?_⟩
    simp only [poppedStore, hs, ↓reduceIte, List.length_tail]
    have : 0 < (store s).length := List.length_pos_iff.mpr hne
    omega

/-- A quiet round leaves every stack unchanged. -/
private theorem poppedStore_eq_of_not_busy (store : ∀ s : Stack k, List (Alphabet s))
    (hb : auxiliaryBusy store = false) : poppedStore (auxiliaries k) store = store := by
  funext s
  by_cases h : s ∈ auxiliaries k
  · simp [poppedStore, h, (auxiliaryBusy_eq_false_iff store).mp hb s h]
  · simp [poppedStore, h]

variable [Fintype State] (q₀ : State)
    (transition : State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)

/-- Reversal transfers one symbol, or resets finite control and halts on the empty stack. -/
private theorem stepAux_reverse (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    TM2.stepAux (program q₀ transition .reverse) v store =
      match store .reversed with
      | [] => ⟨none, initialControl q₀, Function.update store .reversed []⟩
      | b :: bs => ⟨some .reverse, { v with symbol := some b },
          Function.update (Function.update store .reversed bs) .output (b :: store .output)⟩ := by
  cases h : store .reversed with
  | nil => simp [program, TM2.stepAux, h, Option.isSome, Option.getD]
  | cons b bs =>
    simp only [program, TM2.stepAux, h, List.head?_cons, List.tail_cons,
      Option.isSome, Bool.cond_true]
    rfl

/-- When the auxiliaries are empty, the last reversal step has the canonical halting shape. -/
private theorem stepAux_reverse_nil (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s))
    (ha : ∀ s ∈ auxiliaries k, store s = []) (hr : store .reversed = []) :
    TM2.stepAux (program q₀ transition .reverse) v store =
      haltList (machine q₀ transition) (store .output) := by
  rw [stepAux_reverse, hr]
  change TM2.Cfg.mk none (initialControl q₀) _ = TM2.Cfg.mk none (initialControl q₀) _
  congr 1
  funext s
  cases s with
  | input => simp [machine, ha .input (by simp)]
  | before => simp [machine, ha .before (by simp)]
  | output => rfl
  | reversed => simp [machine]
  | work i b => simp [machine, ha (.work i b) (by simp)]

/-- Reversal preserves already populated output, which becomes a suffix of the final word. -/
private def reverseEvals (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s))
    (ha : ∀ s ∈ auxiliaries k, store s = []) :
    StateTransition.EvalsToInTime (TM2.step (program q₀ transition))
      ⟨some .reverse, v, store⟩
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (store .reversed).reverse (store .output))))
      ((store .reversed).length + 1) := by
  cases hr : store .reversed with
  | nil =>
    have hs : (TM2.step (program q₀ transition)) ⟨some .reverse, v, store⟩ =
        some (haltList (machine q₀ transition) (store .output)) := by
      change some (TM2.stepAux (program q₀ transition .reverse) v store) = _
      exact congrArg some (stepAux_reverse_nil q₀ transition v store ha hr)
    change StateTransition.EvalsToInTime _ _
      (some (haltList (machine q₀ transition) (store .output))) 1
    exact .cons hs (.refl _ _)
  | cons b bs =>
    let store' := Function.update (Function.update store .reversed bs) .output (b :: store .output)
    have ha' : ∀ s ∈ auxiliaries k, store' s = [] := by
      intro s hs
      have hne := (mem_auxiliaries s).mp hs
      simpa only [store', Function.update_of_ne hne.1, Function.update_of_ne hne.2] using ha s hs
    have hs : (TM2.step (program q₀ transition)) ⟨some .reverse, v, store⟩ =
        some ⟨some .reverse, { v with symbol := some b }, store'⟩ := by
      change some (TM2.stepAux (program q₀ transition .reverse) v store) = _
      rw [stepAux_reverse, hr]
    have hrec := reverseEvals { v with symbol := some b } store' ha'
    have hrev : store' .reversed = bs := by simp [store']
    have hout : store' .output = b :: store .output := by
      dsimp only [store']
      exact Function.update_self _ _ _
    rw [hrev, hout] at hrec
    rw [List.reverse_cons]
    have hw : List.append (α := Bool) (bs.reverse ++ [b]) (store .output) =
        List.append (α := Bool) bs.reverse (b :: store .output) :=
      List.append_assoc (α := Bool) bs.reverse [b] (store .output)
    rw [hw]
    change StateTransition.EvalsToInTime _ _ _ (bs.length + 1 + 1)
    exact .cons hs hrec
termination_by (store .reversed).length
decreasing_by simp_wf; rw [hr]; exact Nat.lt_succ_self _

/-- Cleanup reaches the canonical halting configuration within a linear number of TM2 steps. -/
private def cleanEvals (v : Control k State) (store : ∀ s : Stack k, List (Alphabet s)) :
    StateTransition.EvalsToInTime (TM2.step (program q₀ transition))
      ⟨some .clean, v, store⟩
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (store .reversed).reverse (store .output))))
      (auxiliaryLength store + (store .reversed).length + 2) := by
  cases hb : auxiliaryBusy store with
  | false =>
    have ha := (auxiliaryBusy_eq_false_iff store).mp hb
    have hs : (TM2.step (program q₀ transition)) ⟨some .clean, v, store⟩ =
        some ⟨some .reverse, { v with busy := false }, store⟩ := by
      change some (TM2.stepAux clean v store) = _
      rw [stepAux_clean, hb, poppedStore_eq_of_not_busy store hb]
      rfl
    exact (StateTransition.EvalsToInTime.cons hs (reverseEvals q₀ transition _ store ha)).mono
      (by omega)
  | true =>
    let store' := poppedStore (auxiliaries k) store
    have hrev : store' .reversed = store .reversed := by simp [store', poppedStore]
    have hout : store' .output = store .output := by simp [store', poppedStore]
    have hs : (TM2.step (program q₀ transition)) ⟨some .clean, v, store⟩ =
        some ⟨some .clean, { v with busy := true }, store'⟩ := by
      change some (TM2.stepAux clean v store) = _
      rw [stepAux_clean, hb]
      rfl
    have hrec := cleanEvals { v with busy := true } store'
    rw [hrev, hout] at hrec
    have hlt := auxiliaryLength_popped_lt store hb
    exact (StateTransition.EvalsToInTime.cons hs hrec).mono (by dsimp only [store'] at *; omega)
termination_by auxiliaryLength store
decreasing_by exact auxiliaryLength_popped_lt store hb

/-- Configuration form of `cleanEvals`, allowing arbitrary finite control and stack contents. -/
def cleanupEvals (cfg : (machine q₀ transition).Cfg) (hl : cfg.l = some .clean) :
    StateTransition.EvalsToInTime (machine q₀ transition).step cfg
      (some (haltList (machine q₀ transition)
        (List.append (α := Bool) (cfg.stk .reversed).reverse (cfg.stk .output))))
      (auxiliaryLength cfg.stk + (cfg.stk .reversed).length + 2) := by
  cases cfg with | mk l v store =>
    cases hl
    exact cleanEvals q₀ transition v store

/-- Auxiliary storage depends only on auxiliary stacks. -/
private theorem auxiliaryLength_congr {store store' : ∀ s : Stack k, List (Alphabet s)}
    (h : ∀ s ∈ auxiliaries k, store' s = store s) :
    auxiliaryLength store' = auxiliaryLength store := by
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hm : s ∈ auxiliaries k
  · simp only [hm, ↓reduceIte, h s hm]
  · simp [hm]

omit [Fintype State] in
/-- Discarding a round cannot increase total storage. -/
private theorem totalStackLength_clean_le (v : Control k State)
    (store : ∀ s : Stack k, List (Alphabet s)) :
    totalStackLength (TM2.stepAux clean v store) ≤ totalStackLength ⟨some .clean, v, store⟩ := by
  rw [stepAux_clean, totalStackLength_eq, totalStackLength_eq]
  have hrev : poppedStore (auxiliaries k) store .reversed = store .reversed := by
    simp [poppedStore]
  have hout : poppedStore (auxiliaries k) store .output = store .output := by
    simp [poppedStore]
  dsimp only
  rw [hrev, hout]
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (auxiliaryLength_popped_le store) _) _

/-- Reversal transfers symbols between the two output stacks without increasing storage. -/
private theorem totalStackLength_reverse (v : Control k State)
    (store : ∀ s : Stack k, List (Alphabet s)) :
    totalStackLength (TM2.stepAux (program q₀ transition .reverse) v store) =
      totalStackLength ⟨some .reverse, v, store⟩ := by
  rw [stepAux_reverse]
  cases hr : store .reversed with
  | nil =>
    have hs : Function.update store .reversed [] = store := by
      rw [← hr]
      exact Function.update_eq_self _ _
    simp only [hs, totalStackLength]
  | cons b bs =>
    let store' := Function.update (Function.update store .reversed bs) .output (b :: store .output)
    have haux : auxiliaryLength store' = auxiliaryLength store := by
      apply auxiliaryLength_congr
      intro s hs
      have hne := (mem_auxiliaries s).mp hs
      simp only [store', Function.update_of_ne hne.1, Function.update_of_ne hne.2]
    have hrev : store' .reversed = bs := by simp [store']
    have hout : store' .output = b :: store .output := Function.update_self _ _ _
    change totalStackLength ⟨some .reverse, { v with symbol := some b }, store'⟩ = _
    rw [totalStackLength_eq, totalStackLength_eq]
    dsimp only
    rw [haux, hrev, hout, hr]
    change auxiliaryLength store + bs.length + ((store .output).length + 1) =
      auxiliaryLength store + (bs.length + 1) + (store .output).length
    omega

/-- A cleanup or halted configuration remains in these phases and cannot gain stack storage. -/
private theorem cleanup_step (cfg : TM2.Cfg (Alphabet (k := k)) Label (Control k State))
    (hl : cfg.l ≠ some .run) :
    (TM2.stepTotal (program q₀ transition) cfg).l ≠ some .run ∧
      totalStackLength (TM2.stepTotal (program q₀ transition) cfg) ≤ totalStackLength cfg := by
  cases cfg with | mk l v store =>
    cases l with
    | none => exact ⟨hl, le_rfl⟩
    | some l =>
      cases l with
      | run => exact False.elim (hl rfl)
      | clean =>
        constructor
        · change (TM2.stepAux clean v store).l ≠ some .run
          rw [stepAux_clean]
          by_cases hb : auxiliaryBusy store = true <;> simp [hb]
        · exact totalStackLength_clean_le v store
      | reverse =>
        constructor
        · change (TM2.stepAux (program q₀ transition .reverse) v store).l ≠ some .run
          rw [stepAux_reverse]
          cases store .reversed <;> simp
        · exact (totalStackLength_reverse q₀ transition v store).le

/-- Every cleanup and reversal step, even after halting, uses at most the initial total storage. -/
theorem cleanup_stack_bound (cfg : (machine q₀ transition).Cfg)
    (hl : cfg.l = some .clean) (i : ℕ) :
    totalStackLength ((TM2.stepTotal (machine q₀ transition).m)^[i] cfg) ≤
      totalStackLength cfg := by
  change TM2.Cfg (Alphabet (k := k)) Label (Control k State) at cfg
  change totalStackLength ((TM2.stepTotal (program q₀ transition))^[i] cfg) ≤ _
  have hinv (n : ℕ) :
      ((TM2.stepTotal (program q₀ transition))^[n] cfg).l ≠ some .run ∧
      totalStackLength ((TM2.stepTotal (program q₀ transition))^[n] cfg) ≤
        totalStackLength cfg := by
    induction n with
    | zero =>
      constructor
      · change cfg.l ≠ some .run
        rw [hl]
        intro h
        cases h
      · exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hs := cleanup_step q₀ transition _ ih.1
      exact ⟨hs.1, hs.2.trans ih.2⟩
  exact (hinv i).2

end

end Turing.MultiTapeTM.ToTM2
