/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Bounds

/-!
# Native query-loop termination

A decreasing natural rank at continuation boundaries gives a finite all-branches native time
bound. The rank and the time bound are ghost data used in the proof. Neither is encoded or
stored by the native machine.

## Main definitions

* `Turing.NondeterministicQueryMachine.Native.HaltsFrom`: all paths from a configuration halt
  within a common number of native steps.

## Main results

* `Turing.NondeterministicQueryMachine.Native.choose_haltsFrom`: a preserved word invariant and
  a decreasing rank on nonfinal passes imply an all-branches time bound.
-/

@[expose] public section

namespace Turing.NondeterministicQueryMachine.Native

variable {k : ℕ} {SI SF : Type} {SP : Bool → Type}
  (I : MultiTapeTM k Bool SI) (P : (b : Bool) → MultiTapeTM k Bool (SP b))
  (F : MultiTapeTM k Bool SF) (C : Fin k)

/-- All native paths from `c` of at least `t` steps end halted. -/
def HaltsFrom {input : List Bool} (c : Cfg k Bool (State SI SP SF) input) (t : ℕ) : Prop :=
  ∀ p : (machine I P F C).RunPath input, p.head = c → t ≤ p.length → p.last.Halted

/-- A tidy deterministic finalizer gives a common native halting bound from its start. -/
theorem finish_haltsFrom {input : List Bool} {ws : Fin k → List Bool} (out : List Bool)
    {t s : ℕ} (hF : MultiTapeTM.TransformsTapes F
      (fun inp w => inp = input ∧ w = ws) (fun _ _ _ _ => True) t s) :
    HaltsFrom I P F C (wordsCfg input (some (.finish F.q₀)) ws out) t := by
  obtain ⟨ws', e, _, q₀, hqhead, hqlast, htime, _⟩ := hF input ws out ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', hlen, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  intro p hhead hp
  have hmap : p.head = q.head.mapState finishState := by
    rw [hhead', hqhead, mapState_wordsCfg]
    exact hhead
  have hq : q.length < p.length + 1 := by
    change q₀.length ≤ t at htime
    omega
  have heq := follows_finish I P F C p q hmap q.length hq (Nat.lt_succ_self _)
  change p ⟨q.length, hq⟩ = q.last.mapState finishState at heq
  have hhalt : (p ⟨q.length, hq⟩).Halted := by
    rw [heq, hlast', hqlast]
    rfl
  exact (MultiTapeNTM.RunPath.last_eq_of_halted p _ hhalt) ▸ hhalt

/-- The native pass loop halts on every branch when continuation strictly decreases a natural
rank. The proof takes maxima of two branch bounds; the machine stores neither rank nor clock. -/
theorem choose_haltsFrom {input : List Bool} (Inv : (Fin k → List Bool) → Prop)
    (rank : (Fin k → List Bool) → ℕ)
    (hP : ∀ b ws, Inv ws → ∃ t s, MultiTapeTM.TransformsTapes (P b)
      (fun inp w => inp = input ∧ w = ws)
      (fun _ _ w' _ => Inv w' ∧ (w' C ≠ [] → rank w' < rank ws)) t s)
    (hF : ∀ ws, Inv ws → ∃ t s, MultiTapeTM.TransformsTapes F
      (fun inp w => inp = input ∧ w = ws) (fun _ _ _ _ => True) t s)
    {ws : Fin k → List Bool} (hInv : Inv ws) (out : List Bool) :
    ∃ t, HaltsFrom I P F C (wordsCfg input (some .choose) ws out) t := by
  have aux : ∀ n, ∀ ws, rank ws = n → Inv ws → ∀ out,
      ∃ t, HaltsFrom I P F C (wordsCfg input (some .choose) ws out) t := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro ws hr hInv out
      have branches : ∀ b, ∃ t, HaltsFrom I P F C
          (wordsCfg input (some (.pass b (P b).q₀)) ws out) t := by
        intro b
        obtain ⟨tP, sP, htP⟩ := hP b ws hInv
        obtain ⟨ws', e, hpost, q₀, hqhead, hqlast, _, _⟩ := htP input ws out ⟨rfl, rfl⟩
        obtain ⟨q, hhead', hlast', _, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
        obtain ⟨tNext, hNext⟩ : ∃ t, HaltsFrom I P F C
            (wordsCfg input (some (if ws' C = [] then .finish F.q₀ else .choose)) ws'
              (out ++ e)) t := by
          by_cases hblank : ws' C = []
          · obtain ⟨tF, sF, htF⟩ := hF ws' hpost.1
            exact ⟨tF, by simpa [hblank] using finish_haltsFrom I P F C (out ++ e) htF⟩
          · obtain ⟨t, ht⟩ := ih (rank ws') (by rw [← hr]; exact hpost.2 hblank)
              ws' rfl hpost.1 (out ++ e)
            exact ⟨t, by simpa [hblank] using ht⟩
        refine ⟨q.length + 1 + tNext, ?_⟩
        intro p hhead hp
        have hmap : p.head = q.head.mapState (passState b) := by
          rw [hhead', hqhead, mapState_wordsCfg]
          exact hhead
        have hq : q.length < p.length := by omega
        have hcfg : p ⟨q.length, by omega⟩ = wordsCfg input (some .check) ws' (out ++ e) := by
          have heq := follows_pass I P F C b p q hmap q.length (by omega) (Nat.lt_succ_self _)
          change p ⟨q.length, by omega⟩ = q.last.mapState (passState b) at heq
          simpa [hlast', hqlast, passState] using heq
        have hstep := p.step ⟨q.length, hq⟩
        change (machine I P F C).Step (p ⟨q.length, by omega⟩)
          (p ⟨q.length + 1, by omega⟩) at hstep
        rw [hcfg] at hstep
        obtain ⟨coin, hcoin⟩ := (step_iff I P F C).mp hstep
        rw [step_check_words I P F C coin] at hcoin
        have htail := hNext (p.drop ⟨q.length + 1, by omega⟩)
          (by simpa using hcoin.symm) (by simp only [RelSeries.drop_length]; omega)
        simpa using htail
      choose time htime using branches
      refine ⟨1 + max (time false) (time true), ?_⟩
      intro p hhead hp
      have hone : 1 < p.length + 1 := by omega
      have hstep := p.step ⟨0, by omega⟩
      change (machine I P F C).Step p.head (p ⟨1, hone⟩) at hstep
      rw [hhead] at hstep
      obtain ⟨b, hb⟩ := (step_iff I P F C).mp hstep
      rw [step_choose I P F C b _ rfl, withState_wordsCfg] at hb
      have hmax : time b ≤ max (time false) (time true) := by cases b <;> omega
      have ht := htime b (p.drop ⟨1, hone⟩) (by simpa using hb.symm)
        (by simp only [RelSeries.drop_length]; omega)
      simpa using ht
  exact aux (rank ws) ws rfl hInv out

/-- A tidy initializer followed by the ranked native loop has a per-input all-branches clock. -/
theorem exists_runsInTime_of_transforms {input : List Bool}
    (Inv : (Fin k → List Bool) → Prop) (rank : (Fin k → List Bool) → ℕ) {tI sI : ℕ}
    (hI : MultiTapeTM.TransformsTapes I
      (fun inp ws => inp = input ∧ ws = fun _ => []) (fun _ _ ws' _ => Inv ws') tI sI)
    (hP : ∀ b ws, Inv ws → ∃ t s, MultiTapeTM.TransformsTapes (P b)
      (fun inp w => inp = input ∧ w = ws)
      (fun _ _ w' _ => Inv w' ∧ (w' C ≠ [] → rank w' < rank ws)) t s)
    (hF : ∀ ws, Inv ws → ∃ t s, MultiTapeTM.TransformsTapes F
      (fun inp w => inp = input ∧ w = ws) (fun _ _ _ _ => True) t s) :
    ∃ t, (machine I P F C).RunsInTime input t := by
  obtain ⟨ws, e, hInv, q₀, hqhead, hqlast, _, _⟩ := hI input (fun _ => []) [] ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', _, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  obtain ⟨t, ht⟩ := choose_haltsFrom I P F C Inv rank hP hF hInv e
  refine ⟨q.length + t, ?_⟩
  intro p hp
  have hmap : p.head = q.head.mapState initState := by
    rw [p.head_eq, hhead', hqhead, mapState_wordsCfg]
    change Cfg.init (.init I.q₀ : State SI SP SF) input = _
    simp [initState, wordsCfg]
  have hq : q.length < p.length + 1 := by change q.length + t ≤ p.length at hp; omega
  have hcfg : p.toRunPath ⟨q.length, hq⟩ = wordsCfg input (some .choose) ws e := by
    have h := follows_init I P F C p.toRunPath q hmap q.length hq (Nat.lt_succ_self _)
    change p.toRunPath ⟨q.length, hq⟩ = q.last.mapState initState at h
    simpa [hlast', hqlast, initState] using h
  have h := ht (p.toRunPath.drop ⟨q.length, hq⟩) (by simpa using hcfg)
    (by change t ≤ p.length - q.length; change q.length + t ≤ p.length at hp; omega)
  simpa using h

end Turing.NondeterministicQueryMachine.Native
