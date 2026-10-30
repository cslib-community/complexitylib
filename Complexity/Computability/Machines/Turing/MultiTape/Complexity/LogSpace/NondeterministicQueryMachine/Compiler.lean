/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine.Routines

/-!
# Native finite-state compilation of nondeterministic query machines

Local linear-space callbacks compile to native binary-choice passes. The abstract state remains
on the work tapes; finite native control stores only callback control states and routing states.

## Main results

* `Turing.NondeterministicQueryMachine.exists_decidesInSpace`: the native compiler preserves
  existential acceptance, bounds every computation prefix, and halts on every branch.
-/

@[expose] public section

namespace Turing.NondeterministicQueryMachine

open MultiTapeTM

namespace Routines

variable {α σ : Type} {M : NondeterministicQueryMachine σ} {enc : α ↪ List Bool} {S : α → ℕ}
  (R : Routines M enc S)

/-- The compiled native nondeterministic machine. -/
noncomputable abbrev machine : MultiTapeNTM R.k Bool (Native.State R.SI R.SP R.SF) :=
  Native.machine R.I R.P R.F R.C

/-- The boundary invariant includes both possible continuation flags. Only the post-pass flag
is used to choose whether to continue. Initialization enters the first pass unconditionally. -/
def Inv (a : α) (ws : Fin R.k → List Bool) : Prop :=
  ∃ s flag, M.Reachable (enc a) s ∧ ws = R.boundary s flag

private theorem pass_inv (a : α) (b : Bool) (ws : Fin R.k → List Bool) (h : R.Inv a ws) :
    ∃ t, TransformsTapes (R.P b) (fun inp w => inp = enc a ∧ w = ws)
      (fun _ _ w' _ => R.Inv a w') t (R.c * S a) := by
  obtain ⟨s, flag, hs, rfl⟩ := h
  obtain ⟨t, ht⟩ := R.pass_spec a s hs b flag
  exact ⟨t, ht.imp (fun _ _ h => h)
    (fun _ _ _ _ _ ⟨hw, _⟩ => ⟨_, _, Reachable.step M (enc a) hs b, hw⟩) le_rfl le_rfl⟩

private theorem finish_spec (a : α) (ws : Fin R.k → List Bool) (h : R.Inv a ws) :
    ∃ t, TransformsTapes R.F (fun inp w => inp = enc a ∧ w = ws)
      (fun _ _ _ _ => True) t (R.c * S a) := by
  obtain ⟨s, flag, hs, rfl⟩ := h
  obtain ⟨t, ht⟩ := R.final_spec a s hs flag
  exact ⟨t, ht.imp (fun _ _ h => h) (fun _ _ _ _ _ _ => trivial) le_rfl le_rfl⟩

/-- All native prefixes remain in the shared workspace window. -/
theorem runsInSpace (a : α) : R.machine.RunsInSpace (enc a) (R.k * (2 * (R.c * S a) + 1)) := by
  obtain ⟨t, ht⟩ := R.initial_spec a
  exact Native.runsInSpace_of_transforms R.I R.P R.F R.C (R.Inv a)
    (ht.imp (fun _ _ h => h)
      (fun _ _ _ _ _ ⟨hw, _⟩ => ⟨_, _, M.reachable_init _, hw⟩) le_rfl le_rfl)
    (R.pass_inv a) (R.finish_spec a)

/-- Decode a boundary state for proof purposes only. It is never stored in finite control. -/
noncomputable def boundaryState (ws : Fin R.k → List Bool) : σ :=
  open scoped Classical in
  if h : ∃ s flag, ws = R.boundary s flag then h.choose else M.init

private theorem boundaryState_eq (s : σ) (flag : Bool) :
    R.boundaryState (R.boundary s flag) = s := by
  classical
  have h : ∃ s' flag', R.boundary s flag = R.boundary s' flag' := ⟨s, flag, rfl⟩
  rw [boundaryState, dite_eq_left h]
  obtain ⟨flag', heq⟩ := h.choose_spec
  exact R.boundary_injective _ _ _ _ heq.symm

/-- A common abstract clock yields an all-branches native clock, without an encoded clock. -/
theorem exists_runsInTime (a : α) {time : ℕ} (hhalt : M.HaltsWithin (enc a) time) :
    ∃ t, R.machine.RunsInTime (enc a) t := by
  obtain ⟨tI, hI⟩ := R.initial_spec a
  apply Native.exists_runsInTime_of_transforms R.I R.P R.F R.C (R.Inv a)
    (fun ws => M.remainingSteps (enc a) (R.boundaryState ws))
    (hI.imp (fun _ _ h => h)
      (fun _ _ _ _ _ ⟨hw, _⟩ => ⟨_, _, M.reachable_init _, hw⟩) le_rfl le_rfl)
  · intro b ws hws
    obtain ⟨s, flag, hs, rfl⟩ := hws
    obtain ⟨t, ht⟩ := R.pass_spec a s hs b flag
    refine ⟨t, R.c * S a, ht.imp (fun _ _ h => h) ?_ le_rfl le_rfl⟩
    rintro _ _ _ _ _ ⟨rfl, _⟩
    refine ⟨⟨_, _, Reachable.step M (enc a) hs b, rfl⟩, ?_⟩
    intro hflag
    rw [R.boundary_flag] at hflag
    have hnext : M.halted (M.step (enc a) s b) = false := by
      cases h : M.halted (M.step (enc a) s b) <;> simp_all [flagWord]
    have hsLive : M.halted s = false := by
      cases h : M.halted s
      · rfl
      · rw [M.step_of_halted _ h] at hnext
        simp [h] at hnext
    simp only [R.boundaryState_eq]
    exact M.remainingSteps_step_lt _ ⟨time, M.haltsFrom_of_reachable _ hhalt hs⟩ hsLive b
  · intro ws hws
    obtain ⟨t, ht⟩ := R.finish_spec a ws hws
    exact ⟨t, R.c * S a, ht⟩

private theorem finish_output (a : α) (s : σ) (hs : M.Reachable (enc a) s)
    (flag : Bool) (out : List Bool) (p : R.machine.RunPath (enc a))
    (hhead : p.head = wordsCfg (enc a) (some (.finish R.F.q₀)) (R.boundary s flag) out)
    (hhalt : p.last.Halted) : p.last.output = out ++ [M.accept s] := by
  obtain ⟨t, ht⟩ := R.final_spec a s hs flag
  obtain ⟨ws', e, he, q₀, hqhead, hqlast, _, _⟩ := ht _ _ out ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', _, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  have hmap : p.head = q.head.mapState Native.finishState := by
    rw [hhead', hqhead, mapState_wordsCfg]
    exact hhead
  by_cases hshort : p.length < q.length
  · have h := Native.follows_finish R.I R.P R.F R.C p q hmap p.length
      (Nat.lt_succ_self _) (by omega)
    change p.last = (q ⟨p.length, by omega⟩).mapState Native.finishState at h
    have hnot := (q.step ⟨p.length, hshort⟩).1
    have hstate : (q ⟨p.length, by omega⟩).state ≠ none := hnot
    have hstate' : (q ⟨p.length, by omega⟩).state = none := by
      have hh : ((q ⟨p.length, by omega⟩).mapState
          (Native.finishState (SI := R.SI) (SP := R.SP))).Halted := h ▸ hhalt
      change (Option.map Native.State.finish _ = none) at hh
      exact Option.map_eq_none_iff.mp hh
    exact (hstate hstate').elim
  · have hq : q.length < p.length + 1 := by omega
    have h := Native.follows_finish R.I R.P R.F R.C p q hmap q.length hq
      (Nat.lt_succ_self _)
    change p ⟨q.length, hq⟩ = q.last.mapState Native.finishState at h
    have heq : p ⟨q.length, hq⟩ = wordsCfg (enc a) none ws' (out ++ e) := by
      simpa [hlast', hqlast, Native.finishState] using h
    have hh : (p ⟨q.length, hq⟩).Halted := by rw [heq]; rfl
    rw [MultiTapeNTM.RunPath.last_eq_of_halted p _ hh, heq, he]
    rfl

/-- Reverse simulation of every halted native branch, including arbitrary native prefixes
within routines. Passes do not emit; the final bit belongs to a reachable halted abstract state. -/
theorem choose_output (a : α) (p : R.machine.RunPath (enc a)) (s : σ)
    (hs : M.Reachable (enc a) s) (flag : Bool) (out : List Bool)
    (hhead : p.head = wordsCfg (enc a) (some .choose) (R.boundary s flag) out)
    (hhalt : p.last.Halted) :
    ∃ s', M.Reachable (enc a) s' ∧ M.halted s' = true ∧
      p.last.output = out ++ [M.accept s'] := by
  have aux : ∀ n, ∀ p : R.machine.RunPath (enc a), p.length = n → ∀ s,
      M.Reachable (enc a) s → ∀ flag out,
      p.head = wordsCfg (enc a) (some .choose) (R.boundary s flag) out → p.last.Halted →
      ∃ s', M.Reachable (enc a) s' ∧ M.halted s' = true ∧
        p.last.output = out ++ [M.accept s'] := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro p hn s hs flag out hhead hhalt
      have hpos : 0 < p.length := by
        by_contra hz
        have heq : p.last = p.head := by
          have hz' : p.length = 0 := by omega
          exact congrArg p (Fin.ext (by simpa using hz'))
        have hh : (wordsCfg (enc a) (some (.choose : Native.State R.SI R.SP R.SF))
            (R.boundary s flag) out).Halted := (heq.trans hhead) ▸ hhalt
        change some _ = none at hh
        cases hh
      have hone : 1 < p.length + 1 := by omega
      have hfirst := p.step ⟨0, by omega⟩
      change R.machine.Step p.head (p ⟨1, hone⟩) at hfirst
      rw [hhead] at hfirst
      obtain ⟨b, hb⟩ := (Native.step_iff R.I R.P R.F R.C).mp hfirst
      rw [Native.step_choose R.I R.P R.F R.C b _ rfl, withState_wordsCfg] at hb
      let p₁ := p.drop ⟨1, hone⟩
      obtain ⟨t, ht⟩ := R.pass_spec a s hs b flag
      obtain ⟨ws', e, ⟨hws, he⟩, q₀, hqhead, hqlast, _, _⟩ := ht _ _ out ⟨rfl, rfl⟩
      obtain ⟨q, hhead', hlast', _, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
      have hmap : p₁.head = q.head.mapState (Native.passState b) := by
        rw [hhead', hqhead, mapState_wordsCfg]
        exact hb.symm
      have hlong : q.length + 1 < p.length := by
        by_contra hshort
        have hq : p₁.length < q.length + 1 := by simp only [p₁, RelSeries.drop_length]; omega
        have h := Native.follows_pass R.I R.P R.F R.C b p₁ q hmap p₁.length
          (Nat.lt_succ_self _) hq
        change p₁.last = (q ⟨p₁.length, hq⟩).mapState (Native.passState b) at h
        have hh : p₁.last.Halted := by simpa [p₁] using hhalt
        rw [h] at hh
        change some _ = none at hh
        cases hh
      have hcfg : p ⟨q.length + 1, by omega⟩ =
          wordsCfg (enc a) (some .check) ws' (out ++ e) := by
        have h := Native.follows_pass R.I R.P R.F R.C b p₁ q hmap q.length
          (by simp only [p₁, RelSeries.drop_length]; omega) (Nat.lt_succ_self _)
        change p ⟨q.length + 1, by omega⟩ = q.last.mapState (Native.passState b) at h
        simpa [hlast', hqlast, Native.passState] using h
      have hnext := p.step ⟨q.length + 1, hlong⟩
      change R.machine.Step (p ⟨q.length + 1, by omega⟩)
        (p ⟨q.length + 2, by omega⟩) at hnext
      rw [hcfg] at hnext
      obtain ⟨coin, hcoin⟩ := (Native.step_iff R.I R.P R.F R.C).mp hnext
      rw [Native.step_check_words R.I R.P R.F R.C coin, hws, he, List.append_nil] at hcoin
      let cut : Fin (p.length + 1) := ⟨q.length + 2, by omega⟩
      have hreach := Reachable.step M (enc a) hs b
      by_cases hblank : R.boundary (M.step (enc a) s b) (!M.halted (M.step (enc a) s b)) R.C = []
      · have hhalt' : M.halted (M.step (enc a) s b) = true := by
          rw [R.boundary_flag] at hblank
          cases hh : M.halted (M.step (enc a) s b) <;> simp_all [flagWord]
        refine ⟨_, hreach, hhalt', ?_⟩
        simpa only [RelSeries.last_drop] using R.finish_output a _ hreach _ out (p.drop cut)
          (by simpa [cut, hblank] using hcoin.symm) (by simpa using hhalt)
      · simpa only [RelSeries.last_drop] using ih (p.drop cut).length
          (by simp only [RelSeries.drop_length, cut]; omega) (p.drop cut) rfl _ hreach _ out
          (by simpa [cut, hblank] using hcoin.symm) (by simpa using hhalt)
  exact aux p.length p rfl s hs flag out hhead hhalt

private theorem exists_finish_path (a : α) (s : σ) (hs : M.Reachable (enc a) s)
    (flag : Bool) (out : List Bool) :
    ∃ p : R.machine.RunPath (enc a),
      p.head = wordsCfg (enc a) (some (.finish R.F.q₀)) (R.boundary s flag) out ∧
      p.last.Halted ∧ p.last.output = out ++ [M.accept s] := by
  obtain ⟨t, ht⟩ := R.final_spec a s hs flag
  obtain ⟨ws', e, he, q₀, hqhead, hqlast, _, _⟩ := ht _ _ out ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', _, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  let p := q.map (Native.finishHom R.I R.P R.F R.C)
  have hlast : p.last = wordsCfg (enc a) none ws' (out ++ [M.accept s]) := by
    simp [p, hlast', hqlast, Native.finishState, he]
  refine ⟨p, ?_, by rw [hlast]; rfl, by rw [hlast]; rfl⟩
  simp [p, hhead', hqhead, Native.finishState]

private theorem exists_pass_path (a : α) (s : σ) (hs : M.Reachable (enc a) s)
    (b flag : Bool) (out : List Bool) :
    ∃ p : R.machine.RunPath (enc a),
      p.head = wordsCfg (enc a) (some .choose) (R.boundary s flag) out ∧
      p.last = wordsCfg (enc a)
        (some (if M.halted (M.step (enc a) s b) then .finish R.F.q₀ else .choose))
        (R.boundary (M.step (enc a) s b) (!M.halted (M.step (enc a) s b))) out := by
  obtain ⟨t, ht⟩ := R.pass_spec a s hs b flag
  obtain ⟨ws', e, ⟨hws, he⟩, p, hhead, hlast, _, _⟩ :=
    Native.exists_round R.I R.P R.F R.C b ht out ⟨rfl, rfl⟩
  refine ⟨p, hhead, ?_⟩
  rw [hws, he, List.append_nil, R.boundary_flag] at hlast
  cases hh : M.halted (M.step (enc a) s b) <;> simpa [hh, flagWord] using hlast

private theorem halted_realizes (a : α) (s : σ) (hs : M.Reachable (enc a) s)
    (hh : M.halted s = true) (flag : Bool) (out : List Bool) :
    ∃ p : R.machine.RunPath (enc a),
      p.head = wordsCfg (enc a) (some .choose) (R.boundary s flag) out ∧
      p.last.Halted ∧ p.last.output = out ++ [M.accept s] := by
  obtain ⟨p, hphead, hplast⟩ := R.exists_pass_path a s hs false flag out
  rw [M.step_of_halted _ hh] at hplast
  simp only [hh, Bool.not_true, ↓reduceIte] at hplast
  obtain ⟨q, hqhead, hqhalt, hqout⟩ := R.exists_finish_path a s hs false out
  exact ⟨p.smash q (hplast.trans hqhead.symm), by simpa using hphead,
    by simpa using hqhalt, by simpa using hqout⟩

/-- Every finite abstract branch ending halted is realized by a native branch. The initially
halted case uses one harmless self-loop pass, matching the unconditional native first pass. -/
theorem choose_realizes (a : α) (choices : List Bool) (s : σ)
    (hs : M.Reachable (enc a) s) (hh : M.halted (M.replay (enc a) choices s) = true)
    (flag : Bool) (out : List Bool) :
    ∃ p : R.machine.RunPath (enc a),
      p.head = wordsCfg (enc a) (some .choose) (R.boundary s flag) out ∧
      p.last.Halted ∧ p.last.output = out ++ [M.accept (M.replay (enc a) choices s)] := by
  induction choices generalizing s flag out with
  | nil => exact R.halted_realizes a s hs hh flag out
  | cons b choices ih =>
    have hs' := Reachable.step M (enc a) hs b
    obtain ⟨p, hphead, hplast⟩ := R.exists_pass_path a s hs b flag out
    by_cases hnext : M.halted (M.step (enc a) s b) = true
    · obtain ⟨q, hqhead, hqhalt, hqout⟩ := R.exists_finish_path a _ hs' false out
      have hconnect : p.last = q.head := by rw [hplast, hqhead]; simp [hnext]
      refine ⟨p.smash q hconnect, by simpa using hphead,
        by simpa using hqhalt, ?_⟩
      simpa only [RelSeries.last_smash, replay_cons, M.replay_of_halted _ hnext] using hqout
    · have hn : M.halted (M.step (enc a) s b) = false := Bool.eq_false_iff.mpr hnext
      obtain ⟨q, hqhead, hqhalt, hqout⟩ := ih _ hs' hh true out
      have hconnect : p.last = q.head := by rw [hplast, hqhead]; simp [hn]
      exact ⟨p.smash q hconnect, by simpa using hphead,
        by simpa using hqhalt, by simpa only [RelSeries.last_smash, replay_cons] using hqout⟩

/-- Native acceptance is exactly existential halted acceptance of the query machine. -/
theorem accepts_iff (a : α) : R.machine.Accepts (enc a) ↔ M.Accepts (enc a) := by
  obtain ⟨tI, hI⟩ := R.initial_spec a
  obtain ⟨ws, e, ⟨hws, he⟩, q₀, hqhead, hqlast, _, _⟩ :=
    hI _ _ [] ⟨rfl, rfl⟩
  obtain ⟨q, hhead', hlast', _, _⟩ := q₀.exists_running (by rw [hqlast]; rfl)
  constructor
  · rintro ⟨p, hhalt, hout⟩
    have hmap : p.head = q.head.mapState Native.initState := by
      rw [p.head_eq, hhead', hqhead, mapState_wordsCfg]
      change Cfg.init (.init R.I.q₀ : Native.State R.SI R.SP R.SF) (enc a) = _
      simp [Native.initState, wordsCfg]
    have hlong : q.length < p.length + 1 := by
      by_contra hshort
      have h := Native.follows_init R.I R.P R.F R.C p.toRunPath q hmap p.length
        (Nat.lt_succ_self _) (by omega)
      change p.last = (q ⟨p.length, by omega⟩).mapState Native.initState at h
      have hh := h ▸ hhalt
      change some _ = none at hh
      cases hh
    have hcfg : p.toRunPath ⟨q.length, hlong⟩ =
        wordsCfg (enc a) (some .choose) (R.boundary M.init false) [] := by
      have h := Native.follows_init R.I R.P R.F R.C p.toRunPath q hmap q.length hlong
        (Nat.lt_succ_self _)
      change p.toRunPath ⟨q.length, hlong⟩ = q.last.mapState Native.initState at h
      simpa [hlast', hqlast, Native.initState, hws, he] using h
    obtain ⟨s, ⟨choices, hchoices⟩, hhalt', hout'⟩ :=
      R.choose_output a (p.toRunPath.drop ⟨q.length, hlong⟩) M.init
        (M.reachable_init _) false [] (by simpa using hcfg) (by simpa using hhalt)
    refine ⟨choices, hchoices ▸ hhalt', ?_⟩
    have hbit : [M.accept s] = [true] := by simpa [hout] using hout'.symm
    rw [hchoices]
    exact List.head_eq_of_cons_eq hbit
  · rintro ⟨choices, hhalt, haccept⟩
    let p := q.map (Native.initHom R.I R.P R.F R.C)
    have hphead : p.head = R.machine.initCfg (enc a) := by
      change (q.map (Native.initHom R.I R.P R.F R.C)).head =
        Cfg.init (.init R.I.q₀ : Native.State R.SI R.SP R.SF) (enc a)
      rw [RelSeries.head_map]
      simp [hhead', hqhead, Native.initState, wordsCfg, Cfg.mapState]
    have hplast : p.last =
        wordsCfg (enc a) (some .choose) (R.boundary M.init false) [] := by
      simp [p, hlast', hqlast, Native.initState, hws, he]
    obtain ⟨p', hp'head, hp'halt, hp'out⟩ :=
      R.choose_realizes a choices M.init (M.reachable_init _) hhalt false []
    change M.accept (M.replay (enc a) choices M.init) = true at haccept
    let p'' := p.smash p' (hplast.trans hp'head.symm)
    exact ⟨⟨p'', by simpa [p''] using hphead⟩,
      by simpa [p''] using hp'halt, by simpa [p'', haccept] using hp'out⟩

end Routines

/-- **Native finite-state compilation.** Linear-space local callbacks and a uniform bound on
all encoded abstract prefixes yield a native nondeterministic decider in `O(S)` visited-cell
space. The abstract clock is used only to prove all-branches halting. Neither an abstract state,
a clock, nor a choice history is stored in native finite control. -/
theorem exists_decidesInSpace {α σ : Type} {enc : α ↪ List Bool} {encS : σ ↪ List Bool}
    (M : NondeterministicQueryMachine σ)
    (hquery : ComputableTidilyInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableTidilyInSpace M.next
      (encPair encS (encPair (encOption encBool) encBool)) encS
      fun p => (encPair encS (encPair (encOption encBool) encBool) p).length)
    (hhalted : ComputableTidilyInSpace M.halted encS encBool fun s => (encS s).length)
    (haccept : ComputableTidilyInSpace M.accept encS encBool fun s => (encS s).length)
    (time : α → ℕ) (hhalt : ∀ a, M.HaltsWithin (enc a) (time a))
    {A : Set α} (hcorrect : ∀ a, a ∈ A ↔ M.Accepts (enc a))
    (S : α → ℕ) (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hsize : ∃ c, ∀ a choices, (encS (M.run (enc a) choices)).length ≤ c * S a) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      ntm.DecidesInSpace enc A (fun a => c * S a) := by
  obtain ⟨R⟩ := M.exists_routines hquery hnext hhalted haccept S hlog hsize
  let : Finite R.SI := R.finiteI
  let : ∀ b, Finite (R.SP b) := R.finiteP
  let : Finite R.SF := R.finiteF
  refine ⟨R.k, Native.State R.SI R.SP R.SF, inferInstance, R.machine,
    R.k * (2 * R.c + 1), ⟨fun a => ?_, fun a => R.exists_runsInTime a (hhalt a)⟩⟩
  refine ⟨(R.runsInSpace a).mono ?_, (hcorrect a).trans (R.accepts_iff a).symm⟩
  have hS : 1 ≤ S a := (Nat.le_add_left _ _).trans (hlog a)
  calc
    R.k * (2 * (R.c * S a) + 1) ≤ R.k * ((2 * R.c + 1) * S a) :=
      Nat.mul_le_mul_left _ (by nlinarith only [hS])
    _ = R.k * (2 * R.c + 1) * S a := by ring

end Turing.NondeterministicQueryMachine
