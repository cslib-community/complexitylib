/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- `exists_runPath_seq_space_le` is from cslib PR #1111 @3441fa81.
-- vendored: `space_seq_le` is stated with the space of run paths since cslib #1122

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Space of a sequential run

The additions of Christian Reitwiessner's branch `crei/tidy-universal` and of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential`: sequential runs read through
`Turing.MultiTapeTM.runFrom`, with their space, and sequential composition of transformations given
by equations.

## Main results

* `Turing.MultiTapeTM.runFrom_seq`: runs compose.
* `Turing.MultiTapeTM.withState_runFrom_seq`: invariants of a sequential run.
* `Turing.MultiTapeTM.space_seq_le`: the space of a sequential run is at most that of its phases.
* `Turing.MultiTapeTM.TransformsTapes.seq_eq`: sequential composition of transformations given by
  equations.
* `Turing.MultiTapeTM.exists_runPath_seq_space_le`: the composed path visits at most the cells of
  the two paths combined.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

variable {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

/-- **Space of a sequential run.** The run path of `seq` composed from two run paths visits at most
the cells of the two paths combined. -/
theorem exists_runPath_seq_space_le {p₀ : tm₀.RunPath input} (h₀ : p₀.last.Halted)
    {p₁ : tm₁.RunPath input} (h₁ : p₁.head = p₀.last.withState (some tm₁.q₀)) :
    ∃ p : (tm₀.seq tm₁).RunPath input,
      p.head = p₀.head.mapState (handOver tm₁.q₀) ∧
      p.last = p₁.last.mapState (Option.map .inr) ∧
      p.length ≤ p₀.length + p₁.length ∧ p.space ≤ p₀.space + p₁.space := by
  obtain ⟨p, hh, hl, ht, hvisited⟩ := exists_runPath_seq h₀ h₁
  refine ⟨p, hh, hl, ht, ?_⟩
  exact (Finset.sum_le_sum fun i _ => (Finset.card_le_card (hvisited i)).trans
    (Finset.card_union_le _ _)).trans_eq Finset.sum_add_distrib

namespace Sequential

/-- The second phase commutes with the existing configuration-state map. -/
lemma step_mapState_inr (cfg : Cfg k Symbol State₁ input) :
    (tm₀.seq tm₁).step (cfg.mapState (Option.map .inr)) =
      (tm₁.step cfg).mapState (Option.map .inr) := by
  let H : (tm₁.stepRel input).Hom ((tm₀.seq tm₁).stepRel input) := combineRightHom
  exact step_iff.mp (H.map_rel (step_iff.mpr rfl))

/-- The running first phase commutes with the existing handover map. -/
lemma step_mapState_handOver (cfg : Cfg k Symbol State₀ input) (h : cfg.state ≠ none) :
    (tm₀.seq tm₁).step (cfg.mapState (handOver tm₁.q₀)) =
      (tm₀.step cfg).mapState (handOver tm₁.q₀) := by
  let H : (tm₀.runningStepRel input).Hom ((tm₀.seq tm₁).stepRel input) :=
    combineLeftHom (handOver_some _)
  exact step_iff.mp (H.map_rel ⟨h, step_iff.mpr rfl⟩)

/-- A halted first-phase configuration is the initial second-phase configuration. -/
lemma mapState_handOver_of_halt {q₁ : State₁} {cfg : Cfg k Symbol State₀ input}
    (h : cfg.state = none) :
    cfg.mapState (handOver q₁) =
      (cfg.withState (some q₁)).mapState (Option.map .inr) := by
  simp [Cfg.mapState, Cfg.withState, h]

/-- The second phase of `seq` mirrors the run of `tm₁`. -/
lemma runFrom_mapState_inr (cfg : Cfg k Symbol State₁ input) (n : ℕ) :
    (tm₀.seq tm₁).runFrom (cfg.mapState (Option.map .inr)) n =
      (tm₁.runFrom cfg n).mapState (Option.map .inr) :=
  (Function.Semiconj.iterate_right (fun c => (step_mapState_inr c).symm) n cfg).symm

/-- While `tm₀` is running, `seq` mirrors it. -/
lemma runFrom_mapState_handOver (cfg : Cfg k Symbol State₀ input) (n : ℕ)
    (h : ∀ m < n, (tm₀.runFrom cfg m).state ≠ none) :
    (tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) n =
      (tm₀.runFrom cfg n).mapState (handOver tm₁.q₀) := by
  simp only [runFrom] at h ⊢
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih fun m hm => h m (by omega),
      step_mapState_handOver _ (h n (by omega))]

end Sequential

open Sequential in
/-- If `tm₀` halts at step `u`, then from step `u` on `seq` mirrors `tm₁`, started where `tm₀`
halted. -/
lemma HaltsAt.runFrom_seq {cfg : Cfg k Symbol State₀ input} {u : ℕ} (h : tm₀.HaltsAt cfg u)
    (n : ℕ) :
    (tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) (u + n) =
      (tm₁.runFrom ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) n).mapState (Option.map .inr) := by
  have hhandoff : (tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) u =
      ((tm₀.runFrom cfg u).withState (some tm₁.q₀)).mapState (Option.map .inr) := by
    rw [runFrom_mapState_handOver cfg u fun _ hm => h.not_halted hm, mapState_handOver_of_halt
      h.halted]
  simp only [runFrom] at hhandoff ⊢
  rw [Nat.add_comm, Function.iterate_add_apply, hhandoff]
  exact runFrom_mapState_inr _ n

open Sequential in
/-- **Sequential composition of runs.** If `tm₀` has halted in `mid` by step `t₀`, and `tm₁`,
started where `tm₀` halted, has halted in `fin` by step `t₁`, then the composed machine has halted
in `fin` by step `t₀ + t₁`. Each machine may halt earlier than its bound; in particular `tm₀` need
not be running at every step before `t₀`. -/
theorem runFrom_seq {cfg mid : Cfg k Symbol State₀ input} {fin : Cfg k Symbol State₁ input}
    {t₀ t₁ : ℕ} (h₀ : tm₀.runFrom cfg t₀ = mid) (hmid : mid.Halted)
    (h₁ : tm₁.runFrom (mid.withState (some tm₁.q₀)) t₁ = fin) (hfin : fin.Halted) :
    (tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) (t₀ + t₁) =
      fin.mapState (Option.map .inr) := by
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  have hrun : (tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) (u + t₁) =
      fin.mapState (Option.map .inr) := by
    rw [hhaltsAt.runFrom_seq, ← hhaltsAt.runFrom_eq hu, h₀, h₁]
  have hhalt : ((tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) (u + t₁)).Halted := by
    simp only [hrun, Cfg.Halted] at hfin ⊢
    simp [Cfg.mapState, hfin]
  rw [runFrom_eq_of_halt _ _ (by omega) hhalt, hrun]

open Sequential in
/-- **Invariants of a sequential run.** If `tm₀` has halted in `mid` by step `t₀`, a property
of the configuration apart from its control state holds throughout the composed run when it
holds before `t₀` in the first run and at every step of `tm₁` started where `tm₀` halted.
Replacing the state by `some ()` retains the input head, work tapes, work-tape heads and output,
and hides both the control-state value and whether that phase has halted. -/
theorem withState_runFrom_seq {P : Cfg k Symbol Unit input → Prop}
    {cfg mid : Cfg k Symbol State₀ input} {t₀ : ℕ} (h₀ : tm₀.runFrom cfg t₀ = mid)
    (hmid : mid.Halted) (hP₀ : ∀ m < t₀, P ((tm₀.runFrom cfg m).withState (some ())))
    (hP₁ : ∀ n, P ((tm₁.runFrom (mid.withState (some tm₁.q₀)) n).withState (some ())))
    (m : ℕ) :
    P (((tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) m).withState (some ())) := by
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  rcases Nat.lt_or_ge m u with hm | hm
  · rw [runFrom_mapState_handOver cfg m fun _ hr => hhaltsAt.not_halted (by lia)]
    change P ((tm₀.runFrom cfg m).withState (some ()))
    exact hP₀ m (by lia)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [hhaltsAt.runFrom_seq, ← hhaltsAt.runFrom_eq hu, h₀]
    change P ((tm₁.runFrom (mid.withState (some tm₁.q₀)) n).withState (some ()))
    exact hP₁ n

open Sequential in
/-- If `tm₀` has halted in `mid` after `t₀` steps and `tm₁`, started from `mid`, has halted after
`t₁` steps, then in `t₀ + t₁` steps `tm₀.seq tm₁` uses at most the space of the two runs combined.
-/
theorem space_seq_le {cfg mid : Cfg k Symbol State₀ input} {t₀ t₁ : ℕ}
    (h₀ : tm₀.runFrom cfg t₀ = mid) (hmid : mid.Halted)
    (h₁ : (tm₁.runFrom (mid.withState (some tm₁.q₀)) t₁).Halted) :
    (MultiTapeNTM.RunPath.ofDeterministic (tm₀.seq tm₁)
      (cfg.mapState (handOver tm₁.q₀)) (t₀ + t₁)).space ≤
      (MultiTapeNTM.RunPath.ofDeterministic tm₀ cfg t₀).space +
        (MultiTapeNTM.RunPath.ofDeterministic tm₁ (mid.withState (some tm₁.q₀)) t₁).space := by
  -- the first halting time of `tm₀`, which may be earlier than `t₀`
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  -- from step `u` on, `seq` mirrors `tm₁`, started on what `tm₀` left
  have hright (n : ℕ) : (tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) (u + n) =
      (tm₁.runFrom (mid.withState (some tm₁.q₀)) n).mapState (Option.map .inr) := by
    rw [hhaltsAt.runFrom_seq, ← hhaltsAt.runFrom_eq hu, h₀]
  have hhalt : ((tm₀.seq tm₁).runFrom (cfg.mapState (handOver tm₁.q₀)) (u + t₁)).Halted := by
    rw [hright]
    exact congrArg (Option.map Sum.inr) h₁
  rw [space_eq_of_halt _ (by omega : u + t₁ ≤ t₀ + t₁) hhalt]
  refine le_trans (space_add_le _ _ _) (Nat.add_le_add ?_ ?_)
  · -- the first phase visits what the first machine visits
    refine le_trans (le_of_eq (space_eq_of_workTapePos _ _ u fun m hm => ?_))
      (space_mono tm₀ _ hu)
    rw [runFrom_mapState_handOver _ m fun _ hr => hhaltsAt.not_halted (by omega)]
    rfl
  · -- the second phase visits what the second machine visits
    rw [← add_zero u, hright 0]
    refine le_of_eq (space_eq_of_workTapePos _ _ t₁ fun m hm => ?_)
    rw [runFrom_mapState_inr]
    rfl

/-- **Sequential composition of transformations given by equations.** If the first machine leaves
the words `ws₁` and emits `e₀`, and the second takes `ws₁` to `ws₂` emitting `e₁`, the composed
machine leaves `ws₂` and emits `e₀ ++ e₁`. -/
theorem TransformsTapes.seq_eq {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {ws₁ ws₂ : Fin k → List Symbol} {e₀ e₁ : List Symbol} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTapes tm₀ P (fun _ _ ws' e => ws' = ws₁ ∧ e = e₀) t₀ s₀)
    (h₁ : TransformsTapes tm₁ (fun _ ws => ws = ws₁) (fun _ _ ws' e => ws' = ws₂ ∧ e = e₁) t₁ s₁) :
    TransformsTapes (tm₀.seq tm₁) P (fun _ _ ws' e => ws' = ws₂ ∧ e = e₀ ++ e₁)
      (t₀ + t₁) (s₀ + s₁) :=
  (transformsTapes_seq h₀ h₁ fun _ _ _ _ _ h => h.1).imp (fun _ _ h => h)
    (by rintro _ _ _ _ _ ⟨_, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩) le_rfl le_rfl

end Turing.MultiTapeTM
