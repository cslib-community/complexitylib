/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Nondeterministic

/-!
# Deciding problems with nondeterministic machines

A nondeterministic machine accepts an input when some computation path ends halted with output
`[true]`, the encoding `Turing.MultiTapeTM.encBool true` used by verifiers and deterministic
deciders. Paths that halt with another output, and paths ending in a stuck configuration, do not
accept. A machine decides `A` in time `t` [Arora and Barak, Definition 2.5][AroraBarak09] when
on every encoded instance `enc a`, every computation path of at least `t a` steps ends halted, and
`a ∈ A` exactly when some computation path on `enc a` accepts. The time bound applies to every
branch, including rejecting ones.

A transition relation may be empty at a running configuration. Upstream's
`Turing.MultiTapeNTM.RunsInTime` therefore permits a computation path that ends stuck before the
time bound; such a path neither halts nor accepts. When no configuration is stuck, every
computation path within the bound extends to a halted one of exactly the bound
(`Turing.MultiTapeNTM.ComputationPath.exists_halted_extension`).

A machine *recognizes* `A` within space `s` (`Turing.MultiTapeNTM.RecognizesInSpace`) when on
every encoded instance every computation prefix visits at most `s a` work-tape cells (upstream
`Turing.MultiTapeNTM.RunsInSpace`), and `a ∈ A` exactly when some computation path accepts. No
time bound is imposed: a branch may run forever or end stuck, and neither accepts. It *decides*
`A` within space `s` (`Turing.MultiTapeNTM.DecidesInSpace`) when moreover every branch halts
[Sipser, Definition 8.1][Sipser2013]: on every encoded instance some number of steps `t` bounds
every computation path (upstream `Turing.MultiTapeNTM.RunsInTime`). A path may still end stuck
before `t` steps; it does not accept, as a branch of a textbook machine that has no move rejects.
The bound `t` may depend arbitrarily on the instance. For machines with finitely many states, as
in `NL` and `NPSPACE`, there are finitely many actions, so the machine branches finitely and by
König's lemma this is equivalent to every branch halting; with infinitely many states it can
be strictly stronger. The terminology follows Sipser's for deterministic machines,
which *recognize* a language when they may loop and *decide* it when they halt on every input.

`Turing.MultiTapeNTM.DecidableInPolyTime` asks for one machine with a binary alphabet and finitely
many states, and one polynomially bounded time bound, for all instances. Like
`Turing.MultiTapeTM.ComputableTidilyInPolyTime`, it is relative to the encoding of instances.

## Main definitions

* `Turing.MultiTapeNTM.Accepts`: some computation path halts with output `[true]`.
* `Turing.MultiTapeNTM.DecidesInTime`: a machine decides a problem within a time bound.
* `Turing.MultiTapeNTM.RecognizesInSpace`: a machine recognizes a problem within a space bound,
  with no halting requirement.
* `Turing.MultiTapeNTM.DecidesInSpace`: a machine decides a problem within a space bound, every
  branch halting.
* `Turing.MultiTapeNTM.DecidableInTime`, `Turing.MultiTapeNTM.DecidableInPolyTime`: some finite
  binary machine decides a problem within a time bound, or within a polynomial time bound.

## Main results

* `Turing.MultiTapeNTM.RunPath.exists_extend_of_halted`: a halted path extends to any length.
* `Turing.MultiTapeNTM.RunsInTime.exists_time_eq`: under a time bound, a halted computation path
  has the last configuration of one of exactly the bound.
* `Turing.MultiTapeNTM.accepts_iff_exists_time_eq`: under a time bound `t`, acceptance is
  witnessed by a computation path of exactly `t` steps.
* `Turing.MultiTapeNTM.ComputationPath.exists_halted_extension`: without stuck configurations,
  every computation path within a time bound is a prefix of a halted one.
* `Turing.MultiTapeNTM.runsInTime_one_of_forall_step_initCfg`: a machine whose first steps all
  halt runs within one step.
* `Turing.MultiTapeNTM.DecidesInSpace.recognizesInSpace`: a decider is a recognizer.
* `Turing.MultiTapeNTM.DecidesInSpace.exists_runsInTime`: every branch of a decider halts.
* `Turing.MultiTapeNTM.RunsInTime.runsInSpace`: space is at most time.
* `Turing.MultiTapeNTM.DecidesInTime.decidesInSpace`: a time-bounded decider is a space-bounded
  one.
* `Turing.MultiTapeTM.ComputesFunInTimeAndSpace.decidesInSpace`,
  `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_decidesInSpace`: a deterministic decider
  within space `s` is a nondeterministic one with one computation path.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol} {ntm : MultiTapeNTM k Symbol State}

/-- A run path that ends halted extends to any longer length, by steps of its halted last
configuration to itself. -/
theorem RunPath.exists_extend_of_halted (p : ntm.RunPath input) (h : p.last.Halted) {n : ℕ}
    (hn : p.length ≤ n) :
    ∃ q : ntm.RunPath input, q.head = p.head ∧ q.length = n ∧ q.last = p.last := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => exact ⟨p, rfl, rfl, rfl⟩
  | succ m ih =>
    obtain ⟨q, hhead, hlen, hlast⟩ := ih (Nat.le_add_right _ _)
    have hstep : ntm.Step q.last q.last := (step_of_halt (hlast ▸ h)).mpr rfl
    exact ⟨q.snoc q.last hstep, by simpa using hhead,
      by rw [RelSeries.snoc_length, hlen, Nat.add_assoc], by simpa using hlast⟩

/-- Under a time bound `t`, every computation path that ends halted has the same last
configuration as a computation path of exactly `t` steps. -/
theorem RunsInTime.exists_time_eq {t : ℕ} (ht : ntm.RunsInTime input t)
    (p : ntm.ComputationPath input) (hp : p.last.Halted) :
    ∃ q : ntm.ComputationPath input, q.time = t ∧ q.last = p.last := by
  rcases le_or_gt t p.time with hle | hlt
  · -- cut the path after `t` steps; it has halted there
    have hlt : t < p.length + 1 := Nat.lt_succ_of_le hle
    let q : ntm.ComputationPath input :=
      ⟨p.toRunPath.take ⟨t, hlt⟩, by rw [RelSeries.head_take]; exact p.head_eq⟩
    have hq : q.last.Halted := ht q (by simp [q, ComputationPath.time, RunPath.time])
    refine ⟨q, by simp [q, ComputationPath.time, RunPath.time], ?_⟩
    have hlast : q.last = p.toRunPath ⟨t, hlt⟩ := RelSeries.last_take _ _
    exact hlast.trans (RunPath.last_eq_of_halted p.toRunPath _ (hlast ▸ hq)).symm
  · obtain ⟨q, hhead, hlen, hlast⟩ := RunPath.exists_extend_of_halted p.toRunPath hp hlt.le
    exact ⟨⟨q, hhead.trans p.head_eq⟩, hlen, hlast⟩

/-- Without stuck configurations, every run path extends to any longer length, as a prefix. -/
theorem RunPath.exists_extend (htotal : ∀ c : Cfg k Symbol State input, ∃ c', ntm.Step c c')
    (p : ntm.RunPath input) {n : ℕ} (hn : p.length ≤ n) :
    ∃ (q : ntm.RunPath input) (hq : q.length = n),
      ∀ i (hi : i < p.length + 1), q ⟨i, by omega⟩ = p ⟨i, hi⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => exact ⟨p, rfl, fun _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨q, hlen, hprefix⟩ := ih (Nat.le_add_right _ _)
    obtain ⟨c, hc⟩ := htotal q.last
    refine ⟨q.snoc c hc, by rw [RelSeries.snoc_length, hlen, Nat.add_assoc], fun i hi => ?_⟩
    rw [← hprefix i hi]
    have hi' : i < q.length + 1 := by omega
    exact (congrArg (q.snoc c hc) (Fin.ext rfl)).trans (RelSeries.snoc_castSucc q c hc ⟨i, hi'⟩)

/-- **Actual halting.** Without stuck configurations, every computation path within a time bound
`t` is a prefix of a computation path of exactly `t` steps, which has halted. -/
theorem ComputationPath.exists_halted_extension
    (htotal : ∀ c : Cfg k Symbol State input, ∃ c', ntm.Step c c') {t : ℕ}
    (ht : ntm.RunsInTime input t) (p : ntm.ComputationPath input) (hp : p.time ≤ t) :
    ∃ (q : ntm.ComputationPath input) (hq : q.time = t), q.last.Halted ∧
      ∀ i (hi : i < p.length + 1),
        q.toRunPath ⟨i, by unfold time RunPath.time at hp hq; omega⟩ = p.toRunPath ⟨i, hi⟩ := by
  obtain ⟨q, hlen, hprefix⟩ := RunPath.exists_extend htotal p.toRunPath hp
  have hhead : q.head = ntm.initCfg input := by
    rw [← p.head_eq]
    exact hprefix 0 (Nat.succ_pos _)
  let q' : ntm.ComputationPath input := ⟨q, hhead⟩
  exact ⟨q', hlen, ht q' hlen.ge, hprefix⟩

/-- If every step from the initial configuration reaches a halted configuration, every computation
path halts within one step. -/
theorem runsInTime_one_of_forall_step_initCfg
    (h : ∀ c, ntm.Step (ntm.initCfg input) c → c.Halted) : ntm.RunsInTime input 1 := by
  intro p hp
  have hlen : 1 < p.length + 1 := by unfold ComputationPath.time RunPath.time at hp; omega
  have hstep : ntm.Step (p.toRunPath ⟨0, by omega⟩) (p.toRunPath ⟨1, hlen⟩) :=
    p.toRunPath.step ⟨0, by omega⟩
  rw [show p.toRunPath ⟨0, by omega⟩ = ntm.initCfg input from p.head_eq] at hstep
  exact (RunPath.last_eq_of_halted p.toRunPath _ (h _ hstep)) ▸ h _ hstep

/-- A computation path extends by any step from its last configuration. -/
theorem ComputationPath.exists_snoc (p : ntm.ComputationPath input) {c : Cfg k Symbol State input}
    (h : ntm.Step p.last c) : ∃ q : ntm.ComputationPath input, q.time = p.time + 1 ∧ q.last = c :=
  ⟨⟨p.toRunPath.snoc c h, by simpa using p.head_eq⟩, by simp [ComputationPath.time, RunPath.time],
    by simp⟩

/-- The machine accepts `input` when some computation path ends halted with output `[true]`. -/
def Accepts (ntm : MultiTapeNTM k Bool State) (input : List Bool) : Prop :=
  ∃ p : ntm.ComputationPath input, p.last.Halted ∧ p.last.output = [true]

/-- Under a time bound `t`, a machine accepts exactly when some computation path of exactly `t`
steps ends with output `[true]`; such a path has halted. -/
theorem accepts_iff_exists_time_eq {ntm : MultiTapeNTM k Bool State} {input : List Bool} {t : ℕ}
    (ht : ntm.RunsInTime input t) :
    ntm.Accepts input ↔ ∃ p : ntm.ComputationPath input, p.time = t ∧ p.last.output = [true] := by
  constructor
  · rintro ⟨p, hhalt, hout⟩
    obtain ⟨q, hq, hlast⟩ := ht.exists_time_eq p hhalt
    exact ⟨q, hq, hlast ▸ hout⟩
  · rintro ⟨p, hp, hout⟩
    exact ⟨p, ht p hp.ge, hout⟩

variable {α : Type*}

/-- `ntm` decides `A` within `t` relative to the encoding `enc`: on every encoded instance `enc a`,
every computation path of at least `t a` steps ends halted, and `a ∈ A` exactly when some
computation path accepts. A computation path may also end stuck before `t a` steps; it does not
accept. -/
def DecidesInTime (ntm : MultiTapeNTM k Bool State) (enc : α ↪ List Bool) (A : Set α)
    (t : α → ℕ) : Prop :=
  ∀ a, ntm.RunsInTime (enc a) (t a) ∧ (a ∈ A ↔ ntm.Accepts (enc a))

/-- Some nondeterministic machine with a binary alphabet and finitely many states decides `A`
within `t`. -/
def DecidableInTime (A : Set α) (enc : α ↪ List Bool) (t : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State),
    ntm.DecidesInTime enc A t

/-- Some nondeterministic machine with a binary alphabet and finitely many states decides `A`
within a time bound polynomial in the length of the encoded instance. -/
def DecidableInPolyTime (A : Set α) (enc : α ↪ List Bool) : Prop :=
  ∃ t, MultiTapeTM.PolyBounded (fun a => (enc a).length) t ∧ DecidableInTime A enc t

/-- Time bounds can be increased. -/
theorem DecidesInTime.mono {ntm : MultiTapeNTM k Bool State} {enc : α ↪ List Bool} {A : Set α}
    {t t' : α → ℕ} (h : ntm.DecidesInTime enc A t) (ht : ∀ a, t a ≤ t' a) :
    ntm.DecidesInTime enc A t' :=
  fun a => ⟨(h a).1.mono (ht a), (h a).2⟩

/-- `ntm` recognizes `A` within space `s` relative to the encoding `enc`: on every encoded
instance `enc a`, every computation prefix visits at most `s a` work-tape cells, and `a ∈ A`
exactly when some computation path accepts. No time bound is imposed: a branch may run forever or
end stuck, and neither accepts. -/
def RecognizesInSpace (ntm : MultiTapeNTM k Bool State) (enc : α ↪ List Bool) (A : Set α)
    (s : α → ℕ) : Prop :=
  ∀ a, ntm.RunsInSpace (enc a) (s a) ∧ (a ∈ A ↔ ntm.Accepts (enc a))

/-- Space bounds can be increased. -/
theorem RecognizesInSpace.mono {ntm : MultiTapeNTM k Bool State} {enc : α ↪ List Bool}
    {A : Set α} {s s' : α → ℕ} (h : ntm.RecognizesInSpace enc A s) (hs : ∀ a, s a ≤ s' a) :
    ntm.RecognizesInSpace enc A s' :=
  fun a => ⟨(h a).1.mono (hs a), (h a).2⟩

/-- `ntm` decides `A` within space `s` relative to the encoding `enc`: it recognizes `A` within
space `s`, and every branch halts [Sipser, Definition 8.1][Sipser2013]: on every encoded instance
some number of steps bounds every computation path. A path may end stuck before the bound; it does
not accept. -/
def DecidesInSpace (ntm : MultiTapeNTM k Bool State) (enc : α ↪ List Bool) (A : Set α)
    (s : α → ℕ) : Prop :=
  ntm.RecognizesInSpace enc A s ∧ ∀ a, ∃ t, ntm.RunsInTime (enc a) t

/-- A decider within space `s` recognizes its problem within space `s`. -/
theorem DecidesInSpace.recognizesInSpace {ntm : MultiTapeNTM k Bool State} {enc : α ↪ List Bool}
    {A : Set α} {s : α → ℕ} (h : ntm.DecidesInSpace enc A s) : ntm.RecognizesInSpace enc A s :=
  h.1

/-- Every branch of a decider halts: on every encoded instance some number of steps bounds every
computation path. -/
theorem DecidesInSpace.exists_runsInTime {ntm : MultiTapeNTM k Bool State}
    {enc : α ↪ List Bool} {A : Set α} {s : α → ℕ} (h : ntm.DecidesInSpace enc A s) (a : α) :
    ∃ t, ntm.RunsInTime (enc a) t :=
  h.2 a

/-- Space bounds can be increased. -/
theorem DecidesInSpace.mono {ntm : MultiTapeNTM k Bool State} {enc : α ↪ List Bool} {A : Set α}
    {s s' : α → ℕ} (h : ntm.DecidesInSpace enc A s) (hs : ∀ a, s a ≤ s' a) :
    ntm.DecidesInSpace enc A s' :=
  ⟨h.recognizesInSpace.mono hs, h.exists_runsInTime⟩

/-- **Space is at most time.** Under a time bound `t`, every computation path visits at most
`k * (t + 1)` work-tape cells: within `t` steps each head visits at most `t + 1` cells, and from
step `t` on the path stays at a halted configuration. -/
theorem RunsInTime.runsInSpace {t : ℕ} (h : ntm.RunsInTime input t) :
    ntm.RunsInSpace input (k * (t + 1)) := by
  intro p
  rcases le_or_gt p.time t with hle | hlt
  · exact (RunPath.space_le_mul_time_add_one p.toRunPath).trans
      (Nat.mul_le_mul_left k (Nat.add_le_add_right hle 1))
  -- the first `t` steps have halted, and the path stays there
  have ht : t < p.length + 1 := by unfold ComputationPath.time RunPath.time at hlt; omega
  let q : ntm.ComputationPath input :=
    ⟨p.toRunPath.take ⟨t, ht⟩, by rw [RelSeries.head_take]; exact p.head_eq⟩
  have hq : q.time = t := rfl
  have hhalt : (p.toRunPath ⟨t, ht⟩).Halted := by
    have hlast : q.last = p.toRunPath ⟨t, ht⟩ := RelSeries.last_take _ _
    exact hlast ▸ h q hq.ge
  have hsub : ∀ c ∈ p.toRunPath, c ∈ q.toRunPath := by
    rintro _ ⟨j, rfl⟩
    rcases le_or_gt j.val t with hj | hj
    · exact ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩
    · refine ⟨Fin.last _, ?_⟩
      have hj' := RunPath.last_eq_of_halted (p.toRunPath.take j) ⟨t, Nat.lt_succ_of_lt hj⟩ hhalt
      rw [RelSeries.last_take] at hj'
      change p.toRunPath ⟨t, ht⟩ = p.toRunPath j
      exact hj'.symm
  exact (RunPath.space_le_of_subset hsub).trans
    ((RunPath.space_le_mul_time_add_one q.toRunPath).trans_eq (by rw [← hq]; rfl))

/-- A decider within time `t` decides within the space it visits in that time, `k * (t a + 1)`, and
every branch halts within `t a` steps. -/
theorem DecidesInTime.decidesInSpace {ntm : MultiTapeNTM k Bool State}
    {enc : α ↪ List Bool} {A : Set α} {t : α → ℕ} (h : ntm.DecidesInTime enc A t) :
    ntm.DecidesInSpace enc A fun a => k * (t a + 1) :=
  ⟨fun a => ⟨(h a).1.runsInSpace, (h a).2⟩, fun a => ⟨t a, (h a).1⟩⟩

/-- **A deterministic decider is a nondeterministic decider** with one computation path: a machine
computing a Boolean function `f` within time `t` and space `s` decides, as a nondeterministic
machine, the problem where `f` is `true` within space `s`. Its only path halts within `t a` steps,
its prefixes and its halted extensions visit no more cells than the run, and it accepts exactly
when it halts with output `[true]`. -/
theorem _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace.decidesInSpace
    {tm : MultiTapeTM k Bool State} {enc : α ↪ List Bool} {f : α → Bool} {t s : α → ℕ}
    {A : Set α} (htm : tm.ComputesFunInTimeAndSpace enc MultiTapeTM.encBool f t s)
    (hA : ∀ a, a ∈ A ↔ f a = true) : tm.toMultiTapeNTM.DecidesInSpace enc A s := by
  refine ⟨fun a => ?_, fun a => ?_⟩
  swap
  · obtain ⟨⟨u, hhalt, -⟩, -, -⟩ := htm a
    exact ⟨u, MultiTapeTM.runsInTime_of_halted hhalt⟩
  obtain ⟨⟨u, hhalt, hout⟩, -, hspace⟩ := htm a
  refine ⟨hspace, ?_⟩
  rw [hA a, accepts_iff_exists_time_eq (MultiTapeTM.runsInTime_of_halted hhalt)]
  constructor
  · intro hf
    refine ⟨ComputationPath.ofDeterministic tm (enc a) u, rfl, ?_⟩
    rw [MultiTapeTM.computationPath_last_eq_runFrom]
    change (tm.runFrom _ u).output = _
    rw [hout, hf]
    rfl
  · rintro ⟨q, hq, hout'⟩
    rw [MultiTapeTM.computationPath_last_eq_runFrom, hq, hout] at hout'
    exact List.head_eq_of_cons_eq hout'

/-- A Boolean function computable within time `t` and space `s` decides the problem where it is
`true` by some nondeterministic machine with a binary alphabet and finitely many states, within
space `s`. -/
theorem _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_decidesInSpace
    {enc : α ↪ List Bool} {f : α → Bool} {t s : α → ℕ} {A : Set α}
    (h : MultiTapeTM.ComputableInTimeAndSpace f enc MultiTapeTM.encBool t s)
    (hA : ∀ a, a ∈ A ↔ f a = true) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State),
      ntm.DecidesInSpace enc A s :=
  let ⟨k, State, hfinite, tm, htm⟩ := h
  ⟨k, State, hfinite, tm.toMultiTapeNTM, htm.decidesInSpace hA⟩

end Turing.MultiTapeNTM
