/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WhileCond
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
public import Complexity.Computability.Machines.Turing.MultiTape.Deterministic
import Mathlib.Tactic.Ring

/-!
# Runs between configurations with shifted words

`Turing.MultiTapeTM.TransformsTapes` describes machines that start and halt with every word at
the start of its tape and every head on the first cell of its word. Some machines keep a word at a
drifting position, for example a stack that grows to the left. This file describes runs between
arbitrary configurations and transports specifications to configurations whose words sit anywhere.

`Turing.Cfg.shift δ` moves the contents and the head of every work tape `i` by `δ i` cells. Machines
are translation invariant (`Turing.MultiTapeTM.runFrom_shift`), so a run from a shifted
configuration is the shifted run. `Turing.tapesCfg input ws o h out` is the configuration whose tape
`i` holds the word `ws i` from cell `o i` on, with its head at cell `h i`; a `wordsCfg`
configuration shifted by `δ` is `tapesCfg input ws δ δ out`.

`Turing.MultiTapeTM.RunsBetween tm c c' t s` says that `tm`, started in its initial state on the
tapes of `c`, has halted on the tapes of `c'` after `t` steps, using at most `s` cells. Such runs
compose sequentially, embed into machines with more tapes, follow from `TransformsTapes`
specifications at any shift, and accumulate along the loop `Turing.MultiTapeTM.whileCond`.

## Main definitions

* `Turing.Cfg.shift`, `Turing.tapesCfg`: shifted configurations.
* `Turing.MultiTapeTM.RunsBetween`: a run between two configurations within bounds.

## Main results

* `Turing.MultiTapeTM.runFrom_shift`, `Turing.MultiTapeTM.space_shift`: translation invariance.
* `Turing.MultiTapeTM.RunsBetween.seq`, `.extendTapes`, `.of_transformsTapes`: composition.
* `Turing.MultiTapeTM.runsBetween_whileCond`: loops, with the costs of the rounds adding up.
-/

public section

namespace Turing

variable {k k' : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The configuration with the contents and the head of every work tape `i` moved by `δ i` cells to
the right. -/
@[expose] def Cfg.shift (δ : Fin k → ℤ) (c : Cfg k Symbol State input) : Cfg k Symbol State input :=
  ⟨c.state, c.inputPos, fun i z => c.workTapes i (z - δ i), fun i => c.workTapePos i + δ i,
    c.output⟩

@[simp]
lemma Cfg.shift_withState (δ : Fin k → ℤ) (c : Cfg k Symbol State input) {State' : Type*}
    (q : Option State') : (c.shift δ).withState q = (c.withState q).shift δ := rfl

/-- The configuration whose work tape `i` holds the word `ws i` from cell `o i` on, with its head at
cell `h i`, the input head at the start of the input and the output `out`. Its state is irrelevant
for `Turing.MultiTapeTM.RunsBetween`. -/
@[expose] def tapesCfg (input : List Symbol) (ws : Fin k → List Symbol) (o h : Fin k → ℤ)
    (out : List Symbol) : Cfg k Symbol Unit input :=
  ⟨none, 1, fun i z => tapeOfList (ws i) (z - o i), h, out⟩

@[simp]
lemma tapesCfg_workTapes (ws : Fin k → List Symbol) (o h : Fin k → ℤ) (out : List Symbol)
    (i : Fin k) (z : ℤ) :
    (tapesCfg input ws o h out).workTapes i z = tapeOfList (ws i) (z - o i) := rfl

@[simp]
lemma tapesCfg_workTapePos (ws : Fin k → List Symbol) (o h : Fin k → ℤ) (out : List Symbol) :
    (tapesCfg input ws o h out).workTapePos = h := rfl

/-- The symbol under the head of a tape of a `tapesCfg` configuration. -/
lemma tapesCfg_workTapeSymbols (ws : Fin k → List Symbol) (o h : Fin k → ℤ) (out : List Symbol)
    (i : Fin k) :
    (tapesCfg input ws o h out).workTapeSymbols i = tapeOfList (ws i) (h i - o i) := rfl

/-- With every head on the first cell of its word, the scanned symbols are the first letters. -/
lemma tapesCfg_workTapeSymbols_self (ws : Fin k → List Symbol) (o : Fin k → ℤ)
    (out : List Symbol) (i : Fin k) :
    (tapesCfg input ws o o out).workTapeSymbols i = (ws i).head? := by
  rw [tapesCfg_workTapeSymbols, sub_self, tapeOfList_zero]

lemma shift_tapesCfg (ws : Fin k → List Symbol) (o h δ : Fin k → ℤ) (out : List Symbol) :
    (tapesCfg input ws o h out).shift δ =
      tapesCfg input ws (fun i => o i + δ i) (fun i => h i + δ i) out := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i z
  simp only [Cfg.shift, tapesCfg]
  congr 1
  ring

lemma tapesCfg_zero_withState (ws : Fin k → List Symbol) (out : List Symbol) (q : Option State) :
    (tapesCfg input ws 0 0 out).withState q = wordsCfg input q ws out := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i z
  simp [tapesCfg, wordsCfg]

/-- A `wordsCfg` configuration, shifted. -/
lemma wordsCfg_shift (ws : Fin k → List Symbol) (δ : Fin k → ℤ) (out : List Symbol)
    (q : Option State) :
    (wordsCfg input q ws out).shift δ = (tapesCfg input ws δ δ out).withState q := by
  rw [← tapesCfg_zero_withState, ← Cfg.shift_withState, shift_tapesCfg]
  simp

namespace MultiTapeTM

/-! ### Translation invariance -/

/-- One step of a machine commutes with shifting the work tapes. -/
theorem step_shift (tm : MultiTapeTM k Symbol State) (δ : Fin k → ℤ)
    (c : Cfg k Symbol State input) : tm.step (c.shift δ) = (tm.step c).shift δ := by
  cases hq : c.state with
  | none =>
    have hq' : (c.shift δ).state = none := hq
    rw [step_of_halt hq', step_of_halt hq]
  | some q =>
    have hq' : (c.shift δ).state = some q := hq
    rw [step_of_state hq', step_of_state hq]
    have hw : (c.shift δ).workTapeSymbols = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, Cfg.shift]
    have hin : (c.shift δ).inputSymbol = c.inputSymbol := rfl
    rw [hw, hin]
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z
      simp only [Action.apply, Cfg.shift]
      generalize ((tm.tr q c.inputSymbol c.workTapeSymbols).workTapes i).1 = w
      cases w with
      | none => rfl
      | some s => simp only [Function.update_apply, sub_eq_iff_eq_add]
    · funext i
      simp only [Action.apply, Cfg.shift]
      ring

/-- **Translation invariance.** The run from a shifted configuration is the shifted run. -/
theorem runFrom_shift (tm : MultiTapeTM k Symbol State) (δ : Fin k → ℤ)
    (c : Cfg k Symbol State input) (t : ℕ) :
    tm.runFrom (c.shift δ) t = (tm.runFrom c t).shift δ := by
  induction t with
  | zero => rfl
  | succ t ih => rw [runFrom_succ, runFrom_succ, ih, step_shift]

/-- A shifted run visits as many cells as the run. -/
theorem space_shift (tm : MultiTapeTM k Symbol State) (δ : Fin k → ℤ)
    (c : Cfg k Symbol State input) (t : ℕ) :
    (MultiTapeNTM.RunPath.ofDeterministic tm (c.shift δ) t).space =
      (MultiTapeNTM.RunPath.ofDeterministic tm c t).space := by
  have h (i : Fin k) : (MultiTapeNTM.RunPath.ofDeterministic tm (c.shift δ) t).visitedByTapeHead i =
      ((MultiTapeNTM.RunPath.ofDeterministic tm c t).visitedByTapeHead i).image (· + δ i) := by
    ext z
    simp only [MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic, Finset.mem_image,
      runFrom_shift]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨m, hm, rfl⟩
  simp only [MultiTapeNTM.RunPath.space, MultiTapeNTM.RunPath.spaceUsedByTape, h,
    Finset.card_image_of_injective _ (add_left_injective _)]

/-! ### Runs between configurations -/

/-- `RunsBetween tm c c' t s`: started in its initial state on the tapes, heads and output of `c`,
the machine has halted after `t` steps on those of `c'`, having visited at most `s` cells. The
states of `c` and `c'` are ignored. -/
@[expose] def RunsBetween (tm : MultiTapeTM k Symbol State) (c c' : Cfg k Symbol Unit input)
    (t s : ℕ) :
    Prop :=
  tm.runFrom (c.withState (some tm.q₀)) t = c'.withState none ∧
    (MultiTapeNTM.RunPath.ofDeterministic tm (c.withState (some tm.q₀)) t).space ≤ s

namespace RunsBetween

variable {tm : MultiTapeTM k Symbol State} {c c' : Cfg k Symbol Unit input} {t s t' s' : ℕ}

/-- Larger bounds: a halted machine stays where it is. -/
theorem mono (h : RunsBetween tm c c' t s) (ht : t ≤ t') (hs : s ≤ s') :
    RunsBetween tm c c' t' s' := by
  have hhalt : (tm.runFrom (c.withState (some tm.q₀)) t).state = none := by rw [h.1]; rfl
  exact ⟨by rw [runFrom_eq_of_halt _ _ ht hhalt, h.1],
    by rw [space_eq_of_halt _ ht hhalt]; exact h.2.trans hs⟩

/-- A run to a halted configuration: its space is at most one cell per tape and configuration. -/
theorem of_runFrom (h : tm.runFrom (c.withState (some tm.q₀)) t = c'.withState none) :
    RunsBetween tm c c' t (k * (t + 1)) :=
  ⟨h, MultiTapeNTM.RunPath.space_le_mul_time_add_one _⟩

/-- A run between shifted configurations. -/
theorem shift (h : RunsBetween tm c c' t s) (δ : Fin k → ℤ) :
    RunsBetween tm (c.shift δ) (c'.shift δ) t s := by
  refine ⟨?_, ?_⟩
  · rw [Cfg.shift_withState, runFrom_shift, h.1]
    rfl
  · rw [Cfg.shift_withState, space_shift]
    exact h.2

open Sequential in
/-- **Sequential composition.** -/
theorem seq {State₁ : Type*} {tm₁ : MultiTapeTM k Symbol State₁} {c'' : Cfg k Symbol Unit input}
    {t₁ s₁ : ℕ} (h₀ : RunsBetween tm c c' t s) (h₁ : RunsBetween tm₁ c' c'' t₁ s₁) :
    RunsBetween (tm.seq tm₁) c c'' (t + t₁) (s + s₁) := by
  have hl : c.withState (some (tm.seq tm₁).q₀) = leftCfg tm₁ (c.withState (some tm.q₀)) := rfl
  have hmid : (c'.withState (none : Option State)).Halted := rfl
  refine ⟨?_, ?_⟩
  · rw [hl, runFrom_seq h₀.1 hmid h₁.1 rfl]
    rfl
  · rw [hl]
    refine (space_seq_le h₀.1 hmid ?_).trans (Nat.add_le_add h₀.2 h₁.2)
    rw [show (c'.withState (none : Option State)).withState (some tm₁.q₀) =
      c'.withState (some tm₁.q₀) from rfl, h₁.1]
    rfl

/-- **A run on the tapes selected by an embedding.** The other tapes are left alone; each costs
one cell. -/
theorem extendTapes (e : Fin k ↪ Fin k') {c : Cfg k' Symbol Unit input}
    {d : Cfg k Symbol Unit input} (h : RunsBetween tm (viewCfg e c) d t s) :
    RunsBetween (tm.extendTapes e) c (embed e d c.workTapes c.workTapePos) t (s + (k' - k)) := by
  refine ⟨?_, ?_⟩
  · rw [runFrom_extendTapes]
    exact congrArg (fun d => embed e d c.workTapes c.workTapePos) h.1
  · exact (space_extendTapes_le tm e _ t).trans (Nat.add_le_add_right h.2 _)

/-- A `TransformsTapes` specification, read as runs between shifted word configurations. -/
theorem of_transformsTapes
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} (h : TransformsTapes tm P Q t s) {ws : Fin k → List Symbol}
    (hP : P input ws) (δ : Fin k → ℤ) (out : List Symbol) :
    ∃ ws' e, Q input ws ws' e ∧
      RunsBetween tm (tapesCfg input ws δ δ out) (tapesCfg input ws' δ δ (out ++ e)) t s := by
  obtain ⟨ws', e, hrun, hQ, hsp⟩ := transformsTapes_iff_runFrom.mp h input ws out hP
  have h0 : RunsBetween tm (tapesCfg input ws 0 0 out) (tapesCfg input ws' 0 0 (out ++ e)) t s :=
    ⟨by rw [tapesCfg_zero_withState, tapesCfg_zero_withState, hrun],
      by rw [tapesCfg_zero_withState]; exact hsp⟩
  refine ⟨ws', e, hQ, ?_⟩
  have := h0.shift δ
  rw [shift_tapesCfg, shift_tapesCfg] at this
  simpa only [Pi.zero_apply, zero_add] using this

/-- A `TransformsTapes` specification whose postcondition determines the words and the emitted
word, read as a run between shifted word configurations. -/
theorem of_transformsTapes_eq
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop} {ws ws' : Fin k → List Symbol}
    {e : List Symbol}
    (h : TransformsTapes tm P (fun _ _ ws'' e' => ws'' = ws' ∧ e' = e) t s)
    (hP : P input ws) (δ : Fin k → ℤ) (out : List Symbol) :
    RunsBetween tm (tapesCfg input ws δ δ out) (tapesCfg input ws' δ δ (out ++ e)) t s := by
  obtain ⟨_, _, ⟨rfl, rfl⟩, h'⟩ := of_transformsTapes h hP δ out
  exact h'

end RunsBetween

/-- Viewing the tapes of a `tapesCfg` configuration through an embedding. -/
@[simp]
lemma viewCfg_tapesCfg (e : Fin k ↪ Fin k') (ws : Fin k' → List Symbol) (o h : Fin k' → ℤ)
    (out : List Symbol) :
    viewCfg e (tapesCfg input ws o h out) =
      tapesCfg input (fun j => ws (e j)) (fun j => o (e j)) (fun j => h (e j)) out := rfl

/-- Placing a `tapesCfg` configuration on the tapes selected by an embedding, the other tapes of
another one. -/
lemma embed_tapesCfg (e : Fin k ↪ Fin k') {v : Fin k → List Symbol} {ov hv : Fin k → ℤ}
    {ws ws' : Fin k' → List Symbol} {o h o' h' : Fin k' → ℤ} {out : List Symbol}
    (hsel : ∀ j, ws' (e j) = v j ∧ o' (e j) = ov j ∧ h' (e j) = hv j)
    (hother : ∀ l ∉ Set.range e, ws' l = ws l ∧ o' l = o l ∧ h' l = h l) :
    embed e (tapesCfg input v ov hv out) (tapesCfg input ws o h out).workTapes
      (tapesCfg input ws o h out).workTapePos = tapesCfg input ws' o' h' out := by
  refine Cfg.ext rfl rfl (funext fun l => ?_) (funext fun l => ?_) rfl
  · rcases hl : partialInv e l with _ | j
    · have hx := hother l fun ⟨j, hj⟩ => by simp [← hj] at hl
      simp only [embed, hl, tapesCfg, hx.1, hx.2.1]
    · have := partialInv_eq_some e hl
      subst this
      simp only [embed, hl, tapesCfg, (hsel j).1, (hsel j).2.1]
  · rcases hl : partialInv e l with _ | j
    · have hx := hother l fun ⟨j, hj⟩ => by simp [← hj] at hl
      simp only [embed, hl, tapesCfg, hx.2.2]
    · have := partialInv_eq_some e hl
      subst this
      simp only [embed, hl, tapesCfg, (hsel j).2.2]

/-- **One step from a `tapesCfg` configuration**, for an action that keeps the input head and emits
nothing: each tape is written and moved as the action says. -/
theorem step_tapesCfg {tm : MultiTapeTM k Symbol State} {q : State}
    {ws ws' : Fin k → List Symbol} {o h o' h' : Fin k → ℤ} {out : List Symbol}
    {a : Action k Symbol State}
    (ha : tm.tr q (tapesCfg input ws o h out).inputSymbol
      (fun i => tapeOfList (ws i) (h i - o i)) = a)
    (hin : a.inputTape = 0) (hout : a.output = none)
    (htape : ∀ i, (match (a.workTapes i).1 with
      | none => fun z => tapeOfList (ws i) (z - o i)
      | some s => Function.update (fun z => tapeOfList (ws i) (z - o i)) (h i) s) =
        fun z => tapeOfList (ws' i) (z - o' i))
    (hhead : ∀ i, h i + ((a.workTapes i).2 : ℤ) = h' i) :
    tm.step ((tapesCfg input ws o h out).withState (some q)) =
      (tapesCfg input ws' o' h' out).withState a.state := by
  rw [step_of_state rfl]
  change (tm.tr q (tapesCfg input ws o h out).inputSymbol
    (fun i => tapeOfList (ws i) (h i - o i))).apply _ = _
  rw [ha]
  refine Cfg.ext rfl ?_ (funext htape) (funext hhead) ?_
  · simp [Action.apply, hin, tapesCfg, Cfg.withState]
  · simp [Action.apply, hout, tapesCfg, Cfg.withState]

/-! ### Loops -/

namespace RunsBetweenWhileCond

variable {c : Option Symbol → (Fin k → Option Symbol) → Bool} {tm : MultiTapeTM k Symbol State}

/-- A configuration of `tm` as one of `whileCond c tm`. -/
private def runCfg (cfg : Cfg k Symbol State input) :
    Cfg k Symbol (RepeatUntilBlankState State) input :=
  cfg.mapState (fun st => some (st.elim .check .run))

private lemma step_runCfg (cfg : Cfg k Symbol State input) (h : ¬ cfg.Halted) :
    (whileCond c tm).step (runCfg cfg) = runCfg (tm.step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hstate : (runCfg cfg).state = some (RepeatUntilBlankState.run q) := by
    simp [runCfg, Cfg.mapState, hq]
  rw [step_of_state hstate, step_of_state hq]
  simp only [whileCond, tr_ofTr]
  rfl

private lemma runFrom_runCfg {cfg : Cfg k Symbol State input} {u n : ℕ} (hhalt : tm.HaltsAt cfg u)
    (hn : n ≤ u) :
    (whileCond c tm).runFrom (runCfg cfg) n = runCfg (tm.runFrom cfg n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runFrom_succ, runFrom_succ, ih (by lia), step_runCfg _ (hhalt.not_halted (by lia))]

private lemma step_check (d : Cfg k Symbol Unit input) :
    (whileCond c tm).step (d.withState (some .check)) =
      d.withState (if c d.inputSymbol d.workTapeSymbols then some (.run tm.q₀) else none) := by
  rw [step_of_state rfl]
  have hw : (d.withState (some (RepeatUntilBlankState.check : RepeatUntilBlankState State))
    ).workTapeSymbols = d.workTapeSymbols := rfl
  have hi : (d.withState (some (RepeatUntilBlankState.check : RepeatUntilBlankState State))
    ).inputSymbol = d.inputSymbol := rfl
  rw [hw, hi]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [whileCond, Action.apply, Cfg.withState]

/-- One round: from `check` with the condition holding, the loop runs `tm` and is back in
`check`. -/
private lemma exists_round {d d' : Cfg k Symbol Unit input} {t s : ℕ}
    (hc : c d.inputSymbol d.workTapeSymbols = true)
    (h : RunsBetween tm d d' t s) :
    ∃ u ≤ t, (whileCond c tm).runFrom (d.withState (some .check)) (u + 1) =
        d'.withState (some .check) ∧
      (MultiTapeNTM.RunPath.ofDeterministic (whileCond c tm) (d.withState (some .check))
        (1 + u)).space ≤ s + k := by
  obtain ⟨u, hu, hhalt⟩ := exists_haltsAt (tm := tm)
    (show (tm.runFrom (d.withState (some tm.q₀)) t).Halted by rw [h.1]; rfl)
  have hstart : (whileCond c tm).step (d.withState (some .check)) =
      runCfg (d.withState (some tm.q₀)) := by
    rw [step_check, hc]
    rfl
  have hrun : (whileCond c tm).runFrom (d.withState (some .check)) (1 + u) =
      d'.withState (some .check) := by
    rw [runFrom_add, runFrom_one, hstart, runFrom_runCfg hhalt le_rfl, ← hhalt.runFrom_eq hu, h.1]
    rfl
  refine ⟨u, hu, by rw [Nat.add_comm]; exact hrun, ?_⟩
  have h1 : (MultiTapeNTM.RunPath.ofDeterministic (whileCond c tm) (d.withState (some .check))
      1).space ≤ k := by
    refine space_le_of_workTapePos_const _ 1 fun m hm => ?_
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · rfl
    · rw [runFrom_one, step_check]
      rfl
  have h2 : (MultiTapeNTM.RunPath.ofDeterministic (whileCond c tm)
      ((whileCond c tm).runFrom (d.withState (some .check)) 1) u).space ≤ s := by
    rw [runFrom_one, hstart, space_eq_of_workTapePos (tm' := tm) _ (d.withState (some tm.q₀)) u
      fun m hm => by rw [runFrom_runCfg hhalt hm]; rfl]
    exact (space_mono tm _ hu).trans h.2
  have := (space_add_le (tm := whileCond c tm) (d.withState (some .check)) 1 u).trans
    (Nat.add_le_add h1 h2)
  omega

end RunsBetweenWhileCond

open RunsBetweenWhileCond in
/-- **Loops.** If `c` holds at the configurations `cfg i` for `i < n`, from each of which `tm`
runs to `cfg (i + 1)`, and fails at `cfg n`, then `whileCond c tm` runs from `cfg 0` to `cfg n`.
The times of the rounds add up, with one step per round to read the condition. -/
theorem runsBetween_whileCond {c : Option Symbol → (Fin k → Option Symbol) → Bool}
    {tm : MultiTapeTM k Symbol State} (cfg : ℕ → Cfg k Symbol Unit input) (n : ℕ) (t s : ℕ → ℕ)
    (hround : ∀ i < n, c (cfg i).inputSymbol (cfg i).workTapeSymbols = true ∧
      RunsBetween tm (cfg i) (cfg (i + 1)) (t i) (s i))
    (hstop : c (cfg n).inputSymbol (cfg n).workTapeSymbols = false) :
    RunsBetween (whileCond c tm) (cfg 0) (cfg n) (∑ i ∈ Finset.range n, (t i + 1) + 1)
      (∑ i ∈ Finset.range n, (s i + k) + 2 * k) := by
  set start := (cfg 0).withState (some (whileCond c tm).q₀) with hstart
  have hrec : ∀ m ≤ n, ∃ τ ≤ ∑ i ∈ Finset.range m, (t i + 1),
      (whileCond c tm).runFrom start τ = (cfg m).withState (some .check) ∧
      (MultiTapeNTM.RunPath.ofDeterministic (whileCond c tm) start τ).space ≤
        ∑ i ∈ Finset.range m, (s i + k) + k := by
    intro m hm
    induction m with
    | zero => exact ⟨0, le_rfl, rfl, by
        simpa using space_le_of_workTapePos_const (tm := whileCond c tm) start 0
          fun m hm => by rw [Nat.le_zero.mp hm]; rfl⟩
    | succ m ih =>
      obtain ⟨τ, hτ, hrun, hsp⟩ := ih (by lia)
      obtain ⟨hc, hr⟩ := hround m (by lia)
      obtain ⟨u, hu, hrun', hsp'⟩ := exists_round hc hr
      refine ⟨τ + (1 + u), by rw [Finset.sum_range_succ]; lia, ?_, ?_⟩
      · rw [runFrom_add, hrun, Nat.add_comm 1 u, hrun']
      · refine (space_add_le _ τ (1 + u)).trans ?_
        rw [hrun, Finset.sum_range_succ]
        have := Nat.add_le_add hsp hsp'
        omega
  obtain ⟨τ, hτ, hrun, hsp⟩ := hrec n le_rfl
  have hfinal : (whileCond c tm).runFrom start (τ + 1) = (cfg n).withState none := by
    rw [runFrom_succ, hrun, step_check, hstop]
    rfl
  have hhalt : ((whileCond c tm).runFrom start (τ + 1)).state = none := by rw [hfinal]; rfl
  refine ⟨by rw [runFrom_eq_of_halt _ _ (by lia) hhalt, hfinal], ?_⟩
  rw [space_eq_of_halt _ (by lia) hhalt]
  have h1 : (MultiTapeNTM.RunPath.ofDeterministic (whileCond c tm)
      ((whileCond c tm).runFrom start τ) 1).space ≤ k := by
    refine space_le_of_workTapePos_const _ 1 fun m hm => ?_
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
    · rfl
    · rw [hrun, runFrom_one, step_check]
      rfl
  have := (space_add_le (tm := whileCond c tm) start τ 1).trans (Nat.add_le_add hsp h1)
  omega

end MultiTapeTM

end Turing
