/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Nondeterministic
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Every branch of a nondeterministic counter program

A nondeterministic counter program (`Turing.CounterProgram.toNondeterministicQueryMachine`)
writes a fresh choice bit into register `0` after every step. Its correctness is proved branch
by branch with the inductive predicate `Turing.CounterProgram.AllBranches`: every branch from a
configuration reaches a configuration satisfying `Q`, or halts in one satisfying `Post`, and
passes only through configurations whose registers are at most `B`. These predicates compose
(`Turing.CounterProgram.AllBranches.bind`), and every branch of a program satisfying one from
its initial configuration with `Q` empty halts within a common number of steps, keeps its
registers bounded and halts only in configurations satisfying `Post`
(`Turing.CounterProgram.AllBranches.exists_haltsWithin`,
`Turing.CounterProgram.AllBranches.replay`).

Most of a program is deterministic: its instructions do not mention register `0`
(`Turing.CounterProgram.Instr.readsChoice`). On such code every branch follows the
deterministic run up to register `0`, so the deterministic reachability of counter programs
(`Turing.CounterProgram.Reaches`) gives both every branch
(`Turing.CounterProgram.allBranches_of_reaches`) and one branch
(`Turing.CounterProgram.branches_of_reaches`).

## Main definitions

* `Turing.CounterProgram.Expr.readsChoice`, `Turing.CounterProgram.Instr.readsChoice`: whether an
  expression or an instruction mentions register `0`.
* `Turing.CounterProgram.AllBranches`: every branch reaches a target or halts.

## Main results

* `Turing.CounterProgram.AllBranches.bind`: sequential composition.
* `Turing.CounterProgram.AllBranches.exists_haltsWithin`,
  `Turing.CounterProgram.AllBranches.replay`:
  the consequences for every branch from the initial configuration.
* `Turing.CounterProgram.allBranches_of_reaches`, `Turing.CounterProgram.branches_of_reaches`:
  deterministic code that does not read register `0`.
* `Turing.CounterProgram.exists_decidesInLogSpace_of_allBranches`: deciding in logarithmic space
  from every branch and one accepting branch.
-/

@[expose] public section

namespace Turing

namespace CounterProgram

/-! ### Code that does not read the choice -/

namespace Expr

/-- Whether an expression mentions register `0`, the choice. -/
def readsChoice : Expr → Bool
  | const _ => false
  | reg i => i == 0
  | add a b | sub a b | bit a b | mul a b | div a b | mod a b => a.readsChoice || b.readsChoice

/-- An expression that does not mention register `0` ignores its value. -/
theorem eval_set_zero {e : Expr} (he : e.readsChoice = false) (regs : List ℕ) (x : ℕ) :
    e.eval (regs.set 0 x) = e.eval regs := by
  induction e with
  | const k => rfl
  | reg i =>
    have hi : i ≠ 0 := by simpa [readsChoice] using he
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hi)]
  | add a b iha ihb | sub a b iha ihb | bit a b iha ihb | mul a b iha ihb | div a b iha ihb
  | mod a b iha ihb =>
    simp only [readsChoice, Bool.or_eq_false_iff] at he
    simp [iha he.1, ihb he.2]

end Expr

namespace Instr

/-- Whether an instruction reads or writes register `0`, the choice. -/
def readsChoice : Instr → Bool
  | assign i e _ => i == 0 || e.readsChoice
  | lt a b _ _ => a.readsChoice || b.readsChoice
  | read e _ _ _ => e.readsChoice
  | emit _ _ => false
  | halt _ => false

end Instr

variable {P : CounterProgram} {w : List Bool}

/-- **A step that does not read the choice commutes with it**: overwriting register `0` before
the step overwrites it after the step. -/
theorem step_withChoice {s : Config} (hs : (P.instr s.1).readsChoice = false) (c : Bool) :
    P.step w (withChoice s c) = withChoice (P.step w s) c := by
  obtain ⟨l, regs⟩ := s
  have hq : P.query (l, regs.set 0 c.toNat) = P.query (l, regs) := by
    simp only [query, Instr.query]
    cases h : P.instr l <;> simp only
    rw [h, Instr.readsChoice] at hs
    exact Expr.eval_set_zero hs _ _
  simp only [withChoice, step_eq, halted]
  by_cases hh : (P.instr l).halts = true
  · simp only [hh, ↓reduceIte]
  · simp only [hh, Bool.false_eq_true, ↓reduceIte, exec, hq]
    cases h : P.instr l with
    | assign i e next =>
      rw [h, Instr.readsChoice, Bool.or_eq_false_iff] at hs
      have hi : i ≠ 0 := by simpa using hs.1
      simp only [Instr.exec, Expr.eval_set_zero hs.2]
      rw [List.set_comm _ _ hi]
    | lt a b yes no =>
      rw [h, Instr.readsChoice, Bool.or_eq_false_iff] at hs
      simp [Instr.exec, Expr.eval_set_zero hs.1, Expr.eval_set_zero hs.2]
    | read e onTrue onFalse onEnd => simp [Instr.exec]
    | emit b next => simp [Instr.exec]
    | halt out => simp [Instr.exec]

/-! ### Every branch -/

variable (P w) in
/-- `P.AllBranches w B Post Q s`: every branch from `s` reaches a configuration satisfying `Q`, or
halts in a configuration satisfying `Post`, and the configurations before are running ones with
registers at most `B`. -/
inductive AllBranches (B : ℕ) (Post Q : Config → Prop) : Config → Prop
  /-- A target is reached. -/
  | exit {s : Config} : Q s → AllBranches B Post Q s
  /-- A halt satisfying `Post`. -/
  | halt {s : Config} : P.halted s = true → Post s → (∀ r ∈ s.2, r ≤ B) →
      AllBranches B Post Q s
  /-- A step from a running configuration, with either choice. -/
  | step {s : Config} : P.halted s = false → (∀ r ∈ s.2, r ≤ B) →
      (∀ choice, AllBranches B Post Q (withChoice (P.step w s) choice)) →
      AllBranches B Post Q s

namespace AllBranches

variable {B : ℕ} {Post Q Q' : Config → Prop} {s : Config}

/-- **Sequential composition**: continuing from every target. -/
theorem bind (h : P.AllBranches w B Post Q s) (h' : ∀ q, Q q → P.AllBranches w B Post Q' q) :
    P.AllBranches w B Post Q' s := by
  induction h with
  | exit hq => exact h' _ hq
  | halt hh hp hb => exact .halt hh hp hb
  | step hh hb _ ih => exact .step hh hb ih

theorem mono (h : P.AllBranches w B Post Q s) (hQ : ∀ q, Q q → Q' q) :
    P.AllBranches w B Post Q' s :=
  h.bind fun q hq => .exit (hQ q hq)

/-- One step from a running configuration, whatever the choice. -/
theorem single (hh : P.halted s = false) (hb : ∀ r ∈ s.2, r ≤ B)
    (h : ∀ choice, Q (withChoice (P.step w s) choice)) : P.AllBranches w B Post Q s :=
  .step hh hb fun c => .exit (h c)

/-- **Every branch halts within a common number of steps**, for a program with no target. -/
theorem exists_haltsWithin (h : P.AllBranches w B Post (fun _ => False) s) :
    ∃ t, ∀ choices : List Bool, t ≤ choices.length →
      P.halted (P.toNondeterministicQueryMachine.replay w choices s) = true := by
  induction h with
  | exit hq => exact hq.elim
  | halt hh _ _ =>
    exact ⟨0, fun choices _ => by
      rw [NondeterministicQueryMachine.replay_of_halted _ _ hh]
      exact hh⟩
  | @step s hh _ _ ih =>
    obtain ⟨t₀, h₀⟩ := ih false
    obtain ⟨t₁, h₁⟩ := ih true
    refine ⟨max t₀ t₁ + 1, fun choices hlen => ?_⟩
    obtain ⟨c, choices, rfl⟩ : ∃ c rest, choices = c :: rest := by
      cases choices with
      | nil => simp at hlen
      | cons c rest => exact ⟨c, rest, rfl⟩
    rw [NondeterministicQueryMachine.replay_cons, step_toNondeterministicQueryMachine, hh]
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [List.length_cons] at hlen
    cases c
    · exact h₀ choices (by omega)
    · exact h₁ choices (by omega)

/-- **Every branch keeps its registers bounded and halts only where `Post` holds**, for a program
with no target. -/
theorem replay (h : P.AllBranches w B Post (fun _ => False) s) (choices : List Bool) :
    (∀ r ∈ (P.toNondeterministicQueryMachine.replay w choices s).2, r ≤ B) ∧
      (P.halted (P.toNondeterministicQueryMachine.replay w choices s) = true →
        Post (P.toNondeterministicQueryMachine.replay w choices s)) := by
  induction h generalizing choices with
  | exit hq => exact hq.elim
  | halt hh hp hb =>
    rw [NondeterministicQueryMachine.replay_of_halted _ _ hh]
    exact ⟨hb, fun _ => hp⟩
  | @step s hh hb _ ih =>
    cases choices with
    | nil => exact ⟨hb, fun h => absurd h (by simp [hh])⟩
    | cons c rest =>
      rw [NondeterministicQueryMachine.replay_cons, step_toNondeterministicQueryMachine, hh]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih c rest

end AllBranches

/-! ### Deterministic code -/

/-- **Every branch through deterministic code** that does not read register `0` follows the
deterministic run, whatever the choice before it. -/
theorem allBranches_of_reaches {B : ℕ} (hB : 1 ≤ B) {Post Q : Config → Prop} {R : Config → Prop}
    {s s' : Config} (h : P.Reaches w R s s')
    (hR : ∀ x, R x → (P.instr x.1).readsChoice = false ∧ (P.instr x.1).IsStep ∧
      ∀ r ∈ x.2, r ≤ B)
    (hQ : ∀ c, Q (withChoice s' c)) (c : Bool) :
    P.AllBranches w B Post Q (withChoice s c) := by
  obtain ⟨t, rfl, ht⟩ := h
  induction t generalizing s c with
  | zero => exact .exit (hQ c)
  | succ t ih =>
    obtain ⟨hr, hstep, hb⟩ := hR _ (ht 0 (by omega))
    simp only [Function.iterate_zero, id] at hr hstep hb
    have hh : P.halted (withChoice s c) = false := by
      revert hstep
      simp only [halted, withChoice_fst]
      cases P.instr s.1 <;> simp [Instr.IsStep, Instr.halts]
    refine .step hh (List.forall_mem_set_of_forall_mem hb (by cases c <;> simp; omega))
      fun c' => ?_
    rw [step_withChoice hr, show withChoice (withChoice (P.step w s) c) c' =
      withChoice (P.step w s) c' by simp [withChoice]]
    exact ih c' (fun t' ht' => by
      have := ht (t' + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
      (by simpa only [Function.iterate_succ_apply] using hQ)

/-- One step of deterministic code that does not read register `0`, with any choice. -/
private theorem branches_step {s : Config} (hr : (P.instr s.1).readsChoice = false)
    (hstep : (P.instr s.1).IsStep) (c c' : Bool) :
    Branches (P := P) (w := w) (withChoice s c) (withChoice (P.step w s) c') := by
  have hh : P.halted (withChoice s c) = false := by
    revert hstep
    simp only [halted, withChoice_fst]
    cases P.instr s.1 <;> simp [Instr.IsStep, Instr.halts]
  have := Branches.single (P := P) (w := w) hh c'
  rwa [step_withChoice hr, show withChoice (withChoice (P.step w s) c) c' =
    withChoice (P.step w s) c' by simp [withChoice]] at this

/-- **One branch through deterministic code** that does not read register `0`: the
deterministic run from `s` to `s'`, ending with any choice `c'` when `s ≠ s'` and with the
initial choice `c` when `s = s'`. -/
theorem branches_of_reaches {R : Config → Prop} {s s' : Config} (h : P.Reaches w R s s')
    (hR : ∀ x, R x → (P.instr x.1).readsChoice = false ∧ (P.instr x.1).IsStep)
    (c c' : Bool) (hc : s = s' → c = c') :
    Branches (P := P) (w := w) (withChoice s c) (withChoice s' c') := by
  obtain ⟨t, rfl, ht⟩ := h
  rcases t with _ | t
  · rw [hc rfl]
    exact Branches.refl _
  · clear hc
    induction t generalizing s c with
    | zero =>
      obtain ⟨hr, hstep⟩ := hR s (by simpa using ht 0 (by omega))
      exact branches_step hr hstep c c'
    | succ t ih =>
      obtain ⟨hr, hstep⟩ := hR s (by simpa using ht 0 (by omega))
      refine (branches_step hr hstep c c).trans ?_
      rw [Function.iterate_succ_apply]
      exact ih c (fun t' ht' => by
        have := ht (t' + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this)

/-! ### Steps of code that does not read the choice -/

variable (P) in
/-- Running configurations, with registers at most `B`, at instructions that do not read the
choice. -/
def Oblivious (B : ℕ) (s : Config) : Prop :=
  (P.instr s.1).readsChoice = false ∧ P.Running B s

namespace Reaches

variable {B : ℕ} {regs : List ℕ} {s' : Config}

theorem oassign {c i : ℕ} {e : Expr} {next : ℕ} (hc : P.instr c = .assign i e next) (hi : i ≠ 0)
    (he : e.readsChoice = false) (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.Reaches w (P.Oblivious B) (next, regs.set i (e.eval regs)) s') :
    P.Reaches w (P.Oblivious B) (c, regs) s' :=
  Reaches.head ⟨by simp [hc, Instr.readsChoice, hi, he], by rw [hc]; trivial, hB⟩
    (by rwa [P.step_assign w hc])

theorem olt {c : ℕ} {x y : Expr} {yes no : ℕ} (hc : P.instr c = .lt x y yes no)
    (hx : x.readsChoice = false) (hy : y.readsChoice = false) (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.Reaches w (P.Oblivious B) (if x.eval regs < y.eval regs then yes else no, regs) s') :
    P.Reaches w (P.Oblivious B) (c, regs) s' :=
  Reaches.head ⟨by simp [hc, Instr.readsChoice, hx, hy], by rw [hc]; trivial, hB⟩
    (by rwa [P.step_lt w hc])

theorem oread {c : ℕ} {e : Expr} {onTrue onFalse onEnd : ℕ}
    (hc : P.instr c = .read e onTrue onFalse onEnd) (he : e.readsChoice = false)
    (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.Reaches w (P.Oblivious B) (readLabel onTrue onFalse onEnd w[e.eval regs]?, regs) s') :
    P.Reaches w (P.Oblivious B) (c, regs) s' :=
  Reaches.head ⟨by simp [hc, Instr.readsChoice, he], by rw [hc]; trivial, hB⟩
    (by rwa [P.step_read w hc])

end Reaches

/-- Every branch through oblivious deterministic code. -/
theorem allBranches_of_oblivious {B : ℕ} (hB : 1 ≤ B) {Post Q : Config → Prop} {s s' : Config}
    (h : P.Reaches w (P.Oblivious B) s s') (hQ : ∀ c, Q (withChoice s' c)) (c : Bool) :
    P.AllBranches w B Post Q (withChoice s c) :=
  allBranches_of_reaches hB h (fun _ hx => ⟨hx.1, hx.2.1, hx.2.2⟩) hQ c

/-- One branch through oblivious deterministic code. -/
theorem branches_of_oblivious {B : ℕ} {s s' : Config} (h : P.Reaches w (P.Oblivious B) s s')
    (c c' : Bool) (hc : s = s' → c = c') :
    Branches (P := P) (w := w) (withChoice s c) (withChoice s' c') :=
  branches_of_reaches h (fun _ hx => ⟨hx.1, hx.2.1⟩) c c' hc

/-! ### Deciding in logarithmic space -/

/-- **A nondeterministic counter program decides in logarithmic space** a problem when, on every
encoded instance, every branch from the initial configuration halts with registers at most
`(n + 1) ^ d` and accepts only instances of the problem, and some branch reaches the accepting
halt on every instance of the problem. -/
theorem exists_decidesInLogSpace_of_allBranches (P : CounterProgram) {α : Type}
    {enc : α ↪ List Bool} {A : Set α} (d : ℕ)
    (hall : ∀ a, P.AllBranches (enc a) (((enc a).length + 1) ^ d)
      (fun s => P.instr s.1 = .accept → a ∈ A) (fun _ => False) P.init)
    (hacc : ∀ a ∈ A, ∃ s, Branches (P := P) (w := enc a) P.init s ∧ P.instr s.1 = .accept) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      ntm.DecidesInSpace enc A fun a => c * (Nat.log2 (enc a).length + 1) := by
  choose time htime using fun a => (hall a).exists_haltsWithin
  refine P.exists_decidesInLogSpace time d (fun a choices hlen => htime a choices hlen.ge)
    (fun a choices => ((hall a).replay choices).1) fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨s, hs, hacc⟩ := hacc a ha
    exact accepts_of_branches hs hacc
  · obtain ⟨choices, hhalt, haccept⟩ := ha
    exact ((hall a).replay choices).2 hhalt (instr_of_accepts hhalt haccept)

end CounterProgram

end Turing
