/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WhileInput
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Step machines

A step machine reads its input with a two-way head and keeps an arbitrary state. In each step, a
pure function of the state and the symbol under the head gives the next state, a move of the head
by at most one cell and a word to emit. It halts in the states where `halt` holds.

Step machines describe space-bounded computations without tapes: the space of a computation is the
size of its states, while the position of the head costs nothing, since a Turing machine realizing
the step machine keeps its input head at the same position. A machine whose states take at most
`s` bits halts on an input of length `n` within `(n + 2) * 3 ^ s` steps, if it halts at all, since
it never repeats a state and a head position before halting; in particular, a machine in
logarithmic space halts within polynomially many steps.

## Main definitions

* `Turing.StepMachine`: step machines.
* `Turing.StepMachine.run`: the configuration after a number of steps.
* `Turing.StepMachine.HaltsAt`: the first step at which a machine has halted.
* `Turing.StepMachine.Simulates`: a step machine simulates a system, with a fixed number of its
  steps per step of the system.

## Main results

* `Turing.StepMachine.Simulates.exists_haltsAt`: a simulating machine halts when the simulated
  system does, with the same output.
* `Turing.StepMachine.HaltsAt.lt_three_pow`: a machine whose states take at most `s` bits halts
  within `(n + 2) * 3 ^ s` steps.
* `Turing.StepMachine.HaltsAt.lt_pow_of_log`: in space `c * log₂ (n + 2)`, a machine halts within
  `(n + 2) ^ (2 * c + 1)` steps.
-/

@[expose] public section

namespace Turing

/-- A step machine with states `σ`, input symbols `Γ` and output symbols `Out`: from the state `q`
with `a` under the head, it moves to `(step q a).1`, moves its head by `(step q a).2.1` and emits
`(step q a).2.2`, unless `halt q`. The symbol under the head is `none` on the blanks before and
after the input, and the head does not move beyond them. Returning to the start of the input needs
no move of its own: move left until the blank before the input, then right. -/
structure StepMachine (σ Γ Out : Type*) where
  /-- The initial state. -/
  init : σ
  /-- The halting states. -/
  halt : σ → Bool
  /-- The next state, the move of the head and the emitted word. -/
  step : σ → Option Γ → σ × SignType × List Out

namespace StepMachine

variable {σ Γ Out : Type*} (m : StepMachine σ Γ Out) {input : List Γ}

/-- A configuration on `input`: the state, the position of the head and the output so far. -/
structure Cfg (σ Out : Type*) (input : List Γ) where
  /-- The state. -/
  state : σ
  /-- The position of the head, with the blanks at `0` and `input.length + 1`. -/
  pos : Fin (input.length + 2)
  /-- The output so far. -/
  out : List Out

/-- The initial configuration: the initial state, the head on the first cell, no output. -/
def initCfg (input : List Γ) : Cfg σ Out input := ⟨m.init, 1, []⟩

/-- The step from the configuration `c`, on the symbol under its head. -/
def stepAt (c : Cfg σ Out input) : σ × SignType × List Out :=
  m.step c.state (MultiTapeTM.inputSymbolAt input c.pos)

/-- One step, unless the machine has halted. -/
def stepCfg (c : Cfg σ Out input) : Cfg σ Out input :=
  if m.halt c.state then c else ⟨(m.stepAt c).1, moveInputPos c.pos (m.stepAt c).2.1,
    c.out ++ (m.stepAt c).2.2⟩

/-- The configuration after `t` steps on `input`. -/
def run (input : List Γ) (t : ℕ) : Cfg σ Out input := m.stepCfg^[t] (m.initCfg input)

/-- The machine has halted after exactly `t` steps, and not before. -/
def HaltsAt (input : List Γ) (t : ℕ) : Prop :=
  m.halt (m.run input t).state ∧ ∀ i < t, ¬m.halt (m.run input i).state

/-- The machine halts on `input` with the output `out`. -/
def Computes (input : List Γ) (out : List Out) : Prop :=
  ∃ t, m.HaltsAt input t ∧ (m.run input t).out = out

/-- The state and the position of the head: all that the next steps depend on. -/
def Cfg.core (c : Cfg σ Out input) : σ × Fin (input.length + 2) := (c.state, c.pos)

lemma run_succ (t : ℕ) : m.run input (t + 1) = m.stepCfg (m.run input t) :=
  Function.iterate_succ_apply' _ _ _

/-- A step from a configuration that has not halted. -/
lemma run_succ_of_not_halt {t : ℕ} (h : m.halt (m.run input t).state = false) :
    m.run input (t + 1) = ⟨(m.stepAt (m.run input t)).1,
      moveInputPos (m.run input t).pos (m.stepAt (m.run input t)).2.1,
      (m.run input t).out ++ (m.stepAt (m.run input t)).2.2⟩ := by
  rw [run_succ, stepCfg]
  simp [h]

/-- Before halting, the output is what the steps emitted. -/
lemma out_run {t : ℕ} (ht : ∀ i < t, m.halt (m.run input i).state = false) :
    (m.run input t).out = ((List.range t).map fun i => (m.stepAt (m.run input i)).2.2).flatten := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [m.run_succ_of_not_halt (ht t (by omega)), List.range_succ, List.map_append,
      List.flatten_append, ih fun i hi => ht i (by omega)]
    simp

/-- The output only grows. -/
lemma out_run_prefix {r t : ℕ} (h : r ≤ t) : (m.run input r).out <+: (m.run input t).out := by
  induction t, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
    refine ih.trans ?_
    rw [run_succ, stepCfg]
    split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _

/-- A halted machine stays put. -/
lemma run_add_of_halt {t : ℕ} (h : m.halt (m.run input t).state) (n : ℕ) :
    m.run input (t + n) = m.run input t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, run_succ, ih]; simp [stepCfg, h]

/-- A machine that has halted by the time `T` halts at some time up to `T`, with the
configuration it has at `T`. -/
lemma exists_haltsAt_le {T : ℕ} (h : m.halt (m.run input T).state) :
    ∃ t ≤ T, m.HaltsAt input t ∧ m.run input t = m.run input T := by
  classical
  have hex : ∃ t, m.halt (m.run input t).state := ⟨T, h⟩
  have hle := Nat.find_min' hex h
  refine ⟨Nat.find hex, hle, ⟨Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩, ?_⟩
  rw [← Nat.add_sub_cancel' hle, m.run_add_of_halt (Nat.find_spec hex)]

/-! ### Simulations -/

/-- `m` on `input` **simulates** the system `next` along `R`, with `d` steps of `m` per step of
the system: `R` is kept by `d` steps from a state that has not halted, and matches the halting
flags and the outputs. -/
structure Simulates {α : Type*} (input : List Γ) (next : α → α) (halt : α → Bool)
    (out : α → List Out) (R : α → Cfg σ Out input → Prop) (d : ℕ) : Prop where
  step : ∀ a c, R a c → halt a = false → R (next a) (m.stepCfg^[d] c)
  halt_eq : ∀ a c, R a c → m.halt c.state = halt a
  out_eq : ∀ a c, R a c → c.out = out a

namespace Simulates

variable {m} {α : Type*} {a₀ : α} {next : α → α} {halt : α → Bool} {out : α → List Out}
  {R : α → Cfg σ Out input → Prop} {d t₀ : ℕ}

/-- From `R` at the time `t₀`, after `u` steps of the system, `m` has made `u * d` more steps
along `R`. -/
lemma run (h : m.Simulates input next halt out R d) (h₀ : R a₀ (m.run input t₀)) {u : ℕ}
    (hu : ∀ i < u, halt (next^[i] a₀) = false) :
    R (next^[u] a₀) (m.run input (t₀ + u * d)) := by
  induction u with
  | zero => simpa using h₀
  | succ u ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul, ← Nat.add_assoc, Nat.add_comm _ d,
      StepMachine.run, Function.iterate_add_apply]
    exact h.step _ _ (ih fun i hi => hu i (by omega)) (hu u (by omega))

/-- **The rounds of a simulation**: within `u` steps of the system, every time of `m` is `j < d`
steps into a round `q`, which starts along `R`. -/
lemma exists_round (h : m.Simulates input next halt out R d) (h₀ : R a₀ (m.run input t₀))
    {u : ℕ} (hu : ∀ i < u, halt (next^[i] a₀) = false) (hd : 0 < d) {i : ℕ} (hi : i ≤ u * d) :
    ∃ q j, j < d ∧ (q < u ∨ q = u ∧ j = 0) ∧ R (next^[q] a₀) (m.run input (t₀ + q * d)) ∧
      m.run input (t₀ + i) = m.stepCfg^[j] (m.run input (t₀ + q * d)) := by
  refine ⟨i / d, i % d, Nat.mod_lt _ hd, ?_, h.run h₀ fun k hk => hu k ?_, ?_⟩
  · rcases Nat.lt_or_ge (i / d) u with hq | hq
    · exact Or.inl hq
    · have := Nat.div_mul_le_self i d
      have := Nat.mul_le_mul_right d hq
      have := Nat.div_add_mod' i d
      have hq' : i / d = u := Nat.eq_of_mul_eq_mul_right hd (by omega)
      exact Or.inr ⟨hq', by rw [hq'] at this; omega⟩
  · have : i / d ≤ u := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hi)
    omega
  · have := Nat.div_add_mod' i d
    rw [StepMachine.run, StepMachine.run, ← Function.iterate_add_apply,
      show i % d + (t₀ + i / d * d) = t₀ + i by omega]

/-- **Simulation**: from `R` at the time `t₀`, when the system halts after `u` steps, `m` halts
within `u * d` more steps, with the same output. -/
theorem exists_haltsAt (h : m.Simulates input next halt out R d) (h₀ : R a₀ (m.run input t₀))
    {u : ℕ} (hu : ∀ i < u, halt (next^[i] a₀) = false) (hend : halt (next^[u] a₀)) :
    ∃ t ≤ t₀ + u * d, m.HaltsAt input t ∧ (m.run input t).out = out (next^[u] a₀) := by
  have hR := h.run h₀ hu
  obtain ⟨t, ht, hhalt, hrun⟩ := m.exists_haltsAt_le (by rw [h.halt_eq _ _ hR]; exact hend)
  exact ⟨t, ht, hhalt, by rw [hrun, h.out_eq _ _ hR]⟩

end Simulates

/-- The next core depends only on the current one. -/
lemma core_stepCfg {c₁ c₂ : Cfg σ Out input} (h : c₁.core = c₂.core) :
    (m.stepCfg c₁).core = (m.stepCfg c₂).core := by
  obtain ⟨q₁, p₁, o₁⟩ := c₁
  obtain ⟨q₂, p₂, o₂⟩ := c₂
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  unfold stepCfg
  split_ifs <;> rfl

/-- Runs from configurations with the same core keep having the same core. -/
lemma core_iterate {c₁ c₂ : Cfg σ Out input} (h : c₁.core = c₂.core) (n : ℕ) :
    (m.stepCfg^[n] c₁).core = (m.stepCfg^[n] c₂).core := by
  induction n generalizing c₁ c₂ with
  | zero => exact h
  | succ n ih => exact ih (m.core_stepCfg h)

/-- A machine never repeats a core before halting: a core shared by the steps `i < j ≤ t` would
give the halted state of step `t` already at step `t - j + i < t`. -/
lemma HaltsAt.core_ne_of_lt {t i j : ℕ} (ht : m.HaltsAt input t) (hij : i < j) (hjt : j ≤ t) :
    (m.run input i).core ≠ (m.run input j).core := by
  intro heq
  have h := m.core_iterate heq (t - j)
  simp only [run, ← Function.iterate_add_apply, Nat.sub_add_cancel hjt] at h
  have hq : (m.run input (t - j + i)).state = (m.run input t).state := congrArg Prod.fst h
  exact ht.2 (t - j + i) (by omega) (hq ▸ ht.1)

/-- **Before halting, the cores of a run are pairwise distinct.** -/
theorem HaltsAt.injOn_core {t : ℕ} (ht : m.HaltsAt input t) :
    Set.InjOn (fun i => (m.run input i).core) (Set.Iic t) := by
  intro i hi j hj hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact ht.core_ne_of_lt m h hj hij
  · exact ht.core_ne_of_lt m h hi hij.symm

/-- **A machine whose states take at most `s` bits halts within `(n + 2) * 3 ^ s` steps** on an
input of length `n`: its runs never repeat a state and a head position before halting, and there
are fewer than `3 ^ s` words of at most `s` bits. -/
theorem HaltsAt.lt_three_pow (enc : σ ↪ List Bool) {s t : ℕ}
    (hs : ∀ i, (enc (m.run input i).state).length ≤ s) (ht : m.HaltsAt input t) :
    t < (input.length + 2) * 3 ^ s := by
  -- a state of at most `s` bits is determined by its bits at the positions below `s`
  let bits (q : σ) (k : Fin s) : Option Bool := (enc q)[k.val]?
  have hbits {q q' : σ} (hq : (enc q).length ≤ s) (hq' : (enc q').length ≤ s)
      (h : bits q = bits q') : q = q' := by
    refine enc.injective (List.ext_getElem? fun k => ?_)
    rcases Nat.lt_or_ge k s with hk | hk
    · exact congrFun h ⟨k, hk⟩
    · simp [List.getElem?_eq_none (hq.trans hk), List.getElem?_eq_none (hq'.trans hk)]
  have hinj : Set.InjOn (fun i => ((m.run input i).pos, bits (m.run input i).state))
      (Set.Iic t) := fun i hi j hj h => ht.injOn_core m hi hj (Prod.ext
    (hbits (hs i) (hs j) (congrArg Prod.snd h)) (congrArg Prod.fst h))
  have hcard := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _)
    (Set.InjOn.mono (by simp) hinj : Set.InjOn _ (Finset.Iic t : Set ℕ))
  simp only [Nat.card_Iic, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_pi, Fintype.card_option, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, show (2 + 1 : ℕ) = 3 from rfl] at hcard
  omega

/-- **Logarithmic space gives polynomial time**: a machine whose states take at most
`c * log₂ (n + 2)` bits halts within `(n + 2) ^ (2 * c + 1)` steps on an input of length `n`. -/
theorem HaltsAt.lt_pow_of_log (enc : σ ↪ List Bool) {c t : ℕ}
    (hs : ∀ i, (enc (m.run input i).state).length ≤ c * Nat.log 2 (input.length + 2))
    (ht : m.HaltsAt input t) : t < (input.length + 2) ^ (2 * c + 1) := by
  refine (ht.lt_three_pow m enc hs).trans_le ?_
  set n := input.length
  calc (n + 2) * 3 ^ (c * Nat.log 2 (n + 2))
      ≤ (n + 2) * 4 ^ (c * Nat.log 2 (n + 2)) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = (n + 2) * (2 ^ Nat.log 2 (n + 2)) ^ (2 * c) := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul]
        ring_nf
    _ ≤ (n + 2) * (n + 2) ^ (2 * c) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) _)
    _ = (n + 2) ^ (2 * c + 1) := by ring

end StepMachine

end Turing
