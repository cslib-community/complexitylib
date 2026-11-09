/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Nondeterministic

/-!
# Alternating machines

An alternating machine [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Arora and Barak, Section 5.3][AroraBarak09] is a nondeterministic machine whose states are
labelled existential or universal. Here it is a closed fair-coin table
(`Turing.MultiTapePTM`, the parametric machine with one action for each of two choices) together
with such a labelling (`Turing.MultiTapeATM`): at a running configuration the two transitions of
the table are the two moves (`Turing.MultiTapeATM.next`), as for the two transition functions of
Arora and Barak. A step of the machine is a step of the nondeterministic machine
`Turing.MultiTapePTM.toNTM` of the table, so no configuration is stuck, and time bounds are those of
that nondeterministic machine (`Turing.MultiTapeNTM.RunsInTime`).

Acceptance is the least fixed point of the labelling: a halted configuration accepts when its
output is exactly `[true]`, an existential configuration when one of its two moves leads to an
accepting configuration, and a universal configuration when both do. It is defined through the
number of moves allowed (`Turing.MultiTapeATM.AcceptsWithin`): within `0` moves only a halted
configuration with output `[true]` accepts, and a running configuration accepts within `n + 1`
moves when one (existential) or both (universal) of its moves accept within `n`. The machine
accepts an input when its initial configuration accepts within some number of moves
(`Turing.MultiTapeATM.Accepts`). Infinite branches never accept, and running configurations
reached when the moves are exhausted do not accept.

A machine decides `A` within time `t` (`Turing.MultiTapeATM.DecidesInTime`) when on every encoded
instance `enc a` every computation path of at least `t a` steps ends halted, and `a ∈ A` exactly
when the machine accepts `enc a`. Under such a bound, acceptance is acceptance within `t a` moves
(`Turing.MultiTapeATM.accepts_iff_acceptsWithin`). `Turing.MultiTapeATM.DecidableInPolyTime` asks
for one machine with a binary alphabet and finitely many states, and one polynomially bounded time
bound, for all instances; like `Turing.MultiTapeNTM.DecidableInPolyTime`, it is relative to the
encoding of instances.

## Main definitions

* `Turing.MultiTapeATM`: an alternating machine, a fair-coin table with universal states.
* `Turing.MultiTapeATM.next`, `Turing.MultiTapeATM.action`: the configuration after a move, and
  the action of a move.
* `Turing.MultiTapeATM.AcceptsWithin`, `Turing.MultiTapeATM.Accepts`: acceptance.
* `Turing.MultiTapeATM.DecidesInTime`, `Turing.MultiTapeATM.DecidableInTime`,
  `Turing.MultiTapeATM.DecidableInPolyTime`: deciding a problem within a time bound.

## Main results

* `Turing.MultiTapeATM.AcceptsWithin.mono`: acceptance within `n` moves is acceptance within more.
* `Turing.MultiTapeATM.runsInTime_iff_stepCoins`: time bounds through lists of moves.
* `Turing.MultiTapeATM.accepts_iff_acceptsWithin`: under a time bound `t`, acceptance is
  acceptance within `t` moves.
* `Turing.MultiTapeATM.accepts_iff_toNTM_accepts`: without universal states, acceptance is
  acceptance by the nondeterministic machine of the table.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing

/-- **An alternating machine** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]: a
closed fair-coin table, whose two transitions at a running configuration are the two moves,
together with a labelling of its states as universal or existential. -/
structure MultiTapeATM (k : ℕ) (Symbol State : Type) where
  /-- The transition table, with one action for each of the two moves. -/
  toPTM : MultiTapePTM k Symbol State
  /-- Whether a state is universal; the other states are existential. -/
  universal : State → Bool

namespace MultiTapeATM

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- The configuration after the move `b`: one step of the table with the coin `b`. A halted
configuration stays unchanged. -/
noncomputable def next (atm : MultiTapeATM k Symbol State) (b : Bool)
    (c : Cfg k Symbol State input) : Cfg k Symbol State input :=
  (atm.toPTM.withCoin b).toTM.step c

/-- The action of the move `b` at a state and read symbols. -/
def action (atm : MultiTapeATM k Symbol State) (state : State) (symbol : Option Symbol)
    (work : Fin k → Option Symbol) (b : Bool) : Turing.Action k Symbol State :=
  MultiTapeMachine.Action.emptyOracleEquiv (atm.toPTM.tr state symbol work Empty.elim b)

variable (atm : MultiTapeATM k Symbol State)

/-- A move from a running configuration applies its action. -/
theorem next_of_state {c : Cfg k Symbol State input} {q : State} (h : c.state = some q)
    (b : Bool) : atm.next b c = (atm.action q c.inputSymbol c.workTapeSymbols b).apply c := by
  rw [next, MultiTapeTM.step_of_state h, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
  rfl

/-- A halted configuration has no other move. -/
theorem next_of_halted {c : Cfg k Symbol State input} (h : c.state = none) (b : Bool) :
    atm.next b c = c :=
  MultiTapeTM.step_of_halt h

/-- Replaying moves one at a time. -/
theorem stepCoins_cons (b : Bool) (coins : List Bool) (c : Cfg k Symbol State input) :
    atm.toPTM.stepCoins (b :: coins) c = atm.toPTM.stepCoins coins (atm.next b c) :=
  rfl

/-- A halted configuration ignores every list of moves. -/
theorem stepCoins_of_halted {c : Cfg k Symbol State input} (h : c.state = none)
    (coins : List Bool) : atm.toPTM.stepCoins coins c = c := by
  induction coins with
  | nil => rfl
  | cons b coins ih => rw [stepCoins_cons, next_of_halted atm h, ih]

/-! ### Acceptance -/

/-- **Acceptance within `n` moves**: within `0` moves a configuration accepts when it has halted
with output `[true]`; within `n + 1` moves a halted configuration accepts when its output is
`[true]`, and a running configuration when one of its two moves (existential state) or both of
them (universal state) lead to configurations accepting within `n` moves. -/
def AcceptsWithin (atm : MultiTapeATM k Bool State) {input : List Bool} :
    ℕ → Cfg k Bool State input → Prop
  | 0, c => c.state = none ∧ c.output = [true]
  | n + 1, c => match c.state with
    | none => c.output = [true]
    | some q => if atm.universal q then ∀ b, atm.AcceptsWithin n (atm.next b c)
      else ∃ b, atm.AcceptsWithin n (atm.next b c)

/-- The machine accepts `input` when its initial configuration accepts within some number of
moves: the least fixed point of the labelling. -/
def Accepts (atm : MultiTapeATM k Bool State) (input : List Bool) : Prop :=
  ∃ n, atm.AcceptsWithin n (atm.toPTM.toNTM.initCfg input)

section Acceptance

variable (atm : MultiTapeATM k Bool State) {input : List Bool} {n : ℕ}
  {c : Cfg k Bool State input}

/-- A halted configuration accepts exactly when its output is `[true]`. -/
theorem acceptsWithin_of_halted (h : c.state = none) :
    atm.AcceptsWithin n c ↔ c.output = [true] := by
  cases n with
  | zero => simp [AcceptsWithin, h]
  | succ n => simp [AcceptsWithin, h]

/-- A running configuration does not accept without moves. -/
theorem not_acceptsWithin_zero {q : State} (h : c.state = some q) : ¬atm.AcceptsWithin 0 c := by
  simp [AcceptsWithin, h]

/-- A universal configuration accepts within `n + 1` moves when both of its moves accept within
`n`. -/
theorem acceptsWithin_succ_of_universal {q : State} (h : c.state = some q)
    (hq : atm.universal q = true) :
    atm.AcceptsWithin (n + 1) c ↔ ∀ b, atm.AcceptsWithin n (atm.next b c) := by
  simp [AcceptsWithin, h, hq]

/-- An existential configuration accepts within `n + 1` moves when one of its moves accepts within
`n`. -/
theorem acceptsWithin_succ_of_existential {q : State} (h : c.state = some q)
    (hq : atm.universal q = false) :
    atm.AcceptsWithin (n + 1) c ↔ ∃ b, atm.AcceptsWithin n (atm.next b c) := by
  simp [AcceptsWithin, h, hq]

variable {atm}

/-- **Acceptance within `n` moves is acceptance within more.** -/
theorem AcceptsWithin.mono {n' : ℕ} (h : atm.AcceptsWithin n c) (hn : n ≤ n') :
    atm.AcceptsWithin n' c := by
  induction n generalizing n' c with
  | zero =>
    obtain ⟨hhalt, hout⟩ := h
    exact (atm.acceptsWithin_of_halted hhalt).mpr hout
  | succ n ih =>
    obtain ⟨n', rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by omega⟩
    rcases hs : c.state with _ | q
    · exact (atm.acceptsWithin_of_halted hs).mpr ((atm.acceptsWithin_of_halted hs).mp h)
    · cases hq : atm.universal q
      · obtain ⟨b, hb⟩ := (atm.acceptsWithin_succ_of_existential hs hq).mp h
        exact (atm.acceptsWithin_succ_of_existential hs hq).mpr ⟨b, ih hb (by omega)⟩
      · have hb := (atm.acceptsWithin_succ_of_universal hs hq).mp h
        exact (atm.acceptsWithin_succ_of_universal hs hq).mpr fun b => ih (hb b) (by omega)

/-- If every list of `t` moves from `c` reaches a halted configuration, acceptance within any
number of moves is acceptance within `t`. -/
theorem AcceptsWithin.of_halted_stepCoins {t : ℕ}
    (ht : ∀ coins : List Bool, coins.length = t → (atm.toPTM.stepCoins coins c).state = none)
    (h : atm.AcceptsWithin n c) : atm.AcceptsWithin t c := by
  induction t generalizing n c with
  | zero =>
    have hhalt : c.state = none := ht [] rfl
    exact (atm.acceptsWithin_of_halted hhalt).mpr ((atm.acceptsWithin_of_halted hhalt).mp h)
  | succ t ih =>
    rcases hs : c.state with _ | q
    · exact (atm.acceptsWithin_of_halted hs).mpr ((atm.acceptsWithin_of_halted hs).mp h)
    · obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => exact absurd h (atm.not_acceptsWithin_zero hs)
        | succ m => exact ⟨m, rfl⟩
      have ht' (b : Bool) : ∀ coins : List Bool, coins.length = t →
          (atm.toPTM.stepCoins coins (atm.next b c)).state = none :=
        fun coins hlen => ht (b :: coins) (by simp [hlen])
      cases hq : atm.universal q
      · obtain ⟨b, hb⟩ := (atm.acceptsWithin_succ_of_existential hs hq).mp h
        exact (atm.acceptsWithin_succ_of_existential hs hq).mpr ⟨b, ih (ht' b) hb⟩
      · have hb := (atm.acceptsWithin_succ_of_universal hs hq).mp h
        exact (atm.acceptsWithin_succ_of_universal hs hq).mpr fun b => ih (ht' b) (hb b)

end Acceptance

/-! ### Time bounds -/

section Time

variable {atm : MultiTapeATM k Symbol State} {input : List Symbol} {t : ℕ}

/-- Under a time bound `t`, every list of `t` moves from the initial configuration reaches a halted
configuration. -/
theorem state_stepCoins_eq_none (h : atm.toPTM.toNTM.RunsInTime input t)
    {coins : List Bool} (hlen : coins.length = t) :
    (atm.toPTM.stepCoins coins (atm.toPTM.toNTM.initCfg input)).state = none := by
  obtain ⟨p, hhead, hp, hlast⟩ :=
    (atm.toPTM.exists_runPath_toNTM_iff (c := atm.toPTM.toNTM.initCfg input)).mpr
      ⟨coins, hlen, rfl⟩
  rw [← hlast]
  exact h ⟨p, hhead⟩ (by simp [MultiTapeNTM.ComputationPath.time, MultiTapeNTM.RunPath.time, hp])

/-- **Time bounds through moves.** Every computation path of at least `t` steps ends halted
exactly when every list of `t` moves from the initial configuration reaches a halted
configuration. -/
theorem runsInTime_iff_stepCoins : atm.toPTM.toNTM.RunsInTime input t ↔
    ∀ coins : List Bool, coins.length = t →
      (atm.toPTM.stepCoins coins (atm.toPTM.toNTM.initCfg input)).state = none := by
  refine ⟨fun h _ hlen => state_stepCoins_eq_none h hlen, fun h p hp => ?_⟩
  have ht : t < p.length + 1 := Nat.lt_succ_of_le hp
  obtain ⟨coins, hlen, hcoins⟩ := (atm.toPTM.exists_runPath_toNTM_iff).mp
    ⟨p.toRunPath.take ⟨t, ht⟩, RelSeries.head_take .., rfl, RelSeries.last_take _ _⟩
  have hhalt : (p.toRunPath ⟨t, ht⟩).Halted := by
    rw [← hcoins, show p.head = atm.toPTM.toNTM.initCfg input from p.head_eq]
    exact h coins hlen
  exact (MultiTapeNTM.RunPath.last_eq_of_halted p.toRunPath _ hhalt) ▸ hhalt

end Time

/-- **Acceptance under a time bound.** If every computation path of at least `t` steps ends
halted, the machine accepts exactly when its initial configuration accepts within `t` moves. -/
theorem accepts_iff_acceptsWithin {atm : MultiTapeATM k Bool State} {input : List Bool} {t : ℕ}
    (h : atm.toPTM.toNTM.RunsInTime input t) :
    atm.Accepts input ↔ atm.AcceptsWithin t (atm.toPTM.toNTM.initCfg input) :=
  ⟨fun ⟨_, hn⟩ => hn.of_halted_stepCoins fun _ hlen => state_stepCoins_eq_none h hlen,
    fun ht => ⟨t, ht⟩⟩

/-! ### Machines without universal states -/

section Existential

variable {atm : MultiTapeATM k Bool State} {input : List Bool}

/-- Without universal states, a configuration accepts within `n` moves exactly when some list of
`n` moves reaches a halted configuration with output `[true]`. -/
theorem acceptsWithin_iff_exists_stepCoins (h : ∀ q, atm.universal q = false) {n : ℕ}
    {c : Cfg k Bool State input} :
    atm.AcceptsWithin n c ↔ ∃ coins : List Bool, coins.length = n ∧
      (atm.toPTM.stepCoins coins c).state = none ∧
        (atm.toPTM.stepCoins coins c).output = [true] := by
  induction n generalizing c with
  | zero =>
    simp only [AcceptsWithin, List.length_eq_zero_iff, exists_eq_left, MultiTapePTM.stepCoins_nil]
  | succ n ih =>
    rcases hs : c.state with _ | q
    · rw [atm.acceptsWithin_of_halted hs]
      constructor
      · intro hout
        exact ⟨List.replicate (n + 1) false, List.length_replicate .., by
          rw [stepCoins_of_halted atm hs]; exact ⟨hs, hout⟩⟩
      · rintro ⟨coins, -, -, hout⟩
        rwa [stepCoins_of_halted atm hs] at hout
    · rw [atm.acceptsWithin_succ_of_existential hs (h q)]
      constructor
      · rintro ⟨b, hb⟩
        obtain ⟨coins, hlen, hcoins⟩ := ih.mp hb
        exact ⟨b :: coins, by simp [hlen], hcoins⟩
      · rintro ⟨coins, hlen, hcoins⟩
        obtain ⟨b, coins, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
        exact ⟨b, ih.mpr ⟨coins, by simpa using hlen, hcoins⟩⟩

/-- **Without universal states an alternating machine is nondeterministic**: under a time bound,
it accepts exactly when the nondeterministic machine of its table accepts. -/
theorem accepts_iff_toNTM_accepts (h : ∀ q, atm.universal q = false) {t : ℕ}
    (ht : atm.toPTM.toNTM.RunsInTime input t) :
    atm.Accepts input ↔ atm.toPTM.toNTM.Accepts input := by
  rw [accepts_iff_acceptsWithin ht, acceptsWithin_iff_exists_stepCoins h,
    MultiTapeNTM.accepts_iff_exists_time_eq ht]
  constructor
  · rintro ⟨coins, hlen, -, hout⟩
    obtain ⟨p, hhead, hp, hlast⟩ :=
      (atm.toPTM.exists_runPath_toNTM_iff (c := atm.toPTM.toNTM.initCfg input)).mpr
        ⟨coins, hlen, rfl⟩
    exact ⟨⟨p, hhead⟩, hp, hlast ▸ hout⟩
  · rintro ⟨p, hp, hout⟩
    obtain ⟨coins, hlen, hcoins⟩ := (atm.toPTM.exists_runPath_toNTM_iff).mp
      ⟨p.toRunPath, p.head_eq, hp, rfl⟩
    exact ⟨coins, hlen, state_stepCoins_eq_none ht hlen, hcoins ▸ hout⟩

end Existential

/-! ### Deciding problems -/

variable {α : Type}

/-- `atm` decides `A` within `t` relative to the encoding `enc`: on every encoded instance
`enc a`, every computation path of at least `t a` steps ends halted, and `a ∈ A` exactly when
`atm` accepts `enc a`. -/
def DecidesInTime (atm : MultiTapeATM k Bool State) (enc : α ↪ List Bool) (A : Set α)
    (t : α → ℕ) : Prop :=
  ∀ a, atm.toPTM.toNTM.RunsInTime (enc a) (t a) ∧ (a ∈ A ↔ atm.Accepts (enc a))

/-- Some alternating machine with a binary alphabet and finitely many states decides `A` within
`t`. -/
def DecidableInTime (A : Set α) (enc : α ↪ List Bool) (t : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (atm : MultiTapeATM k Bool State),
    atm.DecidesInTime enc A t

/-- Some alternating machine with a binary alphabet and finitely many states decides `A` within a
time bound polynomial in the length of the encoded instance. -/
def DecidableInPolyTime (A : Set α) (enc : α ↪ List Bool) : Prop :=
  ∃ t, MultiTapeTM.PolyBounded (fun a => (enc a).length) t ∧ DecidableInTime A enc t

/-- Time bounds can be increased. -/
theorem DecidesInTime.mono {atm : MultiTapeATM k Bool State} {enc : α ↪ List Bool} {A : Set α}
    {t t' : α → ℕ} (h : atm.DecidesInTime enc A t) (ht : ∀ a, t a ≤ t' a) :
    atm.DecidesInTime enc A t' :=
  fun a => ⟨(h a).1.mono (ht a), (h a).2⟩

/-- Under its time bound, a deciding machine decides by acceptance within `t a` moves. -/
theorem DecidesInTime.mem_iff {atm : MultiTapeATM k Bool State} {enc : α ↪ List Bool}
    {A : Set α} {t : α → ℕ} (h : atm.DecidesInTime enc A t) (a : α) :
    a ∈ A ↔ atm.AcceptsWithin (t a) (atm.toPTM.toNTM.initCfg (enc a)) :=
  (h a).2.trans (accepts_iff_acceptsWithin (h a).1)

end MultiTapeATM

end Turing
