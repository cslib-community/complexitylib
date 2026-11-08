/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.SavitchBridge
import CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch
import CslibFrontier.Computability.Complexity.Classes.Alternation.SpaceGame

/-! # Transfer of `AP = PSPACE` and `APSPACE = EXP` to plain machine definitions

An alternating machine is presented by its initial state, its two moves and its labelling of
universal states. Its nondeterministic machine, its acceptance (the least set of configurations
closed under the halting, existential and universal rules) and its resource bounds are stated on
upstream `Turing.MultiTapeNTM`. The library's `Turing.MultiTapeATM` has exactly these
presentations (`exists_eq`), with the same nondeterministic machine (`toNTM_eq`) and acceptance
(`accepts_iff`), so the classes `AP` and `APSPACE` stated here are the library's.
-/

namespace ComplexityAbstracts.AlternationBridge

open Turing ComplexityTests.Abstracts

/-- The nondeterministic machine of an alternating machine with initial state `start`, moves
`move` and universal states `universal`: at a running configuration it may take either move. -/
def toNTM {k : ℕ} {State : Type} (start : State)
    (move : Bool → State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State) :
    Turing.MultiTapeNTM k Bool State where
  q₀ := start
  Tr q symbol work action := ∃ b, move b q symbol work = action

/-- The alternating acceptance of `input`: the initial configuration lies in every set of
configurations closed under the halting, existential and universal rules. -/
def Accepts {k : ℕ} {State : Type} (start : State)
    (move : Bool → State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)
    (universal : State → Bool) (input : List Bool) : Prop :=
  ∀ S : Set (Turing.Cfg k Bool State input),
    (∀ c, c.state = none → c.output = [true] → c ∈ S) →
    (∀ c q, c.state = some q → universal q = false →
      (∃ d, (toNTM start move).Step c d ∧ d ∈ S) → c ∈ S) →
    (∀ c q, c.state = some q → universal q = true →
      (∀ d, (toNTM start move).Step c d → d ∈ S) → c ∈ S) →
    (toNTM start move).initCfg input ∈ S

/-- The initial state of a library alternating machine. -/
def start {k : ℕ} {State : Type} (atm : MultiTapeATM k Bool State) : State :=
  atm.toPTM.initial

/-- The moves of a library alternating machine. -/
def move {k : ℕ} {State : Type} (atm : MultiTapeATM k Bool State) :
    Bool → State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State :=
  fun b q symbol work => atm.action q symbol work b

/-- The presentation has the library's nondeterministic machine. -/
theorem toNTM_eq {k : ℕ} {State : Type} (atm : MultiTapeATM k Bool State) :
    toNTM (start atm) (move atm) = atm.toPTM.toNTM := by
  change MultiTapeNTM.mk _ _ = MultiTapeNTM.mk _ _
  congr
  funext q symbol work action
  exact propext <| exists_congr fun b =>
    (MultiTapeMachine.Action.emptyOracleEquiv.eq_symm_apply).symm

/-- A step of the library machine is one of its two moves. -/
theorem step_iff {k : ℕ} {State : Type} (atm : MultiTapeATM k Bool State) {input : List Bool}
    {c d : Turing.Cfg k Bool State input} :
    atm.toPTM.toNTM.Step c d ↔ ∃ b, atm.next b c = d :=
  atm.toPTM.step_toNTM_iff

/-- The presentation has the library's acceptance. -/
theorem accepts_iff {k : ℕ} {State : Type} (atm : MultiTapeATM k Bool State)
    (input : List Bool) :
    Accepts (start atm) (move atm) atm.universal input ↔ atm.Accepts input := by
  rw [Accepts, toNTM_eq]
  constructor
  · intro h
    refine h {c | ∃ n, atm.AcceptsWithin n c} (fun c hc hout => ⟨0, hc, hout⟩) ?_ ?_
    · rintro c q hc hq ⟨d, hd, n, hn⟩
      obtain ⟨b, rfl⟩ := (step_iff atm).mp hd
      exact ⟨n + 1, (atm.acceptsWithin_succ_of_existential hc hq).mpr ⟨b, hn⟩⟩
    · intro c q hc hq hall
      obtain ⟨n₀, h₀⟩ := hall _ ((step_iff atm).mpr ⟨false, rfl⟩)
      obtain ⟨n₁, h₁⟩ := hall _ ((step_iff atm).mpr ⟨true, rfl⟩)
      refine ⟨max n₀ n₁ + 1, (atm.acceptsWithin_succ_of_universal hc hq).mpr fun b => ?_⟩
      cases b
      · exact h₀.mono (le_max_left _ _)
      · exact h₁.mono (le_max_right _ _)
  · rintro ⟨n, hn⟩ S hhalt hex hall
    suffices key : ∀ n (c : Turing.Cfg k Bool State input), atm.AcceptsWithin n c → c ∈ S from
      key n _ hn
    intro n
    induction n with
    | zero => exact fun c ⟨hc, hout⟩ => hhalt c hc hout
    | succ n ih =>
      intro c hc
      rcases hs : c.state with _ | q
      · exact hhalt c hs ((atm.acceptsWithin_of_halted hs).mp hc)
      · cases hq : atm.universal q
        · obtain ⟨b, hb⟩ := (atm.acceptsWithin_succ_of_existential hs hq).mp hc
          exact hex c q hs hq ⟨_, (step_iff atm).mpr ⟨b, rfl⟩, ih _ hb⟩
        · have hb := (atm.acceptsWithin_succ_of_universal hs hq).mp hc
          refine hall c q hs hq fun d hd => ?_
          obtain ⟨b, rfl⟩ := (step_iff atm).mp hd
          exact ih _ (hb b)

/-- Every presentation is that of a library alternating machine. -/
theorem exists_eq {k : ℕ} {State : Type} (start₀ : State)
    (move₀ : Bool → State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)
    (universal : State → Bool) :
    ∃ atm : MultiTapeATM k Bool State,
      start atm = start₀ ∧ move atm = move₀ ∧ atm.universal = universal :=
  ⟨⟨⟨start₀, fun q symbol work _ b =>
      MultiTapeMachine.Action.emptyOracleEquiv.symm (move₀ b q symbol work)⟩, universal⟩,
    rfl, rfl, rfl⟩

/-- An alternating machine decides `A` within time `t`: on every instance every computation path
of at least `t a` steps ends halted, and `a ∈ A` exactly when the machine accepts `enc a`. -/
def DecidesInTime {α : Type} {k : ℕ} {State : Type} (start : State)
    (move : Bool → State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)
    (universal : State → Bool) (enc : α ↪ List Bool) (A : Set α) (t : α → ℕ) : Prop :=
  ∀ a, (toNTM start move).RunsInTime (enc a) (t a) ∧
    (a ∈ A ↔ Accepts start move universal (enc a))

/-- An alternating machine decides `A` within space `s`: on every instance every computation
prefix visits at most `s a` work-tape cells, some finite time bounds every computation path, and
`a ∈ A` exactly when the machine accepts `enc a`. -/
def DecidesInSpace {α : Type} {k : ℕ} {State : Type} (start : State)
    (move : Bool → State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)
    (universal : State → Bool) (enc : α ↪ List Bool) (A : Set α) (s : α → ℕ) : Prop :=
  (∀ a, (toNTM start move).RunsInSpace (enc a) (s a) ∧
    (a ∈ A ↔ Accepts start move universal (enc a))) ∧
    ∀ a, ∃ t, (toNTM start move).RunsInTime (enc a) t

/-- Alternating polynomial time. -/
def AP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (start : State)
    (move : Bool → State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)
    (universal : State → Bool) (t : α → ℕ),
    (∃ p : ℕ → ℕ, Cslib.PolynomiallyBounded p ∧ ∀ a, t a ≤ p (enc a).length) ∧
    DecidesInTime start move universal enc A t}

/-- Alternating polynomial space. -/
def APSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (start : State)
    (move : Bool → State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State)
    (universal : State → Bool) (s : α → ℕ),
    (∃ p : ℕ → ℕ, Cslib.PolynomiallyBounded p ∧ ∀ a, s a ≤ p (enc a).length) ∧
    DecidesInSpace start move universal enc A s}

/-- Deterministic exponential time, with any space bound. -/
def EXP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → Bool) (d c₁ c₂ : ℕ) (s : ℕ → ℕ),
    Turing.MultiTapeTM.ComputableInTimeAndSpace f enc SavitchBridge.encBool
      (fun a => c₁ * 2 ^ (enc a).length ^ d + c₂) (fun a => s (enc a).length) ∧
    ∀ a, a ∈ A ↔ f a = true}

theorem ap_eq {α : Type} (enc : α ↪ List Bool) : AP enc = Cslib.Complexity.AP enc := by
  ext A
  constructor
  · rintro ⟨k, State, hfin, start₀, move₀, universal, t, ht, h⟩
    obtain ⟨atm, rfl, rfl, rfl⟩ := exists_eq start₀ move₀ universal
    refine ⟨t, ht, k, State, hfin, atm, fun a => ?_⟩
    rw [← toNTM_eq, ← accepts_iff]
    exact h a
  · rintro ⟨t, ht, k, State, hfin, atm, h⟩
    refine ⟨k, State, hfin, start atm, move atm, atm.universal, t, ht, fun a => ?_⟩
    rw [toNTM_eq, accepts_iff]
    exact h a

theorem apspace_eq {α : Type} (enc : α ↪ List Bool) :
    APSPACE enc = Cslib.Complexity.APSPACE enc := by
  ext A
  constructor
  · rintro ⟨k, State, hfin, start₀, move₀, universal, s, hs, h⟩
    obtain ⟨atm, rfl, rfl, rfl⟩ := exists_eq start₀ move₀ universal
    refine ⟨k, State, hfin, atm, s, hs, fun a => ?_, fun a => ?_⟩
    · rw [← toNTM_eq, ← accepts_iff]
      exact h.1 a
    · rw [← toNTM_eq]
      exact h.2 a
  · rintro ⟨k, State, hfin, atm, s, hs, h⟩
    refine ⟨k, State, hfin, start atm, move atm, atm.universal, s, hs, fun a => ?_, fun a => ?_⟩
    · rw [toNTM_eq, accepts_iff]
      exact h.1 a
    · rw [toNTM_eq]
      exact h.2 a

theorem exp_eq {α : Type} (enc : α ↪ List Bool) : EXP enc = Cslib.Complexity.EXP enc := by
  ext A
  rw [Cslib.Complexity.mem_EXP_iff]
  constructor
  · rintro ⟨f, d, c₁, c₂, s, hf, hA⟩
    have hfA : f = Turing.MultiTapeTM.indicator A := by
      funext a
      cases hfa : f a <;> simp [Turing.MultiTapeTM.indicator, hA a, hfa]
    subst hfA
    exact ⟨d, c₁, c₂, s, hf⟩
  · rintro ⟨d, c₁, c₂, s, h⟩
    refine ⟨Turing.MultiTapeTM.indicator A, d, c₁, c₂, s, h, fun a => ?_⟩
    by_cases ha : a ∈ A <;> simp [Turing.MultiTapeTM.indicator, ha]

theorem pspace_eq {α : Type} (enc : α ↪ List Bool) :
    SavitchBridge.PSPACE enc = Cslib.Complexity.PSPACE enc :=
  Set.ext fun _ => TQBFBridge.mem_PSPACE_iff

theorem ap_eq_pspace {α : Type} (enc : α ↪ List Bool) :
    AP enc = SavitchBridge.PSPACE enc := by
  rw [ap_eq, pspace_eq]
  exact Cslib.Complexity.AP_eq_PSPACE

theorem apspace_eq_exp {α : Type} (enc : α ↪ List Bool) : APSPACE enc = EXP enc := by
  rw [apspace_eq, exp_eq]
  exact Cslib.Complexity.APSPACE_eq_EXP

end ComplexityAbstracts.AlternationBridge
