/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.Check
import CslibFrontierAbstracts.AlternationBridge

/-! # Chandra–Kozen–Stockmeyer: alternating time is space, alternating space is exponential time

An alternating machine generalizes a nondeterministic one. Its states are labelled existential or
universal. An existential configuration accepts when one of its moves leads to acceptance, as for
nondeterminism; a universal configuration accepts only when all of its moves do. Chandra, Kozen and
Stockmeyer showed that alternation trades one exponential between time and space: alternating
polynomial time is deterministic polynomial space, and alternating polynomial space is
deterministic exponential time. A polynomial-time alternating computation is a game of polynomially
many moves with a polynomial-time winning condition, which polynomial space evaluates through
quantified Boolean formulas. Conversely, Savitch's midpoint game decides a polynomial-space
computation in alternating polynomial time: the existential player names a midpoint configuration
and the universal player chooses a half. A polynomial-space alternating machine has exponentially
many configurations, and marking the accepting ones bottom-up takes exponential time. Conversely,
an alternating machine decides an exponential-time computation by the circuit-value game on its
tableau, keeping only a polynomial-length claim about one gate.

Each problem has one fixed alternating machine with a binary alphabet, finitely many states and
any number of work tapes, run on the binary encoding `enc a` of an instance `a`, for an arbitrary
injective encoding `enc`. As in Arora and Barak, the machine has two moves, two transition
functions applied to its state and the symbols under its heads. A move from an existential state is
chosen by the existential player, and from a universal state by the universal player. A halted
configuration accepts when its output is exactly `[true]`. Acceptance is a least fixed point, so an
infinite branch never makes a configuration accept. Every branch must halt: a time bound `t` asks
every computation path of at least `t` steps to end halted, and a space bound asks every
computation prefix to visit at most `s` work-tape cells, with some finite time bounding all paths.
Read-only input and write-only output are not charged. `PSPACE` and `EXP` are deterministic and
total.

The third equality of the source, `AL = P` for alternating logarithmic space, is not stated: the
library proves `AL ⊆ P`, and `P ⊆ AL` remains open work.

A reader only needs to inspect the definitions and theorem statements below. Lean checks the
transfer to the library's alternating machines through the bridge, and `#check_abstract` audits the
public dependencies.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*,
  Section 3][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 10.3; Theorem 10.21 for
  `AP = PSPACE`][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 5.3][AroraBarak09]
-/

namespace ComplexityAbstracts.AlternationAbstract

/-! ## Alternating machines -/

/-- An alternating multi-tape machine with `k` work tapes, a binary alphabet and control states
`State`. At a running configuration in state `q`, move `b` performs the action
`move b q symbol work`, where `symbol` is the input symbol under the input head and `work i` the
symbol under the head of work tape `i` (`none` is a blank). An action (upstream `Turing.Action`)
moves the input head, writes to and moves each work-tape head, appends at most one output symbol
and sets the next state; next state `none` halts. -/
structure ATM (k : ℕ) (State : Type) where
  /-- The initial state. -/
  start : State
  /-- The two moves, indexed by `Bool`. -/
  move : Bool → State → Option Bool → (Fin k → Option Bool) → Turing.Action k Bool State
  /-- Whether a state is universal; the other states are existential. -/
  universal : State → Bool

/-- The nondeterministic machine of an alternating machine (upstream `Turing.MultiTapeNTM`): at a
running configuration it may take either move, and a halted configuration steps only to itself.
Its computation paths, time bounds (`Turing.MultiTapeNTM.RunsInTime`) and space bounds
(`Turing.MultiTapeNTM.RunsInSpace`) are those of the alternating machine. -/
def ATM.toNTM {k : ℕ} {State : Type} (M : ATM k State) : Turing.MultiTapeNTM k Bool State where
  q₀ := M.start
  Tr q symbol work action := ∃ b, M.move b q symbol work = action

/-- **Acceptance** is the least fixed point of the labelling: the initial configuration lies in
every set `S` of configurations that contains the halted configurations with output `[true]`,
every existential configuration with a successor in `S`, and every universal configuration whose
successors all lie in `S`. -/
def ATM.Accepts {k : ℕ} {State : Type} (M : ATM k State) (input : List Bool) : Prop :=
  ∀ S : Set (Turing.Cfg k Bool State input),
    (∀ c, c.state = none → c.output = [true] → c ∈ S) →
    (∀ c q, c.state = some q → M.universal q = false →
      (∃ d, M.toNTM.Step c d ∧ d ∈ S) → c ∈ S) →
    (∀ c q, c.state = some q → M.universal q = true →
      (∀ d, M.toNTM.Step c d → d ∈ S) → c ∈ S) →
    M.toNTM.initCfg input ∈ S

/-! ## Alternating time and space -/

/-- `M` decides `A` within time `t`: on every instance `a`, every computation path of at least
`t a` steps ends halted, and `a ∈ A` exactly when `M` accepts `enc a`. -/
def ATM.DecidesInTime {α : Type} {k : ℕ} {State : Type} (M : ATM k State) (enc : α ↪ List Bool)
    (A : Set α) (t : α → ℕ) : Prop :=
  ∀ a, M.toNTM.RunsInTime (enc a) (t a) ∧ (a ∈ A ↔ M.Accepts (enc a))

/-- `M` decides `A` within space `s`: on every instance `a`, every computation prefix visits at
most `s a` work-tape cells, `a ∈ A` exactly when `M` accepts `enc a`, and some finite time bounds
every computation path. -/
def ATM.DecidesInSpace {α : Type} {k : ℕ} {State : Type} (M : ATM k State)
    (enc : α ↪ List Bool) (A : Set α) (s : α → ℕ) : Prop :=
  (∀ a, M.toNTM.RunsInSpace (enc a) (s a) ∧ (a ∈ A ↔ M.Accepts (enc a))) ∧
    ∀ a, ∃ t, M.toNTM.RunsInTime (enc a) t

/-- **Alternating polynomial time**: one finite-state alternating machine decides the problem
within a time bound that is at most a polynomially bounded function of the encoded length. -/
def AP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : ATM k State) (t : α → ℕ),
    (∃ p : ℕ → ℕ, Cslib.PolynomiallyBounded p ∧ ∀ a, t a ≤ p (enc a).length) ∧
    M.DecidesInTime enc A t}

/-- **Alternating polynomial space**: one finite-state alternating machine decides the problem
within a space bound that is at most a polynomially bounded function of the encoded length, every
branch halting. -/
def APSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : ATM k State) (s : α → ℕ),
    (∃ p : ℕ → ℕ, Cslib.PolynomiallyBounded p ∧ ∀ a, s a ≤ p (enc a).length) ∧
    M.DecidesInSpace enc A s}

/-! ## Deterministic space and time -/

/-- A Boolean is encoded by a single bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- **Polynomial space**: one total deterministic machine (upstream
`Turing.MultiTapeTM.ComputableInTimeAndSpace`: a binary multi-tape machine with finitely many
states) computes the indicator of the problem with work space polynomially bounded in the encoded
length. There is no time restriction. -/
def PSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → Bool) (t : α → ℕ) (s : ℕ → ℕ),
    Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpace f enc encBool t (fun a => s (enc a).length) ∧
    ∀ a, a ∈ A ↔ f a = true}

/-- **Exponential time**: one total deterministic machine computes the indicator of the problem
within time `c₁ * 2 ^ n ^ d + c₂` on instances of encoded length `n`, with any space bound. -/
def EXP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → Bool) (d c₁ c₂ : ℕ) (s : ℕ → ℕ),
    Turing.MultiTapeTM.ComputableInTimeAndSpace f enc encBool
      (fun a => c₁ * 2 ^ (enc a).length ^ d + c₂) (fun a => s (enc a).length) ∧
    ∀ a, a ∈ A ↔ f a = true}

/-! ## Main results -/

/-- **Theorem (Chandra–Kozen–Stockmeyer):** alternating polynomial time is polynomial space, for
every injective binary encoding of instances ([Sipser, Theorem 10.21][Sipser2013] for polynomial
bounds). -/
theorem ap_eq_pspace {α : Type} (enc : α ↪ List Bool) : AP enc = PSPACE enc := by
  refine Eq.trans ?_ (AlternationBridge.ap_eq_pspace enc)
  ext A
  constructor
  · rintro ⟨k, State, hfin, M, t, ht, h⟩
    exact ⟨k, State, hfin, M.start, M.move, M.universal, t, ht, h⟩
  · rintro ⟨k, State, hfin, start, move, universal, t, ht, h⟩
    exact ⟨k, State, hfin, ⟨start, move, universal⟩, t, ht, h⟩

/-- **Theorem (Chandra–Kozen–Stockmeyer):** alternating polynomial space is exponential time, for
every injective binary encoding of instances. -/
theorem apspace_eq_exp {α : Type} (enc : α ↪ List Bool) : APSPACE enc = EXP enc := by
  refine Eq.trans ?_ (AlternationBridge.apspace_eq_exp enc)
  ext A
  constructor
  · rintro ⟨k, State, hfin, M, s, hs, h⟩
    exact ⟨k, State, hfin, M.start, M.move, M.universal, s, hs, h⟩
  · rintro ⟨k, State, hfin, start, move, universal, s, hs, h⟩
    exact ⟨k, State, hfin, ⟨start, move, universal⟩, s, hs, h⟩

/--
info: abstract audit passed for `CslibFrontierAbstracts.AlternationAbstract`:
30 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.AlternationAbstract

end ComplexityAbstracts.AlternationAbstract
