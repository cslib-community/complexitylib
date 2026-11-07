/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Logic.Function.DependsOn
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The LOCAL model on oriented cycles

Deterministic synchronous distributed algorithms in the LOCAL model of [Linial][Linial1992] on
consistently oriented cycles. The nodes of the oriented `n`-cycle are `ZMod n`; node `v` has
predecessor `v - 1` and successor `v + 1`. For `n = 0` the graph `ZMod 0 = ℤ` is the infinite
oriented path. Each node receives an input, for instance a unique identifier or an initial colour.

In every round each node exchanges messages with its two neighbours and updates its state.
Messages are unbounded, so an `Algorithm` simply sends its whole state. A `MessageAlgorithm`
with explicit messages reduces to this form (`MessageAlgorithm.toAlgorithm_state`). The round
number is common knowledge. Algorithms are non-uniform: one may be chosen for each cycle length
`n`, so every node knows `n`.

The equivalent *view* formulation: after `r` rounds the state of a node is a function of the
inputs at distance at most `r` (`Algorithm.state_eq_viewState`), so an `r`-round algorithm computes
a `LocalRule` of radius `r` (`Algorithm.run_eq_apply`). Conversely every rule of radius `r` is
computed in `r` rounds by flooding (`LocalRule.toAlgorithm_run`). Lower bounds can thus be proved
for rules and transferred to algorithms. `LocalRule.andThen` runs a rule and then an algorithm on
its outputs.

Identifiers are natural numbers. The standard convention of identifiers from `{1, …, n}` is the
convention `{0, …, n - 1}` used by `Algorithm.ColorsCycle`, shifted by one.

## Main definitions

* `Cslib.Distributed.OrientedCycle.Algorithm`, `Algorithm.state`, `Algorithm.run`: algorithms and
  their executions.
* `Cslib.Distributed.OrientedCycle.MessageAlgorithm`: algorithms with explicit messages.
* `Cslib.Distributed.OrientedCycle.LocalRule`: rules of radius `r` on input windows.
* `Cslib.Distributed.OrientedCycle.LocalRule.andThen`: a rule followed by an algorithm.
* `Cslib.Distributed.OrientedCycle.IsProperColoring`: proper colourings of the oriented cycle.
* `Cslib.Distributed.OrientedCycle.Algorithm.ColorsCycle`: `A` properly `c`-colours every oriented
  `n`-cycle with identifiers `{0, …, n - 1}` in `t` rounds.

## Main results

* `Cslib.Distributed.OrientedCycle.Algorithm.state_eq_viewState`: locality of `r`-round states.
* `Cslib.Distributed.OrientedCycle.Algorithm.run_eq_apply`: `r` rounds compute a radius-`r` rule.
* `Cslib.Distributed.OrientedCycle.LocalRule.toAlgorithm_run`: every radius-`r` rule is computed
  in `r` rounds.
* `Cslib.Distributed.OrientedCycle.LocalRule.andThen_run`: composition of a rule and an algorithm.
* `Cslib.Distributed.OrientedCycle.MessageAlgorithm.toAlgorithm_state`: message passing as state
  exchange.

## References

* [N. Linial, *Locality in distributed graph algorithms*][Linial1992]
-/

public section

namespace Cslib.Distributed.OrientedCycle

/-- A deterministic synchronous algorithm in the LOCAL model on consistently oriented cycles.

Every node starts in state `init x` from its input `x` (an identifier or an initial colour). In
round `r + 1` every node exchanges its whole state with its two neighbours and moves to
`step r p s q`, where `s` is its own state, `p` that of its predecessor and `q` that of its
successor. After the last round a node outputs `output s`. Messages and local computation are
unbounded, the round number is common knowledge, and every node knows the cycle length, since an
algorithm may be chosen separately for each `n`. -/
structure Algorithm (I State O : Type*) where
  /-- The state of a node with input `x` before the first round. -/
  init : I → State
  /-- The new state in round `r + 1` from the predecessor's, own and successor's states. -/
  step : ℕ → State → State → State → State
  /-- The output of a node in a given state. -/
  output : State → O

namespace Algorithm

variable {I S O : Type*} (A : Algorithm I S O) {n : ℕ}

/-- The state of node `v` of the oriented `n`-cycle `ZMod n` after `r` rounds on input `x`.
For `n = 0` the graph `ZMod 0 = ℤ` is the infinite oriented path. -/
@[expose] def state (x : ZMod n → I) : ℕ → ZMod n → S
  | 0, v => A.init (x v)
  | r + 1, v => A.step r (state x r (v - 1)) (state x r v) (state x r (v + 1))

/-- The output of node `v` after `r` rounds. -/
@[expose] def run (x : ZMod n → I) (r : ℕ) (v : ZMod n) : O := A.output (A.state x r v)

@[simp] theorem state_zero (x : ZMod n → I) (v : ZMod n) : A.state x 0 v = A.init (x v) := rfl

theorem state_succ (x : ZMod n → I) (r : ℕ) (v : ZMod n) :
    A.state x (r + 1) v = A.step r (A.state x r (v - 1)) (A.state x r v) (A.state x r (v + 1)) :=
  rfl

/-- Post-processing the output of an algorithm by `g`. -/
def mapOutput {O' : Type*} (g : O → O') : Algorithm I S O' where
  init := A.init
  step := A.step
  output := g ∘ A.output

@[simp] theorem mapOutput_state {O' : Type*} (g : O → O') (x : ZMod n → I) (r : ℕ) :
    (A.mapOutput g).state x r = A.state x r := by
  funext v
  induction r generalizing v with
  | zero => rfl
  | succ r ih => simp only [state_succ, ih]; rfl

@[simp] theorem mapOutput_run {O' : Type*} (g : O → O') (x : ZMod n → I) (r : ℕ) (v : ZMod n) :
    (A.mapOutput g).run x r v = g (A.run x r v) := by
  simp only [run, mapOutput_state]
  rfl

end Algorithm

/-- A message-passing algorithm on oriented cycles: in round `r + 1` every node sends
`toPred r s` to its predecessor and `toSucc r s` to its successor, and then updates its state from
the message `m₁` of its predecessor and the message `m₂` of its successor. -/
structure MessageAlgorithm (I State M O : Type*) where
  /-- The initial state. -/
  init : I → State
  /-- The message sent to the predecessor. -/
  toPred : ℕ → State → M
  /-- The message sent to the successor. -/
  toSucc : ℕ → State → M
  /-- The new state from the old state, the predecessor's message and the successor's message. -/
  receive : ℕ → State → M → M → State
  /-- The output. -/
  output : State → O

namespace MessageAlgorithm

variable {I S M O : Type*} (A : MessageAlgorithm I S M O) {n : ℕ}

/-- The state of node `v` after `r` rounds of message passing. -/
@[expose] def state (x : ZMod n → I) : ℕ → ZMod n → S
  | 0, v => A.init (x v)
  | r + 1, v =>
    A.receive r (state x r v) (A.toSucc r (state x r (v - 1)))
      (A.toPred r (state x r (v + 1)))

/-- A message-passing algorithm as a state-exchange `Algorithm`: a node can compute the messages
its neighbours would send from their states. -/
@[expose] def toAlgorithm : Algorithm I S O where
  init := A.init
  step r p s q := A.receive r s (A.toSucc r p) (A.toPred r q)
  output := A.output

/-- The state-exchange simulation of a message-passing algorithm goes through the same states. -/
theorem toAlgorithm_state (x : ZMod n → I) (r : ℕ) (v : ZMod n) :
    A.toAlgorithm.state x r v = A.state x r v := by
  induction r generalizing v with
  | zero => rfl
  | succ r ih =>
    rw [Algorithm.state_succ, ih, ih, ih]
    rfl

end MessageAlgorithm

/-- The inputs seen from node `v` at offsets `j : ℤ`: the window `j ↦ x (v + j)`. On the cycle this
is the input along the universal cover, the oriented path `ℤ`, viewed from `v`. -/
@[expose] def window {I : Type*} {n : ℕ} (x : ZMod n → I) (v : ZMod n) : ℤ → I :=
  fun j => x (v + j)

/-- A rule of radius `r`: a function of input windows `ℤ → I` that only depends on the offsets
`-r, …, r`. Applied to every node of a cycle (`LocalRule.apply`) it computes the output of an
`r`-round LOCAL algorithm, and conversely (`Algorithm.toLocalRule`, `LocalRule.toAlgorithm`). -/
structure LocalRule (I O : Type*) (r : ℕ) where
  /-- The output from a window of inputs. -/
  toFun : (ℤ → I) → O
  /-- Only the offsets `-r, …, r` matter. -/
  dependsOn : DependsOn toFun (Set.Icc (-(r : ℤ)) r)

namespace LocalRule

variable {I O : Type*} {r : ℕ}

/-- The output of a local rule at node `v` of the oriented `n`-cycle. -/
@[expose] def apply (F : LocalRule I O r) {n : ℕ} (x : ZMod n → I) (v : ZMod n) : O :=
  F.toFun (window x v)

theorem toFun_congr (F : LocalRule I O r) {w w' : ℤ → I}
    (h : ∀ j : ℤ, -(r : ℤ) ≤ j → j ≤ r → w j = w' j) : F.toFun w = F.toFun w' :=
  F.dependsOn fun j hj => h j hj.1 hj.2

end LocalRule

namespace Algorithm

variable {I S O : Type*} (A : Algorithm I S O)

/-- The state after `r` rounds at node `0` of the infinite oriented path, as a function of the
input window. -/
@[expose] def viewState : ℕ → (ℤ → I) → S
  | 0, w => A.init (w 0)
  | r + 1, w =>
    A.step r (viewState r fun j => w (j - 1)) (viewState r w)
      (viewState r fun j => w (j + 1))

/-- **Locality.** The state of a node after `r` rounds is determined by its radius-`r` window. -/
theorem state_eq_viewState {n : ℕ} (x : ZMod n → I) (r : ℕ) (v : ZMod n) :
    A.state x r v = A.viewState r (window x v) := by
  induction r generalizing v with
  | zero => simp [state, viewState, window]
  | succ r ih =>
    rw [state_succ, viewState, ih, ih, ih]
    congr 2 <;> funext j <;> simp only [window] <;> congr 1 <;> push_cast <;> ring

/-- After `r` rounds, the state only depends on the inputs at offsets `-r, …, r`. -/
theorem viewState_dependsOn (r : ℕ) : DependsOn (A.viewState r) (Set.Icc (-(r : ℤ)) r) := by
  induction r with
  | zero =>
    intro w w' h
    simp only [viewState]
    rw [h 0 (by simp)]
  | succ r ih =>
    intro w w' h
    simp only [viewState]
    have h' : ∀ j ∈ Set.Icc (-(r + 1 : ℕ) : ℤ) (r + 1 : ℕ), w j = w' j := h
    congr 1
    · exact ih fun j hj => h' _ (by constructor <;> push_cast <;> linarith [hj.1, hj.2])
    · exact ih fun j hj => h' _ (by constructor <;> push_cast <;> linarith [hj.1, hj.2])
    · exact ih fun j hj => h' _ (by constructor <;> push_cast <;> linarith [hj.1, hj.2])

/-- The radius-`r` rule computed by `r` rounds of an algorithm. -/
@[expose] def toLocalRule (r : ℕ) : LocalRule I O r where
  toFun w := A.output (A.viewState r w)
  dependsOn _ _ h := congrArg A.output (A.viewState_dependsOn r h)

/-- The output after `r` rounds is the radius-`r` rule `A.toLocalRule r` applied at every node. -/
theorem run_eq_apply {n : ℕ} (x : ZMod n → I) (r : ℕ) (v : ZMod n) :
    A.run x r v = (A.toLocalRule r).apply x v := by
  simp only [run, LocalRule.apply, toLocalRule, state_eq_viewState]

end Algorithm

namespace LocalRule

variable {I O : Type*} {r : ℕ}

/-- The full-information algorithm for a local rule: every node floods the window it has learnt
(its state is a window, correct on offsets `-s, …, s` after `s` rounds) and finally applies the
rule. -/
@[expose] def toAlgorithm (F : LocalRule I O r) : Algorithm I (ℤ → I) O where
  init x := fun _ => x
  step _ p s q := fun j => if j < 0 then p (j + 1) else if j = 0 then s 0 else q (j - 1)
  output := F.toFun

private theorem toAlgorithm_state_eq (F : LocalRule I O r) {n : ℕ} (x : ZMod n → I) (s : ℕ)
    (v : ZMod n) (j : ℤ) (hj₁ : -(s : ℤ) ≤ j) (hj₂ : j ≤ s) :
    F.toAlgorithm.state x s v j = x (v + j) := by
  induction s generalizing v j with
  | zero =>
    have : j = 0 := by omega
    subst this
    simp [toAlgorithm]
  | succ s ih =>
    have hstep : ∀ r p s q, F.toAlgorithm.step r p s q =
        fun j => if j < 0 then p (j + 1) else if j = 0 then s 0 else q (j - 1) :=
      fun _ _ _ _ => rfl
    simp only [Algorithm.state_succ, hstep]
    split_ifs with h0 h1
    · rw [ih _ _ (by omega) (by omega)]
      congr 1; push_cast; ring
    · subst h1
      rw [ih _ _ (by omega) (by omega)]
    · rw [ih _ _ (by omega) (by omega)]
      congr 1; push_cast; ring

/-- **Full-information simulation.** Every rule of radius `r` is computed by an `r`-round
algorithm. -/
theorem toAlgorithm_run (F : LocalRule I O r) {n : ℕ} (x : ZMod n → I) (v : ZMod n) :
    F.toAlgorithm.run x r v = F.apply x v :=
  F.toFun_congr fun j hj₁ hj₂ => F.toAlgorithm_state_eq x r v j hj₁ hj₂

/-- Running a rule `F` of radius `r` and then an algorithm `B` on its outputs: for `r` rounds the
nodes flood windows as in `F.toAlgorithm` and keep `B` initialised from `F` on the current window;
from round `r` on they run `B`. -/
@[expose] def andThen {S' O' : Type*} (F : LocalRule I O r) (B : Algorithm O S' O') :
    Algorithm I ((ℤ → I) × S') O' where
  init x := (fun _ => x, B.init (F.toFun fun _ => x))
  step k p s q :=
    if k < r then
      (F.toAlgorithm.step k p.1 s.1 q.1, B.init (F.toFun (F.toAlgorithm.step k p.1 s.1 q.1)))
    else (s.1, B.step (k - r) p.2 s.2 q.2)
  output s := B.output s.2

private theorem andThen_state_le {S' O' : Type*} (F : LocalRule I O r) (B : Algorithm O S' O')
    {n : ℕ} (x : ZMod n → I) {s : ℕ} (hs : s ≤ r) (v : ZMod n) :
    (F.andThen B).state x s v =
      (F.toAlgorithm.state x s v, B.init (F.toFun (F.toAlgorithm.state x s v))) := by
  induction s generalizing v with
  | zero => rfl
  | succ s ih =>
    have hstep : ∀ p q : (ℤ → I) × S', ∀ c : (ℤ → I) × S', (F.andThen B).step s p c q =
        (F.toAlgorithm.step s p.1 c.1 q.1, B.init (F.toFun (F.toAlgorithm.step s p.1 c.1 q.1))) :=
      fun p q c => by simp only [andThen, show s < r by omega, ↓reduceIte]
    rw [Algorithm.state_succ, hstep, ih (by omega), ih (by omega), ih (by omega),
      Algorithm.state_succ]

/-- **Composition.** Running `F.andThen B` for `r + t` rounds is running `B` for `t` rounds on the
outputs of `F`. -/
theorem andThen_run {S' O' : Type*} (F : LocalRule I O r) (B : Algorithm O S' O') {n : ℕ}
    (x : ZMod n → I) (t : ℕ) (v : ZMod n) :
    (F.andThen B).run x (r + t) v = B.run (F.apply x) t v := by
  suffices h : ∀ v, ((F.andThen B).state x (r + t) v).2 = B.state (F.apply x) t v from
    congrArg B.output (h v)
  induction t with
  | zero =>
    intro v
    rw [Nat.add_zero, andThen_state_le F B x le_rfl]
    exact congrArg B.init (F.toAlgorithm_run x v)
  | succ t ih =>
    intro v
    have hstep : ∀ p q c : (ℤ → I) × S', (F.andThen B).step (r + t) p c q =
        (c.1, B.step t p.2 c.2 q.2) :=
      fun p q c => by simp only [andThen, show ¬r + t < r by omega, ↓reduceIte,
        Nat.add_sub_cancel_left]
    rw [← Nat.add_assoc, Algorithm.state_succ, hstep, ih, ih, ih, Algorithm.state_succ]

end LocalRule

/-- A colouring `c` of the oriented `n`-cycle is proper if every node and its successor receive
different colours. -/
@[expose] def IsProperColoring {n : ℕ} {C : Type*} (c : ZMod n → C) : Prop :=
  ∀ v : ZMod n, c v ≠ c (v + 1)

instance {n : ℕ} [NeZero n] {C : Type*} [DecidableEq C] (c : ZMod n → C) :
    Decidable (IsProperColoring c) :=
  inferInstanceAs (Decidable (∀ v : ZMod n, c v ≠ c (v + 1)))

/-- Distinct identifiers form a proper colouring, except on the one-node cycle, whose only node is
its own successor. -/
theorem IsProperColoring.of_injective {n : ℕ} {C : Type*} {c : ZMod n → C}
    (hc : Function.Injective c) (hn : n ≠ 1) : IsProperColoring c := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.2 hn
  intro v h
  have h1 : (1 : ZMod n) = 0 := by linear_combination (hc h).symm
  exact one_ne_zero h1

/-- After `t` rounds, `A` properly colours every oriented `n`-cycle whose nodes carry distinct
identifiers from `{0, …, n - 1}`, with colours `0, …, c - 1`. -/
@[expose] def Algorithm.ColorsCycle {S : Type*} (A : Algorithm ℕ S ℕ) (n t c : ℕ) : Prop :=
  ∀ x : ZMod n → ℕ, Function.Injective x → (∀ v, x v < n) →
    IsProperColoring (A.run x t) ∧ ∀ v, A.run x t v < c

end Cslib.Distributed.OrientedCycle
