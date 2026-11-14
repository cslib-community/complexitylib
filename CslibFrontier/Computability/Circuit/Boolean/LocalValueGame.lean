/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Boolean.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.WordGame

/-!
# Value queries through local Boolean gate access

A decoder supplies the operation and child addresses of one Boolean gate. The value game keeps
only an address and a claimed bit. It follows one child at each move, using universal choices
for a true conjunction or false disjunction. Constants terminate immediately.

This is a semantic interface to local gate access, not a free-oracle machine model. Native
implementations must separately implement the encoded update and charge its running time.
The rank in the correctness and termination theorems is proof data, not a table computed by
the evaluator. It can be circuit depth rather than circuit size.
-/

public section

namespace Cslib.Circuits.Boolean.LocalValueGame

open Turing.MultiTapeATM.WordGame

/-- Local access to a Boolean gate. Negation reads child `false`; constants ignore children. -/
structure Decoder (α : Type) where
  /-- The operation of the addressed gate. -/
  op : α → Op
  /-- The two child addresses, selected by one bit. -/
  child : α → Bool → α

/-- A query asks whether one addressed gate carries the stated bit. -/
structure Claim (α : Type) where
  /-- The addressed gate. -/
  wire : α
  /-- The stated output bit. -/
  value : Bool
  deriving DecidableEq, Fintype

variable {α : Type} (D : Decoder α) (encC : Claim α ↪ List Bool)

/-- The local equation defining the value of a decoded gate. -/
@[expose] def Decoder.eval (value : α → Bool) (a : α) : Bool :=
  match D.op a with
  | .const b => b
  | .not => !value (D.child a false)
  | .and => value (D.child a false) && value (D.child a true)
  | .or => value (D.child a false) || value (D.child a true)

/-- Local evaluation is the ordinary Boolean interpretation of the operation. -/
theorem Decoder.eval_eq_interpretation (value : α → Bool) (a : α) :
    D.eval value a = interpretation (D.op a)
      (fun i => value (D.child a (i.val != 0))) := by
  unfold Decoder.eval
  generalize D.op a = op
  cases op <;> rfl

/-- A rank decreases along every child actually used by an operation. -/
@[expose] def Decoder.Descends (rank : α → ℕ) : Prop :=
  ∀ a b, match D.op a with
    | .const _ => True
    | .not => rank (D.child a false) < rank a
    | .and | .or => rank (D.child a b) < rank a

/-- The player is universal exactly at true conjunctions and false disjunctions. -/
@[expose] def player (c : Claim α) : Bool :=
  match D.op c.wire with
  | .and => c.value
  | .or => !c.value
  | _ => false

/-- Negation flips the claimed bit; a binary gate keeps it and selects one child. -/
@[expose] def next (c : Claim α) (b : Bool) : Claim α :=
  match D.op c.wire with
  | .not => ⟨D.child c.wire false, !c.value⟩
  | _ => ⟨D.child c.wire b, c.value⟩

/-- A constant query is terminal. Other queries store player, move cell, and encoded claim. -/
@[expose] def position (c : Claim α) : List Bool :=
  match D.op c.wire with
  | .const b => if b == c.value then [true] else []
  | _ => player D c :: false :: encC c

open scoped Classical in
/-- Decode the current claim and follow the selected child; malformed words reject. -/
noncomputable def update (w : List Bool) : List Bool :=
  match w with
  | _ :: b :: r =>
    if h : ∃ c, encC c = r then position D encC (next D h.choose b) else []
  | _ => []

open scoped Classical in
/-- Decode a proof-only potential from a nonterminal query; terminal and malformed words have
potential zero. Computing this function is not part of the value evaluator. -/
noncomputable def potential (rank : α → ℕ) (w : List Bool) : ℕ :=
  match w with
  | _ :: _ :: r => if h : ∃ c, encC c = r then rank h.choose.wire else 0
  | _ => 0

variable {D encC}

/-- On an encoded claim the update performs precisely one local move. -/
theorem update_cons (c : Claim α) (u b : Bool) :
    update D encC (u :: b :: encC c) = position D encC (next D c b) := by
  have h : ∃ c', encC c' = encC c := ⟨c, rfl⟩
  simp only [update, h, ↓reduceDIte]
  rw [encC.injective h.choose_spec]

/-- The proof-only potential of an encoded nonterminal query is its address rank. -/
theorem potential_cons (rank : α → ℕ) (c : Claim α) (u b : Bool) :
    potential encC rank (u :: b :: encC c) = rank c.wire := by
  have h : ∃ c', encC c' = encC c := ⟨c, rfl⟩
  simp only [potential, h, ↓reduceDIte]
  rw [encC.injective h.choose_spec]

/-- Terminal queries cost no remaining moves; other positions keep the address potential. -/
theorem potential_position_le (rank : α → ℕ) (c : Claim α) :
    potential encC rank (position D encC c) ≤ rank c.wire := by
  cases ho : D.op c.wire with
  | const b => simp only [position, ho]; split <;> exact Nat.zero_le _
  | not | and | or => simp only [position, ho, potential_cons, le_refl]

/-- A nonterminal position retains the encoded claim. -/
theorem position_eq_cons {c : Claim α} {u x : Bool} {r : List Bool}
    (h : position D encC c = u :: x :: r) :
    (∀ b, D.op c.wire ≠ .const b) ∧ r = encC c := by
  cases ho : D.op c.wire with
  | const b => simp only [position, ho] at h; split at h <;> simp at h
  | not | and | or =>
    simp only [position, ho, List.cons.injEq] at h
    exact ⟨by intro b; simp, h.2.2.symm⟩

/-- Every move from a nonconstant gate decreases the given rank. -/
theorem rank_next_lt {rank : α → ℕ} (hd : D.Descends rank) (c : Claim α)
    (hc : ∀ b, D.op c.wire ≠ .const b) (b : Bool) :
    rank (next D c b).wire < rank c.wire := by
  have h := hd c.wire b
  cases ho : D.op c.wire <;> simp_all [next, Decoder.Descends]

/-- A constant query is won precisely when the claimed bit agrees with the constant. -/
theorem wins_position_const (c : Claim α) (b : Bool) (h : D.op c.wire = .const b) :
    Wins (update D encC) (position D encC c) ↔ b = c.value := by
  simp only [position, h]
  cases b <;> cases c.value <;> simp [not_wins_nil, wins_singleton_iff]

/-- At nonconstant gates the next claim is selected by the current player. -/
theorem wins_position_nonconst (c : Claim α) (hc : ∀ b, D.op c.wire ≠ .const b) :
    Wins (update D encC) (position D encC c) ↔
      if player D c then ∀ b, Wins (update D encC) (position D encC (next D c b))
      else ∃ b, Wins (update D encC) (position D encC (next D c b)) := by
  have hp : position D encC c = player D c :: false :: encC c := by
    cases ho : D.op c.wire <;> simp_all [position]
  rw [hp]
  cases player D c <;>
    simp [wins_false_cons_cons_iff, wins_true_cons_cons_iff, update_cons]

/-- Local semantic equations and decreasing rank suffice for correctness of every query. -/
theorem wins_position_iff {rank : α → ℕ} (hd : D.Descends rank) (value : α → Bool)
    (hv : ∀ a, value a = D.eval value a) (c : Claim α) :
    Wins (update D encC) (position D encC c) ↔ value c.wire = c.value := by
  suffices h : ∀ n (c : Claim α), rank c.wire = n →
      (Wins (update D encC) (position D encC c) ↔ value c.wire = c.value) from
    h _ c rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro c hn
    cases ho : D.op c.wire with
    | const b =>
      rw [wins_position_const c b ho, hv c.wire]
      simp [Decoder.eval, ho]
    | not | and | or =>
      have hc : ∀ b, D.op c.wire ≠ .const b := by intro b; simp [ho]
      rw [wins_position_nonconst c hc]
      have hi (b : Bool) := ih _ (hn ▸ rank_next_lt hd c hc b) (next D c b) rfl
      simp only [hi]
      rw [hv c.wire]
      cases hval : c.value <;> cases h₀ : value (D.child c.wire false) <;>
        cases h₁ : value (D.child c.wire true) <;>
        simp [player, next, Decoder.eval, ho, hval, h₀, h₁,
          Bool.forall_bool, Bool.exists_bool]

/-- All branches terminate within the rank of the starting query. -/
theorem ends_position {rank : α → ℕ} (hd : D.Descends rank) (c : Claim α) :
    Ends (update D encC) (rank c.wire) (position D encC c) := by
  suffices h : ∀ n (c : Claim α), rank c.wire = n →
      Ends (update D encC) n (position D encC c) from h _ c rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro c hn
    cases ho : D.op c.wire with
    | const b =>
      simp only [position, ho]
      split <;> cases n <;> trivial
    | not | and | or =>
      have hc : ∀ b, D.op c.wire ≠ .const b := by intro b; simp [ho]
      have hlt (b : Bool) : rank (next D c b).wire < n := hn ▸ rank_next_lt hd c hc b
      cases n with
      | zero => have := hlt false; omega
      | succ n =>
        simp only [position, ho, Ends]
        intro b
        rw [update_cons]
        exact (ih _ (hlt b) (next D c b) rfl).mono (by have := hlt b; omega)

/-- Every reachable word remains a query, with no larger rank than the starting address. -/
theorem reach_position {rank : α → ℕ} (hd : D.Descends rank) {c₀ : Claim α} {w : List Bool}
    (hw : Reach (update D encC) (position D encC c₀) w) :
    ∃ c, w = position D encC c ∧ rank c.wire ≤ rank c₀.wire := by
  induction hw with
  | start => exact ⟨c₀, rfl, le_rfl⟩
  | move b _ ih =>
    obtain ⟨c, he, hr⟩ := ih
    obtain ⟨hc, rfl⟩ := position_eq_cons he.symm
    rw [update_cons]
    exact ⟨next D c b, rfl, (Nat.le_of_lt (rank_next_lt hd c hc b)).trans hr⟩

/-- The position adds at most two bits to the encoded query. -/
theorem length_position_le (c : Claim α) :
    (position D encC c).length ≤ (encC c).length + 2 := by
  cases ho : D.op c.wire <;> simp [position, ho]
  split <;> simp

end Cslib.Circuits.Boolean.LocalValueGame
