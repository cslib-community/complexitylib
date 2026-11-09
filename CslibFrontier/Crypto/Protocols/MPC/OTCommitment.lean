/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.SharedMul
public import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Languages.Probabilistic.Norm
import Mathlib.Logic.Equiv.Bool

/-!
# Commitment from ideal oblivious transfer

The Crépeau construction described in [Cramer2000], §7.1, p. 21: commit to `b` by supplying
independent pairs `(r, r ^^ b)` to ideal OT. The receiver retains its private selection bits and
the selected values. Opening reveals all pairs, which must have parity `b` and agree with the
selected values. We use the existing `ot14World`, duplicating the two payloads across four slots.

## Main definitions

* `OTCommitment.Sender`: arbitrary randomized, stateful malicious sender.
* `OTCommitment.Receiver`: arbitrary randomized, stateful malicious receiver.
* `OTCommitment.bindingGame`: two openings after a single commit interaction.
* `OTCommitment.receiverCommitWith`: the common monadic receiver recursion.
* `OTCommitment.receiverCommit`, `OTCommitment.receiverRun`: one honest commit execution with
  private sender masks retained internally, and its receiver-only observation.

## Main results

* `OTCommitment.correct`: every honest opening is accepted.
* `OTCommitment.perfectHiding`: adaptive receiver views have identical laws for both committed bits.
* `OTCommitment.binding`: malicious double-opening probability is at most `2⁻ᵏ`.

These are information-theoretic commitment games in the ideal OT hybrid, not realization of an
ideal commitment functionality or malicious MPC completeness. Strategies may be computationally
unbounded; no polynomial-time certificate is asserted. Communication is a fixed sequence of `k`
OT calls followed by opening, with no receiver messages to the sender. Sender abort is represented
by returning no opening; it cannot increase the winning probability.

## References

* [Ronald Cramer, *Introduction to Secure Computation*, January 2000 revision][Cramer2000],
  §7.1, printed p. 21 (PDF p. 25), crediting Crépeau and Kilian.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Cslib.Probability
open scoped ENNReal

/-- One revealed pair for each OT call. The type enforces the opening length. -/
abbrev Opening (k : ℕ) := Fin k → Bool → Bool

/-- The pair encoding an honest commitment bit, duplicated into the four OT slots. -/
def table (b r : Bool) (j : Fin 4) : Bool :=
  if (fin4ToBoolPair j).2 then r ^^ b else r

/-- A call to the existing ideal OT world, retaining its asymmetric answer types. -/
noncomputable def transfer (t : Fin 4 → Bool) (j : Fin 4) :
    PMF ((s : Fin 2) → ot14Spec.Answer () s) :=
  ProbComp.eval (ot14World () (Fin.cases t (fun _ => j)))

@[simp] theorem transfer_eq (t : Fin 4 → Bool) (j : Fin 4) :
    transfer t j = PMF.pure (Fin.cases () (fun _ => t j)) := by
  simp only [transfer, ot14World, ProbComp.eval_pure]
  rfl

/-- Verify all pair parities and every value actually received through OT. -/
def Accepts {k : ℕ} (choices received : Fin k → Bool) (b : Bool) (o : Opening k) : Prop :=
  ∀ i, (o i false ^^ o i true) = b ∧ o i (choices i) = received i

/-- Honest opening from the sender's independent masks. -/
def opening {k : ℕ} (b : Bool) (masks : Fin k → Bool) : Opening k :=
  fun i c => if c then masks i ^^ b else masks i

/-- Honest OT answers agree with an opening, for every choice vector and every mask vector. -/
theorem correct {k : ℕ} (b : Bool) (masks choices : Fin k → Bool) :
    Accepts choices (fun i => table b (masks i) (boolPairToFin4 (false, choices i)))
      b (opening b masks) := by
  intro i
  simp only [opening, table, fin4ToBoolPair_boolPairToFin4]
  cases b <;> cases masks i <;> cases choices i <;> decide

/-- A sender can select any table from its current private state, retain arbitrary additional
randomness, and update its state using its actual OT answer. That answer is `Unit`, not the
receiver's selected bit. The round number counts the calls remaining. -/
structure Sender (State : Type) where
  /-- Randomized table and private state selection; no parity restriction. -/
  choose : ℕ → State → PMF ((Fin 4 → Bool) × State)
  /-- Local processing of the sender's OT response. -/
  receive : State → Unit → State

/-- Run the sender against a fixed, private receiver choice vector. The returned pair contains
the receiver's OT answers and the sender's final private state, kept separate throughout. -/
noncomputable def senderRun {State : Type} (A : Sender State) :
    (k : ℕ) → State → (Fin k → Bool) → PMF ((Fin k → Bool) × State)
  | 0, st, _ => pure (Fin.elim0, st)
  | k + 1, st, choices => do
      let (t, next) ← A.choose k st
      let ans ← transfer t (boolPairToFin4 (false, choices 0))
      let (rest, final) ← senderRun A k (A.receive next (ans 0)) (Fin.tail choices)
      pure (Fin.cons (ans 1) rest, final)

/-- Common sender-table recursion, with only the sampling backend varied. Receiver choices
are not an input; the semantic specialization is related to actual OT by `senderRun_eq`. -/
def senderTablesWith {m : Type → Type} [Monad m] {State : Type}
    (choose : ℕ → State → m ((Fin 4 → Bool) × State)) (receive : State → Unit → State) :
    (k : ℕ) → State → m ((Fin k → Fin 4 → Bool) × State)
  | 0, st => pure (Fin.elim0, st)
  | k + 1, st => do
      let (t, next) ← choose k st
      let (rest, final) ← senderTablesWith choose receive k (receive next ())
      pure (Fin.cons t rest, final)

/-- The same sender's local table transcript. Its independence from receiver choices is a
consequence of `senderRun_eq`, not a restriction that the tables encode a consistent bit. -/
noncomputable def senderTables {State : Type} (A : Sender State) (k : ℕ) (st : State) :
    PMF ((Fin k → Fin 4 → Bool) × State) :=
  senderTablesWith A.choose A.receive k st

/-- No sender table is generated at zero rounds. -/
theorem senderTables_zero {State : Type} (A : Sender State) (st : State) :
    senderTables A 0 st = pure (Fin.elim0, st) := rfl

/-- One sender round chooses its table, receives only `Unit`, then continues. -/
theorem senderTables_succ {State : Type} (A : Sender State) (k : ℕ) (st : State) :
    senderTables A (k + 1) st = (do
      let (t, next) ← A.choose k st
      let (rest, final) ← senderTables A k (A.receive next ())
      pure (Fin.cons t rest, final)) := rfl

/-- Exact factorization of actual OT execution: the sender's local transcript does not depend
on the private choices, and the receiver gets precisely the selected table entries. -/
theorem senderRun_eq {State : Type} (A : Sender State) (k : ℕ) (st : State)
    (choices : Fin k → Bool) :
    senderRun A k st choices = (senderTables A k st).map
      (fun (ts, final) => (fun i => ts i (boolPairToFin4 (false, choices i)), final)) := by
  induction k generalizing st with
  | zero =>
      simp only [senderRun, senderTables_zero, Probability.PMF.monad_pure_eq_pure, PMF.pure_map]
      congr 2 with i : 1
      exact Fin.elim0 i
  | succ k ih =>
      simp only [pmf_norm, senderRun, senderTables_succ, transfer_eq, ih]
      congr 1
      funext ⟨t, next⟩
      congr 1
      funext ⟨ts, final⟩
      congr 2 with i : 1
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Test two candidate openings to opposite bits; `none` is abort. -/
noncomputable def doubleOpens {k : ℕ} (choices received : Fin k → Bool)
    (o : Option (Opening k × Opening k)) : Bool :=
  match o with
  | none => false
  | some (o₀, o₁) => @decide
      (Accepts choices received false o₀ ∧ Accepts choices received true o₁)
      (Classical.propDecidable _)

/-- Conventional malicious-sender double-opening experiment. Initial private state is independent
of the honest receiver's uniform secret choices. Both openings are generated from the final
sender state, without giving the sender either the choices or the selected values. -/
noncomputable def bindingGame {State : Type} (A : Sender State) (k : ℕ)
    (initial : PMF State) (finish : State → PMF (Option (Opening k × Opening k))) : PMF Bool := do
  let st ← initial
  let choices ← PMF.uniformOfFintype (Fin k → Bool)
  let (received, final) ← senderRun A k st choices
  let o ← finish final
  pure (doubleOpens choices received o)

/-- Two opposite-parity openings can simultaneously match at most one choice vector, regardless
of the tables the sender supplied. -/
theorem doubleOpens_unique {k : ℕ} (ts : Fin k → Fin 4 → Bool)
    (o : Option (Opening k × Opening k)) {c d : Fin k → Bool}
    (hc : doubleOpens c (fun i => ts i (boolPairToFin4 (false, c i))) o = true)
    (hd : doubleOpens d (fun i => ts i (boolPairToFin4 (false, d i))) o = true) : c = d := by
  cases o with
  | none => simp [doubleOpens] at hc
  | some o =>
      obtain ⟨o₀, o₁⟩ := o
      simp only [doubleOpens, decide_eq_true_eq] at hc hd
      funext i
      have hc' : o₀ i (c i) = o₁ i (c i) := (hc.1 i).2.trans (hc.2 i).2.symm
      have hd' : o₀ i (d i) = o₁ i (d i) := (hd.1 i).2.trans (hd.2 i).2.symm
      have hp₀ := (hc.1 i).1
      have hp₁ := (hc.2 i).1
      cases hcbit : c i <;> cases hdbit : d i <;>
        simp only [hcbit, hdbit] at hc' hd' ⊢
      all_goals cases h₀ : o₀ i false <;> cases h₁ : o₀ i true <;>
        cases h₂ : o₁ i false <;> cases h₃ : o₁ i true <;>
        simp_all

private theorem fixed_binding {k : ℕ} (ts : Fin k → Fin 4 → Bool)
    (o : Option (Opening k × Opening k)) :
    ((PMF.uniformOfFintype (Fin k → Bool)).map
      (fun c => doubleOpens c (fun i => ts i (boolPairToFin4 (false, c i))) o)) true ≤
      (2 : ℝ≥0∞)⁻¹ ^ k := by
  classical
  rw [Probability.PMF.uniformOfFintype_map_apply]
  let win := fun c => doubleOpens c (fun i => ts i (boolPairToFin4 (false, c i))) o = true
  have : Subsingleton {c // win c} := ⟨fun a b => Subtype.ext
    (doubleOpens_unique ts o a.property b.property)⟩
  have hc : Nat.card {c // win c} ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  calc
    _ ≤ (1 : ℝ≥0∞) / Fintype.card (Fin k → Bool) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) zero_le
    _ = (2 : ℝ≥0∞)⁻¹ ^ k := by simp [ENNReal.inv_pow]

/-- Information-theoretic binding against every randomized stateful sender, including arbitrary
inconsistent OT tables. This is a two-opening bound, not ideal-functionality simulation. -/
theorem binding {State : Type} (A : Sender State) (k : ℕ) (initial : PMF State)
    (finish : State → PMF (Option (Opening k × Opening k))) :
    bindingGame A k initial finish true ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  simp only [bindingGame, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure]
  apply Probability.PMF.bind_apply_le_on_support
  intro st _
  simp only [senderRun_eq, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  apply Probability.PMF.bind_apply_le_on_support
  intro ts _
  rw [PMF.bind_comm]
  apply Probability.PMF.bind_apply_le_on_support
  intro o _
  exact fixed_binding ts.1 o

/-- An adaptive receiver can choose any of the four OT slots from its private state, then
process the selected bit with arbitrary additional randomness. State may contain its full view. -/
structure Receiver (State : Type) where
  /-- Choice of any OT index, depending on all prior local information. -/
  choose : ℕ → State → PMF (Fin 4 × State)
  /-- Randomized state update after seeing the selected bit. -/
  receive : State → Bool → PMF State

/-- One receiver commit recursion, shared by semantic and program executions. The backend
supplies receiver-local actions, fresh masks, and the selected OT answer. No sender mask is
passed to `choose` or `receive`. -/
def receiverCommitWith {m : Type → Type} [Monad m] {State : Type}
    (choose : ℕ → State → m (Fin 4 × State)) (receive : State → Bool → m State)
    (coin : m Bool)
    (call : (Fin 4 → Bool) → Fin 4 → m ((i : Fin 2) → ot14Spec.Answer () i))
    (b : Bool) :
    (k : ℕ) → State → m ((Fin k → Bool) × (Fin k → Fin 4 × Bool) × State)
  | 0, st => pure (Fin.elim0, Fin.elim0, st)
  | k + 1, st => do
      let (j, next) ← choose k st
      let r ← coin
      let answers ← call (table b r) j
      let next ← receive next (answers 1)
      let (masks, rest, final) ← receiverCommitWith choose receive coin call b k next
      pure (Fin.cons r masks, Fin.cons (j, answers 1) rest, final)

/-- Honest commit execution, retaining the sender's private masks alongside the receiver's
transcript and final state. The masks are never passed to the receiver strategy. The semantic
backend uses the actual OT world and is the original PMF specialization of the shared recursion. -/
noncomputable def receiverCommit {State : Type} (A : Receiver State) (b : Bool) (k : ℕ)
    (st : State) : PMF ((Fin k → Bool) × (Fin k → Fin 4 × Bool) × State) :=
  receiverCommitWith A.choose A.receive (PMF.uniformOfFintype Bool) transfer b k st

/-- No receiver calls or masks are sampled at zero rounds. -/
theorem receiverCommit_zero {State : Type} (A : Receiver State) (b : Bool) (st : State) :
    receiverCommit A b 0 st = pure (Fin.elim0, Fin.elim0, st) := rfl

/-- The PMF backend keeps the original actual-OT execution, including sampling order. -/
theorem receiverCommit_succ {State : Type} (A : Receiver State) (b : Bool) (k : ℕ) (st : State) :
    receiverCommit A b (k + 1) st = (do
      let (j, next) ← A.choose k st
      let r ← PMF.uniformOfFintype Bool
      let ans ← transfer (table b r) j
      let next ← A.receive next (ans 1)
      let (masks, rest, final) ← receiverCommit A b k next
      pure (Fin.cons r masks, Fin.cons (j, ans 1) rest, final)) := rfl

/-- Honest sender against an adaptive receiver. The result explicitly includes every receiver
query and answer, as well as final private state. Each fresh sender mask is independent of the
receiver's current query and history. The sender's masks are projected away. -/
noncomputable def receiverRun {State : Type} (A : Receiver State) (b : Bool) (k : ℕ) (st : State) :
    PMF ((Fin k → Fin 4 × Bool) × State) :=
  (receiverCommit A b k st).map Prod.snd

/-- Observing zero commit calls returns an empty receiver transcript. -/
theorem receiverRun_zero {State : Type} (A : Receiver State) (b : Bool) (st : State) :
    receiverRun A b 0 st = pure (Fin.elim0, st) := by
  simp [receiverRun, receiverCommit_zero]

/-- The receiver observation keeps the original step-by-step OT execution, without exposing
any honest sender mask to the strategy. -/
theorem receiverRun_succ {State : Type} (A : Receiver State) (b : Bool) (k : ℕ) (st : State) :
    receiverRun A b (k + 1) st = (do
      let (j, next) ← A.choose k st
      let r ← PMF.uniformOfFintype Bool
      let ans ← transfer (table b r) j
      let next ← A.receive next (ans 1)
      let (rest, final) ← receiverRun A b k next
      pure (Fin.cons (j, ans 1) rest, final)) := by
  simp only [pmf_norm, receiverRun, receiverCommit_succ]

private theorem uniform_table (b : Bool) (j : Fin 4) :
    (PMF.uniformOfFintype Bool).map (fun r => table b r j) = PMF.uniformOfFintype Bool := by
  cases b <;> by_cases h : (fin4ToBoolPair j).2 = true
  · simp only [table, h, ↓reduceIte, Bool.xor_false]
    exact PMF.map_id _
  · simp only [table, h]
    exact PMF.map_id _
  · simpa [table, h, Equiv.boolNot] using PMF.uniformOfFintype_map_equiv (Equiv.boolNot)
  · simp only [table, h]
    exact PMF.map_id _

/-- Perfect hiding of the complete adaptive receiver view, for all four possible OT indices.
The initial state can be any fixed auxiliary input; averaging preserves the equality. -/
theorem perfectHiding {State : Type} (A : Receiver State) (b b' : Bool) (k : ℕ) (st : State) :
    receiverRun A b k st = receiverRun A b' k st := by
  induction k generalizing st with
  | zero => rfl
  | succ k ih =>
      simp only [pmf_norm, receiverRun_succ, transfer_eq]
      congr 1
      funext ⟨j, next⟩
      simp only [ih]
      let f : Bool → PMF ((Fin (k + 1) → Fin 4 × Bool) × State) :=
        fun a => (A.receive next a).bind fun next =>
        (receiverRun A b' k next).map fun p => (Fin.cons (j, a) p.1, p.2)
      change (PMF.uniformOfFintype Bool).bind (f ∘ fun r => table b r j) =
        (PMF.uniformOfFintype Bool).bind (f ∘ fun r => table b' r j)
      rw [← PMF.bind_map, uniform_table, ← PMF.bind_map, uniform_table]

end Cslib.Crypto.Protocols.MPC.OTCommitment
