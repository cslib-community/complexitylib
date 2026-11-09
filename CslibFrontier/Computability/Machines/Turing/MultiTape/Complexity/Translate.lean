/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.MultiPass
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.Tactic.EncLen

/-!
# Folds behind a finite-state translator

A translator reads bits and emits, for each bit, at most one event, with a finite state in between.
A fold over the events of a word is a fold over its bits, whose state also holds the state of the
translator: each bit steps the translator and, if it emits an event, steps the inner fold. This
turns a fold over a convenient encoding into a fold over another one, at the cost of a constant
amount of state, so it applies to streaming and multi-pass folds alike.

## Main definitions

* `Turing.MultiTapeTM.Translator`: finite-state translators from bits to events.
* `Turing.MultiTapeTM.Translator.lift`: the step of a fold on bits from one on events.

## Main results

* `Turing.MultiTapeTM.Translator.foldl_lift`: the lifted fold folds over the events.
* `Turing.MultiTapeTM.ComputableTidilyInO.lift`: the lifted step is tidily computable.
-/

namespace Turing.MultiTapeTM

/-- A translator from bits to events: from each state, a bit leads to a state and at most one
event. -/
public structure Translator (Q E : Type*) where
  /-- The initial state. -/
  q₀ : Q
  /-- The next state and the emitted event, if any. -/
  step : Q → Bool → Q × Option E

namespace Translator

variable {Q E σ : Type*} (tr : Translator Q E)

/-- The state and the events after reading `w` from the state `q`. -/
@[expose] public def run : Q → List Bool → Q × List E
  | q, [] => (q, [])
  | q, b :: w => ((run (tr.step q b).1 w).1, (tr.step q b).2.toList ++ (run (tr.step q b).1 w).2)

/-- The events of `w`. -/
@[expose] public def events (w : List Bool) : List E := (tr.run tr.q₀ w).2

/-- The step of a fold on bits from the step `next` of a fold on events: step the translator and,
if it emits an event, the fold. -/
@[expose] public def lift (next : σ × E → σ) (p : (Q × σ) × Bool) : Q × σ :=
  ((tr.step p.1.1 p.2).1, (tr.step p.1.1 p.2).2.elim p.1.2 fun e => next (p.1.2, e))

/-- **The lifted fold** folds over the events, and ends in the state of the translator. -/
public theorem foldl_lift (next : σ × E → σ) (q : Q) (s : σ) (w : List Bool) :
    w.foldl (fun p b => tr.lift next (p, b)) (q, s) =
      ((tr.run q w).1, (tr.run q w).2.foldl (fun s e => next (s, e)) s) := by
  induction w generalizing q s with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldl_cons, lift, ih, run]
    cases (tr.step q b).2 <;> simp

public lemma run_append (q : Q) (u v : List Bool) :
    tr.run q (u ++ v) =
      ((tr.run (tr.run q u).1 v).1, (tr.run q u).2 ++ (tr.run (tr.run q u).1 v).2) := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih => simp [run, ih]

/-- The events of a prefix are a prefix of the events. -/
public lemma run_take (q : Q) (w : List Bool) (k : ℕ) :
    (tr.run q w).2.take (tr.run q (w.take k)).2.length = (tr.run q (w.take k)).2 := by
  conv_lhs => rw [← List.take_append_drop k w, run_append]
  simp

/-- The bit at position `k` emits the next event, if any. -/
public lemma run_take_succ (q : Q) (w : List Bool) {k : ℕ} (hk : k < w.length) :
    tr.run q (w.take (k + 1)) = ((tr.step (tr.run q (w.take k)).1 w[k]).1,
      (tr.run q (w.take k)).2 ++ (tr.step (tr.run q (w.take k)).1 w[k]).2.toList) := by
  rw [List.take_succ_eq_append_getElem hk, run_append]
  simp [run]

/-- The lifted fold after `k` bits: the state of the translator, and the inner fold after the
events of the first `k` bits. -/
public lemma streamState_lift (next : σ × E → σ) (q : Q) (s : σ) (w : List Bool) (k : ℕ) :
    streamState (q, s) (tr.lift next) w k = ((tr.run q (w.take k)).1,
      streamState s next (tr.run q w).2 (tr.run q (w.take k)).2.length) := by
  rw [streamState, foldl_lift, streamState, run_take]

/-- The passes of the lifted fold, which restart the translator, are those of the inner fold on
the events. -/
public lemma passState_lift (init : σ) (next : σ × E → σ) (passEnd : σ → σ) (w : List Bool)
    (i : ℕ) : passState (tr.q₀, init) (tr.lift next) (fun p => (tr.q₀, passEnd p.2)) w i =
      (tr.q₀, passState init next passEnd (tr.events w) i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [passState, ih, streamState_lift, List.take_length, passState]
    rfl

/-- A bound on the events holds for the event of every bit, if any: the event of bit `k` is the
event after those of the first `k` bits. -/
public lemma elim_le (q : Q) (w : List Bool) {k : ℕ} (hk : k < w.length) (F : ℕ → E → ℕ)
    {m : ℕ} (hF : ∀ j (hj : j < (tr.run q w).2.length), F j (tr.run q w).2[j] ≤ m) :
    (tr.step (tr.run q (w.take k)).1 w[k]).2.elim 0 (F (tr.run q (w.take k)).2.length) ≤ m := by
  cases he : (tr.step (tr.run q (w.take k)).1 w[k]).2 with
  | none => exact Nat.zero_le _
  | some e =>
    have h := tr.run_take q w (k + 1)
    rw [tr.run_take_succ q w hk, he] at h
    have hj : (tr.run q (w.take k)).2.length < (tr.run q w).2.length := by
      have := congrArg List.length h
      enc_len [List.length_take, Option.toList_some, List.length_singleton] at this
    have : (tr.run q w).2[(tr.run q (w.take k)).2.length] = e := by
      have := congrArg (·[(tr.run q (w.take k)).2.length]?) h
      simp only [List.getElem?_take, ↓reduceIte, Option.toList_some,
        List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_singleton] at this
      simpa [List.getElem?_eq_getElem hj] using this
    simpa [this] using hF _ hj

/-- The length of the events of a prefix. -/
public lemma length_run_take_le (q : Q) (w : List Bool) (k : ℕ) :
    (tr.run q (w.take k)).2.length ≤ (tr.run q w).2.length := by
  rw [← tr.run_take q w k]
  exact List.length_take_le' _ _

end Translator

namespace ComputableTidilyInO

variable {Q E σ : Type} [Finite Q] [Inhabited E] {encQ : Q ↪ List Bool}
  {encE : E ↪ List Bool} {encS : σ ↪ List Bool} {next : σ × E → σ} {T S : σ × E → ℕ}

/-- **The lifted step is tidily computable**, within the bounds of the inner step on the emitted
event, if any, plus the length of its input. -/
public theorem lift (tr : Translator Q E)
    (h : ComputableTidilyInO next (encPair encS encE) encS T S) :
    ComputableTidilyInO (tr.lift next) (encPair (encPair encQ encS) encBool) (encPair encQ encS)
      (fun p => (encPair (encPair encQ encS) encBool p).length +
        (tr.step p.1.1 p.2).2.elim 0 fun e => T (p.1.2, e))
      (fun p => (encPair (encPair encQ encS) encBool p).length +
        (tr.step p.1.1 p.2).2.elim 0 fun e => S (p.1.2, e)) := by
  have hl (p : (Q × σ) × Bool) : (encPair encQ encBool (p.1.1, p.2)).length ≤
      (encPair (encPair encQ encS) encBool p).length := by
    enc_len [List.length_singleton]
  have h₁ := fst (encPair encQ encS) encBool
  have hqb := (fst' h₁).prod (snd (encPair encQ encS) encBool)
  have hstate := ((ComputableTidilyInDegree.of_finite (encIn := encPair encQ encBool)
    (encMid := encQ) fun qb : Q × Bool => (tr.step qb.1 qb.2).1).inO_one).comp hqb
  have hsome := ((ComputableTidilyInDegree.of_finite (encIn := encPair encQ encBool)
    (encMid := encBool) fun qb : Q × Bool => (tr.step qb.1 qb.2).2.isSome).inO_one).comp hqb
  have hevent := ((ComputableTidilyInDegree.of_finite (encIn := encPair encQ encBool)
    (encMid := encE) fun qb : Q × Bool => (tr.step qb.1 qb.2).2.getD default).inO_one).comp hqb
  have hs := snd' h₁
  have hnext := h.comp (hs.prod hevent)
  have hall := hstate.prod (hsome.ite hnext hs)
  refine (hall.of_enc_eq (g := tr.lift next) fun p => ?_).mono 20 (fun p => ?_) fun p => ?_
  · simp only [Function.comp_apply, Translator.lift]
    cases (tr.step p.1.1 p.2).2 <;> rfl
  all_goals
    have := hl p
    cases h : (tr.step p.1.1 p.2).2 <;> simp only [Function.comp_apply, h] <;> simp <;> omega

end ComputableTidilyInO

/-! ### Bounds -/

/-- A round of the fold on bits, against the bounds of the fold on events. -/
lemma round_le (cQ K t l : ℕ) :
    2 * K * (t + (4 * cQ + 4 * l + 6) + 1) + (4 * cQ + 4 * l + 6) + 1 ≤
      (2 * K + 1) * (4 * cQ + 7) * (t + l + 1) := by
  have h1 : t + (4 * cQ + 4 * l + 6) + 1 ≤ (4 * cQ + 7) * (t + l + 1) := by nlinarith
  rw [Nat.mul_assoc]
  nlinarith

/-- The time of the fold on bits. -/
lemma time_le (c cI cF cQ K TI TF t l N P li le : ℕ) (hP : 1 ≤ P) (hli : li ≤ l)
    (hle : le ≤ 2 * cQ + 1 + l) :
    c * (cI * (TI + (li + li) + 1) + cF * (le + TF + 1) +
      P * (N + (N + 1) * (2 * K * (t + (4 * cQ + 4 * l + 6) + 1) + (4 * cQ + 4 * l + 6) + 1))) ≤
    c * (3 * cI + cF * (2 * cQ + 3) + (2 * K + 1) * (4 * cQ + 7) + 1) *
      (TI + TF + P * (N + (N + 1) * (t + l + 1))) := by
  set G := (2 * K + 1) * (4 * cQ + 7)
  set W := P * (N + (N + 1) * (t + l + 1))
  have hG : 1 ≤ G := Nat.mul_pos (by omega) (by omega)
  have hX : t + l + 1 ≤ W := by
    calc t + l + 1 ≤ (N + 1) * (t + l + 1) := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ N + (N + 1) * (t + l + 1) := by omega
      _ ≤ W := Nat.le_mul_of_pos_left _ hP
  have hR : P * (N + (N + 1) * (2 * K * (t + (4 * cQ + 4 * l + 6) + 1) + (4 * cQ + 4 * l + 6) + 1))
      ≤ G * W := by
    calc _ ≤ P * (G * N + (N + 1) * (G * (t + l + 1))) := by
          gcongr
          · exact Nat.le_mul_of_pos_left _ hG
          · exact round_le cQ K t l
      _ = G * W := by ring
  have h₁ : cI * (TI + (li + li) + 1) ≤ cI * TI + 2 * cI * W := by nlinarith
  have h₂ : cF * (le + TF + 1) ≤ cF * TF + cF * (2 * cQ + 3) * W := by
    have : le + 1 ≤ (2 * cQ + 3) * W := by nlinarith
    have := Nat.mul_le_mul_left cF this
    rw [Nat.mul_assoc]
    linarith [show cF * (le + TF + 1) = cF * TF + cF * (le + 1) by ring]
  refine le_trans (Nat.mul_le_mul_left c ?_) (le_of_eq (Nat.mul_assoc _ _ _).symm)
  calc _ ≤ cI * TI + 2 * cI * W + (cF * TF + cF * (2 * cQ + 3) * W) + G * W := by linarith
    _ ≤ _ := by ring_nf; omega

/-- The space of the fold on bits. -/
lemma space_le (c cI cF cQ K SI SF s l li le : ℕ) (hli : li ≤ l) (hle : le ≤ 2 * cQ + 1 + l) :
    c * (cI * (SI + (li + li) + 1) + cF * (le + SF + 1) + 2 * K * (s + (4 * cQ + 4 * l + 6) + 1) +
      (4 * cQ + 4 * l + 6) + 1) ≤
    c * (3 * cI + cF * (2 * cQ + 3) + (2 * K + 1) * (4 * cQ + 7) + 1) * (SI + SF + s + l + 1) := by
  have hR := round_le cQ K s l
  have h₁ : cI * (SI + (li + li) + 1) ≤ cI * SI + 2 * cI * (s + l + 1) := by nlinarith
  have h₂ : cF * (le + SF + 1) ≤ cF * SF + cF * (2 * cQ + 3) * (s + l + 1) := by
    have : le + 1 ≤ (2 * cQ + 3) * (s + l + 1) := by nlinarith
    have := Nat.mul_le_mul_left cF this
    rw [Nat.mul_assoc]
    linarith [show cF * (le + SF + 1) = cF * SF + cF * (le + 1) by ring]
  refine le_trans (Nat.mul_le_mul_left c ?_) (le_of_eq (Nat.mul_assoc _ _ _).symm)
  calc _ ≤ cI * SI + 2 * cI * (s + l + 1) + (cF * SF + cF * (2 * cQ + 3) * (s + l + 1)) +
        (2 * K + 1) * (4 * cQ + 7) * (s + l + 1) := by linarith
    _ ≤ _ := by ring_nf; omega

/-- Reads one bit and emits it. -/
def bitReader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩

open Translator in
/-- **Multi-pass folds behind a translator.** A multi-pass fold over the events that the
translator `tr` emits on the encoded input is tidily computable on the encoded input itself, from
parts computable within the given bounds. Each pass reads every bit, so its time is the length of
the input times the bounds on a round; the space is that of the fold on the events. The bounds
`tMax`, `sMax` and `lMax` bound the time and space of a round and of the end of a pass, and the
lengths of the states. -/
public theorem ComputableTidilyInTimeAndSpace.multiPassFold_translate {Q E σ γ ε' φ ω : Type}
    [Finite Q] [Inhabited E] {encQ : Q ↪ List Bool} {encE : E ↪ List Bool}
    {encS : σ ↪ List Bool} {encE' : ε' ↪ List Bool} {encF : φ ↪ List Bool}
    {encIn : γ ↪ List Bool} {encOut : ω ↪ List Bool} (tr : Translator Q E)
    {init : γ → σ} {next : σ × E → σ} {passEmit : σ → ε'} {passEnd : σ → σ} {cont : σ → Bool}
    {finish : σ → φ} {g : γ → ω} {passes : γ → ℕ} {TI SI : γ → ℕ} {T S : σ × E → ℕ}
    {TPE SPE TPN SPN TC SC TF SF : σ → ℕ}
    (hinit : ComputableTidilyInO init encIn encS TI SI)
    (hnext : ComputableTidilyInO next (encPair encS encE) encS T S)
    (hpassEmit : ComputableTidilyInO passEmit encS encE' TPE SPE)
    (hpassEnd : ComputableTidilyInO passEnd encS encS TPN SPN)
    (hcont : ComputableTidilyInO cont encS encBool TC SC)
    (hfinish : ComputableTidilyInO finish encS encF TF SF)
    (hpasses : ∀ x, ∀ i ≤ passes x,
      cont (passState (init x) next passEnd (tr.events (encIn x)) (i + 1)) = decide (i < passes x))
    (hg : ∀ x, encOut (g x) = ((List.range (passes x + 1)).map fun i =>
      encE' (passEmit (streamState (passState (init x) next passEnd (tr.events (encIn x)) i)
        next (tr.events (encIn x)) (tr.events (encIn x)).length))).flatten ++
      encF (finish (passState (init x) next passEnd (tr.events (encIn x)) (passes x + 1))))
    {tMax sMax lMax : γ → ℕ}
    (htMax : ∀ x, ∀ i ≤ passes x, ∀ j (hj : j < (tr.events (encIn x)).length),
      T (streamState (passState (init x) next passEnd (tr.events (encIn x)) i) next
        (tr.events (encIn x)) j, (tr.events (encIn x))[j]) ≤ tMax x)
    (hsMax : ∀ x, ∀ i ≤ passes x, ∀ j (hj : j < (tr.events (encIn x)).length),
      S (streamState (passState (init x) next passEnd (tr.events (encIn x)) i) next
        (tr.events (encIn x)) j, (tr.events (encIn x))[j]) ≤ sMax x)
    (htEnd : ∀ x, ∀ i ≤ passes x,
      TPE (streamState (passState (init x) next passEnd (tr.events (encIn x)) i) next
          (tr.events (encIn x)) (tr.events (encIn x)).length) +
        TPN (streamState (passState (init x) next passEnd (tr.events (encIn x)) i) next
          (tr.events (encIn x)) (tr.events (encIn x)).length) +
        TC (passState (init x) next passEnd (tr.events (encIn x)) (i + 1)) ≤ tMax x)
    (hsEnd : ∀ x, ∀ i ≤ passes x,
      SPE (streamState (passState (init x) next passEnd (tr.events (encIn x)) i) next
          (tr.events (encIn x)) (tr.events (encIn x)).length) +
        SPN (streamState (passState (init x) next passEnd (tr.events (encIn x)) i) next
          (tr.events (encIn x)) (tr.events (encIn x)).length) +
        SC (passState (init x) next passEnd (tr.events (encIn x)) (i + 1)) ≤ sMax x)
    (hS : ∀ x, ∀ i ≤ passes x, ∀ j ≤ (tr.events (encIn x)).length,
      (encS (streamState (passState (init x) next passEnd (tr.events (encIn x)) i) next
        (tr.events (encIn x)) j)).length ≤ lMax x)
    (hSlast : ∀ x, (encS (passState (init x) next passEnd (tr.events (encIn x))
      (passes x + 1))).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace g encIn encOut
      (fun x => c * (TI x + TF (passState (init x) next passEnd (tr.events (encIn x))
        (passes x + 1)) + (passes x + 1) * ((encIn x).length +
          ((encIn x).length + 1) * (tMax x + lMax x + 1))))
      (fun x => c * (SI x + SF (passState (init x) next passEnd (tr.events (encIn x))
        (passes x + 1)) + sMax x + lMax x + 1)) := by
  obtain ⟨cQ, hcQ⟩ : ∃ cQ, ∀ q, (encQ q).length ≤ cQ := by
    rcases isEmpty_or_nonempty Q with hQ | hQ
    · exact ⟨0, fun q => isEmptyElim q⟩
    · obtain ⟨q, hq⟩ := Finite.exists_max fun q => (encQ q).length
      exact ⟨_, hq⟩
  -- the parts on the states with the translator
  have hpre : ComputableTidilyInO (fun s : σ => (tr.q₀, s)) encS (encPair encQ encS)
      (fun s => (encS s).length + (encS s).length)
      (fun s => (encS s).length + (encS s).length) :=
    ComputableTidilyInO.append (enc₂ := encS) (f₂ := id) (g := fun s => (tr.q₀, s))
      (encOut := encPair encQ encS)
      (.of_linear (.const (encMid := encFramed encQ) tr.q₀)) (.of_linear (.of_eq fun _ => rfl))
      fun s => by simp
  have hsnd := ComputableTidilyInO.snd encQ encS
  obtain ⟨cI, hI, -⟩ := hpre.comp hinit
  obtain ⟨cN, hN, -⟩ := ComputableTidilyInO.lift (encQ := encQ) tr hnext
  obtain ⟨cE, hE⟩ := ComputableTidilyInLinearTimeAndSpace.const (α := (Q × σ) × Bool)
    (encIn := encPair (encPair encQ encS) encBool) (encMid := encBits) []
  obtain ⟨cPE, hPE, -⟩ := hpassEmit.comp hsnd
  obtain ⟨cPN, hPN, -⟩ := hpre.comp (hpassEnd.comp hsnd)
  obtain ⟨cC, hC, -⟩ := hcont.comp hsnd
  obtain ⟨cF, hF, -⟩ := hfinish.comp hsnd
  have hI' : ComputableTidilyInTimeAndSpace (fun x => (tr.q₀, init x)) encIn (encPair encQ encS)
      _ _ := hI
  have hPE' : ComputableTidilyInTimeAndSpace (fun p : Q × σ => passEmit p.2) (encPair encQ encS)
      encE' _ _ := hPE
  have hPN' : ComputableTidilyInTimeAndSpace (fun p : Q × σ => (tr.q₀, passEnd p.2))
      (encPair encQ encS) (encPair encQ encS) _ _ := hPN
  have hC' : ComputableTidilyInTimeAndSpace (fun p : Q × σ => cont p.2) (encPair encQ encS)
      encBool _ _ := hC
  have hF' : ComputableTidilyInTimeAndSpace (fun p : Q × σ => finish p.2) (encPair encQ encS)
      encF _ _ := hF
  -- the bounds of the fold on bits
  set K := cN + cE + cPE + cPN + cC + 1 with hK
  let B (x : γ) : ℕ := 4 * cQ + 4 * lMax x + 6
  -- the states of the passes, and the bounds on them
  have hps (x : γ) (i : ℕ) (hi : i ≤ passes x + 1) :
      (encS (passState (init x) next passEnd (tr.events (encIn x)) i)).length ≤ lMax x := by
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact hS x i (by omega) 0 (Nat.zero_le _)
    · exact hSlast x
  have hlen (x : γ) (q : Q) (s : σ) (hs : (encS s).length ≤ lMax x) :
      (encPair encQ encS (q, s)).length ≤ 2 * cQ + 1 + lMax x := by
    have := hcQ q
    enc_len
  have hK2 (a b : ℕ) (hab : a + b ≤ K) (X : ℕ) : a * X + b * X ≤ 2 * K * X := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right X (by omega)
  have hK3 (a b c : ℕ) (habc : a + b + c ≤ K) (X : ℕ) : a * X + b * X + c * X ≤ 2 * K * X := by
    rw [← Nat.add_mul, ← Nat.add_mul]
    exact Nat.mul_le_mul_right X (by omega)
  refine Exists.elim (ComputableTidilyInTimeAndSpace.multiPassFold (r := bitReader)
    (tok := fun b => [b]) (encA := encBool) (fun _ => List.cons_ne_nil _ _)
    (fun a rest => by simp [bitReader, InputReader.read]) (fun x => encIn x) (fun x => by simp)
    hI' hN hE hPE' hPN' hC' hF' (passes := passes) (g := g) (encOut := encOut) ?_ ?_
    (tMax := fun x => 2 * K * (tMax x + B x + 1)) (sMax := fun x => 2 * K * (sMax x + B x + 1))
    (lMax := B) ?_ ?_ ?_ ?_ ?_ ?_ ?_) fun c h => ?_
  case refine_1 =>
    intro x i hi
    rw [Translator.passState_lift]
    exact hpasses x i hi
  case refine_2 =>
    intro x
    rw [hg x]
    simp only [Translator.passState_lift, Translator.streamState_lift, List.take_length,
      encBits_apply, streamEmit_const_nil, List.nil_append]
    rfl
  case refine_3 =>
    intro x i hi j hj
    rw [Translator.passState_lift, Translator.streamState_lift]
    have he := tr.elim_le tr.q₀ (encIn x) hj (fun jj e => T (streamState
      (passState (init x) next passEnd (tr.events (encIn x)) i) next (tr.run tr.q₀ (encIn x)).2 jj,
        e)) (fun jj hjj => htMax x i hi jj hjj)
    have hl := hlen x (tr.run tr.q₀ ((encIn x).take j)).1 _
      (hS x i hi _ (tr.length_run_take_le tr.q₀ (encIn x) j))
    beta_reduce at he ⊢
    simp only [length_encPair, encBool_apply, List.length_singleton, Translator.events] at hl he ⊢
    have hB : B x = 4 * cQ + 4 * lMax x + 6 := rfl
    refine (Nat.add_le_add (Nat.mul_le_mul_left (m := tMax x + B x + 1) cN ?_)
      (Nat.mul_le_mul_left (m := tMax x + B x + 1) cE ?_)).trans (hK2 _ _ (by omega) _)
    · omega
    · omega
  case refine_4 =>
    intro x i hi j hj
    rw [Translator.passState_lift, Translator.streamState_lift]
    have he := tr.elim_le tr.q₀ (encIn x) hj (fun jj e => S (streamState
      (passState (init x) next passEnd (tr.events (encIn x)) i) next (tr.run tr.q₀ (encIn x)).2 jj,
        e)) (fun jj hjj => hsMax x i hi jj hjj)
    have hl := hlen x (tr.run tr.q₀ ((encIn x).take j)).1 _
      (hS x i hi _ (tr.length_run_take_le tr.q₀ (encIn x) j))
    beta_reduce at he ⊢
    simp only [length_encPair, encBool_apply, List.length_singleton, Translator.events] at hl he ⊢
    have hB : B x = 4 * cQ + 4 * lMax x + 6 := rfl
    refine (Nat.add_le_add (Nat.mul_le_mul_left (m := sMax x + B x + 1) cN ?_)
      (Nat.mul_le_mul_left (m := sMax x + B x + 1) cE ?_)).trans (hK2 _ _ (by omega) _)
    · omega
    · omega
  case refine_5 =>
    intro x i hi
    rw [Translator.passState_lift, Translator.streamState_lift, List.take_length,
      Translator.passState_lift]
    have h₀ := hlen x (tr.run tr.q₀ (encIn x)).1 _ (hS x i hi _ le_rfl)
    have h₁ := hlen x tr.q₀ _ (hps x (i + 1) (by omega))
    have h₂ := hps x (i + 1) (by omega)
    have he := htEnd x i hi
    beta_reduce
    simp only [Translator.events, passState, Function.comp_apply] at h₀ h₁ h₂ he ⊢
    have hB : B x = 4 * cQ + 4 * lMax x + 6 := rfl
    refine (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left (m := tMax x + B x + 1) cPE ?_)
      (Nat.mul_le_mul_left (m := tMax x + B x + 1) cPN ?_))
      (Nat.mul_le_mul_left (m := tMax x + B x + 1) cC ?_)).trans (hK3 _ _ _ (by omega) _) <;>
    omega
  case refine_6 =>
    intro x i hi
    rw [Translator.passState_lift, Translator.streamState_lift, List.take_length,
      Translator.passState_lift]
    have h₀ := hlen x (tr.run tr.q₀ (encIn x)).1 _ (hS x i hi _ le_rfl)
    have h₁ := hlen x tr.q₀ _ (hps x (i + 1) (by omega))
    have h₂ := hps x (i + 1) (by omega)
    have he := hsEnd x i hi
    beta_reduce
    simp only [Translator.events, passState, Function.comp_apply] at h₀ h₁ h₂ he ⊢
    have hB : B x = 4 * cQ + 4 * lMax x + 6 := rfl
    refine (Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul_left (m := sMax x + B x + 1) cPE ?_)
      (Nat.mul_le_mul_left (m := sMax x + B x + 1) cPN ?_))
      (Nat.mul_le_mul_left (m := sMax x + B x + 1) cC ?_)).trans (hK3 _ _ _ (by omega) _) <;>
    omega
  case refine_7 =>
    intro x i hi j hj
    rw [Translator.passState_lift, Translator.streamState_lift]
    have := hlen x (tr.run tr.q₀ ((encIn x).take j)).1 _
      (hS x i hi _ (tr.length_run_take_le tr.q₀ (encIn x) j))
    simp only [Translator.events] at this ⊢
    have hB : B x = 4 * cQ + 4 * lMax x + 6 := rfl
    omega
  case refine_8 =>
    intro x
    rw [Translator.passState_lift]
    have := hlen x tr.q₀ _ (hSlast x)
    have hB : B x = 4 * cQ + 4 * lMax x + 6 := rfl
    omega
  case refine_9 =>
    intro x j hj
    simp [B]
  refine ⟨c * (3 * cI + cF * (2 * cQ + 3) + (2 * K + 1) * (4 * cQ + 7) + 1),
    h.mono (fun x => ?_) (fun x => ?_)⟩
  · rw [Translator.passState_lift]
    exact time_le c cI cF cQ K _ _ _ _ _ _ _ _ (by omega) (hps x 0 (Nat.zero_le _))
      (hlen x tr.q₀ _ (hps x _ le_rfl))
  · rw [Translator.passState_lift]
    exact space_le c cI cF cQ K _ _ _ _ _ _ (hps x 0 (Nat.zero_le _))
      (hlen x tr.q₀ _ (hps x _ le_rfl))

end Turing.MultiTapeTM
