/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (successor lower-bound loop regression tests)

public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic

/-!
# Successor lower bounds in native while guards

A queryful countdown stops at a supplied threshold. Its source writes `n + 1 ≤ k` or
`Nat.succ n ≤ k`; the native comparison must use `n < k` without computing a possibly
overflowing successor. The ghost cutoff still bounds every iteration and is not truncated.
-/

public section

namespace CslibFrontierTests.WordRAMRealizeSuccessorWhile

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := WordEncoding.encode
private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := WordEncoding.encode

private def decrement (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read d.1
  pure (d.2 - 1)

/-- Count down the second word to the first, reading the threshold address on each iteration. -/
def successorCountdown (d : ℕ × ℕ) : Memory.Prog ℕ :=
  boundedWhile (fun n k => n + 1 ≤ k) decrement d.1 d.2 d.2

/-- The successor in the source guard is not an executed addition and needs no fit premise. -/
theorem successor_countdown_realizes : Realizes .exact successorCountdown
    (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun k _ => k)
    (fun k _ _ hk hg => by omega)
    (fun k t _ hg _ => ⟨by omega, trivial, ?_⟩) trivial le_rfl hv
  change k - 1 < k
  omega

-- Reversed nonstrict notation has the same successor lower bound.
example : Realizes .exact
    (fun d : ℕ × ℕ => boundedWhile (fun n k => k ≥ n + 1) decrement d.1 d.2 d.2)
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun k _ => k)
    (fun k _ _ hk hg => by omega)
    (fun k t _ hg _ => ⟨by omega, trivial, ?_⟩) trivial le_rfl hv
  change k - 1 < k
  omega

-- The constructor spelling of successor has the same source and native domain.
example : Realizes .exact
    (fun d : ℕ × ℕ => boundedWhile (fun n k => Nat.succ n ≤ k) decrement d.1 d.2 d.2)
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun k _ => k)
    (fun k _ _ hk hg => by omega)
    (fun k t _ hg _ => ⟨by omega, trivial, ?_⟩) trivial le_rfl hv
  change k - 1 < k
  omega

private def above (n k : ℕ) : Prop := n + 1 ≤ k
private instance (n k : ℕ) : Decidable (above n k) := inferInstanceAs (Decidable (n + 1 ≤ k))

-- A named guard keeps its original domain and accepts a noncanonical decidability instance.
example : Realizes .exact
    (fun d : ℕ × ℕ => @boundedWhile _ _ above
      (fun _ _ => Classical.propDecidable _) decrement d.1 d.2 d.2)
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  intro hv
  refine @whileSafe_of_measure _ _ _ (fun _ _ => Classical.propDecidable _) _ _ w _
    (fun _ _ => True) (fun k _ => k)
    (fun k _ _ hk hg => by dsimp only [above] at hg; omega)
    (fun k t _ hg _ => ⟨?_, trivial, ?_⟩) _ _ _ trivial le_rfl hv
  · dsimp only [above] at hg
    omega
  · change k - 1 < k
    dsimp only [above] at hg
    omega

private abbrev two : ℕ := 2

-- Only the literal's predecessor 1 is installed, so word width one already suffices.
example : Realizes .exact
    (fun k : ℕ => boundedWhile (fun _ k => two ≤ k) decrement 0 k k)
    word word (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
  realize
  · exact h
  · intro hv
    refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun k _ => k)
      (fun k _ _ hk hg => by dsimp only [two] at hg; omega)
      (fun k t _ hg _ => ⟨by dsimp only [two] at hg; omega, trivial, ?_⟩)
      trivial le_rfl hv
    change k - 1 < k
    dsimp only [two] at hg
    omega

-- Basis selection does not change the comparison or nontruncation requirement.
example : Realizes .standard successorCountdown pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  intro hv
  have hkfit : Fits w d.2 := hwords 1
  refine whileSafe_of_measure _ _ _ w _ (fun k _ => k ≤ d.2) (fun k _ => k)
    (fun k _ _ hk hg => by omega)
    (fun k t hi hg _ => ⟨hkfit.of_le (by omega), ?_, ?_⟩) le_rfl le_rfl hv
  · change k - 1 ≤ d.2
    omega
  · change k - 1 < k
    omega

example : RealizesBounded .exact successorCountdown pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  intro hv
  refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun k _ => k)
    (fun k _ _ hk hg => by omega)
    (fun k t _ hg _ => ⟨by omega, trivial, ?_⟩) trivial le_rfl hv
  change k - 1 < k
  omega

-- Normalizing the outer successor does not waive fit for an actually computed predecessor.
example : Realizes .exact
    (fun d : ℕ × ℕ => boundedWhile (fun n k => (n + 1) + 1 ≤ k) decrement d.1 d.2 d.2)
    pairWords word (fun w d _ => Fits w (d.1 + 1)) (fun _ _ => 0) := by
  realize
  · exact h
  · intro hv
    refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun k _ => k)
      (fun k _ _ hk hg => by omega)
      (fun k t _ hg _ => ⟨by omega, trivial, ?_⟩) trivial le_rfl hv
    change k - 1 < k
    omega

example : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun d : ℕ × ℕ => boundedWhile (fun n k => (n + 1) + 1 ≤ k) decrement d.1 d.2 d.2)
        pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
      all_goals
        try
          intro hv
          refine whileSafe_of_measure _ _ _ w _ (fun _ _ => True) (fun k _ => k)
            (fun k _ _ hk hg => by omega)
            (fun k t _ hg _ => ⟨by omega, trivial, ?_⟩) trivial le_rfl hv
          change k - 1 < k
          omega
      all_goals omega
  trivial

-- The source has a fitting nonempty run and stops at the requested threshold.
example : Fits 3 1 ∧ Fits 3 4 ∧
    (Memory.spec 3).clientResult (Memory.State.init [0, 0]) (successorCountdown (1, 4)) = 1 := by
  decide

-- Width zero is also a valid false-guard boundary: no successor fits, and no body runs.
example : Fits 0 0 ∧ ¬Fits 0 (0 + 1) ∧
    (Memory.spec 0).clientResult (Memory.State.init []) (successorCountdown (0, 0)) = 0 ∧
    whileSafe (fun n k => n + 1 ≤ k) decrement (fun _ _ _ => True)
      0 0 0 0 (Memory.State.init []) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  change ¬(0 + 1 ≤ 0)
  decide

/-- At a maximal threshold the actual native code exits with no overflow and no memory query,
even though the successor mentioned by the source does not fit the word width. -/
theorem maximal_threshold_executes : ∃ r C, ∃ code : Code .exact r,
    ∃ result threshold : Fin r, ∃ x y : Data r,
      ¬code.ReadsWidth ∧ x.Bounded 2 ∧ x.regs threshold = 3 ∧ ¬Fits 2 (3 + 1) ∧
      ExecWithin 2 code x y C ∧ y.regs result = 3 ∧ y.mem = x.mem := by
  obtain ⟨n, C, emit, he⟩ := successor_countdown_realizes
  let r := 3 + (1 + n + 1)
  let frontier : Fin r := ⟨0, by omega⟩
  let src : Fin 2 → Fin r := fun i => ⟨1 + i.val, by have := i.isLt; omega⟩
  let tmp : Fin (1 + n + 1) → Fin r := fun i => ⟨3 + i.val, by have := i.isLt; omega⟩
  have hi : Function.Injective tmp := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp only [tmp] at this
    omega
  have hd (i : Fin 2) (j : Fin (1 + n + 1)) : src i ≠ tmp j := by
    intro h
    have := congrArg Fin.val h
    dsimp only [src, tmp] at this
    have := i.isLt
    omega
  have hf (j : Fin (1 + n + 1)) : tmp j ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    dsimp only [tmp, frontier] at this
    omega
  have hs (i : Fin 2) : src i ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    dsimp only [src, frontier] at this
    omega
  let x : Data r := ⟨fun i => if i.val = 1 ∨ i.val = 2 then 3 else 0, fun _ => 0⟩
  have hx : x.Bounded 2 := by
    constructor
    · intro i
      change Fits 2 (if i.val = 1 ∨ i.val = 2 then 3 else 0)
      split_ifs <;> decide
    · intro a
      exact fits_zero 2
  have hin : x.regs ∘ src = WordEncoding.encode (3, 3) := by
    funext i
    fin_cases i <;> rfl
  have hp : successorCountdown (3, 3) = pure 3 := by
    simp [successorCountdown, boundedWhile]
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  obtain ⟨y, hy, hm, ho, _⟩ := hrun 2 (3, 3) x hx hin trivial (by
    rw [hp, StateTransitionSpec.clientHistory_pure]
    trivial)
  have hout := ho 0
  change y.regs (tmp 0) = 3 at hout
  refine ⟨r, C, emit frontier src tmp, tmp 0, src 0, x, y,
    hnw, hx, rfl, by decide, ?_, hout, ?_⟩
  · simpa only [hp, memoryCost_pure, Nat.zero_add, Nat.add_zero, Nat.mul_one] using hy
  · exact congrArg Memory.State.mem hm

-- A computed state expression is still rejected during guard parsing, before domain synthesis.
/--
error: realize: a loop guard compares words; the operand
  a + a
depends on the loop state but is not one of its words
-/
#guard_msgs in
example : Realizes .exact
    (fun d : ℕ × ℕ => boundedWhile (fun n k => n + 1 ≤ k + k) decrement d.1 d.2 d.2)
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/--
error: realize: a loop guard must be `a = b`, `a < b`, `a > b`, `a ≠ 0` or `a + 1 ≤ b` on words, got
  P a
-/
#guard_msgs in
example (P : ℕ → Prop) [DecidablePred P] : Realizes .exact
    (fun k : ℕ => boundedWhile (fun _ k => P k) decrement 0 k k)
    word word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

end CslibFrontierTests.WordRAMRealizeSuccessorWhile
