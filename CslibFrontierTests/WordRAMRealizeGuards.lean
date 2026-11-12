/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (word-comparison guard regression tests)

public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
public import CslibFrontier.DataStructure.ApproximateMembership.WordRAM.QuotientFilter.Cluster

/-!
# Native branches for nonstrict and negated comparisons

The source guards stay in their ordinary natural-number notation. Nonstrict comparisons must
not require an increment of either operand, and reversing a comparison must retain the safety
conditions of the selected arithmetic path. Arbitrary opaque predicates remain outside the
supported branch grammar.
-/

public section

namespace CslibFrontierTests.WordRAMRealizeGuards

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.ApproximateMembership.QuotientFilter

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := WordEncoding.encode
private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := WordEncoding.encode

private def selectedWords (P : ℕ → Prop) [DecidablePred P] : ℕ ↪ (Fin 2 → ℕ) where
  toFun n := ![if ¬P n then 0 else 1, n]
  inj' := fun _ _ h => congrFun h 1

-- Nonstrict comparisons select live words without an additional fit hypothesis.
/-- A non-strict word comparison requires no successor-fit premise. -/
theorem nonstrict_realizes : Realizes .exact
    (fun d : ℕ × ℕ => if d.1 ≤ d.2 then pure d.1 else pure d.2)
    (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

example : Realizes .exact
    (fun d : ℕ × ℕ => if d.1 ≥ d.2 then pure d.1 else pure d.2) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Both disequality spellings compile as the opposite equality branch.
example : Realizes .exact
    (fun d : ℕ × ℕ => if d.1 ≠ d.2 then pure d.1 else pure d.2) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

example : Realizes .exact
    (fun d : ℕ × ℕ => if ¬(d.1 = d.2) then pure d.1 else pure d.2) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Negating a strict comparison and repeated negation do not introduce new arithmetic.
example : Realizes .exact
    (fun d : ℕ × ℕ => if ¬(d.1 < d.2) then pure d.1 else pure d.2) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

example : Realizes .exact
    (fun d : ℕ × ℕ => if ¬¬(d.1 ≤ d.2) then pure d.1 else pure d.2) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- A comparison operand may already be encoded by a word whose host predicate is opaque.
-- Normalizing the guard must preserve that whole operand, including its internal selection.
example (P : ℕ → Prop) [DecidablePred P] : Realizes .exact
    (fun n : ℕ => if (if ¬P n then 0 else 1) ≤ n then
      pure (if ¬P n then 0 else 1) else pure n)
    (selectedWords P) word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Guard normalization also applies to returned choices inside constructors.
example : Realizes .exact
    (fun d : ℕ × ℕ => pure (d.1, if d.1 ≤ d.2 then d.1 else d.2)) pairWords pairWords
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Decidability evidence is not part of the machine's comparison convention.
example : Realizes .exact
    (fun d : ℕ × ℕ => @ite (Memory.Prog ℕ) (d.1 ≤ d.2)
      (Classical.propDecidable _) (pure d.1) (pure d.2)) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Equal largest words take the nonstrict branch even though their successors do not fit.
example : Fits 8 255 ∧ ¬Fits 8 (255 + 1) ∧
    (Memory.spec 8).clientResult (Memory.State.init [])
      (if (255 : ℕ) ≤ 255 then pure 7 else pure 9 : Memory.Prog ℕ) = 7 := by
  decide

-- A nonstrict test returning different branch values still charges its result constants.
example : Realizes .exact
    (fun d : ℕ × ℕ => if d.1 ≤ d.2 then pure 0 else pure 1) pairWords word
    (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
  realize
  exact h

-- An actually computed operand must fit, even though the comparison itself needs no successor.
example : Realizes .exact
    (fun d : ℕ × ℕ => if d.1 ≤ d.2 + 1 then pure d.1 else pure d.2) pairWords word
    (fun w d _ => Fits w (d.2 + 1)) (fun _ _ => 0) := by
  realize
  exact h

example : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun d : ℕ × ℕ => if d.1 ≤ d.2 + 1 then pure d.1 else pure d.2) pairWords word
        (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
  trivial

-- The branch condition justifies exact subtraction precisely where that subtraction runs.
example : Realizes .exact
    (fun d : ℕ × ℕ => if d.2 ≤ d.1 then pure (d.1 - d.2) else pure 0) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  omega

example : Realizes .exact
    (fun d : ℕ × ℕ => if d.2 ≠ 0 then pure (d.1 / d.2) else pure 0) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize
  omega

-- Reversing that subtraction condition cannot make an undefined selected path admissible.
example : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun d : ℕ × ℕ => if d.1 ≤ d.2 then pure (d.1 - d.2) else pure 0) pairWords word
        (fun _ _ _ => True) (fun _ _ => 0) := by
      realize
      omega
  trivial

example : Realizes .standard
    (fun d : ℕ × ℕ => if d.1 ≤ d.2 then pure (d.1 - d.2) else pure d.2) pairWords word
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

example : RealizesBounded .exact
    (fun d : ℕ × ℕ => if d.1 ≠ d.2 then pure (d.1, d.2) else pure (d.2, d.1))
    pairWords pairWords (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- Both migrated helpers accept a comparison bound at the largest two-bit word.
example : (Memory.spec 2).clientResult (Memory.State.init [])
    (scanStepTargetProg ((3, 0), ((3, 3), (0, (0, 0))))) = (1, 1) := by
  decide

example : (Memory.spec 2).clientResult (Memory.State.init [])
    (scanStepQueryProg ((3, 0), ((0, 3), (0, 0)))) = 1 := by
  decide

/-- The migrated query really executes at width two with an encoded cutoff of three. The
comparison's former successor premise would fail here; arguments are already installed. -/
theorem maximum_cutoff_executes : ∃ r C, ∃ code : Code .exact r,
    ∃ result cutoff : Fin r, ∃ x y : Data r,
      ¬code.ReadsWidth ∧ x.Bounded 2 ∧ x.regs cutoff = 3 ∧
      ExecWithin 2 code x y C ∧ y.regs result = 1 ∧ y.mem = x.mem := by
  obtain ⟨n, C, emit, he⟩ := realizes_scanStepQuery
  let r := 7 + (1 + n + 1)
  let frontier : Fin r := ⟨0, by omega⟩
  let src : Fin 6 → Fin r := fun i => ⟨1 + i.val, by have := i.isLt; omega⟩
  let tmp : Fin (1 + n + 1) → Fin r := fun i => ⟨7 + i.val, by have := i.isLt; omega⟩
  have hi : Function.Injective tmp := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp only [tmp] at this
    omega
  have hd (i : Fin 6) (j : Fin (1 + n + 1)) : src i ≠ tmp j := by
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
  have hs (i : Fin 6) : src i ≠ frontier := by
    intro h
    have := congrArg Fin.val h
    dsimp only [src, frontier] at this
    omega
  let d : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) := ((3, 0), ((0, 3), (0, 0)))
  let x : Data r := ⟨fun i => if i.val = 1 ∨ i.val = 4 then 3 else 0, fun _ => 0⟩
  have hx : x.Bounded 2 := by
    constructor
    · intro i
      change Fits 2 (if i.val = 1 ∨ i.val = 4 then 3 else 0)
      split_ifs <;> decide
    · intro a
      exact fits_zero 2
  have hin : x.regs ∘ src = WordEncoding.encode d := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hf hs
  obtain ⟨y, hy, hm, ho, _⟩ := hrun 2 d x hx hin (by change 1 < 2 ^ 2; decide)
    (validHistory_scanStepQuery 2 _ d)
  have hout := ho 0
  change y.regs (tmp 0) = 1 at hout
  refine ⟨r, C, emit frontier src tmp, tmp 0, src 3, x, y, hnw, hx, rfl, ?_, hout, ?_⟩
  · simpa only [memoryCost_scanStepQuery, Nat.zero_add, Nat.add_zero, Nat.mul_one] using hy
  · exact congrArg Memory.State.mem hm

-- These are runtime host predicates, rather than one supported comparison between words.
example (P : ℕ → Prop) [DecidablePred P] : True := by
  fail_if_success
    have _ : Realizes .exact
        (fun n : ℕ => if P n then pure 1 else pure 0) word word
        (fun w _ _ => Fits w 1) (fun _ _ => 0) := by
      realize
  trivial

example : Realizes .exact
    (fun d : ℕ × ℕ => if d.1 ≤ d.2 ∧ d.2 ≠ 0 then pure d.1 else pure d.2)
    pairWords word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

end CslibFrontierTests.WordRAMRealizeGuards
