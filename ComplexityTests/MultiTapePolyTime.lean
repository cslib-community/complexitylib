/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Window
import Complexity.Computability.Complexity.CookLevin.Parameters

/-!
# Tests for the polynomial-time calculus

Based on Christian Reitwiessner's `CslibTests/MultiTapePolyTime.lean` (branch `crei/tidy-universal`
@7f7c0696), and the change that branch makes to `CslibTests/MultiTapeComplexity.lean`, with tests
for encoding inference, list construction and indexing.
-/

namespace ComplexityTests.MultiTapePolyTime

open Turing.MultiTapeTM

-- Captured bit maps, option fallback, binary/unary logarithms, and arithmetic closure.
example :
    ComputableTidilyInPolyTime
      (fun p : Bool × List Bool => p.2.map (fun bit => p.1 ^^ bit))
      (encPair encBool encBits) encBits ∧
    ComputableTidilyInPolyTime
      (fun p : Option ℕ × ℕ => p.1.getD (p.2 + 1))
      (encPair (encOption encUnary) encUnary) encUnary ∧
    ComputableTidilyInPolyTime (fun n => Nat.log 2 n + 1) encNat encUnary ∧
    ComputableTidilyInPolyTime (fun n => Nat.log 2 (n ^ 2 + 1)) encUnary encUnary ∧
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.2, p.1 + 1 + 1))
      (encPair encNat encNat) (encPair encNat encNat) :=
  ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop, by fun_prop⟩

example {c : ℕ → Bool} (hc : ComputableTidilyInPolyTime c encNat encBool) :
    ComputableTidilyInPolyTime (fun n => if c n then n + 1 else n) encNat encNat := by
  fun_prop

-- List map, idxOf, getD, and their composition.
example :
    ComputableTidilyInPolyTime (List.map (fun n : ℕ => n + 1))
      (encList encNat) (encList encNat) ∧
    ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1.idxOf p.2)
      (encPair (encList encNat) encNat) encUnary ∧
    ComputableTidilyInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 false)
      (encPair encBits encUnary) encBool ∧
    ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1.getD (p.1.idxOf p.2) 0)
      (encPair (encList encNat) encNat) encNat :=
  ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop⟩

-- Scans, like folds, use an explicit rule for the captured parameter.
example : ComputableTidilyInPolyTime (fun p : List ℕ × ℕ => p.1.any fun n => decide (p.2 = n))
    (encPair (encList encNat) encNat) encBool :=
  ComputableTidilyInPolyTime.anyWith (ComputableTidilyInPolyTime.decide_eq encNat)
    (ComputableTidilyInPolyTime.snd (encList encNat) encNat)
    (ComputableTidilyInPolyTime.fst (encList encNat) encNat)

-- Both raw and framed lists infer the element encoding for unary lengths, and parameterized
-- maps/flatMaps accept polynomial-sized intermediate lists and captured parameters.
example :
    ComputableTidilyInPolyTime (fun w : List Bool => List.range w.length)
      encBits (encList encUnary) ∧
    ComputableTidilyInPolyTime (fun l : List ℕ => List.range l.length)
      (encList encNat) (encList encUnary) ∧
    ComputableTidilyInPolyTime (fun n => (List.range n).map fun i => (n, i))
      encUnary (encList (encPair encUnary encUnary)) ∧
    ComputableTidilyInPolyTime
      (fun p : ℕ × List ℕ => (List.range p.1).flatMap fun i => p.2.map fun j => i + j)
      (encPair encUnary (encList encUnary)) (encList encUnary) :=
  ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop⟩

example : ComputableTidilyInPolyTime (fun n => (List.range n).flatMap fun i => List.replicate i n)
    encUnary (encList encUnary) := by
  have hrep := (ComputableTidilyInDegree.replicate encUnary).computableTidilyInPolyTime.comp
    ((ComputableTidilyInPolyTime.snd encUnary encUnary).prod
      (ComputableTidilyInPolyTime.fst encUnary encUnary))
  exact ComputableTidilyInPolyTime.flatMapWith hrep .id' ComputableTidilyInPolyTime.range

-- Filtering also accepts a parameter and a list whose encoded length grows polynomially.
example : ComputableTidilyInPolyTime
    (fun n => (List.range (n * n)).filter fun i => decide (i < n))
    encUnary (encList encUnary) := by
  have htest : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.2 < p.1))
      (encPair encUnary encUnary) encBool :=
    ComputableTidilyInPolyTime.unary_lt.comp
      ((ComputableTidilyInPolyTime.snd encUnary encUnary).prod
        (ComputableTidilyInPolyTime.fst encUnary encUnary))
  exact ComputableTidilyInPolyTime.filterWith htest .id' (by fun_prop)

-- A fixed list needs no encoding of its elements, even when their type lives in a larger universe.
example {ι : Type 1} (l : List ι) :
    ComputableTidilyInPolyTime (fun n : ℕ => l.map fun _ => n) encUnary (encList encUnary) := by
  fun_prop

-- Signed subtraction feeds the magnitude operation, with both natural results in unary.
example : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => ((p.1 : ℤ) - p.2).natAbs)
    (encPair encUnary encUnary) encUnary := by
  fun_prop

example : ComputableTidilyInPolyTime (fun z : ℤ => (z + 1, (z - 1).natAbs))
    encInt (encPair encInt encUnary) := by
  fun_prop

-- Negative tape positions retain their existing numbering when emitted in binary.
example : ComputableInPolyTime
    (fun n => (Turing.windowList n).map Equiv.intEquivNat) encUnary (encList encNat) :=
  (ComputableInPolyTime.map
    (ComputableInPolyTime.unary_to_binary.comp
      ComputableTidilyInPolyTime.int_equivNat.computableInPolyTime)).comp
    Turing.computableInPolyTime_windowList

-- Unary loop bounds can be evaluated and enumerated for every fixed polynomial and exponent.
example (p : Polynomial ℕ) (c d : ℕ) :
    ComputableTidilyInPolyTime
      (fun w : List Bool => List.range (c * (2 * w.length + 1 + p.eval w.length + 1) ^ d))
      encBits (encList encUnary) := by
  fun_prop

-- Labels generated from unary loop indices can be emitted in binary.
example : ComputableTidilyInPolyTime (fun n => (List.range n).map fun i => Nat.pair n i)
    encUnary (encList encNat) :=
  ComputableTidilyInPolyTime.mapWith
    (ComputableTidilyInPolyTime.unary_to_binary.comp ComputableTidilyInPolyTime.unary_pair)
    .id' ComputableTidilyInPolyTime.range

example : ComputableTidilyInPolyTime (fun q : ℕ × ℕ => (decide (q.1 < q.2), q.1 - q.2))
    (encPair encUnary encUnary) (encPair encBool encUnary) := by
  fun_prop

-- This uses the parameter function called by `reduce`, with an arbitrary instance encoding.
example {α : Type} (enc : α ↪ List Bool) (p : Polynomial ℕ) (c d : ℕ) :
    ComputableTidilyInPolyTime
      (fun a => List.range (Cslib.Complexity.CookLevin.parameters p c d enc a).2.2)
      enc (encList encUnary) := by
  fun_prop

private def finish (move : SignType) (symbol : Bool) : Turing.MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ => ⟨move, Fin.elim0, some symbol, none⟩

private def bit : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; simpa using h⟩

-- A deterministic machine that has halted after `t` steps satisfies the time bound `t`.
example (symbol : Bool) :
    ComputableInTimeAndSpace (fun _ : Bool => symbol) bit bit
      (fun b => if b then 1 else 2) (fun _ => 0) := by
  refine ⟨0, Unit, inferInstance, finish 0 symbol, fun b ↦ ?_⟩
  have h : ((finish 0 symbol).runFrom ((finish 0 symbol).initCfg (bit b)) 1).Halted ∧
      ((finish 0 symbol).runFrom ((finish 0 symbol).initCfg (bit b)) 1).output = bit symbol := by
    rw [runFrom, Function.iterate_one, step_of_state rfl]
    simp [finish, Turing.Cfg.Halted]; rfl
  exact ⟨⟨1, h⟩, (runsInTime_iff_halted.mpr h.1).mono (by cases b <;> decide), by simp⟩


/-- `length_le_length_encList` holds in higher universes and on concrete lifted lists. -/
example :
    let enc : ULift.{1} Bool ↪ List Bool :=
      ⟨fun b => [b.down], fun _ _ h => ULift.ext (by simpa using h)⟩
    let l : List (ULift.{1} Bool) := [ULift.up true, ULift.up false, ULift.up true]
    l.length = 3 ∧ l.length ≤ (Turing.MultiTapeTM.encList enc l).length :=
  ⟨rfl, Turing.MultiTapeTM.length_le_length_encList _ _⟩

-- Fixed division covers both degenerate constants and compositions of computed unary counters.
example (divisor : ℕ) :
    ComputableTidilyInPolyTime (fun n : ℕ => n / 0) encUnary encUnary ∧
    ComputableTidilyInPolyTime (fun n : ℕ => n / 1) encUnary encUnary ∧
    ComputableTidilyInPolyTime
      (fun p : ℕ × ℕ => ((p.1 + p.2) / divisor == p.2, (p.1 * p.2 + 1) / 2))
      (encPair encUnary encUnary) (encPair encBool encUnary) :=
  ⟨by fun_prop, by fun_prop, by fun_prop⟩

end ComplexityTests.MultiTapePolyTime
