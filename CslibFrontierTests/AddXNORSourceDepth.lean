/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Cryptanalysis.AddXNORSourceDepth
-- Evaluate the installed scalar prepass through its unexposed implementation dependencies.
import all CslibFrontier.Cryptanalysis.AddXNORDPDissection
-- Evaluate the unexposed exhaustive reachable-state specification on finite examples.
import all CslibFrontier.Cryptanalysis.AddXNORSmallOperands

/-!
# Depth above the physical width and small-operand populations

Actual DP scalars agree with requested wider class labels, including zero-width
words. Small-operand populations include wraparound and complements of high seeds.
-/

public section
namespace CslibFrontierTests.AddXNORSourceDepth
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

example : SourceCounterBalance.run (Source.ofWords 2 0#1
    [0#1, 0#1, 0#1, 0#1, 0#1, 0#1, 0#1, 0#1]) = 8 := by decide
example : SourceCounterBalance.run (Source.ofWords 1 0#0 [0#0, 0#0, 0#0, 0#0]) = 4 := by decide

/-- Above physical width, some labels are empty even for a uniform seed. -/
example : forwardClassCount 2 (fun _ : Fin 0 => 0#1) 0#1 2#2 = 0 := by decide

/-- Zero-extension of already evaluated states is valid; running lifted arithmetic is not. -/
example : ((1#1+1#1).setWidth 2) ≠ (1#1).setWidth 2+(1#1).setWidth 2 := by decide

example {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m))
    (hk : p ≤ tail.length / 4) :
    let left := SourceCounterCounts.forwardOperands tail
    let right := SourceCounterCounts.backwardOperands tail
    (DPDissection.run (Source.ofWords p s tail)).1 = classBalance p
      (fun i : Fin left.length => left[i.val]) (fun i : Fin right.length => right[i.val]) s 0 :=
  DPDissection.original_classBalance_quarter p s tail hk

example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (s : BitVec m) (tail : List (BitVec m)), p ≤ tail.length/4 →
      DPDissection.sourceCertificate.time (Source.ofWords p s tail) ≤
        2^(tail.length/2)*P (m+tail.length+1) ∧
      DPDissection.sourceCertificate.space (Source.ofWords p s tail) ≤
        (2^(tail.length/4)+(DPDissection.run (Source.ofWords p s tail)).1)*P (m+tail.length+1) :=
  DPDissection.source_quarter_depth_bounds

example : (SmallOperands.reachable [1#5, 2#5, 3#5] 29#5).card = 8 := by decide
example : (SmallOperands.reachable [0#4, 0#4, 0#4, 0#4] 3#4).card = 2 := by decide
example : (SmallOperands.reachable [0#0, 0#0] 0#0).card = 1 := by decide
example : (SmallOperands.reachable ([] : List (BitVec 5)) 29#5).card = 1 := by decide

example {m : ℕ} (s : ℕ) (as : List (BitVec m)) (seed : BitVec m)
    (small : ∀ a ∈ as, a.toNat < 2 ^ s) :
    (SmallOperands.reachable as seed).card ≤ 2*(2*as.length+1)*2^s :=
  SmallOperands.reachable_card_le s as seed small

end CslibFrontierTests.AddXNORSourceDepth
