/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import all CslibFrontier.Cryptanalysis.AddXNORDPDissection

/-!
# Actual scalar balance and DP-prepass dissection clients

Execute binary pair minima, tagged table alignment, original-input count/prepass
composition and the complete witness/miss solver. General endpoints do not take
completed counters, executions or desired resources as hypotheses.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR
namespace CslibFrontierTests.AddXNORCounterBalanceScan

example : PairMaxMin.run [] = 0 := rfl
example : PairMaxMin.run [(8, 3), (4, 11), (0, 17)] = 4 := rfl
example : PairMaxMin.run [(2^20, 2^30), (2^31, 2^19)] = 2^20 := by decide

/-- The same numeric class key is paired even if many counter values collide or are zero. -/
example : CounterBalanceScan.pairs (2,
    ([(0, 3), (1, 0), (2, 3), (3, 2)], [(0, 0), (1, 8), (2, 3), (3, 7)])) =
    [(3, 0), (0, 8), (3, 3), (2, 7)] := by decide
example : CounterBalanceScan.run (2,
    ([(0, 3), (1, 0), (2, 3), (3, 2)], [(0, 0), (1, 8), (2, 3), (3, 7)])) = 3 := by decide

example {p : ℕ} (left right : BitVec p → ℕ) :
    CounterBalanceScan.run (p, (CounterPull.graph left, CounterPull.graph right)) =
      Finset.univ.sup (fun g => min (left g) (right g)) :=
  CounterBalanceScan.run_graphs left right

example : SourceCounterBalance.run (Source.ofWords 2 0#2 []) = 1 := by decide
example : SourceCounterBalance.run (Source.ofWords 0 0#2 [0#2, 0#2, 0#2, 0#2]) = 4 := by decide
example : SourceCounterBalance.run (Source.ofWords 1 8#4 [9#4, 10#4, 11#4, 12#4, 13#4]) = 2 := by
  decide
example : SourceCounterBalance.run (Source.ofWords 2 1#2
    [0#2, 0#2, 0#2, 0#2, 0#2, 0#2, 0#2, 0#2]) = 0 := by decide

/-- The actual faster source prepass, for arbitrary original widths and operand tapes. -/
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (a : BitVec m) (tail : List (BitVec m)),
      SourceCounterBalance.runCertificate.time (Source.ofWords p a tail) ≤
        2^(tail.length/4)*P ((Source.encoding (Source.ofWords p a tail)).length+1) ∧
      SourceCounterBalance.runCertificate.space (Source.ofWords p a tail) ≤
        2^(tail.length/4)*P ((Source.encoding (Source.ofWords p a tail)).length+1) :=
  SourceCounterBalance.source_certificate

example : DPDissection.run (Source.ofWords 2 0#2 []) = (1, some []) := by decide
example : DPDissection.run (Source.ofWords 2 1#2 []) = (1, none) := by decide
example : (DPDissection.run (Source.ofWords 1 0#2 [1#2, 2#2, 3#2, 0#2])).2.isSome = true := by
  decide

example : IsComputable DPDissection.run Source.encoding DPDissection.outputEncoding :=
  DPDissection.sourceCertificate.isComputable

/-- Complete source witness/miss correctness after installing the actual DP scalar prepass. -/
example {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :
    let (_, result) := DPDissection.run (Source.ofWords p s tail)
    (result = none ↔ ¬ Solvable tail s 0) ∧
      ∀ ops, result = some ops → ops.length = tail.length ∧ eval (ops.zip tail) s = 0 :=
  DPDissection.original_correct p s tail

/-- The whole-run envelope uses the actual returned scalar; its equality with the
search balance is derived by the source compatibility proof, not supplied as a premise. -/
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (s : BitVec m) (tail : List (BitVec m)),
      let original := Source.ofWords p s tail
      let I := (Source.encoding original).length
      DPDissection.sourceCertificate.time original ≤ 2^(tail.length/2)*P I ∧
        DPDissection.sourceCertificate.space original ≤
          (2^(tail.length/4)+(DPDissection.run original).1)*P I :=
  DPDissection.sourceCertificate_bounds

/-- The polynomial overhead is in original scalar parameters, not a materialized half space. -/
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (s : BitVec m) (tail : List (BitVec m)), p ≤ m →
      DPDissection.sourceCertificate.time (Source.ofWords p s tail) ≤
        2^(tail.length/2)*P (m+tail.length+1) ∧
      DPDissection.sourceCertificate.space (Source.ofWords p s tail) ≤
        (2^(tail.length/4)+(DPDissection.run (Source.ofWords p s tail)).1)*P (m+tail.length+1) :=
  DPDissection.source_parameter_bounds

end CslibFrontierTests.AddXNORCounterBalanceScan
