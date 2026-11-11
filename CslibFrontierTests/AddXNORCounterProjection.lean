/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import all CslibFrontier.Cryptanalysis.AddXNORSourceCounterCounts

/-!
# Actual full-width projection and source half-count clients

The input words retain high bits. Both forward and inverse tables are computed
through modular projection and the installed DP, including empty/zero-depth and
residual-quarter cases. The general endpoints have no execution/counting premise.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR
namespace CslibFrontierTests.AddXNORCounterProjection

example : CounterProjection.prepare (CounterProjection.ofWords 2 false 9#4 [13#4, 6#4]) =
    CounterDP.ofWords false 1#2 [1#2, 2#2] := by decide

/-- Original high bits are present on the input tape but do not become extra class states. -/
example : CounterProjection.run (CounterProjection.ofWords 2 false 8#4 [13#4, 6#4]) =
    [(0, 2), (1, 0), (2, 0), (3, 2)] := by decide
example : CounterProjection.run (CounterProjection.ofWords 2 true 8#4 [13#4, 6#4]) =
    [(0, 2), (1, 1), (2, 0), (3, 1)] := by decide

/-- Non-self-inverse addition distinguishes forward counts from inverse-to-target counts. -/
example : CounterProjection.run (CounterProjection.ofWords 3 false 8#4 [9#4, 10#4]) =
    [(0, 1), (1, 0), (2, 0), (3, 2), (4, 1), (5, 0), (6, 0), (7, 0)] := by decide
example : CounterProjection.run (CounterProjection.ofWords 3 true 8#4 [9#4, 10#4]) =
    [(0, 1), (1, 0), (2, 0), (3, 1), (4, 1), (5, 1), (6, 0), (7, 0)] := by decide

example : CounterProjection.run (CounterProjection.ofWords 0 false 9#4 [13#4, 6#4]) =
    [(0, 4)] := by decide
example : CounterProjection.prepare (CounterProjection.ofWords 8 true 1#2 []) =
    CounterDP.ofWords true 1#2 [] := by decide
example : CounterProjection.run (CounterProjection.ofWords 2 true 9#4 []) =
    [(0, 0), (1, 1), (2, 0), (3, 0)] := by decide

/-- Arbitrary original inputs produce all source class counts without a semantic oracle. -/
example {m p n : ℕ} (hp : p ≤ m) (as : Fin n → BitVec m) (seed : BitVec m)
    (inverse : Bool) :
    CounterProjection.run (CounterProjection.ofWords p inverse seed (List.ofFn as)) =
      List.ofFn (fun g : Fin (2^p) => (g.val,
        if inverse then backwardClassCount p as seed (BitVec.ofFin g)
        else forwardClassCount p as seed (BitVec.ofFin g))) :=
  CounterProjection.run_classes hp as seed inverse

example : SourceCounterCounts.run (Source.ofWords 1 8#4 []) = ([(0, 1)], [(0, 1)]) := by decide

/-- Residual fourth-quarter operands are consumed by the backward half. -/
example : SourceCounterCounts.task (Source.ofWords 1 8#4 [9#4, 10#4, 11#4, 12#4, 13#4]) true =
    CounterProjection.ofWords 1 true 0#4 [11#4, 12#4, 13#4] := by decide

example : SourceCounterCounts.run (Source.ofWords 1 8#4 [9#4, 10#4, 11#4, 12#4]) =
    ([(0, 2), (1, 2)], [(0, 2), (1, 2)]) := by decide

/-- One actual machine, not a fixed-width instance or a supplied simulation. -/
example : IsComputable SourceCounterCounts.run Source.encoding SourceCounterCounts.countEncoding :=
  SourceCounterCounts.runCertificate.isComputable

/-- Quarter-time source prepass on arbitrary original input, with all intermediate tapes charged. -/
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ m p (a : BitVec m) (tail : List (BitVec m)),
      SourceCounterCounts.runCertificate.time (Source.ofWords p a tail) ≤
        2^(tail.length/4)*P ((Source.encoding (Source.ofWords p a tail)).length+1) ∧
      SourceCounterCounts.runCertificate.space (Source.ofWords p a tail) ≤
        2^(tail.length/4)*P ((Source.encoding (Source.ofWords p a tail)).length+1) :=
  SourceCounterCounts.quarter_certificate

end CslibFrontierTests.AddXNORCounterProjection
