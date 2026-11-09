/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P.WordRAM
public import Complexity.Algorithms.WordRAM.ElementDistinctness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Element distinctness is in `P`, through the word RAM

The instances are lists of naturals whose entries are below their length, encoded as framed lists
of binary naturals. Membership in `P` follows from the linear-time word-RAM decider
`Cslib.Algorithms.WordRAM.ElementDistinctness.decider`
(`Cslib.Algorithms.WordRAM.ElementDistinctness.uniformLinearTime_nodup`) through the simulation of
the word RAM by multi-tape Turing machines (`Cslib.WordRAM.UniformPolynomialTime.mem_P`). No
Turing machine specific to this problem is constructed: the instance's word list is its own
underlying list, and its size is its length.

The decider uses a table of flags indexed by the entries, which is why the entries are bounded by
the length [Cormen et al., Section 11.1][CLRS2009].

## Main definitions

* `Cslib.Algorithms.WordRAM.ElementDistinctness.inputEncoding`: framed lists of binary naturals.

## Main results

* `Cslib.Algorithms.WordRAM.ElementDistinctness.nodup_mem_P`: element distinctness is in `P`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ElementDistinctness

open Cslib.WordRAM Turing.MultiTapeTM

/-- Instances as framed lists of binary naturals. -/
def inputEncoding : Input ↪ List Bool :=
  (Function.Embedding.subtype _).trans (encList encNat)

/-- **Element distinctness is in `P`**, for lists of naturals whose entries are below their
length. The decider is the word-RAM program `decider`, simulated by a multi-tape machine. -/
theorem nodup_mem_P : {l : Input | l.1.Nodup} ∈ Cslib.Complexity.P inputEncoding :=
  uniformLinearTime_nodup.polynomialTime.mem_P checkedOp_polyTime
    (PolyBounded.self.mono fun l => length_le_length_encList encNat l.1) (.of_eq fun _ => rfl)

end Cslib.Algorithms.WordRAM.ElementDistinctness
