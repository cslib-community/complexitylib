/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.MultiNPHard
import CslibFrontier.Computability.MCSP.Multi.NP
import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Tests for the NP-hardness of Multi-MCSP

Instances of `CslibFrontier.Computability.MCSP.MultiNPHard` for the source's constant-free basis
(`Boolean.DeMorgan.interpretation`, Definition 1) and cslib's basis with constants
(`Boolean.interpretation`):

1. The reduction from `GapSetCover 3` runs in polynomial time, so the randomized reduction holds
   with no hypothesis.
2. Every `NP` problem reduces to Multi-MCSP, on positive instances and in general.
3. With `MultiMCSP.mem_NP`, Multi-MCSP over the constant-free basis reduces to itself on positive
   instances.
4. The conditional consequences for `BPP` and `coRP`.
-/

namespace CslibFrontierTests.MultiMCSPNPHard

open Cslib Cslib.Circuits Cslib.Complexity Cslib.Complexity.PromiseProblem Cslib.MultiMCSP
open Turing.MultiTapeTM

/-! ### The reduction from `GapSetCover 3` -/

example : ComputableInPolyTime Reduction.reduce (encPair encSetCover encBits) encInstance :=
  Reduction.computableInPolyTime_reduce

example : RPReducible encSetCover encInstance (GapSetCover 3)
    ((ofSet (MultiMCSP Boolean.DeMorgan.interpretation)).restrict {x | x.Positive}) :=
  rpReducible_gapSetCover

example : RPReducible encSetCover encInstance (GapSetCover 3)
    ((ofSet (MultiMCSP Boolean.interpretation)).restrict {x | x.Positive}) :=
  rpReducible_gapSetCover

/-! ### Hardness for `NP` -/

example {α : Type} {encA : α ↪ List Bool} (A : Set α) (hA : A ∈ NP encA) :
    RPReducible encA encInstance (ofSet A) (ofSet (MultiMCSP Boolean.DeMorgan.interpretation)) :=
  rpHard A hA

example {α : Type} {encA : α ↪ List Bool} (A : Set α) (hA : A ∈ NP encA) :
    RPReducible encA encInstance (ofSet A) (ofSet (MultiMCSP Boolean.interpretation)) :=
  rpHard A hA

example {α : Type} {encA : α ↪ List Bool} (A : Set α) (hA : A ∈ NP encA) :
    RPReducible encA encInstance (ofSet A)
      ((ofSet (MultiMCSP Boolean.DeMorgan.interpretation)).restrict {x | x.Positive}) :=
  rpHard_pos A hA

/-- Multi-MCSP over the constant-free basis is in `NP`, so it reduces to its own positive
instances. -/
example : RPReducible encInstance encInstance (ofSet (MultiMCSP Boolean.DeMorgan.interpretation))
    ((ofSet (MultiMCSP Boolean.DeMorgan.interpretation)).restrict {x | x.Positive}) :=
  rpHard_pos _ mem_NP

/-! ### Conditional consequences -/

example {α : Type} {encA : α ↪ List Bool}
    (h : MultiMCSP Boolean.DeMorgan.interpretation ∈ BPP encInstance) : NP encA ⊆ BPP encA :=
  NP_subset_BPP_of_mem_BPP h

example {α : Type} {encA : α ↪ List Bool}
    (h : MultiMCSP Boolean.interpretation ∈ coRP encInstance) : NP encA ⊆ coRP encA :=
  NP_subset_coRP_of_mem_coRP h

end CslibFrontierTests.MultiMCSPNPHard
