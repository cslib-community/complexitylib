/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Nat.Size
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm

/-!
# Addition and multiplication with bounds of given degrees

Natural numbers are encoded in binary (`Turing.MultiTapeTM.encNat`). Both results are tidy forms of
the schoolbook certificates `Turing.MultiTapeTM.ComputableInO.natAdd` and
`Turing.MultiTapeTM.ComputableInO.natMul`.

## Main results

* `Turing.MultiTapeTM.computableTidilyInDegree_add`: addition in quadratic time and space.
* `Turing.MultiTapeTM.computableTidilyInDegree_mul`: multiplication in cubic time and space.
-/

namespace Turing.MultiTapeTM

/-- A `ComputableInO` certificate with bounds of degrees `d` and `e ≤ d` is tidy within them. -/
private theorem ComputableInO.computableTidilyInDegree {f : ℕ × ℕ → ℕ} {T S : ℕ × ℕ → ℕ}
    {d e : ℕ} (h : ComputableInO f (encPair encNat encNat) encNat T S)
    (hT : DegreeBounded (fun p => (encPair encNat encNat p).length) T d)
    (hS : DegreeBounded (fun p => (encPair encNat encNat p).length) S e) (hed : e ≤ d) :
    ComputableTidilyInDegree f (encPair encNat encNat) encNat d e := by
  obtain ⟨c, hc, hl⟩ := Internal.NormalForm.inO h
  have hs := (hS.add_const 1).smul c
  exact ⟨⟨_, _, (hT.add_const 1).smul c, hs.mono_deg hed, hc⟩, hs.mono hl⟩

/-- **Addition is tidily computable in quadratic time and space**, in the binary encoding. -/
public theorem computableTidilyInDegree_add :
    ComputableTidilyInDegree (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat 2 1 :=
  ComputableInO.natAdd.computableTidilyInDegree ⟨1, fun _ => by simp⟩ ⟨1, fun _ => by simp⟩
    (by decide)

/-- **Multiplication is tidily computable in cubic time and space**, in the binary encoding. -/
public theorem computableTidilyInDegree_mul :
    ComputableTidilyInDegree (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat 3 1 :=
  ComputableInO.natMul.computableTidilyInDegree ⟨1, fun _ => by simp⟩ ⟨1, fun _ => by simp⟩
    (by decide)

end Turing.MultiTapeTM
