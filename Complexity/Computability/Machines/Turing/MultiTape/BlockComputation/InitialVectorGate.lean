/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.InitialVectorCorrect
public import Complexity.Computability.TreeEval.Ary.Packed.Constant
import Complexity.Foundations.Data.List.Lookup

/-!
# Initial vectors supply padded source gates

Internal source padding is a constant Boolean gate. Its extension at an arbitrary field point
is therefore the same paid initial vector already used for leaves.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.InitialVector

open Cslib.TreeEval.Ary

/-- Paid source vectors compute the existing constant gate extension at every field point. -/
theorem values_gateExtension_zero {k s p q r m : ℕ} {Q : Type} [Fact p.Prime]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (limit b : ℕ) [NeZero b] (σ : Schedule k q)
    (hcapacity : r ≤ limit.size) (hb : Encoding.width k s b ≤ r * m)
    (h : Fin (2 ^ m) ↪ ZMod p) (hh : ∀ a, h a = (a.val : ZMod p))
    (x : Fin (k * 3 + 1) → Fin r → ZMod p) (j : Fin r) :
    ((values M e (limit, m, r)).getD j.val 0 : ZMod p) =
      Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb)
        (codeGate (MultiTapePTM.ofDeterministic M) w b σ
          (Encoding.encode e) (Encoding.decode e) 0) x j := by
  rw [values_eq_packBits M e limit b hcapacity hb, List.getD_ofFn_of_lt _ j.isLt 0]
  change _ = Packed.gateExtension h (Packed.packBits hb) (Packed.unpackBits hb)
    (fun _ => Encoding.encode e (some (initialView (MultiTapePTM.ofDeterministic M) b))) x j
  rw [Packed.gateExtension_const, hh]

end Turing.MultiTapePTM.BlockComputation.InitialVector
