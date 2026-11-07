/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.RawController

/-!
# Canonical zero-bank initialization

The raw encoding of the typed evaluator's initial zero registers consists of one
modulus-padded zero per bank cell and the initial call control.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.RawController

/-- A zero field bank retains one modulus-padded cell for each register coordinate. -/
theorem ofRegs_zero {p d r : ℕ} :
    ofRegs (0 : Ary.State (ZMod p) d r) = List.replicate ((d + 1) * r) p := by
  simp only [ofRegs, Pi.zero_apply, ZMod.val_zero, Nat.add_zero, List.ofFn_const]

/-- The initial typed call has precisely the freshly allocated zero-bank representation. -/
theorem ofCfg_initial_zero {p d r : ℕ} [Fact p.Prime] :
    ofCfg (Iter.initialCfg (0 : Ary.State (ZMod p) d r) 1 (0 : Fin (d + 1))) =
      (List.replicate ((d + 1) * r) p, [], some (1, 0)) := by
  simp only [ofCfg, Iter.initialCfg, ofRegs_zero, List.map_nil, ofMode,
    ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt, Fin.val_zero]

end Cslib.TreeEval.Ary.Packed.RawController
