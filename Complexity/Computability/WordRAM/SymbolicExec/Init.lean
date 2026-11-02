/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init

/-!
# The simp set of `wram_exec`

The simp set used by `wram_exec` and `wram_simp` in `Complexity.Computability.WordRAM.SymbolicExec`,
declared in a file of its own because an attribute cannot be used in the file declaring it. Lemmas
and simplification procedures are tagged where they are proved. A simp set is indexed once, when
its lemmas are tagged, so a call that uses it does not index its lemmas again; `wram_exec` and
`wram_simp` run often in a long proof.

## Main definitions

* `wram_simps`: reads of registers and memory after writes, and arithmetic identities.
-/

public meta section

/-- The simp set `wram_simps` reads registers and memory after `Data.set` and `Data.write`, and
simplifies arithmetic identities, for `wram_exec` and `wram_simp`. -/
register_simp_attr wram_simps

end
