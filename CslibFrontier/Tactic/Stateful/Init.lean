/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Aesop

/-!
# Stateful contract rule set

## Main definitions

* `Stateful`: Aesop rules for semantic and operation-cost contracts.
-/

public section

declare_aesop_rule_sets [Stateful]

end
