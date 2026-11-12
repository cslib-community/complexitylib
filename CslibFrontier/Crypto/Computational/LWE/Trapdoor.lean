/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.Trapdoor.Basic
public import CslibFrontier.Crypto.Computational.LWE.Trapdoor.Gadget

/-!
# Micciancio–Peikert Gadget Trapdoors for LWE

Root module re-exporting the power-of-two primitive gadget matrices, short kernel matrices, and
gadget LWE inversion (`CslibFrontier.Crypto.Computational.LWE.Trapdoor.Gadget`) together with the
Micciancio–Peikert (2012) gadget-based trapdoor construction (`GenTrap`, syndrome lifting,
lifted kernel vectors, and deterministic trapdoor LWE inversion in
`CslibFrontier.Crypto.Computational.LWE.Trapdoor.Basic`).
-/
