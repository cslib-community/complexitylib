/-
Copyright (c) 2026 Samuel Schlesinger, real-roots. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, real-roots
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.PrimeModulus
public import CslibFrontier.Crypto.Game.Hybrid

/-!
# Search to Decision LWE

Regev's search-to-decision reduction for prime moduli.

## References

* [O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*][Regev2009]
-/

public section

namespace Cslib.Crypto.PrimeLWE

open Probability Turing.MultiTapeTM

-- TODO: W' iterates over all coordinates i=1..n, and guesses s_i \in Z_q.
-- It shifts a_i \mapsto a_i + r \cdot e_i and distinguishes using DecisionLWE and Hybrid.lean.

end Cslib.Crypto.PrimeLWE
