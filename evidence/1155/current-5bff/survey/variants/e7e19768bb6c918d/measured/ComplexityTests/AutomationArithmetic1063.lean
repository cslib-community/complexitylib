/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.Complexity.Classes.PH.KarpLipton
import Complexity.Computability.Complexity.Classes.ZPP
import Complexity.Computability.MCSP.NP
import Complexity.Computability.Circuit.Boolean.Advice
import Complexity.Computability.Circuit.Boolean.PolynomialTime
import Complexity.Computability.Complexity.Classes.Hierarchy.Nondeterministic
import Complexity.Computability.Complexity.Classes.Padding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure


import Diag1155.Measure
/-! Both original automatic arithmetic blocks from #1063, with their concrete functions,
all five arbitrary constants and the original locally derived `hf`. Hardness assumptions and
circuit witnesses do not enter these arithmetic goals. These are not the explicit production
composition proofs. No missing-certificate negative is invented for a closed arithmetic function.
-/

diag1155_install
open Turing.MultiTapeTM Cslib.MCSP Cslib.Circuits.Boolean
open ComputableTidilyInPolyTime

set_option maxHeartbeats 200000 in
-- Pin the original default as the regression budget; do not raise it.
example (k c_R d_R c_M d_M : ℕ) : True := by
  let f (n : ℕ) : ℕ := n ^ (k + 1) + 1
  have hf : ComputableInPolyTime f encUnary encUnary := by
    unfold f
    fun_prop
  let m_bound (n : ℕ) : ℕ := c_R + (f n + 2) * d_R
  let s_bound (n : ℕ) : ℕ := c_M * (2 * n + 1 + m_bound n + 1) ^ d_M + 2
  let g (n : ℕ) : ℕ := certLength (m_bound n) (s_bound n) + n
  have hs_bound : ComputableInPolyTime s_bound encUnary encUnary := by
    unfold s_bound m_bound f
    fun_prop
  have hg : ComputableInPolyTime g encUnary encUnary := by
    unfold g certLength s_bound m_bound f
    fun_prop
  trivial
