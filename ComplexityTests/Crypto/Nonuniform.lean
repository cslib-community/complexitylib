/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Nonuniform.ZeroKnowledge
import Complexity.Crypto.Computational.Stretch

/-! Checked clients of the nonuniform security notions. Existence of a nonuniform one-way
function or generator is open, so these checks show that the notions are not trivially true
(constant functions, fixed words and length-wise constant generators fail them) and that the
indistinguishability notion is not trivially false. They do not separate the nonuniform notions
from the uniform ones. -/

namespace ComplexityTests.Crypto.Nonuniform

open Cslib Cslib.Crypto

/-- A constant function is not nonuniformly one-way, because it is not even uniformly one-way. -/
example (word : List Bool) : ¬ NonuniformOneWay (fun _ => word) :=
  fun h => not_oneWay_const word h.toOneWay

/-- The nonuniform indistinguishability relation holds between equal ensembles. -/
example : NonuniformlyIndistinguishable (fun n => BitString.uniformList n)
    (fun n => BitString.uniformList n) :=
  NonuniformlyIndistinguishable.refl _

/-- The all-`true` words are distinguishable from uniform words of each positive length. -/
example : ¬ NonuniformlyIndistinguishable (fun n => PMF.pure (List.replicate n true))
    (fun n => BitString.uniformList n) :=
  not_nonuniformlyIndistinguishable_pure_uniformList _ (Filter.eventually_ge_atTop 1)

/-- A generator that, at each seed length, outputs one fixed word of the right length is not a
nonuniform PRG (nor a uniform one): its output's first bit is constant. -/
example : ¬ NonuniformPRG (fun seed => List.replicate (seed.length + 1) false) (· + 1) := by
  intro h
  refine not_nonuniformlyIndistinguishable_pure_uniformList (fun n => List.replicate (n + 1) false)
    (.of_forall fun n => Nat.le_add_left 1 n) ?_
  have hensemble :
      generatorEnsemble (fun seed => List.replicate (seed.length + 1) false) =
        fun n => PMF.pure (List.replicate (n + 1) false) := by
    funext n
    rw [generatorEnsemble_postprocess (fun _ => []) (fun n _ => List.replicate (n + 1) false)]
    simp only [generatorEnsemble, PMF.map_comp]
    exact PMF.map_const _ _
  have hsecure := h.secure
  rw [hensemble] at hsecure
  exact hsecure

/-- The nonuniform generator premise gives the GMW advice premise for CNF instances. -/
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) :
    GMW.AdvicePRG Complexity.encCNF generator length :=
  h.advicePRG _

/-- With empty advice, indistinguishability with advice is uniform indistinguishability, so the
uniform first-bit separation transfers. -/
example : ¬ IndistinguishableWithAdvice (fun _ => []) (fun n => PMF.pure (List.replicate n true))
    (fun n => BitString.uniformList n) := fun h =>
  not_computationallyIndistinguishable_pure_uniformList _ (Filter.eventually_ge_atTop 1)
    (computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil.mpr h)

/-- Stretching a nonuniform one-bit PRG to `3 * n + 1` bits, the GMW length, and feeding it to the
auxiliary-input GMW theorem. -/
example {generator : List Bool → List Bool} (h : NonuniformPRG generator (fun n => n + 1))
    {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ Complexity.NP enc) :
    ∃ zk : ZeroKnowledgeProof enc A, zk.AuxiliaryInputZeroKnowledge :=
  (h.amplify (fun n => 3 * n + 1) (by fun_prop) (fun n => by omega))
    |>.exists_auxiliaryInputZeroKnowledge_of_mem_NP (fun _ => le_rfl) hA

end ComplexityTests.Crypto.Nonuniform
