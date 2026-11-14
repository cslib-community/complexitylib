/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Languages.Probabilistic.UniformNat
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
import Cslib.Probability.PMF
import CslibFrontier.Foundations.Data.ZMod.Basic

/-!
# Binary samples as canonical residues

`sampleBinaryNat w` reads `w` fair bits as a natural number below `2 ^ w`. These are exactly the
canonical representatives `ZMod.val` of the residues modulo `2 ^ w`, so the sampler draws the
canonical representative of a uniform residue. Repeating it lists the representatives of a uniform
residue vector, in coordinate order, and repeating those runs lists the rows of a uniform residue
matrix. Every count and the width may be zero; at width zero every sample is `0`, the only
representative modulo `1`.

## Main results

* `Cslib.ProbComp.eval_sampleBinaryNat_eq_map_val`: one sample is the representative of a uniform
  residue modulo `2 ^ w`.
* `Cslib.ProbComp.eval_replicate_sampleBinaryNat`: `count` samples list the representatives of a
  uniform residue vector.
* `Cslib.ProbComp.eval_replicate_replicate_sampleBinaryNat`: `rows` lists of `cols` samples list,
  row by row, the representatives of a uniform `rows × cols` residue matrix.
-/

public section

namespace Cslib.ProbComp

open Probability

/-- An unsigned `w`-bit sample is the canonical representative of a uniform residue modulo
`2 ^ w`. -/
theorem eval_sampleBinaryNat_eq_map_val (w : ℕ) :
    eval (sampleBinaryNat w) = (PMF.uniformOfFintype (ZMod (2 ^ w))).map ZMod.val := by
  rw [eval_sampleBinaryNat,
    ← PMF.uniformOfFintype_map_equiv (ZMod.finEquiv (2 ^ w)).toEquiv, PMF.map_comp]
  simp only [Function.comp_def, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ZMod.val_finEquiv]

/-- `count` independent unsigned `w`-bit samples list the canonical representatives of a uniform
residue vector modulo `2 ^ w`. -/
theorem eval_replicate_sampleBinaryNat (count w : ℕ) :
    eval (OracleComp.replicate count (sampleBinaryNat w)) =
      (PMF.uniformOfFintype (Fin count → ZMod (2 ^ w))).map
        fun x => List.ofFn fun j => (x j).val :=
  eval_replicate_of_uniform count _ _ (eval_sampleBinaryNat_eq_map_val w)

/-- `rows` independent lists of `cols` unsigned `w`-bit samples list, row by row, the canonical
representatives of a uniform `rows × cols` residue matrix modulo `2 ^ w`. -/
theorem eval_replicate_replicate_sampleBinaryNat (rows cols w : ℕ) :
    eval (OracleComp.replicate rows (OracleComp.replicate cols (sampleBinaryNat w))) =
      (PMF.uniformOfFintype (_root_.Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w)))).map
        fun A => List.ofFn fun i => List.ofFn fun j => (A i j).val :=
  eval_replicate_of_uniform rows _ _ (eval_replicate_sampleBinaryNat cols w)

end Cslib.ProbComp
