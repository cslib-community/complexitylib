/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.RandomPermutation
import CslibFrontier.Languages.Probabilistic.Oracle.CoinFixing
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount

/-!
# Finite pseudorandom permutations

A block cipher with keys in `Key` and blocks in `D` is a keyed permutation `E : Key → Equiv.Perm D`.
In the chosen-plaintext game ([BonehShoup2023], Section 4.1.2, Attack Game 4.1) an adaptive oracle
adversary with private coins queries either `E key` for one uniform key or one uniform
permutation `π` of `D`. In the chosen-ciphertext game (strong PRP, Section 4.1.3) it may also
query the inverse, through the bidirectional interface `RandomPermutation.PermOracleSpec D`.

The PRP/PRF switching lemma ([BonehShoup2023], Theorem 4.4) bounds the advantage of a `Q`-query
adversary between a uniform permutation and a uniform function of `D` by `Q.choose 2 / |D|`
(`advantage_idealExperiment_prfIdealExperiment_le`). Hence PRP security implies PRF security up
to that term (`prfAdvantage_le_advantage_add`, Corollary 4.5). A forward adversary runs unchanged
against the bidirectional interface (`StrongAdversary.ofForward`), so strong PRP security implies
PRP security (`strongAdvantage_ofForward`).

The word-level asymptotic notions `Cslib.Crypto.BlockCipher.PRP` and
`Cslib.Crypto.BlockCipher.StrongPRP` derive their switching lemma from this one.

## Main definitions

* `Cslib.Crypto.PRP.realExperiment`, `Cslib.Crypto.PRP.idealExperiment`,
  `Cslib.Crypto.PRP.advantage`: the chosen-plaintext experiments and their advantage.
* `Cslib.Crypto.PRP.StrongAdversary`, `Cslib.Crypto.PRP.strongRealExperiment`,
  `Cslib.Crypto.PRP.strongIdealExperiment`, `Cslib.Crypto.PRP.strongAdvantage`: the
  chosen-ciphertext experiments and their advantage.
* `Cslib.Crypto.PRP.StrongAdversary.ofForward`: run a forward adversary against the bidirectional
  interface.

## Main results

* `Cslib.Crypto.PRP.advantage_idealExperiment_prfIdealExperiment_le`: the PRP/PRF switching lemma.
* `Cslib.Crypto.PRP.prfAdvantage_le_advantage_add`: a PRP is a PRF up to `Q.choose 2 / |D|`.
* `Cslib.Crypto.PRP.strongAdvantage_ofForward`: strong PRP security implies PRP security.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 4.1.2,
  Attack Game 4.1, Section 4.1.3, and Section 4.4.3, Theorem 4.4 and Corollary 4.5.
-/

@[expose] public section

namespace Cslib.Crypto.PRP

open Probability RandomPermutation
open scoped NNReal

variable {Key D : Type}

/-! ### Chosen-plaintext security -/

/-- The real chosen-plaintext experiment: sample one uniform key and answer every query `x` with
`E key x`. It is the real PRF experiment for the keyed function `E`. -/
noncomputable abbrev realExperiment [Fintype Key] [Nonempty Key] (E : Key → Equiv.Perm D)
    (A : PRF.Adversary D D) : ProbComp Bool :=
  PRF.realExperiment (fun key => ⇑(E key)) A

section Ideal

variable [Fintype D] [DecidableEq D]

/-- The ideal chosen-plaintext experiment: sample one uniform permutation `π` of `D` and answer
every query `x` with `π x`. -/
noncomputable def idealExperiment (A : PRF.Adversary D D) : ProbComp Bool := do
  let π ← ProbComp.uniform (Equiv.Perm D)
  A.run fun x => pure (π x)

/-- The PRP distinguishing advantage of `A` against `E`. -/
noncomputable abbrev advantage [Fintype Key] [Nonempty Key] (E : Key → Equiv.Perm D)
    (A : PRF.Adversary D D) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (realExperiment E A)) (ProbComp.eval (idealExperiment A))

/-- The law of `idealExperiment`: a uniform permutation `π`, then the adversary interpreted at the
`PMF` level against `π`. -/
theorem eval_idealExperiment (A : PRF.Adversary D D) :
    ProbComp.eval (idealExperiment A) =
      (PMF.uniformOfFintype (Equiv.Perm D)).bind fun π =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle fun x => PMF.pure (π x)) A := by
  simp only [idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbOracleComp.eval_run,
    ProbComp.eval_pure]

variable [Nonempty D]

/-- **PRP/PRF switching lemma** ([BonehShoup2023], Theorem 4.4): an adversary making at most `Q`
queries distinguishes a uniform permutation of `D` from a uniform function `D → D` with advantage
at most `Q.choose 2 / |D|`. -/
theorem advantage_idealExperiment_prfIdealExperiment_le {A : PRF.Adversary D D} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) :
    (Game.advantage (ProbComp.eval (idealExperiment A))
      (ProbComp.eval (PRF.idealExperiment A)) : ℝ) ≤ Q.choose 2 / Fintype.card D := by
  rw [eval_idealExperiment, PRF.eval_idealExperiment,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind (PMF.uniformOfFintype (Equiv.Perm D))
      (fun π x => π x) A,
    ProbOracleComp.table_bind_interpret_eq_coinLaw_bind (PMF.uniformOfFintype (D → D))
      (fun f x => f x) A]
  refine Game.advantage_bind_le _ _ _ fun ω => ?_
  rw [Game.coe_advantage, div_eq_mul_inv]
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    Probability.PMF.monad_bind_eq_bind, PMF.bind_pure] using abs_sub_uniformPerm_uniformFunc_le
      (ProbOracleComp.isQueryBounded_fixCoins hQ ω) PMF.pure true

/-- **A PRP is a PRF** ([BonehShoup2023], Corollary 4.5): against an adversary making at most `Q`
queries, the PRF advantage of a block cipher is at most its PRP advantage plus
`Q.choose 2 / |D|`. -/
theorem prfAdvantage_le_advantage_add [Fintype Key] [Nonempty Key] (E : Key → Equiv.Perm D)
    {A : PRF.Adversary D D} {Q : ℕ} (hQ : A.IsQueryBounded Q) :
    (PRF.advantage (fun key => ⇑(E key)) A : ℝ) ≤
      advantage E A + Q.choose 2 / Fintype.card D := by
  have h := Game.advantage_triangle (ProbComp.eval (realExperiment E A))
    (ProbComp.eval (idealExperiment A)) (ProbComp.eval (PRF.idealExperiment A))
  have hswitch := advantage_idealExperiment_prfIdealExperiment_le hQ
  have h' : (PRF.advantage (fun key => ⇑(E key)) A : ℝ) ≤
      advantage E A + Game.advantage (ProbComp.eval (idealExperiment A))
        (ProbComp.eval (PRF.idealExperiment A)) := by
    exact_mod_cast h
  linarith

end Ideal

/-! ### Strong pseudorandom permutations -/

/-- An adaptive test with private coins and oracle access to a permutation of `D` and its inverse:
`.forward x` asks for `π x` and `.inverse y` asks for `π.symm y`. -/
abbrev StrongAdversary (D : Type) := ProbOracleComp (PermOracleSpec D) Bool

/-- Run a forward adversary against the bidirectional interface, sending every query to the
forward direction. Private samples are unchanged. -/
def StrongAdversary.ofForward (A : PRF.Adversary D D) : StrongAdversary D :=
  ProbOracleComp.simulate
    (fun x => ProbOracleComp.query (spec := PermOracleSpec D) (PermQuery.forward x)) A

/-- Running `ofForward A` against any bidirectional oracle runs `A` against its forward direction.
-/
@[simp] theorem StrongAdversary.run_ofForward (A : PRF.Adversary D D)
    (O : (q : PermQuery D) → ProbComp D) :
    (StrongAdversary.ofForward A).run O = A.run fun x => O (.forward x) := by
  simp only [ofForward, ProbOracleComp.run_simulate, ProbOracleComp.run_query]

/-- `ofForward A` makes as many queries as `A`. -/
theorem StrongAdversary.isQueryBounded_ofForward {A : PRF.Adversary D D} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) : (StrongAdversary.ofForward A).IsQueryBounded Q :=
  hQ.simulate fun x =>
    ProbOracleComp.IsQueryBounded.query (spec := PermOracleSpec D) (PermQuery.forward x)

/-- The real chosen-ciphertext experiment: sample one uniform key and answer `.forward x` with
`E key x` and `.inverse y` with `(E key).symm y`. -/
noncomputable def strongRealExperiment [Fintype Key] [Nonempty Key] (E : Key → Equiv.Perm D)
    (A : StrongAdversary D) : ProbComp Bool := do
  let key ← ProbComp.uniform Key
  A.run fun q => pure (evalPerm (E key) q)

/-- A forward adversary plays the real chosen-ciphertext experiment as the chosen-plaintext one. -/
@[simp] theorem strongRealExperiment_ofForward [Fintype Key] [Nonempty Key]
    (E : Key → Equiv.Perm D) (A : PRF.Adversary D D) :
    strongRealExperiment E (StrongAdversary.ofForward A) = realExperiment E A := by
  simp only [strongRealExperiment, StrongAdversary.run_ofForward, evalPerm_forward]
  rfl

section Ideal

variable [Fintype D] [DecidableEq D]

/-- The ideal chosen-ciphertext experiment: sample one uniform permutation `π` of `D` and answer
`.forward x` with `π x` and `.inverse y` with `π.symm y`. -/
noncomputable def strongIdealExperiment (A : StrongAdversary D) : ProbComp Bool := do
  let π ← ProbComp.uniform (Equiv.Perm D)
  A.run fun q => pure (evalPerm π q)

/-- The strong PRP distinguishing advantage of `A` against `E`. -/
noncomputable abbrev strongAdvantage [Fintype Key] [Nonempty Key] (E : Key → Equiv.Perm D)
    (A : StrongAdversary D) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (strongRealExperiment E A))
    (ProbComp.eval (strongIdealExperiment A))

/-- A forward adversary plays the ideal chosen-ciphertext experiment as the chosen-plaintext one.
-/
@[simp] theorem strongIdealExperiment_ofForward (A : PRF.Adversary D D) :
    strongIdealExperiment (StrongAdversary.ofForward A) = idealExperiment A := by
  simp only [strongIdealExperiment, StrongAdversary.run_ofForward, evalPerm_forward]
  rfl

/-- **Strong PRP security implies PRP security** ([BonehShoup2023], Section 4.1.3): the forward
adversary `ofForward A` has the PRP advantage of `A`. -/
theorem strongAdvantage_ofForward [Fintype Key] [Nonempty Key] (E : Key → Equiv.Perm D)
    (A : PRF.Adversary D D) : strongAdvantage E (StrongAdversary.ofForward A) = advantage E A := by
  simp only [strongAdvantage, strongRealExperiment_ofForward, strongIdealExperiment_ofForward]

end Ideal

end Cslib.Crypto.PRP
