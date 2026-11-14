/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Foundations.Control.Monad.Memoize
import CslibFrontier.Languages.Probabilistic.Memoize
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.Product

/-!
# Several independent keys of a finite pseudorandom function

A multi-key adversary queries `t` channels at once: the query `(i, x)` asks channel `i` at `x`.
In the real experiment `multiKeyRealExperiment` the channels are `F (keys i)` for `t` independent
uniform keys; in the ideal experiment `multiKeyIdealExperiment` they are `t` independent uniform
functions `D → R`. This is the `t`-wise parallel composition of a PRF ([BonehShoup2023],
Exercise 4.26), for finite key, input and output types, and the finite counterpart of the
word-level `Cslib.Crypto.PseudorandomFunction.multiKey`.

The proof is the standard hybrid argument. In the `j`-th hybrid the channels below `j` are random
and the others are keyed. The reduction `multiKeyReduction F j A` is one randomized PRF adversary:
it samples its own keys, forwards channel `j` to its PRF challenger, answers the channels above
`j` with its keys, and lazily samples the random channels below `j` with a list cache
(`multiKeyHandler`). Against the real PRF experiment it plays the `j`-th hybrid and against the
ideal one the `(j + 1)`-st, so the multi-key advantage is at most the sum of the `t` PRF
advantages of the reductions (`multiKeyAdvantage_le_sum`). Each reduction makes at most as many
queries as the adversary (`isQueryBounded_multiKeyReduction`).

This deviates from the exercise, which relates the multi-key advantage to `t` times the
advantage of one reduction that picks the hybrid at random. By the triangle inequality the sum of
the `t` hybrid advantages is at least that quantity, so the bound here follows from the
exercise's form and may be weaker. `Cslib.Crypto.Game.advantage_hybrid_average` provides the
averaging step.

## Main definitions

* `Cslib.Crypto.PRF.MultiKeyAdversary`: an adaptive test with private coins and `t` channels.
* `Cslib.Crypto.PRF.multiKeyRealExperiment`, `Cslib.Crypto.PRF.multiKeyIdealExperiment`,
  `Cslib.Crypto.PRF.multiKeyAdvantage`: the multi-key experiments and their advantage.
* `Cslib.Crypto.PRF.MultiKeyCache`, `Cslib.Crypto.PRF.multiKeyHandler`,
  `Cslib.Crypto.PRF.multiKeyReduction`: the hybrid reductions and their lazily sampled channels.

## Main results

* `Cslib.Crypto.PRF.isQueryBounded_multiKeyReduction`: a reduction makes at most as many queries
  as the multi-key adversary.
* `Cslib.Crypto.PRF.multiKeyAdvantage_le_sum`: the multi-key advantage is at most the sum of the
  PRF advantages of the `t` hybrid reductions.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Exercise 4.26 (Parallel composition of PRFs).
-/

public section

namespace Cslib.Crypto.PRF

open Probability
open scoped NNReal

variable {Key D R : Type} {t : ℕ}

/-- An adaptive test with private coins and `t` oracle channels, each a function `D → R`: the query
`(i, x)` asks channel `i` at `x`. -/
abbrev MultiKeyAdversary (t : ℕ) (D R : Type) := ProbOracleComp (fun _ : Fin t × D => R) Bool

/-- The real multi-key experiment: sample `t` independent uniform keys and answer each query
`(i, x)` with `F (keys i) x`. -/
@[expose] noncomputable def multiKeyRealExperiment [Fintype Key] [Nonempty Key] (F : Key → D → R)
    (A : MultiKeyAdversary t D R) : ProbComp Bool := do
  let keys ← ProbComp.uniform (Fin t → Key)
  A.run fun (i, x) => pure (F (keys i) x)

/-- The ideal multi-key experiment: sample `t` independent uniform functions `D → R` and answer each
query `(i, x)` with `tables i x`. -/
@[expose] noncomputable def multiKeyIdealExperiment [Fintype D] [DecidableEq D] [Fintype R]
    [Nonempty R] (A : MultiKeyAdversary t D R) : ProbComp Bool := do
  let tables ← ProbComp.uniform (Fin t → D → R)
  A.run fun (i, x) => pure (tables i x)

/-- The multi-key distinguishing advantage of `A` against `F`. -/
noncomputable abbrev multiKeyAdvantage [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D]
    [Fintype R] [Nonempty R] (F : Key → D → R) (A : MultiKeyAdversary t D R) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (multiKeyRealExperiment F A))
    (ProbComp.eval (multiKeyIdealExperiment A))

/-- The cache of a hybrid reduction: the replies of its lazily sampled channels so far. -/
abbrev MultiKeyCache (t : ℕ) (D R : Type) := List ((Fin t × D) × R)

/-- One call of the `j`-th hybrid reduction with its own `keys`. Channels below `j` are lazily
sampled uniform random functions: a cached request returns its cached reply, and a new one
samples a uniform reply and caches it. Channel `j` is forwarded to the external PRF oracle.
Channels above `j` are evaluated with their keys. -/
noncomputable def multiKeyHandler [DecidableEq D] [Fintype R] [Nonempty R] (F : Key → D → R)
    (j : ℕ) (keys : Fin t → Key) :
    Fin t × D → StateT (MultiKeyCache t D R) (ProbOracleComp (fun _ : D => R)) R
  | (i, x), cache =>
    if i.val < j then ProbOracleComp.sample (memoize (fun _ => ProbComp.uniform R) (i, x) cache)
    else if i.val = j then (fun reply => (reply, cache)) <$> ProbOracleComp.query x
    else pure (F (keys i) x, cache)

/-- The `j`-th hybrid reduction: sample `t` uniform keys, then run the multi-key adversary with
`multiKeyHandler` from the empty cache. It is a PRF adversary for a single channel. -/
noncomputable def multiKeyReduction [Fintype Key] [Nonempty Key] [DecidableEq D] [Fintype R]
    [Nonempty R] (F : Key → D → R) (j : ℕ) (A : MultiKeyAdversary t D R) :
    ProbOracleComp (fun _ : D => R) Bool := do
  let keys ← ProbOracleComp.sample (ProbComp.uniform (Fin t → Key))
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (multiKeyHandler F j keys)) A).run []

/-- A hybrid reduction makes at most as many queries as the multi-key adversary: each request
makes at most one query, and private samples make none. -/
theorem isQueryBounded_multiKeyReduction [Fintype Key] [Nonempty Key] [DecidableEq D] [Fintype R]
    [Nonempty R] (F : Key → D → R) (j : ℕ) {A : MultiKeyAdversary t D R} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) : (multiKeyReduction F j A).IsQueryBounded Q := by
  have hbody (keys : Fin t → Key) :
      (Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (multiKeyHandler F j keys)) A).run []).IsQueryBounded Q := by
    rw [ProbOracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff]
    refine OracleComp.IsCostBounded.run_interpret (fun q cache => ?_) hQ []
    rcases q with k | ⟨i, x⟩
    · simpa [OracleComp.sumHandler, StateT.run, StateT.lift] using
        (ProbOracleComp.IsQueryBounded.sample (spec := fun _ : D => R) (ProbComp.unifFin k)).bind
          fun a => OracleComp.IsCostBounded.pure (a, cache) 0
    · simp only [OracleComp.sumHandler, Sum.elim_inr, StateT.run, multiKeyHandler]
      split_ifs
      · exact (ProbOracleComp.IsQueryBounded.sample _).mono (Nat.zero_le 1)
      · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
          (ProbOracleComp.IsQueryBounded.query (spec := fun _ : D => R) x)
      · exact OracleComp.IsCostBounded.pure _ 1
  simpa [multiKeyReduction] using
    (ProbOracleComp.IsQueryBounded.sample (spec := fun _ : D => R)
      (ProbComp.uniform (Fin t → Key))).bind hbody

/-! ### Correctness of the hybrid reductions -/

section Correctness

variable [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]

/-- The answers of the `j`-th hybrid: random tables below `j`, keys from `j` on. -/
private def hybridOracle (F : Key → D → R) (j : ℕ) (keys : Fin t → Key)
    (tables : Fin t → D → R) : Fin t × D → R
  | (i, x) => if i.val < j then tables i x else F (keys i) x

/-- The `j`-th hybrid experiment, at the `PMF` level. -/
private noncomputable def hybrid (F : Key → D → R) (j : ℕ) (A : MultiKeyAdversary t D R) :
    PMF Bool :=
  (PMF.uniformOfFintype (Fin t → Key)).bind fun keys =>
    (PMF.uniformOfFintype (Fin t → D → R)).bind fun tables =>
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun request => PMF.pure (hybridOracle F j keys tables request))) A

private theorem eval_multiKeyRealExperiment (F : Key → D → R) (A : MultiKeyAdversary t D R) :
    ProbComp.eval (multiKeyRealExperiment F A) = hybrid F 0 A := by
  simp only [multiKeyRealExperiment, hybrid, hybridOracle, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbOracleComp.eval_run, ProbComp.eval_pure, Nat.not_lt_zero,
    ↓reduceIte, PMF.bind_const]

private theorem eval_multiKeyIdealExperiment (F : Key → D → R) (A : MultiKeyAdversary t D R) :
    ProbComp.eval (multiKeyIdealExperiment A) = hybrid F t A := by
  simp only [multiKeyIdealExperiment, hybrid, hybridOracle, ProbComp.eval_bind,
    ProbComp.eval_uniform, ProbOracleComp.eval_run, ProbComp.eval_pure, Fin.is_lt, ↓reduceIte,
    PMF.bind_const]

/-- The reduction's handler after evaluating its private samples, against a deterministic external
oracle `ext`. -/
private noncomputable def semanticHandler (F : Key → D → R) (j : ℕ) (keys : Fin t → Key)
    (ext : D → R) : Fin t × D → StateT (MultiKeyCache t D R) PMF R
  | (i, x), cache =>
    if i.val < j then memoize (fun _ => PMF.uniformOfFintype R) (i, x) cache
    else if i.val = j then PMF.pure (ext x, cache)
    else PMF.pure (F (keys i) x, cache)

omit [Fintype D] in
/-- Against a deterministic external oracle, the reduction samples its keys and runs the adversary
against `semanticHandler`. -/
private theorem interpret_multiKeyReduction (F : Key → D → R) (j : ℕ)
    (A : MultiKeyAdversary t D R) (ext : D → R) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (fun x => PMF.pure (ext x)))
        (multiKeyReduction F j A) =
      (PMF.uniformOfFintype (Fin t → Key)).bind fun keys =>
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
            (semanticHandler F j keys ext)) A).run []).map Prod.fst := by
  simp only [multiKeyReduction, OracleComp.interpret_bind, ProbOracleComp.interpret_sample,
    OracleComp.interpret_map]
  rw [show OracleComp.interpret ProbComp.unifOracle (ProbComp.uniform (Fin t → Key)) =
    ProbComp.eval (ProbComp.uniform (Fin t → Key)) from rfl, ProbComp.eval_uniform,
    Probability.PMF.monad_bind_eq_bind]
  congr 1 with keys : 1
  have hhom : IsMonadHom (ProbOracleComp (fun _ : D => R)) PMF
      (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
        (fun x : D => PMF.pure (ext x)))) :=
    OracleComp.isMonadHom_evalWith _
  rw [OracleComp.map_run_interpret hhom, PMF.monad_map_eq_map]
  congr 3 with q cache : 2
  rcases q with k | ⟨i, x⟩
  · simp [StateT.lift, ProbOracleComp.interpret_sample, ProbComp.unifFin, PMF.map,
      Function.comp_def]
  · simp only [OracleComp.sumHandler, multiKeyHandler, semanticHandler]
    split_ifs
    · rw [ProbOracleComp.interpret_sample]
      exact (ProbComp.eval_memoize _ _ _).trans (by simp only [ProbComp.eval_uniform])
    · simp [PMF.monad_map_eq_map]
    · simp

/-- The deterministic answers of the reduction when its random channels read eager tables. -/
private def eagerOracle (F : Key → D → R) (j : ℕ) (keys : Fin t → Key) (ext : D → R)
    (tables : Fin t → D → R) : Fin t × D → R
  | (i, x) => if i.val < j then tables i x else if i.val = j then ext x else F (keys i) x

omit [Fintype Key] [Nonempty Key] in
/-- The lazy cache of `semanticHandler` is equivalent to eager uniform tables for the channels
below `j`. -/
private theorem run_semanticHandler (F : Key → D → R) (j : ℕ) (keys : Fin t → Key)
    (ext : D → R) (A : MultiKeyAdversary t D R) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (semanticHandler F j keys ext)) A).run []).map Prod.fst =
      (PMF.uniformOfFintype (Fin t → D → R)).bind fun tables =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun request => PMF.pure (eagerOracle F j keys ext tables request))) A := by
  let adapter : Fin t × D → ProbOracleComp (fun _ : Fin t × D => R) R
    | (i, x) => if i.val < j then ProbOracleComp.query (i, x)
      else pure (if i.val = j then ext x else F (keys i) x)
  have h := RandomOracle.interpret_prob_eq_memoize (fun _ : Fin t × D => PMF.uniformOfFintype R)
    (ProbOracleComp.simulate adapter A)
  rw [ProbOracleComp.runWith_simulate] at h
  have hlazy : (fun q => ProbOracleComp.runWith
      (memoize fun _ : Fin t × D => PMF.uniformOfFintype R) (adapter q)) =
      semanticHandler F j keys ext := by
    funext ⟨i, x⟩ cache
    simp only [adapter, semanticHandler]
    split_ifs
    · simp only [ProbOracleComp.runWith, OracleComp.runWith, ProbOracleComp.interpret_query]
      rfl
    all_goals simp [ProbOracleComp.runWith, OracleComp.runWith]
  have heager (table : Fin t × D → R) :
      (fun q => OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (fun q' => PMF.pure (table q'))) (adapter q)) =
        fun request => PMF.pure (eagerOracle F j keys ext (Function.curry table) request) := by
    funext ⟨i, x⟩
    simp only [adapter, eagerOracle]
    split_ifs <;> simp [Function.curry]
  simp only [ProbOracleComp.interpret_simulate, hlazy, heager, PMF.pi_uniformOfFintype,
    Probability.PMF.monad_bind_eq_bind] at h
  rw [ProbOracleComp.runWith, OracleComp.runWith] at h
  rw [← h, ← PMF.uniformOfFintype_map_equiv (Equiv.curry (Fin t) D R), PMF.bind_map]
  rfl

/-- Against the real PRF experiment, the `j`-th reduction is the `j`-th hybrid. -/
private theorem eval_realExperiment_multiKeyReduction (F : Key → D → R) {j : ℕ} (hj : j < t)
    (A : MultiKeyAdversary t D R) :
    ProbComp.eval (realExperiment F (multiKeyReduction F j A)) = hybrid F j A := by
  rw [eval_realExperiment]
  simp only [interpret_multiKeyReduction, run_semanticHandler, hybrid]
  rw [PMF.bind_uniformOfFintype_update ⟨j, hj⟩]
  congr 1 with value : 1; congr 1 with keys : 1; congr 1 with tables : 1
  congr 2 with request : 1
  obtain ⟨i, x⟩ := request
  simp only [eagerOracle, hybridOracle]
  split_ifs with hlt heq
  · rfl
  · have hi : i = ⟨j, hj⟩ := Fin.ext heq
    subst hi
    rw [Function.update_self]
  · have hi : i ≠ ⟨j, hj⟩ := fun h => heq (congrArg Fin.val h)
    rw [Function.update_of_ne hi]

/-- Against the ideal PRF experiment, the `j`-th reduction is the `(j + 1)`-st hybrid. -/
private theorem eval_idealExperiment_multiKeyReduction (F : Key → D → R) {j : ℕ} (hj : j < t)
    (A : MultiKeyAdversary t D R) :
    ProbComp.eval (idealExperiment (multiKeyReduction F j A)) = hybrid F (j + 1) A := by
  rw [eval_idealExperiment]
  simp only [interpret_multiKeyReduction, run_semanticHandler, hybrid]
  conv_rhs =>
    arg 2
    ext keys
    rw [PMF.bind_uniformOfFintype_update ⟨j, hj⟩]
  conv_rhs => rw [PMF.bind_comm]
  congr 1 with table : 1; congr 1 with keys : 1; congr 1 with tables : 1
  congr 2 with request : 1
  obtain ⟨i, x⟩ := request
  simp only [eagerOracle, hybridOracle]
  by_cases hlt : i.val < j
  · have hi : i ≠ ⟨j, hj⟩ := fun h => by
      subst h
      exact Nat.lt_irrefl j hlt
    have hlt' : i.val < j + 1 := by omega
    simp only [hlt, hlt', ↓reduceIte, Function.update_of_ne hi]
  · by_cases heq : i.val = j
    · have hi : i = ⟨j, hj⟩ := Fin.ext heq
      subst hi
      simp only [lt_irrefl, lt_add_one, ↓reduceIte, Function.update_self]
    · have hlt' : ¬i.val < j + 1 := by omega
      simp only [hlt, heq, hlt', ↓reduceIte]

/-- **Multi-key PRF hybrid** ([BonehShoup2023], Exercise 4.26): the multi-key advantage of `A` is at
most the sum of the PRF advantages of the `t` hybrid reductions `multiKeyReduction F j A`. This is
a concrete bound for one finite instance; running time is not modeled. The asymptotic word-level
statement is `Cslib.Crypto.PseudorandomFunction.multiKey`. -/
theorem multiKeyAdvantage_le_sum (F : Key → D → R) (A : MultiKeyAdversary t D R) :
    multiKeyAdvantage F A ≤ ∑ j ∈ Finset.range t, advantage F (multiKeyReduction F j A) := by
  rw [multiKeyAdvantage, eval_multiKeyRealExperiment F A, eval_multiKeyIdealExperiment F A]
  refine (Game.advantage_hybrid_le_sum (fun j => hybrid F j A) t).trans
    (Finset.sum_le_sum fun j hj => le_of_eq ?_)
  have hj : j < t := Finset.mem_range.mp hj
  rw [advantage, eval_realExperiment_multiKeyReduction F hj,
    eval_idealExperiment_multiKeyReduction F hj]

end Correctness

end Cslib.Crypto.PRF
