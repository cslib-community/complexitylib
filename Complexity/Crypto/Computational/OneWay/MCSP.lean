/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.MCSP.NP
public import Complexity.Crypto.Computational.OneWay
public import Complexity.Crypto.Computational.PseudorandomFunction.TruthTable
import Complexity.Computability.Complexity.Classes.Inclusions
import Complexity.Computability.MCSP.Shannon
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Crypto.Computational.OneWayToPRF
import Complexity.Crypto.Negligible.Basic
import Complexity.Foundations.Data.Nat.Log
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
import Complexity.Probability.Uniform
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# MCSP in BPP rules out one-way functions

If the Minimum Circuit Size Problem is decidable in probabilistic polynomial time, then one-way
functions do not exist [Kabanets and Cai][KabanetsCai2000]. One-way functions give pseudorandom
functions (`Cslib.Crypto.OneWay.exists_pseudorandomFunction`), and an MCSP decider distinguishes a
pseudorandom function from a random one:

* The *restriction* of a keyed family computable in polynomial time to the `2 ^ m` inputs of
  length `n` whose first `n - m` bits are `false`, read through the first output bit
  (`Cslib.Crypto.KabanetsCai.restriction`), has a circuit with at most `c (3 n + 2) ^ c + 2`
  gates for a constant `c` (`Cslib.Crypto.KabanetsCai.exists_complexity_restriction_le`).
* A random function restricts to a uniformly random truth table
  (`Cslib.Crypto.KabanetsCai.uniformOfFintype_map_restrictTable`), and at most
  `2 ^ (2 ^ m / 4)` of the `2 ^ (2 ^ m)` truth tables have circuits with at most
  `⌊2 ^ m / (5 m)⌋` gates (`Cslib.MCSP.ncard_setOf_mem_le`,
  `Cslib.Crypto.KabanetsCai.toReal_map_restrictTable_mem_le`).

The distinguisher (`Cslib.Crypto.KabanetsCai.mcspDistinguisher`) takes `m = d ⌈log₂ n⌉` for
`d = c + 2`, queries the oracle on the `2 ^ m ≤ (2 n) ^ d` words above, assembles the first bits
of the replies into a truth table, and runs the bounded-error MCSP decider at threshold
`⌊2 ^ m / (5 m)⌋`. For large `n` this threshold is at least the circuit size of every restriction
of the family, so the decider accepts the pseudorandom table with probability at least `2 / 3`,
and a random table with probability at most `1 / 3 + 2 ^ (2 ^ m / 4) / 2 ^ (2 ^ m)`. The
distinguisher is a uniform strict oracle PPT adversary in the model of
`Cslib.Crypto.PseudorandomFunction` (`Cslib.Crypto.KabanetsCai.isOraclePPT_mcspDistinguisher`),
and its advantage is at least `1 / 4` for all large `n`, which is not negligible.

MCSP is the language `Cslib.MCSP` of instances `(T, s)` whose truth table `T` of `2 ^ m` bits has
a De Morgan circuit with at most `s` gates (all gates counted), encoded by the table followed by
`s` in binary (`Cslib.MCSP.encInstance`); `BPP` is `Cslib.Complexity.BPP` for this encoding. The
hypothesis is that MCSP is in `BPP` at all thresholds; the distinguisher only runs the decider at
thresholds `⌊2 ^ m / (5 m)⌋`. The parts of the distinguisher live in the namespace
`Cslib.Crypto.KabanetsCai`.

## Main definitions

* `Cslib.Crypto.KabanetsCai.mcspRun`: run a bounded-error decider for MCSP on fresh coins.
* `Cslib.Crypto.KabanetsCai.mcspDistinguisher`: the oracle adversary built from an MCSP decider.

## Main results

* `Cslib.Crypto.KabanetsCai.toReal_map_restrictTable_mem_le`: few restrictions of a random
  function have small circuits.
* `Cslib.Crypto.KabanetsCai.isOraclePPT_mcspDistinguisher`: the distinguisher is uniform strict
  oracle PPT.
* `Cslib.Crypto.KabanetsCai.eval_prfRealGame_mcspDistinguisher`,
  `Cslib.Crypto.KabanetsCai.eval_prfIdealGame_mcspDistinguisher`: in both games the decider runs
  on the truth table of a restriction.
* `Cslib.Crypto.not_pseudorandomFunction_of_MCSP_mem_BPP`: if MCSP is in `BPP`, there are no
  pseudorandom functions.
* `Cslib.Crypto.not_oneWay_of_MCSP_mem_BPP`, `Cslib.Crypto.not_oneWay_of_MCSP_mem_P`:
  **Kabanets–Cai**: if MCSP is in `BPP`, or in `P`, there are no one-way functions.

## References

* [V. Kabanets, J.-Y. Cai, *Circuit minimization problem*][KabanetsCai2000]
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM ComputableTidilyInPolyTime Complexity Circuits
  Circuits.Boolean
open scoped BigOperators

namespace KabanetsCai

/-! ### Few random restrictions have small circuits -/

open scoped Classical in
/-- **Few restrictions of a random function have small circuits.** For `16 ≤ m ≤ n`, the
restriction of a uniformly random function from `n` bits to `n` bits to `m` inputs has a circuit
with at most `⌊2 ^ m / (5 m)⌋` gates with probability at most `2 ^ (2 ^ m / 4) / 2 ^ (2 ^ m)`. -/
theorem toReal_map_restrictTable_mem_le {n m : ℕ} (hn : 0 < n) (hm : m ≤ n) (hm16 : 16 ≤ m) :
    ((PMF.uniformOfFintype (BitString n → BitString n)).map (fun table =>
      decide ((⟨m, MCSP.truthTable m (restrictTable n m hn table), 2 ^ m / (5 * m)⟩ :
        MCSP.Instance) ∈ MCSP)) true).toReal ≤ 2 ^ (2 ^ m / 4) / 2 ^ 2 ^ m := by
  have hcomp : (fun table : BitString n → BitString n =>
      decide ((⟨m, MCSP.truthTable m (restrictTable n m hn table), 2 ^ m / (5 * m)⟩ :
        MCSP.Instance) ∈ MCSP)) =
      (fun T : BitString (2 ^ m) => decide ((⟨m, T, 2 ^ m / (5 * m)⟩ : MCSP.Instance) ∈ MCSP)) ∘
        MCSP.truthTable m ∘ restrictTable n m hn := rfl
  rw [hcomp, ← PMF.map_comp, ← PMF.map_comp, uniformOfFintype_map_restrictTable hn hm,
    PMF.uniformOfFintype_map_equiv, PMF.uniformOfFintype_map_apply, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hcard : Nat.card {T : BitString (2 ^ m) //
      decide ((⟨m, T, 2 ^ m / (5 * m)⟩ : MCSP.Instance) ∈ MCSP) = true} =
      {T : BitString (2 ^ m) | (⟨m, T, 2 ^ m / (5 * m)⟩ : MCSP.Instance) ∈ MCSP}.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun T => by simp)
  rw [hcard, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have := MCSP.ncard_setOf_mem_le hm16
  push_cast
  exact div_le_div_of_nonneg_right (by exact_mod_cast this) (by positivity)

/-! ### Running a bounded-error decider for MCSP -/

/-- Run a decider with random coins for MCSP on one instance, with fresh uniform coins of the
length the bounded-error condition prescribes. -/
noncomputable def mcspRun (p : Polynomial ℕ) (V : MCSP.Instance × List Bool → Bool)
    (x : MCSP.Instance) : ProbComp Bool :=
  (fun coins => V (x, coins)) <$> BitString.sampleList (p.eval (MCSP.encInstance x).length)

variable {p : Polynomial ℕ} {V : MCSP.Instance × List Bool → Bool}

theorem isPPTOn_mcspRun
    (hV : ComputableInPolyTime V (encPair MCSP.encInstance encBits) encBool) :
    IsPPTOn MCSP.encInstance encBool (mcspRun p V) :=
  IsPPTOn.map_with (ComputableInPolyTime.sampleList
    (.of_tidy ((unary_eval p).comp (encoding_length MCSP.encInstance)))) hV

/-- The acceptance probability of `mcspRun` is the fraction of accepting coin strings. -/
theorem toReal_eval_mcspRun (p : Polynomial ℕ) (V : MCSP.Instance × List Bool → Bool)
    (x : MCSP.Instance) :
    (ProbComp.eval (mcspRun p V x) true).toReal =
      ((Finset.univ.filter fun r : Fin (p.eval (MCSP.encInstance x).length) → Bool =>
        V (x, List.ofFn r) = true).card : ℝ) / 2 ^ p.eval (MCSP.encInstance x).length := by
  rw [mcspRun, ProbComp.eval_map, BitString.eval_sampleList, BitString.uniformList, PMF.map_comp,
    PMF.uniformOfFintype_map_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

/-- A bounded-error decider accepts a member of MCSP with probability at least `2 / 3`. -/
theorem two_thirds_le_toReal_eval_mcspRun
    (hV : DecidesWithBoundedError MCSP.encInstance p V MCSP) {x : MCSP.Instance} (hx : x ∈ MCSP) :
    2 / 3 ≤ (ProbComp.eval (mcspRun p V x) true).toReal := by
  rw [toReal_eval_mcspRun, le_div_iff₀ (by positivity)]
  have h := (hV x).1 hx
  have h' : ((2 * 2 ^ p.eval (MCSP.encInstance x).length : ℕ) : ℝ) ≤
      ((3 * (Finset.univ.filter fun r : Fin (p.eval (MCSP.encInstance x).length) → Bool =>
        V (x, List.ofFn r) = true).card : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- A bounded-error decider accepts a non-member of MCSP with probability at most `1 / 3`. -/
theorem toReal_eval_mcspRun_le_one_third
    (hV : DecidesWithBoundedError MCSP.encInstance p V MCSP) {x : MCSP.Instance} (hx : x ∉ MCSP) :
    (ProbComp.eval (mcspRun p V x) true).toReal ≤ 1 / 3 := by
  rw [toReal_eval_mcspRun, div_le_iff₀ (by positivity)]
  set k := p.eval (MCSP.encInstance x).length
  have h := (hV x).2 hx
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k → Bool))) (fun r => V (x, List.ofFn r) = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at hsum
  have h' : ((2 * 2 ^ k : ℕ) : ℝ) ≤ ((3 * (Finset.univ.filter fun r : Fin k → Bool =>
      V (x, List.ofFn r) = false).card : ℕ) : ℝ) := by exact_mod_cast h
  have hsum' : (((Finset.univ.filter fun r : Fin k → Bool => V (x, List.ofFn r) = true).card +
      (Finset.univ.filter fun r : Fin k → Bool => V (x, List.ofFn r) = false).card : ℕ) : ℝ) =
      ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast hsum
  push_cast at h' hsum'
  linarith

/-! ### The distinguisher -/

/-- The number of inputs of the truth tables read at parameter `n`: `d ⌈log₂ n⌉`. -/
def tableArity (d n : ℕ) : ℕ := d * Nat.clog 2 n

/-- The MCSP instance read from a list of answers at arity `m`, with threshold `2 ^ m / (5 m)`. -/
def tableInstance (m : ℕ) (answers : List Bool) : MCSP.Instance :=
  ⟨m, BitString.ofList (2 ^ m) answers, 2 ^ m / (5 * m)⟩

/-- **The Kabanets–Cai distinguisher.** At parameter `n`, ask the oracle for the truth table of
its restriction to `m = d ⌈log₂ n⌉` inputs and run the bounded-error decider `V` for MCSP at
threshold `2 ^ m / (5 m)`. -/
noncomputable def mcspDistinguisher (p : Polynomial ℕ) (V : MCSP.Instance × List Bool → Bool)
    (d : ℕ) : OracleDistinguisher := fun n _ => do
  let answers ← queryTable (tableQueries n (tableArity d n))
  ProbOracleComp.sample (mcspRun p V (tableInstance (tableArity d n) answers))

/-- The answers of a deterministic oracle to the queries form the truth table of its
restriction. -/
theorem tableInstance_map_tableQueries (oracle : List Bool → List Bool) (n m : ℕ) :
    tableInstance m ((tableQueries n m).map fun word => (oracle word).headD false) =
      ⟨m, MCSP.truthTable m (restriction oracle n m), 2 ^ m / (5 * m)⟩ := by
  rw [tableInstance, map_tableQueries, BitString.ofList_ofFn]

/-- Against a deterministic oracle, the distinguisher runs the decider on the truth table of the
oracle's restriction. -/
theorem interpret_mcspDistinguisher (d : ℕ) (oracle : List Bool → List Bool) (n : ℕ) :
    OracleComp.interpret (ProbOracleComp.handler ProbComp.unifFin
      fun request => pure (oracle request.2)) (mcspDistinguisher p V d n []) =
      mcspRun p V ⟨tableArity d n, MCSP.truthTable (tableArity d n)
        (restriction oracle n (tableArity d n)), 2 ^ tableArity d n / (5 * tableArity d n)⟩ := by
  rw [mcspDistinguisher, OracleComp.interpret_bind, interpret_queryTable, pure_bind,
    ProbOracleComp.interpret_sample, tableInstance_map_tableQueries]
  exact OracleComp.interpret_query_eq_self _

/-! ### The distinguisher is uniform strict oracle PPT -/

/-- The arity is computed in unary from the unary parameter. -/
@[fun_prop]
theorem computableInPolyTime_tableArity (d : ℕ) :
    ComputableInPolyTime (tableArity d) encUnary encUnary := by
  unfold tableArity
  have := ComputableInPolyTime.unary_clog_const 2
  fun_prop

/-- The table size `2 ^ m` is computed in unary from the unary parameter. -/
theorem computableInPolyTime_two_pow_tableArity (d : ℕ) :
    ComputableInPolyTime (fun n => 2 ^ tableArity d n) encUnary encUnary := by
  simpa only [tableArity, ← pow_mul] using
    ComputableInPolyTime.unary_pow_clog_const ComputableInPolyTime.id' (2 ^ d) 2

/-- The queries are computed in polynomial time from the unary parameter. -/
theorem computableInPolyTime_tableQueries (d : ℕ) :
    ComputableInPolyTime (fun input : ℕ × List Bool =>
      tableQueries input.1 (tableArity d input.1)) (encPair encUnary encBits)
      (encList encBits) := by
  refine .of_tidy ?_
  unfold tableQueries
  have harity : ComputableTidilyInPolyTime (fun input : ℕ × List Bool => tableArity d input.1)
      (encPair encUnary encBits) encUnary :=
    (computableInPolyTime_tableArity d).tidy.comp (fst _ _)
  refine mapWithInput (bitsEnumList harity
    (size := fun L => (2 * (L + 1)) ^ d * (2 * (d * (2 * (L + 1))) + 1)) (by fun_prop)
    fun input => ?_) ?_
  · obtain ⟨n, aux⟩ := input
    dsimp only
    have hn : n ≤ (encPair encUnary encBits (n, aux)).length := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
      omega
    set L := (encPair encUnary encBits (n, aux)).length
    have hpow : 2 ^ Nat.clog 2 n ≤ 2 * (L + 1) := (Nat.two_pow_clog_two_le n).trans (by omega)
    have hclog : Nat.clog 2 n ≤ 2 * (L + 1) := Nat.lt_two_pow_self.le.trans hpow
    refine Nat.mul_le_mul ?_ ?_
    · rw [tableArity, mul_comm, pow_mul]
      exact Nat.pow_le_pow_left hpow d
    · have := Nat.mul_le_mul_left d hclog
      rw [tableArity]
      omega
  · have hsub : ComputableTidilyInPolyTime (fun p : (ℕ × List Bool) × List Bool =>
        p.1.1 - tableArity d p.1.1) (encPair (encPair encUnary encBits) encBits) encUnary :=
      unary_sub.comp ((fst _ _).fst'.prod (harity.comp (fst _ _)))
    exact bitsAppend ((bitsReplicate false).comp hsub) (snd _ _)

/-- The instance read from the answers is computed in polynomial time. -/
theorem computableInPolyTime_tableInstance (d : ℕ) :
    ComputableInPolyTime (fun pair : (ℕ × List Bool) × List Bool =>
      tableInstance (tableArity d pair.1.1) pair.2) (encPair (encPair encUnary encBits) encBits)
      MCSP.encInstance := by
  refine .of_tidy ?_
  have harity : ComputableTidilyInPolyTime (fun pair : (ℕ × List Bool) × List Bool =>
      tableArity d pair.1.1) (encPair (encPair encUnary encBits) encBits) encUnary :=
    (computableInPolyTime_tableArity d).tidy.comp (fst _ _).fst'
  have hsize : ComputableTidilyInPolyTime (fun pair : (ℕ × List Bool) × List Bool =>
      2 ^ tableArity d pair.1.1) (encPair (encPair encUnary encBits) encBits) encUnary :=
    (computableInPolyTime_two_pow_tableArity d).tidy.comp (fst _ _).fst'
  have hraw : ComputableTidilyInPolyTime (fun pair : (ℕ × List Bool) × List Bool =>
      ((pair.2 ++ List.replicate (2 ^ tableArity d pair.1.1) false).take
        (2 ^ tableArity d pair.1.1), 2 ^ tableArity d pair.1.1 / (5 * tableArity d pair.1.1)))
      (encPair (encPair encUnary encBits) encBits) (encPair encBits encNat) :=
    (bitsTakeWithInput (bitsAppend (snd _ _) ((bitsReplicate false).comp hsize)) hsize).prod
      (unary_to_binary.comp (unary_div.comp (hsize.prod (unary_mul.comp
        ((const 5).prod harity)))))
  refine hraw.of_enc_eq fun pair => ?_
  rw [MCSP.encInstance_apply]
  simp only [tableInstance, BitString.ofFn_ofList_eq_take]

/-- **The Kabanets–Cai distinguisher is uniform strict oracle PPT**, for a polynomial-time
decider `V`: it makes `2 ^ m ≤ (2 (n + 1)) ^ d` queries of length `n` and runs `V` on a truth table
of `2 ^ m` bits. -/
theorem isOraclePPT_mcspDistinguisher (d : ℕ)
    (hV : ComputableInPolyTime V (encPair MCSP.encInstance encBits) encBool) :
    IsOraclePPT encBool (mcspDistinguisher p V d) := by
  have hV := hV.tidy
  apply IsOraclePPTOn.isOraclePPT
  exact IsOraclePPTOn.bind_with
    (isOraclePPTOn_queryTable.preprocess (computableInPolyTime_tableQueries d).tidy)
    ((isPPTOn_mcspRun (.of_tidy hV)).preprocess
      (computableInPolyTime_tableInstance d)).isOraclePPTOn

/-! ### The advantage of the distinguisher -/

/-- In the real game, the decider runs on the truth table of the restriction of the family with a
uniform key. -/
theorem eval_prfRealGame_mcspDistinguisher (family : List Bool → List Bool → List Bool)
    {d n : ℕ} (hm : tableArity d n ≤ n) :
    ProbComp.eval (prfRealGame family (mcspDistinguisher p V d) n) =
      (BitString.uniformList n).bind fun key => ProbComp.eval (mcspRun p V
        ⟨tableArity d n, MCSP.truthTable (tableArity d n)
          (restriction (family key) n (tableArity d n)),
          2 ^ tableArity d n / (5 * tableArity d n)⟩) := by
  simp only [prfRealGame, ProbComp.eval_bind, BitString.eval_sampleList,
    interpret_mcspDistinguisher, restriction_prfOracle hm]

/-- In the ideal game, the decider runs on the truth table of the restriction of a uniformly
random function. -/
theorem eval_prfIdealGame_mcspDistinguisher {d n : ℕ} (hn : 0 < n) (hm : tableArity d n ≤ n) :
    ProbComp.eval (prfIdealGame (mcspDistinguisher p V d) n) =
      (PMF.uniformOfFintype (BitString n → BitString n)).bind fun table =>
        ProbComp.eval (mcspRun p V ⟨tableArity d n, MCSP.truthTable (tableArity d n)
          (restrictTable n (tableArity d n) hn table),
          2 ^ tableArity d n / (5 * tableArity d n)⟩) := by
  simp only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    interpret_mcspDistinguisher, restriction_randomFunctionOracle hn hm]

/-- For large `n`, the arity `m = d ⌈log₂ n⌉` with `d = c + 2` satisfies `16 ≤ m ≤ n`, and the
threshold `2 ^ m / (5 m)` is at least `c (3 n + 2) ^ c + 2`. -/
theorem eventually_tableArity (c : ℕ) :
    ∀ᶠ n in Filter.atTop, 0 < n ∧ 16 ≤ tableArity (c + 2) n ∧ tableArity (c + 2) n ≤ n ∧
      c * (3 * n + 2) ^ c + 2 ≤ 2 ^ tableArity (c + 2) n / (5 * tableArity (c + 2) n) := by
  have htend : Filter.Tendsto (Nat.clog 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun n hn => by
      simpa only [Nat.clog_pow 2 b one_lt_two] using Nat.clog_mono_right 2 hn⟩
  have hlin : ∀ᶠ t in Filter.atTop, 2 * (c + 2) * t < 2 ^ t :=
    PolynomiallyBounded.eventually_lt_two_pow (by fun_prop)
  filter_upwards [htend.eventually_ge_atTop 16, htend.eventually hlin,
    Filter.eventually_ge_atTop (10 * (c + 2) * (c * 5 ^ c + 2) + 1)] with n h16 hlin hK
  set t := Nat.clog 2 n
  have hn2 : n ≤ 2 ^ t := Nat.le_pow_clog one_lt_two n
  have h2n : 2 ^ t ≤ 2 * n := Nat.pow_clog_le_mul one_lt_two (by omega)
  have ht : t ≤ 2 * n := Nat.lt_two_pow_self.le.trans h2n
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [tableArity]
    nlinarith
  · rw [tableArity]
    nlinarith
  · rw [tableArity]
    have h3 : (3 * n + 2) ^ c ≤ 5 ^ c * n ^ c := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left (by omega) c
    have h1 : 1 ≤ n ^ c := Nat.one_le_pow c n (by omega)
    have hpow : n ^ (c + 2) ≤ 2 ^ ((c + 2) * t) := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left hn2 _
    have hpos : 0 < 5 * ((c + 2) * t) := by
      have : 0 < t := by omega
      positivity
    refine (Nat.le_div_iff_mul_le hpos).2 ?_
    calc (c * (3 * n + 2) ^ c + 2) * (5 * ((c + 2) * t))
        ≤ (c * (5 ^ c * n ^ c) + 2 * n ^ c) * (5 * ((c + 2) * (2 * n))) := by gcongr; omega
      _ = (10 * (c + 2) * (c * 5 ^ c + 2)) * n * n ^ c := by ring
      _ ≤ n * n * n ^ c := by gcongr; omega
      _ = n ^ (c + 2) := by ring
      _ ≤ 2 ^ ((c + 2) * t) := hpow

/-- A probability, as a real number, is at most one. -/
private theorem toReal_apply_le_one {α : Type*} (q : PMF α) (a : α) : (q a).toReal ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using q.coe_le_one a)

end KabanetsCai

open KabanetsCai

/-- **MCSP in `BPP` rules out pseudorandom functions.** If a bounded-error polynomial-time
decider for MCSP exists, then every keyed family computable in polynomial time is distinguished
from a random function by a uniform strict oracle PPT adversary (`mcspDistinguisher`) with
advantage at least `1 / 4` for all large `n`. -/
theorem not_pseudorandomFunction_of_MCSP_mem_BPP (h : MCSP ∈ BPP MCSP.encInstance)
    (family : List Bool → List Bool → List Bool) : ¬ PseudorandomFunction family := by
  classical
  intro hprf
  obtain ⟨p, V, hV, hdec⟩ := h
  obtain ⟨c, hc⟩ := KabanetsCai.exists_complexity_restriction_le hprf.polyTime
  have hnegl := hprf.secure _ (isOraclePPT_mcspDistinguisher (p := p) (c + 2) hV)
  refine not_negligible_const (c := 1 / 4) (by norm_num) (negligible_of_eventually_le hnegl ?_)
  filter_upwards [eventually_tableArity c] with n ⟨hn, hm16, hmn, hsize⟩
  set m := tableArity (c + 2) n
  -- The decider accepts the pseudorandom truth table with probability at least `2 / 3`.
  have hreal : 2 / 3 ≤
      (ProbComp.eval (prfRealGame family (mcspDistinguisher p V (c + 2)) n) true).toReal := by
    rw [eval_prfRealGame_mcspDistinguisher family hmn, BitString.uniformList, PMF.bind_map,
      PMF.toReal_uniformOfFintype_bind_apply]
    refine Finset.le_expect Finset.univ_nonempty fun key _ => ?_
    refine two_thirds_le_toReal_eval_mcspRun hdec (MCSP.mk_truthTable_mem_iff.2 ?_)
    have := hc (List.ofFn key) m (by simpa using hmn)
    rw [List.length_ofFn] at this
    exact this.trans hsize
  -- It accepts a random truth table with probability at most `1 / 3 + 1 / 12`.
  have hideal :
      (ProbComp.eval (prfIdealGame (mcspDistinguisher p V (c + 2)) n) true).toReal ≤
        1 / 3 + 1 / 12 := by
    rw [eval_prfIdealGame_mcspDistinguisher hn hmn, PMF.toReal_uniformOfFintype_bind_apply]
    set g : (BitString n → BitString n) → Bool := fun table =>
      decide ((⟨m, MCSP.truthTable m (KabanetsCai.restrictTable n m hn table),
        2 ^ m / (5 * m)⟩ : MCSP.Instance) ∈ MCSP)
    have hterm (table : BitString n → BitString n) :
        (ProbComp.eval (mcspRun p V ⟨m,
          MCSP.truthTable m (KabanetsCai.restrictTable n m hn table), 2 ^ m / (5 * m)⟩)
            true).toReal ≤ (PMF.pure (g table) true).toReal + 1 / 3 := by
      by_cases hx : (⟨m, MCSP.truthTable m (KabanetsCai.restrictTable n m hn table),
          2 ^ m / (5 * m)⟩ : MCSP.Instance) ∈ MCSP
      · have : g table = true := decide_eq_true hx
        rw [this, PMF.pure_apply_self, ENNReal.toReal_one]
        linarith [toReal_apply_le_one (ProbComp.eval (mcspRun p V ⟨m,
          MCSP.truthTable m (KabanetsCai.restrictTable n m hn table), 2 ^ m / (5 * m)⟩)) true]
      · have : g table = false := decide_eq_false hx
        rw [this, PMF.pure_apply_of_ne _ _ Bool.false_ne_true.symm, ENNReal.toReal_zero,
          zero_add]
        exact toReal_eval_mcspRun_le_one_third hdec hx
    have hsmall : ((PMF.uniformOfFintype (BitString n → BitString n)).map g true).toReal ≤
        1 / 12 := by
      refine (toReal_map_restrictTable_mem_le hn hmn hm16).trans ?_
      have hN : 16 ≤ 2 ^ m := hm16.trans Nat.lt_two_pow_self.le
      have hnat : 12 * 2 ^ (2 ^ m / 4) ≤ 2 ^ 2 ^ m :=
        calc 12 * 2 ^ (2 ^ m / 4) ≤ 2 ^ 4 * 2 ^ (2 ^ m / 4) := by gcongr; norm_num
          _ = 2 ^ (4 + 2 ^ m / 4) := by rw [pow_add]
          _ ≤ 2 ^ 2 ^ m := Nat.pow_le_pow_right two_pos (by omega)
      rw [div_le_iff₀ (by positivity)]
      have : (12 : ℝ) * 2 ^ (2 ^ m / 4) ≤ 2 ^ 2 ^ m := by exact_mod_cast hnat
      linarith
    calc 𝔼 table, (ProbComp.eval (mcspRun p V ⟨m,
          MCSP.truthTable m (KabanetsCai.restrictTable n m hn table), 2 ^ m / (5 * m)⟩)
            true).toReal
        ≤ 𝔼 table, ((PMF.pure (g table) true).toReal + 1 / 3) :=
          Finset.expect_le_expect fun table _ => hterm table
      _ = ((PMF.uniformOfFintype (BitString n → BitString n)).map g true).toReal + 1 / 3 := by
          rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty,
            ← PMF.toReal_uniformOfFintype_bind_apply]
          rfl
      _ ≤ 1 / 3 + 1 / 12 := by linarith
  rw [← NNReal.coe_le_coe, Game.coe_advantage, Game.succProbability, Game.succProbability,
    ENNReal.coe_toNNReal_eq_toReal, ENNReal.coe_toNNReal_eq_toReal]
  push_cast
  rw [le_abs]
  left
  linarith

/-- **Kabanets–Cai** [Kabanets and Cai][KabanetsCai2000]: if MCSP is in `BPP`, with
instances encoded by their truth table and threshold, then no function is one-way. -/
theorem not_oneWay_of_MCSP_mem_BPP (h : MCSP ∈ BPP MCSP.encInstance) (f : List Bool → List Bool) :
    ¬ OneWay f := fun hf =>
  let ⟨family, hfamily⟩ := hf.exists_pseudorandomFunction
  not_pseudorandomFunction_of_MCSP_mem_BPP h family hfamily

/-- **Kabanets–Cai** for deterministic deciders: if MCSP is in `P`, no function is one-way. -/
theorem not_oneWay_of_MCSP_mem_P (h : MCSP ∈ P MCSP.encInstance) (f : List Bool → List Bool) :
    ¬ OneWay f :=
  not_oneWay_of_MCSP_mem_BPP (P_subset_BPP h) f

end Cslib.Crypto
