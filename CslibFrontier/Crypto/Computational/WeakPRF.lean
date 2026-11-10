/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MAC
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Oracle.Tidy
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Weak pseudorandom functions

A weak pseudorandom function is a keyed family that looks random to an adversary who sees only
evaluations at uniformly random points. Each oracle call returns a fresh uniform `n`-bit point
followed by the family's answer at that point; the adversary never chooses the inputs.

## Main definitions

* `Cslib.Crypto.weakSample`: one uniform point together with an oracle's answer on it.
* `Cslib.Crypto.weakPrfRealGame`, `.weakPrfIdealGame`: the keyed and random-function experiments.
* `Cslib.Crypto.WeakPseudorandomFunction`: efficient evaluation, length and weak security.
* `Cslib.Crypto.weakToPrfDistinguisher`: answers weak-PRF calls through an adaptive PRF oracle.
* `Cslib.Crypto.zeroPatch`: replaces every answer on an all-zero query by the query itself.

## Main results

* `Cslib.Crypto.PseudorandomFunction.weakPseudorandomFunction`: every pseudorandom function is a
  weak pseudorandom function ([KatzLindell2020], Exercise 3.28(a)).
* `Cslib.Crypto.not_eufCma_prfMAC_zeroPatch`: the standard fixed-length MAC built from a
  zero-patched family is forgeable with probability one, without any tagging query.
* `Cslib.Crypto.not_pseudorandomFunction_zeroPatch`: hence no zero-patched family is a
  pseudorandom function.
* `Cslib.Crypto.advantage_weakPrfRealGame_zeroPatch_le`: zero patching moves the weak real game by
  at most `Q / 2ⁿ` against an adversary making at most `Q` calls.
* `Cslib.Crypto.WeakPseudorandomFunction.zeroPatch`: zero patching preserves weak security.
* `Cslib.Crypto.PseudorandomFunction.exists_weak_not_pseudorandom`: if pseudorandom functions
  exist, some weak pseudorandom function is not pseudorandom ([KatzLindell2020], Exercise 3.28(b)).
* `Cslib.Crypto.PseudorandomFunction.exists_weak_not_eufCma_prfMAC`: if pseudorandom functions
  exist, some weak pseudorandom function gives a forgeable fixed-length MAC ([KatzLindell2020],
  Exercise 4.9).

## Implementation notes

Both separations use `zeroPatch`, which agrees with the original family except on the all-zero
query. A weak adversary meets that query only when a uniform point is all-zero, so weak security
survives with an extra `Q / 2ⁿ`; an adaptive adversary or a MAC forger asks for it directly.
This is the construction of Exercise 4.9. Another answer to Exercise 3.28(b) evaluates the
function after rounding odd inputs to even ones; the zero patch is a simpler family that
separates the same two notions.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Exercise 3.28
  (printed p. 103) and Exercise 4.9 (printed p. 141).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-! ### The weak experiments -/

/-- One weak-PRF sample: a uniform `n`-bit point followed by the oracle's answer on it. -/
@[expose]
noncomputable def weakSample (n : ℕ) (oracle : List Bool → List Bool) : ProbComp (List Bool) := do
  let point ← BitString.sampleList n
  return point ++ oracle point

/-- Sample one key; every call returns a fresh uniform point and the keyed answer on it. The
adversary's request payload is ignored. -/
@[expose]
noncomputable def weakPrfRealGame (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let key ← BitString.sampleList n
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin (fun _ => weakSample n (prfOracle family n key)))
    (adversary n [])

/-- Sample one whole random function; every call returns a fresh uniform point and the table's
answer on it. -/
@[expose]
noncomputable def weakPrfIdealGame (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString n → BitString n)
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin
      (fun _ => weakSample n (randomFunctionOracle n table)))
    (adversary n [])

/-- A keyed family evaluated in plain polynomial time whose answers at uniformly random points are
indistinguishable from those of a random function ([KatzLindell2020], Exercise 3.28). -/
structure WeakPseudorandomFunction (family : List Bool → List Bool → List Bool) : Prop where
  /-- One deterministic machine evaluates the family from the encoded key and query. -/
  polyTime : ComputableInPolyTime (fun pair => family pair.1 pair.2)
    (encPair encBits encBits) encBits
  /-- Valid queries receive answers of the declared width. -/
  length_eq : ∀ key query, query.length = key.length → (family key query).length = key.length
  /-- The real and ideal weak experiments use the common game-security calculus. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (weakPrfRealGame family adversary n))
    (fun adversary n => ProbComp.eval (weakPrfIdealGame adversary n)) (IsOraclePPT encBool)

/-! ### Every pseudorandom function is weak -/

/-- Answer one weak call through an adaptive oracle: sample a point, query it, and keep at most
`n` bits of the reply. -/
private noncomputable def weakSampleQuery (n : ℕ) : WordOracleComp Unit (List Bool) := do
  let point ← ProbOracleComp.sample (BitString.sampleList n)
  let answer ← List.take n <$> ProbOracleComp.query ((), point)
  return point ++ answer

/-- Run a weak-PRF adversary against an adaptive PRF oracle, answering each of its calls with
`weakSampleQuery`. -/
noncomputable def weakToPrfDistinguisher (adversary : OracleDistinguisher) :
    OracleDistinguisher :=
  fun n _ => OracleComp.interpret
    (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m))
      (fun _ : Unit × List Bool => weakSampleQuery n)) (adversary n [])

private theorem isOraclePPTOn_weakSampleQuery :
    IsOraclePPTOn (encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)) encBits
      (fun pair : (ℕ × List Bool) × (Unit × List Bool) => weakSampleQuery pair.1.1) := by
  ppt [weakSampleQuery]

private theorem length_le_of_mem_support_weakSampleQuery {n : ℕ} {reply : List Bool}
    (hreply : reply ∈ OracleComp.support (weakSampleQuery n)) : reply.length ≤ 2 * n + 2 := by
  unfold weakSampleQuery at hreply
  obtain ⟨point, hpoint, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hreply
  change point ∈ OracleComp.support
    (ProbOracleComp.sample (BitString.sampleList n)) at hpoint
  rw [ProbOracleComp.support_sample, BitString.eval_sampleList] at hpoint
  have hpointLen : point.length = n := BitString.length_of_mem_support_uniformList hpoint
  obtain ⟨answer, hanswer, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hreply
  obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hanswer
  have hreplyEq := OracleComp.eq_of_mem_supportWith_pure hreply
  subst hreplyEq
  have htake : (raw.take n).length ≤ n := List.length_take_le _ _
  simp only [List.length_append, hpointLen]
  lia

/-- `weakToPrfDistinguisher` preserves strict oracle-PPT admissibility. -/
theorem isOraclePPT_weakToPrfDistinguisher {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (weakToPrfDistinguisher adversary) := by
  let ECaller := encPair encUnary encBits
  have hprepare : ComputableInPolyTime
      (fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      ECaller (encPair encUnary encBits) := by
    dsimp only [ECaller]; fun_prop
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => 2 * pair.1.1 + 2)
      (encPair ECaller encBits) encUnary := by
    dsimp only [ECaller]; exact .of_tidy (by fun_prop)
  have hrun : IsOraclePPTOn ECaller encBool
      (fun caller : ℕ × List Bool => OracleComp.interpret
        (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m))
          (fun _ : Unit × List Bool => weakSampleQuery caller.1)) (adversary caller.1 [])) :=
    IsOraclePPTOn.interpret_preprocess_open' (input := ECaller)
      (handler := fun caller _ => weakSampleQuery caller.1)
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (resources := fun caller _ => 2 * caller.1 + 2)
      hadversary hprepare isOraclePPTOn_weakSampleQuery hres
      (fun _ _ _ hreply => length_le_of_mem_support_weakSampleQuery hreply)
  exact hrun.isOraclePPT

private theorem interpret_unifFin_self {α : Type} (program : ProbComp α) :
    OracleComp.interpret ProbComp.unifFin program = program :=
  OracleComp.interpret_query_eq_self program

/-- Against any deterministic oracle with answers of width at most `n` on `n`-bit points,
`weakToPrfDistinguisher` has the same law as the weak experiment on that oracle. -/
private theorem eval_interpret_weakToPrfDistinguisher (adversary : OracleDistinguisher) (n : ℕ)
    (oracle : List Bool → List Bool)
    (hlen : ∀ point, point.length = n → (oracle point).length ≤ n) :
    ProbComp.eval (OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin (fun request => pure (oracle request.2)))
      (weakToPrfDistinguisher adversary n [])) =
    ProbComp.eval (OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifFin (fun _ => weakSample n oracle))
      (adversary n [])) := by
  unfold weakToPrfDistinguisher
  rw [OracleComp.interpret_interpret, ProbComp.eval_interpret, ProbOracleComp.eval_interpret]
  congr 1
  funext q
  rcases q with m | request
  · simp only [ProbComp.unifFin, ProbOracleComp.interpret_sample, OracleComp.interpret_query,
      ProbComp.unifOracle]
    exact ProbComp.eval_unifFin m
  · simp only [OracleComp.sumHandler, weakSampleQuery, weakSample, OracleComp.interpret_bind,
      ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query, OracleComp.interpret_pure,
      OracleComp.interpret_map, interpret_unifFin_self, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map]
    refine PMF.bind_congr_on_support _ _ _ fun point hpoint => ?_
    rw [BitString.eval_sampleList] at hpoint
    have hpointLen : point.length = n := BitString.length_of_mem_support_uniformList hpoint
    rw [List.take_of_length_le (hlen point hpointLen)]

/-- The reduction turns the adaptive real game into the weak real game. -/
theorem eval_prfRealGame_weakToPrfDistinguisher (family : List Bool → List Bool → List Bool)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfRealGame family (weakToPrfDistinguisher adversary) n) =
      ProbComp.eval (weakPrfRealGame family adversary n) := by
  simp only [prfRealGame, weakPrfRealGame, ProbComp.eval_bind]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
  rw [BitString.eval_sampleList] at hkey
  have hkeyLen : key.length = n := BitString.length_of_mem_support_uniformList hkey
  refine eval_interpret_weakToPrfDistinguisher adversary n _ fun point hpoint => ?_
  simp only [prfOracle, hpoint, ↓reduceIte]
  rw [hlen key point (by rw [hpoint, hkeyLen]), hkeyLen]

/-- The reduction turns the adaptive ideal game into the weak ideal game. -/
theorem eval_prfIdealGame_weakToPrfDistinguisher (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame (weakToPrfDistinguisher adversary) n) =
      ProbComp.eval (weakPrfIdealGame adversary n) := by
  simp only [prfIdealGame, weakPrfIdealGame, ProbComp.eval_bind]
  congr 1
  funext table
  refine eval_interpret_weakToPrfDistinguisher adversary n _ fun point hpoint => ?_
  simp [randomFunctionOracle, hpoint]

/-- **Every pseudorandom function is weak** ([KatzLindell2020], Exercise 3.28(a)): an adversary
that only sees random points can be simulated by one that chooses those points itself. -/
theorem PseudorandomFunction.weakPseudorandomFunction
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    WeakPseudorandomFunction family where
  polyTime := hprf.polyTime
  length_eq := hprf.length_eq
  secure adversary hadversary :=
    (hprf.secure _ (isOraclePPT_weakToPrfDistinguisher hadversary)).congr fun n => by
      dsimp only
      rw [eval_prfRealGame_weakToPrfDistinguisher family hprf.length_eq,
        eval_prfIdealGame_weakToPrfDistinguisher]

/-! ### Zero patching -/

/-- Answer an all-zero query by the query itself, and every other query by the family. -/
@[expose]
def zeroPatch (family : List Bool → List Bool → List Bool) (key query : List Bool) :
    List Bool :=
  if query == List.replicate query.length false then query else family key query

/-- Zero patching preserves plain polynomial-time evaluation. -/
theorem computableInPolyTime_zeroPatch {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ComputableInPolyTime (fun pair : List Bool × List Bool => zeroPatch family pair.1 pair.2)
      (encPair encBits encBits) encBits := by
  unfold zeroPatch
  fun_prop

/-- Zero patching preserves the answer width. -/
theorem length_zeroPatch {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (key query : List Bool) (hquery : query.length = key.length) :
    (zeroPatch family key query).length = key.length := by
  unfold zeroPatch
  split_ifs
  · exact hquery
  · exact hlen key query hquery

/-- On the all-zero query the patched family returns the query itself. -/
theorem zeroPatch_replicate_false (family : List Bool → List Bool → List Bool)
    (key : List Bool) (n : ℕ) :
    zeroPatch family key (List.replicate n false) = List.replicate n false := by
  simp [zeroPatch]

/-! ### The MAC from a zero-patched family is forgeable -/

/-- Output the all-zero message with the all-zero tag, without any tagging query. -/
@[expose]
noncomputable def zeroForger : Forger :=
  fun n _ => pure (List.replicate n false, List.replicate n false)

/-- `zeroForger` is uniformly strict oracle-PPT. -/
theorem isOraclePPT_zeroForger : IsOraclePPT (encPair encBits encBits) zeroForger := by
  ppt [zeroForger]

/-- `zeroForger` always wins against the MAC built from a zero-patched family. -/
theorem eval_eufCmaGame_prfMAC_zeroPatch_zeroForger
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime
      (fun pair : List Bool × List Bool => zeroPatch family pair.1 pair.2)
      (encPair encBits encBits) encBits) (n : ℕ) :
    ProbComp.eval ((prfMAC (zeroPatch family) hpoly).eufCmaGame zeroForger n) = PMF.pure true := by
  simp only [MACScheme.eufCmaGame, zeroForger, OracleComp.interpret_pure, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_pure]
  refine (PMF.bind_congr_on_support _ _ _ fun key hkey => ?_).trans (PMF.bind_const _ _)
  simp only [prfMAC, BitString.eval_sampleList] at hkey ⊢
  have hkeyLen : key.length = n := BitString.length_of_mem_support_uniformList hkey
  simp [zeroPatch_replicate_false, hkeyLen]

/-- **A forgeable MAC from a patched family** ([KatzLindell2020], Exercise 4.9): the fixed-length
MAC built from a zero-patched family is never `EUFCMA`. -/
theorem not_eufCma_prfMAC_zeroPatch {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime
      (fun pair : List Bool × List Bool => zeroPatch family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ¬ (prfMAC (zeroPatch family) hpoly).EUFCMA := by
  intro heuf
  have hone : Negligible (fun _ : ℕ => (1 : ℝ≥0)) :=
    (heuf.negligible zeroForger isOraclePPT_zeroForger).congr fun n => by
      simp [Game.succProbability, eval_eufCmaGame_prfMAC_zeroPatch_zeroForger hpoly n]
  exact not_negligible_const one_ne_zero hone

/-- No zero-patched family is a pseudorandom function: its MAC would otherwise be `EUFCMA`. -/
theorem not_pseudorandomFunction_zeroPatch (family : List Bool → List Bool → List Bool) :
    ¬ PseudorandomFunction (zeroPatch family) := fun hprf =>
  not_eufCma_prfMAC_zeroPatch hprf.polyTime hprf.eufCma_prfMAC

/-! ### Zero patching preserves weak security -/

/-- The law of a weak-PRF adversary whose calls are answered by `weakSample n oracle`. -/
private noncomputable def weakRun {α : Type} (n : ℕ) (oracle : List Bool → List Bool)
    (program : WordOracleComp Unit α) : PMF α :=
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle (fun _ => ProbComp.eval (weakSample n oracle)))
    program

private theorem weakRun_query_bind {α : Type} (n : ℕ) (oracle : List Bool → List Bool)
    (q : ℕ ⊕ (Unit × List Bool))
    (k : probOracleSpec (fun _ : Unit × List Bool => List Bool) q →
      OracleComp (probOracleSpec (fun _ : Unit × List Bool => List Bool)) α) :
    weakRun n oracle (OracleComp.query q >>= k) =
      (OracleComp.sumHandler ProbComp.unifOracle
        (fun _ => ProbComp.eval (weakSample n oracle)) q).bind
        (fun x => weakRun n oracle (k x)) := by
  simp only [weakRun, OracleComp.interpret_bind, OracleComp.interpret_query]
  rfl

private theorem eval_weakSample (n : ℕ) (oracle : List Bool → List Bool) :
    ProbComp.eval (weakSample n oracle) =
      (BitString.uniformList n).bind (fun point => PMF.pure (point ++ oracle point)) := by
  simp only [weakSample, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]

/-- Pointwise bounds away from one exceptional first-stage result bound a two-stage experiment,
up to the probability of that result. -/
private theorem bind_apply_le_add_of_ne {T β : Type} (μ : PMF T) (F G : T → PMF β) (b : β)
    (bad : T) {ε : ℝ≥0∞} (h : ∀ t, t ≠ bad → F t b ≤ G t b + ε) :
    μ.bind F b ≤ μ.bind G b + ε + μ bad := by
  classical
  have hpoint (t : T) :
      μ t * F t b ≤ μ t * G t b + μ t * ε + if t = bad then μ bad else 0 := by
    by_cases ht : t = bad
    · subst ht
      rw [ite_eq_left_of_eq_true _ _ (eq_self t)]
      exact le_add_of_le_right (mul_le_of_le_one_right zero_le (PMF.coe_le_one _ _))
    · simp only [ht, ↓reduceIte, add_zero]
      rw [← mul_add]
      exact mul_le_mul_right (h t ht) _
  simp only [PMF.bind_apply]
  calc ∑' t, μ t * F t b
      ≤ ∑' t, (μ t * G t b + μ t * ε + if t = bad then μ bad else 0) :=
        tsum_le_tsum hpoint
    _ = ∑' t, μ t * G t b + ε + μ bad := by
        rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
          tsum_ite_eq]

/-- Two weak oracles that agree away from the all-zero point give laws that differ by at most
`2⁻ⁿ` per call. -/
private theorem weakRun_apply_le {α : Type} (n : ℕ) (first second : List Bool → List Bool)
    (hagree : ∀ point, point ≠ List.replicate n false → first point = second point)
    {Q : ℕ} {program : WordOracleComp Unit α} (hq : program.IsQueryBounded Q) (a : α) :
    weakRun n first program a ≤ weakRun n second program a + Q * (2 ^ n)⁻¹ := by
  induction hq with
  | pure b Q =>
    simp only [weakRun, OracleComp.interpret_pure]
    exact le_self_add
  | liftBind q k Q _ ih =>
    rcases q with m | request
    · rw [weakRun_query_bind, weakRun_query_bind]
      simp only [Sum.elim_inl, Nat.add_zero]
      exact PMF.bind_apply_le_add_const_on_support _ a fun x _ => ih x
    · rw [weakRun_query_bind, weakRun_query_bind]
      simp only [Sum.elim_inr, OracleComp.sumHandler, eval_weakSample, PMF.bind_bind,
        PMF.pure_bind]
      refine (bind_apply_le_add_of_ne (BitString.uniformList n)
        (fun point => weakRun n first (k (point ++ first point)))
        (fun point => weakRun n second (k (point ++ second point))) a
        (List.replicate n false) (ε := (Q : ℝ≥0∞) * (2 ^ n)⁻¹) fun point hpoint => ?_).trans ?_
      · simp only [hagree point hpoint]
        exact ih _
      · rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc]
        exact add_le_add le_rfl ((BitString.uniformList_apply_le n _).trans_eq (one_div _))

/-- Zero patching moves the weak real game by at most `Q / 2ⁿ` against an adversary making at
most `Q` calls: the two games differ only when a uniform point is all-zero. -/
theorem advantage_weakPrfRealGame_zeroPatch_le (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n Q : ℕ) (hq : (adversary n []).IsQueryBounded Q) :
    (Game.advantage (ProbComp.eval (weakPrfRealGame (zeroPatch family) adversary n))
      (ProbComp.eval (weakPrfRealGame family adversary n)) : ℝ) ≤ Q / 2 ^ n := by
  have heval (f : List Bool → List Bool → List Bool) :
      ProbComp.eval (weakPrfRealGame f adversary n) = (BitString.uniformList n).bind
        (fun key => weakRun n (prfOracle f n key) (adversary n [])) := by
    simp only [weakPrfRealGame, ProbComp.eval_bind, BitString.eval_sampleList,
      ProbOracleComp.eval_interpret]
    rfl
  have hagree (key point : List Bool) (hpoint : point ≠ List.replicate n false) :
      prfOracle (zeroPatch family) n key point = prfOracle family n key point := by
    by_cases hlen : point.length = n
    · simp [prfOracle, zeroPatch, hlen, hpoint]
    · simp [prfOracle, hlen]
  have hne : (Q : ℝ≥0∞) * (2 ^ n)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top Q)
      (ENNReal.inv_ne_top.mpr (pow_ne_zero _ two_ne_zero))
  have hfirst : ProbComp.eval (weakPrfRealGame (zeroPatch family) adversary n) true ≤
      ProbComp.eval (weakPrfRealGame family adversary n) true + Q * (2 ^ n)⁻¹ := by
    rw [heval, heval]
    exact PMF.bind_apply_le_add_const_on_support _ true fun key _ =>
      weakRun_apply_le n _ _ (hagree key) hq true
  have hsecond : ProbComp.eval (weakPrfRealGame family adversary n) true ≤
      ProbComp.eval (weakPrfRealGame (zeroPatch family) adversary n) true + Q * (2 ^ n)⁻¹ := by
    rw [heval, heval]
    exact PMF.bind_apply_le_add_const_on_support _ true fun key _ =>
      weakRun_apply_le n _ _ (fun point hpoint => (hagree key point hpoint).symm) hq true
  have hadv := Game.advantage_le_of_apply_le hne hfirst hsecond
  simpa [ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv] using hadv

/-- **Zero patching preserves weak pseudorandomness**: a weak adversary sees the all-zero point
with probability `2⁻ⁿ` per call, so the patched family stays weakly pseudorandom. -/
theorem WeakPseudorandomFunction.zeroPatch {family : List Bool → List Bool → List Bool}
    (hweak : WeakPseudorandomFunction family) : WeakPseudorandomFunction (zeroPatch family) where
  polyTime := computableInPolyTime_zeroPatch hweak.polyTime
  length_eq := length_zeroPatch hweak.length_eq
  secure adversary hadversary := by
    obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
    let Q : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
    have hq (n : ℕ) : (adversary n []).IsQueryBounded (Q n) := by
      simpa only [Q, List.length_nil, Nat.add_zero] using (hqbounds n []).1
    have hpolyQ : PolynomiallyBounded Q := by
      dsimp only [Q]; fun_prop
    have hpatch :=
      (negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num)).polynomiallyBounded_mul hpolyQ
    refine negligible_of_le ((hweak.secure adversary hadversary).add hpatch) fun n => ?_
    have htri := NNReal.coe_le_coe.mpr (Game.advantage_triangle
      (ProbComp.eval (weakPrfRealGame (Cslib.Crypto.zeroPatch family) adversary n))
      (ProbComp.eval (weakPrfRealGame family adversary n))
      (ProbComp.eval (weakPrfIdealGame adversary n)))
    have hbound := advantage_weakPrfRealGame_zeroPatch_le family adversary n (Q n) (hq n)
    rw [← NNReal.coe_le_coe]
    simp only [Pi.add_apply, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at htri ⊢
    have hgeom : (Q n : ℝ) * (1 / 2) ^ n = Q n / 2 ^ n := by
      rw [one_div, inv_pow, div_eq_mul_inv]
    linarith

/-! ### Separations -/

/-- **A weak pseudorandom function that is not pseudorandom** ([KatzLindell2020],
Exercise 3.28(b)): zero patching any pseudorandom function gives one. -/
theorem PseudorandomFunction.exists_weak_not_pseudorandom
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    ∃ weak, WeakPseudorandomFunction weak ∧ ¬ PseudorandomFunction weak :=
  ⟨zeroPatch family, hprf.weakPseudorandomFunction.zeroPatch,
    not_pseudorandomFunction_zeroPatch family⟩

/-- **A weak pseudorandom function with a forgeable MAC** ([KatzLindell2020], Exercise 4.9):
zero patching any pseudorandom function gives a weak pseudorandom function whose fixed-length
MAC is not `EUFCMA`. -/
theorem PseudorandomFunction.exists_weak_not_eufCma_prfMAC
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    ∃ weak, ∃ hweak : WeakPseudorandomFunction weak, ¬ (prfMAC weak hweak.polyTime).EUFCMA :=
  ⟨zeroPatch family, hprf.weakPseudorandomFunction.zeroPatch, not_eufCma_prfMAC_zeroPatch _⟩

end Cslib.Crypto
