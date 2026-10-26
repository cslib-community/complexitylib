/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Oracle.Diagonal
public import Complexity.Computability.Complexity.Classes.Oracle.Deterministic
public import Complexity.Computability.Complexity.Classes.Oracle.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# An oracle relative to which `P` and `NP` differ

For an oracle language `B`, the unary length language `Cslib.Complexity.unaryLengthLanguage B`
consists of the words `1ⁿ` such that `B` has a word of length `n`. Baker, Gill and Solovay
construct an oracle `B` for which this language is not in `P` relative to `B`, while it is in `NP`
relative to every oracle (a certificate is a word of length `n` in `B`) [BakerGillSolovay1975]; we
follow the proof of [Arora and Barak, Theorem 3.7][AroraBarak09].

The oracle diagonalizes against all candidate deciders at once
(`Cslib.Complexity.exists_oracle_diagonal`). The candidates are the fair-coin tables with one
oracle channel and control states `Fin m`, under the clocks `c * (n + 1) ^ d`, run on `1ⁿ` with
every coin fixed to `false`. They are countably many, and each makes at most one request per
instruction, hence fewer than `2 ^ n` requests for all large `n`. Every decider in `P` relative to
`B` is one of them on the instances `1ⁿ`
(`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`), so none decides the unary length
language (`Cslib.Complexity.exists_unaryLengthLanguage_notMem_PWithOracle`).

The verifier checks that the instance consists of `true` symbols, by a two-state transducer, and
makes one request: the certificate itself
(`Cslib.Complexity.unaryLengthLanguage_mem_NPWithOracle`).
Relative to the diagonal oracle, `P` is therefore strictly contained in `NP`
(`Cslib.Complexity.exists_PWithOracle_ssubset_NPWithOracle`).

## Main definitions

* `Cslib.Complexity.unaryLengthLanguage`: the words `1ⁿ` such that the oracle has a word of
  length `n`.

## Main results

* `Cslib.Complexity.exists_unaryLengthLanguage_notMem_PWithOracle`: for some oracle `B`, the unary
  length language of `B` is not in `P` relative to `B`.
* `Cslib.Complexity.unaryLengthLanguage_mem_NPWithOracle`: the unary length language of every
  oracle is in `NP` relative to it.
* `Cslib.Complexity.exists_PWithOracle_ssubset_NPWithOracle`,
  `Cslib.Complexity.exists_PWithOracle_ne_NPWithOracle`: relative to some oracle, `P ⊊ NP`.

## References

* [T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP Question*][BakerGillSolovay1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Probability

/-- The words `1ⁿ` such that `B` has a word of length `n`. -/
def unaryLengthLanguage (B : Set (List Bool)) : Set (List Bool) :=
  {x | (∀ b ∈ x, b = true) ∧ ∃ w ∈ B, w.length = x.length}

theorem replicate_mem_unaryLengthLanguage {B : Set (List Bool)} {n : ℕ} :
    List.replicate n true ∈ unaryLengthLanguage B ↔ ∃ w ∈ B, w.length = n := by
  simp only [unaryLengthLanguage, Set.mem_ofPred_eq, List.length_replicate]
  exact and_iff_right fun b hb => (List.eq_of_mem_replicate hb)

namespace BakerGillSolovay

/-- A candidate decider: a fair-coin table with `k` work tapes, control `Fin m` and one oracle
channel, together with the constants `c` and `d` of its clock `c * (n + 1) ^ d`. -/
abbrev Candidate : Type := Σ k m : ℕ, MultiTapePTM k Bool (Fin m) Unit × ℕ × ℕ

/-- The clock `c * (n + 1) ^ d` of a candidate on inputs of length `n`. -/
def Candidate.clock (candidate : Candidate) (n : ℕ) : ℕ :=
  candidate.2.2.2.1 * (n + 1) ^ candidate.2.2.2.2

/-- The verdict of a candidate on `1ⁿ`: its clocked run with every coin fixed to `false`, accepting
exactly with output `[true]`. -/
def Candidate.verdict (candidate : Candidate) (n : ℕ) : WordQueryComp Unit Bool :=
  (fun output => decide (output = [true])) <$> candidate.2.2.1.run (pure false)
    (fun op word => OracleComp.query (op, word)) (candidate.clock n) (List.replicate n true)

/-- A candidate makes at most one request per instruction. -/
private theorem Candidate.length_queriesWith_verdict_le (candidate : Candidate) (n : ℕ)
    (A : Set (List Bool)) :
    (OracleComp.queriesWith (languageOracle A) (candidate.verdict n)).length ≤
      candidate.clock n := by
  simp only [verdict, MultiTapePTM.run, MultiTapePTM.runFrom, OracleComp.queriesWith_map]
  exact MultiTapeMachine.length_queriesWith_runConfigFrom_le candidate.2.2.1
    (fun choices => choices false) _ _ _

/-- Every clock is eventually below `2 ^ n`. -/
private theorem Candidate.eventually_clock_lt (candidate : Candidate) :
    ∀ᶠ n in Filter.atTop, candidate.clock n < 2 ^ n :=
  PolynomiallyBounded.eventually_lt_two_pow (f := candidate.clock)
    (by unfold Candidate.clock; fun_prop)

end BakerGillSolovay

open BakerGillSolovay in
/-- **Baker–Gill–Solovay, the lower bound** [Arora and Barak, Theorem 3.7][AroraBarak09]: for some
oracle language `B`, the unary length language of `B` is not decidable in polynomial time relative
to `B`. -/
theorem exists_unaryLengthLanguage_notMem_PWithOracle :
    ∃ B : Set (List Bool), unaryLengthLanguage B ∉ PWithOracle B encBits := by
  obtain ⟨B, hB⟩ := exists_oracle_diagonal Candidate.verdict Candidate.clock
    Candidate.eventually_clock_lt Candidate.length_queriesWith_verdict_le
  refine ⟨B, fun ⟨f, ⟨program, hcertificate, hprogram⟩, hf⟩ => ?_⟩
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcertificate.exists_fin_run_pure_false
  obtain ⟨n, hn⟩ := hB ⟨k, m, machine, c, d⟩
  apply hn
  have hlength : (encBits (List.replicate n true)).length = n := by
    simp [encBits]
  have hverdict := hrun (List.replicate n true) (languageOracle B)
  rw [hprogram, encBool_apply, hlength] at hverdict
  simp only [encBits, Function.Embedding.refl_apply] at hverdict
  have heq : OracleComp.interpret (m := Id) (languageOracle B)
      (Candidate.verdict ⟨k, m, machine, c, d⟩ n) = f (List.replicate n true) := by
    simp only [Candidate.verdict, Candidate.clock, OracleComp.interpret_map]
    rw [hverdict]
    cases f (List.replicate n true) <;> rfl
  rw [heq, ← hf, replicate_mem_unaryLengthLanguage]

namespace BakerGillSolovay

/-- Tracks whether every symbol read so far is `true`, and emits the verdict at the end. -/
private def allTrue : Transducer Bool Bool where
  q₀ := true
  step q b := (q && b, [])
  final q := [q]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem allTrue_run (q : Bool) (x : List Bool) : allTrue.run q x = [q && x.all id] := by
  induction x generalizing q with
  | nil => simp [allTrue]
  | cons b x ih =>
    rw [Transducer.run_cons, ih]
    simp [allTrue, Bool.and_assoc]

/-- Whether the first word consists of `true` symbols only, beside a Boolean, in polynomial
time. -/
private theorem computableTidilyInPolyTime_all_and :
    ComputableTidilyInPolyTime
      (fun pair : (List Bool × List Bool) × Bool => pair.1.1.all id && pair.2)
      (encPair (encPair encBits encBits) encBool) encBool := by
  have hall : ComputableTidilyInPolyTime (fun x : List Bool => x.all id) encBits encBool :=
    (ComputableTidilyInDegree.of_linear (allTrue.computableTidilyInLinearTimeAndSpace fun x => by
      rw [allTrue_run]; simp [encBits, allTrue])).computableTidilyInPolyTime
  have hand : ComputableTidilyInPolyTime (fun q : Bool × Bool => q.1 && q.2)
      (encPair encBool encBool) encBool :=
    (ComputableTidilyInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
      fun q : Bool × Bool => q.1 && q.2).computableTidilyInPolyTime
  exact hand.comp ((hall.comp ((ComputableTidilyInPolyTime.fst encBits encBits).comp
    (ComputableTidilyInPolyTime.fst (encPair encBits encBits) encBool))).prod
    (ComputableTidilyInPolyTime.snd (encPair encBits encBits) encBool))

end BakerGillSolovay

open Classical in
/-- **The unary length language is in `NP` relative to its oracle**: a certificate for `1ⁿ` is a
word of length `n` in the oracle, checked with one request. -/
theorem unaryLengthLanguage_mem_NPWithOracle (B : Set (List Bool)) :
    unaryLengthLanguage B ∈ NPWithOracle B encBits := by
  refine ⟨Polynomial.X, fun xu : List Bool × List Bool => xu.1.all id && decide (xu.2 ∈ B),
    ((computableInPolyTimeWithOracle_mem B).preprocess
      (.of_tidy (ComputableTidilyInPolyTime.snd encBits encBits))).map_with
      (g := fun (xu : List Bool × List Bool) b => xu.1.all id && b)
      (.of_tidy BakerGillSolovay.computableTidilyInPolyTime_all_and), fun x => ?_⟩
  · simp only [unaryLengthLanguage, Set.mem_ofPred_eq, Polynomial.eval_X, encBits,
      Function.Embedding.refl_apply, Bool.and_eq_true, List.all_eq_true, id, decide_eq_true_eq]
    constructor
    · rintro ⟨hall, w, hw, hlength⟩
      exact ⟨w, hlength, hall, hw⟩
    · rintro ⟨w, hlength, hall, hw⟩
      exact ⟨hall, w, hw, hlength⟩

/-- **Baker–Gill–Solovay** [BakerGillSolovay1975], [Arora and Barak, Theorem 3.7][AroraBarak09]:
relative to some oracle language, `P` is strictly contained in `NP`. -/
theorem exists_PWithOracle_ssubset_NPWithOracle :
    ∃ B : Set (List Bool), PWithOracle B encBits ⊂ NPWithOracle B encBits := by
  obtain ⟨B, hB⟩ := exists_unaryLengthLanguage_notMem_PWithOracle
  exact ⟨B, Set.ssubset_iff_subset_ne.mpr ⟨PWithOracle_subset_NPWithOracle B encBits,
    fun h => hB (h ▸ unaryLengthLanguage_mem_NPWithOracle B)⟩⟩

/-- **Baker–Gill–Solovay**: relative to some oracle language, `P ≠ NP`. -/
theorem exists_PWithOracle_ne_NPWithOracle :
    ∃ B : Set (List Bool), PWithOracle B encBits ≠ NPWithOracle B encBits :=
  let ⟨B, hB⟩ := exists_PWithOracle_ssubset_NPWithOracle
  ⟨B, hB.ne⟩

end Cslib.Complexity
