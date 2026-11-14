/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Inclusions
public import CslibFrontier.Computability.Complexity.Classes.IP.PSPACE
public import CslibFrontier.Computability.Complexity.Classes.IP.Reduction
public import CslibFrontier.Computability.Complexity.Classes.IP.Repetition
public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Complexity.Classes.Space.TQBF
import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# `IP = PSPACE` and threshold characterizations of `IP`

Every problem in `PSPACE` reduces to `TQBF` in polynomial time
(`Cslib.Complexity.TQBF_pspaceHard`), `TQBF` has an interactive proof
(`Cslib.Complexity.TQBF_mem_IP`), and `IP` is closed under polynomial-time reductions
(`Cslib.Complexity.PolyTimeReducible.mem_IP`), so `PSPACE ⊆ IP`. With `IP ⊆ PSPACE`
(`Cslib.Complexity.IP_subset_PSPACE`) this is the theorem of Shamir [Shamir][Shamir1992], with the
simplification of Shen [Shen][Shen1992], following Lund, Fortnow, Karloff and Nisan
[LundFortnowKarloffNisan1992]; see [Arora and Barak, Section 8.3][AroraBarak09]. Every class of
the polynomial hierarchy, in particular `coNP`, has interactive proofs.

Because `QBFProtocol.verifier` has perfect completeness (`QBFProtocol.isInteractiveProof_verifier`),
reducing an arbitrary `IP` problem through `PSPACE` to `TQBF` gives an interactive proof with
completeness `1` and soundness error `1 / 3` (`Cslib.Complexity.IP_eq_setOf_isInteractiveProof_one`,
[Arora and Barak, Chapter 8, Exercise 1(d)][AroraBarak07]). Repeating that protocol `k a` times in
sequence via `Cslib.Complexity.sequentialRepeat` preserves completeness `1` while reducing the
soundness error to `(1 / 3) ^ k a ≤ (2 ^ k a)⁻¹`
(`Cslib.Complexity.exists_isInteractiveProof_one_pow_of_mem_IP`), so `IP` is also unchanged when
completeness `1 - 2 ^ (-|enc a|)` and soundness `2 ^ (-|enc a|)` are required
(`Cslib.Complexity.IP_eq_setOf_acceptProb_two_pow_length`,
[Arora and Barak, Chapter 8, Exercise 1(c)][AroraBarak07]).

The classes are those of the library: `IP` with private fair coins, a strict polynomial clock for
one oracle machine against every stateful prover, completeness `2 / 3` and soundness `1 / 3`, and
`PSPACE` decided by one deterministic machine in polynomial space, with respect to any encoding of
the instances.

## Main results

* `Cslib.Complexity.PSPACE_subset_IP`, `Cslib.Complexity.IP_eq_PSPACE`.
* `Cslib.Complexity.PH_subset_IP`, `Cslib.Complexity.coNP_subset_IP`.
* `Cslib.Complexity.exists_isInteractiveProof_one_of_mem_IP`,
  `Cslib.Complexity.mem_IP_iff_exists_isInteractiveProof_one`,
  `Cslib.Complexity.IP_eq_setOf_isInteractiveProof_one`: perfect completeness for `IP`.
* `Cslib.Complexity.exists_isInteractiveProof_one_pow_of_mem_IP`,
  `Cslib.Complexity.mem_IP_iff_exists_acceptProb_two_pow_length`,
  `Cslib.Complexity.IP_eq_setOf_acceptProb_two_pow_length`: exponential amplification for `IP`.

## References

* [C. Lund, L. Fortnow, H. Karloff, N. Nisan, *Algebraic methods for interactive proof
  systems*][LundFortnowKarloffNisan1992]
* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type} (enc : α ↪ List Bool)

/-- **`PSPACE ⊆ IP`** [Shamir][Shamir1992]: every problem in `PSPACE` reduces to `TQBF`, which has
an interactive proof. -/
theorem PSPACE_subset_IP : PSPACE enc ⊆ IP enc :=
  fun A hA => (TQBF_pspaceHard enc A hA).mem_IP TQBF_mem_IP

/-- **`IP = PSPACE`** [Lund, Fortnow, Karloff and Nisan][LundFortnowKarloffNisan1992],
[Shamir][Shamir1992], [Shen][Shen1992]. -/
theorem IP_eq_PSPACE : IP enc = PSPACE enc :=
  (IP_subset_PSPACE enc).antisymm (PSPACE_subset_IP enc)

/-- **Every class of the polynomial hierarchy has interactive proofs.** -/
theorem PH_subset_IP : PH enc ⊆ IP enc :=
  PH_subset_PSPACE.trans (PSPACE_subset_IP enc)

/-- **`coNP ⊆ IP`** [Lund, Fortnow, Karloff and Nisan][LundFortnowKarloffNisan1992]. -/
theorem coNP_subset_IP : coNP enc ⊆ IP enc :=
  coNP_subset_PH.trans (PH_subset_IP enc)

/-! ### Perfect completeness and exponential amplification for `IP` -/

/-- Sequential repetition of `QBFProtocol.verifier` accepts `QBFProtocol.honestProver` with
probability `1` on every true closed formula. -/
theorem QBFProtocol.acceptProb_sequentialRepeat_verifier_honestProver {ψ : Logic.PL.QBF ℕ}
    (hψ : ψ ∈ TQBF) (k : ℕ) :
    acceptProb (sequentialRepeat k (QBFProtocol.verifier ψ)) (QBFProtocol.honestProver ψ) = 1 := by
  refine le_antisymm (PMF.coe_le_one _ _) ?_
  simpa using le_acceptProb_sequentialRepeat (c := 1) (QBFProtocol.honestProver ψ)
    (fun s => by
      change 1 ≤ acceptProb (QBFProtocol.verifier ψ) (QBFProtocol.honestProver ψ)
      exact (QBFProtocol.acceptProb_verifier_honestProver ψ hψ).ge) k

/-- **Perfect completeness and sequential amplification for `IP`**
[Arora and Barak, Chapter 8, Exercise 1(c)–(d)][AroraBarak07]: for every `A ∈ IP enc` and every
repetition count `k : α → ℕ` computable in unary polynomial time, there is a strict oracle-PPT
verifier that accepts some prover with probability `1` on members of `A` and accepts every
prover with probability at most `(1 / 3) ^ k a` on non-members. -/
theorem exists_isInteractiveProof_one_pow_of_mem_IP {A : Set α} (hA : A ∈ IP enc) {k : α → ℕ}
    (hk : ComputableInPolyTime k enc encUnary) :
    ∃ verifier : α → WordOracleComp Unit Bool, IsOraclePPTOn enc encBool verifier ∧
      (∀ a ∈ A, ∃ P : Prover Unit, acceptProb (verifier a) P = 1) ∧
      (∀ a ∉ A, ∀ P : Prover Unit, acceptProb (verifier a) P ≤ (1 / 3 : ENNReal) ^ k a) := by
  obtain ⟨f, hf, hfA⟩ := TQBF_pspaceHard enc A (IP_subset_PSPACE enc hA)
  refine ⟨fun a => sequentialRepeat (k a) (QBFProtocol.verifier (f a)),
    (QBFProtocol.isOraclePPTOn_verifier.preprocess' hf).sequentialRepeat_count hk,
    fun a ha => ⟨QBFProtocol.honestProver (f a),
      QBFProtocol.acceptProb_sequentialRepeat_verifier_honestProver ((hfA a).1 ha) (k a)⟩,
    fun a ha P => acceptProb_sequentialRepeat_le
      (QBFProtocol.isInteractiveProof_verifier.sound (f a) fun h => ha ((hfA a).2 h)) (k a) P⟩

/-- **Perfect completeness for `IP`** [Arora and Barak, Chapter 8, Exercise 1(d)][AroraBarak07]:
every problem in `IP` has a strict oracle-PPT interactive proof with completeness `1` and
soundness error `1 / 3`. -/
theorem exists_isInteractiveProof_one_of_mem_IP {A : Set α} (hA : A ∈ IP enc) :
    ∃ verifier : α → WordOracleComp Unit Bool,
      IsOraclePPTOn enc encBool verifier ∧ IsInteractiveProof verifier A 1 (1 / 3) := by
  obtain ⟨f, hf, hfA⟩ := TQBF_pspaceHard enc A (IP_subset_PSPACE enc hA)
  exact ⟨fun a => QBFProtocol.verifier (f a),
    QBFProtocol.isOraclePPTOn_verifier.preprocess' hf,
    QBFProtocol.isInteractiveProof_verifier.comp hfA⟩

/-- A problem is in `IP` if and only if it has a strict oracle-PPT interactive proof with
completeness `1` and soundness error `1 / 3`
[Arora and Barak, Chapter 8, Exercise 1(d)][AroraBarak07]. -/
theorem mem_IP_iff_exists_isInteractiveProof_one {A : Set α} :
    A ∈ IP enc ↔ ∃ verifier : α → WordOracleComp Unit Bool,
      IsOraclePPTOn enc encBool verifier ∧ IsInteractiveProof verifier A 1 (1 / 3) :=
  ⟨exists_isInteractiveProof_one_of_mem_IP enc, fun ⟨_, hV, h⟩ =>
    mem_IP_of hV h (ENNReal.div_le_of_le_mul (by norm_num)) le_rfl⟩

/-- **`IP` with perfect completeness** [Arora and Barak, Chapter 8, Exercise 1(d)][AroraBarak07]:
requiring completeness `1` instead of `2 / 3` defines the same class `IP enc`. -/
theorem IP_eq_setOf_isInteractiveProof_one :
    IP enc = {A | ∃ verifier : α → WordOracleComp Unit Bool,
      IsOraclePPTOn enc encBool verifier ∧ IsInteractiveProof verifier A 1 (1 / 3)} :=
  Set.ext fun _ => mem_IP_iff_exists_isInteractiveProof_one enc

private theorem one_div_three_pow_le_two_pow_inv (n : ℕ) :
    (1 / 3 : ENNReal) ^ n ≤ (2 ^ n : ENNReal)⁻¹ := by
  rw [ENNReal.inv_pow]
  refine pow_le_pow_left' ?_ n
  rw [one_div, ENNReal.inv_le_inv]
  norm_num

private theorem two_pow_inv_le_one_div_three {n : ℕ} (hn : 2 ≤ n) :
    (2 ^ n : ENNReal)⁻¹ ≤ 1 / 3 := by
  rw [one_div, ENNReal.inv_le_inv]
  calc (3 : ENNReal) ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := pow_le_pow_right' (by norm_num) hn

private theorem two_div_three_le_one_sub_two_pow_inv {n : ℕ} (hn : 2 ≤ n) :
    (2 / 3 : ENNReal) ≤ 1 - (2 ^ n : ENNReal)⁻¹ := by
  refine ENNReal.le_sub_of_add_le_right (by simp) ?_
  calc (2 / 3 : ENNReal) + (2 ^ n : ENNReal)⁻¹
      ≤ 2 / 3 + 1 / 3 := add_le_add le_rfl (two_pow_inv_le_one_div_three hn)
    _ = 1 := by
      rw [← ENNReal.add_div, (by norm_num : (2 : ENNReal) + 1 = 3),
        ENNReal.div_self (by norm_num) (by norm_num)]

open Classical in
/-- Override `verifier` on the single encoded word `w` with the exact membership of `w` in the
image of `A` under `enc`. -/
private noncomputable def patchWord (A : Set α) (enc : α ↪ List Bool) (w : List Bool)
    (verifier : α → WordOracleComp Unit Bool) (a : α) : WordOracleComp Unit Bool :=
  if decide (enc a = w) then pure (decide (∃ x ∈ A, enc x = w)) else verifier a

open Classical in
private theorem isOraclePPTOn_patchWord {A : Set α} {w : List Bool}
    {verifier : α → WordOracleComp Unit Bool} (hV : IsOraclePPTOn enc encBool verifier) :
    IsOraclePPTOn enc encBool (patchWord A enc w verifier) :=
  IsOraclePPTOn.cond'
    (((ComputableTidilyInPolyTime.encode enc).computableInPolyTime).decide_eq' (.const w))
    (ComputableInPolyTime.const (decide (∃ x ∈ A, enc x = w))).isOraclePPTOn hV

private noncomputable def patchWords (A : Set α) (enc : α ↪ List Bool) :
    List (List Bool) → (α → WordOracleComp Unit Bool) → α → WordOracleComp Unit Bool
  | [], verifier => verifier
  | w :: ws, verifier => patchWord A enc w (patchWords A enc ws verifier)

private theorem isOraclePPTOn_patchWords {A : Set α} (ws : List (List Bool))
    {verifier : α → WordOracleComp Unit Bool} (hV : IsOraclePPTOn enc encBool verifier) :
    IsOraclePPTOn enc encBool (patchWords A enc ws verifier) := by
  induction ws with
  | nil => exact hV
  | cons w ws ih => exact isOraclePPTOn_patchWord enc ih

open Classical in
private theorem patchWords_apply_of_mem {A : Set α} {ws : List (List Bool)}
    {verifier : α → WordOracleComp Unit Bool} {a : α} (h : enc a ∈ ws) :
    patchWords A enc ws verifier a = pure (decide (a ∈ A)) := by
  induction ws with
  | nil => contradiction
  | cons w ws ih =>
    simp only [patchWords, patchWord]
    by_cases heq : enc a = w
    · simp only [decide_eq_true heq, ↓reduceIte]
      congr 1
      simp only [decide_eq_decide]
      exact ⟨fun ⟨x, hxA, hx⟩ => enc.injective (hx.trans heq.symm) ▸ hxA,
        fun ha => ⟨a, ha, heq⟩⟩
    · simp only [decide_eq_false heq, Bool.false_eq_true, ↓reduceIte]
      exact ih (List.mem_of_ne_of_mem heq h)

open Classical in
private theorem patchWords_apply_of_notMem {A : Set α} {ws : List (List Bool)}
    {verifier : α → WordOracleComp Unit Bool} {a : α} (h : enc a ∉ ws) :
    patchWords A enc ws verifier a = verifier a := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.mem_cons, not_or] at h
    simp only [patchWords, patchWord, decide_eq_false h.1, ↓reduceIte, Bool.false_eq_true]
    exact ih h.2

private theorem two_le_length_of_notMem_shortWords {w : List Bool}
    (h : w ∉ ([[], [false], [true]] : List (List Bool))) : 2 ≤ w.length := by
  cases w with
  | nil => simp at h
  | cons b w =>
    cases b <;> cases w <;> simp at h ⊢

open Classical in
/-- A problem is in `IP` if and only if it has a strict oracle-PPT verifier with completeness at
least `1 - 2 ^ (-|enc a|)` and soundness error at most `2 ^ (-|enc a|)`
[Arora and Barak, Chapter 8, Exercise 1(c)][AroraBarak07]. -/
theorem mem_IP_iff_exists_acceptProb_two_pow_length {A : Set α} :
    A ∈ IP enc ↔ ∃ verifier : α → WordOracleComp Unit Bool,
      IsOraclePPTOn enc encBool verifier ∧
        (∀ a ∈ A, ∃ P : Prover Unit,
          1 - (2 ^ (enc a).length : ENNReal)⁻¹ ≤ acceptProb (verifier a) P) ∧
        (∀ a ∉ A, ∀ P : Prover Unit,
          acceptProb (verifier a) P ≤ (2 ^ (enc a).length : ENNReal)⁻¹) := by
  refine ⟨fun hA => ?_, fun ⟨verifier, hV, hcomp, hsound⟩ => ?_⟩
  · obtain ⟨verifier, hV, hcomp, hsound⟩ :=
      exists_isInteractiveProof_one_pow_of_mem_IP enc hA (ComputableInPolyTime.encoding_length enc)
    refine ⟨verifier, hV, fun a ha => ?_, fun a ha P =>
      (hsound a ha P).trans (one_div_three_pow_le_two_pow_inv _)⟩
    obtain ⟨P, hP⟩ := hcomp a ha
    exact ⟨P, tsub_le_self.trans_eq hP.symm⟩
  · let ws : List (List Bool) := [[], [false], [true]]
    refine ⟨patchWords A enc ws verifier, isOraclePPTOn_patchWords enc ws hV,
      fun a ha => ?_, fun a ha P => ?_⟩
    · by_cases hmem : enc a ∈ ws
      · refine ⟨Prover.const [], ?_⟩
        rw [patchWords_apply_of_mem enc hmem]
        simpa [acceptProb, ha] using ENNReal.div_le_of_le_mul (by norm_num)
      · obtain ⟨P, hP⟩ := hcomp a ha
        refine ⟨P, ?_⟩
        rw [patchWords_apply_of_notMem enc hmem]
        exact (two_div_three_le_one_sub_two_pow_inv
          (two_le_length_of_notMem_shortWords hmem)).trans hP
    · by_cases hmem : enc a ∈ ws
      · rw [patchWords_apply_of_mem enc hmem]
        simp [acceptProb, ha]
      · rw [patchWords_apply_of_notMem enc hmem]
        exact (hsound a ha P).trans
          (two_pow_inv_le_one_div_three (two_le_length_of_notMem_shortWords hmem))

/-- **`IP` with exponential completeness and soundness**
[Arora and Barak, Chapter 8, Exercise 1(c)][AroraBarak07]: requiring completeness
`1 - 2 ^ (-|enc a|)` and soundness error `2 ^ (-|enc a|)` defines the same class `IP enc`. -/
theorem IP_eq_setOf_acceptProb_two_pow_length :
    IP enc = {A | ∃ verifier : α → WordOracleComp Unit Bool,
      IsOraclePPTOn enc encBool verifier ∧
        (∀ a ∈ A, ∃ P : Prover Unit,
          1 - (2 ^ (enc a).length : ENNReal)⁻¹ ≤ acceptProb (verifier a) P) ∧
        (∀ a ∉ A, ∀ P : Prover Unit,
          acceptProb (verifier a) P ≤ (2 ^ (enc a).length : ENNReal)⁻¹)} :=
  Set.ext fun _ => mem_IP_iff_exists_acceptProb_two_pow_length enc

end Cslib.Complexity
