/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Complexity.Logics.Propositional.CNF.ThreeCNF
public import Mathlib.Data.Nat.Pairing
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Logics.Propositional.CNF.ThreeCNF.PolyTime

/-!
# 3SAT

`ThreeSAT` is the set of satisfiable formulas in conjunctive normal form whose clauses have at most
three literals [Arora and Barak, Section 2.3.1][AroraBarak09]. `toThreeSAT` maps a formula to an
equisatisfiable one of width three, by splitting its clauses (`Cslib.Logic.PL.CNF.to3CNF`) and
numbering the variables injectively. Combining `CNF.isPolyTime_to3CNF` with binary variable
relabelling and the Cook–Levin theorem proves that `ThreeSAT` is `NP`-complete.

## Main definitions

* `Cslib.Complexity.ThreeSAT`.
* `Cslib.Complexity.toThreeSAT`.
* `Cslib.Complexity.ThreeSAT.verifier`: clause-width check combined with `SAT.verifier`.

## Main results

* `Cslib.Complexity.mem_ThreeSAT_toThreeSAT_iff`: `φ ∈ SAT ↔ toThreeSAT φ ∈ ThreeSAT`.
* `Cslib.Complexity.computableInPolyTime_toThreeSAT`: `toThreeSAT` is polynomial-time.
* `Cslib.Complexity.ThreeSAT.isVerifier`, `Cslib.Complexity.ThreeSAT.mem_NP`: `ThreeSAT ∈ NP`.
* `Cslib.Complexity.polyTimeReducible_SAT_ThreeSAT`, `Cslib.Complexity.ThreeSAT_npHard`,
  `Cslib.Complexity.ThreeSAT_npComplete`: `ThreeSAT` is `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The satisfiable formulas whose clauses have at most three literals [Karp1972],
[Arora and Barak, Section 2.3.1][AroraBarak09]. -/
def ThreeSAT : Set (CNF ℕ) := {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ φ.Satisfiable}

/-- An injective numbering of the variables of a split formula: original variables at even
numbers, auxiliary variables at odd numbers through `Nat.pair`. -/
def splitVarToNat : ℕ ⊕ (ℕ × ℕ) → ℕ :=
  Sum.elim (2 * ·) fun p => 2 * Nat.pair p.1 p.2 + 1

theorem splitVarToNat_injective : Function.Injective splitVarToNat := by
  rintro (a | ⟨a₁, a₂⟩) (b | ⟨b₁, b₂⟩) h <;> simp only [splitVarToNat, Sum.elim_inl,
    Sum.elim_inr] at h
  · rw [show a = b by omega]
  · omega
  · omega
  · have : Nat.pair a₁ a₂ = Nat.pair b₁ b₂ := by omega
    rw [Nat.pair_eq_pair] at this
    rw [this.1, this.2]

/-- The reduction from `SAT` to `ThreeSAT`: split the clauses, then number the variables. -/
def toThreeSAT (φ : CNF ℕ) : CNF ℕ := φ.to3CNF.relabel splitVarToNat

/-- **Correctness of the reduction**: `toThreeSAT φ` is in `ThreeSAT` exactly when `φ` is in
`SAT`. -/
theorem mem_ThreeSAT_toThreeSAT_iff (φ : CNF ℕ) : toThreeSAT φ ∈ ThreeSAT ↔ φ ∈ SAT := by
  refine ⟨fun h => ?_, fun h => ⟨fun c hc => ?_, ?_⟩⟩
  · exact (CNF.satisfiable_to3CNF φ).1 ((CNF.satisfiable_relabel splitVarToNat_injective _).1 h.2)
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    simpa using CNF.length_le_three_of_mem_to3CNF hd
  · exact (CNF.satisfiable_relabel splitVarToNat_injective _).2 ((CNF.satisfiable_to3CNF φ).2 h)

/-! ### Polynomial-time reduction and NP-completeness -/

private theorem encNat_two_mul (n : ℕ) :
    encNat (2 * n) = if (encNat n).isEmpty then [] else false :: encNat n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · have hne : n.bits ≠ [] := fun h => hn.ne' (encNat.injective h)
    simp [hne, Nat.bit0_bits n hn.ne']

private theorem encNat_two_mul_add_one (n : ℕ) :
    encNat (2 * n + 1) = true :: encNat n :=
  Nat.bit1_bits n

/-- Variable numbering after clause splitting is polynomial-time: original binary variables shift
by one bit, and unary fresh-variable pairs are paired and converted to odd binary numbers. -/
@[fun_prop]
theorem computableInPolyTime_splitVarToNat :
    ComputableInPolyTime splitVarToNat
      (encSum encNat (encPair encUnary encUnary)) encNat := by
  let encS := encSum encNat (encPair encUnary encUnary)
  let D₁ : Decoder encNat := .nat
  let D₂ : Decoder (encPair encUnary encUnary) := .pair .unary .unary
  have hraw : ComputableInPolyTime (fun x => encS x) encS encBits := .of_eq fun _ => rfl
  have hc : ComputableInPolyTime Sum.isRight encS encBool :=
    ((ComputableInPolyTime.headD false).comp hraw).of_enc_eq fun x => by cases x <;> rfl
  have hpair : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    unfold Nat.pair
    fun_prop
  have hdouble : ComputableInPolyTime (2 * ·) encNat encNat :=
    (show ComputableInPolyTime
        (fun n : ℕ => if (encNat n).isEmpty then ([] : List Bool) else false :: encNat n)
        encNat encBits by fun_prop).of_enc_eq encNat_two_mul
  have hodd : ComputableInPolyTime (fun n : ℕ => 2 * n + 1) encNat encNat :=
    (show ComputableInPolyTime (fun n : ℕ => true :: encNat n)
        encNat encBits by fun_prop).of_enc_eq encNat_two_mul_add_one
  have hl : ComputableInPolyTime (fun x => 2 * D₁.decode (encS x).tail) encS encNat :=
    hdouble.comp (D₁.computableInPolyTime.comp (ComputableInPolyTime.bitsTail.comp hraw))
  have hr : ComputableInPolyTime
      (fun x => 2 * (let p := D₂.decode (encS x).tail; Nat.pair p.1 p.2) + 1) encS encNat :=
    hodd.comp (ComputableInPolyTime.unary_to_binary.comp
      (hpair.comp (D₂.computableInPolyTime.comp (ComputableInPolyTime.bitsTail.comp hraw))))
  refine (hc.ite hr hl).of_enc_eq fun x => ?_
  rcases x with a | ⟨b, c⟩
  · rw [encNat.injective.eq_iff]
    simp only [splitVarToNat, encS, encSum_inl, List.tail_cons, Sum.isRight_inl,
      Bool.false_eq_true, ↓reduceIte, Sum.elim_inl, D₁.decode_enc]
  · rw [encNat.injective.eq_iff]
    simp only [splitVarToNat, encS, encSum_inr, List.tail_cons, Sum.isRight_inr,
      ↓reduceIte, Sum.elim_inr, D₂.decode_enc]

/-- The reduction `toThreeSAT` is computable in polynomial time under `encCNF`. -/
@[fun_prop]
theorem computableInPolyTime_toThreeSAT :
    ComputableInPolyTime toThreeSAT encCNF encCNF :=
  (CNF.computableInPolyTime_relabel computableInPolyTime_splitVarToNat).comp
    (CNF.isPolyTime_to3CNF encNat)

namespace ThreeSAT

/-- The verifier for `ThreeSAT`: check that every clause has at most three literals and evaluate
the formula under the certificate assignment. -/
def verifier (x : CNF ℕ × List Bool) : Bool :=
  (x.1.all fun c => decide (c.length ≤ 3)) && SAT.verifier x

/-- `ThreeSAT.verifier` verifies `ThreeSAT` with certificates as long as the encoded formula: it
is `SAT.verifier` guarded by the clause-width test. -/
theorem isVerifier : IsVerifier encCNF Polynomial.X verifier ThreeSAT := by
  have h : ThreeSAT = {φ | (φ.all fun c => decide (c.length ≤ 3)) = true ∧ φ ∈ SAT} := by
    ext φ
    simp only [ThreeSAT, Set.mem_ofPred_eq, List.all_eq_true, decide_eq_true_eq, mem_SAT]
  rw [h]
  exact SAT.isVerifier.guard

/-- Checking the clause-width bound and evaluating the formula is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encCNF encBits) encBool := by
  unfold verifier
  fun_prop

/-- `ThreeSAT` belongs to `NP`. -/
theorem mem_NP : ThreeSAT ∈ NP encCNF :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end ThreeSAT

/-- `SAT` reduces to `ThreeSAT` in polynomial time via `toThreeSAT`. -/
theorem polyTimeReducible_SAT_ThreeSAT : PolyTimeReducible encCNF encCNF SAT ThreeSAT :=
  ⟨toThreeSAT, computableInPolyTime_toThreeSAT,
    fun φ => (mem_ThreeSAT_toThreeSAT_iff φ).symm⟩

/-- `ThreeSAT` is `NP`-hard. -/
theorem ThreeSAT_npHard : NPHard encCNF ThreeSAT :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_ThreeSAT

/-- **3SAT is NP-complete** [Karp1972]. -/
theorem ThreeSAT_npComplete : NPComplete encCNF ThreeSAT :=
  ⟨ThreeSAT.mem_NP, ThreeSAT_npHard⟩

end Cslib.Complexity
