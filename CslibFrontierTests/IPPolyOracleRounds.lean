/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of dynamic-round AM/IP and oracle-PPT IP)

public import CslibFrontier.Computability.Complexity.Classes.IP.Games.Oracle
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Amplification
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Dynamic-round AM/IP and oracle-PPT IP clients

Non-vacuous clients exercising:
* `AMGame.mergeMerlin` and `AMGame.value_append_arthur_zero` on explicit game shapes,
* `IPPolyRounds_subset_AMPolyRounds` for constant even, constant odd, and parity-varying
  `k(n) = n` round counts,
* `IPQueryBounded_eq_IPk`, `IPQueryBounded_eq_IPk_odd`, `IPQueryBounded_zero`, and
  `IPQueryBounded_eq_AM` for constant-query oracle-PPT verifiers,
* `IPPolyQueryBounded_eq_IPPolyRounds`, `IPPolyQueryBounded_subset_AMPolyRounds`, and
  `IP_subset_AMPolyRounds` on concrete languages and query programs.
-/

public section

namespace CslibFrontierTests.IPPolyOracleRounds

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

/-- Concrete language checking the leading bit, separated on `[true]` and `[false]`. -/
@[expose] def headBitLang : Set (List Bool) :=
  {w : List Bool | w.headD false = true}

/-- `[true]` belongs to `headBitLang` while `[false]` does not. -/
theorem headBitLang_separates : [true] ∈ headBitLang ∧ [false] ∉ headBitLang :=
  ⟨rfl, Bool.false_ne_true⟩

/-- A one-query oracle verifier program sits in query budget `1`. -/
theorem singleQueryProgram_isQueryBounded :
    ProbOracleComp.IsQueryBounded
      ((do
        let y ← ProbOracleComp.query ((), [true])
        pure (y.headD false)) : WordOracleComp Unit Bool) 1 := by
  dsimp only [ProbOracleComp.IsQueryBounded]
  exact (OracleComp.IsCostBounded.bind (ProbOracleComp.IsQueryBounded.query ((), [true]))
    fun _ => .pure _ 0).mono (le_of_eq (Nat.add_zero 1))

private theorem value_matchBit_eq_one :
    AMGame.value true [(.arthur, 1), (.merlin, 1)]
      (fun t => if t.getD 0 false = t.getD 1 false then 1 else 0) = 1 := by
  rw [AMGame.value_arthur]
  have hterm : ∀ r : Fin 1 → Bool, AMGame.value true [(.merlin, 1)]
      (fun t => if (List.ofFn r ++ t).getD 0 false = (List.ofFn r ++ t).getD 1 false
        then (1 : ℚ) else 0) = 1 := fun r => by
    rw [AMGame.value_merlin_true]
    refine le_antisymm (Finset.sup'_le _ _ fun y _ => ?_) ?_
    · simp only [AMGame.value_nil, List.append_nil]
      split_ifs <;> norm_num
    · have hr : (List.ofFn r ++ List.ofFn r).getD 0 false =
          (List.ofFn r ++ List.ofFn r).getD 1 false := by
        simp only [List.ofFn_succ, List.ofFn_zero, Fin.isValue, List.cons_append, List.nil_append,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some]
      refine le_trans ?_ (Finset.le_sup' (f := fun y : Fin 1 → Bool =>
          AMGame.value true [] fun t => if (List.ofFn r ++ (List.ofFn y ++ t)).getD 0 false =
            (List.ofFn r ++ (List.ofFn y ++ t)).getD 1 false then (1 : ℚ) else 0)
        (Finset.mem_univ r))
      simp only [AMGame.value_nil, List.append_nil, hr, reduceIte, le_refl]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, pow_one, nsmul_eq_mul, mul_one]
  norm_num

/-- Merging adjacent Merlin moves collapses `[A 1, M 2, M 3, A 1]` to `[A 1, M 5, A 1]`. -/
example :
    AMGame.mergeMerlin [(.arthur, 1), (.merlin, 2), (.merlin, 3), (.arthur, 1)] =
      [(.arthur, 1), (.merlin, 5), (.arthur, 1)] := rfl

/-- Merging adjacent Merlin moves preserves the Arthur coin count and game value. -/
example :
    AMGame.arthurBits
        (AMGame.mergeMerlin [(.arthur, 1), (.merlin, 1), (.merlin, 1)]) = 1 ∧
      AMGame.value true (AMGame.mergeMerlin [(.arthur, 1), (.merlin, 1), (.merlin, 1)])
          (fun t => if t.getD 0 false = t.getD 1 false then 1 else 0) = 1 :=
  ⟨rfl, by rw [AMGame.value_mergeMerlin]; exact value_matchBit_eq_one⟩

/-- Appending a zero-bit Arthur move preserves `arthurBits` and `AMGame.value true`. -/
example :
    AMGame.arthurBits ([(.arthur, 1), (.merlin, 1)] ++ [(.arthur, 0)]) = 1 ∧
      AMGame.value true ([(.arthur, 1), (.merlin, 1)] ++ [(.arthur, 0)])
          (fun t => if t.getD 0 false = t.getD 1 false then 1 else 0) = 1 :=
  ⟨rfl, by rw [AMGame.value_append_arthur_zero]; exact value_matchBit_eq_one⟩

/-- Dynamic Goldwasser–Sipser instantiated at constant even, constant odd, and `fun n => n`. -/
theorem dynamic_goldwasser_sipser_instantiations {α : Type} (enc : α ↪ List Bool) :
    (IPPolyRounds enc (fun _ => 2) ⊆ AMPolyRounds enc (fun _ => 4)) ∧
      (IPPolyRounds enc (fun _ => 3) ⊆ AMPolyRounds enc (fun _ => 5)) ∧
      (IPPolyRounds enc (fun n => n) ⊆ AMPolyRounds enc (fun n => n + 2)) :=
  ⟨IPPolyRounds_subset_AMPolyRounds _,
    IPPolyRounds_subset_AMPolyRounds _,
    IPPolyRounds_subset_AMPolyRounds _⟩

/-- Oracle-model class equivalences for constant query budgets `q`, `0`, and `q ≥ 1`. -/
theorem oracle_ip_constant_round_instantiations {α : Type} (enc : α ↪ List Bool) (q : ℕ) :
    (IPQueryBounded enc q = IPk enc (2 * q)) ∧
      (IPQueryBounded enc q = IPk enc (2 * q + 1)) ∧
      (IPQueryBounded enc 0 = BPP enc) ∧
      (IPQueryBounded enc (q + 1) = AM enc) :=
  ⟨IPQueryBounded_eq_IPk enc q,
    IPQueryBounded_eq_IPk_odd enc q,
    IPQueryBounded_zero enc,
    IPQueryBounded_eq_AM enc (Nat.succ_pos q)⟩

/-- Dynamic oracle-model equivalence and `IP[2 * (n + 1)] ⊆ AM[2 * (n + 1) + 2]`. -/
theorem oracle_ip_linear_instantiation {α : Type} (enc : α ↪ List Bool) :
    (IPPolyQueryBounded enc (fun n => n + 1) =
        IPPolyRounds enc (fun n => 2 * (n + 1))) ∧
      (IPPolyQueryBounded enc (fun n => n + 1) ⊆
        AMPolyRounds enc (fun n => 2 * (n + 1) + 2)) := by
  have hq : ComputableInPolyTime (fun n => n + 1) encUnary encUnary :=
    ComputableInPolyTime.unary_add' ComputableInPolyTime.id' (ComputableInPolyTime.const 1)
  exact ⟨IPPolyQueryBounded_eq_IPPolyRounds hq, IPPolyQueryBounded_subset_AMPolyRounds hq⟩

private theorem headBitLang_mem_BPP : headBitLang ∈ BPP encBits :=
  P_subset_BPP ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-- `headBitLang` lies in `IPQueryBounded encBits 0` and in `IPQueryBounded encBits 1`. -/
theorem headBitLang_mem_oracle_classes :
    headBitLang ∈ IPQueryBounded encBits 0 ∧
      headBitLang ∈ IPQueryBounded encBits 1 ∧
      headBitLang ∈ IPk encBits 3 := by
  have h0 : headBitLang ∈ IPQueryBounded encBits 0 := by
    rw [IPQueryBounded_zero]
    exact headBitLang_mem_BPP
  have h1 : headBitLang ∈ IPQueryBounded encBits 1 := by
    rw [IPQueryBounded_eq_AM encBits le_rfl]
    exact BPP_subset_AM headBitLang_mem_BPP
  have h3 : headBitLang ∈ IPk encBits 3 := by
    rw [← IPQueryBounded_eq_IPk_odd encBits 1]
    exact h1
  exact ⟨h0, h1, h3⟩

/-- Every `BPP` witness problem like `headBitLang` belongs to `IP` and therefore admits a
polynomial-time round count `k` placing it in `AMPolyRounds`. -/
theorem headBitLang_mem_AMPolyRounds :
    ∃ k : ℕ → ℕ, ComputableInPolyTime k encUnary encUnary ∧
      headBitLang ∈ AMPolyRounds encBits k :=
  IP_subset_AMPolyRounds (BPP_subset_IP encBits headBitLang_mem_BPP)

end CslibFrontierTests.IPPolyOracleRounds

end
