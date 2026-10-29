/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Hierarchy
import Complexity.Computability.Complexity.Classes.Oracle.BakerGillSolovay
import Complexity.Computability.Complexity.Classes.Oracle.Collapse
import Complexity.Computability.Complexity.Classes.Oracle.Monotone

/-! Requests of adaptive word-query programs under language oracles, locality, membership in the
oracle classes, the unary length language, candidate deciders, the diagonal oracle, the
Baker–Gill–Solovay separation, oracles in polynomial space, the words of `TQBF`, the collapse and
oracle monotonicity. -/

namespace ComplexityTests.Relativization

open Cslib Cslib.Complexity Cslib.Logic.PL Turing Turing.MultiTapeTM

/-! ### Adaptive requests -/

/-- Ask `[true]`; on a positive answer, also ask `[false]`. -/
def adaptive : WordQueryComp Unit Bool := do
  let reply ← OracleComp.query ((), [true])
  if reply = [true] then
    let second ← OracleComp.query ((), [false])
    return second = [true]
  else
    return false

/-- An oracle containing `[true]` receives the second request. -/
example : OracleComp.queriesWith (languageOracle {[true]}) adaptive =
    [((), [true]), ((), [false])] := by
  simp [adaptive, languageOracle_apply]

/-- The empty oracle does not. -/
example : OracleComp.queriesWith (languageOracle ∅) adaptive = [((), [true])] := by
  simp [adaptive, languageOracle_apply]

/-- The answer is whether both words are in the oracle. -/
example : OracleComp.interpret (m := Id) (languageOracle {[true], [false]}) adaptive = true := by
  simp only [adaptive, OracleComp.interpret_id_query_bind, languageOracle_apply, Set.mem_insert_iff,
    Set.mem_singleton_iff, true_or, or_true, decide_true, ↓reduceIte]
  rfl

example : OracleComp.interpret (m := Id) (languageOracle {[true]}) adaptive = false := by
  simp only [adaptive, OracleComp.interpret_id_query_bind, languageOracle_apply,
    Set.mem_singleton_iff, decide_true, ↓reduceIte, List.cons.injEq, Bool.false_eq_true, and_true,
    decide_false]
  rfl

/-- Locality: words that are never requested do not matter. -/
example (A : Set (List Bool)) (hA : [true] ∉ A) :
    OracleComp.interpret (m := Id) (languageOracle A) adaptive =
      OracleComp.interpret (m := Id) (languageOracle ∅) adaptive :=
  (interpret_languageOracle_congr adaptive fun q hq => by
    simp only [adaptive, OracleComp.queriesWith_query_bind, languageOracle_apply,
      Set.mem_empty_iff_false, decide_false] at hq
    simp only [List.cons.injEq, Bool.false_eq_true, and_true, ite_false,
      OracleComp.queriesWith_pure, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    simpa using hA).1

/-! ### The oracle classes -/

/-- `P` problems and deterministic polynomial-time computations lift to every oracle, while
`A` and reductions to `A` belong to `P^A` and `NP^A`. -/
example (A : Set (List Bool)) :
    (Set.univ : Set (List Bool)) ∈ PWithOracle A encBits ∧
    ComputableInPolyTimeWithOracle A (fun _ : List Bool => false) encBits encBool ∧
    ComputableInPolyTimeWithOracle A (fun x : List Bool => x.reverse) encBits encBits ∧
    A ∈ NPWithOracle A encBits ∧
    {w : List Bool | w.reverse ∈ A} ∈ PWithOracle A encBits :=
  ⟨P_subset_PWithOracle A encBits ⟨fun _ => true, ComputableInPolyTime.const true,
     fun _ => by simp⟩,
   (ComputableInPolyTime.const false).computableInPolyTimeWithOracle A,
   by fun_prop,
   PWithOracle_subset_NPWithOracle A encBits (mem_PWithOracle_self A),
   PolyTimeReducible.mem_PWithOracle ⟨List.reverse, by fun_prop, fun _ => Iff.rfl⟩
     (mem_PWithOracle_self A)⟩

/-- The oracle adds power: the time-hierarchy diagonal language is not in `P`, but it is in `P`
relative to itself. -/
example : ∃ A : Set (List Bool), A ∈ PWithOracle A encBits ∧ A ∉ P encBits :=
  ⟨_, mem_PWithOracle_self _, diagonal_notMem_P⟩

/-! ### The unary length language -/

example :
    [true, true] ∈ unaryLengthLanguage {[false, true]} ∧
    [] ∈ unaryLengthLanguage {[]} ∧
    [] ∉ unaryLengthLanguage ∅ :=
  ⟨replicate_mem_unaryLengthLanguage.mpr ⟨[false, true], rfl, rfl⟩,
   replicate_mem_unaryLengthLanguage (n := 0).mpr ⟨[], rfl, rfl⟩,
   fun h => by simpa using h.2⟩

/-- Words containing `false` are never in the unary length language. -/
example (B : Set (List Bool)) : [true, false] ∉ unaryLengthLanguage B := fun h => by
  simpa using h.1

example : [true] ∉ unaryLengthLanguage {[], [true, true]} := fun h => by
  obtain ⟨-, w, hw, hlen⟩ := h
  rcases hw with rfl | rfl <;> simp at hlen

/-! ### Candidate deciders -/

open BakerGillSolovay in
/-- A candidate with a machine that halts at once and a zero clock: its verdict makes no request
and rejects, against every oracle. -/
example (A : Set (List Bool)) (n : ℕ) :
    OracleComp.queriesWith (languageOracle A)
      (Candidate.verdict ⟨0, 1, ⟨0, fun _ _ _ _ _ => .step ⟨0, fun i => i.elim0, none, none⟩
        (fun _ => none) (fun _ => 0)⟩, 0, 0⟩ n) = [] ∧
    OracleComp.interpret (m := Id) (languageOracle A)
      (Candidate.verdict ⟨0, 1, ⟨0, fun _ _ _ _ _ => .step ⟨0, fun i => i.elim0, none, none⟩
        (fun _ => none) (fun _ => 0)⟩, 0, 0⟩ n) = false := by
  constructor <;> rfl

/-- `NP` relative to an oracle is closed under reductions: prepending `true` reduces to the unary
language. -/
example (B : Set (List Bool)) :
    {x : List Bool | true :: x ∈ unaryLengthLanguage B} ∈ NPWithOracle B encBits :=
  PolyTimeReducible.mem_NPWithOracle ⟨List.cons true, by fun_prop, fun _ => Iff.rfl⟩
    (unaryLengthLanguage_mem_NPWithOracle B)

/-! ### The diagonal oracle -/

/-- At length `n`, ask whether `0ⁿ` is in the oracle. -/
def zeros (n : ℕ) : WordQueryComp Unit Bool :=
  (fun reply => decide (reply = [true])) <$> OracleComp.query ((), List.replicate n false)

/-- One request per length is fewer than `2 ^ n` from `n = 1` on, so some oracle defeats `zeros`
on the question whether it has a word of length `n`. -/
example : ∃ B : Set (List Bool), ∃ n, ¬(OracleComp.interpret (m := Id) (languageOracle B)
    (zeros n) = true ↔ ∃ w ∈ B, w.length = n) := by
  obtain ⟨B, hB⟩ := exists_oracle_diagonal (ι := Unit) (fun _ => zeros) (fun _ _ => 1)
    (fun _ => Filter.eventually_atTop.mpr ⟨1, fun n hn => Nat.one_lt_two_pow (by omega)⟩)
    (fun _ n A => by simp [zeros])
  exact ⟨B, hB ()⟩

/-! ### Oracles in polynomial space and the collapse -/

/-- An oracle in `PSPACE`: the empty language. `P` relative to it is within `PSPACE`. -/
example : {w : List Bool | w.reverse ∈ (∅ : Set (List Bool))} ∈ PSPACE encBits :=
  PWithOracle_subset_PSPACE
    (P_subset_PSPACE ⟨fun _ => false, ComputableInPolyTime.const false, fun _ => by simp⟩)
    (PolyTimeReducible.mem_PWithOracle ⟨List.reverse, by fun_prop, fun _ => Iff.rfl⟩
      (mem_PWithOracle_self ∅))

/-- A token list with an unexpected token, one with a missing operand, and one whose constant
carries a variable are not well formed; a negated constant and a quantified variable are. -/
example : TQBF.wellFormed [(.not, 0), (.top, 0)] = true ∧
    TQBF.wellFormed [(.ex, 3), (.var, 3)] = true ∧
    TQBF.wellFormed [(.top, 0), (.top, 0)] = false ∧
    TQBF.wellFormed [(.and, 0), (.top, 0)] = false ∧
    TQBF.wellFormed [(.top, 1)] = false := by
  decide

/-- An encoded formula is a code; a word shorter than every encoded formula is not. -/
example : TQBF.isCode (encQBF .top) = true := (TQBF.isCode_iff _).mpr ⟨_, rfl⟩

example : TQBF.isCode [true, true] = false := by
  rw [Bool.eq_false_iff, ne_eq, TQBF.isCode_iff]
  rintro ⟨φ, hφ⟩
  have h₁ := three_mul_length_tokens_le φ
  have h₂ := List.length_pos_of_ne_nil (QBF.tokens_ne_nil φ)
  rw [hφ] at h₁
  simp only [List.length_cons, List.length_nil] at h₁
  omega

/-- The `TQBF` oracle is nontrivial (containing `encQBF .top` and omitting `encQBF .bot`),
collapses `NP` to `P` relative to `encQBF '' TQBF`, and places `TQBF` in `P` relative to it. -/
example :
    (encQBF .top ∈ encQBF '' TQBF ∧ encQBF .bot ∉ encQBF '' TQBF) ∧
    encQBF '' TQBF ∈ NPWithOracle (encQBF '' TQBF) encBits ∧
    TQBF ∈ PWithOracle (encQBF '' TQBF) encQBF :=
  ⟨⟨⟨_, top_mem_TQBF, rfl⟩, fun h => bot_notMem_TQBF (encQBF.injective.mem_set_image.mp h)⟩,
   PWithOracle_image_TQBF_eq_NPWithOracle encBits ▸ mem_PWithOracle_self _,
   PSPACE_subset_PWithOracle image_TQBF_pspaceHard encQBF TQBF_mem_PSPACE⟩

/-- The theorem of Baker, Gill and Solovay: the oracles of the collapse and of the separation. -/
example : (∃ A : Set (List Bool), unaryLengthLanguage A ∈ PWithOracle A encBits) ∧
    ∃ B : Set (List Bool), PWithOracle B encBits ≠ NPWithOracle B encBits := by
  obtain ⟨⟨A, hA⟩, hB⟩ := baker_gill_solovay
  exact ⟨⟨A, hA ▸ unaryLengthLanguage_mem_NPWithOracle A⟩, hB⟩

/-! ### Oracle monotonicity -/

/-- Monotonicity for `P` and `NP` along reversal: `B` and `unaryLengthLanguage B` lie in `P` and
`NP` relative to `{w | w.reverse ∈ B}`. -/
example (B : Set (List Bool)) :
    B ∈ PWithOracle {w | w.reverse ∈ B} encBits ∧
    unaryLengthLanguage B ∈ NPWithOracle {w | w.reverse ∈ B} encBits :=
  have hrev : PolyTimeReducible encBits encBits B {w | w.reverse ∈ B} :=
    ⟨List.reverse, by fun_prop, fun w => by simp⟩
  ⟨hrev.PWithOracle_subset encBits (mem_PWithOracle_self B),
   hrev.NPWithOracle_subset encBits (unaryLengthLanguage_mem_NPWithOracle B)⟩

/-! ### Axioms -/

/-- info: 'Cslib.OracleComp.interpret_id_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.OracleComp.interpret_id_congr

end ComplexityTests.Relativization
