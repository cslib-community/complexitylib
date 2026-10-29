/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BPP
import Complexity.Crypto.Computational.OneWay.BPP
import Complexity.Crypto.Computational.OneWay.MCSP
import Complexity.Crypto.Computational.OneWay.NP

/-! One-way functions against structural hypotheses: the preimage-prefix problem, the
search-to-decision inverter, `OWF ⇒ P ≠ NP` and `OWF ⇒ NP ⊄ BPP`; the truth-table distinguisher
and Kabanets–Cai.
The hypotheses of the inverter and distinguisher lemmas are discharged for concrete functions and
deciders; one-wayness and `MCSP ∈ BPP` are open and are not instantiated. -/

namespace ComplexityTests.OneWayMetacomplexity

open Turing.MultiTapeTM Cslib Cslib.Crypto Cslib.Complexity

-- The preimage-prefix problem of a concrete polynomial-time function is in `NP`.
example : preimagePrefix (fun x => x ++ x) ∈ NP encPreimagePrefix :=
  preimagePrefix_mem_NP (by fun_prop)

-- The search hypothesis is satisfiable: with an exact (classical) decision procedure, the search
-- recovers the input of an injective function.
open Classical in
example (x : List Bool) :
    preimageSearch (fun p => decide (p ∈ preimagePrefix List.reverse)) (x.length, x.reverse) =
      x := by
  simpa using apply_preimageSearch (f := List.reverse)
    (D := fun p => decide (p ∈ preimagePrefix List.reverse)) (fun _ => decide_eq_true_iff.symm) x

-- The search runs on a concrete instance with a decision procedure that is correct for the
-- identity: a prefix extends to a preimage of `y` of length `n` exactly when it is a prefix of
-- `y` and `y` has length `n`.
example : preimageSearch (fun p => decide (p.2.2 <+: p.2.1 ∧ p.2.1.length = p.1))
    (3, [true, false, true]) = [true, false, true] := by decide

-- The inverter lemma applies: the identity is not one-way, by its own inverse.
example : ¬ OneWay id :=
  not_oneWay_of_lengthInverse Prod.snd (ComputableInPolyTime.snd _ _) fun _ => rfl

/-- The preimage-prefix problem of a constant function is in `P`: an image has a preimage of
length `n` with a given prefix exactly when it is the constant and the prefix is short enough. -/
theorem preimagePrefix_const_mem_P :
    preimagePrefix (fun _ => ([] : List Bool)) ∈ P encPreimagePrefix := by
  refine ⟨fun p => p.2.1.isEmpty && decide (p.2.2.length ≤ p.1), by fun_prop,
    fun ⟨n, y, u⟩ => ⟨fun ⟨x, hx, hux, hy⟩ => ?_, fun h => ?_⟩⟩
  · subst hy
    have hle : u.length ≤ n := (hux.length_le).trans_eq hx
    simpa using hle
  · simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at h
    obtain ⟨rfl, hu⟩ := h
    refine ⟨u ++ List.replicate (n - u.length) false, ?_, List.prefix_append _ _, rfl⟩
    simp only [List.length_append, List.length_replicate]
    omega

-- The randomized inverter applies once the preimage-prefix problem is in `BPP`.
example : ∃ inverter : Inverter, Probability.IsPPT encBits inverter ∧
    ∀ n, 1 / 2 ≤ Game.succProbability
      (ProbComp.eval (inversionGame (fun _ => ([] : List Bool)) inverter n)) :=
  exists_inverter_of_preimagePrefix_mem_BPP (P_subset_BPP preimagePrefix_const_mem_P)

-- Closure of `BPP` under reductions applies to a concrete reduction into a problem in `BPP`.
example : {b : Bool | b = true} ∈ BPP encBool :=
  PolyTimeReducible.mem_BPP
    ⟨fun b => if b then (0, [], []) else (0, [true], []), ComputableInPolyTime.of_finite _,
      fun b => by cases b <;> simp [preimagePrefix]⟩
    (P_subset_BPP preimagePrefix_const_mem_P)

-- Against a deterministic oracle, `queryTable` collects the first reply bits, `false` for an
-- empty reply.
example : OracleComp.interpret (ProbOracleComp.handler ProbComp.unifFin
    fun request => pure (List.reverse request.2))
      (KabanetsCai.queryTable [[true, false], [], [false, true]]) = pure [false, false, true] := by
  rw [KabanetsCai.interpret_queryTable]
  rfl

-- The circuit bound applies to a concrete polynomial-time keyed family.
example : ∃ c : ℕ, ∀ (key : List Bool) (m : ℕ), m ≤ key.length →
    Circuits.complexity Circuits.Boolean.interpretation
      (Circuits.single (KabanetsCai.restriction (fun query => key ++ query) key.length m)) ≤
        c * (3 * key.length + 2) ^ c + 2 :=
  KabanetsCai.exists_complexity_restriction_le (family := fun key query => key ++ query)
    (by fun_prop)

-- Restricting a uniformly random `BitString 3 → BitString 3` table gives the all-false
-- `BooleanFunction 2` with probability `1 / 16`.
example :
    ((Probability.PMF.uniformOfFintype (BitString 3 → BitString 3)).map
      (KabanetsCai.restrictTable 3 2 (by norm_num))) (fun _ => false) = 1 / 16 := by
  rw [KabanetsCai.uniformOfFintype_map_restrictTable _ (by norm_num)]
  simp [Probability.PMF.uniformOfFintype_apply]

-- The distinguisher certificate applies to a concrete polynomial-time decider.
example : Probability.IsOraclePPT Turing.MultiTapeTM.encBool
    (KabanetsCai.mcspDistinguisher 0 (fun x => x.2.isEmpty) 3) :=
  KabanetsCai.isOraclePPT_mcspDistinguisher 3 (by fun_prop)

end ComplexityTests.OneWayMetacomplexity
