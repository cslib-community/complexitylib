/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.MassProduction.Pipeline
import Mathlib.Algebra.Field.ZMod

/-!
# Scheduled line recovery clients

These clients satisfy every hypothesis of the composition bound at once over the two-element
field: its bits and nonzero scalar, the constant line code, a placement of the prefixes, a
scheduler for one request, a scheduler for two requests that may share a target, and a size
bound for all functions of the suffix. The bound then applies, including to inputs whose two
requests share their prefix. The zero-request case and the closed-form overhead estimate are
checked.
-/

namespace ComplexityTests.MassProduction.Pipeline

open Cslib Cslib.BitString Cslib.LineCode Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.MassProduction Cslib.Circuits.Boolean.MassProduction.Pipeline

/-! ### The two-element field -/

/-- The bit of an element of `ZMod 2`. -/
def bits2 : ZMod 2 ≃+ BitString 1 where
  toFun x _ := decide (x = 1)
  invFun y := if y 0 then 1 else 0
  left_inv := by decide
  right_inv := by decide
  map_add' := by decide

/-- The only nonzero scalar. -/
def scalar2 : Fin 1 ≃ {c : ZMod 2 // c ≠ 0} where
  toFun _ := ⟨1, by decide⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv c := Subtype.ext (by obtain ⟨c, hc⟩ := c; revert c; decide)

-- The field has `s + 1 = 2 ^ b` elements.
example : 1 + 1 = 2 ^ 1 := succ_eq_two_pow bits2 scalar2

/-- Over `ZMod 2` the constant codewords are line-parity codewords on every `ZMod 2 ^ ℓ`: each
punctured line has a single point. -/
def constantCode (ℓ : ℕ) : LineCode (ZMod 2) ℓ where
  info := {0}
  extend data _ := data 0
  extend_eq data u hu := by rw [Finset.mem_singleton.mp hu]
  sum_extend data u v _ := by
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card]
    exact one_smul ℕ _

/-- Each of the two prefixes of one bit gets its own copy of the constant code. -/
def place2 (ℓ : ℕ) : BitString 1 ↪ Fin 2 × (constantCode ℓ).info × Fin 1 where
  toFun a := (if a 0 then 1 else 0, ⟨0, Finset.mem_singleton_self 0⟩, 0)
  inj' a a' h := by
    have h0 : (if a 0 then (1 : Fin 2) else 0) = if a' 0 then 1 else 0 := congrArg Prod.fst h
    funext i
    rw [Subsingleton.elim i 0]
    cases h1 : a 0 <;> cases h2 : a' 0 <;> simp_all

/-- Every function of `w` bits has a circuit of size `2 ^ w * (2 * w + 2) + 1`. -/
theorem complexity_single_le (w : ℕ) (g : BooleanFunction w) :
    complexity interpretation (single g) ≤ 2 ^ w * (2 * w + 2) + 1 :=
  (Synthesis.selected id g).complexity_le

/-! ### Schedulers -/

/-- Some circuit lists every choice of directions: a scheduler exists whenever every tuple of
targets has nonzero directions with pairwise disjoint punctured lines. -/
theorem exists_isScheduler {K : Type*} [Field K] [Fintype K] [DecidableEq K] {ℓ b s t : ℕ}
    (bits : K ≃+ BitString b) (scalar : Fin s ≃ {c : K // c ≠ 0})
    (h : ∀ targets : Fin t → Fin ℓ → K, ∃ directions : Fin t → Fin ℓ → K,
      (∀ i, directions i ≠ 0) ∧ ∀ i j, i ≠ j →
        Disjoint (puncturedLine (targets i) (directions i))
          (puncturedLine (targets j) (directions j))) :
    ∃ sched : Circuit signature (t * (ℓ * b)) (t * (s * (ℓ * b))),
      IsScheduler bits scalar sched := by
  choose directions hdirections using h
  let decode : BitString (t * (ℓ * b)) → Fin t → Fin ℓ → K :=
    fun y i => (pointEquiv bits.toEquiv).symm fun k => y (finProdFinEquiv (i, k))
  have hdecode (targets : Fin t → Fin ℓ → K) : decode (targetBits bits targets) = targets := by
    funext i
    apply (pointEquiv bits.toEquiv).symm_apply_eq.mpr
    funext k
    simp only [targetBits, blocksEquiv_symm_apply, Function.comp_apply, Equiv.symm_apply_apply,
      pointEquiv_apply]
    rfl
  obtain ⟨sched, hsched⟩ := Interpretation.IsComplete.exists_computes (I := interpretation)
    fun y => lineBits bits (fun j => (scalar j : K)) (decode y) (directions (decode y))
  refine ⟨sched, fun targets => ⟨directions targets, (hdirections targets).1,
    (hdirections targets).2, ?_⟩⟩
  rw [hsched]
  dsimp only
  rw [hdecode]

-- One request on the line `ZMod 2`: the direction `1` always works.
example : ∃ sched : Circuit signature (1 * (1 * 1)) (1 * (1 * (1 * 1))),
    IsScheduler bits2 scalar2 sched :=
  exists_isScheduler bits2 scalar2 fun _ =>
    ⟨fun _ _ => 1, fun _ => Function.ne_iff.mpr ⟨0, one_ne_zero⟩,
      fun i j h => absurd (Subsingleton.elim i j) h⟩

/-- Two requests on the plane `ZMod 2 ^ 2`, which may share their target, always have nonzero
directions with disjoint punctured lines. -/
theorem exists_directions_two : ∀ targets : Fin 2 → Fin 2 → ZMod 2,
    ∃ directions : Fin 2 → Fin 2 → ZMod 2, (∀ i, directions i ≠ 0) ∧ ∀ i j, i ≠ j →
      Disjoint (puncturedLine (targets i) (directions i))
        (puncturedLine (targets j) (directions j)) := by
  decide

/-! ### The composition bound -/

/-- **All hypotheses at once.** For two requests with one prefix bit and one suffix bit, packed
into two copies of the constant code on `ZMod 2 ^ 2`, some scheduler satisfies the composition
bound. -/
theorem exists_bound_two :
    ∃ sched : Circuit signature (2 * (2 * 1)) (2 * (1 * (2 * 1))),
      IsScheduler bits2 scalar2 sched ∧ ∀ f : BooleanFunction (1 + 1),
        complexity interpretation (directProduct f 2) ≤
          sched.size + 2 * Fintype.card (ZMod 2) ^ 2 * 1 * 9 + pipelineOverhead 2 1 1 2 1 1 2 := by
  obtain ⟨sched, hsched⟩ := exists_isScheduler bits2 scalar2 exists_directions_two
  exact ⟨sched, hsched, complexity_directProduct_le_of_isScheduler bits2 scalar2
    (constantCode 2) (place2 2) sched hsched (complexity_single_le 1)⟩

/-- Repeated prefixes: when both requests read the prefix `true`, the recovery circuit still
returns `f` on each request. -/
theorem lineSums_eval_recoveryCircuit_repeated (f : BooleanFunction (1 + 1)) :
    ∃ sched : Circuit signature (2 * (2 * 1)) (2 * (1 * (2 * 1))),
      IsScheduler bits2 scalar2 sched ∧
      ∃ members : Fin (2 * 2 ^ (2 * 1)) → Fin 1 → Circuit signature 1 1,
        ∀ z₁ z₂ : Bool,
          lineSums 2 1 ((recoveryCircuit bits2 (constantCode 2) (place2 2) sched members).eval
            interpretation ![true, z₁, true, z₂]) = ![f ![true, z₁], f ![true, z₂]] := by
  obtain ⟨sched, hsched⟩ := exists_isScheduler bits2 scalar2 exists_directions_two
  choose members hmembers using fun q r => Interpretation.IsComplete.exists_computes
    (I := interpretation) (single (slotResource bits2 (constantCode 2) (place2 2) f q r))
  refine ⟨sched, hsched, members, fun z₁ z₂ => ?_⟩
  rw [lineSums_eval_recoveryCircuit scalar2 hsched hmembers]
  funext i
  fin_cases i <;> exact congrArg f (funext fun k => by fin_cases k <;> rfl)

/-! ### Boundary cases -/

-- Zero requests: every circuit with no inputs and no outputs is a scheduler.
example (sched : Circuit signature (0 * (2 * 1)) (0 * (1 * (2 * 1)))) :
    IsScheduler bits2 scalar2 sched :=
  fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, funext fun i => i.elim0⟩

-- The explicit bound at zero requests.
example (f : BooleanFunction (1 + 1))
    (sched : Circuit signature (0 * (2 * 1)) (0 * (1 * (2 * 1)))) :
    complexity interpretation (directProduct f 0) ≤
      sched.size + 2 * Fintype.card (ZMod 2) ^ 2 * 1 * 9 +
        1444 * (2 ^ 1 + 0 * Fintype.card (ZMod 2) + 2 * Fintype.card (ZMod 2) ^ 2) *
          (1 + 1 + 2 * 1 + Nat.log 2 (0 + 2) + 2) ^ 4 :=
  complexity_directProduct_le_explicit_of_isScheduler bits2 scalar2 (constantCode 2) (place2 2)
    sched (fun _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      funext fun i => i.elim0⟩) (complexity_single_le 1) f

-- The closed-form estimate at the two-request instance.
example : pipelineOverhead 2 1 1 2 1 1 2 ≤
    1444 * (2 ^ 1 + 2 * (1 + 1) + 2 * (1 + 1) ^ 2) * (1 + 1 + 2 * 1 + Nat.log 2 (2 + 2) + 2) ^ 4 :=
  pipelineOverhead_le rfl (by decide)

end ComplexityTests.MassProduction.Pipeline
