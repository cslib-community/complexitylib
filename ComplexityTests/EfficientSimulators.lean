/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.SchnorrProtocol
import Complexity.Crypto.Computational.DiscreteLog.SchnorrGroup
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF.Bind
import ComplexityTests.UnboundedSimulators

/-!
# Efficient special soundness and special HVZK

Checks of `SigmaProtocol.EfficientSpecialSoundness` and `SigmaProtocol.EfficientSpecialHVZK` on
both sides.

* **Schnorr** satisfies both. The extractor computes `(c - c')⁻¹ (z - z')` with `extractNat`
  (evaluated here on concrete numbers), and the strict PPT simulator outputs an accepting
  conversation with probability at least `1 - 1 / 2 ^ n`, here in Schnorr groups.
* **The efficient notions are strictly stronger, under the discrete-logarithm assumption.** For
  discrete logarithms with witnesses in `ZMod q`, every statement has exactly one witness, so the
  unbounded notions hold for protocols that reveal or ignore the witness
  (`ComplexityTests/UnboundedSimulators.lean`): `sendWitnessSigma` is special HVZK and
  `trustMeSigma` is special sound (`specialHVZK_sendWitness`, `exists_specialSoundness_trustMe`).
  An efficient simulator for the first, or an efficient extractor for the second, would be a
  strict PPT algorithm computing discrete logarithms. So under `PrimeOrderGroupFamily.DiscreteLog`
  neither is efficient, for any simulator error at most `1/2`
  (`not_efficientSpecialHVZK_sendWitness`, `not_efficientSpecialSoundness_trustMe`).
-/

namespace ComplexityTests.EfficientSimulators

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol
  Cslib.Interactive Probability Turing.MultiTapeTM ComplexityTests.UnboundedSimulators.Sigma
open scoped ENNReal NNReal

/-! ### Schnorr -/

/-- `extractNat` inverts by Fermat's little theorem: modulo `7`, `(3 - 1)⁻¹ (5 - 2) = 4 · 3 = 5`. -/
example : PrimeOrderGroupFamily.extractNat 7 3 5 1 2 = 5 := by decide

/-- The strict PPT Schnorr simulator for Schnorr groups outputs an accepting conversation with
probability at least `1 - 1 / 2 ^ n`, for every statement and challenge. -/
example (n : ℕ) (d : schnorrGroups.Desc) (u : schnorrGroups.Carrier d)
    (c : ZMod (schnorrGroups.order d)) :
    1 - 1 / 2 ^ n ≤ (ProbComp.eval (schnorrGroups.schnorrSimulateWord
      ((n, d), schnorrGroups.encode d u, encNat c.val))).toOuterMeasure
      {w | ∃ t z, w = (schnorrGroups.encode d t, encNat (ZMod.val z)) ∧
        (schnorrGroups.schnorrFamily (n, d)).Accepts u t c z} :=
  schnorrGroups.simulatorRealizedBy_schnorrSimulateWord.one_sub_le_accepts
    schnorrGroups.efficientSpecialHVZK_schnorr.specialHVZK (n, d) u c

/-! ### Discrete logarithms -/

variable {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}

/-- The discrete-logarithm relation in the group of the description `i.2`, with witnesses in
`ZMod q`: every statement has exactly one witness. -/
abbrev dlRel (F : PrimeOrderGroupFamily) (i : ℕ × F.Desc) (α : ZMod (F.order i.2))
    (u : F.Carrier i.2) : Prop :=
  α • F.generator i.2 = u

theorem dlRel_total (i : ℕ × F.Desc) (u : F.Carrier i.2) : ∃ α, dlRel F i α u :=
  F.smul_generator_surjective i.2 u

theorem dlRel_unique (i : ℕ × F.Desc) {α α' : ZMod (F.order i.2)} {u : F.Carrier i.2}
    (h : dlRel F i α u) (h' : dlRel F i α' u) : α = α' :=
  F.smul_generator_injective i.2 (h.trans h'.symm)

/-- Under the discrete-logarithm assumption, no uniform strict PPT adversary finds the discrete
logarithm with probability at least `1/2` on every instance. -/
theorem not_half_le_discreteLog (hDL : F.DiscreteLog setup)
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair F.encDesc encBits)) encBits
      fun input => adversary input.1 input.2)
    (h : ∀ n d (α : ZMod (F.order d)), 1 / 2 ≤
      (ProbComp.eval (adversary n (d, F.encode d (α • F.generator d)))).toOuterMeasure
        {w | (ofBits w : ZMod (F.order d)) = α}) : False := by
  have hgame (n : ℕ) : (1 / 2 : ℝ≥0∞) ≤ F.discreteLogGame setup adversary n true := by
    simp only [PrimeOrderGroupFamily.discreteLogGame, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure]
    refine PMF.le_bind_apply_on_support _ fun d _ => PMF.le_bind_apply_on_support _ fun α _ => ?_
    rw [show ∀ (p : PMF (List Bool)) (f : List Bool → Bool),
        p.bind (fun guess => PMF.pure (f guess)) = p.map f from fun p f => PMF.bind_pure_comp f p,
      ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    refine le_trans (h n d α) (le_of_eq (congrArg _ ?_))
    ext w
    simp
  refine not_negligible_const (c := 1 / 2) (by norm_num) (negligible_of_le (hDL _ hA) fun n => ?_)
  rw [Game.succProbability, ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  simpa using hgame n

/-! ### Sending the witness is special HVZK, but not efficiently -/

/-- The protocol that sends the witness, for discrete logarithms. -/
noncomputable abbrev sendWitnessFamily (F : PrimeOrderGroupFamily) (i : ℕ × F.Desc) :=
  sendWitnessSigma (dlRel F i)

/-- Its word encodings: scalars in binary, group elements by the family's encoding and challenges
as single bits. -/
def sendWitnessEncoding (F : PrimeOrderGroupFamily) :
    Encoding (ℕ × F.Desc) (fun i => F.Carrier i.2) (fun i => ZMod (F.order i.2)) (fun _ => Bool)
      (fun i => ZMod (F.order i.2)) where
  index := encPair encUnary F.encDesc
  statement i := F.encodeEmbedding i.2
  commitment i := F.encScalar i.2
  challenge _ := encBool
  response i := F.encScalar i.2

/-- Sending the witness is special HVZK at every index, with an unbounded simulator. -/
theorem specialHVZK_sendWitness (i : ℕ × F.Desc) :
    (sendWitnessFamily F i).SpecialHVZK (dlRel F i)
      (choiceSimulate (sendWitnessFamily F i) (dlRel F i)) :=
  sendWitnessSigma_specialHVZK _ (dlRel_total i) fun _ _ _ h h' => dlRel_unique i h h'

/-- **Sending the witness is not efficiently special HVZK** under the discrete-logarithm
assumption, with any simulator and any error at most `1/2`: the simulator's commitment is the
discrete logarithm of its statement. -/
theorem not_efficientSpecialHVZK_sendWitness (hDL : F.DiscreteLog setup)
    (simulate : ∀ i : ℕ × F.Desc, F.Carrier i.2 → Bool → PMF (ZMod (F.order i.2) ×
      ZMod (F.order i.2)))
    {δ : ℕ × F.Desc → ℝ≥0∞} (hδ : ∀ i, δ i ≤ 1 / 2) :
    ¬ EfficientSpecialHVZK (sendWitnessFamily F) (dlRel F) (sendWitnessEncoding F) simulate δ := by
  intro h
  obtain ⟨program, hppt, hreal⟩ := h.realized
  refine not_half_le_discreteLog hDL
    (adversary := fun n input => Prod.fst <$> program ((n, input.1), input.2, encBool true))
    ((hppt.preprocess (prepare := fun input : ℕ × F.Desc × List Bool =>
      ((input.1, input.2.1), input.2.2, encBool true)) (by fun_prop)).map
        (ComputableInPolyTime.fst _ _)) fun n d α => ?_
  have hacc := hreal.one_sub_le_accepts h.specialHVZK (n, d) (α • F.generator d) true
  calc (1 / 2 : ℝ≥0∞) = 1 - 1 / 2 := by rw [one_div, ENNReal.one_sub_inv_two]
    _ ≤ 1 - δ (n, d) := tsub_le_tsub_left (hδ _) 1
    _ ≤ _ := hacc
    _ ≤ _ := by
      rw [ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
      refine MeasureTheory.measure_mono ?_
      rintro _ ⟨t, z, rfl, ht⟩
      have hα : t = α := dlRel_unique (n, d) (of_decide_eq_true ht) rfl
      change ((ofBits (encNat t.val) : ℕ) : ZMod (F.order d)) = α
      rw [encNat_apply, ofBits, Nat.foldr_bit_bits, ZMod.natCast_zmod_val, hα]

/-! ### Accepting everything is special sound, but not efficiently -/

/-- The protocol whose verifier accepts every conversation, for discrete logarithms. -/
noncomputable abbrev trustMeFamily (F : PrimeOrderGroupFamily) (i : ℕ × F.Desc) :=
  trustMeSigma (ZMod (F.order i.2)) (F.Carrier i.2)

/-- Its word encodings: trivial commitments and responses, and challenges as single bits. -/
def trustMeEncoding (F : PrimeOrderGroupFamily) :
    Encoding (ℕ × F.Desc) (fun i => F.Carrier i.2) (fun _ => Unit) (fun _ => Bool)
      (fun _ => Unit) where
  index := encPair encUnary F.encDesc
  statement i := F.encodeEmbedding i.2
  commitment _ := encUnit
  challenge _ := encBool
  response _ := encUnit

/-- Accepting everything is special sound at every index, with an unbounded extractor. -/
theorem exists_specialSoundness_trustMe (i : ℕ × F.Desc) :
    ∃ extract, (trustMeFamily F i).SpecialSoundness (dlRel F i) extract :=
  (exists_specialSoundness_iff _ _).2 fun u _ _ _ _ _ _ _ _ => dlRel_total i u

/-- **Accepting everything is not efficiently special sound** under the discrete-logarithm
assumption, with any extractor: from two trivial conversations it would compute discrete
logarithms. -/
theorem not_efficientSpecialSoundness_trustMe (hDL : F.DiscreteLog setup)
    (extract : ∀ i : ℕ × F.Desc, F.Carrier i.2 → Unit → Bool → Unit → Bool → Unit →
      ZMod (F.order i.2)) :
    ¬ EfficientSpecialSoundness (trustMeFamily F) (dlRel F) (trustMeEncoding F)
      (fun i => F.encScalar i.2) extract := by
  intro h
  obtain ⟨f, hf, hreal⟩ := h.polyTime
  let prepare : ℕ × F.Desc × List Bool →
      (ℕ × F.Desc) × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool :=
    fun input => ((input.1, input.2.1), input.2.2, encUnit (), encBool true, encUnit (),
      encBool false, encUnit ())
  refine not_half_le_discreteLog hDL (adversary := fun n input => pure (f (prepare (n, input))))
    (hf.comp (show ComputableInPolyTime prepare _ _ by fun_prop)).isPPTOn fun n d α => ?_
  have hword := hreal (n, d) (α • F.generator d) () true () false ()
  have hα : extract (n, d) (α • F.generator d) () true () false () = α :=
    dlRel_unique (n, d) (h.specialSoundness (n, d) _ () true () false () (by decide) rfl rfl) rfl
  have hmem : f (prepare (n, d, F.encode d (α • F.generator d))) ∈
      {w : List Bool | (ofBits w : ZMod (F.order d)) = α} := by
    change ((ofBits (f (prepare (n, d, F.encode d (α • F.generator d)))) : ℕ) :
      ZMod (F.order d)) = α
    rw [show f (prepare (n, d, F.encode d (α • F.generator d))) =
      F.encScalar d (extract (n, d) (α • F.generator d) () true () false ()) from hword, hα]
    change ((ofBits (encNat α.val) : ℕ) : ZMod (F.order d)) = α
    rw [encNat_apply, ofBits, Nat.foldr_bit_bits, ZMod.natCast_zmod_val]
  rw [ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply]
  simp [hmem]

end ComplexityTests.EfficientSimulators
