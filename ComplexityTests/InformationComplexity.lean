/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.Information

/-!
Regression clients for information cost: Alice announcing her bit costs nothing internally on
perfectly correlated inputs but one bit externally (so `internalInfoCost ≤ externalInfoCost` can
be strict), the two costs agree on independent inputs, both are at most the depth, and the
information complexity of a relation solved by a protocol that reveals nothing new is `0`.
-/

open Cslib Cslib.Communication Cslib.Probability Cslib.Probability.PMF

namespace InformationComplexityTests

/-- Alice announces her bit. -/
def announce : Protocol Bool Bool Bool := .alice id (.output false) (.output true)

/-- Inputs `(b, b)` for a uniformly random bit `b`. -/
noncomputable def diag : PMF (Bool × Bool) := (PMF.uniformOfFintype Bool).map fun b => (b, b)

/-- Independent uniformly random bits. -/
noncomputable def indep : PMF (Bool × Bool) :=
  (PMF.uniformOfFintype Bool).bind fun a => (PMF.uniformOfFintype Bool).map (a, ·)

theorem announce_leaf_injective : Function.Injective fun b : Bool => announce.leaf b b := by
  decide

theorem announce_solves : announce.Solves (fun x _ z => z = x) Set.univ Set.univ := by
  intro x _ y _
  cases x <;> rfl

theorem diag_fst_eq_snd : ∀ q ∈ diag.support, q.1 = q.2 := by
  intro q hq
  obtain ⟨b, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hq
  rfl

/-- On perfectly correlated inputs, announcing Alice's bit reveals nothing new to either
player. -/
theorem internalInfoCost_announce_diag : internalInfoCost (announce.transcriptLaw diag) = 0 := by
  rw [Protocol.transcriptLaw_eq, internalInfoCost_map,
    condMutualInfo_map_eq_zero_of_determined diag (fun q => q.2) (fun q => q.1)
      (fun q => announce.leaf q.1 q.2) (fun y => announce.leaf y y)
      (fun q hq => by rw [diag_fst_eq_snd q hq]),
    condMutualInfo_map_eq_zero_of_determined diag (fun q => q.1) (fun q => q.2)
      (fun q => announce.leaf q.1 q.2) (fun x => announce.leaf x x)
      (fun q hq => by rw [diag_fst_eq_snd q hq]), add_zero]

/-- ... but an observer learns one bit. -/
theorem externalInfoCost_announce_diag : externalInfoCost (announce.transcriptLaw diag) = 1 := by
  have hl : announce.transcriptLaw diag =
      (PMF.uniformOfFintype Bool).map fun b => (b, b, announce.leaf b b) := by
    rw [Protocol.transcriptLaw_eq, diag, PMF.map_comp]
    rfl
  rw [hl, externalInfoCost_map, mutualInfo_map,
    entropy_map_of_injective _ (f := fun b : Bool => (b, b)) (fun _ _ h => congrArg Prod.fst h),
    entropy_map_of_injective _ announce_leaf_injective,
    entropy_map_of_injective _ (f := fun b : Bool => ((b, b), announce.leaf b b))
      (fun _ _ h => congrArg (fun t => t.1.1) h),
    entropy_uniform, Fintype.card_bool, Nat.cast_ofNat, Real.logb_self_eq_one one_lt_two]
  ring

/-- The inequality `internalInfoCost ≤ externalInfoCost` can be strict. -/
example : internalInfoCost (announce.transcriptLaw diag) <
    externalInfoCost (announce.transcriptLaw diag) := by
  rw [internalInfoCost_announce_diag, externalInfoCost_announce_diag]
  exact one_pos

/-- The external information cost meets the depth bound with equality. -/
example : externalInfoCost (announce.transcriptLaw diag) = announce.depth := by
  rw [externalInfoCost_announce_diag]
  simp [announce]

/-- On independent inputs the two costs agree. -/
example : internalInfoCost (announce.transcriptLaw indep) =
    externalInfoCost (announce.transcriptLaw indep) :=
  announce.internalInfoCost_eq_externalInfoCost indep (mutualInfo_bind_map_prodMk _ _)

example : internalInfoCost (announce.transcriptLaw indep) ≤ 1 :=
  (announce.internalInfoCost_le_depth indep).trans_eq (by simp [announce])

/-- Computing Alice's bit on perfectly correlated inputs has information complexity `0`, although
it needs one bit of communication. -/
example : PublicCoin.infoComplexity 0 (fun x _ z => z = x) Set.univ Set.univ diag = 0 := by
  refine le_antisymm ?_ bot_le
  refine (PublicCoin.infoComplexity_le_protocol announce_solves le_rfl diag).trans_eq ?_
  rw [internalInfoCost_announce_diag, ENNReal.ofReal_zero]

/-- The public-coin costs of a protocol sampled with certainty are those of the protocol. -/
example : PublicCoin.externalInfoCost (PMF.pure announce) diag = 1 := by
  rw [PublicCoin.externalInfoCost_pure, externalInfoCost_announce_diag, ENNReal.ofReal_one]

end InformationComplexityTests
