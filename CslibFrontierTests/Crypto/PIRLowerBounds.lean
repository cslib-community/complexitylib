/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.PIR.Interactive
import CslibFrontier.Crypto.Protocols.PIR.LinearSummation
import CslibFrontier.Probability.PMF.Uniform

/-!
# Tests: lower bounds for private information retrieval

* **Interactive single server.** The server sending a three-bit database is a correct, private
  interactive scheme of protocol depth three, and no scheme has depth at most two. A protocol in
  which the user sends its two-bit index and the server answers with the bit is correct for a
  four-bit database (checked by `decide`) with depth three, so the lower bound shows that it is not
  private.
* **Linear summation.** The basic two-server scheme on three bits sends each server any of the
  `8` sets, while the even-set scheme sends exactly `4 = 2 ^ (3 - 1)`, the least possible, and
  those sets have a two-bit encoding. The scheme that sends `∅` and `{i}` is a correct
  linear-summation scheme, so the lower bound shows that it is not private.
-/

namespace CslibFrontierTests.Crypto.PIRLowerBounds

open Cslib Cslib.Crypto.Protocols.PIR Cslib.Communication Probability

/-! ### Interactive single server -/

example : (InteractiveScheme.download 3).IsCorrect ∧ (InteractiveScheme.download 3).IsPrivate ∧
    (InteractiveScheme.download 3).protocol.depth = 3 :=
  ⟨InteractiveScheme.isCorrect_download 3, InteractiveScheme.isPrivate_download 3,
    InteractiveScheme.depth_download 3⟩

example : ¬ ∃ (C D : Type) (P : InteractiveScheme (Fin 3) C D),
    P.IsCorrect ∧ P.IsPrivate ∧ P.protocol.depth ≤ 2 := by
  rw [InteractiveScheme.exists_iff]
  omega

/-- The server, holding `x`, sends `x j` for the index `j` named by the user's two bits. -/
def sendBit (x : Fin 4 → Bool) (b₁ b₀ : Bool) : Bool :=
  x (cond b₁ (cond b₀ 3 2) (cond b₀ 1 0))

/-- The user sends the two bits of its index, then the server sends the bit, which the user
outputs. -/
def indexProtocol : Protocol ((Fin 4 → Bool) × Unit) (Fin 4 × Unit) (Fin 4 × Unit → Bool) :=
  .bob (fun ic => decide (2 ≤ ic.1.val))
    (.bob (fun ic => decide (ic.1.val % 2 = 1))
      (.alice (fun xd => sendBit xd.1 false false) (.output fun _ => false) (.output fun _ => true))
      (.alice (fun xd => sendBit xd.1 false true) (.output fun _ => false) (.output fun _ => true)))
    (.bob (fun ic => decide (ic.1.val % 2 = 1))
      (.alice (fun xd => sendBit xd.1 true false) (.output fun _ => false) (.output fun _ => true))
      (.alice (fun xd => sendBit xd.1 true true) (.output fun _ => false) (.output fun _ => true)))

theorem run_indexProtocol : ∀ (x : Fin 4 → Bool) (i : Fin 4),
    indexProtocol.run (x, ()) (i, ()) (i, ()) = x i := by
  decide

/-- The user sends its index in the clear. -/
def indexScheme : InteractiveScheme (Fin 4) Unit Unit where
  userCoins _ := pure ()
  serverCoins := pure ()
  protocol := indexProtocol

theorem isCorrect_indexScheme : indexScheme.IsCorrect :=
  indexScheme.isCorrect_iff.mpr fun x i c _ d _ => by
    change indexProtocol.leafOutput (indexProtocol.leaf (x, d) (i, c)) (i, c) = x i
    rw [← Protocol.run_eq_leafOutput_leaf]
    exact run_indexProtocol x i

/-- Sending the index is correct with three bits for a four-bit database, so it is not private. -/
example : ¬ indexScheme.IsPrivate := fun hprivate => by
  have h := InteractiveScheme.card_le_depth isCorrect_indexScheme hprivate
  rw [Fintype.card_fin] at h
  exact absurd h (by decide)

/-! ### Linear summation -/

open Cslib.Crypto.Protocols.PIR.Scheme in
example : (twoServer (Fin 3)).IsLinearSummation := isLinearSummation_twoServer

/-- The basic scheme sends each server any of the `8` sets of three positions. -/
example (σ : Bool) (i : Fin 3) :
    (ProbComp.eval ((twoServer (Fin 3)).serverQuery σ i)).support.ncard = 8 := by
  rw [eval_serverQuery_twoServer,
    Set.eq_univ_of_forall Cslib.Probability.PMF.mem_support_uniformOfFintype, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rfl

/-- The even-set scheme sends exactly `4` sets, the least possible. -/
example (σ : Bool) (i : Fin 3) :
    (ProbComp.eval ((evenTwoServer (0 : Fin 3)).serverQuery σ i)).support.ncard = 4 := by
  rw [ncard_support_evenTwoServer, Fintype.card_fin]
  rfl

example (σ : Bool) : ∃ enc : (Fin 3 → Bool) → BitString 2,
    ∀ i, Set.InjOn enc (ProbComp.eval ((evenTwoServer (0 : Fin 3)).serverQuery σ i)).support :=
  exists_injOn_evenTwoServer (0 : Fin 3) σ

/-- The scheme that sends `∅` to the server `false` and `{i}` to the server `true`. -/
def directSets : Scheme (Fin 3) Bool Unit (Fin 3 → Bool) Bool where
  query i := pure ((), fun σ => Pi.single i σ)
  answer _ x q := x ⬝ᵥ q
  reconstruct _ _ a := a false + a true

theorem isLinearSummation_directSets : directSets.IsLinearSummation where
  answer_eq _ _ _ := rfl
  reconstruct_eq _ _ _ := rfl

theorem isCorrect_directSets : directSets.IsCorrect := by
  rw [isLinearSummation_directSets.isCorrect_iff]
  intro i r q hrq
  simp only [directSets, ProbComp.eval_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hrq
  obtain ⟨-, rfl⟩ := hrq
  funext j
  change (Pi.single i false : Fin 3 → Bool) j + (Pi.single i true : Fin 3 → Bool) j =
    (Pi.single i true : Fin 3 → Bool) j
  rw [show (Pi.single i false : Fin 3 → Bool) = 0 from Pi.single_zero i, Pi.zero_apply, zero_add]

/-- Sending `∅` and `{i}` is a correct linear-summation scheme in which each server receives one
set, fewer than `2 ^ (3 - 1)`, so it is not private. -/
example : ¬ directSets.IsPrivate := fun hprivate => by
  have h := isLinearSummation_directSets.card_sub_one_le isCorrect_directSets hprivate true 0
    (ℓ := 0) (enc := fun _ => Fin.elim0) (by
      rw [Scheme.eval_serverQuery]
      simp only [directSets, ProbComp.eval_pure, PMF.pure_map, PMF.support_pure]
      exact Set.injOn_singleton _ _)
  rw [Fintype.card_fin] at h
  omega

end CslibFrontierTests.Crypto.PIRLowerBounds
