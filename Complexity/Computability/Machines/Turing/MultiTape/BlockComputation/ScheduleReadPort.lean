/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadSearchSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProvidersCorrect

/-!
# Native provider-port readers

After locating a previous provider interval, the reader computes the target block's port from
streamed positive and negative digit counts. The optional provider port has exactly the meaning
of the functional assembler's `portMap`. Tape count and column offset remain fixed parameters;
the schedule, target interval and port are binary runtime data.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleRead

open MultiTapeTM MultiTapeTM.ComputableInSpace

/-- Read a target block's port in another interval's window from streamed digit counts. -/
@[expose] def port (k c : ℕ) : WindowArgs → Fin 3 := fun (σ, i, δ, j) =>
  let pi := read k c 2 (σ, i)
  let ni := read k c 0 (σ, i)
  let pj := read k c 2 (σ, j)
  let nj := read k c 0 (σ, j)
  ⟨(pi + nj + δ - (ni + pj)) % 3, Nat.mod_lt _ (by decide)⟩

/-- The streamed port agrees with the existing numeric port convention. -/
theorem val_port_eq_portOfNum (k c σ i δ j : ℕ) :
    (port k c (σ, i, δ, j)).val = portOfNum k σ c i j δ := by
  simp only [port, read_eq_digitCount, portOfNum]

/-- The selected port is computed in native space linear in actual binary input storage. -/
theorem port_inSpace (k c : ℕ) :
    ComputableInSpace (port k c) encWindowArgs (encFinite (Fin 3))
      (fun a => (encWindowArgs a).length) := by
  have hs := fst encNat (encPair encNat (encPair encNat encNat))
  have ht := snd encNat (encPair encNat (encPair encNat encNat))
  have hi := budget_comp_linear (fst encNat (encPair encNat encNat)) ht
  have hdj := budget_comp_linear (snd encNat (encPair encNat encNat)) ht
  have hd := budget_comp_linear (fst encNat encNat) hdj
  have hj := budget_comp_linear (snd encNat encNat) hdj
  have hpi := budget_comp_linear (read_inSpace k c 2) (budget_prod hs hi)
  have hni := budget_comp_linear (read_inSpace k c 0) (budget_prod hs hi)
  have hpj := budget_comp_linear (read_inSpace k c 2) (budget_prod hs hj)
  have hnj := budget_comp_linear (read_inSpace k c 0) (budget_prod hs hj)
  have hvalue := budget_natSub (budget_natAdd (budget_natAdd hpi hnj) hd)
    (budget_natAdd hni hpj)
  have hfin := budget_finMod (by decide : 0 < 3) hvalue (.refl _)
  exact (budget_finite (encC := encFinite (Fin 3)) id hfin).of_enc_eq
    fun ⟨σ, i, δ, j⟩ => rfl

/-- Locate the last earlier provider, returning its port or absence for a blank target block. -/
@[expose] def providerPort (k c : ℕ) (a : SearchArgs) : Option (Fin 3) :=
  let (σ, i, δ) := a
  (search k c a).map fun j => port k c (σ, i, δ, j)

/-- Native optional provider ports include the predecessor search and use only actual binary
argument storage. A missing predecessor remains absent. -/
theorem providerPort_inSpace (k c : ℕ) :
    ComputableInSpace (providerPort k c) encSearchArgs (encOption (encFinite (Fin 3)))
      (fun a => (encSearchArgs a).length) := by
  have hs := fst encNat (encPair encNat encNat)
  have ht := snd encNat (encPair encNat encNat)
  have hi := ht.fst'
  have hd := ht.snd'
  have hsearch := search_inSpace k c
  have hget : ComputableInSpace (fun o : Option ℕ => o.getD 0)
      (encOption encNat) encNat (fun o => (encOption encNat o).length) :=
    of_inO (ComputableInDegree.getD (enc₁ := encNat) 0).inO_one
  have hisSome : ComputableInSpace (fun o : Option ℕ => o.isSome)
      (encOption encNat) encBool (fun o => (encOption encNat o).length) :=
    of_inO (ComputableInDegree.isSome encNat).inO_one
  have hj := budget_comp_linear hget hsearch
  have hp := budget_comp_linear (port_inSpace k c)
    (budget_prod hs (budget_prod hi (budget_prod hd hj)))
  have hsome := budget_finite (encC := encOption (encFinite (Fin 3))) some hp
  have hnone := budget_const (encB := encOption (encFinite (Fin 3))) none
    (show (fun a => (encSearchArgs a).length) ≼ fun a => (encSearchArgs a).length from .refl _)
  refine (budget_ite (budget_comp_linear hisSome hsearch) hsome hnone).of_enc_eq ?_
  rintro ⟨σ, i, δ⟩
  cases ht : search k c (σ, i, δ) <;> simp [providerPort, ht]

/-- The native optional port is exactly the one supplied to the functional entering-window
assembler by the same numbered schedule. -/
theorem providerPort_eq_portMap {k q : ℕ} (σ : ℕ) (i : Fin q) (h : Fin k) (δ : Fin 3) :
    providerPort k (h + 1) (σ, i, δ) =
      QueryReplay.Providers.portMap (scheduleOfNat k q σ) i h δ := by
  rw [providerPort, search_eq_lastBefore]
  unfold QueryReplay.Providers.portMap
  cases hl : lastBefore (InWindow (scheduleOfNat k q σ) h
      (portBlock (scheduleOfNat k q σ) i h δ)) i with
  | none => simp
  | some j =>
    simp only [Option.map_some]
    congr 1
    apply Fin.ext
    rw [val_port_eq_portOfNum, val_portOf]

/-- Compute every fixed work-head/neighbor port from the actual binary schedule and interval. -/
@[expose] def providerMap (k : ℕ) (a : ℕ × ℕ) : QueryReplay.Providers.PortMap k :=
  let (σ, i) := a
  fun h δ => providerPort k (h + 1) (σ, i, δ)

/-- All provider ports can be computed natively; their fixed family size depends only on the
simulated machine's number of work tapes. -/
theorem providerMap_inSpace (k : ℕ) :
    ComputableInSpace (providerMap k) encState QueryReplay.Providers.encPortMap
      (fun a => (encState a).length) := by
  have hs := fst encNat encNat
  have hi := snd encNat encNat
  have hentry (h : Fin k) (δ : Fin 3) :=
    budget_comp_linear (providerPort_inSpace k (h + 1))
      (budget_prod hs (budget_prod hi (budget_const (encB := encNat) δ.val (.refl _))))
  exact pi_linear fun h => pi_linear fun δ => hentry h δ

/-- The complete native provider map is the existing functional assembler's map. -/
theorem providerMap_eq_portMap {k q : ℕ} (σ : ℕ) (i : Fin q) :
    providerMap k (σ, i) = QueryReplay.Providers.portMap (scheduleOfNat k q σ) i := by
  funext h δ
  exact providerPort_eq_portMap σ i h δ

end Turing.MultiTapePTM.BlockComputation.ScheduleRead
