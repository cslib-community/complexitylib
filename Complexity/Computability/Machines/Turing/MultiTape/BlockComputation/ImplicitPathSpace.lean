/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitPathCorrect
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadSearchSpace
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import Complexity.Tactic.EncLen
import Mathlib.Data.List.FinRange

/-!
# Native implicit block-tree navigation

Every provider branch is compiled for a fixed simulated work head. A fixed finite list of
provider searches is assembled and indexed by the runtime child number. Thus no head exponent
depends on runtime data. Following a path retains only its binary interval cursor and schedule.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ImplicitPath

open MultiTapeTM MultiTapeTM.ComputableInSpace

private theorem fixedList {α β ι : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (items : List ι) (f : ι → α → β)
    (hf : ∀ i, ComputableInSpace (f i) encA encB (fun a => (encA a).length)) :
    ComputableInSpace (fun a => items.map (fun i => f i a)) encA (encList encB)
      (fun a => (encA a).length) := by
  induction items with
  | nil => exact budget_const [] (.refl _)
  | cons i items ih => exact budget_cons (hf i) ih

/-- Binary schedule and current source interval. -/
@[expose] noncomputable def encProviderArgs : (ℕ × ℕ) ↪ List Bool := encPair encNat encNat

/-- Source schedule, horizon, current interval and requested child. -/
@[expose] noncomputable def encChildArgs : (ℕ × ℕ × ℕ × ℕ) ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))

/-- One fixed work-head provider is computed in native linear space. -/
theorem provider_inSpace (k : ℕ) (p : Fin (k * 3)) :
    ComputableInSpace (fun a => provider k a p) encProviderArgs encNat
      (fun a => (encProviderArgs a).length) := by
  let hd := finProdFinEquiv.symm p
  have hs := fst encNat encNat
  have hn := snd encNat encNat
  have hsearch := budget_comp_linear (ScheduleRead.search_inSpace k (hd.1.val + 1))
    (budget_prod hs (budget_prod hn (budget_const (encB := encNat) hd.2.val (.refl _))))
  have hget : ComputableInSpace (fun o : Option ℕ => o.getD 0)
      (encOption encNat) encNat (fun o => (encOption encNat o).length) :=
    of_inO (ComputableInDegree.getD (enc₁ := encNat) 0).inO_one
  have hsome : ComputableInSpace (fun o : Option ℕ => o.isSome)
      (encOption encNat) encBool (fun o => (encOption encNat o).length) :=
    of_inO (ComputableInDegree.isSome encNat).inO_one
  have hindex := budget_natSucc (budget_comp_linear hget hsearch)
  refine (budget_ite (budget_comp_linear hsome hsearch) hindex
    (budget_const (encB := encNat) 0 (.refl _))).of_enc_eq ?_
  rintro ⟨σ, n⟩
  change encNat (((ScheduleRead.search k (hd.1.val + 1) (σ, n, hd.2.val)).map
    fun j => j + 1).getD 0) = encNat (if
      (ScheduleRead.search k (hd.1.val + 1) (σ, n, hd.2.val)).isSome then
        (ScheduleRead.search k (hd.1.val + 1) (σ, n, hd.2.val)).getD 0 + 1 else 0)
  cases ScheduleRead.search k (hd.1.val + 1) (σ, n, hd.2.val) <;> simp

/-- The provider family is fixed by the simulated machine, not by the runtime horizon. -/
theorem providers_inSpace (k : ℕ) :
    ComputableInSpace (providers k) encProviderArgs (encList encNat)
      (fun a => (encProviderArgs a).length) := by
  have h := fixedList encProviderArgs encNat (List.finRange (k * 3))
    (fun p a => provider k a p) (provider_inSpace k)
  exact h.of_enc_eq fun _ => by simp only [providers, List.ofFn_eq_map]

/-- Child navigation uses only binary comparisons and the fixed provider family. -/
theorem child_inSpace (k : ℕ) :
    ComputableInSpace (child k) encChildArgs encNat (fun a => (encChildArgs a).length) := by
  have hs := fst encNat (encPair encNat (encPair encNat encNat))
  have hr := snd encNat (encPair encNat (encPair encNat encNat))
  have hq := hr.fst'
  have hn := hr.snd'.fst'
  have hj := hr.snd'.snd'
  have hzero := budget_const (encIn := encChildArgs) (encB := encNat) 0 (.refl _)
  have hpred := budget_natSub hn (budget_const (encB := encNat) 1 (.refl _))
  have hbelow := budget_natLt hpred hq
  have hchild := budget_natLt hj (budget_const (encB := encNat) (k * 3 + 1) (.refl _))
  have hguard := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod hbelow hchild)
  have hproviders := budget_comp_linear (providers_inSpace k) (budget_prod hs hpred)
  have hlookup := budget_comp_linear (getD.weaken (.of_le_linear 8 8 fun _ => le_rfl))
    (budget_prod hproviders
    (budget_natSub hj (budget_const (encB := encNat) 1 (.refl _))))
  refine (budget_ite (budget_natIsZero hn) hzero (budget_ite hguard
    (budget_ite (budget_natIsZero hj) hpred hlookup) hzero)).of_enc_eq ?_
  rintro ⟨σ, q, n, j⟩
  cases n with
  | zero => simp [child]
  | succ n =>
    by_cases hn : n < q <;> by_cases hj : j < k * 3 + 1 <;>
      simp [child, hn, hj]

/-- The actual path and its binary schedule/horizon storage. -/
@[expose] noncomputable def encWalkArgs : WalkArgs ↪ List Bool :=
  encPair encNat (encPair encNat (encList encNat))

private theorem pathStep_inSpace (k : ℕ) :
    ComputableInSpace (fun p : ((ℕ × ℕ) × ℕ) × ℕ =>
      child k (p.1.1.1, p.1.1.2, p.1.2, p.2))
      (encPair (encPair encProviderArgs encNat) encNat) encNat
      (fun p => (encPair (encPair encProviderArgs encNat) encNat p).length) := by
  have hp := fst (encPair encProviderArgs encNat) encNat
  have hj := snd (encPair encProviderArgs encNat) encNat
  exact budget_comp_linear (child_inSpace k)
    (budget_prod hp.fst'.fst' (budget_prod hp.fst'.snd' (budget_prod hp.snd' hj)))


/-- Walking a stored path keeps only its decreasing binary interval cursor and fixed metadata. -/
theorem walk_inSpace (k : ℕ) :
    ComputableInSpace (walk k) encWalkArgs encNat (fun a => (encWalkArgs a).length) := by
  have hs := fst encNat (encPair encNat (encList encNat))
  have hr := snd encNat (encPair encNat (encList encNat))
  have hq := hr.fst'
  have hpath := hr.snd'
  have hpar := budget_prod hs hq
  have hstates (a : WalkArgs) (i : ℕ) (_hi : i ≤ a.2.2.length) :
      (encNat ((a.2.2.take i).foldl (fun n j => child k (a.1, a.2.1, n, j))
        a.2.1)).length ≤ (encNat a.2.1).length :=
    ComputableTidilyInO.length_encNat_mono (walk_le k a.1 a.2.1 (a.2.2.take i))
  have hspace (a : WalkArgs) (i : ℕ) (hi : i < a.2.2.length) :
      (encPair (encPair encProviderArgs encNat) encNat
        (((a.1, a.2.1), (a.2.2.take i).foldl
          (fun n j => child k (a.1, a.2.1, n, j)) a.2.1), a.2.2[i])).length ≤
            16 * ((encWalkArgs a).length + 1) := by
    have hc := hstates a i hi.le
    have hm := length_le_encList_of_mem encNat (List.getElem_mem hi)
    enc_len [encWalkArgs, encProviderArgs] at *
  have hfold := ComputableInSpace.foldlWith
    (encIn := encWalkArgs) (encP := encProviderArgs) (encB := encNat)
    (encA := encNat) (encL := encList encNat)
    (par := fun a : WalkArgs => (a.1, a.2.1))
    (list := fun a : WalkArgs => a.2.2) (init := fun a : WalkArgs => a.2.1)
    (Sp := fun a => (encWalkArgs a).length) (Sl := fun a => (encWalkArgs a).length)
    (Si := fun a => (encWalkArgs a).length)
    (Q := fun a => 16 * ((encWalkArgs a).length + 1))
    (B := fun a => (encNat a.2.1).length)
    (step := fun par n j => child k (par.1, par.2, n, j))
    hpar hpath hq (pathStep_inSpace k)
    hspace hstates
  exact hfold.weaken (.of_le_linear 100 100 fun a => by enc_len [encWalkArgs, encProviderArgs])

end Turing.MultiTapePTM.BlockComputation.ImplicitPath
