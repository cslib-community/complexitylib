/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitPathSpace
public import Complexity.Computability.TreeEval.Ary.Descending

/-!
# Checked implicit block-tree addresses

A raw path is accepted only if its depth is at most the supplied horizon and every child
number is in the fixed fan-in. Accepted paths resolve to the existing descending tree's node
index. Rejected paths are reported as absent rather than silently becoming the padded source.
Both validation and navigation use native space linear in the stored binary path and metadata.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ImplicitPath

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib.TreeEval.Ary

/-- Valid depth and in-range child numbers for a raw stored path. -/
@[expose] def valid (k : ℕ) : WalkArgs → Bool := fun (_, q, path) =>
  decide (path.length ≤ q) && path.all (fun j => decide (j < k * 3 + 1))

/-- Resolve only well-formed raw addresses; absence remains distinct from the source index. -/
@[expose] def lookupIndex (k : ℕ) (a : WalkArgs) : Option ℕ :=
  if valid k a then some (walk k a) else none

private theorem fold_check (k : ℕ) (path : List ℕ) (ok : Bool) :
    path.foldl (fun good j => good && decide (j < k * 3 + 1)) ok =
      (ok && path.all (fun j => decide (j < k * 3 + 1))) := by
  induction path generalizing ok with
  | nil => simp
  | cons j path ih =>
    simp only [List.foldl_cons, ih, List.all_cons, Bool.and_assoc]

private theorem all_inSpace (k : ℕ) :
    ComputableInSpace (fun a : WalkArgs => a.2.2.all (fun j => decide (j < k * 3 + 1)))
      encWalkArgs encBool (fun a => (encWalkArgs a).length) := by
  have hpath := (snd encNat (encPair encNat (encList encNat))).snd'
  have hinit : ComputableInSpace (fun _ : WalkArgs => true) encWalkArgs encBool
      (fun a => (encWalkArgs a).length) := budget_const true (.refl _)
  have hstep : ComputableInSpace (fun p : Bool × ℕ => p.1 && decide (p.2 < k * 3 + 1))
      (encPair encBool encNat) encBool (fun p => (encPair encBool encNat p).length) :=
    budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
      (budget_prod (fst encBool encNat)
        (budget_natLt (snd encBool encNat)
          (budget_const (encB := encNat) (k * 3 + 1) (.refl _))))
  have hspace (a : WalkArgs) (i : ℕ) (hi : i < a.2.2.length) :
      (encPair encBool encNat
        ((a.2.2.take i).foldl (fun good j => good && decide (j < k * 3 + 1)) true,
          a.2.2[i])).length ≤ 4 * ((encWalkArgs a).length + 1) := by
    have hm := length_le_encList_of_mem encNat (List.getElem_mem hi)
    simp only [encWalkArgs, length_encPair, encBool_apply, List.length_singleton] at *
    omega
  have hstates (a : WalkArgs) (i : ℕ) (_hi : i ≤ a.2.2.length) :
      (encBool ((a.2.2.take i).foldl
        (fun good j => good && decide (j < k * 3 + 1)) true)).length ≤
          4 * ((encWalkArgs a).length + 1) := by
    simp only [encBool_apply, List.length_singleton]
    omega
  have hfold := ComputableInSpace.foldl
    (encIn := encWalkArgs) (encA := encNat) (encL := encList encNat) (encB := encBool)
    (list := fun a : WalkArgs => a.2.2) (init := fun _ : WalkArgs => true)
    (step := fun good j => good && decide (j < k * 3 + 1))
    (Sl := fun a => (encWalkArgs a).length) (Si := fun a => (encWalkArgs a).length)
    (Q := fun a => 4 * ((encWalkArgs a).length + 1))
    (B := fun a => 4 * ((encWalkArgs a).length + 1))
    hpath hinit hstep hspace hstates
  exact (hfold.weaken (.of_le_linear 16 16 fun a => by
    simp only [encWalkArgs, length_encPair]
    omega)).of_enc_eq
    fun a => by simp only [fold_check, Bool.true_and]

/-- Raw-address validation is native and charges only stored path and metadata. -/
theorem valid_inSpace (k : ℕ) :
    ComputableInSpace (valid k) encWalkArgs encBool (fun a => (encWalkArgs a).length) := by
  have hrest := snd encNat (encPair encNat (encList encNat))
  have hq := hrest.fst'
  have hlength := budget_length hrest.snd'
  have hdepth := budget_finite (encC := encBool) Bool.not (budget_natLt hq hlength)
  exact (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod hdepth (all_inSpace k))).of_enc_eq fun ⟨σ, q, path⟩ => by
      by_cases h : path.length ≤ q
      · have hn : ¬q < path.length := by omega
        simp [valid, h, hn]
      · have hn : q < path.length := by omega
        simp [valid, h, hn]

/-- Native lookup preserves malformed-address rejection, including excess path depth. -/
theorem lookupIndex_inSpace (k : ℕ) :
    ComputableInSpace (lookupIndex k) encWalkArgs (encOption encNat)
      (fun a => (encWalkArgs a).length) := by
  have hsome := budget_optionSome (walk_inSpace k)
  exact (budget_ite (valid_inSpace k) hsome
    (budget_const (encB := encOption encNat) none (.refl _))).of_enc_eq fun _ => rfl

private theorem next_eq_child {k q : ℕ} (σ : ℕ) :
    Descending.next (BlockComputation.child (scheduleOfNat k q σ)) =
      BlockComputation.child (scheduleOfNat k q σ) := by
  funext n j
  cases n with
  | zero => rfl
  | succ n => simp [Descending.next]

/-- Typed paths pass the raw child-number guard and resolve to the existing descending model;
only the exact horizon-depth guard remains. -/
theorem lookupIndex_eq_resolve {k q : ℕ} (σ : ℕ) (path : List (Fin (k * 3 + 1))) :
    lookupIndex k (σ, q, path.map Fin.val) =
      if path.length ≤ q then
        some (Descending.resolve (BlockComputation.child (scheduleOfNat k q σ)) q path)
      else none := by
  have hall : (path.map Fin.val).all (fun j => decide (j < k * 3 + 1)) = true := by
    apply List.all_eq_true.mpr
    intro j hj
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hj
    exact decide_eq_true p.isLt
  simp only [lookupIndex, valid, List.length_map, hall, Bool.and_true, decide_eq_true_eq,
    walk_eq, Descending.resolve, next_eq_child]

end Turing.MultiTapePTM.BlockComputation.ImplicitPath
