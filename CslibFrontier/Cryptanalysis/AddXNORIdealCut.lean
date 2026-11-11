/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealChain
public import CslibFrontier.Languages.Probabilistic.RandomPermutation.Reprogramming
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.List.FinRange

/-!
# A valid hidden-cut planting law

An ideal chain uses a different permutation label at each layer. Force one cut edge, leaving
its prefix and suffix permutations unchanged. Swapping the displaced image preserves
bijectivity on every trace. `Cut.uniform_splice` proves the exact planted joint law by an
involutive change of variables; it does not assume the manuscript's literal frontier sampler.

This is the probabilistic change of variables for a stopped game hop. The collision/covering
probability of observing a changed entry is a separate obligation, not a hypothesis here.

## Main definitions

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.pathEquiv`: an ideal path as a permutation.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Cut`: prefix, cut label and suffix with
  distinct cut label.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Cut.splice`: the real single-permutation image swap.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Cut.endpoint_splice`: the new chain reaches
  the target.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Cut.uniform_splice`: exact eager planted
  distribution.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.source_uniform_splice`: the original source chain's
  exact hidden-cut planting law.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Cut.eval_splice_eq_of_not_affected`: changes are
  confined to four concrete query points.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain

open Probability RandomPermutation

/-- A path composed as an actual bijection, so its suffix can be run backwards. -/
@[expose] def pathEquiv {Index Word : Type} (perms : Index → Equiv.Perm Word) :
    List Index → Equiv.Perm Word
  | [] => Equiv.refl Word
  | i :: rest => (perms i).trans (pathEquiv perms rest)

/-- The bundled path agrees with the experiment's original evaluation. -/
theorem pathEquiv_apply {Index Word : Type} (perms : Index → Equiv.Perm Word)
    (path : List Index) (seed : Word) : pathEquiv perms path seed = evaluate perms path seed := by
  induction path generalizing seed with
  | nil => rfl
  | cons i rest ih => exact ih _

/-- Concatenation composes the actual path permutations in traversal order. -/
theorem pathEquiv_append {Index Word : Type} (perms : Index → Equiv.Perm Word)
    (left right : List Index) :
    pathEquiv perms (left ++ right) = (pathEquiv perms left).trans (pathEquiv perms right) := by
  induction left with
  | nil => rfl
  | cons i rest ih => simp only [List.cons_append, pathEquiv, ih, Equiv.trans_assoc]

/-- Reversing a path and inverting each permutation computes the inverse of the whole path. -/
theorem pathEquiv_reverse_symm {Index Word : Type} (perms : Index → Equiv.Perm Word)
    (path : List Index) :
    pathEquiv (fun label => (perms label).symm) path.reverse = (pathEquiv perms path).symm := by
  induction path with
  | nil => rfl
  | cons label rest ih =>
    simp only [List.reverse_cons, pathEquiv_append, pathEquiv, ih, Equiv.symm_trans,
      Equiv.trans_refl]

/-- Updating a label absent from a path leaves its whole permutation unchanged. -/
theorem pathEquiv_update {Index Word : Type} [DecidableEq Index]
    (perms : Index → Equiv.Perm Word) (path : List Index) (edge : Index)
    (replacement : Equiv.Perm Word) (h : edge ∉ path) :
    pathEquiv (Function.update perms edge replacement) path = pathEquiv perms path := by
  induction path with
  | nil => rfl
  | cons i rest ih =>
    have hi : i ≠ edge := fun he => h (by simp [he])
    simp only [pathEquiv, Function.update_of_ne hi, ih (fun hm => h (by simp [hm]))]

/-- Structural data of a single cut. The selected permutation occurs in neither side.
These are syntactic nonoccurrence conditions, not semantic/security conclusions. -/
structure Cut (Index : Type) where
  /-- Labels before the forced edge. -/
  left : List Index
  /-- The permutation whose one entry is forced. -/
  edge : Index
  /-- Labels after the forced edge. -/
  right : List Index
  /-- The prefix does not query the forced permutation. -/
  not_left : edge ∉ left
  /-- The suffix does not query the forced permutation. -/
  not_right : edge ∉ right

namespace Cut

variable {Index Word : Type} [DecidableEq Index] [DecidableEq Word]

/-- Select any position of a path with distinct labels. Nonoccurrence follows from the
syntactic path, without a supplied semantic cut invariant. -/
@[expose] def ofPath (path : List Index) (hn : path.Nodup) (k : Fin path.length) : Cut Index :=
  let split : (path.take k.val ++ path[k.val] :: path.drop (k.val + 1)).Nodup := by
    rw [List.getElem_cons_drop k.isLt, List.take_append_drop]
    exact hn
  let ⟨_, hrest, hdisjoint⟩ := List.nodup_append.mp split
  let ⟨hnot, _⟩ := List.nodup_cons.mp hrest
  { left := path.take k.val
    edge := path[k.val]
    right := path.drop (k.val + 1)
    not_left := fun h => hdisjoint _ h _ (List.mem_cons_self) rfl
    not_right := hnot }

omit [DecidableEq Index] [DecidableEq Word] in
/-- The selected cut reconstructs the entire input path. -/
theorem ofPath_path (path : List Index) (hn : path.Nodup) (k : Fin path.length) :
    (ofPath path hn k).left ++ (ofPath path hn k).edge :: (ofPath path hn k).right = path := by
  change path.take k.val ++ path[k.val] :: path.drop (k.val + 1) = path
  rw [List.getElem_cons_drop k.isLt, List.take_append_drop]

/-- The hidden cut's input after the actual prefix. -/
@[expose] def input (cut : Cut Index) (perms : Index → Equiv.Perm Word) (seed : Word) : Word :=
  pathEquiv perms cut.left seed

/-- The actual suffix permutation. -/
@[expose] def suffix (cut : Cut Index) (perms : Index → Equiv.Perm Word) : Equiv.Perm Word :=
  pathEquiv perms cut.right

/-- The actual full chain target before any reprogramming. -/
@[expose] def endpoint (cut : Cut Index) (perms : Index → Equiv.Perm Word) (seed : Word) : Word :=
  cut.suffix perms (perms cut.edge (cut.input perms seed))

/-- Swap the one selected permutation's images to install the required hidden cut edge. -/
@[expose] def splice (cut : Cut Index) (perms : Index → Equiv.Perm Word) (seed target : Word) :
    Index → Equiv.Perm Word :=
  Function.update perms cut.edge
    (force (perms cut.edge) (cut.input perms seed) ((cut.suffix perms).symm target))

/-- The actual prefix is unaffected by the cut replacement. -/
theorem input_splice (cut : Cut Index) (perms : Index → Equiv.Perm Word) (seed target : Word) :
    cut.input (cut.splice perms seed target) seed = cut.input perms seed := by
  simp only [input, splice, pathEquiv_update perms cut.left cut.edge _ cut.not_left]

/-- The entire suffix, in both directions, is unaffected by the cut replacement. -/
theorem suffix_splice (cut : Cut Index) (perms : Index → Equiv.Perm Word) (seed target : Word) :
    cut.suffix (cut.splice perms seed target) = cut.suffix perms := by
  exact pathEquiv_update perms cut.right cut.edge _ cut.not_right

/-- The forced path reaches the requested target even on collision traces. -/
theorem endpoint_splice (cut : Cut Index) (perms : Index → Equiv.Perm Word) (seed target : Word) :
    cut.endpoint (cut.splice perms seed target) seed = target := by
  rw [endpoint, input_splice, suffix_splice]
  simp only [splice, Function.update_self, force_apply, Equiv.apply_symm_apply]

/-- Retargeting the same cut to its old endpoint restores every permutation. -/
theorem splice_restore (cut : Cut Index) (perms : Index → Equiv.Perm Word) (seed target : Word) :
    cut.splice (cut.splice perms seed target) seed (cut.endpoint perms seed) = perms := by
  rw [splice, input_splice, suffix_splice]
  simp only [splice, Function.update_self, endpoint,
    Equiv.symm_apply_apply, force_restore, Function.update_idem, Function.update_eq_self]

/-- The four possible changed-query points at the selected label. This uses the actual
prefix, inverse suffix and original cut permutation, rather than a supplied hidden path. -/
@[expose] def affected (cut : Cut Index) (perms : Index → Equiv.Perm Word)
    (seed target : Word) (query : Index × PermQuery Word) : Prop :=
  query.1 = cut.edge ∧ match query.2 with
    | .forward point => point = cut.input perms seed ∨
        perms cut.edge point = (cut.suffix perms).symm target
    | .inverse point => point = perms cut.edge (cut.input perms seed) ∨
        point = (cut.suffix perms).symm target

/-- Every query outside the four concrete cut points has exactly the original answer. -/
theorem eval_splice_eq_of_not_affected (cut : Cut Index) (perms : Index → Equiv.Perm Word)
    (seed target : Word) (query : Index × PermQuery Word)
    (h : ¬cut.affected perms seed target query) :
    Family.eval (cut.splice perms seed target) query = Family.eval perms query := by
  obtain ⟨label, query⟩ := query
  by_cases hl : label = cut.edge
  · subst label
    cases query with
    | forward point =>
      have hi : point ≠ cut.input perms seed := fun he => h ⟨rfl, Or.inl he⟩
      have ht : perms cut.edge point ≠ (cut.suffix perms).symm target :=
        fun he => h ⟨rfl, Or.inr he⟩
      simpa only [Family.eval, splice, Function.update_self, evalPerm_forward] using
        force_apply_of_ne (perms cut.edge) (cut.input perms seed)
          ((cut.suffix perms).symm target) point hi ht
    | inverse point =>
      have hi : point ≠ perms cut.edge (cut.input perms seed) := fun he => h ⟨rfl, Or.inl he⟩
      have ht : point ≠ (cut.suffix perms).symm target := fun he => h ⟨rfl, Or.inr he⟩
      simpa only [Family.eval, splice, Function.update_self, evalPerm_inverse] using
        force_symm_apply_of_ne (perms cut.edge) (cut.input perms seed)
          ((cut.suffix perms).symm target) point hi ht
  · simp only [Family.eval, splice, Function.update_of_ne hl]

/-- The reversible whole-experiment change of variables retaining the old target. -/
@[expose] def spliceEquiv (cut : Cut Index) (seed : Word) :
    ((Index → Equiv.Perm Word) × Word) ≃ ((Index → Equiv.Perm Word) × Word) :=
  (show Function.Involutive (fun p : (Index → Equiv.Perm Word) × Word =>
      (cut.splice p.1 seed p.2, cut.endpoint p.1 seed)) from by
    rintro ⟨perms, target⟩
    simp only [splice_restore, endpoint_splice]).toPerm

/-- An independent uniform target forced at the hidden cut gives the exact planted family and
public target. The continuation may observe the entire family and make arbitrary adaptive calls. -/
theorem uniform_splice [Fintype Index] [Fintype Word] [Nonempty Word] {Output : Type}
    (cut : Cut Index) (seed : Word) (observe : (Index → Equiv.Perm Word) → Word → PMF Output) :
    ((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
      (PMF.uniformOfFintype Word).bind fun target =>
        observe (cut.splice perms seed target) target) =
      (PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
        observe perms (cut.endpoint perms seed) := by
  have h := PMF.uniformOfFintype_bind_bind_fst_equiv (cut.spliceEquiv seed)
    (fun perms => observe perms (cut.endpoint perms seed))
  change ((PMF.uniformOfFintype (Index → Equiv.Perm Word)).bind fun perms =>
    (PMF.uniformOfFintype Word).bind fun target =>
      observe (cut.splice perms seed target)
        (cut.endpoint (cut.splice perms seed target) seed)) = _ at h
  simpa only [endpoint_splice] using h

omit [DecidableEq Index] [DecidableEq Word] in
/-- The full endpoint is exactly evaluation of the cut's original path. -/
theorem endpoint_eq_evaluate (cut : Cut Index) (perms : Index → Equiv.Perm Word) (seed : Word) :
    cut.endpoint perms seed = evaluate perms (cut.left ++ cut.edge :: cut.right) seed := by
  rw [← pathEquiv_apply, pathEquiv_append]
  rfl

end Cut

/-- The source path has distinct labels because the layer is part of every label. -/
theorem sourcePath_nodup {q : ℕ} (bits : Operators q) :
    (List.ofFn fun i => (i, bits i)).Nodup :=
  List.nodup_ofFn.mpr fun _ _ heq => congrArg Prod.fst heq

/-- A hidden cut at any source layer, including the eventual middle-layer choice. -/
@[expose] def sourceCut {q : ℕ} (bits : Operators q) (k : Fin q) : Cut (Label q) :=
  Cut.ofPath (List.ofFn fun i => (i, bits i)) (sourcePath_nodup bits)
    ⟨k.val, by simpa only [List.length_ofFn] using k.isLt⟩

/-- The hidden-cut target is the original source chain, not a separately assumed witness. -/
theorem sourceCut_endpoint {q : ℕ} {Word : Type}
    (bits : Operators q) (k : Fin q) (perms : Label q → Equiv.Perm Word) (seed : Word) :
    (sourceCut bits k).endpoint perms seed = chain perms bits seed := by
  rw [Cut.endpoint_eq_evaluate]
  simp only [sourceCut, Cut.ofPath_path, chain]

/-- Exact source planting by a hidden single-cut image swap. This joint law permits observing
all permutations after the change of variables, so it composes with any adaptive adversary. -/
theorem source_uniform_splice {q : ℕ} {Word Output : Type} [Fintype Word]
    [DecidableEq Word] [Nonempty Word] (bits : Operators q) (k : Fin q) (seed : Word)
    (observe : (Label q → Equiv.Perm Word) → Word → PMF Output) :
    ((PMF.uniformOfFintype (Label q → Equiv.Perm Word)).bind fun perms =>
      (PMF.uniformOfFintype Word).bind fun target =>
        observe ((sourceCut bits k).splice perms seed target) target) =
      (PMF.uniformOfFintype (Label q → Equiv.Perm Word)).bind fun perms =>
        observe perms (chain perms bits seed) := by
  simpa only [sourceCut_endpoint] using (sourceCut bits k).uniform_splice seed observe

end Cslib.Cryptanalysis.AddXNOR.IdealChain
