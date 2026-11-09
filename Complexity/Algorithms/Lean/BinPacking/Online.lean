/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.BinPacking.FirstFit

/-!
# Online bin packing

An online bin-packing algorithm receives the items one at a time. It puts each item into a bin
that has room for it or opens a new bin, without seeing the items still to come, and it never
moves an item again. This file models deterministic online algorithms with capacity `C` as
`OnlinePacker C`. The rule `place` picks a bin for the next item from the items seen so far and
the current bins. If the chosen bin has no room, or no bin is chosen, the item opens a new last
bin (`onlineInsert`), so every rule yields a valid packing (`OnlinePacker.isPacking_run`). Every
deterministic online algorithm is such a rule, since its state after a prefix of the input is a
function of that prefix.

Two facts make lower bounds against all online algorithms possible. The packing of `l₁ ++ l₂`
continues the packing of `l₁` (`OnlinePacker.run_append`). And items that fail a predicate do
not change the number of bins holding an item that satisfies it (`OnlinePacker.countP_any_runFrom`):
such bins all exist before the items arrive. First Fit is an online packer
(`run_firstFitPacker`).

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.onlineInsert`: put an item into a chosen bin if it fits,
  and otherwise into a new last bin.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker`: a deterministic online bin-packing algorithm.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.run`: the packing an online packer builds.
* `Cslib.Algorithms.Lean.BinPacking.firstFitPacker`: First Fit as an online packer.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.isPacking_run`: an online packer packs every
  list of items that fit into a bin.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.run_append`: the packing of `l₁ ++ l₂` continues
  the packing of `l₁`.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.countP_any_runFrom`: items failing `p` leave the
  number of bins with an item satisfying `p` unchanged.
* `Cslib.Algorithms.Lean.BinPacking.run_firstFitPacker`: the online packer `firstFitPacker` is
  `firstFit`.
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

open scoped List

/-- Put item `a` into bin `i` (for `o = some i`) if it fits there, and otherwise, or for
`o = none`, into a new last bin. -/
@[expose] def onlineInsert (C a : ℕ) : Option ℕ → List (List ℕ) → List (List ℕ)
  | _, [] => [[a]]
  | none, b :: bs => b :: onlineInsert C a none bs
  | some 0, b :: bs =>
    if b.sum + a ≤ C then (b ++ [a]) :: bs else b :: onlineInsert C a none bs
  | some (i + 1), b :: bs => b :: onlineInsert C a (some i) bs

theorem flatten_onlineInsert_perm (C a : ℕ) :
    ∀ (o : Option ℕ) (bins : List (List ℕ)), (onlineInsert C a o bins).flatten ~ a :: bins.flatten
  | _, [] => by simp [onlineInsert]
  | none, b :: bs => by
    simp only [onlineInsert, List.flatten_cons]
    exact ((flatten_onlineInsert_perm C a none bs).append_left b).trans List.perm_middle
  | some 0, b :: bs => by
    simp only [onlineInsert]
    split_ifs
    · simp only [List.flatten_cons, List.append_assoc, List.singleton_append]
      exact List.perm_middle
    · simp only [List.flatten_cons]
      exact ((flatten_onlineInsert_perm C a none bs).append_left b).trans List.perm_middle
  | some (i + 1), b :: bs => by
    simp only [onlineInsert, List.flatten_cons]
    exact ((flatten_onlineInsert_perm C a (some i) bs).append_left b).trans List.perm_middle

theorem sum_le_of_mem_onlineInsert {C a : ℕ} (ha : a ≤ C) :
    ∀ {o : Option ℕ} {bins : List (List ℕ)}, (∀ b ∈ bins, b.sum ≤ C) →
      ∀ b ∈ onlineInsert C a o bins, b.sum ≤ C
  | _, [], _ => by simpa [onlineInsert] using ha
  | none, b :: bs, h => by
    simp only [onlineInsert, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact ⟨h.1, sum_le_of_mem_onlineInsert ha h.2⟩
  | some 0, b :: bs, h => by
    simp only [onlineInsert]
    split_ifs with hb
    · simp only [List.mem_cons, forall_eq_or_imp, List.sum_append, List.sum_singleton] at h ⊢
      exact ⟨hb, h.2⟩
    · simp only [List.mem_cons, forall_eq_or_imp] at h ⊢
      exact ⟨h.1, sum_le_of_mem_onlineInsert ha h.2⟩
  | some (i + 1), b :: bs, h => by
    simp only [onlineInsert, List.mem_cons, forall_eq_or_imp] at h ⊢
    exact ⟨h.1, sum_le_of_mem_onlineInsert ha h.2⟩

/-- Inserting an item that fails `p` does not change the number of bins holding an item that
satisfies `p`. -/
theorem countP_any_onlineInsert {C a : ℕ} {p : ℕ → Bool} (hp : p a = false) :
    ∀ (o : Option ℕ) (bins : List (List ℕ)),
      (onlineInsert C a o bins).countP (fun b => b.any p) = bins.countP (fun b => b.any p)
  | _, [] => by simp [onlineInsert, hp]
  | none, b :: bs => by
    simp only [onlineInsert, List.countP_cons, countP_any_onlineInsert hp none bs]
  | some 0, b :: bs => by
    simp only [onlineInsert]
    split_ifs
    · simp [List.countP_cons, hp]
    · simp only [List.countP_cons, countP_any_onlineInsert hp none bs]
  | some (i + 1), b :: bs => by
    simp only [onlineInsert, List.countP_cons, countP_any_onlineInsert hp (some i) bs]

/-- A deterministic online bin-packing algorithm with bin capacity `C`. -/
structure OnlinePacker (C : ℕ) where
  /-- The bin chosen for the next item `a`, from the items seen so far and the current bins;
  `none`, or a bin without room, opens a new bin. -/
  place : List ℕ → List (List ℕ) → ℕ → Option ℕ

namespace OnlinePacker

variable {C : ℕ} (A : OnlinePacker C)

/-- The packing that `A` builds from the items `hist` seen so far and the bins `bins` on further
items. -/
@[expose] def runFrom : List ℕ → List (List ℕ) → List ℕ → List (List ℕ)
  | _, bins, [] => bins
  | hist, bins, a :: l => runFrom (hist ++ [a]) (onlineInsert C a (A.place hist bins a) bins) l

/-- The packing of `l` that `A` builds online. -/
@[expose] def run (l : List ℕ) : List (List ℕ) := A.runFrom [] [] l

@[simp] theorem run_nil : A.run [] = [] := rfl

theorem runFrom_append (hist : List ℕ) (bins : List (List ℕ)) (l₁ l₂ : List ℕ) :
    A.runFrom hist bins (l₁ ++ l₂) = A.runFrom (hist ++ l₁) (A.runFrom hist bins l₁) l₂ := by
  induction l₁ generalizing hist bins with
  | nil => simp [runFrom]
  | cons a l ih => simp [runFrom, ih]

/-- **Online.** The packing of `l₁ ++ l₂` continues the packing of `l₁`. -/
theorem run_append (l₁ l₂ : List ℕ) : A.run (l₁ ++ l₂) = A.runFrom l₁ (A.run l₁) l₂ := by
  simp [run, runFrom_append]

theorem flatten_runFrom_perm :
    ∀ (hist : List ℕ) (bins : List (List ℕ)) (l : List ℕ),
      (A.runFrom hist bins l).flatten ~ bins.flatten ++ l
  | _, bins, [] => by simp [runFrom]
  | hist, bins, a :: l => by
    simp only [runFrom]
    refine (flatten_runFrom_perm _ _ l).trans ?_
    refine ((flatten_onlineInsert_perm C a _ bins).append_right l).trans ?_
    simpa using List.perm_middle.symm

theorem sum_le_of_mem_runFrom :
    ∀ {hist : List ℕ} {bins : List (List ℕ)} {l : List ℕ}, (∀ a ∈ l, a ≤ C) →
      (∀ b ∈ bins, b.sum ≤ C) → ∀ b ∈ A.runFrom hist bins l, b.sum ≤ C
  | _, _, [], _, h => by simpa [runFrom] using h
  | _, _, a :: l, hl, h => by
    simp only [runFrom]
    exact sum_le_of_mem_runFrom (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (sum_le_of_mem_onlineInsert (hl a List.mem_cons_self) h)

/-- An online packer packs every list of items that fit into a bin. -/
theorem isPacking_run {l : List ℕ} (hl : ∀ a ∈ l, a ≤ C) : IsPacking C l (A.run l) :=
  ⟨by simpa [run] using A.flatten_runFrom_perm [] [] l, A.sum_le_of_mem_runFrom hl (by simp)⟩

/-- Items that fail `p` leave the number of bins holding an item satisfying `p` unchanged. -/
theorem countP_any_runFrom {p : ℕ → Bool} :
    ∀ {hist : List ℕ} {bins : List (List ℕ)} {l : List ℕ}, (∀ a ∈ l, p a = false) →
      (A.runFrom hist bins l).countP (fun b => b.any p) = bins.countP (fun b => b.any p)
  | _, _, [], _ => by simp [runFrom]
  | _, _, a :: l, hl => by
    simp only [runFrom]
    rw [countP_any_runFrom (fun x hx => hl x (List.mem_cons_of_mem _ hx)),
      countP_any_onlineInsert (hl a List.mem_cons_self)]

end OnlinePacker

/-- First Fit as an online packer: the first bin with room. -/
@[expose] def firstFitPacker (C : ℕ) : OnlinePacker C :=
  ⟨fun _ bins a => bins.findIdx? fun b => b.sum + a ≤ C⟩

private theorem onlineInsert_map_succ (C a : ℕ) (o : Option ℕ) (b : List ℕ)
    (bs : List (List ℕ)) :
    onlineInsert C a (o.map (· + 1)) (b :: bs) = b :: onlineInsert C a o bs := by
  cases o <;> rfl

private theorem onlineInsert_findIdx? (C a : ℕ) :
    ∀ bins : List (List ℕ),
      onlineInsert C a (bins.findIdx? fun b => b.sum + a ≤ C) bins = firstFitInsert C a bins
  | [] => rfl
  | b :: bs => by
    rw [List.findIdx?_cons]
    by_cases h : b.sum + a ≤ C
    · simp [h, onlineInsert, firstFitInsert]
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, onlineInsert_map_succ,
        onlineInsert_findIdx? C a bs, firstFitInsert]

/-- The online packer `firstFitPacker` is First Fit. -/
theorem run_firstFitPacker (C : ℕ) (l : List ℕ) : (firstFitPacker C).run l = firstFit C l := by
  suffices ∀ hist bins, (firstFitPacker C).runFrom hist bins l =
      l.foldl (fun bins a => firstFitInsert C a bins) bins from this [] []
  induction l with
  | nil => intro _ _; rfl
  | cons a l ih =>
    intro hist bins
    rw [OnlinePacker.runFrom, List.foldl_cons, ← ih (hist ++ [a])]
    simp only [firstFitPacker, onlineInsert_findIdx?]

end Cslib.Algorithms.Lean.BinPacking
