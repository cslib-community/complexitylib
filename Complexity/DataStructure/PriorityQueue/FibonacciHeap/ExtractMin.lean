/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.Consolidation
public import Complexity.DataStructure.PriorityQueue.FibonacciHeap.DecreaseKey

/-!
# Fibonacci-heap `extractMin` over a record of named cells

`extractMin n` removes the minimum root `z` and consolidates
[Fredman and Tarjan][FredmanTarjan1987] [Cormen et al., Section 19.2][CLRS2009]:

1. `scatterList … true` walks `z`'s children along their sibling list, makes each an unmarked
   root, and `scatter`s it into the degree table `cons`. Scattering links the tree with the
   table's tree of equal degree (`link`, `linkAs`) until it reaches an empty slot.
2. `scatterList … false` does the same for the other roots, walking the root list from `z`'s
   right neighbour.
3. `gather` scans the table up to the largest degree placed, moving each tree to a new root list
   with `addRoot`, and empties the table.

The largest degree placed is a program value, returned by `scatter` and threaded through the
loops, so the record layout is the same as for the other operations.

The lemmas here only evaluate the programs: each `wp_*` lemma reads and writes cells, and cites
the forest mathematics of `Consolidation.lean` for what the phase does to the forest and the
table (`LinksAs.linked`, `Placing.place`, `Placing.collide`, `Scattering.unmark`,
`Scattering.step`, `Gathering.take`, `FibRawInv.detach`, `Detached.finish`). The loop lemmas are
inductions on the loops' fuel and counters.

Each link costs `14` operations and removes a tree; each scattered root costs at most `9` more;
each table slot costs at most `13`. With `credit = 24` per root, the roots' credits pay for
their scattering, and the amortized cost is at most `92 * (log₂ m + 1)` on a queue of `m`
handles (`extractCharge`), by the Fibonacci degree bound.

The module adapts Renfei Zhou's native formalization (`WordRAM/FibonacciHeap`, its
`Program.lean` and `Consolidate.lean`) to the record level: his extraction and consolidation
programs (`extractMinCode`, the scattering and gathering loops) and their forest and table
reasoning become the programs and loop lemmas here, and his table invariant `SlotInv` and its
lemmas are reused unchanged.

## Main definitions

* `linkAs`, `link`, `scatter`, `scatterList`, `gather`, `extractMin`: record programs.
* `extractCharge`: the amortized charge `92 * (Nat.log 2 m + 1)`.

## Main results

* `wp_link`, `wp_scatter`, `wp_scatterList`, `wp_gather`: linking and the three phases.
* `wp_extractMin`: `extractMin` implements `IndexedMinPQ.step` with amortized cost
  `extractCharge`.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 19.2][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-! ## Programs -/

/-- Make root `x` the newest child of root `u`. -/
def linkAs (u x : ℕ) : Prog Unit := do
  wr (.par x) (u + 1)
  let d ← rd (.deg u)
  if d = 0 then
    wr (.left x) x
    wr (.right x) x
    wr (.child u) (x + 1)
  else
    let c ← rd (.child u)
    spliceAfter (c - 1) x
  wr (.deg u) (d + 1)

/-- Link the roots `a` and `b` of equal degree: the one that precedes becomes the parent of the
other. Returns the new root. -/
def link (a b : ℕ) : Prog ℕ := do
  let ka ← rd (.key a)
  let kb ← rd (.key b)
  if IndexedMinPQ.RawPrioLT (b, kb) (a, ka) then
    linkAs b a
    pure b
  else
    linkAs a b
    pure a

/-- Place root `u` in the consolidation table: while the slot of its degree holds a root, empty
the slot, link the two roots and continue with the new root. Returns the largest degree placed,
at least `md`. `fuel` bounds the number of links. -/
def scatter : ℕ → ℕ → ℕ → Prog ℕ
  | 0, _, md => pure md
  | fuel + 1, u, md => do
    let d ← rd (.deg u)
    let c ← rd (.cons d)
    if c = 0 then
      wr (.cons d) (u + 1)
      pure (max md d)
    else
      wr (.cons d) 0
      let u' ← link u (c - 1)
      scatter fuel u' md

/-- Scatter the `k` roots of a list linked by `right` from `x`. With `prep`, each is first made an
unmarked root: these are the children of the extracted minimum. -/
def scatterList (fuel : ℕ) (prep : Bool) : ℕ → ℕ → ℕ → Prog ℕ
  | 0, _, md => pure md
  | k + 1, x, md => do
    let nxt ← rd (.right x)
    if prep then
      wr (.par x) 0
      let mk ← rd (.mark x)
      wr (.mark x) 0
      let c ← rd .numMarked
      wr .numMarked (c - mk)
    let md' ← scatter fuel x md
    scatterList fuel prep k nxt md'

/-- Move the table's roots at degrees `d, d + 1, …` (`k` slots) to the root list. -/
def gather : ℕ → ℕ → Prog Unit
  | 0, _ => pure ()
  | k + 1, d => do
    let c ← rd (.cons d)
    if c = 0 then gather k (d + 1)
    else
      wr (.cons d) 0
      addRoot (c - 1)
      gather k (d + 1)

/-- Remove and return the minimum of a heap on `n` handles: detach the minimum root `z`, scatter
its children and the other roots into the table, and gather the table into a new root list. -/
def extractMin (n : ℕ) : Prog (Option (Fin n × ℕ)) := do
  let m ← rd .minRoot
  if m = 0 then pure none
  else
    let kz ← rd (.key (m - 1))
    wr (.inHeap (m - 1)) 0
    let c ← rd .sz
    wr .sz (c - 1)
    let rz ← rd (.right (m - 1))
    let nr ← rd .numRoots
    let dz ← rd (.deg (m - 1))
    let cz ← rd (.child (m - 1))
    let md ← scatterList (n + 1) true dz (cz - 1) 0
    let md' ← scatterList (n + 1) false (nr - 1) rz md
    wr .minRoot 0
    wr .numRoots 0
    gather (md' + 1) 0
    pure (if h : m - 1 < n then some (⟨m - 1, h⟩, kz) else none)

/-- The amortized charge of `extractMin` on a queue with `m` handles. -/
def extractCharge (m : ℕ) : ℕ := 92 * (Nat.log 2 m + 1)


section Programs

variable {n w : ℕ}

/-- Making `x` the newest child of `u` evaluates to `LinksAs` in at most nine operations. -/
theorem wp_linkAs {g : Cell → ℕ} {u x : Fin n}
    (hch : (view n g).deg u ≠ 0 → ∃ c r : Fin n, (view n g).child u = c.val + 1 ∧
      (view n g).right c = r.val)
    (hdeg : (view n g).deg u + 1 ≤ n) (hfit : Fits w n) {Q : Unit → (Cell → ℕ) → ℕ → Prop}
    (hQ : ∀ g' t, t ≤ 9 → LinksAs (view n g) u x (view n g') → Q () g' t) :
    Record.wp (Cell.ok n) w (linkAs u x) Q g := by
  have hun := u.isLt
  have hxn := x.isLt
  have hd : g (.deg u) = (view n g).deg u := rfl
  by_cases h0 : (view n g).deg u = 0
  · simp only [linkAs, Record.wp_write_bind, Record.wp_read_bind, Record.wp_write,
      Function.update_apply, reduceCtorEq, ite_false, hd, h0, ite_true, Cell.ok]
    split_ands
    all_goals try first | omega | exact hfit.of_le (by omega)
    refine hQ _ _ (by omega) (Or.inl ⟨h0, ?_⟩)
    simp only [view_update_par, view_update_left, view_update_right, view_update_child,
      view_update_deg]
  · obtain ⟨c, r, hc, hr⟩ := hch h0
    have hc' : g (.child u) = c.val + 1 := hc
    simp only [linkAs, Record.wp_write_bind, Record.wp_read_bind,
      Function.update_apply, reduceCtorEq, ite_false, hd, h0, hc', Nat.add_sub_cancel, Cell.ok]
    refine ⟨⟨hxn, hfit.of_le (by omega)⟩, hun, hun, ?_⟩
    rw [Record.wp_bind]
    refine wp_spliceAfter (by simpa using hr) hfit ?_
    simp only [Record.wp_write, Cell.ok]
    split_ands
    all_goals try first | omega | exact hfit.of_le (by omega)
    refine hQ _ _ (by omega) (Or.inr ⟨c, r, h0, hc, hr, ?_⟩)
    simp only [view_update_par, view_update_left, view_update_right, view_update_deg]


/-- **Linking two roots** of equal degree evaluates, in at most eleven operations, to `Linked`:
the one that precedes becomes the parent. -/
theorem wp_link {g : Cell → ℕ} {T₁ T₂ : FHTree n} (h₁ : ValidRoot (view n g) none T₁)
    (h₂ : ValidRoot (view n g) none T₂) (hnd : (T₁.nodes ++ T₂.nodes).Nodup)
    (hdeg : T₁.deg = T₂.deg) (hdn : T₁.deg + 2 ≤ n) (hfit : Fits w n)
    {Q : ℕ → (Cell → ℕ) → ℕ → Prop}
    (hQ : ∀ g' t (T : FHTree n), t ≤ 11 → Linked (view n g) (view n g') T₁ T₂ T → Q T.root g' t) :
    Record.wp (Cell.ok n) w (link T₁.root T₂.root) Q g := by
  have hd₁ : (view n g).deg T₁.root + 1 ≤ n := by
    rw [ValidSubtree.deg_root h₁.1]; change T₁.deg + 1 ≤ n; omega
  have hd₂ : (view n g).deg T₂.root + 1 ≤ n := by
    rw [ValidSubtree.deg_root h₂.1]; change T₂.deg + 1 ≤ n; omega
  simp only [link, Record.wp_read_bind, Cell.ok]
  refine ⟨T₁.root.isLt, T₂.root.isLt, ?_⟩
  by_cases hlt : IndexedMinPQ.PrioLT (T₂.root, (view n g).key T₂.root)
      (T₁.root, (view n g).key T₁.root)
  · simp only [show IndexedMinPQ.RawPrioLT (↑T₂.root, g (.key ↑T₂.root))
      (↑T₁.root, g (.key ↑T₁.root)) from hlt, ite_true]
    rw [Record.wp_bind]
    exact wp_linkAs (ValidSubtree.exists_child h₂.1) hd₂ hfit fun g' t ht hl =>
      hQ g' _ (.node T₂.root (T₂.children ++ [T₁])) (by omega) ((LinksAs.linked h₂ h₁
        (List.perm_append_comm.nodup_iff.mp hnd) hdeg.symm hlt hl).symm hdeg)
  · simp only [show ¬IndexedMinPQ.RawPrioLT (↑T₂.root, g (.key ↑T₂.root))
      (↑T₁.root, g (.key ↑T₁.root)) from hlt, ite_false]
    rw [Record.wp_bind]
    have hlt₁ := (IndexedMinPQ.prioLT_or_prioLT_of_ne (fun e : T₁.root = T₂.root =>
      List.disjoint_of_nodup_append hnd T₁.root_mem_nodes (by rw [e]; exact T₂.root_mem_nodes))
        _ _).resolve_right hlt
    exact wp_linkAs (ValidSubtree.exists_child h₁.1) hd₁ hfit fun g' t ht hl =>
      hQ g' _ (.node T₁.root (T₁.children ++ [T₂])) (by omega)
        (LinksAs.linked h₁ h₂ hnd hdeg hlt₁ hl)

/-- **Scattering one root.** Placing a tree into the table consolidates its nodes and the
table's. Each link costs `14` operations and removes a tree, so the cost is at most `3` plus `14`
per tree removed. -/
theorem wp_scatter {sz : ℕ} {z : Fin n} (hfit : Fits w n) :
    ∀ (fuel : ℕ) {g : Cell → ℕ} {T : FHTree n} {slots : List (FHTree n)} {md : ℕ},
      Placing sz z (view n g) T slots md → slots.length < fuel →
      Record.wp (Cell.ok n) w (scatter fuel T.root md) (fun md' g' t => ∃ slots',
        Consolidated sz (view n g) (view n g') (forestNodes (T :: slots)) slots' md' ∧
        t + 14 * slots'.length ≤ 3 + 14 * (slots.length + 1)) g
  | 0, _, _, _, _, _, hfuel => absurd hfuel (Nat.not_lt_zero _)
  | fuel + 1, g, T, slots, md, h, hfuel => by
    have hdn := h.deg_bounds.2
    have hdeg : g (.deg T.root) = T.deg := ValidSubtree.deg_root h.valid.1
    simp only [scatter, Record.wp_read_bind, hdeg, Cell.ok]
    refine ⟨T.root.isLt, by omega, ?_⟩
    rcases h.table.lookup (d := T.deg) (by omega) with ⟨h0, hnone⟩ | ⟨i, hi, hdi, hci, hlen, hno⟩
    · have h0' : g (.cons T.deg) = 0 := h0
      simp only [h0', ite_true, Record.wp_write_bind, Record.wp_pure, Cell.ok, view_update_cons]
      exact ⟨⟨by omega, hfit.of_le T.root.isLt⟩, T :: slots, h.place hnone, by simp⟩
    · have hci' : g (.cons T.deg) = slots[i].root.val + 1 := hci
      simp only [hci', Nat.add_one_ne_zero, ite_false, Record.wp_write_bind, Nat.add_sub_cancel,
        Cell.ok]
      refine ⟨⟨by omega, fits_zero w⟩, ?_⟩
      rw [Record.wp_bind]
      obtain ⟨hT₁, hS₁, hnd, hnext⟩ := h.collide hi hdi hno (view_update_cons g 0 T.deg)
      refine wp_link hT₁ hS₁ hnd hdi.symm (by omega) hfit fun g₂ t₂ T' ht₂ hl => ?_
      obtain ⟨h₂, hback⟩ := hnext hl
      refine Record.wp_mono ?_ (wp_scatter hfit fuel h₂ (by omega))
      rintro md' g' t₃ ⟨slots', hc, ht₃⟩
      exact ⟨slots', hback hc, by omega⟩

/-- **Scattering a list of roots.** Walking the trees `rest` along their roots' `right` pointers
(each first made an unmarked root if `prep`) and scattering each consolidates them with the
table. Apart from links, each root costs `4` operations, or `9` with `prep`. -/
theorem wp_scatterList {sz : ℕ} {z : Fin n} (hfit : Fits w n) (prep : Bool) {fuel : ℕ}
    (hfuel : n < fuel) :
    ∀ (k : ℕ) {g : Cell → ℕ} {x : ℕ} {slots rest : List (FHTree n)} {md : ℕ},
      Scattering sz z prep (view n g) slots rest md → rest.length = k →
      (∀ y ∈ (rest.map FHTree.root).head?, x = y.val) →
      Record.wp (Cell.ok n) w (scatterList fuel prep k x md) (fun md' g' t => ∃ slots',
        Consolidated sz (view n g) (view n g') (forestNodes (slots ++ rest)) slots' md' ∧
        t + 14 * slots'.length ≤ (if prep then 9 else 4) * k + 14 * (slots.length + k)) g
  | 0, g, x, slots, rest, md, h, hlen, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [scatterList, Record.wp_pure]
    exact ⟨slots, h.done, by simp⟩
  | k + 1, g, x, slots, [], md, h, hlen, _ => by simp at hlen
  | k + 1, g, x, slots, T :: rest, md, h, hlen, hx => by
    obtain rfl : x = T.root.val := hx _ rfl
    -- After the optional preparation, scatter `T` and continue with `rest`.
    have cont : ∀ (g₁ : Cell → ℕ) (c₀ : ℕ), c₀ + 3 ≤ (if prep then 9 else 4) →
        Scattering sz z prep (view n g₁) slots (T :: rest) md → ValidRoot (view n g₁) none T →
        (∀ {st' slots' md'}, Consolidated sz (view n g₁) st' (forestNodes (slots ++ T :: rest))
          slots' md' → Consolidated sz (view n g) st' (forestNodes (slots ++ T :: rest)) slots'
            md') →
        Record.wp (Cell.ok n) w (scatter fuel T.root md >>= fun md' =>
          scatterList fuel prep k ((view n g).right T.root) md') (fun md' g' t => ∃ slots',
          Consolidated sz (view n g) (view n g') (forestNodes (slots ++ T :: rest)) slots' md' ∧
          t + c₀ + 14 * slots'.length ≤ (if prep then 9 else 4) * (k + 1) +
            14 * (slots.length + (k + 1))) g₁ := by
      intro g₁ c₀ hc₀ h₁ hT₁ hback₁
      rw [Record.wp_bind]
      have hP := h₁.placing hT₁
      refine Record.wp_mono ?_ (wp_scatter hfit fuel hP (by have := hP.length_lt; omega))
      rintro md₂ g₂ t₂ ⟨slots₂, hc₂, ht₂⟩
      obtain ⟨h₂, hback₂⟩ := h₁.step hc₂
      refine Record.wp_mono ?_ (wp_scatterList hfit prep hfuel k h₂ (by simpa using hlen)
        (RightChain.right_head h.chain))
      rintro md' g' t' ⟨slots', hc', ht'⟩
      refine ⟨slots', hback₁ (hback₂ hc'), ?_⟩
      rw [Nat.mul_succ]
      omega
    cases prep
    · simp only [scatterList, Record.wp_read_bind, Cell.ok, Bool.false_eq_true, ite_false]
      exact ⟨T.root.isLt, Record.wp_mono (fun _ _ _ ⟨sl, hc, ht⟩ => ⟨sl, hc, by
        simp only [Bool.false_eq_true, ite_false] at ht; omega⟩)
        (cont g 1 (by simp) h h.validRoot id)⟩
    · simp only [scatterList, Record.wp_read_bind, Record.wp_write_bind, Cell.ok, ite_true,
        Function.update_apply, reduceCtorEq, ite_false]
      have hxn := T.root.isLt
      have hnm_le : (view n g).numMarked ≤ n := h.numMarked ▸ markedCount_le_n _
      obtain ⟨h₁, hT₁, hsc₁⟩ := h.unmark
      have hv₁ : view n (Function.update (Function.update (Function.update g (.par T.root) 0)
          (.mark T.root) 0) .numMarked (g .numMarked - g (.mark T.root))) =
          unmarkState (view n g) T.root := by
        simp only [view_update_par, view_update_mark, view_update_numMarked]
        rfl
      refine ⟨hxn, ⟨hxn, fits_zero w⟩, hxn, ⟨hxn, fits_zero w⟩, trivial,
        ⟨trivial, hfit.of_le ((Nat.sub_le _ _).trans hnm_le)⟩, ?_⟩
      refine Record.wp_mono (fun _ _ _ ⟨sl, hc, ht⟩ => ⟨sl, hc, by
        simp only [ite_true] at ht; omega⟩) (cont _ 6 (by simp) (by rw [hv₁]; exact h₁)
        (by rw [hv₁]; exact hT₁) fun hc => hc.pre (by rw [hv₁]; exact hsc₁) (.refl _))

/-- **Gathering the table.** Scanning the slots `d, …, md` moves every tree of the table to the
root list, leaving the table empty, in at most `13` operations per slot. -/
theorem wp_gather {sz : ℕ} (hfit : Fits w n) :
    ∀ (k : ℕ) {g : Cell → ℕ} {d md : ℕ} {gs slots : List (FHTree n)},
      Gathering sz (view n g) gs slots md → (∀ T ∈ slots, d ≤ T.deg) → d + k = md + 1 →
      Record.wp (Cell.ok n) w (gather k d) (fun _ g' t => ∃ gs',
        Gathered (view n g) (view n g') (forestNodes (gs ++ slots)) gs' ∧
        gs'.length = gs.length + slots.length ∧ t ≤ 13 * k) g
  | 0, g, d, md, gs, slots, h, hge, hk => by
    obtain ⟨rfl, hG⟩ := h.done fun T hT => by have := hge T hT; omega
    simp only [gather, Record.wp_pure]
    exact ⟨gs, by simpa using hG, by simp, le_rfl⟩
  | k + 1, g, d, md, gs, slots, h, hge, hk => by
    have hdn : d ≤ n := SlotInv.le_n h.table (d := d) (by omega)
    simp only [gather, Record.wp_read_bind, Cell.ok]
    refine ⟨hdn, ?_⟩
    rcases h.table.lookup hdn with ⟨h0, hnone⟩ | ⟨i, hi, hdi, hci, hlen, hno⟩
    · have h0' : g (.cons d) = 0 := h0
      simp only [h0', ite_true]
      refine Record.wp_mono (fun _ g' t ⟨gs', hG, hl, ht⟩ => ⟨gs', hG, hl, by omega⟩)
        (wp_gather hfit k h (fun T hT => ?_) (by omega))
      have := hge T hT
      have := hnone T hT
      omega
    · have hci' : g (.cons d) = slots[i].root.val + 1 := hci
      simp only [hci', Nat.add_one_ne_zero, ite_false, Record.wp_write_bind, Nat.add_sub_cancel,
        Cell.ok]
      refine ⟨⟨hdn, fits_zero w⟩, ?_⟩
      rw [Record.wp_bind]
      obtain ⟨hroot, hnr, hnext⟩ := h.take hi hdi hdn hno (view_update_cons g 0 d)
      refine wp_addRoot hroot hfit (hfit.of_le hnr) fun g₂ t₂ ht₂ hadd => ?_
      obtain ⟨h₂, hback⟩ := hnext hadd
      refine Record.wp_mono (fun _ g' t ⟨gs', hG, hl, ht⟩ => ⟨gs', hback hG, by
        simp only [List.length_cons] at hl; omega, by omega⟩)
        (wp_gather hfit k h₂ (fun T hT => ?_) (by omega))
      have := hge T (List.mem_of_mem_eraseIdx hT)
      have := hno T hT
      omega

/-- **Extracting the minimum.** `extractMin n` implements `IndexedMinPQ.step` on `.extractMin`,
preserves the invariant, and costs at most `extractCharge` of the queue's size, amortized. -/
theorem wp_extractMin {K : ℕ} {g : Cell → ℕ} (hI : Inv n K g) (hfit : Fits w n) :
    Record.wp (Cell.ok n) w (extractMin n) (fun a g' t =>
      IndexedMinPQ.step (abs n g) .extractMin = (abs n g', a) ∧ Inv n K g' ∧
        t + potential n g' ≤
          extractCharge (IndexedMinPQ.dom (abs n g)).card + potential n g) g := by
  rcases minRoot_cases hI with h0 | ⟨m, -, hm, -⟩
  · have h0' : g .minRoot = 0 := h0
    simp only [extractMin, Record.wp_read_bind, h0', ite_true, Record.wp_pure, Cell.ok, true_and]
    refine ⟨?_, hI, by simp [extractCharge]; omega⟩
    simp [IndexedMinPQ.step, (FibRawInv.findMin_eq_none hI h0).2]
  obtain ⟨cs, E, hD⟩ := FibRawInv.detach hI hm
  have hm' : g .minRoot = m.val + 1 := hm
  have hmn := m.isLt
  have hdeg : g (.deg m) = cs.length := hD.deg
  have hnr : g .numRoots - 1 = E.length := by
    have := hD.numRoots
    change g .numRoots = _ at this
    omega
  have hszn : (view n g).sz ≤ n := by
    rw [hD.sz]; exact (Finset.card_le_univ _).trans (by simp)
  simp only [extractMin, Record.wp_read_bind, Record.wp_write_bind, hm', Nat.add_one_ne_zero,
    ite_false, Nat.add_sub_cancel, Function.update_apply, reduceCtorEq, Cell.ok, true_and,
    hdeg, hnr]
  refine ⟨hmn, ⟨hmn, fits_zero w⟩, hfit.of_le ((Nat.sub_le _ _).trans hszn), hmn, hmn, hmn, ?_⟩
  rw [Record.wp_bind]
  have hv₁ : view n (Function.update (Function.update g (.inHeap m) 0) .sz (g .sz - 1)) =
      detachState (view n g) m := by
    simp only [view_update_inHeap, view_update_sz]; rfl
  refine Record.wp_mono ?_ (wp_scatterList hfit true (Nat.lt_succ_self n) cs.length
    (by rw [hv₁]; exact hD.scatterChildren) rfl hD.child)
  rintro md₁ g₂ t₁ ⟨slots₁, hc₁, ht₁⟩
  rw [hv₁] at hc₁
  rw [Record.wp_bind]
  refine Record.wp_mono ?_ (wp_scatterList hfit false (Nat.lt_succ_self n) E.length
    (hD.scatterRoots hc₁) rfl hD.right)
  rintro md₂ g₃ t₂ ⟨slots₂, hc₂, ht₂⟩
  simp only [Record.wp_write_bind, Cell.ok, true_and]
  refine ⟨fits_zero w, fits_zero w, ?_⟩
  rw [Record.wp_bind]
  have hv₄ : view n (Function.update (Function.update g₃ .minRoot 0) .numRoots 0) =
      { view n g₃ with minRoot := 0, numRoots := 0 } := rfl
  refine Record.wp_mono ?_ (wp_gather hfit (md₂ + 1) (d := 0) (gs := [])
    (by rw [hv₄]; exact hD.gathering hc₁ hc₂) (fun _ _ => Nat.zero_le _) (by omega))
  rintro _ g' t₃ ⟨gs', hG, hlen, ht₃⟩
  rw [hv₄] at hG
  obtain ⟨hfin, hnm', hmd⟩ := hD.finish hc₁ hc₂ hG
  obtain ⟨hI', habs'⟩ := inv_of_fibRawInv hfin
  simp only [Record.wp_pure]
  refine ⟨?_, hI', ?_⟩
  · rw [habs']
    simp only [IndexedMinPQ.step, hD.findMin, hmn, dite_true, Prod.mk.injEq, Option.some.injEq,
      true_and]
    rfl
  · -- Links are paid by the trees they remove; what remains is logarithmic.
    have hF := SlotInv.length_le hc₂.table
    have hnr' := hG.numRoots
    have hdz := hD.degBound
    have hnr₀ := hD.numRoots
    simp only [ite_true, Bool.false_eq_true, ite_false, List.length_nil] at ht₁ ht₂ hlen
    simp only [potential, credit, extractCharge]
    omega

end Programs

end Cslib.DataStructure.PriorityQueue.FibonacciHeap
