/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.VCOne
public import CslibFrontier.Computability.PolyTime.List.BoundedEnumeration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Binary resource certification of VC-one closure enumeration

The explicit input is a unary width and a framed list of Boolean rows. A bounded prefix frontier
is extended in reverse coordinate order and tested by scanning unary/binary projections of the
original rows. Every frontier is capped at width plus one. The cap has no effect on VC-one input;
it gives polynomial machine resources even outside the promise. No cube, powerset, 2-SAT oracle
or supplied runtime is used. This is the closure stage of [ChenJiangZhu2027], Lemma 6.1 and
Theorem 1.3 (PDF pp. 18–20), using the existing pair-compatible-prefix variant of the proof.
The full table-to-counting-machine composition is a separate stage.
## Main results

* `enumerate_polytime`: uniform polynomial binary computation, including intermediate states.
* `enumerate_rows`: exact promised closure, computed without an oracle or cube traversal.
* `missing_rows`, `missing_length`: exact unwanted rows and the sharp table deficit.

-/

public section

namespace Cslib.Logic.PL.VCOne.BinaryClosure

open Turing.MultiTapeTM

/-- Unary width and explicit variable-length rows; malformed rows are also processed totally. -/
abbrev Input := ℕ × List (List Bool)
/-- Every listed row is stored literally, and the width includes unused coordinates. -/
@[expose] def encInput : Input ↪ List Bool := encPair encUnary (encList encBits)

/-- Scan the original rows for every ordered pair of processed coordinates, including diagonals. -/
@[expose] def compatible (rows : List (List Bool)) (todo : List ℕ) (y : List Bool) : Bool :=
  !rows.isEmpty && todo.all fun i => todo.all fun j => rows.any fun x =>
    (x.getD i false == y.getD i false) && (x.getD j false == y.getD j false)

/-- Full-width update. Fixing the output width prevents malformed state growth. -/
@[expose] def update (n i : ℕ) (b : Bool) (x : List Bool) : List Bool :=
  (List.range n).map fun j => if j = i then b else x.getD j false

/-- Extend each old prefix by each bit; scan projections and remove duplicate rows. -/
@[expose] def candidates (p : Input) (todo : List ℕ) (old : List (List Bool)) : List (List Bool) :=
  (((old.map (update p.1 (todo.headD 0) false)) ++
    (old.map (update p.1 (todo.headD 0) true))).filter
    (compatible p.2 todo)).dedup

/-- The cap is explicit executable control, rather than a supplied frontier budget. -/
@[expose] def next (p : Input) (todo : List ℕ) (old : List (List Bool)) : List (List Bool) :=
  (candidates p todo old).take (p.1 + 1)

/-- Empty tables have empty closure, even at zero coordinates. -/
@[expose] def initial (p : Input) : List (List Bool) :=
  if p.2.isEmpty then [] else [List.replicate p.1 false]

/-- A step retains the processed coordinates and the current bounded frontier. -/
@[expose] def step (p : Input) (state : List ℕ × List (List Bool)) (i : ℕ) :=
  (i :: state.1, next p (i :: state.1) state.2)

/-- Execute exactly one step for each declared coordinate, starting at the last coordinate. -/
@[expose] def enumerate (p : Input) : List (List Bool) :=
  ((List.range p.1).reverse.foldl (step p) ([], initial p)).2

private abbrev encState := encPair (encList encUnary) (encList encBits)

private theorem compatible_polytime : ComputableInPolyTime
    (fun p : (List (List Bool) × List ℕ) × List Bool => compatible p.1.1 p.1.2 p.2)
    (encPair (encPair (encList encBits) (encList encUnary)) encBits) encBool := by
  unfold compatible
  apply ComputableInPolyTime.bool_and' (by fun_prop)
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  apply ComputableInPolyTime.allWithInput (by fun_prop)
  apply ComputableInPolyTime.anyWithInput (by fun_prop)
  fun_prop

private theorem update_polytime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × (Bool × List Bool) => update p.1.1 p.1.2 p.2.1 p.2.2)
    (encPair (encPair encUnary encUnary) (encPair encBool encBits)) encBits := by
  have hm : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (Bool × List Bool) => update p.1.1 p.1.2 p.2.1 p.2.2)
      (encPair (encPair encUnary encUnary) (encPair encBool encBits)) (encList encBool) := by
    unfold update
    apply ComputableInPolyTime.mapWithInput (by fun_prop)
    fun_prop
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.listToBits).comp hm

private theorem candidates_polytime : ComputableInPolyTime
    (fun q : (Input × List ℕ) × List (List Bool) => candidates q.1.1 q.1.2 q.2)
    (encPair (encPair encInput (encList encUnary)) (encList encBits)) (encList encBits) := by
  have hu (b : Bool) : ComputableInPolyTime
      (fun q : (Input × List ℕ) × List (List Bool) =>
        q.2.map (update q.1.1.1 (q.1.2.headD 0) b))
      (encPair (encPair encInput (encList encUnary)) (encList encBits)) (encList encBits) := by
    apply ComputableInPolyTime.mapWithInput (by fun_prop)
    exact update_polytime.comp (show ComputableInPolyTime
      (fun p : ((Input × List ℕ) × List (List Bool)) × List Bool =>
        ((p.1.1.1.1, p.1.1.2.headD 0), (b, p.2))) _ _ from by
          unfold encInput; fun_prop)
  have hc : ComputableInPolyTime
      (fun q : ((Input × List ℕ) × List (List Bool)) × List Bool =>
        compatible q.1.1.1.2 q.1.1.2 q.2)
      (encPair (encPair (encPair encInput (encList encUnary)) (encList encBits)) encBits)
      encBool := by
    exact compatible_polytime.comp (show ComputableInPolyTime
      (fun q : ((Input × List ℕ) × List (List Bool)) × List Bool =>
        ((q.1.1.1.2, q.1.1.2), q.2)) _ _ from by unfold encInput; fun_prop)
  unfold candidates
  exact (Cslib.dedup_polytime encBits []).comp
    (ComputableInPolyTime.filterWithInput
      (ComputableInPolyTime.listAppend' (hu false) (hu true)) hc)

private theorem step_polytime : ComputableInPolyTime
    (fun q : (Input × (List ℕ × List (List Bool))) × ℕ => step q.1.1 q.1.2 q.2)
    (encPair (encPair encInput encState) encUnary) encState := by
  have hc := candidates_polytime.comp (show ComputableInPolyTime
    (fun q : (Input × (List ℕ × List (List Bool))) × ℕ =>
      ((q.1.1, q.2 :: q.1.2.1), q.1.2.2))
    (encPair (encPair encInput encState) encUnary)
    (encPair (encPair encInput (encList encUnary)) (encList encBits)) from by
      unfold encState; fun_prop)
  unfold step next encState
  exact (show ComputableInPolyTime
    (fun q : (Input × (List ℕ × List (List Bool))) × ℕ => q.2 :: q.1.2.1) _ _ from
      by fun_prop).prod (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listTakeWithInput hc.tidy (by unfold encInput; fun_prop)))

/-- Every stored frontier has at most width-plus-one full-width rows, on arbitrary input. -/
theorem next_size (p : Input) (todo : List ℕ) (old : List (List Bool)) :
    (next p todo old).length ≤ p.1 + 1 ∧
      ∀ row ∈ next p todo old, row.length = p.1 := by
  refine ⟨List.length_take_le _ _, ?_⟩
  intro row hr
  have h := List.mem_of_mem_take hr
  rcases List.mem_append.mp (List.mem_filter.mp (List.mem_dedup.mp h)).1 with hr | hr
  all_goals
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hr
    simp [update]

/-- The actual bounded prefix traversal has polynomial bit time and output/workspace cost on
all explicit inputs. The proof charges every projection scan, comparison, copy and loop step. -/
@[fun_prop] theorem enumerate_polytime :
    ComputableInPolyTime enumerate encInput (encList encBits) := by
  have hn : ComputableTidilyInPolyTime (fun p : Input => p.1) encInput encUnary := by
    unfold encInput; fun_prop
  have hz : ComputableTidilyInPolyTime (fun p : Input => List.replicate p.1 false)
      encInput encBits := ComputableTidilyInPolyTime.listToBits.comp
        (ComputableTidilyInPolyTime.replicate hn (.const false))
  have he : ComputableTidilyInPolyTime (fun p : Input => p.2.isEmpty) encInput encBool := by
    unfold encInput; fun_prop
  have hi : ComputableTidilyInPolyTime (fun p : Input => ([], initial p))
      encInput encState := by
    unfold initial encState encInput
    exact (ComputableTidilyInPolyTime.const []).prod
      (he.ite' (ComputableTidilyInPolyTime.const [])
        (ComputableTidilyInPolyTime.cons' hz (.const [])))
  have hnext (p : Input) (todo : List ℕ) (old : List (List Bool)) :
      (encList encBits (next p todo old)).length ≤ (p.1 + 1) * (2 * p.1 + 1) := by
    have h := next_size p todo old
    exact (length_encList_le encBits _ (by simpa only [encBits_apply] using
      fun row hr => (h.2 row hr).le)).trans (Nat.mul_le_mul_right _ h.1)
  have hfold := ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (encA := encUnary) (encL := encList encUnary) (encB := encState)
    (par := id) (list := fun p : Input => (List.range p.1).reverse)
    (init := fun p => ([], initial p)) (step := step)
    ComputableTidilyInPolyTime.id' (by fun_prop) hi step_polytime.tidy
    (growth := fun p => 4 * p.1 + 2 + (p.1 + 1) * (2 * p.1 + 1))
    ((((PolyBounded.const 4).mul hn.polyBounded).add (.const 2)).add
      ((hn.polyBounded.add (.const 1)).mul
        (((PolyBounded.const 2).mul hn.polyBounded).add (.const 1))))
    (by
      intro p state i hi
      have hn := List.mem_range.mp (List.mem_reverse.mp hi)
      have hf := hnext p (i :: state.1) state.2
      simp only [step, id_eq, encState, length_encPair, encList_cons, List.length_append,
        length_frame, encUnary_apply, List.length_replicate]
      omega)
  exact ComputableInPolyTime.of_tidy
    ((ComputableTidilyInPolyTime.snd _ _).comp hfold)

/-- Canonical explicit rows of a finite relation, without enumerating the ambient cube. -/
@[expose] def rows {n : ℕ} (R : Finset (Fin n → Bool)) : List (List Bool) :=
  (R.image List.ofFn).sort (· ≤ ·)

private theorem update_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) (b : Bool) :
    update n i.val b (List.ofFn x) = List.ofFn (Function.update x i b) := by
  apply List.ext_getElem
  · simp [update]
  · intro j hj hk
    simp only [update, List.length_map, List.length_range] at hj
    simp only [update, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [List.getD_ofFn x ⟨j, hj⟩ false]
    by_cases h : j = i.val
    · have he : (⟨j, hj⟩ : Fin n) = i := Fin.ext h
      simp [h]
    · have he : (⟨j, hj⟩ : Fin n) ≠ i := fun h' => h (congrArg Fin.val h')
      simp [h, he]

private theorem compatible_rows {n : ℕ} (R : Finset (Fin n → Bool))
    (todo : List (Fin n)) (y : Fin n → Bool) :
    compatible (rows R) (todo.map Fin.val) (List.ofFn y) =
      decide (PairCompatible R todo.toFinset y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [compatible, rows, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, List.any_eq_true, List.mem_map, Finset.mem_sort, Finset.mem_image,
    beq_iff_eq, decide_eq_true_eq, PairCompatible, List.mem_toFinset]
  constructor
  · rintro ⟨hne, h⟩
    have hr : R.Nonempty := by
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
      have hm : r ∈ R.image List.ofFn := by simpa only [Finset.mem_sort] using hr
      obtain ⟨x, hx, _⟩ := Finset.mem_image.mp hm
      exact ⟨x, hx⟩
    refine ⟨hr, fun i hi j hj => ?_⟩
    have hpat := h i.val ⟨i, hi, rfl⟩ j.val ⟨j, hj, rfl⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, hi', hj'⟩ := hpat
    exact ⟨x, hx, by simpa only [List.getD_ofFn] using hi',
      by simpa only [List.getD_ofFn] using hj'⟩
  · rintro ⟨hr, h⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hr
      intro he
      have hm : List.ofFn x ∈ (R.image List.ofFn).sort (· ≤ ·) := by simp [hx]
      rw [he] at hm
      contradiction
    · rintro i ⟨a, ha, rfl⟩ j ⟨b, hb, rfl⟩
      obtain ⟨x, hx, hi, hj⟩ := h a ha b hb
      exact ⟨List.ofFn x, ⟨x, hx, rfl⟩, by simpa only [List.getD_ofFn] using hi,
        by simpa only [List.getD_ofFn] using hj⟩

/-- Recursive view of the actual reverse-coordinate loop, retaining the same cap and scans. -/
@[expose] def frontier (p : Input) : List ℕ → List (List Bool)
  | [] => initial p
  | i :: todo => next p (i :: todo) (frontier p todo)

private theorem foldr_step (p : Input) (todo : List ℕ) :
    todo.foldr (fun i state => step p state i) ([], initial p) = (todo, frontier p todo) := by
  induction todo with
  | nil => rfl
  | cons i todo ih => rw [List.foldr_cons, ih]; rfl

/-- The executable loop and the recursive prefix view are the same program. -/
theorem enumerate_eq_frontier (p : Input) : enumerate p = frontier p (List.range p.1) := by
  unfold enumerate
  rw [List.foldl_reverse, foldr_step]

private theorem frontier_nodup (p : Input) (todo : List ℕ) : (frontier p todo).Nodup := by
  cases todo with
  | nil => simp only [frontier, initial]; split_ifs <;> simp
  | cons i todo => exact (List.nodup_dedup _).sublist (List.take_sublist _ _)

private theorem candidates_spec {n : ℕ} (R : Finset (Fin n → Bool)) (i : Fin n)
    (todo : List (Fin n)) (old : List (List Bool))
    (hold : old.toFinset = (prefixes R todo).image List.ofFn) :
    (candidates (n, rows R) ((i :: todo).map Fin.val) old).toFinset =
      (prefixes R (i :: todo)).image List.ofFn := by
  have hm (b : Bool) :
      (old.map (update n i.val b)).toFinset =
        ((prefixes R todo).image (fun x => Function.update x i b)).image List.ofFn := by
    rw [show (old.map (update n i.val b)).toFinset =
      old.toFinset.image (update n i.val b) from by ext row; simp,
      hold, Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact update_ofFn x i b
  let U := (prefixes R todo).image (fun x => Function.update x i false) ∪
    (prefixes R todo).image (fun x => Function.update x i true)
  have hraw : ((old.map (update n i.val false)) ++
      (old.map (update n i.val true))).toFinset = U.image List.ofFn := by
    rw [List.toFinset_append, hm, hm, ← Finset.image_union]
  change _ = (U.filter (PairCompatible R (i :: todo).toFinset)).image List.ofFn
  simp only [candidates, List.map_cons, List.headD_cons, List.toFinset_dedup,
    List.toFinset_filter]
  rw [hraw]
  ext row
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hp⟩
    exact ⟨x, ⟨hx, of_decide_eq_true (by simpa only [List.map_cons] using
      ((compatible_rows R (i :: todo) x).symm.trans hp))⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    simpa only [List.map_cons] using (compatible_rows R (i :: todo) x).trans
      (decide_eq_true hp)

/-- On VC-one tables the explicit cap never removes a prefix: the actual frontier equals the
proved pair-compatible prefix relation, including empty tables and zero-width relations. -/
theorem frontier_spec {n : ℕ} (R : Finset (Fin n → Bool)) (hR : DimensionOne R)
    (todo : List (Fin n)) (hn : todo.Nodup) :
    (frontier (n, rows R) (todo.map Fin.val)).toFinset =
      (prefixes R todo).image List.ofFn := by
  induction todo with
  | nil =>
    have hlen : (rows R).length = R.card := by
      simp [rows, Finset.card_image_of_injective _ List.ofFn_injective]
    have he : (rows R).isEmpty = true ↔ ¬ R.Nonempty := by
      simp only [List.isEmpty_iff, ← List.length_eq_zero_iff, hlen,
        Finset.card_eq_zero, Finset.not_nonempty_iff_eq_empty]
    simp only [List.map_nil, frontier, initial, prefixes]
    by_cases hr : R.Nonempty
    · have hb : (rows R).isEmpty = false := Bool.eq_false_iff.mpr (fun h => (he.mp h) hr)
      have hz : List.replicate n false = List.ofFn (fun _ : Fin n => false) := by simp
      simp only [hb, Bool.false_eq_true, ↓reduceIte, hr, List.toFinset_cons,
        List.toFinset_nil, Finset.image_singleton]
      exact congrArg (fun row => ({row} : Finset (List Bool))) hz
    · simp [he.mpr hr, hr]
  | cons i todo ih =>
    have hp := candidates_spec R i todo _ (ih hn.of_cons)
    have hc : (candidates (n, rows R) ((i :: todo).map Fin.val)
        (frontier (n, rows R) (todo.map Fin.val))).length ≤ n + 1 := by
      have hnd : (candidates (n, rows R) ((i :: todo).map Fin.val)
          (frontier (n, rows R) (todo.map Fin.val))).Nodup := List.nodup_dedup _
      rw [← List.toFinset_card_of_nodup hnd, hp]
      exact (Finset.card_image_le).trans (by simpa using prefixes_card R hR _ hn)
    simp only [List.map_cons] at hc hp
    simp only [List.map_cons, frontier, next]
    rw [List.take_of_length_le hc]
    exact hp

/-- Exact closure reconstruction by the polynomial machine, with no table-membership or
closure-output oracle. The only promise is the actual table's VC dimension bound. -/
theorem enumerate_rows {n : ℕ} (R : Finset (Fin n → Bool)) (hR : DimensionOne R) :
    (enumerate (n, rows R)).toFinset = (closure R).image List.ofFn := by
  rw [enumerate_eq_frontier]
  have hmap : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hmap, frontier_spec R hR _ (List.nodup_finRange n)]
  have hp : prefixes R (List.finRange n) = closure R := by
    rw [← listedClosure_eq]
    congr 1
    exact (Fin.sort_univ n).symm
  rw [hp]

/-- Extract only unwanted closure rows by scanning the explicit original table. -/
@[expose] def missing (p : Input) : List (List Bool) :=
  (enumerate p).filter fun y => decide (y ∉ p.2)

/-- Actual unwanted-point extraction charges membership tests and writing. -/
@[fun_prop] theorem missing_polytime :
    ComputableInPolyTime missing encInput (encList encBits) := by
  unfold missing
  exact ComputableInPolyTime.filterWithInput enumerate_polytime
    (ComputableInPolyTime.decide_not
      (ComputableInPolyTime.decide_mem (by unfold encInput; fun_prop) (by fun_prop)))

/-- The extracted rows are exactly the semantic closure difference. -/
theorem missing_rows {n : ℕ} (R : Finset (Fin n → Bool)) (hR : DimensionOne R) :
    (missing (n, rows R)).toFinset = (closure R \ R).image List.ofFn := by
  simp only [missing, List.toFinset_filter, enumerate_rows R hR]
  ext row
  simp only [Finset.mem_filter, Finset.mem_image, decide_eq_true_eq, rows,
    Finset.mem_sort, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hnot⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro h
    exact hnot ⟨x, h, rfl⟩
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, he⟩
    exact hn (List.ofFn_injective he ▸ hy)

/-- The actual unwanted-row list has the sharp Sauer deficit, not merely polynomial size. -/
theorem missing_length {n : ℕ} (R : Finset (Fin n → Bool)) (hR : DimensionOne R) :
    (missing (n, rows R)).length ≤ n + 1 - R.card := by
  have hnd : (missing (n, rows R)).Nodup := by
    unfold missing
    rw [enumerate_eq_frontier]
    exact (frontier_nodup (n, rows R) (List.range n)).filter _
  rw [← List.toFinset_card_of_nodup hnd, missing_rows R hR,
    Finset.card_image_of_injective _ List.ofFn_injective]
  simpa using separators_bound R hR

end Cslib.Logic.PL.VCOne.BinaryClosure
