/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BiTape
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Complexity.Computability.Machines.Turing.SingleTape.Decision
import Complexity.Computability.Machines.Turing.SingleTape.PostTuringMachine

/-!
# Crossing sequences of single-tape Turing machines

Hennie's crossing-sequence method for cslib's deterministic single-tape machines
`Cslib.Turing.SingleTapeTM`. A run is replayed in absolute coordinates: an `AbsCfg` records the
state, an integer head position and an integer-indexed tape, with input cell `i` at position
`i`. The boundary `k : ℤ` separates cells `k - 1` and `k`. The crossing sequence at `k` lists
the states entered by the steps whose head move crosses that boundary.

## Main definitions

* `Cslib.Turing.SingleTapeTM.AbsCfg`, `AbsCfg.next`, `AbsCfg.run`, `absInit`: the run in
  absolute coordinates. `Agrees` links it to the `BiTape` configurations of `tm.step`.
* `Cslib.Turing.SingleTapeTM.AbsCfg.scanned`: the symbol under the head.
* `Cslib.Turing.SingleTapeTM.AbsCfg.shift d`: translation by `d` cells.
* `Cslib.Turing.SingleTapeTM.AbsCfg.crossings k a t`: the crossing sequence at boundary `k`
  during the first `t` steps from `a`.

## Main results

* `Cslib.Turing.SingleTapeTM.absRun_of_relatesWithinSteps`: if `tm.step` leads from the initial
  configuration on `l` to a halted configuration within `t` steps, the absolute run from
  `absInit l` has halted at step `t` and scans the same symbol. `absRun_of_outputsWithinTime`
  and `DecidesByHeadInTime.absRun` specialize it.
* `Cslib.Turing.SingleTapeTM.AbsCfg.run_shift`, `AbsCfg.crossings_shift`: translation
  invariance of runs and crossing sequences.
* `Cslib.Turing.SingleTapeTM.AbsCfg.sum_length_crossings_le`: for any finite set of boundaries,
  the crossing sequences during `t` steps have total length at most `t`.
  `AbsCfg.length_crossings_le` is the single-boundary case, and `AbsCfg.crossings_eq_of_halted`
  says that steps after the halt add no crossings.
* `Cslib.Turing.SingleTapeTM.card_sub_pow_mul_le_sum_length`: pairwise distinct lists over a
  finite type `β`, indexed by `s`, have total length at least `(|s| - (|β| + 1) ^ L) L`. With
  `sum_length_crossings_le`, distinct crossing sequences force a long run.
* `Cslib.Turing.SingleTapeTM.cut_and_paste_run`: let the prefixes `u₁, u₂` be both empty or both
  nonempty. If the runs on `u₁ ++ v₁` and `u₂ ++ v₂` have halted by steps `t₁` and `t₂` with
  equal crossing sequences after the prefixes, then the run on `u₁ ++ v₂` has halted by step
  `t₁ + t₂`. On the left of `|u₁|` its crossing sequences are those of the first run, on the
  right those of the second run, shifted by `|u₂| - |u₁|`. It scans the final symbol of one of
  the two runs.
* `Cslib.Turing.SingleTapeTM.cut_and_paste`: the same for canonical outputs: any output of `tm`
  on `u₁ ++ v₂` begins with the first symbol of one of the two original outputs.

## References

* [F. C. Hennie, *One-tape, off-line Turing machine computations*][Hennie1965]
-/

public section

open Cslib Cslib.Turing Relation

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)

/-- Integer displacement of an optional head movement. -/
@[expose] def moveShift : Option _root_.Turing.Dir → ℤ
  | none => 0
  | some .left => -1
  | some .right => 1

/-- Configuration with an absolute head position and integer-indexed tape. -/
structure AbsCfg where
  /-- The current state; `none` once the machine has halted. -/
  state : Option tm.State
  /-- The absolute head position; input cell `i` sits at position `i`. -/
  pos : ℤ
  /-- The tape contents, indexed by absolute position. -/
  cells : ℤ → Option Symbol

variable {tm}

/-- One step in absolute coordinates; halted configurations are fixed. -/
@[expose] def AbsCfg.next (c : tm.AbsCfg) : tm.AbsCfg :=
  match c.state with
  | none => c
  | some q =>
    let r := tm.tr q (c.cells c.pos)
    ⟨r.2, c.pos + moveShift r.1.movement,
      Function.update c.cells c.pos r.1.symbol⟩

/-- The absolute configuration after `t` steps. -/
@[expose] def AbsCfg.run (c : tm.AbsCfg) (t : ℕ) : tm.AbsCfg := AbsCfg.next^[t] c

variable (tm) in
/-- Initial absolute configuration on input `l`: head at cell `0`. -/
@[expose] def absInit (l : List Symbol) : tm.AbsCfg :=
  ⟨some tm.q₀, 0, (BiTape.mk₁ l).read⟩

/-- A finite configuration agrees with an absolute one. -/
def Agrees (c : tm.Cfg) (a : tm.AbsCfg) : Prop :=
  c.state = a.state ∧ c.BiTape.Represents a.cells a.pos

theorem agrees_init (l : List Symbol) : Agrees (tm.initCfg l) (tm.absInit l) := by
  refine ⟨rfl, fun i => ?_⟩
  simp [absInit, initCfg]

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma dirToSign_cast (d : Option _root_.Turing.Dir) :
    ((dirToSign d : SignType) : ℤ) = moveShift d := by
  rcases d with _ | _ | _ <;> rfl

theorem Agrees.step {c c' : tm.Cfg} {a : tm.AbsCfg} (h : Agrees c a)
    (hs : tm.step c = some c') : Agrees c' a.next := by
  obtain ⟨hst, hrep⟩ := h
  rcases c with ⟨_ | q, t⟩
  · simp [SingleTapeTM.step] at hs
  · simp only at hst
    have hhead : t.head = a.cells a.pos := hrep.head
    rw [step_some, Option.some.injEq] at hs
    subst hs
    have hnext : a.next = ⟨(tm.tr q (a.cells a.pos)).2,
        a.pos + moveShift (tm.tr q (a.cells a.pos)).1.movement,
        Function.update a.cells a.pos (tm.tr q (a.cells a.pos)).1.symbol⟩ := by
      rcases a with ⟨s, p, f⟩
      simp only at hst
      subst hst
      rfl
    rw [hnext, hhead]
    refine ⟨rfl, ?_⟩
    rw [← biTape_step_dirToSign, ← dirToSign_cast]
    exact hrep.step _

lemma AbsCfg.next_of_none {a : tm.AbsCfg} (h : a.state = none) : a.next = a := by
  rcases a with ⟨s, p, f⟩
  simp only at h
  subst h
  rfl

lemma AbsCfg.run_succ (a : tm.AbsCfg) (t : ℕ) : a.run (t + 1) = a.next.run t :=
  Function.iterate_succ_apply _ _ _

lemma AbsCfg.run_zero (a : tm.AbsCfg) : a.run 0 = a := rfl

lemma AbsCfg.run_of_none {a : tm.AbsCfg} (h : a.state = none) (t : ℕ) : a.run t = a :=
  Function.iterate_fixed (next_of_none h) t

/-- The symbol under the head. -/
@[expose] def AbsCfg.scanned (c : tm.AbsCfg) : Option Symbol := c.cells c.pos

/-- Translate a configuration `d` cells to the right: the head and every cell move by `d`. -/
@[expose] def AbsCfg.shift (d : ℤ) (c : tm.AbsCfg) : tm.AbsCfg :=
  ⟨c.state, c.pos + d, fun p => c.cells (p - d)⟩

@[simp] lemma AbsCfg.shift_state (d : ℤ) (c : tm.AbsCfg) : (c.shift d).state = c.state := rfl

@[simp] lemma AbsCfg.shift_pos (d : ℤ) (c : tm.AbsCfg) : (c.shift d).pos = c.pos + d := rfl

@[simp] lemma AbsCfg.shift_cells (d : ℤ) (c : tm.AbsCfg) (p : ℤ) :
    (c.shift d).cells p = c.cells (p - d) := rfl

@[simp] lemma AbsCfg.scanned_shift (d : ℤ) (c : tm.AbsCfg) : (c.shift d).scanned = c.scanned := by
  simp [scanned]

/-- **Translation invariance.** Shifting commutes with a step. -/
lemma AbsCfg.next_shift (d : ℤ) (c : tm.AbsCfg) : (c.shift d).next = c.next.shift d := by
  rcases c with ⟨_ | q, p, f⟩
  · rfl
  · simp only [shift, next, add_sub_cancel_right]
    congr 1
    · exact add_right_comm _ _ _
    · funext x
      by_cases hx : x = p + d
      · subst hx
        simp
      · rw [Function.update_of_ne hx, Function.update_of_ne (fun h => hx (by omega))]

/-- **Translation invariance.** Shifting commutes with running. -/
lemma AbsCfg.run_shift (d : ℤ) (c : tm.AbsCfg) (t : ℕ) :
    (c.shift d).run t = (c.run t).shift d := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih => rw [run_succ, run_succ, next_shift, ih]

/-- Cell `p` lies to the left of the boundary between cells `k - 1` and `k`. -/
@[expose] def IsLeftOf (k p : ℤ) : Prop := p < k

instance (k p : ℤ) : Decidable (IsLeftOf k p) := Int.decLt _ _

/-- The crossing sequence at the boundary between cells `k - 1` and `k` during the first `t`
steps: the states entered by the steps that move the head across that boundary. -/
@[expose] def AbsCfg.crossings (k : ℤ) : tm.AbsCfg → ℕ → List (Option tm.State)
  | _, 0 => []
  | a, t + 1 =>
    if IsLeftOf k a.pos ↔ IsLeftOf k a.next.pos then a.next.crossings k t
    else a.next.state :: a.next.crossings k t

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma moveShift_bounds (d : Option _root_.Turing.Dir) :
    -1 ≤ moveShift d ∧ moveShift d ≤ 1 := by
  rcases d with _ | _ | _ <;> decide

private lemma AbsCfg.next_pos_bounds (a : tm.AbsCfg) :
    -1 ≤ a.next.pos - a.pos ∧ a.next.pos - a.pos ≤ 1 := by
  rcases a with ⟨_ | q, p, f⟩
  · exact ⟨by simp [next], by simp [next]⟩
  · simp only [next, add_sub_cancel_left]
    exact moveShift_bounds _

/-- One step crosses at most one boundary. -/
private lemma AbsCfg.card_filter_cross_le (a : tm.AbsCfg) (K : Finset ℤ) :
    (K.filter fun k => ¬(IsLeftOf k a.pos ↔ IsLeftOf k a.next.pos)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro i hi j hj
  rw [Finset.mem_filter] at hi hj
  unfold IsLeftOf at hi hj
  have h := a.next_pos_bounds
  by_cases h1 : a.pos < i <;> by_cases h2 : a.next.pos < i <;>
    by_cases h3 : a.pos < j <;> by_cases h4 : a.next.pos < j <;>
    simp only [h1, h2, h3, h4, iff_true, iff_false, not_true,
      not_false_eq_true, and_true, and_false] at hi hj <;> omega

lemma AbsCfg.length_crossings_succ (a : tm.AbsCfg) (k : ℤ) (t : ℕ) :
    (a.crossings k (t + 1)).length =
      (if IsLeftOf k a.pos ↔ IsLeftOf k a.next.pos then 0 else 1) +
        (a.next.crossings k t).length := by
  simp only [crossings]
  split_ifs <;> simp [Nat.add_comm]

/-- **Sum lemma.** The crossing sequences at any finite set of boundaries have total length at
most the number of steps. -/
theorem AbsCfg.sum_length_crossings_le (K : Finset ℤ) (a : tm.AbsCfg) (t : ℕ) :
    ∑ k ∈ K, (a.crossings k t).length ≤ t := by
  induction t generalizing a with
  | zero => simp [crossings]
  | succ t ih =>
    simp only [length_crossings_succ, Finset.sum_add_distrib]
    have h1 : (∑ k ∈ K, if IsLeftOf k a.pos ↔ IsLeftOf k a.next.pos then 0 else 1) ≤ 1 := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul,
        mul_one]
      exact a.card_filter_cross_le K
    have h2 := ih a.next
    omega

lemma AbsCfg.crossings_of_none {a : tm.AbsCfg} (h : a.state = none) (k : ℤ) (t : ℕ) :
    a.crossings k t = [] := by
  induction t with
  | zero => rfl
  | succ t ih => simp [crossings, next_of_none h, ih]

/-- A crossing sequence is no longer than the number of steps. -/
lemma AbsCfg.length_crossings_le (a : tm.AbsCfg) (k : ℤ) (t : ℕ) :
    (a.crossings k t).length ≤ t := by
  simpa using a.sum_length_crossings_le {k} t

omit [Inhabited Symbol] [Fintype Symbol] in
/-- At most `(|β| + 1) ^ L` elements have pairwise distinct images that are lists of length
`< L` over `β`. -/
private lemma card_filter_length_lt_le {ι β : Type*} [Fintype β] {s : Finset ι}
    {f : ι → List β} (hf : Set.InjOn f s) (L : ℕ) :
    (s.filter fun x => (f x).length < L).card ≤ (Fintype.card β + 1) ^ L := by
  classical
  have h := Finset.card_le_card_of_injOn (s := s.filter fun x => (f x).length < L)
    (t := (Finset.univ : Finset (Fin L → Option β))) (fun x j => (f x)[(j : ℕ)]?)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
  · simpa [Fintype.card_option] using h
  · intro x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
    refine hf hx.1 hy.1 (List.ext_getElem? fun j => ?_)
    by_cases hj : j < L
    · exact congrFun hxy ⟨j, hj⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

omit [Inhabited Symbol] [Fintype Symbol] in
/-- **Counting distinct crossing sequences.** If `f` takes pairwise distinct values on `s`, lists
over a finite type `β`, then all but `(|β| + 1) ^ L` of them have length at least `L`, so their
total length is at least `(|s| - (|β| + 1) ^ L) L`. -/
theorem card_sub_pow_mul_le_sum_length {ι β : Type*} [Fintype β] {s : Finset ι}
    {f : ι → List β} (hf : Set.InjOn f s) (L : ℕ) :
    (s.card - (Fintype.card β + 1) ^ L) * L ≤ ∑ x ∈ s, (f x).length := by
  classical
  have hbad := card_filter_length_lt_le hf L
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun x => (f x).length < L)
  calc (s.card - (Fintype.card β + 1) ^ L) * L
      ≤ (s.filter fun x => ¬ (f x).length < L).card * L := Nat.mul_le_mul_right _ (by omega)
    _ ≤ ∑ x ∈ s.filter fun x => ¬ (f x).length < L, (f x).length := by
        rw [← smul_eq_mul]
        exact Finset.card_nsmul_le_sum _ _ _ fun x hx => by
          rw [Finset.mem_filter] at hx
          omega
    _ ≤ ∑ x ∈ s, (f x).length :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
          Nat.zero_le _

/-- **Translation invariance.** The shifted run crosses the shifted boundary in the same
states. -/
lemma AbsCfg.crossings_shift (d k : ℤ) (c : tm.AbsCfg) (t : ℕ) :
    (c.shift d).crossings (k + d) t = c.crossings k t := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    have hl (p : ℤ) : IsLeftOf (k + d) (p + d) ↔ IsLeftOf k p := add_lt_add_iff_right d
    simp only [crossings, next_shift, shift_pos, shift_state, hl, ih]

/-- One step from `a` to `a.next` that stays strictly left of `k` crosses no boundary
`k' ≥ k`. -/
private lemma AbsCfg.crossings_succ_of_left {k k' : ℤ} (hk : k ≤ k') {a : tm.AbsCfg} {t : ℕ}
    (h1 : IsLeftOf k a.pos) (h2 : IsLeftOf k a.next.pos) :
    a.crossings k' (t + 1) = a.next.crossings k' t := by
  have hc : IsLeftOf k' a.pos ↔ IsLeftOf k' a.next.pos := by
    unfold IsLeftOf at *
    exact ⟨fun _ => by omega, fun _ => by omega⟩
  simp only [crossings, hc, ite_true]

/-- One step from `a` to `a.next` that stays at or right of `k` crosses no boundary
`k' ≤ k`. -/
private lemma AbsCfg.crossings_succ_of_right {k k' : ℤ} (hk : k' ≤ k) {a : tm.AbsCfg} {t : ℕ}
    (h1 : ¬ IsLeftOf k a.pos) (h2 : ¬ IsLeftOf k a.next.pos) :
    a.crossings k' (t + 1) = a.next.crossings k' t := by
  have hc : IsLeftOf k' a.pos ↔ IsLeftOf k' a.next.pos := by
    unfold IsLeftOf at *
    exact ⟨fun _ => by omega, fun _ => by omega⟩
  simp only [crossings, hc, ite_true]

/-- A run that starts left of `k` and never crosses `k` crosses no boundary `k' ≥ k`. -/
private lemma AbsCfg.crossings_eq_nil_of_left {k k' : ℤ} (hk : k ≤ k') :
    ∀ {t : ℕ} {a : tm.AbsCfg}, IsLeftOf k a.pos → a.crossings k t = [] →
      a.crossings k' t = [] := by
  intro t
  induction t with
  | zero => intro a _ _; rfl
  | succ t ih =>
    intro a ha h
    simp only [crossings] at h
    split_ifs at h with hc
    rw [crossings_succ_of_left hk ha (hc.mp ha)]
    exact ih (hc.mp ha) h

/-- A run that starts at or right of `k` and never crosses `k` crosses no boundary `k' ≤ k`. -/
private lemma AbsCfg.crossings_eq_nil_of_right {k k' : ℤ} (hk : k' ≤ k) :
    ∀ {t : ℕ} {a : tm.AbsCfg}, ¬ IsLeftOf k a.pos → a.crossings k t = [] →
      a.crossings k' t = [] := by
  intro t
  induction t with
  | zero => intro a _ _; rfl
  | succ t ih =>
    intro a ha h
    simp only [crossings] at h
    split_ifs at h with hc
    rw [crossings_succ_of_right hk ha (not_congr hc |>.mp ha)]
    exact ih (not_congr hc |>.mp ha) h

/-- Two runs whose first steps have the same endpoints and target state, and whose remaining
crossing sequences at `k` agree, have equal crossing sequences at `k`. -/
private lemma AbsCfg.crossings_succ_congr {k : ℤ} {C A : tm.AbsCfg} {t s : ℕ}
    (hp : C.pos = A.pos) (hp' : C.next.pos = A.next.pos) (hs : C.next.state = A.next.state)
    (h : C.next.crossings k t = A.next.crossings k s) :
    C.crossings k (t + 1) = A.crossings k (s + 1) := by
  simp only [crossings, hp, hp', hs, h]

private lemma AbsCfg.next_cells_of_ne (a : tm.AbsCfg) {p : ℤ} (hp : p ≠ a.pos) :
    a.next.cells p = a.cells p := by
  rcases a with ⟨_ | q, i, f⟩
  · rfl
  · exact Function.update_of_ne hp _ _

lemma AbsCfg.run_of_crossings_nil {k : ℤ} {t : ℕ} :
    ∀ {a : tm.AbsCfg}, a.crossings k t = [] →
      (IsLeftOf k (a.run t).pos ↔ IsLeftOf k a.pos) ∧
        ∀ p, (IsLeftOf k p ↔ ¬ IsLeftOf k a.pos) → (a.run t).cells p = a.cells p := by
  induction t with
  | zero => intro a _; exact ⟨Iff.rfl, fun _ _ => rfl⟩
  | succ t ih =>
    intro a h
    simp only [crossings] at h
    split_ifs at h with hc
    obtain ⟨h1, h2⟩ := ih h
    rw [run_succ]
    refine ⟨h1.trans hc.symm, fun p hp => ?_⟩
    rw [h2 p (hp.trans (not_congr hc)), next_cells_of_ne]
    rintro rfl
    exact (iff_not_self hp).elim

/-- Crossing sequences of consecutive time intervals concatenate. -/
lemma AbsCfg.crossings_add (k : ℤ) (j : ℕ) :
    ∀ (a : tm.AbsCfg) (t : ℕ),
      a.crossings k (j + t) = a.crossings k j ++ (a.run j).crossings k t := by
  induction j with
  | zero => intro a t; simp [crossings, run_zero]
  | succ j ih =>
    intro a t
    rw [Nat.add_right_comm, run_succ]
    simp only [crossings]
    split_ifs <;> simp [ih]

/-- The first crossing of a nonempty crossing sequence. -/
private lemma AbsCfg.exists_first_crossing {k : ℤ} {s : Option tm.State}
    {σ : List (Option tm.State)} :
    ∀ {T : ℕ} {a : tm.AbsCfg}, a.crossings k T = s :: σ →
      ∃ j, j < T ∧ a.crossings k j = [] ∧
        ¬(IsLeftOf k (a.run j).pos ↔ IsLeftOf k (a.run j).next.pos) ∧
        (a.run j).next.state = s ∧ (a.run j).next.crossings k (T - j - 1) = σ := by
  intro T
  induction T with
  | zero => intro a h; simp [crossings] at h
  | succ T ih =>
    intro a h
    simp only [crossings] at h
    split_ifs at h with hc
    · obtain ⟨j, hj, h0, h1, h2, h3⟩ := ih h
      refine ⟨j + 1, by omega, ?_, ?_, ?_, ?_⟩
      · simp only [crossings, hc, ite_true, h0]
      · rwa [run_succ]
      · rwa [run_succ]
      · rw [run_succ]
        convert h3 using 2
        omega
    · obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨0, by omega, rfl, hc, rfl, rfl⟩

/-- `C` is the splice at boundary `k` of the left part of `L` and the right part of `R`: its
cells come from `L` left of the boundary and from `R` right of it, all three heads are on the
same side, and `C` follows whichever of `L`, `R` owns that side. -/
private structure Splice (k : ℤ) (L R C : tm.AbsCfg) : Prop where
  cells : ∀ p, C.cells p = if IsLeftOf k p then L.cells p else R.cells p
  left_side : IsLeftOf k L.pos ↔ IsLeftOf k C.pos
  right_side : IsLeftOf k R.pos ↔ IsLeftOf k C.pos
  follow_left : IsLeftOf k C.pos → C.state = L.state ∧ C.pos = L.pos
  follow_right : ¬ IsLeftOf k C.pos → C.state = R.state ∧ C.pos = R.pos

/-- Two configurations with the same state, head and scanned symbol take the same step. -/
private lemma AbsCfg.next_agree {A C : tm.AbsCfg} (hs : C.state = A.state) (hp : C.pos = A.pos)
    (hc : C.cells C.pos = A.cells A.pos) :
    C.next.state = A.next.state ∧ C.next.pos = A.next.pos ∧
      C.next.cells C.pos = A.next.cells A.pos := by
  rcases A with ⟨sa, pa, fa⟩
  rcases C with ⟨sc, pc, fc⟩
  simp only at hs hp hc
  subst hs hp
  rcases sc with _ | q
  · exact ⟨rfl, rfl, hc⟩
  · simp only [next, hc, Function.update_self]
    exact ⟨trivial, trivial, trivial⟩

/-- A step of the left run that stays left is mirrored by the splice. -/
private lemma Splice.next_left {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C)
    (hC : IsLeftOf k C.pos)
    (hn : IsLeftOf k L.next.pos) : Splice k L.next R C.next := by
  obtain ⟨hs, hp⟩ := h.follow_left hC
  have hcell : C.cells C.pos = L.cells L.pos := by rw [h.cells, ite_eq_left hC, hp]
  obtain ⟨hs', hp', hc'⟩ := AbsCfg.next_agree hs hp hcell
  refine ⟨fun p => ?_, by rw [hp'], ?_, fun _ => ⟨hs', hp'⟩, fun h' => (h' (hp' ▸ hn)).elim⟩
  · by_cases hpc : p = C.pos
    · subst hpc
      rw [ite_eq_left hC, hc', hp]
    · rw [AbsCfg.next_cells_of_ne _ hpc, h.cells]
      split_ifs
      · rw [AbsCfg.next_cells_of_ne _ (hp ▸ hpc)]
      · rfl
  · rw [hp']
    exact ⟨fun _ => hn, fun _ => h.right_side.mpr hC⟩

/-- A step of the right run that stays right is mirrored by the splice. -/
private lemma Splice.next_right {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C)
    (hC : ¬ IsLeftOf k C.pos) (hn : ¬ IsLeftOf k R.next.pos) : Splice k L R.next C.next := by
  obtain ⟨hs, hp⟩ := h.follow_right hC
  have hcell : C.cells C.pos = R.cells R.pos := by rw [h.cells, ite_eq_right hC, hp]
  obtain ⟨hs', hp', hc'⟩ := AbsCfg.next_agree hs hp hcell
  refine ⟨fun p => ?_, ?_, by rw [hp'], fun h' => (hn (hp' ▸ h')).elim, fun _ => ⟨hs', hp'⟩⟩
  · by_cases hpc : p = C.pos
    · subst hpc
      rw [ite_eq_right hC, hc', hp]
    · rw [AbsCfg.next_cells_of_ne _ hpc, h.cells]
      split_ifs
      · rfl
      · rw [AbsCfg.next_cells_of_ne _ (hp ▸ hpc)]
  · rw [hp']
    exact ⟨fun h' => (hC (h.left_side.mp h')).elim, fun h' => (hn h').elim⟩

/-- A step crossing the boundary rightward goes from cell `k - 1` to cell `k`. -/
private lemma AbsCfg.cross_right {k : ℤ} {a : tm.AbsCfg} (h1 : IsLeftOf k a.pos)
    (h2 : ¬ IsLeftOf k a.next.pos) : a.pos = k - 1 ∧ a.next.pos = k := by
  have h := a.next_pos_bounds
  unfold IsLeftOf at h1 h2
  omega

/-- A step crossing the boundary leftward goes from cell `k` to cell `k - 1`. -/
private lemma AbsCfg.cross_left {k : ℤ} {a : tm.AbsCfg} (h1 : ¬ IsLeftOf k a.pos)
    (h2 : IsLeftOf k a.next.pos) : a.pos = k ∧ a.next.pos = k - 1 := by
  have h := a.next_pos_bounds
  unfold IsLeftOf at h1 h2
  omega

/-- Hand-off to the right: when the left run crosses rightward, the splice continues with the
right run advanced through its matching crossing. -/
private lemma Splice.next_cross_right {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C)
    (hC : IsLeftOf k C.pos) (hn : ¬ IsLeftOf k L.next.pos) {j : ℕ} (h0 : R.crossings k j = [])
    (hx : ¬(IsLeftOf k (R.run j).pos ↔ IsLeftOf k (R.run j).next.pos))
    (hst : (R.run j).next.state = L.next.state) : Splice k L.next (R.run j).next C.next := by
  obtain ⟨hs, hp⟩ := h.follow_left hC
  have hcell : C.cells C.pos = L.cells L.pos := by rw [h.cells, ite_eq_left hC, hp]
  obtain ⟨hs', hp', hc'⟩ := AbsCfg.next_agree hs hp hcell
  have hL : IsLeftOf k L.pos := h.left_side.mpr hC
  obtain ⟨-, hLk⟩ := AbsCfg.cross_right hL hn
  obtain ⟨hRside, hRcells⟩ := AbsCfg.run_of_crossings_nil h0
  have hR' : IsLeftOf k (R.run j).pos := hRside.mpr (h.right_side.mpr hC)
  obtain ⟨hR'k, hR'nk⟩ := AbsCfg.cross_right hR' (fun h' => hx ⟨fun _ => h', fun _ => hR'⟩)
  refine ⟨fun p => ?_, by rw [hp'], by rw [hR'nk, hp', hLk], fun h' => (hn (hp' ▸ h')).elim,
    fun _ => ⟨hs'.trans hst.symm, hp'.trans (hLk.trans hR'nk.symm)⟩⟩
  by_cases hpc : p = C.pos
  · subst hpc
    rw [ite_eq_left hC, hc', hp]
  · rw [AbsCfg.next_cells_of_ne _ hpc, h.cells]
    by_cases hpl : IsLeftOf k p
    · rw [ite_eq_left hpl, ite_eq_left hpl, AbsCfg.next_cells_of_ne _ (hp ▸ hpc)]
    · have hne : p ≠ (R.run j).pos := by
        rintro rfl
        exact hpl hR'
      rw [ite_eq_right hpl, ite_eq_right hpl, AbsCfg.next_cells_of_ne _ hne,
        hRcells p ⟨fun h' => (hpl h').elim, fun h' => (h' (h.right_side.mpr hC)).elim⟩]

/-- Hand-off to the left: when the right run crosses leftward, the splice continues with the
left run advanced through its matching crossing. -/
private lemma Splice.next_cross_left {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C)
    (hC : ¬ IsLeftOf k C.pos) (hn : IsLeftOf k R.next.pos) {j : ℕ} (h0 : L.crossings k j = [])
    (hx : ¬(IsLeftOf k (L.run j).pos ↔ IsLeftOf k (L.run j).next.pos))
    (hst : (L.run j).next.state = R.next.state) : Splice k (L.run j).next R.next C.next := by
  obtain ⟨hs, hp⟩ := h.follow_right hC
  have hcell : C.cells C.pos = R.cells R.pos := by rw [h.cells, ite_eq_right hC, hp]
  obtain ⟨hs', hp', hc'⟩ := AbsCfg.next_agree hs hp hcell
  have hR : ¬ IsLeftOf k R.pos := fun h' => hC (h.right_side.mp h')
  obtain ⟨-, hRk⟩ := AbsCfg.cross_left hR hn
  obtain ⟨hLside, hLcells⟩ := AbsCfg.run_of_crossings_nil h0
  have hL : ¬ IsLeftOf k L.pos := fun h' => hC (h.left_side.mp h')
  have hL' : ¬ IsLeftOf k (L.run j).pos := fun h' => hL (hLside.mp h')
  have hL'n : IsLeftOf k (L.run j).next.pos := by
    by_contra h'
    exact hx ⟨fun h'' => (hL' h'').elim, fun h'' => (h' h'').elim⟩
  obtain ⟨-, hL'nk⟩ := AbsCfg.cross_left hL' hL'n
  refine ⟨fun p => ?_, by rw [hL'nk, hp', hRk], by rw [hp'],
    fun _ => ⟨hs'.trans hst.symm, hp'.trans (hRk.trans hL'nk.symm)⟩,
    fun h' => (h' (hp' ▸ hn)).elim⟩
  by_cases hpc : p = C.pos
  · subst hpc
    rw [ite_eq_right hC, hc', hp]
  · rw [AbsCfg.next_cells_of_ne _ hpc, h.cells]
    by_cases hpl : IsLeftOf k p
    · have hne : p ≠ (L.run j).pos := by
        rintro rfl
        exact hL' hpl
      rw [ite_eq_left hpl, ite_eq_left hpl, AbsCfg.next_cells_of_ne _ hne,
        hLcells p ⟨fun _ => hL, fun _ => hpl⟩]
    · rw [ite_eq_right hpl, ite_eq_right hpl, AbsCfg.next_cells_of_ne _ (hp ▸ hpc)]

private lemma AbsCfg.run_split (a : tm.AbsCfg) {j T : ℕ} (hj : j < T) :
    a.run T = (a.run j).next.run (T - j - 1) := by
  rw [← run_succ, run, run, run, ← Function.iterate_add_apply]
  congr 1
  omega

/-- Split a crossing sequence after step `j`, keeping step `j + 1` in the second part. -/
private lemma AbsCfg.crossings_split (a : tm.AbsCfg) {j T : ℕ} (hj : j < T) (k : ℤ) :
    a.crossings k T = a.crossings k j ++ (a.run j).crossings k (T - j - 1 + 1) := by
  rw [← crossings_add]
  congr 1
  omega

/-- While the splice follows the left run, its next step agrees with the left run's. -/
private lemma Splice.next_agree_left {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C)
    (hC : IsLeftOf k C.pos) : C.next.state = L.next.state ∧ C.next.pos = L.next.pos := by
  obtain ⟨hs, hp⟩ := h.follow_left hC
  have hcell : C.cells C.pos = L.cells L.pos := by rw [h.cells, ite_eq_left hC, hp]
  obtain ⟨hs', hp', -⟩ := AbsCfg.next_agree hs hp hcell
  exact ⟨hs', hp'⟩

/-- While the splice follows the right run, its next step agrees with the right run's. -/
private lemma Splice.next_agree_right {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C)
    (hC : ¬ IsLeftOf k C.pos) : C.next.state = R.next.state ∧ C.next.pos = R.next.pos := by
  obtain ⟨hs, hp⟩ := h.follow_right hC
  have hcell : C.cells C.pos = R.cells R.pos := by rw [h.cells, ite_eq_right hC, hp]
  obtain ⟨hs', hp', -⟩ := AbsCfg.next_agree hs hp hcell
  exact ⟨hs', hp'⟩

/-- Advancing the parked right run through steps without crossings preserves the splice. -/
private lemma Splice.run_right_of_nil {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C)
    (hC : IsLeftOf k C.pos) {t : ℕ} (h0 : R.crossings k t = []) : Splice k L (R.run t) C := by
  obtain ⟨hside, hcells⟩ := AbsCfg.run_of_crossings_nil h0
  have hR : IsLeftOf k R.pos := h.right_side.mpr hC
  refine ⟨fun p => ?_, h.left_side, ⟨fun _ => hC, fun _ => hside.mpr hR⟩, h.follow_left,
    fun h' => (h' hC).elim⟩
  rw [h.cells]
  by_cases hp : IsLeftOf k p
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp, hcells p ⟨fun h' => (hp h').elim, fun h' => (h' hR).elim⟩]

/-- Advancing the parked left run through steps without crossings preserves the splice. -/
private lemma Splice.run_left_of_nil {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C)
    (hC : ¬ IsLeftOf k C.pos) {t : ℕ} (h0 : L.crossings k t = []) : Splice k (L.run t) R C := by
  obtain ⟨hside, hcells⟩ := AbsCfg.run_of_crossings_nil h0
  have hL : ¬ IsLeftOf k L.pos := fun h' => hC (h.left_side.mp h')
  refine ⟨fun p => ?_, ⟨fun h' => (hL (hside.mp h')).elim, fun h' => (hC h').elim⟩,
    h.right_side, fun h' => (hC h').elim, h.follow_right⟩
  rw [h.cells]
  by_cases hp : IsLeftOf k p
  · rw [ite_eq_left hp, ite_eq_left hp, hcells p ⟨fun _ => hL, fun _ => hp⟩]
  · rw [ite_eq_right hp, ite_eq_right hp]

/-- **Cut-and-paste, absolute form.** If the left and right runs halt within `T₁` and `T₂`
steps with equal crossing sequences at `k`, the splice halts within `T₁ + T₂` steps and its
final configuration is the splice of the two final ones. At every boundary `k' ≤ k` the splice
has the crossing sequence of the left run, and at every boundary `k' ≥ k` that of the right
run. -/
private theorem Splice.run_halts {k : ℤ} :
    ∀ (n : ℕ) {L R C : tm.AbsCfg} {T₁ T₂ : ℕ}, T₁ + T₂ ≤ n → Splice k L R C →
      (L.run T₁).state = none → (R.run T₂).state = none →
      L.crossings k T₁ = R.crossings k T₂ →
      ∃ T ≤ T₁ + T₂, (C.run T).state = none ∧
        (∀ k' ≤ k, C.crossings k' T = L.crossings k' T₁) ∧
        (∀ k', k ≤ k' → C.crossings k' T = R.crossings k' T₂) ∧
        Splice k (L.run T₁) (R.run T₂) (C.run T) := by
  intro n
  induction n with
  | zero =>
    intro L R C T₁ T₂ hT h hL hR _
    obtain ⟨rfl, rfl⟩ : T₁ = 0 ∧ T₂ = 0 := by omega
    refine ⟨0, le_rfl, ?_, fun _ _ => rfl, fun _ _ => rfl, h⟩
    by_cases hC : IsLeftOf k C.pos
    · rw [AbsCfg.run_zero, (h.follow_left hC).1]; exact hL
    · rw [AbsCfg.run_zero, (h.follow_right hC).1]; exact hR
  | succ n ih =>
    intro L R C T₁ T₂ hT h hL hR hx
    by_cases hC : IsLeftOf k C.pos
    · obtain ⟨hsL, hpL⟩ := h.follow_left hC
      have hRside : IsLeftOf k R.pos := h.right_side.mpr hC
      by_cases hL0 : L.state = none
      · have hnil : L.crossings k T₁ = [] := AbsCfg.crossings_of_none hL0 k T₁
        have hR0 : R.crossings k T₂ = [] := hx ▸ hnil
        refine ⟨0, Nat.zero_le _, by rw [AbsCfg.run_zero, hsL]; exact hL0,
          fun k' _ => (AbsCfg.crossings_of_none hL0 k' T₁).symm,
          fun k' hk' => (AbsCfg.crossings_eq_nil_of_left hk' hRside hR0).symm, ?_⟩
        rw [AbsCfg.run_of_none hL0, AbsCfg.run_zero]
        exact h.run_right_of_nil hC hR0
      · obtain ⟨T₁, rfl⟩ : ∃ m, T₁ = m + 1 := by
          rcases T₁ with _ | m
          · exact (hL0 hL).elim
          · exact ⟨m, rfl⟩
        rw [AbsCfg.run_succ] at hL
        have hLside : IsLeftOf k L.pos := h.left_side.mpr hC
        obtain ⟨hsn, hpn⟩ := h.next_agree_left hC
        by_cases hs : IsLeftOf k L.pos ↔ IsLeftOf k L.next.pos
        · have hcr : L.crossings k (T₁ + 1) = L.next.crossings k T₁ := by
            simp only [AbsCfg.crossings, hs, ite_true]
          have hsp0 := h.next_left hC (hs.mp hLside)
          obtain ⟨T, hT', hhalt, hcL, hcR, hsp⟩ := ih (by omega) hsp0 hL hR (hcr ▸ hx)
          have hC' : IsLeftOf k C.next.pos := hsp0.left_side.mp (hs.mp hLside)
          refine ⟨T + 1, by omega, by rw [AbsCfg.run_succ]; exact hhalt,
            fun k' hk' => AbsCfg.crossings_succ_congr hpL hpn hsn (hcL k' hk'),
            fun k' hk' => ?_, by rw [AbsCfg.run_succ, AbsCfg.run_succ]; exact hsp⟩
          rw [AbsCfg.crossings_succ_of_left hk' hC hC']
          exact hcR k' hk'
        · have hcr : L.crossings k (T₁ + 1) = L.next.state :: L.next.crossings k T₁ := by
            simp only [AbsCfg.crossings, hs, ite_false]
          obtain ⟨j, hj, h0, hxj, hstj, hrest⟩ := AbsCfg.exists_first_crossing (hcr ▸ hx).symm
          have hn : ¬ IsLeftOf k L.next.pos := fun h' => hs ⟨fun _ => h', fun _ => hLside⟩
          have hsp1 := h.next_cross_right hC hn h0 hxj hstj
          have hR' : IsLeftOf k (R.run j).pos := (AbsCfg.run_of_crossings_nil h0).1.mpr hRside
          obtain ⟨hR'k, hR'nk⟩ :=
            AbsCfg.cross_right hR' (fun h' => hxj ⟨fun _ => h', fun _ => hR'⟩)
          obtain ⟨hLk1, hLk⟩ := AbsCfg.cross_right hLside hn
          rw [AbsCfg.run_split R hj] at hR ⊢
          obtain ⟨T, hT', hhalt, hcL, hcR, hsp⟩ := ih (by omega) hsp1 hL hR hrest.symm
          refine ⟨T + 1, by omega, by rw [AbsCfg.run_succ]; exact hhalt,
            fun k' hk' => AbsCfg.crossings_succ_congr hpL hpn hsn (hcL k' hk'),
            fun k' hk' => ?_, by rw [AbsCfg.run_succ, AbsCfg.run_succ]; exact hsp⟩
          rw [AbsCfg.crossings_split R hj, AbsCfg.crossings_eq_nil_of_left hk' hRside h0,
            List.nil_append]
          exact AbsCfg.crossings_succ_congr (hpL.trans (hLk1.trans hR'k.symm))
            (hpn.trans (hLk.trans hR'nk.symm)) (hsn.trans hstj.symm) (hcR k' hk')
    · obtain ⟨hsR, hpR⟩ := h.follow_right hC
      have hLside : ¬ IsLeftOf k L.pos := fun h' => hC (h.left_side.mp h')
      by_cases hR0 : R.state = none
      · have hnil : R.crossings k T₂ = [] := AbsCfg.crossings_of_none hR0 k T₂
        have hL0 : L.crossings k T₁ = [] := hx ▸ hnil
        refine ⟨0, Nat.zero_le _, by rw [AbsCfg.run_zero, hsR]; exact hR0,
          fun k' hk' => (AbsCfg.crossings_eq_nil_of_right hk' hLside hL0).symm,
          fun k' _ => (AbsCfg.crossings_of_none hR0 k' T₂).symm, ?_⟩
        rw [AbsCfg.run_of_none hR0, AbsCfg.run_zero]
        exact h.run_left_of_nil hC hL0
      · obtain ⟨T₂, rfl⟩ : ∃ m, T₂ = m + 1 := by
          rcases T₂ with _ | m
          · exact (hR0 hR).elim
          · exact ⟨m, rfl⟩
        rw [AbsCfg.run_succ] at hR
        have hRside : ¬ IsLeftOf k R.pos := fun h' => hC (h.right_side.mp h')
        obtain ⟨hsn, hpn⟩ := h.next_agree_right hC
        by_cases hs : IsLeftOf k R.pos ↔ IsLeftOf k R.next.pos
        · have hcr : R.crossings k (T₂ + 1) = R.next.crossings k T₂ := by
            simp only [AbsCfg.crossings, hs, ite_true]
          have hn : ¬ IsLeftOf k R.next.pos := fun h' => hRside (hs.mpr h')
          have hsp0 := h.next_right hC hn
          obtain ⟨T, hT', hhalt, hcL, hcR, hsp⟩ := ih (by omega) hsp0 hL hR (hcr ▸ hx)
          have hC' : ¬ IsLeftOf k C.next.pos := fun h' => hn (hsp0.right_side.mpr h')
          refine ⟨T + 1, by omega, by rw [AbsCfg.run_succ]; exact hhalt, fun k' hk' => ?_,
            fun k' hk' => AbsCfg.crossings_succ_congr hpR hpn hsn (hcR k' hk'),
            by rw [AbsCfg.run_succ, AbsCfg.run_succ]; exact hsp⟩
          rw [AbsCfg.crossings_succ_of_right hk' hC hC']
          exact hcL k' hk'
        · have hcr : R.crossings k (T₂ + 1) = R.next.state :: R.next.crossings k T₂ := by
            simp only [AbsCfg.crossings, hs, ite_false]
          obtain ⟨j, hj, h0, hxj, hstj, hrest⟩ := AbsCfg.exists_first_crossing (hx.trans hcr)
          have hn : IsLeftOf k R.next.pos := by
            by_contra h'
            exact hs ⟨fun h'' => (hRside h'').elim, fun h'' => (h' h'').elim⟩
          have hsp1 := h.next_cross_left hC hn h0 hxj hstj
          have hL' : ¬ IsLeftOf k (L.run j).pos :=
            fun h' => hLside ((AbsCfg.run_of_crossings_nil h0).1.mp h')
          have hL'n : IsLeftOf k (L.run j).next.pos := by
            by_contra h'
            exact hxj ⟨fun h'' => (hL' h'').elim, fun h'' => (h' h'').elim⟩
          obtain ⟨hL'k, hL'nk⟩ := AbsCfg.cross_left hL' hL'n
          obtain ⟨hRk, hRnk⟩ := AbsCfg.cross_left hRside hn
          rw [AbsCfg.run_split L hj] at hL ⊢
          obtain ⟨T, hT', hhalt, hcL, hcR, hsp⟩ := ih (by omega) hsp1 hL hR hrest
          refine ⟨T + 1, by omega, by rw [AbsCfg.run_succ]; exact hhalt, fun k' hk' => ?_,
            fun k' hk' => AbsCfg.crossings_succ_congr hpR hpn hsn (hcR k' hk'),
            by rw [AbsCfg.run_succ, AbsCfg.run_succ]; exact hsp⟩
          rw [AbsCfg.crossings_split L hj, AbsCfg.crossings_eq_nil_of_right hk' hLside h0,
            List.nil_append]
          exact AbsCfg.crossings_succ_congr (hpR.trans (hRk.trans hL'k.symm))
            (hpn.trans (hRnk.trans hL'nk.symm)) (hsn.trans hstj.symm) (hcL k' hk')

/-- Agreement is preserved along a run of the finite machine. -/
lemma Agrees.relatesInSteps {c c' : tm.Cfg} {a : tm.AbsCfg} {m : ℕ} (h : Agrees c a)
    (hr : RelatesInSteps tm.TransitionRelation c c' m) : Agrees c' (a.run m) := by
  induction hr generalizing a with
  | refl => exact h
  | tail t' t'' n _ hstep ih =>
    rw [AbsCfg.run, Function.iterate_succ_apply']
    exact (ih h).step hstep

lemma AbsCfg.run_add (a : tm.AbsCfg) (s t : ℕ) : a.run (s + t) = (a.run s).run t := by
  rw [run, run, run, Nat.add_comm, Function.iterate_add_apply]

/-- A deterministic run has at most one halted configuration. -/
lemma AbsCfg.run_eq_of_halted (a : tm.AbsCfg) {s t : ℕ} (hs : (a.run s).state = none)
    (ht : (a.run t).state = none) : a.run s = a.run t := by
  rcases le_total s t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_add, run_of_none hs]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [run_add, run_of_none ht]

/-- Once a run has halted, later steps add no crossings: crossing sequences up to any two halted
times agree. -/
lemma AbsCfg.crossings_eq_of_halted (a : tm.AbsCfg) (k : ℤ) {s t : ℕ}
    (hs : (a.run s).state = none) (ht : (a.run t).state = none) :
    a.crossings k s = a.crossings k t := by
  rcases le_total s t with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [crossings_add, crossings_of_none hs, List.append_nil]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [crossings_add, crossings_of_none ht, List.append_nil]

/-- If `tm` reaches a halted configuration `c` from the initial configuration on `l` within `t`
steps, then the absolute run has halted by time `t` and scans the symbol under the head of
`c`. -/
theorem absRun_of_relatesWithinSteps {l : List Symbol} {c : tm.Cfg} {t : ℕ}
    (h : RelatesWithinSteps tm.TransitionRelation (tm.initCfg l) c t) (hc : c.state = none) :
    ((tm.absInit l).run t).state = none ∧ ((tm.absInit l).run t).scanned = c.BiTape.head := by
  obtain ⟨m, hm, hr⟩ := h
  have hag := (agrees_init (tm := tm) l).relatesInSteps hr
  have hhalt : ((tm.absInit l).run m).state = none := hag.1.symm.trans hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [AbsCfg.run_add, AbsCfg.run_of_none hhalt]
  exact ⟨hhalt, hag.2.head.symm⟩

/-- If `tm` outputs `l'` on `l` within `t` steps, then the absolute run has halted by time `t`,
and the cell under its head holds the first symbol of `l'`. -/
theorem absRun_of_outputsWithinTime {l l' : List Symbol} {t : ℕ}
    (h : tm.OutputsWithinTime l l' t) :
    ((tm.absInit l).run t).state = none ∧ ((tm.absInit l).run t).scanned = l'.head? := by
  have h' := absRun_of_relatesWithinSteps (c := tm.haltCfg l') h rfl
  simpa [haltCfg] using h'

/-- A decider that answers under the head has halted in the absolute run by the time bound, and
the scanned cell then holds `yes` exactly on members of the language. -/
theorem DecidesByHeadInTime.absRun {α : Type*} {ι : α → Symbol} {L : Language α} {yes : Symbol}
    {T : ℕ → ℕ} (h : tm.DecidesByHeadInTime ι L yes T) (w : List α) :
    ((tm.absInit (w.map ι)).run (T w.length)).state = none ∧
      (((tm.absInit (w.map ι)).run (T w.length)).scanned = some yes ↔ w ∈ L) := by
  obtain ⟨c, hr, hc, hyes⟩ := h w
  obtain ⟨h1, h2⟩ := absRun_of_relatesWithinSteps hr hc
  refine ⟨h1, ?_⟩
  rw [h2]
  exact hyes

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma read_mk₁_append_left {u v v' : List Symbol} {p : ℤ} (hp : p < u.length) :
    (BiTape.mk₁ (u ++ v)).read p = (BiTape.mk₁ (u ++ v')).read p := by
  rw [BiTape.read_mk₁, BiTape.read_mk₁]
  split_ifs with h0
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · rfl

/-- The initial configuration on `u₁ ++ v₂` is the splice at `|u₁|` of the initial configuration
on `u₁ ++ v₁` and that on `u₂ ++ v₂` translated by `|u₁| - |u₂|`. The prefixes must be both
empty or both nonempty, so that all three heads start on the same side of the boundary. -/
private lemma splice_absInit {u₁ v₁ u₂ v₂ : List Symbol} (hu : u₁ = [] ↔ u₂ = []) :
    Splice (u₁.length : ℤ) (tm.absInit (u₁ ++ v₁))
      ((tm.absInit (u₂ ++ v₂)).shift ((u₁.length : ℤ) - u₂.length))
      (tm.absInit (u₁ ++ v₂)) where
  cells p := by
    simp only [absInit, AbsCfg.shift_cells]
    split_ifs with hp
    · exact read_mk₁_append_left hp
    · unfold IsLeftOf at hp
      rw [BiTape.read_mk₁, BiTape.read_mk₁, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
        ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
        List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      congr 1
      omega
  left_side := Iff.rfl
  right_side := by
    simp only [absInit, AbsCfg.shift_pos, IsLeftOf, zero_add]
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff] at hu
    omega
  follow_left _ := ⟨rfl, rfl⟩
  follow_right hp := by
    simp only [absInit, IsLeftOf] at hp
    have h1 : u₁ = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : u₂ = [] := hu.mp h1
    subst h1 h2
    simp [absInit]

/-- The symbol under the head of a splice is the one under the head of the run owning that
side. -/
private lemma Splice.head_cell {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C) :
    C.scanned = L.scanned ∨ C.scanned = R.scanned := by
  by_cases hC : IsLeftOf k C.pos
  · left
    rw [AbsCfg.scanned, h.cells, ite_eq_left hC, (h.follow_left hC).2]
    rfl
  · right
    rw [AbsCfg.scanned, h.cells, ite_eq_right hC, (h.follow_right hC).2]
    rfl

/-- **Cut-and-paste lemma, run form** (Hennie). Let the prefixes `u₁, u₂` be both empty or both
nonempty. Suppose the runs on `u₁ ++ v₁` and `u₂ ++ v₂` have halted by steps `t₁` and `t₂`,
with the same crossing sequence at the boundary after the prefix. Then the run on `u₁ ++ v₂`
has halted by step `t₁ + t₂`. At every boundary `k ≤ |u₁|` its crossing sequence is that of the
run on `u₁ ++ v₁`, and at every boundary `k ≥ |u₁|` it is that of the run on `u₂ ++ v₂` at the
corresponding boundary `k - |u₁| + |u₂|`. The symbol under its head at the halt is the one under
the head of one of the two original runs at its halt. -/
theorem cut_and_paste_run {u₁ v₁ u₂ v₂ : List Symbol} {t₁ t₂ : ℕ} (hu : u₁ = [] ↔ u₂ = [])
    (h₁ : ((tm.absInit (u₁ ++ v₁)).run t₁).state = none)
    (h₂ : ((tm.absInit (u₂ ++ v₂)).run t₂).state = none)
    (hx : (tm.absInit (u₁ ++ v₁)).crossings u₁.length t₁ =
      (tm.absInit (u₂ ++ v₂)).crossings u₂.length t₂) :
    ((tm.absInit (u₁ ++ v₂)).run (t₁ + t₂)).state = none ∧
      (∀ k : ℤ, k ≤ u₁.length → (tm.absInit (u₁ ++ v₂)).crossings k (t₁ + t₂) =
        (tm.absInit (u₁ ++ v₁)).crossings k t₁) ∧
      (∀ k : ℤ, (u₁.length : ℤ) ≤ k → (tm.absInit (u₁ ++ v₂)).crossings k (t₁ + t₂) =
        (tm.absInit (u₂ ++ v₂)).crossings (k - u₁.length + u₂.length) t₂) ∧
      (((tm.absInit (u₁ ++ v₂)).run (t₁ + t₂)).scanned =
          ((tm.absInit (u₁ ++ v₁)).run t₁).scanned ∨
        ((tm.absInit (u₁ ++ v₂)).run (t₁ + t₂)).scanned =
          ((tm.absInit (u₂ ++ v₂)).run t₂).scanned) := by
  have hsp := splice_absInit (tm := tm) (v₁ := v₁) (v₂ := v₂) hu
  have hR : (((tm.absInit (u₂ ++ v₂)).shift ((u₁.length : ℤ) - u₂.length)).run t₂).state =
      none := by
    rw [AbsCfg.run_shift, AbsCfg.shift_state]
    exact h₂
  have hx' : (tm.absInit (u₁ ++ v₁)).crossings u₁.length t₁ =
      ((tm.absInit (u₂ ++ v₂)).shift ((u₁.length : ℤ) - u₂.length)).crossings u₁.length t₂ := by
    rw [hx, ← AbsCfg.crossings_shift ((u₁.length : ℤ) - u₂.length) (u₂.length : ℤ)
      (tm.absInit (u₂ ++ v₂))]
    congr 1
    omega
  obtain ⟨T, hT, hC, hcL, hcR, hsp'⟩ := Splice.run_halts _ le_rfl hsp h₁ hR hx'
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hT
  have hrun : (tm.absInit (u₁ ++ v₂)).run (t₁ + t₂) = (tm.absInit (u₁ ++ v₂)).run T := by
    rw [he, AbsCfg.run_add, AbsCfg.run_of_none hC]
  have hcr (k : ℤ) : (tm.absInit (u₁ ++ v₂)).crossings k (t₁ + t₂) =
      (tm.absInit (u₁ ++ v₂)).crossings k T := by
    rw [he, AbsCfg.crossings_add, AbsCfg.crossings_of_none hC, List.append_nil]
  refine ⟨hrun ▸ hC, fun k hk => (hcr k).trans (hcL k hk), fun k hk => ?_, ?_⟩
  · rw [hcr, hcR k hk, ← AbsCfg.crossings_shift ((u₁.length : ℤ) - u₂.length)
      (k - u₁.length + u₂.length) (tm.absInit (u₂ ++ v₂))]
    congr 1
    omega
  · rw [hrun]
    rcases hsp'.head_cell with h | h
    · exact Or.inl h
    · right
      rw [h, AbsCfg.run_shift, AbsCfg.scanned_shift]

/-- **Cut-and-paste lemma** (Hennie). Let the prefixes `u₁, u₂` be both empty or both
nonempty. If `tm` outputs `o₁` on `u₁ ++ v₁` within `t₁` steps and `o₂` on `u₂ ++ v₂` within
`t₂` steps, with the same crossing sequence at the boundary after the prefix, then the run on
`u₁ ++ v₂` halts within `t₁ + t₂` steps with that crossing sequence after `u₁`, and any output
`o` of `tm` on `u₁ ++ v₂` begins with the first symbol of `o₁` or of `o₂`. -/
theorem cut_and_paste {u₁ v₁ u₂ v₂ o₁ o₂ : List Symbol} {t₁ t₂ : ℕ}
    (hu : u₁ = [] ↔ u₂ = []) (h₁ : tm.OutputsWithinTime (u₁ ++ v₁) o₁ t₁)
    (h₂ : tm.OutputsWithinTime (u₂ ++ v₂) o₂ t₂)
    (hx : (tm.absInit (u₁ ++ v₁)).crossings u₁.length t₁ =
      (tm.absInit (u₂ ++ v₂)).crossings u₂.length t₂) :
    ((tm.absInit (u₁ ++ v₂)).run (t₁ + t₂)).state = none ∧
      (tm.absInit (u₁ ++ v₂)).crossings u₁.length (t₁ + t₂) =
        (tm.absInit (u₁ ++ v₁)).crossings u₁.length t₁ ∧
      ∀ {o : List Symbol} {t : ℕ}, tm.OutputsWithinTime (u₁ ++ v₂) o t →
        o.head? = o₁.head? ∨ o.head? = o₂.head? := by
  obtain ⟨hL, hLc⟩ := absRun_of_outputsWithinTime h₁
  obtain ⟨hR, hRc⟩ := absRun_of_outputsWithinTime h₂
  obtain ⟨hC, hcL, -, hhead⟩ := cut_and_paste_run hu hL hR hx
  refine ⟨hC, hcL _ le_rfl, fun ho => ?_⟩
  obtain ⟨hO, hOc⟩ := absRun_of_outputsWithinTime ho
  rw [← hOc, AbsCfg.run_eq_of_halted _ hO hC, ← hLc, ← hRc]
  exact hhead

end Cslib.Turing.SingleTapeTM
