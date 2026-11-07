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
* `Cslib.Turing.SingleTapeTM.AbsCfg.crossings k a t`: the crossing sequence at boundary `k`
  during the first `t` steps from `a`.

## Main results

* `Cslib.Turing.SingleTapeTM.absRun_of_outputsWithinTime`: if `tm.OutputsWithinTime l l' t`,
  the absolute run from `absInit l` has halted at step `t` with the head on the first symbol of
  `l'`.
* `Cslib.Turing.SingleTapeTM.AbsCfg.sum_length_crossings_le`: for any finite set of boundaries,
  the crossing sequences during `t` steps have total length at most `t`.
* `Cslib.Turing.SingleTapeTM.cut_and_paste`: let `|u₁| = |u₂|`. If the runs on `u₁ ++ v₁` and
  `u₂ ++ v₂` halt within `t₁` and `t₂` steps with equal crossing sequences at the boundary
  after the prefix, then the run on `u₁ ++ v₂` halts within `t₁ + t₂` steps with the same
  crossing sequence, and the first symbol of its output is the first symbol of one of the two
  original outputs.

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
steps with equal crossing sequences at `k`, the splice halts within `T₁ + T₂` steps with the same
crossing sequence, and its final configuration is the splice of the two final ones. -/
private theorem Splice.run_halts {k : ℤ} :
    ∀ (n : ℕ) {L R C : tm.AbsCfg} {T₁ T₂ : ℕ}, T₁ + T₂ ≤ n → Splice k L R C →
      (L.run T₁).state = none → (R.run T₂).state = none →
      L.crossings k T₁ = R.crossings k T₂ →
      ∃ T ≤ T₁ + T₂, (C.run T).state = none ∧ C.crossings k T = L.crossings k T₁ ∧
        Splice k (L.run T₁) (R.run T₂) (C.run T) := by
  intro n
  induction n with
  | zero =>
    intro L R C T₁ T₂ hT h hL hR _
    obtain ⟨rfl, rfl⟩ : T₁ = 0 ∧ T₂ = 0 := by omega
    refine ⟨0, le_rfl, ?_, rfl, h⟩
    by_cases hC : IsLeftOf k C.pos
    · rw [AbsCfg.run_zero, (h.follow_left hC).1]; exact hL
    · rw [AbsCfg.run_zero, (h.follow_right hC).1]; exact hR
  | succ n ih =>
    intro L R C T₁ T₂ hT h hL hR hx
    by_cases hC : IsLeftOf k C.pos
    · obtain ⟨hsL, hpL⟩ := h.follow_left hC
      by_cases hL0 : L.state = none
      · have hnil : L.crossings k T₁ = [] := AbsCfg.crossings_of_none hL0 k T₁
        have hR0 : R.crossings k T₂ = [] := hx ▸ hnil
        refine ⟨0, Nat.zero_le _, by rw [AbsCfg.run_zero, hsL]; exact hL0, by
          rw [hnil]; rfl, ?_⟩
        rw [AbsCfg.run_of_none hL0, AbsCfg.run_zero]
        exact h.run_right_of_nil hC hR0
      · obtain ⟨T₁, rfl⟩ : ∃ m, T₁ = m + 1 := by
          rcases T₁ with _ | m
          · exact (hL0 hL).elim
          · exact ⟨m, rfl⟩
        rw [AbsCfg.run_succ] at hL
        have hLside : IsLeftOf k L.pos := h.left_side.mpr hC
        by_cases hs : IsLeftOf k L.pos ↔ IsLeftOf k L.next.pos
        · have hcr : L.crossings k (T₁ + 1) = L.next.crossings k T₁ := by
            simp only [AbsCfg.crossings, hs, ite_true]
          obtain ⟨T, hT', hhalt, hcs, hsp⟩ :=
            ih (by omega) (h.next_left hC (hs.mp hLside)) hL hR (hcr ▸ hx)
          have hC' : IsLeftOf k C.next.pos :=
            (h.next_left hC (hs.mp hLside)).left_side.mp (hs.mp hLside)
          refine ⟨T + 1, by omega, by rw [AbsCfg.run_succ]; exact hhalt, ?_, ?_⟩
          · simp only [AbsCfg.crossings, iff_of_true hC hC', ite_true]
            rw [hcs]
            exact hcr.symm
          · rw [AbsCfg.run_succ, AbsCfg.run_succ]; exact hsp
        · have hcr : L.crossings k (T₁ + 1) = L.next.state :: L.next.crossings k T₁ := by
            simp only [AbsCfg.crossings, hs, ite_false]
          obtain ⟨j, hj, h0, hxj, hstj, hrest⟩ := AbsCfg.exists_first_crossing (hcr ▸ hx).symm
          have hn : ¬ IsLeftOf k L.next.pos := fun h' => hs ⟨fun _ => h', fun _ => hLside⟩
          have hsp1 := h.next_cross_right hC hn h0 hxj hstj
          rw [AbsCfg.run_split R hj] at hR ⊢
          obtain ⟨T, hT', hhalt, hcs, hsp⟩ := ih (by omega) hsp1 hL hR hrest.symm
          refine ⟨T + 1, by omega, by rw [AbsCfg.run_succ]; exact hhalt, ?_, ?_⟩
          · have hCn : ¬ IsLeftOf k C.next.pos := fun h' => hn (hsp1.left_side.mpr h')
            have hsC : C.next.state = L.next.state := (hsp1.follow_right hCn).1.trans hstj
            have hne : ¬(IsLeftOf k C.pos ↔ IsLeftOf k C.next.pos) := fun h' => hCn (h'.mp hC)
            simp only [AbsCfg.crossings, hne, ite_false]
            rw [hcs, hsC]
            exact hcr.symm
          · rw [AbsCfg.run_succ, AbsCfg.run_succ]; exact hsp
    · obtain ⟨hsR, hpR⟩ := h.follow_right hC
      rw [hx]
      by_cases hR0 : R.state = none
      · have hnil : R.crossings k T₂ = [] := AbsCfg.crossings_of_none hR0 k T₂
        have hL0 : L.crossings k T₁ = [] := hx ▸ hnil
        refine ⟨0, Nat.zero_le _, by rw [AbsCfg.run_zero, hsR]; exact hR0, by
          rw [hnil]; rfl, ?_⟩
        rw [AbsCfg.run_of_none hR0, AbsCfg.run_zero]
        exact h.run_left_of_nil hC hL0
      · obtain ⟨T₂, rfl⟩ : ∃ m, T₂ = m + 1 := by
          rcases T₂ with _ | m
          · exact (hR0 hR).elim
          · exact ⟨m, rfl⟩
        rw [AbsCfg.run_succ] at hR
        have hRside : ¬ IsLeftOf k R.pos := fun h' => hC (h.right_side.mp h')
        by_cases hs : IsLeftOf k R.pos ↔ IsLeftOf k R.next.pos
        · have hcr : R.crossings k (T₂ + 1) = R.next.crossings k T₂ := by
            simp only [AbsCfg.crossings, hs, ite_true]
          have hn : ¬ IsLeftOf k R.next.pos := fun h' => hRside (hs.mpr h')
          obtain ⟨T, hT', hhalt, hcs, hsp⟩ :=
            ih (by omega) (h.next_right hC hn) hL hR (hcr ▸ hx)
          have hC' : ¬ IsLeftOf k C.next.pos := fun h' =>
            hn ((h.next_right hC hn).right_side.mpr h')
          refine ⟨T + 1, by omega, by rw [AbsCfg.run_succ]; exact hhalt, ?_, ?_⟩
          · simp only [AbsCfg.crossings, iff_of_false hC hC', ite_true]
            rw [hcs, hx]
            rfl
          · rw [AbsCfg.run_succ, AbsCfg.run_succ]; exact hsp
        · have hcr : R.crossings k (T₂ + 1) = R.next.state :: R.next.crossings k T₂ := by
            simp only [AbsCfg.crossings, hs, ite_false]
          obtain ⟨j, hj, h0, hxj, hstj, hrest⟩ := AbsCfg.exists_first_crossing (hx.trans hcr)
          have hn : IsLeftOf k R.next.pos := by
            by_contra h'
            exact hs ⟨fun h'' => (hRside h'').elim, fun h'' => (h' h'').elim⟩
          have hsp1 := h.next_cross_left hC hn h0 hxj hstj
          rw [AbsCfg.run_split L hj] at hL ⊢
          obtain ⟨T, hT', hhalt, hcs, hsp⟩ := ih (by omega) hsp1 hL hR hrest
          refine ⟨T + 1, by omega, by rw [AbsCfg.run_succ]; exact hhalt, ?_, ?_⟩
          · have hCn : IsLeftOf k C.next.pos := hsp1.right_side.mp hn
            have hsC : C.next.state = R.next.state := (hsp1.follow_left hCn).1.trans hstj
            have hne : ¬(IsLeftOf k C.pos ↔ IsLeftOf k C.next.pos) := fun h' => hC (h'.mpr hCn)
            simp only [AbsCfg.crossings, hne, ite_false]
            rw [hcs, hsC, hrest]
            exact hcr.symm
          · rw [AbsCfg.run_succ, AbsCfg.run_succ]; exact hsp

/-- Agreement is preserved along a run of the finite machine. -/
lemma Agrees.relatesInSteps {c c' : tm.Cfg} {a : tm.AbsCfg} {m : ℕ} (h : Agrees c a)
    (hr : RelatesInSteps tm.TransitionRelation c c' m) : Agrees c' (a.run m) := by
  induction hr generalizing a with
  | refl => exact h
  | tail t' t'' n _ hstep ih =>
    rw [AbsCfg.run, Function.iterate_succ_apply']
    exact (ih h).step hstep

/-- If `tm` outputs `l'` on `l` within `t` steps, then the absolute run has halted by time `t`,
and the cell under its head holds the first symbol of `l'`. -/
theorem absRun_of_outputsWithinTime {l l' : List Symbol} {t : ℕ}
    (h : tm.OutputsWithinTime l l' t) :
    ((tm.absInit l).run t).state = none ∧
      ((tm.absInit l).run t).cells ((tm.absInit l).run t).pos = l'.head? := by
  obtain ⟨m, hm, hr⟩ := h
  have hag := (agrees_init (tm := tm) l).relatesInSteps hr
  have hhalt : ((tm.absInit l).run m).state = none := hag.1.symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hrun : (tm.absInit l).run (m + d) = (tm.absInit l).run m := by
    rw [AbsCfg.run, Nat.add_comm, Function.iterate_add_apply]
    exact Function.iterate_fixed (AbsCfg.next_of_none hhalt) d
  rw [hrun]
  refine ⟨hhalt, ?_⟩
  rw [← hag.2.head]
  simp [haltCfg]

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma read_mk₁_append_left {u v v' : List Symbol} {p : ℤ} (hp : p < u.length) :
    (BiTape.mk₁ (u ++ v)).read p = (BiTape.mk₁ (u ++ v')).read p := by
  rw [BiTape.read_mk₁, BiTape.read_mk₁]
  split_ifs with h0
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
  · rfl

omit [Inhabited Symbol] [Fintype Symbol] in
private lemma read_mk₁_append_right {u u' v : List Symbol} (hu : u.length = u'.length) {p : ℤ}
    (hp : ¬ p < u.length) :
    (BiTape.mk₁ (u ++ v)).read p = (BiTape.mk₁ (u' ++ v)).read p := by
  rw [BiTape.read_mk₁, BiTape.read_mk₁, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
    ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
    List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hu]

/-- The initial configuration on `u₁ ++ v₂` is the splice at `|u₁|` of those on `u₁ ++ v₁` and
`u₂ ++ v₂`, when `|u₁| = |u₂|`. -/
private lemma splice_absInit {u₁ v₁ u₂ v₂ : List Symbol} (hu : u₁.length = u₂.length) :
    Splice (u₁.length : ℤ) (tm.absInit (u₁ ++ v₁)) (tm.absInit (u₂ ++ v₂))
      (tm.absInit (u₁ ++ v₂)) where
  cells p := by
    simp only [absInit]
    split_ifs with hp
    · exact read_mk₁_append_left hp
    · exact read_mk₁_append_right hu hp
  left_side := Iff.rfl
  right_side := Iff.rfl
  follow_left _ := ⟨rfl, rfl⟩
  follow_right _ := ⟨rfl, rfl⟩

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

/-- The symbol under the head of the final configuration of a splice is the one under the head
of the final configuration of the run owning that side. -/
private lemma Splice.head_cell {k : ℤ} {L R C : tm.AbsCfg} (h : Splice k L R C) :
    C.cells C.pos = L.cells L.pos ∨ C.cells C.pos = R.cells R.pos := by
  by_cases hC : IsLeftOf k C.pos
  · left
    rw [h.cells, ite_eq_left hC, (h.follow_left hC).2]
  · right
    rw [h.cells, ite_eq_right hC, (h.follow_right hC).2]

/-- **Cut-and-paste lemma** (Hennie). Let `|u₁| = |u₂|`. If `tm` outputs `o₁` on `u₁ ++ v₁`
within `t₁` steps and `o₂` on `u₂ ++ v₂` within `t₂` steps, with the same crossing sequence at the
boundary after `u₁`, then the run on `u₁ ++ v₂` halts within `t₁ + t₂` steps with that crossing
sequence, and any output `o` of `tm` on `u₁ ++ v₂` begins with the first symbol of `o₁` or of
`o₂`. -/
theorem cut_and_paste {u₁ v₁ u₂ v₂ o₁ o₂ : List Symbol} {t₁ t₂ : ℕ}
    (hu : u₁.length = u₂.length) (h₁ : tm.OutputsWithinTime (u₁ ++ v₁) o₁ t₁)
    (h₂ : tm.OutputsWithinTime (u₂ ++ v₂) o₂ t₂)
    (hx : (tm.absInit (u₁ ++ v₁)).crossings u₁.length t₁ =
      (tm.absInit (u₂ ++ v₂)).crossings u₁.length t₂) :
    ((tm.absInit (u₁ ++ v₂)).run (t₁ + t₂)).state = none ∧
      (tm.absInit (u₁ ++ v₂)).crossings u₁.length (t₁ + t₂) =
        (tm.absInit (u₁ ++ v₁)).crossings u₁.length t₁ ∧
      ∀ {o : List Symbol} {t : ℕ}, tm.OutputsWithinTime (u₁ ++ v₂) o t →
        o.head? = o₁.head? ∨ o.head? = o₂.head? := by
  obtain ⟨hL, hLc⟩ := absRun_of_outputsWithinTime h₁
  obtain ⟨hR, hRc⟩ := absRun_of_outputsWithinTime h₂
  obtain ⟨T, hT, hC, hcs, hsp⟩ := Splice.run_halts _ le_rfl (splice_absInit hu) hL hR hx
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hT
  refine ⟨by rw [hd, AbsCfg.run_add, AbsCfg.run_of_none hC]; exact hC, ?_, ?_⟩
  · rw [hd, AbsCfg.crossings_add, AbsCfg.crossings_of_none hC, List.append_nil, hcs]
  · intro o t ho
    obtain ⟨hO, hOc⟩ := absRun_of_outputsWithinTime ho
    rw [← hOc, AbsCfg.run_eq_of_halted _ hO hC, ← hLc, ← hRc]
    exact hsp.head_cell


end Cslib.Turing.SingleTapeTM
