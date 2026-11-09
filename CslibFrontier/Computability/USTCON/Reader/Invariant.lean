/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.USTCON.Reader.Correct
public import CslibFrontier.Computability.USTCON.Reader.Encode
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith

/-!
# The states of the read machine for undirected connectivity are small

On the encoding of an instance on `n` vertices, every state of `Cslib.USTCON.Reader.machine` along
its run keeps its numbers below `n`, the depth `D` and the walk length `T` of Reingold's graph, and
`B ^ T` for the counters, where `B = 257 ^ 8`, its slot below `n`, and at most `D + 1` labels and
frames (`Cslib.USTCON.Reader.inv_run`). As `D` and `T` are `O(log n)`, the encoded states have
`O(log n)` bits, which is logarithmic in the length of the encoding
(`Cslib.USTCON.Reader.length_encState_run_le`).

## Main definitions

* `Cslib.USTCON.Reader.Bounds`, `Cslib.USTCON.Reader.Inv`: the bounds on the states, and the
  invariant of the run that keeps them.

## Main results

* `Cslib.USTCON.Reader.inv_run`: the states along the run satisfy the invariant.
* `Cslib.USTCON.Reader.length_encState_run_le`: they have logarithmically many bits.
-/

@[expose] public section

namespace Cslib.USTCON.Reader

open Turing MultiTapeTM Cslib.RotationMap Cslib.Reachability.Reingold Cslib.Complexity

variable (I : USTCONInstance)

/-- The depth of Reingold's graph for the instance. -/
abbrev depthOf : ℕ := depth (Nat.size I.n)

/-- The walk length for the instance. -/
abbrev lenOf : ℕ := walkLength (Nat.size I.n)

/-- **The bounds on the states**: numbers at most `n`, the depth, the walk length and `B ^ T`, the
slot below `n`, and at most `D + 1` labels and frames. -/
structure Bounds (q : State) : Prop where
  cnt : q.cnt ≤ I.n
  n : q.n ≤ I.n
  s : q.s ≤ I.n
  t : q.t ≤ I.n
  depth : q.depth ≤ depthOf I
  len : q.len ≤ lenOf I
  c : q.c ≤ numLabels ^ lenOf I
  w : q.w ≤ numLabels ^ lenOf I
  j : q.j ≤ lenOf I
  v₁ : q.ev.vertex.1 < I.n
  v₂ : q.ev.vertex.2 < I.n
  lower : q.ev.lower.length ≤ depthOf I + 1
  frames : q.ev.frames.length ≤ depthOf I + 1

/-- The parameters of the walks. -/
def WalkParams (q : State) : Prop :=
  q.n = I.n ∧ q.s = I.s ∧ q.t = I.t ∧ q.depth = depthOf I ∧ q.len = lenOf I

/-- The facts of each phase that keep the bounds. -/
def Phase (q : State) : Prop :=
  match q.ctl with
  | .hdrN => q = { init with cnt := q.cnt }
  | .hdrS => q = { init with ctl := .hdrS, n := I.n, cnt := q.cnt } ∧ q.cnt ≤ I.s
  | .hdrT => q = { init with ctl := .hdrT, n := I.n, s := I.s, cnt := q.cnt } ∧ q.cnt ≤ I.t
  | .size =>
    q = { headerState I with cnt := q.cnt, depth := q.depth, len := q.len } ∧
      q.depth + 16 * Nat.size q.cnt = depthOf I ∧ q.len + 4168 * Nat.size q.cnt = lenOf I
  | .start => WalkParams I q
  | .fill =>
    WalkParams I q ∧ q.ev.vertex = ((I.s : ℕ), (I.s : ℕ)) ∧ q.ev.lower.length ≤ depthOf I ∧
      q.ev.frames = [] ∧ q.w = q.c ∧ q.j = lenOf I
  | .next =>
    WalkParams I q ∧ q.ev.lower.length = depthOf I ∧ q.ev.frames = [] ∧
      q.w = q.c / numLabels ^ (lenOf I - q.j)
  | .eval =>
    WalkParams I q ∧ q.ev.lower.length + q.ev.frames.length = depthOf I + 1 ∧ q.j < lenOf I ∧
      q.w = q.c / numLabels ^ (lenOf I - q.j)
  | .check =>
    WalkParams I q ∧ q.ev.lower.length = depthOf I ∧ q.ev.frames = [] ∧ q.j = 0 ∧
      q.w = q.c / numLabels ^ lenOf I
  | .done => True

/-- **The invariant of the run**: the bounds, and the facts of the phase. -/
def Inv (q : State) : Prop :=
  Bounds I q ∧ Phase I q

variable {I}

/-- The slot graph keeps the slots below `n`. -/
private theorem slotRotN_lt {n : ℕ} {v : ℕ × ℕ} (h₁ : v.1 < n) (h₂ : v.2 < n) (b : Label)
    (bit : Bool) :
    (slotRotN n v b bit).1.1 < n ∧ (slotRotN n v b bit).1.2 < n := by
  unfold slotRotN
  split_ifs <;> simp only <;> omega

/-- The digits left after one more step. -/
private theorem div_pow_sub_succ {c T j : ℕ} (hj : j ≠ 0) (hjT : j ≤ T) :
    c / numLabels ^ (T - j) / numLabels = c / numLabels ^ (T - (j - 1)) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ, show T - j + 1 = T - (j - 1) by omega]

/-! ### The invariant is kept -/

/-- Close a bound on a field of an explicit state. -/
local macro "bound_tac" : tactic =>
  `(tactic| first | (dsimp only; omega) | simp)

/-- The bit read in the header of the number of vertices. -/
private theorem readBit_hdrN {i : ℕ} (hi : i ≤ I.n) :
    machine.readBit I.encode { init with cnt := i } = decide (i < I.n) := by
  rw [readBit_of_addr (A := i) rfl, USTCONInstance.getD_encode_n _ hi]

private theorem inv_hdrN {i : ℕ} (hi : i ≤ I.n) :
    Inv I (step { init with cnt := i } (machine.readBit I.encode { init with cnt := i })).1 := by
  have hn := I.n_pos
  rw [readBit_hdrN hi]
  by_cases hlt : i < I.n
  · simp only [step, init, hlt, decide_true, ite_true]
    exact ⟨by constructor <;> bound_tac, rfl⟩
  · have hi' : i = I.n := by omega
    subst hi'
    simp only [step, init, lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
    exact ⟨by constructor <;> bound_tac, rfl, Nat.zero_le _⟩

private theorem inv_hdrS {i : ℕ} (hi : i ≤ I.s) :
    Inv I (step { init with ctl := .hdrS, n := I.n, cnt := i }
      (machine.readBit I.encode { init with ctl := .hdrS, n := I.n, cnt := i })).1 := by
  have hn := I.n_pos
  have hs := I.s.isLt
  rw [readBit_of_addr (A := I.n + 1 + i) rfl, USTCONInstance.getD_encode_s _ hi]
  by_cases hlt : i < I.s
  · simp only [step, init, hlt, decide_true, ite_true]
    exact ⟨by constructor <;> bound_tac, rfl, hlt⟩
  · have hi' : i = I.s := by omega
    subst hi'
    simp only [step, init, lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
    exact ⟨by constructor <;> bound_tac, rfl, Nat.zero_le _⟩

private theorem inv_hdrT {i : ℕ} (hi : i ≤ I.t) :
    Inv I (step { init with ctl := .hdrT, n := I.n, s := I.s, cnt := i }
      (machine.readBit I.encode { init with ctl := .hdrT, n := I.n, s := I.s, cnt := i })).1 := by
  have hn := I.n_pos
  have hs := I.s.isLt
  have ht := I.t.isLt
  rw [readBit_of_addr (A := I.n + 1 + I.s + 1 + i) rfl, USTCONInstance.getD_encode_t _ hi]
  by_cases hlt : i < I.t
  · simp only [step, init, hlt, decide_true, ite_true]
    exact ⟨by constructor <;> bound_tac, rfl, hlt⟩
  · have hi' : i = I.t := by omega
    subst hi'
    simp only [step, init, lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
    refine ⟨⟨le_rfl, le_rfl, by bound_tac, by bound_tac, ?_, ?_, by bound_tac, by bound_tac,
      by bound_tac, by bound_tac, by bound_tac, by bound_tac, by bound_tac⟩, rfl, ?_, ?_⟩
    · simp only [depthOf, depth]; omega
    · simp only [lenOf, walkLength, depth]; omega
    · simp only [depthOf, depth]; ring
    · simp only [lenOf, walkLength, depth]; ring

private theorem inv_size {m d l : ℕ} (hm : m ≤ I.n) (hd : d + 16 * Nat.size m = depthOf I)
    (hl : l + 4168 * Nat.size m = lenOf I) :
    Inv I (step { headerState I with cnt := m, depth := d, len := l }
      (machine.readBit I.encode { headerState I with cnt := m, depth := d, len := l })).1 := by
  have hn := I.n_pos
  have hs := I.s.isLt
  have ht := I.t.isLt
  rw [readBit_of_addr_none rfl]
  rcases Nat.eq_zero_or_pos m with rfl | hm₀
  · simp only [Nat.size_zero, mul_zero, add_zero] at hd hl
    simp only [step, headerState, init, ite_true]
    exact ⟨by constructor <;> bound_tac, rfl, rfl, rfl, hd, hl⟩
  · have hsz := Nat.size_div_two_add_one hm₀.ne'
    simp only [step, headerState, init, hm₀.ne', ite_false]
    refine ⟨by constructor <;> bound_tac, rfl, ?_, ?_⟩ <;> dsimp only <;> omega

private theorem inv_start {q : State} (hb : Bounds I q) (hc : q.ctl = .start)
    (hp : WalkParams I q) :
    Inv I (step q (machine.readBit I.encode q)).1 := by
  obtain ⟨hn, hs, ht, hd, hl⟩ := hp
  have hsn := I.s.isLt
  rw [readBit_of_addr_none (by simp [addr, hc])]
  simp only [step, hc]
  exact ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hb.c, hb.c, hl.le,
    by dsimp only; omega, by dsimp only; omega, by simp, by simp⟩,
    ⟨hn, hs, ht, hd, hl⟩, by simp [hs], by simp, rfl, rfl, hl⟩

private theorem inv_fill {q : State} (hb : Bounds I q) (hc : q.ctl = .fill) (hp : WalkParams I q)
    (hv : q.ev.vertex = ((I.s : ℕ), (I.s : ℕ))) (hlow : q.ev.lower.length ≤ depthOf I)
    (hfr : q.ev.frames = []) (hw : q.w = q.c) (hj : q.j = lenOf I) :
    Inv I (step q (machine.readBit I.encode q)).1 := by
  have hp' := hp
  obtain ⟨hn, hs, ht, hd, hl⟩ := hp
  rw [readBit_of_addr_none (by simp [addr, hc])]
  by_cases hlen : q.ev.lower.length = q.depth
  · simp only [step, hc, hlen, ite_true]
    exact ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hb.c, hb.w, hb.j, hb.v₁, hb.v₂, hb.lower,
      hb.frames⟩, hp', by rw [hlen, hd], hfr, by simp [hw, hj]⟩
  · simp only [step, hc, hlen, ite_false]
    refine ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hb.c, hb.w, hb.j, hb.v₁, hb.v₂, ?_,
      hb.frames⟩, hp', hv, ?_, hfr, hw, hj⟩ <;> simp only [List.length_cons] <;> omega

private theorem inv_next {q : State} (hb : Bounds I q) (hc : q.ctl = .next) (hp : WalkParams I q)
    (hlow : q.ev.lower.length = depthOf I) (hfr : q.ev.frames = [])
    (hw : q.w = q.c / numLabels ^ (lenOf I - q.j)) :
    Inv I (step q (machine.readBit I.encode q)).1 := by
  rw [readBit_of_addr_none (by simp [addr, hc])]
  by_cases hj : q.j = 0
  · simp only [step, hc, hj, ite_true]
    exact ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hb.c, hb.w, Nat.zero_le _, hb.v₁, hb.v₂,
      hb.lower, hb.frames⟩, hp, hlow, hfr, rfl, by simpa [hj] using hw⟩
  · simp only [step, hc, hj, ite_false]
    have hjT := hb.j
    refine ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hb.c,
      (Nat.div_le_self _ _).trans hb.w, by dsimp only; omega, hb.v₁, hb.v₂, hb.lower,
      by simp⟩, hp, by simp [hlow], by dsimp only; omega, ?_⟩
    simp only [hw]
    exact div_pow_sub_succ hj hjT

private theorem inv_eval {q : State} (hb : Bounds I q) (hc : q.ctl = .eval) (hp : WalkParams I q)
    (hlen : q.ev.lower.length + q.ev.frames.length = depthOf I + 1) (hj : q.j < lenOf I)
    (hw : q.w = q.c / numLabels ^ (lenOf I - q.j)) :
    Inv I (step q (machine.readBit I.encode q)).1 := by
  by_cases hfr : q.ev.frames = []
  · simp only [step, hc, hfr, ite_true]
    have hlow : q.ev.lower.length = depthOf I + 1 := by simpa [hfr] using hlen
    refine ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hb.c, hb.w, hb.j, hb.v₁, hb.v₂,
      by simp [hlow], by simp⟩, hp, by simp [hlow], rfl, hw⟩
  · simp only [step, hc, hfr, ite_false]
    have hsum := length_lower_add_length_frames_reingoldEvalStep base baseEquiv
      (slotRot q.n (machine.readBit I.encode q)) q.ev
    have hv := reingoldEvalStep_vertex base baseEquiv
      (P := fun v : ℕ × ℕ ↦ v.1 < I.n ∧ v.2 < I.n)
      (rotG := slotRot q.n (machine.readBit I.encode q))
      (fun v b hv ↦ by rw [hp.1]; exact slotRotN_lt hv.1 hv.2 _ _) (s := q.ev) ⟨hb.v₁, hb.v₂⟩
    refine ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hb.c, hb.w, hb.j, hv.1, hv.2,
      by dsimp only; omega, by dsimp only; omega⟩, hp, by dsimp only; omega, hj, hw⟩

private theorem inv_check {q : State} (hb : Bounds I q) (hc : q.ctl = .check) (hp : WalkParams I q)
    (hw : q.w = q.c / numLabels ^ lenOf I) :
    Inv I (step q (machine.readBit I.encode q)).1 := by
  rw [readBit_of_addr_none (by simp [addr, hc])]
  by_cases hw₀ : q.w ≠ 0
  · simp only [step, hc, hw₀, ne_eq, not_false_eq_true, ite_true]
    exact ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hb.c, hb.w, hb.j, hb.v₁, hb.v₂, hb.lower,
      hb.frames⟩, trivial⟩
  · have hw₀' : q.w = 0 := by simpa using hw₀
    by_cases hvt : q.ev.vertex.1 = q.t
    · simp only [step, hc, hw₀', hvt, ne_eq, not_true_eq_false, ite_false, ite_true]
      exact ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hb.c, Nat.zero_le _, hb.j, hb.v₁, hb.v₂,
        hb.lower, hb.frames⟩, trivial⟩
    · simp only [step, hc, hw₀', hvt, ne_eq, not_true_eq_false, ite_false]
      have hlt : q.c < numLabels ^ lenOf I := by
        rw [hw₀', eq_comm, Nat.div_eq_zero_iff] at hw
        rcases hw with h | h
        · exact absurd h (pow_pos numLabels_pos _).ne'
        · exact h
      exact ⟨⟨hb.cnt, hb.n, hb.s, hb.t, hb.depth, hb.len, hlt, Nat.zero_le _, hb.j, hb.v₁, hb.v₂,
        hb.lower, hb.frames⟩, hp⟩

/-- **The invariant is kept by a step.** -/
private theorem inv_step {q : State} (h : Inv I q) (hd : q.ctl ≠ .done) :
    Inv I (step q (machine.readBit I.encode q)).1 := by
  obtain ⟨hb, hp⟩ := h
  rcases hc : q.ctl with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [Phase, hc] at hp
  · rw [hp]; exact inv_hdrN (hp ▸ hb.cnt)
  · rw [hp.1]; exact inv_hdrS hp.2
  · rw [hp.1]; exact inv_hdrT hp.2
  · rw [hp.1]; exact inv_size (hp.1 ▸ hb.cnt) hp.2.1 hp.2.2
  · exact inv_start hb hc hp
  · exact inv_fill hb hc hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2
  · exact inv_next hb hc hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  · exact inv_eval hb hc hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  · exact inv_check hb hc hp.1 hp.2.2.2.2
  · exact absurd hc hd

/-- The initial state satisfies the invariant. -/
private theorem inv_init : Inv I init := by
  have hn := I.n_pos
  exact ⟨⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, hn, hn, Nat.zero_le _, Nat.zero_le _⟩, rfl⟩

/-- **The states along the run satisfy the invariant.** -/
theorem inv_run (k : ℕ) : Inv I (machine.run I.encode k).state := by
  induction k with
  | zero => exact inv_init
  | succ k ih =>
    rw [Turing.ReadMachine.run_add, Turing.ReadMachine.runFrom_one]
    by_cases hd : (machine.run I.encode k).state.ctl = .done
    · have : machine.halt (machine.run I.encode k).state = true := decide_eq_true hd
      simp only [Turing.ReadMachine.next, this, ite_true]
      exact ih
    · have : machine.halt (machine.run I.encode k).state = false := decide_eq_false hd
      simp only [Turing.ReadMachine.next, this, Bool.false_eq_true, ite_false]
      exact inv_step ih hd

/-! ### The size of the states -/

/-- The encoded labels of a list, each by its rank. -/
private theorem length_encList_finEnum_le {α : Type} [FinEnum α] (l : List α) :
    (encList (encFinEnum α) l).length ≤ l.length * (2 * Nat.card α + 1) := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons a l ih =>
    have := length_encFinEnum_lt a
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

/-- The counters have at most `65 T + 1` binary digits, as `B ≤ 2 ^ 65`. -/
private theorem size_le_of_le_pow {x T : ℕ} (h : x ≤ numLabels ^ T) : Nat.size x ≤ 65 * T + 1 := by
  refine (Nat.size_le_size h).trans (Nat.size_le.2 ?_)
  calc numLabels ^ T ≤ (2 ^ 65) ^ T := Nat.pow_le_pow_left (by norm_num [numLabels]) T
    _ = 2 ^ (65 * T) := (pow_mul _ _ _).symm
    _ < 2 ^ (65 * T + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- There are ten control states. -/
private theorem card_ctl : Nat.card Ctl = 10 := by
  rw [Nat.card_eq_fintype_card]
  rfl

/-- There are seven program counters. -/
private theorem card_pc : Nat.card ReingoldPc = 7 := by
  rw [Nat.card_eq_fintype_card]
  rfl

/-- There are `257 ^ 8` labels. -/
private theorem natCard_label : Nat.card Label = 257 ^ 8 := by
  rw [Nat.card_eq_fintype_card, card_label]

/-- There are `7 · 257 ^ 8` frames. -/
private theorem card_frame : Nat.card (ReingoldPc × Label) = 7 * 257 ^ 8 := by
  rw [Nat.card_prod, card_pc, natCard_label]

/-- The constant of the size of the states. -/
def stateConst : ℕ :=
  64 * (11 + (2 * 257 ^ 8 + 1 + (2 * (7 * 257 ^ 8) + 1)) * 525 + 200000000)

/-- **The states satisfying the bounds have `O(log n)` bits**: at most a constant times the number
of binary digits of `n`, plus one. -/
private theorem length_encState_le_of_bounds {q : State} (hb : Bounds I q) :
    (encState q).length ≤ stateConst * (Nat.size I.n + 1) := by
  set a := Nat.size I.n
  have hD : depthOf I = 16 * a + 524 := rfl
  have hT : lenOf I = 4168 * a + 136240 := by simp only [lenOf, walkLength, depth]; ring
  have hle {x : ℕ} (hx : x ≤ I.n) : (encNat x).length ≤ a := by
    rw [length_encNat_eq_size]; exact Nat.size_le_size hx
  have h₁ := hle hb.cnt
  have h₂ := hle hb.n
  have h₃ := hle hb.s
  have h₄ := hle hb.t
  have h₅ := hle hb.v₁.le
  have h₆ := hle hb.v₂.le
  have h₇ : (encNat q.depth).length ≤ 16 * a + 524 :=
    (length_encNat_le_self _).trans (hD ▸ hb.depth)
  have h₈ : (encNat q.len).length ≤ 4168 * a + 136240 :=
    (length_encNat_le_self _).trans (hT ▸ hb.len)
  have h₉ : (encNat q.j).length ≤ 4168 * a + 136240 :=
    (length_encNat_le_self _).trans (hT ▸ hb.j)
  have h₁₀ : (encNat q.c).length ≤ 65 * (4168 * a + 136240) + 1 := by
    rw [length_encNat_eq_size, ← hT]; exact size_le_of_le_pow hb.c
  have h₁₁ : (encNat q.w).length ≤ 65 * (4168 * a + 136240) + 1 := by
    rw [length_encNat_eq_size, ← hT]; exact size_le_of_le_pow hb.w
  have h₁₂ : (encCtl q.ctl).length ≤ 10 := card_ctl ▸ (length_encFinEnum_lt _).le
  have h₁₃ : (encList encLab q.ev.lower).length ≤ (16 * a + 525) * (2 * Nat.card Label + 1) :=
    (length_encList_finEnum_le _).trans (Nat.mul_le_mul_right _ (by have := hb.lower; omega))
  have h₁₄ : (encList encFrame q.ev.frames).length ≤
      (16 * a + 525) * (2 * Nat.card (ReingoldPc × Label) + 1) :=
    (length_encList_finEnum_le _).trans (Nat.mul_le_mul_right _ (by have := hb.frames; omega))
  rw [natCard_label] at h₁₃
  rw [card_frame] at h₁₄
  refine (length_encState_le q).trans ?_
  rw [stateConst, mul_assoc]
  apply Nat.mul_le_mul_left
  nlinarith

/-- **The states along the run have logarithmically many bits.** -/
theorem length_encState_run_le (k : ℕ) :
    (encState (machine.run I.encode k).state).length ≤
      stateConst * (Nat.log2 I.encode.length + 2) :=
  (length_encState_le_of_bounds (inv_run k).1).trans
    (Nat.mul_le_mul_left _ (by have := I.size_n_le_log2; omega))

end Cslib.USTCON.Reader
