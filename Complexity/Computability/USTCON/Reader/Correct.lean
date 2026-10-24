/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.USTCON.Reader.Defs
import Complexity.Foundations.Data.Nat.Bits

/-!
# Correctness of the read machine for undirected connectivity

On the encoding of an instance `I`, the read machine `Cslib.USTCON.Reader.machine` halts with the
output `[true]` if `t` is reachable from `s` and `[false]` otherwise
(`Cslib.USTCON.Reader.exists_run_eq`). Correctness is claimed only on encodings of instances, as
computability with respect to an encoding requires; recognising which bit strings are encodings is
not formalised.

The proof follows the phases of the machine. The header is counted bit by bit, and the halvings of
`n` give the depth and the walk length of Reingold's graph for `a = Nat.size n`. A walk starts at
the vertex over the slot `(s, s)` with all labels zero, and each step evaluates the rotation map in
place: the evaluation on slots written as pairs of numbers follows the evaluation on `Fin n × Fin n`
(`Cslib.RotationMap.iterate_reingoldEvalStep_mapVertex`), whose step of the original graph is the
rotation map of the regular rotation map of the instance (`Cslib.USTCON.Reader.slotRotN_val`),
reading the adjacency matrix, so it computes the rotation map of Reingold's graph
(`Cslib.RotationMap.exists_iterate_reingoldEvalStep`). The labels of the walk of the counter `c`
are the digits of `c` in base `257 ^ 8`, and every sequence of labels is the sequence of digits of
some counter below `(257 ^ 8) ^ T`, so the machine accepts exactly when some walk of length `T` ends
over a slot of `t`, which is reachability of `t` by
`Cslib.Reachability.Reingold.reachable_iff_exists_walk_of_le_two_pow`.

## Main results

* `Cslib.USTCON.Reader.slotRotN_val`: the step of the slot graph on pairs of numbers.
* `Cslib.USTCON.Reader.exists_run_eq`: the machine decides undirected connectivity.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
-/

@[expose] public section

namespace Cslib.USTCON.Reader

open Cslib.RotationMap Cslib.Reachability.Reingold Cslib.Complexity

/-! ### The step of the slot graph -/

/-- The slots of `Fin n × Fin n` as pairs of numbers. -/
def slotVal {n : ℕ} (v : Fin n × Fin n) : ℕ × ℕ :=
  ((v.1 : ℕ), (v.2 : ℕ))

/-- **The step of the slot graph on pairs of numbers**: given the entry of the adjacency matrix at
the slot, `slotRotN` is the rotation map of the regular rotation map of the instance, read through
the values of the slots. -/
theorem slotRotN_val (I : USTCONInstance) (v : Fin I.n × Fin I.n) (b : Label) :
    slotRotN I.n (slotVal v) b (I.adj v.1 v.2) =
      Prod.map slotVal id ((input I.graph).rot (v, b)) := by
  obtain ⟨v₁, v₂⟩ := v
  have hrot (d : SlotLabel) : (input I.graph).rot ((v₁, v₂), slotLabel d) =
      Prod.map id slotLabel ((slotGraph I.graph (finRotate I.n)).rot ((v₁, v₂), d)) :=
    rot_extendLabels_apply _ _ (v₁, v₂) d
  have hne₁ : slotLabel (.inr ((), (), false)) ≠ slotLabel (.inl ()) :=
    fun h ↦ by simpa using slotLabel.injective h
  have hne₂ : slotLabel (.inr ((), (), true)) ≠ slotLabel (.inl ()) :=
    fun h ↦ by simpa using slotLabel.injective h
  have hne₃ : slotLabel (.inr ((), (), true)) ≠ slotLabel (.inr ((), (), false)) :=
    fun h ↦ by simpa using slotLabel.injective h
  unfold slotRotN
  by_cases h₁ : b = slotLabel (.inl ())
  · subst h₁
    rw [ite_eq_left rfl, hrot]
    by_cases hadj : I.adj v₁ v₂ = true <;> simp [slotSwap, hadj, slotVal]
  by_cases h₂ : b = slotLabel (.inr ((), (), false))
  · subst h₂
    rw [ite_eq_right hne₁, ite_eq_left rfl, hrot]
    simp only [rot_slotGraph_inr_false, Prod.map, slotVal, id, val_finRotate]
    congr 3
  by_cases h₃ : b = slotLabel (.inr ((), (), true))
  · subst h₃
    rw [ite_eq_right hne₂, ite_eq_right hne₃, ite_eq_left rfl, hrot]
    simp only [rot_slotGraph_inr_true, Prod.map, slotVal, id, val_finRotate_symm]
    congr 3
  rw [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃, input,
    rot_extendLabels_of_forall_ne _ _ _ (by rintro (⟨⟩ | ⟨⟨⟩, ⟨⟩, _ | _⟩) h <;> simp_all)]
  rfl

/-! ### Runs without output -/

variable (I : USTCONInstance)

/-- `q'` is reached from `q` on the encoding of `I`, without output. -/
def Reaches (q q' : State) : Prop :=
  ∀ o, ∃ k, machine.runFrom I.encode ⟨q, o⟩ k = ⟨q', o⟩

variable {I}

theorem Reaches.refl (q : State) : Reaches I q q :=
  fun _ ↦ ⟨0, rfl⟩

theorem Reaches.trans {q₁ q₂ q₃ : State} (h₁ : Reaches I q₁ q₂) (h₂ : Reaches I q₂ q₃) :
    Reaches I q₁ q₃ := fun o ↦
  let ⟨k₁, hk₁⟩ := h₁ o
  let ⟨k₂, hk₂⟩ := h₂ o
  ⟨k₁ + k₂, by rw [Turing.ReadMachine.runFrom_add, hk₁, hk₂]⟩

/-- One step without output. -/
private theorem Reaches.single {q q' : State} (hh : q.ctl ≠ .done)
    (hs : step q (machine.readBit I.encode q) = (q', [])) : Reaches I q q' := fun o ↦
  ⟨1, by
    rw [Turing.ReadMachine.runFrom_one, Turing.ReadMachine.next_of_not_halt _ _
      (by simp [machine, hh])]
    simp only [machine] at hs ⊢
    rw [hs, List.append_nil]⟩

/-- Steps along a sequence of states. -/
private theorem reaches_iterate (f : ℕ → State) (m : ℕ) (h : ∀ i < m, Reaches I (f i) (f (i + 1))) :
    Reaches I (f 0) (f m) := by
  induction m with
  | zero => exact .refl _
  | succ m ih => exact (ih fun i hi ↦ h i (by omega)).trans (h m (by omega))

/-- The bit read at an address. -/
theorem readBit_of_addr {q : State} {A : ℕ} (h : addr q = some A) :
    machine.readBit I.encode q = I.encode.getD A false := by
  simp [Turing.ReadMachine.readBit, machine, h]

/-- No bit is read without an address. -/
theorem readBit_of_addr_none {q : State} (h : addr q = none) :
    machine.readBit I.encode q = false := by
  simp [Turing.ReadMachine.readBit, machine, h]

/-! ### The header -/

/-- The state after the header: the number of vertices, the source and the target are counted,
and the halvings start from the depth `524` and the walk length `136240`. -/
def headerState (I : USTCONInstance) : State :=
  { init with
    ctl := .size
    n := I.n
    s := I.s
    t := I.t
    cnt := I.n
    depth := 524
    len := 136240 }

/-- **The header**: the machine counts the number of vertices, the source and the target. -/
private theorem reaches_header : Reaches I init (headerState I) := by
  -- the number of vertices
  have h₁ : Reaches I init { init with ctl := .hdrS, n := I.n } := by
    refine (reaches_iterate (fun i ↦ { init with cnt := i }) I.n
      fun i hi ↦ .single (by simp [init]) ?_) |>.trans (.single (by simp [init]) ?_)
    · rw [readBit_of_addr (A := i) rfl, USTCONInstance.getD_encode_n _ hi.le]
      simp [step, init, hi]
    · rw [readBit_of_addr (A := I.n) rfl, USTCONInstance.getD_encode_n _ le_rfl]
      simp [step, init]
  -- the source
  have h₂ : Reaches I { init with ctl := .hdrS, n := I.n }
      { init with ctl := .hdrT, n := I.n, s := I.s } := by
    refine (reaches_iterate (fun i ↦ { init with ctl := .hdrS, n := I.n, cnt := i }) I.s
      fun i hi ↦ .single (by simp) ?_) |>.trans (.single (by simp) ?_)
    · rw [readBit_of_addr (A := I.n + 1 + i) rfl, USTCONInstance.getD_encode_s _ hi.le]
      simp [step, init, hi]
    · rw [readBit_of_addr (A := I.n + 1 + I.s) rfl, USTCONInstance.getD_encode_s _ le_rfl]
      simp [step, init]
  -- the target
  have h₃ : Reaches I { init with ctl := .hdrT, n := I.n, s := I.s } (headerState I) := by
    refine (reaches_iterate (fun i ↦ { init with ctl := .hdrT, n := I.n, s := I.s, cnt := i })
      I.t fun i hi ↦ .single (by simp) ?_) |>.trans (.single (by simp) ?_)
    · rw [readBit_of_addr (A := I.n + 1 + I.s + 1 + i) rfl, USTCONInstance.getD_encode_t _ hi.le]
      simp [step, init, hi]
    · rw [readBit_of_addr (A := I.n + 1 + I.s + 1 + I.t) rfl,
        USTCONInstance.getD_encode_t _ le_rfl]
      simp [step, init, headerState]
  exact h₁.trans (h₂.trans h₃)

/-- **The halvings**: halving `m` until it vanishes adds `16` to the depth and `4168` to the walk
length for each of its binary digits. -/
private theorem reaches_size (q : State) (m d l : ℕ) :
    Reaches I { q with ctl := .size, cnt := m, depth := d, len := l }
      { q with
        ctl := .start
        cnt := 0
        c := 0
        depth := d + 16 * Nat.size m
        len := l + 4168 * Nat.size m } := by
  induction m using Nat.strong_induction_on generalizing d l with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine .single (by simp) ?_
      rw [readBit_of_addr_none rfl]
      simp [step]
    · refine (Reaches.single
        (q' := { q with ctl := .size, cnt := m / 2, depth := d + 16, len := l + 4168 })
        (by simp) ?_).trans ?_
      · rw [readBit_of_addr_none rfl]
        simp [step, hm.ne']
      · have h := ih (m / 2) (Nat.div_lt_self hm (by norm_num)) (d + 16) (l + 4168)
        have hs := Nat.size_div_two_add_one hm.ne'
        have e₁ : d + 16 * Nat.size m = d + 16 + 16 * Nat.size (m / 2) := by rw [← hs]; ring
        have e₂ : l + 4168 * Nat.size m = l + 4168 + 4168 * Nat.size (m / 2) := by
          rw [← hs]; ring
        rw [e₁, e₂]
        exact h

/-! ### Evaluating the rotation map -/

/-- If a run ends after `N` steps at a point `b` with the property `P`, and the points with the
property `P` are fixed, then the run first meets `P` at some step `k`, where it is already at
`b`. -/
private theorem exists_iterate_eq_forall_not {α : Type*} (f : α → α) (P : α → Prop)
    (hfix : ∀ a, P a → f a = a) {a b : α} {N : ℕ} (hN : f^[N] a = b) (hb : P b) :
    ∃ k, f^[k] a = b ∧ ∀ i < k, ¬P (f^[i] a) := by
  classical
  have hex : ∃ k, P (f^[k] a) := ⟨N, hN ▸ hb⟩
  refine ⟨Nat.find hex, ?_, fun i hi ↦ Nat.find_min hex hi⟩
  have hk := Nat.find_spec hex
  have hle : Nat.find hex ≤ N := Nat.find_min' hex (hN ▸ hb)
  rw [← hN, show N = (N - Nat.find hex) + Nat.find hex by omega, Function.iterate_add_apply,
    Function.iterate_fixed (hfix _ hk)]

/-- The evaluation stays put when no frame is left. -/
private theorem reingoldEvalStep_of_frames_eq_nil {V : Type*} (base' : V × Label → V × Label)
    (s : ReingoldEvalState V Label) (h : s.frames = []) :
    reingoldEvalStep base baseEquiv base' s = s := by
  obtain ⟨v, _ | ⟨b, l⟩, frames⟩ := s <;> subst h <;> rfl

variable (I) in
/-- The step of the slot graph of the instance on pairs of numbers, reading the adjacency matrix
from the encoding. -/
private def inputRot (p : (ℕ × ℕ) × Label) : (ℕ × ℕ) × Label :=
  slotRotN I.n p.1 p.2 (I.encode.getD (I.n + I.s + I.t + 3 + (p.1.1 * I.n + p.1.2)) false)

/-- The step of the slot graph read from the encoding is the rotation map of the regular rotation
map of the instance. -/
private theorem inputRot_slotVal (v : Fin I.n × Fin I.n) (b : Label) :
    inputRot I (slotVal v, b) = Prod.map slotVal id ((input I.graph).rot (v, b)) := by
  rw [inputRot, ← slotRotN_val]
  congr 1
  exact USTCONInstance.getD_encode_matrix I v.1 v.2

/-- **The evaluation of the rotation map**: from a frame for level `m ≥ 1`, freshly pushed with the
label `a` above the registers of a vertex `x` of the `m`-th graph, the machine reaches the registers
of the rotation of the `m`-th graph at `(x, a)`, with the label at the far end below the frames. -/
private theorem reaches_eval (q : State) (hc : q.ctl = .eval) (hn : q.n = I.n) (hs : q.s = I.s)
    (ht : q.t = I.t) {m : ℕ} (hm : m ≠ 0) (x : IteratedProd (Fin I.n × Fin I.n) Label m)
    (a : Label)
    (hev : q.ev = (⟨(x.toList).1, (x.toList).2, [(.zig₀, a)]⟩ :
      ReingoldEvalState (Fin I.n × Fin I.n) Label).mapVertex slotVal) :
    Reaches I q { q with
      ev := (⟨(((reingold base baseEquiv (input I.graph) m).rot (x, a)).1.toList).1,
        ((reingold base baseEquiv (input I.graph) m).rot (x, a)).2 ::
          (((reingold base baseEquiv (input I.graph) m).rot (x, a)).1.toList).2, []⟩ :
        ReingoldEvalState (Fin I.n × Fin I.n) Label).mapVertex slotVal } := by
  set f := reingoldEvalStep base baseEquiv (input I.graph).rot
  set s₀ : ReingoldEvalState (Fin I.n × Fin I.n) Label := ⟨(x.toList).1, (x.toList).2, [(.zig₀, a)]⟩
  obtain ⟨N, hN⟩ := exists_iterate_reingoldEvalStep base baseEquiv (input I.graph) hm x a []
  obtain ⟨k, hk, hlt⟩ := exists_iterate_eq_forall_not f (fun s ↦ s.frames = [])
    (fun s hs ↦ reingoldEvalStep_of_frames_eq_nil _ s hs) hN rfl
  have hq : q = { q with ev := (f^[0] s₀).mapVertex slotVal } := by
    rw [Function.iterate_zero_apply, ← hev]
  rw [hq, ← hk]
  refine reaches_iterate (fun i ↦ { q with ev := (f^[i] s₀).mapVertex slotVal }) k
    fun i hi ↦ .single (by simp [hc]) ?_
  have hne : (f^[i] s₀).frames ≠ [] := hlt i hi
  simp only [step, hc]
  rw [ite_eq_right (by simpa [ReingoldEvalState.mapVertex] using hne),
    Function.iterate_succ_apply']
  congr 2
  rw [← reingoldEvalStep_mapVertex base baseEquiv slotVal (rotG' := inputRot I)
    (fun v b ↦ inputRot_slotVal v b)]
  refine reingoldEvalStep_congr base baseEquiv fun hbase b _ ↦ ?_
  simp only [slotRot, inputRot]
  congr 1
  rw [readBit_of_addr (A := I.n + I.s + I.t + 3 +
    (((f^[i] s₀).mapVertex slotVal).vertex.1 * I.n + ((f^[i] s₀).mapVertex slotVal).vertex.2))]
  simp [addr, hn, hs, ht, hbase]

/-! ### The walks -/

variable (I) in
/-- The walk in the `m`-th graph of Reingold's transformation of the instance from `x` along the
labels of the digits of `w`, for `j` steps. -/
def walkFrom {m : ℕ} :
    IteratedProd (Fin I.n × Fin I.n) Label m → ℕ → ℕ → IteratedProd (Fin I.n × Fin I.n) Label m
  | x, _, 0 => x
  | x, w, j + 1 =>
    walkFrom ((reingold base baseEquiv (input I.graph) m).neighbor x (labelOfNat w))
      (w / numLabels) j

/-- The walk along the digits of `w` is the walk along the labels `labelOfNat (w / B ^ i)`. -/
private theorem walkFrom_eq {m : ℕ} (x : IteratedProd (Fin I.n × Fin I.n) Label m) (w j : ℕ) :
    walkFrom I x w j = ((reingold base baseEquiv (input I.graph) m).pow j).neighbor x
      fun i ↦ labelOfNat (w / numLabels ^ (i : ℕ)) := by
  induction j generalizing x w with
  | zero => exact (neighbor_pow_zero _ _ _).symm
  | succ j ih =>
    rw [walkFrom, ih, neighbor_pow_succ]
    congr 1
    · simp
    · funext i
      simp only [Fin.tail, Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]

/-- The depth of Reingold's graph is positive. -/
private theorem depth_ne_zero (a : ℕ) : depth a ≠ 0 := by
  simp [depth]

/-- **The steps of a walk**: from the next step with the registers of `x`, the digits `w` and `j`
steps left, the machine reaches the end of the walk with the registers of its last vertex and the
digits `w / B ^ j` left. -/
private theorem reaches_walk {m : ℕ} (hm : m ≠ 0) (q : State) (hc : q.ctl = .next) (hn : q.n = I.n)
    (hs : q.s = I.s) (ht : q.t = I.t) (x : IteratedProd (Fin I.n × Fin I.n) Label m) (w j : ℕ)
    (hev : q.ev = ⟨slotVal x.root, (x.toList).2, []⟩) (hw : q.w = w) (hj : q.j = j) :
    Reaches I q { q with
      ctl := .check
      ev := ⟨slotVal (walkFrom I x w j).root, ((walkFrom I x w j).toList).2, []⟩
      w := w / numLabels ^ j
      j := 0 } := by
  induction j generalizing q x w with
  | zero =>
    refine .single (by simp [hc]) ?_
    rw [readBit_of_addr_none (by simp [addr, hc])]
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := q
    simp_all [step, walkFrom]
  | succ j ih =>
    set lab := labelOfNat w
    set r := (reingold base baseEquiv (input I.graph) m).rot (x, lab)
    -- the next step pushes the frame of the top level
    have h₁ : Reaches I q { q with
        ctl := .eval
        ev := (⟨(x.toList).1, (x.toList).2, [(.zig₀, lab)]⟩ :
          ReingoldEvalState (Fin I.n × Fin I.n) Label).mapVertex slotVal
        w := w / numLabels
        j := j } := by
      refine .single (by simp [hc]) ?_
      rw [readBit_of_addr_none (by simp [addr, hc])]
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := q
      simp_all [step, ReingoldEvalState.mapVertex, lab]
    -- the evaluation of the rotation map
    have h₂ := reaches_eval { q with
        ctl := .eval
        ev := (⟨(x.toList).1, (x.toList).2, [(.zig₀, lab)]⟩ :
          ReingoldEvalState (Fin I.n × Fin I.n) Label).mapVertex slotVal
        w := w / numLabels
        j := j } rfl hn hs ht hm x lab rfl
    -- the label at the far end is dropped
    have h₃ : Reaches I { q with
        ctl := .eval
        ev := (⟨(r.1.toList).1, r.2 :: (r.1.toList).2, []⟩ :
          ReingoldEvalState (Fin I.n × Fin I.n) Label).mapVertex slotVal
        w := w / numLabels
        j := j }
        { q with
          ctl := .next
          ev := ⟨slotVal r.1.root, (r.1.toList).2, []⟩
          w := w / numLabels
          j := j } := by
      refine .single (by simp) ?_
      rw [readBit_of_addr_none (by simp [addr, ReingoldEvalState.atRoot,
        ReingoldEvalState.mapVertex])]
      simp [step, ReingoldEvalState.mapVertex]
    have h₄ := ih { q with
        ctl := .next
        ev := ⟨slotVal r.1.root, (r.1.toList).2, []⟩
        w := w / numLabels
        j := j } rfl hn hs ht r.1 (w / numLabels) rfl rfl rfl
    refine h₁.trans (h₂.trans (h₃.trans ?_))
    have e₁ : walkFrom I x w (j + 1) = walkFrom I r.1 (w / numLabels) j := rfl
    have e₂ : w / numLabels ^ (j + 1) = w / numLabels / numLabels ^ j := by
      rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [e₁, e₂]
    exact h₄

/-- **A walk of a counter**: from the start of the walk of the counter `c`, the machine fills the
labels of the start vertex `(⋯ ((s, s), 0) ⋯, 0)` and walks along the digits of `c`. -/
private theorem reaches_start {m : ℕ} (hm : m ≠ 0) (q : State) (hc : q.ctl = .start)
    (hn : q.n = I.n)
    (hs : q.s = I.s) (ht : q.t = I.t) (hd : q.depth = m) :
    Reaches I q { q with
      ctl := .check
      ev := ⟨slotVal (walkFrom I (IteratedProd.mk (I.s, I.s) 0 m) q.c q.len).root,
        ((walkFrom I (IteratedProd.mk (I.s, I.s) 0 m) q.c q.len).toList).2, []⟩
      w := q.c / numLabels ^ q.len
      j := 0 } := by
  -- the start resets the registers
  have h₁ : Reaches I q { q with
      ctl := .fill
      ev := ⟨(q.s, q.s), List.replicate 0 0, []⟩
      w := q.c
      j := q.len } := by
    refine .single (by simp [hc]) ?_
    rw [readBit_of_addr_none (by simp [addr, hc])]
    simp [step, hc]
  -- the labels are filled with zeros
  have h₂ : Reaches I { q with
      ctl := .fill
      ev := ⟨(q.s, q.s), List.replicate 0 0, []⟩
      w := q.c
      j := q.len }
      { q with
        ctl := .next
        ev := ⟨(q.s, q.s), List.replicate m 0, []⟩
        w := q.c
        j := q.len } := by
    refine (reaches_iterate (fun i ↦ { q with
      ctl := .fill
      ev := ⟨(q.s, q.s), List.replicate i 0, []⟩
      w := q.c
      j := q.len }) m fun i hi ↦ .single (by simp) ?_).trans (.single (by simp) ?_)
    · rw [readBit_of_addr_none (by simp [addr])]
      simp [step, hd, hi.ne, List.replicate_succ]
    · rw [readBit_of_addr_none (by simp [addr])]
      simp [step, hd]
  have h₃ := reaches_walk hm { q with
      ctl := .next
      ev := ⟨(q.s, q.s), List.replicate m 0, []⟩
      w := q.c
      j := q.len } rfl hn hs ht (IteratedProd.mk (I.s, I.s) 0 m) q.c q.len
    (by simp [slotVal, hs]) rfl rfl
  exact h₁.trans (h₂.trans h₃)

variable (I) in
/-- The machine halts from `q` with the output `b` appended to the output so far. -/
def Outputs (q : State) (b : Bool) : Prop :=
  ∀ o, ∃ k, machine.halt (machine.runFrom I.encode ⟨q, o⟩ k).state = true ∧
    (machine.runFrom I.encode ⟨q, o⟩ k).out = o ++ [b]

/-- Steps without output before halting with an output. -/
private theorem Reaches.outputs {q q' : State} {b : Bool} (h : Reaches I q q')
    (h' : Outputs I q' b) :
    Outputs I q b := fun o ↦
  let ⟨k₁, hk₁⟩ := h o
  let ⟨k₂, hk₂⟩ := h' o
  ⟨k₁ + k₂, by rw [Turing.ReadMachine.runFrom_add, hk₁]; exact hk₂⟩

/-- Halting in one step with an output. -/
private theorem outputs_single {q q' : State} {b : Bool} (hh : q.ctl ≠ .done)
    (hs : step q (machine.readBit I.encode q) = (q', [b])) (hq' : q'.ctl = .done) :
    Outputs I q b := fun o ↦
  ⟨1, by
    rw [Turing.ReadMachine.runFrom_one, Turing.ReadMachine.next_of_not_halt _ _
      (by simp [machine, hh])]
    simp only [machine] at hs ⊢
    rw [hs]
    simp [hq']⟩

/-- At the end of a walk whose counter has more digits than the walk length, the machine
rejects. -/
private theorem outputs_check_overflow (Q : State) (hc : Q.ctl = .check) (hw : Q.w ≠ 0) :
    Outputs I Q false :=
  outputs_single (q' := { Q with ctl := .done }) (by simp [hc])
    (by rw [readBit_of_addr_none (by simp [addr, hc])]; simp [step, hc, hw]) rfl

/-- At the end of a walk over a slot of `t`, the machine accepts. -/
private theorem outputs_check_success (Q : State) (hc : Q.ctl = .check) (hw : Q.w = 0)
    (ht : Q.ev.vertex.1 = Q.t) : Outputs I Q true :=
  outputs_single (q' := { Q with ctl := .done }) (by simp [hc])
    (by rw [readBit_of_addr_none (by simp [addr, hc])]; simp [step, hc, hw, ht]) rfl

/-- At the end of a walk elsewhere, the machine starts the walk of the next counter. -/
private theorem reaches_check_next (Q : State) (hc : Q.ctl = .check) (hw : Q.w = 0)
    (ht : Q.ev.vertex.1 ≠ Q.t) : Reaches I Q { Q with c := Q.c + 1, ctl := .start } :=
  .single (by simp [hc])
    (by rw [readBit_of_addr_none (by simp [addr, hc])]; simp [step, hc, hw, ht])

variable (I) in
/-- The walk of the counter `c` succeeds: it ends over a slot of `t`. -/
def Success (m T c : ℕ) : Prop :=
  (walkFrom I (IteratedProd.mk (I.s, I.s) 0 m) c T).root.1 = I.t

open scoped Classical in
/-- **The counters**: from the start of the walk of a counter `c ≤ B ^ T`, the machine halts with
the output `[true]` if the walk of some counter between `c` and `B ^ T` succeeds, and `[false]`
otherwise. -/
private theorem outputs_start {m T : ℕ} (hm : m ≠ 0) :
    ∀ d (q : State), numLabels ^ T - q.c = d → q.c ≤ numLabels ^ T → q.ctl = .start →
      q.n = I.n → q.s = I.s → q.t = I.t → q.depth = m → q.len = T →
      Outputs I q (decide (∃ c', q.c ≤ c' ∧ c' < numLabels ^ T ∧ Success I m T c')) := by
  intro d
  induction d with
  | zero =>
    intro q hd hc₀ hc hn hs ht hd' hl
    have hcT : q.c = numLabels ^ T := by omega
    have hfalse : decide (∃ c', q.c ≤ c' ∧ c' < numLabels ^ T ∧ Success I m T c') = false := by
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro c' h₁ h₂
      omega
    rw [hfalse]
    refine (reaches_start hm q hc hn hs ht hd').outputs (outputs_check_overflow _ rfl ?_)
    simp [hl, hcT, Nat.div_self (pow_pos numLabels_pos T)]
  | succ d ih =>
    intro q hd hc₀ hc hn hs ht hd' hl
    have hcT : q.c < numLabels ^ T := by omega
    have hdiv : q.c / numLabels ^ T = 0 := Nat.div_eq_of_lt hcT
    refine (reaches_start hm q hc hn hs ht hd').outputs ?_
    by_cases hsucc : Success I m T q.c
    · have htrue : decide (∃ c', q.c ≤ c' ∧ c' < numLabels ^ T ∧ Success I m T c') = true :=
        decide_eq_true ⟨q.c, le_rfl, hcT, hsucc⟩
      rw [htrue]
      refine outputs_check_success _ rfl (by simp [hl, hdiv]) ?_
      simp only [Success] at hsucc
      simp [slotVal, ht, hl, hsucc]
    · have heq : decide (∃ c', q.c ≤ c' ∧ c' < numLabels ^ T ∧ Success I m T c') =
          decide (∃ c', q.c + 1 ≤ c' ∧ c' < numLabels ^ T ∧ Success I m T c') := by
        congr 1
        refine propext ⟨fun ⟨c', h₁, h₂, h₃⟩ ↦ ⟨c', ?_, h₂, h₃⟩, fun ⟨c', h₁, h₂, h₃⟩ ↦
          ⟨c', by omega, h₂, h₃⟩⟩
        rcases h₁.lt_or_eq with h₁ | h₁
        · exact h₁
        · exact absurd (h₁ ▸ h₃) hsucc
      rw [heq]
      have hne : ((walkFrom I (IteratedProd.mk (I.s, I.s) 0 m) q.c q.len).root.1 : ℕ) ≠ I.t := by
        intro h
        rw [hl] at h
        exact hsucc (Fin.ext h)
      refine (reaches_check_next _ rfl (by simp [hl, hdiv])
        (by simpa [slotVal, ht] using hne)).outputs ?_
      exact ih _ (by simp only; omega) (by simp only; omega) rfl hn hs ht hd' hl

/-! ### Every sequence of labels is a counter -/

/-- **Every sequence of `T` labels is the sequence of the digits of a counter below `B ^ T`.** -/
private theorem exists_labelOfNat_eq (T : ℕ) (k : Fin T → Label) :
    ∃ c < numLabels ^ T, (fun i : Fin T ↦ labelOfNat (c / numLabels ^ (i : ℕ))) = k := by
  induction T with
  | zero => exact ⟨0, by norm_num, funext fun i ↦ i.elim0⟩
  | succ T ih =>
    obtain ⟨c', hc', hk⟩ := ih (Fin.tail k)
    set d := (labelEquiv.symm (k 0) : ℕ)
    have hd : d < numLabels := (labelEquiv.symm (k 0)).isLt
    refine ⟨d + numLabels * c', ?_, funext fun i ↦ ?_⟩
    · calc d + numLabels * c' < numLabels + numLabels * c' := by omega
        _ = numLabels * (c' + 1) := by ring
        _ ≤ numLabels * numLabels ^ T := Nat.mul_le_mul_left _ hc'
        _ = numLabels ^ (T + 1) := (pow_succ' _ _).symm
    · refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp only [Fin.val_zero, pow_zero, Nat.div_one, labelOfNat]
        rw [show (⟨(d + numLabels * c') % numLabels, _⟩ : Fin numLabels) =
            labelEquiv.symm (k 0) from Fin.ext (by simp [Nat.add_mul_mod_self_left,
              Nat.mod_eq_of_lt hd, d]), Equiv.apply_symm_apply]
      · have hdiv : (d + numLabels * c') / numLabels = c' := by
          rw [Nat.add_mul_div_left _ _ numLabels_pos, Nat.div_eq_of_lt hd, zero_add]
        rw [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
        exact congrFun hk i

/-! ### The decision -/

/-- The depth computed from the header is `depth (Nat.size n)`. -/
private theorem depth_eq (a : ℕ) : 524 + 16 * a = depth a := by
  simp only [depth]; ring

/-- The walk length computed from the header is `walkLength (Nat.size n)`. -/
private theorem walkLength_eq (a : ℕ) : 136240 + 4168 * a = walkLength a := by
  simp only [walkLength, depth]; ring

open scoped Classical in
/-- **The machine decides undirected connectivity**: from the initial state, it halts with the
output `[true]` if `t` is reachable from `s`, and `[false]` otherwise. -/
private theorem outputs_init : Outputs I init (decide (I ∈ USTCON)) := by
  classical
  set a := Nat.size I.n
  have hstart := (reaches_header (I := I)).trans
    (reaches_size (headerState I) I.n 524 136240)
  have hout := outputs_start (I := I) (depth_ne_zero a) _
    { headerState I with
      ctl := .start
      cnt := 0
      c := 0
      depth := 524 + 16 * Nat.size I.n
      len := 136240 + 4168 * Nat.size I.n } rfl (Nat.zero_le _) rfl rfl rfl rfl (depth_eq a)
    (walkLength_eq a)
  refine hstart.outputs ?_
  convert hout using 2
  -- the decision is reachability
  have hreach := reachable_iff_exists_walk_of_le_two_pow I.graph (a := a)
    (Nat.lt_size_self I.n).le I.s I.t
  rw [show I ∈ USTCON ↔ I.graph.Reachable I.s I.t from Iff.rfl, hreach]
  refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨c, _, hc, hsucc⟩ ↦ ?_⟩
  · obtain ⟨c, hc, hck⟩ := exists_labelOfNat_eq (walkLength a) k
    refine ⟨c, Nat.zero_le _, hc, ?_⟩
    simp only [Success]
    rw [walkFrom_eq, hck]
    exact hk
  · refine ⟨fun i ↦ labelOfNat (c / numLabels ^ (i : ℕ)), ?_⟩
    simp only [Success] at hsucc
    rw [walkFrom_eq] at hsucc
    exact hsucc

open scoped Classical in
/-- **The read machine decides undirected connectivity**: on the encoding of an instance, it halts
with the output `[true]` if `t` is reachable from `s`, and `[false]` otherwise. -/
theorem exists_run_eq (I : USTCONInstance) :
    ∃ k, machine.halt (machine.run I.encode k).state = true ∧
      (machine.run I.encode k).out = [decide (I ∈ USTCON)] :=
  outputs_init (I := I) []

end Cslib.USTCON.Reader
