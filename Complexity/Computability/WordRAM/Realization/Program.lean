/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic

/-!
# Flat programs from graded memory-client realizations

`Realizes.exists_program` projects the existing realization certificate through
`Refines.executes`. One emitter, scratch size and exchange constant precede every runtime
argument, word width and initial memory. A statically selected coordinate of the faithful result
encoding is observed by the existing `Code.program`; its final halt costs one instruction.
The emitted body is shared by all coordinate observations.

`Realizes.exists_program` takes already installed arguments and frontier.
`Realizes.exists_init_program` instead executes `inputPrefix` from `Data.init`, charging
`2 * k + 5` instructions to install the first `k` input words and frontier. Its explicit layout,
input-word and frontier-fit premises exclude free preparation and address overflow. The initial
memory is retained in full. The whole-memory postcondition and register frame remain available
through `Realizes.exists_refines`; no new execution judgment is introduced here.

## Main definitions

* `inputLoads`: a fixed sequence loading consecutive cells into source registers.
* `inputPrefix`: the native register and frontier installation prefix.
* `inputState`: the functional memory state of the native list-input convention.

## Main results

* `Realizes.exists_program`: a uniform flat program for every static output coordinate, with
  bound `C * (memoryCost + work + 1) + 1`, including the trailing halt.
* `inputPrefix_exec`: a charged, memory-preserving native list-input prefix.
* `Realizes.exists_init_program`: the same uniform flat-program bound from `Data.init`,
  absorbing the actual prefix into its exchange constant.
* `Realizes.exists_unit_program`, `Realizes.exists_init_unit_program`: zero-output clients
  execute a zero write and halt, charging both instructions at every word width.

## References

This semantic projection is original infrastructure over the existing flat compiler.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-- Install consecutive input cells in the given source registers. The terminal self-copy
provides the empty case without adding a skip instruction to the native language. -/
def inputLoads {r : ℕ} (ptr : Fin r) :
    {k : ℕ} → (Fin k → Fin r) → ℕ → Code .exact r
  | 0, _, _ => .op (.copy ptr ptr)
  | _ + 1, src, offset =>
    .seq (.op (.const ptr (offset + 1)))
      (.seq (.op (.load (src 0) ptr)) (inputLoads ptr (fun i => src i.succ) (offset + 1)))

private theorem inputLoads_exec {r k w : ℕ} (ptr : Fin r) (src : Fin k → Fin r)
    (offset : ℕ) (x : Data r) (hi : Function.Injective src)
    (hd : ∀ i, src i ≠ ptr) (hfit : ∀ i : Fin k, Fits w (offset + i.val + 1)) :
    ∃ y, ExecWithin w (inputLoads ptr src offset) x y (2 * k + 1) ∧
      y.mem = x.mem ∧ (∀ i, y.regs (src i) = x.mem (offset + i.val + 1)) ∧
      ∀ j, j ≠ ptr → (∀ i, src i ≠ j) → y.regs j = x.regs j := by
  induction k generalizing offset x with
  | zero =>
    refine ⟨x, ?_, rfl, (fun i => Fin.elim0 i), ?_⟩
    · simpa [inputLoads, Data.set] using
        (ExecWithin.copy (B := .exact) (w := w) (x := x) (d := ptr) (s := ptr))
    · intro j _ _
      rfl
  | succ k ih =>
    let x₁ := x.set ptr (offset + 1)
    let x₂ := x₁.set (src 0) (x.mem (offset + 1))
    have e₁ : ExecWithin (B := .exact) w (.op (.const ptr (offset + 1))) x x₁ 1 :=
      ExecWithin.const (by simpa using hfit 0)
    have e₂ : ExecWithin (B := .exact) w (.op (.load (src 0) ptr)) x₁ x₂ 1 := by
      simpa [x₂, x₁] using
        (ExecWithin.load (B := .exact) (w := w) (x := x₁) (d := src 0) (a := ptr))
    obtain ⟨y, ey, hm, ho, hf⟩ := ih (fun i => src i.succ) (offset + 1) x₂
      (hi.comp (Fin.succ_injective _)) (fun i => hd i.succ)
      (fun i => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfit i.succ)
    refine ⟨y, ?_, hm, ?_, ?_⟩
    · exact (e₁.seq (e₂.seq ey)).mono (by omega)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [hf (src 0) (hd 0) (fun j h => by
          have := hi h
          exact Fin.succ_ne_zero j this)]
        simp [x₂]
      · simpa [x₂, x₁, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ho j
    · intro j hj hs
      rw [hf j hj (fun i => hs i.succ)]
      simp [x₂, x₁, (hs 0).symm, hj]

/-- A native entry prefix installs the frontier and the first `k` input words. All data starts
from the existing `Data.init` convention; register installation is charged. -/
def inputPrefix {r k : ℕ} (frontier ptr : Fin r) (src : Fin k → Fin r) : Code .exact r :=
  .seq (.op (.const ptr 0))
    (.seq (.op (.load frontier ptr))
      (.seq (.op (.const ptr 1))
        (.seq (.op (.exactBin .add frontier frontier ptr)) (inputLoads ptr src 0))))

/-- The whole input memory, with the first free address immediately after its last word. -/
def inputState (words : List ℕ) : Memory.State :=
  ⟨(Data.init words : Data 0).mem, words.length + 1⟩

/-- Argument installation takes at most `2 * k + 5` native instructions. Its memory is unchanged;
only the frontier, pointer and source registers can change. The frontier-fit premise also pays
for the constant one and every input address. -/
theorem inputPrefix_exec {r k w : ℕ} (frontier ptr : Fin r) (src : Fin k → Fin r)
    (words : List ℕ) (hi : Function.Injective src) (hp : ptr ≠ frontier)
    (hd : ∀ i, src i ≠ ptr) (hf : ∀ i, src i ≠ frontier)
    (hk : k ≤ words.length) (hw : Fits w (words.length + 1)) (hin : InputFits w words) :
    ∃ y, ExecWithin w (inputPrefix frontier ptr src) (Data.init words) y (2 * k + 5) ∧
      y.Bounded w ∧ memoryState frontier y = inputState words ∧
      (∀ i, y.regs (src i) = words.getD i.val 0) ∧
      ∀ j, j ≠ frontier → j ≠ ptr → (∀ i, src i ≠ j) → y.regs j = 0 := by
  let x : Data r := Data.init words
  let x₁ := x.set ptr 0
  let x₂ := x₁.set frontier words.length
  let x₃ := x₂.set ptr 1
  let x₄ := x₃.set frontier (words.length + 1)
  have h1 : Fits w 1 := hw.of_le (by omega)
  have e₁ : ExecWithin (B := .exact) w (.op (.const ptr 0)) x x₁ 1 := ExecWithin.const (fits_zero w)
  have e₂ : ExecWithin (B := .exact) w (.op (.load frontier ptr)) x₁ x₂ 1 := by
    simpa [x₂, x₁, x] using
      (ExecWithin.load (B := .exact) (w := w) (x := x₁) (d := frontier) (a := ptr))
  have e₃ : ExecWithin (B := .exact) w (.op (.const ptr 1)) x₂ x₃ 1 := ExecWithin.const h1
  have e₄ : ExecWithin w (.op (.exactBin .add frontier frontier ptr)) x₃ x₄ 1 := by
    apply ExecWithin.op
    simp [Op.eval_exactBin, BinOp.evalExact, x₄, x₃, x₂, hp.symm, Data.put_of_fits hw]
  obtain ⟨y, ey, hm, ho, hframe⟩ := inputLoads_exec ptr src 0 x₄ hi hd
    (fun i => hw.of_le (by omega))
  have he : ExecWithin w (inputPrefix frontier ptr src) x y (2 * k + 5) := by
    exact (e₁.seq (e₂.seq (e₃.seq (e₄.seq ey)))).mono (by omega)
  refine ⟨y, he, he.bounded (Data.Bounded.init hin), ?_, ?_, ?_⟩
  · apply Memory.State.ext
    · exact hm
    · change y.regs frontier = words.length + 1
      rw [hframe frontier hp.symm hf]
      simp [x₄]
  · intro i
    simpa [x₄, x₃, x₂, x₁, x] using ho i
  · intro j hj hptr hs
    rw [hframe j hptr hs]
    simp [x₄, x₃, x₂, x₁, x, hj, hptr]

end Cslib.WordRAM.Realization

namespace Cslib.WordRAM.Realization.Realizes

open Cslib.DataStructure

variable {B : Basis} {k l : ℕ} {δ α : Type}
  {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
  {output : α ↪ (Fin l → ℕ)} {safe : ℕ → δ → Memory.State → Prop}
  {work : δ → Memory.State → ℕ}

/-- Each static coordinate of a faithfully encoded result has one flat program, independent of
the runtime input, width and memory. The selected halt observes an output register of the same
emitted body; the clock includes that halt. Arguments and frontier are explicit entry premises.
For an empty result register vector this makes no scalar observation. -/
theorem exists_program (h : Realizes B p input output safe work) :
    ∃ n C : ℕ,
      ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
          (Fin (l + n + 1) → Fin r) → Code B r,
        ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
          (tmp : Fin (l + n + 1) → Fin r),
          Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
          (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
          ∀ (i : Fin l) (w : ℕ) (d : δ) (x : Data r),
          x.Bounded w → x.regs ∘ src = input d → safe w d (memoryState frontier x) →
          (Memory.spec w).ValidHistory (memoryState frontier x)
            ((Memory.spec w).clientHistory (memoryState frontier x) (p d)) →
          ∃ t, Executes w ((emit frontier src tmp).program (tmp (Fin.castAdd (n + 1) i)))
              ⟨0, x⟩ (output ((Memory.spec w).clientResult (memoryState frontier x) (p d)) i) t ∧
            t ≤ C * (memoryCost (p d) (memoryState frontier x) +
              work d (memoryState frontier x) + 1) + 1 := by
  obtain ⟨n, C, emit, he⟩ := h.exists_refines
  refine ⟨n, C, emit, ?_⟩
  intro r frontier src tmp hi hd hf hs i w d x hx hin hsafe hv
  exact (he frontier src tmp hi hd hf hs w d).executes
    (tmp (Fin.castAdd (n + 1) i)) (fun a => output a i) (fun _ _ _ hout => hout.2 i)
    ⟨rfl, hx, hin, hsafe, hv⟩

/-- A flat exact-basis program starts from the native list-input convention and charges both
argument installation and its trailing halt. The first `k` cells encode the argument; the whole
input memory and its frontier are passed to the client. The fixed installation cost is absorbed
into one exchange constant before every width and runtime argument. -/
theorem exists_init_program (h : Realizes .exact p input output safe work)
    (raw : δ → List ℕ) (hlayout : ∀ d (i : Fin k), (raw d).getD i.val 0 = input d i) :
    ∃ n C : ℕ,
      ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
          (Fin (l + n + 1) → Fin r) → Code .exact r,
        ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
          (tmp : Fin (l + n + 1) → Fin r),
          Function.Injective src → Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
          (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
          ∀ (i : Fin l) (w : ℕ) (d : δ),
          k ≤ (raw d).length → Fits w ((raw d).length + 1) → InputFits w (raw d) →
          safe w d (inputState (raw d)) →
          (Memory.spec w).ValidHistory (inputState (raw d))
            ((Memory.spec w).clientHistory (inputState (raw d)) (p d)) →
          ∃ t, Executes w
              ((Code.seq (inputPrefix frontier (tmp (Fin.last (l + n))) src)
                (emit frontier src tmp)).program (tmp (Fin.castAdd (n + 1) i)))
              (State.init (raw d))
              (output ((Memory.spec w).clientResult (inputState (raw d)) (p d)) i) t ∧
            t ≤ C * (memoryCost (p d) (inputState (raw d)) +
              work d (inputState (raw d)) + 1) + 1 := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C + (2 * k + 5), emit, ?_⟩
  intro r frontier src tmp hsrc htmp hd hf hs i w d hk hw hin hsafe hv
  obtain ⟨x, ex, hx, hm, hwords, _⟩ :=
    inputPrefix_exec frontier (tmp (Fin.last (l + n))) src (raw d) hsrc
      (hf _) (fun j => hd j _) hs hk hw hin
  have harg : x.regs ∘ src = input d := by
    funext j
    exact (hwords j).trans (hlayout d j)
  obtain ⟨y, ey, _, hout, _⟩ := (he frontier src tmp htmp hd hf hs).2 w d x hx harg
    (hm.symm ▸ hsafe) (hm.symm ▸ hv)
  rw [hm] at ey hout
  obtain ⟨t, ht, et⟩ := ex.seq ey
  refine ⟨t + 1, ?_, ?_⟩
  · simpa only [State.init, hout i] using et.executes (tmp (Fin.castAdd (n + 1) i))
  · have hpos : 1 ≤ memoryCost (p d) (inputState (raw d)) +
        work d (inputState (raw d)) + 1 := by omega
    have hover := Nat.mul_le_mul_left (2 * k + 5) hpos
    simp only [Nat.mul_one] at hover
    rw [Nat.add_mul]
    omega

/-- A Unit-returning client needs no output coordinate. Execute an actual zero constant after
its body to obtain a scalar observation, preserving the entire represented client state.
The extra instruction fits every width, including zero. -/
theorem exists_unit_refines {p : δ → Memory.Prog Unit} {output : Unit ↪ (Fin 0 → ℕ)}
    (h : Realizes B p input output safe work) :
    ∃ n C : ℕ,
      ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
          (Fin (0 + n + 1) → Fin r) → Code B r,
        ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
          (tmp : Fin (0 + n + 1) → Fin r),
          Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
          (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
          ∀ (w : ℕ) (d : δ),
          Refines (D := Memory.spec w) w
            (fun s x => s = memoryState frontier x ∧ x.Bounded w ∧ x.regs ∘ src = input d ∧
              safe w d s ∧ (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)))
            (p d)
            (fun _ s y => memoryState frontier y = s ∧ y.regs (tmp 0) = 0)
            (fun s _ => C * (memoryCost (p d) s + work d s + 1) + 1)
            (.seq (emit frontier src tmp) (.op (.const (tmp 0) 0))) := by
  obtain ⟨n, C, emit, he⟩ := h.exists_refines
  refine ⟨n, C, emit, ?_⟩
  intro r frontier src tmp hi hd hf hs w d
  apply Refines.ofFn
  intro s x hx
  obtain ⟨hv, y, ey, hm, _⟩ := (he frontier src tmp hi hd hf hs w d).toOfFn hx
  refine ⟨hv, y.set (tmp 0) 0, ey.seq (ExecWithin.const (fits_zero w)), ?_, ?_⟩
  · apply Eq.trans ?_ hm
    apply Memory.State.ext
    · rfl
    · exact Function.update_of_ne (hf 0).symm _ _
  · simp

/-- A zero-output Unit client has a uniform flat scalar observation after a charged zero write
and halt. Both instructions are included, without a positive-width premise. -/
theorem exists_unit_program {p : δ → Memory.Prog Unit} {output : Unit ↪ (Fin 0 → ℕ)}
    (h : Realizes B p input output safe work) :
    ∃ n C : ℕ,
      ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
          (Fin (0 + n + 1) → Fin r) → Code B r,
        ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
          (tmp : Fin (0 + n + 1) → Fin r),
          Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
          (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
          ∀ (w : ℕ) (d : δ) (x : Data r),
          x.Bounded w → x.regs ∘ src = input d → safe w d (memoryState frontier x) →
          (Memory.spec w).ValidHistory (memoryState frontier x)
            ((Memory.spec w).clientHistory (memoryState frontier x) (p d)) →
          ∃ t, Executes w
              ((Code.seq (emit frontier src tmp) (.op (.const (tmp 0) 0))).program (tmp 0))
              ⟨0, x⟩ 0 t ∧
            t ≤ C * (memoryCost (p d) (memoryState frontier x) +
              work d (memoryState frontier x) + 1) + 2 := by
  obtain ⟨n, C, emit, he⟩ := h.exists_unit_refines
  refine ⟨n, C, emit, ?_⟩
  intro r frontier src tmp hi hd hf hs w d x hx hin hsafe hv
  simpa only [Nat.add_assoc] using
    (he frontier src tmp hi hd hf hs w d).executes (tmp 0) (fun _ => 0)
      (fun _ _ _ hout => hout.2) ⟨rfl, hx, hin, hsafe, hv⟩

/-- Unit-returning clients can start from `Data.init` too. Argument installation is charged and
absorbed into the uniform exchange constant; the real zero write and trailing halt cost two
further instructions. -/
theorem exists_init_unit_program {p : δ → Memory.Prog Unit} {output : Unit ↪ (Fin 0 → ℕ)}
    (h : Realizes .exact p input output safe work)
    (raw : δ → List ℕ) (hlayout : ∀ d (i : Fin k), (raw d).getD i.val 0 = input d i) :
    ∃ n C : ℕ,
      ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
          (Fin (0 + n + 1) → Fin r) → Code .exact r,
        ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
          (tmp : Fin (0 + n + 1) → Fin r),
          Function.Injective src → Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
          (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
          ∀ (w : ℕ) (d : δ),
          k ≤ (raw d).length → Fits w ((raw d).length + 1) → InputFits w (raw d) →
          safe w d (inputState (raw d)) →
          (Memory.spec w).ValidHistory (inputState (raw d))
            ((Memory.spec w).clientHistory (inputState (raw d)) (p d)) →
          ∃ t, Executes w
              ((Code.seq (inputPrefix frontier (tmp (Fin.last (0 + n))) src)
                (.seq (emit frontier src tmp) (.op (.const (tmp 0) 0)))).program (tmp 0))
              (State.init (raw d)) 0 t ∧
            t ≤ C * (memoryCost (p d) (inputState (raw d)) +
              work d (inputState (raw d)) + 1) + 2 := by
  obtain ⟨n, C, emit, he⟩ := h.exists_unit_refines
  refine ⟨n, C + (2 * k + 5), emit, ?_⟩
  intro r frontier src tmp hsrc htmp hd hf hs w d hk hw hin hsafe hv
  obtain ⟨x, ex, hx, hm, hwords, _⟩ :=
    inputPrefix_exec frontier (tmp (Fin.last (0 + n))) src (raw d) hsrc
      (hf _) (fun j => hd j _) hs hk hw hin
  have harg : x.regs ∘ src = input d := by
    funext j
    exact (hwords j).trans (hlayout d j)
  obtain ⟨_, y, ey, _, hout⟩ := (he frontier src tmp htmp hd hf hs w d).toOfFn
    ⟨rfl, hx, harg, hm.symm ▸ hsafe, hm.symm ▸ hv⟩
  rw [hm] at ey
  obtain ⟨t, ht, et⟩ := ex.seq ey
  refine ⟨t + 1, ?_, ?_⟩
  · simpa only [State.init, hout] using et.executes (tmp 0)
  · have hpos : 1 ≤ memoryCost (p d) (inputState (raw d)) +
        work d (inputState (raw d)) + 1 := by omega
    have hover := Nat.mul_le_mul_left (2 * k + 5) hpos
    simp only [Nat.mul_one] at hover
    rw [Nat.add_mul]
    omega

end Cslib.WordRAM.Realization.Realizes
