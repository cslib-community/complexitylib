/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic

/-!
# Bounded memory-client loops

Bounded iteration remains an ordinary `Memory.Prog` term. The local-work currency counts body
work and every iteration, including iterations issuing no memory query. The native realization
uses one fixed body emitter and static registers for the mutable state and countdown counter.

## Main definitions

* `iterate`: bounded iteration in the existing memory-client monad.
* `iterationWork`, `iterationSafe`: local work and domains along the actual semantic states.

## Main results

* `copyBank_exec`: a static register-bank copy with memory and live-register frames.
* `loop_invariant_state_charged`: bounded native loops charge local work and control.
* `Realizes.iterateRuntime`: one uniform body certificate realizes a runtime-bounded loop.

The iteration grading and realization are original infrastructure over the existing free monad
and structured Word-RAM code. No additional program syntax or memory model is introduced.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {δ σ : Type} {B : Basis} {r k l : ℕ}

/-- Execute one fixed body family a runtime-bounded number of times. -/
def iterate (body : δ × σ → Memory.Prog σ) (d : δ) : ℕ → σ → Memory.Prog σ
  | 0, s => pure s
  | n + 1, s => do
      let s' ← body (d, s)
      iterate body d n s'

/-- Local computation and one control-work unit per iteration, along actual semantic states. -/
def iterationWork (body : δ × σ → Memory.Prog σ) (work : (δ × σ) → Memory.State → ℕ)
    (d : δ) : ℕ → σ → Memory.State → ℕ
  | 0, _, _ => 0
  | n + 1, a, s =>
      work (d, a) s + iterationWork body work d n
        ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a))) + 1

/-- Every executed body must satisfy its explicit domain at the reached state. -/
def iterationSafe (body : δ × σ → Memory.Prog σ)
    (safe : ℕ → (δ × σ) → Memory.State → Prop) (w : ℕ) (d : δ) :
    ℕ → σ → Memory.State → Prop
  | 0, _, _ => True
  | n + 1, a, s => safe w (d, a) s ∧ iterationSafe body safe w d n
      ((Memory.spec 0).clientResult s (body (d, a)))
      ((Memory.spec 0).clientState s (body (d, a)))

/-- Native register copies need no word-size or arithmetic side condition. -/
def copyBank : {k : ℕ} → (Fin k → Fin r) → (Fin k → Fin r) → Fin r → Code B r
  | 0, _, _, idle => .op (.copy idle idle)
  | n + 1, src, dst, idle => .seq (.op (.copy (dst 0) (src 0)))
      (copyBank (fun i : Fin n => src i.succ) (fun i => dst i.succ) idle)

/-- Copying a finite bank does not inspect the word width. -/
theorem copyBank_not_readsWidth (src dst : Fin k → Fin r) (idle : Fin r) :
    ¬(copyBank (B := B) src dst idle).ReadsWidth := by
  induction k with
  | zero => simp [copyBank, Code.ReadsWidth, Op.ReadsWidth]
  | succ n ih => simp [copyBank, Code.ReadsWidth, Op.ReadsWidth, ih]

/-- Copy disjoint source words into an injective destination bank, leaving the entire memory and
all other registers unchanged. A neutral copy supplies the zero-length code case. -/
theorem copyBank_exec (src dst : Fin k → Fin r) (idle : Fin r)
    (hi : Function.Injective dst) (hd : ∀ i j, src i ≠ dst j) (w : ℕ) (x : Data r) :
    ∃ y, ExecWithin w (copyBank (B := B) src dst idle) x y (k + 1) ∧
      y.mem = x.mem ∧ (∀ i, y.regs (dst i) = x.regs (src i)) ∧
      ∀ j, (∀ i, dst i ≠ j) → y.regs j = x.regs j := by
  induction k generalizing x with
  | zero =>
    have he : ExecWithin (B := B) w (.op (.copy idle idle)) x x 1 := by
      convert (ExecWithin.copy (B := B) (w := w) (d := idle) (s := idle) (x := x)) using 1
      apply Data.ext <;> simp [Data.set]
    exact ⟨x, he, rfl, fun i => Fin.elim0 i, fun _ _ => rfl⟩
  | succ n ih =>
    let a := x.set (dst 0) (x.regs (src 0))
    obtain ⟨y, hy, hm, hout, hframe⟩ := ih
      (fun i : Fin n => src i.succ) (fun i => dst i.succ)
      (fun i j h => Fin.succ_injective _ (hi h))
      (fun i j => hd i.succ j.succ) a
    have he : ExecWithin (B := B) w (.op (.copy (dst 0) (src 0))) x a 1 :=
      ExecWithin.copy
    refine ⟨y, ?_, hm, ?_, ?_⟩
    · simpa only [copyBank, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he.seq hy
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [hframe (dst 0) (fun j h => Fin.succ_ne_zero _ (hi h))]
        simp [a, Data.set]
      · rw [hout]
        exact Function.update_of_ne (hd j.succ 0) _ _
    · intro j hj
      rw [hframe j (fun i => hj i.succ)]
      exact Function.update_of_ne (hj 0).symm _ _

/-- The result of the memory interpreter is independent of the admissibility width. -/
theorem clientResult_width (w : ℕ) (p : Memory.Prog σ) (s : Memory.State) :
    (Memory.spec w).clientResult s p = (Memory.spec 0).clientResult s p :=
  congrArg Prod.fst (runClient_width w p s)

/-- The final memory/frontier state is independent of the admissibility width. -/
theorem clientState_width (w : ℕ) (p : Memory.Prog σ) (s : Memory.State) :
    (Memory.spec w).clientState s p = (Memory.spec 0).clientState s p :=
  congrArg (fun t => t.2.1) (runClient_width w p s)

/-- Admissible sequential histories split at the actual returned value and memory state. -/
theorem validHistory_bind (w : ℕ) {α β : Type} (p : Memory.Prog α)
    (q : α → Memory.Prog β) (s : Memory.State) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q)) ↔
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
      (Memory.spec w).ValidHistory ((Memory.spec w).clientState s p)
        ((Memory.spec w).clientHistory ((Memory.spec w).clientState s p)
          (q ((Memory.spec w).clientResult s p))) := by
  simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_bind]
  rw [StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient]

/-- Memory cost and certified local work decompose at each actual iteration. -/
theorem iteration_charge_succ (body : δ × σ → Memory.Prog σ)
    (work : (δ × σ) → Memory.State → ℕ) (d : δ) (n : ℕ) (a : σ) (s : Memory.State) :
    memoryCost (iterate body d (n + 1) a) s + iterationWork body work d (n + 1) a s =
      memoryCost (body (d, a)) s + work (d, a) s +
      (memoryCost (iterate body d n ((Memory.spec 0).clientResult s (body (d, a))))
        ((Memory.spec 0).clientState s (body (d, a))) +
      iterationWork body work d n ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a)))) + 1 := by
  rw [show iterate body d (n + 1) a =
    (body (d, a)).bind (iterate body d n) from rfl, memoryCost_bind]
  simp only [iterationWork]
  omega

/-- Sum a state-dependent charge along a fixed semantic transition. -/
def iterationSum (next : σ → σ) (charge : σ → ℕ) : ℕ → σ → ℕ
  | 0, _ => 0
  | n + 1, s => charge s + iterationSum next charge n (next s)

/-- A bounded native loop may charge variable body work and one unit per iteration without
issuing a memory query. Its body, register bank and exchange constants are fixed before fuel.
The remaining-fuel relation also carries arbitrary semantic proof state. -/
theorem loop_invariant_state_charged {cond : Cond r} {code : Code B r} {w C D : ℕ}
    (I : ℕ → σ → Data r → Prop) (next : σ → σ) (charge : σ → ℕ)
    (hexit : ∀ s x, I 0 s x → ¬cond.Holds x)
    (hbody : ∀ n s x, I (n + 1) s x →
      cond.Holds x ∧ ∃ y, ExecWithin w code x y (C * (charge s + 1) + D) ∧
        I n (next s) y)
    {n : ℕ} {s : σ} {x : Data r} (hx : I n s x) :
    ∃ y, ExecWithin w (.loop cond code) x y
        ((C + D + 2) * (iterationSum next charge n s + n + 1)) ∧
      I 0 ((next^[n]) s) y := by
  induction n generalizing s x with
  | zero =>
    refine ⟨x, (ExecWithin.loop_exit (hexit s x hx)).mono ?_, hx⟩
    simp only [iterationSum, Nat.zero_add, Nat.mul_one]
    omega
  | succ n ih =>
    obtain ⟨hc, a, ha, hI⟩ := hbody n s x hx
    obtain ⟨y, hy, hIy⟩ := ih hI
    refine ⟨y, (ExecWithin.loop_iter hc ha hy).mono ?_, ?_⟩
    · simp only [iterationSum]
      nlinarith
    · simpa only [Function.iterate_succ_apply] using hIy

/-- One semantic iteration updates both the mutable value and the complete memory state. -/
def iterationStep (body : δ × σ → Memory.Prog σ) (d : δ) (a : σ × Memory.State) :
    σ × Memory.State :=
  ((Memory.spec 0).clientResult a.2 (body (d, a.1)),
    (Memory.spec 0).clientState a.2 (body (d, a.1)))

/-- The interpreter follows precisely the bounded semantic transition, not an arbitrary state. -/
theorem iterate_result_state (body : δ × σ → Memory.Prog σ) (d : δ) (n : ℕ) (a : σ)
    (s : Memory.State) :
    ((Memory.spec 0).clientResult s (iterate body d n a),
      (Memory.spec 0).clientState s (iterate body d n a)) =
      (iterationStep body d)^[n] (a, s) := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
    rw [show iterate body d (n + 1) a =
      (body (d, a)).bind (iterate body d n) from rfl]
    simpa only [StateTransitionSpec.clientResult, StateTransitionSpec.clientState,
      StateTransitionSpec.runClient_bind, Function.iterate_succ_apply, iterationStep] using
      ih ((Memory.spec 0).clientResult s (body (d, a)))
        ((Memory.spec 0).clientState s (body (d, a)))

/-- The native grading rule's semantic sum is exactly memory charge plus local iteration work. -/
theorem iterationSum_eq (body : δ × σ → Memory.Prog σ)
    (work : (δ × σ) → Memory.State → ℕ) (d : δ) (n : ℕ) (a : σ) (s : Memory.State) :
    iterationSum (iterationStep body d)
        (fun q => memoryCost (body (d, q.1)) q.2 + work (d, q.1) q.2) n (a, s) + n =
      memoryCost (iterate body d n a) s + iterationWork body work d n a s := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
    rw [iterationSum, iteration_charge_succ]
    have h := ih ((Memory.spec 0).clientResult s (body (d, a)))
      ((Memory.spec 0).clientState s (body (d, a)))
    dsimp only [iterationStep] at *
    omega

private def stateSlot {l n : ℕ} (i : Fin l) : Fin (l + (l + n + 3) + 1) :=
  ⟨i.val, by omega⟩

private def counterSlot (l n : ℕ) : Fin (l + (l + n + 3) + 1) := ⟨l, by omega⟩
private def zeroSlot (l n : ℕ) : Fin (l + (l + n + 3) + 1) := ⟨l + 1, by omega⟩
private def oneSlot (l n : ℕ) : Fin (l + (l + n + 3) + 1) := ⟨l + 2, by omega⟩

private def bodySlot {l n : ℕ} (i : Fin (l + n + 1)) : Fin (l + (l + n + 3) + 1) :=
  ⟨l + 3 + i.val, by omega⟩

private def loopBody {n : ℕ} (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
    (Fin (l + n + 1) → Fin r) → Code .exact r)
    (frontier : Fin r) (src : Fin (k + l + 1) → Fin r)
    (tmp : Fin (l + (l + n + 3) + 1) → Fin r) : Code .exact r :=
  .seq (emit frontier (Fin.append (fun i : Fin k => src ⟨i.val, by omega⟩)
    (fun i => tmp (stateSlot i))) (fun i => tmp (bodySlot i))) <|
    .seq (copyBank (fun i : Fin l => tmp (bodySlot (Fin.castAdd (n + 1) i)))
      (fun i => tmp (stateSlot i)) (tmp (zeroSlot l n))) <|
      .seq (.op (.const (tmp (oneSlot l n)) 1))
        (.op (.exactBin .sub (tmp (counterSlot l n))
          (tmp (counterSlot l n)) (tmp (oneSlot l n))))

private def loopEmit {n : ℕ} (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
    (Fin (l + n + 1) → Fin r) → Code .exact r)
    (frontier : Fin r) (src : Fin (k + l + 1) → Fin r)
    (tmp : Fin (l + (l + n + 3) + 1) → Fin r) : Code .exact r :=
  .seq (copyBank (fun i : Fin l => src ⟨k + i.val, by omega⟩)
    (fun i => tmp (stateSlot i)) (tmp (zeroSlot l n))) <|
    .seq (.op (.copy (tmp (counterSlot l n)) (src ⟨k + l, by omega⟩))) <|
      .seq (.op (.const (tmp (zeroSlot l n)) 0))
        (.loop (.lt (tmp (zeroSlot l n)) (tmp (counterSlot l n)))
          (loopBody emit frontier src tmp))

namespace Realizes

/-- A runtime-bounded loop reuses one fixed body emitter, including iterations without queries.
The visible domain is precisely the body domains along the actual semantic states. -/
theorem iterateRuntime (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : Realizes .exact body
      ((input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding) output safe work) :
    Realizes .exact (fun d : (δ × σ) × ℕ => iterate body d.1.1 d.2 d.1.2)
      ((((input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w d s => iterationSafe body safe w d.1.1 d.2 d.1.2 s)
      (fun d s => iterationWork body work d.1.1 d.2 d.1.2 s) := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨l + n + 3, C + 2 * l + 8, loopEmit emit, ?_⟩
  intro r frontier src tmp hi hd hf hs
  let st : Fin l → Fin r := fun i => tmp (stateSlot i)
  let ctr := tmp (counterSlot l n)
  let zero := tmp (zeroSlot l n)
  let one := tmp (oneSlot l n)
  let bt : Fin (l + n + 1) → Fin r := fun i => tmp (bodySlot i)
  let env : Fin k → Fin r := fun i => src ⟨i.val, by omega⟩
  let bs := Fin.append env st
  have hst : Function.Injective st := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun j : Fin (l + (l + n + 3) + 1) => j.val) (hi hij)
  have hbt : Function.Injective bt := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val (hi hij)
    dsimp only [bodySlot] at hh
    omega
  have hbdis : ∀ i j, bs i ≠ bt j := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [bs, Fin.append_left] using hd (⟨i.val, by omega⟩ : Fin (k + l + 1)) (bodySlot j)
    · simp only [bs, Fin.append_right]
      intro hij
      have hh := congrArg Fin.val (hi hij)
      dsimp only [stateSlot, bodySlot] at hh
      omega
  have hbf : ∀ j, bt j ≠ frontier := fun j => hf _
  have hbs : ∀ i, bs i ≠ frontier := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [bs, Fin.append_left] using hs (⟨i.val, by omega⟩ : Fin (k + l + 1))
    · simpa only [bs, Fin.append_right] using hf (stateSlot i)
  obtain ⟨hnw, hrun⟩ := he frontier bs bt hbt hbdis hbf hbs
  have houtdis : ∀ i j : Fin l, bt (Fin.castAdd (n + 1) i) ≠ st j := by
    intro i j hij
    have hh := congrArg Fin.val (hi hij)
    dsimp only [bodySlot, stateSlot] at hh
    omega
  have hct : ctr ≠ zero := by
    intro hij
    have := congrArg Fin.val (hi hij)
    simp [counterSlot, zeroSlot] at this
  have hco : ctr ≠ one := by
    intro hij
    have := congrArg Fin.val (hi hij)
    simp [counterSlot, oneSlot] at this
  have hzo : zero ≠ one := by
    intro hij
    have := congrArg Fin.val (hi hij)
    simp [zeroSlot, oneSlot] at this
  have hregbt (a : Fin (l + (l + n + 3) + 1)) (ha : a.val < l + 3) :
      ∀ j, bt j ≠ tmp a := by
    intro j hij
    have hh := congrArg Fin.val (hi hij)
    dsimp only [bodySlot] at hh
    omega
  have hregst (a : Fin (l + (l + n + 3) + 1)) (ha : l ≤ a.val) :
      ∀ i, st i ≠ tmp a := by
    intro i hij
    have hh := congrArg Fin.val (hi hij)
    dsimp only [stateSlot] at hh
    omega
  refine ⟨?_, ?_⟩
  · change ¬(loopEmit emit frontier src tmp).ReadsWidth
    simpa [loopEmit, loopBody, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin,
      copyBank_not_readsWidth] using hnw
  · intro w d x hx hin hsafe hv
    let a₀ := d.1.2
    let d₀ := d.1.1
    let fuel := d.2
    let s₀ := memoryState frontier x
    have henv (i : Fin k) : x.regs (env i) = input d₀ i := by
      have hh : x.regs (src (Fin.castAdd 1 (Fin.castAdd l i))) = input d₀ i := by
        simpa [d₀, Fin.appendEquiv] using congrFun hin (Fin.castAdd 1 (Fin.castAdd l i))
      have hidx : Fin.castAdd 1 (Fin.castAdd l i) = (⟨i.val, by omega⟩ : Fin (k + l + 1)) := by
        apply Fin.ext
        rfl
      rw [hidx] at hh
      exact hh
    have hstate (i : Fin l) : x.regs (src ⟨k + i.val, by omega⟩) = output a₀ i := by
      have hh : x.regs (src (Fin.castAdd 1 (Fin.natAdd k i))) = output a₀ i := by
        simpa [a₀, Fin.appendEquiv] using congrFun hin (Fin.castAdd 1 (Fin.natAdd k i))
      have hidx : Fin.castAdd 1 (Fin.natAdd k i) =
          (⟨k + i.val, by omega⟩ : Fin (k + l + 1)) := by
        apply Fin.ext
        rfl
      rw [hidx] at hh
      exact hh
    have hfuel : x.regs (src ⟨k + l, by omega⟩) = fuel := by
      have hh : x.regs (src (Fin.natAdd (k + l) 0)) = fuel := by
        simpa [fuel, Fin.appendEquiv] using congrFun hin (Fin.natAdd (k + l) 0)
      have hidx : Fin.natAdd (k + l) 0 = (⟨k + l, by omega⟩ : Fin (k + l + 1)) := by
        apply Fin.ext
        simp
      rw [hidx] at hh
      exact hh
    obtain ⟨a, ha, ham, has, haf⟩ := copyBank_exec
      (fun i : Fin l => src ⟨k + i.val, by omega⟩) st zero hst
      (fun _ _ => hd _ _) w x
    let b := a.set ctr fuel
    let z := b.set zero 0
    have hafuel : a.regs (src ⟨k + l, by omega⟩) = fuel := by
      rw [haf _ (fun _ => (hd _ _).symm)]
      exact hfuel
    have hc : ExecWithin (B := .exact) w (.op (.copy ctr (src ⟨k + l, by omega⟩))) a b 1 := by
      simpa only [hafuel] using
        (ExecWithin.copy (B := .exact) (w := w) (d := ctr)
          (s := src ⟨k + l, by omega⟩) (x := a))
    have hz : ExecWithin (B := .exact) w (.op (.const zero 0)) b z 1 :=
      ExecWithin.const (fits_zero w)
    let I : ℕ → (σ × Memory.State) → Data r → Prop := fun j q y =>
      y.Bounded w ∧ memoryState frontier y = q.2 ∧
      (∀ i, y.regs (env i) = input d₀ i) ∧ (∀ i, y.regs (st i) = output q.1 i) ∧
      y.regs ctr = j ∧ y.regs zero = 0 ∧ iterationSafe body safe w d₀ j q.1 q.2 ∧
      (Memory.spec w).ValidHistory q.2
        ((Memory.spec w).clientHistory q.2 (iterate body d₀ j q.1)) ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i
    have hIz : I fuel (a₀, s₀) z := by
      refine ⟨(ha.seq (hc.seq hz)).bounded hx, ?_, ?_, ?_, ?_, ?_, hsafe, hv, ?_⟩
      · apply Memory.State.ext
        · exact ham
        · change (b.set zero 0).regs frontier = x.regs frontier
          rw [show (b.set zero 0).regs frontier = b.regs frontier from
            Function.update_of_ne (hf (zeroSlot l n)).symm _ _,
            show b.regs frontier = a.regs frontier from
              Function.update_of_ne (hf (counterSlot l n)).symm _ _,
            haf frontier (fun i => hf _)]
      · intro i
        simp only [z, b, Data.set]
        rw [Function.update_of_ne (hd _ _), Function.update_of_ne (hd _ _),
          haf _ (fun _ => (hd _ _).symm)]
        exact henv i
      · intro i
        simp only [z, b, Data.set]
        rw [Function.update_of_ne (hregst _ (by simp [zeroSlot]) i),
          Function.update_of_ne (hregst _ (by simp [counterSlot]) i), has]
        exact hstate i
      · simp [z, b, Data.set, hct]
      · simp [z, Data.set]
      · intro i hif htmp
        simp only [z, b, Data.set]
        rw [Function.update_of_ne (htmp _).symm,
          Function.update_of_ne (htmp _).symm, haf _ (fun _ => htmp _)]
    have hbody : ∀ j q y, I (j + 1) q y →
        (Cond.lt zero ctr).Holds y ∧ ∃ y',
          ExecWithin w (loopBody emit frontier src tmp) y y'
            (C * (memoryCost (body (d₀, q.1)) q.2 + work (d₀, q.1) q.2 + 1) + (l + 3)) ∧
          I j (iterationStep body d₀ q) y' := by
      intro j q y hIy
      obtain ⟨hyb, hym, hye, hys, hyc, hyz, hysafe, hyv, hyframe⟩ := hIy
      refine ⟨by simp [Cond.Holds, hyz, hyc], ?_⟩
      have hvparts := (validHistory_bind w (body (d₀, q.1))
        (iterate body d₀ j) q.2).mp hyv
      have hinbody : y.regs ∘ bs =
          ((input.prodMap output).trans (Fin.appendEquiv k l).toEmbedding) (d₀, q.1) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa [bs, Fin.appendEquiv] using hye i
        · simpa [bs, Fin.appendEquiv] using hys i
      obtain ⟨u, hu, hum, huo, huf⟩ := hrun w (d₀, q.1) y hyb hinbody
        (hym ▸ hysafe.1) (hym ▸ hvparts.1)
      rw [hym] at hu hum huo
      rw [clientState_width] at hum
      simp only [clientResult_width] at huo
      obtain ⟨v, hv', hvm, hvs, hvf⟩ := copyBank_exec
        (fun i : Fin l => bt (Fin.castAdd (n + 1) i)) st zero hst houtdis w u
      have hvctr : v.regs ctr = j + 1 := by
        rw [hvf _ (hregst _ (by simp [counterSlot])),
          huf _ (hf _) (hregbt _ (by simp [counterSlot]))]
        exact hyc
      have hvzero : v.regs zero = 0 := by
        rw [hvf _ (hregst _ (by simp [zeroSlot])),
          huf _ (hf _) (hregbt _ (by simp [zeroSlot]))]
        exact hyz
      have h1 : Fits w 1 := (hyb.1 ctr).of_le (by omega)
      let t := v.set one 1
      let y' := t.set ctr j
      have ht : ExecWithin (B := .exact) w (.op (.const one 1)) v t 1 :=
        ExecWithin.const h1
      have htc : t.regs ctr = j + 1 := by
        rw [show t.regs ctr = v.regs ctr from Function.update_of_ne hco _ _]
        exact hvctr
      have htone : t.regs one = 1 := by simp [t, Data.set]
      have hjfit : Fits w j := (hyb.1 ctr).of_le (by omega)
      have hdec : ExecWithin w (.op (.exactBin .sub ctr ctr one)) t y' 1 := by
        apply ExecWithin.op
        rw [Op.eval_exactBin, htc, htone]
        simp only [BinOp.evalExact, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel,
          Option.bind_some]
        exact Data.put_of_fits hjfit
      refine ⟨y', ?_, ?_⟩
      · exact (hu.seq (hv'.seq (ht.seq hdec))).mono (by omega)
      · refine ⟨(hu.seq (hv'.seq (ht.seq hdec))).bounded hyb, ?_, ?_, ?_, ?_, ?_,
          hysafe.2, ?_, ?_⟩
        · apply Memory.State.ext
          · exact hvm.trans (congrArg Memory.State.mem hum)
          · change (t.set ctr j).regs frontier = _
            rw [show (t.set ctr j).regs frontier = t.regs frontier from
              Function.update_of_ne (hf (counterSlot l n)).symm _ _,
              show t.regs frontier = v.regs frontier from
                Function.update_of_ne (hf (oneSlot l n)).symm _ _,
              hvf frontier (fun i => hf _)]
            exact congrArg Memory.State.frontier hum
        · intro i
          simp only [y', t, Data.set]
          rw [Function.update_of_ne (hd _ _), Function.update_of_ne (hd _ _),
            hvf _ (fun _ => (hd _ _).symm), huf _ (hs _) (fun _ => (hd _ _).symm)]
          exact hye i
        · intro i
          simp only [y', t, Data.set]
          rw [Function.update_of_ne (hregst _ (by simp [counterSlot]) i),
            Function.update_of_ne (hregst _ (by simp [oneSlot]) i), hvs, huo]
          rfl
        · simp [y', Data.set]
        · simp [y', t, Data.set, hct.symm, hzo, hvzero]
        · have hrest := hvparts.2
          rw [clientState_width w, clientResult_width w] at hrest
          exact hrest
        · intro i hif htmp
          simp only [y', t, Data.set]
          rw [Function.update_of_ne (htmp _).symm, Function.update_of_ne (htmp _).symm,
            hvf _ (fun _ => htmp _), huf _ hif (fun _ => htmp _)]
          exact hyframe i hif htmp
    obtain ⟨y, hy, hIy⟩ := loop_invariant_state_charged I (iterationStep body d₀)
      (fun q => memoryCost (body (d₀, q.1)) q.2 + work (d₀, q.1) q.2)
      (fun q y hI => by simp [Cond.Holds, hI.2.2.2.2.1, hI.2.2.2.2.2.1]) hbody hIz
    rw [iterationSum_eq] at hy
    have hfinal := iterate_result_state body d₀ fuel a₀ s₀
    rw [← hfinal] at hIy
    obtain ⟨_, hym, _, hys, _, _, _, _, hyf⟩ := hIy
    refine ⟨y, (ha.seq (hc.seq (hz.seq hy))).mono ?_, ?_, ?_, hyf⟩
    · nlinarith
    · change memoryState frontier y = (Memory.spec w).clientState s₀ (iterate body d₀ fuel a₀)
      rw [clientState_width w]
      exact hym
    · intro i
      change y.regs (st i) = output ((Memory.spec w).clientResult s₀ (iterate body d₀ fuel a₀)) i
      rw [clientResult_width w]
      exact hys i

end Realizes
end Cslib.WordRAM.Realization
