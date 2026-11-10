/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.GhostLoop
public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import CslibFrontier.Computability.WordRAM.RegisterCopy
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.DataStructure.Memory.Frame

/-!
# Bounded memory-client loops

Bounded iteration remains an ordinary `Memory.Prog` term. The local-work currency counts body
work and every iteration, including iterations issuing no memory query. The native realization
uses one fixed body emitter and static registers for the mutable state and countdown counter.

## Main definitions

* `iterate`: bounded iteration in the existing memory-client monad.
* `iterationWork`, `iterationSafe`: local work and domains along the actual semantic states.
* `loopEmit`, `loopBody`: the native loop with a fixed body emitter, and one native iteration,
  over the register bank `stateSlot`, `counterSlot`, `zeroSlot`, `oneSlot`, `bodySlot`.

## Main results

* `iterationSum_eq`: the native grading rule's semantic sum is memory charge plus local work.
* `Realizes.Witness.loopEmit_spec`: the loop emitter with additive per-iteration overhead.
* `Realizes.Witness.iterateRuntime`, `Realizes.iterateRuntime`: one uniform body witness or
  certificate realizes a runtime-bounded loop.

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

/-- The loop's state words, which are also its result slots. -/
def stateSlot {l n : ℕ} (i : Fin l) : Fin (l + (l + n + 3) + 1) :=
  ⟨i.val, by omega⟩

/-- The loop's countdown register. -/
def counterSlot (l n : ℕ) : Fin (l + (l + n + 3) + 1) := ⟨l, by omega⟩
/-- A register holding zero, for the loop test. -/
def zeroSlot (l n : ℕ) : Fin (l + (l + n + 3) + 1) := ⟨l + 1, by omega⟩
/-- A register holding one, for the countdown. -/
def oneSlot (l n : ℕ) : Fin (l + (l + n + 3) + 1) := ⟨l + 2, by omega⟩

/-- The body's scratch bank inside the loop's bank. -/
def bodySlot {l n : ℕ} (i : Fin (l + n + 1)) : Fin (l + (l + n + 3) + 1) :=
  ⟨l + 3 + i.val, by omega⟩

/-- One native iteration: run the body on the environment and state words, copy its result into
the state words and count down. -/
def loopBody {n : ℕ} (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
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

/-- The native loop: install the state words and the counter, then iterate `loopBody` while the
counter is positive. -/
def loopEmit {n : ℕ} (emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
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

/-- The existing loop emitter retains the complete realization postcondition while paying
body charges and state/control overhead separately. This bounds that supplied emitter, not a
classically reselected implementation. -/
theorem Witness.loopEmit_spec (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : Witness .exact body (appendWords input output) output safe work) :
    ∀ {r : ℕ} (frontier : Fin r) (src : Fin (k + l + 1) → Fin r)
      (tmp : Fin (l + (l + h.scratchSize + 3) + 1) → Fin r),
      Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
      (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
      ¬(loopEmit h.code frontier src tmp).ReadsWidth ∧
      ∀ (w : ℕ) (d : (δ × σ) × ℕ) (x : Data r), x.Bounded w →
        x.regs ∘ src = (((appendWords input output).prodMap
            (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) d →
        iterationSafe body safe w d.1.1 d.2 d.1.2 (memoryState frontier x) →
        (Memory.spec w).ValidHistory (memoryState frontier x)
          ((Memory.spec w).clientHistory (memoryState frontier x)
            (iterate body d.1.1 d.2 d.1.2)) →
        ∃ y, ExecWithin w (loopEmit h.code frontier src tmp) x y
            (h.factor * (memoryCost (iterate body d.1.1 d.2 d.1.2) (memoryState frontier x) +
              iterationWork body work d.1.1 d.2 d.1.2 (memoryState frontier x)) +
                (l + 5) * (d.2 + 1)) ∧
          memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x)
            (iterate body d.1.1 d.2 d.1.2) ∧
          (∀ i : Fin l, y.regs (tmp (Fin.castAdd ((l + h.scratchSize + 3) + 1) i)) =
            output ((Memory.spec w).clientResult (memoryState frontier x)
              (iterate body d.1.1 d.2 d.1.2)) i) ∧
          ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  let n := h.scratchSize
  let C := h.factor
  let emit : ∀ {r : ℕ}, Fin r → (Fin (k + l) → Fin r) →
      (Fin (l + n + 1) → Fin r) → Code .exact r := h.code
  have he : Realizes.Spec .exact body (appendWords input output) output safe work n C emit :=
    h.code_spec
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
        simpa [d₀, appendWords, Fin.appendEquiv] using
          congrFun hin (Fin.castAdd 1 (Fin.castAdd l i))
      have hidx : Fin.castAdd 1 (Fin.castAdd l i) = (⟨i.val, by omega⟩ : Fin (k + l + 1)) := by
        apply Fin.ext
        rfl
      rw [hidx] at hh
      exact hh
    have hstate (i : Fin l) : x.regs (src ⟨k + i.val, by omega⟩) = output a₀ i := by
      have hh : x.regs (src (Fin.castAdd 1 (Fin.natAdd k i))) = output a₀ i := by
        simpa [a₀, appendWords, Fin.appendEquiv] using
          congrFun hin (Fin.castAdd 1 (Fin.natAdd k i))
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
      wram_exec [hafuel]
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
          wram_simp [b]
          exact haf frontier fun i => hf _
      · intro i
        wram_simp [z, b]
        rw [haf _ fun _ => (hd _ _).symm]
        exact henv i
      · intro i
        wram_simp [z, b, st, zero, ctr]
        exact (has i).trans (hstate i)
      · wram_simp [z, b]
      · wram_simp [z]
      · intro i hif htmp
        wram_simp [z, b]
        exact haf _ fun _ => htmp _
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
          (appendWords input output) (d₀, q.1) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa [bs, appendWords, Fin.appendEquiv] using hye i
        · simpa [bs, appendWords, Fin.appendEquiv] using hys i
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
      have htc : t.regs ctr = j + 1 := by wram_simp [t, hvctr]
      have htone : t.regs one = 1 := by simp [t, Data.set]
      have hjfit : Fits w j := (hyb.1 ctr).of_le (by omega)
      have hdec : ExecWithin w (.op (.exactBin .sub ctr ctr one)) t y' 1 := by
        wram_exec [htc, htone]
      refine ⟨y', ?_, ?_⟩
      · exact (hu.seq (hv'.seq (ht.seq hdec))).mono (by omega)
      · refine ⟨(hu.seq (hv'.seq (ht.seq hdec))).bounded hyb, ?_, ?_, ?_, ?_, ?_,
          hysafe.2, ?_, ?_⟩
        · apply Memory.State.ext
          · exact hvm.trans (congrArg Memory.State.mem hum)
          · change (t.set ctr j).regs frontier = _
            wram_simp [t]
            rw [hvf frontier fun i => hf _]
            exact congrArg Memory.State.frontier hum
        · intro i
          wram_simp [y', t]
          rw [hvf _ fun _ => (hd _ _).symm, huf _ (hs _) fun _ => (hd _ _).symm]
          exact hye i
        · intro i
          wram_simp [y', t, st, one, ctr]
          exact (hvs i).trans (huo _)
        · wram_simp [y']
        · wram_simp [y', t, hvzero]
        · have hrest := hvparts.2
          rw [clientState_width w, clientResult_width w] at hrest
          exact hrest
        · intro i hif htmp
          wram_simp [y', t]
          rw [hvf _ fun _ => htmp _, huf _ hif fun _ => htmp _]
          exact hyframe i hif htmp
    obtain ⟨y, hy, hIy⟩ := ExecWithin.loop_invariant_state_additive I (iterationStep body d₀)
      (fun q => memoryCost (body (d₀, q.1)) q.2 + work (d₀, q.1) q.2)
      (fun q y hI => by simp [Cond.Holds, hI.2.2.2.2.1, hI.2.2.2.2.2.1]) hbody hIz
    have hsum := iterationSum_eq body work d₀ fuel a₀ s₀
    have hsumC := congrArg (C * ·) hsum
    have hfinal := iterate_result_state body d₀ fuel a₀ s₀
    rw [← hfinal] at hIy
    obtain ⟨_, hym, _, hys, _, _, _, _, hyf⟩ := hIy
    refine ⟨y, (ha.seq (hc.seq (hz.seq hy))).mono ?_, ?_, ?_, hyf⟩
    · nlinarith [hsumC]
    · change memoryState frontier y = (Memory.spec w).clientState s₀ (iterate body d₀ fuel a₀)
      rw [clientState_width w]
      exact hym
    · intro i
      change y.regs (st i) = output ((Memory.spec w).clientResult s₀ (iterate body d₀ fuel a₀)) i
      rw [clientResult_width w]
      exact hys i

/-- Retain the supplied body and the existing loop emitter as data. Its original coarse
realization contract follows from the sharper same-emitter `loopEmit_spec`. -/
def Witness.iterateRuntime (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : Witness .exact body
      (appendWords input output) output safe work) :
    Witness .exact (fun ((d, a), fuel) => iterate body d fuel a)
      (((appendWords input output).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w ((d, a), fuel) s => iterationSafe body safe w d fuel a s)
      (fun ((d, a), fuel) s => iterationWork body work d fuel a s) where
  scratchSize := l + h.scratchSize + 3
  factor := h.factor + 2 * l + 8
  code := loopEmit h.code
  code_spec := by
    intro r frontier src tmp hi hd hf hs
    obtain ⟨hnw, hrun⟩ := h.loopEmit_spec input output frontier src tmp hi hd hf hs
    refine ⟨hnw, ?_⟩
    intro w d x hx hin hsafe hv
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x hx hin hsafe hv
    refine ⟨y, hy.mono ?_, hm, hout, hframe⟩
    have hsum := iterationSum_eq body work d.1.1 d.2 d.1.2 (memoryState frontier x)
    have hcount : d.2 ≤ memoryCost (iterate body d.1.1 d.2 d.1.2) (memoryState frontier x) +
        iterationWork body work d.1.1 d.2 d.1.2 (memoryState frontier x) := by omega
    have hscaled := Nat.mul_le_mul_left (l + 5) (Nat.add_le_add_right hcount 1)
    nlinarith [hscaled]

/-- The existential runtime-loop realization erases the retained supplied emitter. -/
theorem iterateRuntime (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : Realizes .exact body
      (appendWords input output) output safe work) :
    Realizes .exact (fun ((d, a), fuel) => iterate body d fuel a)
      (((appendWords input output).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w ((d, a), fuel) s => iterationSafe body safe w d fuel a s)
      (fun ((d, a), fuel) s => iterationWork body work d fuel a s) :=
  (Witness.iterateRuntime input output (Witness.ofRealizes h)).toRealizes

end Realizes

namespace RealizesBounded

/-- Frontier-bounded realization of runtime-bounded `iterate`. -/
theorem iterateRuntime (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → Memory.Prog σ}
    {safe : ℕ → (δ × σ) → Memory.State → Prop}
    {work : (δ × σ) → Memory.State → ℕ}
    (h : RealizesBounded .exact body (appendWords input output) output safe work) :
    RealizesBounded .exact (fun ((d, a), fuel) => iterate body d fuel a)
      (((appendWords input output).prodMap
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
          (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w ((d, a), fuel) s => iterationSafe body safe w d fuel a s)
      (fun ((d, a), fuel) s => iterationWork body work d fuel a s) := by
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
  have hst : Function.Injective st := fun i j hij =>
    Fin.ext (congrArg (fun j : Fin (l + (l + n + 3) + 1) => j.val) (hi hij))
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
  have hct : ctr ≠ zero := fun hij => by
    have := congrArg Fin.val (hi hij); simp [counterSlot, zeroSlot] at this
  have hco : ctr ≠ one := fun hij => by
    have := congrArg Fin.val (hi hij); simp [counterSlot, oneSlot] at this
  have hzo : zero ≠ one := fun hij => by
    have := congrArg Fin.val (hi hij); simp [zeroSlot, oneSlot] at this
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
  refine ⟨by simpa [loopEmit, loopBody, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin,
    copyBank_not_readsWidth] using hnw, ?_⟩
  rintro w ⟨⟨d₀, a₀⟩, fuel⟩ x hx hin hsafe hv
  let s₀ := memoryState frontier x
  let L_end := ((Memory.spec 0).clientState s₀ (iterate body d₀ fuel a₀)).frontier
  have henv (i : Fin k) : x.regs (env i) = input d₀ i := by
    have hh : x.regs (src (Fin.castAdd 1 (Fin.castAdd l i))) = input d₀ i := by
      simpa [appendWords, Fin.appendEquiv] using
        congrFun hin (Fin.castAdd 1 (Fin.castAdd l i))
    have hidx : Fin.castAdd 1 (Fin.castAdd l i) = (⟨i.val, by omega⟩ : Fin (k + l + 1)) :=
      Fin.ext rfl
    rw [hidx] at hh
    exact hh
  have hstate (i : Fin l) : x.regs (src ⟨k + i.val, by omega⟩) = output a₀ i := by
    have hh : x.regs (src (Fin.castAdd 1 (Fin.natAdd k i))) = output a₀ i := by
      simpa [appendWords, Fin.appendEquiv] using
        congrFun hin (Fin.castAdd 1 (Fin.natAdd k i))
    have hidx : Fin.castAdd 1 (Fin.natAdd k i) = (⟨k + i.val, by omega⟩ : Fin (k + l + 1)) :=
      Fin.ext rfl
    rw [hidx] at hh
    exact hh
  have hfuel : x.regs (src ⟨k + l, by omega⟩) = fuel := by
    have hh : x.regs (src (Fin.natAdd (k + l) 0)) = fuel := by
      simpa [Fin.appendEquiv] using congrFun hin (Fin.natAdd (k + l) 0)
    have hidx : Fin.natAdd (k + l) 0 = (⟨k + l, by omega⟩ : Fin (k + l + 1)) := by
      apply Fin.ext; simp
    rw [hidx] at hh
    exact hh
  obtain ⟨a, ha, ham, has, haf⟩ := copyBank_execBounded
    (fun i : Fin l => src ⟨k + i.val, by omega⟩) st zero hst
    (fun _ _ => hd _ _) w L_end x
  let b := a.set ctr fuel
  let z := b.set zero 0
  have hafuel : a.regs (src ⟨k + l, by omega⟩) = fuel := by
    rw [haf _ (fun _ => (hd _ _).symm)]
    exact hfuel
  have hc : ExecBounded (B := .exact) w L_end (.op (.copy ctr (src ⟨k + l, by omega⟩))) a b 1 := by
    simpa only [hafuel] using
      (ExecBounded.copy (B := .exact) (w := w) (L := L_end) (d := ctr)
        (s := src ⟨k + l, by omega⟩) (x := a))
  have hz : ExecBounded (B := .exact) w L_end (.op (.const zero 0)) b z 1 :=
    ExecBounded.const (fits_zero w)
  let I : ℕ → (σ × Memory.State) → Data r → Prop := fun j q y =>
    y.Bounded w ∧ memoryState frontier y = q.2 ∧
    ((Memory.spec 0).clientState q.2 (iterate body d₀ j q.1)).frontier ≤ L_end ∧
    (∀ i, y.regs (env i) = input d₀ i) ∧ (∀ i, y.regs (st i) = output q.1 i) ∧
    y.regs ctr = j ∧ y.regs zero = 0 ∧ iterationSafe body safe w d₀ j q.1 q.2 ∧
    (Memory.spec w).ValidHistory q.2
      ((Memory.spec w).clientHistory q.2 (iterate body d₀ j q.1)) ∧
    ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i
  have hIz : I fuel (a₀, s₀) z := by
    refine ⟨(ha.seq (hc.seq hz)).bounded hx, ?_, le_rfl, ?_, ?_, ?_, ?_, hsafe, hv, ?_⟩
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
        ExecBounded w L_end (loopBody emit frontier src tmp) y y'
          (C * (memoryCost (body (d₀, q.1)) q.2 + work (d₀, q.1) q.2 + 1) + (l + 3)) ∧
        I j (iterationStep body d₀ q) y' := by
    intro j q y hIy
    obtain ⟨hyb, hym, hL, hye, hys, hyc, hyz, hysafe, hyv, hyframe⟩ := hIy
    refine ⟨by simp [Cond.Holds, hyz, hyc], ?_⟩
    have hvparts := (validHistory_bind w (body (d₀, q.1)) (iterate body d₀ j) q.2).mp hyv
    have hinbody : y.regs ∘ bs = (appendWords input output) (d₀, q.1) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa [bs, appendWords, Fin.appendEquiv] using hye i
      · simpa [bs, appendWords, Fin.appendEquiv] using hys i
    obtain ⟨u, hu, hum, huo, huf⟩ := hrun w (d₀, q.1) y hyb hinbody
      (hym ▸ hysafe.1) (hym ▸ hvparts.1)
    rw [hym] at hu hum huo
    rw [clientState_width] at hum
    simp only [clientResult_width] at huo
    have hstep_eq :
        ((Memory.spec 0).clientState q.2 (iterate body d₀ (j + 1) q.1)) =
        ((Memory.spec 0).clientState ((Memory.spec 0).clientState q.2 (body (d₀, q.1)))
          (iterate body d₀ j ((Memory.spec 0).clientResult q.2 (body (d₀, q.1))))) := by
      simp only [iterate, StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
        ← PFunctor.FreeM.bind_eq_bind, StateTransitionSpec.runClient_bind]
    have hL' : ((Memory.spec 0).clientState (iterationStep body d₀ q).2
        (iterate body d₀ j (iterationStep body d₀ q).1)).frontier ≤ L_end := by
      dsimp only [iterationStep]
      rw [← hstep_eq]
      exact hL
    have hu_le : u.regs frontier ≤ L_end := by
      have hum_fr := congrArg Memory.State.frontier hum
      change u.regs frontier = ((Memory.spec 0).clientState q.2 (body (d₀, q.1))).frontier at hum_fr
      rw [hum_fr]
      exact (Memory.frontier_le_clientState (w := 0)
        ((Memory.spec 0).clientState q.2 (body (d₀, q.1)))
        (iterate body d₀ j ((Memory.spec 0).clientResult q.2 (body (d₀, q.1))))).trans hL'
    obtain ⟨v, hv', hvm, hvs, hvf⟩ := copyBank_execBounded
      (fun i : Fin l => bt (Fin.castAdd (n + 1) i)) st zero hst houtdis w L_end u
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
    have ht : ExecBounded (B := .exact) w L_end (.op (.const one 1)) v t 1 :=
      ExecBounded.const h1
    have htc : t.regs ctr = j + 1 := by
      rw [show t.regs ctr = v.regs ctr from Function.update_of_ne hco _ _]
      exact hvctr
    have htone : t.regs one = 1 := by simp [t, Data.set]
    have hjfit : Fits w j := (hyb.1 ctr).of_le (by omega)
    have hdec : ExecBounded w L_end (.op (.exactBin .sub ctr ctr one)) t y' 1 := by
      refine ExecBounded.op trivial ?_
      rw [Op.eval_exactBin, htc, htone]
      simp only [BinOp.evalExact, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel,
        Option.bind_some]
      exact Data.put_of_fits hjfit
    refine ⟨y', ((hu.mono_bound hu_le).seq (hv'.seq (ht.seq hdec))).mono (by omega), ?_⟩
    refine ⟨((hu.mono_bound hu_le).seq (hv'.seq (ht.seq hdec))).bounded hyb, ?_, hL',
      ?_, ?_, ?_, ?_, hysafe.2, ?_, ?_⟩
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
  obtain ⟨y, hy, hIy⟩ := ExecBounded.loop_invariant_state_additive I (iterationStep body d₀)
    (fun q => memoryCost (body (d₀, q.1)) q.2 + work (d₀, q.1) q.2)
    (fun q y hI => by simp [Cond.Holds, hI.2.2.2.2.2.1, hI.2.2.2.2.2.2.1]) hbody hIz
  have hsum := iterationSum_eq body work d₀ fuel a₀ s₀
  have hsumC := congrArg (C * ·) hsum
  have hfinal := iterate_result_state body d₀ fuel a₀ s₀
  rw [← hfinal] at hIy
  obtain ⟨_, hym, _, _, hys, _, _, _, _, hyf⟩ := hIy
  have hy_fr : y.regs frontier = L_end := congrArg Memory.State.frontier hym
  have hwhole := ha.seq (hc.seq (hz.seq hy))
  rw [← hy_fr] at hwhole
  have hcount : fuel ≤ memoryCost (iterate body d₀ fuel a₀) s₀ +
      iterationWork body work d₀ fuel a₀ s₀ := by omega
  have hscaled := Nat.mul_le_mul_left (l + 5) (Nat.add_le_add_right hcount 1)
  refine ⟨y, hwhole.mono ?_, ?_, ?_, hyf⟩
  · change _ ≤ (C + 2 * l + 8) *
      (memoryCost (iterate body d₀ fuel a₀) s₀ + iterationWork body work d₀ fuel a₀ s₀ + 1)
    nlinarith [hsumC, hscaled]
  · change memoryState frontier y = (Memory.spec w).clientState s₀ (iterate body d₀ fuel a₀)
    rw [clientState_width w]
    exact hym
  · intro i
    change y.regs (st i) = output ((Memory.spec w).clientResult s₀ (iterate body d₀ fuel a₀)) i
    rw [clientResult_width w]
    exact hys i

end RealizesBounded
end Cslib.WordRAM.Realization
