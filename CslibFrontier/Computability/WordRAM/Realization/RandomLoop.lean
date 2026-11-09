/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Loop
public import CslibFrontier.Computability.WordRAM.Realization.Random

import CslibFrontier.Computability.WordRAM.SymbolicExec
/-!
# Runtime-bounded loops with private coins

`RealizesRand.iterate` realizes a runtime-bounded loop whose body is a memory client with private
coins. The loop is any family `loop d n a` satisfying the iteration equations
`loop d 0 a = pure a` and `loop d (n + 1) a = body (d, a) >>= loop d n`. The client need not be
rewritten into a canonical form: a recursive client such as `link methods (contractTimes n)`
satisfies these equations directly. The native code is the loop of `Realizes.iterateRuntime`
(`loopEmit`) around the body's emitter.

Every body run must satisfy the body's domain, and the body's time and `rand` budgets must stay
within the uniform per-iteration budgets `T` and `R`, at every state that the loop reaches with
positive probability. With `n` iterations the loop then takes `n * (T + 1)` units of time and at
most `n * R` `rand` calls on every path. Its law is the law of the loop's run.

## Main results

* `RealizesRand.iterate`: one uniform body certificate realizes a runtime-bounded loop.

The rule is original infrastructure over the existing native loop and `ExecRandLaw`.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {δ σ : Type} {k l : ℕ}

namespace RealizesRand

/-- **Loops.** One uniform body certificate realizes a runtime-bounded loop, given by its
iteration equations. The visible domain asks for the body's domain and per-iteration budgets at
every supported state reached after fewer than `fuel` iterations. -/
theorem iterate (input : δ ↪ (Fin k → ℕ)) (output : σ ↪ (Fin l → ℕ))
    {body : δ × σ → ProbOracleComp Memory.Op.Result σ}
    {loop : δ → ℕ → σ → ProbOracleComp Memory.Op.Result σ}
    (hzero : ∀ d a, loop d 0 a = pure a)
    (hsucc : ∀ d n a, loop d (n + 1) a = body (d, a) >>= loop d n)
    {safe : ℕ → δ × σ → Memory.State → Prop} {time calls : δ × σ → Memory.State → ℕ}
    (T R : (δ × σ) × ℕ → Memory.State → ℕ)
    (h : RealizesRand .exact body (appendWords input output) output safe time calls) :
    RealizesRand .exact (fun ((d, a), fuel) => loop d fuel a)
      (((appendWords input output).prodMap (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
        (Fin.appendEquiv (k + l) 1).toEmbedding) output
      (fun w ((d, a), fuel) s => ∀ j < fuel, ∀ b s',
        (b, s') ∈ ((Memory.spec w).toRandomized.withCoins.run (loop d j a) s).support →
          safe w (d, b) s' ∧ time (d, b) s' ≤ T ((d, a), fuel) s ∧
            calls (d, b) s' ≤ R ((d, a), fuel) s)
      (fun ((d, a), fuel) s => fuel * (T ((d, a), fuel) s + 1))
      (fun ((d, a), fuel) s => fuel * R ((d, a), fuel) s) := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨l + n + 3, C + l + 5, loopEmit emit, ?_⟩
  intro r frontier src tmp hi hd hf hs
  let st : Fin l → Fin r := fun i => tmp (stateSlot i)
  let ctr := tmp (counterSlot l n)
  let zero := tmp (zeroSlot l n)
  let one := tmp (oneSlot l n)
  let bt : Fin (l + n + 1) → Fin r := fun i => tmp (bodySlot i)
  let env : Fin k → Fin r := fun i => src ⟨i.val, by omega⟩
  let bs := Fin.append env st
  have hval {a b : Fin (l + (l + n + 3) + 1)} (h : tmp a = tmp b) : a.val = b.val :=
    congrArg Fin.val (hi h)
  have hst : Function.Injective st := fun i j h => Fin.ext (hval h)
  have hbt : Function.Injective bt := fun i j h => by
    have := hval h
    dsimp only [bodySlot] at this
    exact Fin.ext (by omega)
  have hbdis : ∀ i j, bs i ≠ bt j := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [bs, Fin.append_left] using hd (⟨i.val, by omega⟩ : Fin (k + l + 1)) (bodySlot j)
    · simp only [bs, Fin.append_right]
      intro h
      have := hval h
      dsimp only [stateSlot, bodySlot] at this
      omega
  have hbs : ∀ i, bs i ≠ frontier := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [bs, Fin.append_left] using hs (⟨i.val, by omega⟩ : Fin (k + l + 1))
    · simpa only [bs, Fin.append_right] using hf (stateSlot i)
  obtain ⟨hnw, hrun⟩ := he frontier bs bt hbt hbdis (fun j => hf _) hbs
  have houtdis : ∀ i j : Fin l, bt (Fin.castAdd (n + 1) i) ≠ st j := fun i j h => by
    have := hval h
    dsimp only [bodySlot, stateSlot] at this
    omega
  have hct : ctr ≠ zero := fun h => by have := hval h; simp [counterSlot, zeroSlot] at this
  have hco : ctr ≠ one := fun h => by have := hval h; simp [counterSlot, oneSlot] at this
  have hzo : zero ≠ one := fun h => by have := hval h; simp [zeroSlot, oneSlot] at this
  have hregbt (a : Fin (l + (l + n + 3) + 1)) (ha : a.val < l + 3) : ∀ j, bt j ≠ tmp a :=
    fun j h => by
      have := hval h
      dsimp only [bodySlot] at this
      omega
  have hregst (a : Fin (l + (l + n + 3) + 1)) (ha : l ≤ a.val) : ∀ i, st i ≠ tmp a :=
    fun i h => by
      have := hval h
      dsimp only [stateSlot] at this
      omega
  refine ⟨?_, ?_⟩
  · change ¬(loopEmit emit frontier src tmp).ReadsWidth
    simpa [loopEmit, loopBody, Code.ReadsWidth, Op.ReadsWidth, Op.exactBin,
      copyBank_not_readsWidth] using hnw
  intro w ⟨⟨d₀, a₀⟩, fuel⟩ x hx hin hsafe hv
  let s₀ := memoryState frontier x
  let D := (Memory.spec w).toRandomized.withCoins
  let T₀ := T ((d₀, a₀), fuel) s₀
  let R₀ := R ((d₀, a₀), fuel) s₀
  let K := C * (T₀ + 1) + l + 5
  let Q : Data r → Prop := fun y => ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i
  let obs : Data r → (Fin l → ℕ) × Memory.State :=
    fun y => (fun i => y.regs (st i), memoryState frontier y)
  let F : σ × Memory.State → (Fin l → ℕ) × Memory.State := fun (b, s) => (output b, s)
  let Good : ℕ → σ → Memory.State → Prop := fun j a s => ∀ i < j, ∀ b s',
    (b, s') ∈ (D.run (loop d₀ i a) s).support →
      safe w (d₀, b) s' ∧ time (d₀, b) s' ≤ T₀ ∧ calls (d₀, b) s' ≤ R₀
  let I : ℕ → σ → Memory.State → Data r → Prop := fun j a s y =>
    y.Bounded w ∧ memoryState frontier y = s ∧ (∀ i, y.regs (env i) = input d₀ i) ∧
      (∀ i, y.regs (st i) = output a i) ∧ y.regs ctr = j ∧ y.regs zero = 0 ∧ Good j a s ∧
      (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s (loop d₀ j a) ∧ Q y
  have key : ∀ j a s y, I j a s y →
      ExecRandLaw w (.loop (.lt zero ctr) (loopBody emit frontier src tmp)) y Q (j * K + 2)
        (j * R₀) obs ((D.run (loop d₀ j a) s).map F) := by
    intro j
    induction j with
    | zero =>
      rintro a s y ⟨-, hym, -, hys, hyc, hyz, -, -, hyQ⟩
      have hexit : ¬(Cond.lt zero ctr).Holds y := by
        change ¬y.regs zero < y.regs ctr
        rw [hyc, hyz]
        exact Nat.lt_irrefl 0
      refine ((ExecRandLaw.loop_exit (body := loopBody emit frontier src tmp) (P := Q) (f := obs)
        hexit hyQ).mono (fun _ h => h) (by simp) (Nat.zero_le _)).congr_law ?_
      rw [hzero, RandomizedSpec.run_pure, PMF.pure_map]
      exact congrArg PMF.pure (Prod.ext (funext hys) hym)
    | succ j ih =>
      rintro a s y ⟨hyb, hym, hye, hys, hyc, hyz, hgood, hyv, hyQ⟩
      have hself : (a, s) ∈ (D.run (loop d₀ 0 a) s).support := by
        rw [hzero, RandomizedSpec.run_pure, PMF.support_pure]
        rfl
      obtain ⟨hsafe₀, htime₀, hcalls₀⟩ := hgood 0 (Nat.succ_pos j) a s hself
      rw [hsucc] at hyv
      have hyv' : D.toSpec.DemonicValid s ((body (d₀, a)).bind (loop d₀ j)) := hyv
      obtain ⟨hvB, hvL⟩ := StateTransitionSpec.DemonicValid.of_bind hyv'
      have hinbody : y.regs ∘ bs = (appendWords input output) (d₀, a) := by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simpa [bs, appendWords, Fin.appendEquiv] using hye i
        · simpa [bs, appendWords, Fin.appendEquiv] using hys i
      let ν := (D.run (body (d₀, a)) s).map F
      have hB := ((hrun w (d₀, a) y hyb hinbody (hym ▸ hsafe₀) (hym ▸ hvB)).withBounded
        hyb).withSupport
      rw [hym] at hB
      -- The deterministic tail of an iteration: copy the result into the state words and count
      -- down.
      let P' : Data r → Prop := fun y' => y'.Bounded w ∧ (∀ i, y'.regs (env i) = input d₀ i) ∧
        y'.regs ctr = j ∧ y'.regs zero = 0 ∧ Q y' ∧ obs y' ∈ ν.support
      have hbody : ExecRandLaw w (loopBody emit frontier src tmp) y P'
          (C * (time (d₀, a) s + 1) + (l + 1 + (1 + 1))) (calls (d₀, a) s + 0) obs
          (ν.bind PMF.pure) := by
        refine ExecRandLaw.seq hB fun u ⟨⟨huf, hub⟩, husup⟩ => ?_
        obtain ⟨v, hv', hvm, hvs, hvf⟩ := copyBank_exec
          (fun i : Fin l => bt (Fin.castAdd (n + 1) i)) st zero hst houtdis w u
        have hvctr : v.regs ctr = j + 1 := by
          rw [hvf _ (hregst _ (by simp [counterSlot])),
            huf _ (hf _) (hregbt _ (by simp [counterSlot]))]
          exact hyc
        have hvzero : v.regs zero = 0 := by
          rw [hvf _ (hregst _ (by simp [zeroSlot])), huf _ (hf _) (hregbt _ (by simp [zeroSlot]))]
          exact hyz
        have h1 : Fits w 1 := (hyb.1 ctr).of_le (by omega)
        have hjfit : Fits w j := (hyb.1 ctr).of_le (by omega)
        let t := v.set one 1
        let y' := t.set ctr j
        have ht : ExecWithin (B := .exact) w (.op (.const one 1)) v t 1 := ExecWithin.const h1
        have htc : t.regs ctr = j + 1 := by wram_simp [t, hvctr]
        have htone : t.regs one = 1 := by simp [t, Data.set]
        have hdec : ExecWithin w (.op (.exactBin .sub ctr ctr one)) t y' 1 := by
          wram_exec [htc, htone]
        have hobs : obs y' =
            ((fun i : Fin l => u.regs (bt (Fin.castAdd (n + 1) i))), memoryState frontier u) := by
          refine Prod.ext (funext fun i => ?_) (Memory.State.ext hvm ?_)
          · change (t.set ctr j).regs (st i) = _
            wram_simp [t, st, one, ctr]
            exact hvs i
          · change (t.set ctr j).regs frontier = u.regs frontier
            wram_simp [t]
            exact hvf frontier fun i => hf _
        rw [← hobs]
        refine ExecRandLaw.of_execWithin (hv'.seq (ht.seq hdec)) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact (hv'.seq (ht.seq hdec)).bounded hub
        · intro i
          wram_simp [y', t]
          rw [hvf _ fun _ => (hd _ _).symm, huf _ (hs _) fun _ => (hd _ _).symm]
          exact hye i
        · wram_simp [y']
        · wram_simp [y', t, hvzero]
        · intro i hif htmp
          wram_simp [y', t]
          rw [hvf _ fun _ => htmp _, huf _ hif fun _ => htmp _]
          exact hyQ i hif htmp
        · rw [hobs]
          exact husup
      rw [PMF.bind_pure] at hbody
      have : Nonempty σ := ⟨a⟩
      let κ : (Fin l → ℕ) × Memory.State → PMF ((Fin l → ℕ) × Memory.State) := fun (v, s') =>
        (D.run (loop d₀ j (Function.invFun output v)) s').map F
      have hdecode : ∀ b, Function.invFun output (output b) = b :=
        Function.leftInverse_invFun output.injective
      have hcond : (Cond.lt zero ctr).Holds y := by
        change y.regs zero < y.regs ctr
        rw [hyc, hyz]
        exact Nat.succ_pos j
      refine ((ExecRandLaw.loop_iter (κ := κ) (Q := Q) (f := obs) (T₂ := j * K + 2)
        (R₂ := j * R₀) hcond hbody
        fun y' ⟨hy'b, hy'e, hy'c, hy'z, hy'Q, hy'sup⟩ => ?_).mono (fun _ h => h) ?_ ?_).congr_law
        ?_
      · obtain ⟨⟨b, s'⟩, hmem, hb⟩ := (PMF.mem_support_map_iff _ _ _).mp hy'sup
        obtain ⟨hbout, hbs⟩ := Prod.mk.inj hb
        obtain ⟨tr, hrunB⟩ := D.exists_clientRun_of_mem_support hvB hmem
        have hκ : κ (obs y') = (D.run (loop d₀ j b) s').map F := by
          change (D.run (loop d₀ j (Function.invFun output (fun i => y'.regs (st i))))
            (memoryState frontier y')).map F = _
          rw [← hbout, hdecode, ← hbs]
        rw [hκ]
        refine ih b s' y' ⟨hy'b, hbs.symm, hy'e, fun i => (congrFun hbout i).symm, hy'c, hy'z,
          fun i hi b' s'' hmem' => hgood (i + 1) (by omega) b' s'' ?_, hvL b s' tr hrunB, hy'Q⟩
        rw [hsucc, RandomizedSpec.run_bind, PMF.mem_support_bind_iff]
        exact ⟨(b, s'), hmem, hmem'⟩
      · have := Nat.mul_le_mul_left C (Nat.add_le_add_right htime₀ 1)
        change C * (time (d₀, a) s + 1) + (l + 1 + (1 + 1)) +
          (j * (C * (T₀ + 1) + l + 5) + 2) + 2 ≤ (j + 1) * (C * (T₀ + 1) + l + 5) + 2
        rw [Nat.succ_mul]
        omega
      · rw [Nat.add_zero, Nat.succ_mul]
        omega
      · change ((D.run (body (d₀, a)) s).map F).bind κ = (D.run (loop d₀ (j + 1) a) s).map F
        rw [PMF.bind_map, hsucc, RandomizedSpec.run_bind, PMF.map_bind]
        congr 1
        funext ⟨b, s'⟩
        simp only [Function.comp_apply, κ, F, hdecode]
  have henv (i : Fin k) : x.regs (env i) = input d₀ i := by
    have hh : x.regs (src (Fin.castAdd 1 (Fin.castAdd l i))) = input d₀ i := by
      simpa [appendWords, Fin.appendEquiv] using congrFun hin (Fin.castAdd 1 (Fin.castAdd l i))
    exact hh
  have hstate (i : Fin l) : x.regs (src ⟨k + i.val, by omega⟩) = output a₀ i := by
    have hh : x.regs (src (Fin.castAdd 1 (Fin.natAdd k i))) = output a₀ i := by
      simpa [appendWords, Fin.appendEquiv] using congrFun hin (Fin.castAdd 1 (Fin.natAdd k i))
    exact hh
  have hfuel : x.regs (src ⟨k + l, by omega⟩) = fuel := by
    have hh : x.regs (src (Fin.natAdd (k + l) 0)) = fuel := by
      simpa [Fin.appendEquiv] using congrFun hin (Fin.natAdd (k + l) 0)
    exact hh
  obtain ⟨a, ha, ham, has, haf⟩ := copyBank_exec
    (fun i : Fin l => src ⟨k + i.val, by omega⟩) st zero hst (fun _ _ => hd _ _) w x
  let b := a.set ctr fuel
  let z := b.set zero 0
  have hafuel : a.regs (src ⟨k + l, by omega⟩) = fuel := by
    rw [haf _ (fun _ => (hd _ _).symm)]
    exact hfuel
  have hc : ExecWithin (B := .exact) w (.op (.copy ctr (src ⟨k + l, by omega⟩))) a b 1 := by
    wram_exec [hafuel]
  have hz : ExecWithin (B := .exact) w (.op (.const zero 0)) b z 1 :=
    ExecWithin.const (fits_zero w)
  have hIz : I fuel a₀ s₀ z := by
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
  have hloop := ExecRandLaw.seq_det ha (ExecRandLaw.seq_det hc (ExecRandLaw.seq_det hz
    (key fuel a₀ s₀ z hIz)))
  refine hloop.mono (fun _ h => h) ?_ le_rfl
  change l + 1 + (1 + (1 + (fuel * (C * (T₀ + 1) + l + 5) + 2))) ≤
    (C + l + 5) * (fuel * (T₀ + 1) + 1)
  have h₁ : fuel * (l + 5) ≤ (l + 5) * (fuel * (T₀ + 1)) := by
    rw [Nat.mul_comm fuel]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have h₂ : fuel * (C * (T₀ + 1) + l + 5) = C * (fuel * (T₀ + 1)) + fuel * (l + 5) := by ring
  have h₃ : (C + l + 5) * (fuel * (T₀ + 1) + 1) =
      C * (fuel * (T₀ + 1)) + (l + 5) * (fuel * (T₀ + 1)) + (C + l + 5) := by ring
  rw [h₂, h₃]
  omega

end RealizesRand

end Cslib.WordRAM.Realization
