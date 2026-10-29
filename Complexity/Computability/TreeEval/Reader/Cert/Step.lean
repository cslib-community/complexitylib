/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Tuple
public import Complexity.Computability.TreeEval.Reader.Cert.Weight
public import Complexity.Computability.TreeEval.Reader.Cert.Regs
public import Complexity.Computability.TreeEval.Reader.Cert.Offset

/-!
# The step of the Tree Evaluation read machine within its space budget

The halting test, the address and the step of `Cslib.TreeEval.Reader.machine`, on tuples, are
computable within the space budget `Cslib.TreeEval.Reader.stepBudget`: the length of the
encoded tuple, the value length, the height, and the registers with every entry as long as the
prime and the round of the top frame together. On the states the machine reaches, the budget is
`O((h + ℓ) log ℓ)`.

## Main definitions

* `Cslib.TreeEval.Reader.stepBudget`: the space budget of a step.

## Main results

* `Cslib.TreeEval.Reader.stepT_inSpace`: the step within the budget.

## References

* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024]
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval],
  Algorithm 1, which the machine runs.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM ComputableInSpace Iter

/-- The total length of the registers and of the sums of a tuple. -/
def regLen (x : Tuple) : ℕ :=
  x.regs.1.length + x.regs.2.1.length + x.regs.2.2.length + x.acc.length

/-- The encoding of the inputs of a step. -/
abbrev encStepInT : Tuple × Bool ↪ List Bool := encPair encTuple encBool

/-- **The space budget of a step**, on the tuple and the bit read. -/
def stepBudget (y : Tuple × Bool) : ℕ :=
  (encStepInT y).length + y.1.ell + y.1.height + 1 +
    (regLen y.1 + y.1.ell + 1) *
      ((encNat y.1.p).length + (encNat (y.1.stack.headD dfr).round).length +
        (encNat y.1.ell).length + 4)

theorem len_le_stepBudget : (fun y => (encStepInT y).length) ≼ stepBudget :=
  .of_le fun y => by simp only [stepBudget]; omega

theorem ell_le_stepBudget : (fun y : Tuple × Bool => y.1.ell) ≼ stepBudget :=
  .of_le fun y => by simp only [stepBudget]; omega

theorem height_le_stepBudget : (fun y : Tuple × Bool => y.1.height) ≼ stepBudget :=
  .of_le fun y => by simp only [stepBudget]; omega

/-- The product of the length of the registers and of a length bounded by the prime, the round
of the top frame and the value length is within the budget. -/
private theorem mul_le_stepBudget {u v : Tuple × Bool → ℕ}
    (hu : ∀ y, u y ≤ regLen y.1 + y.1.ell + 1)
    (hv : ∀ y, v y ≤ 2 * ((encNat y.1.p).length + (encNat (y.1.stack.headD dfr).round).length +
      (encNat y.1.ell).length + 4)) :
    (fun y => u y * v y) ≼ stepBudget := by
  refine ⟨2, fun y => ?_⟩
  have := Nat.mul_le_mul (hu y) (hv y)
  simp only [stepBudget]
  nlinarith

private theorem length_get_le_regLen (x : Tuple) (r : Fin 3) :
    (x.regs.get r).length ≤ regLen x := by
  fin_cases r <;> simp [Regs.get, regLen] <;> omega

/-! ### Projections -/

section Proj

private theorem projT_inSpace {β : Type} {encB : β ↪ List Bool} {f : Tuple × Bool → β}
    (h : ComputableInSpace f encStepInT encB fun y => (encStepInT y).length) :
    ComputableInSpace f encStepInT encB stepBudget :=
  h.weaken len_le_stepBudget

private theorem hTup : ComputableInSpace (fun y : Tuple × Bool => y.1) encStepInT encTuple
    stepBudget := projT_inSpace (fst _ _)

private theorem hBit : ComputableInSpace (fun y : Tuple × Bool => y.2) encStepInT encBool
    stepBudget := projT_inSpace (snd _ _)

private theorem hParams : ComputableInSpace (fun y : Tuple × Bool => y.1.1.1) encStepInT
    (encPair encNat (encPair encNat encNat)) stepBudget := fst' (fst' hTup)

theorem ell_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.ell) encStepInT encNat
    stepBudget := fst' hParams

theorem height_inSpace :
    ComputableInSpace (fun y : Tuple × Bool => y.1.height) encStepInT encNat
      stepBudget := fst' (snd' hParams)

private theorem hP : ComputableInSpace (fun y : Tuple × Bool => y.1.p) encStepInT encNat
    stepBudget := snd' (snd' hParams)

private theorem hRegs : ComputableInSpace
    (fun y : Tuple × Bool => y.1.regs) encStepInT encRegs
    stepBudget := snd' (fst' hTup)

private theorem hStackMode : ComputableInSpace (fun y : Tuple × Bool => y.1.2.1) encStepInT
    (encPair (encList encFrame) encMode) stepBudget := fst' (snd' hTup)

theorem stack_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.stack) encStepInT
    (encList encFrame) stepBudget := fst' hStackMode

private theorem hMode : ComputableInSpace
    (fun y : Tuple × Bool => y.1.mode) encStepInT encMode
    stepBudget := snd' hStackMode

private theorem hCtl : ComputableInSpace
    (fun y : Tuple × Bool => y.1.2.2) encStepInT encCtlTuple
    stepBudget := snd' (snd' hTup)

theorem tag_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.tag) encStepInT
    (encFinEnum (Fin 7)) stepBudget := fst' hCtl

theorem n₁_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.n₁) encStepInT encNat
    stepBudget := fst' (snd' hCtl)

private theorem hN₂ : ComputableInSpace (fun y : Tuple × Bool => y.1.n₂) encStepInT encNat
    stepBudget := fst' (snd' (snd' hCtl))

private theorem hAcc : ComputableInSpace (fun y : Tuple × Bool => y.1.acc) encStepInT
    (encList encNat) stepBudget := snd' (snd' (snd' hCtl))

/-- The top frame. -/
private theorem hTop : ComputableInSpace
    (fun y : Tuple × Bool => y.1.stack.headD dfr) encStepInT
    encFrame stepBudget :=
  budget_headD dfr stack_inSpace

/-- The rest of the stack. -/
theorem rest_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.stack.tail) encStepInT
    (encList encFrame) stepBudget :=
  budget_tail stack_inSpace

/-- A function of the finite fields of the top frame. -/
private theorem hTopFinite {β : Type} {encB : β ↪ List Bool} (g : Fin 4 × Bool × Fin 3 → β) :
    ComputableInSpace (fun y : Tuple × Bool => g (Frame.equiv (y.1.stack.headD dfr)).2)
      encStepInT encB stepBudget :=
  budget_comp_linear (f := fun y : Tuple × Bool => y.1.stack.headD dfr) (frameFinite_inSpace g)
    hTop

private theorem hRound : ComputableInSpace
    (fun y : Tuple × Bool => (y.1.stack.headD dfr).round)
    encStepInT encNat stepBudget :=
  budget_comp_linear round_inSpace hTop

/-- A function of the mode. -/
private theorem hModeFinite {β : Type} {encB : β ↪ List Bool} (g : Mode → β) :
    ComputableInSpace (fun y : Tuple × Bool => g y.1.mode) encStepInT encB stepBudget :=
  budget_finite g hMode

end Proj

/-! ### Constructing frames, stacks and tuples -/

section Build

variable {β : Type} {encIn : β ↪ List Bool} {Bs : β → ℕ}

private theorem mkFrame_inSpace {j : β → ℕ} {g : β → Fin 4 × Bool × Fin 3}
    (hj : ComputableInSpace j encIn encNat Bs)
    (hg : ComputableInSpace g encIn (encFinEnum (Fin 4 × Bool × Fin 3)) Bs) :
    ComputableInSpace (fun x => Frame.equiv.symm (j x, g x)) encIn encFrame Bs :=
  (budget_prod hj hg).of_enc_eq fun x => by rw [encFrame_apply, Equiv.apply_symm_apply]

private theorem mkTuple_inSpace {e h p : β → ℕ} {R : β → Regs} {st : β → List Frame} {m : β → Mode}
    {c : β → Fin 7 × ℕ × ℕ × List ℕ}
    (he : ComputableInSpace e encIn encNat Bs)
    (hh : ComputableInSpace h encIn encNat Bs)
    (hp : ComputableInSpace p encIn encNat Bs)
    (hR : ComputableInSpace R encIn encRegs Bs)
    (hst : ComputableInSpace st encIn (encList encFrame) Bs)
    (hm : ComputableInSpace m encIn encMode Bs)
    (hc : ComputableInSpace c encIn encCtlTuple Bs) :
    ComputableInSpace (fun x => ((((e x, h x, p x), R x), (st x, m x), c x) : Tuple))
      encIn encTuple Bs :=
  budget_prod (budget_prod (budget_prod he (budget_prod hh hp)) hR)
    (budget_prod (budget_prod hst hm) hc)

private theorem mkCtl_inSpace {t : β → Fin 7} {a b : β → ℕ} {acc : β → List ℕ}
    (ht : ComputableInSpace t encIn (encFinEnum (Fin 7)) Bs)
    (ha : ComputableInSpace a encIn encNat Bs)
    (hb : ComputableInSpace b encIn encNat Bs)
    (hacc : ComputableInSpace acc encIn (encList encNat) Bs) :
    ComputableInSpace (fun x => (t x, a x, b x, acc x)) encIn encCtlTuple Bs :=
  budget_prod ht (budget_prod ha (budget_prod hb hacc))

end Build

/-! ### The branches of the step -/

section Branches

/-- The encoding of the results of a step. -/
abbrev encStepOut : Tuple × List Bool ↪ List Bool := encPair encTuple encBits

private theorem out_inSpace {T : Tuple × Bool → Tuple}
    (hT : ComputableInSpace T encStepInT encTuple stepBudget) :
    ComputableInSpace (fun y => (T y, ([] : List Bool))) encStepInT encStepOut stepBudget :=
  budget_prod hT (budget_const [] len_le_stepBudget)

private theorem withCtl_inSpace {c : Tuple × Bool → Fin 7 × ℕ × ℕ × List ℕ}
    (hc : ComputableInSpace c encStepInT encCtlTuple stepBudget) :
    ComputableInSpace (fun y => y.1.withCtl (c y)) encStepInT encTuple stepBudget :=
  budget_prod (fst' hTup) (budget_prod hStackMode hc)

private theorem hConstTag (t : Fin 7) :
    ComputableInSpace (fun _ : Tuple × Bool => t) encStepInT
      (encFinEnum (Fin 7)) stepBudget :=
  budget_const t len_le_stepBudget

private theorem hConstNat (n : ℕ) :
    ComputableInSpace (fun _ : Tuple × Bool => n) encStepInT encNat stepBudget :=
  budget_const n len_le_stepBudget

private theorem hNil :
    ComputableInSpace (fun _ : Tuple × Bool => ([] : List ℕ)) encStepInT (encList encNat)
      stepBudget := budget_const [] len_le_stepBudget

theorem succ_inSpace {n : Tuple × Bool → ℕ}
    (hn : ComputableInSpace n encStepInT encNat stepBudget) :
    ComputableInSpace (fun y => n y + 1) encStepInT encNat stepBudget :=
  budget_natSucc hn

/-- The header: reading the value length. -/
private theorem branch0_inSpace :
    ComputableInSpace (fun y : Tuple × Bool => if y.2 then
        (y.1.withCtl (0, y.1.n₁ + 1, 0, []), ([] : List Bool))
      else ((((y.1.n₁, y.1.height, y.1.p), y.1.regs), y.1.2.1, (1, 0, 0, [])), []))
      encStepInT encStepOut stepBudget :=
  budget_ite hBit
    (out_inSpace
      (withCtl_inSpace
        (mkCtl_inSpace (hConstTag 0) (succ_inSpace n₁_inSpace) (hConstNat 0) hNil)))
    (out_inSpace
      (budget_prod
        (budget_prod (budget_prod n₁_inSpace (budget_prod height_inSpace hP)) hRegs)
      (budget_prod hStackMode (mkCtl_inSpace (hConstTag 1) (hConstNat 0) (hConstNat 0) hNil))))

/-- The header: reading the height. -/
private theorem branch1_inSpace :
    ComputableInSpace (fun y : Tuple × Bool => if y.2 then
        (y.1.withCtl (1, y.1.n₁ + 1, 0, []), ([] : List Bool))
      else ((((y.1.ell, y.1.n₁, y.1.p), y.1.regs), y.1.2.1, (2, 2 * y.1.ell + 2, 2, [])), []))
      encStepInT encStepOut stepBudget := by
  have h2e : ComputableInSpace (fun y : Tuple × Bool => 2 * y.1.ell + 2) encStepInT encNat
      stepBudget :=
    (succ_inSpace (succ_inSpace (budget_natAdd ell_inSpace ell_inSpace))).of_enc_eq
      fun _ => by congr 1; omega
  exact budget_ite hBit
    (out_inSpace
      (withCtl_inSpace
        (mkCtl_inSpace (hConstTag 1) (succ_inSpace n₁_inSpace) (hConstNat 0) hNil)))
    (out_inSpace (budget_prod
      (budget_prod (budget_prod ell_inSpace (budget_prod n₁_inSpace hP)) hRegs)
      (budget_prod hStackMode (mkCtl_inSpace (hConstTag 2) h2e (hConstNat 2) hNil))))

private theorem hReplicate :
    ComputableInSpace (fun y : Tuple × Bool => List.replicate y.1.ell 0) encStepInT
      (encList encNat) stepBudget := by
  refine budget_comp replicate (budget_prod ell_inSpace (hConstNat 0)) (.const_mul 64 ?_)
  exact mul_le_stepBudget (fun y => by dsimp only; omega) fun y => by
    simp only [length_encPair]; have : (encNat 0).length = 0 := rfl; omega

/-- The search for the prime. -/
private theorem branch2_inSpace :
    ComputableInSpace (fun y : Tuple × Bool =>
      if y.1.n₂ < y.1.n₁ then
        if y.1.n₁ % y.1.n₂ = 0 then (y.1.withCtl (2, y.1.n₁ + 1, 2, []), ([] : List Bool))
        else (y.1.withCtl (2, y.1.n₁, y.1.n₂ + 1, []), [])
      else ((((y.1.ell, y.1.height, y.1.n₁),
        (List.replicate y.1.ell 0, List.replicate y.1.ell 0, List.replicate y.1.ell 0)),
        ([], .call false 2), runCtl), []))
      encStepInT encStepOut stepBudget := by
  have hlt := budget_natLt hN₂ n₁_inSpace
  have hmod := budget_natMod n₁_inSpace hN₂
  have hz := budget_natIsZero hmod
  have hzeros : ComputableInSpace (fun y : Tuple × Bool =>
      ((List.replicate y.1.ell 0, List.replicate y.1.ell 0, List.replicate y.1.ell 0) : Regs))
      encStepInT encRegs stepBudget :=
    budget_prod hReplicate (budget_prod hReplicate hReplicate)
  have hfound : ComputableInSpace (fun y : Tuple × Bool =>
      ((((y.1.ell, y.1.height, y.1.n₁),
        (List.replicate y.1.ell 0, List.replicate y.1.ell 0, List.replicate y.1.ell 0)),
        ([], Mode.call false 2), runCtl) : Tuple)) encStepInT encTuple stepBudget :=
    mkTuple_inSpace ell_inSpace height_inSpace n₁_inSpace hzeros
      (budget_const (encB := encList encFrame) [] len_le_stepBudget)
      (budget_const (encB := encMode) (.call false 2) len_le_stepBudget)
      (mkCtl_inSpace (hConstTag 3) (hConstNat 0) (hConstNat 0) hNil)
  refine (budget_ite hlt (budget_ite hz
    (out_inSpace
      (withCtl_inSpace
        (mkCtl_inSpace (hConstTag 2) (succ_inSpace n₁_inSpace) (hConstNat 2) hNil)))
    (out_inSpace
      (withCtl_inSpace
        (mkCtl_inSpace (hConstTag 2) n₁_inSpace (succ_inSpace hN₂) hNil))))
    (out_inSpace hfound)).of_enc_eq fun y => ?_
  simp only [decide_eq_true_eq]

private theorem hLt {a b : Tuple × Bool → ℕ}
    (ha : ComputableInSpace a encStepInT encNat stepBudget)
    (hb : ComputableInSpace b encStepInT encNat stepBudget) :
    ComputableInSpace (fun y => decide (a y < b y)) encStepInT encBool stepBudget :=
  budget_natLt ha hb

private theorem hSgnVal {p : Tuple × Bool → ℕ} {neg : Tuple × Bool → Bool}
    (hp : ComputableInSpace p encStepInT encNat stepBudget)
    (hneg : ComputableInSpace neg encStepInT encBool stepBudget) :
    ComputableInSpace (fun y => sgnVal (p y) (neg y)) encStepInT encNat stepBudget :=
  (budget_ite hneg (budget_natPred hp) (hConstNat 1))
    |>.of_enc_eq fun y => by simp only [sgnVal]

private theorem withRegsModeCtl_inSpace {R : Tuple × Bool → Regs} {st : Tuple × Bool → List Frame}
    {m : Tuple × Bool → Mode} {c : Tuple × Bool → Fin 7 × ℕ × ℕ × List ℕ}
    (hR : ComputableInSpace R encStepInT encRegs stepBudget)
    (hst : ComputableInSpace st encStepInT (encList encFrame) stepBudget)
    (hm : ComputableInSpace m encStepInT encMode stepBudget)
    (hc : ComputableInSpace c encStepInT encCtlTuple stepBudget) :
    ComputableInSpace (fun y => y.1.with (R y) (st y) (m y) (c y)) encStepInT encTuple
      stepBudget :=
  mkTuple_inSpace ell_inSpace height_inSpace hP hR hst hm hc

/-- Reading a leaf. -/
private theorem branch4_inSpace :
    ComputableInSpace (fun y : Tuple × Bool =>
      if y.1.mode.isCall then
        if y.1.n₁ < y.1.ell then
          (y.1.with (y.1.regs.set y.1.mode.target (modifyAt (y.1.regs.get y.1.mode.target) y.1.n₁
            (addMod y.1.p (if y.2 then sgnVal y.1.p y.1.mode.neg else 0)))) y.1.stack y.1.mode
            (4, y.1.n₁ + 1, 0, []), ([] : List Bool))
        else (y.1.with y.1.regs y.1.stack .ret runCtl, [])
      else (y.1, []))
      encStepInT encStepOut stepBudget := by
  have ht := hModeFinite (encB := encReg) Mode.target
  have hneg := hModeFinite (encB := encBool) Mode.neg
  have hcall := hModeFinite (encB := encBool) Mode.isCall
  have hc := budget_ite hBit (hSgnVal hP hneg) (hConstNat 0)
  have hmod := modifyAt_inSpace (get_inSpace hRegs ht) n₁_inSpace hP hc
  have hset := set_inSpace hRegs ht hmod
  refine (budget_ite hcall (budget_ite (hLt n₁_inSpace ell_inSpace)
    (out_inSpace (withRegsModeCtl_inSpace hset stack_inSpace hMode
      (mkCtl_inSpace (hConstTag 4) (succ_inSpace n₁_inSpace) (hConstNat 0) hNil)))
    (out_inSpace (withRegsModeCtl_inSpace hRegs stack_inSpace
      (budget_const (encB := encMode) .ret len_le_stepBudget)
      (mkCtl_inSpace (hConstTag 3) (hConstNat 0) (hConstNat 0) hNil))))
    (out_inSpace hTup)).of_enc_eq fun y => ?_
  simp only [decide_eq_true_eq]

private theorem hFrTarget : ComputableInSpace
    (fun y : Tuple × Bool => (y.1.stack.headD dfr).target)
    encStepInT encReg stepBudget :=
  hTopFinite (fun g => g.2.2)

private theorem hFrNeg : ComputableInSpace (fun y : Tuple × Bool => (y.1.stack.headD dfr).neg)
    encStepInT encBool stepBudget :=
  hTopFinite (fun g => g.2.1)

private theorem hRegPlus (k : Fin 3) :
    ComputableInSpace (fun y : Tuple × Bool => (y.1.stack.headD dfr).target + k)
      encStepInT encReg stepBudget :=
  hTopFinite (fun g => g.2.2 + k)

/-- The top frame with a new phase. -/
private theorem hFrPhase (ph : Fin 4) :
    ComputableInSpace (fun y : Tuple × Bool => { y.1.stack.headD dfr with phase := ph })
      encStepInT encFrame stepBudget :=
  (mkFrame_inSpace hRound (hTopFinite (encB := encFinEnum (Fin 4 × Bool × Fin 3))
    fun g => (ph, g.2.1, g.2.2))).of_enc_eq fun _ => rfl

/-- The pass over the table of the gate of the top frame. -/
private theorem branch5_inSpace :
    ComputableInSpace (fun y : Tuple × Bool =>
      if y.1.stack.isEmpty then (y.1, ([] : List Bool))
      else if y.1.n₁ < tableLength y.1.ell then
        if y.2 then
          (y.1.withCtl (5, y.1.n₁ + 1, 0, modifyAt y.1.acc (y.1.n₁ % y.1.ell) (addMod y.1.p
            (weight y.1.p y.1.ell (y.1.n₁ / y.1.ell)
              (y.1.regs.get ((y.1.stack.headD dfr).target + 1))
              (y.1.regs.get ((y.1.stack.headD dfr).target + 2))))), [])
        else (y.1.withCtl (5, y.1.n₁ + 1, 0, y.1.acc), [])
      else (y.1.with (subtractSums y.1.p (sgnVal y.1.p (y.1.stack.headD dfr).neg)
          (y.1.stack.headD dfr).target y.1.acc y.1.regs)
        ({ y.1.stack.headD dfr with phase := 2 } :: y.1.stack.tail)
        (.call true ((y.1.stack.headD dfr).target + 1)) runCtl, []))
      encStepInT encStepOut stepBudget := by
  have hempty := budget_isEmpty stack_inSpace
  have hG := budget_comp tableLength_inSpace ell_inSpace
    (.const_mul 4096 (ell_le_stepBudget.add (.const 1 _)))
  have hdm := budget_comp_lin natDivMod (linear_mul _) (budget_prod n₁_inSpace ell_inSpace)
  have hk := fst' hdm
  have hi := snd' hdm
  have hx := get_inSpace hRegs (hRegPlus 1)
  have hy := get_inSpace hRegs (hRegPlus 2)
  have hw := budget_comp weight_inSpace
    (budget_prod (budget_prod hP (budget_prod ell_inSpace hk))
    (budget_prod hx hy)) (.const_mul 64 (((length_le (budget_prod (budget_prod hP
      (budget_prod ell_inSpace hk)) (budget_prod hx hy))).add ell_le_stepBudget).add
        (.const 1 _)))
  have hacc' := modifyAt_inSpace hAcc hi hP hw
  have hB : (fun y : Tuple × Bool => (y.1.regs.get (y.1.stack.headD dfr).target).length *
      ((encNat y.1.p).length + 1)) ≼ stepBudget :=
    mul_le_stepBudget (fun y => by
      have := length_get_le_regLen y.1 (y.1.stack.headD dfr).target
      omega) fun y => by omega
  have hsub := subtractSums_inSpace hP (hSgnVal hP hFrNeg) hFrTarget hAcc hRegs hB
  refine (budget_ite hempty (out_inSpace hTup) (budget_ite (hLt n₁_inSpace hG)
    (budget_ite hBit
      (out_inSpace
        (withCtl_inSpace
          (mkCtl_inSpace (hConstTag 5) (succ_inSpace n₁_inSpace) (hConstNat 0) hacc')))
      (out_inSpace
        (withCtl_inSpace
          (mkCtl_inSpace (hConstTag 5) (succ_inSpace n₁_inSpace) (hConstNat 0) hAcc))))
    (out_inSpace (withRegsModeCtl_inSpace hsub (budget_cons (hFrPhase 2) rest_inSpace)
      (hTopFinite (encB := encMode) fun g => .call true (g.2.2 + 1))
      (mkCtl_inSpace (hConstTag 3) (hConstNat 0) (hConstNat 0) hNil))))).of_enc_eq fun y => ?_
  simp only [decide_eq_true_eq]
  rfl

private theorem length_get_scale (R : Regs) (p : ℕ) (r r' : Fin 3) (a : ℕ) :
    ((R.scale p r a).get r').length = (R.get r').length := by
  fin_cases r <;> fin_cases r' <;> simp [Regs.scale, Regs.set, Regs.get]

private theorem length_unitInv_le (p j : ℕ) : (encNat (unitInv p j)).length ≤
    (encNat p).length + 2 := by
  have h₁ := length_encNat_mono (powMod_le (p := p) (a := j + 1)
    (k := p - 2) le_rfl)
  have h₂ := length_encNat_add_le_add p 1
  have : (encNat 1).length = 1 := rfl
  rw [unitInv]; omega

/-- A register scaled by a residue no longer than the prime and the round of the top frame. -/
private theorem scaleT_inSpace {R : Tuple × Bool → Regs} {r : Tuple × Bool → Fin 3}
    {a : Tuple × Bool → ℕ}
    (hR : ComputableInSpace R encStepInT encRegs stepBudget)
    (hr : ComputableInSpace r encStepInT encReg stepBudget)
    (ha : ComputableInSpace a encStepInT encNat stepBudget)
    (hlen : ∀ y r', ((R y).get r').length = (y.1.regs.get r').length)
    (hasz : ∀ y, (encNat (a y)).length ≤
      (encNat y.1.p).length + (encNat (y.1.stack.headD dfr).round).length + 3) :
    ComputableInSpace (fun y => (R y).scale y.1.p (r y) (a y)) encStepInT encRegs
      stepBudget :=
  scale_inSpace hP ha hR hr len_le_stepBudget
    (mul_le_stepBudget
      (fun y => by rw [hlen]; have := length_get_le_regLen y.1 (r y); omega)
      fun y => by have := hasz y; omega)

private theorem hFrame0 : ComputableInSpace (fun y : Tuple × Bool =>
    (⟨0, 0, y.1.mode.neg, y.1.mode.target⟩ : Frame)) encStepInT encFrame stepBudget :=
  (mkFrame_inSpace (hConstNat 0) (hModeFinite (encB := encFinEnum (Fin 4 × Bool × Fin 3))
    fun m => (0, m.neg, m.target))).of_enc_eq fun _ => rfl

private theorem hFrameNext : ComputableInSpace (fun y : Tuple × Bool =>
    (⟨(y.1.stack.headD dfr).round + 1, 0, (y.1.stack.headD dfr).neg,
      (y.1.stack.headD dfr).target⟩ : Frame)) encStepInT encFrame stepBudget :=
  (mkFrame_inSpace (succ_inSpace hRound)
    (hTopFinite (encB := encFinEnum (Fin 4 × Bool × Fin 3))
    fun g => (0, g.2.1, g.2.2))).of_enc_eq fun _ => rfl

private theorem hRun : ComputableInSpace
    (fun _ : Tuple × Bool => runCtl) encStepInT encCtlTuple
    stepBudget := mkCtl_inSpace (hConstTag 3) (hConstNat 0) (hConstNat 0) hNil

/-- The steps of the iterative procedure. -/
private theorem branch3_inSpace :
    ComputableInSpace (fun y : Tuple × Bool => runStepT y.1) encStepInT encStepOut
      stepBudget := by
  have ht := hModeFinite (encB := encReg) Mode.target
  have hcall := hModeFinite (encB := encBool) Mode.isCall
  have hlenEq := budget_natEq (budget_length stack_inSpace) height_inSpace
  have hempty := budget_isEmpty stack_inSpace
  have hph (k : Fin 4) := hTopFinite (encB := encBool) fun g => decide (g.1 = k)
  have hR0 := scaleT_inSpace hRegs (hModeFinite (encB := encReg) fun m => m.target + 1)
    (hConstNat (unitVal 0)) (fun _ _ => rfl) fun y => by
      have : (encNat (unitVal 0)).length = 1 := rfl
      omega
  have hRj := scaleT_inSpace hRegs (hRegPlus 2) (succ_inSpace hRound)
    (fun _ _ => rfl)
    fun y => by
    have := length_encNat_add_le_add (y.1.stack.headD dfr).round 1
    have : (encNat 1).length = 1 := rfl
    omega
  have hinv := budget_comp_linear unitInv_inSpace (budget_prod hP hRound)
  have hR2 := scaleT_inSpace hRegs (hRegPlus 1) hinv (fun _ _ => rfl) fun y => by
    have := length_unitInv_le y.1.p (y.1.stack.headD dfr).round; dsimp only; omega
  have hR3 := scaleT_inSpace hRegs (hRegPlus 2) hinv (fun _ _ => rfl) fun y => by
    have := length_unitInv_le y.1.p (y.1.stack.headD dfr).round; dsimp only; omega
  have hR3' := scaleT_inSpace hR3 (hRegPlus 1) (succ_inSpace (succ_inSpace hRound))
    (fun y r' => length_get_scale _ _ _ _ _) fun y => by
      have := length_encNat_add_le_add (y.1.stack.headD dfr).round 2
      have : (encNat 2).length = 2 := rfl
      rw [show (y.1.stack.headD dfr).round + 1 + 1 = (y.1.stack.headD dfr).round + 2 by omega]
      omega
  have hout := budget_comp mapEqOne_inSpace
    (get_inSpace hRegs (budget_const 2 len_le_stepBudget))
    (.const_mul 64
      ((length_le (get_inSpace hRegs (budget_const 2 len_le_stepBudget))).add (.const 1 _)))
  have hnext := hLt (succ_inSpace hRound) (budget_natPred hP)
  refine (budget_ite hcall
    (budget_ite hlenEq
      (out_inSpace (withCtl_inSpace (mkCtl_inSpace (hConstTag 4) (hConstNat 0) (hConstNat 0) hNil)))
      (out_inSpace (withRegsModeCtl_inSpace hR0 (budget_cons hFrame0 stack_inSpace)
        (hModeFinite (encB := encMode) fun m => .call false (m.target + 1)) hRun)))
    (budget_ite hempty
      (budget_prod (withCtl_inSpace (mkCtl_inSpace (hConstTag 6) (hConstNat 0) (hConstNat 0) hNil))
        hout)
      (budget_ite (hph 0)
        (out_inSpace (withRegsModeCtl_inSpace hRj (budget_cons (hFrPhase 1) rest_inSpace)
          (hTopFinite (encB := encMode) fun g => .call false (g.2.2 + 2)) hRun))
        (budget_ite (hph 1)
          (out_inSpace (withCtl_inSpace (mkCtl_inSpace (hConstTag 5) (hConstNat 0) (hConstNat 0)
            hReplicate)))
          (budget_ite (hph 2)
            (out_inSpace (withRegsModeCtl_inSpace hR2 (budget_cons (hFrPhase 3) rest_inSpace)
              (hTopFinite (encB := encMode) fun g => .call true (g.2.2 + 2)) hRun))
            (budget_ite hnext
              (out_inSpace (withRegsModeCtl_inSpace hR3' (budget_cons hFrameNext rest_inSpace)
                (hTopFinite (encB := encMode) fun g => .call false (g.2.2 + 1)) hRun))
              (out_inSpace (withRegsModeCtl_inSpace hR3 rest_inSpace
                (budget_const (encB := encMode) .ret len_le_stepBudget) hRun)))))))).of_enc_eq
    fun y => ?_
  simp only [runStepT, decide_eq_true_eq]
  rfl

end Branches

/-- **The step within its space budget.** -/
theorem stepT_inSpace : ComputableInSpace stepT encStepInT encStepOut stepBudget := by
  have ht (k : Fin 7) :=
    budget_finite (encC := encBool) (fun t : Fin 7 => decide (t = k)) tag_inSpace
  refine (budget_ite (ht 0) branch0_inSpace (budget_ite (ht 1) branch1_inSpace
    (budget_ite (ht 2) branch2_inSpace (budget_ite (ht 3) branch3_inSpace
      (budget_ite (ht 4) branch4_inSpace (budget_ite (ht 5) branch5_inSpace
        (out_inSpace hTup))))))).of_enc_eq fun y => ?_
  simp only [stepT, decide_eq_true_eq]

end Reader

end Cslib.TreeEval
