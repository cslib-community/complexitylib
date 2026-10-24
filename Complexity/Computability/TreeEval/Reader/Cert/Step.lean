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
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain

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

open Turing MultiTapeTM ComputableTidilyInSpace Iter

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
    (h : ComputableTidilyInSpace f encStepInT encB fun y => (encStepInT y).length) :
    ComputableTidilyInSpace f encStepInT encB stepBudget :=
  h.weaken len_le_stepBudget

private theorem hTup : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1) encStepInT encTuple
    stepBudget := projT_inSpace (fst _ _)

private theorem hBit : ComputableTidilyInSpace (fun y : Tuple × Bool => y.2) encStepInT encBool
    stepBudget := projT_inSpace (snd _ _)

private theorem hParams : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.1.1) encStepInT
    (encPair encNat (encPair encNat encNat)) stepBudget := fst' (fst' hTup)

theorem ell_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.ell) encStepInT encNat
    stepBudget := .of_tidy (fst' hParams)

theorem height_inSpace :
    ComputableInSpace (fun y : Tuple × Bool => y.1.height) encStepInT encNat
      stepBudget := .of_tidy (fst' (snd' hParams))

private theorem hP : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.p) encStepInT encNat
    stepBudget := snd' (snd' hParams)

private theorem hRegs : ComputableTidilyInSpace
    (fun y : Tuple × Bool => y.1.regs) encStepInT encRegs
    stepBudget := snd' (fst' hTup)

private theorem hStackMode : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1) encStepInT
    (encPair (encList encFrame) encMode) stepBudget := fst' (snd' hTup)

theorem stack_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.stack) encStepInT
    (encList encFrame) stepBudget := .of_tidy (fst' hStackMode)

private theorem hMode : ComputableTidilyInSpace
    (fun y : Tuple × Bool => y.1.mode) encStepInT encMode
    stepBudget := snd' hStackMode

private theorem hCtl : ComputableTidilyInSpace
    (fun y : Tuple × Bool => y.1.2.2) encStepInT encCtlTuple
    stepBudget := snd' (snd' hTup)

theorem tag_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.tag) encStepInT
    (encFinEnum (Fin 7)) stepBudget := .of_tidy (fst' hCtl)

theorem n₁_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.n₁) encStepInT encNat
    stepBudget := .of_tidy (fst' (snd' hCtl))

private theorem hN₂ : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.n₂) encStepInT encNat
    stepBudget := fst' (snd' (snd' hCtl))

private theorem hAcc : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.acc) encStepInT
    (encList encNat) stepBudget := snd' (snd' (snd' hCtl))

/-- The top frame. -/
private theorem hTop : ComputableTidilyInSpace
    (fun y : Tuple × Bool => y.1.stack.headD dfr) encStepInT
    encFrame stepBudget :=
  budget_comp_linear (of_inO (.of_linear (ListEncoding.headD (enc := encList encFrame) dfr)))
    stack_inSpace.tidy

/-- The rest of the stack. -/
theorem rest_inSpace : ComputableInSpace (fun y : Tuple × Bool => y.1.stack.tail) encStepInT
    (encList encFrame) stepBudget :=
  .of_tidy (budget_comp_linear (of_inO (.of_linear (ListEncoding.tail encFrame)))
    stack_inSpace.tidy)

/-- A function of the finite fields of the top frame. -/
private theorem hTopFinite {β : Type} {encB : β ↪ List Bool} (g : Fin 4 × Bool × Fin 3 → β) :
    ComputableTidilyInSpace (fun y : Tuple × Bool => g (Frame.equiv (y.1.stack.headD dfr)).2)
      encStepInT encB stepBudget :=
  budget_comp_linear (f := fun y : Tuple × Bool => y.1.stack.headD dfr) (frameFinite_inSpace g).tidy
    hTop

private theorem hRound : ComputableTidilyInSpace
    (fun y : Tuple × Bool => (y.1.stack.headD dfr).round)
    encStepInT encNat stepBudget :=
  budget_comp_linear round_inSpace.tidy hTop

/-- A function of the mode. -/
private theorem hModeFinite {β : Type} {encB : β ↪ List Bool} (g : Mode → β) :
    ComputableTidilyInSpace (fun y : Tuple × Bool => g y.1.mode) encStepInT encB stepBudget :=
  budget_finite g hMode

end Proj

/-! ### Constructing frames, stacks and tuples -/

section Build

variable {β : Type} {encIn : β ↪ List Bool} {Bs : β → ℕ}

private theorem mkFrame_inSpace {j : β → ℕ} {g : β → Fin 4 × Bool × Fin 3}
    (hj : ComputableTidilyInSpace j encIn encNat Bs)
    (hg : ComputableTidilyInSpace g encIn (encFinEnum (Fin 4 × Bool × Fin 3)) Bs) :
    ComputableTidilyInSpace (fun x => Frame.equiv.symm (j x, g x)) encIn encFrame Bs :=
  (budget_prod hj hg).of_enc_eq fun x => by rw [encFrame_apply, Equiv.apply_symm_apply]

private theorem cons_inSpace {ε : Type} {enc : ε ↪ List Bool} {a : β → ε} {l : β → List ε}
    (ha : ComputableTidilyInSpace a encIn enc Bs)
    (hl : ComputableTidilyInSpace l encIn (encList enc) Bs) :
    ComputableTidilyInSpace (fun x => a x :: l x) encIn (encList enc) Bs :=
  budget_comp_linear (of_inO (ComputableTidilyInDegree.cons enc).inO_one) (budget_prod ha hl)

private theorem mkTuple_inSpace {e h p : β → ℕ} {R : β → Regs} {st : β → List Frame} {m : β → Mode}
    {c : β → Fin 7 × ℕ × ℕ × List ℕ}
    (he : ComputableTidilyInSpace e encIn encNat Bs)
    (hh : ComputableTidilyInSpace h encIn encNat Bs)
    (hp : ComputableTidilyInSpace p encIn encNat Bs)
    (hR : ComputableTidilyInSpace R encIn encRegs Bs)
    (hst : ComputableTidilyInSpace st encIn (encList encFrame) Bs)
    (hm : ComputableTidilyInSpace m encIn encMode Bs)
    (hc : ComputableTidilyInSpace c encIn encCtlTuple Bs) :
    ComputableTidilyInSpace (fun x => ((((e x, h x, p x), R x), (st x, m x), c x) : Tuple))
      encIn encTuple Bs :=
  budget_prod (budget_prod (budget_prod he (budget_prod hh hp)) hR)
    (budget_prod (budget_prod hst hm) hc)

private theorem mkCtl_inSpace {t : β → Fin 7} {a b : β → ℕ} {acc : β → List ℕ}
    (ht : ComputableTidilyInSpace t encIn (encFinEnum (Fin 7)) Bs)
    (ha : ComputableTidilyInSpace a encIn encNat Bs)
    (hb : ComputableTidilyInSpace b encIn encNat Bs)
    (hacc : ComputableTidilyInSpace acc encIn (encList encNat) Bs) :
    ComputableTidilyInSpace (fun x => (t x, a x, b x, acc x)) encIn encCtlTuple Bs :=
  budget_prod ht (budget_prod ha (budget_prod hb hacc))

end Build

/-! ### The branches of the step -/

section Branches

/-- The encoding of the results of a step. -/
abbrev encStepOut : Tuple × List Bool ↪ List Bool := encPair encTuple encBits

private theorem out_inSpace {T : Tuple × Bool → Tuple}
    (hT : ComputableTidilyInSpace T encStepInT encTuple stepBudget) :
    ComputableTidilyInSpace (fun y => (T y, ([] : List Bool))) encStepInT encStepOut stepBudget :=
  budget_prod hT (budget_const [] len_le_stepBudget)

private theorem withCtl_inSpace {c : Tuple × Bool → Fin 7 × ℕ × ℕ × List ℕ}
    (hc : ComputableTidilyInSpace c encStepInT encCtlTuple stepBudget) :
    ComputableTidilyInSpace (fun y => y.1.withCtl (c y)) encStepInT encTuple stepBudget :=
  budget_prod (fst' hTup) (budget_prod hStackMode hc)

private theorem hConstTag (t : Fin 7) :
    ComputableTidilyInSpace (fun _ : Tuple × Bool => t) encStepInT
      (encFinEnum (Fin 7)) stepBudget :=
  budget_const t len_le_stepBudget

private theorem hConstNat (n : ℕ) :
    ComputableTidilyInSpace (fun _ : Tuple × Bool => n) encStepInT encNat stepBudget :=
  budget_const n len_le_stepBudget

private theorem hNil :
    ComputableTidilyInSpace (fun _ : Tuple × Bool => ([] : List ℕ)) encStepInT (encList encNat)
      stepBudget := budget_const [] len_le_stepBudget

theorem succ_inSpace {n : Tuple × Bool → ℕ}
    (hn : ComputableInSpace n encStepInT encNat stepBudget) :
    ComputableInSpace (fun y => n y + 1) encStepInT encNat stepBudget := by
  have hn := hn.tidy
  exact .of_tidy (budget_comp_lin natSucc linear_succ hn)

/-- The header: reading the value length. -/
private theorem branch0_inSpace :
    ComputableTidilyInSpace (fun y : Tuple × Bool => if y.2 then
        (y.1.withCtl (0, y.1.n₁ + 1, 0, []), ([] : List Bool))
      else ((((y.1.n₁, y.1.height, y.1.p), y.1.regs), y.1.2.1, (1, 0, 0, [])), []))
      encStepInT encStepOut stepBudget :=
  budget_ite hBit
    (out_inSpace
      (withCtl_inSpace
        (mkCtl_inSpace (hConstTag 0) (succ_inSpace n₁_inSpace).tidy (hConstNat 0) hNil)))
    (out_inSpace
      (budget_prod
        (budget_prod (budget_prod n₁_inSpace.tidy (budget_prod height_inSpace.tidy hP)) hRegs)
      (budget_prod hStackMode (mkCtl_inSpace (hConstTag 1) (hConstNat 0) (hConstNat 0) hNil))))

/-- The header: reading the height. -/
private theorem branch1_inSpace :
    ComputableTidilyInSpace (fun y : Tuple × Bool => if y.2 then
        (y.1.withCtl (1, y.1.n₁ + 1, 0, []), ([] : List Bool))
      else ((((y.1.ell, y.1.n₁, y.1.p), y.1.regs), y.1.2.1, (2, 2 * y.1.ell + 2, 2, [])), []))
      encStepInT encStepOut stepBudget := by
  have h2e : ComputableTidilyInSpace (fun y : Tuple × Bool => 2 * y.1.ell + 2) encStepInT encNat
      stepBudget := by
    have h := budget_comp_lin natAdd linear_succ (budget_prod ell_inSpace.tidy ell_inSpace.tidy)
    exact (succ_inSpace (succ_inSpace (.of_tidy h))).tidy.of_enc_eq fun y => by congr 1; omega
  exact budget_ite hBit
    (out_inSpace
      (withCtl_inSpace
        (mkCtl_inSpace (hConstTag 1) (succ_inSpace n₁_inSpace).tidy (hConstNat 0) hNil)))
    (out_inSpace (budget_prod
      (budget_prod (budget_prod ell_inSpace.tidy (budget_prod n₁_inSpace.tidy hP)) hRegs)
      (budget_prod hStackMode (mkCtl_inSpace (hConstTag 2) h2e (hConstNat 2) hNil))))

private theorem hReplicate :
    ComputableTidilyInSpace (fun y : Tuple × Bool => List.replicate y.1.ell 0) encStepInT
      (encList encNat) stepBudget := by
  refine budget_comp replicate (budget_prod ell_inSpace.tidy (hConstNat 0)) (.const_mul 64 ?_)
  exact mul_le_stepBudget (fun y => by dsimp only; omega) fun y => by
    simp only [length_encPair]; have : (encNat 0).length = 0 := rfl; omega

/-- The search for the prime. -/
private theorem branch2_inSpace :
    ComputableTidilyInSpace (fun y : Tuple × Bool =>
      if y.1.n₂ < y.1.n₁ then
        if y.1.n₁ % y.1.n₂ = 0 then (y.1.withCtl (2, y.1.n₁ + 1, 2, []), ([] : List Bool))
        else (y.1.withCtl (2, y.1.n₁, y.1.n₂ + 1, []), [])
      else ((((y.1.ell, y.1.height, y.1.n₁),
        (List.replicate y.1.ell 0, List.replicate y.1.ell 0, List.replicate y.1.ell 0)),
        ([], .call false 2), runCtl), []))
      encStepInT encStepOut stepBudget := by
  have hlt := budget_comp_lin natLt linear_succ (budget_prod hN₂ n₁_inSpace.tidy)
  have hmod := budget_comp_lin natMod (linear_mul _) (budget_prod n₁_inSpace.tidy hN₂)
  have hz := budget_comp_linear natIsZero hmod
  have hzeros : ComputableTidilyInSpace (fun y : Tuple × Bool =>
      ((List.replicate y.1.ell 0, List.replicate y.1.ell 0, List.replicate y.1.ell 0) : Regs))
      encStepInT encRegs stepBudget :=
    budget_prod hReplicate (budget_prod hReplicate hReplicate)
  have hfound : ComputableTidilyInSpace (fun y : Tuple × Bool =>
      ((((y.1.ell, y.1.height, y.1.n₁),
        (List.replicate y.1.ell 0, List.replicate y.1.ell 0, List.replicate y.1.ell 0)),
        ([], Mode.call false 2), runCtl) : Tuple)) encStepInT encTuple stepBudget :=
    mkTuple_inSpace ell_inSpace.tidy height_inSpace.tidy n₁_inSpace.tidy hzeros
      (budget_const (encB := encList encFrame) [] len_le_stepBudget)
      (budget_const (encB := encMode) (.call false 2) len_le_stepBudget)
      (mkCtl_inSpace (hConstTag 3) (hConstNat 0) (hConstNat 0) hNil)
  refine (budget_ite hlt (budget_ite hz
    (out_inSpace
      (withCtl_inSpace
        (mkCtl_inSpace (hConstTag 2) (succ_inSpace n₁_inSpace).tidy (hConstNat 2) hNil)))
    (out_inSpace
      (withCtl_inSpace
        (mkCtl_inSpace (hConstTag 2) n₁_inSpace.tidy (succ_inSpace (.of_tidy hN₂)).tidy hNil))))
    (out_inSpace hfound)).of_enc_eq fun y => ?_
  simp only [decide_eq_true_eq]

private theorem hLt {a b : Tuple × Bool → ℕ}
    (ha : ComputableTidilyInSpace a encStepInT encNat stepBudget)
    (hb : ComputableTidilyInSpace b encStepInT encNat stepBudget) :
    ComputableTidilyInSpace (fun y => decide (a y < b y)) encStepInT encBool stepBudget :=
  budget_comp_lin natLt linear_succ (budget_prod ha hb)

private theorem hSgnVal {p : Tuple × Bool → ℕ} {neg : Tuple × Bool → Bool}
    (hp : ComputableTidilyInSpace p encStepInT encNat stepBudget)
    (hneg : ComputableTidilyInSpace neg encStepInT encBool stepBudget) :
    ComputableTidilyInSpace (fun y => sgnVal (p y) (neg y)) encStepInT encNat stepBudget :=
  (budget_ite hneg (budget_comp_lin natPred linear_succ hp) (hConstNat 1))
    |>.of_enc_eq fun y => by simp only [sgnVal]

private theorem withRegsModeCtl_inSpace {R : Tuple × Bool → Regs} {st : Tuple × Bool → List Frame}
    {m : Tuple × Bool → Mode} {c : Tuple × Bool → Fin 7 × ℕ × ℕ × List ℕ}
    (hR : ComputableTidilyInSpace R encStepInT encRegs stepBudget)
    (hst : ComputableTidilyInSpace st encStepInT (encList encFrame) stepBudget)
    (hm : ComputableTidilyInSpace m encStepInT encMode stepBudget)
    (hc : ComputableTidilyInSpace c encStepInT encCtlTuple stepBudget) :
    ComputableTidilyInSpace (fun y => y.1.with (R y) (st y) (m y) (c y)) encStepInT encTuple
      stepBudget :=
  mkTuple_inSpace ell_inSpace.tidy height_inSpace.tidy hP hR hst hm hc

/-- Reading a leaf. -/
private theorem branch4_inSpace :
    ComputableTidilyInSpace (fun y : Tuple × Bool =>
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
  have hc := (budget_ite hBit (hSgnVal hP hneg) (hConstNat 0))
  have hmod :=
    (modifyAt_inSpace (get_inSpace (.of_tidy hRegs) (.of_tidy ht)) n₁_inSpace (.of_tidy hP)
    (.of_tidy hc)).tidy
  have hset := (set_inSpace (.of_tidy hRegs) (.of_tidy ht) (.of_tidy hmod)).tidy
  refine (budget_ite hcall (budget_ite (hLt n₁_inSpace.tidy ell_inSpace.tidy)
    (out_inSpace (withRegsModeCtl_inSpace hset stack_inSpace.tidy hMode
      (mkCtl_inSpace (hConstTag 4) (succ_inSpace n₁_inSpace).tidy (hConstNat 0) hNil)))
    (out_inSpace (withRegsModeCtl_inSpace hRegs stack_inSpace.tidy
      (budget_const (encB := encMode) .ret len_le_stepBudget)
      (mkCtl_inSpace (hConstTag 3) (hConstNat 0) (hConstNat 0) hNil))))
    (out_inSpace hTup)).of_enc_eq fun y => ?_
  simp only [decide_eq_true_eq]

private theorem hFrTarget : ComputableTidilyInSpace
    (fun y : Tuple × Bool => (y.1.stack.headD dfr).target)
    encStepInT encReg stepBudget :=
  hTopFinite (fun g => g.2.2)

private theorem hFrNeg : ComputableTidilyInSpace (fun y : Tuple × Bool => (y.1.stack.headD dfr).neg)
    encStepInT encBool stepBudget :=
  hTopFinite (fun g => g.2.1)

private theorem hRegPlus (k : Fin 3) :
    ComputableTidilyInSpace (fun y : Tuple × Bool => (y.1.stack.headD dfr).target + k)
      encStepInT encReg stepBudget :=
  hTopFinite (fun g => g.2.2 + k)

/-- The top frame with a new phase. -/
private theorem hFrPhase (ph : Fin 4) :
    ComputableTidilyInSpace (fun y : Tuple × Bool => { y.1.stack.headD dfr with phase := ph })
      encStepInT encFrame stepBudget :=
  (mkFrame_inSpace hRound (hTopFinite (encB := encFinEnum (Fin 4 × Bool × Fin 3))
    fun g => (ph, g.2.1, g.2.2))).of_enc_eq fun _ => rfl

/-- The pass over the table of the gate of the top frame. -/
private theorem branch5_inSpace :
    ComputableTidilyInSpace (fun y : Tuple × Bool =>
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
  have hempty := budget_comp_linear
    (of_inO (.of_linear (ListEncoding.isEmpty (enc₁ := encFrame) (enc := encList encFrame))))
      stack_inSpace.tidy
  have hG := budget_comp tableLength_inSpace.tidy ell_inSpace.tidy
    (.const_mul 4096 (ell_le_stepBudget.add
    (.const 1 _)))
  have hdm := budget_comp_lin natDivMod (linear_mul _)
    (budget_prod n₁_inSpace.tidy ell_inSpace.tidy)
  have hk := fst' hdm
  have hi := snd' hdm
  have hx := (get_inSpace (.of_tidy hRegs) (.of_tidy (hRegPlus 1))).tidy
  have hy := (get_inSpace (.of_tidy hRegs) (.of_tidy (hRegPlus 2))).tidy
  have hw := budget_comp weight_inSpace.tidy
    (budget_prod (budget_prod hP (budget_prod ell_inSpace.tidy hk))
    (budget_prod hx hy)) (.const_mul 64 (((length_le (budget_prod (budget_prod hP
      (budget_prod ell_inSpace.tidy hk)) (budget_prod hx hy))).add ell_le_stepBudget).add
        (.const 1 _)))
  have hacc' := (modifyAt_inSpace (.of_tidy hAcc) (.of_tidy hi) (.of_tidy hP) (.of_tidy hw)).tidy
  have hB : (fun y : Tuple × Bool => (y.1.regs.get (y.1.stack.headD dfr).target).length *
      ((encNat y.1.p).length + 1)) ≼ stepBudget :=
    mul_le_stepBudget (fun y => by
      have := length_get_le_regLen y.1 (y.1.stack.headD dfr).target
      omega) fun y => by omega
  have hsub :=
    (subtractSums_inSpace (.of_tidy hP) (.of_tidy (hSgnVal hP hFrNeg)) (.of_tidy hFrTarget)
    (.of_tidy hAcc) (.of_tidy hRegs) hB).tidy
  refine (budget_ite hempty (out_inSpace hTup) (budget_ite (hLt n₁_inSpace.tidy hG)
    (budget_ite hBit
      (out_inSpace
        (withCtl_inSpace
          (mkCtl_inSpace (hConstTag 5) (succ_inSpace n₁_inSpace).tidy (hConstNat 0) hacc')))
      (out_inSpace
        (withCtl_inSpace
          (mkCtl_inSpace (hConstTag 5) (succ_inSpace n₁_inSpace).tidy (hConstNat 0) hAcc))))
    (out_inSpace (withRegsModeCtl_inSpace hsub (cons_inSpace (hFrPhase 2) rest_inSpace.tidy)
      (hTopFinite (encB := encMode) fun g => .call true (g.2.2 + 1))
      (mkCtl_inSpace (hConstTag 3) (hConstNat 0) (hConstNat 0) hNil))))).of_enc_eq fun y => ?_
  simp only [decide_eq_true_eq]
  rfl

private theorem length_get_scale (R : Regs) (p : ℕ) (r r' : Fin 3) (a : ℕ) :
    ((R.scale p r a).get r').length = (R.get r').length := by
  fin_cases r <;> fin_cases r' <;> simp [Regs.scale, Regs.set, Regs.get]

private theorem length_unitInv_le (p j : ℕ) : (encNat (unitInv p j)).length ≤
    (encNat p).length + 2 := by
  have h₁ := ComputableTidilyInO.length_encNat_mono (powMod_le (p := p) (a := j + 1)
    (k := p - 2) le_rfl)
  have h₂ := length_encNat_add_le_add p 1
  have : (encNat 1).length = 1 := rfl
  rw [unitInv]; omega

/-- A register scaled by a residue no longer than the prime and the round of the top frame. -/
private theorem scaleT_inSpace {R : Tuple × Bool → Regs} {r : Tuple × Bool → Fin 3}
    {a : Tuple × Bool → ℕ}
    (hR : ComputableTidilyInSpace R encStepInT encRegs stepBudget)
    (hr : ComputableTidilyInSpace r encStepInT encReg stepBudget)
    (ha : ComputableTidilyInSpace a encStepInT encNat stepBudget)
    (hlen : ∀ y r', ((R y).get r').length = (y.1.regs.get r').length)
    (hasz : ∀ y, (encNat (a y)).length ≤
      (encNat y.1.p).length + (encNat (y.1.stack.headD dfr).round).length + 3) :
    ComputableTidilyInSpace (fun y => (R y).scale y.1.p (r y) (a y)) encStepInT encRegs
      stepBudget :=
  (scale_inSpace (.of_tidy hP) (.of_tidy ha) (.of_tidy hR) (.of_tidy hr) len_le_stepBudget
    (mul_le_stepBudget
      (fun y => by rw [hlen]; have := length_get_le_regLen y.1 (r y); omega)
      fun y => by have := hasz y; omega)).tidy

private theorem hFrame0 : ComputableTidilyInSpace (fun y : Tuple × Bool =>
    (⟨0, 0, y.1.mode.neg, y.1.mode.target⟩ : Frame)) encStepInT encFrame stepBudget :=
  (mkFrame_inSpace (hConstNat 0) (hModeFinite (encB := encFinEnum (Fin 4 × Bool × Fin 3))
    fun m => (0, m.neg, m.target))).of_enc_eq fun _ => rfl

private theorem hFrameNext : ComputableTidilyInSpace (fun y : Tuple × Bool =>
    (⟨(y.1.stack.headD dfr).round + 1, 0, (y.1.stack.headD dfr).neg,
      (y.1.stack.headD dfr).target⟩ : Frame)) encStepInT encFrame stepBudget :=
  (mkFrame_inSpace (succ_inSpace (.of_tidy hRound)).tidy
    (hTopFinite (encB := encFinEnum (Fin 4 × Bool × Fin 3))
    fun g => (0, g.2.1, g.2.2))).of_enc_eq fun _ => rfl

private theorem hRun : ComputableTidilyInSpace
    (fun _ : Tuple × Bool => runCtl) encStepInT encCtlTuple
    stepBudget := mkCtl_inSpace (hConstTag 3) (hConstNat 0) (hConstNat 0) hNil

/-- The steps of the iterative procedure. -/
private theorem branch3_inSpace :
    ComputableTidilyInSpace (fun y : Tuple × Bool => runStepT y.1) encStepInT encStepOut
      stepBudget := by
  have ht := hModeFinite (encB := encReg) Mode.target
  have hcall := hModeFinite (encB := encBool) Mode.isCall
  have hlenEq := budget_comp_linear natEq (budget_prod (budget_comp length stack_inSpace.tidy
    (.const_mul 8 ((length_le stack_inSpace.tidy).add (.const 1 _)))) height_inSpace.tidy)
  have hempty := budget_comp_linear
    (of_inO (.of_linear (ListEncoding.isEmpty (enc₁ := encFrame) (enc := encList encFrame))))
      stack_inSpace.tidy
  have hph (k : Fin 4) := hTopFinite (encB := encBool) fun g => decide (g.1 = k)
  have hR0 := scaleT_inSpace hRegs (hModeFinite (encB := encReg) fun m => m.target + 1)
    (hConstNat (unitVal 0)) (fun _ _ => rfl) fun y => by
      have : (encNat (unitVal 0)).length = 1 := rfl
      omega
  have hRj := scaleT_inSpace hRegs (hRegPlus 2) (succ_inSpace (.of_tidy hRound)).tidy
    (fun _ _ => rfl)
    fun y => by
    have := length_encNat_add_le_add (y.1.stack.headD dfr).round 1
    have : (encNat 1).length = 1 := rfl
    omega
  have hinv := budget_comp_linear unitInv_inSpace.tidy (budget_prod hP hRound)
  have hR2 := scaleT_inSpace hRegs (hRegPlus 1) hinv (fun _ _ => rfl) fun y => by
    have := length_unitInv_le y.1.p (y.1.stack.headD dfr).round; dsimp only; omega
  have hR3 := scaleT_inSpace hRegs (hRegPlus 2) hinv (fun _ _ => rfl) fun y => by
    have := length_unitInv_le y.1.p (y.1.stack.headD dfr).round; dsimp only; omega
  have hR3' := scaleT_inSpace hR3 (hRegPlus 1) (succ_inSpace (succ_inSpace (.of_tidy hRound))).tidy
    (fun y r' => length_get_scale _ _ _ _ _) fun y => by
      have := length_encNat_add_le_add (y.1.stack.headD dfr).round 2
      have : (encNat 2).length = 2 := rfl
      rw [show (y.1.stack.headD dfr).round + 1 + 1 = (y.1.stack.headD dfr).round + 2 by omega]
      omega
  have hout := budget_comp mapEqOne_inSpace.tidy
    (get_inSpace (.of_tidy hRegs) (.of_tidy (budget_const 2 len_le_stepBudget))).tidy
    (.const_mul 64
      ((length_le
      (get_inSpace (.of_tidy hRegs) (.of_tidy (budget_const 2 len_le_stepBudget))).tidy).add
      (.const 1 _)))
  have hnext := hLt (succ_inSpace (.of_tidy hRound)).tidy (budget_comp_lin natPred linear_succ hP)
  refine (budget_ite hcall
    (budget_ite hlenEq
      (out_inSpace (withCtl_inSpace (mkCtl_inSpace (hConstTag 4) (hConstNat 0) (hConstNat 0) hNil)))
      (out_inSpace (withRegsModeCtl_inSpace hR0 (cons_inSpace hFrame0 stack_inSpace.tidy)
        (hModeFinite (encB := encMode) fun m => .call false (m.target + 1)) hRun)))
    (budget_ite hempty
      (budget_prod (withCtl_inSpace (mkCtl_inSpace (hConstTag 6) (hConstNat 0) (hConstNat 0) hNil))
        hout)
      (budget_ite (hph 0)
        (out_inSpace (withRegsModeCtl_inSpace hRj (cons_inSpace (hFrPhase 1) rest_inSpace.tidy)
          (hTopFinite (encB := encMode) fun g => .call false (g.2.2 + 2)) hRun))
        (budget_ite (hph 1)
          (out_inSpace (withCtl_inSpace (mkCtl_inSpace (hConstTag 5) (hConstNat 0) (hConstNat 0)
            hReplicate)))
          (budget_ite (hph 2)
            (out_inSpace (withRegsModeCtl_inSpace hR2 (cons_inSpace (hFrPhase 3) rest_inSpace.tidy)
              (hTopFinite (encB := encMode) fun g => .call true (g.2.2 + 2)) hRun))
            (budget_ite hnext
              (out_inSpace (withRegsModeCtl_inSpace hR3' (cons_inSpace hFrameNext rest_inSpace.tidy)
                (hTopFinite (encB := encMode) fun g => .call false (g.2.2 + 1)) hRun))
              (out_inSpace (withRegsModeCtl_inSpace hR3 rest_inSpace.tidy
                (budget_const (encB := encMode) .ret len_le_stepBudget) hRun)))))))).of_enc_eq
    fun y => ?_
  simp only [runStepT, decide_eq_true_eq]
  rfl

end Branches

/-- **The step within its space budget.** -/
theorem stepT_inSpace : ComputableInSpace stepT encStepInT encStepOut stepBudget := by
  refine .of_tidy ?_
  have ht (k : Fin 7) :=
    budget_finite (encC := encBool) (fun t : Fin 7 => decide (t = k)) tag_inSpace.tidy
  refine (budget_ite (ht 0) branch0_inSpace (budget_ite (ht 1) branch1_inSpace
    (budget_ite (ht 2) branch2_inSpace (budget_ite (ht 3) branch3_inSpace
      (budget_ite (ht 4) branch4_inSpace (budget_ite (ht 5) branch5_inSpace
        (out_inSpace hTup))))))).of_enc_eq fun y => ?_
  simp only [stepT, decide_eq_true_eq]

end Reader

end Cslib.TreeEval
