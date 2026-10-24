/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.USTCON.Reader.Encode
public import Complexity.Computability.Machines.ReadMachine.Tidy
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# The read machine for undirected connectivity within linear work space

The halting test, the address and the step of `Cslib.USTCON.Reader.machine` are tidily computable
within work space linear in the length of the encoded state (and the bit read): every step is a
bounded number of operations on the numbers and the heads of the lists of the state — comparisons,
successors and predecessors, products for the address, divisions by the number of labels, and
functions of the finitely many controls, labels and frames. So the step machine simulating the read
machine is tidy within space linear in its states and the position of its head
(`Cslib.USTCON.Reader.tidy_machine`).

## Main definitions

* `Cslib.USTCON.Reader.encStepIn`, `Cslib.USTCON.Reader.stepBudget`: the encoded inputs of a step
  and their length.

## Main results

* `Cslib.USTCON.Reader.halt_inSpace`, `Cslib.USTCON.Reader.addr_inSpace`,
  `Cslib.USTCON.Reader.step_inSpace`: the components of the machine within linear space.
* `Cslib.USTCON.Reader.tidy_machine`: the simulating step machine is tidy.
-/

@[expose] public section

namespace Cslib.USTCON.Reader

open Turing MultiTapeTM ComputableTidilyInSpace Cslib.RotationMap Cslib.Reachability.Reingold

/-- The encoding of the inputs of a step: the tuple and the bit read. -/
abbrev encStepIn : Tuple × Bool ↪ List Bool :=
  encPair encTuple encBool

/-- **The space budget of a step**: the length of the encoded tuple and bit. -/
def stepBudget (y : Tuple × Bool) : ℕ :=
  (encStepIn y).length

private theorem len_le_stepBudget : (fun y => (encStepIn y).length) ≼ stepBudget :=
  .refl _

/-! ### Projections -/

section Proj

private theorem hTup : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1) encStepIn encTuple
    stepBudget :=
  fst _ _

private theorem hBit : ComputableTidilyInSpace (fun y : Tuple × Bool => y.2) encStepIn encBool
    stepBudget :=
  snd _ _

private theorem hCtl : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.1.1) encStepIn encCtl
    stepBudget :=
  fst' (fst' hTup)

private theorem hCnt : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.1.2) encStepIn encNat
    stepBudget :=
  snd' (fst' hTup)

private theorem hN : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.1.1) encStepIn encNat
    stepBudget :=
  fst' (fst' (fst' (snd' hTup)))

private theorem hS :
    ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.1.2.1) encStepIn encNat stepBudget :=
  fst' (snd' (fst' (fst' (snd' hTup))))

private theorem hT :
    ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.1.2.2) encStepIn encNat stepBudget :=
  snd' (snd' (fst' (fst' (snd' hTup))))

private theorem hDepth :
    ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.2.1) encStepIn encNat stepBudget :=
  fst' (snd' (fst' (snd' hTup)))

private theorem hLen :
    ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.1.2.2) encStepIn encNat stepBudget :=
  snd' (snd' (fst' (snd' hTup)))

private theorem hC : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.1.1) encStepIn encNat
    stepBudget :=
  fst' (fst' (snd' (snd' hTup)))

private theorem hW :
    ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.1.2.1) encStepIn encNat stepBudget :=
  fst' (snd' (fst' (snd' (snd' hTup))))

private theorem hJ :
    ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.1.2.2) encStepIn encNat stepBudget :=
  snd' (snd' (fst' (snd' (snd' hTup))))

private theorem hV₁ :
    ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.1.1) encStepIn encNat stepBudget :=
  fst' (fst' (snd' (snd' (snd' hTup))))

private theorem hV₂ :
    ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.1.2) encStepIn encNat stepBudget :=
  snd' (fst' (snd' (snd' (snd' hTup))))

private theorem hLower : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.2.1) encStepIn
    (encList encLab) stepBudget :=
  fst' (snd' (snd' (snd' (snd' hTup))))

private theorem hFrames : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.2.2) encStepIn
    (encList encFrame) stepBudget :=
  snd' (snd' (snd' (snd' (snd' hTup))))

end Proj

/-! ### Building tuples and lists within the budget -/

section Build

variable {β : Type} {encIn : β ↪ List Bool} {Bs : β → ℕ}

/-- A tuple from its components. -/
private theorem mkT {ctl : β → Ctl} {cnt n s t d l c w j v₁ v₂ : β → ℕ} {low : β → List Label}
    {fr : β → List (ReingoldPc × Label)}
    (h₁ : ComputableTidilyInSpace ctl encIn encCtl Bs)
    (h₂ : ComputableTidilyInSpace cnt encIn encNat Bs)
    (h₃ : ComputableTidilyInSpace n encIn encNat Bs)
    (h₄ : ComputableTidilyInSpace s encIn encNat Bs)
    (h₅ : ComputableTidilyInSpace t encIn encNat Bs)
    (h₆ : ComputableTidilyInSpace d encIn encNat Bs)
    (h₇ : ComputableTidilyInSpace l encIn encNat Bs)
    (h₈ : ComputableTidilyInSpace c encIn encNat Bs)
    (h₉ : ComputableTidilyInSpace w encIn encNat Bs)
    (h₁₀ : ComputableTidilyInSpace j encIn encNat Bs)
    (h₁₁ : ComputableTidilyInSpace v₁ encIn encNat Bs)
    (h₁₂ : ComputableTidilyInSpace v₂ encIn encNat Bs)
    (h₁₃ : ComputableTidilyInSpace low encIn (encList encLab) Bs)
    (h₁₄ : ComputableTidilyInSpace fr encIn (encList encFrame) Bs) :
    ComputableTidilyInSpace (fun x => (((ctl x, cnt x), ((n x, s x, t x), (d x, l x)),
      ((c x, w x, j x), ((v₁ x, v₂ x), low x, fr x))) : Tuple)) encIn encTuple Bs :=
  budget_prod (budget_prod h₁ h₂) (budget_prod (budget_prod (budget_prod h₃ (budget_prod h₄ h₅))
    (budget_prod h₆ h₇)) (budget_prod (budget_prod h₈ (budget_prod h₉ h₁₀))
      (budget_prod (budget_prod h₁₁ h₁₂) (budget_prod h₁₃ h₁₄))))

end Build

/-! ### The halting test and the address -/

/-- A function of the control. -/
private theorem hCtlFinite {β : Type} {encB : β ↪ List Bool} (g : Ctl → β) :
    ComputableTidilyInSpace (fun y : Tuple × Bool => g y.1.1.1) encStepIn encB stepBudget :=
  budget_finite g hCtl

/-- The halting test on tuples. -/
private theorem haltT_inSpace :
    ComputableTidilyInSpace (fun x : Tuple => decide (x.1.1 = .done)) encTuple encBool
      fun x => stepBudget (x, false) :=
  ReadMachine.comp_pairFalse_inSpace (fun _ => le_rfl) (hCtlFinite fun k ↦ decide (k = .done))

/-- Whether the next step of the evaluation is a step of the slot graph, from the labels and the
frames. -/
private def atRootT (low : List Label) (fr : List (ReingoldPc × Label)) : Bool :=
  !low.isEmpty && low.tail.isEmpty && !fr.isEmpty &&
    (fun p : ReingoldPc × Label ↦ decide (p.1 = .call₀) || decide (p.1 = .call₁))
      (fr.headD (.zig₀, 0))

private theorem atRootT_eq (v : ℕ × ℕ) (low : List Label) (fr : List (ReingoldPc × Label)) :
    atRootT low fr = (⟨v, low, fr⟩ : ReingoldEvalState (ℕ × ℕ) Label).atRoot := by
  rcases low with _ | ⟨b, _ | ⟨b', l⟩⟩ <;> rcases fr with _ | ⟨⟨pc, a⟩, rest⟩ <;>
    try rfl
  cases pc <;> rfl

/-- Whether the next step of the evaluation is a step of the slot graph, within the budget. -/
private theorem atRootT_inSpace : ComputableTidilyInSpace
    (fun y : Tuple × Bool ↦ atRootT y.1.2.2.2.2.1 y.1.2.2.2.2.2) encStepIn encBool stepBudget := by
  have h₄ := budget_finite (encC := encBool)
    (fun p : ReingoldPc × Label ↦ decide (p.1 = .call₀) || decide (p.1 = .call₁))
    (budget_headD (ReingoldPc.zig₀, (0 : Label)) hFrames)
  exact budget_finite (encC := encBool)
    (fun q : Bool × Bool × Bool × Bool ↦ !q.1 && q.2.1 && !q.2.2.1 && q.2.2.2)
    (budget_prod (budget_isEmpty hLower) (budget_prod (budget_isEmpty (budget_tail hLower))
      (budget_prod (budget_isEmpty hFrames) h₄)))

/-- The address on tuples. -/
private theorem addrT_inSpace :
    ComputableTidilyInSpace (fun x : Tuple ↦ addr (State.ofTuple x)) encTuple (encOption encNat)
      fun x => stepBudget (x, false) := by
  have hc (k : Ctl) := hCtlFinite (encB := encBool) fun k' ↦ decide (k' = k)
  have hbase := atRootT_inSpace
  have none' := budget_const (encB := encOption encNat) (encIn := encStepIn) (Bs := stepBudget)
    none (.refl _)
  have hhdr := budget_natAdd (budget_natAdd (budget_natAdd hN hS) hT) (budget_const 3 (.refl _))
  have h := budget_ite (hc .hdrN) (budget_optionSome hCnt) (budget_ite (hc .hdrS)
    (budget_optionSome (budget_natAdd (budget_natSucc hN) hCnt)) (budget_ite (hc .hdrT)
      (budget_optionSome
        (budget_natAdd (budget_natSucc (budget_natAdd (budget_natSucc hN) hS)) hCnt))
      (budget_ite (hc .eval)
        (budget_ite hbase
          (budget_optionSome (budget_natAdd hhdr (budget_natAdd (budget_natMul hV₁ hN) hV₂)))
          none')
        none')))
  refine (ReadMachine.comp_pairFalse_inSpace (fun _ => le_rfl) h).of_enc_eq fun x ↦ ?_
  obtain ⟨⟨ctl, cnt⟩, ⟨⟨n, s, t⟩, d, l⟩, ⟨c, w, j⟩, v, low, fr⟩ := x
  cases ctl
  case eval => simp only [addr, State.ofTuple, atRootT_eq v]; rfl
  all_goals simp [addr, State.ofTuple]

/-! ### The label of a digit, by a finite-state fold over the binary digits -/

instance : NeZero numLabels :=
  ⟨numLabels_pos.ne'⟩

/-- A step of computing a number modulo the number of labels from its binary digits, least
significant first: the residue so far and the residue of the next place value. -/
private def modStep (p : ZMod numLabels × ZMod numLabels) (b : Bool) :
    ZMod numLabels × ZMod numLabels :=
  (p.1 + (if b then p.2 else 0), 2 * p.2)

private theorem foldl_modStep (w : ℕ) :
    ∀ r q : ZMod numLabels, (w.bits.foldl modStep (r, q)).1 = r + q * w := by
  induction w using Nat.binaryRec' with
  | zero => intro r q; simp [Nat.zero_bits]
  | bit b w hb ih =>
    intro r q
    rw [Nat.bits_append_bit w b hb, List.foldl_cons, modStep, ih, Nat.bit_val]
    cases b
    · simp only [Bool.false_eq_true, ite_false, add_zero, Bool.toNat_false]
      push_cast
      ring
    · simp only [ite_true, Bool.toNat_true]
      push_cast
      ring

/-- The label of a residue. -/
private def labelOfZMod (z : ZMod numLabels) : Label :=
  labelEquiv ⟨z.val, ZMod.val_lt z⟩

/-- The label of a digit is the label of the residue computed by the fold. -/
private theorem labelOfNat_eq (w : ℕ) :
    labelOfNat w = labelOfZMod (w.bits.foldl modStep (0, 1)).1 := by
  rw [foldl_modStep, zero_add, one_mul, labelOfZMod, labelOfNat]
  congr 2

/-- **The label of a digit** is computed by a finite-state fold over the binary digits of `w`,
within work space linear in their number. -/
private theorem labelOfNat_inSpace :
    ComputableTidilyInSpace labelOfNat encNat encLab fun w => (encNat w).length := by
  have hfold := of_inO (ComputableTidilyInO.foldl_bits_finite
    (encFinEnum (ZMod numLabels × ZMod numLabels)) modStep (0, 1))
  have h := hfold.of_encIn_eq (α' := ℕ) (encIn' := encNat) Nat.bits fun w ↦ by
    rw [encNat_apply, encBits_apply]
  have h' := budget_comp_linear (of_finite (encIn := encFinEnum (ZMod numLabels × ZMod numLabels))
    (encB := encLab) fun p : ZMod numLabels × ZMod numLabels ↦ labelOfZMod p.1) h
  exact (h'.weaken (.const 0 _)).of_enc_eq fun w ↦ by rw [labelOfNat_eq]

/-! ### The step of the evaluation -/

/-- The next program counter of a frame. -/
private def nextPc : ReingoldPc → ReingoldPc
  | .zig₀ => .call₀
  | .call₀ => .zag₀
  | .zag₀ => .zig₁
  | .zig₁ => .call₁
  | .call₁ => .zag₁
  | .zag₁ => .finish
  | .finish => .finish

/-- Whether a program counter is a step of `H`. -/
private def isHStep : ReingoldPc → Bool
  | .zig₀ | .zag₀ | .zig₁ | .zag₁ => true
  | _ => false

/-- Whether a program counter is a rotation of the level below. -/
private def isCall : ReingoldPc → Bool
  | .call₀ | .call₁ => true
  | _ => false

/-- **The step of the evaluation, from the heads of the lists**: a step of `H` on the head label and
the label of the top frame, a rotation of the level below, as a step of the slot graph at level `1`
or a push, or the final permutation and a pop. -/
private def evalStepT (n : ℕ) (bit : Bool) (v : ℕ × ℕ) (low : List Label)
    (fr : List (ReingoldPc × Label)) : (ℕ × ℕ) × List Label × List (ReingoldPc × Label) :=
  if low.isEmpty || fr.isEmpty then (v, low, fr)
  else if isHStep (fr.headD (.zig₀, 0)).1 then
    ((v, (reingoldHStep base baseEquiv (fr.headD (.zig₀, 0)).1
        (low.headD 0, (fr.headD (.zig₀, 0)).2)).1 :: low.tail,
      (nextPc (fr.headD (.zig₀, 0)).1, (reingoldHStep base baseEquiv (fr.headD (.zig₀, 0)).1
        (low.headD 0, (fr.headD (.zig₀, 0)).2)).2) :: fr.tail))
  else if isCall (fr.headD (.zig₀, 0)).1 then
    if low.tail.isEmpty then
      ((slotRotN n v (low.headD 0) bit).1, (slotRotN n v (low.headD 0) bit).2 :: low.tail,
        (nextPc (fr.headD (.zig₀, 0)).1, (fr.headD (.zig₀, 0)).2) :: fr.tail)
    else
      (v, low.tail, (.zig₀, low.headD 0) ::
        (nextPc (fr.headD (.zig₀, 0)).1, (fr.headD (.zig₀, 0)).2) :: fr.tail)
  else (v, reingoldFinish baseEquiv (fr.headD (.zig₀, 0)).2 :: low, fr.tail)

private theorem evalStepT_eq (n : ℕ) (bit : Bool) (s : ReingoldEvalState (ℕ × ℕ) Label) :
    evalStepT n bit s.vertex s.lower s.frames =
      ((reingoldEvalStep base baseEquiv (slotRot n bit) s).vertex,
        (reingoldEvalStep base baseEquiv (slotRot n bit) s).lower,
        (reingoldEvalStep base baseEquiv (slotRot n bit) s).frames) := by
  obtain ⟨v, _ | ⟨b, l⟩, _ | ⟨⟨pc, a⟩, rest⟩⟩ := s
  all_goals try rfl
  cases pc <;> by_cases hl : l = [] <;> simp [evalStepT, reingoldEvalStep, isHStep, isCall, nextPc,
    slotRot, hl]

private theorem hVert : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.1) encStepIn
    (encPair encNat encNat) stepBudget :=
  fst' (snd' (snd' (snd' hTup)))

/-- The head label below the frames. -/
private theorem hHeadLab : ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.2.1.headD 0)
    encStepIn encLab stepBudget :=
  budget_headD 0 hLower

/-- The top frame. -/
private theorem hTop :
    ComputableTidilyInSpace (fun y : Tuple × Bool => y.1.2.2.2.2.2.headD (.zig₀, 0))
      encStepIn encFrame stepBudget :=
  budget_headD _ hFrames

/-- **The step of the slot graph** on the slot, the head label and the bit read. -/
private theorem slotRotN_inSpace : ComputableTidilyInSpace
    (fun y : Tuple × Bool => slotRotN y.1.2.1.1.1 y.1.2.2.2.1 (y.1.2.2.2.2.1.headD 0) y.2)
    encStepIn (encPair (encPair encNat encNat) encLab) stepBudget := by
  have ht (d : SlotLabel) := budget_finite (encC := encBool)
    (fun b : Label ↦ decide (b = slotLabel d)) hHeadLab
  have hc (d : SlotLabel) := budget_const (encB := encLab) (encIn := encStepIn) (Bs := stepBudget)
    (slotLabel d) (.refl _)
  have h := budget_ite (ht (.inl ()))
    (budget_prod (budget_ite hBit (budget_prod hV₂ hV₁) hVert) hHeadLab)
    (budget_ite (ht (.inr ((), (), false)))
      (budget_prod (budget_prod hV₁ (budget_ite (budget_natEq (budget_natSucc hV₂) hN)
        (budget_const (encB := encNat) 0 (.refl _)) (budget_natSucc hV₂)))
        (hc (.inr ((), (), true))))
      (budget_ite (ht (.inr ((), (), true)))
        (budget_prod
          (budget_prod hV₁
            (budget_ite (budget_natIsZero hV₂) (budget_natPred hN) (budget_natPred hV₂)))
          (hc (.inr ((), (), false))))
        (budget_prod hVert hHeadLab)))
  exact h.of_enc_eq fun y ↦ by simp only [slotRotN, decide_eq_true_eq]

/-- **The step of the evaluation** within the budget. -/
private theorem evalStepT_inSpace : ComputableTidilyInSpace
    (fun y : Tuple × Bool => evalStepT y.1.2.1.1.1 y.2 y.1.2.2.2.1 y.1.2.2.2.2.1 y.1.2.2.2.2.2)
    encStepIn encEval stepBudget := by
  have hl := budget_tail hLower
  have hrest := budget_tail hFrames
  have hH := budget_finite (encC := encPair encLab encLab)
    (fun p : (ReingoldPc × Label) × Label ↦ reingoldHStep base baseEquiv p.1.1 (p.2, p.1.2))
    (budget_prod hTop hHeadLab)
  have hnew := budget_finite (encC := encFrame)
    (fun p : (ReingoldPc × Label) × (Label × Label) ↦ (nextPc p.1.1, p.2.2)) (budget_prod hTop hH)
  have hnext := budget_finite (encC := encFrame)
    (fun p : ReingoldPc × Label ↦ (nextPc p.1, p.2)) hTop
  have hpush := budget_finite (encC := encFrame) (fun b : Label ↦ (ReingoldPc.zig₀, b)) hHeadLab
  have hfin := budget_finite (encC := encLab) (fun p : ReingoldPc × Label ↦
    reingoldFinish baseEquiv p.2) hTop
  have hempty := budget_finite (encC := encBool) (fun q : Bool × Bool ↦ q.1 || q.2)
    (budget_prod (budget_isEmpty hLower) (budget_isEmpty hFrames))
  have h := budget_ite hempty (budget_prod hVert (budget_prod hLower hFrames))
    (budget_ite (budget_finite (encC := encBool) (fun p : ReingoldPc × Label ↦ isHStep p.1) hTop)
      (budget_prod hVert (budget_prod (budget_cons (fst' hH) hl) (budget_cons hnew hrest)))
      (budget_ite (budget_finite (encC := encBool) (fun p : ReingoldPc × Label ↦ isCall p.1) hTop)
        (budget_ite (budget_isEmpty hl)
          (budget_prod (fst' slotRotN_inSpace)
            (budget_prod (budget_cons (snd' slotRotN_inSpace) hl) (budget_cons hnext hrest)))
          (budget_prod hVert (budget_prod hl (budget_cons hpush (budget_cons hnext hrest)))))
        (budget_prod hVert (budget_prod (budget_cons hfin hLower) hrest))))
  exact h.of_enc_eq fun y ↦ rfl

/-! ### The step -/

/-- The step on tuples. -/
private def stepT (y : Tuple × Bool) : Tuple × List Bool :=
  ((step (State.ofTuple y.1) y.2).1.toTuple, (step (State.ofTuple y.1) y.2).2)

/-- **The step on tuples** within the budget. -/
private theorem stepT_inSpace : ComputableTidilyInSpace stepT encStepIn (encPair encTuple encBits)
    stepBudget := by
  have hc (k : Ctl) := hCtlFinite (encB := encBool) fun k' ↦ decide (k' = k)
  have cctl (k : Ctl) := budget_const (encB := encCtl) (encIn := encStepIn) (Bs := stepBudget) k
    (.refl _)
  have cnat (a : ℕ) := budget_const (encB := encNat) (encIn := encStepIn) (Bs := stepBudget) a
    (.refl _)
  have nil := budget_const (encB := encBits) (encIn := encStepIn) (Bs := stepBudget) [] (.refl _)
  have T₁ := mkT hCtl (budget_natSucc hCnt) hN hS hT hDepth hLen hC hW hJ hV₁ hV₂ hLower hFrames
  have keep (k : Ctl) := mkT (cctl k) hCnt hN hS hT hDepth hLen hC hW hJ hV₁ hV₂ hLower hFrames
  have hdrN := budget_ite hBit (budget_prod T₁ nil) (budget_prod (mkT (cctl .hdrS) (cnat 0) hCnt
    hS hT hDepth hLen hC hW hJ hV₁ hV₂ hLower hFrames) nil)
  have hdrS := budget_ite hBit (budget_prod T₁ nil) (budget_prod (mkT (cctl .hdrT) (cnat 0) hN
    hCnt hT hDepth hLen hC hW hJ hV₁ hV₂ hLower hFrames) nil)
  have hdrT := budget_ite hBit (budget_prod T₁ nil) (budget_prod (mkT (cctl .size) hN hN hS hCnt
    (cnat 524) (cnat 136240) hC hW hJ hV₁ hV₂ hLower hFrames) nil)
  have size := budget_ite (budget_natIsZero hCnt)
    (budget_prod (mkT (cctl .start) hCnt hN hS hT hDepth hLen (cnat 0) hW hJ hV₁ hV₂ hLower
      hFrames) nil)
    (budget_prod (mkT hCtl (budget_natDiv hCnt (cnat 2)) hN hS hT (budget_natAdd hDepth (cnat 16))
      (budget_natAdd hLen (cnat 4168)) hC hW hJ hV₁ hV₂ hLower hFrames) nil)
  have start := budget_prod (mkT (cctl .fill) hCnt hN hS hT hDepth hLen hC hC hLen hS hS
    (budget_const (encB := encList encLab) [] (.refl _))
    (budget_const (encB := encList encFrame) [] (.refl _))) nil
  have fill := budget_ite (budget_natEq (budget_length hLower) hDepth)
    (budget_prod (keep .next) nil)
    (budget_prod (mkT hCtl hCnt hN hS hT hDepth hLen hC hW hJ hV₁ hV₂
      (budget_cons (budget_const (encB := encLab) (0 : Label) (.refl _)) hLower) hFrames) nil)
  have hlab := budget_comp_lin labelOfNat_inSpace (.refl _) hW
  have next := budget_ite (budget_natIsZero hJ) (budget_prod (keep .check) nil)
    (budget_prod (mkT (cctl .eval) hCnt hN hS hT hDepth hLen hC (budget_natDiv hW (cnat numLabels))
      (budget_natPred hJ) hV₁ hV₂ hLower (budget_cons (budget_finite (encC := encFrame)
        (fun l : Label ↦ (ReingoldPc.zig₀, l)) hlab)
        (budget_const (encB := encList encFrame) [] (.refl _)))) nil)
  have eval := budget_ite (budget_isEmpty hFrames)
    (budget_prod (mkT (cctl .next) hCnt hN hS hT hDepth hLen hC hW hJ hV₁ hV₂ (budget_tail hLower)
      hFrames) nil)
    (budget_prod (mkT hCtl hCnt hN hS hT hDepth hLen hC hW hJ
      (fst' (fst' evalStepT_inSpace)) (snd' (fst' evalStepT_inSpace))
      (fst' (snd' evalStepT_inSpace)) (snd' (snd' evalStepT_inSpace))) nil)
  have check := budget_ite (budget_finite (encC := encBool) not (budget_natIsZero hW))
    (budget_prod (keep .done) (budget_const (encB := encBits) [false] (.refl _)))
    (budget_ite (budget_natEq hV₁ hT)
      (budget_prod (keep .done) (budget_const (encB := encBits) [true] (.refl _)))
      (budget_prod (mkT (cctl .start) hCnt hN hS hT hDepth hLen (budget_natSucc hC) hW hJ hV₁ hV₂
        hLower hFrames) nil))
  have done := budget_prod hTup nil
  have h := budget_ite (hc .hdrN) hdrN (budget_ite (hc .hdrS) hdrS (budget_ite (hc .hdrT) hdrT
    (budget_ite (hc .size) size (budget_ite (hc .start) start (budget_ite (hc .fill) fill
      (budget_ite (hc .next) next (budget_ite (hc .eval) eval (budget_ite (hc .check) check
        done))))))))
  refine h.of_enc_eq fun y ↦ ?_
  obtain ⟨⟨⟨ctl, cnt⟩, ⟨⟨n, s, t⟩, d, l⟩, ⟨c, w, j⟩, v, low, fr⟩, b⟩ := y
  apply congrArg (encPair encTuple encBits)
  cases ctl
  case eval =>
    by_cases hfr : fr = []
    · simp [stepT, step, State.ofTuple, State.toTuple, hfr]
    · have he := evalStepT_eq n b ⟨v, low, fr⟩
      simp only at he
      simp [stepT, step, State.ofTuple, State.toTuple, hfr, he]
  case size => by_cases h : cnt = 0 <;> simp [stepT, step, State.ofTuple, State.toTuple, h]
  case fill => by_cases h : low.length = d <;> simp [stepT, step, State.ofTuple, State.toTuple, h]
  case next => by_cases h : j = 0 <;> simp [stepT, step, State.ofTuple, State.toTuple, h]
  case check =>
    obtain ⟨v₁, v₂⟩ := v
    by_cases hw : w = 0
    · by_cases hv : v₁ = t
      · subst hv
        simp [stepT, step, State.ofTuple, State.toTuple, hw]
      · simp [stepT, step, State.ofTuple, State.toTuple, hw, hv]
    · simp [stepT, step, State.ofTuple, State.toTuple, hw]
  all_goals cases b <;> simp [stepT, step, State.ofTuple, State.toTuple]

/-! ### On states -/

/-- **The space budget of a state**: the length of its encoded tuple with a bit. -/
def stateBudget (q : State) : ℕ :=
  stepBudget (q.toTuple, false)

private theorem stepBudget_bool (x : Tuple) (b : Bool) : stepBudget (x, b) = stepBudget
    (x, false) := by
  cases b <;> simp [stepBudget, encBool_apply]

/-- The halting test of `machine` is tidily computable within the space budget of the state. -/
theorem halt_inSpace : ComputableTidilyInSpace machine.halt encState encBool stateBudget :=
  (haltT_inSpace.of_encIn_eq State.toTuple fun _ ↦ rfl).of_enc_eq fun _ ↦ rfl

/-- The address of `machine` is tidily computable within the space budget of the state. -/
theorem addr_inSpace : ComputableTidilyInSpace machine.addr encState (encOption encNat)
    stateBudget :=
  (addrT_inSpace.of_encIn_eq State.toTuple fun _ ↦ rfl).of_enc_eq fun _ ↦ rfl

/-- The step of `machine`, on a state and the bit read, is tidily computable within the space
budget of the state. -/
theorem step_inSpace :
    ComputableTidilyInSpace (fun p : State × Bool => machine.step p.1 p.2)
      (encPair encState encBool) (encPair encState encBits) fun p => stateBudget p.1 := by
  have h := stepT_inSpace.of_encIn_eq (α' := State × Bool) (encIn' := encPair encState encBool)
    (fun p ↦ (p.1.toTuple, p.2)) fun _ ↦ rfl
  refine (h.mono_le fun p ↦ ?_).of_enc_eq fun _ ↦ rfl
  rw [stateBudget, stepBudget_bool]

/-- **The step machine simulating the read machine is tidy**, within the space of its states
together with the position of its head. -/
theorem tidy_machine : ∃ T, machine.toStepMachine.Tidy (encPair encState encNat)
    (ReadMachine.stateT encState T stateBudget) (ReadMachine.stateS encState stateBudget) := by
  obtain ⟨T₁, h₁⟩ := halt_inSpace
  obtain ⟨T₂, h₂⟩ := addr_inSpace
  obtain ⟨T₃, h₃⟩ := step_inSpace
  let T : State → ℕ := fun s => T₁ s + T₂ s + T₃ (s, false) + T₃ (s, true)
  exact ⟨T, ReadMachine.tidy_toStepMachine (h₁.mono_le (fun s => by simp only [T]; omega)
    fun _ => le_rfl) (h₂.mono_le (fun s => by simp only [T]; omega) fun _ => le_rfl)
    (h₃.mono_le (fun p => by rcases p with ⟨s, _ | _⟩ <;> simp only [T] <;> omega)
      fun _ => le_rfl)⟩

end Cslib.USTCON.Reader
