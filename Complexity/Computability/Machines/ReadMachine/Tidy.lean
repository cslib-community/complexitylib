/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.ReadMachine.StepMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.StepMachine

/-!
# Resource certificates for read-machine simulations

If the halting test, the address and the step of a read machine have plain charged resource
certificates, then the step of `Turing.ReadMachine.toStepMachine` has a resource certificate on
its states, which add the position of the head: the work space grows by the length of the position
in binary, and the time by a factor of the position, to compare it with the address.

## Main results

* `Turing.ReadMachine.pairFalse_inSpace`, `Turing.ReadMachine.comp_pairFalse_inSpace`: evaluating
  a function of a state and a bit at the bit `false` within the space budget of the step.
* `Turing.ReadMachine.toStepMachine_resourceCertificate`: the simulating step machine has a plain
  resource certificate.
-/

@[expose] public section

namespace Turing

namespace ReadMachine

open MultiTapeTM MultiTapeTM.ComputableInO

/-! ### Computing within fixed budgets -/

section Budget

variable {γ β δ : Type} {encIn : γ ↪ List Bool} {encB : β ↪ List Bool} {encD : δ ↪ List Bool}
  {Bt Bs : γ → ℕ}

/-- Composition within the budgets. -/
theorem budget_comp {f : γ → β} {g : β → δ} {Tg Sg : β → ℕ}
    (hg : ComputableInO g encB encD Tg Sg) (hf : ComputableInO f encIn encB Bt Bs)
    (hT : (fun x => Tg (f x)) ≼ Bt) (hS : (fun x => Sg (f x)) ≼ Bs) :
    ComputableInO (fun x => g (f x)) encIn encD Bt Bs :=
  (hg.comp hf).weaken (.add (.refl _) hT) (.add (.refl _) hS)

/-- Composition with a map computed in linear time and space, within the budgets. -/
theorem budget_comp_linear {f : γ → β} {g : β → δ}
    (hg : ComputableInO g encB encD (fun b => (encB b).length) fun b => (encB b).length)
    (hf : ComputableInO f encIn encB Bt Bs) (hst : Bs ≼ Bt) :
    ComputableInO (fun x => g (f x)) encIn encD Bt Bs :=
  budget_comp hg hf (BigOLe.trans hf.length_le hst) hf.length_le

/-- Pairs within the budgets. -/
theorem budget_prod {f : γ → β} {g : γ → δ} (hf : ComputableInO f encIn encB Bt Bs)
    (hg : ComputableInO g encIn encD Bt Bs) :
    ComputableInO (fun x => (f x, g x)) encIn (encPair encB encD) Bt Bs :=
  (hf.prod hg).weaken (.add (.refl _) (.refl _)) (.add (.refl _) (.refl _))

/-- Conditionals within the budgets. -/
theorem budget_ite {c : γ → Bool} {f g : γ → β}
    (hc : ComputableInO c encIn encBool Bt Bs) (hf : ComputableInO f encIn encB Bt Bs)
    (hg : ComputableInO g encIn encB Bt Bs) :
    ComputableInO (fun x => if c x then f x else g x) encIn encB Bt Bs :=
  (hc.ite hf hg).weaken (.add (.refl _) (.ite _ (.refl _) (.refl _)))
    (.add (.refl _) (.ite _ (.refl _) (.refl _)))

/-- A constant within the budgets. -/
theorem budget_const (b : β) (hl : (fun x => (encIn x).length) ≼ Bs) (hst : Bs ≼ Bt) :
    ComputableInO (fun _ : γ => b) encIn encB Bt Bs :=
  (const b).weaken (hl.trans hst) hl

/-- A function of finitely many values, within the budgets. -/
theorem budget_finite {f : γ → β} [Finite β] (g : β → δ)
    (hf : ComputableInO f encIn encB Bt Bs) (hst : Bs ≼ Bt) :
    ComputableInO (fun x => g (f x)) encIn encD Bt Bs :=
  budget_comp_linear (ComputableInDegree.of_finite g).inO_one hf hst

/-- Pairing a state with the bit `false`, within any space budget at least the encoded pair
length. -/
theorem pairFalse_inSpace {α : Type} {enc : α ↪ List Bool} {B : α × Bool → ℕ}
    (hB : ∀ x, (encPair enc encBool (x, false)).length ≤ B (x, false)) :
    ComputableTidilyInSpace (fun x : α => (x, false)) enc (encPair enc encBool)
      fun x => B (x, false) :=
  (ComputableTidilyInSpace.budget_prod
    (ComputableTidilyInSpace.of_inO (.of_linear (.of_eq (f := id) fun _ => rfl)))
    (ComputableTidilyInSpace.budget_const (encB := encBool) false (.refl _))).weaken
      (.of_le fun x => by
        have := hB x
        simp only [length_encPair] at this ⊢
        omega)

/-- Evaluating a function of a state and a bit at the bit `false`, within the space budget of the
step. -/
theorem comp_pairFalse_inSpace {α : Type} {enc : α ↪ List Bool} {B : α × Bool → ℕ}
    (hB : ∀ x, (encPair enc encBool (x, false)).length ≤ B (x, false)) {f : α × Bool → β}
    (h : ComputableTidilyInSpace f (encPair enc encBool) encB B) :
    ComputableTidilyInSpace (fun x : α => f (x, false)) enc encB fun x => B (x, false) :=
  ComputableTidilyInSpace.budget_comp h (pairFalse_inSpace hB) (.refl _)

end Budget

variable {σ : Type} {m : ReadMachine σ} {encS : σ ↪ List Bool} {T S : σ → ℕ}

/-- The input of a step of the simulating machine. -/
abbrev encStepIn (encS : σ ↪ List Bool) : (σ × ℕ) × Option Bool ↪ List Bool :=
  encPair (encPair encS encNat) (encOption encBool)

/-- The length of the input of a step. -/
abbrev inLen (encS : σ ↪ List Bool) (p : (σ × ℕ) × Option Bool) : ℕ := (encStepIn encS p).length

/-- The space budget of a step. -/
abbrev spaceB (encS : σ ↪ List Bool) (S : σ → ℕ) (p : (σ × ℕ) × Option Bool) : ℕ :=
  S p.1.1 + inLen encS p

/-- The time budget of a step. -/
abbrev timeB (encS : σ ↪ List Bool) (T S : σ → ℕ) (p : (σ × ℕ) × Option Bool) : ℕ :=
  (p.1.2 + 1) * (T p.1.1 + S p.1.1 + inLen encS p + 1) ^ 2

theorem spaceB_le_timeB (p : (σ × ℕ) × Option Bool) : spaceB encS S p ≤ timeB encS T S p := by
  simp only [spaceB, timeB]
  have h₁ : S p.1.1 + inLen encS p ≤ (T p.1.1 + S p.1.1 + inLen encS p + 1) ^ 2 :=
    (by omega : _ ≤ T p.1.1 + S p.1.1 + inLen encS p + 1).trans (Nat.le_self_pow (by norm_num) _)
  exact h₁.trans (Nat.le_mul_of_pos_left _ (by omega))

theorem inLen_le_spaceB (p : (σ × ℕ) × Option Bool) : inLen encS p ≤ spaceB encS S p := by
  simp

theorem inLen_le_timeB (p : (σ × ℕ) × Option Bool) : inLen encS p ≤ timeB encS T S p :=
  (inLen_le_spaceB (S := S) p).trans (spaceB_le_timeB p)

/-- The projections of the input are within the budgets. -/
theorem budget_proj :
    ComputableInO (fun p : (σ × ℕ) × Option Bool => p.1.1) (encStepIn encS) encS
      (timeB encS T S) (spaceB encS S) ∧
    ComputableInO (fun p : (σ × ℕ) × Option Bool => p.1.2) (encStepIn encS) encNat
      (timeB encS T S) (spaceB encS S) ∧
    ComputableInO (fun p : (σ × ℕ) × Option Bool => p.2) (encStepIn encS)
      (encOption encBool) (timeB encS T S) (spaceB encS S) := by
  have h₁ := fst (encPair encS encNat) (encOption encBool)
  refine ⟨(fst' h₁).weaken (.of_le inLen_le_timeB)
      (.of_le inLen_le_spaceB),
    (snd' h₁).weaken (.of_le inLen_le_timeB)
      (.of_le inLen_le_spaceB),
    (snd (encPair encS encNat) (encOption encBool)).weaken
      (.of_le inLen_le_timeB) (.of_le inLen_le_spaceB)⟩

/-- The time of a comparison with the head position is within the time budget. -/
theorem lt_bigOLe {u : (σ × ℕ) × Option Bool → ℕ} (h : u ≼ spaceB encS S) :
    (fun p => (p.1.2 + 1) * (u p + 1) ^ 2) ≼ timeB encS T S := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(c + 1) ^ 2, fun p => ?_⟩
  have h₁ : u p + 1 ≤ (c + 1) * (T p.1.1 + S p.1.1 + inLen encS p + 1) := by
    have := hc p; simp only [spaceB] at this; nlinarith
  have h₂ := Nat.pow_le_pow_left h₁ 2
  simp only [timeB]
  calc (p.1.2 + 1) * (u p + 1) ^ 2
      ≤ (p.1.2 + 1) * ((c + 1) * (T p.1.1 + S p.1.1 + inLen encS p + 1)) ^ 2 :=
        Nat.mul_le_mul_left _ h₂
    _ = (c + 1) ^ 2 * ((p.1.2 + 1) * (T p.1.1 + S p.1.1 + inLen encS p + 1) ^ 2) := by ring
    _ ≤ _ := by nlinarith

/-- A square of something within the space budget is within the time budget. -/
theorem sq_bigOLe {u : (σ × ℕ) × Option Bool → ℕ} (h : u ≼ spaceB encS S) :
    (fun p => (u p + 1) ^ 2) ≼ timeB encS T S :=
  (BigOLe.of_le fun _ => Nat.le_mul_of_pos_left _ (by omega)).trans (lt_bigOLe h)

/-- The step of the simulating machine, written with its components. -/
def stepBy (m : ReadMachine σ) (p : (σ × ℕ) × Option Bool) : (σ × ℕ) × SignType × List Bool :=
  let isN := (m.addr p.1.1).isNone
  let A₁ := (m.addr p.1.1).getD 0 + 1
  let e := decide (p.1.2 = A₁)
  let l := decide (p.1.2 < A₁)
  let b := (fun q : Bool × Bool × Option Bool => if q.1 then false else if q.2.1 then
    q.2.2.getD false else false) (isN, e, p.2)
  let r := m.step p.1.1 b
  let cond := (fun q : Bool × Bool × Bool × Option Bool × Bool =>
    q.1 || q.2.1 || (q.2.2.1 && q.2.2.2.1.isNone && !q.2.2.2.2))
      (isN, e, l, p.2, decide (p.1.2 = 0))
  if cond then ((r.1, p.1.2), 0, r.2)
  else if l then ((p.1.1, p.1.2 + 1), 1, [])
  else ((p.1.1, p.1.2 - 1), -1, [])

theorem stepBy_eq (p : (σ × ℕ) × Option Bool) : stepBy m p = (m.toStepMachine).step p.1 p.2 := by
  obtain ⟨⟨q, pos⟩, a⟩ := p
  simp only [stepBy, toStepMachine, stepAt]
  rcases hA : m.addr q with _ | A
  · simp
  · by_cases h₁ : pos = A + 1
    · simp [h₁]
    · by_cases h₂ : pos < A + 1
      · by_cases h₃ : a = none ∧ pos ≠ 0
        · obtain ⟨rfl, h₄⟩ := h₃
          simp [h₁, h₂, h₄]
        · rcases a with _ | a
          · have h₄ : pos = 0 := by simpa using h₃
            simp [h₄]
          · simp [h₁, h₂]
      · simp [h₁, h₂]

/-- The time bound of a state of the simulating machine. -/
abbrev stateT (encS : σ ↪ List Bool) (T S : σ → ℕ) (q : σ × ℕ) : ℕ :=
  (q.2 + 1) * (T q.1 + S q.1 + 2 * (encPair encS encNat q).length + 4) ^ 2

/-- The space bound of a state of the simulating machine. -/
abbrev stateS (encS : σ ↪ List Bool) (S : σ → ℕ) (q : σ × ℕ) : ℕ :=
  S q.1 + 2 * (encPair encS encNat q).length + 4

theorem inLen_le (p : (σ × ℕ) × Option Bool) :
    inLen encS p ≤ 2 * (encPair encS encNat p.1).length + 3 := by
  obtain ⟨q, a⟩ := p
  rcases a with _ | b <;> simp [inLen, encStepIn]

/-- **The simulating step machine has a resource certificate**, if the halting test, address and
step have plain resource certificates with the given state bounds. -/
theorem toStepMachine_resourceCertificate (hhalt : ComputableInO m.halt encS encBool T S)
    (haddr : ComputableInO m.addr encS (encOption encNat) T S)
    (hstep : ComputableInO (fun p : σ × Bool => m.step p.1 p.2) (encPair encS encBool)
      (encPair encS encBits) (fun p => T p.1) fun p => S p.1) :
    (m.toStepMachine).ResourceCertificate (encPair encS encNat)
      (stateT encS T S) (stateS encS S) where
  computable_halt := by
    refine ((hhalt.comp (fst encS encNat)).mono_le (fun q => ?_) fun q => ?_)
    · simp only [stateT]
      have : (encPair encS encNat q).length + T q.1 ≤
          (T q.1 + S q.1 + 2 * (encPair encS encNat q).length + 4) ^ 2 :=
        (by omega : _ ≤ T q.1 + S q.1 + 2 * (encPair encS encNat q).length + 4).trans
          (Nat.le_self_pow (by norm_num) _)
      exact this.trans (Nat.le_mul_of_pos_left _ (by omega))
    · simp only [stateS]; omega
  computable_step := by
    have hst : spaceB encS S ≼ timeB encS T S := .of_le spaceB_le_timeB
    have hin : (fun p => (encStepIn encS p).length) ≼ spaceB encS S := .of_le inLen_le_spaceB
    obtain ⟨hq, hpos, ha⟩ := budget_proj (encS := encS) (T := T) (S := S)
    -- the address and its components
    have hT : (fun p : (σ × ℕ) × Option Bool => T p.1.1) ≼ timeB encS T S := .of_le fun p => by
      simp only [timeB]
      have : T p.1.1 ≤ (T p.1.1 + S p.1.1 + inLen encS p + 1) ^ 2 :=
        (by omega : _ ≤ T p.1.1 + S p.1.1 + inLen encS p + 1).trans
          (Nat.le_self_pow (by norm_num) _)
      exact this.trans (Nat.le_mul_of_pos_left _ (by omega))
    have hS : (fun p : (σ × ℕ) × Option Bool => S p.1.1) ≼ spaceB encS S := .of_le fun p => by
      simp [spaceB]
    have hA := budget_comp haddr hq hT hS
    have hisNone : ComputableInO (fun o : Option ℕ => o.isNone)
        (encOption encNat) encBool (fun o => (encOption encNat o).length)
        (fun o => (encOption encNat o).length) := by
      refine ((ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool)
        Bool.not).inO_one.comp_linear (ComputableInDegree.isSome encNat).inO_one).of_enc_eq
          (g := fun o : Option ℕ => o.isNone) fun o => ?_
      cases o <;> rfl
    have hisN := budget_comp_linear hisNone hA hst
    have hgetD := budget_comp_linear (ComputableInDegree.getD (enc₁ := encNat) 0).inO_one
      hA hst
    have hA₁ := budget_comp natSucc hgetD (sq_bigOLe hgetD.length_le)
      (.add hgetD.length_le (.const 1 _))
    have hpair := budget_prod hpos hA₁
    have he := budget_comp (ComputableInO.eq encNat) hpair
      ((BigOLe.of_le fun p => by simp only [length_encPair]; nlinarith).trans
        (sq_bigOLe hpair.length_le)) hpair.length_le
    have hl := budget_comp natLt hpair (sq_bigOLe hpair.length_le)
      (.add hpair.length_le (.const 1 _))
    -- the bit read and the step of the read machine
    have hb := budget_finite (encD := encBool)
      (fun q : Bool × Bool × Option Bool => if q.1 then false else if q.2.1
        then q.2.2.getD false else false) (budget_prod hisN (budget_prod he ha)) hst
    have hr := budget_comp hstep (budget_prod hq hb) hT hS
    have hz := budget_comp_linear natIsZero hpos hst
    have hc := budget_finite (encD := encBool) (fun q : Bool × Bool × Bool × Option Bool × Bool =>
      q.1 || q.2.1 || (q.2.2.1 && q.2.2.2.1.isNone && !q.2.2.2.2))
      (budget_prod hisN (budget_prod he (budget_prod hl (budget_prod ha hz)))) hst
    -- the three results
    have hres₁ := budget_prod (encB := encPair encS encNat) (budget_prod (fst' hr) hpos)
      (budget_prod (encB := encSign) (budget_const (0 : SignType) hin hst) (snd' hr))
    have hres₂ := budget_prod (encB := encPair encS encNat) (budget_prod hq
      (budget_comp natSucc hpos (sq_bigOLe hpos.length_le)
        (.add hpos.length_le (.const 1 _))))
      (budget_prod (encB := encSign) (budget_const (1 : SignType) hin hst)
        (budget_const (encB := encBits) ([] : List Bool) hin hst))
    have hres₃ := budget_prod (encB := encPair encS encNat) (budget_prod hq
      (budget_comp natPred hpos (sq_bigOLe hpos.length_le)
        (.add hpos.length_le (.const 1 _))))
      (budget_prod (encB := encSign) (budget_const (-1 : SignType) hin hst)
        (budget_const (encB := encBits) ([] : List Bool) hin hst))
    have hall := budget_ite hc hres₁ (budget_ite hl hres₂ hres₃)
    refine ((hall.of_enc_eq fun p => by rw [← stepBy_eq]; rfl).mono 4 (fun p => ?_)
      fun p => ?_)
    · have := inLen_le (encS := encS) p
      simp only [timeB, stateT]
      have h : T p.1.1 + S p.1.1 + inLen encS p + 1 ≤
          T p.1.1 + S p.1.1 + 2 * (encPair encS encNat p.1).length + 4 := by omega
      have := Nat.mul_le_mul_left (p.1.2 + 1) (Nat.pow_le_pow_left h 2)
      omega
    · have := inLen_le (encS := encS) p
      simp only [spaceB, stateS]
      omega

end ReadMachine

end Turing
