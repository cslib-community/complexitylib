/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Witness
public import Mathlib.Logic.Equiv.Fin.Basic
import CslibFrontier.DataStructure.Memory.Frame

/-!
# Uniform sequential realization of memory clients

The continuation has one realization for the environment paired with its runtime answer.
Its source registers append the first computation's answer slots to the original inputs.
The predecessor's auxiliary words are dead after its answer is available, so the continuation
reuses them. Its bank already contains the final output slots, so no result copy is needed.
The retained witness gives the concrete scratch, factor and emitter with the existing Spec.

## Main definitions

* `bindSharedLeft`, `bindSharedRight`: the shared-bank layout for retained binds.
* `Realizes.Witness.bind`: sequential composition retaining data and sharing dead scratch.

## Main results

* `bindShared_layout`: both stages' register premises from those of the composite bank.
* `bindShared_appendWords`: the continuation's source bank after the predecessor's frame and output.
* `bind_cost_le`: additive cost bound under the maximum of two exchange factors.
* `Realizes.SpecWith.bind`, `Realizes.With.bind`: judgment-parametric sequential composition.
* `Realizes.bind`, `RealizesBounded.bind`: sequential realization certificates.
* `Realizes.Witness.bind_execWithin`: tighter native budgets on the same supplied emitter.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-- The continuation's prefix in a bind that shares dead predecessor auxiliary words. -/
def bindSharedLeft {m n₂ l n₁ : ℕ} (i : Fin (m + n₂ + 1)) :
    Fin (m + (l + max n₁ n₂) + 1) := ⟨i.val, by omega⟩

/-- The predecessor's live answer is placed at the tail; its dead auxiliary words share the
continuation's prefix. Each stage map is injective, although their union need not be. -/
def bindSharedRight {m n₂ l n₁ : ℕ} (i : Fin (l + n₁ + 1)) :
    Fin (m + (l + max n₁ n₂) + 1) :=
  if h : i.val < l then ⟨m + max n₁ n₂ + 1 + i.val, by omega⟩
  else ⟨i.val - l, by omega⟩

/-- The register premises of both stages of a shared-bank bind. If the composite bank `tmp` is
injective and avoids the sources `src` and the frontier, then the predecessor's bank
`tmp ∘ bindSharedRight` and the continuation's bank `tmp ∘ bindSharedLeft` are injective. The
continuation's sources, `src` followed by the predecessor's live answer slots, avoid its bank
and the frontier. -/
theorem bindShared_layout {r k m l n₁ n₂ : ℕ} {frontier : Fin r} {src : Fin k → Fin r}
    {tmp : Fin (m + (l + max n₁ n₂) + 1) → Fin r} (hi : Function.Injective tmp)
    (hd : ∀ i j, src i ≠ tmp j) (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    Function.Injective (tmp ∘ bindSharedRight) ∧ Function.Injective (tmp ∘ bindSharedLeft) ∧
      (∀ i j, Fin.append src (fun a => tmp (bindSharedRight (Fin.castAdd (n₁ + 1) a))) i ≠
        tmp (bindSharedLeft j)) ∧
      ∀ i, Fin.append src (fun a => tmp (bindSharedRight (Fin.castAdd (n₁ + 1) a))) i ≠
        frontier := by
  have hleft : Function.Injective (tmp ∘ bindSharedLeft) := by
    intro a b hab
    have h := congrArg Fin.val (hi hab)
    exact Fin.ext h
  have hright : Function.Injective (tmp ∘ bindSharedRight) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val (hi hab)
    have hm₁ := Nat.le_max_left n₁ n₂
    have ha := a.isLt
    have hb := b.isLt
    dsimp only [Function.comp_apply, bindSharedRight] at h
    split_ifs at h <;> dsimp only at h <;> omega
  -- The predecessor's live answer sits in the tail, above every slot of the continuation.
  have hdisjoint (a : Fin l) (b : Fin (m + n₂ + 1)) :
      tmp (bindSharedRight (Fin.castAdd (n₁ + 1) a)) ≠ tmp (bindSharedLeft b) := by
    intro hab
    have h := congrArg Fin.val (hi hab)
    have hm₂ := Nat.le_max_right n₁ n₂
    have hb := b.isLt
    simp only [bindSharedRight, Fin.val_castAdd, dite_eq_left a.isLt, bindSharedLeft] at h
    omega
  refine ⟨hright, hleft, fun i j => ?_, fun i => ?_⟩
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [Fin.append_left] using hd a (bindSharedLeft j)
    · simpa only [Fin.append_right] using hdisjoint b j
  · refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [Fin.append_left] using hs a
    · simpa only [Fin.append_right] using hf (bindSharedRight (Fin.castAdd (n₁ + 1) b))

/-- After the predecessor writes `answer a` into its live tail slots and preserves registers
outside `frontier` and `tmp ∘ bindSharedRight`, the continuation's source bank holds
`appendWords input answer (d, a)`. -/
theorem bindShared_appendWords {δ α : Type} {r k m l n₁ n₂ : ℕ}
    {frontier : Fin r} {src : Fin k → Fin r} {tmp : Fin (m + (l + max n₁ n₂) + 1) → Fin r}
    {input : δ ↪ (Fin k → ℕ)} {answer : α ↪ (Fin l → ℕ)} {d : δ} {a : α} {x z : Data r}
    (hin : x.regs ∘ src = input d)
    (hframe : ∀ i, i ≠ frontier → (∀ j, (tmp ∘ bindSharedRight) j ≠ i) → z.regs i = x.regs i)
    (hd : ∀ i j, src i ≠ tmp j) (hs : ∀ i, src i ≠ frontier)
    (hout : ∀ j : Fin l,
      z.regs ((tmp ∘ bindSharedRight) (Fin.castAdd (n₁ + 1) j)) = answer a j) :
    z.regs ∘ Fin.append src (fun i => tmp (bindSharedRight (Fin.castAdd (n₁ + 1) i))) =
      appendWords input answer (d, a) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · change z.regs (Fin.append src _ (Fin.castAdd l j)) =
      Fin.append (input d) (answer a) (Fin.castAdd l j)
    simp only [Fin.append_left]
    exact (hframe (src j) (hs j) (fun t => (hd j _).symm)).trans (congrFun hin j)
  · change z.regs (Fin.append src _ (Fin.natAdd k j)) =
      Fin.append (input d) (answer a) (Fin.natAdd k j)
    simpa only [Fin.append_right, Function.comp_apply] using hout j

/-- Combine two stage cost bounds `C₁ * (t₁ + 1)` and `C₂ * (t₂ + 1)` under `max C₁ C₂`. -/
theorem bind_cost_le {C₁ C₂ t₁ t₂ t : ℕ} (ht : t₁ + t₂ + 1 ≤ t) :
    C₁ * (t₁ + 1) + C₂ * (t₂ + 1) ≤ max C₁ C₂ * (t + 1) := by
  calc
    _ ≤ max C₁ C₂ * (t₁ + 1) + max C₁ C₂ * (t₂ + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
        (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
    _ = max C₁ C₂ * (t₁ + t₂ + 1 + 1) := by ring
    _ ≤ max C₁ C₂ * (t + 1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right ht 1)

private theorem bind_intermediate {δ α β : Type} {r k m l n₁ n₂ : ℕ}
    {p : δ → Memory.Prog α} {q : δ × α → Memory.Prog β}
    {input : δ ↪ (Fin k → ℕ)} {answer : α ↪ (Fin l → ℕ)}
    {safeQ : ℕ → δ × α → Memory.State → Prop}
    {frontier : Fin r} {src : Fin k → Fin r} {tmp : Fin (m + (l + max n₁ n₂) + 1) → Fin r}
    {w : ℕ} {d : δ} {x z : Data r}
    (hin : x.regs ∘ src = input d)
    (hsafeQ0 : safeQ w (d, (Memory.spec 0).clientResult (memoryState frontier x) (p d))
      ((Memory.spec 0).clientState (memoryState frontier x) (p d)))
    (hvQ : (Memory.spec w).ValidHistory
      ((Memory.spec w).clientState (memoryState frontier x) (p d))
      ((Memory.spec w).clientHistory
        ((Memory.spec w).clientState (memoryState frontier x) (p d))
        (q (d, (Memory.spec w).clientResult (memoryState frontier x) (p d)))))
    (hmP : memoryState frontier z = (Memory.spec w).clientState (memoryState frontier x) (p d))
    (houtP : ∀ i : Fin l, z.regs ((tmp ∘ bindSharedRight) (Fin.castAdd (n₁ + 1) i)) =
      answer ((Memory.spec w).clientResult (memoryState frontier x) (p d)) i)
    (hframeP : ∀ i, i ≠ frontier → (∀ j, (tmp ∘ bindSharedRight) j ≠ i) → z.regs i = x.regs i)
    (hd : ∀ i j, src i ≠ tmp j) (hs : ∀ i, src i ≠ frontier) :
    let s := memoryState frontier x
    let a := (Memory.spec 0).clientResult s (p d)
    let s' := (Memory.spec 0).clientState s (p d)
    memoryState frontier z = s' ∧
      z.regs ∘ Fin.append src (fun i => tmp (bindSharedRight (Fin.castAdd (n₁ + 1) i))) =
        appendWords input answer (d, a) ∧
      safeQ w (d, a) (memoryState frontier z) ∧
      (Memory.spec w).ValidHistory (memoryState frontier z)
        ((Memory.spec w).clientHistory (memoryState frontier z) (q (d, a))) := by
  dsimp only
  rw [clientState_width] at hmP hvQ
  rw [clientResult_width] at houtP hvQ
  exact ⟨hmP, bindShared_appendWords hin hframeP hd hs houtP, hmP.symm ▸ hsafeQ0, hmP.symm ▸ hvQ⟩

private theorem clientState_clientResult_bind_width {α β : Type} (w : ℕ) (s : Memory.State)
    (p : Memory.Prog α) (q : α → Memory.Prog β) :
    (Memory.spec w).clientState s (p.bind q) =
        (Memory.spec w).clientState ((Memory.spec 0).clientState s p)
          (q ((Memory.spec 0).clientResult s p)) ∧
      (Memory.spec w).clientResult s (p.bind q) =
        (Memory.spec w).clientResult ((Memory.spec 0).clientState s p)
          (q ((Memory.spec 0).clientResult s p)) := by
  change (Memory.spec w).clientState s (p >>= q) = _ ∧
    (Memory.spec w).clientResult s (p >>= q) = _
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
  simp only [clientState_width w p s, clientResult_width w p s, and_self]

namespace Realizes

variable {B : Basis} {δ α β : Type} {k l m : ℕ}
  {p : δ → Memory.Prog α} {q : δ × α → Memory.Prog β}
  {input : δ ↪ (Fin k → ℕ)} {answer : α ↪ (Fin l → ℕ)}
  {output : β ↪ (Fin m → ℕ)}
  {safeP : ℕ → δ → Memory.State → Prop} {safeQ : ℕ → δ × α → Memory.State → Prop}
  {workP : δ → Memory.State → ℕ} {workQ : δ × α → Memory.State → ℕ}

/-- Shared verification core for sequential `Memory.Prog` composition over parametric execution
judgments `execP` and `execQ`. Produces the composite non-`ReadsWidth` check and, given any
admissible entry state, constructs the intermediate and final states, frontier monotonicity,
both stage execution certificates, and the composite memory, output and frame facts. -/
private theorem bind_run
    {execP execQ : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {n₁ C₁ n₂ C₂ : ℕ}
    {emitP : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n₁ + 1) → Fin r) → Code B r}
    {emitQ : ∀ {r : ℕ}, (frontier : Fin r) → (Fin (k + l) → Fin r) →
      (Fin (m + n₂ + 1) → Fin r) → Code B r}
    (hsP : SpecWith B execP p input answer safeP workP n₁ C₁ emitP)
    (hsQ : SpecWith B execQ q (appendWords input answer) output safeQ workQ n₂ C₂ emitQ)
    (hbounded : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x z : Data r} {T : ℕ},
      execP w frontier c x z T → x.Bounded w → z.Bounded w)
    {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r)
    (tmp : Fin (m + (l + max n₁ n₂) + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    let N := l + max n₁ n₂
    let left : Fin (m + n₂ + 1) → Fin (m + N + 1) := bindSharedLeft
    let right : Fin (l + n₁ + 1) → Fin (m + N + 1) := bindSharedRight
    let nextSrc := Fin.append src (fun i => tmp (right (Fin.castAdd (n₁ + 1) i)))
    ¬(Code.seq (emitP frontier src (tmp ∘ right))
        (emitQ frontier nextSrc (tmp ∘ left))).ReadsWidth ∧
      ∀ (w : ℕ) (d : δ) (x : Data r),
        let s := memoryState frontier x
        let a := (Memory.spec 0).clientResult s (p d)
        let s' := (Memory.spec 0).clientState s (p d)
        x.Bounded w → x.regs ∘ src = input d → (safeP w d s ∧ safeQ w (d, a) s') →
        (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s ((p d).bind fun a => q (d, a))) →
        ∃ z y,
          (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) ∧
          z.Bounded w ∧ z.regs ∘ nextSrc = appendWords input answer (d, a) ∧
          memoryState frontier z = s' ∧ safeQ w (d, a) (memoryState frontier z) ∧
          (Memory.spec w).ValidHistory (memoryState frontier z)
            ((Memory.spec w).clientHistory (memoryState frontier z) (q (d, a))) ∧
          z.regs frontier ≤ y.regs frontier ∧
          execP w frontier (emitP frontier src (tmp ∘ right)) x z
            (C₁ * (memoryCost (p d) s + workP d s + 1)) ∧
          execQ w frontier (emitQ frontier nextSrc (tmp ∘ left)) z y
            (C₂ * (memoryCost (q (d, a)) s' + workQ (d, a) s' + 1)) ∧
          memoryState frontier y = (Memory.spec w).clientState s ((p d).bind fun a => q (d, a)) ∧
          (∀ i : Fin m, y.regs (tmp (Fin.castAdd (N + 1) i)) =
            output ((Memory.spec w).clientResult s ((p d).bind fun a => q (d, a))) i) ∧
          ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  let N := l + max n₁ n₂
  let left : Fin (m + n₂ + 1) → Fin (m + N + 1) := bindSharedLeft
  let right : Fin (l + n₁ + 1) → Fin (m + N + 1) := bindSharedRight
  let nextSrc : Fin (k + l) → Fin r :=
    Fin.append src (fun i => tmp (right (Fin.castAdd (n₁ + 1) i)))
  obtain ⟨hright, hleft, hnextDisjoint, hnextFrontier⟩ := bindShared_layout hi hd hf hs
  obtain ⟨hnwP, hrunP⟩ := hsP frontier src (tmp ∘ right) hright
    (fun i j => hd i (right j)) (fun j => hf (right j)) hs
  obtain ⟨hnwQ, hrunQ⟩ := hsQ frontier nextSrc (tmp ∘ left) hleft hnextDisjoint
    (fun j => hf (left j)) hnextFrontier
  refine ⟨fun h => h.elim hnwP hnwQ, fun w d x hx hin hsafe hv => ?_⟩
  let s := memoryState frontier x
  let a := (Memory.spec 0).clientResult s (p d)
  let s' := (Memory.spec 0).clientState s (p d)
  obtain ⟨hvP, hvQ⟩ := (validHistory_bind w (p d) (fun a => q (d, a)) s).mp hv
  obtain ⟨z, hz, hmP, houtP, hframeP⟩ := hrunP w d x hx hin hsafe.1 hvP
  have hzb : z.Bounded w := hbounded hz hx
  obtain ⟨hmP', hinQ, hsafeQ, hvalidQ⟩ :=
    bind_intermediate (q := q) hin hsafe.2 hvQ hmP houtP hframeP hd hs
  obtain ⟨y, hy, hmQ, houtQ, hframeQ⟩ :=
    hrunQ w (d, a) z hzb hinQ hsafeQ hvalidQ
  have hfr_le : z.regs frontier ≤ y.regs frontier := by
    have hle := Memory.frontier_le_clientState (w := w) (memoryState frontier z) (q (d, a))
    have hmQ_fr := congrArg Memory.State.frontier hmQ
    change y.regs frontier =
      ((Memory.spec w).clientState (memoryState frontier z) (q (d, a))).frontier at hmQ_fr
    exact hmQ_fr ▸ hle
  obtain ⟨hstate_bind, hres_bind⟩ :=
    clientState_clientResult_bind_width w s (p d) fun a => q (d, a)
  refine ⟨z, y, hvP, hzb, hinQ, hmP', hsafeQ, hvalidQ, hfr_le, hz, ?_, ?_, ?_, ?_⟩
  · simpa only [hmP'] using hy
  · rw [hmP'] at hmQ
    exact hmQ.trans hstate_bind.symm
  · intro i
    have hout := houtQ i
    rw [hmP'] at hout
    exact hout.trans (congrArg (output · i) hres_bind.symm)
  · intro i hif htmp
    exact (hframeQ i hif (fun j => htmp (left j))).trans
      (hframeP i hif (fun j => htmp (right j)))

/-- Judgment-parametric sequential composition on `SpecWith`. -/
theorem SpecWith.bind
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    {n₁ C₁ n₂ C₂ : ℕ}
    {emitP : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (l + n₁ + 1) → Fin r) → Code B r}
    {emitQ : ∀ {r : ℕ}, (frontier : Fin r) → (Fin (k + l) → Fin r) →
      (Fin (m + n₂ + 1) → Fin r) → Code B r}
    (hsP : SpecWith B exec p input answer safeP workP n₁ C₁ emitP)
    (hsQ : SpecWith B exec q (appendWords input answer) output safeQ workQ n₂ C₂ emitQ)
    (hbounded : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x z : Data r} {T : ℕ},
      exec w frontier c x z T → x.Bounded w → z.Bounded w)
    (hseq : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c₁ c₂ : Code B r} {x z y : Data r}
      {T₁ T₂ : ℕ}, z.regs frontier ≤ y.regs frontier →
      exec w frontier c₁ x z T₁ → exec w frontier c₂ z y T₂ →
      exec w frontier (.seq c₁ c₂) x y (T₁ + T₂))
    (hmono : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T₁ T₂ : ℕ},
      T₁ ≤ T₂ → exec w frontier c x y T₁ → exec w frontier c x y T₂) :
    SpecWith B exec (fun d => (p d).bind (fun a => q (d, a))) input output
      (fun w d s => safeP w d s ∧
        safeQ w (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)))
      (fun d s => workP d s +
        workQ (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)) + 1)
      (l + max n₁ n₂) (max C₁ C₂)
      (fun frontier src tmp =>
        .seq (emitP frontier src (tmp ∘ bindSharedRight))
          (emitQ frontier
            (Fin.append src (fun i => tmp (bindSharedRight (Fin.castAdd (n₁ + 1) i))))
            (tmp ∘ bindSharedLeft))) := by
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hnw, hrun⟩ := bind_run hsP hsQ hbounded frontier src tmp hi hd hf hs
  refine ⟨hnw, fun w d x hx hin hsafe hv => ?_⟩
  let s := memoryState frontier x
  let a := (Memory.spec 0).clientResult s (p d)
  let s' := (Memory.spec 0).clientState s (p d)
  obtain ⟨z, y, _, _, _, _, _, _, hfr_le, hz, hy, hm, hout, hframe⟩ :=
    hrun w d x hx hin hsafe hv
  refine ⟨y, hmono ?_ (hseq hfr_le hz hy), hm, hout, hframe⟩
  change C₁ * (memoryCost (p d) s + workP d s + 1) +
      C₂ * (memoryCost (q (d, a)) s' + workQ (d, a) s' + 1) ≤
    max C₁ C₂ * (memoryCost ((p d).bind fun a => q (d, a)) s +
      (workP d s + workQ (d, a) s' + 1) + 1)
  rw [memoryCost_bind]
  exact bind_cost_le (by dsimp only [a, s']; omega)

/-- Judgment-parametric sequential composition on `Realizes.With`. -/
theorem With.bind
    {exec : ∀ {r : ℕ}, ℕ → Fin r → Code B r → Data r → Data r → ℕ → Prop}
    (hP : With B exec p input answer safeP workP)
    (hQ : With B exec q (appendWords input answer) output safeQ workQ)
    (hbounded : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x z : Data r} {T : ℕ},
      exec w frontier c x z T → x.Bounded w → z.Bounded w)
    (hseq : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c₁ c₂ : Code B r} {x z y : Data r}
      {T₁ T₂ : ℕ}, z.regs frontier ≤ y.regs frontier →
      exec w frontier c₁ x z T₁ → exec w frontier c₂ z y T₂ →
      exec w frontier (.seq c₁ c₂) x y (T₁ + T₂))
    (hmono : ∀ {r : ℕ} {w : ℕ} {frontier : Fin r} {c : Code B r} {x y : Data r} {T₁ T₂ : ℕ},
      T₁ ≤ T₂ → exec w frontier c x y T₁ → exec w frontier c x y T₂) :
    With B exec (fun d => (p d).bind (fun a => q (d, a))) input output
      (fun w d s => safeP w d s ∧
        safeQ w (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)))
      (fun d s => workP d s +
        workQ (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)) + 1) :=
  let ⟨_, _, _, hsP⟩ := hP
  let ⟨_, _, _, hsQ⟩ := hQ
  ⟨_, _, _, SpecWith.bind hsP hsQ hbounded hseq hmono⟩

/-- Tighten the native budgets of the supplied component runs without changing code, domain
or semantic postconditions. The continuation receives the predecessor's derived encoded answer,
exact intermediate memory, boundedness, safety and valid history. Both stages receive their
derived layout premises. Only execution bounds are
supplied by the callbacks; the complete frame/input/memory proof is shared with `Witness.bind`.
The resulting bound is additive on the same retained sequential emitter. -/
theorem Witness.bind_execWithin (hP : Witness B p input answer safeP workP)
    (hQ : Witness B q (appendWords input answer) output safeQ workQ) :
  let n₁ := hP.scratchSize
  let n₂ := hQ.scratchSize
  let C₁ := hP.factor
  let C₂ := hQ.factor
  let N := l + max n₁ n₂
  let left : Fin (m + n₂ + 1) → Fin (m + N + 1) := bindSharedLeft
  let right : Fin (l + n₁ + 1) → Fin (m + N + 1) := bindSharedRight
  let emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (m + N + 1) → Fin r) → Code B r := fun frontier src tmp =>
    .seq (hP.code frontier src (tmp ∘ right))
      (hQ.code frontier
        (Fin.append src (fun i => tmp (right (Fin.castAdd (n₁ + 1) i)))) (tmp ∘ left))
  ∀ {r : ℕ} (frontier : Fin r) (src : Fin k → Fin r) (tmp : Fin (m + N + 1) → Fin r),
    Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
    (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
    ¬(emit frontier src tmp).ReadsWidth ∧
    ∀ (w : ℕ) (d : δ) (x : Data r),
      let s := memoryState frontier x
      let a := (Memory.spec 0).clientResult s (p d)
      let s' := (Memory.spec 0).clientState s (p d)
      let nextSrc := Fin.append src (fun i => tmp (right (Fin.castAdd (n₁ + 1) i)))
      x.Bounded w → x.regs ∘ src = input d → (safeP w d s ∧ safeQ w (d, a) s') →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s ((p d).bind fun a => q (d, a))) →
      ∀ TP TQ : ℕ,
        (Function.Injective (tmp ∘ right) →
          (∀ i j, src i ≠ (tmp ∘ right) j) → (∀ j, (tmp ∘ right) j ≠ frontier) →
          (∀ i, src i ≠ frontier) →
          (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
          ∀ z, ExecWithin w (hP.code frontier src (tmp ∘ right)) x z
          (C₁ * (memoryCost (p d) s + workP d s + 1)) →
            ExecWithin w (hP.code frontier src (tmp ∘ right)) x z TP) →
        (∀ z, Function.Injective (tmp ∘ left) →
          (∀ i j, nextSrc i ≠ (tmp ∘ left) j) → (∀ j, (tmp ∘ left) j ≠ frontier) →
          (∀ i, nextSrc i ≠ frontier) →
          z.Bounded w → z.regs ∘ nextSrc = appendWords input answer (d, a) →
          memoryState frontier z = s' → safeQ w (d, a) (memoryState frontier z) →
          (Memory.spec w).ValidHistory (memoryState frontier z)
            ((Memory.spec w).clientHistory (memoryState frontier z) (q (d, a))) →
          ∀ y, ExecWithin w (hQ.code frontier nextSrc (tmp ∘ left)) z y
            (C₂ * (memoryCost (q (d, a)) (memoryState frontier z) +
              workQ (d, a) (memoryState frontier z) + 1)) →
            ExecWithin w (hQ.code frontier nextSrc (tmp ∘ left)) z y TQ) →
        ∃ y, ExecWithin w (emit frontier src tmp) x y (TP + TQ) ∧
          memoryState frontier y = (Memory.spec w).clientState s ((p d).bind fun a => q (d, a)) ∧
          (∀ i : Fin m, y.regs (tmp (Fin.castAdd (N + 1) i)) =
            output ((Memory.spec w).clientResult s ((p d).bind fun a => q (d, a))) i) ∧
          ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  dsimp only
  intro r frontier src tmp hi hd hf hs
  obtain ⟨hright, hleft, hnextDisjoint, hnextFrontier⟩ := bindShared_layout hi hd hf hs
  obtain ⟨hnw, hrun⟩ := bind_run hP.code_spec hQ.code_spec
    (fun h => h.bounded) frontier src tmp hi hd hf hs
  refine ⟨hnw, fun w d x hx hin hsafe hv TP TQ htP htQ => ?_⟩
  obtain ⟨z, y, hvP, hzb, hinQ, hmP, hsafeQ, hvalidQ, _, hz, hy, hm, hout, hframe⟩ :=
    hrun w d x hx hin hsafe hv
  exact ⟨y, (htP hright (fun i j => hd i _) (fun j => hf _) hs hvP z hz).seq
    (htQ z hleft hnextDisjoint (fun j => hf _) hnextFrontier
      hzb hinQ hmP hsafeQ hvalidQ y (by simpa only [hmP] using hy)),
    hm, hout, hframe⟩

/-- Retain one uniform sequential emitter while reusing the predecessor's dead auxiliary words.
Only its runtime answer remains live in a separate tail bank. The continuation's result slots
are already the composite result slots, so no copies or extra charge are introduced. -/
def Witness.bind (hP : Witness B p input answer safeP workP)
    (hQ : Witness B q (appendWords input answer)
      output safeQ workQ) :
    Witness B (fun d => (p d).bind (fun a => q (d, a))) input output
      (fun w d s => safeP w d s ∧
        safeQ w (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)))
      (fun d s => workP d s +
        workQ (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)) + 1) :=
  let n₁ := hP.scratchSize
  let n₂ := hQ.scratchSize
  let N := l + max n₁ n₂
  { scratchSize := N
    factor := max hP.factor hQ.factor
    code := fun frontier src tmp =>
      .seq (hP.code frontier src (tmp ∘ bindSharedRight))
        (hQ.code frontier
          (Fin.append src (fun i => tmp (bindSharedRight (Fin.castAdd (n₁ + 1) i))))
          (tmp ∘ bindSharedLeft))
    code_spec := SpecWith.bind hP.code_spec hQ.code_spec (fun h => h.bounded)
      (fun _ hz hy => hz.seq hy) (fun hT h => h.mono hT) }

/-- One uniform continuation emitter consumes the original environment and the first runtime
answer. Its domain and work charge are evaluated at the deterministic intermediate state.
All emitted code, register banks and the exchange constant precede runtime answers. -/
theorem bind (hP : Realizes B p input answer safeP workP)
    (hQ : Realizes B q (appendWords input answer)
      output safeQ workQ) :
    Realizes B (fun d => (p d).bind (fun a => q (d, a))) input output
      (fun w d s => safeP w d s ∧
        safeQ w (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)))
      (fun d s => workP d s +
        workQ (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)) + 1) :=
  (Witness.bind (Witness.ofRealizes hP) (Witness.ofRealizes hQ)).toRealizes

end Realizes

namespace RealizesBounded

/-- Frontier-bounded sequential composition of two `Memory.Prog` realizations. -/
theorem bind {B : Basis} {δ α β : Type} {k l m : ℕ}
    {p : δ → Memory.Prog α} {q : δ × α → Memory.Prog β}
    {input : δ ↪ (Fin k → ℕ)} {answer : α ↪ (Fin l → ℕ)} {output : β ↪ (Fin m → ℕ)}
    {safeP : ℕ → δ → Memory.State → Prop} {safeQ : ℕ → δ × α → Memory.State → Prop}
    {workP : δ → Memory.State → ℕ} {workQ : δ × α → Memory.State → ℕ}
    (hP : RealizesBounded B p input answer safeP workP)
    (hQ : RealizesBounded B q (appendWords input answer) output safeQ workQ) :
    RealizesBounded B (fun d => (p d).bind (fun a => q (d, a))) input output
      (fun w d s => safeP w d s ∧
        safeQ w (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)))
      (fun d s => workP d s +
        workQ (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)) + 1) :=
  Realizes.With.bind hP hQ (fun h => h.bounded)
    (fun hfr hz hy => (hz.mono_bound hfr).seq hy) (fun hT h => h.mono hT)

/-- Sequencing with the bind's control unit absorbed (`work = 0`). -/
theorem bind₀ {B : Basis} {δ α β : Type} {k l m : ℕ}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
    {q : δ × α → Memory.Prog β} {answer : α ↪ (Fin l → ℕ)} {output' : β ↪ (Fin m → ℕ)}
    {safeP : ℕ → δ → Memory.State → Prop} {safeQ : ℕ → δ × α → Memory.State → Prop}
    (hP : RealizesBounded B p input answer safeP (fun _ _ => 0))
    (hQ : RealizesBounded B q ((input.prodMap answer).trans (Fin.appendEquiv k l).toEmbedding)
      output' safeQ (fun _ _ => 0)) :
    RealizesBounded B (fun d => (p d).bind (fun a => q (d, a))) input output'
      (fun w d s => safeP w d s ∧
        safeQ w (d, (Memory.spec 0).clientResult s (p d)) ((Memory.spec 0).clientState s (p d)))
      (fun _ _ => 0) :=
  (hP.bind hQ).mono_mul 1 (fun _ _ => by omega)

/-- Sequencing with closed-form reply and next memory (`work = 0`). -/
theorem bind₀_of_run {B : Basis} {δ α β : Type} {k l m : ℕ}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
    {q : δ × α → Memory.Prog β} {answer : α ↪ (Fin l → ℕ)} {output' : β ↪ (Fin m → ℕ)}
    {safeP : ℕ → δ → Memory.State → Prop} {safeQ : ℕ → δ × α → Memory.State → Prop}
    (hP : RealizesBounded B p input answer safeP (fun _ _ => 0))
    (hQ : RealizesBounded B q ((input.prodMap answer).trans (Fin.appendEquiv k l).toEmbedding)
      output' safeQ (fun _ _ => 0))
    (reply : δ → Memory.State → α) (next : δ → Memory.State → Memory.State)
    (hreply : ∀ d s, (Memory.spec 0).clientResult s (p d) = reply d s)
    (hnext : ∀ d s, (Memory.spec 0).clientState s (p d) = next d s) :
    RealizesBounded B (fun d => (p d).bind (fun a => q (d, a))) input output'
      (fun w d s => safeP w d s ∧ safeQ w (d, reply d s) (next d s)) (fun _ _ => 0) :=
  (bind₀ hP hQ).consequence (fun w d s _ _ h => by rw [hreply, hnext]; exact h)
    (fun _ _ => le_rfl)

end RealizesBounded

end Cslib.WordRAM.Realization
