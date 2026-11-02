/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Uniform sequential realization of memory clients

The continuation has one realization for the environment paired with its runtime answer.
Its source registers append the first computation's answer slots to the original inputs.
Two disjoint static scratch banks preserve that environment without client-written intermediate
assertions. The continuation's bank already contains the final output slots, so no copy is needed.

## Main results

* `Realizes.bind`: sequential realization with additive memory and local-work charges.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

private def bindLeft {m n₂ l n₁ : ℕ} (i : Fin (m + n₂ + 1)) :
    Fin (m + (n₂ + l + n₁ + 1) + 1) := ⟨i.val, by omega⟩

private def bindRight {m n₂ l n₁ : ℕ} (i : Fin (l + n₁ + 1)) :
    Fin (m + (n₂ + l + n₁ + 1) + 1) := ⟨m + n₂ + 1 + i.val, by omega⟩

private theorem validHistory_bind {α β : Type} (w : ℕ) (s : Memory.State)
    (p : Memory.Prog α) (q : α → Memory.Prog β) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p.bind q)) ↔
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
        (Memory.spec w).ValidHistory ((Memory.spec w).clientState s p)
          ((Memory.spec w).clientHistory ((Memory.spec w).clientState s p)
            (q ((Memory.spec w).clientResult s p))) := by
  have hh : (Memory.spec w).clientHistory s (p.bind q) =
      (Memory.spec w).clientHistory s p ++
        (Memory.spec w).clientHistory ((Memory.spec w).clientState s p)
          (q ((Memory.spec w).clientResult s p)) := by
    simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.clientState,
      StateTransitionSpec.clientResult, StateTransitionSpec.runClient_bind]
  rw [hh, StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient]

namespace Realizes

variable {B : Basis} {δ α β : Type} {k l m : ℕ}
  {p : δ → Memory.Prog α} {q : δ × α → Memory.Prog β}
  {input : δ ↪ (Fin k → ℕ)} {answer : α ↪ (Fin l → ℕ)}
  {output : β ↪ (Fin m → ℕ)}
  {safeP : ℕ → δ → Memory.State → Prop} {safeQ : ℕ → δ × α → Memory.State → Prop}
  {workP : δ → Memory.State → ℕ} {workQ : δ × α → Memory.State → ℕ}

/-- One uniform continuation emitter consumes the original environment and the first runtime
answer. Its domain and work charge are evaluated at the deterministic intermediate state.
All emitted code, register banks and the exchange constant precede runtime answers. -/
theorem bind (hP : Realizes B p input answer safeP workP)
    (hQ : Realizes B q ((input.prodMap answer).trans (Fin.appendEquiv k l).toEmbedding)
      output safeQ workQ) :
    Realizes B (fun d => (p d).bind (fun a => q (d, a))) input output
      (fun w d s => safeP w d s ∧
        safeQ w (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)))
      (fun d s => workP d s +
        workQ (d, (Memory.spec 0).clientResult s (p d))
          ((Memory.spec 0).clientState s (p d)) + 1) := by
  obtain ⟨n₁, C₁, emitP, heP⟩ := hP
  obtain ⟨n₂, C₂, emitQ, heQ⟩ := hQ
  let N := n₂ + l + n₁ + 1
  let C := max C₁ C₂
  let left : Fin (m + n₂ + 1) → Fin (m + N + 1) := bindLeft
  let right : Fin (l + n₁ + 1) → Fin (m + N + 1) := bindRight
  let emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin k → Fin r) →
      (Fin (m + N + 1) → Fin r) → Code B r := fun frontier src tmp =>
    .seq (emitP frontier src (tmp ∘ right))
      (emitQ frontier
        (Fin.append src (fun i => tmp (right (Fin.castAdd (n₁ + 1) i)))) (tmp ∘ left))
  refine ⟨N, C, emit, ?_⟩
  intro r frontier src tmp hi hd hf hs
  have hleft : Function.Injective (tmp ∘ left) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val (hi hab)
    exact h
  have hright : Function.Injective (tmp ∘ right) := by
    intro a b hab
    apply Fin.ext
    have := congrArg Fin.val (hi hab)
    change m + n₂ + 1 + a.val = m + n₂ + 1 + b.val at this
    omega
  have hdisjoint (a : Fin (l + n₁ + 1)) (b : Fin (m + n₂ + 1)) :
      tmp (right a) ≠ tmp (left b) := by
    intro hab
    have := congrArg Fin.val (hi hab)
    change m + n₂ + 1 + a.val = b.val at this
    omega
  let nextSrc : Fin (k + l) → Fin r :=
    Fin.append src (fun i => tmp (right (Fin.castAdd (n₁ + 1) i)))
  have hnextDisjoint (i : Fin (k + l)) (j : Fin (m + n₂ + 1)) :
      nextSrc i ≠ (tmp ∘ left) j := by
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [nextSrc, Fin.append_left, Function.comp_apply] using hd a (left j)
    · simpa only [nextSrc, Fin.append_right, Function.comp_apply] using
        hdisjoint (Fin.castAdd (n₁ + 1) b) j
  have hnextFrontier (i : Fin (k + l)) : nextSrc i ≠ frontier := by
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa only [nextSrc, Fin.append_left] using hs a
    · simpa only [nextSrc, Fin.append_right] using hf (right (Fin.castAdd (n₁ + 1) b))
  obtain ⟨hnwP, hrunP⟩ := heP frontier src (tmp ∘ right) hright
    (fun i j => hd i (right j)) (fun j => hf (right j)) hs
  obtain ⟨hnwQ, hrunQ⟩ := heQ frontier nextSrc (tmp ∘ left) hleft hnextDisjoint
    (fun j => hf (left j)) hnextFrontier
  refine ⟨fun h => h.elim hnwP hnwQ, ?_⟩
  intro w d x hx hin hsafe hv
  let s := memoryState frontier x
  let a := (Memory.spec 0).clientResult s (p d)
  let s' := (Memory.spec 0).clientState s (p d)
  have hresult : (Memory.spec w).clientResult s (p d) = a :=
    congrArg Prod.fst (runClient_width w (p d) s)
  have hstate : (Memory.spec w).clientState s (p d) = s' :=
    congrArg (fun z => z.2.1) (runClient_width w (p d) s)
  obtain ⟨hvP, hvQ⟩ := (validHistory_bind w s (p d) (fun a => q (d, a))).mp hv
  obtain ⟨z, hz, hmP, houtP, hframeP⟩ := hrunP w d x hx hin hsafe.1 hvP
  change memoryState frontier z = (Memory.spec w).clientState s (p d) at hmP
  rw [hstate] at hmP
  change ∀ i : Fin l, z.regs ((tmp ∘ right) (Fin.castAdd (n₁ + 1) i)) =
    answer ((Memory.spec w).clientResult s (p d)) i at houtP
  rw [hresult] at houtP
  have hinQ : z.regs ∘ nextSrc =
      ((input.prodMap answer).trans (Fin.appendEquiv k l).toEmbedding) (d, a) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change z.regs (nextSrc (Fin.castAdd l j)) =
        Fin.append (input d) (answer a) (Fin.castAdd l j)
      simp only [nextSrc, Fin.append_left]
      exact (hframeP (src j) (hs j) (fun t => (hd j (right t)).symm)).trans (congrFun hin j)
    · change z.regs (nextSrc (Fin.natAdd k j)) =
        Fin.append (input d) (answer a) (Fin.natAdd k j)
      simpa only [nextSrc, Fin.append_right, Function.comp_apply] using houtP j
  have hsafeQ : safeQ w (d, a) (memoryState frontier z) := by
    rw [hmP]
    exact hsafe.2
  have hvalidQ : (Memory.spec w).ValidHistory (memoryState frontier z)
      ((Memory.spec w).clientHistory (memoryState frontier z) (q (d, a))) := by
    rw [hmP]
    simpa only [hstate, hresult] using hvQ
  obtain ⟨y, hy, hmQ, houtQ, hframeQ⟩ :=
    hrunQ w (d, a) z (hz.bounded hx) hinQ hsafeQ hvalidQ
  refine ⟨y, (hz.seq hy).mono ?_, ?_, ?_, ?_⟩
  · change C₁ * (memoryCost (p d) s + workP d s + 1) +
      C₂ * (memoryCost (q (d, a)) (memoryState frontier z) +
        workQ (d, a) (memoryState frontier z) + 1) ≤
        C * (memoryCost ((p d).bind (fun a => q (d, a))) s +
          (workP d s + workQ (d, a) s' + 1) + 1)
    rw [hmP, memoryCost_bind]
    calc
      _ ≤ C * (memoryCost (p d) s + workP d s + 1) +
          C * (memoryCost (q (d, a)) s' + workQ (d, a) s' + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
          (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
      _ = _ := by
        rw [← Nat.mul_add]
        congr 1
        dsimp only [a, s']
        omega
  · rw [hmP] at hmQ
    exact hmQ.trans (by
      simp only [StateTransitionSpec.clientState, StateTransitionSpec.runClient_bind]
      rw [runClient_width w (p d) s])
  · intro i
    have hslot : left (Fin.castAdd (n₂ + 1) i) = Fin.castAdd (N + 1) i := rfl
    rw [hmP] at houtQ
    simpa only [hslot, Function.comp_apply, StateTransitionSpec.clientResult,
      StateTransitionSpec.runClient_bind, runClient_width] using houtQ i
  · intro i hif htmp
    exact (hframeQ i hif (fun j => htmp (left j))).trans
      (hframeP i hif (fun j => htmp (right j)))

end Realizes

end Cslib.WordRAM.Realization
