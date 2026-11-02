/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Branch
public import Complexity.Computability.WordRAM.Realization.Witness
public import Complexity.DataStructure.Memory.Frame

/-!
# Uniform dispatch for products over shared memory

A product specification dispatches over a sum of operations. `Realizes.sum` combines two
certified families using one native conditional and static input-coordinate maps. The common
faithful result encoding is explicit; operation-dependent observation remains the existing
module adapter's responsibility. The conditional's two-instruction allowance is local work.

The emitter and its scratch size and exchange constant precede every runtime input, word width
and layout. Only the selected component's safety and work are needed. The kernel still represents
the literal whole memory and frontier. Shared-memory product and allocator invariants remain the
existing `Memory.Framed.prod` and `Memory.Allocator.prod` contracts, with state-dependent
footprints, resident ownership and reserved room; this module introduces no replacement model.

## Main results

* `Realizes.sum`: charged native dispatch over a sum of encoded inputs.
* `Realizes.product_exec`: whole-memory native execution and a block frame, under explicit
  containment of the dynamic product footprint and reserved future region.

## References

This is original realization infrastructure over the existing product specifications and
shared-memory framing/allocator contracts. It supplies no automatic native bound for an opaque
client or uncharged initialization.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

private theorem holds_rename_iff {r k : ℕ} (c : Cond k) (src : Fin k → Fin r)
    (x : Data r) (v : Fin k → ℕ) (h : x.regs ∘ src = v) :
    (c.rename src).Holds x ↔ test c v := by
  cases c <;> simp only [Cond.rename, Cond.Holds, test] <;>
    simp only [← h, Function.comp_apply]

namespace Realizes

/-- Combine uniformly realized components by a real native branch. The supplied sum encoding
and coordinate maps account for all input words; the condition must select the corresponding
summand. No default input for the unselected side, host-side dispatch or free glue is used. -/
theorem sum {B : Basis} {δ₁ δ₂ α : Type} {k k₁ k₂ l : ℕ}
    {p₁ : δ₁ → Memory.Prog α} {p₂ : δ₂ → Memory.Prog α}
    {input₁ : δ₁ ↪ (Fin k₁ → ℕ)} {input₂ : δ₂ ↪ (Fin k₂ → ℕ)}
    {output : α ↪ (Fin l → ℕ)}
    {safe₁ : ℕ → δ₁ → Memory.State → Prop} {safe₂ : ℕ → δ₂ → Memory.State → Prop}
    {work₁ : δ₁ → Memory.State → ℕ} {work₂ : δ₂ → Memory.State → ℕ}
    (h₁ : Realizes B p₁ input₁ output safe₁ work₁)
    (h₂ : Realizes B p₂ input₂ output safe₂ work₂)
    (input : δ₁ ⊕ δ₂ ↪ (Fin k → ℕ)) (ix₁ : Fin k₁ → Fin k) (ix₂ : Fin k₂ → Fin k)
    (route₁ : ∀ d i, input₁ d i = input (.inl d) (ix₁ i))
    (route₂ : ∀ d i, input₂ d i = input (.inr d) (ix₂ i))
    (c : Cond k) (left : ∀ d, test c (input (.inl d)))
    (right : ∀ d, ¬test c (input (.inr d))) :
    Realizes B (Sum.elim p₁ p₂) input output
      (fun w d s => d.elim (fun a => safe₁ w a s) (fun b => safe₂ w b s))
      (fun d s => d.elim (fun a => work₁ a s) (fun b => work₂ b s) + 2) := by
  obtain ⟨n₁, C₁, e₁, he₁⟩ := h₁
  obtain ⟨n₂, C₂, e₂, he₂⟩ := h₂
  let i₁ : Fin (l + n₁ + 1) → Fin (l + (n₁ + n₂) + 1) := Fin.castLE (by omega)
  let i₂ : Fin (l + n₂ + 1) → Fin (l + (n₁ + n₂) + 1) := Fin.castLE (by omega)
  refine ⟨n₁ + n₂, max C₁ C₂ + 2, fun frontier src tmp =>
    .branch (c.rename src) (e₁ frontier (src ∘ ix₁) (tmp ∘ i₁))
      (e₂ frontier (src ∘ ix₂) (tmp ∘ i₂)), ?_⟩
  intro r frontier src tmp hi hd hf hs
  have hi₁ : Function.Injective (tmp ∘ i₁) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Fin (l + (n₁ + n₂) + 1) => z.val) (hi hab)
  have hi₂ : Function.Injective (tmp ∘ i₂) := by
    intro a b hab
    apply Fin.ext
    exact congrArg (fun z : Fin (l + (n₁ + n₂) + 1) => z.val) (hi hab)
  obtain ⟨hn₁, hr₁⟩ := he₁ frontier (src ∘ ix₁) (tmp ∘ i₁) hi₁
    (fun i j => hd (ix₁ i) (i₁ j)) (fun j => hf (i₁ j)) (fun i => hs (ix₁ i))
  obtain ⟨hn₂, hr₂⟩ := he₂ frontier (src ∘ ix₂) (tmp ∘ i₂) hi₂
    (fun i j => hd (ix₂ i) (i₂ j)) (fun j => hf (i₂ j)) (fun i => hs (ix₂ i))
  refine ⟨fun h => h.elim hn₁ hn₂, ?_⟩
  intro w d x hx hin hsafe hv
  have hc := holds_rename_iff c src x (input d) hin
  cases d with
  | inl a =>
    have hin₁ : x.regs ∘ (src ∘ ix₁) = input₁ a := by
      funext i
      exact (congrFun hin (ix₁ i)).trans (route₁ a i).symm
    obtain ⟨y, hy, hm, hout, hframe⟩ := hr₁ w a x hx hin₁ hsafe hv
    refine ⟨y, (hy.branch_pos (hc.mpr (left a))).mono ?_, hm, ?_, ?_⟩
    · have hC : C₁ ≤ max C₁ C₂ + 2 := by omega
      have hmul := Nat.mul_le_mul_right
        (memoryCost (p₁ a) (memoryState frontier x) + work₁ a (memoryState frontier x) + 1) hC
      calc
        _ ≤ (max C₁ C₂ + 2) *
            (memoryCost (p₁ a) (memoryState frontier x) + work₁ a (memoryState frontier x) + 1) +
              (max C₁ C₂ + 2) * 2 := by omega
        _ = _ := by simp only [Sum.elim_inl]; ring
    · intro i
      have heq : Fin.castAdd (n₁ + n₂ + 1) i = i₁ (Fin.castAdd (n₁ + 1) i) := Fin.ext rfl
      rw [heq]
      exact hout i
    · intro i hif htmp
      exact hframe i hif (fun j => htmp (i₁ j))
  | inr b =>
    have hin₂ : x.regs ∘ (src ∘ ix₂) = input₂ b := by
      funext i
      exact (congrFun hin (ix₂ i)).trans (route₂ b i).symm
    obtain ⟨y, hy, hm, hout, hframe⟩ := hr₂ w b x hx hin₂ hsafe hv
    refine ⟨y, (hy.branch_neg (fun h => right b (hc.mp h))).mono ?_, hm, ?_, ?_⟩
    · have hC : C₂ ≤ max C₁ C₂ + 2 := by omega
      have hmul := Nat.mul_le_mul_right
        (memoryCost (p₂ b) (memoryState frontier x) + work₂ b (memoryState frontier x) + 1) hC
      calc
        _ ≤ (max C₁ C₂ + 2) *
            (memoryCost (p₂ b) (memoryState frontier x) + work₂ b (memoryState frontier x) + 1) +
              (max C₁ C₂ + 2) * 2 := by omega
        _ = _ := by simp only [Sum.elim_inr]; ring
    · intro i
      have heq : Fin.castAdd (n₁ + n₂ + 1) i = i₂ (Fin.castAdd (n₂ + 1) i) := Fin.ext rfl
      rw [heq]
      exact hout i
    · intro i hif htmp
      exact hframe i hif (fun j => htmp (i₂ j))

/-- A certified product method preserves a reserved native block. The block must contain both
its current state-dependent footprint and every cell its shared room permits it to allocate.
The observation equation is the existing semantic correspondence; it adds no executable work.
All native work comes from `h`, including any glue already present in `p`.

This is a native execution/frame theorem for the represented method. It does not construct a
`StateTransitionImpl`, a decoder, argument installation or an arbitrary-client clock. -/
theorem product_exec {B : Basis} {δ α : Type} {r k l w : ℕ}
    {D₁ D₂ : StateTransitionSpec.{0, 0, 0}}
    (M₁ : Memory.Framed D₁ w) (M₂ : Memory.Framed D₂ w)
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}
    (h : Realizes B p input output safe work)
    (frontier : Fin r) (src : Fin k → Fin r) (tmp : Fin (l + h.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    (d : δ) (x : Data r) (o : (product D₁ D₂).Op) (answer : α → (product D₁ D₂).Result o)
    (source : (p d).bind (fun a => pure (answer a)) = (M₁.prod M₂).methods o)
    (hx : x.Bounded w) (hin : x.regs ∘ src = input d)
    (hsafe : safe w d (memoryState frontier x))
    (hinv : (M₁.prod M₂).inv (memoryState frontier x))
    (hvalid : (product D₁ D₂).valid ((M₁.prod M₂).abs (memoryState frontier x)) o)
    (region : Block)
    (hfootprint : ∀ a ∈ (M₁.prod M₂).footprint (memoryState frontier x), a ∈ region.footprint)
    (hroom : ∀ a, (memoryState frontier x).frontier ≤ a →
      a < (memoryState frontier x).frontier + (M₁.prod M₂).room (memoryState frontier x) →
      a ∈ region.footprint) :
    ∃ y, ExecWithin w (h.code frontier src tmp) x y
          (h.factor * (memoryCost (p d) (memoryState frontier x) +
            work d (memoryState frontier x) + 1)) ∧
      memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (p d) ∧
      (M₁.prod M₂).inv (memoryState frontier y) ∧
      (product D₁ D₂).step ((M₁.prod M₂).abs (memoryState frontier x)) o
        ((M₁.prod M₂).abs (memoryState frontier y))
        (answer ((Memory.spec w).clientResult (memoryState frontier x) (p d))) ∧
      Modifies region.footprint x.mem y.mem ∧
      (M₁.prod M₂).footprint (memoryState frontier y) ⊆ region.footprint ∧
      (memoryState frontier y).frontier + (M₁.prod M₂).room (memoryState frontier y) ≤
        (memoryState frontier x).frontier + (M₁.prod M₂).room (memoryState frontier x) ∧
      (∀ i : Fin l, y.regs (tmp (Fin.castAdd (h.scratchSize + 1) i)) =
        output ((Memory.spec w).clientResult (memoryState frontier x) (p d)) i) ∧
      ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i := by
  let F := M₁.prod M₂
  let s := memoryState frontier x
  have hresult : (Memory.spec w).clientResult s (F.methods o) =
      answer ((Memory.spec w).clientResult s (p d)) := by
    rw [← source]
    change (Memory.spec w).clientResult s (p d >>= fun a => pure (answer a)) = _
    rw [StateTransitionSpec.clientResult_bind]
    rfl
  have hstate : (Memory.spec w).clientState s (F.methods o) =
      (Memory.spec w).clientState s (p d) := by
    rw [← source]
    change (Memory.spec w).clientState s (p d >>= fun a => pure (answer a)) = _
    rw [StateTransitionSpec.clientState_bind]
    rfl
  have hhistory : (Memory.spec w).clientHistory s (F.methods o) =
      (Memory.spec w).clientHistory s (p d) := by
    rw [← source]
    change (Memory.spec w).clientHistory s (p d >>= fun a => pure (answer a)) = _
    rw [StateTransitionSpec.clientHistory_bind]
    exact List.append_nil _
  have hvF := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
    (F.valid o hinv hvalid)
  have hvp : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) :=
    hhistory ▸ hvF
  obtain ⟨y, hy, hm, hout, hframe⟩ :=
    (h.code_spec frontier src tmp hi hd hf hs).2 w d x hx hin hsafe hvp
  have hcanon := (Memory.spec w).clientRun_canonical s (F.methods o) hvF
  obtain ⟨hstep, hinv'⟩ := F.correct o hinv hvalid hcanon
  obtain ⟨houtside, hgrow, hbudget⟩ := F.modifies o hinv hvalid hcanon
  have hfinal : (Memory.spec w).clientState s (F.methods o) = memoryState frontier y :=
    hstate.trans hm.symm
  rw [hfinal] at hstep hinv' houtside hgrow hbudget
  rw [hresult] at hstep
  change (memoryState frontier y).frontier + F.room (memoryState frontier y) ≤
    s.frontier + F.room s at hbudget
  have hfront : (memoryState frontier y).frontier ≤ s.frontier + F.room s := by omega
  have habove : ∀ a, (memoryState frontier y).frontier ≤ a → y.mem a = x.mem a := by
    intro a ha
    have h := Memory.mem_clientState_of_frontier_le s (F.methods o) hvF (a := a)
    rw [hfinal] at h
    exact h ha
  have hmod : Modifies region.footprint x.mem y.mem := by
    intro a ha
    by_cases hlt : a < s.frontier
    · exact houtside a hlt (fun hm => ha (hfootprint a hm))
    · have hbound : (memoryState frontier y).frontier ≤ a := by
        by_contra! h
        exact ha (hroom a (Nat.le_of_not_gt hlt) (h.trans_le hfront))
      exact habove a hbound
  have hcontained : F.footprint (memoryState frontier y) ⊆ region.footprint := by
    intro a ha
    rcases hgrow a ha with h | h
    · exact hfootprint a h
    · exact hroom a h ((F.lt_frontier hinv' ha).trans_le hfront)
  exact ⟨y, hy, hm, hinv', hstep, hmod, hcontained, hbudget, hout, hframe⟩

end Realizes

end Cslib.WordRAM.Realization
