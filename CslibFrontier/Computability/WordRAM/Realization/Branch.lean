/-
Copyright (c) 2026 Samuel Schlesinger, Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Witness

/-!
# Native branching in memory-client realizations

The branch test reads only the encoded live words. Both alternatives have uniform emitters;
only the selected alternative's domain, fit obligations and local work are required at runtime.
The two-instruction allowance includes the jump on the negative path.

## Main definitions

* `test`: interpret an existing native condition on a word-vector environment.

## Main results

* `test_rename`: a renamed native condition tests the words in its source registers.
* `Realizes.Witness.branch`: retain a native conditional with one shared temporary bank.
* `Realizes.branch`: erase the supplied branch witness when only existence is needed.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {B : Basis} {δ α : Type} {k l : ℕ}

/-- The existing native condition observes the encoded words, without inspecting memory. -/
def test (c : Cond k) (v : Fin k → ℕ) : Prop := c.Holds ⟨v, fun _ => 0⟩

instance (c : Cond k) (v : Fin k → ℕ) : Decidable (test c v) := by
  unfold test
  infer_instance

/-- A renamed condition holds of native data exactly when it holds of the words in its source
registers. -/
theorem test_rename {r : ℕ} (c : Cond k) (src : Fin k → Fin r)
    (x : Data r) (v : Fin k → ℕ) (h : x.regs ∘ src = v) :
    (c.rename src).Holds x ↔ test c v := by
  cases c <;> simp only [Cond.rename, Cond.Holds, test] <;>
    simp only [← h, Function.comp_apply]

namespace Realizes

/-- Both alternatives reuse the same temporary prefix: only the larger scratch bank is
reserved. The native conditional charges control and requires only the selected domain/work;
the supplied code and resource fields remain data before all runtime values. -/
def Witness.branch {pos neg : δ → Memory.Prog α}
    {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safePos safeNeg : ℕ → δ → Memory.State → Prop}
    {workPos workNeg : δ → Memory.State → ℕ} (c : Cond k)
    (hp : Witness B pos input output safePos workPos)
    (hn : Witness B neg input output safeNeg workNeg) :
    Witness B (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun d s => (if test c (input d) then workPos d s else workNeg d s) + 2) :=
  let np := hp.scratchSize
  let nn := hn.scratchSize
  { scratchSize := max np nn
    factor := max hp.factor hn.factor + 2
    code := fun frontier src tmp =>
      .branch (c.rename src)
        (hp.code frontier src (tmp ∘ Fin.castLE (by omega)))
        (hn.code frontier src (tmp ∘ Fin.castLE (by omega)))
    code_spec := by
      intro r frontier src tmp hi hd hf hs
      let ip : Fin (l + np + 1) → Fin (l + max np nn + 1) := Fin.castLE (by omega)
      let ineg : Fin (l + nn + 1) → Fin (l + max np nn + 1) := Fin.castLE (by omega)
      have hip : Function.Injective (tmp ∘ ip) := by
        intro a b hab
        apply Fin.ext
        exact congrArg (fun z : Fin (l + max np nn + 1) => z.val) (hi hab)
      have hin : Function.Injective (tmp ∘ ineg) := by
        intro a b hab
        apply Fin.ext
        exact congrArg (fun z : Fin (l + max np nn + 1) => z.val) (hi hab)
      obtain ⟨hnp, hrp⟩ := hp.code_spec frontier src (tmp ∘ ip) hip
        (fun i j => hd i (ip j)) (fun j => hf (ip j)) hs
      obtain ⟨hnn, hrn⟩ := hn.code_spec frontier src (tmp ∘ ineg) hin
        (fun i j => hd i (ineg j)) (fun j => hf (ineg j)) hs
      refine ⟨fun h => h.elim hnp hnn, ?_⟩
      intro w d x hx hin hsafe hv
      have hc := test_rename c src x (input d) hin
      by_cases ht : test c (input d)
      · simp only [ite_eq_left ht] at hsafe hv ⊢
        obtain ⟨y, hy, hm, hout, hframe⟩ := hrp w d x hx hin hsafe hv
        refine ⟨y, (hy.branch_pos (hc.mpr ht)).mono ?_, hm, ?_, ?_⟩
        · have hC : hp.factor ≤ max hp.factor hn.factor + 2 := by omega
          have hmul := Nat.mul_le_mul_right
            (memoryCost (pos d) (memoryState frontier x) +
              workPos d (memoryState frontier x) + 1) hC
          calc
            _ ≤ (max hp.factor hn.factor + 2) *
                (memoryCost (pos d) (memoryState frontier x) +
                  workPos d (memoryState frontier x) + 1) + 2 := by omega
            _ ≤ (max hp.factor hn.factor + 2) *
                (memoryCost (pos d) (memoryState frontier x) +
                  workPos d (memoryState frontier x) + 1) +
                  (max hp.factor hn.factor + 2) * 2 := by omega
            _ = _ := by ring
        · intro i
          have heq : Fin.castAdd (max np nn + 1) i = ip (Fin.castAdd (np + 1) i) := Fin.ext rfl
          rw [heq]
          exact hout i
        · intro i hif htmp
          exact hframe i hif (fun j => htmp (ip j))
      · simp only [ite_eq_right ht] at hsafe hv ⊢
        obtain ⟨y, hy, hm, hout, hframe⟩ := hrn w d x hx hin hsafe hv
        refine ⟨y, (hy.branch_neg (fun h => ht (hc.mp h))).mono ?_, hm, ?_, ?_⟩
        · have hC : hn.factor ≤ max hp.factor hn.factor + 2 := by omega
          have hmul := Nat.mul_le_mul_right
            (memoryCost (neg d) (memoryState frontier x) +
              workNeg d (memoryState frontier x) + 1) hC
          calc
            _ ≤ (max hp.factor hn.factor + 2) *
                (memoryCost (neg d) (memoryState frontier x) +
                  workNeg d (memoryState frontier x) + 1) + 2 := by omega
            _ ≤ (max hp.factor hn.factor + 2) *
                (memoryCost (neg d) (memoryState frontier x) +
                  workNeg d (memoryState frontier x) + 1) +
                  (max hp.factor hn.factor + 2) * 2 := by omega
            _ = _ := by ring
        · intro i
          have heq : Fin.castAdd (max np nn + 1) i = ineg (Fin.castAdd (nn + 1) i) := Fin.ext rfl
          rw [heq]
          exact hout i
        · intro i hif htmp
          exact hframe i hif (fun j => htmp (ineg j))
  }

/-- Both branch emitters precede all runtime values. Shared result slots and disjointness from
live inputs are synthesized internally; the entry domain and work charge select the actual path. -/
theorem branch {pos neg : δ → Memory.Prog α}
    {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safePos safeNeg : ℕ → δ → Memory.State → Prop}
    {workPos workNeg : δ → Memory.State → ℕ} (c : Cond k)
    (hp : Realizes B pos input output safePos workPos)
    (hn : Realizes B neg input output safeNeg workNeg) :
    Realizes B (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun d s => (if test c (input d) then workPos d s else workNeg d s) + 2) :=
  (Witness.branch c (Witness.ofRealizes hp) (Witness.ofRealizes hn)).toRealizes

end Realizes

namespace RealizesBounded

/-- Frontier-bounded conditional realization. -/
theorem branch {pos neg : δ → Memory.Prog α}
    {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safePos safeNeg : ℕ → δ → Memory.State → Prop}
    {workPos workNeg : δ → Memory.State → ℕ} (c : Cond k)
    (hp : RealizesBounded B pos input output safePos workPos)
    (hn : RealizesBounded B neg input output safeNeg workNeg) :
    RealizesBounded B (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun d s => (if test c (input d) then workPos d s else workNeg d s) + 2) := by
  obtain ⟨np, Cp, emitP, hsp⟩ := hp
  obtain ⟨nn, Cn, emitN, hsn⟩ := hn
  refine ⟨max np nn, max Cp Cn + 2, fun frontier src tmp =>
    .branch (c.rename src)
      (emitP frontier src (tmp ∘ Fin.castLE (by omega)))
      (emitN frontier src (tmp ∘ Fin.castLE (by omega))), ?_⟩
  intro r frontier src tmp hi hd hf hs
  let ip : Fin (l + np + 1) → Fin (l + max np nn + 1) := Fin.castLE (by omega)
  let ineg : Fin (l + nn + 1) → Fin (l + max np nn + 1) := Fin.castLE (by omega)
  have hip : Function.Injective (tmp ∘ ip) := fun a b hab =>
    Fin.ext (congrArg (fun z : Fin (l + max np nn + 1) => z.val) (hi hab))
  have hin : Function.Injective (tmp ∘ ineg) := fun a b hab =>
    Fin.ext (congrArg (fun z : Fin (l + max np nn + 1) => z.val) (hi hab))
  obtain ⟨hnp, hrp⟩ := hsp frontier src (tmp ∘ ip) hip
    (fun i j => hd i (ip j)) (fun j => hf (ip j)) hs
  obtain ⟨hnn, hrn⟩ := hsn frontier src (tmp ∘ ineg) hin
    (fun i j => hd i (ineg j)) (fun j => hf (ineg j)) hs
  refine ⟨fun h => h.elim hnp hnn, fun w d x hx hin' hsafe hv => ?_⟩
  have hc := test_rename c src x (input d) hin'
  by_cases ht : test c (input d)
  · simp only [ite_eq_left ht] at hsafe hv ⊢
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrp w d x hx hin' hsafe hv
    refine ⟨y, (ExecBounded.branch_pos (hc.mpr ht) hy).mono ?_, hm, ?_,
      fun i hif htmp => hframe i hif (fun j => htmp (ip j))⟩
    · have hC : Cp ≤ max Cp Cn + 2 := by omega
      have hmul := Nat.mul_le_mul_right
        (memoryCost (pos d) (memoryState frontier x) +
          workPos d (memoryState frontier x) + 1) hC
      calc
        _ ≤ (max Cp Cn + 2) *
            (memoryCost (pos d) (memoryState frontier x) +
              workPos d (memoryState frontier x) + 1) + 2 := by omega
        _ ≤ (max Cp Cn + 2) *
            (memoryCost (pos d) (memoryState frontier x) +
              workPos d (memoryState frontier x) + 1) +
              (max Cp Cn + 2) * 2 := by omega
        _ = _ := by ring
    · intro i
      exact hout i
  · simp only [ite_eq_right ht] at hsafe hv ⊢
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrn w d x hx hin' hsafe hv
    refine ⟨y, (ExecBounded.branch_neg (fun h => ht (hc.mp h)) hy).mono ?_, hm, ?_,
      fun i hif htmp => hframe i hif (fun j => htmp (ineg j))⟩
    · have hC : Cn ≤ max Cp Cn + 2 := by omega
      have hmul := Nat.mul_le_mul_right
        (memoryCost (neg d) (memoryState frontier x) +
          workNeg d (memoryState frontier x) + 1) hC
      calc
        _ ≤ (max Cp Cn + 2) *
            (memoryCost (neg d) (memoryState frontier x) +
              workNeg d (memoryState frontier x) + 1) + 2 := by omega
        _ ≤ (max Cp Cn + 2) *
            (memoryCost (neg d) (memoryState frontier x) +
              workNeg d (memoryState frontier x) + 1) +
              (max Cp Cn + 2) * 2 := by omega
        _ = _ := by ring
    · intro i
      exact hout i

/-- Frontier-bounded branching with the test and jump absorbed (`work = 0`). -/
theorem branch₀ {B : Basis} {δ α : Type} {k l : ℕ}
    {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {pos neg : δ → Memory.Prog α} {safePos safeNeg : ℕ → δ → Memory.State → Prop}
    (c : Cond k) (hp : RealizesBounded B pos input output safePos (fun _ _ => 0))
    (hn : RealizesBounded B neg input output safeNeg (fun _ _ => 0)) :
    RealizesBounded B (fun d => if test c (input d) then pos d else neg d) input output
      (fun w d s => if test c (input d) then safePos w d s else safeNeg w d s)
      (fun _ _ => 0) :=
  (branch c hp hn).mono_mul 2 (fun _ _ => by split <;> omega)

end RealizesBounded

end Cslib.WordRAM.Realization
