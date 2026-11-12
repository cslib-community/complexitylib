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
* `branchPrefix_layout`, `branch_cost_le`: prefix-bank layout, frame weakening and cost relaxation.
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

/-- Restricting a temporary bank `tmp` to a prefix `Fin.castLE h` preserves injectivity and
disjointness from `src` and `frontier`, and weakens a prefix frame to a frame on `tmp`. -/
theorem branchPrefix_layout {r k m M : ℕ} {frontier : Fin r} {src : Fin k → Fin r}
    {tmp : Fin M → Fin r} (h : m ≤ M) (hi : Function.Injective tmp)
    (hd : ∀ i j, src i ≠ tmp j) (hf : ∀ j, tmp j ≠ frontier) :
    Function.Injective (tmp ∘ Fin.castLE h) ∧
      (∀ i j, src i ≠ (tmp ∘ Fin.castLE h) j) ∧
      (∀ j, (tmp ∘ Fin.castLE h) j ≠ frontier) ∧
      ∀ {x y : Data r},
        (∀ i, i ≠ frontier → (∀ j, (tmp ∘ Fin.castLE h) j ≠ i) → y.regs i = x.regs i) →
        ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i :=
  ⟨hi.comp (Fin.castLE_injective h), fun i j => hd i (Fin.castLE h j),
    fun j => hf (Fin.castLE h j), fun hframe i hif htmp => hframe i hif fun _ => htmp _⟩

/-- Relax a branch alternative's cost `C * (t + 1) + e` (with `e ≤ 2` control steps) under
`max Cp Cn + 2` and an enlarged work bound `t ≤ t'`. -/
theorem branch_cost_le {C Cp Cn t t' e : ℕ} (hC : C ≤ max Cp Cn) (ht : t ≤ t') (he : e ≤ 2) :
    C * (t + 1) + e ≤ (max Cp Cn + 2) * (t' + 1) := by
  have := Nat.mul_le_mul hC (Nat.add_le_add_right ht 1)
  nlinarith

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
      obtain ⟨hip, hdp, hfp, hframep⟩ := branchPrefix_layout (m := l + np + 1) (by omega) hi hd hf
      obtain ⟨hin, hdn, hfn, hframen⟩ := branchPrefix_layout (m := l + nn + 1) (by omega) hi hd hf
      obtain ⟨hnp, hrp⟩ := hp.code_spec frontier src (tmp ∘ ip) hip hdp hfp hs
      obtain ⟨hnn, hrn⟩ := hn.code_spec frontier src (tmp ∘ ineg) hin hdn hfn hs
      refine ⟨fun h => h.elim hnp hnn, fun w d x hx hin' hsafe hv => ?_⟩
      have hc := test_rename c src x (input d) hin'
      by_cases ht : test c (input d)
      · simp only [ite_eq_left ht] at hsafe hv ⊢
        obtain ⟨y, hy, hm, hout, hframe⟩ := hrp w d x hx hin' hsafe hv
        exact ⟨y, (hy.branch_pos (hc.mpr ht)).mono
          (branch_cost_le (Nat.le_max_left _ _) (by omega) (by omega)), hm, hout, hframep hframe⟩
      · simp only [ite_eq_right ht] at hsafe hv ⊢
        obtain ⟨y, hy, hm, hout, hframe⟩ := hrn w d x hx hin' hsafe hv
        exact ⟨y, (hy.branch_neg (fun h => ht (hc.mp h))).mono
          (branch_cost_le (Nat.le_max_right _ _) (by omega) le_rfl), hm, hout, hframen hframe⟩
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
  obtain ⟨hip, hdp, hfp, hframep⟩ := branchPrefix_layout (m := l + np + 1) (by omega) hi hd hf
  obtain ⟨hin, hdn, hfn, hframen⟩ := branchPrefix_layout (m := l + nn + 1) (by omega) hi hd hf
  obtain ⟨hnp, hrp⟩ := hsp frontier src (tmp ∘ ip) hip hdp hfp hs
  obtain ⟨hnn, hrn⟩ := hsn frontier src (tmp ∘ ineg) hin hdn hfn hs
  refine ⟨fun h => h.elim hnp hnn, fun w d x hx hin' hsafe hv => ?_⟩
  have hc := test_rename c src x (input d) hin'
  by_cases ht : test c (input d)
  · simp only [ite_eq_left ht] at hsafe hv ⊢
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrp w d x hx hin' hsafe hv
    exact ⟨y, (ExecBounded.branch_pos (hc.mpr ht) hy).mono
      (branch_cost_le (Nat.le_max_left _ _) (by omega) (by omega)), hm, hout, hframep hframe⟩
  · simp only [ite_eq_right ht] at hsafe hv ⊢
    obtain ⟨y, hy, hm, hout, hframe⟩ := hrn w d x hx hin' hsafe hv
    exact ⟨y, (ExecBounded.branch_neg (fun h => ht (hc.mp h)) hy).mono
      (branch_cost_le (Nat.le_max_right _ _) (by omega) le_rfl), hm, hout, hframen hframe⟩

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
