/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Pointer.Program
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerInput.Setup
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Core
import Complexity.Computability.WordRAM.Call

/-!
# Physical setup before external-pointer gathering

Setup normalizes only the source bank. External physical pointers survive exactly, even above
the virtual modulus. The source layout is executed and translated before the native gather.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The original callable register bank retains its distinct register identities. -/
theorem callableBank_injective : Function.Injective callableBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 173 => k.val) h)

/-- The original source data represented in the native pointer front. -/
@[expose] def view (w b : ℕ) (x : Data 173) : Data 160 :=
  MemoryWindow.view w b (x.comap callableBank)

/-- Reuse the existing single-window compiler, preserving the separate external-pointer bank. -/
theorem exec_source {w W b T : ℕ} {c : Code .standard 160} {v v' : Data 160}
    (he : ExecWithin w c v v' T) (hc : ¬c.ReadsWidth) (hv : v.Bounded w)
    (x : Data 173) (hmatch : MemoryWindow.Matches w b v (x.comap callableBank))
    (hw : w ≤ W) (hfit : Fits W (b + 2 ^ w)) :
    ∃ y, ExecWithin W ((MemoryWindow.compile c).rename callableBank) x y (3 * T) ∧
      MemoryWindow.Matches w b v' (y.comap callableBank) ∧
      (∀ a, a < b ∨ b + 2 ^ w ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin 173, 163 ≤ i.val → y.regs i = x.regs i := by
  obtain ⟨y, hy, ⟨ym, yf⟩, yr⟩ := ExecWithin.rename_post callableBank_injective
    (MemoryWindow.execWithin he hc hv hmatch hw hfit)
  refine ⟨y, hy, ym, yf, ?_⟩
  intro i hi
  apply yr i
  intro j hj
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

private def noStores {r : ℕ} : Code .standard r → Prop
  | .op (.store _ _) => False
  | .op _ => True
  | .seq a b | .branch _ a b => noStores a ∧ noStores b
  | .loop _ a => noStores a
  | .rand _ _ => True

private instance noStores.instDecidable {r : ℕ} : (c : Code .standard r) → Decidable (noStores c)
  | .op (.store _ _) => isFalse id
  | .op (.const _ _) | .op (.copy _ _) | .op (.alu _ _ _) | .op (.load _ _) => isTrue trivial
  | .seq a b | .branch _ a b =>
    have := noStores.instDecidable a
    have := noStores.instDecidable b
    inferInstanceAs (Decidable (noStores a ∧ noStores b))
  | .loop _ a => noStores.instDecidable a
  | .rand _ _ => isTrue trivial

private theorem noStores_mem {r W T : ℕ} {c : Code .standard r} {x y : Data r}
    (he : Exec W c x y T) (hc : noStores c) : y.mem = x.mem := by
  induction he with
  | @op o x y ho =>
    cases o with
    | const d v => obtain ⟨_, rfl⟩ := Data.put_eq_some.1 ho; rfl
    | copy | load => simp only [Op.eval, Option.some.injEq] at ho; cases ho; rfl
    | alu f d args => obtain ⟨v, _, _, rfl⟩ := Op.eval_alu_eq_some.1 ho; rfl
    | store => exact False.elim hc
  | seq h₁ h₂ ih₁ ih₂ => exact (ih₂ hc.2).trans (ih₁ hc.1)
  | branch_pos _ _ ih => exact ih hc.1
  | branch_neg _ _ ih => exact ih hc.2
  | loop_exit => rfl
  | loop_iter _ _ _ ih₁ ih₂ => exact (ih₂ hc).trans (ih₁ hc)

/-- Actual translated setup computes parameters and retains every external physical pointer. -/
theorem exec_setupLayout {W b m t N Q : ℕ} (x : Data 173)
    (hb : x.regs Reg.base = b)
    (hL : x.mem (b + 1) = 21 * m) (hm : x.mem (b + 2) = m)
    (hN : x.mem (b + 3) = N) (hQ : x.mem (b + 4) = Q)
    (ht : x.mem (b + QueriedProduct.inputEnd m N Q) = t)
    (htm : t ≤ m) (hgeom : D m ^ 18 ≤ N)
    (hfit : Fits W (b + 4 * CallableProduct.windowSize N Q + 1024)) :
    ∃ y, ExecWithin W setupLayout x y
        (517 * Nat.clog 2 (N + Q + 3) + 184 + 3 * PointerInput.prefixTime (21 * m)) ∧
      QueriedProduct.Parameters (21 * m) m N Q (view (CallableProduct.sourceWidth N Q) b y) ∧
      (view (CallableProduct.sourceWidth N Q) b y).regs BoxProduct.Reg.threshold = t ∧
      y.regs Reg.base = b ∧
      y.regs (callableBank CallableProduct.Reg.modulus) = CallableProduct.windowSize N Q ∧
      (view (CallableProduct.sourceWidth N Q) b y).Bounded (CallableProduct.sourceWidth N Q) ∧
      y.mem = x.mem ∧
      ∀ i : Fin 173, 163 ≤ i.val → y.regs i = x.regs i := by
  obtain ⟨s, hs, ⟨sm, smatch, sbound⟩, sf⟩ := ExecWithin.rename_post callableBank_injective
    (CallableProduct.exec_setup (x.comap callableBank) hb hN hQ hfit)
  change s.mem = x.mem at sm
  obtain ⟨_, _, hbudget⟩ := CallableBoxProduct.source_admission (Q := Q) htm hgeom
  let v := view (CallableProduct.sourceWidth N Q) b s
  have vread (a : ℕ) (ha : Fits (CallableProduct.sourceWidth N Q) (x.mem (b + a))) :
      v.mem a = x.mem (b + a) := by
    change s.mem (b + a) % _ = _
    rw [sm, Nat.mod_eq_of_lt ha]
  obtain ⟨p, hp, pp, pt, pm⟩ := PointerInput.exec_setupLayout (show m ≤ 21 * m by omega) v
    ((vread 1 (by rw [hL]; exact hbudget.of_le (by
      unfold BoxProduct.wordBudget QueriedProduct.wordBudget; omega))).trans hL)
    ((vread 2 (by rw [hm]; exact hbudget.of_le (by
      unfold BoxProduct.wordBudget QueriedProduct.wordBudget; omega))).trans hm)
    ((vread 3 (by rw [hN]; exact hbudget.of_le (by
      unfold BoxProduct.wordBudget QueriedProduct.wordBudget; omega))).trans hN)
    ((vread 4 (by rw [hQ]; exact hbudget.of_le (by
      unfold BoxProduct.wordBudget QueriedProduct.wordBudget; omega))).trans hQ)
    ((vread _ (by rw [ht]; exact hbudget.of_le (by unfold BoxProduct.wordBudget; omega))).trans ht)
    hbudget
  obtain ⟨y, hy, ym, _, yf⟩ := exec_source hp (by decide) sbound s smatch
    (CallableProduct.setup_fits hfit).1 (hfit.of_le (by
      change b + CallableProduct.windowSize N Q ≤ _; omega))
  have yview : view (CallableProduct.sourceWidth N Q) b y = p := ym.view_eq
  refine ⟨y, hs.seq hy, ?_, ?_, ym.base_eq, ym.modulus_eq, ?_, ?_, ?_⟩
  · rw [yview]; exact pp
  · rw [yview]; exact pt
  · rw [yview]; exact hp.bounded sbound
  · obtain ⟨k, _, he⟩ := hs.seq hy
    exact noStores_mem he (by decide)
  · intro i hi
    exact (yf i hi).trans (sf i (by
      intro j hj
      have hv := congrArg Fin.val hj
      change j.val = i.val at hv
      omega))

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PointerBoxProduct
