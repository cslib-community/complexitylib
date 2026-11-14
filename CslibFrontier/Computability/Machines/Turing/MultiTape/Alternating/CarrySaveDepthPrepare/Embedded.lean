/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarrySaveDepthPrepare

/-!
# Depth preparation beside a protected evaluator

The depth machine uses a blank scratch prefix and the first twelve tapes of a protected block.
Its binary count is already in that block. The native run writes the binary and unary depth words,
preserving every other word, including the two trailing source and marker tapes. Reindexing the
checked preparation does not add time or rescan the potentially long predicate context.
-/

public noncomputable section

namespace Turing.MultiTapeATM.CarrySaveDepthPrepare.Embedded

open MultiTapeTM

/-- The first twelve protected evaluator tapes follow the scratch prefix. -/
@[expose] def coreTapes (scratch size : ℕ) (hsize : 12 ≤ size) :
    Fin 12 ↪ Fin (scratch + size + 2) where
  toFun i := ⟨scratch + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change scratch + i.val = scratch + j.val at hv
    omega

/-- A core coordinate is shifted only by the scratch prefix. -/
@[simp] theorem coreTapes_val (scratch size : ℕ) (hsize : 12 ≤ size) (i : Fin 12) :
    (coreTapes scratch size hsize i).val = scratch + i.val := rfl

/-- Depth preparation reuses the scratch prefix and only the twelve protected core tapes. -/
def embedding (k scratch size : ℕ) (hk : k ≤ scratch) (hsize : 12 ≤ size) :
    Fin (k + 12) ↪ Fin (scratch + size + 2) where
  toFun i := ⟨if i.val < 12 then scratch + i.val else i.val - 12, by
    have := i.isLt
    split_ifs <;> omega⟩
  inj' := by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    have hv := congrArg Fin.val h
    change (if i.val < 12 then scratch + i.val else i.val - 12) =
      (if j.val < 12 then scratch + j.val else j.val - 12) at hv
    apply Fin.ext
    split_ifs at hv <;> omega

/-- Core coordinates keep their indices inside the protected evaluator block. -/
@[simp] theorem embedding_core (k scratch size : ℕ) (hk : k ≤ scratch) (hsize : 12 ≤ size)
    (i : Fin 12) :
    embedding k scratch size hk hsize (Fin.castLE (by omega) i) =
      coreTapes scratch size hsize i := by
  apply Fin.ext
  change (if i.val < 12 then scratch + i.val else i.val - 12) = scratch + i.val
  simp [i.isLt]

/-- Every private depth tape lies in the reusable scratch prefix. -/
theorem embedding_private (k scratch size : ℕ) (hk : k ≤ scratch) (hsize : 12 ≤ size)
    (i : Fin (k + 12)) (hi : 12 ≤ i.val) :
    (embedding k scratch size hk hsize i).val < scratch := by
  have := i.isLt
  change (if i.val < 12 then scratch + i.val else i.val - 12) < scratch
  rw [ite_eq_right (Nat.not_lt.mpr hi)]
  omega

/-- One uniform depth machine fits beside any larger protected evaluator. Only its two depth
words change; the shared scratch, all other protected words and both trailing tapes survive. -/
theorem exists_prepare :
    ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM (k + 12) Bool S) (c d : ℕ),
      ∀ (scratch size : ℕ) (hk : k ≤ scratch) (hsize : 12 ≤ size)
        (input : List Bool) (n : ℕ) (words : Fin (scratch + size + 2) → List Bool)
        (out : List Bool),
        words (coreTapes scratch size hsize 7) = encNat n →
        words (coreTapes scratch size hsize 0) = [] →
        words (coreTapes scratch size hsize 4) = [] →
        (∀ i, i.val < scratch → words i = []) →
        RunsBetween (input := input) (tm.extendTapes (embedding k scratch size hk hsize))
          { tapesCfg input words 0 0 out with inputPos := 0 }
          { tapesCfg input
              (Function.update
                (Function.update words (coreTapes scratch size hsize 0) (encNat (Nat.clog 2 n)))
                (coreTapes scratch size hsize 4) (encUnary (Nat.clog 2 n)))
              0 0 out with inputPos := 0 }
          (c * ((encNat n).length + 1) ^ d)
          ((scratch + size + 2) * (c * ((encNat n).length + 1) ^ d + 1)) := by
  obtain ⟨k, S, hS, tm, c, d, htm⟩ := CarrySaveDepthPrepare.exists_prepare
  refine ⟨k, S, hS, tm, c, d, ?_⟩
  intro scratch size hk hsize input n words out hcount hheight hfront hblank
  let e := embedding k scratch size hk hsize
  have hcore (i : Fin 12) : e (Fin.castLE (by omega) i) = coreTapes scratch size hsize i :=
    embedding_core k scratch size hk hsize i
  have h0 : e 0 = coreTapes scratch size hsize 0 := hcore 0
  have h4 : e 4 = coreTapes scratch size hsize 4 := hcore 4
  have h7 : e 7 = coreTapes scratch size hsize 7 := hcore 7
  have hr := htm input n (fun i => words (e i)) out
    (by simpa only [h7] using hcount) (by simpa only [h0] using hheight)
    (by simpa only [h4] using hfront)
    (fun i hi => hblank _ (embedding_private k scratch size hk hsize i hi))
  apply RunsBetween.of_runFrom
  rw [runFrom_extendTapes]
  change embed e (tm.runFrom
    ((CarrySaveDepthPrepare.config input (fun i => words (e i)) out).withState (some tm.q₀))
      (c * ((encNat n).length + 1) ^ d)) _ _ = _
  rw [hr]
  have ht := embed_tapesCfg (input := input) (e := e)
    (v := Function.update (Function.update (fun i => words (e i)) 0
      (encNat (Nat.clog 2 n))) 4 (encUnary (Nat.clog 2 n)))
    (ws := words)
    (ws' := Function.update (Function.update words (e 0) (encNat (Nat.clog 2 n)))
      (e 4) (encUnary (Nat.clog 2 n)))
    (ov := 0) (hv := 0) (o := 0) (h := 0) (o' := 0) (h' := 0) (out := out)
    (fun i => ⟨by simp [Function.update_apply, e.injective.eq_iff], rfl, rfl⟩)
    (fun i hi => ⟨by
      have hne (j) : i ≠ e j := fun h => hi ⟨j, h.symm⟩
      simp [Function.update_of_ne (hne 0), Function.update_of_ne (hne 4)], rfl, rfl⟩)
  have ht' := congrArg (fun cfg : Cfg (scratch + size + 2) Bool Unit input =>
    ({ cfg with inputPos := 0 } : Cfg (scratch + size + 2) Bool Unit input).withState
      (none : Option S)) ht
  simpa only [h0, h4, CarrySaveDepthPrepare.config, embed, Cfg.withState] using ht'

end Turing.MultiTapeATM.CarrySaveDepthPrepare.Embedded
