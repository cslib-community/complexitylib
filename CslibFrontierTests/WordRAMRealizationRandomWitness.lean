/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.Realization.Random
import CslibFrontier.Computability.WordRAM.Realization.Primitive
import CslibFrontier.Probability.PMF.Uniform

/-!
A supplied coin is written to memory and read back. Its returned word and final memory cell
are correlated under a genuinely nondegenerate law. The explicit body has six registers rather
than the disjoint bind's seven, and no randomized Backend or new execution model is used.
Native bounds here count the body; argument installation and halt are separate.
-/

namespace CslibFrontierTests.WordRAMRealizationRandomWitness

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

private def word : ℕ ↪ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
private def unitWords : Unit ↪ (Fin 0 → ℕ) :=
  (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
private def inputs := appendWords word word
private def withReply := appendWords inputs word

private def storeRead :=
  (Realizes.writeWitness (B := .exact) withReply 1 2).bind
    (Realizes.readWitness (appendWords withReply unitWords) 1)

private def supplied :=
  (RealizesRand.coinWitness (B := .exact) inputs 0).bind storeRead.toRand
    (fun _ _ => 3) (fun _ _ => 0)

private noncomputable def experiment (d : ℕ × ℕ) : ProbOracleComp Memory.Op.Result ℕ := do
  let r ← Fin.val <$> ProbOracleComp.sample (ProbComp.unifFin d.1)
  OracleComp.liftRight (do
    Memory.write d.2 r
    Memory.read d.2)

-- Supplied data retains the actual bank and factor, rather than choosing them from a Prop.
example : supplied.scratchSize = 1 ∧ supplied.factor = 1 := ⟨rfl, rfl⟩

example : 2 + (1 + supplied.scratchSize + 1) + 1 = 6 ∧
    2 + (1 + (0 + 1 + 0 + 1) + 1) + 1 = 7 := by decide

private def fr : Fin 6 := 0
private def src : Fin 2 → Fin 6 := fun i => ⟨i.val + 1, by omega⟩
private def tmp : Fin 3 → Fin 6 := fun i => ⟨3 + i.val, by omega⟩

-- The same fixed body samples once, stores that very reply and reads the stored word.
example : supplied.code fr src tmp =
    .seq (.rand 5 1) (.seq (.op (.store 2 5)) (.op (.load 3 2))) := rfl

private theorem run_experiment (w : ℕ) (d : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec w).toRandomized.withCoins.run (experiment d) s =
      (Probability.PMF.uniformOfFintype (Fin (d.1 + 1))).map
        (fun r => (r.val, (⟨Function.update s.mem d.2 r.val, s.frontier⟩ : Memory.State))) := by
  rw [experiment, RandomizedSpec.run_bind, RandomizedSpec.run_map,
    RandomizedSpec.withCoins_run_sample, ProbComp.eval_unifFin,
    PMF.map_comp, PMF.bind_map, ← PMF.bind_pure_comp]
  congr 1
  funext r
  simp only [Function.comp_apply]
  rw [RandomizedSpec.withCoins_run_liftRight, StateTransitionSpec.run_toRandomized]
  simp [Function.update_self]

private theorem admissible {w : ℕ} {d : ℕ × ℕ} {s : Memory.State}
    (hfit : Fits w d.1) (haddr : d.2 < s.frontier) :
    (Memory.spec w).toRandomized.withCoins.toSpec.DemonicValid s (experiment d) := by
  unfold experiment
  rw [bind_map_left]
  refine RandomizedSpec.demonicValid_sample_bind fun r => ?_
  apply RandomizedSpec.demonicValid_liftRight
  apply StateTransitionSpec.toRandomized_demonicValid_of_validHistory
  change (d.2 < s.frontier ∧ Fits w r.val) ∧ d.2 < s.frontier ∧ True
  exact ⟨⟨haddr, hfit.of_le (by have := r.isLt; omega)⟩, haddr, trivial⟩

private def initial (frontier upper address : ℕ) (mem : ℕ → ℕ) : Data 6 :=
  ⟨![frontier, upper, address, 0, 0, 0], mem⟩

private theorem native (w frontier upper address : ℕ) (mem : ℕ → ℕ)
    (hb : (initial frontier upper address mem).Bounded w) (ha : address < frontier) :
    ExecRandLaw w (supplied.code fr src tmp) (initial frontier upper address mem)
      (fun y => ∀ i, i ≠ fr → (∀ j, tmp j ≠ i) →
        y.regs i = (initial frontier upper address mem).regs i)
      6 1 (fun y => (y.regs 3, memoryState fr y))
      ((Probability.PMF.uniformOfFintype (Fin (upper + 1))).map
        fun r => (r.val, (⟨Function.update mem address r.val, frontier⟩ : Memory.State))) := by
  have hi : Function.Injective tmp := by
    intro a b h
    apply Fin.ext
    have h' := congrArg Fin.val h
    change 3 + a.val = 3 + b.val at h'
    omega
  have hd (i : Fin 2) (j : Fin 3) : src i ≠ tmp j := by
    intro h
    have h' := congrArg Fin.val h
    change i.val + 1 = 3 + j.val at h'
    have := i.isLt
    omega
  have hf (j : Fin 3) : tmp j ≠ fr := by
    intro h
    have h' := congrArg Fin.val h
    change 3 + j.val = 0 at h'
    omega
  have hs (i : Fin 2) : src i ≠ fr := by
    intro h
    have h' := congrArg Fin.val h
    change i.val + 1 = 0 at h'
    omega
  have h := (supplied.code_spec fr src tmp hi hd hf hs).2 w (upper, address)
    (initial frontier upper address mem) hb (by funext i; fin_cases i <;> rfl)
    ⟨trivial, fun _ _ _ => ⟨⟨trivial, trivial⟩, le_rfl, le_rfl⟩⟩
    (admissible (w := w) (d := (upper, address)) (s := ⟨mem, frontier⟩) (hb.1 1) ha)
  have h' := h.map (fun z : (Fin 1 → ℕ) × Memory.State => (z.1 0, z.2))
  apply h'.congr_law
  rw [PMF.map_comp]
  change ((Memory.spec w).toRandomized.withCoins.run (experiment (upper, address))
    ⟨mem, frontier⟩).map _ = _
  rw [run_experiment, PMF.map_comp]
  rfl

-- A uniform four-outcome draw includes the largest width-two payload. The literal final
-- memory is retained, including every inaccessible cell; the result equals the written cell.
example : ExecRandLaw 2 (supplied.code fr src tmp) (initial 2 3 1 (fun _ => 2))
    (fun y => ∀ i, i ≠ fr → (∀ j, tmp j ≠ i) → y.regs i = (initial 2 3 1 (fun _ => 2)).regs i)
    6 1 (fun y => (y.regs 3, memoryState fr y))
    ((Probability.PMF.uniformOfFintype (Fin 4)).map fun r =>
      (r.val, (⟨Function.update (fun _ => 2) 1 r.val, 2⟩ : Memory.State))) := by
  apply native
  · constructor
    · intro i
      fin_cases i <;> decide
    · intro a
      change Fits 2 2
      decide
  · decide

-- Zero upper bound still executes one rand instruction; it is not a no-draw branch.
example : ExecRandLaw 1 (supplied.code fr src tmp) (initial 1 0 0 (fun _ => 1))
    (fun y => ∀ i, i ≠ fr → (∀ j, tmp j ≠ i) → y.regs i = (initial 1 0 0 (fun _ => 1)).regs i)
    6 1 (fun y => (y.regs 3, memoryState fr y))
    ((Probability.PMF.uniformOfFintype (Fin 1)).map fun r =>
      (r.val, (⟨Function.update (fun _ => 1) 0 r.val, 1⟩ : Memory.State))) := by
  apply native
  · constructor
    · intro i
      fin_cases i <;> decide
    · intro a
      change Fits 1 1
      decide
  · decide

-- The distribution is genuinely nondegenerate: both extreme outcomes have positive support.
example : (0, (⟨Function.update (fun _ => 2) 1 0, 2⟩ : Memory.State)) ∈
      ((Memory.spec 2).toRandomized.withCoins.run (experiment (3, 1)) ⟨fun _ => 2, 2⟩).support ∧
    (3, (⟨Function.update (fun _ => 2) 1 3, 2⟩ : Memory.State)) ∈
      ((Memory.spec 2).toRandomized.withCoins.run (experiment (3, 1)) ⟨fun _ => 2, 2⟩).support := by
  rw [run_experiment]
  constructor
  · exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨(0 : Fin 4), Probability.PMF.mem_support_uniformOfFintype _, rfl⟩
  · exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨(3 : Fin 4), Probability.PMF.mem_support_uniformOfFintype _, rfl⟩

-- Original input coordinates may alias. Here upper=address=1, while the physically unused
-- input register2 is an unrelated live marker3 that the full frame must preserve.
example : ExecRandLaw 2 (supplied.code fr (fun _ => 1) tmp)
    (⟨![2, 1, 3, 0, 0, 0], fun _ => 2⟩ : Data 6)
    (fun y => y.regs 2 = 3 ∧ y.regs 1 = 1)
    6 1 (fun y => (y.regs 3, memoryState fr y))
    ((Probability.PMF.uniformOfFintype (Fin 2)).map fun r =>
      (r.val, (⟨Function.update (fun _ => 2) 1 r.val, 2⟩ : Memory.State))) := by
  have h := (supplied.code_spec fr (fun _ => 1) tmp
    (by change Function.Injective tmp; decide)
    (by
      intro i j
      fin_cases j <;> decide)
    (by
      intro j
      change tmp j ≠ (0 : Fin 6)
      fin_cases j <;> decide)
    (by intro i; change (1 : Fin 6) ≠ 0; decide)).2 2 (1, 1)
      (⟨![2, 1, 3, 0, 0, 0], fun _ => 2⟩ : Data 6)
      (by
        constructor
        · intro i
          fin_cases i <;> decide
        · intro a
          change Fits 2 2
          decide)
      (by funext i; fin_cases i <;> rfl)
      ⟨trivial, fun _ _ _ => ⟨⟨trivial, trivial⟩, le_rfl, le_rfl⟩⟩
      (admissible (w := 2) (d := (1, 1)) (s := ⟨fun _ => 2, 2⟩) (by decide) (by decide))
  have h' := (h.map (fun z : (Fin 1 → ℕ) × Memory.State => (z.1 0, z.2))).mono
    (Q := fun y => y.regs 2 = 3 ∧ y.regs 1 = 1) (fun y hf => ?_) le_rfl le_rfl
  · apply h'.congr_law
    rw [PMF.map_comp]
    change ((Memory.spec 2).toRandomized.withCoins.run (experiment (1, 1))
      ⟨fun _ => 2, 2⟩).map _ = _
    rw [run_experiment, PMF.map_comp]
    rfl
  · exact ⟨hf 2 (by decide) (fun j he => by
      have hval := congrArg Fin.val he
      change 3 + j.val = 2 at hval
      omega), hf 1 (by decide) (fun j he => by
      have hval := congrArg Fin.val he
      change 3 + j.val = 1 at hval
      omega)⟩

-- Invalid continuation history is not a claimed RAM fault or an extra fit premise.
example : ¬(Memory.spec 2).ValidHistory ⟨fun _ => 0, 2⟩
    ((Memory.spec 2).clientHistory ⟨fun _ => 0, 2⟩ (do
      Memory.write 2 0
      Memory.read 2)) := by decide

end CslibFrontierTests.WordRAMRealizationRandomWitness
