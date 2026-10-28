/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import Complexity.Algorithms.WordRAM.ThreeSum.Frontend

/-!
# Fully admissible clients of the complete native frontend

The execution observations are in `WordRAMThreeSumFrontend`. These clients consume proved
native contracts, discharge all global promises, and check integer injectivity and signed-width
composition. They do not claim interpreter execution.
-/

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ThreeSum.Frontend

-- The empty case still has twenty triples and sixty array slots at κ=0.
example : width 0 0 = 484 ∧ (layout 0 0).count = 20 ∧ (layout 0 0).arrays = 60 := by
  decide +kernel

example : ∃ (y : Data 128) (steps : ℕ),
    Executes 4096 ((program 0).program descriptorCount) (State.init []) 20 steps ∧
      Runs 4096 ((program 0).program descriptorCount) (State.init [])
        ⟨(program 0).size, y⟩ (steps - 1) ∧
      steps ≤ cost 0 0 ∧ readRoots (layout 0 0) y.mem =
        Cslib.Algorithms.ThreeSum.inputs 1 (fun i : Fin 0 => ([] : List ℤ)[i]) := by
  obtain ⟨y, steps, he, hr, ht, ho, _, _, _, _⟩ := runs_input (κ := 0) (w := 4096) [] (by decide)
    (by simp)
  exact ⟨y, steps, he, hr, ht, ho⟩

-- The signed endpoints satisfy both the input promise and the physical/signed width offset.
example : ∃ steps,
    Executes 4096 ((program 1).program descriptorCount)
      (State.init ([(-4 : ℤ), 4].map Signed.encode)) (layout 1 2).count steps ∧
      steps ≤ cost 1 2 := by
  have hv : ∀ z ∈ ([(-4 : ℤ), 4] : List ℤ), |z| ≤ ((2 + 2) ^ 1 : ℕ) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> decide
  obtain ⟨y, steps, he, _, ht, _, _, _, _, _⟩ :=
    runs_input (κ := 1) (w := 4096) [(-4 : ℤ), 4] (by decide) hv
  exact ⟨steps, he, ht⟩

-- A generic caller obtains actual native slots, injective integer arrays and full multiplicities.
example {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hv : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ y rs, ExecWithin w (program κ) (Data.init (input.map Signed.encode)) y
        (cost κ input.length - 1) ∧
      Output (layout κ input.length) ((input.length + 2) ^ κ) rs y.mem ∧
      (∀ p ∈ rs, (input.map Signed.encode).count p.1 = p.2) ∧
      (∀ j < (layout κ input.length).arrays,
        ((readArray y.mem ((layout κ input.length).descriptors + 2 * j)).map Signed.decode).Nodup ∧
        ∀ u ∈ readArray y.mem ((layout κ input.length).descriptors + 2 * j),
          Cslib.GenericRAM.Signed.Fits (w - 2) (Signed.decode u)) := by
  obtain ⟨y, rs, he, ho, _, _, _, hn, _, hk, hc, _, _, _, _⟩ := exec_input input hw hv
  refine ⟨y, rs, he, ho, fun p hp => (hc p hp).2, ?_⟩
  intro j hj
  rw [ho.read_array hj]
  refine ⟨Math.array_decoded_nodup hk hn _ _ j, ?_⟩
  intro u hu
  exact signed_output_fits hw (Math.array_magnitude hk hv _ j u hu)

-- A polynomial allocation bound includes descriptor addresses as well as all output payloads.
example (κ n : ℕ) : (layout κ n).endpoint ≤ (n + 2) ^ (80 * κ + 480) := by
  exact (Arrays.layout_bounds (layout κ n) ((n + 2) ^ κ)).2.2.2.2.2.2.2.2.1 |>.trans
    (array_budget_polynomial κ n)

-- A checked frontend value fits the signed kernel ABI at the derived physical width.
example : Cslib.GenericRAM.Signed.Fits (4096 - 2) (-8) :=
  signed_output_fits (κ := 1) (n := 2) (by decide) (by decide)

-- Complete array construction also accepts arbitrary old output and scratch memory.
example (mem : ℕ → ℕ) :
    let x : Data 48 := ⟨(fun i => match i.val with
      | 0 | 20 | 21 | 34 => 1
      | 28 => 3
      | _ => 0), mem⟩
    ∃ y, ExecWithin 16 Arrays.program x y (60 * 32 + 21) ∧
      Output ⟨0, 3⟩ 1 [] y.mem ∧
      Modifies (Block.mk 1 180).footprint mem y.mem := by
  dsimp only
  obtain ⟨y, he, ho, _, _, _, _, hf⟩ := Arrays.exec (w := 16) (U := 1) ⟨0, 3⟩ []
    ⟨(fun i => match i.val with | 0 | 20 | 21 | 34 => 1 | 28 => 3 | _ => 0), mem⟩
    rfl rfl rfl rfl rfl rfl rfl (by decide) (Block.holdsList_nil _ _) (Block.holdsList_nil _ _)
    (by simp) (by decide)
  exact ⟨y, he, ho, hf⟩
