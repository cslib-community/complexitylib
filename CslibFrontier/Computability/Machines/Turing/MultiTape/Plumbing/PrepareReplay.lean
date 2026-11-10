/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PreparePair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapesView
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import CslibFrontier.Foundations.Data.Fin.Tuple
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Preparing saved coins and a buffered input

Both closed and external-oracle replay decode an encoded pair onto disjoint tapes. The first
word supplies saved coins; the second becomes the virtual input, with a separate boundary marker.
These helpers describe the same deterministic preparation independently of the replay controller.

## Main definitions

* `Turing.MultiTapeTM.ReplayInput.prepareTapes`: reserve disjoint source and preparation tapes.
* `Turing.MultiTapeTM.ReplayInput.words`: prepared coins and input before marking the boundary.

## Main results

* `Turing.MultiTapeTM.ReplayInput.runFrom_prepare`: the pair preparer's full machine execution.
* `Turing.MultiTapeTM.ReplayInput.runFrom_mark`: the two-step virtual-input boundary marker.

## References

Extracted from `MultiTape.Probabilistic.ReplayInput`, adapted there from the cslib `crypto` branch
at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ReplayInput

variable {k r : ℕ} {PrepareState : Type}

/-- Reserve source tapes before pair preparation and a boundary-marker tape after it. -/
def prepareTapes (k r : ℕ) : Fin (r + 2) ↪ Fin (k + r + 3) :=
  (Fin.natAddEmb k).trans Fin.castSuccEmb

/-- The two prepared words, with blank source, scratch and boundary tapes. -/
def words (k r : ℕ) (coins input : List Bool) : Fin (k + r + 3) → List Bool :=
  Fin.snoc (Fin.append (n := r + 2) (fun _ : Fin k => [])
    (Fin.append (fun _ : Fin r => []) ![coins, input])) []

/-- An initial source tape configuration with the saved coins on its last work tape. -/
def initial {Q : Type} (k r : ℕ) (coins input : List Bool) (q : Option Q) :
    Cfg (k + r + 1) Bool Q input :=
  wordsCfg input q (Fin.snoc (fun _ => []) coins) []

/-- Separate the source and saved-coin tapes from the virtual input and boundary marker. -/
theorem words_eq (k r : ℕ) (coins input : List Bool) :
    words k r coins input = Fin.append (Fin.snoc (fun _ : Fin (k + r) => []) coins)
      ![input, []] := by
  simp only [words, ← Fin.append_snoc, Fin.append_left_snoc]
  simpa [Fin.append_const, Function.comp_def] using
    (Fin.append_assoc (fun _ : Fin k => ([] : List Bool)) (fun _ : Fin r => [])
      (![coins, input, []] : Fin 3 → List Bool)).symm

/-- Two instructions prepare the virtual-input boundary marker. -/
theorem runFrom_mark (coins input outer : List Bool) :
    (markFlag (k + r + 1) (some true)).runFrom
        (wordsCfg outer (some (markWork Bool (some true)).q₀) (words k r coins input) []) 2 =
      inCfg true (initial k r coins input (Q := MarkWorkState) none) outer := by
  rw [words_eq, markFlag, runFrom_tapeEmb]
  have hv : oneTapeCfg (Fin.natAdd (k + r + 1) 1)
      (wordsCfg outer (some (markWork Bool (some true)).q₀)
        (Fin.append (Fin.snoc (fun _ : Fin (k + r) => []) coins) ![input, []]) []) =
      ⟨some (markWork Bool (some true)).q₀, 1, fun _ => (fun _ => none), fun _ => 0, []⟩ := by
    simp [oneTapeCfg, wordsCfg]
  rw [hv, runFrom_markWork, embed_tapeEmb]
  refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;>
    cases i using Fin.addCases with
    | left j => simp [initial, wordsCfg,
        Fin.castAdd_ne_natAdd]
    | right j => match j with
      | 0 | 1 => simp [initial, wordsCfg]

/-- Pair preparation reaches its exact output words on the reserved tapes. -/
theorem runFrom_prepare (prepare : MultiTapeTM (r + 2) Bool PrepareState)
    (coins input outer : List Bool) (t s : ℕ)
    (h : TransformsTapes prepare (fun inp ws => inp = outer ∧ ws = fun _ => [])
      (fun _ _ ws' emitted =>
        ws' = Fin.append (fun _ : Fin r => []) ![coins, input] ∧ emitted = []) t s) :
    (prepare.extendTapes (prepareTapes k r)).runFrom
        ((prepare.extendTapes (prepareTapes k r)).initCfg outer) t =
      wordsCfg outer none (words k r coins input) [] := by
  obtain ⟨ws', _, hrun, ⟨⟨hv, rfl⟩, hx⟩, _⟩ :=
    transformsTapes_iff_runFrom.mp (h.extendTapes (prepareTapes k r))
      outer (fun _ => []) [] ⟨rfl, rfl⟩
  have hw : ws' = words k r coins input := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      rw [hx]
      · simp [words]
      · rintro ⟨j, hj⟩
        have : k + (j : ℕ) = k + r + 2 := congrArg Fin.val hj
        lia
    | cast i =>
      cases i using (Fin.addCases (m := k) (n := r + 2)) with
      | left i =>
        rw [hx]
        · simp [words]
        · rintro ⟨j, hj⟩
          have : (Fin.natAdd k j).castSucc = (i.castAdd (r + 2)).castSucc := hj
          exact Fin.castAdd_ne_natAdd i j (Fin.castSucc_injective _ this).symm
      | right j =>
        have hj : ws' (Fin.natAdd k j).castSucc = Fin.append (fun _ => []) ![coins, input] j :=
          congrFun hv j
        simpa only [words, Fin.snoc_castSucc, Fin.append_right] using hj
  simpa only [initCfg_eq_wordsCfg, hw, List.nil_append] using hrun

end Turing.MultiTapeTM.ReplayInput
