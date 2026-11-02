/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProviderLabels
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayLoadCorrect
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Tactic.FinCases

/-!
# Correct provider-window assembly

The raw combiner preserves canonical buffers and selects the same blocks as the semantic
entering window. Checked labels must all succeed, including labels at unused provider ports.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Providers

variable {k s : ℕ} {Q : Type}

private theorem length_block (b : ℕ) (ports : PortMap k) (previous : RawResult k Q)
    (providers : ProviderValues k Q) (hprevious : Load.CanonicalWindows b previous)
    (hproviders : ∀ h d, Load.CanonicalWindows b (providers h d)) (h : Fin k) (d : Fin 3) :
    (block b ports previous providers h d).length = b := by
  have hp := hprevious.1 h
  have hh := (hproviders h d).1 h
  cases ht : ports h d with
  | none =>
    simp only [block, ht, List.length_map, List.length_take, hp]
    omega
  | some p =>
    have hfit := Nat.mul_le_mul_right b (Nat.succ_le_of_lt p.isLt)
    rw [Nat.succ_mul] at hfit
    simp only [block, ht, List.length_take, List.length_drop, hh]
    omega

private theorem code_block (b : ℕ) (ports : PortMap k) (previous : RawResult k Q)
    (providers : ProviderValues k Q) (hproviders : ∀ h d, Load.CanonicalWindows b (providers h d))
    (h : Fin k) (d : Fin 3) (n : ℕ) (hn : n ∈ block b ports previous providers h d) : n ≤ 2 := by
  cases ht : ports h d with
  | none =>
    simp only [block, ht, List.mem_map] at hn
    obtain ⟨_, _, rfl⟩ := hn
    decide
  | some p =>
    simp only [block, ht] at hn
    exact (hproviders h d).2 h n (List.mem_of_mem_drop (List.mem_of_mem_take hn))

/-- Assembling valid provider blocks preserves the loader's canonical explicit buffers. -/
theorem canonical_combine (b : ℕ) (ports : PortMap k) (previous : RawResult k Q)
    (providers : ProviderValues k Q) (hprevious : Load.CanonicalWindows b previous)
    (hproviders : ∀ h d, Load.CanonicalWindows b (providers h d)) :
    Load.CanonicalWindows b (combine (b, ports, previous, providers)) := by
  constructor
  · intro h
    simp only [List.length_append,
      length_block b ports previous providers hprevious hproviders]
    omega
  · intro h n hn
    simp only [List.mem_append] at hn
    rcases hn with (hn | hn) | hn
    · exact code_block b ports previous providers hproviders h 0 n hn
    · exact code_block b ports previous providers hproviders h 1 n hn
    · exact code_block b ports previous providers hproviders h 2 n hn

private theorem getD_block (b : ℕ) (ports : PortMap k) (previous : RawResult k Q)
    (providers : ProviderValues k Q) (h : Fin k) (d : Fin 3) (r : ℕ) (hr : r < b) :
    cellOfCode ((block b ports previous providers h d).getD r 0) =
      match ports h d with
      | none => none
      | some p => cellOfCode (((providers h d).2.2.2 h).getD (p.val * b + r) 0) := by
  cases ht : ports h d with
  | none => simp [block, ht, cellOfCode]
  | some p => rw [block, ht, List.getD_take_drop _ _ hr]

/-- Interpreting the native result gives exactly the selected semantic entering windows. -/
theorem toView_combine (b : ℕ) [NeZero b] (ports : PortMap k) (previous : RawResult k Q)
    (providers : ProviderValues k Q) (hprevious : Load.CanonicalWindows b previous)
    (hproviders : ∀ h d, Load.CanonicalWindows b (providers h d)) :
    RawResult.toView b (combine (b, ports, previous, providers)) =
      ((RawResult.toView b previous).1, fun h d r =>
        match ports h d with
        | none => none
        | some p => (RawResult.toView b (providers h d)).2 h p r) := by
  apply Prod.ext
  · rfl
  · funext h d r
    have hr := ZMod.val_lt r
    have hl (d : Fin 3) := length_block b ports previous providers hprevious hproviders h d
    have hread :
        (block b ports previous providers h 0 ++ block b ports previous providers h 1 ++
          block b ports previous providers h 2).getD (d.val * b + r.val) 0 =
        (block b ports previous providers h d).getD r.val 0 := by
      fin_cases d
      · rw [List.getD_append _ _ _ _ (by simp only [List.length_append, hl]; omega)]
        simpa using
          List.getD_append (block b ports previous providers h 0)
            (block b ports previous providers h 1) 0 r.val (by simpa only [hl] using hr)
      · rw [List.getD_append _ _ _ _ (by simp only [List.length_append, hl]; omega)]
        rw [List.getD_append_right _ _ _ _ (by simp only [hl]; omega)]
        simp only [hl]
        congr 1
        omega
      · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, hl]; omega)]
        simp only [List.length_append, hl]
        congr 1
        omega
    change cellOfCode ((block b ports previous providers h 0 ++
      block b ports previous providers h 1 ++ block b ports previous providers h 2).getD
        (d.val * b + r.val) 0) = _
    rw [hread, getD_block b ports previous providers h d r.val hr]
    cases ht : ports h d <;> simp [ht, RawResult.toView]

/-- Successful checked parsing of every supplied label gives the assembled raw windows.
The condition includes provider words whose selected port is absent. -/
theorem Labels.combine_of_parse {s : ℕ} (e : Q ≃ Fin s) (b : ℕ) (ports : PortMap k)
    (previousWord : List Bool) (providerWords : Labels.ProviderWords k)
    (previous : RawResult k Q) (providers : ProviderValues k Q)
    (hprevious : Encoding.NativeChecked.parse e (b, previousWord) = some previous)
    (hproviders : ∀ h d,
      Encoding.NativeChecked.parse e (b, providerWords h d) = some (providers h d)) :
    Labels.combine e (b, ports, previousWord, providerWords) =
      some (Providers.combine (b, ports, previous, providers)) := by
  simp [Labels.combine, hprevious, hproviders]

/-- The semantic schedule chooses the last earlier interval containing each entering block,
then reads that block at its port in the provider's window. A never visited block is blank.
This finite map specifies the native assembler's input; computing it is a caller operation. -/
@[expose] def portMap {q : ℕ} (σ : Schedule k q) (i : Fin q) : PortMap k := fun h d =>
  (lastBefore (InWindow σ h (portBlock σ i h d)) i).map
    fun j => portOf σ j h (portBlock σ i h d)

/-- With the schedule's provider ports, native assembly reconstructs exactly the functional
block gate's entering window. The preceding control record is retained. All provider values
here have already succeeded; checking that condition belongs to the checked-label wrapper. -/
theorem toView_combine_enteringWindow {q : ℕ} (machine : MultiTapePTM k Bool Q)
    (b : ℕ) [NeZero b] (σ : Schedule k q) (i : Fin q) (previous : RawResult k Q)
    (providers : ProviderValues k Q) (hprevious : Load.CanonicalWindows b previous)
    (hproviders : ∀ h d, Load.CanonicalWindows b (providers h d)) :
    RawResult.toView b (combine (b, portMap σ i, previous, providers)) =
      ((RawResult.toView b previous).1,
        enteringWindow machine b σ i (fun h d => some (RawResult.toView b (providers h d)))) := by
  rw [toView_combine b (portMap σ i) previous providers hprevious hproviders]
  apply Prod.ext
  · rfl
  · funext h d r
    cases ht : lastBefore (InWindow σ h (portBlock σ i h d)) i <;>
      simp [portMap, enteringWindow, ht]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Providers
