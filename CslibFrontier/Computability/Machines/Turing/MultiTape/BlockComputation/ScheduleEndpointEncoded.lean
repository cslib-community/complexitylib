/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointSelector
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointOutput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleEndpointDispatch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BranchRunsBetween
import Mathlib.Tactic.FinCases

/-!
# The complete encoded schedule endpoint adapter

The finite native adapter starts with the framed external query on its input tape. It prepares
the raw table and two binary fields, checks raw validity before selector dispatch, and emits
the complete tagged endpoint answer. Malformed rows, invalid selectors and invalid intervals
are all rejected. Every input conversion, dispatch and output transition is charged.
-/

public section

namespace Turing.MultiTapeTM.ScheduleEndpointEncoded

open ScheduleEndpointQuery

private abbrev totalTapes (scratch selectorTapes : ℕ) := (scratch + 4) + (selectorTapes + 7)

private def prepareTapes (scratch selectorTapes : ℕ) :
    Fin (scratch + 4) ↪ Fin (totalTapes scratch selectorTapes) :=
  Fin.castAddEmb (selectorTapes + 7)

private def fieldTape (scratch selectorTapes : ℕ) (i : Fin 4) :
    Fin (totalTapes scratch selectorTapes) :=
  prepareTapes scratch selectorTapes (Fin.natAdd scratch i)

private def selectorTapes (scratch K : ℕ) (source : Fin K) :
    Fin K ↪ Fin (totalTapes scratch K) :=
  ⟨fun i => if i = source then fieldTape scratch K 1
    else Fin.natAdd (scratch + 4) (i.castAdd 7), by
    intro i j hij
    by_cases hi : i = source <;> by_cases hj : j = source
    · exact hi.trans hj.symm
    · have hv := congrArg Fin.val hij
      simp only [hi, hj, ite_true, ite_false, fieldTape, prepareTapes,
        Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    · have hv := congrArg Fin.val hij
      simp only [hi, hj, ite_true, ite_false, fieldTape, prepareTapes,
        Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    · apply Fin.ext
      have hv := congrArg Fin.val hij
      simp only [hi, hj, ite_false, Fin.val_castAdd, Fin.val_natAdd] at hv
      omega⟩

private theorem selectorTapes_apply (scratch K : ℕ) (source j : Fin K) :
    selectorTapes scratch K source j = if j = source then fieldTape scratch K 1
      else Fin.natAdd (scratch + 4) (j.castAdd 7) := rfl

private def endpointMap (scratch K : ℕ) (target : Fin K) :
    Fin 7 → Fin (totalTapes scratch K) :=
  ![Fin.natAdd (scratch + 4) (Fin.natAdd K 0), fieldTape scratch K 2,
    Fin.natAdd (scratch + 4) (Fin.natAdd K 2), fieldTape scratch K 0,
    Fin.natAdd (scratch + 4) (Fin.natAdd K 4),
    Fin.natAdd (scratch + 4) (Fin.natAdd K 5),
    Fin.natAdd (scratch + 4) (target.castAdd 7)]

private def endpointTapes (scratch K : ℕ) (target : Fin K) :
    Fin 7 ↪ Fin (totalTapes scratch K) :=
  ⟨endpointMap scratch K target, by
    intro i j hij
    have hv := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      have := target.isLt
      dsimp [endpointMap, fieldTape, prepareTapes] at hv
      omega⟩

private theorem endpointTapes_apply (scratch K : ℕ) (target : Fin K) (j : Fin 7) :
    endpointTapes scratch K target j = endpointMap scratch K target j := rfl

private def preparedWords (scratch K k : ℕ) (a : Input) :
    Fin (totalTapes scratch K) → List Bool :=
  Fin.append (Fin.append (fun _ : Fin scratch => [])
    ![a.raw, a.selector.bits, a.interval.bits, [ScheduleBits.validate k a.raw]])
    (fun _ : Fin (K + 7) => [])

private def selectedWords (scratch K k : ℕ) (source target : Fin K) (a : Input) :
    Fin (totalTapes scratch K) → List Bool :=
  Function.update (preparedWords scratch K k a) (selectorTapes scratch K source target)
    (ScheduleEndpointSelector.word k a.selector)

private theorem preparedWords_selector (scratch K k : ℕ) (source : Fin K) (a : Input) :
    (fun j => preparedWords scratch K k a (selectorTapes scratch K source j)) =
      Function.update (fun _ => []) source a.selector.bits := by
  funext j
  by_cases hj : j = source
  · subst j
    simp [preparedWords, selectorTapes_apply, fieldTape, prepareTapes]
  · simp [preparedWords, selectorTapes_apply, hj]

private theorem selectedWords_selector (scratch K k : ℕ) (source target : Fin K) (a : Input) :
    (fun j => selectedWords scratch K k source target a (selectorTapes scratch K source j)) =
      Function.update (Function.update (fun _ => []) source a.selector.bits) target
        (ScheduleEndpointSelector.word k a.selector) := by
  funext j
  simp only [selectedWords, Function.update_apply,
    (selectorTapes scratch K source).injective.eq_iff]
  rw [congrFun (preparedWords_selector scratch K k source a) j]
  simp only [Function.update_apply]

private theorem selectedWords_endpoint (scratch K k : ℕ) (source target : Fin K)
    (hne : source ≠ target) (a : Input) :
    (fun j => selectedWords scratch K k source target a
      (endpointTapes scratch K target j)) =
      ![[], a.interval.bits, [], a.raw, [], [], ScheduleEndpointSelector.word k a.selector] := by
  have ht : target ≠ source := Ne.symm hne
  have he : selectorTapes scratch K source target =
      Fin.natAdd (scratch + 4) (target.castAdd 7) := by
    rw [selectorTapes_apply, ite_eq_right ht]
  have htag (j : Fin 7) : endpointTapes scratch K target j =
      Fin.natAdd (scratch + 4) (target.castAdd 7) ↔ j = 6 := by
    change endpointTapes scratch K target j = endpointTapes scratch K target 6 ↔ j = 6
    exact (endpointTapes scratch K target).injective.eq_iff
  simp only [selectedWords, he]
  funext j
  simp only [Function.update_apply, htag]
  fin_cases j <;>
    simp [preparedWords, endpointTapes_apply, endpointMap, fieldTape, prepareTapes]

private theorem runsBetween_prepare {scratch K k : ℕ} {Q : Type}
    {tm : MultiTapeTM (scratch + 4) Bool Q} {c : ℕ}
    (hprep : ∀ (a : Input) (out : List Bool),
      RunsBetween tm (tapesCfg (ScheduleEndpointInput.encInput a) (fun _ => []) 0 0 out)
        (tapesCfg (ScheduleEndpointInput.encInput a)
          (Fin.append (fun _ : Fin scratch => [])
            ![a.raw, a.selector.bits, a.interval.bits, [ScheduleBits.validate k a.raw]])
          0 0 out)
        (c * ((ScheduleEndpointInput.encInput a).length + 1))
        ((scratch + 4) * (c * ((ScheduleEndpointInput.encInput a).length + 1) + 1)))
    (a : Input) (out : List Bool) :
    RunsBetween (tm.extendTapes (prepareTapes scratch K))
      (tapesCfg (ScheduleEndpointInput.encInput a) (fun _ => []) 0 0 out)
      (tapesCfg (ScheduleEndpointInput.encInput a) (preparedWords scratch K k a) 0 0 out)
      (c * ((ScheduleEndpointInput.encInput a).length + 1))
      (totalTapes scratch K * (c * ((ScheduleEndpointInput.encInput a).length + 1) + 1)) := by
  have h := hprep a out
  have hv : viewCfg (prepareTapes scratch K)
      (tapesCfg (ScheduleEndpointInput.encInput a) (fun _ => []) 0 0 out) =
      tapesCfg (ScheduleEndpointInput.encInput a) (fun _ : Fin (scratch + 4) => []) 0 0 out := rfl
  rw [← hv] at h
  have he := h.extendTapes (prepareTapes scratch K)
  have hf : embed (prepareTapes scratch K)
      (tapesCfg (ScheduleEndpointInput.encInput a)
        (Fin.append (fun _ : Fin scratch => [])
          ![a.raw, a.selector.bits, a.interval.bits, [ScheduleBits.validate k a.raw]]) 0 0 out)
      (tapesCfg (ScheduleEndpointInput.encInput a) (fun _ => []) 0 0 out).workTapes
      (tapesCfg (ScheduleEndpointInput.encInput a) (fun _ => []) 0 0 out).workTapePos =
      tapesCfg (ScheduleEndpointInput.encInput a) (preparedWords scratch K k a) 0 0 out := by
    rw [prepareTapes, embed_castAdd]
    refine Cfg.ext rfl rfl ?_ ?_ rfl <;> funext i <;> induction i using Fin.addCases <;>
      simp [preparedWords, tapesCfg]
  rw [hf] at he
  exact RunsBetween.of_runFrom he.1

private theorem runsBetween_select {scratch K k : ℕ} {Q : Type}
    {tm : MultiTapeTM K Bool Q} {source target : Fin K} {c : ℕ}
    (hselect : ∀ (input out : List Bool) (selector : ℕ),
      RunsBetween tm
        (tapesCfg input (Function.update (fun _ => []) source selector.bits) 0 0 out)
        (tapesCfg input (Function.update (Function.update (fun _ => []) source selector.bits)
          target (ScheduleEndpointSelector.word k selector)) 0 0 out)
        c (K * (c + 1)))
    (input out : List Bool) (a : Input) :
    RunsBetween (tm.extendTapes (selectorTapes scratch K source))
      (tapesCfg input (preparedWords scratch K k a) 0 0 out)
      (tapesCfg input (selectedWords scratch K k source target a) 0 0 out)
      c (totalTapes scratch K * (c + 1)) := by
  have h := hselect input out a.selector
  have hv : viewCfg (selectorTapes scratch K source)
      (tapesCfg input (preparedWords scratch K k a) 0 0 out) =
      tapesCfg input (Function.update (fun _ => []) source a.selector.bits) 0 0 out := by
    rw [viewCfg_tapesCfg, preparedWords_selector]
    rfl
  rw [← hv] at h
  have he := h.extendTapes (selectorTapes scratch K source)
  have hf : embed (selectorTapes scratch K source)
      (tapesCfg input (Function.update (Function.update (fun _ => []) source a.selector.bits)
        target (ScheduleEndpointSelector.word k a.selector)) 0 0 out)
      (tapesCfg input (preparedWords scratch K k a) 0 0 out).workTapes
      (tapesCfg input (preparedWords scratch K k a) 0 0 out).workTapePos =
      tapesCfg input (selectedWords scratch K k source target a) 0 0 out := by
    apply embed_tapesCfg
    · intro j
      exact ⟨congrFun (selectedWords_selector scratch K k source target a) j, rfl, rfl⟩
    · intro j hj
      have hne : j ≠ selectorTapes scratch K source target := fun he => hj ⟨target, he.symm⟩
      exact ⟨Function.update_of_ne hne .., rfl, rfl⟩
  rw [hf] at he
  exact RunsBetween.of_runFrom he.1

private def endpointClock (k : ℕ) (a : Input) : ℕ :=
  (8 * k + 32) * a.raw.length + 5 * a.interval.bits.length + 6 * k + 49

private theorem runsBetween_dispatch (scratch K k : ℕ) (source target : Fin K)
    (hne : source ≠ target) (input out : List Bool) (a : Input)
    (hvalid : ScheduleBits.validate k a.raw = true) :
    ∃ final, RunsBetween ((ScheduleEndpointDispatch.machine k).extendTapes
      (endpointTapes scratch K target))
      (tapesCfg input (selectedWords scratch K k source target a) 0 0 out) final
      (endpointClock k a) (totalTapes scratch K * (endpointClock k a + 1)) ∧
      final.output = out ++ ScheduleEndpointAnswer.encAnswer (query k a) := by
  obtain ⟨rs, hrs⟩ := (ScheduleBits.validate_eq_true_iff_exists_rows k a.raw).mp hvalid
  let σ : MultiTapePTM.Schedule k rs.length := fun j => rs[j.val]
  have hσ : List.ofFn σ = rs := List.ofFn_getElem
  have hw : RawScheduleEndpoint.word σ = a.raw := by
    rw [RawScheduleEndpoint.word, hσ, hrs]
  have hq : rs.length ≤ a.raw.length := by
    have hl := RawScheduleEndpoint.length_word σ
    rw [hw] at hl
    nlinarith
  have hr := ScheduleEndpointDispatch.runsBetween input out σ a.selector a.interval
  have hv : viewCfg (endpointTapes scratch K target)
      (tapesCfg input (selectedWords scratch K k source target a) 0 0 out) =
      ScheduleEndpointDispatch.initialConfig input a.raw a.interval.bits
        (ScheduleEndpointSelector.word k a.selector) out := by
    rw [viewCfg_tapesCfg, selectedWords_endpoint scratch K k source target hne a]
    rfl
  rw [hw, ← hv] at hr
  have he := hr.extendTapes (endpointTapes scratch K target)
  have ht : (8 * k + 32) * rs.length + 5 * a.interval.bits.length + 6 * k + 49 ≤
      endpointClock k a := by
    dsimp only [endpointClock]
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.mul_le_mul_left (8 * k + 32) hq) _) _) _
  refine ⟨_, (RunsBetween.of_runFrom he.1).mono ht
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right ht 1)), ?_⟩
  have ho := ScheduleEndpointDispatch.finalConfig_output_query input out σ a.selector a.interval
  have ha : (⟨a.raw, a.selector, a.interval⟩ : Input) = a := by cases a; rfl
  simpa only [embed, hw, ha] using ho

/-- One finite native machine handles the complete external encoding, including malformed raw
tables and arbitrary binary selectors and intervals. It preserves the previous output and appends
the tagged total query answer, with every preparation, guard, dispatch and serialization step
included in a linear clock. The machine and its coefficient are chosen before all requests. -/
theorem exists_machine (k : ℕ) :
    ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q) (c : ℕ),
      ∀ (a : Input) (out : List Bool), ∃ final,
        RunsBetween tm (tapesCfg (ScheduleEndpointInput.encInput a) (fun _ => []) 0 0 out)
          final (c * ((ScheduleEndpointInput.encInput a).length + 1))
          (K * (c * ((ScheduleEndpointInput.encInput a).length + 1) + 1)) ∧
        final.output = out ++ ScheduleEndpointAnswer.encAnswer (query k a) := by
  classical
  obtain ⟨scratch, Q₀, hQ₀, prepare, c₀, hprepare⟩ := ScheduleEndpointInput.exists_prepare k
  obtain ⟨K, Q₁, hQ₁, select, source, target, c₁, hne, hselect⟩ :=
    ScheduleEndpointSelector.exists_prepare k
  let N := totalTapes scratch K
  let selected := (select.extendTapes (selectorTapes scratch K source)).seq
    ((ScheduleEndpointDispatch.machine k).extendTapes (endpointTapes scratch K target))
  let guarded := branchOn (fun cell : Option Bool => cell.getD false)
    (fieldTape scratch K 3) selected (ScheduleEndpointDispatch.reject N)
  let tm := (prepare.extendTapes (prepareTapes scratch K)).seq guarded
  let c := c₀ + c₁ + 14 * k + 87
  refine ⟨N, _, inferInstance, tm, c, ?_⟩
  intro a out
  let input := ScheduleEndpointInput.encInput a
  let prepared := tapesCfg input (preparedWords scratch K k a) 0 0 out
  have hp := runsBetween_prepare (K := K) hprepare a out
  have hcell : prepared.workTapeSymbols (fieldTape scratch K 3) =
      some (ScheduleBits.validate k a.raw) := by
    simp [prepared, tapesCfg_workTapeSymbols_self, preparedWords, fieldTape, prepareTapes]
  have hlen := ScheduleEndpointInput.length_encInput a
  have hraw : a.raw.length ≤ input.length := by dsimp only [input]; omega
  have hindex : a.interval.bits.length ≤ input.length := by dsimp only [input]; omega
  cases hv : ScheduleBits.validate k a.raw with
  | false =>
    have hg := (ScheduleEndpointDispatch.runsBetween_reject prepared).branchOn_of_false
      (test := fun cell : Option Bool => cell.getD false) (i := fieldTape scratch K 3)
      (tm₁ := selected) (by
        rw [hcell, hv]
        rfl)
    have hr := hp.seq hg
    have ht : c₀ * (input.length + 1) + (1 + 1) ≤ c * (input.length + 1) := by
      dsimp only [c]
      nlinarith
    refine ⟨_, (RunsBetween.of_runFrom hr.1).mono ht
      (Nat.mul_le_mul_left N (Nat.add_le_add_right ht 1)), ?_⟩
    have hquery : query k a = none := by
      apply query_eq_none_of_not_valid
      simp [valid, hv]
    simp [prepared, tapesCfg, hquery, ScheduleEndpointAnswer.encAnswer]
  | true =>
    have hs := runsBetween_select (scratch := scratch) hselect input out a
    obtain ⟨final, hd, hout⟩ := runsBetween_dispatch scratch K k source target hne input out a hv
    have hg := (hs.seq hd).branchOn_of_true
      (test := fun cell : Option Bool => cell.getD false) (i := fieldTape scratch K 3)
      (tm₂ := ScheduleEndpointDispatch.reject N) (by
        change (prepared.workTapeSymbols (fieldTape scratch K 3)).getD false = true
        rw [hcell, hv]
        rfl)
    have hr := hp.seq hg
    have ht : c₀ * (input.length + 1) + (c₁ + endpointClock k a + 1) ≤
        c * (input.length + 1) := by
      have hraw' := Nat.mul_le_mul_left (8 * k + 32) hraw
      have hindex' := Nat.mul_le_mul_left 5 hindex
      dsimp only [c, endpointClock]
      nlinarith
    exact ⟨final, (RunsBetween.of_runFrom hr.1).mono ht
      (Nat.mul_le_mul_left N (Nat.add_le_add_right ht 1)), hout⟩

end Turing.MultiTapeTM.ScheduleEndpointEncoded
