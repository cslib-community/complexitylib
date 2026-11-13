/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProviderLabelsCorrect
public import CslibFrontier.Computability.TreeEval.Ary.Packed.AssignmentLabelsCorrect

/-!
# Total local gate supplier correctness

The native supplier computes the existing functional gate on every assignment, including failed
canonical labels and invalid motion. The explicit interpolation limit must pay the previous
label's width so that rejected calls emit the exact fixed-width FAIL code. No assumption that
all assignment labels succeed is imposed by the total theorem.

The same holds for explicit label words of the label width
(`Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier.finish_prepareWords_eq_gate`); on words
that encode views, the supplier computes the gate on those views
(`Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier.finish_prepareWords_encode`).
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier

open MultiTapeTM Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- The existing Boolean codec's FAIL value is exactly a fixed-width zero word. -/
theorem ofFn_encode_none (e : Q ≃ Fin s) (b : ℕ) [NeZero b] :
    List.ofFn (Encoding.encode (k := k) (b := b) e none) =
      List.replicate (Encoding.width k s b) false := by
  have hzero : Encoding.encode (k := k) (b := b) e none = fun _ => false := by
    funext j
    unfold Encoding.encode
    exact Fin.cases rfl (fun _ => rfl) j
  rw [hzero]
  simp

/-- Rejected parsing emits the previous word blanked, which is the full paid FAIL word when the
previous word has the label width, independently of the rejection time. -/
theorem finish_prepareWords_of_combined_none (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (N b σ i t : ℕ) (words : Assignments.Words k)
    (hlength : words.previous.length = Encoding.width k s b)
    (hcombined : Providers.Labels.combine e (b, ScheduleRead.providerMap k (σ, i),
      words.previous, words.providers) = none) :
    (CheckedGate.machine M e).finish ((CheckedGate.machine M e).runFrom w
      (prepareWords e (N, b, σ, i, words)) t) =
      List.replicate (Encoding.width k s b) false := by
  rw [prepareWords_eq_of_combined_none e N b σ i words hcombined,
    CheckedGate.runFrom_inl, CheckedGate.finish_inl, hlength]

/-- Rejected parsing emits the full paid FAIL word, independently of the rejection time. -/
theorem finish_prepare_of_combined_none (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (N b σ i limit counter stride t : ℕ)
    (hcapacity : Encoding.width k s b ≤ limit.size)
    (hcombined : Providers.Labels.combine e (b, ScheduleRead.providerMap k (σ, i),
      (Assignments.labels k ⟨limit, counter, stride, Encoding.width k s b⟩).previous,
      (Assignments.labels k ⟨limit, counter, stride, Encoding.width k s b⟩).providers) = none) :
    (CheckedGate.machine M e).finish ((CheckedGate.machine M e).runFrom w
      (prepare e (N, b, σ, i, limit, counter, stride)) t) =
      List.replicate (Encoding.width k s b) false :=
  finish_prepareWords_of_combined_none M e w N b σ i t _
    (AssignmentLabels.length_label _ _ _ _ _ (by simpa using hcapacity)) hcombined

/-- Failure of any checked input forces the functional gate to FAIL, even when that provider's
window is absent and its contents would otherwise be unused. -/
theorem gate_eq_none_of_failed_parse {q : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) (σ : Schedule k q) (i : Fin q)
    (previousWord : List Bool) (providerWords : Providers.Labels.ProviderWords k)
    (hfailed : Encoding.NativeChecked.parse (k := k) e (b, previousWord) = none ∨
      ∃ h δ, Encoding.NativeChecked.parse (k := k) e (b, providerWords h δ) = none) :
    gate (MultiTapePTM.ofDeterministic M) w b σ i
      ((Encoding.NativeChecked.parse (k := k) e (b, previousWord)).map fun raw => raw.toView b)
      (fun h δ => (Encoding.NativeChecked.parse (k := k) e (b, providerWords h δ)).map
        fun raw => raw.toView b) = none := by
  classical
  rcases hfailed with hp | ⟨h, δ, hp⟩
  · simp [gate, hp]
  · have hnot : ¬∀ h' δ',
        (Encoding.NativeChecked.parse (k := k) e (b, providerWords h' δ')).isSome = true := by
      intro hall
      have hsome := hall h δ
      simp [hp] at hsome
    cases hprevious : Encoding.NativeChecked.parse (k := k) e (b, previousWord) with
    | none => simp [gate]
    | some previous => simp [gate, hnot]

/-- On all label words of the label width, the complete native local supplier emits exactly the
encoded existing block gate applied to the checked decoded words. Provider failure propagates at
every port. -/
theorem finish_prepareWords_eq_gate {q : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q) (words : Assignments.Words k)
    (hlength : words.previous.length = Encoding.width k s b) :
    (CheckedGate.machine M e).finish ((CheckedGate.machine M e).runFrom w
      (prepareWords e (w.length, b, σ, i, words)) b) =
      List.ofFn (Encoding.encode e (gate (MultiTapePTM.ofDeterministic M) w b
        (scheduleOfNat k q σ) i
        ((Encoding.NativeChecked.parse (k := k) e (b, words.previous)).map fun raw => raw.toView b)
        (fun h δ => (Encoding.NativeChecked.parse (k := k) e (b, words.providers h δ)).map
          fun raw => raw.toView b))) := by
  classical
  cases hcombined : Providers.Labels.combine e
      (b, ScheduleRead.providerMap k (σ, i), words.previous, words.providers) with
  | none =>
    have hfailed := (Providers.Labels.combine_eq_none_iff e b
      (ScheduleRead.providerMap k (σ, i)) words.previous words.providers).mp hcombined
    have hgate := gate_eq_none_of_failed_parse M e w b (scheduleOfNat k q σ) i
      words.previous words.providers hfailed
    rw [finish_prepareWords_of_combined_none M e w w.length b σ i b words hlength hcombined,
      hgate, ofFn_encode_none]
  | some combined =>
    cases hprevious : Encoding.NativeChecked.parse (k := k) e (b, words.previous) with
    | none =>
      have hnone := (Providers.Labels.combine_eq_none_iff e b
        (ScheduleRead.providerMap k (σ, i)) words.previous words.providers).mpr (Or.inl hprevious)
      rw [hcombined] at hnone
      contradiction
    | some previous =>
      let empty : RawResult k Q := (none, fun _ => 0, .empty, fun _ => [])
      let providers : Providers.ProviderValues k Q := fun h δ =>
        (Encoding.NativeChecked.parse (k := k) e (b, words.providers h δ)).getD empty
      have hproviders (h : Fin k) (δ : Fin 3) :
          Encoding.NativeChecked.parse (k := k) e (b, words.providers h δ) =
            some (providers h δ) := by
        cases hparse : Encoding.NativeChecked.parse (k := k) e (b, words.providers h δ) with
        | none =>
          have hnone := (Providers.Labels.combine_eq_none_iff e b
            (ScheduleRead.providerMap k (σ, i)) words.previous words.providers).mpr
              (Or.inr ⟨h, δ, hparse⟩)
          rw [hcombined] at hnone
          contradiction
        | some value => simp [providers, hparse]
      have hf := finish_prepareWords_of_parses M e w b σ i words previous providers hprevious
        hproviders
      simpa only [hprevious, hproviders, Option.map_some] using hf

/-- On label words that encode values, the native local supplier emits the encoded existing block
gate applied to those values: a caller that stores encoded views needs no parsing argument. -/
theorem finish_prepareWords_encode {q : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q) (previous : Option (View k Q b))
    (providers : Fin k → Fin 3 → Option (View k Q b)) :
    (CheckedGate.machine M e).finish ((CheckedGate.machine M e).runFrom w
      (prepareWords e (w.length, b, σ, i, ⟨List.ofFn (Encoding.encode e previous),
        fun h δ => List.ofFn (Encoding.encode e (providers h δ))⟩)) b) =
      List.ofFn (Encoding.encode e (gate (MultiTapePTM.ofDeterministic M) w b
        (scheduleOfNat k q σ) i previous providers)) := by
  rw [finish_prepareWords_eq_gate M e w b σ i _ (List.length_ofFn)]
  simp only [Encoding.NativeChecked.parse_ofFn,
    decodeChecked_encode _ _ (Encoding.decode_encode e)]

/-- On every assignment, the complete native local supplier emits exactly the encoded existing
block gate applied to the checked decoded labels. The only capacity premise pays the previous
word used to serialize rejection; provider failure still propagates at every port. -/
theorem finish_prepare_eq_gate {q : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (limit counter stride : ℕ) (hcapacity : Encoding.width k s b ≤ limit.size) :
    let words := Assignments.labels k ⟨limit, counter, stride, Encoding.width k s b⟩
    (CheckedGate.machine M e).finish ((CheckedGate.machine M e).runFrom w
      (prepare e (w.length, b, σ, i, limit, counter, stride)) b) =
      List.ofFn (Encoding.encode e (gate (MultiTapePTM.ofDeterministic M) w b
        (scheduleOfNat k q σ) i
        ((Encoding.NativeChecked.parse (k := k) e (b, words.previous)).map fun raw => raw.toView b)
        (fun h δ => (Encoding.NativeChecked.parse (k := k) e (b, words.providers h δ)).map
          fun raw => raw.toView b))) :=
  finish_prepareWords_eq_gate M e w b σ i _
    (AssignmentLabels.length_label _ _ _ _ _ (by simpa using hcapacity))

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier
