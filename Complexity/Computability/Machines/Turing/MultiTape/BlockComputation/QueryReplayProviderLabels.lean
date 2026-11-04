/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import
  Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayProviders
public import
  Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeChecked
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds

/-!
# Checked labels for native provider-window assembly

The input contains actual previous and provider label words, the runtime block width and a
fixed finite port map. Every label must pass the exact canonical-code parser, including labels
whose port map entry is `none`. Only after all checks succeed are decoded windows passed to the
native provider assembler. Rejected labels cannot become successful default windows.

These words are gate-assignment data, not a stored copy of the simulated machine's original
input. Acquiring assignment labels and computing the port map remain caller operations.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Providers.Labels

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- Actual provider label words, indexed by fixed work tape and neighboring block. -/
abbrev ProviderWords (k : ℕ) := Fin k → Fin 3 → List Bool

/-- Binary block width, port choices, previous label and every provider label. -/
abbrev Args (k : ℕ) := ℕ × PortMap k × List Bool × ProviderWords k

/-- Each actual label word is charged in the fixed finite family encoding. -/
@[expose] noncomputable def encProviderWords : ProviderWords k ↪ List Bool :=
  encPi (encPi encBits)

/-- Runtime width and all actual gate-assignment data, with no implicit label table. -/
@[expose] noncomputable def encArgs : Args k ↪ List Bool :=
  encPair encNat (encPair encPortMap (encPair encBits encProviderWords))

/-- Reject unless the previous label and every provider label are accepted, even when a port
is unused. Default values are extracted only under this complete acceptance guard. -/
@[expose] noncomputable def combine (e : Q ≃ Fin s) : Args k → Option (RawResult k Q) :=
  fun (b, ports, previousWord, providerWords) =>
    let empty : RawResult k Q := (none, fun _ => 0, .empty, fun _ => [])
    let previous := Encoding.NativeChecked.parse e (b, previousWord)
    let providers := fun h d => Encoding.NativeChecked.parse e (b, providerWords h d)
    if previous.isSome && decide (∀ h d, (providers h d).isSome = true) then
      some (Providers.combine (b, ports, previous.getD empty,
        fun h d => (providers h d).getD empty))
    else none

variable [Finite Q]

/-- Complete canonical validation and window assembly use native space linear in the actual
encoded arguments. Only the fixed tape and three-port families are enumerated. -/
theorem combine_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (combine (k := k) e) encArgs
      (encOption (encRawResult (k := k) (Q := Q))) (fun a => (encArgs a).length) := by
  classical
  let empty : RawResult k Q := (none, fun _ => 0, .empty, fun _ => [])
  have hb := fst encNat (encPair (encPortMap (k := k))
    (encPair encBits (encProviderWords (k := k))))
  have hrest := snd encNat (encPair (encPortMap (k := k))
    (encPair encBits (encProviderWords (k := k))))
  have hports := hrest.fst'
  have hpreviousWord := hrest.snd'.fst'
  have hproviderWords := hrest.snd'.snd'
  have hprevious := budget_comp_linear (Encoding.NativeChecked.parse_inSpace (k := k) e)
    (budget_prod hb hpreviousWord)
  have hprovider (h : Fin k) (d : Fin 3) :=
    budget_comp_linear (Encoding.NativeChecked.parse_inSpace (k := k) e)
      (budget_prod hb (budget_comp_linear
        (of_inO (ComputableInO.pi_apply encBits d))
        (budget_comp_linear (of_inO (ComputableInO.pi_apply (encPi encBits) h)) hproviderWords)))
  have hget : ComputableInSpace (fun o : Option (RawResult k Q) => o.getD empty)
      (encOption (encRawResult (k := k) (Q := Q))) (encRawResult (k := k) (Q := Q))
      (fun o => (encOption (encRawResult (k := k) (Q := Q)) o).length) :=
    of_inO (ComputableInDegree.getD (enc₁ := encRawResult) empty).inO_one
  have hisSome : ComputableInSpace (fun o : Option (RawResult k Q) => o.isSome)
      (encOption (encRawResult (k := k) (Q := Q))) encBool
      (fun o => (encOption (encRawResult (k := k) (Q := Q)) o).length) :=
    of_inO (ComputableInDegree.isSome (encRawResult (k := k) (Q := Q))).inO_one
  have hpreviousRaw := budget_comp_linear hget hprevious
  have hproviderRaw := pi_linear (Index := Fin k) fun h =>
    pi_linear (Index := Fin 3) fun d => budget_comp_linear hget (hprovider h d)
  have hflags := pi_linear (Index := Fin k) fun h =>
    pi_linear (Index := Fin 3) fun d => budget_comp_linear hisSome (hprovider h d)
  have hall := budget_finite (encC := encBool)
    (fun flags : Fin k → Fin 3 → Bool => decide (∀ h d, flags h d = true)) hflags
  have hguard := budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
    (budget_prod (budget_comp_linear hisSome hprevious) hall)
  have hargs := budget_prod hb (budget_prod hports (budget_prod hpreviousRaw hproviderRaw))
  have hcombined := budget_comp_linear (Providers.combine_inSpace (k := k) (Q := Q)) hargs
  have hsome := budget_comp_linear
    (of_inO (ComputableInDegree.optionSome (enc₁ := encRawResult (k := k) (Q := Q))
      (enc := encOption (encRawResult (k := k) (Q := Q)))).inO_one) hcombined
  refine (budget_ite hguard hsome
    (budget_const (encB := encOption (encRawResult (k := k) (Q := Q))) none (.refl _))).of_enc_eq ?_
  intro a
  rcases a with ⟨b, ports, previousWord, providerWords⟩
  simp only [combine, empty]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Providers.Labels
