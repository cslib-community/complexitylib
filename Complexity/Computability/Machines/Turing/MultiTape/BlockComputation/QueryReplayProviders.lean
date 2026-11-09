/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAccess
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi

/-!
# Native assembly of provider windows

Each of the three blocks of a work-tape window is selected from its explicit provider buffer.
An absent provider produces a blank prefix by mapping the previous buffer's paid prefix to zero.
All slices are bounded by actual stored buffers; a binary width never creates a fresh list of
that length. The previous control, head residues and output summary are retained exactly.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Providers

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k : ℕ} {Q : Type}

/-- For each tape and destination block, the supplying block of its provider, or a blank source. -/
abbrev PortMap (k : ℕ) := Fin k → Fin 3 → Option (Fin 3)

/-- Explicit local data for the fixed family of tape/block provider nodes. -/
abbrev ProviderValues (k : ℕ) (Q : Type) := Fin k → Fin 3 → RawResult k Q

/-- Runtime width, provider-port map, previous value and every supplied provider value. -/
abbrev Args (k : ℕ) (Q : Type) := ℕ × PortMap k × RawResult k Q × ProviderValues k Q

/-- Select an actual stored block, or blank an actual prefix of the previous window. -/
@[expose] def block (b : ℕ) (ports : PortMap k) (previous : RawResult k Q)
    (providers : ProviderValues k Q) (h : Fin k) (d : Fin 3) : List ℕ :=
  let (_, _, _, previousCells) := previous
  match ports h d with
  | none => ((previousCells h).take b).map (fun _ => 0)
  | some p =>
    let (_, _, _, providerCells) := providers h d
    ((providerCells h).drop (p.val * b)).take b

/-- Assemble the three destination blocks and retain the previous finite control record. -/
@[expose] def combine : Args k Q → RawResult k Q :=
  fun (b, ports, previous, providers) =>
    let (control, residues, track, _) := previous
    (control, residues, track, fun h =>
      block b ports previous providers h 0 ++ block b ports previous providers h 1 ++
        block b ports previous providers h 2)

/-- The fixed provider ports are encoded individually, independently of runtime windows. -/
@[expose] noncomputable def encPortMap : PortMap k ↪ List Bool :=
  encPi (encPi (encOption (encFinite (Fin 3))))

variable [Finite Q]

/-- Every provider value is stored explicitly in a fixed tape/block family. -/
@[expose] noncomputable def encProviderValues : ProviderValues k Q ↪ List Bool :=
  encPi (encPi encRawResult)

/-- Binary width and all actual buffers, including the previous value used to pay blank blocks. -/
@[expose] noncomputable def encArgs : Args k Q ↪ List Bool :=
  encPair encNat (encPair encPortMap (encPair encRawResult encProviderValues))

private theorem zeroMap_inSpace : ComputableInSpace (fun l : List ℕ => l.map (fun _ => 0))
    (encList encNat) (encList encNat) (fun l => (encList encNat l).length) := by
  have hid : ComputableInSpace (fun l : List ℕ => l) (encList encNat) (encList encNat)
      (fun l => (encList encNat l).length) := of_inO ComputableInDegree.id'.inO_one
  have hstep : ComputableInSpace (fun p : List ℕ × ℕ => p.1 ++ [0])
      (encPair (encList encNat) encNat) (encList encNat)
      (fun p => (encPair (encList encNat) encNat p).length) :=
    budget_snoc (fst _ _) (budget_const 0 (.refl _))
  have hfold (l out : List ℕ) :
      l.foldl (fun acc _ => acc ++ [0]) out = out ++ l.map (fun _ => 0) := by
    induction l generalizing out with
    | nil => simp
    | cons n l ih => simp [List.foldl_cons, ih, List.append_assoc]
  have hmap (l : List ℕ) : (encList encNat (l.map (fun _ => 0))).length ≤
      (encList encNat l).length :=
    length_encList_map_le encNat encNat (by intro n _; simp)
  have hstate (l : List ℕ) (i : ℕ) (_hi : i ≤ l.length) :
      (encList encNat ((l.take i).foldl (fun acc _ => acc ++ [0]) [])).length ≤
        (encList encNat l).length := by
    rw [hfold, List.nil_append]
    exact (hmap _).trans (length_encList_take_le encNat l i)
  have hspace (l : List ℕ) (i : ℕ) (hi : i < l.length) :
      (encPair (encList encNat) encNat
        ((l.take i).foldl (fun acc _ => acc ++ [0]) [], l[i])).length ≤
          4 * ((encList encNat l).length + 1) := by
    have ha := length_le_encList_of_mem encNat (List.getElem_mem hi)
    have hs := hstate l i hi.le
    simp only [length_encPair]
    omega
  have hf := ComputableInSpace.foldl hid (budget_const [] (.refl _)) hstep hspace hstate
  refine hf.weaken (.of_le_linear 16 16 fun _ => by omega) |>.of_enc_eq ?_
  intro l
  rw [hfold, List.nil_append]

private theorem block_inSpace (h : Fin k) (d : Fin 3) : ComputableInSpace
    (fun a : Args k Q => block a.1 a.2.1 a.2.2.1 a.2.2.2 h d) encArgs (encList encNat)
    (fun a => (encArgs a).length) := by
  have hb := fst encNat (encPair (encPortMap (k := k))
    (encPair (encRawResult (k := k) (Q := Q)) (encProviderValues (k := k) (Q := Q))))
  have hrest := snd encNat (encPair (encPortMap (k := k))
    (encPair (encRawResult (k := k) (Q := Q)) (encProviderValues (k := k) (Q := Q))))
  have hports := hrest.fst'
  have hprevious := hrest.snd'.fst'
  have hproviders := hrest.snd'.snd'
  have hport := budget_comp_linear
    (of_inO (ComputableInO.pi_apply (encOption (encFinite (Fin 3))) d))
    (budget_comp_linear (of_inO (ComputableInO.pi_apply
      (encPi (encOption (encFinite (Fin 3)))) h)) hports)
  have hpreviousCells := budget_comp_linear (of_inO (ComputableInO.pi_apply (encList encNat) h))
    hprevious.snd'.snd'.snd'
  have hblank := budget_comp_linear zeroMap_inSpace
    (budget_comp_linear (listTake encNat) (budget_prod hpreviousCells hb))
  have hprovider := budget_comp_linear
    (of_inO (ComputableInO.pi_apply (encRawResult (k := k) (Q := Q)) d))
    (budget_comp_linear
      (of_inO (ComputableInO.pi_apply (encPi (encRawResult (k := k) (Q := Q))) h)) hproviders)
  have hproviderCells := budget_comp_linear (of_inO (ComputableInO.pi_apply (encList encNat) h))
    hprovider.snd'.snd'.snd'
  have hpair := fst (encArgs (k := k) (Q := Q)) (encFinite (Fin 3))
  have hselected := budget_comp_linear (listTake encNat)
    (budget_prod (budget_comp_linear (listDrop encNat)
      (budget_prod (budget_comp_linear hproviderCells hpair)
        (budget_natMul (budget_finite (encC := encNat) Fin.val
          (snd (encArgs (k := k) (Q := Q)) (encFinite (Fin 3))))
          (budget_comp_linear hb hpair)))) (budget_comp_linear hb hpair))
  have hid : ComputableInSpace (fun a : Args k Q => a) encArgs encArgs
      (fun a => (encArgs a).length) := of_inO ComputableInDegree.id'.inO_one
  refine (budget_comp_linear (optionElimSnd hblank hselected) (budget_prod hid hport)).of_enc_eq ?_
  intro a
  cases hp : a.2.1 h d <;> simp [block, hp]

/-- Uniform native assembly, charging every supplied buffer and retaining the control record
without a lookup over possible window values. -/
theorem combine_inSpace : ComputableInSpace (combine (k := k) (Q := Q)) encArgs encRawResult
    (fun a => (encArgs a).length) := by
  have hprevious := (snd encNat (encPair (encPortMap (k := k))
    (encPair (encRawResult (k := k) (Q := Q)) (encProviderValues (k := k) (Q := Q))))).snd'.fst'
  have hcells := pi_linear (Index := Fin k) fun h =>
    budget_comp_linear (of_inO (ComputableInDegree.listAppend encNat).inO_one)
      (budget_prod (block_inSpace (Q := Q) h 0)
        (budget_comp_linear (of_inO (ComputableInDegree.listAppend encNat).inO_one)
          (budget_prod (block_inSpace (Q := Q) h 1) (block_inSpace (Q := Q) h 2))))
  refine (budget_prod hprevious.fst'
    (budget_prod hprevious.snd'.fst' (budget_prod hprevious.snd'.snd'.fst' hcells))).of_enc_eq ?_
  rintro ⟨b, ports, ⟨control, residues, track, cells⟩, providers⟩
  simp only [combine, encRawResult, List.append_assoc]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Providers
