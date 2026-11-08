/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Counting

/-!
# Canonical certificates for labelled terminal branches

An occurrence-index certificate replays a list-choice machine until its first halt, then requires
only zeros in the remaining positions. A running endpoint, out-of-range occurrence or nonzero
terminal padding is invalid for both the accepting and rejecting classifiers.

## Main definitions

* `Turing.MultiTapeCTM.decodeCertificate`: replay and validate an index certificate.
* `Turing.MultiTapeCTM.padCertificate`: uniquely pad a terminal trace to a fixed clock.
* `Turing.MultiTapeCTM.certificateCount`: count valid certificates with a specified verdict.

## Main results

* `Turing.MultiTapeCTM.padCertificate_bijOn`: the actual padding map is a bijection between bounded
  terminal branches and all successful decoder inputs of the fixed length.
* `Turing.MultiTapeCTM.certificateCounts_eq`: both accepting and rejecting counts are preserved.

These are combinatorial results over natural-number indices. No polynomial-time binary checker,
#P membership, reverse verifier-to-machine simulation or GapP characterization is proved here.
Those require separate uniform constructions and resource proofs.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]

The operational machine and occurrence semantics are those of `MultiTape.Counting`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- Decode occurrence indices, allowing only zero padding after the first halt. The result
retains the consumed trace and final configuration. Invalid indices, nonzero terminal padding,
and a running configuration at the end of the certificate all fail. -/
def decodeCertificate (machine : MultiTapeCTM k Symbol State) :
    Cfg k Symbol State input → List ℕ → Option (List ℕ × Cfg k Symbol State input)
  | cfg, word => match cfg.state with
    | none => if word = List.replicate word.length 0 then some ([], cfg) else none
    | some _ => match word with
      | [] => none
      | index :: rest => do
          let next ← machine.step? cfg index
          (machine.decodeCertificate next rest).map fun result => (index :: result.1, result.2)

theorem decodeCertificate_of_halted (machine : MultiTapeCTM k Symbol State)
    {cfg : Cfg k Symbol State input} (h : cfg.Halted) (word : List ℕ) :
    machine.decodeCertificate cfg word =
      if word = List.replicate word.length 0 then some ([], cfg) else none := by
  cases word <;> simp [decodeCertificate, h]

/-- Every terminal branch has exactly the intended all-zero padded certificate. -/
theorem decodeCertificate_append_replicate (machine : MultiTapeCTM k Symbol State)
    {cfg final : Cfg k Symbol State input} {choices : List ℕ}
    (hrun : machine.runBranch cfg choices = some final) (hhalt : final.Halted) (padding : ℕ) :
    machine.decodeCertificate cfg (choices ++ List.replicate padding 0) =
      some (choices, final) := by
  induction choices generalizing cfg with
  | nil =>
    simp only [runBranch_nil, Option.some.injEq] at hrun
    subst cfg
    simp [machine.decodeCertificate_of_halted hhalt]
  | cons index rest ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hrun
    cases hs : cfg.state with
    | none => simp [machine.step?_of_halted hs] at hstep
    | some state =>
      simp [decodeCertificate, hs, hstep, ih hrest]

/-- Successful decoding gives a genuine first-halting branch, with uniquely forced padding. -/
theorem decodeCertificate_sound (machine : MultiTapeCTM k Symbol State)
    {cfg final : Cfg k Symbol State input} {word choices : List ℕ}
    (h : machine.decodeCertificate cfg word = some (choices, final)) :
    machine.runBranch cfg choices = some final ∧ final.Halted ∧
      word = choices ++ List.replicate (word.length - choices.length) 0 := by
  induction word generalizing cfg choices with
  | nil =>
    cases hs : cfg.state with
    | none =>
      simp only [decodeCertificate, hs, List.length_nil, List.replicate_zero, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [hs, Cfg.Halted]
    | some state => simp [decodeCertificate, hs] at h
  | cons index word ih =>
    cases hs : cfg.state with
    | none =>
      rw [machine.decodeCertificate_of_halted hs] at h
      split_ifs at h with hzero
      · obtain ⟨rfl, rfl⟩ := Option.some.inj h
        exact ⟨rfl, hs, by simpa using hzero⟩
    | some state =>
      simp only [decodeCertificate, hs, bind, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at h
      obtain ⟨next, hstep, ⟨rest, final'⟩, hdecode, heq⟩ := h
      cases heq
      obtain ⟨hrun, hhalt, hword⟩ := ih hdecode
      refine ⟨?_, hhalt, ?_⟩
      · simp [runBranch_cons, hstep, hrun]
      · simpa only [List.length_cons, Nat.add_sub_add_right, List.cons_append,
          List.cons.injEq, true_and] using hword

/-- Decoding is exact replay plus canonical zero padding, rather than an assumed counting
certificate. Both acceptance and rejection can use its same validity condition. -/
theorem decodeCertificate_eq_some_iff (machine : MultiTapeCTM k Symbol State)
    (cfg final : Cfg k Symbol State input) (word choices : List ℕ) :
    machine.decodeCertificate cfg word = some (choices, final) ↔
      machine.runBranch cfg choices = some final ∧ final.Halted ∧
        word = choices ++ List.replicate (word.length - choices.length) 0 := by
  constructor
  · exact machine.decodeCertificate_sound
  · rintro ⟨hrun, hhalt, hword⟩
    rw [hword]
    exact machine.decodeCertificate_append_replicate hrun hhalt _

/-- Pad a terminal occurrence trace to a fixed clock. Padding is not an actual machine step. -/
def padCertificate (fuel : ℕ) (choices : List ℕ) : List ℕ :=
  choices ++ List.replicate (fuel - choices.length) 0

/-- Canonical padding is injective on terminal branches, including branches of different lengths. -/
theorem padCertificate_injOn (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) :
    Set.InjOn (padCertificate fuel) (machine.branches fuel cfg) := by
  intro left hleft right hright heq
  obtain ⟨_, finalLeft, hrunLeft, hhaltLeft⟩ :=
    (machine.mem_branches_iff cfg fuel left).mp hleft
  obtain ⟨_, finalRight, hrunRight, hhaltRight⟩ :=
    (machine.mem_branches_iff cfg fuel right).mp hright
  have hleft := machine.decodeCertificate_append_replicate hrunLeft hhaltLeft
    (fuel - left.length)
  have hright := machine.decodeCertificate_append_replicate hrunRight hhaltRight
    (fuel - right.length)
  change machine.decodeCertificate cfg (padCertificate fuel left) = _ at hleft
  change machine.decodeCertificate cfg (padCertificate fuel right) = _ at hright
  rw [heq] at hleft
  exact congrArg Prod.fst (Option.some.inj (hleft.symm.trans hright))

/-- The finite set of canonical fixed-length certificates. Its membership theorem identifies it
with the independently defined decoder's successful inputs. -/
def certificates (machine : MultiTapeCTM k Symbol State)
    (fuel : ℕ) (cfg : Cfg k Symbol State input) : Finset (List ℕ) :=
  (machine.branches fuel cfg).image (padCertificate fuel)

theorem mem_certificates_iff (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) (word : List ℕ) :
    word ∈ machine.certificates fuel cfg ↔
      word.length = fuel ∧ (machine.decodeCertificate cfg word).isSome := by
  constructor
  · intro h
    obtain ⟨choices, hchoices, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hlen, final, hrun, hhalt⟩ := (machine.mem_branches_iff cfg fuel choices).mp hchoices
    constructor
    · simp [padCertificate, Nat.add_sub_of_le hlen]
    · rw [padCertificate, machine.decodeCertificate_append_replicate hrun hhalt]
      rfl
  · rintro ⟨hlen, hdecode⟩
    obtain ⟨⟨choices, final⟩, hdecode⟩ := Option.isSome_iff_exists.mp hdecode
    obtain ⟨hrun, hhalt, hword⟩ := machine.decodeCertificate_sound hdecode
    have hbound : choices.length ≤ fuel := by grind
    refine Finset.mem_image.mpr ⟨choices,
      (machine.mem_branches_iff cfg fuel choices).mpr ⟨hbound, final, hrun, hhalt⟩, ?_⟩
    simpa only [padCertificate, hlen] using hword.symm

/-- The actual trace-to-certificate map is a bijection onto all successful fixed-length decoder
inputs. No extra copies are introduced by terminal padding or by distinct equal-effect choices. -/
theorem padCertificate_bijOn (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) :
    Set.BijOn (padCertificate fuel) (machine.branches fuel cfg)
      {word | word.length = fuel ∧ (machine.decodeCertificate cfg word).isSome} := by
  refine ⟨?_, machine.padCertificate_injOn cfg fuel, ?_⟩
  · intro choices hchoices
    exact (machine.mem_certificates_iff cfg fuel _).mp
      (Finset.mem_image.mpr ⟨choices, hchoices, rfl⟩)
  · intro word hword
    exact Finset.mem_image.mp ((machine.mem_certificates_iff cfg fuel word).mpr hword)

/-- Canonical certificates and terminal branches have exactly the same cardinality. -/
theorem card_certificates (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) :
    (machine.certificates fuel cfg).card = (machine.branches fuel cfg).card :=
  Finset.card_image_of_injOn (machine.padCertificate_injOn cfg fuel)

/-- The certificate classifier retains decoder validity for either terminal verdict. In
particular, complementing the verdict still excludes every invalid certificate. -/
def certificateAccepts (machine : MultiTapeCTM k Symbol State) (verdict : List Symbol → Bool)
    (cfg : Cfg k Symbol State input) (word : List ℕ) : Bool :=
  (machine.decodeCertificate cfg word).any fun result => verdict result.2.output

theorem certificateAccepts_of_invalid (machine : MultiTapeCTM k Symbol State)
    (verdict : List Symbol → Bool) {cfg : Cfg k Symbol State input} {word : List ℕ}
    (h : machine.decodeCertificate cfg word = none) :
    machine.certificateAccepts verdict cfg word = false := by
  simp [certificateAccepts, h]

/-- Count fixed-length canonical certificates with the specified terminal verdict. -/
def certificateCount (machine : MultiTapeCTM k Symbol State) (verdict : List Symbol → Bool)
    (fuel : ℕ) (cfg : Cfg k Symbol State input) : ℕ :=
  ((machine.certificates fuel cfg).filter (machine.certificateAccepts verdict cfg ·)).card

/-- The decoder's exact bijection preserves every terminal verdict, hence both accepting and
rejecting counts. This is a combinatorial result, with no efficient binary checker claimed. -/
theorem certificateCount_eq_branchCount (machine : MultiTapeCTM k Symbol State)
    (verdict : List Symbol → Bool) (fuel : ℕ) (cfg : Cfg k Symbol State input) :
    machine.certificateCount verdict fuel cfg = machine.branchCount verdict fuel cfg := by
  unfold certificateCount certificates
  rw [Finset.filter_image, Finset.card_image_of_injOn
    ((machine.padCertificate_injOn cfg fuel).mono (Finset.filter_subset _ _))]
  unfold branchCount
  congr 1
  apply Finset.filter_congr
  intro choices hchoices
  obtain ⟨_, final, hrun, hhalt⟩ := (machine.mem_branches_iff cfg fuel choices).mp hchoices
  simp [certificateAccepts, padCertificate,
    machine.decodeCertificate_append_replicate hrun hhalt, hrun]

/-- The two valid-certificate classifiers recover the accepting and rejecting machine counts
separately; invalid certificates contribute to neither side. -/
theorem certificateCounts_eq (machine : MultiTapeCTM k Bool State)
    {input : List Bool} (fuel : ℕ) (cfg : Cfg k Bool State input) :
    machine.certificateCount (· == [true]) fuel cfg = machine.acceptCount fuel cfg ∧
      machine.certificateCount (fun out => !(out == [true])) fuel cfg =
        machine.rejectCount fuel cfg :=
  ⟨machine.certificateCount_eq_branchCount _ _ _, machine.certificateCount_eq_branchCount _ _ _⟩

end Turing.MultiTapeCTM
