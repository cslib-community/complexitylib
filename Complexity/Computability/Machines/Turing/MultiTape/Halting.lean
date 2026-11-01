/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Partialize
public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Decode

/-!
# The halting problem is undecidable

Every word `w` describes a machine, `Turing.MultiTapeTM.Universal.decodeDesc w`, and the encoded
description `eDesc (desc eS eBit tm)` of a machine `tm` with a binary alphabet and finitely many
states describes `tm` itself. The halting problem asks, of a pair of words `(w, x)`, whether the
machine described by `w` halts on `x`, read as symbols under the coding
`Turing.MultiTapeTM.Universal.eBit` (`Turing.MultiTapeTM.haltingProblem`); the acceptance problem
asks whether it halts with output `[true]` (`Turing.MultiTapeTM.acceptanceProblem`). Their
self-application forms ask the same of a word run on itself
(`Turing.MultiTapeTM.selfHaltingProblem`, `Turing.MultiTapeTM.selfAcceptanceProblem`). None of the
four is decidable [Turing][Turing1936] [Sipser, Theorems 4.11 and 5.1][Sipser2013].

All four results come from one diagonal argument, that of the time hierarchy theorem
(`Cslib.Complexity.not_forall_halted_diagonal`, in
`Complexity.Computability.Complexity.Classes.Hierarchy`) without the clock. A machine run on its own
description can make its behavior depend on any computable verdict about that description
(`Turing.MultiTapeTM.exists_self_desc`): `Turing.MultiTapeTM.partialize` turns a total machine
computing the verdict, followed by a choice of a partial result for each verdict, into a machine
that diverges or halts with the chosen output. So no computable verdict is `true` on the
descriptions of all machines behaving in one way on their own descriptions and `false` on those of
all machines behaving in another way (`Turing.MultiTapeTM.not_separates_self_desc`): some machine
behaves, on its own description, in the way its verdict excludes. Halting separates divergence
from halting with output `[]`, and acceptance separates halting with output `[false]` from halting
with output `[true]`, so neither is decidable even on descriptions of machines
(`Turing.MultiTapeTM.halting_problem`, `Turing.MultiTapeTM.acceptance_problem` and their
self-application forms). The undecidability of the four sets of words follows
(`Turing.MultiTapeTM.not_isDecidable_of_separates_self_desc`), the encoded-pair forms through the
mapping reduction `w ↦ (w, w)`.

`Turing.MultiTapeTM.not_isDecidable_of_separates_self_desc` is Rice's theorem for the behavior of
machines on their own descriptions. The classical theorem [Rice][Rice1953], about the behavior on
all inputs, is `Turing.MultiTapeTM.rice` in
`Complexity.Computability.Machines.Turing.MultiTape.Halting.Rice`; it needs in addition an s-m-n
theorem for descriptions (`Turing.MultiTapeTM.Universal.hardwire`).

Mathlib proves corresponding theorems for its own model of computation, partial recursive codes.
`ComputablePred.halting_problem` fixes the input: for each `n`, no computable predicate decides
whether the code `c` halts on `n`. Its native counterpart, for each input of bits, is
`Turing.MultiTapeTM.not_isDecidable_halts`, a corollary of Rice's theorem in
`Complexity.Computability.Machines.Turing.MultiTape.Halting.Rice`; the halting problem here,
`Turing.MultiTapeTM.haltingProblem`, takes the input as part of the instance instead.
`ComputablePred.rice` and `ComputablePred.rice₂` are Rice's theorem for codes. Transferring these
results would need simulations in both directions between codes and the machines of this library,
which are not developed here, so the native results are proved directly, on the universal
simulation of Christian Reitwiessner (`Turing.MultiTapeTM.Universal.simulate_desc`) and the decoder
of descriptions (`Turing.MultiTapeTM.Universal.decodeDesc_eDesc`).

## Main definitions

* `Turing.MultiTapeTM.haltingProblem`, `Turing.MultiTapeTM.selfHaltingProblem`: halting.
* `Turing.MultiTapeTM.acceptanceProblem`, `Turing.MultiTapeTM.selfAcceptanceProblem`: acceptance.

## Main results

* `Turing.MultiTapeTM.IsComputable.exists_partialize`: computable partial results are the
  behaviors of machines.
* `Turing.MultiTapeTM.exists_self_desc`, `Turing.MultiTapeTM.not_separates_self_desc`:
  self-reference by self-application, and the diagonal argument.
* `Turing.MultiTapeTM.halting_problem`, `Turing.MultiTapeTM.halting_problem_self`: no computable
  function decides halting on descriptions of machines.
* `Turing.MultiTapeTM.acceptance_problem`, `Turing.MultiTapeTM.acceptance_problem_self`: no
  computable function decides acceptance on descriptions of machines.
* `Turing.MultiTapeTM.not_isDecidable_haltingProblem`,
  `Turing.MultiTapeTM.not_isDecidable_selfHaltingProblem`,
  `Turing.MultiTapeTM.not_isDecidable_acceptanceProblem`,
  `Turing.MultiTapeTM.not_isDecidable_selfAcceptanceProblem`: the four problems are undecidable.
* `Turing.MultiTapeTM.not_isDecidable_of_separates_self_desc`: Rice's theorem for the behavior of
  machines on their own descriptions.

## References

* [A. M. Turing, *On Computable Numbers, with an Application to the
  Entscheidungsproblem*][Turing1936]
* [H. G. Rice, *Classes of Recursively Enumerable Sets and Their Decision Problems*][Rice1953]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Universal

/-! ### Machines from computable partial results -/

/-- **Computable partial results are the behaviors of machines**: if `f` is computable with
results encoded by `encPartial`, some machine with a binary alphabet and finitely many states
halts on `encIn a` with output `o` exactly when `f a = some o`, and diverges when `f a = none`. -/
theorem IsComputable.exists_partialize {α : Type*} {encIn : α ↪ List Bool}
    {f : α → Option (List Bool)} (hf : IsComputable f encIn encPartial) :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (tm : MultiTapeTM k Bool State),
      ∀ a o, tm.Computes (encIn a) o ↔ o ∈ f a := by
  obtain ⟨k, State, _, tm, htm⟩ := isComputable_iff.mp hf
  have := Fintype.ofFinite State
  exact ⟨k, _, inferInstance, tm.partialize, fun a => (htm a).partialize⟩

/-! ### The diagonal argument -/

/-- **Self-reference by self-application.** For every computable verdict `f` on words and every
choice `r` of a partial result for each verdict, some machine with a binary alphabet and finitely
many states, run on its own description `w`, has the partial result `r (f w)`: it halts with
output `o` exactly when `r (f w) = some o`, and diverges when `r (f w) = none`. -/
theorem exists_self_desc {f : List Bool → Bool} (hf : IsComputable f encBits encBool)
    (r : Bool → Option (List Bool)) :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (eS : State ↪ ℕ)
      (tm : MultiTapeTM k Bool State),
      ∀ o, tm.Computes (eDesc (desc eS eBit tm)) o ↔ o ∈ r (f (eDesc (desc eS eBit tm))) := by
  obtain ⟨k, State, _, tm, htm⟩ :=
    ((IsComputable.of_finite (encIn := encBool) (encMid := encPartial) r).comp hf).exists_partialize
  exact ⟨k, State, inferInstance, (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding, tm,
    htm _⟩

/-- **The diagonal argument.** No computable verdict on words is `false` on the description of
every machine whose behavior on its own description is `r₀` and `true` on the description of
every machine whose behavior on its own description is `r₁`: some machine behaves on its own
description as `r₀` when the verdict is `true`, and as `r₁` when it is `false`. A behavior is a
partial result: `none` for divergence, `some o` for halting with output `o`. -/
theorem not_separates_self_desc {f : List Bool → Bool} (hf : IsComputable f encBits encBool)
    (r₀ r₁ : Option (List Bool))
    (h₀ : ∀ ⦃k : ℕ⦄ ⦃State : Type⦄ [Fintype State] (eS : State ↪ ℕ)
      (tm : MultiTapeTM k Bool State), (∀ o, tm.Computes (eDesc (desc eS eBit tm)) o ↔ o ∈ r₀) →
        f (eDesc (desc eS eBit tm)) = false)
    (h₁ : ∀ ⦃k : ℕ⦄ ⦃State : Type⦄ [Fintype State] (eS : State ↪ ℕ)
      (tm : MultiTapeTM k Bool State), (∀ o, tm.Computes (eDesc (desc eS eBit tm)) o ↔ o ∈ r₁) →
        f (eDesc (desc eS eBit tm)) = true) :
    False := by
  obtain ⟨k, State, _, eS, tm, htm⟩ := exists_self_desc hf fun b => if b then r₀ else r₁
  cases hw : f (eDesc (desc eS eBit tm))
  · simp only [hw, Bool.false_eq_true, ↓reduceIte] at htm
    exact Bool.false_ne_true (hw.symm.trans (h₁ eS tm htm))
  · simp only [hw, ↓reduceIte] at htm
    exact Bool.false_ne_true (hw.symm.trans (h₀ eS tm htm)).symm

/-! ### Halting and acceptance on descriptions of machines -/

/-- **The halting problem, in self-application form.** No computable function decides, on the
description of every machine with a binary alphabet and finitely many states, whether the machine
halts on its own description. -/
theorem halting_problem_self :
    ¬∃ f : List Bool → Bool, IsComputable f encBits encBool ∧
      ∀ ⦃k : ℕ⦄ ⦃State : Type⦄ [Fintype State] (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State),
        f (eDesc (desc eS eBit tm)) = true ↔ tm.Halts (eDesc (desc eS eBit tm)) := by
  rintro ⟨f, hf, hdec⟩
  refine not_separates_self_desc hf none (some []) (fun k State _ eS tm h => ?_)
    fun k State _ eS tm h => (hdec eS tm).mpr ((h []).mpr rfl).halts
  rw [← Bool.not_eq_true, hdec eS tm, halts_iff_exists_computes]
  exact fun ⟨o, ho⟩ => nomatch (h o).mp ho

/-- **The halting problem.** No computable function decides, on the description of every machine
with a binary alphabet and finitely many states and every input, whether the machine halts on the
input. -/
theorem halting_problem :
    ¬∃ f : List Bool × List Bool → Bool, IsComputable f (encPair encBits encBits) encBool ∧
      ∀ ⦃k : ℕ⦄ ⦃State : Type⦄ [Fintype State] (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State)
        (x : List Bool), f (eDesc (desc eS eBit tm), x) = true ↔ tm.Halts x :=
  fun ⟨f, hf, hdec⟩ => halting_problem_self ⟨fun w => f (w, w),
    hf.comp ((isComputable_id encBits).prod (isComputable_id encBits)),
    fun _ _ _ eS tm => hdec eS tm _⟩

/-- **The acceptance problem, in self-application form.** No computable function decides, on the
description of every machine with a binary alphabet and finitely many states, whether the machine
halts with output `[true]` on its own description. -/
theorem acceptance_problem_self :
    ¬∃ f : List Bool → Bool, IsComputable f encBits encBool ∧
      ∀ ⦃k : ℕ⦄ ⦃State : Type⦄ [Fintype State] (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State),
        f (eDesc (desc eS eBit tm)) = true ↔ tm.Computes (eDesc (desc eS eBit tm)) [true] := by
  rintro ⟨f, hf, hdec⟩
  refine not_separates_self_desc hf (some [false]) (some [true]) (fun k State _ eS tm h => ?_)
    fun k State _ eS tm h => (hdec eS tm).mpr ((h [true]).mpr rfl)
  rw [← Bool.not_eq_true, hdec eS tm, h]
  simp

/-- **The acceptance problem.** No computable function decides, on the description of every
machine with a binary alphabet and finitely many states and every input, whether the machine halts
with output `[true]` on the input. -/
theorem acceptance_problem :
    ¬∃ f : List Bool × List Bool → Bool, IsComputable f (encPair encBits encBits) encBool ∧
      ∀ ⦃k : ℕ⦄ ⦃State : Type⦄ [Fintype State] (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State)
        (x : List Bool), f (eDesc (desc eS eBit tm), x) = true ↔ tm.Computes x [true] :=
  fun ⟨f, hf, hdec⟩ => acceptance_problem_self ⟨fun w => f (w, w),
    hf.comp ((isComputable_id encBits).prod (isComputable_id encBits)),
    fun _ _ _ eS tm => hdec eS tm _⟩

/-! ### The halting and acceptance problems on words -/

/-- **The halting problem**: the pairs of words `(w, x)` such that the machine described by `w`
halts on `x`. -/
def haltingProblem : Set (List Bool × List Bool) :=
  {p | (decodeDesc p.1).Halts (p.2.map eBit)}

/-- The words `w` such that the machine described by `w` halts on `w`. -/
def selfHaltingProblem : Set (List Bool) :=
  {w | (decodeDesc w).Halts (w.map eBit)}

/-- **The acceptance problem**: the pairs of words `(w, x)` such that the machine described by `w`
halts on `x` with output `[true]`. -/
def acceptanceProblem : Set (List Bool × List Bool) :=
  {p | (decodeDesc p.1).Computes (p.2.map eBit) [eBit true]}

/-- The words `w` such that the machine described by `w` halts on `w` with output `[true]`. -/
def selfAcceptanceProblem : Set (List Bool) :=
  {w | (decodeDesc w).Computes (w.map eBit) [eBit true]}

theorem mem_haltingProblem {p : List Bool × List Bool} :
    p ∈ haltingProblem ↔ (decodeDesc p.1).Halts (p.2.map eBit) :=
  Iff.rfl

theorem mem_selfHaltingProblem {w : List Bool} :
    w ∈ selfHaltingProblem ↔ (decodeDesc w).Halts (w.map eBit) :=
  Iff.rfl

theorem mem_acceptanceProblem {p : List Bool × List Bool} :
    p ∈ acceptanceProblem ↔ (decodeDesc p.1).Computes (p.2.map eBit) [eBit true] :=
  Iff.rfl

theorem mem_selfAcceptanceProblem {w : List Bool} :
    w ∈ selfAcceptanceProblem ↔ (decodeDesc w).Computes (w.map eBit) [eBit true] :=
  Iff.rfl

variable {k : ℕ} {State : Type} [Fintype State] (eS : State ↪ ℕ) (tm : MultiTapeTM k Bool State)

/-- On the description of a machine, the halting problem asks whether the machine halts. -/
theorem desc_mem_haltingProblem_iff (x : List Bool) :
    (eDesc (desc eS eBit tm), x) ∈ haltingProblem ↔ tm.Halts x := by
  rw [mem_haltingProblem, decodeDesc_eDesc, Desc.halts_desc]

/-- On the description of a machine, the self-application form of the halting problem asks
whether the machine halts on its own description. -/
theorem desc_mem_selfHaltingProblem_iff :
    eDesc (desc eS eBit tm) ∈ selfHaltingProblem ↔ tm.Halts (eDesc (desc eS eBit tm)) := by
  rw [mem_selfHaltingProblem, decodeDesc_eDesc, Desc.halts_desc]

/-- On the description of a machine, the acceptance problem asks whether the machine halts with
output `[true]`. -/
theorem desc_mem_acceptanceProblem_iff (x : List Bool) :
    (eDesc (desc eS eBit tm), x) ∈ acceptanceProblem ↔ tm.Computes x [true] := by
  rw [mem_acceptanceProblem, decodeDesc_eDesc, ← List.map_singleton, Desc.computes_desc]

/-- On the description of a machine, the self-application form of the acceptance problem asks
whether the machine halts with output `[true]` on its own description. -/
theorem desc_mem_selfAcceptanceProblem_iff :
    eDesc (desc eS eBit tm) ∈ selfAcceptanceProblem ↔
      tm.Computes (eDesc (desc eS eBit tm)) [true] := by
  rw [mem_selfAcceptanceProblem, decodeDesc_eDesc, ← List.map_singleton, Desc.computes_desc]

/-- **Rice's theorem for the behavior on self-descriptions.** A set of words containing the
description of every machine whose behavior on its own description is `r₁`, and the description of
no machine whose behavior on its own description is `r₀`, is undecidable. -/
theorem not_isDecidable_of_separates_self_desc {P : Set (List Bool)} (r₀ r₁ : Option (List Bool))
    (h₀ : ∀ ⦃k : ℕ⦄ ⦃State : Type⦄ [Fintype State] (eS : State ↪ ℕ)
      (tm : MultiTapeTM k Bool State), (∀ o, tm.Computes (eDesc (desc eS eBit tm)) o ↔ o ∈ r₀) →
        eDesc (desc eS eBit tm) ∉ P)
    (h₁ : ∀ ⦃k : ℕ⦄ ⦃State : Type⦄ [Fintype State] (eS : State ↪ ℕ)
      (tm : MultiTapeTM k Bool State), (∀ o, tm.Computes (eDesc (desc eS eBit tm)) o ↔ o ∈ r₁) →
        eDesc (desc eS eBit tm) ∈ P) :
    ¬IsDecidable P encBits := fun h =>
  let ⟨f, hf, hP⟩ := h.exists_isComputable
  not_separates_self_desc hf r₀ r₁ (fun _ _ _ eS tm h => by simpa [hP] using h₀ eS tm h)
    fun _ _ _ eS tm h => (hP _).mp (h₁ eS tm h)

/-- **The halting problem is undecidable, in self-application form.** -/
theorem not_isDecidable_selfHaltingProblem : ¬IsDecidable selfHaltingProblem encBits :=
  not_isDecidable_of_separates_self_desc none (some [])
    (fun _ _ _ eS tm h hmem => by
      obtain ⟨o, ho⟩ :=
        halts_iff_exists_computes.mp ((desc_mem_selfHaltingProblem_iff eS tm).mp hmem)
      exact nomatch (h o).mp ho)
    fun _ _ _ eS tm h => (desc_mem_selfHaltingProblem_iff eS tm).mpr ((h []).mpr rfl).halts

/-- Running a word on itself is a mapping reduction of the self-application form of halting to
halting. -/
theorem selfHaltingProblem_mappingReducible :
    MappingReducible encBits (encPair encBits encBits) selfHaltingProblem haltingProblem :=
  ⟨fun w => (w, w), (isComputable_id encBits).prod (isComputable_id encBits), fun _ => Iff.rfl⟩

/-- **The halting problem is undecidable.** -/
theorem not_isDecidable_haltingProblem : ¬IsDecidable haltingProblem (encPair encBits encBits) :=
  selfHaltingProblem_mappingReducible.not_isDecidable not_isDecidable_selfHaltingProblem

/-- **The acceptance problem is undecidable, in self-application form.** -/
theorem not_isDecidable_selfAcceptanceProblem : ¬IsDecidable selfAcceptanceProblem encBits :=
  not_isDecidable_of_separates_self_desc (some [false]) (some [true])
    (fun _ _ _ eS tm h hmem => by
      have := (h [true]).mp ((desc_mem_selfAcceptanceProblem_iff eS tm).mp hmem)
      simp at this)
    fun _ _ _ eS tm h => (desc_mem_selfAcceptanceProblem_iff eS tm).mpr ((h [true]).mpr rfl)

/-- Running a word on itself is a mapping reduction of the self-application form of acceptance to
acceptance. -/
theorem selfAcceptanceProblem_mappingReducible :
    MappingReducible encBits (encPair encBits encBits) selfAcceptanceProblem acceptanceProblem :=
  ⟨fun w => (w, w), (isComputable_id encBits).prod (isComputable_id encBits), fun _ => Iff.rfl⟩

/-- **The acceptance problem is undecidable.** -/
theorem not_isDecidable_acceptanceProblem :
    ¬IsDecidable acceptanceProblem (encPair encBits encBits) :=
  selfAcceptanceProblem_mappingReducible.not_isDecidable not_isDecidable_selfAcceptanceProblem

end Turing.MultiTapeTM
