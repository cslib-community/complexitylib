/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PostCorrespondence.Basic
public import CslibFrontier.Foundations.Data.List.UnaryCode
import CslibFrontier.Foundations.Data.List.Append

/-!
# Letter codings of correspondence problems

A substitution `c : α → List β` acts on dominoes letter by letter. When it is injective on words,
it preserves PCP and MPCP solvability in both directions. Two instances give the alphabet changes
of PCP:

* the unary code `boolCode a = 1^{encode a} 0` reduces PCP over any `Primcodable` alphabet to PCP
  over `Bool`;
* the letter map `true ↦ a`, `false ↦ b` with `a ≠ b` reduces PCP over `Bool` to PCP over any
  `Primcodable` alphabet with two distinct letters.

## Main definitions

* `Cslib.PostCorrespondence.Domino.subst`, `Cslib.PostCorrespondence.MInstance.subst`: a
  substitution applied to a domino and to an MPCP instance.
* `Cslib.PostCorrespondence.boolCode`: the binary code of a letter.

## Main results

* `Cslib.PostCorrespondence.solvable_map_subst_iff`,
  `Cslib.PostCorrespondence.MInstance.solvable_subst_iff`: substitutions injective on words
  preserve solvability.
* `Cslib.PostCorrespondence.solvable_manyOneReducible_bool`,
  `Cslib.PostCorrespondence.solvable_bool_manyOneReducible`: PCP over `Bool` and PCP over any
  alphabet with two distinct letters are many-one equivalent.
* `Cslib.PostCorrespondence.mSolvable_manyOneReducible_bool`,
  `Cslib.PostCorrespondence.mSolvable_bool_manyOneReducible`: the same for MPCP.
-/

public section

namespace Cslib.PostCorrespondence

variable {α β : Type*}

/-- Apply the substitution `c`, a map from letters to words, to both words of a domino. -/
def Domino.subst (c : α → List β) (d : Domino α) : Domino β :=
  ⟨d.top.flatMap c, d.bottom.flatMap c⟩

/-- Apply the substitution `c` to every domino of an MPCP instance. -/
def MInstance.subst (c : α → List β) (I : MInstance α) : MInstance β :=
  ⟨I.start.subst c, I.dominoes.map (Domino.subst c)⟩

theorem tops_map_subst (c : α → List β) (ds : List (Domino α)) :
    tops (ds.map (Domino.subst c)) = (tops ds).flatMap c := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.map_cons, tops_cons, tops_cons, ih, List.flatMap_append]; rfl

theorem bottoms_map_subst (c : α → List β) (ds : List (Domino α)) :
    bottoms (ds.map (Domino.subst c)) = (bottoms ds).flatMap c := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [List.map_cons, bottoms_cons, bottoms_cons, ih, List.flatMap_append]; rfl

private theorem exists_preimages {f : α → β} {P : List α} :
    ∀ {l : List β}, (∀ b ∈ l, b ∈ P.map f) → ∃ l' : List α, (∀ a ∈ l', a ∈ P) ∧ l'.map f = l
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩
  | b :: l, h => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (h b List.mem_cons_self)
    obtain ⟨l', hl', rfl⟩ := exists_preimages fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨a :: l', fun x hx => ?_, rfl⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hl' x hx

/-- A substitution that is injective on words preserves PCP solvability, in both directions. -/
theorem solvable_map_subst_iff {c : α → List β}
    (hc : Function.Injective fun w : List α => w.flatMap c) (P : List (Domino α)) :
    Solvable (P.map (Domino.subst c)) ↔ Solvable P := by
  constructor
  · rintro ⟨es, hne, hmem, heq⟩
    obtain ⟨ds, hds, rfl⟩ := exists_preimages hmem
    refine ⟨ds, fun h => hne (by rw [h, List.map_nil]), hds, hc ?_⟩
    simpa only [tops_map_subst, bottoms_map_subst] using heq
  · rintro ⟨ds, hne, hmem, heq⟩
    refine ⟨ds.map (Domino.subst c), fun h => hne (List.map_eq_nil_iff.mp h),
      fun e he => ?_, by rw [tops_map_subst, bottoms_map_subst, heq]⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact List.mem_map_of_mem (hmem d hd)

/-- A substitution that is injective on words preserves MPCP solvability, in both directions. -/
theorem MInstance.solvable_subst_iff {c : α → List β}
    (hc : Function.Injective fun w : List α => w.flatMap c) (I : MInstance α) :
    (I.subst c).Solvable ↔ I.Solvable := by
  constructor
  · rintro ⟨es, hmem, heq⟩
    obtain ⟨ds, hds, rfl⟩ := exists_preimages hmem
    refine ⟨ds, hds, hc ?_⟩
    simpa only [MInstance.subst, Domino.subst, tops_map_subst, bottoms_map_subst,
      List.flatMap_append] using heq
  · rintro ⟨ds, hmem, heq⟩
    refine ⟨ds.map (Domino.subst c), fun e he => ?_, ?_⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      exact List.mem_map_of_mem (hmem d hd)
    · simp only [MInstance.subst, Domino.subst, tops_map_subst, bottoms_map_subst,
        ← List.flatMap_append, heq]

/-! ### A binary code -/

/-- The binary code of a letter of an encodable alphabet: the unary code of its encoding. -/
def boolCode [Encodable α] (a : α) : List Bool := List.unaryCode (Encodable.encode a)

theorem flatMap_boolCode_injective [Encodable α] :
    Function.Injective fun w : List α => w.flatMap boolCode := by
  intro u v h
  have h' : (u.map Encodable.encode).flatMap List.unaryCode =
      (v.map Encodable.encode).flatMap List.unaryCode := by
    rw [List.flatMap_map, List.flatMap_map]
    exact h
  exact List.map_injective_iff.mpr Encodable.encode_injective (List.flatMap_unaryCode_injective h')

theorem primrec_boolCode [Primcodable α] : Primrec (boolCode : α → List Bool) :=
  List.primrec_unaryCode.comp Primrec.encode

section Primrec

variable [Primcodable α] [Primcodable β]

theorem Domino.primrec_subst {c : α → List β} (hc : Primrec c) : Primrec (Domino.subst c) := by
  have hw : Primrec fun w : List α => w.flatMap c :=
    Primrec.list_flatMap Primrec.id (hc.comp Primrec.snd).to₂
  exact Domino.primrec₂_mk.comp (hw.comp Domino.primrec_top) (hw.comp Domino.primrec_bottom)

theorem primrec_map_subst {c : α → List β} (hc : Primrec c) :
    Primrec fun P : List (Domino α) => P.map (Domino.subst c) :=
  Primrec.list_map Primrec.id ((Domino.primrec_subst hc).comp Primrec.snd).to₂

theorem MInstance.primrec_subst {c : α → List β} (hc : Primrec c) :
    Primrec (MInstance.subst c) :=
  MInstance.primrec₂_mk.comp ((Domino.primrec_subst hc).comp MInstance.primrec_start)
    ((primrec_map_subst hc).comp MInstance.primrec_dominoes)

end Primrec

/-! ### Changing the alphabet -/

/-- PCP over any encodable alphabet reduces to PCP over `Bool`. -/
theorem solvable_manyOneReducible_bool [Primcodable α] :
    (Solvable : List (Domino α) → Prop) ≤₀ (Solvable : List (Domino Bool) → Prop) :=
  ⟨fun P => P.map (Domino.subst boolCode), (primrec_map_subst primrec_boolCode).to_comp,
    fun P => (solvable_map_subst_iff flatMap_boolCode_injective P).symm⟩

/-- MPCP over any encodable alphabet reduces to MPCP over `Bool`. -/
theorem mSolvable_manyOneReducible_bool [Primcodable α] :
    (MInstance.Solvable : MInstance α → Prop) ≤₀ (MInstance.Solvable : MInstance Bool → Prop) :=
  ⟨MInstance.subst boolCode, (MInstance.primrec_subst primrec_boolCode).to_comp,
    fun I => (MInstance.solvable_subst_iff flatMap_boolCode_injective I).symm⟩

/-- The letter map `true ↦ a`, `false ↦ b`, as a substitution. -/
private def pairCode (a b : α) (x : Bool) : List α := [if x then a else b]

private theorem flatMap_pairCode_injective {a b : α} (hab : a ≠ b) :
    Function.Injective fun w : List Bool => w.flatMap (pairCode a b) := by
  refine List.flatMap_singleton_injective (f := fun x : Bool => if x then a else b) ?_
  intro x y h
  cases x <;> cases y <;> simp_all [Ne.symm hab]

/-- PCP over `Bool` reduces to PCP over any alphabet with two distinct letters. -/
theorem solvable_bool_manyOneReducible [Primcodable α] {a b : α} (hab : a ≠ b) :
    (Solvable : List (Domino Bool) → Prop) ≤₀ (Solvable : List (Domino α) → Prop) :=
  ⟨fun P => P.map (Domino.subst (pairCode a b)), (primrec_map_subst (Primrec.dom_finite _)).to_comp,
    fun P => (solvable_map_subst_iff (flatMap_pairCode_injective hab) P).symm⟩

/-- MPCP over `Bool` reduces to MPCP over any alphabet with two distinct letters. -/
theorem mSolvable_bool_manyOneReducible [Primcodable α] {a b : α} (hab : a ≠ b) :
    (MInstance.Solvable : MInstance Bool → Prop) ≤₀ (MInstance.Solvable : MInstance α → Prop) :=
  ⟨MInstance.subst (pairCode a b), (MInstance.primrec_subst (Primrec.dom_finite _)).to_comp,
    fun I => (MInstance.solvable_subst_iff (flatMap_pairCode_injective hab) I).symm⟩

end Cslib.PostCorrespondence
