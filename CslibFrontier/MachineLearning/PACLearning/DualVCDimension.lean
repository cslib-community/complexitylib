/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.VCDimension
import Mathlib.Combinatorics.SetFamily.DualVC

/-!
# The dual class and Assouad's dual VC bound

The *dual class* of a binary concept class `C` on `α` is the class on the concepts of `C`
(`dualClass C : ConceptClass ↥C Bool`) whose members are the evaluations `c ↦ c x`, one for each
point `x : α`. If `C` is drawn as a binary matrix with a row for each concept and a column for each
point, the dual class consists of the columns.

Assouad's dual VC bound [Assouad1983; MoranYehudayoff2016, Claim 1.5] says that if every finite set
shattered by `C` has at most `d` points, then every finite family of concepts shattered by the dual
class has fewer than `2 ^ (d + 1)` members. Mathlib proves this for finite set families
(`Finset.vcDim_dualFamily_le`). The proof here reduces to Mathlib's bitstring-coding lemma
(`Finset.exists_shatters_of_dualFamily_shatters`). It traces the concepts of a shattered family on
a finite set of witness points, one for each subfamily.

The dual class enters the Moran–Yehudayoff compression scheme through classes of the form
`{g ∘ φ | g ∈ G}`, which test a learned hypothesis `φ r` at a point. A set shattered by such a class
is mapped injectively by `φ` onto a set shattered by `G` (`SetShatters.injOn_of_comp`,
`SetShatters.image_of_comp`), so the size bounds of `G` transfer (`SetShatters.card_le_of_comp`).

## Main definitions

- `dualClass C`: the evaluations `c ↦ c x` on the concepts of `C`.

## Main results

- `SetShatters.card_le_of_comp`: a bound on the shattered finite sets of `G` bounds those of
  `{g ∘ φ | g ∈ G}`.
- `card_le_of_setShatters_dualClass`: **Assouad's dual VC bound**. If the shattered finite sets of
  `C` have at most `d` points, those of `dualClass C` have at most `2 ^ (d + 1) - 1`.
- `hasFiniteVCDim_dualClass`, `vcDim_dualClass_le`: the same bound for `vcDim`.

## References

* [P. Assouad, *Densité et dimension*][Assouad1983]
* [S. Moran, A. Yehudayoff, *Sample compression schemes for VC classes*][MoranYehudayoff2016]
-/

public section

open Set

namespace Cslib.MachineLearning.PACLearning

variable {ι κ α : Type*}

/-! ### Shattering through a map -/

/-- If the precomposed class `{g ∘ φ | g ∈ G}` shatters `W`, then `φ` is injective on `W`: two
points of `W` with the same image receive the same label from every concept of the class, so no
concept separates them. -/
theorem SetShatters.injOn_of_comp {G : ConceptClass κ Bool} {φ : ι → κ} {W : Set ι}
    (hW : SetShatters ((fun g => g ∘ φ) '' G) W) : InjOn φ W := by
  intro i hi j hj hij
  by_contra hne
  obtain ⟨_, ⟨g, -, rfl⟩, hg⟩ := hW {i} (singleton_subset_iff.2 hi)
  have hgi : g (φ i) = true := by
    have : i ∈ (g ∘ φ) ⁻¹' {true} ∩ W := hg ▸ mem_singleton i
    exact this.1
  have hgj : j ∈ (g ∘ φ) ⁻¹' {true} ∩ W := ⟨show g (φ j) = true from hij ▸ hgi, hj⟩
  exact hne (hg ▸ hgj : j ∈ ({i} : Set ι)).symm

/-- If the precomposed class `{g ∘ φ | g ∈ G}` shatters `W`, then `G` shatters `φ '' W`. -/
theorem SetShatters.image_of_comp {G : ConceptClass κ Bool} {φ : ι → κ} {W : Set ι}
    (hW : SetShatters ((fun g => g ∘ φ) '' G) W) : SetShatters G (φ '' W) := by
  intro V hV
  obtain ⟨_, ⟨g, hg, rfl⟩, hgW⟩ := hW (W ∩ φ ⁻¹' V) inter_subset_left
  have key (i : ι) : g (φ i) = true ∧ i ∈ W ↔ i ∈ W ∧ φ i ∈ V := Set.ext_iff.1 hgW i
  refine ⟨g, hg, Set.ext fun k => ⟨?_, fun hk => ?_⟩⟩
  · rintro ⟨hgk, i, hi, rfl⟩
    exact ((key i).1 ⟨hgk, hi⟩).2
  · obtain ⟨i, hi, rfl⟩ := hV hk
    exact ⟨((key i).2 ⟨hi, hk⟩).1, i, hi, rfl⟩

/-- A bound on the finite sets shattered by `G` bounds the finite sets shattered by the precomposed
class `{g ∘ φ | g ∈ G}`. -/
theorem SetShatters.card_le_of_comp {G : ConceptClass κ Bool} {d : ℕ}
    (hG : ∀ V : Finset κ, SetShatters G ↑V → V.card ≤ d) {φ : ι → κ} {W : Finset ι}
    (hW : SetShatters ((fun g => g ∘ φ) '' G) ↑W) : W.card ≤ d := by
  classical
  rw [← Finset.card_image_of_injOn hW.injOn_of_comp]
  exact hG _ (by simpa only [Finset.coe_image] using hW.image_of_comp)

/-! ### The dual class -/

/-- The *dual class* of `C`: the binary concepts on the concepts of `C` that evaluate at a point
`x`, `c ↦ c x`. -/
def dualClass (C : ConceptClass α Bool) : ConceptClass ↥C Bool :=
  range fun (x : α) (c : ↥C) => (c : α → Bool) x

theorem mem_dualClass {C : ConceptClass α Bool} {g : ↥C → Bool} :
    g ∈ dualClass C ↔ ∃ x : α, (fun c : ↥C => (c : α → Bool) x) = g :=
  Iff.rfl

/-- For a family `F` shattered by the dual class, some finite set `X` of points traces each
subfamily `G ⊆ F`: some `x ∈ X` lies in exactly the concepts of `G`. -/
private theorem exists_finset_of_setShatters_dualClass {C : ConceptClass α Bool} {F : Finset ↥C}
    (hF : SetShatters (dualClass C) ↑F) :
    ∃ X : Finset α, ∀ G ⊆ F, ∃ x ∈ X, ∀ c ∈ F, (c : α → Bool) x = true ↔ c ∈ G := by
  classical
  have hw (G : F.powerset) :
      ∃ x : α, ∀ c ∈ F, (c : α → Bool) x = true ↔ c ∈ (G : Finset ↥C) := by
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hF ↑(G : Finset ↥C) (by exact_mod_cast Finset.mem_powerset.1 G.2)
    refine ⟨x, fun c hc => ?_⟩
    have := Set.ext_iff.1 hx c
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, Finset.mem_coe, hc,
      and_true] at this
    exact this
  choose w hw using hw
  exact ⟨Finset.univ.image w, fun G hG =>
    ⟨w ⟨G, Finset.mem_powerset.2 hG⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hw _⟩⟩

/-- **Assouad's dual VC bound** [Assouad1983; MoranYehudayoff2016, Claim 1.5]: if every finite set
shattered by `C` has at most `d` points, then every finite family of concepts shattered by the dual
class has at most `2 ^ (d + 1) - 1` members. -/
theorem card_le_of_setShatters_dualClass {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {F : Finset ↥C}
    (hF : SetShatters (dualClass C) ↑F) : F.card ≤ 2 ^ (d + 1) - 1 := by
  classical
  obtain ⟨X, hX⟩ := exists_finset_of_setShatters_dualClass hF
  -- the trace of a concept on the witness points
  let τ : ↥C → Finset α := fun c => X.filter fun x => (c : α → Bool) x = true
  have hτ (c : ↥C) (x : α) : x ∈ τ c ↔ x ∈ X ∧ (c : α → Bool) x = true := Finset.mem_filter
  have hinj : Set.InjOn τ ↑F := by
    intro c hc c' hc' hcc'
    obtain ⟨x, hxX, hx⟩ := hX {c} (Finset.singleton_subset_iff.2 hc)
    have hxc : x ∈ τ c' := hcc' ▸ (hτ c x).2 ⟨hxX, (hx c hc).2 (Finset.mem_singleton_self c)⟩
    exact (Finset.mem_singleton.1 ((hx c' hc').1 ((hτ c' x).1 hxc).2)).symm
  have hcard : (F.image τ).card = F.card := Finset.card_image_of_injOn hinj
  -- the dual family of the traces shatters the traces
  have hshat : ((F.image τ).dualFamily X).Shatters (F.image τ) := by
    intro t ht
    obtain ⟨x, hxX, hx⟩ := hX (F.filter fun c => τ c ∈ t) (Finset.filter_subset _ _)
    refine ⟨(F.image τ).filter fun A => x ∈ A, Finset.mem_dualFamily.2 ⟨x, hxX, rfl⟩, ?_⟩
    ext A
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨hA, -, hxA⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hA
      exact ((Finset.mem_filter.1 ((hx c hc).1 ((hτ c x).1 hxA).2))).2
    · intro hAt
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (ht hAt)
      exact ⟨ht hAt, ht hAt,
        (hτ c x).2 ⟨hxX, (hx c hc).2 (Finset.mem_filter.2 ⟨hc, hAt⟩)⟩⟩
  by_contra hlt
  obtain ⟨T, hTX, hTcard, hTs⟩ := Finset.exists_shatters_of_dualFamily_shatters
    (F.image τ) X hshat (n := d + 1) (by rw [hcard]; omega)
  -- the traces shatter `T`, hence so does `C`
  have hCT : SetShatters C ↑T := by
    intro V hV
    have hVfin : V.Finite := T.finite_toSet.subset hV
    obtain ⟨A, hA, hTA⟩ := hTs (show hVfin.toFinset ⊆ T from by
      intro x hx; exact hV (hVfin.mem_toFinset.1 hx))
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hA
    refine ⟨c, c.2, Set.ext fun x => ?_⟩
    have := Finset.ext_iff.1 hTA x
    simp only [Finset.mem_inter, hτ, Set.Finite.mem_toFinset] at this
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro ⟨hcx, hxT⟩
      exact this.1 ⟨hxT, hTX hxT, hcx⟩
    · intro hxV
      have h := this.2 hxV
      exact ⟨h.2.2, h.1⟩
  have := hC T hCT
  omega

/-- If `C` has finite VC dimension, so does its dual class. -/
theorem hasFiniteVCDim_dualClass {C : ConceptClass α Bool} (hC : HasFiniteVCDim C) :
    HasFiniteVCDim (dualClass C) :=
  have ⟨_, hd⟩ := hasFiniteVCDim_iff.1 hC
  hasFiniteVCDim_iff.2 ⟨_, fun _ hF => card_le_of_setShatters_dualClass hd hF⟩

/-- **Assouad's dual VC bound** for `vcDim`: the dual class of a class of finite VC dimension `d`
has VC dimension at most `2 ^ (d + 1) - 1`. -/
theorem vcDim_dualClass_le {C : ConceptClass α Bool} (hC : HasFiniteVCDim C) :
    vcDim (dualClass C) ≤ 2 ^ (vcDim C + 1) - 1 :=
  csSup_le' fun _ ⟨_, hF, hshat⟩ =>
    hF ▸ card_le_of_setShatters_dualClass (fun _ hW => hW.card_le_vcDim hC) hshat

end Cslib.MachineLearning.PACLearning
