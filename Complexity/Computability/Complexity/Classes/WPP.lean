/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.FewP
public import Complexity.Computability.Complexity.Classes.SPP
public import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
public import Complexity.Foundations.Order.BooleanSubalgebra
import Complexity.Computability.Complexity.Classes.SPP.FewP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Wide and length-dependent counting gaps

WPP allows a GapP function to take either zero or a nonzero polynomial-time computable integer
target; LWPP restricts that target to depend on input length. We follow
[Hemaspaandra et al., Definitions 2.4–2.5][HemaspaandraEtAl2018], crediting the original
[Fenner–Fortnow–Kurtz][FennerFortnowKurtz1994] definitions. Targets use binary integers
`encIntBin`; the length argument of LWPP uses unary `encUnary`, so an exponentially large
numeric target is permitted. These are verifier-based counting classes, without a proved
nondeterministic-machine characterization.

In addition to the basic containments (`SPP ⊆ LWPP ⊆ WPP`, `UP ⊆ FewP ⊆ LWPP ⊆ WPP`, and
`WPP ⊆ C=P ∩ coC=P`) and Boolean closures (complement, intersection, union, difference, and
symmetric difference), we prove two robustness properties from
[Hemaspaandra et al., Section 3][HemaspaandraEtAl2018]:
* **Finite multiple-target robustness** (`mem_WPP_of_finset_targets`,
  `mem_LWPP_of_finset_targets`): if a `GapP` function takes `0` on nonmembers and one of a fixed
  finite family of nonzero polynomial-time targets on members, then interpolating the product
  `∏ i ∈ s, f i - ∏ i ∈ s, (f i - g)` collapses the accepting targets to the single nonzero
  product `∏ i ∈ s, f i`.
* **Polynomial-time unary-indexed target normalization and reduction closure**
  (`mem_LWPP_of_polyTime_index`, `PolyTimeReducible.mem_LWPP`): if the target is `f (k a)` for a
  unary-computable index `k : α → ℕ` (such as the encoded output length of a polynomial-time
  many-one reduction), multiplying the gap by the product of `f i` over all `i ≤ p(|a|)` with
  `i ≠ k a` normalizes the target to `∏_{i ≤ p(|a|)} f i`, which depends only on the input length.

Full polynomial-family multiple-target robustness (`Poly-LWPP = LWPP` and `Poly-WPP = WPP`),
with no computability assumption on the accepting index, is proved in `WPP.Robustness`.
Oracle lowness of `SPP`, `LWPP`, and `WPP` (including fixed-target `LWPPWithFixedTarget` and
`WPPWithFixedTarget` lowness with unrelativized `FP` targets) is proved in `WPP.Lowness`.

## Main definitions

* `WPP`: an input-dependent nonzero FP target.
* `LWPP`: a nonzero FP target depending only on encoded input length.

## Main results

* `mem_WPP`, `mem_LWPP`: membership through a polynomial-time target.
* `SPP_subset_LWPP`, `LWPP_subset_WPP`, `UP_subset_LWPP`, `UP_subset_WPP`,
  `coUP_subset_LWPP`, `coUP_subset_WPP`, `FewP_subset_LWPP`, `FewP_subset_WPP`,
  `WPP_subset_CeqP`, `WPP_subset_coCeqP`.
* `compl_mem_WPP`, `inter_mem_WPP`, `union_mem_WPP`, `diff_mem_WPP`, `symmDiff_mem_WPP`:
  Boolean closure of `WPP`.
* `compl_mem_LWPP`, `inter_mem_LWPP`, `union_mem_LWPP`, `diff_mem_LWPP`, `symmDiff_mem_LWPP`:
  length-dependent Boolean closure of `LWPP`.
* `mem_WPP_of_finset_targets`, `mem_LWPP_of_finset_targets`: finite multiple-target robustness.
* `mem_LWPP_of_polyTime_index`: normalization of a polynomial-time unary-indexed target to a
  length-dependent target.
* `PolyTimeReducible.mem_WPP`, `PolyTimeReducible.mem_LWPP`: polynomial-time many-one reduction
  closure.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
* [E. Hemaspaandra et al., *The Robustness of LWPP and WPP, with an Application to Graph
  Reconstruction*][HemaspaandraEtAl2018]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM
open scoped symmDiff

variable {α β : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- Wide gaps: zero on nonmembers and a nonzero binary FP target on members
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]. -/
def WPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ g ∈ GapP enc, ∃ f : α → ℤ, ComputableInPolyTime f enc encIntBin ∧
    (∀ a, f a ≠ 0) ∧ (∀ a, g a = 0 ∨ g a = f a) ∧ ∀ a, a ∈ A ↔ g a = f a}

/-- Wide gaps with a target computed in polynomial time from unary input length
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994]. -/
def LWPP (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ g ∈ GapP enc, ∃ f : ℕ → ℤ, ComputableInPolyTime f encUnary encIntBin ∧
    (∀ n, f n ≠ 0) ∧ (∀ a, g a = 0 ∨ g a = f (enc a).length) ∧
    ∀ a, a ∈ A ↔ g a = f (enc a).length}

theorem mem_WPP : A ∈ WPP enc ↔ ∃ g ∈ GapP enc, ∃ f : α → ℤ,
    ComputableInPolyTime f enc encIntBin ∧
      (∀ a, f a ≠ 0) ∧ (∀ a, g a = 0 ∨ g a = f a) ∧ ∀ a, a ∈ A ↔ g a = f a :=
  Iff.rfl

theorem mem_LWPP : A ∈ LWPP enc ↔ ∃ g ∈ GapP enc, ∃ f : ℕ → ℤ,
    ComputableInPolyTime f encUnary encIntBin ∧
      (∀ n, f n ≠ 0) ∧ (∀ a, g a = 0 ∨ g a = f (enc a).length) ∧
      ∀ a, a ∈ A ↔ g a = f (enc a).length :=
  Iff.rfl

/-- The constant target one witnesses the SPP containment. -/
theorem SPP_subset_LWPP : SPP enc ⊆ LWPP enc := by
  rintro A ⟨g, hg, hr, hA⟩
  exact ⟨g, hg, fun _ => 1, .const _, fun _ => one_ne_zero, hr, hA⟩

/-- Computing the encoded input length turns an LWPP target into a WPP target. -/
theorem LWPP_subset_WPP : LWPP enc ⊆ WPP enc := by
  rintro A ⟨g, hg, f, hf, hn, hr, hA⟩
  exact ⟨g, hg, fun a => f (enc a).length,
    hf.comp (.encoding_length enc), fun a => hn _, hr, hA⟩

/-- Unambiguous polynomial time is contained in `LWPP` via `SPP`. -/
theorem UP_subset_LWPP : UP enc ⊆ LWPP enc :=
  UP_subset_SPP.trans SPP_subset_LWPP

/-- Unambiguous polynomial time is contained in `WPP`. -/
theorem UP_subset_WPP : UP enc ⊆ WPP enc :=
  UP_subset_LWPP.trans LWPP_subset_WPP

/-- `coUP` is contained in `LWPP` via `SPP`. -/
theorem coUP_subset_LWPP : coUP enc ⊆ LWPP enc :=
  coUP_subset_SPP.trans SPP_subset_LWPP

/-- `coUP` is contained in `WPP`. -/
theorem coUP_subset_WPP : coUP enc ⊆ WPP enc :=
  coUP_subset_LWPP.trans LWPP_subset_WPP

/-- Polynomially bounded ambiguity `FewP` is contained in `LWPP` via `FewP ⊆ SPP`. -/
theorem FewP_subset_LWPP : FewP enc ⊆ LWPP enc :=
  FewP_subset_SPP.trans SPP_subset_LWPP

/-- Polynomially bounded ambiguity `FewP` is contained in `WPP`. -/
theorem FewP_subset_WPP : FewP enc ⊆ WPP enc :=
  FewP_subset_LWPP.trans LWPP_subset_WPP

/-- Subtraction of the target gives a zero test for WPP membership. -/
theorem WPP_subset_CeqP : WPP enc ⊆ CeqP enc := by
  rintro A ⟨g, hg, f, hf, -, -, hA⟩
  exact ⟨g - f, GapP.sub_mem' hg (mem_GapP_of_polyTime hf), fun a => by
    simpa [sub_eq_zero] using hA a⟩

/-- A WPP gap is nonzero exactly on members. -/
theorem WPP_subset_coCeqP : WPP enc ⊆ coCeqP enc := by
  rintro A ⟨g, hg, f, -, hn, hr, hA⟩
  refine mem_coCeqP_iff_exists_GapP.mpr ⟨g, hg, fun a => ?_⟩
  rw [hA a]
  rcases hr a with h | h <;> simp [h, hn a, (hn a).symm]

/-- Complement exchanges the zero and target values. -/
theorem compl_mem_WPP (hA : A ∈ WPP enc) : Aᶜ ∈ WPP enc := by
  rw [mem_WPP] at hA ⊢
  obtain ⟨g, hg, f, hf, hn, hr, hA⟩ := hA
  refine ⟨f - g, GapP.sub_mem' (mem_GapP_of_polyTime hf) hg, f, hf, hn,
    fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> simp [h]
  · rcases hr a with h | h <;> simp [hA a, h, (hn a).symm]

/-- Products preserve the zero-or-target condition and the target is still nonzero. -/
theorem inter_mem_WPP (hA : A ∈ WPP enc) (hB : B ∈ WPP enc) : A ∩ B ∈ WPP enc := by
  rw [mem_WPP] at hA hB ⊢
  obtain ⟨g, hg, f, hf, hn, hr, hA⟩ := hA
  obtain ⟨g', hg', f', hf', hn', hr', hB⟩ := hB
  refine ⟨g * g', GapP.mul_mem hg hg', f * f', hf.intBin_mul' hf',
    fun a => mul_ne_zero (hn a) (hn' a), fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> rcases hr' a with h' | h' <;> simp [h, h']
  · rcases hr a with h | h <;> rcases hr' a with h' | h' <;>
      simp [hA a, hB a, h, h', hn a, hn' a, (hn a).symm, (hn' a).symm]

/-- `WPP` as a Boolean subalgebra of `Set α`. -/
def WPP.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (WPP enc) (UP_subset_WPP (P_subset_UP empty_mem_P)) (fun _ => compl_mem_WPP)
    (fun _ _ => inter_mem_WPP)

@[simp]
theorem WPP.coe_booleanSubalgebra : (WPP.booleanSubalgebra enc : Set (Set α)) = WPP enc := rfl

@[simp]
theorem WPP.mem_booleanSubalgebra : A ∈ WPP.booleanSubalgebra enc ↔ A ∈ WPP enc := Iff.rfl

/-- Union follows by De Morgan's law. -/
theorem union_mem_WPP (hA : A ∈ WPP enc) (hB : B ∈ WPP enc) : A ∪ B ∈ WPP enc :=
  (WPP.booleanSubalgebra enc).sup_mem hA hB

/-- `WPP` is closed under set difference. -/
theorem diff_mem_WPP (hA : A ∈ WPP enc) (hB : B ∈ WPP enc) : A \ B ∈ WPP enc :=
  (WPP.booleanSubalgebra enc).sdiff_mem hA hB

/-- `WPP` is closed under symmetric difference. -/
theorem symmDiff_mem_WPP (hA : A ∈ WPP enc) (hB : B ∈ WPP enc) : A ∆ B ∈ WPP enc :=
  (WPP.booleanSubalgebra enc).symmDiff_mem hA hB

/-- Polynomial-time precomposition preserves the target and the exact gap. -/
theorem PolyTimeReducible.mem_WPP {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ WPP encB) : A ∈ WPP enc := by
  obtain ⟨r, hr, hAB⟩ := h
  obtain ⟨g, hg, f, hf, hn, hgr, hB⟩ := hB
  exact ⟨g ∘ r, GapP.comp_mem hg hr, f ∘ r, hf.comp hr, fun a => hn _,
    fun a => hgr _, fun a => (hAB a).trans (hB _)⟩

/-- The complementary gap uses the same length-dependent target. -/
theorem compl_mem_LWPP (hA : A ∈ LWPP enc) : Aᶜ ∈ LWPP enc := by
  rw [mem_LWPP] at hA ⊢
  obtain ⟨g, hg, f, hf, hn, hr, hA⟩ := hA
  have htarget := mem_GapP_of_polyTime (hf.comp (.encoding_length enc))
  refine ⟨(fun a => f (enc a).length) - g, GapP.sub_mem' htarget hg,
    f, hf, hn, fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> simp [h]
  · rcases hr a with h | h <;> simp [hA a, h, (hn _).symm]

/-- Multiplying length-dependent targets preserves length dependence. -/
theorem inter_mem_LWPP (hA : A ∈ LWPP enc) (hB : B ∈ LWPP enc) : A ∩ B ∈ LWPP enc := by
  rw [mem_LWPP] at hA hB ⊢
  obtain ⟨g, hg, f, hf, hn, hr, hA⟩ := hA
  obtain ⟨g', hg', f', hf', hn', hr', hB⟩ := hB
  refine ⟨g * g', GapP.mul_mem hg hg', f * f', hf.intBin_mul' hf',
    fun n => mul_ne_zero (hn n) (hn' n), fun a => ?_, fun a => ?_⟩
  · rcases hr a with h | h <;> rcases hr' a with h' | h' <;> simp [h, h']
  · rcases hr a with h | h <;> rcases hr' a with h' | h' <;>
      simp [hA a, hB a, h, h', hn _, hn' _, (hn _).symm, (hn' _).symm]

/-- `LWPP` as a Boolean subalgebra of `Set α`. -/
def LWPP.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (LWPP enc) (UP_subset_LWPP (P_subset_UP empty_mem_P)) (fun _ => compl_mem_LWPP)
    (fun _ _ => inter_mem_LWPP)

@[simp]
theorem LWPP.coe_booleanSubalgebra : (LWPP.booleanSubalgebra enc : Set (Set α)) = LWPP enc := rfl

@[simp]
theorem LWPP.mem_booleanSubalgebra : A ∈ LWPP.booleanSubalgebra enc ↔ A ∈ LWPP enc := Iff.rfl

/-- Union preserves length-dependent targets. -/
theorem union_mem_LWPP (hA : A ∈ LWPP enc) (hB : B ∈ LWPP enc) : A ∪ B ∈ LWPP enc :=
  (LWPP.booleanSubalgebra enc).sup_mem hA hB

/-- `LWPP` is closed under set difference. -/
theorem diff_mem_LWPP (hA : A ∈ LWPP enc) (hB : B ∈ LWPP enc) : A \ B ∈ LWPP enc :=
  (LWPP.booleanSubalgebra enc).sdiff_mem hA hB

/-- `LWPP` is closed under symmetric difference. -/
theorem symmDiff_mem_LWPP (hA : A ∈ LWPP enc) (hB : B ∈ LWPP enc) : A ∆ B ∈ LWPP enc :=
  (LWPP.booleanSubalgebra enc).symmDiff_mem hA hB

/-! ### Finite multiple-target robustness -/

private theorem finset_prod_intBin {ι : Type*} (s : Finset ι) {f : ι → α → ℤ}
    (hf : ∀ i ∈ s, ComputableInPolyTime (f i) enc encIntBin) :
    ComputableInPolyTime (fun a => ∏ i ∈ s, f i a) enc encIntBin := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (ComputableInPolyTime.const 1).of_enc_eq fun _ => congrArg encIntBin (by simp)
  | insert i s hi ih =>
    have hmul := (hf i (Finset.mem_insert_self i s)).intBin_mul'
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact hmul.of_enc_eq fun a => congrArg encIntBin (Finset.prod_insert hi)

private theorem finset_prod_mem_GapP {ι : Type*} (s : Finset ι) {f : ι → α → ℤ}
    (hf : ∀ i ∈ s, f i ∈ GapP enc) : (fun a => ∏ i ∈ s, f i a) ∈ GapP enc := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact GapP.one_mem
  | insert i s hi ih =>
    have hmul := GapP.mul_mem (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    convert hmul using 1
    ext a
    exact Finset.prod_insert hi

private theorem finsetTargetWitness {ι : Type*} (s : Finset ι) {g : α → ℤ} {f : ι → α → ℤ}
    (hg : g ∈ GapP enc)
    (hf : ∀ i ∈ s, ComputableInPolyTime (f i) enc encIntBin)
    (hn : ∀ i ∈ s, ∀ a, f i a ≠ 0)
    (hr : ∀ a, g a = 0 ∨ ∃ i ∈ s, g a = f i a)
    (hA : ∀ a, a ∈ A ↔ ∃ i ∈ s, g a = f i a) :
    ∃ G ∈ GapP enc, (∀ a, G a = 0 ∨ G a = ∏ i ∈ s, f i a) ∧
      ∀ a, a ∈ A ↔ G a = ∏ i ∈ s, f i a := by
  let F : α → ℤ := fun a => ∏ i ∈ s, f i a
  let P : α → ℤ := fun a => ∏ i ∈ s, (f i a - g a)
  have hF : ComputableInPolyTime F enc encIntBin := finset_prod_intBin s hf
  have hFn (a : α) : F a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i hi => hn i hi a
  have hP : P ∈ GapP enc :=
    finset_prod_mem_GapP s fun i hi => GapP.sub_mem' (mem_GapP_of_polyTime (hf i hi)) hg
  have hP_zero {a : α} (hz : g a = 0) : P a = F a := by
    simp [P, F, hz]
  have hP_mem {a : α} (hmem : ∃ i ∈ s, g a = f i a) : P a = 0 := by
    obtain ⟨i, hi, hgi⟩ := hmem
    exact Finset.prod_eq_zero hi (by lia)
  refine ⟨F - P, GapP.sub_mem' (mem_GapP_of_polyTime hF) hP, fun a => ?_, fun a => ?_⟩
  · rcases hr a with hz | hmem
    · exact Or.inl (by simp [F, hP_zero hz])
    · exact Or.inr (by simp [F, hP_mem hmem])
  · rw [hA a]
    constructor
    · intro hmem
      simp [F, hP_mem hmem]
    · intro hFP
      rcases hr a with hz | hmem
      · exfalso
        apply hFn a
        have : F a - P a = 0 := by simp [hP_zero hz]
        have hEq : F a - P a = F a := hFP
        lia
      · exact hmem

/-- **Finite multiple-target robustness for `WPP`:** a `GapP` function that takes `0` outside `A`
and one of a fixed finite family of nonzero polynomial-time targets on `A` witnesses `A ∈ WPP`
(the fixed-`Finset` case of [Hemaspaandra et al., Theorem 3.7][HemaspaandraEtAl2018], whose proof
is the product interpolation of their Theorem 3.1). -/
theorem mem_WPP_of_finset_targets {ι : Type*} (s : Finset ι) {g : α → ℤ} {f : ι → α → ℤ}
    (hg : g ∈ GapP enc)
    (hf : ∀ i ∈ s, ComputableInPolyTime (f i) enc encIntBin)
    (hn : ∀ i ∈ s, ∀ a, f i a ≠ 0)
    (hr : ∀ a, g a = 0 ∨ ∃ i ∈ s, g a = f i a)
    (hA : ∀ a, a ∈ A ↔ ∃ i ∈ s, g a = f i a) : A ∈ WPP enc := by
  obtain ⟨G, hG, hR, hGA⟩ := finsetTargetWitness s hg hf hn hr hA
  exact ⟨G, hG, _, finset_prod_intBin s hf,
    fun a => Finset.prod_ne_zero_iff.mpr fun i hi => hn i hi a, hR, hGA⟩

/-- **Finite multiple-target robustness for `LWPP`:** a `GapP` function that takes `0` outside `A`
and one of a fixed finite family of nonzero length-dependent polynomial-time targets on `A`
witnesses `A ∈ LWPP` (the fixed-`Finset` case of the product interpolation in
[Hemaspaandra et al., Theorem 3.1][HemaspaandraEtAl2018]). -/
theorem mem_LWPP_of_finset_targets {ι : Type*} (s : Finset ι) {g : α → ℤ} {f : ι → ℕ → ℤ}
    (hg : g ∈ GapP enc)
    (hf : ∀ i ∈ s, ComputableInPolyTime (f i) encUnary encIntBin)
    (hn : ∀ i ∈ s, ∀ n, f i n ≠ 0)
    (hr : ∀ a, g a = 0 ∨ ∃ i ∈ s, g a = f i (enc a).length)
    (hA : ∀ a, a ∈ A ↔ ∃ i ∈ s, g a = f i (enc a).length) : A ∈ LWPP enc := by
  obtain ⟨G, hG, hR, hGA⟩ := finsetTargetWitness s hg
    (fun i hi => (hf i hi).comp (.encoding_length enc))
    (fun i hi a => hn i hi (enc a).length) hr hA
  exact ⟨G, hG, fun n => ∏ i ∈ s, f i n, finset_prod_intBin s hf,
    fun n => Finset.prod_ne_zero_iff.mpr fun i hi => hn i hi n, hR, hGA⟩

/-! ### Unary-indexed target normalization and `LWPP` reduction closure -/

/-- **Unary-indexed target normalization for `LWPP`:** if a `GapP` function takes `0` outside `A`
and `f (k a)` on `A`, where `f : ℕ → ℤ` is a nonzero unary-input polynomial-time target and
`k : α → ℕ` is computable in polynomial time in unary, then multiplying the gap by the
`FP`-computable product of `f i` over `i ≤ p(|a|)` with `i ≠ k a` normalizes the target to depend
only on
`(enc a).length` [Fenner–Fortnow–Kurtz][FennerFortnowKurtz1994];
[Hemaspaandra et al., Section 3][HemaspaandraEtAl2018]. -/
theorem mem_LWPP_of_polyTime_index {g : α → ℤ} {f : ℕ → ℤ} {k : α → ℕ}
    (hg : g ∈ GapP enc)
    (hf : ComputableInPolyTime f encUnary encIntBin)
    (hn : ∀ n, f n ≠ 0)
    (hk : ComputableInPolyTime k enc encUnary)
    (hr : ∀ a, g a = 0 ∨ g a = f (k a))
    (hA : ∀ a, a ∈ A ↔ g a = f (k a)) : A ∈ LWPP enc := by
  obtain ⟨p, hp⟩ := hk.polyBounded.exists_polynomial
  have hlt (a : α) : k a < p.eval (enc a).length + 1 := Nat.lt_succ_of_le (hp a)
  let bound (n : ℕ) : ℕ := p.eval n + 1
  have hbound : ComputableInPolyTime bound encUnary encUnary :=
    ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.unary_eval p).prod (.const 1))
  let F (n : ℕ) : ℤ := ((List.range (bound n)).map f).prod
  have hF : ComputableInPolyTime F encUnary encIntBin :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_prod).comp
      ((ComputableInPolyTime.map hf).comp
        (ComputableInPolyTime.range.comp hbound))
  have hFn (n : ℕ) : F n ≠ 0 := List.prod_ne_zero (by simp [hn])
  let h (a : α) : ℤ :=
    (((List.range (bound (enc a).length)).filter (fun i => decide (i ≠ k a))).map f).prod
  have hlist : ComputableInPolyTime
      (fun a : α => List.range (bound (enc a).length)) enc (encList encUnary) :=
    (ComputableInPolyTime.range.comp hbound).comp (.encoding_length enc)
  have htest : ComputableInPolyTime
      (fun x : α × ℕ => decide (x.2 ≠ k x.1)) (encPair enc encUnary) encBool :=
    (ComputableInPolyTime.bool_not.comp
      (ComputableInPolyTime.decide_eq' (.snd enc encUnary) (hk.comp (.fst enc encUnary)))).of_enc_eq
      fun x => congrArg encBool (by simp)
  have hh : ComputableInPolyTime h enc encIntBin :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_prod).comp
      ((ComputableInPolyTime.map hf).comp
        (ComputableInPolyTime.filterWithInput hlist htest))
  have hmul (a : α) : f (k a) * h a = F (enc a).length := by
    have herase :
        (List.range (bound (enc a).length)).filter (fun i => decide (i ≠ k a)) =
          (List.range (bound (enc a).length)).erase (k a) := by
      rw [List.nodup_range.erase_eq_filter]
      exact List.filter_congr fun i _ => by simp [bne, beq_eq_decide]
    simpa only [h, F, herase] using List.prod_map_erase f (List.mem_range.mpr (hlt a))
  refine ⟨g * h, GapP.mul_mem hg (mem_GapP_of_polyTime hh), F, hF, hFn,
    fun a => ?_, fun a => ?_⟩
  · rcases hr a with hz | hfk
    · exact Or.inl (by simp [hz])
    · exact Or.inr (by simp [hfk, hmul a])
  · rw [hA a]
    rcases hr a with hz | hfk
    · simp [hz, (hFn (enc a).length).symm, (hn (k a)).symm]
    · simp [hfk, hmul a]

/-- **Polynomial-time many-one reductions preserve `LWPP`**
[Fenner–Fortnow–Kurtz][FennerFortnowKurtz1994];
[Hemaspaandra et al., Section 3][HemaspaandraEtAl2018]: the target `f |r(a)|` has unary-computable
index `k a = |r(a)|`, which `mem_LWPP_of_polyTime_index` normalizes to a function of `|a|`. -/
theorem PolyTimeReducible.mem_LWPP {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ LWPP encB) : A ∈ LWPP enc := by
  obtain ⟨r, hr, hAB⟩ := h
  obtain ⟨g, hg, f, hf, hn, hgr, hB⟩ := hB
  exact mem_LWPP_of_polyTime_index (GapP.comp_mem hg hr) hf hn
    ((ComputableInPolyTime.encoding_length encB).comp hr)
    (fun a => hgr (r a)) (fun a => (hAB a).trans (hB (r a)))

end Cslib.Complexity
