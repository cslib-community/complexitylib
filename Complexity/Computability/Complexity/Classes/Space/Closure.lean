/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space
public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Foundations.Order.BooleanSubalgebra
import Complexity.Computability.Complexity.Classes.Space.Savitch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Characterizations and closure properties of `PSPACE`

A problem is in `PSPACE` exactly when a Boolean function deciding it is computable within
some time and space polynomial in the length of the encoded instance
(`Cslib.Complexity.mem_PSPACE_iff_computableInO`,
`Cslib.Complexity.mem_PSPACE_iff_computableInPolySpace`). `PSPACE` is closed under
complement, under polynomial-time reductions, and under polynomially bounded existential
quantification [Arora and Barak, Chapter 4][AroraBarak09]. The existential quantifier over the
words `w` of length `ℓ` is reachability within two steps from the all-zero word to the all-one word
of width `ℓ + 1`, along edges to `true :: w` for the accepted `w` and from every word starting with
`true` to the all-one word; Savitch's algorithm decides it at depth `1`, enumerating the candidates
in place and reusing the space of the decider for each.

## Main results

* `Cslib.Complexity.mem_PSPACE_iff_computableInO`: `PSPACE` in the quantitative calculus.
* `Cslib.Complexity.mem_PSPACE_iff_computableInPolySpace`,
  `Cslib.Complexity.mem_PSPACE_of_computableInPolySpace`: `PSPACE` within polynomial space.
* `Cslib.Complexity.compl_mem_PSPACE`, `Cslib.Complexity.inter_mem_PSPACE`,
  `Cslib.Complexity.union_mem_PSPACE`, `Cslib.Complexity.diff_mem_PSPACE`,
  `Cslib.Complexity.symmDiff_mem_PSPACE`, `Cslib.Complexity.PSPACE.booleanSubalgebra`,
  `Cslib.Complexity.PolyTimeReducible.mem_PSPACE`, `Cslib.Complexity.setOf_exists_mem_PSPACE`:
  closure properties of `PSPACE`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Filter

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}


/-- **`PSPACE` in the quantitative calculus**: a problem is in `PSPACE` exactly when a Boolean
function deciding it is computable within some time and within space polynomial in the length of
the encoded instance. -/
theorem mem_PSPACE_iff_computableInO : A ∈ PSPACE enc ↔ ∃ (f : α → Bool) (T S : α → ℕ),
    ComputableInO f enc encBool T S ∧ PolyBounded (fun a => (enc a).length) S ∧
      ∀ a, a ∈ A ↔ f a = true := by
  constructor
  · rintro ⟨f, ⟨t, s, hs, hf⟩, hA⟩
    exact ⟨f, t, s, ⟨1, hf.mono (fun _ => by omega) fun _ => by omega, fun _ => by simp⟩, hs, hA⟩
  · rintro ⟨f, T, S, ⟨c, hc, -⟩, hS, hA⟩
    exact ⟨f, ⟨_, _, (PolyBounded.const c).mul (hS.add (.const 1)), hc⟩, hA⟩

/-- **`PSPACE` within polynomial space**: a problem is in `PSPACE` exactly when a Boolean function
deciding it is computable within space polynomial in the length of the encoded instance
(`Turing.MultiTapeTM.ComputableInPolySpace`). -/
theorem mem_PSPACE_iff_computableInPolySpace : A ∈ PSPACE enc ↔
    ∃ f : α → Bool, ComputableInPolySpace f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true := by
  constructor
  · rintro ⟨f, ⟨t, s, hs, hf⟩, hA⟩
    obtain ⟨c, d, hcd⟩ := hs.exists_le
    refine ⟨f, ⟨t, fun n => c * (n + 1) ^ d + 1, by fun_prop,
      hf.mono (fun _ => le_rfl) fun a => (hcd a).trans (Nat.le_succ _),
      fun _ => by simp⟩, hA⟩
  · rintro ⟨f, ⟨t, s, hs, hf, -⟩, hA⟩
    exact ⟨f, ⟨t, _, .of_polynomiallyBounded _ hs, hf⟩, hA⟩

/-- A Boolean function computable within polynomial space decides a problem in `PSPACE`. -/
theorem mem_PSPACE_of_computableInPolySpace {f : α → Bool}
    (hf : ComputableInPolySpace f enc encBool) (hA : ∀ a, a ∈ A ↔ f a = true) :
    A ∈ PSPACE enc :=
  mem_PSPACE_iff_computableInPolySpace.mpr ⟨f, hf, hA⟩

/-- **`PSPACE` is closed under complement**: negate the answer. -/
theorem compl_mem_PSPACE (hA : A ∈ PSPACE enc) : Aᶜ ∈ PSPACE enc := by
  obtain ⟨f, hf, hA⟩ := mem_PSPACE_iff_computableInPolySpace.mp hA
  exact mem_PSPACE_of_computableInPolySpace
    ((ComputableInPolySpace.of_polyTime ComputableInPolyTime.bool_not).comp hf)
    fun a => by simp [hA a]

open scoped symmDiff

/-- **`PSPACE` is closed under intersection.** -/
theorem inter_mem_PSPACE {B : Set α} (hA : A ∈ PSPACE enc) (hB : B ∈ PSPACE enc) :
    A ∩ B ∈ PSPACE enc := by
  obtain ⟨f, hf, hA⟩ := mem_PSPACE_iff_computableInPolySpace.mp hA
  obtain ⟨g, hg, hB⟩ := mem_PSPACE_iff_computableInPolySpace.mp hB
  exact mem_PSPACE_of_computableInPolySpace
    ((ComputableInPolySpace.of_polyTime ComputableInPolyTime.bool_and).comp (hf.prod hg))
    fun a => by simp [hA a, hB a]

/-- `PSPACE` as a Boolean subalgebra of `Set α`. -/
def PSPACE.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (PSPACE enc) (P_subset_PSPACE empty_mem_P) (fun _ => compl_mem_PSPACE)
    (fun _ _ => inter_mem_PSPACE)

@[simp]
theorem PSPACE.coe_booleanSubalgebra :
    (PSPACE.booleanSubalgebra enc : Set (Set α)) = PSPACE enc := rfl

@[simp]
theorem PSPACE.mem_booleanSubalgebra : A ∈ PSPACE.booleanSubalgebra enc ↔ A ∈ PSPACE enc :=
  Iff.rfl

/-- `PSPACE` is closed under union. -/
theorem union_mem_PSPACE {B : Set α} (hA : A ∈ PSPACE enc) (hB : B ∈ PSPACE enc) :
    A ∪ B ∈ PSPACE enc :=
  (PSPACE.booleanSubalgebra enc).sup_mem hA hB

/-- `PSPACE` is closed under set difference. -/
theorem diff_mem_PSPACE {B : Set α} (hA : A ∈ PSPACE enc) (hB : B ∈ PSPACE enc) :
    A \ B ∈ PSPACE enc :=
  (PSPACE.booleanSubalgebra enc).sdiff_mem hA hB

/-- `PSPACE` is closed under symmetric difference. -/
theorem symmDiff_mem_PSPACE {B : Set α} (hA : A ∈ PSPACE enc) (hB : B ∈ PSPACE enc) :
    A ∆ B ∈ PSPACE enc :=
  (PSPACE.booleanSubalgebra enc).symmDiff_mem hA hB

/-- **`PSPACE` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PSPACE {β : Type} {encB : β ↪ List Bool} {B : Set β}
    (h : PolyTimeReducible enc encB A B) (hB : B ∈ PSPACE encB) : A ∈ PSPACE enc := by
  obtain ⟨g, hg, hAB⟩ := h
  obtain ⟨f, hf, hB⟩ := mem_PSPACE_iff_computableInPolySpace.mp hB
  exact mem_PSPACE_of_computableInPolySpace (hf.comp (.of_polyTime hg))
    fun a => (hAB a).trans (hB (g a))

/-- The edges of the graph on words of width `n + 1` whose reachability within two steps from the
all-zero word to the all-one word is a bounded existential over `f`: an edge from the all-zero word
to `true :: w` when `f (x, w)`, and from every word starting with `true` to the all-one word. -/
private def existsEdge {β : Type} (f : β × List Bool → Bool) (x : β) (u v : List Bool) : Bool :=
  if !(u.any fun b => b) && v.headD false then f (x, v.tail)
  else u.headD false && !(v.any fun b => !b)

/-- Savitch's algorithm at depth `1` on the edges of `existsEdge` decides the bounded
existential. -/
private theorem savitch_existsEdge {β : Type} (f : β × List Bool → Bool) (x : β) (n : ℕ) :
    Cslib.Reachability.savitch (existsEdge f x) (n + 1) 1 (List.replicate (n + 1) false)
      (List.replicate (n + 1) true) = true ↔ ∃ w : List Bool, w.length = n ∧ f (x, w) = true := by
  rw [Cslib.Reachability.savitch_eq]
  simp only [Cslib.Reachability.reach, List.any_eq_true, Cslib.BitString.mem_enumList,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨m, hm, h₁ | h₁, h₂ | h₂⟩
    · subst h₁
      exact absurd h₂ (by simp [List.replicate_succ])
    · subst h₁
      refine ⟨List.replicate n true, List.length_replicate .., ?_⟩
      simpa [existsEdge, List.replicate_succ] using h₂
    · subst h₂
      refine ⟨List.replicate n true, List.length_replicate .., ?_⟩
      simpa [existsEdge, List.replicate_succ] using h₁
    · obtain ⟨b, w, rfl⟩ := List.exists_cons_of_length_eq_add_one hm
      refine ⟨w, by simpa using hm, ?_⟩
      cases b <;> simp_all [existsEdge, List.replicate_succ]
  · rintro ⟨w, hw, hf⟩
    refine ⟨true :: w, by simp [hw], Or.inr ?_, Or.inr ?_⟩
    · simp [existsEdge, List.replicate_succ, hf]
    · simp [existsEdge, List.replicate_succ]

private theorem polyTime_inO {β γ : Type} {encIn : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {f : β → γ} (hf : ComputableInPolyTime f encIn encOut) :
    ∃ T S : β → ℕ, PolyBounded (fun x => (encIn x).length) S ∧
      ComputableInO f encIn encOut T S := by
  obtain ⟨t, s, ht, hs, hc⟩ := hf
  exact ⟨fun x => t (encIn x).length, fun x => t (encIn x).length + s (encIn x).length,
    .of_polynomiallyBounded _ (ht.add hs), 1,
    hc.mono (fun _ => by dsimp only; omega) fun _ => by dsimp only; omega,
    fun x => by have := hc.length_le x; dsimp only; omega⟩

attribute [local fun_prop] ComputableInPolyTime.fst' ComputableInPolyTime.snd'
    ComputableInPolyTime.bool_and' in
/-- **`PSPACE` is closed under polynomially bounded existential quantification**: if `B ⊆ β × List
Bool` is in `PSPACE` and `ℓ` is polynomial-time, then so is the set of the `x` for which some word
`w` of length `ℓ x` has `(x, w) ∈ B`. The candidates are enumerated in place: this is reachability
within two steps between two words of width `ℓ x + 1` (`existsEdge`), which Savitch's algorithm
decides at depth `1`, reusing the space of the decider of `B` for every candidate
(`Cslib.Reachability.computableInO_savitch`). -/
theorem setOf_exists_mem_PSPACE {β : Type} {encB : β ↪ List Bool} {B : Set (β × List Bool)}
    {ℓ : β → ℕ} (hB : B ∈ PSPACE (encPair encB encBits))
    (hℓ : ComputableInPolyTime ℓ encB encUnary) :
    {x | ∃ w : List Bool, w.length = ℓ x ∧ (x, w) ∈ B} ∈ PSPACE encB := by
  obtain ⟨f, T, S, hf, hS, hB⟩ := mem_PSPACE_iff_computableInO.mp hB
  set encQ := encPair encB (encPair encBits encBits)
  -- the edge test: polynomial-time tests around one call of the decider of `B`
  have hg : ComputableInPolyTime (fun q : β × List Bool × List Bool => (q.1, q.2.2.tail))
      encQ (encPair encB encBits) := by fun_prop
  have hc : ComputableInPolyTime
      (fun q : β × List Bool × List Bool => !(q.2.1.any fun b => b) && q.2.2.headD false)
      encQ encBool := by fun_prop
  have he : ComputableInPolyTime
      (fun q : β × List Bool × List Bool => q.2.1.headD false && !(q.2.2.any fun b => !b))
      encQ encBool := by fun_prop
  obtain ⟨Tg, Sg, hSg, hgO⟩ := polyTime_inO hg
  obtain ⟨Tc, Sc, hSc, hcO⟩ := polyTime_inO hc
  obtain ⟨Te, Se, hSe, heO⟩ := polyTime_inO he
  have hedge := hcO.ite (hf.comp hgO) heO
  -- the arguments of Savitch's algorithm
  have hin : ComputableInPolyTime
      (fun x => (x, ℓ x + 1, 1, List.replicate (ℓ x + 1) false, List.replicate (ℓ x + 1) true))
      encB (Cslib.Reachability.encArgs encB) := by
    unfold Cslib.Reachability.encArgs
    fun_prop
  obtain ⟨Ti, Si, hSi, hinO⟩ := polyTime_inO hin
  have h := Cslib.Reachability.computableInO_savitch (edge := existsEdge f) (par := id)
    hedge hinO (fun _ => List.length_replicate ..) fun _ => List.length_replicate ..
  -- the space is polynomial
  have hSedge : PolyBounded (fun q => (encQ q).length) fun q =>
      Sc q + if !(q.2.1.any fun b => b) && q.2.2.headD false then Sg q + S (q.1, q.2.2.tail)
        else Se q :=
    (hSc.add (hSg.add (hS.comp hg.polyBounded_length) |>.add hSe)).mono fun q => by
      split_ifs <;> omega
  obtain ⟨cE, dE, hcE⟩ := hSedge.exists_le
  have hℓ' : PolyBounded (fun x => (encB x).length) ℓ :=
    hℓ.polyBounded_length.mono fun x => by simp [encUnary_apply]
  have hG : PolyBounded (fun x => (encB x).length)
      fun x => 2 * (encB x).length + 3 * ℓ x + 6 :=
    (((PolyBounded.const 2).mul .self).add ((PolyBounded.const 3).mul hℓ')).add (.const 6)
  have hpow : PolyBounded (fun x => (encB x).length)
      fun x => cE * (2 * (encB x).length + 3 * ℓ x + 6) ^ dE :=
    PolyBounded.comp (size' := id) (v := fun n => cE * n ^ dE)
      (PolyBounded.of_polynomiallyBounded (bound := fun n => cE * n ^ dE) id (by fun_prop)) hG
  refine mem_PSPACE_iff_computableInO.mpr ⟨_, _, _, h, ?_, fun x => ?_⟩
  · refine (((hSi.add ((PolyBounded.const 2).mul (hℓ'.add (.const 3)))).add .self).add
      hpow).mono fun x => ?_
    have hmax : Cslib.Reachability.edgeMax (fun q : β × List Bool × List Bool =>
        Sc q + if (!(q.2.1.any fun b => b) && q.2.2.headD false) = true then
          Sg q + S (q.1, q.2.2.tail) else Se q) x (ℓ x + 1) ≤
        cE * (2 * (encB x).length + 3 * ℓ x + 6) ^ dE :=
      listMax_le fun u hu => listMax_le fun v hv => by
        refine (hcE _).trans (Nat.mul_le_mul_left cE (Nat.pow_le_pow_left ?_ dE))
        simp only [encQ, length_encPair, encBits_apply, Cslib.BitString.mem_enumList.mp hu,
          Cslib.BitString.mem_enumList.mp hv]
        omega
    change Si x + (1 + 1) * (1 + (ℓ x + 1) + 1) + (encB x).length +
        Cslib.Reachability.edgeMax (fun q : β × List Bool × List Bool =>
          Sc q + if (!(q.2.1.any fun b => b) && q.2.2.headD false) = true then
            Sg q + S (q.1, q.2.2.tail) else Se q) x (ℓ x + 1) ≤
      Si x + 2 * (ℓ x + 3) + (encB x).length + cE * (2 * (encB x).length + 3 * ℓ x + 6) ^ dE
    omega
  · simp only [Set.mem_ofPred_eq, hB, id]
    exact (savitch_existsEdge f x (ℓ x)).symm

end Cslib.Complexity
