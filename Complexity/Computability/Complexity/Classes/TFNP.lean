/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option
import Complexity.Computability.Complexity.Classes.NP.Witness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Search problems: FNP, FP and TFNP

A *search problem* is a relation `R : α → List Bool → Prop` between instances and solutions; the
task is to find, given `a`, some `w` with `R a w` [Papadimitriou, Section 10.3][Papadimitriou94],
[Arora and Barak, Section 2.5][AroraBarak09]. Solutions are bit strings, so the length of a
solution is the length of its description, as in Megiddo and Papadimitriou
[MegiddoPapadimitriou1991]. Instances are encoded by `enc : α ↪ List Bool`, and a verifier reads
the pair `encPair enc encBits (a, w) = frame (enc a) ++ w`, as for `Cslib.Complexity.NP`.

* `Cslib.Complexity.FNP`: relations that are *polynomially balanced* (every solution of `a` has
  length at most `p (enc a).length` for a polynomial `p`) and *polynomial-time decidable*. These
  are the two conditions of [Papadimitriou, Section 10.3][Papadimitriou94]. Balance is a property
  of the relation itself: unlike the certificates of `NP`, solutions have no prescribed length.
  `Cslib.Complexity.mem_FNP_iff_exists_bounded` gives the equivalent form in which the length bound
  is part of the decided predicate.
* `Cslib.Complexity.SolvesSearch R f`: a function `f : α → Option (List Bool)` *solves* `R` if
  `f a = some w` only for solutions `w` of `a`, and `f a = none` only when `a` has no solution.
* `Cslib.Complexity.FPSearch`: the relations in `FNP` solved by a polynomial-time function, with
  outputs encoded by `encOption encBits`. This is Papadimitriou's class `FP` of search problems
  [Papadimitriou, Section 10.3][Papadimitriou94]; it is named `FPSearch` to distinguish it from
  the class of polynomial-time computable functions.
* `Cslib.Complexity.TFNP`: the *total* relations in `FNP`, those for which every instance has a
  solution [MegiddoPapadimitriou1991].

`NP` is the class of domains of `FNP` relations (`Cslib.Complexity.mem_NP_iff_exists_FNP`), and
the domain of a relation in `FPSearch` is in `P` (`Cslib.Complexity.searchDomain_mem_P`). Hence
`FNP enc ⊆ FPSearch enc` implies `NP enc ⊆ P enc`
(`Cslib.Complexity.NP_subset_P_of_FNP_subset_FPSearch`). The converse, and the search-to-decision
reduction for `SAT`, are in `Complexity.Computability.Complexity.Classes.TFNP.SearchToDecision`.

Total problems arise from `NP ∩ coNP`: if `A` and its complement are domains of the `FNP`
relations `R` and `S`, then the disjoint sum `Cslib.Complexity.searchSum R S`, whose solutions are
`true :: u` for a solution `u` of `R` and `false :: u` for a solution `u` of `S`, is in `TFNP`.
Solving it in polynomial time decides `A`, so `TFNP enc ⊆ FPSearch enc` implies
`NP enc ∩ coNP enc ⊆ P enc` [MegiddoPapadimitriou1991]
(`Cslib.Complexity.NP_inter_coNP_subset_P_of_TFNP_subset_FPSearch`). The converse is not known,
and no relation is claimed to be hard here.

## Reductions

A *polynomial-time search reduction* from `R` to `S` (`Cslib.Complexity.SearchReducible`) is a
pair of polynomial-time functions: `f` maps instances of `R` to instances of `S`, and `g` maps a
solution `w` of `f a` back to the solution `g (a, w)` of `a`. This is the reduction of Megiddo and
Papadimitriou [MegiddoPapadimitriou1991] and of Johnson, Papadimitriou and Yannakakis
[JohnsonPapadimitriouYannakakis1988] used for `TFNP` and its subclasses. For relations that need
not be total, `f` must in addition map instances with a solution to instances with a solution (as
in Levin reductions); otherwise a solver for `S` reporting that `f a` has no solution would say
nothing about `a`. For a total target, this condition holds automatically
(`Cslib.Complexity.SearchReducible.of_isTotalSearch`), so on `TFNP` the definition is exactly the
one-way condition of the literature. A search reduction is in particular a polynomial-time
many-one reduction between the domains (`Cslib.Complexity.SearchReducible.polyTimeReducible`).

## Main definitions

* `Cslib.Complexity.searchDomain`, `Cslib.Complexity.IsTotalSearch`,
  `Cslib.Complexity.SolvesSearch`.
* `Cslib.Complexity.FNP`, `Cslib.Complexity.FPSearch`, `Cslib.Complexity.TFNP`.
* `Cslib.Complexity.verifierSearch`: the search problem of a verifier.
* `Cslib.Complexity.searchSum`: the disjoint sum of two search problems.
* `Cslib.Complexity.SearchReducible`, `Cslib.Complexity.SearchHard`,
  `Cslib.Complexity.SearchComplete`.

## Main results

* `Cslib.Complexity.FPSearch_subset_FNP`, `Cslib.Complexity.TFNP_subset_FNP`.
* `Cslib.Complexity.searchDomain_mem_NP`, `Cslib.Complexity.mem_NP_iff_exists_FNP`: `NP` is the
  class of domains of `FNP` relations.
* `Cslib.Complexity.searchDomain_mem_P`, `Cslib.Complexity.NP_subset_P_of_FNP_subset_FPSearch`.
* `Cslib.Complexity.searchSum_mem_TFNP`,
  `Cslib.Complexity.searchDomain_mem_P_of_searchSum_mem_FPSearch`,
  `Cslib.Complexity.NP_inter_coNP_subset_P_of_TFNP_subset_FPSearch`: the bridge to `NP ∩ coNP`.
* `Cslib.Complexity.SearchReducible.refl`, `Cslib.Complexity.SearchReducible.trans`: search
  reducibility is a preorder.
* `Cslib.Complexity.SearchReducible.mem_FPSearch`, `Cslib.Complexity.SearchReducible.isTotalSearch`,
  `Cslib.Complexity.SearchReducible.mem_TFNP`: closure of `FPSearch` and transfer of totality.
* `Cslib.Complexity.SearchHard.subset_FPSearch`: if a problem hard for a subclass of `FNP` is in
  `FPSearch`, so is the whole subclass.

## References

* [N. Megiddo, C. H. Papadimitriou, *On total functions, existence theorems and computational
  complexity*][MegiddoPapadimitriou1991]
* [D. S. Johnson, C. H. Papadimitriou, M. Yannakakis, *How easy is local
  search?*][JohnsonPapadimitriouYannakakis1988]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α β γ : Type}

/-! ### Search problems and solvers -/

section Basic

variable {R : α → List Bool → Prop}

/-- The instances of the search problem `R` that have a solution. -/
def searchDomain (R : α → List Bool → Prop) : Set α := {a | ∃ w, R a w}

theorem mem_searchDomain {a : α} : a ∈ searchDomain R ↔ ∃ w, R a w := Iff.rfl

/-- The search problem `R` is *total*: every instance has a solution. -/
def IsTotalSearch (R : α → List Bool → Prop) : Prop := ∀ a, ∃ w, R a w

theorem isTotalSearch_iff_searchDomain_eq_univ : IsTotalSearch R ↔ searchDomain R = Set.univ :=
  (Set.eq_univ_iff_forall (s := searchDomain R)).symm

/-- `f` *solves* the search problem `R`: it returns `some w` only for a solution `w`, and `none`
only on instances without solutions. -/
def SolvesSearch (R : α → List Bool → Prop) (f : α → Option (List Bool)) : Prop :=
  ∀ a, (∀ w, f a = some w → R a w) ∧ (f a = none → a ∉ searchDomain R)

variable {f : α → Option (List Bool)}

theorem SolvesSearch.rel (h : SolvesSearch R f) {a : α} {w : List Bool} (ha : f a = some w) :
    R a w :=
  (h a).1 w ha

theorem SolvesSearch.notMem (h : SolvesSearch R f) {a : α} (ha : f a = none) :
    a ∉ searchDomain R :=
  (h a).2 ha

/-- A solver finds a solution exactly on the instances that have one. -/
theorem SolvesSearch.isSome_iff (h : SolvesSearch R f) {a : α} :
    (f a).isSome ↔ a ∈ searchDomain R := by
  cases ha : f a with
  | none => simpa using h.notMem ha
  | some w => simpa using ⟨w, h.rel ha⟩

/-- A function that always returns a solution solves the search problem. -/
theorem solvesSearch_some {g : α → List Bool} (hg : ∀ a, R a (g a)) :
    SolvesSearch R fun a => some (g a) :=
  fun a => ⟨fun _ h => Option.some_injective _ h ▸ hg a, fun h => (Option.some_ne_none _ h).elim⟩

/-- A solver of a total search problem never returns `none`. -/
theorem SolvesSearch.rel_getD (h : SolvesSearch R f) (htot : IsTotalSearch R) (a : α)
    (d : List Bool) : R a ((f a).getD d) := by
  cases ha : f a with
  | none => exact (h.notMem ha (htot a)).elim
  | some w => exact h.rel ha

end Basic

/-! ### The classes -/

/-- The search problems in `FNP` with respect to the encoding `enc` of instances: relations that
are polynomially balanced, every solution of `a` having length at most `p (enc a).length` for a
polynomial `p`, and decided by a polynomial-time function of the instance and the candidate
solution [Papadimitriou, Section 10.3][Papadimitriou94]. -/
def FNP (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | (∃ p : Polynomial ℕ, ∀ a w, R a w → w.length ≤ p.eval (enc a).length) ∧
    ∃ V : α × List Bool → Bool, ComputableInPolyTime V (encPair enc encBits) encBool ∧
      ∀ a w, R a w ↔ V (a, w) = true}

/-- The search problems in `FNP` solved by a polynomial-time function, Papadimitriou's class `FP`
of search problems [Papadimitriou, Section 10.3][Papadimitriou94]. -/
def FPSearch (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ ∃ f : α → Option (List Bool),
    ComputableInPolyTime f enc (encOption encBits) ∧ SolvesSearch R f}

/-- The total search problems in `FNP` [Megiddo and Papadimitriou][MegiddoPapadimitriou1991]. -/
def TFNP (enc : α ↪ List Bool) : Set (α → List Bool → Prop) :=
  {R | R ∈ FNP enc ∧ IsTotalSearch R}

variable {enc : α ↪ List Bool} {R S : α → List Bool → Prop}

theorem mem_FNP : R ∈ FNP enc ↔
    (∃ p : Polynomial ℕ, ∀ a w, R a w → w.length ≤ p.eval (enc a).length) ∧
      ∃ V : α × List Bool → Bool, ComputableInPolyTime V (encPair enc encBits) encBool ∧
        ∀ a w, R a w ↔ V (a, w) = true :=
  Iff.rfl

theorem mem_FPSearch : R ∈ FPSearch enc ↔ R ∈ FNP enc ∧ ∃ f : α → Option (List Bool),
    ComputableInPolyTime f enc (encOption encBits) ∧ SolvesSearch R f :=
  Iff.rfl

theorem mem_TFNP : R ∈ TFNP enc ↔ R ∈ FNP enc ∧ IsTotalSearch R := Iff.rfl

/-- Every search problem in `FPSearch` is in `FNP`. -/
theorem FPSearch_subset_FNP : FPSearch enc ⊆ FNP enc := fun _ h => h.1

/-- Every search problem in `TFNP` is in `FNP`. -/
theorem TFNP_subset_FNP : TFNP enc ⊆ FNP enc := fun _ h => h.1

/-- **`FNP` with the length bound in the verifier.** A relation is in `FNP` exactly when it holds
of the candidate solutions of length at most `p (enc a).length` accepted by a polynomial-time
verifier. -/
theorem mem_FNP_iff_exists_bounded : R ∈ FNP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        ∀ a w, R a w ↔ w.length ≤ p.eval (enc a).length ∧ V (a, w) = true := by
  rw [mem_FNP]
  constructor
  · rintro ⟨⟨p, hp⟩, V, hV, hR⟩
    exact ⟨p, V, hV, fun a w => ⟨fun h => ⟨hp a w h, (hR a w).1 h⟩, fun h => (hR a w).2 h.2⟩⟩
  · rintro ⟨p, V, hV, hR⟩
    refine ⟨⟨p, fun a w h => ((hR a w).1 h).1⟩,
      fun x => decide (x.2.length ≤ p.eval (enc x.1).length) && V x, ?_, fun a w => ?_⟩
    · exact bool_and' (unary_le' (length_bits.comp (snd enc encBits))
        ((unary_eval p).comp ((encoding_length enc).comp (fst enc encBits)))) hV
    · simp only [hR a w, Bool.and_eq_true, decide_eq_true_eq]

/-- A polynomial-time solver of a total relation in `FNP` puts it in `FPSearch`. -/
theorem mem_FPSearch_of_total (hR : R ∈ FNP enc) {g : α → List Bool}
    (hg : ComputableInPolyTime g enc encBits) (h : ∀ a, R a (g a)) : R ∈ FPSearch enc := by
  exact ⟨hR, _, ((optionSome encBits).comp hg), solvesSearch_some h⟩

/-- A total relation in `FPSearch` has a polynomial-time function returning a solution. -/
theorem exists_total_of_mem_FPSearch (hR : R ∈ FPSearch enc) (htot : IsTotalSearch R) :
    ∃ g : α → List Bool, ComputableInPolyTime g enc encBits ∧ ∀ a, R a (g a) :=
  let ⟨_, f, hf, hsolve⟩ := hR
  ⟨fun a => (f a).getD [], optionGetDWithInput hf (const []),
    fun a => hsolve.rel_getD htot a []⟩

/-! ### Domains and `NP` -/

/-- **Domains of `FNP` relations are in `NP`**: a solution, framed and padded, is a certificate. -/
theorem searchDomain_mem_NP (hR : R ∈ FNP enc) : searchDomain R ∈ NP enc := by
  obtain ⟨⟨p, hp⟩, V, hV, hR⟩ := mem_FNP.mp hR
  exact mem_NP_of_witness (encW := encBits)
    ⟨fun w => w, fun _ => rfl, ComputableInPolyTime.id'.exists_degree⟩
    hV
    (fun a w => (hR a w).symm) fun a w h => ⟨w, h, hp a w h⟩

/-- The search problem of a verifier: the certificates of the prescribed length that it accepts. -/
def verifierSearch (enc : α ↪ List Bool) (p : Polynomial ℕ) (V : α × List Bool → Bool) (a : α)
    (w : List Bool) : Prop :=
  w.length = p.eval (enc a).length ∧ V (a, w) = true

/-- The search problem of a polynomial-time verifier is in `FNP`. -/
theorem verifierSearch_mem_FNP {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    verifierSearch enc p V ∈ FNP enc := by
  refine mem_FNP.mpr ⟨⟨p, fun a w h => h.1.le⟩,
    fun x => decide (x.2.length = p.eval (enc x.1).length) && V x, ?_, fun a w => ?_⟩
  · exact (bool_and' (decide_eq' (length_bits.comp (snd enc encBits))
      ((unary_eval p).comp ((encoding_length enc).comp (fst enc encBits)))) hV)
  · simp only [verifierSearch, Bool.and_eq_true, decide_eq_true_eq]

/-- A verifier verifies exactly the domain of its search problem. -/
theorem IsVerifier.searchDomain_eq {p : Polynomial ℕ} {V : α × List Bool → Bool} {A : Set α}
    (h : IsVerifier enc p V A) : searchDomain (verifierSearch enc p V) = A :=
  Set.ext fun a => (h a).symm

/-- **`NP` is the class of domains of `FNP` relations.** -/
theorem mem_NP_iff_exists_FNP {A : Set α} : A ∈ NP enc ↔ ∃ R ∈ FNP enc, searchDomain R = A :=
  ⟨fun ⟨_, _, hV, hA⟩ => ⟨_, verifierSearch_mem_FNP hV, hA.searchDomain_eq⟩,
    fun ⟨_, hR, hA⟩ => hA ▸ searchDomain_mem_NP hR⟩

/-- **Domains of `FPSearch` relations are in `P`**: test whether the solver finds a solution. -/
theorem searchDomain_mem_P (hR : R ∈ FPSearch enc) : searchDomain R ∈ P enc :=
  let ⟨_, f, hf, hsolve⟩ := hR
  ⟨fun a => (f a).isSome, (optionIsSome hf), fun _ => hsolve.isSome_iff.symm⟩

/-- **If every `FNP` relation is in `FPSearch`, then `NP ⊆ P`** for the encoding `enc`. -/
theorem NP_subset_P_of_FNP_subset_FPSearch (h : FNP enc ⊆ FPSearch enc) : NP enc ⊆ P enc :=
  fun _ hA =>
    let ⟨_, hR, hRA⟩ := mem_NP_iff_exists_FNP.1 hA
    hRA ▸ searchDomain_mem_P (h hR)

/-! ### Disjoint sums and `NP ∩ coNP` -/

/-- The disjoint sum of the search problems `R` and `S`: the solutions of `a` are `true :: u` for
the solutions `u` of `a` in `R`, and `false :: u` for the solutions `u` of `a` in `S`. -/
def searchSum (R S : α → List Bool → Prop) (a : α) : List Bool → Prop
  | [] => False
  | true :: u => R a u
  | false :: u => S a u

@[simp]
theorem searchSum_nil {a : α} : ¬searchSum R S a [] := id

@[simp]
theorem searchSum_true_cons {a : α} {u : List Bool} : searchSum R S a (true :: u) ↔ R a u :=
  Iff.rfl

@[simp]
theorem searchSum_false_cons {a : α} {u : List Bool} : searchSum R S a (false :: u) ↔ S a u :=
  Iff.rfl

theorem searchDomain_searchSum : searchDomain (searchSum R S) = searchDomain R ∪ searchDomain S :=
  Set.ext fun _ => ⟨fun ⟨w, hw⟩ => match w, hw with
    | true :: u, hw => .inl ⟨u, hw⟩
    | false :: u, hw => .inr ⟨u, hw⟩,
    fun h => h.elim (fun ⟨u, hu⟩ => ⟨true :: u, hu⟩) fun ⟨u, hu⟩ => ⟨false :: u, hu⟩⟩

/-- `FNP` is closed under disjoint sums. -/
theorem searchSum_mem_FNP (hR : R ∈ FNP enc) (hS : S ∈ FNP enc) : searchSum R S ∈ FNP enc := by
  obtain ⟨⟨p, hp⟩, V, hV, hRV⟩ := mem_FNP.mp hR
  obtain ⟨⟨q, hq⟩, W, hW, hSW⟩ := mem_FNP.mp hS
  refine mem_FNP.mpr ⟨⟨p + q + 1, fun a w h => ?_⟩,
    fun x => !x.2.isEmpty && if x.2.headD false then V (x.1, x.2.tail) else W (x.1, x.2.tail),
    ?_, fun a w => ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_one]
    match w, h with
    | true :: u, h =>
      have := hp a u h
      simp only [List.length_cons]
      omega
    | false :: u, h =>
      have := hq a u h
      simp only [List.length_cons]
      omega
  · have htail : ComputableInPolyTime (fun x : α × List Bool => (x.1, x.2.tail))
        (encPair enc encBits) (encPair enc encBits) :=
      (fst enc encBits).prod (bitsTail.comp (snd enc encBits))
    refine (bool_and' (bool_not.comp ?_)
      (ite' (encC := encBool) ?_ (hV.comp htail) (hW.comp htail)))
    · fun_prop
    · fun_prop
  · match w with
    | [] => simp
    | true :: u => simp [hRV]
    | false :: u => simp [hSW]

/-- The disjoint sum of search problems whose domains cover all instances is total. -/
theorem isTotalSearch_searchSum (h : ∀ a, a ∈ searchDomain R ∨ a ∈ searchDomain S) :
    IsTotalSearch (searchSum R S) := fun a => by
  rw [← mem_searchDomain, searchDomain_searchSum]
  exact h a

/-- The disjoint sum of `FNP` relations whose domains cover all instances is in `TFNP`. -/
theorem searchSum_mem_TFNP (hR : R ∈ FNP enc) (hS : S ∈ FNP enc)
    (h : ∀ a, a ∈ searchDomain R ∨ a ∈ searchDomain S) : searchSum R S ∈ TFNP enc :=
  ⟨searchSum_mem_FNP hR hS, isTotalSearch_searchSum h⟩

/-- **Problems in `NP ∩ coNP` give total search problems**: if `A` and its complement are in `NP`,
then `A` and `Aᶜ` are domains of `FNP` relations whose disjoint sum is in `TFNP`. -/
theorem exists_searchSum_mem_TFNP {A : Set α} (hA : A ∈ NP enc) (hA' : A ∈ coNP enc) :
    ∃ R S, searchDomain R = A ∧ searchDomain S = Aᶜ ∧ searchSum R S ∈ TFNP enc := by
  obtain ⟨R, hR, rfl⟩ := mem_NP_iff_exists_FNP.1 hA
  obtain ⟨S, hS, hSA⟩ := mem_NP_iff_exists_FNP.1 hA'
  refine ⟨R, S, rfl, hSA, searchSum_mem_TFNP hR hS fun a => ?_⟩
  rw [hSA]
  exact em _

/-- **Solving a disjoint sum decides the first domain.** If the domains of `R` and `S` are
disjoint and `searchSum R S` is in `FPSearch`, the domain of `R` is in `P`: an instance is in it
exactly when the solver returns a solution tagged `true`. -/
theorem searchDomain_mem_P_of_searchSum_mem_FPSearch (hRS : searchSum R S ∈ FPSearch enc)
    (hdisj : Disjoint (searchDomain R) (searchDomain S)) : searchDomain R ∈ P enc := by
  obtain ⟨-, f, hf, hsolve⟩ := mem_FPSearch.mp hRS
  refine mem_P.mpr ⟨fun a => ((f a).getD []).headD false, ?_, fun a => ?_⟩
  · have hget := optionGetDWithInput hf
      (const [] : ComputableInPolyTime (fun _ : α => ([] : List Bool)) enc encBits)
    fun_prop
  · change a ∈ searchDomain R ↔ ((f a).getD []).headD false = true
    cases ha : f a with
    | none =>
      have := hsolve.notMem ha
      rw [searchDomain_searchSum] at this
      exact ⟨fun h => (this (.inl h)).elim, fun h => by simp at h⟩
    | some w =>
      have hw := hsolve.rel ha
      rcases w with _ | ⟨_ | _, u⟩
      · exact hw.elim
      · exact ⟨fun h => (Set.disjoint_left.1 hdisj h ⟨u, hw⟩).elim, fun h => by simp at h⟩
      · exact ⟨fun _ => rfl, fun _ => ⟨u, hw⟩⟩

/-- **If every `TFNP` relation is in `FPSearch`, then `NP ∩ coNP ⊆ P`** for the encoding `enc`
[MegiddoPapadimitriou1991]. -/
theorem NP_inter_coNP_subset_P_of_TFNP_subset_FPSearch (h : TFNP enc ⊆ FPSearch enc) :
    NP enc ∩ coNP enc ⊆ P enc := fun A ⟨hA, hA'⟩ => by
  obtain ⟨R, S, rfl, hS, hRS⟩ := exists_searchSum_mem_TFNP hA hA'
  exact searchDomain_mem_P_of_searchSum_mem_FPSearch (h hRS)
    (hS ▸ disjoint_compl_right)

/-! ### Search reductions -/

/-- A **polynomial-time search reduction** from `R` to `S`: a polynomial-time map `f` of
instances that maps instances with a solution to instances with a solution, and a
polynomial-time map `g` taking a solution `w` of `f a` back to a solution `g (a, w)` of `a`. -/
def SearchReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (R : α → List Bool → Prop)
    (S : β → List Bool → Prop) : Prop :=
  ∃ (f : α → β) (g : α × List Bool → List Bool), ComputableInPolyTime f encA encB ∧
    ComputableInPolyTime g (encPair encA encBits) encBits ∧
      (∀ a, a ∈ searchDomain R → f a ∈ searchDomain S) ∧ ∀ a w, S (f a) w → R a (g (a, w))

/-- `S` is hard for the class `𝒞` of search problems under search reductions: every problem in
`𝒞`, with any encoding of its instances, reduces to `S`. This is `HardUnder` for
`SearchReducible`. -/
def SearchHard (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (α → List Bool → Prop))
    (encB : β ↪ List Bool) (S : β → List Bool → Prop) : Prop :=
  HardUnder (fun enc => SearchReducible enc encB) @𝒞 S

/-- `S` is complete for the class `𝒞` of search problems: it is in `𝒞` and hard for it. This is
`CompleteUnder` for `SearchReducible` (`searchComplete_iff_completeUnder`), with its second conjunct
stated as `SearchHard`. -/
def SearchComplete (𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (α → List Bool → Prop))
    (encB : β ↪ List Bool) (S : β → List Bool → Prop) : Prop :=
  S ∈ 𝒞 encB ∧ SearchHard 𝒞 encB S

/-- Search hardness is hardness under `SearchReducible`. -/
theorem searchHard_iff_hardUnder {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (α → List Bool → Prop)}
    {encB : β ↪ List Bool} {S : β → List Bool → Prop} :
    SearchHard 𝒞 encB S ↔ HardUnder (fun enc => SearchReducible enc encB) @𝒞 S :=
  Iff.rfl

/-- Search completeness is completeness under `SearchReducible`. -/
theorem searchComplete_iff_completeUnder
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (α → List Bool → Prop)}
    {encB : β ↪ List Bool} {S : β → List Bool → Prop} :
    SearchComplete 𝒞 encB S ↔ CompleteUnder (fun enc => SearchReducible enc encB) @𝒞 encB S :=
  Iff.rfl

section Reductions

variable {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {T : β → List Bool → Prop} {U : γ → List Bool → Prop}

/-- For a total target, the one-way condition on solutions suffices for a search reduction. -/
theorem SearchReducible.of_isTotalSearch (hT : IsTotalSearch T) {f : α → β}
    {g : α × List Bool → List Bool} (hf : ComputableInPolyTime f encA encB)
    (hg : ComputableInPolyTime g (encPair encA encBits) encBits)
    (h : ∀ a w, T (f a) w → R a (g (a, w))) : SearchReducible encA encB R T := by
  exact ⟨f, g, hf, hg, fun a _ => hT (f a), h⟩

/-- Every search problem reduces to itself. -/
@[refl]
theorem SearchReducible.refl (encA : α ↪ List Bool) (R : α → List Bool → Prop) :
    SearchReducible encA encA R R :=
  ⟨id, Prod.snd, .id', .snd encA encBits, fun _ h => h, fun _ _ h => h⟩

/-- Search reductions compose. -/
@[trans]
theorem SearchReducible.trans (hRT : SearchReducible encA encB R T)
    (hTU : SearchReducible encB encC T U) : SearchReducible encA encC R U :=
  let ⟨f, g, hf, hg, hdom, hsol⟩ := hRT
  let ⟨f', g', hf', hg', hdom', hsol'⟩ := hTU
  ⟨f' ∘ f, fun x => g (x.1, g' (f x.1, x.2)), hf'.comp hf, by fun_prop,
    fun a ha => hdom' _ (hdom a ha), fun a w h => hsol a _ (hsol' (f a) w h)⟩

/-- A search reduction is a polynomial-time many-one reduction between the domains. -/
theorem SearchReducible.polyTimeReducible (h : SearchReducible encA encB R T) :
    PolyTimeReducible encA encB (searchDomain R) (searchDomain T) :=
  let ⟨f, _, hf, _, hdom, hsol⟩ := h
  ⟨f, hf, fun a => ⟨hdom a, fun ⟨w, hw⟩ => ⟨_, hsol a w hw⟩⟩⟩

/-- **Totality transfers backwards along search reductions.** -/
theorem SearchReducible.isTotalSearch (h : SearchReducible encA encB R T)
    (hT : IsTotalSearch T) : IsTotalSearch R :=
  let ⟨f, _, _, _, _, hsol⟩ := h
  fun a => let ⟨w, hw⟩ := hT (f a); ⟨_, hsol a w hw⟩

/-- An `FNP` relation that reduces to a `TFNP` relation is in `TFNP`. -/
theorem SearchReducible.mem_TFNP (h : SearchReducible encA encB R T) (hR : R ∈ FNP encA)
    (hT : T ∈ TFNP encB) : R ∈ TFNP encA :=
  ⟨hR, h.isTotalSearch hT.2⟩

/-- **`FPSearch` is closed under search reductions**: an `FNP` relation that reduces to a relation
in `FPSearch` is in `FPSearch`. -/
theorem SearchReducible.mem_FPSearch (h : SearchReducible encA encB R T) (hR : R ∈ FNP encA)
    (hT : T ∈ FPSearch encB) : R ∈ FPSearch encA := by
  obtain ⟨f, g, hf, hg, hdom, hsol⟩ := h
  obtain ⟨-, s, hs, hsolve⟩ := Complexity.mem_FPSearch.mp hT
  refine Complexity.mem_FPSearch.mpr ⟨hR, fun a => (s (f a)).elim none fun w => some (g (a, w)),
    (optionElimWithInput (hs.comp hf) (const none)
      ((optionSome encBits).comp hg)),
    fun a => ⟨fun w ha => ?_, fun ha hR => ?_⟩⟩
  · cases hsa : s (f a) with
    | none => simp [hsa] at ha
    | some v =>
      simp only [hsa, Option.elim_some, Option.some.injEq] at ha
      exact ha ▸ hsol a v (hsolve.rel hsa)
  · cases hsa : s (f a) with
    | none => exact hsolve.notMem hsa (hdom a hR)
    | some v => simp [hsa] at ha

section Hardness

variable {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (α → List Bool → Prop)}

/-- Hardness transfers along search reductions. -/
theorem SearchHard.trans (hT : SearchHard 𝒞 encB T) (hTU : SearchReducible encB encC T U) :
    SearchHard 𝒞 encC U :=
  HardUnder.trans (fun _ _ h h' => h.trans h') hT hTU

/-- **A hard problem in `FPSearch` collapses the class.** If every problem of `𝒞` is in `FNP` and
a `𝒞`-hard problem is in `FPSearch`, then every problem of `𝒞` is in `FPSearch`. -/
theorem SearchHard.subset_FPSearch (h𝒞 : ∀ {α : Type} (enc : α ↪ List Bool), 𝒞 enc ⊆ FNP enc)
    (hT : SearchHard 𝒞 encB T) (hT' : T ∈ FPSearch encB) (enc : α ↪ List Bool) :
    𝒞 enc ⊆ FPSearch enc :=
  fun R hR => (hT enc R hR).mem_FPSearch (h𝒞 enc hR) hT'

/-- A `TFNP`-complete problem is in `FPSearch` exactly when all of `TFNP` is. -/
theorem SearchComplete.TFNP_subset_FPSearch_iff {β : Type} {encB : β ↪ List Bool}
    {T : β → List Bool → Prop} (hT : SearchComplete @TFNP encB T) :
    T ∈ FPSearch encB ↔ ∀ {α : Type} (enc : α ↪ List Bool), TFNP enc ⊆ FPSearch enc :=
  ⟨fun h _ enc => SearchHard.subset_FPSearch (fun _ => TFNP_subset_FNP) hT.2 h enc,
    fun h => h encB hT.1⟩

end Hardness

end Reductions

end Cslib.Complexity
