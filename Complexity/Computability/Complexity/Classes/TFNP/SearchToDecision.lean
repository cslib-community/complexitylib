/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.TFNP
public import Complexity.Computability.Complexity.Problems.SAT
import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Classes.NP.SelfReduction
import Complexity.Computability.Complexity.Classes.P.Complement
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Search to decision: `FPSearch = FNP` exactly when `P = NP`

Every search problem in `FNP` reduces to a decision problem in `NP`
[Papadimitriou, Section 10.3][Papadimitriou94], [Arora and Barak, Section 2.5][AroraBarak09]: its
*prefix problem* (`Cslib.Complexity.prefixSearch`) asks, given an instance `a` and a word `u`,
whether some solution of `a` begins with `u`. A decision procedure `D` for it finds solutions bit
by bit (`Cslib.Complexity.prefixSearchRun`): starting from the empty word, stop when the current
word is a solution, and otherwise extend it by `false` when `D` says that a solution begins with
the extension, and by `true` otherwise. As long as some solution begins with the current word,
this stays true, and the word grows by one bit at every step until it is a solution; since
solutions are no longer than `p (enc a).length`, that many steps suffice
(`Cslib.Complexity.rel_prefixSearchRun`).

Hence if `NP ⊆ P` for the encoding of pairs of instances and words, every `FNP` relation is in
`FPSearch` (`Cslib.Complexity.FNP_subset_FPSearch_of_NP_subset_P`), and with
`Cslib.Complexity.NP_subset_P_of_FNP_subset_FPSearch`, `FNP ⊆ FPSearch` for every encoding exactly
when `NP ⊆ P` for every encoding (`Cslib.Complexity.FNP_subset_FPSearch_iff`). Through the
Cook–Levin theorem this happens exactly when `SAT ∈ P`
(`Cslib.Complexity.FNP_subset_FPSearch_iff_SAT_mem_P`).

For `SAT` itself the self-reduction of
`Complexity.Computability.Complexity.Classes.NP.SelfReduction` finds satisfying assignments
directly: the search problem `Cslib.Complexity.SAT.searchRel` of assignment certificates is in
`FPSearch` exactly when `SAT ∈ P`
(`Cslib.Complexity.SAT.searchRel_mem_FPSearch_iff`).

## Main definitions

* `Cslib.Complexity.prefixSearch`: the prefix problem of a search problem.
* `Cslib.Complexity.prefixSearchStep`, `Cslib.Complexity.prefixSearchRun`: search through prefixes.
* `Cslib.Complexity.SAT.searchRel`: the search problem of satisfying assignments.

## Main results

* `Cslib.Complexity.prefixSearch_mem_FNP`: the prefix problem of an `FNP` relation is in `FNP`, so
  its domain is in `NP`.
* `Cslib.Complexity.rel_prefixSearchRun`: with a correct decision procedure for the prefix problem,
  the search through prefixes finds a solution of every instance that has one.
* `Cslib.Complexity.FNP_subset_FPSearch_of_NP_subset_P`, `Cslib.Complexity.FNP_subset_FPSearch_iff`,
  `Cslib.Complexity.FNP_subset_FPSearch_iff_SAT_mem_P`.
* `Cslib.Complexity.SAT.searchRel_mem_FNP`, `Cslib.Complexity.SAT.searchDomain_searchRel`,
  `Cslib.Complexity.SAT.searchRel_mem_FPSearch_iff`.

## References

* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool} {R : α → List Bool → Prop}

/-! ### The prefix problem -/

/-- The prefix problem of `R`: the solutions of a pair `(a, u)` are the words `v` such that
`u ++ v` is a solution of `a`. Its domain consists of the pairs `(a, u)` such that some solution of
`a` begins with `u`. -/
def prefixSearch (R : α → List Bool → Prop) (x : α × List Bool) (v : List Bool) : Prop :=
  R x.1 (x.2 ++ v)

/-- The prefix problem of an `FNP` relation is in `FNP`. -/
theorem prefixSearch_mem_FNP (hR : R ∈ FNP enc) : prefixSearch R ∈ FNP (encPair enc encBits) := by
  obtain ⟨⟨p, hp⟩, V, hV, hRV⟩ := mem_FNP.mp hR
  refine mem_FNP.mpr
    ⟨⟨p, fun x v h => ?_⟩, fun y => V (y.1.1, y.1.2 ++ y.2), ?_, fun x v => hRV _ _⟩
  · have h₁ := hp _ _ h
    have h₂ := Polynomial.eval_mono p (length_le_encPair_left enc encBits x)
    simp only [List.length_append] at h₁
    omega
  · exact (hV.comp ((fst (encPair enc encBits) encBits).fst'.prod
      (bitsAppend (fst (encPair enc encBits) encBits).snd' (snd (encPair enc encBits) encBits))))

/-! ### Search through prefixes -/

/-- One step of the search through prefixes, with `V` deciding solutions and `D` deciding the
prefix problem: keep a solution, and otherwise extend the word by `false` if `D` accepts the
extension, and by `true` if not. -/
def prefixSearchStep (V D : α × List Bool → Bool) (a : α) (u : List Bool) : List Bool :=
  if V (a, u) then u else if D (a, u ++ [false]) then u ++ [false] else u ++ [true]

/-- The search through prefixes for `n a` steps, starting from the empty word. -/
def prefixSearchRun (V D : α × List Bool → Bool) (n : α → ℕ) (a : α) : List Bool :=
  (List.replicate (n a) false).foldl (fun u _ => prefixSearchStep V D a u) []

section Correctness

variable {V D : α × List Bool → Bool} (hV : ∀ a w, R a w ↔ V (a, w) = true)
  (hD : ∀ a u, D (a, u) = true ↔ ∃ v, R a (u ++ v))
include hV

/-- A solution is kept by the search. -/
private theorem foldl_prefixSearchStep_of_rel {a : α} {u : List Bool} (hu : R a u) (l : List Bool) :
    l.foldl (fun u _ => prefixSearchStep V D a u) u = u := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldl_cons, prefixSearchStep, ite_eq_left ((hV a u).1 hu)]
    exact ih

include hD

/-- A step from a word that some solution extends, but that is not a solution, adds one bit and
keeps a solution extending the word. -/
private theorem prefixSearchStep_spec {a : α} {u : List Bool} (hu : ∃ v, R a (u ++ v))
    (hnot : ¬R a u) :
    (∃ v, R a (prefixSearchStep V D a u ++ v)) ∧
      (prefixSearchStep V D a u).length = u.length + 1 := by
  have hVu : ¬V (a, u) = true := fun h => hnot ((hV a u).2 h)
  obtain ⟨v, hv⟩ := hu
  rw [prefixSearchStep, ite_eq_right hVu]
  by_cases hDu : D (a, u ++ [false]) = true
  · rw [ite_eq_left hDu]
    exact ⟨(hD _ _).1 hDu, by simp⟩
  · rw [ite_eq_right hDu]
    refine ⟨?_, by simp⟩
    rcases v with _ | ⟨_ | _, v⟩
    · exact (hnot (by simpa using hv)).elim
    · exact (hDu ((hD _ _).2 ⟨v, by simpa using hv⟩)).elim
    · exact ⟨v, by simpa using hv⟩

/-- The search through prefixes keeps a solution extending the word, and the word is a solution or
has grown by one bit per step. -/
private theorem foldl_prefixSearchStep_spec {a : α} (l : List Bool) {u : List Bool}
    (hu : ∃ v, R a (u ++ v)) :
    (∃ v, R a (l.foldl (fun u _ => prefixSearchStep V D a u) u ++ v)) ∧
      (R a (l.foldl (fun u _ => prefixSearchStep V D a u) u) ∨
        u.length + l.length ≤ (l.foldl (fun u _ => prefixSearchStep V D a u) u).length) := by
  induction l generalizing u with
  | nil => exact ⟨hu, .inr le_rfl⟩
  | cons b l ih =>
    by_cases hRu : R a u
    · rw [foldl_prefixSearchStep_of_rel hV hRu]
      exact ⟨hu, .inl hRu⟩
    · obtain ⟨hstep, hlen⟩ := prefixSearchStep_spec hV hD hu hRu
      obtain ⟨h₁, h₂⟩ := ih hstep
      refine ⟨h₁, h₂.imp_right fun h => ?_⟩
      rw [List.foldl_cons]
      simp only [List.length_cons, hlen] at h ⊢
      omega

/-- **Search through prefixes is correct.** If the solutions of `a` are no longer than `n a`, and
`a` has a solution, the search through prefixes for `n a` steps finds one. -/
theorem rel_prefixSearchRun {n : α → ℕ} (hn : ∀ a w, R a w → w.length ≤ n a) {a : α}
    (ha : a ∈ searchDomain R) : R a (prefixSearchRun V D n a) := by
  obtain ⟨⟨v, hv⟩, h⟩ := foldl_prefixSearchStep_spec hV hD (List.replicate (n a) false)
    (u := []) (a := a) (let ⟨w, hw⟩ := ha; ⟨w, by simpa using hw⟩)
  rw [← prefixSearchRun] at hv h
  rcases h with h | hlen
  · exact h
  · have := hn a _ hv
    simp only [List.length_append, List.length_nil, List.length_replicate, zero_add] at hlen this
    have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    simpa [hv0] using hv

end Correctness

/-- The search through prefixes is polynomial-time when `V`, `D` and the number of steps are. -/
private theorem computableInPolyTime_prefixSearchRun {V D : α × List Bool → Bool} {n : α → ℕ}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hD : ComputableInPolyTime D (encPair enc encBits) encBool)
    (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (prefixSearchRun V D n) enc encBits := by
  have hstep : ComputableInPolyTime
      (fun y : (α × List Bool) × Bool => prefixSearchStep V D y.1.1 y.1.2)
      (encPair (encPair enc encBits) encBool) encBits := by
    have hu : ComputableInPolyTime (fun y : (α × List Bool) × Bool => y.1.2)
        (encPair (encPair enc encBits) encBool) encBits := (fst _ _).snd'
    have ha : ComputableInPolyTime (fun y : (α × List Bool) × Bool => y.1.1)
        (encPair (encPair enc encBits) encBool) enc := (fst _ _).fst'
    have happ (b : Bool) : ComputableInPolyTime
        (fun y : (α × List Bool) × Bool => y.1.2 ++ [b])
        (encPair (encPair enc encBits) encBool) encBits := bitsAppend hu (const [b])
    unfold prefixSearchStep
    exact ite' (encC := encBool) (hV.comp (ha.prod hu)) hu
      (ite' (encC := encBool) (hD.comp (ha.prod (happ false))) (happ false) (happ true))
  unfold prefixSearchRun
  refine foldlWithInput_of_bounded_growth (const []) ⟨(bitsReplicate false).comp hn, hstep,
    inferInstance, inferInstance⟩ (growth := fun _ => 1) ⟨.const 1, fun a u _ _ => ?_⟩
  simp only [encBits, Function.Embedding.refl_apply, prefixSearchStep]
  split_ifs <;> simp

/-! ### `FPSearch = FNP` exactly when `P = NP` -/

/-- **Search reduces to decision**: if the `NP` problems on pairs of instances and words are in
`P`, every `FNP` relation is in `FPSearch`. The solver decides the prefix problem, searches through
prefixes, and checks the result. -/
theorem FNP_subset_FPSearch_of_NP_subset_P
    (h : NP (encPair enc encBits) ⊆ P (encPair enc encBits)) : FNP enc ⊆ FPSearch enc := by
  intro R hR
  obtain ⟨⟨p, hp⟩, V, hV, hRV⟩ := mem_FNP.mp hR
  obtain ⟨D, hD, hDR⟩ := mem_P.mp
    (h (searchDomain_mem_NP (prefixSearch_mem_FNP (mem_FNP.mpr ⟨⟨p, hp⟩, V, hV, hRV⟩))))
  let n : α → ℕ := fun a => p.eval (enc a).length
  have hn : ComputableInPolyTime n enc encUnary := (unary_eval p).comp (encoding_length enc)
  have hrun := computableInPolyTime_prefixSearchRun hV hD hn
  refine mem_FPSearch.mpr
    ⟨mem_FNP.mpr ⟨⟨p, hp⟩, V, hV, hRV⟩, fun a => if V (a, prefixSearchRun V D n a) then
    some (prefixSearchRun V D n a) else none, ?_, fun a => ?_⟩
  · exact 
      (ite' (encC := encBool) (hV.comp (id'.prod hrun)) ((optionSome encBits).comp hrun)
        (const none))
  · have hcorrect := rel_prefixSearchRun hRV (fun a u => (hDR (a, u)).symm) hp (a := a)
    constructor
    · intro w hw
      beta_reduce at hw
      split_ifs at hw with hVa
      exact Option.some_injective _ hw ▸ (hRV _ _).2 hVa
    · intro hw ha
      beta_reduce at hw
      split_ifs at hw with hVa
      exact hVa ((hRV _ _).1 (hcorrect ha))

/-- **`FPSearch = FNP` exactly when `P = NP`**, both for every encoding of instances. -/
theorem FNP_subset_FPSearch_iff :
    (∀ {α : Type} (enc : α ↪ List Bool), FNP enc ⊆ FPSearch enc) ↔
      ∀ {α : Type} (enc : α ↪ List Bool), NP enc ⊆ P enc :=
  ⟨fun h _ enc => NP_subset_P_of_FNP_subset_FPSearch (h enc),
    fun h _ enc => FNP_subset_FPSearch_of_NP_subset_P (h (encPair enc encBits))⟩

/-- **`FPSearch = FNP` exactly when `SAT ∈ P`**, by the Cook–Levin theorem. -/
theorem FNP_subset_FPSearch_iff_SAT_mem_P :
    (∀ {α : Type} (enc : α ↪ List Bool), FNP enc ⊆ FPSearch enc) ↔ SAT ∈ P encCNF := by
  rw [FNP_subset_FPSearch_iff, SAT_mem_P_iff]
  exact ⟨fun h _ e => le_antisymm P_subset_NP (h e), fun h _ e => (h e).ge⟩

/-! ### `SAT` -/

namespace SAT

/-- The search problem of `SAT`: certificates for `SAT.verifier`, listing the values of the
variables in order of first occurrence, that are no longer than the encoded formula. -/
def searchRel (φ : Logic.PL.CNF ℕ) (w : List Bool) : Prop :=
  w.length ≤ (encCNF φ).length ∧ verifier (φ, w) = true

/-- The search problem of `SAT` is in `FNP`. -/
theorem searchRel_mem_FNP : searchRel ∈ FNP encCNF :=
  mem_FNP_iff_exists_bounded.2 ⟨Polynomial.X, verifier, computableInPolyTime_verifier,
    fun _ _ => by simp [searchRel]⟩

/-- The formulas with a solution in `SAT.searchRel` are the satisfiable ones. -/
theorem searchDomain_searchRel : searchDomain searchRel = SAT := by
  ext φ
  refine ⟨fun ⟨w, _, hw⟩ => ⟨_, hw⟩, fun hφ => ?_⟩
  obtain ⟨w, hw, hV⟩ := (isVerifier φ).1 hφ
  exact ⟨w, by simp [hw], hV⟩

/-- **Search to decision for `SAT`**: satisfying assignments are found in polynomial time exactly
when `SAT ∈ P`. -/
theorem searchRel_mem_FPSearch_iff : searchRel ∈ FPSearch encCNF ↔ SAT ∈ P encCNF := by
  refine ⟨fun h => searchDomain_searchRel ▸ searchDomain_mem_P h, fun h => ?_⟩
  obtain ⟨D, hD, hSAT⟩ := mem_P.mp h
  have hsearch : ComputableInPolyTime (search D) encCNF encBits :=
    (computableInPolyTime_search (D := fun _ => D) ((hD.comp (snd _ _)))
      (id'))
  refine mem_FPSearch.mpr
    ⟨searchRel_mem_FNP, fun φ => if D φ then some (search D φ) else none,
      (ite' (encC := encBool) hD ((optionSome encBits).comp hsearch) (const none)),
      fun φ => ⟨fun w hw => ?_, ?_⟩⟩
  · beta_reduce at hw
    split_ifs at hw with hDφ
    cases Option.some_injective _ hw
    exact ⟨(length_search D φ).trans_le (length_vars_le φ),
      verifier_search (fun ψ _ => (hSAT ψ).symm) ((hSAT φ).2 hDφ)⟩
  · intro hw
    beta_reduce at hw
    split_ifs at hw with hDφ
    rw [searchDomain_searchRel]
    exact fun hφ => hDφ ((hSAT φ).1 hφ)

end SAT

end Cslib.Complexity
