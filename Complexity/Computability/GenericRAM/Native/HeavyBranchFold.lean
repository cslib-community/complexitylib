/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.BooleanFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.PolyTime.CNF.SparsePolyCompile
public import Complexity.Foundations.BooleanAnalysis.SparseEquations
public import Complexity.Foundations.Data.List.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
import Mathlib.Order.Interval.Finset.Nat

/-!
# Heavy-variable branching and streaming common-zero accumulation

Implements the heavy-variable branching reduction and space-efficient streaming accumulator from
§5.5 (*Proof of Theorem 2.2*, pp. 38–39) of [OpenAI, *The Exponential Time Hypothesis is
False*][OpenAI2026ETH] over `SparsePolyCompile`, bridged to `SparseEquations` and `BooleanFold`.

## Main definitions

* `extendAssignment`, `rootCount`, `toFinsetEquation`, `heavyVarList`, `relabelFreeVar`,
  `freeVarEquiv`: common-zero count `N(P)`, heavy-variable filter, and dense `[n] \ S ≃ [n - |S|]`.
* `substituteEquation`, `relabelEquation`, `BranchOutcome`, `prepareBranch`, `branchRootCount`,
  `branchCountOracle`: simultaneous `(S, vals)` substitution, short-circuiting, and oracle dispatch.
* `BranchInput`, `encBranchInput`, `branchBody`, `streamBranches`, `countByBranching`,
  `branchCountCertificate`, `branchBodyCertificate`, `certificate`, `countCertificate`,
  `stepOverhead`: streaming `BooleanFold` combinator and native time/space certificates.

## Main results

* `rootCount_eq_commonZeroCount`, `toFinset_heavyVarList_eq_heavyVars`,
  `length_heavyVarList_le_div`, `prepareBranch_reduced_canonical`,
  `prepareBranch_reduced_degree_le`, `prepareBranch_reduced_length_le`,
  `prepareBranch_reduced_varDegree_le`, `length_enc_reduced_le`.
* `branchRootCount_prepareBranch`, `sum_branch_count_eq_rootCount`, `streamBranches_correct`,
  `countByBranching_eq_rootCount`, `runPrefix_sum_le_two_pow`, `computableInPolyTime_prepareBranch`,
  `streamBranches_computableInO`, `countByBranching_computableInO`, `polyBounded_branchWorkspace`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §5.5 (pp. 38–39)
-/

@[expose] public section
namespace Cslib.GenericRAM.HeavyBranchFold
open Cslib Cslib.BitString Cslib.Complexity Turing.MultiTapeTM

/-! ### 1. Common-Zero Counting, `SparseEquations` Bridges, and `heavyVarList` -/

/-- Extend a finite assignment `σ : BitString n` (`Fin n → Bool`) by `false` outside `[n]`. -/
def extendAssignment {n : ℕ} (σ : BitString n) (i : ℕ) : Bool :=
  if h : i < n then σ ⟨i, h⟩ else false
/-- Exact number of common zeros `N(P)` of `sys` over `BitString n` (`Fin n → Bool`). -/
def rootCount (n : ℕ) (sys : List (List (List ℕ))) : ℕ :=
  (Finset.univ.filter fun σ : BitString n => evalSystem sys (extendAssignment σ)).card
/-- Lift a sparse `𝔽₂` equation `eq : List (List ℕ)` to `Finset (Finset (Fin n))`. -/
def toFinsetEquation (n : ℕ) (eq : List (List ℕ)) : Finset (Finset (Fin n)) :=
  (eq.map fun m => Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ m).toFinset
/-- Sorted list of heavy variables `v < n` with `b₀ < varDegree v sys` (§5.5 of [OpenAI2026ETH]). -/
def heavyVarList (n b₀ : ℕ) (sys : List (List (List ℕ))) : List ℕ :=
  (List.range n).filter fun v => decide (b₀ < varDegree v sys)

@[simp] theorem evalMonomialList_contradiction (σ : ℕ → Bool) :
    evalMonomialList [[]] σ = true := rfl
@[simp] theorem evalSystem_nil (σ : ℕ → Bool) : evalSystem [] σ = true := rfl
@[simp] theorem extendAssignment_coe {n : ℕ} (σ : BitString n) (i : Fin n) :
    extendAssignment σ i = σ i := by simp only [extendAssignment, i.isLt, ↓reduceDIte, Fin.eta]
theorem rootCount_le_two_pow (n : ℕ) (sys : List (List (List ℕ))) : rootCount n sys ≤ 2 ^ n :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, BitString.card])

private theorem monomialSum_toFinsetEquation {n : ℕ} {eq : List (List ℕ)}
    (heq : IsCanonicalEquation eq) (hvars : ∀ m ∈ eq, ∀ v ∈ m, v < n) (σ : BitString n) :
    monomialSum (ZMod 2) (toFinsetEquation n eq) σ =
      bitVal (ZMod 2) (evalMonomialList eq (extendAssignment σ)) := by
  let f (m : List ℕ) : Finset (Fin n) := Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ m
  have hmem_of {m₁ m₂ : List ℕ} (hm₁ : m₁ ∈ eq) (hf : f m₁ = f m₂) {v : ℕ} (hv : v ∈ m₁) :
      v ∈ m₂ := by
    have h : (⟨v, hvars m₁ hm₁ v hv⟩ : Fin n) ∈ f m₂ :=
      hf ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    exact (Finset.mem_filter.mp h).2
  have hnd_f : (eq.map f).Nodup := heq.1.map_on fun m₁ hm₁ m₂ hm₂ hf =>
    (heq.2 m₁ hm₁).eq_of_toFinset_eq (heq.2 m₂ hm₂) (by
      ext v; simp only [List.mem_toFinset]; exact ⟨hmem_of hm₁ hf, hmem_of hm₂ hf.symm⟩)
  have hnd_s : (eq.map List.toFinset).Nodup :=
    heq.1.map_on fun m₁ hm₁ m₂ hm₂ h => (heq.2 m₁ hm₁).eq_of_toFinset_eq (heq.2 m₂ hm₂) h
  rw [monomialSum, toFinsetEquation, List.sum_toFinset _ hnd_f,
    bitVal_evalMonomialList_eq_sum_monomial heq, List.sum_toFinset _ hnd_s,
    List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun m hm => ?_)
  simp only [Function.comp_apply, monomial_apply]
  have hiff : (∀ i ∈ f m, σ i = true) ↔ (∀ v ∈ m.toFinset, extendAssignment σ v = true) :=
    ⟨fun h v hv => by
      have hvm := List.mem_toFinset.mp hv; have hvn := hvars m hm v hvm
      simpa only [extendAssignment, hvn, ↓reduceDIte] using
        h ⟨v, hvn⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvm⟩),
    fun h i hi => by
      have him := List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
      simpa only [extendAssignment_coe] using h i him⟩
  by_cases h : ∀ i ∈ f m, σ i = true
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.mpr h)]

/-- **Specification bridge to `SparseEquations.commonZeroCount`**: for any canonical sparse `𝔽₂`
system `sys` on `< n` variables, `rootCount n sys` agrees with `Cslib.BitString.commonZeroCount`. -/
theorem rootCount_eq_commonZeroCount {n : ℕ} {sys : List (List (List ℕ))}
    (hcan : ∀ eq ∈ sys, IsCanonicalEquation eq) (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) :
    rootCount n sys =
      commonZeroCount Finset.univ (fun i : Fin sys.length => toFinsetEquation n sys[i]) := by
  rw [rootCount, commonZeroCount]; congr 1; ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, evalSystem_eq_true_iff, IsCommonZero]
  refine ⟨fun h i _ => ?_, fun h eq heq => ?_⟩
  · rw [monomialSum_toFinsetEquation (hcan sys[i] (List.getElem_mem i.2))
      (hvars sys[i] (List.getElem_mem i.2)) σ, h sys[i] (List.getElem_mem i.2), bitVal_false]
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem heq
    have hz := (monomialSum_toFinsetEquation (hcan sys[k] heq) (hvars sys[k] heq) σ).symm.trans
      (h ⟨k, hk⟩ trivial)
    cases hb : evalMonomialList sys[k] (extendAssignment σ)
    · rfl
    · rw [hb, bitVal_true] at hz; exact absurd hz one_ne_zero

theorem pairwise_lt_heavyVarList (n b₀ : ℕ) (sys : List (List (List ℕ))) :
    (heavyVarList n b₀ sys).Pairwise (· < ·) := List.pairwise_lt_range.filter _
theorem nodup_heavyVarList (n b₀ : ℕ) (sys : List (List (List ℕ))) :
    (heavyVarList n b₀ sys).Nodup := (pairwise_lt_heavyVarList n b₀ sys).imp ne_of_lt
@[simp] theorem mem_heavyVarList_iff {n b₀ v : ℕ} {sys : List (List (List ℕ))} :
    v ∈ heavyVarList n b₀ sys ↔ v < n ∧ b₀ < varDegree v sys := by
  simp only [heavyVarList, List.mem_filter, List.mem_range, decide_eq_true_eq]
theorem lt_of_mem_heavyVarList {n b₀ v : ℕ} {sys : List (List (List ℕ))}
    (hv : v ∈ heavyVarList n b₀ sys) : v < n := (mem_heavyVarList_iff.mp hv).1
theorem varDegree_le_of_not_mem_heavyVarList {n b₀ u : ℕ} {sys : List (List (List ℕ))}
    (hun : u < n) (hu : u ∉ heavyVarList n b₀ sys) : varDegree u sys ≤ b₀ := by
  rw [mem_heavyVarList_iff, not_and, not_lt] at hu; exact hu hun

private theorem varIncidence_eq_varDegree (sys : List (List (List ℕ))) (v : ℕ) :
    varIncidence Finset.univ (fun i : Fin sys.length => (equationVars sys[i]).toFinset) v =
      varDegree v sys := by
  have hfil : ({i ∈ (List.finRange sys.length).toFinset | v ∈ (equationVars sys[i]).toFinset} :
      Finset (Fin sys.length)) =
      ((List.finRange sys.length).filter fun i => decide (v ∈ equationVars sys[i])).toFinset := by
    ext i; simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  rw [varIncidence, ← List.toFinset_finRange, hfil,
    List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _), ← List.countP_eq_length_filter,
    varDegree]
  conv_rhs => rw [← (List.ofFn_eq_map.symm.trans (List.ofFn_getElem (xs := sys))), List.countP_map]
  exact List.countP_congr fun i _ => by simp only [Function.comp_apply, Fin.getElem_fin]

/-- **Specification bridge to `SparseEquations.heavyVars`**: `heavyVarList n b₀ sys` enumerates
`Cslib.BitString.heavyVars` in strictly increasing order. -/
theorem toFinset_heavyVarList_eq_heavyVars (n b₀ : ℕ) (sys : List (List (List ℕ))) :
    (heavyVarList n b₀ sys).toFinset = heavyVars (Finset.range n) Finset.univ
      (fun i : Fin sys.length => (equationVars sys[i]).toFinset) b₀ := by
  ext v; simp only [List.mem_toFinset, mem_heavyVarList_iff, heavyVars, Finset.mem_filter,
    Finset.mem_range, varIncidence_eq_varDegree]

/-- **Markov heavy-variable bound (§5.5, p. 38)**: for `0 < b₀` and variables `< n`,
`(heavyVarList n b₀ sys).length ≤ (sys.map fun eq => (equationVars eq).length).sum / b₀`. -/
theorem length_heavyVarList_le_div {n b₀ : ℕ} {sys : List (List (List ℕ))}
    (hb₀ : 0 < b₀) (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) :
    (heavyVarList n b₀ sys).length ≤ (sys.map fun eq => (equationVars eq).length).sum / b₀ := by
  rw [← List.toFinset_card_of_nodup (nodup_heavyVarList n b₀ sys),
    toFinset_heavyVarList_eq_heavyVars]
  have hU : ∀ i ∈ (Finset.univ : Finset (Fin sys.length)),
      (equationVars sys[i]).toFinset ⊆ Finset.range n := fun i _ v hv => by
    obtain ⟨m, hm, hvm⟩ := mem_equationVars.mp (List.mem_toFinset.mp hv)
    exact Finset.mem_range.mpr (hvars sys[i] (List.getElem_mem i.2) m hm v hvm)
  refine (card_heavyVars_le_div _ _ _ hb₀ hU).trans (Nat.div_le_div_right (le_of_eq ?_))
  rw [totalIncidence, ← List.toFinset_finRange, List.sum_toFinset _ (List.nodup_finRange _)]
  conv_rhs => rw [← (List.ofFn_eq_map.symm.trans (List.ofFn_getElem (xs := sys))), List.map_map]
  exact congrArg List.sum (List.map_congr_left fun i _ => by simp only [Function.comp_apply,
    Fin.getElem_fin, equationVars, List.toFinset_card_of_nodup (nodup_sortDedup _)])

/-! ### 2. Order-Preserving Dense Free-Variable Relabeling -/

/-- Densely relabel a free variable `v : ℕ` outside `S` as `v - (S.filter (· < v)).length` (defined
totally for all `v : ℕ`, with natural subtraction truncated at `0` if `(S.filter (· < v)).length`
is at least `v`). -/
def relabelFreeVar (S : List ℕ) (v : ℕ) : ℕ := v - (S.filter (· < v)).length

/-- For `S.Nodup`, `relabelFreeVar S` is strictly increasing from `u ∉ S` to any larger `v`. -/
theorem relabelFreeVar_strictMono {S : List ℕ} (hS : S.Nodup) {u v : ℕ}
    (hu : u ∉ S) (huv : u < v) : relabelFreeVar S u < relabelFreeVar S v := by
  have hle_u := List.length_filter_lt_le hS u
  have hsub : (S.filter (· < v)).toFinset ⊆ (S.filter (· < u)).toFinset ∪ Finset.Ioo u v := by
    intro s hs; obtain ⟨hsS, hsv⟩ := List.mem_filter.mp (List.mem_toFinset.mp hs)
    rcases lt_or_gt_of_ne (fun h : s = u => hu (h ▸ hsS)) with hsu | hus
    · exact Finset.mem_union_left _
        (List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hsS, decide_eq_true hsu⟩))
    · exact Finset.mem_union_right _ (Finset.mem_Ioo.mpr ⟨hus, of_decide_eq_true hsv⟩)
  have hcard_v : (S.filter (· < v)).length ≤ (S.filter (· < u)).length + (v - u - 1) := by
    rw [← List.toFinset_card_of_nodup (hS.filter _), ← List.toFinset_card_of_nodup (hS.filter _)]
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by rw [Nat.card_Ioo]))
  simp only [relabelFreeVar]; omega

/-- For `S.Nodup` in `< n`, every free variable `u < n` outside `S` maps below `n - S.length`. -/
theorem relabelFreeVar_lt_sub {n : ℕ} {S : List ℕ} (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n)
    {u : ℕ} (hu : u ∉ S) (hun : u < n) : relabelFreeVar S u < n - S.length := by
  have hfil : S.filter (· < n) = S := List.filter_eq_self.mpr fun s hs => decide_eq_true (hSn s hs)
  simpa only [relabelFreeVar, hfil] using relabelFreeVar_strictMono hS hu hun

/-- For `S.Nodup`, `relabelFreeVar S` is injective on all variables outside `S`. -/
theorem relabelFreeVar_injOn {S : List ℕ} (hS : S.Nodup) {u v : ℕ}
    (hu : u ∉ S) (hv : v ∉ S) (heq : relabelFreeVar S u = relabelFreeVar S v) : u = v := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · exact absurd heq (ne_of_lt (relabelFreeVar_strictMono hS hu huv))
  · rfl
  · exact absurd heq.symm (ne_of_lt (relabelFreeVar_strictMono hS hv hvu))

private theorem card_freeVars {n : ℕ} {S : List ℕ} (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) :
    Fintype.card {i : Fin n // (i : ℕ) ∉ S} = n - S.length := by
  rw [Fintype.card_subtype_compl (fun i : Fin n => (i : ℕ) ∈ S), Fintype.card_fin,
    Fintype.card_subtype]
  have hmap : (Finset.univ.filter fun i : Fin n => (i : ℕ) ∈ S).map
      ⟨Fin.val, Fin.val_injective⟩ = S.toFinset := by
    ext x; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, List.mem_toFinset]
    exact ⟨fun ⟨i, hi, hix⟩ => hix ▸ hi, fun hx => ⟨⟨x, hSn x hx⟩, hx, rfl⟩⟩
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩, hmap, List.toFinset_card_of_nodup hS]

/-- Order-preserving bijection `[n] \ S ≃ Fin (n - S.length)` for `S.Nodup` in `< n`. -/
noncomputable def freeVarEquiv {n : ℕ} {S : List ℕ} (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) :
    {i : Fin n // (i : ℕ) ∉ S} ≃ Fin (n - S.length) :=
  Equiv.ofBijective
    (fun i => ⟨relabelFreeVar S i.1, relabelFreeVar_lt_sub hS hSn i.2 i.1.isLt⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun i j hij => Subtype.ext <| Fin.ext <|
        relabelFreeVar_injOn hS i.2 j.2 (congrArg Fin.val hij),
       by rw [card_freeVars hS hSn, Fintype.card_fin]⟩)

/-! ### 3. Multi-Variable Substitution, Canonicalization, and `prepareBranch` -/

/-- Substitute `(S, vals)` across `eq` and cancel duplicate monomials modulo `2` (looking up the
first index `S.idxOf v` if `S` has duplicates, defaulting missing entries `≥ vals.length` to
`false`, and ignoring trailing `vals` entries past `S.length`). -/
def substituteEquation (S : List ℕ) (vals : List Bool) (eq : List (List ℕ)) : List (List ℕ) :=
  reduceEquation
    ((eq.filter fun m => !m.any fun v => decide (v ∈ S) && !vals.getD (S.idxOf v) false).map
      fun m => m.filter fun v => decide (v ∉ S))

/-- Relabel all free variables in an equation using `relabelFreeVar S`. -/
def relabelEquation (S : List ℕ) (eq : List (List ℕ)) : List (List ℕ) :=
  eq.map fun m => m.map (relabelFreeVar S)

/-- Outcome of preparing a single heavy-variable branch `(S ↦ vals)` (§5.5 of [OpenAI2026ETH]). -/
inductive BranchOutcome where
  /-- Contradictory constant equation `1 = 0` (`[[]]`) appeared; `0` satisfying completions. -/
  | contradiction : BranchOutcome
  /-- All equations simplified to `0 = 0`; all `2 ^ freeVars` completions satisfy the system. -/
  | tautology (freeVars : ℕ) : BranchOutcome
  /-- Non-empty reduced system on `freeVars = n - |S|` densely relabeled free variables. -/
  | reduced (freeVars : ℕ) (sys : List (List (List ℕ))) : BranchOutcome
  deriving DecidableEq, Repr

/-- Structural option view of `BranchOutcome` for native encoding and option elimination. -/
def BranchOutcome.toOption : BranchOutcome → Option (ℕ × Option (List (List (List ℕ))))
  | .contradiction => none
  | .tautology n' => some (n', none)
  | .reduced n' sys' => some (n', some sys')

theorem BranchOutcome.toOption_injective : Function.Injective BranchOutcome.toOption := by
  rintro (_ | n₁ | ⟨n₁, s₁⟩) (_ | n₂ | ⟨n₂, s₂⟩) h <;> cases h <;> rfl

/-- Native binary encoding of `BranchOutcome` (`n'` in unary, `sys'` as framed nested lists). -/
@[irreducible] def encBranchOutcome : BranchOutcome ↪ List Bool :=
  (⟨BranchOutcome.toOption, BranchOutcome.toOption_injective⟩ : BranchOutcome ↪ _).trans
    (encOption (encPair encUnary (encOption (encList (encList (encList encNat))))))

private theorem encBranchOutcome_eq (o : BranchOutcome) : encBranchOutcome o =
    encOption (encPair encUnary (encOption (encList (encList (encList encNat))))) o.toOption := by
  unfold encBranchOutcome; rfl

/-- Restrict `sys` to `S ↦ vals`, drop `0 = 0` (`[]`), short-circuit `1 = 0` (`[[]]`) and empty
systems, or densely relabel `[n] \ S ≃ [n - S.length]` (truncated at `0` if `n < |S|`). -/
def prepareBranch (n : ℕ) (S : List ℕ) (vals : List Bool) (sys : List (List (List ℕ))) :
    BranchOutcome :=
  let nonZero := (sys.map (substituteEquation S vals)).filter fun eq => !eq.isEmpty
  if decide ([[]] ∈ nonZero) then .contradiction
  else if nonZero.isEmpty then .tautology (n - S.length)
  else .reduced (n - S.length) (nonZero.map (relabelEquation S))

theorem nodup_substituteEquation (S : List ℕ) (vals : List Bool) (eq : List (List ℕ)) :
    (substituteEquation S vals eq).Nodup := nodup_reduceEquation _
theorem length_substituteEquation_le (S : List ℕ) (vals : List Bool) (eq : List (List ℕ)) :
    (substituteEquation S vals eq).length ≤ eq.length :=
  (length_reduceEquation_le _).trans ((List.length_map _).trans_le (List.length_filter_le _ _))
theorem mem_substituteEquation_exists {S : List ℕ} {vals : List Bool} {eq : List (List ℕ)}
    {m' : List ℕ} (hm' : m' ∈ substituteEquation S vals eq) :
    ∃ m ∈ eq, m' = m.filter (fun v => decide (v ∉ S)) := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (mem_of_mem_reduceEquation hm')
  exact ⟨m, (List.mem_filter.mp hm).1, rfl⟩
theorem isCanonicalEquation_substituteEquation (S : List ℕ) (vals : List Bool)
    {eq : List (List ℕ)} (heq : IsCanonicalEquation eq) :
    IsCanonicalEquation (substituteEquation S vals eq) := by
  refine ⟨nodup_substituteEquation S vals eq, fun m' hm' => ?_⟩
  obtain ⟨m, hm, rfl⟩ := mem_substituteEquation_exists hm'; exact (heq.2 m hm).filter _

private theorem isCanonicalMonomial_relabel {S : List ℕ} (hS : S.Nodup) {m : List ℕ}
    (hm : IsCanonicalMonomial m) (hfree : ∀ u ∈ m, u ∉ S) :
    IsCanonicalMonomial (m.map (relabelFreeVar S)) := by
  unfold IsCanonicalMonomial at hm ⊢; induction m with
  | nil => exact List.Pairwise.nil
  | cons u ms ih =>
    rw [List.pairwise_cons] at hm
    simp only [List.map_cons, List.pairwise_cons, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    exact ⟨fun v hv => relabelFreeVar_strictMono hS (hfree u List.mem_cons_self) (hm.1 v hv),
      ih hm.2 fun v hv => hfree v (List.mem_cons_of_mem u hv)⟩

theorem isCanonicalEquation_relabelEquation {S : List ℕ} (hS : S.Nodup)
    {eq : List (List ℕ)} (heq : IsCanonicalEquation eq) (hfree : ∀ m ∈ eq, ∀ u ∈ m, u ∉ S) :
    IsCanonicalEquation (relabelEquation S eq) := by
  refine ⟨heq.1.map_on fun m₁ hm₁ m₂ hm₂ hmap =>
    List.ext_getElem (by simpa only [List.length_map] using congrArg List.length hmap)
      fun i h₁ h₂ => relabelFreeVar_injOn hS (hfree m₁ hm₁ _ (List.getElem_mem h₁))
        (hfree m₂ hm₂ _ (List.getElem_mem h₂)) (Option.some.inj <| by
          simpa only [List.getElem?_map, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂,
            Option.map_some] using congrArg (·[i]?) hmap), fun m'' hm'' => ?_⟩
  obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm''
  exact isCanonicalMonomial_relabel hS (heq.2 m' hm') (hfree m' hm')

theorem prepareBranch_freeVars_eq {n n' : ℕ} {S : List ℕ} {vals : List Bool}
    {sys : List (List (List ℕ))} :
    (prepareBranch n S vals sys = .tautology n' → n' = n - S.length) ∧
      (∀ sys', prepareBranch n S vals sys = .reduced n' sys' → n' = n - S.length) := by
  unfold prepareBranch; dsimp only; split_ifs <;> refine ⟨fun h => ?_, fun _ h => ?_⟩ <;>
    cases h <;> rfl

theorem prepareBranch_eq_reduced_iff {n n' : ℕ} {S : List ℕ} {vals : List Bool}
    {sys sys' : List (List (List ℕ))} :
    prepareBranch n S vals sys = .reduced n' sys' ↔
      let nonZero := (sys.map (substituteEquation S vals)).filter fun eq => !eq.isEmpty
      [[]] ∉ nonZero ∧ nonZero ≠ [] ∧ n' = n - S.length ∧
        sys' = nonZero.map (relabelEquation S) := by
  unfold prepareBranch; dsimp only; split_ifs with hc he
  · exact ⟨(fun h => by cases h), fun ⟨h1, _⟩ => absurd (of_decide_eq_true hc) h1⟩
  · exact ⟨(fun h => by cases h), fun ⟨_, h2, _⟩ => absurd (List.isEmpty_iff.mp he) h2⟩
  · exact ⟨fun h => by cases h; exact ⟨hc ∘ decide_eq_true, he ∘ List.isEmpty_iff.mpr, rfl, rfl⟩,
      fun ⟨_, _, hn, hs⟩ => by subst hn hs; rfl⟩

private theorem mem_reduced_exists {n n' : ℕ} {S : List ℕ} {vals : List Bool}
    {sys sys' : List (List (List ℕ))} (hred : prepareBranch n S vals sys = .reduced n' sys')
    {eq' : List (List ℕ)} (heq' : eq' ∈ sys') :
    ∃ eq₀ ∈ sys, substituteEquation S vals eq₀ ≠ [] ∧
      eq' = relabelEquation S (substituteEquation S vals eq₀) := by
  obtain ⟨_, _, _, rfl⟩ := prepareBranch_eq_reduced_iff.mp hred
  obtain ⟨eq₁, heq₁, rfl⟩ := List.mem_map.mp heq'
  obtain ⟨hmap, hne⟩ := List.mem_filter.mp heq₁
  obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp hmap
  exact ⟨eq₀, heq₀, (fun h => by rw [h] at hne; cases hne), rfl⟩

/-- For `S.Nodup` in `< n` and canonical `sys` on `< n`, any `.reduced n' sys'` branch has
`n' = n - S.length`, `sys' ≠ []`, `[] ∉ sys'`, `[[]] ∉ sys'`, and canonical `< n'` equations. -/
theorem prepareBranch_reduced_canonical {n : ℕ} {S : List ℕ} {vals : List Bool}
    {sys sys' : List (List (List ℕ))} {n' : ℕ}
    (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) (hcan : ∀ eq ∈ sys, IsCanonicalEquation eq)
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hred : prepareBranch n S vals sys = .reduced n' sys') :
    n' = n - S.length ∧ sys' ≠ [] ∧ [] ∉ sys' ∧ [[]] ∉ sys' ∧
      (∀ eq' ∈ sys', IsCanonicalEquation eq') ∧
      (∀ eq' ∈ sys', ∀ m' ∈ eq', ∀ v' ∈ m', v' < n') := by
  obtain ⟨hcontra, hne_nz, rfl, hsys'⟩ := prepareBranch_eq_reduced_iff.mp hred
  refine ⟨rfl, fun h => hne_nz (List.map_eq_nil_iff.mp (hsys'.symm.trans h)), ?_, ?_, ?_, ?_⟩
  · intro hmem; obtain ⟨_, _, hne, heq⟩ := mem_reduced_exists hred hmem
    exact hne (List.map_eq_nil_iff.mp heq.symm)
  · intro hmem; rw [hsys'] at hmem; obtain ⟨eq₁, heq₁, hmap⟩ := List.mem_map.mp hmem
    cases eq₁ with
    | nil => simp only [relabelEquation, List.map_nil, reduceCtorEq] at hmap
    | cons m₁ ms₁ =>
      simp only [relabelEquation, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at hmap
      exact hcontra (hmap.1 ▸ hmap.2 ▸ heq₁)
  · intro eq' heq'; obtain ⟨eq₀, heq₀, _, rfl⟩ := mem_reduced_exists hred heq'
    refine isCanonicalEquation_relabelEquation hS
      (isCanonicalEquation_substituteEquation S vals (hcan eq₀ heq₀)) fun m' hm' u hu => ?_
    obtain ⟨_, _, rfl⟩ := mem_substituteEquation_exists hm'
    exact of_decide_eq_true (List.mem_filter.mp hu).2
  · intro eq' heq' m' hm' v' hv'
    obtain ⟨eq₀, heq₀, _, rfl⟩ := mem_reduced_exists hred heq'
    obtain ⟨m₁, hm₁, rfl⟩ := List.mem_map.mp hm'; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv'
    obtain ⟨m₀, hm₀, rfl⟩ := mem_substituteEquation_exists hm₁
    obtain ⟨hum₀, huS⟩ := List.mem_filter.mp hu
    exact relabelFreeVar_lt_sub hS hSn (of_decide_eq_true huS) (hvars eq₀ heq₀ m₀ hm₀ u hum₀)

/-- Degree preservation: if `sys` has degree at most `k`, so does any reduced branch `sys'`. -/
theorem prepareBranch_reduced_degree_le {n k : ℕ} {S : List ℕ} {vals : List Bool}
    {sys sys' : List (List (List ℕ))} {n' : ℕ} (hdeg : ∀ eq ∈ sys, ∀ m ∈ eq, m.length ≤ k)
    (hred : prepareBranch n S vals sys = .reduced n' sys') :
    ∀ eq' ∈ sys', ∀ m' ∈ eq', m'.length ≤ k := by
  intro eq' heq' m' hm'; obtain ⟨eq₀, heq₀, _, rfl⟩ := mem_reduced_exists hred heq'
  obtain ⟨m₁, hm₁, rfl⟩ := List.mem_map.mp hm'; obtain ⟨m₀, hm₀, rfl⟩ :=
    mem_substituteEquation_exists hm₁
  rw [List.length_map]; exact (List.length_filter_le _ _).trans (hdeg eq₀ heq₀ m₀ hm₀)

/-- Monomial-count and scope-width preservation across `prepareBranch`. -/
theorem prepareBranch_reduced_length_le {n : ℕ} {S : List ℕ} {vals : List Bool}
    {sys sys' : List (List (List ℕ))} {n' : ℕ}
    (hred : prepareBranch n S vals sys = .reduced n' sys') :
    sys'.length ≤ sys.length ∧ ∀ eq' ∈ sys', ∃ eq ∈ sys,
      eq'.length ≤ eq.length ∧ (equationVars eq').length ≤ (equationVars eq).length := by
  refine ⟨?_, fun eq' heq' => ?_⟩
  · obtain ⟨_, _, _, rfl⟩ := prepareBranch_eq_reduced_iff.mp hred
    rw [List.length_map]; exact (List.length_filter_le _ _).trans (by rw [List.length_map])
  · obtain ⟨eq₀, heq₀, _, rfl⟩ := mem_reduced_exists hred heq'
    have hlen : (relabelEquation S (substituteEquation S vals eq₀)).length ≤ eq₀.length := by
      rw [relabelEquation, List.length_map]; exact length_substituteEquation_le _ _ _
    refine ⟨eq₀, heq₀, hlen, ?_⟩
    rw [equationVars, equationVars, ← List.toFinset_card_of_nodup (nodup_sortDedup _),
      ← List.toFinset_card_of_nodup (nodup_sortDedup _), toFinset_sortDedup, toFinset_sortDedup]
    have hsub : ((relabelEquation S (substituteEquation S vals eq₀)).flatten).toFinset ⊆
        (eq₀.flatten.filter fun u => decide (u ∉ S)).toFinset.image (relabelFreeVar S) := by
      intro v' hv'
      obtain ⟨m'', hm'', hv''⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hv')
      obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm''
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv''
      obtain ⟨m₀, hm₀, rfl⟩ := mem_substituteEquation_exists hm'
      obtain ⟨hum₀, huS⟩ := List.mem_filter.mp hu
      exact Finset.mem_image.mpr ⟨u, List.mem_toFinset.mpr
        (List.mem_filter.mpr ⟨List.mem_flatten.mpr ⟨m₀, hm₀, hum₀⟩, huS⟩), rfl⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
      (Finset.card_le_card fun u hu => List.mem_toFinset.mpr
        (List.mem_filter.mp (List.mem_toFinset.mp hu)).1))

/-- Per-variable incidence preservation: for `S.Nodup` and `u ∉ S`, `varDegree (relabelFreeVar S u)`
on any `.reduced` branch `sys'` never exceeds `varDegree u sys`. -/
theorem varDegree_relabelFreeVar_le {n : ℕ} {S : List ℕ} {vals : List Bool}
    {sys sys' : List (List (List ℕ))} {n' : ℕ} (hS : S.Nodup) {u : ℕ} (hu : u ∉ S)
    (hred : prepareBranch n S vals sys = .reduced n' sys') :
    varDegree (relabelFreeVar S u) sys' ≤ varDegree u sys := by
  obtain ⟨_, _, _, rfl⟩ := prepareBranch_eq_reduced_iff.mp hred
  simp only [varDegree, List.countP_map]
  refine List.filter_sublist.countP_le.trans ?_
  rw [List.countP_map]; apply List.countP_mono_left; intro eq₀ _ hmem
  simp only [Function.comp_apply, decide_eq_true_eq, mem_equationVars] at hmem ⊢
  obtain ⟨m'', hm'', hu'⟩ := hmem
  obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm''
  obtain ⟨w, hw, hrel⟩ := List.mem_map.mp hu'
  obtain ⟨m₀, hm₀, rfl⟩ := mem_substituteEquation_exists hm'
  obtain ⟨hwm₀, hwS⟩ := List.mem_filter.mp hw
  exact ⟨m₀, hm₀, (relabelFreeVar_injOn hS (of_decide_eq_true hwS) hu hrel) ▸ hwm₀⟩

/-- Uniform free-variable incidence preservation (§5.5 of [OpenAI2026ETH]): for `S.Nodup` in `< n`,
if every `u < n` outside `S` has `varDegree u sys ≤ b₀`, every `u' < n'` in `sys'` has `≤ b₀`. -/
theorem prepareBranch_reduced_varDegree_le {n b₀ : ℕ} {S : List ℕ} {vals : List Bool}
    {sys sys' : List (List (List ℕ))} {n' : ℕ}
    (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) (hinc : ∀ u < n, u ∉ S → varDegree u sys ≤ b₀)
    (hred : prepareBranch n S vals sys = .reduced n' sys') :
    ∀ u' < n', varDegree u' sys' ≤ b₀ := by
  have hn' := prepareBranch_freeVars_eq.2 sys' hred; subst hn'
  intro u' hu'; let i := (freeVarEquiv hS hSn).symm ⟨u', hu'⟩
  have hrel : relabelFreeVar S i.1 = u' :=
    congrArg Fin.val ((freeVarEquiv hS hSn).apply_symm_apply ⟨u', hu'⟩)
  rw [← hrel]; exact (varDegree_relabelFreeVar_le hS i.2 hred).trans (hinc i.1 i.1.isLt i.2)

/-! ### 4. Exact Common-Zero Count Preservation -/

/-- Exact common-zero count represented by a `BranchOutcome`. -/
def branchRootCount : BranchOutcome → ℕ
  | .contradiction => 0
  | .tautology n' => 2 ^ n'
  | .reduced n' sys' => rootCount n' sys'

/-- Dispatch a `BranchOutcome` to an external counting oracle `solver` on `.reduced` branches. -/
def branchCountOracle (solver : ℕ → List (List (List ℕ)) → ℕ) : BranchOutcome → ℕ
  | .contradiction => 0
  | .tautology n' => 2 ^ n'
  | .reduced n' sys' => solver n' sys'

@[simp] theorem branchCountOracle_rootCount : branchCountOracle rootCount = branchRootCount := by
  funext o; cases o <;> rfl

private theorem evalMonomialList_substituteEquation {S : List ℕ} {vals : List Bool} {σ : ℕ → Bool}
    (hagree : ∀ v ∈ S, vals.getD (S.idxOf v) false = σ v) (eq : List (List ℕ)) :
    evalMonomialList (substituteEquation S vals eq) σ = evalMonomialList eq σ := by
  rw [substituteEquation, evalMonomialList_reduceEquation]
  induction eq with
  | nil => rfl
  | cons m ms ih =>
    rw [List.filter_cons, evalMonomialList_cons]
    split_ifs with hkeep
    · simp only [Bool.not_eq_true', List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq,
        not_and, Bool.not_eq_false] at hkeep
      rw [List.map_cons, evalMonomialList_cons, ih]
      congr 1; rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      refine ⟨fun h v hvm => ?_, fun h v hv => h v (List.mem_filter.mp hv).1⟩
      by_cases hvS : v ∈ S
      · exact (hagree v hvS).symm.trans (hkeep v hvm hvS)
      · exact h v (List.mem_filter.mpr ⟨hvm, decide_eq_true hvS⟩)
    · have hany := by simpa only [Bool.not_eq_true', Bool.not_eq_false] using hkeep
      obtain ⟨v, hvm, hv⟩ := List.any_eq_true.mp hany
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hv
      have hall : m.all σ = false := Bool.eq_false_iff.mpr fun h =>
        Bool.false_ne_true (((hagree v hv.1).symm.trans hv.2).symm.trans
          (List.all_eq_true.mp h v hvm))
      rw [hall, Bool.false_xor, ih]

private theorem evalMonomialList_relabelEquation {S : List ℕ} {σ τ : ℕ → Bool} {eq : List (List ℕ)}
    (hrel : ∀ m ∈ eq, ∀ u ∈ m, τ (relabelFreeVar S u) = σ u) :
    evalMonomialList (relabelEquation S eq) τ = evalMonomialList eq σ := by
  induction eq with
  | nil => rfl
  | cons m ms ih =>
    simp only [relabelEquation, List.map_cons, evalMonomialList_cons, List.all_map]
    have hm : m.all (τ ∘ relabelFreeVar S) = m.all σ := by
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      exact ⟨fun h u hu => (hrel m List.mem_cons_self u hu).symm.trans (h u hu),
        fun h u hu => (hrel m List.mem_cons_self u hu).trans (h u hu)⟩
    rw [hm, ← relabelEquation, ih fun m' hm' u hu => hrel m' (List.mem_cons_of_mem m hm') u hu]

private noncomputable def mergeAssignment {n : ℕ} {S : List ℕ}
    (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) (vals : List Bool)
    (τ : BitString (n - S.length)) : BitString n :=
  fun i => if hiS : (i : ℕ) ∈ S then vals.getD (S.idxOf (i : ℕ)) false
    else τ (freeVarEquiv hS hSn ⟨i, hiS⟩)

private theorem map_extend_mergeAssignment {n : ℕ} {S : List ℕ}
    (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) {vals : List Bool} (hvals : vals.length = S.length)
    (τ : BitString (n - S.length)) :
    S.map (extendAssignment (mergeAssignment hS hSn vals τ)) = vals := by
  apply List.ext_getElem (by rw [List.length_map, hvals]); intro k hk₁ hk₂
  rw [List.length_map] at hk₁
  have hs_mem : S[k] ∈ S := List.getElem_mem hk₁
  have hs_lt : S[k] < n := hSn S[k] hs_mem
  have hidx : S.idxOf S[k] = k := List.Nodup.idxOf_getElem hS k hk₁
  simp only [List.getElem_map, extendAssignment, hs_lt, ↓reduceDIte, mergeAssignment, hs_mem,
    hidx, List.getD_eq_getElem vals false hk₂]

private noncomputable def fiberEquiv {n : ℕ} {S : List ℕ} {vals : List Bool}
    (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) (hvals : vals.length = S.length) :
    BitString (n - S.length) ≃ {σ : BitString n // S.map (extendAssignment σ) = vals} where
  toFun τ := ⟨mergeAssignment hS hSn vals τ, map_extend_mergeAssignment hS hSn hvals τ⟩
  invFun σ := fun j => σ.1 ((freeVarEquiv hS hSn).symm j).1
  left_inv τ := by
    funext j; let u := (freeVarEquiv hS hSn).symm j
    simp only [mergeAssignment, u.2, ↓reduceDIte, Subtype.eta, Equiv.apply_symm_apply, u]
  right_inv := fun ⟨σ, hσ⟩ => by
    apply Subtype.ext; funext i; simp only [mergeAssignment]; split_ifs with hiS
    · have hk : S.idxOf (i : ℕ) < S.length := List.idxOf_lt_length_of_mem hiS
      rw [← hσ, List.getD_eq_getElem _ false (by rw [List.length_map]; exact hk)]
      simp only [List.getElem_map, List.getElem_idxOf hk, extendAssignment_coe]
    · simp only [Equiv.symm_apply_apply]

private theorem evalSystem_mergeAssignment {n : ℕ} {S : List ℕ} {vals : List Bool}
    {sys : List (List (List ℕ))} (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n)
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) (τ : BitString (n - S.length)) :
    let nonZero := (sys.map (substituteEquation S vals)).filter fun eq => !eq.isEmpty
    evalSystem sys (extendAssignment (mergeAssignment hS hSn vals τ)) =
      if decide ([[]] ∈ nonZero) then false
      else if nonZero.isEmpty then true
      else evalSystem (nonZero.map (relabelEquation S)) (extendAssignment τ) := by
  intro nonZero; set σ := extendAssignment (mergeAssignment hS hSn vals τ)
  have hagree : ∀ v ∈ S, vals.getD (S.idxOf v) false = σ v := fun v hv => by
    have hvn : v < n := hSn v hv
    simp only [σ, extendAssignment, hvn, ↓reduceDIte, mergeAssignment, hv]
  have hsys_eq : evalSystem sys σ = evalSystem nonZero σ := by
    rw [Bool.eq_iff_iff, evalSystem_eq_true_iff, evalSystem_eq_true_iff]
    refine ⟨fun h eq₁ heq₁ => ?_, fun h eq₀ heq₀ => ?_⟩
    · obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp (List.mem_filter.mp heq₁).1
      exact (evalMonomialList_substituteEquation hagree eq₀).trans (h eq₀ heq₀)
    · rw [← evalMonomialList_substituteEquation hagree eq₀]
      by_cases hemp : (substituteEquation S vals eq₀).isEmpty
      · rw [List.isEmpty_iff.mp hemp, evalMonomialList_nil]
      · exact h _ (List.mem_filter.mpr
          ⟨List.mem_map_of_mem heq₀, by simp only [hemp, Bool.not_false]⟩)
  rw [hsys_eq]; split_ifs with hcontra hempty
  · rw [decide_eq_true_iff] at hcontra
    exact Bool.eq_false_iff.mpr fun ht =>
      Bool.false_ne_true (((evalSystem_eq_true_iff _ _).mp ht [[]] hcontra).symm.trans
        (evalMonomialList_contradiction σ))
  · rw [List.isEmpty_iff.mp hempty, evalSystem_nil]
  · rw [Bool.eq_iff_iff, evalSystem_eq_true_iff, evalSystem_eq_true_iff]
    have heq_rel : ∀ eq₁ ∈ nonZero,
        evalMonomialList (relabelEquation S eq₁) (extendAssignment τ) = evalMonomialList eq₁ σ := by
      intro eq₁ heq₁; obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp (List.mem_filter.mp heq₁).1
      apply evalMonomialList_relabelEquation; intro m' hm' u hu
      obtain ⟨m₀, hm₀, rfl⟩ := mem_substituteEquation_exists hm'
      obtain ⟨hum₀, huS_dec⟩ := List.mem_filter.mp hu
      have huS : u ∉ S := of_decide_eq_true huS_dec
      have hun : u < n := hvars eq₀ heq₀ m₀ hm₀ u hum₀
      have hrel_lt : relabelFreeVar S u < n - S.length := relabelFreeVar_lt_sub hS hSn huS hun
      simp only [extendAssignment, hrel_lt, ↓reduceDIte, σ, hun, mergeAssignment, huS]; rfl
    exact ⟨fun h eq' heq' => by
        obtain ⟨eq₁, heq₁, rfl⟩ := List.mem_map.mp heq'
        exact (heq_rel eq₁ heq₁).trans (h eq₁ heq₁),
      fun h eq₁ heq₁ => (heq_rel eq₁ heq₁).symm.trans (h _ (List.mem_map_of_mem heq₁))⟩

/-- Single-branch exactness: for `S.Nodup` in `< n`, `sys` on `< n`, and `vals.length = S.length`,
`branchRootCount (prepareBranch n S vals sys)` counts common zeros extending `(S, vals)`. -/
theorem branchRootCount_prepareBranch {n : ℕ} {S : List ℕ} {vals : List Bool}
    {sys : List (List (List ℕ))} (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n)
    (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n) (hvals : vals.length = S.length) :
    branchRootCount (prepareBranch n S vals sys) =
      (Finset.univ.filter fun σ : BitString n =>
        S.map (extendAssignment σ) = vals ∧ evalSystem sys (extendAssignment σ) = true).card := by
  have hbij : (Finset.univ.filter fun σ : BitString n =>
        S.map (extendAssignment σ) = vals ∧ evalSystem sys (extendAssignment σ) = true).card =
      (Finset.univ.filter fun τ : BitString (n - S.length) =>
        evalSystem sys (extendAssignment (mergeAssignment hS hSn vals τ)) = true).card := by
    symm; refine Finset.card_bij (fun τ _ => (fiberEquiv hS hSn hvals τ).1) ?_ ?_ ?_
    · intro τ hτ; rw [Finset.mem_filter] at hτ ⊢
      exact ⟨Finset.mem_univ _, (fiberEquiv hS hSn hvals τ).2, hτ.2⟩
    · exact fun _ _ _ _ h => (fiberEquiv hS hSn hvals).injective (Subtype.ext h)
    · intro σ hσ; rw [Finset.mem_filter] at hσ
      let τ := (fiberEquiv hS hSn hvals).symm ⟨σ, hσ.2.1⟩
      have hτ : (fiberEquiv hS hSn hvals τ).1 = σ :=
        congrArg Subtype.val ((fiberEquiv hS hSn hvals).apply_symm_apply ⟨σ, hσ.2.1⟩)
      refine ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hτ⟩
      change evalSystem sys (extendAssignment (fiberEquiv hS hSn hvals τ).1) = true
      rw [hτ]; exact hσ.2.2
  rw [hbij]
  have heval := fun τ => evalSystem_mergeAssignment (vals := vals) hS hSn hvars τ
  simp only [heval]; unfold prepareBranch; dsimp only; split_ifs
  · simp only [branchRootCount, Finset.filter_false, Finset.card_empty]
  · simp only [branchRootCount, Finset.filter_true_of_mem, implies_true, Finset.card_univ]
    exact BitString.card.symm
  · rfl

/-- **Exponential-branching decomposition identity**: for `S.Nodup` in `< n` and `sys` on `< n`,
summing `branchCountOracle solver` over `0 ≤ idx < 2 ^ S.length` via `lowBits S.length idx` equals
`rootCount n sys` whenever `solver` is exact on `.reduced` branches. -/
theorem sum_branch_count_eq_rootCount
    {n : ℕ} {S : List ℕ} {sys : List (List (List ℕ))} {solver : ℕ → List (List (List ℕ)) → ℕ}
    (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hsolver : ∀ vals, vals.length = S.length → ∀ n' sys',
      prepareBranch n S vals sys = .reduced n' sys' → solver n' sys' = rootCount n' sys') :
    ((List.range (2 ^ S.length)).map fun idx =>
      branchCountOracle solver (prepareBranch n S (lowBits S.length idx) sys)).sum =
      rootCount n sys := by
  have hmap : ((List.range (2 ^ S.length)).map fun idx =>
      branchCountOracle solver (prepareBranch n S (lowBits S.length idx) sys)) =
      (enumList S.length).map fun vals =>
        branchCountOracle solver (prepareBranch n S vals sys) := by
    rw [← BooleanFold.decoded_range_eq_enumList, List.map_map]; rfl
  have horacle : ∀ vals ∈ enumList S.length,
      branchCountOracle solver (prepareBranch n S vals sys) =
        branchRootCount (prepareBranch n S vals sys) := fun vals hvals => by
    cases hout : prepareBranch n S vals sys with
    | contradiction | tautology _ => rfl
    | reduced n' sys' => exact hsolver vals (BitString.length_of_mem_enumList hvals) n' sys' hout
  have hnd : (enumList S.length).Nodup := (BitString.nodup_enum S.length).map List.ofFn_injective
  rw [hmap, List.map_congr_left horacle, ← List.sum_toFinset _ hnd]
  let roots := Finset.univ.filter fun σ : BitString n => evalSystem sys (extendAssignment σ) = true
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := roots) (t := (enumList S.length).toFinset)
    (f := fun σ : BitString n => S.map (extendAssignment σ))
    (fun σ _ => List.mem_toFinset.mpr (BitString.mem_enumList.mpr (List.length_map _)))
  rw [rootCount, hpart]; refine Finset.sum_congr rfl fun vals hvals => ?_
  rw [branchRootCount_prepareBranch hS hSn hvars
    (BitString.length_of_mem_enumList (List.mem_toFinset.mp hvals))]
  congr 1; ext σ; simp only [roots, Finset.mem_filter, Finset.mem_univ, true_and, and_comm]

/-! ### 5. Plain Polynomial-Time Certificates for `heavyVarList` and `prepareBranch` -/

private theorem length_enc_substituteEquation_le (S : List ℕ) (vals : List Bool)
    (eq : List (List ℕ)) :
    (encList (encList encNat) (substituteEquation S vals eq)).length ≤
      (encList (encList encNat) eq).length :=
  (length_enc_reduceEquation_le _).trans
    ((length_encList_map_le _ _ fun _ _ => length_encList_sublist encNat List.filter_sublist).trans
      (length_encList_sublist _ List.filter_sublist))

/-- Computing `heavyVarList n b₀ sys` (`n` in unary, `b₀` in binary) is polynomial-time. -/
theorem computableInPolyTime_heavyVarList :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × List (List (List ℕ)) => heavyVarList p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encNat) (encList (encList (encList encNat))))
      (encList encNat) := by
  let encSys := encList (encList (encList encNat))
  have hrange : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List (List (List ℕ)) => (List.range p.1.1).map fun v => v)
      (encPair (encPair encUnary encNat) encSys) (encList encNat) :=
    (ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp
      (ComputableInPolyTime.range.comp ((ComputableInPolyTime.fst _ _).fst'))
  have hpred : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × List (List (List ℕ))) × ℕ => decide (q.1.1.2 < varDegree q.2 q.1.2))
      (encPair (encPair (encPair encUnary encNat) encSys) encNat) encBool :=
    ComputableInPolyTime.binary_lt' ((ComputableInPolyTime.fst _ _).fst'.snd')
      (ComputableInPolyTime.unary_to_binary.comp (computableInPolyTime_varDegree.comp
        ((ComputableInPolyTime.snd _ _).prod ((ComputableInPolyTime.fst _ _).snd'))))
  exact (ComputableInPolyTime.filterWithInput
    (test := fun x v => decide (x.1.2 < varDegree v x.2)) hrange hpred).of_enc_eq
      fun _ => congrArg (encList encNat) (by rw [List.map_id']; rfl)

@[fun_prop] theorem computableInPolyTime_heavyVarList_comp {α : Type} {encIn : α ↪ List Bool}
    {fn fb : α → ℕ} {fsys : α → List (List (List ℕ))}
    (hn : ComputableInPolyTime fn encIn encUnary) (hb : ComputableInPolyTime fb encIn encNat)
    (hsys : ComputableInPolyTime fsys encIn (encList (encList (encList encNat)))) :
    ComputableInPolyTime (fun a => heavyVarList (fn a) (fb a) (fsys a)) encIn (encList encNat) :=
  computableInPolyTime_heavyVarList.comp ((hn.prod hb).prod hsys)

/-- `relabelFreeVar` is computable in polynomial time. -/
theorem computableInPolyTime_relabelFreeVar :
    ComputableInPolyTime (fun p : List ℕ × ℕ => relabelFreeVar p.1 p.2)
      (encPair (encList encNat) encNat) encNat := by
  have hfil : ComputableInPolyTime (fun p : List ℕ × ℕ => (p.1.filter (· < p.2)).length)
      (encPair (encList encNat) encNat) encUnary := by fun_prop
  exact ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.unary_to_binary.comp hfil)

@[fun_prop] theorem computableInPolyTime_relabelFreeVar_comp {α : Type} {encIn : α ↪ List Bool}
    {S : α → List ℕ} {v : α → ℕ} (hS : ComputableInPolyTime S encIn (encList encNat))
    (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun a => relabelFreeVar (S a) (v a)) encIn encNat :=
  computableInPolyTime_relabelFreeVar.comp (hS.prod hv)

/-- `relabelEquation` is computable in polynomial time. -/
theorem computableInPolyTime_relabelEquation :
    ComputableInPolyTime (fun p : List ℕ × List (List ℕ) => relabelEquation p.1 p.2)
      (encPair (encList encNat) (encList (encList encNat))) (encList (encList encNat)) := by
  unfold relabelEquation
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  apply ComputableInPolyTime.mapWithInput (by fun_prop)
  exact computableInPolyTime_relabelFreeVar.comp
    ((ComputableInPolyTime.fst _ _).fst'.fst'.prod (ComputableInPolyTime.snd _ _))

@[fun_prop] theorem computableInPolyTime_relabelEquation_comp {α : Type} {encIn : α ↪ List Bool}
    {S : α → List ℕ} {eq : α → List (List ℕ)} (hS : ComputableInPolyTime S encIn (encList encNat))
    (heq : ComputableInPolyTime eq encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun a => relabelEquation (S a) (eq a)) encIn (encList (encList encNat)) :=
  computableInPolyTime_relabelEquation.comp (hS.prod heq)

/-- `substituteEquation` is computable in polynomial time. -/
theorem computableInPolyTime_substituteEquation :
    ComputableInPolyTime
      (fun p : List ℕ × (List Bool × List (List ℕ)) => substituteEquation p.1 p.2.1 p.2.2)
      (encPair (encList encNat) (encPair encBits (encList (encList encNat))))
      (encList (encList encNat)) := by
  let encEq := encList (encList encNat)
  have hraw : ComputableInPolyTime
      (fun p : List ℕ × (List Bool × List (List ℕ)) =>
        ((p.2.2.filter fun m => !m.any fun v => decide (v ∈ p.1) && !p.2.1.getD (p.1.idxOf v) false)
          |>.map fun m => m.filter fun v => decide (v ∉ p.1)))
      (encPair (encList encNat) (encPair encBits encEq)) encEq := by fun_prop
  simpa only [Function.comp_def, substituteEquation] using
    computableInPolyTime_reduceEquation.comp hraw

@[fun_prop] theorem computableInPolyTime_substituteEquation_comp {α : Type} {encIn : α ↪ List Bool}
    {S : α → List ℕ} {vals : α → List Bool} {eq : α → List (List ℕ)}
    (hS : ComputableInPolyTime S encIn (encList encNat))
    (hvals : ComputableInPolyTime vals encIn encBits)
    (heq : ComputableInPolyTime eq encIn (encList (encList encNat))) :
    ComputableInPolyTime (fun a => substituteEquation (S a) (vals a) (eq a))
      encIn (encList (encList encNat)) :=
  computableInPolyTime_substituteEquation.comp (hS.prod (hvals.prod heq))

/-- `prepareBranch` is computable in polynomial time. -/
theorem computableInPolyTime_prepareBranch :
    ComputableInPolyTime
      (fun p : ℕ × List ℕ × List Bool × List (List (List ℕ)) =>
        prepareBranch p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair (encList encNat)
        (encPair encBits (encList (encList (encList encNat)))))) encBranchOutcome := by
  let P := ℕ × List ℕ × List Bool × List (List (List ℕ))
  let encEq := encList (encList encNat); let encSys := encList encEq
  let encOptSys := encOption encSys; let encInner := encPair encUnary encOptSys
  let encOut := encOption encInner
  let encIn := encPair encUnary (encPair (encList encNat) (encPair encBits encSys))
  let nz (p : P) := (p.2.2.2.map (substituteEquation p.2.1 p.2.2.1)).filter fun eq => !eq.isEmpty
  have hnonZero : ComputableInPolyTime nz encIn encSys :=
    ComputableInPolyTime.filterWithInput
      (ComputableInPolyTime.mapWithInput (by fun_prop)
        (computableInPolyTime_substituteEquation.comp
          ((ComputableInPolyTime.fst _ _).snd'.fst'.prod
            ((ComputableInPolyTime.fst _ _).snd'.snd'.fst'.prod
              (ComputableInPolyTime.snd _ _))))) (by fun_prop)
  have hrelMap : ComputableInPolyTime (fun p : P => (nz p).map (relabelEquation p.2.1))
      encIn encSys :=
    ComputableInPolyTime.mapWithInput hnonZero
      (computableInPolyTime_relabelEquation.comp
        ((ComputableInPolyTime.fst _ _).snd'.fst'.prod (ComputableInPolyTime.snd _ _)))
  have hn' : ComputableInPolyTime (fun p : P => p.1 - p.2.1.length) encIn encUnary := by
    fun_prop
  have hc1 := ComputableInPolyTime.decide_mem hnonZero (ComputableInPolyTime.const [[]])
  have hc2 := (by fun_prop : ComputableInPolyTime (List.isEmpty (α := List (List ℕ))) encSys
    encBool).comp hnonZero
  have hb1 := (ComputableInPolyTime.optionSome encInner).comp
    (hn'.prod (ComputableInPolyTime.const (encOut := encOptSys) none))
  have hb2 := (ComputableInPolyTime.optionSome encInner).comp
    (hn'.prod ((ComputableInPolyTime.optionSome encSys).comp hrelMap))
  have hopt :=
    hc1.ite' (ComputableInPolyTime.const (encOut := encOut) none) (hc2.ite' hb1 hb2)
  have hfun (p : P) :
      (if decide ([[]] ∈ nz p) then none
        else if (nz p).isEmpty then some (p.1 - p.2.1.length, none)
        else some (p.1 - p.2.1.length, some ((nz p).map (relabelEquation p.2.1)))) =
        (prepareBranch p.1 p.2.1 p.2.2.1 p.2.2.2).toOption := by
    dsimp only [nz, prepareBranch, BranchOutcome.toOption]; split_ifs <;> rfl
  exact hopt.of_enc_eq fun p => (encBranchOutcome_eq _).trans
    (congrArg encOut (by rw [← hfun p]; rfl))

@[fun_prop] theorem computableInPolyTime_prepareBranch_comp {α : Type} {encIn : α ↪ List Bool}
    {n : α → ℕ} {S : α → List ℕ} {vals : α → List Bool} {sys : α → List (List (List ℕ))}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hS : ComputableInPolyTime S encIn (encList encNat))
    (hvals : ComputableInPolyTime vals encIn encBits)
    (hsys : ComputableInPolyTime sys encIn (encList (encList (encList encNat)))) :
    ComputableInPolyTime (fun a => prepareBranch (n a) (S a) (vals a) (sys a))
      encIn encBranchOutcome := by
  simpa only [Function.comp_def] using
    computableInPolyTime_prepareBranch.comp (hn.prod (hS.prod (hvals.prod hsys)))

/-! ### 6. Space-Efficient Streaming `BooleanFold` Combinator -/

/-- Input tuple `(n, S, sys)` for streaming heavy-variable branching. -/
abbrev BranchInput : Type := ℕ × List ℕ × List (List (List ℕ))
instance : DecidableEq BranchInput := inferInstance
/-- Native encoding of `BranchInput` (`n` in unary, `S` and `sys` as framed lists). -/
def encBranchInput : BranchInput ↪ List Bool :=
  encPair encUnary (encPair (encList encNat) (encList (encList (encList encNat))))

/-- Encoded-size non-expansion: every `.reduced n' sys'` branch produced by `prepareBranch` has
encoded solver input `(n', sys')` no longer than the parent `encBranchInput (n, S, sys)`. -/
theorem length_enc_reduced_le {n n' : ℕ} {S : List ℕ} {vals : List Bool}
    {sys sys' : List (List (List ℕ))} (hred : prepareBranch n S vals sys = .reduced n' sys') :
    (encPair encUnary (encList (encList (encList encNat))) (n', sys')).length ≤
      (encBranchInput (n, S, sys)).length := by
  obtain ⟨_, _, rfl, rfl⟩ := prepareBranch_eq_reduced_iff.mp hred
  have hrel : ∀ eq₁ : List (List ℕ), (encList (encList encNat) (relabelEquation S eq₁)).length ≤
      (encList (encList encNat) eq₁).length := fun eq₁ =>
    length_encList_map_le (encList encNat) (encList encNat) fun m _ =>
      length_encList_map_le encNat encNat fun v _ => by
        simpa [Nat.size_eq_bits_len, relabelFreeVar] using Nat.size_le_size (Nat.sub_le v _)
  have hsys : (encList (encList (encList encNat))
      (((sys.map (substituteEquation S vals)).filter fun eq => !eq.isEmpty).map
        (relabelEquation S))).length ≤ (encList (encList (encList encNat)) sys).length :=
    (length_encList_map_le _ _ fun eq₁ _ => hrel eq₁).trans
      ((length_encList_sublist _ List.filter_sublist).trans
        (length_encList_map_le _ _ fun eq₀ _ => length_enc_substituteEquation_le S vals eq₀))
  simp only [encBranchInput, length_encPair, encUnary_apply, List.length_replicate]; omega

/-- Single streaming step of heavy-variable branching. -/
def branchBody (solver : ℕ → List (List (List ℕ)) → ℕ)
    (p : (ℕ × List Bool) × (BranchInput × ℕ)) : BranchInput × ℕ :=
  (p.2.1, p.2.2 + branchCountOracle solver (prepareBranch p.2.1.1 p.2.1.2.1 p.1.2 p.2.1.2.2))
/-- Stream all `2 ^ |S|` heavy-variable assignments via `BooleanFold.run` without materializing the
assignment list, returning `(finalIdx, (|S|, (inp, totalCount)))`. -/
def streamBranches (solver : ℕ → List (List (List ℕ)) → ℕ) (inp : BranchInput) :
    ℕ × (ℕ × (BranchInput × ℕ)) :=
  BooleanFold.run (branchBody solver) inp.2.1.length (inp, 0)
/-- Total common-zero count computed by streaming `2 ^ |S|` heavy-variable branches. -/
def countByBranching (solver : ℕ → List (List (List ℕ)) → ℕ) (inp : BranchInput) : ℕ :=
  (streamBranches solver inp).2.2.2

private theorem foldl_branchBody_eq (solver : ℕ → List (List (List ℕ)) → ℕ)
    (k : ℕ) (inp : BranchInput) (l : List (List Bool)) (acc₀ : ℕ) :
    l.foldl (fun acc vals => branchBody solver ((k, vals), acc)) (inp, acc₀) =
      (inp, acc₀ + (l.map fun vals =>
        branchCountOracle solver (prepareBranch inp.1 inp.2.1 vals inp.2.2)).sum) := by
  induction l generalizing acc₀ with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons vals vs ih =>
    rw [List.foldl_cons, List.map_cons, List.sum_cons,
      show branchBody solver ((k, vals), (inp, acc₀)) =
        (inp, acc₀ + branchCountOracle solver (prepareBranch inp.1 inp.2.1 vals inp.2.2)) from rfl,
      ih, Nat.add_assoc]

/-- Prefix invariant of `BooleanFold.runPrefix`: `inp` is preserved and the accumulator holds the
sum of the first `j` decoded branch counts. -/
theorem runPrefix_branchBody_accumulator (solver : ℕ → List (List (List ℕ)) → ℕ)
    (inp : BranchInput) (j : ℕ) :
    (BooleanFold.runPrefix (branchBody solver) inp.2.1.length j (inp, 0)).2.2 =
      (inp, ((List.range j).map fun idx =>
        branchCountOracle solver
          (prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2)).sum) := by
  rw [BooleanFold.prefix_accumulator,
    ← List.foldl_map (f := lowBits inp.2.1.length)
      (g := fun acc vals => branchBody solver ((inp.2.1.length, vals), acc)),
    foldl_branchBody_eq]
  simp only [Nat.zero_add, List.map_map, Function.comp_def]

/-- **Streaming correctness**: for `S.Nodup` in `< n` and `sys` on `< n`, `(streamBranches solver
(n, S, sys)).2.2 = ((n, S, sys), rootCount n sys)` when `solver` is exact on `.reduced` branches. -/
theorem streamBranches_correct {n : ℕ} {S : List ℕ} {sys : List (List (List ℕ))}
    {solver : ℕ → List (List (List ℕ)) → ℕ}
    (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hsolver : ∀ vals, vals.length = S.length → ∀ n' sys',
      prepareBranch n S vals sys = .reduced n' sys' → solver n' sys' = rootCount n' sys') :
    (streamBranches solver (n, S, sys)).2.2 = ((n, S, sys), rootCount n sys) := by
  rw [streamBranches, BooleanFold.run_accumulator, foldl_branchBody_eq, Nat.zero_add,
    ← BooleanFold.decoded_range_eq_enumList, List.map_map]
  exact congrArg (Prod.mk (n, S, sys)) (sum_branch_count_eq_rootCount hS hSn hvars hsolver)

/-- **Streaming count correctness**: for `S.Nodup` in `< n` and `sys` on `< n`, `countByBranching
solver (n, S, sys) = rootCount n sys` when `solver` is exact on `.reduced` branches. -/
theorem countByBranching_eq_rootCount {n : ℕ} {S : List ℕ} {sys : List (List (List ℕ))}
    {solver : ℕ → List (List (List ℕ)) → ℕ}
    (hS : S.Nodup) (hSn : ∀ s ∈ S, s < n) (hvars : ∀ eq ∈ sys, ∀ m ∈ eq, ∀ v ∈ m, v < n)
    (hsolver : ∀ vals, vals.length = S.length → ∀ n' sys',
      prepareBranch n S vals sys = .reduced n' sys' → solver n' sys' = rootCount n' sys') :
    countByBranching solver (n, S, sys) = rootCount n sys :=
  congrArg Prod.snd (streamBranches_correct hS hSn hvars hsolver)

end Cslib.GenericRAM.HeavyBranchFold
end

public section
namespace Cslib.GenericRAM.HeavyBranchFold
open Cslib Cslib.BitString Cslib.Complexity Turing.MultiTapeTM

private def reducedCost (f : ℕ × List (List (List ℕ)) → ℕ) : BranchOutcome → ℕ
  | .reduced n' sys' => f (n', sys')
  | _ => 0

/-- Selected-branch native certificate for `branchCountOracle solver`: a fixed `csolver` runs ONLY
on `.reduced n' sys'` outcomes, while `.contradiction` emits `0` and `.tautology n'` emits `2 ^ n'`
via `BooleanFold.clock` in linear time and space. -/
noncomputable def branchCountCertificate {solver : ℕ → List (List (List ℕ)) → ℕ}
    (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
      (encPair encUnary (encList (encList (encList encNat)))) encNat) :
    NativeCertificate (branchCountOracle solver) encBranchOutcome encNat :=
  let encSys := encList (encList (encList encNat))
  let encInner := encPair encUnary (encOption encSys)
  let cpair : NativeCertificate
      (fun r : (ℕ × Option (List (List (List ℕ)))) × List (List (List ℕ)) => (r.1.1, r.2))
      (encPair encInner encSys) (encPair encUnary encSys) :=
    ((NativeCertificate.linear (ComputableInO.fst encInner encSys)).fst).prod
      (NativeCertificate.payload encInner encSys)
  let innerCert : NativeCertificate
      (fun q : ℕ × Option (List (List (List ℕ))) =>
        q.2.elim (2 ^ q.1) (fun sys' => solver q.1 sys')) encInner encNat :=
    NativeCertificate.option (NativeCertificate.payload encUnary (encOption encSys))
      (BooleanFold.clock.pull (encOption encSys)) (csolver.comp cpair)
  (NativeCertificate.option (value := BranchOutcome.toOption)
    (NativeCertificate.linear (f := BranchOutcome.toOption)
      (ei := encBranchOutcome) (em := encOption encInner)
      (.of_eq fun o => (encBranchOutcome_eq o).symm))
    (NativeCertificate.const 0)
    (innerCert.comp (NativeCertificate.payload encBranchOutcome encInner))).congr
    fun o => by cases o <;> rfl

private theorem branchCountCertificate_bounds {solver : ℕ → List (List (List ℕ)) → ℕ}
    (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
      (encPair encUnary (encList (encList (encList encNat)))) encNat) (o : BranchOutcome) :
    (branchCountCertificate csolver).time o ≤
        20 * (encBranchOutcome o).length + 5 + reducedCost csolver.time o ∧
      (branchCountCertificate csolver).space o ≤
        20 * (encBranchOutcome o).length + 5 + reducedCost csolver.space o := by
  cases o with
  | contradiction =>
    dsimp only [branchCountCertificate, NativeCertificate.congr, NativeCertificate.option,
      NativeCertificate.linear, NativeCertificate.const, BranchOutcome.toOption, Option.elim,
      reducedCost]; omega
  | tautology n' =>
    rw [encBranchOutcome_eq]
    dsimp only [branchCountCertificate, NativeCertificate.congr, NativeCertificate.option,
      NativeCertificate.linear, NativeCertificate.comp, NativeCertificate.payload,
      NativeCertificate.pull, NativeCertificate.post, BooleanFold.clock, BranchOutcome.toOption,
      Option.elim, reducedCost]
    simp only [encBranchOutcome_eq, BranchOutcome.toOption, encOption_some, encOption_none,
      length_encPair, List.length_cons, List.length_nil, encUnary_apply, List.length_replicate]
    omega
  | reduced n' sys' =>
    rw [encBranchOutcome_eq]
    dsimp only [branchCountCertificate, NativeCertificate.congr, NativeCertificate.option,
      NativeCertificate.linear, NativeCertificate.comp, NativeCertificate.payload,
      NativeCertificate.prod, NativeCertificate.fst, NativeCertificate.post,
      BranchOutcome.toOption, Option.elim, reducedCost]
    simp only [encBranchOutcome_eq, BranchOutcome.toOption, encOption_some, length_encPair,
      List.length_cons, encUnary_apply, List.length_replicate]; omega

theorem computableInPolyTime_prepareStep :
    ComputableInPolyTime (fun p : (ℕ × List Bool) × (BranchInput × ℕ) =>
      prepareBranch p.2.1.1 p.2.1.2.1 p.1.2 p.2.1.2.2)
      (encPair (encPair encUnary encBits) (encPair encBranchInput encNat)) encBranchOutcome := by
  unfold encBranchInput; fun_prop
private theorem computableInPolyTime_binaryAdd :
    ComputableInPolyTime (fun x : ℕ × ℕ => x.1 + x.2) (encPair encNat encNat) encNat :=
  ComputableInPolyTime.binary_add
private theorem computableInPolyTime_dim :
    ComputableInPolyTime (fun inp : BranchInput => inp.2.1.length) encBranchInput encUnary := by
  unfold encBranchInput; fun_prop
private noncomputable def prepareStepCert :=
  NativeCertificate.ofPolyTime computableInPolyTime_prepareStep
private noncomputable def binaryAddCert :=
  NativeCertificate.ofPolyTime computableInPolyTime_binaryAdd
private noncomputable def dimCert := NativeCertificate.ofPolyTime computableInPolyTime_dim
private noncomputable def initAccCert : NativeCertificate (fun inp : BranchInput => (inp, 0))
    encBranchInput (encPair encBranchInput encNat) :=
  (NativeCertificate.linear (.of_eq fun _ => rfl)).prod (NativeCertificate.const 0)
private noncomputable def prepVisitCert := NativeCertificate.ofPolyTime
  (BooleanFold.prepare_polyTime (encB := encPair encBranchInput encNat))

/-- Per-branch native callback certificate for `branchBody solver` (for a fixed `solver`). -/
noncomputable def branchBodyCertificate {solver : ℕ → List (List (List ℕ)) → ℕ}
    (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
      (encPair encUnary (encList (encList (encList encNat)))) encNat) :
    NativeCertificate (branchBody solver)
      (encPair (encPair encUnary encBits) (encPair encBranchInput encNat))
      (encPair encBranchInput encNat) :=
  let cpay := NativeCertificate.payload (encPair encUnary encBits) (encPair encBranchInput encNat)
  (cpay.fst).prod
    (binaryAddCert.comp ((cpay.snd).prod ((branchCountCertificate csolver).comp prepareStepCert)))
/-- Full streaming native certificate for `streamBranches solver` (for a fixed `solver`). -/
noncomputable def certificate {solver : ℕ → List (List (List ℕ)) → ℕ}
    (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
      (encPair encUnary (encList (encList (encList encNat)))) encNat) :
    NativeCertificate (streamBranches solver)
      encBranchInput (encPair encNat (encPair encUnary (encPair encBranchInput encNat))) :=
  BooleanFold.certificate dimCert initAccCert (branchBodyCertificate csolver)
/-- Full streaming native certificate for `countByBranching solver` (for a fixed `solver`). -/
noncomputable def countCertificate {solver : ℕ → List (List (List ℕ)) → ℕ}
    (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
      (encPair encUnary (encList (encList (encList encNat)))) encNat) :
    NativeCertificate (countByBranching solver) encBranchInput encNat :=
  (((certificate csolver).snd).snd).snd
private theorem length_le_encBranchInput (inp : BranchInput) :
    2 * inp.1 + 2 * inp.2.1.length + 2 ≤ (encBranchInput inp).length := by
  have hS : inp.2.1.length ≤ (encList encNat inp.2.1).length :=
    SizedListEncoding.length_le (encA := encNat) inp.2.1
  simp only [encBranchInput, length_encPair, encUnary_apply, List.length_replicate]; omega

/-- Prefix sum bound: when `solver n' sys' ≤ 2 ^ n'` on reduced branches of `inp`, every streaming
prefix `j ≤ 2 ^ |S|` keeps the running sum at most `j * 2 ^ (n - |S|)`. -/
theorem runPrefix_sum_le {solver : ℕ → List (List (List ℕ)) → ℕ} {inp : BranchInput}
    (hbound : ∀ idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      solver n' sys' ≤ 2 ^ n')
    {j : ℕ} (hj : j ≤ 2 ^ inp.2.1.length) :
    (BooleanFold.runPrefix (branchBody solver) inp.2.1.length j (inp, 0)).2.2.2 ≤
      j * 2 ^ (inp.1 - inp.2.1.length) := by
  rw [runPrefix_branchBody_accumulator]; dsimp only
  have hterm : ∀ x ∈ (List.range j).map (fun idx =>
      branchCountOracle solver (prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2)),
      x ≤ 2 ^ (inp.1 - inp.2.1.length) := by
    intro x hx; obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hx
    have hlt : idx < 2 ^ inp.2.1.length := Nat.lt_of_lt_of_le (List.mem_range.mp hidx) hj
    cases hout : prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 with
    | contradiction => exact Nat.zero_le _
    | tautology n' => rw [prepareBranch_freeVars_eq.1 hout]; exact le_rfl
    | reduced n' sys' => exact (prepareBranch_freeVars_eq.2 sys' hout) ▸ hbound idx hlt n' sys' hout
  simpa only [List.length_map, List.length_range, smul_eq_mul] using
    List.sum_le_length_nsmul _ (2 ^ (inp.1 - inp.2.1.length)) hterm

/-- When `|S| ≤ n` and `solver n' sys' ≤ 2 ^ n'` on reduced branches, the running sum satisfies
`Z ≤ 2 ^ n` throughout the entire streaming traversal (§5.5 p. 39 of [OpenAI2026ETH]). -/
theorem runPrefix_sum_le_two_pow {solver : ℕ → List (List (List ℕ)) → ℕ} {inp : BranchInput}
    (hSn : inp.2.1.length ≤ inp.1)
    (hbound : ∀ idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      solver n' sys' ≤ 2 ^ n')
    {j : ℕ} (hj : j ≤ 2 ^ inp.2.1.length) :
    (BooleanFold.runPrefix (branchBody solver) inp.2.1.length j (inp, 0)).2.2.2 ≤ 2 ^ inp.1 :=
  (runPrefix_sum_le hbound hj).trans <| (Nat.mul_le_mul_right _ hj).trans_eq <|
    (Nat.pow_add 2 _ _).symm.trans (by rw [Nat.add_sub_of_le hSn])

private noncomputable def monoPolyBound {α : Type*} {size u : α → ℕ}
    (h : PolyBounded size u) (k : ℕ) : ℕ :=
  Classical.choose h.exists_le * (k + 1) ^ Classical.choose (Classical.choose_spec h.exists_le)

private theorem monoPolyBound_isPoly {α : Type*} {size u : α → ℕ}
    (h : PolyBounded size u) : PolynomiallyBounded (monoPolyBound h) := by
  unfold monoPolyBound; fun_prop

attribute [local fun_prop] monoPolyBound_isPoly

private theorem le_monoPolyBound {α : Type*} {size u : α → ℕ}
    (h : PolyBounded size u) (a : α) {M : ℕ} (hM : size a ≤ M) :
    u a ≤ monoPolyBound h M :=
  (Classical.choose_spec (Classical.choose_spec h.exists_le) a).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) _))

private noncomputable def visitOverhead (L : ℕ) : ℕ :=
  let hpv := NativeCertificate.ofPolyTime_isPolynomial
    (BooleanFold.prepare_polyTime (encB := encPair encBranchInput encNat))
  let hps := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_prepareStep
  let hadd := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_binaryAdd
  17 * L + 18 + monoPolyBound hpv.1 (5 * L + 5) + monoPolyBound hpv.2 (5 * L + 5) +
    monoPolyBound hps.1 (6 * L + 4) + monoPolyBound hps.2 (6 * L + 4) +
    20 * monoPolyBound computableInPolyTime_prepareStep.polyBounded_length (6 * L + 4) +
    monoPolyBound hadd.1 (3 * L + 1) + monoPolyBound hadd.2 (3 * L + 1)

/-- Solver-independent polynomial overhead per streaming round and for initialization. -/
noncomputable def stepOverhead (L : ℕ) : ℕ :=
  let hd := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_dim
  2 * monoPolyBound hd.1 L + 2 * monoPolyBound hd.2 L +
    visitOverhead L + 2 * (L + 2) ^ 2 + 25 * L + 25

/-- `stepOverhead` is polynomially bounded in the encoded input length. -/
@[fun_prop] theorem polynomiallyBounded_stepOverhead : PolynomiallyBounded stepOverhead := by
  unfold stepOverhead visitOverhead; fun_prop

private theorem branchBodyCertificate_eq {solver : ℕ → List (List (List ℕ)) → ℕ}
    (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
      (encPair encUnary (encList (encList (encList encNat)))) encNat)
    (q : (ℕ × List Bool) × (BranchInput × ℕ)) :
    let o := prepareBranch q.2.1.1 q.2.1.2.1 q.1.2 q.2.1.2.2
    let lq := (encPair (encPair encUnary encBits) (encPair encBranchInput encNat) q).length
    (branchBodyCertificate csolver).time q =
        2 * lq + prepareStepCert.time q + (branchCountCertificate csolver).time o +
          binaryAddCert.time (q.2.2, branchCountOracle solver o) ∧
      (branchBodyCertificate csolver).space q =
        2 * lq + prepareStepCert.space q + (branchCountCertificate csolver).space o +
          binaryAddCert.space (q.2.2, branchCountOracle solver o) := by
  dsimp only [branchBodyCertificate, NativeCertificate.prod, NativeCertificate.comp,
    NativeCertificate.fst, NativeCertificate.snd, NativeCertificate.payload,
    NativeCertificate.linear, NativeCertificate.post, Function.comp_def]; omega

private theorem branch_step_bounds {solver : ℕ → List (List (List ℕ)) → ℕ}
    (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
      (encPair encUnary (encList (encList (encList encNat)))) encNat)
    {R_solver Q_solver : BranchInput → ℕ}
    (hbound : ∀ (inp : BranchInput) idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      solver n' sys' ≤ 2 ^ n')
    (hR : ∀ (inp : BranchInput) idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      csolver.time (n', sys') ≤ R_solver inp)
    (hQ : ∀ (inp : BranchInput) idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      csolver.space (n', sys') ≤ Q_solver inp)
    (inp : BranchInput) {j : ℕ} (hj : j ≤ 2 ^ inp.2.1.length) :
    let L := (encBranchInput inp).length
    let st := BooleanFold.runPrefix (branchBody solver) inp.2.1.length j (inp, 0)
    let vcert := BooleanFold.visitCertificate (branchBodyCertificate csolver)
    (encPair encUnary (encPair encBranchInput encNat) st.2).length ≤ 4 * L + 1 ∧
      vcert.time st ≤ visitOverhead L + R_solver inp ∧
      vcert.space st ≤ visitOverhead L + Q_solver inp := by
  intro L st vcert
  have hL : 2 * inp.1 + 2 * inp.2.1.length + 2 ≤ L := length_le_encBranchInput inp
  have hst_pair : st.2.2 = (inp, st.2.2.2) :=
    Prod.ext (by rw [runPrefix_branchBody_accumulator]) rfl
  have hsum_le : st.2.2.2 ≤ 2 ^ (inp.2.1.length + inp.1) :=
    (runPrefix_sum_le (hbound inp) hj).trans <|
      (Nat.mul_le_mul hj (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))).trans_eq
        (Nat.pow_add 2 _ _).symm
  have hlen_accSum : (encNat st.2.2.2).length ≤ L := by
    have h : (encNat st.2.2.2).length ≤ (encNat (2 ^ (inp.2.1.length + inp.1))).length := by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size hsum_le
    rw [BooleanFold.length_clock] at h; omega
  have hlen_acc : (encPair encBranchInput encNat st.2.2).length ≤ 3 * L + 1 := by
    rw [hst_pair, length_encPair]
    change 2 * L + 1 + (encNat st.2.2.2).length ≤ 3 * L + 1; omega
  have hst1 : st.1 = j := IndexFold.run_index _ _ _
  have hst21 : st.2.1 = inp.2.1.length := BooleanFold.prefix_width _ _ _ _
  have hlen_inner : (encPair encUnary (encPair encBranchInput encNat) st.2).length ≤ 4 * L + 1 := by
    rw [show st.2 = (inp.2.1.length, st.2.2) from Prod.ext hst21 rfl, length_encPair,
      encUnary_apply, List.length_replicate]; dsimp only; omega
  have hlen_state : (encPair encNat (encPair encUnary (encPair encBranchInput encNat)) st).length ≤
      5 * L + 5 := by
    have h := BooleanFold.length_prefix_le (encB := encPair encBranchInput encNat)
      (branchBody solver) inp.2.1.length j (3 * L + 1) (inp, 0) hj hlen_acc
    change (encPair encNat (encPair encUnary (encPair encBranchInput encNat)) st).length ≤ _ at h
    omega
  let q : (ℕ × List Bool) × (BranchInput × ℕ) := ((st.2.1, lowBits st.2.1 st.1), st.2.2)
  have hlen_q : (encPair (encPair encUnary encBits) (encPair encBranchInput encNat) q).length ≤
      6 * L + 4 := by
    have h := BooleanFold.length_callback_input (encB := encPair encBranchInput encNat)
      st.2.1 st.1 st.2.2
    change (encPair (encPair encUnary encBits) (encPair encBranchInput encNat) q).length = _ at h
    rw [hst21] at h; omega
  let idx' := if j < 2 ^ inp.2.1.length then j else 0
  have hidx'_lt : idx' < 2 ^ inp.2.1.length := by
    dsimp only [idx']; split_ifs with hlt; exacts [hlt, Nat.two_pow_pos _]
  have hlow_eq : lowBits st.2.1 st.1 = lowBits inp.2.1.length idx' := by
    rw [hst21, hst1]; dsimp only [idx']; split_ifs with hlt
    · rfl
    · rw [show j = 2 ^ inp.2.1.length by omega, lowBits_two_pow]
  let o := prepareBranch q.2.1.1 q.2.1.2.1 q.1.2 q.2.1.2.2
  have ho_eq : o = prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx') inp.2.2 := by
    dsimp only [o, q]; rw [congrArg Prod.fst hst_pair, hlow_eq]
  obtain ⟨hbc_le, hsolT, hsolS⟩ : branchCountOracle solver o ≤ 2 ^ inp.1 ∧
      reducedCost csolver.time o ≤ R_solver inp ∧ reducedCost csolver.space o ≤ Q_solver inp := by
    rw [ho_eq]; cases hout : prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx') inp.2.2 with
    | contradiction => exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
    | tautology n' =>
      rw [prepareBranch_freeVars_eq.1 hout]
      exact ⟨Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _), Nat.zero_le _, Nat.zero_le _⟩
    | reduced n' sys' =>
      have hn' := prepareBranch_freeVars_eq.2 sys' hout
      exact ⟨(hbound inp idx' hidx'_lt n' sys' hout).trans
          (hn' ▸ Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)),
        hR inp idx' hidx'_lt n' sys' hout, hQ inp idx' hidx'_lt n' sys' hout⟩
  have hlen_bc : (encNat (branchCountOracle solver o)).length ≤ L := by
    have h : (encNat (branchCountOracle solver o)).length ≤ (encNat (2 ^ inp.1)).length := by
      simpa [Nat.size_eq_bits_len] using Nat.size_le_size hbc_le
    rw [BooleanFold.length_clock] at h; omega
  have hlen_add : (encPair encNat encNat (q.2.2, branchCountOracle solver o)).length ≤ 3 * L + 1 :=
    by rw [show q.2.2 = st.2.2.2 from rfl, length_encPair]; dsimp only; omega
  let hpv := NativeCertificate.ofPolyTime_isPolynomial
    (BooleanFold.prepare_polyTime (encB := encPair encBranchInput encNat))
  let hps := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_prepareStep
  let hadd := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_binaryAdd
  have hpvT := le_monoPolyBound hpv.1 st hlen_state
  have hpvS := le_monoPolyBound hpv.2 st hlen_state
  have hpsT := le_monoPolyBound hps.1 q hlen_q; have hpsS := le_monoPolyBound hps.2 q hlen_q
  have houtL := le_monoPolyBound computableInPolyTime_prepareStep.polyBounded_length q hlen_q
  have haddT := le_monoPolyBound hadd.1 _ hlen_add; have haddS := le_monoPolyBound hadd.2 _ hlen_add
  obtain ⟨hbcT, hbcS⟩ := branchCountCertificate_bounds csolver o
  obtain ⟨hbodyT, hbodyS⟩ := branchBodyCertificate_eq csolver q
  let sL := (encPair encNat (encPair encUnary (encPair encBranchInput encNat)) st).length
  let bcert := branchBodyCertificate csolver
  have hvT : vcert.time st = sL + (prepVisitCert.time st + bcert.time q) := rfl
  have hvS : vcert.space st = sL + (prepVisitCert.space st + bcert.space q) := rfl
  dsimp only [sL, bcert, o, prepVisitCert, prepareStepCert, binaryAddCert]
    at hbcT hbcS houtL hlen_add haddT haddS hsolT hsolS hvT hvS hbodyT hbodyS
  refine ⟨hlen_inner, ?_, ?_⟩
  · rw [hvT, hbodyT]; dsimp only [visitOverhead, prepareStepCert, binaryAddCert]; omega
  · rw [hvS, hbodyS]; dsimp only [visitOverhead, prepareStepCert, binaryAddCert]; omega

/-- **Space-efficient streaming `ComputableInO` bound for `streamBranches`** (§5.5 of
[OpenAI2026ETH]): for fixed `solver` bounded by `2 ^ n'` with time `≤ R_solver` and space
`≤ Q_solver` on `.reduced` branches, runs in time `O(stepOverhead |inp| + (2 ^ |S| + 1) *
(stepOverhead |inp| + R_solver inp))` and workspace `O(stepOverhead |inp| + Q_solver inp)`. -/
theorem streamBranches_computableInO {solver : ℕ → List (List (List ℕ)) → ℕ}
    (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
      (encPair encUnary (encList (encList (encList encNat)))) encNat)
    (R_solver Q_solver : BranchInput → ℕ)
    (hbound : ∀ (inp : BranchInput) idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      solver n' sys' ≤ 2 ^ n')
    (hR : ∀ (inp : BranchInput) idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      csolver.time (n', sys') ≤ R_solver inp)
    (hQ : ∀ (inp : BranchInput) idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      csolver.space (n', sys') ≤ Q_solver inp) :
    ComputableInO (streamBranches solver)
      encBranchInput (encPair encNat (encPair encUnary (encPair encBranchInput encNat)))
      (fun inp => stepOverhead (encBranchInput inp).length +
        (2 ^ inp.2.1.length + 1) * (stepOverhead (encBranchInput inp).length + R_solver inp))
      (fun inp => stepOverhead (encBranchInput inp).length + Q_solver inp) := by
  have hfold := IndexFold.computableInO
    (BooleanFold.clock.comp dimCert) (dimCert.prod initAccCert)
    (BooleanFold.visitCertificate (branchBodyCertificate csolver))
    (fun inp => visitOverhead (encBranchInput inp).length + R_solver inp)
    (fun inp => visitOverhead (encBranchInput inp).length + Q_solver inp)
    (fun inp => 4 * (encBranchInput inp).length + 1)
    (fun inp j hj => (branch_step_bounds csolver hbound hR hQ inp hj).2.1)
    (fun inp j hj => (branch_step_bounds csolver hbound hR hQ inp hj).2.2)
    (fun inp j hj => (branch_step_bounds csolver hbound hR hQ inp hj).1)
  let hd := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_dim
  refine hfold.mono_le (fun inp => ?_) (fun inp => ?_)
  · let L := (encBranchInput inp).length
    have hL : 2 * inp.1 + 2 * inp.2.1.length + 2 ≤ L := length_le_encBranchInput inp
    have hdT : dimCert.time inp ≤ monoPolyBound hd.1 L := le_monoPolyBound hd.1 inp le_rfl
    have hclk := BooleanFold.length_clock inp.2.1.length
    have hsq : (inp.2.1.length + 1 + 1) ^ 2 ≤ (L + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hct : BooleanFold.clock.time inp.2.1.length = inp.2.1.length := by
      simp only [BooleanFold.clock, encUnary_apply, List.length_replicate]
    simp only [NativeCertificate.comp_time, NativeCertificate.prod_time, initAccCert,
      NativeCertificate.linear_time, NativeCertificate.const_time, Function.comp_apply, hct, hclk]
    have hmul :
        (2 * (inp.2.1.length + 1) + 1 + (4 * L + 1) +
            (inp.2.1.length + 1 + 1) ^ 2 + (visitOverhead L + R_solver inp)) +
          (2 * (inp.2.1.length + 1) + 1 + (4 * L + 1)) +
          (inp.2.1.length + 1 + 1) ^ 2 ≤ stepOverhead L + R_solver inp := by
      dsimp only [stepOverhead, L] at hsq ⊢; omega
    have hprod := Nat.mul_le_mul_left (2 ^ inp.2.1.length + 1) hmul
    dsimp only [stepOverhead, L] at hdT hprod ⊢; omega
  · let L := (encBranchInput inp).length
    have hL : 2 * inp.1 + 2 * inp.2.1.length + 2 ≤ L := length_le_encBranchInput inp
    have hdS : dimCert.space inp ≤ monoPolyBound hd.2 L := le_monoPolyBound hd.2 inp le_rfl
    have hclk := BooleanFold.length_clock inp.2.1.length
    have hcs : BooleanFold.clock.space inp.2.1.length = inp.2.1.length := by
      simp only [BooleanFold.clock, encUnary_apply, List.length_replicate]
    simp only [NativeCertificate.comp_space, NativeCertificate.prod_space, initAccCert,
      NativeCertificate.linear_space, NativeCertificate.const_space, Function.comp_apply, hcs, hclk]
    dsimp only [stepOverhead, L] at hdS ⊢; omega

/-- **Space-efficient streaming `ComputableInO` bound for `countByBranching`** (§5.5 of
[OpenAI2026ETH]): for fixed `solver` bounded by `2 ^ n'` with time `≤ R_solver` and space
`≤ Q_solver` on `.reduced` branches, returns the total count in time `O(stepOverhead |inp| +
(2 ^ |S| + 1) * (stepOverhead |inp| + R_solver inp))` and workspace `O(stepOverhead |inp| +
Q_solver inp)` (with no `2 ^ |S|` factor in workspace). -/
theorem countByBranching_computableInO {solver : ℕ → List (List (List ℕ)) → ℕ}
    (csolver : NativeCertificate (fun p : ℕ × List (List (List ℕ)) => solver p.1 p.2)
      (encPair encUnary (encList (encList (encList encNat)))) encNat)
    (R_solver Q_solver : BranchInput → ℕ)
    (hbound : ∀ (inp : BranchInput) idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      solver n' sys' ≤ 2 ^ n')
    (hR : ∀ (inp : BranchInput) idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      csolver.time (n', sys') ≤ R_solver inp)
    (hQ : ∀ (inp : BranchInput) idx, idx < 2 ^ inp.2.1.length → ∀ n' sys',
      prepareBranch inp.1 inp.2.1 (lowBits inp.2.1.length idx) inp.2.2 = .reduced n' sys' →
      csolver.space (n', sys') ≤ Q_solver inp) :
    ComputableInO (countByBranching solver) encBranchInput encNat
      (fun inp => stepOverhead (encBranchInput inp).length +
        (2 ^ inp.2.1.length + 1) * (stepOverhead (encBranchInput inp).length + R_solver inp))
      (fun inp => stepOverhead (encBranchInput inp).length + Q_solver inp) :=
  (ComputableInO.snd encBranchInput encNat).comp_linear <|
    (ComputableInO.snd encUnary (encPair encBranchInput encNat)).comp_linear <|
      (ComputableInO.snd encNat (encPair encUnary (encPair encBranchInput encNat))).comp_linear
        (streamBranches_computableInO csolver R_solver Q_solver hbound hR hQ)

/-- Polynomial-workspace preservation: whenever `Q_solver` is polynomially bounded in the encoded
input length, the total streaming workspace `stepOverhead |inp| + Q_solver inp` is also
polynomially bounded (independent of `2 ^ |S|`). -/
theorem polyBounded_branchWorkspace {Q_solver : BranchInput → ℕ}
    (hQ : PolyBounded (fun inp => (encBranchInput inp).length) Q_solver) :
    PolyBounded (fun inp => (encBranchInput inp).length)
      (fun inp => stepOverhead (encBranchInput inp).length + Q_solver inp) :=
  (PolyBounded.of_polynomiallyBounded _ polynomiallyBounded_stepOverhead).add hQ

end Cslib.GenericRAM.HeavyBranchFold
end
