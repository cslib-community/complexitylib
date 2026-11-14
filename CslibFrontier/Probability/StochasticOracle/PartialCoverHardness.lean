/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.PartialCoverRisk
public import CslibFrontier.Computability.PCP.Approximation.SetCover.ApproxReduction
import CslibFrontier.Computability.PCP.Approximation.SetCover.LundYannakakis
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic

/-!
# Set Cover hardness of minimum-token one-turn partial-cover selection

[Wang2027], hardness remark after the proof of Theorem 4, Section 5 (PDF p. 11).
Given an unweighted Set Cover instance $(U, \{V_i\}_{i \in [k]})$, oracle $i$ returns
$V_i$ with certainty at unit token cost and unit latency. With $p = \eta = 1$,
$y_e = 1/n$ and $\rho = n$, every response covering a new element passes the local
dual test, so a one-turn batch succeeds exactly when its returned sets cover $U$ and
its token cost is the number of oracle calls, counting repeated calls separately.
An optimal batch needs at most one call to each deterministic oracle.

`Selection` is the binary input of this deterministic oracle class: ground labels,
the known returned set of every oracle and natural token costs. `success` is the
probability, under the actual fixed-order retention law `Instance.law` of
`PartialCoverRisk`, that the retained subfamilies cover the ground set; the batch
issues `ζᵢ` calls to oracle `i`. `minSelection` is the minimization problem whose
feasible solutions are call-count vectors with success probability at least
$\eta = 1$, priced by their token cost $c(\zeta) = \sum_i c_i \zeta_i$.

The reduction `approxPreservingReducible_setCover_selection` is approximation
preserving with identity ratio, so the library's unconditional Lund–Yannakakis/Feige
constant-factor Set Cover hardness transfers: `P_eq_NP_of_selection_approx_const`.
The source's sharper $(1-\varepsilon)\ln n$ inapproximability (Dinur–Steurer) is
**not** proved here: it needs low-soundness Label Cover beyond the library's
constant-round base (#4335). `P_eq_NP_of_selection_approx` transfers `NP`-hardness of
`GapSetCover r` only for a constant ratio `r`; a $\ln n$ bound additionally needs
instance-dependent (`GapSetCoverFn`) versions of the hardness and `P = NP` wrappers. The
reduction itself would carry over, since it maps ratios by the identity and keeps the
ground set.

## Main definitions

* `Selection`, `encSelection`: deterministic oracle tables and their binary encoding.
* `Selection.success`: actual one-turn retention success probability of a call vector.
* `minSelection`: minimum-token one-turn partial-cover selection at $\eta = 1$.

## Main results

* `Selection.success_eq`: success is one exactly when the queried sets cover the ground set.
* `Selection.admissible`: these oracles satisfy Theorem 4's conditional guarantee with `p = 1`.
* `approxPreservingReducible_setCover_selection`: Set Cover reduces with identity ratio.
* `P_eq_NP_of_selection_approx`, `P_eq_NP_of_selection_approx_const`: polynomial-time
  approximation of the selection problem collapses `P` and `NP`.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.PartialCover.Hardness
open Finset Cslib.Optimization.OneConstraint Cslib.Complexity Turing.MultiTapeTM

/-- Deterministic oracle tables of the hardness remark. Oracle `i` returns its known
set `oracles[i]` with certainty; elements outside `ground` are ignored. -/
structure Selection where
  /-- Ground labels $U$, which every successful batch must cover. -/
  ground : List ℕ
  /-- The set $V_i$ returned by every call to oracle `i`. -/
  oracles : List (List ℕ)
  /-- Natural token cost of one call to oracle `i`; missing entries cost zero. -/
  costs : List ℕ
  deriving DecidableEq

/-- Framed binary ground labels, oracle sets and token costs. -/
enc_structure encSelection : Selection where
  ground : (encList encNat), oracles : encNatSetList, costs : (encList encNat)

namespace Selection

variable (x : Selection)

/-- Number of oracles. -/
abbrev size : ℕ := x.oracles.length

/-- The unit-weight WSC instance with dual prices `1/n`, where `n = |U|`. -/
def inst : Instance ℕ (Fin x.size) where
  ground := x.ground.toFinset
  sets j := x.oracles[j].toFinset.filter (· ∈ x.ground)
  sets_subset j := fun e he => by simpa using (Finset.mem_filter.1 he).2
  weight _ := 1
  weight_nonneg _ := zero_le_one
  dual _ := 1 / (x.ground.toFinset.card : ℝ)
  dual_nonneg _ := by positivity
  dual_feasible j := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hsub : (x.oracles[j].toFinset.filter (· ∈ x.ground)) ⊆ x.ground.toFinset :=
      fun e he => by simpa using (Finset.mem_filter.1 he).2
    rcases Nat.eq_zero_or_pos x.ground.toFinset.card with h0 | hpos
    · simp [h0]
    · rw [mul_one_div, div_le_one (by exact_mod_cast hpos)]
      exact_mod_cast Finset.card_le_card hsub

/-- The local dual-test factor $\rho = n$. -/
def rho : ℝ := x.ground.toFinset.card

/-- Calls of a one-turn batch issuing `ζ.getD i 0` calls to oracle `i`, in oracle order. -/
def calls (ζ : List ℕ) : List (Fin x.size) :=
  (List.finRange x.size).flatMap fun i : Fin x.size => List.replicate (ζ.getD (i : ℕ) 0) i

/-- The `k`th processed response: the singleton subfamily of the `k`th called oracle. -/
def response (ζ : List ℕ) (k : ℕ) : Finset (Fin x.size) :=
  ((x.calls ζ)[k]?).elim ∅ fun i => {i}

/-- Deterministic response kernel, read off from the processing position. -/
def kernel (ζ : List ℕ) : Instance.ResponseKernel (Fin x.size) :=
  fun h => Distribution.pure (x.response ζ h.length)

/-- Known eligibility sets in processing order, one per call. -/
def eligible (ζ : List ℕ) : List (Finset ℕ) := (x.calls ζ).map fun i => (x.inst).sets i

/-- Probability that the actual retention law certifies a cover of the ground set. -/
def success (ζ : List ℕ) : ℝ :=
  Instance.event ((x.inst).law x.rho (x.kernel ζ) [] ∅ (x.eligible ζ))
    fun C => (x.inst).covered C = (x.inst).ground

/-- Token cost $c(\zeta) = \sum_i c_i \zeta_i$ over the actual oracles. -/
def tokens (ζ : List ℕ) : ℕ :=
  ((List.range x.size).map fun i => x.costs.getD i 0 * ζ.getD i 0).sum

/-- The batch queries every ground element through some called oracle. -/
def Covers (ζ : List ℕ) : Prop :=
  ∀ e ∈ x.ground, ∃ i : Fin x.size, 0 < ζ.getD (i : ℕ) 0 ∧ e ∈ x.oracles[i]

/-- Retained family after processing the responses at positions `k, k+1, …, k+n-1`. -/
def final (ζ : List ℕ) : ℕ → Finset (Fin x.size) → ℕ → Finset (Fin x.size)
  | _, C, 0 => C
  | k, C, n + 1 => final ζ (k + 1) ((x.inst).step x.rho C (x.response ζ k)) n

open scoped Classical in
/-- The actual retention law of a deterministic batch is concentrated on `final`. -/
theorem event_law (ζ : List ℕ) (A : Finset (Fin x.size) → Prop) :
    ∀ (vs : List (Finset ℕ)) (h : List (Finset (Fin x.size))) (C : Finset (Fin x.size)),
      Instance.event ((x.inst).law x.rho (x.kernel ζ) h C vs) A =
        if A (x.final ζ h.length C vs.length) then 1 else 0 := by
  intro vs
  induction vs with
  | nil =>
    intro h C
    simp only [Instance.law, Instance.event, Distribution.mean_pure]
    congr
  | cons V vs ih =>
    intro h C
    simp only [Instance.law, Instance.event, Distribution.mean_bind, kernel,
      Distribution.mean_pure, List.length_cons, final]
    exact ih _ _

/-- A response covering a new element passes the local dual test with `ρ = n`. -/
theorem certified_of_new {C : Finset (Fin x.size)} {i : Fin x.size} {e : ℕ}
    (he : e ∈ (x.inst).sets i) (hC : e ∉ (x.inst).covered C) :
    (x.inst).Certified x.rho C {i} := by
  have hcov : (x.inst).covered {i} = (x.inst).sets i := by simp [Instance.covered]
  have hnew : ((x.inst).covered {i} \ (x.inst).covered C).Nonempty :=
    ⟨e, by rw [Finset.mem_sdiff, hcov]; exact ⟨he, hC⟩⟩
  refine ⟨hnew, ?_⟩
  have hsub : (x.inst).covered {i} \ (x.inst).covered C ⊆ x.ground.toFinset :=
    fun a ha => (x.inst).sets_subset i (by rw [← hcov]; exact (Finset.mem_sdiff.1 ha).1)
  have hpos : (0 : ℝ) < x.ground.toFinset.card := by
    exact_mod_cast Finset.card_pos.2 (hnew.mono hsub)
  have hone : (1 : ℝ) ≤ ((x.inst).covered {i} \ (x.inst).covered C).card := by
    exact_mod_cast Finset.card_pos.2 hnew
  simp only [Instance.cost, Finset.sum_singleton, rho]
  change (1 : ℝ) ≤ _ * ∑ _e ∈ _, 1 / (x.ground.toFinset.card : ℝ)
  rw [Finset.sum_const, nsmul_eq_mul]
  calc (1 : ℝ) ≤ _ := hone
    _ = _ := by field_simp

/-- Retaining a deterministic singleton response adds exactly its set. -/
theorem covered_step_singleton (C : Finset (Fin x.size)) (i : Fin x.size) :
    (x.inst).covered ((x.inst).step x.rho C {i}) = (x.inst).covered C ∪ (x.inst).sets i := by
  classical
  have hcov : (x.inst).covered {i} = (x.inst).sets i := by simp [Instance.covered]
  unfold Instance.step
  split_ifs with hc
  · rw [(x.inst).covered_union, hcov]
  · refine (Finset.union_eq_left.2 fun e he => ?_).symm
    by_contra hC
    exact hc (x.certified_of_new he hC)

theorem covered_response (ζ : List ℕ) (k : ℕ) :
    (x.inst).covered (x.response ζ k) =
      ((x.calls ζ)[k]?).elim ∅ fun i => (x.inst).sets i := by
  unfold response
  cases (x.calls ζ)[k]? <;> simp [Instance.covered]

theorem covered_step_response (ζ : List ℕ) (C : Finset (Fin x.size)) (k : ℕ) :
    (x.inst).covered ((x.inst).step x.rho C (x.response ζ k)) =
      (x.inst).covered C ∪ (x.inst).covered (x.response ζ k) := by
  classical
  unfold response
  cases (x.calls ζ)[k]? with
  | none =>
    simp only [Option.elim_none]
    unfold Instance.step
    split_ifs <;> simp [Instance.covered]
  | some i =>
    simp only [Option.elim_some]
    rw [x.covered_step_singleton]
    simp [Instance.covered]

theorem mem_covered_final (ζ : List ℕ) (e : ℕ) : ∀ (n k : ℕ) (C : Finset (Fin x.size)),
    e ∈ (x.inst).covered (x.final ζ k C n) ↔
      e ∈ (x.inst).covered C ∨ ∃ j < n, e ∈ (x.inst).covered (x.response ζ (k + j)) := by
  intro n
  induction n with
  | zero => intro k C; simp [final]
  | succ n ih =>
    intro k C
    rw [final, ih, x.covered_step_response, Finset.mem_union]
    constructor
    · rintro ((h | h) | ⟨j, hj, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0, by omega, by simpa using h⟩
      · exact Or.inr ⟨j + 1, by omega, by rwa [show k + (j + 1) = k + 1 + j by omega]⟩
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases j with _ | j
        · exact Or.inl (Or.inr (by simpa using h))
        · exact Or.inr ⟨j, by omega, by rwa [show k + 1 + j = k + (j + 1) by omega]⟩

theorem mem_calls (ζ : List ℕ) (i : Fin x.size) : i ∈ x.calls ζ ↔ 0 < ζ.getD (i : ℕ) 0 := by
  simp only [calls, List.mem_flatMap, List.mem_finRange, List.mem_replicate, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact Nat.pos_of_ne_zero hj
  · intro h; exact ⟨i, h.ne', rfl⟩

/-- The retained family covers exactly the ground elements of the queried sets. -/
theorem mem_covered_final_calls (ζ : List ℕ) (e : ℕ) :
    e ∈ (x.inst).covered (x.final ζ 0 ∅ (x.calls ζ).length) ↔
      e ∈ x.ground ∧ ∃ i : Fin x.size, 0 < ζ.getD (i : ℕ) 0 ∧ e ∈ x.oracles[i] := by
  rw [x.mem_covered_final]
  simp only [Instance.covered, Finset.biUnion_empty, Finset.notMem_empty, false_or, zero_add]
  constructor
  · rintro ⟨j, hj, he⟩
    have hj' : (x.calls ζ)[j]? = some (x.calls ζ)[j] := List.getElem?_eq_getElem hj
    have hc := x.covered_response ζ j
    simp only [Instance.covered] at hc
    rw [hc, hj', Option.elim_some] at he
    have hm := (x.mem_calls ζ (x.calls ζ)[j]).1 (List.getElem_mem hj)
    simp only [inst, Finset.mem_filter, List.mem_toFinset] at he
    exact ⟨he.2, _, hm, he.1⟩
  · rintro ⟨hg, i, hi, he⟩
    obtain ⟨j, hj, hji⟩ := List.getElem_of_mem ((x.mem_calls ζ i).2 hi)
    refine ⟨j, hj, ?_⟩
    have hc := x.covered_response ζ j
    simp only [Instance.covered] at hc
    rw [hc, List.getElem?_eq_getElem hj, Option.elim_some, hji]
    simpa [inst, hg] using he

open scoped Classical in
/-- **Deterministic success.** The actual one-turn retention law succeeds with
probability one exactly when the queried sets cover the ground set, and otherwise
with probability zero. -/
theorem success_eq (ζ : List ℕ) :
    x.success ζ = if x.Covers ζ then 1 else 0 := by
  classical
  unfold success
  rw [x.event_law, List.length_nil, eligible, List.length_map]
  congr 1
  apply propext
  constructor
  · intro h e he
    have hm : e ∈ (x.inst).covered (x.final ζ 0 ∅ (x.calls ζ).length) := by
      rw [h]; simpa [inst] using he
    exact ((x.mem_covered_final_calls ζ e).1 hm).2
  · intro h
    apply Finset.Subset.antisymm
    · intro e he
      have := ((x.mem_covered_final_calls ζ e).1 he).1
      simpa [inst] using this
    · intro e he
      have he' : e ∈ x.ground := by simpa [inst] using he
      exact (x.mem_covered_final_calls ζ e).2 ⟨he', h e he'⟩

theorem one_le_success_iff (ζ : List ℕ) : 1 ≤ x.success ζ ↔ x.Covers ζ := by
  classical
  rw [x.success_eq]; split_ifs with h <;> simp [h]

/-- These oracles satisfy Theorem 4's joint local-certification/coverage guarantee
with `p = 1`, at every reached history of the fixed processing order. -/
theorem admissible (ζ : List ℕ) :
    (x.inst).Admissible x.rho 1 (x.kernel ζ) [] ∅ (x.eligible ζ) := by
  classical
  suffices H : ∀ (n k : ℕ) (h : List (Finset (Fin x.size))) (C : Finset (Fin x.size)),
      h.length = k → (x.eligible ζ).drop k = (x.eligible ζ).drop k →
      n = ((x.eligible ζ).drop k).length →
      (x.inst).Admissible x.rho 1 (x.kernel ζ) h C ((x.eligible ζ).drop k) by
    simpa using H _ 0 [] ∅ rfl rfl rfl
  intro n
  induction n with
  | zero =>
    intro k h C _ _ hn
    rw [List.eq_nil_of_length_eq_zero hn.symm]
    trivial
  | succ n ih =>
    intro k h C hk _ hn
    have hlt : k < (x.calls ζ).length := by
      have : 0 < ((x.eligible ζ).drop k).length := by omega
      simpa [eligible] using this
    have hdrop : (x.eligible ζ).drop k =
        (x.inst).sets (x.calls ζ)[k] :: (x.eligible ζ).drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa [eligible] using hlt)]
      simp [eligible]
    have hresp : x.response ζ k = {(x.calls ζ)[k]} := by
      simp [response, List.getElem?_eq_getElem hlt]
    rw [hdrop]
    refine ⟨fun e he hC => ?_, fun P hP => ?_⟩
    · simp only [kernel, hk, hresp, Instance.event, Distribution.mean_pure]
      have hc := x.certified_of_new he hC
      have hm : e ∈ (x.inst).covered {(x.calls ζ)[k]} := by simpa [Instance.covered] using he
      simp [hc, hm]
    · have hP' : P = x.response ζ k := by
        by_contra hne
        simp [kernel, hk, Distribution.pure, hne] at hP
      subst hP'
      exact ih (k + 1) _ _ (by simp [hk]) rfl (by simp at hn ⊢; omega)

/-- Valid inputs: every ground element is returned by some oracle. -/
def Valid : Prop := ∀ e ∈ x.ground, ∃ V ∈ x.oracles, e ∈ V

theorem exists_feasible (hx : x.Valid) : ∃ ζ, 1 ≤ x.success ζ := by
  refine ⟨List.replicate x.size 1, (x.one_le_success_iff _).2 fun e he => ?_⟩
  obtain ⟨V, hV, heV⟩ := hx e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hV
  exact ⟨⟨i, hi⟩, by simp [List.getD_eq_getElem?_getD, hi], heV⟩

open scoped Classical in
/-- Minimum token cost of a successful one-turn batch; zero on invalid inputs. -/
def optTokens : ℕ :=
  if h : ∃ k ζ, 1 ≤ x.success ζ ∧ x.tokens ζ = k then Nat.find h else 0

theorem optTokens_le {ζ : List ℕ} (hζ : 1 ≤ x.success ζ) : x.optTokens ≤ x.tokens ζ := by
  classical
  have h : ∃ k ζ, 1 ≤ x.success ζ ∧ x.tokens ζ = k := ⟨_, ζ, hζ, rfl⟩
  simp only [optTokens, h, ↓reduceDIte]
  exact Nat.find_min' h ⟨ζ, hζ, rfl⟩

theorem exists_optTokens (hx : x.Valid) : ∃ ζ, 1 ≤ x.success ζ ∧ x.tokens ζ = x.optTokens := by
  classical
  obtain ⟨ζ, hζ⟩ := x.exists_feasible hx
  have h : ∃ k ζ, 1 ≤ x.success ζ ∧ x.tokens ζ = k := ⟨_, ζ, hζ, rfl⟩
  simp only [optTokens, h, ↓reduceDIte]
  exact Nat.find_spec h

end Selection

/-- **Minimum-token one-turn partial-cover selection** on deterministic oracle tables:
feasible call vectors certify a cover with probability at least $\eta = 1$ under the
actual retention law, and cost their token bill $c(\zeta)$. -/
def minSelection : MinOptProblem Selection (List ℕ) where
  IsValid := Selection.Valid
  Feasible x ζ := 1 ≤ x.success ζ
  cost x ζ := (x.tokens ζ : ℝ)
  opt x := (x.optTokens : ℝ)
  opt_le x _ _ hζ := by exact_mod_cast x.optTokens_le hζ
  exists_opt x hx := by
    obtain ⟨ζ, hζ, he⟩ := x.exists_optTokens hx
    exact ⟨ζ, hζ, by exact_mod_cast he⟩

/-! ### The reduction from Set Cover -/

/-- Oracle `i` returns the `i`th candidate set at unit token cost. -/
def ofSetSystem (S : SetSystem) : Selection := ⟨S.ground, S.sets, S.sets.map fun _ => 1⟩

/-- Read back the indices of queried oracles, i.e. those with a positive call count. -/
def queried (S : SetSystem) (ζ : List ℕ) : List ℕ :=
  (((ζ.take S.sets.length).zipIdx).filter fun q => q.1 != 0).map Prod.snd

/-- The instance map of the reduction runs in polynomial time. -/
theorem computable_ofSetSystem : ComputableInPolyTime ofSetSystem encSetSystem encSelection := by
  unfold ofSetSystem
  refine encSelection_mk_deg.computableInPolyTime.comp
    (computableInPolyTime_setSystemGround.prod (computableInPolyTime_setSystemSets.prod ?_))
  exact (ComputableInPolyTime.map (ComputableInPolyTime.const 1)).comp
    computableInPolyTime_setSystemSets

/-- Reading back the queried oracles runs in polynomial time. -/
theorem computable_queried : ComputableInPolyTime (fun p : SetSystem × List ℕ => queried p.1 p.2)
    (encPair encSetSystem (encList encNat)) (encList encNat) := by
  unfold queried
  fun_prop

theorem mem_queried (S : SetSystem) (ζ : List ℕ) (i : ℕ) :
    i ∈ queried S ζ ↔ i < S.sets.length ∧ 0 < ζ.getD i 0 := by
  simp only [queried, List.mem_map, List.mem_filter, bne_iff_ne, ne_eq, Prod.exists,
    exists_eq_right, List.mem_zipIdx_iff_getElem?, List.getElem?_take]
  by_cases hi : i < S.sets.length
  · simp only [hi, ↓reduceIte, true_and, List.getD_eq_getElem?_getD]
    cases ζ[i]? <;> simp [Nat.pos_iff_ne_zero]
  · simp [hi]

/-- Filtering positive entries never exceeds the sum. -/
private theorem length_filter_le_sum (l : List ℕ) :
    (l.filter fun i => i != 0).length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = 0
    · simp [h, ih]
    · simp only [List.filter_cons, h, bne_iff_ne, ne_eq, not_false_eq_true,
        ↓reduceIte, List.length_cons, List.sum_cons]
      omega

private theorem length_filter_zipIdx (l : List ℕ) (k : ℕ) :
    ((l.zipIdx k).filter fun q => q.1 != 0).length = (l.filter fun i => i != 0).length := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.filter_cons, List.filter_cons]
    split_ifs <;> simp [ih]

private theorem sum_take (ζ : List ℕ) (m : ℕ) :
    (ζ.take m).sum = ((List.range m).map fun i => ζ.getD i 0).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.take_add_one, List.sum_append, ih, List.range_succ, List.map_append, List.sum_append]
    cases h : ζ[m]? <;> simp [List.getD_eq_getElem?_getD, h]

private theorem sum_indicator (l : List ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (l.map fun i => if p i then 1 else 0).sum = (l.filter fun i => decide (p i)).length := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih, add_comm]

theorem tokens_ofSetSystem (S : SetSystem) (ζ : List ℕ) :
    (ofSetSystem S).tokens ζ = ((List.range S.sets.length).map fun i => ζ.getD i 0).sum := by
  unfold Selection.tokens
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi : i < S.sets.length := List.mem_range.1 hi
  simp [ofSetSystem, List.getD_eq_getElem?_getD, hi]

theorem length_queried_le (S : SetSystem) (ζ : List ℕ) :
    (queried S ζ).length ≤ (ofSetSystem S).tokens ζ := by
  rw [tokens_ofSetSystem, ← sum_take, queried, List.length_map, length_filter_zipIdx]
  exact length_filter_le_sum _

theorem valid_ofSetSystem_iff (S : SetSystem) : (ofSetSystem S).Valid ↔ S.Coverable := by
  rw [← SetSystem.coverableBool_eq_true_iff]
  simp [Selection.Valid, SetSystem.coverableBool, ofSetSystem]

theorem covers_ofSetSystem_iff (S : SetSystem) (ζ : List ℕ) :
    (ofSetSystem S).Covers ζ ↔ S.isCoverList (queried S ζ) = true := by
  rw [SetSystem.isCoverList_eq_true_iff]
  constructor
  · intro h
    refine ⟨fun i hi => ((mem_queried S ζ i).1 hi).1, fun u hu => ?_⟩
    obtain ⟨i, hi, hu⟩ := h u hu
    exact ⟨i, (mem_queried S ζ i).2 ⟨i.isLt, hi⟩, i.isLt, hu⟩
  · rintro ⟨-, h⟩ u hu
    obtain ⟨i, hiq, hi, hu⟩ := h u hu
    exact ⟨⟨i, hi⟩, ((mem_queried S ζ i).1 hiq).2, hu⟩

/-- The paper's reduction preserves the optimum: minimum token cost equals the
minimum Set Cover size. -/
theorem optTokens_ofSetSystem (S : SetSystem) (hS : S.Coverable) :
    (ofSetSystem S).optTokens = S.optCoverSize := by
  classical
  have hv := (valid_ofSetSystem_iff S).2 hS
  apply le_antisymm
  · obtain ⟨I, hI, hlen⟩ := minSetCover.exists_opt S hS
    let ζ := (List.range S.sets.length).map fun i => if i ∈ I then 1 else 0
    have hget (i : ℕ) (hi : i < S.sets.length) : ζ.getD i 0 = if i ∈ I then 1 else 0 := by
      simp [ζ, List.getD_eq_getElem?_getD, hi]
    have hcov : (ofSetSystem S).Covers ζ := by
      intro u hu
      obtain ⟨i, hiI, hi, hui⟩ := ((S.isCoverList_eq_true_iff I).1 hI).2 u hu
      refine ⟨⟨i, hi⟩, ?_, hui⟩
      change 0 < ζ.getD i 0
      rw [hget i hi]
      simp [hiI]
    refine ((ofSetSystem S).optTokens_le (((ofSetSystem S).one_le_success_iff ζ).2 hcov)).trans ?_
    rw [tokens_ofSetSystem]
    have hsum : ((List.range S.sets.length).map fun i => ζ.getD i 0).sum =
        ((List.range S.sets.length).filter fun i => decide (i ∈ I)).length := by
      rw [← sum_indicator]
      congr 1
      exact List.map_congr_left fun i hi => hget i (List.mem_range.1 hi)
    have hnd : ((List.range S.sets.length).filter fun i => decide (i ∈ I)).Nodup :=
      (List.nodup_range).filter _
    rw [hsum, ← List.toFinset_card_of_nodup hnd]
    have hlen' : I.length = S.optCoverSize := by
      change (I.length : ℝ) = S.optCoverSize at hlen
      exact_mod_cast hlen
    rw [← hlen']
    refine (Finset.card_le_card fun i hi => ?_).trans (List.toFinset_card_le I)
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi ⊢
    exact hi.2
  · obtain ⟨ζ, hζ, he⟩ := (ofSetSystem S).exists_optTokens hv
    have hI := (covers_ofSetSystem_iff S ζ).1 (((ofSetSystem S).one_le_success_iff ζ).1 hζ)
    have h1 := minSetCover.opt_le S (queried S ζ) hS hI
    have h2 := length_queried_le S ζ
    change (S.optCoverSize : ℝ) ≤ (queried S ζ).length at h1
    rw [← he]
    exact (by exact_mod_cast h1 : S.optCoverSize ≤ (queried S ζ).length).trans h2

/-- **Set Cover reduces approximation-preservingly to minimum-token one-turn
partial-cover selection**, with identity ratio transformation. -/
theorem approxPreservingReducible_setCover_selection :
    ApproxPreservingReducible minSetCover minSelection encSetSystem encSelection
      (encList encNat) (encList encNat) (fun _ ρ => ρ) := by
  refine ⟨ofSetSystem, queried, computable_ofSetSystem, computable_queried,
    fun S hS => (valid_ofSetSystem_iff S).2 hS,
    fun S ζ _ hζ => (covers_ofSetSystem_iff S ζ).1
      (((ofSetSystem S).one_le_success_iff ζ).1 hζ), fun S ρ ζ hS _ hcost => ?_⟩
  change ((queried S ζ).length : ℝ) ≤ ρ * (S.optCoverSize : ℝ)
  change ((ofSetSystem S).tokens ζ : ℝ) ≤ ρ * ((ofSetSystem S).optTokens : ℝ) at hcost
  rw [optTokens_ofSetSystem S hS] at hcost
  exact (by exact_mod_cast length_queried_le S ζ : ((queried S ζ).length : ℝ) ≤ _).trans hcost

/-- If `GapSetCover r` is `NP`-hard, a polynomial-time `ρ`-approximation (`0 ≤ ρ < r`)
for minimum-token one-turn partial-cover selection implies `P = NP`. -/
theorem P_eq_NP_of_selection_approx {A : Selection → List ℕ} {ρ r : ℝ}
    (hhard : PromiseProblem.NPHard encSetCover (GapSetCover r)) (hρ0 : 0 ≤ ρ) (hρ : ρ < r)
    (hA : ComputableInPolyTime A encSelection (encList encNat))
    (happrox : minSelection.IsApprox (fun _ => ρ) A) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc := by
  obtain ⟨A₁, hA₁, happrox₁⟩ :=
    approxPreservingReducible_setCover_selection.comp_isApprox hA happrox
  exact P_eq_NP_of_setCover_approx hhard hρ0 hρ hA₁ happrox₁ enc

/-- **Hardness transfer for [Wang2027], p. 11.** Unless `P = NP`, minimum-token one-turn
partial-cover selection has no polynomial-time constant-factor approximation, from the
library's unconditional Lund–Yannakakis/Feige constant-factor Set Cover hardness. The
source's $(1-\varepsilon)\ln n$ factor additionally needs Dinur–Steurer (#4335). -/
theorem P_eq_NP_of_selection_approx_const {A : Selection → List ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hA : ComputableInPolyTime A encSelection (encList encNat))
    (happrox : minSelection.IsApprox (fun _ => c) A) {α : Type} (enc : α ↪ List Bool) :
    P enc = NP enc :=
  P_eq_NP_of_selection_approx (GapSetCover_npHard (by linarith : 1 < c + 2)) hc0
    (by linarith : c < c + 2) hA happrox enc

end Cslib.Probability.StochasticOracle.PartialCover.Hardness
