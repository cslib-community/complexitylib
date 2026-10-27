/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.LowDegree
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared
public import Complexity.Logics.Propositional.CNF.ParityTests
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.ZMod.Basic
import Complexity.Foundations.Data.BitString.ZModTwo

/-!
# Polynomial compilation of CNF parity tests over `𝔽₂`

For a propositional clause `c : Clause V`, its violation bit `!c.eval σ` on an assignment
`σ : V → Bool` expands over `𝔽₂ = ZMod 2` into a multilinear sum of monomials
(`Cslib.Logic.PL.Clause.falsifyMonomials`): a tautological clause expands to `∅` (`0`), the empty
clause expands to `{∅}` (`1`), and a nontautological clause with positive variables `P` and
negative variables `N` expands to `{S ∪ N | S ⊆ P}`, using the identity
`∏_{v ∈ P} (1 + x_v) ∏_{v ∈ N} x_v = ∑_{S ⊆ P} ∏_{v ∈ S ∪ N} x_v` over `ZMod 2`. Repeated literals
within `c` collapse automatically, so every monomial has support in `(c.map Prod.fst).toFinset`
and degree at most `c.length`, and there are at most `2 ^ c.length` monomials.

Given a formula `φ : CNF V` with `m = φ.length` clauses and a binary parity-check row
`r : Fin φ.length → Bool`, equation (6.1) of [OpenAI2026ETH] specifies the `𝔽₂` polynomial equation
`P_r(σ) = ∑_{e : r e = true} v_e(σ) = 0`. Retaining the monomials that occur in an odd number of
active clauses (`Cslib.Logic.PL.CNF.parityRowMonomials`) cancels duplicate monomials modulo `2`:
adding rows in the Boolean ring corresponds to taking the symmetric difference of their monomial
sets (`Cslib.Logic.PL.CNF.parityRowMonomials_add`), evaluating the compiled monomial sum agrees
with the parity check `∑ e, r e * φ.violations σ e` (`Cslib.Logic.PL.CNF.sum_parityRowMonomials`),
and when every clause has length at most `k`, each retained monomial has degree at most `k` and
there are at most `weight r * 2 ^ k` monomials (`≤ P * 2 ^ k` for `r = testRow γ` of length `P`).

On a finite variable type `V`, the common zeros of `{φ.parityRowMonomials r | r ∈ rows}` are
therefore the assignments accepted by `PassesTests φ.violations rows`, decomposing as
`numPassing φ.violations rows = φ.modelCountOn Finset.univ + D(rows)` where `D(rows)` counts
accepted nonsatisfying assignments, and equaling `φ.modelCountOn Finset.univ` after the
`3 * Fintype.card V` greedy rounds of `CNF.numPassing_greedy` [OpenAI2026ETH, Lemma 6.2, §6.3].

## Main definitions

* `Cslib.Logic.PL.Clause.falsifyMonomials`: canonical `𝔽₂` multilinear monomial set of `!c.eval`.
* `Cslib.Logic.PL.CNF.parityRowMonomials`: mod-`2` cancelled `𝔽₂` monomial set of a parity row on
  clause violations.

## Main results

* `Cslib.Logic.PL.Clause.sum_falsifyMonomials`: semantic agreement of `Clause.falsifyMonomials`
  with `bitVal (ZMod 2) (!c.eval σ)`.
* `Cslib.Logic.PL.Clause.subset_vars_of_mem_falsifyMonomials`,
  `Cslib.Logic.PL.Clause.card_le_length_of_mem_falsifyMonomials`,
  `Cslib.Logic.PL.Clause.card_falsifyMonomials_le`: support, degree, and `2 ^ c.length` sparsity
  bounds for one clause.
* `Cslib.Logic.PL.CNF.sum_parityRowMonomials`,
  `Cslib.Logic.PL.CNF.sum_parityRowMonomials_eq_zero_iff`: semantic agreement of a compiled parity
  row with `∑ e, r e * φ.violations σ e`.
* `Cslib.Logic.PL.CNF.parityRowMonomials_add`: mod-`2` symmetric-difference cancellation across
  added parity rows.
* `Cslib.Logic.PL.CNF.card_parityRowMonomials_le`,
  `Cslib.Logic.PL.CNF.card_parityRowMonomials_testRow_le`: sparsity bounds `weight r * 2 ^ k` and
  `P * 2 ^ k`.
* `Cslib.Logic.PL.CNF.commonZero_parityRowMonomials_iff_passesTests`,
  `Cslib.Logic.PL.CNF.numPassing_violations_eq_modelCountOn_add`,
  `Cslib.Logic.PL.CNF.card_commonZeros_greedy`,
  `Cslib.Logic.PL.CNF.greedy_system_bounds`: common-zero equivalence, `N(A) = #F + D(A)`
  decomposition, exact `CNF.modelCountOn Finset.univ` recovery after `3 n` greedy rounds, and
  candidate-system size, degree, and sparsity bounds.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6 (eq. 6.1), §6.2
  (Lemma 6.2), and §6.3, pp. 39–40, 42–43
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Cslib.BitString

variable {V : Type*}

/-! ### Clause-falsification monomials over `ZMod 2` -/

section Clause

variable [DecidableEq V]

/-- The canonical multilinear `𝔽₂` monomials whose sum evaluates to `!c.eval σ` over `ZMod 2`.
If some variable occurs both positively and negatively in `c`, the clause is tautological and the
set is empty; otherwise it consists of `S ∪ neg` as `S` ranges over subsets of the positive
variables `pos` of `c`, expanding `∏_{v ∈ pos} (1 + x_v) ∏_{v ∈ neg} x_v` modulo `2`. -/
def Clause.falsifyMonomials (c : Clause V) : Finset (Finset V) :=
  let pos := (c.map Prod.fst).toFinset.filter fun v => (v, true) ∈ c
  let neg := (c.map Prod.fst).toFinset.filter fun v => (v, false) ∈ c
  if Disjoint pos neg then
    pos.powerset.image fun S => S ∪ neg
  else
    ∅

/-- The empty clause is always falsified, so its falsification polynomial is the constant `1`
(`{∅}`). -/
@[simp] theorem Clause.falsifyMonomials_nil :
    Clause.falsifyMonomials ([] : Clause V) = {∅} := by
  simp [Clause.falsifyMonomials]

/-- A tautological clause containing both `(v, true)` and `(v, false)` has empty falsification
monomial set. -/
theorem Clause.falsifyMonomials_eq_empty_of_tautology {c : Clause V} {v : V}
    (hpos : (v, true) ∈ c) (hneg : (v, false) ∈ c) :
    c.falsifyMonomials = ∅ := by
  dsimp only [Clause.falsifyMonomials]
  have hv_vars : v ∈ (c.map Prod.fst).toFinset :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨(v, true), hpos, rfl⟩)
  have hndisj : ¬ Disjoint
      ((c.map Prod.fst).toFinset.filter fun u => (u, true) ∈ c)
      ((c.map Prod.fst).toFinset.filter fun u => (u, false) ∈ c) :=
    Finset.not_disjoint_iff.mpr
      ⟨v, Finset.mem_filter.mpr ⟨hv_vars, hpos⟩, Finset.mem_filter.mpr ⟨hv_vars, hneg⟩⟩
  simp only [hndisj, ↓reduceIte]

/-- Every monomial in `c.falsifyMonomials` uses only variables occurring in `c`. -/
theorem Clause.subset_vars_of_mem_falsifyMonomials {c : Clause V} {M : Finset V}
    (hM : M ∈ c.falsifyMonomials) : M ⊆ (c.map Prod.fst).toFinset := by
  dsimp only [Clause.falsifyMonomials] at hM
  split_ifs at hM with hdisj
  · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hM
    exact Finset.union_subset
      ((Finset.mem_powerset.mp hS).trans (Finset.filter_subset _ _))
      (Finset.filter_subset _ _)
  · simp at hM

/-- Every monomial in `c.falsifyMonomials` has degree at most the number of distinct variables in
`c`. -/
theorem Clause.card_le_card_vars_of_mem_falsifyMonomials {c : Clause V} {M : Finset V}
    (hM : M ∈ c.falsifyMonomials) : #M ≤ (c.map Prod.fst).toFinset.card :=
  Finset.card_le_card (Clause.subset_vars_of_mem_falsifyMonomials hM)

/-- Every monomial in `c.falsifyMonomials` has degree at most `c.length`. -/
theorem Clause.card_le_length_of_mem_falsifyMonomials {c : Clause V} {M : Finset V}
    (hM : M ∈ c.falsifyMonomials) : #M ≤ c.length :=
  (Clause.card_le_card_vars_of_mem_falsifyMonomials hM).trans
    ((List.toFinset_card_le _).trans_eq (List.length_map _))

/-- A clause on `d` distinct variables expands to at most `2 ^ d` falsification monomials. -/
theorem Clause.card_falsifyMonomials_le_two_pow_card_vars (c : Clause V) :
    #c.falsifyMonomials ≤ 2 ^ (c.map Prod.fst).toFinset.card := by
  dsimp only [Clause.falsifyMonomials]
  split_ifs with hdisj
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_powerset]
    exact Nat.pow_le_pow_right (by positivity) (Finset.card_filter_le _ _)
  · simp

/-- A clause `c` expands to at most `2 ^ c.length` falsification monomials. -/
theorem Clause.card_falsifyMonomials_le (c : Clause V) :
    #c.falsifyMonomials ≤ 2 ^ c.length :=
  (Clause.card_falsifyMonomials_le_two_pow_card_vars c).trans
    (Nat.pow_le_pow_right (by positivity)
      ((List.toFinset_card_le _).trans_eq (List.length_map _)))

/-- **Clause-falsification polynomial identity over `𝔽₂`** [OpenAI2026ETH, §6]. For every clause
`c` and truth assignment `σ`, the sum over `c.falsifyMonomials` in `ZMod 2` equals the violation
bit `!c.eval σ` read in `ZMod 2`. -/
theorem Clause.sum_falsifyMonomials (c : Clause V) (σ : V → Bool) :
    ∑ M ∈ c.falsifyMonomials, monomial (ZMod 2) M σ = bitVal (ZMod 2) (!c.eval σ) := by
  let vars := (c.map Prod.fst).toFinset
  let pos := vars.filter fun v => (v, true) ∈ c
  let neg := vars.filter fun v => (v, false) ∈ c
  have hmem_pos : ∀ {v : V}, v ∈ pos ↔ (v, true) ∈ c := fun {v} =>
    ⟨fun h => (Finset.mem_filter.mp h).2, fun h =>
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨(v, true), h, rfl⟩), h⟩⟩
  have hmem_neg : ∀ {v : V}, v ∈ neg ↔ (v, false) ∈ c := fun {v} =>
    ⟨fun h => (Finset.mem_filter.mp h).2, fun h =>
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨(v, false), h, rfl⟩), h⟩⟩
  change ∑ M ∈ (if Disjoint pos neg then pos.powerset.image fun S => S ∪ neg else ∅),
      monomial (ZMod 2) M σ = bitVal (ZMod 2) (!c.eval σ)
  split_ifs with hdisj
  · have hinj : Set.InjOn (fun S : Finset V => S ∪ neg) pos.powerset := by
      intro S₁ hS₁ S₂ hS₂ heq
      dsimp only at heq
      have hS₁' : S₁ ⊆ pos := Finset.mem_powerset.mp (Finset.mem_coe.mp hS₁)
      have hS₂' : S₂ ⊆ pos := Finset.mem_powerset.mp (Finset.mem_coe.mp hS₂)
      ext v
      constructor
      · intro hv
        have hv_un : v ∈ S₂ ∪ neg := by
          rw [← heq]
          exact Finset.mem_union_left _ hv
        exact (Finset.mem_union.mp hv_un).resolve_right
          (Finset.disjoint_left.mp hdisj (hS₁' hv))
      · intro hv
        have hv_un : v ∈ S₁ ∪ neg := by
          rw [heq]
          exact Finset.mem_union_left _ hv
        exact (Finset.mem_union.mp hv_un).resolve_right
          (Finset.disjoint_left.mp hdisj (hS₂' hv))
    rw [Finset.sum_image hinj]
    have hmul : ∀ S ∈ pos.powerset,
        monomial (ZMod 2) (S ∪ neg) σ = monomial (ZMod 2) S σ * monomial (ZMod 2) neg σ := by
      intro S _
      simpa only [Pi.mul_apply] using congrFun (monomial_mul (R := ZMod 2) S neg).symm σ
    rw [Finset.sum_congr rfl hmul, ← Finset.sum_mul]
    let posTrue := pos.filter fun v => σ v = true
    have hpos_sum : ∑ S ∈ pos.powerset, monomial (ZMod 2) S σ =
        if ∀ v ∈ pos, σ v = false then 1 else 0 := by
      have hfilt : (pos.powerset.filter fun S => ∀ v ∈ S, σ v = true) = posTrue.powerset := by
        ext S
        simp only [posTrue, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨fun ⟨hSp, hSσ⟩ v hv => Finset.mem_filter.mpr ⟨hSp hv, hSσ v hv⟩,
          fun hS => ⟨fun v hv => (Finset.mem_filter.mp (hS hv)).1,
            fun v hv => (Finset.mem_filter.mp (hS hv)).2⟩⟩
      simp only [monomial_apply, Finset.sum_boole, hfilt, Finset.card_powerset]
      split_ifs with hall
      · have hempty : posTrue = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro v hv
          obtain ⟨hvp, hvσ⟩ := Finset.mem_filter.mp hv
          rw [hall v hvp] at hvσ
          exact Bool.false_ne_true hvσ
        simp [hempty]
      · push Not at hall
        obtain ⟨v, hvp, hvσ⟩ := hall
        have hne : #posTrue ≠ 0 := Finset.card_ne_zero.mpr
          ⟨v, Finset.mem_filter.mpr ⟨hvp, Bool.eq_true_of_not_eq_false hvσ⟩⟩
        rw [Nat.cast_pow, ZMod.natCast_self, zero_pow hne]
    rw [hpos_sum, monomial_apply]
    have hfals : c.eval σ = false ↔
        (∀ v ∈ pos, σ v = false) ∧ (∀ v ∈ neg, σ v = true) := by
      rw [← Bool.not_eq_true, Clause.eval_eq_true_iff]
      constructor
      · intro h
        refine ⟨fun v hv => ?_, fun v hv => ?_⟩
        · exact Bool.eq_false_iff.mpr fun hσ => h ⟨(v, true), hmem_pos.mp hv, hσ⟩
        · exact Bool.eq_true_of_not_eq_false fun hσ => h ⟨(v, false), hmem_neg.mp hv, hσ⟩
      · rintro ⟨hp, hn⟩ ⟨⟨v, b⟩, hl, hσ⟩
        cases b
        · rw [hn v (hmem_neg.mpr hl)] at hσ
          exact Bool.false_ne_true hσ.symm
        · rw [hp v (hmem_pos.mpr hl)] at hσ
          exact Bool.false_ne_true hσ
    split_ifs with hp hn
    · rw [hfals.mpr ⟨hp, hn⟩]
      decide
    · have hct : c.eval σ = true := Bool.eq_true_of_not_eq_false fun h => hn (hfals.mp h).2
      rw [hct]
      decide
    · have hct : c.eval σ = true := Bool.eq_true_of_not_eq_false fun h => hp (hfals.mp h).1
      rw [hct]
      decide
    · have hct : c.eval σ = true := Bool.eq_true_of_not_eq_false fun h => hp (hfals.mp h).1
      rw [hct]
      decide
  · rw [Finset.not_disjoint_iff] at hdisj
    obtain ⟨v, hvp, hvn⟩ := hdisj
    have hsat : c.eval σ = true := by
      rw [Clause.eval_eq_true_iff]
      cases hσ : σ v
      · exact ⟨(v, false), hmem_neg.mp hvn, hσ⟩
      · exact ⟨(v, true), hmem_pos.mp hvp, hσ⟩
    simp [hsat]

/-- The falsification polynomial of `c` vanishes at `σ` over `ZMod 2` if and only if `σ` satisfies
`c`. -/
theorem Clause.sum_falsifyMonomials_eq_zero_iff (c : Clause V) (σ : V → Bool) :
    ∑ M ∈ c.falsifyMonomials, monomial (ZMod 2) M σ = 0 ↔ c.eval σ = true := by
  rw [Clause.sum_falsifyMonomials]
  cases c.eval σ <;> decide

/-- The falsification polynomial of `c` has multilinear degree at most `c.length` over `ZMod 2`. -/
theorem Clause.sum_falsifyMonomials_mem_lowDegree (c : Clause V) :
    (fun σ => ∑ M ∈ c.falsifyMonomials, monomial (ZMod 2) M σ) ∈
      lowDegree (ZMod 2) V c.length := by
  have hfn : (fun σ => ∑ M ∈ c.falsifyMonomials, monomial (ZMod 2) M σ) =
      ∑ M ∈ c.falsifyMonomials, monomial (ZMod 2) M := by
    funext σ
    simp only [Finset.sum_apply]
  rw [hfn]
  exact sum_mem_lowDegree _ fun M hM =>
    monomial_mem_lowDegree (Clause.card_le_length_of_mem_falsifyMonomials hM)

end Clause

/-! ### Parity-check row compilation and mod-`2` cancellation -/

section ParityRow

variable [DecidableEq V]

/-- The canonical `𝔽₂` monomial set of the linear parity-check equation (6.1) for row
`r : Fin φ.length → Bool` on `φ : CNF V`: a monomial `M` is retained precisely when it belongs to
`(φ.get e).falsifyMonomials` for an odd number of active clauses `e` (`r e = true`), cancelling
duplicate monomials modulo `2`. -/
def CNF.parityRowMonomials (φ : CNF V) (r : Fin φ.length → Bool) : Finset (Finset V) :=
  (({e : Fin φ.length | r e = true} : Finset (Fin φ.length)).biUnion
    fun e => (φ.get e).falsifyMonomials).filter
    fun M => #{e : Fin φ.length | r e = true ∧ M ∈ (φ.get e).falsifyMonomials} % 2 = 1

/-- A monomial belongs to `φ.parityRowMonomials r` if and only if it appears in an odd number of
active clauses `e` with `r e = true`. -/
@[simp] theorem CNF.mem_parityRowMonomials {φ : CNF V} {r : Fin φ.length → Bool} {M : Finset V} :
    M ∈ φ.parityRowMonomials r ↔
      #{e : Fin φ.length | r e = true ∧ M ∈ (φ.get e).falsifyMonomials} % 2 = 1 := by
  simp only [CNF.parityRowMonomials, Finset.mem_filter, Finset.mem_biUnion, and_iff_right_iff_imp]
  intro hodd
  have hne : ({e : Fin φ.length | r e = true ∧ M ∈ (φ.get e).falsifyMonomials} :
      Finset _).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨e, he⟩ := hne
  obtain ⟨-, hr, hM⟩ := Finset.mem_filter.mp he
  exact ⟨e, ⟨Finset.mem_univ e, hr⟩, hM⟩

/-- The zero parity row compiles to the empty monomial set. -/
@[simp] theorem CNF.parityRowMonomials_zero (φ : CNF V) :
    φ.parityRowMonomials 0 = ∅ := by
  ext M
  simp [Bool.zero_eq_false]

/-- A unit parity row selecting only clause `e` compiles to `(φ.get e).falsifyMonomials`. -/
theorem CNF.parityRowMonomials_single (φ : CNF V) (e : Fin φ.length) :
    φ.parityRowMonomials (Pi.single e true) = (φ.get e).falsifyMonomials := by
  ext M
  rw [CNF.mem_parityRowMonomials]
  have hset : ({i : Fin φ.length |
      (Pi.single e true : Fin φ.length → Bool) i = true ∧
        M ∈ (φ.get i).falsifyMonomials} : Finset _) =
      if M ∈ (φ.get e).falsifyMonomials then {e} else ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i = e
    · subst hi
      simp only [Pi.single_eq_same, true_and]
      split_ifs with hM <;> simpa using hM
    · have h0 : (Pi.single e true : Fin φ.length → Bool) i = false :=
        Pi.single_eq_of_ne (M := fun _ => Bool) hi true
      rw [h0]
      split_ifs <;> simp [hi]
  rw [hset]
  split_ifs with hM <;> simpa using hM

/-- **Mod-`2` monomial cancellation across rows.** Adding two parity-check rows in the Boolean ring
takes the symmetric difference of their compiled monomial sets. -/
theorem CNF.parityRowMonomials_add (φ : CNF V) (r₁ r₂ : Fin φ.length → Bool) :
    φ.parityRowMonomials (r₁ + r₂) =
      symmDiff (φ.parityRowMonomials r₁) (φ.parityRowMonomials r₂) := by
  ext M
  rw [CNF.mem_parityRowMonomials, Finset.mem_symmDiff, CNF.mem_parityRowMonomials,
    CNF.mem_parityRowMonomials]
  let s₁ : Finset (Fin φ.length) :=
    {e : Fin φ.length | r₁ e = true ∧ M ∈ (φ.get e).falsifyMonomials}
  let s₂ : Finset (Fin φ.length) :=
    {e : Fin φ.length | r₂ e = true ∧ M ∈ (φ.get e).falsifyMonomials}
  have hs : ({e : Fin φ.length | (r₁ + r₂) e = true ∧ M ∈ (φ.get e).falsifyMonomials} :
      Finset _) = symmDiff s₁ s₂ := by
    ext e
    simp only [s₁, s₂, Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_univ, true_and,
      Pi.add_apply, Bool.add_eq_xor]
    cases r₁ e <;> cases r₂ e <;> simp
  rw [hs]
  change #(symmDiff s₁ s₂) % 2 = 1 ↔
    (#s₁ % 2 = 1 ∧ ¬#s₂ % 2 = 1 ∨ #s₂ % 2 = 1 ∧ ¬#s₁ % 2 = 1)
  have h1 := Finset.card_sdiff_add_card_inter s₁ s₂
  have h2 := Finset.card_sdiff_add_card_inter s₂ s₁
  rw [Finset.inter_comm] at h2
  have hsd : #(symmDiff s₁ s₂) = #(s₁ \ s₂) + #(s₂ \ s₁) := by
    rw [Finset.symmDiff_def]
    exact Finset.card_union_of_disjoint disjoint_sdiff_sdiff
  omega

/-- Every monomial in `φ.parityRowMonomials r` is supported on the variables of `φ`. -/
theorem CNF.subset_vars_of_mem_parityRowMonomials {φ : CNF V} {r : Fin φ.length → Bool}
    {M : Finset V} (hM : M ∈ φ.parityRowMonomials r) : M ⊆ φ.vars.toFinset := by
  dsimp only [CNF.parityRowMonomials] at hM
  obtain ⟨hU, -⟩ := Finset.mem_filter.mp hM
  obtain ⟨e, -, hMe⟩ := Finset.mem_biUnion.mp hU
  intro v hv
  have hv_c := Clause.subset_vars_of_mem_falsifyMonomials hMe hv
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv_c)
  exact List.mem_toFinset.mpr (CNF.mem_vars.mpr ⟨φ.get e, List.get_mem φ e, l.2, hl⟩)

/-- When every clause of `φ` has length at most `k`, every monomial in `φ.parityRowMonomials r` has
degree at most `k`. -/
theorem CNF.card_le_of_mem_parityRowMonomials {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {r : Fin φ.length → Bool} {M : Finset V}
    (hM : M ∈ φ.parityRowMonomials r) : #M ≤ k := by
  dsimp only [CNF.parityRowMonomials] at hM
  obtain ⟨hU, -⟩ := Finset.mem_filter.mp hM
  obtain ⟨e, -, hMe⟩ := Finset.mem_biUnion.mp hU
  exact (Clause.card_le_length_of_mem_falsifyMonomials hMe).trans (hk _ (List.get_mem φ e))

/-- When every clause of `φ` has length at most `k`, the compiled polynomial of row `r` has
multilinear degree at most `k` over `ZMod 2`. -/
theorem CNF.sum_parityRowMonomials_mem_lowDegree {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (r : Fin φ.length → Bool) :
    (fun σ => ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ) ∈
      lowDegree (ZMod 2) V k := by
  have hfn : (fun σ => ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ) =
      ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M := by
    funext σ
    simp only [Finset.sum_apply]
  rw [hfn]
  exact sum_mem_lowDegree _ fun M hM =>
    monomial_mem_lowDegree (CNF.card_le_of_mem_parityRowMonomials hk hM)

/-- **Sparsity of a compiled parity row** [OpenAI2026ETH, §6.2]. When every clause of `φ` has
length at most `k`, `φ.parityRowMonomials r` contains at most `weight r * 2 ^ k` monomials. -/
theorem CNF.card_parityRowMonomials_le {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (r : Fin φ.length → Bool) :
    #(φ.parityRowMonomials r) ≤ weight r * 2 ^ k := by
  calc #(φ.parityRowMonomials r)
      ≤ #( ({e : Fin φ.length | r e = true} : Finset (Fin φ.length)).biUnion
          fun e => (φ.get e).falsifyMonomials ) :=
        Finset.card_filter_le _ _
    _ ≤ ∑ e ∈ {e : Fin φ.length | r e = true}, #(φ.get e).falsifyMonomials :=
        Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ {e : Fin φ.length | r e = true}, 2 ^ k :=
        Finset.sum_le_sum fun e _ =>
          (Clause.card_falsifyMonomials_le (φ.get e)).trans
            (Nat.pow_le_pow_right (by positivity) (hk _ (List.get_mem φ e)))
    _ = weight r * 2 ^ k := by
        rw [Finset.sum_const, smul_eq_mul]
        rfl

/-- **Sparsity of a compiled test-list row** [OpenAI2026ETH, Lemma 6.2]. For any test list
`γ : Fin P → Fin φ.length × Bool` on a `k`-CNF formula `φ`, `φ.parityRowMonomials (testRow γ)`
contains at most `P * 2 ^ k` monomials. -/
theorem CNF.card_parityRowMonomials_testRow_le {φ : CNF V} {k P : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (γ : Fin P → Fin φ.length × Bool) :
    #(φ.parityRowMonomials (testRow γ)) ≤ P * 2 ^ k :=
  (CNF.card_parityRowMonomials_le hk (testRow γ)).trans
    (Nat.mul_le_mul_right _ (weight_testRow_le γ))

/-- **Compiled parity-row evaluation identity** [OpenAI2026ETH, eq. (6.1)]. Evaluating the sum of
`φ.parityRowMonomials r` at `σ` over `ZMod 2` equals the parity `∑ e, r e * φ.violations σ e` read
in `ZMod 2`. -/
theorem CNF.sum_parityRowMonomials (φ : CNF V) (r : Fin φ.length → Bool) (σ : V → Bool) :
    ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ =
      bitVal (ZMod 2) (∑ e : Fin φ.length, r e * φ.violations σ e) := by
  let s : Finset (Fin φ.length) := {e : Fin φ.length | r e = true}
  let U : Finset (Finset V) := s.biUnion fun e => (φ.get e).falsifyMonomials
  have hdouble :
      ∑ e ∈ s, ∑ M ∈ (φ.get e).falsifyMonomials, monomial (ZMod 2) M σ =
        ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ := by
    have hext : ∀ e ∈ s,
        ∑ M ∈ (φ.get e).falsifyMonomials, monomial (ZMod 2) M σ =
          ∑ M ∈ U, if M ∈ (φ.get e).falsifyMonomials then monomial (ZMod 2) M σ else 0 := by
      intro e he
      have hfilter_eq : (U.filter fun M => M ∈ (φ.get e).falsifyMonomials) =
          (φ.get e).falsifyMonomials := by
        ext M
        simp only [U, Finset.mem_filter, Finset.mem_biUnion, and_iff_right_iff_imp]
        exact fun hM => ⟨e, he, hM⟩
      rw [← Finset.sum_filter, hfilter_eq]
    rw [Finset.sum_congr rfl hext, Finset.sum_comm]
    have hcoeff : ∀ M ∈ U,
        (∑ e ∈ s, if M ∈ (φ.get e).falsifyMonomials then monomial (ZMod 2) M σ else 0) =
          if #{e : Fin φ.length | r e = true ∧ M ∈ (φ.get e).falsifyMonomials} % 2 = 1 then
            monomial (ZMod 2) M σ
          else 0 := by
      intro M _
      rw [← Finset.sum_filter]
      have hfilt : (s.filter fun e => M ∈ (φ.get e).falsifyMonomials) =
          ({e : Fin φ.length | r e = true ∧ M ∈ (φ.get e).falsifyMonomials} : Finset _) := by
        ext e
        simp [s]
      rw [hfilt, Finset.sum_const, nsmul_eq_mul]
      set c := #{e : Fin φ.length | r e = true ∧ M ∈ (φ.get e).falsifyMonomials}
      rcases Nat.mod_two_eq_zero_or_one c with hc0 | hc1
      · have h0 : (c : ZMod 2) = 0 :=
          (ZMod.natCast_eq_zero_iff c 2).mpr (Nat.dvd_of_mod_eq_zero hc0)
        simp [hc0, h0]
      · have h1 : (c : ZMod 2) = 1 := by
          rw [← Nat.div_add_mod c 2, hc1]
          push_cast
          simp [CharTwo.two_eq_zero]
        simp [hc1, h1]
    rw [Finset.sum_congr rfl hcoeff, ← Finset.sum_filter]
    rfl
  rw [← hdouble]
  calc ∑ e ∈ s, ∑ M ∈ (φ.get e).falsifyMonomials, monomial (ZMod 2) M σ
      = ∑ e ∈ s, bitVal (ZMod 2) (φ.violations σ e) :=
        Finset.sum_congr rfl fun e _ => Clause.sum_falsifyMonomials (φ.get e) σ
    _ = ∑ e : Fin φ.length, bitVal (ZMod 2) (r e * φ.violations σ e) := by
        rw [← Finset.sum_subset (Finset.subset_univ s)]
        · refine Finset.sum_congr rfl fun e he => ?_
          have hr : r e = true := (Finset.mem_filter.mp he).2
          rw [hr, Bool.one_eq_true.symm, one_mul]
        · intro e _ he
          have hr : r e = false := by
            simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] using he
          rw [hr, Bool.zero_eq_false.symm, zero_mul, Bool.zero_eq_false, bitVal_false]
    _ = ∑ e : Fin φ.length, bitEquiv.symm (r e * φ.violations σ e) :=
        Finset.sum_congr rfl fun e _ => (bitEquiv_symm_apply _).symm
    _ = bitEquiv.symm (∑ e : Fin φ.length, r e * φ.violations σ e) :=
        (map_sum bitEquiv.symm _ _).symm
    _ = bitVal (ZMod 2) (∑ e : Fin φ.length, r e * φ.violations σ e) :=
        bitEquiv_symm_apply _

/-- **Parity-row zero criterion** [OpenAI2026ETH, eq. (6.1)]. An assignment `σ` is a zero of the
compiled `ZMod 2` polynomial of row `r` if and only if the violation parity
`∑ e, r e * φ.violations σ e` is `false`. -/
theorem CNF.sum_parityRowMonomials_eq_zero_iff (φ : CNF V) (r : Fin φ.length → Bool)
    (σ : V → Bool) :
    ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ = 0 ↔
      (∑ e : Fin φ.length, r e * φ.violations σ e) = false := by
  rw [CNF.sum_parityRowMonomials]
  cases ∑ e : Fin φ.length, r e * φ.violations σ e <;> decide

/-- Dot-product form of `CNF.sum_parityRowMonomials_eq_zero_iff`. -/
theorem CNF.sum_parityRowMonomials_eq_zero_iff_dotProduct (φ : CNF V) (r : Fin φ.length → Bool)
    (σ : V → Bool) :
    ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ = 0 ↔
      r ⬝ᵥ φ.violations σ = false :=
  CNF.sum_parityRowMonomials_eq_zero_iff φ r σ

/-- For a test list `γ`, the compiled `ZMod 2` polynomial of `testRow γ` vanishes at `σ` if and
only if `testParity γ (φ.violations σ) = false`. -/
theorem CNF.sum_parityRowMonomials_testRow_eq_zero_iff {P : ℕ} (φ : CNF V)
    (γ : Fin P → Fin φ.length × Bool) (σ : V → Bool) :
    ∑ M ∈ φ.parityRowMonomials (testRow γ), monomial (ZMod 2) M σ = 0 ↔
      testParity γ (φ.violations σ) = false := by
  rw [CNF.sum_parityRowMonomials_eq_zero_iff_dotProduct, testRow_dotProduct]

/-- **Common-zero characterization.** An assignment `σ` vanishes on every compiled equation in
`rows` if and only if `PassesTests φ.violations rows σ`. -/
theorem CNF.commonZero_parityRowMonomials_iff_passesTests (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) (σ : V → Bool) :
    (∀ r ∈ rows, ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ = 0) ↔
      PassesTests φ.violations rows σ :=
  forall₂_congr fun r _ => CNF.sum_parityRowMonomials_eq_zero_iff_dotProduct φ r σ

/-- Common-zero characterization phrased over the compiled equation list
`rows.map φ.parityRowMonomials`. -/
theorem CNF.commonZero_map_parityRowMonomials_iff_passesTests (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) (σ : V → Bool) :
    (∀ eq ∈ rows.map φ.parityRowMonomials, ∑ M ∈ eq, monomial (ZMod 2) M σ = 0) ↔
      PassesTests φ.violations rows σ := by
  rw [List.forall_mem_map]
  exact CNF.commonZero_parityRowMonomials_iff_passesTests φ rows σ

end ParityRow

/-! ### Common-zero counts and exact bridge to `CNF.modelCountOn` -/

section ModelCountBridge

variable [Fintype V] [DecidableEq V]

/-- On a finite variable type `V`, `φ.modelCountOn Finset.univ` counts all satisfying assignments
`σ : V → Bool`. -/
@[simp] theorem CNF.modelCountOn_univ (φ : CNF V) :
    φ.modelCountOn Finset.univ = #{σ : V → Bool | φ.eval σ = true} := by
  unfold CNF.modelCountOn
  refine Finset.card_nbij' (fun σ v => σ ⟨v, Finset.mem_univ v⟩) (fun τ v => τ v.1)
    (fun σ hσ => ?_) (fun τ hτ => ?_) (fun _ _ => rfl) (fun _ _ => rfl)
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, dite_true] at hσ ⊢
    exact hσ
  · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, dite_true] at hτ ⊢
    exact hτ

/-- The number of common zeros of `{φ.parityRowMonomials r | r ∈ rows}` on `V → Bool` equals
`numPassing φ.violations rows`. -/
theorem CNF.card_commonZeros_parityRowMonomials (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) :
    #{σ : V → Bool |
        ∀ r ∈ rows, ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ = 0} =
      numPassing φ.violations rows := by
  unfold numPassing
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    CNF.commonZero_parityRowMonomials_iff_passesTests]

/-- **`N(A) = #F + D(A)` decomposition** [OpenAI2026ETH, §6, p. 40]. The number of assignments
passing `rows` equals `φ.modelCountOn Finset.univ` plus the number of nonsatisfying assignments
still accepted by `rows`. -/
theorem CNF.numPassing_violations_eq_modelCountOn_add (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) :
    numPassing φ.violations rows =
      φ.modelCountOn Finset.univ +
        #{σ : V → Bool | φ.eval σ = false ∧ PassesTests φ.violations rows σ} := by
  rw [numPassing_eq, CNF.modelCountOn_univ]
  congr 1
  · congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, CNF.violations_eq_zero_iff]
  · congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, CNF.violations_eq_zero_iff,
      Bool.not_eq_true, and_comm]

/-- **`N(P_A) = #F + D(A)` for compiled `𝔽₂` equations** [OpenAI2026ETH, §6, p. 40]. -/
theorem CNF.card_commonZeros_eq_modelCountOn_add (φ : CNF V)
    (rows : List (Fin φ.length → Bool)) :
    #{σ : V → Bool |
        ∀ r ∈ rows, ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ = 0} =
      φ.modelCountOn Finset.univ +
        #{σ : V → Bool | φ.eval σ = false ∧ PassesTests φ.violations rows σ} := by
  rw [CNF.card_commonZeros_parityRowMonomials, CNF.numPassing_violations_eq_modelCountOn_add]

/-- **Exact common-zero count after `3 n` greedy parity-test rounds**
[OpenAI2026ETH, Lemma 6.2 & §6.3]. Under the hypotheses of `CNF.numPassing_greedy`, the common
zeros of the compiled `𝔽₂` polynomial system `A (3 * Fintype.card V)` number exactly
`φ.modelCountOn Finset.univ` (`#F`). -/
theorem CNF.card_commonZeros_greedy (φ : CNF V) {P : ℕ}
    (hn : 1 ≤ Fintype.card V) (hP : 1 ≤ P) (A : ℕ → List (Fin φ.length → Bool))
    (hinit : ∀ σ, PassesTests φ.violations (A 0) σ → φ.eval σ = false →
      φ.length ≤ P * weight (φ.violations σ))
    (γ : ℕ → Fin P → Fin φ.length × Bool) (hA : ∀ i, A (i + 1) = A i ++ [testRow (γ i)])
    (hγ : ∀ i (γ' : Fin P → Fin φ.length × Bool),
      numPassing φ.violations (A i ++ [testRow (γ i)]) ≤
        numPassing φ.violations (A i ++ [testRow γ'])) :
    #{σ : V → Bool |
        ∀ r ∈ A (3 * Fintype.card V),
          ∑ M ∈ φ.parityRowMonomials r, monomial (ZMod 2) M σ = 0} =
      φ.modelCountOn Finset.univ := by
  rw [CNF.card_commonZeros_parityRowMonomials,
    CNF.numPassing_greedy φ hn hP A hinit γ hA hγ, CNF.modelCountOn_univ]

/-- **Quantitative bounds on compiled greedy systems** [OpenAI2026ETH, Lemma 6.2, p. 42]. If every
clause of `φ` has length at most `k`, the initial matrix `A 0` has at most `3 n` rows each of
weight at most `D₀`, and each round appends `testRow (γ i)` of list length `P`, then at any stage
`i ≤ 3 n` the compiled system `(A i).map φ.parityRowMonomials` has at most `3 n + i` (`≤ 6 n`)
equations, each of degree at most `k`, supported on `φ.vars.toFinset`, and containing at most
`max D₀ P * 2 ^ k` monomials. -/
theorem CNF.greedy_system_bounds (φ : CNF V) {k D₀ P : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (A : ℕ → List (Fin φ.length → Bool))
    (hA₀_len : (A 0).length ≤ 3 * Fintype.card V)
    (hA₀_wt : ∀ r ∈ A 0, weight r ≤ D₀)
    (γ : ℕ → Fin P → Fin φ.length × Bool)
    (hA : ∀ i, A (i + 1) = A i ++ [testRow (γ i)]) {i : ℕ}
    (hi : i ≤ 3 * Fintype.card V) :
    ((A i).map φ.parityRowMonomials).length ≤ 6 * Fintype.card V ∧
      ∀ eq ∈ (A i).map φ.parityRowMonomials,
        (∀ M ∈ eq, M ⊆ φ.vars.toFinset ∧ #M ≤ k) ∧ #eq ≤ max D₀ P * 2 ^ k := by
  have hstep : ∀ j, (A j).length ≤ 3 * Fintype.card V + j ∧
      ∀ r ∈ A j, weight r ≤ max D₀ P := by
    intro j
    induction j with
    | zero =>
      exact ⟨by simpa using hA₀_len, fun r hr => (hA₀_wt r hr).trans (le_max_left D₀ P)⟩
    | succ j ih =>
      rw [hA j, List.length_append, List.length_singleton]
      refine ⟨by omega, fun r hr => ?_⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact ih.2 r hr
      · rw [List.mem_singleton.mp hr]
        exact (weight_testRow_le (γ j)).trans (le_max_right D₀ P)
  obtain ⟨hlen, hwt⟩ := hstep i
  refine ⟨by rw [List.length_map]; omega, ?_⟩
  rw [List.forall_mem_map]
  intro r hr
  refine ⟨fun M hM => ⟨CNF.subset_vars_of_mem_parityRowMonomials hM,
    CNF.card_le_of_mem_parityRowMonomials hk hM⟩, ?_⟩
  exact (CNF.card_parityRowMonomials_le hk r).trans (Nat.mul_le_mul_right _ (hwt r hr))

end ModelCountBridge

end Cslib.Logic.PL
