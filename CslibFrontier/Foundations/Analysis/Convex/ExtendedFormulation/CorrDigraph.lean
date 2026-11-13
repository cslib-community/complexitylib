/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.StableSet
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.TourSplit
public import CslibFrontier.Foundations.Data.List.ConsecutivePairs
import Mathlib.Tactic.FinCases

/-!
# Directed Hamiltonian gadget for the correlation polytope

This module formalizes Steps (i) and (ii) of [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11],
encoding the correlation equations `C_{ij} = C_{ii} ∧ C_{jj}` for `i < j` as a `3`-SAT formula
and realizing its satisfying assignments via Sipser's diamond–clause directed graph `CorrDigraph`
on `O(p²)` vertices (`card_corrDigraphV_le`).

## Main definitions

* `CorrVar`, `CorrDigraphV`, `corrDigraphAdj`: Sipser's directed Hamiltonian-cycle gadget graph
  for the correlation equations on `Fin p`.
* `slotClause`: maps each variable-chain slot `(v, ℓ)` to at most one `(clause, polarity)`.

## Main results

* `card_corrDigraphV_le`: `Fintype.card (CorrDigraphV p) ≤ 23 * p ^ 2` for `1 ≤ p`.
* `exists_dirTour_of_assignment`: every `b : Finset (Fin p)` yields a directed Hamiltonian tour
  whose `(chain v 1, chain v 0)` arcs encode `b bᵀ`.
* `exists_assignment_of_dirTour`: every directed Hamiltonian tour of `corrDigraphAdj p`
  encodes `b bᵀ` for some `b : Finset (Fin p)`.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.4 (Lemma 11, Steps (i)–(ii)).
-/


public section

/-- Variables of the correlation `3`-SAT formula on `Fin p`: diagonal `C_{ii}` and
upper-triangular off-diagonal `C_{ij}` (`i < j`). -/
inductive CorrVar (p : ℕ) : Type
  | diag (i : Fin p)
  | off (e : CorrPairIdx p)
  deriving DecidableEq

/-- Equivalence between `CorrVar p` and `Fin p ⊕ CorrPairIdx p`. -/
def corrVarEquivSum (p : ℕ) : CorrVar p ≃ Fin p ⊕ CorrPairIdx p where
  toFun
    | .diag i => Sum.inl i
    | .off e => Sum.inr e
  invFun
    | Sum.inl i => .diag i
    | Sum.inr e => .off e
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with i | e <;> rfl

instance (p : ℕ) : Fintype (CorrVar p) :=
  Fintype.ofEquiv _ (corrVarEquivSum p).symm

instance (p : ℕ) [NeZero p] : Nonempty (CorrVar p) := ⟨.diag 0⟩

/-- Number of occurrence slots in the chain of `v : CorrVar p`. -/
@[expose] def chainSlots (p : ℕ) : CorrVar p → ℕ
  | .diag _ => 4 * p
  | .off _ => 4

/-- Number of chain vertices in the diamond gadget of `v : CorrVar p` (`3 * slots + 1`). -/
@[expose] def chainLen (p : ℕ) (v : CorrVar p) : ℕ :=
  3 * chainSlots p v + 1

theorem two_le_chainLen {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p) : 2 ≤ chainLen p v := by
  cases v <;> simp only [chainLen, chainSlots] <;> omega

/-- Cyclic next variable in `CorrVar p` (`p ≥ 1`). -/
noncomputable def varNext {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p) : CorrVar p :=
  have : NeZero (Fintype.card (CorrVar p)) := ⟨@Fintype.card_ne_zero _ _ ⟨.diag ⟨0, hp⟩⟩⟩
  let e := Fintype.equivFin (CorrVar p)
  e.symm (e v + 1)

theorem varNext_bijective {p : ℕ} (hp : 1 ≤ p) : Function.Bijective (varNext hp) := by
  have : NeZero (Fintype.card (CorrVar p)) := ⟨@Fintype.card_ne_zero _ _ ⟨.diag ⟨0, hp⟩⟩⟩
  let e := Fintype.equivFin (CorrVar p)
  have h1 : Function.Bijective (fun k : Fin (Fintype.card (CorrVar p)) => k + 1) :=
    ⟨fun a b h => add_right_cancel h, fun b => ⟨b - 1, sub_add_cancel b 1⟩⟩
  exact (e.symm.bijective.comp h1).comp e.bijective

/-- Vertices of the directed correlation gadget `D_p`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Step (ii)]. -/
inductive CorrDigraphV (p : ℕ) : Type
  | gate (v : CorrVar p)
  | chain (v : CorrVar p) (k : Fin (chainLen p v))
  | clause (e : CorrPairIdx p) (c : Fin 4)
  deriving DecidableEq

/-- Equivalence unpacking `CorrDigraphV p` into sums and products for cardinality bounds. -/
def corrDigraphVEquiv (p : ℕ) :
    CorrDigraphV p ≃ CorrVar p ⊕ (Σ v : CorrVar p, Fin (chainLen p v)) ⊕ (CorrPairIdx p × Fin 4)
    where
  toFun
    | .gate v => Sum.inl v
    | .chain v k => Sum.inr (Sum.inl ⟨v, k⟩)
    | .clause e c => Sum.inr (Sum.inr (e, c))
  invFun
    | Sum.inl v => .gate v
    | Sum.inr (Sum.inl ⟨v, k⟩) => .chain v k
    | Sum.inr (Sum.inr (e, c)) => .clause e c
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with v | ⟨v, k⟩ | ⟨e, c⟩ <;> rfl

instance (p : ℕ) : Fintype (CorrDigraphV p) :=
  Fintype.ofEquiv _ (corrDigraphVEquiv p).symm

instance (p : ℕ) [NeZero p] : Nonempty (CorrDigraphV p) := ⟨.gate (.diag 0)⟩

/-- Quadratic vertex-count bound `|V(D_p)| ≤ 23 p²` for `p ≥ 1`. -/
theorem card_corrDigraphV_le {p : ℕ} (hp : 1 ≤ p) : Fintype.card (CorrDigraphV p) ≤ 23 * p ^ 2 := by
  have hcard_pair : 2 * Fintype.card (CorrPairIdx p) ≤ p ^ 2 := by
    let f : CorrPairIdx p ⊕ CorrPairIdx p → Fin p × Fin p :=
      Sum.elim (fun e => (e.fst, e.snd)) (fun e => (e.snd, e.fst))
    have hinj : Function.Injective f := by
      rintro (e₁ | e₁) (e₂ | e₂) heq
      · simp only [f, Sum.elim_inl, Prod.mk.injEq] at heq
        cases e₁; cases e₂; simp only at heq; rcases heq with ⟨rfl, rfl⟩; rfl
      · simp only [f, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq] at heq
        exfalso
        have h1 : e₁.fst < e₁.snd := e₁.lt
        have h2 : e₂.fst < e₂.snd := e₂.lt
        rw [heq.1, heq.2] at h1
        exact lt_asymm h1 h2
      · simp only [f, Sum.elim_inr, Sum.elim_inl, Prod.mk.injEq] at heq
        exfalso
        have h1 : e₁.fst < e₁.snd := e₁.lt
        have h2 : e₂.fst < e₂.snd := e₂.lt
        rw [← heq.1, ← heq.2] at h2
        exact lt_asymm h1 h2
      · simp only [f, Sum.elim_inr, Prod.mk.injEq] at heq
        cases e₁; cases e₂; simp only at heq; rcases heq with ⟨rfl, rfl⟩; rfl
    have hle := Fintype.card_le_of_injective f hinj
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at hle
    nlinarith
  rw [Fintype.card_congr (corrDigraphVEquiv p), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_congr (corrVarEquivSum p), Fintype.card_sum, Fintype.card_fin,
    Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  have hsig : ∑ v : CorrVar p, Fintype.card (Fin (chainLen p v)) =
      p * (12 * p + 1) + Fintype.card (CorrPairIdx p) * 13 := by
    rw [Fintype.sum_equiv (corrVarEquivSum p) _ (Sum.elim (fun _ => 12 * p + 1) (fun _ => 13))
      fun x => by
        rw [Fintype.card_fin]
        cases x with
        | diag _ =>
            simp only [corrVarEquivSum, Equiv.coe_fn_mk, Sum.elim_inl, chainLen, chainSlots]
            omega
        | off _ =>
            simp only [corrVarEquivSum, Equiv.coe_fn_mk, Sum.elim_inr, chainLen, chainSlots]]
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hsig]
  have hp2 : p ≤ p ^ 2 := by nlinarith
  nlinarith

theorem three_le_card_corrDigraphV {p : ℕ} (hp : 1 ≤ p) : 3 ≤ Fintype.card (CorrDigraphV p) := by
  let i0 : Fin p := ⟨0, hp⟩
  have h := Fintype.card_le_of_injective
    (fun k : Fin (chainLen p (.diag i0)) => CorrDigraphV.chain (.diag i0) k)
    (fun k₁ k₂ he => by cases he; rfl)
  rw [Fintype.card_fin] at h
  have hlen : 3 ≤ chainLen p (.diag i0) := by simp only [chainLen, chainSlots]; omega
  exact hlen.trans h

theorem two_le_card_corrDigraphV {p : ℕ} (hp : 1 ≤ p) : 2 ≤ Fintype.card (CorrDigraphV p) :=
  by have := three_le_card_corrDigraphV hp; omega

/-- Polarity of literal 1 (`C_{ii}`), literal 2 (`C_{jj}`), and literal 3 (`C_{ij}`) in the
four clauses enforcing `C_{ij} = C_{ii} ∧ C_{jj}`
[FioriniMassarPokuttaTiwaryDeWolf2015, Step (i)]. -/
@[expose] def clauseLit₁ : Fin 4 → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => false

/-- Polarity of literal 2 (`C_{jj}`) in the four clauses enforcing `C_{ij} = C_{ii} ∧ C_{jj}`
[FioriniMassarPokuttaTiwaryDeWolf2015, Step (i)]. -/
@[expose] def clauseLit₂ : Fin 4 → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => true

/-- Polarity of literal 3 (`C_{ij}`) in the four clauses enforcing `C_{ij} = C_{ii} ∧ C_{jj}`
[FioriniMassarPokuttaTiwaryDeWolf2015, Step (i)]. -/
@[expose] def clauseLit₃ : Fin 4 → Bool
  | 0 => true
  | 1 => false
  | 2 => false
  | 3 => false

theorem forall_clause_iff_eq_and (bi bj be : Bool) :
    (∀ c : Fin 4, bi = clauseLit₁ c ∨ bj = clauseLit₂ c ∨ be = clauseLit₃ c) ↔
      be = (bi && bj) := by
  constructor
  · intro h
    cases bi <;> cases bj <;> cases be <;>
      first | decide | exact absurd (h 0) (by decide) | exact absurd (h 1) (by decide) |
        exact absurd (h 2) (by decide) | exact absurd (h 3) (by decide)
  · rintro rfl c
    fin_cases c <;> cases bi <;> cases bj <;> decide

/-- Unique clause and literal polarity attached to slot `(v, ℓ)`, if any. -/
def slotClause (p : ℕ) :
    (v : CorrVar p) → Fin (chainSlots p v) → Option ((CorrPairIdx p × Fin 4) × Bool)
  | .diag i, ℓ =>
      let j : Fin p := ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩
      let c : Fin 4 := ⟨ℓ.1 % 4, by omega⟩
      if h1 : i < j then some ((⟨i, j, h1⟩, c), clauseLit₁ c)
      else if h2 : j < i then some ((⟨j, i, h2⟩, c), clauseLit₂ c)
      else none
  | .off e, ℓ => some ((e, ℓ), clauseLit₃ ℓ)

theorem slotClause_eq_some_iff {p : ℕ} {v : CorrVar p} {ℓ : Fin (chainSlots p v)}
    {e : CorrPairIdx p} {c : Fin 4} {lit : Bool} :
    slotClause p v ℓ = some ((e, c), lit) ↔
      (v = .diag e.fst ∧ ℓ.1 = 4 * Fin.val e.snd + c.1 ∧ lit = clauseLit₁ c) ∨
      (v = .diag e.snd ∧ ℓ.1 = 4 * Fin.val e.fst + c.1 ∧ lit = clauseLit₂ c) ∨
      (v = .off e ∧ ℓ.1 = c.1 ∧ lit = clauseLit₃ c) := by
  cases v with
  | diag i =>
      dsimp only [slotClause]
      have hdiv : ℓ.1 = 4 * (ℓ.1 / 4) + ℓ.1 % 4 := by omega
      split_ifs with h1 h2
      · simp only [Option.some.injEq, Prod.mk.injEq, CorrVar.diag.injEq, false_and, or_false]
        constructor
        · rintro ⟨⟨he, hc⟩, rfl⟩
          left
          have he1 :
              e = ⟨i, ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩, h1⟩ :=
            he.symm
          subst he1 hc
          exact ⟨rfl, hdiv, rfl⟩
        · rintro (⟨rfl, hl, rfl⟩ | ⟨rfl, hl, rfl⟩)
          · have hj : ℓ.1 / 4 = e.snd.1 := by omega
            have hc : ℓ.1 % 4 = c.1 := by omega
            have hc' : (⟨ℓ.1 % 4, by omega⟩ : Fin 4) = c := Fin.ext hc
            have he' :
                (⟨e.fst, ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩,
                  h1⟩ : CorrPairIdx p) = e := by
              cases e; simp only [CorrPairIdx.mk.injEq, Fin.ext_iff, true_and]; exact hj
            exact ⟨⟨he', hc'⟩, congrArg clauseLit₁ hc'⟩
          · exfalso
            have hj : ℓ.1 / 4 = e.fst.1 := by omega
            have hlt : e.fst.1 < e.snd.1 := e.lt
            have hlt1 : e.snd.1 < ℓ.1 / 4 := h1
            omega
      · simp only [Option.some.injEq, Prod.mk.injEq, CorrVar.diag.injEq, false_and, or_false]
        constructor
        · rintro ⟨⟨he, hc⟩, rfl⟩
          right
          have he1 :
              e = ⟨⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩, i, h2⟩ :=
            he.symm
          subst he1 hc
          exact ⟨rfl, hdiv, rfl⟩
        · rintro (⟨rfl, hl, rfl⟩ | ⟨rfl, hl, rfl⟩)
          · exfalso
            have hj : ℓ.1 / 4 = e.snd.1 := by omega
            have hlt : e.fst.1 < e.snd.1 := e.lt
            have hnot :
                ¬ e.fst < ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩ := h1
            exact hnot (by simpa only [Fin.lt_def, hj] using hlt)
          · have hj : ℓ.1 / 4 = e.fst.1 := by omega
            have hc : ℓ.1 % 4 = c.1 := by omega
            have hc' : (⟨ℓ.1 % 4, by omega⟩ : Fin 4) = c := Fin.ext hc
            have he' :
                (⟨⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩, e.snd,
                  h2⟩ : CorrPairIdx p) = e := by
              cases e; simp only [CorrPairIdx.mk.injEq, Fin.ext_iff, and_true]; exact hj
            exact ⟨⟨he', hc'⟩, congrArg clauseLit₂ hc'⟩
      · simp only [CorrVar.diag.injEq, false_iff, not_or, not_and]
        refine ⟨fun he hl _ => ?_, fun he hl _ => ?_, fun h => by cases h⟩
        · subst he
          have hj : ℓ.1 / 4 = e.snd.1 := by omega
          have hlt : e.fst < ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩ := by
            simpa only [Fin.lt_def, hj] using e.lt
          exact h1 hlt
        · subst he
          have hj : ℓ.1 / 4 = e.fst.1 := by omega
          have hlt : ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩ < e.snd := by
            simpa only [Fin.lt_def, hj] using e.lt
          exact h2 hlt
  | off e' =>
      dsimp only [slotClause]
      constructor
      · intro h
        injection h with h
        injection h with h1 h2
        injection h1 with he hl
        subst he hl h2
        exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
      · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, hc, rfl⟩)
        · cases h
        · cases h
        · cases CorrVar.off.inj h
          cases Fin.ext hc
          rfl

/-- Directed adjacency of `D_p` [FioriniMassarPokuttaTiwaryDeWolf2015, §3.4, Step (ii)]. -/
@[expose] def corrDigraphAdj (p : ℕ) (hp : 1 ≤ p) : CorrDigraphV p → CorrDigraphV p → Prop
  | .gate v, .chain v' k => v = v' ∧ (k.1 = 0 ∨ k.1 + 1 = chainLen p v)
  | .chain v' k, .gate v => v = varNext hp v' ∧ (k.1 = 0 ∨ k.1 + 1 = chainLen p v')
  | .chain v₁ k₁, .chain v₂ k₂ => v₁ = v₂ ∧ (k₁.1 + 1 = k₂.1 ∨ k₂.1 + 1 = k₁.1)
  | .chain v k, .clause e c =>
      ∃ (ℓ : Fin (chainSlots p v)) (lit : Bool), slotClause p v ℓ = some ((e, c), lit) ∧
        ((lit = false ∧ k.1 = 3 * ℓ.1 + 1) ∨ (lit = true ∧ k.1 = 3 * ℓ.1 + 2))
  | .clause e c, .chain v k =>
      ∃ (ℓ : Fin (chainSlots p v)) (lit : Bool), slotClause p v ℓ = some ((e, c), lit) ∧
        ((lit = false ∧ k.1 = 3 * ℓ.1 + 2) ∨ (lit = true ∧ k.1 = 3 * ℓ.1 + 1))
  | _, _ => False

theorem corrDigraphAdj_irrefl {p : ℕ} (hp : 1 ≤ p) (u : CorrDigraphV p) :
    ¬ corrDigraphAdj p hp u u := by
  cases u with
  | gate v => exact fun h => by exact h
  | chain v k =>
      intro ⟨_, h⟩
      omega
  | clause e c => exact fun h => by exact h

section TourAssignment

private noncomputable def varAt (p : ℕ)
    (k : Fin (Fintype.card (CorrVar p))) : CorrVar p :=
  (Fintype.equivFin (CorrVar p)).symm k

private theorem varNext_varAt {p : ℕ} [NeZero p] (hp : 1 ≤ p)
    (k : Fin (Fintype.card (CorrVar p))) :
    varNext hp (varAt p k) = varAt p (k + 1) := by
  simp only [varNext, varAt, Equiv.apply_symm_apply]

private def assignVarVal {p : ℕ} (b : Finset (Fin p)) : CorrVar p → Bool
  | .diag i => decide (i ∈ b)
  | .off e => decide (e.fst ∈ b ∧ e.snd ∈ b)

private def clauseOwner {p : ℕ} (b : Finset (Fin p)) (q : CorrPairIdx p × Fin 4) :
    (v : CorrVar p) × Fin (chainSlots p v) :=
  let e := q.1
  let c := q.2
  if h1 : assignVarVal b (.diag e.fst) = clauseLit₁ c then
    ⟨.diag e.fst, ⟨4 * e.snd.1 + c.1, by simp only [chainSlots]; omega⟩⟩
  else if h2 : assignVarVal b (.diag e.snd) = clauseLit₂ c then
    ⟨.diag e.snd, ⟨4 * e.fst.1 + c.1, by simp only [chainSlots]; omega⟩⟩
  else
    ⟨.off e, ⟨c.1, by simp only [chainSlots]; omega⟩⟩

private theorem slotClause_clauseOwner {p : ℕ} (b : Finset (Fin p))
    (q : CorrPairIdx p × Fin 4) :
    slotClause p (clauseOwner b q).1 (clauseOwner b q).2 =
      some (q, assignVarVal b (clauseOwner b q).1) := by
  rcases q with ⟨e, c⟩
  by_cases h1 : assignVarVal b (.diag e.fst) = clauseLit₁ c
  · have hco : clauseOwner b (e, c) =
        ⟨.diag e.fst, ⟨4 * e.snd.1 + c.1, by simp only [chainSlots]; omega⟩⟩ := by
      dsimp only [clauseOwner]
      simp only [eq_true h1, ↓reduceDIte]
    rw [hco, slotClause_eq_some_iff]
    left; exact ⟨rfl, rfl, h1⟩
  · by_cases h2 : assignVarVal b (.diag e.snd) = clauseLit₂ c
    · have hco : clauseOwner b (e, c) =
          ⟨.diag e.snd, ⟨4 * e.fst.1 + c.1, by simp only [chainSlots]; omega⟩⟩ := by
        dsimp only [clauseOwner]
        simp only [eq_false h1, eq_true h2, ↓reduceDIte]
      rw [hco, slotClause_eq_some_iff]
      right; left; exact ⟨rfl, rfl, h2⟩
    · have hsat : assignVarVal b (.off e) =
          (assignVarVal b (.diag e.fst) && assignVarVal b (.diag e.snd)) := by
        simp only [assignVarVal]
        by_cases hi : e.fst ∈ b <;> by_cases hj : e.snd ∈ b <;> simp only [hi, hj, decide_true,
          decide_false, Bool.and_true, Bool.and_false, and_self, and_false, false_and]
      have hfor := (forall_clause_iff_eq_and (assignVarVal b (.diag e.fst))
        (assignVarVal b (.diag e.snd)) (assignVarVal b (.off e))).2 hsat c
      have h3 : assignVarVal b (.off e) = clauseLit₃ c := by
        rcases hfor with h | h | h
        · exact absurd h h1
        · exact absurd h h2
        · exact h
      have hco : clauseOwner b (e, c) =
          ⟨.off e, ⟨c.1, by simp only [chainSlots]; omega⟩⟩ := by
        dsimp only [clauseOwner]
        simp only [eq_false h1, eq_false h2, ↓reduceDIte]
      rw [hco, slotClause_eq_some_iff]
      right; right; exact ⟨rfl, rfl, h3⟩

private def slotDetour {p : ℕ} (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) : List (CorrDigraphV p) :=
  match slotClause p v ℓ with
  | some (q, _) => if clauseOwner b q = ⟨v, ℓ⟩ then [.clause q.1 q.2] else []
  | none => []

private theorem mem_slotDetour_iff {p : ℕ} (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) (x : CorrDigraphV p) :
    x ∈ slotDetour b v ℓ ↔
      ∃ q, x = .clause q.1 q.2 ∧ clauseOwner b q = ⟨v, ℓ⟩ := by
  dsimp only [slotDetour]
  cases h : slotClause p v ℓ with
  | none =>
      simp only [List.not_mem_nil, false_iff, not_exists, not_and]
      intro q _ hq
      have hs := slotClause_clauseOwner b q
      rw [hq, h] at hs
      cases hs
  | some ql =>
      rcases ql with ⟨q, lit⟩
      dsimp only
      split_ifs with hq
      · simp only [List.mem_singleton]
        constructor
        · rintro rfl; exact ⟨q, rfl, hq⟩
        · rintro ⟨q', rfl, hq'⟩
          have hs := slotClause_clauseOwner b q'
          rw [hq', h, Option.some.injEq, Prod.mk.injEq] at hs
          rw [hs.1]
      · simp only [List.not_mem_nil, false_iff, not_exists, not_and]
        intro q' _ hq'
        have hs := slotClause_clauseOwner b q'
        rw [hq', h, Option.some.injEq, Prod.mk.injEq] at hs
        exact hq (hs.1 ▸ hq')

private def slotVisit {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) : List (CorrDigraphV p) :=
  let k₀ : Fin (chainLen p v) := ⟨3 * ℓ.1, by simp only [chainLen]; omega⟩
  let k₁ : Fin (chainLen p v) := ⟨3 * ℓ.1 + 1, by simp only [chainLen]; omega⟩
  let k₂ : Fin (chainLen p v) := ⟨3 * ℓ.1 + 2, by simp only [chainLen]; omega⟩
  if assignVarVal b v = false then
    [.chain v k₀, .chain v k₁] ++ slotDetour b v ℓ ++ [.chain v k₂]
  else
    [.chain v k₂] ++ slotDetour b v ℓ ++ [.chain v k₁, .chain v k₀]

private theorem slotVisit_ne_nil {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) : slotVisit _hp b v ℓ ≠ [] := by
  dsimp only [slotVisit]
  split_ifs <;> simp only [List.cons_append, List.nil_append, ne_eq, List.cons_ne_nil,
    not_false_eq_true]

private theorem chainSlots_pos {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p) : 0 < chainSlots p v := by
  cases v <;> simp only [chainSlots] <;> omega

private def varBlock {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    List (CorrDigraphV p) :=
  let kEnd : Fin (chainLen p v) := ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩
  if assignVarVal b v = false then
    [.gate v] ++ ((List.finRange (chainSlots p v)).flatMap (slotVisit hp b v)) ++ [.chain v kEnd]
  else
    [.gate v, .chain v kEnd] ++
      (((List.finRange (chainSlots p v)).map Fin.rev).flatMap (slotVisit hp b v))

private theorem varBlock_ne_nil {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    varBlock hp b v ≠ [] := by
  dsimp only [varBlock]
  split_ifs <;> simp only [List.cons_append, List.nil_append, ne_eq, List.cons_ne_nil,
    not_false_eq_true]

private theorem head_varBlock {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    (varBlock hp b v).head (varBlock_ne_nil hp b v) = .gate v := by
  dsimp only [varBlock]
  split_ifs <;> simp only [List.cons_append, List.nil_append, List.head_cons]

private theorem getLast_varBlock {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    (varBlock hp b v).getLast (varBlock_ne_nil hp b v) =
      if assignVarVal b v = false then
        .chain v ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩
      else
        .chain v ⟨0, by have := chainSlots_pos hp v; simp only [chainLen]; omega⟩ := by
  have hs := chainSlots_pos hp v
  have hfr : List.finRange (chainSlots p v) ≠ [] := mt List.finRange_eq_nil_iff.1 hs.ne'
  have hrev : (List.finRange (chainSlots p v)).map Fin.rev ≠ [] :=
    mt List.map_eq_nil_iff.1 hfr
  dsimp only [varBlock]
  split_ifs with hval
  · simp only [List.cons_append, List.nil_append,
    List.getLast_cons (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
    List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast_singleton]
  · simp only [List.cons_append, List.nil_append]
    have htrue : assignVarVal b v = true := Bool.eq_true_of_not_eq_false hval
    have hfm := List.flatMap_ne_nil hrev (fun ℓ _ => slotVisit_ne_nil hp b v ℓ)
    rw [List.getLast_cons (List.cons_ne_nil _ _), List.getLast_cons hfm,
      List.getLast_flatMap hrev (fun ℓ _ => slotVisit_ne_nil hp b v ℓ)]
    have hgl : ((List.finRange (chainSlots p v)).map Fin.rev).getLast hrev = ⟨0, hs⟩ := by
      rw [List.getLast_eq_getElem]
      simp only [List.getElem_map, List.length_map, List.length_finRange, List.getElem_finRange]
      ext; simp only [Fin.val_rev, Fin.val_cast]; omega
    rw [hgl]
    simp only [slotVisit, htrue, Bool.true_eq_false, ↓reduceIte, List.cons_append, List.nil_append]
    rw [List.getLast_cons (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
      List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast_cons (List.cons_ne_nil _ _), List.getLast_singleton]

private theorem List.consecutivePairs_slotVisit_mem {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p))
    (v : CorrVar p) (ℓ : Fin (chainSlots p v)) {x y : CorrDigraphV p}
    (hmem : (x, y) ∈ List.consecutivePairs (slotVisit hp b v ℓ)) :
    corrDigraphAdj p hp x y := by
  have hchain {i j : Fin (chainLen p v)} (h : i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) :
      corrDigraphAdj p hp (.chain v i) (.chain v j) := ⟨rfl, h⟩
  -- The clause visited by its owner slot carries the variable's value as its literal.
  have hown {q : CorrPairIdx p × Fin 4} {lit : Bool} (hs : slotClause p v ℓ = some (q, lit))
      (ho : clauseOwner b q = ⟨v, ℓ⟩) : lit = assignVarVal b v := by
    have hcl := slotClause_clauseOwner b q
    rw [ho, hs, Option.some.injEq, Prod.mk.injEq] at hcl
    exact hcl.2
  -- A visit walks the slot's three chain vertices upwards (value `false`) or downwards (`true`),
  -- detouring through the slot's clause between `3ℓ + 1` and `3ℓ + 2` when the slot owns it.
  dsimp only [slotVisit, slotDetour] at hmem
  cases hval : assignVarVal b v <;> rcases hs : slotClause p v ℓ with _ | ⟨q, lit⟩ <;>
    simp only [hval, hs, Bool.true_eq_false, ↓reduceIte] at hmem <;>
    try split_ifs at hmem with ho
  all_goals
    simp only [List.append_nil, List.cons_append, List.nil_append,
      List.consecutivePairs_cons_cons, List.consecutivePairs_singleton, List.mem_cons,
      Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    casesm* _ ∨ _ <;> obtain ⟨rfl, rfl⟩ := hmem <;>
    first
      | exact hchain (.inl rfl)
      | exact hchain (.inr rfl)
      | exact ⟨ℓ, lit, hs, .inl ⟨(hown hs ho).trans hval, rfl⟩⟩
      | exact ⟨ℓ, lit, hs, .inr ⟨(hown hs ho).trans hval, rfl⟩⟩

private theorem head_slotVisit {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) :
    (slotVisit _hp b v ℓ).head (slotVisit_ne_nil _hp b v ℓ) =
      if assignVarVal b v = false then
        .chain v ⟨3 * ℓ.1, by simp only [chainLen]; omega⟩
      else
        .chain v ⟨3 * ℓ.1 + 2, by simp only [chainLen]; omega⟩ := by
  dsimp only [slotVisit]
  split_ifs <;> simp only [List.cons_append, List.nil_append, List.head_cons]

private theorem getLast_slotVisit {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) :
    (slotVisit _hp b v ℓ).getLast (slotVisit_ne_nil _hp b v ℓ) =
      if assignVarVal b v = false then
        .chain v ⟨3 * ℓ.1 + 2, by simp only [chainLen]; omega⟩
      else
        .chain v ⟨3 * ℓ.1, by simp only [chainLen]; omega⟩ := by
  dsimp only [slotVisit]
  split_ifs <;> simp only [List.cons_append, List.nil_append]
  · rw [List.getLast_cons (List.cons_ne_nil _ _),
      List.getLast_cons (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
      List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast_singleton]
  · rw [List.getLast_cons (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
      List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast_cons (List.cons_ne_nil _ _), List.getLast_singleton]


private lemma varBlock_forward_edges {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p))
    (v : CorrVar p) (hval : assignVarVal b v = false) {x y : CorrDigraphV p}
    (hfr : List.finRange (chainSlots p v) ≠ []) :
    (x, y) ∈ List.consecutivePairs (varBlock hp b v) ↔
      (x = .gate v ∧ y = ((List.finRange (chainSlots p v)).flatMap
          (fun ℓ => slotVisit hp b v ℓ)).head
        (List.flatMap_ne_nil hfr (fun ℓ _ => slotVisit_ne_nil hp b v ℓ))) ∨
      (x, y) ∈ List.consecutivePairs ((List.finRange (chainSlots p v)).flatMap
        (fun ℓ => slotVisit hp b v ℓ)) ∨
      (x = ((List.finRange (chainSlots p v)).flatMap (fun ℓ => slotVisit hp b v ℓ)).getLast
        (List.flatMap_ne_nil hfr (fun ℓ _ => slotVisit_ne_nil hp b v ℓ)) ∧
        y = .chain v ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩) := by
  dsimp only [varBlock]
  simp only [hval, ↓reduceIte]
  have hfm := List.flatMap_ne_nil hfr (fun ℓ _ => slotVisit_ne_nil hp b v ℓ)
  have hcat := List.append_ne_nil_of_left_ne_nil hfm
    [.chain v ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩]
  rw [List.append_assoc,
    List.consecutivePairs_append (List.cons_ne_nil _ _) hcat,
    List.consecutivePairs_append hfm (List.cons_ne_nil _ _)]
  simp only [List.consecutivePairs_singleton,
    List.nil_append, List.mem_append, List.mem_cons, Prod.mk.injEq,
    List.not_mem_nil, or_false, List.getLast_singleton]
  rw [List.head_append_of_ne_nil hfm]
  tauto

private theorem List.consecutivePairs_varBlock_mem {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p))
    (v : CorrVar p) {x y : CorrDigraphV p}
    (hmem : (x, y) ∈ List.consecutivePairs (varBlock hp b v)) :
    corrDigraphAdj p hp x y := by
  have hs := chainSlots_pos hp v
  have hfr : List.finRange (chainSlots p v) ≠ [] := mt List.finRange_eq_nil_iff.1 hs.ne'
  have hrev : (List.finRange (chainSlots p v)).map Fin.rev ≠ [] :=
    mt List.map_eq_nil_iff.1 hfr
  by_cases hval : assignVarVal b v = false
  · rw [varBlock_forward_edges hp b v hval hfr] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hflat | ⟨rfl, rfl⟩
    · rw [List.head_flatMap hfr (fun ℓ _ => slotVisit_ne_nil hp b v ℓ), head_slotVisit, hval]
      have hhead : (List.finRange (chainSlots p v)).head hfr = ⟨0, hs⟩ := by
        apply Fin.ext
        rw [List.head_eq_getElem]
        simp only [List.getElem_finRange, Fin.val_cast]
      simp only [hhead, ↓reduceIte, corrDigraphAdj, Nat.mul_zero, true_and]
      exact Or.inl trivial
    · rw [List.mem_consecutivePairs_flatMap hfr (fun ℓ => slotVisit_ne_nil hp b v ℓ)] at hflat
      rcases hflat with ⟨ℓ, _, hxy⟩ | ⟨⟨ℓ₁, ℓ₂⟩, hadj, rfl, rfl⟩
      · exact List.consecutivePairs_slotVisit_mem hp b v ℓ hxy
      · rw [List.mem_consecutivePairs_iff_exists_getElem] at hadj
        obtain ⟨i, hi, h1, h2⟩ := hadj
        have h1v := congrArg Fin.val h1
        have h2v := congrArg Fin.val h2
        simp only [List.length_finRange, List.getElem_finRange, Fin.val_cast] at hi h1v h2v
        rw [getLast_slotVisit, head_slotVisit, hval]
        simp only [↓reduceIte, corrDigraphAdj, true_and]
        left; omega
    · rw [List.getLast_flatMap hfr (fun ℓ _ => slotVisit_ne_nil hp b v ℓ), getLast_slotVisit, hval]
      have hgl : (List.finRange (chainSlots p v)).getLast hfr = ⟨chainSlots p v - 1, by omega⟩ :=
        by
          apply Fin.ext
          simp only [List.getLast_eq_getElem, List.length_finRange, List.getElem_finRange,
            Fin.val_cast]
      simp only [hgl, ↓reduceIte, corrDigraphAdj, true_and]
      left; omega
  · have htrue : assignVarVal b v = true := Bool.eq_true_of_not_eq_false hval
    dsimp only [varBlock] at hmem
    simp only [htrue, Bool.true_eq_false, ↓reduceIte] at hmem
    have hfm := List.flatMap_ne_nil hrev (fun ℓ _ => slotVisit_ne_nil hp b v ℓ)
    rw [show [.gate v, .chain v ⟨3 * chainSlots p v, _⟩] ++
        ((List.finRange (chainSlots p v)).map Fin.rev).flatMap (slotVisit hp b v) =
        ([.gate v, .chain v ⟨3 * chainSlots p v, _⟩] : List _) ++
          ((List.finRange (chainSlots p v)).map Fin.rev).flatMap (slotVisit hp b v) from rfl,
      List.consecutivePairs_append (List.cons_ne_nil _ _) hfm] at hmem
    simp only [List.consecutivePairs_cons_cons, List.consecutivePairs_singleton,
      List.nil_append, List.cons_append, List.getLast_cons (List.cons_ne_nil _ _),
      List.getLast_singleton, List.mem_cons, Prod.mk.injEq, ] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hflat
    · simp only [corrDigraphAdj, chainLen, true_and]
      right; trivial
    · rw [List.head_flatMap hrev (fun ℓ _ => slotVisit_ne_nil hp b v ℓ), head_slotVisit, htrue]
      simp only [Bool.true_eq_false, ↓reduceIte]
      have hh : ((List.finRange (chainSlots p v)).map Fin.rev).head hrev =
          ⟨chainSlots p v - 1, by omega⟩ := by
        rw [List.head_eq_getElem, List.getElem_map, List.getElem_finRange]
        ext; simp only [Fin.val_rev, Fin.val_cast]
      simp only [hh, corrDigraphAdj, true_and]
      right; omega
    · rw [List.mem_consecutivePairs_flatMap hrev (fun ℓ => slotVisit_ne_nil hp b v ℓ)] at hflat
      rcases hflat with ⟨ℓ, _, hxy⟩ | ⟨⟨ℓ₁, ℓ₂⟩, hadj, rfl, rfl⟩
      · exact List.consecutivePairs_slotVisit_mem hp b v ℓ hxy
      · rw [List.mem_consecutivePairs_iff_exists_getElem] at hadj
        obtain ⟨i, hi, h1, h2⟩ := hadj
        simp only [List.length_map, List.length_finRange, List.getElem_map,
          List.getElem_finRange] at hi h1 h2
        rw [getLast_slotVisit, head_slotVisit, htrue]
        simp only [Bool.true_eq_false, ↓reduceIte, ← h1, ← h2, Fin.val_rev, Fin.val_cast,
          corrDigraphAdj, true_and]
        right; omega

private theorem mem_slotVisit_iff {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) (x : CorrDigraphV p) :
    x ∈ slotVisit _hp b v ℓ ↔
      (x = .chain v ⟨3 * ℓ.1, by simp only [chainLen]; omega⟩ ∨
       x = .chain v ⟨3 * ℓ.1 + 1, by simp only [chainLen]; omega⟩ ∨
       x = .chain v ⟨3 * ℓ.1 + 2, by simp only [chainLen]; omega⟩) ∨
      ∃ q, x = .clause q.1 q.2 ∧ clauseOwner b q = ⟨v, ℓ⟩ := by
  -- Both orientations list the same vertices, in opposite orders.
  dsimp only [slotVisit]
  split_ifs <;> simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
    mem_slotDetour_iff] <;>
    generalize (∃ q : CorrPairIdx p × Fin 4, x = .clause q.1 q.2 ∧ clauseOwner b q = ⟨v, ℓ⟩) =
      hd <;>
    tauto

private theorem slotVisit_nodup {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) : (slotVisit _hp b v ℓ).Nodup := by
  have hdet : (slotDetour b v ℓ).Nodup := by
    dsimp only [slotDetour]
    cases slotClause p v ℓ with
    | none => exact List.nodup_nil
    | some _ =>
        dsimp only
        split_ifs <;> simp only [List.nodup_singleton, List.nodup_nil]
  have hdisj : ∀ z ∈ slotDetour b v ℓ, ∀ k : Fin (chainLen p v), z ≠ .chain v k :=
    fun z hz k h => by
      rw [mem_slotDetour_iff] at hz
      rcases hz with ⟨q, rfl, _⟩
      cases h
  dsimp only [slotVisit]
  split_ifs <;> simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.mem_append, List.not_mem_nil, not_or, not_false_eq_true, and_true]
  · refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · intro h
      have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
    · exact fun hd => hdisj _ hd _ rfl
    · intro h
      have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
    · exact fun hd => hdisj _ hd _ rfl
    · intro h
      have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
    · exact List.nodup_append.2 ⟨hdet, List.nodup_singleton _, fun z hz w hw hzw => by
        rw [List.mem_singleton] at hw; subst hw; exact hdisj z hz _ hzw⟩
  · refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact fun hd => hdisj _ hd _ rfl
    · intro h
      have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
    · intro h
      have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
    · refine List.nodup_append.2 ⟨hdet, ?_, fun z hz w hw hzw => ?_⟩
      · simp only [List.nodup_cons, List.mem_singleton, List.nodup_nil, List.not_mem_nil,
        not_false_eq_true, and_true]
        intro h
        have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> exact hdisj z hz _ hzw

private theorem slotVisit_disjoint {p : ℕ} (_hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    {ℓ₁ ℓ₂ : Fin (chainSlots p v)} (hne : ℓ₁ ≠ ℓ₂) :
    List.Disjoint (slotVisit _hp b v ℓ₁) (slotVisit _hp b v ℓ₂) := by
  intro x h₁ h₂
  rw [mem_slotVisit_iff] at h₁ h₂
  rcases h₁ with (rfl | rfl | rfl) | ⟨q₁, rfl, hq₁⟩ <;>
    rcases h₂ with (h | h | h) | ⟨q₂, h, hq₂⟩
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2)
    dsimp only at this; exact hne (Fin.ext (by omega))
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
  · cases h
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2)
    dsimp only at this; exact hne (Fin.ext (by omega))
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
  · cases h
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2); dsimp only at this; omega
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2)
    dsimp only at this; exact hne (Fin.ext (by omega))
  · cases h
  · cases h
  · cases h
  · cases h
  · obtain ⟨h1, h2⟩ := CorrDigraphV.clause.inj h
    have hq : q₁ = q₂ := Prod.ext h1 h2
    subst hq
    rw [hq₁] at hq₂
    exact hne (eq_of_heq (Sigma.mk.inj hq₂).2)

private theorem mem_varBlock_iff {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p)
    (x : CorrDigraphV p) :
    x ∈ varBlock hp b v ↔
      x = .gate v ∨
      (∃ k : Fin (chainLen p v), x = .chain v k) ∨
      (∃ q, x = .clause q.1 q.2 ∧ (clauseOwner b q).1 = v) := by
  have hrev_mem : ∀ ℓ : Fin (chainSlots p v),
      ℓ ∈ (List.finRange (chainSlots p v)).map Fin.rev := fun ℓ => by
    rw [List.mem_map]
    exact ⟨ℓ.rev, List.mem_finRange _, Fin.rev_rev ℓ⟩
  -- Both orientations visit the gate, the last chain vertex and every slot.
  have hblock : x ∈ varBlock hp b v ↔ x = .gate v ∨
      x = .chain v ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩ ∨
      ∃ ℓ, x ∈ slotVisit hp b v ℓ := by
    dsimp only [varBlock]
    split_ifs <;> simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false,
      List.mem_flatMap, List.mem_finRange, true_and, hrev_mem] <;> tauto
  simp only [hblock, mem_slotVisit_iff]
  constructor
  · rintro (rfl | rfl | ⟨ℓ, (rfl | rfl | rfl) | ⟨q, rfl, hq⟩⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inl ⟨_, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, rfl, by rw [hq]⟩)
  · rintro (rfl | ⟨k, rfl⟩ | ⟨q, rfl, hq⟩)
    · exact Or.inl rfl
    · by_cases hk : k.1 = 3 * chainSlots p v
      · exact Or.inr (Or.inl (congrArg (CorrDigraphV.chain v) (Fin.ext hk)))
      · have hk_lt : k.1 < 3 * chainSlots p v := by
          have := k.2; simp only [chainLen] at this; omega
        let ℓ : Fin (chainSlots p v) := ⟨k.1 / 3, by omega⟩
        refine Or.inr (Or.inr ⟨ℓ, Or.inl ?_⟩)
        have hcases : k.1 % 3 = 0 ∨ k.1 % 3 = 1 ∨ k.1 % 3 = 2 := by omega
        rcases hcases with h | h | h
        · left; exact congrArg (CorrDigraphV.chain v) (Fin.ext (by dsimp only [ℓ]; omega))
        · right; left; exact congrArg (CorrDigraphV.chain v) (Fin.ext (by dsimp only [ℓ]; omega))
        · right; right; exact congrArg (CorrDigraphV.chain v) (Fin.ext (by dsimp only [ℓ]; omega))
    · right; right
      rcases hco : clauseOwner b q with ⟨v', ℓ⟩
      rw [hco] at hq; dsimp only at hq; subst hq
      exact ⟨ℓ, Or.inr ⟨q, rfl, hco⟩⟩

private theorem varBlock_nodup {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p)) (v : CorrVar p) :
    (varBlock hp b v).Nodup := by
  have hfr_nd : (List.finRange (chainSlots p v)).Nodup := List.nodup_finRange _
  have hrev_nd : ((List.finRange (chainSlots p v)).map Fin.rev).Nodup :=
    hfr_nd.map Fin.rev_injective
  have hslot_nd : ∀ ℓ ∈ List.finRange (chainSlots p v), (slotVisit hp b v ℓ).Nodup :=
    fun ℓ _ => slotVisit_nodup hp b v ℓ
  have hslot_pair :
      (List.finRange (chainSlots p v)).Pairwise (fun a c => List.Disjoint (slotVisit hp b v a)
        (slotVisit hp b v c)) :=
    hfr_nd.imp (fun hne => slotVisit_disjoint hp b v hne)
  have hrev_pair :
      ((List.finRange (chainSlots p v)).map Fin.rev).Pairwise
        (fun a c => List.Disjoint (slotVisit hp b v a) (slotVisit hp b v c)) :=
    hrev_nd.imp (fun hne => slotVisit_disjoint hp b v hne)
  have hfm_nd : ((List.finRange (chainSlots p v)).flatMap (slotVisit hp b v)).Nodup :=
    List.nodup_flatMap.2 ⟨hslot_nd, hslot_pair⟩
  have hrev_fm_nd :
      (((List.finRange (chainSlots p v)).map Fin.rev).flatMap (slotVisit hp b v)).Nodup :=
    List.nodup_flatMap.2 ⟨fun ℓ _ => slotVisit_nodup hp b v ℓ, hrev_pair⟩
  have hno_end : ∀ ℓ : Fin (chainSlots p v),
      .chain v ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩ ∉ slotVisit hp b v ℓ :=
    fun ℓ h => by
      rw [mem_slotVisit_iff] at h
      rcases h with (h | h | h) | ⟨q, h, _⟩
      · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2)
        dsimp only at this; omega
      · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2)
        dsimp only at this; omega
      · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2)
        dsimp only at this; omega
      · cases h
  dsimp only [varBlock]
  split_ifs
  · refine List.nodup_append.2 ⟨?_, List.nodup_singleton _, fun z hz w hw hzw => ?_⟩
    · simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_flatMap,
      List.mem_finRange, true_and, hfm_nd, and_true]
      rintro ⟨ℓ, h⟩
      rw [mem_slotVisit_iff] at h
      rcases h with (h | h | h) | ⟨q, h, _⟩ <;> cases h
    · rw [List.mem_singleton] at hw; subst hw
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_flatMap,
        List.mem_finRange, true_and] at hz
      rcases hz with hz | ⟨ℓ, hℓ⟩
      · subst hz; cases hzw
      · exact hno_end ℓ (hzw ▸ hℓ)
  · simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.mem_flatMap,
    not_or, hrev_fm_nd, and_true]
    refine ⟨⟨(by intro h; cases h), fun ⟨ℓ, _, h⟩ => by
      rw [mem_slotVisit_iff] at h
      rcases h with (h | h | h) | ⟨q, h, _⟩ <;> cases h⟩,
      fun ⟨ℓ, _, h⟩ => hno_end ℓ h⟩

private theorem mem_of_mem_consecutivePairs {α : Type*} {l : List α} {x y : α}
    (h : (x, y) ∈ List.consecutivePairs l) : x ∈ l ∧ y ∈ l :=
  ⟨(List.of_mem_zip h).1, List.mem_of_mem_tail (List.of_mem_zip h).2⟩

private theorem chain_one_zero_not_mem_forward {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p))
    (v : CorrVar p) (hval : assignVarVal b v = false) :
    (.chain v ⟨1, by have := two_le_chainLen hp v; omega⟩,
      .chain v ⟨0, by have := two_le_chainLen hp v; omega⟩) ∉
        List.consecutivePairs (varBlock hp b v) := by
  have hs := chainSlots_pos hp v
  have hfr : List.finRange (chainSlots p v) ≠ [] := mt List.finRange_eq_nil_iff.1 hs.ne'
  intro hmem
  rw [varBlock_forward_edges hp b v hval hfr] at hmem
  rcases hmem with ⟨h1, _⟩ | hflat | ⟨_, h2⟩
  · cases h1
  · rw [List.mem_consecutivePairs_flatMap hfr (fun ℓ => slotVisit_ne_nil hp b v ℓ)] at hflat
    rcases hflat with ⟨ℓ, _, hxy⟩ | ⟨⟨ℓ₁, ℓ₂⟩, hadj, _, h2⟩
    · -- Within a forward slot visit every chain step goes up.
      dsimp only [slotVisit, slotDetour] at hxy
      simp only [hval, ↓reduceIte] at hxy
      rcases hsc : slotClause p v ℓ with _ | ql <;> simp only [hsc] at hxy <;>
        try split_ifs at hxy
      all_goals
        simp only [List.append_nil, List.cons_append, List.nil_append,
          List.consecutivePairs_cons_cons, List.consecutivePairs_singleton, List.mem_cons,
          Prod.mk.injEq, List.not_mem_nil, or_false] at hxy
        casesm* _ ∨ _ <;> obtain ⟨h1, h2⟩ := hxy <;>
          simp only [CorrDigraphV.chain.injEq, reduceCtorEq, heq_eq_eq, Fin.mk.injEq,
            true_and] at h1 h2
    · rw [head_slotVisit, hval] at h2
      simp only [↓reduceIte, CorrDigraphV.chain.injEq, heq_eq_eq] at h2
      have := congrArg Fin.val h2.2
      dsimp only at this
      have hne : ℓ₂.1 ≠ 0 := by
        rw [List.mem_consecutivePairs_iff_exists_getElem] at hadj
        obtain ⟨i, hi, _, h2'⟩ := hadj
        simp only [List.length_finRange, List.getElem_finRange] at hi h2'
        have hv2 := congrArg Fin.val h2'
        simp only [Fin.val_cast] at hv2
        omega
      omega
  · have := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h2).2)
    dsimp only at this; omega

private theorem chain_one_zero_mem_backward {p : ℕ} (hp : 1 ≤ p) (b : Finset (Fin p))
    (v : CorrVar p) (hval : assignVarVal b v = true) :
    (.chain v ⟨1, by have := two_le_chainLen hp v; omega⟩,
      .chain v ⟨0, by have := two_le_chainLen hp v; omega⟩) ∈
        List.consecutivePairs (varBlock hp b v) := by
  have hs := chainSlots_pos hp v
  have hfr : List.finRange (chainSlots p v) ≠ [] := mt List.finRange_eq_nil_iff.1 hs.ne'
  have hrev : (List.finRange (chainSlots p v)).map Fin.rev ≠ [] :=
    mt List.map_eq_nil_iff.1 hfr
  have hfm := List.flatMap_ne_nil hrev (fun ℓ _ => slotVisit_ne_nil hp b v ℓ)
  dsimp only [varBlock]
  simp only [hval, Bool.true_eq_false, ↓reduceIte]
  rw [show [.gate v, .chain v ⟨3 * chainSlots p v, _⟩] ++
      ((List.finRange (chainSlots p v)).map Fin.rev).flatMap (slotVisit hp b v) =
      ([.gate v, .chain v ⟨3 * chainSlots p v, _⟩] : List _) ++
        ((List.finRange (chainSlots p v)).map Fin.rev).flatMap (slotVisit hp b v) from rfl,
    List.consecutivePairs_append (List.cons_ne_nil _ _) hfm]
  refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
  rw [List.mem_consecutivePairs_flatMap hrev (fun ℓ => slotVisit_ne_nil hp b v ℓ)]
  left
  let ℓ₀ : Fin (chainSlots p v) := ⟨0, hs⟩
  refine ⟨ℓ₀, ?_, ?_⟩
  · rw [List.mem_map]
    exact ⟨ℓ₀.rev, List.mem_finRange _, Fin.rev_rev ℓ₀⟩
  · dsimp only [slotVisit]
    simp only [hval, Bool.true_eq_false, ↓reduceIte]
    rw [List.consecutivePairs_append (List.append_ne_nil_of_left_ne_nil (List.cons_ne_nil _ _) _)
      (List.cons_ne_nil _ _)]
    refine List.mem_append_right _ (List.mem_cons_of_mem _ ?_)
    simp only [List.consecutivePairs_cons_cons, List.consecutivePairs_singleton,
      ℓ₀, Nat.mul_zero, zero_add]
    simp

/-- Every vertex subset `b : Finset (Fin p)` (`1 ≤ p`) determines a satisfying assignment of the
correlation `3`-SAT formula and hence a directed Hamiltonian tour `τ` of `corrDigraphAdj p hp`
whose `chain v 1 → chain v 0` arcs realize `b` on diagonals and `b × b` on off-diagonals
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11, Steps (i)–(ii)]. -/
theorem exists_dirTour_of_assignment {p : ℕ} [NeZero p] (hp : 1 ≤ p) (b : Finset (Fin p)) :
    ∃ τ : Fin (Fintype.card (CorrDigraphV p)) ≃ CorrDigraphV p,
      IsDirTour (corrDigraphAdj p hp) τ ∧
      (∀ i : Fin p,
        (∃ t : Fin (Fintype.card (CorrDigraphV p)),
          τ t = .chain (.diag i) ⟨1, by have := two_le_chainLen hp (.diag i); omega⟩ ∧
          τ (t + 1) = .chain (.diag i) ⟨0, by have := two_le_chainLen hp (.diag i); omega⟩) ↔
          i ∈ b) ∧
      (∀ e : CorrPairIdx p,
        (∃ t : Fin (Fintype.card (CorrDigraphV p)),
          τ t = .chain (.off e) ⟨1, by have := two_le_chainLen hp (.off e); omega⟩ ∧
          τ (t + 1) = .chain (.off e) ⟨0, by have := two_le_chainLen hp (.off e); omega⟩) ↔
          e.fst ∈ b ∧ e.snd ∈ b) := by
  classical
  let M := Fintype.card (CorrVar p)
  have hM_pos : 0 < M := Fintype.card_pos
  have hM_ne : List.finRange M ≠ [] := mt List.finRange_eq_nil_iff.1 hM_pos.ne'
  let tourList : List (CorrDigraphV p) :=
    (List.finRange M).flatMap (fun k => varBlock hp b (varAt p k))
  have htl_ne : tourList ≠ [] :=
    List.flatMap_ne_nil hM_ne (fun k _ => varBlock_ne_nil hp b (varAt p k))
  have hdisj_v : ∀ {v₁ v₂ : CorrVar p}, v₁ ≠ v₂ →
      List.Disjoint (varBlock hp b v₁) (varBlock hp b v₂) := fun hne x hx₁ hx₂ => by
    rw [mem_varBlock_iff] at hx₁ hx₂
    rcases hx₁ with rfl | ⟨k₁, rfl⟩ | ⟨q₁, rfl, hq₁⟩ <;>
      rcases hx₂ with h | ⟨k₂, h⟩ | ⟨q₂, h, hq₂⟩
    · exact hne (CorrDigraphV.gate.inj h)
    · cases h
    · cases h
    · cases h
    · exact hne (CorrDigraphV.chain.inj h).1
    · cases h
    · cases h
    · cases h
    · obtain ⟨h1, h2⟩ := CorrDigraphV.clause.inj h
      have hq : q₁ = q₂ := Prod.ext h1 h2
      subst hq
      exact hne (hq₁.symm.trans hq₂)
  have htl_nd : tourList.Nodup := by
    refine List.nodup_flatMap.2 ⟨fun k _ => varBlock_nodup hp b (varAt p k), ?_⟩
    refine (List.nodup_finRange M).imp fun {k₁ k₂} hne => hdisj_v ?_
    intro h; exact hne ((Fintype.equivFin (CorrVar p)).symm.injective h)
  have hvar : ∀ u : CorrVar p, varAt p ((Fintype.equivFin (CorrVar p)) u) = u := fun u => by
    simp only [varAt, Equiv.symm_apply_apply]
  have htl_mem : ∀ x : CorrDigraphV p, x ∈ tourList := fun x => by
    rw [List.mem_flatMap]
    cases x with
    | gate v =>
        refine ⟨(Fintype.equivFin (CorrVar p)) v, List.mem_finRange _, ?_⟩
        rw [mem_varBlock_iff, hvar]; exact Or.inl rfl
    | chain v k =>
        refine ⟨(Fintype.equivFin (CorrVar p)) v, List.mem_finRange _, ?_⟩
        rw [mem_varBlock_iff, hvar]; exact Or.inr (Or.inl ⟨k, rfl⟩)
    | clause e c =>
        refine ⟨(Fintype.equivFin (CorrVar p)) (clauseOwner b (e, c)).1, List.mem_finRange _, ?_⟩
        rw [mem_varBlock_iff, hvar]; exact Or.inr (Or.inr ⟨(e, c), rfl, rfl⟩)
  have htoFinset : tourList.toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.2 (fun x => List.mem_toFinset.2 (htl_mem x))
  have hlen : tourList.length = Fintype.card (CorrDigraphV p) := by
    rw [← List.toFinset_card_of_nodup htl_nd, htoFinset, Finset.card_univ]
  have hlen3 : 3 ≤ tourList.length := hlen ▸ three_le_card_corrDigraphV hp
  have hlen2 : 2 ≤ tourList.length := by omega
  have : NeZero tourList.length := ⟨by omega⟩
  let τFin : Fin tourList.length ≃ CorrDigraphV p :=
    Equiv.ofBijective (fun i => tourList[i.1])
      ((Fintype.bijective_iff_injective_and_card _).2
        ⟨fun i j h => Fin.ext (htl_nd.getElem_inj_iff.1 h),
          (Fintype.card_fin tourList.length).trans hlen⟩)
  let τ : Fin (Fintype.card (CorrDigraphV p)) ≃ CorrDigraphV p :=
    (finCongr hlen.symm).trans τFin
  have hτ_apply : ∀ t : Fin (Fintype.card (CorrDigraphV p)),
      τ t = tourList[(finCongr hlen.symm t).1] := fun _ => rfl
  have hsucc : ∀ t : Fin (Fintype.card (CorrDigraphV p)),
      finCongr hlen.symm (t + 1) = finCongr hlen.symm t + 1 := fun t => by
    ext
    have h1a : (1 : Fin (Fintype.card (CorrDigraphV p))).1 = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    have h1b : (1 : Fin tourList.length).1 = 1 := by
      rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    simp only [finCongr_apply, Fin.val_cast, Fin.val_add, h1a, h1b, hlen]
  have hpair_iff : ∀ x y : CorrDigraphV p,
      (∃ t : Fin (Fintype.card (CorrDigraphV p)), τ t = x ∧ τ (t + 1) = y) ↔
        (x, y) ∈ (tourList.getLast htl_ne, tourList.head htl_ne) ::
          List.consecutivePairs tourList := by
    intro x y
    rw [← List.cyclicPairs_mem_iff tourList htl_ne hlen2]
    constructor
    · rintro ⟨t, rfl, rfl⟩
      exact ⟨finCongr hlen.symm t, rfl, by simp only [hτ_apply, hsucc]⟩
    · rintro ⟨i, rfl, rfl⟩
      refine ⟨(finCongr hlen.symm).symm i, by simp only [hτ_apply, Equiv.apply_symm_apply], ?_⟩
      simp only [hτ_apply, hsucc, Equiv.apply_symm_apply]
  have hcyc_adj : ∀ {x y : CorrDigraphV p},
      (x, y) ∈ (tourList.getLast htl_ne, tourList.head htl_ne) :: List.consecutivePairs tourList →
        corrDigraphAdj p hp x y := by
    -- Consecutive variable blocks are linked from a chain end to the next gate.
    have hlink {u w : CorrVar p} (hvn : varNext hp u = w) :
        corrDigraphAdj p hp ((varBlock hp b u).getLast (varBlock_ne_nil hp b u))
          ((varBlock hp b w).head (varBlock_ne_nil hp b w)) := by
      rw [getLast_varBlock, head_varBlock]
      split_ifs <;> simp only [corrDigraphAdj, hvn, chainLen, true_and]
      · exact Or.inr trivial
      · exact Or.inl trivial
    intro x y hmem
    rw [List.mem_cons, Prod.mk.injEq, List.mem_consecutivePairs_flatMap hM_ne
      (fun k => varBlock_ne_nil hp b (varAt p k))] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | (⟨k, _, hxy⟩ | ⟨⟨k₁, k₂⟩, hadj, rfl, rfl⟩)
    · rw [List.getLast_flatMap hM_ne (fun k _ => varBlock_ne_nil hp b (varAt p k)),
        List.head_flatMap hM_ne (fun k _ => varBlock_ne_nil hp b (varAt p k))]
      have hlast : (List.finRange M).getLast hM_ne = ⟨M - 1, by omega⟩ := by
        apply Fin.ext
        simp only [List.getLast_eq_getElem, List.length_finRange, List.getElem_finRange,
          Fin.val_cast]
      have hhead : (List.finRange M).head hM_ne = ⟨0, hM_pos⟩ := by
        apply Fin.ext
        simp only [List.head_eq_getElem, List.getElem_finRange, Fin.val_cast]
      rw [hlast, hhead]
      have hvn : varNext hp (varAt p ⟨M - 1, by omega⟩) = varAt p ⟨0, hM_pos⟩ := by
        rw [varNext_varAt]
        congr 1; ext
        by_cases hM1 : M = 1
        · have : (⟨M - 1, by omega⟩ + 1 : Fin M) = ⟨0, hM_pos⟩ := by
            ext; dsimp only; rw [Fin.val_add, Fin.val_one']
            change (M - 1 + 1 % M) % M = 0
            rw [hM1]
          exact congrArg Fin.val this
        · have h1M : (1 : Fin M).1 = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
          rw [Fin.val_add]; dsimp only
          rw [h1M, show M - 1 + 1 = M by omega, Nat.mod_self]
      exact hlink hvn
    · exact List.consecutivePairs_varBlock_mem hp b (varAt p k) hxy
    · rw [List.mem_consecutivePairs_iff_exists_getElem] at hadj
      obtain ⟨i, hi, h1, h2⟩ := hadj
      simp only [List.length_finRange, List.getElem_finRange] at hi h1 h2
      refine hlink ?_
      rw [varNext_varAt]; congr 1; ext
      have h1M : (1 : Fin M).1 = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, h1M, ← h1, ← h2]
      exact Nat.mod_eq_of_lt hi
  have h10_iff : ∀ v : CorrVar p,
      (∃ t : Fin (Fintype.card (CorrDigraphV p)),
        τ t = .chain v ⟨1, by have := two_le_chainLen hp v; omega⟩ ∧
        τ (t + 1) = .chain v ⟨0, by have := two_le_chainLen hp v; omega⟩) ↔
        assignVarVal b v = true := by
    intro v
    rw [hpair_iff]
    rw [List.mem_cons, Prod.mk.injEq, List.mem_consecutivePairs_flatMap hM_ne
      (fun k => varBlock_ne_nil hp b (varAt p k))]
    constructor
    · rintro (⟨hlast, hhead⟩ | (⟨k, _, hk⟩ | ⟨⟨k₁, k₂⟩, _, _, hhead⟩))
      · rw [List.head_flatMap hM_ne (fun k _ => varBlock_ne_nil hp b (varAt p k)), head_varBlock]
          at hhead
        cases hhead
      · have hm := (mem_of_mem_consecutivePairs hk).1
        rw [mem_varBlock_iff] at hm
        rcases hm with h | ⟨_, h⟩ | ⟨_, h, _⟩
        · cases h
        · have hv := (CorrDigraphV.chain.inj h).1
          rw [← hv] at hk
          by_cases hval : assignVarVal b v = false
          · exact absurd hk (chain_one_zero_not_mem_forward hp b v hval)
          · exact Bool.eq_true_of_not_eq_false hval
        · cases h
      · rw [head_varBlock] at hhead; cases hhead
    · intro htrue
      right; left
      refine ⟨(Fintype.equivFin (CorrVar p)) v, List.mem_finRange _, ?_⟩
      rw [hvar]
      exact chain_one_zero_mem_backward hp b v htrue
  refine ⟨τ, fun t => hcyc_adj ((hpair_iff _ _).1 ⟨t, rfl, rfl⟩), fun i => ?_, fun e => ?_⟩
  · simpa only [assignVarVal, decide_eq_true_eq] using h10_iff (.diag i)
  · simpa only [assignVarVal, decide_eq_true_eq] using h10_iff (.off e)

private theorem eq_slot_of_clauseAdj {p : ℕ} {v : CorrVar p} {ℓ ℓ' : Fin (chainSlots p v)}
    {r : ℕ} (hr : r = 1 ∨ r = 2) {c₁ c₂ : Bool} {e : CorrPairIdx p} {c : Fin 4} {lit : Bool}
    (_hs : slotClause p v ℓ' = some ((e, c), lit))
    (hk : (lit = c₁ ∧ 3 * ℓ.1 + r = 3 * ℓ'.1 + 1) ∨
      (lit = c₂ ∧ 3 * ℓ.1 + r = 3 * ℓ'.1 + 2)) :
    ℓ' = ℓ ∧ ((r = 1 ∧ lit = c₁) ∨ (r = 2 ∧ lit = c₂)) := by
  rcases hr with rfl | rfl <;> rcases hk with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact ⟨Fin.ext (by omega), Or.inl ⟨rfl, rfl⟩⟩
  · omega
  · omega
  · exact ⟨Fin.ext (by omega), Or.inr ⟨rfl, rfl⟩⟩

private theorem corrDigraphAdj_gate_out {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p)
    (x : CorrDigraphV p) :
    corrDigraphAdj p hp (.gate v) x ↔
      x = .chain v ⟨0, by have := two_le_chainLen hp v; omega⟩ ∨
      x = .chain v ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩ := by
  cases x with
  | gate _ => simp only [corrDigraphAdj, reduceCtorEq, or_self]
  | chain v' k =>
      dsimp only [corrDigraphAdj]
      constructor
      · rintro ⟨rfl, h | h⟩
        · left; exact congrArg (CorrDigraphV.chain v) (Fin.ext (by dsimp only; omega))
        · right
          exact congrArg (CorrDigraphV.chain v)
            (Fin.ext (by simp only [chainLen] at h; dsimp only; omega))
      · rintro (h | h) <;> obtain ⟨rfl, hk⟩ := CorrDigraphV.chain.inj h <;>
          have hv := congrArg Fin.val (eq_of_heq hk) <;> dsimp only at hv
        · exact ⟨rfl, Or.inl hv⟩
        · exact ⟨rfl, Or.inr (by simp only [chainLen]; omega)⟩
  | clause _ _ => simp only [corrDigraphAdj, reduceCtorEq, or_self]

/-- At an endpoint `k` of the chain of `v` (its first or last vertex) with interior neighbor `k'`,
the in-neighbors are the gate of `v` and `k'`, and the out-neighbors are the next gate and `k'`. -/
private theorem corrDigraphAdj_chainEnd {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p)
    {k k' : Fin (chainLen p v)} (hk : k.1 = 0 ∨ k.1 + 1 = chainLen p v)
    (hk' : k'.1 + 1 = k.1 ∨ k.1 + 1 = k'.1) (x : CorrDigraphV p) :
    (corrDigraphAdj p hp x (.chain v k) ↔ x = .gate v ∨ x = .chain v k') ∧
      (corrDigraphAdj p hp (.chain v k) x ↔ x = .gate (varNext hp v) ∨ x = .chain v k') := by
  have hnb (j : Fin (chainLen p v)) : (j.1 + 1 = k.1 ∨ k.1 + 1 = j.1) ↔ j = k' := by
    rw [Fin.ext_iff]
    have := j.2
    have := k'.2
    omega
  cases x with
  | gate v' =>
      simp only [corrDigraphAdj, and_iff_left hk, CorrDigraphV.gate.injEq, reduceCtorEq, or_false,
        iff_self, and_true]
      exact ⟨And.left, by rintro rfl; exact ⟨rfl, hk⟩⟩
  | chain v' j =>
      dsimp only [corrDigraphAdj]
      simp only [reduceCtorEq, false_or]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · rintro ⟨rfl, h⟩
        rw [(hnb j).1 h]
      · rintro ⟨⟩
        exact ⟨rfl, hk'⟩
      · rintro ⟨rfl, h⟩
        rw [(hnb j).1 h.symm]
      · rintro ⟨⟩
        exact ⟨rfl, hk'.symm⟩
  | clause e c =>
      simp only [corrDigraphAdj, reduceCtorEq, or_self, iff_false]
      have hℓ (ℓ : Fin (chainSlots p v)) := ℓ.2
      simp only [chainLen] at hk
      constructor <;> rintro ⟨ℓ, lit, _, ⟨_, h⟩ | ⟨_, h⟩⟩ <;> have := hℓ ℓ <;> omega

private theorem corrDigraphAdj_chain_iff {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p)
    (k k_prev k_next : Fin (chainLen p v))
    (hk_prev : k_prev.1 + 1 = k.1) (hk_next : k.1 + 1 = k_next.1)
    (hk0 : k.1 ≠ 0) (hkn : k.1 + 1 ≠ chainLen p v) (x : CorrDigraphV p) :
    (corrDigraphAdj p hp (.chain v k) x ↔
      x = .chain v k_prev ∨ x = .chain v k_next ∨
      ∃ e c, x = .clause e c ∧ corrDigraphAdj p hp (.chain v k) (.clause e c)) ∧
    (corrDigraphAdj p hp x (.chain v k) ↔
      x = .chain v k_prev ∨ x = .chain v k_next ∨
      ∃ e c, x = .clause e c ∧ corrDigraphAdj p hp (.clause e c) (.chain v k)) := by
  cases x with
  | gate v_gate =>
      simp only [corrDigraphAdj, reduceCtorEq, exists_false, false_and, or_self, iff_false]
      constructor <;>
        · rintro ⟨heq, h⟩; subst v_gate; rcases h with h | h
          · exact hk0 h
          · exact hkn h
  | chain v' k' =>
      dsimp only [corrDigraphAdj]
      simp only [reduceCtorEq, false_and, exists_false, or_false]
      have hchain : (v' = v ∧ (k'.1 + 1 = k.1 ∨ k.1 + 1 = k'.1)) ↔
          (CorrDigraphV.chain v' k' : CorrDigraphV p) = .chain v k_prev ∨
          (CorrDigraphV.chain v' k' : CorrDigraphV p) = .chain v k_next := by
        constructor
        · rintro ⟨heq, h⟩; subst v'
          rcases h with h | h
          · exact Or.inl (congrArg (CorrDigraphV.chain v) (Fin.ext (show k'.1 = k_prev.1 by omega)))
          · exact Or.inr (congrArg (CorrDigraphV.chain v) (Fin.ext (show k'.1 = k_next.1 by omega)))
        · rintro (h | h) <;> obtain ⟨heq, hk⟩ := CorrDigraphV.chain.inj h <;> subst v'
          · exact ⟨rfl, Or.inl (by have := congrArg Fin.val (eq_of_heq hk); omega)⟩
          · exact ⟨rfl, Or.inr (by have := congrArg Fin.val (eq_of_heq hk); omega)⟩
      constructor
      · exact Iff.trans
          (by exact ⟨fun ⟨heq, h⟩ => ⟨heq.symm, h.symm⟩, fun ⟨heq, h⟩ => ⟨heq.symm, h.symm⟩⟩)
          hchain
      · exact hchain
  | clause e c =>
      constructor <;>
        · constructor
          · intro h
            exact Or.inr (Or.inr ⟨e, c, And.intro rfl h⟩)
          · rintro (h | h | ⟨e', c', heq, h⟩)
            · contradiction
            · contradiction
            · injection heq with h1 h2; subst h1 h2; exact h

private theorem corrDigraphAdj_mul3 {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p)
    {j : ℕ} (hj0 : 0 < j) (hjS : j < chainSlots p v) (x : CorrDigraphV p) :
    (corrDigraphAdj p hp (.chain v ⟨3 * j, by simp only [chainLen]; omega⟩) x ↔
      x = .chain v ⟨3 * j - 1, by simp only [chainLen]; omega⟩ ∨
      x = .chain v ⟨3 * j + 1, by simp only [chainLen]; omega⟩) ∧
    (corrDigraphAdj p hp x (.chain v ⟨3 * j, by simp only [chainLen]; omega⟩) ↔
      x = .chain v ⟨3 * j - 1, by simp only [chainLen]; omega⟩ ∨
      x = .chain v ⟨3 * j + 1, by simp only [chainLen]; omega⟩) := by
  have h := corrDigraphAdj_chain_iff hp v
    ⟨3 * j, by simp only [chainLen]; omega⟩
    ⟨3 * j - 1, by simp only [chainLen]; omega⟩
    ⟨3 * j + 1, by simp only [chainLen]; omega⟩
    (by dsimp only; omega) rfl (by dsimp only; omega)
    (by dsimp only [chainLen]; omega) x
  -- No clause is attached to a multiple of three, in either direction.
  refine ⟨h.1.trans ?_, h.2.trans ?_⟩ <;>
    exact or_congr_right (or_iff_left fun ⟨_, _, _, _, _, _, h⟩ => by
      rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> dsimp only at h <;> omega)

/-- Out-neighbors of the slot vertex `k = 3ℓ + r` (`r ∈ {1, 2}`) of the chain of `v`: its chain
neighbors and the slot's clause when the slot literal is `false` (`r = 1`) or `true` (`r = 2`). -/
private theorem corrDigraphAdj_slot_out {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) {r : ℕ} (hr : r = 1 ∨ r = 2) (k kPrev kNext : Fin (chainLen p v))
    (hk : k.1 = 3 * ℓ.1 + r) (hPrev : kPrev.1 + 1 = k.1) (hNext : k.1 + 1 = kNext.1)
    (x : CorrDigraphV p) :
    corrDigraphAdj p hp (.chain v k) x ↔
      x = .chain v kPrev ∨ x = .chain v kNext ∨
      ∃ e c, slotClause p v ℓ = some ((e, c), decide (r = 2)) ∧ x = .clause e c := by
  have hℓ := ℓ.2
  rw [(corrDigraphAdj_chain_iff hp v k kPrev kNext hPrev hNext (by omega)
    (by simp only [chainLen]; omega) x).1]
  simp only [corrDigraphAdj]
  refine or_congr_right (or_congr_right ⟨?_, ?_⟩)
  · rintro ⟨e, c, rfl, ℓ', lit, hs, hk'⟩
    rw [hk] at hk'
    obtain ⟨rfl, hlit⟩ := eq_slot_of_clauseAdj hr hs hk'
    refine ⟨e, c, ?_, rfl⟩
    rcases hlit with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hs
  · rintro ⟨e, c, hs, rfl⟩
    refine ⟨e, c, rfl, ℓ, _, hs, ?_⟩
    rcases hr with rfl | rfl
    · exact Or.inl ⟨rfl, hk⟩
    · exact Or.inr ⟨rfl, hk⟩

private theorem corrDigraphAdj_slot1_out {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) (x : CorrDigraphV p) :
    corrDigraphAdj p hp (.chain v ⟨3 * ℓ.1 + 1, by simp only [chainLen]; omega⟩) x ↔
      x = .chain v ⟨3 * ℓ.1, by simp only [chainLen]; omega⟩ ∨
      x = .chain v ⟨3 * ℓ.1 + 2, by simp only [chainLen]; omega⟩ ∨
      ∃ e c, slotClause p v ℓ = some ((e, c), false) ∧ x = .clause e c := by
  refine corrDigraphAdj_slot_out hp v ℓ (.inl rfl) _ _ _ ?_ ?_ ?_ x <;> rfl

private theorem corrDigraphAdj_slot2_out {p : ℕ} (hp : 1 ≤ p) (v : CorrVar p)
    (ℓ : Fin (chainSlots p v)) (x : CorrDigraphV p) :
    corrDigraphAdj p hp (.chain v ⟨3 * ℓ.1 + 2, by simp only [chainLen]; omega⟩) x ↔
      x = .chain v ⟨3 * ℓ.1 + 1, by simp only [chainLen]; omega⟩ ∨
      x = .chain v ⟨3 * (ℓ.1 + 1), by simp only [chainLen]; omega⟩ ∨
      ∃ e c, slotClause p v ℓ = some ((e, c), true) ∧ x = .clause e c := by
  refine corrDigraphAdj_slot_out hp v ℓ (.inr rfl) _ _ _ ?_ ?_ ?_ x <;> rfl

/-- Every directed Hamiltonian tour `τ` of `corrDigraphAdj p hp` induces an assignment
`b : Finset (Fin p)` such that `chain v 1 → chain v 0` occurs in `τ` iff `v` evaluates to `true`
on `b bᵀ` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11, Steps (i)–(ii)]. -/
theorem exists_assignment_of_dirTour {p : ℕ} [NeZero p] (hp : 1 ≤ p)
    {τ : Fin (Fintype.card (CorrDigraphV p)) ≃ CorrDigraphV p}
    (hτ : IsDirTour (corrDigraphAdj p hp) τ) :
    ∃ b : Finset (Fin p),
      (∀ i : Fin p,
        (∃ t : Fin (Fintype.card (CorrDigraphV p)),
          τ t = .chain (.diag i) ⟨1, by have := two_le_chainLen hp (.diag i); omega⟩ ∧
          τ (t + 1) = .chain (.diag i) ⟨0, by have := two_le_chainLen hp (.diag i); omega⟩) ↔
          i ∈ b) ∧
      (∀ e : CorrPairIdx p,
        (∃ t : Fin (Fintype.card (CorrDigraphV p)),
          τ t = .chain (.off e) ⟨1, by have := two_le_chainLen hp (.off e); omega⟩ ∧
          τ (t + 1) = .chain (.off e) ⟨0, by have := two_le_chainLen hp (.off e); omega⟩) ↔
          e.fst ∈ b ∧ e.snd ∈ b) := by
  classical
  have h3 : 3 ≤ Fintype.card (CorrDigraphV p) := three_le_card_corrDigraphV hp
  have hnb_ne : ∀ u : CorrDigraphV p,
      τ (τ.symm u - 1) ≠ τ (τ.symm u + 1) := fun u h =>
    fin_sub_one_ne_add_one h3 (τ.symm u) (τ.injective h)
  have hpred_adj : ∀ u : CorrDigraphV p, corrDigraphAdj p hp (τ (τ.symm u - 1)) u := fun u => by
    have h := hτ (τ.symm u - 1)
    rwa [sub_add_cancel, τ.apply_symm_apply] at h
  have hsucc_adj : ∀ u : CorrDigraphV p, corrDigraphAdj p hp u (τ (τ.symm u + 1)) := fun u => by
    have h := hτ (τ.symm u)
    rwa [τ.apply_symm_apply] at h
  have hprev_of_next : ∀ {x y : CorrDigraphV p},
      τ (τ.symm x + 1) = y → τ (τ.symm y - 1) = x := fun {x y} h => by
    have heq : τ.symm y = τ.symm x + 1 := τ.symm_apply_eq.2 h.symm
    rw [heq, add_sub_cancel_right, τ.apply_symm_apply]
  have hnext_of_prev : ∀ {x y : CorrDigraphV p},
      τ (τ.symm y - 1) = x → τ (τ.symm x + 1) = y := fun {x y} h => by
    have heq : τ.symm x = τ.symm y - 1 := τ.symm_apply_eq.2 h.symm
    rw [heq, sub_add_cancel, τ.apply_symm_apply]
  -- The top two vertices of the last slot are the last two vertices of the chain.
  have hlast_eq : ∀ (v : CorrVar p) (ℓ : ℕ) (_h : ℓ + 1 = chainSlots p v),
      (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩ : CorrDigraphV p) =
          .chain v ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩ ∧
        (.chain v ⟨3 * ℓ + 2, by simp only [chainLen]; omega⟩ : CorrDigraphV p) =
          .chain v ⟨3 * chainSlots p v - 1, by
            have := chainSlots_pos hp v; simp only [chainLen]; omega⟩ :=
    fun v ℓ h => ⟨congrArg (CorrDigraphV.chain v) (Fin.ext (by dsimp only; omega)),
      congrArg (CorrDigraphV.chain v) (Fin.ext (by dsimp only; omega))⟩
  have hchain0_dich : ∀ v : CorrVar p,
      let c0 : CorrDigraphV p := .chain v ⟨0, by have := two_le_chainLen hp v; omega⟩
      let c1 : CorrDigraphV p := .chain v ⟨1, by have := two_le_chainLen hp v; omega⟩
      let cL : CorrDigraphV p := .chain v ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩
      let cLm : CorrDigraphV p := .chain v ⟨3 * chainSlots p v - 1, by
        have := chainSlots_pos hp v; simp only [chainLen]; omega⟩
      (τ (τ.symm c0 - 1) = .gate v ∧ τ (τ.symm c0 + 1) = c1 ∧
       τ (τ.symm cL - 1) = cLm ∧ τ (τ.symm cL + 1) = .gate (varNext hp v)) ∨
      (τ (τ.symm c0 - 1) = c1 ∧ τ (τ.symm c0 + 1) = .gate (varNext hp v) ∧
       τ (τ.symm cL - 1) = .gate v ∧ τ (τ.symm cL + 1) = cLm) := by
    intro v c0 c1 cL cLm
    have hc0_ne_cL : c0 ≠ cL := fun h => by
      have hv := congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj h).2)
      have hs := chainSlots_pos hp v; dsimp only at hv; omega
    have hc0 := corrDigraphAdj_chainEnd hp v
      (k := ⟨0, by have := two_le_chainLen hp v; omega⟩)
      (k' := ⟨1, by have := two_le_chainLen hp v; omega⟩) (.inl rfl) (.inr rfl)
    have hcL := corrDigraphAdj_chainEnd hp v
      (k := ⟨3 * chainSlots p v, by simp only [chainLen]; omega⟩)
      (k' := ⟨3 * chainSlots p v - 1, by have := chainSlots_pos hp v; simp only [chainLen]; omega⟩)
      (.inr (by simp only [chainLen])) (.inl (by have := chainSlots_pos hp v; dsimp only; omega))
    have hc0_in := (hc0 _).1.1 (hpred_adj c0)
    have hc0_out := (hc0 _).2.1 (hsucc_adj c0)
    have hcL_in := (hcL _).1.1 (hpred_adj cL)
    have hcL_out := (hcL _).2.1 (hsucc_adj cL)
    have hg_out := (corrDigraphAdj_gate_out hp v _).1 (hsucc_adj (.gate v))
    have hbranch : ∀ {a aN b bN : CorrDigraphV p}, a ≠ b →
        τ (τ.symm (.gate v) + 1) = a →
        (τ (τ.symm a + 1) = .gate (varNext hp v) ∨ τ (τ.symm a + 1) = aN) →
        (τ (τ.symm b - 1) = .gate v ∨ τ (τ.symm b - 1) = bN) →
        (τ (τ.symm b + 1) = .gate (varNext hp v) ∨ τ (τ.symm b + 1) = bN) →
        τ (τ.symm a - 1) = .gate v ∧ τ (τ.symm a + 1) = aN ∧
          τ (τ.symm b - 1) = bN ∧ τ (τ.symm b + 1) = .gate (varNext hp v) := by
      intro a aN b bN hab hg ha_out hb_in hb_out
      have hta_in : τ (τ.symm a - 1) = .gate v := hprev_of_next hg
      have htb_in_ne : τ (τ.symm b - 1) ≠ .gate v := fun hb => by
        have ht_eq := congrArg (· + 1) (τ.injective (hta_in.trans hb.symm))
        rw [sub_add_cancel, sub_add_cancel] at ht_eq
        exact hab (τ.symm.injective ht_eq)
      have htb_in : τ (τ.symm b - 1) = bN := hb_in.resolve_left htb_in_ne
      have hta_out : τ (τ.symm a + 1) = aN := by
        refine ha_out.resolve_left fun h => ?_
        have htb_out_ne : τ (τ.symm b + 1) ≠ .gate (varNext hp v) := fun hb => by
          have ht_eq := congrArg (· - 1) (τ.injective (h.trans hb.symm))
          rw [add_sub_cancel_right, add_sub_cancel_right] at ht_eq
          exact hab (τ.symm.injective ht_eq)
        exact hnb_ne b (htb_in.trans (hb_out.resolve_left htb_out_ne).symm)
      have htb_out : τ (τ.symm b + 1) = .gate (varNext hp v) :=
        hb_out.resolve_right fun h => hnb_ne b (htb_in.trans h.symm)
      exact ⟨hta_in, hta_out, htb_in, htb_out⟩
    rcases hg_out with hg | hg
    · exact Or.inl (hbranch hc0_ne_cL hg hc0_out hcL_in hcL_out)
    · obtain ⟨htL_in, htL_out, ht0_in, ht0_out⟩ :=
        hbranch hc0_ne_cL.symm hg hcL_out hc0_in hc0_out
      exact Or.inr ⟨ht0_in, ht0_out, htL_in, htL_out⟩
  have hno_clash : ∀ (v : CorrVar p) (ℓ : ℕ) (hℓ : ℓ < chainSlots p v),
      let c0 : CorrDigraphV p := .chain v ⟨3 * ℓ, by simp only [chainLen]; omega⟩
      let c1 : CorrDigraphV p := .chain v ⟨3 * ℓ + 1, by simp only [chainLen]; omega⟩
      let c2 : CorrDigraphV p := .chain v ⟨3 * ℓ + 2, by simp only [chainLen]; omega⟩
      let c3 : CorrDigraphV p := .chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩
      τ (τ.symm c1 - 1) = c0 → τ (τ.symm c2 - 1) = c3 → False := by
    intro v ℓ hℓ c0 c1 c2 c3 hc1_in hc2_in
    have h1out := (corrDigraphAdj_slot1_out hp v ⟨ℓ, hℓ⟩ _).1 (hsucc_adj c1)
    have h2out := (corrDigraphAdj_slot2_out hp v ⟨ℓ, hℓ⟩ _).1 (hsucc_adj c2)
    rcases h1out with h | h | ⟨e₁, d₁, hs₁, _⟩
    · exact hnb_ne c1 (hc1_in.trans h.symm)
    · have hc2_in' := hprev_of_next h
      have hne :=
        congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj (hc2_in.symm.trans hc2_in')).2)
      dsimp only at hne; omega
    · rcases h2out with h | h | ⟨e₂, d₂, hs₂, _⟩
      · have hc1_in' := hprev_of_next h
        have hne :=
          congrArg Fin.val (eq_of_heq (CorrDigraphV.chain.inj (hc1_in.symm.trans hc1_in')).2)
        dsimp only at hne; omega
      · exact hnb_ne c2 (hc2_in.trans h.symm)
      · have heq := hs₁.symm.trans hs₂
        cases heq
  let isFwd (v : CorrVar p) : Prop :=
    τ (τ.symm (.chain v ⟨0, by have := two_le_chainLen hp v; omega⟩) + 1) =
      .chain v ⟨1, by have := two_le_chainLen hp v; omega⟩
  have hdich_fwd (v : CorrVar p) (hf : isFwd v) :=
    (hchain0_dich v).resolve_right fun h => by cases hf.symm.trans h.2.1
  have hdich_bwd (v : CorrVar p) (hnf : ¬ isFwd v) :=
    (hchain0_dich v).resolve_left fun h => hnf h.2.1
  have hslot_fwd : ∀ (v : CorrVar p) (hf : isFwd v) (ℓ : ℕ) (hℓ : ℓ < chainSlots p v),
      let c0 : CorrDigraphV p := .chain v ⟨3 * ℓ, by simp only [chainLen]; omega⟩
      let c2 : CorrDigraphV p := .chain v ⟨3 * ℓ + 2, by simp only [chainLen]; omega⟩
      let c1 : CorrDigraphV p := .chain v ⟨3 * ℓ + 1, by simp only [chainLen]; omega⟩
      let c3 : CorrDigraphV p := .chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩
      τ (τ.symm c0 + 1) = c1 ∧ τ (τ.symm c2 + 1) = c3 := by
    intro v hf ℓ
    have hc2_of_c0 : ∀ (ℓ' : ℕ) (hℓ' : ℓ' < chainSlots p v),
        τ (τ.symm (.chain v ⟨3 * ℓ', by simp only [chainLen]; omega⟩) + 1) =
          .chain v ⟨3 * ℓ' + 1, by simp only [chainLen]; omega⟩ →
        τ (τ.symm (.chain v ⟨3 * ℓ' + 2, by simp only [chainLen]; omega⟩) + 1) =
          .chain v ⟨3 * (ℓ' + 1), by simp only [chainLen]; omega⟩ := by
      intro ℓ' hℓ' hc0_out
      have hc1_in := hprev_of_next hc0_out
      by_cases hlast : ℓ' + 1 = chainSlots p v
      · have hL : τ (τ.symm (.chain v ⟨3 * chainSlots p v,
            by simp only [chainLen]; omega⟩) - 1) =
            .chain v ⟨3 * chainSlots p v - 1, by
              have := chainSlots_pos hp v; simp only [chainLen]; omega⟩ := by
          exact (hdich_fwd v hf).2.2.1
        rw [(hlast_eq v ℓ' hlast).1, (hlast_eq v ℓ' hlast).2]
        exact hnext_of_prev hL
      · have hj0 : 0 < ℓ' + 1 := Nat.succ_pos ℓ'
        have hjS : ℓ' + 1 < chainSlots p v := by omega
        have hc3_in := (corrDigraphAdj_mul3 hp v hj0 hjS _).2.1
          (hpred_adj (.chain v ⟨3 * (ℓ' + 1), by simp only [chainLen]; omega⟩))
        have hc3_out := (corrDigraphAdj_mul3 hp v hj0 hjS _).1.1
          (hsucc_adj (.chain v ⟨3 * (ℓ' + 1), by simp only [chainLen]; omega⟩))
        have hc2_eq : (.chain v ⟨3 * ℓ' + 2, by simp only [chainLen]; omega⟩ :
            CorrDigraphV p) =
            .chain v ⟨3 * (ℓ' + 1) - 1, by simp only [chainLen]; omega⟩ :=
          congrArg (CorrDigraphV.chain v) (Fin.ext (by dsimp only; omega))
        rw [hc2_eq]
        rcases hc3_in with h | h
        · exact hnext_of_prev h
        · exfalso
          rcases hc3_out with h' | h'
          · exact hno_clash v ℓ' hℓ' hc1_in (hc2_eq ▸ hprev_of_next h')
          · exact hnb_ne (.chain v ⟨3 * (ℓ' + 1), by simp only [chainLen]; omega⟩)
              (h.trans h'.symm)
    induction ℓ with
    | zero =>
        intro hℓ
        refine ⟨hf, hc2_of_c0 0 hℓ hf⟩
    | succ ℓ ih =>
        intro hℓ
        have hprev := (ih (by omega)).2
        have h0_in : τ (τ.symm (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩) - 1) =
            .chain v ⟨3 * ℓ + 2, by simp only [chainLen]; omega⟩ := hprev_of_next hprev
        have h0_out_raw := (corrDigraphAdj_mul3 hp v (Nat.succ_pos ℓ) hℓ _).1.1
          (hsucc_adj (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩))
        have hc0_out : τ (τ.symm (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩) + 1) =
            .chain v ⟨3 * (ℓ + 1) + 1, by simp only [chainLen]; omega⟩ := by
          rcases h0_out_raw with h | h
          · exfalso
            have hm_eq : (.chain v ⟨3 * (ℓ + 1) - 1, by simp only [chainLen]; omega⟩ :
                CorrDigraphV p) =
                .chain v ⟨3 * ℓ + 2, by simp only [chainLen]; omega⟩ :=
              congrArg (CorrDigraphV.chain v) (Fin.ext (by dsimp only; omega))
            exact hnb_ne (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩)
              (h0_in.trans (hm_eq ▸ h).symm)
          · exact h
        exact ⟨hc0_out, hc2_of_c0 (ℓ + 1) hℓ hc0_out⟩
  have hslot_bwd : ∀ (v : CorrVar p) (hnf : ¬ isFwd v) (d ℓ : ℕ)
      (hd : ℓ + d + 1 = chainSlots p v),
      let c1 : CorrDigraphV p := .chain v ⟨3 * ℓ + 1, by simp only [chainLen]; omega⟩
      let c0 : CorrDigraphV p := .chain v ⟨3 * ℓ, by simp only [chainLen]; omega⟩
      τ (τ.symm (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩) + 1) =
        .chain v ⟨3 * ℓ + 2, by simp only [chainLen]; omega⟩ ∧
      τ (τ.symm c1 + 1) = c0 := by
    intro v hnf d
    have hc1_of_c3 : ∀ (ℓ' : ℕ) (hℓ' : ℓ' < chainSlots p v),
        τ (τ.symm (.chain v ⟨3 * (ℓ' + 1), by simp only [chainLen]; omega⟩) + 1) =
          .chain v ⟨3 * ℓ' + 2, by simp only [chainLen]; omega⟩ →
        τ (τ.symm (.chain v ⟨3 * ℓ' + 1, by simp only [chainLen]; omega⟩) + 1) =
          .chain v ⟨3 * ℓ', by simp only [chainLen]; omega⟩ := by
      intro ℓ' hℓ' hc3_out
      have hc2_in := hprev_of_next hc3_out
      rcases Nat.eq_zero_or_pos ℓ' with rfl | hpos
      · exact hnext_of_prev (hdich_bwd v hnf).1
      · have hc0_in_raw := (corrDigraphAdj_mul3 hp v hpos hℓ' _).2.1
          (hpred_adj (.chain v ⟨3 * ℓ', by simp only [chainLen]; omega⟩))
        have hc0_out_raw := (corrDigraphAdj_mul3 hp v hpos hℓ' _).1.1
          (hsucc_adj (.chain v ⟨3 * ℓ', by simp only [chainLen]; omega⟩))
        have hc0_in : τ (τ.symm (.chain v ⟨3 * ℓ', by simp only [chainLen]; omega⟩) - 1) =
            .chain v ⟨3 * ℓ' + 1, by simp only [chainLen]; omega⟩ := by
          rcases hc0_in_raw with h | h
          · exfalso
            rcases hc0_out_raw with h' | h'
            · exact hnb_ne (.chain v ⟨3 * ℓ', by simp only [chainLen]; omega⟩)
                (h.trans h'.symm)
            · exact hno_clash v ℓ' hℓ' (hprev_of_next h') hc2_in
          · exact h
        exact hnext_of_prev hc0_in
    induction d with
    | zero =>
        intro ℓ hd
        have hc3_out : τ (τ.symm (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩) + 1) =
            .chain v ⟨3 * ℓ + 2, by simp only [chainLen]; omega⟩ := by
          rw [(hlast_eq v ℓ (by omega)).1, (hlast_eq v ℓ (by omega)).2]
          exact (hdich_bwd v hnf).2.2.2
        exact ⟨hc3_out, hc1_of_c3 ℓ (by omega) hc3_out⟩
    | succ d ih =>
        intro ℓ hd
        have hnext_slot := (ih (ℓ + 1) (by omega)).2
        have hj0 : 0 < ℓ + 1 := Nat.succ_pos ℓ
        have hjS : ℓ + 1 < chainSlots p v := by omega
        have h_in : τ (τ.symm (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩) - 1) =
            .chain v ⟨3 * (ℓ + 1) + 1, by simp only [chainLen]; omega⟩ :=
          hprev_of_next hnext_slot
        have h_out_raw := (corrDigraphAdj_mul3 hp v hj0 hjS _).1.1
          (hsucc_adj (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩))
        have hc3_out : τ (τ.symm (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩) + 1) =
            .chain v ⟨3 * ℓ + 2, by simp only [chainLen]; omega⟩ := by
          rcases h_out_raw with h | h
          · have hm_eq : (.chain v ⟨3 * (ℓ + 1) - 1, by simp only [chainLen]; omega⟩ :
                CorrDigraphV p) =
                .chain v ⟨3 * ℓ + 2, by simp only [chainLen]; omega⟩ :=
              congrArg (CorrDigraphV.chain v) (Fin.ext (by dsimp only; omega))
            exact hm_eq ▸ h
          · exfalso
            exact hnb_ne (.chain v ⟨3 * (ℓ + 1), by simp only [chainLen]; omega⟩)
              (h_in.trans h.symm)
        exact ⟨hc3_out, hc1_of_c3 ℓ (by omega) hc3_out⟩
  have hrev_iff : ∀ v : CorrVar p,
      (∃ t : Fin (Fintype.card (CorrDigraphV p)),
        τ t = .chain v ⟨1, by have := two_le_chainLen hp v; omega⟩ ∧
        τ (t + 1) = .chain v ⟨0, by have := two_le_chainLen hp v; omega⟩) ↔
        ¬ isFwd v := by
    intro v
    constructor
    · rintro ⟨t, ht1, ht0⟩ hf
      have h0_in := hprev_of_next (show τ (τ.symm (τ t) + 1) =
          .chain v ⟨0, by have := two_le_chainLen hp v; omega⟩ by
        simpa only [τ.symm_apply_apply] using ht0)
      rw [ht1] at h0_in
      cases (hdich_fwd v hf).1.symm.trans h0_in
    · intro hnf
      refine ⟨τ.symm (.chain v ⟨0, by have := two_le_chainLen hp v; omega⟩) - 1,
        (hdich_bwd v hnf).1, ?_⟩
      rw [sub_add_cancel, τ.apply_symm_apply]
  let b : Finset (Fin p) := Finset.univ.filter (fun i => ¬ isFwd (.diag i))
  refine ⟨b, ?_, ?_⟩
  · intro i
    refine (hrev_iff (.diag i)).trans ?_
    simp only [b, Finset.mem_filter, Finset.mem_univ, true_and]
  · intro e
    have hsat : ∀ c : Fin 4,
        decide (¬ isFwd (.diag e.fst)) = clauseLit₁ c ∨
        decide (¬ isFwd (.diag e.snd)) = clauseLit₂ c ∨
        decide (¬ isFwd (.off e)) = clauseLit₃ c := by
      intro c
      have hcl := hpred_adj (.clause e c)
      cases hu : τ (τ.symm (.clause e c) - 1) with
      | gate _ => rw [hu] at hcl; cases hcl
      | clause _ _ => rw [hu] at hcl; cases hcl
      | chain v k =>
          rw [hu] at hcl
          rcases hcl with ⟨ℓ, lit, hsc, hk⟩
          have hnext := hnext_of_prev hu
          have hval : decide (¬ isFwd v) = lit := by
            by_cases hf : isFwd v
            · have hc2 := (hslot_fwd v hf ℓ.1 ℓ.2).2
              have hlit : lit = false := by
                rcases hk with ⟨rfl, _⟩ | ⟨rfl, hk2⟩
                · rfl
                · exfalso
                  have hkeq : (.chain v k : CorrDigraphV p) =
                      .chain v ⟨3 * ℓ.1 + 2, by simp only [chainLen]; omega⟩ :=
                    congrArg (CorrDigraphV.chain v) (Fin.ext hk2)
                  rw [hkeq] at hnext
                  cases hnext.symm.trans hc2
              simp only [hf, not_true_eq_false, decide_false, hlit]
            · have hc1 := (hslot_bwd v hf (chainSlots p v - 1 - ℓ.1) ℓ.1
                (by have := ℓ.2; omega)).2
              have hlit : lit = true := by
                rcases hk with ⟨rfl, hk1⟩ | ⟨rfl, _⟩
                · exfalso
                  have hkeq : (.chain v k : CorrDigraphV p) =
                      .chain v ⟨3 * ℓ.1 + 1, by simp only [chainLen]; omega⟩ :=
                    congrArg (CorrDigraphV.chain v) (Fin.ext hk1)
                  rw [hkeq] at hnext
                  cases hnext.symm.trans hc1
                · rfl
              simp only [hf, not_false_eq_true, decide_true, hlit]
          rw [slotClause_eq_some_iff] at hsc
          rcases hsc with ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
          · exact Or.inl hval
          · exact Or.inr (Or.inl hval)
          · exact Or.inr (Or.inr hval)
    have heq := (forall_clause_iff_eq_and _ _ _).1 hsat
    refine (hrev_iff (.off e)).trans ?_
    rw [← decide_eq_true_iff (p := ¬ isFwd (.off e)), heq, Bool.and_eq_true,
      decide_eq_true_iff, decide_eq_true_iff]
    simp only [b, Finset.mem_filter, Finset.mem_univ, true_and]
