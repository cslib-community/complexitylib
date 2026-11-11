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

private def corrVarEquivSum (p : ℕ) : CorrVar p ≃ Fin p ⊕ CorrPairIdx p where
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
  let e := Fintype.equivFin (CorrVar p)
  e.symm (e v + 1)

theorem varNext_bijective {p : ℕ} (hp : 1 ≤ p) : Function.Bijective (varNext hp) := by
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

private def corrDigraphVEquiv (p : ℕ) :
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
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, two_mul] at hle
    nlinarith
  rw [Fintype.card_congr (corrDigraphVEquiv p), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_congr (corrVarEquivSum p), Fintype.card_sum, Fintype.card_fin,
    Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  have hsig : ∑ v : CorrVar p, Fintype.card (Fin (chainLen p v)) =
      p * (12 * p + 1) + Fintype.card (CorrPairIdx p) * 13 := by
    rw [Fintype.sum_equiv (corrVarEquivSum p) _ (Sum.elim (fun _ => 12 * p + 1) (fun _ => 13))
      fun x => by cases x <;> simp [corrVarEquivSum, chainLen, chainSlots]]
    simp only [Fintype.sum_sum_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  rw [hsig]
  have hp2 : p ≤ p ^ 2 := by nlinarith
  nlinarith

theorem two_le_card_corrDigraphV {p : ℕ} (hp : 1 ≤ p) : 2 ≤ Fintype.card (CorrDigraphV p) := by
  let i0 : Fin p := ⟨0, hp⟩
  have h := Fintype.card_le_of_injective
    (fun k : Fin (chainLen p (.diag i0)) => CorrDigraphV.chain (.diag i0) k)
    (fun k₁ k₂ he => by cases he; rfl)
  rw [Fintype.card_fin] at h
  exact (two_le_chainLen hp (.diag i0)).trans h

/-- Polarity of literal 1 (`C_{ii}`), literal 2 (`C_{jj}`), and literal 3 (`C_{ij}`) in the
four clauses enforcing `C_{ij} = C_{ii} ∧ C_{jj}` [FioriniMassarPokuttaTiwaryDeWolf2015, Step (i)]. -/
@[expose] def clauseLit₁ : Fin 4 → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => false

@[expose] def clauseLit₂ : Fin 4 → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => true

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
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    cases bi <;> cases bj <;> cases be <;>
      simp only [clauseLit₁, clauseLit₂, clauseLit₃, Bool.and_true, Bool.and_false,
        Bool.false_and] at h0 h1 h2 h3 ⊢ <;> decide
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
      (v = .diag e.fst ∧ ℓ.1 = 4 * e.snd.1 + c.1 ∧ lit = clauseLit₁ c) ∨
      (v = .diag e.snd ∧ ℓ.1 = 4 * e.fst.1 + c.1 ∧ lit = clauseLit₂ c) ∨
      (v = .off e ∧ ℓ.1 = c.1 ∧ lit = clauseLit₃ c) := by
  cases v with
  | diag i =>
      dsimp only [slotClause]
      have hdiv : ℓ.1 = 4 * (ℓ.1 / 4) + ℓ.1 % 4 := by omega
      split_ifs with h1 h2
      · simp only [Option.some.injEq, Prod.mk.injEq, CorrVar.diag.injEq, reduceCtorEq, false_and,
          or_false]
        constructor
        · rintro ⟨⟨he, hc⟩, rfl⟩
          left
          have he1 : e = ⟨i, ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩, h1⟩ :=
            he.symm
          subst he1 hc
          exact ⟨rfl, hdiv, rfl⟩
        · rintro (⟨rfl, hl, rfl⟩ | ⟨rfl, hl, rfl⟩)
          · have hj : ℓ.1 / 4 = e.snd.1 := by omega
            have hc : ℓ.1 % 4 = c.1 := by omega
            have he' : (⟨e.fst, ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩,
                h1⟩ : CorrPairIdx p) = e := by
              cases e; simp only [CorrPairIdx.mk.injEq, Fin.ext_iff, true_and]; exact hj
            exact ⟨⟨he', Fin.ext hc⟩, rfl⟩
          · exfalso
            have hj : ℓ.1 / 4 = e.fst.1 := by omega
            have hlt : e.fst.1 < e.snd.1 := e.lt
            have hlt1 : e.snd.1 < ℓ.1 / 4 := h1
            omega
      · simp only [Option.some.injEq, Prod.mk.injEq, CorrVar.diag.injEq, reduceCtorEq, false_and,
          or_false]
        constructor
        · rintro ⟨⟨he, hc⟩, rfl⟩
          right
          have he1 : e = ⟨⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩, i, h2⟩ :=
            he.symm
          subst he1 hc
          exact ⟨rfl, hdiv, rfl⟩
        · rintro (⟨rfl, hl, rfl⟩ | ⟨rfl, hl, rfl⟩)
          · exfalso
            have hj : ℓ.1 / 4 = e.snd.1 := by omega
            have hlt : e.fst.1 < e.snd.1 := e.lt
            have hnot : ¬ e.fst < ⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩ := h1
            exact hnot (by simpa only [Fin.lt_def, hj] using hlt)
          · have hj : ℓ.1 / 4 = e.fst.1 := by omega
            have hc : ℓ.1 % 4 = c.1 := by omega
            have he' : (⟨⟨ℓ.1 / 4, by have := ℓ.2; simp only [chainSlots] at this; omega⟩, e.snd,
                h2⟩ : CorrPairIdx p) = e := by
              cases e; simp only [CorrPairIdx.mk.injEq, Fin.ext_iff, and_true]; exact hj
            exact ⟨⟨he', Fin.ext hc⟩, rfl⟩
      · simp only [reduceCtorEq, CorrVar.diag.injEq, false_iff, not_or, not_and]
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
      simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, false_or,
        CorrVar.off.injEq]
      constructor
      · rintro ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, hc, rfl⟩
        exact ⟨⟨rfl, Fin.ext hc⟩, rfl⟩

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
