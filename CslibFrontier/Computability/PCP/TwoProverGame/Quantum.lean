/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame
public import CslibFrontier.Foundations.Quantum.POVM
import CslibFrontier.Probability.PMF.Event

/-!
# Entangled strategies for two-prover one-round games

A *quantum strategy* for a two-prover one-round game in the finite-dimensional tensor-product
model [Cleve, Høyer, Toner, Watrous, §2][CleveHoyerTonerWatrous2004] consists of a shared unit
state `ψ ∈ ℂ^ι ⊗ ℂ^κ`, a POVM `{X_x^a}_a` on `ℂ^ι` for each question `x` of Alice, and a POVM
`{Y_y^b}_b` on `ℂ^κ` for each question `y` of Bob (`Cslib.PCP.QuantumStrategy`). On questions
`(x, y)` the answers are `(a, b)` with probability `⟨ψ|X_x^a ⊗ Y_y^b|ψ⟩`
(`Cslib.PCP.QuantumStrategy.answers`), and the winning probability is
`∑_{x,y} π(x,y) ∑_{a,b} ⟨ψ|X_x^a ⊗ Y_y^b|ψ⟩ V(a,b|x,y)`
(`Cslib.PCP.TwoProverGame.quantumWinProb`, `Cslib.PCP.TwoProverGame.quantumWinProb_eq_sum`).

The *entangled value* `ω*(G)` is the supremum of the winning probability over all finite
dimensions (`Cslib.PCP.TwoProverGame.quantumValue`). Strategies on any finite index types are
bounded by it, by relabelling the bases (`Cslib.PCP.TwoProverGame.quantumWinProb_le_quantumValue`).
A deterministic classical strategy is the quantum strategy with one-dimensional systems and
constant measurements (`Cslib.PCP.QuantumStrategy.ofDeterministic`), so
`value G ≤ quantumValue G` (`Cslib.PCP.TwoProverGame.value_le_quantumValue`).

[Cleve, Høyer, Toner, Watrous, §2][CleveHoyerTonerWatrous2004] give both parties copies of the
same space `ℂⁿ`; `quantumValue` lets the two dimensions differ. The two suprema are equal (pad the
smaller space), but only the inequality `value_le_quantumValue` and upper bounds on `quantumValue`
are used here. The shared state is pure, as in the source; the commuting-operator model is not
formalized.

## Main definitions

* `Cslib.PCP.QuantumStrategy`: a quantum strategy in the tensor-product model.
* `Cslib.PCP.QuantumStrategy.answers`, `Cslib.PCP.QuantumStrategy.prob`: the distribution of the
  answers on given questions.
* `Cslib.PCP.QuantumStrategy.ofDeterministic`: a deterministic strategy as a quantum strategy.
* `Cslib.PCP.QuantumStrategy.reindex`: relabelling the bases of the two systems.
* `Cslib.PCP.TwoProverGame.quantumWinProb`: the winning probability of a quantum strategy.
* `Cslib.PCP.TwoProverGame.quantumValue`: the entangled value of a game.

## Main results

* `Cslib.PCP.TwoProverGame.quantumWinProb_eq_sum`: the winning probability as an explicit sum.
* `Cslib.PCP.TwoProverGame.quantumWinProb_ofDeterministic`: the quantum embedding of a
  deterministic strategy wins with its classical probability.
* `Cslib.PCP.TwoProverGame.quantumWinProb_le_quantumValue`,
  `Cslib.PCP.TwoProverGame.quantumValue_le`: `quantumValue` is the least upper bound.
* `Cslib.PCP.TwoProverGame.value_le_quantumValue`: entanglement does not hurt.

## References

* [R. Cleve, P. Høyer, B. Toner, J. Watrous, *Consequences and limits of nonlocal
  strategies*][CleveHoyerTonerWatrous2004]
-/

@[expose] public section

namespace Cslib.PCP

open Matrix Quantum
open scoped Kronecker

/-- A **quantum strategy** for a game with questions `X`, `Y` and answers `A`, `B` in the
finite-dimensional tensor-product model
[Cleve, Høyer, Toner, Watrous, §2][CleveHoyerTonerWatrous2004]: a shared unit state on
`ℂ^ι ⊗ ℂ^κ`, and a POVM on Alice's (Bob's) system for each of her (his) questions. -/
structure QuantumStrategy (X Y A B ι κ : Type*) [Fintype A] [Fintype B] [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] where
  /-- The shared state. -/
  state : EuclideanSpace ℂ (ι × κ)
  /-- The shared state is a unit vector. -/
  norm_state : ‖state‖ = 1
  /-- Alice's measurement on question `x`. -/
  alice : X → POVM A ι
  /-- Bob's measurement on question `y`. -/
  bob : Y → POVM B κ

namespace QuantumStrategy

variable {X Y A B ι κ ι' κ' : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The distribution of the answers on questions `(x, y)`: the outcome of measuring the shared
state with `X_x ⊗ Y_y`. -/
noncomputable def answers (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) : PMF (A × B) :=
  ((S.alice x).kronecker (S.bob y)).measure S.state S.norm_state

theorem answers_apply (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) (a : A) (b : B) :
    S.answers x y (a, b) = ENNReal.ofReal
      (star S.state.ofLp ⬝ᵥ (((S.alice x).effect a ⊗ₖ (S.bob y).effect b) *ᵥ S.state.ofLp)).re :=
  rfl

/-- The probability `⟨ψ|X_x^a ⊗ Y_y^b|ψ⟩` that the players answer `(a, b)` on questions `(x, y)`:
the outcome probability of the product POVM. -/
noncomputable def prob (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  ((S.alice x).kronecker (S.bob y)).prob S.state (a, b)

theorem prob_eq (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) (a : A) (b : B) :
    S.prob x y a b =
      (star S.state.ofLp ⬝ᵥ (((S.alice x).effect a ⊗ₖ (S.bob y).effect b) *ᵥ S.state.ofLp)).re :=
  rfl

theorem prob_nonneg (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) (a : A) (b : B) :
    0 ≤ S.prob x y a b :=
  POVM.prob_nonneg _ _ _

theorem sum_prob (S : QuantumStrategy X Y A B ι κ) (x : X) (y : Y) :
    ∑ a, ∑ b, S.prob x y a b = 1 := by
  have h := ((S.alice x).kronecker (S.bob y)).sum_prob S.state
  rw [S.norm_state, one_pow, Fintype.sum_prod_type] at h
  exact h

/-- The deterministic strategy `(ha, hb)` as a quantum strategy on one-dimensional systems. -/
noncomputable def ofDeterministic [DecidableEq A] [DecidableEq B] (ha : X → A) (hb : Y → B) :
    QuantumStrategy X Y A B (Fin 1) (Fin 1) where
  state := EuclideanSpace.single (0, 0) 1
  norm_state := by simp
  alice x := POVM.const (ha x)
  bob y := POVM.const (hb y)

theorem answers_ofDeterministic [DecidableEq A] [DecidableEq B] (ha : X → A) (hb : Y → B)
    (x : X) (y : Y) : (ofDeterministic ha hb).answers x y = PMF.pure (ha x, hb y) := by
  ext ⟨a, b⟩
  rw [answers_apply, PMF.pure_apply]
  simp only [ofDeterministic, POVM.const, Prod.mk.injEq]
  by_cases h1 : a = ha x <;> by_cases h2 : b = hb y <;> simp [h1, h2]

variable [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']

/-- Relabel the bases of the two systems along `e : ι ≃ ι'` and `f : κ ≃ κ'`. -/
noncomputable def reindex (S : QuantumStrategy X Y A B ι κ) (e : ι ≃ ι') (f : κ ≃ κ') :
    QuantumStrategy X Y A B ι' κ' where
  state := WithLp.toLp 2 (S.state.ofLp ∘ (e.prodCongr f).symm)
  norm_state := by
    rw [EuclideanSpace.norm_eq, ← S.norm_state, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp (e.prodCongr f).symm fun p => ‖S.state p‖ ^ 2
  alice x := (S.alice x).reindex e
  bob y := (S.bob y).reindex f

/-- Relabelling the bases does not change the distribution of the answers. -/
theorem answers_reindex (S : QuantumStrategy X Y A B ι κ) (e : ι ≃ ι') (f : κ ≃ κ') (x : X)
    (y : Y) : (S.reindex e f).answers x y = S.answers x y := by
  ext ⟨a, b⟩
  rw [answers_apply, answers_apply]
  congr 2
  rw [← star_dotProduct_submatrix_mulVec (e.prodCongr f)
    ((S.alice x).effect a ⊗ₖ (S.bob y).effect b) S.state.ofLp]
  rfl

end QuantumStrategy

namespace TwoProverGame

variable {X Y A B : Type*} (G : TwoProverGame X Y A B) [Fintype A] [Fintype B]

/-- The probability that the quantum strategy `S` wins `G`. -/
noncomputable def quantumWinProb {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (S : QuantumStrategy X Y A B ι κ) : ℝ :=
  ((G.questions.bind fun q => (S.answers q.1 q.2).map fun ab => (q, ab)).toOuterMeasure
    {z | G.accepts z.1.1 z.1.2 z.2.1 z.2.2}).toReal

section WinProb

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem quantumWinProb_nonneg (S : QuantumStrategy X Y A B ι κ) : 0 ≤ G.quantumWinProb S :=
  ENNReal.toReal_nonneg

theorem quantumWinProb_le_one (S : QuantumStrategy X Y A B ι κ) : G.quantumWinProb S ≤ 1 :=
  (ENNReal.toReal_mono ENNReal.one_ne_top
    (Cslib.Probability.PMF.toOuterMeasure_le_one _ _)).trans_eq ENNReal.toReal_one

/-- The winning probability of a quantum strategy
[Cleve, Høyer, Toner, Watrous, §2][CleveHoyerTonerWatrous2004]:
`∑_{x,y} π(x,y) ∑_{a,b} V(a,b|x,y) ⟨ψ|X_x^a ⊗ Y_y^b|ψ⟩`. -/
theorem quantumWinProb_eq_sum [Fintype X] [Fintype Y] [∀ x y a b, Decidable (G.accepts x y a b)]
    (S : QuantumStrategy X Y A B ι κ) :
    G.quantumWinProb S = ∑ x, ∑ y, (G.questions (x, y)).toReal * ∑ a, ∑ b,
      if G.accepts x y a b then
        (star S.state.ofLp ⬝ᵥ (((S.alice x).effect a ⊗ₖ (S.bob y).effect b) *ᵥ S.state.ofLp)).re
      else 0 := by
  rw [quantumWinProb, PMF.toOuterMeasure_bind_apply, tsum_fintype, ENNReal.toReal_sum
    fun q _ => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _), ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply,
    Cslib.Probability.PMF.toOuterMeasure_apply_toReal, ← Finset.univ_product_univ,
    Finset.sum_product]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  split_ifs
  · rw [QuantumStrategy.answers_apply, ENNReal.toReal_ofReal]
    exact ((S.alice x).kronecker (S.bob y)).prob_nonneg S.state (a, b)
  · rfl

/-- Relabelling the bases does not change the winning probability. -/
theorem quantumWinProb_reindex {ι' κ' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ']
    [DecidableEq κ'] (S : QuantumStrategy X Y A B ι κ) (e : ι ≃ ι') (f : κ ≃ κ') :
    G.quantumWinProb (S.reindex e f) = G.quantumWinProb S := by
  simp only [quantumWinProb, QuantumStrategy.answers_reindex]

end WinProb

/-- The quantum embedding of a deterministic strategy wins with its classical probability. -/
theorem quantumWinProb_ofDeterministic [DecidableEq A] [DecidableEq B] (ha : X → A)
    (hb : Y → B) : G.quantumWinProb (QuantumStrategy.ofDeterministic ha hb) = G.winProb ha hb := by
  rw [quantumWinProb, winProb]
  simp_rw [QuantumStrategy.answers_ofDeterministic, PMF.pure_map]
  rw [show (fun q => PMF.pure (q, ha q.1, hb q.2)) =
      PMF.pure ∘ fun q : X × Y => (q, ha q.1, hb q.2) from rfl, PMF.bind_pure_comp,
    PMF.toOuterMeasure_map_apply]
  rfl

/-- The **entangled value** `ω*(G)` of a game: the supremum of the winning probability of quantum
strategies over all finite dimensions
[Cleve, Høyer, Toner, Watrous, §2][CleveHoyerTonerWatrous2004]. -/
noncomputable def quantumValue : ℝ :=
  ⨆ (n : ℕ) (m : ℕ) (S : QuantumStrategy X Y A B (Fin n) (Fin m)), G.quantumWinProb S

private theorem quantumWinProb_le_quantumValue_fin {n m : ℕ}
    (S : QuantumStrategy X Y A B (Fin n) (Fin m)) : G.quantumWinProb S ≤ G.quantumValue := by
  have hb : ∀ n m (S : QuantumStrategy X Y A B (Fin n) (Fin m)), G.quantumWinProb S ≤ 1 :=
    fun _ _ S => G.quantumWinProb_le_one S
  refine le_trans ?_ (le_ciSup (f := fun n => ⨆ (m : ℕ)
    (S : QuantumStrategy X Y A B (Fin n) (Fin m)), G.quantumWinProb S) ⟨1, ?_⟩ n)
  · refine le_trans ?_ (le_ciSup (f := fun m => ⨆ S : QuantumStrategy X Y A B (Fin n) (Fin m),
      G.quantumWinProb S) ⟨1, ?_⟩ m)
    · exact le_ciSup (f := G.quantumWinProb) ⟨1, by rintro _ ⟨S, rfl⟩; exact hb n m S⟩ S
    · rintro _ ⟨m, rfl⟩
      exact Real.iSup_le (hb n m) zero_le_one
  · rintro _ ⟨n, rfl⟩
    exact Real.iSup_le (fun m => Real.iSup_le (hb n m) zero_le_one) zero_le_one

/-- Every quantum strategy, on any finite-dimensional systems, wins with probability at most the
entangled value. -/
theorem quantumWinProb_le_quantumValue {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (S : QuantumStrategy X Y A B ι κ) : G.quantumWinProb S ≤ G.quantumValue := by
  rw [← G.quantumWinProb_reindex S (Fintype.equivFin ι) (Fintype.equivFin κ)]
  exact G.quantumWinProb_le_quantumValue_fin _

/-- A bound on the winning probability of every quantum strategy bounds the entangled value. -/
theorem quantumValue_le {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      (S : QuantumStrategy X Y A B ι κ), G.quantumWinProb S ≤ c) :
    G.quantumValue ≤ c :=
  Real.iSup_le (fun _ => Real.iSup_le (fun _ => Real.iSup_le (fun S => h S) hc) hc) hc

theorem quantumValue_le_one : G.quantumValue ≤ 1 :=
  G.quantumValue_le zero_le_one fun S => G.quantumWinProb_le_one S

theorem quantumValue_nonneg : 0 ≤ G.quantumValue :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun S =>
    G.quantumWinProb_nonneg S

/-- **Entanglement does not hurt**: the classical value is at most the entangled value. -/
theorem value_le_quantumValue [Finite X] [Finite Y] [Nonempty A] [Nonempty B] :
    G.value ≤ G.quantumValue := by
  classical
  obtain ⟨ha, hb, h⟩ := G.exists_winProb_eq_value
  rw [← h, ← G.quantumWinProb_ofDeterministic]
  exact G.quantumWinProb_le_quantumValue _

end TwoProverGame

end Cslib.PCP
