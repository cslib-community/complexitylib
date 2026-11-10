/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure.Positive
public import CslibFrontier.Logics.FirstOrder.Operator.Tuple

/-!
# Pulling transitive-closure formulas back to tuples

An interpretation of target elements by full `d`-tuples lifts from ordinary first-order formulas
to FO(TC). A closure over pairs of `k`-tuples of targets becomes a closure over pairs of
`k * d`-tuples of source elements, and relation arities are multiplied by `d`. Term values are
named by existential coordinates, as in the least-fixed-point pullback, so the translation reuses
an ordinary first-order pullback, including its handling of target constants.

The semantic theorem uses a bijection between source tuples and target elements. It induces a
bijection between closure vertices, which carries one edge relation to the other and so preserves
reflexive reachability. The translation also preserves the closure polarity `TC.Positive`.

## Main definitions

* `Cslib.Logic.FO.TC.Tuple.onFormula`: extend a first-order tuple pullback to FO(TC).

## Main results

* `Cslib.Logic.FO.TC.Tuple.realize_onFormula`: the pullback preserves truth for all relation
  valuations that correspond blockwise.
* `Cslib.Logic.FO.TC.Tuple.positive_onFormula`: the pullback preserves closure polarity.
-/

public section

open FirstOrder Language

namespace Cslib.Logic.FO.TC.Tuple

open Operator Operator.Tuple

variable {L L' : Language} {d : ℕ}

/-- Concatenated coordinate blocks are carried to concatenated targets. -/
theorem blockEquiv_pair {M N : Type*} (e : (Fin d → M) ≃ N) {k : ℕ}
    (xs ys : Fin (k * d) → M) :
    blockEquiv e (2 * k) (fun i => pair xs ys (Fin.cast (Nat.mul_assoc 2 k d) i)) =
      pair (blockEquiv e k xs) (blockEquiv e k ys) := by
  rw [← pair_left_right (blockEquiv e (2 * k) _)]
  congr 1
  · funext i
    simp only [left, blockEquiv_apply]
    congr 1
    funext j
    have h : Fin.cast (Nat.mul_assoc 2 k d)
        (finProdFinEquiv (Fin.cast (Nat.two_mul k).symm (Fin.castAdd k i), j)) =
        Fin.cast (Nat.two_mul (k * d)).symm (Fin.castAdd (k * d) (finProdFinEquiv (i, j))) :=
      Fin.ext (by simp)
    rw [h, pair, Fin.cast_cast, Fin.cast_eq_self, Fin.append_left]
  · funext i
    simp only [right, blockEquiv_apply]
    congr 1
    funext j
    have h : Fin.cast (Nat.mul_assoc 2 k d)
        (finProdFinEquiv (Fin.cast (Nat.two_mul k).symm (Fin.natAdd k i), j)) =
        Fin.cast (Nat.two_mul (k * d)).symm (Fin.natAdd (k * d) (finProdFinEquiv (i, j))) :=
      Fin.ext (by
        simp only [Fin.val_cast, finProdFinEquiv_apply_val, Fin.val_natAdd]
        rw [Nat.mul_add, Nat.mul_comm d k]
        omega)
    rw [h, pair, Fin.cast_cast, Fin.cast_eq_self, Fin.append_right]

/-- Reachability is invariant under a bijection that carries one edge relation to the other. -/
private theorem reflTransGen_equiv {A B : Type*} (g : A ≃ B) (r : A → A → Prop)
    (p : B → B → Prop) (h : ∀ a b, r a b ↔ p (g a) (g b)) (a b : A) :
    Relation.ReflTransGen r a b ↔ Relation.ReflTransGen p (g a) (g b) := by
  refine ⟨fun hab => Relation.ReflTransGen.lift g (fun x y hxy => (h x y).mp hxy) a b hab,
    fun hab => ?_⟩
  have := Relation.ReflTransGen.lift g.symm (r := p) (p := r)
    (fun x y hxy => (h _ _).mpr (by simpa only [Equiv.apply_symm_apply] using hxy)) _ _ hab
  simpa only [Function.onFun, Equiv.symm_apply_apply] using this

/-- Lay out the flattened coordinates of two endpoint tuples as one closure tuple. -/
@[expose] def endpointMap {β : Type*} {k : ℕ} : β ⊕ Fin (2 * k * d) → β ⊕ Fin (2 * (k * d)) :=
  Sum.map id (Fin.cast (Nat.mul_assoc 2 k d))

/-- Extend an ordinary first-order tuple pullback to FO(TC) syntax. A closure of width `k`
becomes a closure of width `k * d`. -/
@[expose] noncomputable def onFormula (f : FOMap L L' d) :
    {Γ : List ℕ} → {α : Type} → Operator.Formula L' shape Γ α →
      Operator.Formula L shape (Γ.map (· * d)) (α × Fin d)
  | _, _, .ofFO φ => .ofFO (f φ)
  | _, _, .rel r args =>
    applyTerms f args (.rel (r.scale d) (fun i => .var (.inr i)))
  | _, _, .neg φ => .neg (onFormula f φ)
  | _, _, .conj φ ψ => .conj (onFormula f φ) (onFormula f ψ)
  | _, _, .ex φ => exBlock (onFormula f φ)
  | _, _, .op k body args =>
    applyTerms f args (tc (k := k * d)
      ((onFormula f (body ⟨0, Nat.one_pos⟩)).relabel (endpointMap ∘ Sum.map Sum.inl id ∘ scopeMap))
      (fun i => .var (.inr (Fin.cast (Nat.mul_assoc 2 k d).symm i))))

variable {Γ : List ℕ} {α : Type}

/-- Naming term values does not change the polarity of closures. -/
@[simp] theorem positive_applyTerms (f : FOMap L L' d) {k : ℕ} (args : Fin k → L'.Term α)
    (φ : Operator.Formula L shape Γ ((α × Fin d) ⊕ Fin (k * d))) (s : Bool) :
    Positive (applyTerms f args φ) s ↔ Positive φ s := by
  rw [applyTerms, positive_exs]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- Tuple pullback preserves the polarity of every closure. -/
@[simp] theorem positive_onFormula (f : FOMap L L' d) (φ : Operator.Formula L' shape Γ α)
    (s : Bool) : Positive (onFormula f φ) s ↔ Positive φ s := by
  induction φ generalizing s with
  | ofFO φ => exact Iff.rfl
  | rel r args => exact (positive_applyTerms f args _ s).trans Iff.rfl
  | neg φ ih => exact ih (!s)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ s) (ihψ s)
  | ex φ ih =>
    rw [onFormula, exBlock, positive_exs, positive_relabel]
    exact ih s
  | op k body args ih =>
    rw [onFormula, positive_applyTerms]
    exact and_congr Iff.rfl ((positive_relabel _ _ true).trans (ih ⟨0, Nat.one_pos⟩ true))

variable {M N : Type} [L.Structure M] [L'.Structure N]
  (f : FOMap L L' d) (e : (Fin d → M) ≃ N)
  (hf : ∀ {α : Type} (φ : L'.Formula α) (v : α × Fin d → M),
    (f φ).Realize v ↔ φ.Realize (fun a => e (fun i => v (a, i))))

/-- The endpoint layout and the scope map send the bound endpoint coordinates to the blocks of
the two closure endpoints. -/
private theorem endpoint_valuation {β : Type} (v : β × Fin d → M) {k : ℕ}
    (XS : Fin (2 * k * d) → M) (us ws : Fin (k * d) → M) :
    (fun a => e (fun i => (Sum.elim (Sum.elim v XS) (pair us ws) ∘
        (endpointMap ∘ Sum.map Sum.inl id ∘ scopeMap)) (a, i))) =
      Sum.elim (fun b => e (fun i => v (b, i))) (pair (blockEquiv e k us) (blockEquiv e k ws)) := by
  funext a
  cases a with
  | inl b => rfl
  | inr j => exact congrFun (blockEquiv_pair e us ws) j

include hf in
/-- A pulled-back closure whose body defines the transported edge relation is the transported
reachability relation. -/
private theorem realize_applyTerms_tc {k : ℕ} (args : Fin (2 * k) → L'.Term α)
    (φs : Operator.Formula L shape (Γ.map (· * d))
      (((α × Fin d) ⊕ Fin (2 * k * d)) ⊕ Fin (2 * (k * d))))
    (φt : Operator.Formula L' shape Γ (α ⊕ Fin (2 * k)))
    (ρs : RelEnv (Γ.map (· * d)) M) (ρt : RelEnv Γ N) (v : α × Fin d → M)
    (hφ : ∀ (XS : Fin (2 * k * d) → M) (us ws : Fin (k * d) → M),
      φs.Realize interpretation ρs (Sum.elim (Sum.elim v XS) (pair us ws)) ↔
        φt.Realize interpretation ρt (Sum.elim (fun a => e (fun i => v (a, i)))
          (pair (blockEquiv e k us) (blockEquiv e k ws)))) :
    (applyTerms f args (tc (k := k * d) φs
        (fun i => .var (.inr (Fin.cast (Nat.mul_assoc 2 k d).symm i))))).Realize
          interpretation ρs v ↔
      (tc φt args).Realize interpretation ρt (fun a => e (fun i => v (a, i))) := by
  rw [realize_applyTerms f e hf, realize_tc, realize_tc]
  set Y : Fin (2 * k) → N := fun i => (args i).realize (fun a => e (fun j => v (a, j)))
  set P := (blockEquiv e k).symm (left Y)
  set Q := (blockEquiv e k).symm (right Y)
  have hXS : (blockEquiv e (2 * k)).symm Y =
      fun i => pair P Q (Fin.cast (Nat.mul_assoc 2 k d) i) := by
    rw [Equiv.symm_apply_eq, blockEquiv_pair, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      pair_left_right]
  have key := reflTransGen_equiv (blockEquiv e k)
    (fun xs ys => φs.Realize interpretation ρs
      (Sum.elim (Sum.elim v (fun i => pair P Q (Fin.cast (Nat.mul_assoc 2 k d) i))) (pair xs ys)))
    (fun xs ys => φt.Realize interpretation ρt
      (Sum.elim (fun a => e (fun i => v (a, i))) (pair xs ys)))
    (hφ _) P Q
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at key
  rw [hXS]
  have hends : ∀ {R : (Fin (k * d) → M) → (Fin (k * d) → M) → Prop} {a b a' b'},
      a = a' → b = b' → (Relation.ReflTransGen R a b ↔ Relation.ReflTransGen R a' b') := by
    rintro R a b _ _ rfl rfl
    rfl
  refine (hends ?_ ?_).trans key
  · funext i
    exact congrFun (left_pair P Q) i
  · funext i
    exact congrFun (right_pair P Q) i

include hf in
/-- Full-tuple pullback preserves truth for arbitrary scoped relation valuations, including
nested closures. The relation valuations correspond blockwise through `blockEquiv`. -/
theorem realize_onFormula (φ : Operator.Formula L' shape Γ α) :
    ∀ (ρs : RelEnv (Γ.map (· * d)) M) (ρt : RelEnv Γ N),
      (∀ {k} (r : RelVar Γ k) xs, xs ∈ ρs (r.scale d) ↔ blockEquiv e k xs ∈ ρt r) →
      ∀ v : α × Fin d → M,
        (onFormula f φ).Realize interpretation ρs v ↔
          φ.Realize interpretation ρt (fun a => e (fun i => v (a, i))) := by
  induction φ with
  | ofFO φ =>
    intro ρs ρt hρ v
    exact hf φ v
  | rel r args =>
    intro ρs ρt hρ v
    exact realize_applyTerms_rel f e hf _ _ r args ρs ρt (hρ r) v
  | neg φ ih =>
    intro ρs ρt hρ v
    exact not_congr (ih ρs ρt hρ v)
  | conj φ ψ ihφ ihψ =>
    intro ρs ρt hρ v
    exact and_congr (ihφ ρs ρt hρ v) (ihψ ρs ρt hρ v)
  | ex φ ih =>
    intro ρs ρt hρ v
    exact realize_exBlock e _ _ ρs v _ (ih ρs ρt hρ)
  | op k body args ih =>
    intro ρs ρt hρ v
    exact realize_applyTerms_tc f e hf args
      ((onFormula f (body ⟨0, Nat.one_pos⟩)).relabel (endpointMap ∘ Sum.map Sum.inl id ∘ scopeMap))
      (body ⟨0, Nat.one_pos⟩) ρs ρt v
      (fun XS us ws => (Operator.Formula.realize_relabel _ _ _ _ _).trans
        ((ih ⟨0, Nat.one_pos⟩ ρs ρt hρ _).trans
          (iff_of_eq (congrArg _ (endpoint_valuation e v XS us ws)))))

end Cslib.Logic.FO.TC.Tuple
