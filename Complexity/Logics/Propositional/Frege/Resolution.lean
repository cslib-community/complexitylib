/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Frege
public import Complexity.Logics.Propositional.Resolution.Proof
import Mathlib.Tactic.Linarith

/-!
# Frege simulates resolution

A clause `C` becomes the formula `¬ℓ₁ → ⋯ → ¬ℓₖ → ⊥` over the distinct literals `ℓᵢ` of `C`
(`Cslib.Logic.PL.Clause.toFormula`), where `¬v` is `v → ⊥` and the negation of `¬v` is `v`
itself. It holds exactly when the clause does (`Cslib.Logic.PL.Clause.eval_toFormula`). Every
resolution proof translates line by line into a Frege proof (`Cslib.Logic.PL.CNF.IsProof.frege`),
a standard fact in the framework of [Cook and Reckhow][CookReckhow1979]. One resolution step
(`Cslib.Logic.PL.Frege.derivableInSize_toFormula_resolvent`) goes as follows, for premises `C₁`
and `C₂`, the resolvent `R` on `v` and the negations `Δ` of the literals of `R`:

1. from `C₁`, `Δ` and `¬v`, detach the antecedents of the formula of `C₁` to derive `⊥`;
2. discharge `¬v` with the deduction theorem and apply double-negation elimination to get `v`;
3. from `C₂`, `Δ` and `v`, derive `⊥` in the same way;
4. discharge `Δ` with the deduction theorem with linear overhead
   (`Cslib.Logic.PL.Frege.IsProof.deduction`), which gives the formula of `R`.

On premises of width at most `w` this costs at most `stepBound w = 10 (2 w + 1) (42 w + 23)`
lines, quadratic in `w`. The step does not need the pivot to occur in the premises. The resolvent
reuses earlier lines through `Cslib.Logic.PL.Frege.IsProof.cut`, so a resolution proof of `s` lines
of width at most `w` becomes a Frege proof of at most `stepBound w * s` lines, and a resolution
refutation of `s` lines of a CNF on `N` variables a Frege proof of `⊥` of at most
`stepBound (2 N) * s` lines (`Cslib.Logic.PL.CNF.RefutableInSize.frege`). As in
`Complexity.Logics.Propositional.CuttingPlanes.Resolution`, sizes count lines; every line of the
translation has `O(w)` connectives, but formula sizes are not measured.

As a consequence, Frege refutes exactly the unsatisfiable CNFs
(`Cslib.Logic.PL.CNF.exists_frege_refutation_iff_not_satisfiable`).

## Main definitions

* `Cslib.Logic.PL.Clause.toFormula`: the formula of a clause.
* `Cslib.Logic.PL.Frege.stepBound`: the cost of one resolution step.

## Main results

* `Cslib.Logic.PL.Frege.derivableInSize_toFormula_resolvent`: one resolution step.
* `Cslib.Logic.PL.CNF.IsProof.frege`, `Cslib.Logic.PL.CNF.RefutableInSize.frege`: Frege
  simulates resolution.
* `Cslib.Logic.PL.CNF.exists_frege_refutation_iff_not_satisfiable`: Frege refutes exactly the
  unsatisfiable CNFs.

## References

* [S. A. Cook, R. A. Reckhow, *The relative efficiency of propositional proof
  systems*][CookReckhow1979]
-/

public section

namespace Cslib.Logic.PL

open Frege Frege.Formula

variable {V : Type*}

namespace Frege.Formula

/-- `Δ ⇒ ⊥` is true exactly when some formula of `Δ` is false. -/
theorem eval_imps_bot (σ : V → Bool) (Δ : List (Formula V)) :
    (imps Δ ⊥).eval σ = Δ.any fun δ => !δ.eval σ := by
  induction Δ with
  | nil => rfl
  | cons a Δ ih => simp [ih]

end Frege.Formula

/-- The negation of a literal, as a formula: `¬v` for `(v, true)` and `v` for `(v, false)`. -/
@[expose] def Literal.negFormula (l : Literal V) : Frege.Formula V :=
  if l.2 then Proposition.neg (var l.1) else var l.1

/-- The negation of a literal is true exactly when the literal is false. -/
theorem Literal.eval_negFormula (σ : V → Bool) (l : Literal V) :
    l.negFormula.eval σ = !l.eval σ := by
  obtain ⟨v, b⟩ := l
  cases b <;> cases h : σ v <;> simp [negFormula, Literal.eval, h]

variable [DecidableEq V]

/-- A clause as a formula: the negations of its distinct literals imply `⊥`. -/
@[expose] def Clause.toFormula (c : Clause V) : Frege.Formula V :=
  imps ((c.dedup).map Literal.negFormula) ⊥

/-- The formula of a clause is true exactly when the clause is. -/
theorem Clause.eval_toFormula (σ : V → Bool) (c : Clause V) : c.toFormula.eval σ = c.eval σ := by
  rw [toFormula, eval_imps_bot, Clause.eval]
  simp only [List.any_map, Function.comp_def, Literal.eval_negFormula, Bool.not_not]
  exact Bool.eq_iff_iff.2 (by simp [List.any_eq_true, List.mem_dedup])

/-- The formula of the empty clause is `⊥`. -/
theorem Clause.toFormula_nil : Clause.toFormula ([] : Clause V) = ⊥ := rfl

/-- A clause formula has at most as many antecedents as the clause has distinct literals. -/
private theorem length_dedup_map_le_width (c : Clause V) :
    ((c.dedup).map Literal.negFormula).length ≤ c.width := by
  rw [List.length_map, Clause.width, List.card_toFinset]

namespace Frege

/-- The bound on the Frege lines simulating one resolution step on clauses of width at most
`w`. -/
@[expose] def stepBound (w : ℕ) : ℕ := 10 * (2 * w + 1) * (42 * w + 23)

/-- `stepBound` is monotone. -/
theorem stepBound_mono {w w' : ℕ} (h : w ≤ w') : stepBound w ≤ stepBound w' := by
  unfold stepBound
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

/-- **One resolution step in Frege**: from the formulas of `c₁` and `c₂`, the formula of their
resolvent on `v` has a proof of at most `stepBound (max (width c₁) (width c₂))` lines. The pivot
need not occur in the premises. -/
theorem derivableInSize_toFormula_resolvent (c₁ c₂ : Clause V) (v : V) :
    DerivableInSize [c₁.toFormula, c₂.toFormula] (c₁.resolvent c₂ v).toFormula
      (stepBound (max c₁.width c₂.width)) := by
  set Γ₀ : List (Formula V) := [c₁.toFormula, c₂.toFormula]
  set Δ : List (Formula V) := ((c₁.resolvent c₂ v).dedup).map Literal.negFormula
  set nv : Formula V := Proposition.neg (var v)
  set a := c₁.width
  set b := c₂.width
  have hΔlen : Δ.length ≤ a + b := by
    refine (length_dedup_map_le_width _).trans ?_
    unfold Clause.width
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro l hl
    simp only [List.mem_toFinset, Clause.mem_resolvent] at hl
    simp only [Finset.mem_union, List.mem_toFinset]
    tauto
  -- negations of the literals of `c₁` other than `(v, true)` are in `Δ`
  have hΔ₁ : ∀ l ∈ c₁, l ≠ (v, true) → l.negFormula ∈ Δ := fun l hl hne =>
    List.mem_map.2 ⟨l, List.mem_dedup.2 (Clause.mem_resolvent.2 (Or.inl ⟨hl, hne⟩)), rfl⟩
  have hΔ₂ : ∀ l ∈ c₂, l ≠ (v, false) → l.negFormula ∈ Δ := fun l hl hne =>
    List.mem_map.2 ⟨l, List.mem_dedup.2 (Clause.mem_resolvent.2 (Or.inr ⟨hl, hne⟩)), rfl⟩
  -- from `c₁`, `Δ` and `¬v`, derive `⊥`
  have hp₀ : IsProof ((Γ₀ ++ Δ) ++ [nv]) [] := .nil
  obtain ⟨M₁a, g₁a, h₁a⟩ := Grows.collect hp₀
    (Δ := c₁.toFormula :: (c₁.dedup).map Literal.negFormula) (by
      intro δ hδ
      left
      rcases List.mem_cons.1 hδ with rfl | hδ
      · simp [Γ₀]
      · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hδ
        by_cases hlv : l = (v, true)
        · subst hlv
          simp [nv, Literal.negFormula]
        · exact List.mem_append_left _ (List.mem_append_right _
            (hΔ₁ l (List.mem_dedup.1 hl) hlv)))
  obtain ⟨M₁, g₁b, h₁b⟩ := Grows.imps_elim g₁a.proof (h₁a _ List.mem_cons_self)
    fun δ hδ => h₁a δ (List.mem_cons_of_mem _ hδ)
  have hM₁len : M₁.length ≤ 2 * a + 1 := by
    have := (g₁a.trans g₁b).length_of_nil
    have h1 := length_dedup_map_le_width c₁
    simp only [List.length_cons] at this
    omega
  -- discharge `¬v`
  obtain ⟨L₁, g₂, h₂⟩ := IsProof.deduction (Γ := Γ₀ ++ Δ) (Δ := [nv]) (g₁a.trans g₁b).proof
    (L := []) .nil
  have hnn : Proposition.neg nv ∈ L₁ := h₂ _ h₁b
  -- `v` by double negation elimination
  have g₃ := grows_ax g₂.proof (IsAxiom.dne (var v))
  have g₄ := grows_mp g₃.proof (List.mem_cons_of_mem _ hnn) List.mem_cons_self
  -- from `c₂`, derive `⊥`
  obtain ⟨L₅, g₅, h₅⟩ := Grows.collect g₄.proof
    (Δ := c₂.toFormula :: (c₂.dedup).map Literal.negFormula) (by
      intro δ hδ
      rcases List.mem_cons.1 hδ with rfl | hδ
      · left; simp [Γ₀]
      · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hδ
        by_cases hlv : l = (v, false)
        · subst hlv
          right
          simp [Literal.negFormula]
        · left
          exact List.mem_append_right _ (hΔ₂ l (List.mem_dedup.1 hl) hlv))
  obtain ⟨M₂, g₆, h₆⟩ := Grows.imps_elim g₅.proof (h₅ _ List.mem_cons_self)
    fun δ hδ => h₅ δ (List.mem_cons_of_mem _ hδ)
  have gM₂ := ((((g₂.trans g₃).trans g₄).trans g₅).trans g₆)
  have hM₂len : M₂.length ≤ 40 * a + 2 * b + 23 := by
    have := gM₂.length_of_nil
    have h1 := length_dedup_map_le_width c₂
    simp only [List.length_cons, List.length_nil] at this
    omega
  -- discharge `Δ`
  obtain ⟨L₃, g₇, h₇⟩ := IsProof.deduction (Γ := Γ₀) (Δ := Δ) gM₂.proof (L := []) .nil
  refine ⟨L₃, g₇.proof, h₇ _ h₆, ?_⟩
  have h3 := g₇.length_of_nil
  have hab : a + b ≤ 2 * max a b := by omega
  calc L₃.length ≤ 10 * (Δ.length + 1) * M₂.length := h3
    _ ≤ 10 * (a + b + 1) * (40 * a + 2 * b + 23) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hM₂len
    _ ≤ stepBound (max a b) := by
      unfold stepBound
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)

end Frege

open Frege

/-- **Frege simulates resolution**, line by line: a resolution proof from `φ` all of whose lines
have width at most `w` becomes a Frege proof from the formulas of the clauses of `φ`, containing
the formula of every line, with at most `stepBound w` Frege lines per resolution line. -/
theorem CNF.IsProof.frege {φ : CNF V} {ls : List (Clause V)} (h : φ.IsProof ls) {w : ℕ}
    (hw : ∀ c ∈ ls, c.width ≤ w) :
    ∃ L, Frege.IsProof (φ.map Clause.toFormula) L ∧ (∀ c ∈ ls, c.toFormula ∈ L) ∧
      L.length ≤ stepBound w * ls.length := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | @mem ls c _ hc ih =>
    obtain ⟨L, hL, hmem, hlen⟩ := ih fun d hd => hw d (List.mem_cons_of_mem _ hd)
    refine ⟨c.toFormula :: L, hL.hyp (List.mem_map_of_mem hc), fun d hd => ?_, ?_⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem d hd)
    · have h1 : 1 ≤ stepBound w := by unfold stepBound; nlinarith
      simp only [List.length_cons, Nat.mul_succ]
      omega
  | @resolvent ls c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨L, hL, hmem, hlen⟩ := ih fun d hd => hw d (List.mem_cons_of_mem _ hd)
    obtain ⟨M, hM, hR, hMlen⟩ := derivableInSize_toFormula_resolvent c₁ c₂ v
    have hM' : Frege.IsProof (φ.map Clause.toFormula ++ [c₁.toFormula, c₂.toFormula]) M :=
      hM.mono fun x hx => List.mem_append_right _ hx
    obtain ⟨M', hp, hlen', hmem'⟩ := hM'.cut hL (by simp [hmem _ h₁, hmem _ h₂])
    refine ⟨M' ++ L, hp, fun d hd => ?_, ?_⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact hmem' _ hR
      · exact List.mem_append_right _ (hmem d hd)
    · have hs : stepBound (max c₁.width c₂.width) ≤ stepBound w :=
        stepBound_mono (max_le (hw _ (List.mem_cons_of_mem _ h₁))
          (hw _ (List.mem_cons_of_mem _ h₂)))
      simp only [List.length_append, List.length_cons, Nat.mul_succ]
      omega

/-- A resolution refutation of `φ` with `s` lines becomes a Frege refutation of the formulas of the
clauses of `φ` (a Frege proof containing `⊥`) with at most `stepBound (2 N) * s` lines, where `N`
is the number of variables of `φ`. -/
theorem CNF.RefutableInSize.frege {φ : CNF V} {s : ℕ} (h : φ.RefutableInSize s) :
    ∃ L, Frege.IsProof (φ.map Clause.toFormula) L ∧ (⊥ : Frege.Formula V) ∈ L ∧
      L.length ≤ stepBound (2 * φ.vars.toFinset.card) * s := by
  obtain ⟨ls, hp, hnil, hlen⟩ := h
  obtain ⟨L, hL, hmem, hlen'⟩ := hp.frege fun c hc => hp.width_le hc
  exact ⟨L, hL, hmem _ hnil, hlen'.trans (Nat.mul_le_mul_left _ hlen)⟩

/-- **Frege refutes exactly the unsatisfiable CNFs**: the formulas of the clauses of `φ` have a
Frege proof of `⊥` exactly when `φ` is unsatisfiable. -/
theorem CNF.exists_frege_refutation_iff_not_satisfiable {φ : CNF V} :
    (∃ L, Frege.IsProof (φ.map Clause.toFormula) L ∧ (⊥ : Frege.Formula V) ∈ L) ↔
      ¬ φ.Satisfiable := by
  constructor
  · rintro ⟨L, hL, hbot⟩ ⟨σ, hσ⟩
    have hΓ : ∀ γ ∈ φ.map Clause.toFormula, γ.eval σ = true := by
      intro γ hγ
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hγ
      rw [Clause.eval_toFormula]
      exact List.all_eq_true.1 hσ c hc
    have := hL.eval hΓ _ hbot
    simp at this
  · intro h
    obtain ⟨s, hs⟩ := CNF.exists_refutableInSize_iff_not_satisfiable.2 h
    obtain ⟨L, hL, hbot, -⟩ := hs.frege
    exact ⟨L, hL, hbot⟩

end Cslib.Logic.PL
