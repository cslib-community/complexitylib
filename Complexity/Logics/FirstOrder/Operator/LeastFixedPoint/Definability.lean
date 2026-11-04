/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.LeastFixedPoint
public import Complexity.Logics.FirstOrder.Operator.Definability.Polarity
public import Complexity.Tactic.FOOperator.Init

/-!
# Certified synthesis of least-fixed-point formulas

A positive defining formula for a relation transformer gives a defining formula for its least
fixed point. The body certificate is uniform over both structures and candidate relations. The
polarity certificate is syntactic, so synthesis cannot hide negative recursion behind a semantic
monotonicity hypothesis. `fo_definable` composes the registered body rules and this LFP rule.

## Main results

* `definable_lfp`: synthesize a fixed-point application to arbitrary first-order terms.
* `definable_lfp_vars`, `definable_lfp_unary`: forms suited to predicates on free variables.
-/

public section

universe u v w z t

open FirstOrder Language

namespace Cslib.Logic.FO.LFP

variable {L : Language.{u, v}} {ι : Type t} {M : ι → Type z} [∀ i, L.Structure (M i)]
  {Γ : List ℕ} {ρ : ∀ i, Operator.RelEnv Γ (M i)} {α : Type w} {k : ℕ}

/-- A positive body certificate synthesizes an LFP formula defining a given family of monotone
operators. The single body witness works for every structure and every candidate relation. -/
@[aesop safe apply (rule_sets := [FODefinable])]
theorem definable_lfp (F : ∀ i, (α → M i) → Set (Fin k → M i) →o Set (Fin k → M i))
    (args : Fin k → L.Term α)
    (hF : Operator.PolarityDefinable (L := L) policy headMark true
      (fun j : (i : ι) × Set (Fin k → M i) => M j.1)
      (fun _ => interpretation) (fun j => Operator.RelEnv.cons j.2 (ρ j.1))
      (fun j v => (v ∘ Sum.inr) ∈ F j.1 (v ∘ Sum.inl) j.2)) :
    Operator.Definable (L := L) policy M (fun _ => interpretation) ρ
      (fun i v => (fun j => (args j).realize v) ∈ (F i v).lfp) := by
  obtain ⟨body, hwf, hpos, hbody⟩ := hF
  refine ⟨lfp body args, (wellFormed_lfp _ _).2 ⟨hwf, hpos⟩, ?_⟩
  intro i v
  rw [realize_lfp body hpos args (ρ i) v]
  have hstep : stepHom body hpos (ρ i) v = F i v := by
    apply OrderHom.ext
    funext R
    ext xs
    exact hbody ⟨i, R⟩ (Sum.elim v xs)
  rw [hstep]

/-- Free-variable tuples provide a directly matching synthesis rule for LFP membership. -/
@[aesop safe apply (rule_sets := [FODefinable])]
theorem definable_lfp_vars
    (F : ∀ i, (α → M i) → Set (Fin k → M i) →o Set (Fin k → M i)) (args : Fin k → α)
    (hF : Operator.PolarityDefinable (L := L) policy headMark true
      (fun j : (i : ι) × Set (Fin k → M i) => M j.1)
      (fun _ => interpretation) (fun j => Operator.RelEnv.cons j.2 (ρ j.1))
      (fun j v => (v ∘ Sum.inr) ∈ F j.1 (v ∘ Sum.inl) j.2)) :
    Operator.Definable (L := L) policy M (fun _ => interpretation) ρ
      (fun i v => (v ∘ args) ∈ (F i v).lfp) :=
  definable_lfp F (fun j => .var (args j)) hF

/-- Unary fixed-point predicates written with vector notation are synthesized directly. -/
@[aesop safe apply (rule_sets := [FODefinable])]
theorem definable_lfp_unary
    (F : ∀ i, (α → M i) → Set (Fin 1 → M i) →o Set (Fin 1 → M i)) (a : α)
    (hF : Operator.PolarityDefinable (L := L) policy headMark true
      (fun j : (i : ι) × Set (Fin 1 → M i) => M j.1)
      (fun _ => interpretation) (fun j => Operator.RelEnv.cons j.2 (ρ j.1))
      (fun j v => (v ∘ Sum.inr) ∈ F j.1 (v ∘ Sum.inl) j.2)) :
    Operator.Definable (L := L) policy M (fun _ => interpretation) ρ
      (fun i v => ![v a] ∈ (F i v).lfp) := by
  apply (definable_lfp F ![.var a] hF).congr
  intro i v
  have htuple : (fun j => ((![.var a] : Fin 1 → L.Term α) j).realize v) = ![v a] := by
    funext j
    simp only [Matrix.cons_val_fin_one, Term.realize_var]
  rw [htuple]

end Cslib.Logic.FO.LFP
