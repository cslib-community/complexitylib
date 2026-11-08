/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Logics.Propositional.Defs
public import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
# Frege proofs

A *Frege system* [Cook and Reckhow][CookReckhow1979] is a line-based propositional proof system
given by finitely many sound axiom schemes and inference rules. This file fixes the Hilbert-style
system with the axiom schemes K, S and double-negation elimination for `→` and `⊥`, the usual
introduction and elimination schemes for `∧` and `∨`, and modus ponens as the only rule
(`Cslib.Logic.PL.Frege.IsAxiom`). A *proof* from hypotheses `Γ` is a list of formulas, each a
hypothesis, an axiom instance, or obtained by modus ponens from two earlier lines
(`Cslib.Logic.PL.Frege.IsProof`). As in `Complexity.Logics.Propositional.Resolution.Proof`, proofs
are listed from their last line to their first, and the size of a proof is its number of lines.

Formulas are cslib's propositions `Cslib.Logic.PL.Proposition` over the atoms `WithBot V`, with
the atom `⊥` read as falsity. cslib's propositions are a syntax for proof systems and carry no
Boolean semantics, so this file adds one (`Cslib.Logic.PL.Frege.Formula.eval`). No other formula
type of the library fits: the CNF and QBF types have no implication, and circuit formulas are
indexed by a fixed number of inputs.

The file proves soundness (`Cslib.Logic.PL.Frege.IsProof.eval`) and the tools used to build proofs
with explicit line counts:

* `Cslib.Logic.PL.Frege.IsProof.cut`: a proof from `Γ ++ Δ` replays on top of a proof from `Γ`
  among whose lines are the formulas of `Δ`, with at most as many new lines. This lets a later
  step reuse earlier lines, so that simulated proofs keep their line structure.
* `Cslib.Logic.PL.Frege.IsProof.deduction`: the **deduction theorem with linear overhead**. A proof
  from `Γ ++ Δ` becomes a proof from `Γ` containing `Δ ⇒ φ` (`Cslib.Logic.PL.Frege.Formula.imps`)
  for each of its lines `φ`, with at most `10 (|Δ| + 1)` lines per original line. Discharging the
  hypotheses of `Δ` one at a time would instead multiply the size by a constant per hypothesis.

## Main definitions

* `Cslib.Logic.PL.Frege.Formula`, `Cslib.Logic.PL.Frege.Formula.eval`.
* `Cslib.Logic.PL.Frege.IsAxiom`, `Cslib.Logic.PL.Frege.IsProof`: the Frege system.
* `Cslib.Logic.PL.Frege.Derives`: derivability in a bounded number of lines.

## Main results

* `Cslib.Logic.PL.Frege.IsProof.eval`: soundness.
* `Cslib.Logic.PL.Frege.IsProof.cut`, `Cslib.Logic.PL.Frege.IsProof.deduction`.

## References

* [S. A. Cook, R. A. Reckhow, *The relative efficiency of propositional proof
  systems*][CookReckhow1979]
-/

@[expose] public section

namespace Cslib.Logic.PL.Frege

variable {V : Type*}

/-- Formulas: cslib's propositions over the atoms `WithBot V`, where the atom `⊥` is falsity. -/
abbrev Formula (V : Type*) := Proposition (WithBot V)

namespace Formula

/-- Falsity. -/
abbrev bot : Formula V := Proposition.atom ⊥

/-- A variable. -/
abbrev var (v : V) : Formula V := Proposition.atom (v : WithBot V)

/-- Implication. -/
abbrev imp (φ ψ : Formula V) : Formula V := Proposition.imp φ ψ

/-- Negation `φ → ⊥`. -/
abbrev neg (φ : Formula V) : Formula V := imp φ bot

/-- Boolean value of a formula under an assignment; the atom `⊥` is false. -/
def eval (σ : V → Bool) : Formula V → Bool
  | .atom a => a.recBotCoe false σ
  | .and φ ψ => eval σ φ && eval σ ψ
  | .or φ ψ => eval σ φ || eval σ ψ
  | .imp φ ψ => !eval σ φ || eval σ ψ

@[simp] theorem eval_bot (σ : V → Bool) : eval σ bot = false := rfl
@[simp] theorem eval_var (σ : V → Bool) (v : V) : eval σ (var v) = σ v := rfl
@[simp] theorem eval_imp (σ : V → Bool) (φ ψ : Formula V) :
    eval σ (imp φ ψ) = (!eval σ φ || eval σ ψ) := rfl
@[simp] theorem eval_and (σ : V → Bool) (φ ψ : Formula V) :
    eval σ (.and φ ψ) = (eval σ φ && eval σ ψ) := rfl
@[simp] theorem eval_or (σ : V → Bool) (φ ψ : Formula V) :
    eval σ (.or φ ψ) = (eval σ φ || eval σ ψ) := rfl

/-- `a₁ → (a₂ → ⋯ → (aₖ → φ))`. -/
def imps (Δ : List (Formula V)) (φ : Formula V) : Formula V := Δ.foldr imp φ

@[simp] theorem imps_nil (φ : Formula V) : imps [] φ = φ := rfl
@[simp] theorem imps_cons (a : Formula V) (Δ φ) : imps (a :: Δ) φ = imp a (imps Δ φ) := rfl

end Formula

open Formula

/-- The axiom schemes: K, S, double-negation elimination, and the schemes for `∧` and `∨`. -/
inductive IsAxiom : Formula V → Prop
  /-- `φ → (ψ → φ)`. -/
  | k (φ ψ : Formula V) : IsAxiom (imp φ (imp ψ φ))
  /-- `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))`. -/
  | s (φ ψ χ : Formula V) : IsAxiom (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  /-- `¬¬φ → φ`. -/
  | dne (φ : Formula V) : IsAxiom (imp (neg (neg φ)) φ)
  /-- `φ ∧ ψ → φ`. -/
  | andElimL (φ ψ : Formula V) : IsAxiom (imp (.and φ ψ) φ)
  /-- `φ ∧ ψ → ψ`. -/
  | andElimR (φ ψ : Formula V) : IsAxiom (imp (.and φ ψ) ψ)
  /-- `φ → (ψ → φ ∧ ψ)`. -/
  | andIntro (φ ψ : Formula V) : IsAxiom (imp φ (imp ψ (.and φ ψ)))
  /-- `φ → φ ∨ ψ`. -/
  | orIntroL (φ ψ : Formula V) : IsAxiom (imp φ (.or φ ψ))
  /-- `ψ → φ ∨ ψ`. -/
  | orIntroR (φ ψ : Formula V) : IsAxiom (imp ψ (.or φ ψ))
  /-- `(φ → χ) → ((ψ → χ) → (φ ∨ ψ → χ))`. -/
  | orElim (φ ψ χ : Formula V) : IsAxiom (imp (imp φ χ) (imp (imp ψ χ) (imp (.or φ ψ) χ)))

/-- Frege proofs from hypotheses `Γ`, listed from the last line to the first. -/
inductive IsProof (Γ : List (Formula V)) : List (Formula V) → Prop
  /-- The empty proof. -/
  | nil : IsProof Γ []
  /-- A hypothesis is a new line. -/
  | hyp {L : List (Formula V)} {φ : Formula V} : IsProof Γ L → φ ∈ Γ → IsProof Γ (φ :: L)
  /-- An axiom instance is a new line. -/
  | ax {L : List (Formula V)} {φ : Formula V} : IsProof Γ L → IsAxiom φ → IsProof Γ (φ :: L)
  /-- Modus ponens from two earlier lines `φ` and `φ → ψ`. -/
  | mp {L : List (Formula V)} {φ ψ : Formula V} : IsProof Γ L → φ ∈ L → imp φ ψ ∈ L →
      IsProof Γ (ψ :: L)

/-- Every axiom instance is true under every assignment. -/
theorem IsAxiom.eval {φ : Formula V} (h : IsAxiom φ) (σ : V → Bool) : φ.eval σ = true := by
  cases h <;> simp only [eval_imp, eval_and, eval_or, eval_bot] <;>
    grind

/-- **Soundness**: under an assignment satisfying every hypothesis, every line is true. -/
theorem IsProof.eval {Γ L : List (Formula V)} (h : IsProof Γ L) {σ : V → Bool}
    (hσ : ∀ γ ∈ Γ, γ.eval σ = true) : ∀ φ ∈ L, φ.eval σ = true := by
  induction h with
  | nil => simp
  | hyp _ hφ ih => exact List.forall_mem_cons.2 ⟨hσ _ hφ, ih⟩
  | ax _ hφ ih => exact List.forall_mem_cons.2 ⟨hφ.eval σ, ih⟩
  | mp _ h₁ h₂ ih =>
    refine List.forall_mem_cons.2 ⟨?_, ih⟩
    have e₁ := ih _ h₁
    have e₂ := ih _ h₂
    simp only [eval_imp, e₁, Bool.not_true, Bool.false_or] at e₂
    exact e₂

/-- `L'` extends the proof `L` by at most `n` lines. -/
def Grows (Γ L L' : List (Formula V)) (n : ℕ) : Prop :=
  ∃ M, L' = M ++ L ∧ IsProof Γ L' ∧ M.length ≤ n

/-- No new lines. -/
theorem Grows.refl {Γ L : List (Formula V)} (h : IsProof Γ L) : Grows Γ L L 0 :=
  ⟨[], rfl, h, le_rfl⟩

/-- Growth composes, adding the line counts. -/
theorem Grows.trans {Γ L L' L'' : List (Formula V)} {m n : ℕ} (h₁ : Grows Γ L L' m)
    (h₂ : Grows Γ L' L'' n) : Grows Γ L L'' (n + m) := by
  obtain ⟨M, rfl, -, hM⟩ := h₁
  obtain ⟨N, rfl, hp, hN⟩ := h₂
  exact ⟨N ++ M, by simp, hp, by simp; omega⟩

/-- The extended list is a proof. -/
theorem Grows.proof {Γ L L' : List (Formula V)} {n : ℕ} (h : Grows Γ L L' n) :
    IsProof Γ L' := by
  obtain ⟨_, _, hp, _⟩ := h
  exact hp

/-- Growth keeps the old lines. -/
theorem Grows.subset {Γ L L' : List (Formula V)} {n : ℕ} (h : Grows Γ L L' n) : L ⊆ L' := by
  obtain ⟨M, rfl, -, -⟩ := h
  exact List.subset_append_right _ _

/-- Growth by at most `m` lines is growth by at most `n ≥ m` lines. -/
theorem Grows.mono {Γ L L' : List (Formula V)} {m n : ℕ} (h : Grows Γ L L' m) (hmn : m ≤ n) :
    Grows Γ L L' n := by
  obtain ⟨M, rfl, hp, hM⟩ := h
  exact ⟨M, rfl, hp, hM.trans hmn⟩

/-- Adding an axiom instance. -/
theorem grows_ax {Γ L : List (Formula V)} (h : IsProof Γ L) {φ : Formula V} (hφ : IsAxiom φ) :
    Grows Γ L (φ :: L) 1 := ⟨[φ], rfl, h.ax hφ, le_rfl⟩

/-- Adding a hypothesis. -/
theorem grows_hyp {Γ L : List (Formula V)} (h : IsProof Γ L) {φ : Formula V} (hφ : φ ∈ Γ) :
    Grows Γ L (φ :: L) 1 := ⟨[φ], rfl, h.hyp hφ, le_rfl⟩

/-- Adding a modus ponens line. -/
theorem grows_mp {Γ L : List (Formula V)} (h : IsProof Γ L) {φ ψ : Formula V} (h₁ : φ ∈ L)
    (h₂ : imp φ ψ ∈ L) : Grows Γ L (ψ :: L) 1 := ⟨[ψ], rfl, h.mp h₁ h₂, le_rfl⟩

/-- **Cut**: a proof from `Γ ++ Δ` replays on top of a proof `L` from `Γ` containing every
formula of `Δ`, with at most as many new lines. -/
theorem IsProof.cut {Γ Δ M L : List (Formula V)} (hM : IsProof (Γ ++ Δ) M) (hL : IsProof Γ L)
    (hΔ : ∀ δ ∈ Δ, δ ∈ L) :
    ∃ M', IsProof Γ (M' ++ L) ∧ M'.length ≤ M.length ∧ ∀ φ ∈ M, φ ∈ M' ++ L := by
  induction hM with
  | nil => exact ⟨[], hL, le_rfl, by simp⟩
  | @hyp M φ _ hφ ih =>
    obtain ⟨M', hp, hlen, hmem⟩ := ih
    rcases List.mem_append.1 hφ with hφ | hφ
    · refine ⟨φ :: M', hp.hyp hφ, by simp; omega, ?_⟩
      intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hmem ψ hψ)
    · refine ⟨M', hp, by simp; omega, ?_⟩
      intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact List.mem_append_right _ (hΔ _ hφ)
      · exact hmem ψ hψ
  | @ax M φ _ hφ ih =>
    obtain ⟨M', hp, hlen, hmem⟩ := ih
    refine ⟨φ :: M', hp.ax hφ, by simp; omega, ?_⟩
    intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hmem ψ hψ)
  | @mp M φ ψ _ h₁ h₂ ih =>
    obtain ⟨M', hp, hlen, hmem⟩ := ih
    refine ⟨ψ :: M', hp.mp (hmem _ h₁) (hmem _ h₂), by simp; omega, ?_⟩
    intro χ hχ
    rcases List.mem_cons.1 hχ with rfl | hχ
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hmem χ hχ)

/-- Proofs are monotone in the hypotheses. -/
theorem IsProof.mono {Γ Γ' L : List (Formula V)} (h : IsProof Γ L) (hΓ : Γ ⊆ Γ') :
    IsProof Γ' L := by
  induction h with
  | nil => exact .nil
  | hyp _ hφ ih => exact ih.hyp (hΓ hφ)
  | ax _ hφ ih => exact ih.ax hφ
  | mp _ h₁ h₂ ih => exact ih.mp h₁ h₂

/-- `φ` is derivable from `Γ` in at most `n` lines. -/
def Derives (Γ : List (Formula V)) (n : ℕ) (φ : Formula V) : Prop :=
  ∃ L, IsProof Γ L ∧ L.length ≤ n ∧ φ ∈ L

/-- Two proofs from the same hypotheses can be stacked. -/
theorem IsProof.append {Γ L M : List (Formula V)} (hL : IsProof Γ L) (hM : IsProof Γ M) :
    IsProof Γ (M ++ L) := by
  induction hM with
  | nil => simpa using hL
  | hyp _ hφ ih => exact ih.hyp hφ
  | ax _ hφ ih => exact ih.ax hφ
  | mp _ h₁ h₂ ih => exact ih.mp (List.mem_append_left _ h₁) (List.mem_append_left _ h₂)

namespace Derives

variable {Γ : List (Formula V)}

/-- Derivability in `n` lines implies derivability in `m ≥ n` lines. -/
theorem mono_len {n m : ℕ} {φ : Formula V} (h : Derives Γ n φ) (hnm : n ≤ m) :
    Derives Γ m φ := by
  obtain ⟨L, hL, hlen, hφ⟩ := h
  exact ⟨L, hL, hlen.trans hnm, hφ⟩

/-- An axiom instance in one line. -/
theorem ax {φ : Formula V} (h : IsAxiom φ) : Derives Γ 1 φ :=
  ⟨[φ], IsProof.nil.ax h, le_rfl, List.mem_cons_self⟩

/-- A hypothesis in one line. -/
theorem hyp {φ : Formula V} (h : φ ∈ Γ) : Derives Γ 1 φ :=
  ⟨[φ], IsProof.nil.hyp h, le_rfl, List.mem_cons_self⟩

/-- Modus ponens, stacking the two derivations. -/
theorem mp {m n : ℕ} {φ ψ : Formula V} (h₁ : Derives Γ m (imp φ ψ)) (h₂ : Derives Γ n φ) :
    Derives Γ (m + n + 1) ψ := by
  obtain ⟨L₁, hL₁, hlen₁, hφψ⟩ := h₁
  obtain ⟨L₂, hL₂, hlen₂, hφ⟩ := h₂
  refine ⟨ψ :: (L₂ ++ L₁), (hL₁.append hL₂).mp (List.mem_append_left _ hφ)
    (List.mem_append_right _ hφψ), by simp; omega, List.mem_cons_self⟩

/-- `φ → φ` in five lines. -/
theorem id (φ : Formula V) : Derives Γ 5 (imp φ φ) :=
  (((ax (IsAxiom.s φ (imp φ φ) φ)).mp (ax (IsAxiom.k φ (imp φ φ)))).mp
    (ax (IsAxiom.k φ φ))).mono_len (by omega)

/-- Weakening under an antecedent `a`. -/
theorem lift {n : ℕ} {φ : Formula V} (a : Formula V) (h : Derives Γ n φ) :
    Derives Γ (n + 2) (imp a φ) :=
  ((ax (IsAxiom.k φ a)).mp h).mono_len (by omega)

/-- Hypothetical syllogism. -/
theorem trans {m n : ℕ} {P Q R : Formula V} (h₁ : Derives Γ m (imp P Q))
    (h₂ : Derives Γ n (imp Q R)) : Derives Γ (m + n + 5) (imp P R) :=
  (((ax (IsAxiom.s P Q R)).mp (h₂.lift P)).mp h₁).mono_len (by omega)

/-- `a → (b₁ → ⋯ → bₖ → a)`. -/
theorem imp_imps_self (a : Formula V) (Δ : List (Formula V)) :
    Derives Γ (5 + 6 * Δ.length) (imp a (imps Δ a)) := by
  induction Δ with
  | nil => exact id a
  | cons b Δ ih =>
    have h := ((ax (IsAxiom.s a (imps Δ a) (imp b (imps Δ a)))).mp
      ((ax (IsAxiom.k (imps Δ a) b)).lift a)).mp ih
    exact h.mono_len (by simp; omega)

/-- `b₁ → ⋯ → bₖ → a` for `a` among the `bᵢ`. -/
theorem imps_mem {a : Formula V} {Δ : List (Formula V)} (h : a ∈ Δ) :
    Derives Γ (5 + 8 * Δ.length) (imps Δ a) := by
  induction Δ with
  | nil => simp at h
  | cons b Δ ih =>
    by_cases hab : a = b
    · subst hab
      exact (imp_imps_self a Δ).mono_len (by simp; omega)
    · have h' : a ∈ Δ := (List.mem_cons.1 h).resolve_left hab
      exact ((ih h').lift b).mono_len (by simp; omega)

/-- Distribution of `b₁ → ⋯ → bₖ →` over implication. -/
theorem imps_dist (Δ : List (Formula V)) (φ ψ : Formula V) :
    Derives Γ (5 + 10 * Δ.length) (imp (imps Δ (imp φ ψ)) (imp (imps Δ φ) (imps Δ ψ))) := by
  induction Δ with
  | nil => exact id _
  | cons a Δ ih =>
    have h₁ := (ax (IsAxiom.s a (imps Δ (imp φ ψ)) (imp (imps Δ φ) (imps Δ ψ)))).mp (ih.lift a)
    have h := h₁.trans (ax (IsAxiom.s a (imps Δ φ) (imps Δ ψ)))
    exact h.mono_len (by simp; omega)

end Derives

/-- Appending a derivation from the same hypotheses. -/
theorem Grows.of_derives {Γ L : List (Formula V)} (hL : IsProof Γ L) {n : ℕ} {φ : Formula V}
    (h : Derives Γ n φ) : ∃ L', Grows Γ L L' n ∧ φ ∈ L' := by
  obtain ⟨M, hM, hlen, hφ⟩ := h
  exact ⟨M ++ L, ⟨M, rfl, hL.append hM, hlen⟩, List.mem_append_left _ hφ⟩

/-- Weakening an available line under the antecedents `Δ`, two lines per antecedent. -/
theorem Grows.imps_of_mem {Γ L : List (Formula V)} (hL : IsProof Γ L) {φ : Formula V}
    (hφ : φ ∈ L) (Δ : List (Formula V)) :
    ∃ L', Grows Γ L L' (2 * Δ.length) ∧ imps Δ φ ∈ L' := by
  induction Δ with
  | nil => exact ⟨L, Grows.refl hL, hφ⟩
  | cons a Δ ih =>
    obtain ⟨L₁, g₁, h₁⟩ := ih
    have g₂ := grows_ax g₁.proof (IsAxiom.k (imps Δ φ) a)
    have g₃ := grows_mp g₂.proof (List.mem_cons_of_mem _ h₁) List.mem_cons_self
    exact ⟨_, (g₁.trans g₂).trans g₃ |>.mono (by simp; omega), List.mem_cons_self⟩

/-- **Deduction theorem with linear overhead**: a proof from `Γ ++ Δ` becomes a proof from `Γ` of
`Δ ⇒ φ` for each of its lines `φ`, with at most `10 (|Δ| + 1)` lines per original line. -/
theorem IsProof.deduction {Γ Δ M : List (Formula V)} (hM : IsProof (Γ ++ Δ) M)
    {L : List (Formula V)} (hL : IsProof Γ L) :
    ∃ L', Grows Γ L L' (10 * (Δ.length + 1) * M.length) ∧ ∀ φ ∈ M, imps Δ φ ∈ L' := by
  induction hM with
  | nil => exact ⟨L, (Grows.refl hL).mono (Nat.zero_le _), by simp⟩
  | @hyp M φ _ hφ ih =>
    obtain ⟨L₁, g₁, h₁⟩ := ih
    rcases List.mem_append.1 hφ with hφ | hφ
    · have g₂ := grows_hyp g₁.proof hφ
      obtain ⟨L₃, g₃, h₃⟩ := Grows.imps_of_mem g₂.proof List.mem_cons_self Δ
      refine ⟨L₃, ((g₁.trans g₂).trans g₃).mono (by simp only [List.length_cons]; nlinarith), ?_⟩
      intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact h₃
      · exact g₃.subset (g₂.subset (h₁ ψ hψ))
    · obtain ⟨L₂, g₂, h₂⟩ := Grows.of_derives g₁.proof (Derives.imps_mem (Γ := Γ) hφ)
      refine ⟨L₂, (g₁.trans g₂).mono (by simp only [List.length_cons]; nlinarith), ?_⟩
      intro ψ hψ
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact h₂
      · exact g₂.subset (h₁ ψ hψ)
  | @ax M φ _ hφ ih =>
    obtain ⟨L₁, g₁, h₁⟩ := ih
    have g₂ := grows_ax g₁.proof hφ
    obtain ⟨L₃, g₃, h₃⟩ := Grows.imps_of_mem g₂.proof List.mem_cons_self Δ
    refine ⟨L₃, ((g₁.trans g₂).trans g₃).mono (by simp only [List.length_cons]; nlinarith), ?_⟩
    intro ψ hψ
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact h₃
    · exact g₃.subset (g₂.subset (h₁ ψ hψ))
  | @mp M φ ψ _ hφ hφψ ih =>
    obtain ⟨L₁, g₁, h₁⟩ := ih
    obtain ⟨L₂, g₂, h₂⟩ := Grows.of_derives g₁.proof (Derives.imps_dist (Γ := Γ) Δ φ ψ)
    have g₃ := grows_mp g₂.proof (g₂.subset (h₁ _ hφψ)) h₂
    have g₄ := grows_mp g₃.proof (List.mem_cons_of_mem _ (g₂.subset (h₁ _ hφ)))
      List.mem_cons_self
    refine ⟨_, (((g₁.trans g₂).trans g₃).trans g₄).mono
      (by simp only [List.length_cons]; nlinarith), ?_⟩
    intro χ hχ
    rcases List.mem_cons.1 hχ with rfl | hχ
    · exact List.mem_cons_self
    · exact g₄.subset (g₃.subset (g₂.subset (h₁ χ hχ)))

/-- Detaching the antecedents `Δ` of an available line `Δ ⇒ φ`, one line per antecedent, when
every antecedent is available. -/
theorem Grows.imps_elim {Γ L : List (Formula V)} (hL : IsProof Γ L) {Δ : List (Formula V)}
    {φ : Formula V} (h : imps Δ φ ∈ L) (hΔ : ∀ δ ∈ Δ, δ ∈ L) :
    ∃ L', Grows Γ L L' Δ.length ∧ φ ∈ L' := by
  induction Δ generalizing L with
  | nil => exact ⟨L, Grows.refl hL, h⟩
  | cons a Δ ih =>
    have g₁ := grows_mp hL (hΔ a List.mem_cons_self) h
    obtain ⟨L₂, g₂, h₂⟩ := ih g₁.proof List.mem_cons_self
      fun δ hδ => List.mem_cons_of_mem _ (hΔ δ (List.mem_cons_of_mem _ hδ))
    exact ⟨L₂, (g₁.trans g₂).mono (by simp), h₂⟩

/-- Adding hypotheses: every formula of `Δ` that is a hypothesis or already available becomes
available, one line per formula. -/
theorem Grows.collect {Γ L : List (Formula V)} (hL : IsProof Γ L) {Δ : List (Formula V)}
    (hΔ : ∀ δ ∈ Δ, δ ∈ Γ ∨ δ ∈ L) : ∃ L', Grows Γ L L' Δ.length ∧ ∀ δ ∈ Δ, δ ∈ L' := by
  induction Δ with
  | nil => exact ⟨L, Grows.refl hL, by simp⟩
  | cons a Δ ih =>
    obtain ⟨L₁, g₁, h₁⟩ := ih fun δ hδ => hΔ δ (List.mem_cons_of_mem _ hδ)
    rcases hΔ a List.mem_cons_self with ha | ha
    · have g₂ := grows_hyp g₁.proof ha
      refine ⟨_, (g₁.trans g₂).mono (by simp; omega), fun δ hδ => ?_⟩
      rcases List.mem_cons.1 hδ with rfl | hδ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h₁ δ hδ)
    · refine ⟨L₁, g₁.mono (by simp), fun δ hδ => ?_⟩
      rcases List.mem_cons.1 hδ with rfl | hδ
      · exact g₁.subset ha
      · exact h₁ δ hδ

/-- Growing the empty proof by `n` lines gives at most `n` lines. -/
theorem Grows.length_of_nil {Γ L : List (Formula V)} {n : ℕ} (h : Grows Γ [] L n) :
    L.length ≤ n := by
  obtain ⟨M, rfl, -, hM⟩ := h
  simpa using hM

end Cslib.Logic.PL.Frege
