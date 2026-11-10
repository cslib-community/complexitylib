/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.SizeWidth
public import CslibFrontier.Logics.Propositional.Tseitin

/-!
# Resolution lower bounds for Tseitin formulas

Tseitin formulas on graphs of good expansion are hard for resolution [Urquhart][Urquhart1987].
[Ben-Sasson and Wigderson][BenSassonWigderson2001] made this simple by going through width:
on a connected multigraph `G`, every resolution refutation of a Tseitin formula has a line of width
at least the expansion `e(G)` (`Cslib.Multigraph.minBalancedCut`), the least number of edges
between a set of between a third and two thirds of the vertices and its complement
(`Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_refutableInWidth`). With the size–width tradeoff
(`Cslib.Logic.PL.CNF.exp_le_of_refutableInSize`), a multigraph whose vertices
have at most `k ≤ e(G) - 2` edges other than self-loops, and with at most `N` edges, needs
refutations of at least `exp ((e(G) - k - 2)² / 8N)` lines
(`Cslib.Logic.PL.Tseitin.exp_le_of_refutableInSize`).

The width bound measures a clause `c` by the least number `μ(c)` of vertices whose constraints
imply it (`Cslib.Logic.PL.Tseitin.Implies`).

* A clause of the formula is implied by the constraint of a single vertex, so `μ ≤ 1` on it.
* The constraints implying the two premises of a resolution step together imply the resolvent, so
  `μ` is subadditive along resolution steps.
* The empty clause is implied by the constraints of all vertices only, since on a connected
  multigraph those of any other set are satisfiable
  (`Cslib.Logic.PL.Tseitin.exists_forall_mem_parityOn_incidence_eq`).

Hence the first line of a refutation with `μ > |V| / 3` has `μ ≤ 2 |V| / 3`. If the constraints of
`S` imply a clause `c` but those of `S` without any one vertex `v` do not, then `c` mentions every
edge `e` between `S` and its complement: an assignment satisfying the constraints of `S` without
`v`, and falsifying `c`, violates the constraint at `v`; flipping the value of `e` repairs it and
changes no other constraint of `S`, and if `c` did not mention `e` it would still falsify `c`
(`Cslib.Logic.PL.Tseitin.exists_mem_of_mem_edgeCut`). Taking `S` of size `μ(c)` for that line
gives the bound.

## Main definitions

* `Cslib.Logic.PL.Tseitin.Implies`: the constraints of a set of vertices imply a clause.

## Main results

* `Cslib.Logic.PL.Tseitin.exists_card_edgeCut_le_width`: every refutation of a Tseitin formula on
  a connected multigraph has a line at least as wide as the number of edges leaving some set of
  more than a third and at most two thirds of the vertices.
* `Cslib.Logic.PL.Tseitin.minBalancedCut_le_of_refutableInWidth`: **the width lower bound** of
  Ben-Sasson and Wigderson, `w ≥ e(G)`.
* `Cslib.Logic.PL.Tseitin.exp_le_of_refutableInSize`: **the size lower bound**,
  `s ≥ exp ((e(G) - k - 2)² / 8N)`.

## References

* [A. Urquhart, *Hard examples for resolution*][Urquhart1987]
* [E. Ben-Sasson, A. Wigderson, *Short proofs are narrow—resolution made
  simple*][BenSassonWigderson2001]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 18][Jukna2012]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Finset Function

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

namespace Tseitin

/-- The constraints of the vertices in `S` **imply** the clause `c`: every assignment whose parity
at each vertex of `S` is its charge satisfies `c`. -/
def Implies (ends : E → Sym2 V) (χ : V → Bool) (S : Finset V) (c : Clause E) : Prop :=
  ∀ σ : E → Bool, (∀ v ∈ S, parityOn (Multigraph.incidence ends v) σ = χ v) → c.eval σ = true

variable {ends : E → Sym2 V} {χ : V → Bool}

omit [Fintype V] [DecidableEq E] in
/-- More constraints imply more. -/
theorem Implies.mono {S T : Finset V} {c : Clause E} (h : Implies ends χ S c) (hST : S ⊆ T) :
    Implies ends χ T c :=
  fun σ hσ => h σ fun v hv => hσ v (hST hv)

/-- A clause of the Tseitin formula is implied by the constraint of a single vertex. -/
private theorem exists_implies_singleton_of_mem_tseitinFormula {c : Clause E}
    (hc : c ∈ CNF.tseitinFormula ends χ) : ∃ v, Implies ends χ {v} c := by
  obtain ⟨v, hv⟩ := CNF.mem_tseitinFormula.1 hc
  refine ⟨v, fun σ hσ => ?_⟩
  have h := (CNF.eval_parityOnEq_eq_true_iff _ _ σ).2 (hσ v (mem_singleton_self v))
  exact (CNF.eval_eq_true_iff σ _).1 h c hv

omit [Fintype V] in
/-- The constraints implying the premises of a resolution step together imply the resolvent. -/
theorem Implies.resolvent {S₁ S₂ : Finset V} {c₁ c₂ : Clause E} (h₁ : Implies ends χ S₁ c₁)
    (h₂ : Implies ends χ S₂ c₂) (x : E) : Implies ends χ (S₁ ∪ S₂) (c₁.resolvent c₂ x) :=
  fun σ hσ => Clause.eval_resolvent x (h₁ σ fun v hv => hσ v (mem_union_left _ hv))
    (h₂ σ fun v hv => hσ v (mem_union_right _ hv))

/-- A clause derivable from the Tseitin formula is implied by the constraints of all vertices. -/
private theorem implies_univ_of_derives {c : Clause E} (h : (CNF.tseitinFormula ends χ).Derives c) :
    Implies ends χ univ c := fun σ hσ =>
  h.eval_eq_true ((CNF.eval_tseitinFormula_eq_true_iff σ).2 fun v => hσ v (mem_univ v))

omit [DecidableEq E] in
/-- On a connected multigraph, only the constraints of all vertices imply the empty clause. -/
private theorem eq_univ_of_implies_nil (hG : (Multigraph.toSimpleGraph ends).Connected)
    {S : Finset V} (h : Implies ends χ S []) : S = univ := by
  by_contra hS
  obtain ⟨σ, hσ⟩ := exists_forall_mem_parityOn_incidence_eq hG χ hS
  exact Bool.false_ne_true (h σ hσ)

omit [DecidableEq E] in
/-- **Minimal sets of constraints imply clauses mentioning their edge cut**
[Ben-Sasson and Wigderson][BenSassonWigderson2001]. If the constraints of `S` imply `c`, but those
of `S` without any one of its vertices do not, then `c` mentions every edge between `S` and its
complement. -/
theorem exists_mem_of_mem_edgeCut {S : Finset V} {c : Clause E} (h : Implies ends χ S c)
    (hmin : ∀ v ∈ S, ¬ Implies ends χ (S.erase v) c) {e : E}
    (he : e ∈ Multigraph.edgeCut ends S) : ∃ b, (e, b) ∈ c := by
  classical
  obtain ⟨v, hv, w, hw, hvw⟩ := Multigraph.mem_edgeCut.1 he
  by_contra! hc
  -- an assignment satisfying the constraints of `S` without `v`, and falsifying `c`
  refine hmin v hv fun σ hσ => ?_
  by_contra hcσ
  have hσv : parityOn (Multigraph.incidence ends v) σ ≠ χ v := fun hv' =>
    hcσ <| h σ fun u hu => by
      by_cases huv : u = v
      · exact huv ▸ hv'
      · exact hσ u (mem_erase.2 ⟨huv, hu⟩)
  -- flipping `e` satisfies the constraints of `S` and still falsifies `c`
  obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ c).1 <| h (update σ e !σ e) fun u hu => by
    rw [parityOn_incidence_update_not]
    simp only [Multigraph.mem_incidence_of_ends_eq hvw]
    by_cases huv : u = v
    · subst huv
      have hne : u ≠ w := fun h => mem_compl.1 hw (h ▸ hu)
      cases hp : parityOn (Multigraph.incidence ends u) σ <;> cases hχ : χ u <;> simp_all
    · have huw : u ≠ w := fun h => mem_compl.1 hw (h ▸ hu)
      simp only [huv, huw, or_self, false_and, decide_false, Bool.false_xor]
      exact hσ u (mem_erase.2 ⟨huv, hu⟩)
  have hle : l.1 ≠ e := fun h' => hc l.2 (h' ▸ hl)
  rw [update_of_ne hle] at hσl
  exact hcσ ((Clause.eval_eq_true_iff σ c).2 ⟨l, hl, hσl⟩)

/-- If the constraints of `S` imply `c`, but those of `S` without any one of its vertices do not,
then `c` is at least as wide as the number of edges leaving `S`. -/
private theorem card_edgeCut_le_width {S : Finset V} {c : Clause E} (h : Implies ends χ S c)
    (hmin : ∀ v ∈ S, ¬ Implies ends χ (S.erase v) c) :
    #(Multigraph.edgeCut ends S) ≤ c.width := by
  choose! b hb using fun e (he : e ∈ Multigraph.edgeCut ends S) =>
    exists_mem_of_mem_edgeCut h hmin he
  exact card_le_card_of_injOn (fun e => (e, b e)) (fun e he => List.mem_toFinset.2 (hb e he))
    fun _ _ _ _ heq => congrArg Prod.fst heq

/-- The least number of vertices whose constraints imply `c` (`0` if there is none). -/
private noncomputable def μ (ends : E → Sym2 V) (χ : V → Bool) (c : Clause E) : ℕ :=
  sInf {k | ∃ S : Finset V, #S = k ∧ Implies ends χ S c}

omit [Fintype V] [DecidableEq E] in
private theorem μ_le {S : Finset V} {c : Clause E} (h : Implies ends χ S c) :
    μ ends χ c ≤ #S :=
  Nat.sInf_le ⟨S, rfl, h⟩

omit [DecidableEq E] in
private theorem exists_card_eq_μ {c : Clause E} (h : Implies ends χ univ c) :
    ∃ S : Finset V, #S = μ ends χ c ∧ Implies ends χ S c :=
  Nat.sInf_mem (s := {k | ∃ S : Finset V, #S = k ∧ Implies ends χ S c}) ⟨_, univ, rfl, h⟩

/-- Along a proof from the Tseitin formula, either `μ ≤ |V| / 3` on every line, or some line has
`|V| / 3 < μ ≤ 2 |V| / 3`: the first line with `μ > |V| / 3` is a resolvent of lines with
`μ ≤ |V| / 3`. -/
private theorem forall_or_exists_μ (hn : 2 ≤ Fintype.card V) {ls : List (Clause E)}
    (h : (CNF.tseitinFormula ends χ).IsProof ls) :
    (∀ c ∈ ls, 3 * μ ends χ c ≤ Fintype.card V) ∨
      ∃ c ∈ ls, Fintype.card V < 3 * μ ends χ c ∧ 3 * μ ends χ c ≤ 2 * Fintype.card V := by
  induction h with
  | nil => exact Or.inl (by simp)
  | @mem ls c _ hc ih =>
    rcases ih with ih | ⟨d, hd, hd'⟩
    · obtain ⟨v, hv⟩ := exists_implies_singleton_of_mem_tseitinFormula hc
      have h1 : μ ends χ c ≤ 1 := (μ_le hv).trans (card_singleton v).le
      by_cases h3 : 3 * μ ends χ c ≤ Fintype.card V
      · exact Or.inl fun d hd => (List.mem_cons.1 hd).elim (fun h => h ▸ h3) (ih d)
      · exact Or.inr ⟨c, List.mem_cons_self, by omega, by omega⟩
    · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, hd'⟩
  | @resolvent ls c₁ c₂ x hp h₁ h₂ _ _ ih =>
    rcases ih with ih | ⟨d, hd, hd'⟩
    · obtain ⟨S₁, hS₁, hi₁⟩ := exists_card_eq_μ (implies_univ_of_derives (hp.derives h₁))
      obtain ⟨S₂, hS₂, hi₂⟩ := exists_card_eq_μ (implies_univ_of_derives (hp.derives h₂))
      have hle : μ ends χ (c₁.resolvent c₂ x) ≤ μ ends χ c₁ + μ ends χ c₂ :=
        (μ_le (hi₁.resolvent hi₂ x)).trans ((card_union_le _ _).trans (by omega))
      have hc₁ := ih c₁ h₁
      have hc₂ := ih c₂ h₂
      by_cases h3 : 3 * μ ends χ (c₁.resolvent c₂ x) ≤ Fintype.card V
      · exact Or.inl fun d hd => (List.mem_cons.1 hd).elim (fun h => h ▸ h3) (ih d)
      · exact Or.inr ⟨_, List.mem_cons_self, by omega, by omega⟩
    · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, hd'⟩

/-- **Refutations of Tseitin formulas have wide lines**
[Ben-Sasson and Wigderson][BenSassonWigderson2001] [Jukna, Chapter 18][Jukna2012]. On a connected
multigraph with at least two vertices, every resolution refutation of a Tseitin formula has a line
at least as wide as the number of edges between some set `S` with `|V| / 3 < |S| ≤ 2 |V| / 3` and
its complement. -/
theorem exists_card_edgeCut_le_width [Nontrivial V]
    (hG : (Multigraph.toSimpleGraph ends).Connected) {ls : List (Clause E)}
    (h : (CNF.tseitinFormula ends χ).IsProof ls) (hnil : [] ∈ ls) :
    ∃ c ∈ ls, ∃ S : Finset V, Fintype.card V < 3 * #S ∧ 3 * #S ≤ 2 * Fintype.card V ∧
      #(Multigraph.edgeCut ends S) ≤ c.width := by
  have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card
  rcases forall_or_exists_μ hn h with hall | ⟨c, hc, h₁, h₂⟩
  · -- the empty clause needs the constraints of all vertices
    obtain ⟨S, hS, hi⟩ := exists_card_eq_μ (implies_univ_of_derives (h.derives hnil))
    have h' := hall [] hnil
    rw [← hS, eq_univ_of_implies_nil hG hi, card_univ] at h'
    omega
  · obtain ⟨S, hS, hi⟩ := exists_card_eq_μ (implies_univ_of_derives (h.derives hc))
    refine ⟨c, hc, S, hS ▸ h₁, hS ▸ h₂, card_edgeCut_le_width hi fun v hv hv' => ?_⟩
    have h' := μ_le hv'
    rw [card_erase_of_mem hv, hS] at h'
    omega

/-- **The width lower bound for Tseitin formulas**
[Ben-Sasson and Wigderson][BenSassonWigderson2001] [Jukna, Chapter 18][Jukna2012]: on a connected
multigraph, every resolution refutation of a Tseitin formula has width at least the expansion
`e(G)`. -/
theorem minBalancedCut_le_of_refutableInWidth (hG : (Multigraph.toSimpleGraph ends).Connected)
    {w : ℕ} (h : (CNF.tseitinFormula ends χ).RefutableInWidth w) :
    Multigraph.minBalancedCut ends ≤ w := by
  obtain ⟨ls, hp, hnil, hw⟩ := h
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [Multigraph.minBalancedCut_eq_zero_of_subsingleton]
    exact Nat.zero_le w
  · obtain ⟨c, hc, S, h₁, h₂, hS⟩ := exists_card_edgeCut_le_width hG hp hnil
    exact (Multigraph.minBalancedCut_le_card_edgeCut ends h₁.le h₂).trans (hS.trans (hw c hc))

/-- **The size lower bound for Tseitin formulas**
[Ben-Sasson and Wigderson, Corollary 3.6][BenSassonWigderson2001] [Jukna, Chapter 18][Jukna2012].
On a connected multigraph with at most `N` edges whose vertices have at most `k` edges other than
self-loops, if `k + 2 ≤ e(G)`, every resolution refutation of a Tseitin formula has at least
`exp ((e(G) - k - 2)² / 8N)` lines. -/
theorem exp_le_of_refutableInSize (hG : (Multigraph.toSimpleGraph ends).Connected) {k N s : ℕ}
    (hk : ∀ v, #(Multigraph.incidence ends v) ≤ k) (hN : Fintype.card E ≤ N)
    (hke : k + 2 ≤ Multigraph.minBalancedCut ends)
    (hs : (CNF.tseitinFormula ends χ).RefutableInSize s) :
    Real.exp (((Multigraph.minBalancedCut ends : ℝ) - k - 2) ^ 2 / (8 * N)) ≤ s :=
  CNF.exp_le_of_refutableInSize
    (fun c hc => (List.toFinset_card_le c).trans (CNF.length_le_of_mem_tseitinFormula hk hc))
    (CNF.card_toFinset_vars_tseitinFormula_le.trans hN)
    (fun _ => minBalancedCut_le_of_refutableInWidth hG) hke hs

end Tseitin

end Cslib.Logic.PL
