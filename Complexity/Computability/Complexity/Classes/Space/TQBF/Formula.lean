/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.TQBF
public import Complexity.Algorithms.Reachability.Savitch
public import Complexity.Logics.Propositional.CNF

/-!
# Midpoint formulas

Reachability in `2 ^ i` steps is expressed by a quantified Boolean formula of size linear in `i`,
by the midpoint recursion of Savitch's theorem with a universal quantifier folding the two halves
into one copy of the formula of the level below [Sipser, Theorem 8.9][Sipser2013]
[Arora and Barak, Theorem 4.13][AroraBarak09]:
`Φ_{i+1}(a, b) = ∃ m, ∀ x y, ((x = a ∧ y = m) ∨ (x = m ∧ y = b)) → Φ_i(x, y)`.

The words are held by blocks of `w` variables (`Cslib.Complexity.TQBF.blockVars`): at level `i`
the source, the target and the midpoint blocks, numbered by even numbers
(`Cslib.Complexity.TQBF.blockVar`), so that the odd numbers are free for the formula of level `0`.
Given a formula of level `0` whose value is that of `Cslib.Reachability.reach e w 0` on the words
held by the source and target blocks of level `0`, the midpoint formula of level `i`
(`Cslib.Complexity.TQBF.midpoint`) has, under every assignment, the value of
`Cslib.Reachability.reach e w i` on the words held by the blocks of level `i`
(`Cslib.Complexity.TQBF.eval_midpoint`). Fixing the blocks of level `d` to two words of width `w`
gives a closed formula (`Cslib.Complexity.TQBF.savitchFormula`) whose value is
`Cslib.Reachability.reach e w d u v` (`Cslib.Complexity.TQBF.eval_savitchFormula`), as soon as the
free variables of the formula of level `0` lie in its two blocks
(`Cslib.Complexity.TQBF.closed_savitchFormula`).

The formulas use the derived connectives of `Cslib.Logic.PL.QBF`: blocks of quantifiers
(`Cslib.Logic.PL.QBF.exs`, `Cslib.Logic.PL.QBF.alls`), conjunctions of lists
(`Cslib.Logic.PL.QBF.conj`), implication, equivalence, literals, and formulas in conjunctive normal
form (`Cslib.Logic.PL.QBF.ofCNF`). Their tokens are given here explicitly
(`Cslib.Logic.PL.QBF.tokens_exs`, …), for the polynomial-time construction of the formulas.

## Main definitions

* `Cslib.Complexity.TQBF.blockVar`, `Cslib.Complexity.TQBF.blockVars`: the variables of the blocks.
* `Cslib.Complexity.TQBF.midpoint`, `Cslib.Complexity.TQBF.savitchFormula`: the midpoint formulas.

## Main results

* `Cslib.Logic.PL.QBF.tokens_exs`, `Cslib.Logic.PL.QBF.tokens_alls`,
  `Cslib.Logic.PL.QBF.tokens_ofCNF`, …: the tokens of the derived connectives.
* `Cslib.Complexity.TQBF.eval_midpoint`, `Cslib.Complexity.TQBF.eval_savitchFormula`: the midpoint
  formulas express reachability by midpoints.
* `Cslib.Complexity.TQBF.closed_savitchFormula`: they are closed.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.9][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.13][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL.QBF

/-! ### Tokens of the derived connectives -/

theorem tokens_exs (vs : List ℕ) (φ : QBF ℕ) :
    (exs vs φ).tokens = vs.map (fun v => (Kind.ex, v)) ++ φ.tokens := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [exs, tokens] using ih

theorem tokens_alls (vs : List ℕ) (φ : QBF ℕ) :
    (alls vs φ).tokens = vs.map (fun v => (Kind.all, v)) ++ φ.tokens := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [alls, tokens] using ih

theorem tokens_conj (l : List (QBF ℕ)) :
    (conj l).tokens = l.flatMap (fun φ => (Kind.and, 0) :: φ.tokens) ++ [(Kind.top, 0)] := by
  induction l with
  | nil => rfl
  | cons φ l ih => simpa [conj, tokens] using ih

private theorem tokens_imp (φ ψ : QBF ℕ) :
    (imp φ ψ).tokens = (Kind.or, 0) :: (Kind.not, 0) :: (φ.tokens ++ ψ.tokens) := rfl

theorem tokens_iff (φ ψ : QBF ℕ) : (iff φ ψ).tokens =
    (Kind.or, 0) :: (Kind.and, 0) :: (φ.tokens ++ ψ.tokens ++
      ((Kind.and, 0) :: (Kind.not, 0) :: (φ.tokens ++ (Kind.not, 0) :: ψ.tokens))) := by
  simp [iff, tokens]

theorem tokens_lit (v : ℕ) (b : Bool) :
    (lit v b).tokens = if b then [(Kind.var, v)] else [(Kind.not, 0), (Kind.var, v)] := by
  cases b <;> rfl

theorem tokens_ofCNF (φ : CNF ℕ) : (ofCNF φ).tokens = φ.flatMap (fun c => (Kind.and, 0) ::
    (c.flatMap (fun l => (Kind.or, 0) :: (lit l.1 l.2).tokens) ++ [(Kind.bot, 0)])) ++
      [(Kind.top, 0)] := by
  have hc (c : Clause ℕ) : (ofClause c).tokens =
      c.flatMap (fun l => (Kind.or, 0) :: (lit l.1 l.2).tokens) ++ [(Kind.bot, 0)] := by
    induction c with
    | nil => rfl
    | cons l c ih => simpa [ofClause, tokens] using ih
  induction φ with
  | nil => rfl
  | cons c φ ih => simpa [ofCNF, tokens, hc] using ih

end Cslib.Logic.PL.QBF

namespace Cslib.Complexity.TQBF

open Cslib.Logic.PL Cslib.Reachability

/-! ### Blocks of variables -/

/-- The `j`-th variable of the source (`kind = 0`), target (`kind = 1`) or midpoint (`kind = 2`)
block of level `i`. The variables of the blocks are even. -/
def blockVar (kind i j : ℕ) : ℕ := 2 * Nat.pair (3 * i + kind) j

/-- The variables of the block `kind` of level `i`, for words of width `w`. -/
def blockVars (w kind i : ℕ) : List ℕ := (List.range w).map (blockVar kind i)

/-- The word held by a block under an assignment. -/
def block (σ : ℕ → Bool) (w kind i : ℕ) : List Bool := (blockVars w kind i).map σ

theorem length_block (σ : ℕ → Bool) (w kind i : ℕ) : (block σ w kind i).length = w := by
  simp [block, blockVars]

/-- Block variables are even. -/
theorem blockVar_mod_two (kind i j : ℕ) : blockVar kind i j % 2 = 0 := by
  simp [blockVar]

theorem blockVar_inj {k k' i i' j j' : ℕ} (hk : k < 3) (hk' : k' < 3)
    (h : blockVar k i j = blockVar k' i' j') : k = k' ∧ i = i' ∧ j = j' := by
  simp only [blockVar, Nat.mul_left_cancel_iff two_pos, Nat.pair_eq_pair] at h
  omega

private theorem blockVar_mem_blockVars {w k k' i i' j : ℕ} (hk : k < 3) (hk' : k' < 3) :
    blockVar k i j ∈ blockVars w k' i' ↔ k = k' ∧ i = i' ∧ j < w := by
  simp only [blockVars, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j', hj', h⟩
    obtain ⟨rfl, rfl, rfl⟩ := blockVar_inj hk' hk h
    exact ⟨rfl, rfl, hj'⟩
  · rintro ⟨rfl, rfl, hj⟩
    exact ⟨j, hj, rfl⟩

private theorem nodup_blockVars (w kind i : ℕ) (hk : kind < 3) : (blockVars w kind i).Nodup :=
  List.nodup_range.map fun _ _ h => (blockVar_inj hk hk h).2.2

/-- The source and target blocks of a level are disjoint. -/
theorem nodup_blockVars_append (w i : ℕ) : (blockVars w 0 i ++ blockVars w 1 i).Nodup := by
  refine List.nodup_append.mpr ⟨nodup_blockVars w 0 i (by omega),
    nodup_blockVars w 1 i (by omega), fun a ha b hb hab => ?_⟩
  simp only [blockVars, List.mem_map] at ha hb
  obtain ⟨j, -, rfl⟩ := ha
  obtain ⟨j', -, rfl⟩ := hb
  exact absurd (blockVar_inj (by omega) (by omega) hab).1 (by omega)

/-- Assignments agreeing outside a list of variables that misses a block hold the same word in
it. -/
private theorem block_eq_of_agree {σ τ : ℕ → Bool} {vs : List ℕ} (h : ∀ x ∉ vs, τ x = σ x)
    {w k i : ℕ}
    (hvs : ∀ j < w, blockVar k i j ∉ vs) : block τ w k i = block σ w k i := by
  simp only [block, blockVars, List.map_map]
  exact List.map_inj_left.mpr fun j hj => h _ (hvs j (List.mem_range.mp hj))

/-- Any values can be given to a list of distinct variables, keeping the others. -/
private theorem exists_agree_map_eq (σ : ℕ → Bool) {vs : List ℕ} (hvs : vs.Nodup) {bs : List Bool}
    (hbs : bs.length = vs.length) : ∃ τ, (∀ x ∉ vs, τ x = σ x) ∧ vs.map τ = bs := by
  classical
  refine ⟨fun x => if x ∈ vs then bs.getD (vs.idxOf x) false else σ x, fun x hx => by simp [hx], ?_⟩
  refine List.ext_getElem (by simp [hbs]) fun j h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_mem, ite_true, hvs.idxOf_getElem,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂, Option.getD_some]

/-- Any two words of width `w` can be held by the source and target blocks of a level, keeping the
other variables. -/
private theorem exists_agree_block (σ : ℕ → Bool) {w : ℕ} (i : ℕ) {u v : List Bool}
    (hu : u.length = w)
    (hv : v.length = w) : ∃ τ, (∀ x ∉ blockVars w 0 i ++ blockVars w 1 i, τ x = σ x) ∧
      block τ w 0 i = u ∧ block τ w 1 i = v := by
  obtain ⟨τ, hτ, h⟩ := exists_agree_map_eq σ (nodup_blockVars_append w i) (bs := u ++ v)
    (by simp [blockVars, hu, hv])
  rw [List.map_append] at h
  obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [blockVars, hu])
  exact ⟨τ, hτ, h₁, h₂⟩

/-- Any word of width `w` can be held by a block, keeping the other variables. -/
private theorem exists_agree_block_one (σ : ℕ → Bool) {w k : ℕ} (hk : k < 3) (i : ℕ) {u : List Bool}
    (hu : u.length = w) : ∃ τ, (∀ x ∉ blockVars w k i, τ x = σ x) ∧ block τ w k i = u :=
  exists_agree_map_eq σ (nodup_blockVars w k i hk) (by simp [blockVars, hu])

/-! ### Formulas on blocks -/

/-- The block `k` of level `i` holds the same word as the block `k'` of level `i'`. -/
def eqBlock (w k i k' i' : ℕ) : QBF ℕ :=
  QBF.conj ((List.range w).map fun j => QBF.iff (.var (blockVar k i j)) (.var (blockVar k' i' j)))

/-- The block `k` of level `i` holds the word `u`. -/
def isBlock (w k i : ℕ) (u : List Bool) : QBF ℕ :=
  QBF.conj ((List.range w).map fun j => QBF.lit (blockVar k i j) (u.getD j false))

theorem eval_eqBlock (σ : ℕ → Bool) (w k i k' i' : ℕ) :
    (eqBlock w k i k' i').eval σ = decide (block σ w k i = block σ w k' i') := by
  simp only [eqBlock, QBF.eval_conj, List.all_map, block, blockVars, List.map_map]
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff, List.map_inj_left]
  simp

private theorem eval_isBlock (σ : ℕ → Bool) {w : ℕ} (k i : ℕ) {u : List Bool} (hu : u.length = w) :
    (isBlock w k i u).eval σ = decide (block σ w k i = u) := by
  have hu' : u = (List.range w).map fun j => u.getD j false :=
    List.ext_getElem (by simp [hu]) fun j h₁ h₂ => by simp [List.getD_eq_getElem?_getD, h₁]
  simp only [isBlock, QBF.eval_conj, List.all_map, block, blockVars, List.map_map]
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  conv_rhs => rw [hu', List.map_inj_left]
  simp

theorem mem_freeVars_eqBlock {w k i k' i' x : ℕ} (hx : x ∈ (eqBlock w k i k' i').freeVars) :
    x ∈ blockVars w k i ∨ x ∈ blockVars w k' i' := by
  simp only [eqBlock, QBF.mem_freeVars_conj, List.mem_map, List.mem_range] at hx
  obtain ⟨_, ⟨j, hj, rfl⟩, hx⟩ := hx
  simp only [QBF.freeVars_iff, QBF.freeVars_var, Finset.mem_union, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact .inl (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  · exact .inr (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

private theorem mem_freeVars_isBlock {w k i x : ℕ} {u : List Bool}
    (hx : x ∈ (isBlock w k i u).freeVars) :
    x ∈ blockVars w k i := by
  simp only [isBlock, QBF.mem_freeVars_conj, List.mem_map, List.mem_range] at hx
  obtain ⟨_, ⟨j, hj, rfl⟩, hx⟩ := hx
  rw [QBF.freeVars_lit, Finset.mem_singleton] at hx
  exact hx ▸ List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

/-! ### The midpoint formulas -/

/-- The hypothesis of level `i + 1`: the source and target blocks of level `i` hold the source
of level `i + 1` and the midpoint, or the midpoint and the target of level `i + 1`. -/
def halves (w i : ℕ) : QBF ℕ :=
  .or (.and (eqBlock w 0 i 0 (i + 1)) (eqBlock w 1 i 2 (i + 1)))
    (.and (eqBlock w 0 i 2 (i + 1)) (eqBlock w 1 i 1 (i + 1)))

/-- **The midpoint formula of level `i`**: the formula `base` at level `0`, and at level `i + 1`,
some midpoint such that, for all words held by the source and target blocks of level `i` that
form one of the two halves, the formula of level `i` holds. -/
def midpoint (w : ℕ) (base : QBF ℕ) : ℕ → QBF ℕ
  | 0 => base
  | i + 1 => QBF.exs (blockVars w 2 (i + 1))
      (QBF.alls (blockVars w 0 i ++ blockVars w 1 i) (QBF.imp (halves w i) (midpoint w base i)))

/-- **The midpoint formulas express reachability by midpoints.** If, under every assignment, the
formula of level `0` has the value of `reach e w 0` on the words held by the source and target
blocks of level `0`, then so does the formula of every level `i`, with `reach e w i`. -/
theorem eval_midpoint {e : List Bool → List Bool → Bool} {w : ℕ} {base : QBF ℕ}
    (hbase : ∀ σ, base.eval σ = reach e w 0 (block σ w 0 0) (block σ w 1 0)) (i : ℕ)
    (σ : ℕ → Bool) :
    (midpoint w base i).eval σ = reach e w i (block σ w 0 i) (block σ w 1 i) := by
  induction i generalizing σ with
  | zero => exact hbase σ
  | succ i ih =>
    -- blocks of level `i + 1` are untouched by the quantifiers of level `i`
    have hlow : ∀ k < 3, ∀ k' < 2, ∀ j < w, blockVar k (i + 1) j ∉
        blockVars w 0 i ++ blockVars w 1 i := by
      intro k hk k' _ j _ h
      rcases List.mem_append.mp h with h | h <;>
        · obtain ⟨-, h, -⟩ := (blockVar_mem_blockVars hk (by omega)).mp h
          omega
    have hmid : ∀ k < 2, ∀ j < w, blockVar k (i + 1) j ∉ blockVars w 2 (i + 1) := by
      intro k hk j _ h
      obtain ⟨h, -, -⟩ := (blockVar_mem_blockVars (by omega) (by omega)).mp h
      omega
    rw [Bool.eq_iff_iff, midpoint, QBF.eval_exs_eq_true_iff]
    simp only [reach, List.any_eq_true, Bool.and_eq_true, BitString.mem_enumList]
    constructor
    · rintro ⟨τ₁, hτ₁, h⟩
      rw [QBF.eval_alls_eq_true_iff] at h
      have hsrc := block_eq_of_agree hτ₁ (hmid 0 (by omega))
      have hdst := block_eq_of_agree hτ₁ (hmid 1 (by omega))
      -- the halves, for the words held by the source and target blocks of level `i`
      have hhalf : ∀ u v, u.length = w → v.length = w →
          ((u = block σ w 0 (i + 1) ∧ v = block τ₁ w 2 (i + 1)) ∨
            (u = block τ₁ w 2 (i + 1) ∧ v = block σ w 1 (i + 1))) → reach e w i u v = true := by
        intro u v hu hv huv
        obtain ⟨τ₂, hτ₂, h₁, h₂⟩ := exists_agree_block τ₁ i hu hv
        have := h τ₂ hτ₂
        rw [QBF.eval_imp, Bool.or_eq_true, Bool.not_eq_true', ih, h₁, h₂] at this
        refine this.resolve_left ?_
        simp only [halves, QBF.eval_or, QBF.eval_and, eval_eqBlock, h₁, h₂,
          block_eq_of_agree hτ₂ (hlow 0 (by omega) 0 (by omega)),
          block_eq_of_agree hτ₂ (hlow 1 (by omega) 0 (by omega)),
          block_eq_of_agree hτ₂ (hlow 2 (by omega) 0 (by omega)), hsrc, hdst]
        rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
      exact ⟨block τ₁ w 2 (i + 1), length_block .., hhalf _ _ (length_block ..)
        (length_block ..) (.inl ⟨rfl, rfl⟩), hhalf _ _ (length_block ..) (length_block ..)
        (.inr ⟨rfl, rfl⟩)⟩
    · rintro ⟨m, hm, h₁, h₂⟩
      obtain ⟨τ₁, hτ₁, hτm⟩ := exists_agree_block_one σ (k := 2) (by omega) (i + 1) hm
      have hsrc := block_eq_of_agree hτ₁ (hmid 0 (by omega))
      have hdst := block_eq_of_agree hτ₁ (hmid 1 (by omega))
      refine ⟨τ₁, hτ₁, (QBF.eval_alls_eq_true_iff ..).mpr fun τ₂ hτ₂ => ?_⟩
      rw [QBF.eval_imp, Bool.or_eq_true, Bool.not_eq_true', ih]
      by_cases hh : (halves w i).eval τ₂ = true
      · right
        simp only [halves, QBF.eval_or, QBF.eval_and, eval_eqBlock,
          block_eq_of_agree hτ₂ (hlow 0 (by omega) 0 (by omega)),
          block_eq_of_agree hτ₂ (hlow 1 (by omega) 0 (by omega)),
          block_eq_of_agree hτ₂ (hlow 2 (by omega) 0 (by omega)), hsrc, hdst, hτm,
          Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hh
        rcases hh with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [ha, hb]
          exact h₁
        · rw [ha, hb]
          exact h₂
      · left
        simpa using hh

/-- The free variables of the midpoint formula of level `i` lie in the source and target blocks
of level `i`, as soon as those of the formula of level `0` lie in the blocks of level `0`. -/
private theorem mem_freeVars_midpoint {w : ℕ} {base : QBF ℕ}
    (hbase : ∀ x ∈ base.freeVars, x ∈ blockVars w 0 0 ∨ x ∈ blockVars w 1 0) (i : ℕ) :
    ∀ x ∈ (midpoint w base i).freeVars, x ∈ blockVars w 0 i ∨ x ∈ blockVars w 1 i := by
  induction i with
  | zero => exact hbase
  | succ i ih =>
    intro x hx
    simp only [midpoint, QBF.freeVars_exs, QBF.freeVars_alls, QBF.freeVars_imp, Finset.mem_sdiff,
      Finset.mem_union, List.mem_toFinset, List.mem_append] at hx
    obtain ⟨⟨hx, hlow⟩, hmid⟩ := hx
    rcases hx with hx | hx
    · simp only [halves, QBF.freeVars_or, QBF.freeVars_and, Finset.mem_union] at hx
      rcases hx with (hx | hx) | (hx | hx) <;> rcases mem_freeVars_eqBlock hx with hx | hx <;>
        tauto
    · exact absurd (ih x hx) hlow

/-- **Savitch's formula**: the midpoint formula of level `d`, with its source and target blocks
fixed to the words `u` and `v`. -/
def savitchFormula (w d : ℕ) (base : QBF ℕ) (u v : List Bool) : QBF ℕ :=
  QBF.exs (blockVars w 0 d ++ blockVars w 1 d)
    (.and (isBlock w 0 d u) (.and (isBlock w 1 d v) (midpoint w base d)))

/-- **Savitch's formula expresses reachability by midpoints**, for words of width `w`. -/
theorem eval_savitchFormula {e : List Bool → List Bool → Bool} {w : ℕ} {base : QBF ℕ}
    (hbase : ∀ σ, base.eval σ = reach e w 0 (block σ w 0 0) (block σ w 1 0)) (d : ℕ)
    {u v : List Bool} (hu : u.length = w) (hv : v.length = w) (σ : ℕ → Bool) :
    (savitchFormula w d base u v).eval σ = reach e w d u v := by
  rw [Bool.eq_iff_iff, savitchFormula, QBF.eval_exs_eq_true_iff]
  simp only [QBF.eval_and, Bool.and_eq_true, eval_isBlock _ _ _ hu, eval_isBlock _ _ _ hv,
    decide_eq_true_eq, eval_midpoint hbase]
  constructor
  · rintro ⟨τ, -, rfl, rfl, h⟩
    exact h
  · intro h
    obtain ⟨τ, hτ, rfl, rfl⟩ := exists_agree_block σ d hu hv
    exact ⟨τ, hτ, rfl, rfl, h⟩

/-- **Savitch's formula is closed**, as soon as the free variables of the formula of level `0` lie
in the source and target blocks of level `0`. -/
theorem closed_savitchFormula {w : ℕ} {base : QBF ℕ}
    (hbase : ∀ x ∈ base.freeVars, x ∈ blockVars w 0 0 ∨ x ∈ blockVars w 1 0) (d : ℕ)
    (u v : List Bool) : (savitchFormula w d base u v).Closed := by
  refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
  simp only [savitchFormula, QBF.freeVars_exs, QBF.freeVars_and, Finset.mem_sdiff,
    Finset.mem_union, List.mem_toFinset, List.mem_append] at hx
  obtain ⟨hx, hblock⟩ := hx
  rcases hx with hx | hx | hx
  · exact hblock (.inl (mem_freeVars_isBlock hx))
  · exact hblock (.inr (mem_freeVars_isBlock hx))
  · exact hblock (mem_freeVars_midpoint hbase d x hx)

/-! ### Tokens of the midpoint formulas -/

/-- The tokens of an equivalence of two variables. -/
def iffTokens (x y : ℕ) : List (QBF.Kind × ℕ) :=
  [(.or, 0), (.and, 0), (.var, x), (.var, y), (.and, 0), (.not, 0), (.var, x), (.not, 0),
    (.var, y)]

theorem tokens_eqBlock (w k i k' i' : ℕ) : (eqBlock w k i k' i').tokens =
    (List.range w).flatMap (fun j => (.and, 0) :: iffTokens (blockVar k i j) (blockVar k' i' j)) ++
      [(.top, 0)] := by
  simp only [eqBlock, QBF.tokens_conj, List.flatMap_map, QBF.tokens_iff, QBF.tokens, iffTokens,
    List.cons_append, List.nil_append]

theorem tokens_isBlock (w k i : ℕ) (u : List Bool) : (isBlock w k i u).tokens =
    (List.range w).flatMap
      (fun j => (.and, 0) :: (QBF.lit (blockVar k i j) (u.getD j false)).tokens) ++
      [(.top, 0)] := by
  simp only [isBlock, QBF.tokens_conj, List.flatMap_map]

/-- The tokens the level `i + 1` adds in front of the midpoint formula of level `i`. -/
def levelTokens (w i : ℕ) : List (QBF.Kind × ℕ) :=
  (blockVars w 2 (i + 1)).map (fun v => (.ex, v)) ++
    (blockVars w 0 i ++ blockVars w 1 i).map (fun v => (.all, v)) ++
    (halves w i).not.tokens.cons (.or, 0)

private theorem tokens_midpoint_succ (w : ℕ) (base : QBF ℕ) (i : ℕ) :
    (midpoint w base (i + 1)).tokens = levelTokens w i ++ (midpoint w base i).tokens := by
  simp only [midpoint, QBF.tokens_exs, QBF.tokens_alls, QBF.tokens_imp, levelTokens,
    List.append_assoc, List.cons_append, QBF.tokens]

/-- The tokens of the midpoint formula of level `d`: the levels from `d` down to `1`, then the
formula of level `0`. -/
theorem tokens_midpoint (w : ℕ) (base : QBF ℕ) (d : ℕ) :
    (midpoint w base d).tokens = (List.range d).reverse.flatMap (levelTokens w) ++ base.tokens := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [tokens_midpoint_succ, ih, List.range_succ, List.reverse_append, List.flatMap_append]
    simp

end Cslib.Complexity.TQBF
