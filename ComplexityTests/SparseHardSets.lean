/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Sparse
import Complexity.Computability.Complexity.Classes.Sparse.BoundedTruthTable
import Complexity.Computability.Complexity.Classes.Sparse.Conjunctive
import Complexity.Computability.Complexity.Classes.Sparse.Fortune
import Complexity.Computability.Complexity.Classes.Sparse.Mahaney
import Complexity.Computability.Complexity.Classes.Sparse.OneQuery
import Complexity.Computability.Complexity.Classes.Sparse.Prune

/-!
# Sparse problems and the procedures of Fortune and Mahaney

Sparse and non-sparse problems; the pruning rules and the searches of the self-reduction tree on
concrete inputs, including a bound too small for Fortune's procedure to be correct; and the
procedures as exponential-time deciders for `SAT`, which satisfy the hypotheses of
`Cslib.Complexity.Fortune.accepts_iff`, `Cslib.Complexity.Mahaney.accepts_iff` and
`Cslib.Complexity.OneQuery.accepts_iff` with the identity reductions of `UNSAT` and `SAT` to the
encodings of their members, or the negated one-query reduction of `SAT` to `UNSAT`, and an
exponential bound. The left set of `SAT` on concrete formulas, `SEARCH-RIGHT` on concrete levels,
and the conjunctive procedure with queries that decide satisfiability, which satisfy the hypotheses
of `Cslib.Complexity.Conjunctive.accepts_iff` with the bound `0`. `SEARCH-RIGHT`, `SEARCH-LEFT`
and `PRUNE` on a concrete level with a two-depth Hausdorff decomposition, which satisfies the
hypotheses of `Cslib.Complexity.BTT.getElem_mem_prune`. The Hausdorff sets of the parity truth
table on concrete answers; conjunctive reductions of the Hausdorff sets of the identity one-query
reduction to tally problems; the bounded truth-table procedure on concrete formulas, including
queries that do not come from a reduction, which break it; and queries that decide satisfiability,
which satisfy the hypotheses of `Cslib.Complexity.BTT.accepts_iff`.

The main hypotheses of `Cslib.Complexity.Fortune.SAT_mem_P`, `Cslib.Complexity.Mahaney.SAT_mem_P`,
`Cslib.Complexity.OneQuery.SAT_mem_P`, `Cslib.Complexity.Conjunctive.SAT_mem_P` and
`Cslib.Complexity.BTT.SAT_mem_P`, a reduction of `SAT` or `UNSAT` to a sparse problem, cannot be
instantiated unless `P = NP`; the tests check the procedures and the other hypotheses instead.
-/

namespace ComplexityTests.SparseHardSets

open Cslib Cslib.Complexity Cslib.Complexity.Fortune Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Sparse problems -/

/-- Words of even length consisting only of `true`s. -/
private def evenOnes : Set (List Bool) := {w | Even w.length ∧ ∀ b ∈ w, b = true}

example : evenOnes ∈ SPARSE encBits ∧ (evenOnes : Language Bool) ∈ Circuits.Boolean.PPoly :=
  ⟨mem_SPARSE_of_unary fun _ hw => hw.2,
    Circuits.Boolean.PPoly.of_mem_SPARSE (mem_SPARSE_of_unary fun _ hw => hw.2)⟩

/-- A finite problem over an infinite type with any encoding, and its subsets. -/
example (enc : ℕ ↪ List Bool) : ({0, 5, 7} : Set ℕ) ∈ SPARSE enc ∧ ({5} : Set ℕ) ∈ SPARSE enc :=
  let h : ({0, 5, 7} : Set ℕ) ∈ SPARSE enc := (Set.toFinite _).mem_SPARSE
  ⟨h, mem_SPARSE_of_subset (by simp) h⟩

/-- All words are not sparse, so neither are all formulas through their encodings. -/
example : (Set.univ : Set (List Bool)) ∉ SPARSE encBits ∧
    (Set.univ : Set (List Bool)) ∉ SPARSE (Function.Embedding.refl _) := by
  refine ⟨univ_notMem_SPARSE, fun h => univ_notMem_SPARSE ?_⟩
  simpa using image_mem_SPARSE_encBits_iff.mpr h

/-! ### Pruning and search on concrete inputs -/

/-- The first entry with each label is kept, then at most `c + 1` of them. -/
example : prune (· % 3) 5 [1, 3, 4, 2, 1, 5] = [1, 3, 2] ∧
    prune (· % 3) 1 [1, 3, 4, 2, 1, 5] = [1, 3] ∧ prune id 0 [7, 7, 8] = [7] := by
  decide

example : expand 4 [[], [(1, false)]] =
    [[(4, true)], [(4, false)], [(1, false), (4, true)], [(1, false), (4, false)]] := by
  decide

/-- With the encodings of the formulas as labels, no two nodes share a label, so a bound larger
than the tree keeps every node and the procedure is a brute-force search. -/
example : accepts encCNF 8 [[(0, true), (1, false)], [(1, true)]] = true ∧
    accepts encCNF 8 [[(0, true)], [(0, false)]] = false ∧
    accepts encCNF 8 [[(0, true)], [(1, true)], [(0, false), (1, false)]] = false := by
  decide

/-- A bound too small breaks the procedure: with `c = 0` only the first child, which sets the
variable to `true`, survives the first level, so the satisfiable formula `¬x₀` is rejected. -/
example : search (fun a => encCNF (SAT.units a ++ [[(0, false)]])) 0 [[(0, false)]] =
      [[(0, true)]] ∧
    accepts encCNF 0 [[(0, false)]] = false ∧ [[(0, false)]] ∈ SAT :=
  ⟨by decide, by decide, ⟨fun _ => false, rfl⟩⟩

/-! ### Fortune's procedure with an exponential bound -/

/-- At most `(M + 1) 2 ^ M` words have length at most `M`. -/
private theorem card_le_of_length_le {M : ℕ} (s : Finset (List Bool))
    (hs : ∀ w ∈ s, w.length ≤ M) : s.card ≤ (M + 1) * 2 ^ M := by
  classical
  have hsub : s ⊆ (Finset.range (M + 1)).biUnion fun n =>
      (Finset.univ : Finset (Fin n → Bool)).image List.ofFn := by
    intro w hw
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨w.length, Nat.lt_succ_of_le (hs w hw), fun i => w[i], List.ofFn_getElem⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_card_nsmul _ _ (2 ^ M) fun n hn => ?_).trans (by simp)
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact Nat.pow_le_pow_right two_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

/-- The hypotheses of `accepts_iff` are satisfiable: the encoding reduces `UNSAT` to the encodings
of unsatisfiable formulas, and the number of words of bounded length bounds the census. So
Fortune's procedure with an exponential bound decides `SAT`. -/
example (φ : CNF ℕ) :
    let L := (encCNF φ).length
    let M := L + L * (8 * L + 11)
    accepts encCNF ((M + 1) * 2 ^ M) φ = true ↔ φ ∈ SAT := by
  intro L M
  refine accepts_iff (K := encCNF '' UNSAT) (M := M) (fun ψ => ?_) (fun a ha hlen => ?_)
    (fun s hs => card_le_of_length_le s fun w hw => (hs w hw).2)
  · rw [encCNF.injective.mem_set_image]
    rfl
  · have hunits := SAT.length_encCNF_units_le ha
    have hvars := SAT.length_vars_le φ
    dsimp only [M, L]
    rw [SAT.length_encCNF_append]
    nlinarith

/-! ### Mahaney's theorem -/

/-- A stage keeps the first node and the first node with each label `(a + b) % 3` after it, and
drops the first node when more than `t` others remain; pruning repeats it. -/
example : Mahaney.stage (fun a b : ℕ => (a + b) % 3) 1 [0, 1, 4, 2] = [1, 2] ∧
    Mahaney.stage (fun a b : ℕ => (a + b) % 3) 2 [0, 1, 4, 2] = [0, 1, 2] ∧
    Mahaney.prune (fun a b : ℕ => (a + b) % 3) 1 [0, 1, 4, 2] = [1, 2] ∧
    Mahaney.prune (fun a b : ℕ => (a + b) % 3) 0 [0, 1, 4, 2] = [2] := by
  decide

/-- The disjunction of the nodes fixing `x₀` to `true` and to `false` in `x₀ ∧ ¬x₀` is
unsatisfiable, while in `x₁` it is satisfiable. -/
example : Mahaney.disj [[(0, true)], [(0, false)]] [(0, true)] [(0, false)] ∉ SAT ∧
    Mahaney.disj [[(1, true)]] [(0, true)] [(0, false)] ∈ SAT := by
  rw [Mahaney.disj_mem_SAT_iff, Mahaney.disj_mem_SAT_iff]
  refine ⟨fun h => ?_, .inl ⟨fun _ => true, rfl⟩⟩
  rcases h with ⟨σ, hσ⟩ | ⟨σ, hσ⟩ <;> cases h0 : σ 0 <;> simp [SAT.units, CNF.eval, h0] at hσ

example : Mahaney.accepts encCNF 8 [[(0, true), (1, false)], [(1, true)]] = true ∧
    Mahaney.accepts encCNF 8 [[(0, true)], [(0, false)]] = false := by
  decide

/-- The hypotheses of `Mahaney.accepts_iff` are satisfiable: the encoding reduces `SAT` to the
encodings of satisfiable formulas, and the number of words of bounded length bounds the census. -/
example (φ : CNF ℕ) :
    let L := (encCNF φ).length
    let M := L * L * (16 * L + 21) + L
    Mahaney.accepts encCNF ((M + 1) * 2 ^ M) φ = true ↔ φ ∈ SAT := by
  intro L M
  refine Mahaney.accepts_iff (K := encCNF '' SAT) (M := M) (fun ψ => ?_)
    (fun a b ha hb hla hlb => ?_) (fun s hs => card_le_of_length_le s fun w hw => (hs w hw).2)
  · rw [encCNF.injective.mem_set_image]
  · have hvars := SAT.length_vars_le φ
    have hla' : a.length ≤ L := hla.trans hvars
    have hlb' : b.length ≤ L := hlb.trans hvars
    refine (Mahaney.length_encCNF_disj_le ha hb).trans ?_
    dsimp only [M]
    gcongr

/-! ### Sparse sets hard under one-query reductions -/

/-- A stage drops the first node when more than `t` of the other nodes with distinct labels have
the sign `true`, and otherwise keeps it with the first `2 t + 1` of them. -/
example : OneQuery.stage (fun _ b : ℕ => (b, decide (5 ≤ b))) 1 [0, 1, 2, 3, 4, 5, 6] =
      [1, 2, 3, 4, 5, 6] ∧
    OneQuery.stage (fun _ b : ℕ => (b, decide (5 ≤ b))) 2 [0, 1, 2, 3, 4, 5, 6] =
      [0, 1, 2, 3, 4, 5] ∧
    OneQuery.stage (fun _ b : ℕ => (b, false)) 1 [0, 1, 2, 3, 4, 5, 6] = [0, 1, 2, 3] := by
  decide

/-- Pruning repeats the stage: with the labels `((a + b) % 4, true)`, the first node is dropped
while more than one other label remains, and only duplicates are removed otherwise. -/
example : OneQuery.prune (fun a b : ℕ => ((a + b) % 4, true)) 1 [0, 1, 2, 3, 4, 5, 6] = [3, 4] ∧
    OneQuery.prune (fun _ b : ℕ => (b, false)) 1 [0, 1, 2, 3, 4, 5, 6] = [0, 1, 2, 3] := by
  decide

/-- The negated one-query reduction of `SAT` to `UNSAT` of Grochow's Question 3.2: query the
formula itself and negate the answer. -/
private def negQuery : CNF ℕ × List Bool → Bool := fun p => !p.2.headD false

private theorem mem_SAT_iff_negQuery (ψ : CNF ℕ) : ψ ∈ SAT ↔
    negQuery (ψ, truthTableAnswers ((fun p : CNF ℕ × ℕ => p.1) ⁻¹' UNSAT) (fun _ => 1) ψ) =
      true := by
  classical
  simp only [negQuery, truthTableAnswers, List.ofFn_succ, List.ofFn_zero, List.headD_cons,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Set.mem_preimage, UNSAT,
    Set.mem_ofPred_eq, not_not]
  rfl

/-- One-query reductions may negate the answer: `SAT` reduces to `UNSAT` with one query. -/
example : PolyTimeKTruthTableReducible 1 encCNF encCNF SAT UNSAT := by
  refine ⟨fun _ => 1, fun p => p.1, negQuery, by fun_prop, by fun_prop,
    by unfold negQuery; fun_prop, fun _ => le_rfl, mem_SAT_iff_negQuery⟩

/-- The signed label of a formula under the negated reduction is its marked encoding with the
sign `false`, and the labels decide satisfiability. -/
example (ψ : CNF ℕ) :
    OneQuery.signedKey encCNF (fun _ => 1) (fun p => p.1) negQuery ψ = (true :: encCNF ψ, false) ∧
      (ψ ∈ SAT ↔ (true :: encCNF ψ ∈ List.cons true '' (encCNF '' UNSAT) ↔ false = true)) := by
  have hkey : OneQuery.signedKey encCNF (fun _ => 1) (fun p => p.1) negQuery ψ =
      (true :: encCNF ψ, false) := rfl
  have h := OneQuery.mem_SAT_iff_signedKey (encB := encCNF) (S := UNSAT) (r := fun _ => 1)
    (q := fun p => p.1) (d := negQuery) (fun _ => le_rfl) mem_SAT_iff_negQuery ψ
  rw [hkey] at h
  exact ⟨rfl, h⟩

/-- With the marked encodings of the formulas as words, no two pairs of nodes share a label, so a
bound larger than the tree keeps every node. -/
example : OneQuery.accepts (fun ψ => (true :: encCNF ψ, false)) 8
      [[(0, true), (1, false)], [(1, true)]] = true ∧
    OneQuery.accepts (fun ψ => (true :: encCNF ψ, false)) 8
      [[(0, true)], [(0, false)]] = false := by
  decide

/-- The hypotheses of `OneQuery.accepts_iff` are satisfiable with signed labels of the sign
`false`: the marked encoding of a formula lies in the marked encodings of unsatisfiable formulas
exactly when the formula is unsatisfiable. -/
example (φ : CNF ℕ) :
    let L := (encCNF φ).length
    let M := L * L * (16 * L + 21) + L + 1
    OneQuery.accepts (fun ψ => (true :: encCNF ψ, false)) ((M + 1) * 2 ^ M) φ = true ↔
      φ ∈ SAT := by
  intro L M
  refine OneQuery.accepts_iff (K := List.cons true '' (encCNF '' UNSAT)) (M := M) (fun ψ => ?_)
    (fun a b ha hb hla hlb => ?_) (fun s hs => card_le_of_length_le s fun w hw => (hs w hw).2)
  · rw [List.cons_injective.mem_set_image, encCNF.injective.mem_set_image]
    simp [UNSAT, SAT]
  · have hvars := SAT.length_vars_le φ
    have hla' : a.length ≤ L := hla.trans hvars
    have hlb' : b.length ≤ L := hlb.trans hvars
    have := Mahaney.length_encCNF_disj_le ha hb
    simp only [List.length_cons]
    dsimp only [M]
    have : a.length * b.length * (16 * (encCNF φ).length + 21) ≤ L * L * (16 * L + 21) := by
      gcongr
    omega

/-! ### The left set of `SAT` -/

/-- The clauses of `SAT.atLeast`: one for each position with the value `true`, listing the
variables at earlier positions with the value `false` and its own. -/
example : SAT.atLeast [(0, true), (1, false), (2, true)] = [[(0, true)], [(1, true), (2, true)]] :=
  by decide

/-- `SAT.atLeast` compares lexicographically: the assignment `0 ↦ false, 1 ↦ true, 2 ↦ false`
reads `[false, true, false]` along `0, 1, 2`, which is below `[true, false, true]` and above
`[false, false, true]`. -/
example : (SAT.atLeast [(0, true), (1, false), (2, true)]).eval (· == 1) = false ∧
    (SAT.atLeast [(0, false), (1, false), (2, true)]).eval (· == 1) = true ∧
    ¬([true, false, true] ≤ [false, true, false]) ∧ [false, false, true] ≤ [false, true, false] :=
  by decide

/-- The only witness of `¬x₀ ∧ x₁` is `[false, true]`, so its left set contains `[false, false]`
and `[false, true]` but not `[true, false]`. -/
example : ([[(0, false)], [(1, true)]], [false, false]) ∈ LeftSAT ∧
    ([[(0, false)], [(1, true)]], [false, true]) ∈ LeftSAT ∧
    ([[(0, false)], [(1, true)]], [true, false]) ∉ LeftSAT := by
  refine ⟨⟨rfl, (· == 1), rfl, by decide⟩, ⟨rfl, (· == 1), rfl, by decide⟩, ?_⟩
  rintro ⟨-, σ, hσ, hle⟩
  have h0 : σ 0 = false := by
    simpa [CNF.eval, Clause.eval, Literal.eval] using (List.all_eq_true.1 hσ) _ List.mem_cons_self
  have hv : CNF.vars [[((0 : ℕ), false)], [(1, true)]] = [0, 1] := rfl
  rw [hv, List.map_cons, List.map_cons, List.map_nil, h0] at hle
  revert hle
  cases σ 1 <;> decide

/-- `SAT` and its left set reduce to each other. -/
example : PolyTimeReducible encCNF (encPair encCNF encBits) SAT LeftSAT ∧
    LeftSAT ∈ NP (encPair encCNF encBits) :=
  ⟨SAT_polyTimeReducible_LeftSAT, LeftSAT_mem_NP⟩

/-! ### Sparse sets hard under conjunctive reductions -/

/-- `SEARCH-RIGHT` with the queries `n ↦ [n / 2]`: with the bound `1` it keeps `1`, whose successor
`2` asks the new query `1` while one query has been seen, and the last node; with the bound `2` it
also keeps `3`, whose successor asks the new query `2` while two have been seen. -/
example : Conjunctive.searchRight (fun n : ℕ => [n / 2]) 1 [0, 1, 2, 3, 4, 5] = [1, 5] ∧
    Conjunctive.searchRight (fun n : ℕ => [n / 2]) 2 [0, 1, 2, 3, 4, 5] = [1, 3, 5] ∧
    Conjunctive.prune (fun n : ℕ => [n / 2]) 1 [5, 4, 3, 2, 1, 0] = [5, 1] := by
  decide

/-- `SEARCH-RIGHT` keeps the end of a run whose queries lie in a set with one member: the queries of
`0` and `1` are `0`, and `2` asks `1`. -/
example : 1 ∈ Conjunctive.searchRight (fun n : ℕ => [n / 2]) 1 [0, 1, 2, 3, 4, 5] :=
  Conjunctive.mem_searchRight (K := {0}) (A := [0]) (B := [2, 3, 4, 5])
    (fun T hT => (Finset.card_le_card (s := T) (t := {0}) fun u hu => by simpa using hT u hu).trans
      (by simp))
    (by decide) fun z hz => by
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
      subst hz
      exact ⟨1, by decide, by simp⟩

/-- With the encodings of the formulas as single queries, a bound larger than the tree keeps every
node and the procedure is a brute-force search. -/
example :
    Conjunctive.accepts (fun ψ => [encCNF ψ]) 8 [[(0, true), (1, false)], [(1, true)]] = true ∧
    Conjunctive.accepts (fun ψ => [encCNF ψ]) 8 [[(0, true)], [(0, false)]] = false := by
  decide

open Classical in
/-- The hypotheses of `Conjunctive.accepts_iff` are satisfiable: queries that are empty for
satisfiable formulas and the empty word otherwise reduce `SAT` conjunctively to the empty set, and
the bound `0` keeps at most two nodes per level. -/
example (φ : CNF ℕ) :
    Conjunctive.accepts (fun ψ => if ψ ∈ SAT then [] else [[]]) 0 φ = true ↔ φ ∈ SAT := by
  refine Conjunctive.accepts_iff (K := ∅) (M := 0) (fun ψ => ?_) (fun a _ _ w hw => ?_)
    (fun T hT => ?_)
  · split <;> simp_all
  · split at hw <;> simp_all
  · exact (Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun w hw => (hT w hw).1)).le

/-! ### Pruning along a Hausdorff decomposition -/

/-- The sets `C 0 = {0, …, 6}`, `C 1 = {2, …, 6}`, `C 2 = {2, 3}` and `C 3 = ∅`, a Hausdorff
decomposition `(C 0 \ C 1) ∪ (C 2 \ C 3) = {0, 1, 2, 3}`. -/
private def hausdorff : ℕ → ℕ → Bool
  | 0, y => y ≤ 6
  | 1, y => 2 ≤ y && y ≤ 6
  | 2, y => 2 ≤ y && y ≤ 3
  | _, _ => false

/-- One query per node and set: `0` for the members of `C j`, and a query naming the node
otherwise, so that each `C j` reduces conjunctively to `{0}`. -/
private def hausdorffQueries (j y : ℕ) : List ℕ := [if hausdorff j y then 0 else y + 1]

/-- On the level `0, …, 7`: `SEARCH-RIGHT` from `0` keeps `6`, the end of the run in `C 0`, and the
last node; `SEARCH-LEFT` from `6` keeps `2`, the start of the run in `C 1`, and the first node;
`PRUNE` keeps `3`, the last node of `{0, 1, 2, 3}`. -/
example : BTT.searchRightFrom (hausdorffQueries 0) 1 (List.range 8) 0 = [6, 7] ∧
    BTT.searchLeftFrom (hausdorffQueries 1) 1 (List.range 8) 6 = [2, 0] ∧
    BTT.prune hausdorffQueries 1 2 (List.range 8) = [0, 1, 2, 3, 6, 7] := by
  decide

/-- The hypotheses of `BTT.getElem_mem_prune` hold for this decomposition, with the target `{0}`
and the bound `1`. -/
example : (List.range 8)[3] ∈ BTT.prune hausdorffQueries 1 2 (List.range 8) :=
  BTT.getElem_mem_prune (C := fun j y => hausdorff j y = true) (K := fun _ => {w | w = 0})
    (by decide) (fun j y _ h => by rcases j with _ | _ | _ | j <;> simp_all [hausdorff]; omega)
    (by decide) (by decide)
    fun _ _ T hT => Finset.card_le_one.2 fun a ha b hb => (hT a ha).trans (hT b hb).symm

/-! ### Sparse sets hard under bounded truth-table reductions -/

/-- The parity of the number of `true` answers. -/
private def parityTable (v : List Bool) : Bool := v.count true % 2 == 1

/-- Below the answers `11`, the chain `11 > 10` alternates from `false` to `true`, so `11` is in the
first Hausdorff set of the parity table; `10` is in the zeroth, where the parity is `true`. -/
example : BTT.Hausdorff parityTable [true, true] 1 ∧ BTT.Hausdorff parityTable [true, false] 0 :=
  ⟨⟨[true, true], [[true, false]], by unfold BTT.StepBelow; decide, rfl, by decide, by decide⟩,
    ⟨[true, false], [], by simp, rfl, by decide, by decide⟩⟩

/-- The Hausdorff decomposition of the parity table: the answers `10` lie in the zeroth set and
not the first one, and the answers `11` in no difference `C (2 d) \ C (2 d + 1)`. -/
example : (∃ d < 2, BTT.Hausdorff parityTable [true, false] (2 * d) ∧
      ¬BTT.Hausdorff parityTable [true, false] (2 * d + 1)) ∧
    ¬∃ d < 2, BTT.Hausdorff parityTable [true, true] (2 * d) ∧
      ¬BTT.Hausdorff parityTable [true, true] (2 * d + 1) :=
  ⟨(BTT.eq_true_iff_exists_hausdorff (by decide)).1 (by decide),
    fun h => absurd ((BTT.eq_true_iff_exists_hausdorff (by decide)).2 h) (by decide)⟩

/-- The Hausdorff sets of the identity one-query reduction of any set of natural numbers to itself
reduce conjunctively to tally problems. -/
example (B : Set ℕ) (j : ℕ) : ∃ A : Set ℕ, PolyTimeCTTReducible encUnary encUnary
    {n | BTT.Hausdorff (fun v => v.headD false)
      (truthTableAnswers ((fun p : ℕ × ℕ => p.1) ⁻¹' B) (fun _ => 1) n) j} A :=
  BTT.exists_polyTimeCTTReducible_hausdorff (k := 1) (d := fun p => p.2.headD false)
    ⟨B, .refl _ _⟩ (by fun_prop) (by fun_prop) (by fun_prop) (fun _ => le_rfl) j

/-- Queries that do not come from a reduction break the procedure: with the queries
`[|ψ| + j]` and the bound `0`, the satisfiable `x₀ ∧ x₁` is accepted but the satisfiable
`x₀ ∧ ¬x₁` is rejected, while the unsatisfiable `x₀ ∧ ¬x₀` is always rejected. -/
example : BTT.accepts (fun j ψ => [ψ.length + j]) 1 0 [[(0, true)], [(1, true)]] = true ∧
    BTT.accepts (fun j ψ => [ψ.length + j]) 1 0 [[(0, true)], [(1, false)]] = false ∧
    BTT.accepts (fun j ψ => [ψ.length + j]) 1 0 [[(0, true)], [(0, false)]] = false := by
  decide

open Classical in
/-- The hypotheses of `BTT.accepts_iff` are satisfiable: `SAT` is `C 0 \ C 1` for the sets
`C 0 = SAT` and `C j = ∅` otherwise, which reduce conjunctively to the empty set with no query for
members and the query `0` otherwise. -/
example (φ : CNF ℕ) :
    BTT.accepts (fun j ψ => if j = 0 ∧ ψ ∈ SAT then [] else [0]) 1 1 φ = true ↔ φ ∈ SAT := by
  refine BTT.accepts_iff (C := fun j ψ => j = 0 ∧ ψ ∈ SAT) (A := fun _ => ∅) (M := 0)
    (fun j ψ h => absurd h.1 (by omega)) (fun ψ => ?_) (fun j _ ψ => ?_)
    (fun j _ a _ _ w hw => ?_) le_rfl
  · constructor
    · exact fun h => ⟨0, by omega, ⟨rfl, h⟩, fun h' => absurd h'.1 (by omega)⟩
    · rintro ⟨d, -, ⟨-, h⟩, -⟩
      exact h
  · split <;> simp_all
  · split at hw <;> simp_all

end ComplexityTests.SparseHardSets
