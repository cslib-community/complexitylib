/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.BallPath
public import CslibFrontier.Logics.FirstOrder.Locality.Hanf
import CslibFrontier.Tactic.FirstOrder.Simp
import Mathlib.Basic.Finite.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.SuccPred.Nat

/-!
# Transitive closure and reachability are not first-order: proofs by Gaifman locality

Gaifman locality ([Libkin, Corollary 4.13][Libkin2004], `NbhdIso.formula_realize_iff`) says that,
in a finite structure, tuples with isomorphic radius-`(3 ^ (n + 1) - 1) / 2` neighborhoods satisfy
the same formulas of quantifier rank at most `n`. This module derives from it that transitive
closure and reachability are not first-order definable, following [Libkin, §4.1, Figure 4.1
(p. 46) and the discussion after Definition 4.7 (p. 49)][Libkin2004], and checks Libkin's
observation that the locality radius must be exponential in the quantifier rank
([Libkin, §4.3, p. 54][Libkin2004]).

A binary relation `R` on `M` is a structure of the language of graphs, `relStructure R`, with
`adj` read as `R` itself, so that directed graphs need no new language. Its Gaifman graph is the
symmetrization `SimpleGraph.fromRel R` (`gaifmanGraph_relStructure`). For the covering relation
`⋖` of a preorder it is the Hasse diagram (`gaifmanGraph_covBy`); on `Fin N` this is the path
graph, and `(Fin N, ⋖)` is the successor relation on `N` points.

* **Transitive closure.** On the successor relation, two points `a < b` far from each other and
  from both ends have isomorphic neighborhoods in either order, so they satisfy the same formulas
  of bounded rank in either order (`realize_swap_covBy`). The reflexive–transitive closure of `⋖`
  on `Fin N` is `≤` and its transitive closure is `<`. So a formula of quantifier rank `q` that
  defines either closure on `Fin N` forces `N ≤ 2 · 3 ^ (q + 1)`
  (`card_le_of_realize_iff_reflTransGen`, `card_le_of_realize_iff_transGen`). Hence no formula
  defines the reflexive–transitive closure, or the transitive closure, of the edge relation on all
  finite structures (`not_exists_formula_reflTransGen`, `not_exists_formula_transGen`).
* **Reachability in one graph.** In the disjoint union `G ⊕g G` of two copies of a finite simple
  graph, a pair of vertices of one copy at distance more than `2r + 1` and the corresponding pair
  across the two copies have isomorphic radius-`r` neighborhoods (`nbhdIso_sum`). Only the first
  pair is connected. So a formula of quantifier rank `q` that defines reachability in `G ⊕g G`
  bounds the distance of connected vertices of `G` by `3 ^ (q + 1)`
  (`edist_le_of_realize_iff_reachable`). For two paths on `m` vertices this forces
  `m ≤ 3 ^ (q + 1) + 1` (`card_le_of_realize_iff_reachable_pathGraph`), and no formula defines
  reachability on all finite simple graphs (`not_exists_formula_reachable`).
* **The locality radius is exponential.** The formulas `distLE k` have quantifier rank `k` and say
  that the distance is at most `2 ^ k` (`realize_distLE`). In two disjoint copies of a path on
  `2 ^ (k + 1) + 1` vertices, the two ends of one copy and the corresponding pair across the copies
  have isomorphic radius-`(2 ^ k - 1)` neighborhoods, but only the first pair satisfies
  `distLE (k + 1)` (`exists_nbhdIso_realize_distLE`). So any radius that makes all formulas of rank
  `n` Gaifman-local on finite graphs is at least `2 ^ (n - 1)` (`two_pow_le_of_gaifman_radius`),
  against the upper bound `(3 ^ (n + 1) - 1) / 2` of [Libkin, Corollary 4.13][Libkin2004]. The
  exact value `2 ^ n - 1` of [Libkin, Exercises 4.10 and 4.11 (pp. 63–64)][Libkin2004] is not
  formalized here.

All formulas range over the pure graph vocabulary `FirstOrder.Language.graph`, with no built-in
order or arithmetic. The constants come from Gaifman's radius; they are not claimed to be sharp.
That transitive closure is definable in FO(TC), so that FO(TC) is strictly more expressive than
FO, is `Cslib.Logic.FO.TC.exists_formula_not_fo_equivalent`.

## Main definitions

* `Cslib.Logic.FO.Locality.relStructure`: a binary relation as a structure of the language of
  graphs.
* `Cslib.Logic.FO.Locality.distLE`: the formulas `distance ≤ 2 ^ k`, of quantifier rank `k`.

## Main results

* `Cslib.Logic.FO.Locality.realize_swap_covBy`: Gaifman locality on the successor relation
  [Libkin, Figure 4.1][Libkin2004].
* `Cslib.Logic.FO.Locality.card_le_of_realize_iff_reflTransGen`,
  `Cslib.Logic.FO.Locality.card_le_of_realize_iff_transGen`: the quantitative bounds for transitive
  closure.
* `Cslib.Logic.FO.Locality.not_exists_formula_reflTransGen`,
  `Cslib.Logic.FO.Locality.not_exists_formula_transGen`: transitive closure is not first-order.
* `Cslib.Logic.FO.Locality.edist_le_of_realize_iff_reachable`,
  `Cslib.Logic.FO.Locality.not_exists_formula_reachable`: reachability is not first-order.
* `Cslib.Logic.FO.Locality.exists_nbhdIso_realize_distLE`,
  `Cslib.Logic.FO.Locality.two_pow_le_of_gaifman_radius`: the locality radius is exponential.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Locality

universe u

/-! ### Binary relations as structures -/

/-- A binary relation as a structure of the language of graphs: `adj` is read as the relation
itself, with no symmetry or irreflexivity assumed. -/
@[instance_reducible]
def relStructure {M : Type*} (R : M → M → Prop) : Language.graph.Structure M where
  RelMap | .adj => fun x => R (x 0) (x 1)

@[simp] theorem relMap_relStructure {M : Type*} (R : M → M → Prop) (x y : M) :
    (letI := relStructure R; RelMap adj ![x, y]) ↔ R x y :=
  Iff.rfl

/-- The Gaifman graph of a binary relation is its symmetrization. -/
theorem gaifmanGraph_relStructure {M : Type*} (R : M → M → Prop) :
    @gaifmanGraph Language.graph M (relStructure R) = SimpleGraph.fromRel R := by
  let := relStructure R
  ext x y
  rw [gaifmanGraph_adj, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, l, R', t, hR, ⟨i, rfl⟩, j, rfl⟩
    cases R'
    have h01 : ∀ p : Fin 2, p = 0 ∨ p = 1 := fun p => by fin_cases p <;> simp
    change R (t 0) (t 1) at hR
    refine ⟨hne, ?_⟩
    rcases h01 i with rfl | rfl <;> rcases h01 j with rfl | rfl
    · exact absurd rfl hne
    · exact .inl hR
    · exact .inr hR
    · exact absurd rfl hne
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, 2, .adj, ![x, y], h, ⟨0, rfl⟩, 1, rfl⟩
    · exact ⟨hne, 2, .adj, ![y, x], h, ⟨1, rfl⟩, 0, rfl⟩

/-- The Gaifman graph of the covering relation of a preorder is its Hasse diagram. -/
theorem gaifmanGraph_covBy {α : Type*} [Preorder α] :
    @gaifmanGraph Language.graph α (relStructure (· ⋖ ·)) = SimpleGraph.hasse α := by
  rw [gaifmanGraph_relStructure]
  ext x y
  rw [SimpleGraph.fromRel_adj, SimpleGraph.hasse_adj]
  exact ⟨fun h => h.2, fun h => ⟨fun hxy => by subst hxy; rcases h with h | h <;> exact h.ne rfl,
    h⟩⟩

/-! ### Transitive closure on the successor relation -/

section Chain

variable {N : ℕ}

/-- `3 ^ n` is odd, so it is `2r + 1` for the Hanf radius `r = (3 ^ n - 1) / 2`. -/
private theorem three_pow_eq_two_mul_add_one (n : ℕ) : 3 ^ n = 2 * ((3 ^ n - 1) / 2) + 1 := by
  obtain ⟨k, hk⟩ : Odd (3 ^ n) := Odd.pow (by decide)
  omega

private theorem mem_ball_covBy {r : ℕ} {a x : Fin N} :
    x ∈ @ball Language.graph (Fin N) (relStructure (· ⋖ ·)) 1 (fun _ => a) r ↔
      (x : ℕ) ≤ a + r ∧ (a : ℕ) ≤ x + r := by
  rw [@mem_ball_const, gaifmanGraph_covBy, ← SimpleGraph.pathGraph,
    SimpleGraph.edist_pathGraph, Nat.cast_le]
  omega

/-- Translation along the successor relation is an isomorphism of radius-`r` neighborhoods of
single points that are at least `r` away from both ends. -/
private theorem isNbhdIso_shift {r : ℕ} {a b : Fin N} (ha : r ≤ (a : ℕ)) (ha' : (a : ℕ) + r < N)
    (hb : r ≤ (b : ℕ)) (hb' : (b : ℕ) + r < N) :
    @IsNbhdIso Language.graph (Fin N) (Fin N) (relStructure (· ⋖ ·))
      (relStructure (· ⋖ ·)) 1 r (fun _ => a) (fun _ => b)
      (fun x => ⟨min (x + b - a) (N - 1), by omega⟩) := by
  let := relStructure (M := Fin N) (· ⋖ ·)
  refine ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun _ => ?_, ?_⟩
  · rw [mem_ball_covBy] at hx ⊢
    simp only
    omega
  · rw [mem_ball_covBy] at hx hy
    have := congrArg Fin.val hxy
    simp only at this
    exact Fin.ext (by omega)
  · rw [mem_ball_covBy] at hy
    refine ⟨⟨y + a - b, by omega⟩, ?_, Fin.ext ?_⟩
    · rw [mem_ball_covBy]
      simp only
      omega
    · simp only
      omega
  · exact Fin.ext (by simp only; omega)
  · intro l R t ht
    match l, R with
    | 2, .adj =>
      have h0 := mem_ball_covBy.1 (ht 0)
      have h1 := mem_ball_covBy.1 (ht 1)
      change ((_ : Fin N) ⋖ _) ↔ ((_ : Fin N) ⋖ _)
      simp only [Fin.covBy_iff, Nat.covBy_iff_add_one_eq, Function.comp_apply]
      omega

/-- **Gaifman locality on the successor relation** ([Libkin, §4.1, Figure 4.1][Libkin2004]): two
points `a < b` of the successor relation `(Fin N, ⋖)`, far from each other and from both ends,
satisfy the same formulas of quantifier rank at most `n` in either order. -/
theorem realize_swap_covBy {n : ℕ} {φ : Language.graph.Formula (Fin 2)}
    (hφ : quantifierRank φ ≤ n) {a b : Fin N} (hab : (a : ℕ) + 3 ^ (n + 1) < b)
    (ha : (3 ^ (n + 1) - 1) / 2 ≤ (a : ℕ)) (hb : (b : ℕ) + (3 ^ (n + 1) - 1) / 2 < N) :
    (letI := relStructure (M := Fin N) (· ⋖ ·); φ.Realize ![a, b]) ↔
      (letI := relStructure (M := Fin N) (· ⋖ ·); φ.Realize ![b, a]) := by
  let := relStructure (M := Fin N) (· ⋖ ·)
  have h3 := three_pow_eq_two_mul_add_one (n + 1)
  set r := (3 ^ (n + 1) - 1) / 2
  have far : ∀ x y : Fin N, (x : ℕ) + (2 * r + 1) < y →
      ((2 * r + 1 : ℕ) : ℕ∞) < (gaifmanGraph Language.graph (Fin N)).edist x y := by
    intro x y hxy
    rw [gaifmanGraph_covBy, ← SimpleGraph.pathGraph, SimpleGraph.edist_pathGraph, Nat.cast_lt]
    omega
  have H := IsNbhdIso.snoc (k := 1) (a := fun _ => a) (b := fun _ => b)
    (isNbhdIso_shift (r := r) (by omega) (by omega) (by omega) (by omega))
    (isNbhdIso_shift (r := r) (a := b) (b := a) (by omega) (by omega) (by omega) (by omega))
    (fun _ => far a b (by omega))
    (fun _ => by rw [SimpleGraph.edist_comm]; exact far a b (by omega))
  have e1 : (Fin.snoc (fun _ : Fin 1 => a) b : Fin 2 → Fin N) = ![a, b] := by
    ext i; fin_cases i <;> rfl
  have e2 : (Fin.snoc (fun _ : Fin 1 => b) a : Fin 2 → Fin N) = ![b, a] := by
    ext i; fin_cases i <;> rfl
  rw [e1, e2] at H
  exact H.formula_realize_iff hφ

/-- A formula that defines on the successor relation a relation `Q` with `Q a b` and `¬ Q b a`
for all `a < b` forces a short chain: `N ≤ 2 · 3 ^ (q + 1)` for its quantifier rank `q`. -/
private theorem card_le_of_realize_of_lt {φ : Language.graph.Formula (Fin 2)}
    {Q : Fin N → Fin N → Prop} (hQ : ∀ a b : Fin N, a < b → Q a b ∧ ¬ Q b a)
    (hφ : ∀ a b : Fin N, (letI := relStructure (M := Fin N) (· ⋖ ·); φ.Realize ![a, b]) ↔ Q a b) :
    N ≤ 2 * 3 ^ (quantifierRank φ + 1) := by
  by_contra hN
  have h3 := three_pow_eq_two_mul_add_one (quantifierRank φ + 1)
  generalize (3 ^ (quantifierRank φ + 1) - 1) / 2 = r at h3
  let a : Fin N := ⟨r, by omega⟩
  let b : Fin N := ⟨3 * r + 2, by omega⟩
  have hab : a < b := Fin.lt_def.2 (by simp only [a, b]; omega)
  have := realize_swap_covBy (φ := φ) le_rfl (a := a) (b := b) (by simp only [a, b]; omega)
    (by simp only [a]; omega) (by simp only [b]; omega)
  rw [hφ, hφ] at this
  exact (hQ a b hab).2 (this.1 (hQ a b hab).1)

/-- **Transitive closure is not first-order, quantitatively** ([Libkin, §4.1][Libkin2004]): a
formula of quantifier rank `q` that defines the reflexive–transitive closure of the successor
relation on `Fin N` forces `N ≤ 2 · 3 ^ (q + 1)`. -/
theorem card_le_of_realize_iff_reflTransGen {φ : Language.graph.Formula (Fin 2)}
    (hφ : ∀ a b : Fin N, (letI := relStructure (M := Fin N) (· ⋖ ·); φ.Realize ![a, b]) ↔
      Relation.ReflTransGen (· ⋖ ·) a b) :
    N ≤ 2 * 3 ^ (quantifierRank φ + 1) :=
  card_le_of_realize_of_lt (fun a b hab => by
    rw [← le_iff_reflTransGen_covBy, ← le_iff_reflTransGen_covBy]
    exact ⟨hab.le, not_le.2 hab⟩) hφ

/-- **Transitive closure is not first-order, quantitatively**: the same bound for the transitive
closure of the successor relation on `Fin N`, which is `<`. -/
theorem card_le_of_realize_iff_transGen {φ : Language.graph.Formula (Fin 2)}
    (hφ : ∀ a b : Fin N, (letI := relStructure (M := Fin N) (· ⋖ ·); φ.Realize ![a, b]) ↔
      Relation.TransGen (· ⋖ ·) a b) :
    N ≤ 2 * 3 ^ (quantifierRank φ + 1) :=
  card_le_of_realize_of_lt (fun a b hab => by
    rw [← lt_iff_transGen_covBy, ← lt_iff_transGen_covBy]
    exact ⟨hab, lt_asymm hab⟩) hφ

end Chain

/-- The successor relation on `N` points, carried to `ULift (Fin N)` in any universe, as a strong
homomorphism from `(Fin N, ⋖)`. -/
private def ulift (N : ℕ) :
    @Equiv Language.graph (Fin N) (ULift.{u} (Fin N)) (relStructure (· ⋖ ·))
      (@Equiv.inducedStructure Language.graph (Fin N) (ULift.{u} (Fin N))
        (relStructure (· ⋖ ·)) Equiv.ulift.symm) :=
  @Equiv.inducedStructureEquiv Language.graph (Fin N) (ULift.{u} (Fin N)) (relStructure (· ⋖ ·))
    Equiv.ulift.symm

/-- A formula over `(Fin N, ⋖)`, read in its copy on `ULift (Fin N)`. -/
private theorem realize_ulift {N : ℕ} (φ : Language.graph.Formula (Fin 2)) (a b : Fin N) :
    (letI := @Equiv.inducedStructure Language.graph (Fin N) (ULift.{u} (Fin N))
        (relStructure (· ⋖ ·)) Equiv.ulift.symm;
      φ.Realize ![ULift.up a, ULift.up b]) ↔
      (letI := relStructure (M := Fin N) (· ⋖ ·); φ.Realize ![a, b]) := by
  let := relStructure (M := Fin N) (· ⋖ ·)
  let := @Equiv.inducedStructure Language.graph (Fin N) (ULift.{u} (Fin N)) _ Equiv.ulift.symm
  have h := StrongHomClass.realize_formula (ulift.{u} N) φ (v := ![a, b])
  have h2 : (ulift.{u} N ∘ ![a, b]) = ![ULift.up a, ULift.up b] := by
    ext i; fin_cases i <;> rfl
  rwa [h2] at h

/-- **Transitive closure is not first-order definable** ([Libkin, §4.1][Libkin2004]): no formula
`φ(x, y)` of the language of graphs, read as the language of directed graphs, defines the
reflexive–transitive closure of the edge relation on all finite structures. -/
theorem not_exists_formula_reflTransGen :
    ¬ ∃ φ : Language.graph.Formula (Fin 2), ∀ (M : Type u) [Finite M]
      [Language.graph.Structure M] (a b : M),
      φ.Realize ![a, b] ↔ Relation.ReflTransGen (fun x y : M => RelMap adj ![x, y]) a b := by
  rintro ⟨φ, hφ⟩
  set N := 2 * 3 ^ (quantifierRank φ + 1) + 1
  let := @Equiv.inducedStructure Language.graph (Fin N) (ULift.{u} (Fin N))
    (relStructure (· ⋖ ·)) Equiv.ulift.symm
  have := card_le_of_realize_iff_reflTransGen (N := N) (φ := φ) fun a b => by
    rw [← realize_ulift, hφ]
    exact ⟨fun h => h.lift ULift.down fun _ _ h => h, fun h => h.lift ULift.up fun _ _ h => h⟩
  omega

/-- **Transitive closure is not first-order definable**: no formula `φ(x, y)` of the language of
graphs defines the transitive closure of the edge relation on all finite structures. -/
theorem not_exists_formula_transGen :
    ¬ ∃ φ : Language.graph.Formula (Fin 2), ∀ (M : Type u) [Finite M]
      [Language.graph.Structure M] (a b : M),
      φ.Realize ![a, b] ↔ Relation.TransGen (fun x y : M => RelMap adj ![x, y]) a b := by
  -- `φ(x, y) ∨ x = y` would then define the reflexive–transitive closure.
  rintro ⟨φ, hφ⟩
  refine not_exists_formula_reflTransGen.{u} ⟨φ ⊔ (Term.var 0).equal (Term.var 1), ?_⟩
  intro M _ _ a b
  rw [Relation.reflTransGen_iff_eq_or_transGen, Formula.realize_sup, hφ, Formula.realize_equal]
  simp only [Term.realize_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact or_comm.trans (or_congr_left eq_comm)

/-! ### Undirected reachability -/

section Undirected

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph isomorphism is an isomorphism of all neighborhoods. -/
theorem isNbhdIso_of_iso (e : G ≃g H) {k r : ℕ} {a : Fin k → V} {b : Fin k → W}
    (hab : ∀ i, e (a i) = b i) :
    @IsNbhdIso Language.graph V W G.structure H.structure k r a b e := by
  let := G.structure
  let := H.structure
  have hball : ∀ x, x ∈ ball Language.graph a r ↔ e x ∈ ball Language.graph b r := by
    intro x
    simp only [mem_ball, gaifmanGraph_structure, ← hab, e.edist_eq]
  refine ⟨⟨fun x hx => (hball x).1 hx, fun x _ y _ h => e.injective h, fun y hy => ?_⟩,
    hab, ?_⟩
  · exact ⟨e.symm y, (hball _).2 (by simpa using hy), by simp⟩
  · intro l R t _
    match l, R with
    | 2, .adj => exact e.map_adj_iff

/-- The fold of `G ⊕g G` onto `G`. -/
private def foldHom : G ⊕g G →g G where
  toFun := Sum.elim id id
  map_rel' {x y} h := by
    cases x <;> cases y <;> simp_all

/-- **Far-apart pairs in one copy look like pairs across two copies**: in `G ⊕g G`, if `u` and
`v` are at distance more than `2r + 1` in `G`, then the radius-`r` neighborhoods of
`(inl u, inl v)` and `(inl u, inr v)` are isomorphic. -/
theorem nbhdIso_sum {r : ℕ} {u v : V} (huv : ((2 * r + 1 : ℕ) : ℕ∞) < G.edist u v) :
    @NbhdIso Language.graph (V ⊕ V) (V ⊕ V) (G ⊕g G).structure (G ⊕g G).structure 2 r
      ![.inl u, .inl v] ![.inl u, .inr v] := by
  let := (G ⊕g G).structure
  have H := IsNbhdIso.snoc (k := 1) (a := fun _ => Sum.inl u) (b := fun _ => Sum.inl u)
    (c := Sum.inl v) (c' := Sum.inr v) (IsNbhdIso.refl r _)
    (isNbhdIso_of_iso (SimpleGraph.Iso.sumComm (G := G) (H := G)) (fun _ => rfl))
    (fun _ => by
      rw [gaifmanGraph_structure]
      exact huv.trans_le (foldHom.edist_le (.inl u) (.inl v)))
    (fun _ => by
      rw [gaifmanGraph_structure, SimpleGraph.edist_eq_top_of_not_reachable
        (SimpleGraph.not_reachable_sum_inl_inr u v)]
      exact ENat.natCast_lt_top _)
  have e1 : (Fin.snoc (fun _ : Fin 1 => (Sum.inl u : V ⊕ V)) (.inl v) : Fin 2 → V ⊕ V) =
      ![.inl u, .inl v] := by
    ext i; fin_cases i <;> rfl
  have e2 : (Fin.snoc (fun _ : Fin 1 => (Sum.inl u : V ⊕ V)) (.inr v) : Fin 2 → V ⊕ V) =
      ![.inl u, .inr v] := by
    ext i; fin_cases i <;> rfl
  rwa [e1, e2] at H

/-- **Gaifman locality in a disjoint union of two copies**: if `u` and `v` are at distance more
than `3 ^ (n + 1)` in a finite graph `G`, then `(inl u, inl v)` and `(inl u, inr v)` satisfy the
same formulas of quantifier rank at most `n` in `G ⊕g G`. -/
theorem realize_sum_inl_iff_inr [Finite V] {n : ℕ} {φ : Language.graph.Formula (Fin 2)}
    (hφ : quantifierRank φ ≤ n) {u v : V} (huv : ((3 ^ (n + 1) : ℕ) : ℕ∞) < G.edist u v) :
    (letI := (G ⊕g G).structure; φ.Realize ![(.inl u : V ⊕ V), .inl v]) ↔
      (letI := (G ⊕g G).structure; φ.Realize ![(.inl u : V ⊕ V), .inr v]) := by
  let := (G ⊕g G).structure
  rw [three_pow_eq_two_mul_add_one] at huv
  exact (nbhdIso_sum huv).formula_realize_iff hφ

/-- **Reachability is not first-order on a fixed graph**: if a formula `φ(x, y)` of quantifier
rank `q` defines reachability in `G ⊕g G`, then no two vertices of `G` that are connected in `G`
are at distance more than `3 ^ (q + 1)`. -/
theorem edist_le_of_realize_iff_reachable [Finite V] {φ : Language.graph.Formula (Fin 2)}
    (hφ : ∀ x y : V ⊕ V, (letI := (G ⊕g G).structure; φ.Realize ![x, y]) ↔
      (G ⊕g G).Reachable x y) {u v : V} (huv : G.Reachable u v) :
    G.edist u v ≤ ((3 ^ (quantifierRank φ + 1) : ℕ) : ℕ∞) := by
  by_contra h
  have := realize_sum_inl_iff_inr (φ := φ) le_rfl (not_le.1 h)
  rw [hφ, hφ] at this
  exact SimpleGraph.not_reachable_sum_inl_inr u v
    (this.1 (huv.map SimpleGraph.Embedding.sumInl.toHom))

/-- **Reachability is not first-order on a fixed graph, for paths**: a formula of quantifier rank
`q` that defines reachability in the disjoint union of two paths on `m` vertices forces
`m ≤ 3 ^ (q + 1) + 1`. -/
theorem card_le_of_realize_iff_reachable_pathGraph {m : ℕ} {φ : Language.graph.Formula (Fin 2)}
    (hφ : ∀ x y : Fin m ⊕ Fin m,
      (letI := (SimpleGraph.pathGraph m ⊕g SimpleGraph.pathGraph m).structure;
        φ.Realize ![x, y]) ↔ (SimpleGraph.pathGraph m ⊕g SimpleGraph.pathGraph m).Reachable x y) :
    m ≤ 3 ^ (quantifierRank φ + 1) + 1 := by
  by_contra hm
  have : 0 < 3 ^ (quantifierRank φ + 1) := pow_pos (by decide) _
  have h := edist_le_of_realize_iff_reachable hφ (u := ⟨0, by omega⟩) (v := ⟨m - 1, by omega⟩)
    ((SimpleGraph.connected_pathGraph.2 (by omega)).preconnected _ _)
  rw [SimpleGraph.edist_pathGraph, Nat.cast_le] at h
  simp only at h
  omega

/-- **Reachability is not first-order definable** on finite graphs: no formula `φ(x, y)` of the
language of graphs defines reachability in every finite simple graph. -/
theorem not_exists_formula_reachable :
    ¬ ∃ φ : Language.graph.Formula (Fin 2), ∀ (V : Type u) [Finite V] (G : SimpleGraph V)
      (x y : V), (letI := G.structure; φ.Realize ![x, y]) ↔ G.Reachable x y := by
  rintro ⟨φ, hφ⟩
  have : 0 < 3 ^ (quantifierRank φ + 1) := pow_pos (by decide) _
  set m := 3 ^ (quantifierRank φ + 1) + 2
  let e : ULift.{u} (Fin m) ≃ Fin m := Equiv.ulift
  let G := (SimpleGraph.pathGraph m).comap e
  have hG := SimpleGraph.Iso.comap e (SimpleGraph.pathGraph m)
  have h := edist_le_of_realize_iff_reachable (G := G) (φ := φ)
    (fun x y => hφ (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin m)) (G ⊕g G) x y)
    (u := hG.symm ⟨0, by omega⟩) (v := hG.symm ⟨m - 1, by omega⟩)
    ((SimpleGraph.connected_pathGraph.2 (by omega)).preconnected _ _ |>.map hG.symm.toHom)
  rw [← hG.edist_eq, hG.apply_symm_apply, hG.apply_symm_apply, SimpleGraph.edist_pathGraph,
    Nat.cast_le] at h
  simp only at h
  omega

/-! ### The locality radius must be exponential -/

/-- Libkin's distance formulas ([Libkin, §4.3, p. 54][Libkin2004]): `distLE k` has quantifier rank
`k` (`quantifierRank_distLE`) and says that the distance from `x 0` to `x 1` is at most `2 ^ k`
(`realize_distLE`). It is `∃ z, distLE k (x, z) ∧ distLE k (z, y)` for `k + 1`. Libkin's `d_0` is
`E(x, y)`, so his `d_k` asks for a walk of length exactly `2 ^ k`; `distLE 0` is
`x = y ∨ E(x, y)` instead, so that `distLE k` is exactly the closed ball of radius `2 ^ k`. -/
def distLE : ℕ → Language.graph.Formula (Fin 2)
  | 0 => Term.equal (Term.var 0) (Term.var 1) ⊔ adj.formula₂ (Term.var 0) (Term.var 1)
  | k + 1 => (BoundedFormula.relabel (fun i : Fin 2 => ![Sum.inl 0, Sum.inr 0] i) (distLE k) ⊓
      BoundedFormula.relabel (fun i : Fin 2 => ![Sum.inr 0, Sum.inl 1] i) (distLE k)).ex

@[simp] theorem quantifierRank_distLE (k : ℕ) : quantifierRank (distLE k) = k := by
  induction k with
  | zero =>
    simp only [distLE, quantifierRank_sup, Term.equal, Relations.formula₂, Relations.formula,
      quantifierRank_bdEqual, quantifierRank_relations_boundedFormula, max_self]
  | succ k ih =>
    simp only [distLE, quantifierRank_ex, quantifierRank_inf, quantifierRank_relabel, ih, max_self]

theorem realize_distLE_zero {M : Type*} [Language.graph.Structure M] (x y : M) :
    (distLE 0).Realize ![x, y] ↔ x = y ∨ RelMap adj ![x, y] := by
  fo_simp [distLE]

theorem realize_distLE_succ {M : Type*} [Language.graph.Structure M] (k : ℕ) (x y : M) :
    (distLE (k + 1)).Realize ![x, y] ↔
      ∃ z, (distLE k).Realize ![x, z] ∧ (distLE k).Realize ![z, y] := by
  fo_simp [distLE, Formula.Realize]
  refine exists_congr fun z => and_congr ?_ ?_ <;>
  · apply iff_of_eq
    congr 1
    · ext i; fin_cases i <;> rfl
    · exact Subsingleton.elim _ _

/-- `distLE k` says that the distance is at most `2 ^ k`. -/
theorem realize_distLE (G : SimpleGraph V) (k : ℕ) (x y : V) :
    (letI := G.structure; (distLE k).Realize ![x, y]) ↔ G.edist x y ≤ ((2 ^ k : ℕ) : ℕ∞) := by
  let := G.structure
  induction k generalizing x y with
  | zero =>
    rw [realize_distLE_zero, pow_zero, Nat.cast_one, SimpleGraph.edist_le_one_iff_adj_or_eq]
    exact Or.comm
  | succ k ih =>
    have h2 : ((2 ^ (k + 1) : ℕ) : ℕ∞) = ((2 ^ k : ℕ) : ℕ∞) + ((2 ^ k : ℕ) : ℕ∞) := by
      rw [pow_succ, mul_two, Nat.cast_add]
    rw [realize_distLE_succ]
    simp only [ih]
    constructor
    · rintro ⟨z, h1, h2'⟩
      exact SimpleGraph.edist_triangle.trans (h2 ▸ add_le_add h1 h2')
    · intro h
      exact SimpleGraph.exists_edist_le_of_edist_le_add (by rwa [Nat.cast_add, ← h2])

/-- **The locality radius must be exponential in the quantifier rank**
([Libkin, §4.3, p. 54][Libkin2004]): the rank-`(k + 1)` formula `distLE (k + 1)` distinguishes two
pairs whose radius-`(2 ^ k - 1)` neighborhoods are isomorphic. The pairs are the two ends of a
path on `2 ^ (k + 1) + 1` vertices, and an end of that path with the far end of a disjoint copy. -/
theorem exists_nbhdIso_realize_distLE (k : ℕ) :
    ∃ (V : Type) (_ : Finite V) (G : SimpleGraph V) (a b : Fin 2 → V),
      (letI := G.structure; NbhdIso Language.graph (2 ^ k - 1) a b) ∧
      (letI := G.structure; (distLE (k + 1)).Realize a) ∧
      ¬ (letI := G.structure; (distLE (k + 1)).Realize b) := by
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hk' : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  set m := 2 ^ (k + 1) + 1
  let P := SimpleGraph.pathGraph m
  have hP : P.edist ⟨0, by omega⟩ ⟨2 ^ (k + 1), by omega⟩ = ((2 ^ (k + 1) : ℕ) : ℕ∞) := by
    rw [SimpleGraph.edist_pathGraph]
    simp
  refine ⟨Fin m ⊕ Fin m, inferInstance, P ⊕g P, ![.inl ⟨0, by omega⟩, .inl ⟨2 ^ (k + 1), by omega⟩],
    ![.inl ⟨0, by omega⟩, .inr ⟨2 ^ (k + 1), by omega⟩], ?_, ?_, ?_⟩
  · exact nbhdIso_sum (by rw [hP, Nat.cast_lt]; omega)
  · rw [realize_distLE]
    exact ((SimpleGraph.Embedding.sumInl (G := P) (H := P)).toHom.edist_le _ _).trans hP.le
  · rw [realize_distLE, SimpleGraph.edist_eq_top_of_not_reachable
      (SimpleGraph.not_reachable_sum_inl_inr _ _)]
    exact not_le.2 (ENat.natCast_lt_top _)

/-- **No subexponential radius gives Gaifman locality**: if a radius `ρ n` makes every formula of
quantifier rank at most `n` Gaifman-local on finite graphs (as `(3 ^ (n + 1) - 1) / 2` does,
[Libkin, Corollary 4.13][Libkin2004]), then `ρ (k + 1) ≥ 2 ^ k`. This is Libkin's lower bound
`lr(d_k) ≥ 2 ^ (k - 1)`; the exact Gaifman rank `2 ^ n - 1` ([Libkin, Exercise 4.11][Libkin2004])
is not formalized. -/
theorem two_pow_le_of_gaifman_radius {ρ : ℕ → ℕ}
    (hρ : ∀ (n : ℕ) (V : Type) [Finite V] (G : SimpleGraph V) (a b : Fin 2 → V)
      (φ : Language.graph.Formula (Fin 2)), quantifierRank φ ≤ n →
      (letI := G.structure; NbhdIso Language.graph (ρ n) a b) →
      ((letI := G.structure; φ.Realize a) ↔ (letI := G.structure; φ.Realize b))) (k : ℕ) :
    2 ^ k ≤ ρ (k + 1) := by
  by_contra h
  obtain ⟨V, _, G, a, b, hab, ha, hb⟩ := exists_nbhdIso_realize_distLE k
  let := G.structure
  exact hb ((hρ (k + 1) V G a b _ (quantifierRank_distLE _).le (hab.mono (by omega))).1 ha)

end Undirected

end Cslib.Logic.FO.Locality
