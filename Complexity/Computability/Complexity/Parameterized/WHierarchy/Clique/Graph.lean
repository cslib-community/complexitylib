/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded.Certificate
public import Complexity.Computability.Complexity.Parameterized.WHierarchy
public import Complexity.Computability.Complexity.Parameterized.WHierarchy.Clique.Bracket
public import Complexity.Computability.Complexity.Problems.Clique.OfAdj
public import Complexity.Foundations.Data.List.ListsUpTo
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

/-!
# The graph of a circuit of weft one

This file builds, from a circuit of weft at most `1` and depth at most `d` and a weight `k`, a
graph and a clique size (`WCS.toClique`), and shows that the graph has a clique of that size
exactly when the circuit has a satisfying input with `k` ones (`WCS.toClique_mem_Clique_iff`).
This is the graph construction behind the `W[1]`-hardness of `Clique`
[Cygan et al., Chapter 13][CyganEtAl2015] [DowneyFellows1999], in a form adapted to the
certificates of `Cslib.Circuits.Boolean.Unbounded.WeftOne`.

Write `n` for the number of inputs and `kk = min (n + 1) k`. The vertices are of two kinds.

* A *certificate*: at most `2 ^ d` wire-value claims that are valid for the output
  (`WeftOne.claimsValid`).
* A *bracket*: at most `2 ^ (d + 1)` pairs `(j, s)` with `j < kk` and `s < n`, read as "the
  `j`-th selected input is `s`" (`WCS.ToClique.know`).

A certificate is adjacent to a bracket when Kleene evaluation from the partial input that the
bracket describes refutes no check of a claim. Two brackets are adjacent when they are consistent
(`WCS.ToClique.consistent`) and have different lists of indices. The clique size is one more than
the number of lists of at most `2 ^ (d + 1)` indices below `kk`.

A satisfying input with `k` ones gives a clique: its correct certificate, and the correct bracket
of every list of indices. Conversely, a clique of that size has one certificate and one bracket
for each list of indices. The brackets of the one-index lists select `k` increasing positions,
and every check of a claim is at small depth, so it is determined by at most `2 ^ d` inputs
(`WeftOne.exists_determining`), which the bracket of some list of at most `2 ^ (d + 1)` indices
describes (`WCS.ToClique.exists_cover`). The certificate is adjacent to that bracket, so the check
holds on the selected input, which therefore satisfies the circuit.

## Main definitions

* `Cslib.Complexity.WCS.ToClique.vertices`, `Cslib.Complexity.WCS.ToClique.vadj`: the vertices
  and adjacency of the graph.
* `Cslib.Complexity.WCS.toClique`: the graph and clique size of a circuit and a weight.

## Main results

* `Cslib.Complexity.WCS.toClique_mem_Clique_iff`: the graph has a clique of the size exactly
  when the circuit has a satisfying input with `k` ones.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Chapter 13][CyganEtAl2015]
* [R. G. Downey, M. R. Fellows, *Parameterized Complexity*][DowneyFellows1999]
-/

@[expose] public section

namespace Cslib.Complexity.WCS

open Circuits Circuits.Boolean Circuits.Boolean.Unbounded

namespace ToClique

/-! ### The construction -/

/-- The wire-value pairs of the wires of a gate list with `L` gates from `n` inputs. -/
def claimUniverse (n L : ℕ) : List (ℕ × Bool) :=
  (List.range (n + L)).flatMap fun w => [(w, true), (w, false)]

/-- The certificates: lists of at most `2 ^ d` wire-value pairs that are valid for output `o`. -/
def certs (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o : ℕ) : List (List (ℕ × Bool)) :=
  ((claimUniverse n gates.length).listsUpTo (2 ^ d)).filter (WeftOne.claimsValid d n gates o)

/-- The index-position pairs: `(j, s)` with `j < kk` and `s < n`. -/
def pairs (n kk : ℕ) : List (ℕ × ℕ) :=
  (List.range kk).flatMap fun j => (List.range n).map (j, ·)

/-- The brackets: lists of at most `2 ^ (d + 1)` index-position pairs. -/
def brackets (d n kk : ℕ) : List (List (ℕ × ℕ)) :=
  (pairs n kk).listsUpTo (2 ^ (d + 1))

/-- The index lists: lists of at most `2 ^ (d + 1)` indices below `kk`. -/
def classes (d kk : ℕ) : List (List ℕ) :=
  (List.range kk).listsUpTo (2 ^ (d + 1))

/-- The partial input that a bracket describes. -/
def knowList (n kk : ℕ) (P : List (ℕ × ℕ)) : List (Option Bool) :=
  (List.range n).map (know kk P)

/-- A bracket refutes a list of claims when Kleene evaluation from the partial input it describes
finds a check of a claim false. -/
def refutes (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (cl : List (ℕ × Bool))
    (P : List (ℕ × ℕ)) : Bool :=
  (cl.flatMap (WeftOne.claimChecks n gates)).any fun e =>
    (kleeneEval (knowList n kk P) gates).getD e.1 none == some (!e.2)

/-- A vertex: a list of claims tagged `true`, or a bracket tagged `false`. -/
abbrev Vertex : Type := Bool × (List (ℕ × Bool) × List (ℕ × ℕ))

/-- The vertices: the certificates, then the brackets. -/
def vertices (d n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o : ℕ) : List Vertex :=
  (certs d n gates o).map (fun cl => (true, cl, [])) ++
    (brackets d n kk).map (fun P => (false, [], P))

/-- Adjacency: a certificate and a bracket that does not refute it, or two consistent brackets
with different lists of indices. -/
def vadj (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (v w : Vertex) : Bool :=
  if v.1 then !w.1 && !refutes n kk gates v.2.1 w.2.2
  else !w.1 && (v.2.2.map Prod.fst != w.2.2.map Prod.fst) && consistent v.2.2 w.2.2

/-- The graph of a gate list from `n` inputs with output `o`, for depth `d` and weight `k`. -/
def graph (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o k : ℕ) : Graph :=
  Graph.ofAdj (vertices d n (min (n + 1) k) gates o) (vadj n (min (n + 1) k) gates)

/-- The clique size for depth `d`, `n` inputs and weight `k`. -/
def size (d n k : ℕ) : ℕ :=
  (classes d (min (n + 1) k)).length + 1

end ToClique

open ToClique

/-- **The graph of a circuit of weft one and a weight**, with its clique size. -/
def toClique {d : ℕ} (x : WeftCircuit 1 d × ℕ) : Graph × ℕ :=
  (graph d x.1.1.1 x.1.1.2.code.1 (x.1.1.2.outputs 0).toNat x.2, size d x.1.1.1 x.2)

namespace ToClique

/-! ### Basic facts -/

theorem mem_claimUniverse {n L : ℕ} {c : ℕ × Bool} : c ∈ claimUniverse n L ↔ c.1 < n + L := by
  obtain ⟨w, b⟩ := c
  cases b <;> simp [claimUniverse]

theorem mem_certs {d n : ℕ} {gates : List (Unbounded.Op × List ℕ)} {o : ℕ}
    {cl : List (ℕ × Bool)} :
    cl ∈ certs d n gates o ↔ cl.length ≤ 2 ^ d ∧ (∀ c ∈ cl, c.1 < n + gates.length) ∧
      WeftOne.claimsValid d n gates o cl = true := by
  simp only [certs, List.mem_filter, List.mem_listsUpTo, mem_claimUniverse, and_assoc]

theorem mem_pairs {n kk : ℕ} {p : ℕ × ℕ} : p ∈ pairs n kk ↔ p.1 < kk ∧ p.2 < n := by
  obtain ⟨j, s⟩ := p
  simp [pairs]

theorem mem_brackets {d n kk : ℕ} {P : List (ℕ × ℕ)} :
    P ∈ brackets d n kk ↔ P.length ≤ 2 ^ (d + 1) ∧ ∀ p ∈ P, p.1 < kk ∧ p.2 < n := by
  simp only [brackets, List.mem_listsUpTo, mem_pairs]

theorem mem_classes {d kk : ℕ} {C : List ℕ} :
    C ∈ classes d kk ↔ C.length ≤ 2 ^ (d + 1) ∧ ∀ j ∈ C, j < kk := by
  simp only [classes, List.mem_listsUpTo, List.mem_range]

theorem nodup_classes (d kk : ℕ) : (classes d kk).Nodup :=
  List.nodup_listsUpTo List.nodup_range _

theorem mem_vertices {d n kk : ℕ} {gates : List (Unbounded.Op × List ℕ)} {o : ℕ} {v : Vertex} :
    v ∈ vertices d n kk gates o ↔ (v.1 = true ∧ v.2.2 = [] ∧ v.2.1 ∈ certs d n gates o) ∨
      (v.1 = false ∧ v.2.1 = [] ∧ v.2.2 ∈ brackets d n kk) := by
  obtain ⟨b, cl, P⟩ := v
  simp only [vertices, List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro (⟨cl', h, rfl, rfl, rfl⟩ | ⟨P', h, rfl, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl, h⟩
    · exact Or.inr ⟨rfl, rfl, h⟩
  · rintro (⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩)
    · exact Or.inl ⟨cl, h, rfl, rfl, rfl⟩
    · exact Or.inr ⟨P, h, rfl, rfl, rfl⟩

theorem vadj_self (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (v : Vertex) :
    vadj n kk gates v v = false := by
  obtain ⟨b, cl, P⟩ := v
  cases b <;> simp [vadj]

theorem vadj_certs (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (cl cl' : List (ℕ × Bool))
    (P P' : List (ℕ × ℕ)) : vadj n kk gates (true, cl, P) (true, cl', P') = false := by
  simp [vadj]

theorem vadj_cert_bracket (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ))
    (cl : List (ℕ × Bool)) (P : List (ℕ × ℕ)) :
    (vadj n kk gates (true, cl, []) (false, [], P) ||
      vadj n kk gates (false, [], P) (true, cl, [])) = !refutes n kk gates cl P := by
  simp [vadj]

theorem vadj_brackets_iff (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ))
    (P Q : List (ℕ × ℕ)) :
    (vadj n kk gates (false, [], P) (false, [], Q) ||
      vadj n kk gates (false, [], Q) (false, [], P)) = true ↔
      P.map Prod.fst ≠ Q.map Prod.fst ∧ consistent P Q = true := by
  rw [consistent_comm] at *
  simp only [vadj, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
    Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  rw [consistent_comm Q P]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨h₁, h₂⟩
    · exact ⟨fun h => h₁ h.symm, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact Or.inl ⟨h₁, h₂⟩

/-! ### Refutation -/

theorem length_knowList (n kk : ℕ) (P : List (ℕ × ℕ)) : (knowList n kk P).length = n := by
  simp [knowList]

theorem getD_knowList {n kk : ℕ} (P : List (ℕ × ℕ)) {s : ℕ} (hs : s < n) :
    (knowList n kk P).getD s none = know kk P s := by
  simp [knowList, List.getD_eq_getElem?_getD, hs]

/-- A bracket whose partial input approximates `x` does not refute claims whose checks hold
on `x`. -/
theorem refutes_eq_false {n kk : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    (h : Program.IsCodeFrom Unbounded.signature n 0 gates) {x : List Bool} {P : List (ℕ × ℕ)}
    (hx : List.Forall₂ Approx (knowList n kk P) x) {cl : List (ℕ × Bool)}
    (hchecks : ∀ e ∈ cl.flatMap (WeftOne.claimChecks n gates),
      (evalCode Unbounded.interpretation false x gates).getD e.1 false = e.2) :
    refutes n kk gates cl P = false := by
  rw [refutes, List.any_eq_false]
  intro e he hbad
  have happ := approx_kleeneEval hx (length_eq_arity_of_isCodeFrom h) e.1
  rw [beq_iff_eq] at hbad
  rw [hbad] at happ
  have := happ _ rfl
  rw [hchecks e he] at this
  cases e.2 <;> simp at this

/-- The partial input of a bracket approximates `x` when every defined answer is right. -/
theorem forall₂_knowList {n kk : ℕ} {P : List (ℕ × ℕ)} {x : List Bool} (hx : x.length = n)
    (h : ∀ s < n, ∀ b, know kk P s = some b → b = x.getD s false) :
    List.Forall₂ Approx (knowList n kk P) x := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [knowList, hx], fun i h₁ h₂ => ?_⟩
  intro b hb
  simp only [knowList, List.get_eq_getElem, List.getElem_map, List.getElem_range] at hb
  have hi : i < n := by simpa [knowList] using h₁
  rw [h i hi b hb, List.get_eq_getElem, List.getD_eq_getElem _ _ (by omega)]

/-- A finite set of naturals is the image of a function increasing on `[0, T.card)`. -/
theorem exists_strictMonoOn_enum (T : Finset ℕ) :
    ∃ u : ℕ → ℕ, StrictMonoOn u (Set.Iio T.card) ∧
      ∀ s, s ∈ T ↔ ∃ i < T.card, u i = s := by
  classical
  let e := T.orderEmbOfFin rfl
  refine ⟨fun j => if h : j < T.card then e ⟨j, h⟩ else 0, ?_, fun s => ?_⟩
  · intro i hi j hj hij
    simp only [Set.mem_Iio] at hi hj
    simp only [hi, hj, dite_true]
    exact e.strictMono (Fin.mk_lt_mk.2 hij)
  · constructor
    · intro hs
      obtain ⟨i, hi⟩ := (Finset.range_orderEmbOfFin T rfl ▸ hs : s ∈ Set.range e)
      exact ⟨i.1, i.2, by simp only [i.2, dite_true, Fin.eta]; exact hi⟩
    · rintro ⟨i, hi, rfl⟩
      simp only [hi, dite_true]
      exact Finset.orderEmbOfFin_mem T rfl _

end ToClique

end Cslib.Complexity.WCS
