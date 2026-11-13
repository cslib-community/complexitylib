/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Certificate
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy
public import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.Clique.Bracket
public import CslibFrontier.Computability.Complexity.Problems.Clique.OfAdj
public import CslibFrontier.Foundations.Data.List.ListsUpTo
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

/-!
# The graph of a circuit of weft one

This file builds, from a circuit of weft at most `1` and depth at most `d` and a weight `k`, a
graph and a clique size (`WCS.toClique`), and shows that the graph has a clique of that size
exactly when the circuit has a satisfying input with `k` ones (`WCS.toClique_mem_Clique_iff`).
This is the core of the `W[1]`-hardness of `Clique` [Cygan et al., Chapter 13][CyganEtAl2015]
[DowneyFellows1999]. The graph, with one certificate vertex built on the certificates of
`Cslib.Circuits.Boolean.Unbounded.WeftOne` and bracket vertices, is this library's formulation.
Certifying an unselected input by the consecutive selected inputs around it follows the classical
gap technique of the standard proof [DowneyFellows1999] [FlumGrohe2006]. The locators have not been
checked against the books.

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
* `Cslib.Complexity.WCS.ToClique.mem_Clique_of_eval`,
  `Cslib.Complexity.WCS.ToClique.satisfiableWithWeight_of_mem_Clique`: the two directions.

## References

* [M. Cygan et al., *Parameterized Algorithms*, Chapter 13][CyganEtAl2015]
* [R. G. Downey, M. R. Fellows, *Parameterized Complexity*][DowneyFellows1999]
* [J. Flum, M. Grohe, *Parameterized Complexity Theory*][FlumGrohe2006]
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
def indexLists (d kk : ℕ) : List (List ℕ) :=
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

/-- A vertex: a certificate (`isCert = true`) with wire-value claims, or a bracket
(`isCert = false`) with `(index, position)` pairs. -/
structure Vertex where
  /-- `true` for a certificate vertex, `false` for a bracket vertex. -/
  isCert : Bool
  /-- The certificate's wire-value claims (empty for a bracket vertex). -/
  claims : List (ℕ × Bool)
  /-- The bracket's `(index, position)` pairs (empty for a certificate vertex). -/
  bracket : List (ℕ × ℕ)
  deriving DecidableEq

/-- The vertices: the certificates, then the brackets. -/
def vertices (d n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o : ℕ) : List Vertex :=
  (certs d n gates o).map (fun cl => ⟨true, cl, []⟩) ++
    (brackets d n kk).map (fun P => ⟨false, [], P⟩)

/-- Adjacency: a certificate and a bracket that does not refute it, or two consistent brackets
with different lists of indices. -/
def vadj (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ)) (v w : Vertex) : Bool :=
  if v.isCert then !w.isCert && !refutes n kk gates v.claims w.bracket
  else !w.isCert && (v.bracket.map Prod.fst != w.bracket.map Prod.fst) &&
    consistent v.bracket w.bracket

/-- The graph of a gate list from `n` inputs with output `o`, for depth `d` and weight `k`. -/
def graph (d n : ℕ) (gates : List (Unbounded.Op × List ℕ)) (o k : ℕ) : Graph :=
  Graph.ofAdj (vertices d n (min (n + 1) k) gates o) (vadj n (min (n + 1) k) gates)

/-- The clique size for depth `d`, `n` inputs and weight `k`. -/
def size (d n k : ℕ) : ℕ :=
  (indexLists d (min (n + 1) k)).length + 1

end ToClique

open ToClique

/-- **The graph of a circuit of weft one and a weight**, with its clique size. -/
def toClique {d : ℕ} (x : WCSInstance 1 d) : CliqueInstance :=
  ⟨graph d x.circuit.toCircuit.1 x.circuit.toCircuit.2.code.1
    (x.circuit.toCircuit.2.outputs 0).toNat x.weight, size d x.circuit.toCircuit.1 x.weight⟩

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

theorem mem_indexLists {d kk : ℕ} {C : List ℕ} :
    C ∈ indexLists d kk ↔ C.length ≤ 2 ^ (d + 1) ∧ ∀ j ∈ C, j < kk := by
  simp only [indexLists, List.mem_listsUpTo, List.mem_range]

theorem nodup_indexLists (d kk : ℕ) : (indexLists d kk).Nodup :=
  List.nodup_listsUpTo List.nodup_range _

theorem mem_vertices {d n kk : ℕ} {gates : List (Unbounded.Op × List ℕ)} {o : ℕ} {v : Vertex} :
    v ∈ vertices d n kk gates o ↔
      (v.isCert = true ∧ v.bracket = [] ∧ v.claims ∈ certs d n gates o) ∨
      (v.isCert = false ∧ v.claims = [] ∧ v.bracket ∈ brackets d n kk) := by
  obtain ⟨b, cl, P⟩ := v
  simp only [vertices, List.mem_append, List.mem_map, Vertex.mk.injEq]
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
    (P P' : List (ℕ × ℕ)) : vadj n kk gates ⟨true, cl, P⟩ ⟨true, cl', P'⟩ = false := by
  simp [vadj]

theorem vadj_cert_bracket (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ))
    (cl : List (ℕ × Bool)) (P : List (ℕ × ℕ)) :
    (vadj n kk gates ⟨true, cl, []⟩ ⟨false, [], P⟩ ||
      vadj n kk gates ⟨false, [], P⟩ ⟨true, cl, []⟩) = !refutes n kk gates cl P := by
  simp [vadj]

theorem vadj_brackets_iff (n kk : ℕ) (gates : List (Unbounded.Op × List ℕ))
    (P Q : List (ℕ × ℕ)) :
    (vadj n kk gates ⟨false, [], P⟩ ⟨false, [], Q⟩ ||
      vadj n kk gates ⟨false, [], Q⟩ ⟨false, [], P⟩) = true ↔
      P.map Prod.fst ≠ Q.map Prod.fst ∧ consistent P Q = true := by
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
private theorem exists_strictMonoOn_enum (T : Finset ℕ) :
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

/-! ### Selected inputs -/

/-- The input of length `n` whose ones are the positions `u 0, …, u (kk - 1)`. -/
private def selected (n kk : ℕ) (u : ℕ → ℕ) : BitString n :=
  fun i => decide (∃ j < kk, u j = i.1)

/-- Selecting `kk` increasing positions below `n` gives an input with `kk` ones. -/
private theorem weight_selected {n kk : ℕ} {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk))
    (hun : ∀ j < kk, u j < n) : BitString.weight (selected n kk u) = kk := by
  classical
  have himg : (Finset.univ.filter fun i : Fin n => selected n kk u i = true).map
      Fin.valEmbedding = (Finset.range kk).image u := by
    ext s
    simp only [selected, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_image, Finset.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨j, hj, hji⟩, rfl⟩
      exact ⟨j, hj, hji⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨u j, hun j hj⟩, ⟨j, hj, rfl⟩, rfl⟩
  have hinj : Set.InjOn u ↑(Finset.range kk) := by
    rw [Finset.coe_range]
    exact hu.injOn
  rw [BitString.weight, ← Finset.card_map Fin.valEmbedding, himg,
    Finset.card_image_of_injOn hinj, Finset.card_range]

/-- Every input with `k` ones is the selected input of the increasing enumeration of its ones. -/
private theorem exists_eq_selected {n k : ℕ} (x : BitString n) (hk : BitString.weight x = k) :
    ∃ u : ℕ → ℕ, StrictMonoOn u (Set.Iio k) ∧ (∀ j < k, u j < n) ∧ x = selected n k u := by
  classical
  set T : Finset ℕ := (Finset.univ.filter fun i : Fin n => x i = true).map Fin.valEmbedding
    with hTdef
  have hmemT : ∀ s, s ∈ T ↔ ∃ h : s < n, x ⟨s, h⟩ = true := by
    intro s
    simp only [hTdef, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.2, hi⟩
    · rintro ⟨h, hs⟩
      exact ⟨⟨s, h⟩, hs, rfl⟩
  have hTcard : T.card = k := by
    rw [hTdef, Finset.card_map, ← hk]
    rfl
  obtain ⟨u, hu, hTu⟩ := exists_strictMonoOn_enum T
  rw [hTcard] at hu hTu
  refine ⟨u, hu, fun j hj => ((hmemT (u j)).1 ((hTu (u j)).2 ⟨j, hj, rfl⟩)).1, ?_⟩
  funext i
  simp only [selected, ← hTu, hmemT, Fin.eta, exists_prop_of_true i.2]
  cases x i <;> rfl

/-- Reading position `s < n` of the selected input. -/
private theorem getD_ofFn_selected {n kk : ℕ} (u : ℕ → ℕ) {s : ℕ} (hs : s < n) :
    (List.ofFn (selected n kk u)).getD s false = decide (∃ j < kk, u j = s) := by
  rw [List.getD_eq_getElem _ _ (by rwa [List.length_ofFn]), List.getElem_ofFn]
  rfl

/-! ### Correctness -/

/-- The indices of the bracket `C.map (j, u j)` are `C`. -/
private theorem map_fst_map_pair (u : ℕ → ℕ) (C : List ℕ) :
    (C.map fun j => (j, u j)).map Prod.fst = C := by
  simp only [List.map_map]
  exact List.map_id C

/-- The correct brackets `C.map (j, u j)` of two different lists of indices below `kk` are
adjacent when `u` increases. -/
private theorem vadj_correct_brackets {n kk : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk)) {C C' : List ℕ} (hC : ∀ j ∈ C, j < kk)
    (hC' : ∀ j ∈ C', j < kk) (hCC : C ≠ C') :
    (vadj n kk gates ⟨false, [], C.map fun j => (j, u j)⟩
        ⟨false, [], C'.map fun j => (j, u j)⟩ ||
      vadj n kk gates ⟨false, [], C'.map fun j => (j, u j)⟩
        ⟨false, [], C.map fun j => (j, u j)⟩) = true := by
  rw [vadj_brackets_iff, map_fst_map_pair, map_fst_map_pair]
  refine ⟨hCC, consistent_iff.2 fun p hp q hq => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hq
  rw [pairOk_iff]
  exact ⟨(hu.injOn.eq_iff (hC i hi) (hC' j hj)).symm,
    (hu.lt_iff_lt (Set.mem_Iio.2 (hC i hi)) (Set.mem_Iio.2 (hC' j hj))).symm⟩

/-- **Completeness of the graph.** A satisfying input with `k` ones of a circuit of weft at most
`1` and depth at most `d` gives a clique of the size. -/
theorem mem_Clique_of_eval {d n : ℕ} (c : Circuit Unbounded.signature n 1) (hw : c.weft ≤ 1)
    (hd : c.depth ≤ d) {k : ℕ} (x : BitString n) (hk : BitString.weight x = k)
    (hx : c.eval Unbounded.interpretation x 0 = true) :
    (⟨graph d n c.code.1 (c.outputs 0).toNat k, size d n k⟩ : CliqueInstance) ∈ Clique := by
  classical
  have hkn : k ≤ n := hk ▸ BitString.weight_le_length x
  -- The ones of `x`, enumerated in increasing order.
  obtain ⟨u, hu, hun, rfl⟩ := exists_eq_selected x hk
  -- The correct certificate.
  obtain ⟨cl, hcllen, hclcorr, hclvalid⟩ := WeftOne.exists_claimsValid_circuit c hw hd _ hx
  have hcl : cl ∈ certs d n c.code.1 (c.outputs 0).toNat :=
    mem_certs.2 ⟨hcllen, fun e he => (hclcorr e he).1, hclvalid⟩
  -- The correct brackets, none of which refutes the certificate.
  let B : List ℕ → List (ℕ × ℕ) := fun C => C.map fun j => (j, u j)
  have hB : ∀ C ∈ indexLists d k, B C ∈ brackets d n k := by
    intro C hC
    obtain ⟨hlen, hlt⟩ := mem_indexLists.1 hC
    refine mem_brackets.2 ⟨by simpa [B] using hlen, fun p hp => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    exact ⟨hlt j hj, hun j (hlt j hj)⟩
  have hnoref : ∀ C ∈ indexLists d k, refutes n k c.code.1 cl (B C) = false := by
    intro C hC
    refine refutes_eq_false c.isCodeFrom_code (forall₂_knowList List.length_ofFn ?_)
      (WeftOne.checks_correct c.isCodeFrom_code List.length_ofFn fun e he => (hclcorr e he).2)
    intro s hs b hb
    have hPu : ∀ p ∈ B C, p.1 < k ∧ p.2 = u p.1 := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
      exact ⟨(mem_indexLists.1 hC).2 j hj, rfl⟩
    rw [know_sound hu hPu hb, getD_ofFn_selected u hs]
  -- The clique: the certificate and the correct bracket of every list of indices.
  rw [ToClique.graph, size, min_eq_right (by omega : k ≤ n + 1),
    Graph.mem_Clique_ofAdj_iff_entries (vadj_self _ _ _)]
  refine ⟨insert (⟨true, cl, []⟩ : Vertex)
      ((indexLists d k).toFinset.image fun C => (⟨false, [], B C⟩ : Vertex)),
    ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective,
      List.toFinset_card_of_nodup (nodup_indexLists d k)]
    intro C C' h
    simp only [Vertex.mk.injEq, true_and, B] at h
    rw [← map_fst_map_pair u C, ← map_fst_map_pair u C', h]
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hv
    rcases hv with rfl | ⟨C, hC, rfl⟩
    · exact mem_vertices.2 (Or.inl ⟨rfl, rfl, hcl⟩)
    · exact mem_vertices.2 (Or.inr ⟨rfl, rfl, hB C hC⟩)
  · intro v hv w hw hvw
    simp only [Finset.mem_insert, Finset.mem_image, List.mem_toFinset] at hv hw
    rcases hv with rfl | ⟨C, hC, rfl⟩ <;> rcases hw with rfl | ⟨C', hC', rfl⟩
    · exact absurd rfl hvw
    · rw [vadj_cert_bracket, hnoref C' hC']
      rfl
    · rw [Bool.or_comm, vadj_cert_bracket, hnoref C hC]
      rfl
    · exact vadj_correct_brackets hu (mem_indexLists.1 hC).2 (mem_indexLists.1 hC').2
        fun h => hvw (h ▸ rfl)

/-- The index list of a bracket vertex, and `none` for a certificate vertex. -/
private def label (v : Vertex) : Option (List ℕ) :=
  if v.isCert then none else some (v.bracket.map Prod.fst)

/-- Adjacent vertices have different labels: certificates are never adjacent to each other, and
adjacent brackets have different lists of indices. -/
private theorem label_ne_of_adj {n kk : ℕ} {gates : List (Unbounded.Op × List ℕ)} {v w : Vertex}
    (h : (vadj n kk gates v w || vadj n kk gates w v) = true) : label v ≠ label w := by
  obtain ⟨b, cl, P⟩ := v
  obtain ⟨b', cl', P'⟩ := w
  cases b <;> cases b'
  · simp only [vadj, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and,
      Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    simp only [label, Bool.false_eq_true, ↓reduceIte, ne_eq, Option.some.injEq]
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    exacts [h, Ne.symm h]
  · simp [label]
  · simp [label]
  · simp [vadj] at h

/-- **The shape of a clique of the size.** Labels are injective on a clique and take at most
`(indexLists d kk).length + 1` values, so a clique of that size contains a certificate and,
for every list of indices, a bracket with that list. -/
private theorem clique_shape {d n kk : ℕ} {gates : List (Unbounded.Op × List ℕ)} {o : ℕ}
    {T : Finset Vertex} (hTcard : T.card = (indexLists d kk).length + 1)
    (hTv : ∀ v ∈ T, v ∈ vertices d n kk gates o)
    (hTadj : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → (vadj n kk gates v w || vadj n kk gates w v) = true) :
    (∃ cl, (⟨true, cl, []⟩ : Vertex) ∈ T ∧ cl ∈ certs d n gates o) ∧
      ∀ C ∈ indexLists d kk, ∃ P, (⟨false, [], P⟩ : Vertex) ∈ T ∧ P.map Prod.fst = C := by
  classical
  have hinj : Set.InjOn label T := fun v hv w hw hvw => by
    by_contra hne
    exact label_ne_of_adj (hTadj v hv w hw hne) hvw
  have hsub : T.image label ⊆ insert none ((indexLists d kk).toFinset.image some) := by
    intro l hl
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hl
    rcases mem_vertices.1 (hTv v hv) with ⟨h1, -, -⟩ | ⟨h1, -, hP⟩
    · simp [label, h1]
    · obtain ⟨hlen, hlt⟩ := mem_brackets.1 hP
      simp only [label, h1, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert, reduceCtorEq,
        Finset.mem_image, List.mem_toFinset, Option.some.injEq, exists_eq_right, false_or]
      exact mem_indexLists.2 ⟨by simpa using hlen, fun j hj => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
        exact (hlt p hp).1⟩
  have himg : T.image label = insert none ((indexLists d kk).toFinset.image some) := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_image_of_injOn hinj, hTcard, Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective _),
      List.toFinset_card_of_nodup (nodup_indexLists d kk)]
  constructor
  · obtain ⟨⟨b, cl, P⟩, hv, hl⟩ := Finset.mem_image.1 (himg ▸ Finset.mem_insert_self none _)
    rcases mem_vertices.1 (hTv _ hv) with ⟨-, rfl, hcl⟩ | ⟨rfl, -, -⟩
    · cases b
      · simp [label] at hl
      · exact ⟨cl, hv, hcl⟩
    · simp [label] at hl
  · intro C hC
    have hl : some C ∈ T.image label := himg ▸ Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (List.mem_toFinset.2 hC))
    obtain ⟨⟨b, cl, P⟩, hv, hl⟩ := Finset.mem_image.1 hl
    rcases mem_vertices.1 (hTv _ hv) with ⟨rfl, -, -⟩ | ⟨rfl, rfl, -⟩
    · simp [label] at hl
    · exact ⟨P, hv, by simpa [label] using hl⟩

/-- Pairs of two different brackets of a clique are compatible. -/
private theorem pairOk_of_mem_clique {n kk : ℕ} {gates : List (Unbounded.Op × List ℕ)}
    {T : Finset Vertex}
    (hTadj : ∀ v ∈ T, ∀ w ∈ T, v ≠ w → (vadj n kk gates v w || vadj n kk gates w v) = true)
    {P Q : List (ℕ × ℕ)} (hP : (⟨false, [], P⟩ : Vertex) ∈ T)
    (hQ : (⟨false, [], Q⟩ : Vertex) ∈ T) (hPQ : P ≠ Q) :
    ∀ p ∈ P, ∀ q ∈ Q, pairOk p q = true := by
  have hadj := hTadj _ hP _ hQ fun h => hPQ (by simpa using h)
  rw [vadj_brackets_iff] at hadj
  exact consistent_iff.1 hadj.2

/-- **The certificate survives.** If a certificate is not refuted by a correct bracket of every
list of indices, for positions `u` increasing on `[0, kk)`, every check of a claim holds on the
selected input. A check is determined by at most `2 ^ d` inputs (`WeftOne.exists_determining`),
which the bracket of some list of at most `2 ^ (d + 1)` indices describes (`exists_cover`). -/
private theorem checks_of_not_refutes {d n kk : ℕ} (c : Circuit Unbounded.signature n 1)
    {u : ℕ → ℕ} (hu : StrictMonoOn u (Set.Iio kk)) {cl : List (ℕ × Bool)}
    (hcl : cl ∈ certs d n c.code.1 (c.outputs 0).toNat)
    (hcover : ∀ C ∈ indexLists d kk, ∃ P, (∀ p ∈ P, p.1 < kk ∧ p.2 = u p.1) ∧
      P.map Prod.fst = C ∧ refutes n kk c.code.1 cl P = false) :
    ∀ e ∈ cl.flatMap (WeftOne.claimChecks n c.code.1),
      (evalCode Unbounded.interpretation false (List.ofFn (selected n kk u)) c.code.1).getD
        e.1 false = e.2 := by
  intro e he
  have hvalid := (mem_certs.1 hcl).2.2
  simp only [WeftOne.claimsValid, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hvalid
  obtain ⟨S, hScard, hSlt, hSdet⟩ :=
    WeftOne.exists_determining c.isCodeFrom_code (hvalid.2 e he) le_rfl
  obtain ⟨J, hJcard, hJlt, hJknow⟩ := exists_cover hu S
  have hJlen : J.toList.length ≤ 2 ^ (d + 1) := by
    rw [Finset.length_toList, pow_succ, mul_comm]
    exact hJcard.trans (Nat.mul_le_mul_left 2 hScard)
  obtain ⟨P, hPu, hPC, hnr⟩ := hcover J.toList
    (mem_indexLists.2 ⟨hJlen, fun j hj => hJlt j (Finset.mem_toList.1 hj)⟩)
  -- The bracket `P` names every index of `J`, so it determines the check.
  have hJP : ∀ j ∈ J, (j, u j) ∈ P := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (hPC ▸ Finset.mem_toList.2 hj :
      j ∈ P.map Prod.fst)
    rw [← (hPu p hp).2]
    exact hp
  have hdet := hSdet (List.ofFn (selected n kk u)) (knowList n kk P) List.length_ofFn
      (length_knowList n kk P) fun s hs => by
    rw [getD_knowList P (hSlt s hs), getD_ofFn_selected u (hSlt s hs)]
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (hJknow P hJP s hs)
    rw [hb, know_sound hu hPu hb]
  -- Since `P` does not refute the check, it holds.
  rw [refutes, List.any_eq_false] at hnr
  have hbad := hnr e he
  rw [hdet] at hbad
  obtain ⟨w, b⟩ := e
  simp only at hbad ⊢
  generalize (evalCode Unbounded.interpretation false (List.ofFn (selected n kk u))
    c.code.1).getD w false = v at hbad ⊢
  cases v <;> cases b <;> simp at hbad ⊢

/-- **Soundness of the graph.** If the graph of a circuit has a clique of the size, the circuit
has a satisfying input with `k` ones. -/
theorem satisfiableWithWeight_of_mem_Clique {d n : ℕ} (c : Circuit Unbounded.signature n 1)
    {k : ℕ}
    (h : (⟨graph d n c.code.1 (c.outputs 0).toNat k, size d n k⟩ : CliqueInstance) ∈ Clique) :
    c.SatisfiableWithWeight Unbounded.interpretation k := by
  classical
  set kk := min (n + 1) k with hkk
  rw [ToClique.graph, size, ← hkk, Graph.mem_Clique_ofAdj_iff_entries (vadj_self _ _ _)] at h
  obtain ⟨T, hTcard, hTv, hTadj⟩ := h
  obtain ⟨⟨cl, hclT, hcl⟩, hcover⟩ := clique_shape hTcard hTv hTadj
  -- The selection, read off the brackets of the one-index lists.
  have hsing : ∀ j < kk, ∃ s, (⟨false, [], [(j, s)]⟩ : Vertex) ∈ T ∧ s < n := by
    intro j hj
    obtain ⟨P, hPT, hPC⟩ := hcover [j]
      (mem_indexLists.2 ⟨by simp [Nat.one_le_two_pow], by simpa using hj⟩)
    obtain ⟨⟨j', s⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.1 hPC
    rcases mem_vertices.1 (hTv _ hPT) with ⟨h1, -, -⟩ | ⟨-, -, hP⟩
    · simp at h1
    · exact ⟨s, hPT, ((mem_brackets.1 hP).2 _ (List.mem_singleton_self _)).2⟩
  choose! u hu hun using hsing
  -- Every bracket of the clique is correct for `u`, and `u` increases.
  have hpairs : ∀ P, (⟨false, [], P⟩ : Vertex) ∈ T → ∀ p ∈ P, p.1 < kk ∧ p.2 = u p.1 := by
    intro P hPT p hp
    have hp1 : p.1 < kk := by
      rcases mem_vertices.1 (hTv _ hPT) with ⟨h1, -, -⟩ | ⟨-, -, hP⟩
      · simp at h1
      · exact ((mem_brackets.1 hP).2 p hp).1
    refine ⟨hp1, ?_⟩
    by_cases hPeq : P = [(p.1, u p.1)]
    · rw [hPeq, List.mem_singleton] at hp
      exact congrArg Prod.snd hp
    · have hok := pairOk_of_mem_clique hTadj hPT (hu p.1 hp1) hPeq p hp _
        (List.mem_singleton_self _)
      exact ((pairOk_iff _ _).1 hok).1.1 rfl
  have hmono : StrictMonoOn u (Set.Iio kk) := by
    intro i hi j hj hij
    have hok := pairOk_of_mem_clique hTadj (hu i hi) (hu j hj)
      (by simp only [ne_eq, List.cons.injEq, Prod.mk.injEq, and_true]; omega) _
      (List.mem_singleton_self _) _ (List.mem_singleton_self _)
    exact ((pairOk_iff _ _).1 hok).2.1 hij
  have hkk' : kk = k := by
    have := (weight_selected hmono hun).symm.trans_le (BitString.weight_le_length _)
    omega
  -- The selected input.
  refine ⟨selected n kk u, hkk' ▸ weight_selected hmono hun, ?_⟩
  refine WeftOne.eval_of_claimsValid_circuit c (mem_certs.1 hcl).2.2 _
    (checks_of_not_refutes c hmono hcl fun C hC => ?_)
  obtain ⟨P, hPT, hPC⟩ := hcover C hC
  have hadj := hTadj _ hclT _ hPT (by simp)
  rw [vadj_cert_bracket] at hadj
  exact ⟨P, hpairs P hPT, hPC, by simpa using hadj⟩

end ToClique

/-- **Correctness of the graph construction.** The graph of a circuit of weft at most `1` and
depth at most `d` has a clique of the size exactly when the circuit has a satisfying input with
`k` ones. -/
theorem toClique_mem_Clique_iff {d : ℕ} (x : WCSInstance 1 d) :
    toClique x ∈ Clique ↔ x ∈ WCS 1 d := by
  obtain ⟨⟨⟨n, c⟩, hw, hd⟩, k⟩ := x
  rw [mem_WCS]
  exact ⟨satisfiableWithWeight_of_mem_Clique c,
    fun ⟨y, hy, hc⟩ => mem_Clique_of_eval c hw hd y hy hc⟩

end Cslib.Complexity.WCS
