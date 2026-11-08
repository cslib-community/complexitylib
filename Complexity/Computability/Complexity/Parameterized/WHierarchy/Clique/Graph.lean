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
This is the core of the `W[1]`-hardness of `Clique` [Cygan et al., Chapter 13][CyganEtAl2015]
[DowneyFellows1999]. The certificate-and-bracket graph is an original construction of this library,
built on the certificates of `Cslib.Circuits.Boolean.Unbounded.WeftOne`; the cited sources prove the
theorem through their own reduction. The chapter locator has not been checked against the book.

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

/-! ### Correctness -/

/-- **Completeness of the graph.** A satisfying input with `k` ones of a circuit of weft at most
`1` and depth at most `d` gives a clique of the size. -/
theorem mem_Clique_of_eval {d n : ℕ} (c : Circuit Unbounded.signature n 1) (hw : c.weft ≤ 1)
    (hd : c.depth ≤ d) {k : ℕ} (x : BitString n) (hk : BitString.weight x = k)
    (hx : c.eval Unbounded.interpretation x 0 = true) :
    (graph d n c.code.1 (c.outputs 0).toNat k, size d n k) ∈ Clique := by
  classical
  set T : Finset ℕ := (Finset.univ.filter fun i : Fin n => x i = true).map Fin.valEmbedding
    with hTdef
  have hTcard : T.card = k := by
    rw [hTdef, Finset.card_map, ← hk]
    rfl
  have hkn : k ≤ n := hk ▸ BitString.weight_le_length x
  have hkk : min (n + 1) k = k := min_eq_right (by omega)
  have hmemT : ∀ s, s ∈ T ↔ ∃ h : s < n, x ⟨s, h⟩ = true := by
    intro s
    simp only [hTdef, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.2, hi⟩
    · rintro ⟨h, hs⟩
      exact ⟨⟨s, h⟩, hs, rfl⟩
  obtain ⟨u, hu, hTu⟩ := exists_strictMonoOn_enum T
  rw [hTcard] at hu hTu
  have hun : ∀ i < k, u i < n := fun i hi => ((hmemT (u i)).1 ((hTu (u i)).2 ⟨i, hi, rfl⟩)).1
  have hlt : ∀ {i j}, i < k → j < k → (u i < u j ↔ i < j) := fun hi hj =>
    hu.lt_iff_lt (Set.mem_Iio.2 hi) (Set.mem_Iio.2 hj)
  have hinj : ∀ {i j}, i < k → j < k → (u i = u j ↔ i = j) := fun hi hj =>
    ⟨fun h => hu.injOn (Set.mem_Iio.2 hi) (Set.mem_Iio.2 hj) h, fun h => h ▸ rfl⟩
  -- The correct certificate.
  obtain ⟨cl, hcllen, hclcorr, hclvalid⟩ := WeftOne.exists_claimsValid_circuit c hw hd x hx
  have hcl : cl ∈ certs d n c.code.1 (c.outputs 0).toNat :=
    mem_certs.2 ⟨hcllen, fun e he => (hclcorr e he).1, hclvalid⟩
  -- The correct brackets.
  let B : List ℕ → List (ℕ × ℕ) := fun C => C.map fun j => (j, u j)
  have hBfst : ∀ C, (B C).map Prod.fst = C := fun C => by
    simp only [B, List.map_map]
    exact List.map_id C
  have hB : ∀ C ∈ classes d k, B C ∈ brackets d n k := by
    intro C hC
    obtain ⟨hlen, hlt'⟩ := mem_classes.1 hC
    refine mem_brackets.2 ⟨by simpa [B] using hlen, fun p hp => ?_⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    exact ⟨hlt' j hj, hun j (hlt' j hj)⟩
  have hxlen : (List.ofFn x).length = n := List.length_ofFn
  have hnoref : ∀ C ∈ classes d k, refutes n k c.code.1 cl (B C) = false := by
    intro C hC
    have hCk := (mem_classes.1 hC).2
    refine refutes_eq_false c.isCodeFrom_code (forall₂_knowList hxlen ?_)
      (WeftOne.checks_correct c.isCodeFrom_code hxlen fun e he => (hclcorr e he).2)
    intro s hs b hb
    have hPu : ∀ p ∈ B C, p.1 < k ∧ p.2 = u p.1 := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
      exact ⟨hCk j hj, rfl⟩
    rw [know_sound hu hPu hb, List.getD_eq_getElem _ _ (by omega), List.getElem_ofFn]
    by_cases hxs : x ⟨s, hs⟩ = true
    · rw [hxs, decide_eq_true_iff]
      exact (hTu s).1 ((hmemT s).2 ⟨hs, hxs⟩)
    · rw [Bool.not_eq_true] at hxs
      rw [hxs, decide_eq_false_iff_not]
      intro h
      obtain ⟨_, h'⟩ := (hmemT s).1 ((hTu s).2 h)
      rw [hxs] at h'
      exact Bool.false_ne_true h'
  -- The clique.
  rw [graph, size, hkk, Graph.mem_Clique_ofAdj_iff_entries (vadj_self _ _ _)]
  refine ⟨insert (true, cl, []) ((classes d k).toFinset.image fun C => (false, [], B C)),
    ?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective,
      List.toFinset_card_of_nodup (nodup_classes d k)]
    intro C C' h
    simp only [Prod.mk.injEq, true_and] at h
    rw [← hBfst C, ← hBfst C', h]
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
    · have hCC : C ≠ C' := fun h => hvw (h ▸ rfl)
      rw [vadj_brackets_iff, hBfst, hBfst]
      refine ⟨hCC, consistent_iff.2 fun p hp q hq => ?_⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hq
      have hik := (mem_classes.1 hC).2 i hi
      have hjk := (mem_classes.1 hC').2 j hj
      rw [pairOk_iff]
      exact ⟨(hinj hik hjk).symm, (hlt hik hjk).symm⟩

/-- **Soundness of the graph.** If the graph of a circuit has a clique of the size, the circuit
has a satisfying input with `k` ones. -/
theorem satisfiableWithWeight_of_mem_Clique {d n : ℕ} (c : Circuit Unbounded.signature n 1)
    {k : ℕ} (h : (graph d n c.code.1 (c.outputs 0).toNat k, size d n k) ∈ Clique) :
    c.SatisfiableWithWeight Unbounded.interpretation k := by
  classical
  set kk := min (n + 1) k with hkk
  rw [graph, size, ← hkk, Graph.mem_Clique_ofAdj_iff_entries (vadj_self _ _ _)] at h
  obtain ⟨T, hTcard, hTv, hTadj⟩ := h
  -- The vertices of the clique.
  have hTv' := fun v hv => mem_vertices.1 (hTv v hv)
  set Cs := T.filter fun v => v.1 = true with hCs
  set Bs := T.filter fun v => ¬ v.1 = true with hBs
  have hCs1 : Cs.card ≤ 1 := by
    refine Finset.card_le_one.2 fun v hv w hw => ?_
    by_contra hvw
    rw [hCs, Finset.mem_filter] at hv hw
    obtain ⟨b, cl, P⟩ := v
    obtain ⟨b', cl', P'⟩ := w
    simp only at hv hw
    obtain ⟨hv, rfl⟩ := hv
    obtain ⟨hw, rfl⟩ := hw
    have := hTadj _ hv _ hw hvw
    simp [vadj_certs] at this
  have hBsv : ∀ v ∈ Bs, v.1 = false ∧ v.2.1 = [] ∧ v.2.2 ∈ brackets d n kk := by
    intro v hv
    rw [hBs, Finset.mem_filter] at hv
    rcases hTv' v hv.1 with h | h
    · exact absurd h.1 hv.2
    · exact h
  have hBinj : Set.InjOn (fun v : Vertex => v.2.2.map Prod.fst) Bs := by
    intro v hv w hw hvw
    by_contra hne
    obtain ⟨hv1, hv2, -⟩ := hBsv v hv
    obtain ⟨hw1, hw2, -⟩ := hBsv w hw
    obtain ⟨b, cl, P⟩ := v
    obtain ⟨b', cl', P'⟩ := w
    simp only at hv1 hv2 hw1 hw2 hvw
    subst hv1 hv2 hw1 hw2
    have := hTadj _ (Finset.mem_filter.1 hv).1 _ (Finset.mem_filter.1 hw).1 hne
    rw [vadj_brackets_iff] at this
    exact this.1 hvw
  have hBsub : Bs.image (fun v : Vertex => v.2.2.map Prod.fst) ⊆ (classes d kk).toFinset := by
    intro C hC
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hC
    obtain ⟨-, -, hP⟩ := hBsv v hv
    obtain ⟨hlen, hlt⟩ := mem_brackets.1 hP
    refine List.mem_toFinset.2 (mem_classes.2 ⟨by simpa using hlen, fun j hj => ?_⟩)
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj
    exact (hlt p hp).1
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) fun v => v.1 = true
  rw [← hCs, ← hBs, hTcard] at hsplit
  have hBle : Bs.card ≤ (classes d kk).length := by
    rw [← Finset.card_image_of_injOn hBinj, ← List.toFinset_card_of_nodup (nodup_classes d kk)]
    exact Finset.card_le_card hBsub
  have hCs1' : Cs.card = 1 := by omega
  have hBimg : Bs.image (fun v : Vertex => v.2.2.map Prod.fst) = (classes d kk).toFinset := by
    refine Finset.eq_of_subset_of_card_le hBsub ?_
    rw [Finset.card_image_of_injOn hBinj, List.toFinset_card_of_nodup (nodup_classes d kk)]
    omega
  have hcover : ∀ C ∈ classes d kk, ∃ P, (false, [], P) ∈ T ∧ P ∈ brackets d n kk ∧
      P.map Prod.fst = C := by
    intro C hC
    rw [← List.mem_toFinset, ← hBimg] at hC
    obtain ⟨v, hv, hvC⟩ := Finset.mem_image.1 hC
    obtain ⟨hv1, hv2, hP⟩ := hBsv v hv
    obtain ⟨b, cl, P⟩ := v
    simp only at hv1 hv2 hP hvC
    subst hv1 hv2
    exact ⟨P, (Finset.mem_filter.1 hv).1, hP, hvC⟩
  -- The certificate.
  obtain ⟨v₀, hv₀⟩ := Finset.card_eq_one.1 hCs1'
  have hv₀Cs : v₀ ∈ Cs := hv₀ ▸ Finset.mem_singleton_self v₀
  rw [hCs, Finset.mem_filter] at hv₀Cs
  obtain ⟨hv₀T, hv₀1⟩ := hv₀Cs
  obtain ⟨b₀, cl, P₀⟩ := v₀
  simp only at hv₀1
  subst hv₀1
  have hcl : P₀ = [] ∧ cl ∈ certs d n c.code.1 (c.outputs 0).toNat := by
    rcases hTv' _ hv₀T with h | h
    · exact ⟨h.2.1, h.2.2⟩
    · exact absurd h.1 (by simp)
  obtain ⟨rfl, hcl⟩ := hcl
  have hmemBs : ∀ P, ((false, [], P) : Vertex) ∈ T → ((false, [], P) : Vertex) ∈ Bs :=
    fun P hP => by
      rw [hBs, Finset.mem_filter]
      exact ⟨hP, Bool.false_ne_true⟩
  -- The selection, read off the brackets of the one-index lists.
  have hsing : ∀ j < kk, ∃ s, ((false, [], [(j, s)]) : Vertex) ∈ T ∧ s < n := by
    intro j hj
    obtain ⟨P, hPT, hP, hPC⟩ := hcover [j]
      (mem_classes.2 ⟨by simp [Nat.one_le_two_pow], by simpa using hj⟩)
    obtain ⟨⟨j', s⟩, rfl, hp⟩ := List.map_eq_singleton_iff.1 hPC
    simp only at hp
    subst hp
    exact ⟨s, hPT, ((mem_brackets.1 hP).2 (j', s) (List.mem_singleton_self _)).2⟩
  choose! u hu hun using hsing
  have hpairs : ∀ P, ((false, [], P) : Vertex) ∈ T → ∀ p ∈ P, p.1 < kk ∧ p.2 = u p.1 := by
    intro P hPT p hp
    have hp1 := ((mem_brackets.1 (hBsv _ (hmemBs P hPT)).2.2).2 p hp).1
    refine ⟨hp1, ?_⟩
    by_cases hPeq : P.map Prod.fst = [p.1]
    · have heq := hBinj (hmemBs P hPT) (hmemBs _ (hu p.1 hp1)) (by simpa using hPeq)
      simp only [Prod.mk.injEq, true_and] at heq
      rw [heq, List.mem_singleton] at hp
      exact congrArg Prod.snd hp
    · have hne : ((false, [], P) : Vertex) ≠ (false, [], [(p.1, u p.1)]) := by
        intro h
        simp only [Prod.mk.injEq, true_and] at h
        subst h
        simp at hPeq
      have hadj := hTadj _ hPT _ (hu p.1 hp1) hne
      rw [vadj_brackets_iff] at hadj
      have hok := consistent_iff.1 hadj.2 p hp (p.1, u p.1) (List.mem_singleton_self _)
      rw [pairOk_iff] at hok
      exact hok.1.1 rfl
  have hmono : StrictMonoOn u (Set.Iio kk) := by
    intro i hi j hj hij
    have hne : ((false, [], [(i, u i)]) : Vertex) ≠ (false, [], [(j, u j)]) := by
      intro h
      simp only [Prod.mk.injEq, List.cons.injEq, and_true, true_and] at h
      omega
    have hadj := hTadj _ (hu i hi) _ (hu j hj) hne
    rw [vadj_brackets_iff] at hadj
    have hok := consistent_iff.1 hadj.2 (i, u i) (List.mem_singleton_self _) (j, u j)
      (List.mem_singleton_self _)
    rw [pairOk_iff] at hok
    exact hok.2.1 hij
  have hinj : Set.InjOn u ↑(Finset.range kk) := by
    rw [Finset.coe_range]
    exact hmono.injOn
  have hkkn : kk ≤ n := by
    have := Finset.card_le_card_of_injOn u (s := Finset.range kk) (t := Finset.range n)
      (by
        intro j hj
        simpa using hun j (by simpa using hj)) hinj
    simpa using this
  have hkk' : kk = k := by omega
  -- The selected input.
  let x : BitString n := fun i => decide (∃ j < kk, u j = i.1)
  refine ⟨x, ?_, ?_⟩
  · have himg : (Finset.univ.filter fun i : Fin n => decide (∃ j < kk, u j = i.1) = true).map
        Fin.valEmbedding = (Finset.range kk).image u := by
      ext s
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_image, Finset.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨i, ⟨j, hj, hji⟩, rfl⟩
        exact ⟨j, hj, hji⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨u j, hun j hj⟩, ⟨j, hj, rfl⟩, rfl⟩
    rw [BitString.weight, ← Finset.card_map Fin.valEmbedding, himg,
      Finset.card_image_of_injOn hinj, Finset.card_range, hkk']
  · have hvalid := (mem_certs.1 hcl).2.2
    have hvalid' := hvalid
    simp only [WeftOne.claimsValid, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at hvalid'
    refine WeftOne.eval_of_claimsValid_circuit c hvalid _ fun e he => ?_
    obtain ⟨S, hScard, hSlt, hSdet⟩ :=
      WeftOne.exists_determining c.isCodeFrom_code (hvalid'.2 e he) le_rfl
    obtain ⟨J, hJcard, hJlt, hJknow⟩ := exists_cover hmono S
    have hJlen : J.toList.length ≤ 2 ^ (d + 1) := by
      rw [Finset.length_toList, pow_succ, mul_comm]
      exact hJcard.trans (Nat.mul_le_mul_left 2 hScard)
    obtain ⟨P, hPT, -, hPC⟩ := hcover J.toList
      (mem_classes.2 ⟨hJlen, fun j hj => hJlt j (Finset.mem_toList.1 hj)⟩)
    have hPu := hpairs P hPT
    have hJP : ∀ j ∈ J, (j, u j) ∈ P := by
      intro j hj
      have hjP : j ∈ P.map Prod.fst := by
        rw [hPC]
        exact Finset.mem_toList.2 hj
      obtain ⟨p, hp, hpj⟩ := List.mem_map.1 hjP
      subst hpj
      rw [← (hPu p hp).2]
      exact hp
    have hdet := hSdet (List.ofFn x) (knowList n kk P) List.length_ofFn (length_knowList n kk P) (by
      intro s hs
      rw [getD_knowList P (hSlt s hs)]
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (hJknow P hJP s hs)
      rw [hb, know_sound hmono hPu hb,
        List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hSlt s hs), List.getElem_ofFn])
    have hne : ((true, cl, []) : Vertex) ≠ (false, [], P) := by simp
    have hadj := hTadj _ hv₀T _ hPT hne
    rw [vadj_cert_bracket] at hadj
    have hnr : refutes n kk c.code.1 cl P = false := by simpa using hadj
    rw [refutes, List.any_eq_false] at hnr
    have hbad := hnr e (List.mem_flatMap.2 (List.mem_flatMap.1 he))
    rw [hdet] at hbad
    obtain ⟨w, b⟩ := e
    simp only at hbad ⊢
    generalize (evalCode Unbounded.interpretation false (List.ofFn x) c.code.1).getD w false = v
      at hbad ⊢
    cases v <;> cases b <;> simp at hbad ⊢

end ToClique

/-- **Correctness of the graph construction.** The graph of a circuit of weft at most `1` and
depth at most `d` has a clique of the size exactly when the circuit has a satisfying input with
`k` ones. -/
theorem toClique_mem_Clique_iff {d : ℕ} (x : WeftCircuit 1 d × ℕ) :
    toClique x ∈ Clique ↔ x ∈ WCS 1 d := by
  obtain ⟨⟨⟨n, c⟩, hw, hd⟩, k⟩ := x
  rw [mem_WCS]
  exact ⟨satisfiableWithWeight_of_mem_Clique c,
    fun ⟨y, hy, hc⟩ => mem_Clique_of_eval c hw hd y hy hc⟩

end Cslib.Complexity.WCS
