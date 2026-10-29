/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized.Kernelization
public import Complexity.Computability.Complexity.Problems.VertexCover
import Complexity.Computability.Complexity.FineGrained.ExhaustiveSearch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Nat.Bitwise
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-!
# Fixed-parameter tractability of vertex cover

A bounded search tree of depth `k` decides whether a graph has a vertex cover of size `k`
[DowneyFellows1999, Section 3.1] [FlumGrohe2006, Section 1.2] [CyganEtAl2015, Section 3.1]: every
edge `{u, v}` between declared vertices must have `u` or `v` in any cover, so branching on the two
endpoints of the first uncovered edge (`Cslib.Complexity.VertexCover.branchStep`) explores at most
`2 ^ k` root-to-leaf paths of length `k`.

A path of length `m` is numbered by `i < 2 ^ m`, whose `j`-th binary digit chooses the endpoint at
step `j` (`Cslib.Complexity.VertexCover.foldBranch`). To keep the path length bounded by the size
of the graph even when the binary target `k` exceeds the number `n` of distinct declared vertices,
the search caps the depth at `min n k` (`Cslib.Complexity.VertexCover.cap`) and checks `k ≤ n`
separately (`Cslib.Complexity.mem_VertexCover_iff_exists_card_le`). Iterating over the
`2 ^ min n k` paths (`Cslib.Complexity.DecidableInExpTime.of_exhaustiveSearch`) runs within time
`2 ^ k` times a polynomial in the length of the encoded instance
(`Cslib.Complexity.VertexCover_decidableInExpTime_one`), so `VertexCover` is fixed-parameter
tractable in the target size `k` (`Cslib.Complexity.VertexCover_mem_FPT`).

## Main definitions

* `Cslib.Complexity.VertexCover.branchStep`, `Cslib.Complexity.VertexCover.foldBranch`: a step and
  a root-to-leaf path of the bounded search tree.
* `Cslib.Complexity.VertexCover.search`: bounded-search-tree decision procedure for `VertexCover`.

## Main results

* `Cslib.Complexity.VertexCover.exists_lt_two_pow_isCover_foldBranch`: if a graph has a vertex
  cover of at most `m` vertices, one of the `2 ^ m` paths of length `m` finds a cover.
* `Cslib.Complexity.VertexCover.search_eq_true_iff`: `VertexCover.search` decides `VertexCover`.
* `Cslib.Complexity.VertexCover_decidableInExpTime_one`: `VertexCover` is decidable within time
  `2 ^ k` times a polynomial in the length of the encoded instance.
* `Cslib.Complexity.VertexCover_mem_FPT`, `Cslib.Complexity.VertexCover_hasKernel`: `VertexCover`
  is fixed-parameter tractable and has a kernel in the target size `k`.

## References

* [R. G. Downey, M. R. Fellows, *Parameterized Complexity*][DowneyFellows1999]
* [J. Flum, M. Grohe, *Parameterized Complexity Theory*][FlumGrohe2006]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

namespace VertexCover

/-! ### Bounded search tree -/

/-- One step in the bounded search tree for vertex cover: if `C` is already a cover, keep `C`;
otherwise pick the first uncovered edge `(u, v)` and add `u` (when `b = false`) or `v` (when
`b = true`) to `C`. -/
def branchStep (G : Graph) (C : List ℕ) (b : Bool) : List ℕ :=
  if isCover G C then C
  else
    let e := (uncoveredEdges G C).headD (0, 0)
    (if b then e.2 else e.1) :: C

/-- Follow the bounded search tree along a list of branching bits `bs`. -/
def foldBranch (G : Graph) (bs : List Bool) : List ℕ :=
  bs.foldl (branchStep G) []

private theorem foldBranch_append_singleton (G : Graph) (bs : List Bool) (b : Bool) :
    foldBranch G (bs ++ [b]) = branchStep G (foldBranch G bs) b := by
  simp [foldBranch]

private theorem headD_mem_uncoveredEdges {G : Graph} {C : List ℕ}
    (h : isCover G C = false) :
    (uncoveredEdges G C).headD (0, 0) ∈ uncoveredEdges G C := by
  rw [isCover] at h
  cases hle : uncoveredEdges G C with
  | nil => simp [hle] at h
  | cons e es => simp

private theorem mem_of_mem_branchStep {G : Graph} {C : List ℕ} {b : Bool} (hC : ∀ v ∈ C, v ∈ G.1) :
    ∀ v ∈ branchStep G C b, v ∈ G.1 := by
  unfold branchStep
  cases h : isCover G C
  · dsimp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨_, he₁, he₂, _, _, _⟩ := mem_uncoveredEdges_iff.mp (headD_mem_uncoveredEdges h)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · split_ifs <;> assumption
    · exact hC v hv
  · simpa using hC

private theorem length_branchStep_le (G : Graph) (C : List ℕ) (b : Bool) :
    (branchStep G C b).length ≤ C.length + 1 := by
  unfold branchStep
  split_ifs <;> simp

/-- Every vertex added along a search-tree path is a declared vertex of `G`. -/
private theorem mem_of_mem_foldBranch (G : Graph) (bs : List Bool) :
    ∀ v ∈ foldBranch G bs, v ∈ G.1 := by
  induction bs using List.reverseRecOn with
  | nil => simp [foldBranch]
  | append_singleton bs b ih =>
    rw [foldBranch, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact mem_of_mem_branchStep ih

/-- A search-tree path of length `|bs|` picks at most `|bs|` vertices. -/
private theorem length_foldBranch_le (G : Graph) (bs : List Bool) :
    (foldBranch G bs).length ≤ bs.length := by
  induction bs using List.reverseRecOn with
  | nil => simp [foldBranch]
  | append_singleton bs b ih =>
    rw [foldBranch, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton]
    exact (length_branchStep_le G (foldBranch G bs) b).trans (Nat.add_le_add_right ih 1)

/-- Along any vertex cover `S`, at each depth `m` some path of length `m` either has already found
a cover or has accumulated `m` distinct vertices of `S`. -/
private theorem exists_foldBranch_subset (G : Graph) {S : Finset ℕ}
    (hS : ∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) (m : ℕ) :
    ∃ bs : List Bool, bs.length = m ∧ (∀ v ∈ foldBranch G bs, v ∈ S) ∧
      (foldBranch G bs).Nodup ∧
      (isCover G (foldBranch G bs) = true ∨ (foldBranch G bs).length = m) := by
  induction m with
  | zero => exact ⟨[], rfl, by simp [foldBranch], by simp [foldBranch], Or.inr rfl⟩
  | succ m ih =>
    obtain ⟨bs, hbs, hsub, hnodup, hcov⟩ := ih
    set C := foldBranch G bs
    cases h : isCover G C
    · have hlen : C.length = m := hcov.resolve_left (by simp [h])
      set e := (uncoveredEdges G C).headD (0, 0)
      obtain ⟨he, he₁, he₂, hne, he₁C, he₂C⟩ :=
        mem_uncoveredEdges_iff.mp (headD_mem_uncoveredEdges h)
      have hadj : G.toSimpleGraph.Adj e.1 e.2 := ⟨hne, Or.inl he⟩
      have heS : e.1 ∈ S ∨ e.2 ∈ S := hS e.1 he₁ e.2 he₂ hadj
      let b : Bool := decide (e.1 ∉ S)
      have hwS : (if b then e.2 else e.1) ∈ S := by
        by_cases h₁ : e.1 ∈ S
        · simp [b, h₁]
        · simp [b, h₁, heS.resolve_left h₁]
      have hwC : (if b then e.2 else e.1) ∉ C := by
        split_ifs <;> assumption
      have hstep : foldBranch G (bs ++ [b]) = (if b then e.2 else e.1) :: C := by
        rw [foldBranch_append_singleton]
        simp [C, branchStep, h, e]
      refine ⟨bs ++ [b], by simp [hbs], ?_, ?_, Or.inr ?_⟩
      · rw [hstep]
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hwS
        · exact hsub v hv
      · rw [hstep]
        exact List.nodup_cons.mpr ⟨hwC, hnodup⟩
      · rw [hstep, List.length_cons, hlen]
    · have hstep : foldBranch G (bs ++ [false]) = C := by
        rw [foldBranch_append_singleton]
        simp [C, branchStep, h]
      refine ⟨bs ++ [false], by simp [hbs], ?_, ?_, Or.inl ?_⟩
      · rwa [hstep]
      · rwa [hstep]
      · rwa [hstep]

/-- If `G` has a vertex cover of at most `m` vertices, some branching word `bs` of length `m`
produces a cover. -/
private theorem exists_isCover_foldBranch {G : Graph} {S : Finset ℕ}
    (hS : ∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) {m : ℕ}
    (hm : S.card ≤ m) :
    ∃ bs : List Bool, bs.length = m ∧ isCover G (foldBranch G bs) = true := by
  obtain ⟨bs, hbs, hsub, hnodup, hcov | hlen⟩ := exists_foldBranch_subset G hS m
  · exact ⟨bs, hbs, hcov⟩
  · refine ⟨bs, hbs, isCover_eq_true_iff.mpr fun u hu v hv hadj => ?_⟩
    have hsub' : (foldBranch G bs).toFinset ⊆ S :=
      fun w hw => hsub w (List.mem_toFinset.mp hw)
    have hcard : S.card ≤ (foldBranch G bs).toFinset.card := by
      rw [List.toFinset_card_of_nodup hnodup, hlen]
      exact hm
    have heq := (Finset.eq_of_subset_of_card_le hsub' hcard).symm
    rcases hS u hu v hv hadj with huS | hvS
    · exact Or.inl (List.mem_toFinset.mp (heq ▸ huS))
    · exact Or.inr (List.mem_toFinset.mp (heq ▸ hvS))

/-- **Completeness of the bounded search tree.** A graph `G` has a vertex cover of at most `m`
declared vertices if and only if some `i < 2 ^ m` leads to a cover along the path of length `m`
given by the binary digits of `i`. -/
theorem exists_lt_two_pow_isCover_foldBranch (G : Graph) (m : ℕ) :
    (∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.1) ∧
      (∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → u ∈ S ∨ v ∈ S) ∧ S.card ≤ m) ↔
      ∃ i < 2 ^ m, isCover G (foldBranch G ((List.range m).map i.testBit)) = true := by
  constructor
  · rintro ⟨S, _, hS, hm⟩
    obtain ⟨bs, hbs, hcov⟩ := exists_isCover_foldBranch hS hm
    refine ⟨(BitVec.ofBoolListLE bs).toNat, (BitVec.isLt _).trans_eq (by simp [hbs]), ?_⟩
    have hmap : (List.range m).map (BitVec.ofBoolListLE bs).toNat.testBit = bs := by
      apply List.ext_getElem (by simp [hbs])
      intro j hj₁ hj₂
      simp only [List.getElem_map, List.getElem_range, BitVec.testBit_toNat,
        BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj₂, Option.getD_some]
    rwa [hmap]
  · rintro ⟨i, _, hcov⟩
    set C := foldBranch G ((List.range m).map i.testBit)
    refine ⟨C.toFinset, fun v hv => mem_of_mem_foldBranch G _ v (List.mem_toFinset.mp hv),
      fun u hu v hv hadj => ?_, ?_⟩
    · simpa only [List.mem_toFinset] using isCover_eq_true_iff.mp hcov u hu v hv hadj
    · exact (List.toFinset_card_le C).trans
        ((length_foldBranch_le G _).trans (by simp))

/-! ### The search procedure -/

/-- The search depth `min |V| k`, where `|V|` is the number of distinct declared vertices of `G`. -/
def cap (x : Graph × ℕ) : ℕ :=
  min x.1.distinctVertices.length x.2

theorem cap_eq (x : Graph × ℕ) : cap x = min x.1.1.toFinset.card x.2 := by
  rw [cap, Graph.length_distinctVertices]

theorem cap_le_snd (x : Graph × ℕ) : cap x ≤ x.2 :=
  Nat.min_le_right _ _

/-- **Bounded-search-tree decision procedure for `VertexCover`**: try all `2 ^ cap x` paths of
length `cap x` and check that `k ≤ |V|` (`cap x = k`). -/
def search (x : Graph × ℕ) : Bool :=
  decide (cap x = x.2) &&
    (List.range (2 ^ cap x)).any fun i =>
      isCover x.1 (foldBranch x.1 ((List.range (cap x)).map i.testBit))

/-- **`VertexCover.search` decides `VertexCover`.** -/
theorem search_eq_true_iff (x : Graph × ℕ) : search x = true ↔ x ∈ VertexCover := by
  rcases x with ⟨G, k⟩
  rw [search, mem_VertexCover_iff_exists_card_le]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, cap_eq,
    min_eq_right_iff]
  refine and_congr_right fun hk => ?_
  rw [min_eq_right hk, exists_lt_two_pow_isCover_foldBranch]

/-! ### Running time -/

open ComputableInPolyTime in
/-- The capped depth `cap` is computable in polynomial time in unary. -/
@[fun_prop]
theorem computableInPolyTime_cap :
    ComputableInPolyTime cap (encPair encGraph encNat) encUnary := by
  unfold cap
  exact binary_min_unary' (by fun_prop) (snd _ _)

open ComputableInPolyTime in
/-- A single step of the bounded search tree is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_branchStep :
    ComputableInPolyTime (fun p : (Graph × List ℕ) × Bool => branchStep p.1.1 p.1.2 p.2)
      (encPair (encPair encGraph (encList encNat)) encBool) (encList encNat) := by
  unfold branchStep
  fun_prop

/-- Each step of the bounded search tree increases the encoded cover by at most
`2 * |encGraph G| + 2` bits. -/
private theorem length_encList_branchStep_le (G : Graph) (C : List ℕ) (b : Bool) :
    (encList encNat (branchStep G C b)).length ≤
      (encList encNat C).length + (2 * (encGraph G).length + 2) := by
  unfold branchStep
  cases h : isCover G C
  · dsimp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨_, he₁, he₂, _, _, _⟩ := mem_uncoveredEdges_iff.mp (headD_mem_uncoveredEdges h)
    have h₁ : (encNat ((uncoveredEdges G C).headD (0, 0)).1).length ≤ (encGraph G).length := by
      calc (encNat ((uncoveredEdges G C).headD (0, 0)).1).length
          ≤ (encList encNat G.1).length := length_le_encList_of_mem encNat he₁
        _ ≤ (encGraph G).length := by simp only [encGraph, length_encPair]; omega
    have h₂ : (encNat ((uncoveredEdges G C).headD (0, 0)).2).length ≤ (encGraph G).length := by
      calc (encNat ((uncoveredEdges G C).headD (0, 0)).2).length
          ≤ (encList encNat G.1).length := length_le_encList_of_mem encNat he₂
        _ ≤ (encGraph G).length := by simp only [encGraph, length_encPair]; omega
    have hw : (encNat (if b then ((uncoveredEdges G C).headD (0, 0)).2
        else ((uncoveredEdges G C).headD (0, 0)).1)).length ≤ (encGraph G).length := by
      split_ifs <;> assumption
    simp only [Bool.false_eq_true, ↓reduceIte, encList_cons, List.length_append, length_frame]
    omega
  · simp only [↓reduceIte]
    omega

/-- Candidate path tuples `((G, k), cap (G, k), i)`, with `cap (G, k)` in unary. -/
private abbrev Cand : Type := ((Graph × ℕ) × ℕ) × ℕ

private abbrev encCand : Cand ↪ List Bool :=
  encPair (encPair (encPair encGraph encNat) encUnary) encNat

open ComputableInPolyTime in
/-- Computing the `m` branching bits of path `i` is polynomial-time. -/
private theorem computableInPolyTime_branchBits :
    ComputableInPolyTime (fun s : Cand => (List.range s.1.2).map s.2.testBit)
      encCand (encList encBool) := by
  have heq : (fun s : Cand => (List.range s.1.2).map s.2.testBit) =
      fun s => (List.range s.1.2).map fun j => (encNat s.2).getD j false := by
    funext s
    congr 1
    funext j
    rw [Nat.testBit_eq_inth]
    rfl
  rw [heq]
  exact mapWithInput (range.comp ((snd _ _).comp (fst _ _)))
    (bitsGetDWithInput
      ((of_eq (f := encNat) (encIn := encNat) (encOut := encBits) fun _ => rfl).comp
        ((snd _ _).comp (fst _ _))) (snd _ _) false)

open ComputableInPolyTime in
/-- Following a root-to-leaf path in the bounded search tree is polynomial-time. -/
private theorem computableInPolyTime_foldBranch :
    ComputableInPolyTime
      (fun s : Cand => foldBranch s.1.1.1 ((List.range s.1.2).map s.2.testBit))
      encCand (encList encNat) := by
  have hG : ComputableInPolyTime (fun s : Cand => s.1.1.1) encCand encGraph := by fun_prop
  have hgrowth_poly : PolyBounded (fun s : Cand => (encCand s).length)
      (fun s : Cand => 2 * (encGraph s.1.1.1).length + 2) :=
    ((PolyBounded.const 2).mul hG.polyBounded_length).add (.const 2)
  exact foldlWith_of_bounded_growth hG computableInPolyTime_branchBits (const [])
    computableInPolyTime_branchStep hgrowth_poly
    fun s C b _ => length_encList_branchStep_le s.1.1.1 C b

open ComputableInPolyTime in
/-- Checking whether candidate path `i` yields a valid vertex cover of size `k ≤ |V|` is
polynomial-time. -/
private theorem computableInPolyTime_checkCand :
    ComputableInPolyTime
      (fun s : Cand =>
        decide (s.1.2 = s.1.1.2) &&
          isCover s.1.1.1 (foldBranch s.1.1.1 ((List.range s.1.2).map s.2.testBit)))
      encCand encBool := by
  have hcov : ComputableInPolyTime
      (fun s : Cand => isCover s.1.1.1 (foldBranch s.1.1.1 ((List.range s.1.2).map s.2.testBit)))
      encCand encBool :=
    computableInPolyTime_isCover.comp
      ((show ComputableInPolyTime (fun s : Cand => s.1.1.1) encCand encGraph
        by fun_prop).prod computableInPolyTime_foldBranch)
  exact bool_and'
    (((unary_to_binary.comp ((snd _ _).comp (fst _ _))).beq
      ((snd _ _).comp ((fst _ _).comp (fst _ _)))).of_enc_eq
      fun _ => by simp [beq_eq_decide])
    hcov

end VertexCover

/-- **`VertexCover` by bounded search tree**: `VertexCover` is decidable within time `2 ^ k` times
a polynomial in the length of the encoded instance, for target cover size `k`. -/
theorem VertexCover_decidableInExpTime_one :
    DecidableInExpTime VertexCover (encPair encGraph encNat) Prod.snd 1 := by
  have hB : DecidableInExpTime
      {s : VertexCover.Cand |
        (decide (s.1.2 = s.1.1.2) &&
          VertexCover.isCover s.1.1.1
            (VertexCover.foldBranch s.1.1.1 ((List.range s.1.2).map s.2.testBit))) = true}
      VertexCover.encCand (fun _ => 0) 0 :=
    .of_computableInPolyTime VertexCover.computableInPolyTime_checkCand (fun _ => Iff.rfl)
  have hf : ComputableInPolyTime
      (fun q : (Graph × ℕ) × ℕ => ((q.1, VertexCover.cap q.1), q.2))
      (encPair (encPair encGraph encNat) encNat) VertexCover.encCand := by fun_prop
  have hfA (x : Graph × ℕ) : x ∈ VertexCover ↔ ∃ i < 2 ^ VertexCover.cap x,
      ((x, VertexCover.cap x), i) ∈
        {s : VertexCover.Cand |
          (decide (s.1.2 = s.1.1.2) &&
            VertexCover.isCover s.1.1.1
              (VertexCover.foldBranch s.1.1.1 ((List.range s.1.2).map s.2.testBit))) = true} := by
    rw [← VertexCover.search_eq_true_iff, VertexCover.search]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hcap, i, hi, hcov⟩
      exact ⟨i, hi, hcap, hcov⟩
    · rintro ⟨i, hi, hcap, hcov⟩
      exact ⟨hcap, i, hi, hcov⟩
  simpa using hB.of_exhaustiveSearch hf VertexCover.computableInPolyTime_cap hfA
    (c := 0) (fun _ _ => Nat.zero_le _) (M := 1) (K := 0)
    (fun x => by simpa using VertexCover.cap_le_snd x) le_rfl

/-- **`VertexCover` is fixed-parameter tractable** in the target cover size `k`. -/
theorem VertexCover_mem_FPT : VertexCover ∈ FPT (encPair encGraph encNat) Prod.snd :=
  VertexCover_decidableInExpTime_one.mem_FPT

/-- **`VertexCover` has a kernel** in the target cover size `k`. -/
theorem VertexCover_hasKernel : HasKernel (encPair encGraph encNat) Prod.snd VertexCover :=
  hasKernel_of_mem_FPT VertexCover_mem_FPT

end Cslib.Complexity
