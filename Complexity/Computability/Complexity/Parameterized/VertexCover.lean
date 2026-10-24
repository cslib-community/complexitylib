/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized.Kernelization
public import Complexity.Computability.Complexity.Problems.VertexCover
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Binary
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
`2 ^ min n k` paths (`Cslib.Complexity.VertexCover.search`) runs within time `2 ^ k` times a
polynomial in the length of the encoded instance
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
* `Cslib.Complexity.VertexCover.exists_computableInO_search`: its running time.
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

private theorem cap_le_length (x : Graph × ℕ) : cap x ≤ (encGraph x.1).length :=
  (Nat.min_le_left _ _).trans x.1.length_distinctVertices_le

theorem cap_le_snd (x : Graph × ℕ) : cap x ≤ x.2 :=
  Nat.min_le_right _ _

/-- The state of the bounded-search-tree iteration: the instance `(G, k)`, the capped depth `cap`
in unary, the number of the next root-to-leaf path to try, and whether a cover has been found. -/
abbrev State : Type := ((Graph × ℕ) × ℕ) × (ℕ × Bool)

/-- States encoded as framed tuples, with the capped depth in unary. -/
private abbrev encState : State ↪ List Bool :=
  encPair (encPair (encPair encGraph encNat) encUnary) (encPair encNat encBool)

/-- Try the next numbered path in the bounded search tree. -/
def step (s : State) : State :=
  (s.1, (s.2.1 + 1,
    s.2.2 || isCover s.1.1.1 (foldBranch s.1.1.1 ((List.range s.1.2).map s.2.1.testBit))))

/-- The initial state: no path tried yet. -/
def init (x : Graph × ℕ) : State := ((x, cap x), (0, false))

/-- Check that the target `k` is at most `|V|` (`s.1.2 = s.1.1.2`) and that a cover was found. -/
def finish (s : State) : Bool :=
  decide (s.1.2 = s.1.1.2) && s.2.2

/-- **Bounded-search-tree decision procedure for `VertexCover`**: try all `2 ^ cap x` paths of
length `cap x` and check that `k ≤ |V|` (`cap x = k`). -/
def search (x : Graph × ℕ) : Bool :=
  finish (step^[2 ^ cap x] (init x))

private theorem iterate_step_init (x : Graph × ℕ) (j : ℕ) :
    step^[j] (init x) = ((x, cap x),
      (j, (List.range j).any fun i =>
        isCover x.1 (foldBranch x.1 ((List.range (cap x)).map i.testBit)))) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, step, List.range_succ, List.any_append]
    simp

/-- **`VertexCover.search` decides `VertexCover`.** -/
theorem search_eq_true_iff (x : Graph × ℕ) : search x = true ↔ x ∈ VertexCover := by
  rcases x with ⟨G, k⟩
  rw [search, iterate_step_init, finish, mem_VertexCover_iff_exists_card_le]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, cap_eq,
    min_eq_right_iff]
  refine and_congr_right fun hk => ?_
  rw [min_eq_right hk, exists_lt_two_pow_isCover_foldBranch]

/-! ### Running time -/

open ComputableTidilyInPolyTime in
/-- The capped depth `cap` is computable in polynomial time in unary. -/
@[fun_prop]
theorem computableInPolyTime_cap :
    ComputableInPolyTime cap (encPair encGraph encNat) encUnary := by
  refine .of_tidy ?_
  have heq : cap = fun x : Graph × ℕ =>
      Cslib.BitString.boundedBinaryValue x.1.distinctVertices.length (encNat x.2).reverse := by
    funext x
    rw [cap, Cslib.BitString.boundedBinaryValue_eq, encNat_apply,
      Cslib.BitString.binaryValue_reverse_bits]
  rw [heq]
  exact bitsBoundedBinaryValueWithInput
    ((length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.tidy.comp (fst _ _)))
    (bitsReverse.comp ((encode encNat).comp (snd _ _)))

open ComputableTidilyInPolyTime in
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

open ComputableTidilyInPolyTime in
/-- Computing the `m` branching bits of path `i` is polynomial-time. -/
private theorem computableTidilyInPolyTime_branchBits :
    ComputableTidilyInPolyTime (fun s : State => (List.range s.1.2).map s.2.1.testBit)
      encState (encList encBool) := by
  have heq : (fun s : State => (List.range s.1.2).map s.2.1.testBit) =
      fun s => (List.range s.1.2).map fun j => (encNat s.2.1).getD j false := by
    funext s
    congr 1
    funext j
    rw [Nat.testBit_eq_inth]
    rfl
  rw [heq]
  exact mapWithInput (range.comp ((snd _ _).comp (fst _ _)))
    (bitsGetDWithInput ((encode encNat).comp ((fst _ _).comp ((snd _ _).comp (fst _ _))))
      (snd _ _) false)

open ComputableTidilyInPolyTime in
/-- Following a root-to-leaf path in the bounded search tree is polynomial-time. -/
private theorem computableTidilyInPolyTime_foldBranch :
    ComputableTidilyInPolyTime
      (fun s : State => foldBranch s.1.1.1 ((List.range s.1.2).map s.2.1.testBit))
      encState (encList encNat) := by
  have hG : ComputableTidilyInPolyTime (fun s : State => s.1.1.1) encState encGraph := by fun_prop
  have hgrowth_poly : PolyBounded (fun s : State => (encState s).length)
      (fun s : State => 2 * (encGraph s.1.1.1).length + 2) :=
    ((PolyBounded.const 2).mul hG.polyBounded_length).add (.const 2)
  exact foldlWith_of_bounded_growth hG computableTidilyInPolyTime_branchBits (const [])
    computableInPolyTime_branchStep.tidy hgrowth_poly
    fun s C b _ => length_encList_branchStep_le s.1.1.1 C b

open ComputableTidilyInPolyTime in
/-- One step of the search iteration is polynomial-time. -/
private theorem computableTidilyInPolyTime_step
    : ComputableTidilyInPolyTime step encState encState := by
  have hcov : ComputableTidilyInPolyTime
      (fun s : State => isCover s.1.1.1 (foldBranch s.1.1.1 ((List.range s.1.2).map s.2.1.testBit)))
      encState encBool :=
    computableInPolyTime_isCover.tidy.comp
      ((show ComputableTidilyInPolyTime (fun s : State => s.1.1.1) encState encGraph
        by fun_prop).prod computableTidilyInPolyTime_foldBranch)
  have hor : ComputableTidilyInPolyTime
      (fun s : State =>
        s.2.2 || isCover s.1.1.1 (foldBranch s.1.1.1 ((List.range s.1.2).map s.2.1.testBit)))
      encState encBool :=
    bool_or.comp ((show ComputableTidilyInPolyTime (fun s : State => s.2.2) encState encBool
      by fun_prop).prod hcov)
  exact (fst _ _).prod ((computableTidilyInPolyTime_succ.comp (by fun_prop)).prod hor)

open ComputableTidilyInPolyTime in
/-- The initial state of the search is computed in polynomial time. -/
private theorem computableTidilyInPolyTime_init :
    ComputableTidilyInPolyTime init (encPair encGraph encNat) encState := by
  have hcap := computableInPolyTime_cap.tidy
  unfold init
  fun_prop

open ComputableTidilyInPolyTime in
/-- The number `2 ^ cap x` of paths is computed in binary in polynomial time. -/
private theorem computableTidilyInPolyTime_count :
    ComputableTidilyInPolyTime (fun x => 2 ^ cap x) (encPair encGraph encNat) encNat := by
  have hcap := computableInPolyTime_cap.tidy
  fun_prop

open ComputableTidilyInPolyTime in
/-- Extracting the final answer from the search state is polynomial-time. -/
private theorem computableTidilyInPolyTime_finish :
    ComputableTidilyInPolyTime finish encState encBool := by
  unfold finish
  exact bool_and'
    ((unary_to_binary.comp ((snd _ _).comp (fst _ _))).decide_eq' (by fun_prop))
    (by fun_prop)

/-- **Running time of the bounded search tree for `VertexCover`**: within time `2 ^ k` times a
polynomial in the length of the encoded instance. -/
theorem exists_computableInO_search : ∃ e, ComputableInO search
    (encPair encGraph encNat) encBool
    (fun x => 2 ^ x.2 * ((encPair encGraph encNat x).length + 1) ^ e)
    fun x => 2 ^ x.2 * ((encPair encGraph encNat x).length + 1) ^ e := by
  have this : ∃ e, ComputableTidilyInO search (encPair encGraph encNat) encBool
      (fun x => 2 ^ x.2 * ((encPair encGraph encNat x).length + 1) ^ e) fun x => 2 ^ x.2 *
      ((encPair encGraph encNat x).length + 1) ^ e := by
    obtain ⟨d, _, hstep⟩ := computableTidilyInPolyTime_step.exists_degree
    obtain ⟨d₀, _, hinit⟩ := computableTidilyInPolyTime_init.exists_degree
    obtain ⟨d₁, _, hcount⟩ := computableTidilyInPolyTime_count.exists_degree
    obtain ⟨d₂, _, hans⟩ := computableTidilyInPolyTime_finish.exists_degree
    set size : Graph × ℕ → ℕ := fun x => (encPair encGraph encNat x).length
    set B : Graph × ℕ → ℕ := fun x => 16 * (size x + 1)
    have hcap (x : Graph × ℕ) : cap x ≤ size x :=
      (cap_le_length x).trans (by simp only [size, length_encPair]; omega)
    have hstate : ∀ x, ∀ j ≤ 2 ^ cap x,
        (encState (step^[j] (init x))).length ≤ B x := by
      intro x j hj
      have hK := ComputableTidilyInO.length_encNat_mono hj
      rw [encNat_two_pow] at hK
      have h₁ := hcap x
      rw [iterate_step_init]
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hK
      simp only [encState, length_encPair, encUnary_apply, List.length_replicate, encBool_apply,
        List.length_singleton, B, size] at h₁ ⊢
      omega
    have hiter := ComputableTidilyInO.iterate hcount.inO hinit.inO hstep.inO
      (R := fun x => (B x + 1) ^ d) (Q := fun x => (B x + 1) ^ d) (B := B)
      (fun x j hj => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate x j hj) 1) d)
      (fun x j hj => Nat.pow_le_pow_left (Nat.add_le_add_right (hstate x j hj) 1) d) hstate
    have h := hans.inO.comp hiter
    have hB : PolyBounded size B := .of_forall_le 16 1 fun _ => by simp [B]
    have hpow (j : ℕ) : PolyBounded size fun x => (B x + 1) ^ j :=
      ((PolyBounded.of_polynomiallyBounded id (bound := fun n => (n + 1) ^ j) (by fun_prop)).comp
        hB).mono fun _ => le_rfl
    have hL (j : ℕ) : PolyBounded size fun x => (size x + 1) ^ j :=
      .of_forall_le 1 j fun _ => by simp
    obtain ⟨c, e, hT⟩ := exists_le_mul_two_pow_of_polyBounded (size := size) (μ := Prod.snd)
      ((hpow d).add (hB.add (.of_forall_le 4 2 fun _ => le_rfl)))
      ((hL d₁).add ((hL d₀).add (hpow d₂)))
      (T := fun x => ((encPair encGraph encNat x).length + 1) ^ d₁ +
        ((encPair encGraph encNat x).length + 1) ^ d₀ +
        (2 ^ cap x + 1) * ((B x + 1) ^ d + B x + ((encNat (2 ^ cap x)).length + 1) ^ 2) +
        ((encState (step^[2 ^ cap x] (init x))).length + 1) ^ d₂)
      (fun x => by
        have hK : ((encNat (2 ^ cap x)).length + 1) ^ 2 ≤ 4 * (size x + 1) ^ 2 := by
          rw [encNat_two_pow]
          simp only [List.length_append, List.length_replicate, List.length_singleton]
          calc (cap x + 1 + 1) ^ 2 ≤ (2 * (size x + 1)) ^ 2 :=
                Nat.pow_le_pow_left (by have := hcap x; omega) 2
            _ = 4 * (size x + 1) ^ 2 := by ring
        have hS := Nat.pow_le_pow_left (Nat.add_le_add_right (hstate x _ le_rfl) 1) d₂
        have h2 : 2 ^ cap x ≤ 2 ^ x.2 := Nat.pow_le_pow_right (by norm_num) (cap_le_snd x)
        have h3 := Nat.mul_le_mul (Nat.add_le_add_right h2 1)
          (Nat.add_le_add_left hK ((B x + 1) ^ d + B x))
        simp only [size] at h3 hS ⊢
        nlinarith)
    refine ⟨e, (h.mono c (fun x => ?_) fun x => ?_).of_enc_eq fun x => rfl⟩
    all_goals
      have h₁ := hT x
      simp only [size] at h₁
      generalize 2 ^ cap x = N at h₁ ⊢
      generalize (encNat N).length = K at h₁ ⊢
      obtain ⟨X, hX⟩ : ∃ X, (B x + 1) ^ d + B x = X := ⟨_, rfl⟩
      rw [hX] at h₁
      have h₂ : K ≤ (K + 1) ^ 2 := by nlinarith
      have h₃ : X + (K + 1) ^ 2 ≤ (N + 1) * (X + (K + 1) ^ 2) := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith
  simpa only [computableInO_iff_computableTidilyInO] using this

end VertexCover

/-- **`VertexCover` by bounded search tree**: `VertexCover` is decidable within time `2 ^ k` times
a polynomial in the length of the encoded instance, for target cover size `k`. -/
theorem VertexCover_decidableInExpTime_one :
    DecidableInExpTime VertexCover (encPair encGraph encNat) Prod.snd 1 := by
  obtain ⟨e, h⟩ := VertexCover.exists_computableInO_search
  refine DecidableInExpTime.of_computableInO h (fun x => (VertexCover.search_eq_true_iff x).symm) 1
    e
    fun x => ?_
  rw [one_mul, Real.rpow_natCast]
  push_cast
  rw [one_mul]

/-- **`VertexCover` is fixed-parameter tractable** in the target cover size `k`. -/
theorem VertexCover_mem_FPT : VertexCover ∈ FPT (encPair encGraph encNat) Prod.snd :=
  VertexCover_decidableInExpTime_one.mem_FPT

/-- **`VertexCover` has a kernel** in the target cover size `k`. -/
theorem VertexCover_hasKernel : HasKernel (encPair encGraph encNat) Prod.snd VertexCover :=
  hasKernel_of_mem_FPT VertexCover_mem_FPT

end Cslib.Complexity
