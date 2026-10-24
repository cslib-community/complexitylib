/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.BipartiteMatching
public import Complexity.Computability.Circuit.Monotone.KarchmerWigderson
public import Complexity.Computability.Communication.Disjointness
public import Complexity.Computability.Communication.Operations
public import Mathlib.Data.Fintype.Pi
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.PMF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Monotone formulas for bipartite perfect matching need linear depth

**Raz and Wigderson** showed that monotone circuits deciding whether a graph has a perfect matching
need linear depth [RazWigderson1992]. For bipartite graphs with `n` left and `n` right vertices,
a monotone formula computing `bipartitePerfectMatching n` has depth at least
`(n - 2 ^ 14) / 2 ^ 13` (`Monotone.le_mul_eformulaDepth_bipartitePerfectMatching_add`). By the
monotone Karchmer–Wigderson theorem (`Monotone.eformulaDepth_eq_ecomplexity`) this is a lower
bound on the monotone Karchmer–Wigderson game of bipartite perfect matching
(`le_mul_ecomplexity_bipartitePerfectMatching_add`): Alice holds a graph with a perfect matching,
Bob one without, and they must find an edge of Alice's graph missing from Bob's.

The proof is a randomized reduction from disjointness, whose randomized complexity is linear
(`PublicCoin.le_mul_ecomplexityFun_disjointness_add_of_le`), to this game [RazWigderson1992],
[Kushilevitz and Nisan, Chapter 10][KushilevitzNisan1997], here with gadgets for bipartite graphs.
Let Alice and Bob hold sets `x, y ⊆ [m]` and fix `i₀ ∈ [m]`. Every `i` has a left vertex `bᵢ` and
right vertices `aᵢ`, `cᵢ` (`RazWigderson.Vertex`, with `m + e` further left vertices and `e` further
right ones to reach `n`). Alice's graph is a perfect matching that matches `bᵢ` to `aᵢ` when `i ∈ x`
and to `cᵢ` otherwise (`RazWigderson.aliceGraph`). Bob's graph omits exactly the edges from the
vertices `bᵢ` with `i = i₀` or `i ∈ y` to the right vertices other than the `cⱼ` with `j ≠ i₀` and
`j ∈ y`; the former outnumber the latter by one, so it has no perfect matching
(`RazWigderson.bobGraph`, `RazWigderson.not_hasPerfectMatching_bobGraph`). The edges of Alice's
graph missing from Bob's lie at `bᵢ₀` and at the `bᵢ` with `i ∈ x ∩ y`
(`RazWigderson.exists_of_aliceGraph_of_bobGraph`). With shared random bits the players relabel the
vertices by a uniformly random pair of permutations, run a protocol for the game, and Bob answers
that the sets are disjoint when the edge found is at `bᵢ₀` and `i₀` is not in both sets
(`RazWigderson.bobAnswer`, `RazWigderson.oneRun`). On disjoint sets the answer is always right. If
some `ℓ ≠ i₀` is in both sets, exchanging the edges of Alice's matching at `bᵢ₀` and `bℓ` preserves
both graphs, so the edge found is at `bᵢ₀` for at most half of the relabellings
(`RazWigderson.two_mul_card_filter_run_oneRun_le`). Answering that the sets are disjoint only when
`k` independent runs all say so errs with probability at most `2 ^ (-k)`, with `k (c + 1)` bits for
a protocol of `c` bits (`RazWigderson.solves_reduction`,
`ecomplexityFun_disjointness_le_mul_ecomplexity_bipartitePerfectMatching`). Taking `k = 6` and
`m = n / 2` gives the bound. The constants are not optimized.

## Main definitions

* `Cslib.Circuits.BipartiteMatching.RazWigderson.swapIf`,
  `Cslib.Circuits.BipartiteMatching.RazWigderson.aliceMatching`: the gadget swap and perfect
  matching of Alice's graph.
* `Cslib.Circuits.BipartiteMatching.RazWigderson.aliceGraph`,
  `Cslib.Circuits.BipartiteMatching.RazWigderson.bobGraph`,
  `Cslib.Circuits.BipartiteMatching.RazWigderson.hallSet`,
  `Cslib.Circuits.BipartiteMatching.RazWigderson.coverSet`: the graphs of the reduction and the
  Hall witness for Bob's graph.
* `Cslib.Circuits.BipartiteMatching.RazWigderson.Relabeling`,
  `Cslib.Circuits.BipartiteMatching.RazWigderson.relabel`: vertex relabellings of bipartite graphs.
* `Cslib.Circuits.BipartiteMatching.RazWigderson.repeatedRun`,
  `Cslib.Circuits.BipartiteMatching.RazWigderson.reduction`: repeated runs and the public-coin
  protocol for disjointness.

## Main results

* `Cslib.Circuits.BipartiteMatching.RazWigderson.two_mul_card_filter_run_oneRun_le`: the symmetry
  of the reduction.
* `Cslib.Circuits.BipartiteMatching.RazWigderson.solves_reduction`: its error.
* `Cslib.Circuits.ecomplexityFun_disjointness_le_mul_ecomplexity_bipartitePerfectMatching`: the
  Raz–Wigderson reduction.
* `Cslib.Circuits.le_mul_ecomplexity_bipartitePerfectMatching_add`: the monotone
  Karchmer–Wigderson game of bipartite perfect matching needs `Ω(n)` bits.
* `Cslib.Circuits.Monotone.le_mul_eformulaDepth_bipartitePerfectMatching_add`: monotone formulas
  for bipartite perfect matching need depth `Ω(n)`.

## References

* [R. Raz and A. Wigderson, *Monotone circuits for matching require linear
  depth*][RazWigderson1992]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Circuits

open Cslib.Communication Finset Probability

namespace BipartiteMatching.RazWigderson

variable {m e : ℕ}

/-! ### The graphs of the reduction -/

/-- The vertices of the graphs of the reduction, on each side: two copies of `Fin m` and `e` extra
vertices. On the left, `inl (inl i)` is the vertex `bᵢ` of the gadget of `i`; on the right,
`inl (inl i)` and `inl (inr i)` are its vertices `aᵢ` and `cᵢ`. -/
abbrev Vertex (m e : ℕ) : Type :=
  (Fin m ⊕ Fin m) ⊕ Fin e

/-- Exchange `inl i` and `inr i` exactly when the bit `x i` is zero. -/
def swapIf (x : BitString m) : Fin m ⊕ Fin m → Fin m ⊕ Fin m
  | .inl i => cond (x i) (.inl i) (.inr i)
  | .inr i => cond (x i) (.inr i) (.inl i)

/-- Exchanging twice gives back the vertex. -/
theorem swapIf_involutive (x : BitString m) : Function.Involutive (swapIf x) := by
  rintro (i | i) <;> cases h : x i <;> simp [swapIf, h]

/-- Alice's perfect matching: the gadget vertex `bᵢ` is matched to `aᵢ` when `i` is in her set and
to `cᵢ` otherwise, the other copy of `Fin m` takes the remaining vertices, and the extra vertices
are matched to themselves. -/
def aliceMatching (x : BitString m) : Equiv.Perm (Vertex m e) :=
  Equiv.sumCongr (Function.Involutive.toPerm (swapIf x) (swapIf_involutive x)) (Equiv.refl _)

/-- Alice matches `bᵢ` to `aᵢ` when `x i` is one and to `cᵢ` otherwise. -/
@[simp] theorem aliceMatching_inl_inl (x : BitString m) (i : Fin m) :
    aliceMatching (e := e) x (.inl (.inl i)) = .inl (cond (x i) (.inl i) (.inr i)) :=
  rfl

/-- Alice's graph: the edges of her perfect matching. -/
def aliceGraph (x : BitString m) (p : Vertex m e × Vertex m e) : Bool :=
  decide (p.2 = aliceMatching x p.1)

/-- The left vertices of Bob's Hall violator: the gadget vertices `bᵢ` with `i = i₀` or `i` in his
set. -/
def hallSet (i₀ : Fin m) (y : BitString m) : Vertex m e → Bool
  | .inl (.inl i) => decide (i = i₀) || y i
  | _ => false

/-- Their neighbours in Bob's graph: the gadget vertices `cⱼ` with `j ≠ i₀` in his set. -/
def coverSet (i₀ : Fin m) (y : BitString m) : Vertex m e → Bool
  | .inl (.inr j) => !decide (j = i₀) && y j
  | _ => false

/-- Bob's graph: all edges except those from `hallSet` to right vertices outside `coverSet`. -/
def bobGraph (i₀ : Fin m) (y : BitString m) (p : Vertex m e × Vertex m e) : Bool :=
  !hallSet i₀ y p.1 || coverSet i₀ y p.2

/-- Bob's answer to an edge found by the Karchmer–Wigderson protocol, `true` meaning that the sets
are disjoint: whether the edge starts at `bᵢ₀` and, when `i₀` is in his set, ends at `cᵢ₀`. -/
def bobAnswer (i₀ : Fin m) (y : BitString m) (p : Vertex m e × Vertex m e) : Bool :=
  decide (p.1 = .inl (.inl i₀)) && (!y i₀ || decide (p.2 = .inl (.inr i₀)))

/-- Alice's graph has a perfect matching: her matching. -/
theorem hasPerfectMatching_aliceGraph (x : BitString m) :
    HasPerfectMatching (aliceGraph (e := e) x) :=
  ⟨aliceMatching x, fun v => by simp [aliceGraph]⟩

/-- Bob's graph has no perfect matching: `hallSet` has one more vertex than `coverSet`, which
contains all its neighbours. -/
theorem not_hasPerfectMatching_bobGraph (i₀ : Fin m) (y : BitString m) :
    ¬HasPerfectMatching (bobGraph (e := e) i₀ y) := by
  let b : Fin m ↪ Vertex m e := ⟨fun i => .inl (.inl i), fun i j h => by simpa using h⟩
  let c : Fin m ↪ Vertex m e := ⟨fun i => .inl (.inr i), fun i j h => by simpa using h⟩
  set B := (univ : Finset (Fin m)).filter fun j => j ≠ i₀ ∧ y j = true
  have hA : (univ : Finset (Fin m)).filter (fun i => i = i₀ ∨ y i = true) = insert i₀ B := by
    ext i
    by_cases h : i = i₀ <;> simp [B, h]
  refine not_hasPerfectMatching_of_card_lt (S := (insert i₀ B).map b) (T := B.map c) ?_ ?_
  · intro v hv w hw
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hv
    rw [← hA, mem_filter] at hi
    have hhall : hallSet i₀ y (b i) = true := by
      change hallSet i₀ y (.inl (.inl i)) = true
      rcases hi.2 with h | h <;> simp [hallSet, h]
    simp only [bobGraph, hhall, Bool.not_true, Bool.false_or] at hw
    rcases w with (j | j) | j <;> simp only [coverSet, Bool.false_eq_true] at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hw
    exact mem_map.mpr ⟨j, mem_filter.mpr ⟨mem_univ _, hw⟩, rfl⟩
  · rw [card_map, card_map, card_insert_of_notMem (by simp [B])]
    omega

/-- The edges of Alice's graph missing from Bob's graph are the edges of her matching at `bᵢ` for
`i = i₀` and for `i` in both sets. -/
theorem exists_of_aliceGraph_of_bobGraph {x y : BitString m} {i₀ : Fin m}
    {p : Vertex m e × Vertex m e} (hA : aliceGraph x p = true) (hB : bobGraph i₀ y p = false) :
    ∃ i, p = (.inl (.inl i), aliceMatching x (.inl (.inl i))) ∧
      (i = i₀ ∨ x i = true ∧ y i = true) := by
  obtain ⟨u, w⟩ := p
  simp only [aliceGraph, decide_eq_true_eq] at hA
  subst hA
  simp only [bobGraph, Bool.or_eq_false_iff, Bool.not_eq_false'] at hB
  obtain ⟨hhall, hcover⟩ := hB
  rcases u with (i | i) | i <;> simp only [hallSet, Bool.false_eq_true] at hhall
  refine ⟨i, rfl, ?_⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hhall
  cases hx : x i
  · simp only [aliceMatching_inl_inl, hx, Bool.cond_false, coverSet, Bool.and_eq_false_iff,
      Bool.not_eq_false', decide_eq_true_eq] at hcover
    rcases hhall with h | h
    · exact Or.inl h
    · rcases hcover with h' | h'
      · exact Or.inl h'
      · rw [h] at h'
        exact absurd h' (by decide)
  · rcases hhall with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩

/-- Bob answers that the sets are disjoint exactly on the edge at `bᵢ₀`, unless `i₀` is in both
sets. -/
private theorem bobAnswer_aliceMatching (i₀ i : Fin m) (x y : BitString m) :
    bobAnswer i₀ y (.inl (.inl i), aliceMatching (e := e) x (.inl (.inl i))) =
      (decide (i = i₀) && !(x i₀ && y i₀)) := by
  by_cases h : i = i₀
  · subst h
    cases hx : x i <;> cases hy : y i <;> simp [bobAnswer, hx, hy]
  · simp [bobAnswer, h]

/-- **The symmetry of the reduction.** Exchanging the edges of Alice's matching at `bᵢ₀` and `bℓ`
preserves her graph. -/
private theorem aliceGraph_swap_swap {x : BitString m} {i₀ ℓ : Fin m} (u w : Vertex m e) :
    aliceGraph x (Equiv.swap (.inl (.inl i₀)) (.inl (.inl ℓ)) u,
        Equiv.swap (aliceMatching x (.inl (.inl i₀))) (aliceMatching x (.inl (.inl ℓ))) w) =
      aliceGraph x (u, w) := by
  simp only [aliceGraph, Equiv.swap_apply_apply, Equiv.Perm.mul_apply, Equiv.apply_eq_iff_eq,
    Equiv.Perm.inv_eq_iff_eq]

/-- Exchanging the edges of Alice's matching at `bᵢ₀` and `bℓ`, for `ℓ` in both sets, preserves
Bob's graph. -/
private theorem bobGraph_swap_swap {x y : BitString m} {i₀ ℓ : Fin m} (hx : x ℓ = true)
    (hy : y ℓ = true) (u w : Vertex m e) :
    bobGraph i₀ y (Equiv.swap (.inl (.inl i₀)) (.inl (.inl ℓ)) u,
        Equiv.swap (aliceMatching x (.inl (.inl i₀))) (aliceMatching x (.inl (.inl ℓ))) w) =
      bobGraph i₀ y (u, w) := by
  have h₁ : hallSet (e := e) i₀ y (.inl (.inl i₀)) = hallSet (e := e) i₀ y (.inl (.inl ℓ)) := by
    simp [hallSet, hy]
  have h₂ : coverSet (e := e) i₀ y (aliceMatching x (.inl (.inl i₀))) =
      coverSet (e := e) i₀ y (aliceMatching x (.inl (.inl ℓ))) := by
    cases h : x i₀ <;> simp [coverSet, hx, h]
  simp only [bobGraph, Equiv.apply_swap_eq_self h₁, Equiv.apply_swap_eq_self h₂]

/-! ### The randomized protocol -/

variable {n k : ℕ}

/-- The relabellings of the graphs of the reduction: a permutation of the left and one of the right
vertices. -/
abbrev Relabeling (m e : ℕ) : Type :=
  Equiv.Perm (Vertex m e) × Equiv.Perm (Vertex m e)

/-- The relabellings form a finite type. Declaring the instance directly keeps the instance terms
for tuples of relabellings below the size limit of instance synthesis. -/
instance (m e : ℕ) : Fintype (Relabeling m e) :=
  instFintypeProd _ _

/-- The pair of vertices named by an input bit of `bipartitePerfectMatching n`, identifying the
vertices of the reduction with `Fin n` along `h` and relabelling them by `σ`. -/
def relabel (h : Vertex m e ≃ Fin n) (σ : Relabeling m e) (k : Fin (n * n)) :
    Vertex m e × Vertex m e :=
  (σ.1.symm (h.symm (finProdFinEquiv.symm k).1), σ.2.symm (h.symm (finProdFinEquiv.symm k).2))

/-- One run of the reduction: the players relabel their graphs by `σ`, run the protocol `p` for the
monotone Karchmer–Wigderson game of bipartite perfect matching on them, and Bob answers on the edge
it finds. -/
def oneRun (p : KWProtocol (Fin (n * n))) (h : Vertex m e ≃ Fin n) (i₀ : Fin m)
    (σ : Relabeling m e) : Protocol (BitString m) (BitString m) Bool :=
  (p.comap (fun x k => aliceGraph x (relabel h σ k)) fun y k => bobGraph i₀ y (relabel h σ k)).bind
    fun k => .bob (fun y => bobAnswer i₀ y (relabel h σ k)) (.output false) (.output true)

variable {p : KWProtocol (Fin (n * n))} {h : Vertex m e ≃ Fin n} {i₀ : Fin m}

/-- A run outputs Bob's answer on the edge found by `p`, relabelled back. -/
private theorem run_oneRun (σ : Relabeling m e) (x y : BitString m) :
    (oneRun p h i₀ σ).run x y = bobAnswer i₀ y (relabel h σ
      (p.run (fun k => aliceGraph x (relabel h σ k)) fun k => bobGraph i₀ y (relabel h σ k))) := by
  simp only [oneRun, Protocol.run_bind, Protocol.run_comap, Protocol.run_bob,
    Protocol.run_output]
  cases bobAnswer i₀ y _ <;> rfl

/-- A run sends one more bit than `p`. -/
theorem depth_oneRun_le (σ : Relabeling m e) : (oneRun p h i₀ σ).depth ≤ p.depth + 1 := by
  refine (Protocol.depth_bind_le (d := 1) fun _ => ?_).trans ?_
  · simp
  · rw [Protocol.depth_comap]

private theorem graph_relabel (h : Vertex m e ≃ Fin n) (σ : Relabeling m e)
    (G : Vertex m e × Vertex m e → Bool) :
    graph (fun k => G (relabel h σ k)) =
      fun q => G ((h.symm.trans σ.1.symm) q.1, (h.symm.trans σ.2.symm) q.2) := by
  funext q
  simp only [graph, relabel, Equiv.symm_apply_apply, Equiv.trans_apply]

/-- The relabelled graphs are an instance of the monotone Karchmer–Wigderson game of bipartite
perfect matching: Alice's has a perfect matching and Bob's has none. -/
private theorem bipartitePerfectMatching_aliceGraph (h : Vertex m e ≃ Fin n) (σ : Relabeling m e)
    (x : BitString m) :
    bipartitePerfectMatching n (fun k => aliceGraph x (relabel h σ k)) = true := by
  rw [bipartitePerfectMatching_eq_true_iff, graph_relabel]
  exact (hasPerfectMatching_comp_iff _ _ _).mpr (hasPerfectMatching_aliceGraph x)

/-- Bob's relabelled graph has no perfect matching. -/
private theorem bipartitePerfectMatching_bobGraph (h : Vertex m e ≃ Fin n) (σ : Relabeling m e)
    (y : BitString m) :
    bipartitePerfectMatching n (fun k => bobGraph i₀ y (relabel h σ k)) = false := by
  rw [Bool.eq_false_iff]
  intro hpm
  rw [bipartitePerfectMatching_eq_true_iff, graph_relabel] at hpm
  exact not_hasPerfectMatching_bobGraph i₀ y ((hasPerfectMatching_comp_iff _ _ _).mp hpm)

variable (hp : p.Solves ExceedsAt {x | bipartitePerfectMatching n x = true}
  {y | bipartitePerfectMatching n y = false})
include hp

/-- A run answers `true` exactly on the edge of the gadget of `i₀`, unless `i₀` is in both sets. -/
private theorem exists_run_oneRun (σ : Relabeling m e) (x y : BitString m) :
    ∃ i, (i = i₀ ∨ x i = true ∧ y i = true) ∧
      (oneRun p h i₀ σ).run x y = (decide (i = i₀) && !(x i₀ && y i₀)) := by
  have hv := hp _ (bipartitePerfectMatching_aliceGraph h σ x) _
    (bipartitePerfectMatching_bobGraph (i₀ := i₀) h σ y)
  obtain ⟨i, hi, hrun⟩ := exists_of_aliceGraph_of_bobGraph hv.1 hv.2
  refine ⟨i, hrun, ?_⟩
  rw [run_oneRun, hi, bobAnswer_aliceMatching]

/-- On disjoint sets every run answers `true`. -/
private theorem run_oneRun_of_disjointness {x y : BitString m} (hxy : disjointness x y = true)
    (σ : Relabeling m e) : (oneRun p h i₀ σ).run x y = true := by
  obtain ⟨i, hi, hrun⟩ := exists_run_oneRun hp σ x y
  simp only [disjointness, decide_eq_true_eq] at hxy
  have hi₀ : i = i₀ := hi.resolve_right fun ⟨hx, hy⟩ => by simpa [hx, hy] using hxy i
  rw [hrun, hi₀, hxy i₀]
  simp

/-- If `i₀` is in both sets, every run answers `false`. -/
private theorem run_oneRun_of_mem {x y : BitString m} (hx : x i₀ = true) (hy : y i₀ = true)
    (σ : Relabeling m e) : (oneRun p h i₀ σ).run x y = false := by
  obtain ⟨i, -, hrun⟩ := exists_run_oneRun hp σ x y
  rw [hrun, hx, hy]
  simp

omit hp in
/-- **The symmetry of the reduction.** If some `ℓ ≠ i₀` is in both sets, a run answers `true` for at
most half of the relabellings: exchanging the edges of Alice's matching at `bᵢ₀` and `bℓ` preserves
both graphs, hence the edge found, but moves it off `bᵢ₀` when it was there. -/
theorem two_mul_card_filter_run_oneRun_le {x y : BitString m} {ℓ : Fin m} (hℓ : ℓ ≠ i₀)
    (hx : x ℓ = true) (hy : y ℓ = true) :
    2 * #{σ : Relabeling m e | (oneRun p h i₀ σ).run x y = true} ≤
      Fintype.card (Relabeling m e) := by
  set τ : Relabeling m e := (Equiv.swap (.inl (.inl i₀)) (.inl (.inl ℓ)),
    Equiv.swap (aliceMatching x (.inl (.inl i₀))) (aliceMatching x (.inl (.inl ℓ))))
  have hrel (σ : Relabeling m e) (k : Fin (n * n)) :
      relabel h (σ * τ) k = (τ.1 (relabel h σ k).1, τ.2 (relabel h σ k).2) := by
    simp only [relabel, τ, Prod.fst_mul, Prod.snd_mul, Equiv.Perm.mul_def, Equiv.symm_trans_apply,
      Equiv.symm_swap]
  have hA (σ : Relabeling m e) : (fun k => aliceGraph x (relabel h (σ * τ) k)) =
      fun k => aliceGraph x (relabel h σ k) := by
    funext k
    rw [hrel]
    exact aliceGraph_swap_swap _ _
  have hB (σ : Relabeling m e) : (fun k => bobGraph i₀ y (relabel h (σ * τ) k)) =
      fun k => bobGraph i₀ y (relabel h σ k) := by
    funext k
    rw [hrel]
    exact bobGraph_swap_swap hx hy _ _
  set E := (univ : Finset (Relabeling m e)).filter fun σ => (oneRun p h i₀ σ).run x y = true
  have hsub : E.image (· * τ) ⊆ Eᶜ := by
    intro σ' hσ'
    obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hσ'
    rw [mem_filter] at hσ
    rw [mem_compl, mem_filter, not_and, run_oneRun, hA, hB, hrel]
    intro _
    have h₁ := hσ.2
    rw [run_oneRun] at h₁
    set q := relabel h σ (p.run (fun k => aliceGraph x (relabel h σ k))
      fun k => bobGraph i₀ y (relabel h σ k))
    simp only [bobAnswer, Bool.and_eq_true, decide_eq_true_eq] at h₁
    simp only [bobAnswer, h₁.1, τ, Equiv.swap_apply_left, Sum.inl.injEq, hℓ, decide_false,
      Bool.false_and, Bool.false_eq_true, not_false_eq_true]
  have hcard : #(E.image (· * τ)) = #E := card_image_of_injective _ (mul_left_injective τ)
  have := card_le_card hsub
  rw [hcard, card_compl] at this
  have hE : #E ≤ Fintype.card (Relabeling m e) := card_le_univ E
  omega

omit hp

/-- `k` runs of the reduction with independent relabellings; the answer is that the sets are
disjoint when every run says so. -/
def repeatedRun (p : KWProtocol (Fin (n * n))) (h : Vertex m e ≃ Fin n) (i₀ : Fin m)
    (σs : Fin k → Relabeling m e) : Protocol (BitString m) (BitString m) Bool :=
  Protocol.runAll (fun i => oneRun p h i₀ (σs i)) fun v => decide (∀ i, v i = true)

/-- **The Raz–Wigderson reduction**: a public-coin protocol for disjointness from a protocol `p`
for the monotone Karchmer–Wigderson game of bipartite perfect matching, running it `k` times on
uniformly random relabellings of the graphs of the reduction. -/
noncomputable def reduction (p : KWProtocol (Fin (n * n))) (h : Vertex m e ≃ Fin n)
    (i₀ : Fin m) (k : ℕ) : PublicCoin (BitString m) (BitString m) Bool :=
  (PMF.uniformOfFintype (Fin k → Relabeling m e)).map (repeatedRun p h i₀)

/-- The reduction sends at most `k` times one more bit than `p`. -/
theorem depth_reduction_le : (reduction p h i₀ k).depth ≤ k * (p.depth + 1) := by
  refine PublicCoin.depth_le_iff.mpr fun q hq => ?_
  obtain ⟨σs, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hq
  exact_mod_cast Protocol.depth_runAll_le fun i => depth_oneRun_le (σs i)

include hp in
/-- **The error of the reduction**: it decides disjointness with error at most `2 ^ (-k)`, for
`k > 0`. On disjoint sets every run answers `true`; if `i₀` is in both sets, every run answers
`false`; otherwise each run answers `true` with probability at most `1 / 2`
(`two_mul_card_filter_run_oneRun_le`), independently. -/
theorem solves_reduction (hk : 0 < k) :
    (reduction p h i₀ k).Solves (1 / 2 ^ k) (fun x y b => disjointness x y = b) Set.univ
      Set.univ := by
  classical
  intro x _ y _
  rw [PublicCoin.errorProb, reduction, PMF.toOuterMeasure_map_apply,
    Probability.PMF.toOuterMeasure_uniformOfFintype_toReal]
  set bad := (univ : Finset (Fin k → Relabeling m e)).filter
    (· ∈ repeatedRun p h i₀ ⁻¹' {q | ¬disjointness x y = q.run x y})
  have hbad : #bad * 2 ^ k ≤ Fintype.card (Relabeling m e) ^ k := by
    by_cases hxy : disjointness x y = true
    · -- On disjoint sets the reduction never errs.
      suffices bad = ∅ by simp [this]
      refine filter_eq_empty_iff.mpr fun σs _ => ?_
      simp [repeatedRun, run_oneRun_of_disjointness hp hxy, hxy]
    by_cases h₀ : x i₀ = true ∧ y i₀ = true
    · -- If `i₀` is in both sets, it never errs either.
      suffices bad = ∅ by simp [this]
      have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
      refine filter_eq_empty_iff.mpr fun σs _ => ?_
      rw [Bool.not_eq_true] at hxy
      simp [repeatedRun, run_oneRun_of_mem hp h₀.1 h₀.2, hxy]
    -- Otherwise it errs only when every run answers `true`.
    have hℓ : ∃ ℓ, x ℓ = true ∧ y ℓ = true := by
      simpa only [disjointness, decide_eq_true_eq, not_forall, Bool.and_eq_false_iff, not_or,
        Bool.not_eq_false] using hxy
    obtain ⟨ℓ, hxℓ, hyℓ⟩ := hℓ
    have hℓ₀ : ℓ ≠ i₀ := fun h' => h₀ (h' ▸ ⟨hxℓ, hyℓ⟩)
    set E := (univ : Finset (Relabeling m e)).filter fun σ => (oneRun p h i₀ σ).run x y = true
    have hsub : bad ⊆ Fintype.piFinset fun _ => E := by
      intro σs hσs
      simp only [bad, mem_filter, Set.mem_preimage, Set.mem_ofPred_eq, repeatedRun,
        Protocol.run_runAll] at hσs
      rw [Fintype.mem_piFinset]
      intro i
      rw [Bool.not_eq_true] at hxy
      rw [hxy, eq_comm, Bool.not_eq_false, decide_eq_true_iff] at hσs
      exact mem_filter.mpr ⟨mem_univ _, hσs.2 i⟩
    have hE := two_mul_card_filter_run_oneRun_le (p := p) (h := h) hℓ₀ hxℓ hyℓ
    calc #bad * 2 ^ k ≤ #E ^ k * 2 ^ k := by
          gcongr
          simpa using card_le_card hsub
      _ = (2 * #E) ^ k := by ring
      _ ≤ Fintype.card (Relabeling m e) ^ k := Nat.pow_le_pow_left hE k
  have hpos : (0 : ℝ) < Fintype.card (Relabeling m e) ^ k := by positivity
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_le_div_iff₀ hpos (by positivity),
    one_mul]
  exact_mod_cast hbad

end BipartiteMatching.RazWigderson

open BipartiteMatching BipartiteMatching.RazWigderson

/-- **The Raz–Wigderson reduction** [RazWigderson1992]: if the monotone Karchmer–Wigderson game of
bipartite perfect matching on `K_{n,n}` has a protocol sending `c` bits and `2 m ≤ n` with `0 < m`,
then public-coin protocols decide disjointness of `m`-bit strings with error `2 ^ (-k)` sending
at most `k (c + 1)` bits, for every `k > 0`. -/
theorem ecomplexityFun_disjointness_le_mul_ecomplexity_bipartitePerfectMatching {m n k : ℕ}
    (hm : 0 < m) (hmn : 2 * m ≤ n) (hk : 0 < k) :
    PublicCoin.ecomplexityFun (1 / 2 ^ k) (disjointness : BitString m → BitString m → Bool) ≤
      k * (Protocol.ecomplexity ExceedsAt {x | bipartitePerfectMatching n x = true}
        {y | bipartitePerfectMatching n y = false} + 1) := by
  cases hc : Protocol.ecomplexity ExceedsAt {x | bipartitePerfectMatching n x = true}
      {y | bipartitePerfectMatching n y = false} using ENat.recTopCoe with
  | top =>
    rw [top_add, ENat.mul_top (by exact_mod_cast hk.ne')]
    exact le_top
  | coe c =>
    obtain ⟨p, hp, hpc⟩ := Protocol.ecomplexity_le_iff.mp hc.le
    have hcard : Fintype.card (Vertex m (n - 2 * m)) = n := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    refine (PublicCoin.ecomplexity_le_depth (solves_reduction hp
      (h := Fintype.equivFinOfCardEq hcard) (i₀ := ⟨0, hm⟩) hk)).trans
      (depth_reduction_le.trans ?_)
    exact_mod_cast Nat.mul_le_mul_left k (Nat.add_le_add_right hpc 1)

/-- **The monotone Karchmer–Wigderson game of bipartite perfect matching needs `Ω(n)` bits**
[RazWigderson1992]: on `K_{n,n}`, it needs at least `(n - 2 ^ 14) / 2 ^ 13` bits. -/
theorem le_mul_ecomplexity_bipartitePerfectMatching_add (n : ℕ) :
    (n : ℕ∞) ≤ 2 ^ 13 * Protocol.ecomplexity ExceedsAt {x | bipartitePerfectMatching n x = true}
      {y | bipartitePerfectMatching n y = false} + 2 ^ 14 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · calc (n : ℕ∞) ≤ 2 ^ 14 := by exact_mod_cast (show n ≤ 2 ^ 14 by omega)
      _ ≤ _ := le_add_self
  set m := n / 2
  have hm : 0 < m := by omega
  have h1 := PublicCoin.le_mul_ecomplexityFun_disjointness_add_of_le
    (ε := 1 / 2 ^ 6) (by norm_num) m
  have h2 := ecomplexityFun_disjointness_le_mul_ecomplexity_bipartitePerfectMatching
    (n := n) (k := 6) hm (by omega) (by norm_num)
  cases hc : Protocol.ecomplexity ExceedsAt {x | bipartitePerfectMatching n x = true}
      {y | bipartitePerfectMatching n y = false} using ENat.recTopCoe with
  | top => simp
  | coe c =>
    rw [hc] at h2
    cases hr : PublicCoin.ecomplexityFun (1 / 2 ^ 6)
        (disjointness : BitString m → BitString m → Bool) using ENat.recTopCoe with
    | top =>
      rw [hr] at h2
      exact absurd (top_le_iff.mp h2) (by exact_mod_cast ENat.natCast_ne_top (6 * (c + 1)))
    | coe r =>
      rw [hr] at h1 h2
      have h1' : m ≤ 2 ^ 9 * r + 2 ^ 12 := by exact_mod_cast h1
      have h2' : r ≤ 6 * (c + 1) := by exact_mod_cast h2
      have : n ≤ 2 ^ 13 * c + 2 ^ 14 := by omega
      exact_mod_cast this

namespace Monotone

/-- **Monotone formulas for bipartite perfect matching need linear depth** [RazWigderson1992]: a
monotone formula computing whether a subgraph of `K_{n,n}` has a perfect matching has depth at
least `(n - 2 ^ 14) / 2 ^ 13`, counting AND and OR gates of fan-in two. -/
theorem le_mul_eformulaDepth_bipartitePerfectMatching_add (n : ℕ) :
    (n : ℕ∞) ≤ 2 ^ 13 * eformulaDepth (bipartitePerfectMatching n) + 2 ^ 14 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have : NeZero (n * n) := ⟨by positivity⟩
  rw [eformulaDepth_eq_ecomplexity]
  exact le_mul_ecomplexity_bipartitePerfectMatching_add n

end Monotone

end Cslib.Circuits
