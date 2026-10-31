/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import Complexity.Computability.PolyTime.CNF.SparsePolyCompile
import Complexity.Foundations.Data.List.OfFn

/-!
# The incidence network of Lemma D.2

Lemma D.2 of [OpenAI2026ETH] (pp. 54–56) counts the common zeros of a sparse polynomial system
over `𝔽₂` by contracting, for each *degree array*, a bipartite Boolean tensor network whose wires
index the monomials of the incidence polynomial. This file builds that network as a described
network (`DescribedNetwork`) and proves its shape: it is rows-first bipartite, and its edges,
vertices and ports are counted. The entries of its vertices, their native evaluation, the wire
bound (D.3) and the contraction are separate.

**The system.** A system on `n` variables is a list `sys` of equations, each a list of monomials,
each a list of variable indices (the representation of `Cslib.Complexity.evalSystem`). The *scope*
of test `i` is `equationVars sys[i]`, its variables in increasing order without repetition, and an
*incidence* is a pair of a test and a variable of its scope.

**Groups and arrays** (p. 55). The tests and the variables are split separately into `J` groups by
their residues modulo `J` (`testGroup`, `varGroup`), so that group sizes differ by at most one. The
incidences between test group `g` and variable group `h` are listed by `pairInc J sys g h`, as
pairs of the position of the test in its group and the variable. A *degree array* is a list `d`
whose entry `g J + h` is the number `d_gh` of selected incidences of the pair `(g, h)`. It is *live*
(`live`) when its entries below `J²` sum to at most `K`; this is the paper's bound
`Σ d_gh ≤ K`.

**Index wires** (p. 55). The pair `(g, h)` gets `⌈log₂ C_gh⌉` wires (`width`), where
`C_gh = C(N_gh, d_gh)` is the number of subsets of size `d_gh` of its `N_gh` incidences; the bits on
them index such a subset. The wires of the `J²` pairs are numbered consecutively in the order
`g J + h` (`blockStart`, `blockRange`), and there are `numWires` of them. Test group `g` is a row
whose ports are the wires of the pairs `(g, 0), …, (g, J - 1)` in order (`rowPorts`), and variable
group `h` is a column whose ports are those of `(0, h), …, (J - 1, h)` (`colPorts`).

**Descriptors** (`Desc`). A row carries the precision `P`, the truncation order `ℓ`, the monomials
of the tests of its group and, for each variable group, the incidences of the pair and their
selected number. A column carries `P`, the variables of its group and the same lists for each test
group. A fixed table, read as in an explicit network, describes the other vertices.

**Padding and dead arrays** (`network`). Theorem D.1 is applied at a size `s`, and its interface
asks for at least `s` edges (`Cslib.Circuits.Frontier.EntryAdmissible`). The network adds
`s - M` disjoint edges, `M` the number of index wires, each with a row whose table `[1, 0]` is
`[x = 0]` and a column whose table `[1, 1]` is the constant one; they leave the contraction
unchanged. A dead array (not live) gets only the `s` padding edges and one isolated row with the
table `[0]`, so its contraction is zero; the loop of Lemma D.2 can then sum over all arrays
without a validity test.

## Main definitions

* `Cslib.Circuits.Frontier.IncidenceNetwork.testGroup`,
  `Cslib.Circuits.Frontier.IncidenceNetwork.varGroup`: the groups.
* `Cslib.Circuits.Frontier.IncidenceNetwork.pairInc`: the incidences of a pair of groups.
* `Cslib.Circuits.Frontier.IncidenceNetwork.width`: the number of index wires of a pair.
* `Cslib.Circuits.Frontier.IncidenceNetwork.live`: the arrays with `Σ d_gh ≤ K`.
* `Cslib.Circuits.Frontier.IncidenceNetwork.Desc`: the descriptors.
* `Cslib.Circuits.Frontier.IncidenceNetwork.network`: the network of an array, with its number of
  rows.

## Main results

* `Cslib.Circuits.Frontier.IncidenceNetwork.flatMap_blockRange`: consecutive blocks of wires.
* `Cslib.Circuits.Frontier.IncidenceNetwork.isRowsFirstBipartite_network`: the network is
  rows-first bipartite.
* `Cslib.Circuits.Frontier.IncidenceNetwork.numEdges_network`: it has `max M s` edges.
* `Cslib.Circuits.Frontier.IncidenceNetwork.length_vertices_network`: it has `2 J + 2 (s - M)`
  vertices when live, and `1 + 2 s` when dead.
* `Cslib.Circuits.Frontier.IncidenceNetwork.length_rowPorts`,
  `Cslib.Circuits.Frontier.IncidenceNetwork.length_colPorts`: the degrees of the group vertices.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.2 (pp. 54–56).
-/

public section

namespace Cslib.Circuits.Frontier.IncidenceNetwork

open Cslib.Complexity

/-! ### Consecutive blocks of wires -/

/-- The first number of block `b` when block `b'` has `w b'` numbers: `Σ_{b' < b} w b'`. -/
@[expose] def blockStart (w : ℕ → ℕ) (b : ℕ) : ℕ := ((List.range b).map w).sum

/-- The numbers of block `b`: `blockStart w b, …, blockStart w b + w b - 1`. -/
@[expose] def blockRange (w : ℕ → ℕ) (b : ℕ) : List ℕ := List.range' (blockStart w b) (w b)

theorem blockStart_succ (w : ℕ → ℕ) (b : ℕ) : blockStart w (b + 1) = blockStart w b + w b := by
  simp [blockStart, List.range_succ]

/-- **Consecutive blocks**: the numbers of the blocks below `B`, in order, are the numbers below
`blockStart w B`. -/
theorem flatMap_blockRange (w : ℕ → ℕ) (B : ℕ) :
    (List.range B).flatMap (blockRange w) = List.range (blockStart w B) := by
  induction B with
  | zero => simp [blockStart]
  | succ B ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, blockRange,
      List.range_eq_range', List.range_eq_range', blockStart_succ]
    simpa using List.range'_append_1 (s := 0) (m := blockStart w B) (n := w B)

/-- The pairs `g J + h` for `g < G` and `h < J`, in order, are the numbers below `G J`. -/
theorem flatMap_range_mul (G J : ℕ) :
    (List.range G).flatMap (fun g => (List.range J).map (g * J + ·)) = List.range (G * J) := by
  induction G with
  | zero => simp
  | succ G ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton,
      ← List.range'_eq_map_range, List.range_eq_range', List.range_eq_range', Nat.succ_mul]
    simpa using List.range'_append_1 (s := 0) (m := G * J) (n := J)

/-- A list sum over `List.range n` is the `Finset` sum over `range n` (`List.sum_map_range`). -/
theorem sum_map_range_eq_sum_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  (List.sum_map_range n f).trans (Finset.sum_range f).symm

/-! ### Groups and incidences -/

/-- **The tests of group `g`** among `a` tests in `J` groups: those whose index is `g` modulo
`J`, in increasing order. -/
@[expose] def testGroup (J a g : ℕ) : List ℕ := (List.range a).filter (· % J = g)

/-- **The variables of group `h`** among `n` variables in `J` groups. -/
@[expose] def varGroup (J n h : ℕ) : List ℕ := (List.range n).filter (· % J = h)

/-- **The incidences of the pair `(g, h)`**: for each test of group `g`, in order, the pairs
`(t, v)` of its position `t` in the group and a variable `v` of its scope in group `h`, in
increasing order. -/
@[expose] def pairInc (J : ℕ) (sys : List (List (List ℕ))) (g h : ℕ) : List (ℕ × ℕ) :=
  (testGroup J sys.length g).zipIdx.flatMap fun p =>
    ((equationVars (sys.getD p.1 [])).filter (· % J = h)).map fun v => (p.2, v)

/-- **The number of index wires of the pair `(g, h)`** for the array `d`: `⌈log₂ C(N_gh, d_gh)⌉`,
where `N_gh` is the number of incidences of the pair and `d_gh` the entry `g J + h` of `d`. -/
@[expose] def width (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (g h : ℕ) : ℕ :=
  Nat.clog 2 ((pairInc J sys g h).length.choose (d.getD (g * J + h) 0))

/-- The number of index wires of block `b`, the pair `(b / J, b % J)`. -/
@[expose] def blockWidth (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (b : ℕ) : ℕ :=
  width J sys d (b / J) (b % J)

/-- The number of index wires of all `J²` pairs. -/
@[expose] def numWires (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) : ℕ :=
  blockStart (blockWidth J sys d) (J * J)

/-- **The ports of test group `g`**: the wires of the pairs `(g, 0), …, (g, J - 1)`. -/
@[expose] def rowPorts (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (g : ℕ) : List ℕ :=
  (List.range J).flatMap fun h => blockRange (blockWidth J sys d) (g * J + h)

/-- **The ports of variable group `h`**: the wires of the pairs `(0, h), …, (J - 1, h)`. -/
@[expose] def colPorts (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (h : ℕ) : List ℕ :=
  (List.range J).flatMap fun g => blockRange (blockWidth J sys d) (g * J + h)

/-- **Live arrays**: the entries of `d` below `J²` sum to at most `K`. -/
@[expose] def live (J K : ℕ) (d : List ℕ) : Bool :=
  decide (((List.range (J * J)).map (d.getD · 0)).sum ≤ K)

/-! ### Descriptors and the network -/

/-- A block of a group vertex: the incidences of a pair of groups and their selected number. -/
abbrev Block : Type := List (ℕ × ℕ) × ℕ

/-- **The descriptor of a vertex**: a test group (`inl`: the precision `P`, the truncation order
`ℓ`, the monomials of its tests and its blocks), a variable group (`inr (inl …)`: the precision,
its variables and its blocks), or a fixed table (`inr (inr …)`), read as in an explicit network. -/
abbrev Desc : Type :=
  (ℕ × ℕ × List (List (List ℕ)) × List Block) ⊕ (ℕ × List ℕ × List Block) ⊕ List ℕ

/-- The blocks of test group `g`: the pairs `(g, 0), …, (g, J - 1)`. -/
@[expose] def rowBlocks (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (g : ℕ) :
    List Block :=
  (List.range J).map fun h => (pairInc J sys g h, d.getD (g * J + h) 0)

/-- The blocks of variable group `h`: the pairs `(0, h), …, (J - 1, h)`. -/
@[expose] def colBlocks (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (h : ℕ) :
    List Block :=
  (List.range J).map fun g => (pairInc J sys g h, d.getD (g * J + h) 0)

/-- The vertex of test group `g`. -/
@[expose] def rowVertex (P ℓ J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (g : ℕ) :
    List ℕ × Desc :=
  (rowPorts J sys d g, .inl (P, ℓ, (testGroup J sys.length g).map (sys.getD · []),
    rowBlocks J sys d g))

/-- The vertex of variable group `h` among `n` variables. -/
@[expose] def colVertex (P J n : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) (h : ℕ) :
    List ℕ × Desc :=
  (colPorts J sys d h, .inr (.inl (P, varGroup J n h, colBlocks J sys d h)))

/-- The padding row on edge `e`: the table `[1, 0]`, that is `[x = 0]`. -/
@[expose] def padRow (e : ℕ) : List ℕ × Desc := ([e], .inr (.inr [1, 0]))

/-- The padding column on edge `e`: the table `[1, 1]`, the constant one. -/
@[expose] def padCol (e : ℕ) : List ℕ × Desc := ([e], .inr (.inr [1, 1]))

/-- The isolated row of a dead array: the table `[0]`. -/
@[expose] def deadRow : List ℕ × Desc := ([], .inr (.inr [0]))

/-- The number of index wires of the network: `numWires` for a live array, none for a dead one. -/
@[expose] def mainWires (J K : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) : ℕ :=
  if live J K d then numWires J sys d else 0

/-- The rows of the network: the test groups for a live array, or the isolated row for a dead
one, then the padding rows. -/
@[expose] def rows (P ℓ J K s : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :
    List (List ℕ × Desc) :=
  (if live J K d then (List.range J).map (rowVertex P ℓ J sys d) else [deadRow]) ++
    (List.range (s - mainWires J K sys d)).map fun e => padRow (mainWires J K sys d + e)

/-- The columns of the network: the variable groups for a live array, then the padding
columns. -/
@[expose] def cols (P J K s n : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :
    List (List ℕ × Desc) :=
  (if live J K d then (List.range J).map (colVertex P J n sys d) else []) ++
    (List.range (s - mainWires J K sys d)).map fun e => padCol (mainWires J K sys d + e)

/-- **The incidence network of the array `d`** (Lemma D.2, pp. 55–56), with its number of rows:
for `J` groups, degree cap `K`, size `s`, precision `P`, truncation order `ℓ`, and the system `sys`
on `n` variables. A live array gets the index wires and the group vertices; every array gets
padding up to `s` edges. -/
@[expose] def network (P ℓ J K s n : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :
    ℕ × DescribedNetwork Desc :=
  ((rows P ℓ J K s sys d).length,
    ⟨mainWires J K sys d + (s - mainWires J K sys d),
      rows P ℓ J K s sys d ++ cols P J K s n sys d⟩)

/-! ### Counting ports -/

variable {J : ℕ} {sys : List (List (List ℕ))} {d : List ℕ}

/-- The block of the pair `(g, h)` has the index wires of the pair. -/
theorem blockWidth_mul_add {g h : ℕ} (hh : h < J) :
    blockWidth J sys d (g * J + h) = width J sys d g h := by
  have hJ : 0 < J := by omega
  rw [blockWidth, Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt hh, Nat.mod_eq_of_lt hh, Nat.zero_add]

/-- The ports of all test groups, in order, are the index wires. -/
theorem flatMap_rowPorts (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :
    (List.range J).flatMap (rowPorts J sys d) = List.range (numWires J sys d) := by
  have h := congrArg (List.flatMap (blockRange (blockWidth J sys d))) (flatMap_range_mul J J)
  rw [List.flatMap_assoc, flatMap_blockRange] at h
  rw [numWires, ← h]
  simp only [List.flatMap_map]
  rfl

/-- The number of times a number is a port of the test groups: once if it is an index wire. -/
theorem sum_count_rowPorts (i : ℕ) :
    ((List.range J).map fun g => (rowPorts J sys d g).count i).sum =
      if i < numWires J sys d then 1 else 0 := by
  have h := congrArg (List.count i) (flatMap_rowPorts J sys d)
  rw [List.count_flatMap, List.count_range] at h
  simpa [Function.comp_def] using h

/-- The number of times a number is a port of the variable groups: once if it is an index wire. -/
theorem sum_count_colPorts (i : ℕ) :
    ((List.range J).map fun h => (colPorts J sys d h).count i).sum =
      if i < numWires J sys d then 1 else 0 := by
  rw [← sum_count_rowPorts]
  simp only [rowPorts, colPorts, List.count_flatMap, sum_map_range_eq_sum_range, Function.comp_def]
  exact Finset.sum_comm

/-- A port of a test group `g < J` is an index wire. -/
theorem lt_of_mem_rowPorts {g i : ℕ} (hg : g < J) (hi : i ∈ rowPorts J sys d g) :
    i < numWires J sys d := by
  have : i ∈ (List.range J).flatMap (rowPorts J sys d) :=
    List.mem_flatMap.mpr ⟨g, List.mem_range.mpr hg, hi⟩
  rw [flatMap_rowPorts] at this
  exact List.mem_range.mp this

/-- A port of a variable group `h < J` is an index wire. -/
theorem lt_of_mem_colPorts {h i : ℕ} (hh : h < J) (hi : i ∈ colPorts J sys d h) :
    i < numWires J sys d := by
  have hc : 0 < (colPorts J sys d h).count i := List.count_pos_iff.mpr hi
  have h1 := sum_count_colPorts (J := J) (sys := sys) (d := d) i
  have h2 : (colPorts J sys d h).count i ≤
      ((List.range J).map fun h => (colPorts J sys d h).count i).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩)
  by_contra hn
  rw [ite_eq_right hn] at h1
  omega

/-- **The degree of a test group** `g`: the index wires of its pairs. -/
theorem length_rowPorts (g : ℕ) :
    (rowPorts J sys d g).length = ∑ h ∈ Finset.range J, width J sys d g h := by
  rw [rowPorts, List.length_flatMap, sum_map_range_eq_sum_range]
  exact Finset.sum_congr rfl fun h hh => by
    rw [blockRange, List.length_range', blockWidth_mul_add (Finset.mem_range.mp hh)]

/-- **The degree of a variable group** `h`: the index wires of its pairs. -/
theorem length_colPorts (h : ℕ) (hh : h < J) :
    (colPorts J sys d h).length = ∑ g ∈ Finset.range J, width J sys d g h := by
  rw [colPorts, List.length_flatMap, sum_map_range_eq_sum_range]
  exact Finset.sum_congr rfl fun g _ => by
    rw [blockRange, List.length_range', blockWidth_mul_add hh]

/-- **The number of index wires** is the sum over the pairs. -/
theorem numWires_eq (J : ℕ) (sys : List (List (List ℕ))) (d : List ℕ) :
    numWires J sys d = ∑ g ∈ Finset.range J, ∑ h ∈ Finset.range J, width J sys d g h := by
  have h := congrArg List.length (flatMap_rowPorts J sys d)
  rw [List.length_range, List.length_flatMap, sum_map_range_eq_sum_range] at h
  rw [← h]
  exact Finset.sum_congr rfl fun g _ => length_rowPorts g

/-! ### The shape of the network -/

variable {P ℓ K s n : ℕ}

/-- The padding edges `M, …, M + q - 1`, one per padding vertex, in order. -/
private theorem sum_count_pad (M q i : ℕ) (f : ℕ → List ℕ × Desc) (hf : ∀ e, (f e).1 = [e]) :
    ((List.range q).map fun e => (f (M + e)).1.count i).sum =
      if M ≤ i ∧ i < M + q then 1 else 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_singleton,
      List.sum_singleton, hf, List.count_singleton]
    split_ifs <;> simp_all <;> omega

/-- The number of rows. -/
theorem fst_network : (network P ℓ J K s n sys d).1 = (rows P ℓ J K s sys d).length := rfl

/-- **The network has `max M s` edges**, for `M` its index wires: at least `s`. -/
theorem numEdges_network :
    (network P ℓ J K s n sys d).2.numEdges = max (mainWires J K sys d) s := by
  change mainWires J K sys d + (s - mainWires J K sys d) = _
  omega

/-- The number of rows: `J` or one, plus the padding. -/
theorem length_rows :
    (rows P ℓ J K s sys d).length =
      (if live J K d then J else 1) + (s - mainWires J K sys d) := by
  unfold rows
  split_ifs <;> simp [Nat.add_comm]

/-- The number of columns: `J` or none, plus the padding. -/
theorem length_cols :
    (cols P J K s n sys d).length =
      (if live J K d then J else 0) + (s - mainWires J K sys d) := by
  unfold cols
  split_ifs <;> simp [Nat.add_comm]

/-- **The number of vertices**: `2 J + 2 (s - M)` for a live array, `1 + 2 s` for a dead one. -/
theorem length_vertices_network :
    (network P ℓ J K s n sys d).2.vertices.length =
      (if live J K d then 2 * J else 1) + 2 * (s - mainWires J K sys d) := by
  change (rows P ℓ J K s sys d ++ cols P J K s n sys d).length = _
  rw [List.length_append, length_rows, length_cols]
  split_ifs <;> omega

/-- **The network is rows-first bipartite**: every port is an edge, and every edge is a port of
exactly one row and of exactly one column. -/
theorem isRowsFirstBipartite_network :
    (network P ℓ J K s n sys d).2.IsRowsFirstBipartite (network P ℓ J K s n sys d).1 := by
  set M := mainWires J K sys d with hM
  have hv : (network P ℓ J K s n sys d).2.vertices =
      rows P ℓ J K s sys d ++ cols P J K s n sys d := rfl
  have hE : (network P ℓ J K s n sys d).2.numEdges = M + (s - M) := rfl
  rw [fst_network]
  unfold DescribedNetwork.IsRowsFirstBipartite
  rw [hv, hE, List.take_left, List.drop_left]
  refine ⟨fun v hv i hi => ?_, fun i hi => ⟨?_, ?_⟩⟩
  · -- Every port names an edge.
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · by_cases hl : live J K d
        · rw [ite_eq_left hl] at hv
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
          have := lt_of_mem_rowPorts (List.mem_range.mp hg) hi
          rw [hM, mainWires, ite_eq_left hl]
          omega
        · rw [ite_eq_right hl] at hv
          rw [List.mem_singleton.mp hv] at hi
          simp [deadRow] at hi
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
        rw [List.mem_range] at he
        simp only [padRow, List.mem_singleton] at hi
        omega
    · rcases List.mem_append.mp hv with hv | hv
      · by_cases hl : live J K d
        · rw [ite_eq_left hl] at hv
          obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hv
          have := lt_of_mem_colPorts (List.mem_range.mp hh) hi
          rw [hM, mainWires, ite_eq_left hl]
          omega
        · rw [ite_eq_right hl] at hv
          simp at hv
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
        rw [List.mem_range] at he
        simp only [padCol, List.mem_singleton] at hi
        omega
  · -- Exactly one row.
    rw [rows, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def]
    rw [sum_count_pad M (s - M) i padRow fun _ => rfl]
    by_cases hl : live J K d
    · simp only [ite_eq_left hl, List.map_map, Function.comp_def, rowVertex]
      rw [sum_count_rowPorts]
      have : M = numWires J sys d := by rw [hM, mainWires, ite_eq_left hl]
      split_ifs <;> omega
    · simp only [ite_eq_right hl, List.map_singleton, deadRow, List.count_nil, List.sum_singleton]
      have : M = 0 := by rw [hM, mainWires, ite_eq_right hl]
      split_ifs <;> omega
  · -- Exactly one column.
    rw [cols, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def]
    rw [sum_count_pad M (s - M) i padCol fun _ => rfl]
    by_cases hl : live J K d
    · simp only [ite_eq_left hl, List.map_map, Function.comp_def, colVertex]
      rw [sum_count_colPorts]
      have : M = numWires J sys d := by rw [hM, mainWires, ite_eq_left hl]
      split_ifs <;> omega
    · simp only [ite_eq_right hl, List.map_nil, List.sum_nil]
      have : M = 0 := by rw [hM, mainWires, ite_eq_right hl]
      split_ifs <;> omega

end Cslib.Circuits.Frontier.IncidenceNetwork
