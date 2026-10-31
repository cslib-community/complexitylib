/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import Complexity.Logics.Propositional.CNF.ModelCount
import Mathlib.Data.List.GetD

/-!
# The clause network of a CNF formula

The explicit Boolean tensor network of the fixed-density case of Theorem 1.1 of [OpenAI2026ETH]
(Appendix D.2): its contraction is the number of satisfying assignments of the formula, it is
bipartite with its rows first, and its degree is bounded by the clause width.

Number the literal occurrences of a formula `φ` with `m` clauses `0, …, N - 1` in order
(`Cslib.Logic.PL.occurrences`). Occurrence `u` has three edges, `3 u`, `3 u + 1` and `3 u + 2`.

* **Rows.** Clause `i` is a vertex whose ports are the edges `3 u` of its occurrences `u`; its
  tensor is one except at the single assignment that falsifies every literal of the clause
  (`ClauseNetwork.clauseEntry`). Occurrence `u` has a *link* vertex with the two ports `3 u + 1`
  and `3 u + 2` and the equality tensor.
* **Columns.** Occurrence `u` has an *equality* vertex with the ports `3 u` and `3 u + 1`, and
  `3 w + 2` for every occurrence `w` whose previous occurrence of the same variable is `u`
  (`ClauseNetwork.prev`, which is `w` itself at a first occurrence). Its tensor is equality
  (`ClauseNetwork.eqEntry`).

So the occurrences of a variable form a chain of equality vertices, subdivided by the link
vertices, and every edge joins a row to a column. An assignment of the edges has weight one
exactly when the three edges of every occurrence carry the value of its variable and every clause
has a true literal, so the contraction is the model count
(`ClauseNetwork.contraction_clauseNetwork`).
This is the network of Appendix D.2 with equality chains in place of equality trees: its
equality vertices have degree at most four (`ClauseNetwork.length_qPorts_le`), which is all that
Theorem D.1 needs, and the subdivision is built in. It does not merge repeated variables of a
clause; their edges are joined by the chain.

The tables are listed from the first `2 ^ B` numbers (`ClauseNetwork.boundedTable`), for a bound
`B` on the degrees, so that the network is computed from constant-length lists; for the clause
network of width `k` formulas, `B = max k 4` (`ClauseNetwork.clauseNetwork`).

## Main definitions

* `Cslib.Circuits.Frontier.ClauseNetwork.prev`: the previous occurrence of the same variable.
* `Cslib.Circuits.Frontier.ClauseNetwork.clausePorts`,
  `Cslib.Circuits.Frontier.ClauseNetwork.qPorts`: the ports of the clause and equality vertices.
* `Cslib.Circuits.Frontier.ClauseNetwork.network`: the network of an occurrence list.
* `Cslib.Circuits.Frontier.ClauseNetwork.clauseNetwork`: the clause network of a formula, with
  its number of rows.

## Main results

* `Cslib.Circuits.Frontier.ClauseNetwork.count_map_fst_occurrences`: a clause has as many
  occurrences as literals.
* `Cslib.Circuits.Frontier.ClauseNetwork.contraction_clauseNetwork`: the contraction is the model
  count.
* `Cslib.Circuits.Frontier.ClauseNetwork.isRowsFirstBipartite_clauseNetwork`: the bipartition.
* `Cslib.Circuits.Frontier.ClauseNetwork.maxDegree_clauseNetwork_le`: degree at most `max k 4`.
* `Cslib.Circuits.Frontier.ClauseNetwork.numEdges_clauseNetwork`,
  `Cslib.Circuits.Frontier.ClauseNetwork.length_vertices_clauseNetwork`,
  `Cslib.Circuits.Frontier.ClauseNetwork.length_table_clauseNetwork`: its size and full tables.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.2 (p. 54).
-/

public section

namespace Cslib.Circuits.Frontier.ClauseNetwork

open Cslib.Logic.PL

/-! ### Occurrences -/

private theorem count_map_fst_flatMap_zipIdx (φ : CNF ℕ) (s i : ℕ) :
    (((φ.zipIdx s).flatMap fun c => c.1.zipIdx.map fun l => (c.2, l.2, l.1)).map Prod.fst).count
        i = if s ≤ i then (φ.getD (i - s) []).length else 0 := by
  induction φ generalizing s with
  | nil => simp
  | cons c φ ih =>
    simp only [List.zipIdx_cons, List.flatMap_cons, List.map_append, List.map_map,
      List.count_append, ih]
    have hc : (c.zipIdx.map (Prod.fst ∘ fun l => (s, l.2, l.1))).count i =
        if i = s then c.length else 0 := by
      simp only [Function.comp_def, List.map_const', List.count_replicate, List.length_zipIdx]
      split_ifs <;> simp_all
    rw [hc]
    by_cases his : i = s
    · subst his
      simp
    · by_cases hsi : s ≤ i
      · have he : i - s = (i - (s + 1)) + 1 := by omega
        simp [his, hsi, show s + 1 ≤ i by omega, he]
      · simp [his, hsi, show ¬s + 1 ≤ i by omega]

/-- Clause `i` has as many occurrences as literals. -/
theorem count_map_fst_occurrences (φ : CNF ℕ) (i : ℕ) :
    ((occurrences φ).map Prod.fst).count i = (φ.getD i []).length := by
  have h := count_map_fst_flatMap_zipIdx φ 0 i
  simp only [Nat.zero_le, ite_true, Nat.sub_zero] at h
  exact h

/-! ### Occurrence data -/

variable (os : List (Occurrence ℕ))

/-- Occurrence `u`: its clause, its position in the clause and its literal, with a default past the
end. -/
@[expose] def occ (u : ℕ) : Occurrence ℕ := os.getD u (0, 0, (0, false))

/-- The variable of occurrence `u`. -/
@[expose] def var (u : ℕ) : ℕ := let (_, _, (v, _)) := occ os u; v

/-- The polarity of occurrence `u`. -/
@[expose] def pol (u : ℕ) : Bool := let (_, _, (_, b)) := occ os u; b

/-- The clause of occurrence `u`. -/
@[expose] def clauseOf (u : ℕ) : ℕ := (occ os u).1

/-- The previous occurrence of the variable of occurrence `u`, or `u` itself if there is none. -/
@[expose] def prev (u : ℕ) : ℕ :=
  ((List.range u).reverse.find? fun w => decide (var os w = var os u)).getD u

/-! ### The network -/

/-- A table of the `2 ^ w` values `f 0, …, f (2 ^ w - 1)` when `w ≤ B`, listed by keeping the
numbers below `2 ^ w` among the first `2 ^ B`. -/
@[expose] def boundedTable (B w : ℕ) (f : ℕ → ℕ) : List ℕ :=
  ((List.range (2 ^ B)).filter fun idx => idx < 2 ^ w).map f

/-- The equality tensor on `w` ports: one at the all-`false` and the all-`true` words. -/
@[expose] def eqEntry (w idx : ℕ) : ℕ := if idx = 0 ∨ idx + 1 = 2 ^ w then 1 else 0

/-- The clause tensor: zero at the one word `z` that falsifies every literal, one elsewhere. -/
@[expose] def clauseEntry (z idx : ℕ) : ℕ := if idx = z then 0 else 1

/-- The ports of clause `i`: the edges `3 u` of its occurrences `u`. -/
@[expose] def clausePorts (i : ℕ) : List ℕ :=
  ((List.range os.length).filter fun u => clauseOf os u = i).map fun u => 3 * u

/-- The ports of the equality vertex of occurrence `w`: `3 w`, `3 w + 1`, and `3 u + 2` for the
occurrences `u` whose previous occurrence is `w`. -/
@[expose] def qPorts (w : ℕ) : List ℕ :=
  [3 * w, 3 * w + 1] ++
    ((List.range os.length).filter fun u => prev os u = w).map fun u => 3 * u + 2

/-- The falsifying word of a clause vertex with the ports `ps`, as a number. -/
@[expose] def falsifier (ps : List ℕ) : ℕ := BitString.lsbValue (ps.map fun j => !pol os (j / 3))

/-- The clause vertex `i`. -/
@[expose] def clauseVertex (B i : ℕ) : List ℕ × List ℕ :=
  (clausePorts os i,
    boundedTable B (clausePorts os i).length (clauseEntry (falsifier os (clausePorts os i))))

/-- The link vertex of occurrence `u`. -/
@[expose] def linkVertex (u : ℕ) : List ℕ × List ℕ := ([3 * u + 1, 3 * u + 2], [1, 0, 0, 1])

/-- The equality vertex of occurrence `w`. -/
@[expose] def qVertex (B w : ℕ) : List ℕ × List ℕ :=
  (qPorts os w, boundedTable B (qPorts os w).length (eqEntry (qPorts os w).length))

/-- **The network of an occurrence list** with `m` clauses and degree bound `B`, with its number
of rows `m + N`: the clause vertices, the link vertices, and then the equality vertices. -/
@[expose] def network (B m : ℕ) : ℕ × ExplicitTensorNetwork ℕ :=
  (m + os.length, ⟨3 * os.length,
    (List.range m).map (clauseVertex os B) ++ (List.range os.length).map linkVertex ++
      (List.range os.length).map (qVertex os B)⟩)

/-- **The clause network** of a formula, for clause width at most `k`. -/
@[expose] def clauseNetwork (k : ℕ) (φ : CNF ℕ) : ℕ × ExplicitTensorNetwork ℕ :=
  network (occurrences φ) (max k 4) φ.length

/-! ### The occurrence data -/

theorem occ_eq_getElem {u : ℕ} (hu : u < os.length) : occ os u = os[u] :=
  List.getD_eq_getElem _ _ hu

/-- Listing the occurrences by number gives the occurrence list back. -/
theorem map_occ_range : (List.range os.length).map (occ os) = os := by
  refine List.ext_getElem (by simp) fun u h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact occ_eq_getElem os h₂

/-- The occurrence with a given number, as a member of the list. -/
theorem occ_mem {u : ℕ} (hu : u < os.length) : occ os u ∈ os := by
  rw [occ_eq_getElem os hu]
  exact List.getElem_mem hu

/-- **The previous occurrence.** Either `prev u < u` is an occurrence of the same variable with no
occurrence of that variable strictly between, or `u` is the first occurrence of its variable. -/
theorem prev_spec (u : ℕ) :
    (prev os u < u ∧ var os (prev os u) = var os u ∧
        ∀ w, prev os u < w → w < u → var os w ≠ var os u) ∨
      (prev os u = u ∧ ∀ w < u, var os w ≠ var os u) := by
  unfold prev
  cases h : (List.range u).reverse.find? fun w => decide (var os w = var os u) with
  | none =>
    right
    simp only [Option.getD_none]
    refine ⟨by simp, fun w hw => ?_⟩
    have := List.find?_eq_none.mp h w (by simpa using hw)
    simpa using this
  | some b =>
    left
    simp only [Option.getD_some]
    obtain ⟨hb, as, bs, hl, has⟩ := List.find?_eq_some_iff_append.mp h
    have hbmem : b ∈ (List.range u).reverse := by rw [hl]; simp
    have hbu : b < u := by simpa using hbmem
    refine ⟨hbu, by simpa using hb, fun w hbw hwu => ?_⟩
    have hwmem : w ∈ as ++ b :: bs := by rw [← hl]; simpa using hwu
    have hpw : List.Pairwise (fun x y => y < x) (as ++ b :: bs) := by
      rw [← hl, List.pairwise_reverse]
      exact List.pairwise_lt_range
    rcases List.mem_append.mp hwmem with hw | hw
    · simpa using has w hw
    · rcases List.mem_cons.mp hw with rfl | hw
      · omega
      · have := ((List.pairwise_append.mp hpw).2.1)
        have := (List.pairwise_cons.mp this).1 w hw
        omega

theorem prev_le (u : ℕ) : prev os u ≤ u := by
  rcases prev_spec os u with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

theorem var_prev (u : ℕ) : var os (prev os u) = var os u := by
  rcases prev_spec os u with ⟨-, h, -⟩ | ⟨h, -⟩
  · exact h
  · rw [h]

/-- Two occurrences `u < u'` whose previous occurrence is the same `w` include `w` itself. -/
theorem eq_of_prev_eq {w u u' : ℕ} (hu : prev os u = w) (hu' : prev os u' = w) (hne : u ≠ w)
    (hne' : u' ≠ w) : u = u' := by
  have key : ∀ a b, prev os a = w → prev os b = w → a ≠ w → b ≠ w → a < b → False := by
    intro a b ha hb haw hbw hab
    rcases prev_spec os a with ⟨ha1, ha2, -⟩ | ⟨ha1, -⟩
    · rcases prev_spec os b with ⟨hb1, hb2, hb3⟩ | ⟨hb1, -⟩
      · exact hb3 a (by omega) hab (by rw [← ha2, ← hb2, ha, hb])
      · omega
    · omega
  rcases lt_trichotomy u u' with h | h | h
  · exact (key u u' hu hu' hne hne' h).elim
  · exact h
  · exact (key u' u hu' hu hne' hne h).elim

/-! ### Tables -/

/-- For `w ≤ B`, the bounded table is the table of `f` on `0, …, 2 ^ w - 1`. -/
theorem boundedTable_eq {B w : ℕ} (f : ℕ → ℕ) (h : w ≤ B) :
    boundedTable B w f = (List.range (2 ^ w)).map f := by
  have hle : 2 ^ w ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) h
  unfold boundedTable
  congr 1
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  rw [hc, List.range_add, List.filter_append, List.filter_eq_self.mpr (by simp),
    List.filter_eq_nil_iff.mpr (by simp), List.append_nil]

theorem length_boundedTable {B w : ℕ} (f : ℕ → ℕ) (h : w ≤ B) :
    (boundedTable B w f).length = 2 ^ w := by
  simp [boundedTable_eq f h]

/-- Looking up a bounded table at a word of length at most `B` evaluates its function at the
value of the word. -/
theorem entry_boundedTable {B : ℕ} (f : ℕ → ℕ) {bs : List Bool} (h : bs.length ≤ B) :
    ExplicitTensorNetwork.entry (boundedTable B bs.length f) bs = f (BitString.lsbValue bs) := by
  rw [ExplicitTensorNetwork.entry, boundedTable_eq f h,
    List.getD_eq_getElem _ _ (by simpa using BitString.lsbValue_lt bs)]
  simp

private theorem eq_replicate_or_iff (bs : List Bool) :
    (bs = List.replicate bs.length false ∨ bs = List.replicate bs.length true) ↔
      ∀ a ∈ bs, ∀ b ∈ bs, a = b := by
  constructor
  · rintro (h | h) a ha b hb <;> rw [h] at ha hb <;>
      rw [List.eq_of_mem_replicate ha, List.eq_of_mem_replicate hb]
  · intro h
    cases bs with
    | nil => simp
    | cons a bs =>
      have hall : ∀ b ∈ a :: bs, b = a := fun b hb => h b hb a List.mem_cons_self
      cases a
      · exact Or.inl (List.eq_replicate_iff.mpr ⟨rfl, hall⟩)
      · exact Or.inr (List.eq_replicate_iff.mpr ⟨rfl, hall⟩)

/-- The equality tensor at a word: one exactly when all its bits are equal. -/
theorem eqEntry_lsbValue (bs : List Bool) :
    eqEntry bs.length (BitString.lsbValue bs) = if ∀ a ∈ bs, ∀ b ∈ bs, a = b then 1 else 0 := by
  have h0 : BitString.lsbValue bs = 0 ↔ bs = List.replicate bs.length false := by
    constructor
    · intro h
      exact BitString.lsbValue_injective (by simp) (by simp [h])
    · intro h
      rw [h, BitString.lsbValue_replicate_false]
  have h1 : BitString.lsbValue bs + 1 = 2 ^ bs.length ↔ bs = List.replicate bs.length true := by
    have hr := BitString.lsbValue_replicate_true bs.length
    constructor
    · intro h
      exact BitString.lsbValue_injective (by simp) (by omega)
    · intro h
      rw [h]
      simpa using hr
  unfold eqEntry
  simp only [h0, h1, eq_replicate_or_iff]

/-- The clause tensor at a word of the length of its falsifying word: zero exactly at that
word. -/
theorem clauseEntry_lsbValue {bs zs : List Bool} (h : bs.length = zs.length) :
    clauseEntry (BitString.lsbValue zs) (BitString.lsbValue bs) = if bs = zs then 0 else 1 := by
  unfold clauseEntry
  congr 1
  exact propext ⟨BitString.lsbValue_injective h, fun h => h ▸ rfl⟩

/-! ### Ports -/

variable {os}

theorem mem_clausePorts {i j : ℕ} :
    j ∈ clausePorts os i ↔ ∃ u < os.length, clauseOf os u = i ∧ 3 * u = j := by
  simp [clausePorts, and_assoc]

theorem nodup_clausePorts (i : ℕ) : (clausePorts os i).Nodup :=
  (List.nodup_range.filter _).map fun _ _ h => by omega

theorem mem_qPorts {w j : ℕ} :
    j ∈ qPorts os w ↔
      j = 3 * w ∨ j = 3 * w + 1 ∨ ∃ u < os.length, prev os u = w ∧ 3 * u + 2 = j := by
  simp [qPorts, and_assoc]

theorem nodup_qPorts (w : ℕ) : (qPorts os w).Nodup := by
  unfold qPorts
  refine List.Nodup.append (by simp) ((List.nodup_range.filter _).map fun _ _ h => by omega) ?_
  intro a ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hb
  omega

/-- The number of ports of clause `i` is its number of occurrences. -/
theorem length_clausePorts (i : ℕ) :
    (clausePorts os i).length = (os.map Prod.fst).count i := by
  rw [clausePorts, List.length_map, ← List.countP_eq_length_filter, List.count]
  conv_rhs => rw [← map_occ_range os]
  rw [List.map_map, List.countP_map]
  congr 1

/-- An equality vertex has at most four ports. -/
theorem length_qPorts_le (w : ℕ) : (qPorts os w).length ≤ 4 := by
  classical
  have hnd : ((List.range os.length).filter fun u => prev os u = w).Nodup :=
    List.nodup_range.filter _
  set l := (List.range os.length).filter fun u => prev os u = w
  have hsplit : l.toFinset ⊆ {w} ∪ (l.toFinset.filter fun u => u ≠ w) := by
    intro u hu
    by_cases h : u = w
    · simp [h]
    · simp [hu, h]
  have hcard : (l.toFinset.filter fun u => u ≠ w).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    simp only [Finset.mem_filter, List.mem_toFinset, l, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at ha hb
    exact eq_of_prev_eq os ha.1.2 hb.1.2 ha.2 hb.2
  have hl : l.length ≤ 2 := by
    rw [← List.toFinset_card_of_nodup hnd]
    calc l.toFinset.card ≤ ({w} ∪ (l.toFinset.filter fun u => u ≠ w)).card :=
          Finset.card_le_card hsplit
      _ ≤ ({w} : Finset ℕ).card + (l.toFinset.filter fun u => u ≠ w).card :=
          Finset.card_union_le _ _
      _ ≤ 2 := by simp only [Finset.card_singleton]; omega
  have hq : (qPorts os w).length = 2 + l.length := by
    simp only [qPorts, l, List.length_append, List.length_cons, List.length_nil, List.length_map]
  omega

/-! ### The network: sizes and bipartition -/

variable (os)

@[simp] theorem fst_network (B m : ℕ) : (network os B m).1 = m + os.length := rfl

@[simp] theorem numEdges_network (B m : ℕ) : (network os B m).2.numEdges = 3 * os.length := rfl

theorem vertices_network (B m : ℕ) : (network os B m).2.vertices =
    (List.range m).map (clauseVertex os B) ++ (List.range os.length).map linkVertex ++
      (List.range os.length).map (qVertex os B) := rfl

@[simp] theorem length_vertices_network (B m : ℕ) :
    (network os B m).2.vertices.length = m + 2 * os.length := by
  simp only [vertices_network, List.length_append, List.length_map, List.length_range]
  omega

private theorem sum_range_ite (m a : ℕ) (c : Prop) [Decidable c] :
    ((List.range m).map fun i => if c ∧ a = i then 1 else 0).sum = if c ∧ a < m then 1 else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    by_cases hc : c
    · rcases lt_trichotomy a m with h | rfl | h
      · simp [hc, h, Nat.lt_succ_of_lt h, h.ne]
      · simp [hc]
      · simp [hc, show ¬ a < m by omega, show ¬ a < m + 1 by omega, show a ≠ m by omega]
    · simp [hc]

private theorem sum_range_ite' (m a : ℕ) :
    ((List.range m).map fun i => if a = i then 1 else 0).sum = if a < m then 1 else 0 := by
  simpa using sum_range_ite m a True

private theorem count_clausePorts (i j : ℕ) :
    (clausePorts os i).count j =
      if (j % 3 = 0 ∧ j / 3 < os.length) ∧ clauseOf os (j / 3) = i then 1 else 0 := by
  rw [List.Nodup.count (nodup_clausePorts i)]
  have key : j ∈ clausePorts os i ↔
      (j % 3 = 0 ∧ j / 3 < os.length) ∧ clauseOf os (j / 3) = i := by
    rw [mem_clausePorts]
    constructor
    · rintro ⟨u, hu, rfl, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [show 3 * u / 3 = u by omega]
    · rintro ⟨⟨h0, hlt⟩, rfl⟩
      exact ⟨j / 3, hlt, rfl, by omega⟩
  by_cases h : (j % 3 = 0 ∧ j / 3 < os.length) ∧ clauseOf os (j / 3) = i <;> simp [h, key]

private theorem count_link (u j : ℕ) :
    (linkVertex u).1.count j = if (j % 3 ≠ 0) ∧ j / 3 = u then 1 else 0 := by
  rw [List.Nodup.count (by simp [linkVertex])]
  have key : j ∈ (linkVertex u).1 ↔ (j % 3 ≠ 0) ∧ j / 3 = u := by
    simp only [linkVertex, List.mem_cons, List.not_mem_nil, or_false]
    omega
  by_cases h : (j % 3 ≠ 0) ∧ j / 3 = u <;> simp [h, key]

private theorem count_qPorts (w j : ℕ) :
    (qPorts os w).count j =
      if (j < 3 * os.length) ∧ (if j % 3 = 2 then prev os (j / 3) else j / 3) = w then 1 else 0
      + if (3 * os.length ≤ j) ∧ (j = 3 * w ∨ j = 3 * w + 1) then 1 else 0 := by
  rw [List.Nodup.count (nodup_qPorts w)]
  have key : j ∈ qPorts os w ↔
      ((j < 3 * os.length) ∧ (if j % 3 = 2 then prev os (j / 3) else j / 3) = w) ∨
        ((3 * os.length ≤ j) ∧ (j = 3 * w ∨ j = 3 * w + 1)) := by
    rw [mem_qPorts]
    constructor
    · rintro (rfl | rfl | ⟨u, hu, rfl, rfl⟩)
      · by_cases hw : 3 * w < 3 * os.length
        · left
          simp [hw]
        · right
          omega
      · by_cases hw : 3 * w + 1 < 3 * os.length
        · left
          simp [hw, show (3 * w + 1) / 3 = w by omega]
        · right
          omega
      · left
        simp [show 3 * u + 2 < 3 * os.length by omega, show (3 * u + 2) % 3 = 2 by omega,
          show (3 * u + 2) / 3 = u by omega]
    · rintro (⟨hj, h⟩ | ⟨-, h⟩)
      · split_ifs at h with h2
        · exact Or.inr (Or.inr ⟨j / 3, by omega, h, by omega⟩)
        · subst h
          omega
      · omega
  by_cases h1 : (j < 3 * os.length) ∧ (if j % 3 = 2 then prev os (j / 3) else j / 3) = w
  · have h2 : ¬ ((3 * os.length ≤ j) ∧ (j = 3 * w ∨ j = 3 * w + 1)) := fun h => by omega
    simp [key, h1, h2]
  · by_cases h2 : (3 * os.length ≤ j) ∧ (j = 3 * w ∨ j = 3 * w + 1) <;> simp [key, h1, h2]

/-- **The network is rows-first bipartite** when every occurrence names one of the `m`
clauses. -/
theorem isRowsFirstBipartite_network (B m : ℕ) (hcl : ∀ o ∈ os, o.1 < m) :
    (network os B m).2.IsRowsFirstBipartite (network os B m).1 := by
  have hcl' : ∀ u < os.length, clauseOf os u < m := fun u hu => hcl _ (occ_mem os hu)
  refine ⟨?_, fun j hj => ⟨?_, ?_⟩⟩
  · intro v hv i hi
    simp only [vertices_network, List.mem_append, List.mem_map, List.mem_range] at hv
    rcases hv with (⟨i', -, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨w, hw, rfl⟩
    · obtain ⟨u, hu, -, rfl⟩ := mem_clausePorts.mp hi
      simp only [numEdges_network]
      omega
    · simp only [linkVertex, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [numEdges_network]
      omega
    · rcases mem_qPorts.mp hi with rfl | rfl | ⟨u, hu, -, rfl⟩ <;> simp only [numEdges_network] <;>
        omega
  · simp only [numEdges_network] at hj
    rw [fst_network, vertices_network, List.take_left' (by simp), List.map_append,
      List.sum_append, List.map_map, List.map_map]
    simp only [Function.comp_def, clauseVertex, count_clausePorts, count_link]
    rw [sum_range_ite, sum_range_ite]
    by_cases h0 : j % 3 = 0
    · simp [h0, hcl' (j / 3) (by omega), show j / 3 < os.length by omega]
    · simp [h0, show j / 3 < os.length by omega]
  · simp only [numEdges_network] at hj
    rw [fst_network, vertices_network, List.drop_left' (by simp), List.map_map]
    simp only [Function.comp_def, qVertex, count_qPorts, hj, true_and, show ¬ 3 * os.length ≤ j by
      omega, false_and, ite_false, Nat.add_zero]
    rw [sum_range_ite']
    have : (if j % 3 = 2 then prev os (j / 3) else j / 3) < os.length := by
      split_ifs
      · exact (prev_le os _).trans_lt (by omega)
      · omega
    simp [this]

/-! ### Degrees -/

/-- **The degree bound**: if every clause has at most `B` occurrences, every vertex has at most
`max B 4` ports. -/
theorem maxDegree_network_le (B m : ℕ) (hB : ∀ i, (os.map Prod.fst).count i ≤ B) :
    (network os (max B 4) m).2.maxDegree ≤ max B 4 := by
  refine (ExplicitTensorNetwork.maxDegree_le_iff _).mpr fun v hv => ?_
  simp only [vertices_network, List.mem_append, List.mem_map, List.mem_range] at hv
  rcases hv with (⟨i, -, rfl⟩ | ⟨u, -, rfl⟩) | ⟨w, -, rfl⟩
  · simp only [clauseVertex, length_clausePorts]
    exact (hB i).trans (le_max_left _ _)
  · simp [linkVertex]
  · exact (length_qPorts_le w).trans (le_max_right _ _)

/-- **Full tables**: under the degree bound, every table lists `2 ^ (number of ports)` values. -/
theorem length_table_network (B m : ℕ) (hB : ∀ i, (os.map Prod.fst).count i ≤ B) :
    ∀ v ∈ (network os (max B 4) m).2.vertices, v.2.length = 2 ^ v.1.length := by
  intro v hv
  have hdeg := (network os (max B 4) m).2.length_le_maxDegree hv
  have hmax := maxDegree_network_le os B m hB
  simp only [vertices_network, List.mem_append, List.mem_map, List.mem_range] at hv
  rcases hv with (⟨i, -, rfl⟩ | ⟨u, -, rfl⟩) | ⟨w, -, rfl⟩
  · exact length_boundedTable _ (hdeg.trans hmax)
  · rfl
  · exact length_boundedTable _ (hdeg.trans hmax)

/-! ### The contraction -/

private theorem prod_map_boole {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.map fun a => if p a then (1 : ℕ) else 0).prod = if ∀ a ∈ l, p a then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    by_cases ha : p a <;> simp [ha]

/-- The bits on the edges, read as a function of the edge numbers. -/
private def bitAt {E : ℕ} (x : Fin E → Bool) (j : ℕ) : Bool := if h : j < E then x ⟨j, h⟩ else false

/-- The weight conditions of an assignment: every clause has an edge differing from its falsifying
word, every link vertex sees equal bits, and every equality vertex sees equal bits. -/
private def Good (m : ℕ) (X : ℕ → Bool) : Prop :=
  (∀ i < m, ¬ ∀ j ∈ clausePorts os i, X j = !pol os (j / 3)) ∧
    (∀ u < os.length, X (3 * u + 1) = X (3 * u + 2)) ∧
    ∀ w < os.length, ∀ a ∈ qPorts os w, ∀ b ∈ qPorts os w, X a = X b

private instance (m : ℕ) (X : ℕ → Bool) : Decidable (Good os m X) := by
  unfold Good
  infer_instance

/-- The entry of a clause vertex: one exactly when some port differs from the falsifying word. -/
private theorem entry_clauseVertex {B i : ℕ} (X : ℕ → Bool) (h : (clausePorts os i).length ≤ B) :
    ExplicitTensorNetwork.entry (clauseVertex os B i).2 ((clauseVertex os B i).1.map X) =
      if ¬ ∀ j ∈ clausePorts os i, X j = !pol os (j / 3) then 1 else 0 := by
  simp only [clauseVertex]
  rw [show (clausePorts os i).length = ((clausePorts os i).map X).length by simp,
    entry_boundedTable _ (by simpa using h), falsifier, clauseEntry_lsbValue (by simp)]
  simp only [List.map_inj_left]
  by_cases hc : ∀ j ∈ clausePorts os i, X j = !pol os (j / 3)
  · simp only [eq_true hc, not_true_eq_false, ite_true, ite_false]
  · simp only [eq_false hc, not_false_eq_true, ite_true, ite_false]

private theorem entry_linkVertex (u : ℕ) (X : ℕ → Bool) :
    ExplicitTensorNetwork.entry (linkVertex u).2 ((linkVertex u).1.map X) =
      if X (3 * u + 1) = X (3 * u + 2) then 1 else 0 := by
  simp only [linkVertex, List.map_cons, List.map_nil, ExplicitTensorNetwork.entry,
    BitString.lsbValue]
  cases X (3 * u + 1) <;> cases X (3 * u + 2) <;> rfl

private theorem entry_qVertex {B w : ℕ} (X : ℕ → Bool) (h : (qPorts os w).length ≤ B) :
    ExplicitTensorNetwork.entry (qVertex os B w).2 ((qVertex os B w).1.map X) =
      if ∀ a ∈ qPorts os w, ∀ b ∈ qPorts os w, X a = X b then 1 else 0 := by
  simp only [qVertex]
  rw [show (qPorts os w).length = ((qPorts os w).map X).length by simp,
    entry_boundedTable _ (by simpa using h), eqEntry_lsbValue]
  simp

/-- The contraction counts the assignments satisfying the weight conditions. -/
private theorem contraction_network_eq (B m : ℕ) (hB : ∀ i, (os.map Prod.fst).count i ≤ B) :
    (network os (max B 4) m).2.contraction =
      (Finset.univ.filter fun x : Fin (3 * os.length) → Bool => Good os m (bitAt x)).card := by
  rw [ExplicitTensorNetwork.contraction, ← Nat.cast_id (Finset.card _), ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hpb : ∀ ps : List ℕ, (network os (max B 4) m).2.portBits x ps = ps.map (bitAt x) :=
    fun _ => rfl
  simp only [hpb]
  rw [vertices_network, List.map_append, List.map_append, List.prod_append, List.prod_append,
    List.map_map, List.map_map, List.map_map]
  have h1 : (List.range m).map ((fun v => ExplicitTensorNetwork.entry v.2 (v.1.map (bitAt x))) ∘
      clauseVertex os (max B 4)) = (List.range m).map fun i =>
        if ¬ ∀ j ∈ clausePorts os i, bitAt x j = !pol os (j / 3) then 1 else 0 :=
    List.map_congr_left fun i _ => entry_clauseVertex os (bitAt x)
      ((length_clausePorts i).trans_le ((hB i).trans (le_max_left _ _)))
  have h2 : (List.range os.length).map ((fun v => ExplicitTensorNetwork.entry v.2
      (v.1.map (bitAt x))) ∘ linkVertex) = (List.range os.length).map fun u =>
        if bitAt x (3 * u + 1) = bitAt x (3 * u + 2) then 1 else 0 :=
    List.map_congr_left fun u _ => entry_linkVertex u (bitAt x)
  have h3 : (List.range os.length).map ((fun v => ExplicitTensorNetwork.entry v.2
      (v.1.map (bitAt x))) ∘ qVertex os (max B 4)) = (List.range os.length).map fun w =>
        if ∀ a ∈ qPorts os w, ∀ b ∈ qPorts os w, bitAt x a = bitAt x b then 1 else 0 :=
    List.map_congr_left fun w _ => entry_qVertex os (bitAt x)
      ((length_qPorts_le w).trans (le_max_right _ _))
  rw [h1, h2, h3, prod_map_boole, prod_map_boole, prod_map_boole]
  clear h1 h2 h3 hpb
  simp only [List.mem_range, Good]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- Under the weight conditions, the three edges of an occurrence carry equal bits, equal to the
bit on the clause edge of the previous occurrence. -/
private theorem consistent_of_good {m : ℕ} {X : ℕ → Bool} (h : Good os m X) {u : ℕ}
    (hu : u < os.length) :
    X (3 * u) = X (3 * u + 1) ∧ X (3 * u + 1) = X (3 * u + 2) ∧
      X (3 * u + 2) = X (3 * prev os u) := by
  obtain ⟨-, hlink, hq⟩ := h
  refine ⟨hq u hu _ (by simp [qPorts]) _ (by simp [qPorts]), hlink u hu, ?_⟩
  exact hq (prev os u) ((prev_le os u).trans_lt hu) _
    (mem_qPorts.mpr (Or.inr (Or.inr ⟨u, hu, rfl, rfl⟩))) _ (mem_qPorts.mpr (Or.inl rfl))

/-- Under the weight conditions, occurrences of the same variable carry equal bits on their
clause edges. -/
private theorem eq_of_var_eq {m : ℕ} {X : ℕ → Bool} (h : Good os m X) {u w : ℕ}
    (hu : u < os.length) (hw : w < os.length) (huw : var os u = var os w) :
    X (3 * u) = X (3 * w) := by
  have key : ∀ w, w < os.length → ∀ u ≤ w, var os u = var os w → X (3 * u) = X (3 * w) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw u huw hv
      rcases Nat.eq_or_lt_of_le huw with rfl | hlt
      · rfl
      rcases prev_spec os w with ⟨hp, hpv, hbetween⟩ | ⟨-, hfirst⟩
      · have hup : u ≤ prev os w := by
          by_contra hc
          exact hbetween u (by omega) hlt hv
        obtain ⟨h1, h2, h3⟩ := consistent_of_good os h hw
        rw [ih (prev os w) hp (by omega) u hup (by rw [hv, hpv]), h1, h2, h3]
      · exact (hfirst u hlt hv).elim
  rcases le_total u w with h' | h'
  · exact key w hw u h' huw
  · exact (key u hu w h' huw.symm).symm

private theorem bitAt_eq {E : ℕ} (x : Fin E → Bool) {j : ℕ} (hj : j < E) :
    bitAt x j = x ⟨j, hj⟩ := by
  simp [bitAt, hj]

variable {φ : CNF ℕ}

private theorem var_mem_vars {u : ℕ} (hu : u < (occurrences φ).length) :
    var (occurrences φ) u ∈ φ.vars := by
  rw [← map_occurrences]
  exact List.mem_map.mpr ⟨_, occ_mem _ hu, rfl⟩

private theorem exists_var_eq {v : ℕ} (hv : v ∈ φ.vars) :
    ∃ u < (occurrences φ).length, var (occurrences φ) u = v := by
  rw [← map_occurrences] at hv
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv
  obtain ⟨u, hu, rfl⟩ := List.mem_iff_getElem.mp ho
  exact ⟨u, hu, by simp [var, occ_eq_getElem _ hu]⟩

/-- An occurrence names a clause and one of its literals. -/
private theorem mem_of_occ {u : ℕ} (hu : u < (occurrences φ).length) :
    ∃ h : clauseOf (occurrences φ) u < φ.length,
      (occ (occurrences φ) u).2.2 ∈ φ[clauseOf (occurrences φ) u] := by
  obtain ⟨h₁, h₂, h₃⟩ := mem_occurrences.mp (occ_mem _ hu)
  exact ⟨h₁, by rw [h₃]; exact List.getElem_mem h₂⟩

/-- Every literal of a clause is an occurrence. -/
private theorem exists_occ {i : ℕ} (hi : i < φ.length) {l : Literal ℕ} (hl : l ∈ φ[i]) :
    ∃ u < (occurrences φ).length, clauseOf (occurrences φ) u = i ∧
      (occ (occurrences φ) u).2.2 = l := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hl
  obtain ⟨u, hu, hou⟩ := List.mem_iff_getElem.mp
    ((mem_occurrences (φ := φ) (o := (i, j, φ[i][j]))).mpr ⟨hi, hj, rfl⟩)
  exact ⟨u, hu, by simp [clauseOf, occ_eq_getElem _ hu, hou],
    by simp [occ_eq_getElem _ hu, hou]⟩

/-- **The weight conditions describe the satisfying assignments**: an assignment of the edges has
weight one exactly when it puts on the three edges of every occurrence the value of its variable
under a satisfying assignment. -/
private theorem good_iff
    (hmem₁ : ∀ u < os.length, ∃ h : clauseOf os u < φ.length, (occ os u).2.2 ∈ φ[clauseOf os u])
    (hmem₂ : ∀ i (hi : i < φ.length), ∀ l ∈ φ[i],
      ∃ u < os.length, clauseOf os u = i ∧ (occ os u).2.2 = l)
    (x : Fin (3 * os.length) → Bool) :
    Good os φ.length (bitAt x) ↔
      ∃ σ : ℕ → Bool, φ.eval σ = true ∧ (fun j => σ (var os (j.val / 3))) = x := by
  constructor
  · intro h
    have hvs : ∀ u < os.length, (os.map fun o => o.2.2.1).idxOf (var os u) < os.length ∧
        var os ((os.map fun o => o.2.2.1).idxOf (var os u)) = var os u := by
      intro u hu
      have hm : var os u ∈ os.map fun o => o.2.2.1 := List.mem_map.mpr ⟨_, occ_mem os hu, rfl⟩
      have hlt := List.idxOf_lt_length_of_mem hm
      have h1 := List.getElem_idxOf hlt
      rw [List.length_map] at hlt
      refine ⟨hlt, ?_⟩
      rw [List.getElem_map] at h1
      rw [var, occ_eq_getElem os hlt]
      exact h1
    have hrep : ∀ u < os.length,
        bitAt x (3 * (os.map fun o => o.2.2.1).idxOf (var os u)) = bitAt x (3 * u) :=
      fun u hu => eq_of_var_eq os h (hvs u hu).1 hu (hvs u hu).2
    refine ⟨fun v => bitAt x (3 * (os.map fun o => o.2.2.1).idxOf v), ?_, ?_⟩
    · rw [CNF.eval_eq_true_iff]
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
      have hcl := h.1 i hi
      simp only [not_forall] at hcl
      obtain ⟨j, hj, hne⟩ := hcl
      obtain ⟨u, hu, hci, rfl⟩ := mem_clausePorts.mp hj
      rw [show 3 * u / 3 = u by omega] at hne
      have hpol : bitAt x (3 * u) = pol os u := by
        revert hne
        cases bitAt x (3 * u) <;> cases pol os u <;> simp
      subst hci
      obtain ⟨_, hocc⟩ := hmem₁ u hu
      rw [Clause.eval_eq_true_iff]
      exact ⟨_, hocc, (hrep u hu).trans hpol⟩
    · funext j
      have hj := j.isLt
      have hu : j.val / 3 < os.length := by omega
      change bitAt x (3 * (os.map fun o => o.2.2.1).idxOf (var os (j.val / 3))) = x j
      rw [hrep _ hu, ← bitAt_eq x hj]
      obtain ⟨h1, h2, -⟩ := consistent_of_good os h hu
      have hcases : j.val = 3 * (j.val / 3) ∨ j.val = 3 * (j.val / 3) + 1 ∨
          j.val = 3 * (j.val / 3) + 2 := by omega
      rcases hcases with h' | h' | h'
      · rw [← h']
      · rw [h1, ← h']
      · rw [h1, h2, ← h']
  · rintro ⟨σ, hσ, rfl⟩
    have hX : ∀ j < 3 * os.length, bitAt (fun j : Fin (3 * os.length) =>
        σ (var os (j.val / 3))) j = σ (var os (j / 3)) := fun j hj => bitAt_eq _ hj
    refine ⟨fun i hi hall => ?_, fun u hu => ?_, fun w hw a ha b hb => ?_⟩
    · have hc := (CNF.eval_eq_true_iff σ φ).mp hσ _ (List.getElem_mem hi)
      obtain ⟨l, hl, hsl⟩ := (Clause.eval_eq_true_iff σ _).mp hc
      obtain ⟨u, hu, hci, hocc⟩ := hmem₂ i hi l hl
      have h3u : 3 * u ∈ clausePorts os i := mem_clausePorts.mpr ⟨u, hu, hci, rfl⟩
      have := hall _ h3u
      rw [hX _ (by omega), show 3 * u / 3 = u by omega] at this
      have hv : var os u = l.1 := congrArg Prod.fst hocc
      have hp : pol os u = l.2 := congrArg Prod.snd hocc
      rw [hv, hp, hsl] at this
      cases l.2 <;> simp at this
    · rw [hX _ (by omega), hX _ (by omega), show (3 * u + 1) / 3 = u by omega,
        show (3 * u + 2) / 3 = u by omega]
    · have hval : ∀ c ∈ qPorts os w, bitAt (fun j : Fin (3 * os.length) =>
          σ (var os (j.val / 3))) c = σ (var os w) := by
        intro c hc
        rcases mem_qPorts.mp hc with rfl | rfl | ⟨u, hu, hpu, rfl⟩
        · rw [hX _ (by omega), show 3 * w / 3 = w by omega]
        · rw [hX _ (by omega), show (3 * w + 1) / 3 = w by omega]
        · rw [hX _ (by omega), show (3 * u + 2) / 3 = u by omega, ← hpu, var_prev]
      rw [hval a ha, hval b hb]

/-- **The contraction of the clause network is the model count**, for formulas whose clauses have
at most `k` literals. -/
theorem contraction_clauseNetwork {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k) :
    (clauseNetwork k φ).2.contraction = φ.modelCount := by
  have hB : ∀ i, ((occurrences φ).map Prod.fst).count i ≤ k := by
    intro i
    rw [count_map_fst_occurrences]
    by_cases hi : i < φ.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hk _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.zero_le _
  rw [clauseNetwork, contraction_network_eq _ k _ hB]
  symm
  refine CNF.modelCount_eq_card_filter (fun σ (j : Fin (3 * (occurrences φ).length)) =>
    σ (var (occurrences φ) (j.val / 3))) _ (fun σ τ _ _ => ?_)
      fun x => good_iff _ (fun _ => mem_of_occ) (fun _ => exists_occ) x
  constructor
  · intro h v hv
    obtain ⟨u, hu, rfl⟩ := exists_var_eq hv
    have := congrFun h ⟨3 * u, by omega⟩
    simpa [show 3 * u / 3 = u by omega] using this
  · intro h
    funext j
    exact h _ (var_mem_vars (by have := j.isLt; omega))


/-- **The clause network is rows-first bipartite.** -/
theorem isRowsFirstBipartite_clauseNetwork (k : ℕ) (φ : CNF ℕ) :
    (clauseNetwork k φ).2.IsRowsFirstBipartite (clauseNetwork k φ).1 :=
  isRowsFirstBipartite_network _ _ _ fun _ ho => (mem_occurrences.mp ho).1

private theorem count_le_of_width {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k) (i : ℕ) :
    ((occurrences φ).map Prod.fst).count i ≤ k := by
  rw [count_map_fst_occurrences]
  by_cases hi : i < φ.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hk _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

/-- **The degree bound**: for clauses of at most `k` literals, every vertex has at most `max k 4`
ports. -/
theorem maxDegree_clauseNetwork_le {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k) :
    (clauseNetwork k φ).2.maxDegree ≤ max k 4 :=
  maxDegree_network_le _ k _ (count_le_of_width hk)

/-- **Full tables**, for clauses of at most `k` literals. -/
theorem length_table_clauseNetwork {k : ℕ} (hk : ∀ c ∈ φ, c.length ≤ k) :
    ∀ v ∈ (clauseNetwork k φ).2.vertices, v.2.length = 2 ^ v.1.length :=
  length_table_network _ k _ (count_le_of_width hk)

/-- The clause network has three edges per literal occurrence. -/
theorem numEdges_clauseNetwork (k : ℕ) (φ : CNF ℕ) :
    (clauseNetwork k φ).2.numEdges = 3 * φ.vars.length := by
  rw [← length_occurrences]
  rfl

/-- The clause network has one vertex per clause and two per literal occurrence. -/
theorem length_vertices_clauseNetwork (k : ℕ) (φ : CNF ℕ) :
    (clauseNetwork k φ).2.vertices.length = φ.length + 2 * φ.vars.length := by
  rw [← length_occurrences, clauseNetwork, length_vertices_network]

end Cslib.Circuits.Frontier.ClauseNetwork
