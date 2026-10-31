/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.FastContractionSchedule
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeChildPolyTime
import Mathlib.Data.List.GetD

/-!
# The shapes of the calls of the native contraction recursion

Structural bounds on every call reached from a root of the native recursion
(`FastContraction.scheme FastContraction.nativeMk`) with `m` edges, valid for every input, whatever
the schedule: they are what makes the calls, frames and values polynomially long.

**The invariant** (`FastContraction.Shape`). A reached call at depth `d` keeps the root's scale and
modulus, is well-formed, has at most `2 m` edges, precision at most `p₀ + 40 m² d` for the root's
precision `p₀`, at most `V₀ + m² d` vertices for the root's `V₀` vertices, as many rows (unless it
is the root), and every vertex descriptor is a table of the root or a packet descriptor whose fields
are bounded (`FastContraction.PacketBound`). It passes to the native children
(`FastContraction.Shape.child`): a child has at most twice the edges of its parent
(`NativeChild.numEdges_nativeChild_le`), its precision `p_t = p + 8 h 2 ^ (a - i) + 8 M (a + 1)` is
at most `p + 40 m²` since `2 ^ a ≤ m`, and it adds at most `M (2 ^ a) ^ 12 ≤ m²` packet vertices
(`NativeChild.numPackets_nativeParentPacking_le`).

## Main definitions

* `Cslib.Circuits.Frontier.FastContraction.PacketBound`: the bounded packet descriptors.
* `Cslib.Circuits.Frontier.FastContraction.Shape`: the invariant.

## Main results

* `Cslib.Circuits.Frontier.FastContraction.Shape.child`: the invariant passes to the native
  children.
* `Cslib.Circuits.Frontier.FastContraction.Reach.shape`: every reached call satisfies it.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6–§D.4.7 (pp. 63–64).
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction

open ContractionSchedule ChildCursor NativeRecovery NativeChild

/-- **A bounded packet descriptor** for a root with modulus `fl` and `m` edges, at precision at most
`P`, on a vertex with `k` ports: its precision is at most `P` and is its number of exponents per
tile, its modulus is `fl`, it has `2 ^ a` slots with `a ≤ ⌊log₂ m⌋`, `2 ^ (i + 1)` tiles with
`i ≤ a`, a grid point of size at most `2 ^ a`, no column list, a 0/1 interpolation value with at
most `e` coordinates, `k` tags with slots below `2 ^ a`, and at most `2 ^ (i + 1) p` exponents, each
at most `p`. -/
@[expose] def PacketBound (fl : List ℕ) (m P k : ℕ) (d : NativePacket.PacketDesc) : Prop :=
  d.1.p ≤ P ∧ d.1.nb = d.1.p ∧ d.1.fl = fl ∧ d.1.a ≤ Nat.log 2 m ∧ d.1.L = 2 ^ d.1.a ∧
    d.1.i ≤ d.1.a ∧ d.1.tiles = 2 ^ (d.1.i + 1) ∧ d.1.t.natAbs ≤ 2 ^ d.1.a ∧ d.1.cols = [] ∧
    d.1.ζ.length ≤ fl.length ∧ (∀ z ∈ d.1.ζ, z ≤ 1) ∧ d.2.1.length = k ∧
    (∀ b ∈ d.2.1, b.2 < 2 ^ d.1.a) ∧ d.2.2.length ≤ d.1.tiles * d.1.p ∧ ∀ b ∈ d.2.2, b ≤ d.1.p

theorem PacketBound.mono {fl : List ℕ} {m P P' k : ℕ} {d : NativePacket.PacketDesc}
    (h : PacketBound fl m P k d) (hP : P ≤ P') : PacketBound fl m P' k d :=
  ⟨h.1.trans hP, h.2⟩

/-- **The shape of a call** reached from a root `x₀` with `m` edges, precision `p₀` and `V₀`
vertices, at depth `d`. -/
structure Shape (x₀ x : Call) : Prop where
  /-- The scale is the root's. -/
  scale_eq : x.scale = x₀.scale
  /-- The modulus is the root's. -/
  fl_eq : x.fl = x₀.fl
  /-- The call is well-formed. -/
  wf : WF x
  /-- The bound plus the depth does not exceed the root's. -/
  bound_add_depth_le : x.bound + x.depth ≤ x₀.bound + x₀.depth
  /-- At most twice the root's number of edges. -/
  edges_le : x.edges ≤ 2 * x₀.edges
  /-- The precision grows by at most `40 m²` per level. -/
  prec_le : x.prec ≤ x₀.prec + x.depth * (40 * x₀.edges ^ 2)
  /-- The vertices grow by at most `m²` per level. -/
  vertices_le : x.net.vertices.length ≤ x₀.net.vertices.length + x.depth * x₀.edges ^ 2
  /-- The rows are the root's or at most the vertices of a parent. -/
  rows_le : x = x₀ ∨ x.rows ≤ x₀.net.vertices.length + x.depth * x₀.edges ^ 2
  /-- Every descriptor is a descriptor of the root or a bounded packet descriptor. -/
  desc : ∀ v ∈ x.net.vertices, (∃ w ∈ x₀.net.vertices, v.2 = w.2) ∨
    ∃ d, v.2 = .inr d ∧
      PacketBound x₀.fl x₀.edges (x₀.prec + x.depth * (40 * x₀.edges ^ 2)) v.1.length d

/-- The exponent tuple of a child of an active call has entries below the node's precision. -/
theorem lt_nodePrec_of_mem_children {x : Call} {c : State} (hc : c ∈ children x) :
    ∀ b ∈ c.2.2.1, b < nodePrec x c.1 := by
  simp only [children, cursorList, nodeBlock, pointBlock, groupBlock, List.mem_flatMap,
    List.mem_range, List.mem_map] at hc
  obtain ⟨j, -, i, -, β, hβ, g, -, rfl⟩ := hc
  exact fun b hb => BudgetTuples.lt_of_mem_budgetTuples (weights_pos j) hβ hb

/-- The ports of a vertex of a well-formed call are at most its edges. -/
theorem length_le_edges_of_wf {x : Call} (hx : WF x) {v : List ℕ × VertexDesc}
    (hv : v ∈ x.net.vertices) : v.1.length ≤ x.edges := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
  have hnd : (x.net.vertices[k]).1.Nodup := nodup_ports hx.2 ⟨k, hk⟩
  have hsub : (x.net.vertices[k]).1.toFinset ⊆ Finset.range x.edges := fun j hj =>
    Finset.mem_range.mpr (hx.2.1 _ (List.getElem_mem hk) j (List.mem_toFinset.mp hj))
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at this
  simpa using this

section Child

variable {x₀ x : Call}

/-- The schedule's numbers at an active call at scale `m`: `a ≤ ⌊log₂ m⌋`, `2 ^ (12 a) ≤ m`,
`u ≤ ⌊log₂ m⌋ < m`, and `h ≤ 3 M + u`. -/
theorem slots_facts (ha : active x = true) :
    slots x ≤ Nat.log 2 x.scale ∧ (2 ^ slots x) ^ 12 ≤ x.scale ∧ 2 ^ slots x ≤ x.scale ∧
      levels x ≤ Nat.log 2 x.scale ∧ Nat.log 2 x.scale < x.scale ∧
      step x ≤ 3 * x.edges + levels x := by
  have ha' := ha
  simp only [active, decide_eq_true_eq] at ha'
  obtain ⟨-, hu, -, -, -, -, -⟩ := ha'
  set L := Nat.log 2 x.scale
  have hL1 : 1 ≤ L := by
    have : levels x = L / 2 ^ (17 + x.depth) := rfl
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [this, h0, Nat.zero_div] at hu; omega
    · exact h0
  have hs0 : x.scale ≠ 0 := by
    intro h0; simp only [L, h0, Nat.log_zero_right] at hL1; omega
  have hsL : 2 ^ L ≤ x.scale := Nat.pow_log_le_self 2 hs0
  have ha32 : slots x ≤ L / 32768 := slotBits_le _ _
  have h12 : (2 ^ slots x) ^ 12 ≤ x.scale := by
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hsL
  refine ⟨by omega, h12, (Nat.pow_le_pow_right (by norm_num) (by omega)).trans hsL,
    Nat.div_le_self _ _, Nat.log_lt_self 2 hs0, ?_⟩
  unfold step taperStep
  rw [show taper x.scale x.depth = levels x from rfl]
  rcases Nat.eq_zero_or_pos (levels x) with h0 | h0
  · rw [h0, Nat.div_zero]; exact Nat.zero_le _
  · exact (Nat.div_le_self _ _).trans (by omega)

/-- **The node precisions grow by at most `40 m²`**, at an active call at scale `m` with at most
`m` edges. -/
theorem nodePrec_le_add (ha : active x = true) (hM : x.edges ≤ x.scale) (j : ℕ) :
    nodePrec x j ≤ x.prec + 40 * x.scale ^ 2 := by
  obtain ⟨haL, -, hL, huL, hLs, hh⟩ := slots_facts ha
  unfold nodePrec nodePrecision
  set m := x.scale
  have h1 : 2 ^ (slots x - level x ((nodes x).getD j 0)) ≤ m :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)).trans hL
  have h2 : step x ≤ 4 * m := by omega
  have h3 : 8 * step x * 2 ^ (slots x - level x ((nodes x).getD j 0)) ≤ 32 * m ^ 2 :=
    calc 8 * step x * 2 ^ (slots x - level x ((nodes x).getD j 0)) ≤ 8 * (4 * m) * m :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h1
      _ = 32 * m ^ 2 := by ring
  have h4 : 8 * x.edges * (slots x + 1) ≤ 8 * m ^ 2 :=
    calc 8 * x.edges * (slots x + 1) ≤ 8 * m * m := Nat.mul_le_mul (Nat.mul_le_mul_left _ hM)
          (by omega)
      _ = 8 * m ^ 2 := by ring
  omega

/-- The level of a node index is at most `a`, and its node has size at most `2 ^ a`. -/
theorem level_le_slots_of_mem_children (ha : active x = true) {c : State} (hc : c ∈ children x) :
    level x ((nodes x).getD c.1 0) < slots x ∧
      (node (slots x) ((nodes x).getD c.1 0)).natAbs ≤ 2 ^ slots x := by
  have hu := OnSchedule.level_lt_levels hc
  have ha' := ha
  simp only [active, decide_eq_true_eq] at ha'
  obtain ⟨-, -, -, hua, -, -, -⟩ := ha'
  refine ⟨hu.trans_le hua, ?_⟩
  obtain ⟨hj, -, -⟩ := lt_of_mem_children hc
  have hkmem : (nodes x).getD c.1 0 ∈ nodes x := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  obtain ⟨hk, -, -⟩ := mem_nodes.mp hkmem
  rw [pow_succ] at hk
  unfold node
  have e : (2 : ℤ) ^ slots x = ((2 ^ slots x : ℕ) : ℤ) := by push_cast; rfl
  rw [e]
  omega

/-- The interpolation points are 0/1 lists with `e` coordinates. -/
theorem getD_points_facts (x : Call) (i : ℕ) :
    ((points x).getD i []).length ≤ x.fl.length ∧ ∀ z ∈ (points x).getD i [], z ≤ 1 := by
  by_cases hi : i < (points x).length
  · rw [List.getD_eq_getElem _ _ hi]
    simp only [points, List.getElem_map, digits, List.length_map, List.length_range, le_refl,
      List.mem_map, List.mem_range, true_and, forall_exists_index, and_imp]
    rintro z j - rfl
    split_ifs <;> omega
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

/-- The rows of a native child are at most the parent's vertices. -/
theorem childRows_le (r i : ℕ) (D : DescribedNetwork VertexDesc)
    (pk : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)) (g : ℕ) :
    childRows r i D pk g ≤ D.vertices.length := by
  unfold childRows
  refine (List.count_le_length).trans ?_
  simp [groupsOf]

/-- A packet descriptor built from a packet context with bounded fields is bounded. -/
theorem packetBound_packetCtx {fl ζ β : List ℕ} {m P k a i pt g q : ℕ} {t : ℤ}
    {tags : List (Bool × ℕ)} (hpt : pt ≤ P) (ha : a ≤ Nat.log 2 m) (hi : i ≤ a)
    (ht : t.natAbs ≤ 2 ^ a) (hζ : ζ.length ≤ fl.length) (hζ1 : ∀ z ∈ ζ, z ≤ 1)
    (htags : tags.length = k) (hslots : ∀ b ∈ tags, b.2 < 2 ^ a)
    (hβ : β.length ≤ 2 ^ (i + 1) * pt) (hβ' : ∀ b ∈ β, b ≤ pt) :
    PacketBound fl m P k (packetCtx fl a i pt t ζ g q, tags, β) :=
  ⟨hpt, rfl, rfl, ha, rfl, hi, rfl, ht, rfl, hζ, hζ1, htags, hslots, hβ, hβ'⟩

/-- **The shape passes to the native children** of an active call, from a root `x₀` at scale `m`
equal to its number of edges, with bound plus depth `m + 1`. -/
theorem Shape.child (h₀s : x₀.scale = x₀.edges) (h₀b : x₀.bound + x₀.depth = x₀.edges + 1)
    (h : Shape x₀ x) (ha : active x = true) {c : State} (hc : c ∈ children x) :
    Shape x₀ (FastContraction.child x nativeMk c) := by
  set m := x₀.edges
  have hsc : x.scale = m := h.scale_eq.trans h₀s
  have hM : x.edges ≤ m := by
    have := edges_lt_bound_of_active ha
    have := h.bound_add_depth_le
    omega
  obtain ⟨haL, h12, hL, -, -, -⟩ := slots_facts ha
  rw [hsc] at haL h12 hL
  have hK := pow_slots_le_edges_of_active ha
  obtain ⟨hlev, hnode⟩ := level_le_slots_of_mem_children ha hc
  have hprec : nodePrec x c.1 ≤ x.prec + 40 * m ^ 2 := by
    have := nodePrec_le_add ha (hsc ▸ hM) c.1
    rwa [hsc] at this
  have hmk := nativeMk_eq h.wf ha hc
  set pk := nativeParentPacking x.rows (slots x) x.net
  have hpk : pk.2.1 ≤ m ^ 2 := by
    have := numPackets_nativeParentPacking_le x.rows (slots x) x.net
    calc pk.2.1 ≤ x.edges * (2 ^ slots x) ^ 12 := this
      _ ≤ m * m := Nat.mul_le_mul hM h12
      _ = m ^ 2 := by ring
  have hslot : ∀ y ∈ pk.2.2, y.2 < 2 ^ slots x := by
    intro y hy
    rw [show pk = nativeParentPacking x.rows (slots x) x.net from rfl,
      nativeParentPacking_eq h.wf.2 hK] at hy
    obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hy
    exact ((parentPacking h.wf.2 (slots x)).slot e).2
  have hvert : (FastContraction.child x nativeMk c).net.vertices.length ≤
      x.net.vertices.length + m ^ 2 := by
    change (nativeMk x c).2.vertices.length ≤ _
    rw [hmk, length_vertices_nativeChild]
    have := childRows_le x.rows (level x ((nodes x).getD c.1 0)) x.net pk c.2.2.2
    omega
  refine ⟨h.scale_eq, h.fl_eq, wfChildren_nativeMk x h.wf ha c hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := edges_lt_bound_of_active ha
    have := h.bound_add_depth_le
    change x.edges + (x.depth + 1) ≤ _
    omega
  · change (nativeMk x c).2.numEdges ≤ 2 * m
    rw [hmk]
    exact (numEdges_nativeChild_le _ _ _ _ _ _ _ _ _ _ _).trans (Nat.mul_le_mul_left 2 hM)
  · change nodePrec x c.1 ≤ x₀.prec + (x.depth + 1) * (40 * m ^ 2)
    have : x.prec ≤ x₀.prec + x.depth * (40 * m ^ 2) := h.prec_le
    rw [add_one_mul]
    omega
  · change _ ≤ x₀.net.vertices.length + (x.depth + 1) * m ^ 2
    have : x.net.vertices.length ≤ x₀.net.vertices.length + x.depth * m ^ 2 :=
      h.vertices_le
    rw [add_one_mul]
    omega
  · refine Or.inr ?_
    change (nativeMk x c).1 ≤ x₀.net.vertices.length + (x.depth + 1) * m ^ 2
    rw [hmk]
    have := childRows_le x.rows (level x ((nodes x).getD c.1 0)) x.net pk c.2.2.2
    have : x.net.vertices.length ≤ x₀.net.vertices.length + x.depth * m ^ 2 :=
      h.vertices_le
    rw [add_one_mul]
    omega
  · intro v hv
    change v ∈ (nativeMk x c).2.vertices at hv
    rw [hmk] at hv
    rcases mem_vertices_nativeChild _ _ _ _ _ _ _ _ _ _ _ hv with ⟨w, hw, hd, hl⟩ |
      ⟨q, -, tags, hd, htl, hts⟩
    · rcases h.desc w hw with ⟨u, hu, hu'⟩ | ⟨d, hwd, hb⟩
      · exact Or.inl ⟨u, hu, hd.trans hu'⟩
      · refine Or.inr ⟨d, hd.trans hwd, ?_⟩
        rw [hl]
        refine hb.mono ?_
        change x₀.prec + x.depth * (40 * m ^ 2) ≤ x₀.prec + (x.depth + 1) * (40 * m ^ 2)
        rw [add_one_mul]
        omega
    · refine Or.inr ⟨_, hd, ?_⟩
      have hζ := getD_points_facts x c.2.1
      have hβ := lt_nodePrec_of_mem_children hc
      have hp : nodePrec x c.1 ≤ x₀.prec + (x.depth + 1) * (40 * m ^ 2) := by
        have : x.prec ≤ x₀.prec + x.depth * (40 * m ^ 2) := h.prec_le
        rw [add_one_mul]
        omega
      have hfl : x.fl.length = x₀.fl.length := by rw [h.fl_eq]
      rw [h.fl_eq] at hζ ⊢
      refine packetBound_packetCtx hp haL hlev.le hnode (hfl ▸ hζ.1) hζ.2 htl (fun b hb => ?_)
        (length_betaSlice_le _ _ _ _) fun b hb => (hβ b (mem_of_mem_betaSlice _ _ _ hb)).le
      rcases hts b hb with h0 | ⟨y, hy, hy'⟩
      · rw [h0]; exact Nat.two_pow_pos _
      · rw [hy']; exact hslot y hy

/-- **Every reached call has the shape** of a root `x₀` that is well-formed, at scale its number of
edges, with bound plus depth `m + 1`. -/
theorem Reach.shape (h₀s : x₀.scale = x₀.edges) (h₀b : x₀.bound + x₀.depth = x₀.edges + 1)
    (h₀ : WF x₀) (h : Reach nativeMk x₀ x) : Shape x₀ x := by
  induction h with
  | root =>
    exact ⟨rfl, rfl, h₀, le_rfl, by omega, Nat.le_add_right _ _, Nat.le_add_right _ _,
      Or.inl rfl, fun v hv => Or.inl ⟨v, hv, rfl⟩⟩
  | step c _ ha hc ih => exact ih.child h₀s h₀b ha hc

end Child

end Cslib.Circuits.Frontier.FastContraction
