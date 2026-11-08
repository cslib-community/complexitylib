/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Tactic.EncLen
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.GetD
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Iterate
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite certificates for rotations of listed multigraphs

A certificate lists the successor of each of the `2m` indexed darts. Dart `2i` is the first
end of listed edge `i`, and dart `2i+1` its second end. The checker uses bounded table lookup
and at most `2m` iterations for orbit membership, including singleton orbits. All labels and
indices use binary encodings; no loop is funded by a vertex label or a supplied table entry.

The table must be a permutation, every endpoint must be declared, and the successor orbits
must be exactly the endpoint fibers. Accepted certificates decode to the existing
`Graph.RotationSystem`; conversely every rotation on a graph with declared endpoints has a
certificate. Decoding is proof-only; the Boolean checker does not execute a choice operation.

`verifyGenusZero` additionally checks `V+F=E+2` in each nonempty edge component, counting
distinct endpoint vertices, indexed edges, and all face orbits. Isolated declared vertices use
the separate point-component convention `V=1,E=0,F=1`; they contribute no dart orbit. No face
is required to carry a constraint, and repeated vertices along face orbits are allowed.

This finite representation and its correctness proofs are original. They supply no geometric
realization or planarity recognition theorem.

## Main definitions

* `Cslib.Complexity.Graph.RotationCertificate`: binary successor table.
* `Cslib.Complexity.Graph.RotationCertificate.verifyGenusZero`: finite supplied-certificate check.
* `Cslib.Complexity.Graph.RotationSystem.NumericalGenusZero`: componentwise numerical predicate.

## Main results

* `Cslib.Complexity.Graph.RotationCertificate.decode_ofRotation`: exact rotation recovery.
* `Cslib.Complexity.Graph.RotationCertificate.verifyEuler_eq_true_iff`: numerical correspondence.
* `Cslib.Complexity.Graph.RotationCertificate.exists_bounded_certificate_iff`: both directions
  with a quadratic certificate bit bound.
-/

public section

namespace Cslib.Complexity.Graph

open Turing.MultiTapeTM

namespace Dart

/-- Binary index of a dart: edge position followed by its endpoint bit. -/
@[expose] def index {G : Graph} (d : Dart G) : ℕ := 2 * d.1.val + d.2.toNat

/-- Indexed darts are exactly the positions of the flattened endpoint list. -/
@[expose] def indexEquiv (G : Graph) : Dart G ≃ Fin (2 * G.2.length) where
  toFun d := ⟨d.index, by
    have := endpoint_index_lt G d.1.isLt d.2
    simpa only [incidenceVertices_length, index] using this⟩
  invFun i := (⟨i.val / 2, by omega⟩, decide (i.val % 2 = 1))
  left_inv d := by
    rcases d with ⟨⟨i, hi⟩, b⟩
    cases b <;> simp [index]
    omega
  right_inv i := by
    apply Fin.ext
    change 2 * (i.val / 2) + (decide (i.val % 2 = 1)).toNat = i.val
    by_cases h : i.val % 2 = 1 <;> simp only [h, decide_true, decide_false,
      Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The code reads exactly the original dart endpoint. -/
theorem vertex_index {G : Graph} (d : Dart G) :
    G.incidenceVertices.getD d.index 0 = d.vertex :=
  getD_incidenceVertices_endpoint G d.1 d.2

end Dart

/-- One binary successor index for each indexed edge end, in edge/end order. -/
structure RotationCertificate where
  /-- Successor table; its required length is twice the actual edge-list length. -/
  successor : List ℕ
  deriving DecidableEq, Repr

/-- A rotation certificate is its framed list of binary successor indices. -/
enc_structure encRotationCertificate : RotationCertificate where successor : (encList encNat)

/-- Graph, framed, followed by its successor certificate. Labels and indices are binary. -/
abbrev encGraphRotationCertificate := encPair encGraph encRotationCertificate

namespace RotationCertificate

/-- Total table iteration. Missing entries return zero, even for enormous binary indices. -/
@[expose] def walk (table : List ℕ) (steps start : ℕ) : ℕ :=
  (fun i => table.getD i 0)^[steps] start

/-- Orbit test with a clock funded by the actual number of darts. -/
@[expose] def orbitBool (n : ℕ) (table : List ℕ) (i j : ℕ) : Bool :=
  (List.range n).any fun k => decide (walk table k i = j)

/-- All declared endpoints, exact table length, permutation, and exact endpoint fibers. -/
@[expose] def verifyRotation (G : Graph) (c : RotationCertificate) : Bool :=
  (G.incidenceVertices.all fun v => G.1.any fun u => decide (u = v)) &&
    decide (c.successor.length = 2 * G.2.length) &&
    enumeratesBool (List.range (2 * G.2.length)) c.successor &&
    (List.range (2 * G.2.length)).all fun i =>
      (List.range (2 * G.2.length)).all fun j =>
        decide (orbitBool (2 * G.2.length) c.successor i j =
          decide (G.incidenceVertices.getD i 0 = G.incidenceVertices.getD j 0))

private theorem verifyRotation_parts {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) :
    (∀ v ∈ G.incidenceVertices, v ∈ G.1) ∧
      c.successor.length = 2 * G.2.length ∧ c.successor.Nodup ∧
      (∀ v, v ∈ c.successor ↔ v < 2 * G.2.length) ∧
      ∀ i < 2 * G.2.length, ∀ j < 2 * G.2.length,
        orbitBool (2 * G.2.length) c.successor i j =
          decide (G.incidenceVertices.getD i 0 = G.incidenceVertices.getD j 0) := by
  simpa only [verifyRotation, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, enumeratesBool_eq_true_iff, List.mem_range,
    exists_eq_right, and_assoc] using h

private def tableMap (G : Graph) (c : RotationCertificate) (h : verifyRotation G c = true)
    (i : Fin (2 * G.2.length)) : Fin (2 * G.2.length) :=
  ⟨c.successor.getD i 0, (verifyRotation_parts h).2.2.2.1 _ |>.mp (by
    rw [List.getD_eq_getElem _ _ (by rw [(verifyRotation_parts h).2.1]; exact i.isLt)]
    exact List.getElem_mem _)⟩

private theorem tableMap_injective {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) : Function.Injective (tableMap G c h) := by
  intro i j hij
  apply Fin.ext
  have hi : i.val < c.successor.length := by rw [(verifyRotation_parts h).2.1]; exact i.isLt
  have hj : j.val < c.successor.length := by rw [(verifyRotation_parts h).2.1]; exact j.isLt
  have heq := congrArg Fin.val hij
  simp only [tableMap, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at heq
  have heq' : (⟨i.val, hi⟩ : Fin c.successor.length) = ⟨j.val, hj⟩ :=
    (List.nodup_iff_injective_get.mp (verifyRotation_parts h).2.2.1) heq
  exact congrArg (fun k : Fin c.successor.length => k.val) heq'

private noncomputable def tablePerm (G : Graph) (c : RotationCertificate)
    (h : verifyRotation G c = true) : Equiv.Perm (Fin (2 * G.2.length)) :=
  Equiv.ofBijective (tableMap G c h)
    ⟨tableMap_injective h, Finite.surjective_of_injective (tableMap_injective h)⟩

private theorem sameCycle_iff_bounded {α : Type} [Fintype α]
    (f : Equiv.Perm α) (d e : α) :
    f.SameCycle d e ↔ ∃ k < Fintype.card α, f^[k] d = e := by
  classical
  constructor
  · intro h
    by_cases hd : d ∈ f.support
    · obtain ⟨k, hk, he⟩ := h.exists_pow_eq_of_mem_support hd
      exact ⟨k, hk.trans_le (Finset.card_le_univ _), by
        simpa only [Equiv.Perm.iterate_eq_pow] using he⟩
    · refine ⟨0, Fintype.card_pos_iff.mpr ⟨d⟩, ?_⟩
      exact h.eq_of_left (Equiv.Perm.notMem_support.mp hd)
  · rintro ⟨k, -, he⟩
    exact ⟨(k : ℤ), by simpa only [zpow_natCast, Equiv.Perm.iterate_eq_pow] using he⟩

/-- A bounded table orbit is the existing permutation's `SameCycle`, when its entries encode
that permutation. The clock is the cardinality, rather than the permutation's order. -/
theorem orbitBool_eq_true_iff {G : Graph} (f : Equiv.Perm (Dart G)) (table : List ℕ)
    (ht : ∀ d, table.getD d.index 0 = (f d).index) (d e : Dart G) :
    orbitBool (2 * G.2.length) table d.index e.index = true ↔ f.SameCycle d e := by
  have hw (k : ℕ) (d : Dart G) : walk table k d.index = (f^[k] d).index := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [walk, Function.iterate_succ_apply', ← walk, ih, ht, Function.iterate_succ_apply']
  simp only [orbitBool, List.any_eq_true, List.mem_range, decide_eq_true_eq, hw]
  rw [sameCycle_iff_bounded, Dart.card]
  constructor <;> rintro ⟨k, hk, he⟩ <;> refine ⟨k, hk, ?_⟩
  · exact (Dart.indexEquiv G).injective (Fin.ext he)
  · exact congrArg Dart.index he

private noncomputable def decodedPerm (G : Graph) (c : RotationCertificate)
    (h : verifyRotation G c = true) : Equiv.Perm (Dart G) :=
  ((Dart.indexEquiv G).trans (tablePerm G c h)).trans (Dart.indexEquiv G).symm

private theorem index_decodedPerm {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) :
    (decodedPerm G c h d).index = c.successor.getD d.index 0 := by
  exact congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply
    (tablePerm G c h (Dart.indexEquiv G d)))

/-- Decode an accepted finite table to the existing rotation-system structure. This operation
is used in proofs; the native checker executes only finite list operations. -/
noncomputable def decode (G : Graph) (c : RotationCertificate)
    (h : verifyRotation G c = true) : RotationSystem G where
  rotate := decodedPerm G c h
  sameCycle_iff d e := by
    rw [← orbitBool_eq_true_iff _ c.successor (fun d => (index_decodedPerm h d).symm),
      (verifyRotation_parts h).2.2.2.2 d.index (Dart.indexEquiv G d).isLt
        e.index (Dart.indexEquiv G e).isLt,
      decide_eq_true_eq, Dart.vertex_index, Dart.vertex_index]

/-- The decoded successor is exactly the supplied table entry. -/
theorem index_decode_rotate {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) :
    ((decode G c h).rotate d).index = c.successor.getD d.index 0 :=
  index_decodedPerm h d

/-- A table for an abstract rotation, in the canonical edge/end order. -/
@[expose] def ofRotation {G : Graph} (r : RotationSystem G) : RotationCertificate :=
  ⟨List.ofFn fun i : Fin (2 * G.2.length) => (r.rotate ((Dart.indexEquiv G).symm i)).index⟩

/-- The canonical table has exactly two entries per listed edge. -/
@[simp] theorem length_ofRotation {G : Graph} (r : RotationSystem G) :
    (ofRotation r).successor.length = 2 * G.2.length := by simp [ofRotation]

/-- Reading the canonical table recovers the rotation. -/
theorem getD_ofRotation {G : Graph} (r : RotationSystem G) (d : Dart G) :
    (ofRotation r).successor.getD d.index 0 = (r.rotate d).index := by
  rw [List.getD_eq_getElem _ _ (by rw [length_ofRotation]; exact (Dart.indexEquiv G d).isLt)]
  simp [ofRotation, ← show (Dart.indexEquiv G d).val = d.index from rfl]

/-- Every existing rotation has an accepted finite certificate when its endpoints are declared.
No rotation is assumed to be geometrically planar. -/
theorem verifyRotation_ofRotation {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    verifyRotation G (ofRotation r) = true := by
  have hinj : Function.Injective (fun i : Fin (2 * G.2.length) =>
      (r.rotate ((Dart.indexEquiv G).symm i)).index) := by
    intro i j h
    exact (Dart.indexEquiv G).symm.injective (r.rotate.injective
      ((Dart.indexEquiv G).injective (Fin.ext h)))
  have hmem (v : ℕ) : v ∈ (ofRotation r).successor ↔ v < 2 * G.2.length := by
    simp only [ofRotation, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩
      exact (Dart.indexEquiv G (r.rotate ((Dart.indexEquiv G).symm i))).isLt
    · intro hv
      refine ⟨Dart.indexEquiv G (r.rotate.symm ((Dart.indexEquiv G).symm ⟨v, hv⟩)), ?_⟩
      simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      exact congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨v, hv⟩)
  simp only [verifyRotation, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, enumeratesBool_eq_true_iff, List.mem_range]
  refine ⟨⟨⟨?_, length_ofRotation r⟩, ?_⟩, ?_⟩
  · exact fun v hv => ⟨v, hG v hv, rfl⟩
  · exact ⟨List.nodup_ofFn.mpr hinj, hmem⟩
  · intro i hi j hj
    let d := (Dart.indexEquiv G).symm ⟨i, hi⟩
    let e := (Dart.indexEquiv G).symm ⟨j, hj⟩
    have hd : d.index = i := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨i, hi⟩)
    have he : e.index = j := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨j, hj⟩)
    rw [← hd, ← he]
    apply Bool.eq_iff_iff.mpr
    rw [orbitBool_eq_true_iff r.rotate _ (getD_ofRotation r), decide_eq_true_eq,
      Dart.vertex_index, Dart.vertex_index, r.sameCycle_iff]

/-- Encoding and then decoding preserves the actual successor permutation. -/
theorem decode_ofRotation_rotate {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    (decode G (ofRotation r) (verifyRotation_ofRotation r hG)).rotate = r.rotate := by
  apply Equiv.ext
  intro d
  apply (Dart.indexEquiv G).injective
  apply Fin.ext
  change ((decode G (ofRotation r) (verifyRotation_ofRotation r hG)).rotate d).index =
    (r.rotate d).index
  rw [index_decode_rotate, getD_ofRotation]

/-- Canonical table encoding and checked decoding recover the existing rotation structure. -/
theorem decode_ofRotation {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    decode G (ofRotation r) (verifyRotation_ofRotation r hG) = r := by
  have hrot := decode_ofRotation_rotate r hG
  generalize decode G (ofRotation r) (verifyRotation_ofRotation r hG) = s at hrot ⊢
  cases s
  cases r
  cases hrot
  rfl

/-- A coarse quadratic bit bound for the canonical certificate, including all framing.
The bound depends on the encoded graph length, even for sparse, very large vertex labels. -/
theorem length_enc_ofRotation_le {G : Graph} (r : RotationSystem G) :
    (encRotationCertificate (ofRotation r)).length ≤ 10 * ((encGraph G).length + 1) ^ 2 := by
  have hm : G.2.length ≤ (encGraph G).length := by
    calc G.2.length ≤ (encList (encPair encNat encNat) G.2).length :=
        length_le_length_encList _ _
      _ ≤ (encGraph G).length := by enc_len [encGraph]
  have hb : ∀ v ∈ (ofRotation r).successor, (encNat v).length ≤ 2 * G.2.length := by
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    have hi := (Dart.indexEquiv G (r.rotate ((Dart.indexEquiv G).symm i))).isLt
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact (Nat.size_le_self _).trans (Nat.le_of_lt hi)
  have hs := length_encList_le encNat (ofRotation r).successor hb
  rw [length_ofRotation] at hs
  change (encList encNat (ofRotation r).successor).length ≤ _
  exact hs.trans (by nlinarith [Nat.mul_self_le_mul_self hm])

/-- One breadth-first expansion, retaining the old list. Repetitions are harmless: the result
is used only for membership, never as a vertex count. -/
@[expose] def componentStep (G : Graph) (seen : List ℕ) : List ℕ :=
  seen ++ G.1.filter fun v => seen.any fun u => G.adjBool u v

/-- Finite reachability from a declared root, with one iteration per declared vertex record. -/
@[expose] def componentVertices (G : Graph) (root : ℕ) : List ℕ :=
  (componentStep G)^[G.1.length] [root]

/-- Native component membership; no range up to a binary vertex label is constructed. -/
@[expose] def componentBool (G : Graph) (root v : ℕ) : Bool :=
  (componentVertices G root).any fun u => decide (u = v)

/-- Membership in the same connected component of the existing graph on declared vertices. -/
@[expose] def SameComponent (G : Graph) (u v : ℕ) : Prop :=
  ∃ hu : u ∈ G.1, ∃ hv : v ∈ G.1, G.induced.Reachable ⟨u, hu⟩ ⟨v, hv⟩

/-- A declared vertex is in its own component, including an isolated vertex. -/
theorem SameComponent.refl {G : Graph} {v : ℕ} (hv : v ∈ G.1) : SameComponent G v v :=
  ⟨hv, hv, .rfl⟩

/-- Component membership is symmetric. -/
theorem SameComponent.symm {G : Graph} {u v : ℕ} (h : SameComponent G u v) :
    SameComponent G v u := by
  obtain ⟨hu, hv, h⟩ := h
  exact ⟨hv, hu, h.symm⟩

/-- Component membership is transitive. -/
theorem SameComponent.trans {G : Graph} {u v w : ℕ}
    (h : SameComponent G u v) (h' : SameComponent G v w) : SameComponent G u w := by
  obtain ⟨hu, hv, h⟩ := h
  obtain ⟨_, hw, h'⟩ := h'
  exact ⟨hu, hw, h.trans h'⟩

private theorem mem_componentStep {G : Graph} {seen : List ℕ} {v : ℕ} :
    v ∈ componentStep G seen ↔
      v ∈ seen ∨ v ∈ G.1 ∧ ∃ u ∈ seen, G.toSimpleGraph.Adj u v := by
  simp [componentStep, List.any_eq_true]

private theorem mem_iterate_componentStep {G : Graph} {seen : List ℕ} {v : ℕ}
    (hv : v ∈ seen) (k : ℕ) : v ∈ (componentStep G)^[k] seen := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact mem_componentStep.mpr (Or.inl ih)

private theorem walk_mem_componentStep {G : Graph}
    {u v : {v // v ∈ G.1}} (p : G.induced.Walk u v) {seen : List ℕ}
    (hu : u.val ∈ seen) : v.val ∈ (componentStep G)^[p.length] seen := by
  induction p generalizing seen with
  | nil => exact hu
  | @cons u w v hadj p ih =>
    rw [SimpleGraph.Walk.length_cons, Function.iterate_succ_apply]
    apply ih
    exact mem_componentStep.mpr (Or.inr ⟨w.property, u.val, hu, hadj⟩)

/-- The finite expansion agrees exactly with connectedness in the existing induced graph.
The path bound is the number of declared vertices, including malformed duplicate records. -/
theorem componentBool_eq_true_iff {G : Graph} {root v : ℕ} (hr : root ∈ G.1) :
    componentBool G root v = true ↔ SameComponent G root v := by
  simp only [componentBool, List.any_eq_true, decide_eq_true_eq, exists_eq_right]
  constructor
  · intro hv
    have hs (k : ℕ) : ∀ w ∈ (componentStep G)^[k] [root], SameComponent G root w := by
      induction k with
      | zero =>
        intro w hw
        have hw' : w = root := List.mem_singleton.mp hw
        subst w
        exact ⟨hr, hr, .rfl⟩
      | succ k ih =>
        intro w hw
        rw [Function.iterate_succ_apply'] at hw
        rcases mem_componentStep.mp hw with hw | ⟨hw, u, hu, hadj⟩
        · exact ih _ hw
        · obtain ⟨hr, hu', hru⟩ := ih _ hu
          exact ⟨hr, hw, hru.trans (SimpleGraph.Adj.reachable hadj)⟩
    exact hs _ _ hv
  · rintro ⟨hr, hv, hconn⟩
    obtain ⟨p, hp⟩ := hconn.exists_isPath
    have hc : Fintype.card {v // v ∈ G.1} = G.1.toFinset.card := card_vertexSubtype G
    have hlen' : p.length ≤ G.1.length := by
      have := hp.length_lt
      rw [hc] at this
      exact this.le.trans G.1.toFinset_card_le
    have hm := walk_mem_componentStep p (seen := [root]) (by simp)
    have := mem_iterate_componentStep (G := G) hm (G.1.length - p.length)
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hlen'] at this

/-- Reverse a dart's endpoint bit without inspecting vertex labels. -/
@[expose] def reverseIndex (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

/-- Binary reversal agrees with reversal of the existing indexed dart. -/
theorem reverseIndex_index {G : Graph} (d : Dart G) : reverseIndex d.index = d.reverse.index := by
  rcases d with ⟨i, b⟩
  cases b <;> simp [reverseIndex, Dart.index, Dart.reverse]

/-- The face successor table: reverse the edge, then look up the inverse rotation.
`idxOf` returns the table length on failure, making this total on malformed certificates. -/
@[expose] def faceTable (G : Graph) (c : RotationCertificate) : List ℕ :=
  (List.range (2 * G.2.length)).map fun i => c.successor.idxOf (reverseIndex i)

/-- Test that this dart is the least indexed member of its face orbit, including fixed points. -/
@[expose] def faceRepBool (n : ℕ) (table : List ℕ) (i : ℕ) : Bool :=
  (List.range n).all fun j => !orbitBool n table i j || decide (i ≤ j)

private theorem idxOf_decode {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) :
    c.successor.idxOf d.index = ((decode G c h).rotate.symm d).index := by
  let e := (decode G c h).rotate.symm d
  have hi : e.index < c.successor.length := by
    rw [(verifyRotation_parts h).2.1]
    exact (Dart.indexEquiv G e).isLt
  have he : c.successor.getD e.index 0 = d.index := by
    rw [← index_decode_rotate h e]
    exact congrArg Dart.index ((decode G c h).rotate.apply_symm_apply d)
  rw [← he, List.getD_eq_getElem _ _ hi]
  exact (verifyRotation_parts h).2.2.1.idxOf_getElem e.index hi

/-- The finite face table realizes exactly `RotationSystem.faceNext`. -/
theorem getD_faceTable {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) :
    (faceTable G c).getD d.index 0 = ((decode G c h).faceNext d).index := by
  have hd : d.index < 2 * G.2.length := (Dart.indexEquiv G d).isLt
  rw [List.getD_eq_getElem _ _ (by simpa only [faceTable, List.length_map,
    List.length_range] using hd)]
  simp only [faceTable, List.getElem_map, List.getElem_range, reverseIndex_index,
    idxOf_decode h]
  rfl

/-- Componentwise Euler test. Every declared root is checked separately. For a root with no
incident dart, use the point-component convention `V=1,E=0,F=1`, not a dart orbit.
For an edge component, count distinct vertices, listed edge positions, and every face orbit. -/
@[expose] def verifyEuler (G : Graph) (c : RotationCertificate) : Bool :=
  G.1.all fun root =>
    if G.incidenceVertices.any (fun v => decide (v = root)) then
      decide (G.distinctVertices.countP (componentBool G root) +
        ((List.range (2 * G.2.length)).countP fun i =>
          componentBool G root (G.incidenceVertices.getD i 0) &&
            faceRepBool (2 * G.2.length) (faceTable G c) i) =
        G.2.countP (fun e => componentBool G root e.1) + 2)
    else decide (1 + 1 = 0 + 2)

/-- Full supplied-certificate checker: rotation validity and componentwise numerical Euler. -/
@[expose] def verifyGenusZero (G : Graph) (c : RotationCertificate) : Bool :=
  verifyRotation G c && verifyEuler G c

end RotationCertificate

namespace RotationSystem

/-- Every dart endpoint is declared when all listed edge endpoints are declared. -/
theorem vertex_mem {G : Graph}
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) : d.vertex ∈ G.1 := by
  apply hG
  rw [← Dart.vertex_index, List.getD_eq_getElem _ _ (show d.index < G.incidenceVertices.length
    from endpoint_index_lt G d.1.isLt d.2)]
  exact List.getElem_mem _

/-- The two indexed ends of an edge belong to the same declared-vertex component,
including when the edge is a loop. All listed endpoints must be declared. -/
theorem sameComponent_reverse {G : Graph}
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    RotationCertificate.SameComponent G d.vertex d.reverse.vertex := by
  have hd := vertex_mem hG d
  have he := vertex_mem hG d.reverse
  by_cases h : d.vertex = d.reverse.vertex
  · rw [h]
    exact .refl he
  · refine ⟨hd, he, SimpleGraph.Adj.reachable ?_⟩
    change G.toSimpleGraph.Adj d.vertex d.reverse.vertex
    rw [toSimpleGraph_adj]
    refine ⟨h, ?_⟩
    have hm : G.2.getD d.1.val (0, 0) ∈ G.2 := by
      rw [List.getD_eq_getElem _ _ d.1.isLt]
      exact List.getElem_mem _
    rcases d with ⟨i, b⟩
    cases b
    · exact Or.inl hm
    · exact Or.inr hm

/-- A face successor stays in the same edge component. -/
theorem sameComponent_faceNext {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (d : Dart G) :
    RotationCertificate.SameComponent G d.vertex (r.faceNext d).vertex := by
  have hv : (r.faceNext d).vertex = d.reverse.vertex := by
    change (r.rotate.symm d.reverse).vertex = d.reverse.vertex
    have := r.vertex_rotate (r.rotate.symm d.reverse)
    simpa only [Equiv.apply_symm_apply] using this.symm
  rw [hv]
  exact sameComponent_reverse hG d

/-- All darts of each face orbit belong to one edge component. Thus componentwise face counts
cannot split an orbit or transfer a face between disconnected edge components. -/
theorem sameComponent_of_sameFace {G : Graph} (r : RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) {d e : Dart G}
    (h : r.faceNext.SameCycle d e) :
    RotationCertificate.SameComponent G d.vertex e.vertex := by
  obtain ⟨k, -, rfl⟩ := (RotationCertificate.sameCycle_iff_bounded r.faceNext d e).mp h
  clear h
  induction k with
  | zero => exact .refl (vertex_mem hG d)
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (r.sameComponent_faceNext hG _)

/-- The least indexed dart of a face. Fixed points qualify, so their faces are counted too. -/
@[expose] def IsFaceRepresentative {G : Graph} (r : RotationSystem G) (d : Dart G) : Prop :=
  ∀ e, r.faceNext.SameCycle d e → d.index ≤ e.index

open Classical in
/-- Componentwise numerical genus zero. An edge component has `V+F=E+2`, with distinct
endpoint vertices, indexed edge records and all face orbits. An isolated declared vertex is a
point component with one conventional face and no dart. This is a numerical predicate on the
existing rotations, not an equivalence to geometric planarity. In particular, geometric outer
faces of disconnected drawings have not been identified with these componentwise faces. -/
@[expose] noncomputable def NumericalGenusZero {G : Graph} (r : RotationSystem G) : Prop :=
  ∀ root ∈ G.1,
    if ∃ d : Dart G, d.vertex = root then
      G.distinctVertices.countP (fun v => decide (RotationCertificate.SameComponent G root v)) +
        ((List.finRange (2 * G.2.length)).countP fun i =>
          decide (RotationCertificate.SameComponent G root
            ((Dart.indexEquiv G).symm i).vertex ∧
              r.IsFaceRepresentative ((Dart.indexEquiv G).symm i))) =
        G.2.countP (fun e => decide (RotationCertificate.SameComponent G root e.1)) + 2
    else 1 + 1 = 0 + 2

/-- Each face orbit has exactly one representative, including a one-dart fixed-point orbit. -/
theorem existsUnique_faceRepresentative {G : Graph} (r : RotationSystem G) (d : Dart G) :
    ∃! e, r.faceNext.SameCycle d e ∧ r.IsFaceRepresentative e := by
  classical
  let P (n : ℕ) := ∃ e : Dart G, e.index = n ∧ r.faceNext.SameCycle d e
  have hex : ∃ n, P n := ⟨d.index, d, rfl, .rfl⟩
  obtain ⟨e, he, hde⟩ := Nat.find_spec hex
  have hrep : r.IsFaceRepresentative e := by
    intro f hef
    rw [he]
    exact Nat.find_min' hex ⟨f, rfl, hde.trans hef⟩
  refine ⟨e, ⟨hde, hrep⟩, fun f ⟨hdf, hfrep⟩ => ?_⟩
  apply (Dart.indexEquiv G).injective
  apply Fin.ext
  exact Nat.le_antisymm (hfrep e (hdf.symm.trans hde)) (hrep f (hde.symm.trans hdf))

end RotationSystem

namespace RotationCertificate

private theorem incidentBool_eq_true_iff (G : Graph) (root : ℕ) :
    G.incidenceVertices.any (fun v => decide (v = root)) = true ↔
      ∃ d : Dart G, d.vertex = root := by
  simp only [List.any_eq_true, decide_eq_true_eq, exists_eq_right]
  constructor
  · intro hr
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
    let j : Fin (2 * G.2.length) := ⟨i.val, i.isLt.trans_eq (incidenceVertices_length G)⟩
    let d := (Dart.indexEquiv G).symm j
    refine ⟨d, ?_⟩
    have hd : d.index = i.val := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply j)
    rw [← Dart.vertex_index, hd, List.getD_eq_getElem _ _ i.isLt]
    exact hi
  · rintro ⟨d, rfl⟩
    rw [← Dart.vertex_index, List.getD_eq_getElem _ _ (show d.index < G.incidenceVertices.length
      from endpoint_index_lt G d.1.isLt d.2)]
    exact List.getElem_mem _

/-- The face representative test counts exactly the existing face orbits. -/
theorem faceRepBool_eq_true_iff {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) (d : Dart G) :
    faceRepBool (2 * G.2.length) (faceTable G c) d.index = true ↔
      (decode G c h).IsFaceRepresentative d := by
  simp only [faceRepBool, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, RotationSystem.IsFaceRepresentative]
  constructor
  · intro hr e he
    have hh := hr e.index (Dart.indexEquiv G e).isLt
    have ho := (orbitBool_eq_true_iff (decode G c h).faceNext _ (getD_faceTable h) d e).mpr he
    simpa only [ho, Bool.true_eq_false, false_or] using hh
  · intro hr i hi
    let e := (Dart.indexEquiv G).symm ⟨i, hi⟩
    have he : e.index = i := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨i, hi⟩)
    by_cases ho : orbitBool (2 * G.2.length) (faceTable G c) d.index i = true
    · right
      rw [← he] at ho ⊢
      exact hr e ((orbitBool_eq_true_iff _ _ (getD_faceTable h) d e).mp ho)
    · exact Or.inl (Bool.eq_false_iff.mpr ho)

/-- The executable Euler check agrees with the explicit componentwise numerical predicate
on the decoded existing rotation. No geometric correspondence is used. -/
theorem verifyEuler_eq_true_iff {G : Graph} {c : RotationCertificate}
    (h : verifyRotation G c = true) :
    verifyEuler G c = true ↔ (decode G c h).NumericalGenusZero := by
  classical
  unfold verifyEuler RotationSystem.NumericalGenusZero
  rw [List.all_eq_true]
  apply forall₂_congr
  intro root hr
  have hcb : componentBool G root = fun v => decide (SameComponent G root v) := by
    funext v
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact componentBool_eq_true_iff hr
  have hfaces : ((List.range (2 * G.2.length)).countP fun i =>
      componentBool G root (G.incidenceVertices.getD i 0) &&
        faceRepBool (2 * G.2.length) (faceTable G c) i) =
      ((List.finRange (2 * G.2.length)).countP fun i =>
        decide (SameComponent G root ((Dart.indexEquiv G).symm i).vertex ∧
          (decode G c h).IsFaceRepresentative ((Dart.indexEquiv G).symm i))) := by
    rw [← List.map_coe_finRange_eq_range, List.countP_map]
    apply List.countP_congr
    intro i _
    let d := (Dart.indexEquiv G).symm i
    have hd : d.index = i.val := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply i)
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    rw [← hd, Dart.vertex_index, componentBool_eq_true_iff hr, faceRepBool_eq_true_iff h]
  by_cases hi : ∃ d : Dart G, d.vertex = root
  · have hb := (incidentBool_eq_true_iff G root).mpr hi
    simp only [hb, ↓reduceIte, hi, decide_eq_true_eq]
    rw [hfaces, hcb]
  · have hb : G.incidenceVertices.any (fun v => decide (v = root)) = false :=
      Bool.eq_false_iff.mpr (mt (incidentBool_eq_true_iff G root).mp hi)
    simp [hb, hi]

/-- Exact soundness and completeness for a *supplied* certificate. Acceptance is equivalent to
an actual rotation represented by the table and satisfying componentwise numerical Euler. -/
theorem verifyGenusZero_eq_true_iff (G : Graph) (c : RotationCertificate) :
    verifyGenusZero G c = true ↔
      ∃ h : verifyRotation G c = true, (decode G c h).NumericalGenusZero := by
  simp only [verifyGenusZero, Bool.and_eq_true]
  constructor
  · rintro ⟨h, he⟩
    exact ⟨h, (verifyEuler_eq_true_iff h).mp he⟩
  · rintro ⟨h, he⟩
    exact ⟨h, (verifyEuler_eq_true_iff h).mpr he⟩

/-- Every numerical genus-zero rotation has a certificate within the explicit quadratic bit
bound, and every accepted such certificate supplies an actual numerical genus-zero rotation. -/
theorem exists_bounded_certificate_iff (G : Graph)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    (∃ r : RotationSystem G, r.NumericalGenusZero) ↔
      ∃ c : RotationCertificate,
        (encRotationCertificate c).length ≤ 10 * ((encGraph G).length + 1) ^ 2 ∧
          verifyGenusZero G c = true := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨ofRotation r, length_enc_ofRotation_le r, ?_⟩
    apply (verifyGenusZero_eq_true_iff _ _).mpr
    refine ⟨verifyRotation_ofRotation r hG, ?_⟩
    rwa [decode_ofRotation]
  · rintro ⟨c, -, hc⟩
    obtain ⟨h, hr⟩ := (verifyGenusZero_eq_true_iff G c).mp hc
    exact ⟨decode G c h, hr⟩

end RotationCertificate
end Cslib.Complexity.Graph
