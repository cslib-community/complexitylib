/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpace

/-!
# Intersection parity of finite closed passage systems

A closed passage system pairs the actual darts of a supported indexed edge set, using each
exactly once and pairing only darts at the same vertex. This retains multiple visits,
high-degree vertices, arbitrary local pairings and self-intersections. It adds no graph,
topological universe or intersection-parity premise.

Intervals follow the literal cyclic successor `rotate`, stopping at its first visit to the
second end. Two passages alternate when exactly one end is in this interval and their four
darts are distinct. The finite face-color proof is an original reconstruction: boundaries
telescope along a rotation interval, and the resulting endpoint contributions cancel along
the second closed passage system.

The final result concerns the existing componentwise numerical genus model. It proves no
drawing realization, drawing operation, weak or unified Hanani–Tutte theorem, recognition
criterion, or Boolean CSP dichotomy.

## Main definitions

* `Cslib.Complexity.Graph.ClosedPassages`: exactly-once finite dart pairing.
* `Cslib.Complexity.Graph.RotationSystem.Alternates`: literal cyclic port alternation.
* `Cslib.Complexity.Graph.RotationSystem.intersectionParity`: sum of passage-pair crossing bits.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.sum_alternates_eq_faceColors`: local telescoping.
* `Cslib.Complexity.Graph.RotationSystem.intersectionParity_eq_false`: closed-system parity.
-/

public section

namespace Cslib.Complexity.Graph


/-- A finite pairing of all actual darts of a Boolean edge support. This is the local
passage data of closed edge-disjoint routes; it need not consist of one connected route. -/
structure ClosedPassages (G : Graph) (x : Fin G.2.length → Bool) where
  /-- Number of indexed passages, including separate visits to the same vertex. -/
  count : ℕ
  /-- Exactly-once enumeration of both ends of every supported edge. The two ports of a
  passage are distinct because this map is an equivalence. -/
  ports : (Fin count × Bool) ≃ {d : Dart G // x d.1 = true}
  /-- Both ports of each passage are incident at the same original vertex. -/
  vertex_eq : ∀ i, (ports (i, false)).val.vertex = (ports (i, true)).val.vertex

namespace ClosedPassages

variable {G : Graph} {x : Fin G.2.length → Bool} (P : ClosedPassages G x)

/-- The actual indexed dart at one port of a passage. -/
@[expose] def dart (i : Fin P.count) (b : Bool) : Dart G := (P.ports (i, b)).val

/-- Every passage port belongs to the declared edge support. -/
theorem supported (i : Fin P.count) (b : Bool) : x (P.dart i b).1 = true :=
  (P.ports (i, b)).property

/-- The two ends of one passage are distinct, including passages through loop ends. -/
theorem dart_ne (i : Fin P.count) : P.dart i false ≠ P.dart i true := by
  intro h
  have := P.ports.injective (Subtype.ext h)
  exact Bool.false_ne_true (congrArg Prod.snd this)

/-- A dart sum over the support can be read as the sum over all indexed passage ports. -/
theorem sum_ports (f : Dart G → Bool) :
    (∑ i : Fin P.count, (f (P.dart i false) + f (P.dart i true))) =
      ∑ d : Dart G, if x d.1 = true then f d else 0 := by
  classical
  have hs : (∑ d : Dart G, if x d.1 = true then f d else 0) =
      ∑ d : {d : Dart G // x d.1 = true}, f d.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun d => by simp) f
  rw [hs]
  have h := Equiv.sum_comp P.ports (fun d => f d.val)
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, dart, add_comm] using h

include P in
/-- Exactly-once closed passage data have even parity at every original vertex. -/
theorem vertexEven : G.VertexEven x := by
  classical
  intro v
  have h := P.sum_ports (fun d => if d.vertex = v then true else false)
  have hz : (∑ i : Fin P.count,
      ((if (P.dart i false).vertex = v then true else false) +
      (if (P.dart i true).vertex = v then true else false))) = false := by
    apply Finset.sum_eq_zero
    intro i _
    rw [show (P.dart i false).vertex = (P.dart i true).vertex from P.vertex_eq i]
    exact BooleanRing.add_self _
  rw [hz] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro d _
  cases x d.1 <;> simp

end ClosedPassages

namespace RotationSystem

variable {G : Graph} (r : RotationSystem G)

open Classical in
/-- Number of literal forward rotations to the first visit to `b` from `a`. It is zero
when the endpoints are at different vertices, or when they coincide. -/
@[expose] noncomputable def rotationDistance (a b : Dart G) : ℕ :=
  if h : r.rotate.SameCycle a b then Nat.find h.exists_nat_pow_eq else 0

/-- Forward rotation reaches the terminal dart at the recorded distance. -/
theorem pow_rotationDistance (a b : Dart G) (h : a.vertex = b.vertex) :
    (r.rotate ^ r.rotationDistance a b) a = b := by
  classical
  rw [rotationDistance, dite_eq_left ((r.sameCycle_iff a b).mpr h)]
  exact Nat.find_spec ((r.sameCycle_iff a b).mpr h).exists_nat_pow_eq

/-- No earlier iterate reaches the terminal dart. -/
theorem pow_ne_of_lt_rotationDistance (a b : Dart G) (h : a.vertex = b.vertex)
    {k : ℕ} (hk : k < r.rotationDistance a b) : (r.rotate ^ k) a ≠ b := by
  classical
  rw [rotationDistance, dite_eq_left ((r.sameCycle_iff a b).mpr h)] at hk
  exact Nat.find_min _ hk

/-- A checked first-hit calculation determines the literal forward distance. This permits
finite clients to compute intervals without evaluating classical orbit decisions. -/
theorem rotationDistance_eq (a b : Dart G) (h : a.vertex = b.vertex) (n : ℕ)
    (hn : (r.rotate ^ n) a = b)
    (hmin : ∀ k < n, (r.rotate ^ k) a ≠ b) : r.rotationDistance a b = n := by
  classical
  rw [rotationDistance, dite_eq_left ((r.sameCycle_iff a b).mpr h)]
  exact (Nat.find_eq_iff _).mpr ⟨hn, hmin⟩

private theorem pow_injective_to_distance (a b : Dart G) (h : a.vertex = b.vertex)
    {i j : ℕ} (hi : i ≤ r.rotationDistance a b) (hj : j ≤ r.rotationDistance a b)
    (heq : (r.rotate ^ i) a = (r.rotate ^ j) a) : i = j := by
  wlog hij : i < j generalizing i j
  · rcases lt_trichotomy i j with hij | hij | hij
    · exact this hi hj heq hij
    · exact hij
    · exact (this hj hi heq.symm hij).symm
  have hn : r.rotationDistance a b - j + i < r.rotationDistance a b := by omega
  apply False.elim
  apply r.pow_ne_of_lt_rotationDistance a b h hn
  calc
    (r.rotate ^ (r.rotationDistance a b - j + i)) a =
        (r.rotate ^ (r.rotationDistance a b - j)) ((r.rotate ^ i) a) := by
      rw [pow_add, Equiv.Perm.mul_apply]
    _ = (r.rotate ^ (r.rotationDistance a b - j)) ((r.rotate ^ j) a) := congrArg _ heq
    _ = (r.rotate ^ r.rotationDistance a b) a := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hj]
    _ = b := r.pow_rotationDistance a b h

open Classical in
/-- The literal directed cyclic interval `(a,b]`: rotate forward from `a` to the first `b`,
excluding `a` and including `b`. For alternating passages all four darts are distinct, so
including the terminal dart makes no difference. Different endpoint vertices give `∅`. -/
@[expose] noncomputable def rotationInterval (a b : Dart G) : Finset (Dart G) :=
  (Finset.range (r.rotationDistance a b)).image fun k => (r.rotate ^ (k + 1)) a

/-- Every dart of the rotation interval is at its starting vertex. -/
theorem vertex_of_mem_rotationInterval (a b d : Dart G)
    (hd : d ∈ r.rotationInterval a b) : d.vertex = a.vertex := by
  classical
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hd
  exact (r.sameCycle_iff _ _).mp
    (Equiv.Perm.sameCycle_pow_right.mpr
      (Equiv.Perm.SameCycle.rfl (f := r.rotate) (x := a))).symm

/-- Interval sums telescope along the actual rotation, without any topological assumption. -/
theorem sum_rotationInterval (a b : Dart G) (h : a.vertex = b.vertex)
    (q : Dart G → Bool) :
    (∑ d ∈ r.rotationInterval a b, (q d + q (r.rotate.symm d))) = q b + q a := by
  classical
  rw [rotationInterval, Finset.sum_image]
  · have hstep (k : ℕ) : r.rotate.symm ((r.rotate ^ (k + 1)) a) = (r.rotate ^ k) a := by
      rw [pow_succ', Equiv.Perm.mul_apply, Equiv.symm_apply_apply]
    simp only [hstep, ← BooleanRing.sub_eq_add]
    rw [Finset.sum_range_sub (fun k => q ((r.rotate ^ k) a)),
      r.pow_rotationDistance a b h]
    simp only [pow_zero, Equiv.Perm.one_apply, BooleanRing.sub_eq_add]
  · intro i hi j hj heq
    have := r.pow_injective_to_distance a b h
      (i := i + 1) (j := j + 1) (by simpa using Finset.mem_range.mp hi)
      (by simpa using Finset.mem_range.mp hj) heq
    omega

/-- Adjacent face colors around a vertex differ by the boundary label on its intervening
actual dart. This is the precise orientation identity for `faceNext = rotate.symm ∘ reverse`. -/
theorem faceBoundary_rotate (q : r.Face → Bool) (d : Dart G) :
    r.faceBoundary q d.1 =
      q (Quotient.mk _ d) + q (Quotient.mk _ (r.rotate.symm d)) := by
  rw [r.faceBoundary_dart, ← Bool.add_eq_xor]
  congr 1
  apply congrArg q
  have hf := r.face_eq_next d.reverse
  change (Quotient.mk _ (r.rotate.symm d.reverse.reverse) : r.Face) = _ at hf
  rw [Dart.reverse_reverse] at hf
  exact hf.symm

/-- Boundary labels along a rotation interval telescope to its two incident face colors. -/
theorem sum_faceBoundary_rotationInterval (q : r.Face → Bool) (a b : Dart G)
    (h : a.vertex = b.vertex) :
    (∑ d ∈ r.rotationInterval a b, r.faceBoundary q d.1) =
      q (Quotient.mk _ b) + q (Quotient.mk _ a) := by
  simp only [r.faceBoundary_rotate]
  exact r.sum_rotationInterval a b h (fun d => q (Quotient.mk _ d))

open Classical in
/-- Two directed passages alternate in the literal rotation when their four actual darts
are distinct, they share a vertex, and exactly one end of the first is in the directed
interval between the second's ends. No reflection quotient is taken. -/
@[expose] noncomputable def Alternates (a b c d : Dart G) : Prop :=
  a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
    a.vertex = b.vertex ∧ c.vertex = d.vertex ∧ a.vertex = c.vertex ∧
    ((a ∈ r.rotationInterval c d) ↔ (b ∉ r.rotationInterval c d))

open Classical in
/-- For four distinct ports, the alternating bit is exactly the sum of the two interval
membership bits. The off-vertex case is zero because rotation intervals stay at one vertex. -/
theorem alternates_eq_interval (a b c d : Dart G)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hv : a.vertex = b.vertex)
    (hw : c.vertex = d.vertex) :
    decide (r.Alternates a b c d) =
      decide (a ∈ r.rotationInterval c d) + decide (b ∈ r.rotationInterval c d) := by
  classical
  by_cases hvc : a.vertex = c.vertex
  · have hbdv : b.vertex = d.vertex := hv.symm.trans (hvc.trans hw)
    by_cases ha : a ∈ r.rotationInterval c d <;>
      by_cases hb : b ∈ r.rotationInterval c d <;>
      simp [Alternates, hab, hcd, hac, had, hbc, hbd, hv, hw, hbdv, ha, hb,
        Bool.add_eq_xor]
  · have ha : a ∉ r.rotationInterval c d :=
      fun h => hvc (r.vertex_of_mem_rotationInterval c d a h)
    have hb : b ∉ r.rotationInterval c d :=
      fun h => hvc (hv.trans (r.vertex_of_mem_rotationInterval c d b h))
    simp [Alternates, hvc, ha, hb, Bool.add_eq_xor]

private theorem disjoint_ports_ne {x y : Fin G.2.length → Bool}
    (P : ClosedPassages G x) (Q : ClosedPassages G y)
    (hdisj : ∀ e, x e = true → y e = true → False)
    (i : Fin P.count) (j : Fin Q.count) (b c : Bool) : P.dart i b ≠ Q.dart j c := by
  intro h
  apply hdisj (P.dart i b).1 (P.supported i b)
  rw [h]
  exact Q.supported j c

open Classical in
/-- Against one passage of an edge-disjoint system, the sum of all alternating passage
pairs counts precisely the supported darts in its literal rotation interval. Local pairing
choices and multiple visits are unrestricted. -/
theorem sum_alternates_eq_interval {x y : Fin G.2.length → Bool}
    (P : ClosedPassages G x) (Q : ClosedPassages G y)
    (hdisj : ∀ e, x e = true → y e = true → False) (j : Fin Q.count) :
    (∑ i : Fin P.count, decide (r.Alternates
      (P.dart i false) (P.dart i true) (Q.dart j false) (Q.dart j true))) =
      ∑ d ∈ r.rotationInterval (Q.dart j false) (Q.dart j true), x d.1 := by
  classical
  calc
    _ = ∑ i : Fin P.count,
        (decide (P.dart i false ∈ r.rotationInterval (Q.dart j false) (Q.dart j true)) +
        decide (P.dart i true ∈ r.rotationInterval (Q.dart j false) (Q.dart j true))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact r.alternates_eq_interval _ _ _ _ (P.dart_ne i) (Q.dart_ne j)
        (disjoint_ports_ne P Q hdisj i j false false)
        (disjoint_ports_ne P Q hdisj i j false true)
        (disjoint_ports_ne P Q hdisj i j true false)
        (disjoint_ports_ne P Q hdisj i j true true) (P.vertex_eq i) (Q.vertex_eq j)
    _ = ∑ d : Dart G, if x d.1 = true then
        decide (d ∈ r.rotationInterval (Q.dart j false) (Q.dart j true)) else 0 :=
      P.sum_ports (fun d =>
        decide (d ∈ r.rotationInterval (Q.dart j false) (Q.dart j true)))
    _ = _ := by
      rw [← Finset.sum_ite_mem_eq
        (r.rotationInterval (Q.dart j false) (Q.dart j true)) (fun d => x d.1)]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hm : d ∈ r.rotationInterval (Q.dart j false) (Q.dart j true) <;>
        cases x d.1 <;> simp [hm, Bool.zero_eq_false]

open Classical in
/-- If the first support is a face boundary, its local alternating count along one passage
of an edge-disjoint system is the sum of the two incident face colors. -/
theorem sum_alternates_eq_faceColors {x y : Fin G.2.length → Bool}
    (P : ClosedPassages G x) (Q : ClosedPassages G y)
    (hdisj : ∀ e, x e = true → y e = true → False)
    (q : r.Face → Bool) (hq : r.faceBoundary q = x) (j : Fin Q.count) :
    (∑ i : Fin P.count, decide (r.Alternates
      (P.dart i false) (P.dart i true) (Q.dart j false) (Q.dart j true))) =
      q (Quotient.mk _ (Q.dart j true)) + q (Quotient.mk _ (Q.dart j false)) := by
  rw [r.sum_alternates_eq_interval P Q hdisj j, ← hq]
  exact r.sum_faceBoundary_rotationInterval q _ _ (Q.vertex_eq j)

open Classical in
/-- Total intersection parity of indexed passage pairs, using literal local alternation in
the actual rotation. Distinct visits and arbitrary local pairing choices are counted separately. -/
@[expose] noncomputable def intersectionParity {x y : Fin G.2.length → Bool}
    (P : ClosedPassages G x) (Q : ClosedPassages G y) : Bool :=
  ∑ j : Fin Q.count, ∑ i : Fin P.count, decide (r.Alternates
    (P.dart i false) (P.dart i true) (Q.dart j false) (Q.dart j true))

/-- Face-boundary support has even total intersection with every edge-disjoint closed
passage system, independently of genus. Adjacent face colors agree on the second support;
its exactly-once dart enumeration makes every endpoint contribution occur twice. -/
theorem intersectionParity_faceBoundary {x y : Fin G.2.length → Bool}
    (P : ClosedPassages G x) (Q : ClosedPassages G y)
    (hdisj : ∀ e, x e = true → y e = true → False)
    (q : r.Face → Bool) (hq : r.faceBoundary q = x) : r.intersectionParity P Q = false := by
  classical
  have hx (i : Fin G.2.length) (hi : y i = true) : x i = false := by
    cases he : x i
    · rfl
    · exact False.elim (hdisj i he hi)
  have hf (d : Dart G) (hd : y d.1 = true) :
      q (Quotient.mk _ d) = q (Quotient.mk _ d.reverse) := by
    have he := (r.faceBoundary_dart q d).symm.trans ((congrFun hq d.1).trans (hx d.1 hd))
    cases ha : q (Quotient.mk _ d) <;>
      cases hb : q (Quotient.mk _ d.reverse) <;> simp_all
  unfold intersectionParity
  simp only [r.sum_alternates_eq_faceColors P Q hdisj q hq, add_comm]
  rw [Q.sum_ports (fun d => q (Quotient.mk _ d))]
  simp only [Dart, Fintype.sum_prod_type, Fintype.sum_bool]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : y i = true
  · have he := hf (i, false) hi
    change q (Quotient.mk _ (i, false)) = q (Quotient.mk _ (i, true)) at he
    simp only [hi, ite_true, he, BooleanRing.add_self]
  · simp [hi]

/-- Any two supported edge-disjoint closed passage systems on a componentwise numerically
genus-zero rotation have even total local intersection parity. Endpoints must be declared;
vertex names may be sparse or duplicated, and loops, parallel edges, isolated vertices,
disconnected supports, multiple visits and arbitrary local pairings are allowed. All local
circular-order and parity facts are proved internally. No geometric or Hanani–Tutte premise
is assumed or concluded. -/
theorem intersectionParity_eq_false
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hgenus : r.NumericalGenusZero)
    {x y : Fin G.2.length → Bool} (P : ClosedPassages G x) (Q : ClosedPassages G y)
    (hdisj : ∀ e, x e = true → y e = true → False) :
    r.intersectionParity P Q = false := by
  obtain ⟨q, hq⟩ := (r.vertexEven_iff_exists_faceColors hG hgenus x).mp P.vertexEven
  exact r.intersectionParity_faceBoundary P Q hdisj q hq

end RotationSystem
end Cslib.Complexity.Graph
