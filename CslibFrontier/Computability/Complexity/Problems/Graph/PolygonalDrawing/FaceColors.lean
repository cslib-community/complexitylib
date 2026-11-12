/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SegmentArrangement
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Sectors

/-!
# Right-side colors of an embedded polygonal drawing

The construction uses one internally chosen ray direction, actual segment endpoints,
and angular prefix sums. Segment interiors transport colors, the two bend germs transport
them through each bend, and literal clockwise realization identifies the empty vertex sectors.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

variable {G : Graph} {D : PolygonalDrawing G}

open Classical in
private noncomputable def endpointSet (D : PolygonalDrawing G) : Finset ℂ :=
  Finset.univ.image D.segmentStart ∪ Finset.univ.image D.segmentFinish

private structure Frame (D : PolygonalDrawing G) where
  u : ℂ
  nonzero : u ≠ 0
  heights : Set.InjOn (fun z => (u * z).im) (↑(endpointSet D) : Set ℂ)

private def Frame.a (F : Frame D) (i : D.SegmentIndex) : ℂ := F.u * D.segmentStart i
private def Frame.b (F : Frame D) (i : D.SegmentIndex) : ℂ := F.u * D.segmentFinish i

private theorem Frame.mem_start (_F : Frame D) (i : D.SegmentIndex) :
    D.segmentStart i ∈ endpointSet D := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

private theorem Frame.mem_finish (_F : Frame D) (i : D.SegmentIndex) :
    D.segmentFinish i ∈ endpointSet D := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

private theorem Frame.endpoint (F : Frame D) (k : D.SegmentIndex × Bool) :
    rayEndpoint F.a F.b k = F.u * rayEndpoint D.segmentStart D.segmentFinish k := by
  rcases k with ⟨i, tag⟩
  cases tag <;> rfl

private theorem Frame.vector (F : Frame D) (k : D.SegmentIndex × Bool) :
    rayEndVector F.a F.b k = F.u * rayEndVector D.segmentStart D.segmentFinish k := by
  rcases k with ⟨i, tag⟩
  cases tag <;> simp [rayEndVector, a, b, mul_sub]

private theorem Frame.mem_endpoint (F : Frame D) (k : D.SegmentIndex × Bool) :
    rayEndpoint D.segmentStart D.segmentFinish k ∈ endpointSet D := by
  rcases k with ⟨i, tag⟩
  cases tag
  · exact F.mem_start i
  · exact F.mem_finish i

private theorem Frame.height (F : Frame D) (hD : D.IsEmbedding) (i : D.SegmentIndex) :
    (F.a i).im ≠ (F.b i).im := by
  intro h
  exact (hD.simple i.1).segment_ne i.2 (F.heights (F.mem_start i) (F.mem_finish i) h)

private theorem Frame.lineMap (F : Frame D) (i : D.SegmentIndex) (t : ℝ) :
    AffineMap.lineMap (F.a i) (F.b i) t =
      F.u * AffineMap.lineMap (D.segmentStart i) (D.segmentFinish i) t := by
  let f : ℂ →ₗ[ℝ] ℂ := (LinearMap.mulLeft ℂ F.u).restrictScalars ℝ
  exact (f.toAffineMap.apply_lineMap _ _ t).symm

private theorem Frame.disjoint (F : Frame D) (hD : D.IsEmbedding)
    (i j : D.SegmentIndex) (hne : j ≠ i) (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    AffineMap.lineMap (F.a i) (F.b i) t ∉ segment ℝ (F.a j) (F.b j) := by
  rw [segment_eq_image_lineMap]
  rintro ⟨s, hs, heq⟩
  rw [F.lineMap, F.lineMap] at heq
  have hpoint := mul_left_cancel₀ F.nonzero heq
  apply hD.segment_interior_disjoint i j hne t ht
  rw [← hpoint]
  exact lineMap_mem_segment ℝ _ _ hs

private theorem Frame.remote (F : Frame D) (hD : D.IsEmbedding)
    (k : D.SegmentIndex × Bool) (j : D.SegmentIndex)
    (ha : F.a j ≠ rayEndpoint F.a F.b k) (hb : F.b j ≠ rayEndpoint F.a F.b k) :
    (rayEndpoint F.a F.b k).im ≠ (F.a j).im ∧
      (rayEndpoint F.a F.b k).im ≠ (F.b j).im ∧
      rayEndpoint F.a F.b k ∉ segment ℝ (F.a j) (F.b j) := by
  have ha' : D.segmentStart j ≠ rayEndpoint D.segmentStart D.segmentFinish k := by
    intro h
    exact ha (by rw [F.endpoint]; exact congrArg (F.u * ·) h)
  have hb' : D.segmentFinish j ≠ rayEndpoint D.segmentStart D.segmentFinish k := by
    intro h
    exact hb (by rw [F.endpoint]; exact congrArg (F.u * ·) h)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [F.endpoint] at h
    exact ha' (F.heights (F.mem_endpoint k) (F.mem_start j) h).symm
  · intro h
    rw [F.endpoint] at h
    exact hb' (F.heights (F.mem_endpoint k) (F.mem_finish j) h).symm
  · rw [segment_eq_image_lineMap]
    rintro ⟨t, ht, heq⟩
    rw [F.lineMap, F.endpoint] at heq
    have hpoint := mul_left_cancel₀ F.nonzero heq
    have hp : rayEndpoint D.segmentStart D.segmentFinish k ∈
        segment ℝ (D.segmentStart j) (D.segmentFinish j) :=
      hpoint ▸ lineMap_mem_segment ℝ _ _ ht
    exact (hD.segment_endpoint_contact k j hp).elim ha' hb'

private theorem Frame.distinct (F : Frame D) (hD : D.IsEmbedding)
    (k e : D.SegmentIndex × Bool) (hp : rayEndpoint F.a F.b e = rayEndpoint F.a F.b k)
    (harg : turnArg (rayEndVector F.a F.b e) = turnArg (rayEndVector F.a F.b k)) : e = k :=
  rayEndVector_injective_of_interior_disjoint F.a F.b
    (fun i h => F.height hD i (congrArg Complex.im h)) (F.disjoint hD) k e hp harg

private theorem Frame.even (F : Frame D) (x : Fin G.2.length → Bool) (hx : G.VertexEven x)
    (p : ℂ) :
    (∑ i : D.SegmentIndex, ((if F.a i = p then x i.1 else 0) +
      (if F.b i = p then x i.1 else 0))) = false :=
  D.segment_endpoints_even x hx F.u p

private noncomputable def Frame.color (F : Frame D) (x : Fin G.2.length → Bool)
    (k : D.SegmentIndex × Bool) : Bool :=
  rayGermColor F.a F.b (fun i => x i.1) (rayEndpoint F.a F.b k) (rayEndVector F.a F.b k)

private theorem Frame.color_adjacent (F : Frame D) (hD : D.IsEmbedding)
    (x : Fin G.2.length → Bool) (hx : G.VertexEven x) (p : ℂ)
    (k l : D.SegmentIndex × Bool)
    (hk : rayEndpoint F.a F.b k = p) (hl : rayEndpoint F.a F.b l = p) (hkl : k ≠ l)
    (hgap : ∀ j : D.SegmentIndex × Bool, rayEndpoint F.a F.b j = p → j ≠ k → j ≠ l →
      ¬sbtw ((rayEndVector F.a F.b k).arg : Real.Angle)
        ((rayEndVector F.a F.b j).arg : Real.Angle)
        ((rayEndVector F.a F.b l).arg : Real.Angle)) :
    F.color x k + F.color x l = x k.1.1 := by
  unfold Frame.color
  rw [hk, hl]
  exact rayGermColor_adjacent F.a F.b (fun i => x i.1) (F.height hD) p
    (F.even x hx p) k l hk hl hkl
    (fun j f hj hf h => F.distinct hD f j (hj.trans hf.symm) h) hgap

private theorem Frame.color_ends (F : Frame D) (hD : D.IsEmbedding)
    (x : Fin G.2.length → Bool) (hx : G.VertexEven x) (i : D.SegmentIndex) :
    F.color x (i, false) + F.color x (i, true) = x i.1 := by
  exact rayGermColor_ends F.a F.b (fun i => x i.1) (F.height hD) (F.even x hx) i
    (F.disjoint hD i) (F.remote hD) (F.distinct hD)

private theorem Frame.color_bend (F : Frame D) (hD : D.IsEmbedding)
    (x : Fin G.2.length → Bool) (hx : G.VertexEven x)
    (e : Fin G.2.length) (i : Fin (D.route e).bends) :
    F.color x (⟨e, i.castSucc⟩, true) + F.color x (⟨e, i.succ⟩, false) = x e := by
  let k : D.SegmentIndex × Bool := (⟨e, i.castSucc⟩, true)
  let l : D.SegmentIndex × Bool := (⟨e, i.succ⟩, false)
  let p := F.u * (D.route e).point i.castSucc.succ
  have hk : rayEndpoint F.a F.b k = p := rfl
  have hl : rayEndpoint F.a F.b l = p := rfl
  have hkl : k ≠ l := by
    intro h
    have := congrArg Prod.snd h
    exact Bool.false_ne_true this.symm
  have hclass (j : D.SegmentIndex × Bool) (hj : rayEndpoint F.a F.b j = p) :
      j = k ∨ j = l := by
    rw [F.endpoint] at hj
    exact hD.segment_ends_at_bend e i j (mul_left_cancel₀ F.nonzero hj)
  have hgap (j : D.SegmentIndex × Bool) (hj : rayEndpoint F.a F.b j = p)
      (hjk : j ≠ k) (hjl : j ≠ l) :
      ¬sbtw ((rayEndVector F.a F.b k).arg : Real.Angle)
        ((rayEndVector F.a F.b j).arg : Real.Angle)
        ((rayEndVector F.a F.b l).arg : Real.Angle) := by
    exact ((hclass j hj).elim hjk hjl).elim
  exact F.color_adjacent hD x hx p k l hk hl hkl hgap

private theorem Frame.color_bend_transport (F : Frame D) (hD : D.IsEmbedding)
    (x : Fin G.2.length → Bool) (hx : G.VertexEven x)
    (e : Fin G.2.length) (i : Fin (D.route e).bends) :
    F.color x (⟨e, i.castSucc⟩, false) = F.color x (⟨e, i.succ⟩, false) := by
  have h := (F.color_ends hD x hx ⟨e, i.castSucc⟩).trans (F.color_bend hD x hx e i).symm
  rw [add_comm (F.color x (⟨e, i.castSucc⟩, false))] at h
  exact add_left_cancel h

private theorem Frame.color_route_ends (F : Frame D) (hD : D.IsEmbedding)
    (x : Fin G.2.length → Bool) (hx : G.VertexEven x) (e : Fin G.2.length) :
    F.color x (D.segmentEnd (e, false)) + F.color x (D.segmentEnd (e, true)) = x e := by
  have hstart (i : Fin (D.route e).segments) :
      F.color x (⟨e, 0⟩, false) = F.color x (⟨e, i⟩, false) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact ih.trans (F.color_bend_transport hD x hx e i)
  have h := F.color_ends hD x hx ⟨e, Fin.last (D.route e).bends⟩
  rw [← hstart (Fin.last (D.route e).bends)] at h
  exact h

private theorem Frame.color_vertex (F : Frame D) (hD : D.IsEmbedding)
    {r : RotationSystem G} (hR : D.Realizes r)
    (x : Fin G.2.length → Bool) (hx : G.VertexEven x)
    (d : Dart G) (hv : d.vertex ∈ G.1) :
    F.color x (D.segmentEnd d) + F.color x (D.segmentEnd (r.rotate.symm d)) = x d.1 := by
  classical
  let a := r.rotate.symm d
  let k := D.segmentEnd d
  let l := D.segmentEnd a
  let p := F.u * D.vertex d.vertex
  have har : r.rotate a = d := r.rotate.apply_symm_apply d
  have hav : a.vertex = d.vertex := by rw [← har, r.vertex_rotate]
  have hk : rayEndpoint F.a F.b k = p := by rw [F.endpoint, D.segmentEnd_endpoint]
  have hl : rayEndpoint F.a F.b l = p := by rw [F.endpoint, D.segmentEnd_endpoint, hav]
  have hclass (j : D.SegmentIndex × Bool) (hj : rayEndpoint F.a F.b j = p) :
      ∃ c : Dart G, c.vertex = d.vertex ∧ D.segmentEnd c = j := by
    rw [F.endpoint] at hj
    exact hD.segment_end_at_vertex d.vertex hv j (mul_left_cancel₀ F.nonzero hj)
  by_cases had : a = d
  · have hfixed : r.rotate d = d := by simpa only [had] using har
    have honly (j : D.SegmentIndex × Bool) (hj : rayEndpoint F.a F.b j = p) : j = k := by
      obtain ⟨c, hcv, hc⟩ := hclass j hj
      have hcd : c = d := ((r.sameCycle_iff c d).mpr hcv).eq_of_right hfixed
      simpa only [hcd] using hc.symm
    have hsum : (∑ j : D.SegmentIndex × Bool,
        if rayEndpoint F.a F.b j = p then x j.1.1 else 0) = x d.1 := by
      rw [Finset.sum_eq_single k]
      · rw [ite_eq_left hk]
        rfl
      · intro j _ hj
        have hpoint : rayEndpoint F.a F.b j ≠ p := fun hp => hj (honly j hp)
        simp only [hpoint, ↓reduceIte]
      · simp
    have heven : (∑ j : D.SegmentIndex × Bool,
        if rayEndpoint F.a F.b j = p then x j.1.1 else 0) = 0 := by
      simpa only [Fintype.sum_prod_type, Fintype.sum_bool, rayEndpoint,
        Bool.false_eq_true, ↓reduceIte, add_comm, Bool.zero_eq_false] using F.even x hx p
    have hx0 : x d.1 = 0 := hsum.symm.trans heven
    change F.color x k + F.color x l = x d.1
    have hkl : l = k := congrArg D.segmentEnd had
    rw [hkl, BooleanRing.add_self, hx0]
  · have hkl : k ≠ l := fun h => had (D.segmentEnd_injective h.symm)
    have hgap (j : D.SegmentIndex × Bool) (hj : rayEndpoint F.a F.b j = p)
        (hjk : j ≠ k) (hjl : j ≠ l) :
        ¬sbtw ((rayEndVector F.a F.b k).arg : Real.Angle)
          ((rayEndVector F.a F.b j).arg : Real.Angle)
          ((rayEndVector F.a F.b l).arg : Real.Angle) := by
      obtain ⟨c, hcv, hc⟩ := hclass j hj
      have hcd : c ≠ d := fun h => hjk (by rw [← hc, h])
      have hca : c ≠ a := fun h => hjl (by rw [← hc, h])
      rw [← hc]
      change ¬sbtw ((rayEndVector F.a F.b (D.segmentEnd d)).arg : Real.Angle)
        ((rayEndVector F.a F.b (D.segmentEnd c)).arg : Real.Angle)
        ((rayEndVector F.a F.b (D.segmentEnd a)).arg : Real.Angle)
      simp only [F.vector, D.segmentEnd_vector]
      rw [sbtw_arg_mul_iff F.u (D.germ d) (D.germ c) (D.germ a) F.nonzero
        (hR.nonzero d) (hR.nonzero c) (hR.nonzero a)]
      exact hR.not_sbtw_inverse_rotate d c hcv hcd hca
    exact F.color_adjacent hD x hx p k l hk hl hkl hgap

/-- Every vertex-even indexed edge label of an actual polygonal embedding is the
boundary of colors on the actual face quotient of the literally realized clockwise
rotation. The multiplier and all side transport are constructed internally from the
finite real-affine segments. No genus or topological separation hypothesis is used. -/
theorem IsEmbedding.exists_faceColors {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) {r : RotationSystem G} (hR : D.Realizes r)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (x : Fin G.2.length → Bool) (hx : G.VertexEven x) :
    ∃ q : r.Face → Bool, r.faceBoundary q = x := by
  classical
  obtain ⟨u, hu, hheight⟩ := exists_mul_im_injOn (endpointSet D)
  let F : Frame D := ⟨u, hu, hheight⟩
  let color (d : Dart G) : Bool := F.color x (D.segmentEnd d)
  have hedge (d : Dart G) : color d + color d.reverse = x d.1 := by
    rcases d with ⟨e, tag⟩
    cases tag
    · exact F.color_route_ends hD x hx e
    · exact (add_comm _ _).trans (F.color_route_ends hD x hx e)
  have hnext (d : Dart G) : color (r.faceNext d) = color d := by
    have hv := F.color_vertex hD hR x hx d.reverse (RotationSystem.vertex_mem hG d.reverse)
    have h := (hedge d).trans hv.symm
    rw [add_comm (color d)] at h
    exact (add_left_cancel h).symm
  have hcycle (a b : Dart G) (h : r.faceNext.SameCycle a b) : color a = color b := by
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    have hp (n : ℕ) : color ((r.faceNext ^ n) a) = color a := by
      induction n with
      | zero => rfl
      | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, hnext] using ih
    rw [← hn, hp]
  let q : r.Face → Bool := Quotient.lift color hcycle
  refine ⟨q, funext fun e => ?_⟩
  exact hedge (e, false)

end Cslib.Complexity.Graph.PolygonalDrawing
