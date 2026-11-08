/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.TraceParameters
public import Complexity.Cryptanalysis.AddXNORNativeClassPrepare
public import Complexity.Cryptanalysis.AddXNORNativeQuarterProjection
import all Complexity.Computability.WordRAM.Structured
import all Complexity.Cryptanalysis.AddXNORNativeClassSemantics
import all Complexity.Cryptanalysis.AddXNORNativeClassRetain
import all Complexity.Cryptanalysis.AddXNORNativeClassProbe
import all Complexity.Cryptanalysis.AddXNORNativeProjection

/-!
# Complete native search of one low-bit class

From original operand arrays, construct the projected middle quarters and both
quarter bucket families, retain the complete forward class, and stream the entire
opposite class with early exit. The tag is nonzero exactly when the selected
class contains a solution, and returned registers reconstruct the original chain.
These are the native class-level completeness and finite instruction-time
components of [WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22.
Counter-selected orientation, iteration across classes, global computed-balance
resources and the source multitape bit model remain separate.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Native projection of both original middle quarters, in the needed orders. -/
@[expose] def projectMiddle (c n₂ b₃ n₃ q₂ q₃ N : ℕ) : Code .standard 32 :=
  .seq (projectQuarter c q₂ n₂ N true) (projectQuarter b₃ q₃ n₃ N true)

private theorem projectMiddle_exec {W m p c b₃ q₂ q₃ : ℕ}
    (bs cs : List (BitVec m)) (x : Data 32)
    (hsecond : ∀ i (hi : i < bs.length), x.mem (c + i) = bs[i].toNat)
    (hthird : ∀ i (hi : i < cs.reverse.length), x.mem (b₃ + i) = cs.reverse[i].toNat)
    (hend₂ : c + bs.length ≤ q₂) (hend₃ : b₃ + cs.length ≤ q₂)
    (hscratch : q₂ + bs.length ≤ q₃)
    (hfit : Fits W (q₂ + q₃ + bs.length + cs.length + 2 ^ p + 8)) :
    ∃ y, ExecWithin W (projectMiddle c bs.length b₃ cs.length q₂ q₃ (2 ^ p)) x y
        ((10 * bs.length + 8) + (10 * cs.length + 8)) ∧
      (∀ i (hi : i < (bs.map (BitVec.setWidth p)).reverse.length),
        y.mem (q₂ + i) = (bs.map (BitVec.setWidth p)).reverse[i].toNat) ∧
      (∀ i (hi : i < (cs.map (BitVec.setWidth p)).length),
        y.mem (q₃ + i) = (cs.map (BitVec.setWidth p))[i].toNat) ∧
      (∀ a, a < q₂ ∨ q₃ + cs.length ≤ a → y.mem a = x.mem a) := by
  have hN := Nat.two_pow_pos p
  obtain ⟨z, hz, zm, zf⟩ := projectQuarter_exec (p := p) (a := c) (b := q₂) true bs x
    hsecond hend₂ (hfit.of_le (by omega))
  obtain ⟨y, hy, ym, yf⟩ := projectQuarter_exec (p := p) (a := b₃) (b := q₃) true cs.reverse z
    (by intro i hi; rw [zf _ (by simp only [List.length_reverse] at hi; omega)];
        exact hthird i hi)
    (by simp only [List.length_reverse]; omega)
    (hfit.of_le (by simp only [List.length_reverse]; omega))
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · simpa only [projectMiddle, List.length_reverse] using hz.seq hy
  · intro i hi
    have hi' : i < bs.length := by simpa using hi
    rw [yf _ (by simp only [List.length_reverse]; omega), zm]
    simp [Counters.projectedPrefix, hi', List.map_reverse]
  · intro i hi
    have hi' : i < cs.length := by simpa using hi
    rw [ym]; simp [Counters.projectedPrefix, hi']
  · intro a ha
    rw [yf _ (by simp only [List.length_reverse]; omega), zf _ (by omega)]

/-- Transfer the class-loop layout, including the raw class value. -/
@[expose] def classLayout (b q n M N g h D : ℕ) : Code .standard 32 :=
  ram[ fullBase ← #b; projectedBase ← #q; count ← #n; fullModulus ← #M;
    projectedModulus ← #N; initial ← #g; heads ← #h; Dictionary.table ← #D ]

private theorem classLayout_exec {W : ℕ} (b q n M N g h D : ℕ) (x : Data 32)
    (hfit : Fits W (b + q + n + M + N + g + h + D)) :
    ExecWithin W (classLayout b q n M N g h D) x
      (x.set fullBase b |>.set projectedBase q |>.set count n |>.set fullModulus M
        |>.set projectedModulus N |>.set initial g |>.set heads h |>.set Dictionary.table D) 8 := by
  have hb : Fits W b := hfit.of_le (by omega)
  have hq : Fits W q := hfit.of_le (by omega)
  have hn : Fits W n := hfit.of_le (by omega)
  have hM : Fits W M := hfit.of_le (by omega)
  have hN : Fits W N := hfit.of_le (by omega)
  have hg : Fits W g := hfit.of_le (by omega)
  have hh : Fits W h := hfit.of_le (by omega)
  have hD : Fits W D := hfit.of_le (by omega)
  ram_eval [classLayout, hb, hq, hn, hM, hN, hg, hh, hD, fullBase, projectedBase, count,
    fullModulus, projectedModulus, initial, heads, Dictionary.table, Fin.mk.injEq]

/-- Both complete class iterators, with a natively computed streaming bound. -/
@[expose] def searchPreparedClass (c n₂ b₃ n₃ q₂ q₃ M N g h h₄ D : ℕ) : Code .standard 32 :=
  .seq (classLayout c q₂ n₂ M N g h D)
    (.seq retainClass (.seq (classLayout b₃ q₃ n₃ M N g h₄ D)
      (.seq (ram[ one ← #1; stop ← one <<< count ]) probeClass)))

/-- Original-input search of one selected low-bit class. No packed index or
precomputed correct bucket/query is an input: both middle words are loop counters. -/
@[expose] def searchClass (b n₁ c n₂ b₃ n₃ b₄ n₄ q₂ q₃ M N s t g h f h₄ f₄ D : ℕ) :
    Code .standard 32 :=
  .seq (projectMiddle c n₂ b₃ n₃ q₂ q₃ N)
    (.seq (prepareClassBuckets b n₁ b₄ n₄ M s t h f h₄ f₄ N)
      (searchPreparedClass c n₂ b₃ n₃ q₂ q₃ M N g h h₄ D))

/-- Stores charged to one search. The entire opposite-class streaming phase
is write-free, so its potentially much larger duration is absent. -/
def searchStores {m p : ℕ} (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) : ℕ :=
  ((10 * bs.length + 8) + (10 * cs.length + 8)) +
    ((7 + (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10) +
      (7 + (4 * 2 ^ p + 2 ^ ds.length * (18 * ds.length + 37) + 10))) +
      (8 + ((5 + classRetainTime bs g (fun k => Forward.records as s p k.toNat)
        0 (2 ^ bs.length)) + (8 + (2 + 0)))))

/-- General original-array class decision, witness soundness, derived dictionary
validity and finite native time. Every premise is about raw inputs, layout or
word capacity; no traversal, termination or semantic dictionary is assumed. -/
theorem searchClass_exec {W m p b c b₃ b₄ q₂ q₃ h f h₄ f₄ D : ℕ}
    (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p) (x : Data 32)
    (hfirst : ∀ i (hi : i < as.length), x.mem (b + i) = as[i].toNat)
    (hsecond : ∀ i (hi : i < bs.length), x.mem (c + i) = bs[i].toNat)
    (hthird : ∀ i (hi : i < cs.reverse.length), x.mem (b₃ + i) = cs.reverse[i].toNat)
    (hfourth : ∀ i (hi : i < ds.reverse.length), x.mem (b₄ + i) = ds.reverse[i].toNat)
    (hend₁ : b + as.length ≤ q₂) (hend₂ : c + bs.length ≤ q₂)
    (hend₃ : b₃ + cs.length ≤ q₂) (hend₄ : b₄ + ds.length ≤ q₂)
    (hproj : q₂ + bs.length ≤ q₃) (hprojEnd : q₃ + cs.length ≤ h)
    (hfpos : 0 < f) (hheads : h + 2 ^ p ≤ f)
    (harenas : f + 3 * 2 ^ as.length ≤ h₄) (hheads₄ : h₄ + 2 ^ p ≤ f₄)
    (hboundary : f₄ + 3 * 2 ^ ds.length ≤ D)
    (hzero : ∀ a, D ≤ a → x.mem a = 0)
    (hfit : Fits W (4 * (b + c + b₃ + b₄ + q₂ + q₃ + h + f + h₄ + f₄ + D +
      as.length + bs.length + cs.length + ds.length) + 20 * 2 ^ m + 10 * 2 ^ p +
      10 * 2 ^ as.length + 10 * 2 ^ bs.length + 10 * 2 ^ cs.length +
      10 * 2 ^ ds.length + 64)) :
    let fs := fun k : BitVec p => Forward.records as s p k.toNat
    let rs := inverseRecords ds t p
    let es := classEntries bs g fs 0 (2 ^ bs.length)
    ∃ y, ExecWithin W
        (searchClass b as.length c bs.length b₃ cs.length b₄ ds.length q₂ q₃
          (2 ^ m) (2 ^ p) s.toNat t.toNat g.toNat h f h₄ f₄ D) x y
        (((10 * bs.length + 8) + (10 * cs.length + 8)) +
          ((7 + (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10) +
            (7 + (4 * 2 ^ p + 2 ^ ds.length * (18 * ds.length + 37) + 10))) +
            (8 + ((5 + classRetainTime bs g fs 0 (2 ^ bs.length)) +
              (8 + (2 + (4 + classProbeTime cs g rs 0 (2 ^ cs.length)))))))) ∧
      StoresWithin W
        (searchClass b as.length c bs.length b₃ cs.length b₄ ds.length q₂ q₃
          (2 ^ m) (2 ^ p) s.toNat t.toNat g.toNat h f h₄ f₄ D) x y
        (((10 * bs.length + 8) + (10 * cs.length + 8)) +
          ((7 + (4 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) + 10) +
            (7 + (4 * 2 ^ p + 2 ^ ds.length * (18 * ds.length + 37) + 10))) +
            (8 + ((5 + classRetainTime bs g fs 0 (2 ^ bs.length)) +
              (8 + (2 + (4 + classProbeTime cs g rs 0 (2 ^ cs.length))))))))
        (searchStores as bs cs ds s g) ∧
      (y.regs operand ≠ 0 ↔ PackedClassSolution as bs cs ds s t g) ∧
      (y.regs operand = 0 ↔ ¬PackedClassSolution as bs cs ds s t g) ∧
      (y.regs operand ≠ 0 →
        eval (((decode as.length (y.regs operand - 1)).zip as) ++
          ((decode bs.length (y.regs bits)).zip bs) ++
          ((decode cs.length (y.regs operators)).zip cs) ++
          ((decode ds.length (y.regs firstOperators)).zip ds)) s = t) ∧
      (y.regs operand ≠ 0 → y.regs operand - 1 < 2 ^ as.length ∧
        y.regs bits < 2 ^ bs.length ∧ y.regs operators < 2 ^ cs.length ∧
        y.regs firstOperators < 2 ^ ds.length) ∧
      ∃ keys, Dictionary.Valid y.mem D (y.regs Dictionary.top) keys ∧ keys.length ≤ es.length ∧
        (∀ a, a < q₂ → y.mem a = x.mem a) ∧
        (∀ a, D ≤ a → Dictionary.erasedMemory y.mem D keys a = 0) ∧
        (∀ k ∈ keys, k < 2 ^ m) ∧ y.regs Dictionary.table = D := by
  dsimp only
  have hA := Nat.two_pow_pos as.length
  have hB := Nat.two_pow_pos bs.length
  have hC := Nat.two_pow_pos cs.length
  have hE := Nat.two_pow_pos ds.length
  have hP := Nat.two_pow_pos p
  let fs := fun k : BitVec p => Forward.records as s p k.toNat
  let rs := inverseRecords ds t p
  let es := classEntries bs g fs 0 (2 ^ bs.length)
  obtain ⟨z, hz, z₂, z₃, zframe⟩ := projectMiddle_exec (p := p) bs cs x hsecond hthird
    hend₂ hend₃ hproj (hfit.of_le (by omega))
  obtain ⟨u, hu, _, uf, ur, uframe⟩ := prepareClassBuckets_exec
    (W := W) (b := b) (b₄ := b₄) (h := h) (f := f) (h₄ := h₄) (f₄ := f₄) (D := D)
    as ds s t z
    (by intro i hi; rw [zframe _ (Or.inl (by omega))]; exact hfirst i hi)
    (by intro i hi; rw [zframe _ (Or.inl (by simp only [List.length_reverse] at hi; omega))];
        exact hfourth i hi)
    (by omega) (by omega) hfpos hheads harenas hheads₄ hboundary (hfit.of_le (by omega))
  have original (a : ℕ) (ha : a < q₂ ∨ D ≤ a) : u.mem a = x.mem a := by
    rw [uframe _ (by omega), zframe _ (by omega)]
  have low₂ (i : ℕ) (hi : i < (bs.map (BitVec.setWidth p)).reverse.length) :
      u.mem (q₂ + i) = (bs.map (BitVec.setWidth p)).reverse[i].toNat := by
    rw [uframe _ (Or.inl (by simp only [List.length_reverse, List.length_map] at hi; omega))]
    exact z₂ i hi
  have low₃ (i : ℕ) (hi : i < (cs.map (BitVec.setWidth p)).length) :
      u.mem (q₃ + i) = (cs.map (BitVec.setWidth p))[i].toNat := by
    rw [uframe _ (Or.inl (by simp only [List.length_map] at hi; omega))]; exact z₃ i hi
  let r := u.set fullBase c |>.set projectedBase q₂ |>.set count bs.length
    |>.set fullModulus (2 ^ m) |>.set projectedModulus (2 ^ p)
    |>.set initial g.toNat |>.set heads h |>.set Dictionary.table D
  have layout := classLayout_exec c q₂ bs.length (2 ^ m) (2 ^ p) g.toNat h D u
    (hfit.of_le (by have := g.isLt; omega))
  have empty (a : ℕ) (ha : D ≤ a) : r.mem a = 0 := (original a (Or.inr ha)).trans (hzero a ha)
  obtain ⟨v, hv, vm, vt, _, keys, vk, vlen, vrestore⟩ := retainClass_exec
    (W := W) (a := as.length) (b := c) (q := q₂) (h := h) (D := D)
    (boundary := f + 3 * 2 ^ as.length) bs g fs r
    (by simp +decide [r, fullBase, projectedBase, count, fullModulus, projectedModulus,
      initial, heads, Dictionary.table])
    (by simp +decide [r, projectedBase, count, fullModulus, projectedModulus,
      initial, heads, Dictionary.table])
    (by simp +decide [r, fullModulus, projectedModulus, initial, heads, Dictionary.table])
    (by simp +decide [r, projectedModulus, initial, heads, Dictionary.table])
    (by simp +decide [r, count, fullModulus, projectedModulus, initial, heads, Dictionary.table])
    (by simp +decide [r, initial, heads, Dictionary.table])
    (by simp +decide [r, heads, Dictionary.table]) (by simp [r])
    (by intro i hi; change u.mem _ = _
        rw [original _ (Or.inl (by omega))]; exact hsecond i hi) low₂ uf
    (by intro k r hr; have hh := (mem_forwardRecords as s k r).mp hr
        rw [hh.2.1]; exact (eval ((decode as.length r.2).zip as) s).isLt)
    (by intro k r hr; exact ((mem_forwardRecords as s k r).mp hr).1)
    (by omega) (by omega) (by omega) (by omega) empty (hfit.of_le (by omega))
  have frame (a : ℕ) (ha : a < D) : v.mem a = u.mem a := by
    rw [vm, Dictionary.filledMemory_below _ _ _ _ _ ha]
    rfl
  let ready := v.set fullBase b₃ |>.set projectedBase q₃ |>.set count cs.length
    |>.set fullModulus (2 ^ m) |>.set projectedModulus (2 ^ p)
    |>.set initial g.toNat |>.set heads h₄ |>.set Dictionary.table D
  have layout₃ := classLayout_exec b₃ q₃ cs.length (2 ^ m) (2 ^ p) g.toNat h₄ D v
    (hfit.of_le (by have := g.isLt; omega))
  let start := ready.set one 1 |>.set stop (2 ^ cs.length)
  have limit : ExecWithin (B := .standard) W (ram[ one ← #1; stop ← one <<< count ])
      ready start 2 := by
    have h1 : Fits W 1 := hfit.of_le (by omega)
    have hn : Fits W (2 ^ cs.length) := hfit.of_le (by omega)
    have hc : ready.regs count = cs.length := by
      simp +decide [ready, count, fullModulus, projectedModulus, initial, heads, Dictionary.table]
    ram_eval [start, h1, hn, hc, Nat.shiftLeft_eq, one_mul, one, count, stop, Fin.mk.injEq]
  obtain ⟨y, hy, ym, yh, _, yw⟩ := probeClass_exec
    (W := W) (b := b₃) (q := q₃) (h := h₄) (D := D) (boundary := f₄ + 3 * 2 ^ ds.length)
    cs g rs start
    (by simp +decide [start, ready, fullBase, projectedBase, count, fullModulus,
      projectedModulus, initial, heads, Dictionary.table, one, stop])
    (by simp +decide [start, ready, projectedBase, count, fullModulus,
      projectedModulus, initial, heads, Dictionary.table, one, stop])
    (by simp +decide [start, ready, fullModulus, projectedModulus, initial, heads,
      Dictionary.table, one, stop])
    (by simp +decide [start, ready, projectedModulus, initial, heads, Dictionary.table, one, stop])
    (by simp +decide [start, ready, count, fullModulus, projectedModulus, initial,
      heads, Dictionary.table, one, stop])
    (by simp +decide [start, ready, initial, heads, Dictionary.table, one, stop])
    (by simp +decide [start, ready, heads, Dictionary.table, one, stop])
    (by simp +decide [start, ready, Dictionary.table, one, stop]) (by simp [start])
    (by
      intro i hi
      have hi' : i < cs.length := by simpa only [List.length_reverse] using hi
      change v.mem _ = _
      rw [frame _ (by omega), original _ (Or.inl (by omega))]
      exact hthird i hi)
    (by
      intro i hi
      have hi' : i < cs.length := by simpa only [List.length_map] using hi
      change v.mem _ = _
      rw [frame _ (by omega)]
      exact low₃ i hi)
    (by intro k; change Linked v.mem _ (v.mem _) _
        rw [frame _ (by have := k.isLt; omega)]
        exact (ur k).frame (fun a ha => frame a (by omega)))
    (by intro k r hr; have hh := (mem_inverseRecords ds t k r).mp hr
        rw [hh.2.1]; exact (backward ((decode ds.length r.2).zip ds) t).isLt)
    (hfit.of_le (by omega))
  have tag : y.regs operand ≠ 0 ↔ PackedClassSolution as bs cs ds s t g := by
    rw [yh]
    change (∃ w < 2 ^ cs.length, ClassHit cs g rs v.mem D w) ↔ _
    rw [vm]
    exact nativeClassHit_iff hp as bs cs ds s t g D r.mem
      (fun q => empty _ (by simp only [Dictionary.slot]; omega))
  refine ⟨y, hz.seq (hu.seq (layout.seq (hv.seq (layout₃.seq (limit.seq hy))))),
    ?_, tag, ?_, ?_, ?_, keys, ?_, vlen, ?_, ?_, ?_, ?_⟩
  · exact hz.stores.seq (hu.stores.seq (layout.stores.seq (hv.stores.seq
      (layout₃.stores.seq (limit.stores.seq (hy.withoutStores (by decide)))))))
  · constructor
    · intro hz hs; exact (tag.mpr hs) hz
    · intro hn; by_contra hz; exact hn (tag.mp hz)
  · intro hit
    obtain ⟨_, _, r', hr', hu', hs', ht', hb'⟩ := yw hit
    apply nativeClassWitness_sound hp as bs cs ds s t g D r.mem y
      (fun q => empty _ (by simp only [Dictionary.slot]; omega)) hit
    refine ⟨r', hr', hu', hs', ?_, ?_⟩
    · simpa only [start, ready, Data.set_mem, vm] using ht'
    · simpa only [start, ready, Data.set_mem, vm] using hb'
  · intro hit
    obtain ⟨hc, _, r', hr', hu', _, ht', hb'⟩ := yw hit
    have ht : y.regs operand = Dictionary.filledMemory D es r.mem 0
        (Dictionary.slot D (y.regs state)) := by
      simpa only [start, ready, Data.set_mem, vm, es] using ht'
    have hb : y.regs bits = Dictionary.filledMemory D es r.mem 0
        (Dictionary.slot D (y.regs state) + 1) := by
      simpa only [start, ready, Data.set_mem, vm, es] using hb'
    obtain ⟨e, he, _, hf, hv⟩ := Dictionary.filledMemory_provenance D es r.mem 0
      (y.regs state) (empty _ (by simp only [Dictionary.slot]; omega)) (by rwa [← ht])
    have hF := (mem_forwardClass hp as bs s g e).mp he
    have hB := (mem_inverseRecords ds t (classQuery cs g (y.regs operators)) r').mp hr'
    refine ⟨?_, ?_, hc, ?_⟩
    · rw [ht.trans hf, Nat.add_sub_cancel]; exact hF.1
    · rw [hb.trans hv]; exact hF.2.1
    · rw [hu']; exact hB.1
  · have yt : y.regs Dictionary.top = v.regs Dictionary.top :=
      ((layout₃.seq (limit.seq hy)).regs_eq (by
        unfold classLayout
        simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
        decide))
    simpa only [yt, ym, start, ready, Data.set_mem] using vk
  · intro a ha
    rw [ym]
    change v.mem a = x.mem a
    rw [frame _ (by omega), original _ (Or.inl ha)]
  · intro a ha
    have hmem : y.mem = v.mem := by simpa only [start, ready, Data.set_mem] using ym
    rw [hmem, vrestore]
    exact empty a ha
  · intro k hk
    have hpresent := vk.present k |>.mpr hk
    rw [vm, Dictionary.filledMemory_present_iff D es r.mem 0 k
      (empty _ (by simp only [Dictionary.slot]; omega))] at hpresent
    obtain ⟨e, he, heq⟩ := hpresent
    have hh := (mem_forwardClass hp as bs s g e).mp he
    rw [← heq, hh.2.2.1]
    exact (eval (((decode as.length e.first).zip as) ++
      ((decode bs.length e.second).zip bs)) s).isLt
  · have ht := (limit.seq hy).regs_eq (by decide :
      (Code.seq (ram[ one ← #1; stop ← one <<< count ]) probeClass).Preserves Dictionary.table)
    simpa +decide [start, ready, Dictionary.table, one, stop] using ht


end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
