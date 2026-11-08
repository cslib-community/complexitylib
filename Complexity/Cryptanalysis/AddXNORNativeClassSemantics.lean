/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORDissection
public import Complexity.Cryptanalysis.AddXNORNativeClassRetain
public import Complexity.Cryptanalysis.AddXNORNativeClassProbe
public import Complexity.Cryptanalysis.AddXNORNativeForwardRetain
public import Complexity.Cryptanalysis.AddXNORNativeBackward
import all Complexity.Cryptanalysis.AddXNORNativeForwardRetain
import all Complexity.Cryptanalysis.AddXNORNativeBackward
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
import all Complexity.Cryptanalysis.AddXNORNativeClassProbe
import all Complexity.Cryptanalysis.AddXNORNativeClassRetain
import all Complexity.Cryptanalysis.AddXNORNativeRetain

/-!
# Indexed completeness semantics of the native class search

The observers below contain all admissible packed quarter indices, preserving
multiplicity and zero indices. They connect native bucket filtering and dictionary
presence to original four-quarter solutions in the selected low-bit class.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

/-- The indexed inverse-quarter bucket actually constructed by native preparation. -/
def inverseRecords {m : ℕ} (as : List (BitVec m)) (t : BitVec m) (p : ℕ)
    (k : BitVec p) : List (ℕ × ℕ) :=
  (Backward.bucketIndices as t (2 ^ p) k.toNat (2 ^ as.length)).map
    fun u => ((Backward.indexedState as t u).toNat, u)

/-- Every indexed forward record in the actual bucket, without deduplication. -/
theorem mem_forwardRecords {m p : ℕ} (as : List (BitVec m)) (s : BitVec m)
    (k : BitVec p) (r : ℕ × ℕ) :
    r ∈ Forward.records as s p k.toNat ↔ r.2 < 2 ^ as.length ∧
      r.1 = (eval ((decode as.length r.2).zip as) s).toNat ∧
      r.1 % 2 ^ p = k.toNat := by
  rcases r with ⟨s₀, u₀⟩
  simp only [Forward.records, bucketIndices_eq, List.mem_map, List.mem_reverse,
    List.mem_filter, List.mem_range, beq_iff_eq, indexedState, Prod.mk.injEq]
  constructor
  · rintro ⟨u, ⟨hu, hk⟩, hs, hidx⟩
    subst u
    exact ⟨hu, hs.symm, hs ▸ hk⟩
  · rintro ⟨hu, hs, hk⟩
    exact ⟨u₀, ⟨hu, hs ▸ hk⟩, hs.symm, rfl⟩

/-- Every indexed inverse record in the actual native bucket. -/
theorem mem_inverseRecords {m p : ℕ} (as : List (BitVec m)) (t : BitVec m)
    (k : BitVec p) (r : ℕ × ℕ) :
    r ∈ inverseRecords as t p k ↔ r.2 < 2 ^ as.length ∧
      r.1 = (backward ((decode as.length r.2).zip as) t).toNat ∧
      r.1 % 2 ^ p = k.toNat := by
  rcases r with ⟨s₀, u₀⟩
  simp only [inverseRecords, Backward.bucketIndices_eq, List.mem_map, List.mem_reverse,
    List.mem_filter, List.mem_range, beq_iff_eq, Backward.indexedState, Prod.mk.injEq]
  constructor
  · rintro ⟨u, ⟨hu, hk⟩, hs, hidx⟩
    subst u
    exact ⟨hu, hs.symm, hs ▸ hk⟩
  · rintro ⟨hu, hs, hk⟩
    exact ⟨u₀, ⟨hu, hs ▸ hk⟩, hs.symm, rfl⟩

/-- The native class loop inserts every selected bucket at every packed index. -/
theorem mem_classEntries {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j n : ℕ) (e : Dictionary.Entry) :
    e ∈ classEntries as g rs j n ↔ ∃ v, j ≤ v ∧ v < j + n ∧
      e ∈ retainedEntries as v (rs (retainQuery as g v)) := by
  induction n generalizing j with
  | zero => simp [classEntries]; omega
  | succ n ih =>
    simp only [classEntries, List.mem_append, ih]
    constructor
    · rintro (h | ⟨v, hv, hv', he⟩)
      · exact ⟨j, le_rfl, by omega, h⟩
      · exact ⟨v, by omega, by omega, he⟩
    · rintro ⟨v, hv, hv', he⟩
      by_cases hj : v = j
      · subst v; exact Or.inl he
      · exact Or.inr ⟨v, by omega, by omega, he⟩

/-- All four packed words satisfy their ordinary finite bounds and solve the
original chain, with its middle state in the selected low-bit class. -/
def PackedClassSolution {m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m)
    (g : BitVec p) : Prop :=
  ∃ u < 2 ^ as.length, ∃ v < 2 ^ bs.length, ∃ w < 2 ^ cs.length, ∃ z < 2 ^ ds.length,
    (eval (((decode as.length u).zip as) ++ ((decode bs.length v).zip bs)) s).setWidth p = g ∧
    eval (((decode as.length u).zip as) ++ ((decode bs.length v).zip bs) ++
      ((decode cs.length w).zip cs) ++ ((decode ds.length z).zip ds)) s = t

/-- Packed indices express exactly the existing functional dissection meeting
predicate. Encoding and decoding preserve every indexed Boolean quarter word. -/
theorem packedClassSolution_iff_meets {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p) :
    PackedClassSolution as bs cs ds s t g ↔ Dissection.Meets as bs cs ds s t g := by
  constructor
  · rintro ⟨u, _, v, _, w, _, z, _, hg, hs⟩
    let l : ClassEnumeration.Record m := ⟨decode as.length u, decode bs.length v,
      eval (((decode as.length u).zip as) ++ ((decode bs.length v).zip bs)) s⟩
    let r : ClassEnumeration.Record m := ⟨decode cs.length w, decode ds.length z,
      backward ((decode cs.length w).zip cs) (backward ((decode ds.length z).zip ds) t)⟩
    have meet : l.state = r.state := by
      apply (eval_bijective ((decode cs.length w).zip cs)).1
      apply (eval_bijective ((decode ds.length z).zip ds)).1
      simp only [l, r, eval_backward]
      simpa only [eval_append] using hs
    refine ⟨l, (ClassEnumeration.mem_classRecords hp as bs s g l).mpr ?_,
      r, (ClassEnumeration.mem_backClassRecords hp cs ds t g r).mpr ?_, meet⟩
    · exact ⟨decode_length _ _, decode_length _ _, by simp [l, eval_append], hg⟩
    · exact ⟨decode_length _ _, decode_length _ _, rfl,
        (congrArg (BitVec.setWidth p) meet.symm).trans hg⟩
  · rintro ⟨l, hl, r, hr, hm⟩
    have hf := (ClassEnumeration.mem_classRecords hp as bs s g l).mp hl
    have hb := (ClassEnumeration.mem_backClassRecords hp cs ds t g r).mp hr
    have d₁ : decode as.length (encode l.first) = l.first := by rw [← hf.1, decode_encode]
    have d₂ : decode bs.length (encode l.second) = l.second := by rw [← hf.2.1, decode_encode]
    have d₃ : decode cs.length (encode r.first) = r.first := by rw [← hb.1, decode_encode]
    have d₄ : decode ds.length (encode r.second) = r.second := by rw [← hb.2.1, decode_encode]
    refine ⟨encode l.first, by simpa only [hf.1] using encode_lt l.first,
      encode l.second, by simpa only [hf.2.1] using encode_lt l.second,
      encode r.first, by simpa only [hb.1] using encode_lt r.first,
      encode r.second, by simpa only [hb.2.1] using encode_lt r.second, ?_, ?_⟩
    · rw [d₁, d₂, eval_append, ← hf.2.2.1]; exact hf.2.2.2
    · rw [d₁, d₂, d₃, d₄]
      simp only [eval_append]
      rw [← hf.2.2.1, hm, hb.2.2.1, eval_backward, eval_backward]

/-- Exact full-state members of the constructed forward-class dictionary. -/
theorem mem_forwardClass {m p : ℕ} (hp : p ≤ m) (as bs : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (e : Dictionary.Entry) :
    e ∈ classEntries bs g (fun k => Forward.records as s p k.toNat) 0 (2 ^ bs.length) ↔
      e.first < 2 ^ as.length ∧ e.second < 2 ^ bs.length ∧
      e.state = (eval (((decode as.length e.first).zip as) ++
        ((decode bs.length e.second).zip bs)) s).toNat ∧
      (eval (((decode as.length e.first).zip as) ++
        ((decode bs.length e.second).zip bs)) s).setWidth p = g := by
  rw [mem_classEntries]
  simp only [Nat.zero_le, Nat.zero_add, true_and, retainedEntries, List.mem_map]
  constructor
  · rintro ⟨v, hv, r, hr, he⟩
    have hf := mem_forwardRecords as s (retainQuery bs g v) r |>.mp hr
    subst e
    simp only [eval_append]
    have hrstate : BitVec.ofNat m r.1 = eval ((decode as.length r.2).zip as) s := by
      rw [hf.2.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine ⟨hf.1, hv, by rw [hrstate], ?_⟩
    have hlow : (eval ((decode as.length r.2).zip as) s).setWidth p = retainQuery bs g v := by
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_setWidth, ← hf.2.1] using hf.2.2
    have heval := eval_project hp ((decode bs.length v).zip bs)
      (eval ((decode as.length r.2).zip as) s)
    simp only [project] at heval
    rw [heval]
    rw [show (List.map (fun x : Bool × BitVec m => (x.1, x.2.setWidth p))
      ((decode bs.length v).zip bs)) =
      (decode bs.length v).zip (bs.map (BitVec.setWidth p)) from List.zip_map_right.symm]
    rw [hlow]
    exact eval_backward _ _
  · rintro ⟨hu, hv, hstate, hclass⟩
    let st := eval ((decode as.length e.first).zip as) s
    have heval := eval_project hp ((decode bs.length e.second).zip bs) st
    simp only [project] at heval
    have hlow : st.setWidth p = retainQuery bs g e.second := by
      apply (eval_bijective ((decode bs.length e.second).zip (bs.map (BitVec.setWidth p)))).1
      rw [retainQuery, eval_backward]
      simpa only [List.zip_map_right, Prod.map_def, id_eq] using
        heval.symm.trans (by simpa only [eval_append] using hclass)
    refine ⟨e.second, hv, (st.toNat, e.first), ?_, ?_⟩
    · rw [mem_forwardRecords]
      exact ⟨hu, rfl, by simpa only [BitVec.toNat_setWidth] using congrArg BitVec.toNat hlow⟩
    · have he : (eval ((decode bs.length e.second).zip bs)
          (BitVec.ofNat m st.toNat)).toNat = e.state := by
        simpa only [st, BitVec.ofNat_toNat, BitVec.setWidth_eq, eval_append] using hstate.symm
      cases e
      simp_all only

/-- The complete native stream against the complete constructed forward class
has a hit exactly when the selected class contains an original indexed solution. -/
theorem nativeClassHit_iff {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) (D : ℕ) (mem : ℕ → ℕ)
    (hz : ∀ q, mem (Dictionary.slot D q) = 0) :
    (∃ w < 2 ^ cs.length, ClassHit cs g (inverseRecords ds t p)
      (Dictionary.filledMemory D
        (classEntries bs g (fun k => Forward.records as s p k.toNat) 0 (2 ^ bs.length)) mem 0)
      D w) ↔ PackedClassSolution as bs cs ds s t g := by
  constructor
  · rintro ⟨w, hw, r, hr, hit⟩
    obtain ⟨e, he, hq⟩ := (Dictionary.filledMemory_present_iff D _ mem 0 _ (hz _)).mp hit
    have hf := (mem_forwardClass hp as bs s g e).mp he
    have hb := (mem_inverseRecords ds t (classQuery cs g w) r).mp hr
    have meet : eval (((decode as.length e.first).zip as) ++
        ((decode bs.length e.second).zip bs)) s =
        backward ((decode cs.length w).zip cs) (backward ((decode ds.length r.2).zip ds) t) := by
      apply BitVec.eq_of_toNat_eq
      rw [← hf.2.2.1, hq, hb.2.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine ⟨e.first, hf.1, e.second, hf.2.1, w, hw, r.2, hb.1, hf.2.2.2, ?_⟩
    simp only [eval_append] at meet ⊢
    rw [meet, eval_backward, eval_backward]
  · rintro ⟨u, hu, v, hv, w, hw, z, hz', hclass, hsol⟩
    let left := eval (((decode as.length u).zip as) ++ ((decode bs.length v).zip bs)) s
    let right := backward ((decode ds.length z).zip ds) t
    have meet : left = backward ((decode cs.length w).zip cs) right := by
      apply (eval_bijective ((decode cs.length w).zip cs)).1
      apply (eval_bijective ((decode ds.length z).zip ds)).1
      rw [eval_backward, eval_backward]
      simpa only [left, eval_append] using hsol
    have hl : left.setWidth p = g := hclass
    have heval := eval_project hp ((decode cs.length w).zip cs) left
    have hmid : eval ((decode cs.length w).zip cs) left = right := by
      rw [meet, eval_backward]
    rw [hmid, hl] at heval
    have hright : right.setWidth p = classQuery cs g w := by
      simpa only [project, List.zip_map_right, Prod.map_def, id_eq, hl, classQuery] using heval
    let r : ℕ × ℕ := (right.toNat, z)
    have hr : r ∈ inverseRecords ds t p (classQuery cs g w) := by
      rw [mem_inverseRecords]
      exact ⟨hz', rfl, by simpa only [r, BitVec.toNat_setWidth] using
        (congrArg BitVec.toNat hright)⟩
    let e : Dictionary.Entry := ⟨left.toNat, u, v⟩
    have he : e ∈ classEntries bs g (fun k => Forward.records as s p k.toNat)
        0 (2 ^ bs.length) := (mem_forwardClass hp as bs s g e).mpr ⟨hu, hv, rfl, hl⟩
    refine ⟨w, hw, r, hr, ?_⟩
    apply (Dictionary.filledMemory_present_iff D _ mem 0 _ (hz _)).mpr
    refine ⟨e, he, ?_⟩
    simpa only [e, r, BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg BitVec.toNat meet

/-- Physical payload provenance in the complete dictionary reconstructs the
original chain. The scan supplies these raw payload equalities as conclusions. -/
theorem nativeClassWitness_sound {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s t : BitVec m) (g : BitVec p) (D : ℕ) (mem : ℕ → ℕ) (x : Cslib.WordRAM.Data 32)
    (hz : ∀ q, mem (Dictionary.slot D q) = 0)
    (hit : x.regs operand ≠ 0)
    (payload : ∃ r ∈ inverseRecords ds t p (classQuery cs g (x.regs operators)),
      x.regs firstOperators = r.2 ∧
      x.regs state = (backward ((decode cs.length (x.regs operators)).zip cs)
        (BitVec.ofNat m r.1)).toNat ∧
      x.regs operand = Dictionary.filledMemory D
        (classEntries bs g (fun k => Forward.records as s p k.toNat) 0 (2 ^ bs.length))
        mem 0 (Dictionary.slot D (x.regs state)) ∧
      x.regs bits = Dictionary.filledMemory D
        (classEntries bs g (fun k => Forward.records as s p k.toNat) 0 (2 ^ bs.length))
        mem 0 (Dictionary.slot D (x.regs state) + 1)) :
    eval (((decode as.length (x.regs operand - 1)).zip as) ++
      ((decode bs.length (x.regs bits)).zip bs) ++
      ((decode cs.length (x.regs operators)).zip cs) ++
      ((decode ds.length (x.regs firstOperators)).zip ds)) s = t := by
  obtain ⟨r, hr, hu, hs, ht, hb⟩ := payload
  obtain ⟨e, he, hq, hf, hv⟩ := Dictionary.filledMemory_provenance D _ mem 0
    (x.regs state) (hz _) (by rwa [← ht])
  have hF := (mem_forwardClass hp as bs s g e).mp he
  have hB := (mem_inverseRecords ds t (classQuery cs g (x.regs operators)) r).mp hr
  have tag : x.regs operand = e.first + 1 := ht.trans hf
  have word : x.regs bits = e.second := hb.trans hv
  have meet : eval (((decode as.length e.first).zip as) ++
      ((decode bs.length e.second).zip bs)) s =
      backward ((decode cs.length (x.regs operators)).zip cs)
        (backward ((decode ds.length r.2).zip ds) t) := by
    apply BitVec.eq_of_toNat_eq
    rw [← hF.2.2.1, hq, hs, hB.2.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [tag, Nat.add_sub_cancel, word, hu]
  simp only [eval_append] at meet ⊢
  rw [meet, eval_backward, eval_backward]

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
