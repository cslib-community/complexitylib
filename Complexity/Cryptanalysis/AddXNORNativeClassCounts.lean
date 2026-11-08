/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNativeCounterPair
public import Complexity.Cryptanalysis.AddXNORNativeOrientedSearch
import all Complexity.Cryptanalysis.AddXNORNativeClassSearch
import all Complexity.Cryptanalysis.AddXNORNativeOrientedSearch
import all Complexity.Cryptanalysis.AddXNORClassEnumeration
import all Complexity.Cryptanalysis.AddXNORNativeClassSemantics
import all Complexity.Cryptanalysis.AddXNORNativeClassRetain
import all Complexity.Cryptanalysis.AddXNORNativeClassProbe
import all Complexity.Cryptanalysis.AddXNORNativeForwardRetain
import all Complexity.Cryptanalysis.AddXNORNativeBuckets
import all Complexity.Cryptanalysis.AddXNORNativeBackward
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration

/-!
# Indexed work counts of the actual native class streams

Packed numeric iteration visits every operator word once, including coincident
states. The native filtered bucket lengths therefore agree with the computed
multiplicity counters, not with a Boolean support count or a class mean.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

/-- Forward multiplicity observer of the actual native counter table. -/
def forwardCount {m p : ℕ} (as bs : List (BitVec m)) (s : BitVec m) (g : BitVec p) : ℕ :=
  (WordTable.classCounters ((as ++ bs).map (BitVec.setWidth p)) (s.setWidth p)).read g

/-- Backward multiplicity observer in its physical complemented coordinates. -/
def backwardCount {m p : ℕ} (cs ds : List (BitVec m)) (t : BitVec m) (g : BitVec p) : ℕ :=
  (WordTable.backwardCounters ((cs ++ ds).map (BitVec.setWidth p)) (t.setWidth p)).read g

/-- Total original operand count. -/
def totalLength {m : ℕ} (as bs cs ds : List (BitVec m)) : ℕ :=
  as.length + bs.length + cs.length + ds.length

/-- A polynomial coefficient common to both native directions. -/
def workFactor (q : ℕ) : ℕ := 100 * (q + 1)

/-- Layout-independent quarter enumeration work per class. -/
def quarterWork (p a b c d : ℕ) : ℕ := 2 ^ p + 2 ^ a + 2 ^ b + 2 ^ c + 2 ^ d

/-- Exact maximum of the two constructed multiplicity counters' minima. -/
def computedBalance {m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m) : ℕ :=
  Finset.univ.sup fun g : BitVec p => min (forwardCount as bs s g) (backwardCount cs ds t g)

end Cslib.Cryptanalysis.AddXNOR.Native.Driver

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open scoped BigOperators

/-- Numeric packed enumeration is a permutation of the existing operator words. -/
theorem packedWords_perm (n : ℕ) :
    (List.ofFn fun v : Fin (2 ^ n) => decode n v.val).Perm (operatorWords n) := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr (decode_injective n))
    (ClassEnumeration.operatorWords_nodup n)).mpr
  intro bs
  simp only [List.mem_ofFn, mem_operatorWords]
  constructor
  · rintro ⟨v, rfl⟩; exact decode_length _ _
  · intro hl
    refine ⟨⟨encode bs, by simpa only [hl] using encode_lt bs⟩, ?_⟩
    simpa only [← hl] using decode_encode bs

/-- Sum every packed word exactly once using the semantic word enumeration. -/
theorem sum_packedWords (n : ℕ) (f : List Bool → ℕ) :
    (∑ v : Fin (2 ^ n), f (decode n v.val)) = ((operatorWords n).map f).sum := by
  rw [← List.sum_ofFn]
  simpa only [List.map_ofFn, Function.comp_def] using ((packedWords_perm n).map f).sum_eq

/-- Numeric iteration of both quarter words preserves every indexed pair. -/
theorem sum_packedPairs (a b : ℕ) (f : List Bool → List Bool → ℕ) :
    (∑ v : Fin (2 ^ b), ∑ u : Fin (2 ^ a), f (decode a u.val) (decode b v.val)) =
      ((operatorWords b).map fun ys => ((operatorWords a).map fun xs => f xs ys).sum).sum := by
  calc
    _ = ∑ v : Fin (2 ^ b), ((operatorWords a).map fun xs => f xs (decode b v.val)).sum := by
      apply Finset.sum_congr rfl
      intro v _
      exact sum_packedWords a (fun xs => f xs (decode b v.val))
    _ = _ := sum_packedWords b (fun ys => ((operatorWords a).map fun xs => f xs ys).sum)

/-- The exact retained insertion count is a sum of actual bucket lengths. -/
theorem classEntries_length_sum {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j n : ℕ) :
    (classEntries as g rs j n).length =
      ∑ v ∈ Finset.range n, (rs (retainQuery as g (j + v))).length := by
  induction n generalizing j with
  | zero => simp [classEntries]
  | succ n ih =>
    rw [classEntries, List.length_append, ih, Finset.sum_range_succ']
    simp only [retainedEntries, List.length_map, Nat.add_zero]
    simp only [Nat.add_comm, Nat.add_left_comm]

/-- The full opposite stream's record count is the corresponding bucket sum. -/
theorem classProbeHits_sum {m p : ℕ} (as : List (BitVec m)) (g : BitVec p)
    (rs : BitVec p → List (ℕ × ℕ)) (j n : ℕ) :
    classProbeHits as g rs j n =
      ∑ v ∈ Finset.range n, (rs (classQuery as g (j + v))).length := by
  induction n generalizing j with
  | zero => simp [classProbeHits]
  | succ n ih =>
    rw [classProbeHits, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    simp only [Nat.add_comm, Nat.add_left_comm]

private theorem retain_test {m p : ℕ} (hp : p ≤ m) (bs : List (BitVec m))
    (g : BitVec p) (v : ℕ) (st : BitVec m) :
    st.toNat % 2 ^ p = (retainQuery bs g v).toNat ↔
      (eval ((decode bs.length v).zip bs) st).setWidth p = g := by
  have hlow : st.toNat % 2 ^ p = (retainQuery bs g v).toNat ↔
      st.setWidth p = retainQuery bs g v := by
    constructor
    · intro h; apply BitVec.eq_of_toNat_eq; simpa only [BitVec.toNat_setWidth] using h
    · intro h; simpa only [BitVec.toNat_setWidth] using congrArg BitVec.toNat h
  rw [hlow, eval_project hp]
  have he := eval_append_eq_iff ([] : List (Bool × BitVec p))
    ((decode bs.length v).zip (bs.map (BitVec.setWidth p))) (st.setWidth p) g
  simpa only [List.nil_append, eval, project, List.zip_map_right, Prod.map_def,
    id_eq, retainQuery] using he.symm

private theorem forwardBucket_length {m p : ℕ} (hp : p ≤ m)
  (as bs : List (BitVec m)) (s : BitVec m) (g : BitVec p) (v : ℕ) :
    (Forward.records as s p (retainQuery bs g v).toNat).length =
      ∑ u : Fin (2 ^ as.length), if
        (eval ((decode bs.length v).zip bs)
          (eval ((decode as.length u.val).zip as) s)).setWidth p = g
          then 1 else 0 := by
  rw [Forward.records, List.length_map, bucketIndices_eq, List.length_reverse,
    ClassEnumeration.filter_length_eq_sum, ← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro u _
  simp only [beq_iff_eq, indexedState, retain_test hp]

/-- Every emitted forward record is counted once, including repeated full states. -/
theorem insertionCount_eq_classRecords {m p : ℕ} (hp : p ≤ m)
    (as bs : List (BitVec m)) (s : BitVec m) (g : BitVec p) :
    insertionCount as bs s g = (ClassEnumeration.classRecords as bs s g).length := by
  rw [insertionCount, classEntries_length_sum, ClassEnumeration.classRecords_length hp]
  simp only [Nat.zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [forwardBucket_length hp]
  exact sum_packedPairs as.length bs.length (fun xs ys =>
    if (eval (ys.zip bs) (eval (xs.zip as) s)).setWidth p = g then 1 else 0)

/-- The native insertion stream has exactly the multiplicity in its computed counter. -/
theorem insertionCount_eq_forwardCount {m p : ℕ} (hp : p ≤ m)
    (as bs : List (BitVec m)) (s : BitVec m) (g : BitVec p) :
    insertionCount as bs s g = Driver.forwardCount as bs s g := by
  rw [insertionCount_eq_classRecords hp]
  have h := ClassEnumeration.classRecords_length_eq_count hp as.get bs.get s g
  simp only [List.ofFn_get] at h
  rw [h]
  have hh := WordTable.projected_classCounters hp (Fin.append as.get bs.get) s g
  change (WordTable.classCounters (List.ofFn ((BitVec.setWidth p) ∘ Fin.append as.get bs.get))
    (s.setWidth p)).read g = _ at hh
  simpa only [Driver.forwardCount, ← List.map_ofFn, List.ofFn_fin_append, List.ofFn_get]
    using hh.symm

private theorem probe_test {m p : ℕ} (hp : p ≤ m) (cs : List (BitVec m))
    (g : BitVec p) (v : ℕ) (st : BitVec m) :
    st.toNat % 2 ^ p = (classQuery cs g v).toNat ↔
      (backward ((decode cs.length v).zip cs) st).setWidth p = g := by
  have hlow : st.toNat % 2 ^ p = (classQuery cs g v).toNat ↔
      st.setWidth p = classQuery cs g v := by
    constructor
    · intro h; apply BitVec.eq_of_toNat_eq; simpa only [BitVec.toNat_setWidth] using h
    · intro h; simpa only [BitVec.toNat_setWidth] using congrArg BitVec.toNat h
  rw [hlow, backward_project hp]
  have he := eval_append_eq_iff ([] : List (Bool × BitVec p))
    ((decode cs.length v).zip (cs.map (BitVec.setWidth p))) g (st.setWidth p)
  simp only [List.nil_append, eval] at he
  simpa only [classQuery, project, List.zip_map_right, Prod.map_def, id_eq, eq_comm] using he

private theorem inverseBucket_length {m p : ℕ} (hp : p ≤ m)
    (cs ds : List (BitVec m)) (t : BitVec m) (g : BitVec p) (v : ℕ) :
    (inverseRecords ds t p (classQuery cs g v)).length =
      ∑ z : Fin (2 ^ ds.length), if (backward ((decode cs.length v).zip cs)
        (backward ((decode ds.length z.val).zip ds) t)).setWidth p = g then 1 else 0 := by
  rw [inverseRecords, List.length_map, Backward.bucketIndices_eq, List.length_reverse,
    ClassEnumeration.filter_length_eq_sum, ← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro z _
  simp only [beq_iff_eq, Backward.indexedState, probe_test hp]

/-- Native streaming visits exactly the computed backward class multiplicity. -/
theorem classProbeHits_eq_backwardCount {m p : ℕ} (hp : p ≤ m)
    (cs ds : List (BitVec m)) (t : BitVec m) (g : BitVec p) :
    classProbeHits cs g (inverseRecords ds t p) 0 (2 ^ cs.length) =
      Driver.backwardCount cs ds t g := by
  rw [classProbeHits_sum]
  simp only [Nat.zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [inverseBucket_length hp]
  have hs := sum_packedPairs ds.length cs.length (fun zs ws =>
    if (backward (ws.zip cs) (backward (zs.zip ds) t)).setWidth p = g then 1 else 0)
  rw [hs, ← ClassEnumeration.backClassRecords_length hp]
  have h := ClassEnumeration.backClassRecords_length_eq_count hp cs.get ds.get t g
  simp only [List.ofFn_get] at h
  rw [h]
  have hh := WordTable.projected_backwardCounters hp (Fin.append cs.get ds.get) t g
  change (WordTable.backwardCounters (List.ofFn ((BitVec.setWidth p) ∘ Fin.append cs.get ds.get))
    (t.setWidth p)).read g = _ at hh
  simpa only [Driver.backwardCount, ← List.map_ofFn, List.ofFn_fin_append, List.ofFn_get]
    using hh.symm

/-- The conjugated inverse-retention stream has the original backward count. -/
theorem reverse_forwardCount {m p : ℕ} (hp : p ≤ m) (cs ds : List (BitVec m))
    (t : BitVec m) (g : BitVec p) :
    Driver.forwardCount ds.reverse cs.reverse (~~~t) (~~~g) = Driver.backwardCount cs ds t g := by
  simp only [Driver.forwardCount, Driver.backwardCount, ← List.reverse_append,
    List.map_reverse, BitVec.setWidth_not hp, WordTable.backwardCounters_conjugate]

/-- The conjugated opposite stream has the original forward count. -/
theorem reverse_backwardCount {m p : ℕ} (hp : p ≤ m) (as bs : List (BitVec m))
    (s : BitVec m) (g : BitVec p) :
    Driver.backwardCount bs.reverse as.reverse (~~~s) (~~~g) = Driver.forwardCount as bs s g := by
  have hh := WordTable.backwardCounters_conjugate
    ((bs.reverse ++ as.reverse).map (BitVec.setWidth p)) ((~~~s).setWidth p) (~~~g)
  simpa only [Driver.forwardCount, Driver.backwardCount, List.reverse_append, List.map_append,
    List.map_reverse, List.reverse_reverse, BitVec.setWidth_not hp, BitVec.not_not] using hh.symm

/-- All forward indexed words are partitioned by the actual computed class counters. -/
theorem sum_forwardCount {m p : ℕ} (hp : p ≤ m) (as bs : List (BitVec m)) (s : BitVec m) :
    (∑ g : BitVec p, Driver.forwardCount as bs s g) = 2 ^ (as.length + bs.length) := by
  have hf (g : BitVec p) := WordTable.projected_classCounters hp (Fin.append as.get bs.get) s g
  change ∀ g, (WordTable.classCounters (List.ofFn ((BitVec.setWidth p) ∘ Fin.append as.get bs.get))
    (s.setWidth p)).read g = _ at hf
  simpa only [Driver.forwardCount, ← hf, ← List.map_ofFn, List.ofFn_fin_append, List.ofFn_get]
    using sum_forwardClassCount p (Fin.append as.get bs.get) s

/-- All inverse indexed words are partitioned by the actual backward counters. -/
theorem sum_backwardCount {m p : ℕ} (hp : p ≤ m) (cs ds : List (BitVec m)) (t : BitVec m) :
    (∑ g : BitVec p, Driver.backwardCount cs ds t g) = 2 ^ (cs.length + ds.length) := by
  have hf (g : BitVec p) := WordTable.projected_backwardCounters hp (Fin.append cs.get ds.get) t g
  change ∀ g, (WordTable.backwardCounters
    (List.ofFn ((BitVec.setWidth p) ∘ Fin.append cs.get ds.get))
    (t.setWidth p)).read g = _ at hf
  simpa only [Driver.backwardCount, ← hf, ← List.map_ofFn, List.ofFn_fin_append, List.ofFn_get]
    using sum_backwardClassCount p (Fin.append cs.get ds.get) t

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter

namespace Cslib.Cryptanalysis.AddXNOR.Native.Driver

open Quarter

/-- Store bound for a forward-retained lifetime, including physical release. -/
theorem orientedStores_forward_le {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p) :
    orientedStores false as bs cs ds s t g ≤ workFactor (totalLength as bs cs ds) *
      (quarterWork p as.length bs.length cs.length ds.length + forwardCount as bs s g) := by
  have exactCount : orientedStores false as bs cs ds s t g =
      8 * 2 ^ p + 2 ^ as.length * (11 * as.length + 22) +
      2 ^ ds.length * (18 * ds.length + 37) + 2 ^ bs.length * (18 * bs.length + 35) +
      forwardCount as bs s g * (11 * bs.length + 42) + 10 * (bs.length + cs.length) + 82 := by
    simp only [orientedStores, searchStores, Bool.false_eq_true, ↓reduceIte,
      classRetainTime_eq]
    rw [insertionCount_eq_forwardCount hp]
    rw [show (classEntries bs g (fun k => Forward.records as s p k.toNat) 0
        (2 ^ bs.length)).length = forwardCount as bs s g from
          insertionCount_eq_forwardCount hp _ _ _ _]
    ring
  rw [exactCount]
  let q := totalLength as bs cs ds
  let C := workFactor q
  have ha : as.length ≤ q := by dsimp [q, totalLength]; omega
  have hb : bs.length ≤ q := by dsimp [q, totalLength]; omega
  have hc : cs.length ≤ q := by dsimp [q, totalLength]; omega
  have hd : ds.length ≤ q := by dsimp [q, totalLength]; omega
  have hA := Nat.mul_le_mul_left (2 ^ as.length)
    (show 11 * as.length + 22 ≤ C by dsimp [C, workFactor]; omega)
  have hB := Nat.mul_le_mul_left (2 ^ bs.length)
    (show 18 * bs.length + 35 ≤ C by dsimp [C, workFactor]; omega)
  have hD := Nat.mul_le_mul_left (2 ^ ds.length)
    (show 18 * ds.length + 37 ≤ C by dsimp [C, workFactor]; omega)
  have hF := Nat.mul_le_mul_left (forwardCount as bs s g)
    (show 11 * bs.length + 42 ≤ C by dsimp [C, workFactor]; omega)
  have hN : 8 * 2 ^ p + 10 * (bs.length + cs.length) + 82 ≤ C * 2 ^ p := by
    have hpos := Nat.two_pow_pos p
    have hq : bs.length + cs.length ≤ q := by dsimp [q, totalLength]; omega
    have hmul := Nat.mul_le_mul_left (2 ^ p)
      (show 10 * q + 90 ≤ C by dsimp [C, workFactor]; omega)
    nlinarith
  change _ ≤ C * _
  dsimp only [quarterWork]
  have hC := Nat.zero_le (C * 2 ^ cs.length)
  nlinarith

/-- The inverse physical construction has the analogous bound in the original
backward counter, proved by complement conjugacy rather than reinterpretation. -/
theorem orientedStores_backward_le {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p) :
    orientedStores true as bs cs ds s t g ≤ workFactor (totalLength as bs cs ds) *
      (quarterWork p as.length bs.length cs.length ds.length + backwardCount cs ds t g) := by
  have hr := orientedStores_forward_le hp ds.reverse cs.reverse bs.reverse as.reverse
    (~~~t) (~~~s) (~~~g)
  have hi : orientedStores true as bs cs ds s t g =
      orientedStores false ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~s) (~~~g) := by
    simp only [orientedStores, Bool.false_eq_true, ↓reduceIte]
  rw [← hi, reverse_forwardCount hp] at hr
  have len : totalLength ds.reverse cs.reverse bs.reverse as.reverse =
      totalLength as bs cs ds := by simp only [totalLength, List.length_reverse]; omega
  have qw : quarterWork p ds.reverse.length cs.reverse.length bs.reverse.length as.reverse.length =
      quarterWork p as.length bs.length cs.length ds.length := by
    simp only [quarterWork, List.length_reverse]; omega
  rwa [len, qw] at hr

/-- The selected retained class is bounded by the maximum of the actual minima. -/
theorem min_count_le_computedBalance {m p : ℕ}
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p) :
    min (forwardCount as bs s g) (backwardCount cs ds t g) ≤
      computedBalance (p := p) as bs cs ds s t :=
  Finset.le_sup (f := fun k : BitVec p =>
    min (forwardCount as bs s k) (backwardCount cs ds t k)) (Finset.mem_univ g)

/-- A uniform per-lifetime store allowance. This is reused, not summed across classes. -/
def lifetimeStores {m p : ℕ} (as bs cs ds : List (BitVec m)) (s t : BitVec m) : ℕ :=
  workFactor (totalLength as bs cs ds) *
    (quarterWork p as.length bs.length cs.length ds.length +
      computedBalance (p := p) as bs cs ds s t)

end Cslib.Cryptanalysis.AddXNOR.Native.Driver
