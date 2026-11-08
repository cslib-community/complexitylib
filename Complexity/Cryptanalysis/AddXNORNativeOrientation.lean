/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORChainReverse
public import Complexity.Cryptanalysis.AddXNORNativeClassSearch
public import Complexity.Cryptanalysis.AddXNORNativeBalance
import all Complexity.Cryptanalysis.AddXNORNativeClassSemantics

/-!
# Correct inverse orientation of native class search

Complement conjugacy and reversal exchange the two halves without replacing an
inverse continuation by forward evaluation in the original dictionary. The raw
arrays already have the required orders: the original reversed fourth and third
quarters become the forward first and second quarters of the conjugated chain.
This is the orientation correspondence used in [WangLvShenZhang2027],
Lemma 8/Theorem 7, PDF pp. 21–22; native counter selection is separate.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

private theorem reverse_meets {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p)
    (hm : Dissection.Meets as bs cs ds s t g) :
    Dissection.Meets ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~s) (~~~g) := by
  obtain ⟨l, hl, r, hr, he⟩ := hm
  have hf := (ClassEnumeration.mem_classRecords hp as bs s g l).mp hl
  have hb := (ClassEnumeration.mem_backClassRecords hp cs ds t g r).mp hr
  let l' : ClassEnumeration.Record m := ⟨r.second.reverse, r.first.reverse, ~~~r.state⟩
  let r' : ClassEnumeration.Record m := ⟨l.second.reverse, l.first.reverse, ~~~l.state⟩
  refine ⟨l', (ClassEnumeration.mem_classRecords hp _ _ _ _ _).mpr ?_,
    r', (ClassEnumeration.mem_backClassRecords hp _ _ _ _ _).mpr ?_, ?_⟩
  · refine ⟨by simpa [l'] using hb.2.1, by simpa [l'] using hb.1, ?_, ?_⟩
    · change ~~~r.state = _
      rw [hb.2.2.1]
      simp only [backward_eq_not_eval_reverse, BitVec.not_not]
      simp only [List.zip_eq_zipWith]
      rw [List.reverse_zipWith hb.1, List.reverse_zipWith hb.2.1]
    · change (~~~r.state).setWidth p = ~~~g
      rw [BitVec.setWidth_not hp, hb.2.2.2]
  · refine ⟨by simpa [r'] using hf.2.1, by simpa [r'] using hf.1, ?_, ?_⟩
    · change ~~~l.state = _
      rw [hf.2.2.1]
      change _ = backward (l.second.reverse.zip bs.reverse)
        (backward (l.first.reverse.zip as.reverse) (~~~s))
      simp only [List.zip_eq_zipWith]
      rw [← List.reverse_zipWith hf.1, ← List.reverse_zipWith hf.2.1,
        backward_reverse_not, backward_reverse_not]
    · change (~~~l.state).setWidth p = ~~~g
      rw [BitVec.setWidth_not hp, hf.2.2.2]
  · change ~~~r.state = ~~~l.state
    rw [he]

/-- Both native search orientations decide the same original selected class.
The inverse-retained dictionary stores complemented inverse states, with operator
words reversed together with their operands. -/
theorem packedClassSolution_reverse_iff {m p : ℕ} (hp : p ≤ m)
    (as bs cs ds : List (BitVec m)) (s t : BitVec m) (g : BitVec p) :
    PackedClassSolution ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~s) (~~~g) ↔
      PackedClassSolution as bs cs ds s t g := by
  rw [packedClassSolution_iff_meets hp, packedClassSolution_iff_meets hp]
  constructor
  · intro h
    simpa only [List.reverse_reverse, BitVec.not_not] using
      reverse_meets hp ds.reverse cs.reverse bs.reverse as.reverse (~~~t) (~~~s) (~~~g) h
  · exact reverse_meets hp as bs cs ds s t g

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
