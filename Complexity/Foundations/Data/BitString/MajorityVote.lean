/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Threshold

/-!
# Majority votes with faulty voters

Two facts about the strict majority `BitString.strictMajorityOn s vote` of the votes in a finite
set `s`, used by majority-vote arguments such as Byzantine agreement: it depends only on the votes
in `s` (`BitString.strictMajorityOn_congr`), and it is `v` when every vote outside a set `F` of
faulty voters is `v` and the voters in `s` outside `F` are more than half of `s`
(`BitString.strictMajorityOn_eq_of_forall_notMem`). The faulty set `F` need not lie in `s`.

## Main results

* `Cslib.BitString.strictMajorityOn_congr`: the majority depends only on the votes in `s`.
* `Cslib.BitString.strictMajorityOn_eq_of_forall_notMem`: a strict majority of correct voters
  determines the outcome.
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*}

/-- `strictMajorityOn` depends only on the votes in `s`. -/
theorem strictMajorityOn_congr {s : Finset ι} {f g : ι → Bool} (h : ∀ i ∈ s, f i = g i) :
    strictMajorityOn s f = strictMajorityOn s g := by
  unfold strictMajorityOn
  rw [Finset.filter_congr fun i hi => by rw [h i hi]]

/-- The strict majority of `s` is `v` if every vote in `s` outside `F` is `v` and these votes are
more than half of `s`. -/
theorem strictMajorityOn_eq_of_forall_notMem {s F : Finset ι} {vote : ι → Bool} {v : Bool}
    (hv : ∀ j ∈ s, j ∉ F → vote j = v) (h : s.card / 2 < s.card - F.card) :
    strictMajorityOn s vote = v := by
  classical
  by_contra hne
  have h₁ := card_filter_eq_le_half_of_strictMajorityOn_ne s vote v hne
  have h₂ : s \ F ⊆ s.filter fun j => vote j = v := fun j hj =>
    Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hj).1, hv j (Finset.mem_sdiff.1 hj).1
      (Finset.mem_sdiff.1 hj).2⟩
  have h₃ := Finset.card_le_card h₂
  have h₄ := Finset.le_card_sdiff F s
  omega

end Cslib.BitString
