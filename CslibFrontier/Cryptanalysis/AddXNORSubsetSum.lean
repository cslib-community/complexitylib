/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORGuardedChain
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Numerical operands for the Add/XNOR subset-sum reduction

[WangLvShenZhang2027], Theorem 1, PDF pp. 9–11. Guard `i` starts at
bit `4i + 2`. The positive-source-number hypothesis is used for the natural
subtraction in the second operand. These are actual full-width words.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

open scoped List

/-- Initial guard word, with control bits `01` and each guard equal to one. -/
@[expose] def guardConstant : ℕ → ℕ
  | 0 => 1
  | r + 1 => guardConstant r + 2 ^ (4 * r + 2)

/-- The guard constant fits below the high resource field. -/
theorem guardConstant_lt (r : ℕ) : guardConstant r < 2 ^ (4 * r + 2) := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [guardConstant]
    have he : 2 ^ (4 * (r + 1) + 2) = 16 * 2 ^ (4 * r + 2) := by
      rw [show 4 * (r + 1) + 2 = (4 * r + 2) + 4 by omega, pow_add]
      ring
    rw [he]
    omega

/-- Future guards do not affect any earlier field, including the control bits. -/
theorem guardConstant_mod {r i : ℕ} (hi : i ≤ r) :
    guardConstant r % 2 ^ (4 * i + 2) = guardConstant i := by
  induction r with
  | zero =>
    have : i = 0 := by omega
    subst i
    decide
  | succ r ih =>
    by_cases hir : i = r + 1
    · subst i
      exact Nat.mod_eq_of_lt (guardConstant_lt _)
    · have hi' : i ≤ r := by omega
      rw [guardConstant, Nat.add_mod,
        Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 4 * i + 2 ≤ 4 * r + 2)),
        Nat.add_zero, Nat.mod_mod, ih hi']

/-- The initial field condition used by the guard-recovery theorem. -/
theorem guardConstant_field {r i m : ℕ} (hi : i < r) (hm : 4 * r + 2 ≤ m) :
    (BitVec.ofNat m (guardConstant r)).setWidth (4 + (4 * i + 2)) =
      1#4 ++ (BitVec.ofNat m (guardConstant r)).setWidth (4 * i + 2) := by
  have hp : 4 + (4 * i + 2) ≤ m := by omega
  rw [BitVec.setWidth_ofNat_of_le hp, BitVec.setWidth_ofNat_of_le (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_append_eq_mul_add]
  rw [show 4 + (4 * i + 2) = 4 * (i + 1) + 2 by omega,
    guardConstant_mod (by omega : i + 1 ≤ r), guardConstant_mod (by omega : i ≤ r),
    guardConstant]
  norm_num
  omega

/-- The `i`th pair of alternating operands in the paper's construction. -/
@[expose] def subsetGuard (m K i s : ℕ) : GuardBlock m :=
  { position := 4 * i + 2
    first := BitVec.ofNat m (3 * 2 ^ (4 * i + 2))
    second := BitVec.ofNat m (s * 2 ^ K - 3 * 2 ^ (4 * i + 2)) }

private theorem scaled_sub (s K p : ℕ) (hs : 0 < s) (hp : p + 4 ≤ K) :
    s * 2 ^ K - 3 * 2 ^ p =
      (16 * (s * 2 ^ (K - (p + 4)) - 1) + 13) * 2 ^ p := by
  have he : 2 ^ K = 16 * 2 ^ (K - (p + 4)) * 2 ^ p := by
    calc
      _ = 2 ^ ((4 + (K - (p + 4))) + p) := by congr 1; omega
      _ = _ := by rw [pow_add, pow_add]; norm_num
  have hz : 0 < s * 2 ^ (K - (p + 4)) := Nat.mul_pos hs (Nat.two_pow_pos _)
  rw [he, show s * (16 * 2 ^ (K - (p + 4)) * 2 ^ p) =
    (16 * (s * 2 ^ (K - (p + 4)))) * 2 ^ p by ring, ← Nat.sub_mul]
  congr 1
  omega

private theorem small_field (m p a : ℕ) (hp : 4 + p ≤ m) (ha : a < 16) :
    (BitVec.ofNat m (a * 2 ^ p)).setWidth (4 + p) =
      BitVec.ofNat 4 a ++ 0#p := by
  rw [BitVec.setWidth_ofNat_of_le hp]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_append_eq_mul_add]
  change (a * 2 ^ p) % 2 ^ (4 + p) = (a % 16) * 2 ^ p + 0
  rw [Nat.mod_eq_of_lt ha, Nat.add_zero]
  apply Nat.mod_eq_of_lt
  rw [pow_add]
  exact Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos _)

/-- The first operand's projected four-bit guard is three. -/
theorem subsetGuard_first_field {m K i s : ℕ} (hm : 4 + (4 * i + 2) ≤ m) :
    (subsetGuard m K i s).first.setWidth (4 + (4 * i + 2)) =
      3#4 ++ 0#(4 * i + 2) := by
  exact small_field m (4 * i + 2) 3 hm (by decide)

/-- The second operand's projected guard is thirteen, derived from the actual
subtraction, for every positive source number. -/
theorem subsetGuard_second_field {m K i s : ℕ} (hs : 0 < s)
    (hK : 4 + (4 * i + 2) ≤ K) (hm : K ≤ m) :
    (subsetGuard m K i s).second.setWidth (4 + (4 * i + 2)) =
      13#4 ++ 0#(4 * i + 2) := by
  rw [subsetGuard, BitVec.setWidth_ofNat_of_le (hK.trans hm)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_append_eq_mul_add]
  change (s * 2 ^ K - 3 * 2 ^ (4 * i + 2)) % 2 ^ (4 + (4 * i + 2)) =
    (13 % 16) * 2 ^ (4 * i + 2) + 0
  rw [scaled_sub s K (4 * i + 2) hs (by omega)]
  rw [show 2 ^ (4 + (4 * i + 2)) = 16 * 2 ^ (4 * i + 2) by rw [pow_add]; rfl,
    Nat.mul_mod_mul_right]
  norm_num [Nat.add_mod]

/-- Adding the two operands gives precisely the high-field source number. -/
theorem subsetGuard_pair {m K i s : ℕ} (hs : 0 < s)
    (hK : 4 + (4 * i + 2) ≤ K) :
    (subsetGuard m K i s).first + (subsetGuard m K i s).second =
      BitVec.ofNat m (s * 2 ^ K) := by
  have he : 3 * 2 ^ (4 * i + 2) ≤ s * 2 ^ K := by
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hK
    rw [pow_add] at hp
    norm_num at hp
    have hm : 2 ^ K ≤ s * 2 ^ K := by
      simpa using Nat.mul_le_mul_right (2 ^ K) hs
    have hz := Nat.two_pow_pos (4 * i + 2)
    omega
  change BitVec.ofNat m _ + BitVec.ofNat m _ = _
  rw [← BitVec.ofNat_add, Nat.add_sub_of_le he]

/-- Four additions encode twice the source number, with no low-field change. -/
theorem subsetGuard_weight {m K i s : ℕ} (hs : 0 < s)
    (hK : 4 + (4 * i + 2) ≤ K) :
    (subsetGuard m K i s).weight = BitVec.ofNat m (s * 2 ^ (K + 1)) := by
  simp only [GuardBlock.weight, subsetGuard_pair hs hK, ← BitVec.ofNat_add]
  congr 1
  rw [pow_succ]
  ring

/-- The two low control bits force the last operation to be addition and the
preceding XNOR parity to be even. This excludes zero-padding false positives. -/
theorem final_control {m : ℕ} (hm : 2 ≤ m) (xs : List (Bool × BitVec m))
    (s target : BitVec m) (hs : s.setWidth 2 = 1#2)
    (htarget : target.setWidth 2 = 1#2)
    (hoperands : ∀ x ∈ xs, x.2.setWidth 2 = 0)
    (b : Bool) (hzero : step b (eval xs s) (-target) = 0) :
    b = false ∧ xnorParity xs = false ∧ eval xs s = target := by
  have hn := normalized_low_invariant hm xs hoperands s false
  simp only [Bool.false_xor] at hn
  rw [normalize_project hm] at hn
  change normalize (xnorParity xs) ((eval xs s).setWidth 2) = s.setWidth 2 at hn
  rw [hs] at hn
  have hraw : (eval xs s).setWidth 2 = normalize (xnorParity xs) 1#2 := by
    cases hp : xnorParity xs
    · simpa [hp, normalize] using hn
    · have h := congrArg (fun w : BitVec 2 => ~~~w) hn
      simpa [hp, normalize] using h
  have hd : (-target).setWidth 2 = 3#2 := by
    have h := congrArg (fun w : BitVec m => w.setWidth 2) (add_neg_cancel target)
    rw [BitVec.setWidth_add _ _ hm, htarget] at h
    have hz : (0 : BitVec m).setWidth 2 = (0 : BitVec 2) := by simp
    rw [hz] at h
    exact eq_neg_of_add_eq_zero_right h
  have hl := congrArg (fun w : BitVec m => w.setWidth 2) hzero
  rw [step_project hm, hraw, hd] at hl
  have hz : (0 : BitVec m).setWidth 2 = (0 : BitVec 2) := by simp
  rw [hz] at hl
  have hb : b = false ∧ xnorParity xs = false := by
    cases b <;> cases hp : xnorParity xs <;> simp_all [normalize, step]
  refine ⟨hb.1, hb.2, ?_⟩
  rw [hb.1] at hzero
  exact eq_of_add_neg_eq_zero (by simpa only [step, Bool.false_eq_true, ↓reduceIte] using hzero)

/-- The actual list of guard blocks, indexed by position rather than source
value, so repeated source numbers retain independent choices. -/
@[expose] def subsetGuards (m : ℕ) (numbers : List ℕ) : List (GuardBlock m) :=
  numbers.zipIdx.map fun (s, i) => subsetGuard m (4 * numbers.length + 2) i s

private theorem ofNat_project_zero {m p : ℕ} (hp : p ≤ m) (x : ℕ)
    (hx : 2 ^ p ∣ x) : (BitVec.ofNat m x).setWidth p = 0 := by
  rw [BitVec.setWidth_ofNat_of_le hp]
  apply BitVec.eq_of_toNat_eq
  simpa using Nat.mod_eq_zero_of_dvd hx

private theorem subsetGuard_zero {m K i s p : ℕ} (hp : p ≤ 4 * i + 2)
    (hK : 4 * i + 2 ≤ K) (hm : p ≤ m) :
    (subsetGuard m K i s).first.setWidth p = 0 ∧
      (subsetGuard m K i s).second.setWidth p = 0 := by
  have hd : 2 ^ p ∣ 3 * 2 ^ (4 * i + 2) :=
    dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hp) _
  have hd' : 2 ^ p ∣ s * 2 ^ K :=
    dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (hp.trans hK)) _
  exact ⟨ofNat_project_zero hm _ hd, ofNat_project_zero hm _ (Nat.dvd_sub hd' hd)⟩

/-- Every numerical block satisfies the local field and weight requirements
of guard recovery. No guard condition is an assumption on the source problem. -/
theorem subsetGuards_fields {m : ℕ} (numbers : List ℕ)
    (hpos : ∀ s ∈ numbers, 0 < s) (hm : 4 * numbers.length + 2 ≤ m) :
    ∀ g ∈ subsetGuards m numbers, 4 + g.position ≤ 4 * numbers.length + 2 ∧
      (BitVec.ofNat m (guardConstant numbers.length)).setWidth (4 + g.position) =
        1#4 ++ (BitVec.ofNat m (guardConstant numbers.length)).setWidth g.position ∧
      g.first.setWidth (4 + g.position) = 3#4 ++ 0#g.position ∧
      g.second.setWidth (4 + g.position) = 13#4 ++ 0#g.position ∧
      g.weight.setWidth (4 * numbers.length + 2) = 0 := by
  intro g hg
  obtain ⟨⟨s, i⟩, hi, rfl⟩ := List.mem_map.1 hg
  have hi' := List.mem_zipIdx hi
  have him : i < numbers.length := by simpa using hi'.2.1
  have hs : s ∈ numbers := by rw [hi'.2.2]; exact List.getElem_mem _
  have hfield : 4 + (4 * i + 2) ≤ 4 * numbers.length + 2 := by omega
  refine ⟨hfield, guardConstant_field him hm,
    subsetGuard_first_field (hfield.trans hm),
    subsetGuard_second_field (hpos s hs) hfield hm, ?_⟩
  rw [subsetGuard_weight (hpos s hs) hfield]
  apply ofNat_project_zero hm
  exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) _

/-- Guard positions strictly increase, and later actual operands are zero in
all earlier guard/control fields. -/
theorem subsetGuards_separated {m : ℕ} (numbers : List ℕ)
    (hm : 4 * numbers.length + 2 ≤ m) :
    (subsetGuards m numbers).Pairwise fun g g' =>
      g'.first.setWidth (4 + g.position) = 0 ∧
      g'.second.setWidth (4 + g.position) = 0 := by
  rw [subsetGuards, List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_zipIdx] at hi hj
  rw [List.getElem_zipIdx, List.getElem_zipIdx]
  apply subsetGuard_zero (by dsimp [subsetGuard]; omega)
    (by omega) (by dsimp [subsetGuard]; omega)


/-- The target state immediately before the final correcting addition. -/
@[expose] def subsetTarget (m : ℕ) (numbers : List ℕ) (target : ℕ) : BitVec m :=
  BitVec.ofNat m (guardConstant numbers.length + target * 2 ^ (4 * numbers.length + 3))

/-- The actual reduction operands, with `q` unrestricted zero operands and a
final correcting operand. The initial guard constant is supplied separately. -/
@[expose] def subsetOperands (m q : ℕ) (numbers : List ℕ) (target : ℕ) : List (BitVec m) :=
  guardedOperands (subsetGuards m numbers) ++ List.replicate q 0 ++ [-subsetTarget m numbers target]

private theorem sum_ofNat {m : ℕ} (xs : List ℕ) :
    (xs.map (BitVec.ofNat m)).sum = BitVec.ofNat m xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, BitVec.ofNat_add]

private theorem sum_weights {m : ℕ} (numbers : List ℕ) (hpos : ∀ s ∈ numbers, 0 < s)
    (xs : List (ℕ × ℕ)) (hxs : xs <+ numbers.zipIdx) :
    ((xs.map fun (s, i) => subsetGuard m (4 * numbers.length + 2) i s).map GuardBlock.weight).sum =
      BitVec.ofNat m ((xs.map Prod.fst).sum * 2 ^ (4 * numbers.length + 3)) := by
  rw [List.map_map]
  have he : xs.map (GuardBlock.weight ∘ fun (s, i) => subsetGuard m (4 * numbers.length + 2) i s) =
      (xs.map fun x => x.1 * 2 ^ (4 * numbers.length + 3)).map (BitVec.ofNat m) := by
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨s, i⟩ hx
    have hi := List.mem_zipIdx (hxs.subset hx)
    have hs : s ∈ numbers := by rw [hi.2.2]; exact List.getElem_mem _
    exact subsetGuard_weight (hpos _ hs) (by omega)
  rw [he, sum_ofNat, List.sum_map_mul_right]

private theorem target_low {m : ℕ} (numbers : List ℕ) (target : ℕ)
    (hm : 4 * numbers.length + 2 ≤ m) :
    (subsetTarget m numbers target).setWidth (4 * numbers.length + 2) =
      (BitVec.ofNat m (guardConstant numbers.length)).setWidth (4 * numbers.length + 2) := by
  unfold subsetTarget
  rw [BitVec.setWidth_ofNat_of_le hm, BitVec.setWidth_ofNat_of_le hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd
    (dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega :
      4 * numbers.length + 2 ≤ 4 * numbers.length + 3)) _), Nat.add_zero, Nat.mod_mod]

private theorem guard_control {m : ℕ} (numbers : List ℕ) (hm : 2 ≤ m) :
    (BitVec.ofNat m (guardConstant numbers.length)).setWidth 2 = 1#2 := by
  rw [BitVec.setWidth_ofNat_of_le hm]
  apply BitVec.eq_of_toNat_eq
  have h := guardConstant_mod (r := numbers.length) (i := 0) (by omega)
  change guardConstant numbers.length % 4 = 1 at h
  simpa only [BitVec.toNat_ofNat] using h


private theorem target_control {m : ℕ} (numbers : List ℕ) (target : ℕ)
    (hm : 4 * numbers.length + 2 ≤ m) :
    (subsetTarget m numbers target).setWidth 2 = 1#2 := by
  have h := project_eq_of_low_eq (show 2 ≤ 4 * numbers.length + 2 by omega)
    (target_low numbers target hm)
  exact h.trans (guard_control numbers (by omega))

private theorem preOps_controls {m q : ℕ} (numbers : List ℕ)
    (hm : 4 * numbers.length + 2 ≤ m) (bs : List Bool) :
    ∀ x ∈ bs.zip (guardedOperands (subsetGuards m numbers) ++ List.replicate q 0),
      x.2.setWidth 2 = 0 := by
  apply operands_zero_of_project
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨g, hg, ha⟩ := List.mem_flatMap.1 ha
    obtain ⟨⟨s, i⟩, hi, rfl⟩ := List.mem_map.1 hg
    have hi' := List.mem_zipIdx hi
    have hz := subsetGuard_zero (s := s) (i := i) (K := 4 * numbers.length + 2)
      (show 2 ≤ 4 * i + 2 by omega) (by omega) (show 2 ≤ m by omega)
    simp only [GuardBlock.operands, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    all_goals first | exact hz.1 | exact hz.2
  · have ha' : a = 0 := List.eq_of_mem_replicate ha
    rw [ha']; simp

/-- Soundness for the actual numerical construction: every unrestricted zero
solution yields a source sublist whose scaled sum agrees with the target. No
NP-hardness or existence of a reduction is assumed. -/
theorem subset_reduction_sound_modular {m q : ℕ} (numbers : List ℕ) (target : ℕ)
    (hpos : ∀ s ∈ numbers, 0 < s) (hm : 4 * numbers.length + 2 ≤ m)
    (hsolve : Solvable (subsetOperands m q numbers target)
      (BitVec.ofNat m (guardConstant numbers.length)) 0) :
    ∃ chosen : List ℕ, chosen <+ numbers ∧
      BitVec.ofNat m (guardConstant numbers.length + chosen.sum * 2 ^ (4 * numbers.length + 3)) =
        subsetTarget m numbers target := by
  obtain ⟨bs, hlen, hzero⟩ := hsolve
  rcases List.eq_nil_or_concat bs with rfl | ⟨preOps, b, rfl⟩
  · simp [subsetOperands] at hlen
  · rw [List.concat_eq_append] at hlen hzero
    have hlen' : preOps.length =
        (guardedOperands (subsetGuards m numbers) ++ List.replicate q 0).length := by
      simp only [List.length_append, List.length_singleton, subsetOperands] at hlen ⊢
      omega
    have hz : eval (preOps.zip (guardedOperands (subsetGuards m numbers) ++
        List.replicate q 0) ++ [(b, -subsetTarget m numbers target)])
        (BitVec.ofNat m (guardConstant numbers.length)) = 0 := by
      simpa only [subsetOperands, ← List.append_assoc, List.zip_append hlen',
        List.zip_cons_cons, List.zip_nil_right] using hzero
    rw [eval_append] at hz
    change step b (eval (preOps.zip (guardedOperands (subsetGuards m numbers) ++
      List.replicate q 0)) (BitVec.ofNat m (guardConstant numbers.length)))
        (-subsetTarget m numbers target) = 0 at hz
    have hc := final_control (show 2 ≤ m by omega) _ _ _
      (guard_control numbers (by omega)) (target_control numbers target hm)
      (preOps_controls numbers hm preOps) b hz
    have hnorm : normalize (xnorParity (preOps.zip
        (guardedOperands (subsetGuards m numbers) ++ List.replicate q 0)))
        (eval (preOps.zip (guardedOperands (subsetGuards m numbers) ++ List.replicate q 0))
          (BitVec.ofNat m (guardConstant numbers.length))) = subsetTarget m numbers target := by
      rw [hc.2.1, hc.2.2]; rfl
    have hl := congrArg (fun w : BitVec m => w.setWidth (4 * numbers.length + 2)) hnorm
    rw [target_low numbers target hm] at hl
    obtain ⟨chosen, hchosen, he⟩ := recover_guarded_chain hm (subsetGuards m numbers)
      (List.replicate q 0) (fun a ha => List.eq_of_mem_replicate ha) _
      (subsetGuards_fields numbers hpos hm) (subsetGuards_separated numbers hm) preOps hlen' hl
    obtain ⟨xs, hxs, rfl⟩ := List.sublist_map_iff.1 hchosen
    refine ⟨xs.map Prod.fst, ?_, ?_⟩
    · simpa only [List.zipIdx_map_fst] using hxs.map Prod.fst
    · rw [sum_weights numbers hpos xs hxs] at he
      rw [BitVec.ofNat_add]
      exact he.symm.trans hnorm


private theorem eval_add_zeros {m : ℕ} (q : ℕ) (s : BitVec m) :
    eval (List.replicate q (false, (0 : BitVec m))) s = s := by
  induction q with
  | zero => rfl
  | succ q ih => simpa [List.replicate_succ, eval, step] using ih

/-- Completeness of the actual numerical construction. Every source sublist
solution supplies all the operators, including zero padding and the final step. -/
theorem subset_reduction_complete {m q : ℕ} (numbers : List ℕ) (target : ℕ)
    (hpos : ∀ s ∈ numbers, 0 < s)
    (chosen : List ℕ) (hchosen : chosen <+ numbers) (hsum : chosen.sum = target) :
    Solvable (subsetOperands m q numbers target)
      (BitVec.ofNat m (guardConstant numbers.length)) 0 := by
  have hmapped : chosen <+ (numbers.zipIdx.map Prod.fst) := by
    simpa only [List.zipIdx_map_fst] using hchosen
  obtain ⟨xs, hxs, rfl⟩ := List.sublist_map_iff.1 hmapped
  have hg := hxs.map (fun (s, i) => subsetGuard m (4 * numbers.length + 2) i s)
  obtain ⟨bs, hlen, he⟩ := realize_guarded_sublist hg
    (BitVec.ofNat m (guardConstant numbers.length))
  change bs.length = (guardedOperands (subsetGuards m numbers)).length at hlen
  rw [sum_weights numbers hpos xs hxs, hsum, ← BitVec.ofNat_add] at he
  change eval (bs.zip (guardedOperands (subsetGuards m numbers)))
    (BitVec.ofNat m (guardConstant numbers.length)) = subsetTarget m numbers target at he
  refine ⟨bs ++ List.replicate q false ++ [false], ?_, ?_⟩
  · simp [subsetOperands, hlen, subsetGuards]
  · have hl : (bs ++ List.replicate q false).length =
        (guardedOperands (subsetGuards m numbers) ++ List.replicate q 0).length := by
      simp [hlen, subsetGuards]
    rw [subsetOperands, List.zip_append hl,
      List.zip_append hlen, eval_append, eval_append, he]
    simp only [List.zip_replicate, List.zip_cons_cons, List.zip_nil_right,
      min_self, eval]
    rw [eval_add_zeros]
    simp [step]

private theorem no_wrap {m r h a S : ℕ} (ha : a ≤ S) (hS : S < 2 ^ h)
    (hm : 4 * r + h + 3 ≤ m) :
    guardConstant r + a * 2 ^ (4 * r + 3) < 2 ^ m := by
  have hc := guardConstant_lt r
  have hp : 2 ^ (4 * r + 3) = 2 * 2 ^ (4 * r + 2) := by
    rw [show 4 * r + 3 = (4 * r + 2) + 1 by omega, pow_succ]; omega
  have he : 2 ^ (4 * r + h + 3) = 2 ^ (4 * r + 3) * 2 ^ h := by
    rw [← pow_add]; congr 1; omega
  have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hm
  rw [he] at hpow
  have hz := Nat.two_pow_pos (4 * r + 2)
  nlinarith

/-- The actual unrestricted reduction is sound and complete when the word
width prevents modular aliasing. This is the many-one mathematical map;
polynomial-time/encoding and complexity-class certificates are not asserted here.
`q` is arbitrary, so the same proof supports balanced and wider padded instances. -/
theorem subset_reduction_iff {m q h : ℕ} (numbers : List ℕ) (target : ℕ)
    (hpos : ∀ s ∈ numbers, 0 < s) (hsource : numbers.sum < 2 ^ h)
    (htarget : target ≤ numbers.sum) (hm : 4 * numbers.length + h + 3 ≤ m) :
    Solvable (subsetOperands m q numbers target)
      (BitVec.ofNat m (guardConstant numbers.length)) 0 ↔
      ∃ chosen : List ℕ, chosen <+ numbers ∧ chosen.sum = target := by
  constructor
  · intro hs
    obtain ⟨chosen, hchosen, he⟩ := subset_reduction_sound_modular numbers target hpos
      (by omega : 4 * numbers.length + 2 ≤ m) hs
    have hsum : chosen.sum ≤ numbers.sum := hchosen.sum_le_sum (fun _ _ => Nat.zero_le _)
    have hleft := no_wrap hsum hsource hm
    have hright := no_wrap htarget hsource hm
    have hn := congrArg BitVec.toNat he
    change (guardConstant numbers.length + chosen.sum * 2 ^ (4 * numbers.length + 3)) % 2 ^ m =
      (guardConstant numbers.length + target * 2 ^ (4 * numbers.length + 3)) % 2 ^ m at hn
    rw [Nat.mod_eq_of_lt hleft, Nat.mod_eq_of_lt hright] at hn
    have hmul : chosen.sum * 2 ^ (4 * numbers.length + 3) =
        target * 2 ^ (4 * numbers.length + 3) := by omega
    exact ⟨chosen, hchosen, (Nat.mul_right_cancel (Nat.two_pow_pos _) hmul)⟩
  · rintro ⟨chosen, hc, ht⟩
    exact subset_reduction_complete numbers target hpos chosen hc ht

/-- Number of operands, counting the initial guard word. -/
theorem subsetOperands_length (m q : ℕ) (numbers : List ℕ) (target : ℕ) :
    (subsetOperands m q numbers target).length + 1 = 4 * numbers.length + q + 2 := by
  have hlen : ∀ gs : List (GuardBlock m), (guardedOperands gs).length = 4 * gs.length := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      change (g.operands ++ guardedOperands gs).length = _
      simp only [List.length_append, GuardBlock.operands, List.length_cons, List.length_nil, ih]
      simp
      omega
  simp [subsetOperands, hlen, subsetGuards]
  omega

/-- The source's balanced parameters, with `h + 1` unrestricted zero operands. -/
theorem balanced_subset_reduction {h : ℕ} (numbers : List ℕ) (target : ℕ)
    (hpos : ∀ s ∈ numbers, 0 < s) (hsource : numbers.sum < 2 ^ h)
    (htarget : target ≤ numbers.sum) :
    let n := 4 * numbers.length + h + 3
    (subsetOperands n (h + 1) numbers target).length + 1 = n ∧
      (Solvable (subsetOperands n (h + 1) numbers target)
        (BitVec.ofNat n (guardConstant numbers.length)) 0 ↔
        ∃ chosen : List ℕ, chosen <+ numbers ∧ chosen.sum = target) := by
  dsimp only
  exact ⟨by rw [subsetOperands_length]; omega,
    subset_reduction_iff numbers target hpos hsource htarget le_rfl⟩


end Cslib.Cryptanalysis.AddXNOR
