/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORCounting
public import Complexity.Cryptanalysis.AddXNORTransfer
public import Complexity.Cryptanalysis.AddXNORReachability
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Size
import all Complexity.Cryptanalysis.AddXNORSwap
import Mathlib.Tactic.Linarith

/-!
# Low-bit classes of actual Add/XNOR chains

[WangLvShenZhang2027], Lemma 8 and Theorem 7 (PDF pp. 21–22).
Classes retain distinct indexed operator strings, including repeated full states.
`WordTable.classCounters`, `WordTable.backwardCounters` and
`WordTable.maxMin` compute the counters and balance, with correctness proofs and
recursive arithmetic-operation bounds. These bounds charge natural additions and
comparisons separately from Boolean/pointer operations; they are not native
bit-runtime bounds. Counter bit lengths are proved, rather than assumed.

Their partition identities and uniform per-class expectations do not assert
independence or control the expectation of the maximum balance parameter.
The backward expectation requires a nonempty suffix: its first operand supplies
the independent uniform word, while the target remains fixed.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

/-- Size of the forward low-bit class, counting operator strings with multiplicity. -/
@[expose] def forwardClassCount {m q : ℕ} (p : ℕ) (as : Fin q → BitVec m)
    (s : BitVec m) (g : BitVec p) : ℕ :=
  ∑ bs : Fin q → Bool, if (eval (steps bs as) s).setWidth p = g then 1 else 0

/-- Size of the backward low-bit class, retaining every indexed suffix. -/
@[expose] def backwardClassCount {m q : ℕ} (p : ℕ) (as : Fin q → BitVec m)
    (t : BitVec m) (g : BitVec p) : ℕ :=
  ∑ bs : Fin q → Bool, if (backward (steps bs as) t).setWidth p = g then 1 else 0

/-- Every prefix belongs to exactly one class, for all widths and lengths. -/
theorem sum_forwardClassCount {m q : ℕ} (p : ℕ) (as : Fin q → BitVec m) (s : BitVec m) :
    ∑ g : BitVec p, forwardClassCount p as s g = 2 ^ q := by
  unfold forwardClassCount
  rw [Finset.sum_comm]
  simp

/-- Every suffix belongs to exactly one class, also when the suffix is empty. -/
theorem sum_backwardClassCount {m q : ℕ} (p : ℕ) (as : Fin q → BitVec m) (t : BitVec m) :
    ∑ g : BitVec p, backwardClassCount p as t g = 2 ^ q := by
  unfold backwardClassCount
  rw [Finset.sum_comm]
  simp

/-- The explicit balance parameter of Theorem 7. The two cuts need not have
identical length. This finite maximum is computable and never assumes balance. -/
@[expose] def classBalance {m l r : ℕ} (p : ℕ) (left : Fin l → BitVec m)
    (right : Fin r → BitVec m) (s t : BitVec m) : ℕ :=
  Finset.univ.sup fun g : BitVec p =>
    min (forwardClassCount p left s g) (backwardClassCount p right t g)

/-- Each stored smaller class has size at most the actual computed balance. -/
theorem min_classCount_le_balance {m l r : ℕ} (p : ℕ) (left : Fin l → BitVec m)
    (right : Fin r → BitVec m) (s t : BitVec m) (g : BitVec p) :
    min (forwardClassCount p left s g) (backwardClassCount p right t g) ≤
      classBalance p left right s t :=
  Finset.le_sup (f := fun g =>
    min (forwardClassCount p left s g) (backwardClassCount p right t g)) (Finset.mem_univ g)

private theorem low_uniform_mass (h p : ℕ) (g : BitVec p) :
    (𝔼 s : BitVec (h + p), if s.setWidth p = g then (1 : ℚ) else 0) = 1 / 2 ^ p := by
  rw [show (𝔼 s : BitVec (h + p), if s.setWidth p = g then (1 : ℚ) else 0) =
    (𝔼 s : BitVec p, if s = g then (1 : ℚ) else 0) from
      expect_low h p (fun s => if s = g then (1 : ℚ) else 0)]
  simp [Finset.expect_eq_sum_div_card, Fintype.card_congr BitVec.equivFin.toEquiv]

/-- A fixed prefix has a uniform projected state when its initial word is uniform. -/
theorem forward_low_mass (h p : ℕ) (xs : List (Bool × BitVec (h + p))) (g : BitVec p) :
    (𝔼 s : BitVec (h + p), if (eval xs s).setWidth p = g then (1 : ℚ) else 0) =
      1 / 2 ^ p := by
  calc
    _ = 𝔼 s : BitVec (h + p), if s.setWidth p = g then (1 : ℚ) else 0 :=
      Fintype.expect_bijective (eval xs) (eval_bijective xs) _ _ (fun _ => rfl)
    _ = _ := low_uniform_mass h p g

/-- Theorem 7's exact per-prefix-class expectation, conditional on all later
operands. Full independence of the operands therefore gives the same mean. -/
theorem mean_forwardClassCount (h p q : ℕ) (as : Fin q → BitVec (h + p)) (g : BitVec p) :
    (𝔼 s : BitVec (h + p), (forwardClassCount p as s g : ℚ)) = 2 ^ q / 2 ^ p := by
  simp only [forwardClassCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.expect_sum_comm]
  simp [forward_low_mass, nsmul_eq_mul, div_eq_mul_inv]

/-- Forward class means in the literal independent uniform-operand experiment. -/
theorem uniform_mean_forwardClassCount (h p q : ℕ) (g : BitVec p) :
    (𝔼 as : Fin q → BitVec (h + p), 𝔼 s : BitVec (h + p),
      (forwardClassCount p as s g : ℚ)) = 2 ^ q / 2 ^ p := by
  simp [mean_forwardClassCount]

private theorem unstep_operand_bijective {m : ℕ} (b : Bool) (t : BitVec m) :
    Function.Bijective (unstep b t) := by
  have hinv : Function.Involutive (unstep b t) := by
    intro a
    cases b <;> simp [unstep, BitVec.not_xor_right, ← BitVec.xor_assoc]
  exact hinv.bijective

/-- A fixed nonempty backward operator string has uniform low state over its
first operand. This does not require a random target or initial word. -/
theorem backward_low_mass (h p : ℕ) (b : Bool)
    (post : List (Bool × BitVec (h + p))) (t : BitVec (h + p)) (g : BitVec p) :
    (𝔼 a : BitVec (h + p),
      if (backward ((b, a) :: post) t).setWidth p = g then (1 : ℚ) else 0) =
      1 / 2 ^ p := by
  calc
    _ = 𝔼 s : BitVec (h + p), if s.setWidth p = g then (1 : ℚ) else 0 :=
      Fintype.expect_bijective (unstep b (backward post t))
        (unstep_operand_bijective b (backward post t)) _ _ (fun _ => rfl)
    _ = _ := low_uniform_mass h p g

/-- Theorem 7's backward per-class mean, conditional on every operand except
the first one of the nonempty suffix. -/
theorem mean_backwardClassCount (h p q : ℕ) (post : Fin q → BitVec (h + p))
    (t : BitVec (h + p)) (g : BitVec p) :
    (𝔼 a : BitVec (h + p),
      (backwardClassCount p (Fin.cons a post) t g : ℚ)) = 2 ^ (q + 1) / 2 ^ p := by
  simp only [backwardClassCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.expect_sum_comm]
  have hs (bs : Fin (q + 1) → Bool) (a : BitVec (h + p)) :
      steps bs (Fin.cons a post) =
        (bs 0, a) :: steps (fun i => bs i.succ) post := by
    simp [steps, List.ofFn_succ]
  simp only [hs, backward_low_mass]
  simp [nsmul_eq_mul, div_eq_mul_inv]

/-- Literal independent uniform sampling of every operand in a nonempty suffix. -/
theorem uniform_mean_backwardClassCount (h p q : ℕ) (t : BitVec (h + p)) (g : BitVec p) :
    (𝔼 post : Fin q → BitVec (h + p), 𝔼 a : BitVec (h + p),
      (backwardClassCount p (Fin.cons a post) t g : ℚ)) = 2 ^ (q + 1) / 2 ^ p := by
  simp [mean_backwardClassCount]

namespace WordTable

/-- Convert a Boolean table to zero/one integer counters. -/
@[expose] def indicators : {m : ℕ} → WordTable Bool m → WordTable ℕ m
  | 0, .leaf b => .leaf (if b then 1 else 0)
  | _ + 1, .node l r => .node (indicators l) (indicators r)

/-- Add the counters at corresponding leaves. A tick at a leaf counts one
natural-number addition, not one bit operation; counters are not unit-cost bits. -/
@[expose] def sumCounters : {m : ℕ} → WordTable ℕ m → WordTable ℕ m →
    Cslib.Algorithms.Lean.TimeM ℕ (WordTable ℕ m)
  | 0, .leaf a, .leaf b => ⟨.leaf (a + b), 1⟩
  | _ + 1, .node a b, .node c d => do
    let z ← sumCounters a c
    let o ← sumCounters b d
    Cslib.Algorithms.Lean.TimeM.tick 1
    return .node z o

/-- The counting version of the reachable-state update retains both choices,
even if they have identical states. -/
@[expose] def countAdvance {m : ℕ} (bits : List Bool) (table : WordTable ℕ m) :
    Cslib.Algorithms.Lean.TimeM ℕ (WordTable ℕ m) := do
  let neg ← complement bits
  let a ← addPull neg true table
  let x ← xorPull neg table
  sumCounters a x

/-- Compute all class counters in one dynamic program. -/
@[expose] def countRun {m : ℕ} : List (List Bool) → WordTable ℕ m →
    Cslib.Algorithms.Lean.TimeM ℕ (WordTable ℕ m)
  | [], table => ⟨table, 1⟩
  | a :: as, table => do
    let next ← countAdvance a table
    let result ← countRun as next
    Cslib.Algorithms.Lean.TimeM.tick 2
    return result

/-- All low-bit forward class counts, computed without enumerating operator words. -/
@[expose] def classCounters {m : ℕ} (as : List (BitVec m)) (s : BitVec m) : WordTable ℕ m :=
  (countRun (as.map stateKey) (indicators (point m (stateKey s)).ret)).ret

open Cslib.Algorithms.Lean

private theorem indicators_read {m : ℕ} (table : WordTable Bool m) (s : BitVec m) :
    (indicators table).read s = if table.read s then 1 else 0 := by
  induction table with
  | leaf b => rfl
  | @node n l r ihl ihr =>
    obtain ⟨⟨s, b⟩, rfl⟩ := (concat_bijective n).2 s
    cases b <;> simp [indicators, read_node, ihl, ihr]

private theorem sumCounters_read {m : ℕ} (a b : WordTable ℕ m) (s : BitVec m) :
    (sumCounters a b).ret.read s = a.read s + b.read s := by
  induction a with
  | leaf a => cases b; rfl
  | @node n l r ihl ihr =>
    cases b with
    | node c d =>
      obtain ⟨⟨s, b⟩, rfl⟩ := (concat_bijective n).2 s
      cases b <;> simp [sumCounters, read_node, ihl, ihr]

private theorem countAdvance_read {m : ℕ} (table : WordTable ℕ m) (a t : BitVec m) :
    (countAdvance (stateKey a) table).ret.read t =
      table.read (unstep false t a) + table.read (unstep true t a) := by
  simp only [countAdvance, TimeM.ret_bind, complement_ret, complement_key, sumCounters_read,
    addPull_read, xorPull_read, unstep, Bool.false_eq_true, ↓reduceIte, Bool.toNat_true]
  congr 1
  · congr 1
    simp [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, add_assoc]
  · congr 1
    simp [BitVec.not_xor_right]

private theorem countRun_read {m : ℕ} (as : List (BitVec m))
    (table : WordTable ℕ m) (t : BitVec m) :
    (countRun (as.map stateKey) table).ret.read t =
      ((operatorWords as.length).map fun bs => table.read (backward (bs.zip as) t)).sum := by
  induction as generalizing table with
  | nil => simp [countRun, operatorWords, backward]
  | cons a as ih =>
    simp only [List.map_cons, countRun, TimeM.ret_bind, TimeM.ret_pure, ih]
    simp only [countAdvance_read, List.sum_map_add, List.length_cons, operatorWords,
      List.map_append, List.sum_append, List.map_map, Function.comp_def,
      List.zip_cons_cons, backward]

private theorem sum_operatorWords (n : ℕ) (f : List Bool → ℕ) :
    ((operatorWords n).map f).sum = ∑ bs : Fin n → Bool, f (List.ofFn bs) := by
  induction n generalizing f with
  | zero => simp [operatorWords]
  | succ n ih =>
    have hb : Function.Bijective
        (fun p : Bool × (Fin n → Bool) => Fin.cons (α := fun _ => Bool) p.1 p.2) := by
      constructor
      · intro ⟨b, bs⟩ ⟨c, cs⟩ h
        have hh := congrFun h 0
        have ht := congrArg Fin.tail h
        simp only [Fin.cons_zero] at hh
        simp only [Fin.tail_cons] at ht
        exact Prod.ext hh ht
      · intro bs
        exact ⟨(bs 0, Fin.tail bs), Fin.cons_self_tail bs⟩
    rw [← Fintype.sum_bijective _ hb
      (fun p : Bool × (Fin n → Bool) => f (List.ofFn (Fin.cons (α := fun _ => Bool) p.1 p.2)))
      (fun bs => f (List.ofFn bs)) (fun _ => rfl), Fintype.sum_prod_type]
    simp [operatorWords, List.map_append, List.map_map, ih,
      List.ofFn_succ, Function.comp_def, add_comm]

private theorem steps_zip {m q : ℕ} (bs : Fin q → Bool) (as : Fin q → BitVec m) :
    (List.ofFn bs).zip (List.ofFn as) = steps bs as := by
  induction q with
  | zero => rfl
  | succ q ih => simp [List.ofFn_succ, steps, ih]

/-- The dynamic-program output is exactly the full solution count at each state. -/
theorem classCounters_read {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) :
    (classCounters (List.ofFn as) s).read t = solutionCount as s t := by
  simp only [classCounters, countRun_read, indicators_read, point_read]
  simp only [List.length_ofFn, sum_operatorWords, solutionCount, steps_zip]
  apply Finset.sum_congr rfl
  intro bs _
  have he : s = backward (steps bs as) t ↔ eval (steps bs as) s = t := by
    constructor
    · intro h; rw [h, eval_backward]
    · intro h; rw [← h, backward_eval]
  simp [he]

/-- All counters fit in at most `q+1` bits. This is the counter-size obligation
needed in addition to the arithmetic-operation count for a bit-cost bridge. -/
theorem classCounters_size_le {m q : ℕ} (as : Fin q → BitVec m) (s t : BitVec m) :
    Nat.size ((classCounters (List.ofFn as) s).read t) ≤ q + 1 := by
  rw [classCounters_read]
  have hb : solutionCount as s t ≤ 2 ^ q := by
    unfold solutionCount
    calc
      _ ≤ ∑ _bs : Fin q → Bool, 1 := by
        apply Finset.sum_le_sum
        intro bs _
        split <;> omega
      _ = _ := by simp
  apply Nat.size_le.2
  have hp := Nat.two_pow_pos q
  rw [pow_succ]
  omega

/-- Project once, then compute every forward low-bit class by the actual counter
program. This retains indexed witnesses even for equal-valued operands. -/
theorem projected_classCounters {m p q : ℕ} (hp : p ≤ m)
    (as : Fin q → BitVec m) (s : BitVec m) (g : BitVec p) :
    (classCounters (List.ofFn fun i => (as i).setWidth p) (s.setWidth p)).read g =
      forwardClassCount p as s g := by
  rw [classCounters_read]
  unfold solutionCount forwardClassCount
  apply Finset.sum_congr rfl
  intro bs _
  have he : steps bs (fun i => (as i).setWidth p) = project p (steps bs as) := by
    simp [steps, project, List.map_ofFn, Function.comp_def]
  rw [he, ← eval_project hp]

/-- Counter addition has the same actual table traversal as Boolean union.
This counts natural additions and table nodes; it does not make addition of
arbitrarily large counters a unit bit operation. -/
theorem sumCounters_work {m : ℕ} (a b : WordTable ℕ m) :
    (sumCounters a b).time + 1 = 2 * 2 ^ m := by
  induction a with
  | leaf v => cases b; rfl
  | node l r ihl ihr =>
    cases b with
    | node c d =>
      have hz := ihl c
      have ho := ihr d
      simp only [sumCounters, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, pow_succ]
      omega

/-- All class counters use linear-in-table work per layer. The work units include
natural additions separately from Boolean/pointer operations. -/
theorem countAdvance_work_le {m : ℕ} (bits : List Bool) (table : WordTable ℕ m) :
    (countAdvance bits table).time ≤ 26 * 2 ^ m + 3 * bits.length + 1 := by
  have ha := addPull_time table (complement bits).ret true
  have hx := xorPull_time table (complement bits).ret
  have hu := sumCounters_work (addPull (complement bits).ret true table).ret
    (xorPull (complement bits).ret table).ret
  simp only [countAdvance, TimeM.time_bind, complement_time]
  omega

theorem countRun_work_le {m : ℕ} (as : List (List Bool)) (table : WordTable ℕ m)
    (hwidth : ∀ a ∈ as, a.length ≤ m) :
    (countRun as table).time ≤ as.length * (26 * 2 ^ m + 3 * m + 3) + 1 := by
  induction as generalizing table with
  | nil => simp [countRun]
  | cons a as ih =>
    have ha := countAdvance_work_le a table
    have hw := hwidth a List.mem_cons_self
    have hr := ih (countAdvance a table).ret (fun b hb => hwidth b (List.mem_cons_of_mem _ hb))
    simp only [countRun, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_cons]
    nlinarith

/-- The inverse-chain counting update pulls back by the forward step. -/
@[expose] def countBackAdvance {m : ℕ} (bits : List Bool) (table : WordTable ℕ m) :
    TimeM ℕ (WordTable ℕ m) := do
  let neg ← complement bits
  let a ← addPull bits false table
  let x ← xorPull neg table
  sumCounters a x

/-- Process the last operand first, as actual inverse-chain evaluation requires. -/
@[expose] def countBackRun {m : ℕ} : List (List Bool) → WordTable ℕ m →
    TimeM ℕ (WordTable ℕ m)
  | [], table => ⟨table, 1⟩
  | a :: as, table => do
    let next ← countBackRun as table
    let result ← countBackAdvance a next
    TimeM.tick 2
    return result

/-- All backward state counters, with the actual target as the singleton seed. -/
@[expose] def backwardCounters {m : ℕ} (as : List (BitVec m)) (t : BitVec m) : WordTable ℕ m :=
  (countBackRun (as.map stateKey) (indicators (point m (stateKey t)).ret)).ret

private theorem countBackAdvance_read {m : ℕ} (table : WordTable ℕ m) (a s : BitVec m) :
    (countBackAdvance (stateKey a) table).ret.read s =
      table.read (step false s a) + table.read (step true s a) := by
  simp [countBackAdvance, sumCounters_read, addPull_read, xorPull_read, step,
    complement_key, BitVec.not_xor_right]

private theorem countBackRun_read {m : ℕ} (as : List (BitVec m))
    (table : WordTable ℕ m) (s : BitVec m) :
    (countBackRun (as.map stateKey) table).ret.read s =
      ((operatorWords as.length).map fun bs => table.read (eval (bs.zip as) s)).sum := by
  induction as generalizing s with
  | nil => simp [countBackRun, operatorWords, eval]
  | cons a as ih =>
    simp only [List.map_cons, countBackRun, TimeM.ret_bind, TimeM.ret_pure,
      countBackAdvance_read, ih, List.length_cons, operatorWords, List.map_append,
      List.sum_append, List.map_map, Function.comp_def, List.zip_cons_cons, eval]

/-- Every backward state is counted once per suffix witness, including coincidences. -/
theorem backwardCounters_read {m q : ℕ} (as : Fin q → BitVec m) (t s : BitVec m) :
    (backwardCounters (List.ofFn as) t).read s = solutionCount as s t := by
  simp only [backwardCounters, countBackRun_read, indicators_read, point_read,
    List.length_ofFn, sum_operatorWords, steps_zip, solutionCount]
  apply Finset.sum_congr rfl
  intro bs _
  simp [eq_comm]

/-- Backward counters also fit in `q+1` bits, despite arbitrary coincident states. -/
theorem backwardCounters_size_le {m q : ℕ} (as : Fin q → BitVec m) (t s : BitVec m) :
    Nat.size ((backwardCounters (List.ofFn as) t).read s) ≤ q + 1 := by
  rw [backwardCounters_read, ← classCounters_read]
  exact classCounters_size_le as s t

/-- The backward projected-class counters are computed by inverse-chain DP. -/
theorem projected_backwardCounters {m p q : ℕ} (hp : p ≤ m)
    (as : Fin q → BitVec m) (t : BitVec m) (g : BitVec p) :
    (backwardCounters (List.ofFn fun i => (as i).setWidth p) (t.setWidth p)).read g =
      backwardClassCount p as t g := by
  rw [backwardCounters_read]
  unfold solutionCount backwardClassCount
  apply Finset.sum_congr rfl
  intro bs _
  have he : steps bs (fun i => (as i).setWidth p) = project p (steps bs as) := by
    simp [steps, project, List.map_ofFn, Function.comp_def]
  have hb : eval (project p (steps bs as)) g = t.setWidth p ↔
      (backward (steps bs as) t).setWidth p = g := by
    rw [backward_project hp]
    constructor
    · intro h; rw [← h, backward_eval]
    · intro h; rw [← h, eval_backward]
  simp only [he, hb]

/-- Traverse two count tables to compute their maximum smaller-class size. -/
@[expose] def maxMin : {m : ℕ} → WordTable ℕ m → WordTable ℕ m → TimeM ℕ ℕ
  | 0, .leaf a, .leaf b => ⟨min a b, 1⟩
  | _ + 1, .node a b, .node c d => do
    let l ← maxMin a c
    let r ← maxMin b d
    TimeM.tick 1
    return max l r

private theorem le_maxMin {m : ℕ} (a b : WordTable ℕ m) (s : BitVec m) :
    min (a.read s) (b.read s) ≤ (maxMin a b).ret := by
  induction a with
  | leaf v => cases b; exact le_refl _
  | @node n l r ihl ihr =>
    cases b with
    | node c d =>
      obtain ⟨⟨s, bit⟩, rfl⟩ := (concat_bijective n).2 s
      cases bit
      · simpa [maxMin, read_node] using (ihl c s).trans (le_max_left _ _)
      · simpa [maxMin, read_node] using (ihr d s).trans (le_max_right _ _)

private theorem maxMin_attained {m : ℕ} (a b : WordTable ℕ m) :
    ∃ s : BitVec m, (maxMin a b).ret = min (a.read s) (b.read s) := by
  induction a with
  | leaf v => cases b; exact ⟨0#0, rfl⟩
  | @node n l r ihl ihr =>
    cases b with
    | node c d =>
      obtain ⟨s, hs⟩ := ihl c
      obtain ⟨t, ht⟩ := ihr d
      by_cases h : (maxMin l c).ret ≤ (maxMin r d).ret
      · refine ⟨t.concat true, ?_⟩
        change max (maxMin l c).ret (maxMin r d).ret = _
        rw [max_eq_right h, read_node, read_node]
        exact ht
      · refine ⟨s.concat false, ?_⟩
        change max (maxMin l c).ret (maxMin r d).ret = _
        rw [max_eq_left (by omega : (maxMin r d).ret ≤ (maxMin l c).ret),
          read_node, read_node]
        exact hs

/-- The executable tree traversal computes the actual finite maximum. -/
theorem maxMin_eq_sup {m : ℕ} (a b : WordTable ℕ m) :
    (maxMin a b).ret = Finset.univ.sup (fun s : BitVec m => min (a.read s) (b.read s)) := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := maxMin_attained a b
    rw [hs]
    exact Finset.le_sup (f := fun s : BitVec m => min (a.read s) (b.read s))
      (Finset.mem_univ s)
  · exact Finset.sup_le fun s _ => le_maxMin a b s

/-- The exact balance is computed from the two projected counter tables before
any full-width class list is generated. This is correctness of the precomputation;
it is not a native bit-runtime certificate for it. -/
theorem computed_balance {m p l r : ℕ} (hp : p ≤ m)
    (left : Fin l → BitVec m) (right : Fin r → BitVec m) (s t : BitVec m) :
    (maxMin (classCounters (List.ofFn fun i => (left i).setWidth p) (s.setWidth p))
      (backwardCounters (List.ofFn fun i => (right i).setWidth p) (t.setWidth p))).ret =
        classBalance p left right s t := by
  rw [maxMin_eq_sup]
  simp only [projected_classCounters hp, projected_backwardCounters hp, classBalance]

/-- Count the max/min traversal, treating counter comparisons as arithmetic
operations rather than pretending that their bit cost is constant. -/
theorem maxMin_work {m : ℕ} (a b : WordTable ℕ m) :
    (maxMin a b).time + 1 = 2 * 2 ^ m := by
  induction a with
  | leaf v => cases b; rfl
  | node l r ihl ihr =>
    cases b with
    | node c d =>
      have hz := ihl c
      have ho := ihr d
      simp only [maxMin, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, pow_succ]
      omega

/-- Inverse-chain counting uses the same linear table work per operand. -/
theorem countBackAdvance_work_le {m : ℕ} (bits : List Bool) (table : WordTable ℕ m) :
    (countBackAdvance bits table).time ≤ 26 * 2 ^ m + 3 * bits.length + 1 := by
  have ha := addPull_time table bits false
  have hx := xorPull_time table (complement bits).ret
  have hu := sumCounters_work (addPull bits false table).ret
    (xorPull (complement bits).ret table).ret
  simp only [countBackAdvance, TimeM.time_bind, complement_time]
  omega

theorem countBackRun_work_le {m : ℕ} (as : List (List Bool)) (table : WordTable ℕ m)
    (hwidth : ∀ a ∈ as, a.length ≤ m) :
    (countBackRun as table).time ≤ as.length * (26 * 2 ^ m + 3 * m + 3) + 1 := by
  induction as with
  | nil => simp [countBackRun]
  | cons a as ih =>
    have ha := countBackAdvance_work_le a (countBackRun as table).ret
    have hw := hwidth a List.mem_cons_self
    have hr := ih (fun b hb => hwidth b (List.mem_cons_of_mem _ hb))
    simp only [countBackRun, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, List.length_cons]
    nlinarith

end WordTable

/-- Exact membership of a full solution in the same low-bit class on both sides. -/
theorem solution_same_class {m p : ℕ} (left right : List (Bool × BitVec m))
    (s t : BitVec m) (h : eval (left ++ right) s = t) :
    ∃! g : BitVec p, (eval left s).setWidth p = g ∧ (backward right t).setWidth p = g := by
  have hm := (eval_append_eq_iff left right s t).1 h
  refine ⟨(eval left s).setWidth p, ⟨rfl, by rw [hm]⟩, ?_⟩
  intro g hg
  exact hg.1.symm

end Cslib.Cryptanalysis.AddXNOR
