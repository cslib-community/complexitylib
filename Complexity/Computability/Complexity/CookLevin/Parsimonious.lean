/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Complexity.CookLevin.Reduction
public import Complexity.Logics.Propositional.CNF.ModelCount
import Complexity.Logics.Propositional.CNF.ModelCount.Relabel

/-!
# The Cook–Levin reduction is parsimonious

The Cook–Levin tableau `tableau tm u L T` has exactly one satisfying assignment for each
certificate `w` of length `L` that makes `tm`, started on `u ++ w`, halt within `T` steps with
output `[true]` (`modelCount_tableau`). Consequently the Cook–Levin reduction of a verifier `V`
maps an instance `a` to a formula with exactly as many satisfying assignments as there are
certificates of the verifier's length that `V` accepts with `a` (`modelCount_reduce`): it is
parsimonious [Valiant][Valiant1979], [Arora and Barak, Section 17.3][AroraBarak09].

Every variable of the tableau is *determined* (`Determined`): it is a certificate bit `j < L`, a
basic feature at a time `t ≤ T`, or a symbol read or a situation at a time `t < T`
(`determined_of_mem_vars_tableau`). A satisfying assignment `σ` agrees on the determined variables
with the assignment read off the run on its own certificate (`eq_runAssignment_of_eval_tableau`):
on the basic features by the soundness of the tableau (`agrees_of_eval_tableau`), on the symbols
read since the read clauses make the actual symbol true and the uniqueness clauses allow only one,
and on the situations since the situation clauses and the uniqueness clauses make a situation true
exactly when its state and its symbols read are. Two satisfying assignments with the same
certificate therefore agree on every variable of the tableau. Conversely, when `T > 0` the input
clauses mention every certificate bit, so two satisfying assignments that agree on the variables
of the tableau have the same certificate; when `T = 0` no run has halted and the tableau is
unsatisfiable.

## Main definitions

* `Cslib.Complexity.CookLevin.Determined`: the variables determined by the certificate.

## Main results

* `Cslib.Complexity.CookLevin.determined_of_mem_vars_tableau`: the variables of the tableau are
  determined.
* `Cslib.Complexity.CookLevin.eq_runAssignment_of_eval_tableau`: a satisfying assignment is
  determined by its certificate.
* `Cslib.Complexity.CookLevin.modelCount_tableau`: the number of satisfying assignments of the
  tableau is the number of accepted certificates.
* `Cslib.Complexity.CookLevin.modelCount_reduce`: the Cook–Levin reduction is parsimonious.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 17.3.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature Cslib.Logic.PL

variable {k : ℕ} {State : Type} [Fintype State]

/-- The variables of the tableau for inputs of length `n`, certificates of length `L` and `T`
steps that a satisfying assignment determines from its certificate: the certificate bits `j < L`,
the basic features at times `t ≤ T`, and the symbols read and the situations at times `t < T`. -/
def Determined (n L T : ℕ) (v : Var k State) : Prop :=
  (∃ j < L, v = .cert j) ∨ (∃ t ≤ T, ∃ φ ∈ basic n T, v = .holds t φ) ∨
    ∃ t < T, (∃ i s, v = .holds t (.read i s)) ∨ (∃ s, v = .holds t (.inRead s)) ∨
      ∃ y, v = .holds t (.sit y)

namespace Determined

variable {n L T : ℕ}

private theorem cert {j : ℕ} (hj : j < L) : Determined (State := State) (k := k) n L T (.cert j) :=
  Or.inl ⟨j, hj, rfl⟩

private theorem holds_basic {t : ℕ} (ht : t ≤ T) {φ : Feature k State} (hφ : φ ∈ basic n T) :
    Determined n L T (.holds t φ) :=
  Or.inr (Or.inl ⟨t, ht, φ, hφ, rfl⟩)

private theorem holds_read {t : ℕ} (ht : t < T) (i : Fin k) (s : Option Bool) :
    Determined (State := State) n L T (.holds t (.read i s)) :=
  Or.inr (Or.inr ⟨t, ht, Or.inl ⟨i, s, rfl⟩⟩)

private theorem holds_inRead {t : ℕ} (ht : t < T) (s : Option Bool) :
    Determined (State := State) (k := k) n L T (.holds t (.inRead s)) :=
  Or.inr (Or.inr ⟨t, ht, Or.inr (Or.inl ⟨s, rfl⟩)⟩)

private theorem holds_sit {t : ℕ} (ht : t < T) (y : Situation k State) :
    Determined n L T (.holds t (.sit y)) :=
  Or.inr (Or.inr ⟨t, ht, Or.inr (Or.inr ⟨y, rfl⟩)⟩)

end Determined

/-! ### The variables of the tableau -/

section Vars

variable [DecidableEq State] {tm : MultiTapeTM k Bool State} {u : List Bool}
  {L T : ℕ} {c : Clause (Var k State)} {l : Literal (Var k State)}

omit [DecidableEq State] in
private theorem determined_of_mem_initClauses (hc : c ∈ initClauses tm T) (hl : l ∈ c) :
    Determined (u.length + L) L T l.1 := by
  simp only [initClauses, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.mem_finRange, mem_windowList, List.not_mem_nil, or_false, true_and] at hc
  rcases hc with (rfl | rfl | rfl) | ⟨i, rfl | ⟨z, hz, rfl⟩⟩ <;>
    obtain rfl := List.mem_singleton.1 hl
  exacts [.holds_basic (Nat.zero_le _) (state_mem_basic _),
    .holds_basic (Nat.zero_le _) (inPos_mem_basic (by omega)),
    .holds_basic (Nat.zero_le _) (out_mem_basic _),
    .holds_basic (Nat.zero_le _) (head_mem_basic i (by simp)),
    .holds_basic (Nat.zero_le _) (cell_mem_basic i hz _)]

private theorem determined_of_mem_oneHotClauses {t : ℕ} (ht : t ≤ T)
    (hc : c ∈ oneHotClauses u L T t) (hl : l ∈ c) : Determined (u.length + L) L T l.1 := by
  obtain ⟨g, hg, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨φ, hφ, he⟩ := List.mem_map.1 (CNF.fst_mem_of_mem_exactlyOne hc hl)
  rw [← he]
  exact .holds_basic ht (mem_basic_iff_exists_mem_groups.2 ⟨g, hg, hφ⟩)

omit [DecidableEq State] in
private theorem determined_of_mem_inputClauses {t j : ℕ} (ht : t < T)
    (hj : j < u.length + L + 2) (hc : c ∈ inputClauses (k := k) (State := State) u L t j)
    (hl : l ∈ c) :
    Determined (u.length + L) L T l.1 := by
  have hpos : Determined (State := State) (k := k) (u.length + L) L T (.holds t (.inPos j)) :=
    .holds_basic ht.le (inPos_mem_basic hj)
  unfold inputClauses at hc
  split_ifs at hc with h₁ h₂
  · obtain rfl := List.mem_singleton.1 hc
    rcases Clause.fst_mem_of_mem_imp hl with h | h
    · rw [List.mem_singleton.1 h]
      exact hpos
    · rw [h]
      exact .holds_inRead ht _
  · obtain rfl := List.mem_singleton.1 hc
    rcases Clause.fst_mem_of_mem_imp hl with h | h
    · rw [List.mem_singleton.1 h]
      exact hpos
    · rw [h]
      exact .holds_inRead ht _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · rcases Clause.fst_mem_of_mem_impLits hl with ⟨h, hh, he⟩ | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl <;> rw [he]
        · exact hpos
        · exact .cert (by omega)
      · rw [h]
        exact .holds_inRead ht _

omit [DecidableEq State] in
private theorem determined_of_mem_readClauses {t : ℕ} (ht : t < T)
    (hc : c ∈ readClauses u L T t) (hl : l ∈ c) : Determined (u.length + L) L T l.1 := by
  simp only [readClauses, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
    mem_windowList, mem_symbols, true_and, List.mem_range] at hc
  rcases hc with ⟨i, z, hz, s, rfl⟩ | ⟨j, hj, hc⟩
  · rcases Clause.fst_mem_of_mem_imp hl with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> rw [h]
      exacts [.holds_basic ht.le (head_mem_basic i hz), .holds_basic ht.le (cell_mem_basic i hz s)]
    · rw [h]
      exact .holds_read ht i s
  · exact determined_of_mem_inputClauses ht hj hc hl

omit [DecidableEq State] in
private theorem determined_of_mem_sitClauses {t : ℕ} (ht : t < T) (hc : c ∈ sitClauses t)
    (hl : l ∈ c) : Determined (u.length + L) L T l.1 := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hc
  rcases Clause.fst_mem_of_mem_imp hl with h | h
  · simp only [List.mem_cons, List.mem_map, List.mem_finRange, true_and] at h
    rcases h with h | h | ⟨i, h⟩
    · rw [h]
      exact .holds_basic ht.le (state_mem_basic _)
    · rw [h]
      exact .holds_inRead ht _
    · rw [← h]
      exact .holds_read ht i _
  · rw [h]
    exact .holds_sit ht y

private theorem determined_of_mem_uniqueClauses {t : ℕ} (ht : t < T)
    (hc : c ∈ uniqueClauses t) (hl : l ∈ c) : Determined (u.length + L) L T l.1 := by
  simp only [uniqueClauses, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and,
    mem_situations, List.mem_cons, List.mem_map] at hc
  rcases hc with (⟨i, hc⟩ | hc) | ⟨y, rfl | rfl | ⟨i, rfl⟩⟩
  · obtain ⟨s, -, he⟩ := List.mem_map.1 (CNF.fst_mem_of_mem_atMostOne hc hl)
    rw [← he]
    exact .holds_read ht i s
  · obtain ⟨s, -, he⟩ := List.mem_map.1 (CNF.fst_mem_of_mem_atMostOne hc hl)
    rw [← he]
    exact .holds_inRead ht s
  -- each implication `sit y → x` mentions `sit y` and its conclusion `x`
  all_goals
    rcases Clause.fst_mem_of_mem_imp hl with h | h
    · rw [List.mem_singleton.1 h]
      exact .holds_sit ht y
    rw [h]
  · exact .holds_basic ht.le (state_mem_basic _)
  · exact .holds_inRead ht _
  · exact .holds_read ht i _

private theorem determined_of_mem_stepClauses {t : ℕ} (ht : t < T)
    (hc : c ∈ stepClauses tm u L T t) (hl : l ∈ c) : Determined (u.length + L) L T l.1 := by
  obtain ⟨φ, hφ, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  rcases Clause.fst_mem_of_mem_impLits hl with ⟨h, hh, he⟩ | h
  · obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hh
    rw [he]
    rcases mem_basic_of_mem_stepTerms tm hφ hc' hl' with hb | ⟨y, rfl⟩
    · exact .holds_basic ht.le hb
    · exact .holds_sit ht y
  · rw [h]
    exact .holds_basic ht hφ

omit [DecidableEq State] in
private theorem determined_of_mem_acceptClauses
    (hc : c ∈ acceptClauses (k := k) (State := State) T) (hl : l ∈ c) :
    Determined (u.length + L) L T l.1 := by
  simp only [acceptClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> obtain rfl := List.mem_singleton.1 hl
  exacts [.holds_basic le_rfl (state_mem_basic _), .holds_basic le_rfl (out_mem_basic _)]

/-- **The variables of the tableau are determined** by the certificate. -/
theorem determined_of_mem_vars_tableau {v : Var k State} (hv : v ∈ (tableau tm u L T).vars) :
    Determined (u.length + L) L T v := by
  obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.1 hv
  change Determined (u.length + L) L T (v, b).1
  simp only [tableau, List.mem_append, List.mem_flatMap, List.mem_range] at hc
  rcases hc with ((hc | ⟨t, ht, hc⟩) | ⟨t, ht, ((hc | hc) | hc) | hc⟩) | hc
  · exact determined_of_mem_initClauses hc hl
  · exact determined_of_mem_oneHotClauses (by omega) hc hl
  · exact determined_of_mem_readClauses ht hc hl
  · exact determined_of_mem_sitClauses ht hc hl
  · exact determined_of_mem_uniqueClauses ht hc hl
  · exact determined_of_mem_stepClauses ht hc hl
  · exact determined_of_mem_acceptClauses hc hl

/-- When the tableau unrolls at least one step, it mentions every certificate bit. -/
private theorem cert_mem_vars_tableau (hT : 0 < T) {j : ℕ} (hj : j < L) :
    Var.cert j ∈ (tableau tm u L T).vars := by
  refine CNF.mem_vars.2 ⟨Clause.impLits [(.holds 0 (.inPos (u.length + 1 + j)), true),
    (.cert j, true)] (.holds 0 (.inRead (some true))), ?_, false, ?_⟩
  · simp only [tableau, List.mem_append, List.mem_flatMap, List.mem_range]
    refine Or.inl (Or.inr ⟨0, hT, Or.inl (Or.inl (Or.inl ?_))⟩)
    simp only [readClauses, List.mem_append, List.mem_flatMap, List.mem_range]
    refine Or.inr ⟨u.length + 1 + j, by omega, ?_⟩
    unfold inputClauses
    split_ifs with h₁ h₂
    · omega
    · omega
    · rw [show u.length + 1 + j - 1 - u.length = j by omega]
      exact List.mem_cons_self ..
  · simp [Clause.impLits, Std.Sat.Literal.negate]

end Vars

/-! ### Satisfying assignments are determined by their certificates -/

section Determination

variable [DecidableEq State] {tm : MultiTapeTM k Bool State} {u : List Bool}
  {L T : ℕ} {σ : Var k State → Bool}

/-- **A satisfying assignment is determined by its certificate**: on the determined variables it
agrees with the assignment read off the run on its certificate. -/
theorem eq_runAssignment_of_eval_tableau (h : (tableau tm u L T).eval σ = true)
    {v : Var k State} (hv : Determined (u.length + L) L T v) :
    σ v = runAssignment tm u (certWord σ L) v := by
  obtain ⟨-, -, hsteps, -⟩ := eval_tableau.1 h
  have hA := agrees_of_eval_tableau h
  have hb (t : ℕ) (ht : t ≤ T) (i : Fin k) :
      |(tm.runFrom (tm.initCfg (u ++ certWord σ L)) t).workTapePos i| ≤ T :=
    (abs_workTapePos_runFrom_le _ t i).trans (by exact_mod_cast ht)
  have hread (t : ℕ) (ht : t < T) (i : Fin k) (s : Option Bool) :
      σ (.holds t (.read i s)) = true ↔
        (Feature.read i s).Holds (tm.runFrom (tm.initCfg (u ++ certWord σ L)) t) := by
    obtain ⟨hr, -, hu, -⟩ := hsteps t ht
    have hact := ((eval_readClauses t).1 hr).1 i _ _ (hb t ht.le i)
      ((hA t ht.le _ (head_mem_basic i (hb t ht.le i))).2 rfl)
      ((hA t ht.le _ (cell_mem_basic i (hb t ht.le i) _)).2 rfl)
    rw [holds_read]
    exact ⟨fun hs => ((eval_uniqueClauses t).1 hu).1 i _ _ hact hs, fun hs => hs ▸ hact⟩
  have hinRead (t : ℕ) (ht : t < T) (s : Option Bool) :
      σ (.holds t (.inRead s)) = true ↔
        (Feature.inRead s : Feature k State).Holds
          (tm.runFrom (tm.initCfg (u ++ certWord σ L)) t) := by
    obtain ⟨hr, -, hu, -⟩ := hsteps t ht
    have hp := (tm.runFrom (tm.initCfg (u ++ certWord σ L)) t).inputPos.isLt
    simp only [List.length_append, length_certWord] at hp
    have hact := ((eval_readClauses t).1 hr).2 _ hp ((hA t ht.le _ (inPos_mem_basic hp)).2 rfl)
    rw [← Cfg.inputSymbol_eq_inputAt] at hact
    rw [holds_inRead]
    exact ⟨fun hs => ((eval_uniqueClauses t).1 hu).2.1 _ _ hact hs, fun hs => hs ▸ hact⟩
  rcases hv with ⟨j, hj, rfl⟩ | ⟨t, ht, φ, hφ, rfl⟩ | ⟨t, ht, ⟨i, s, rfl⟩ | ⟨s, rfl⟩ | ⟨y, rfl⟩⟩
  · simp [runAssignment, certWord, List.getD_eq_getElem?_getD, hj]
  · rw [Bool.eq_iff_iff, runAssignment_holds]
    exact hA t ht φ hφ
  · rw [Bool.eq_iff_iff, runAssignment_holds]
    exact hread t ht i s
  · rw [Bool.eq_iff_iff, runAssignment_holds]
    exact hinRead t ht s
  · rw [Bool.eq_iff_iff, runAssignment_holds]
    obtain ⟨hr, hs, hu, -⟩ := hsteps t ht
    refine ⟨fun hy => ?_, (hA t ht.le).sit (hb t ht.le) hr hs⟩
    obtain ⟨hq, hi, hri⟩ := ((eval_uniqueClauses t).1 hu).2.2 y hy
    exact (holds_sit_iff y).2 ⟨(hA t ht.le _ (state_mem_basic _)).1 hq, (hinRead t ht _).1 hi,
      fun i => (hread t ht i _).1 (hri i)⟩

/-- Two satisfying assignments with the same certificate agree on the variables of the
tableau. -/
private theorem eq_of_eval_tableau_of_certWord_eq {τ : Var k State → Bool}
    (hσ : (tableau tm u L T).eval σ = true) (hτ : (tableau tm u L T).eval τ = true)
    (hc : certWord σ L = certWord τ L) {v : Var k State} (hv : v ∈ (tableau tm u L T).vars) :
    σ v = τ v := by
  have hd := determined_of_mem_vars_tableau hv
  rw [eq_runAssignment_of_eval_tableau hσ hd, eq_runAssignment_of_eval_tableau hτ hd, hc]

/-- A tableau unrolled for no step is unsatisfiable: the initial configuration is running. -/
private theorem eval_tableau_zero : (tableau tm u L 0).eval σ = false := by
  by_contra h
  have hz := (exists_eval_tableau_iff (tm := tm) (u := u) (T := 0) (z := certWord σ L)).1
    ⟨σ, by rw [length_certWord], by rw [length_certWord]; simpa using h⟩
  simp [runFrom] at hz

end Determination

/-! ### Counting satisfying assignments -/

section Counting

variable [DecidableEq State] {tm : MultiTapeTM k Bool State} {u : List Bool}
  {L T : ℕ}

/-- **The Cook–Levin tableau is parsimonious**: its satisfying assignments correspond one to one
to the certificates `w` of length `L` that make `tm`, started on `u ++ w`, halt within `T` steps
with output `[true]`. -/
theorem modelCount_tableau :
    (tableau tm u L T).modelCount = (Finset.univ.filter fun w : Fin L → Bool =>
      (tm.runFrom (tm.initCfg (u ++ List.ofFn w)) T).state = none ∧
        (tm.runFrom (tm.initCfg (u ++ List.ofFn w)) T).output = [true]).card := by
  refine CNF.modelCount_eq_card_filter (fun σ (j : Fin L) => σ (.cert j)) _
    (fun σ τ hσ hτ => ⟨fun h v hv => ?_, fun h => funext fun j => ?_⟩) fun w => ⟨?_, ?_⟩
  · refine eq_of_eval_tableau_of_certWord_eq hσ hτ ?_ hv
    rw [certWord_eq_ofFn, certWord_eq_ofFn, h]
  · rcases Nat.eq_zero_or_pos T with rfl | hT
    · rw [eval_tableau_zero] at hσ
      exact absurd hσ Bool.false_ne_true
    · exact h _ (cert_mem_vars_tableau hT j.2)
  · rintro ⟨hhalt, hout⟩
    refine ⟨runAssignment tm u (List.ofFn w), eval_tableau_runAssignment (by simp) hhalt hout,
      funext fun j => ?_⟩
    simp [runAssignment, List.getD_eq_getElem?_getD]
  · rintro ⟨σ, hσ, rfl⟩
    rw [← certWord_eq_ofFn]
    exact (exists_eval_tableau_iff (z := certWord σ L)).1
      ⟨σ, by rw [length_certWord], by rwa [length_certWord]⟩

/-- **The Cook–Levin reduction is parsimonious.** Under the hypotheses of `reduce_mem_SAT_iff`,
the formula `reduce tm p c d enc a` has exactly as many satisfying assignments as there are
certificates `w` of length `p (enc a).length` with `V (a, w) = true`. -/
theorem modelCount_reduce {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {c d : ℕ} (a : α)
    (hrun : ∀ w : List Bool, w.length = p.eval (enc a).length →
      (tm.runFrom (tm.initCfg (encPair enc encBits (a, w)))
          (c * ((encPair enc encBits (a, w)).length + 1) ^ d)).state = none ∧
        (tm.runFrom (tm.initCfg (encPair enc encBits (a, w)))
          (c * ((encPair enc encBits (a, w)).length + 1) ^ d)).output = [V (a, w)]) :
    (reduce tm p c d enc a).modelCount = acceptCount V a (p.eval (enc a).length) := by
  rw [reduce, parameters, CNF.modelCount_relabel Var.index_injective, modelCount_tableau,
    acceptCount]
  refine congrArg Finset.card (Finset.filter_congr fun w _ => ?_)
  have hw : (List.ofFn w).length = p.eval (enc a).length := List.length_ofFn
  have hlen : (encPair enc encBits (a, List.ofFn w)).length =
      2 * (enc a).length + 1 + p.eval (enc a).length := by
    rw [length_encPair, encBits_apply, hw]
  obtain ⟨hhalt, hout⟩ := hrun _ hw
  rw [hlen, encPair_apply, encBits_apply] at hhalt hout
  rw [hhalt, hout]
  simp

end Counting

end Cslib.Complexity.CookLevin
