/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Tableau

/-!
# Correctness of the Cook–Levin tableau

`tableau tm u L T` is satisfiable exactly when some certificate `w` of length `L` makes `tm`,
started on `u ++ w`, halt within `T` steps with output `[true]`. More precisely, for a fixed
certificate `z`, it has a satisfying assignment encoding `z` exactly when `tm`, started on
`u ++ z`, has halted after `T` steps with output `[true]` (`exists_eval_tableau_iff`).

Each family of clauses is first characterised semantically (`eval_initClauses`,
`eval_readClauses`, `eval_stepClauses`, …). The uniqueness clauses (`eval_uniqueClauses`) are not
needed for soundness; they make the satisfying assignments unique for each certificate
(`CslibFrontier/Computability/Complexity/CookLevin/Parsimonious.lean`), and completeness checks that
the assignment read off the run
satisfies them. Soundness then shows, by induction on time, that a
satisfying assignment describes the run on the certificate it encodes (`Agrees`,
`agrees_of_eval_tableau`):
by the one-hot clauses it suffices that the basic features holding at time `t + 1` are true
(`Agrees.of_oneHot`), and each of them follows from a term of its step equation
(`Turing.MultiTapeTM.Feature.holds_step_iff_exists_stepTerms`) through a step clause.
Completeness reads an assignment off the run (`runAssignment`); its step clauses hold by the same
step equation.

## Main results

* `Cslib.Complexity.CookLevin.exists_eval_tableau_iff`: the tableau with fixed certificate bits.
* `Cslib.Complexity.CookLevin.tableau_satisfiable_iff`: the tableau is correct.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature Cslib.Logic.PL

variable {k : ℕ} {State : Type} {tm : MultiTapeTM k Bool State} {u : List Bool} {L T : ℕ}
  {σ : Var k State → Bool}

/-- The certificate encoded by an assignment. -/
def certWord (σ : Var k State → Bool) (L : ℕ) : List Bool := (List.range L).map fun j => σ (.cert j)

@[simp] theorem length_certWord (σ : Var k State → Bool) (L : ℕ) : (certWord σ L).length = L := by
  simp [certWord]

theorem certWord_eq_ofFn (σ : Var k State → Bool) (L : ℕ) :
    certWord σ L = List.ofFn fun j : Fin L => σ (.cert j) :=
  List.ext_getElem (by simp) fun j _ _ => by simp [certWord]

/-! ### Semantics of the clause families -/

/-- The initial clauses fix the initial configuration. -/
theorem eval_initClauses :
    (initClauses tm T).eval σ = true ↔
      σ (.holds 0 (.state (some tm.q₀))) = true ∧ σ (.holds 0 (.inPos 1)) = true ∧
        σ (.holds 0 (.out .empty)) = true ∧
        ∀ i, σ (.holds 0 (.head i 0)) = true ∧
          ∀ z : ℤ, |z| ≤ T → σ (.holds 0 (.cell i z none)) = true := by
  simp [initClauses, CNF.eval_flatMap_eq_true_iff, CNF.eval_map_eq_true_iff]

/-- The input clauses at position `j`: the input head there reads the input symbol, a certificate
bit included. -/
private theorem eval_inputClauses (t j : ℕ) :
    (inputClauses (k := k) (State := State) u L t j).eval σ = true ↔
      (σ (.holds t (.inPos j)) = true →
        σ (.holds t (.inRead (inputAt (u ++ certWord σ L) j))) = true) := by
  unfold inputClauses
  split_ifs with h₁ h₂
  · have : inputAt (u ++ certWord σ L) j = none := by
      rcases h₁ with rfl | h₁
      · rfl
      · simp only [inputAt, show j ≠ 0 by omega, ite_false]
        exact List.getElem?_eq_none (by simp only [List.length_append, length_certWord]; omega)
    simp [this]
  · have : inputAt (u ++ certWord σ L) j = u[j - 1]? := by
      simp only [inputAt, show j ≠ 0 by omega, ite_false]
      exact List.getElem?_append_left (by omega)
    simp [this]
  · have : inputAt (u ++ certWord σ L) j = some (σ (.cert (j - 1 - u.length))) := by
      simp only [inputAt, show j ≠ 0 by omega, ite_false]
      rw [List.getElem?_append_right (by omega)]
      simp [certWord, List.getElem?_map, List.getElem?_range (show j - 1 - u.length < L by omega)]
    rw [this]
    cases hc : σ (.cert (j - 1 - u.length)) <;> cases hp : σ (.holds t (.inPos j)) <;>
      simp [hc, hp]

/-- The read clauses: the symbol a head reads, from its position and the cell there, is true. -/
theorem eval_readClauses (t : ℕ) :
    (readClauses (k := k) (State := State) u L T t).eval σ = true ↔
      (∀ i (z : ℤ) s, |z| ≤ T → σ (.holds t (.head i z)) = true →
        σ (.holds t (.cell i z s)) = true → σ (.holds t (.read i s)) = true) ∧
      ∀ j < u.length + L + 2, σ (.holds t (.inPos j)) = true →
        σ (.holds t (.inRead (inputAt (u ++ certWord σ L) j))) = true := by
  simp only [readClauses, CNF.eval_append, Bool.and_eq_true, CNF.eval_flatMap_eq_true_iff,
    CNF.eval_map_eq_true_iff, List.mem_finRange, mem_windowList, List.mem_range,
    eval_inputClauses, Clause.eval_imp, List.mem_cons, List.mem_nil_iff, or_false,
    forall_eq_or_imp, forall_eq, true_implies, mem_symbols]
  exact ⟨fun ⟨h, h'⟩ => ⟨fun i z s hz hh hc => h i z hz s ⟨hh, hc⟩, h'⟩,
    fun ⟨h, h'⟩ => ⟨fun i z hz s ⟨hh, hc⟩ => h i z s hz hh hc, h'⟩⟩

/-- The accept clauses ask for a halted run with output `[true]`. -/
private theorem eval_acceptClauses :
    (acceptClauses (k := k) (State := State) T).eval σ = true ↔
      σ (.holds T (.state none)) = true ∧ σ (.holds T (.out (.one true))) = true := by
  simp [acceptClauses]

section Soundness

variable [Fintype State]

/-- The situation clauses: a situation holds when its state and the symbols it reads do. -/
private theorem eval_sitClauses (t : ℕ) :
    (sitClauses (k := k) (State := State) t).eval σ = true ↔
      ∀ y : Situation k State, σ (.holds t (.state (some y.1))) = true →
        σ (.holds t (.inRead y.2.1)) = true → (∀ i, σ (.holds t (.read i (y.2.2 i))) = true) →
          σ (.holds t (.sit y)) = true := by
  simp [sitClauses, CNF.eval_map_eq_true_iff]

variable [DecidableEq State] in
/-- The uniqueness clauses: each head reads at most one symbol, and a true situation has its
state and symbols read true. -/
theorem eval_uniqueClauses (t : ℕ) :
    (uniqueClauses (k := k) (State := State) t).eval σ = true ↔
      (∀ i s s', σ (.holds t (.read i s)) = true → σ (.holds t (.read i s')) = true → s = s') ∧
      (∀ s s', σ (.holds t (.inRead s)) = true → σ (.holds t (.inRead s')) = true → s = s') ∧
      ∀ y : Situation k State, σ (.holds t (.sit y)) = true →
        σ (.holds t (.state (some y.1))) = true ∧ σ (.holds t (.inRead y.2.1)) = true ∧
          ∀ i, σ (.holds t (.read i (y.2.2 i))) = true := by
  simp only [uniqueClauses, CNF.eval_append, Bool.and_eq_true, CNF.eval_flatMap_eq_true_iff,
    CNF.eval_atMostOne, List.forall_mem_map, List.mem_finRange, mem_symbols, mem_situations,
    true_implies, CNF.eval_cons, CNF.eval_map_eq_true_iff, Clause.eval_imp, List.mem_cons,
    List.mem_nil_iff, or_false, forall_eq, Var.holds.injEq, Feature.read.injEq,
    Feature.inRead.injEq, true_and]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    exact ⟨h₁, h₂, fun y hy => ⟨(h₃ y).1 hy, (h₃ y).2.1 hy, fun i => (h₃ y).2.2 i hy⟩⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨h₁, h₂⟩, fun y => ⟨fun hy => (h₃ y hy).1, fun hy => (h₃ y hy).2.1,
      fun i hy => (h₃ y hy).2.2 i⟩⟩

/-- An assignment describes the configuration `cfg` at time `t`: the basic features true at time
`t` are those holding of `cfg`. -/
def Agrees (σ : Var k State → Bool) (n T t : ℕ) {input : List Bool}
    (cfg : Cfg k Bool State input) : Prop :=
  ∀ φ ∈ basic n T, σ (.holds t φ) = true ↔ φ.Holds cfg

/-- Under the read and situation clauses, the situation of a configuration that an assignment
describes is true. -/
theorem Agrees.sit {cfg : Cfg k Bool State (u ++ certWord σ L)} {t : ℕ}
    (hA : Agrees σ (u.length + L) T t cfg) (hb : ∀ i, |cfg.workTapePos i| ≤ T)
    (hread : (readClauses u L T t).eval σ = true) (hsit : (sitClauses t).eval σ = true)
    {y : Situation k State} (hy : (Feature.sit y).Holds cfg) : σ (.holds t (.sit y)) = true := by
  obtain ⟨hs, hi, hr⟩ := (holds_sit_iff y).1 hy
  obtain ⟨hreadW, hreadI⟩ := (eval_readClauses t).1 hread
  have hp := cfg.inputPos.isLt
  refine (eval_sitClauses t).1 hsit y ((hA _ (state_mem_basic _)).2 hs) ?_ fun i => ?_
  · rw [← holds_inRead.1 hi, Cfg.inputSymbol_eq_inputAt]
    refine hreadI _ (by simp only [List.length_append, length_certWord] at hp; omega) ?_
    exact (hA _ (inPos_mem_basic (by simpa using hp))).2 rfl
  · rw [← holds_read.1 (hr i)]
    exact hreadW i _ _ (hb i) ((hA _ (head_mem_basic i (hb i))).2 rfl)
      ((hA _ (cell_mem_basic i (hb i) _)).2 rfl)

variable [DecidableEq State]

/-- The step clauses impose the step equation of every basic feature. -/
theorem eval_stepClauses (t : ℕ) :
    (stepClauses tm u L T t).eval σ = true ↔
      ∀ φ ∈ basic (u.length + L) T, ∀ c ∈ stepTerms tm (u.length + L) T φ,
        (∀ l ∈ c, σ (.holds t l.1) = l.2) → σ (.holds (t + 1) φ) = true := by
  simp only [stepClauses, CNF.eval_flatMap_eq_true_iff, CNF.eval_map_eq_true_iff,
    Clause.eval_impLits, List.forall_mem_map]

/-- The one-hot clauses at time `t`. -/
private theorem eval_oneHotClauses (t : ℕ) :
    (oneHotClauses (k := k) (State := State) u L T t).eval σ = true ↔
      ∀ g ∈ groups (u.length + L) T, (CNF.exactlyOne (g.map (.holds t))).eval σ = true :=
  CNF.eval_flatMap_eq_true_iff ..

/-- The tableau holds when each of its families does, at each time. -/
theorem eval_tableau :
    (tableau tm u L T).eval σ = true ↔
      (initClauses tm T).eval σ = true ∧ (∀ t ≤ T, (oneHotClauses u L T t).eval σ = true) ∧
        (∀ t < T, (readClauses u L T t).eval σ = true ∧ (sitClauses t).eval σ = true ∧
          (uniqueClauses t).eval σ = true ∧ (stepClauses tm u L T t).eval σ = true) ∧
        (acceptClauses T).eval σ = true := by
  simp only [tableau, CNF.eval_append, Bool.and_eq_true, CNF.eval_flatMap_eq_true_iff,
    List.mem_range, Nat.lt_succ_iff, and_assoc]

/-! ### Soundness -/

/-- Under the one-hot clauses at time `t`, an assignment describes `cfg` at time `t` as soon as
the basic features holding of `cfg` are true. -/
theorem Agrees.of_oneHot {input : List Bool} {cfg : Cfg k Bool State input} {t : ℕ}
    (hlen : input.length = u.length + L) (hone : (oneHotClauses u L T t).eval σ = true)
    (hb : ∀ i, |cfg.workTapePos i| ≤ T)
    (h : ∀ φ ∈ basic (u.length + L) T, φ.Holds cfg → σ (.holds t φ) = true) :
    Agrees σ (u.length + L) T t cfg := by
  intro φ hφ
  obtain ⟨g, hg, hφg⟩ := List.mem_flatten.1 hφ
  obtain ⟨ψ, hψg, hψ⟩ := exists_holds_of_mem_groups hlen hb hg
  rw [CNF.eq_true_iff_of_eval_exactlyOne_map (Var.holds_right_injective t)
    ((eval_oneHotClauses t).1 hone g hg) hψg (h ψ (List.mem_flatten.2 ⟨g, hg, hψg⟩) hψ) hφg]
  exact ⟨fun e => e ▸ hψ, fun hφ' => eq_of_holds_of_mem_groups hg hφg hψg hφ' hψ⟩

/-- One step of the induction: if `σ` describes `cfg` at time `t` and satisfies the clauses of
time `t`, it describes the next configuration at time `t + 1`. -/
private theorem Agrees.step {cfg : Cfg k Bool State (u ++ certWord σ L)} {t : ℕ}
    (hA : Agrees σ (u.length + L) T t cfg) (hb : ∀ i, |cfg.workTapePos i| ≤ T)
    (hb' : ∀ i, |(tm.step cfg).workTapePos i| ≤ T)
    (hread : (readClauses u L T t).eval σ = true) (hsit : (sitClauses t).eval σ = true)
    (hstep : (stepClauses tm u L T t).eval σ = true)
    (hone : (oneHotClauses u L T (t + 1)).eval σ = true) :
    Agrees σ (u.length + L) T (t + 1) (tm.step cfg) := by
  have hlen : (u ++ certWord σ L).length = u.length + L := by simp
  refine Agrees.of_oneHot hlen hone hb' fun φ hφ hφs => ?_
  obtain ⟨c, hc, hct⟩ := (holds_step_iff_exists_stepTerms tm hlen hb hφ).1 hφs
  refine (eval_stepClauses t).1 hstep φ hφ c hc fun l hl => ?_
  rcases mem_basic_of_mem_stepTerms tm hφ hc hl with hlb | ⟨y, rfl⟩
  · rw [Bool.eq_iff_iff, hA _ hlb]
    exact hct l hl
  · exact hA.sit hb hread hsit ((hct _ hl).2 rfl)

/-- A satisfying assignment describes the run on the certificate it encodes, up to time `T`. -/
theorem agrees_of_eval_tableau (h : (tableau tm u L T).eval σ = true) :
    ∀ t ≤ T, Agrees σ (u.length + L) T t (tm.runFrom (tm.initCfg (u ++ certWord σ L)) t) := by
  obtain ⟨hinit, hone, hsteps, -⟩ := eval_tableau.1 h
  have hb (t : ℕ) (ht : t ≤ T) (i : Fin k) :
      |(tm.runFrom (tm.initCfg (u ++ certWord σ L)) t).workTapePos i| ≤ T :=
    (abs_workTapePos_runFrom_le _ t i).trans (by exact_mod_cast ht)
  intro t ht
  induction t with
  | zero =>
    obtain ⟨i₁, i₂, i₃, i₄⟩ := eval_initClauses.1 hinit
    refine Agrees.of_oneHot (by simp) (hone 0 (Nat.zero_le _)) (hb 0 ht) fun φ hφ hφs => ?_
    rcases mem_basic.1 hφ with ⟨q, rfl⟩ | ⟨j, -, rfl⟩ | ⟨i, z, hz, rfl⟩ | ⟨i, z, s, hz, rfl⟩ |
      ⟨o, rfl⟩ <;>
      simp only [Feature.Holds, runFrom, Function.iterate_zero_apply, initCfg_eq_wordsCfg,
        wordsCfg, tapeOfList_nil] at hφs <;> subst hφs
    exacts [i₁, i₂, (i₄ i).1, (i₄ i).2 z hz, i₃]
  | succ t ih =>
    obtain ⟨hread, hsit, -, hstep⟩ := hsteps t (by omega)
    have hb' := hb (t + 1) ht
    rw [runFrom_succ] at hb' ⊢
    exact (ih (by omega)).step (hb t (by omega)) hb' hread hsit hstep (hone (t + 1) ht)

end Soundness

/-! ### Completeness -/

section Completeness

variable [DecidableEq State]

/-- The assignment read off the run of `tm` on `u ++ w`: each feature variable says whether the
feature holds of the run, and the certificate variables spell `w`. -/
noncomputable def runAssignment (tm : MultiTapeTM k Bool State) (u w : List Bool) :
    Var k State → Bool
  | .holds t φ => decide (φ.Holds (tm.runFrom (tm.initCfg (u ++ w)) t))
  | .cert j => w.getD j false

private theorem certWord_runAssignment {w : List Bool} (hw : w.length = L) :
    certWord (runAssignment tm u w) L = w := by
  subst hw
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp [certWord, runAssignment, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]

@[simp] theorem runAssignment_holds {w : List Bool} {t : ℕ} {φ : Feature k State} :
    runAssignment tm u w (.holds t φ) = true ↔ φ.Holds (tm.runFrom (tm.initCfg (u ++ w)) t) :=
  decide_eq_true_iff

variable [Fintype State]

/-- The assignment read off an accepting run satisfies the tableau. -/
theorem eval_tableau_runAssignment {w : List Bool} (hw : w.length = L)
    (hhalt : (tm.runFrom (tm.initCfg (u ++ w)) T).state = none)
    (hout : (tm.runFrom (tm.initCfg (u ++ w)) T).output = [true]) :
    (tableau tm u L T).eval (runAssignment tm u w) = true := by
  have hlen : (u ++ w).length = u.length + L := by simp [hw]
  have hb (t : ℕ) (ht : t ≤ T) (i : Fin k) :
      |(tm.runFrom (tm.initCfg (u ++ w)) t).workTapePos i| ≤ T :=
    (abs_workTapePos_runFrom_le _ t i).trans (by exact_mod_cast ht)
  refine eval_tableau.2 ⟨?_, fun t ht => ?_, fun t ht => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · refine eval_initClauses.2 ⟨?_, ?_, ?_, fun i => ⟨?_, fun z _ => ?_⟩⟩ <;>
      simp [runFrom, OutView.ofList]
  · refine (eval_oneHotClauses t).2 fun g hg => ?_
    obtain ⟨ψ, hψg, hψ⟩ := exists_holds_of_mem_groups hlen (hb t ht) hg
    refine CNF.eval_exactlyOne_map_of_iff (Var.holds_right_injective t) hψg fun φ hφ => ?_
    rw [runAssignment_holds]
    exact ⟨fun h => eq_of_holds_of_mem_groups hg hφ hψg h hψ, fun e => e ▸ hψ⟩
  · refine (eval_readClauses t).2 ⟨fun i z s _ hh hc => ?_, fun j _ hj => ?_⟩
    · rw [runAssignment_holds] at hh hc ⊢
      rw [holds_read, Cfg.workTapeSymbols, holds_head.1 hh, holds_cell.1 hc]
    · rw [certWord_runAssignment hw, runAssignment_holds, holds_inRead,
        Cfg.inputSymbol_eq_inputAt, holds_inPos.1 ((runAssignment_holds).1 hj)]
  · refine (eval_sitClauses t).2 fun y hs hi hr => ?_
    rw [runAssignment_holds] at hs hi ⊢
    exact (holds_sit_iff y).2 ⟨hs, hi, fun i => runAssignment_holds.1 (hr i)⟩
  · refine (eval_uniqueClauses t).2 ⟨fun i s s' h h' => ?_, fun s s' h h' => ?_, fun y hy => ?_⟩
    · rw [runAssignment_holds, holds_read] at h h'
      exact h.symm.trans h'
    · rw [runAssignment_holds, holds_inRead] at h h'
      exact h.symm.trans h'
    · obtain ⟨hs, hi, hr⟩ := (holds_sit_iff y).1 (runAssignment_holds.1 hy)
      exact ⟨runAssignment_holds.2 hs, runAssignment_holds.2 hi,
        fun i => runAssignment_holds.2 (hr i)⟩
  · refine (eval_stepClauses t).2 fun φ hφ c hc hall => ?_
    rw [runAssignment_holds, runFrom_succ]
    refine (holds_step_iff_exists_stepTerms tm hlen (hb t ht.le) hφ).2 ⟨c, hc, fun l hl => ?_⟩
    rw [← hall l hl, runAssignment_holds]
  · exact eval_acceptClauses.2 ⟨runAssignment_holds.2 hhalt,
      runAssignment_holds.2 (by rw [holds_out, hout]; rfl)⟩

/-- **The tableau with fixed certificate bits.** `tableau tm u z.length T` has a satisfying
assignment whose certificate is `z` exactly when `tm`, started on `u ++ z`, has halted after `T`
steps with output `[true]`. -/
theorem exists_eval_tableau_iff {z : List Bool} :
    (∃ σ, certWord σ z.length = z ∧ (tableau tm u z.length T).eval σ = true) ↔
      (tm.runFrom (tm.initCfg (u ++ z)) T).state = none ∧
        (tm.runFrom (tm.initCfg (u ++ z)) T).output = [true] := by
  constructor
  · rintro ⟨σ, hz, h⟩
    have hA := agrees_of_eval_tableau h T le_rfl
    obtain ⟨-, -, -, haccept⟩ := eval_tableau.1 h
    obtain ⟨hstate, hout⟩ := eval_acceptClauses.1 haccept
    rw [hz] at hA
    exact ⟨(hA _ (state_mem_basic _)).1 hstate,
      OutView.ofList_eq_one_iff.1 ((hA _ (out_mem_basic _)).1 hout)⟩
  · rintro ⟨hhalt, hout⟩
    exact ⟨runAssignment tm u z, certWord_runAssignment rfl,
      eval_tableau_runAssignment rfl hhalt hout⟩

/-- **The Cook–Levin tableau is correct.** `tableau tm u L T` is satisfiable exactly when some
certificate `w` of length `L` makes `tm`, started on `u ++ w`, halt within `T` steps with output
`[true]`. -/
theorem tableau_satisfiable_iff :
    (tableau tm u L T).Satisfiable ↔
      ∃ w : List Bool, w.length = L ∧ (tm.runFrom (tm.initCfg (u ++ w)) T).state = none ∧
        (tm.runFrom (tm.initCfg (u ++ w)) T).output = [true] := by
  constructor
  · rintro ⟨σ, h⟩
    have hL := length_certWord σ L
    refine ⟨certWord σ L, hL, exists_eval_tableau_iff.1 ⟨σ, ?_⟩⟩
    rw [hL]
    exact ⟨rfl, h⟩
  · rintro ⟨w, rfl, h⟩
    obtain ⟨σ, -, hσ⟩ := exists_eval_tableau_iff.2 h
    exact ⟨σ, hσ⟩

end Completeness

end Cslib.Complexity.CookLevin
