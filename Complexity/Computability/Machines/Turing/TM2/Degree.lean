/-
Copyright (c) 2026 Carlos Toledo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlos Toledo
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.Simulation
public import Complexity.Computability.Machines.Turing.TM2.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Fold

/-!
# Mathlib TM2 steps and clocked runs with machine-independent degrees

`Turing.TM2.stepTotal_polyTime` certifies one step of a fixed TM2 program in polynomial time,
but the degree of that polynomial comes out of the polynomial-time calculus and may depend on the
program. When the program is chosen after a parameter, as in a `2 ^ (δ n)` argument where the
machine depends on `δ`, a program-dependent degree is not enough. Here the step is certified in
the degree calculus (`Turing.MultiTapeTM.ComputableInDegree`) with time, space and output degree
one, for every program: composing linear-output pieces keeps the degree at one. A run of `t`
steps, with `t` given in unary, is then a left fold of degree two, again for every machine with
finite stack alphabets. The configuration encoding is `Turing.TM2.encCfg`.

## Main definitions

* `Turing.TM2.runBit`: run a Boolean `TM2ComputableAux` machine for `t` padded steps on `w` and
  read the top of its output stack.

## Main results

* `Turing.TM2.stepTotal_computableInDegree`: one TM2 step has degrees one, for every program.
* `Turing.TM2.runBit_computableInDegree`: the clocked run has time and space degree two and output
  degree one in the length of the encoded input `(w, t)`, for every machine.
* `Turing.TM2.runBit_eq`: a clock at least the running time reads the machine's answer.

## References

Uses Christian Reitwiessner's degree calculus; see the source marker in
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/Degree.lean`.
-/

@[expose] public section

namespace Turing.TM2

open MultiTapeTM

/-! ### Dependent finite tables with degree one -/

section Table

variable {α Index : Type} {Value : Index → Type} [Fintype Index]
  {input : α ↪ List Bool} {enc : ∀ i, Value i ↪ List Bool}

private theorem ofFn_computableInDegree {d : ℕ} (hd : 1 ≤ d) {count : ℕ}
    {words : α → Fin count → List Bool}
    (h : ∀ j, ComputableInDegree (fun a => words a j) input encBits d 1) :
    ComputableInDegree (fun a => List.ofFn (words a)) input (encList encBits) d 1 := by
  induction count with
  | zero =>
    simpa using (ComputableInDegree.const (encIn := input) (encMid := encList encBits)
      ([] : List (List Bool))).mono (d' := d) (e' := 1) hd (by omega)
  | succ count ih =>
    have hrest := ih (words := fun a j => words a j.succ) (fun j => h j.succ)
    have hc := (ComputableInDegree.cons encBits).comp ((h 0).prod hrest)
    exact (hc.mono (d' := d) (e' := 1) (by simp [hd]) (by simp)).of_enc_eq fun a => by
      simp only [List.ofFn_succ]; rfl

/-- Building a dependent table, entry by entry, at any degree `d ≥ 1` with linear output. -/
private theorem dpi_computableInDegree {d : ℕ} (hd : 1 ≤ d) {values : α → ∀ i, Value i}
    (h : ∀ i, ComputableInDegree (fun a => values a i) input (enc i) d 1) :
    ComputableInDegree values input (encDPi enc) d 1 := by
  have hw : ∀ j : Fin (Fintype.card Index), ComputableInDegree
      (fun a => enc ((Fintype.equivFin Index).symm j) (values a ((Fintype.equivFin Index).symm j)))
      input encBits d 1 := fun j =>
    (h ((Fintype.equivFin Index).symm j)).of_enc_eq fun _ => rfl
  exact (ofFn_computableInDegree hd hw).of_enc_eq fun _ => rfl

private theorem iterate_tail_computableInDegree {β : Type} {encB : β ↪ List Bool} (j : ℕ) :
    ComputableInDegree (List.tail^[j]) (encList encB) (encList encB) 1 1 := by
  induction j with
  | zero => exact ComputableInDegree.of_eq fun _ => rfl
  | succ j ih =>
    have h := ih.comp (ComputableInDegree.tail (enc₁ := encB))
    exact (h.mono).of_enc_eq fun l => by rw [Function.iterate_succ]

private theorem dpi_apply_computableInDegree (enc : ∀ i, Value i ↪ List Bool) (i : Index) :
    ComputableInDegree (fun values : ∀ j, Value j => values i) (encDPi enc) (enc i) 1 1 := by
  set e := Fintype.equivFin Index
  have hlist : ComputableInDegree
      (fun values : ∀ j, Value j => List.ofFn fun j => enc (e.symm j) (values (e.symm j)))
      (encDPi enc) (encList encBits) 1 1 := ComputableInDegree.of_eq fun _ => rfl
  have h := (ComputableInDegree.headD (enc₁ := encBits) ([] : List Bool)).comp
    ((iterate_tail_computableInDegree (e i).val).comp hlist)
  refine h.mono.of_enc_eq fun values => ?_
  simp only [Function.comp_apply, List.tail_iterate, encBits]
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_ofFn]
  have hx : ∀ x, x = i → enc x (values x) = enc i (values i) := by rintro x rfl; rfl
  simpa using (hx _ (by simp [e])).symm

private theorem dpi_update_computableInDegree [DecidableEq Index] {values : α → ∀ i, Value i}
    {i : Index} {value : α → Value i}
    (hvalues : ComputableInDegree values input (encDPi enc) 1 1)
    (hvalue : ComputableInDegree value input (enc i) 1 1) :
    ComputableInDegree (fun a => Function.update (values a) i (value a))
      input (encDPi enc) 1 1 := by
  apply dpi_computableInDegree le_rfl
  intro j
  by_cases h : j = i
  · subst j
    simpa using hvalue
  · exact ((dpi_apply_computableInDegree enc j).comp hvalues).mono.of_enc_eq fun a => by
      simp only [Function.comp_apply, Function.update_of_ne h]

end Table

/-! ### One statement and one step -/

section Step

variable {K : Type} [Fintype K] [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
  [Finite Λ] [Finite σ] [∀ k, Finite (Γ k)]

/-- The encoding of the stack family inside `Turing.TM2.encCfg`. -/
private noncomputable abbrev encStk : (∀ k, List (Γ k)) ↪ List Bool :=
  encDPi (fun k => encList (encFinite (Γ k)))

omit [DecidableEq K] in
private theorem cfg_mk_computableInDegree {α : Type} {input : α ↪ List Bool}
    {label : α → Option Λ} {state : α → σ} {store : α → ∀ k, List (Γ k)}
    (hl : ComputableInDegree label input (encFinite (Option Λ)) 1 1)
    (hv : ComputableInDegree state input (encFinite σ) 1 1)
    (hs : ComputableInDegree store input encStk 1 1) :
    ComputableInDegree (fun a => Cfg.mk (label a) (state a) (store a)) input encCfg 1 1 :=
  (hl.prod (hv.prod hs)).mono.of_enc_eq fun _ => rfl

omit [DecidableEq K] in
private theorem cfg_label_computableInDegree :
    ComputableInDegree (Cfg.l (Γ := Γ) (Λ := Λ) (σ := σ)) encCfg (encFinite (Option Λ)) 1 1 :=
  ((ComputableInDegree.fst _ _).comp (ComputableInDegree.of_eq
    (f := fun cfg : Cfg Γ Λ σ => (cfg.l, cfg.var, cfg.stk))
    (encMid := encPair (encFinite (Option Λ)) (encPair (encFinite σ) encStk)) fun _ => rfl)).mono

omit [DecidableEq K] in
private theorem cfg_var_computableInDegree :
    ComputableInDegree (Cfg.var (Γ := Γ) (Λ := Λ) (σ := σ)) encCfg (encFinite σ) 1 1 :=
  ((ComputableInDegree.fst _ _).comp ((ComputableInDegree.snd _ _).comp
    (ComputableInDegree.of_eq
    (f := fun cfg : Cfg Γ Λ σ => (cfg.l, cfg.var, cfg.stk))
    (encMid := encPair (encFinite (Option Λ)) (encPair (encFinite σ) encStk)) fun _ => rfl))).mono

omit [DecidableEq K] in
private theorem cfg_stk_computableInDegree :
    ComputableInDegree (Cfg.stk (Γ := Γ) (Λ := Λ) (σ := σ)) encCfg encStk 1 1 :=
  ((ComputableInDegree.snd _ _).comp ((ComputableInDegree.snd _ _).comp
    (ComputableInDegree.of_eq
    (f := fun cfg : Cfg Γ Λ σ => (cfg.l, cfg.var, cfg.stk))
    (encMid := encPair (encFinite (Option Λ)) (encPair (encFinite σ) encStk)) fun _ => rfl))).mono

omit [DecidableEq K] in
private theorem map_headD_computableInDegree {α : Type} {input : α ↪ List Bool}
    {state : α → σ} {store : α → ∀ k, List (Γ k)}
    (hv : ComputableInDegree state input (encFinite σ) 1 1)
    (hs : ComputableInDegree store input encStk 1 1)
    (k : K) (f : σ → Option (Γ k) → σ) :
    ComputableInDegree (fun a => f (state a) (store a k).head?) input (encFinite σ) 1 1 := by
  rcases isEmpty_or_nonempty (Γ k) with hΓ | ⟨⟨d⟩⟩
  · have h := (ComputableInDegree.of_finite (encIn := encFinite σ) (encMid := encFinite σ)
      (fun s => f s none)).comp hv
    refine h.mono.of_enc_eq fun a => ?_
    have : (store a k).head? = none := by
      rcases store a k with _ | ⟨x, _⟩
      · rfl
      · exact isEmptyElim x
    simp only [Function.comp_apply, this]
  · have hl := ((dpi_apply_computableInDegree (fun k => encList (encFinite (Γ k))) k).comp
      hs).mono (d' := 1) (e' := 1)
    have hE := (ComputableInDegree.isEmpty (enc₁ := encFinite (Γ k))).comp hl
    have hH := (ComputableInDegree.headD (enc₁ := encFinite (Γ k)) d).comp hl
    have h := (ComputableInDegree.of_finite (encIn := encPair (encFinite σ)
      (encPair encBool (encFinite (Γ k)))) (encMid := encFinite σ)
      (fun p : σ × Bool × Γ k => f p.1 (if p.2.1 then none else some p.2.2))).comp
      (hv.prod (hE.prod hH))
    refine h.mono.of_enc_eq fun a => ?_
    simp only [Function.comp_apply]
    rcases store a k with _ | ⟨x, l⟩ <;> rfl

private theorem stepAux_computableInDegree (q : Stmt Γ Λ σ) : ∀ {α : Type}
    {input : α ↪ List Bool} {state : α → σ} {store : α → ∀ k, List (Γ k)},
    ComputableInDegree state input (encFinite σ) 1 1 →
    ComputableInDegree store input encStk 1 1 →
    ComputableInDegree (fun a => stepAux q (state a) (store a)) input encCfg 1 1 := by
  induction q with
  | push k f q ih =>
    intro α input state store hv hs
    have hsymbol := (ComputableInDegree.of_finite (encIn := encFinite σ)
      (encMid := encFinite (Γ k)) f).comp hv
    have hstack := (dpi_apply_computableInDegree (fun k => encList (encFinite (Γ k))) k).comp hs
    have hcons := ((ComputableInDegree.cons (encFinite (Γ k))).comp
      (hsymbol.prod hstack)).mono (d' := 1) (e' := 1)
    exact ih hv (dpi_update_computableInDegree hs hcons)
  | peek k f q ih =>
    intro α input state store hv hs
    exact ih (map_headD_computableInDegree hv hs k f) hs
  | pop k f q ih =>
    intro α input state store hv hs
    have hstack := (dpi_apply_computableInDegree (fun k => encList (encFinite (Γ k))) k).comp hs
    have htail := ((ComputableInDegree.tail (enc₁ := encFinite (Γ k))).comp hstack).mono
      (d' := 1) (e' := 1)
    exact ih (map_headD_computableInDegree hv hs k f) (dpi_update_computableInDegree hs htail)
  | load f q ih =>
    intro α input state store hv hs
    exact ih (((ComputableInDegree.of_finite (encIn := encFinite σ)
      (encMid := encFinite σ) f).comp hv).mono) hs
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro α input state store hv hs
    have hc := (ComputableInDegree.of_finite (encIn := encFinite σ) (encMid := encBool)
      f).comp hv
    have h := ComputableInDegree.ite (c := fun a => f (state a))
      (f := fun a => stepAux q₁ (state a) (store a))
      (g := fun a => stepAux q₂ (state a) (store a)) hc
      (ih₁ (hv.restrict _) (hs.restrict _)) (ih₂ (hv.restrict _) (hs.restrict _))
    refine h.mono.of_enc_eq fun a => ?_
    simp only [stepAux]
    cases f (state a) <;> rfl
  | goto f =>
    intro α input state store hv hs
    exact cfg_mk_computableInDegree (((ComputableInDegree.of_finite (encIn := encFinite σ)
      (encMid := encFinite (Option Λ)) fun v => some (f v)).comp hv).mono) hv hs
  | halt =>
    intro α input state store hv hs
    exact cfg_mk_computableInDegree (ComputableInDegree.const none).mono hv hs

/-- The step, by cases over a list of labels. -/
private noncomputable def stepCases (M : Λ → Stmt Γ Λ σ) :
    List (Option Λ) → Cfg Γ Λ σ → Cfg Γ Λ σ
  | [], c => c
  | l :: Ls, c => by
    classical
    exact if c.l = l then stepTotal M c else stepCases M Ls c

omit [Fintype K] [Finite Λ] [Finite σ] [∀ k, Finite (Γ k)] in
private theorem stepCases_eq (M : Λ → Stmt Γ Λ σ) (Ls : List (Option Λ))
    (c : Cfg Γ Λ σ) (h : c.l ∈ Ls) : stepCases M Ls c = stepTotal M c := by
  induction Ls with
  | nil => simp at h
  | cons l Ls ih =>
    classical
    simp only [stepCases]
    split_ifs with hl
    · rfl
    · exact ih ((List.mem_cons.mp h).resolve_left hl)

private theorem stepCases_computableInDegree (M : Λ → Stmt Γ Λ σ) (Ls : List (Option Λ)) :
    ∀ {α : Type} {input : α ↪ List Bool} {cfg : α → Cfg Γ Λ σ},
    ComputableInDegree cfg input encCfg 1 1 →
    ComputableInDegree (fun a => stepCases M Ls (cfg a)) input encCfg 1 1 := by
  classical
  induction Ls with
  | nil => intro α input cfg hc; exact hc
  | cons l Ls ih =>
    intro α input cfg hc
    have hcond := (ComputableInDegree.of_finite (encIn := encFinite (Option Λ))
      (encMid := encBool) fun l' : Option Λ => decide (l' = l)).comp
      (cfg_label_computableInDegree.comp hc)
    have hyes : ComputableInDegree ((fun a => stepTotal M (cfg a)) ∘ Subtype.val)
        ((Function.Embedding.subtype fun a => decide ((cfg a).l = l) = true).trans input)
        encCfg 1 1 := by
      have hr := hc.restrict (fun a => decide ((cfg a).l = l) = true)
      cases l with
      | none =>
        refine hr.of_enc_eq fun a => ?_
        have h := of_decide_eq_true a.2
        simp only [Function.comp_apply, stepTotal, h, Option.elim_none]
      | some l =>
        have h := stepAux_computableInDegree (M l) (cfg_var_computableInDegree.comp hr).mono
          (cfg_stk_computableInDegree.comp hr).mono
        refine h.of_enc_eq fun a => ?_
        have h := of_decide_eq_true a.2
        simp only [Function.comp_apply, stepTotal, h, Option.elim_some]
    have hno := ih (hc.restrict (fun a => decide ((cfg a).l = l) = false))
    have h := ComputableInDegree.ite (c := fun a => decide ((cfg a).l = l))
      (f := fun a => stepTotal M (cfg a)) (g := fun a => stepCases M Ls (cfg a)) hcond hyes hno
    refine h.mono.of_enc_eq fun a => ?_
    simp only [stepCases]
    by_cases hl : (cfg a).l = l <;> simp [hl]

/-- **One TM2 step in degree one**, for every program: time, space and output length are linear
in the length of the encoded configuration, with degrees that do not depend on `M`. -/
theorem stepTotal_computableInDegree (M : Λ → Stmt Γ Λ σ) :
    ComputableInDegree (stepTotal M) encCfg encCfg 1 1 := by
  classical
  let _ := Fintype.ofFinite Λ
  have h := stepCases_computableInDegree M (Finset.univ : Finset (Option Λ)).toList
    (ComputableInDegree.of_eq (f := fun c : Cfg Γ Λ σ => c) fun _ => rfl)
  exact h.of_enc_eq fun c => by rw [stepCases_eq M _ c (by simp)]

end Step

/-! ### The clocked run -/

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-- Run `t` padded steps of `M` on `w` and read the top of the output stack: on the input
`(w, t)`, start the machine of `M` on `w` (through its input alphabet), run `t` steps of
`Turing.TM2.stepTotal`, which stays put after halting, and read the top of the output stack
through the output alphabet. -/
noncomputable def runBit (M : TM2ComputableAux Bool Bool) (x : List Bool × ℕ) : Bool :=
  M.outputAlphabet ((((List.replicate x.2 true).foldl (fun c _ => stepTotal M.tm.m c)
    (initList M.tm (x.1.map M.inputAlphabet.symm))).stk M.tm.k₁).headD
      (M.outputAlphabet.symm false))

section Run

variable (M : TM2ComputableAux Bool Bool) [hfin : ∀ k, Finite (M.tm.Γ k)]

private theorem initList_computableInDegree : ComputableInDegree
    (fun x : List Bool × ℕ => initList M.tm (x.1.map M.inputAlphabet.symm))
    (encPair (encList encBool) encUnary) encCfg 2 1 := by
  -- The input word is mapped through the input alphabet by the tidy `mapWith` rule.
  have hw : ComputableInDegree (fun x : List Bool × ℕ => x.1.map M.inputAlphabet.symm)
      (encPair (encList encBool) encUnary) (encList (encFinite (M.tm.Γ M.tm.k₀))) 2 1 := by
    have h := ComputableTidilyInDegree.mapWith (encIn := encPair (encList encBool) encUnary)
      (π := Bool) (encP := encBool) (enc := encBool) (encB := encFinite (M.tm.Γ M.tm.k₀))
      (f := fun p : Bool × Bool => M.inputAlphabet.symm p.2)
      (par := fun _ : List Bool × ℕ => false) (list := fun x => x.1)
      (ComputableTidilyInDegree.of_finite _)
      ((ComputableTidilyInDegree.const false).mono (d' := 1) (e' := 1))
      (ComputableTidilyInDegree.fst (encList encBool) encUnary)
    simp only [max_self] at h
    obtain ⟨⟨t, s, ht, hs, hc⟩, hl⟩ := h
    exact ⟨⟨t, s, ht, hs, hc.computableInTimeAndSpace⟩, hl⟩
  have hstk : ComputableInDegree
      (fun x : List Bool × ℕ => (initList M.tm (x.1.map M.inputAlphabet.symm)).stk)
      (encPair (encList encBool) encUnary) encStk 2 1 := by
    apply dpi_computableInDegree (by norm_num)
    intro k
    by_cases hk : k = M.tm.k₀
    · subst k
      exact hw.mono.of_enc_eq fun x => by simp [initList]
    · exact ((ComputableInDegree.const (encIn := encPair (encList encBool) encUnary)
        (encMid := encList (encFinite (M.tm.Γ k))) []).mono).of_enc_eq fun x => by
          simp [initList, hk]
  have h := ((ComputableInDegree.const (encIn := encPair (encList encBool) encUnary)
    (encMid := encFinite (Option M.tm.Λ)) (some M.tm.main)).prod
    ((ComputableInDegree.const (encIn := encPair (encList encBool) encUnary)
      (encMid := encFinite M.tm.σ) M.tm.initialState).prod hstk))
  exact h.mono.of_enc_eq fun _ => rfl

omit hfin in
/-- The configuration after `i` padded steps keeps every stack within `|w| + C * i`. -/
private theorem stack_le (C : ℕ)
    (hC : ∀ (cfg : Cfg M.tm.Γ M.tm.Λ M.tm.σ) (bound : ℕ), (∀ k, (cfg.stk k).length ≤ bound) →
      ∀ k, ((stepTotal M.tm.m cfg).stk k).length ≤ bound + C)
    (s : List (M.tm.Γ M.tm.k₀)) (i : ℕ) :
    ∀ k, (((stepTotal M.tm.m)^[i] (initList M.tm s)).stk k).length ≤ s.length + C * i := by
  induction i with
  | zero =>
    intro k
    by_cases hk : k = M.tm.k₀
    · subst k; simp [initList]
    · simp [initList, hk]
  | succ i ih =>
    intro k
    calc _ = ((stepTotal M.tm.m ((stepTotal M.tm.m)^[i] (initList M.tm s))).stk k).length :=
          congrArg (fun cfg : Cfg M.tm.Γ M.tm.Λ M.tm.σ => (cfg.stk k).length)
            (Function.iterate_succ_apply' (stepTotal M.tm.m) i (initList M.tm s))
      _ ≤ s.length + C * i + C := hC _ _ ih k
      _ = s.length + C * (i + 1) := by ring

/-- **The clocked run in degree two.** On `(w, t)`, with the bits of `w` framed one by one and
`t` in unary, `runBit M` has time and space degree two and output degree one, for every machine
whose stack alphabets are finite. -/
theorem runBit_computableInDegree :
    ComputableInDegree (runBit M) (encPair (encList encBool) encUnary) encBool 2 1 := by
  obtain ⟨C, hC⟩ := stepTotal_stack_bound M.tm.m
  obtain ⟨A, hA⟩ := length_encCfg_le (Γ := M.tm.Γ) (Λ := M.tm.Λ) (σ := M.tm.σ)
  have hlist : ComputableInDegree (fun x : List Bool × ℕ => List.replicate x.2 true)
      (encPair (encList encBool) encUnary) encBits 1 1 :=
    (ComputableInDegree.snd _ _).of_enc_eq fun _ => rfl
  have hstep : ComputableInDegree
      (fun p : Cfg M.tm.Γ M.tm.Λ M.tm.σ × Bool => stepTotal M.tm.m p.1)
      (encPair encCfg encBool) encCfg 1 1 :=
    ((stepTotal_computableInDegree M.tm.m).comp (ComputableInDegree.fst _ _)).mono
  have hB : DegreeBounded (fun x : List Bool × ℕ => (encPair (encList encBool) encUnary x).length)
      (fun x => A * (x.1.length + C * x.2 + 1)) 1 := by
    refine ⟨A * (C + 2), fun x => ?_⟩
    have h1 := length_le_length_encList encBool x.1
    simp only [length_encPair, encUnary_apply, List.length_replicate, pow_one]
    generalize ((encList encBool) x.1).length = L at h1 ⊢
    have h2 : x.1.length + C * x.2 + 1 ≤ (C + 2) * (2 * L + 1 + x.2 + 1) := by nlinarith
    calc A * (x.1.length + C * x.2 + 1) ≤ A * ((C + 2) * (2 * L + 1 + x.2 + 1)) :=
          Nat.mul_le_mul_left A h2
      _ = A * (C + 2) * (2 * L + 1 + x.2 + 1) := by ring
  have hfold := ComputableInDegree.foldl' (encA := encBool) (encL := encBits)
    (encB := encCfg) (list := fun x : List Bool × ℕ => List.replicate x.2 true)
    (init := fun x => initList M.tm (x.1.map M.inputAlphabet.symm))
    (step := fun c _ => stepTotal M.tm.m c) hlist (initList_computableInDegree M) hstep hB
    (fun x i hi => by
      rw [List.take_replicate]
      erw [List.foldl_const]
      rw [List.length_replicate]
      refine hA _ _ fun k => (stack_le M C hC _ _ k).trans ?_
      simp only [List.length_map, List.length_replicate] at hi ⊢
      exact Nat.add_le_add_left (Nat.mul_le_mul_left C ((Nat.min_le_left _ _).trans hi)) _)
  have hout := (ComputableInDegree.of_finite (encIn := encFinite (M.tm.Γ M.tm.k₁))
    (encMid := encBool) M.outputAlphabet).comp
    ((ComputableInDegree.headD (enc₁ := encFinite (M.tm.Γ M.tm.k₁))
      (M.outputAlphabet.symm false)).comp
    ((dpi_apply_computableInDegree (fun k => encList (encFinite (M.tm.Γ k))) M.tm.k₁).comp
      (cfg_stk_computableInDegree.comp hfold)))
  exact hout.mono.of_enc_eq fun _ => rfl

end Run

/-- **The clocked run reads the machine's answer.** If `M`, started on `w`, outputs `[b]` within
`T` steps, then `t ≥ T` padded steps read `b`. -/
theorem runBit_eq (M : TM2ComputableAux Bool Bool) {w : List Bool} {b : Bool} {T t : ℕ}
    (h : TM2OutputsInTime M.tm (w.map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) T) (hT : T ≤ t) :
    runBit M (w, t) = b := by
  have h' : TM2OutputsInTime M.tm (w.map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) t :=
    ⟨h.toEvalsTo, h.steps_le_m.trans hT⟩
  have heval := iterate_stepTotal_of_evals M.tm _ _ _ h'
  unfold runBit
  erw [List.foldl_const]
  rw [List.length_replicate]
  change M.outputAlphabet ((((stepTotal M.tm.m)^[t]
    (initList M.tm (w.map M.inputAlphabet.invFun))).stk M.tm.k₁).headD _) = b
  rw [heval]
  simp [haltList]

end Turing.TM2
