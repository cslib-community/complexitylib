/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.Sentence

/-!
# Level-named raw formulas

A raw formula is **level-named** when its variables follow the convention of Mathlib's
`FirstOrder.Language.BoundedFormula`: the variable bound by the `k`-th enclosing quantifier
(counting from the outside, starting at `0`) is named `2 * k`, and a free variable `x` is named
`2 * x + 1`. `Cslib.Logic.FO.RawFormula.WellScoped F A d φ` says that `φ`, placed under `d`
quantifiers, is level-named, that its free variables satisfy `F` and that its atoms satisfy `A`;
`Cslib.Logic.FO.RawFormula.primrecRel_wellScoped` decides it primitive recursively, by computing
bottom-up the interval of depths `d` at which a formula is well scoped.

`Cslib.Logic.FO.RawFormula.levels` renames an arbitrary raw formula into a level-named one with the
same meaning (`Cslib.Logic.FO.RawFormula.realize_levels`). It is defined by structural recursion:
the body of `all x φ` is renamed first and then shifted by
`Cslib.Logic.FO.RawFormula.bindShift x`, which sends the free name of `x` to level `0` and moves
every level up by one. A sentence over `σ` is renamed into a formula that is well scoped at depth
`0` (`Cslib.Logic.FO.RawFormula.wellScoped_levels_of_isSentenceOver`).

These are the raw-syntax half of the translation between raw formulas and Mathlib's
`L.BoundedFormula` (`CslibFrontier/Logics/FirstOrder/Raw/BoundedFormula.lean`).

## Main definitions

* `Cslib.Logic.FO.RawFormula.mapVars`: renaming of variables.
* `Cslib.Logic.FO.RawFormula.NameOk`, `Cslib.Logic.FO.RawFormula.WellScoped`: level-named formulas.
* `Cslib.Logic.FO.RawFormula.bindShift`, `Cslib.Logic.FO.RawFormula.levels`: renaming into
  level-named form.

## Main results

* `Cslib.Logic.FO.RawFormula.realize_mapVars`: semantics of an injective renaming.
* `Cslib.Logic.FO.RawFormula.primrecRel_wellScoped`: being well scoped is primitive recursive.
* `Cslib.Logic.FO.RawFormula.realize_levels`, `Cslib.Logic.FO.RawFormula.finSat_levels`,
  `Cslib.Logic.FO.RawFormula.finValid_levels`: `levels` preserves meaning.
* `Cslib.Logic.FO.RawFormula.wellScoped_levels`,
  `Cslib.Logic.FO.RawFormula.wellScoped_levels_of_isSentenceOver`: `levels` produces level-named
  formulas.
* `Cslib.Logic.FO.RawFormula.primrec₂_mapVars`, `Cslib.Logic.FO.RawFormula.primrec₂_bindShift`,
  `Cslib.Logic.FO.RawFormula.primrec_levels`.
-/

public section

namespace Cslib.Logic.FO

namespace RawFormula

/-! ### Renaming variables -/

/-- Rename every variable occurrence, bound or free, by `f`. -/
@[expose]
def mapVars (f : ℕ → ℕ) : RawFormula → RawFormula
  | falsum => falsum
  | equal x y => equal (f x) (f y)
  | rel r args => rel r (args.map f)
  | imp φ ψ => imp (mapVars f φ) (mapVars f ψ)
  | all x φ => all (f x) (mapVars f φ)

theorem atoms_mapVars (f : ℕ → ℕ) : ∀ φ : RawFormula, (mapVars f φ).atoms = φ.atoms
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => by simp [mapVars, atoms]
  | imp φ ψ => by simp only [mapVars, atoms, atoms_mapVars f φ, atoms_mapVars f ψ]
  | all _ φ => by simp only [mapVars, atoms, atoms_mapVars f φ]

@[simp]
theorem quantifierDepth_mapVars (f : ℕ → ℕ) :
    ∀ φ : RawFormula, (mapVars f φ).quantifierDepth = φ.quantifierDepth
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ => by
    simp only [mapVars, quantifierDepth_imp, quantifierDepth_mapVars f φ,
      quantifierDepth_mapVars f ψ]
  | all _ φ => by simp only [mapVars, quantifierDepth_all, quantifierDepth_mapVars f φ]

/-- Renaming by an injective map: the renamed formula holds under `v` iff the formula holds under
`v ∘ f`. -/
theorem realize_mapVars {M : Type*} {I : ℕ → List M → Prop} {f : ℕ → ℕ}
    (hf : Function.Injective f) :
    ∀ (φ : RawFormula) (v : ℕ → M), (mapVars f φ).Realize I v ↔ φ.Realize I (v ∘ f)
  | falsum, _ => Iff.rfl
  | equal _ _, _ => Iff.rfl
  | rel _ _, _ => by simp [mapVars, List.map_map]
  | imp φ ψ, v => by
    simp only [mapVars, realize_imp, realize_mapVars hf φ, realize_mapVars hf ψ]
  | all x φ, v => by
    simp only [mapVars, realize_all, realize_mapVars hf φ,
      Function.update_comp_eq_of_injective _ hf]

/-! ### Level-named formulas -/

/-- The name `y` is admissible under `d` quantifiers: a level `y = 2 * i` with `i < d`, or a free
name `y = 2 * x + 1` with `F x`. -/
@[expose]
def NameOk (F : ℕ → Prop) (d y : ℕ) : Prop :=
  (y % 2 = 0 ∧ y / 2 < d) ∨ (y % 2 = 1 ∧ F (y / 2))

/-- `φ`, placed under `d` quantifiers, is **level-named**: every variable occurrence is an
admissible name (`NameOk F d`), the quantifier at depth `k` binds the level `2 * k`, and every atom
`(r, arity)` satisfies `A`. -/
@[expose]
def WellScoped (F : ℕ → Prop) (A : ℕ → ℕ → Prop) : ℕ → RawFormula → Prop
  | _, falsum => True
  | d, equal x y => NameOk F d x ∧ NameOk F d y
  | d, rel r args => A r args.length ∧ ∀ y ∈ args, NameOk F d y
  | d, imp φ ψ => WellScoped F A d φ ∧ WellScoped F A d ψ
  | d, all x φ => x = 2 * d ∧ WellScoped F A (d + 1) φ

theorem NameOk.mono {F G : ℕ → Prop} (h : ∀ x, F x → G x) {d y : ℕ} (hy : NameOk F d y) :
    NameOk G d y :=
  hy.imp id fun h' => ⟨h'.1, h _ h'.2⟩

theorem WellScoped.mono {F G : ℕ → Prop} {A B : ℕ → ℕ → Prop} (hF : ∀ x, F x → G x)
    (hA : ∀ r k, A r k → B r k) : ∀ {d : ℕ} {φ : RawFormula}, WellScoped F A d φ →
      WellScoped G B d φ
  | _, falsum, _ => trivial
  | _, equal _ _, h => ⟨h.1.mono hF, h.2.mono hF⟩
  | _, rel _ _, h => ⟨hA _ _ h.1, fun y hy => (h.2 y hy).mono hF⟩
  | _, imp _ _, h => ⟨h.1.mono hF hA, h.2.mono hF hA⟩
  | _, all _ _, h => ⟨h.1, h.2.mono hF hA⟩

/-! ### Deciding well-scopedness -/

/-! The set of depths `d` at which a formula is well scoped is an interval: a ray `[lo, ∞)` or a
segment `[lo, hi]` (possibly empty). It is computed bottom-up: atoms give rays, `imp` intersects,
and `all x` keeps at most the single depth `x / 2`. -/

/-- `d` lies in the depth interval `p`: `p.1 ≤ d`, and `d ≤ hi` when `p.2 = some hi`. -/
private def InDepths (d : ℕ) (p : ℕ × Option ℕ) : Prop :=
  p.1 ≤ d ∧ d ≤ p.2.getD d

private instance (d : ℕ) (p : ℕ × Option ℕ) : Decidable (InDepths d p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Intersection of depth intervals. -/
private def inter (p q : ℕ × Option ℕ) : ℕ × Option ℕ :=
  (max p.1 q.1, Option.merge min p.2 q.2)

private theorem inDepths_inter {d : ℕ} {p q : ℕ × Option ℕ} :
    InDepths d (inter p q) ↔ InDepths d p ∧ InDepths d q := by
  obtain ⟨a, _ | b⟩ := p <;> obtain ⟨c, _ | e⟩ := q <;>
    simp only [InDepths, inter, Option.merge, Option.getD_none, Option.getD_some] <;> omega

/-- The depth interval at which the name `y` is admissible. -/
private def nameDepths (F : ℕ → Prop) [DecidablePred F] (y : ℕ) : ℕ × Option ℕ :=
  if y % 2 = 0 then (y / 2 + 1, none) else if F (y / 2) then (0, none) else (1, some 0)

private theorem inDepths_nameDepths {F : ℕ → Prop} [DecidablePred F] {d y : ℕ} :
    InDepths d (nameDepths F y) ↔ NameOk F d y := by
  unfold nameDepths NameOk
  split_ifs with h1 h2
  · simp only [InDepths, Option.getD_none]
    constructor
    · intro h; exact Or.inl ⟨h1, by omega⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega
  · simp only [InDepths, Option.getD_none]
    constructor
    · intro _; exact Or.inr ⟨by omega, h2⟩
    · intro _; omega
  · simp only [InDepths, Option.getD_some]
    constructor
    · intro h; omega
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · omega
      · exact absurd h h2

/-- The depth interval at which all names in a list are admissible. -/
private def listDepths (F : ℕ → Prop) [DecidablePred F] (ys : List ℕ) : ℕ × Option ℕ :=
  ys.foldr (fun y p => inter (nameDepths F y) p) (0, none)

private theorem inDepths_listDepths {F : ℕ → Prop} [DecidablePred F] {d : ℕ} :
    ∀ ys : List ℕ, InDepths d (listDepths F ys) ↔ ∀ y ∈ ys, NameOk F d y
  | [] => by simp [listDepths, InDepths]
  | y :: ys => by
    rw [listDepths, List.foldr_cons, inDepths_inter, inDepths_nameDepths, ← listDepths,
      inDepths_listDepths ys, List.forall_mem_cons]

/-- The depth interval at which `all x φ` is well scoped, from the interval `p` of `φ`. -/
private def allDepths (x : ℕ) (p : ℕ × Option ℕ) : ℕ × Option ℕ :=
  if x % 2 = 0 ∧ InDepths (x / 2 + 1) p then (x / 2, some (x / 2)) else (1, some 0)

private theorem inDepths_allDepths {d x : ℕ} {p : ℕ × Option ℕ} :
    InDepths d (allDepths x p) ↔ x = 2 * d ∧ InDepths (d + 1) p := by
  unfold allDepths
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have e : InDepths d (x / 2, some (x / 2)) ↔ d = x / 2 := by
      simp only [InDepths, Option.getD_some]; omega
    rw [e]
    constructor
    · rintro rfl
      exact ⟨by omega, h2⟩
    · rintro ⟨rfl, -⟩
      omega
  · have e : ¬InDepths d (1, some 0) := by simp only [InDepths, Option.getD_some]; omega
    simp only [e, false_iff]
    rintro ⟨rfl, hp⟩
    have h2 : 2 * d / 2 = d := by omega
    exact h ⟨by omega, by rw [h2]; exact hp⟩

/-- The depth interval at which a formula is well scoped. -/
private def depths (F : ℕ → Prop) [DecidablePred F] (A : ℕ → ℕ → Prop) [DecidableRel A] :
    RawFormula → ℕ × Option ℕ
  | falsum => (0, none)
  | equal x y => listDepths F [x, y]
  | rel r args => if A r args.length then listDepths F args else (1, some 0)
  | imp φ ψ => inter (depths F A φ) (depths F A ψ)
  | all x φ => allDepths x (depths F A φ)

private theorem inDepths_depths {F : ℕ → Prop} [DecidablePred F] {A : ℕ → ℕ → Prop}
    [DecidableRel A] : ∀ (φ : RawFormula) (d : ℕ), InDepths d (depths F A φ) ↔ WellScoped F A d φ
  | falsum, d => by simp [depths, InDepths, WellScoped]
  | equal x y, d => by
    simp [depths, WellScoped, inDepths_listDepths]
  | rel r args, d => by
    unfold depths WellScoped
    split_ifs with h
    · rw [inDepths_listDepths]; simp [h]
    · simp only [InDepths, Option.getD_some, h, false_and, iff_false]; omega
  | imp φ ψ, d => by
    rw [depths, WellScoped, inDepths_inter, inDepths_depths φ, inDepths_depths ψ]
  | all x φ, d => by
    rw [depths, WellScoped, inDepths_allDepths, inDepths_depths φ]

section Primrec

open Primrec

private theorem primrec₂_inter : Primrec₂ inter :=
  Primrec.pair (nat_max.comp (fst.comp fst) (fst.comp snd))
    ((option_casesOn (snd.comp fst) (snd.comp snd)
      (option_casesOn (snd.comp (snd.comp fst)) (option_some.comp snd)
        (option_some.comp (nat_min.comp (snd.comp fst) snd)).to₂).to₂).of_eq fun p => by
      obtain ⟨⟨a, _ | b⟩, ⟨c, _ | e⟩⟩ := p <;> rfl)

private theorem primrecRel_inDepths : PrimrecRel InDepths :=
  PrimrecPred.and (nat_le.comp (fst.comp snd) fst)
    (nat_le.comp fst (option_getD.comp (snd.comp snd) fst))

private theorem primrec_nameDepths {F : ℕ → Prop} [DecidablePred F] (hF : PrimrecPred F) :
    Primrec (nameDepths F) :=
  Primrec.ite (Primrec.eq.comp (nat_mod.comp Primrec.id (const 2)) (const 0))
    (Primrec.pair (succ.comp (nat_div.comp Primrec.id (const 2))) (const none))
    (Primrec.ite (hF.comp (nat_div.comp Primrec.id (const 2))) (const (0, none))
      (const (1, some 0)))

private theorem primrec_listDepths {F : ℕ → Prop} [DecidablePred F] (hF : PrimrecPred F) :
    Primrec (listDepths F) :=
  list_foldr Primrec.id (const (0, none))
    (primrec₂_inter.comp ((primrec_nameDepths hF).comp (fst.comp snd)) (snd.comp snd)).to₂

private theorem primrec_depths {F : ℕ → Prop} [DecidablePred F] {A : ℕ → ℕ → Prop}
    [DecidableRel A] (hF : PrimrecPred F) (hA : PrimrecRel A) : Primrec (depths F A) := by
  have hL := primrec_listDepths hF
  have h := primrec₂_of_rec (α := Unit) (σ := ℕ × Option ℕ) (fun _ φ => depths F A φ)
    (const (0, none))
    (e := fun _ p => listDepths F [p.1, p.2])
    (hL.comp (list_cons.comp (fst.comp snd) (list_cons.comp (snd.comp snd) (const [])))).to₂
    (r := fun _ p => if A p.1 p.2.length then listDepths F p.2 else (1, some 0))
    (Primrec.ite (hA.comp (fst.comp snd) (list_length.comp (snd.comp snd)))
      (hL.comp (snd.comp snd)) (const (1, some 0))).to₂
    (i := fun _ p => inter p.2.1 p.2.2)
    (primrec₂_inter.comp (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))).to₂
    (l := fun _ p => allDepths p.1.1 p.2)
    (Primrec.ite
      (PrimrecPred.and (Primrec.eq.comp (nat_mod.comp (fst.comp (fst.comp snd)) (const 2))
        (const 0))
        (primrecRel_inDepths.comp (succ.comp (nat_div.comp (fst.comp (fst.comp snd)) (const 2)))
          (snd.comp snd)))
      (Primrec.pair (nat_div.comp (fst.comp (fst.comp snd)) (const 2))
        (option_some.comp (nat_div.comp (fst.comp (fst.comp snd)) (const 2))))
      (const (1, some 0))).to₂
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  exact h.comp (const ()) Primrec.id

/-- **Being well scoped is primitive recursive**, for primitive recursive `F` and `A`. -/
theorem primrecRel_wellScoped {F : ℕ → Prop} {A : ℕ → ℕ → Prop} (hF : PrimrecPred F)
    (hA : PrimrecRel A) : PrimrecRel (WellScoped F A) := by
  classical
  exact (primrecRel_inDepths.comp fst ((primrec_depths hF hA).comp snd)).of_eq fun p =>
    inDepths_depths p.2 p.1

end Primrec

/-! ### Renaming into level-named form -/

/-- The renaming applied when the free variable `x` becomes bound by a new outermost quantifier:
its free name `2 * x + 1` becomes the level `0`, every level `2 * i` becomes `2 * (i + 1)`, and
the other free names are unchanged. -/
@[expose]
def bindShift (x y : ℕ) : ℕ :=
  if y = 2 * x + 1 then 0 else if y % 2 = 0 then y + 2 else y

theorem bindShift_injective (x : ℕ) : Function.Injective (bindShift x) := by
  intro a b h
  simp only [bindShift] at h
  split_ifs at h <;> omega

/-- Rename the variables of a formula into level-named form: a free variable `x` becomes
`2 * x + 1`, and `all x φ` becomes `all 0 φ'`, where `φ'` is the renamed body shifted by
`bindShift x`. -/
@[expose]
def levels : RawFormula → RawFormula
  | falsum => falsum
  | equal x y => equal (2 * x + 1) (2 * y + 1)
  | rel r args => rel r (args.map fun x => 2 * x + 1)
  | imp φ ψ => imp (levels φ) (levels ψ)
  | all x φ => all 0 (mapVars (bindShift x) (levels φ))

theorem atoms_levels : ∀ φ : RawFormula, (levels φ).atoms = φ.atoms
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => by simp [levels, atoms]
  | imp φ ψ => by simp only [levels, atoms, atoms_levels φ, atoms_levels ψ]
  | all _ φ => by simp only [levels, atoms, atoms_mapVars, atoms_levels φ]

@[simp]
theorem quantifierDepth_levels : ∀ φ : RawFormula, (levels φ).quantifierDepth = φ.quantifierDepth
  | falsum => rfl
  | equal _ _ => rfl
  | rel _ _ => rfl
  | imp φ ψ => by
    simp only [levels, quantifierDepth_imp, quantifierDepth_levels φ, quantifierDepth_levels ψ]
  | all _ φ => by
    simp only [levels, quantifierDepth_all, quantifierDepth_mapVars, quantifierDepth_levels φ]

/-- `levels φ` holds under `ρ` iff `φ` holds under `x ↦ ρ (2 * x + 1)`. -/
theorem realize_levels {M : Type*} {I : ℕ → List M → Prop} :
    ∀ (φ : RawFormula) (ρ : ℕ → M), (levels φ).Realize I ρ ↔ φ.Realize I (fun x => ρ (2 * x + 1))
  | falsum, _ => Iff.rfl
  | equal _ _, _ => Iff.rfl
  | rel _ _, _ => by simp [levels, List.map_map, Function.comp_def]
  | imp φ ψ, ρ => by simp only [levels, realize_imp, realize_levels φ, realize_levels ψ]
  | all x φ, ρ => by
    simp only [levels, realize_all, realize_mapVars (bindShift_injective x), realize_levels φ]
    refine forall_congr' fun m => ?_
    congr! 1
    funext y
    by_cases hy : y = x
    · subst hy; simp [bindShift]
    · have h1 : bindShift x (2 * y + 1) = 2 * y + 1 := by
        simp only [bindShift]; split_ifs <;> omega
      simp only [Function.comp_apply, h1, Function.update_of_ne hy,
        Function.update_of_ne (show 2 * y + 1 ≠ 0 by omega)]

theorem finSat_levels (φ : RawFormula) : FinSat (levels φ) ↔ FinSat φ := by
  constructor
  · rintro ⟨M, hf, hn, I, ρ, h⟩
    exact ⟨M, hf, hn, I, _, (realize_levels φ ρ).1 h⟩
  · rintro ⟨M, hf, hn, I, v, h⟩
    refine ⟨M, hf, hn, I, fun y => v (y / 2), (realize_levels φ _).2 ?_⟩
    simpa [show ∀ x : ℕ, (2 * x + 1) / 2 = x by omega] using h

theorem finValid_levels (φ : RawFormula) : FinValid (levels φ) ↔ FinValid φ := by
  constructor
  · intro h M _ _ I v
    have := (realize_levels φ (fun y => v (y / 2))).1 (h M I _)
    simpa [show ∀ x : ℕ, (2 * x + 1) / 2 = x by omega] using this
  · intro h M _ _ I ρ
    exact (realize_levels φ ρ).2 (h M I _)

private theorem nameOk_bindShift {F : ℕ → Prop} {x d y : ℕ}
    (hy : NameOk F d y) : NameOk (fun z => F z ∧ z ≠ x) (d + 1) (bindShift x y) := by
  unfold NameOk at hy ⊢
  unfold bindShift
  split_ifs with h1 h2
  · omega
  · omega
  · rcases hy with hy | hy
    · omega
    · exact Or.inr ⟨hy.1, hy.2, by omega⟩

private theorem nameOk_bindShift_self {F : ℕ → Prop} {x d : ℕ} :
    NameOk F (d + 1) (bindShift x (2 * x + 1)) := by
  simp [NameOk, bindShift]

/-- Shifting a formula that is well scoped at depth `d`, whose free variables satisfy `F` or are
`x`, gives a formula well scoped at depth `d + 1` whose free variables satisfy `F` and differ from
`x`. -/
private theorem wellScoped_mapVars_bindShift {F : ℕ → Prop} {A : ℕ → ℕ → Prop} {x : ℕ} :
    ∀ {d : ℕ} {φ : RawFormula}, WellScoped (fun z => F z ∨ z = x) A d φ →
      WellScoped (fun z => F z ∧ z ≠ x) A (d + 1) (mapVars (bindShift x) φ)
  | _, falsum, _ => trivial
  | d, equal y z, h => ⟨nameOk_bindShift' h.1, nameOk_bindShift' h.2⟩
  | d, rel r args, h => ⟨by simpa using h.1, by
      simp only [List.mem_map]
      rintro _ ⟨y, hy, rfl⟩
      exact nameOk_bindShift' (h.2 y hy)⟩
  | d, imp φ ψ, h => ⟨wellScoped_mapVars_bindShift h.1, wellScoped_mapVars_bindShift h.2⟩
  | d, all y φ, h => ⟨by rw [h.1]; simp only [bindShift]; split_ifs <;> omega,
      wellScoped_mapVars_bindShift h.2⟩
where
  nameOk_bindShift' {d y : ℕ} (hy : NameOk (fun z => F z ∨ z = x) d y) :
      NameOk (fun z => F z ∧ z ≠ x) (d + 1) (bindShift x y) := by
    by_cases hyx : y = 2 * x + 1
    · subst hyx; exact nameOk_bindShift_self
    · have hy' : NameOk (fun z => F z) d y := by
        rcases hy with hy | ⟨h1, h2 | h2⟩
        · exact Or.inl hy
        · exact Or.inr ⟨h1, h2⟩
        · exact absurd (by omega : y = 2 * x + 1) hyx
      exact nameOk_bindShift hy'

/-- `levels φ` is level-named at depth `0`, with free variables among those of `φ` and the same
atoms. -/
theorem wellScoped_levels :
    ∀ φ : RawFormula, WellScoped (· ∈ φ.freeVars) (fun r k => (r, k) ∈ φ.atoms) 0 (levels φ)
  | falsum => trivial
  | equal x y => by
    refine ⟨Or.inr ⟨by omega, ?_⟩, Or.inr ⟨by omega, ?_⟩⟩ <;> simp [freeVars] <;> omega
  | rel r args => by
    refine ⟨by simp [atoms], ?_⟩
    simp only [List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    exact Or.inr ⟨by omega, by simpa [freeVars, show (2 * x + 1) / 2 = x by omega] using hx⟩
  | imp φ ψ => ⟨(wellScoped_levels φ).mono (fun _ h => by simp [freeVars, h])
      (fun _ _ h => by simp [atoms, h]),
    (wellScoped_levels ψ).mono (fun _ h => by simp [freeVars, h])
      (fun _ _ h => by simp [atoms, h])⟩
  | all x φ => by
    refine ⟨rfl, ?_⟩
    have h := wellScoped_mapVars_bindShift (F := fun z => z ∈ φ.freeVars ∧ z ≠ x) (x := x)
      ((wellScoped_levels φ).mono (fun z hz => by by_cases hzx : z = x <;> simp [hz, hzx])
        fun _ _ h => h)
    exact h.mono (fun z hz => mem_freeVars_all.2 hz.1) fun _ _ h => h

/-- `levels` renames a sentence over `σ` into a formula that is level-named at depth `0`, without
free names and with atoms in `σ`. -/
theorem wellScoped_levels_of_isSentenceOver {σ : Set (ℕ × ℕ)} {φ : RawFormula}
    (h : IsSentenceOver σ φ) : WellScoped (fun _ => False) (fun r k => (r, k) ∈ σ) 0 (levels φ) :=
  (wellScoped_levels φ).mono (fun x hx => by rw [h.1] at hx; simp at hx)
    fun r k hrk => h.2 _ hrk

section Primrec

open Primrec

theorem primrec₂_mapVars {α : Type*} [Primcodable α] {f : α → ℕ → ℕ} (hf : Primrec₂ f) :
    Primrec₂ fun a φ => mapVars (f a) φ :=
  primrec₂_of_rec (fun a φ => mapVars (f a) φ) (const falsum)
    (e := fun a p => equal (f a p.1) (f a p.2))
    (primrec_equal (hf.comp fst (fst.comp snd)) (hf.comp fst (snd.comp snd))).to₂
    (r := fun a p => rel p.1 (p.2.map (f a)))
    (primrec_rel (fst.comp snd) (list_map (snd.comp snd) (hf.comp (fst.comp fst) snd).to₂)).to₂
    (i := fun _ p => imp p.2.1 p.2.2)
    (primrec_imp (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))).to₂
    (l := fun a p => all (f a p.1.1) p.2)
    (primrec_all (hf.comp fst (fst.comp (fst.comp snd))) (snd.comp snd)).to₂
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

theorem primrec₂_bindShift : Primrec₂ bindShift :=
  Primrec.ite (Primrec.eq.comp snd (succ.comp (nat_mul.comp (const 2) fst))) (const 0)
    (Primrec.ite (Primrec.eq.comp (nat_mod.comp snd (const 2)) (const 0))
      (nat_add.comp snd (const 2)) snd)

theorem primrec_levels : Primrec levels := by
  have h := primrec₂_of_rec (α := Unit) (σ := RawFormula) (fun _ φ => levels φ) (const falsum)
    (e := fun _ p => equal (2 * p.1 + 1) (2 * p.2 + 1))
    (primrec_equal (nat_double_succ.comp (fst.comp snd)) (nat_double_succ.comp (snd.comp snd))).to₂
    (r := fun _ p => rel p.1 (p.2.map fun x => 2 * x + 1))
    (primrec_rel (fst.comp snd) (list_map (snd.comp snd) (nat_double_succ.comp snd).to₂)).to₂
    (i := fun _ p => imp p.2.1 p.2.2)
    (primrec_imp (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))).to₂
    (l := fun _ p => all 0 (mapVars (bindShift p.1.1) p.2))
    (primrec_all (const 0) ((primrec₂_mapVars primrec₂_bindShift).comp (fst.comp (fst.comp snd))
      (snd.comp snd))).to₂
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  exact h.comp (const ()) Primrec.id

end Primrec

end RawFormula

end Cslib.Logic.FO
