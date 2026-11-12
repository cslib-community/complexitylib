/-
Copyright (c) 2018 Mario Carneiro, 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Samuel Schlesinger
-/
module
-- upstream: candidate (Mathlib, `Mathlib/Computability/RecursiveIn.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.RecursiveInCode
public import Mathlib.Computability.Primrec.Basic

/-!
# Primitive recursive evaluator for oracle computations

This file proves that structural recursion on `Nat.RecursiveIn.Code` (`Code.primrec_recOn'`,
`Code.primrec_recOn`) and the stage-bounded oracle evaluator `Nat.RecursiveIn.Code.evaln`
(`Code.primrec_evaln`) are primitive recursive.

It adapts the strong-recursion table argument of `Mathlib/Computability/PartrecCode.lean`
(Apache 2.0, by Mario Carneiro) from `Nat.Partrec.Code` to `Nat.RecursiveIn.Code`. Relative to
that proof, `Code.primrec_recOn'` adds the `oracle` constructor at Gödel number `4` (shifting the
composite constructors to `n + 5`), and `G` carries the finite oracle prefix `σ : List ℕ` as an
extra parameter of the strong recursion so that the `oracle` branch looks up `σ[n]?`.

## Main results

* `Nat.RecursiveIn.Code.encodeCode_lt_pair`, `Nat.RecursiveIn.Code.encodeCode_lt_comp`,
  `Nat.RecursiveIn.Code.encodeCode_lt_prec`, `Nat.RecursiveIn.Code.encodeCode_lt_rfind'`: code
  encodings of immediate subcodes are strictly smaller than those of the composite code.
* `Nat.RecursiveIn.Code.primrec_recOn'`, `Nat.RecursiveIn.Code.primrec_recOn`: structural
  recursion on `Nat.RecursiveIn.Code` is primitive recursive.
* `Nat.RecursiveIn.Code.primrec_evaln`: stage-bounded oracle evaluation `Code.evaln` is primitive
  recursive in `(σ, (k, c), n)`.

## References

* Adapted from `Mathlib/Computability/PartrecCode.lean` (Apache 2.0, by Mario Carneiro).
* [S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive
  unsolvability*][KleenePost1954]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

open Encodable Denumerable
open Primrec
open Nat Nat.RecursiveIn Nat.RecursiveIn.Code

public section

namespace Nat.RecursiveIn.Code

/-- The subcodes of `Code.pair cf cg` have strictly smaller Gödel numbers than `pair cf cg`. -/
theorem encodeCode_lt_pair (cf cg : Code) :
    encodeCode cf < encodeCode (pair cf cg) ∧ encodeCode cg < encodeCode (pair cf cg) := by
  simp only [encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode) (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 5))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩

/-- The subcodes of `Code.comp cf cg` have strictly smaller Gödel numbers than `comp cf cg`. -/
theorem encodeCode_lt_comp (cf cg : Code) :
    encodeCode cf < encodeCode (comp cf cg) ∧ encodeCode cg < encodeCode (comp cf cg) := by
  have : encodeCode (pair cf cg) < encodeCode (comp cf cg) := by simp [encodeCode]
  exact (encodeCode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

/-- The subcodes of `Code.prec cf cg` have strictly smaller Gödel numbers than `prec cf cg`. -/
theorem encodeCode_lt_prec (cf cg : Code) :
    encodeCode cf < encodeCode (prec cf cg) ∧ encodeCode cg < encodeCode (prec cf cg) := by
  have : encodeCode (pair cf cg) < encodeCode (prec cf cg) := by simp [encodeCode]
  exact (encodeCode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

/-- The subcode of `Code.rfind' cf` has a strictly smaller Gödel number than `rfind' cf`. -/
theorem encodeCode_lt_rfind' (cf : Code) : encodeCode cf < encodeCode (rfind' cf) := by
  simp only [encodeCode]
  omega

/-- Structural recursion on `Nat.RecursiveIn.Code` with tupled branch functions is primitive
recursive. Adapted from `Nat.Partrec.Code.primrec_recOn'` with an additional `oracle` branch. -/
theorem primrec_recOn' {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {o : α → σ} (ho : Primrec o)
    {pr : α → Code × Code × σ × σ → σ} (hpr : Primrec₂ pr)
    {co : α → Code × Code × σ × σ → σ} (hco : Primrec₂ co) {pc : α → Code × Code × σ × σ → σ}
    (hpc : Primrec₂ pc) {rf : α → Code × σ → σ} (hrf : Primrec₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      Code.recOn c (z a) (s a) (l a) (r a) (o a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun a => F a (c a) : α → σ) := by
  intro _ _ _ _ F
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    letI p1 := p.1; letI p2 := p.2; letI a := p1.1; letI IH := p1.2; letI n := p2.1; letI m := p2.2
    IH[m]?.bind fun s =>
    IH[m.unpair.1]?.bind fun s₁ =>
    IH[m.unpair.2]?.map fun s₂ =>
    bif n.bodd then
      (bif n.div2.bodd then (rf a (ofNat Code m, s))
        else (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      else (bif n.div2.bodd then (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        else (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have : Primrec G₁ :=
    option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) <| .mk <|
    option_bind ((list_getElem?.comp (snd.comp fst)
      (fst.comp <| Primrec.unpair.comp (snd.comp snd))).comp fst) <| .mk <|
    option_map ((list_getElem?.comp (snd.comp fst)
      (snd.comp <| Primrec.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk <|
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (Primrec.unpair.comp m)
    have m₂ := snd.comp (Primrec.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    (nat_bodd.comp n).cond
      ((nat_bodd.comp <| nat_div2.comp n).cond
        (hrf.comp a (((Primrec.ofNat Code).comp m).pair s))
        (hpc.comp a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
      (Primrec.cond (nat_bodd.comp <| nat_div2.comp n)
        (hco.comp a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂))
        (hpr.comp a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    n.casesOn (some (o a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
  have : Primrec₂ G := .mk <|
    nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (ho.comp
      (fst.comp <| fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    this.comp <|
      ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst.comp fst).pair <|
      snd.pair <| nat_div2.comp <| nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
    |>.comp .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  iterate 5 rcases n with - | n; · simp [ofNatCode_eq, Code.ofNatCode]; rfl
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  change G₁ ((a, (List.range (n + 5)).map fun n => F a (ofNat Code n)), n, m) =
    some (F a (ofNat Code (n + 5)))
  have hm : m < n + 5 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
  simp only [List.length_map, List.length_range, List.getElem?_eq_getElem, hm, m1, m2,
    List.getElem_map, List.getElem_range, Option.bind_some, Option.map_some, G₁, m]
  rw [show ofNat Code (n + 5) = Code.ofNatCode (n + 5) from rfl]
  simp only [Code.ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl


/-- Structural recursion on `Nat.RecursiveIn.Code` with curried branch functions is primitive
recursive. Adapted from `Nat.Partrec.Code.primrec_recOn` with an additional `oracle` branch. -/
theorem primrec_recOn {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {o : α → σ} (ho : Primrec o)
    {pr : α → Code → Code → σ → σ → σ}
    (hpr : Primrec fun a : α × Code × Code × σ × σ =>
      let a2 := a.2; let a22 := a2.2; let a222 := a22.2; pr a.1 a2.1 a22.1 a222.1 a222.2)
    {co : α → Code → Code → σ → σ → σ}
    (hco : Primrec fun a : α × Code × Code × σ × σ =>
      let a2 := a.2; let a22 := a2.2; let a222 := a22.2; co a.1 a2.1 a22.1 a222.1 a222.2)
    {pc : α → Code → Code → σ → σ → σ}
    (hpc : Primrec fun a : α × Code × Code × σ × σ =>
      let a2 := a.2; let a22 := a2.2; let a222 := a22.2; pc a.1 a2.1 a22.1 a222.1 a222.2)
    {rf : α → Code → σ → σ} (hrf : Primrec fun a : α × Code × σ =>
      let a2 := a.2; rf a.1 a2.1 a2.2) :
    let F (a : α) (c : Code) : σ :=
      Code.recOn c (z a) (s a) (l a) (r a) (o a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  primrec_recOn' hc hz hs hl hr ho
    (pr := fun a b => let b2 := b.2; let b22 := b2.2; pr a b.1 b2.1 b22.1 b22.2) (.mk hpr)
    (co := fun a b => let b2 := b.2; let b22 := b2.2; co a b.1 b2.1 b22.1 b22.2) (.mk hco)
    (pc := fun a b => let b2 := b.2; let b22 := b2.2; pc a b.1 b2.1 b22.1 b22.2) (.mk hpc)
    (rf := fun a b => rf a b.1 b.2) (.mk hrf)

private def lup (L : List (List (Option ℕ))) (p : ℕ × Code) (n : ℕ) := do
  let l ← L[encode p]?
  let o ← l[n]?
  o

private theorem hlup : Primrec fun p : _ × (_ × _) × _ => let p2 := p.2; lup p.1 p2.1 p2.2 :=
  Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)

private noncomputable def G (σ : List ℕ) (L : List (List (Option ℕ))) : Option (List (Option ℕ)) :=
  Option.some <|
    let a := ofNat (ℕ × Code) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        Code.recOn c
          (some 0) -- zero
          (some (Nat.succ n))
          (some n.unpair.1)
          (some n.unpair.2)
          (σ[n]?) -- oracle
          (fun cf cg _ _ => do
            let x ← lup L (k, cf) n
            let y ← lup L (k, cg) n
            some (Nat.pair x y))
          (fun cf cg _ _ => do
            let x ← lup L (k, cg) n
            lup L (k, cf) x)
          (fun cf cg _ _ =>
            let z := n.unpair.1
            n.unpair.2.casesOn (lup L (k, cf) z) fun y => do
              let i ← lup L (k', c) (Nat.pair z y)
              lup L (k, cg) (Nat.pair z (Nat.pair y i)))
          (fun cf _ =>
            let z := n.unpair.1
            let m := n.unpair.2
            do
              let x ← lup L (k, cf) (Nat.pair z m)
              x.casesOn (some m) fun _ => lup L (k', c) (Nat.pair z (m + 1)))


private theorem hG : Primrec₂ G := by
  have a := (Primrec.ofNat (ℕ × Code)).comp (Primrec.list_length (α := List (Option ℕ)).comp
    (Primrec.snd (α := List ℕ) (β := List (List (Option ℕ)))))
  have k := Primrec.fst.comp a
  refine Primrec.option_some.comp (Primrec.list_map (β := ℕ) (σ := Option ℕ)
    (Primrec.list_range.comp k) (?_ : Primrec _))
  replace k := k.comp (Primrec.fst (β := ℕ))
  have n := Primrec.snd (α := List ℕ × List (List (Option ℕ))) (β := ℕ)
  refine Primrec.nat_casesOn k (_root_.Primrec.const Option.none) (?_ : Primrec _)
  have k := k.comp (Primrec.fst (β := ℕ))
  have n := n.comp (Primrec.fst (β := ℕ))
  have k' := Primrec.snd (α := (List ℕ × List (List (Option ℕ))) × ℕ) (β := ℕ)
  have c := Primrec.snd.comp (a.comp <| (Primrec.fst (β := ℕ)).comp (Primrec.fst (β := ℕ)))
  have σ_expr : Primrec (fun (p : ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) =>
    let p1 := p.1; let p11 := p1.1; p11.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have n_expr : Primrec (fun (p : ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) =>
    let p1 := p.1; p1.2) :=
    Primrec.snd.comp Primrec.fst
  have o_σ := Primrec.list_getElem?.comp σ_expr n_expr
  apply
    primrec_recOn c
      (_root_.Primrec.const (some 0))
      (Primrec.option_some.comp (_root_.Primrec.succ.comp n))
      (Primrec.option_some.comp (Primrec.fst.comp <| Primrec.unpair.comp n))
      (Primrec.option_some.comp (Primrec.snd.comp <| Primrec.unpair.comp n))
      o_σ
  · have L := (Primrec.snd.comp <| Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
    have p_k_cf := k.pair cf
    have p_k_cf_n := p_k_cf.pair n
    have p_L_arg := L.pair p_k_cf_n
    refine Primrec.option_bind (hlup.comp p_L_arg) ?_
    unfold Primrec₂
    conv =>
      congr
      · ext p
        dsimp only
        erw [Option.bind_eq_bind, ← Option.map_eq_bind]
    have p_k_cg := k.pair cg
    have p_k_cg_n := p_k_cg.pair n
    have p_L_arg2 := L.pair p_k_cg_n
    have H2 : Primrec (fun p : ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
        Code × Code × Option ℕ × Option ℕ) × ℕ => _) :=
      (hlup.comp p_L_arg2).comp
        (Primrec.fst (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
          Code × Code × Option ℕ × Option ℕ)) (β := ℕ))
    refine Primrec.option_map H2 ?_
    unfold Primrec₂
    exact Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  · have L := (Primrec.snd.comp <| Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
    have p_k_cg := k.pair cg
    have p_k_cg_n := p_k_cg.pair n
    have p_L_arg := L.pair p_k_cg_n
    refine Primrec.option_bind (hlup.comp p_L_arg) ?_
    unfold Primrec₂
    have p_k_cf := k.pair cf
    have p_k_cf_fst := p_k_cf.comp (Primrec.fst
      (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
        Code × Code × Option ℕ × Option ℕ)) (β := ℕ))
    have p_kcf_snd := p_k_cf_fst.pair (Primrec.snd
      (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
        Code × Code × Option ℕ × Option ℕ)) (β := ℕ))
    have L_fst := L.comp (Primrec.fst
      (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
        Code × Code × Option ℕ × Option ℕ)) (β := ℕ))
    have h := hlup.comp (L_fst.pair p_kcf_snd)
    exact h
  · have L := (Primrec.snd.comp <| Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    refine Primrec.nat_casesOn (Primrec.snd.comp (Primrec.unpair.comp n)) ?_ ?_
    · have p_k_cf := k.pair cf
      exact hlup.comp (L.pair (p_k_cf.pair z))
    · have L := L.comp (Primrec.fst (β := ℕ))
      have z := z.comp (Primrec.fst (β := ℕ))
      have y := Primrec.snd
        (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
          Code × Code × Option ℕ × Option ℕ))
        (β := ℕ)
      have p_kc := k'.pair c
      have p_kc_fst := p_kc.comp (Primrec.fst
        (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Code × Option ℕ × Option ℕ))
      have p_kc_fst_fst := p_kc_fst.comp (Primrec.fst
        (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
          Code × Code × Option ℕ × Option ℕ) (β := ℕ))
      have p_zy := Primrec₂.natPair.comp z y
      have p_arg2 := p_kc_fst_fst.pair p_zy
      have h₁ := hlup.comp (L.pair p_arg2)
      refine Primrec.option_bind h₁ (?_ : Primrec _)
      have z := z.comp (Primrec.fst (β := ℕ))
      have y := y.comp (Primrec.fst (β := ℕ))
      have i := Primrec.snd
        (α := (((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
          Code × Code × Option ℕ × Option ℕ) × ℕ))
        (β := ℕ)
      have p_k_cg := k.pair cg
      have p_k_cg_fst := p_k_cg.comp (Primrec.fst
        (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
          Code × Code × Option ℕ × Option ℕ)) (β := ℕ))
      have p_k_cg_fst_fst := p_k_cg_fst.comp (Primrec.fst
        (α := (((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
          Code × Code × Option ℕ × Option ℕ) × ℕ)) (β := ℕ))
      have p_yi := Primrec₂.natPair.comp y i
      have p_zyi := Primrec₂.natPair.comp z p_yi
      have p_arg2 := p_k_cg_fst_fst.pair p_zyi
      have L_fst := L.comp (Primrec.fst
        (α := (((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
          Code × Code × Option ℕ × Option ℕ) × ℕ)) (β := ℕ))
      have h₂ := hlup.comp (L_fst.pair p_arg2)
      exact h₂
  · have L := (Primrec.snd.comp <| Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ))
        (β := Code × Option ℕ))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    have m := Primrec.snd.comp (Primrec.unpair.comp n)
    have p_k_cf := k.pair cf
    have p_zm := Primrec₂.natPair.comp z m
    have p_kcf_zm := p_k_cf.pair p_zm
    have h₁ := hlup.comp (L.pair p_kcf_zm)
    refine Primrec.option_bind h₁ (?_ : Primrec _)
    have m := m.comp (Primrec.fst (β := ℕ))
    refine Primrec.nat_casesOn Primrec.snd (Primrec.option_some.comp m) ?_
    unfold Primrec₂
    have p_kc := k'.pair c
    have p_kc_fst := p_kc.comp (Primrec.fst
      (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)) (β := Code × Option ℕ))
    have p_kc_fst_fst := p_kc_fst.comp (Primrec.fst
      (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) × Code × Option ℕ)) (β := ℕ))
    have z_fst := z.comp (Primrec.fst
      (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) × Code × Option ℕ)) (β := ℕ))
    have m_succ := _root_.Primrec.succ.comp m
    have p_zm := Primrec₂.natPair.comp z_fst m_succ
    have p_arg2 := p_kc_fst_fst.pair p_zm
    have L_fst := L.comp (Primrec.fst
      (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) × Code × Option ℕ)) (β := ℕ))
    have H3 : Primrec (fun p : ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
        Code × Option ℕ) × ℕ => _) :=
      hlup.comp (L_fst.pair p_arg2)
    exact H3.comp (Primrec.fst
      (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) × Code × Option ℕ) × ℕ) (β := ℕ))

private theorem evaln_map (σ k c n) :
    ((List.range k)[n]?.bind fun a ↦ evaln σ k c a) = evaln σ k c n := by
  by_cases kn : n < k
  · simp [List.getElem?_range kn]
  · rw [List.getElem?_eq_none]
    · cases e : evaln σ k c n
      · rfl
      exact kn.elim (evaln_bound e)
    simpa using kn

/-- The `Nat.RecursiveIn.Code.evaln` function is primitive recursive. -/
theorem primrec_evaln :
    Primrec fun q : List ℕ × (ℕ × Code) × ℕ =>
      let q2 := q.2; let q21 := q2.1; evaln q.1 q21.1 q21.2 q2.2 :=
  have :
    Primrec₂ fun (σ : List ℕ) (n : ℕ) =>
      let a := ofNat (ℕ × Code) n
      (List.range a.1).map (evaln σ a.1 a.2) :=
    Primrec.nat_strong_rec (fun σ n => let a := ofNat (ℕ × Code) n;
        (List.range a.1).map (evaln σ a.1 a.2)) hG
      fun σ p => by
      simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
        Nat.pair_unpair, Option.some_inj]
      refine List.map_congr_left fun n => ?_
      have : List.range p = List.range (Nat.pair p.unpair.1 (encode (ofNat Code p.unpair.2))) := by
        simp
      rw [this]
      generalize p.unpair.1 = k
      generalize ofNat Code p.unpair.2 = c
      intro nk
      rcases k with - | k'
      · simp [evaln]
      let k := k' + 1
      simp only
      simp only [List.mem_range, Nat.lt_succ_iff] at nk
      have hg :
        ∀ {k' c' n},
          Nat.pair k' (encode c') < Nat.pair k (encode c) →
            lup ((List.range (Nat.pair k (encode c))).map fun n =>
              (List.range n.unpair.1).map (evaln σ n.unpair.1 (ofNat Code n.unpair.2))) (k', c') n =
            evaln σ k' c' n := by
        intro k₁ c₁ n₁ hl
        simp [lup, List.getElem?_range hl, evaln_map, Bind.bind, Option.bind_map]
      obtain - | - | - | - | - | ⟨cf, cg⟩ | ⟨cf, cg⟩ | ⟨cf, cg⟩ | cf := c <;>
        simp only [evaln, bind, nk, guard_true, pure, Option.bind_some, unpaired, pair_unpair]
      · obtain ⟨lf, lg⟩ := encodeCode_lt_pair cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf), hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln σ k cf n
        · rfl
        cases evaln σ k cg n <;> rfl
      · obtain ⟨lf, lg⟩ := encodeCode_lt_comp cf cg
        rw [hg (Nat.pair_lt_pair_right _ lg)]
        cases evaln σ k cg n
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lf)]
      · obtain ⟨lf, lg⟩ := encodeCode_lt_prec cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        cases n.unpair.2
        · rfl
        simp only
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
        cases evaln σ k' _ _
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lg)]
      · have lf := encodeCode_lt_rfind' cf
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        rcases evaln σ k cf n with - | x
        · rfl
        simp only [Option.bind_some]
        cases x with
        | zero => simp
        | succ _ => simpa using hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)
  (Primrec.option_bind
    (Primrec.list_getElem?.comp (this.comp Primrec.fst
      (Primrec.encode_iff.2 (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))
    Primrec.snd.to₂).of_eq
    fun ⟨σ, ⟨k, c⟩, n⟩ => by simp [evaln_map, Option.bind_map]

end Nat.RecursiveIn.Code

