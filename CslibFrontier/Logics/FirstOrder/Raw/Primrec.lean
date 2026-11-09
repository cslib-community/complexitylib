/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.Basic
public import Mathlib.Computability.Primrec.List

/-!
# Primitive recursive operations on raw formulas

The constructors of `Cslib.Logic.FO.RawFormula` are primitive recursive for its `Denumerable`
coding, and so is every function defined by structural recursion with primitive recursive step
functions (`Cslib.Logic.FO.RawFormula.primrec₂_of_rec`, modelled on Mathlib's
`Nat.Partrec.Code.primrec_recOn'`).

## Main results

* `Cslib.Logic.FO.RawFormula.primrec_equal`, `primrec_rel`, `primrec_imp`, `primrec_all`,
  `primrec_neg`, `primrec_conj`, `primrec_ex`, `primrec_bigConj`: the constructors and derived
  connectives are primitive recursive.
* `Cslib.Logic.FO.RawFormula.primrec₂_of_rec`: structural recursion is primitive recursive.
* `Cslib.Logic.FO.RawFormula.primrec₂_rename`, `primrec_varBound`.
-/

public section

namespace Cslib.Logic.FO

namespace RawFormula

open Primrec

variable {α : Type*} [Primcodable α]

theorem primrec_equal {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => equal (f a) (g a) :=
  Primrec.encode_iff.1 <| (nat_add.comp (nat_mul.comp (const 4) (Primrec₂.natPair.comp hf hg))
    (const 1)).of_eq fun _ => rfl

theorem primrec_rel {f : α → ℕ} {g : α → List ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => rel (f a) (g a) :=
  Primrec.encode_iff.1 <| (nat_add.comp (nat_mul.comp (const 4)
    (Primrec₂.natPair.comp hf (Primrec.encode_iff.2 hg))) (const 2)).of_eq fun _ => rfl

theorem primrec_imp {f g : α → RawFormula} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => imp (f a) (g a) :=
  Primrec.encode_iff.1 <| (nat_add.comp (nat_mul.comp (const 4)
    (Primrec₂.natPair.comp (Primrec.encode_iff.2 hf) (Primrec.encode_iff.2 hg))) (const 3)).of_eq
    fun _ => rfl

theorem primrec_all {f : α → ℕ} {g : α → RawFormula} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => all (f a) (g a) :=
  Primrec.encode_iff.1 <| (nat_add.comp (nat_mul.comp (const 4)
    (Primrec₂.natPair.comp hf (Primrec.encode_iff.2 hg))) (const 4)).of_eq fun _ => rfl

theorem primrec_neg {f : α → RawFormula} (hf : Primrec f) : Primrec fun a => neg (f a) :=
  primrec_imp hf (const falsum)

theorem primrec_conj {f g : α → RawFormula} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => conj (f a) (g a) :=
  primrec_neg (primrec_imp hf (primrec_neg hg))

theorem primrec_ex {f : α → ℕ} {g : α → RawFormula} (hf : Primrec f) (hg : Primrec g) :
    Primrec fun a => ex (f a) (g a) :=
  primrec_neg (primrec_all hf (primrec_neg hg))

theorem primrec_bigConj : Primrec bigConj :=
  (list_foldr Primrec.id (const verum) (primrec_conj (fst.comp snd) (snd.comp snd)).to₂).of_eq
    fun l => (bigConj_eq_foldr l).symm

/-- **Structural recursion on raw formulas is primitive recursive.** A function `F a φ` given by
primitive recursive step functions on each constructor (the `imp` and `all` steps may use the
recursive values on the immediate subformulas) is primitive recursive. -/
theorem primrec₂_of_rec {σ : Type*} [Primcodable σ] (F : α → RawFormula → σ)
    {z : α → σ} (hz : Primrec z)
    {e : α → ℕ × ℕ → σ} (he : Primrec₂ e)
    {r : α → ℕ × List ℕ → σ} (hr : Primrec₂ r)
    {i : α → (RawFormula × RawFormula) × (σ × σ) → σ} (hi : Primrec₂ i)
    {l : α → (ℕ × RawFormula) × σ → σ} (hl : Primrec₂ l)
    (Hz : ∀ a, F a falsum = z a)
    (He : ∀ a x y, F a (equal x y) = e a (x, y))
    (Hr : ∀ a x as, F a (rel x as) = r a (x, as))
    (Hi : ∀ a φ ψ, F a (imp φ ψ) = i a ((φ, ψ), (F a φ, F a ψ)))
    (Hl : ∀ a x φ, F a (all x φ) = l a ((x, φ), F a φ)) :
    Primrec₂ F := by
  let G₁ : (α × List σ) × ℕ → Option σ := fun ((a, IH), m) =>
    let q := m / 4
    if m % 4 = 0 then some (e a q.unpair)
    else if m % 4 = 1 then some (r a (q.unpair.1, Denumerable.ofNat (List ℕ) q.unpair.2))
    else if m % 4 = 2 then
      IH[q.unpair.1]?.bind fun s₁ => IH[q.unpair.2]?.map fun s₂ =>
        i a ((ofNat q.unpair.1, ofNat q.unpair.2), (s₁, s₂))
    else IH[q.unpair.2]?.map fun s => l a ((q.unpair.1, ofNat q.unpair.2), s)
  have hq : Primrec fun p : (α × List σ) × ℕ => p.2 / 4 := nat_div.comp snd (const 4)
  have hq1 := fst.comp (Primrec.unpair.comp hq)
  have hq2 := snd.comp (Primrec.unpair.comp hq)
  have hmod : Primrec fun p : (α × List σ) × ℕ => p.2 % 4 := nat_mod.comp snd (const 4)
  have ha : Primrec fun p : (α × List σ) × ℕ => p.1.1 := fst.comp fst
  have hIH : Primrec fun p : (α × List σ) × ℕ => p.1.2 := snd.comp fst
  have hofNat : Primrec ofNat := Primrec.ofNat RawFormula
  have hG₁ : Primrec G₁ := by
    refine Primrec.ite (Primrec.eq.comp hmod (const 0))
      (option_some.comp (he.comp ha (Primrec.unpair.comp hq))) ?_
    refine Primrec.ite (Primrec.eq.comp hmod (const 1))
      (option_some.comp (hr.comp ha (Primrec.pair hq1 ((Primrec.ofNat (List ℕ)).comp hq2)))) ?_
    refine Primrec.ite (Primrec.eq.comp hmod (const 2)) ?_ ?_
    · refine option_bind (list_getElem?.comp hIH hq1) ?_
      refine option_map ((list_getElem?.comp hIH hq2).comp fst) ?_
      exact hi.comp (ha.comp (fst.comp fst))
        (Primrec.pair (Primrec.pair (hofNat.comp (hq1.comp (fst.comp fst)))
          (hofNat.comp (hq2.comp (fst.comp fst)))) (Primrec.pair (snd.comp fst) snd))
    · refine option_map (list_getElem?.comp hIH hq2) ?_
      exact hl.comp (ha.comp fst)
        (Primrec.pair (Primrec.pair (hq1.comp fst) (hofNat.comp (hq2.comp fst))) snd)
  let G : α → List σ → Option σ := fun a IH =>
    Nat.casesOn IH.length (some (z a)) fun m => G₁ ((a, IH), m)
  have hG : Primrec₂ G :=
    nat_casesOn (list_length.comp snd) (option_some.comp (hz.comp fst))
      (hG₁.comp (Primrec.pair (Primrec.pair (fst.comp fst) (snd.comp fst)) snd)).to₂
  have h := nat_strong_rec (fun a n => F a (ofNat n)) hG fun a n => by
    rcases n with _ | m
    · simp [G, Hz, ofNat_zero]
    · simp only [G, List.length_map, List.length_range, G₁]
      have h1 := unpair_fst_div_four_lt m
      have h2 := unpair_snd_div_four_lt m
      rw [ofNat_succ]
      split_ifs <;>
        simp [He, Hr, Hi, Hl, h1, h2]
  exact (h.comp fst (Primrec.encode.comp snd)).of_eq fun p => by
    simp only [encode_eq_toNat, ofNat_toNat]

theorem primrec₂_rename : Primrec₂ rename := by
  refine primrec₂_of_rec (α := List ℕ) (σ := RawFormula) rename (const falsum)
    (e := fun _ p => equal p.1 p.2) (primrec_equal (fst.comp snd) (snd.comp snd)).to₂
    (r := fun σ p => rel ((σ[p.1]?).getD p.1) p.2)
    (primrec_rel (option_getD.comp (list_getElem?.comp fst (fst.comp snd)) (fst.comp snd))
      (snd.comp snd)).to₂
    (i := fun _ p => imp p.2.1 p.2.2)
    (primrec_imp (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))).to₂
    (l := fun _ p => all p.1.1 p.2)
    (primrec_all (fst.comp (fst.comp snd)) (snd.comp snd)).to₂
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => ?_) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  simp only [rename, List.getD_eq_getElem?_getD]

theorem primrec_varBound : Primrec varBound := by
  have h := primrec₂_of_rec (α := Unit) (σ := ℕ) (fun _ φ => varBound φ) (const 0)
    (e := fun _ p => max p.1 p.2 + 1)
    (succ.comp (nat_max.comp (fst.comp snd) (snd.comp snd))).to₂
    (r := fun _ p => (p.2.map (· + 1)).foldr max 0)
    (list_foldr (list_map (snd.comp snd) (succ.comp snd).to₂) (const 0)
      (nat_max.comp (fst.comp snd) (snd.comp snd)).to₂).to₂
    (i := fun _ p => max p.2.1 p.2.2)
    (nat_max.comp (fst.comp (snd.comp snd)) (snd.comp (snd.comp snd))).to₂
    (l := fun _ p => max (p.1.1 + 1) p.2)
    (nat_max.comp (succ.comp (fst.comp (fst.comp snd))) (snd.comp snd)).to₂
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  exact h.comp (const ()) Primrec.id

end RawFormula

end Cslib.Logic.FO
