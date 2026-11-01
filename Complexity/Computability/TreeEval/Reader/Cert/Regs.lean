/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Cert.Residue
public import Complexity.Computability.TreeEval.Reader.Encode
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.ZipFold

/-!
# Register operations within linear work space

The register operations of `Cslib.TreeEval.Reader` are computable within work space linear
in the lengths of their encoded arguments.

## Main results

* `Cslib.TreeEval.Reader.get_inSpace`, `.set_inSpace`: selecting and replacing a register.
* `Cslib.TreeEval.Reader.scale_inSpace`: multiplying a register by a residue.
* `Cslib.TreeEval.Reader.subtractSums_inSpace`: subtracting a multiple of the sums of a pass.
-/

@[expose] public section

namespace Cslib.TreeEval

namespace Reader

open Turing MultiTapeTM ComputableInSpace

/-- The encoding of register indices. -/
abbrev encReg : Fin 3 ↪ List Bool := encFinEnum (Fin 3)

variable {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ}

/-- **Selecting a register**, given the registers and the index within a budget. -/
theorem get_inSpace {R : α → Regs} {t : α → Fin 3}
    (hR : ComputableInSpace R encIn encRegs Bs)
    (ht : ComputableInSpace t encIn encReg Bs) :
    ComputableInSpace (fun x => (R x).get (t x)) encIn (encList encNat) Bs := by
  have h₀ := fst' hR
  have h₁ := fst' (snd' hR)
  have h₂ := snd' (snd' hR)
  have hz := budget_finite (encC := encBool) (fun r : Fin 3 => decide (r = 0)) ht
  have ho := budget_finite (encC := encBool) (fun r : Fin 3 => decide (r = 1)) ht
  refine (budget_ite hz h₀ (budget_ite ho h₁ h₂)).of_enc_eq fun x => ?_
  congr 1
  generalize t x = r
  fin_cases r <;> rfl

/-- **Replacing a register.** -/
theorem set_inSpace {R : α → Regs} {t : α → Fin 3} {l : α → List ℕ}
    (hR : ComputableInSpace R encIn encRegs Bs)
    (ht : ComputableInSpace t encIn encReg Bs)
    (hl : ComputableInSpace l encIn (encList encNat) Bs) :
    ComputableInSpace (fun x => (R x).set (t x) (l x)) encIn encRegs Bs := by
  have h₀ := fst' hR
  have h₁ := fst' (snd' hR)
  have h₂ := snd' (snd' hR)
  have hz := budget_finite (encC := encBool) (fun r : Fin 3 => decide (r = 0)) ht
  have ho := budget_finite (encC := encBool) (fun r : Fin 3 => decide (r = 1)) ht
  refine (budget_ite hz (budget_prod hl (budget_prod h₁ h₂))
    (budget_ite ho (budget_prod h₀ (budget_prod hl h₂))
      (budget_prod h₀ (budget_prod h₁ hl)))).of_enc_eq fun x => ?_
  congr 1
  generalize t x = r
  fin_cases r <;> rfl

private theorem length_mulMod_le (p a v : ℕ) :
    (encNat (mulMod p a v)).length ≤ (encNat p).length + (encNat a).length + (encNat v).length :=
  (length_encNat_mono (Nat.mod_le _ _)).trans
    ((length_encNat_mul_le a v).trans (by omega))

private theorem length_encList_map_mulMod_le (p a : ℕ) (l : List ℕ) :
    (encList encNat (l.map (mulMod p a))).length ≤
      (encList encNat l).length + l.length * (2 * ((encNat p).length + (encNat a).length)) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    have := length_mulMod_le p a v
    simp only [List.map_cons, length_encList, List.sum_cons, List.length_cons] at ih this ⊢
    nlinarith

/-- **Multiplying a register by a residue**, within a budget that covers the register with every
entry as long as the prime and the factor together. -/
theorem scale_inSpace {p a : α → ℕ} {R : α → Regs} {r : α → Fin 3}
    (hp : ComputableInSpace p encIn encNat Bs)
    (ha : ComputableInSpace a encIn encNat Bs)
    (hR : ComputableInSpace R encIn encRegs Bs)
    (hr : ComputableInSpace r encIn encReg Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs)
    (hB : (fun x => ((R x).get (r x)).length * ((encNat (p x)).length + (encNat (a x)).length))
      ≼ Bs) :
    ComputableInSpace (fun x => (R x).scale (p x) (r x) (a x)) encIn encRegs Bs := by
  have hl := get_inSpace hR hr
  have hpa := budget_prod hp ha
  have hf : ComputableInSpace (fun q : (ℕ × ℕ) × ℕ => mulMod q.1.1 q.1.2 q.2)
      (encPair (encPair encNat encNat) encNat) encNat
      fun q => (encPair (encPair encNat encNat) encNat q).length + 1 := by
    have hl₀ : (fun q => (encPair (encPair encNat encNat) encNat q).length) ≼
        fun q => (encPair (encPair encNat encNat) encNat q).length + 1 := .of_le fun _ => by omega
    have h₁ := (fst (encPair encNat encNat) encNat).weaken hl₀
    have h₂ := (snd (encPair encNat encNat) encNat).weaken hl₀
    exact budget_comp_linear mulMod_inSpace (budget_prod (fst' h₁) (budget_prod (snd' h₁) h₂))
  have hmap := mapWith hf hpa hl
  have hmap' : ComputableInSpace (fun x => ((R x).get (r x)).map (mulMod (p x) (a x)))
      encIn (encList encNat) Bs := by
    refine hmap.weaken ?_
    have hlen := length_le hl
    have hplen := length_le hpa
    refine (((((hin.add (.refl _)).add (.refl _)).add hplen).add hlen).add ?_).add ?_
    · obtain ⟨c₁, hc₁⟩ := hlen
      obtain ⟨c₂, hc₂⟩ := hB
      refine ⟨c₁ + 2 * c₂, fun x => ?_⟩
      have := length_encList_map_mulMod_le (p x) (a x) ((R x).get (r x))
      have h₁ := hc₁ x
      have h₂ := hc₂ x
      dsimp only at h₁ h₂ ⊢
      nlinarith
    · obtain ⟨c₁, hc₁⟩ := hplen
      obtain ⟨c₂, hc₂⟩ := hlen
      refine ⟨2 * c₁ + c₂ + 2, fun x => listMax_le fun v hv => ?_⟩
      have h₁ := hc₁ x
      have h₂ := hc₂ x
      have hv' := length_le_encList_of_mem encNat hv
      dsimp only at h₁ h₂ ⊢
      rw [length_encPair] at ⊢
      have : (encNat v).length ≤ c₂ * (Bs x + 1) := hv'.trans h₂
      nlinarith
  exact set_inSpace hR hr hmap'

/-- **Changing one entry by adding a residue**, `modifyAt l i (addMod p c)`. -/
theorem modifyAt_inSpace {l : α → List ℕ} {i p c : α → ℕ}
    (hl : ComputableInSpace l encIn (encList encNat) Bs)
    (hi : ComputableInSpace i encIn encNat Bs)
    (hp : ComputableInSpace p encIn encNat Bs)
    (hc : ComputableInSpace c encIn encNat Bs) :
    ComputableInSpace (fun x => modifyAt (l x) (i x) (addMod (p x) (c x))) encIn
      (encList encNat) Bs := by
  have hv := budget_comp_lin getD (linear_mul _) (budget_prod hl hi)
  have hv' := budget_comp_linear addMod_inSpace (budget_prod hp (budget_prod hc hv))
  refine (budget_comp set (budget_prod hl (budget_prod hi hv')) ?_).of_enc_eq fun x => rfl
  obtain ⟨c₁, h₁⟩ := length_le (budget_prod hl hi)
  obtain ⟨c₂, h₂⟩ := length_le hv'
  refine ⟨256 * (c₁ + c₂ + 1), fun x => ?_⟩
  have := h₁ x
  have := h₂ x
  dsimp only at *
  simp only [length_encPair] at *
  nlinarith

/-- A coordinate of subtracting `c` times a sum `a` from a register, with parameters `(p, c)`. -/
private def subElem (q : ℕ × ℕ) (v : ℕ) (a : Option ℕ) : ℕ :=
  addMod q.1 v (negMod q.1 (mulMod q.1 q.2 (a.getD 0)))

private theorem subtractSums_eq (p c : ℕ) (t : Fin 3) (acc : List ℕ) (R : Regs) :
    subtractSums p c t acc R = R.set t
      (zipFold (fun q v a => some (subElem q v a)) (p, c) (R.get t) acc) := by
  rw [subtractSums, zipFold_some]
  congr 1
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  have hi : i < (R.get t).length := by simpa using h₁
  simp [List.getElem_mapIdx, List.getD_eq_getElem?_getD, hi, subElem]

/-- The encoding of the arguments of `subElem`. -/
private abbrev encSubArg : (ℕ × ℕ) × ℕ × Option ℕ ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair encNat (encOption encNat))

/-- The encoding of the parameters, the register and the sums. -/
private abbrev encSubInput : (ℕ × ℕ) × List ℕ × List ℕ ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair (encList encNat) (encList encNat))

private theorem length_subElem_le (p c v a : ℕ) :
    (encNat (addMod p v (negMod p (mulMod p c a)))).length ≤ (encNat p).length + (encNat v).length
    := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [addMod, negMod]
  · have := length_encNat_mono (Nat.mod_lt (v + negMod p (mulMod p c a)) hp).le
    simp only [addMod]; omega

private theorem subElem_inSpace :
    ComputableInSpace (fun q : (ℕ × ℕ) × ℕ × Option ℕ => some (subElem q.1 q.2.1 q.2.2)) encSubArg
      (encOption encNat) fun q => (encSubArg q).length := by
  have hpar := fst (encPair encNat encNat) (encPair encNat (encOption encNat))
  have harg := snd (encPair encNat encNat) (encPair encNat (encOption encNat))
  have hp := fst' hpar
  have ha := budget_comp_linear (of_inO (ComputableInDegree.optionGetD encNat 0).inO_one)
    (snd' harg)
  have hm := budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod (snd' hpar) ha))
  have hn := budget_comp_linear negMod_inSpace (budget_prod hp hm)
  have he := budget_comp_linear addMod_inSpace (budget_prod hp (budget_prod (fst' harg) hn))
  exact budget_comp_linear (of_inO (ComputableInDegree.optionSome (enc₁ := encNat)).inO_one) he

private theorem length_encList_mapIdx_le (l : List ℕ) (f : ℕ → ℕ → ℕ) (P : ℕ)
    (hf : ∀ i v, (encNat (f i v)).length ≤ P + (encNat v).length) :
    (encList encNat (l.mapIdx f)).length ≤ (encList encNat l).length + l.length * (2 * P) := by
  induction l generalizing f with
  | nil => simp
  | cons v l ih =>
    have h₁ := hf 0 v
    have h₂ := ih (fun i => f (i + 1)) fun i w => hf (i + 1) w
    rw [List.mapIdx_cons]
    simp only [length_encList, List.map_cons, List.sum_cons, List.length_cons] at h₁ h₂ ⊢
    nlinarith

/-- **The register with `c` times the sums subtracted**, from `((p, c), r, acc)`. -/
private theorem subtractList_inSpace :
    ∃ K, ComputableInSpace
      (fun q : (ℕ × ℕ) × List ℕ × List ℕ =>
        zipFold (fun q v a => some (subElem q v a)) q.1 q.2.1 q.2.2)
      encSubInput (encList encNat)
      fun q => K * ((encSubInput q).length + 2 * ((encSubInput q).length +
        q.2.1.length * ((encNat q.1.1).length + 1)) + 1) := by
  refine ComputableInSpace.zipFold subElem_inSpace fun ⟨⟨p, c⟩, r, acc⟩ i => ?_
  rw [zipFold_some]
  have h₁ := length_encList_mapIdx_le (r.take i)
    (fun j v => subElem (p, c) v acc[j]?) (encNat p).length fun _ _ => length_subElem_le ..
  have h₂ := length_encList_take_le encNat r i
  have h₃ : (r.take i).length * (2 * (encNat p).length) ≤ r.length * (2 * (encNat p).length) :=
    Nat.mul_le_mul_right _ (by simp)
  simp only [length_encPair] at h₁ ⊢
  nlinarith

/-- **Subtracting `c` times the sums of a pass from a register**, within a budget that covers the
register with every entry as long as the prime. -/
theorem subtractSums_inSpace {p c : α → ℕ} {t : α → Fin 3} {acc : α → List ℕ} {R : α → Regs}
    (hp : ComputableInSpace p encIn encNat Bs)
    (hc : ComputableInSpace c encIn encNat Bs)
    (ht : ComputableInSpace t encIn encReg Bs)
    (hacc : ComputableInSpace acc encIn (encList encNat) Bs)
    (hR : ComputableInSpace R encIn encRegs Bs)
    (hB : (fun x => ((R x).get (t x)).length * ((encNat (p x)).length + 1)) ≼ Bs) :
    ComputableInSpace (fun x => subtractSums (p x) (c x) (t x) (acc x) (R x)) encIn encRegs Bs
    := by
  have harg := budget_prod (budget_prod hp hc) (budget_prod (get_inSpace hR ht) hacc)
  obtain ⟨K, hlist⟩ := subtractList_inSpace
  have hsub := budget_comp hlist harg
    (.const_mul K (((length_le harg).add (.const_mul 2 ((length_le harg).add hB))).add
      (.const 1 _)))
  exact (set_inSpace hR ht hsub).of_enc_eq fun x => by rw [subtractSums_eq]

/-- **The bits of a register**, `l.map (· == 1)`, encoded as themselves. -/
theorem mapEqOne_inSpace :
    ComputableInSpace (fun l : List ℕ => l.map (· == 1)) (encList encNat) encBits
      fun l => 64 * ((encList encNat l).length + 1) := by
  have hstep : ComputableInSpace (fun q : List Bool × ℕ => q.1 ++ [q.2 == 1])
      (encPair encBits encNat) encBits fun q => 8 * ((encPair encBits encNat q).length + 1) := by
    have hl : (fun q => (encPair encBits encNat q).length) ≼
        fun q => 4 * ((encPair encBits encNat q).length + 1) := .of_le fun _ => by omega
    have he := budget_comp_linear natEq (budget_prod ((snd encBits encNat).weaken hl)
      (budget_const (encB := encNat) 1 hl))
    have h := ComputableInSpace.append ((fst encBits encNat).weaken hl) he
      (g := fun q : List Bool × ℕ => q.1 ++ [q.2 == 1]) (encD := encBits) fun q => by
        cases hq : q.2 == 1 <;> simp_all [encBits_apply, encBool_apply]
    exact h.weaken (.of_le fun _ => by omega)
  have hlen (l : List ℕ) (i : ℕ) (hi : i ≤ l.length) :
      (encBits ((l.take i).foldl (fun acc v => acc ++ [v == 1]) [])).length ≤
        (encList encNat l).length := by
    have hf (m : List ℕ) (acc : List Bool) :
        (m.foldl (fun acc v => acc ++ [v == 1]) acc) = acc ++ m.map (· == 1) := by
      induction m generalizing acc with
      | nil => simp
      | cons v m ih => simp [ih]
    rw [hf, encBits_apply, List.nil_append, List.length_map]
    have := List.length_take_le' i l
    have := length_le_length_encList encNat l
    omega
  have h := foldl (encL := encList encNat) (list := fun l : List ℕ => l)
    (init := fun _ => ([] : List Bool)) (step := fun acc v => acc ++ [v == 1])
    (of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)) (budget_const [] (.refl _)) hstep
    (Q := fun l => 8 * (3 * (encList encNat l).length + 2))
    (B := fun l => (encList encNat l).length)
    (fun l i hi => by
      have h₁ := hlen l i hi.le
      have h₂ := length_le_encList_of_mem encNat (List.getElem_mem hi)
      rw [length_encPair]; dsimp only; omega)
    (fun l i hi => hlen l i hi)
  refine h.mono_le (fun l => by omega) |>.of_enc_eq fun l => ?_
  have hf (m : List ℕ) (acc : List Bool) :
      (m.foldl (fun acc v => acc ++ [v == 1]) acc) = acc ++ m.map (· == 1) := by
    induction m generalizing acc with
    | nil => simp
    | cons v m ih => simp [ih]
  rw [hf, List.nil_append]

end Reader

end Cslib.TreeEval
