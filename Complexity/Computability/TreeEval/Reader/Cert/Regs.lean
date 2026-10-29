/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Reader.Cert.Residue
public import Complexity.Computability.TreeEval.Reader.Encode

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

/-- A step of subtracting `c` times the sums `acc` from a register, on `((p, c, acc), i, out)`. -/
private def subStep (s : (ℕ × ℕ × List ℕ) × ℕ × List ℕ) (v : ℕ) : (ℕ × ℕ × List ℕ) × ℕ × List ℕ :=
  (s.1, s.2.1 + 1, s.2.2 ++ [addMod s.1.1 v (negMod s.1.1 (mulMod s.1.1 s.1.2.1
    (s.1.2.2.getD s.2.1 0)))])

private theorem foldl_subStep (p c : ℕ) (acc l : List ℕ) (j : ℕ) (out : List ℕ) :
    l.foldl subStep ((p, c, acc), j, out) = ((p, c, acc), j + l.length, out ++ l.mapIdx fun i v =>
      addMod p v (negMod p (mulMod p c (acc.getD (j + i) 0)))) := by
  induction l generalizing j out with
  | nil => simp
  | cons v l ih =>
    have hf : (fun i w => addMod p w (negMod p (mulMod p c (acc.getD (j + 1 + i) 0)))) =
        (fun i w => addMod p w (negMod p (mulMod p c (acc.getD (j + (i + 1)) 0)))) := by
      funext i w; rw [show j + 1 + i = j + (i + 1) by omega]
    rw [List.foldl_cons, subStep, ih, List.mapIdx_cons, hf]
    simp only [List.length_cons, List.append_assoc, List.singleton_append, add_zero,
      Prod.mk.injEq, true_and, and_true]
    omega

private theorem subtractSums_eq (p c : ℕ) (t : Fin 3) (acc : List ℕ) (R : Regs) :
    subtractSums p c t acc R = R.set t (((R.get t).foldl subStep ((p, c, acc), 0, [])).2.2) := by
  rw [foldl_subStep, subtractSums]
  congr 1
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  have hi : i < (R.get t).length := by simpa using h₁
  simp [List.getElem_mapIdx, List.getD_eq_getElem?_getD, hi]

/-- The encoding of the parameters `(p, c, acc)` of `subStep`. -/
private abbrev encSubPar : ℕ × ℕ × List ℕ ↪ List Bool := encPair encNat
    (encPair encNat (encList encNat))

/-- The encoding of the states of `subStep`. -/
private abbrev encSubState : (ℕ × ℕ × List ℕ) × ℕ × List ℕ ↪ List Bool :=
  encPair encSubPar (encPair encNat (encList encNat))

private theorem length_subElem_le (p c v a : ℕ) :
    (encNat (addMod p v (negMod p (mulMod p c a)))).length ≤ (encNat p).length + (encNat v).length
    := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [addMod, negMod]
  · have := length_encNat_mono (Nat.mod_lt (v + negMod p (mulMod p c a)) hp).le
    simp only [addMod]; omega

private theorem subStep_inSpace :
    ComputableInSpace (fun q : ((ℕ × ℕ × List ℕ) × ℕ × List ℕ) × ℕ => subStep q.1 q.2)
      (encPair encSubState encNat) encSubState
      fun q => 64 * ((encPair encSubState encNat q).length + 1) := by
  have hl : (fun q => (encPair encSubState encNat q).length) ≼
      fun q => 64 * ((encPair encSubState encNat q).length + 1) := .of_le fun _ => by omega
  have hs := (fst encSubState encNat).weaken hl
  have hv := (snd encSubState encNat).weaken hl
  have hpar := fst' hs
  have hp := fst' hpar
  have hc := fst' (snd' hpar)
  have hacc := snd' (snd' hpar)
  have hj := fst' (snd' hs)
  have hout := snd' (snd' hs)
  have ha := budget_comp_lin getD (linear_mul _) (budget_prod hacc hj)
  have hm := budget_comp_linear mulMod_inSpace (budget_prod hp (budget_prod hc ha))
  have hn := budget_comp_linear negMod_inSpace (budget_prod hp hm)
  have he := budget_comp_linear addMod_inSpace (budget_prod hp (budget_prod hv hn))
  have happ := budget_snoc hout he
  have hsucc := budget_comp_lin natSucc linear_succ hj
  exact budget_prod hpar (budget_prod hsucc happ)

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

/-- **The register with `c` times the sums subtracted**, from `((p, c, acc), r)`. -/
private theorem subtractList_inSpace :
    ComputableInSpace
      (fun q : (ℕ × ℕ × List ℕ) × List ℕ => (q.2.foldl subStep (q.1, 0, [])).2.2)
      (encPair encSubPar (encList encNat)) (encList encNat)
      fun q => 8192 * ((encPair encSubPar (encList encNat) q).length +
        q.2.length * ((encNat q.1.1).length + 1) + 1) := by
  have hl : (fun q => (encPair encSubPar (encList encNat) q).length) ≼
      fun q => 2048 * ((encPair encSubPar (encList encNat) q).length +
        q.2.length * ((encNat q.1.1).length + 1) + 1) := .of_le fun _ => by nlinarith
  have hlist := (snd encSubPar (encList encNat)).weaken hl
  have hinit := budget_prod ((fst encSubPar (encList encNat)).weaken hl)
    (budget_prod (budget_const (encB := encNat) 0 hl)
      (budget_const (encB := encList encNat) ([] : List ℕ) hl))
  have hlen (l : List ℕ) : l.length ≤ (encList encNat l).length := by
    rw [length_encList]
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  have hstate (q : (ℕ × ℕ × List ℕ) × List ℕ) (j : ℕ) (hj : j ≤ q.2.length) :
      (encSubState ((q.2.take j).foldl subStep (q.1, 0, []))).length ≤
        4 * ((encPair encSubPar (encList encNat) q).length +
          q.2.length * ((encNat q.1.1).length + 1) + 1) := by
    obtain ⟨⟨p, c, acc⟩, r⟩ := q
    rw [foldl_subStep]
    have h₁ := length_encList_mapIdx_le (r.take j)
      (fun i v => addMod p v (negMod p (mulMod p c (acc.getD (0 + i) 0)))) (encNat p).length
      fun i v => length_subElem_le p c v _
    have h₂ := length_encList_take_le encNat r j
    have h₃ : (encNat (0 + (r.take j).length)).length ≤ r.length := by
      rw [length_encNat_eq_size]
      exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by rw [zero_add, List.length_take]; omega)
    have h₄ := hlen r
    have h₅ : (r.take j).length * (2 * (encNat p).length) ≤ r.length * (2 * (encNat p).length) :=
      Nat.mul_le_mul_right _ (by simp)
    simp only [length_encPair, List.nil_append] at h₁ ⊢
    nlinarith
  have h := foldl (encL := encList encNat) (list := fun q : (ℕ × ℕ × List ℕ) × List ℕ => q.2)
    (step := subStep) hlist hinit subStep_inSpace
    (Q := fun q => 64 * (2 * (4 * ((encPair encSubPar (encList encNat) q).length +
      q.2.length * ((encNat q.1.1).length + 1) + 1)) + 1 +
      (encPair encSubPar (encList encNat) q).length + 1))
    (B := fun q => 4 * ((encPair encSubPar (encList encNat) q).length +
      q.2.length * ((encNat q.1.1).length + 1) + 1))
    (fun q i hi => by
      have h₁ := hstate q i hi.le
      have h₂ := length_le_encList_of_mem encNat (List.getElem_mem hi)
      have h₃ : (encList encNat q.2).length ≤ (encPair encSubPar (encList encNat) q).length := by
        rw [length_encPair]; omega
      rw [length_encPair]; dsimp only; omega)
    (fun q i hi => hstate q i hi)
  refine (snd' (snd' h)).mono_le fun q => ?_
  have : (encList encNat q.2).length ≤ (encPair encSubPar (encList encNat) q).length := by
    rw [length_encPair]; omega
  omega

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
  have harg := budget_prod (budget_prod hp (budget_prod hc hacc)) (get_inSpace hR ht)
  have hsub := budget_comp subtractList_inSpace harg (by
    refine .const_mul 8192 (((length_le harg).add hB).add (.const 1 _)))
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
