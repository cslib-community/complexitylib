/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.HashFamily.WordRAM.Tabulation

/-!
# Two adjacent random fills

The double-tabulation and reduced `k`-wise families resample their seeds the same way: a setup
program, a `randFillLoop` over a first slice of `n₁` words of `b₁` bits at `base`, a second setup,
and a `randFillLoop` over the adjacent slice of `n₂` words of `b₂` bits, both through one renamed
six-register bank. This module proves the execution, the pathwise facts and the product
uniformity of the two slices once, for arbitrary setups.

## Main definitions

* `Tabulation.twoFillCode`, `Tabulation.twoFillComp`: the program and its explicit computation.

## Main results

* `Tabulation.twoFillCode_execRand`: exact randomized execution, given the setups' effects.
* `Tabulation.mem_support_twoFillComp`: bounded slice words, frame, preserved extra register and
  exact cost on every outcome.
* `Tabulation.map_extractSlices_eval_twoFillComp`: the two slices are jointly uniform.
-/

public section

namespace Cslib.DataStructure.HashFamily.WordRAM.Tabulation

open Cslib.WordRAM Cslib.Probability

variable {r : ℕ}

/-- Setup `c₁`, fill the first slice, setup `c₂`, fill the second slice, with the fill bank renamed
by `f`. -/
@[expose] def twoFillCode (f : Fin 6 → Fin r) (c₁ c₂ : Code .exact r) : Code .exact r :=
  .seq c₁ (.seq (randFillLoop.rename f) (.seq c₂ (randFillLoop.rename f)))

/-- The computation of `twoFillCode f c₁ c₂` when the setups reach `s₁ x` in `t₁` and `s₂ y` in
`t₂` instructions: `n₁` words of `b₁` bits at `base`, then `n₂` words of `b₂` bits after them. -/
@[expose] noncomputable def twoFillComp (f : Fin 6 → Fin r) (s₁ s₂ : Data r → Data r)
    (t₁ t₂ b₁ b₂ base n₁ n₂ : ℕ) (x : Data r) : ProbComp (Data r × ℕ) := do
  let x1 := s₁ x
  let z1 ← randFillComp b₁ base n₁ (x1.comap f)
  let x2 := s₂ (z1.1.extend f x1)
  let z2 ← randFillComp b₂ (base + n₁) n₂ (x2.comap f)
  pure (z2.1.extend f x2, t₁ + (z1.2 + (t₂ + z2.2)))

/-- **Exact `ExecRand` execution of `twoFillCode`.** The first setup prepares the first fill; the
second prepares the second fill from any state whose fill bank ends the first slice and holds
one. -/
theorem twoFillCode_execRand {w : ℕ} {f : Fin 6 → Fin r} (hf : Function.Injective f)
    {c₁ c₂ : Code .exact r} {s₁ s₂ : Data r → Data r} {t₁ t₂ b₁ b₂ base n₁ n₂ : ℕ}
    {x : Data r} (h₁ : Exec w c₁ x (s₁ x) t₁)
    (hptr₁ : ((s₁ x).comap f).regs regPtr = base)
    (hend₁ : ((s₁ x).comap f).regs regEnd = base + n₁)
    (hmask₁ : ((s₁ x).comap f).regs regMask = 2 ^ b₁ - 1)
    (hone₁ : ((s₁ x).comap f).regs regOne = 1)
    (h₂ : ∀ y, (y.comap f).regs regEnd = base + n₁ → Exec w c₂ y (s₂ y) t₂)
    (hs₂ : ∀ y, (y.comap f).regs regOne = 1 →
      ((s₂ y).comap f).regs regPtr = base + n₁ ∧
      ((s₂ y).comap f).regs regEnd = base + n₁ + n₂ ∧
      ((s₂ y).comap f).regs regMask = 2 ^ b₂ - 1 ∧ ((s₂ y).comap f).regs regOne = 1)
    (hfit₁ : Fits w (base + n₁)) (hmask_fit₁ : Fits w (2 ^ b₁ - 1))
    (hfit₂ : Fits w (base + n₁ + n₂)) (hmask_fit₂ : Fits w (2 ^ b₂ - 1)) :
    ExecRand w (twoFillCode f c₁ c₂) x (twoFillComp f s₁ s₂ t₁ t₂ b₁ b₂ base n₁ n₂ x) := by
  set x1 := s₁ x
  have hloop1 := (randFillLoop_execRand (w := w) (bits := b₁) (arrBase := base) n₁
    (x := x1.comap f) hptr₁ hend₁ hmask₁ hone₁ hfit₁ hmask_fit₁).rename hf
  have hrest : ∀ z1 ∈ (randFillComp b₁ base n₁ (x1.comap f)).support,
      ExecRand w (.seq c₂ (randFillLoop.rename f)) (z1.1.extend f x1) (do
        let x2 := s₂ (z1.1.extend f x1)
        let z2 ← randFillComp b₂ (base + n₁) n₂ (x2.comap f)
        pure (z2.1.extend f x2, t₂ + z2.2)) := by
    intro z1 hz1
    obtain ⟨_, _, hend1, _, hone1, _, _, _⟩ := mem_support_randFillComp hz1
    set y1 := z1.1.extend f x1
    have hy1 : y1.comap f = z1.1 := Data.comap_extend hf _ _
    obtain ⟨hptr₂, hend₂, hmask₂, hone₂⟩ := hs₂ y1 (by rw [hy1, hone1, hone₁])
    have h2 := (h₂ y1 (by rw [hy1, hend1, hend₁])).execRand
    have hloop2 := (randFillLoop_execRand (w := w) (bits := b₂) (arrBase := base + n₁) n₂
      (x := (s₂ y1).comap f) hptr₂ hend₂ hmask₂ hone₂ hfit₂ hmask_fit₂).rename hf
    have hseq2 := ExecRand.seq
      (m₂ := fun z : Data r =>
        (fun z2 : Data 6 × ℕ => (z2.1.extend f z, z2.2)) <$>
          randFillComp b₂ (base + n₁) n₂ (z.comap f))
      h2 (fun z hz => by
        cases OracleComp.eq_of_mem_supportWith_pure hz
        exact hloop2)
    simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def] using hseq2
  have hseq12 := ExecRand.seq
    (m₂ := fun z : Data r => do
      let x2 := s₂ z
      let z2 ← randFillComp b₂ (base + n₁) n₂ (x2.comap f)
      pure (z2.1.extend f x2, t₂ + z2.2))
    hloop1 (fun z hz => by
      obtain ⟨z1, hz1, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
      exact hrest z1 hz1)
  have hall := ExecRand.seq
    (m₂ := fun z : Data r => do
      let z1 ← randFillComp b₁ base n₁ (z.comap f)
      let x2 := s₂ (z1.1.extend f z)
      let z2 ← randFillComp b₂ (base + n₁) n₂ (x2.comap f)
      pure (z2.1.extend f x2, z1.2 + (t₂ + z2.2)))
    h₁.execRand (fun z hz => by
      cases OracleComp.eq_of_mem_supportWith_pure hz
      simpa only [bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp_def] using hseq12)
  simpa only [twoFillCode, twoFillComp, bind_assoc, pure_bind, map_eq_bind_pure_comp,
    Function.comp_def] using hall

/-- **Pathwise facts of `twoFillComp`**, for setups that change only registers outside the extra
fill register: both slices hold words of their widths, memory outside them is unchanged, the extra
register survives and the cost is exact. -/
theorem mem_support_twoFillComp {f : Fin 6 → Fin r} (hf : Function.Injective f)
    {s₁ s₂ : Data r → Data r} {t₁ t₂ b₁ b₂ base n₁ n₂ : ℕ} {x : Data r}
    (hs₁ : ∀ y, (s₁ y).mem = y.mem ∧
      ((s₁ y).comap f).regs regExtra = (y.comap f).regs regExtra)
    (hs₂ : ∀ y, (s₂ y).mem = y.mem ∧
      ((s₂ y).comap f).regs regExtra = (y.comap f).regs regExtra)
    {z : Data r × ℕ} (hz : z ∈ (twoFillComp f s₁ s₂ t₁ t₂ b₁ b₂ base n₁ n₂ x).support) :
    (z.1.comap f).regs regExtra = (x.comap f).regs regExtra ∧
      (∀ i < n₁, z.1.mem (base + i) < 2 ^ b₁) ∧
      (∀ i < n₂, z.1.mem (base + n₁ + i) < 2 ^ b₂) ∧
      (∀ a, (a < base ∨ base + n₁ + n₂ ≤ a) → z.1.mem a = x.mem a) ∧
      z.2 = t₁ + (5 * n₁ + 2 + (t₂ + (5 * n₂ + 2))) := by
  dsimp only [twoFillComp] at hz
  obtain ⟨z1, hz1, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  obtain ⟨z2, hz2, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
  cases OracleComp.eq_of_mem_supportWith_pure hpure
  obtain ⟨hsteps1, _, _, _, _, hextra1, hlt1, hframe1⟩ := mem_support_randFillComp hz1
  obtain ⟨hsteps2, _, _, _, _, hextra2, hlt2, hframe2⟩ := mem_support_randFillComp hz2
  obtain ⟨hm1, he1⟩ := hs₁ x
  obtain ⟨hm2, he2⟩ := hs₂ (z1.1.extend f (s₁ x))
  -- Memory after the second setup is that of the first fill's outcome.
  have hmem2 : ((s₂ (z1.1.extend f (s₁ x))).comap f).mem = z1.1.mem := hm2
  refine ⟨?_, fun i hi => ?_, hlt2, fun a ha => ?_, ?_⟩
  · rw [Data.comap_extend hf, hextra2, he2, Data.comap_extend hf, hextra1, he1]
  · change z2.1.mem (base + i) < 2 ^ b₁
    rw [hframe2 _ (Or.inl (by omega)), hmem2]
    exact hlt1 i hi
  · change z2.1.mem a = x.mem a
    rw [hframe2 a (by omega), hmem2, hframe1 a (by omega)]
    exact hm1 ▸ rfl
  · rw [hsteps1, hsteps2]

/-- **Joint uniformity of the two slices** produced by `twoFillComp`, for a second setup that does
not write memory. -/
theorem map_extractSlices_eval_twoFillComp {f : Fin 6 → Fin r} {s₁ s₂ : Data r → Data r}
    {t₁ t₂ b₁ b₂ base n₁ n₂ : ℕ} (hs₂ : ∀ y, (s₂ y).mem = y.mem) (x : Data r) :
    ((twoFillComp f s₁ s₂ t₁ t₂ b₁ b₂ base n₁ n₂ x).eval).map
        (fun z => (extractSlice base b₁ n₁ z.1.mem, extractSlice (base + n₁) b₂ n₂ z.1.mem)) =
      PMF.uniformOfFintype ((Fin n₁ → Fin (2 ^ b₁)) × (Fin n₂ → Fin (2 ^ b₂))) := by
  set x1 := s₁ x
  set m1 := randFillComp b₁ base n₁ (x1.comap f)
  have hinner : ∀ z1 : Data 6 × ℕ,
      (let x2 := s₂ (z1.1.extend f x1)
       (do
         let z2 ← randFillComp b₂ (base + n₁) n₂ (x2.comap f)
         pure (z2.1.extend f x2, t₁ + (z1.2 + (t₂ + z2.2)))).eval).map
        (fun z : Data r × ℕ =>
          (extractSlice base b₁ n₁ z.1.mem, extractSlice (base + n₁) b₂ n₂ z.1.mem)) =
      (PMF.uniformOfFintype (Fin n₂ → Fin (2 ^ b₂))).map
        (fun s => (extractSlice base b₁ n₁ z1.1.mem, s)) := by
    intro z1
    dsimp only
    set x2 := s₂ (z1.1.extend f x1)
    set m2 := randFillComp b₂ (base + n₁) n₂ (x2.comap f)
    have hd : (do
        let z2 ← m2
        pure (z2.1.extend f x2, t₁ + (z1.2 + (t₂ + z2.2)))) =
        (fun z2 : Data 6 × ℕ => (z2.1.extend f x2, t₁ + (z1.2 + (t₂ + z2.2)))) <$> m2 :=
      bind_pure_comp _ _
    rw [hd, ProbComp.eval_map, PMF.map_comp]
    have hcongr :
        m2.eval.map
          ((fun z : Data r × ℕ =>
              (extractSlice base b₁ n₁ z.1.mem, extractSlice (base + n₁) b₂ n₂ z.1.mem)) ∘
            fun z2 : Data 6 × ℕ => (z2.1.extend f x2, t₁ + (z1.2 + (t₂ + z2.2)))) =
        m2.eval.map
          ((fun s => (extractSlice base b₁ n₁ z1.1.mem, s)) ∘
            fun z2 : Data 6 × ℕ => extractSlice (base + n₁) b₂ n₂ z2.1.mem) := by
      refine Cslib.Probability.PMF.map_congr_on_support _ _ _ fun z2 hz2 => ?_
      rw [ProbComp.support_eval] at hz2
      obtain ⟨_, _, _, _, _, _, _, hframe2⟩ := mem_support_randFillComp hz2
      have hslice : extractSlice base b₁ n₁ z2.1.mem = extractSlice base b₁ n₁ z1.1.mem := by
        funext idx
        dsimp only [extractSlice]
        rw [hframe2 (base + idx.val) (Or.inl (by have := idx.isLt; omega)),
          show (x2.comap f).mem = z1.1.mem from hs₂ _]
      dsimp only [Function.comp_apply, Data.extend]
      rw [hslice]
    rw [hcongr, ← PMF.map_comp, map_extractSlice_eval_randFillComp]
  dsimp only [twoFillComp]
  rw [ProbComp.eval_bind, PMF.map_bind]
  have hbind : m1.eval.bind
      (fun z1 =>
        (let x2 := s₂ (z1.1.extend f x1)
         (do
           let z2 ← randFillComp b₂ (base + n₁) n₂ (x2.comap f)
           pure (z2.1.extend f x2, t₁ + (z1.2 + (t₂ + z2.2)))).eval).map
          (fun z : Data r × ℕ =>
            (extractSlice base b₁ n₁ z.1.mem, extractSlice (base + n₁) b₂ n₂ z.1.mem))) =
      m1.eval.bind
        (fun z1 =>
          (PMF.uniformOfFintype (Fin n₂ → Fin (2 ^ b₂))).map
            (fun s => (extractSlice base b₁ n₁ z1.1.mem, s))) := by
    congr 1
    funext z1
    exact hinner z1
  rw [hbind]
  have hmap_bind :
      m1.eval.bind
        (fun z1 =>
          (PMF.uniformOfFintype (Fin n₂ → Fin (2 ^ b₂))).map
            (fun s => (extractSlice base b₁ n₁ z1.1.mem, s))) =
      (m1.eval.map (fun z1 => extractSlice base b₁ n₁ z1.1.mem)).bind
        (fun s₁ => (PMF.uniformOfFintype (Fin n₂ → Fin (2 ^ b₂))).map (s₁, ·)) := by
    rw [PMF.bind_map]
    rfl
  rw [hmap_bind, map_extractSlice_eval_randFillComp, PMF.uniformOfFintype_prod]

end Cslib.DataStructure.HashFamily.WordRAM.Tabulation
