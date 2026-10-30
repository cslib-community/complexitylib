/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine
import Mathlib.Data.List.GetD

/-!
# Framed native routines for nondeterministic query machines

The abstract state is framed on a work tape. Each deterministic pass reads the input in place,
performs one selected transition, and writes the continuation flag. Only the finalizer emits.

## Main definitions

* `Turing.NondeterministicQueryMachine.Routines`: finite native routines and their specifications.

## Main results

* `Turing.NondeterministicQueryMachine.exists_routines`: constructs the routines from local
  linear-space computability, with one space bound for all reachable boundary states.
-/

@[expose] public section

namespace Turing.NondeterministicQueryMachine

open MultiTapeTM QueryMachine.Simulation

open ComputableTidilyInLinearTimeAndSpace in
private theorem linearFlag : ComputableTidilyInLinearTimeAndSpace flagWord encBool encBits := by
  convert (of_eq (f := id) (encIn := encBool) (encMid := encBool) fun _ => rfl).ite
    ((const [true]).restrict _) ((const []).restrict _) using 1
  funext c
  cases c <;> rfl

private theorem blankBoundary {k : ℕ} {V C : Fin k} (hVC : V ≠ C) (v : List Bool) :
    passTapes V C v [] = Function.update (fun _ => []) V v := by
  funext l
  by_cases hl : l = C
  · subst hl; simp [passTapes, hVC.symm]
  · simp [passTapes, hl]

/-- Concrete finite routines, sharing tape origins and a common linear space budget. -/
structure Routines {α σ : Type} (M : NondeterministicQueryMachine σ)
    (enc : α ↪ List Bool) (S : α → ℕ) where
  /-- The shared number of work tapes. -/
  k : ℕ
  /-- Finite control of the initialization routine. -/
  SI : Type
  /-- Finite control of each binary-choice pass routine. -/
  SP : Bool → Type
  /-- Finite control of the final verdict routine. -/
  SF : Type
  finiteI : Finite SI
  finiteP : ∀ b, Finite (SP b)
  finiteF : Finite SF
  /-- The initialization machine. -/
  I : MultiTapeTM k Bool SI
  /-- The pass machine selected by one nondeterministic bit. -/
  P : (b : Bool) → MultiTapeTM k Bool (SP b)
  /-- The machine emitting the final verdict. -/
  F : MultiTapeTM k Bool SF
  /-- The tape holding the continuation flag. -/
  C : Fin k
  /-- The encoded abstract state and flag at the common tape origins. -/
  boundary : σ → Bool → (Fin k → List Bool)
  boundary_flag : ∀ s b, boundary s b C = flagWord b
  boundary_injective : ∀ s b s' b', boundary s b = boundary s' b' → s = s'
  /-- A common coefficient for the routines' space windows. -/
  c : ℕ
  initial_spec : ∀ a, ∃ t, TransformsTapes I
    (fun inp ws => inp = enc a ∧ ws = fun _ => [])
    (fun _ _ ws' e => ws' = boundary M.init false ∧ e = []) t (c * S a)
  pass_spec : ∀ a s, M.Reachable (enc a) s → ∀ choice flag, ∃ t, TransformsTapes (P choice)
    (fun inp ws => inp = enc a ∧ ws = boundary s flag)
    (fun _ _ ws' e => ws' = boundary (M.step (enc a) s choice)
      (!M.halted (M.step (enc a) s choice)) ∧ e = []) t (c * S a)
  final_spec : ∀ a s, M.Reachable (enc a) s → ∀ flag, ∃ t, TransformsTapes F
    (fun inp ws => inp = enc a ∧ ws = boundary s flag)
    (fun _ _ _ e => e = [M.accept s]) t (c * S a)

/-- Compile local query-machine callbacks into concrete finite native routines. -/
theorem exists_routines {α σ : Type} {enc : α ↪ List Bool} {encS : σ ↪ List Bool}
    (M : NondeterministicQueryMachine σ)
    (hquery : ComputableTidilyInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableTidilyInSpace M.next
      (encPair encS (encPair (encOption encBool) encBool)) encS
      fun p => (encPair encS (encPair (encOption encBool) encBool) p).length)
    (hhalted : ComputableTidilyInSpace M.halted encS encBool fun s => (encS s).length)
    (haccept : ComputableTidilyInSpace M.accept encS encBool fun s => (encS s).length)
    (S : α → ℕ) (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hsize : ∃ c, ∀ a choices, (encS (M.run (enc a) choices)).length ≤ c * S a) :
    Nonempty (Routines M enc S) := by
  classical
  obtain ⟨cS, hS⟩ := hsize
  have hS1 (a : α) : 1 ≤ S a := (Nat.le_add_left _ _).trans (hlog a)
  have hreach (a : α) (s : σ) (hs : M.Reachable (enc a) s) :
      (encS s).length ≤ cS * S a := by
    obtain ⟨coins, rfl⟩ := hs
    exact hS a coins
  obtain ⟨cI, hI⟩ := computableInTimeAndSpace_of_const (encIn := enc)
    (encOut := encPass encS) ((M.init, 0, none) : PassState σ)
  obtain ⟨cE, hE⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair (encPass encS) encBool) (encOut := encBits) ([] : List Bool)
  obtain ⟨cPE, hPE⟩ := computableInTimeAndSpace_of_const
    (encIn := encPass encS) (encOut := encBits) ([] : List Bool)
  obtain ⟨TN, cN, hN, -⟩ := passNext_inSpace hquery false
  have hpns (b : Bool) := passEnd_inSpace hnext hhalted b
  choose TPN cPN hPN hlenPN using hpns
  obtain ⟨TC, cC, hC, -⟩ := passCont_inSpace hhalted false
  obtain ⟨TF, cF, hF, -⟩ := passFinish_inSpace haccept false
  obtain ⟨cfr, hfr⟩ := ComputableTidilyInLinearTimeAndSpace.of_frame (f := id)
    (encIn := encPass encS) (encOut := encFramed (encPass encS)) fun _ => rfl
  obtain ⟨cuf, huf⟩ := ComputableTidilyInLinearTimeAndSpace.of_unframe (f := id)
    (encIn := encFramed (encPass encS)) (encOut := encPass encS) fun s => by simp
  obtain ⟨cfl, hfl⟩ := linearFlag
  obtain ⟨cI', hI'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr
    hI.computableTidilyInTimeAndSpace
  obtain ⟨cN', hN'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr hN
  obtain ⟨cF', hF'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hF huf
  obtain ⟨cPE', hPE'⟩ := ComputableTidilyInTimeAndSpace.comp_linear
    hPE.computableTidilyInTimeAndSpace huf
  have hpn₁ (b : Bool) := ComputableTidilyInTimeAndSpace.comp_linear (hPN b) huf
  choose cPN₁ hPN₁ using hpn₁
  have hpn' (b : Bool) := ComputableTidilyInTimeAndSpace.comp_linear hfr (hPN₁ b)
  choose cPN' hPN' using hpn'
  obtain ⟨cC₁, hC₁⟩ := ComputableTidilyInTimeAndSpace.comp_linear hC huf
  obtain ⟨cC', hC'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfl hC₁
  obtain ⟨kI, SI, _, tmI, htmI⟩ := hI'
  obtain ⟨kE, SE, _, tmE, htmE⟩ := hE.computableTidilyInTimeAndSpace
  obtain ⟨kN, SN, _, tmN, htmN⟩ := hN'
  obtain ⟨kF, SF, _, tmF, htmF⟩ := hF'
  obtain ⟨kPE, SPE, _, tmPE, htmPE⟩ := hPE'
  choose kPN SPN finitePN tmPN htmPN using hPN'
  let : ∀ b, Finite (SPN b) := finitePN
  obtain ⟨kC, SC, _, tmC, htmC⟩ := hC'
  let m := kI + kE + kN + kF + kPE + kPN false + kPN true + kC + 8
  let V : Fin (m + 4) := ⟨m, by omega⟩
  let N : Fin (m + 4) := ⟨m + 1, by omega⟩
  let W : Fin (m + 4) := ⟨m + 2, by omega⟩
  let C : Fin (m + 4) := ⟨m + 3, by omega⟩
  have hVN : V ≠ N := by simp [V, N, Fin.ext_iff]
  have hVW : V ≠ W := by simp [V, W, Fin.ext_iff]
  have hNW : N ≠ W := by simp [N, W, Fin.ext_iff]
  have hVC : V ≠ C := by simp [V, C, Fin.ext_iff]
  obtain ⟨eI, heI⟩ := exists_embedding_eq (K := m + 4) (by omega) (Fin.last kI) V
  obtain ⟨eE, heE⟩ := exists_embedding_eq (K := m + 4) (by omega)
    (Fin.natAdd kE (0 : Fin 2)) V
  obtain ⟨eN, heN, heN'⟩ := exists_embedding_eq₂ (K := m + 4) (by omega)
    (i := Fin.natAdd (kN + 1) (0 : Fin 2)) (o := (Fin.last kN).castAdd 2)
    (by simp [Fin.ext_iff]) hVN
  obtain ⟨eF, heF⟩ := exists_embedding_eq (K := m + 4) (by omega)
    (Fin.natAdd kF (0 : Fin 2)) V
  obtain ⟨ePE, hePE⟩ := exists_embedding_eq (K := m + 4) (by omega)
    (Fin.natAdd kPE (0 : Fin 2)) V
  have hepn (b : Bool) : ∃ e : Fin (kPN b + 1 + 2) ↪ Fin (m + 4),
      e (Fin.natAdd (kPN b + 1) (0 : Fin 2)) = V ∧
      e ((Fin.last (kPN b)).castAdd 2) = N := by
    apply exists_embedding_eq₂ (by cases b <;> dsimp [m] <;> omega)
      (by simp [Fin.ext_iff]) hVN
  choose ePN hePN hePN' using hepn
  obtain ⟨eC, heC, heC'⟩ := exists_embedding_eq₂ (K := m + 4) (by omega)
    (i := Fin.natAdd (kC + 1) (0 : Fin 2)) (o := (Fin.last kC).castAdd 2)
    (by simp [Fin.ext_iff]) hVC
  have hI₀ := fun a => (htmI a).outputToWord_onTape heI
  have hE₀ := fun a => (htmE a).inputFromWord_extendTapes true heE
  have hN₀ := fun a => (htmN a).onWords_extendTapes true heN heN'
  have hF₀ := fun a => (htmF a).inputFromWord_extendTapes true heF
  have hPE₀ := fun a => (htmPE a).inputFromWord_extendTapes true hePE
  have hPN₀ := fun b a => (htmPN b a).onWords_extendTapes true (hePN b) (hePN' b)
  have hC₀ := fun a => (htmC a).onWords_extendTapes true heC heC'
  let D := cfr + cuf + cfl + cI + cE + cPE + cN + cF + cC + cI' + cN' + cF' + cPE' +
    cPN false + cPN true + cPN₁ false + cPN₁ true + cPN' false + cPN' true + cC₁ + cC' + m + 100
  have hcPN (b : Bool) : cPN b ≤ D := by cases b <;> dsimp [D] <;> omega
  have hcPN₁ (b : Bool) : cPN₁ b ≤ D := by cases b <;> dsimp [D] <;> omega
  have hcPN' (b : Bool) : cPN' b ≤ D := by cases b <;> dsimp [D] <;> omega
  let L (a : α) := (2 * cS + 7) * S a
  have hL1 (a : α) : 1 ≤ L a := by have := hS1 a; dsimp [L]; nlinarith
  have hscan (a : α) (s : σ) (hs : M.Reachable (enc a) s) (b : Bool) (j : ℕ)
      (hj : j ≤ (enc a).length) :
      (encPass encS (streamState ((s, 0, none) : PassState σ)
        (passNext (M.withChoice b)) (enc a) j)).length ≤ L a := by
    rw [QueryMachine.Simulation.streamState_passNext _ _ _ hj]
    exact (length_passState_le (enc a) (hreach a s hs) (hlog a) hj _).trans
      (Nat.mul_le_mul_right _ (by omega))
  let B (s : σ) (flag : Bool) := passTapes V C
    (frame (encPass encS ((s, 0, none) : PassState σ))) (flagWord flag)
  let Im := tmI.outputToWord.extendTapes eI
  let Pm (b : Bool) := passTM
    (⟨(), fun _ bit => (none, some bit)⟩ : InputReader Bool Unit)
    ((tmE.inputFromWord true).extendTapes eE) ((tmN.onWords true).extendTapes eN)
    ((tmPE.inputFromWord true).extendTapes ePE) (((tmPN b).onWords true).extendTapes (ePN b))
    ((tmC.onWords true).extendTapes eC) V N W C hVN hVW hNW
  let Fm := ((clearWork Bool).extendTapes (tapeEmb C)).seq
    ((tmF.inputFromWord true).extendTapes eF)
  let G := 1000 * (m + 5) * D * (2 * cS + 8)
  have hD : m + 100 ≤ D := by dsimp [D]; omega
  have hG (a : α) : 1000 * (m + 5) * (D * (L a + 1)) ≤ G * S a := by
    have hLin : L a + 1 ≤ (2 * cS + 8) * S a := by
      dsimp [L]; have := hS1 a; nlinarith
    have hmult := Nat.mul_le_mul_left (1000 * (m + 5) * D) hLin
    dsimp [G]
    nlinarith
  refine ⟨{ k := m + 4
            SI := _
            SP := fun b => _
            SF := _
            finiteI := inferInstance
            finiteP := fun b => by
              set_option synthInstance.maxSize 1024 in infer_instance
            finiteF := inferInstance
            I := Im
            P := Pm
            F := Fm
            C := C
            boundary := B
            boundary_flag := ?_
            boundary_injective := ?_
            c := G
            initial_spec := ?_
            pass_spec := ?_
            final_spec := ?_ }⟩
  · intro s b
    simp [B, passTapes]
  · intro s b s' b' h
    have hv := congrFun h V
    simp only [B, passTapes, Function.update_of_ne hVC, Function.update_self] at hv
    have hp := (encPass encS).injective (frame_injective hv)
    exact congrArg Prod.fst hp
  · intro a
    have hlen := hscan a M.init (M.reachable_init _) false 0 (Nat.zero_le _)
    simp only [streamState_zero] at hlen
    have h := hI₀ a
    refine ⟨_, h.imp (fun _ _ h => h) (fun _ _ _ _ _ ⟨hw, he⟩ => ⟨?_, he⟩)
      le_rfl ?_⟩
    · simpa [B, flagWord, blankBoundary hVC] using hw
    · have hcfr : cfr ≤ D := by dsimp [D]; omega
      have hcI' : cI' ≤ D := by dsimp [D]; omega
      have hm₁ := Nat.mul_le_mul hcfr (Nat.add_le_add_right hlen 1)
      have hm₂ := Nat.mul_le_mul hcI' (Nat.add_le_add_right hlen 1)
      refine le_trans (b := 10 * (D * (L a + 1))) ?_
        ((Nat.mul_le_mul_right _ (by omega : 10 ≤ 1000 * (m + 5))).trans (hG a))
      simp only [Function.comp_apply, Function.const_apply, id_eq, encFramed_apply, length_frame]
      change 0 + cfr * ((encPass encS (M.init, 0, none)).length + 1) +
        cI' * ((encPass encS (M.init, 0, none)).length + 1) +
        2 * (2 * (encPass encS (M.init, 0, none)).length + 1) + kI + 4 +
        (m + 4 - (kI + 1)) ≤ _
      have hk : kI ≤ m := by dsimp [m]; omega
      have hU : m + 100 + L a ≤ D * (L a + 1) := by nlinarith
      omega
  · intro a s hs b flag
    let q (j : ℕ) := streamState ((s, 0, none) : PassState σ)
      (passNext (M.withChoice false)) (enc a) j
    let s' := M.step (enc a) s b
    let q' : PassState σ := (s', 0, none)
    have hend : passEnd (M.withChoice b) (q (enc a).length) = q' :=
      M.passEnd_streamState (enc a) b s
    have hq (j : ℕ) (hj : j ≤ (enc a).length) : (encPass encS (q j)).length ≤ L a :=
      hscan a s hs false j hj
    have hq' : (encPass encS q').length ≤ L a :=
      hscan a s' (Reachable.step M (enc a) hs b) false 0 (Nat.zero_le _)
    let U := D * (L a + 1)
    have hm₁ (c : ℕ) (hc : c ≤ D) (n : ℕ) (hn : n ≤ L a) : c * (n + 1) ≤ U :=
      Nat.mul_le_mul hc (Nat.add_le_add_right hn 1)
    have hm₂ (c : ℕ) (hc : c ≤ D) (n : ℕ) (hn : n ≤ L a) : c * (2 * n + 2) ≤ 2 * U := by
      have := hm₁ c hc n hn
      dsimp [U] at *
      nlinarith
    have hsmall : m + 100 + L a ≤ U := by dsimp [U]; nlinarith only [hD]
    have hlarge : 100 * (L a + 1) + m ≤ U := by dsimp [U]; nlinarith only [hD]
    let T := (∑ j ∈ Finset.range (enc a).length,
        (cN * (TN (q j, (enc a).getD j false) + 1) + (2 * cE + 2))) +
      (2 * cPE + 2) + cPN b * (TPN b (q (enc a).length) + 1) + cC * (TC q' + 1)
    have hT (j : ℕ) (hj : j < (enc a).length) :
        cN * (TN (q j, (enc a)[j]) + 1) + (2 * cE + 2) ≤ T := by
      rw [← List.getD_eq_getElem _ false hj]
      exact (Finset.single_le_sum
        (f := fun j => cN * (TN (q j, (enc a).getD j false) + 1) + (2 * cE + 2))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)).trans
        (by omega)
    have hTe : (2 * cPE + 2) + cPN b * (TPN b (q (enc a).length) + 1) +
        cC * (TC q' + 1) ≤ T := by omega
    have hloop := transformsTapesAt_streamLoop_encoded
      (⟨(), fun _ bit => (none, some bit)⟩ : InputReader Bool Unit)
      (fun bit => [bit]) (fun _ => List.cons_ne_nil _ _)
      (fun bit rest => by simp [InputReader.read]) hVN hVW hNW
      ((s, 0, none) : PassState σ) (enc a) (passNext (M.withChoice false))
      (fun _ => ([] : List Bool)) hE₀ hN₀
      (roundCost := fun _ => 2 * T + 4 * U)
      (sMax := 10 * U + 3 * U + 16 * L a + 7 * (m + 4) + 40) (lMax := L a)
      (by
        intro j hj
        have ht := hT j hj
        have h₀ := hq j hj.le
        have h₁ := hq (j + 1) hj
        have hmfr := hm₁ cfr (by dsimp [D]; omega) _ h₁
        have hmN := hm₁ cN' (by dsimp [D]; omega) _ h₁
        dsimp only [q] at ht h₀ h₁ hmfr hmN
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame,
          ← streamState_succ ((s, 0, none) : PassState σ) _ _ hj,
          encBool_apply, List.length_singleton]
        omega)
      (by
        intro j hj
        have h₀ := hq j hj.le
        have h₁ := hq (j + 1) hj
        have hmfr := hm₁ cfr (by dsimp [D]; omega) _ h₁
        have hmN := hm₁ cN' (by dsimp [D]; omega) _ h₁
        have hn := Nat.mul_le_mul (show cN ≤ D by dsimp [D]; omega)
          (show (encPair (encPass encS) encBool (q j, (enc a)[j])).length + 1 ≤
            4 * (L a + 1) by
              simp only [length_encPair, encBool_apply, List.length_singleton] at h₀ ⊢
              omega)
        dsimp only [q] at h₀ h₁ hmfr hmN hn
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame,
          ← streamState_succ ((s, 0, none) : PassState σ) _ _ hj,
          length_encPair, encBool_apply, List.length_singleton] at h₀ h₁ hmfr hmN hn ⊢
        have hkE : kE ≤ m := by dsimp [m]; omega
        have hkN : kN ≤ m := by dsimp [m]; omega
        change _ ≤ D * (4 * (L a + 1)) at hn
        have hnu : D * (4 * (L a + 1)) = 4 * U := by dsimp [U]; ring
        rw [hnu] at hn
        omega)
      hq (fun _ _ => by simp only [encBool_apply, List.length_singleton]; exact hL1 a)
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hloop
    have hbits (l : List Bool) : l.flatMap (fun b => [b]) = l := by
      induction l with
      | nil => rfl
      | cons b l ih =>
        simpa only [List.flatMap_cons, List.singleton_append] using congrArg (b :: ·) ih
    simp only [hbits] at hloop
    have hloop' := hloop.imp (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ h => h) le_rfl
      (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * (m + 4))
        (show 10 * U + 3 * U + 16 * L a + 7 * (m + 4) + 40 +
          16 * L a + 4 * (m + 4) + 26 ≤ 100 * U by omega)) _)
    have hEe : ∃ t, TransformsTapes ((tmPE.inputFromWord true).extendTapes ePE)
        (fun _ ws => ws = Function.update (fun _ => []) V (frame (encPass encS (q (enc a).length))))
        (fun _ ws ws' em => ws' = ws ∧ em = []) t (10 * U + 4 * L a + 3 * (m + 4) + 12) := by
      refine ⟨_, (hPE₀ (q (enc a).length)).imp (fun _ _ h => h)
        (fun _ _ _ _ _ h => h) le_rfl ?_⟩
      have hu := hm₂ cuf (by dsimp [D]; omega) _ (hq _ le_rfl)
      have hp := hm₁ cPE' (by dsimp [D]; omega) _ (hq _ le_rfl)
      simp only [id_eq, encFramed_apply, length_frame]
      have hkPE : kPE ≤ m := by dsimp [m]; omega
      have hqn := hq (enc a).length le_rfl
      nlinarith only [hu, hp, hqn, hsmall, hkPE, Nat.sub_le (m + 4) (kPE + 2)]
    have hNe : ∃ t, TransformsTapes (((tmPN b).onWords true).extendTapes (ePN b))
        (fun _ ws => ws = Function.update (fun _ => []) V (frame (encPass encS (q (enc a).length))))
        (fun _ ws ws' em => ws' = Function.update ws N (frame (encPass encS q')) ∧ em = [])
        t (30 * U + 4 * (m + 4) + 20) := by
      refine ⟨_, (hPN₀ b (q (enc a).length)).imp (fun _ _ h => h)
        (fun _ _ _ _ _ h => by
          simpa only [Function.comp_apply, id_eq, encFramed_apply, hend] using h)
        le_rfl ?_⟩
      have hu := hm₂ cuf (by dsimp [D]; omega) _ (hq _ le_rfl)
      have hp := hm₁ (cPN b) (hcPN b) _ (hq _ le_rfl)
      have hp₁ := hm₁ (cPN₁ b) (hcPN₁ b) _ (hq _ le_rfl)
      have hfr := hm₁ cfr (by dsimp [D]; omega) _ hq'
      have hp' := hm₁ (cPN' b) (hcPN' b) _ hq'
      simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, hend]
      have hkPN : kPN b ≤ m := by cases b <;> dsimp [m] <;> omega
      have hqn := hq (enc a).length le_rfl
      nlinarith only [hu, hp, hp₁, hfr, hp', hqn, hq', hsmall, hkPN,
        Nat.sub_le (m + 4) (kPN b + 1 + 2)]
    have hCm : ∃ t, TransformsTapes ((tmC.onWords true).extendTapes eC)
        (fun _ ws => ws = Function.update (fun _ => []) V (frame (encPass encS q')))
        (fun _ ws ws' em => ws' = Function.update ws C (flagWord (!M.halted s')) ∧ em = [])
        t (30 * U + 4 * (m + 4) + 20) := by
      refine ⟨_, (hC₀ q').imp (fun _ _ h => h) (fun _ _ _ _ _ h => h) le_rfl ?_⟩
      have hu := hm₂ cuf (by dsimp [D]; omega) _ hq'
      have hc := hm₁ cC (by dsimp [D]; omega) _ hq'
      have hc₁ := hm₁ cC₁ (by dsimp [D]; omega) _ hq'
      have hf : 2 * cfl ≤ 2 * U := by
        have hcfl : cfl ≤ D := by dsimp [D]; omega
        dsimp [U]
        nlinarith only [hcfl]
      have hc' : 2 * cC' ≤ 2 * U := by
        have hcc : cC' ≤ D := by dsimp [D]; omega
        dsimp [U]
        nlinarith only [hcc]
      simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame,
        encBool_apply, List.length_singleton]
      have hflag : (flagWord (!M.halted s')).length ≤ 1 := by
        cases M.halted s' <;> simp [flagWord]
      have hkC : kC ≤ m := by dsimp [m]; omega
      have hflag' : (encBits (flagWord (passCont (M.withChoice false) q'))).length ≤ 1 := hflag
      nlinarith only [hu, hc, hc₁, hf, hc', hflag', hq', hsmall, hkC,
        Nat.sub_le (m + 4) (kC + 1 + 2)]
    obtain ⟨tEe, hEe⟩ := hEe
    obtain ⟨tNe, hNe⟩ := hNe
    obtain ⟨tCm, hCm⟩ := hCm
    have h := transformsTapes_passTM hVN hVW hNW hVC (enc a)
      (frame (encPass encS ((s, 0, none) : PassState σ)))
      (frame (encPass encS (q (enc a).length))) [] []
      (frame (encPass encS q')) (flagWord flag) (flagWord (!M.halted s'))
      (by simpa only [streamEmit_const_nil] using hloop') hEe hNe hCm
    refine ⟨_, h.imp (fun _ _ h => h) (fun _ _ _ _ _ h => by simpa only [List.nil_append] using h)
      le_rfl ?_⟩
    have hflag : (flagWord flag).length ≤ 1 := by cases flag <;> simp [flagWord]
    have hlen := hq (enc a).length le_rfl
    simp only [length_frame]
    refine le_trans (b := 1000 * (m + 5) * U) ?_ (hG a)
    have hU1 : 1 ≤ U := by omega
    have hkU : m + 4 ≤ U := by omega
    have hmul := Nat.mul_le_mul_left (2 * (m + 4)) (show 100 * U ≤ 100 * U by rfl)
    nlinarith only [hflag, hlen, hq', hsmall, hU1, hkU]
  · intro a s hs flag
    let v := frame (encPass encS ((s, 0, none) : PassState σ))
    let U := D * (L a + 1)
    have hlen := hscan a s hs false 0 (Nat.zero_le _)
    simp only [streamState_zero] at hlen
    have hclear := (transformsTapes_clearWork_tapeEmb C (flagWord flag)).imp
      (P' := fun inp ws => inp = enc a ∧ ws = B s flag)
      (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) V v ∧ e = [])
      (fun _ _ ⟨_, h⟩ => by simp [h, B, passTapes])
      (fun _ _ _ _ ⟨_, hw⟩ ⟨hw', he⟩ => ⟨by
        rw [hw', hw]
        rw [show Function.update (B s flag) C [] = passTapes V C v [] by
          simp only [B, passTapes, Function.update_idem, v]]
        exact blankBoundary hVC v, he⟩)
      le_rfl le_rfl
    have hfinish := (hF₀ ((s, 0, none) : PassState σ)).imp
      (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) V v ∧ e = [M.accept s])
      (fun _ _ h => h) (fun _ _ _ _ hw ⟨hw', he⟩ => ⟨hw'.trans hw, he⟩) le_rfl le_rfl
    refine ⟨_, (hclear.seq_eq hfinish).imp (fun _ _ h => h)
      (fun _ _ _ _ _ h => by simpa using h.2) le_rfl ?_⟩
    have hm₁ := Nat.mul_le_mul (show cuf ≤ D by dsimp [D]; omega)
      (show 2 * (encPass encS (s, 0, none)).length + 2 ≤ 2 * (L a + 1) by omega)
    have hm₂ := Nat.mul_le_mul (show cF ≤ D by dsimp [D]; omega) (Nat.add_le_add_right hlen 1)
    have hm₃ := Nat.mul_le_mul (show cF' ≤ D by dsimp [D]; omega) (Nat.add_le_add_right hlen 1)
    have hflag : (flagWord flag).length ≤ 1 := by cases flag <;> simp [flagWord]
    have hsmall : m + 100 + L a ≤ U := by dsimp [U]; nlinarith only [hD]
    have hlarge : 100 * (L a + 1) + m ≤ U := by dsimp [U]; nlinarith only [hD]
    refine le_trans (b := 20 * U) ?_
      ((Nat.mul_le_mul_right _ (by omega : 20 ≤ 1000 * (m + 5))).trans (hG a))
    simp only [id_eq, encFramed_apply, length_frame]
    have hkF : kF ≤ m := by dsimp [m]; omega
    change (flagWord flag).length + 1 + (m + 4) +
      (cuf * (2 * (encPass encS (s, 0, none)).length + 1 + 1) +
        cF * ((encPass encS (s, 0, none)).length + 1) +
        cF' * ((encPass encS (s, 0, none)).length + 1) +
        2 * (2 * (encPass encS (s, 0, none)).length + 1 + 2) +
        2 * kF + 8 + (m + 4 - (kF + 2))) ≤ _
    dsimp only [U] at hsmall ⊢
    nlinarith only [hm₁, hm₂, hm₃, hflag, hlen, hsmall, hkF, Nat.sub_le (m + 4) (kF + 2)]

end Turing.NondeterministicQueryMachine
