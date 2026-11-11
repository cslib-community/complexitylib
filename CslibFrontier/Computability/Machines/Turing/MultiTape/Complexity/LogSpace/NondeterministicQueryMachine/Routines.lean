/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.NondeterministicQueryMachine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.SpaceNormalForm
import Mathlib.Data.List.GetD

/-!
# Framed native routines for nondeterministic query machines

The abstract state is framed on a work tape. The initializer writes the start state of the input,
which may depend on the input. Each deterministic pass reads the input in place, performs one
selected transition, and writes the continuation flag. Only the finalizer emits.

## Main definitions

* `Turing.NondeterministicQueryMachine.Routines`: finite native routines and their specifications.

## Main results

* `Turing.NondeterministicQueryMachine.exists_routines`: constructs the routines from local
  linear-space computability and a start state computable in space `O(S)`, with one space bound
  for all reachable boundary states.
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

private theorem le_of_add_le8 {a₁ a₂ a₃ a₄ a₅ a₆ a₇ : ℕ} {m : ℕ}
    (h : a₁ + a₂ + a₃ + a₄ + a₅ + a₆ + a₇ ≤ m) :
    a₁ ≤ m ∧ a₂ ≤ m ∧ a₃ ≤ m ∧ a₄ ≤ m ∧ a₅ ≤ m ∧ a₆ ≤ m ∧ a₇ ≤ m := by
  omega

private theorem mul_le_of_add_le14
    {c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ D L U n : ℕ}
    (hD : c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + c₇ + c₈ + c₉ + c₁₀ + c₁₁ + c₁₂ + c₁₃ + c₁₄ ≤ D)
    (hU : D * (L + 1) ≤ U) (hn : n ≤ L) :
    c₁ * (n + 1) ≤ U ∧ c₂ * (2 * n + 1 + 1) ≤ 2 * U ∧ c₃ * (n + 1) ≤ U ∧
    c₄ * (n + 1) ≤ U ∧ c₅ * (n + 1) ≤ U ∧ c₆ * (n + 1) ≤ U ∧
    c₇ * (n + 1) ≤ U ∧ c₈ * (n + 1) ≤ U ∧ c₉ * (n + 1) ≤ U ∧
    c₁₀ * (n + 1) ≤ U ∧ c₁₁ * (n + 1) ≤ U ∧ c₁₂ * (n + 1) ≤ U ∧
    c₁₃ * (n + 1) ≤ U ∧ c₁₄ * (n + 1) ≤ U := by
  have hm {c : ℕ} (hc : c ≤ D) : c * (n + 1) ≤ U :=
    (Nat.mul_le_mul hc (Nat.add_le_add_right hn 1)).trans hU
  have hm2 {c : ℕ} (hc : c ≤ D) : c * (2 * n + 1 + 1) ≤ 2 * U := by
    rw [show c * (2 * n + 1 + 1) = 2 * (c * (n + 1)) by ring]
    exact Nat.mul_le_mul_left 2 (hm hc)
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ :
      c₁ ≤ D ∧ c₂ ≤ D ∧ c₃ ≤ D ∧ c₄ ≤ D ∧ c₅ ≤ D ∧ c₆ ≤ D ∧ c₇ ≤ D ∧
      c₈ ≤ D ∧ c₉ ≤ D ∧ c₁₀ ≤ D ∧ c₁₁ ≤ D ∧ c₁₂ ≤ D ∧ c₁₃ ≤ D ∧ c₁₄ ≤ D := by omega
  exact ⟨hm h₁, hm2 h₂, hm h₃, hm h₄, hm h₅, hm h₆, hm h₇, hm h₈, hm h₉, hm h₁₀,
    hm h₁₁, hm h₁₂, hm h₁₃, hm h₁₄⟩

/-- Concrete finite routines, sharing tape origins and a common linear space budget. On the input
`enc a` the abstract run starts in `start a`; the passes and the finalizer do not depend on `a`. -/
structure Routines {α σ : Type} (M : NondeterministicQueryMachine σ) (start : α → σ)
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
    (fun _ _ ws' e => ws' = boundary (start a) false ∧ e = []) t (c * S a)
  pass_spec : ∀ a s, (M.withInit (start a)).Reachable (enc a) s → ∀ choice flag, ∃ t,
    TransformsTapes (P choice)
    (fun inp ws => inp = enc a ∧ ws = boundary s flag)
    (fun _ _ ws' e => ws' = boundary (M.step (enc a) s choice)
      (!M.halted (M.step (enc a) s choice)) ∧ e = []) t (c * S a)
  final_spec : ∀ a s, (M.withInit (start a)).Reachable (enc a) s → ∀ flag, ∃ t,
    TransformsTapes F
    (fun inp ws => inp = enc a ∧ ws = boundary s flag)
    (fun _ _ _ e => e = [M.accept s]) t (c * S a)

/-- Compile local query-machine callbacks and a start state computable in space `O(S)` into
concrete finite native routines. -/
theorem exists_routines {α σ : Type} {enc : α ↪ List Bool} {encS : σ ↪ List Bool}
    (M : NondeterministicQueryMachine σ)
    (hquery : ComputableInSpace M.query encS encNat fun s => (encS s).length)
    (hnext : ComputableInSpace M.next
      (encPair encS (encPair (encOption encBool) encBool)) encS
      fun p => (encPair encS (encPair (encOption encBool) encBool) p).length)
    (hhalted : ComputableInSpace M.halted encS encBool fun s => (encS s).length)
    (haccept : ComputableInSpace M.accept encS encBool fun s => (encS s).length)
    (start : α → σ) (S : α → ℕ) (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hstart : ComputableInSpace start enc encS S)
    (hsize : ∃ c, ∀ a choices,
      (encS ((M.withInit (start a)).run (enc a) choices)).length ≤ c * S a) :
    Nonempty (Routines M start enc S) := by
  classical
  obtain ⟨cS, hS⟩ := hsize
  have hS1 (a : α) : 1 ≤ S a := (Nat.le_add_left _ _).trans (hlog a)
  have hreach (a : α) (s : σ) (hs : (M.withInit (start a)).Reachable (enc a) s) :
      (encS s).length ≤ cS * S a := by
    obtain ⟨coins, rfl⟩ := hs
    exact hS a coins
  have hstart' : ComputableInSpace (fun a => ((start a, 0, none) : PassState σ)) enc
      (encPass encS) S :=
    (hstart.prod ((ComputableInSpace.constZero 0).prod (ComputableInSpace.constZero none))).mono_le
      fun _ => le_rfl
  obtain ⟨TI, cI, hI, -⟩ := Internal.NormalForm.space hstart'
  obtain ⟨cE, hE⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair (encPass encS) encBool) (encOut := encBits) ([] : List Bool)
  obtain ⟨cPE, hPE⟩ := computableInTimeAndSpace_of_const
    (encIn := encPass encS) (encOut := encBits) ([] : List Bool)
  obtain ⟨TN, cN, hN, -⟩ := Internal.NormalForm.space (passNext_inSpace hquery false)
  have hpns (b : Bool) := Internal.NormalForm.space (passEnd_inSpace hnext hhalted b)
  choose TPN cPN hPN hlenPN using hpns
  obtain ⟨TC, cC, hC, -⟩ := Internal.NormalForm.space (passCont_inSpace hhalted false)
  obtain ⟨TF, cF, hF, -⟩ := Internal.NormalForm.space (passFinish_inSpace haccept false)
  obtain ⟨cfr, hfr⟩ := ComputableTidilyInLinearTimeAndSpace.of_frame (f := id)
    (encIn := encPass encS) (encOut := encFramed (encPass encS)) fun _ => rfl
  obtain ⟨cuf, huf⟩ := ComputableTidilyInLinearTimeAndSpace.of_unframe (f := id)
    (encIn := encFramed (encPass encS)) (encOut := encPass encS) fun s => by simp
  obtain ⟨cfl, hfl⟩ := linearFlag
  obtain ⟨cI', hI'⟩ := ComputableTidilyInTimeAndSpace.comp_linear hfr hI
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
  obtain ⟨m, hm⟩ : ∃ m, m = kI + kE + kN + kF + kPE + kPN false + kPN true + kC + 8 := ⟨_, rfl⟩
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
    apply exists_embedding_eq₂ (by cases b <;> omega)
      (by simp [Fin.ext_iff]) hVN
  choose ePN hePN hePN' using hepn
  obtain ⟨eC, heC, heC'⟩ := exists_embedding_eq₂ (K := m + 4) (by omega)
    (i := Fin.natAdd (kC + 1) (0 : Fin 2)) (o := (Fin.last kC).castAdd 2)
    (by simp [Fin.ext_iff]) hVC
  have hk (b : Bool) :=
    le_of_add_le8 (by cases b <;> omega : kI + kE + kN + kF + kPE + kPN b + kC ≤ m)
  clear hm
  have hI₀ := fun a => (htmI a).outputToWord_onTape heI
  have hE₀ := fun a => (htmE a).inputFromWord_extendTapes true heE
  have hN₀ := fun a => (htmN a).onWords_extendTapes true heN heN'
  have hF₀ := fun a => (htmF a).inputFromWord_extendTapes true heF
  have hPE₀ := fun a => (htmPE a).inputFromWord_extendTapes true hePE
  have hPN₀ := fun b a => (htmPN b a).onWords_extendTapes true (hePN b) (hePN' b)
  have hC₀ := fun a => (htmC a).onWords_extendTapes true heC heC'
  clear hquery hnext hhalted haccept hI hE hPE hN hPN hlenPN hC hF hfr huf hfl
    hPN₁ hC₁ htmI htmE htmN htmF htmPE htmPN htmC
    heI heE heN heN' heF hePE hePN hePN' heC heC'
  obtain ⟨D, hD_eq⟩ : ∃ D, D = cfr + cuf + cfl + cI + cE + cPE + cN + cF + cC + cI' + cN' +
    cF' + cPE' + cPN false + cPN true + cPN₁ false + cPN₁ true + cPN' false + cPN' true +
    cC₁ + cC' + m + 100 := ⟨_, rfl⟩
  have hcN : cN ≤ D := by omega
  have hcI : cI ≤ D := by omega
  have hD : m + 100 ≤ D := by omega
  have hcD (b : Bool) :
      cfr + cuf + cfl + cF + cC + cI' + cN' + cF' + cPE' + cPN b + cPN₁ b + cPN' b + cC₁ + cC' ≤
        D := by cases b <;> omega
  clear hD_eq
  obtain ⟨L, hL_eq⟩ : ∃ L : α → ℕ, ∀ a, L a = (2 * cS + 7) * S a := ⟨_, fun _ => rfl⟩
  have hL1 (a : α) : 1 ≤ L a := by rw [hL_eq]; exact Nat.mul_pos (by omega) (hS1 a)
  have hSL (a : α) : S a ≤ L a := by rw [hL_eq]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hscan (a : α) (s : σ) (hs : (M.withInit (start a)).Reachable (enc a) s) (b : Bool)
      (j : ℕ) (hj : j ≤ (enc a).length) :
      (encPass encS (streamState ((s, 0, none) : PassState σ)
        (passNext (M.withChoice b)) (enc a) j)).length ≤ L a := by
    rw [hL_eq, QueryMachine.Simulation.streamState_passNext _ _ _ hj]
    exact (length_passState_le (enc a) (hreach a s hs) (hlog a) hj _).trans
      (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨U, hU_eq⟩ : ∃ U : α → ℕ, ∀ a, U a = D * (L a + 1) := ⟨_, fun _ => rfl⟩
  have hU_bounds {a : α} {n : ℕ} (hn : n ≤ L a) (b : Bool) :=
    mul_le_of_add_le14 (hcD b) (le_of_eq (hU_eq a).symm) hn
  have hcIU (a : α) : cI * (S a + 1) ≤ U a :=
    (Nat.mul_le_mul hcI (Nat.add_le_add_right (hSL a) 1)).trans (le_of_eq (hU_eq a).symm)
  have hm₄ {a : α} {n : ℕ} (hn : n + 1 ≤ 4 * (L a + 1)) : cN * (n + 1) ≤ 4 * U a :=
    (Nat.mul_le_mul hcN hn).trans (le_of_eq (by rw [hU_eq]; ring))
  have hlarge (a : α) : 100 * (L a + 1) + m ≤ U a := by
    rw [hU_eq]
    calc 100 * (L a + 1) + m ≤ 100 * (L a + 1) + m * (L a + 1) :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_right m (by omega)) _
      _ = (m + 100) * (L a + 1) := by ring
      _ ≤ D * (L a + 1) := Nat.mul_le_mul_right (L a + 1) hD
  have hsmall (a : α) : m + 100 + L a ≤ U a := by have := hlarge a; omega
  obtain ⟨G, hG_eq⟩ : ∃ G, G = 1000 * (m + 5) * D * (2 * cS + 8) := ⟨_, rfl⟩
  have hG (a : α) {k : ℕ} (hk_le : k ≤ 1000 * (m + 5)) : k * U a ≤ G * S a := by
    have hLin : L a + 1 ≤ (2 * cS + 8) * S a := by
      rw [hL_eq]
      calc (2 * cS + 7) * S a + 1 ≤ (2 * cS + 7) * S a + S a := Nat.add_le_add_left (hS1 a) _
        _ = (2 * cS + 8) * S a := by ring
    rw [hU_eq, hG_eq]
    calc k * (D * (L a + 1)) ≤ 1000 * (m + 5) * (D * ((2 * cS + 8) * S a)) := by gcongr
      _ = 1000 * (m + 5) * D * (2 * cS + 8) * S a := by ring
  clear hcN hcI hD hcD hL_eq hU_eq hG_eq hSL
  have hflag (x : Bool) : (flagWord x).length ≤ 1 := by cases x <;> simp [flagWord]
  let B (s : σ) (flag : Bool) := passTapes V C
    (frame (encPass encS ((s, 0, none) : PassState σ))) (flagWord flag)
  refine ⟨{ k := m + 4
            SI := _
            SP := fun b => _
            SF := _
            finiteI := inferInstance
            finiteP := fun b => by
              set_option synthInstance.maxSize 1024 in infer_instance
            finiteF := inferInstance
            I := tmI.outputToWord.extendTapes eI
            P := fun b => passTM
              (⟨(), fun _ bit => (none, some bit)⟩ : InputReader Bool Unit)
              ((tmE.inputFromWord true).extendTapes eE) ((tmN.onWords true).extendTapes eN)
              ((tmPE.inputFromWord true).extendTapes ePE)
              (((tmPN b).onWords true).extendTapes (ePN b))
              ((tmC.onWords true).extendTapes eC) V N W C hVN hVW hNW
            F := ((clearWork Bool).extendTapes (tapeEmb C)).seq
              ((tmF.inputFromWord true).extendTapes eF)
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
    exact congrArg Prod.fst ((encPass encS).injective (frame_injective hv))
  · intro a
    have hlen := hscan a (start a) ((M.withInit (start a)).reachable_init _) false 0
      (Nat.zero_le _)
    simp only [streamState_zero] at hlen
    refine ⟨_, (hI₀ a).imp (fun _ _ h => h)
      (fun _ _ _ _ _ ⟨hw, he⟩ => ⟨by simpa [B, flagWord, passTapes_nil hVC] using hw, he⟩)
      le_rfl (le_trans ?_ (hG a (k := 10) (by omega)))⟩
    have := hU_bounds hlen false
    have := hsmall a
    have := hk false
    have := hcIU a
    simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame]
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
      hscan a s' (Reachable.step _ (enc a) hs b) false 0 (Nat.zero_le _)
    have hqn := hq (enc a).length le_rfl
    have hsm := hsmall a
    have hlg := hlarge a
    have hkb := hk b
    obtain ⟨T, hT_eq⟩ : ∃ T, T = (∑ j ∈ Finset.range (enc a).length,
        (cN * (TN (q j, (enc a).getD j false) + 1) + (2 * cE + 2))) +
      (2 * cPE + 2) + cPN b * (TPN b (q (enc a).length) + 1) + cC * (TC q' + 1) := ⟨_, rfl⟩
    have hT (j : ℕ) (hj : j < (enc a).length) :
        cN * (TN (q j, (enc a)[j]) + 1) + (2 * cE + 2) ≤ T := by
      rw [hT_eq, ← List.getD_eq_getElem _ false hj]
      exact (Finset.single_le_sum
        (f := fun j => cN * (TN (q j, (enc a).getD j false) + 1) + (2 * cE + 2))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)).trans (by omega)
    clear hT_eq
    have hloop := transformsTapesAt_streamLoop_encoded
      (⟨(), fun _ bit => (none, some bit)⟩ : InputReader Bool Unit)
      (fun bit => [bit]) (fun _ => List.cons_ne_nil _ _)
      (fun bit rest => by simp [InputReader.read]) hVN hVW hNW
      ((s, 0, none) : PassState σ) (enc a) (passNext (M.withChoice false))
      (fun _ => ([] : List Bool)) hE₀ hN₀
      (roundCost := fun _ => 2 * T + 4 * U a)
      (sMax := 10 * U a + 3 * U a + 16 * L a + 7 * (m + 4) + 40) (lMax := L a)
      (by
        intro j hj
        have ht := hT j hj
        have h₀ := hq j hj.le
        have h₁ := hq (j + 1) hj
        have hu := hU_bounds h₁ false
        dsimp only [q] at ht h₀ h₁ hu
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame,
          ← streamState_succ ((s, 0, none) : PassState σ) _ _ hj,
          encBool_apply, List.length_singleton]
        omega)
      (by
        intro j hj
        have h₀ := hq j hj.le
        have h₁ := hq (j + 1) hj
        have hu := hU_bounds h₁ false
        have hn := hm₄ (show (encPair (encPass encS) encBool (q j, (enc a)[j])).length + 1 ≤
          4 * (L a + 1) by
            simp only [length_encPair, encBool_apply, List.length_singleton] at h₀ ⊢; omega)
        dsimp only [q] at h₀ h₁ hu hn
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame,
          ← streamState_succ ((s, 0, none) : PassState σ) _ _ hj,
          length_encPair, encBool_apply, List.length_singleton] at h₀ h₁ hu hn ⊢
        omega)
      hq (fun _ _ => by simp only [encBool_apply, List.length_singleton]; exact hL1 a)
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.flatMap_singleton'] at hloop
    have hloop' := hloop.imp (fun _ _ _ h => h) (fun _ _ _ _ _ _ _ h => h) le_rfl
      (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * (m + 4)) (by omega : _ ≤ 100 * U a)) _)
    have hEe := (hPE₀ (q (enc a).length)).imp (fun _ _ h => h) (fun _ _ _ _ _ h => h) le_rfl
      (show _ ≤ 10 * U a + 4 * L a + 3 * (m + 4) + 12 by
        have := hU_bounds hqn b
        simp only [id_eq, encFramed_apply, length_frame]; omega)
    have hNe := (hPN₀ b (q (enc a).length)).imp (fun _ _ h => h)
      (fun _ _ _ _ _ h => by
        simpa only [Function.comp_apply, id_eq, encFramed_apply, hend] using h) le_rfl
      (show _ ≤ 30 * U a + 4 * (m + 4) + 20 by
        have := hU_bounds hqn b; have := hU_bounds hq' b
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame, hend]; omega)
    have hCm := (hC₀ q').imp (fun _ _ h => h) (fun _ _ _ _ _ h => h) le_rfl
      (show _ ≤ 30 * U a + 4 * (m + 4) + 20 by
        have := hU_bounds hq' b; have := hU_bounds (hL1 a) b
        have : (encBits (flagWord (passCont (M.withChoice false) q'))).length ≤ 1 := hflag _
        simp only [Function.comp_apply, id_eq, encFramed_apply, length_frame,
          encBool_apply, List.length_singleton]; omega)
    have h := transformsTapes_passTM hVN hVW hNW hVC (enc a)
      (frame (encPass encS ((s, 0, none) : PassState σ)))
      (frame (encPass encS (q (enc a).length))) [] []
      (frame (encPass encS q')) (flagWord flag) (flagWord (!M.halted s'))
      (by simpa only [streamEmit_const_nil] using hloop') hEe hNe hCm
    refine ⟨_, h.imp (fun _ _ h => h) (fun _ _ _ _ _ h => by simpa only [List.nil_append] using h)
      le_rfl (le_trans ?_ (hG a le_rfl))⟩
    have := hflag flag
    have hMU : 2 * (m + 4) * (100 * U a) + 200 * U a ≤ 1000 * (m + 5) * U a := by
      rw [show 2 * (m + 4) * (100 * U a) + 200 * U a = (200 * m + 1000) * U a by ring]
      exact Nat.mul_le_mul_right _ (by omega)
    simp only [length_frame]
    omega
  · intro a s hs flag
    let v := frame (encPass encS ((s, 0, none) : PassState σ))
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
        exact passTapes_nil hVC v, he⟩)
      le_rfl le_rfl
    have hfinish := (hF₀ ((s, 0, none) : PassState σ)).imp
      (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) V v ∧ e = [M.accept s])
      (fun _ _ h => h) (fun _ _ _ _ hw ⟨hw', he⟩ => ⟨hw'.trans hw, he⟩) le_rfl le_rfl
    refine ⟨_, (hclear.seq_eq hfinish).imp (fun _ _ h => h)
      (fun _ _ _ _ _ h => by simpa using h.2) le_rfl
      (le_trans ?_ (hG a (k := 20) (by omega)))⟩
    have := hU_bounds hlen false
    have := hflag flag
    have := hsmall a
    have := hk false
    simp only [id_eq, encFramed_apply, length_frame]
    omega

end Turing.NondeterministicQueryMachine
