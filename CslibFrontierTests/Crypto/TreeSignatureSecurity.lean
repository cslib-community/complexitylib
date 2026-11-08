/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.TreeSignature.Security
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Tests for stateless tree signature security

Behavioral and nonvacuity checks for `CslibFrontier.Crypto.Computational.TreeSignature.Security` and
the `n`-bit message-domain guard of `TreeSignature.sign`:

1. **Off-domain signing guard**: `TreeSignature.sign` returns `pure []` whenever `msg.length ≠ n`
   (preventing off-domain signing queries from leaking `n`-bit node public-key certificates), while
   every supported signature on an `n`-bit message is non-empty and verifies.
2. **Concrete forgery extraction (`extractForgery`)**: on a depth-`3` visited cache
   `[([true, false], 2), ([true], 1), ([], 0)]`, a path diverging at depth `1` (`[true, true, …]`)
   extracts the internal child-key forgery `(1, pk₂', σ₁')` at slot `1` (and the depth-`0`
   certificate `(1, pk₁, σ₀)` at root slot `0`), while a fresh message along `[true, false, false]`
   extracts the leaf-parent forgery `(0, msgStar, σLeaf)` at slot `2`.
3. **Leaf-collision abort vs. reduction nonvacuity**: at depth `1` (`2` leaves), any `3`-query
   forger triggers a leaf collision (`bad = true`, reply `[]`) by pigeonhole on `Bool`, giving exact
   success probability `0` when using the 3rd reply in `lazyTreeGame`. Conversely, a `0`-query
   forger against an insecure toy indexed scheme `echo` wins `lazyTreeGame` with exact probability
   `1`, and `succProbability_lazyTreeGame_le` forces `indexedForger` to win `echo.indexedEufCmaGame`
   with probability at least `1 / 2`.
4. **Asymptotic upgrades**: concrete instantiations of `negligible_inv_two_pow_of_le`,
   `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_prf`,
   `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay`, and
   `OneWay.exists_eufCMA_of_hashFamily`.
-/

namespace ComplexityTests.Crypto.TreeSignatureSecurity

open Cslib Cslib.Crypto Cslib.Crypto.TreeSignature Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ### Toy deterministic indexed scheme -/

/-- A toy indexed scheme with empty keys whose signatures are the encoded `(u, msg)` pairs. -/
noncomputable def echo : IndexedSignatureScheme where
  capacity _ := 2
  keyGen _ := pure ([], [])
  sign _ u msg := pure (encPair encUnary encBits (u, msg))
  verify _ u msg sig := sig == encPair encUnary encBits (u, msg)
  capacity_polyTime := ComputableInPolyTime.const 2
  keyGen_ppt := (ComputableInPolyTime.const ([], [])).isPPTOn
  sign_ppt := by
    apply ComputableInPolyTime.isPPTOn
    polytime
  verify_polyTime := by polytime
  verify_sign _ _ _ _ _ _ sig hsig := by
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsig
    simp [hsig]

/-- Seeded interface for `echo` requiring `0` coin bits. -/
noncomputable def echoSeeded : echo.Seeded where
  keyGenWith _ _ := ([], [])
  keyGenBudget _ := 0
  signWith _ u msg _ := encPair encUnary encBits (u, msg)
  signBudget _ _ _ := 0
  keyGenWith_polyTime := ComputableInPolyTime.const ([], [])
  keyGenBudget_polyTime := ComputableInPolyTime.const 0
  keyGenWith_mem_support _ _ := by simp [echo]
  eval_keyGen _ _ _ := by
    simp only [echo, ProbComp.eval_pure]
    exact (PMF.map_const (BitString.uniformList _) ([], [])).symm
  signWith_polyTime := by polytime
  signBudget_polyTime := ComputableInPolyTime.const 0
  signWith_mem_support _ _ _ _ := by simp [echo]
  eval_sign _ _ _ _ _ := by
    simp only [echo, ProbComp.eval_pure]
    exact (PMF.map_const (BitString.uniformList _) _).symm

/-- Constant all-`false` coin generator. -/
def zeroCoins (_ _ : List Bool) (L : ℕ) : List Bool := List.replicate L false

theorem computableInPolyTime_zeroCoins :
    ComputableInPolyTime (fun ((k, inp, L) : List Bool × List Bool × ℕ) => zeroCoins k inp L)
      (encPair encBits (encPair encBits encUnary)) encBits := by
  unfold zeroCoins
  polytime

/-- Packaged stateless tree scheme over `echo` at depth `n + 1`. -/
noncomputable abbrev echoTree : SignatureScheme :=
  scheme echo echoSeeded zeroCoins id (· + 1) computableInPolyTime_zeroCoins
    ComputableInPolyTime.id' (by polytime) (fun _ => le_rfl) (fun _ => Nat.succ_pos _)

/-! ### 1. Off-domain signing guard (`msg.length = n`) -/

def sk2 : List Bool := encPair encUnary encBits (2, [true, false])
def pk2 : List Bool := encPair encUnary encBits (2, [])

-- Short (`1 ≠ 2`) and long (`3 ≠ 2`) messages are refused with `pure []` without certifying nodes.
example : echoTree.sign sk2 [true] = pure [] := by
  simp only [echoTree, scheme, sign, sk2, keyDecoder.decode_enc]
  simp

example : echoTree.sign sk2 [true, false, true] = pure [] := by
  simp only [echoTree, scheme, sign, sk2, keyDecoder.decode_enc]
  simp

-- Every supported signature on a `2`-bit message is non-empty and verifies under `pk2`.
example (sig : List Bool) (hsig : sig ∈ (ProbComp.eval (echoTree.sign sk2 [true, true])).support) :
    sig ≠ [] ∧ echoTree.verify pk2 [true, true] sig = true := by
  have hk : (pk2, sk2) ∈ (ProbComp.eval (echoTree.keyGen 2)).support := by
    simp only [echoTree, scheme, keyGen, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    exact ⟨[true, false], BitString.mem_support_uniformList_iff.mpr rfl, rfl⟩
  have hv := echoTree.verify_sign 2 (pk2, sk2) hk [true, true] rfl sig hsig
  refine ⟨?_, hv⟩
  rintro rfl
  revert hv
  decide +kernel

/-! ### 2. Concrete `extractForgery` cases at depth `3` -/

/-- Visited node-slot cache after querying leaf `[true, false, true]`:
root `[] ↦ 0`, `[true] ↦ 1`, `[true, false] ↦ 2`. -/
def sampleVisited : NodeSlotCache :=
  [([true, false], 2), ([true], 1), ([], 0)]

def pk₁ : List Bool := [false, false]
def pk₂ : List Bool := [true, false]
def pk₂' : List Bool := [true, true]
def σ₀ : List Bool := [true]
def σ₁ : List Bool := [false, true]
def σ₁' : List Bool := [true, false]
def σLeaf : List Bool := [true, true, true]
def msgStar : List Bool := [false, true]

-- Internal divergence: leaf `[true, true, false]` diverges from `sampleVisited` after `[true]`
-- (`j = 1 < 2`, slot `1`, child bit `true` so `u = 1`).
example :
    extractForgery 3 1 sampleVisited msgStar
      (encodeSignature [true, true, false] [(pk₁, σ₀), (pk₂', σ₁')] σLeaf) =
    (1, pk₂', σ₁') := by
  decide +kernel

-- Root slot (`target = 0`, `path = []`, `j = 0 < 2`) extracts the depth-`0` certificate
-- `(1, pk₁, σ₀)`.
example :
    extractForgery 3 0 sampleVisited msgStar
      (encodeSignature [true, true, false] [(pk₁, σ₀), (pk₂', σ₁')] σLeaf) =
    (1, pk₁, σ₀) := by
  decide +kernel

-- Leaf-parent forgery: leaf `[true, false, false]` reaches visited leaf-parent `[true, false]`
-- (`j = 2`, slot `2`, final bit `false` so `u = 0`) on fresh message `msgStar`.
example :
    extractForgery 3 2 sampleVisited msgStar
      (encodeSignature [true, false, false] [(pk₁, σ₀), (pk₂, σ₁)] σLeaf) =
    (0, msgStar, σLeaf) := by
  decide +kernel

/-! ### 3. Leaf-collision abort vs. `indexedForger` nonvacuity -/

/-- A `3`-query forger at `n = 2` that outputs the 3rd oracle reply `r₃` on fresh message
`[true, true]`. At depth `1` (`2` leaves `[false]` and `[true]`), three valid signing queries
necessarily repeat a leaf, so the 3rd query always aborts (`bad = true`) and returns `r₃ = []`. -/
def threeQueryForger : Forger := fun _ _ => do
  let _ ← ProbOracleComp.query ((), [false, false])
  let _ ← ProbOracleComp.query ((), [false, true])
  let r₃ ← ProbOracleComp.query ((), [true, false])
  return ([true, true], r₃)

private theorem bool_pigeonhole_three (b₁ b₂ b₃ : Bool) :
    b₂ = b₁ ∨ b₃ = b₂ ∨ b₃ = b₁ := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

private theorem lazySignHandler_depth_one {msg r : List Bool} {s s' : LazyTreeState}
    (hmsg : msg.length = 2)
    (hs : (r, s') ∈
      (ProbComp.eval (lazySignHandler echo (fun _ => 1) 2 ([], []) ((), msg) s)).support) :
    (r = [] ∧ s'.2.2.2 = true ∧ s'.2.2.1 = s.2.2.1) ∨
      ∃ b : Bool, [b] ∉ s.2.2.1 ∧ s'.2.2.1 = [b] :: s.2.2.1 := by
  unfold lazySignHandler at hs
  simp only [hmsg, ↓reduceIte] at hs
  split_ifs at hs with hb
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs.symm
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · simp only [ProbComp.eval_bind, BitString.eval_sampleList, PMF.mem_support_bind_iff] at hs
    obtain ⟨l, hl, hsl⟩ := hs
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp (BitString.length_of_mem_support_uniformList hl)
    split_ifs at hsl with hseen
    · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hsl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hsl.symm
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hsl
      obtain ⟨_, -, _, -, heq⟩ := hsl
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq.symm
      exact Or.inr ⟨b, fun hm => hseen (List.contains_iff_mem.mpr hm), rfl⟩

-- At depth `1`, `threeQueryForger` has exact success probability `0` in `lazyTreeGame` because the
-- 3rd query always hits a leaf collision (`s₃.2.2.2 = true`) and returns `r₃ = []`.
example :
    Game.succProbability (ProbComp.eval (lazyTreeGame echo (fun _ => 1) threeQueryForger 2)) =
      0 := by
  have hzero : (ProbComp.eval (lazyTreeGame echo (fun _ => 1) threeQueryForger 2)) true = 0 := by
    rw [PMF.apply_eq_zero_iff]
    intro htrue
    simp only [lazyTreeGame, echo, threeQueryForger, OracleComp.interpret_bind,
      OracleComp.interpret_pure, ProbOracleComp.interpret_query, StateT.run_bind,
      StateT.run_pure] at htrue
    simp only [StateT.run, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at htrue
    obtain ⟨⟨r₁, s₁⟩, hs₁, ⟨r₂, s₂⟩, hs₂, ⟨r₃, s₃⟩, hs₃, hwin⟩ := htrue
    have h₁ := lazySignHandler_depth_one rfl hs₁
    have h₂ := lazySignHandler_depth_one rfl hs₂
    have h₃ := lazySignHandler_depth_one rfl hs₃
    have hr₃ : r₃ = [] := by
      rcases h₃ with ⟨hr, _, _⟩ | ⟨b₃, hnot₃, _⟩
      · exact hr
      · rcases h₂ with ⟨_, hb₂, _⟩ | ⟨b₂, hnot₂, heq₂⟩
        · unfold lazySignHandler at hs₃
          simp only [List.length_cons, List.length_nil, hb₂, ↓reduceIte, ProbComp.eval_pure,
            PMF.mem_support_pure_iff] at hs₃
          exact (Prod.mk.inj hs₃).1
        · rcases h₁ with ⟨_, hb₁, _⟩ | ⟨b₁, _, heq₁⟩
          · unfold lazySignHandler at hs₂
            simp only [List.length_cons, List.length_nil, hb₁, ↓reduceIte, ProbComp.eval_pure,
              PMF.mem_support_pure_iff] at hs₂
            have hb₂ : s₂.2.2.2 = true := by
              obtain ⟨_, rfl⟩ := Prod.mk.inj hs₂.symm
              rfl
            unfold lazySignHandler at hs₃
            simp only [List.length_cons, List.length_nil, hb₂, ↓reduceIte, ProbComp.eval_pure,
              PMF.mem_support_pure_iff] at hs₃
            exact (Prod.mk.inj hs₃).1
          · rw [heq₂, heq₁] at hnot₃
            rw [heq₁] at hnot₂
            have hne : b₂ ≠ b₁ := fun h => hnot₂ (h ▸ List.mem_singleton.mpr rfl)
            rcases bool_pigeonhole_three b₁ b₂ b₃ with rfl | rfl | rfl
            · exact (hne rfl).elim
            · exact (hnot₃ List.mem_cons_self).elim
            · exact (hnot₃ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))).elim
    replace hwin := hwin.symm
    simp only [hr₃, Bool.and_eq_true] at hwin
    exact absurd hwin.2 (by decide +kernel)
  simp [Game.succProbability, hzero]

/-- A `0`-query tree forger against `echo` at depth `1`: forges on `0^n` at leaf `[false]`. -/
def zeroQueryEchoForger : Forger := fun n _ =>
  let msg := List.replicate n false
  pure (msg, encodeSignature [false] [] (encPair encUnary encBits (0, msg)))

theorem isOraclePPT_zeroQueryEchoForger :
    IsOraclePPT (encPair encBits encBits) zeroQueryEchoForger := by
  refine IsOraclePPTOn.isOraclePPT ?_
  unfold zeroQueryEchoForger encodeSignature
  exact ComputableInPolyTime.isOraclePPTOn (by polytime)

-- Nonvacuity of `indexedForger` via `succProbability_lazyTreeGame_le`: `zeroQueryEchoForger` wins
-- `lazyTreeGame` with probability `1` (`Q = 0`, `slotBound = 0`, `dyadicSize 0 = 2`), so
-- `indexedForger` wins `echo.indexedEufCmaGame` with probability at least `1 / 2`.
example (n : ℕ) :
    (1 : ℝ≥0) / 2 ≤ Game.succProbability (ProbComp.eval
      (echo.indexedEufCmaGame
        (indexedForger echo (fun _ => 1) (fun _ => 0) (fun m => m + 5)
          zeroQueryEchoForger) n)) := by
  have hlazy : Game.succProbability
      (ProbComp.eval (lazyTreeGame echo (fun _ => 1) zeroQueryEchoForger n)) = 1 := by
    have heval : ProbComp.eval (lazyTreeGame echo (fun _ => 1) zeroQueryEchoForger n) =
        PMF.pure true := by
      simp only [lazyTreeGame, echo, zeroQueryEchoForger, OracleComp.interpret_pure,
        StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
        verify, encodeSignature, keyDecoder.decode_enc, signatureDecoder.decode_enc]
      simp
    simp [Game.succProbability, heval]
  have hsigCap : ∀ keys ∈ (ProbComp.eval (echo.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (echo.keyGen n)).support, msg = keys'.1) →
      ∀ σ ∈ (ProbComp.eval (echo.sign keys.2 u msg)).support, σ.length ≤ n + 5 := by
    intro keys hkeys u hu msg hmsg σ hσ
    simp only [echo, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hkeys hσ
    subst hσ
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
    rcases hmsg with hlen | ⟨keys', hk', rfl⟩
    · omega
    · simp only [echo, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hk'
      subst hk'
      simp only [List.length_nil]
      omega
  have hbound := succProbability_lazyTreeGame_le echo (fun _ => 1) (fun _ => 0) (fun m => m + 5)
    (n := n) (Q := 0) le_rfl le_rfl (by omega) hsigCap zeroQueryEchoForger
    (fun _ _ => .pure _ 0)
  rw [hlazy] at hbound
  have hdyadic : dyadicSize 0 = 2 := rfl
  rw [hdyadic] at hbound
  exact (div_le_iff₀' (by norm_num)).mpr (by exact_mod_cast hbound)

/-! ### 4. Asymptotic security upgrades -/

-- Depth `2 * n + 1 ≥ n` yields negligible leaf-collision scale `(1 : ℝ≥0) / 2 ^ (2 * n + 1)`.
example : Negligible (fun n => (1 : ℝ≥0) / 2 ^ (2 * n + 1)) :=
  negligible_inv_two_pow_of_le fun n => by omega

-- Upgrading an indexed EUF-CMA scheme + PRF yields negligible forging probability against any
-- oracle-PPT forger.
example {S : IndexedSignatureScheme} (hS : S.IndexedEUFCMA) (hcap : ∀ n, 2 ≤ S.capacity n)
    {F : List Bool → List Bool → List Bool} (hF : PseudorandomFunction F) :
    ∃ M : SignatureScheme,
      Negligible (fun n => Game.succProbability
        (ProbComp.eval (M.eufCmaGame zeroQueryEchoForger n))) := by
  obtain ⟨M, hM⟩ := hS.exists_eufCMA_of_prf hcap hF
  exact ⟨M, hM.negligible zeroQueryEchoForger isOraclePPT_zeroQueryEchoForger⟩

-- Upgrading an indexed EUF-CMA scheme + OWF, and OWF + CRHF, produces both full `EUFCMA` and
-- `OneTimeEUFCMA` stateless signature schemes.
example {S : IndexedSignatureScheme} (hS : S.IndexedEUFCMA) (hcap : ∀ n, 2 ≤ S.capacity n)
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ M : SignatureScheme, M.EUFCMA ∧ M.OneTimeEUFCMA := by
  obtain ⟨M, hM⟩ := hS.exists_eufCMA_of_oneWay hcap hf
  exact ⟨M, hM, hM.oneTimeEUFCMA⟩

example {f : List Bool → List Bool} (hf : OneWay f)
    {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ M : SignatureScheme, M.EUFCMA ∧ M.OneTimeEUFCMA := by
  obtain ⟨M, hM⟩ := hf.exists_eufCMA_of_hashFamily hH
  exact ⟨M, hM, hM.oneTimeEUFCMA⟩

end ComplexityTests.Crypto.TreeSignatureSecurity
