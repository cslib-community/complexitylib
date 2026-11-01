/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.FastLeaves
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.EntryContractionMachine
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Theorem D.1 for entry procedures: the resource analysis

The instance of the contraction interface for entry procedures
(`Cslib.Circuits.Frontier.EntryContractionAlgorithm`) given by the native machine
`EntryContraction.fastCore` (milestone E1.3 of #1538): for every native certificate `ce` of an
entry procedure, `CountingSimulation.entryContractionAlgorithm ce` contracts the networks admissible
for `ce` (`Cslib.Circuits.Frontier.EntryAdmissible`) in time `poly(n) 2 ^ O(s / √⌊log₂ s⌋)` and
polynomial space. This is Theorem D.1 of [OpenAI2026ETH] (p. 53) at truncation order `1`, with
the entries given by procedures.

The analysis follows the one for explicit networks (`CountingSimulation.FastAnalysis`,
`CountingSimulation.fastSizes`, `CountingSimulation.fastLeaves`), with the root call of
`EntryContraction.rootCall`, the precision in unary and the guard `EntryContraction.guard`, which
every admissible input at the modulus passes. The one new ingredient is the cost of the root
entries at a leaf (§D.4.7, p. 64):

* **root descriptors stay with their ports** (`FastContraction.Reach.exists_root_of_inl`): every
  root descriptor of a reached call is the descriptor of a vertex of the input network with as many
  ports, since the native child renumbers the ports of the vertices it keeps. So the entry bounds of
  admissibility apply at every reached leaf;
* **the leaf bound with entry costs** (`FastContraction.exists_leafCertificate_le_of_entry`): a
  leaf whose root entries take time `E` and space `ES` takes time
  `K (n + ES + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋) (E + 1)`;
* **the entry costs fit the budget**: `E ≤ C (s + L + 1) ^ C 2 ^ (C ⌈s ^ (9/10)⌉)`, and
  `C ⌈s ^ (9/10)⌉ ≤ s / √⌊log₂ s⌋` from some size on (`exists_mul_ceilNineTenths_le`).

## Main results

* `Cslib.Complexity.CountingSimulation.entry_length_le_of_reach`: polynomial sizes along the
  recursion from a guarded input.
* `Cslib.Complexity.CountingSimulation.exists_entryLeaves_le`: the leaf bounds on admissible
  inputs.
* `Cslib.Complexity.CountingSimulation.exists_entryAnalysis`: the resource analysis of the
  recursion on admissible inputs.
* `Cslib.Complexity.CountingSimulation.exists_fastCore_le`: the machine within the interface's
  bounds.
* `Cslib.Complexity.CountingSimulation.entryContractionAlgorithm`: the contraction algorithm for
  entry procedures.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53) and
  Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ContractionSchedule
  Cslib.Circuits.Frontier.EntryContraction Cslib.GenericRAM Cslib.GenericRAM.StackRecursion
  Turing.MultiTapeTM
open Cslib.Circuits.Frontier.FastContraction (Call Reach reachInv scheme nativeMk value encCall
  encFrame encValue leafCertificate modulus active OnSchedule fuelConst)

variable {T : Type} {encT : T ↪ List Bool} {entry : T → List Bool → List ℕ}

/-! ### The root -/

/-- The parts of an encoded input `(P, fl, r, G)` against its length. -/
theorem length_parts_le_encInput (P : ℕ) (fl : List ℕ) (r : ℕ) (G : DescribedNetwork T) :
    P + fl.length + (encNat r).length + (DescribedNetwork.encDescribed encT G).length ≤
      (encInput encT (P, fl, r, G)).length := by
  have h := length_le_length_encList encNat fl
  simp only [encInput, length_encPair, encUnary_apply, List.length_replicate] at h ⊢
  omega

/-- **Guarded roots are on the schedule**, for every constant `C ≥ 1` with precision at most
`C m`. -/
theorem onSchedule_rootCall {P C r : ℕ} {G : DescribedNetwork T}
    (hg : EntryContraction.guard (P, modulus G.numEdges, r, G) = true) (hC : 1 ≤ C)
    (hp : P ≤ C * G.numEdges) :
    OnSchedule C G.numEdges (rootCall (P, modulus G.numEdges, r, G)) := by
  have hdeg : ∀ v ∈ G.vertices, v.1.length ≤ degreeBound G.numEdges := by
    simp only [EntryContraction.guard, decide_eq_true_eq] at hg
    exact hg.2.2
  refine FastContraction.onSchedule_root hC rfl rfl rfl (wf_rootCall hg) (fun v hv => ?_) rfl rfl
    hp
  simp only [rootCall, FastContraction.rootNet, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  exact hdeg w hw

/-- **The clock is subexponential on admissible inputs**: with `s ≤ m ≤ C s` edges and precision
`P ≤ D s`, it is at most `2 ^ (K₀ (C + D) s / √⌊log₂ s⌋)`. -/
theorem clock_le {C D s P r : ℕ} {fl : List ℕ} {G : DescribedNetwork T} (hs : 2 ≤ s)
    (hsm : s ≤ G.numEdges) (hmC : G.numEdges ≤ C * s) (hP : P ≤ D * s) :
    clock (P, fl, r, G) ≤ 2 ^ (fuelConst * (C + D) * s / Nat.sqrt (Nat.log 2 s)) := by
  simp only [clock]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  set y := G.numEdges + P
  have hy : y ≤ (C + D) * s := by rw [add_mul]; omega
  have hsy : s ≤ y := by omega
  have hq : 1 ≤ Nat.sqrt (Nat.log 2 s) := Nat.one_le_sqrt_log_two hs
  have hq' : Nat.sqrt (Nat.log 2 s) ≤ Nat.sqrt (Nat.log 2 y) := Nat.sqrt_log_two_mono hsy
  calc fuelConst * y / Nat.sqrt (Nat.log 2 y) ≤ fuelConst * y / Nat.sqrt (Nat.log 2 s) :=
        Nat.div_le_div_left hq' hq
    _ ≤ fuelConst * (C + D) * s / Nat.sqrt (Nat.log 2 s) := by
        refine Nat.div_le_div_right ?_
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hy

/-! ### The sizes -/

/-- **Polynomial sizes along the recursion**: every call reached from the root of a guarded input
of encoded length `n`, its frames and its tagged value are at most `2 ^ 55 (n + 1) ^ 24` long. -/
theorem entry_length_le_of_reach {x : ℕ × List ℕ × ℕ × DescribedNetwork T}
    (hg : EntryContraction.guard x = true) {y : Call T} (hy : Reach nativeMk (rootCall x) y) :
    (encCall encT y).length ≤ 2 ^ 55 * ((encInput encT x).length + 1) ^ 24 ∧
      (∀ a, (reachInv entry nativeMk (rootCall x)).frame y a →
        (encPair (encCall encT) encFrame (y, a)).length ≤
          2 ^ 55 * ((encInput encT x).length + 1) ^ 24) ∧
      (encValue (y.depth, value entry nativeMk y)).length ≤
        2 ^ 55 * ((encInput encT x).length + 1) ^ 24 := by
  obtain ⟨P, fl, r, G⟩ := x
  set x₀ := rootCall (P, fl, r, G) with hx₀
  set m := G.numEdges with hm
  set n := (encInput encT (P, fl, r, G)).length with hn
  set Y := n + 1 with hY
  have hparts := length_parts_le_encInput (encT := encT) P fl r G
  have hmv := DescribedNetwork.length_numEdges_vertices_le (encT := encT) G
  rw [← hn] at hparts
  have hfl : fl = modulus m := by
    simp only [EntryContraction.guard, decide_eq_true_eq] at hg
    exact hg.1
  have hsh := FastContraction.Reach.shape (x₀ := x₀) rfl rfl (wf_rootCall hg) hy
  set Z := 2 ^ 14 * Y ^ 8 with hZ
  have hY1 : 1 ≤ Y := by omega
  have hmY : m + 1 ≤ Y := by omega
  have hY3 : Y ≤ Y ^ 3 := Nat.le_self_pow (by norm_num) _
  have hY8 : Y ^ 3 ≤ Y ^ 8 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY2 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hm2 : m ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm5 : (m + 1) ^ 5 ≤ Y ^ 5 := Nat.pow_le_pow_left hmY 5
  have hPm : x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1 ≤ 41 * Y ^ 3 := by
    change P + (m + 1) * (40 * m ^ 2) + 1 ≤ 41 * Y ^ 3
    have : (m + 1) * (40 * m ^ 2) ≤ Y * (40 * Y ^ 2) := Nat.mul_le_mul hmY (by omega)
    have : Y * (40 * Y ^ 2) = 40 * Y ^ 3 := by ring
    omega
  have hZ1 : 256 * (x₀.edges + 1) ^ 5 * (x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1) +
      x₀.fl.length ≤ Z := by
    have h1 : 256 * (x₀.edges + 1) ^ 5 * (x₀.prec + (x₀.edges + 1) * (40 * x₀.edges ^ 2) + 1) ≤
        256 * Y ^ 5 * (41 * Y ^ 3) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm5) hPm
    have h2 : 256 * Y ^ 5 * (41 * Y ^ 3) = 10496 * Y ^ 8 := by ring
    have h3 : x₀.fl.length ≤ 32 * Y ^ 8 := by
      change fl.length ≤ 32 * Y ^ 8
      omega
    omega
  have hZ2 : x₀.net.vertices.length + (x₀.edges + 1) * x₀.edges ^ 2 + (encNat x₀.rows).length ≤
      Z := by
    have : (x₀.edges + 1) * x₀.edges ^ 2 ≤ Y * Y ^ 2 := Nat.mul_le_mul hmY hm2
    have : Y * Y ^ 2 = Y ^ 3 := by ring
    have hV : x₀.net.vertices.length = G.vertices.length := List.length_map _
    change _ + _ + (encNat r).length ≤ Z
    omega
  have hR₀ : ∀ w ∈ x₀.net.vertices,
      (VertexDesc.enc encT w.2).length ≤ 200 * (Z + 1) ^ 2 := by
    intro w hw
    change w ∈ List.map _ G.vertices at hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    rw [length_encSum]
    simp only [Sum.elim_inl]
    have h1 := length_le_encList_of_mem (encPair (encList encNat) encT) hu
    have h2 : (encList (encPair (encList encNat) encT) G.vertices).length ≤
        (DescribedNetwork.encDescribed encT G).length := by
      change _ ≤ (encPair encUnary (encList (encPair (encList encNat) encT))
        (G.numEdges, G.vertices)).length
      rw [length_encPair]
      dsimp only
      omega
    rw [length_encPair] at h1
    have : Z ≤ (Z + 1) ^ 2 := (Nat.le_succ Z).trans (Nat.le_self_pow (by norm_num) _)
    omega
  obtain ⟨hc, hv, hf⟩ := hsh.length_le entry rfl rfl rfl hZ1 hZ2
    (fun z hz => by
      change z ∈ fl at hz
      rw [hfl] at hz
      exact le_one_of_mem_modulus hz) hR₀
  -- `1000 (Z + 1) ^ 3 ≤ 2 ^ 55 (n + 1) ^ 24`.
  have hfin : 1000 * (Z + 1) ^ 3 ≤ 2 ^ 55 * Y ^ 24 := by
    have h1 : Z + 1 ≤ 2 ^ 15 * Y ^ 8 := by
      have : 1 ≤ Y ^ 8 := Nat.one_le_pow _ _ hY1
      omega
    have h2 : (Z + 1) ^ 3 ≤ (2 ^ 15 * Y ^ 8) ^ 3 := Nat.pow_le_pow_left h1 3
    have h3 : (2 ^ 15 * Y ^ 8) ^ 3 = 2 ^ 45 * Y ^ 24 := by ring
    rw [h3] at h2
    have h4 : 1000 * (2 ^ 45 * Y ^ 24) ≤ 2 ^ 55 * Y ^ 24 := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by norm_num)
    exact (Nat.mul_le_mul_left 1000 h2).trans h4
  refine ⟨hc.trans hfin, fun a ⟨_, ha, c, _, hac⟩ => ?_, hv.trans hfin⟩
  rw [hac]
  exact (hf ha _ c).trans hfin

/-! ### The leaves -/

/-- **The facts at the reached calls that the leaf bounds use.** For all constants `C` and `D`
there is `s₀` such that on every guarded input at the modulus with `s ≤ m ≤ C s` edges and
precision `P ≤ D s`, every reached call has scale `m`, at most `2 m` edges, and, from `s₀` on,
precision at most `m ^ 4`, and at most `leafSize m` edges if the machine treats it as a leaf. -/
theorem entry_reach_facts (C D : ℕ) : ∃ s₀, ∀ (s P r : ℕ) (G : DescribedNetwork T), 2 ≤ s →
    P ≤ D * s → s ≤ G.numEdges → G.numEdges ≤ C * s →
    EntryContraction.guard (P, modulus G.numEdges, r, G) = true →
    ∀ y, Reach nativeMk (rootCall (P, modulus G.numEdges, r, G)) y →
      y.scale = G.numEdges ∧ y.edges ≤ 2 * y.scale ∧
        (s₀ ≤ s → y.prec ≤ y.scale ^ 4 ∧ (active y = false → y.edges ≤ leafSize y.scale)) := by
  obtain ⟨sA, hsA⟩ := exists_activeBounds_le D
  refine ⟨max sA (D + 81), fun s P r G hs hPD hsm hmC hg y hy => ?_⟩
  set m := G.numEdges with hm
  have hp₀ : P ≤ D * m := hPD.trans (Nat.mul_le_mul_left _ hsm)
  have hsh := FastContraction.Reach.shape (x₀ := rootCall (P, modulus m, r, G)) rfl rfl
    (wf_rootCall hg) hy
  have hsc : y.scale = m := hsh.scale_eq
  refine ⟨hsc, hsc ▸ hsh.edges_le, fun hs₀ => ⟨?_, fun hl => ?_⟩⟩
  · have hbd := hsh.bound_add_depth_le
    change y.bound + y.depth ≤ (m + 1) + 0 at hbd
    have hprec : y.prec ≤ P + y.depth * (40 * m ^ 2) := hsh.prec_le
    have : y.depth * (40 * m ^ 2) ≤ (m + 1) * (40 * m ^ 2) := Nat.mul_le_mul_right _ (by omega)
    have h4 : D * m + (m + 1) * (40 * m ^ 2) ≤ m ^ 4 := by
      have hm81 : D + 81 ≤ m := by omega
      have h1 : D * m ≤ m * m := Nat.mul_le_mul_right _ (by omega)
      have h2 : 81 * m ^ 3 ≤ m ^ 4 := by
        rw [pow_succ m 3, mul_comm (m ^ 3) m]
        exact Nat.mul_le_mul_right _ (by omega)
      have h3 : m * m ≤ m ^ 3 := by nlinarith
      have h4 : m ^ 2 ≤ m ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have e : (m + 1) * (40 * m ^ 2) = 40 * m ^ 3 + 40 * m ^ 2 := by ring
      have h5 : m * m = m ^ 2 := by ring
      omega
    rw [hsc]
    omega
  · have hm2 : D + 2 ≤ m := by omega
    have hC1 : P / m + 1 ≤ D + 1 := by
      have := Nat.div_le_div_right (c := m) hp₀
      rw [Nat.mul_div_cancel _ (by omega)] at this
      omega
    have hB := hsA m (by omega) (P / m + 1) hC1
    have hpC : P ≤ (P / m + 1) * m :=
      (Nat.lt_div_mul_add (a := P) (b := m) (by omega)).le.trans (by rw [add_mul, one_mul])
    have h := hy.onSchedule hB (onSchedule_rootCall hg (Nat.le_add_left 1 _) hpC)
    rw [hsc]
    exact h.edges_le_leafSize hB hl

/-- `2 ^ (C ⌈s ^ (9/10)⌉) ≤ 2 ^ (C s₁) 2 ^ (s / √⌊log₂ s⌋)` once `C ⌈s ^ (9/10)⌉` fits the budget
from `s₁` on. -/
private theorem two_pow_mul_ceilNineTenths_le {C s₁ : ℕ}
    (hs₁ : ∀ s, s₁ ≤ s → C * ceilNineTenths s ≤ s / Nat.sqrt (Nat.log 2 s)) (s : ℕ) :
    2 ^ (C * ceilNineTenths s) ≤ 2 ^ (C * s₁) * 2 ^ (s / Nat.sqrt (Nat.log 2 s)) := by
  rw [← pow_add]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rcases le_or_gt s₁ s with h | h
  · have := hs₁ s h
    omega
  · exact (Nat.mul_le_mul_left C ((ceilNineTenths_le_self s).trans h.le)).trans
      (Nat.le_add_right _ _)

/-- **The leaf bounds on admissible inputs**: for a native certificate `ce` of the entry procedure
and all constants `C` and `D` there is `K` such that on every input at the modulus admissible at
size `s ≥ 2` with constant `C` and with precision `1 ≤ P ≤ D s`, direct summation at every reached
call that the machine treats as a leaf takes time at most `K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and
space at most `K (n + 1) ^ K`. The root entries take time at most
`C (s + L + 1) ^ C 2 ^ (C ⌈s ^ (9/10)⌉)` at every reached leaf
(`FastContraction.Reach.exists_root_of_inl`), within the budget from some size on
(`exists_mul_ceilNineTenths_le`). -/
theorem exists_entryLeaves_le
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (C D : ℕ) :
    ∃ K : ℕ, ∀ (s P r : ℕ) (G : DescribedNetwork T), 2 ≤ s → 1 ≤ P → P ≤ D * s →
      EntryAdmissible ce C s (r, G) →
      ∀ y, Reach nativeMk (rootCall (P, modulus G.numEdges, r, G)) y → active y = false →
        (leafCertificate ce nativeMk).time y ≤
            K * ((encInput encT (P, modulus G.numEdges, r, G)).length + 1) ^ K *
              2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
          (leafCertificate ce nativeMk).space y ≤
            K * ((encInput encT (P, modulus G.numEdges, r, G)).length + 1) ^ K := by
  obtain ⟨s₀, hs₀⟩ := entry_reach_facts (T := T) C D
  obtain ⟨KB, hKB⟩ := FastContraction.exists_leafCertificate_le_of_entry ce C 4 s₀
  obtain ⟨s₁, hs₁⟩ := exists_mul_ceilNineTenths_le C
  obtain ⟨cW, hcW⟩ : ∃ cW, cW = 2 ^ 55 + C * 2 ^ C + 1 := ⟨_, rfl⟩
  obtain ⟨cE, hcE⟩ : ∃ cE, cE = (C * 2 ^ C + 1) * 2 ^ (C * s₁) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = KB * cW ^ KB * cE + (24 + C) * KB + C + KB + 1 := ⟨_, rfl⟩
  refine ⟨K, fun s P r G hs hP hPD hA y hy hl => ?_⟩
  have hg : EntryContraction.guard (P, modulus G.numEdges, r, G) = true :=
    guard_of_entryAdmissible hA
  obtain ⟨-, hsm, hmC, -, hent⟩ := hA
  simp only at hsm hmC hent
  set n := (encInput encT (P, modulus G.numEdges, r, G)).length with hn
  set Y := n + 1 with hY
  set S := Nat.sqrt (Nat.log 2 s) with hS
  set L := (DescribedNetwork.encDescribed encT G).length with hL
  have hparts := length_parts_le_encInput (encT := encT) P (modulus G.numEdges) r G
  have hmv := DescribedNetwork.length_numEdges_vertices_le (encT := encT) G
  rw [← hn] at hparts
  obtain ⟨hsc, hE2, hbig⟩ := hs₀ s P r G hs hPD hsm hmC hg y hy
  obtain ⟨-, hshape⟩ := hy.wf_packetShape (wf_rootCall hg) (packetShape_rootCall _)
  -- The root entries at the leaf.
  have hroot : ∀ v ∈ y.net.vertices, ∀ t, v.2 = .inl t → ∀ bs : List Bool,
      bs.length = v.1.length →
      ce.time (t, bs) ≤ C * (s + L + 1) ^ C * 2 ^ (C * ceilNineTenths s) ∧
        ce.space (t, bs) ≤ C * (s + L + 1) ^ C := by
    intro v hv t ht bs hbs
    obtain ⟨w, hw, hwt, hwlen⟩ := hy.exists_root_of_inl hv ht
    change w ∈ List.map _ G.vertices at hw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    simp only [Sum.inl.injEq] at hwt
    subst hwt
    exact hent u hu bs (hbs.trans hwlen.symm)
  obtain ⟨hT, hSp⟩ := hKB nativeMk s y _ _ hs (hsc ▸ hsm) (hsc ▸ hmC) hshape hE2
    (fun h => ⟨(hbig h).2 hl, (hbig h).1⟩) hroot
  have hny := (entry_length_le_of_reach (encT := encT) (entry := entry) hg hy).1
  rw [← hn] at hny
  change _ ≤ 2 ^ 55 * Y ^ 24 at hny
  -- The arithmetic against `Y = n + 1`.
  have hY1 : 1 ≤ Y := by omega
  have hsLY : s + L + 1 ≤ 2 * Y := by omega
  have hES : C * (s + L + 1) ^ C ≤ C * 2 ^ C * Y ^ C := by
    calc C * (s + L + 1) ^ C ≤ C * (2 * Y) ^ C := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsLY _)
      _ = C * 2 ^ C * Y ^ C := by rw [mul_pow, Nat.mul_assoc]
  have hYC : Y ^ C ≤ Y ^ (24 + C) := Nat.pow_le_pow_right hY1 (by omega)
  have hY24 : Y ^ 24 ≤ Y ^ (24 + C) := Nat.pow_le_pow_right hY1 (by omega)
  have hW : (encCall encT y).length + C * (s + L + 1) ^ C + 1 ≤ cW * Y ^ (24 + C) := by
    have h1 : 2 ^ 55 * Y ^ 24 ≤ 2 ^ 55 * Y ^ (24 + C) := Nat.mul_le_mul_left _ hY24
    have h2 : C * 2 ^ C * Y ^ C ≤ C * 2 ^ C * Y ^ (24 + C) := Nat.mul_le_mul_left _ hYC
    have h3 : 1 ≤ Y ^ (24 + C) := Nat.one_le_pow _ _ hY1
    have e : cW * Y ^ (24 + C) = 2 ^ 55 * Y ^ (24 + C) + C * 2 ^ C * Y ^ (24 + C) +
        Y ^ (24 + C) := by rw [hcW]; ring
    omega
  have hWK : KB * ((encCall encT y).length + C * (s + L + 1) ^ C + 1) ^ KB ≤
      KB * cW ^ KB * Y ^ ((24 + C) * KB) := by
    calc _ ≤ KB * (cW * Y ^ (24 + C)) ^ KB := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW _)
      _ = KB * cW ^ KB * Y ^ ((24 + C) * KB) := by rw [mul_pow, ← pow_mul]; ring
  have hE1 : C * (s + L + 1) ^ C * 2 ^ (C * ceilNineTenths s) + 1 ≤
      cE * Y ^ C * 2 ^ (s / S) := by
    have h1 := two_pow_mul_ceilNineTenths_le hs₁ s
    have h2 : C * (s + L + 1) ^ C * 2 ^ (C * ceilNineTenths s) ≤
        C * 2 ^ C * Y ^ C * (2 ^ (C * s₁) * 2 ^ (s / S)) := Nat.mul_le_mul hES h1
    have h3 : 1 ≤ Y ^ C * (2 ^ (C * s₁) * 2 ^ (s / S)) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have e : cE * Y ^ C * 2 ^ (s / S) = C * 2 ^ C * Y ^ C * (2 ^ (C * s₁) * 2 ^ (s / S)) +
        Y ^ C * (2 ^ (C * s₁) * 2 ^ (s / S)) := by rw [hcE]; ring
    omega
  have hexp : KB * s / S + s / S ≤ K * s / S :=
    Nat.div_add_div_le_add_div.trans (Nat.div_le_div_right (by
      rw [← Nat.add_one_mul]; exact Nat.mul_le_mul_right _ (by omega)))
  constructor
  · calc _ ≤ KB * ((encCall encT y).length + C * (s + L + 1) ^ C + 1) ^ KB *
          2 ^ (KB * s / S) * (C * (s + L + 1) ^ C * 2 ^ (C * ceilNineTenths s) + 1) := hT
      _ ≤ KB * cW ^ KB * Y ^ ((24 + C) * KB) * 2 ^ (KB * s / S) * (cE * Y ^ C * 2 ^ (s / S)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ hWK) hE1
      _ = KB * cW ^ KB * cE * Y ^ ((24 + C) * KB + C) * 2 ^ (KB * s / S + s / S) := by
          rw [pow_add, pow_add]; ring
      _ ≤ K * Y ^ K * 2 ^ (K * s / S) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hY1 (by omega)))
            (Nat.pow_le_pow_right (by norm_num) hexp)
  · calc _ ≤ KB * ((encCall encT y).length + C * (s + L + 1) ^ C + 1) ^ KB := hSp
      _ ≤ KB * cW ^ KB * Y ^ ((24 + C) * KB) := hWK
      _ ≤ K * Y ^ K := by
          have hcE1 : 1 ≤ cE := by rw [hcE]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
          refine Nat.mul_le_mul ?_ (Nat.pow_le_pow_right hY1 (by omega))
          calc KB * cW ^ KB ≤ KB * cW ^ KB * cE := Nat.le_mul_of_pos_right _ hcE1
            _ ≤ K := by omega

/-! ### The resource analysis -/

/-- **The resource analysis of the recursion on admissible inputs.** For a native certificate `ce`
of the entry procedure and all constants `C` and `D` there are `K` and `s₀` such that on every input
at the modulus admissible at size `s ≥ 2` with constant `C` and with precision `1 ≤ P ≤ D s`, the
root call has a derivation whose nodes, frames and values are at most `F` long, whose leaves take
time at most `TL` and space at most `SL`, with `H` open calls, such that
`H + F + SL ≤ K (n + 1) ^ K` and `TL ≤ K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` for the input length
`n`; and from `s₀` on its `N` nodes fit in the clock, `2 N - 1 ≤ clock`. -/
theorem exists_entryAnalysis
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (C D : ℕ) :
    ∃ K s₀ : ℕ, ∀ (s P r : ℕ) (G : DescribedNetwork T), 2 ≤ s → 1 ≤ P → P ≤ D * s →
      EntryAdmissible ce C s (r, G) →
      ∃ N H F TL SL : ℕ,
        (scheme entry nativeMk).Eval
          (reachInv entry nativeMk (rootCall (P, modulus G.numEdges, r, G)))
          (rootCall (P, modulus G.numEdges, r, G))
          (0, value entry nativeMk (rootCall (P, modulus G.numEdges, r, G))) N H ∧
        (s₀ ≤ s → 2 * N - 1 ≤ clock (P, modulus G.numEdges, r, G)) ∧
        (∀ y, (reachInv entry nativeMk (rootCall (P, modulus G.numEdges, r, G))).node y →
          (encCall encT y).length ≤ F ∧
            ((scheme entry nativeMk).isLeaf y = true →
              (leafCertificate ce nativeMk).time y ≤ TL ∧
                (leafCertificate ce nativeMk).space y ≤ SL)) ∧
        (∀ y a, (reachInv entry nativeMk (rootCall (P, modulus G.numEdges, r, G))).frame y a →
          (encPair (encCall encT) encFrame (y, a)).length ≤ F) ∧
        (∀ v, (reachInv entry nativeMk (rootCall (P, modulus G.numEdges, r, G))).value v →
          (encValue v).length ≤ F) ∧
        H + F + SL ≤ K * ((encInput encT (P, modulus G.numEdges, r, G)).length + 1) ^ K ∧
        TL ≤ K * ((encInput encT (P, modulus G.numEdges, r, G)).length + 1) ^ K *
          2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) := by
  obtain ⟨KL, hKL⟩ := exists_entryLeaves_le ce C D
  obtain ⟨sA, hsA⟩ := exists_activeBounds_le D
  refine ⟨2 ^ 55 + 24 + KL + 1, max sA (D + 2), fun s P r G hs hP hPD hA => ?_⟩
  have hg : EntryContraction.guard (P, modulus G.numEdges, r, G) = true :=
    guard_of_entryAdmissible hA
  have hsm : s ≤ G.numEdges := hA.2.1
  have hKL' := hKL s P r G hs hP hPD hA
  set x := (P, modulus G.numEdges, r, G) with hx
  set x₀ := rootCall x with hx₀
  set m := G.numEdges with hm
  set n := (encInput encT x).length with hn
  have hparts := length_parts_le_encInput (encT := encT) P (modulus G.numEdges) r G
  have hmv := DescribedNetwork.length_numEdges_vertices_le (encT := encT) G
  rw [← hx, ← hn] at hparts
  have hmn : m ≤ n := by omega
  have hp₀ : P ≤ D * m := hPD.trans (Nat.mul_le_mul_left _ hsm)
  -- The derivation.
  obtain ⟨N, H, he, hN, hH⟩ : ∃ N H, (scheme entry nativeMk).Eval (reachInv entry nativeMk x₀) x₀
      (0, value entry nativeMk x₀) N H ∧ (max sA (D + 2) ≤ s → 2 * N - 1 ≤ clock x) ∧
        H ≤ m + 1 := by
    by_cases hs₀ : max sA (D + 2) ≤ s
    · have hm2 : D + 2 ≤ m := by omega
      have hC1 : P / m + 1 ≤ D + 1 := by
        have := Nat.div_le_div_right (c := m) hp₀
        rw [Nat.mul_div_cancel _ (by omega)] at this
        omega
      have hB := hsA m (by omega) (P / m + 1) hC1
      have hpC : P ≤ (P / m + 1) * m :=
        (Nat.lt_div_mul_add (a := P) (b := m) (by omega)).le.trans (by rw [add_mul, one_mul])
      obtain ⟨N, H, he, hN, hH⟩ := FastContraction.exists_eval_onSchedule entry hB
        (onSchedule_rootCall hg (Nat.le_add_left 1 _) hpC) rfl (by omega)
      exact ⟨N, H, he, fun _ => two_mul_sub_one_le_fuel hm2 hp₀ hN,
        hH.trans ((Nat.log_lt_self 2 (by omega)).le.trans (Nat.le_succ _))⟩
    · obtain ⟨N, H, he, hH⟩ := FastContraction.exists_eval_reachInv (ev := entry) (mk := nativeMk)
        (x₀ := x₀) rfl
      exact ⟨N, H, he, fun h => absurd h hs₀, hH⟩
  -- The bounds.
  set K := 2 ^ 55 + 24 + KL + 1 with hK
  have hB1 : 1 ≤ n + 1 := by omega
  refine ⟨N, H, 2 ^ 55 * (n + 1) ^ 24,
    KL * (n + 1) ^ KL * 2 ^ (KL * s / Nat.sqrt (Nat.log 2 s)), KL * (n + 1) ^ KL, he, hN,
    fun y hy => ⟨(entry_length_le_of_reach (entry := entry) hg hy).1, fun hl => ?_⟩,
    fun y a ha => (entry_length_le_of_reach (entry := entry) hg ha.1).2.1 a ha,
    fun v ⟨y, hy, hv⟩ => hv ▸ (entry_length_le_of_reach (entry := entry) hg hy).2.2, ?_, ?_⟩
  · exact hKL' y hy (by simpa [scheme] using hl)
  · have h1 : H ≤ 1 * (n + 1) ^ K := by
      have : n + 1 ≤ (n + 1) ^ K := Nat.le_self_pow (by omega) _
      omega
    have h2 : 2 ^ 55 * (n + 1) ^ 24 ≤ 2 ^ 55 * (n + 1) ^ K :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 (by omega))
    have h3 : KL * (n + 1) ^ KL ≤ KL * (n + 1) ^ K :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 (by omega))
    calc H + 2 ^ 55 * (n + 1) ^ 24 + KL * (n + 1) ^ KL
        ≤ 1 * (n + 1) ^ K + 2 ^ 55 * (n + 1) ^ K + KL * (n + 1) ^ K := by omega
      _ ≤ K * (n + 1) ^ K := by
          rw [← add_mul, ← add_mul]
          exact Nat.mul_le_mul_right _ (by omega)
  · exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hB1 (by omega)))
      (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (Nat.mul_le_mul_right _
        (by omega))))

/-! ### The resources of the machine -/

/-- **The machine within the interface's bounds.** For a native certificate `ce` of the entry
procedure and all constants `C` and `D` there is `K` such that on every input at the modulus
admissible at size `s ≥ 2` with constant `C` and with precision `1 ≤ P ≤ D s`, the machine
`EntryContraction.fastCore ce` takes time at most `K (n + 1) ^ K 2 ^ (K s / √⌊log₂ s⌋)` and space at
most `K (n + 1) ^ K`. Admissible inputs pass the guard; from some size on the clocked run returns
the root's value, and below it direct summation costs a constant factor. -/
theorem exists_fastCore_le
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) (C D : ℕ) :
    ∃ K : ℕ, ∀ (s P r : ℕ) (G : DescribedNetwork T), 2 ≤ s → 1 ≤ P → P ≤ D * s →
      EntryAdmissible ce C s (r, G) →
      (fastCore ce).time (P, modulus G.numEdges, r, G) ≤
          K * ((encInput encT (P, modulus G.numEdges, r, G)).length + 1) ^ K *
            2 ^ (K * s / Nat.sqrt (Nat.log 2 s)) ∧
        (fastCore ce).space (P, modulus G.numEdges, r, G) ≤
          K * ((encInput encT (P, modulus G.numEdges, r, G)).length + 1) ^ K := by
  obtain ⟨Ka, s₀, hKa⟩ := exists_entryAnalysis ce C D
  obtain ⟨K₁, hK₁⟩ := Scheme.certificate_le
    (FastContraction.scheme_nativeMk_polyTime (encT := encT) entry) (leafCertificate ce nativeMk)
  obtain ⟨K₂, hK₂⟩ := exists_directCore_le (entry := entry) ce C
  have hgP := NativeCertificate.ofPolyTime_isPolynomial (guard_polyTime (encT := encT))
  have hcnP := NativeCertificate.ofPolyTime_isPolynomial (clock_polyTime (encT := encT))
  have hcrP := NativeCertificate.ofPolyTime_isPolynomial (rootCall_polyTime (encT := encT))
  have hfuelL := (clock_polyTime (encT := encT)).polyBounded_length
  obtain ⟨c₁, d₁, h₁⟩ := (((((((hgP.1.add hgP.2).add hcnP.1).add hcnP.2).add hcrP.1).add
    hcrP.2).add hfuelL).add .self).exists_le
  have htP := NativeCertificate.ofPolyTime_isPolynomial (valueTag_polyTime (encT := encT))
  have hoP := NativeCertificate.ofPolyTime_isPolynomial (valueList_polyTime (encT := encT))
  have hfP := NativeCertificate.ofPolyTime_isPolynomial
    (ComputableInPolyTime.fst (encInput encT) encValue)
  obtain ⟨c₂, d₂, h₂⟩ := (((((htP.1.add htP.2).add hoP.1).add hoP.2).add hfP.1).add
    hfP.2).exists_le
  obtain ⟨K, hK⟩ := exists_clockedRun_le K₁ Ka (4 * c₁) d₁ (2 * (c₂ * (Ka + 2) ^ d₂))
    ((Ka + 1) * d₂) (2 * (K₂ * 2 ^ (K₂ * s₀))) K₂ (fuelConst * (C + D))
  refine ⟨K, fun s P r G hs hP hPD hA => ?_⟩
  obtain ⟨N, H, F, TL, SL, he, hN, hnode, hframe, hvalue, hHFS, hTL⟩ :=
    hKa s P r G hs hP hPD hA
  have hg : EntryContraction.guard (P, modulus G.numEdges, r, G) = true :=
    guard_of_entryAdmissible hA
  obtain ⟨hdT, hdS⟩ := hK₂ s P r G hA
  set x := (P, modulus G.numEdges, r, G)
  have hq1 := h₁ x
  set B := (encInput encT x).length + 1 with hB
  obtain ⟨hrT, hrS⟩ := hK₁ (NativeCertificate.ofPolyTime clock_polyTime)
    (NativeCertificate.ofPolyTime rootCall_polyTime) _ F TL SL hnode hframe hvalue x _ N H he
  have hrT' : (runCore ce).time x ≤ _ := hrT
  have hrS' : (runCore ce).space x ≤ _ := hrS
  -- The output of the run, and direct summation below `s₀`.
  have hdec (v : ℕ × List ℕ) (hv : (reachInv entry nativeMk (rootCall x)).value v) :
      (NativeCertificate.ofPolyTime (valueTag_polyTime (encT := encT))).time (x, v) +
        (NativeCertificate.ofPolyTime (valueTag_polyTime (encT := encT))).space (x, v) +
        (NativeCertificate.ofPolyTime (valueList_polyTime (encT := encT))).time (x, v) +
        (NativeCertificate.ofPolyTime (valueList_polyTime (encT := encT))).space (x, v) +
        (NativeCertificate.ofPolyTime
          (ComputableInPolyTime.fst (encInput encT) encValue)).time (x, v) +
        (NativeCertificate.ofPolyTime
          (ComputableInPolyTime.fst (encInput encT) encValue)).space (x, v) ≤
        c₂ * (Ka + 2) ^ d₂ * B ^ ((Ka + 1) * d₂) := by
    refine (h₂ (x, v)).trans ?_
    rw [Nat.mul_assoc, pow_mul, ← mul_pow]
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have := hvalue v hv
    have hB1 : B ≤ B ^ (Ka + 1) := Nat.le_self_pow (by omega) _
    have hBK := Nat.mul_le_mul_left Ka
      (Nat.pow_le_pow_right (by omega : 1 ≤ B) (by omega : Ka ≤ Ka + 1))
    simp only [length_encPair (enc₁ := encInput encT) (enc₂ := encValue), add_mul]
    omega
  have hdir (hs₀ : s < s₀) : (directCore entry ce).time x ≤ K₂ * 2 ^ (K₂ * s₀) * B ^ K₂ :=
    hdT.trans (le_of_le_of_eq (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hs₀.le))) (by ring))
  have hdirS : (directCore entry ce).space x ≤ K₂ * 2 ^ (K₂ * s₀) * B ^ K₂ :=
    hdS.trans (le_of_le_of_eq (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos (K₂ * s₀))) (by ring))
  have hbig : s₀ ≤ s → (scheme entry nativeMk).run clock rootCall x =
      some (0, value entry nativeMk (rootCall x)) :=
    fun h => Scheme.run_eq_some he (hN h)
  rw [fastCore_time, fastCore_space, ite_eq_left hg, ite_eq_left hg]
  -- The output step: decoding a value, or direct summation below `s₀`.
  refine hK (by omega) hrT' hrS' (by rw [Nat.mul_assoc]; omega) ?_ (clock_le hs hA.2.1 hA.2.2.1 hPD)
    hHFS hTL
  rw [Nat.mul_assoc 2, Nat.mul_assoc 2]
  rcases hr : (scheme entry nativeMk).run clock rootCall x with _ | ⟨tag, coeffs⟩
  · have hs₀ : s < s₀ := Nat.lt_of_not_le fun h => by rw [hbig h] at hr; cases hr
    have := hdir hs₀
    simp only [Option.elim_none]; omega
  · have hd := hdec (tag, coeffs) (Scheme.value_of_run_eq_some he hr)
    simp only [Option.elim_some]
    split_ifs with h0
    · omega
    · have hs₀ : s < s₀ := Nat.lt_of_not_le fun h => by
        rw [hbig h] at hr; cases hr; simp at h0
      have := hdir hs₀; omega

/-! ### The contraction algorithm -/

/-- **Theorem D.1 for entry procedures** ([OpenAI2026ETH], p. 53, at truncation order `1`): for
every native certificate `ce` of an entry procedure, the guarded native recursion with direct
summation as the fallback (`EntryContraction.fastCore ce`) is a contraction algorithm for the
networks admissible for `ce`, in time `poly(n) 2 ^ O(s / √⌊log₂ s⌋)` and polynomial space. -/
noncomputable def entryContractionAlgorithm
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    EntryContractionAlgorithm encT entry (EntryAdmissible ce) where
  core := coreValue entry
  certificate := fastCore ce
  val_core := val_coreValue
  bound C D := exists_fastCore_le ce C D

end Cslib.Complexity.CountingSimulation
