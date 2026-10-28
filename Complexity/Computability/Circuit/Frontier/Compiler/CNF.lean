/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.SatCount
public import Complexity.Computability.Circuit.Frontier.Compiler
public import Complexity.Computability.Complexity.Problems.CircuitSAT
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared
public import Complexity.Logics.Propositional.CSP.ToCNF
import Complexity.Computability.Circuit.Program

/-!
# Exact-multiplicity CSP and CNF compilation of circuits via the frontier compiler

Compiles a circuit `c : Circuit σ n m` over an arbitrary Boolean signature `σ` into a Boolean
constraint satisfaction instance `Compiler.toCSP c : CSP (CircuitRel σ m) ℕ` on its reachable wires
(`Compiler.Signal c`), and from there via `Cslib.Logic.PL.CSP.toCNF` into a CNF formula
`Compiler.toCNF c I acc` accompanied by an explicit unread-input / unconstrained-wire shift
`Compiler.freeShift c I acc`, such that:

1. **Bounded scope and clause width:** when `c.FanInAtMost k`, every constraint of `toCSP c` (and
   therefore every clause of `toCNF c I acc`) has width at most `k + 1`.
2. **Gate-size variable bound:** `(toCNF c I acc).numVars ≤ k * c.size + m` (independent of the
   ambient input count `n`), bounded through `Compiler.card_signal_le` on `Compiler.Signal c`.
3. **Exact multiplicity (`acceptCount_eq_two_pow_freeShift_mul_modelCount`):**
   `c.acceptCount I acc = 2 ^ freeShift c I acc * (toCNF c I acc).modelCount`,
   proved through the frontier constraint network `Compiler.network c I _`, its exactness and
   trace-uniqueness theorems (`Compiler.satisfies_iff`, `Compiler.eq_trace`,
   `Compiler.accepted_network`), and read-dependence (`Network.dependsOn_read`).

### Source relation and library extensions

Appendix C.1 of [OpenAI2026ETH] (p. 51) introduces one variable per gate (`n + s` variables total)
for single-output De Morgan (`AND`/`OR`/`NOT`) circuits to preserve **satisfiability** in 3-CNF.
Generalizing to arbitrary signatures `σ` and multi-output acceptance predicates `acc`, pruning to
reachable wires (`Signal c`) so the variable bound `k * c.size + m` depends on gate count rather
than ambient input count `n`, and tracking exact multiplicity via `2 ^ freeShift` for `#Circuit-SAT`
are original extensions built on `Cslib.Circuits.Frontier.Compiler` and `Cslib.Logic.PL.CSP.ToCNF`.

## Main definitions

* `Cslib.Circuits.Frontier.Compiler.satisfiedPairsEquiv`: bijection between input/edge-assignment
  pairs satisfying `Compiler.network` and `Network.accepted`.
* `Cslib.Circuits.Frontier.Compiler.CircuitRel`, `Cslib.Circuits.Frontier.Compiler.circuitSem`:
  relation alphabet `σ.Op ⊕ Fin m` and Boolean semantics for gate evaluation and output acceptance.
* `Cslib.Circuits.Frontier.Compiler.toCSP`, `Cslib.Circuits.Frontier.Compiler.toCNF`,
  `Cslib.Circuits.Frontier.Compiler.freeShift`, `Cslib.Circuits.Frontier.Compiler.toSatCNF`,
  `Cslib.Circuits.Frontier.Compiler.satFreeShift`: reachable-wire CSP and exact-multiplicity CNF
  compilation.

## Main results

* `Cslib.Circuits.Frontier.Compiler.length_scope_le_of_mem_toCSP`,
  `Cslib.Circuits.Frontier.Compiler.length_le_of_mem_toCNF`: constraint scopes and clauses have
  length at most `k + 1` when `c.FanInAtMost k`.
* `Cslib.Circuits.Frontier.Compiler.numVars_toCNF_le`: `(toCNF c I acc).numVars ≤ k * c.size + m`.
* `Cslib.Circuits.Frontier.Compiler.acceptCount_eq_two_pow_freeShift_mul_modelCount`,
  `Cslib.Circuits.Frontier.Compiler.satCount_eq_two_pow_satFreeShift_mul_modelCount`:
  exact counting identities reducing `#Circuit-SAT` to bounded-width `#SAT`.
* `Cslib.Circuits.Frontier.Compiler.satisfiable_toSatCNF_iff`: satisfiability equivalence.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix C.1, p. 51.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Compiler

open Cslib.Logic.PL Set

/-! ### Uniqueness bijection on `Compiler.network` -/

section FrontierBounds

variable {σ : Signature} {n m : ℕ}

/-- By `Compiler.satisfies_iff` and `Compiler.eq_trace`, pairs `(x, α)` satisfying
`Compiler.network c I Acc` correspond bijectively to accepted inputs
`x ∈ (network c I Acc).accepted` with zero multiplicity inflation. -/
noncomputable def satisfiedPairsEquiv {U : Type*} (c : Circuit σ n m)
    (I : Interpretation σ U) (Acc : Fin m → Set U) :
    {p : (Fin n → U) × (Edge c → U) // (network c I Acc).Satisfies p.1 p.2} ≃
      (network c I Acc).accepted where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun x :=
    ⟨(x.1, fun e => c.program.trace I x.1 e.signal.1),
      satisfies_trace (by
        have hx : x.1 ∈ {y : Fin n → U | ∀ o, c.eval I y o ∈ Acc o} :=
          accepted_network (c := c) (I := I) (Acc := Acc) ▸ x.2
        exact hx)⟩
  left_inv p := Subtype.ext (Prod.ext rfl (satisfies_iff.mp p.2).2.symm)
  right_inv _ := Subtype.ext rfl

end FrontierBounds

/-! ### Constructive CSP and CNF compilation along reachable wires -/

/-- Relation alphabet for frontier CSP compilation of an `m`-output circuit over `σ`:
* `.inl op`: a gate-evaluation relation on `outWire :: argWires`;
* `.inr o`: the unary acceptance predicate at output `o : Fin m`. -/
abbrev CircuitRel (σ : Signature) (m : ℕ) : Type :=
  σ.Op ⊕ Fin m

/-- Boolean relation semantics for `CircuitRel σ m`:
* `.inl op` accepts `outBit :: inBits` iff `inBits.length = σ.Arity op` and
  `outBit = I op (fun a => inBits.getD a.val false)`;
* `.inr o` accepts `[b]` iff `acc o b = true`. -/
def circuitSem {σ : Signature} {m : ℕ} (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) : CircuitRel σ m → List Bool → Bool
  | .inl op, outBit :: inBits =>
    decide (inBits.length = σ.Arity op) &&
      (outBit == I op fun a => inBits.getD a.val false)
  | .inl _, [] => false
  | .inr o, [b] => acc o b
  | .inr _, _ => false

/-- One backward reachability step on a gate `(g, j)`: if gate wire `n + j` is already marked
reachable, prepend its argument wires `g.2`. -/
def reachStep {σ : Signature} (n : ℕ) (seen : List ℕ) (gj : (σ.Op × List ℕ) × ℕ) : List ℕ :=
  if seen.any (· == n + gj.2) then gj.1.2 ++ seen else seen

/-- Backward pass computing the list of reachable wire numbers from a serialized circuit `(gates,
outputs)` on `n` inputs. -/
def reachWiresCode {σ : Signature} (n : ℕ) (code : List (σ.Op × List ℕ) × List ℕ) : List ℕ :=
  code.1.zipIdx.reverse.foldl (reachStep n) code.2

/-- Number of reachable internal gates in a serialized circuit on `n` inputs. -/
def reachGateCountCode {σ : Signature} (n : ℕ) (code : List (σ.Op × List ℕ) × List ℕ) : ℕ :=
  code.1.zipIdx.countP fun gj => (reachWiresCode n code).any (· == n + gj.2)

/-- Serialized circuit-to-CSP compiler emitting one gate constraint `(Sum.inl g.1, (n + j) :: g.2)`
for each reachable gate `(g, j)` followed by one unary output constraint
`(Sum.inr o, [code.2.getD o.val 0])` for each `o : Fin m`. -/
def toCSPCode {σ : Signature} (m n : ℕ) (code : List (σ.Op × List ℕ) × List ℕ) :
    CSP (CircuitRel σ m) ℕ :=
  let reach := reachWiresCode n code
  let gCons : CSP (CircuitRel σ m) ℕ :=
    (code.1.zipIdx.filter fun gj => reach.any (· == n + gj.2)).map
      fun gj => (Sum.inl gj.1.1, (n + gj.2) :: gj.1.2)
  let outCons : CSP (CircuitRel σ m) ℕ :=
    (List.finRange m).map fun o => (Sum.inr o, [code.2.getD o.val 0])
  gCons ++ outCons

/-- Reachable-wire Boolean CSP compiled from `c : Circuit σ n m`. -/
def toCSP {σ : Signature} {n m : ℕ} (c : Circuit σ n m) : CSP (CircuitRel σ m) ℕ :=
  toCSPCode m n c.code

/-- Serialized circuit-to-CNF compiler obtained by applying `CSP.toCNF (circuitSem I acc)` to
`toCSPCode m n code`. -/
def toCNFCode {σ : Signature} (I : Interpretation σ Bool) {m : ℕ} (acc : Fin m → Bool → Bool)
    (n : ℕ) (code : List (σ.Op × List ℕ) × List ℕ) : CNF ℕ :=
  (toCSPCode m n code).toCNF (circuitSem I acc)

/-- Exact binary-exponent shift accounting for unread inputs and reachable wires that do not appear
syntactically in `toCNFCode` (e.g. unconstrained outputs). -/
def freeShiftCode {σ : Signature} (I : Interpretation σ Bool) {m : ℕ}
    (acc : Fin m → Bool → Bool) (n : ℕ) (code : List (σ.Op × List ℕ) × List ℕ) : ℕ :=
  n + reachGateCountCode n code - (toCNFCode I acc n code).numVars

/-- Exact-multiplicity CNF formula compiled from `c : Circuit σ n m` along its reachable wires. -/
def toCNF {σ : Signature} {n m : ℕ} (c : Circuit σ n m) (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) : CNF ℕ :=
  toCNFCode I acc n c.code

/-- Unread-input / unconstrained-wire exponent shift accompanying `toCNF c I acc`. -/
def freeShift {σ : Signature} {n m : ℕ} (c : Circuit σ n m) (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) : ℕ :=
  freeShiftCode I acc n c.code

/-- Specialization of `toCNF` to 1-output `#Circuit-SAT` (accepting `true` at output `0`). -/
def toSatCNF {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (I : Interpretation σ Bool) : CNF ℕ :=
  toCNF c I (fun _ b => b)

/-- Specialization of `freeShift` to 1-output `#Circuit-SAT`. -/
def satFreeShift {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (I : Interpretation σ Bool) : ℕ :=
  freeShift c I (fun _ b => b)

/-! ### Local constraint semantics -/

private theorem eval_gateConstraint_eq_true_iff {σ : Signature} {m : ℕ}
    (I : Interpretation σ Bool) (acc : Fin m → Bool → Bool)
    {outWire : ℕ} {g : σ.Op × List ℕ} (hlen : g.2.length = σ.Arity g.1) (τ : ℕ → Bool) :
    Cslib.Logic.PL.Constraint.eval (circuitSem I acc) τ (Sum.inl g.1, outWire :: g.2) = true ↔
      τ outWire = I g.1 (fun a => τ (g.2[a.val]'(a.isLt.trans_eq hlen.symm))) := by
  simp only [Cslib.Logic.PL.Constraint.eval, List.map_cons, circuitSem, List.length_map, hlen,
    decide_true, Bool.true_and, beq_iff_eq]
  refine ⟨fun h => h.trans (congrArg (I g.1) (funext fun a => ?_)),
    fun h => h.trans (congrArg (I g.1) (funext fun a => ?_))⟩
  · have ha : a.val < g.2.length := a.isLt.trans_eq hlen.symm
    simp [List.getD_eq_getElem?_getD, ha]
  · have ha : a.val < g.2.length := a.isLt.trans_eq hlen.symm
    simp [List.getD_eq_getElem?_getD, ha]

/-! ### Equivalence of `reachWiresCode` and `Compiler.Reach` -/

private theorem mem_foldl_reachStep_of_mem {σ : Signature} (n : ℕ)
    (l : List ((σ.Op × List ℕ) × ℕ)) (seen : List ℕ) {i : ℕ} (hi : i ∈ seen) :
    i ∈ l.foldl (reachStep n) seen := by
  induction l generalizing seen with
  | nil => exact hi
  | cons gj l ih =>
    apply ih
    unfold reachStep
    split_ifs
    · exact List.mem_append_right _ hi
    · exact hi

private theorem mem_reachWiresCode_iff {σ : Signature} {n m : ℕ} (c : Circuit σ n m) (i : ℕ) :
    i ∈ reachWiresCode n c.code ↔ ∃ w : Wire n c.size, w.toNat = i ∧ Reach c w := by
  have hcode1 : c.code.1 = List.ofFn fun j : Fin c.size => (c.program.lines j).code :=
    Program.code_eq_ofFn_lines c.program
  let L : List ((σ.Op × List ℕ) × ℕ) := c.code.1.zipIdx.reverse
  have hL_len : L.length = c.size := by simp [L]
  constructor
  · -- Soundness: every wire in `reachWiresCode` is reachable in `c`.
    suffices hsound : ∀ (l : List ((σ.Op × List ℕ) × ℕ)) (seen : List ℕ),
        (∀ gj ∈ l, ∃ j : Fin c.size, gj = ((c.program.lines j).code, j.val)) →
        (∀ x ∈ seen, ∃ w : Wire n c.size, w.toNat = x ∧ Reach c w) →
        ∀ x ∈ l.foldl (reachStep n) seen, ∃ w : Wire n c.size, w.toNat = x ∧ Reach c w by
      exact hsound L c.code.2 (fun gj hgj => by
        simp only [L, List.mem_reverse, List.mem_zipIdx_iff_getElem?] at hgj
        obtain ⟨hj_lt, hget⟩ := List.getElem?_eq_some_iff.mp hgj
        have hj : gj.2 < c.size := by simpa using hj_lt
        refine ⟨⟨gj.2, hj⟩, Prod.ext ?_ rfl⟩
        have hget' : c.code.1[gj.2]'hj_lt = (c.program.lines ⟨gj.2, hj⟩).code := by
          simp [hcode1]
        exact hget.symm.trans hget') (fun x hx => by
        simp only [Circuit.code, List.mem_ofFn] at hx
        obtain ⟨o, rfl⟩ := hx
        exact ⟨c.outputs o, rfl, .output o⟩) i
    intro l
    induction l with
    | nil => intro seen _ hseen x hx; exact hseen x hx
    | cons gj l ih =>
      intro seen hl hseen
      apply ih _ (fun gj' hgj' => hl gj' (List.mem_cons_of_mem _ hgj'))
      obtain ⟨j, rfl⟩ := hl gj (List.mem_cons_self ..)
      intro x hx
      unfold reachStep at hx
      split_ifs at hx with hany
      · rcases List.mem_append.mp hx with harg | hprev
        · simp only [List.any_eq_true, beq_iff_eq] at hany
          obtain ⟨_, hmem, rfl⟩ := hany
          obtain ⟨w, hw_nat, hw_reach⟩ := hseen (n + j.val) hmem
          obtain rfl : w = .gate j := Wire.toNat_injective (hw_nat.trans rfl)
          simp only [Line.code, List.mem_ofFn] at harg
          obtain ⟨a, rfl⟩ := harg
          exact ⟨(c.program.lines j).wires a, rfl, .arg a hw_reach⟩
        · exact hseen x hprev
      · exact hseen x hx
  · -- Completeness: every `Reach c w` enters the backward fold before its consumers are passed.
    rintro ⟨w, rfl, hw⟩
    let accAt (t : ℕ) : List ℕ := (L.take t).foldl (reachStep n) c.code.2
    have hmono : ∀ {t₁ t₂ : ℕ}, t₁ ≤ t₂ → ∀ {x : ℕ}, x ∈ accAt t₁ → x ∈ accAt t₂ := by
      intro t₁ t₂ ht x hx
      have hsplit : L.take t₂ = L.take t₁ ++ (L.take t₂).drop t₁ := by
        conv_lhs => rw [← List.take_append_drop t₁ (L.take t₂), List.take_take,
          Nat.min_eq_left ht]
      dsimp only [accAt]
      rw [hsplit, List.foldl_append]
      exact mem_foldl_reachStep_of_mem n _ _ hx
    have hfull : accAt c.size = reachWiresCode n c.code := by
      dsimp only [accAt, reachWiresCode]
      rw [List.take_of_length_le hL_len.le]
    suffices hcomp : w.toNat ∈ accAt c.size ∧
        (∀ j : Fin c.size, w = .gate j → n + j.val ∈ accAt (c.size - 1 - j.val)) by
      exact hfull ▸ hcomp.1
    induction hw with
    | output o =>
      have h0 : (c.outputs o).toNat ∈ accAt 0 := by
        simp [accAt, Circuit.code]
      refine ⟨hmono (Nat.zero_le _) h0, fun j hj => ?_⟩
      have : (c.outputs o).toNat = n + j.val := by simp [hj]
      exact this ▸ hmono (Nat.zero_le _) h0
    | @arg k a hg ih =>
      have hk_mem : n + k.val ∈ accAt (c.size - 1 - k.val) := ih.2 k rfl
      set t := c.size - 1 - k.val
      have ht_lt : t < L.length := by rw [hL_len]; omega
      have hLt : L[t]'ht_lt = ((c.program.lines k).code, k.val) := by
        have hidx : c.code.1.zipIdx.length - 1 - t = k.val := by
          simp only [List.length_zipIdx, Circuit.length_code_fst]
          omega
        simp only [L, List.getElem_reverse]
        simp only [hidx, List.getElem_zipIdx, Nat.zero_add, Prod.mk.injEq, and_true]
        simp [hcode1]
      have hstep_mem : ((c.program.lines k).wires a).toNat ∈ accAt (t + 1) := by
        have htake : L.take (t + 1) = L.take t ++ [L[t]'ht_lt] :=
          List.take_succ_eq_append_getElem ht_lt
        have hstep_eq :
            accAt (t + 1) = reachStep n (accAt t) ((c.program.lines k).code, k.val) := by
          dsimp only [accAt]
          rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, hLt]
        rw [hstep_eq]
        unfold reachStep
        have hany : ((accAt t).any fun x => x == n + k.val) = true := by
          simp only [List.any_eq_true, beq_iff_eq]
          exact ⟨n + k.val, hk_mem, rfl⟩
        dsimp only
        rw [hany]
        exact List.mem_append_left _ (by simp [Line.code])
      refine ⟨hmono (by omega) hstep_mem, fun j hj => ?_⟩
      have hjk : j < k := Program.lt_of_lines_wires_eq_gate c.program k a j hj
      have ht_le : t + 1 ≤ c.size - 1 - j.val := by omega
      have hnat : ((c.program.lines k).wires a).toNat = n + j.val := by simp [hj]
      exact hnat ▸ hmono ht_le hstep_mem

/-! ### Structural bounds on `toCSP` and `toCNF` -/

section StructuralBounds

variable {σ : Signature} {n m : ℕ}

/-- Every constraint in `toCSP c` has scope length at most `k + 1` when `c.FanInAtMost k`. -/
theorem length_scope_le_of_mem_toCSP {c : Circuit σ n m} {k : ℕ} (hfan : c.FanInAtMost k)
    {con : Cslib.Logic.PL.Constraint (CircuitRel σ m) ℕ} (hcon : con ∈ toCSP c) :
    con.2.length ≤ k + 1 := by
  have hcode1 : c.code.1 = List.ofFn fun j : Fin c.size => (c.program.lines j).code :=
    Program.code_eq_ofFn_lines c.program
  simp only [toCSP, toCSPCode, List.mem_append] at hcon
  rcases hcon with hg | ho
  · simp only [List.mem_map, List.mem_filter, List.mem_zipIdx_iff_getElem?] at hg
    obtain ⟨⟨g, j⟩, ⟨hget, _⟩, rfl⟩ := hg
    obtain ⟨hj_lt, hgj⟩ := List.getElem?_eq_some_iff.mp hget
    have hj : j < c.size := by simpa using hj_lt
    have hg_eq : g = (c.program.lines ⟨j, hj⟩).code := by
      have hline : c.code.1[j]'hj_lt = (c.program.lines ⟨j, hj⟩).code := by simp [hcode1]
      exact hgj.symm.trans hline
    subst hg_eq
    have harity : σ.Arity (c.program.lines ⟨j, hj⟩).op ≤ k :=
      Program.fanInAtMost_iff.mp hfan ⟨j, hj⟩
    simp only [List.length_cons, Line.length_code_snd]
    omega
  · simp only [List.mem_map, List.mem_finRange, true_and] at ho
    obtain ⟨o, rfl⟩ := ho
    simp only [List.length_singleton]
    omega

/-- Every clause of `toCNF c I acc` has length at most `k + 1` when `c.FanInAtMost k`. -/
theorem length_le_of_mem_toCNF {c : Circuit σ n m} (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) {k : ℕ} (hfan : c.FanInAtMost k)
    {cl : Clause ℕ} (hcl : cl ∈ toCNF c I acc) :
    cl.length ≤ k + 1 :=
  CSP.length_clause_mem_toCNF (fun _ hcon => length_scope_le_of_mem_toCSP hfan hcon) hcl

/-- Every variable occurring in `toCSP c` belongs to `(reachWiresCode n c.code).toFinset`. -/
theorem vars_toCSP_subset (c : Circuit σ n m) :
    (toCSP c).vars.toFinset ⊆ (reachWiresCode n c.code).toFinset := by
  have hcode1 : c.code.1 = List.ofFn fun j : Fin c.size => (c.program.lines j).code :=
    Program.code_eq_ofFn_lines c.program
  intro v hv
  rw [List.mem_toFinset, CSP.vars, List.mem_flatMap] at hv
  rw [List.mem_toFinset, mem_reachWiresCode_iff]
  obtain ⟨con, hcon, hv_mem⟩ := hv
  simp only [toCSP, toCSPCode, List.mem_append] at hcon
  rcases hcon with hg | ho
  · simp only [List.mem_map, List.mem_filter, List.mem_zipIdx_iff_getElem?] at hg
    obtain ⟨⟨g, j⟩, ⟨hget, hreach⟩, rfl⟩ := hg
    obtain ⟨hj_lt, hgj⟩ := List.getElem?_eq_some_iff.mp hget
    have hj : j < c.size := by simpa using hj_lt
    have hg_eq : g = (c.program.lines ⟨j, hj⟩).code := by
      have hline : c.code.1[j]'hj_lt = (c.program.lines ⟨j, hj⟩).code := by simp [hcode1]
      exact hgj.symm.trans hline
    subst hg_eq
    simp only [List.any_eq_true, beq_iff_eq] at hreach
    obtain ⟨_, hmem_r, rfl⟩ := hreach
    obtain ⟨w, hw_nat, hw_reach⟩ := (mem_reachWiresCode_iff c (n + j)).mp hmem_r
    obtain rfl : w = .gate ⟨j, hj⟩ := Wire.toNat_injective (hw_nat.trans rfl)
    simp only [List.mem_cons] at hv_mem
    rcases hv_mem with rfl | harg
    · exact ⟨.gate ⟨j, hj⟩, rfl, hw_reach⟩
    · simp only [Line.code, List.mem_ofFn] at harg
      obtain ⟨a, rfl⟩ := harg
      exact ⟨(c.program.lines ⟨j, hj⟩).wires a, rfl, .arg a hw_reach⟩
  · simp only [List.mem_map, List.mem_finRange, true_and] at ho
    obtain ⟨o, rfl⟩ := ho
    simp only [List.mem_singleton] at hv_mem
    subst hv_mem
    have hget : c.code.2.getD o.val 0 = (c.outputs o).toNat := by simp [Circuit.code]
    exact ⟨c.outputs o, hget.symm, .output o⟩

/-- Every variable occurring in `toCNF c I acc` belongs to `(reachWiresCode n c.code).toFinset`. -/
theorem vars_toCNF_subset (c : Circuit σ n m) (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) :
    (toCNF c I acc).vars.toFinset ⊆ (reachWiresCode n c.code).toFinset := by
  intro v hv
  exact vars_toCSP_subset c (List.mem_toFinset.mpr (CSP.mem_vars_toCNF (List.mem_toFinset.mp hv)))

/-- `(reachWiresCode n c.code).toFinset` has cardinality `Nat.card (Signal c)`. -/
theorem card_reachWiresCode_toFinset (c : Circuit σ n m) :
    (reachWiresCode n c.code).toFinset.card = Nat.card (Signal c) := by
  let e : Signal c ≃ {i : ℕ // i ∈ (reachWiresCode n c.code).toFinset} :=
    { toFun := fun w => ⟨w.1.toNat,
        List.mem_toFinset.mpr ((mem_reachWiresCode_iff c w.1.toNat).mpr ⟨w.1, rfl, w.2⟩)⟩
      invFun := fun i =>
        let hlt : i.1 < n + c.size := by
          obtain ⟨w, hw_eq, _⟩ := (mem_reachWiresCode_iff c i.1).mp (List.mem_toFinset.mp i.2)
          exact hw_eq ▸ w.toNat_lt
        ⟨Wire.ofNat i.1 hlt, by
          obtain ⟨w, hw_eq, hw⟩ := (mem_reachWiresCode_iff c i.1).mp (List.mem_toFinset.mp i.2)
          have hof : Wire.ofNat i.1 hlt = w := by
            apply Wire.toNat_injective
            simp [hw_eq]
          exact hof.symm ▸ hw⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun i => Subtype.ext (by simp) }
  calc (reachWiresCode n c.code).toFinset.card
      = Fintype.card {i : ℕ // i ∈ (reachWiresCode n c.code).toFinset} :=
        (Fintype.card_coe _).symm
    _ = Nat.card {i : ℕ // i ∈ (reachWiresCode n c.code).toFinset} :=
        Nat.card_eq_fintype_card.symm
    _ = Nat.card (Signal c) := Nat.card_congr e.symm

/-- When `c.FanInAtMost k`, `toCNF c I acc` uses at most `k * c.size + m` distinct variables. -/
theorem numVars_toCNF_le {c : Circuit σ n m} (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) {k : ℕ} (hfan : c.FanInAtMost k) :
    (toCNF c I acc).numVars ≤ k * c.size + m := by
  calc (toCNF c I acc).numVars
      ≤ (reachWiresCode n c.code).toFinset.card :=
        Finset.card_le_card (vars_toCNF_subset c I acc)
    _ = Nat.card (Signal c) := card_reachWiresCode_toFinset c
    _ ≤ k * c.size + m := card_signal_le hfan

/-- `toCNF c I acc` uses at most `n + c.size` distinct variables (all wire numbers lie below
`n + c.size`). -/
theorem numVars_toCNF_le_add_size (c : Circuit σ n m) (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) :
    (toCNF c I acc).numVars ≤ n + c.size := by
  have hsub : (reachWiresCode n c.code).toFinset ⊆ Finset.range (n + c.size) := by
    intro i hi
    obtain ⟨w, rfl, _⟩ := (mem_reachWiresCode_iff c i).mp (List.mem_toFinset.mp hi)
    exact Finset.mem_range.mpr w.toNat_lt
  calc (toCNF c I acc).numVars
      ≤ (reachWiresCode n c.code).toFinset.card :=
        Finset.card_le_card (vars_toCNF_subset c I acc)
    _ ≤ (Finset.range (n + c.size)).card := Finset.card_le_card hsub
    _ = n + c.size := Finset.card_range _

end StructuralBounds

/-! ### Exact counting through `Compiler.network` -/

section ExactCounting

variable {σ : Signature} {n m : ℕ}

private def accSet (acc : Fin m → Bool → Bool) (o : Fin m) : Set Bool :=
  {b | acc o b = true}

private theorem reachGateCountCode_eq_card_filter (c : Circuit σ n m) :
    reachGateCountCode n c.code =
      ((reachWiresCode n c.code).toFinset.filter (n ≤ ·)).card := by
  classical
  let S := (reachWiresCode n c.code).toFinset
  let p (j : Fin c.size) : Bool := (reachWiresCode n c.code).any (· == n + j.val)
  have hp_iff (j : Fin c.size) : p j = true ↔ Reach c (.gate j) := by
    simp only [p, List.any_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨_, hmem, rfl⟩
      obtain ⟨w, hw_nat, hw_reach⟩ := (mem_reachWiresCode_iff c (n + j.val)).mp hmem
      obtain rfl : w = .gate j := Wire.toNat_injective (hw_nat.trans rfl)
      exact hw_reach
    · intro hr
      exact ⟨n + j.val, (mem_reachWiresCode_iff c (n + j.val)).mpr ⟨.gate j, rfl, hr⟩, rfl⟩
  have hcount : reachGateCountCode n c.code =
      (Finset.univ.filter fun j : Fin c.size => p j = true).card := by
    have hzip : c.code.1.zipIdx =
        (List.finRange c.size).map fun j => ((c.program.lines j).code, j.val) := by
      apply List.ext_getElem (by simp)
      intro idx h1 h2
      have hcode1 : c.code.1 = List.ofFn fun j : Fin c.size => (c.program.lines j).code :=
        Program.code_eq_ofFn_lines c.program
      simp [hcode1]
    rw [reachGateCountCode, hzip, List.countP_map, Function.comp_def]
    change (List.finRange c.size).countP p = _
    rw [List.countP_eq_length_filter]
    have hnodup : ((List.finRange c.size).filter p).Nodup :=
      (List.nodup_finRange c.size).filter p
    rw [← List.toFinset_card_of_nodup hnodup]
    congr 1
    ext j
    simp
  rw [hcount]
  refine Finset.card_bij (fun (j : Fin c.size) _ => n + j.val)
    (fun j hj => ?_) (fun j₁ _ j₂ _ h => Fin.ext (by omega)) (fun i hi => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp_iff] at hj
    simp only [Finset.mem_filter, List.mem_toFinset, mem_reachWiresCode_iff]
    exact ⟨⟨.gate j, rfl, hj⟩, Nat.le_add_right n j.val⟩
  · simp only [Finset.mem_filter, List.mem_toFinset, mem_reachWiresCode_iff] at hi
    obtain ⟨⟨w, rfl, hw⟩, hge⟩ := hi
    cases w with
    | input idx => exact absurd hge (not_le.mpr idx.isLt)
    | gate j =>
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, (hp_iff j).mpr hw⟩, rfl⟩

private theorem eval_toCSP_iff_satisfies_network (c : Circuit σ n m) (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) (τ : ℕ → Bool) :
    (toCSP c).eval (circuitSem I acc) τ = true ↔
      (network c I (accSet acc)).Satisfies (fun i => τ i.val)
        (fun e => τ e.signal.1.toNat) := by
  have hcode1 : c.code.1 = List.ofFn fun j : Fin c.size => (c.program.lines j).code :=
    Program.code_eq_ofFn_lines c.program
  have hout_iff :
      (∀ con ∈ (List.finRange m).map (fun o => (Sum.inr o, [c.code.2.getD o.val 0])),
        Cslib.Logic.PL.Constraint.eval (circuitSem I acc) τ con = true) ↔
        ∀ o : Fin m, acc o (τ (c.outputs o).toNat) = true := by
    simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, Cslib.Logic.PL.Constraint.eval, List.map_singleton, circuitSem]
    refine forall_congr' fun o => ?_
    have hget : c.code.2.getD o.val 0 = (c.outputs o).toNat := by simp [Circuit.code]
    rw [hget]
  rw [CSP.eval, toCSP, toCSPCode, List.all_append, Bool.and_eq_true, List.all_map,
    List.all_eq_true, List.all_eq_true, hout_iff]
  simp only [Function.comp_def, List.mem_filter, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨hgates, houts⟩ v
    cases v with
    | signal w =>
      obtain ⟨w, hw⟩ := w
      cases w with
      | input i => rfl
      | gate g =>
        have hmem_r : n + g.val ∈ reachWiresCode n c.code :=
          (mem_reachWiresCode_iff c (n + g.val)).mpr ⟨.gate g, rfl, hw⟩
        have hany : ((reachWiresCode n c.code).any fun x => x == n + g.val) = true := by
          simp only [List.any_eq_true, beq_iff_eq]
          exact ⟨n + g.val, hmem_r, rfl⟩
        have hg_lt : g.val < c.code.1.length := by simp [g.isLt]
        have hget : c.code.1[g.val]? = some (c.program.lines g).code := by
          rw [List.getElem?_eq_getElem hg_lt]
          simp [hcode1]
        have hcl := hgates ((c.program.lines g).code, g.val) ⟨hget, hany⟩
        have heq := (eval_gateConstraint_eq_true_iff I acc (Line.length_code_snd _) τ).mp hcl
        dsimp only at heq
        refine heq.trans (congrArg (I (c.program.lines g).op) (funext fun a => ?_))
        simp only [Line.code, List.getElem_ofFn, argEdge, signal_deliverEdge, consumed]
        rfl
    | junction j =>
      intro e he
      rcases e with ⟨_, ⟨k, _⟩⟩ | j'
      · cases k with
        | zero => cases he
        | succ _ => cases he; rfl
      · cases he; rfl
    | output o =>
      change τ (outEdge c o).signal.1.toNat ∈ accSet acc o
      rw [signal_deliverEdge]
      exact houts o
  · intro hsat
    refine ⟨fun ⟨g, j⟩ ⟨hget, hany⟩ => ?_, fun o => ?_⟩
    · obtain ⟨hj_lt, hgj⟩ := List.getElem?_eq_some_iff.mp hget
      have hj : j < c.size := by simpa using hj_lt
      have hg_eq : g = (c.program.lines ⟨j, hj⟩).code := by
        have hline : c.code.1[j]'hj_lt = (c.program.lines ⟨j, hj⟩).code := by simp [hcode1]
        exact hgj.symm.trans hline
      subst hg_eq
      simp only [List.any_eq_true, beq_iff_eq] at hany
      obtain ⟨_, hmem_r, rfl⟩ := hany
      obtain ⟨w, hw_nat, hw_reach⟩ := (mem_reachWiresCode_iff c (n + j)).mp hmem_r
      obtain rfl : w = .gate ⟨j, hj⟩ := Wire.toNat_injective (hw_nat.trans rfl)
      rw [eval_gateConstraint_eq_true_iff I acc (Line.length_code_snd _) τ]
      have hsig : τ (n + j) =
          I (c.program.lines ⟨j, hj⟩).op (fun a => τ (argEdge hw_reach a).signal.1.toNat) :=
        hsat (.signal ⟨.gate ⟨j, hj⟩, hw_reach⟩)
      refine hsig.trans (congrArg (I (c.program.lines ⟨j, hj⟩).op) (funext fun a => ?_))
      simp only [Line.code, List.getElem_ofFn, argEdge, signal_deliverEdge, consumed]
    · have hout : τ (outEdge c o).signal.1.toNat ∈ accSet acc o := hsat (.output o)
      rwa [signal_deliverEdge] at hout

private theorem eval_toCNF_iff_satisfies_network (c : Circuit σ n m) (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) (τ : ℕ → Bool) :
    (toCNF c I acc).eval τ = true ↔
      (network c I (accSet acc)).Satisfies (fun i => τ i.val)
        (fun e => τ e.signal.1.toNat) := by
  change ((toCSP c).toCNF (circuitSem I acc)).eval τ = true ↔ _
  rw [CSP.eval_toCNF, eval_toCSP_iff_satisfies_network]

/-- **Exact counting via `Compiler.network`.** For every circuit `c : Circuit σ n m`,
interpretation `I`, and output predicate `acc`, the number of accepted inputs equals
`2 ^ freeShift c I acc * (toCNF c I acc).modelCount`. -/
theorem acceptCount_eq_two_pow_freeShift_mul_modelCount (c : Circuit σ n m)
    (I : Interpretation σ Bool) (acc : Fin m → Bool → Bool) :
    c.acceptCount I acc = 2 ^ freeShift c I acc * (toCNF c I acc).modelCount := by
  classical
  let S : Finset ℕ := (reachWiresCode n c.code).toFinset
  let R : Finset (Fin n) := Finset.univ.filter fun i : Fin n => Reach c (.input i)
  let N := network c I (accSet acc)
  let extendS (τ : S → Bool) (v : ℕ) : Bool := if h : v ∈ S then τ ⟨v, h⟩ else false
  let extendR (x₀ : R → Bool) (i : Fin n) : Bool := if h : i ∈ R then x₀ ⟨i, h⟩ else false
  have hmemS_input (i : Fin n) : i.val ∈ S ↔ i ∈ R := by
    simp only [S, R, List.mem_toFinset, mem_reachWiresCode_iff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨fun ⟨w, hw_nat, hw_reach⟩ =>
        (Wire.toNat_injective (hw_nat.trans rfl) : w = .input i) ▸ hw_reach,
      fun hr => ⟨.input i, rfl, hr⟩⟩
  -- Step 1: `modelCountOn S` counts accepted restricted inputs on `R`.
  have hmodelOn : (toCNF c I acc).modelCountOn S =
      (Finset.univ.filter fun x₀ : R → Bool => extendR x₀ ∈ N.accepted).card := by
    let toR (τ : S → Bool) (i : R) : Bool :=
      τ ⟨i.1.val, (hmemS_input i.1).mpr i.2⟩
    have hext_eq (τ : S → Bool) (i : Fin n) : extendR (toR τ) i = extendS τ i.val := by
      by_cases hi : i ∈ R
      · have hiS : i.val ∈ S := (hmemS_input i).mpr hi
        simp [extendR, extendS, toR, hi, hiS]
      · have hiS : i.val ∉ S := fun h => hi ((hmemS_input i).mp h)
        simp [extendR, extendS, hi, hiS]
    refine Finset.card_bij (fun τ _ => toR τ) (fun τ hτ => ?_) (fun τ₁ h₁ τ₂ h₂ h => ?_)
      (fun x₀ hx₀ => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      have hsat := (eval_toCNF_iff_satisfies_network c I acc (extendS τ)).mp hτ
      have hfun : (fun i : Fin n => extendS τ i.val) = extendR (toR τ) :=
        funext fun i => (hext_eq τ i).symm
      rw [hfun] at hsat
      exact ⟨_, hsat⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      have hsat₁ := (eval_toCNF_iff_satisfies_network c I acc (extendS τ₁)).mp h₁
      have hsat₂ := (eval_toCNF_iff_satisfies_network c I acc (extendS τ₂)).mp h₂
      have hfun₁ : (fun i : Fin n => extendS τ₁ i.val) = extendR (toR τ₁) :=
        funext fun i => (hext_eq τ₁ i).symm
      have hfun₂ : (fun i : Fin n => extendS τ₂ i.val) = extendR (toR τ₂) :=
        funext fun i => (hext_eq τ₂ i).symm
      rw [hfun₁] at hsat₁
      rw [hfun₂, ← h] at hsat₂
      funext ⟨v, hv⟩
      obtain ⟨w, rfl, hw⟩ := (mem_reachWiresCode_iff c v).mp (List.mem_toFinset.mp hv)
      have he₁ := eq_trace hsat₁ (head ⟨w, hw⟩)
      have he₂ := eq_trace hsat₂ (head ⟨w, hw⟩)
      simpa only [signal_head, extendS, hv, ↓reduceDIte] using he₁.trans he₂.symm
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₀
      have hacc : ∀ o, c.eval I (extendR x₀) o ∈ accSet acc o := by
        have hx' : extendR x₀ ∈ (network c I (accSet acc)).accepted := hx₀
        rwa [accepted_network] at hx'
      let τ : S → Bool := fun v =>
        let hlt : v.1 < n + c.size := by
          obtain ⟨w, hw_eq, _⟩ := (mem_reachWiresCode_iff c v.1).mp (List.mem_toFinset.mp v.2)
          exact hw_eq ▸ w.toNat_lt
        c.program.trace I (extendR x₀) (Wire.ofNat v.1 hlt)
      have hτ_wire (w : Signal c) :
          extendS τ w.1.toNat = c.program.trace I (extendR x₀) w.1 := by
        have hwS : w.1.toNat ∈ S :=
          List.mem_toFinset.mpr ((mem_reachWiresCode_iff c w.1.toNat).mpr ⟨w.1, rfl, w.2⟩)
        simp [extendS, hwS, τ]
      have htoR : toR τ = x₀ := by
        funext ⟨i, hi⟩
        have hiR : Reach c (.input i) := (Finset.mem_filter.mp hi).2
        have := hτ_wire ⟨.input i, hiR⟩
        simpa [extendS, (hmemS_input i).mpr hi, extendR, hi, toR] using this
      refine ⟨τ, ?_, htoR⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [eval_toCNF_iff_satisfies_network]
      have hfun : (fun i : Fin n => extendS τ i.val) = extendR x₀ := by
        rw [← htoR]
        exact funext fun i => (hext_eq τ i).symm
      have hedge : (fun e : Edge c => extendS τ e.signal.1.toNat) =
          fun e => c.program.trace I (extendR x₀) e.signal.1 :=
        funext fun e => hτ_wire e.signal
      rw [hfun, hedge]
      exact satisfies_trace hacc
  -- Step 2: Unread inputs outside `R` contribute `2 ^ (n - R.card)` via `N.dependsOn_read`.
  have haccept : c.acceptCount I acc = 2 ^ (n - R.card) * (toCNF c I acc).modelCountOn S := by
    let split : (Fin n → Bool) ≃ (R → Bool) × ({i : Fin n // i ∉ R} → Bool) :=
      Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ R) (fun _ => Bool)
    have hdep (x : Fin n → Bool) :
        (∀ o, acc o (c.eval I x o) = true) ↔ extendR (split x).1 ∈ N.accepted := by
      have hacc_iff : (∀ o, acc o (c.eval I x o) = true) ↔ x ∈ N.accepted := by
        rw [accepted_network]
        rfl
      rw [hacc_iff]
      refine Eq.to_iff (N.dependsOn_read fun i hi => ?_)
      obtain ⟨v, _, hsite⟩ := hi
      obtain ⟨hreach, _⟩ := site_eq_some hsite
      have hiR : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hreach⟩
      simp [extendR, split, hiR]
    let bij : {x : Fin n → Bool // ∀ o : Fin m, acc o (c.eval I x o) = true} ≃
        {x₀ : R → Bool // extendR x₀ ∈ N.accepted} × ({i : Fin n // i ∉ R} → Bool) :=
      { toFun := fun x => (⟨(split x.1).1, (hdep x.1).mp x.2⟩, (split x.1).2)
        invFun := fun p =>
          ⟨split.symm (p.1.1, p.2), by
            rw [hdep, Equiv.apply_symm_apply]
            exact p.1.2⟩
        left_inv := fun x => Subtype.ext (split.symm_apply_apply x.1)
        right_inv := fun p => by simp only [Equiv.apply_symm_apply] }
    have hcard := Fintype.card_congr bij
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
      Fintype.card_fin, Fintype.card_coe] at hcard
    rw [Circuit.acceptCount, ← Fintype.card_subtype, hcard, Fintype.card_subtype, ← hmodelOn,
      Nat.mul_comm]
  -- Step 3: Combine `2 ^ (n - R.card)` with `CNF.modelCountOn_eq_mul_modelCount` on `S`.
  rw [haccept, CNF.modelCountOn_eq_mul_modelCount _ S (vars_toCNF_subset c I acc), ← mul_assoc,
    ← pow_add]
  suffices hexp : n - R.card + (S.card - (toCNF c I acc).numVars) = freeShift c I acc by
    rw [hexp]
  have hS_split : S.card = (S.filter (· < n)).card + (S.filter (n ≤ ·)).card := by
    have hdisj : Disjoint (S.filter (· < n)) (S.filter (n ≤ ·)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases lt_or_ge x n with hlt | hge
    · simp [hlt, not_le.mpr hlt]
    · simp [hge, not_lt.mpr hge]
  have hR_card : (S.filter (· < n)).card = R.card := by
    refine Finset.card_bij (fun (i : ℕ) hi => ⟨i, (Finset.mem_filter.mp hi).2⟩)
      (fun i hi => ?_) (fun _ _ _ _ h => Fin.mk.inj_iff.mp h) (fun i hi => ?_)
    · exact (hmemS_input ⟨i, (Finset.mem_filter.mp hi).2⟩).mp (Finset.mem_filter.mp hi).1
    · exact ⟨i.val, Finset.mem_filter.mpr ⟨(hmemS_input i).mpr hi, i.isLt⟩, rfl⟩
  have hgate_card : reachGateCountCode n c.code = (S.filter (n ≤ ·)).card :=
    reachGateCountCode_eq_card_filter c
  have hR_le : R.card ≤ n := by
    simpa using Finset.card_le_univ R
  have hnum_le : (toCNF c I acc).numVars ≤ S.card :=
    Finset.card_le_card (vars_toCNF_subset c I acc)
  simp only [freeShift, freeShiftCode, toCNF] at hnum_le ⊢
  omega

/-- Single-output `#Circuit-SAT` specialization of
`acceptCount_eq_two_pow_freeShift_mul_modelCount`. -/
theorem satCount_eq_two_pow_satFreeShift_mul_modelCount (c : Circuit σ n 1)
    (I : Interpretation σ Bool) :
    c.satCount I = 2 ^ satFreeShift c I * (toSatCNF c I).modelCount := by
  rw [c.satCount_eq_acceptCount I]
  exact acceptCount_eq_two_pow_freeShift_mul_modelCount c I (fun _ b => b)

/-- `toCNF c I acc` is satisfiable iff `c` has an input accepted by `acc`. -/
theorem satisfiable_toCNF_iff (c : Circuit σ n m) (I : Interpretation σ Bool)
    (acc : Fin m → Bool → Bool) :
    (toCNF c I acc).Satisfiable ↔
      ∃ x : Fin n → Bool, ∀ o, acc o (c.eval I x o) = true := by
  rw [← CNF.modelCount_pos_iff]
  have hcnt := acceptCount_eq_two_pow_freeShift_mul_modelCount c I acc
  have hpos_acc : 0 < c.acceptCount I acc ↔
      ∃ x : Fin n → Bool, ∀ o, acc o (c.eval I x o) = true := by
    simp only [Circuit.acceptCount, Finset.card_pos, Finset.Nonempty, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [← hpos_acc, hcnt]
  exact ⟨fun h => mul_pos (pow_pos Nat.zero_lt_two _) h,
    fun h => Nat.pos_of_mul_pos_left h⟩

/-- `toSatCNF c I` is satisfiable iff `⟨n, c⟩ ∈ SignatureCircuitSAT I`. -/
theorem satisfiable_toSatCNF_iff (c : Circuit σ n 1) (I : Interpretation σ Bool) :
    (toSatCNF c I).Satisfiable ↔
      (⟨n, c⟩ : Σ n, Circuit σ n 1) ∈ Cslib.Complexity.SignatureCircuitSAT I := by
  rw [toSatCNF, satisfiable_toCNF_iff]
  exact exists_congr fun x =>
    ⟨fun h => h 0, fun h o => Subsingleton.elim (0 : Fin 1) o ▸ h⟩

end ExactCounting

end Cslib.Circuits.Frontier.Compiler
