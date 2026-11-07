import Complexity.Computability.Complexity.Classes.P.FirstOrder
import Mathlib.ModelTheory.Graph

/-! Executable ordered FO(LFP) clients: genuine iteration, nested binders, captured parameters,
numeric atoms, nullary tables, and rejection of malformed or undersized inputs. -/

open FirstOrder Language Cslib.Logic Cslib.Logic.FO

namespace ComplexityTests.FOLeastFixedPointPolyTime

private abbrev L := Ordered.language Language.empty

private def vocabulary : Vocabulary Language.empty where
  count := 0
  symbol := Equiv.equivOfIsEmpty _ _

private def truth : LFP.RawFormula L [] Empty := .ofFO ⊤

example : LFP.ModelChecker.modelChecker vocabulary truth (2, []) = true := by decide
example : LFP.ModelChecker.modelChecker vocabulary truth (0, []) = false := by decide
example : LFP.ModelChecker.modelChecker vocabulary truth (1, []) = false := by decide
example : LFP.ModelChecker.modelChecker vocabulary truth (2, [ [true] ]) = false := by decide

-- Every relation is a fixed point of the identity operator; its least fixed point is empty.
private def identity : LFP.RawFormula L [] Empty :=
  LFP.lfp (.rel .here ![.var (.inr 0)]) ![Ordered.zero Language.empty]

example : LFP.ModelChecker.modelChecker vocabulary identity (2, []) = false := by decide

-- The second disjunct becomes true only after the first stage inserts zero.
private def grow : LFP.RawFormula L [1] (Empty ⊕ Fin 1) :=
  .disj (.ofFO ((Term.var (.inr 0)).equal (Ordered.zero Language.empty)))
    (.conj (.rel .here ![Ordered.zero Language.empty])
      (.ofFO ((Term.var (.inr 0)).equal (Ordered.one Language.empty))))

private def reachesOne : LFP.RawFormula L [] Empty :=
  LFP.lfp grow ![Ordered.one Language.empty]

private def reachesMax : LFP.RawFormula L [] Empty :=
  LFP.lfp grow ![Ordered.max Language.empty]

example : reachesOne.wellFormed LFP.policy = true := by decide
example : LFP.ModelChecker.modelChecker vocabulary reachesOne (2, []) = true := by decide
example : LFP.ModelChecker.modelChecker vocabulary reachesMax (2, []) = true := by decide
example : LFP.ModelChecker.modelChecker vocabulary reachesMax (3, []) = false := by decide

-- The inner binder reads the outer approximation through `there here`.
private def nested : LFP.RawFormula L [] Empty :=
  LFP.lfp
    (LFP.lfp
      (.disj (.ofFO ((Term.var (.inr 0)).equal (Ordered.zero Language.empty)))
        (.rel (.there .here) ![Ordered.zero Language.empty]))
      ![.var (.inr 0)])
    ![Ordered.one Language.empty]

example : nested.wellFormed LFP.policy = true := by decide
example : LFP.ModelChecker.modelChecker vocabulary nested (2, []) = true := by decide

private def parameter : LFP.RawFormula L [] Bool :=
  LFP.lfp (.ofFO ((Term.var (.inr 0)).equal (.var (.inl false)))) ![.var true]

example : LFP.ModelChecker.eval vocabulary parameter (2, []) []
    (fun b => if b then 1 else 0) = false := by decide
example : LFP.ModelChecker.eval vocabulary parameter (2, []) [] (fun _ => 0) = true := by decide

-- The table of a nullary relation still has one bit when the domain is empty.
private def nullary : LFP.RawFormula L [] Empty := LFP.lfp (.ofFO ⊤) Fin.elim0

example : LFP.ModelChecker.eval vocabulary nullary (0, []) [] Empty.elim = true := by decide

private def numeric : LFP.RawFormula L [] Empty :=
  .ofFO (Ordered.bit Language.empty (Ordered.max Language.empty) (Ordered.one Language.empty))

example : LFP.ModelChecker.modelChecker vocabulary numeric (2, []) = false := by decide
example : LFP.ModelChecker.modelChecker vocabulary numeric (3, []) = true := by decide

private def quantified : LFP.RawFormula L [] Empty :=
  .ex (.ofFO (Ordered.bit Language.empty (.var none) (Ordered.one Language.empty)))

example : LFP.ModelChecker.modelChecker vocabulary quantified (2, []) = false := by decide
example : LFP.ModelChecker.modelChecker vocabulary quantified (3, []) = true := by decide

private def bounded : LFP.RawFormula L [] Empty :=
  .ofFO (.all (.rel (.inr .le) ![.var (.inr 0), Ordered.max Language.empty]))

example : LFP.ModelChecker.modelChecker vocabulary bounded (2, []) = true := by decide

private def graphVocabulary : Vocabulary Language.graph where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨2, FirstOrder.Language.adj⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun ⟨_, .adj⟩ => rfl }

private def forwardEdge : LFP.RawFormula (Ordered.language Language.graph) [] Empty :=
  .ofFO (Relations.formula₂ (.inl FirstOrder.Language.adj)
    (Ordered.zero Language.graph) (Ordered.max Language.graph))

private def backwardEdge : LFP.RawFormula (Ordered.language Language.graph) [] Empty :=
  .ofFO (Relations.formula₂ (.inl FirstOrder.Language.adj)
    (Ordered.max Language.graph) (Ordered.zero Language.graph))

-- The first coordinate is the least significant truth-table digit.
example : LFP.ModelChecker.modelChecker graphVocabulary forwardEdge
    (2, [ [false, false, true, false] ]) = true := by decide
example : LFP.ModelChecker.modelChecker graphVocabulary backwardEdge
    (2, [ [false, false, true, false] ]) = false := by decide

-- The native machine certificate is discoverable by the usual automation.
example : Turing.MultiTapeTM.ComputableInPolyTime
    (LFP.ModelChecker.modelChecker vocabulary nested) encStructure Turing.MultiTapeTM.encBool := by
  fun_prop

end ComplexityTests.FOLeastFixedPointPolyTime
