import CslibFrontier.Computability.Complexity.Classes.ModP.Composite

namespace Cslib.Complexity.Tests

variable {α : Type} {enc : α ↪ List Bool}

example (A B : Set α) (hA : A ∈ ParityP enc) (hB : B ∈ ModP 3 enc) : A ∪ B ∈ ModP 6 enc := by
  have hA2 : A ∈ ModP 2 enc := ModP_two ▸ hA
  have hA6 : A ∈ ModP 6 enc := ModP_subset_ModP_of_dvd (by decide) (by decide) hA2
  have hB6 : B ∈ ModP 6 enc := ModP_subset_ModP_of_dvd (by decide) (by decide) hB
  exact supClosed_ModP 6 hA6 hB6

example (A B : Set α) (hA : A ∈ ModP 6 enc) (hB : B ∈ ModP 6 enc) : A ∪ B ∈ ModP 6 enc :=
  supClosed_ModP 6 hA hB

example (A B : Set α) (hA : A ∈ ModP 0 enc) (hB : B ∈ ModP 0 enc) : A ∪ B ∈ ModP 0 enc :=
  supClosed_ModP 0 hA hB

example (A B : Set α) (hA : A ∈ ModP 1 enc) (hB : B ∈ ModP 1 enc) : A ∪ B ∈ ModP 1 enc :=
  supClosed_ModP 1 hA hB

end Cslib.Complexity.Tests
