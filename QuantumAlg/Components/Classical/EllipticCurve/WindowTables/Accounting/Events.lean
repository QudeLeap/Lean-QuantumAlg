/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Accounting
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Complete native event pools for table-program composition

These bounds retain the native operation labels and their widths. Sequential
and indexed composition only add independent component allowances. A row write
has one fixed vector-write coordinate, independent of its operands and index.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Accounting

open Execution
open scoped BigOperators

noncomputable section

variable {model : ExecutionModel}

/-- The complete native pool of a sequence is exactly the sum of its actual component pools. -/
lemma seq_pool {pre mid post : RuntimeCtx model.kind} {allocate : Bool}
    (first : Circuit model pre mid allocate) (second : Circuit model mid post allocate)
    (path : (first.seq second).Path) :
    (first.seq second).resourcePool path =
      first.resourcePool path.1 + second.resourcePool path.2 := by
  change ResourcePool.ofList (_ ++ _) = _
  exact ResourcePool.ofList_append _ _

/-- Every actual sequential path pays both complete component event pools. -/
lemma seq_pool_le {pre mid post : RuntimeCtx model.kind} {allocate : Bool}
    (first : Circuit model pre mid allocate) (second : Circuit model mid post allocate)
    (firstBudget secondBudget : ResourcePool model) (path : (first.seq second).Path)
    (firstBound : first.resourcePool path.1 ≤ firstBudget)
    (secondBound : second.resourcePool path.2 ≤ secondBudget) :
    (first.seq second).resourcePool path ≤ firstBudget + secondBudget := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add firstBound secondBound

/-- A symbolic finite repetition retains each component's complete native labels. -/
lemma range_pool_le {ctx : RuntimeCtx model.kind} {allocate : Bool} (count : Nat)
    (body : Fin count → Circuit model ctx ctx allocate) (budget : ResourcePool model)
    (bounded : ∀ index path, (body index).resourcePool path ≤ budget)
    (path : (Circuit.forRange count body).Path) :
    (Circuit.forRange count body).resourcePool path ≤ count • budget := by
  have bound := Circuit.forRange_pool_le_sum count body (fun _ => budget) bounded path
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using bound

/-- The independent coordinate of one actual existing-array row overwrite. -/
def rowWriteEnvelope (model : ExecutionModel) [BitWord.Selected model] (width length : Nat) :
    ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.vector .write length width)))

/-- The row's data and its static index do not alter the charged native operation. -/
lemma rowWrite_pool [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    {width length : Nat} (array : CWriteRef ctx (.fixedVector length (.unsignedWord width)))
    (index : Fin length) (input : CInputRef ctx (.unsignedWord width))
    (path : (BitWord.instruction (execution := model) (rowWriteOp array index input)).Path) :
    (BitWord.instruction (execution := model) (rowWriteOp array index input)).resourcePool path =
      rowWriteEnvelope model width length := by
  rw [Circuit.resourcePool, BitWord.bitWord_instruction_eventTrace]
  rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Accounting
