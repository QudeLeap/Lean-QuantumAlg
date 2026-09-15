/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Permutation.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# The same actual unitary instruction in permuted entry coordinates

Logical coordinates follow the identical physical wires. The existing
zero-event identity suffix gives the program the target context's complete
ordered physical list. Original gate placements, native events and evaluated
depth are preserved; no physical SWAP or additional gate is introduced.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

variable {source target : RuntimeCtx .quantum}
  (same : source.entries.Perm target.entries) (program : UnitaryCircuit source.register)

/-- Re-express the original operator and advertise every identical live target wire. -/
def unitaryProgram : UnitaryCircuit target.register :=
  (UnitaryCircuit.reindex (basis same) program).seq
    (.identity target.register target.physicalIdx target.identitiesNodup)

/-- The literal emitted unitary instruction lists exactly the target context's live wires. -/
theorem unitaryProgram_physical (placed : program.physical_idx = source.physicalIdx) :
    (unitaryProgram same program).physical_idx = target.physicalIdx := by
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  intro wire present
  change wire ∈ program.physical_idx at present
  rw [placed] at present
  exact ((quantumWires_perm same).map QuantumWire.identity).mem_iff.mp present

/-- Every matrix entry remains the original one on the corresponding physical-wire values. -/
theorem unitaryProgram_matrix (row column : target.register.Index) :
    (unitaryProgram same program).matrix row column =
      program.matrix ((basis same).symm row) ((basis same).symm column) := by
  have matrix : ((unitaryProgram same program).matrix : HilbertOperator target.register) =
      Matrix.reindex (basis same) (basis same)
        (program.matrix : HilbertOperator source.register) := by
    change (1 : HilbertOperator target.register) * _ = _
    exact Matrix.one_mul _
  rw [matrix]
  rfl

/-- The same native event list is retained in its complete original order. -/
theorem unitaryProgram_trace : (unitaryProgram same program).eventTrace = program.eventTrace := by
  rw [unitaryProgram, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.reindex_eventTrace]
  exact List.append_nil _

/-- Every native event coordinate retains its original multiplicity. -/
theorem unitaryProgram_cost : (unitaryProgram same program).eventCost = program.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, unitaryProgram_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- All native duration assignments give the original evaluated dependency depth. -/
theorem unitaryProgram_depth (duration : Resource.Event .quantum → Nat) :
    (unitaryProgram same program).evaluatedEventDepth duration =
      program.evaluatedEventDepth duration := by
  change program.evaluatedEventDepth duration + 0 = program.evaluatedEventDepth duration
  exact Nat.add_zero _

/-- Arbitrary external-reference coordinates retain every original joint operator entry. -/
theorem unitaryProgram_joint_entry (Reference : Register)
    (row column : target.register.Index) (referenceRow referenceColumn : Reference.Index) :
    (UnitaryOperator.prodTensor (unitaryProgram same program).matrix
      (1 : UnitaryOperator Reference)) (row, referenceRow) (column, referenceColumn) =
        (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
          ((basis same).symm row, referenceRow) ((basis same).symm column, referenceColumn) := by
  rw [UnitaryOperator.prodTensor_apply, UnitaryOperator.prodTensor_apply, unitaryProgram_matrix]

end

end QuantumAlg.Execution.ContextPermutation
