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

Logical coordinates follow the identical physical wires. The construction
embeds the complete source layout in the corresponding target positions.
Original gate and query placements, event counts and dependency depth are
preserved; the layout correspondence supplies no physical SWAP.
-/

namespace QuantumAlg.Execution.ContextPermutation

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
  {source target : RuntimeCtx .quantum} (same : source.entries.Perm target.entries)
  (program : UnitaryCircuit gates oracles source.quantumLayout)

private def placement : QuantumLayout.Embedding source.quantumLayout target.quantumLayout where
  position := (positions same).toEmbedding
  wire_eq := positions_wire same

private theorem placement_basis (value : target.register.Index) :
    ((placement same).splitBasis value).1 = (basis same).symm value := by
  funext index
  apply Fin.ext
  have unchanged := basis_value same ((basis same).symm value) index
  rw [Equiv.apply_symm_apply] at unchanged
  exact (QuantumLayout.Embedding.embedding_splitBasis_selected_value
    (placement same) value index).trans unchanged.symm

/-- Re-express the actual construction on precisely the same target physical systems. -/
def unitaryProgram : UnitaryCircuit gates oracles target.quantumLayout :=
  UnitaryCircuit.embed (placement same) program

/-- Every matrix entry remains the original one on the corresponding physical-wire values. -/
theorem unitaryProgram_matrix (row column : target.register.Index) :
    (unitaryProgram same program).matrix row column =
      program.matrix ((basis same).symm row) ((basis same).symm column) := by
  change (placement same).liftOperator program.matrix row column = _
  rw [QuantumLayout.Embedding.liftOperator_entry_of_surjective
    (placement same) (positions same).surjective, placement_basis, placement_basis]

/-- Every granted native and query event is retained in its complete original order. -/
theorem unitaryProgram_trace (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (unitaryProgram same program).eventTrace operations services =
      program.eventTrace operations services := rfl

/-- Every native event coordinate retains its original multiplicity. -/
theorem unitaryProgram_cost (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (unitaryProgram same program).eventCost operations services =
      program.eventCost operations services := rfl

/-- All native duration assignments give the original evaluated dependency depth. -/
theorem unitaryProgram_depth (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (duration : Resource.Event (.quantum gates oracles operations services) → Nat) :
    DepthExpr.depthEval duration ((unitaryProgram same program).eventDepth operations services) =
      DepthExpr.depthEval duration (program.eventDepth operations services) := rfl

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
