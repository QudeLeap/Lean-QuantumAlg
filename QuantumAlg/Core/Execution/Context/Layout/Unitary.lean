/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator

/-!
# Native execution on the same ordered physical wires

An owned context and its supplied layout may present the same wire list
through different dependent types. Equality of complete ordered wire records
allows embedding the actual native word without introducing a physical gate.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {leftCount rightCount : Nat}
  (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
  (sameWires : left.wires = right.wires)

private def equalWiresPlacement : QuantumLayout.Embedding left right where
  position := (positionsOfEqualWires left right sameWires).toEmbedding
  wire_eq := wireAtCorrespondingPosition left right sameWires

private theorem equalWiresPlacement_basis (value : right.Basis) :
    ((equalWiresPlacement left right sameWires).splitBasis value).1 =
      (basisOfEqualWires left right sameWires).symm value := by
  funext index
  apply Fin.ext
  have unchanged := basisOfEqualWires_value left right sameWires
    ((basisOfEqualWires left right sameWires).symm value) index
  rw [Equiv.apply_symm_apply] at unchanged
  exact (QuantumLayout.Embedding.embedding_splitBasis_selected_value
    (equalWiresPlacement left right sameWires) value index).trans (by
      simpa [equalWiresPlacement] using unchanged)

/-- Retain the complete native word on the same ordered physical systems. -/
public def unitaryOfEqualWires (program : UnitaryCircuit gates oracles left) :
    UnitaryCircuit gates oracles right :=
  UnitaryCircuit.embed (equalWiresPlacement left right sameWires) program

/-- The exact source operator is transported by corresponding physical-wire values only. -/
public theorem unitaryOfEqualWires_matrix (program : UnitaryCircuit gates oracles left) :
    (unitaryOfEqualWires left right sameWires program).matrix =
      UnitaryOperator.reindex (basisOfEqualWires left right sameWires) program.matrix := by
  apply Subtype.ext
  ext row column
  change (equalWiresPlacement left right sameWires).liftOperator program.matrix row column = _
  refine (QuantumLayout.Embedding.liftOperator_entry_of_surjective
    (equalWiresPlacement left right sameWires)
    (positionsOfEqualWires left right sameWires).surjective program.matrix row column).trans ?_
  rw [equalWiresPlacement_basis, equalWiresPlacement_basis]
  rfl

/-- No native event or declared query is introduced or removed by equal-wire placement. -/
public theorem unitaryOfEqualWires_trace (program : UnitaryCircuit gates oracles left)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (unitaryOfEqualWires left right sameWires program).eventTrace operations services =
      program.eventTrace operations services := by
  rfl

/-- Every native coordinate retains its multiplicity under equal-wire placement. -/
public theorem unitaryOfEqualWires_cost (program : UnitaryCircuit gates oracles left)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (unitaryOfEqualWires left right sameWires program).eventCost operations services =
      program.eventCost operations services := by
  rfl

/-- The complete dependency expression is unchanged, including macro boundaries. -/
public theorem unitaryOfEqualWires_depth (program : UnitaryCircuit gates oracles left)
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (unitaryOfEqualWires left right sameWires program).eventDepth operations services =
      program.eventDepth operations services := by
  rfl

end

end QuantumAlg.Execution
