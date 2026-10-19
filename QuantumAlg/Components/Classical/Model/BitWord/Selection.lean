/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Placement
public import QuantumAlg.Core.Base.Model
import all QuantumAlg.Components.Classical.Model.BitWord.Placement
import all QuantumAlg.Core.Base.Model

/-!
# Explicit selection of the bit and word language

Built-in classical routines require this exact native language. The surrounding
execution still chooses its quantum gates and both oracle declarations. This
proof of selection grants no new token or evaluator to a different model;
using a different native language requires its own actual implementation.
-/

namespace QuantumAlg.BitWord

noncomputable section

/-- The surrounding execution has selected the built-in bit and word operations. -/
public class Selected (execution : ExecutionModel) : Prop where
  operations_eq : execution.classicalOperations = model

public instance selectedClassical (services : ClassicalOracleModel) :
    Selected (.classical model services) := ⟨rfl⟩

public instance selectedQuantum (gates : GateModel) (oracles : OracleModel)
    (services : ClassicalOracleModel) : Selected (.quantum gates oracles model services) := ⟨rfl⟩

variable {execution : ExecutionModel} [Selected execution]
  {ctx : RuntimeCtx execution.kind} {input output : CShape}

/-- Place the actual declaration token in the selected execution's native language. -/
@[expose, implicit_reducible]
public def selectedApplication (op : ClassicalOp input output ctx ctx) :
    execution.classicalOperations.Application ctx :=
  cast (congrArg (fun operations : ClassicalOpModel => operations.Application ctx)
    (Selected.operations_eq (execution := execution)).symm) (application op)

/-- The same native coordinate, transported only across the proved model equality. -/
@[expose, implicit_reducible]
public def selectedCoordinate (label : Resource.ClassicalOpLabel) : execution.ClassicalCoordinate :=
  cast (congrArg ClassicalOpModel.Coordinate
    (Selected.operations_eq (execution := execution)).symm) label

/-- A selected instruction retains its actual declared output shape. -/
public lemma selectedApplication_output (op : ClassicalOp input output ctx ctx) :
    execution.classicalOperations.outputShape
      (selectedApplication (execution := execution) op).token = output := by
  cases execution with
  | classical operations services =>
      have same := Selected.operations_eq (execution := .classical operations services)
      change operations = model at same
      cases same
      rfl
  | quantum gates oracles operations services =>
      have same := Selected.operations_eq (execution := .quantum gates oracles operations services)
      change operations = model at same
      cases same
      rfl

end

end QuantumAlg.BitWord
