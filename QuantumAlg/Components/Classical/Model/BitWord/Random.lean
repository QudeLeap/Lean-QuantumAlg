/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Classical.Model.BitWord.Selection
public import QuantumAlg.Core.Execution.Circuit
public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Components.Classical.Model.BitWord.Selection
import all QuantumAlg.Components.Classical.Model.BitWord.Semantics
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual uniform random-bit leaves in the selected native language

The random token has a unit operand and uniformly distributed bit-string output.
A lexical unit cell supplies that operand without an assumed caller cell or a
literal-valued read reference. The actual caller output is lifted through this
scope. The one native event and its returned output path remain explicit.
-/

namespace QuantumAlg.BitWord.Random

noncomputable section

/-- The canonical uniform law on all bit strings, including the single empty string. -/
@[expose]
public def uniformBits (width : Nat) : PMF (CShape.Value (.bits width)) :=
  @PMF.uniformOfFintype (CShape.Value (.bits width)) inferInstance ⟨.bits fun _ => false⟩

/-- The existing model-owned random token placed at its declared operand and output. -/
@[expose]
public def application {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (unit : CInputRef ctx .unit) (output : CWriteRef ctx (.bits width)) :
    BitWord.model.Application ctx where
  token := ⟨.unit, .bits width, .randomBits width⟩
  input := unit
  output := output

/-- The random declaration fixes the uniform distribution, independently of the unit value. -/
public theorem randomApplication_distribution {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width : Nat} (unit : CInputRef ctx .unit) (output : CWriteRef ctx (.bits width))
    (value : CShape.Value .unit) :
    BitWord.model.evaluate (application unit output).token value =
      uniformBits width := by
  rfl

variable {execution : ExecutionModel} [Selected execution]
  {ctx : RuntimeCtx execution.kind} {width : Nat}

/-- Transport the same random application only across the proved native-model selection. -/
@[expose, implicit_reducible]
public def selectedApplication (unit : CInputRef ctx .unit)
    (output : CWriteRef ctx (.bits width)) : execution.classicalOperations.Application ctx :=
  cast (congrArg (fun operations : ClassicalOpModel => operations.Application ctx)
    (Selected.operations_eq (execution := execution)).symm) (application unit output)

/-- Model selection preserves the exact bit-string output shape. -/
public theorem selectedRandomApplication_output (unit : CInputRef ctx .unit)
    (output : CWriteRef ctx (.bits width)) :
    execution.classicalOperations.outputShape
      (selectedApplication (execution := execution) unit output).token = .bits width := by
  cases execution with
  | classical operations services =>
      have same := Selected.operations_eq (execution := .classical operations services)
      change operations = BitWord.model at same
      cases same
      rfl
  | quantum gates oracles operations services =>
      have same := Selected.operations_eq (execution := .quantum gates oracles operations services)
      change operations = BitWord.model at same
      cases same
      rfl

/-- Supply the nullary operand by actual lexical allocation and emit one declared random leaf. -/
@[expose, implicit_reducible]
public def code (output : CWriteRef ctx (.bits width)) : Circuit execution ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey .unit ctx.runtimeCtx_canonicalFreshKey_fresh
    (.classical (selectedApplication (execution := execution)
      (.storage (CStorageRef.workspaceHead ctx ctx.canonicalFreshKey .unit
        ctx.runtimeCtx_canonicalFreshKey_fresh))
      (output.underWorkspace ctx.canonicalFreshKey .unit ctx.runtimeCtx_canonicalFreshKey_fresh)))

/-- The actual path records exactly the generated bit string, including the empty-width case. -/
public def pathEquiv (output : CWriteRef ctx (.bits width)) :
    (code (execution := execution) output).Path ≃ CShape.Value (.bits width) :=
  Equiv.cast (congrArg CShape.Value (selectedRandomApplication_output
    (execution := execution)
    (.storage (CStorageRef.workspaceHead ctx ctx.canonicalFreshKey .unit
      ctx.runtimeCtx_canonicalFreshKey_fresh))
    (output.underWorkspace ctx.canonicalFreshKey .unit ctx.runtimeCtx_canonicalFreshKey_fresh)))

/-- Lexical unit allocation emits no event; the actual random leaf emits its width coordinate. -/
public theorem randomCode_eventTrace (output : CWriteRef ctx (.bits width))
    (path : (code (execution := execution) output).Path) :
    (code (execution := execution) output).eventTrace path =
      [.classicalOperation (BitWord.selectedCoordinate (execution := execution)
        (.randomBits width))] := by
  cases execution with
  | classical operations services =>
      have same := Selected.operations_eq (execution := .classical operations services)
      change operations = BitWord.model at same
      cases same
      rfl
  | quantum gates oracles operations services =>
      have same := Selected.operations_eq (execution := .quantum gates oracles operations services)
      change operations = BitWord.model at same
      cases same
      rfl

/-- Each actual sampling path charges precisely one native event. -/
public theorem randomCode_eventCount (output : CWriteRef ctx (.bits width))
    (path : (code (execution := execution) output).Path) :
    ((code (execution := execution) output).resourcePool path).card = 1 := by
  rw [Circuit.resourcePool, randomCode_eventTrace]
  rfl

/-- The same declared random operation supplies one unit-duration dependency step. -/
public theorem randomCode_unitDepth (output : CWriteRef ctx (.bits width))
    (path : (code (execution := execution) output).Path) :
    (code (execution := execution) output).depth (fun _ => 1) path = 1 := by
  cases execution with
  | classical operations services =>
      have same := Selected.operations_eq (execution := .classical operations services)
      change operations = BitWord.model at same
      cases same
      rfl
  | quantum gates oracles operations services =>
      have same := Selected.operations_eq (execution := .quantum gates oracles operations services)
      change operations = BitWord.model at same
      cases same
      rfl

end

end QuantumAlg.BitWord.Random
