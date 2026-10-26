/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback
import all QuantumAlg.Primitives.QFT.Semiclassical.PhaseMatrix
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases
import all QuantumAlg.Core.Execution.Store.History

/-!
# Exact full-layout diagonal of the real earlier-cell feedback

Each scalar below is derived from the actual native phase token selected by
the same original stored result. The whole physical layout and Reference
remain present. The guarded instruction is the identity on other-stream and
future cells, with no assumption about their initial values.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback

noncomputable section

open Execution

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Literal phase scalar on the selected original physical bit. -/
def phaseScalar (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active) (value : CShape.Value (.finite 2))
    (basis : ctx.register.Index) : Complex :=
  if value.toFin.val = 1 then
    if (basis (ports.wires current)).val = 0 then 1 else
      Partner.rotation true ((ports.position current).val - previous.2.val - 1)
  else 1

lemma phaseProgram_matrix_diagonal (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (value : CShape.Value (.finite 2)) (environment : OracleModel.empty.Interpretation) :
    ((phaseProgram (oracles := .empty) ports previous current value).matrix environment :
      HilbertOperator ctx.register) =
        Matrix.diagonal (phaseScalar ports previous current value) := by
  cases value with
  | finite bit =>
      dsimp only [phaseProgram]
      by_cases selected : bit.val = 1
      · simp only [if_pos selected]
        rw [qftSemiclassical_nativePhase_diagonal]
        apply congrArg Matrix.diagonal
        funext basis
        simp only [phaseScalar, CShape.Value.toFin, if_pos selected]
        by_cases zero : (basis (ports.wires current)).val = 0 <;>
          simp [zero, Partner.rotation]
      · simp only [if_neg selected]
        rw [UnitaryCircuit.identity_matrix]
        ext row column
        simp [phaseScalar, CShape.Value.toFin, selected, Matrix.diagonal_apply,
          Matrix.one_apply]

/-- The actual native matrix is diagonal jointly with every untouched Reference index. -/
lemma phaseProgram_reference_diagonal (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (value : CShape.Value (.finite 2)) (environment : OracleModel.empty.Interpretation)
    (Reference : Register) :
    (UnitaryOperator.prodTensor
        ((phaseProgram (oracles := .empty) ports previous current value).matrix environment)
          (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference)) =
      Matrix.diagonal (fun basis => phaseScalar ports previous current value basis.1) := by
  ext row column
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  change ((phaseProgram (oracles := .empty) ports previous current value).matrix environment :
      HilbertOperator ctx.register) row.1 column.1 *
      (1 : HilbertOperator Reference) row.2 column.2 = _
  rw [phaseProgram_matrix_diagonal]
  have equality : row = column ↔ row.1 = column.1 ∧ row.2 = column.2 := Prod.ext_iff
  by_cases physical : row.1 = column.1 <;> by_cases reference : row.2 = column.2 <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, equality, physical, reference]

/-- Extracted from the actual guarded native branch, never used to choose circuit syntax. -/
def oneOperator (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active) (environment : OracleModel.empty.Interpretation)
    (Reference : Register) (stored : Store ctx) : HilbertOperator (ctx.register.prod Reference) :=
  if ports.past previous then
    UnitaryOperator.prodTensor
      ((phaseProgram (oracles := .empty) ports previous current
        (stored.read (.storage (ports.results previous).toCStorageRef))).matrix environment)
      (1 : UnitaryOperator Reference)
  else 1

def oneScalar (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active) (stored : Store ctx) (basis : ctx.register.Index) : Complex :=
  if ports.past previous then phaseScalar ports previous current
    (stored.read (.storage (ports.results previous).toCStorageRef)) basis else 1

lemma oneOperator_diagonal (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) (stored : Store ctx) :
    oneOperator ports previous current environment Reference stored =
      Matrix.diagonal (fun basis => oneScalar ports previous current stored basis.1) := by
  by_cases prior : ports.past previous
  · simp only [oneOperator, oneScalar, if_pos prior]
    exact phaseProgram_reference_diagonal ports previous current _ environment Reference
  · simp only [oneOperator, oneScalar, if_neg prior]
    ext row column
    simp only [Matrix.one_apply, Matrix.diagonal_apply]

private lemma identity_store_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((Circuit.id (model := .quantum AlgorithmGate.model .empty operations services)
      (allowAllocation := false) ctx).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix := by
  rw [Circuit.execute_id]
  calc
    _ = (ExecutionState.filterClassical
        (state.mapHistory (fun record => (record.1, (record.2, ()))))
          (fun entry => entry.1 = stored)).quantumMarginal.matrix := by
      apply congrArg (fun result : State ctx Reference
        (services.HiddenState × (History × Unit)) =>
          (result.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix)
      exact ExecutionState.executionState_mapClassical_congr state rfl
    _ = _ := congrArg DensityOperator.matrix (State.mapHistory_store_marginal _ _ _)

/-- Same stored-cell read and actual guard, retaining complete original densities and Reference. -/
lemma one_store_matrix (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((one ports previous current).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      oneOperator ports previous current environment.quantum Reference stored *
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix *
          (oneOperator ports previous current environment.quantum Reference
            stored).conjTranspose := by
  by_cases prior : ports.past previous
  · rw [one_of_past ports previous current prior, selected_store_matrix,
      DensityOperator.applyUnitary_matrix]
    simp only [oneOperator, if_pos prior]
  · rw [one, if_neg prior, identity_store_matrix]
    simp only [oneOperator, if_neg prior, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback
