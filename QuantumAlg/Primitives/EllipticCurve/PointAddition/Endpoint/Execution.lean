/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Specification
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Specification
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Context
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Endpoint.Construction
import all QuantumAlg.Core.Algorithm.Unitary.Endpoint
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed
import all QuantumAlg.Core.Algorithm.Unitary.Laws
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Base.State.Density.BasisSupport
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.Trace

/-!
# Complete ECADD execution on the promised clean subspace

Native event, space and time bounds belong to the same placed program. Exact
basis columns extend by positivity and linearity to every admitted mixed
state jointly with an arbitrary reference. All physical systems remain live
in the complete output, including the restored owned auxiliary suffix.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ControlledPointAddition.Execution
noncomputable section

variable {environment : model.Environment}

local instance {α : Type} : DecidableEq α := Classical.decEq α
private lemma indicator_transport {Source Target : Type}
    (sourceDecision : DecidableEq Source) (targetDecision : DecidableEq Target)
    (basis : Source ≃ Target) (row : Target) (column : Source) :
    @ite ℂ (basis.symm row = column) (sourceDecision _ _) 1 0 =
      @ite ℂ (row = basis column) (targetDecision _ _) 1 0 := by
  by_cases same : basis.symm row = column
  · rw [if_pos same, if_pos (basis.symm_apply_eq.mp same)]
  · rw [if_neg same, if_neg (fun equal => same (basis.symm_apply_eq.mpr equal))]

private lemma unitary_column_of_ket {count : Nat} {layout : QuantumLayout count}
    (code : UnitaryCircuit AlgorithmGate.model .empty layout)
    (input output row : layout.register.Index)
    (action : code.applyNormalized environment.quantum (NormalizedVector.ket input) =
      NormalizedVector.ket output) :
    (code.matrix environment.quantum) row input = if row = output then 1 else 0 := by
  have entry := congrArg (fun state : NormalizedVector layout.register => state row) action
  change (code.matrix environment.quantum).applyVec (NormalizedVector.ket input) row =
    (NormalizedVector.ket output) row at entry
  simpa only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply] using entry

variable [params : Arithmetic.VariableModularMul.Parameters]
variable (E : PrimeFieldShortWeierstrass params.modulus.val) [Fact params.modulus.val.Prime]

/-- Place the literal production word on the same ordered physical systems with explicit roles. -/
def program (Q : AffinePoint E) : UnitaryCircuit AlgorithmGate.model .empty (context
  params.width).quantumLayout :=
  QuantumAlg.Execution.unitaryOfEqualWires rawLayout (context params.width).quantumLayout
    raw_wires (ControlledPointAddition.program E Q)

/-- The complete actual native run retains every supplied and auxiliary wire. -/
def algorithm (Q : AffinePoint E) : Algorithm model (context params.width) (context params.width)
  .unit :=
  UnitaryExecution.algorithm (program E Q)

private lemma target_column (Q : AffinePoint E) (value : Legal E Q)
    (row : (context params.width).register.Index) :
    semanticOperator E Q row (incoming E Q value) = if row = outgoing E Q value then 1 else 0 := by
  have entry := congrArg (fun vector : HilbertVector (context params.width).register => vector row)
    (UnitaryOperator.ofPerm_applyVec_ket (semanticPermutation E Q).symm (incoming E Q value))
  change (semanticOperator E Q).applyVec (NormalizedVector.ket (incoming E Q value)) row =
    (NormalizedVector.ket (semanticPermutation E Q (incoming E Q value))) row at entry
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    semanticPermutation_incoming, NormalizedVector.ket_apply] at entry
  exact entry

private lemma raw_program_clean_ket (Q : AffinePoint E) (value : Legal E Q) :
    (ControlledPointAddition.program E Q).applyNormalized environment.quantum
        (NormalizedVector.ket (cleanLabel E value.1 value.2.1)) =
      NormalizedVector.ket (cleanLabel E value.1
        (controlledResultPoint E Q value.1 value.2.1 value.2.2.1 value.2.2.2)) := by
  simpa only [GenericPointAddition.ExceptionalCleanup.encodedKet, cleanLabel] using
    program_clean_ket E Q value.1 value.2.1 value.2.2.1 value.2.2.2

section

attribute [local irreducible] ControlledPointAddition.program

/-- Exact legal columns of the actual execution and independently specified translation agree. -/
lemma program_column (Q : AffinePoint E) (value : Legal E Q)
    (row : (context params.width).register.Index) :
    ((program E Q).matrix environment.quantum) row (incoming E Q value) =
      semanticOperator E Q row (incoming E Q value) :=
      by
  have entry := unitary_column_of_ket (environment := environment)
    (ControlledPointAddition.program E Q)
    (cleanLabel E value.1 value.2.1)
    (cleanLabel E value.1
      (controlledResultPoint E Q value.1 value.2.1 value.2.2.1 value.2.2.2))
    (rawBasis.symm row) (raw_program_clean_ket E Q value)
  rw [target_column]
  have matrix := QuantumAlg.Execution.unitaryOfEqualWires_matrix
    (environment := environment.quantum) rawLayout
    (context params.width).quantumLayout raw_wires (ControlledPointAddition.program E Q)
  change ((program E Q).matrix environment.quantum) = _ at matrix
  rw [matrix]
  change ((ControlledPointAddition.program E Q).matrix environment.quantum) (rawBasis.symm row)
    (rawBasis.symm (rawBasis (cleanLabel E value.1 value.2.1))) = _
  rw [Equiv.symm_apply_apply, entry]
  exact indicator_transport _ _ rawBasis row _

end

private lemma actual_events (hcharacteristic : 3 < params.modulus.val)
    (hfieldWidth : params.width = Nat.clog 2 params.modulus.val) (Q : AffinePoint E) :
    (program E Q).eventCost ≤ (resources (params := params)).events := by
  have same : (program E Q).eventCost = (ControlledPointAddition.program E Q).eventCost :=
    QuantumAlg.Execution.unitaryOfEqualWires_cost rawLayout (context params.width).quantumLayout
      raw_wires (ControlledPointAddition.program E Q) .empty .empty
  rw [same]
  apply ResourcePool.le_iff_count.mpr
  intro event
  cases event with
  | gate coordinate =>
      cases coordinate with
      | toffoli =>
          simpa [resources] using program_toffoli_count_le_published hcharacteristic hfieldWidth E Q
      | cnot =>
          have bound : ResourcePool.count (model := model) (.gate .cnot)
              (ControlledPointAddition.program E Q).eventCost ≤ circuitDepthBound params.width := by
            refine (Multiset.count_le_card _ _).trans ?_
            change (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
              (GenericPointAddition.ExceptionalCleanup.translationGates (E := E) (Q :=
                Q))).eventCost.card ≤ _
            rw [EncodedBit.GateSpec.programList_eventCost_card]
            exact GenericPointAddition.ExceptionalCleanup.translationGates_length_le (E := E) (Q :=
              Q)
          simpa [resources] using bound
      | singleQubit =>
          have zero := GenericPointAddition.ExceptionalCleanup.translationProgram_x_count_zero (E :=
            E) (Q := Q)
          simpa [resources, ControlledPointAddition.program] using le_of_eq zero
  | oracle coordinate => exact Empty.elim coordinate
  | classicalOperation coordinate => exact Empty.elim coordinate
  | classicalQuery coordinate => exact Empty.elim coordinate
  | preparation dimension =>
      have zero := UnitaryCircuit.unitaryCircuit_event_count_classical_context
        (ControlledPointAddition.program E Q) .empty .empty (.preparation dimension)
      simpa [resources] using le_of_eq zero
  | measurement dimension =>
      have zero := UnitaryCircuit.unitaryCircuit_event_count_classical_context
        (ControlledPointAddition.program E Q) .empty .empty (.measurement dimension)
      simpa [resources] using le_of_eq zero

private lemma actual_time (Q : AffinePoint E) :
    (program E Q).evaluatedEventDepth Resource.Event.quantumDuration ≤ circuitDepthBound
      params.width := by
  refine (DepthExpr.depthEval_mono Resource.Event.quantumDuration_le_one _).trans ?_
  change (ControlledPointAddition.program E Q).evaluatedEventDepth (fun _ => 1) ≤ _
  exact program_unitDepth_le E Q

private lemma actual_state (Q : AffinePoint E) {Reference : Register}
    (input : QuantumAlg.Execution.OracleInput .empty (context params.width) Reference)
    (allowed : valid E Q input.caller.localState) :
    (StateRequirement.unitary (semanticOperator E Q)).Holds input.caller
      ((algorithm E Q).run.finalState environment Reference input.state) := by
  have joint : DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor ((program E Q).matrix environment.quantum)
          (1 : UnitaryOperator Reference))
        input.caller.state.quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor (semanticOperator E Q) (1 : UnitaryOperator Reference))
        input.caller.state.quantumMarginal := by
    apply DensityOperator.applyLocalUnitary_eq_on_basis_support _ (Set.range (incoming E Q))
    · intro basis absent
      rw [← QuantumAlg.Execution.Input.localState_quantumMarginal]
      exact allowed basis absent
    · intro basis present row
      obtain ⟨value, rfl⟩ := present
      exact program_column E Q value row
  intro value
  cases value with
  | unit =>
      change (StatePromise.mixed (StateRequirement.unitaryTarget (semanticOperator E Q) Reference
        input.caller)
        (StateRequirement.unitaryTarget_normalized (semanticOperator E Q) Reference
          input.caller)).Holds
          (DensityOperator.observeSelectionWithReference (context params.width).quantumLayout
            Finset.univ Reference
            ((((algorithm E Q).run.finalState environment Reference input.state).mapClassical
              (fun _ => CShape.Value.unit)).block CShape.Value.unit))
      rw [ExecutionState.executionState_mapClassical_const_block]
      change (StatePromise.mixed _ _).Holds
        (DensityOperator.observeSelectionWithReference _ _ _
          (({ code := .unitary (program E Q), output := Output.all (context params.width) .unit } :
            AlgorithmRun model (context params.width) (context params.width) .unit).finalState
              environment Reference input.state).quantumMarginal)
      rw [AlgorithmRun.finalState_unitary_quantumMarginal,
        ← QuantumAlg.Execution.OracleInput.oracleInput_caller_quantumMarginal input, joint]
      change (StateRequirement.unitaryTarget (semanticOperator E Q) Reference input.caller).matrix =
        ((StateRequirement.unitaryTarget (semanticOperator E Q) Reference input.caller).mass : ℝ) •
          (StateRequirement.unitaryTarget (semanticOperator E Q) Reference input.caller).matrix
      rw [StateRequirement.unitaryTarget_normalized]
      simp only [one_smul]

end
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ControlledPointAddition.Execution
