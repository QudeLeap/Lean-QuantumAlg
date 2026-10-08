/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.BodyState
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.State.Preservation

/-!
# Complete actual in-place multiplication and division states

The actual fixed preparation and finite-cell allocation establish the
required support internally. The actual body then equals the independent
mathematical target, with its real stored outcomes and source fibers
summed by the existing execution semantics
[LYL+26, sec_point_add/sec_point_add.tex:24-36,45-105,119-122].

The initial store is copied into AlgorithmRun's mathematical history,
exactly as defined by that run. The proof retains this history through
both allocations and the body, and only finalState forgets it. Any full
Output descriptor is allowed. Only the original local support domain is
assumed, and the final matrix includes every external-reference entry.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceState

noncomputable section

open Execution MAU.Inversion.SharedEEA InversePreparation

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem prefix_marginal (modulus : Nat)
    (body : Circuit (.quantum AlgorithmGate.model .empty)
      (NumeratorMeasurement.context modulus.size)
      (NumeratorMeasurement.context modulus.size))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (before modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × H)) :
    ((Circuit.seq (InPlacePreparation.circuit modulus)
      (Circuit.seq (NumeratorMeasurement.allocate modulus.size) body)).execute
        Reference state).quantumMarginal =
      (body.execute Reference
        ((NumeratorMeasurement.allocate modulus.size).execute Reference
          ((InPlacePreparation.circuit modulus).execute Reference state))).quantumMarginal := by
  rw [Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal]

private theorem copied_preparation (modulus : Nat) {Reference : Register}
    (input : OracleInput .empty (before modulus.size) Reference) :
    ((NumeratorMeasurement.allocate modulus.size).execute Reference
      ((InPlacePreparation.circuit modulus).execute Reference
        (input.state.mapClassical
          (fun value => (value.1, (value.2, value.1)))))).quantumMarginal =
      InPlaceTarget.inputDensity modulus Reference input.caller.state.quantumMarginal := by
  have actual := InPlacePreparedSupport.actual_density modulus
    (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))
  change _ = InPlaceTarget.inputDensity modulus Reference
    (input.state.mapClassical
      (fun value => (value.1, (value.2, value.1)))).quantumMarginal at actual
  exact actual.trans (congrArg (InPlaceTarget.inputDensity modulus Reference)
    ((ExecutionState.mapClassical_quantumMarginal input.state
      (fun value => (value.1, (value.2, value.1)))).trans
      input.oracleInput_caller_quantumMarginal.symm))

private theorem copied_support (modulus : Nat) {Reference : Register}
    (input : OracleInput .empty (before modulus.size) Reference)
    (valid : InPlaceDomain.valid modulus input.caller.localState)
    (basis : (Register.prod (NumeratorMeasurement.context modulus.size).register Reference).Index)
    (outside : ¬InPlacePreparedSupport.admissible modulus basis.1) :
    ((NumeratorMeasurement.allocate modulus.size).execute Reference
      ((InPlacePreparation.circuit modulus).execute Reference
        (input.state.mapClassical
          (fun value => (value.1, (value.2, value.1)))))).quantumMarginal.matrix
          basis basis = 0 := by
  have entry := congrArg
    (fun density : DensityOperator
      (Register.prod (NumeratorMeasurement.context modulus.size).register Reference) =>
        density.matrix basis basis) (copied_preparation modulus input)
  refine entry.trans ?_
  unfold InPlaceTarget.inputDensity
  erw [DensityOperator.reindex_entry]
  exact DensityOperator.joint_diagonal_zero_of_marginal_diagonal_zero
    (InPlacePreparedSupport.density modulus Reference input.caller.state.quantumMarginal) _
    (InPlacePreparedSupport.prepared_diagonal modulus input.caller valid _ outside) basis.2

/-- The complete actual division run has the independent joint target for any full output. -/
theorem division_finalState (modulus : Nat) (prime : Nat.Prime modulus)
    {shape : CShape} (output : Output (NumeratorMeasurement.context modulus.size) shape)
    {Reference : Register} (input : OracleInput .empty (before modulus.size) Reference)
    (valid : InPlaceDomain.valid modulus input.caller.localState) :
    (({ code := InPlaceDivision.code modulus prime, output := output } :
      AlgorithmRun (.quantum AlgorithmGate.model .empty) (before modulus.size)
        (NumeratorMeasurement.context modulus.size) shape).finalState
        Reference input.state).quantumMarginal =
      InPlaceTarget.density .division modulus prime Reference
        input.caller.state.quantumMarginal := by
  have history :
      (({ code := InPlaceDivision.code modulus prime, output := output } :
        AlgorithmRun (.quantum AlgorithmGate.model .empty) (before modulus.size)
          (NumeratorMeasurement.context modulus.size) shape).finalState
          Reference input.state).quantumMarginal =
      ((InPlaceDivision.code modulus prime).execute Reference
        (input.state.mapClassical
          (fun value => (value.1, (value.2, value.1))))).quantumMarginal :=
    AlgorithmRun.finalState_quantumMarginal
      ({ code := InPlaceDivision.code modulus prime, output := output } :
        AlgorithmRun (.quantum AlgorithmGate.model .empty) (before modulus.size)
          (NumeratorMeasurement.context modulus.size) shape) Reference input.state
  have actual := InPlaceBodyState.division_density modulus prime
    ((NumeratorMeasurement.allocate modulus.size).execute Reference
      ((InPlacePreparation.circuit modulus).execute Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))))
    (copied_support modulus input valid)
  exact history.trans ((prefix_marginal modulus (InPlaceDivision.body modulus prime)
    (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans
    (actual.trans (congrArg
      (DensityOperator.applyUnitary (InPlaceTarget.jointOperator .division modulus prime Reference))
      (copied_preparation modulus input))))

/-- The same strong full-state theorem holds for the actual measured multiplication schedule. -/
theorem multiplication_finalState (modulus : Nat) (prime : Nat.Prime modulus)
    {shape : CShape} (output : Output (NumeratorMeasurement.context modulus.size) shape)
    {Reference : Register} (input : OracleInput .empty (before modulus.size) Reference)
    (valid : InPlaceDomain.valid modulus input.caller.localState) :
    (({ code := InPlaceMultiplication.code modulus prime, output := output } :
      AlgorithmRun (.quantum AlgorithmGate.model .empty) (before modulus.size)
        (NumeratorMeasurement.context modulus.size) shape).finalState
        Reference input.state).quantumMarginal =
      InPlaceTarget.density .multiplication modulus prime Reference
        input.caller.state.quantumMarginal := by
  have history :
      (({ code := InPlaceMultiplication.code modulus prime, output := output } :
        AlgorithmRun (.quantum AlgorithmGate.model .empty) (before modulus.size)
          (NumeratorMeasurement.context modulus.size) shape).finalState
          Reference input.state).quantumMarginal =
      ((InPlaceMultiplication.code modulus prime).execute Reference
        (input.state.mapClassical
          (fun value => (value.1, (value.2, value.1))))).quantumMarginal :=
    AlgorithmRun.finalState_quantumMarginal
      ({ code := InPlaceMultiplication.code modulus prime, output := output } :
        AlgorithmRun (.quantum AlgorithmGate.model .empty) (before modulus.size)
          (NumeratorMeasurement.context modulus.size) shape) Reference input.state
  have actual := InPlaceBodyState.multiplication_density modulus prime
    ((NumeratorMeasurement.allocate modulus.size).execute Reference
      ((InPlacePreparation.circuit modulus).execute Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))))
    (copied_support modulus input valid)
  exact history.trans ((prefix_marginal modulus (InPlaceMultiplication.body modulus prime)
    (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans
    (actual.trans (congrArg
      (DensityOperator.applyUnitary
        (InPlaceTarget.jointOperator .multiplication modulus prime Reference))
      (copied_preparation modulus input))))

end

end QuantumAlg.MeasuredUncompute.InPlaceState
