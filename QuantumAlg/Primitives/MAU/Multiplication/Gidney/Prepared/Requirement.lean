/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Prepared.Program
import all QuantumAlg.Core.Execution.Prepared.Unitary
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Independent complete output target for internally prepared multiplication

The target contains the incoming word and arbitrary reference, a tensor
factor fixed to the auxiliary zero basis, and the independently specified
unit-multiplication operator. It contains no execution or resource projection.
The actual prepare/unitary sequence satisfies this complete joint-state
requirement, after summing the actual classical histories.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Execution.OwnedQubits

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def preparedTarget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register)
    (input : Execution.Input (context width) Reference) :
    DensityOperator (Register.prod
      ((preparedContext width).quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference (preparedContext width).quantumLayout
    Finset.univ Reference
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (preparedOperator width modulus coefficient)
        (1 : UnitaryOperator Reference))
      (Execution.preparedDensity auxiliaryKey (auxiliaryLayout width)
        (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)
        (auxiliaryPreparation width).normalized Reference input.state.quantumMarginal))

private theorem preparedTarget_normalized (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register)
    (input : Execution.Input (context width) Reference) :
    (preparedTarget width modulus coefficient Reference input).IsNormalized := by
  let initial : DensityOperator (Register.prod (preparedContext width).register Reference) :=
    Execution.preparedDensity auxiliaryKey (auxiliaryLayout width)
      (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)
      (auxiliaryPreparation width).normalized Reference input.state.quantumMarginal
  let operator : UnitaryOperator (Register.prod (preparedContext width).register Reference) :=
    UnitaryOperator.prodTensor (preparedOperator width modulus coefficient)
      (1 : UnitaryOperator Reference)
  have preparedMass : initial.mass = input.state.quantumMarginal.mass :=
    Execution.preparedDensity_mass (ctx := context width) auxiliaryKey (auxiliaryLayout width)
      (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)
      (auxiliaryPreparation width).normalized Reference input.state.quantumMarginal
  exact (DensityOperator.observeSelectionWithReference_mass
    (preparedContext width).quantumLayout Finset.univ Reference
    (DensityOperator.applyUnitary operator initial)).trans
      ((DensityOperator.applyUnitary_mass operator initial).trans
        (preparedMass.trans ((ExecutionState.quantumMarginal_mass input.state).trans
          input.normalized)))

/-- Complete prepared output, specified independently and jointly with every external reference. -/
def preparedRequirement (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) :
    StateRequirement (context width) (preparedContext width) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (preparedTarget width modulus coefficient Reference input)
      (preparedTarget_normalized width modulus coefficient Reference input)

/-- Actual preparation and native multiplication meet the complete independent state target. -/
theorem gidneyPreparedRequirement_holds (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) {shape : CShape}
    (output : Output (preparedContext width) shape) {Reference : Register}
    (input : Execution.Input (context width) Reference) :
    (preparedRequirement width modulus coefficient).Holds input
      (({ code := preparedCode width modulus coefficient, output := output } :
        AlgorithmRun (context width) (preparedContext width) shape).finalState
          Reference input.state) := by
  intro value
  cases value with
  | unit =>
      let initial : DensityOperator (Register.prod (preparedContext width).register Reference) :=
        Execution.preparedDensity auxiliaryKey (auxiliaryLayout width)
          (gidneyAuxiliary_fresh width) (gidneyAuxiliary_disjoint width)
          (auxiliaryPreparation width).normalized Reference input.state.quantumMarginal
      let result := ({ code := preparedCode width modulus coefficient, output := output } :
        AlgorithmRun (context width) (preparedContext width) shape).finalState Reference input.state
      have actual : result.quantumMarginal = DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (preparedUnitary width modulus coefficient).matrix
            (1 : UnitaryOperator Reference)) initial :=
        Execution.preparedUnitary_finalState_quantumMarginal (ctx := context width)
          auxiliaryKey (auxiliaryLayout width) (gidneyAuxiliary_fresh width)
          (gidneyAuxiliary_disjoint width) (auxiliaryPreparation width)
          (preparedUnitary width modulus coefficient)
          (gidneyPreparedUnitary_physical width modulus coefficient) output Reference input.state
      have semantic := actual.trans
        (congrArg (fun operator : UnitaryOperator (preparedContext width).register =>
          DensityOperator.applyUnitary
            (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) initial)
          (gidneyPreparedUnitary_matrix width modulus coefficient))
      have observed := congrArg
        (fun density : DensityOperator (Register.prod (preparedContext width).register Reference) =>
          DensityOperator.observeSelectionWithReference (preparedContext width).quantumLayout
            Finset.univ Reference density)
        ((ExecutionState.executionState_mapClassical_const_block result CShape.Value.unit).trans
          semantic)
      have targetHolds :
          (StatePromise.mixed (preparedTarget width modulus coefficient Reference input)
            (preparedTarget_normalized width modulus coefficient Reference input)).Holds
              (preparedTarget width modulus coefficient Reference input) := by
        change (preparedTarget width modulus coefficient Reference input).matrix =
          ((preparedTarget width modulus coefficient Reference input).mass : ℝ) •
            (preparedTarget width modulus coefficient Reference input).matrix
        rw [preparedTarget_normalized]
        simp only [one_smul]
      exact (congrArg
        (StatePromise.mixed (preparedTarget width modulus coefficient Reference input)
          (preparedTarget_normalized width modulus coefficient Reference input)).Holds
        observed).mpr targetHolds

end

end QuantumAlg.MAU.Multiplication.Gidney
