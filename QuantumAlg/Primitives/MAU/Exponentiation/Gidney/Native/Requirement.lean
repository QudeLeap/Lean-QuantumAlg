/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Semantics
import all QuantumAlg.Core.Execution.Prepared.Unitary
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.Observe
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Independent complete output target for internally prepared exponentiation

The target contains the incoming exponent, arbitrary XOR target and reference,
a factor fixed to the two declared work words, and the independent
modular-power XOR operator. It contains no execution or resource projection.
The actual prepare/unitary sequence satisfies this complete joint-state
requirement, after summing the actual classical histories.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open Execution.SuppliedQubits

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def preparedTarget (m width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) (Reference : Register)
    (input : Execution.Input (context (m + width)) Reference) :
    DensityOperator (Register.prod
      ((preparedContext m width).quantumLayout.selectedRegister Finset.univ) Reference) :=
  DensityOperator.observeSelectionWithReference (preparedContext m width).quantumLayout
    Finset.univ Reference
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor (arithmeticNativeOperator m width modulus positive base)
        (1 : UnitaryOperator Reference))
      (Execution.preparedDensity workKey (workLayout m width)
        (gidneyExponentWork_fresh m width) (gidneyExponentWork_disjoint m width)
        (workPreparation m width).normalized Reference
          input.state.quantumMarginal))

private theorem preparedTarget_normalized (m width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) (Reference : Register)
    (input : Execution.Input (context (m + width)) Reference) :
    (preparedTarget m width modulus positive base Reference input).IsNormalized := by
  let initial : DensityOperator (Register.prod (preparedContext m width).register Reference) :=
    Execution.preparedDensity workKey (workLayout m width)
      (gidneyExponentWork_fresh m width) (gidneyExponentWork_disjoint m width)
      (workPreparation m width).normalized Reference input.state.quantumMarginal
  let operator : UnitaryOperator (Register.prod (preparedContext m width).register Reference) :=
    UnitaryOperator.prodTensor (arithmeticNativeOperator m width modulus positive base)
      (1 : UnitaryOperator Reference)
  have preparedMass : initial.mass = input.state.quantumMarginal.mass :=
    Execution.preparedDensity_mass (ctx := context (m + width)) workKey (workLayout m width)
      (gidneyExponentWork_fresh m width) (gidneyExponentWork_disjoint m width)
      (workPreparation m width).normalized Reference input.state.quantumMarginal
  exact (DensityOperator.observeSelectionWithReference_mass
    (preparedContext m width).quantumLayout Finset.univ Reference
    (DensityOperator.applyUnitary operator initial)).trans
      ((DensityOperator.applyUnitary_mass operator initial).trans
        (preparedMass.trans ((ExecutionState.quantumMarginal_mass input.state).trans
          input.normalized)))

/-- Complete prepared output, specified independently and jointly with every external reference. -/
def preparedRequirement (m width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) :
    StateRequirement (context (m + width)) (preparedContext m width) :=
  .jointReference Finset.univ .unit fun Reference input _ =>
    .mixed (preparedTarget m width modulus positive base Reference input)
      (preparedTarget_normalized m width modulus positive base Reference input)

/-- Actual work preparation and native exponentiation meet the complete independent state target. -/
theorem gidneyExponentPreparedRequirement_holds (m width : Nat) (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (base : (ZMod modulus.val)ˣ) {shape : CShape}
    (output : Output (preparedContext m width) shape) {Reference : Register}
    (input : Execution.OracleInput .empty (context (m + width)) Reference) :
    (preparedRequirement m width modulus positive base).Holds input.caller
      (({ code := arithmeticNativeCode m width modulus positive base, output := output } :
        AlgorithmRun (.quantum AlgorithmGate.model .empty)
          (context (m + width)) (preparedContext m width) shape).finalState
          Reference input.state) := by
  intro value
  cases value with
  | unit =>
      let initial : DensityOperator (Register.prod (preparedContext m width).register Reference) :=
        Execution.preparedDensity workKey (workLayout m width)
          (gidneyExponentWork_fresh m width) (gidneyExponentWork_disjoint m width)
          (workPreparation m width).normalized Reference
            input.caller.state.quantumMarginal
      let result :=
        ({ code := arithmeticNativeCode m width modulus positive base, output := output } :
        AlgorithmRun (.quantum AlgorithmGate.model .empty)
          (context (m + width)) (preparedContext m width) shape).finalState
          Reference input.state
      have actualWithService : result.quantumMarginal = DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (arithmeticNativeUnitary m width modulus positive base).matrix
            (1 : UnitaryOperator Reference))
          (Execution.preparedDensity workKey (workLayout m width)
            (gidneyExponentWork_fresh m width) (gidneyExponentWork_disjoint m width)
            (workPreparation m width).normalized Reference input.state.quantumMarginal) :=
        Execution.preparedUnitary_finalState_quantumMarginal (ctx := context (m + width))
          workKey (workLayout m width) (gidneyExponentWork_fresh m width)
          (gidneyExponentWork_disjoint m width)
          (arithmeticNativeUnitary m width modulus positive base) output Reference input.state
      have actual : result.quantumMarginal = DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor (arithmeticNativeUnitary m width modulus positive base).matrix
            (1 : UnitaryOperator Reference)) initial :=
        actualWithService.trans (congrArg
          (fun density : DensityOperator
              (Register.prod (preparedContext m width).register Reference) =>
            DensityOperator.applyUnitary
              (UnitaryOperator.prodTensor
                (arithmeticNativeUnitary m width modulus positive base).matrix
                (1 : UnitaryOperator Reference)) density)
          (congrArg
            (fun density : DensityOperator
                (Register.prod (context (m + width)).register Reference) =>
              Execution.preparedDensity workKey (workLayout m width)
                (gidneyExponentWork_fresh m width) (gidneyExponentWork_disjoint m width)
                (workPreparation m width).normalized Reference density)
            input.oracleInput_caller_quantumMarginal.symm))
      have semantic := actual.trans
        (congrArg (fun operator : UnitaryOperator (preparedContext m width).register =>
          DensityOperator.applyUnitary
            (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) initial)
          (arithmeticNativeUnitary_semantics m width modulus positive base))
      have observed := congrArg
        (fun density :
            DensityOperator (Register.prod (preparedContext m width).register Reference) =>
          DensityOperator.observeSelectionWithReference (preparedContext m width).quantumLayout
            Finset.univ Reference density)
        ((ExecutionState.executionState_mapClassical_const_block result CShape.Value.unit).trans
          semantic)
      have targetHolds :
          (StatePromise.mixed (preparedTarget m width modulus positive base Reference input.caller)
            (preparedTarget_normalized m width modulus positive base Reference input.caller)).Holds
              (preparedTarget m width modulus positive base Reference input.caller) := by
        change (preparedTarget m width modulus positive base Reference input.caller).matrix =
          ((preparedTarget m width modulus positive base Reference input.caller).mass : ℝ) •
            (preparedTarget m width modulus positive base Reference input.caller).matrix
        rw [preparedTarget_normalized]
        simp only [one_smul]
      exact (congrArg
        (StatePromise.mixed (preparedTarget m width modulus positive base Reference input.caller)
          (preparedTarget_normalized m width modulus positive base Reference input.caller)).Holds
        observed).mpr targetHolds

end

end QuantumAlg.MAU.Exponentiation.Gidney
