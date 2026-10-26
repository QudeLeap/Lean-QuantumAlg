/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Owned

/-! # Actual enable directions on the same owned854 bank and complete classical Store -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable

noncomputable section

open Execution

local instance {Data : Type} : DecidableEq Data := Classical.decEq Data

def direction (inverse : Bool) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  if inverse then inverseProgram stream width bounded else program stream width bounded

variable {ctx : RuntimeCtx .quantum} (scope : OwnedScope ctx)

def physicalProgram (inverse : Bool) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    UnitaryCircuit AlgorithmGate.model .empty scope.viewed.quantumLayout :=
  unitaryOfEqualWires _ _ scope.viewed_wires (direction inverse stream width bounded)

def circuit {services : ClassicalOracleModel} (inverse : Bool) (stream : Fin 2)
    (width : Nat) (bounded : width ≤ 15) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx false :=
  .ownedLayoutView scope.view (.unitary (physicalProgram scope inverse stream width bounded))

lemma circuit_execute_complete {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (inverse : Bool) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (circuit scope inverse stream width bounded).execute environment Reference state =
      scope.view.join (((scope.view.split state).applyUnitary fun _ =>
        UnitaryOperator.prodTensor
          ((physicalProgram scope inverse stream width bounded).matrix environment.quantum)
          (1 : UnitaryOperator Reference)).mapClassical
            (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))) :=
  (Circuit.execute_ownedLayoutView scope.view _ environment Reference state).trans
    (congrArg scope.view.join (Circuit.execute_unitary environment (scope.view.split state)
      (physicalProgram scope inverse stream width bounded)))

lemma circuit_eventTrace {services : ClassicalOracleModel} (inverse : Bool) (stream : Fin 2)
    (width : Nat) (bounded : width ≤ 15)
    (path : (circuit scope (services := services) inverse stream width bounded).Path) :
    (circuit scope inverse stream width bounded).eventTrace path =
      (direction inverse stream width bounded).eventTrace BitWord.model services :=
  unitaryOfEqualWires_trace _ _ scope.viewed_wires
    (direction inverse stream width bounded) BitWord.model services

lemma circuit_quantumTime {services : ClassicalOracleModel} (inverse : Bool) (stream : Fin 2)
    (width : Nat) (bounded : width ≤ 15)
    (path : (circuit scope (services := services) inverse stream width bounded).Path) :
    (circuit scope inverse stream width bounded).quantumTime path =
      2 * (width + 1) + EncodedBit.Word.OneDirtyLayout.gateCount (width + 1) + 1 := by
  change DepthExpr.depthEval Resource.Event.quantumDuration
    ((physicalProgram scope inverse stream width bounded).eventDepth BitWord.model services) = _
  rw [physicalProgram, unitaryOfEqualWires_depth,
    UnitaryCircuit.unitaryCircuit_quantumDuration_classical_context]
  cases inverse
  · exact program_quantumTime stream width bounded
  · exact inverseProgram_quantumTime stream width bounded

lemma circuit_peakResidentSpace {services : ClassicalOracleModel} (inverse : Bool)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (path : (circuit scope (services := services) inverse stream width bounded).Path) :
    (circuit scope inverse stream width bounded).peakResidentSpace path = ctx.residentSpace :=
  (circuit scope inverse stream width bounded).fixed_peakResidentSpace path

lemma circuit_peakAuxiliarySpace {services : ClassicalOracleModel} (inverse : Bool)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (path : (circuit scope (services := services) inverse stream width bounded).Path) :
    (circuit scope inverse stream width bounded).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  (circuit scope inverse stream width bounded).fixed_peakAuxiliarySpace path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable
