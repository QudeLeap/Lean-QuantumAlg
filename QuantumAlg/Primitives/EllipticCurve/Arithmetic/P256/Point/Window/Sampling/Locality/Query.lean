/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Core.Execution.Instrument.Execution
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Native
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Instrument
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Reference.Factor

/-!
# All-input locality of the actual table query

The same runtime loader, inserted native body and paid measured unlookup
have a local Kraus product on every input label. Its operator reads the
actual returned measurement Store. No graph, arithmetic admission or
clean-input condition is needed for this full interpreter equation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution EncodedBit.WindowLookup
open scoped BigOperators Kronecker

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {lowWidth highRemaining : Nat}

/-- The local factors of the literal table query, retaining its actual stored measurement mask. -/
def queryLocalOperator
    (parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining)
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts parameters.physical parameters.sameWires
        parameters.frame.result parameters.output)).Path)
    (environment : OracleModel.empty.Interpretation) : HilbertOperator ctx.register :=
  (RuntimeUnlookup.restorationOperator parameters.frame (services := services)
    parameters.physical parameters.sameWires (.storage parameters.mask.toCStorageRef)
    parameters.parity parameters.temporary (RuntimeTable.splitInputs parameters.source)
    environment (measuredWordFinalStore (oracles := .empty) (services := services)
      parameters.physical parameters.sameWires parameters.frame.result parameters.output
      parameters.mask store path) : HilbertOperator ctx.register) *
    measuredWordLocalKraus parameters.physical parameters.sameWires parameters.frame.result
      parameters.frame.resultDistinct parameters.output parameters.mask store path environment *
    (body.matrix environment : HilbertOperator ctx.register) *
    ((parameters.observedLoader store).matrix environment : HilbertOperator ctx.register)

/-- Every actual query branch is its same local matrix beside the arbitrary reference identity. -/
lemma query_branch_tensor_reference
    (parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining)
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts parameters.physical parameters.sameWires
        parameters.frame.result parameters.output)).Path)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    parameters.insertedBranchOperator body store path environment Reference =
      queryLocalOperator parameters body store path environment ⊗ₖ
        (1 : HilbertOperator Reference) := by
  unfold RuntimeTable.CycleParameters.insertedBranchOperator RuntimeUnlookup.branchOperator
    queryLocalOperator
  rw [unitaryOperator_prodTensor_identity, unitaryOperator_prodTensor_identity,
    unitaryOperator_prodTensor_identity, measuredWordKraus_tensor_reference,
    HilbertOperator.kronecker_identity_mul, HilbertOperator.kronecker_identity_mul,
    HilbertOperator.kronecker_identity_mul]

/-- The full actual table-query records construct an unconditional local instrument. -/
def queryInstrument
    (parameters : RuntimeTable.CycleParameters encoding ctx 256 lowWidth highRemaining)
    (body : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Execution.Instrument (QueryInsertion.circuit parameters body)
      ((Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
        (resultReadouts parameters.physical parameters.sameWires
          parameters.frame.result parameters.output)).Path) environment where
  record := parameters.insertedRecord body
  operator store path := queryLocalOperator parameters body store path environment.quantum
  blocks := by
    intro Reference History _ state result
    have actual := QueryInsertion.circuit_block_matrix parameters body environment
      Reference state result
    refine actual.trans ?_
    apply Finset.sum_congr rfl
    intro original _
    apply Finset.sum_congr rfl
    intro path _
    exact (congrArg (fun operator : HilbertOperator (ctx.register.prod Reference) =>
      if Execution.Instrument.retainedRecord (services := services) (parameters.insertedRecord body)
          original path = result then
        operator * (state.block original).matrix * operator.conjTranspose
      else 0)
      ((query_branch_tensor_reference parameters body original.1 path
        environment.quantum Reference).trans (kronecker_referenceLift _))).trans
      (Execution.ite_decisions _ _ _ _)

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
