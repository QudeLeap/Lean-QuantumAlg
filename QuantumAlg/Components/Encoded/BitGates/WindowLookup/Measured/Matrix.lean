/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Semantics

/-!
# Complete retained blocks of the actual word measurement/reset circuit

Each operator is the original parallel H layer, the actual same-wire joint
projector, and the stored-mask selected physical X layer. The exact output
sums every original classical block in its real overwrite fiber and retains
all off-diagonal entries, including arbitrary external reference coordinates.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution
open scoped BigOperators

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- One actual outcome branch of the same original physical parallel H/MZ/reset program. -/
def measuredWordKraus (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path)
    (environment : oracles.Interpretation) (Reference : Register) :
    HilbertOperator (Register.prod ctx.register Reference) :=
  (UnitaryOperator.prodTensor
    ((measuredWordCorrection (services := services) physical sameWires target distinct
      output mask store path).matrix environment)
    (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference)) *
    Circuit.measurementPathProjector (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (services := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output) Reference path *
    (UnitaryOperator.prodTensor
      ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
        (wordHadamardProgram physical oracles target distinct)).matrix environment)
      (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod ctx.register Reference))

/-- Exact real output fibers of the original circuit, with the same actual per-record operator. -/
lemma measuredResetWordCircuit_block_matrix (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (measuredResetWordCircuit (oracles := oracles) (services := services)
        physical sameWires target distinct output mask).Path)))
    (row column : (Register.prod ctx.register Reference).Index) :
    (((measuredResetWordCircuit physical sameWires target distinct output mask).execute
      environment Reference state).block result).matrix row column =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ path,
        if measuredWordRecord physical sameWires target distinct output mask original path =
            result then
          (measuredWordKraus physical sameWires target distinct output mask original.1 path
            environment.quantum Reference * (state.block original).matrix *
            (measuredWordKraus physical sameWires target distinct output mask original.1 path
              environment.quantum Reference).conjTranspose) row column
        else 0 := by
  rw [measuredResetWordCircuit_execute, ExecutionState.mapClassical_block_matrix]
  simp only [Matrix.sum_apply, ExecutionState.applyUnitary_block]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro path _
  split_ifs
  · rw [ExecutionState.measureZ_block]
    simp only [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix,
      ZMeasurement.branch, measuredWordKraus, Circuit.measurementPathProjector,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rfl

end

end QuantumAlg.EncodedBit.WindowLookup
