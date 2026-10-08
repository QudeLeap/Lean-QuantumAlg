/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Readout
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Actual measured and packed results jointly with the external reference

The real Z sequence writes its actual outcomes to finite cells. The charged
packing instruction reads them and writes the packed result. Every classical
observation of that resulting store has the exact fiber formula below, with
all reference matrix entries retained. In particular, observations may retain
borrowed classical values together with the sampled parameter and outcome.

The store expression records those existing instructions' writes. It neither
prescribes a measurement result nor introduces another execution operation.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
  (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
  (result : CWriteRef ctx (.bits (resultBits m ell width)))

/-- The existing measured-write sequence and its real charged packing instruction. -/
def measuredPacking : Circuit model ctx ctx :=
  .seq (Circuit.measurementSequence (readouts m ell width sameWires cells))
    (BitWord.instruction (packing m ell width cells result))

/-- The actual writes on one basis fiber, including the final real packing output write. -/
def packedBasisStore (store : Store ctx) (basis : ctx.register.Index) : Store ctx :=
  (Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := .empty)
    (readouts m ell width sameWires cells) store
    (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts m ell width sameWires cells) basis)).applyOp
      (packing m ell width cells result)

/-- The actual final packed cell contains the original source's complete two-exponent outcome. -/
theorem shortDLP_runtimePacked_output
    (distinct : Function.Injective (fun index => (cells index).key))
    (store : Store ctx) (basis : ctx.register.Index) :
    (packedBasisStore m ell width sameWires cells result store basis).read
        (.storage result.toCStorageRef) =
      CShape.Value.bits ((ShortDLP.measurement (registerParameters m ell width)).readout
        (RuntimePlacement.basisEquiv m ell width sameWires basis)) :=
  (Store.read_applyOp_output
    (Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts m ell width sameWires cells) store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := BitWord.model) (classicalOracles := .empty)
        (readouts m ell width sameWires cells) basis))
    (packing m ell width cells result)).trans
      (shortDLP_runtimePacking_measured_value m ell width sameWires cells distinct
        result store basis)

/-- Each observed packed store has its actual-input reference fiber,
including off-diagonal entries. -/
theorem shortDLP_runtimePacked_joint_reference_entry
    {Reference : Register} {History Observed : Type} [Fintype History] [Fintype Observed]
    (state : State ctx Reference (model.HiddenState × History))
    (observe : Store ctx → Observed) (value : Observed)
    (left right : Reference.Index) :
    (∑ basis : ctx.register.Index,
      DensityOperator.matrix
        ((ExecutionState.mapClassical
          ((measuredPacking m ell width sameWires cells result).execute Reference state)
          (fun entry => observe entry.1)).block value)
        (basis, left) (basis, right)) =
      ExecutionState.referenceFiberSum state (fun original basis =>
        if observe (packedBasisStore m ell width sameWires cells result original.1 basis) = value
        then 1 else 0) left right := by
  rw [ExecutionState.mapClassical_block_referenceFiberSum]
  rw [measuredPacking, Circuit.execute_seq]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  rw [BitWord.bitWord_instruction_execute]
  simp only [ExecutionState.referenceFiberSum_mapClassical]
  rw [Circuit.measurementSequence_referenceFiberSum]
  rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
