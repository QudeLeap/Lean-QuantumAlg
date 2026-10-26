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
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Reference.Factor

/-!
# All-input locality of both actual measured arithmetic calls

Each factor comes from the original save/reset/Store-selected native tail.
The complete actual Store, old hidden state and chronological paths remain
in the interpreter equation. This locality law imposes no arithmetic
correctness premise on active or exceptional labels.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution EncodedBit.WindowLookup
open Chain
open scoped BigOperators Kronecker

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires = ctx.quantumLayout.wires)
  (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
  (kind : Arithmetic.Call.Kind) (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)

/-- The actual same-mask feedback, reset and native prefix, without its untouched reference. -/
def callLocalOperator (store : Store ctx)
    (path : Reset.Instrument.Outcome (services := services) .numerator sameWires output)
    (environment : OracleModel.empty.Interpretation) : HilbertOperator ctx.register :=
  (Reset.Instrument.feedbackOperator sameWires mask
    (Arithmetic.Call.tail kind stream width bounded) environment
    (Reset.Instrument.resetRecord (services := services) .numerator sameWires output mask
      store path).1 : HilbertOperator ctx.register) *
    measuredWordLocalKraus (QubitLayout.canonical _) sameWires (resultWord .numerator)
      (resultWord_distinct .numerator) output mask store path environment *
    ((unitaryOfEqualWires (QubitLayout.canonical _).toQuantum ctx.quantumLayout sameWires
      (Arithmetic.Call.beforeReset kind stream width bounded)).matrix environment :
        HilbertOperator ctx.register)

/-- Every actual measured arithmetic branch has only identity on its external reference. -/
lemma call_branch_tensor_reference (store : Store ctx)
    (path : Reset.Instrument.Outcome (services := services) .numerator sameWires output)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    Arithmetic.Call.branchOperator sameWires output mask kind stream width bounded
        store path environment Reference =
      callLocalOperator sameWires output mask kind stream width bounded store path environment
        ⊗ₖ (1 : HilbertOperator Reference) := by
  unfold Arithmetic.Call.branchOperator Reset.Instrument.branchOperator
    Arithmetic.Call.prefixOperator callLocalOperator
  rw [unitaryOperator_prodTensor_identity, unitaryOperator_prodTensor_identity,
    measuredWordKraus_tensor_reference, HilbertOperator.kronecker_identity_mul,
    HilbertOperator.kronecker_identity_mul]

/-- Both literal measured arithmetic calls construct full unconditional local instruments. -/
def callInstrument
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Execution.Instrument (Arithmetic.Call.circuit sameWires output mask kind stream width bounded)
      (Reset.Instrument.Outcome (services := services) .numerator sameWires output)
      environment where
  record := Arithmetic.Call.record sameWires output mask kind stream width bounded
  operator store path :=
    callLocalOperator sameWires output mask kind stream width bounded store path environment.quantum
  blocks := by
    intro Reference History _ state result
    have actual := Arithmetic.Call.circuit_block_matrix sameWires output mask kind stream
      width bounded environment Reference state result
    refine actual.trans ?_
    apply Finset.sum_congr rfl
    intro original _
    apply Finset.sum_congr rfl
    intro path _
    by_cases selected : Execution.Instrument.retainedRecord (services := services)
        (Arithmetic.Call.record sameWires output mask kind stream width bounded)
        original path = result
    · rw [if_pos selected, if_pos selected, call_branch_tensor_reference,
        kronecker_referenceLift]
    · rw [if_neg selected, if_neg selected]

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
