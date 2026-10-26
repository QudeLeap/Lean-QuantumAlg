/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Locality.Reset
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset
import all QuantumAlg.Core.Execution.Instrument.Naturality
import all QuantumAlg.Core.Execution.Instrument.Support

/-!
# All-input reference laws of the real active-bank reset

Structural induction follows the original finite reset sequence. Each MZ and
same-cell correction has its actual local Kraus operator; every original
Store write and chronological Path remains present. No clean, canonical or
good-label premise is imposed on the input, and no circuit is replaced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Cleanup.Parameters

variable (parameters : Cleanup.Parameters ctx)

private lemma one_referenceNatural (wire : Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceNatural (parameters.one wire) environment := by
  intro Reference operator History _ state
  exact window_sourceReset_reference_unitary wire (parameters.outputAt wire)
    (parameters.shifts wire) environment Reference operator state

private lemma one_referenceSupported (wire : Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceSupported (parameters.one wire) environment := by
  intro Reference allowed History _ state supported result basis absent
  exact window_sourceReset_reference_support wire (parameters.outputAt wire)
    (parameters.shifts wire) environment Reference allowed state supported result basis absent

/-- The original arbitrary-count MZ/X sequence commutes with every external-reference unitary. -/
lemma cleanup_referenceNatural (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceNatural (parameters.run count wires) environment
        := by
  induction count with
  | zero =>
      change Execution.ReferenceNatural (Circuit.id
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (allowAllocation := false) ctx) environment
      intro Reference operator History _ state
      rw [Circuit.execute_id, Circuit.execute_id]
      exact Execution.classical_unitary state _ _
  | succ count ih =>
      change Execution.ReferenceNatural ((parameters.one (wires 0)).seq
        (parameters.run count (fun index => wires index.succ))) environment
      exact (parameters.one_referenceNatural (wires 0) environment).seq (ih _)

/-- Every actual reset record retains all previously absent external-reference coordinates. -/
lemma cleanup_referenceSupported (count : Nat) (wires : Fin count → Fin ctx.systemCount)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceSupported (parameters.run count wires)
        environment := by
  induction count with
  | zero =>
      change Execution.ReferenceSupported (Circuit.id
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (allowAllocation := false) ctx) environment
      intro Reference allowed History _ state supported result basis absent
      rw [Circuit.execute_id]
      exact classical_reference_support state _ allowed supported result basis absent
  | succ count ih =>
      change Execution.ReferenceSupported ((parameters.one (wires 0)).seq
        (parameters.run count (fun index => wires index.succ))) environment
      exact (parameters.one_referenceSupported (wires 0) environment).seq (ih _)

end Cleanup.Parameters

namespace Sampling.Parameters

/-- Literal identity embedding preserves reference naturality of the same real active-bank reset. -/
lemma sampling_reset_referenceNatural (parameters : Sampling.Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceNatural (parameters.reset index) environment :=
  (parameters.resetParameters.cleanup_referenceNatural (index.lowerWidth + 1)
    (parameters.wire index) environment).embed_identity

/-- Literal identity embedding preserves reference support through the same real active reset. -/
lemma sampling_reset_referenceSupported (parameters : Sampling.Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceSupported (parameters.reset index) environment :=
  (parameters.resetParameters.cleanup_referenceSupported (index.lowerWidth + 1)
    (parameters.wire index) environment).embed_identity

end Sampling.Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
