/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Naturality
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Chain
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Scope
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver

/-!
# Unconditional external-reference naturality of the actual allocating point Driver

This consumer uses the original paid five-array builder and the literal
six-query, two-measured-call body. All input labels and full classical,
hidden-state and chronological records are retained. No arithmetic promise
or separately supplied body action is an input to the resulting equality.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution ClassicalAlgorithms.Modular

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The actual constructed-table Driver leaves arbitrary reference unitaries completely natural. -/
lemma driver_reference_unitary (parameters : Driver.Parameters ctx)
    (frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame ctx 256)
    (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (Reference : Register) (operator : UnitaryOperator Reference)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (Driver.circuit parameters frame spec row).execute environment Reference
        (state.applyUnitary (fun _ =>
          UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator)) =
      ((Driver.circuit parameters frame spec row).execute environment Reference state).applyUnitary
        (fun _ => UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register) operator) := by
  have actual : Execution.ReferenceNatural (Driver.circuit parameters frame spec row) environment :=
    constructedTables_referenceNatural frame spec row
      (fun lift same table => (Driver.kernelParameters parameters lift same table.arrays).circuit)
      environment (fun lift same table =>
        chain_reference_unitary (Driver.kernelParameters parameters lift same table.arrays)
          environment)
  exact actual Reference operator state

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
