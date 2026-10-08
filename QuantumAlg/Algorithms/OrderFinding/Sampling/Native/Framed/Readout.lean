/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Execution.Measurement.Readout
import all QuantumAlg.Core.Execution.FiniteReadout
import all QuantumAlg.Core.Execution.Store

/-!
# Actual measured cells of the selected source sampler

Every phase wire writes a distinct retained cell. Reading that cell after the
actual measurement path yields the selected physical basis value. The proof
does not assume a preselected sample or discard the caller's classical frame.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

variable (ctx : RuntimeCtx .quantum) (noQuantum : ctx.quantumWires = [])

private theorem phaseReadout_key (t width : Nat) (index : Fin t) :
    (phaseReadout ctx noQuantum t width index).output.key =
      (MeasurementCells.reference (resultContext ctx noQuantum t width) 2 t index).key :=
  FiniteReadout.transported_key (phaseWire_dimension ctx noQuantum t width index) _

private theorem phaseReadout_read_value (t width : Nat) (index : Fin t)
    (store : Store (post ctx noQuantum t width)) :
    (store.read (.storage
      (phaseReadout ctx noQuantum t width index).output.toCStorageRef)).toFin.val =
      (store.read (.storage
        (MeasurementCells.reference
          (resultContext ctx noQuantum t width) 2 t index).toCStorageRef)).toFin.val :=
  FiniteReadout.transported_read_value (phaseWire_dimension ctx noQuantum t width index) _ store

/-- The real phase-measurement destinations are pairwise distinct. -/
theorem readouts_keys_nodup (t width : Nat) :
    ((readouts ctx noQuantum t width).map (fun item => item.output.key)).Nodup := by
  rw [readouts, List.map_ofFn]
  apply List.nodup_ofFn.mpr
  intro left right same
  apply MeasurementCells.reference_key_injective (resultContext ctx noQuantum t width) 2 t
  exact (phaseReadout_key ctx noQuantum t width left).symm.trans
    (same.trans (phaseReadout_key ctx noQuantum t width right))

/-- An actual Z write stores its physical basis value in the corresponding cell. -/
theorem measuredCell_value (t width : Nat) (store : Store (post ctx noQuantum t width))
    (basis : (post ctx noQuantum t width).register.Index) (index : Fin t)
    {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel} :
    ((Circuit.writeMeasurementPath (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      (readouts ctx noQuantum t width) store
      (Circuit.measurementBasisPath (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services)
        (readouts ctx noQuantum t width) basis)).read
        (.storage
          (MeasurementCells.reference
            (resultContext ctx noQuantum t width) 2 t index).toCStorageRef)).toFin.val =
      (basis (phaseWire ctx noQuantum t width index)).val := by
  have actual := Circuit.writeMeasurementBasis_read
    (gates := gates) (oracles := oracles)
    (operations := operations) (services := services)
    (readouts ctx noQuantum t width)
    (readouts_keys_nodup ctx noQuantum t width)
    (phaseReadout ctx noQuantum t width index) (List.mem_ofFn.mpr ⟨index, rfl⟩) store basis
  have numeric := congrArg (fun value => value.toFin.val) actual
  rw [phaseReadout_read_value] at numeric
  exact numeric

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
