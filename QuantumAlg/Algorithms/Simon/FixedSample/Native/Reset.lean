/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset.Layout
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement

/-!
# Actual two-batch reset with reused Simon measurement cells

The first register is measured into the n existing finite cells and corrected
by one selected parallel X layer. The second register then overwrites those
same cells and executes its own selected parallel layer. These batches are
sequential because their classical storage is shared. The following sample
overwrites every result cell again before packing its new retained row.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

variable {oracles : OracleModel}
variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

/-- Real stored bits select native X members on precisely one physical n-wire half. -/
def correction (half : Fin 2) (value : CShape.Value (.fixedVector n (.finite 2))) :
    UnitaryCircuit AlgorithmGate.model oracles (context base noQuantum n count).quantumLayout :=
  UnitaryCircuit.placeAt (Gate.HadamardLayer.layout n)
    (context base noQuantum n count).quantumLayout (positions base noQuantum n count half)
    (dimensions base noQuantum n count half)
    (ZReset.BankParallel.Correction.layer oracles n (QubitReadouts.mask value))

/-- Measurements consume only the existing cells and never allocate child workspace. -/
@[implicit_reducible]
def measure {allowAllocation : Bool} (half : Fin 2) :
    Circuit (nativeModel oracles) (context base noQuantum n count)
      (context base noQuantum n count) allowAllocation :=
  Circuit.measurementSequence (readouts base noQuantum n count half)

/-- The branch reads the actual finite result vector written by the preceding measurements. -/
@[implicit_reducible]
def selected {allowAllocation : Bool} (half : Fin 2) :
    Circuit (nativeModel oracles) (context base noQuantum n count)
      (context base noQuantum n count) allowAllocation :=
  .branch (QubitReadouts.input (cells base noQuantum n count)) fun value =>
    .unitary (correction base noQuantum n count half value)

/-- One actual batch contains n Z writes and one possible native parallel correction layer. -/
@[implicit_reducible]
def batch {allowAllocation : Bool} (half : Fin 2) :
    Circuit (nativeModel oracles) (context base noQuantum n count)
      (context base noQuantum n count) allowAllocation :=
  .seq (measure base noQuantum n count half) (selected base noQuantum n count half)

/-- The two original bank halves reset in sequence using the same existing finite cells. -/
@[implicit_reducible]
def code {allowAllocation : Bool} :
    Circuit (nativeModel oracles) (context base noQuantum n count)
      (context base noQuantum n count) allowAllocation :=
  .seq (batch base noQuantum n count 0) (batch base noQuantum n count 1)

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset
