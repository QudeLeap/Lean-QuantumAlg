/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Layout
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Primitives.ZReset.Bank.Scope

/-!
# Actual fixed-sample Simon execution on one retained bank

One zero preparation allocates the original two-register bank. Each finite
round runs the supplied circuit, measures its first register and packs the
observed finite cells into that round's fixed slot. Later rounds first reset
the same bank with actual measurement and correction instructions. All sample
cells and the quantum bank remain in the complete final output.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native

open Execution

noncomputable section

/-- Every sample slot is created by the actual retain instruction. -/
@[implicit_reducible]
def allocateSlots (base : RuntimeCtx .quantum) (n : Nat) :
    (count : Nat) → Circuit base (slots base n count)
  | 0 => .id base
  | count + 1 =>
      .seq (allocateSlots base n count)
        (.retain (slots base n count) (slots base n count).canonicalFreshKey
          (.bits n) (slots base n count).canonicalFreshKey_fresh)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

/-- The single real quantum preparation, after the fixed classical slot allocations. -/
def prepare : Circuit (slots base n count) (bankContext base noQuantum n count) :=
  .prepare (slots base n count) (slots base n count).canonicalFreshKey (bankLayout n)
    (slots base n count).canonicalFreshKey_fresh (allocationDisjoint base noQuantum n count)
    (preparation n)

/-- Allocate fixed sample slots, prepare one bank and retain its measurement cells exactly once. -/
def allocate : Circuit base (context base noQuantum n count) :=
  .seq (allocateSlots base n count)
    (.seq (prepare base noQuantum n count)
      (MeasurementCells.allocate (bankContext base noQuantum n count) 2 n))

/-- Measure a source first-register position into its actual finite result cell. -/
def readout (index : Fin n) : ZReadout (context base noQuantum n count) where
  wire := wireEquiv n (nativeSimon_context_wires base noQuantum n count)
    ⟨index.val, by omega⟩
  output := by
    rw [nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count)]
    exact cells base noQuantum n count index

/-- The original first-register order fixes the actual sequence of measurement instructions. -/
def readouts : List (ZReadout (context base noQuantum n count)) :=
  List.ofFn (readout base noQuantum n count)

/-- One paid instruction writes the observed bits directly into the selected fixed sample slot. -/
def packing (index : Fin count) : ClassicalOp (.fixedVector n (.finite 2)) (.bits n)
    (context base noQuantum n count) (context base noQuantum n count) :=
  .packFiniteBits n (context base noQuantum n count)
    (MeasurementCells.input (bankContext base noQuantum n count) 2 n)
    (sampleRef base noQuantum n count index)

/-- The original supplied unitary, real finite measurements and charged row packing. -/
def sample (sampling : SamplingCircuit n) (index : Fin count) :
    Circuit (context base noQuantum n count) (context base noQuantum n count) :=
  .seq
    (.unitary (member n (nativeSimon_context_wires base noQuantum n count) sampling)
      (nativeSimon_member_physicalIdx n
        (nativeSimon_context_wires base noQuantum n count) sampling))
    (.seq (Circuit.measurementSequence (readouts base noQuantum n count))
      (.classical (packing base noQuantum n count index)))

/-- Paid reset acts on every existing bank qubit and releases only its classical scratch. -/
def reset : Circuit (context base noQuantum n count) (context base noQuantum n count) :=
  ZReset.BankScope.code
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))

/-- A later round resets and then samples the same bank into its own fixed slot. -/
def reusedSample (sampling : SamplingCircuit n) (index : Fin count) :
    Circuit (context base noQuantum n count) (context base noQuantum n count) :=
  .seq (reset base noQuantum n count) (sample base noQuantum n count sampling index)

/-- Sample zero uses the actual initial preparation; each later index includes its paid reset. -/
def sampleBatch (sampling : SamplingCircuit n) : (count : Nat) →
    Circuit (context base noQuantum n count) (context base noQuantum n count)
  | 0 => .id (context base noQuantum n 0)
  | count + 1 =>
      .seq (sample base noQuantum n (count + 1) sampling 0)
        (Circuit.forRange count fun index =>
          reusedSample base noQuantum n (count + 1) sampling index.succ)

/-- The exact finite program allocates its quantum bank only during initialization. -/
def code (sampling : SamplingCircuit n) : Circuit base (context base noQuantum n count) :=
  .seq (allocate base noQuantum n count) (sampleBatch base noQuantum n sampling count)

/-- Observe the real stored sample vector while retaining the complete bank and all live entries. -/
def run (sampling : SamplingCircuit n) :
    AlgorithmRun base (context base noQuantum n count) (.fixedVector count (.bits n)) where
  code := code base noQuantum n count sampling
  output := Output.all (context base noQuantum n count)
    (.read (samplesInput base noQuantum n count))

/-- The sample result does not hide or discard any surviving classical or quantum allocation. -/
theorem nativeSimon_output_listing (sampling : SamplingCircuit n) :
    (run base noQuantum n count sampling).output.listing =
      (context base noQuantum n count).keys := rfl

end

end QuantumAlg.SimonsProblem.FixedSample.Native
