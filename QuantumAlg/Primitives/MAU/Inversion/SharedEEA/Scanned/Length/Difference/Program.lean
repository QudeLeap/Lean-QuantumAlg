/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Difference.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction
import all QuantumAlg.Primitives.MAU.Addition.TTK.Overflow
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-!
# Actual direct difference and its complete physical native inverse

The program subtracts the original address from the original prefix and
xors the borrow into the existing conjunction. It runs unconditionally
on all original labels. Copy selection and finite clipping are separate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma source_onto (length : Nat) :
    Function.Surjective (Addition.TTK.overflowEncoding length).encode :=
  Scanned.product_total _ _ (prodEquiv (m := length) (n := length)).surjective Scanned.bool_total

/-- Place the actual native overflow subtractor on precisely these existing pool systems. -/
def program (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (subsystem width length fits).program (source_onto length) (encoding_surjective width)
    (Addition.TTK.overflowSubtractionProgram length)

/-- Independent full finite subtraction action, including the entire original complement. -/
def step (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (state : Data width) : Data width :=
  ((subsystem width length fits).full (source_onto length) (encoding_surjective width)).step
    (fun pair => (Addition.TTK.overflowSubtractionOutput pair.1, pair.2)) state

/-- Exact coherent action holds before any zero-work, admitted-range or trajectory promise. -/
lemma program_realizes (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width length fits) environment
      (step width length fits) :=
  (subsystem width length fits).program_realizes (source_onto length)
    (encoding_surjective width) (Addition.TTK.ttkOverflowSubtraction_realizes length)

/-- Full arithmetic addition is the mathematical inverse of this same native difference. -/
def restore (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (state : Data width) : Data width :=
  ((subsystem width length fits).full (source_onto length) (encoding_surjective width)).step
    (fun pair => (Addition.TTK.overflowOutput pair.1, pair.2)) state

/-- The real forward overflow word reverses the original subtraction instruction sequence. -/
def restoreProgram (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (subsystem width length fits).program (source_onto length) (encoding_surjective width)
    (Addition.TTK.overflowProgram length)

/-- The actual emitted restore has the complete finite inverse action on this same carrier. -/
lemma restoreProgram_realizes (width length : Nat)
    (fits : length ≤ ScanMetadata.addressWidth width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (restoreProgram width length fits) environment
      (restore width length fits) :=
  (subsystem width length fits).program_realizes (source_onto length)
    (encoding_surjective width) (Addition.TTK.ttkOverflow_realizes_addition length)

/-- The complete restore returns every original work, metadata, flag and pool position. -/
lemma restore_step (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width)
    (state : Data width) : restore width length fits (step width length fits state) = state := by
  unfold restore step FullPlacement.step
  simp only [Equiv.apply_symm_apply, Addition.TTK.overflowOutput_overflowSubtractionOutput,
    Prod.eta, Equiv.symm_apply_apply]

/-- Physical placement changes no actual native event occurrence or multiplicity. -/
lemma program_eventTrace (width length : Nat) (fits : length ≤ ScanMetadata.addressWidth width) :
    (program width length fits).eventTrace =
      (Addition.TTK.overflowSubtractionProgram length).eventTrace :=
  (subsystem width length fits).program_eventTrace _ _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthDifference
