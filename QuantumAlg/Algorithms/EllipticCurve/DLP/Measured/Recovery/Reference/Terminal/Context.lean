/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Preparation
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Paired-result coordinate context

The mathematical reference carrier consists of the complete scalar workspace
and one finite-two result cell for every paired word bit. These context and
cell coordinates support full Store equivalences; they construct no circuit,
allocation, preparation, Fourier transform or measurement instruction.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ScalarMultiplication.MeasuredPlacement.Allocation

/-- Paired finite-two result coordinates extend the complete scalar reference context. -/
def exponentMeasurementContext (modulus exponentWidth : Nat) : RuntimeCtx .quantum :=
  MeasurementCells.context (after modulus.size (2 * exponentWidth)) 2 (2 * exponentWidth)

/-- Every paired word index identifies its own finite result cell in the reference carrier. -/
def exponentMeasurementCells (modulus exponentWidth : Nat) :
    Fin (2 * exponentWidth) →
      CWriteRef (exponentMeasurementContext modulus exponentWidth) (.finite 2) :=
  MeasurementCells.reference (after modulus.size (2 * exponentWidth)) 2 (2 * exponentWidth)

/-- Distinct paired result coordinates have distinct actual storage identities. -/
lemma exponentMeasurementCells_distinct (modulus exponentWidth : Nat) :
    Function.Injective fun index => (exponentMeasurementCells modulus exponentWidth index).key :=
  MeasurementCells.reference_key_injective _ 2 (2 * exponentWidth)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
