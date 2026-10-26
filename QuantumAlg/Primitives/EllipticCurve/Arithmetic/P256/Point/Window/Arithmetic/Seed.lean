/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Seed
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active
import all QuantumAlg.Components.Encoded.BitGates.Predicate.Compute.Inverse
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport

/-!
# Full original-window boundary of the fixed quantum source preparation

The actual point program prepares its original fixed source bits, and its
own unitary adjoint clears them again after the updated numerical values.
Both directions keep every original address and supplied C/N/W bit. This
is the existing fixed native layer, independent of the mathematical point
seed or its coordinates; it introduces no classical initialization.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

attribute [local irreducible] modulus Inversion.Seed.blank Inversion.initial Inversion.Seed.program

/-- Complete original source workspace before its existing fixed native preparation. -/
def sourceBlank (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Address) : Raw :=
  (Inversion.Seed.blank input numerator (0, (0, false)) flags, address)

/-- The actual fixed source layer reaches precisely the original complete cleared initializer. -/
lemma sourceSeedProgram_blank (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Address) :
    (suffixProgram Inversion.Seed.program).applyNormalized environment
        (ket (sourceBlank input numerator flags address)) =
      ket (Chain.Arithmetic.Call.clearedInitial input numerator flags address) := by
  have actual := Inversion.Seed.program_blank environment input numerator (0, (0, false)) flags
  have lifted := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    Frame.encoding addressEncoding Inversion.Seed.program
    (Inversion.Seed.blank input numerator (0, (0, false)) flags)
    (Inversion.initial input numerator (0, (0, false)) flags) address actual
  change (suffixProgram Inversion.Seed.program).applyNormalized environment
    (ket (Inversion.Seed.blank input numerator (0, (0, false)) flags, address)) =
      ket (Inversion.initial input numerator (0, (0, false)) flags, address) at lifted
  exact lifted

/-- The same actual source adjoint clears its own source workspace at the updated X and Y. -/
lemma sourceSeedProgram_dagger (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Address) :
    (suffixProgram
      (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty))).applyNormalized
        environment (ket (Chain.Arithmetic.Call.clearedInitial input numerator flags address)) =
      ket (sourceBlank input numerator flags address) := by
  have actual := EncodedBit.PredicateCompute.dagger_apply_encoded_ket_of_apply
    Inversion.Seed.program environment
    (Inversion.Seed.blank input numerator (0, (0, false)) flags)
    (Inversion.initial input numerator (0, (0, false)) flags)
    (Inversion.Seed.program_blank environment input numerator (0, (0, false)) flags)
  have lifted := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    Frame.encoding addressEncoding
    (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty))
    (Inversion.initial input numerator (0, (0, false)) flags)
    (Inversion.Seed.blank input numerator (0, (0, false)) flags) address actual
  change (suffixProgram
    (Inversion.Seed.program.dagger (AlgorithmGate.oracleFreeAdjoints .empty))).applyNormalized
      environment (ket (Inversion.initial input numerator (0, (0, false)) flags, address)) =
        ket (Inversion.Seed.blank input numerator (0, (0, false)) flags, address) at lifted
  exact lifted

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
