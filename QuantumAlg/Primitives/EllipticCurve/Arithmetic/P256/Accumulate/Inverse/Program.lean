/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Program
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-! # Complete actual native adjoint of source-restoring multiply-accumulate -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Inverse

noncomputable section

open QuantumAlg.EncodedBit Horner

variable {Saved : Type} (saved : BinaryLabelEncoding Saved)
  (multiplier : RetainedMultiplier saved) (outer : EncodedBit saved)
  (outerMultiplier : ∀ index,
    (operandSavedBit saved outer).wire ≠
      (operandMultiplierBit saved (.retained (multiplier.bits index))).wire)

/-- One actual native inverse for every original MAC instruction, in reverse execution order. -/
def program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (operandEncoding saved).width).toQuantum :=
  (Accumulate.program saved multiplier outer outerMultiplier).dagger
    (AlgorithmGate.oracleFreeAdjoints .empty)

lemma matrix_inverse (environment : OracleModel.empty.Interpretation) :
    (program saved multiplier outer outerMultiplier).matrix environment =
      ((Accumulate.program saved multiplier outer outerMultiplier).matrix environment)⁻¹ := by
  rw [program, UnitaryCircuit.dagger_matrix,
    Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
      environment]
  exact Unitary.star_eq_inv _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Accumulate.Inverse
