/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Cascade
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Framing
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade.Correctness

/-!
# Full-density composition of actual conversions and measured point calls

The actual inverse coordinate conversion precedes the measured cascade and
the actual forward conversion follows it. Full-density correctness composes
their exact unitary actions with the independent point target on its supported
domain, retaining the complete quantum register and arbitrary reference.
The conclusion sums over classical stores and execution histories.
The support premise concerns the converted mathematical input density.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open Execution MeasuredUncompute

/-- Actual coordinate operators surround the independent chronological point target. -/
def convertedCascadeTarget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (Reference : Register) :
    UnitaryOperator (Register.prod (readyContext p.size count).register Reference) :=
  pairOperator p.size count (InPlaceTarget.modulusWord p) coefficient Reference *
    (cascadeTarget E points Reference order *
      pairOperator p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹ Reference)

/-- The same complete converted circuit has its full joint target on the point-cascade domain. -/
theorem convertedCascade_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) {Reference : Register} {H : Type} [Fintype H]
    (original : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (support : cascadeSupport E points Reference order
      (DensityOperator.applyUnitary
        (pairOperator p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹ Reference)
        original.quantumMarginal)) :
    ((convertedCascade E points order coefficient).execute Reference original).quantumMarginal =
      DensityOperator.applyUnitary (convertedCascadeTarget E points order coefficient Reference)
        original.quantumMarginal := by
  have before := pairCircuit_density p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹
    original
  have middleSupport : cascadeSupport E points Reference order
      (((pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹).execute
        Reference original).quantumMarginal) := by
    rw [before]
    exact support
  have middle := cascade_density E points order _ middleSupport
  have after := pairCircuit_density p.size count (InPlaceTarget.modulusWord p) coefficient
    ((cascade E points order).execute Reference
      ((pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹).execute
        Reference original))
  have joined := after.trans (congrArg
    (DensityOperator.applyUnitary
      (pairOperator p.size count (InPlaceTarget.modulusWord p) coefficient Reference))
    (middle.trans (congrArg (DensityOperator.applyUnitary (cascadeTarget E points Reference order))
      before)))
  rw [convertedCascade, Circuit.execute_seq, State.mapHistory_quantumMarginal,
    Circuit.execute_seq, State.mapHistory_quantumMarginal]
  exact joined.trans (by
    rw [convertedCascadeTarget, DensityOperator.applyUnitary_mul,
      DensityOperator.applyUnitary_mul])

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
