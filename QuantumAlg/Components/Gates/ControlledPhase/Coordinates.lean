/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.ControlledPhase.Operator
import all QuantumAlg.Components.Gates.ControlledPhase.Operator
import all QuantumAlg.Components.BinaryLabelEncoding
public import QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Signature
public import QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Original controlled-phase targets in ordered binary coordinates

The original big-endian labels and physical coordinate vectors select the
same control and target bits. This bridge preserves the original target
operator for every register width and every supplied phase.
-/

namespace QuantumAlg

noncomputable section

/-- The original addressed phase reads exactly the supplied logical control and target bits. -/
public theorem qftControlledPhaseFactor_coordinates {width : Nat}
    (control target : Fin width) (angle : Real) (basis : Fin width → Fin 2) :
    qftControlledPhaseFactor control target angle (QuantumSignature.qubitsIndexEquiv width basis) =
      if finTwoEquiv (basis control) && finTwoEquiv (basis target) then
        Complex.exp ((angle : Complex) * Complex.I) else 1 := by
  have bit (index : Fin width) :
      (QuantumSignature.qubitsIndexEquiv width basis).val.testBit
        (WireAddress.bitIndex index).val = finTwoEquiv (basis index) := by
    change (BinaryBasis.bigEndianEquiv width basis).val.testBit
      (WireAddress.bitIndex index).val = finTwoEquiv (basis index)
    have reversed : (WireAddress.bitIndex index).val = index.rev.val := by
      simp only [WireAddress.bitIndex, Fin.val_rev]
      omega
    rw [reversed]
    exact BinaryBasis.bigEndianEquiv_bit width basis index
  simp only [qftControlledPhaseFactor, bit]

/-- Reindexing the unchanged target yields its exact diagonal on the ordered physical bits. -/
public theorem qftControlledPhaseOperator_coordinates {width : Nat}
    (control target : Fin width) (angle : Real) :
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv width).symm
      (qftControlledPhaseOperator control target angle)).val =
        Matrix.diagonal (fun (basis : Fin width → Fin 2) =>
          if finTwoEquiv (basis control) && finTwoEquiv (basis target) then
            Complex.exp ((angle : Complex) * Complex.I) else 1) := by
  refine Matrix.ext fun (row : Fin width → Fin 2) (column : Fin width → Fin 2) => ?_
  change (Matrix.diagonal (qftControlledPhaseFactor control target angle))
    (QuantumSignature.qubitsIndexEquiv width row)
    (QuantumSignature.qubitsIndexEquiv width column) = _
  change (if QuantumSignature.qubitsIndexEquiv width row =
      QuantumSignature.qubitsIndexEquiv width column then
        qftControlledPhaseFactor control target angle (QuantumSignature.qubitsIndexEquiv width row)
      else 0) =
    (if row = column then
      (if finTwoEquiv (row control) && finTwoEquiv (row target) then
        Complex.exp ((angle : Complex) * Complex.I) else 1) else 0)
  have factor := qftControlledPhaseFactor_coordinates control target angle row
  by_cases same : row = column
  · subst column
    simp only [factor]
  · have different : QuantumSignature.qubitsIndexEquiv width row ≠
        QuantumSignature.qubitsIndexEquiv width column :=
      fun equal => same ((QuantumSignature.qubitsIndexEquiv width).injective equal)
    simp only [if_neg different, if_neg same]

end

end QuantumAlg
