/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.QubitPrimitive.Basis
import all QuantumAlg.Components.QubitPrimitive.Basis
import all QuantumAlg.Components.QubitPrimitive.Semantics
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Exact binary-word semantics of placed native primitives

The fixed big-endian interpretation connects the actual physical application
to the original addressed word operator. No additional encoding, gate instance
or caller-supplied operator equality is needed.
-/

namespace QuantumAlg.QubitPrimitive

noncomputable section

private theorem binary_increment (value : Bool) :
    finTwoEquiv (finTwoEquiv.symm value + 1) = !value := by
  cases value <;> rfl

private theorem bitIndex_value {n : Nat} (wire : Fin n) :
    (WireAddress.bitIndex wire).val = wire.rev.val := by
  change n - 1 - wire.val = n - (wire.val + 1)
  omega

private theorem decode_flip {n : Nat} (target : Fin n) (label : Fin (2 ^ n)) :
    (BinaryBasis.bigEndianEquiv n).symm (WireAddress.flipBit target label) =
      Function.update ((BinaryBasis.bigEndianEquiv n).symm label) target
        ((BinaryBasis.bigEndianEquiv n).symm label target + 1) := by
  funext observed
  apply finTwoEquiv.injective
  rw [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply,
    ← bitIndex_value observed]
  by_cases same : observed = target
  · subst observed
    rw [Function.update_self, WireAddress.bit_flipBit_self, bitIndex_value]
    exact (binary_increment _).symm
  · rw [Function.update_of_ne same, BinaryBasis.bigEndianEquiv_symm_value,
      Equiv.apply_symm_apply, ← bitIndex_value observed]
    exact WireAddress.bit_flipBit_of_ne (Ne.symm same) label

private theorem decoded_bit {n : Nat} (label : Fin (2 ^ n)) (wire : Fin n) :
    label.val.testBit (WireAddress.bitIndex wire).val =
      finTwoEquiv ((BinaryBasis.bigEndianEquiv n).symm label wire) := by
  rw [BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply, bitIndex_value]

private theorem basisAction_decoded {n : Nat} (primitive : QubitPrimitive n)
    (label : Fin (2 ^ n)) :
    basisAction primitive ((BinaryBasis.bigEndianEquiv n).symm label) =
      (BinaryBasis.bigEndianEquiv n).symm (primitive.applyLabel label) := by
  cases primitive with
  | x target => exact (decode_flip target label).symm
  | cnot control target distinct =>
      change Function.update ((BinaryBasis.bigEndianEquiv n).symm label) target
        ((BinaryBasis.bigEndianEquiv n).symm label control +
          (BinaryBasis.bigEndianEquiv n).symm label target) =
        (BinaryBasis.bigEndianEquiv n).symm (WireAddress.cnotMap control target label)
      rw [WireAddress.cnotMap, decoded_bit label control]
      generalize value : (BinaryBasis.bigEndianEquiv n).symm label control = bit
      fin_cases bit <;> simp [finTwoEquiv, decode_flip, add_comm]
  | toffoli first second target distinct firstTarget secondTarget =>
      change Function.update ((BinaryBasis.bigEndianEquiv n).symm label) target
        ((BinaryBasis.bigEndianEquiv n).symm label first *
          (BinaryBasis.bigEndianEquiv n).symm label second +
            (BinaryBasis.bigEndianEquiv n).symm label target) =
        (BinaryBasis.bigEndianEquiv n).symm (WireAddress.toffoliMap first second target label)
      rw [WireAddress.toffoliMap, decoded_bit label first, decoded_bit label second]
      generalize firstValue : (BinaryBasis.bigEndianEquiv n).symm label first = firstBit
      generalize secondValue : (BinaryBasis.bigEndianEquiv n).symm label second = secondBit
      fin_cases firstBit <;> fin_cases secondBit <;>
        simp [finTwoEquiv, decode_flip, add_comm]

/-- Actual native execution realizes the original addressed word operator with exact phase. -/
public theorem nativeApplication_operator {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) :
    (nativeApplication layout primitive).operator =
      UnitaryOperator.reindex layout.basisEquiv.symm primitive.operator := by
  refine (nativeApplication_operator_ofPerm layout primitive).trans
    (Eq.trans ?_ (UnitaryOperator.reindex_ofPerm
      (R := Qubits n) (S := layout.toQuantum.register) layout.basisEquiv.symm
      primitive.perm.symm).symm)
  apply congrArg UnitaryOperator.ofPerm
  apply Equiv.ext
  intro basis
  change nativeAmbientPermutation layout primitive basis =
    (BinaryBasis.bigEndianEquiv n).symm
      (primitive.perm.symm (BinaryBasis.bigEndianEquiv n basis))
  rw [nativeAmbientPermutation_apply layout primitive basis]
  have rowAction : primitive.perm.symm (BinaryBasis.bigEndianEquiv n basis) =
      primitive.applyLabel (BinaryBasis.bigEndianEquiv n basis) := by
    cases primitive <;> rfl
  rw [rowAction]
  exact (congrArg (basisAction primitive)
    ((BinaryBasis.bigEndianEquiv n).symm_apply_apply basis)).symm.trans
      (basisAction_decoded primitive (BinaryBasis.bigEndianEquiv n basis))


/-- Applying the actual placed gate to a binary ket gives the original addressed output word. -/
theorem nativeApplication_apply_ket {n : Nat} (layout : QubitLayout n)
    (primitive : QubitPrimitive n) (label : Fin (2 ^ n)) :
    (nativeApplication layout primitive).operator.apply
      (NormalizedVector.ket (layout.basisEquiv.symm label)) =
        NormalizedVector.ket (layout.basisEquiv.symm (primitive.applyLabel label)) := by
  rw [nativeApplication_operator_ofPerm layout primitive]
  refine (UnitaryOperator.ofPerm_apply_ket (R := layout.toQuantum.register)
    (nativeAmbientPermutation layout primitive) (layout.basisEquiv.symm label)).trans ?_
  apply congrArg NormalizedVector.ket
  apply (Equiv.symm_apply_eq (nativeAmbientPermutation layout primitive)).mpr
  symm
  change nativeAmbientPermutation layout primitive
    ((BinaryBasis.bigEndianEquiv n).symm (primitive.applyLabel label)) =
      (BinaryBasis.bigEndianEquiv n).symm label
  rw [nativeAmbientPermutation_apply layout primitive
    ((BinaryBasis.bigEndianEquiv n).symm (primitive.applyLabel label))]
  exact (basisAction_decoded primitive (primitive.applyLabel label)).trans
    (congrArg (BinaryBasis.bigEndianEquiv n).symm (primitive.applyLabel_applyLabel label))

end

end QuantumAlg.QubitPrimitive
