/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Native.Program
import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Semantics
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Independent semantics of literal native modular exponentiation

The mathematical target is the finite permutation that preserves both work
words and the exponent while XORing `base ^ exponent mod modulus` into the
arbitrary target.  It is defined independently of the circuit and its resource
trace.  The realization theorem for the emitted gate list proves exact matrix
equality, including all phases and external superpositions.
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

attribute [local implicit_reducible] oracleEncoding encoding
  Multiplication.Accumulate.Gidney.encoding nativeEncoding

/-- Mathematical change of field order between the prepared runtime carrier
and the independently specified arithmetic oracle. -/
def nativeOracleOrder (exponentWidth width : Nat) :
    NativeRegisters exponentWidth width ≃ OracleRegisters exponentWidth width where
  toFun state := ((state.2.1, state.1), state.2.2)
  invFun state := (state.1.2, (state.1.1, state.2))
  left_inv := by rintro ⟨⟨power, auxiliary⟩, exponent, target⟩; rfl
  right_inv := by rintro ⟨⟨exponent, power, auxiliary⟩, target⟩; rfl

private lemma xorPower_involutive {exponentWidth width : Nat}
    (value : Fin (2 ^ width)) :
    Function.Involutive (fun state : NativeRegisters exponentWidth width =>
      xorPower state value) := by
  intro state
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      change (state.1.1.val ^^^ value.val) ^^^ value.val = state.1.1.val
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · rfl
  · rfl

/-- The identity word loader is a complete mathematical permutation. -/
def nativeIdentityLoadEquiv (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    Equiv.Perm (NativeRegisters exponentWidth width) where
  toFun state := xorPower state (unitResidueWord modulus positive 1)
  invFun state := xorPower state (unitResidueWord modulus positive 1)
  left_inv := xorPower_involutive _
  right_inv := xorPower_involutive _

/-- Independent all-label action of identity load, modular-power XOR oracle,
and identity unload in the runtime field order. -/
def nativeArithmeticEquiv (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) : Equiv.Perm (NativeRegisters exponentWidth width) :=
  ((nativeIdentityLoadEquiv exponentWidth width modulus positive).trans
    (nativeOracleOrder exponentWidth width) |>.trans
      (unitPowerOracleEquiv exponentWidth width modulus base)).trans
        (nativeOracleOrder exponentWidth width).symm |>.trans
          (nativeIdentityLoadEquiv exponentWidth width modulus positive)

/-- The independent operation acts on any label, including noncanonical work. -/
def nativeArithmeticStep (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    NativeRegisters exponentWidth width → NativeRegisters exponentWidth width :=
  nativeArithmeticEquiv exponentWidth width modulus positive base

lemma nativeArithmeticStep_eq (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (state : NativeRegisters exponentWidth width) :
    nativeArithmeticStep exponentWidth width modulus positive base state =
      xorPower ((nativeOracleOrder exponentWidth width).symm
        (unitPowerOracleOutput modulus base
          ((nativeOracleOrder exponentWidth width)
            (xorPower state (unitResidueWord modulus positive 1)))))
        (unitResidueWord modulus positive 1) := by
  change xorPower ((nativeOracleOrder exponentWidth width).symm
      (unitPowerOracleEquiv exponentWidth width modulus base
        ((nativeOracleOrder exponentWidth width)
          (xorPower state (unitResidueWord modulus positive 1)))))
      (unitResidueWord modulus positive 1) = _
  rw [unitPowerOracleEquiv_apply]

/-- On freshly zeroed work, the independent arithmetic action restores both
work words and XORs the modular power into an arbitrary supplied target. -/
lemma nativeArithmeticStep_clean (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) (exponent : Fin (2 ^ exponentWidth))
    (target : Fin (2 ^ width)) :
    nativeArithmeticStep exponentWidth width modulus positive base
        ((0, 0), (exponent, target)) =
      ((0, 0), (exponent,
        ⟨target.val ^^^ (unitResidueWord modulus positive (base ^ exponent.val)).val,
          Nat.xor_lt_two_pow target.isLt
            (unitResidueWord modulus positive (base ^ exponent.val)).isLt⟩)) := by
  let initial := unitResidueWord modulus positive 1
  have loaded : xorPower ((0, 0), (exponent, target)) initial =
      ((initial, 0), (exponent, target)) := by
    apply Prod.ext
    · apply Prod.ext
      · apply Fin.ext
        change (0 : Nat) ^^^ initial.val = initial.val
        exact Nat.zero_xor _
      · rfl
    · rfl
  change xorPower ((nativeOracleOrder exponentWidth width).symm
    (unitPowerOracleEquiv exponentWidth width modulus base
      ((nativeOracleOrder exponentWidth width)
        (xorPower ((0, 0), (exponent, target)) initial)))) initial = _
  rw [loaded]
  change xorPower ((nativeOracleOrder exponentWidth width).symm
    (unitPowerOracleEquiv exponentWidth width modulus base
      ((exponent, initial, 0), target))) initial = _
  rw [unitPowerOracleEquiv_apply,
    unitPowerOracleOutput_clean exponentWidth width modulus positive base exponent target]
  apply Prod.ext
  · apply Prod.ext
    · apply Fin.ext
      change initial.val ^^^ initial.val = 0
      exact Nat.xor_self _
    · rfl
  · rfl

private def nativeLabelEquiv (exponentWidth width : Nat) :
    NativeRegisters exponentWidth width ≃
      (Qubits (nativeEncoding exponentWidth width).width).Index :=
  (Equiv.prodCongr (prodEquiv (m := width) (n := width))
    (prodEquiv (m := exponentWidth) (n := width))).trans
      (prodEquiv (m := width + width) (n := exponentWidth + width))

private lemma nativeLabelEquiv_eq_encode (exponentWidth width : Nat)
    (state : NativeRegisters exponentWidth width) :
    nativeLabelEquiv exponentWidth width state =
      (nativeEncoding exponentWidth width).encode state :=
  rfl

/-- The full physical reorder reads exactly the arithmetic fields in oracle order. -/
private lemma oracleBasisAt_encode (exponentWidth width : Nat)
    (state : NativeRegisters exponentWidth width) :
    UnitaryCircuit.basisAt
      (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum
      (nativeSourceLayout exponentWidth width)
      (oraclePosition exponentWidth width)
      (oraclePosition_dimensions exponentWidth width)
      ((nativeSourceBasisEquiv exponentWidth width).symm
        ((nativeEncoding exponentWidth width).encode state)) =
    (QubitLayout.canonical (oracleEncoding exponentWidth width).width).basisEquiv.symm
      ((oracleEncoding exponentWidth width).encode
        (nativeOracleOrder exponentWidth width state)) := by
  funext index
  change Fin ((exponentWidth + (width + width)) + width) at index
  apply Fin.ext
  change
    ((BinaryBasis.bigEndianEquiv ((width + width) + (exponentWidth + width))).symm
      (prodEquiv (prodEquiv (state.1.1, state.1.2),
        prodEquiv (state.2.1, state.2.2)))
      (oraclePosition exponentWidth width index)).val =
    ((BinaryBasis.bigEndianEquiv ((exponentWidth + (width + width)) + width)).symm
      (prodEquiv (prodEquiv (state.2.1, prodEquiv (state.1.1, state.1.2)),
        state.2.2)) index).val
  refine Fin.addCases (fun firstPart => ?_) (fun target => ?_) index
  · refine Fin.addCases (fun exponent => ?_) (fun work => ?_) firstPart
    · have position : oraclePosition exponentWidth width
          (Fin.castAdd width (Fin.castAdd (width + width) exponent)) =
          Fin.natAdd (width + width) (Fin.castAdd width exponent) := by
        apply Fin.ext
        simp only [oraclePosition_val, Fin.val_castAdd, Fin.val_natAdd,
          BinaryLabelEncoding.finIdentity, BinaryLabelEncoding.ofEquiv]
        split_ifs <;> omega
      rw [position]
      simp only [BinaryBasis.bigEndianEquiv_prod_right,
        BinaryBasis.bigEndianEquiv_prod_left]
    · refine Fin.addCases (fun power => ?_) (fun auxiliary => ?_) work
      · have position : oraclePosition exponentWidth width
            (Fin.castAdd width (Fin.natAdd exponentWidth (Fin.castAdd width power))) =
            Fin.castAdd (exponentWidth + width) (Fin.castAdd width power) := by
          apply Fin.ext
          simp only [oraclePosition_val, Fin.val_castAdd, Fin.val_natAdd,
            BinaryLabelEncoding.finIdentity, BinaryLabelEncoding.ofEquiv]
          split_ifs <;> omega
        rw [position]
        simp only [BinaryBasis.bigEndianEquiv_prod_left,
          BinaryBasis.bigEndianEquiv_prod_right]
      · have position : oraclePosition exponentWidth width
            (Fin.castAdd width (Fin.natAdd exponentWidth (Fin.natAdd width auxiliary))) =
            Fin.castAdd (exponentWidth + width) (Fin.natAdd width auxiliary) := by
          apply Fin.ext
          simp only [oraclePosition_val, Fin.val_castAdd, Fin.val_natAdd,
            BinaryLabelEncoding.finIdentity, BinaryLabelEncoding.ofEquiv]
          split_ifs <;> omega
        rw [position]
        simp only [BinaryBasis.bigEndianEquiv_prod_left,
          BinaryBasis.bigEndianEquiv_prod_right]
  · have position : oraclePosition exponentWidth width
        (Fin.natAdd (exponentWidth + (width + width)) target) =
        Fin.natAdd (width + width) (Fin.natAdd exponentWidth target) := by
      apply Fin.ext
      simp only [oraclePosition_val, Fin.val_natAdd,
        BinaryLabelEncoding.finIdentity, BinaryLabelEncoding.ofEquiv]
      split_ifs <;> omega
    rw [position]
    simp only [BinaryBasis.bigEndianEquiv_prod_right]

/-- Pure arithmetic relabelling from oracle-order words to native-order words. -/
private def nativeOracleBasisEquiv (exponentWidth width : Nat) :
    (Qubits (oracleEncoding exponentWidth width).width).Index ≃
      (Qubits (nativeEncoding exponentWidth width).width).Index :=
  (wordExponentiationBasis exponentWidth width).symm |>.trans
    (nativeOracleOrder exponentWidth width).symm |>.trans
      (nativeLabelEquiv exponentWidth width)

private lemma oracleEncode_eq_wordBasis (exponentWidth width : Nat)
    (state : OracleRegisters exponentWidth width) :
    (oracleEncoding exponentWidth width).encode state =
      wordExponentiationBasis exponentWidth width state := by
  rfl

private lemma nativeOracleBasisEquiv_encode (exponentWidth width : Nat)
    (state : NativeRegisters exponentWidth width) :
    nativeOracleBasisEquiv exponentWidth width
        ((oracleEncoding exponentWidth width).encode
          (nativeOracleOrder exponentWidth width state)) =
      (nativeEncoding exponentWidth width).encode state := by
  rw [oracleEncode_eq_wordBasis]
  simp only [nativeOracleBasisEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply]
  exact nativeLabelEquiv_eq_encode exponentWidth width state

private lemma nativeOracleBasisEquiv_symm_encode (exponentWidth width : Nat)
    (state : NativeRegisters exponentWidth width) :
    (nativeOracleBasisEquiv exponentWidth width).symm
        ((nativeEncoding exponentWidth width).encode state) =
      (oracleEncoding exponentWidth width).encode
        (nativeOracleOrder exponentWidth width state) := by
  apply (nativeOracleBasisEquiv exponentWidth width).injective
  rw [Equiv.apply_symm_apply, nativeOracleBasisEquiv_encode]

/-- The selected physical arithmetic oracle is the independent word operator
under the exact full-carrier field-order equivalence. -/
def nativeOracleWordOperator (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryOperator (Qubits (nativeEncoding exponentWidth width).width) :=
  UnitaryOperator.reindex (nativeOracleBasisEquiv exponentWidth width)
    (wordExponentiationOperator exponentWidth width modulus base)

private lemma reindex_ket_action {R S : Register} (equivalence : R.Index ≃ S.Index)
    (operator : UnitaryOperator R) (start finish : R.Index)
    (action : operator.apply (NormalizedVector.ket start) =
      NormalizedVector.ket finish) :
    (UnitaryOperator.reindex equivalence operator).apply
        (NormalizedVector.ket (equivalence start)) =
      NormalizedVector.ket (equivalence finish) := by
  have raw : operator.applyVec (NormalizedVector.ket start : HilbertVector R) =
      (NormalizedVector.ket finish : HilbertVector R) :=
    congrArg NormalizedVector.vec action
  have mapped := UnitaryOperator.reindex_applyVec equivalence operator
    (NormalizedVector.ket start : HilbertVector R)
  rw [HilbertVector.reindex_ket, raw, HilbertVector.reindex_ket] at mapped
  apply NormalizedVector.ext
  intro output
  change (UnitaryOperator.reindex equivalence operator).applyVec
    (NormalizedVector.ket (equivalence start) : HilbertVector S) output =
      (NormalizedVector.ket (equivalence finish) : HilbertVector S) output
  exact congrArg (fun state : HilbertVector S => state output) mapped

private lemma nativeOracleBasisEquiv_word (exponentWidth width : Nat)
    (state : OracleRegisters exponentWidth width) :
    nativeOracleBasisEquiv exponentWidth width
        (wordExponentiationBasis exponentWidth width state) =
      (nativeEncoding exponentWidth width).encode
        ((nativeOracleOrder exponentWidth width).symm state) := by
  have h := nativeOracleBasisEquiv_encode exponentWidth width
    ((nativeOracleOrder exponentWidth width).symm state)
  rw [← oracleEncode_eq_wordBasis exponentWidth width state]
  simpa only [Equiv.apply_symm_apply] using h

/-- The independent oracle word matrix acts on every native-order label. -/
lemma nativeOracleWordOperator_ket (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ)
    (state : NativeRegisters exponentWidth width) :
    (nativeOracleWordOperator exponentWidth width modulus base).apply
        (NormalizedVector.ket ((nativeEncoding exponentWidth width).encode state)) =
      NormalizedVector.ket (R := Qubits (nativeEncoding exponentWidth width).width)
        ((nativeEncoding exponentWidth width).encode
          ((nativeOracleOrder exponentWidth width).symm
            (unitPowerOracleOutput modulus base
              (nativeOracleOrder exponentWidth width state)))) := by
  have action := reindex_ket_action
    (nativeOracleBasisEquiv exponentWidth width)
    (wordExponentiationOperator exponentWidth width modulus base)
    (wordExponentiationBasis exponentWidth width
      (nativeOracleOrder exponentWidth width state))
    (wordExponentiationBasis exponentWidth width
      (unitPowerOracleOutput modulus base (nativeOracleOrder exponentWidth width state)))
    (wordExponentiationOperator_ket exponentWidth width modulus base
      (nativeOracleOrder exponentWidth width state))
  rw [nativeOracleBasisEquiv_word exponentWidth width
    (nativeOracleOrder exponentWidth width state),
    nativeOracleBasisEquiv_word exponentWidth width
      (unitPowerOracleOutput modulus base (nativeOracleOrder exponentWidth width state))]
    at action
  simpa only [nativeOracleWordOperator, Equiv.symm_apply_apply] using action

private def nativeIdentityLabelPermutation (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    Equiv.Perm ((Qubits (nativeEncoding exponentWidth width).width).Index) :=
  (nativeLabelEquiv exponentWidth width).permCongr
    (nativeIdentityLoadEquiv exponentWidth width modulus positive)

/-- Independent finite permutation for XOR loading the first work word. -/
def nativeIdentityWordOperator (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    UnitaryOperator (Qubits (nativeEncoding exponentWidth width).width) :=
  UnitaryOperator.ofPerm
    (nativeIdentityLabelPermutation exponentWidth width modulus positive).symm

private lemma nativeIdentityWordOperator_ket (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (state : NativeRegisters exponentWidth width) :
    (nativeIdentityWordOperator exponentWidth width modulus positive).apply
        (NormalizedVector.ket ((nativeEncoding exponentWidth width).encode state)) =
      NormalizedVector.ket (R := Qubits (nativeEncoding exponentWidth width).width)
        ((nativeEncoding exponentWidth width).encode
          (xorPower state (unitResidueWord modulus positive 1))) := by
  rw [nativeIdentityWordOperator, UnitaryOperator.ofPerm_apply_ket]
  apply congrArg NormalizedVector.ket
  change (nativeIdentityLabelPermutation exponentWidth width modulus positive).symm⁻¹
      ((nativeEncoding exponentWidth width).encode state) = _
  rw [Equiv.Perm.inv_def, Equiv.symm_symm, nativeIdentityLabelPermutation,
    Equiv.permCongr_apply, ← nativeLabelEquiv_eq_encode,
    Equiv.symm_apply_apply, nativeLabelEquiv_eq_encode]
  rfl

private lemma identityProgram_matrix_of_realizes (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    (body : UnitaryCircuit AlgorithmGate.model .empty (nativeSourceLayout exponentWidth width)) →
    UnitaryCircuit.Realizes (nativeEncoding exponentWidth width) body environment
      (fun state => xorPower state (unitResidueWord modulus positive 1)) →
    (body.matrix environment) =
      UnitaryOperator.reindex (nativeSourceBasisEquiv exponentWidth width).symm
        (nativeIdentityWordOperator exponentWidth width modulus positive) := by
  intro body realizes
  apply Subtype.ext
  ext output input
  change (body.matrix environment) output input =
    (nativeIdentityWordOperator exponentWidth width modulus positive)
      (nativeSourceBasisEquiv exponentWidth width output)
      (nativeSourceBasisEquiv exponentWidth width input)
  obtain ⟨state, encoded⟩ := (nativeLabelEquiv exponentWidth width).surjective
    (nativeSourceBasisEquiv exponentWidth width input)
  have inputEq :
      (nativeSourceBasisEquiv exponentWidth width).symm
          ((nativeEncoding exponentWidth width).encode state) = input := by
    apply (nativeSourceBasisEquiv exponentWidth width).injective
    rw [Equiv.apply_symm_apply, ← nativeLabelEquiv_eq_encode, encoded]
  rw [← inputEq, Equiv.apply_symm_apply]
  have circuit := congrArg
    (fun result : NormalizedVector (nativeSourceLayout exponentWidth width).register =>
      result output)
    (realizes.apply_encoded_ket state)
  have semantic := congrArg
    (fun result : NormalizedVector (Qubits (nativeEncoding exponentWidth width).width) =>
      result (nativeSourceBasisEquiv exponentWidth width output))
    (nativeIdentityWordOperator_ket exponentWidth width modulus positive state)
  have actualColumn :=
    (HilbertOperator.applyVec_ket
      ((body.matrix environment) :
        HilbertOperator (nativeSourceLayout exponentWidth width).register)
      ((nativeSourceBasisEquiv exponentWidth width).symm
        ((nativeEncoding exponentWidth width).encode state)) output).symm.trans circuit
  have semanticColumn :=
    (HilbertOperator.applyVec_ket
      (nativeIdentityWordOperator exponentWidth width modulus positive :
        HilbertOperator (Qubits (nativeEncoding exponentWidth width).width))
      ((nativeEncoding exponentWidth width).encode state)
      (nativeSourceBasisEquiv exponentWidth width output)).symm.trans semantic
  have ketBridge :
      (NormalizedVector.ket
          ((nativeSourceBasisEquiv exponentWidth width).symm
            ((nativeEncoding exponentWidth width).encode
              (xorPower state (unitResidueWord modulus positive 1))))) output =
        (NormalizedVector.ket
          ((nativeEncoding exponentWidth width).encode
            (xorPower state (unitResidueWord modulus positive 1))))
          (nativeSourceBasisEquiv exponentWidth width output) := by
    simp only [NormalizedVector.ket_apply, Equiv.eq_symm_apply]
  exact actualColumn.trans (ketBridge.trans semanticColumn.symm)

/-- The physical X loader equals the independent first-word XOR operator. -/
lemma identityLoadProgram_matrix (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    ((identityLoadProgram exponentWidth width modulus positive).matrix environment) =
      UnitaryOperator.reindex (nativeSourceBasisEquiv exponentWidth width).symm
        (nativeIdentityWordOperator exponentWidth width modulus positive) :=
  identityProgram_matrix_of_realizes exponentWidth width modulus positive
    (identityLoadProgram exponentWidth width modulus positive)
    (identityLoadProgram_realizes exponentWidth width modulus positive)

/-- Reverse X gates retain exact phase and the same all-label XOR action. -/
lemma identityUnloadProgram_matrix (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val) :
    ((identityUnloadProgram exponentWidth width modulus positive).matrix environment) =
      UnitaryOperator.reindex (nativeSourceBasisEquiv exponentWidth width).symm
        (nativeIdentityWordOperator exponentWidth width modulus positive) :=
  identityProgram_matrix_of_realizes exponentWidth width modulus positive
    (identityUnloadProgram exponentWidth width modulus positive)
    (identityUnloadProgram_realizes exponentWidth width modulus positive)

/-- Independently specified arithmetic oracle in its actual canonical physical basis. -/
def arithmeticOraclePhysicalOperator (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryOperator
      ((QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum).register :=
  UnitaryOperator.reindex
    (QubitLayout.canonical (oracleEncoding exponentWidth width).width).basisEquiv.symm
    (wordExponentiationOperator exponentWidth width modulus base)

/-- The selected-power compute, copy and uncompute circuit has the exact
independent all-label matrix in the original physical basis. -/
lemma oracleProgram_physical_matrix (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    ((oracleProgram exponentWidth width modulus base).matrix environment) =
      arithmeticOraclePhysicalOperator exponentWidth width modulus base := by
  have h := gidneyExponentOracle_matrix (environment := environment)
    exponentWidth width modulus base
  change UnitaryOperator.reindex
      (QubitLayout.canonical (oracleEncoding exponentWidth width).width).basisEquiv
      ((oracleProgram exponentWidth width modulus base).matrix environment) =
        wordExponentiationOperator exponentWidth width modulus base at h
  have h' := congrArg
    (UnitaryOperator.reindex
      (QubitLayout.canonical (oracleEncoding exponentWidth width).width).basisEquiv.symm) h
  rw [UnitaryOperator.unitaryOperator_reindex_cancel] at h'
  exact h'

/-- Independent selected-oracle matrix on the complete native source carrier. -/
def placedArithmeticOperator (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    UnitaryOperator (nativeSourceLayout exponentWidth width).register :=
  UnitaryCircuit.operatorAt
    (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum
    (nativeSourceLayout exponentWidth width)
    (oraclePosition exponentWidth width)
    (oraclePosition_dimensions exponentWidth width)
    (arithmeticOraclePhysicalOperator exponentWidth width modulus base)

lemma placedArithmeticOracle_matrix (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    ((placedArithmeticOracle exponentWidth width modulus base).matrix environment) =
      placedArithmeticOperator exponentWidth width modulus base := by
  rw [placedArithmeticOracle, UnitaryCircuit.placeAt_matrix,
    oracleProgram_physical_matrix]
  rfl

/-- The dimension-certified placement is exactly the independent oracle
permutation in the native binary word order, including all noncanonical labels. -/
lemma placedArithmeticOperator_word (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (base : (ZMod modulus.val)ˣ) :
    placedArithmeticOperator exponentWidth width modulus base =
      UnitaryOperator.reindex (nativeSourceBasisEquiv exponentWidth width).symm
        (nativeOracleWordOperator exponentWidth width modulus base) := by
  apply Subtype.ext
  ext output input
  change (UnitaryCircuit.operatorAt
      (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum
      (nativeSourceLayout exponentWidth width)
      (oraclePosition exponentWidth width)
      (oraclePosition_dimensions exponentWidth width)
      (arithmeticOraclePhysicalOperator exponentWidth width modulus base)) output input =
    (nativeOracleWordOperator exponentWidth width modulus base)
      (nativeSourceBasisEquiv exponentWidth width output)
      (nativeSourceBasisEquiv exponentWidth width input)
  rw [UnitaryCircuit.operatorAt_entry_of_surjective
    (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum
    (nativeSourceLayout exponentWidth width)
    (oraclePosition exponentWidth width)
    (oraclePosition_dimensions exponentWidth width)
    (oraclePosition_surjective exponentWidth width)]
  change (wordExponentiationOperator exponentWidth width modulus base)
      ((QubitLayout.canonical (oracleEncoding exponentWidth width).width).basisEquiv
        (UnitaryCircuit.basisAt
          (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum
          (nativeSourceLayout exponentWidth width)
          (oraclePosition exponentWidth width)
          (oraclePosition_dimensions exponentWidth width) output))
      ((QubitLayout.canonical (oracleEncoding exponentWidth width).width).basisEquiv
        (UnitaryCircuit.basisAt
          (QubitLayout.canonical (oracleEncoding exponentWidth width).width).toQuantum
          (nativeSourceLayout exponentWidth width)
          (oraclePosition exponentWidth width)
          (oraclePosition_dimensions exponentWidth width) input)) =
    (wordExponentiationOperator exponentWidth width modulus base)
      ((nativeOracleBasisEquiv exponentWidth width).symm
        (nativeSourceBasisEquiv exponentWidth width output))
      ((nativeOracleBasisEquiv exponentWidth width).symm
        (nativeSourceBasisEquiv exponentWidth width input))
  obtain ⟨rowState, rowEncoded⟩ := (nativeLabelEquiv exponentWidth width).surjective
    (nativeSourceBasisEquiv exponentWidth width output)
  obtain ⟨columnState, columnEncoded⟩ := (nativeLabelEquiv exponentWidth width).surjective
    (nativeSourceBasisEquiv exponentWidth width input)
  have rowEq : (nativeSourceBasisEquiv exponentWidth width).symm
      ((nativeEncoding exponentWidth width).encode rowState) = output := by
    apply (nativeSourceBasisEquiv exponentWidth width).injective
    rw [Equiv.apply_symm_apply, ← nativeLabelEquiv_eq_encode, rowEncoded]
  have columnEq : (nativeSourceBasisEquiv exponentWidth width).symm
      ((nativeEncoding exponentWidth width).encode columnState) = input := by
    apply (nativeSourceBasisEquiv exponentWidth width).injective
    rw [Equiv.apply_symm_apply, ← nativeLabelEquiv_eq_encode, columnEncoded]
  rw [← rowEq, ← columnEq]
  rw [oracleBasisAt_encode exponentWidth width rowState,
    oracleBasisAt_encode exponentWidth width columnState]
  simp only [Equiv.apply_symm_apply]
  rw [nativeOracleBasisEquiv_symm_encode exponentWidth width rowState,
    nativeOracleBasisEquiv_symm_encode exponentWidth width columnState]

/-- Circuit-independent all-label arithmetic operator in native binary order. -/
def nativeArithmeticWordOperator (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    UnitaryOperator (Qubits (nativeEncoding exponentWidth width).width) :=
  (nativeIdentityWordOperator exponentWidth width modulus positive) *
    ((nativeOracleWordOperator exponentWidth width modulus base) *
      (nativeIdentityWordOperator exponentWidth width modulus positive))

private lemma unitary_mul_apply_normalized {R : Register}
    (left right : UnitaryOperator R) (state : NormalizedVector R) :
    (left * right).apply state = left.apply (right.apply state) := by
  apply NormalizedVector.ext
  intro output
  change (left * right).applyVec state output =
    left.applyVec (right.applyVec state) output
  rw [UnitaryOperator.mul_applyVec]

/-- The independent complete word operator implements the mathematical
load, all-label modular-power oracle, and unload permutation. -/
lemma nativeArithmeticWordOperator_ket (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ)
    (state : NativeRegisters exponentWidth width) :
    (nativeArithmeticWordOperator exponentWidth width modulus positive base).apply
        (NormalizedVector.ket ((nativeEncoding exponentWidth width).encode state)) =
      NormalizedVector.ket (R := Qubits (nativeEncoding exponentWidth width).width)
        ((nativeEncoding exponentWidth width).encode
          (nativeArithmeticStep exponentWidth width modulus positive base state)) := by
  let identity := unitResidueWord modulus positive 1
  have load := nativeIdentityWordOperator_ket exponentWidth width modulus positive state
  have oracle := nativeOracleWordOperator_ket exponentWidth width modulus base
    (xorPower state identity)
  have unload := nativeIdentityWordOperator_ket exponentWidth width modulus positive
    ((nativeOracleOrder exponentWidth width).symm
      (unitPowerOracleOutput modulus base
        ((nativeOracleOrder exponentWidth width) (xorPower state identity))))
  rw [nativeArithmeticWordOperator, unitary_mul_apply_normalized,
    unitary_mul_apply_normalized, load, oracle, unload]
  apply congrArg NormalizedVector.ket
  exact congrArg (nativeEncoding exponentWidth width).encode
    (nativeArithmeticStep_eq exponentWidth width modulus positive base state).symm

/-- The complete source target is assembled only from independently defined
word operators and a dimension-certified placement. -/
def arithmeticNativeSourceOperator (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    UnitaryOperator (nativeSourceLayout exponentWidth width).register :=
  let load := UnitaryOperator.reindex (nativeSourceBasisEquiv exponentWidth width).symm
    (nativeIdentityWordOperator exponentWidth width modulus positive)
  load * (placedArithmeticOperator exponentWidth width modulus base * load)

lemma arithmeticNativeSourceOperator_word (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    arithmeticNativeSourceOperator exponentWidth width modulus positive base =
      UnitaryOperator.reindex (nativeSourceBasisEquiv exponentWidth width).symm
        (nativeArithmeticWordOperator exponentWidth width modulus positive base) := by
  unfold arithmeticNativeSourceOperator nativeArithmeticWordOperator
  rw [placedArithmeticOperator_word,
    UnitaryOperator.unitaryOperator_reindex_mul,
    UnitaryOperator.unitaryOperator_reindex_mul]

/-- Exact phase-sensitive equality for the literal arithmetic candidate. -/
lemma arithmeticNativeSourceProgram_matrix (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    ((arithmeticNativeSourceProgram exponentWidth width modulus positive base).matrix environment) =
      arithmeticNativeSourceOperator exponentWidth width modulus positive base := by
  rw [arithmeticNativeSourceProgram, UnitaryCircuit.seq_matrix,
    UnitaryCircuit.seq_matrix, identityLoadProgram_matrix,
    identityUnloadProgram_matrix, placedArithmeticOracle_matrix]
  simp only [arithmeticNativeSourceOperator, mul_assoc]

/-- Independently specified arithmetic composition on the actual prepared
runtime carrier. Its definition contains no circuit or resource projection. -/
def arithmeticNativeOperator (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    UnitaryOperator (preparedContext exponentWidth width).register :=
  UnitaryOperator.reindex (nativePlacementBasisEquiv exponentWidth width)
    (arithmeticNativeSourceOperator exponentWidth width modulus positive base)

/-- Exact matrix equality for the complete prepared arithmetic candidate. -/
lemma arithmeticNativeUnitary_semantics (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    ((arithmeticNativeUnitary exponentWidth width modulus positive base).matrix environment) =
      arithmeticNativeOperator exponentWidth width modulus positive base := by
  rw [arithmeticNativeUnitary_matrix, arithmeticNativeSourceProgram_matrix]
  rfl

/-- The prepared arithmetic target is the independent all-label word
permutation transported through the actual runtime basis. -/
lemma arithmeticNativeOperator_word (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    arithmeticNativeOperator exponentWidth width modulus positive base =
      UnitaryOperator.reindex (preparedBasisEquiv exponentWidth width).symm
        (nativeArithmeticWordOperator exponentWidth width modulus positive base) := by
  unfold arithmeticNativeOperator
  rw [arithmeticNativeSourceOperator_word,
    UnitaryOperator.unitaryOperator_reindex_trans]
  rfl

/-- Exact phase-sensitive matrix equality on the prepared runtime carrier. -/
lemma arithmeticNativeUnitary_word (exponentWidth width : Nat)
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (base : (ZMod modulus.val)ˣ) :
    ((arithmeticNativeUnitary exponentWidth width modulus positive base).matrix environment) =
      UnitaryOperator.reindex (preparedBasisEquiv exponentWidth width).symm
        (nativeArithmeticWordOperator exponentWidth width modulus positive base) := by
  rw [arithmeticNativeUnitary_semantics, arithmeticNativeOperator_word]


end

end QuantumAlg.MAU.Exponentiation.Gidney
