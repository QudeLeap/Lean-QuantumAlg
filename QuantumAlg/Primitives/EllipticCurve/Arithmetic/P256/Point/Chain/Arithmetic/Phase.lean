/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Save
import all QuantumAlg.Components.Encoded.BitGates.Word.PhaseCorrection.Controlled
import all QuantumAlg.Primitives.MeasuredUncompute.Character
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources

/-!
# The actual product-recompute and same-mask correction

The existing zero target receives the selected product. Its literal Pauli
correction is followed by the same complete arithmetic adjoint. In the
inactive sector, the saved numerator receives the actual negatively
selected H-CNOT-H word instead. Both sectors return the entire original
label and preserve its exact relative phase. The measured mask is an
explicit branch parameter; its actual Store read is composed separately.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Phase

noncomputable section

open QuantumAlg.EncodedBit

def physicalSelector : Selector → EncodedBit Frame.encoding
  | .enable => Native.BorrowedControl.flag
  | .normal => Frame.normalBit

private lemma selector_get (assignment : PortAssignment) (selection : Selector)
    (state : Frame.Raw) :
    (physicalSelector selection).get state =
      (selectorBit assignment selection).get
        ((Placement.layout assignment).grouping state).2.2 := by
  cases selection
  · exact (Native.BorrowedControl.controlBit_get assignment state).symm
  · exact (Placement.savedNormal_get assignment state).symm

def word (port : WordPort) : EncodedBit.Word Frame.encoding 256 := ⟨port.bit⟩

private lemma selector_word_ne (selection : Selector) (port : WordPort) (index : Fin 256) :
    (physicalSelector selection).wire ≠ ((word port).bit index).wire := by
  change (physicalSelector selection).wire ≠ (port.bit index).wire
  intro same
  have positions := congrArg Fin.val same
  have bound := index.isLt
  cases selection
  · rw [physicalSelector, Native.BorrowedControl.flag_wire, WordPort.bit_wire] at positions
    cases port <;> simp only [WordPort.physicalIndex] at positions <;> omega
  · rw [physicalSelector, Frame.normalBit_wire, WordPort.bit_wire] at positions
    cases port <;> simp only [WordPort.physicalIndex] at positions <;> omega

def compute (assignment : PortAssignment) (selection : Selector) : Native.Circuit :=
  (Placement.layout assignment).place
    (Save.rawCleanProgram (Placement.restEncoding assignment) (selectorBit assignment selection))

lemma compute_apply (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (source saved : Word)
    (retained : Placement.Rest assignment)
    (admitted : (selectorBit assignment selection).get retained = true → Canonical source) :
    (compute assignment selection).applyNormalized environment
        (Native.ket (Native.arithmeticState assignment source Horner.zeroWord saved retained)) =
      Native.ket (Native.arithmeticState assignment source
        (Horner.productWord source saved ((selectorBit assignment selection).get retained))
        saved retained) :=
  (Placement.layout assignment).place_ket_of_eq _ _ _
    (Save.rawClean_product (Placement.restEncoding assignment) (selectorBit assignment selection)
      environment source saved retained admitted)

def recomputedProgram (assignment : PortAssignment) (selection : Selector)
    (outcome : Word) : Native.Circuit :=
  (compute assignment selection).seq
    ((EncodedBit.Word.PhaseCorrection.program (QubitLayout.canonical _) .empty
      (word assignment.target) (fun index => outcome.val.testBit index.val)).seq
        ((compute assignment selection).dagger (AlgorithmGate.oracleFreeAdjoints .empty)))

def inactiveProgram (assignment : PortAssignment) (selection : Selector)
    (outcome : Word) : Native.Circuit :=
  EncodedBit.Word.PhaseCorrection.Controlled.program (QubitLayout.canonical _) .empty
    (physicalSelector selection) (word assignment.multiplier)
    (selector_word_ne selection assignment.multiplier) false
    (fun index => outcome.val.testBit index.val)

def program (assignment : PortAssignment) (selection : Selector) (outcome : Word) :
    Native.Circuit :=
  (recomputedProgram assignment selection outcome).seq
    (inactiveProgram assignment selection outcome)

private lemma conjugated_phase {count : Nat} {layout : QuantumLayout count}
    (body correction : UnitaryCircuit AlgorithmGate.model .empty layout)
    (environment : OracleModel.empty.Interpretation)
    (initial computed : NormalizedVector layout.register) (coefficient : ℂ)
    (forward : body.applyNormalized environment initial = computed)
    (phase : correction.applyVec environment computed.vec = coefficient • computed.vec) :
    (body.seq (correction.seq (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))).applyVec
        environment initial.vec = coefficient • initial.vec := by
  have inverse : ((body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).matrix environment) =
      (body.matrix environment)⁻¹ := by
    rw [UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]
    exact Unitary.star_eq_inv _
  have backward := (congrArg
    ((body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyNormalized environment)
      forward).symm.trans
    (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized body _ inverse initial)
  have forwardVec : body.applyVec environment initial.vec = computed.vec :=
    congrArg NormalizedVector.vec forward
  have backwardVec : (body.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).applyVec
      environment computed.vec = initial.vec := congrArg NormalizedVector.vec backward
  rw [UnitaryCircuit.applyVec_seq, forwardVec,
    UnitaryCircuit.applyVec_seq, phase, UnitaryCircuit.applyVec_smul,
    backwardVec]

lemma recomputedProgram_applyVec (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (source saved outcome : Word)
    (retained : Placement.Rest assignment)
    (admitted : (selectorBit assignment selection).get retained = true → Canonical source) :
    (recomputedProgram assignment selection outcome).applyVec environment
        (Native.ket (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec =
      WalshHadamard.walshSign outcome
        (Horner.productWord source saved ((selectorBit assignment selection).get retained)) •
        (Native.ket
          (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec := by
  apply conjugated_phase _ _ environment _ _ _
    (compute_apply assignment selection environment source saved retained admitted)
  have actual := EncodedBit.Word.PhaseCorrection.phaseCorrection_sequence_ket
    (environment := environment) (QubitLayout.canonical _) .empty (word assignment.target)
    (EncodedBit.Word.PhaseCorrection.selected fun index => outcome.val.testBit index.val)
    (Native.arithmeticState assignment source
      (Horner.productWord source saved ((selectorBit assignment selection).get retained))
        saved retained)
  have character := MeasuredUncompute.measuredCorrection_sign_walsh
    (word assignment.target) (Native.arithmeticState assignment source
      (Horner.productWord source saved ((selectorBit assignment selection).get retained))
        saved retained)
    (Horner.productWord source saved ((selectorBit assignment selection).get retained)) outcome
    (fun index => (WordPort.bit_get assignment.target index _).trans
      (congrArg (fun value : Word => value.val.testBit index.val)
        (Native.arithmeticState_target assignment source _ saved retained)))
  exact actual.trans (congrArg (fun coefficient : ℂ => coefficient •
    (Native.ket (Native.arithmeticState assignment source
      (Horner.productWord source saved ((selectorBit assignment selection).get retained))
        saved retained)).vec) character)

lemma inactiveProgram_applyVec (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (source saved outcome : Word)
    (retained : Placement.Rest assignment) :
    (inactiveProgram assignment selection outcome).applyVec environment
        (Native.ket (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec =
      (if (selectorBit assignment selection).get retained = false then
        WalshHadamard.walshSign outcome saved else 1) •
        (Native.ket
          (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec := by
  have actual := EncodedBit.Word.PhaseCorrection.Controlled.controlledPhaseCorrection_sequence_ket
    (environment := environment) (QubitLayout.canonical _) .empty (physicalSelector selection)
    (word assignment.multiplier) (selector_word_ne selection assignment.multiplier) false
    (EncodedBit.Word.PhaseCorrection.selected fun index => outcome.val.testBit index.val)
    (Native.arithmeticState assignment source Horner.zeroWord saved retained)
  have selected : (physicalSelector selection).get
      (Native.arithmeticState assignment source Horner.zeroWord saved retained) =
        (selectorBit assignment selection).get retained :=
    (selector_get assignment selection _).trans (congrArg
      (fun grouped : Horner.OperandRegisters (Word × Placement.Rest assignment) =>
        (selectorBit assignment selection).get grouped.2.2)
      (Native.arithmeticState_grouping assignment source Horner.zeroWord saved retained))
  have character := MeasuredUncompute.measuredCorrection_sign_walsh
    (word assignment.multiplier)
    (Native.arithmeticState assignment source Horner.zeroWord saved retained) saved outcome
    (fun index => (WordPort.bit_get assignment.multiplier index _).trans
      (congrArg (fun value : Word => value.val.testBit index.val)
        (Native.arithmeticState_multiplier assignment source Horner.zeroWord saved retained)))
  have coefficients : (if (physicalSelector selection).get
        (Native.arithmeticState assignment source Horner.zeroWord saved retained) = false then
      EncodedBit.Word.PhaseCorrection.sign (word assignment.multiplier)
        (Native.arithmeticState assignment source Horner.zeroWord saved retained)
        (EncodedBit.Word.PhaseCorrection.selected fun index => outcome.val.testBit index.val)
      else 1) = (if (selectorBit assignment selection).get retained = false then
        WalshHadamard.walshSign outcome saved else 1) :=
    congrArg₂ (fun (enabled : Bool) (sign : ℂ) => if enabled = false then sign else 1)
      selected character
  exact actual.trans (congrArg (fun coefficient : ℂ => coefficient •
    (Native.ket
      (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec) coefficients)

private lemma combined_character (source saved outcome : Word) (selected : Bool) :
    WalshHadamard.walshSign outcome (Horner.productWord source saved selected) *
        (if selected = false then WalshHadamard.walshSign outcome saved else 1) =
      WalshHadamard.walshSign outcome (Save.savedWord source saved selected) := by
  cases selected
  · have zero : Horner.productWord source saved false = Horner.zeroWord :=
      Save.product_false source saved
    have zeroSign : WalshHadamard.walshSign outcome Horner.zeroWord = 1 :=
      @WalshHadamard.walshSign_zero_right width outcome
    have head : WalshHadamard.walshSign outcome (Horner.productWord source saved false) = 1 :=
      (congrArg (fun value : Word => WalshHadamard.walshSign outcome value) zero).trans
        zeroSign
    simp only [Save.savedWord, Bool.false_eq_true, if_false, if_true]
    exact (congrArg (fun coefficient : ℂ =>
      coefficient * WalshHadamard.walshSign outcome saved) head).trans (one_mul _)
  · simp only [Save.savedWord, if_true, Bool.true_eq_false, if_false, mul_one]

/-- The actual correction supplies the character of the active product or inactive saved Y. -/
lemma program_applyVec (assignment : PortAssignment) (selection : Selector)
    (environment : OracleModel.empty.Interpretation) (source saved outcome : Word)
    (retained : Placement.Rest assignment)
    (admitted : (selectorBit assignment selection).get retained = true → Canonical source) :
    (program assignment selection outcome).applyVec environment
        (Native.ket (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec =
      WalshHadamard.walshSign outcome
        (Save.savedWord source saved ((selectorBit assignment selection).get retained)) •
        (Native.ket
          (Native.arithmeticState assignment source Horner.zeroWord saved retained)).vec := by
  rw [program, UnitaryCircuit.applyVec_seq,
    recomputedProgram_applyVec assignment selection environment source saved outcome retained
      admitted,
    UnitaryCircuit.applyVec_smul,
    inactiveProgram_applyVec assignment selection environment source saved outcome retained,
    smul_smul, combined_character]

end

end Arithmetic.Phase

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
