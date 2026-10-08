/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.FinPow
public import QuantumAlg.Algorithms.QPE.Query
public import QuantumAlg.Core.Base.Oracle.Placement.Entries
import all QuantumAlg.Algorithms.QPE.Query
import all QuantumAlg.Core.Base.Oracle.Placement.Entries
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Exact QPE source-query argument coordinates

The actual physical application reads the selected phase bit and the full
original source label. All values follow from the declared wire positions;
no basis permutation or replacement state is supplied independently.
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

/-- Binary labels for the original phase/source tensor encode the actual physical input word. -/
public def pairBasis {phaseWidth systemWidth : Nat}
    (phase : Fin (2 ^ phaseWidth)) (source : Fin (2 ^ systemWidth)) :
    (QuantumSignature.qubits (phaseWidth + systemWidth)).Basis :=
  (QuantumSignature.qubitsIndexEquiv (phaseWidth + systemWidth)).symm (prodEquiv (phase, source))

/-- The declared control occupies its original reversed phase position. -/
public theorem qpeNative_query_control_position {phaseWidth systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) (stage : Fin phaseWidth) (index : Fin 1) :
    (queryApplication unitary stage).embedding.position (Fin.castAdd systemWidth index) =
      Fin.castAdd systemWidth stage.rev := by
  change Fin.addCases (motive := fun _ : Fin (1 + systemWidth) =>
    Fin (phaseWidth + systemWidth))
    (fun _ : Fin 1 => Fin.castAdd systemWidth stage.rev)
    (Fin.natAdd phaseWidth) (Fin.castAdd systemWidth index) = _
  exact Fin.addCases_left index

/-- Each source argument remains at its original position after the phase prefix. -/
public theorem qpeNative_query_source_position {phaseWidth systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) (stage : Fin phaseWidth)
    (index : Fin systemWidth) :
    (queryApplication unitary stage).embedding.position (Fin.natAdd 1 index) =
      Fin.natAdd phaseWidth index := by
  change Fin.addCases (motive := fun _ : Fin (1 + systemWidth) =>
    Fin (phaseWidth + systemWidth))
    (fun _ : Fin 1 => Fin.castAdd systemWidth stage.rev)
    (Fin.natAdd phaseWidth) (Fin.natAdd 1 index) = _
  exact Fin.addCases_right index

/-- The declared arguments are the selected phase bit and original source coordinates. -/
public theorem qpeNative_query_selected_basis {phaseWidth systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) (stage : Fin phaseWidth)
    (phase : Fin (2 ^ phaseWidth)) (source : Fin (2 ^ systemWidth)) :
    ((queryApplication unitary stage).basisEquiv (pairBasis phase source)).1 =
      Fin.addCases (fun _ : Fin 1 => finTwoEquiv.symm (phase.val.testBit stage.val))
        ((QuantumSignature.qubitsIndexEquiv systemWidth).symm source) := by
  funext index
  refine Fin.addCases (fun first => ?_) (fun last => ?_) index
  · have zero : first = 0 := Subsingleton.elim _ _
    subst first
    apply Fin.ext
    have selected := OracleModel.Application.oracleApplication_selected_value
      (queryApplication unitary stage) (pairBasis phase source) (Fin.castAdd systemWidth 0)
    have original := congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := phaseWidth) (rightWidth := systemWidth) phase source stage.rev)
    change (((queryApplication unitary stage).basisEquiv (pairBasis phase source)).1
      (Fin.castAdd systemWidth 0)).val =
        (finTwoEquiv.symm (phase.val.testBit stage.val)).val
    refine selected.trans (original.trans ?_)
    simp only [BinaryBasis.bigEndianEquiv_symm_value, Fin.rev_rev]
  · apply Fin.ext
    have selected := OracleModel.Application.oracleApplication_selected_value
      (queryApplication unitary stage) (pairBasis phase source) (Fin.natAdd 1 last)
    have original := congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_right
      (leftWidth := phaseWidth) (rightWidth := systemWidth) phase source last)
    rw [qpeNative_query_source_position] at selected
    change (((queryApplication unitary stage).basisEquiv (pairBasis phase source)).1
      (Fin.natAdd 1 last)).val =
        (pairBasis phase source (Fin.natAdd phaseWidth last)).val at selected
    have right := congrArg Fin.val (Fin.addCases_right
      (motive := fun _ : Fin (1 + systemWidth) => Fin 2)
      (left := fun _ : Fin 1 => finTwoEquiv.symm (phase.val.testBit stage.val))
      (right := (QuantumSignature.qubitsIndexEquiv systemWidth).symm source) last)
    exact selected.trans (original.trans right.symm)

private theorem oneDecoded (bit : Fin 2) :
    (BinaryBasis.bigEndianEquiv 1).symm bit = (fun _ : Fin 1 => bit) := by
  funext index
  fin_cases index
  fin_cases bit <;> rfl

/-- The selected coordinates encode the original controlled source label exactly. -/
public theorem qpeNative_query_selected_binary {phaseWidth systemWidth : Nat}
    (unitary : UnitaryOperator (Qubits systemWidth)) (stage : Fin phaseWidth)
    (phase : Fin (2 ^ phaseWidth)) (source : Fin (2 ^ systemWidth)) :
    ((queryApplication unitary stage).basisEquiv (pairBasis phase source)).1 =
      (QuantumSignature.qubitsIndexEquiv (1 + systemWidth)).symm
        (prodEquiv (finTwoEquiv.symm (phase.val.testBit stage.val), source)) := by
  rw [qpeNative_query_selected_basis]
  change Fin.addCases (fun _ : Fin 1 => finTwoEquiv.symm (phase.val.testBit stage.val))
    ((BinaryBasis.bigEndianEquiv systemWidth).symm source) =
      (BinaryBasis.bigEndianEquiv (1 + systemWidth)).symm
        (prodEquiv (finTwoEquiv.symm (phase.val.testBit stage.val), source))
  rw [BinaryBasis.bigEndianEquiv_symm_prod (leftWidth := 1) (rightWidth := systemWidth),
    oneDecoded]

end

end QuantumAlg.QuantumPhaseEstimation.Native
