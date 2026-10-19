/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Query.Coordinates
import all QuantumAlg.Algorithms.QPE.Query.Coordinates
import all QuantumAlg.Algorithms.QPE.Query
import all QuantumAlg.Core.Base.Oracle.Placement.Entries
import all QuantumAlg.Core.Base.Oracle.Placement.Construction
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# The complete untouched phase complement of a QPE query

All source systems and exactly one phase control belong to the query. The
remaining phase positions form its full complement. Equality there, together
with equality of the control, recovers equality of the entire phase label.
-/

namespace QuantumAlg.QuantumPhaseEstimation.Native

noncomputable section

/-- An unselected position must belong to the original phase register. -/
public lemma qpeNative_complement_phase_position {phaseWidth : Nat} (systemWidth : Nat)
  (stage : Fin phaseWidth)
    (position : Fin (phaseWidth + systemWidth))
    (unselected : position ∉ (queryApplication systemWidth stage).embedding.selection) :
    ∃ index : Fin phaseWidth, Fin.castAdd systemWidth index = position := by
  revert unselected
  refine Fin.addCases (fun phaseIndex => ?_) (fun sourceIndex => ?_) position
  · intro _
    exact ⟨phaseIndex, rfl⟩
  · intro unselected
    apply False.elim
    apply unselected
    rw [← qpeNative_query_source_position systemWidth stage sourceIndex]
    exact Finset.mem_map_of_mem
      (queryApplication systemWidth stage).embedding.position
      (Finset.mem_univ (Fin.natAdd 1 sourceIndex))

/-- Every phase wire other than the declared control is untouched by the query. -/
public lemma qpeNative_other_phase_unselected {phaseWidth : Nat} (systemWidth : Nat) (stage
  index : Fin phaseWidth)
    (different : index ≠ stage.rev) :
    Fin.castAdd systemWidth index ∉ (queryApplication systemWidth stage).embedding.selection := by
  intro selected
  obtain ⟨argument, _, same⟩ := Finset.mem_map.mp selected
  revert same
  refine Fin.addCases (fun control => ?_) (fun source => ?_) argument
  · intro same
    rw [qpeNative_query_control_position] at same
    apply different
    apply Fin.ext
    exact (congrArg Fin.val same).symm
  · intro same
    rw [qpeNative_query_source_position] at same
    have values := congrArg Fin.val same
    change phaseWidth + source.val = index.val at values
    omega

/-- Equal original phase labels give equal complete complements, regardless of source values. -/
public lemma qpeNative_query_complement_same_phase {phaseWidth : Nat} (systemWidth : Nat)
  (stage : Fin phaseWidth)
    (phase : Fin (2 ^ phaseWidth)) (leftSource rightSource : Fin (2 ^ systemWidth)) :
    ((queryApplication systemWidth stage).basisEquiv (pairBasis phase leftSource)).2 =
      ((queryApplication systemWidth stage).basisEquiv (pairBasis phase rightSource)).2 := by
  funext position
  rw [OracleModel.Application.oracleApplication_complement_value,
    OracleModel.Application.oracleApplication_complement_value]
  obtain ⟨index, same⟩ := qpeNative_complement_phase_position systemWidth stage position.val
    (Finset.mem_compl.mp position.property)
  apply Fin.ext
  have left := congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
    (leftWidth := phaseWidth) (rightWidth := systemWidth) phase leftSource index)
  have right := congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
    (leftWidth := phaseWidth) (rightWidth := systemWidth) phase rightSource index)
  rw [← same]
  exact left.trans right.symm

/-- The control and full complementary phase values determine the original entire phase label. -/
public lemma qpeNative_control_complement_phase_eq {phaseWidth : Nat} (systemWidth : Nat)
  (stage : Fin phaseWidth)
    (leftPhase rightPhase : Fin (2 ^ phaseWidth))
    (leftSource rightSource : Fin (2 ^ systemWidth))
    (control : finTwoEquiv.symm (leftPhase.val.testBit stage.val) =
      finTwoEquiv.symm (rightPhase.val.testBit stage.val))
    (complement :
      ((queryApplication systemWidth stage).basisEquiv (pairBasis leftPhase leftSource)).2 =
        ((queryApplication systemWidth stage).basisEquiv (pairBasis rightPhase rightSource)).2) :
    leftPhase = rightPhase := by
  apply (QuantumSignature.qubitsIndexEquiv phaseWidth).symm.injective
  funext index
  by_cases selected : index = stage.rev
  · subst index
    change (BinaryBasis.bigEndianEquiv phaseWidth).symm leftPhase stage.rev =
      (BinaryBasis.bigEndianEquiv phaseWidth).symm rightPhase stage.rev
    simpa only [BinaryBasis.bigEndianEquiv_symm_value, Fin.rev_rev] using control
  · let position : QuantumLayout.SelectedPosition
        (queryApplication systemWidth stage).embedding.selectionᶜ :=
      ⟨Fin.castAdd systemWidth index,
        Finset.mem_compl.mpr (qpeNative_other_phase_unselected systemWidth stage index selected)⟩
    have actual := congrFun complement position
    rw [OracleModel.Application.oracleApplication_complement_value,
      OracleModel.Application.oracleApplication_complement_value] at actual
    have left := congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := phaseWidth) (rightWidth := systemWidth) leftPhase leftSource index)
    have right := congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := phaseWidth) (rightWidth := systemWidth) rightPhase rightSource index)
    apply Fin.ext
    exact left.symm.trans ((congrArg Fin.val actual).trans right)

end

end QuantumAlg.QuantumPhaseEstimation.Native
