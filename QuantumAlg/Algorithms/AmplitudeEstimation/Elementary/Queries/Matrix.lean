/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Queries
import all QuantumAlg.Core.Base.Oracle.Placement.Entries
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Exact source-suffix query matrices

The actual source placement preserves every phase and work value. Its matrix
is the declared preparation, or its granted inverse, tensored with identity
on the unchanged prefix. The proof follows the actual selected wire values.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

private def application {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :=
  OracleModel.Application.ofPositions (oracles U good) .preparation
    (QuantumSignature.qubits (totalQubits t n)).canonicalPlacement.layout
    (sourcePositions (phaseWidth t n) n) (fun _ => rfl)

private def pair {t n : Nat} (phase : Fin (2 ^ phaseWidth t n)) (source : Fin (2 ^ n)) :=
  (QuantumSignature.qubitsIndexEquiv (totalQubits t n)).symm (prodEquiv (phase, source))

private theorem selected_pair {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n))
    (phase : Fin (2 ^ phaseWidth t n)) (source : Fin (2 ^ n)) :
    ((application t U good).basisEquiv (pair phase source)).1 =
      (QuantumSignature.qubitsIndexEquiv n).symm source := by
  funext index
  apply Fin.ext
  exact (OracleModel.Application.oracleApplication_selected_value
    (application t U good) (pair phase source) index).trans
    (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_right
      (leftWidth := phaseWidth t n) (rightWidth := n) phase source index))

private theorem prefix_outside {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (index : Fin (phaseWidth t n)) :
    Fin.castAdd n index ∈ (application t U good).embedding.selectionᶜ := by
  apply Finset.mem_compl.mpr
  intro member
  obtain ⟨position, _, same⟩ := Finset.mem_map.mp member
  have values := congrArg Fin.val same
  change phaseWidth t n + position.val = index.val at values
  have bound := index.isLt
  omega

private theorem outside_prefix {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) (position : Fin (totalQubits t n))
    (outside : position ∈ (application t U good).embedding.selectionᶜ) :
    ∃ index : Fin (phaseWidth t n), Fin.castAdd n index = position := by
  revert outside
  refine Fin.addCases (fun index => ?_) (fun index => ?_) position
  · intro _
    exact ⟨index, rfl⟩
  · intro outside
    exact False.elim (Finset.mem_compl.mp outside
      (Finset.mem_map_of_mem (application t U good).embedding.position
        (Finset.mem_univ index)))

private theorem complement_pair {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n))
    (left right : Fin (2 ^ phaseWidth t n)) (first second : Fin (2 ^ n)) :
    ((application t U good).basisEquiv (pair left first)).2 =
        ((application t U good).basisEquiv (pair right second)).2 ↔ left = right := by
  constructor
  · intro same
    apply (QuantumSignature.qubitsIndexEquiv (phaseWidth t n)).symm.injective
    funext index
    have actual := congrFun same ⟨Fin.castAdd n index, prefix_outside t U good index⟩
    have one := BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := phaseWidth t n) (rightWidth := n) left first index
    have two := BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := phaseWidth t n) (rightWidth := n) right second index
    apply Fin.ext
    exact (congrArg Fin.val one).symm.trans
      ((congrArg Fin.val actual).trans (congrArg Fin.val two))
  · intro same
    subst right
    funext position
    rw [OracleModel.Application.oracleApplication_complement_value,
      OracleModel.Application.oracleApplication_complement_value]
    obtain ⟨index, equal⟩ := outside_prefix t U good position.val position.property
    apply Fin.ext
    rw [← equal]
    exact (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
      (leftWidth := phaseWidth t n) (rightWidth := n) left first index)).trans
      (congrArg Fin.val (BinaryBasis.bigEndianEquiv_prod_left
        (leftWidth := phaseWidth t n) (rightWidth := n) left second index)).symm

/-- Ordinary preparation acts on the source with identity on every original prefix value. -/
theorem preparation_matrix {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (preparation t U good).binaryMatrix =
      (1 : UnitaryOperator (Qubits (phaseWidth t n))).tensor U := by
  ext row column
  rcases (prodEquiv (m := phaseWidth t n) (n := n)).surjective row with
    ⟨⟨leftPhase, leftSource⟩, rfl⟩
  rcases (prodEquiv (m := phaseWidth t n) (n := n)).surjective column with
    ⟨⟨rightPhase, rightSource⟩, rfl⟩
  rw [UnitaryOperator.tensor_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  change (application t U good).operator (pair leftPhase leftSource)
    (pair rightPhase rightSource) = _
  rw [OracleModel.Application.oracleApplication_model_entry, selected_pair, selected_pair]
  change U ((QuantumSignature.qubitsIndexEquiv n)
      ((QuantumSignature.qubitsIndexEquiv n).symm leftSource))
    ((QuantumSignature.qubitsIndexEquiv n)
      ((QuantumSignature.qubitsIndexEquiv n).symm rightSource)) * (if _ then 1 else 0) = _
  simp only [Equiv.apply_symm_apply, complement_pair]
  change U leftSource rightSource * (if leftPhase = rightPhase then 1 else 0) =
    (if leftPhase = rightPhase then 1 else 0) * U leftSource rightSource
  exact mul_comm _ _

/-- Granted inverse preparation preserves the same complete phase and work prefix. -/
theorem inversePreparation_matrix {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (inversePreparation t U good).binaryMatrix =
      (1 : UnitaryOperator (Qubits (phaseWidth t n))).tensor U.dagger := by
  change (preparation t U.dagger good).binaryMatrix = _
  exact preparation_matrix t U.dagger good

end

end QuantumAlg.AmplitudeEstimation.Elementary
