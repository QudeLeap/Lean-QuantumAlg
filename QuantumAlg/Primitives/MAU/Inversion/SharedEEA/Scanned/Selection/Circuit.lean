/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Preparation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Enable
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Scan.Metadata
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint

/-!
# Prepared coherent selection with actual inverse cleanup

The source phase-enable CNOTs surround complete address preparation, the
pruned native scan, and the actual unitary inverse of preparation. Every
clean address and prefix is returned to its initial state. The separate
conjunction bit may be dirty throughout; no measurement or reset is used.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.PreparedSelection

noncomputable section

open NumberTheory.SharedEEA

/-- The actual five-part selection program uses only the existing source and pool wires. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (SelectionEnable.program width).seq ((AddressPreparation.program width).seq
    ((SelectionScan.program width).seq
      (((AddressPreparation.program width).dagger (AlgorithmGate.oracleFreeAdjoints .empty)).seq
        (SelectionEnable.program width))))

private def ket (width : Nat) (state : Data width) :
    NormalizedVector (QubitLayout.canonical (encoding width).width).toQuantum.register :=
  NormalizedVector.ket
    ((QubitLayout.canonical _).basisEquiv.symm ((encoding width).encode state))

/-- Exact ket action of the paid composition, including restoration of the complete pool. -/
lemma program_apply_encoded_ket_clean (width : Nat)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (prefixZero : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (program width).applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical _).basisEquiv.symm ((encoding width).encode state))) =
      NormalizedVector.ket
        ((QubitLayout.canonical _).basisEquiv.symm ((encoding width).encode
          (SelectionEnable.step width
            ((SelectionScan.step width (AddressPreparation.step width
              (SelectionEnable.step width state))).1, state.2)))) := by
  let enabled := SelectionEnable.step width state
  let prepared := AddressPreparation.step width enabled
  let scanned := SelectionScan.step width prepared
  let restored : Data width := (scanned.1, state.2)
  have preparedEq : prepared = (enabled.1,
      (ScanMetadata.address enabled.1.coefficientLength enabled.1.quotientLength
        enabled.1.flags.first, (0#(ScanMetadata.addressWidth width), state.2.2.2))) :=
    AddressPreparation.step_clean width enabled addressZero prefixZero
  have preparedPrefix : prepared.2.2.1 = 0#(ScanMetadata.addressWidth width) := by
    rw [preparedEq]
  have scannedPool : scanned.2 = prepared.2 := SelectionScan.step_pool width prepared
  have scannedAddress :
      ScanMetadata.address scanned.1.coefficientLength scanned.1.quotientLength
        scanned.1.flags.first =
      ScanMetadata.address prepared.1.coefficientLength prepared.1.quotientLength
        prepared.1.flags.first := SelectionScan.step_address width prepared
  have prepareRestored : AddressPreparation.step width restored = scanned := by
    rw [AddressPreparation.step_clean width restored addressZero prefixZero]
    apply Prod.ext
    · rfl
    · change (ScanMetadata.address scanned.1.coefficientLength scanned.1.quotientLength
        scanned.1.flags.first, (0#(ScanMetadata.addressWidth width), state.2.2.2)) = scanned.2
      rw [scannedAddress, scannedPool, preparedEq]
  let inverse :=
    (AddressPreparation.program width).dagger (AlgorithmGate.oracleFreeAdjoints .empty)
  have inverseEq : inverse.matrix environment =
      ((AddressPreparation.program width).matrix environment)⁻¹ := by
    dsimp only [inverse]
    rw [UnitaryCircuit.dagger_matrix,
      Subsingleton.elim ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment)
        environment]
    exact Unitary.star_eq_inv _
  have unprepare : inverse.applyNormalized environment (ket width scanned) =
      ket width restored := by
    have forward :=
      (AddressPreparation.program_realizes width environment).apply_encoded_ket restored
    rw [prepareRestored] at forward
    exact (congrArg (inverse.applyNormalized environment) forward).symm.trans
      (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
        (AddressPreparation.program width) inverse inverseEq (ket width restored))
  unfold program
  exact UnitaryCircuit.applyNormalized_seq_of_eq
    ((SelectionEnable.program_realizes width environment).apply_encoded_ket state)
    (UnitaryCircuit.applyNormalized_seq_of_eq
      ((AddressPreparation.program_realizes width environment).apply_encoded_ket enabled)
      (UnitaryCircuit.applyNormalized_seq_of_eq
        (SelectionScan.program_apply_encoded_ket width environment prepared preparedPrefix)
        (UnitaryCircuit.applyNormalized_seq_of_eq unprepare
          ((SelectionEnable.program_realizes width environment).apply_encoded_ket restored))))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.PreparedSelection
