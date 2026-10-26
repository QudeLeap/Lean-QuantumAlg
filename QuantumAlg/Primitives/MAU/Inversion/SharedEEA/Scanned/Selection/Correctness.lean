/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Circuit
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Specification

/-! # Exact original source action and complete pool restoration of the paid selection -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.PreparedSelection

noncomputable section

open NumberTheory.SharedEEA

private lemma scan_prepared_source (width : Nat) (source : Registers width) (conjunction : Bool) :
    (SelectionScan.step width (source,
      (ScanMetadata.address source.coefficientLength source.quotientLength source.flags.first,
        (0#(ScanMetadata.addressWidth width), conjunction)))).1 =
      SelectionSpecification.selectedSource width source := by
  rw [SelectionScan.step_eq, ScanMetadata.address_toNat]
  unfold SelectionSpecification.selectedSource
  split
  · split
    · rw [SelectionExchange.action_eq_source]
    · rfl
  · rfl

/-- Every clean pool realizes the independent full-label source action and is returned unchanged. -/
lemma program_apply_sourceStep (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : Data width)
    (addressZero : state.2.1 = 0#(ScanMetadata.addressWidth width))
    (prefixZero : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (program width).applyNormalized environment
      (NormalizedVector.ket
        ((QubitLayout.canonical _).basisEquiv.symm ((encoding width).encode state))) =
      NormalizedVector.ket
        ((QubitLayout.canonical _).basisEquiv.symm ((encoding width).encode
          (SelectionSpecification.sourceStep width state.1, state.2))) := by
  rw [program_apply_encoded_ket_clean width environment state addressZero prefixZero]
  have sourceEq : SelectionEnable.sourceStep width
      (SelectionScan.step width (AddressPreparation.step width
        (SelectionEnable.step width state))).1 =
      SelectionSpecification.sourceStep width state.1 := by
    rw [AddressPreparation.step_clean width (SelectionEnable.step width state)
      addressZero prefixZero, scan_prepared_source]
    exact SelectionSpecification.enable_selected_enable width state.1
  have finalEq : SelectionEnable.step width
      ((SelectionScan.step width (AddressPreparation.step width
        (SelectionEnable.step width state))).1, state.2) =
      (SelectionSpecification.sourceStep width state.1, state.2) := by
    apply Prod.ext
    · exact sourceEq
    · rfl
  rw [finalEq]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.PreparedSelection
