/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Reference
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.Prefix
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Rows.Frequency
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Locality.Inverse

/-!
# Exact retained Fourier-row action on full-layout basis vectors

The existing actual readout Kraus matrix sends a basis input to its negative
Fourier coefficient times the basis vector with the active bank zero. The
complete physical complement and arbitrary external Reference are identical.
The stored-prefix phase remains explicit. These equalities hold for every
active count, including zero; they introduce no physical source register,
permutation, instruction or domain requirement.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma partition_row_ket {R : Register} {Active Saved : Type}
    [DecidableEq Active] [DecidableEq Saved]
    (partition : R.Index ≃ Active × Saved) (zero : Active)
    (matrix : HilbertOperator R) (column : R.Index) (scalar : Complex)
    (entries : ∀ row, matrix row column =
      if (partition row).1 = zero ∧ (partition row).2 = (partition column).2 then scalar else 0) :
    matrix.applyVec (NormalizedVector.ket column : HilbertVector R) =
      scalar • (NormalizedVector.ket (partition.symm (zero, (partition column).2)) :
        HilbertVector R) := by
  ext row
  change matrix.applyVec (NormalizedVector.ket column : HilbertVector R) row =
    scalar * NormalizedVector.ket (partition.symm (zero, (partition column).2)) row
  rw [HilbertOperator.applyVec_ket, entries, NormalizedVector.ket_apply]
  have selected : (partition row).1 = zero ∧ (partition row).2 = (partition column).2 ↔
      row = partition.symm (zero, (partition column).2) := by
    constructor
    · intro same
      apply partition.injective
      have coordinates : partition row = (zero, (partition column).2) :=
        Prod.ext same.1 same.2
      exact coordinates.trans (partition.apply_symm_apply _).symm
    · intro same
      have coordinates := (congrArg partition same).trans (partition.apply_symm_apply _)
      have first := congrArg (fun pair : Active × Saved => pair.1) coordinates
      have last := congrArg (fun pair : Active × Saved => pair.2) coordinates
      exact ⟨first, last⟩
  by_cases same : row = partition.symm (zero, (partition column).2)
  · rw [if_pos (selected.mpr same), if_pos same, mul_one]
  · rw [if_neg (fun condition => same (selected.mp condition)), if_neg same, mul_zero]

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

/-- Zero only the same active bank in the complete coordinate description. -/
def windowZeroBankColumn (ports : Ports ctx totalBits active) (Reference : Register)
    (column : (ctx.register.prod Reference).Index) : (ctx.register.prod Reference).Index :=
  (referenceBankCoordinates ports.wires ports.qubits Reference).symm
    (Partner.zeroBits active,
      (referenceBankCoordinates ports.wires ports.qubits Reference column).2)

/-- The actual row retains its inherited prefix phases and the full saved basis label. -/
lemma window_source_suffix_ket (ports : Ports ctx totalBits active) (Reference : Register)
    (stored : Store ctx) (outcome : Bits active)
    (column : (ctx.register.prod Reference).Index) :
    (sourceWindowKraus ports Reference stored outcome).applyVec
        (NormalizedVector.ket column : HilbertVector (ctx.register.prod Reference)) =
      (Partner.fourierRows true active outcome
          (referenceBankCoordinates ports.wires ports.qubits Reference column).1 *
        Partner.phaseBasis active
          (Partner.suffixPhases true ports.start active (fun _ => 1)
            (Feedback.storedPrefix ports stored))
          (bankCoordinates ports.wires ports.qubits column.1).1) •
        (NormalizedVector.ket (windowZeroBankColumn ports Reference column) :
          HilbertVector (ctx.register.prod Reference)) := by
  exact partition_row_ket (referenceBankCoordinates ports.wires ports.qubits Reference)
    (Partner.zeroBits active) (sourceWindowKraus ports Reference stored outcome) column _
    (fun row => Feedback.window_source_suffix_entry ports Reference stored outcome row column)

/-- The same physical outcomes carry the reversed-frequency negative Fourier coefficient. -/
lemma window_source_frequency_ket (ports : Ports ctx totalBits active) (Reference : Register)
    (stored : Store ctx) (outcome : Bits active)
    (column : (ctx.register.prod Reference).Index) :
    (sourceWindowKraus ports Reference stored outcome).applyVec
        (NormalizedVector.ket column : HilbertVector (ctx.register.prod Reference)) =
      (star (QFTOperator active (decodedWindowFrequency active outcome)
          (binaryEquiv active
            (referenceBankCoordinates ports.wires ports.qubits Reference column).1)) *
        Feedback.wordScalar ports stored column.1 (List.finRange active)) •
        (NormalizedVector.ket (windowZeroBankColumn ports Reference column) :
          HilbertVector (ctx.register.prod Reference)) := by
  exact partition_row_ket (referenceBankCoordinates ports.wires ports.qubits Reference)
    (Partner.zeroBits active) (sourceWindowKraus ports Reference stored outcome) column _
    (fun row => window_source_frequency_entry ports Reference stored outcome row column)

/-- The same actually executed native feedback and readout product has this exact ket action. -/
lemma window_native_frequency_ket (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (stored : Store ctx) (outcome : Bits active)
    (column : (ctx.register.prod Reference).Index) :
    HilbertOperator.applyVec
        (outcomeKraus environment Reference active ports outcome *
          (Feedback.wordOperator ports environment Reference stored (List.finRange active) :
            HilbertOperator (ctx.register.prod Reference)))
        (NormalizedVector.ket column : HilbertVector (ctx.register.prod Reference)) =
      (star (QFTOperator active (decodedWindowFrequency active outcome)
          (binaryEquiv active
            (referenceBankCoordinates ports.wires ports.qubits Reference column).1)) *
        Feedback.wordScalar ports stored column.1 (List.finRange active)) •
        (NormalizedVector.ket (windowZeroBankColumn ports Reference column) :
          HilbertVector (ctx.register.prod Reference)) := by
  rw [window_feedbackKraus_eq_source]
  exact window_source_frequency_ket ports Reference stored outcome column

/-- The actual local inverse-window instrument keeps identity on the entire external Reference. -/
lemma window_inverseLocal_reference_ket (ports : Ports ctx totalBits active)
    (Reference : Register) (stored : Store ctx) (outcome : Bits active)
    (column : (ctx.register.prod Reference).Index) :
    (Execution.Instrument.referenceLift Reference (Source.inverseLocalOperator ports stored
      outcome)).applyVec
        (NormalizedVector.ket column : HilbertVector (ctx.register.prod Reference)) =
      (star (QFTOperator active (decodedWindowFrequency active outcome)
          (binaryEquiv active
            (referenceBankCoordinates ports.wires ports.qubits Reference column).1)) *
        Feedback.wordScalar ports stored column.1 (List.finRange active)) •
        (NormalizedVector.ket (windowZeroBankColumn ports Reference column) :
          HilbertVector (ctx.register.prod Reference)) := by
  rw [← Source.window_sourceInverse_referenceLift]
  exact window_source_frequency_ket ports Reference stored outcome column

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
