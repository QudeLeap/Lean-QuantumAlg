/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Readout
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Geometry
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Outputs
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Actual output cells and complete physical Fourier-bank coordinates

The real writable references in the endpoint retain each measured tuple bit.
The output vector is the structural read of exactly those cells. The basis
label is only a mathematical equivalence of those same physical wire values;
no packing operation, permutation gate or positive-width premise is introduced.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

noncomputable section

open Execution

/-- Tuple outcomes represented as the endpoint's actual shaped binary vector. -/
def resultValue (n : Nat) (outcome : Bits n) :
    CShape.Value (.fixedVector n (.finite 2)) :=
  .fixedVector (fun i => .finite (tupleCoordinates n outcome i))

/-- The dependent result reference is the same real retained cell after its dimension cast. -/
lemma resultCell_eq_cast (n : Nat) (i : Fin n) :
    resultCell n i = castBinaryOutput (qftSemiclassical_wires_qubits n i)
      (MeasurementCells.reference (inputContext n) 2 n i) := by
  have first : resultCell n i ≍ MeasurementCells.reference (inputContext n) 2 n i := by
    unfold resultCell
    exact cast_heq _ _
  have second : castBinaryOutput (qftSemiclassical_wires_qubits n i)
      (MeasurementCells.reference (inputContext n) 2 n i) ≍
        MeasurementCells.reference (inputContext n) 2 n i := by
    unfold castBinaryOutput
    exact eqRec_heq
      (φ := fun dimension : ℕ+ => CWriteRef (outputContext n) (.finite dimension))
      (qftSemiclassical_wires_qubits n i).symm
      (MeasurementCells.reference (inputContext n) 2 n i)
  exact eq_of_heq (first.trans second.symm)

/-- No two measured physical positions write the same result cell. -/
lemma resultCell_separate (n : Nat) :
    Function.Injective (fun i => (resultCell n i).key) := by
  intro left right same
  apply MeasurementCells.reference_key_injective (inputContext n) 2 n
  simpa only [resultCell_eq_cast, castBinaryOutput_key] using same

private lemma cast_read {ctx : RuntimeCtx .quantum} {first second : ℕ+}
    (same : first = second) (store : Store ctx) (output : CWriteRef ctx (.finite second)) :
    same ▸ store.read (.storage (castBinaryOutput same output).toCStorageRef) =
      store.read (.storage output.toCStorageRef) := by
  cases same
  rfl

private lemma cast_finite {first second : ℕ+} (same : first = second) (bit : Fin second) :
    same ▸ (CShape.Value.finite
      (Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) same).symm bit)) =
        CShape.Value.finite bit := by
  cases same
  rfl

/-- Every physical outcome is read back from the actual complete final store. -/
lemma resultRead_outcomeStore (n : Nat) (original : Store (outputContext n))
    (outcome : Bits n) :
    (resultRead n).eval
      (outcomeStore (wires n) (qftSemiclassical_wires_qubits n)
        (resultCell n) original outcome) = resultValue n outcome := by
  change CShape.Value.fixedVector (fun i =>
    (outcomeStore (wires n) (qftSemiclassical_wires_qubits n)
      (resultCell n) original outcome).read
        (.storage (MeasurementCells.reference (inputContext n) 2 n i).toCStorageRef)) = _
  congr 1
  funext i
  have stored := outcomeStore_read (wires n) (qftSemiclassical_wires_qubits n)
    (resultCell n) (resultCell_separate n) original outcome i
  have transported := congrArg (fun value => qftSemiclassical_wires_qubits n i ▸ value) stored
  have reference := resultCell_eq_cast n i
  have read := congrArg (fun output : CWriteRef (outputContext n)
      (.finite ((outputContext n).quantumLayout.wire (wires n i)).dimension) =>
    qftSemiclassical_wires_qubits n i ▸
      (outcomeStore (wires n) (qftSemiclassical_wires_qubits n)
        (resultCell n) original outcome).read (.storage output.toCStorageRef)) reference
  exact (cast_read (ctx := outputContext n) (qftSemiclassical_wires_qubits n i)
    (outcomeStore (wires n) (qftSemiclassical_wires_qubits n)
      (resultCell n) original outcome)
    (MeasurementCells.reference (inputContext n) 2 n i)).symm.trans
      (read.symm.trans (transported.trans
        (cast_finite (qftSemiclassical_wires_qubits n i) _)))

/-- Reading all outcome cells preserves exactly the existing source binary label. -/
lemma physicalLabel_resultValue (n : Nat) (outcome : Bits n) :
    physicalLabel n (resultValue n outcome) = binaryEquiv n outcome := by
  change BinaryBasis.bigEndianEquiv n
    ((BinaryBasis.bigEndianEquiv n).symm (binaryEquiv n outcome)) = _
  exact Equiv.apply_symm_apply _ _

/-- Distinct physical outcome tuples give distinct actual output vectors, including width zero. -/
lemma resultValue_injective (n : Nat) : Function.Injective (resultValue n) := by
  intro left right same
  apply (binaryEquiv n).injective
  simpa only [physicalLabel_resultValue] using congrArg (physicalLabel n) same

/-- All real binary output vectors occur as mathematical tuple labels; no runtime conversion. -/
lemma resultValue_surjective (n : Nat) : Function.Surjective (resultValue n) := by
  intro value
  refine ⟨(binaryEquiv n).symm (physicalLabel n value), ?_⟩
  apply (physicalLabelEquiv n).injective
  simp only [qftSemiclassical_physicalLabelEquiv_apply, physicalLabel_resultValue,
    Equiv.apply_symm_apply]

/-- Every physical endpoint wire occurs once in the actual measurement injection. -/
lemma wires_surjective (n : Nat) : Function.Surjective (wires n) :=
  (positionsOfEqualWires (bankLayout n) (outputContext n).quantumLayout
    (qftSemiclassical_output_wires n)).surjective

/-- The source bank coordinates read the full endpoint bank in its unchanged order. -/
lemma bankCoordinates_output_label (n : Nat) (basis : (outputContext n).register.Index) :
    binaryEquiv n
      (bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) basis).1 =
        outputBasisEquiv n basis := by
  rw [bankCoordinates_label]
  apply congrArg (BinaryBasis.bigEndianEquiv n)
  funext i
  apply Fin.ext
  have values := basisOfEqualWires_value (bankLayout n) (outputContext n).quantumLayout
    (qftSemiclassical_output_wires n)
    ((basisOfEqualWires (bankLayout n) (outputContext n).quantumLayout
      (qftSemiclassical_output_wires n)).symm basis) i
  rw [Equiv.apply_symm_apply] at values
  change (basis (wires n i)).val =
    ((basisOfEqualWires (bankLayout n) (outputContext n).quantumLayout
      (qftSemiclassical_output_wires n)).symm basis i).val at values ⊢
  exact values

/-- There is no omitted physical subsystem in the endpoint's bank complement. -/
lemma bankCoordinates_output_complement (n : Nat)
    (left right : (outputContext n).register.Index) :
    (bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) left).2 =
      (bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) right).2 := by
  apply (bankCoordinates_complement_eq_iff _ _ _ _).mpr
  intro position absent
  obtain ⟨i, same⟩ := wires_surjective n position
  exact False.elim (absent ((physicalBankEmbedding_member _ _).mpr ⟨i, same⟩))

/-- A different actual endpoint basis cannot carry the measured tuple's physical bank label. -/
lemma bankCoordinates_output_ne (n : Nat) (outcome : Bits n)
    (row : (outputContext n).register.Index)
    (different : row ≠ (outputBasisEquiv n).symm (binaryEquiv n outcome)) :
    (bankCoordinates (wires n) (qftSemiclassical_wires_qubits n) row).1 ≠ outcome := by
  intro same
  apply different
  apply (outputBasisEquiv n).injective
  rw [Equiv.apply_symm_apply, ← bankCoordinates_output_label, same]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint
