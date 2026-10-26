/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Hadamard
import all QuantumAlg.Core.Execution.Measurement.Effect

/-!
# Full retained physical Hadamard measurement columns

The actual parallel H matrix retains every physical complement coordinate.
Projecting its requested result values therefore leaves precisely the named
full basis column, with its exact product of native Hadamard amplitudes.
No assumption about the unmeasured systems or an encoded image is needed.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The original selected result values and all original complement values fix the full label. -/
lemma wordBasis_eq_of_coordinates (physical : QubitLayout encoding.width)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (first second : physical.toQuantum.Basis)
    (selected : ∀ index, first (target.bit index).wire = second (target.bit index).wire)
    (complement : physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct)) first =
      physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct)) second) : first = second := by
  funext wire
  by_cases present : wire ∈ Finset.univ.map (wordPosition target distinct)
  · obtain ⟨index, _, rfl⟩ := Finset.mem_map.mp present
    exact selected index
  · exact congrFun complement ⟨wire, Finset.mem_compl.mpr present⟩

/-- Actual joint result-value projector on the original existing physical systems. -/
def wordValueProjector (physical : QubitLayout encoding.width) (target : Word encoding width)
    (result : physical.toQuantum.Basis) : HilbertOperator physical.toQuantum.register :=
  ZMeasurement.projector
    (fun basis : physical.toQuantum.Basis => fun index : Fin width =>
      basis (target.bit index).wire)
    (fun index : Fin width => result (target.bit index).wire)

/-- Exact amplitude of the original native H bank between its named physical result values. -/
def wordHadamardAmplitude (physical : QubitLayout encoding.width) (target : Word encoding width)
    (row column : physical.toQuantum.Basis) : ℂ :=
  ∏ index : Fin width, Gate.HOp (Fin.cast rfl (row (target.bit index).wire))
    (Fin.cast rfl (column (target.bit index).wire))

private lemma wordHadamard_entry (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (environment : oracles.Interpretation) (row column : physical.toQuantum.Basis) :
    (wordHadamardProgram physical oracles target distinct).matrix environment row column =
      wordHadamardAmplitude physical target row column *
        (if physical.toQuantum.restrictComplementBasis
            (Finset.univ.map (wordPosition target distinct)) row =
          physical.toQuantum.restrictComplementBasis
            (Finset.univ.map (wordPosition target distinct)) column then 1 else 0) :=
  wordHadamardProgram_matrix_entry physical oracles target distinct row column environment

private lemma projector_applyVec_any {R : Register} {Outcome : Type}
    [decision : DecidableEq Outcome] (readout : R.Index → Outcome) (outcome : Outcome)
    (vector : HilbertVector R) (index : R.Index) :
    (ZMeasurement.projector readout outcome).applyVec vector index =
      if readout index = outcome then vector index else 0 := by
  cases Subsingleton.elim decision (Classical.decEq Outcome)
  exact ZMeasurement.projector_applyVec readout outcome vector index

/-- Projecting an actual parallel-H column retains its exact coefficient
and complete basis label. -/
lemma wordHadamard_projected_ket (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : Word encoding width)
    (distinct : Function.Injective fun index => (target.bit index).wire)
    (environment : oracles.Interpretation) (input result : physical.toQuantum.Basis)
    (complement : physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct)) result =
      physical.toQuantum.restrictComplementBasis
        (Finset.univ.map (wordPosition target distinct)) input) :
    HilbertOperator.applyVec ((wordValueProjector physical target result) *
      ((wordHadamardProgram physical oracles target distinct).matrix environment :
        HilbertOperator physical.toQuantum.register))
          (NormalizedVector.ket (R := physical.toQuantum.register) input).vec =
      wordHadamardAmplitude physical target result input •
          (NormalizedVector.ket (R := physical.toQuantum.register) result).vec := by
  ext row
  rw [HilbertOperator.mul_applyVec, wordValueProjector, projector_applyVec_any,
    HilbertOperator.applyVec_ket]
  change (if (fun index : Fin width => row (target.bit index).wire) =
      (fun index : Fin width => result (target.bit index).wire) then
        (wordHadamardProgram physical oracles target distinct).matrix environment row input
      else 0) = _
  rw [wordHadamard_entry]
  by_cases same : row = result
  · subst row
    simp only [if_true, complement, PiLp.smul_apply, smul_eq_mul,
      NormalizedVector.ket_apply, mul_one]
  · simp only [PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply, same, if_false,
      mul_zero]
    split_ifs with selected unchanged
    · exact False.elim (same (wordBasis_eq_of_coordinates physical target distinct row result
        (fun index => congrFun selected index) (unchanged.trans complement.symm)))
    · simp
    · rfl

end

end QuantumAlg.EncodedBit.WindowLookup
