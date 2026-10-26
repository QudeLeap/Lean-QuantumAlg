/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Phase
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact stored-result phase beside every external reference

The operator is the actual selected native Z or identity tensored with the
same reference identity. Its exact character is independent of all other
dirty/control/reference labels; no separability condition is imposed on the
incoming superposition [G25, main.tex:271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured

noncomputable section

open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {oracles : OracleModel}

/-- The actual selected native phase acts on the original register beside reference identity. -/
def phaseReferenceOperator (physical : QubitLayout encoding.width)
    (target : EncodedBit encoding) (outcome : Fin 2) (environment : oracles.Interpretation)
    (Reference : Register) :
    UnitaryOperator (Register.prod physical.toQuantum.register Reference) :=
  UnitaryOperator.prodTensor
    ((Instruction.phaseProgram (oracles := oracles) physical target outcome).matrix environment)
    (1 : UnitaryOperator Reference)

/-- Every full encoded/reference ket retains exactly the native selected phase character. -/
lemma phaseProgram_reference_ket (physical : QubitLayout encoding.width)
    (target : EncodedBit encoding) (outcome : Fin 2) (environment : oracles.Interpretation)
    (state : Data) {Reference : Register} (reference : Reference.Index) :
    (phaseReferenceOperator physical target outcome environment Reference).applyVec
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode state), reference)).vec =
      EncodedBit.MeasuredUncompute.character outcome (target.get state) •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode state), reference)).vec := by
  have actual := phaseProgram_applyVec_encoded_ket physical target outcome
    (environment := environment) state
  change UnitaryOperator.applyVec
    ((Instruction.phaseProgram physical target outcome).matrix environment) _ = _ at actual
  rw [phaseReferenceOperator, ← HilbertVector.prodTensor_ket,
    UnitaryOperator.prodTensor_applyVec_prodTensor, actual, UnitaryOperator.one_applyVec]
  ext index
  simp only [HilbertVector.prodTensor_apply, PiLp.smul_apply, smul_eq_mul]
  exact mul_assoc _ _ _

/-- Linearity retains every dirty/control/reference coherence with the exact stored phase. -/
lemma phaseProgram_coherent_reference (physical : QubitLayout encoding.width)
    (target : EncodedBit encoding) (outcome : Fin 2) (environment : oracles.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (phaseReferenceOperator physical target outcome environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec) =
      ∑ index, (amplitude index *
        EncodedBit.MeasuredUncompute.character outcome (target.get (state index))) •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec := by
  change HilbertOperator.applyVec
    (phaseReferenceOperator physical target outcome environment Reference :
      HilbertOperator (Register.prod physical.toQuantum.register Reference)) _ = _
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul]
  have actual := phaseProgram_reference_ket physical target outcome environment
    (state index) (reference index)
  change HilbertOperator.applyVec _ _ = _ at actual
  rw [actual, smul_smul]

end

end QuantumAlg.MAU.Addition.Gidney.Measured
