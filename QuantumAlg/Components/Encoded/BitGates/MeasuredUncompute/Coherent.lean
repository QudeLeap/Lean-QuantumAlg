/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Branch
import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Semantics

/-!
# Common branch amplitude after an actual native phase correction

The consumer supplies an actual native circuit and proves its character on
the reachable label family. This compositional lemma retains that program;
it does not construct a free phase oracle or supply any measurement record.
The actual measurement/reset circuit and its complete block equation live in
the imported supporting modules [G25, main.tex:199-295].
-/

namespace QuantumAlg.EncodedBit.MeasuredUncompute

noncomputable section

open scoped BigOperators

open NormalizedVector

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {oracles : OracleModel} {environment : oracles.Interpretation}

/-- The measured character is its own exact inverse. -/
lemma character_mul_self (outcome : Fin 2) (value : Bool) :
    character outcome value * character outcome value = 1 := by
  unfold character
  split_ifs <;> norm_num

private lemma phase_reference_ket {R : Register}
    (program : UnitaryOperator R) (basis : R.Index) (scalar : ℂ)
    (actual : program.applyVec (NormalizedVector.ket (R := R) basis).vec =
      scalar • (NormalizedVector.ket (R := R) basis).vec)
    {Reference : Register} (reference : Reference.Index) :
    HilbertOperator.applyVec (R := Register.prod R Reference)
        (UnitaryOperator.prodTensor program (1 : UnitaryOperator Reference))
        (NormalizedVector.ket (R := Register.prod R Reference) (basis, reference)).vec =
      scalar • (NormalizedVector.ket (R := Register.prod R Reference) (basis, reference)).vec := by
  change HilbertOperator.applyVec (R := R) program _ = _ at actual
  ext row
  rcases row with ⟨localIndex, referenceIndex⟩
  rw [HilbertOperator.applyVec_ket]
  have column := congrArg (fun vector : HilbertVector R => vector localIndex) actual
  rw [HilbertOperator.applyVec_ket] at column
  change program localIndex basis * (if referenceIndex = reference then (1 : ℂ) else 0) = _
  rw [column]
  simp only [PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply]
  change (scalar * (if localIndex = basis then 1 else 0)) *
      (if referenceIndex = reference then 1 else 0) =
    scalar * (if (localIndex, referenceIndex) = (basis, reference) then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- An actually executed native correction cancels every retained character with common amplitude.
The family may contain arbitrary controls, dirty values and external-reference correlations. -/
lemma corrected_branch_coherent_reference (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (outcome : Fin 2)
    (phaseProgram : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (actual : ∀ index, phaseProgram.applyVec environment
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode (resetLabel target (state index))))).vec =
      character outcome (target.get (state index)) •
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode (resetLabel target (state index))))).vec) :
    (UnitaryOperator.prodTensor (phaseProgram.matrix environment)
      (1 : UnitaryOperator Reference)).applyVec
        ((branchOperator (environment := environment) target layout outcome Reference).applyVec
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod layout.toQuantum.register Reference)
              (layout.basisEquiv.symm (encoding.encode (state index)), reference index)).vec)) =
      invSqrt2 • ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod layout.toQuantum.register Reference)
          (layout.basisEquiv.symm (encoding.encode (resetLabel target (state index))),
            reference index)).vec := by
  rw [branch_coherent_reference]
  change HilbertOperator.applyVec
    (UnitaryOperator.prodTensor (phaseProgram.matrix environment)
      (1 : UnitaryOperator Reference) :
        HilbertOperator (Register.prod layout.toQuantum.register Reference)) _ = _
  rw [HilbertOperator.applyVec_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul,
    phase_reference_ket (phaseProgram.matrix environment) _ _ (actual index), smul_smul,
    smul_smul]
  congr 1
  calc
    (amplitude index * (invSqrt2 * character outcome (target.get (state index)))) *
        character outcome (target.get (state index)) =
      (invSqrt2 * amplitude index) *
        (character outcome (target.get (state index)) *
          character outcome (target.get (state index))) := by ring
    _ = _ := by rw [character_mul_self, mul_one]

end

end QuantumAlg.EncodedBit.MeasuredUncompute
