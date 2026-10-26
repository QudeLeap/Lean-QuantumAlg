/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Phase.Reference

/-!
# Exact products of the native record-conditioned adder operators

Each factor is the actual compiled native unitary, physical H/MZ/reset
branch, or stored-result native Z. The outcome assignment selects the
retained measurement record; connecting it to chronological Store writes
is a separate execution obligation. No phase correction or normalized
branch probability is assumed [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Instruction

noncomputable section

open EncodedBit NormalizedVector
open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {records : Nat}
  {oracles : OracleModel}

/-- Complete encoded label action of one actual native or physical reset factor. -/
def labelStep : Instruction encoding records → Data → Data
  | .native gates => GateSpec.stepList gates
  | .vent target _ => MeasuredUncompute.resetLabel target
  | .phase _ _ => id

/-- Exact unnormalized factor, retaining both measured-carry and paid native Z characters. -/
def branchWeight (outcome : Fin records → Fin 2) : Instruction encoding records → Data → ℂ
  | .native _, _ => 1
  | .vent target record, state =>
      invSqrt2 * MeasuredUncompute.character (outcome record) (target.get state)
  | .phase target record, state =>
      MeasuredUncompute.character (outcome record) (target.get state)

/-- The same physical instruction's retained operator beside the untouched reference. -/
def branchOperator (physical : QubitLayout encoding.width)
    (environment : oracles.Interpretation) (Reference : Register)
    (outcome : Fin records → Fin 2) : Instruction encoding records →
      HilbertOperator (Register.prod physical.toQuantum.register Reference)
  | .native gates => UnitaryOperator.prodTensor
      ((GateSpec.programList physical oracles gates).matrix environment)
      (1 : UnitaryOperator Reference)
  | .vent target record => MeasuredUncompute.branchOperator
      (environment := environment) target physical (outcome record) Reference
  | .phase target record => phaseReferenceOperator physical target (outcome record)
      environment Reference

private lemma native_reference_ket (physical : QubitLayout encoding.width)
    (environment : oracles.Interpretation) (gates : List (GateSpec encoding))
    (state : Data) {Reference : Register} (reference : Reference.Index) :
    (UnitaryOperator.prodTensor
      ((GateSpec.programList physical oracles gates).matrix environment)
      (1 : UnitaryOperator Reference)).applyVec
        (ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode state), reference)).vec =
      (ket (R := Register.prod physical.toQuantum.register Reference)
        (physical.basisEquiv.symm (encoding.encode (GateSpec.stepList gates state)),
          reference)).vec := by
  have actual := congrArg NormalizedVector.vec
    ((GateSpec.realizesList physical oracles gates environment).apply_encoded_ket state)
  change UnitaryOperator.applyVec
    ((GateSpec.programList physical oracles gates).matrix environment) _ = _ at actual
  rw [← HilbertVector.prodTensor_ket,
    UnitaryOperator.prodTensor_applyVec_prodTensor, actual, UnitaryOperator.one_applyVec,
    HilbertVector.prodTensor_ket]

/-- Every native record-conditioned factor retains all dirty/control/reference amplitudes. -/
lemma branchOperator_reference_ket (physical : QubitLayout encoding.width)
    (environment : oracles.Interpretation) (outcome : Fin records → Fin 2)
    (instruction : Instruction encoding records) (state : Data)
    {Reference : Register} (reference : Reference.Index) :
    (instruction.branchOperator physical environment Reference outcome).applyVec
        (ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode state), reference)).vec =
      instruction.branchWeight outcome state •
        (ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode (instruction.labelStep state)),
            reference)).vec := by
  cases instruction with
  | native gates =>
      simpa only [branchOperator, branchWeight, labelStep, one_smul,
        UnitaryOperator.applyVec] using
        native_reference_ket physical environment gates state reference
  | vent target record =>
      exact MeasuredUncompute.branch_reference_ket
        (environment := environment) target physical (outcome record) state reference
  | phase target record =>
      exact phaseProgram_reference_ket physical target (outcome record) environment state reference

/-- Chronological full-label fold of exactly the compiled instruction list. -/
def wordLabel : List (Instruction encoding records) → Data → Data
  | [], state => state
  | instruction :: rest, state => wordLabel rest (instruction.labelStep state)

/-- Product of the retained native characters on their actual successive input labels. -/
def wordWeight (outcome : Fin records → Fin 2) :
    List (Instruction encoding records) → Data → ℂ
  | [], _ => 1
  | instruction :: rest, state =>
      instruction.branchWeight outcome state * wordWeight outcome rest (instruction.labelStep state)

/-- Chronological product of the same physical native and measurement/reset factors. -/
def wordBranch (physical : QubitLayout encoding.width)
    (environment : oracles.Interpretation) (Reference : Register)
    (outcome : Fin records → Fin 2) : List (Instruction encoding records) →
      HilbertOperator (Register.prod physical.toQuantum.register Reference)
  | [] => 1
  | instruction :: rest =>
      wordBranch physical environment Reference outcome rest *
        instruction.branchOperator physical environment Reference outcome

/-- Exact retained product on each complete original encoded label and arbitrary reference. -/
lemma wordBranch_reference_ket (physical : QubitLayout encoding.width)
    (environment : oracles.Interpretation) (outcome : Fin records → Fin 2)
    (word : List (Instruction encoding records)) (state : Data)
    {Reference : Register} (reference : Reference.Index) :
    (wordBranch physical environment Reference outcome word).applyVec
        (ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode state), reference)).vec =
      wordWeight outcome word state •
        (ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode (wordLabel word state)), reference)).vec := by
  induction word generalizing state with
  | nil => simp [wordBranch, wordWeight, wordLabel, HilbertOperator.one_applyVec]
  | cons instruction rest ih =>
      rw [wordBranch, HilbertOperator.mul_applyVec, branchOperator_reference_ket,
        HilbertOperator.applyVec_smul, ih, smul_smul]
      rfl

/-- Linearity retains arbitrary dirty/control/reference correlations before any record is summed. -/
lemma wordBranch_coherent_reference (physical : QubitLayout encoding.width)
    (environment : oracles.Interpretation) (outcome : Fin records → Fin 2)
    (word : List (Instruction encoding records))
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (wordBranch physical environment Reference outcome word).applyVec
        (∑ index, amplitude index •
          (ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec) =
      ∑ index, (amplitude index * wordWeight outcome word (state index)) •
        (ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode (wordLabel word (state index))),
            reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul, wordBranch_reference_ket, smul_smul]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Instruction
