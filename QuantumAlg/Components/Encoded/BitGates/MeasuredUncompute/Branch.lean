/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.MeasuredUncompute.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Hadamard
import all QuantumAlg.Core.Execution.Measurement.Effect
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Exact retained character of each physical measurement/reset branch

The matrices are the native Hadamard, the actual measured-wire projector and
the actual outcome-selected identity/X. The target resets physically; every
other encoded wire remains arbitrary. Its measured character is retained
until a consumer executes its separately charged phase correction
[G25, main.tex:199-295].
-/

namespace QuantumAlg.EncodedBit.MeasuredUncompute

noncomputable section

open NormalizedVector

open scoped BigOperators Kronecker

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {oracles : OracleModel} {environment : oracles.Interpretation}

/-- Clear just the measured semantic bit, preserving all other encoded wires. -/
def resetLabel (target : EncodedBit encoding) (state : Data) : Data :=
  if target.get state then target.flip state else state

/-- The retained sign of the actual X-basis outcome on an input bit. -/
def character (outcome : Fin 2) (value : Bool) : ℂ :=
  if outcome = 1 ∧ value = true then -1 else 1

/-- Clearing the target is independent of its initial Boolean value. -/
lemma resetLabel_flip (target : EncodedBit encoding) (state : Data) :
    resetLabel target (target.flip state) = resetLabel target state := by
  simp only [resetLabel, get_flip_self, flip_flip]
  cases target.get state <;> rfl

/-- The outcome label at the actual encoded wire, with its physical dimension. -/
def actualOutcome (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (outcome : Fin 2) : Fin (layout.toQuantum.wire target.wire).dimension :=
  Fin.cast rfl outcome

private lemma physical_get (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (state : Data) :
    layout.basisEquiv.symm (encoding.encode state) target.wire =
      actualOutcome target layout (finTwoEquiv.symm (target.get state)) := by
  apply Fin.ext
  exact congrArg Fin.val (target.targetBasisEquiv_first state)

private lemma resetLabel_basis (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (state : Data) :
    layout.basisEquiv.symm (encoding.encode (resetLabel target state)) =
      Function.update (layout.basisEquiv.symm (encoding.encode state)) target.wire 0 := by
  funext index
  by_cases selected : index = target.wire
  · subst index
    rw [Function.update_self, physical_get]
    apply Fin.ext
    change (finTwoEquiv.symm (target.get (resetLabel target state))).val = 0
    unfold resetLabel
    cases value : target.get state <;> simp [value, get_flip_self, finTwoEquiv]
  · rw [Function.update_of_ne selected]
    unfold resetLabel
    cases value : target.get state
    · rfl
    · exact congrFun (congrArg Prod.snd (target.targetBasisEquiv_flip state)) ⟨index, selected⟩

/-- Exactly the identity/X circuit selected by this measured outcome. -/
def correction (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (outcome : Fin 2) : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  QuditShift.qubitShiftCircuit layout.toQuantum target.wire rfl oracles (-(actualOutcome target
    layout outcome))

/-- The actual projector reads the same physical target as H and its selected reset. -/
def projector (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (outcome : Fin 2) : HilbertOperator layout.toQuantum.register :=
  ZMeasurement.projector (R := layout.toQuantum.register)
    (fun basis : layout.toQuantum.register.Index => basis target.wire) (actualOutcome target
      layout outcome)

/-- Native record-conditioned operator of H, MZ and physical reset, before phase correction. -/
def nativeBranch (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (outcome : Fin 2) : HilbertOperator layout.toQuantum.register :=
  ((correction (oracles := oracles) target layout outcome).matrix environment :
      HilbertOperator layout.toQuantum.register) * projector target layout outcome *
    ((target.hadamard layout oracles).matrix environment :
      HilbertOperator layout.toQuantum.register)

private lemma correction_selected_ket (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (outcome : Fin 2) (state : Data)
    (selected : finTwoEquiv.symm (target.get state) = outcome) :
    (correction target layout outcome).applyVec environment
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      (NormalizedVector.ket (R := layout.toQuantum.register)
        (layout.basisEquiv.symm (encoding.encode (resetLabel target state)))).vec := by
  change ((correction target layout outcome).matrix environment).applyVec _ = _
  rw [correction, QuditShift.qubitShiftCircuit_matrix]
  have actual := congrArg NormalizedVector.vec
    (QuditShift.quditShift_operator_apply_ket layout.toQuantum target.wire (-(actualOutcome
      target layout outcome))
      (layout.basisEquiv.symm (encoding.encode state)))
  refine actual.trans ?_
  rw [physical_get, selected, add_neg_cancel, ← resetLabel_basis]

private lemma correction_projected_ket (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (outcome : Fin 2) (state : Data) :
    (correction target layout outcome).applyVec environment
        ((projector target layout outcome).applyVec
          (NormalizedVector.ket (R := layout.toQuantum.register)
            (layout.basisEquiv.symm (encoding.encode state))).vec) =
      if finTwoEquiv.symm (target.get state) = outcome then
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode (resetLabel target state)))).vec
      else 0 := by
  unfold projector
  have projected := ZMeasurement.projector_ket (R := layout.toQuantum.register)
    (fun basis : layout.toQuantum.register.Index => basis target.wire)
    (actualOutcome target layout outcome) (layout.basisEquiv.symm (encoding.encode state))
  split_ifs at projected with selectedActual
  · have selected : finTwoEquiv.symm (target.get state) = outcome := by
      apply Fin.ext
      exact (congrArg Fin.val (target.targetBasisEquiv_first state)).symm.trans
        (congrArg Fin.val selectedActual)
    rw [if_pos selected]
    exact (congrArg ((correction target layout outcome).applyVec environment) projected).trans
      (correction_selected_ket (environment := environment) target layout outcome state selected)
  · have selected : ¬finTwoEquiv.symm (target.get state) = outcome := by
      intro equal
      apply selectedActual
      apply Fin.ext
      exact (congrArg Fin.val (target.targetBasisEquiv_first state)).trans
        (congrArg Fin.val equal)
    rw [if_neg selected]
    refine (congrArg ((correction target layout outcome).applyVec environment) projected).trans ?_
    ext row
    simp [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec]

/-- Each actual outcome has precisely its input-bit character and the same positive amplitude. -/
lemma branch_encoded_ket (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (outcome : Fin 2) (state : Data) :
    (nativeBranch (environment := environment) target layout outcome).applyVec
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      (invSqrt2 * character outcome (target.get state)) •
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode (resetLabel target state)))).vec := by
  simp only [nativeBranch, HilbertOperator.mul_applyVec]
  change (correction target layout outcome).applyVec environment
    ((projector target layout outcome).applyVec
      ((target.hadamard layout oracles).applyVec environment _)) = _
  rw [EncodedBit.hadamard_applyVec_encoded_ket]
  simp only [HilbertOperator.applyVec_smul, HilbertOperator.applyVec_add,
    UnitaryCircuit.applyVec_smul, UnitaryCircuit.applyVec_add]
  rw [correction_projected_ket, correction_projected_ket, resetLabel_flip]
  cases value : target.get state <;> fin_cases outcome <;>
    simp [character, value, get_flip_self, finTwoEquiv]

/-- Reference extension of the same physical, unnormalized native branch. -/
def branchOperator (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (outcome : Fin 2) (Reference : Register) :
    HilbertOperator (Register.prod layout.toQuantum.register Reference) :=
  nativeBranch (environment := environment) target layout outcome ⊗ₖ
    (1 : HilbertOperator Reference)

/-- The character retains every dirty/control/reference label, before any outcome is summed. -/
lemma branch_reference_ket (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (outcome : Fin 2) (state : Data)
    {Reference : Register} (reference : Reference.Index) :
    (branchOperator (environment := environment) target layout outcome Reference).applyVec
        (NormalizedVector.ket (R := Register.prod layout.toQuantum.register Reference)
          (layout.basisEquiv.symm (encoding.encode state), reference)).vec =
      (invSqrt2 * character outcome (target.get state)) •
        (NormalizedVector.ket (R := Register.prod layout.toQuantum.register Reference)
          (layout.basisEquiv.symm (encoding.encode (resetLabel target state)), reference)).vec := by
  ext row
  rcases row with ⟨localIndex, referenceIndex⟩
  rw [HilbertOperator.applyVec_ket]
  have column := congrArg
    (fun vector : HilbertVector layout.toQuantum.register => vector localIndex)
    (branch_encoded_ket (environment := environment) target layout outcome state)
  rw [HilbertOperator.applyVec_ket] at column
  change nativeBranch (environment := environment) target layout outcome localIndex
      (layout.basisEquiv.symm (encoding.encode state)) *
      (if referenceIndex = reference then (1 : ℂ) else 0) = _
  rw [column]
  simp only [PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply]
  change ((invSqrt2 * character outcome (target.get state)) *
      (if localIndex = layout.basisEquiv.symm (encoding.encode (resetLabel target state))
        then 1 else 0)) * (if referenceIndex = reference then 1 else 0) =
    (invSqrt2 * character outcome (target.get state)) *
      (if (localIndex, referenceIndex) =
        (layout.basisEquiv.symm (encoding.encode (resetLabel target state)), reference)
        then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Linearity retains the exact character on arbitrary entangled superpositions. -/
lemma branch_coherent_reference (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (outcome : Fin 2)
    {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (branchOperator (environment := environment) target layout outcome Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod layout.toQuantum.register Reference)
            (layout.basisEquiv.symm (encoding.encode (state index)), reference index)).vec) =
      ∑ index, (amplitude index * (invSqrt2 * character outcome (target.get (state index)))) •
        (NormalizedVector.ket (R := Register.prod layout.toQuantum.register Reference)
          (layout.basisEquiv.symm (encoding.encode (resetLabel target (state index))),
            reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul, branch_reference_ket, smul_smul]

end

end QuantumAlg.EncodedBit.MeasuredUncompute
