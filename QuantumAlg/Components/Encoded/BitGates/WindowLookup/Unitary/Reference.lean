/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary
import all QuantumAlg.Core.Base.Tensor.Certified
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Exact table XOR beside an arbitrary entangled reference

The operator is the actual native table circuit tensored with the untouched
reference identity. Linearity retains the same amplitude, with no phase or
normalization adjustment, on the explicitly stated clean prefix subspace.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

open scoped Kronecker

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {addressWidth wordWidth : Nat}

/-- Extend only the actual lookup matrix by the identity on the existing external reference. -/
def enabledLookupReferenceOperator (frame : SelectorFrame encoding addressWidth)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (height : Nat)
    (environment : oracles.Interpretation) (Reference : Register) :
    HilbertOperator (Register.prod physical.toQuantum.register Reference) :=
  (enabledLookupProgram frame physical oracles target table active height).matrix environment ⊗ₖ
    (1 : HilbertOperator Reference)

/-- Every original target and reference label has the exact physical table XOR image. -/
lemma enabledLookup_reference_ket (frame : SelectorFrame encoding addressWidth)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (height : Nat) (covered : wordWidth ≤ 2 ^ height)
    (environment : oracles.Interpretation) (state : Data) (clean : frame.CleanFrom 0 state)
    {Reference : Register} (reference : Reference.Index) :
    (enabledLookupReferenceOperator frame physical oracles target table active height
      environment Reference).applyVec
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode state), reference)).vec =
      (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
        (physical.basisEquiv.symm
          (encoding.encode (enabledLookupStep frame target table active state)),
            reference)).vec := by
  have vector := congrArg NormalizedVector.vec
    (enabledLookupProgram_apply_encoded_ket frame physical oracles target table active
      height covered environment state clean)
  change HilbertOperator.applyVec
    ((enabledLookupProgram frame physical oracles target table active height).matrix environment :
      HilbertOperator physical.toQuantum.register) (NormalizedVector.ket
      (physical.basisEquiv.symm (encoding.encode state))).vec = _ at vector
  ext row
  rcases row with ⟨localIndex, referenceIndex⟩
  rw [HilbertOperator.applyVec_ket]
  have column := congrArg
    (fun value : HilbertVector physical.toQuantum.register => value localIndex) vector
  rw [HilbertOperator.applyVec_ket] at column
  change (enabledLookupProgram frame physical oracles target table active height).matrix
      environment localIndex (physical.basisEquiv.symm (encoding.encode state)) *
      (if referenceIndex = reference then (1 : ℂ) else 0) = _
  rw [column]
  let output := physical.basisEquiv.symm
    (encoding.encode (enabledLookupStep frame target table active state))
  simp only [NormalizedVector.ket_apply]
  change (if localIndex = output then (1 : ℂ) else 0) *
      (if referenceIndex = reference then 1 else 0) =
    if ((localIndex, referenceIndex) : physical.toQuantum.register.Index × Reference.Index) =
        (output, reference) then 1 else 0
  by_cases sameLocal : localIndex = output
  · by_cases sameReference : referenceIndex = reference
    · have joint : ((localIndex, referenceIndex) :
          physical.toQuantum.register.Index × Reference.Index) = (output, reference) :=
        Prod.ext sameLocal sameReference
      rw [if_pos sameLocal, if_pos sameReference, if_pos joint]
      exact one_mul 1
    · have joint : ((localIndex, referenceIndex) :
          physical.toQuantum.register.Index × Reference.Index) ≠ (output, reference) :=
        fun equal => sameReference (congrArg Prod.snd equal)
      rw [if_pos sameLocal, if_neg sameReference, if_neg joint]
      exact mul_zero 1
  · have joint : ((localIndex, referenceIndex) :
        physical.toQuantum.register.Index × Reference.Index) ≠ (output, reference) :=
      fun equal => sameLocal (congrArg Prod.fst equal)
    rw [if_neg sameLocal, if_neg joint, zero_mul]

/-- Arbitrary entanglement retains the same coefficient on every promised basis input. -/
lemma enabledLookup_coherent_reference (frame : SelectorFrame encoding addressWidth)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Fin (2 ^ addressWidth) → Fin (2 ^ wordWidth))
    (active : Fin (2 ^ addressWidth) → Bool) (height : Nat) (covered : wordWidth ≤ 2 ^ height)
    (environment : oracles.Interpretation) {Reference : Register} {Index : Type} [Fintype Index]
    (state : Index → Data) (clean : ∀ index, frame.CleanFrom 0 (state index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (enabledLookupReferenceOperator frame physical oracles target table active height
      environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm
            (encoding.encode (enabledLookupStep frame target table active (state index))),
              reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul,
    enabledLookup_reference_ket frame physical oracles target table active height covered
      environment (state index) (clean index)]

end

end QuantumAlg.EncodedBit.WindowLookup
