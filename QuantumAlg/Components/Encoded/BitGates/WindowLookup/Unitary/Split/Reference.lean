/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unitary.Split
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Actual full-address dirty-target XOR beside an arbitrary reference

The original top-address optimization retains the exact native lookup
matrix. Tensoring only that actual matrix with the reference identity keeps
every complex coefficient and the complete dirty-target XOR image.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

open scoped BigOperators

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width wordWidth : Nat}

/-- The actual full-address native lookup matrix, with the existing reference untouched. -/
def splitLookupReferenceOperator (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth)) (height : Nat)
    (environment : oracles.Interpretation) (Reference : Register) :
    HilbertOperator (Register.prod physical.toQuantum.register Reference) :=
  UnitaryOperator.prodTensor
    ((splitLookupProgram frame physical oracles target table height).matrix environment)
    (1 : UnitaryOperator Reference)

/-- The original dirty target and every external reference label retain exact table XOR. -/
lemma splitLookup_reference_ket (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth))
    (height : Nat) (covered : wordWidth ≤ 2 ^ height) (environment : oracles.Interpretation)
    (state : Data) (clean : frame.CleanFrom 0 state)
    {Reference : Register} (reference : Reference.Index) :
    (splitLookupReferenceOperator frame physical oracles target table height
      environment Reference).applyVec
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm (encoding.encode state), reference)).vec =
      (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
        (physical.basisEquiv.symm (encoding.encode (splitLookupStep frame target table state)),
          reference)).vec := by
  have actual := congrArg NormalizedVector.vec
    (splitLookupProgram_apply_encoded_ket frame physical oracles target table height covered
      environment state clean)
  change UnitaryOperator.applyVec
    ((splitLookupProgram frame physical oracles target table height).matrix environment)
    (NormalizedVector.ket (R := physical.toQuantum.register)
      (physical.basisEquiv.symm (encoding.encode state))).vec = _ at actual
  change (UnitaryOperator.prodTensor
    ((splitLookupProgram frame physical oracles target table height).matrix environment)
    (1 : UnitaryOperator Reference)).applyVec _ = _
  rw [← HilbertVector.prodTensor_ket, UnitaryOperator.prodTensor_applyVec_prodTensor,
    actual, UnitaryOperator.one_applyVec, HilbertVector.prodTensor_ket]

/-- Arbitrary coherent reference families retain their original amplitudes on every dirty target. -/
lemma splitLookup_coherent_reference (frame : SelectorFrame encoding width)
    (physical : QubitLayout encoding.width) (oracles : OracleModel)
    (target : LookupTarget frame wordWidth)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ wordWidth))
    (height : Nat) (covered : wordWidth ≤ 2 ^ height) (environment : oracles.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (clean : ∀ index, frame.CleanFrom 0 (state index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    (splitLookupReferenceOperator frame physical oracles target table height
      environment Reference).applyVec
        (∑ index, amplitude index •
          (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
            (physical.basisEquiv.symm (encoding.encode (state index)), reference index)).vec) =
      ∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod physical.toQuantum.register Reference)
          (physical.basisEquiv.symm
            (encoding.encode (splitLookupStep frame target table (state index))),
            reference index)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [HilbertOperator.applyVec_smul,
    splitLookup_reference_ket frame physical oracles target table height covered environment
      (state index) (clean index)]

end

end QuantumAlg.EncodedBit.WindowLookup
