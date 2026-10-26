/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.SeedProjection
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Born
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Comparison
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement.Zero
import all QuantumAlg.Components.Encoded.StateEmbedding.Reference
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Reference.Preservation

/-!
# Complete reference contraction of the same original measured member source

The faithful physical injection changes no reference entry. The unit-one
source column gives its exact Born weight times the original complete
Store/reference coefficient. This contracts only the local quantum output;
actual Store observers remain separate [GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution QuantumFourierTransform.Semiclassical
open scoped BigOperators Kronecker

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MemberContractCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]
  (generator target : (ZMod modulus.toNat)ˣ)

/-- Canonical source frequencies of the actual original chronological readout tuples. -/
def measuredMemberFrequencies (readout : MemberReadouts m ell) :
    Fin (2 ^ (ell + m)) × Fin (2 ^ ell) :=
  (qftReverseBits (ell + m) (binaryEquiv (ell + m) readout.1),
    qftReverseBits ell (binaryEquiv ell readout.2))

/-- Faithful injection and local contraction retain the complete incoming reference coefficient. -/
lemma memberFourier_seed_reference_sum {Reference : Register}
    (reference : DensityOperator Reference)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (leftRef rightRef : Reference.Index) :
    let embedding := BasisEmbedding.matrix
      (zeroJointEmbedding base noQuantum m ell width modulus Reference)
    let source := sourceWithReference
      (memberFourierKraus m ell width modulus generator target first second) Reference
    (∑ basis : (MemberContractCtx base noQuantum m ell width).register.Index,
      (embedding * (source *
        (BasisReference.target (R := Recycling.Carrier.units modulus.toNat) 1 reference).matrix *
          source.conjTranspose) *
        embedding.conjTranspose) (basis, leftRef) (basis, rightRef)) =
      (memberFourierWeight m ell width modulus generator target first second : ℂ) *
        reference.matrix leftRef rightRef := by
  dsimp only
  rw [zeroJointEmbedding, BasisEmbedding.reference_sandwich_sum]
  let operator := memberFourierKraus m ell width modulus generator target first second
  have entries (row : (Recycling.Carrier.units modulus.toNat).Index) :
      (sourceWithReference operator Reference *
        (BasisReference.target (R := Recycling.Carrier.units modulus.toNat) 1 reference).matrix *
          (sourceWithReference operator Reference).conjTranspose) (row, leftRef) (row, rightRef) =
        operator row 1 * reference.matrix leftRef rightRef * star (operator row 1) :=
    comparison_tensor_seed (Source := Recycling.Carrier.units modulus.toNat)
      (Target := Recycling.Carrier.units modulus.toNat) operator 1 reference row row leftRef
        rightRef
  calc
    _ = ∑ row : (Recycling.Carrier.units modulus.toNat).Index,
        operator row 1 * reference.matrix leftRef rightRef * star (operator row 1) :=
      Finset.sum_congr rfl (fun row _ => entries row)
    _ = _ := by
      simp only [memberFourierWeight, Complex.ofReal_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      let amplitude := operator row 1
      have coefficient : amplitude * star amplitude = ((‖amplitude‖ ^ 2 : ℝ) : ℂ) := by
        simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' amplitude
      change amplitude * _ * star amplitude = _
      rw [← coefficient]
      ring

private lemma memberComparison_reference_entry {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (MemberContractCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (entry : Store (MemberContractCtx base noQuantum m ell width) × (model.HiddenState × Unit))
    (leftRef rightRef : Reference.Index) :
    (comparisonReferenceDensity
      ((state.mapHistory (fun record => (record.1, ()))).block entry)).matrix leftRef rightRef =
      (state.filterClassical (fun original => original.1 = entry.1)).referenceMarginal.matrix
        leftRef rightRef := by
  rw [comparisonReferenceDensity, DensityOperator.marginalLeft_matrix,
    ExecutionState.referenceMarginal, DensityOperator.marginalLeft_matrix]
  simp only [DensityOperator.reindex_entry, comparison_compressed_block]

/-- The same canonical chronological source has its exact complete Store/reference Born factor. -/
lemma member_canonical_seed_reference_sum {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (MemberContractCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (entry : Store (MemberContractCtx base noQuantum m ell width) × (model.HiddenState × Unit))
    (readout : MemberReadouts m ell) (leftRef rightRef : Reference.Index) :
    let embedding := BasisEmbedding.matrix
      (zeroJointEmbedding base noQuantum m ell width modulus Reference)
    let source := canonicalMemberSource m ell width modulus generator target Reference readout
    let comparison := unitSeedComparison base noQuantum m ell width modulus state
    let frequency := measuredMemberFrequencies m ell readout
    (∑ basis : (MemberContractCtx base noQuantum m ell width).register.Index,
      (embedding * (source * (comparison.block entry).matrix * source.conjTranspose) *
        embedding.conjTranspose) (basis, leftRef) (basis, rightRef)) =
      (memberFourierWeight m ell width modulus generator target frequency.1 frequency.2 : ℂ) *
        (state.filterClassical (fun original => original.1 = entry.1)).referenceMarginal.matrix
          leftRef rightRef := by
  let frequency := measuredMemberFrequencies m ell readout
  have decoded : (frequencyBits (ell + m) frequency.1, frequencyBits ell frequency.2) = readout :=
    Prod.ext (Partner.qftPartner_frequencyBits_decode (ell + m) readout.1)
      (Partner.qftPartner_frequencyBits_decode ell readout.2)
  have source := canonicalMemberSource_fullFourier m ell width modulus generator target Reference
    frequency.1 frequency.2
  rw [decoded] at source
  dsimp only
  rw [source]
  exact (memberFourier_seed_reference_sum base noQuantum m ell width modulus generator target
    (comparisonReferenceDensity ((state.mapHistory (fun record => (record.1, ()))).block entry))
    frequency.1 frequency.2 leftRef rightRef).trans
      (congrArg (fun coefficient : ℂ =>
        (memberFourierWeight m ell width modulus generator target frequency.1 frequency.2 : ℂ) *
          coefficient)
        (memberComparison_reference_entry base noQuantum m ell width state entry leftRef rightRef))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
