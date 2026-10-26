/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Packing.Frequency
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Packing.Parent
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Contraction
import all QuantumAlg.Primitives.ShortDLP.BornProbability.Distribution
import all QuantumAlg.Util.FinPow.BitReverse

/-!
# Original terminal labels of the actual paid measured-member output

Both chronological streams are reversed separately and retain the original
complete source terminal convention. The finite bijection is mathematical;
the existing native packing instruction remains charged [GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution QuantumFourierTransform.Semiclassical

/-- Every original chronological pair corresponds to exactly one unchanged source terminal. -/
def measuredMemberTerminalEquiv (m ell width : Nat) : MemberReadouts m ell ≃
    Outcome (registerParameters m ell width) :=
  ((Equiv.prodCongr
      ((binaryEquiv (ell + m)).trans (qftReverseBitsPerm (ell + m)))
      ((binaryEquiv ell).trans (qftReverseBitsPerm ell))).trans prodEquiv).trans
    (Equiv.ofBijective
      (BornProbability.shortDLPMeasurementOutcome (registerParameters m ell width))
      (BornProbability.shortDLPMeasurementOutcome_bijective _))

/-- The original complete Fourier terminal is selected at exactly the two original frequencies. -/
lemma measuredMemberTerminalEquiv_apply (m ell width : Nat) (readout : MemberReadouts m ell) :
    measuredMemberTerminalEquiv m ell width readout =
      BornProbability.shortDLPMeasurementOutcome (registerParameters m ell width)
        (prodEquiv (measuredMemberFrequencies m ell readout)) := rfl

private lemma measuredTerminal_binary_coordinates (m ell width : Nat)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    (fun index => finTwoEquiv
      ((BinaryBasis.bigEndianEquiv ((ell + m) + ell)).symm (prodEquiv (first, second)) index)) =
      BornProbability.shortDLPMeasurementOutcome (registerParameters m ell width)
        (prodEquiv (first, second)) := by
  funext index
  have coordinate := congrArg finTwoEquiv
    (BinaryBasis.bigEndianEquiv_symm_value ((ell + m) + ell) (prodEquiv (first, second)) index)
  rw [Equiv.apply_symm_apply] at coordinate
  refine coordinate.trans ?_
  change (prodEquiv (first, second)).val.testBit index.rev.val =
    (prodEquiv (first, second)).val.testBit (((ell + m) + ell) - 1 - index.val)
  apply congrArg (fun position => (prodEquiv (first, second)).val.testBit position)
  calc
    index.rev.val = resultBits m ell - (index.val + 1) := Fin.val_rev index
    _ = ((ell + m) + ell) - 1 - index.val := by unfold resultBits; omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

/-- The paid instruction's actual input value packs to the unchanged complete source terminal. -/
lemma measuredPackedReadout_terminal
    (original : Store (context base noQuantum m ell width)) (readout : MemberReadouts m ell) :
    Packing.packedReadoutValue m ell (memberReadoutValue m ell readout) =
      CShape.Value.bits (measuredMemberTerminalEquiv m ell width readout) := by
  let frequency := measuredMemberFrequencies m ell readout
  have decoded : (frequencyBits (ell + m) frequency.1, frequencyBits ell frequency.2) = readout :=
    Prod.ext (Partner.qftPartner_frequencyBits_decode (ell + m) readout.1)
      (Partner.qftPartner_frequencyBits_decode ell readout.2)
  have input := Packing.measuredPacking_readout_input base noQuantum m ell width
    (memberReadoutStore base noQuantum m ell width original readout)
  rw [memberReadoutStore_resultRead] at input
  have canonical := Packing.measuredPacking_frequency_input base noQuantum m ell width original
    frequency.1 frequency.2
  rw [decoded] at canonical
  exact (congrArg (CShape.packFiniteBits (resultBits m ell)) (input.symm.trans canonical)).trans
    ((Packing.measured_pack_binary_coordinates (resultBits m ell)
      ((BinaryBasis.bigEndianEquiv ((ell + m) + ell)).symm (prodEquiv frequency))).trans
        (congrArg CShape.Value.bits
          (measuredTerminal_binary_coordinates m ell width frequency.1 frequency.2)))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
