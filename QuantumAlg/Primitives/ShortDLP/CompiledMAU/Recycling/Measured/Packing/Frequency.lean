/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Packing
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Store
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import Mathlib.Tactic.FinCases

/-!
# The actual paid packed value has the original complete Fourier frequency order

Both original measured streams are read from their true retained cells. The
native packing instruction writes the canonical concatenated frequency bits
to its actual existing destination [GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Packing

noncomputable section

open Execution QuantumFourierTransform.Semiclassical

private lemma measured_pack_binary_coordinates (count : Nat) (values : Fin count → Fin 2) :
    CShape.packFiniteBits count (.fixedVector (fun index => .finite (values index))) =
      CShape.Value.bits (fun index => finTwoEquiv (values index)) := by
  apply congrArg CShape.Value.bits
  funext index
  change decide ((values index).val = 1) = finTwoEquiv (values index)
  generalize values index = value
  fin_cases value <;> simp [finTwoEquiv]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev FrequencyPackingCtx := context base noQuantum m ell width

/-- The paid instruction reads both real chronological tuples reversed within their own words. -/
lemma measuredPacking_member_input
    (original : Store (FrequencyPackingCtx base noQuantum m ell width))
    (outcome : MemberReadouts m ell) :
    (memberReadoutStore base noQuantum m ell width original outcome).read
        (frequencyInput base noQuantum m ell width) =
      .fixedVector (fun index => .finite (Fin.addCases
        (fun position => tupleCoordinates (ell + m) outcome.1 position.rev)
        (fun position => tupleCoordinates ell outcome.2 position.rev) index)) := by
  apply congrArg CShape.Value.fixedVector
  funext index
  refine Fin.addCases (fun first => ?_) (fun second => ?_) index
  · have cell : Fin.addCases
        (fun position => .storage (firstCell base noQuantum m ell width position.rev).toCStorageRef)
        (fun position => .storage
          (secondCell base noQuantum m ell width position.rev).toCStorageRef)
        (Fin.castAdd ell first) =
          (CInputRef.storage (firstCell base noQuantum m ell width first.rev).toCStorageRef) :=
      Fin.addCases_left first
    have coordinate : Fin.addCases (motive := fun _ => Fin 2)
        (fun position => tupleCoordinates (ell + m) outcome.1 position.rev)
        (fun position => tupleCoordinates ell outcome.2 position.rev) (Fin.castAdd ell first) =
          tupleCoordinates (ell + m) outcome.1 first.rev := Fin.addCases_left first
    exact (congrArg
      (fun input => (memberReadoutStore base noQuantum m ell width original outcome).read input)
      cell).trans
        ((memberReadoutStore_first base noQuantum m ell width original outcome first.rev).trans
          (congrArg (fun bit : Fin 2 => (CShape.Value.finite bit : CShape.Value (.finite 2)))
            coordinate.symm))
  · have cell : Fin.addCases
        (fun position => .storage (firstCell base noQuantum m ell width position.rev).toCStorageRef)
        (fun position => .storage
          (secondCell base noQuantum m ell width position.rev).toCStorageRef)
        (Fin.natAdd (ell + m) second) =
          (CInputRef.storage (secondCell base noQuantum m ell width second.rev).toCStorageRef) :=
      Fin.addCases_right second
    have coordinate : Fin.addCases (motive := fun _ => Fin 2)
        (fun position => tupleCoordinates (ell + m) outcome.1 position.rev)
        (fun position => tupleCoordinates ell outcome.2 position.rev)
        (Fin.natAdd (ell + m) second) = tupleCoordinates ell outcome.2 second.rev :=
      Fin.addCases_right second
    exact (congrArg
      (fun input => (memberReadoutStore base noQuantum m ell width original outcome).read input)
      cell).trans
        ((memberReadoutStore_second base noQuantum m ell width original outcome second.rev).trans
          (congrArg (fun bit : Fin 2 => (CShape.Value.finite bit : CShape.Value (.finite 2)))
            coordinate.symm))

/-- The actual input is the canonical complete Fourier frequency vector, including its reversal. -/
lemma measuredPacking_frequency_input
    (original : Store (FrequencyPackingCtx base noQuantum m ell width))
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    (memberReadoutStore base noQuantum m ell width original
      (frequencyBits (ell + m) first, frequencyBits ell second)).read
        (frequencyInput base noQuantum m ell width) =
      CShape.Value.fixedVector (fun index =>
        (CShape.Value.finite ((BinaryBasis.bigEndianEquiv ((ell + m) + ell)).symm
          (prodEquiv (first, second)) index) : CShape.Value (.finite 2))) := by
  refine (measuredPacking_member_input base noQuantum m ell width original
    (frequencyBits (ell + m) first, frequencyBits ell second)).trans ?_
  simp_rw [Partner.qftPartner_frequency_reversed_coordinate]
  rw [BinaryBasis.bigEndianEquiv_symm_prod]
  rfl

/-- The real charged packing instruction writes exactly the canonical source frequency bits. -/
lemma measuredPacking_frequency_output
    (result : CWriteRef (FrequencyPackingCtx base noQuantum m ell width) (.bits (resultBits m ell)))
    (original : Store (FrequencyPackingCtx base noQuantum m ell width))
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    ((memberReadoutStore base noQuantum m ell width original
      (frequencyBits (ell + m) first, frequencyBits ell second)).applyOp
        (operation base noQuantum m ell width result)).read (.storage result.toCStorageRef) =
      CShape.Value.bits (fun index => finTwoEquiv
        ((BinaryBasis.bigEndianEquiv ((ell + m) + ell)).symm
          (prodEquiv (first, second)) index)) := by
  exact (measuredPacking_output base noQuantum m ell width result _).trans
    ((congrArg (CShape.packFiniteBits (resultBits m ell))
      (measuredPacking_frequency_input base noQuantum m ell width original first second)).trans
        (measured_pack_binary_coordinates (resultBits m ell)
          ((BinaryBasis.bigEndianEquiv ((ell + m) + ell)).symm (prodEquiv (first, second)))))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Packing
