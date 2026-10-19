/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Stored.Trajectory
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Readout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packing
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Packed
import all QuantumAlg.Primitives.ShortDLP.BornProbability.Distribution
import all QuantumAlg.Primitives.ShortDLP.Measurement
import all QuantumAlg.Util.FinPow.BinaryBasis.Append
import all QuantumAlg.Core.Algorithm.ClassicalOp
import Mathlib.Tactic.FinCases

/-!
# The actual paid packed value of both short-DLP implementations

The reused-control member writes its chronological outcomes to real binary
cells. Its existing charged packing instruction reverses each stream into
the source frequency order. The old full-bank member's existing measured
packing writes the same Boolean value. The comparison concerns the values
of these real destination cells, without identifying their different stores
or their different quantum registers.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.PackedFrequency

noncomputable section

open Execution QuantumFourierTransform.Semiclassical

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- Canonical source coordinates, with the first frequency word before the second. -/
def canonicalReadout (m ell : Nat) (first : Fin (2 ^ (ell + m)))
    (second : Fin (2 ^ ell)) : Fin (resultBits m ell) → Bool :=
  fun index => finTwoEquiv
    ((BinaryBasis.bigEndianEquiv ((ell + m) + ell)).symm (prodEquiv (first, second)) index)

/-- Nominal finite-bit packing retains the corresponding Boolean coordinates exactly. -/
private lemma pack_binary_coordinates (count : Nat) (values : Fin count → Fin 2) :
    CShape.packFiniteBits count (.fixedVector (fun index => .finite (values index))) =
      CShape.Value.bits (fun index => finTwoEquiv (values index)) := by
  apply congrArg CShape.Value.bits
  funext index
  change decide ((values index).val = 1) = finTwoEquiv (values index)
  generalize values index = value
  fin_cases value <;> simp [finTwoEquiv]

/-- The packed coordinates are exactly the original source's terminal Boolean outcome. -/
lemma canonicalReadout_eq_source (m ell width : Nat)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    canonicalReadout m ell first second =
      BornProbability.shortDLPMeasurementOutcome (registerParameters m ell width)
        (prodEquiv (first, second)) := by
  funext index
  have coordinate := congrArg finTwoEquiv
    (BinaryBasis.bigEndianEquiv_symm_value ((ell + m) + ell)
      (prodEquiv (first, second)) index)
  rw [Equiv.apply_symm_apply] at coordinate
  refine coordinate.trans ?_
  change (prodEquiv (first, second)).val.testBit index.rev.val =
    (prodEquiv (first, second)).val.testBit (((ell + m) + ell) - 1 - index.val)
  apply congrArg (fun position => (prodEquiv (first, second)).val.testBit position)
  calc
    index.rev.val = resultBits m ell - (index.val + 1) := Fin.val_rev index
    _ = ((ell + m) + ell) - 1 - index.val := by
      unfold resultBits
      omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

/-- Real chronological writes supply the canonical two-word vector to the paid instruction. -/
lemma memberStore_frequencyInput_canonical
    (original : Store (context base noQuantum m ell width))
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    (MemberInstrument.memberStore base noQuantum m ell width original
      (frequencyBits (ell + m) first, frequencyBits ell second)).read
        (frequencyInput base noQuantum m ell width) =
      CShape.Value.fixedVector (fun index =>
        (CShape.Value.finite ((BinaryBasis.bigEndianEquiv ((ell + m) + ell)).symm
          (prodEquiv (first, second)) index) : CShape.Value (.finite 2))) := by
  rw [StoredTrajectory.memberStore_frequencyInput]
  simp_rw [Partner.qftPartner_frequency_reversed_coordinate]
  rw [BinaryBasis.bigEndianEquiv_symm_prod]
  rfl

/-- The actual reused-control packing operation writes the canonical source value. -/
lemma member_packed_output
    (result : CWriteRef (context base noQuantum m ell width) (.bits (resultBits m ell)))
    (original : Store (context base noQuantum m ell width))
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    ((MemberInstrument.memberStore base noQuantum m ell width original
      (frequencyBits (ell + m) first, frequencyBits ell second)).applyOp
      (Packing.operation base noQuantum m ell width result)).read
        (.storage result.toCStorageRef) =
      CShape.Value.bits (canonicalReadout m ell first second) := by
  rw [Packing.recyclingPacking_output, memberStore_frequencyInput_canonical]
  exact pack_binary_coordinates (resultBits m ell)
    ((BinaryBasis.bigEndianEquiv ((ell + m) + ell)).symm (prodEquiv (first, second)))

variable {old : RuntimeCtx .quantum}
  (sameWires : old.quantumWires = (runtimeLayout m ell width).wires)
  (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef old (.finite 2))
  (oldResult : CWriteRef old (.bits (RuntimeRound.resultBits m ell width)))

/-- The old full-bank's real measured and paid packed store has the same canonical value. -/
lemma old_packed_output (distinct : Function.Injective (fun index => (cells index).key))
    (original : Store old)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    (FullWordReadout.frequencyStore m ell width sameWires cells oldResult
      original first second).read (.storage oldResult.toCStorageRef) =
      CShape.Value.bits (canonicalReadout m ell first second) := by
  unfold FullWordReadout.frequencyStore
  rw [RuntimeRound.shortDLP_runtimePacked_output m ell width sameWires cells
    oldResult distinct, Equiv.apply_symm_apply, FullWordReadout.source_readout_frequency]
  change CShape.Value.bits
    (BornProbability.shortDLPMeasurementOutcome (registerParameters m ell width)
      (prodEquiv (((tripleEquiv (registerParameters m ell width)).symm
        ((tripleEquiv (registerParameters m ell width)) ((first, second), 0))).1))) = _
  rw [Equiv.symm_apply_apply, canonicalReadout_eq_source m ell width]
  rfl

/-- Only real packed destination values are identified across the two physical implementations. -/
lemma new_old_packed_output
    (distinct : Function.Injective (fun index => (cells index).key))
    (result : CWriteRef (context base noQuantum m ell width) (.bits (resultBits m ell)))
    (newOriginal : Store (context base noQuantum m ell width)) (oldOriginal : Store old)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    ((MemberInstrument.memberStore base noQuantum m ell width newOriginal
      (frequencyBits (ell + m) first, frequencyBits ell second)).applyOp
      (Packing.operation base noQuantum m ell width result)).read
        (.storage result.toCStorageRef) =
      (FullWordReadout.frequencyStore m ell width sameWires cells oldResult
        oldOriginal first second).read (.storage oldResult.toCStorageRef) :=
  (member_packed_output base noQuantum m ell width result newOriginal first second).trans
    (old_packed_output m ell width sameWires cells oldResult distinct
      oldOriginal first second).symm

/-- Source decoding of the actual common packed value recovers precisely the sampled pair. -/
lemma decode_canonical (m ell width : Nat)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    ShortDLP.decodeOutcome (registerParameters m ell width)
        (canonicalReadout m ell first second) = (first, second) := by
  rw [canonicalReadout_eq_source m ell width, ShortDLP.decodeOutcome,
    BornProbability.fullRegisterIndex_shortDLPMeasurementOutcome, Equiv.symm_apply_apply]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.PackedFrequency
