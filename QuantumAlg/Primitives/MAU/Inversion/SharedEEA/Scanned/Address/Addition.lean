/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Copy
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.WordPair
import all QuantumAlg.Primitives.MAU.Addition.TTK.Parallel
import all QuantumAlg.Primitives.MAU.Addition.TTK.Correctness

/-!
# Actual full-carry addition for the scan address

A rescheduled TTK body uses the complete address as target. Its addend is
exactly the quotient-length word plus the existing high prefix position.
The position is part of the supplied physical addend and is preserved on
all labels; later clean-pool preparation discharges its zero-padding premise.
No source length is converted into a classical circuit factory.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressAddition

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The actual quotient bits are preceded by the retained existing high padding bit. -/
def source (width : Nat) : Word (encoding width) (ScanMetadata.addressWidth width) where
  bit index := if zero : index.val = 0 then AddressCopy.padding width
    else sourceBit width (quotientLengthBit width
      ⟨index.val - 1, by
        have within := index.isLt
        unfold ScanMetadata.addressWidth at within
        omega⟩)

private lemma source_target_ne (width : Nat)
    (left right : Fin (ScanMetadata.addressWidth width)) :
    ((source width).bit left).wire ≠ ((AddressCopy.target width).bit right).wire := by
  unfold source
  dsimp only
  split
  · exact (address_prefix_ne width right _).symm
  · exact source_address_ne width _ right

private lemma source_source_ne (width : Nat)
    (left right : Fin (ScanMetadata.addressWidth width)) (different : left ≠ right) :
    ((source width).bit left).wire ≠ ((source width).bit right).wire := by
  unfold source
  dsimp only
  split_ifs with first second
  · exact False.elim (different (Fin.ext (first.trans second.symm)))
  · exact (source_prefix_ne width _ _).symm
  · exact source_prefix_ne width _ _
  · intro same
    apply different
    apply Fin.ext
    have values := congrArg Fin.val same
    simp only [Scanned.sourceBit_wire, quotientLengthBit_wire] at values
    omega

/-- The subsystem injection uses exactly the named quotient/padding and address wires. -/
def placement (width : Nat) :
    WireSubsystem (Addition.TTK.encoding (ScanMetadata.addressWidth width)) (encoding width) :=
  wordPairSubsystem (source width) (AddressCopy.target width)
    (fun left right same => by
      by_contra different
      exact source_source_ne width left right different same)
    (fun left right same => by
      by_contra different
      exact address_address_ne width left right different same)
    (source_target_ne width)

private lemma source_total (width : Nat) :
    Function.Surjective (Addition.TTK.encoding (ScanMetadata.addressWidth width)).encode :=
  (prodEquiv (m := ScanMetadata.addressWidth width)
    (n := ScanMetadata.addressWidth width)).surjective

/-- Actual TTK addition at those original subsystem positions; no systems are allocated. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (placement width).program (source_total width) (encoding_surjective width)
    (Addition.TTK.parallelLowRippleProgram (ScanMetadata.addressWidth width))

/-- Complete coherent finite arithmetic, including the entire unchanged complement. -/
def step (width : Nat) (state : Data width) : Data width :=
  ((placement width).full (source_total width) (encoding_surjective width)).step
    (fun pair => (Addition.TTK.lowOutput pair.1, pair.2)) state

/-- The actual placed body implements its exact two-word addition on every finite label. -/
lemma program_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment (step width) := by
  apply (placement width).program_realizes (source_total width) (encoding_surjective width)
  apply (Addition.TTK.ttkParallelLowRipple_realizes_fold
    (ScanMetadata.addressWidth width) environment).congrStep
  exact Addition.TTK.ttkLowRipple_step (ScanMetadata.addressWidth width)

/-- Every native occurrence is charged exactly as in the actual full-carry TTK adder. -/
lemma program_eventTrace (width : Nat) :
    (program width).eventTrace =
      (Addition.TTK.parallelLowRippleProgram (ScanMetadata.addressWidth width)).eventTrace :=
  (placement width).program_eventTrace (source_total width) (encoding_surjective width) _

/-- Every physical dependency is retained under arbitrary native event durations. -/
lemma program_evaluatedEventDepth (width : Nat)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) :
    (program width).evaluatedEventDepth duration =
      (Addition.TTK.parallelLowRippleProgram (ScanMetadata.addressWidth width)).evaluatedEventDepth
        duration :=
  (placement width).program_evaluatedEventDepth (source_total width) (encoding_surjective width)
    _ duration

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressAddition
