/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.Comparator
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule.ZeroTestValue
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Util.Nat.FixedWidth
import all QuantumAlg.Util.NumberTheory.Binary.GCD.FixedRound
import all QuantumAlg.Primitives.MAU.Inversion.MK.Layout
import all QuantumAlg.Primitives.MAU.Inversion.MK.DataPath.Counter

/-!
# Swap data path

This focused leaf is part of the exact fixed-round binary-GCD inversion
realization.  It is exported only through the canonical `MAU.Inversion.MK`
aggregate.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-! ## Swap data-path atoms -/

/-- Three-Toffoli bit swap between `u` and `v`, controlled by the comparison
ancilla.  This is the first local data-path atom needed by the swap-based
Montgomery--Kaliski round formulation [HJN+20, modular-arithmetic.tex:176-195]. -/
def compareControlledUVSwapBitGates
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  EncodedBit.controlledSwapGates
    (liftedCompareBit n counterWidth)
    (liftedUBit n counterWidth uIndex)
    (liftedVBit n counterWidth vIndex)
    (liftedCompare_liftedUBit_wire_ne n counterWidth uIndex)
    (liftedCompare_liftedVBit_wire_ne n counterWidth vIndex)
    (liftedUBit_liftedVBit_wire_ne n counterWidth uIndex vIndex)

/-- Base-gate program for one comparison-controlled `u`/`v` bit swap. -/
def compareControlledUVSwapBitProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.controlledSwapProgram (QubitLayout.canonical _) .empty
    (liftedCompareBit n counterWidth)
    (liftedUBit n counterWidth uIndex)
    (liftedVBit n counterWidth vIndex)
    (liftedCompare_liftedUBit_wire_ne n counterWidth uIndex)
    (liftedCompare_liftedVBit_wire_ne n counterWidth vIndex)
    (liftedUBit_liftedVBit_wire_ne n counterWidth uIndex vIndex)

/-- Folded semantic action of one comparison-controlled `u`/`v` bit swap. -/
def compareControlledUVSwapBitStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  EncodedBit.controlledSwapStep
    (liftedCompareBit n counterWidth)
    (liftedUBit n counterWidth uIndex)
    (liftedVBit n counterWidth vIndex)
    (liftedCompare_liftedUBit_wire_ne n counterWidth uIndex)
    (liftedCompare_liftedVBit_wire_ne n counterWidth vIndex)
    (liftedUBit_liftedVBit_wire_ne n counterWidth uIndex vIndex)

/-- The comparison-controlled `u`/`v` bit-swap program realizes its folded
base-gate semantics. -/
lemma compareControlledUVSwapBit_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (compareControlledUVSwapBitProgram n counterWidth uIndex vIndex) environment
      (compareControlledUVSwapBitStep n counterWidth uIndex vIndex) :=
  EncodedBit.controlledSwap_realizes (environment := environment)
    (QubitLayout.canonical _) .empty
    (liftedCompareBit n counterWidth)
    (liftedUBit n counterWidth uIndex)
    (liftedVBit n counterWidth vIndex)
    (liftedCompare_liftedUBit_wire_ne n counterWidth uIndex)
    (liftedCompare_liftedVBit_wire_ne n counterWidth vIndex)
    (liftedUBit_liftedVBit_wire_ne n counterWidth uIndex vIndex)

/-- The comparison-controlled `u`/`v` bit swap preserves the comparison
ancilla. -/
lemma compareControlledUVSwapBitStep_get_compare
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (compareControlledUVSwapBitStep n counterWidth uIndex vIndex x) =
      (liftedCompareBit n counterWidth).get x := by
  simpa [compareControlledUVSwapBitStep, compareControlledUVSwapBitGates]
    using EncodedBit.controlledSwapStep_get_control
      (liftedCompareBit n counterWidth)
      (liftedUBit n counterWidth uIndex)
      (liftedVBit n counterWidth vIndex)
      (liftedCompare_liftedUBit_wire_ne n counterWidth uIndex)
      (liftedCompare_liftedVBit_wire_ne n counterWidth vIndex)
      (liftedUBit_liftedVBit_wire_ne n counterWidth uIndex vIndex) x

/-- The comparison-controlled `u`/`v` bit swap sends the original selected
`v` bit to `u` when compare is set, and otherwise preserves `u`. -/
lemma compareControlledUVSwapBitStep_get_uBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedUBit n counterWidth uIndex).get
        (compareControlledUVSwapBitStep n counterWidth uIndex vIndex x) =
      if (liftedCompareBit n counterWidth).get x then
        (liftedVBit n counterWidth vIndex).get x
      else
        (liftedUBit n counterWidth uIndex).get x := by
  simpa [compareControlledUVSwapBitStep, compareControlledUVSwapBitGates]
    using EncodedBit.controlledSwapStep_get_left
      (liftedCompareBit n counterWidth)
      (liftedUBit n counterWidth uIndex)
      (liftedVBit n counterWidth vIndex)
      (liftedCompare_liftedUBit_wire_ne n counterWidth uIndex)
      (liftedCompare_liftedVBit_wire_ne n counterWidth vIndex)
      (liftedUBit_liftedVBit_wire_ne n counterWidth uIndex vIndex) x

/-- The comparison-controlled `u`/`v` bit swap sends the original selected
`u` bit to `v` when compare is set, and otherwise preserves `v`. -/
lemma compareControlledUVSwapBitStep_get_vBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedVBit n counterWidth vIndex).get
        (compareControlledUVSwapBitStep n counterWidth uIndex vIndex x) =
      if (liftedCompareBit n counterWidth).get x then
        (liftedUBit n counterWidth uIndex).get x
      else
        (liftedVBit n counterWidth vIndex).get x := by
  simpa [compareControlledUVSwapBitStep, compareControlledUVSwapBitGates]
    using EncodedBit.controlledSwapStep_get_right
      (liftedCompareBit n counterWidth)
      (liftedUBit n counterWidth uIndex)
      (liftedVBit n counterWidth vIndex)
      (liftedCompare_liftedUBit_wire_ne n counterWidth uIndex)
      (liftedCompare_liftedVBit_wire_ne n counterWidth vIndex)
      (liftedUBit_liftedVBit_wire_ne n counterWidth uIndex vIndex) x

/-- A comparison-controlled `u`/`v` bit swap preserves any readout whose wire is
distinct from the selected `u` and `v` wires. -/
lemma compareControlledUVSwapBitStep_get_observed_of_swap_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (observed :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (huObserved : (liftedUBit n counterWidth uIndex).wire ≠ observed.wire)
    (hvObserved : (liftedVBit n counterWidth vIndex).wire ≠ observed.wire)
    (x : RegistersWithComparisonWork n counterWidth) :
    observed.get
        (compareControlledUVSwapBitStep n counterWidth uIndex vIndex x) =
      observed.get x := by
  simpa [compareControlledUVSwapBitStep, compareControlledUVSwapBitGates]
    using EncodedBit.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedUBit n counterWidth uIndex)
      (liftedVBit n counterWidth vIndex)
      observed
      (liftedCompare_liftedUBit_wire_ne n counterWidth uIndex)
      (liftedCompare_liftedVBit_wire_ne n counterWidth vIndex)
      (liftedUBit_liftedVBit_wire_ne n counterWidth uIndex vIndex)
      huObserved hvObserved x

/-- A comparison-controlled `u`/`v` bit swap preserves every comparison-work
carry bit. -/
lemma compareControlledUVSwapBitStep_get_comparisonCarry
    (n counterWidth : Nat) (uIndex vIndex workBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (compareControlledUVSwapBitStep n counterWidth uIndex vIndex x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  apply compareControlledUVSwapBitStep_get_observed_of_swap_ne
  · exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.uBit n counterWidth uIndex)
      (comparisonCarryValueBit n workBit)
  · exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.vBit n counterWidth vIndex)
      (comparisonCarryValueBit n workBit)

/-- Full little-endian word swap between `u` and `v`, controlled by the
comparison ancilla.  This is the word-level data-path atom for the swap-based
Montgomery--Kaliski round formulation [HJN+20,
modular-arithmetic.tex:176-195]. -/
def compareControlledUVSwapGates
    (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  EncodedBit.Word.controlledSwapGates
    (liftedCompareBit n counterWidth)
    (liftedUWord n counterWidth)
    (liftedVWord n counterWidth)
    (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
    (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
    (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)

/-- Base-gate program for the comparison-controlled `u`/`v` word swap. -/
def compareControlledUVSwapProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledSwapProgram (QubitLayout.canonical _) .empty
    (liftedCompareBit n counterWidth)
    (liftedUWord n counterWidth)
    (liftedVWord n counterWidth)
    (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
    (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
    (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)

/-- Folded semantic action of the comparison-controlled `u`/`v` word swap. -/
def compareControlledUVSwapStep
    (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  EncodedBit.Word.controlledSwapStep
    (liftedCompareBit n counterWidth)
    (liftedUWord n counterWidth)
    (liftedVWord n counterWidth)
    (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
    (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
    (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)

/-- The comparison-controlled `u`/`v` word-swap program realizes its folded
base-gate semantics. -/
lemma compareControlledUVSwap_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (compareControlledUVSwapProgram n counterWidth) environment
      (compareControlledUVSwapStep n counterWidth) :=
  EncodedBit.Word.controlledSwap_realizes (environment := environment)
    (QubitLayout.canonical _) .empty
    (liftedCompareBit n counterWidth)
    (liftedUWord n counterWidth)
    (liftedVWord n counterWidth)
    (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
    (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
    (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)

/-- The comparison-controlled `u`/`v` word swap preserves the comparison
ancilla. -/
lemma compareControlledUVSwapStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (compareControlledUVSwapStep n counterWidth x) =
      (liftedCompareBit n counterWidth).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      (liftedCompareBit n counterWidth)
      (fun i => Ne.symm
        (liftedCompare_liftedUWordBit_wire_ne n counterWidth i))
      (fun i => Ne.symm
        (liftedCompare_liftedVWordBit_wire_ne n counterWidth i))
      x

/-- The comparison-controlled `u`/`v` word swap preserves the active flag. -/
lemma compareControlledUVSwapStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (compareControlledUVSwapStep n counterWidth x) =
      (liftedActiveBit n counterWidth).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      (liftedActiveBit n counterWidth)
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i)
          (RegisterBits.activeBit n counterWidth)
          (by
            simpa [RegisterBits.uValueBit] using
              Ne.symm (RegisterBits.active_u_wire_ne n counterWidth
                (WireAddress.littleEndianWire i))))
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i)
          (RegisterBits.activeBit n counterWidth)
          (by
            simpa [RegisterBits.vValueBit] using
              Ne.symm (RegisterBits.active_v_wire_ne n counterWidth
                (WireAddress.littleEndianWire i))))
      x

/-- The comparison-controlled `u`/`v` word swap preserves every stored
branch-history bit. -/
lemma compareControlledUVSwapStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (compareControlledUVSwapStep n counterWidth x) =
      (liftedHistoryBit n counterWidth historyIndex).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      (liftedHistoryBit n counterWidth historyIndex)
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (by
            simpa [RegisterBits.uValueBit] using
              RegisterBits.u_history_wire_ne n counterWidth
                (WireAddress.littleEndianWire i) historyIndex))
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (by
            simpa [RegisterBits.vValueBit] using
              RegisterBits.v_history_wire_ne n counterWidth
                (WireAddress.littleEndianWire i) historyIndex))
      x

/-- The comparison-controlled `u`/`v` word swap preserves the first scratch
bit. -/
lemma compareControlledUVSwapStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (compareControlledUVSwapStep n counterWidth x) =
      (liftedScratchABit n counterWidth).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      (liftedScratchABit n counterWidth)
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i)
          (RegisterBits.scratchABit n counterWidth)
          (by
            simpa [RegisterBits.uValueBit] using
              RegisterBits.u_scratchA_wire_ne n counterWidth
                (WireAddress.littleEndianWire i)))
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i)
          (RegisterBits.scratchABit n counterWidth)
          (by
            simpa [RegisterBits.vValueBit] using
              RegisterBits.v_scratchA_wire_ne n counterWidth
                (WireAddress.littleEndianWire i)))
      x

/-- The comparison-controlled `u`/`v` word swap preserves the second scratch
bit. -/
lemma compareControlledUVSwapStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchBBit n counterWidth).get
        (compareControlledUVSwapStep n counterWidth x) =
      (liftedScratchBBit n counterWidth).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      (liftedScratchBBit n counterWidth)
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth i)
          (RegisterBits.scratchBBit n counterWidth)
          (by
            simpa [RegisterBits.uValueBit] using
              RegisterBits.u_scratchB_wire_ne n counterWidth
                (WireAddress.littleEndianWire i)))
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth i)
          (RegisterBits.scratchBBit n counterWidth)
          (by
            simpa [RegisterBits.vValueBit] using
              RegisterBits.v_scratchB_wire_ne n counterWidth
                (WireAddress.littleEndianWire i)))
      x

/-- The comparison-controlled `u`/`v` word swap preserves every
comparison-work carry bit. -/
lemma compareControlledUVSwapStep_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (compareControlledUVSwapStep n counterWidth x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      (liftedComparisonCarryBit n counterWidth workBit)
      (fun i => liftedUWordBit_liftedComparisonCarry_wire_ne
        n counterWidth i workBit)
      (fun i => liftedVWordBit_liftedComparisonCarry_wire_ne
        n counterWidth i workBit)
      x

/-- The comparison-controlled `u`/`v` word swap sends the selected `v` value bit
to `u` when compare is set, and otherwise preserves the selected `u` value bit. -/
lemma compareControlledUVSwapStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedUWord n counterWidth).bit bit).get
        (compareControlledUVSwapStep n counterWidth x) =
      if (liftedCompareBit n counterWidth).get x then
        ((liftedVWord n counterWidth).bit bit).get x
      else
        ((liftedUWord n counterWidth).bit bit).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_left
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      bit
      (fun j hj => liftedUWordBit_liftedUWordBit_wire_ne
        n counterWidth j bit hj)
      (fun j => Ne.symm
        (liftedUWordBit_liftedVWordBit_wire_ne n counterWidth bit j))
      (fun j => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth j bit)
      (fun j hj => liftedVWordBit_liftedVWordBit_wire_ne
        n counterWidth j bit hj)
      x

/-- The comparison-controlled `u`/`v` word swap sends the selected `u` value bit
to `v` when compare is set, and otherwise preserves the selected `v` value bit. -/
lemma compareControlledUVSwapStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit bit).get
        (compareControlledUVSwapStep n counterWidth x) =
      if (liftedCompareBit n counterWidth).get x then
        ((liftedUWord n counterWidth).bit bit).get x
      else
        ((liftedVWord n counterWidth).bit bit).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_right
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      bit
      (fun j hj => liftedUWordBit_liftedUWordBit_wire_ne
        n counterWidth j bit hj)
      (fun j => Ne.symm
        (liftedUWordBit_liftedVWordBit_wire_ne n counterWidth bit j))
      (fun j => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth j bit)
      (fun j hj => liftedVWordBit_liftedVWordBit_wire_ne
        n counterWidth j bit hj)
      x

/-- The comparison-controlled `u`/`v` word swap preserves every `r`
coefficient bit. -/
lemma compareControlledUVSwapStep_get_rCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedRCoeffWord n counterWidth).bit bit).get
        (compareControlledUVSwapStep n counterWidth x) =
      ((liftedRCoeffWord n counterWidth).bit bit).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      ((liftedRCoeffWord n counterWidth).bit bit)
      (fun i => liftedUWordBit_liftedRCoeffWordBit_wire_ne
        n counterWidth i bit)
      (fun i => liftedVWordBit_liftedRCoeffWordBit_wire_ne
        n counterWidth i bit)
      x

/-- The comparison-controlled `u`/`v` word swap preserves every `s`
coefficient bit. -/
lemma compareControlledUVSwapStep_get_sCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedSCoeffWord n counterWidth).bit bit).get
        (compareControlledUVSwapStep n counterWidth x) =
      ((liftedSCoeffWord n counterWidth).bit bit).get x := by
  simpa [compareControlledUVSwapStep, compareControlledUVSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedUWord n counterWidth)
      (liftedVWord n counterWidth)
      (liftedCompare_liftedUWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth)
      (fun i => liftedUWordBit_liftedVWordBit_wire_ne n counterWidth i i)
      ((liftedSCoeffWord n counterWidth).bit bit)
      (fun i => liftedUWordBit_liftedSCoeffWordBit_wire_ne
        n counterWidth i bit)
      (fun i => liftedVWordBit_liftedSCoeffWordBit_wire_ne
        n counterWidth i bit)
      x

/-- Full coefficient-word swap between `r` and `s`, controlled by the
comparison ancilla.  Together with the `u`/`v` word swap, this is the paired
data-path atom in the swap-based Montgomery--Kaliski round formulation
[HJN+20, modular-arithmetic.tex:176-195]. -/
def compareControlledRSSwapGates
    (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  EncodedBit.Word.controlledSwapGates
    (liftedCompareBit n counterWidth)
    (liftedRCoeffWord n counterWidth)
    (liftedSCoeffWord n counterWidth)
    (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
    (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
    (fun i => Ne.symm
      (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth i i))

/-- Base-gate program for the comparison-controlled `r`/`s` coefficient-word
swap. -/
def compareControlledRSSwapProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.Word.controlledSwapProgram (QubitLayout.canonical _) .empty
    (liftedCompareBit n counterWidth)
    (liftedRCoeffWord n counterWidth)
    (liftedSCoeffWord n counterWidth)
    (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
    (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
    (fun i => Ne.symm
      (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth i i))

/-- Folded semantic action of the comparison-controlled `r`/`s` coefficient-word
swap. -/
def compareControlledRSSwapStep
    (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  EncodedBit.Word.controlledSwapStep
    (liftedCompareBit n counterWidth)
    (liftedRCoeffWord n counterWidth)
    (liftedSCoeffWord n counterWidth)
    (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
    (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
    (fun i => Ne.symm
      (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth i i))

/-- The comparison-controlled `r`/`s` coefficient-word swap program realizes its
folded base-gate semantics. -/
lemma compareControlledRSSwap_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (compareControlledRSSwapProgram n counterWidth) environment
      (compareControlledRSSwapStep n counterWidth) :=
  EncodedBit.Word.controlledSwap_realizes (environment := environment)
    (QubitLayout.canonical _) .empty
    (liftedCompareBit n counterWidth)
    (liftedRCoeffWord n counterWidth)
    (liftedSCoeffWord n counterWidth)
    (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
    (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
    (fun i => Ne.symm
      (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth i i))

/-- The comparison-controlled `r`/`s` word swap preserves the comparison
ancilla. -/
lemma compareControlledRSSwapStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (compareControlledRSSwapStep n counterWidth x) =
      (liftedCompareBit n counterWidth).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth i i))
      (liftedCompareBit n counterWidth)
      (fun i => Ne.symm
        (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth i))
      (fun i => Ne.symm
        (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth i))
      x

/-- The comparison-controlled `r`/`s` coefficient-word swap preserves the
active flag. -/
lemma compareControlledRSSwapStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (compareControlledRSSwapStep n counterWidth x) =
      (liftedActiveBit n counterWidth).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth i i))
      (liftedActiveBit n counterWidth)
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.rCoeffBit n counterWidth i)
          (RegisterBits.activeBit n counterWidth)
          (Ne.symm (RegisterBits.active_rCoeff_wire_ne n counterWidth i)))
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.sCoeffBit n counterWidth i)
          (RegisterBits.activeBit n counterWidth)
          (Ne.symm (RegisterBits.active_sCoeff_wire_ne n counterWidth i)))
      x

/-- The comparison-controlled `r`/`s` coefficient-word swap preserves every
stored branch-history bit. -/
lemma compareControlledRSSwapStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (compareControlledRSSwapStep n counterWidth x) =
      (liftedHistoryBit n counterWidth historyIndex).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth i i))
      (liftedHistoryBit n counterWidth historyIndex)
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.rCoeffBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (RegisterBits.rCoeff_history_wire_ne n counterWidth i
            historyIndex))
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.sCoeffBit n counterWidth i)
          (RegisterBits.historyBit n counterWidth historyIndex)
          (RegisterBits.sCoeff_history_wire_ne n counterWidth i
            historyIndex))
      x

/-- The comparison-controlled `r`/`s` coefficient-word swap preserves the first
scratch bit. -/
lemma compareControlledRSSwapStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (compareControlledRSSwapStep n counterWidth x) =
      (liftedScratchABit n counterWidth).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth i i))
      (liftedScratchABit n counterWidth)
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.rCoeffBit n counterWidth i)
          (RegisterBits.scratchABit n counterWidth)
          (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth i))
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.sCoeffBit n counterWidth i)
          (RegisterBits.scratchABit n counterWidth)
          (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth i))
      x

/-- The comparison-controlled `r`/`s` coefficient-word swap preserves the second
scratch bit. -/
lemma compareControlledRSSwapStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchBBit n counterWidth).get
        (compareControlledRSSwapStep n counterWidth x) =
      (liftedScratchBBit n counterWidth).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne n counterWidth i i))
      (liftedScratchBBit n counterWidth)
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.rCoeffBit n counterWidth i)
          (RegisterBits.scratchBBit n counterWidth)
          (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth i))
      (fun i =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.sCoeffBit n counterWidth i)
          (RegisterBits.scratchBBit n counterWidth)
          (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth i))
      x

/-- The comparison-controlled `r`/`s` word swap preserves every comparison-work
carry bit. -/
lemma compareControlledRSSwapStep_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (compareControlledRSSwapStep n counterWidth x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth i i))
      (liftedComparisonCarryBit n counterWidth workBit)
      (fun i => liftedRCoeffWordBit_liftedComparisonCarry_wire_ne
        n counterWidth i workBit)
      (fun i => liftedSCoeffWordBit_liftedComparisonCarry_wire_ne
        n counterWidth i workBit)
      x

/-- The comparison-controlled `r`/`s` word swap sends the selected `s`
coefficient bit to `r` when compare is set, and otherwise preserves the
selected `r` coefficient bit. -/
lemma compareControlledRSSwapStep_get_rCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedRCoeffWord n counterWidth).bit bit).get
        (compareControlledRSSwapStep n counterWidth x) =
      if (liftedCompareBit n counterWidth).get x then
        ((liftedSCoeffWord n counterWidth).bit bit).get x
      else
        ((liftedRCoeffWord n counterWidth).bit bit).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_left
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth i i))
      bit
      (fun j hj => liftedRCoeffWordBit_liftedRCoeffWordBit_wire_ne
        n counterWidth j bit hj)
      (fun j => liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
        n counterWidth j bit)
      (fun j => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth bit j))
      (fun j hj => liftedSCoeffWordBit_liftedSCoeffWordBit_wire_ne
        n counterWidth j bit hj)
      x

/-- The comparison-controlled `r`/`s` word swap sends the selected `r`
coefficient bit to `s` when compare is set, and otherwise preserves the
selected `s` coefficient bit. -/
lemma compareControlledRSSwapStep_get_sCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedSCoeffWord n counterWidth).bit bit).get
        (compareControlledRSSwapStep n counterWidth x) =
      if (liftedCompareBit n counterWidth).get x then
        ((liftedRCoeffWord n counterWidth).bit bit).get x
      else
        ((liftedSCoeffWord n counterWidth).bit bit).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_right
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth i i))
      bit
      (fun j hj => liftedRCoeffWordBit_liftedRCoeffWordBit_wire_ne
        n counterWidth j bit hj)
      (fun j => liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
        n counterWidth j bit)
      (fun j => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth bit j))
      (fun j hj => liftedSCoeffWordBit_liftedSCoeffWordBit_wire_ne
        n counterWidth j bit hj)
      x

/-- The comparison-controlled `r`/`s` coefficient-word swap preserves every
`u` value bit. -/
lemma compareControlledRSSwapStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedUWord n counterWidth).bit bit).get
        (compareControlledRSSwapStep n counterWidth x) =
      ((liftedUWord n counterWidth).bit bit).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth i i))
      ((liftedUWord n counterWidth).bit bit)
      (fun i => Ne.symm
        (liftedUWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth bit i))
      (fun i => Ne.symm
        (liftedUWordBit_liftedSCoeffWordBit_wire_ne
          n counterWidth bit i))
      x

/-- The comparison-controlled `r`/`s` coefficient-word swap preserves every
`v` value bit. -/
lemma compareControlledRSSwapStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit bit).get
        (compareControlledRSSwapStep n counterWidth x) =
      ((liftedVWord n counterWidth).bit bit).get x := by
  simpa [compareControlledRSSwapStep, compareControlledRSSwapGates]
    using EncodedBit.Word.controlledSwapStep_get_observed_of_swap_ne
      (liftedCompareBit n counterWidth)
      (liftedRCoeffWord n counterWidth)
      (liftedSCoeffWord n counterWidth)
      (liftedCompare_liftedRCoeffWordBit_wire_ne n counterWidth)
      (liftedCompare_liftedSCoeffWordBit_wire_ne n counterWidth)
      (fun i => Ne.symm
        (liftedSCoeffWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth i i))
      ((liftedVWord n counterWidth).bit bit)
      (fun i => Ne.symm
        (liftedVWordBit_liftedRCoeffWordBit_wire_ne
          n counterWidth bit i))
      (fun i => Ne.symm
        (liftedVWordBit_liftedSCoeffWordBit_wire_ne
          n counterWidth bit i))
      x

/-! ## Paired swap composition atom -/

/-- Appended base-gate program for the paired comparison-controlled `u`/`v`
and `r`/`s` swaps.  This packages the swap-based Kaliski round data-path slice
as one circuit object before the later arithmetic-update gates are sequenced
around it [HJN+20, modular-arithmetic.tex:176-195]. -/
def compareControlledUVRSSwapProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (compareControlledUVSwapProgram n counterWidth)
    (compareControlledRSSwapProgram n counterWidth)

/-- Folded semantic action of the paired comparison-controlled `u`/`v` and
`r`/`s` swaps. -/
def compareControlledUVRSSwapStep (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x =>
    compareControlledRSSwapStep n counterWidth
      (compareControlledUVSwapStep n counterWidth x)

/-- The paired comparison-controlled swap program realizes its folded
base-gate semantics. -/
lemma compareControlledUVRSSwap_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (compareControlledUVRSSwapProgram n counterWidth) environment
      (compareControlledUVRSSwapStep n counterWidth) := by
  unfold compareControlledUVRSSwapProgram compareControlledUVRSSwapStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := compareControlledUVSwapStep n counterWidth)
    (secondStep := compareControlledRSSwapStep n counterWidth)
    (compareControlledUVSwap_realizes n counterWidth)
    (compareControlledRSSwap_realizes n counterWidth)

/-- The paired swap preserves the comparison ancilla. -/
lemma compareControlledUVRSSwapStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      (liftedCompareBit n counterWidth).get x := by
  simp [compareControlledUVRSSwapStep,
    compareControlledRSSwapStep_get_compare,
    compareControlledUVSwapStep_get_compare]

/-- The paired swap preserves the active flag. -/
lemma compareControlledUVRSSwapStep_get_active
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      (liftedActiveBit n counterWidth).get x := by
  simp [compareControlledUVRSSwapStep,
    compareControlledRSSwapStep_get_active,
    compareControlledUVSwapStep_get_active]

/-- The paired swap preserves every stored branch-history bit. -/
lemma compareControlledUVRSSwapStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      (liftedHistoryBit n counterWidth historyIndex).get x := by
  simp [compareControlledUVRSSwapStep,
    compareControlledRSSwapStep_get_historyBit,
    compareControlledUVSwapStep_get_historyBit]

/-- The paired swap preserves the first scratch bit. -/
lemma compareControlledUVRSSwapStep_get_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      (liftedScratchABit n counterWidth).get x := by
  simp [compareControlledUVRSSwapStep,
    compareControlledRSSwapStep_get_scratchA,
    compareControlledUVSwapStep_get_scratchA]

/-- The paired swap preserves the second scratch bit. -/
lemma compareControlledUVRSSwapStep_get_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchBBit n counterWidth).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      (liftedScratchBBit n counterWidth).get x := by
  simp [compareControlledUVRSSwapStep,
    compareControlledRSSwapStep_get_scratchB,
    compareControlledUVSwapStep_get_scratchB]

/-- The paired swap preserves every comparison-work carry bit. -/
lemma compareControlledUVRSSwapStep_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  simp [compareControlledUVRSSwapStep,
    compareControlledRSSwapStep_get_comparisonCarry,
    compareControlledUVSwapStep_get_comparisonCarry]

/-- The paired swap sends the selected `v` value bit to `u` when compare is
set, and otherwise preserves the selected `u` value bit. -/
lemma compareControlledUVRSSwapStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedUWord n counterWidth).bit bit).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      if (liftedCompareBit n counterWidth).get x then
        ((liftedVWord n counterWidth).bit bit).get x
      else
        ((liftedUWord n counterWidth).bit bit).get x := by
  rw [compareControlledUVRSSwapStep]
  rw [compareControlledRSSwapStep_get_uWordBit]
  rw [compareControlledUVSwapStep_get_uWordBit]

/-- The paired swap sends the selected `u` value bit to `v` when compare is
set, and otherwise preserves the selected `v` value bit. -/
lemma compareControlledUVRSSwapStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit bit).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      if (liftedCompareBit n counterWidth).get x then
        ((liftedUWord n counterWidth).bit bit).get x
      else
        ((liftedVWord n counterWidth).bit bit).get x := by
  rw [compareControlledUVRSSwapStep]
  rw [compareControlledRSSwapStep_get_vWordBit]
  rw [compareControlledUVSwapStep_get_vWordBit]

/-- The paired swap sends the selected `s` coefficient bit to `r` when compare
is set, and otherwise preserves the selected `r` coefficient bit. -/
lemma compareControlledUVRSSwapStep_get_rCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedRCoeffWord n counterWidth).bit bit).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      if (liftedCompareBit n counterWidth).get x then
        ((liftedSCoeffWord n counterWidth).bit bit).get x
      else
        ((liftedRCoeffWord n counterWidth).bit bit).get x := by
  rw [compareControlledUVRSSwapStep]
  rw [compareControlledRSSwapStep_get_rCoeffWordBit]
  rw [compareControlledUVSwapStep_get_compare]
  rw [compareControlledUVSwapStep_get_sCoeffWordBit]
  rw [compareControlledUVSwapStep_get_rCoeffWordBit]

/-- The paired swap sends the selected `r` coefficient bit to `s` when compare
is set, and otherwise preserves the selected `s` coefficient bit. -/
lemma compareControlledUVRSSwapStep_get_sCoeffWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedSCoeffWord n counterWidth).bit bit).get
        (compareControlledUVRSSwapStep n counterWidth x) =
      if (liftedCompareBit n counterWidth).get x then
        ((liftedRCoeffWord n counterWidth).bit bit).get x
      else
        ((liftedSCoeffWord n counterWidth).bit bit).get x := by
  rw [compareControlledUVRSSwapStep]
  rw [compareControlledRSSwapStep_get_sCoeffWordBit]
  rw [compareControlledUVSwapStep_get_compare]
  rw [compareControlledUVSwapStep_get_rCoeffWordBit]
  rw [compareControlledUVSwapStep_get_sCoeffWordBit]

end
end MK
end MAU.Inversion
end QuantumAlg

end
