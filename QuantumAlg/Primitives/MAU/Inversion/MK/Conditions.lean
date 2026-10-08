/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Primitives.MAU.Inversion.MK.History

/-!
# Round conditions

This focused leaf is part of the exact fixed-round binary-GCD inversion
realization.  It is exported only through the canonical `MAU.Inversion.MK`
aggregate.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-! ## Coefficient-work-lifted odd branch-code staging -/

/-- Gate list that stages the RNSL17 `uGreater` branch code from the existing
comparison selector bit.  This is an explicit branch-code staging point for
the odd branch after the selector/data-path slice has preserved the comparison
condition; it does not write history or run the shift data path by itself
[RNSL17, ECDLP.tex:468-475]. -/
def uGreaterBranchCodeToScratchGates
    (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  activeConditionBranchCodeToScratchGates n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.uGreater

/-- Base-gate program for comparison-conditioned `uGreater` branch-code
staging. -/
def uGreaterBranchCodeToScratchProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uGreaterBranchCodeToScratchGates n counterWidth)

/-- Semantic step for comparison-conditioned `uGreater` branch-code staging. -/
def uGreaterBranchCodeToScratchStep
    (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uGreaterBranchCodeToScratchGates n counterWidth)

/-- The comparison-conditioned `uGreater` branch-code staging program is a
concrete encoded-bit base-gate realization over the Montgomery--Kaliski
register layout. -/
theorem uGreaterBranchCodeToScratch_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (uGreaterBranchCodeToScratchProgram n counterWidth)
      (uGreaterBranchCodeToScratchStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uGreaterBranchCodeToScratchGates n counterWidth)

/-- The fixed `uGreater` branch code is staged by two Toffoli leaves. -/
theorem uGreaterBranchCodeToScratchGates_length
    (n counterWidth : Nat) :
    (uGreaterBranchCodeToScratchGates n counterWidth).length = 2 := by
  simp [uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchGates, Branch.auxBit,
    Branch.historyBit]

/-- The fixed `uGreater` branch-code staging contains no X leaf. -/
theorem uGreaterBranchCodeToScratchGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((uGreaterBranchCodeToScratchGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simp [uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchGates, Branch.auxBit,
    Branch.historyBit]

/-- The fixed `uGreater` branch-code staging contains no CNOT leaf. -/
theorem uGreaterBranchCodeToScratchGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((uGreaterBranchCodeToScratchGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp [uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchGates, Branch.auxBit,
    Branch.historyBit]

/-- The fixed `uGreater` branch code has exactly two Toffoli leaves. -/
theorem uGreaterBranchCodeToScratchGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((uGreaterBranchCodeToScratchGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 := by
  simp [uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchGates, Branch.auxBit,
    Branch.historyBit]

/-- Comparison-conditioned `uGreater` branch-code staging preserves the active
flag. -/
theorem uGreaterBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (uGreaterBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  simpa [uGreaterBranchCodeToScratchStep,
    uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_active n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater x

/-- Comparison-conditioned `uGreater` branch-code staging preserves the
comparison selector bit. -/
theorem uGreaterBranchCodeToScratchStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.compareBit n counterWidth).get
        (uGreaterBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.compareBit n counterWidth).get x := by
  simpa [uGreaterBranchCodeToScratchStep,
    uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_condition n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater x

/-- Comparison-conditioned `uGreater` branch-code staging toggles scratchA
exactly under active `v < u`. -/
theorem uGreaterBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (uGreaterBranchCodeToScratchStep n counterWidth x) =
      ((RegisterBits.scratchABit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          (RegisterBits.compareBit n counterWidth).get x)) := by
  simpa [uGreaterBranchCodeToScratchStep,
    uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep, Branch.auxBit] using
      activeConditionBranchCodeToScratchStep_get_scratchA n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater x

/-- Comparison-conditioned `uGreater` branch-code staging toggles scratchB
exactly under active `v < u`. -/
theorem uGreaterBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.scratchBBit n counterWidth).get
        (uGreaterBranchCodeToScratchStep n counterWidth x) =
      ((RegisterBits.scratchBBit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          (RegisterBits.compareBit n counterWidth).get x)) := by
  simpa [uGreaterBranchCodeToScratchStep,
    uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep, Branch.historyBit] using
      activeConditionBranchCodeToScratchStep_get_scratchB n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater x

/-- Comparison-conditioned `uGreater` branch-code staging preserves every
stored branch-history bit. -/
theorem uGreaterBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (uGreaterBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  simpa [uGreaterBranchCodeToScratchStep,
    uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_historyBit n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater historyIndex x

/-- Comparison-conditioned `uGreater` branch-code staging preserves every
little-endian `u` value bit. -/
theorem uGreaterBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    (RegisterBits.uValueBit n counterWidth bit).get
        (uGreaterBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.uValueBit n counterWidth bit).get x := by
  simpa [uGreaterBranchCodeToScratchStep,
    uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater
        (RegisterBits.uValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.uValueBit] using
            Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        (by
          simpa [RegisterBits.uValueBit] using
            Ne.symm (RegisterBits.u_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        x

/-- Comparison-conditioned `uGreater` branch-code staging preserves every
little-endian `v` value bit. -/
theorem uGreaterBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    (RegisterBits.vValueBit n counterWidth bit).get
        (uGreaterBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.vValueBit n counterWidth bit).get x := by
  simpa [uGreaterBranchCodeToScratchStep,
    uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater
        (RegisterBits.vValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.vValueBit] using
            Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        (by
          simpa [RegisterBits.vValueBit] using
            Ne.symm (RegisterBits.v_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        x

/-- Comparison-conditioned `uGreater` branch-code staging preserves every
little-endian `s` coefficient value bit. -/
theorem uGreaterBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.sCoeffValueBit n counterWidth bit).get
        (uGreaterBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.sCoeffValueBit n counterWidth bit).get x := by
  simpa [uGreaterBranchCodeToScratchStep,
    uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater
        (RegisterBits.sCoeffValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.sCoeffValueBit] using
            Ne.symm (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        (by
          simpa [RegisterBits.sCoeffValueBit] using
            Ne.symm (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        x

/-- Comparison-conditioned `uGreater` branch-code staging preserves every
little-endian `r` coefficient value bit. -/
theorem uGreaterBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.rCoeffValueBit n counterWidth bit).get
        (uGreaterBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.rCoeffValueBit n counterWidth bit).get x := by
  simpa [uGreaterBranchCodeToScratchStep,
    uGreaterBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater
        (RegisterBits.rCoeffValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.rCoeffValueBit] using
            Ne.symm (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        (by
          simpa [RegisterBits.rCoeffValueBit] using
            Ne.symm (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        x

/-- Gate list for explicit `vLe` branch-code staging from the existing
comparison selector bit.  The RNSL17 `vLe` branch code is `00`, so this
concrete staging point is a no-op on both scratch-code bits while still
providing the same structural hook as the other branches [RNSL17,
ECDLP.tex:468-475]. -/
def vLeBranchCodeToScratchGates
    (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  activeConditionBranchCodeToScratchGates n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.vLe

/-- Base-gate program for explicit `vLe` branch-code staging. -/
def vLeBranchCodeToScratchProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (vLeBranchCodeToScratchGates n counterWidth)

/-- Semantic step for explicit `vLe` branch-code staging. -/
def vLeBranchCodeToScratchStep
    (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (vLeBranchCodeToScratchGates n counterWidth)

/-- The explicit `vLe` branch-code staging program is a concrete encoded-bit
base-gate realization over the Montgomery--Kaliski register layout. -/
theorem vLeBranchCodeToScratch_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (vLeBranchCodeToScratchProgram n counterWidth)
      (vLeBranchCodeToScratchStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (vLeBranchCodeToScratchGates n counterWidth)

/-- Explicit `vLe` branch-code staging preserves the active flag. -/
theorem vLeBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (vLeBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  simpa [vLeBranchCodeToScratchStep, vLeBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_active n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe x

/-- Explicit `vLe` branch-code staging preserves the comparison selector bit.
-/
theorem vLeBranchCodeToScratchStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.compareBit n counterWidth).get
        (vLeBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.compareBit n counterWidth).get x := by
  simpa [vLeBranchCodeToScratchStep, vLeBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_condition n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe x

/-- Explicit `vLe` branch-code staging preserves scratchA because its auxiliary
code bit is false. -/
theorem vLeBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (vLeBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.scratchABit n counterWidth).get x := by
  simpa [vLeBranchCodeToScratchStep, vLeBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep, Branch.auxBit] using
      activeConditionBranchCodeToScratchStep_get_scratchA n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe x

/-- Explicit `vLe` branch-code staging preserves scratchB because its history
code bit is false. -/
theorem vLeBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.scratchBBit n counterWidth).get
        (vLeBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.scratchBBit n counterWidth).get x := by
  simpa [vLeBranchCodeToScratchStep, vLeBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep, Branch.historyBit] using
      activeConditionBranchCodeToScratchStep_get_scratchB n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe x

/-- Explicit `vLe` branch-code staging preserves every stored branch-history
bit. -/
theorem vLeBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (vLeBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  simpa [vLeBranchCodeToScratchStep, vLeBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_historyBit n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe historyIndex x

/-- Explicit `vLe` branch-code staging preserves every little-endian `u`
value bit. -/
theorem vLeBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    (RegisterBits.uValueBit n counterWidth bit).get
        (vLeBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.uValueBit n counterWidth bit).get x := by
  simpa [vLeBranchCodeToScratchStep, vLeBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe
        (RegisterBits.uValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.uValueBit] using
            Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        (by
          simpa [RegisterBits.uValueBit] using
            Ne.symm (RegisterBits.u_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        x

/-- Explicit `vLe` branch-code staging preserves every little-endian `v`
value bit. -/
theorem vLeBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    (RegisterBits.vValueBit n counterWidth bit).get
        (vLeBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.vValueBit n counterWidth bit).get x := by
  simpa [vLeBranchCodeToScratchStep, vLeBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe
        (RegisterBits.vValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.vValueBit] using
            Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        (by
          simpa [RegisterBits.vValueBit] using
            Ne.symm (RegisterBits.v_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        x

/-- Explicit `vLe` branch-code staging preserves every little-endian `s`
coefficient value bit. -/
theorem vLeBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.sCoeffValueBit n counterWidth bit).get
        (vLeBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.sCoeffValueBit n counterWidth bit).get x := by
  simpa [vLeBranchCodeToScratchStep, vLeBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe
        (RegisterBits.sCoeffValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.sCoeffValueBit] using
            Ne.symm (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        (by
          simpa [RegisterBits.sCoeffValueBit] using
            Ne.symm (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        x

/-- Explicit `vLe` branch-code staging preserves every little-endian `r`
coefficient value bit. -/
theorem vLeBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.rCoeffValueBit n counterWidth bit).get
        (vLeBranchCodeToScratchStep n counterWidth x) =
      (RegisterBits.rCoeffValueBit n counterWidth bit).get x := by
  simpa [vLeBranchCodeToScratchStep, vLeBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchStep] using
      activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe
        (RegisterBits.rCoeffValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.rCoeffValueBit] using
            Ne.symm (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        (by
          simpa [RegisterBits.rCoeffValueBit] using
            Ne.symm (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
        x

/-- When the compare selector is true, the compare-conditioned `uGreater`
branch-code staging is the active-guarded fixed `uGreater` staging. -/
theorem uGreaterBranchCodeToScratchStep_eq_activeBranchCodeToScratchStep_of_compare_true
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = true) :
    uGreaterBranchCodeToScratchStep n counterWidth x =
      activeBranchCodeToScratchStep n counterWidth Branch.uGreater x := by
  let active := RegisterBits.activeBit n counterWidth
  let compare := RegisterBits.compareBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  have hcompareLocal : compare.get x = true := by
    simpa [compare] using hcompare
  change
      EncodedBit.toffoliStep active compare scratchB
          (EncodedBit.toffoliStep active compare scratchA x) =
        EncodedBit.cnotStep active scratchB
          (EncodedBit.cnotStep active scratchA x)
  have hfirst :
      EncodedBit.toffoliStep active compare scratchA x =
        EncodedBit.cnotStep active scratchA x := by
    by_cases hactive : active.get x
    · simp [EncodedBit.toffoliStep, EncodedBit.cnotStep, hactive,
        hcompareLocal]
    · simp [EncodedBit.toffoliStep, EncodedBit.cnotStep, hactive]
  rw [hfirst]
  let y := EncodedBit.cnotStep active scratchA x
  have hcompareAfter :
      compare.get y = true := by
    dsimp [y]
    rw [EncodedBit.cnotStep_get_of_target_ne active scratchA compare
      (Ne.symm (RegisterBits.compare_scratchA_wire_ne n counterWidth))]
    exact hcompareLocal
  change EncodedBit.toffoliStep active compare scratchB y =
    EncodedBit.cnotStep active scratchB y
  by_cases hactiveY : active.get y
  · simp [EncodedBit.toffoliStep, EncodedBit.cnotStep, hactiveY,
      hcompareAfter]
  · simp [EncodedBit.toffoliStep, EncodedBit.cnotStep, hactiveY]

/-- When the compare selector is false, the compare-conditioned `uGreater`
branch-code staging is the active-guarded fixed `vLe` staging. -/
theorem uGreaterBranchCodeToScratchStep_eq_activeBranchCodeToScratchStep_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = false) :
    uGreaterBranchCodeToScratchStep n counterWidth x =
      activeBranchCodeToScratchStep n counterWidth Branch.vLe x := by
  let active := RegisterBits.activeBit n counterWidth
  let compare := RegisterBits.compareBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  have hcompareLocal : compare.get x = false := by
    simpa [compare] using hcompare
  change
      EncodedBit.toffoliStep active compare scratchB
          (EncodedBit.toffoliStep active compare scratchA x) =
        x
  have hfirst :
      EncodedBit.toffoliStep active compare scratchA x = x := by
    by_cases hactive : active.get x
    · simp [EncodedBit.toffoliStep, hactive, hcompareLocal]
    · simp [EncodedBit.toffoliStep, hactive]
  rw [hfirst]
  by_cases hactive : active.get x
  · simp [EncodedBit.toffoliStep, hactive, hcompareLocal]
  · simp [EncodedBit.toffoliStep, hactive]

/-- Lifted semantic step for `uGreater` branch-code staging over the attached
comparison-work register. -/
def liftedUGreaterBranchCodeToScratchStep
    (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x => (uGreaterBranchCodeToScratchStep n counterWidth x.1, x.2)

/-- Circuit for lifted `uGreater` branch-code staging. -/
def liftedUGreaterBranchCodeToScratchProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (uGreaterBranchCodeToScratchProgram n counterWidth)

/-- The lifted `uGreater` circuit realizes its product action. -/
theorem liftedUGreaterBranchCodeToScratch_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (liftedUGreaterBranchCodeToScratchProgram n counterWidth)
      (liftedUGreaterBranchCodeToScratchStep n counterWidth) := by
  unfold liftedUGreaterBranchCodeToScratchProgram
    liftedUGreaterBranchCodeToScratchStep
  simpa [registersWithComparisonWorkEncoding] using
    UnitaryCircuit.Realizes.onBinaryPrefix
      (right := comparisonWorkEncoding n)
      (uGreaterBranchCodeToScratch_realizes n counterWidth)

/-- Lifted `uGreater` branch-code staging preserves the active flag. -/
theorem liftedUGreaterBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x) =
      (liftedActiveBit n counterWidth).get x := by
  change (RegisterBits.activeBit n counterWidth).get
        (uGreaterBranchCodeToScratchStep n counterWidth x.1) =
      (RegisterBits.activeBit n counterWidth).get x.1
  exact uGreaterBranchCodeToScratchStep_get_active n counterWidth x.1

/-- Lifted `uGreater` branch-code staging preserves the comparison selector
bit. -/
theorem liftedUGreaterBranchCodeToScratchStep_get_compare
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x) =
      (liftedCompareBit n counterWidth).get x := by
  change (RegisterBits.compareBit n counterWidth).get
        (uGreaterBranchCodeToScratchStep n counterWidth x.1) =
      (RegisterBits.compareBit n counterWidth).get x.1
  exact uGreaterBranchCodeToScratchStep_get_compare n counterWidth x.1

/-- Lifted `uGreater` branch-code staging toggles scratchA exactly under the
lifted active flag and comparison condition. -/
theorem liftedUGreaterBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x) =
      ((liftedScratchABit n counterWidth).get x ^^
        ((liftedActiveBit n counterWidth).get x &&
          (liftedCompareBit n counterWidth).get x)) := by
  change (RegisterBits.scratchABit n counterWidth).get
        (uGreaterBranchCodeToScratchStep n counterWidth x.1) =
      ((RegisterBits.scratchABit n counterWidth).get x.1 ^^
        ((RegisterBits.activeBit n counterWidth).get x.1 &&
          (RegisterBits.compareBit n counterWidth).get x.1))
  exact uGreaterBranchCodeToScratchStep_get_scratchA n counterWidth x.1

/-- Lifted `uGreater` branch-code staging toggles scratchB exactly under the
lifted active flag and comparison condition. -/
theorem liftedUGreaterBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchBBit n counterWidth).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x) =
      ((liftedScratchBBit n counterWidth).get x ^^
        ((liftedActiveBit n counterWidth).get x &&
          (liftedCompareBit n counterWidth).get x)) := by
  change (RegisterBits.scratchBBit n counterWidth).get
        (uGreaterBranchCodeToScratchStep n counterWidth x.1) =
      ((RegisterBits.scratchBBit n counterWidth).get x.1 ^^
        ((RegisterBits.activeBit n counterWidth).get x.1 &&
          (RegisterBits.compareBit n counterWidth).get x.1))
  exact uGreaterBranchCodeToScratchStep_get_scratchB n counterWidth x.1

/-- Lifted semantic step for explicit `vLe` branch-code staging over the
attached comparison-work register. -/
def liftedVLeBranchCodeToScratchStep
    (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x => (vLeBranchCodeToScratchStep n counterWidth x.1, x.2)

/-- Circuit for lifted explicit `vLe` branch-code staging. -/
def liftedVLeBranchCodeToScratchProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (vLeBranchCodeToScratchProgram n counterWidth)

/-- The lifted `vLe` circuit realizes its product action. -/
theorem liftedVLeBranchCodeToScratch_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (liftedVLeBranchCodeToScratchProgram n counterWidth)
      (liftedVLeBranchCodeToScratchStep n counterWidth) := by
  unfold liftedVLeBranchCodeToScratchProgram liftedVLeBranchCodeToScratchStep
  simpa [registersWithComparisonWorkEncoding] using
    UnitaryCircuit.Realizes.onBinaryPrefix
      (right := comparisonWorkEncoding n)
      (vLeBranchCodeToScratch_realizes n counterWidth)

/-- Lifted explicit `vLe` branch-code staging preserves the active flag. -/
theorem liftedVLeBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x) =
      (liftedActiveBit n counterWidth).get x := by
  change (RegisterBits.activeBit n counterWidth).get
        (vLeBranchCodeToScratchStep n counterWidth x.1) =
      (RegisterBits.activeBit n counterWidth).get x.1
  exact vLeBranchCodeToScratchStep_get_active n counterWidth x.1

/-- Lifted explicit `vLe` branch-code staging preserves the comparison
selector bit. -/
theorem liftedVLeBranchCodeToScratchStep_get_compare
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x) =
      (liftedCompareBit n counterWidth).get x := by
  change (RegisterBits.compareBit n counterWidth).get
        (vLeBranchCodeToScratchStep n counterWidth x.1) =
      (RegisterBits.compareBit n counterWidth).get x.1
  exact vLeBranchCodeToScratchStep_get_compare n counterWidth x.1

/-- Lifted explicit `vLe` branch-code staging preserves scratchA. -/
theorem liftedVLeBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x) =
      (liftedScratchABit n counterWidth).get x := by
  change (RegisterBits.scratchABit n counterWidth).get
        (vLeBranchCodeToScratchStep n counterWidth x.1) =
      (RegisterBits.scratchABit n counterWidth).get x.1
  exact vLeBranchCodeToScratchStep_get_scratchA n counterWidth x.1

/-- Lifted explicit `vLe` branch-code staging preserves scratchB. -/
theorem liftedVLeBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchBBit n counterWidth).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x) =
      (liftedScratchBBit n counterWidth).get x := by
  change (RegisterBits.scratchBBit n counterWidth).get
        (vLeBranchCodeToScratchStep n counterWidth x.1) =
      (RegisterBits.scratchBBit n counterWidth).get x.1
  exact vLeBranchCodeToScratchStep_get_scratchB n counterWidth x.1

/-- Coefficient-work-lifted `uGreater` branch-code staging. -/
def coeffWorkUGreaterBranchCodeToScratchStep
    (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (liftedUGreaterBranchCodeToScratchStep n counterWidth)

/-- Gate list for coefficient-work-lifted `uGreater` branch-code staging. -/
def coeffWorkUGreaterBranchCodeToScratchGates
    (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  ((uGreaterBranchCodeToScratchGates n counterWidth).map
      (EncodedBit.GateSpec.prodLeft (comparisonWorkEncoding n))).map
    (EncodedBit.GateSpec.prodLeft (coeffAdderWorkEncoding n))

/-- Base-gate program for coefficient-work-lifted `uGreater` branch-code
staging. -/
def coeffWorkUGreaterBranchCodeToScratchProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkUGreaterBranchCodeToScratchGates n counterWidth)

/-- The explicit coefficient-work-lifted `uGreater` branch-code staging gate list
has the existing lifted semantic action. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_eq_gateList
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkUGreaterBranchCodeToScratchGates n counterWidth) x =
      coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x := by
  unfold coeffWorkUGreaterBranchCodeToScratchGates
    coeffWorkUGreaterBranchCodeToScratchStep
    liftComparisonWorkStepToCoeffAdderWork
    liftedUGreaterBranchCodeToScratchStep
    uGreaterBranchCodeToScratchStep
  unfold registersWithCoeffAdderWorkEncoding
    registersWithComparisonWorkEncoding
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  rw [EncodedBit.GateSpec.stepList_prodLeft]

/-- The coefficient-work-lifted `uGreater` branch-code staging program realizes
the existing semantic action. -/
theorem coeffWorkUGreaterBranchCodeToScratch_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterBranchCodeToScratchProgram n counterWidth)
      (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkUGreaterBranchCodeToScratchGates n counterWidth)
    (coeffWorkUGreaterBranchCodeToScratchStep_eq_gateList n counterWidth)

/-- Product lifting preserves the fixed `uGreater` staging length. -/
theorem coeffWorkUGreaterBranchCodeToScratchGates_length
    (n counterWidth : Nat) :
    (coeffWorkUGreaterBranchCodeToScratchGates n counterWidth).length = 2 := by
  unfold coeffWorkUGreaterBranchCodeToScratchGates
    registersWithCoeffAdderWorkEncoding registersWithComparisonWorkEncoding
  simp only [List.length_map, uGreaterBranchCodeToScratchGates_length]

private theorem coeffWorkUGreaterBranchCodeToScratchGates_events
    (n counterWidth : Nat) :
    (coeffWorkUGreaterBranchCodeToScratchGates n counterWidth).map
        (EncodedBit.GateSpec.event .empty) =
      (uGreaterBranchCodeToScratchGates n counterWidth).map
        (EncodedBit.GateSpec.event .empty) := by
  unfold coeffWorkUGreaterBranchCodeToScratchGates
    registersWithCoeffAdderWorkEncoding registersWithComparisonWorkEncoding
  rw [EncodedBit.GateSpec.map_event_prodLeft,
    EncodedBit.GateSpec.map_event_prodLeft]

/-- Product lifting preserves the fixed `uGreater` staging X coordinate. -/
theorem coeffWorkUGreaterBranchCodeToScratchGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkUGreaterBranchCodeToScratchGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  calc
    ((coeffWorkUGreaterBranchCodeToScratchGates n counterWidth).map
        EncodedBit.GateSpec.xMultiplicity).sum =
        ((uGreaterBranchCodeToScratchGates n counterWidth).map
          EncodedBit.GateSpec.xMultiplicity).sum :=
      EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
        .empty
        (coeffWorkUGreaterBranchCodeToScratchGates_events n counterWidth)
    _ = 0 := uGreaterBranchCodeToScratchGates_xMultiplicity_sum n counterWidth

/-- Product lifting preserves the fixed `uGreater` staging CNOT coordinate. -/
theorem coeffWorkUGreaterBranchCodeToScratchGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkUGreaterBranchCodeToScratchGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  calc
    ((coeffWorkUGreaterBranchCodeToScratchGates n counterWidth).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
        ((uGreaterBranchCodeToScratchGates n counterWidth).map
          EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        .empty
        (coeffWorkUGreaterBranchCodeToScratchGates_events n counterWidth)
    _ = 0 :=
      uGreaterBranchCodeToScratchGates_cnotMultiplicity_sum n counterWidth

/-- Product lifting preserves the fixed `uGreater` staging Toffoli coordinate. -/
theorem coeffWorkUGreaterBranchCodeToScratchGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((coeffWorkUGreaterBranchCodeToScratchGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 := by
  calc
    ((coeffWorkUGreaterBranchCodeToScratchGates n counterWidth).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
        ((uGreaterBranchCodeToScratchGates n counterWidth).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        .empty
        (coeffWorkUGreaterBranchCodeToScratchGates_events n counterWidth)
    _ = 2 :=
      uGreaterBranchCodeToScratchGates_toffoliMultiplicity_sum n counterWidth

/-- Coefficient-work-lifted explicit `vLe` branch-code staging. -/
def coeffWorkVLeBranchCodeToScratchStep
    (n counterWidth : Nat) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (liftedVLeBranchCodeToScratchStep n counterWidth)

/-- Circuit for coefficient-work-lifted explicit `vLe` branch-code staging. -/
def coeffWorkVLeBranchCodeToScratchProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (liftedVLeBranchCodeToScratchProgram n counterWidth)

/-- The coefficient-work-lifted `vLe` circuit realizes its step. -/
theorem coeffWorkVLeBranchCodeToScratch_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVLeBranchCodeToScratchProgram n counterWidth)
      (coeffWorkVLeBranchCodeToScratchStep n counterWidth) :=
  liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (liftedVLeBranchCodeToScratch_realizes n counterWidth)

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_carryIn
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_carryWorkBit
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_carryIn
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_carryWorkBit
    (n counterWidth : Nat) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves the active
flag. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  change (liftedActiveBit n counterWidth).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x.1) =
      (liftedActiveBit n counterWidth).get x.1
  exact liftedUGreaterBranchCodeToScratchStep_get_active n counterWidth x.1

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves the
comparison selector bit. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_compare
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  change (liftedCompareBit n counterWidth).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x.1) =
      (liftedCompareBit n counterWidth).get x.1
  exact liftedUGreaterBranchCodeToScratchStep_get_compare n counterWidth x.1

/-- Coefficient-work-lifted `uGreater` branch-code staging toggles scratchA
under the active comparison condition. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderScratchABit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderCompareBit n counterWidth).get x)) := by
  change (liftedScratchABit n counterWidth).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedScratchABit n counterWidth).get x.1 ^^
        ((liftedActiveBit n counterWidth).get x.1 &&
          (liftedCompareBit n counterWidth).get x.1))
  exact liftedUGreaterBranchCodeToScratchStep_get_scratchA
    n counterWidth x.1

/-- Coefficient-work-lifted `uGreater` branch-code staging toggles scratchB
under the active comparison condition. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderScratchBBit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderCompareBit n counterWidth).get x)) := by
  change (liftedScratchBBit n counterWidth).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedScratchBBit n counterWidth).get x.1 ^^
        ((liftedActiveBit n counterWidth).get x.1 &&
          (liftedCompareBit n counterWidth).get x.1))
  exact liftedUGreaterBranchCodeToScratchStep_get_scratchB
    n counterWidth x.1

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves every
stored branch-history bit. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  change (liftedHistoryBit n counterWidth historyIndex).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x.1) =
      (liftedHistoryBit n counterWidth historyIndex).get x.1
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (uGreaterBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x.1.1
  exact uGreaterBranchCodeToScratchStep_get_historyBit
    n counterWidth historyIndex x.1.1

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves each `u`
word bit. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderUWord n counterWidth).bit bit).get x := by
  change ((liftedUWord n counterWidth).bit bit).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedUWord n counterWidth).bit bit).get x.1
  change (RegisterBits.uValueBit n counterWidth bit).get
        (uGreaterBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.uValueBit n counterWidth bit).get x.1.1
  exact uGreaterBranchCodeToScratchStep_get_uWordBit n counterWidth bit x.1.1

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves each `v`
word bit. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderVWord n counterWidth).bit bit).get x := by
  change ((liftedVWord n counterWidth).bit bit).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedVWord n counterWidth).bit bit).get x.1
  change (RegisterBits.vValueBit n counterWidth bit).get
        (uGreaterBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.vValueBit n counterWidth bit).get x.1.1
  exact uGreaterBranchCodeToScratchStep_get_vWordBit n counterWidth bit x.1.1

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves the `u`
source word. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_u
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUGreaterBranchCodeToScratchStep_get_uWordBit
    n counterWidth bit x
  simpa [coeffAdderUWord_get_testBit] using h

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves the `v`
source word. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_v
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUGreaterBranchCodeToScratchStep_get_vWordBit
    n counterWidth bit x
  simpa [coeffAdderVWord_get_testBit] using h

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves each `s`
coefficient value bit. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x := by
  change ((liftedSCoeffValueWord n counterWidth).bit bit).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedSCoeffValueWord n counterWidth).bit bit).get x.1
  change (RegisterBits.sCoeffValueBit n counterWidth bit).get
        (uGreaterBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.sCoeffValueBit n counterWidth bit).get x.1.1
  exact uGreaterBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth bit x.1.1

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves each `r`
coefficient value bit. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x := by
  change ((liftedRCoeffValueWord n counterWidth).bit bit).get
        (liftedUGreaterBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedRCoeffValueWord n counterWidth).bit bit).get x.1
  change (RegisterBits.rCoeffValueBit n counterWidth bit).get
        (uGreaterBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.rCoeffValueBit n counterWidth bit).get x.1.1
  exact uGreaterBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth bit x.1.1

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves the `s`
coefficient word. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_sCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUGreaterBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth bit x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- Coefficient-work-lifted `uGreater` branch-code staging preserves the `r`
coefficient word. -/
theorem coeffWorkUGreaterBranchCodeToScratchStep_get_rCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUGreaterBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth bit x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves the
active flag. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  change (liftedActiveBit n counterWidth).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x.1) =
      (liftedActiveBit n counterWidth).get x.1
  exact liftedVLeBranchCodeToScratchStep_get_active n counterWidth x.1

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves the
comparison selector bit. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_compare
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  change (liftedCompareBit n counterWidth).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x.1) =
      (liftedCompareBit n counterWidth).get x.1
  exact liftedVLeBranchCodeToScratchStep_get_compare n counterWidth x.1

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves
scratchA. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  change (liftedScratchABit n counterWidth).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x.1) =
      (liftedScratchABit n counterWidth).get x.1
  exact liftedVLeBranchCodeToScratchStep_get_scratchA n counterWidth x.1

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves
scratchB. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  change (liftedScratchBBit n counterWidth).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x.1) =
      (liftedScratchBBit n counterWidth).get x.1
  exact liftedVLeBranchCodeToScratchStep_get_scratchB n counterWidth x.1

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves every
stored branch-history bit. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  change (liftedHistoryBit n counterWidth historyIndex).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x.1) =
      (liftedHistoryBit n counterWidth historyIndex).get x.1
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (vLeBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x.1.1
  exact vLeBranchCodeToScratchStep_get_historyBit
    n counterWidth historyIndex x.1.1

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves each
`u` word bit. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit bit).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderUWord n counterWidth).bit bit).get x := by
  change ((liftedUWord n counterWidth).bit bit).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedUWord n counterWidth).bit bit).get x.1
  change (RegisterBits.uValueBit n counterWidth bit).get
        (vLeBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.uValueBit n counterWidth bit).get x.1.1
  exact vLeBranchCodeToScratchStep_get_uWordBit n counterWidth bit x.1.1

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves each
`v` word bit. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit bit).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderVWord n counterWidth).bit bit).get x := by
  change ((liftedVWord n counterWidth).bit bit).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedVWord n counterWidth).bit bit).get x.1
  change (RegisterBits.vValueBit n counterWidth bit).get
        (vLeBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.vValueBit n counterWidth bit).get x.1.1
  exact vLeBranchCodeToScratchStep_get_vWordBit n counterWidth bit x.1.1

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves the
`u` source word. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_u
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeBranchCodeToScratchStep n counterWidth x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVLeBranchCodeToScratchStep_get_uWordBit
    n counterWidth bit x
  simpa [coeffAdderUWord_get_testBit] using h

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves the
`v` source word. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_v
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeBranchCodeToScratchStep n counterWidth x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVLeBranchCodeToScratchStep_get_vWordBit
    n counterWidth bit x
  simpa [coeffAdderVWord_get_testBit] using h

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves each
`s` coefficient value bit. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit bit).get x := by
  change ((liftedSCoeffValueWord n counterWidth).bit bit).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedSCoeffValueWord n counterWidth).bit bit).get x.1
  change (RegisterBits.sCoeffValueBit n counterWidth bit).get
        (vLeBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.sCoeffValueBit n counterWidth bit).get x.1.1
  exact vLeBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth bit x.1.1

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves each
`r` coefficient value bit. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (bit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit bit).get x := by
  change ((liftedRCoeffValueWord n counterWidth).bit bit).get
        (liftedVLeBranchCodeToScratchStep n counterWidth x.1) =
      ((liftedRCoeffValueWord n counterWidth).bit bit).get x.1
  change (RegisterBits.rCoeffValueBit n counterWidth bit).get
        (vLeBranchCodeToScratchStep n counterWidth x.1.1) =
      (RegisterBits.rCoeffValueBit n counterWidth bit).get x.1.1
  exact vLeBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth bit x.1.1

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves the
`s` coefficient word. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_sCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeBranchCodeToScratchStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVLeBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth bit x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- Coefficient-work-lifted explicit `vLe` branch-code staging preserves the
`r` coefficient word. -/
theorem coeffWorkVLeBranchCodeToScratchStep_get_rCoeff
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeBranchCodeToScratchStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVLeBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth bit x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- Sequence the odd `uGreater` selector-plus-add data path with explicit
branch-code staging.  The resulting object is the staged input expected by the
aux-active shift dispatch, but it is still only one branch slice, not a full
round update. -/
def coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkUGreaterBranchCodeToScratchStep n counterWidth
      (coeffWorkUGreaterSelectorThenAddRIntoSStep n counterWidth bit
        historyIndex x)

/-- Circuit for the `uGreater` add path followed by branch-code staging. -/
def coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUGreaterSelectorThenAddRIntoSProgram n counterWidth bit
      historyIndex)
    (coeffWorkUGreaterBranchCodeToScratchProgram n counterWidth)

/-- The staged `uGreater` add-path circuit realizes its step. -/
theorem coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratch_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchProgram
        n counterWidth bit historyIndex)
      (coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchProgram
    coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkUGreaterSelectorThenAddRIntoSStep n counterWidth bit
        historyIndex)
    (secondStep := coeffWorkUGreaterBranchCodeToScratchStep n counterWidth)
    (coeffWorkUGreaterSelectorThenAddRIntoS_realizes n counterWidth bit
      historyIndex)
    (coeffWorkUGreaterBranchCodeToScratch_realizes n counterWidth)

/-- The staged `uGreater` branch-code slice preserves the active flag. -/
theorem
    coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep
          n counterWidth bit historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_active]
  exact coeffWorkUGreaterSelectorThenAddRIntoSStep_get_active
    n counterWidth bit historyIndex x

/-- On clean comparison inputs and clean scratchA, explicit `uGreater`
branch-code staging leaves scratchA equal to active `v < u`. -/
theorem
    coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      ((RegisterBits.activeBit n counterWidth).get x &&
        decide (x.v.val < x.u.val)) := by
  rw [coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_scratchA]
  rw [coeffWorkUGreaterSelectorThenAddRIntoSStep_get_active]
  rw [coeffWorkUGreaterSelectorThenAddRIntoSStep_get_compare_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hfinal]
  rw [coeffWorkUGreaterSelectorThenAddRIntoSStep_get_scratchA]
  change
    (x.scratchA ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val))) =
      ((RegisterBits.activeBit n counterWidth).get x &&
        decide (x.v.val < x.u.val))
  rw [hscratchA]
  simp

/-- After clean explicit `uGreater` branch-code staging, the aux-active shift
dispatch selects the unconditioned `u/s` shift group when the round is active
and the comparison selector is true. -/
theorem
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_after_uGreaterBranchCodeStaging_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hfinal : bit.val + 1 = n)
    (hgreater : decide (x.v.val < x.u.val) = true) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
        (coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      coeffWorkUDiv2ThenSMul2Step n counterWidth
        (coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) := by
  let staged :=
    coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hactiveStaged :
      (coeffAdderActiveBit n counterWidth).get staged = true := by
    dsimp [staged]
    rw [
      coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAStaged :
      (coeffAdderScratchABit n counterWidth).get staged = true := by
    dsimp [staged]
    rw [
      coeffWorkUGreaterSelectorThenAddRIntoSThenBranchCodeToScratchStep_get_scratchA_clean
        n counterWidth bit historyIndex x work hscratchA hcompare hfinal]
    have hgreaterProp : x.v.val < x.u.val :=
      of_decide_eq_true hgreater
    simp [hactive, hgreaterProp]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_of_active_true_scratchA_true
      n counterWidth staged hactiveStaged hscratchAStaged

/-- Sequence the odd `vLe` selector-plus-add data path with explicit zero-code
branch-code staging. -/
def coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkVLeBranchCodeToScratchStep n counterWidth
      (coeffWorkVLeSelectorThenAddSIntoRStep n counterWidth bit historyIndex x)

/-- Circuit for the `vLe` add path followed by zero-code staging. -/
def coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVLeSelectorThenAddSIntoRProgram n counterWidth bit historyIndex)
    (coeffWorkVLeBranchCodeToScratchProgram n counterWidth)

/-- The staged `vLe` add-path circuit realizes its step. -/
theorem coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratch_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchProgram
        n counterWidth bit historyIndex)
      (coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchProgram
    coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVLeSelectorThenAddSIntoRStep n counterWidth bit historyIndex)
    (secondStep := coeffWorkVLeBranchCodeToScratchStep n counterWidth)
    (coeffWorkVLeSelectorThenAddSIntoR_realizes n counterWidth bit historyIndex)
    (coeffWorkVLeBranchCodeToScratch_realizes n counterWidth)

/-- The staged `vLe` branch-code slice preserves the active flag. -/
theorem coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep
          n counterWidth bit historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep]
  rw [coeffWorkVLeBranchCodeToScratchStep_get_active]
  exact coeffWorkVLeSelectorThenAddSIntoRStep_get_active
    n counterWidth bit historyIndex x

/-- On clean scratchA, explicit zero-code `vLe` branch-code staging preserves
scratchA through the selector-plus-add path. -/
theorem
    coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      false := by
  rw [coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep]
  rw [coeffWorkVLeBranchCodeToScratchStep_get_scratchA]
  rw [coeffWorkVLeSelectorThenAddSIntoRStep_get_scratchA]
  change x.scratchA = false
  exact hscratchA

/-- After explicit zero-code `vLe` branch-code staging, the aux-active shift
dispatch selects the unconditioned `v/r` shift group when the active flag
remains true and the auxiliary bit remains false. -/
theorem
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_after_vLeBranchCodeStaging_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
        (coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      coeffWorkVDiv2ThenRMul2Step n counterWidth
        (coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) := by
  let staged :=
    coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hactiveStaged :
      (coeffAdderActiveBit n counterWidth).get staged = true := by
    dsimp [staged]
    rw [
      coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAStaged :
      (coeffAdderScratchABit n counterWidth).get staged = false := by
    dsimp [staged]
    exact
      coeffWorkVLeSelectorThenAddSIntoRThenBranchCodeToScratchStep_get_scratchA_clean
        n counterWidth bit historyIndex x work hscratchA
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_of_active_true_scratchA_false
      n counterWidth staged hactiveStaged hscratchAStaged

/-- Sequence the corrected odd `uGreater` selector-plus-subtract/add data path
with explicit branch-code staging.  The resulting object is the staged input
expected by the auxiliary active/branch-code shift dispatch. -/
def coeffWorkUGreaterSubAddBranchCodeToScratchStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkUGreaterBranchCodeToScratchStep n counterWidth
      (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
        n counterWidth bit historyIndex x)

/-- Circuit for the corrected `uGreater` subtract/add path and staging. -/
def coeffWorkUGreaterSubAddBranchCodeToScratchProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRProgram
      n counterWidth bit historyIndex)
    (coeffWorkUGreaterBranchCodeToScratchProgram n counterWidth)

/-- The corrected staged `uGreater` circuit realizes its step. -/
theorem coeffWorkUGreaterSubAddBranchCodeToScratch_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterSubAddBranchCodeToScratchProgram
        n counterWidth bit historyIndex)
      (coeffWorkUGreaterSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkUGreaterSubAddBranchCodeToScratchProgram
    coeffWorkUGreaterSubAddBranchCodeToScratchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
        n counterWidth bit historyIndex)
    (secondStep := coeffWorkUGreaterBranchCodeToScratchStep n counterWidth)
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoR_realizes
      n counterWidth bit historyIndex)
    (coeffWorkUGreaterBranchCodeToScratch_realizes n counterWidth)

/-- The corrected staged `uGreater` branch-code slice preserves the active
flag. -/
theorem coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUGreaterSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_active]
  exact coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_active
    n counterWidth bit historyIndex x

/-- On clean comparison inputs and clean scratchA, corrected explicit
`uGreater` branch-code staging leaves scratchA equal to active `v < u`. -/
theorem
    coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUGreaterSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      ((RegisterBits.activeBit n counterWidth).get x &&
        decide (x.v.val < x.u.val)) := by
  let y :=
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hscratchInput :
      (coeffAdderScratchABit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchY : (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    exact
      coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_scratchA_clean
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work) hscratchInput
  have hactiveY :
      (coeffAdderActiveBit n counterWidth).get y =
        (RegisterBits.activeBit n counterWidth).get x := by
    dsimp [y]
    rw [
      coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_active]
    rfl
  have hcompareY :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (x.v.val < x.u.val) := by
    dsimp [y]
    exact
      coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_compare_clean
        n counterWidth bit historyIndex x work hscratchA hcompare hfinal
  rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep]
  change
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth y) =
      ((RegisterBits.activeBit n counterWidth).get x &&
        decide (x.v.val < x.u.val))
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_scratchA]
  rw [hscratchY, hactiveY, hcompareY]
  simp

/-- On clean comparison inputs, corrected explicit `uGreater` branch-code
staging preserves the staged `v < u` predicate. -/
theorem coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUGreaterSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_compare]
  exact
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_compare_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- Corrected explicit `uGreater` branch-code staging preserves the selector's
branch-history toggle through the final branch-code staging step. -/
theorem coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUGreaterSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val))) := by
  rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_historyBit]
  exact
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_history_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hscratchB
      hfinal

/-- Corrected explicit `uGreater` branch-code staging preserves every history
slot except the selected target slot. -/
theorem coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkUGreaterSubAddBranchCodeToScratchStep
          n counterWidth bit target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_historyBit]
  exact
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_historyBit_of_ne
      n counterWidth bit target observed hne x

/-- Corrected explicit `uGreater` branch-code staging preserves the source
subtract result on `u`. -/
theorem coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_u_sub_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkUGreaterSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex x).1.1.u =
      x.1.1.u - x.1.1.v := by
  let y :=
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
      n counterWidth bit historyIndex x
  have hyu :
      y.1.1.u = x.1.1.u - x.1.1.v := by
    dsimp [y]
    exact
      coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_u_sub_of_clean
        n counterWidth bit historyIndex x hcarry hwork
  have hbranch :
      (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth y).1.1.u =
        y.1.1.u :=
    coeffWorkUGreaterBranchCodeToScratchStep_get_u n counterWidth y
  rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep]
  exact hbranch.trans hyu

/-- Corrected explicit `uGreater` branch-code staging preserves the
coefficient update `r := r + s`. -/
theorem coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_rCoeff_add_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkUGreaterSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex x).1.1.rCoeff =
      x.1.1.rCoeff + x.1.1.sCoeff := by
  let y :=
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
      n counterWidth bit historyIndex x
  have hyr :
      y.1.1.rCoeff = x.1.1.rCoeff + x.1.1.sCoeff := by
    dsimp [y]
    exact
      coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_rCoeff_add_of_clean
        n counterWidth bit historyIndex x hcarry hwork
  have hbranch :
      (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth y).1.1.rCoeff =
        y.1.1.rCoeff :=
    coeffWorkUGreaterBranchCodeToScratchStep_get_rCoeff n counterWidth y
  rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep]
  exact hbranch.trans hyr

/-- Corrected explicit `uGreater` branch-code staging preserves the untouched
`s` coefficient word. -/
theorem coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_sCoeff
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex x).1.1.sCoeff =
      x.1.1.sCoeff := by
  let z :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep
      n counterWidth bit historyIndex x
  let y :=
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
      n counterWidth bit historyIndex x
  have hys : y.1.1.sCoeff = x.1.1.sCoeff := by
    have hsub := coeffWorkSubVFromUThenAddSIntoRStep_get_sCoeff
      n counterWidth z
    have hsel := coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_sCoeff
      n counterWidth bit historyIndex x
    dsimp [y, z]
    rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
    change (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth z).1.1.sCoeff =
      x.1.1.sCoeff
    rw [hsub, hsel]
  have hbranch :
      (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth y).1.1.sCoeff =
        y.1.1.sCoeff :=
    coeffWorkUGreaterBranchCodeToScratchStep_get_sCoeff n counterWidth y
  rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep]
  exact hbranch.trans hys

/-- Corrected explicit `uGreater` branch-code staging preserves the untouched
`v` source word. -/
theorem coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_v
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex x).1.1.v =
      x.1.1.v := by
  let y :=
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
      n counterWidth bit historyIndex x
  have hyv : y.1.1.v = x.1.1.v := by
    dsimp [y]
    exact
      coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_v
        n counterWidth bit historyIndex x
  have hbranch :
      (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth y).1.1.v =
        y.1.1.v :=
    coeffWorkUGreaterBranchCodeToScratchStep_get_v n counterWidth y
  rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep]
  exact hbranch.trans hyv

/-- After clean corrected `uGreater` branch-code staging, the aux-active shift
dispatch selects the unconditioned `u/s` shift group when the round is active
and the comparison selector is true. -/
theorem
    coeffWorkAuxShiftDispatch_eq_uShift_after_uGreaterSubAddCode_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hfinal : bit.val + 1 = n)
    (hgreater : decide (x.v.val < x.u.val) = true) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
        (coeffWorkUGreaterSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      coeffWorkUDiv2ThenSMul2Step n counterWidth
        (coeffWorkUGreaterSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) := by
  let staged :=
    coeffWorkUGreaterSubAddBranchCodeToScratchStep
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hactiveStaged :
      (coeffAdderActiveBit n counterWidth).get staged = true := by
    dsimp [staged]
    rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAStaged :
      (coeffAdderScratchABit n counterWidth).get staged = true := by
    dsimp [staged]
    rw [coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_scratchA_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hfinal]
    rw [hactive, hgreater]
    simp
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_of_active_true_scratchA_true
      n counterWidth staged hactiveStaged hscratchAStaged

/-- Sequence the corrected odd `vLe` selector-plus-subtract/add data path with
explicit zero-code branch-code staging. -/
def coeffWorkVLeSubAddBranchCodeToScratchStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkVLeBranchCodeToScratchStep n counterWidth
      (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
        n counterWidth bit historyIndex x)

/-- Circuit for the corrected `vLe` subtract/add path and zero-code staging. -/
def coeffWorkVLeSubAddBranchCodeToScratchProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSProgram
      n counterWidth bit historyIndex)
    (coeffWorkVLeBranchCodeToScratchProgram n counterWidth)

/-- The corrected staged `vLe` circuit realizes its step. -/
theorem coeffWorkVLeSubAddBranchCodeToScratch_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVLeSubAddBranchCodeToScratchProgram
        n counterWidth bit historyIndex)
      (coeffWorkVLeSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkVLeSubAddBranchCodeToScratchProgram
    coeffWorkVLeSubAddBranchCodeToScratchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
        n counterWidth bit historyIndex)
    (secondStep := coeffWorkVLeBranchCodeToScratchStep n counterWidth)
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoS_realizes
      n counterWidth bit historyIndex)
    (coeffWorkVLeBranchCodeToScratch_realizes n counterWidth)

/-- The corrected staged `vLe` branch-code slice preserves the active flag. -/
theorem coeffWorkVLeSubAddBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVLeSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkVLeSubAddBranchCodeToScratchStep]
  rw [coeffWorkVLeBranchCodeToScratchStep_get_active]
  exact coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_active
    n counterWidth bit historyIndex x

/-- On clean scratchA, corrected explicit zero-code `vLe` branch-code staging
preserves the clean auxiliary bit through the subtract/add path. -/
theorem coeffWorkVLeSubAddBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVLeSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      false := by
  let y :=
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hscratchInput :
      (coeffAdderScratchABit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchY : (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    exact
      coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_scratchA_clean
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work) hscratchInput
  rw [coeffWorkVLeSubAddBranchCodeToScratchStep]
  change
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVLeBranchCodeToScratchStep n counterWidth y) =
      false
  rw [coeffWorkVLeBranchCodeToScratchStep_get_scratchA]
  exact hscratchY

/-- On clean comparison inputs, corrected explicit `vLe` branch-code staging
preserves the staged comparison predicate. -/
theorem coeffWorkVLeSubAddBranchCodeToScratchStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVLeSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkVLeSubAddBranchCodeToScratchStep]
  rw [coeffWorkVLeBranchCodeToScratchStep_get_compare]
  exact
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_compare_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- Corrected explicit zero-code `vLe` branch-code staging preserves the
zero-code branch-history no-op through the final branch-code staging step. -/
theorem coeffWorkVLeSubAddBranchCodeToScratchStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVLeSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  rw [coeffWorkVLeSubAddBranchCodeToScratchStep]
  rw [coeffWorkVLeBranchCodeToScratchStep_get_historyBit]
  exact
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_history_clean
      n counterWidth bit historyIndex x work hscratchB

/-- Corrected explicit `vLe` branch-code staging preserves every history slot
except the selected target slot. -/
theorem coeffWorkVLeSubAddBranchCodeToScratchStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkVLeSubAddBranchCodeToScratchStep
          n counterWidth bit target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkVLeSubAddBranchCodeToScratchStep]
  rw [coeffWorkVLeBranchCodeToScratchStep_get_historyBit]
  exact
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_historyBit_of_ne
      n counterWidth bit target observed hne x

/-- Corrected explicit `vLe` branch-code staging preserves the source
subtract result on `v`. -/
theorem coeffWorkVLeSubAddBranchCodeToScratchStep_get_v_sub_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkVLeSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex x).1.1.v =
      x.1.1.v - x.1.1.u := by
  let y :=
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
      n counterWidth bit historyIndex x
  have hyv :
      y.1.1.v = x.1.1.v - x.1.1.u := by
    dsimp [y]
    exact
      coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_v_sub_of_clean
        n counterWidth bit historyIndex x hcarry hwork
  have hbranch :
      (coeffWorkVLeBranchCodeToScratchStep n counterWidth y).1.1.v =
        y.1.1.v :=
    coeffWorkVLeBranchCodeToScratchStep_get_v n counterWidth y
  rw [coeffWorkVLeSubAddBranchCodeToScratchStep]
  exact hbranch.trans hyv

/-- Corrected explicit `vLe` branch-code staging preserves the coefficient
update `s := s + r`. -/
theorem coeffWorkVLeSubAddBranchCodeToScratchStep_get_sCoeff_add_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkVLeSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex x).1.1.sCoeff =
      x.1.1.sCoeff + x.1.1.rCoeff := by
  let y :=
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
      n counterWidth bit historyIndex x
  have hys :
      y.1.1.sCoeff = x.1.1.sCoeff + x.1.1.rCoeff := by
    dsimp [y]
    exact
      coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_sCoeff_add_of_clean
        n counterWidth bit historyIndex x hcarry hwork
  have hbranch :
      (coeffWorkVLeBranchCodeToScratchStep n counterWidth y).1.1.sCoeff =
        y.1.1.sCoeff :=
    coeffWorkVLeBranchCodeToScratchStep_get_sCoeff n counterWidth y
  rw [coeffWorkVLeSubAddBranchCodeToScratchStep]
  exact hbranch.trans hys

/-- Corrected explicit `vLe` branch-code staging preserves the untouched `r`
coefficient word. -/
theorem coeffWorkVLeSubAddBranchCodeToScratchStep_get_rCoeff
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex x).1.1.rCoeff =
      x.1.1.rCoeff := by
  let z :=
    coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex x
  let y :=
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
      n counterWidth bit historyIndex x
  have hyr : y.1.1.rCoeff = x.1.1.rCoeff := by
    have hsub := coeffWorkSubUFromVThenAddRIntoSStep_get_rCoeff
      n counterWidth z
    have hsel := coeffWorkVLeSelectorBranchHistoryWriteStep_get_rCoeff
      n counterWidth bit historyIndex x
    dsimp [y, z]
    rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
    change (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth z).1.1.rCoeff =
      x.1.1.rCoeff
    rw [hsub, hsel]
  have hbranch :
      (coeffWorkVLeBranchCodeToScratchStep n counterWidth y).1.1.rCoeff =
        y.1.1.rCoeff :=
    coeffWorkVLeBranchCodeToScratchStep_get_rCoeff n counterWidth y
  rw [coeffWorkVLeSubAddBranchCodeToScratchStep]
  exact hbranch.trans hyr

/-- Corrected explicit `vLe` branch-code staging preserves the untouched `u`
source word. -/
theorem coeffWorkVLeSubAddBranchCodeToScratchStep_get_u
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex x).1.1.u =
      x.1.1.u := by
  let y :=
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
      n counterWidth bit historyIndex x
  have hyu : y.1.1.u = x.1.1.u := by
    dsimp [y]
    exact coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_u
      n counterWidth bit historyIndex x
  have hbranch :
      (coeffWorkVLeBranchCodeToScratchStep n counterWidth y).1.1.u =
        y.1.1.u :=
    coeffWorkVLeBranchCodeToScratchStep_get_u n counterWidth y
  rw [coeffWorkVLeSubAddBranchCodeToScratchStep]
  exact hbranch.trans hyu

/-- After clean corrected `vLe` branch-code staging, the aux-active shift
dispatch selects the unconditioned `v/r` shift group when the active flag
remains true and the auxiliary bit remains false. -/
theorem coeffWorkAuxShiftDispatch_eq_vShift_after_vLeSubAddCode_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
        (coeffWorkVLeSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      coeffWorkVDiv2ThenRMul2Step n counterWidth
        (coeffWorkVLeSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) := by
  let staged :=
    coeffWorkVLeSubAddBranchCodeToScratchStep
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hactiveStaged :
      (coeffAdderActiveBit n counterWidth).get staged = true := by
    dsimp [staged]
    rw [coeffWorkVLeSubAddBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAStaged :
      (coeffAdderScratchABit n counterWidth).get staged = false := by
    dsimp [staged]
    exact
      coeffWorkVLeSubAddBranchCodeToScratchStep_get_scratchA_clean
        n counterWidth bit historyIndex x work hscratchA
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_of_active_true_scratchA_false
      n counterWidth staged hactiveStaged hscratchAStaged

/-! ## `u`-even condition staging -/

/-- Gate list that computes the negated selected `u` bit into the comparison
ancilla.  On a clean comparison bit this stages the `u`-even condition for the
first RNSL17 branch; it is not the full branch selector [RNSL17,
ECDLP.tex:399-421,468-475]. -/
def uBitNotToCompareGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  [ EncodedBit.GateSpec.x (RegisterBits.compareBit n counterWidth)
  , EncodedBit.GateSpec.cnot
      (RegisterBits.uBit n counterWidth bit)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.u_compare_wire_ne n counterWidth bit) ]

/-- Base-gate program for staging a negated selected `u` bit into compare. -/
def uBitNotToCompareProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uBitNotToCompareGates n counterWidth bit)

/-- Semantic step for staging a negated selected `u` bit into compare. -/
def uBitNotToCompareStep
    (n counterWidth : Nat) (bit : Fin n) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uBitNotToCompareGates n counterWidth bit)

/-- The `u`-bit-to-compare staging program is a concrete encoded-bit
base-gate realization over the Montgomery--Kaliski register layout. -/
theorem uBitNotToCompare_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (uBitNotToCompareProgram n counterWidth bit)
      (uBitNotToCompareStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uBitNotToCompareGates n counterWidth bit)

/-- Staging toggles compare as `!compare ^^ uBit`; in particular, clean compare
becomes the negated selected `u` bit. -/
theorem uBitNotToCompareStep_get_compare
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.compareBit n counterWidth).get
        (uBitNotToCompareStep n counterWidth bit x) =
      (!(RegisterBits.compareBit n counterWidth).get x ^^
        (RegisterBits.uBit n counterWidth bit).get x) := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  change compare.get (EncodedBit.cnotStep source compare
      (compare.flip x)) = (!compare.get x ^^ source.get x)
  rw [EncodedBit.cnotStep_get_target]
  rw [EncodedBit.get_flip_of_wire_ne compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]
  rw [EncodedBit.get_flip_self]

/-- On a clean comparison ancilla, staging computes the negated selected `u`
bit. -/
theorem uBitNotToCompareStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hclean : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.compareBit n counterWidth).get
        (uBitNotToCompareStep n counterWidth bit x) =
      !(RegisterBits.uBit n counterWidth bit).get x := by
  rw [uBitNotToCompareStep_get_compare]
  have hcleanValue : x.compare = false := by
    simpa using hclean
  cases (RegisterBits.uBit n counterWidth bit).get x <;>
    simp [hcleanValue]

/-- Staging preserves the selected `u` bit. -/
theorem uBitNotToCompareStep_get_uBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uBit n counterWidth bit).get
        (uBitNotToCompareStep n counterWidth bit x) =
      (RegisterBits.uBit n counterWidth bit).get x := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  change source.get (EncodedBit.cnotStep source compare
      (compare.flip x)) = source.get x
  rw [EncodedBit.cnotStep_get_of_target_ne source compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]
  rw [EncodedBit.get_flip_of_wire_ne compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]

/-- Staging preserves the active flag. -/
theorem uBitNotToCompareStep_get_active
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (uBitNotToCompareStep n counterWidth bit x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  change active.get (EncodedBit.cnotStep source compare
      (compare.flip x)) = active.get x
  rw [EncodedBit.cnotStep_get_of_target_ne source compare active
    (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth))]
  rw [EncodedBit.get_flip_of_wire_ne compare active
    (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth))]

/-- Staging a negated selected `u` bit preserves every stored branch-history
bit. -/
theorem uBitNotToCompareStep_get_historyBit
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (uBitNotToCompareStep n counterWidth bit x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  let history := RegisterBits.historyBit n counterWidth historyIndex
  change history.get (EncodedBit.cnotStep source compare
      (compare.flip x)) = history.get x
  rw [EncodedBit.cnotStep_get_of_target_ne source compare history
    (RegisterBits.compare_history_wire_ne n counterWidth historyIndex)]
  rw [EncodedBit.get_flip_of_wire_ne compare history
    (RegisterBits.compare_history_wire_ne n counterWidth historyIndex)]

/-- Gate list that stages the first RNSL17 branch code from the selected
`u`-bit parity test, then restores the comparison ancilla.  On clean compare it
xors the `u`-even branch code `10` into the scratch encoder bits under the
active guard.  The other branch selector/history slices are implemented
separately; the full round data-path update remains a later obligation
[RNSL17, ECDLP.tex:399-421,468-475]. -/
def uEvenBranchCodeToScratchGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  uBitNotToCompareGates n counterWidth bit ++
  activeConditionBranchCodeToScratchGates n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.uEven ++
  (uBitNotToCompareGates n counterWidth bit).reverse

/-- Base-gate program for active-guarded `u`-even branch-code staging with
compare restored. -/
def uEvenBranchCodeToScratchProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uEvenBranchCodeToScratchGates n counterWidth bit)

/-- Semantic step for active-guarded `u`-even branch-code staging with compare
restored. -/
def uEvenBranchCodeToScratchStep
    (n counterWidth : Nat) (bit : Fin n) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uEvenBranchCodeToScratchGates n counterWidth bit)

/-- The `u`-even branch-code staging program is a concrete encoded-bit base-gate
realization over the Montgomery--Kaliski register layout. -/
theorem uEvenBranchCodeToScratch_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (uEvenBranchCodeToScratchProgram n counterWidth bit)
      (uEvenBranchCodeToScratchStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uEvenBranchCodeToScratchGates n counterWidth bit)

/-- On clean compare, the `u`-even branch-code staging restores the comparison
ancilla after using it as the condition bit. -/
theorem uEvenBranchCodeToScratchStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hclean : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.compareBit n counterWidth).get
        (uEvenBranchCodeToScratchStep n counterWidth bit x) =
      false := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  have hcompare : compare.get x = false := hclean
  change compare.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    false
  rw [EncodedBit.get_flip_self]
  rw [EncodedBit.cnotStep_get_target]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA
    compare (Ne.symm (RegisterBits.compare_scratchA_wire_ne n counterWidth))]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA
    source (Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth bit))]
  rw [EncodedBit.cnotStep_get_target]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]
  rw [EncodedBit.get_flip_of_wire_ne compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]
  rw [EncodedBit.get_flip_self]
  cases source.get x <;> simp [hcompare]

/-- On clean compare, `u`-even branch-code staging toggles scratchA exactly when
the active flag is set and the selected `u` bit is zero. -/
theorem uEvenBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hclean : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.scratchABit n counterWidth).get
        (uEvenBranchCodeToScratchStep n counterWidth bit x) =
      ((RegisterBits.scratchABit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          !(RegisterBits.uBit n counterWidth bit).get x)) := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  have hcompare : compare.get x = false := hclean
  change scratchA.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    (scratchA.get x ^^ (active.get x && !source.get x))
  rw [EncodedBit.get_flip_of_wire_ne compare scratchA
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare scratchA
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)]
  rw [EncodedBit.toffoliStep_get_target]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare active
    (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth))]
  rw [EncodedBit.get_flip_of_wire_ne compare active
    (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth))]
  rw [EncodedBit.cnotStep_get_target]
  rw [EncodedBit.get_flip_self]
  rw [EncodedBit.get_flip_of_wire_ne compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare scratchA
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)]
  rw [EncodedBit.get_flip_of_wire_ne compare scratchA
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)]
  cases source.get x <;> simp [hcompare]

/-- On clean compare, `u`-even branch-code staging preserves scratchB because
the `u`-even code is `10` [RNSL17, ECDLP.tex:471]. -/
theorem uEvenBranchCodeToScratchStep_get_scratchB_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (_hclean : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.scratchBBit n counterWidth).get
        (uEvenBranchCodeToScratchStep n counterWidth bit x) =
      (RegisterBits.scratchBBit n counterWidth).get x := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  change scratchB.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    scratchB.get x
  rw [EncodedBit.get_flip_of_wire_ne compare scratchB
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare scratchB
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA scratchB
    (RegisterBits.scratchA_scratchB_wire_ne n counterWidth)]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare scratchB
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)]
  rw [EncodedBit.get_flip_of_wire_ne compare scratchB
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)]

/-- Active-guarded `u`-even branch-code staging preserves the selected `u` bit.
-/
theorem uEvenBranchCodeToScratchStep_get_uBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uBit n counterWidth bit).get
        (uEvenBranchCodeToScratchStep n counterWidth bit x) =
      (RegisterBits.uBit n counterWidth bit).get x := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  change source.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    source.get x
  rw [EncodedBit.get_flip_of_wire_ne compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA source
    (Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth bit))]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]
  rw [EncodedBit.get_flip_of_wire_ne compare source
    (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth bit))]

/-- Active-guarded `u`-even branch-code staging preserves every little-endian
`u` value bit. -/
theorem uEvenBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uValueBit n counterWidth targetBit).get
        (uEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      (RegisterBits.uValueBit n counterWidth targetBit).get x := by
  let source := RegisterBits.uBit n counterWidth selectorBit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let observed := RegisterBits.uValueBit n counterWidth targetBit
  have hcompareObserved : compare.wire ≠ observed.wire := by
    simpa [compare, observed, RegisterBits.uValueBit] using
      Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit))
  have hscratchAObserved : scratchA.wire ≠ observed.wire := by
    simpa [scratchA, observed, RegisterBits.uValueBit] using
      Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit))
  change observed.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    observed.get x
  rw [EncodedBit.get_flip_of_wire_ne compare observed hcompareObserved]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare observed
    hcompareObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA
    observed hscratchAObserved]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare observed
    hcompareObserved]
  rw [EncodedBit.get_flip_of_wire_ne compare observed hcompareObserved]

/-- Active-guarded `u`-even branch-code staging preserves every little-endian
`v` value bit. -/
theorem uEvenBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vValueBit n counterWidth targetBit).get
        (uEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      (RegisterBits.vValueBit n counterWidth targetBit).get x := by
  let source := RegisterBits.uBit n counterWidth selectorBit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let observed := RegisterBits.vValueBit n counterWidth targetBit
  have hcompareObserved : compare.wire ≠ observed.wire := by
    simpa [compare, observed, RegisterBits.vValueBit] using
      Ne.symm (RegisterBits.v_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit))
  have hscratchAObserved : scratchA.wire ≠ observed.wire := by
    simpa [scratchA, observed, RegisterBits.vValueBit] using
      Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit))
  change observed.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    observed.get x
  rw [EncodedBit.get_flip_of_wire_ne compare observed hcompareObserved]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare observed
    hcompareObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA
    observed hscratchAObserved]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare observed
    hcompareObserved]
  rw [EncodedBit.get_flip_of_wire_ne compare observed hcompareObserved]

/-- Active-guarded `u`-even branch-code staging preserves every little-endian
`s` coefficient value bit. -/
theorem uEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.sCoeffValueBit n counterWidth targetBit).get
        (uEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      (RegisterBits.sCoeffValueBit n counterWidth targetBit).get x := by
  let source := RegisterBits.uBit n counterWidth selectorBit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let observed := RegisterBits.sCoeffValueBit n counterWidth targetBit
  have hcompareObserved : compare.wire ≠ observed.wire := by
    simpa [compare, observed, RegisterBits.sCoeffValueBit] using
      RegisterBits.compare_sCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit)
  have hscratchAObserved : scratchA.wire ≠ observed.wire := by
    simpa [scratchA, observed, RegisterBits.sCoeffValueBit] using
      Ne.symm (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit))
  change observed.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    observed.get x
  rw [EncodedBit.get_flip_of_wire_ne compare observed hcompareObserved]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare observed
    hcompareObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA
    observed hscratchAObserved]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare observed
    hcompareObserved]
  rw [EncodedBit.get_flip_of_wire_ne compare observed hcompareObserved]

/-- Active-guarded `u`-even branch-code staging preserves every little-endian
`r` coefficient value bit. -/
theorem uEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.rCoeffValueBit n counterWidth targetBit).get
        (uEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      (RegisterBits.rCoeffValueBit n counterWidth targetBit).get x := by
  let source := RegisterBits.uBit n counterWidth selectorBit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let observed := RegisterBits.rCoeffValueBit n counterWidth targetBit
  have hcompareObserved : compare.wire ≠ observed.wire := by
    simpa [compare, observed, RegisterBits.rCoeffValueBit] using
      RegisterBits.compare_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit)
  have hscratchAObserved : scratchA.wire ≠ observed.wire := by
    simpa [scratchA, observed, RegisterBits.rCoeffValueBit] using
      Ne.symm (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit))
  change observed.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    observed.get x
  rw [EncodedBit.get_flip_of_wire_ne compare observed hcompareObserved]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare observed
    hcompareObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA
    observed hscratchAObserved]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare observed
    hcompareObserved]
  rw [EncodedBit.get_flip_of_wire_ne compare observed hcompareObserved]

/-- Active-guarded `u`-even branch-code staging preserves the active flag. -/
theorem uEvenBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (uEvenBranchCodeToScratchStep n counterWidth bit x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  change active.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    active.get x
  rw [EncodedBit.get_flip_of_wire_ne compare active
    (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth))]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare active
    (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth))]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA active
    (Ne.symm (RegisterBits.active_scratchA_wire_ne n counterWidth))]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare active
    (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth))]
  rw [EncodedBit.get_flip_of_wire_ne compare active
    (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth))]

/-- Active-guarded `u`-even branch-code staging preserves every stored
branch-history bit. -/
theorem uEvenBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (uEvenBranchCodeToScratchStep n counterWidth bit x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  let source := RegisterBits.uBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let history := RegisterBits.historyBit n counterWidth historyIndex
  change history.get
      (compare.flip
        (EncodedBit.cnotStep source compare
          (EncodedBit.toffoliStep active compare scratchA
            (EncodedBit.cnotStep source compare (compare.flip x))))) =
    history.get x
  rw [EncodedBit.get_flip_of_wire_ne compare history
    (RegisterBits.compare_history_wire_ne n counterWidth historyIndex)]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare history
    (RegisterBits.compare_history_wire_ne n counterWidth historyIndex)]
  rw [EncodedBit.toffoliStep_get_of_target_ne active compare scratchA history
    (RegisterBits.scratchA_history_wire_ne n counterWidth historyIndex)]
  rw [EncodedBit.cnotStep_get_of_target_ne source compare history
    (RegisterBits.compare_history_wire_ne n counterWidth historyIndex)]
  rw [EncodedBit.get_flip_of_wire_ne compare history
    (RegisterBits.compare_history_wire_ne n counterWidth historyIndex)]

/-- The complete `u`-even branch-code staging list is palindromic. -/
@[simp] theorem uEvenBranchCodeToScratchGates_reverse
    (n counterWidth : Nat) (bit : Fin n) :
    (uEvenBranchCodeToScratchGates n counterWidth bit).reverse =
      uEvenBranchCodeToScratchGates n counterWidth bit := by
  simp [uEvenBranchCodeToScratchGates, uBitNotToCompareGates,
    activeConditionBranchCodeToScratchGates, Branch.auxBit,
    Branch.historyBit]

/-- Gate list that runs the `u`-even branch-code staging, attempts the
branch-history write, and then uncomputes the scratch-code staging.  Since the
RNSL17 `uEven` code is `10`, the history code bit is zero; this slice witnesses
that the same concrete gate structure leaves `m_i` unchanged for this branch
[RNSL17, ECDLP.tex:468-475]. -/
def uEvenBranchHistoryWriteGates
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  uEvenBranchCodeToScratchGates n counterWidth bit ++
  [activeScratchBToHistoryGate n counterWidth historyIndex] ++
  (uEvenBranchCodeToScratchGates n counterWidth bit).reverse

/-- Base-gate program for the `u`-even branch-history no-op write slice. -/
def uEvenBranchHistoryWriteProgram
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uEvenBranchHistoryWriteGates n counterWidth bit historyIndex)

/-- Semantic step for the `u`-even branch-history no-op write slice. -/
def uEvenBranchHistoryWriteStep
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uEvenBranchHistoryWriteGates n counterWidth bit historyIndex)

/-- The `u`-even branch-history write slice is a concrete encoded-bit base-gate
realization over the Montgomery--Kaliski register layout. -/
theorem uEvenBranchHistoryWrite_realizes
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (uEvenBranchHistoryWriteProgram n counterWidth bit historyIndex)
      (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uEvenBranchHistoryWriteGates n counterWidth bit historyIndex)

theorem uEvenBranchHistoryWriteStep_eq
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x =
      uEvenBranchCodeToScratchStep n counterWidth bit
        (activeScratchBToHistoryStep n counterWidth historyIndex
          (uEvenBranchCodeToScratchStep n counterWidth bit x)) := by
  simp [uEvenBranchHistoryWriteStep, uEvenBranchHistoryWriteGates,
    uEvenBranchCodeToScratchStep, activeScratchBToHistoryStep,
    EncodedBit.GateSpec.stepList_append, EncodedBit.GateSpec.stepList]

/-- On clean compare and clean scratchB, the `u`-even history-write slice leaves
the selected `m_i` bit unchanged, matching the `uEven` history code bit
`0` [RNSL17, ECDLP.tex:471]. -/
theorem uEvenBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  rw [uEvenBranchHistoryWriteStep_eq]
  rw [uEvenBranchCodeToScratchStep_get_historyBit]
  rw [activeScratchBToHistoryStep_get_historyBit]
  rw [uEvenBranchCodeToScratchStep_get_historyBit]
  rw [uEvenBranchCodeToScratchStep_get_active]
  rw [uEvenBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth bit x hcompare]
  simp [hscratchB]

/-- The `u`-even branch-history write slice preserves every history slot
except the selected target slot. -/
theorem uEvenBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth observed).get
        (uEvenBranchHistoryWriteStep n counterWidth bit target x) =
      (RegisterBits.historyBit n counterWidth observed).get x := by
  rw [uEvenBranchHistoryWriteStep_eq]
  rw [uEvenBranchCodeToScratchStep_get_historyBit]
  rw [activeScratchBToHistoryStep_get_historyBit_of_ne
    n counterWidth target observed hne]
  rw [uEvenBranchCodeToScratchStep_get_historyBit]

/-- Lifted semantic step for the `uEven` branch-history write over the attached
comparison-work register. -/
def liftedUEvenBranchHistoryWriteStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x => (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x.1, x.2)

/-- Circuit for the lifted `uEven` branch-history write. -/
def liftedUEvenBranchHistoryWriteProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (uEvenBranchHistoryWriteProgram n counterWidth bit historyIndex)

/-- The lifted `uEven` circuit realizes its product action. -/
theorem liftedUEvenBranchHistoryWrite_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (liftedUEvenBranchHistoryWriteProgram n counterWidth bit historyIndex)
      (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex) := by
  unfold liftedUEvenBranchHistoryWriteProgram liftedUEvenBranchHistoryWriteStep
  simpa [registersWithComparisonWorkEncoding] using
    UnitaryCircuit.Realizes.onBinaryPrefix
      (right := comparisonWorkEncoding n)
      (uEvenBranchHistoryWrite_realizes n counterWidth bit historyIndex)

/-- On clean lifted compare and scratchB bits, the lifted `uEven` history-write
slice leaves the selected branch-history bit unchanged. -/
theorem liftedUEvenBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false)
    (hscratchB : (liftedScratchBBit n counterWidth).get x = false) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedHistoryBit n counterWidth historyIndex).get x := by
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x.1) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x.1
  apply uEvenBranchHistoryWriteStep_get_history_clean
  · change (RegisterBits.compareBit n counterWidth).get x.1 = false at hcompare
    exact hcompare
  · change (RegisterBits.scratchBBit n counterWidth).get x.1 = false at hscratchB
    exact hscratchB

/-- The lifted `uEven` history-write slice preserves every history slot except
the selected target slot. -/
theorem liftedUEvenBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth observed).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit target x) =
      (liftedHistoryBit n counterWidth observed).get x := by
  change (RegisterBits.historyBit n counterWidth observed).get
        (uEvenBranchHistoryWriteStep n counterWidth bit target x.1) =
      (RegisterBits.historyBit n counterWidth observed).get x.1
  exact uEvenBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth bit target observed hne x.1

/-- The lifted `uEven` branch-history write preserves every comparison-work
carry bit, because it only acts on the leading Kaliski registers. -/
theorem liftedUEvenBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  rfl

/-- On clean compare, the `uEven` branch-history write slice restores the
comparison ancilla after staging, writing, and uncomputing the branch code. -/
theorem uEvenBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.compareBit n counterWidth).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      false := by
  rw [uEvenBranchHistoryWriteStep_eq]
  let y :=
    activeScratchBToHistoryStep n counterWidth historyIndex
      (uEvenBranchCodeToScratchStep n counterWidth bit x)
  have hcompareAfterWrite :
      (RegisterBits.compareBit n counterWidth).get y = false := by
    dsimp [y]
    rw [activeScratchBToHistoryStep_get_compare]
    exact uEvenBranchCodeToScratchStep_get_compare_clean n counterWidth bit
      x hcompare
  change (RegisterBits.compareBit n counterWidth).get
      (uEvenBranchCodeToScratchStep n counterWidth bit y) = false
  exact uEvenBranchCodeToScratchStep_get_compare_clean n counterWidth bit y
    hcompareAfterWrite

/-- On clean compare, the `uEven` branch-history write slice restores the first
scratch-code bit. -/
theorem uEvenBranchHistoryWriteStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.scratchABit n counterWidth).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (RegisterBits.scratchABit n counterWidth).get x := by
  rw [uEvenBranchHistoryWriteStep_eq]
  let y :=
    activeScratchBToHistoryStep n counterWidth historyIndex
      (uEvenBranchCodeToScratchStep n counterWidth bit x)
  have hcompareAfterWrite :
      (RegisterBits.compareBit n counterWidth).get y = false := by
    dsimp [y]
    rw [activeScratchBToHistoryStep_get_compare]
    exact uEvenBranchCodeToScratchStep_get_compare_clean n counterWidth bit
      x hcompare
  change (RegisterBits.scratchABit n counterWidth).get
      (uEvenBranchCodeToScratchStep n counterWidth bit y) =
    (RegisterBits.scratchABit n counterWidth).get x
  rw [uEvenBranchCodeToScratchStep_get_scratchA_clean n counterWidth bit y
    hcompareAfterWrite]
  dsimp [y]
  rw [activeScratchBToHistoryStep_get_scratchA]
  rw [uEvenBranchCodeToScratchStep_get_scratchA_clean n counterWidth bit x
    hcompare]
  rw [activeScratchBToHistoryStep_get_active]
  rw [uEvenBranchCodeToScratchStep_get_active]
  rw [activeScratchBToHistoryStep_get_uBit]
  rw [uEvenBranchCodeToScratchStep_get_uBit]
  cases (RegisterBits.scratchABit n counterWidth).get x <;>
    cases (RegisterBits.activeBit n counterWidth).get x <;>
      cases (RegisterBits.uBit n counterWidth bit).get x <;> simp

/-- On clean compare, the `uEven` branch-history write slice restores the
second scratch-code bit. -/
theorem uEvenBranchHistoryWriteStep_get_scratchB_clean
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.scratchBBit n counterWidth).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (RegisterBits.scratchBBit n counterWidth).get x := by
  rw [uEvenBranchHistoryWriteStep_eq]
  let y :=
    activeScratchBToHistoryStep n counterWidth historyIndex
      (uEvenBranchCodeToScratchStep n counterWidth bit x)
  have hcompareAfterWrite :
      (RegisterBits.compareBit n counterWidth).get y = false := by
    dsimp [y]
    rw [activeScratchBToHistoryStep_get_compare]
    exact uEvenBranchCodeToScratchStep_get_compare_clean n counterWidth bit
      x hcompare
  change (RegisterBits.scratchBBit n counterWidth).get
      (uEvenBranchCodeToScratchStep n counterWidth bit y) =
    (RegisterBits.scratchBBit n counterWidth).get x
  rw [uEvenBranchCodeToScratchStep_get_scratchB_clean n counterWidth bit y
    hcompareAfterWrite]
  dsimp [y]
  rw [activeScratchBToHistoryStep_get_scratchB]
  rw [uEvenBranchCodeToScratchStep_get_scratchB_clean n counterWidth bit x
    hcompare]

/-- The `uEven` branch-history write slice preserves the active flag. -/
theorem uEvenBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  rw [uEvenBranchHistoryWriteStep_eq]
  rw [uEvenBranchCodeToScratchStep_get_active]
  rw [activeScratchBToHistoryStep_get_active]
  rw [uEvenBranchCodeToScratchStep_get_active]

/-- The `uEven` branch-history write slice preserves the selected `u` bit. -/
theorem uEvenBranchHistoryWriteStep_get_uBit
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.uBit n counterWidth bit).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (RegisterBits.uBit n counterWidth bit).get x := by
  rw [uEvenBranchHistoryWriteStep_eq]
  rw [uEvenBranchCodeToScratchStep_get_uBit]
  rw [activeScratchBToHistoryStep_get_uBit]
  rw [uEvenBranchCodeToScratchStep_get_uBit]

/-- Lifted clean-compare endpoint for the `uEven` branch-history write slice. -/
theorem liftedUEvenBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedCompareBit n counterWidth).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      false := by
  change (RegisterBits.compareBit n counterWidth).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x.1) =
      false
  apply uEvenBranchHistoryWriteStep_get_compare_clean
  change (RegisterBits.compareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- Lifted scratchA restoration endpoint for the `uEven` branch-history write
slice. -/
theorem liftedUEvenBranchHistoryWriteStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedScratchABit n counterWidth).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedScratchABit n counterWidth).get x := by
  change (RegisterBits.scratchABit n counterWidth).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x.1) =
      (RegisterBits.scratchABit n counterWidth).get x.1
  apply uEvenBranchHistoryWriteStep_get_scratchA_clean
  change (RegisterBits.compareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- Lifted scratchB restoration endpoint for the `uEven` branch-history write
slice. -/
theorem liftedUEvenBranchHistoryWriteStep_get_scratchB_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedScratchBBit n counterWidth).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedScratchBBit n counterWidth).get x := by
  change (RegisterBits.scratchBBit n counterWidth).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x.1) =
      (RegisterBits.scratchBBit n counterWidth).get x.1
  apply uEvenBranchHistoryWriteStep_get_scratchB_clean
  change (RegisterBits.compareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- Lifted active-flag preservation endpoint for the `uEven`
branch-history write slice. -/
theorem liftedUEvenBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedActiveBit n counterWidth).get x := by
  change (RegisterBits.activeBit n counterWidth).get
        (uEvenBranchHistoryWriteStep n counterWidth bit historyIndex x.1) =
      (RegisterBits.activeBit n counterWidth).get x.1
  exact uEvenBranchHistoryWriteStep_get_active n counterWidth bit historyIndex
    x.1

/-- Lifted selected-`u` preservation endpoint for the `uEven`
branch-history write slice. -/
theorem liftedUEvenBranchHistoryWriteStep_get_uBit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedUBit n counterWidth bit).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedUBit n counterWidth bit).get x := by
  simpa [liftedUBit, liftedUEvenBranchHistoryWriteStep,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit] using
    uEvenBranchHistoryWriteStep_get_uBit n counterWidth bit historyIndex x.1

/-! ## `v`-even condition staging -/

/-- Gate list that toggles the comparison ancilla exactly when one selected
`v` bit is zero, restoring the selected `v` bit afterward.  This is the
single-bit zero-test atom used by the later all-zero detector. -/
def vBitNotToCompareGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  [ EncodedBit.GateSpec.x (RegisterBits.vBit n counterWidth bit)
  , EncodedBit.GateSpec.cnot
      (RegisterBits.vBit n counterWidth bit)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.v_compare_wire_ne n counterWidth bit)
  , EncodedBit.GateSpec.x (RegisterBits.vBit n counterWidth bit) ]

/-- Base-gate program for the single-bit `v = 0` detector atom. -/
def vBitNotToCompareProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (vBitNotToCompareGates n counterWidth bit)

/-- Semantic step for the single-bit `v = 0` detector atom. -/
def vBitNotToCompareStep
    (n counterWidth : Nat) (bit : Fin n) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (vBitNotToCompareGates n counterWidth bit)

/-- The single-bit `v = 0` detector atom is a concrete encoded-bit base-gate
realization over the Montgomery--Kaliski register layout. -/
theorem vBitNotToCompare_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (vBitNotToCompareProgram n counterWidth bit)
      (vBitNotToCompareStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (vBitNotToCompareGates n counterWidth bit)

/-- The single-bit detector toggles compare by the negated selected `v` bit. -/
theorem vBitNotToCompareStep_get_compare
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.compareBit n counterWidth).get
        (vBitNotToCompareStep n counterWidth bit x) =
      ((RegisterBits.compareBit n counterWidth).get x ^^
        !(RegisterBits.vBit n counterWidth bit).get x) := by
  let sourceV := RegisterBits.vBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  change compare.get
      (sourceV.flip
        (EncodedBit.cnotStep sourceV compare (sourceV.flip x))) =
    (compare.get x ^^ !sourceV.get x)
  rw [EncodedBit.get_flip_of_wire_ne sourceV compare
    (RegisterBits.v_compare_wire_ne n counterWidth bit)]
  rw [EncodedBit.cnotStep_get_target]
  rw [EncodedBit.get_flip_of_wire_ne sourceV compare
    (RegisterBits.v_compare_wire_ne n counterWidth bit)]
  rw [EncodedBit.get_flip_self]

/-- On clean compare, the single-bit detector writes the negated selected
`v` bit into compare. -/
theorem vBitNotToCompareStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hclean : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.compareBit n counterWidth).get
        (vBitNotToCompareStep n counterWidth bit x) =
      !(RegisterBits.vBit n counterWidth bit).get x := by
  rw [vBitNotToCompareStep_get_compare]
  have hcleanValue : x.compare = false := by
    simpa using hclean
  cases (RegisterBits.vBit n counterWidth bit).get x <;> simp [hcleanValue]

/-- The single-bit detector restores the selected `v` bit. -/
theorem vBitNotToCompareStep_get_vBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vBit n counterWidth bit).get
        (vBitNotToCompareStep n counterWidth bit x) =
      (RegisterBits.vBit n counterWidth bit).get x := by
  let sourceV := RegisterBits.vBit n counterWidth bit
  let compare := RegisterBits.compareBit n counterWidth
  change sourceV.get
      (sourceV.flip
        (EncodedBit.cnotStep sourceV compare (sourceV.flip x))) =
    sourceV.get x
  rw [EncodedBit.get_flip_self]
  rw [EncodedBit.cnotStep_get_of_target_ne sourceV compare sourceV
    (Ne.symm (RegisterBits.v_compare_wire_ne n counterWidth bit))]
  rw [EncodedBit.get_flip_self]
  cases sourceV.get x <;> simp

/-- The single-bit detector restores every little-endian `v` value bit. -/
theorem vBitNotToCompareStep_get_vValueBit
    (n counterWidth : Nat) (bit targetBit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vValueBit n counterWidth targetBit).get
        (vBitNotToCompareStep n counterWidth bit x) =
      (RegisterBits.vValueBit n counterWidth targetBit).get x := by
  by_cases htarget : WireAddress.littleEndianWire targetBit = bit
  · simpa [RegisterBits.vValueBit, htarget] using
      vBitNotToCompareStep_get_vBit n counterWidth bit x
  · let sourceV := RegisterBits.vBit n counterWidth bit
    let compare := RegisterBits.compareBit n counterWidth
    let observed := RegisterBits.vValueBit n counterWidth targetBit
    have hsourceVObserved : sourceV.wire ≠ observed.wire := by
      simpa [sourceV, observed, RegisterBits.vValueBit] using
        v_v_wire_ne n counterWidth bit
          (WireAddress.littleEndianWire targetBit) (Ne.symm htarget)
    have hcompareObserved : compare.wire ≠ observed.wire := by
      simpa [compare, observed, RegisterBits.vValueBit] using
        Ne.symm (RegisterBits.v_compare_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit))
    change observed.get
        (sourceV.flip
          (EncodedBit.cnotStep sourceV compare (sourceV.flip x))) =
      observed.get x
    rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]
    rw [EncodedBit.cnotStep_get_of_target_ne sourceV compare observed
      hcompareObserved]
    rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]

/-- The single-bit detector restores the full `v` word. -/
theorem vBitNotToCompareStep_v
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (vBitNotToCompareStep n counterWidth bit x).v = x.v := by
  apply word_eq_of_testBit_eq
  intro targetBit
  simpa [RegisterBits.vValueBit_get] using
    vBitNotToCompareStep_get_vValueBit n counterWidth bit targetBit x

/-- In width one, the single-bit detector is the complete `v = 0` detector. -/
theorem vBitNotToCompareStep_get_compare_clean_one
    (counterWidth : Nat) (x : Registers 1 counterWidth)
    (hclean : (RegisterBits.compareBit 1 counterWidth).get x = false) :
    (RegisterBits.compareBit 1 counterWidth).get
        (vBitNotToCompareStep 1 counterWidth 0 x) =
      decide (x.v.val = 0) := by
  rw [vBitNotToCompareStep_get_compare_clean 1 counterWidth 0 x hclean]
  have hwire : WireAddress.bitIndex (0 : Fin 1) = (0 : Fin 1) := by
    apply Fin.ext
    simp [WireAddress.bitIndex]
  have hbit :
      (RegisterBits.vBit 1 counterWidth 0).get x =
        x.v.val.testBit 0 := by
    simpa [RegisterBits.vValueBit, WireAddress.littleEndianWire, hwire] using
      RegisterBits.vValueBit_get 1 counterWidth 0 x
  rw [hbit]
  have hlt := x.v.isLt
  have hcases : x.v.val = 0 ∨ x.v.val = 1 := by omega
  rcases hcases with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- Distinct lifted comparison-work carry bits occupy distinct wires. -/
theorem liftedComparisonCarry_liftedComparisonCarry_wire_ne
    (n counterWidth : Nat) (left right : Fin n) (h : left ≠ right) :
    (liftedComparisonCarryBit n counterWidth left).wire ≠
      (liftedComparisonCarryBit n counterWidth right).wire := by
  exact liftComparisonWorkBit_liftComparisonWorkBit_wire_ne n counterWidth
    (comparisonCarryValueBit n left) (comparisonCarryValueBit n right)
    (comparisonCarryValue_comparisonCarryValue_wire_ne n left right h)

private def encodedWordXIndicesStep
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (word : EncodedBit.Word encoding width) (indices : List (Fin width)) :
    Data -> Data :=
  fun x => indices.foldl (fun y bit => (word.bit bit).flip y) x

private theorem encodedWordXIndicesStep_get_bit
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (word : EncodedBit.Word encoding width) (indices : List (Fin width))
    (hnodup : indices.Nodup) (bit : Fin width)
    (hword :
      ∀ left right : Fin width,
        left ≠ right -> (word.bit left).wire ≠ (word.bit right).wire)
    (x : Data) :
    (word.bit bit).get (encodedWordXIndicesStep word indices x) =
      ((word.bit bit).get x ^^ decide (bit ∈ indices)) := by
  induction indices generalizing x with
  | nil =>
      simp [encodedWordXIndicesStep]
  | cons head rest ih =>
      have hrestNodup : rest.Nodup := hnodup.tail
      have hheadNotMem : head ∉ rest := hnodup.notMem
      unfold encodedWordXIndicesStep at *
      change
        (word.bit bit).get
            (rest.foldl (fun y bit => (word.bit bit).flip y)
              ((word.bit head).flip x)) =
          ((word.bit bit).get x ^^ decide (bit ∈ head :: rest))
      by_cases hhead : head = bit
      · subst head
        rw [ih hrestNodup ((word.bit bit).flip x)]
        rw [EncodedBit.get_flip_self]
        simp [hheadNotMem]
      · rw [ih hrestNodup ((word.bit head).flip x)]
        have hget :
            (word.bit bit).get ((word.bit head).flip x) =
              (word.bit bit).get x := by
          rw [EncodedBit.get_flip_of_wire_ne (word.bit head) (word.bit bit)
            (hword head bit hhead)]
        rw [hget]
        have hbitHead : bit ≠ head := Ne.symm hhead
        by_cases hmem : bit ∈ rest <;> simp [hbitHead, hmem]

private theorem encodedWordXGateList_stepList_eq_indicesStep
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (word : EncodedBit.Word encoding width) :
    EncodedBit.GateSpec.stepList
        (List.ofFn fun bit : Fin width =>
          EncodedBit.GateSpec.x (word.bit bit)) =
      encodedWordXIndicesStep word (List.ofFn fun bit : Fin width => bit) := by
  funext x
  rw [EncodedBit.GateSpec.stepList_eq_foldl, encodedWordXIndicesStep]
  let gateOfIndex : Fin width -> EncodedBit.GateSpec encoding := fun bit =>
    EncodedBit.GateSpec.x (word.bit bit)
  change
    List.foldl (fun y gate => gate.step y) x (List.ofFn gateOfIndex) =
      List.foldl (fun y bit => (word.bit bit).flip y) x
        (List.ofFn fun bit : Fin width => bit)
  rw [show List.ofFn gateOfIndex =
      (List.ofFn fun bit : Fin width => bit).map gateOfIndex by
        simpa [gateOfIndex] using
          (List.ofFn_comp' (fun bit : Fin width => bit) gateOfIndex)]
  generalize List.ofFn (fun bit : Fin width => bit) = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons bit rest ih =>
      simpa [gateOfIndex, EncodedBit.GateSpec.step] using
        ih ((word.bit bit).flip x)

private theorem encodedWordXGateList_reverse_stepList_eq_indicesStep
    {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
    (word : EncodedBit.Word encoding width) :
    EncodedBit.GateSpec.stepList
        (List.ofFn fun bit : Fin width =>
          EncodedBit.GateSpec.x (word.bit bit)).reverse =
      encodedWordXIndicesStep word (List.ofFn fun bit : Fin width => bit).reverse := by
  funext x
  rw [EncodedBit.GateSpec.stepList_eq_foldl, encodedWordXIndicesStep]
  let gateOfIndex : Fin width -> EncodedBit.GateSpec encoding := fun bit =>
    EncodedBit.GateSpec.x (word.bit bit)
  change
    List.foldl (fun y gate => gate.step y) x (List.ofFn gateOfIndex).reverse =
      List.foldl (fun y bit => (word.bit bit).flip y) x
        (List.ofFn fun bit : Fin width => bit).reverse
  rw [show List.ofFn gateOfIndex =
      (List.ofFn fun bit : Fin width => bit).map gateOfIndex by
        simpa [gateOfIndex] using
          (List.ofFn_comp' (fun bit : Fin width => bit) gateOfIndex)]
  rw [← List.map_reverse]
  generalize (List.ofFn fun bit : Fin width => bit).reverse = indices
  induction indices generalizing x with
  | nil =>
      rfl
  | cons bit rest ih =>
      simpa [gateOfIndex, EncodedBit.GateSpec.step] using
        ih ((word.bit bit).flip x)

/-- Gate list flipping every lifted `v` value bit.  This lets the following
prefix network compute an AND of `!v_i` with positive Toffoli controls. -/
def vZeroDetectorNegateVGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  List.ofFn fun bit : Fin n =>
    EncodedBit.GateSpec.x ((liftedVWord n counterWidth).bit bit)

/-- The `v`-negation gate list flips exactly the selected lifted `v` bit. -/
theorem vZeroDetectorNegateVGates_get_vValueBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit bit).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorNegateVGates n counterWidth) x) =
      !((liftedVWord n counterWidth).bit bit).get x := by
  rw [vZeroDetectorNegateVGates,
    encodedWordXGateList_stepList_eq_indicesStep]
  have hnodup : (List.ofFn fun bit : Fin n => bit).Nodup :=
    List.nodup_ofFn_ofInjective (fun _ _ h => h)
  have hmem : bit ∈ (List.ofFn fun other : Fin n => other) :=
    List.mem_ofFn.mpr ⟨bit, rfl⟩
  simpa [hmem] using
    encodedWordXIndicesStep_get_bit (liftedVWord n counterWidth)
      (List.ofFn fun other : Fin n => other) hnodup bit
      (fun left right h =>
        liftedVWordBit_liftedVWordBit_wire_ne n counterWidth left right h)
      x

/-- The reversed `v`-negation gate list also flips exactly the selected lifted
`v` bit. -/
theorem vZeroDetectorNegateVGates_reverse_get_vValueBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit bit).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorNegateVGates n counterWidth).reverse x) =
      !((liftedVWord n counterWidth).bit bit).get x := by
  rw [vZeroDetectorNegateVGates,
    encodedWordXGateList_reverse_stepList_eq_indicesStep]
  have hnodup : ((List.ofFn fun bit : Fin n => bit).reverse).Nodup :=
    List.nodup_reverse.mpr
      (List.nodup_ofFn_ofInjective (fun _ _ h => h))
  have hmem : bit ∈ (List.ofFn fun other : Fin n => other).reverse := by
    simp
  simpa [hmem] using
    encodedWordXIndicesStep_get_bit (liftedVWord n counterWidth)
      (List.ofFn fun other : Fin n => other).reverse hnodup bit
      (fun left right h =>
        liftedVWordBit_liftedVWordBit_wire_ne n counterWidth left right h)
      x

/-- Clean comparison work has all lifted carry bits clear. -/
@[simp] theorem liftedComparisonCarryBit_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (x, cleanComparisonWork n) = false := by
  change (comparisonCarryValueBit n bit).get (cleanComparisonWork n) = false
  simp

/-- The `v`-negation gate list preserves every comparison-work carry readout. -/
theorem vZeroDetectorNegateVGates_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorNegateVGates n counterWidth) x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [vZeroDetectorNegateVGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨bit, rfl⟩
  intro y
  exact EncodedBit.get_flip_of_wire_ne
    ((liftedVWord n counterWidth).bit bit)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth bit workBit)
    y

/-- The reversed `v`-negation gate list preserves every comparison-work carry
readout. -/
theorem vZeroDetectorNegateVGates_reverse_get_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorNegateVGates n counterWidth).reverse x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hmem : gate ∈ vZeroDetectorNegateVGates n counterWidth :=
    List.mem_reverse.mp hgate
  rw [vZeroDetectorNegateVGates] at hmem
  rcases List.mem_ofFn.mp hmem with ⟨bit, rfl⟩
  intro y
  exact EncodedBit.get_flip_of_wire_ne
    ((liftedVWord n counterWidth).bit bit)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth bit workBit)
    y

/-- The `v`-negation gate list preserves compare. -/
theorem vZeroDetectorNegateVGates_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorNegateVGates n counterWidth) x) =
      (liftedCompareBit n counterWidth).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [vZeroDetectorNegateVGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨bit, rfl⟩
  intro y
  exact EncodedBit.get_flip_of_wire_ne
    ((liftedVWord n counterWidth).bit bit)
    (liftedCompareBit n counterWidth)
    (Ne.symm (liftedCompare_liftedVWordBit_wire_ne n counterWidth bit)) y

/-- The reversed `v`-negation gate list preserves compare. -/
theorem vZeroDetectorNegateVGates_reverse_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorNegateVGates n counterWidth).reverse x) =
      (liftedCompareBit n counterWidth).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hmem : gate ∈ vZeroDetectorNegateVGates n counterWidth :=
    List.mem_reverse.mp hgate
  rw [vZeroDetectorNegateVGates] at hmem
  rcases List.mem_ofFn.mp hmem with ⟨bit, rfl⟩
  intro y
  exact EncodedBit.get_flip_of_wire_ne
    ((liftedVWord n counterWidth).bit bit)
    (liftedCompareBit n counterWidth)
    (Ne.symm (liftedCompare_liftedVWordBit_wire_ne n counterWidth bit)) y

/-- Forward prefix-AND network for a nonempty `v = 0` detector.  After all
`v` bits have been flipped, it computes the running conjunction into the
comparison carry-work word. -/
def vZeroDetectorPrefixGates (tail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding tail.succ counterWidth)) :=
  [ EncodedBit.GateSpec.cnot
      ((liftedVWord tail.succ counterWidth).bit 0)
      (liftedComparisonCarryBit tail.succ counterWidth 0)
      (liftedVWordBit_liftedComparisonCarry_wire_ne tail.succ counterWidth 0 0)
  ] ++
  (List.ofFn fun bit : Fin tail =>
    EncodedBit.GateSpec.toffoli
      (liftedComparisonCarryBit tail.succ counterWidth (Fin.castSucc bit))
      ((liftedVWord tail.succ counterWidth).bit (Fin.succ bit))
      (liftedComparisonCarryBit tail.succ counterWidth (Fin.succ bit))
      (Ne.symm
        (liftedVWordBit_liftedComparisonCarry_wire_ne tail.succ counterWidth
          (Fin.succ bit) (Fin.castSucc bit)))
      (liftedComparisonCarry_liftedComparisonCarry_wire_ne tail.succ
        counterWidth (Fin.castSucc bit) (Fin.succ bit) (by
          intro h
          have hval := congrArg Fin.val h
          simp at hval))
      (liftedVWordBit_liftedComparisonCarry_wire_ne tail.succ counterWidth
        (Fin.succ bit) (Fin.succ bit)))

private def vZeroDetectorPrefixUntilIndex (n upto : Nat) (h : upto < n)
    (bit : Fin upto.succ) : Fin n :=
  ⟨bit.val, by omega⟩

private def vZeroDetectorPrefixUntilPrevIndex (n upto : Nat) (h : upto < n)
    (bit : Fin upto) : Fin n :=
  ⟨bit.val, by omega⟩

private def vZeroDetectorPrefixUntilNextIndex (n upto : Nat) (h : upto < n)
    (bit : Fin upto) : Fin n :=
  ⟨bit.val + 1, by omega⟩

private theorem vZeroDetectorPrefixUntilPrevIndex_ne_nextIndex
    (n upto : Nat) (h : upto < n) (bit : Fin upto) :
    vZeroDetectorPrefixUntilPrevIndex n upto h bit ≠
      vZeroDetectorPrefixUntilNextIndex n upto h bit := by
  intro hidx
  have hval := congrArg Fin.val hidx
  simp [vZeroDetectorPrefixUntilPrevIndex,
    vZeroDetectorPrefixUntilNextIndex] at hval

private def vZeroDetectorPrefixGatesUntil
    (n counterWidth upto : Nat) (h : upto < n) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  [ EncodedBit.GateSpec.cnot
      ((liftedVWord n counterWidth).bit
        (vZeroDetectorPrefixUntilIndex n upto h 0))
      (liftedComparisonCarryBit n counterWidth
        (vZeroDetectorPrefixUntilIndex n upto h 0))
      (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth
        (vZeroDetectorPrefixUntilIndex n upto h 0)
        (vZeroDetectorPrefixUntilIndex n upto h 0))
  ] ++
  (List.ofFn fun bit : Fin upto =>
    EncodedBit.GateSpec.toffoli
      (liftedComparisonCarryBit n counterWidth
        (vZeroDetectorPrefixUntilPrevIndex n upto h bit))
      ((liftedVWord n counterWidth).bit
        (vZeroDetectorPrefixUntilNextIndex n upto h bit))
      (liftedComparisonCarryBit n counterWidth
        (vZeroDetectorPrefixUntilNextIndex n upto h bit))
      (Ne.symm
        (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth
          (vZeroDetectorPrefixUntilNextIndex n upto h bit)
          (vZeroDetectorPrefixUntilPrevIndex n upto h bit)))
      (liftedComparisonCarry_liftedComparisonCarry_wire_ne n counterWidth
        (vZeroDetectorPrefixUntilPrevIndex n upto h bit)
        (vZeroDetectorPrefixUntilNextIndex n upto h bit)
        (vZeroDetectorPrefixUntilPrevIndex_ne_nextIndex n upto h bit))
      (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth
        (vZeroDetectorPrefixUntilNextIndex n upto h bit)
        (vZeroDetectorPrefixUntilNextIndex n upto h bit)))

private theorem vZeroDetectorPrefixGates_eq_until
    (tail counterWidth : Nat) :
    vZeroDetectorPrefixGates tail counterWidth =
      vZeroDetectorPrefixGatesUntil tail.succ counterWidth tail
        (Nat.lt_succ_self tail) := by
  rfl

private def vZeroDetectorPrefixRead
    (n counterWidth upto : Nat) (h : upto < n)
    (x : RegistersWithComparisonWork n counterWidth) : Bool :=
  (List.ofFn fun bit : Fin upto.succ =>
    ((liftedVWord n counterWidth).bit
      (vZeroDetectorPrefixUntilIndex n upto h bit)).get x).all id

private theorem vZeroDetectorPrefixRead_succ
    (n counterWidth upto : Nat) (h : upto.succ < n)
    (x : RegistersWithComparisonWork n counterWidth) :
    vZeroDetectorPrefixRead n counterWidth upto.succ h x =
      (vZeroDetectorPrefixRead n counterWidth upto (by omega) x &&
        ((liftedVWord n counterWidth).bit
          (vZeroDetectorPrefixUntilNextIndex n upto.succ h
            (Fin.last upto))).get x) := by
  rw [vZeroDetectorPrefixRead, vZeroDetectorPrefixRead]
  rw [List.ofFn_succ']
  simp [vZeroDetectorPrefixUntilIndex, vZeroDetectorPrefixUntilNextIndex,
    Bool.and_assoc]

private theorem vZeroDetectorPrefixRead_eq_decide
    (n counterWidth upto : Nat) (h : upto < n)
    (x : RegistersWithComparisonWork n counterWidth) :
    vZeroDetectorPrefixRead n counterWidth upto h x =
      decide
        (∀ bit : Fin upto.succ,
          ((liftedVWord n counterWidth).bit
            (vZeroDetectorPrefixUntilIndex n upto h bit)).get x = true) := by
  by_cases hall :
      ∀ bit : Fin upto.succ,
        ((liftedVWord n counterWidth).bit
          (vZeroDetectorPrefixUntilIndex n upto h bit)).get x = true
  · have hprefix :
        vZeroDetectorPrefixRead n counterWidth upto h x = true := by
      rw [vZeroDetectorPrefixRead, List.all_eq_true]
      intro value hmem
      rcases List.mem_ofFn.mp hmem with ⟨bit, rfl⟩
      exact hall bit
    simp [hprefix, hall]
  · have hprefix :
        vZeroDetectorPrefixRead n counterWidth upto h x = false := by
      rw [vZeroDetectorPrefixRead, List.all_eq_false]
      push Not at hall
      rcases hall with ⟨bit, hbit⟩
      exact ⟨((liftedVWord n counterWidth).bit
          (vZeroDetectorPrefixUntilIndex n upto h bit)).get x,
        List.mem_ofFn.mpr ⟨bit, rfl⟩, hbit⟩
    simp [hprefix, hall]

private theorem vZeroDetectorPrefixGatesUntil_get_vValueBit
    (n counterWidth upto : Nat) (h : upto < n) (target : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit target).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGatesUntil n counterWidth upto h) x) =
      ((liftedVWord n counterWidth).bit target).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [vZeroDetectorPrefixGatesUntil] at hgate
  simp only [List.mem_append, List.mem_singleton] at hgate
  rcases hgate with hfirst | hrest
  · subst gate
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      (liftedComparisonCarryBit n counterWidth
        (vZeroDetectorPrefixUntilIndex n upto h 0))
      ((liftedVWord n counterWidth).bit target)
      (Ne.symm
        (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth
          target (vZeroDetectorPrefixUntilIndex n upto h 0))) y
  · rcases List.mem_ofFn.mp hrest with ⟨bit, rfl⟩
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      (liftedComparisonCarryBit n counterWidth
        (vZeroDetectorPrefixUntilNextIndex n upto h bit))
      ((liftedVWord n counterWidth).bit target)
      (Ne.symm
        (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth
          target (vZeroDetectorPrefixUntilNextIndex n upto h bit))) y

private theorem vZeroDetectorPrefixGatesUntil_get_later_comparisonCarry
    (n counterWidth upto : Nat) (h : upto < n) (target : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hlater : upto < target.val) :
    (liftedComparisonCarryBit n counterWidth target).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGatesUntil n counterWidth upto h) x) =
      (liftedComparisonCarryBit n counterWidth target).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [vZeroDetectorPrefixGatesUntil] at hgate
  simp only [List.mem_append, List.mem_singleton] at hgate
  rcases hgate with hfirst | hrest
  · subst gate
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      (liftedComparisonCarryBit n counterWidth
        (vZeroDetectorPrefixUntilIndex n upto h 0))
      (liftedComparisonCarryBit n counterWidth target)
      (liftedComparisonCarry_liftedComparisonCarry_wire_ne n counterWidth
        (vZeroDetectorPrefixUntilIndex n upto h 0) target
        (by
          apply Fin.ne_of_val_ne
          simp [vZeroDetectorPrefixUntilIndex]
          omega)) y
  · rcases List.mem_ofFn.mp hrest with ⟨bit, rfl⟩
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      (liftedComparisonCarryBit n counterWidth
        (vZeroDetectorPrefixUntilNextIndex n upto h bit))
      (liftedComparisonCarryBit n counterWidth target)
      (liftedComparisonCarry_liftedComparisonCarry_wire_ne n counterWidth
        (vZeroDetectorPrefixUntilNextIndex n upto h bit) target
        (by
          apply Fin.ne_of_val_ne
          simp [vZeroDetectorPrefixUntilNextIndex]
          omega)) y

private def vZeroDetectorPrefixGatesUntilSuccGate
    (n counterWidth upto : Nat) (h : upto.succ < n) :
    EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth) :=
  EncodedBit.GateSpec.toffoli
    (liftedComparisonCarryBit n counterWidth
      (vZeroDetectorPrefixUntilPrevIndex n upto.succ h (Fin.last upto)))
    ((liftedVWord n counterWidth).bit
      (vZeroDetectorPrefixUntilNextIndex n upto.succ h (Fin.last upto)))
    (liftedComparisonCarryBit n counterWidth
      (vZeroDetectorPrefixUntilNextIndex n upto.succ h (Fin.last upto)))
    (Ne.symm
      (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth
        (vZeroDetectorPrefixUntilNextIndex n upto.succ h (Fin.last upto))
        (vZeroDetectorPrefixUntilPrevIndex n upto.succ h (Fin.last upto))))
    (liftedComparisonCarry_liftedComparisonCarry_wire_ne n counterWidth
      (vZeroDetectorPrefixUntilPrevIndex n upto.succ h (Fin.last upto))
      (vZeroDetectorPrefixUntilNextIndex n upto.succ h (Fin.last upto))
      (vZeroDetectorPrefixUntilPrevIndex_ne_nextIndex n upto.succ h
        (Fin.last upto)))
    (liftedVWordBit_liftedComparisonCarry_wire_ne n counterWidth
      (vZeroDetectorPrefixUntilNextIndex n upto.succ h (Fin.last upto))
      (vZeroDetectorPrefixUntilNextIndex n upto.succ h (Fin.last upto)))

private theorem vZeroDetectorPrefixGatesUntil_succ
    (n counterWidth upto : Nat) (h : upto.succ < n) :
    vZeroDetectorPrefixGatesUntil n counterWidth upto.succ h =
      vZeroDetectorPrefixGatesUntil n counterWidth upto (by omega) ++
        [vZeroDetectorPrefixGatesUntilSuccGate n counterWidth upto h] := by
  rw [vZeroDetectorPrefixGatesUntil, vZeroDetectorPrefixGatesUntil,
    vZeroDetectorPrefixGatesUntilSuccGate]
  rw [List.ofFn_succ']
  simp [vZeroDetectorPrefixUntilIndex,
    vZeroDetectorPrefixUntilPrevIndex, vZeroDetectorPrefixUntilNextIndex]

private theorem vZeroDetectorPrefixGatesUntil_get_final_clean
    (n counterWidth upto : Nat) (h : upto < n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hwork :
      ∀ bit : Fin n,
        (liftedComparisonCarryBit n counterWidth bit).get x = false) :
    (liftedComparisonCarryBit n counterWidth
        (vZeroDetectorPrefixUntilIndex n upto h (Fin.last upto))).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGatesUntil n counterWidth upto h) x) =
      vZeroDetectorPrefixRead n counterWidth upto h x := by
  induction upto with
  | zero =>
      rw [vZeroDetectorPrefixGatesUntil, vZeroDetectorPrefixRead]
      simp only [List.ofFn_zero, List.append_nil,
        EncodedBit.GateSpec.stepList, id_eq]
      simp only [EncodedBit.GateSpec.step]
      have hlast :
          vZeroDetectorPrefixUntilIndex n 0 h (Fin.last 0) =
            vZeroDetectorPrefixUntilIndex n 0 h 0 := by
        apply Fin.ext
        simp [vZeroDetectorPrefixUntilIndex]
      rw [hlast]
      rw [List.ofFn_succ']
      simp only [List.ofFn_zero]
      rw [hlast]
      rw [EncodedBit.cnotStep_get_target]
      have hclean := hwork (vZeroDetectorPrefixUntilIndex n 0 h 0)
      rw [hclean]
      cases hv :
          ((liftedVWord n counterWidth).bit
            (vZeroDetectorPrefixUntilIndex n 0 h 0)).get x <;>
        simp
  | succ upto ih =>
      let hprev : upto < n := by omega
      let prev :=
        vZeroDetectorPrefixUntilPrevIndex n upto.succ h (Fin.last upto)
      let next :=
        vZeroDetectorPrefixUntilNextIndex n upto.succ h (Fin.last upto)
      let y :=
        EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGatesUntil n counterWidth upto hprev) x
      have htargetClean :
          (liftedComparisonCarryBit n counterWidth next).get y = false := by
        dsimp [y, next]
        rw [vZeroDetectorPrefixGatesUntil_get_later_comparisonCarry
          n counterWidth upto hprev
          (vZeroDetectorPrefixUntilNextIndex n upto.succ h (Fin.last upto)) x
          (by
            simp [vZeroDetectorPrefixUntilNextIndex])]
        exact hwork (vZeroDetectorPrefixUntilNextIndex n upto.succ h
          (Fin.last upto))
      have hprevCarry :
          (liftedComparisonCarryBit n counterWidth prev).get y =
            vZeroDetectorPrefixRead n counterWidth upto hprev x := by
        dsimp [prev, y]
        simpa [vZeroDetectorPrefixUntilPrevIndex,
          vZeroDetectorPrefixUntilIndex] using ih hprev
      have hvNext :
          ((liftedVWord n counterWidth).bit next).get y =
            ((liftedVWord n counterWidth).bit next).get x := by
        dsimp [y]
        exact vZeroDetectorPrefixGatesUntil_get_vValueBit
          n counterWidth upto hprev next x
      rw [vZeroDetectorPrefixGatesUntil_succ]
      rw [EncodedBit.GateSpec.stepList_append]
      change (liftedComparisonCarryBit n counterWidth next).get
          ((vZeroDetectorPrefixGatesUntilSuccGate n counterWidth upto h).step
            y) =
        vZeroDetectorPrefixRead n counterWidth upto.succ h x
      rw [vZeroDetectorPrefixGatesUntilSuccGate]
      change (liftedComparisonCarryBit n counterWidth next).get
          (EncodedBit.toffoliStep
            (liftedComparisonCarryBit n counterWidth prev)
            ((liftedVWord n counterWidth).bit next)
            (liftedComparisonCarryBit n counterWidth next) y) =
        vZeroDetectorPrefixRead n counterWidth upto.succ h x
      rw [EncodedBit.toffoliStep_get_target]
      rw [htargetClean, hprevCarry, hvNext]
      rw [vZeroDetectorPrefixRead_succ]
      simp [next, vZeroDetectorPrefixUntilNextIndex]

private theorem vZeroDetectorPrefixGates_get_final_clean
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth)
    (hwork :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get x =
          false) :
    (liftedComparisonCarryBit tail.succ counterWidth (Fin.last tail)).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGates tail counterWidth) x) =
      vZeroDetectorPrefixRead tail.succ counterWidth tail
        (Nat.lt_succ_self tail) x := by
  rw [vZeroDetectorPrefixGates_eq_until]
  have hlast :
      vZeroDetectorPrefixUntilIndex tail.succ tail
          (Nat.lt_succ_self tail) (Fin.last tail) =
        Fin.last tail := by
    apply Fin.ext
    simp [vZeroDetectorPrefixUntilIndex, Fin.last]
  simpa [hlast] using
    vZeroDetectorPrefixGatesUntil_get_final_clean tail.succ counterWidth tail
      (Nat.lt_succ_self tail) x hwork

private theorem vZeroDetectorPrefixRead_after_negate_eq_decide_v_zero
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    vZeroDetectorPrefixRead tail.succ counterWidth tail
        (Nat.lt_succ_self tail)
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorNegateVGates tail.succ counterWidth) x) =
      decide (x.1.v.val = 0) := by
  rw [vZeroDetectorPrefixRead_eq_decide]
  by_cases hzero : x.1.v.val = 0
  · have hguard :=
      vZeroGuard_of_v_zero tail.succ counterWidth x.1 hzero
    have hall :
        ∀ bit : Fin tail.succ,
          ((liftedVWord tail.succ counterWidth).bit
              (vZeroDetectorPrefixUntilIndex tail.succ tail
                (Nat.lt_succ_self tail) bit)).get
              (EncodedBit.GateSpec.stepList
                (vZeroDetectorNegateVGates tail.succ counterWidth) x) =
            true := by
      intro bit
      have hidx :
          vZeroDetectorPrefixUntilIndex tail.succ tail
              (Nat.lt_succ_self tail) bit =
            bit := by
        apply Fin.ext
        simp [vZeroDetectorPrefixUntilIndex]
      rw [hidx]
      rw [vZeroDetectorNegateVGates_get_vValueBit]
      have hvfalse :
          ((liftedVWord tail.succ counterWidth).bit bit).get x = false := by
        change
          (RegisterBits.vValueBit tail.succ counterWidth bit).get x.1 =
            false
        exact hguard bit
      rw [hvfalse]
      simp
    simp [hall, hzero]
  · have hnotHall :
        ¬ ∀ bit : Fin tail.succ,
          ((liftedVWord tail.succ counterWidth).bit
              (vZeroDetectorPrefixUntilIndex tail.succ tail
                (Nat.lt_succ_self tail) bit)).get
              (EncodedBit.GateSpec.stepList
                (vZeroDetectorNegateVGates tail.succ counterWidth) x) =
            true := by
      intro hall
      apply hzero
      apply v_zero_of_vZeroGuard tail.succ counterWidth x.1
      intro bit
      have hidx :
          vZeroDetectorPrefixUntilIndex tail.succ tail
              (Nat.lt_succ_self tail) bit =
            bit := by
        apply Fin.ext
        simp [vZeroDetectorPrefixUntilIndex]
      have hread := hall bit
      rw [hidx] at hread
      rw [vZeroDetectorNegateVGates_get_vValueBit] at hread
      cases hv :
          ((liftedVWord tail.succ counterWidth).bit bit).get x
      · change
          (RegisterBits.vValueBit tail.succ counterWidth bit).get x.1 =
            false
        simpa [liftedVWord, liftRegisterBitToComparisonWork,
          BinaryLabelEncoding.prodLeftBit] using hv
      · simp [hv] at hread
    simp [hnotHall, hzero]

/-- The forward prefix-AND network only writes comparison-work carry bits, so it
preserves every lifted `v` value-bit readout. -/
theorem vZeroDetectorPrefixGates_get_vValueBit
    (tail counterWidth : Nat) (target : Fin tail.succ)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    ((liftedVWord tail.succ counterWidth).bit target).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGates tail counterWidth) x) =
      ((liftedVWord tail.succ counterWidth).bit target).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  rw [vZeroDetectorPrefixGates] at hgate
  simp only [List.mem_append, List.mem_singleton] at hgate
  rcases hgate with hfirst | hrest
  · subst gate
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      (liftedComparisonCarryBit tail.succ counterWidth 0)
      ((liftedVWord tail.succ counterWidth).bit target)
      (Ne.symm
        (liftedVWordBit_liftedComparisonCarry_wire_ne tail.succ counterWidth
          target 0)) y
  · rcases List.mem_ofFn.mp hrest with ⟨bit, rfl⟩
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      (liftedComparisonCarryBit tail.succ counterWidth (Fin.succ bit))
      ((liftedVWord tail.succ counterWidth).bit target)
      (Ne.symm
        (liftedVWordBit_liftedComparisonCarry_wire_ne tail.succ counterWidth
          target (Fin.succ bit))) y

/-- Reversing the prefix-AND network still preserves every lifted `v` value-bit
readout. -/
theorem vZeroDetectorPrefixGates_reverse_get_vValueBit
    (tail counterWidth : Nat) (target : Fin tail.succ)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    ((liftedVWord tail.succ counterWidth).bit target).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGates tail counterWidth).reverse x) =
      ((liftedVWord tail.succ counterWidth).bit target).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hmem :
      gate ∈ vZeroDetectorPrefixGates tail counterWidth :=
    List.mem_reverse.mp hgate
  rw [vZeroDetectorPrefixGates] at hmem
  simp only [List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hfirst | hrest
  · subst gate
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      (liftedComparisonCarryBit tail.succ counterWidth 0)
      ((liftedVWord tail.succ counterWidth).bit target)
      (Ne.symm
        (liftedVWordBit_liftedComparisonCarry_wire_ne tail.succ counterWidth
          target 0)) y
  · rcases List.mem_ofFn.mp hrest with ⟨bit, rfl⟩
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      (liftedComparisonCarryBit tail.succ counterWidth (Fin.succ bit))
      ((liftedVWord tail.succ counterWidth).bit target)
      (Ne.symm
        (liftedVWordBit_liftedComparisonCarry_wire_ne tail.succ counterWidth
          target (Fin.succ bit))) y

/-- Every prefix-AND gate is wire-disjoint from the comparison ancilla. -/
theorem vZeroDetectorPrefixGates_bitDisjoint_compare
    (tail counterWidth : Nat) (gate :
      EncodedBit.GateSpec
        (registersWithComparisonWorkEncoding tail.succ counterWidth))
    (hgate : gate ∈ vZeroDetectorPrefixGates tail counterWidth) :
    EncodedBit.GateSpec.bitDisjoint
      (liftedCompareBit tail.succ counterWidth) gate := by
  rw [vZeroDetectorPrefixGates] at hgate
  simp only [List.mem_append, List.mem_singleton] at hgate
  rcases hgate with hfirst | hrest
  · subst gate
    constructor
    · exact Ne.symm
        (liftedCompare_liftedVWordBit_wire_ne tail.succ counterWidth 0)
    · exact Ne.symm
        (liftedCompare_liftedComparisonCarry_wire_ne tail.succ counterWidth 0)
  · rcases List.mem_ofFn.mp hrest with ⟨bit, rfl⟩
    constructor
    · exact Ne.symm
        (liftedCompare_liftedComparisonCarry_wire_ne tail.succ counterWidth
          (Fin.castSucc bit))
    · constructor
      · exact Ne.symm
          (liftedCompare_liftedVWordBit_wire_ne tail.succ counterWidth
            (Fin.succ bit))
      · exact Ne.symm
          (liftedCompare_liftedComparisonCarry_wire_ne tail.succ counterWidth
            (Fin.succ bit))

/-- The forward prefix-AND network preserves compare. -/
theorem vZeroDetectorPrefixGates_get_compare
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (liftedCompareBit tail.succ counterWidth).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGates tail counterWidth) x) =
      (liftedCompareBit tail.succ counterWidth).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hdisjoint :=
    vZeroDetectorPrefixGates_bitDisjoint_compare tail counterWidth gate hgate
  cases gate with
  | x target =>
      exact fun y => EncodedBit.get_flip_of_wire_ne target
        (liftedCompareBit tail.succ counterWidth) hdisjoint y
  | cnot control target hct =>
      exact fun y => EncodedBit.get_flip_of_wire_ne target
        (liftedCompareBit tail.succ counterWidth) hdisjoint.2 y
  | toffoli controlA controlB target hab ha hb =>
      exact fun y => EncodedBit.get_flip_of_wire_ne target
        (liftedCompareBit tail.succ counterWidth) hdisjoint.2.2 y

/-- The reversed prefix-AND network preserves compare. -/
theorem vZeroDetectorPrefixGates_reverse_get_compare
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (liftedCompareBit tail.succ counterWidth).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGates tail counterWidth).reverse x) =
      (liftedCompareBit tail.succ counterWidth).get x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  have hmem : gate ∈ vZeroDetectorPrefixGates tail counterWidth :=
    List.mem_reverse.mp hgate
  have hdisjoint :=
    vZeroDetectorPrefixGates_bitDisjoint_compare tail counterWidth gate hmem
  cases gate with
  | x target =>
      exact fun y => EncodedBit.get_flip_of_wire_ne target
        (liftedCompareBit tail.succ counterWidth) hdisjoint y
  | cnot control target hct =>
      exact fun y => EncodedBit.get_flip_of_wire_ne target
        (liftedCompareBit tail.succ counterWidth) hdisjoint.2 y
  | toffoli controlA controlB target hab ha hb =>
      exact fun y => EncodedBit.get_flip_of_wire_ne target
        (liftedCompareBit tail.succ counterWidth) hdisjoint.2.2 y

/-- Copy the final prefix-AND bit into the comparison ancilla. -/
def vZeroDetectorCopyOutGate (tail counterWidth : Nat) :
    EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding tail.succ counterWidth) :=
  EncodedBit.GateSpec.cnot
    (liftedComparisonCarryBit tail.succ counterWidth (Fin.last tail))
    (liftedCompareBit tail.succ counterWidth)
    (Ne.symm
      (liftedCompare_liftedComparisonCarry_wire_ne tail.succ counterWidth
        (Fin.last tail)))

/-- Copying the detector result into compare preserves every lifted `v`
value-bit readout. -/
theorem vZeroDetectorCopyOutGate_get_vValueBit
    (tail counterWidth : Nat) (target : Fin tail.succ)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    ((liftedVWord tail.succ counterWidth).bit target).get
        ((vZeroDetectorCopyOutGate tail counterWidth).step x) =
      ((liftedVWord tail.succ counterWidth).bit target).get x := by
  simpa [vZeroDetectorCopyOutGate, EncodedBit.GateSpec.step] using
    EncodedBit.cnotStep_get_of_target_ne
      (liftedComparisonCarryBit tail.succ counterWidth (Fin.last tail))
      (liftedCompareBit tail.succ counterWidth)
      ((liftedVWord tail.succ counterWidth).bit target)
      (liftedCompare_liftedVWordBit_wire_ne tail.succ counterWidth target) x

/-- Copying the detector result into compare preserves comparison-work carry
readouts. -/
theorem vZeroDetectorCopyOutGate_get_comparisonCarry
    (tail counterWidth : Nat) (workBit : Fin tail.succ)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (liftedComparisonCarryBit tail.succ counterWidth workBit).get
        ((vZeroDetectorCopyOutGate tail counterWidth).step x) =
      (liftedComparisonCarryBit tail.succ counterWidth workBit).get x := by
  simpa [vZeroDetectorCopyOutGate, EncodedBit.GateSpec.step] using
    EncodedBit.cnotStep_get_of_target_ne
      (liftedComparisonCarryBit tail.succ counterWidth (Fin.last tail))
      (liftedCompareBit tail.succ counterWidth)
      (liftedComparisonCarryBit tail.succ counterWidth workBit)
      (liftedCompare_liftedComparisonCarry_wire_ne tail.succ counterWidth
        workBit) x

/-- Copying the detector result xors the final prefix carry into compare. -/
theorem vZeroDetectorCopyOutGate_get_compare
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (liftedCompareBit tail.succ counterWidth).get
        ((vZeroDetectorCopyOutGate tail counterWidth).step x) =
      ((liftedCompareBit tail.succ counterWidth).get x ^^
        (liftedComparisonCarryBit tail.succ counterWidth (Fin.last tail)).get
          x) := by
  simpa [vZeroDetectorCopyOutGate, EncodedBit.GateSpec.step,
    Bool.xor_comm] using
    EncodedBit.cnotStep_get_target
      (liftedComparisonCarryBit tail.succ counterWidth (Fin.last tail))
      (liftedCompareBit tail.succ counterWidth) x

/-- Prefix compute, compare-copy, and prefix uncompute restore every comparison
carry-work bit.  The compare-copy sits between compute and uncompute, but the
prefix gates are disjoint from compare, so the uncompute still sees the same
`v`/carry controls. -/
theorem vZeroDetectorPrefixCopyUncompute_get_comparisonCarry
    (tail counterWidth : Nat) (workBit : Fin tail.succ)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (liftedComparisonCarryBit tail.succ counterWidth workBit).get
        (EncodedBit.GateSpec.stepList
          (vZeroDetectorPrefixGates tail counterWidth).reverse
          ((vZeroDetectorCopyOutGate tail counterWidth).step
            (EncodedBit.GateSpec.stepList
              (vZeroDetectorPrefixGates tail counterWidth) x))) =
      (liftedComparisonCarryBit tail.succ counterWidth workBit).get x := by
  let prefixGates := vZeroDetectorPrefixGates tail counterWidth
  let carry := liftedComparisonCarryBit tail.succ counterWidth workBit
  let compare := liftedCompareBit tail.succ counterWidth
  let finalCarry :=
    liftedComparisonCarryBit tail.succ counterWidth (Fin.last tail)
  let z := EncodedBit.GateSpec.stepList prefixGates x
  have hcomm :
      EncodedBit.GateSpec.stepList prefixGates.reverse (compare.flip z) =
        compare.flip (EncodedBit.GateSpec.stepList prefixGates.reverse z) := by
    apply EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
    intro gate hgate
    exact vZeroDetectorPrefixGates_bitDisjoint_compare tail counterWidth gate
      (List.mem_reverse.mp hgate)
  change
    carry.get
        (EncodedBit.GateSpec.stepList prefixGates.reverse
          ((vZeroDetectorCopyOutGate tail counterWidth).step z)) =
      carry.get x
  change
    carry.get
        (EncodedBit.GateSpec.stepList prefixGates.reverse
          (EncodedBit.cnotStep finalCarry compare z)) =
      carry.get x
  unfold EncodedBit.cnotStep
  by_cases hfinal : finalCarry.get z
  · rw [if_pos hfinal, hcomm]
    rw [EncodedBit.get_flip_of_wire_ne compare carry
      (liftedCompare_liftedComparisonCarry_wire_ne tail.succ counterWidth
        workBit)]
    rw [EncodedBit.GateSpec.stepList_reverse_stepList]
  · rw [if_neg hfinal]
    rw [EncodedBit.GateSpec.stepList_reverse_stepList]

/-- Full comparison-work-backed `v = 0` detector.  For nonempty words it flips
the `v` bits, computes a prefix AND into comparison work, copies the final
prefix to compare, uncomputes the prefix, and restores `v`.  The empty-word
case toggles compare, matching the vacuous all-zero predicate. -/
def vZeroDetectorWithComparisonWorkGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  match n with
  | 0 =>
      [EncodedBit.GateSpec.x (liftedCompareBit 0 counterWidth)]
  | tail + 1 =>
      let negate := vZeroDetectorNegateVGates tail.succ counterWidth
      let prefixGates := vZeroDetectorPrefixGates tail counterWidth
      negate ++ prefixGates ++ [vZeroDetectorCopyOutGate tail counterWidth] ++
        prefixGates.reverse ++ negate.reverse

/-- Base-gate program for the comparison-work-backed `v = 0` detector. -/
def vZeroDetectorWithComparisonWorkProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (vZeroDetectorWithComparisonWorkGates n counterWidth)

/-- Semantic step for the comparison-work-backed `v = 0` detector. -/
def vZeroDetectorWithComparisonWorkStep (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (vZeroDetectorWithComparisonWorkGates n counterWidth)

/-- The comparison-work-backed `v = 0` detector is a concrete base-gate list
over the product register layout. -/
theorem vZeroDetectorWithComparisonWork_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (vZeroDetectorWithComparisonWorkProgram n counterWidth)
      (vZeroDetectorWithComparisonWorkStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (vZeroDetectorWithComparisonWorkGates n counterWidth)

/-- The comparison-work-backed detector preserves every lifted `v` value-bit. -/
theorem vZeroDetectorWithComparisonWorkStep_get_vValueBit
    (tail counterWidth : Nat) (target : Fin tail.succ)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    ((liftedVWord tail.succ counterWidth).bit target).get
        (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x) =
      ((liftedVWord tail.succ counterWidth).bit target).get x := by
  rw [vZeroDetectorWithComparisonWorkStep,
    vZeroDetectorWithComparisonWorkGates]
  simp only [Nat.succ_eq_add_one]
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [vZeroDetectorNegateVGates_reverse_get_vValueBit]
  rw [vZeroDetectorPrefixGates_reverse_get_vValueBit]
  simp only [EncodedBit.GateSpec.stepList, id_eq]
  rw [vZeroDetectorCopyOutGate_get_vValueBit]
  rw [vZeroDetectorPrefixGates_get_vValueBit]
  rw [vZeroDetectorNegateVGates_get_vValueBit]
  simp

/-- The comparison-work-backed detector preserves the full `v` word. -/
theorem vZeroDetectorWithComparisonWorkStep_v
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (vZeroDetectorWithComparisonWorkStep n counterWidth x).1.v =
      x.1.v := by
  cases n with
  | zero =>
      apply word_eq_of_testBit_eq
      intro bit
      exact Fin.elim0 bit
  | succ tail =>
      apply word_eq_of_testBit_eq
      intro target
      have h :=
        vZeroDetectorWithComparisonWorkStep_get_vValueBit tail counterWidth
          target x
      simpa [liftedVWord, RegisterBits.vValueBit_get,
        liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit] using h

/-- The nonempty comparison-work-backed detector preserves any observed bit
whose wire is disjoint from the detector's writable targets: `v`, compare, and
comparison carry-work bits. -/
theorem vZeroDetectorWithComparisonWorkStep_get_observed_of_detector_ne
    (tail counterWidth : Nat)
    (observed :
      EncodedBit (registersWithComparisonWorkEncoding tail.succ counterWidth))
    (hv :
      ∀ bit : Fin tail.succ,
        ((liftedVWord tail.succ counterWidth).bit bit).wire ≠ observed.wire)
    (hcompare : (liftedCompareBit tail.succ counterWidth).wire ≠ observed.wire)
    (hcarry :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).wire ≠
          observed.wire)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    observed.get
        (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x) =
      observed.get x := by
  have hprefix :
      ∀ gate,
        gate ∈ vZeroDetectorPrefixGates tail counterWidth ->
          EncodedBit.GateSpec.targetFlipPreserves
            (fun y => observed.get y) gate := by
    intro gate hgate
    rw [vZeroDetectorPrefixGates] at hgate
    simp only [List.mem_append, List.mem_singleton] at hgate
    rcases hgate with hfirst | hrest
    · subst gate
      intro y
      exact EncodedBit.get_flip_of_wire_ne
        (liftedComparisonCarryBit tail.succ counterWidth 0) observed
        (hcarry 0) y
    · rcases List.mem_ofFn.mp hrest with ⟨bit, rfl⟩
      intro y
      exact EncodedBit.get_flip_of_wire_ne
        (liftedComparisonCarryBit tail.succ counterWidth (Fin.succ bit))
        observed (hcarry (Fin.succ bit)) y
  rw [vZeroDetectorWithComparisonWorkStep,
    vZeroDetectorWithComparisonWorkGates]
  simp only [Nat.succ_eq_add_one]
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [vZeroDetectorNegateVGates, List.mem_append, List.mem_singleton]
    at hgate
  rcases hgate with (((hneg | hprefixForward) | hcopy) | hprefixReverse) |
    hnegReverse
  · rcases List.mem_ofFn.mp hneg with ⟨bit, rfl⟩
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      ((liftedVWord tail.succ counterWidth).bit bit) observed (hv bit) y
  · exact hprefix gate hprefixForward
  · subst gate
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      (liftedCompareBit tail.succ counterWidth) observed hcompare y
  · exact hprefix gate (List.mem_reverse.mp hprefixReverse)
  · have hmem :=
      List.mem_reverse.mp hnegReverse
    rcases List.mem_ofFn.mp hmem with ⟨bit, rfl⟩
    intro y
    exact EncodedBit.get_flip_of_wire_ne
      ((liftedVWord tail.succ counterWidth).bit bit) observed (hv bit) y

/-- The comparison-work-backed detector preserves the `u` word. -/
theorem vZeroDetectorWithComparisonWorkStep_u
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x).1.u =
      x.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    vZeroDetectorWithComparisonWorkStep_get_observed_of_detector_ne
      tail counterWidth ((liftedUWord tail.succ counterWidth).bit bit)
      (fun vbit =>
        Ne.symm
          (liftedUWordBit_liftedVWordBit_wire_ne tail.succ counterWidth
            bit vbit))
      (liftedCompare_liftedUWordBit_wire_ne tail.succ counterWidth bit)
      (fun workBit =>
        Ne.symm
          (liftedUWordBit_liftedComparisonCarry_wire_ne tail.succ
            counterWidth bit workBit))
      x
  simpa [liftedUWord, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using h

/-- The comparison-work-backed detector preserves the `s` coefficient word. -/
theorem vZeroDetectorWithComparisonWorkStep_sCoeff
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x).1.sCoeff =
      x.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    vZeroDetectorWithComparisonWorkStep_get_observed_of_detector_ne
      tail counterWidth ((liftedSCoeffValueWord tail.succ counterWidth).bit bit)
      (fun vbit =>
        liftedVWordBit_liftedSCoeffValueWordBit_wire_ne tail.succ
          counterWidth vbit bit)
      (liftedCompare_liftedSCoeffValueWordBit_wire_ne tail.succ
        counterWidth bit)
      (fun workBit =>
        Ne.symm
          (liftedSCoeffValueWordBit_liftedComparisonCarry_wire_ne
            tail.succ counterWidth bit workBit))
      x
  simpa [liftedSCoeffValueWord, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using h

/-- The comparison-work-backed detector preserves the `r` coefficient word. -/
theorem vZeroDetectorWithComparisonWorkStep_rCoeff
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x).1.rCoeff =
      x.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    vZeroDetectorWithComparisonWorkStep_get_observed_of_detector_ne
      tail counterWidth ((liftedRCoeffValueWord tail.succ counterWidth).bit bit)
      (fun vbit =>
        liftedVWordBit_liftedRCoeffValueWordBit_wire_ne tail.succ
          counterWidth vbit bit)
      (liftedCompare_liftedRCoeffValueWordBit_wire_ne tail.succ
        counterWidth bit)
      (fun workBit =>
        Ne.symm
          (liftedRCoeffValueWordBit_liftedComparisonCarry_wire_ne
            tail.succ counterWidth bit workBit))
      x
  simpa [liftedRCoeffValueWord, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using h

/-- The comparison-work-backed detector preserves the first scratch bit. -/
theorem vZeroDetectorWithComparisonWorkStep_scratchA
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x).1.scratchA =
      x.1.scratchA := by
  have h :=
    vZeroDetectorWithComparisonWorkStep_get_observed_of_detector_ne
      tail counterWidth (liftedScratchABit tail.succ counterWidth)
      (fun bit =>
        liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
          (RegisterBits.vValueBit tail.succ counterWidth bit)
          (RegisterBits.scratchABit tail.succ counterWidth)
          (RegisterBits.v_scratchA_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
        (RegisterBits.compareBit tail.succ counterWidth)
        (RegisterBits.scratchABit tail.succ counterWidth)
        (RegisterBits.compare_scratchA_wire_ne tail.succ counterWidth))
      (fun workBit =>
        Ne.symm
          (liftedScratchA_liftedComparisonCarry_wire_ne tail.succ
            counterWidth workBit))
      x
  simpa [liftedScratchABit, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit, RegisterBits.scratchABit_get] using h

/-- The comparison-work-backed detector preserves the second scratch bit. -/
theorem vZeroDetectorWithComparisonWorkStep_scratchB
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x).1.scratchB =
      x.1.scratchB := by
  have h :=
    vZeroDetectorWithComparisonWorkStep_get_observed_of_detector_ne
      tail counterWidth (liftedScratchBBit tail.succ counterWidth)
      (fun bit =>
        liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
          (RegisterBits.vValueBit tail.succ counterWidth bit)
          (RegisterBits.scratchBBit tail.succ counterWidth)
          (RegisterBits.v_scratchB_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
        (RegisterBits.compareBit tail.succ counterWidth)
        (RegisterBits.scratchBBit tail.succ counterWidth)
        (RegisterBits.compare_scratchB_wire_ne tail.succ counterWidth))
      (fun workBit =>
        Ne.symm
          (liftRegisterBit_liftComparisonWorkBit_wire_ne tail.succ counterWidth
            (RegisterBits.scratchBBit tail.succ counterWidth)
            (comparisonCarryValueBit tail.succ workBit)))
      x
  simpa [liftedScratchBBit, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit, RegisterBits.scratchBBit_get] using h

/-- The comparison-work-backed detector preserves the history word. -/
theorem vZeroDetectorWithComparisonWorkStep_history
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x).1.history =
      x.1.history := by
  apply word_eq_of_testBit_eq
  intro bit
  let observed :=
    liftRegisterBitToComparisonWork tail.succ counterWidth
      (RegisterBits.historyBit tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
  have h :=
    vZeroDetectorWithComparisonWorkStep_get_observed_of_detector_ne
      tail counterWidth observed
      (fun vbit =>
        liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
          (RegisterBits.vValueBit tail.succ counterWidth vbit)
          (RegisterBits.historyBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit))
          (RegisterBits.v_history_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire vbit)
            (WireAddress.littleEndianWire bit)))
      (liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
        (RegisterBits.compareBit tail.succ counterWidth)
        (RegisterBits.historyBit tail.succ counterWidth
          (WireAddress.littleEndianWire bit))
        (RegisterBits.compare_history_wire_ne tail.succ counterWidth
          (WireAddress.littleEndianWire bit)))
      (fun workBit =>
        Ne.symm
          (liftRegisterBit_liftComparisonWorkBit_wire_ne tail.succ counterWidth
            (RegisterBits.historyBit tail.succ counterWidth
              (WireAddress.littleEndianWire bit))
            (comparisonCarryValueBit tail.succ workBit)))
      x
  simpa [observed, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit, RegisterBits.historyBit_get,
    WireAddress.bitIndex_littleEndianWire] using h

/-- The comparison-work-backed detector preserves the active flag. -/
theorem vZeroDetectorWithComparisonWorkStep_active
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x).1.active =
      x.1.active := by
  have h :=
    vZeroDetectorWithComparisonWorkStep_get_observed_of_detector_ne
      tail counterWidth (liftedActiveBit tail.succ counterWidth)
      (fun bit =>
        liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
          (RegisterBits.vValueBit tail.succ counterWidth bit)
          (RegisterBits.activeBit tail.succ counterWidth)
          (Ne.symm
            (RegisterBits.active_v_wire_ne tail.succ counterWidth
              (WireAddress.littleEndianWire bit))))
      (liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
        (RegisterBits.compareBit tail.succ counterWidth)
        (RegisterBits.activeBit tail.succ counterWidth)
        (Ne.symm (RegisterBits.active_compare_wire_ne tail.succ counterWidth)))
      (fun workBit =>
        Ne.symm
          (liftRegisterBit_liftComparisonWorkBit_wire_ne tail.succ counterWidth
            (RegisterBits.activeBit tail.succ counterWidth)
            (comparisonCarryValueBit tail.succ workBit)))
      x
  simpa [liftedActiveBit, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit, RegisterBits.activeBit_get] using h

/-- The comparison-work-backed detector preserves the padding counter. -/
theorem vZeroDetectorWithComparisonWorkStep_counter
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x).1.counter =
      x.1.counter := by
  apply word_eq_of_testBit_eq
  intro bit
  let observed :=
    liftRegisterBitToComparisonWork tail.succ counterWidth
      (RegisterBits.counterBit tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
  have h :=
    vZeroDetectorWithComparisonWorkStep_get_observed_of_detector_ne
      tail counterWidth observed
      (fun vbit =>
        liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
          (RegisterBits.vValueBit tail.succ counterWidth vbit)
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit))
          (RegisterBits.v_counter_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire vbit)
            (WireAddress.littleEndianWire bit)))
      (liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
        (RegisterBits.compareBit tail.succ counterWidth)
        (RegisterBits.counterBit tail.succ counterWidth
          (WireAddress.littleEndianWire bit))
        (RegisterBits.compare_counter_wire_ne tail.succ counterWidth
          (WireAddress.littleEndianWire bit)))
      (fun workBit =>
        Ne.symm
          (liftRegisterBit_liftComparisonWorkBit_wire_ne tail.succ counterWidth
            (RegisterBits.counterBit tail.succ counterWidth
              (WireAddress.littleEndianWire bit))
            (comparisonCarryValueBit tail.succ workBit)))
      x
  simpa [observed, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit, WireAddress.bitIndex_littleEndianWire]
    using h

/-- On clean comparison work, the detector restores the comparison-work register. -/
theorem vZeroDetectorWithComparisonWorkStep_work_clean_any
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
        (x, cleanComparisonWork tail.succ)).2 =
      cleanComparisonWork tail.succ := by
  let output :=
    vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  have hcarry :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get output =
          false := by
    intro bit
    dsimp [output]
    rw [vZeroDetectorWithComparisonWorkStep, vZeroDetectorWithComparisonWorkGates]
    simp only [Nat.succ_eq_add_one]
    rw [EncodedBit.GateSpec.stepList_append,
      EncodedBit.GateSpec.stepList_append,
      EncodedBit.GateSpec.stepList_append,
      EncodedBit.GateSpec.stepList_append]
    rw [vZeroDetectorNegateVGates_reverse_get_comparisonCarry]
    simp only [EncodedBit.GateSpec.stepList, id_eq]
    rw [vZeroDetectorPrefixCopyUncompute_get_comparisonCarry]
    rw [vZeroDetectorNegateVGates_get_comparisonCarry]
    simp
  cases hwork : output.2 with
  | mk carry =>
      have hcarryWord : carry = (0 : Word tail.succ) := by
        apply word_eq_of_testBit_eq
        intro bit
        have hbit := hcarry bit
        change (comparisonCarryValueBit tail.succ bit).get output.2 = false
          at hbit
        rw [hwork] at hbit
        simpa [comparisonCarryValueBit, comparisonCarryBit,
          comparisonWorkEquiv, BinaryLabelEncoding.finIdentityBit,
          BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel] using hbit
      rw [hcarryWord]
      rfl

/-- Compatibility wrapper for callers that still carry a clean-compare
precondition. -/
theorem vZeroDetectorWithComparisonWorkStep_work_clean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (_hcompare : x.compare = false) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
        (x, cleanComparisonWork tail.succ)).2 =
      cleanComparisonWork tail.succ :=
  vZeroDetectorWithComparisonWorkStep_work_clean_any tail counterWidth x

/-- On clean compare and comparison work, the comparison-work-backed detector
writes the source-level `v = 0` predicate into compare. -/
theorem vZeroDetectorWithComparisonWorkStep_get_compare_clean
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth)
    (hcompare : (liftedCompareBit tail.succ counterWidth).get x = false)
    (hwork :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get x =
          false) :
    (liftedCompareBit tail.succ counterWidth).get
        (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x) =
      decide (x.1.v.val = 0) := by
  let negate := vZeroDetectorNegateVGates tail.succ counterWidth
  let prefixGates := vZeroDetectorPrefixGates tail counterWidth
  let z0 := EncodedBit.GateSpec.stepList negate x
  have hworkZ0 :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get z0 =
          false := by
    intro bit
    dsimp [z0, negate]
    rw [vZeroDetectorNegateVGates_get_comparisonCarry]
    exact hwork bit
  have hfinalCarry :
      (liftedComparisonCarryBit tail.succ counterWidth (Fin.last tail)).get
          (EncodedBit.GateSpec.stepList prefixGates z0) =
        vZeroDetectorPrefixRead tail.succ counterWidth tail
          (Nat.lt_succ_self tail) z0 := by
    dsimp [prefixGates]
    exact vZeroDetectorPrefixGates_get_final_clean tail counterWidth z0
      hworkZ0
  rw [vZeroDetectorWithComparisonWorkStep,
    vZeroDetectorWithComparisonWorkGates]
  simp only [Nat.succ_eq_add_one]
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [vZeroDetectorNegateVGates_reverse_get_compare]
  rw [vZeroDetectorPrefixGates_reverse_get_compare]
  simp only [EncodedBit.GateSpec.stepList, id_eq]
  rw [vZeroDetectorCopyOutGate_get_compare]
  rw [vZeroDetectorPrefixGates_get_compare]
  rw [vZeroDetectorNegateVGates_get_compare]
  rw [hcompare]
  simp only [Nat.succ_eq_add_one, Bool.false_bne, Fin.val_eq_zero_iff]
  rw [hfinalCarry]
  dsimp [z0, negate]
  simpa using
    vZeroDetectorPrefixRead_after_negate_eq_decide_v_zero tail counterWidth x

/-- On clean comparison work, the comparison-work-backed detector xors the
source-level `v = 0` predicate into compare. -/
theorem vZeroDetectorWithComparisonWorkStep_get_compare_clean_xor
    (tail counterWidth : Nat)
    (x : RegistersWithComparisonWork tail.succ counterWidth)
    (hwork :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get x =
          false) :
    (liftedCompareBit tail.succ counterWidth).get
        (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth x) =
      ((liftedCompareBit tail.succ counterWidth).get x ^^
        decide (x.1.v.val = 0)) := by
  let negate := vZeroDetectorNegateVGates tail.succ counterWidth
  let prefixGates := vZeroDetectorPrefixGates tail counterWidth
  let z0 := EncodedBit.GateSpec.stepList negate x
  have hworkZ0 :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get z0 =
          false := by
    intro bit
    dsimp [z0, negate]
    rw [vZeroDetectorNegateVGates_get_comparisonCarry]
    exact hwork bit
  have hfinalCarry :
      (liftedComparisonCarryBit tail.succ counterWidth (Fin.last tail)).get
          (EncodedBit.GateSpec.stepList prefixGates z0) =
        vZeroDetectorPrefixRead tail.succ counterWidth tail
          (Nat.lt_succ_self tail) z0 := by
    dsimp [prefixGates]
    exact vZeroDetectorPrefixGates_get_final_clean tail counterWidth z0
      hworkZ0
  rw [vZeroDetectorWithComparisonWorkStep,
    vZeroDetectorWithComparisonWorkGates]
  simp only [Nat.succ_eq_add_one]
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [vZeroDetectorNegateVGates_reverse_get_compare]
  rw [vZeroDetectorPrefixGates_reverse_get_compare]
  simp only [EncodedBit.GateSpec.stepList, id_eq]
  rw [vZeroDetectorCopyOutGate_get_compare]
  rw [vZeroDetectorPrefixGates_get_compare]
  rw [vZeroDetectorNegateVGates_get_compare]
  simp only [Nat.succ_eq_add_one, Fin.val_eq_zero_iff]
  rw [hfinalCarry]
  dsimp [z0, negate]
  simpa [Bool.xor_assoc] using
    congrArg (fun b => (liftedCompareBit tail.succ counterWidth).get x ^^ b)
      (vZeroDetectorPrefixRead_after_negate_eq_decide_v_zero tail counterWidth x)

/-- On clean comparison work, the detector's register endpoint only xors
`v = 0` into compare. -/
theorem vZeroDetectorWithComparisonWorkStep_register_cleanEndpoint
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
        (x, cleanComparisonWork tail.succ)).1 =
      { x with compare := x.compare ^^ decide (x.v.val = 0) } := by
  let y :=
    (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)).1
  have hu : y.u = x.u := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_u tail counterWidth
      (x, cleanComparisonWork tail.succ)
  have hv : y.v = x.v := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_v tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  have hs : y.sCoeff = x.sCoeff := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_sCoeff tail counterWidth
      (x, cleanComparisonWork tail.succ)
  have hr : y.rCoeff = x.rCoeff := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_rCoeff tail counterWidth
      (x, cleanComparisonWork tail.succ)
  have hscratchA : y.scratchA = x.scratchA := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_scratchA tail counterWidth
      (x, cleanComparisonWork tail.succ)
  have hscratchB : y.scratchB = x.scratchB := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_scratchB tail counterWidth
      (x, cleanComparisonWork tail.succ)
  have hhistory : y.history = x.history := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_history tail counterWidth
      (x, cleanComparisonWork tail.succ)
  have hactive : y.active = x.active := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_active tail counterWidth
      (x, cleanComparisonWork tail.succ)
  have hcounter : y.counter = x.counter := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_counter tail counterWidth
      (x, cleanComparisonWork tail.succ)
  have hworkClean :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get
          (x, cleanComparisonWork tail.succ) = false := by
    intro bit
    change
      (comparisonCarryValueBit tail.succ bit).get
        (cleanComparisonWork tail.succ) = false
    exact comparisonCarryValueBit_clean tail.succ bit
  have hcompare : y.compare = x.compare ^^ decide (x.v.val = 0) := by
    dsimp [y]
    have h :=
      vZeroDetectorWithComparisonWorkStep_get_compare_clean_xor
        tail counterWidth (x, cleanComparisonWork tail.succ) hworkClean
    change
      (liftedCompareBit tail.succ counterWidth).get
          (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
            (x, cleanComparisonWork tail.succ)) =
        x.compare ^^ decide (x.v.val = 0)
    rw [h]
    have hinput :
        (liftedCompareBit tail.succ counterWidth).get
            (x, cleanComparisonWork tail.succ) = x.compare := by
      simp [liftedCompareBit, liftRegisterBitToComparisonWork,
        BinaryLabelEncoding.prodLeftBit]
    cases hcmp : x.compare <;> by_cases hzero : x.v.val = 0 <;>
      simp [hinput, hcmp, hzero]
  change y = { x with compare := x.compare ^^ decide (x.v.val = 0) }
  clear_value y
  rcases y with
    ⟨yu, yv, ycompare, ysCoeff, yrCoeff, yscratchA, yscratchB,
      yhistory, yactive, ycounter⟩
  rcases x with
    ⟨xu, xv, xcompare, xsCoeff, xrCoeff, xscratchA, xscratchB,
      xhistory, xactive, xcounter⟩
  simp at hu hv hs hr hscratchA hscratchB hhistory hactive hcounter
  subst yu
  subst yv
  subst ysCoeff
  subst yrCoeff
  subst yscratchA
  subst yscratchB
  subst yhistory
  subst yactive
  subst ycounter
  cases ycompare <;> cases hcmp : xcompare <;>
    by_cases hzero : xv.val = 0 <;> simp [hcmp, hzero] at hcompare ⊢

/-- Clean endpoint for the comparison-work-backed `v = 0` detector. -/
theorem vZeroDetectorWithComparisonWorkStep_cleanEndpoint
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
        (x, cleanComparisonWork tail.succ) =
      ({ x with compare := x.compare ^^ decide (x.v.val = 0) },
        cleanComparisonWork tail.succ) := by
  exact Prod.ext
    (vZeroDetectorWithComparisonWorkStep_register_cleanEndpoint
      tail counterWidth x)
    (vZeroDetectorWithComparisonWorkStep_work_clean_any tail counterWidth x)

/-! ## Detector-gated terminating counter mode -/

/-- Lift the comparison-work-backed `v = 0` detector over the dedicated
counter-increment work object. -/
def detectorCounterVZeroDetectorStep (n counterWidth : Nat) :
    RegistersWithDetectorCounterWork n counterWidth ->
      RegistersWithDetectorCounterWork n counterWidth :=
  fun x => (vZeroDetectorWithComparisonWorkStep n counterWidth x.1, x.2)

/-- Actual circuit for the detector lifted over counter-increment work. -/
def detectorCounterVZeroDetectorProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithDetectorCounterWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix
    (counterIncrementWorkEncoding counterWidth).width
    (vZeroDetectorWithComparisonWorkProgram n counterWidth)

/-- The detector lifted over counter-increment work realizes its product action. -/
theorem detectorCounterVZeroDetector_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithDetectorCounterWorkEncoding n counterWidth)
      (detectorCounterVZeroDetectorProgram n counterWidth)
      (detectorCounterVZeroDetectorStep n counterWidth) := by
  unfold detectorCounterVZeroDetectorProgram detectorCounterVZeroDetectorStep
  exact UnitaryCircuit.Realizes.onBinaryPrefix
    (right := counterIncrementWorkEncoding counterWidth)
    (vZeroDetectorWithComparisonWork_realizes n counterWidth)

/-- The detector lifted over counter-increment work preserves the counter-work
object. -/
theorem detectorCounterVZeroDetectorStep_counterWork
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterVZeroDetectorStep n counterWidth x).2 = x.2 := by
  rfl

/-- On clean comparison work, the lifted detector restores the comparison-work
object and leaves counter-increment work untouched. -/
theorem detectorCounterVZeroDetectorStep_comparisonWork_clean_any
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (work : CounterIncrementWork counterWidth) :
    (detectorCounterVZeroDetectorStep tail.succ counterWidth
        ((x, cleanComparisonWork tail.succ), work)).1.2 =
      cleanComparisonWork tail.succ := by
  exact vZeroDetectorWithComparisonWorkStep_work_clean_any
    tail counterWidth x

/-- Clean endpoint for the detector lifted over counter-increment work. -/
theorem detectorCounterVZeroDetectorStep_cleanEndpoint
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (work : CounterIncrementWork counterWidth) :
    detectorCounterVZeroDetectorStep tail.succ counterWidth
        ((x, cleanComparisonWork tail.succ), work) =
      (({ x with compare := x.compare ^^ decide (x.v.val = 0) },
        cleanComparisonWork tail.succ), work) := by
  unfold detectorCounterVZeroDetectorStep
  rw [vZeroDetectorWithComparisonWorkStep_cleanEndpoint]

/-- On clean comparison work, the lifted detector xors the source-level
`v = 0` predicate into compare. -/
theorem detectorCounterVZeroDetectorStep_get_compare_clean_xor
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (work : CounterIncrementWork counterWidth) :
    (detectorCounterCompareBit tail.succ counterWidth).get
        (detectorCounterVZeroDetectorStep tail.succ counterWidth
          ((x, cleanComparisonWork tail.succ), work)) =
      (x.compare ^^ decide (x.v.val = 0)) := by
  have hworkClean :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get
          (x, cleanComparisonWork tail.succ) = false := by
    intro bit
    change
      (comparisonCarryValueBit tail.succ bit).get
        (cleanComparisonWork tail.succ) = false
    exact comparisonCarryValueBit_clean tail.succ bit
  change
    (liftedCompareBit tail.succ counterWidth).get
        (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
          (x, cleanComparisonWork tail.succ)) =
      (x.compare ^^ decide (x.v.val = 0))
  rw [vZeroDetectorWithComparisonWorkStep_get_compare_clean_xor
    tail counterWidth (x, cleanComparisonWork tail.succ) hworkClean]
  simp [liftedCompareBit, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit]

/-- Running the lifted detector twice on clean comparison work restores compare. -/
theorem detectorCounterVZeroDetectorStep_get_compare_clean_twice
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (work : CounterIncrementWork counterWidth) :
    (detectorCounterCompareBit tail.succ counterWidth).get
        (detectorCounterVZeroDetectorStep tail.succ counterWidth
          (detectorCounterVZeroDetectorStep tail.succ counterWidth
            ((x, cleanComparisonWork tail.succ), work))) =
      x.compare := by
  let y :=
    vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  have hworkFirst :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get
          (x, cleanComparisonWork tail.succ) = false := by
    intro bit
    change
      (comparisonCarryValueBit tail.succ bit).get
        (cleanComparisonWork tail.succ) = false
    exact comparisonCarryValueBit_clean tail.succ bit
  have hfirstCompare :
      (liftedCompareBit tail.succ counterWidth).get y =
        (x.compare ^^ decide (x.v.val = 0)) := by
    simpa [y, liftedCompareBit, liftRegisterBitToComparisonWork,
      BinaryLabelEncoding.prodLeftBit] using
      vZeroDetectorWithComparisonWorkStep_get_compare_clean_xor
        tail counterWidth (x, cleanComparisonWork tail.succ) hworkFirst
  have hfirstWork : y.2 = cleanComparisonWork tail.succ := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_work_clean_any
      tail counterWidth x
  have hworkSecond :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get y =
          false := by
    intro bit
    change
      (comparisonCarryValueBit tail.succ bit).get y.2 = false
    rw [hfirstWork]
    exact comparisonCarryValueBit_clean tail.succ bit
  have hvPres : y.1.v = x.v := by
    dsimp [y]
    exact vZeroDetectorWithComparisonWorkStep_v
      tail.succ counterWidth (x, cleanComparisonWork tail.succ)
  have hsecond :=
    vZeroDetectorWithComparisonWorkStep_get_compare_clean_xor
      tail counterWidth y hworkSecond
  change
    (liftedCompareBit tail.succ counterWidth).get
        (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth y) =
      x.compare
  rw [hsecond, hfirstCompare]
  have hdec : decide (y.1.v.val = 0) = decide (x.v.val = 0) := by
    rw [hvPres]
  rw [hdec]
  cases x.compare <;> cases decide (x.v.val = 0) <;> simp

/-- Gate list for the terminating counter-mode action inside the
detector-plus-counter workspace: clear active, then increment the padding
counter using the dedicated clean counter-increment work object. -/
def detectorCounterTerminatingCounterModeGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithDetectorCounterWorkEncoding n counterWidth)) :=
  [EncodedBit.GateSpec.x (detectorCounterActiveBit n counterWidth)] ++
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
      (detectorCounterIncrementLayout n counterWidth)

/-- Semantic action for the detector-plus-counter terminating counter mode. -/
def detectorCounterTerminatingCounterModeStep (n counterWidth : Nat) :
    RegistersWithDetectorCounterWork n counterWidth ->
      RegistersWithDetectorCounterWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (detectorCounterTerminatingCounterModeGates n counterWidth)

/-- Actual circuit for the detector-plus-counter terminating counter mode. -/
def detectorCounterTerminatingCounterModeProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithDetectorCounterWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (detectorCounterTerminatingCounterModeGates n counterWidth)

/-- The terminating counter-mode circuit realizes its gate-list action. -/
theorem detectorCounterTerminatingCounterMode_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithDetectorCounterWorkEncoding n counterWidth)
      (detectorCounterTerminatingCounterModeProgram n counterWidth)
      (detectorCounterTerminatingCounterModeStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (detectorCounterTerminatingCounterModeGates n counterWidth)

/-- Expose the terminating detector-counter step as an active-flag flip followed
by the clean carry/sum incrementer. -/
theorem detectorCounterTerminatingCounterModeStep_eq_cleanCarrySum_after_active
    (n counterWidth : Nat)
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n)
    (work : CounterIncrementWork counterWidth) :
    detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), work) =
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
        (detectorCounterIncrementLayout n counterWidth)
        (({ x with active := !x.active }, cmpWork), work) := by
  rw [detectorCounterTerminatingCounterModeStep,
    detectorCounterTerminatingCounterModeGates]
  rw [EncodedBit.GateSpec.stepList_append]
  simp [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    detectorCounterActiveBit, liftedActiveBit,
    liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, RegisterBits.activeBit,
    RegisterBits.tupleActiveBit, registerTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.boolBit, EncodedBit.relabel]

/-- The terminating detector-counter step preserves any lifted
register-plus-comparison readout that is disjoint from the active flag and all
padding-counter target bits. -/
theorem detectorCounterTerminatingCounterModeStep_get_stateObserved
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (hactive :
      (liftedActiveBit n counterWidth).wire ≠ observed.wire)
    (hcounter :
      ∀ bit : Fin counterWidth,
        (liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire bit))).wire ≠ observed.wire)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (liftComparisonStateBitToDetectorCounterWork n counterWidth observed).get
        (detectorCounterTerminatingCounterModeStep n counterWidth x) =
      (liftComparisonStateBitToDetectorCounterWork n counterWidth observed).get
        x := by
  let liftedObserved :=
    liftComparisonStateBitToDetectorCounterWork n counterWidth observed
  let afterActive : RegistersWithDetectorCounterWork n counterWidth :=
    (({ x.1.1 with active := !x.1.1.active }, x.1.2), x.2)
  have hnorm :
      detectorCounterTerminatingCounterModeStep n counterWidth x =
        PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (detectorCounterIncrementLayout n counterWidth) afterActive := by
    simpa [afterActive] using
      detectorCounterTerminatingCounterModeStep_eq_cleanCarrySum_after_active
        n counterWidth x.1.1 x.1.2 x.2
  rw [hnorm]
  have hadder :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (detectorCounterIncrementLayout n counterWidth) liftedObserved
      (fun bit =>
        liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
          n counterWidth
          (liftRegisterBitToComparisonWork n counterWidth
            (RegisterBits.counterBit n counterWidth
              (WireAddress.littleEndianWire bit)))
          observed (hcounter bit))
      (fun bit =>
        Ne.symm
          (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
            n counterWidth observed
            (counterIncrementCarryWorkBit counterWidth bit)))
      afterActive
  have hbefore :
      liftedObserved.get afterActive = liftedObserved.get x := by
    have hflip :=
      EncodedBit.get_flip_of_wire_ne
        (detectorCounterActiveBit n counterWidth) liftedObserved
        (liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
          n counterWidth (liftedActiveBit n counterWidth) observed hactive)
        x
    simpa [afterActive, liftedObserved, detectorCounterActiveBit,
      liftedActiveBit, liftComparisonStateBitToDetectorCounterWork,
      liftRegisterBitToComparisonWork, RegisterBits.activeBit,
      RegisterBits.tupleActiveBit, registerTupleEquiv,
      BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.boolBit, EncodedBit.relabel] using hflip
  simpa [liftedObserved,
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep] using
    hadder.trans hbefore

/-- The terminating detector-counter step preserves the `u` word. -/
theorem detectorCounterTerminatingCounterModeStep_u
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  let observed :=
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.uValueBit n counterWidth bit)
  have h :=
    detectorCounterTerminatingCounterModeStep_get_stateObserved
      n counterWidth observed
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.uValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.uValueBit] using
            RegisterBits.active_u_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
      (fun counterBit =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.uValueBit n counterWidth bit)
          (by
            simpa [RegisterBits.uValueBit] using
              Ne.symm (RegisterBits.u_counter_wire_ne n counterWidth
                (WireAddress.littleEndianWire bit)
                (WireAddress.littleEndianWire counterBit))))
      x
  simpa [observed, liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    RegisterBits.uValueBit_get] using h

/-- The terminating detector-counter step preserves the `v` word. -/
theorem detectorCounterTerminatingCounterModeStep_v
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  let observed :=
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.vValueBit n counterWidth bit)
  have h :=
    detectorCounterTerminatingCounterModeStep_get_stateObserved
      n counterWidth observed
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.vValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.vValueBit] using
            RegisterBits.active_v_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
      (fun counterBit =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.vValueBit n counterWidth bit)
          (by
            simpa [RegisterBits.vValueBit] using
              Ne.symm (RegisterBits.v_counter_wire_ne n counterWidth
                (WireAddress.littleEndianWire bit)
                (WireAddress.littleEndianWire counterBit))))
      x
  simpa [observed, liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    RegisterBits.vValueBit_get] using h

/-- The terminating detector-counter step preserves the `s` coefficient word. -/
theorem detectorCounterTerminatingCounterModeStep_sCoeff
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  let observed :=
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.sCoeffValueBit n counterWidth bit)
  have h :=
    detectorCounterTerminatingCounterModeStep_get_stateObserved
      n counterWidth observed
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.sCoeffValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.sCoeffValueBit] using
            RegisterBits.active_sCoeff_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
      (fun counterBit =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.sCoeffValueBit n counterWidth bit)
          (by
            simpa [RegisterBits.sCoeffValueBit] using
              Ne.symm (RegisterBits.sCoeff_counter_wire_ne n counterWidth
                (WireAddress.littleEndianWire bit)
                (WireAddress.littleEndianWire counterBit))))
      x
  simpa [observed, liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    RegisterBits.sCoeffValueBit_get] using h

/-- The terminating detector-counter step preserves the `r` coefficient word. -/
theorem detectorCounterTerminatingCounterModeStep_rCoeff
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  let observed :=
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.rCoeffValueBit n counterWidth bit)
  have h :=
    detectorCounterTerminatingCounterModeStep_get_stateObserved
      n counterWidth observed
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.rCoeffValueBit n counterWidth bit)
        (by
          simpa [RegisterBits.rCoeffValueBit] using
            RegisterBits.active_rCoeff_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
      (fun counterBit =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.rCoeffValueBit n counterWidth bit)
          (by
            simpa [RegisterBits.rCoeffValueBit] using
              Ne.symm (RegisterBits.rCoeff_counter_wire_ne n counterWidth
                (WireAddress.littleEndianWire bit)
                (WireAddress.littleEndianWire counterBit))))
      x
  simpa [observed, liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    RegisterBits.rCoeffValueBit_get] using h

/-- The terminating detector-counter step preserves compare. -/
theorem detectorCounterTerminatingCounterModeStep_compare
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth x).1.1.compare =
      x.1.1.compare := by
  have h :=
    detectorCounterTerminatingCounterModeStep_get_stateObserved
      n counterWidth (liftedCompareBit n counterWidth)
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth))
      (fun counterBit =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.compareBit n counterWidth)
          (Ne.symm (RegisterBits.compare_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire counterBit))))
      x
  simpa [liftedCompareBit, liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit] using h

/-- The terminating detector-counter step preserves scratchA. -/
theorem detectorCounterTerminatingCounterModeStep_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth x).1.1.scratchA =
      x.1.1.scratchA := by
  have h :=
    detectorCounterTerminatingCounterModeStep_get_stateObserved
      n counterWidth
      (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.scratchABit n counterWidth))
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchABit n counterWidth)
        (RegisterBits.active_scratchA_wire_ne n counterWidth))
      (fun counterBit =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.scratchABit n counterWidth)
          (Ne.symm (RegisterBits.scratchA_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire counterBit))))
      x
  simpa [liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    RegisterBits.scratchABit_get] using h

/-- The terminating detector-counter step preserves scratchB. -/
theorem detectorCounterTerminatingCounterModeStep_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth x).1.1.scratchB =
      x.1.1.scratchB := by
  have h :=
    detectorCounterTerminatingCounterModeStep_get_stateObserved
      n counterWidth
      (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.scratchBBit n counterWidth))
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.active_scratchB_wire_ne n counterWidth))
      (fun counterBit =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.scratchBBit n counterWidth)
          (Ne.symm (RegisterBits.scratchB_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire counterBit))))
      x
  simpa [liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    RegisterBits.scratchBBit_get] using h

/-- The terminating detector-counter step preserves branch history. -/
theorem detectorCounterTerminatingCounterModeStep_history
    (n counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork n counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth x).1.1.history =
      x.1.1.history := by
  apply word_eq_of_testBit_eq
  intro bit
  let observed :=
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.historyBit n counterWidth
        (WireAddress.littleEndianWire bit))
  have h :=
    detectorCounterTerminatingCounterModeStep_get_stateObserved
      n counterWidth observed
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.historyBit n counterWidth
          (WireAddress.littleEndianWire bit))
        (RegisterBits.active_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)))
      (fun counterBit =>
        liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (RegisterBits.historyBit n counterWidth
            (WireAddress.littleEndianWire bit))
          (Ne.symm (RegisterBits.history_counter_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire counterBit))))
      x
  simpa [observed, liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    RegisterBits.historyBit_get] using h

/-- The terminating detector-counter step toggles the concrete active flag
before incrementing the padding counter. -/
theorem detectorCounterTerminatingCounterModeStep_active
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (cmpWork : ComparisonWork n) (work : CounterIncrementWork counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), work)).1.1.active = !x.active := by
  rw [detectorCounterTerminatingCounterModeStep_eq_cleanCarrySum_after_active]
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (detectorCounterIncrementLayout n counterWidth)
      (detectorCounterActiveBit n counterWidth)
      (fun bit =>
        liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
          n counterWidth
          (liftRegisterBitToComparisonWork n counterWidth
            (RegisterBits.counterBit n counterWidth
              (WireAddress.littleEndianWire bit)))
          (liftedActiveBit n counterWidth)
          (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
            (RegisterBits.counterBit n counterWidth
              (WireAddress.littleEndianWire bit))
            (RegisterBits.activeBit n counterWidth)
            (Ne.symm (RegisterBits.active_counter_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))))
      (fun bit =>
        Ne.symm
          (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
            n counterWidth (liftedActiveBit n counterWidth)
            (counterIncrementCarryWorkBit counterWidth bit)))
      (({ x with active := !x.active }, cmpWork), work)
  simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    detectorCounterActiveBit, liftedActiveBit,
    liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    RegisterBits.activeBit_get] using h

/-- On active inputs, the terminating detector-counter step clears `active`. -/
theorem detectorCounterTerminatingCounterModeStep_active_of_active
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (cmpWork : ComparisonWork n) (work : CounterIncrementWork counterWidth)
    (hactive : x.active = true) :
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), work)).1.1.active = false := by
  rw [detectorCounterTerminatingCounterModeStep_active, hactive]
  rfl

/-- The terminating detector-counter step preserves the comparison-work object. -/
theorem detectorCounterTerminatingCounterModeStep_comparisonWork
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (cmpWork : ComparisonWork n)
    (work : CounterIncrementWork counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), work)).1.2 = cmpWork := by
  apply (comparisonWorkEquiv n).injective
  change
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), work)).1.2.carry = cmpWork.carry
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    detectorCounterTerminatingCounterModeStep_get_stateObserved
      n counterWidth (liftedComparisonCarryBit n counterWidth bit)
      (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (comparisonCarryValueBit n bit))
      (fun counterBit =>
        liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
          (RegisterBits.counterBit n counterWidth
            (WireAddress.littleEndianWire counterBit))
          (comparisonCarryValueBit n bit))
      ((x, cmpWork), work)
  simpa [comparisonCarryValueBit, comparisonCarryBit, comparisonWorkEquiv,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    EncodedBit.relabel, WireAddress.bitIndex_littleEndianWire,
    liftedComparisonCarryBit, liftComparisonWorkBit,
    liftComparisonStateBitToDetectorCounterWork,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit] using h

/-- The terminating detector-counter step preserves clean comparison work. -/
theorem detectorCounterTerminatingCounterModeStep_comparisonWork_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (work : CounterIncrementWork counterWidth) :
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cleanComparisonWork n), work)).1.2 =
      cleanComparisonWork n := by
  exact detectorCounterTerminatingCounterModeStep_comparisonWork
    n counterWidth x (cleanComparisonWork n) work

/-- On clean counter-increment work inputs, the terminating detector-counter
step restores the counter-increment work object. -/
theorem detectorCounterTerminatingCounterModeStep_counterWork_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (cmpWork : ComparisonWork n) :
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), cleanCounterIncrementWork counterWidth)).2 =
      cleanCounterIncrementWork counterWidth := by
  rw [detectorCounterTerminatingCounterModeStep_eq_cleanCarrySum_after_active]
  apply Prod.ext
  · have h :=
      True.intro
    clear h
    apply word_eq_of_testBit_eq
    intro bit
    have hbit :=
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
        (detectorCounterIncrementLayout n counterWidth) bit
        (({ x with active := !x.active }, cmpWork),
          cleanCounterIncrementWork counterWidth)
    simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
      detectorCounterIncrementLayout, detectorCounterIncrementSourceWord,
      detectorCounterIncrementSourceBit,
      liftCounterIncrementWorkBitToDetectorCounterWork,
      counterIncrementSourceBit, counterIncrementWorkEncoding, wordEncoding,
      BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
      WireAddress.bitIndex_littleEndianWire,
      cleanCounterIncrementWork] using hbit
  · apply Prod.ext
    · have h :=
        PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
          (detectorCounterIncrementLayout n counterWidth)
          (({ x with active := !x.active }, cmpWork),
            cleanCounterIncrementWork counterWidth)
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        detectorCounterIncrementLayout, detectorCounterIncrementCarryInBit,
        liftCounterIncrementWorkBitToDetectorCounterWork,
        counterIncrementCarryInBit, BinaryLabelEncoding.prodRightBit,
        BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.boolBit,
        cleanCounterIncrementWork] using h
    · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
      intro bit
      have h :=
        PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
          (detectorCounterIncrementLayout n counterWidth) bit
          (({ x with active := !x.active }, cmpWork),
            cleanCounterIncrementWork counterWidth)
          (by
            intro k
            exact detectorCounterIncrementCarryWorkBit_get_clean
              n counterWidth k ({ x with active := !x.active }) cmpWork)
      simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        detectorCounterIncrementLayout, detectorCounterIncrementCarryWorkWord,
        detectorCounterIncrementCarryWorkBit,
        liftCounterIncrementWorkBitToDetectorCounterWork,
        counterIncrementCarryWorkBit, counterIncrementWorkEncoding,
        BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.finIdentityBit,
        PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding] using h

/-- In the detector-counter workspace, the forward carry stage computes the
propagated natural addition carry for `source + counter`. -/
theorem detectorCounterIncrement_carryStage_get_workCarry_natAddCarry
    (n counterWidth : Nat) (j : Fin (counterWidth - 1))
    (x : RegistersWithDetectorCounterWork n counterWidth)
    (hcarry : (detectorCounterIncrementCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (counterWidth - 1),
        ((detectorCounterIncrementCarryWorkWord n counterWidth).bit k).get x =
          false) :
    ((detectorCounterIncrementCarryWorkWord n counterWidth).bit j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (detectorCounterIncrementLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.2.1.val x.1.1.counter.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (detectorCounterIncrementLayout n counterWidth) x
  change
    ((detectorCounterIncrementCarryWorkWord n counterWidth).bit j).get stage =
      Nat.BinaryArithmetic.natAddCarry
        x.2.1.val x.1.1.counter.val (j.val + 1)
  have hmain : ∀ m, ∀ j : Fin (counterWidth - 1), j.val = m ->
      ((detectorCounterIncrementCarryWorkWord n counterWidth).bit j).get
          stage =
        Nat.BinaryArithmetic.natAddCarry
          x.2.1.val x.1.1.counter.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
            (detectorCounterIncrementLayout n counterWidth) j x hwork
        change
          ((detectorCounterIncrementCarryWorkWord n counterWidth).bit j).get
              stage =
            Nat.BinaryArithmetic.natAddCarry
              x.2.1.val x.1.1.counter.val (j.val + 1)
        change
          ((detectorCounterIncrementLayout n counterWidth).workCarry.bit j).get
              ((detectorCounterIncrementLayout n counterWidth).carryStageIndexStep
                x) =
            Nat.BinaryArithmetic.natAddCarry
              x.2.1.val x.1.1.counter.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (detectorCounterIncrementLayout n counterWidth) x
          rw [hdata]
          have hcarryData : x.2.2.1 = false := by
            simpa [detectorCounterIncrementCarryInBit_get] using hcarry
          simp [detectorCounterIncrementLayout,
            detectorCounterIncrementSourceWord_get_testBit,
            detectorCounterCounterWord_get_testBit,
            detectorCounterIncrementCarryInBit_get, hcarryData,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let p :=
            PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpRec' :
              ((detectorCounterIncrementLayout n counterWidth).workCarry.bit p).get
                  ((detectorCounterIncrementLayout n counterWidth).carryStageIndexStep
                    x) =
                Nat.BinaryArithmetic.natAddCarry
                  x.2.1.val x.1.1.counter.val (p.val + 1) := by
            simpa [stage, detectorCounterIncrementLayout] using hpRec
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          rw [hpRec', hpSucc]
          simp [detectorCounterIncrementLayout,
            detectorCounterIncrementSourceWord_get_testBit,
            detectorCounterCounterWord_get_testBit,
            PlainAdder.Schedule.CarryWorkLayout.lowIndex,
            Nat.BinaryArithmetic.natAddCarry]
  exact hmain j.val j rfl

/-- In the detector-counter workspace, the carry selected before each counter
target sum is the propagated natural addition carry. -/
theorem detectorCounterIncrement_carryBeforeSum_get_natAddCarry
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : RegistersWithDetectorCounterWork n counterWidth)
    (hcarry : (detectorCounterIncrementCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (counterWidth - 1),
        ((detectorCounterIncrementCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
        (detectorCounterIncrementLayout n counterWidth) bit).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (detectorCounterIncrementLayout n counterWidth) x) =
      Nat.BinaryArithmetic.natAddCarry
        x.2.1.val x.1.1.counter.val bit.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : bit.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (detectorCounterIncrementLayout n counterWidth) x
    rw [hdata]
    have hcarryData : x.2.2.1 = false := by
      simpa [detectorCounterIncrementCarryInBit_get] using hcarry
    simp [detectorCounterIncrementLayout,
      detectorCounterIncrementCarryInBit_get, hcarryData,
      Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : bit.val - 1 < counterWidth - 1 := by
      have hbit := bit.isLt
      omega
    let j : Fin (counterWidth - 1) := ⟨bit.val - 1, hjLt⟩
    have hworkCarry :=
      detectorCounterIncrement_carryStage_get_workCarry_natAddCarry
        n counterWidth j x hcarry hwork
    have hjSucc : j.val + 1 = bit.val := by
      dsimp [j]
      omega
    change
      ((detectorCounterIncrementCarryWorkWord n counterWidth).bit j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (detectorCounterIncrementLayout n counterWidth) x) =
        Nat.BinaryArithmetic.natAddCarry
          x.2.1.val x.1.1.counter.val bit.val
    rw [hworkCarry, hjSucc]

/-- On clean counter-increment work, each detector-counter target bit is written
as `counter + 1`. -/
theorem
    detectorCounterTerminatingCounterModeStep_get_counter_add_testBit_of_clean
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n) :
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), cleanCounterIncrementWork counterWidth)).1.1.counter.val.testBit
        bit.val =
      (x.counter + (1 : Word counterWidth)).val.testBit bit.val := by
  let input : RegistersWithDetectorCounterWork n counterWidth :=
    (({ x with active := !x.active }, cmpWork),
      cleanCounterIncrementWork counterWidth)
  have hright :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (detectorCounterIncrementLayout n counterWidth) bit input
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep]
    at hright
  have hcarry :
      (detectorCounterIncrementCarryInBit n counterWidth).get input =
        false := by
    simp [input, detectorCounterIncrementCarryInBit_get,
      cleanCounterIncrementWork]
  have hwork :
      ∀ k : Fin (counterWidth - 1),
        ((detectorCounterIncrementCarryWorkWord n counterWidth).bit k).get
          input = false := by
    intro k
    exact detectorCounterIncrementCarryWorkBit_get_clean
      n counterWidth k ({ x with active := !x.active }) cmpWork
  have hcarryBit :=
    detectorCounterIncrement_carryBeforeSum_get_natAddCarry
      n counterWidth bit input hcarry hwork
  rw [hcarryBit] at hright
  rw [detectorCounterTerminatingCounterModeStep_eq_cleanCarrySum_after_active]
  calc
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
        (detectorCounterIncrementLayout n counterWidth) input).1.1.counter.val.testBit
        bit.val =
        (((x.counter.val.testBit bit.val ^^
              (1 : Word counterWidth).val.testBit bit.val) ^^
            Nat.BinaryArithmetic.natAddCarry
              (1 : Word counterWidth).val x.counter.val bit.val)) := by
      simpa [input, detectorCounterIncrementLayout,
        PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
        detectorCounterCounterWord_get_testBit,
        detectorCounterIncrementSourceWord_get_testBit,
        cleanCounterIncrementWork, Bool.xor_assoc] using hright
    _ = (x.counter + (1 : Word counterWidth)).val.testBit bit.val := by
      simpa [Bool.xor_assoc] using
        (word_add_testBit_eq_xor3 counterWidth
          (1 : Word counterWidth) x.counter bit).symm

/-- On clean counter-increment work, the detector-counter terminating step
increments the concrete padding counter. -/
theorem detectorCounterTerminatingCounterModeStep_counter_of_clean
    (n counterWidth : Nat)
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n) :
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), cleanCounterIncrementWork counterWidth)).1.1.counter =
      wordIncrement counterWidth x.counter := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [detectorCounterTerminatingCounterModeStep_get_counter_add_testBit_of_clean]
  rw [word_add_one_eq_wordIncrement]

/-- On clean counter-increment work, the detector-counter terminating step
preserves the source fields, toggles `active`, increments the padding counter,
and restores its work object. -/
theorem detectorCounterTerminatingCounterModeStep_register_cleanEndpoint_any
    (n counterWidth : Nat)
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n) :
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), cleanCounterIncrementWork counterWidth)).1.1 =
      { x with
        active := !x.active,
        counter := wordIncrement counterWidth x.counter } := by
  let input : RegistersWithDetectorCounterWork n counterWidth :=
    ((x, cmpWork), cleanCounterIncrementWork counterWidth)
  let y := (detectorCounterTerminatingCounterModeStep n counterWidth input).1.1
  have hu : y.u = x.u := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_u n counterWidth input
  have hv : y.v = x.v := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_v n counterWidth input
  have hcompare : y.compare = x.compare := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_compare n counterWidth input
  have hs : y.sCoeff = x.sCoeff := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_sCoeff n counterWidth input
  have hr : y.rCoeff = x.rCoeff := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_rCoeff n counterWidth input
  have hscratchA : y.scratchA = x.scratchA := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_scratchA n counterWidth input
  have hscratchB : y.scratchB = x.scratchB := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_scratchB n counterWidth input
  have hhistory : y.history = x.history := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_history n counterWidth input
  have hactiveOut : y.active = !x.active := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_active
        n counterWidth x cmpWork (cleanCounterIncrementWork counterWidth)
  have hcounter : y.counter = wordIncrement counterWidth x.counter := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_counter_of_clean
        n counterWidth x cmpWork
  change y =
    { x with
      active := !x.active,
      counter := wordIncrement counterWidth x.counter }
  clear_value y
  rcases y with
    ⟨yu, yv, ycompare, ysCoeff, yrCoeff, yscratchA, yscratchB,
      yhistory, yactive, ycounter⟩
  rcases x with
    ⟨xu, xv, xcompare, xsCoeff, xrCoeff, xscratchA, xscratchB,
      xhistory, xactive, xcounter⟩
  change yu = xu at hu
  change yv = xv at hv
  change ycompare = xcompare at hcompare
  change ysCoeff = xsCoeff at hs
  change yrCoeff = xrCoeff at hr
  change yscratchA = xscratchA at hscratchA
  change yscratchB = xscratchB at hscratchB
  change yhistory = xhistory at hhistory
  change yactive = !xactive at hactiveOut
  change ycounter = wordIncrement counterWidth xcounter at hcounter
  simp [hu, hv, hcompare, hs, hr, hscratchA, hscratchB, hhistory,
    hactiveOut, hcounter]

/-- On clean counter-increment work and active input, the detector-counter
terminating step has the expected register endpoint. -/
theorem detectorCounterTerminatingCounterModeStep_register_cleanEndpoint
    (n counterWidth : Nat)
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n)
    (hactive : x.active = true) :
    (detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), cleanCounterIncrementWork counterWidth)).1.1 =
      { x with
        active := false,
        counter := wordIncrement counterWidth x.counter } := by
  let input : RegistersWithDetectorCounterWork n counterWidth :=
    ((x, cmpWork), cleanCounterIncrementWork counterWidth)
  let y := (detectorCounterTerminatingCounterModeStep n counterWidth input).1.1
  have hu : y.u = x.u := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_u n counterWidth input
  have hv : y.v = x.v := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_v n counterWidth input
  have hcompare : y.compare = x.compare := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_compare n counterWidth input
  have hs : y.sCoeff = x.sCoeff := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_sCoeff n counterWidth input
  have hr : y.rCoeff = x.rCoeff := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_rCoeff n counterWidth input
  have hscratchA : y.scratchA = x.scratchA := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_scratchA n counterWidth input
  have hscratchB : y.scratchB = x.scratchB := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_scratchB n counterWidth input
  have hhistory : y.history = x.history := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_history n counterWidth input
  have hactiveOut : y.active = false := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_active_of_active
        n counterWidth x cmpWork (cleanCounterIncrementWork counterWidth)
        hactive
  have hcounter : y.counter = wordIncrement counterWidth x.counter := by
    simpa [y, input] using
      detectorCounterTerminatingCounterModeStep_counter_of_clean
        n counterWidth x cmpWork
  change y =
    { x with
      active := false,
      counter := wordIncrement counterWidth x.counter }
  clear_value y
  rcases y with
    ⟨yu, yv, ycompare, ysCoeff, yrCoeff, yscratchA, yscratchB,
      yhistory, yactive, ycounter⟩
  rcases x with
    ⟨xu, xv, xcompare, xsCoeff, xrCoeff, xscratchA, xscratchB,
      xhistory, xactive, xcounter⟩
  change yu = xu at hu
  change yv = xv at hv
  change ycompare = xcompare at hcompare
  change ysCoeff = xsCoeff at hs
  change yrCoeff = xrCoeff at hr
  change yscratchA = xscratchA at hscratchA
  change yscratchB = xscratchB at hscratchB
  change yhistory = xhistory at hhistory
  change yactive = false at hactiveOut
  change ycounter = wordIncrement counterWidth xcounter at hcounter
  simp [hu, hv, hcompare, hs, hr, hscratchA, hscratchB, hhistory,
    hactiveOut, hcounter]

/-- Full clean endpoint for the detector-counter terminating step. -/
theorem detectorCounterTerminatingCounterModeStep_cleanEndpoint
    (n counterWidth : Nat)
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n)
    (hactive : x.active = true) :
    detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), cleanCounterIncrementWork counterWidth) =
      (({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter }, cmpWork),
        cleanCounterIncrementWork counterWidth) := by
  exact Prod.ext
    (Prod.ext
      (detectorCounterTerminatingCounterModeStep_register_cleanEndpoint
        n counterWidth x cmpWork hactive)
      (detectorCounterTerminatingCounterModeStep_comparisonWork
        n counterWidth x cmpWork (cleanCounterIncrementWork counterWidth)))
    (detectorCounterTerminatingCounterModeStep_counterWork_clean
      n counterWidth x cmpWork)

/-- On clean counter-increment work and inactive input, the detector-counter
terminating step flips `active` on and increments the padding counter.  This is
the local obstruction that prevents using the clean-restoring total selector as
the concrete route without additional path/control information. -/
theorem detectorCounterTerminatingCounterModeStep_cleanEndpoint_of_inactive
    (n counterWidth : Nat)
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n)
    (hactive : x.active = false) :
    detectorCounterTerminatingCounterModeStep n counterWidth
        ((x, cmpWork), cleanCounterIncrementWork counterWidth) =
      (({ x with
          active := true,
          counter := wordIncrement counterWidth x.counter }, cmpWork),
        cleanCounterIncrementWork counterWidth) := by
  exact Prod.ext
    (Prod.ext
      (by
        simpa [hactive] using
          detectorCounterTerminatingCounterModeStep_register_cleanEndpoint_any
            n counterWidth x cmpWork)
      (detectorCounterTerminatingCounterModeStep_comparisonWork
        n counterWidth x cmpWork (cleanCounterIncrementWork counterWidth)))
    (detectorCounterTerminatingCounterModeStep_counterWork_clean
      n counterWidth x cmpWork)

/-- The terminating counter-mode gate list is disjoint from the staged compare
control bit. -/
theorem detectorCounterTerminatingCounterModeGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ detectorCounterTerminatingCounterModeGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (detectorCounterCompareBit n counterWidth) gate := by
  intro gate hmem
  simp only [detectorCounterTerminatingCounterModeGates, List.mem_append,
    List.mem_singleton] at hmem
  rcases hmem with hactive | hinc
  · subst gate
    simp only [EncodedBit.GateSpec.bitDisjoint]
    exact liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
      n counterWidth (liftedActiveBit n counterWidth)
      (liftedCompareBit n counterWidth)
      (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth))
  · exact
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
        (detectorCounterIncrementLayout n counterWidth)
        (detectorCounterCompareBit n counterWidth)
        (fun i =>
          Ne.symm
            (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
              n counterWidth (liftedCompareBit n counterWidth)
              (counterIncrementSourceBit counterWidth i)))
        (fun i =>
          liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
            n counterWidth
            (liftRegisterBitToComparisonWork n counterWidth
              (RegisterBits.counterBit n counterWidth
                (WireAddress.littleEndianWire i)))
            (liftedCompareBit n counterWidth)
            (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
              (RegisterBits.counterBit n counterWidth
                (WireAddress.littleEndianWire i))
              (RegisterBits.compareBit n counterWidth)
              (Ne.symm
                (RegisterBits.compare_counter_wire_ne n counterWidth
                  (WireAddress.littleEndianWire i)))))
        (Ne.symm
          (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
            n counterWidth (liftedCompareBit n counterWidth)
            (counterIncrementCarryInBit counterWidth)))
        (fun j =>
          Ne.symm
            (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
              n counterWidth (liftedCompareBit n counterWidth)
              (counterIncrementCarryWorkBit counterWidth j)))
        gate hinc

/-- The terminating counter-mode gate list is disjoint from a selected clean
comparison-work bit, used as the extra control-work bit. -/
theorem detectorCounterTerminatingCounterModeGates_bitDisjoint_comparisonCarry
    (n counterWidth : Nat) (workBit : Fin n) :
    ∀ gate, gate ∈ detectorCounterTerminatingCounterModeGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint
        (detectorCounterComparisonCarryBit n counterWidth workBit) gate := by
  intro gate hmem
  simp only [detectorCounterTerminatingCounterModeGates, List.mem_append,
    List.mem_singleton] at hmem
  rcases hmem with hactive | hinc
  · subst gate
    simp only [EncodedBit.GateSpec.bitDisjoint]
    exact liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
      n counterWidth (liftedActiveBit n counterWidth)
      (liftedComparisonCarryBit n counterWidth workBit)
      (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (comparisonCarryValueBit n workBit))
  · exact
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_bitDisjoint
        (detectorCounterIncrementLayout n counterWidth)
        (detectorCounterComparisonCarryBit n counterWidth workBit)
        (fun i =>
          Ne.symm
            (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
              n counterWidth (liftedComparisonCarryBit n counterWidth workBit)
              (counterIncrementSourceBit counterWidth i)))
        (fun i =>
          liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
            n counterWidth
            (liftRegisterBitToComparisonWork n counterWidth
              (RegisterBits.counterBit n counterWidth
                (WireAddress.littleEndianWire i)))
            (liftedComparisonCarryBit n counterWidth workBit)
            (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
              (RegisterBits.counterBit n counterWidth
                (WireAddress.littleEndianWire i))
              (comparisonCarryValueBit n workBit)))
        (Ne.symm
          (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
            n counterWidth (liftedComparisonCarryBit n counterWidth workBit)
            (counterIncrementCarryInBit counterWidth)))
        (fun j =>
          Ne.symm
            (liftComparisonStateBit_liftDetectorCounterWorkBit_wire_ne
              n counterWidth (liftedComparisonCarryBit n counterWidth workBit)
              (counterIncrementCarryWorkBit counterWidth j)))
        gate hinc

/-- Compare and a selected comparison-work carry bit are distinct in the
detector-plus-counter workspace. -/
theorem detectorCounterCompareBit_comparisonCarryBit_wire_ne
    (n counterWidth : Nat) (workBit : Fin n) :
    (detectorCounterCompareBit n counterWidth).wire ≠
      (detectorCounterComparisonCarryBit n counterWidth workBit).wire :=
  liftComparisonStateBit_detectorCounter_liftComparisonStateBit_wire_ne
    n counterWidth (liftedCompareBit n counterWidth)
    (liftedComparisonCarryBit n counterWidth workBit)
    (liftedCompare_liftedComparisonCarry_wire_ne n counterWidth workBit)

/-- Compare-controlled terminating counter-mode gate list.  The control is
computed by the surrounding detector, and the final comparison-carry bit is used
as the clean control-work bit. -/
def detectorCounterControlledTerminatingCounterModeGates
    (tail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (detectorCounterCompareBit tail.succ counterWidth)
    (detectorCounterComparisonCarryBit tail.succ counterWidth (Fin.last tail))
    (detectorCounterTerminatingCounterModeGates tail.succ counterWidth)
    (detectorCounterTerminatingCounterModeGates_bitDisjoint_compare
      tail.succ counterWidth)
    (detectorCounterTerminatingCounterModeGates_bitDisjoint_comparisonCarry
      tail.succ counterWidth (Fin.last tail))
    (detectorCounterCompareBit_comparisonCarryBit_wire_ne
      tail.succ counterWidth (Fin.last tail))

/-- Semantic action for the compare-controlled terminating counter-mode list. -/
def detectorCounterControlledTerminatingCounterModeStep
    (tail counterWidth : Nat) :
    RegistersWithDetectorCounterWork tail.succ counterWidth ->
      RegistersWithDetectorCounterWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (detectorCounterControlledTerminatingCounterModeGates tail counterWidth)

/-- Actual circuit for the compare-controlled terminating counter mode. -/
def detectorCounterControlledTerminatingCounterModeProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical ((registersWithDetectorCounterWorkEncoding
        tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (detectorCounterControlledTerminatingCounterModeGates tail counterWidth)

/-- The compare-controlled circuit realizes its gate-list action. -/
theorem detectorCounterControlledTerminatingCounterMode_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)
      (detectorCounterControlledTerminatingCounterModeProgram
        tail counterWidth)
      (detectorCounterControlledTerminatingCounterModeStep tail counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (detectorCounterControlledTerminatingCounterModeGates tail counterWidth)

/-- If compare is false, the compare-controlled terminating counter mode is a
no-op. -/
theorem
    detectorCounterControlledTerminatingCounterModeStep_eq_self_of_compare_false
    (tail counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork tail.succ counterWidth)
    (hcompare :
      (detectorCounterCompareBit tail.succ counterWidth).get x = false) :
    detectorCounterControlledTerminatingCounterModeStep tail counterWidth x =
      x := by
  simpa [detectorCounterControlledTerminatingCounterModeStep,
    detectorCounterControlledTerminatingCounterModeGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (detectorCounterCompareBit tail.succ counterWidth)
      (detectorCounterComparisonCarryBit tail.succ counterWidth (Fin.last tail))
      (detectorCounterTerminatingCounterModeGates tail.succ counterWidth)
      (detectorCounterTerminatingCounterModeGates_bitDisjoint_compare
        tail.succ counterWidth)
      (detectorCounterTerminatingCounterModeGates_bitDisjoint_comparisonCarry
        tail.succ counterWidth (Fin.last tail))
      (detectorCounterCompareBit_comparisonCarryBit_wire_ne
        tail.succ counterWidth (Fin.last tail))
      x hcompare

/-- If compare is true and the selected comparison-work bit is clean, the
compare-controlled wrapper acts like the terminating counter-mode gate list. -/
theorem
    detectorCounterControlledTerminatingCounterModeStep_eq_terminating_of_compare_true
    (tail counterWidth : Nat)
    (x : RegistersWithDetectorCounterWork tail.succ counterWidth)
    (hcompare :
      (detectorCounterCompareBit tail.succ counterWidth).get x = true)
    (hwork :
      (detectorCounterComparisonCarryBit tail.succ counterWidth
        (Fin.last tail)).get x = false) :
    detectorCounterControlledTerminatingCounterModeStep tail counterWidth x =
      detectorCounterTerminatingCounterModeStep tail.succ counterWidth x := by
  simpa [detectorCounterControlledTerminatingCounterModeStep,
    detectorCounterControlledTerminatingCounterModeGates,
    detectorCounterTerminatingCounterModeStep,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (detectorCounterCompareBit tail.succ counterWidth)
      (detectorCounterComparisonCarryBit tail.succ counterWidth (Fin.last tail))
      (detectorCounterTerminatingCounterModeGates tail.succ counterWidth)
      (detectorCounterTerminatingCounterModeGates_bitDisjoint_compare
        tail.succ counterWidth)
      (detectorCounterTerminatingCounterModeGates_bitDisjoint_comparisonCarry
        tail.succ counterWidth (Fin.last tail))
      (detectorCounterCompareBit_comparisonCarryBit_wire_ne
        tail.succ counterWidth (Fin.last tail))
      x hcompare hwork

/-- Complete detector-gated terminating counter-mode wrapper: compute `v = 0`
into compare, run the compare-controlled terminating counter-mode action, then
run the same detector again to clean compare and comparison work. -/
def detectorGatedTerminatingCounterModeWithWorkStep
    (tail counterWidth : Nat) :
    RegistersWithDetectorCounterWork tail.succ counterWidth ->
      RegistersWithDetectorCounterWork tail.succ counterWidth :=
  fun x =>
    detectorCounterVZeroDetectorStep tail.succ counterWidth
      (detectorCounterControlledTerminatingCounterModeStep tail counterWidth
        (detectorCounterVZeroDetectorStep tail.succ counterWidth x))

/-- Actual circuit for the complete detector-gated terminating counter mode. -/
def detectorGatedTerminatingCounterModeWithWorkProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithDetectorCounterWorkEncoding tail.succ counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (detectorCounterVZeroDetectorProgram tail.succ counterWidth)
    (UnitaryCircuit.seq
      (detectorCounterControlledTerminatingCounterModeProgram
        tail counterWidth)
      (detectorCounterVZeroDetectorProgram tail.succ counterWidth))

/-- The complete detector-gated terminating counter mode is realized by a single
composed base-gate program. -/
theorem detectorGatedTerminatingCounterModeWithWork_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)
      (detectorGatedTerminatingCounterModeWithWorkProgram tail counterWidth)
      (detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth) := by
  change UnitaryCircuit.Realizes
    (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)
    (UnitaryCircuit.seq
      (detectorCounterVZeroDetectorProgram tail.succ counterWidth)
      (UnitaryCircuit.seq
        (detectorCounterControlledTerminatingCounterModeProgram
          tail counterWidth)
        (detectorCounterVZeroDetectorProgram tail.succ counterWidth)))
    (fun x =>
      detectorCounterVZeroDetectorStep tail.succ counterWidth
        (detectorCounterControlledTerminatingCounterModeStep tail counterWidth
          (detectorCounterVZeroDetectorStep tail.succ counterWidth x)))
  exact UnitaryCircuit.Realizes.seq
    (firstStep := detectorCounterVZeroDetectorStep tail.succ counterWidth)
    (secondStep := fun y =>
      detectorCounterVZeroDetectorStep tail.succ counterWidth
        (detectorCounterControlledTerminatingCounterModeStep
          tail counterWidth y))
    (detectorCounterVZeroDetector_realizes tail.succ counterWidth)
    (UnitaryCircuit.Realizes.seq
      (firstStep :=
        detectorCounterControlledTerminatingCounterModeStep tail counterWidth)
      (secondStep := detectorCounterVZeroDetectorStep tail.succ counterWidth)
      (detectorCounterControlledTerminatingCounterMode_realizes
        tail counterWidth)
      (detectorCounterVZeroDetector_realizes tail.succ counterWidth))

/-- The detector-gated terminating counter mode lifted to the full fixed-round
workspace, preserving the coefficient-adder work. -/
def fullRoundWorkTerminatingStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    (fullRoundWorkDetectorEquiv tail.succ counterWidth).symm
      (detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
          ((fullRoundWorkDetectorEquiv tail.succ counterWidth x).1),
        (fullRoundWorkDetectorEquiv tail.succ counterWidth x).2)

/-- Actual circuit for the detector-gated terminating counter mode after
lifting it across the coefficient-adder work in the detector/counter-native
layout. -/
def fullRoundWorkTerminatingProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical (((BinaryLabelEncoding.prod
        (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)
        (coeffAdderWorkEncoding tail.succ)).relabel
          (fullRoundWorkDetectorEquiv tail.succ counterWidth)).width)).toQuantum :=
  UnitaryCircuit.onBinaryPrefix
    (coeffAdderWorkEncoding tail.succ).width
    (detectorGatedTerminatingCounterModeWithWorkProgram tail counterWidth)

/-- The native-layout lifted circuit realizes the full-round terminating
semantic update after relabeling only the data carrier. -/
theorem fullRoundWorkTerminating_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      ((BinaryLabelEncoding.prod
        (registersWithDetectorCounterWorkEncoding tail.succ counterWidth)
        (coeffAdderWorkEncoding tail.succ)).relabel
          (fullRoundWorkDetectorEquiv tail.succ counterWidth))
      (fullRoundWorkTerminatingProgram tail counterWidth)
      (fullRoundWorkTerminatingStep tail counterWidth) := by
  exact UnitaryCircuit.Realizes.relabel
    (fullRoundWorkDetectorEquiv tail.succ counterWidth)
    (UnitaryCircuit.Realizes.onBinaryPrefix
      (right := coeffAdderWorkEncoding tail.succ)
      (detectorGatedTerminatingCounterModeWithWork_realizes
        tail counterWidth))

/-- Standard-layout view of the lifted terminating counter-mode step.  This is
the same semantic update as `fullRoundWorkTerminatingStep`, but expressed as an
action on the outer comparison/counter product with coefficient-adder work
inserted in the middle. -/
def fullRoundWorkTerminatingStandardLayoutStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    let y :=
      detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
        (x.1.1, x.2)
    ((y.1, x.1.2), y.2)

theorem fullRoundWorkTerminatingStandardLayoutStep_eq
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    fullRoundWorkTerminatingStandardLayoutStep tail counterWidth x =
      fullRoundWorkTerminatingStep tail counterWidth x := by
  rcases x with ⟨⟨regs, coeffWork⟩, counterWork⟩
  rfl

/-- Actual circuit for the terminating counter-mode step under the standard
full-round work encoding. -/
def fullRoundWorkTerminatingStandardLayoutProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithFullRoundWorkEncoding tail.succ counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryMiddle
    (leftWidth :=
      (registersWithComparisonWorkEncoding tail.succ counterWidth).width)
    (middleWidth := (coeffAdderWorkEncoding tail.succ).width)
    (rightWidth := (counterIncrementWorkEncoding counterWidth).width)
    (detectorGatedTerminatingCounterModeWithWorkProgram tail counterWidth)

/-- The standard-layout terminating circuit realizes the same full-round
semantic update. -/
theorem fullRoundWorkTerminatingStandardLayout_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkTerminatingStandardLayoutProgram tail counterWidth)
      (fullRoundWorkTerminatingStep tail counterWidth) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.onBinaryMiddle
      (left := registersWithComparisonWorkEncoding tail.succ counterWidth)
      (middle := coeffAdderWorkEncoding tail.succ)
      (right := counterIncrementWorkEncoding counterWidth)
      (detectorGatedTerminatingCounterModeWithWork_realizes
        tail counterWidth))
  exact fullRoundWorkTerminatingStandardLayoutStep_eq tail counterWidth

/-- Under the detector/counter native layout, the lifted terminating
full-round step projects to the detector-gated terminating counter-mode step. -/
theorem fullRoundWorkTerminatingStep_detectorCounterProjection
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkDetectorEquiv tail.succ counterWidth
        (fullRoundWorkTerminatingStep tail counterWidth x)).1 =
      detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
        ((fullRoundWorkDetectorEquiv tail.succ counterWidth x).1) := by
  rcases x with ⟨⟨regs, coeffWork⟩, counterWork⟩
  rfl

/-- Under the detector/counter native layout, the lifted terminating
full-round step preserves the coefficient-adder work component. -/
theorem fullRoundWorkTerminatingStep_coeffWorkProjection
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkDetectorEquiv tail.succ counterWidth
        (fullRoundWorkTerminatingStep tail counterWidth x)).2 =
      (fullRoundWorkDetectorEquiv tail.succ counterWidth x).2 := by
  rcases x with ⟨⟨regs, coeffWork⟩, counterWork⟩
  rfl

/-- In the standard full-round product view, the lifted terminating step leaves
the coefficient-adder work unchanged. -/
theorem fullRoundWorkTerminatingStep_preservesCoeffAdderWork
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkTerminatingStep tail counterWidth x).1.2 = x.1.2 := by
  rcases x with ⟨⟨regs, coeffWork⟩, counterWork⟩
  rfl

/-- On clean detector work, if `v = 0`, the detector-gated wrapper runs the
terminating counter-mode path between detector compute and uncompute. -/
theorem
    detectorGatedTerminatingCounterModeWithWorkStep_eq_terminating_path_of_v_zero
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (work : CounterIncrementWork counterWidth)
    (hcompare : x.compare = false)
    (hv : x.v.val = 0) :
    detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
        ((x, cleanComparisonWork tail.succ), work) =
      detectorCounterVZeroDetectorStep tail.succ counterWidth
        (detectorCounterTerminatingCounterModeStep tail.succ counterWidth
          (detectorCounterVZeroDetectorStep tail.succ counterWidth
            ((x, cleanComparisonWork tail.succ), work))) := by
  have hworkClean :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get
          (x, cleanComparisonWork tail.succ) = false := by
    intro bit
    change
      (comparisonCarryValueBit tail.succ bit).get
        (cleanComparisonWork tail.succ) = false
    exact comparisonCarryValueBit_clean tail.succ bit
  have hdetCompare :=
    vZeroDetectorWithComparisonWorkStep_get_compare_clean_xor
      tail counterWidth (x, cleanComparisonWork tail.succ) hworkClean
  have hcompareAfter :
      (detectorCounterCompareBit tail.succ counterWidth).get
          (detectorCounterVZeroDetectorStep tail.succ counterWidth
            ((x, cleanComparisonWork tail.succ), work)) = true := by
    change
      (liftedCompareBit tail.succ counterWidth).get
          (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
            (x, cleanComparisonWork tail.succ)) = true
    rw [hdetCompare]
    simp [liftedCompareBit, liftRegisterBitToComparisonWork,
      BinaryLabelEncoding.prodLeftBit, hcompare, hv]
  have hdetWork :=
    vZeroDetectorWithComparisonWorkStep_work_clean
      tail counterWidth x hcompare
  have hworkAfter :
      (detectorCounterComparisonCarryBit tail.succ counterWidth
        (Fin.last tail)).get
          (detectorCounterVZeroDetectorStep tail.succ counterWidth
            ((x, cleanComparisonWork tail.succ), work)) = false := by
    change
      (comparisonCarryValueBit tail.succ (Fin.last tail)).get
          (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
            (x, cleanComparisonWork tail.succ)).2 = false
    rw [hdetWork]
    exact comparisonCarryValueBit_clean tail.succ (Fin.last tail)
  rw [detectorGatedTerminatingCounterModeWithWorkStep]
  rw [detectorCounterControlledTerminatingCounterModeStep_eq_terminating_of_compare_true
    tail counterWidth
    (detectorCounterVZeroDetectorStep tail.succ counterWidth
      ((x, cleanComparisonWork tail.succ), work))
    hcompareAfter hworkAfter]

/-- On clean detector work, if `v ≠ 0`, the detector-gated wrapper does not run
the terminating counter-mode path. -/
theorem
    detectorGatedTerminatingCounterModeWithWorkStep_eq_double_detector_of_v_nonzero
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (work : CounterIncrementWork counterWidth)
    (hcompare : x.compare = false)
    (hv : x.v.val ≠ 0) :
    detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
        ((x, cleanComparisonWork tail.succ), work) =
      detectorCounterVZeroDetectorStep tail.succ counterWidth
        (detectorCounterVZeroDetectorStep tail.succ counterWidth
          ((x, cleanComparisonWork tail.succ), work)) := by
  have hworkClean :
      ∀ bit : Fin tail.succ,
        (liftedComparisonCarryBit tail.succ counterWidth bit).get
          (x, cleanComparisonWork tail.succ) = false := by
    intro bit
    change
      (comparisonCarryValueBit tail.succ bit).get
        (cleanComparisonWork tail.succ) = false
    exact comparisonCarryValueBit_clean tail.succ bit
  have hdetCompare :=
    vZeroDetectorWithComparisonWorkStep_get_compare_clean_xor
      tail counterWidth (x, cleanComparisonWork tail.succ) hworkClean
  have hcompareAfter :
      (detectorCounterCompareBit tail.succ counterWidth).get
          (detectorCounterVZeroDetectorStep tail.succ counterWidth
            ((x, cleanComparisonWork tail.succ), work)) = false := by
    change
      (liftedCompareBit tail.succ counterWidth).get
          (vZeroDetectorWithComparisonWorkStep tail.succ counterWidth
            (x, cleanComparisonWork tail.succ)) = false
    rw [hdetCompare]
    simp [liftedCompareBit, liftRegisterBitToComparisonWork,
      BinaryLabelEncoding.prodLeftBit, hcompare, hv]
  rw [detectorGatedTerminatingCounterModeWithWorkStep]
  rw [detectorCounterControlledTerminatingCounterModeStep_eq_self_of_compare_false
    tail counterWidth
    (detectorCounterVZeroDetectorStep tail.succ counterWidth
      ((x, cleanComparisonWork tail.succ), work))
    hcompareAfter]

/-- Clean endpoint for the complete detector-gated terminating counter mode in
the concrete `v = 0` case. -/
theorem
    detectorGatedTerminatingCounterModeWithWorkStep_cleanEndpoint_of_v_zero
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0) :
    detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
        ((x, cleanComparisonWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      (({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [detectorGatedTerminatingCounterModeWithWorkStep_eq_terminating_path_of_v_zero
    tail counterWidth x (cleanCounterIncrementWork counterWidth)
    hcompare hvZero]
  rw [detectorCounterVZeroDetectorStep_cleanEndpoint]
  let xDetected : Registers tail.succ counterWidth :=
    { x with compare := x.compare ^^ decide (x.v.val = 0) }
  have hactiveDetected : xDetected.active = true := by
    simp [xDetected, hactive]
  rw [detectorCounterTerminatingCounterModeStep_cleanEndpoint
    tail.succ counterWidth xDetected (cleanComparisonWork tail.succ)
    hactiveDetected]
  rw [detectorCounterVZeroDetectorStep_cleanEndpoint]
  simp [xDetected, hcompare, hvZero]

/-- On inactive clean `v = 0` inputs, the detector-gated terminating prefix
still runs the terminating counter-mode action, which flips `active` on.  This
captures why the surrounding total route needs original-active/path
information rather than a clean-restoring semantic target. -/
theorem
    detectorGatedTerminatingCounterModeWithWorkStep_cleanEndpoint_of_v_zero_inactive
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = false)
    (hvZero : x.v.val = 0) :
    detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
        ((x, cleanComparisonWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      (({ x with
          active := true,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [detectorGatedTerminatingCounterModeWithWorkStep_eq_terminating_path_of_v_zero
    tail counterWidth x (cleanCounterIncrementWork counterWidth)
    hcompare hvZero]
  rw [detectorCounterVZeroDetectorStep_cleanEndpoint]
  let xDetected : Registers tail.succ counterWidth :=
    { x with compare := x.compare ^^ decide (x.v.val = 0) }
  have hactiveDetected : xDetected.active = false := by
    simp [xDetected, hactive]
  rw [detectorCounterTerminatingCounterModeStep_cleanEndpoint_of_inactive
    tail.succ counterWidth xDetected (cleanComparisonWork tail.succ)
    hactiveDetected]
  rw [detectorCounterVZeroDetectorStep_cleanEndpoint]
  simp [xDetected, hcompare, hvZero]

/-- Clean endpoint for the complete detector-gated terminating counter mode in
the concrete `v ≠ 0` case: the detector compute/uncompute pair restores the
input and the terminating counter mode is skipped. -/
theorem
    detectorGatedTerminatingCounterModeWithWorkStep_cleanEndpoint_of_v_nonzero
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hvNonzero : x.v.val ≠ 0) :
    detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
        ((x, cleanComparisonWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((x, cleanComparisonWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [detectorGatedTerminatingCounterModeWithWorkStep_eq_double_detector_of_v_nonzero
    tail counterWidth x (cleanCounterIncrementWork counterWidth)
    hcompare hvNonzero]
  rw [detectorCounterVZeroDetectorStep_cleanEndpoint]
  rw [detectorCounterVZeroDetectorStep_cleanEndpoint]
  cases x
  simp at hcompare ⊢

/-- Clean endpoint for the full-workspace lifted terminating counter mode in
the concrete `v = 0` case; the coefficient-adder work is preserved. -/
theorem fullRoundWorkTerminatingStep_cleanEndpoint_of_v_zero
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0) :
    fullRoundWorkTerminatingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkTerminatingStep]
  change
    (fullRoundWorkDetectorEquiv tail.succ counterWidth).symm
        (detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
            ((x, cleanComparisonWork tail.succ),
              cleanCounterIncrementWork counterWidth),
          cleanCoeffAdderWork tail.succ) =
      ((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
  rw [detectorGatedTerminatingCounterModeWithWorkStep_cleanEndpoint_of_v_zero
    tail counterWidth x hcompare hactive hvZero]
  rfl

/-- On inactive clean `v = 0` inputs, the full-workspace terminating prefix
flips `active` on while preserving coefficient-adder work.  The outer aggregate
route cannot use this prefix unconditionally without retaining original-active
control information. -/
theorem fullRoundWorkTerminatingStep_cleanEndpoint_of_v_zero_inactive
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = false)
    (hvZero : x.v.val = 0) :
    fullRoundWorkTerminatingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with
          active := true,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkTerminatingStep]
  change
    (fullRoundWorkDetectorEquiv tail.succ counterWidth).symm
        (detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
            ((x, cleanComparisonWork tail.succ),
              cleanCounterIncrementWork counterWidth),
          cleanCoeffAdderWork tail.succ) =
      ((({ x with
          active := true,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
  rw [
    detectorGatedTerminatingCounterModeWithWorkStep_cleanEndpoint_of_v_zero_inactive
      tail counterWidth x hcompare hactive hvZero]
  rfl

/-- Clean endpoint for the full-workspace lifted terminating counter mode in
the concrete `v ≠ 0` case: the terminating detector wrapper is a no-op and the
full-round work object is restored. -/
theorem fullRoundWorkTerminatingStep_cleanEndpoint_of_v_nonzero
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hvNonzero : x.v.val ≠ 0) :
    fullRoundWorkTerminatingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkTerminatingStep]
  change
    (fullRoundWorkDetectorEquiv tail.succ counterWidth).symm
        (detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
            ((x, cleanComparisonWork tail.succ),
              cleanCounterIncrementWork counterWidth),
          cleanCoeffAdderWork tail.succ) =
      (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
  rw [detectorGatedTerminatingCounterModeWithWorkStep_cleanEndpoint_of_v_nonzero
    tail counterWidth x hcompare hvNonzero]
  rfl

/-- Gate list that computes the second RNSL17 branch condition into the
comparison ancilla.  On clean compare it stages `uBit && !vBit`, i.e. the
`u`-odd and `v`-even selector condition for the `vEven` branch; it is not the
full branch selector [RNSL17, ECDLP.tex:399-421,468-475]. -/
def uOddVBitNotToCompareGates
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  [ EncodedBit.GateSpec.x (RegisterBits.vBit n counterWidth vIndex)
  , EncodedBit.GateSpec.toffoli
      (RegisterBits.uBit n counterWidth uIndex)
      (RegisterBits.vBit n counterWidth vIndex)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.u_v_wire_ne n counterWidth uIndex vIndex)
      (RegisterBits.u_compare_wire_ne n counterWidth uIndex)
      (RegisterBits.v_compare_wire_ne n counterWidth vIndex)
  , EncodedBit.GateSpec.x (RegisterBits.vBit n counterWidth vIndex) ]

/-- Base-gate program for staging `uBit && !vBit` into compare. -/
def uOddVBitNotToCompareProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uOddVBitNotToCompareGates n counterWidth uIndex vIndex)

/-- Semantic step for staging `uBit && !vBit` into compare. -/
def uOddVBitNotToCompareStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uOddVBitNotToCompareGates n counterWidth uIndex vIndex)

/-- The `u`-odd/`v`-even condition staging program is a concrete encoded-bit
base-gate realization over the Montgomery--Kaliski register layout. -/
theorem uOddVBitNotToCompare_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (uOddVBitNotToCompareProgram n counterWidth uIndex vIndex)
      (uOddVBitNotToCompareStep n counterWidth uIndex vIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uOddVBitNotToCompareGates n counterWidth uIndex vIndex)

/-- Staging toggles compare by `uBit && !vBit`. -/
theorem uOddVBitNotToCompareStep_get_compare
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.compareBit n counterWidth).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      ((RegisterBits.compareBit n counterWidth).get x ^^
        ((RegisterBits.uBit n counterWidth uIndex).get x &&
          !(RegisterBits.vBit n counterWidth vIndex).get x)) := by
  let sourceU := RegisterBits.uBit n counterWidth uIndex
  let sourceV := RegisterBits.vBit n counterWidth vIndex
  let compare := RegisterBits.compareBit n counterWidth
  change compare.get
      (sourceV.flip
        (EncodedBit.toffoliStep sourceU sourceV compare
          (sourceV.flip x))) =
    (compare.get x ^^ (sourceU.get x && !sourceV.get x))
  rw [EncodedBit.get_flip_of_wire_ne sourceV compare
    (RegisterBits.v_compare_wire_ne n counterWidth vIndex)]
  rw [EncodedBit.toffoliStep_get_target]
  rw [EncodedBit.get_flip_of_wire_ne sourceV compare
    (RegisterBits.v_compare_wire_ne n counterWidth vIndex)]
  rw [EncodedBit.get_flip_of_wire_ne sourceV sourceU
    (Ne.symm (RegisterBits.u_v_wire_ne n counterWidth uIndex vIndex))]
  rw [EncodedBit.get_flip_self]

/-- On a clean comparison ancilla, staging computes `uBit && !vBit`. -/
theorem uOddVBitNotToCompareStep_get_compare_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth)
    (hclean : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.compareBit n counterWidth).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      ((RegisterBits.uBit n counterWidth uIndex).get x &&
        !(RegisterBits.vBit n counterWidth vIndex).get x) := by
  rw [uOddVBitNotToCompareStep_get_compare]
  have hcleanValue : x.compare = false := by
    simpa using hclean
  cases (RegisterBits.uBit n counterWidth uIndex).get x <;>
    cases (RegisterBits.vBit n counterWidth vIndex).get x <;>
      simp [hcleanValue]

/-- Staging `uBit && !vBit` preserves the selected `u` bit. -/
theorem uOddVBitNotToCompareStep_get_uBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uBit n counterWidth uIndex).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.uBit n counterWidth uIndex).get x := by
  let sourceU := RegisterBits.uBit n counterWidth uIndex
  let sourceV := RegisterBits.vBit n counterWidth vIndex
  let compare := RegisterBits.compareBit n counterWidth
  change sourceU.get
      (sourceV.flip
        (EncodedBit.toffoliStep sourceU sourceV compare
          (sourceV.flip x))) =
    sourceU.get x
  rw [EncodedBit.get_flip_of_wire_ne sourceV sourceU
    (Ne.symm (RegisterBits.u_v_wire_ne n counterWidth uIndex vIndex))]
  rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
    sourceU (Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth uIndex))]
  exact EncodedBit.get_flip_of_wire_ne sourceV sourceU
    (Ne.symm (RegisterBits.u_v_wire_ne n counterWidth uIndex vIndex)) x

/-- Staging `uBit && !vBit` preserves every little-endian `u` value bit. -/
theorem uOddVBitNotToCompareStep_get_uWordBit
    (n counterWidth : Nat) (uIndex vIndex targetBit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uValueBit n counterWidth targetBit).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.uValueBit n counterWidth targetBit).get x := by
  by_cases htarget : WireAddress.littleEndianWire targetBit = uIndex
  · simpa [RegisterBits.uValueBit, htarget] using
      uOddVBitNotToCompareStep_get_uBit n counterWidth uIndex vIndex x
  · let sourceU := RegisterBits.uBit n counterWidth uIndex
    let sourceV := RegisterBits.vBit n counterWidth vIndex
    let compare := RegisterBits.compareBit n counterWidth
    let observed := RegisterBits.uValueBit n counterWidth targetBit
    have hsourceVObserved : sourceV.wire ≠ observed.wire := by
      simpa [sourceV, observed, RegisterBits.uValueBit] using
        Ne.symm (RegisterBits.u_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit) vIndex)
    have hcompareObserved : compare.wire ≠ observed.wire := by
      simpa [compare, observed, RegisterBits.uValueBit] using
        Ne.symm (RegisterBits.u_compare_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit))
    change observed.get
        (sourceV.flip
          (EncodedBit.toffoliStep sourceU sourceV compare
            (sourceV.flip x))) =
      observed.get x
    rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]
    rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
      observed hcompareObserved]
    rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]

/-- Staging `uBit && !vBit` restores the selected `v` bit. -/
theorem uOddVBitNotToCompareStep_get_vBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vBit n counterWidth vIndex).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.vBit n counterWidth vIndex).get x := by
  let sourceU := RegisterBits.uBit n counterWidth uIndex
  let sourceV := RegisterBits.vBit n counterWidth vIndex
  let compare := RegisterBits.compareBit n counterWidth
  change sourceV.get
      (sourceV.flip
        (EncodedBit.toffoliStep sourceU sourceV compare
          (sourceV.flip x))) =
    sourceV.get x
  rw [EncodedBit.get_flip_self]
  rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
    sourceV (Ne.symm (RegisterBits.v_compare_wire_ne n counterWidth vIndex))]
  rw [EncodedBit.get_flip_self]
  cases sourceV.get x <;> simp

/-- Staging `uBit && !vBit` restores every little-endian `v` value bit. -/
theorem uOddVBitNotToCompareStep_get_vWordBit
    (n counterWidth : Nat) (uIndex vIndex targetBit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vValueBit n counterWidth targetBit).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.vValueBit n counterWidth targetBit).get x := by
  by_cases htarget : WireAddress.littleEndianWire targetBit = vIndex
  · simpa [RegisterBits.vValueBit, htarget] using
      uOddVBitNotToCompareStep_get_vBit n counterWidth uIndex vIndex x
  · let sourceU := RegisterBits.uBit n counterWidth uIndex
    let sourceV := RegisterBits.vBit n counterWidth vIndex
    let compare := RegisterBits.compareBit n counterWidth
    let observed := RegisterBits.vValueBit n counterWidth targetBit
    have hsourceVObserved : sourceV.wire ≠ observed.wire := by
      simpa [sourceV, observed, RegisterBits.vValueBit] using
        v_v_wire_ne n counterWidth vIndex
          (WireAddress.littleEndianWire targetBit) (Ne.symm htarget)
    have hcompareObserved : compare.wire ≠ observed.wire := by
      simpa [compare, observed, RegisterBits.vValueBit] using
        Ne.symm (RegisterBits.v_compare_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit))
    change observed.get
        (sourceV.flip
          (EncodedBit.toffoliStep sourceU sourceV compare
            (sourceV.flip x))) =
      observed.get x
    rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]
    rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
      observed hcompareObserved]
    rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]

/-- Staging `uBit && !vBit` preserves every little-endian `s` coefficient
value bit. -/
theorem uOddVBitNotToCompareStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n) (targetBit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.sCoeffValueBit n counterWidth targetBit).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.sCoeffValueBit n counterWidth targetBit).get x := by
  let sourceU := RegisterBits.uBit n counterWidth uIndex
  let sourceV := RegisterBits.vBit n counterWidth vIndex
  let compare := RegisterBits.compareBit n counterWidth
  let observed := RegisterBits.sCoeffValueBit n counterWidth targetBit
  have hsourceVObserved : sourceV.wire ≠ observed.wire := by
    simpa [sourceV, observed, RegisterBits.sCoeffValueBit] using
      RegisterBits.v_sCoeff_wire_ne n counterWidth vIndex
        (WireAddress.littleEndianWire targetBit)
  have hcompareObserved : compare.wire ≠ observed.wire := by
    simpa [compare, observed, RegisterBits.sCoeffValueBit] using
      RegisterBits.compare_sCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit)
  change observed.get
      (sourceV.flip
        (EncodedBit.toffoliStep sourceU sourceV compare
          (sourceV.flip x))) =
    observed.get x
  rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
    observed hcompareObserved]
  rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]

/-- Staging `uBit && !vBit` preserves every little-endian `r` coefficient
value bit. -/
theorem uOddVBitNotToCompareStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n) (targetBit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.rCoeffValueBit n counterWidth targetBit).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.rCoeffValueBit n counterWidth targetBit).get x := by
  let sourceU := RegisterBits.uBit n counterWidth uIndex
  let sourceV := RegisterBits.vBit n counterWidth vIndex
  let compare := RegisterBits.compareBit n counterWidth
  let observed := RegisterBits.rCoeffValueBit n counterWidth targetBit
  have hsourceVObserved : sourceV.wire ≠ observed.wire := by
    simpa [sourceV, observed, RegisterBits.rCoeffValueBit] using
      RegisterBits.v_rCoeff_wire_ne n counterWidth vIndex
        (WireAddress.littleEndianWire targetBit)
  have hcompareObserved : compare.wire ≠ observed.wire := by
    simpa [compare, observed, RegisterBits.rCoeffValueBit] using
      RegisterBits.compare_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire targetBit)
  change observed.get
      (sourceV.flip
        (EncodedBit.toffoliStep sourceU sourceV compare
          (sourceV.flip x))) =
    observed.get x
  rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
    observed hcompareObserved]
  rw [EncodedBit.get_flip_of_wire_ne sourceV observed hsourceVObserved]

/-- Staging `uBit && !vBit` preserves the active flag. -/
theorem uOddVBitNotToCompareStep_get_active
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  let sourceU := RegisterBits.uBit n counterWidth uIndex
  let sourceV := RegisterBits.vBit n counterWidth vIndex
  let compare := RegisterBits.compareBit n counterWidth
  let active := RegisterBits.activeBit n counterWidth
  change active.get
      (sourceV.flip
        (EncodedBit.toffoliStep sourceU sourceV compare
          (sourceV.flip x))) =
    active.get x
  rw [EncodedBit.get_flip_of_wire_ne sourceV active
    (Ne.symm (RegisterBits.active_v_wire_ne n counterWidth vIndex))]
  rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
    active (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth))]
  rw [EncodedBit.get_flip_of_wire_ne sourceV active
    (Ne.symm (RegisterBits.active_v_wire_ne n counterWidth vIndex))]

/-- Staging `uBit && !vBit` preserves the first scratch bit. -/
theorem uOddVBitNotToCompareStep_get_scratchA
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.scratchABit n counterWidth).get x := by
  let sourceU := RegisterBits.uBit n counterWidth uIndex
  let sourceV := RegisterBits.vBit n counterWidth vIndex
  let compare := RegisterBits.compareBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  change scratchA.get
      (sourceV.flip
        (EncodedBit.toffoliStep sourceU sourceV compare
          (sourceV.flip x))) =
    scratchA.get x
  rw [EncodedBit.get_flip_of_wire_ne sourceV scratchA
    (RegisterBits.v_scratchA_wire_ne n counterWidth vIndex)]
  rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
    scratchA (RegisterBits.compare_scratchA_wire_ne n counterWidth)]
  rw [EncodedBit.get_flip_of_wire_ne sourceV scratchA
    (RegisterBits.v_scratchA_wire_ne n counterWidth vIndex)]

/-- Staging `uBit && !vBit` preserves the second scratch bit. -/
theorem uOddVBitNotToCompareStep_get_scratchB
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.scratchBBit n counterWidth).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.scratchBBit n counterWidth).get x := by
  let sourceU := RegisterBits.uBit n counterWidth uIndex
  let sourceV := RegisterBits.vBit n counterWidth vIndex
  let compare := RegisterBits.compareBit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  change scratchB.get
      (sourceV.flip
        (EncodedBit.toffoliStep sourceU sourceV compare
          (sourceV.flip x))) =
    scratchB.get x
  rw [EncodedBit.get_flip_of_wire_ne sourceV scratchB
    (RegisterBits.v_scratchB_wire_ne n counterWidth vIndex)]
  rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
    scratchB (RegisterBits.compare_scratchB_wire_ne n counterWidth)]
  rw [EncodedBit.get_flip_of_wire_ne sourceV scratchB
    (RegisterBits.v_scratchB_wire_ne n counterWidth vIndex)]

/-- Staging `uBit && !vBit` preserves every stored branch-history bit. -/
theorem uOddVBitNotToCompareStep_get_historyBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  let sourceU := RegisterBits.uBit n counterWidth uIndex
  let sourceV := RegisterBits.vBit n counterWidth vIndex
  let compare := RegisterBits.compareBit n counterWidth
  let history := RegisterBits.historyBit n counterWidth historyIndex
  change history.get
      (sourceV.flip
        (EncodedBit.toffoliStep sourceU sourceV compare
          (sourceV.flip x))) =
    history.get x
  rw [EncodedBit.get_flip_of_wire_ne sourceV history
    (RegisterBits.v_history_wire_ne n counterWidth vIndex historyIndex)]
  rw [EncodedBit.toffoliStep_get_of_target_ne sourceU sourceV compare
    history (RegisterBits.compare_history_wire_ne n counterWidth historyIndex)]
  rw [EncodedBit.get_flip_of_wire_ne sourceV history
    (RegisterBits.v_history_wire_ne n counterWidth vIndex historyIndex)]

/-- The `u`-odd/`v`-even condition staging gate list is palindromic. -/
@[simp] theorem uOddVBitNotToCompareGates_reverse
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    (uOddVBitNotToCompareGates n counterWidth uIndex vIndex).reverse =
      uOddVBitNotToCompareGates n counterWidth uIndex vIndex := by
  rfl

/-- Gate list that stages the second RNSL17 branch code from the `u`-odd and
`v`-even condition, then restores the comparison ancilla.  On clean compare it
xors the `vEven` branch code `01` into the scratch encoder bits under the
active guard.  The comparison-branch selector/history slices are implemented
separately; the full round data-path update remains a later obligation
[RNSL17, ECDLP.tex:399-421,468-475]. -/
def vEvenBranchCodeToScratchGates
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  uOddVBitNotToCompareGates n counterWidth uIndex vIndex ++
  activeConditionBranchCodeToScratchGates n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.vEven ++
  (uOddVBitNotToCompareGates n counterWidth uIndex vIndex).reverse

/-- Base-gate program for active-guarded `vEven` branch-code staging with
compare restored. -/
def vEvenBranchCodeToScratchProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (vEvenBranchCodeToScratchGates n counterWidth uIndex vIndex)

/-- Semantic step for active-guarded `vEven` branch-code staging with compare
restored. -/
def vEvenBranchCodeToScratchStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (vEvenBranchCodeToScratchGates n counterWidth uIndex vIndex)

/-- The `vEven` branch-code staging program is a concrete encoded-bit base-gate
realization over the Montgomery--Kaliski register layout. -/
theorem vEvenBranchCodeToScratch_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (vEvenBranchCodeToScratchProgram n counterWidth uIndex vIndex)
      (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (vEvenBranchCodeToScratchGates n counterWidth uIndex vIndex)

theorem vEvenBranchCodeToScratchStep_eq
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x =
      uOddVBitNotToCompareStep n counterWidth uIndex vIndex
        (activeConditionBranchCodeToScratchStep n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (RegisterBits.active_compare_wire_ne n counterWidth)
          (RegisterBits.compare_scratchA_wire_ne n counterWidth)
          (RegisterBits.compare_scratchB_wire_ne n counterWidth)
          Branch.vEven
          (uOddVBitNotToCompareStep n counterWidth uIndex vIndex x)) := by
  simp [vEvenBranchCodeToScratchStep, vEvenBranchCodeToScratchGates,
    uOddVBitNotToCompareStep, activeConditionBranchCodeToScratchStep,
    EncodedBit.GateSpec.stepList_append]

/-- On clean compare, `vEven` branch-code staging restores the comparison
ancilla after using it as the condition bit. -/
theorem vEvenBranchCodeToScratchStep_get_compare_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth)
    (hclean : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.compareBit n counterWidth).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      false := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_compare]
  rw [activeConditionBranchCodeToScratchStep_get_condition]
  rw [activeConditionBranchCodeToScratchStep_get_uBit]
  rw [activeConditionBranchCodeToScratchStep_get_vBit]
  rw [uOddVBitNotToCompareStep_get_compare_clean
    n counterWidth uIndex vIndex x hclean]
  rw [uOddVBitNotToCompareStep_get_uBit]
  rw [uOddVBitNotToCompareStep_get_vBit]
  cases (RegisterBits.uBit n counterWidth uIndex).get x <;>
    cases (RegisterBits.vBit n counterWidth vIndex).get x <;> simp

/-- On clean compare, `vEven` branch-code staging preserves scratchA because
the `vEven` code is `01` [RNSL17, ECDLP.tex:471]. -/
theorem vEvenBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth)
    (hclean : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.scratchABit n counterWidth).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (RegisterBits.scratchABit n counterWidth).get x := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_scratchA]
  rw [activeConditionBranchCodeToScratchStep_get_scratchA]
  rw [uOddVBitNotToCompareStep_get_scratchA]
  rw [uOddVBitNotToCompareStep_get_active]
  rw [uOddVBitNotToCompareStep_get_compare_clean
    n counterWidth uIndex vIndex x hclean]
  simp [Branch.auxBit]

/-- On clean compare, `vEven` branch-code staging toggles scratchB exactly when
the active flag is set, the selected `u` bit is one, and the selected `v` bit is
zero. -/
theorem vEvenBranchCodeToScratchStep_get_scratchB_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth)
    (hclean : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.scratchBBit n counterWidth).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      ((RegisterBits.scratchBBit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          (RegisterBits.uBit n counterWidth uIndex).get x &&
          !(RegisterBits.vBit n counterWidth vIndex).get x)) := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_scratchB]
  rw [activeConditionBranchCodeToScratchStep_get_scratchB]
  rw [uOddVBitNotToCompareStep_get_scratchB]
  rw [uOddVBitNotToCompareStep_get_active]
  rw [uOddVBitNotToCompareStep_get_compare_clean
    n counterWidth uIndex vIndex x hclean]
  cases (RegisterBits.activeBit n counterWidth).get x <;>
    cases (RegisterBits.uBit n counterWidth uIndex).get x <;>
      cases (RegisterBits.vBit n counterWidth vIndex).get x <;>
        simp [Branch.historyBit]

/-- Active-guarded `vEven` branch-code staging preserves the selected `u` bit.
-/
theorem vEvenBranchCodeToScratchStep_get_uBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uBit n counterWidth uIndex).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (RegisterBits.uBit n counterWidth uIndex).get x := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_uBit]
  rw [activeConditionBranchCodeToScratchStep_get_uBit]
  rw [uOddVBitNotToCompareStep_get_uBit]

/-- Active-guarded `vEven` branch-code staging preserves every little-endian
`u` value bit. -/
theorem vEvenBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (uIndex vIndex targetBit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uValueBit n counterWidth targetBit).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (RegisterBits.uValueBit n counterWidth targetBit).get x := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_uWordBit]
  rw [activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.vEven
    (RegisterBits.uValueBit n counterWidth targetBit)
    (by
      simpa [RegisterBits.uValueBit] using
        Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit)))
    (by
      simpa [RegisterBits.uValueBit] using
        Ne.symm (RegisterBits.u_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit)))]
  rw [uOddVBitNotToCompareStep_get_uWordBit]

/-- Active-guarded `vEven` branch-code staging preserves the selected `v` bit.
-/
theorem vEvenBranchCodeToScratchStep_get_vBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vBit n counterWidth vIndex).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (RegisterBits.vBit n counterWidth vIndex).get x := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_vBit]
  rw [activeConditionBranchCodeToScratchStep_get_vBit]
  rw [uOddVBitNotToCompareStep_get_vBit]

/-- Active-guarded `vEven` branch-code staging preserves every little-endian
`v` value bit. -/
theorem vEvenBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (uIndex vIndex targetBit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vValueBit n counterWidth targetBit).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (RegisterBits.vValueBit n counterWidth targetBit).get x := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_vWordBit]
  rw [activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.vEven
    (RegisterBits.vValueBit n counterWidth targetBit)
    (by
      simpa [RegisterBits.vValueBit] using
        Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit)))
    (by
      simpa [RegisterBits.vValueBit] using
        Ne.symm (RegisterBits.v_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit)))]
  rw [uOddVBitNotToCompareStep_get_vWordBit]

/-- Active-guarded `vEven` branch-code staging preserves every little-endian
`s` coefficient value bit. -/
theorem vEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n) (targetBit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.sCoeffValueBit n counterWidth targetBit).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (RegisterBits.sCoeffValueBit n counterWidth targetBit).get x := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_sCoeffValueWordBit]
  rw [activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.vEven
    (RegisterBits.sCoeffValueBit n counterWidth targetBit)
    (by
      simpa [RegisterBits.sCoeffValueBit] using
        Ne.symm (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit)))
    (by
      simpa [RegisterBits.sCoeffValueBit] using
        Ne.symm (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit)))]
  rw [uOddVBitNotToCompareStep_get_sCoeffValueWordBit]

/-- Active-guarded `vEven` branch-code staging preserves every little-endian
`r` coefficient value bit. -/
theorem vEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n) (targetBit : Fin (n + 1))
    (x : Registers n counterWidth) :
    (RegisterBits.rCoeffValueBit n counterWidth targetBit).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (RegisterBits.rCoeffValueBit n counterWidth targetBit).get x := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_rCoeffValueWordBit]
  rw [activeConditionBranchCodeToScratchStep_get_of_scratch_ne n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.vEven
    (RegisterBits.rCoeffValueBit n counterWidth targetBit)
    (by
      simpa [RegisterBits.rCoeffValueBit] using
        Ne.symm (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit)))
    (by
      simpa [RegisterBits.rCoeffValueBit] using
        Ne.symm (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire targetBit)))]
  rw [uOddVBitNotToCompareStep_get_rCoeffValueWordBit]

/-- Active-guarded `vEven` branch-code staging preserves the active flag. -/
theorem vEvenBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_active]
  rw [activeConditionBranchCodeToScratchStep_get_active]
  rw [uOddVBitNotToCompareStep_get_active]

/-- Active-guarded `vEven` branch-code staging preserves every stored
branch-history bit. -/
theorem vEvenBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  rw [vEvenBranchCodeToScratchStep_eq]
  rw [uOddVBitNotToCompareStep_get_historyBit]
  rw [activeConditionBranchCodeToScratchStep_get_historyBit]
  rw [uOddVBitNotToCompareStep_get_historyBit]

/-- The complete `vEven` branch-code staging list is palindromic. -/
@[simp] theorem vEvenBranchCodeToScratchGates_reverse
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    (vEvenBranchCodeToScratchGates n counterWidth uIndex vIndex).reverse =
      vEvenBranchCodeToScratchGates n counterWidth uIndex vIndex := by
  simp [vEvenBranchCodeToScratchGates,
    activeConditionBranchCodeToScratchGates, Branch.auxBit,
    Branch.historyBit]

/-- Gate list that writes the `vEven` branch-history bit after staging its
branch code, then uncomputes the scratch-code staging.  This connects the
RNSL17 code bit `m_i` write to the same concrete branch-code gates; it is still
only the `vEven` history slice, not the full round update circuit [RNSL17,
ECDLP.tex:468-475]. -/
def vEvenBranchHistoryWriteGates
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  vEvenBranchCodeToScratchGates n counterWidth uIndex vIndex ++
  [activeScratchBToHistoryGate n counterWidth historyIndex] ++
  (vEvenBranchCodeToScratchGates n counterWidth uIndex vIndex).reverse

/-- Base-gate program for writing the staged `vEven` branch-history bit. -/
def vEvenBranchHistoryWriteProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (vEvenBranchHistoryWriteGates n counterWidth uIndex vIndex historyIndex)

/-- Semantic step for writing the staged `vEven` branch-history bit. -/
def vEvenBranchHistoryWriteStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (vEvenBranchHistoryWriteGates n counterWidth uIndex vIndex historyIndex)

/-- The `vEven` branch-history write program is a concrete encoded-bit
base-gate realization over the Montgomery--Kaliski register layout. -/
theorem vEvenBranchHistoryWrite_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (vEvenBranchHistoryWriteProgram n counterWidth uIndex vIndex
        historyIndex)
      (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
        historyIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (vEvenBranchHistoryWriteGates n counterWidth uIndex vIndex historyIndex)

theorem vEvenBranchHistoryWriteStep_eq
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex historyIndex x =
      vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
        (activeScratchBToHistoryStep n counterWidth historyIndex
          (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x)) := by
  simp [vEvenBranchHistoryWriteStep, vEvenBranchHistoryWriteGates,
    vEvenBranchCodeToScratchStep, activeScratchBToHistoryStep,
    EncodedBit.GateSpec.stepList_append, EncodedBit.GateSpec.stepList]

/-- On clean compare and clean scratchB, the `vEven` history-write slice toggles
the selected `m_i` bit exactly under the staged `vEven` branch condition. -/
theorem vEvenBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          (RegisterBits.uBit n counterWidth uIndex).get x &&
          !(RegisterBits.vBit n counterWidth vIndex).get x)) := by
  rw [vEvenBranchHistoryWriteStep_eq]
  rw [vEvenBranchCodeToScratchStep_get_historyBit]
  rw [activeScratchBToHistoryStep_get_historyBit]
  rw [vEvenBranchCodeToScratchStep_get_historyBit]
  rw [vEvenBranchCodeToScratchStep_get_active]
  rw [vEvenBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth uIndex vIndex x hcompare]
  cases (RegisterBits.activeBit n counterWidth).get x <;>
    cases (RegisterBits.uBit n counterWidth uIndex).get x <;>
      cases (RegisterBits.vBit n counterWidth vIndex).get x <;>
        simp [hscratchB]

/-- The `v`-even branch-history write slice preserves every history slot
except the selected target slot. -/
theorem vEvenBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth observed).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex target x) =
      (RegisterBits.historyBit n counterWidth observed).get x := by
  rw [vEvenBranchHistoryWriteStep_eq]
  rw [vEvenBranchCodeToScratchStep_get_historyBit]
  rw [activeScratchBToHistoryStep_get_historyBit_of_ne
    n counterWidth target observed hne]
  rw [vEvenBranchCodeToScratchStep_get_historyBit]

/-- Lifted semantic step for the `vEven` branch-history write over the attached
comparison-work register. -/
def liftedVEvenBranchHistoryWriteStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x =>
    (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex historyIndex x.1,
      x.2)

/-- Actual circuit for the lifted `vEven` branch-history write. -/
def liftedVEvenBranchHistoryWriteProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (vEvenBranchHistoryWriteProgram n counterWidth uIndex vIndex historyIndex)

/-- The lifted history-write circuit realizes the product action. -/
theorem liftedVEvenBranchHistoryWrite_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithComparisonWorkEncoding n counterWidth)
      (liftedVEvenBranchHistoryWriteProgram n counterWidth uIndex vIndex
        historyIndex)
      (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
        historyIndex) := by
  exact UnitaryCircuit.Realizes.onBinaryPrefix
    (right := comparisonWorkEncoding n)
    (vEvenBranchHistoryWrite_realizes n counterWidth uIndex vIndex
      historyIndex)

/-- On clean lifted compare and scratchB bits, the lifted `vEven` history-write
slice toggles the selected branch-history bit under the staged `vEven`
condition. -/
theorem liftedVEvenBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false)
    (hscratchB : (liftedScratchBBit n counterWidth).get x = false) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      ((liftedHistoryBit n counterWidth historyIndex).get x ^^
        ((liftedActiveBit n counterWidth).get x &&
          (RegisterBits.uBit n counterWidth uIndex).get x.1 &&
          !(RegisterBits.vBit n counterWidth vIndex).get x.1)) := by
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x.1 ^^
        ((RegisterBits.activeBit n counterWidth).get x.1 &&
          (RegisterBits.uBit n counterWidth uIndex).get x.1 &&
          !(RegisterBits.vBit n counterWidth vIndex).get x.1))
  apply vEvenBranchHistoryWriteStep_get_history_clean
  · change (RegisterBits.compareBit n counterWidth).get x.1 = false at hcompare
    exact hcompare
  · change (RegisterBits.scratchBBit n counterWidth).get x.1 = false at hscratchB
    exact hscratchB

/-- The lifted `vEven` history-write slice preserves every history slot except
the selected target slot. -/
theorem liftedVEvenBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth observed).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          target x) =
      (liftedHistoryBit n counterWidth observed).get x := by
  change (RegisterBits.historyBit n counterWidth observed).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex target
          x.1) =
      (RegisterBits.historyBit n counterWidth observed).get x.1
  exact vEvenBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth uIndex vIndex target observed hne x.1

/-- The lifted `vEven` branch-history write preserves every comparison-work
carry bit, because it only acts on the leading Kaliski registers. -/
theorem liftedVEvenBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  rfl

/-- On clean compare, the `vEven` branch-history write slice restores the
comparison ancilla after staging, writing, and uncomputing the branch code. -/
theorem vEvenBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.compareBit n counterWidth).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      false := by
  rw [vEvenBranchHistoryWriteStep_eq]
  let y :=
    activeScratchBToHistoryStep n counterWidth historyIndex
      (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x)
  have hcompareAfterWrite :
      (RegisterBits.compareBit n counterWidth).get y = false := by
    dsimp [y]
    rw [activeScratchBToHistoryStep_get_compare]
    exact vEvenBranchCodeToScratchStep_get_compare_clean n counterWidth
      uIndex vIndex x hcompare
  change (RegisterBits.compareBit n counterWidth).get
      (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex y) = false
  exact vEvenBranchCodeToScratchStep_get_compare_clean n counterWidth uIndex
    vIndex y hcompareAfterWrite

/-- On clean compare, the `vEven` branch-history write slice restores the first
scratch-code bit. -/
theorem vEvenBranchHistoryWriteStep_get_scratchA_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.scratchABit n counterWidth).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (RegisterBits.scratchABit n counterWidth).get x := by
  rw [vEvenBranchHistoryWriteStep_eq]
  let y :=
    activeScratchBToHistoryStep n counterWidth historyIndex
      (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x)
  have hcompareAfterWrite :
      (RegisterBits.compareBit n counterWidth).get y = false := by
    dsimp [y]
    rw [activeScratchBToHistoryStep_get_compare]
    exact vEvenBranchCodeToScratchStep_get_compare_clean n counterWidth
      uIndex vIndex x hcompare
  change (RegisterBits.scratchABit n counterWidth).get
      (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex y) =
    (RegisterBits.scratchABit n counterWidth).get x
  rw [vEvenBranchCodeToScratchStep_get_scratchA_clean n counterWidth uIndex
    vIndex y hcompareAfterWrite]
  dsimp [y]
  rw [activeScratchBToHistoryStep_get_scratchA]
  rw [vEvenBranchCodeToScratchStep_get_scratchA_clean n counterWidth uIndex
    vIndex x hcompare]

/-- On clean compare, the `vEven` branch-history write slice restores the
second scratch-code bit. -/
theorem vEvenBranchHistoryWriteStep_get_scratchB_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hcompare : (RegisterBits.compareBit n counterWidth).get x = false) :
    (RegisterBits.scratchBBit n counterWidth).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (RegisterBits.scratchBBit n counterWidth).get x := by
  rw [vEvenBranchHistoryWriteStep_eq]
  let y :=
    activeScratchBToHistoryStep n counterWidth historyIndex
      (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x)
  have hcompareAfterWrite :
      (RegisterBits.compareBit n counterWidth).get y = false := by
    dsimp [y]
    rw [activeScratchBToHistoryStep_get_compare]
    exact vEvenBranchCodeToScratchStep_get_compare_clean n counterWidth
      uIndex vIndex x hcompare
  change (RegisterBits.scratchBBit n counterWidth).get
      (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex y) =
    (RegisterBits.scratchBBit n counterWidth).get x
  rw [vEvenBranchCodeToScratchStep_get_scratchB_clean n counterWidth uIndex
    vIndex y hcompareAfterWrite]
  dsimp [y]
  rw [activeScratchBToHistoryStep_get_scratchB]
  rw [vEvenBranchCodeToScratchStep_get_scratchB_clean n counterWidth uIndex
    vIndex x hcompare]
  rw [activeScratchBToHistoryStep_get_active]
  rw [vEvenBranchCodeToScratchStep_get_active]
  rw [activeScratchBToHistoryStep_get_uBit]
  rw [vEvenBranchCodeToScratchStep_get_uBit]
  rw [activeScratchBToHistoryStep_get_vBit]
  rw [vEvenBranchCodeToScratchStep_get_vBit]
  cases (RegisterBits.scratchBBit n counterWidth).get x <;>
    cases (RegisterBits.activeBit n counterWidth).get x <;>
      cases (RegisterBits.uBit n counterWidth uIndex).get x <;>
        cases (RegisterBits.vBit n counterWidth vIndex).get x <;> simp

/-- The `vEven` branch-history write slice preserves the active flag. -/
theorem vEvenBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  rw [vEvenBranchHistoryWriteStep_eq]
  rw [vEvenBranchCodeToScratchStep_get_active]
  rw [activeScratchBToHistoryStep_get_active]
  rw [vEvenBranchCodeToScratchStep_get_active]

/-- The `vEven` branch-history write slice preserves the selected `u` bit. -/
theorem vEvenBranchHistoryWriteStep_get_uBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.uBit n counterWidth uIndex).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (RegisterBits.uBit n counterWidth uIndex).get x := by
  rw [vEvenBranchHistoryWriteStep_eq]
  rw [vEvenBranchCodeToScratchStep_get_uBit]
  rw [activeScratchBToHistoryStep_get_uBit]
  rw [vEvenBranchCodeToScratchStep_get_uBit]

/-- The `vEven` branch-history write slice preserves the selected `v` bit. -/
theorem vEvenBranchHistoryWriteStep_get_vBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.vBit n counterWidth vIndex).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (RegisterBits.vBit n counterWidth vIndex).get x := by
  rw [vEvenBranchHistoryWriteStep_eq]
  rw [vEvenBranchCodeToScratchStep_get_vBit]
  rw [activeScratchBToHistoryStep_get_vBit]
  rw [vEvenBranchCodeToScratchStep_get_vBit]

/-- Lifted clean-compare endpoint for the `vEven` branch-history write slice. -/
theorem liftedVEvenBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedCompareBit n counterWidth).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      false := by
  change (RegisterBits.compareBit n counterWidth).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      false
  apply vEvenBranchHistoryWriteStep_get_compare_clean
  change (RegisterBits.compareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- Lifted scratchA restoration endpoint for the `vEven` branch-history write
slice. -/
theorem liftedVEvenBranchHistoryWriteStep_get_scratchA_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedScratchABit n counterWidth).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (liftedScratchABit n counterWidth).get x := by
  change (RegisterBits.scratchABit n counterWidth).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      (RegisterBits.scratchABit n counterWidth).get x.1
  apply vEvenBranchHistoryWriteStep_get_scratchA_clean
  change (RegisterBits.compareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- Lifted scratchB restoration endpoint for the `vEven` branch-history write
slice. -/
theorem liftedVEvenBranchHistoryWriteStep_get_scratchB_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedScratchBBit n counterWidth).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (liftedScratchBBit n counterWidth).get x := by
  change (RegisterBits.scratchBBit n counterWidth).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      (RegisterBits.scratchBBit n counterWidth).get x.1
  apply vEvenBranchHistoryWriteStep_get_scratchB_clean
  change (RegisterBits.compareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- Lifted active-flag preservation endpoint for the `vEven`
branch-history write slice. -/
theorem liftedVEvenBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (liftedActiveBit n counterWidth).get x := by
  change (RegisterBits.activeBit n counterWidth).get
        (vEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      (RegisterBits.activeBit n counterWidth).get x.1
  exact vEvenBranchHistoryWriteStep_get_active n counterWidth uIndex vIndex
    historyIndex x.1

/-- Lifted selected-`u` preservation endpoint for the `vEven`
branch-history write slice. -/
theorem liftedVEvenBranchHistoryWriteStep_get_uBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedUBit n counterWidth uIndex).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (liftedUBit n counterWidth uIndex).get x := by
  simpa [liftedUBit, liftedVEvenBranchHistoryWriteStep,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit] using
    vEvenBranchHistoryWriteStep_get_uBit n counterWidth uIndex vIndex
      historyIndex x.1

/-- Lifted selected-`v` preservation endpoint for the `vEven`
branch-history write slice. -/
theorem liftedVEvenBranchHistoryWriteStep_get_vBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedVBit n counterWidth vIndex).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (liftedVBit n counterWidth vIndex).get x := by
  simpa [liftedVBit, liftedVEvenBranchHistoryWriteStep,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit] using
    vEvenBranchHistoryWriteStep_get_vBit n counterWidth uIndex vIndex
      historyIndex x.1

end
end MK
end MAU.Inversion
end QuantumAlg

end
