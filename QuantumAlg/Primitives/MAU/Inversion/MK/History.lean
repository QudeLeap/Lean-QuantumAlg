/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Primitives.MAU.Inversion.MK.Selector

/-!
# Route history

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

/-! ## Supplied-condition branch-history write -/

/-- Gate list that writes a branch-history bit after staging a supplied
condition's RNSL17 branch code into the two scratch-code bits, then uncomputes
the staging.  This is the shared bridge used after a concrete selector circuit
has produced the condition bit; in particular, the word-comparison selector for
the odd branches remains a separate circuit obligation [RNSL17,
ECDLP.tex:399-421,468-475]. -/
def activeConditionBranchHistoryWriteGates
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  activeConditionBranchCodeToScratchGates n counterWidth condition
    hactiveCondition hconditionScratchA hconditionScratchB branch ++
  [activeScratchBToHistoryGate n counterWidth historyIndex] ++
  (activeConditionBranchCodeToScratchGates n counterWidth condition
    hactiveCondition hconditionScratchA hconditionScratchB branch).reverse

/-- Base-gate program for writing a supplied-condition branch-history bit. -/
def activeConditionBranchHistoryWriteProgram
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeConditionBranchHistoryWriteGates n counterWidth condition
      hactiveCondition hconditionScratchA hconditionScratchB branch
      historyIndex)

/-- Semantic step for writing a supplied-condition branch-history bit. -/
def activeConditionBranchHistoryWriteStep
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n)) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (activeConditionBranchHistoryWriteGates n counterWidth condition
      hactiveCondition hconditionScratchA hconditionScratchB branch
      historyIndex)

/-- The supplied-condition branch-history write program is a concrete
encoded-bit base-gate realization over the Montgomery--Kaliski register
layout. -/
theorem activeConditionBranchHistoryWrite_realizes
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (activeConditionBranchHistoryWriteProgram n counterWidth condition
        hactiveCondition hconditionScratchA hconditionScratchB branch
        historyIndex)
      (activeConditionBranchHistoryWriteStep n counterWidth condition
        hactiveCondition hconditionScratchA hconditionScratchB branch
        historyIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (activeConditionBranchHistoryWriteGates n counterWidth condition
      hactiveCondition hconditionScratchA hconditionScratchB branch
      historyIndex)

theorem activeConditionBranchHistoryWriteStep_eq
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    activeConditionBranchHistoryWriteStep n counterWidth condition
        hactiveCondition hconditionScratchA hconditionScratchB branch
        historyIndex x =
      EncodedBit.GateSpec.stepList
        (activeConditionBranchCodeToScratchGates n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB
          branch).reverse
        (activeScratchBToHistoryStep n counterWidth historyIndex
          (activeConditionBranchCodeToScratchStep n counterWidth condition
            hactiveCondition hconditionScratchA hconditionScratchB
            branch x)) := by
  simp [activeConditionBranchHistoryWriteStep,
    activeConditionBranchHistoryWriteGates,
    activeConditionBranchCodeToScratchStep, activeScratchBToHistoryStep,
    EncodedBit.GateSpec.stepList_append, EncodedBit.GateSpec.stepList]

/-- On clean scratchB, the supplied-condition branch-history slice toggles the
selected `m_i` bit exactly when the active flag, the supplied condition, and
the branch history-code bit are all set. -/
theorem activeConditionBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (activeConditionBranchHistoryWriteStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch
          historyIndex x) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          condition.get x && branch.historyBit)) := by
  rw [activeConditionBranchHistoryWriteStep_eq]
  rw [activeConditionBranchCodeToScratchReverseStep_get_historyBit]
  rw [activeScratchBToHistoryStep_get_historyBit]
  rw [activeConditionBranchCodeToScratchStep_get_historyBit]
  rw [activeConditionBranchCodeToScratchStep_get_active]
  rw [activeConditionBranchCodeToScratchStep_get_scratchB]
  cases (RegisterBits.activeBit n counterWidth).get x <;>
    cases condition.get x <;>
      cases branch <;>
        simp [Branch.historyBit, hscratchB]

/-- The supplied-condition branch-history slice preserves the active flag. -/
theorem activeConditionBranchHistoryWriteStep_get_active
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (activeConditionBranchHistoryWriteStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch
          historyIndex x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  rw [activeConditionBranchHistoryWriteStep_eq]
  rw [activeConditionBranchCodeToScratchReverseStep_get_active]
  rw [activeScratchBToHistoryStep_get_active]
  exact activeConditionBranchCodeToScratchStep_get_active n counterWidth
    condition hactiveCondition hconditionScratchA hconditionScratchB branch x

/-- The supplied-condition branch-history slice preserves scratchA when the
supplied condition bit is disjoint from the selected history target. -/
theorem activeConditionBranchHistoryWriteStep_get_scratchA
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n))
    (hconditionHistory :
      condition.wire ≠
        (RegisterBits.historyBit n counterWidth historyIndex).wire)
    (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (activeConditionBranchHistoryWriteStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch
          historyIndex x) =
      (RegisterBits.scratchABit n counterWidth).get x := by
  rw [activeConditionBranchHistoryWriteStep_eq]
  rw [activeConditionBranchCodeToScratchReverseStep_get_scratchA]
  let staged :=
    activeConditionBranchCodeToScratchStep n counterWidth condition
      hactiveCondition hconditionScratchA hconditionScratchB branch x
  rw [activeScratchBToHistoryStep_get_active]
  rw [activeScratchBToHistoryStep_get_condition n counterWidth historyIndex
    condition hconditionHistory staged]
  rw [activeConditionBranchCodeToScratchStep_get_active]
  rw [activeConditionBranchCodeToScratchStep_get_condition]
  rw [activeScratchBToHistoryStep_get_scratchA]
  rw [activeConditionBranchCodeToScratchStep_get_scratchA]
  cases (RegisterBits.activeBit n counterWidth).get x <;>
    cases condition.get x <;>
      cases (RegisterBits.scratchABit n counterWidth).get x <;>
        cases branch <;>
          simp [Branch.auxBit]

/-- The supplied-condition branch-history slice preserves the supplied
condition bit.  The extra wire-disjointness premise records that the supplied
condition is not the selected history target. -/
theorem activeConditionBranchHistoryWriteStep_get_condition
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n))
    (hconditionHistory :
      condition.wire ≠
        (RegisterBits.historyBit n counterWidth historyIndex).wire)
    (x : Registers n counterWidth) :
    condition.get
        (activeConditionBranchHistoryWriteStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch
          historyIndex x) =
      condition.get x := by
  rw [activeConditionBranchHistoryWriteStep_eq]
  rw [activeConditionBranchCodeToScratchReverseStep_get_condition]
  let staged :=
    activeConditionBranchCodeToScratchStep n counterWidth condition
      hactiveCondition hconditionScratchA hconditionScratchB branch x
  have hmiddle :
      condition.get
          (activeScratchBToHistoryStep n counterWidth historyIndex staged) =
        condition.get staged := by
    let active := RegisterBits.activeBit n counterWidth
    let scratchB := RegisterBits.scratchBBit n counterWidth
    let history := RegisterBits.historyBit n counterWidth historyIndex
    simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
      EncodedBit.GateSpec.step, active, scratchB, history] using
      EncodedBit.toffoliStep_get_of_target_ne active scratchB history
        condition (Ne.symm hconditionHistory) staged
  rw [hmiddle]
  exact activeConditionBranchCodeToScratchStep_get_condition n counterWidth
    condition hactiveCondition hconditionScratchA hconditionScratchB branch x

/-- The supplied-condition branch-history slice preserves any observed bit
disjoint from the scratch-code targets and the selected history target. -/
theorem activeConditionBranchHistoryWriteStep_get_of_preserved
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (historyIndex : Fin (2 * n))
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hscratchA :
      (RegisterBits.scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB :
      (RegisterBits.scratchBBit n counterWidth).wire ≠ observed.wire)
    (hhistory :
      (RegisterBits.historyBit n counterWidth historyIndex).wire ≠
        observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (activeConditionBranchHistoryWriteStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch
          historyIndex x) =
      observed.get x := by
  rw [activeConditionBranchHistoryWriteStep_eq]
  rw [activeConditionBranchCodeToScratchReverseStep_get_of_scratch_ne
    n counterWidth condition hactiveCondition hconditionScratchA
    hconditionScratchB branch observed hscratchA hscratchB]
  rw [activeScratchBToHistoryStep_get_of_history_ne
    n counterWidth historyIndex observed hhistory]
  exact activeConditionBranchCodeToScratchStep_get_of_scratch_ne
    n counterWidth condition hactiveCondition hconditionScratchA
    hconditionScratchB branch observed hscratchA hscratchB x

/-- The supplied-condition branch-history slice preserves every history slot
except the selected target slot. -/
theorem activeConditionBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (target observed : Fin (2 * n))
    (hne : target ≠ observed)
    (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth observed).get
        (activeConditionBranchHistoryWriteStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch
          target x) =
      (RegisterBits.historyBit n counterWidth observed).get x :=
  activeConditionBranchHistoryWriteStep_get_of_preserved n counterWidth
    condition hactiveCondition hconditionScratchA hconditionScratchB branch
    target (RegisterBits.historyBit n counterWidth observed)
    (RegisterBits.scratchA_history_wire_ne n counterWidth observed)
    (RegisterBits.scratchB_history_wire_ne n counterWidth observed)
    (RegisterBits.history_history_wire_ne n counterWidth hne) x

/-! ## Comparison-conditioned odd-branch history write -/

/-- Gate list that writes the RNSL17 `uGreater` history bit from a supplied
comparison ancilla.  The comparison bit is treated as an already-computed
selector for `v < u`; the composed selector/history witness below supplies
the concrete comparator path over the attached comparison-work register
[RNSL17, ECDLP.tex:399-421,468-475]. -/
def uGreaterBranchHistoryWriteGates
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  activeConditionBranchHistoryWriteGates n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.uGreater historyIndex

/-- Base-gate program for writing the `uGreater` history bit from the
comparison ancilla. -/
def uGreaterBranchHistoryWriteProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uGreaterBranchHistoryWriteGates n counterWidth historyIndex)

/-- Semantic step for writing the `uGreater` history bit from the comparison
ancilla. -/
def uGreaterBranchHistoryWriteStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uGreaterBranchHistoryWriteGates n counterWidth historyIndex)

/-- The comparison-conditioned `uGreater` history-write program is a concrete
encoded-bit base-gate realization over the Montgomery--Kaliski register
layout. -/
theorem uGreaterBranchHistoryWrite_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (uGreaterBranchHistoryWriteProgram n counterWidth historyIndex)
      (uGreaterBranchHistoryWriteStep n counterWidth historyIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uGreaterBranchHistoryWriteGates n counterWidth historyIndex)

/-- On clean scratchB, the comparison-conditioned `uGreater` slice toggles the
selected `m_i` bit exactly when the active flag and supplied comparison bit are
set. -/
theorem uGreaterBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          (RegisterBits.compareBit n counterWidth).get x)) := by
  simpa [uGreaterBranchHistoryWriteStep, uGreaterBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep, Branch.historyBit] using
    activeConditionBranchHistoryWriteStep_get_history_clean n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.uGreater historyIndex x hscratchB

/-- The comparison-conditioned `uGreater` history-write slice preserves every
history slot except the selected target slot. -/
theorem uGreaterBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed) (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth observed).get
        (uGreaterBranchHistoryWriteStep n counterWidth target x) =
      (RegisterBits.historyBit n counterWidth observed).get x := by
  simpa [uGreaterBranchHistoryWriteStep, uGreaterBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_historyBit_of_ne n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.uGreater target observed hne x

/-- The comparison-conditioned `uGreater` history-write slice preserves the
comparison condition bit supplied by the selector. -/
theorem uGreaterBranchHistoryWriteStep_get_compare
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.compareBit n counterWidth).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.compareBit n counterWidth).get x := by
  simpa [uGreaterBranchHistoryWriteStep, uGreaterBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep]
    using
      activeConditionBranchHistoryWriteStep_get_condition n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater historyIndex
        (RegisterBits.compare_history_wire_ne n counterWidth historyIndex) x

/-- The comparison-conditioned `uGreater` history-write slice preserves the
active flag. -/
theorem uGreaterBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  simpa [uGreaterBranchHistoryWriteStep, uGreaterBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
      activeConditionBranchHistoryWriteStep_get_active n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater historyIndex x

/-- The comparison-conditioned `uGreater` history-write slice restores
scratchA after staging and unstaging the branch code. -/
theorem uGreaterBranchHistoryWriteStep_get_scratchA
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.scratchABit n counterWidth).get x := by
  simpa [uGreaterBranchHistoryWriteStep, uGreaterBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
      activeConditionBranchHistoryWriteStep_get_scratchA n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.uGreater historyIndex
        (RegisterBits.compare_history_wire_ne n counterWidth historyIndex) x

/-- The comparison-conditioned `uGreater` history-write slice preserves every
little-endian `u` value bit. -/
theorem uGreaterBranchHistoryWriteStep_get_uWordBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uValueBit n counterWidth bit).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.uValueBit n counterWidth bit).get x := by
  simpa [uGreaterBranchHistoryWriteStep, uGreaterBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_of_preserved n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.uGreater historyIndex
      (RegisterBits.uValueBit n counterWidth bit)
      (by
        simpa [RegisterBits.uValueBit] using
          Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.uValueBit] using
          Ne.symm (RegisterBits.u_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.uValueBit] using
          Ne.symm (RegisterBits.u_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex))
      x

/-- The comparison-conditioned `uGreater` history-write slice preserves every
little-endian `v` value bit. -/
theorem uGreaterBranchHistoryWriteStep_get_vWordBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vValueBit n counterWidth bit).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.vValueBit n counterWidth bit).get x := by
  simpa [uGreaterBranchHistoryWriteStep, uGreaterBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_of_preserved n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.uGreater historyIndex
      (RegisterBits.vValueBit n counterWidth bit)
      (by
        simpa [RegisterBits.vValueBit] using
          Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.vValueBit] using
          Ne.symm (RegisterBits.v_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.vValueBit] using
          Ne.symm (RegisterBits.v_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex))
      x

/-- The comparison-conditioned `uGreater` history-write slice preserves every
little-endian `s` coefficient value bit. -/
theorem uGreaterBranchHistoryWriteStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (bit : Fin (n + 1)) (x : Registers n counterWidth) :
    (RegisterBits.sCoeffValueBit n counterWidth bit).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.sCoeffValueBit n counterWidth bit).get x := by
  simpa [uGreaterBranchHistoryWriteStep, uGreaterBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_of_preserved n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.uGreater historyIndex
      (RegisterBits.sCoeffValueBit n counterWidth bit)
      (by
        simpa [RegisterBits.sCoeffValueBit] using
          Ne.symm (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.sCoeffValueBit] using
          Ne.symm (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.sCoeffValueBit] using
          Ne.symm (RegisterBits.sCoeff_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex))
      x

/-- The comparison-conditioned `uGreater` history-write slice preserves every
little-endian `r` coefficient value bit. -/
theorem uGreaterBranchHistoryWriteStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (bit : Fin (n + 1)) (x : Registers n counterWidth) :
    (RegisterBits.rCoeffValueBit n counterWidth bit).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.rCoeffValueBit n counterWidth bit).get x := by
  simpa [uGreaterBranchHistoryWriteStep, uGreaterBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_of_preserved n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.uGreater historyIndex
      (RegisterBits.rCoeffValueBit n counterWidth bit)
      (by
        simpa [RegisterBits.rCoeffValueBit] using
          Ne.symm (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.rCoeffValueBit] using
          Ne.symm (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.rCoeffValueBit] using
          Ne.symm (RegisterBits.rCoeff_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex))
      x

/-- Lifted semantic step for the comparison-conditioned `uGreater`
history-write slice over the attached comparison-work register. -/
def liftedUGreaterBranchHistoryWriteStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x => (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x.1, x.2)

/-- Circuit for the lifted comparison-conditioned `uGreater` history write. -/
def liftedUGreaterBranchHistoryWriteProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (uGreaterBranchHistoryWriteProgram n counterWidth historyIndex)

/-- The lifted `uGreater` history-write circuit realizes its product action. -/
theorem liftedUGreaterBranchHistoryWrite_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (liftedUGreaterBranchHistoryWriteProgram n counterWidth historyIndex)
      (liftedUGreaterBranchHistoryWriteStep n counterWidth historyIndex) := by
  unfold liftedUGreaterBranchHistoryWriteProgram
    liftedUGreaterBranchHistoryWriteStep
  simpa [registersWithComparisonWorkEncoding] using
    UnitaryCircuit.Realizes.onBinaryPrefix
      (right := comparisonWorkEncoding n)
      (uGreaterBranchHistoryWrite_realizes n counterWidth historyIndex)

/-- On clean lifted scratchB, the lifted comparison-conditioned `uGreater`
slice toggles the selected branch-history bit exactly when the lifted active
flag and lifted comparison bit are set. -/
theorem liftedUGreaterBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hscratchB : (liftedScratchBBit n counterWidth).get x = false) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (liftedUGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      ((liftedHistoryBit n counterWidth historyIndex).get x ^^
        ((liftedActiveBit n counterWidth).get x &&
          (liftedCompareBit n counterWidth).get x)) := by
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x.1) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x.1 ^^
        ((RegisterBits.activeBit n counterWidth).get x.1 &&
          (RegisterBits.compareBit n counterWidth).get x.1))
  apply uGreaterBranchHistoryWriteStep_get_history_clean
  change (RegisterBits.scratchBBit n counterWidth).get x.1 = false at hscratchB
  exact hscratchB

/-- The lifted `uGreater` history-write slice preserves every history slot
except the selected target slot. -/
theorem liftedUGreaterBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth observed).get
        (liftedUGreaterBranchHistoryWriteStep n counterWidth target x) =
      (liftedHistoryBit n counterWidth observed).get x := by
  change (RegisterBits.historyBit n counterWidth observed).get
        (uGreaterBranchHistoryWriteStep n counterWidth target x.1) =
      (RegisterBits.historyBit n counterWidth observed).get x.1
  exact uGreaterBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth target observed hne x.1

/-- The lifted `uGreater` branch-history write preserves every comparison-work
carry bit, because it only acts on the leading Kaliski registers. -/
theorem liftedUGreaterBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (liftedUGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  rfl

/-- The lifted comparison-conditioned `uGreater` history-write slice preserves
the lifted comparison condition bit. -/
theorem liftedUGreaterBranchHistoryWriteStep_get_compare
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (liftedUGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (liftedCompareBit n counterWidth).get x := by
  change (RegisterBits.compareBit n counterWidth).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x.1) =
      (RegisterBits.compareBit n counterWidth).get x.1
  exact uGreaterBranchHistoryWriteStep_get_compare n counterWidth
    historyIndex x.1

/-- The lifted comparison-conditioned `uGreater` history-write slice preserves
the lifted active flag. -/
theorem liftedUGreaterBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (liftedUGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (liftedActiveBit n counterWidth).get x := by
  change (RegisterBits.activeBit n counterWidth).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x.1) =
      (RegisterBits.activeBit n counterWidth).get x.1
  exact uGreaterBranchHistoryWriteStep_get_active n counterWidth
    historyIndex x.1

/-- The lifted comparison-conditioned `uGreater` history-write slice restores
the lifted scratchA bit. -/
theorem liftedUGreaterBranchHistoryWriteStep_get_scratchA
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (liftedUGreaterBranchHistoryWriteStep n counterWidth historyIndex x) =
      (liftedScratchABit n counterWidth).get x := by
  change (RegisterBits.scratchABit n counterWidth).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex x.1) =
      (RegisterBits.scratchABit n counterWidth).get x.1
  exact uGreaterBranchHistoryWriteStep_get_scratchA n counterWidth
    historyIndex x.1

/-- Semantic composition of the full `uGreater` comparison selector followed by
the lifted `uGreater` branch-history write. -/
def uGreaterSelectorBranchHistoryWriteStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x =>
    liftedUGreaterBranchHistoryWriteStep n counterWidth historyIndex
      (uGreaterScratchACompareSelectorStep n counterWidth bit x)

/-- Circuit for the composed `uGreater` selector/history-write slice. -/
def uGreaterSelectorBranchHistoryWriteProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (uGreaterScratchACompareSelectorProgram n counterWidth bit)
    (liftedUGreaterBranchHistoryWriteProgram n counterWidth historyIndex)

/-- The composed `uGreater` selector/history-write circuit realizes its step. -/
theorem uGreaterSelectorBranchHistoryWrite_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (uGreaterSelectorBranchHistoryWriteProgram n counterWidth bit historyIndex)
      (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex) := by
  unfold uGreaterSelectorBranchHistoryWriteProgram
    uGreaterSelectorBranchHistoryWriteStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := uGreaterScratchACompareSelectorStep n counterWidth bit)
    (secondStep :=
      liftedUGreaterBranchHistoryWriteStep n counterWidth historyIndex)
    (uGreaterScratchACompareSelector_realizes n counterWidth bit)
    (liftedUGreaterBranchHistoryWrite_realizes n counterWidth historyIndex)

/-- The composed `uGreater` selector/history-write slice restores every
comparison-work carry bit.  This ties the selector restoration theorem to the
same composed base-gate program used for the history-write endpoint. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit historyIndex
          x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  unfold uGreaterSelectorBranchHistoryWriteStep
  rw [liftedUGreaterBranchHistoryWriteStep_get_comparisonCarry]
  exact uGreaterScratchACompareSelectorStep_get_comparisonCarry n counterWidth
    bit workBit x

/-- The composed `uGreater` selector/history-write slice preserves the active
flag through selector restoration and branch-history write. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (liftedActiveBit n counterWidth).get x := by
  unfold uGreaterSelectorBranchHistoryWriteStep
  rw [liftedUGreaterBranchHistoryWriteStep_get_active]
  exact uGreaterScratchACompareSelectorStep_get_active n counterWidth bit x

/-- The composed `uGreater` selector/history-write slice preserves scratchA;
the comparator restores its borrow input and the history write unstages the
branch-code bit. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (liftedScratchABit n counterWidth).get x := by
  unfold uGreaterSelectorBranchHistoryWriteStep
  rw [liftedUGreaterBranchHistoryWriteStep_get_scratchA]
  exact uGreaterScratchACompareSelectorStep_get_scratchA n counterWidth bit x

/-- The composed `uGreater` selector/history-write slice preserves every
little-endian `u` value bit. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_uWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedUWord n counterWidth).bit targetBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((liftedUWord n counterWidth).bit targetBit).get x := by
  unfold uGreaterSelectorBranchHistoryWriteStep
  change (RegisterBits.uValueBit n counterWidth targetBit).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex
          (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
            x).1) =
      ((liftedUWord n counterWidth).bit targetBit).get x
  rw [uGreaterBranchHistoryWriteStep_get_uWordBit]
  exact uGreaterScratchACompareSelectorStep_get_uWordBit
    n counterWidth selectorBit targetBit x

/-- The composed `uGreater` selector/history-write slice preserves every
little-endian `v` value bit. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_vWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit targetBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((liftedVWord n counterWidth).bit targetBit).get x := by
  unfold uGreaterSelectorBranchHistoryWriteStep
  change (RegisterBits.vValueBit n counterWidth targetBit).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex
          (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
            x).1) =
      ((liftedVWord n counterWidth).bit targetBit).get x
  rw [uGreaterBranchHistoryWriteStep_get_vWordBit]
  exact uGreaterScratchACompareSelectorStep_get_vWordBit
    n counterWidth selectorBit targetBit x

/-- The composed `uGreater` selector/history-write slice preserves every
little-endian `s` coefficient value bit. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x := by
  unfold uGreaterSelectorBranchHistoryWriteStep
  change (RegisterBits.sCoeffValueBit n counterWidth targetBit).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex
          (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
            x).1) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x
  rw [uGreaterBranchHistoryWriteStep_get_sCoeffValueWordBit]
  exact uGreaterScratchACompareSelectorStep_get_sCoeffValueWordBit
    n counterWidth selectorBit targetBit x

/-- The composed `uGreater` selector/history-write slice preserves every
little-endian `r` coefficient value bit. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x := by
  unfold uGreaterSelectorBranchHistoryWriteStep
  change (RegisterBits.rCoeffValueBit n counterWidth targetBit).get
        (uGreaterBranchHistoryWriteStep n counterWidth historyIndex
          (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
            x).1) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x
  rw [uGreaterBranchHistoryWriteStep_get_rCoeffValueWordBit]
  exact uGreaterScratchACompareSelectorStep_get_rCoeffValueWordBit
    n counterWidth selectorBit targetBit x

/-- On clean comparison work and clean scratchA, the composed `uGreater`
selector/history-write slice leaves the comparison bit equal to the staged
`uGreater` predicate `v < u`. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (liftedCompareBit n counterWidth).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit historyIndex
          (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val) := by
  unfold uGreaterSelectorBranchHistoryWriteStep
  rw [liftedUGreaterBranchHistoryWriteStep_get_compare]
  exact uGreaterScratchACompareSelectorStep_get_compare_clean n counterWidth
    bit x hscratchA hcompare hfinal

/-- On clean comparison work and clean scratch ancillas, the composed
`uGreater` selector/history-write slice toggles the selected history bit exactly
when the round is active and `v < u`.  This endpoint theorem is paired with the
selector work-restoration theorem above
[RNSL17, ECDLP.tex:399-421,468-475]. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : bit.val + 1 = n) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit historyIndex
          (x, cleanComparisonWork n)) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val))) := by
  let selected :=
    uGreaterScratchACompareSelectorStep n counterWidth bit
      (x, cleanComparisonWork n)
  have hscratchBSelected :
      (liftedScratchBBit n counterWidth).get selected = false := by
    dsimp [selected]
    rw [uGreaterScratchACompareSelectorStep_get_scratchB]
    change (RegisterBits.scratchBBit n counterWidth).get x = false
    exact hscratchB
  unfold uGreaterSelectorBranchHistoryWriteStep
  rw [liftedUGreaterBranchHistoryWriteStep_get_history_clean
    n counterWidth historyIndex selected hscratchBSelected]
  dsimp [selected]
  rw [uGreaterScratchACompareSelectorStep_get_historyBit]
  rw [uGreaterScratchACompareSelectorStep_get_active]
  rw [uGreaterScratchACompareSelectorStep_get_compare_clean n counterWidth
    bit x hscratchA hcompare hfinal]
  change
    ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
      ((RegisterBits.activeBit n counterWidth).get x &&
        decide (x.v.val < x.u.val))) =
    ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
      ((RegisterBits.activeBit n counterWidth).get x &&
        decide (x.v.val < x.u.val)))
  rfl

/-- The composed `uGreater` selector/history-write slice preserves every
history slot except the selected target slot. -/
theorem uGreaterSelectorBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth observed).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit target x) =
      (liftedHistoryBit n counterWidth observed).get x := by
  unfold uGreaterSelectorBranchHistoryWriteStep
  rw [liftedUGreaterBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth target observed hne]
  exact uGreaterScratchACompareSelectorStep_get_historyBit
    n counterWidth bit observed x

/-- Gate list that applies the RNSL17 `vLe` history-write slice from a supplied
comparison ancilla.  The `vLe` branch history-code bit is zero, so this bridge
is a concrete no-op write for `m_i`; the composed selector/history witness
below ties this supplied-condition bridge to the same concrete comparator path
[RNSL17, ECDLP.tex:399-421,468-475].
-/
def vLeBranchHistoryWriteGates
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  activeConditionBranchHistoryWriteGates n counterWidth
    (RegisterBits.compareBit n counterWidth)
    (RegisterBits.active_compare_wire_ne n counterWidth)
    (RegisterBits.compare_scratchA_wire_ne n counterWidth)
    (RegisterBits.compare_scratchB_wire_ne n counterWidth)
    Branch.vLe historyIndex

/-- Base-gate program for the comparison-conditioned `vLe` history-write
slice. -/
def vLeBranchHistoryWriteProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (vLeBranchHistoryWriteGates n counterWidth historyIndex)

/-- Semantic step for the comparison-conditioned `vLe` history-write slice. -/
def vLeBranchHistoryWriteStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (vLeBranchHistoryWriteGates n counterWidth historyIndex)

/-- The comparison-conditioned `vLe` history-write program is a concrete
encoded-bit base-gate realization over the Montgomery--Kaliski register
layout. -/
theorem vLeBranchHistoryWrite_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (vLeBranchHistoryWriteProgram n counterWidth historyIndex)
      (vLeBranchHistoryWriteStep n counterWidth historyIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (vLeBranchHistoryWriteGates n counterWidth historyIndex)

/-- On clean scratchB, the comparison-conditioned `vLe` slice leaves the
selected `m_i` bit unchanged, matching the `vLe` history code bit `0`
[RNSL17, ECDLP.tex:471].
-/
theorem vLeBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  simpa [vLeBranchHistoryWriteStep, vLeBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep, Branch.historyBit] using
    activeConditionBranchHistoryWriteStep_get_history_clean n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.vLe historyIndex x hscratchB

/-- The comparison-conditioned `vLe` history-write slice preserves every
history slot except the selected target slot. -/
theorem vLeBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed) (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth observed).get
        (vLeBranchHistoryWriteStep n counterWidth target x) =
      (RegisterBits.historyBit n counterWidth observed).get x := by
  simpa [vLeBranchHistoryWriteStep, vLeBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_historyBit_of_ne n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.vLe target observed hne x

/-- The comparison-conditioned `vLe` history-write slice preserves the
comparison condition bit supplied by the selector. -/
theorem vLeBranchHistoryWriteStep_get_compare
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.compareBit n counterWidth).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.compareBit n counterWidth).get x := by
  simpa [vLeBranchHistoryWriteStep, vLeBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep]
    using
      activeConditionBranchHistoryWriteStep_get_condition n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe historyIndex
        (RegisterBits.compare_history_wire_ne n counterWidth historyIndex) x

/-- The comparison-conditioned `vLe` history-write slice preserves the active
flag. -/
theorem vLeBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  simpa [vLeBranchHistoryWriteStep, vLeBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
      activeConditionBranchHistoryWriteStep_get_active n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe historyIndex x

/-- The comparison-conditioned `vLe` history-write slice preserves scratchA.
For this zero-code branch, the staging gates leave scratchA unchanged. -/
theorem vLeBranchHistoryWriteStep_get_scratchA
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.scratchABit n counterWidth).get x := by
  simpa [vLeBranchHistoryWriteStep, vLeBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
      activeConditionBranchHistoryWriteStep_get_scratchA n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth)
        Branch.vLe historyIndex
        (RegisterBits.compare_history_wire_ne n counterWidth historyIndex) x

/-- The comparison-conditioned `vLe` history-write slice preserves every
little-endian `u` value bit. -/
theorem vLeBranchHistoryWriteStep_get_uWordBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uValueBit n counterWidth bit).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.uValueBit n counterWidth bit).get x := by
  simpa [vLeBranchHistoryWriteStep, vLeBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_of_preserved n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.vLe historyIndex
      (RegisterBits.uValueBit n counterWidth bit)
      (by
        simpa [RegisterBits.uValueBit] using
          Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.uValueBit] using
          Ne.symm (RegisterBits.u_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.uValueBit] using
          Ne.symm (RegisterBits.u_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex))
      x

/-- The comparison-conditioned `vLe` history-write slice preserves every
little-endian `v` value bit. -/
theorem vLeBranchHistoryWriteStep_get_vWordBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vValueBit n counterWidth bit).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.vValueBit n counterWidth bit).get x := by
  simpa [vLeBranchHistoryWriteStep, vLeBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_of_preserved n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.vLe historyIndex
      (RegisterBits.vValueBit n counterWidth bit)
      (by
        simpa [RegisterBits.vValueBit] using
          Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.vValueBit] using
          Ne.symm (RegisterBits.v_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.vValueBit] using
          Ne.symm (RegisterBits.v_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex))
      x

/-- The comparison-conditioned `vLe` history-write slice preserves every
little-endian `s` coefficient value bit. -/
theorem vLeBranchHistoryWriteStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (bit : Fin (n + 1)) (x : Registers n counterWidth) :
    (RegisterBits.sCoeffValueBit n counterWidth bit).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.sCoeffValueBit n counterWidth bit).get x := by
  simpa [vLeBranchHistoryWriteStep, vLeBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_of_preserved n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.vLe historyIndex
      (RegisterBits.sCoeffValueBit n counterWidth bit)
      (by
        simpa [RegisterBits.sCoeffValueBit] using
          Ne.symm (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.sCoeffValueBit] using
          Ne.symm (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.sCoeffValueBit] using
          Ne.symm (RegisterBits.sCoeff_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex))
      x

/-- The comparison-conditioned `vLe` history-write slice preserves every
little-endian `r` coefficient value bit. -/
theorem vLeBranchHistoryWriteStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (bit : Fin (n + 1)) (x : Registers n counterWidth) :
    (RegisterBits.rCoeffValueBit n counterWidth bit).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (RegisterBits.rCoeffValueBit n counterWidth bit).get x := by
  simpa [vLeBranchHistoryWriteStep, vLeBranchHistoryWriteGates,
    activeConditionBranchHistoryWriteStep] using
    activeConditionBranchHistoryWriteStep_get_of_preserved n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      Branch.vLe historyIndex
      (RegisterBits.rCoeffValueBit n counterWidth bit)
      (by
        simpa [RegisterBits.rCoeffValueBit] using
          Ne.symm (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.rCoeffValueBit] using
          Ne.symm (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa [RegisterBits.rCoeffValueBit] using
          Ne.symm (RegisterBits.rCoeff_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex))
      x

/-- Lifted semantic step for the comparison-conditioned `vLe`
history-write slice over the attached comparison-work register. -/
def liftedVLeBranchHistoryWriteStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x => (vLeBranchHistoryWriteStep n counterWidth historyIndex x.1, x.2)

/-- Circuit for the lifted comparison-conditioned `vLe` history write. -/
def liftedVLeBranchHistoryWriteProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (vLeBranchHistoryWriteProgram n counterWidth historyIndex)

/-- The lifted `vLe` history-write circuit realizes its product action. -/
theorem liftedVLeBranchHistoryWrite_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (liftedVLeBranchHistoryWriteProgram n counterWidth historyIndex)
      (liftedVLeBranchHistoryWriteStep n counterWidth historyIndex) := by
  unfold liftedVLeBranchHistoryWriteProgram liftedVLeBranchHistoryWriteStep
  simpa [registersWithComparisonWorkEncoding] using
    UnitaryCircuit.Realizes.onBinaryPrefix
      (right := comparisonWorkEncoding n)
      (vLeBranchHistoryWrite_realizes n counterWidth historyIndex)

/-- On clean lifted scratchB, the lifted comparison-conditioned `vLe` slice
leaves the selected branch-history bit unchanged. -/
theorem liftedVLeBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hscratchB : (liftedScratchBBit n counterWidth).get x = false) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (liftedVLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (liftedHistoryBit n counterWidth historyIndex).get x := by
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x.1) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x.1
  apply vLeBranchHistoryWriteStep_get_history_clean
  change (RegisterBits.scratchBBit n counterWidth).get x.1 = false at hscratchB
  exact hscratchB

/-- The lifted `vLe` history-write slice preserves every history slot except
the selected target slot. -/
theorem liftedVLeBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth observed).get
        (liftedVLeBranchHistoryWriteStep n counterWidth target x) =
      (liftedHistoryBit n counterWidth observed).get x := by
  change (RegisterBits.historyBit n counterWidth observed).get
        (vLeBranchHistoryWriteStep n counterWidth target x.1) =
      (RegisterBits.historyBit n counterWidth observed).get x.1
  exact vLeBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth target observed hne x.1

/-- The lifted `vLe` branch-history write preserves every comparison-work carry
bit, because it only acts on the leading Kaliski registers. -/
theorem liftedVLeBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (liftedVLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  rfl

/-- The lifted comparison-conditioned `vLe` history-write slice preserves the
lifted comparison condition bit. -/
theorem liftedVLeBranchHistoryWriteStep_get_compare
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (liftedVLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (liftedCompareBit n counterWidth).get x := by
  change (RegisterBits.compareBit n counterWidth).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x.1) =
      (RegisterBits.compareBit n counterWidth).get x.1
  exact vLeBranchHistoryWriteStep_get_compare n counterWidth historyIndex x.1

/-- The lifted comparison-conditioned `vLe` history-write slice preserves the
lifted active flag. -/
theorem liftedVLeBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (liftedVLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (liftedActiveBit n counterWidth).get x := by
  change (RegisterBits.activeBit n counterWidth).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x.1) =
      (RegisterBits.activeBit n counterWidth).get x.1
  exact vLeBranchHistoryWriteStep_get_active n counterWidth historyIndex x.1

/-- The lifted comparison-conditioned `vLe` history-write slice preserves the
lifted scratchA bit. -/
theorem liftedVLeBranchHistoryWriteStep_get_scratchA
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (liftedVLeBranchHistoryWriteStep n counterWidth historyIndex x) =
      (liftedScratchABit n counterWidth).get x := by
  change (RegisterBits.scratchABit n counterWidth).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex x.1) =
      (RegisterBits.scratchABit n counterWidth).get x.1
  exact vLeBranchHistoryWriteStep_get_scratchA n counterWidth historyIndex x.1

/-- Semantic composition of the full comparison selector followed by the lifted
`vLe` branch-history write. -/
def vLeSelectorBranchHistoryWriteStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x =>
    liftedVLeBranchHistoryWriteStep n counterWidth historyIndex
      (uGreaterScratchACompareSelectorStep n counterWidth bit x)

/-- Circuit for the composed selector/`vLe` history-write slice. -/
def vLeSelectorBranchHistoryWriteProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (uGreaterScratchACompareSelectorProgram n counterWidth bit)
    (liftedVLeBranchHistoryWriteProgram n counterWidth historyIndex)

/-- The composed selector/`vLe` history-write circuit realizes its step. -/
theorem vLeSelectorBranchHistoryWrite_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (vLeSelectorBranchHistoryWriteProgram n counterWidth bit historyIndex)
      (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex) := by
  unfold vLeSelectorBranchHistoryWriteProgram vLeSelectorBranchHistoryWriteStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := uGreaterScratchACompareSelectorStep n counterWidth bit)
    (secondStep := liftedVLeBranchHistoryWriteStep n counterWidth historyIndex)
    (uGreaterScratchACompareSelector_realizes n counterWidth bit)
    (liftedVLeBranchHistoryWrite_realizes n counterWidth historyIndex)

/-- The composed selector/`vLe` history-write slice restores every
comparison-work carry bit. -/
theorem vLeSelectorBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  unfold vLeSelectorBranchHistoryWriteStep
  rw [liftedVLeBranchHistoryWriteStep_get_comparisonCarry]
  exact uGreaterScratchACompareSelectorStep_get_comparisonCarry n counterWidth
    bit workBit x

/-- The composed selector/`vLe` history-write slice preserves the active flag
through selector restoration and the zero-code history write. -/
theorem vLeSelectorBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedActiveBit n counterWidth).get x := by
  unfold vLeSelectorBranchHistoryWriteStep
  rw [liftedVLeBranchHistoryWriteStep_get_active]
  exact uGreaterScratchACompareSelectorStep_get_active n counterWidth bit x

/-- The composed selector/`vLe` history-write slice preserves scratchA through
selector restoration and the zero-code history write. -/
theorem vLeSelectorBranchHistoryWriteStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedScratchABit n counterWidth).get x := by
  unfold vLeSelectorBranchHistoryWriteStep
  rw [liftedVLeBranchHistoryWriteStep_get_scratchA]
  exact uGreaterScratchACompareSelectorStep_get_scratchA n counterWidth bit x

/-- The composed selector/`vLe` history-write slice preserves every
little-endian `u` value bit. -/
theorem vLeSelectorBranchHistoryWriteStep_get_uWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedUWord n counterWidth).bit targetBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((liftedUWord n counterWidth).bit targetBit).get x := by
  unfold vLeSelectorBranchHistoryWriteStep
  change (RegisterBits.uValueBit n counterWidth targetBit).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex
          (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
            x).1) =
      ((liftedUWord n counterWidth).bit targetBit).get x
  rw [vLeBranchHistoryWriteStep_get_uWordBit]
  exact uGreaterScratchACompareSelectorStep_get_uWordBit
    n counterWidth selectorBit targetBit x

/-- The composed selector/`vLe` history-write slice preserves every
little-endian `v` value bit. -/
theorem vLeSelectorBranchHistoryWriteStep_get_vWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit targetBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((liftedVWord n counterWidth).bit targetBit).get x := by
  unfold vLeSelectorBranchHistoryWriteStep
  change (RegisterBits.vValueBit n counterWidth targetBit).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex
          (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
            x).1) =
      ((liftedVWord n counterWidth).bit targetBit).get x
  rw [vLeBranchHistoryWriteStep_get_vWordBit]
  exact uGreaterScratchACompareSelectorStep_get_vWordBit
    n counterWidth selectorBit targetBit x

/-- The composed selector/`vLe` history-write slice preserves every
little-endian `s` coefficient value bit. -/
theorem vLeSelectorBranchHistoryWriteStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x := by
  unfold vLeSelectorBranchHistoryWriteStep
  change (RegisterBits.sCoeffValueBit n counterWidth targetBit).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex
          (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
            x).1) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x
  rw [vLeBranchHistoryWriteStep_get_sCoeffValueWordBit]
  exact uGreaterScratchACompareSelectorStep_get_sCoeffValueWordBit
    n counterWidth selectorBit targetBit x

/-- The composed selector/`vLe` history-write slice preserves every
little-endian `r` coefficient value bit. -/
theorem vLeSelectorBranchHistoryWriteStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x := by
  unfold vLeSelectorBranchHistoryWriteStep
  change (RegisterBits.rCoeffValueBit n counterWidth targetBit).get
        (vLeBranchHistoryWriteStep n counterWidth historyIndex
          (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
            x).1) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x
  rw [vLeBranchHistoryWriteStep_get_rCoeffValueWordBit]
  exact uGreaterScratchACompareSelectorStep_get_rCoeffValueWordBit
    n counterWidth selectorBit targetBit x

/-- On clean comparison work and clean scratchA, the composed selector/`vLe`
history-write slice leaves the comparison bit equal to the staged `uGreater`
predicate `v < u`; the `vLe` history code itself is the zero-code complement
handled by the history endpoint below. -/
theorem vLeSelectorBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (liftedCompareBit n counterWidth).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex
          (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val) := by
  unfold vLeSelectorBranchHistoryWriteStep
  rw [liftedVLeBranchHistoryWriteStep_get_compare]
  exact uGreaterScratchACompareSelectorStep_get_compare_clean n counterWidth
    bit x hscratchA hcompare hfinal

/-- On clean scratchB, the composed selector/`vLe` history-write slice leaves
the selected history bit unchanged.  This realizes the RNSL17 `vLe` history
code bit `0` through the same concrete selector/bridge composition
[RNSL17, ECDLP.tex:399-421,468-475]. -/
theorem vLeSelectorBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth)
    (hscratchB : (liftedScratchBBit n counterWidth).get x = false) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex x) =
      (liftedHistoryBit n counterWidth historyIndex).get x := by
  let selected := uGreaterScratchACompareSelectorStep n counterWidth bit x
  have hscratchBSelected :
      (liftedScratchBBit n counterWidth).get selected = false := by
    dsimp [selected]
    rw [uGreaterScratchACompareSelectorStep_get_scratchB]
    exact hscratchB
  unfold vLeSelectorBranchHistoryWriteStep
  rw [liftedVLeBranchHistoryWriteStep_get_history_clean
    n counterWidth historyIndex selected hscratchBSelected]
  dsimp [selected]
  rw [uGreaterScratchACompareSelectorStep_get_historyBit]

/-- The composed selector/`vLe` history-write slice preserves every history
slot except the selected target slot. -/
theorem vLeSelectorBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth observed).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit target x) =
      (liftedHistoryBit n counterWidth observed).get x := by
  unfold vLeSelectorBranchHistoryWriteStep
  rw [liftedVLeBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth target observed hne]
  exact uGreaterScratchACompareSelectorStep_get_historyBit
    n counterWidth bit observed x

/-! ## Coefficient-work-lifted comparison selector -/

/-- Gate list for the cleanup-compatible `uGreater` comparison selector after
lifting it over the trailing coefficient-adder work object. -/
def coeffWorkUGreaterScratchACompareSelectorGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  (uGreaterScratchACompareSelectorGates n counterWidth bit).map
    (EncodedBit.GateSpec.prodLeft (coeffAdderWorkEncoding n))

/-- Base-gate program for the coefficient-work-lifted cleanup-compatible
`uGreater` comparison selector. -/
def coeffWorkUGreaterScratchACompareSelectorProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit)

/-- Coefficient-work-lifted cleanup-compatible `uGreater` comparison selector.
On clean comparison inputs at the final bit, this writes the predicate `v < u`
into `compare`; it does not yet write branch history or apply the odd data
path. -/
def coeffWorkUGreaterScratchACompareSelectorStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (uGreaterScratchACompareSelectorStep n counterWidth bit)

/-- The explicit coefficient-work gate list has the same folded semantics as
the lifted comparison selector step. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_eq_gateList
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit) x =
      coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x := by
  change
    EncodedBit.GateSpec.stepList
        ((uGreaterScratchACompareSelectorGates n counterWidth bit).map
          (EncodedBit.GateSpec.prodLeft (coeffAdderWorkEncoding n))) x =
      (uGreaterScratchACompareSelectorStep n counterWidth bit x.1, x.2)
  exact
    EncodedBit.GateSpec.stepList_prodLeft
      (coeffAdderWorkEncoding n)
      (uGreaterScratchACompareSelectorGates n counterWidth bit) x

/-- Product lifting preserves the selector's exact physical length. -/
theorem coeffWorkUGreaterScratchACompareSelectorGates_length
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffWorkUGreaterScratchACompareSelectorGates
      n counterWidth bit).length = 10 * n + 1 := by
  simp only [coeffWorkUGreaterScratchACompareSelectorGates, List.length_map,
    uGreaterScratchACompareSelectorGates_length]

/-- Product lifting preserves the selector's exact X coordinate. -/
theorem coeffWorkUGreaterScratchACompareSelectorGates_xMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit).map
      EncodedBit.GateSpec.xMultiplicity).sum = 4 * n := by
  calc
    ((coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit).map
        EncodedBit.GateSpec.xMultiplicity).sum =
        ((uGreaterScratchACompareSelectorGates n counterWidth bit).map
          EncodedBit.GateSpec.xMultiplicity).sum :=
      EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
        .empty
        (EncodedBit.GateSpec.map_event_prodLeft (coeffAdderWorkEncoding n)
          (uGreaterScratchACompareSelectorGates n counterWidth bit))
    _ = 4 * n :=
      uGreaterScratchACompareSelectorGates_xMultiplicity_sum
        n counterWidth bit

/-- Product lifting preserves the selector's exact CNOT coordinate. -/
theorem coeffWorkUGreaterScratchACompareSelectorGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  calc
    ((coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
        ((uGreaterScratchACompareSelectorGates n counterWidth bit).map
          EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        .empty
        (EncodedBit.GateSpec.map_event_prodLeft (coeffAdderWorkEncoding n)
          (uGreaterScratchACompareSelectorGates n counterWidth bit))
    _ = 1 :=
      uGreaterScratchACompareSelectorGates_cnotMultiplicity_sum
        n counterWidth bit

/-- Product lifting preserves the selector's exact Toffoli coordinate. -/
theorem coeffWorkUGreaterScratchACompareSelectorGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * n := by
  calc
    ((coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
        ((uGreaterScratchACompareSelectorGates n counterWidth bit).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        .empty
        (EncodedBit.GateSpec.map_event_prodLeft (coeffAdderWorkEncoding n)
          (uGreaterScratchACompareSelectorGates n counterWidth bit))
    _ = 6 * n :=
      uGreaterScratchACompareSelectorGates_toffoliMultiplicity_sum
        n counterWidth bit

/-- The coefficient-work-lifted cleanup-compatible comparison selector gate
list realizes the lifted selector step. -/
theorem coeffWorkUGreaterScratchACompareSelector_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterScratchACompareSelectorProgram n counterWidth bit)
      (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit)
    (coeffWorkUGreaterScratchACompareSelectorStep_eq_gateList
      n counterWidth bit)

/-- On clean comparison inputs, the coefficient-work-lifted selector writes
the staged predicate `v < u` into `compare`. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  change (liftedCompareBit n counterWidth).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit
          (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val)
  exact uGreaterScratchACompareSelectorStep_get_compare_clean
    n counterWidth bit x hscratchA hcompare hfinal

/-- The coefficient-work-lifted selector preserves scratchA. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  change (liftedScratchABit n counterWidth).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x.1) =
      (liftedScratchABit n counterWidth).get x.1
  exact uGreaterScratchACompareSelectorStep_get_scratchA n counterWidth bit x.1

/-- The coefficient-work-lifted selector preserves scratchB. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_scratchB
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  change (liftedScratchBBit n counterWidth).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x.1) =
      (liftedScratchBBit n counterWidth).get x.1
  exact uGreaterScratchACompareSelectorStep_get_scratchB n counterWidth bit x.1

/-- The coefficient-work-lifted selector preserves the active flag. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_active
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  change (liftedActiveBit n counterWidth).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x.1) =
      (liftedActiveBit n counterWidth).get x.1
  exact uGreaterScratchACompareSelectorStep_get_active n counterWidth bit x.1

/-- The coefficient-work-lifted selector preserves every stored branch-history
bit. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_historyBit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  change (liftedHistoryBit n counterWidth historyIndex).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x.1) =
      (liftedHistoryBit n counterWidth historyIndex).get x.1
  exact uGreaterScratchACompareSelectorStep_get_historyBit
    n counterWidth bit historyIndex x.1

/-- The coefficient-work-lifted selector preserves every comparison-work carry
bit. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_comparisonCarry
    (n counterWidth : Nat) (bit workBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  change (liftedComparisonCarryBit n counterWidth workBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x.1) =
      (liftedComparisonCarryBit n counterWidth workBit).get x.1
  exact uGreaterScratchACompareSelectorStep_get_comparisonCarry
    n counterWidth bit workBit x.1

/-- The coefficient-work-lifted selector preserves the dedicated
coefficient-adder carry-in flag. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- The coefficient-work-lifted comparison selector preserves the complete
physical padding counter. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_counter
    (n counterWidth : Nat) (selectorBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterScratchACompareSelectorStep
        n counterWidth selectorBit x).1.1.counter = x.1.1.counter := by
  change
    (uGreaterScratchACompareSelectorStep
      n counterWidth selectorBit x.1).1.counter = x.1.1.counter
  apply word_eq_of_testBit_eq
  intro counterBit
  let observed :=
    liftRegisterBitToComparisonWork n counterWidth
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire counterBit))
  have h := uGreaterScratchACompareSelectorStep_get_of_preserved
    n counterWidth selectorBit observed
    (liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire counterBit))
      (RegisterBits.compare_counter_wire_ne n counterWidth
        (WireAddress.littleEndianWire counterBit)))
    (fun j =>
      liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth j)
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire counterBit))
        (by
          simpa [RegisterBits.vValueBit] using
            RegisterBits.v_counter_wire_ne n counterWidth
              (WireAddress.littleEndianWire j)
              (WireAddress.littleEndianWire counterBit)))
    (fun j =>
      Ne.symm (liftRegisterBit_liftComparisonWorkBit_wire_ne
        n counterWidth
        (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire counterBit))
        (comparisonCarryValueBit n j)))
    x.1
  change
    (uGreaterScratchACompareSelectorStep
      n counterWidth selectorBit x.1).1.counter.val.testBit counterBit.val =
      x.1.1.counter.val.testBit counterBit.val
  simpa [observed, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit,
    WireAddress.bitIndex_littleEndianWire] using h

/-- The coefficient-work-lifted selector preserves each dedicated
coefficient-adder carry-work bit. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryWorkBit
    (n counterWidth : Nat) (bit : Fin n) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- The coefficient-work-lifted selector preserves every little-endian `u`
value bit. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_uWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit targetBit).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth
          selectorBit x) =
      ((coeffAdderUWord n counterWidth).bit targetBit).get x := by
  change ((liftedUWord n counterWidth).bit targetBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
          x.1) =
      ((liftedUWord n counterWidth).bit targetBit).get x.1
  exact uGreaterScratchACompareSelectorStep_get_uWordBit
    n counterWidth selectorBit targetBit x.1

/-- The coefficient-work-lifted selector preserves every little-endian `v`
value bit. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_vWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit targetBit).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth
          selectorBit x) =
      ((coeffAdderVWord n counterWidth).bit targetBit).get x := by
  change ((liftedVWord n counterWidth).bit targetBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
          x.1) =
      ((liftedVWord n counterWidth).bit targetBit).get x.1
  exact uGreaterScratchACompareSelectorStep_get_vWordBit
    n counterWidth selectorBit targetBit x.1

/-- The coefficient-work-lifted selector preserves every little-endian `s`
coefficient value bit. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth
          selectorBit x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
          x.1) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact uGreaterScratchACompareSelectorStep_get_sCoeffValueWordBit
    n counterWidth selectorBit targetBit x.1

/-- The coefficient-work-lifted selector preserves every little-endian `r`
coefficient value bit. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth
          selectorBit x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth selectorBit
          x.1) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact uGreaterScratchACompareSelectorStep_get_rCoeffValueWordBit
    n counterWidth selectorBit targetBit x.1

/-- The coefficient-work-lifted selector preserves the `u` source word. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_u
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h :=
    coeffWorkUGreaterScratchACompareSelectorStep_get_uWordBit
      n counterWidth bit targetBit x
  simpa [coeffAdderUWord_get_testBit] using h

/-- The coefficient-work-lifted selector preserves the `v` source word. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_v
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h :=
    coeffWorkUGreaterScratchACompareSelectorStep_get_vWordBit
      n counterWidth bit targetBit x
  simpa [coeffAdderVWord_get_testBit] using h

/-- The coefficient-work-lifted selector preserves the `s` coefficient word. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_sCoeff
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h :=
    coeffWorkUGreaterScratchACompareSelectorStep_get_sCoeffValueWordBit
      n counterWidth bit targetBit x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- The coefficient-work-lifted selector preserves the `r` coefficient word. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_rCoeff
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h :=
    coeffWorkUGreaterScratchACompareSelectorStep_get_rCoeffValueWordBit
      n counterWidth bit targetBit x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- The coefficient-work-lifted selector preserves each comparison-prefix
carry bit used by the source-subtract adders. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_get_comparisonCarryPrefix
    (n counterWidth : Nat) (selectorBit : Fin n) (workBit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit workBit).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth
          selectorBit x) =
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit workBit).get
        x := by
  simpa [coeffAdderComparisonCarryPrefixWord] using
    coeffWorkUGreaterScratchACompareSelectorStep_get_comparisonCarry
      n counterWidth selectorBit (coeffAdderComparisonCarryPrefixIndex n workBit)
      x

/-- On clean comparison inputs, the coefficient-work-lifted selector establishes
compare-valid on its own output state. -/
theorem coeffWorkUGreaterScratchACompareSelectorStep_compare_valid_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
          ((x, cleanComparisonWork n), work)) =
      decide
        ((coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
            ((x, cleanComparisonWork n), work)).1.1.v.val <
          (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
            ((x, cleanComparisonWork n), work)).1.1.u.val) := by
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_compare_clean
    n counterWidth bit x work hscratchA hcompare hfinal]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]

/-- On clean comparison inputs, if both source words are odd and `v < u`, the
selector output already latches the branch decision as `uGreater` before any
odd data-path mutation. -/
theorem
    coeffWorkUGreaterScratchACompareSelectorStep_fromCoeffWorkSignals_uGreater_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val) :
    Branch.fromCoeffWorkSignals tail.succ counterWidth
        (coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth
          bit ((x, cleanComparisonWork tail.succ), work)) =
      Branch.uGreater := by
  have hcompareOut :
      (coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth
          bit ((x, cleanComparisonWork tail.succ), work)).1.1.compare =
        decide (x.v.val < x.u.val) := by
    simpa [coeffAdderCompareBit_get] using
      coeffWorkUGreaterScratchACompareSelectorStep_get_compare_clean
        tail.succ counterWidth bit x work hscratchA hcompare hfinal
  rw [Branch.fromCoeffWorkSignals]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
  rw [hcompareOut]
  simp [Branch.fromCircuitSignals, huOdd, hvOdd, hlt]

/-- On clean comparison inputs, if both source words are odd and `v < u` is
false, the selector output already latches the branch decision as `vLe` before
any odd data-path mutation. -/
theorem
    coeffWorkUGreaterScratchACompareSelectorStep_fromCoeffWorkSignals_vLe_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val) :
    Branch.fromCoeffWorkSignals tail.succ counterWidth
        (coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth
          bit ((x, cleanComparisonWork tail.succ), work)) =
      Branch.vLe := by
  have hcompareOut :
      (coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth
          bit ((x, cleanComparisonWork tail.succ), work)).1.1.compare =
        decide (x.v.val < x.u.val) := by
    simpa [coeffAdderCompareBit_get] using
      coeffWorkUGreaterScratchACompareSelectorStep_get_compare_clean
        tail.succ counterWidth bit x work hscratchA hcompare hfinal
  rw [Branch.fromCoeffWorkSignals]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
  rw [hcompareOut]
  simp [Branch.fromCircuitSignals, huOdd, hvOdd, hnlt]

/-- Compose the lifted cleanup-compatible comparison selector with the
compare-selected odd data path.  On clean comparison inputs, the reduction
lemmas below remove the external compare-valid assumption for the odd-odd
data-path slice; this is not yet an outer active-round wrapper. -/
def coeffWorkCompareSelectorThenSelectedOddDataPathStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkCompareSelectedOddDataPathStep n counterWidth
      (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit x)

/-- Gate list for the comparison selector followed by the selected odd data
path. -/
def coeffWorkCompareSelectorThenSelectedOddDataPathGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  coeffWorkUGreaterScratchACompareSelectorGates n counterWidth bit ++
  coeffWorkCompareSelectedOddDataPathGates n counterWidth

/-- Base-gate program for the comparison selector followed by the selected odd
data path. -/
def coeffWorkCompareSelectorThenSelectedOddDataPathProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectorThenSelectedOddDataPathGates n counterWidth bit)

/-- The explicit comparison-selector/selected-odd gate list has the existing
composite semantic action. -/
theorem coeffWorkCompareSelectorThenSelectedOddDataPathStep_eq_gateList
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkCompareSelectorThenSelectedOddDataPathGates
          n counterWidth bit) x =
      coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit x := by
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathGates]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_eq_gateList]
  rw [coeffWorkCompareSelectedOddDataPathStep_eq_gateList]
  rfl

/-- The comparison-selector/selected-odd program realizes the existing composite
semantic action. -/
theorem coeffWorkCompareSelectorThenSelectedOddDataPath_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareSelectorThenSelectedOddDataPathProgram n counterWidth bit)
      (coeffWorkCompareSelectorThenSelectedOddDataPathStep
        n counterWidth bit) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectorThenSelectedOddDataPathGates n counterWidth bit)
    (coeffWorkCompareSelectorThenSelectedOddDataPathStep_eq_gateList
      n counterWidth bit)

/-- Exact physical length of comparison selection followed by its odd data
path. -/
theorem coeffWorkCompareSelectorThenSelectedOddDataPathGates_length
    (n counterWidth : Nat) (bit : Fin n) :
    (coeffWorkCompareSelectorThenSelectedOddDataPathGates
      n counterWidth bit).length = 36 * (n - 1) + 54 * n + 9 := by
  simp only [coeffWorkCompareSelectorThenSelectedOddDataPathGates,
    List.length_append,
    coeffWorkUGreaterScratchACompareSelectorGates_length,
    coeffWorkCompareSelectedOddDataPathGates_length]
  omega

/-- Exact X coordinate of comparison selection followed by its odd data
path. -/
theorem
    coeffWorkCompareSelectorThenSelectedOddDataPathGates_xMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((coeffWorkCompareSelectorThenSelectedOddDataPathGates
      n counterWidth bit).map EncodedBit.GateSpec.xMultiplicity).sum =
      4 * n + 4 := by
  simp only [coeffWorkCompareSelectorThenSelectedOddDataPathGates,
    List.map_append, List.sum_append,
    coeffWorkUGreaterScratchACompareSelectorGates_xMultiplicity_sum,
    coeffWorkCompareSelectedOddDataPathGates_xMultiplicity_sum]

/-- Exact CNOT coordinate of comparison selection followed by its odd data
path. -/
theorem
    coeffWorkCompareSelectorThenSelectedOddDataPathGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((coeffWorkCompareSelectorThenSelectedOddDataPathGates
      n counterWidth bit).map EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp only [coeffWorkCompareSelectorThenSelectedOddDataPathGates,
    List.map_append, List.sum_append,
    coeffWorkUGreaterScratchACompareSelectorGates_cnotMultiplicity_sum,
    coeffWorkCompareSelectedOddDataPathGates_cnotMultiplicity_sum,
    Nat.add_zero]

/-- Exact Toffoli coordinate of comparison selection followed by its odd data
path. -/
theorem
    coeffWorkCompareSelectorThenSelectedOddDataPathGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((coeffWorkCompareSelectorThenSelectedOddDataPathGates
      n counterWidth bit).map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      50 * n + 36 * (n - 1) + 4 := by
  simp only [coeffWorkCompareSelectorThenSelectedOddDataPathGates,
    List.map_append, List.sum_append,
    coeffWorkUGreaterScratchACompareSelectorGates_toffoliMultiplicity_sum,
    coeffWorkCompareSelectedOddDataPathGates_toffoliMultiplicity_sum]
  omega

/-- On clean comparison inputs, if `v < u`, the composed selector and selected
odd data path reduces to the `u := u - v; r := r + s` path after selector
staging. -/
theorem
    coeffWorkCompareSelectorSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_clean_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work) =
      coeffWorkSubVFromUThenAddSIntoRStep n counterWidth
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
          ((x, cleanComparisonWork n), work)) := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_compare_clean
      n counterWidth bit x work hscratchA hcompare hfinal]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
  have hltY : y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change coeffWorkCompareSelectedOddDataPathStep n counterWidth y =
    coeffWorkSubVFromUThenAddSIntoRStep n counterWidth y
  exact
    coeffWorkCompareSelectedOddDataPathStep_eq_subVFromUThenAddSIntoR_of_compare_valid_lt
      n counterWidth y hcompareValid hltY hcontrolWorkY hsourceCarryY

/-- On clean comparison inputs, if `v < u` is false, the composed selector and
selected odd data path reduces to the `v := v - u; s := s + r` path after
selector staging. -/
theorem
    coeffWorkCompareSelectorSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_clean_not_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work) =
      coeffWorkSubUFromVThenAddRIntoSStep n counterWidth
        (coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
          ((x, cleanComparisonWork n), work)) := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_compare_clean
      n counterWidth bit x work hscratchA hcompare hfinal]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
  have hnltY : ¬ y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hnlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change coeffWorkCompareSelectedOddDataPathStep n counterWidth y =
    coeffWorkSubUFromVThenAddRIntoSStep n counterWidth y
  exact
    coeffWorkCompareSelectedOddDataPathStep_eq_subUFromVThenAddRIntoS_of_compare_valid_not_lt
      n counterWidth y hcompareValid hnltY hcontrolWorkY hsourceCarryY

/-- On clean comparison inputs with `v < u`, the composed selector and selected
odd data path writes `u := u - v`. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_u_sub_clean_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work)).1.1.u =
      x.u - x.v := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    exact coeffWorkUGreaterScratchACompareSelectorStep_compare_valid_clean
      n counterWidth bit x work hscratchA hcompare hfinal
  have hltY : y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  have hsourceWorkY :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get y =
          false := by
    intro k
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_comparisonCarryPrefix]
    exact hsourceWork k
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change (coeffWorkCompareSelectedOddDataPathStep n counterWidth y).1.1.u =
    x.u - x.v
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_u_sub_of_compare_valid_lt_clean
      n counterWidth y hcompareValid hltY hcontrolWorkY hsourceCarryY
      hsourceWorkY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]

/-- On clean comparison inputs with `v < u`, the composed selector and selected
odd data path writes `r := r + s`. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_rCoeff_add_clean_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work)).1.1.rCoeff =
      x.rCoeff + x.sCoeff := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    exact coeffWorkUGreaterScratchACompareSelectorStep_compare_valid_clean
      n counterWidth bit x work hscratchA hcompare hfinal
  have hltY : y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  have hcoeffWorkY :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get y =
          false := by
    intro k
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryWorkBit]
    exact hcoeffWork k
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change
      (coeffWorkCompareSelectedOddDataPathStep n counterWidth y).1.1.rCoeff =
    x.rCoeff + x.sCoeff
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_rCoeff_add_of_compare_valid_lt_clean
      n counterWidth y hcompareValid hltY hcontrolWorkY hsourceCarryY
      hcoeffWorkY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_rCoeff]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_sCoeff]

/-- On clean comparison inputs with `v < u`, the composed selector and selected
odd data path preserves the untouched `v` source word. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_v_clean_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work)).1.1.v =
      x.v := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    exact coeffWorkUGreaterScratchACompareSelectorStep_compare_valid_clean
      n counterWidth bit x work hscratchA hcompare hfinal
  have hltY : y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change (coeffWorkCompareSelectedOddDataPathStep n counterWidth y).1.1.v =
    x.v
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_v_of_compare_valid_lt_clean
      n counterWidth y hcompareValid hltY hcontrolWorkY hsourceCarryY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]

/-- On clean comparison inputs with `v < u`, the composed selector and selected
odd data path preserves the untouched `s` coefficient word. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_sCoeff_clean_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work)).1.1.sCoeff =
      x.sCoeff := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    exact coeffWorkUGreaterScratchACompareSelectorStep_compare_valid_clean
      n counterWidth bit x work hscratchA hcompare hfinal
  have hltY : y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change
      (coeffWorkCompareSelectedOddDataPathStep n counterWidth y).1.1.sCoeff =
    x.sCoeff
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_sCoeff_of_compare_valid_lt_clean
      n counterWidth y hcompareValid hltY hcontrolWorkY hsourceCarryY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_sCoeff]

/-- On clean comparison inputs with `v < u` false, the composed selector and
selected odd data path writes `v := v - u`. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_v_sub_clean_not_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work)).1.1.v =
      x.v - x.u := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    exact coeffWorkUGreaterScratchACompareSelectorStep_compare_valid_clean
      n counterWidth bit x work hscratchA hcompare hfinal
  have hnltY : ¬ y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hnlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  have hsourceWorkY :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get y =
          false := by
    intro k
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_comparisonCarryPrefix]
    exact hsourceWork k
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change (coeffWorkCompareSelectedOddDataPathStep n counterWidth y).1.1.v =
    x.v - x.u
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_v_sub_of_compare_valid_not_lt_clean
      n counterWidth y hcompareValid hnltY hcontrolWorkY hsourceCarryY
      hsourceWorkY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]

/-- On clean comparison inputs with `v < u` false, the composed selector and
selected odd data path writes `s := s + r`. -/
theorem
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_sCoeff_add_clean_not_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work)).1.1.sCoeff =
      x.sCoeff + x.rCoeff := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    exact coeffWorkUGreaterScratchACompareSelectorStep_compare_valid_clean
      n counterWidth bit x work hscratchA hcompare hfinal
  have hnltY : ¬ y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hnlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  have hcoeffWorkY :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get y =
          false := by
    intro k
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryWorkBit]
    exact hcoeffWork k
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change
      (coeffWorkCompareSelectedOddDataPathStep n counterWidth y).1.1.sCoeff =
    x.sCoeff + x.rCoeff
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_sCoeff_add_of_compare_valid_not_lt_clean
      n counterWidth y hcompareValid hnltY hcontrolWorkY hsourceCarryY
      hcoeffWorkY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_sCoeff]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_rCoeff]

/-- On clean comparison inputs with `v < u` false, the composed selector and
selected odd data path preserves the untouched `u` source word. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_u_clean_not_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work)).1.1.u =
      x.u := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    exact coeffWorkUGreaterScratchACompareSelectorStep_compare_valid_clean
      n counterWidth bit x work hscratchA hcompare hfinal
  have hnltY : ¬ y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hnlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change (coeffWorkCompareSelectedOddDataPathStep n counterWidth y).1.1.u =
    x.u
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_u_of_compare_valid_not_lt_clean
      n counterWidth y hcompareValid hnltY hcontrolWorkY hsourceCarryY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]

/-- On clean comparison inputs with `v < u` false, the composed selector and
selected odd data path preserves the untouched `r` coefficient word. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_rCoeff_clean_not_lt
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth bit
        ((x, cleanComparisonWork n), work)).1.1.rCoeff =
      x.rCoeff := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcompareValid :
      (coeffAdderCompareBit n counterWidth).get y =
        decide (y.1.1.v.val < y.1.1.u.val) := by
    dsimp [y]
    exact coeffWorkUGreaterScratchACompareSelectorStep_compare_valid_clean
      n counterWidth bit x work hscratchA hcompare hfinal
  have hnltY : ¬ y.1.1.v.val < y.1.1.u.val := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
    exact hnlt
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change
      (coeffWorkCompareSelectedOddDataPathStep n counterWidth y).1.1.rCoeff =
    x.rCoeff
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_rCoeff_of_compare_valid_not_lt_clean
      n counterWidth y hcompareValid hnltY hcontrolWorkY hsourceCarryY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_rCoeff]

/-- The composed comparison selector and selected odd data path preserves the
active flag on clean selected-control inputs. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth
          bit ((x, cleanComparisonWork n), work)) =
      (RegisterBits.activeBit n counterWidth).get x := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change
      (coeffAdderActiveBit n counterWidth).get
          (coeffWorkCompareSelectedOddDataPathStep n counterWidth y) =
        (RegisterBits.activeBit n counterWidth).get x
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_active
      n counterWidth y hcontrolWorkY hsourceCarryY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_active]
  rfl

/-- On clean comparison inputs, the composed comparison selector and selected
odd data path leaves the compare bit equal to the selector's original
`v < u` predicate.  This is not a compare-valid statement for the mutated
output source registers. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth
          bit ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change
      (coeffAdderCompareBit n counterWidth).get
          (coeffWorkCompareSelectedOddDataPathStep n counterWidth y) =
        decide (x.v.val < x.u.val)
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_compare
      n counterWidth y hcontrolWorkY hsourceCarryY]
  dsimp [y]
  rw [
    coeffWorkUGreaterScratchACompareSelectorStep_get_compare_clean
      n counterWidth bit x work hscratchA hcompare hfinal]

/-- The composed comparison selector and selected odd data path preserves every
stored branch-history bit on clean selected-control inputs. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_historyBit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth
          bit ((x, cleanComparisonWork n), work)) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change
      (coeffAdderHistoryBit n counterWidth historyIndex).get
          (coeffWorkCompareSelectedOddDataPathStep n counterWidth y) =
        (RegisterBits.historyBit n counterWidth historyIndex).get x
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_historyBit
      n counterWidth historyIndex y hcontrolWorkY hsourceCarryY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_historyBit]
  rfl

/-- On clean selected-control inputs, the composed comparison selector and
selected odd data path restores scratchA. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth
          bit ((x, cleanComparisonWork n), work)) =
      false := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_scratchA_clean
      n counterWidth y hcontrolWorkY hsourceCarryY

/-- On clean selected-control inputs, the composed comparison selector and
selected odd data path preserves scratchB. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchB
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth
          bit ((x, cleanComparisonWork n), work)) =
      (RegisterBits.scratchBBit n counterWidth).get x := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  change
      (coeffAdderScratchBBit n counterWidth).get
          (coeffWorkCompareSelectedOddDataPathStep n counterWidth y) =
        (RegisterBits.scratchBBit n counterWidth).get x
  rw [
    coeffWorkCompareSelectedOddDataPathStep_get_scratchB
      n counterWidth y hcontrolWorkY hsourceCarryY]
  dsimp [y]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchB]
  rfl

/-- On clean selected-control inputs and clean source-subtract work, the
composed comparison selector and selected odd data path restores each
comparison-prefix carry bit. -/
theorem
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin n) (workBit : Fin (n - 1))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false)
    (hsourceWork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit workBit).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth
          bit ((x, cleanComparisonWork n), work)) =
      false := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  have hsourceWorkY :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get y =
          false := by
    intro k
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_comparisonCarryPrefix]
    exact hsourceWork k
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_comparisonCarryPrefix_clean
      n counterWidth workBit y hcontrolWorkY hsourceCarryY hsourceWorkY

/-- On clean comparison input, the composed comparison selector and selected
odd data path also restores the dedicated final comparison-carry bit. -/
theorem
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_comparisonCarry_final_clean
    (n counterWidth : Nat) (finalBit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hfinal : finalBit.val + 1 = n)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffAdderComparisonCarryBit n counterWidth finalBit).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth
          finalBit ((x, cleanComparisonWork n), work)) =
      false := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth finalBit
      ((x, cleanComparisonWork n), work)
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  have hfinalCleanY :
      (coeffAdderComparisonCarryBit n counterWidth finalBit).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_comparisonCarry]
    change
      (comparisonCarryValueBit n finalBit).get
          (cleanComparisonWork n) = false
    exact comparisonCarryValueBit_clean n finalBit
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_finalComparisonCarry_clean
      n counterWidth finalBit y hcontrolWorkY hsourceCarryY hfinal
      hfinalCleanY

/-- On clean selected-control inputs, the composed comparison selector and
selected odd data path restores the dedicated coefficient-adder carry-in bit. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_coeffCarryIn_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth
          bit ((x, cleanComparisonWork n), work)) =
      false := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_coeffCarryIn_clean
      n counterWidth y hcontrolWorkY hsourceCarryY

/-- On clean selected-control inputs and clean coefficient-adder work, the
composed comparison selector and selected odd data path restores every
dedicated coefficient-adder carry-work bit. -/
theorem coeffWorkCompareSelectorSelectedOddDataPathStep_get_carryWork_clean
    (n counterWidth : Nat) (bit : Fin n)
    (workBit : Fin ((n + 1) - 1))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit n counterWidth).get
          ((x, cleanComparisonWork n), work) = false)
    (hcoeffWork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep n counterWidth
          bit ((x, cleanComparisonWork n), work)) =
      false := by
  let y :=
    coeffWorkUGreaterScratchACompareSelectorStep n counterWidth bit
      ((x, cleanComparisonWork n), work)
  have hcontrolWorkY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  have hsourceCarryY :
      (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    change x.scratchA = false
    exact hscratchA
  have hcoeffWorkY :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get y =
          false := by
    intro k
    dsimp [y]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryWorkBit]
    exact hcoeffWork k
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  exact
    coeffWorkCompareSelectedOddDataPathStep_get_carryWork_clean
      n counterWidth workBit y hcontrolWorkY hsourceCarryY hcoeffWorkY

/-- In the odd-odd case, the branch decision latched from the selector output
has auxiliary code bit equal to the compare bit preserved by the selected odd
data-path prefix.  The branch is read before `u` or `v` is mutated. -/
theorem
    coeffWorkCompareSelectorSelectedOddDataPathStep_latchedOddBranch_auxBit_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (Branch.fromCoeffWorkSignals tail.succ counterWidth
        (coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth
          bit ((x, cleanComparisonWork tail.succ), work))).auxBit =
      (coeffAdderCompareBit tail.succ counterWidth).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep
          tail.succ counterWidth bit
          ((x, cleanComparisonWork tail.succ), work)) := by
  have hcompareOut :
      (coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth
          bit ((x, cleanComparisonWork tail.succ), work)).1.1.compare =
        decide (x.v.val < x.u.val) := by
    simpa [coeffAdderCompareBit_get] using
      coeffWorkUGreaterScratchACompareSelectorStep_get_compare_clean
        tail.succ counterWidth bit x work hscratchA hcompare hfinal
  rw [
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth bit x work hscratchA hcompare hfinal
      hcontrolWork]
  rw [Branch.fromCoeffWorkSignals]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
  rw [hcompareOut]
  by_cases hlt : x.v.val < x.u.val
  · simp [Branch.fromCircuitSignals, Branch.auxBit, huOdd, hvOdd, hlt]
  · simp [Branch.fromCircuitSignals, Branch.auxBit, huOdd, hvOdd, hlt]

/-- In the odd-odd case, the branch decision latched from the selector output
has history code bit equal to the compare bit preserved by the selected odd
data-path prefix.  The branch is read before `u` or `v` is mutated. -/
theorem
    coeffWorkCompareSelectorSelectedOddDataPathStep_latchedOddBranch_historyBit_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (Branch.fromCoeffWorkSignals tail.succ counterWidth
        (coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth
          bit ((x, cleanComparisonWork tail.succ), work))).historyBit =
      (coeffAdderCompareBit tail.succ counterWidth).get
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep
          tail.succ counterWidth bit
          ((x, cleanComparisonWork tail.succ), work)) := by
  have hcompareOut :
      (coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth
          bit ((x, cleanComparisonWork tail.succ), work)).1.1.compare =
        decide (x.v.val < x.u.val) := by
    simpa [coeffAdderCompareBit_get] using
      coeffWorkUGreaterScratchACompareSelectorStep_get_compare_clean
        tail.succ counterWidth bit x work hscratchA hcompare hfinal
  rw [
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth bit x work hscratchA hcompare hfinal
      hcontrolWork]
  rw [Branch.fromCoeffWorkSignals]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_u]
  rw [coeffWorkUGreaterScratchACompareSelectorStep_get_v]
  rw [hcompareOut]
  by_cases hlt : x.v.val < x.u.val
  · simp [Branch.fromCircuitSignals, Branch.historyBit, huOdd, hvOdd, hlt]
  · simp [Branch.fromCircuitSignals, Branch.historyBit, huOdd, hvOdd, hlt]

/-- In the odd-odd case, the branch code latched from the selector output is
the pair of compare bits preserved by the selected odd data-path prefix.  This
is a carried-code statement; it does not recompute branch signals after the
data path mutates `u` or `v`. -/
theorem
    coeffWorkCompareSelectorSelectedOddDataPathStep_latchedOddBranch_code_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    Branch.code
        (Branch.fromCoeffWorkSignals tail.succ counterWidth
          (coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth
            bit ((x, cleanComparisonWork tail.succ), work))) =
      ((coeffAdderCompareBit tail.succ counterWidth).get
          (coeffWorkCompareSelectorThenSelectedOddDataPathStep
            tail.succ counterWidth bit
            ((x, cleanComparisonWork tail.succ), work)),
       (coeffAdderCompareBit tail.succ counterWidth).get
          (coeffWorkCompareSelectorThenSelectedOddDataPathStep
            tail.succ counterWidth bit
            ((x, cleanComparisonWork tail.succ), work))) := by
  rw [Branch.code]
  rw [
    coeffWorkCompareSelectorSelectedOddDataPathStep_latchedOddBranch_auxBit_clean
      tail counterWidth bit x work hscratchA hcompare hfinal huOdd hvOdd
      hcontrolWork]
  rw [
    coeffWorkCompareSelectorSelectedOddDataPathStep_latchedOddBranch_historyBit_clean
      tail counterWidth bit x work hscratchA hcompare hfinal huOdd hvOdd
      hcontrolWork]

/-! ## Coefficient-work-lifted odd branch-history selectors -/

/-- Coefficient-work-lifted `uGreater` selector/history-write slice.  This keeps
the concrete odd-branch history selector in the same workspace as the
coefficient-add data path without yet composing a full Kaliski round. -/
def coeffWorkUGreaterSelectorBranchHistoryWriteStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit historyIndex)

/-- Circuit for the coefficient-work-lifted `uGreater` selector/history write. -/
def coeffWorkUGreaterSelectorBranchHistoryWriteProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (uGreaterSelectorBranchHistoryWriteProgram n counterWidth bit historyIndex)

/-- The coefficient-work-lifted `uGreater` circuit realizes its step. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWrite_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterSelectorBranchHistoryWriteProgram n counterWidth bit
        historyIndex)
      (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex) :=
  liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (uGreaterSelectorBranchHistoryWrite_realizes n counterWidth bit
      historyIndex)

/-- Coefficient-work-lifted `vLe` selector/history-write slice.  Its history
endpoint remains the zero-code no-op branch-history write from the lifted
comparison-work slice. -/
def coeffWorkVLeSelectorBranchHistoryWriteStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex)

/-- Circuit for the coefficient-work-lifted `vLe` selector/history write. -/
def coeffWorkVLeSelectorBranchHistoryWriteProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (vLeSelectorBranchHistoryWriteProgram n counterWidth bit historyIndex)

/-- The coefficient-work-lifted `vLe` circuit realizes its step. -/
theorem coeffWorkVLeSelectorBranchHistoryWrite_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVLeSelectorBranchHistoryWriteProgram n counterWidth bit
        historyIndex)
      (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex) :=
  liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (vLeSelectorBranchHistoryWrite_realizes n counterWidth bit historyIndex)

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves the
dedicated coefficient-adder work object. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_coeffAdderWork
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex x).2 = x.2 := by
  rfl

/-- The coefficient-work-lifted `vLe` selector/history slice preserves the
dedicated coefficient-adder work object. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_coeffAdderWork
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex x).2 = x.2 := by
  rfl

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_carryIn
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- The coefficient-work-lifted `vLe` selector/history slice preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_carryIn
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_carryWorkBit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- The coefficient-work-lifted `vLe` selector/history slice preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_carryWorkBit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
the active flag. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  change (liftedActiveBit n counterWidth).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x.1) =
      (liftedActiveBit n counterWidth).get x.1
  exact uGreaterSelectorBranchHistoryWriteStep_get_active
    n counterWidth bit historyIndex x.1

/-- The coefficient-work-lifted `vLe` selector/history slice preserves the
active flag. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  change (liftedActiveBit n counterWidth).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex
          x.1) =
      (liftedActiveBit n counterWidth).get x.1
  exact vLeSelectorBranchHistoryWriteStep_get_active
    n counterWidth bit historyIndex x.1

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
scratchA. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  change (liftedScratchABit n counterWidth).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x.1) =
      (liftedScratchABit n counterWidth).get x.1
  exact uGreaterSelectorBranchHistoryWriteStep_get_scratchA
    n counterWidth bit historyIndex x.1

/-- The coefficient-work-lifted `vLe` selector/history slice preserves
scratchA. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  change (liftedScratchABit n counterWidth).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex
          x.1) =
      (liftedScratchABit n counterWidth).get x.1
  exact vLeSelectorBranchHistoryWriteStep_get_scratchA
    n counterWidth bit historyIndex x.1

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
each comparison-work carry bit. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  change (liftedComparisonCarryBit n counterWidth workBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x.1) =
      (liftedComparisonCarryBit n counterWidth workBit).get x.1
  exact uGreaterSelectorBranchHistoryWriteStep_get_comparisonCarry
    n counterWidth bit historyIndex workBit x.1

/-- The coefficient-work-lifted `vLe` selector/history slice preserves each
comparison-work carry bit. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  change (liftedComparisonCarryBit n counterWidth workBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex
          x.1) =
      (liftedComparisonCarryBit n counterWidth workBit).get x.1
  exact vLeSelectorBranchHistoryWriteStep_get_comparisonCarry
    n counterWidth bit historyIndex workBit x.1

/-- On clean comparison inputs, the coefficient-work-lifted `uGreater`
selector/history slice leaves compare equal to the staged predicate `v < u`. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  change (liftedCompareBit n counterWidth).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val)
  exact uGreaterSelectorBranchHistoryWriteStep_get_compare_clean
    n counterWidth bit historyIndex x hscratchA hcompare hfinal

/-- On clean comparison inputs, the coefficient-work-lifted `vLe`
selector/history slice preserves the same staged predicate bit `v < u`; the
history endpoint accounts for the zero-code branch bit. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  change (liftedCompareBit n counterWidth).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex
          (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val)
  exact vLeSelectorBranchHistoryWriteStep_get_compare_clean
    n counterWidth bit historyIndex x hscratchA hcompare hfinal

/-- On clean inputs, the coefficient-work-lifted `uGreater` selector/history
slice toggles the selected history bit exactly under active `v < u`. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex ((x, cleanComparisonWork n), work)) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val))) := by
  change (liftedHistoryBit n counterWidth historyIndex).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex (x, cleanComparisonWork n)) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val)))
  exact uGreaterSelectorBranchHistoryWriteStep_get_history_clean
    n counterWidth bit historyIndex x hscratchA hcompare hscratchB hfinal

/-- On clean scratchB, the coefficient-work-lifted `vLe` selector/history slice
leaves the selected history bit unchanged. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  change (liftedHistoryBit n counterWidth historyIndex).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit historyIndex
          x.1) =
      (liftedHistoryBit n counterWidth historyIndex).get x.1
  apply vLeSelectorBranchHistoryWriteStep_get_history_clean
  change (liftedScratchBBit n counterWidth).get x.1 = false at hscratchB
  exact hscratchB

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
every history slot except the selected target slot. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  change (liftedHistoryBit n counterWidth observed).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth bit target
          x.1) =
      (liftedHistoryBit n counterWidth observed).get x.1
  exact uGreaterSelectorBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth bit target observed hne x.1

/-- The coefficient-work-lifted `vLe` selector/history slice preserves every
history slot except the selected target slot. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
          target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  change (liftedHistoryBit n counterWidth observed).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth bit target x.1) =
      (liftedHistoryBit n counterWidth observed).get x.1
  exact vLeSelectorBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth bit target observed hne x.1

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
each little-endian `u` value bit. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_uWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit targetBit).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth
          selectorBit historyIndex x) =
      ((coeffAdderUWord n counterWidth).bit targetBit).get x := by
  change ((liftedUWord n counterWidth).bit targetBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x.1) =
      ((liftedUWord n counterWidth).bit targetBit).get x.1
  exact uGreaterSelectorBranchHistoryWriteStep_get_uWordBit
    n counterWidth selectorBit targetBit historyIndex x.1

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
each little-endian `v` value bit. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_vWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit targetBit).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth
          selectorBit historyIndex x) =
      ((coeffAdderVWord n counterWidth).bit targetBit).get x := by
  change ((liftedVWord n counterWidth).bit targetBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x.1) =
      ((liftedVWord n counterWidth).bit targetBit).get x.1
  exact uGreaterSelectorBranchHistoryWriteStep_get_vWordBit
    n counterWidth selectorBit targetBit historyIndex x.1

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
each little-endian `s` coefficient value bit. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth
          selectorBit historyIndex x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x.1) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact uGreaterSelectorBranchHistoryWriteStep_get_sCoeffValueWordBit
    n counterWidth selectorBit targetBit historyIndex x.1

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
each little-endian `r` coefficient value bit. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth
          selectorBit historyIndex x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (uGreaterSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x.1) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact uGreaterSelectorBranchHistoryWriteStep_get_rCoeffValueWordBit
    n counterWidth selectorBit targetBit historyIndex x.1

/-- The coefficient-work-lifted `vLe` selector/history slice preserves each
little-endian `u` value bit. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_uWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit targetBit).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((coeffAdderUWord n counterWidth).bit targetBit).get x := by
  change ((liftedUWord n counterWidth).bit targetBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x.1) =
      ((liftedUWord n counterWidth).bit targetBit).get x.1
  exact vLeSelectorBranchHistoryWriteStep_get_uWordBit
    n counterWidth selectorBit targetBit historyIndex x.1

/-- The coefficient-work-lifted `vLe` selector/history slice preserves each
little-endian `v` value bit. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_vWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit targetBit).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((coeffAdderVWord n counterWidth).bit targetBit).get x := by
  change ((liftedVWord n counterWidth).bit targetBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x.1) =
      ((liftedVWord n counterWidth).bit targetBit).get x.1
  exact vLeSelectorBranchHistoryWriteStep_get_vWordBit
    n counterWidth selectorBit targetBit historyIndex x.1

/-- The coefficient-work-lifted `vLe` selector/history slice preserves each
little-endian `s` coefficient value bit. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x.1) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact vLeSelectorBranchHistoryWriteStep_get_sCoeffValueWordBit
    n counterWidth selectorBit targetBit historyIndex x.1

/-- The coefficient-work-lifted `vLe` selector/history slice preserves each
little-endian `r` coefficient value bit. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (vLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
          historyIndex x.1) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact vLeSelectorBranchHistoryWriteStep_get_rCoeffValueWordBit
    n counterWidth selectorBit targetBit historyIndex x.1

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
the `u` source word. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_u
    (n counterWidth : Nat) (selectorBit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth
        selectorBit historyIndex x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_uWordBit
    n counterWidth selectorBit bit historyIndex x
  simpa [coeffAdderUWord_get_testBit] using h

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
the `v` source word. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_v
    (n counterWidth : Nat) (selectorBit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth
        selectorBit historyIndex x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_vWordBit
    n counterWidth selectorBit bit historyIndex x
  simpa [coeffAdderVWord_get_testBit] using h

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
the `s` coefficient word. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_sCoeff
    (n counterWidth : Nat) (selectorBit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth
        selectorBit historyIndex x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_sCoeffValueWordBit
      n counterWidth selectorBit bit historyIndex x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- The coefficient-work-lifted `uGreater` selector/history slice preserves
the `r` coefficient word. -/
theorem coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_rCoeff
    (n counterWidth : Nat) (selectorBit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth
        selectorBit historyIndex x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_rCoeffValueWordBit
      n counterWidth selectorBit bit historyIndex x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- The coefficient-work-lifted `vLe` selector/history slice preserves the `u`
source word. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_u
    (n counterWidth : Nat) (selectorBit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
        historyIndex x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVLeSelectorBranchHistoryWriteStep_get_uWordBit
    n counterWidth selectorBit bit historyIndex x
  simpa [coeffAdderUWord_get_testBit] using h

/-- The coefficient-work-lifted `vLe` selector/history slice preserves the `v`
source word. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_v
    (n counterWidth : Nat) (selectorBit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
        historyIndex x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVLeSelectorBranchHistoryWriteStep_get_vWordBit
    n counterWidth selectorBit bit historyIndex x
  simpa [coeffAdderVWord_get_testBit] using h

/-- The coefficient-work-lifted `vLe` selector/history slice preserves the `s`
coefficient word. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_sCoeff
    (n counterWidth : Nat) (selectorBit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
        historyIndex x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    coeffWorkVLeSelectorBranchHistoryWriteStep_get_sCoeffValueWordBit
      n counterWidth selectorBit bit historyIndex x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- The coefficient-work-lifted `vLe` selector/history slice preserves the `r`
coefficient word. -/
theorem coeffWorkVLeSelectorBranchHistoryWriteStep_get_rCoeff
    (n counterWidth : Nat) (selectorBit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth selectorBit
        historyIndex x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h :=
    coeffWorkVLeSelectorBranchHistoryWriteStep_get_rCoeffValueWordBit
      n counterWidth selectorBit bit historyIndex x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-! ## Coefficient-work-lifted odd branch data-path slices -/

/-- Sequence the coefficient-work-lifted `uGreater` selector/history slice with
the swap-selected `r`-into-`s` coefficient adder.  This is a concrete
selector-plus-data-path slice for the odd Montgomery--Kaliski branch, not yet a
complete inversion round [RNSL17, ECDLP.tex:399-421,468-475; VBE95,
9511018.tex:237-264,591-618]. -/
def coeffWorkUGreaterSelectorThenAddRIntoSStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkSwapsThenAddRIntoSStep n counterWidth
      (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex x)

/-- Circuit for the `uGreater` selector plus `r`-into-`s` data path. -/
def coeffWorkUGreaterSelectorThenAddRIntoSProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUGreaterSelectorBranchHistoryWriteProgram n counterWidth bit
      historyIndex)
    (coeffWorkSwapsThenAddRIntoSProgram n counterWidth)

/-- The `uGreater` selector plus `r`-into-`s` circuit realizes its step. -/
theorem coeffWorkUGreaterSelectorThenAddRIntoS_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterSelectorThenAddRIntoSProgram n counterWidth bit
        historyIndex)
      (coeffWorkUGreaterSelectorThenAddRIntoSStep n counterWidth bit
        historyIndex) := by
  unfold coeffWorkUGreaterSelectorThenAddRIntoSProgram
    coeffWorkUGreaterSelectorThenAddRIntoSStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex)
    (secondStep := coeffWorkSwapsThenAddRIntoSStep n counterWidth)
    (coeffWorkUGreaterSelectorBranchHistoryWrite_realizes n counterWidth bit
      historyIndex)
    (coeffWorkSwapsThenAddRIntoS_realizes n counterWidth)

/-- On clean comparison inputs, the `uGreater` selector-plus-data-path slice
keeps the staged comparison predicate available after the coefficient-adder
data path. -/
theorem coeffWorkUGreaterSelectorThenAddRIntoSStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUGreaterSelectorThenAddRIntoSStep n counterWidth bit
          historyIndex ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkUGreaterSelectorThenAddRIntoSStep]
  rw [coeffWorkSwapsThenAddRIntoSStep_get_compare]
  exact coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_compare_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- On clean inputs, the `uGreater` selector-plus-data-path slice preserves the
selector's branch-history toggle through the coefficient-adder data path. -/
theorem coeffWorkUGreaterSelectorThenAddRIntoSStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUGreaterSelectorThenAddRIntoSStep n counterWidth bit
          historyIndex ((x, cleanComparisonWork n), work)) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val))) := by
  rw [coeffWorkUGreaterSelectorThenAddRIntoSStep]
  rw [coeffWorkSwapsThenAddRIntoSStep_get_historyBit]
  exact coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_history_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hscratchB hfinal

/-- The `uGreater` selector-plus-data-path slice preserves the active flag. -/
theorem coeffWorkUGreaterSelectorThenAddRIntoSStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUGreaterSelectorThenAddRIntoSStep n counterWidth bit
          historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkUGreaterSelectorThenAddRIntoSStep]
  rw [coeffWorkSwapsThenAddRIntoSStep_get_active]
  exact coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_active
    n counterWidth bit historyIndex x

/-- The `uGreater` selector-plus-data-path slice preserves scratchA. -/
theorem coeffWorkUGreaterSelectorThenAddRIntoSStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUGreaterSelectorThenAddRIntoSStep n counterWidth bit
          historyIndex x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  rw [coeffWorkUGreaterSelectorThenAddRIntoSStep]
  rw [coeffWorkSwapsThenAddRIntoSStep_get_scratchA]
  exact coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_scratchA
    n counterWidth bit historyIndex x

/-- Sequence the coefficient-work-lifted `vLe` selector/history slice with the
swap-selected `s`-into-`r` coefficient adder.  This is the symmetric odd-branch
selector-plus-data-path slice, still short of a complete inversion round
[RNSL17, ECDLP.tex:399-421,468-475; VBE95, 9511018.tex:237-264,591-618]. -/
def coeffWorkVLeSelectorThenAddSIntoRStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkSwapsThenAddSIntoRStep n counterWidth
      (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex x)

/-- Circuit for the `vLe` selector plus `s`-into-`r` data path. -/
def coeffWorkVLeSelectorThenAddSIntoRProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVLeSelectorBranchHistoryWriteProgram n counterWidth bit
      historyIndex)
    (coeffWorkSwapsThenAddSIntoRProgram n counterWidth)

/-- The `vLe` selector plus `s`-into-`r` circuit realizes its step. -/
theorem coeffWorkVLeSelectorThenAddSIntoR_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVLeSelectorThenAddSIntoRProgram n counterWidth bit historyIndex)
      (coeffWorkVLeSelectorThenAddSIntoRStep n counterWidth bit
        historyIndex) := by
  unfold coeffWorkVLeSelectorThenAddSIntoRProgram
    coeffWorkVLeSelectorThenAddSIntoRStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex)
    (secondStep := coeffWorkSwapsThenAddSIntoRStep n counterWidth)
    (coeffWorkVLeSelectorBranchHistoryWrite_realizes n counterWidth bit
      historyIndex)
    (coeffWorkSwapsThenAddSIntoR_realizes n counterWidth)

/-- On clean comparison inputs, the `vLe` selector-plus-data-path slice keeps
the staged comparison predicate available after the coefficient-adder data
path. -/
theorem coeffWorkVLeSelectorThenAddSIntoRStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVLeSelectorThenAddSIntoRStep n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkVLeSelectorThenAddSIntoRStep]
  rw [coeffWorkSwapsThenAddSIntoRStep_get_compare]
  exact coeffWorkVLeSelectorBranchHistoryWriteStep_get_compare_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- On clean scratchB, the `vLe` selector-plus-data-path slice preserves the
zero-code branch-history no-op through the coefficient-adder data path. -/
theorem coeffWorkVLeSelectorThenAddSIntoRStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVLeSelectorThenAddSIntoRStep n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  rw [coeffWorkVLeSelectorThenAddSIntoRStep]
  rw [coeffWorkSwapsThenAddSIntoRStep_get_historyBit]
  exact coeffWorkVLeSelectorBranchHistoryWriteStep_get_history_clean
    n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
    hscratchB

/-- The `vLe` selector-plus-data-path slice preserves the active flag. -/
theorem coeffWorkVLeSelectorThenAddSIntoRStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVLeSelectorThenAddSIntoRStep n counterWidth bit historyIndex
          x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkVLeSelectorThenAddSIntoRStep]
  rw [coeffWorkSwapsThenAddSIntoRStep_get_active]
  exact coeffWorkVLeSelectorBranchHistoryWriteStep_get_active
    n counterWidth bit historyIndex x

/-- The `vLe` selector-plus-data-path slice preserves scratchA. -/
theorem coeffWorkVLeSelectorThenAddSIntoRStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVLeSelectorThenAddSIntoRStep n counterWidth bit historyIndex
          x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  rw [coeffWorkVLeSelectorThenAddSIntoRStep]
  rw [coeffWorkSwapsThenAddSIntoRStep_get_scratchA]
  exact coeffWorkVLeSelectorBranchHistoryWriteStep_get_scratchA
    n counterWidth bit historyIndex x

/-- Sequence the `uGreater` selector/history slice with the concrete source
subtraction `u := u - v` and coefficient update `r := r + s`. -/
def coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkSubVFromUThenAddSIntoRStep n counterWidth
      (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex x)

/-- Circuit for the `uGreater` selector and subtract/add data path. -/
def coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUGreaterSelectorBranchHistoryWriteProgram n counterWidth bit
      historyIndex)
    (coeffWorkSubVFromUThenAddSIntoRProgram n counterWidth)

/-- The `uGreater` selector and subtract/add circuit realizes its step. -/
theorem coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoR_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRProgram
        n counterWidth bit historyIndex)
      (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRProgram
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex)
    (secondStep := coeffWorkSubVFromUThenAddSIntoRStep n counterWidth)
    (coeffWorkUGreaterSelectorBranchHistoryWrite_realizes n counterWidth bit
      historyIndex)
    (coeffWorkSubVFromUThenAddSIntoR_realizes n counterWidth)

/-- Sequence the `vLe` selector/history slice with the concrete source
subtraction `v := v - u` and coefficient update `s := s + r`. -/
def coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkSubUFromVThenAddRIntoSStep n counterWidth
      (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex x)

/-- Circuit for the `vLe` selector and subtract/add data path. -/
def coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVLeSelectorBranchHistoryWriteProgram n counterWidth bit
      historyIndex)
    (coeffWorkSubUFromVThenAddRIntoSProgram n counterWidth)

/-- The `vLe` selector and subtract/add circuit realizes its step. -/
theorem coeffWorkVLeSelectorThenSubUFromVThenAddRIntoS_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSProgram
        n counterWidth bit historyIndex)
      (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSProgram
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
        historyIndex)
    (secondStep := coeffWorkSubUFromVThenAddRIntoSStep n counterWidth)
    (coeffWorkVLeSelectorBranchHistoryWrite_realizes n counterWidth bit
      historyIndex)
    (coeffWorkSubUFromVThenAddRIntoS_realizes n counterWidth)

/-- The corrected `uGreater` selector-plus-subtract/add slice lands on clean
scratchA when the input scratchA is clean. -/
theorem coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
          n counterWidth bit historyIndex x) =
      false := by
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
  apply coeffWorkSubVFromUThenAddSIntoRStep_get_scratchA_clean
  rw [coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_scratchA]
  exact hcarry

/-- The corrected `vLe` selector-plus-subtract/add slice lands on clean
scratchA when the input scratchA is clean. -/
theorem coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
          n counterWidth bit historyIndex x) =
      false := by
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
  apply coeffWorkSubUFromVThenAddRIntoSStep_get_scratchA_clean
  rw [coeffWorkVLeSelectorBranchHistoryWriteStep_get_scratchA]
  exact hcarry

/-- The corrected `uGreater` selector-plus-subtract/add slice restores each
comparison-prefix carry-work bit when the input comparison-prefix work is clean. -/
theorem
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit workBit).get
        (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
          n counterWidth bit historyIndex x) =
      false := by
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
  apply coeffWorkSubVFromUThenAddSIntoRStep_get_comparisonCarryPrefix_clean
  intro k
  have hpres :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_comparisonCarry
      n counterWidth bit historyIndex
      (coeffAdderComparisonCarryPrefixIndex n k) x
  calc
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
        (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x := by
      simpa [coeffAdderComparisonCarryPrefixWord] using hpres
    _ = false := hwork k

/-- The corrected `vLe` selector-plus-subtract/add slice restores each
comparison-prefix carry-work bit when the input comparison-prefix work is clean. -/
theorem
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_comparisonCarryPrefix_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin (n - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit workBit).get
        (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
          n counterWidth bit historyIndex x) =
      false := by
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
  apply coeffWorkSubUFromVThenAddRIntoSStep_get_comparisonCarryPrefix_clean
  intro k
  have hpres :=
    coeffWorkVLeSelectorBranchHistoryWriteStep_get_comparisonCarry
      n counterWidth bit historyIndex
      (coeffAdderComparisonCarryPrefixIndex n k) x
  calc
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
        (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
          historyIndex x) =
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get x := by
      simpa [coeffAdderComparisonCarryPrefixWord] using hpres
    _ = false := hwork k

/-- The corrected `uGreater` selector-plus-subtract/add slice preserves the
active flag. -/
theorem coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
          n counterWidth bit historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
  rw [coeffWorkSubVFromUThenAddSIntoRStep_get_active]
  exact coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_active
    n counterWidth bit historyIndex x

/-- On clean comparison inputs, the corrected `uGreater`
selector-plus-subtract/add slice keeps the staged `v < u` predicate
available for branch-code staging. -/
theorem
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
  rw [coeffWorkSubVFromUThenAddSIntoRStep_get_compare]
  exact coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_compare_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- The corrected `vLe` selector-plus-subtract/add slice preserves the active
flag. -/
theorem coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
          n counterWidth bit historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
  rw [coeffWorkSubUFromVThenAddRIntoSStep_get_active]
  exact coeffWorkVLeSelectorBranchHistoryWriteStep_get_active
    n counterWidth bit historyIndex x

/-- On clean comparison inputs, the corrected `vLe`
selector-plus-subtract/add slice keeps the staged comparison predicate
available for branch-code staging. -/
theorem coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
  rw [coeffWorkSubUFromVThenAddRIntoSStep_get_compare]
  exact coeffWorkVLeSelectorBranchHistoryWriteStep_get_compare_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- On clean inputs, the corrected `uGreater` selector-plus-subtract/add slice
preserves the selector's branch-history toggle through the concrete
subtract/add data path. -/
theorem
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val))) := by
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
  rw [coeffWorkSubVFromUThenAddSIntoRStep_get_historyBit]
  exact coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_history_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hscratchB hfinal

/-- The corrected `uGreater` selector-plus-subtract/add slice preserves every
history slot except the selected target slot. -/
theorem
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
          n counterWidth bit target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
  rw [coeffWorkSubVFromUThenAddSIntoRStep_get_historyBit]
  exact coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth bit target observed hne x

/-- On clean scratchB, the corrected `vLe` selector-plus-subtract/add slice
preserves the zero-code branch-history no-op through the concrete subtract/add
data path. -/
theorem coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
  rw [coeffWorkSubUFromVThenAddRIntoSStep_get_historyBit]
  exact coeffWorkVLeSelectorBranchHistoryWriteStep_get_history_clean
    n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
    hscratchB

/-- The corrected `vLe` selector-plus-subtract/add slice preserves every
history slot except the selected target slot. -/
theorem
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
          n counterWidth bit target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
  rw [coeffWorkSubUFromVThenAddRIntoSStep_get_historyBit]
  exact coeffWorkVLeSelectorBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth bit target observed hne x

/-- The corrected `uGreater` selector-plus-subtract/add slice writes
`u := u - v` when the source-subtract carry/work inputs are clean. -/
theorem coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_u_sub_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
        n counterWidth bit historyIndex x).1.1.u =
      x.1.1.u - x.1.1.v := by
  let y :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
      historyIndex x
  have hcarryY : (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_scratchA]
    exact hcarry
  have hworkY :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          y = false := by
    intro k
    dsimp [y]
    have hpres :=
      coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_comparisonCarry
        n counterWidth bit historyIndex
        (coeffAdderComparisonCarryPrefixIndex n k) x
    calc
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          (coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
            historyIndex x) =
          ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
            x := by
        simpa [coeffAdderComparisonCarryPrefixWord] using hpres
      _ = false := hwork k
  have hmain :=
    coeffWorkSubVFromUThenAddSIntoRStep_get_u_sub_of_clean
      n counterWidth y hcarryY hworkY
  have hu :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_u
      n counterWidth bit historyIndex x
  have hv :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_v
      n counterWidth bit historyIndex x
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
  change (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth y).1.1.u =
    x.1.1.u - x.1.1.v
  dsimp [y] at hmain
  rw [hu, hv] at hmain
  exact hmain

/-- The corrected `uGreater` selector-plus-subtract/add slice preserves the
untouched `v` source word. -/
theorem coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_v
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
        n counterWidth bit historyIndex x).1.1.v =
      x.1.1.v := by
  let y :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
      historyIndex x
  have hsub := coeffWorkSubVFromUThenAddSIntoRStep_get_v n counterWidth y
  have hsel :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_v
      n counterWidth bit historyIndex x
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
  change (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth y).1.1.v =
    x.1.1.v
  rw [hsub, hsel]

/-- The corrected `uGreater` selector-plus-subtract/add slice writes
`r := r + s` when the coefficient-adder carry/work inputs are clean. -/
theorem coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_rCoeff_add_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
        n counterWidth bit historyIndex x).1.1.rCoeff =
      x.1.1.rCoeff + x.1.1.sCoeff := by
  let y :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
      historyIndex x
  have hcarryY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_carryIn]
    exact hcarry
  have hworkY :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get y =
          false := by
    intro k
    dsimp [y]
    rw [coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_carryWorkBit]
    exact hwork k
  have hmain :=
    coeffWorkSubVFromUThenAddSIntoRStep_get_rCoeff_add_of_clean
      n counterWidth y hcarryY hworkY
  have hr :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_rCoeff
      n counterWidth bit historyIndex x
  have hs :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep_get_sCoeff
      n counterWidth bit historyIndex x
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep]
  change
    (coeffWorkSubVFromUThenAddSIntoRStep n counterWidth y).1.1.rCoeff =
      x.1.1.rCoeff + x.1.1.sCoeff
  dsimp [y] at hmain
  rw [hr, hs] at hmain
  exact hmain

/-- The corrected `vLe` selector-plus-subtract/add slice writes `v := v - u`
when the source-subtract carry/work inputs are clean. -/
theorem coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_v_sub_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (coeffAdderScratchABit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          x = false) :
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep n counterWidth bit
        historyIndex x).1.1.v =
      x.1.1.v - x.1.1.u := by
  let y :=
    coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
      historyIndex x
  have hcarryY : (coeffAdderScratchABit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkVLeSelectorBranchHistoryWriteStep_get_scratchA]
    exact hcarry
  have hworkY :
      ∀ k : Fin (n - 1),
        ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          y = false := by
    intro k
    dsimp [y]
    have hpres :=
      coeffWorkVLeSelectorBranchHistoryWriteStep_get_comparisonCarry
        n counterWidth bit historyIndex
        (coeffAdderComparisonCarryPrefixIndex n k) x
    calc
      ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
          (coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
            historyIndex x) =
          ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit k).get
            x := by
        simpa [coeffAdderComparisonCarryPrefixWord] using hpres
      _ = false := hwork k
  have hmain :=
    coeffWorkSubUFromVThenAddRIntoSStep_get_v_sub_of_clean
      n counterWidth y hcarryY hworkY
  have hv :=
    coeffWorkVLeSelectorBranchHistoryWriteStep_get_v
      n counterWidth bit historyIndex x
  have hu :=
    coeffWorkVLeSelectorBranchHistoryWriteStep_get_u
      n counterWidth bit historyIndex x
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
  change
    (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth y).1.1.v =
      x.1.1.v - x.1.1.u
  dsimp [y] at hmain
  rw [hv, hu] at hmain
  exact hmain

/-- The corrected `vLe` selector-plus-subtract/add slice preserves the
untouched `u` source word. -/
theorem coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_u
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
        n counterWidth bit historyIndex x).1.1.u =
      x.1.1.u := by
  let y :=
    coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
      historyIndex x
  have hsub := coeffWorkSubUFromVThenAddRIntoSStep_get_u n counterWidth y
  have hsel :=
    coeffWorkVLeSelectorBranchHistoryWriteStep_get_u
      n counterWidth bit historyIndex x
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
  change (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth y).1.1.u =
    x.1.1.u
  rw [hsub, hsel]

/-- The corrected `vLe` selector-plus-subtract/add slice writes `s := s + r`
when the coefficient-adder carry/work inputs are clean. -/
theorem coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_sCoeff_add_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep n counterWidth bit
        historyIndex x).1.1.sCoeff =
      x.1.1.sCoeff + x.1.1.rCoeff := by
  let y :=
    coeffWorkVLeSelectorBranchHistoryWriteStep n counterWidth bit
      historyIndex x
  have hcarryY :
      (liftedCoeffAdderCarryInBit n counterWidth).get y = false := by
    dsimp [y]
    rw [coeffWorkVLeSelectorBranchHistoryWriteStep_get_carryIn]
    exact hcarry
  have hworkY :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get y =
          false := by
    intro k
    dsimp [y]
    rw [coeffWorkVLeSelectorBranchHistoryWriteStep_get_carryWorkBit]
    exact hwork k
  have hmain :=
    coeffWorkSubUFromVThenAddRIntoSStep_get_sCoeff_add_of_clean
      n counterWidth y hcarryY hworkY
  have hs :=
    coeffWorkVLeSelectorBranchHistoryWriteStep_get_sCoeff
      n counterWidth bit historyIndex x
  have hr :=
    coeffWorkVLeSelectorBranchHistoryWriteStep_get_rCoeff
      n counterWidth bit historyIndex x
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep]
  change
    (coeffWorkSubUFromVThenAddRIntoSStep n counterWidth y).1.1.sCoeff =
      x.1.1.sCoeff + x.1.1.rCoeff
  dsimp [y] at hmain
  rw [hs, hr] at hmain
  exact hmain

/-! ## Compact-carrier branch-history atom -/

namespace Compact

/-- Write the staged history-code bit to the sole persistent history word,
guarded by the compact active flag. -/
def activeScratchBToHistoryGate
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    EncodedBit.GateSpec (encoding n counterWidth) :=
  EncodedBit.GateSpec.toffoli
    (activeBit n counterWidth)
    (scratchBBit n counterWidth)
    (historyBit n counterWidth bit)
    (activeBit_scratchBBit_wire_ne n counterWidth)
    (activeBit_historyBit_wire_ne n counterWidth bit)
    (scratchBBit_historyBit_wire_ne n counterWidth bit)

/-- Physical one-gate history-write program on the compact carrier. -/
def activeScratchBToHistoryProgram
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.program
    (activeScratchBToHistoryGate n counterWidth bit)
    (QubitLayout.canonical _) .empty

/-- Semantic action of the compact history-write atom. -/
def activeScratchBToHistoryStep
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.step
    (activeScratchBToHistoryGate n counterWidth bit)

theorem activeScratchBToHistory_realizes
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (activeScratchBToHistoryProgram n counterWidth bit)
      (activeScratchBToHistoryStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizes (QubitLayout.canonical _) .empty
    (activeScratchBToHistoryGate n counterWidth bit)

/-- The compact history atom records the active staged history code. -/
theorem activeScratchBToHistoryStep_get_historyBit
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (historyBit n counterWidth bit).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      ((historyBit n counterWidth bit).get x ^^
        ((activeBit n counterWidth).get x &&
          (scratchBBit n counterWidth).get x)) := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_target
      (activeBit n counterWidth) (scratchBBit n counterWidth)
      (historyBit n counterWidth bit) x

/-- The compact history atom preserves the active flag. -/
theorem activeScratchBToHistoryStep_get_active
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      (activeBit n counterWidth).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (scratchBBit n counterWidth)
      (historyBit n counterWidth bit) (activeBit n counterWidth)
      (Ne.symm (activeBit_historyBit_wire_ne n counterWidth bit)) x

/-- The compact history atom preserves the staged history code. -/
theorem activeScratchBToHistoryStep_get_scratchB
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (scratchBBit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      (scratchBBit n counterWidth).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (scratchBBit n counterWidth)
      (historyBit n counterWidth bit) (scratchBBit n counterWidth)
      (Ne.symm (scratchBBit_historyBit_wire_ne n counterWidth bit)) x

/-- The compact history atom preserves the auxiliary branch-code bit. -/
theorem activeScratchBToHistoryStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      (scratchABit n counterWidth).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (scratchBBit n counterWidth)
      (historyBit n counterWidth bit) (scratchABit n counterWidth)
      (Ne.symm (scratchABit_historyBit_wire_ne n counterWidth bit)) x

/-- The compact history atom preserves the staged comparison result. -/
theorem activeScratchBToHistoryStep_get_compare
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      (compareBit n counterWidth).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (scratchBBit n counterWidth)
      (historyBit n counterWidth bit) (compareBit n counterWidth)
      (Ne.symm (compareBit_historyBit_wire_ne n counterWidth bit)) x

/-- The compact history atom preserves any bit other than its history target. -/
theorem activeScratchBToHistoryStep_get_of_target_ne
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (observed : EncodedBit (encoding n counterWidth))
    (hne : (historyBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (activeScratchBToHistoryStep n counterWidth bit x) =
      observed.get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (scratchBBit n counterWidth)
      (historyBit n counterWidth bit) observed hne x

/-- The compact history write preserves the complete `u` word. -/
theorem activeScratchBToHistoryStep_core_u
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (activeScratchBToHistoryStep
      n counterWidth historyIndex x).core.u = x.core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeScratchBToHistoryStep_get_of_target_ne
    n counterWidth historyIndex ((uValueWord n counterWidth).bit bit)
    (by
      simpa [historyBit, uValueWord, RegisterBits.uValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex)).symm) x
  simpa only [uValueWord_get] using h

/-- The compact history write preserves the complete `v` word. -/
theorem activeScratchBToHistoryStep_core_v
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (activeScratchBToHistoryStep
      n counterWidth historyIndex x).core.v = x.core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeScratchBToHistoryStep_get_of_target_ne
    n counterWidth historyIndex ((vValueWord n counterWidth).bit bit)
    (by
      simpa [historyBit, vValueWord, RegisterBits.vValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex)).symm) x
  simpa only [vValueWord_get] using h

/-- The compact history write preserves the complete `s` coefficient word. -/
theorem activeScratchBToHistoryStep_core_sCoeff
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (activeScratchBToHistoryStep
      n counterWidth historyIndex x).core.sCoeff = x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeScratchBToHistoryStep_get_of_target_ne
    n counterWidth historyIndex ((sCoeffValueWord n counterWidth).bit bit)
    (by
      simpa [historyBit, sCoeffValueWord, sCoeffValueBit,
        RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex)).symm) x
  simpa only [sCoeffValueWord, sCoeffValueBit_get] using h

/-- The compact history write preserves the complete `r` coefficient word. -/
theorem activeScratchBToHistoryStep_core_rCoeff
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (activeScratchBToHistoryStep
      n counterWidth historyIndex x).core.rCoeff = x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeScratchBToHistoryStep_get_of_target_ne
    n counterWidth historyIndex ((rCoeffValueWord n counterWidth).bit bit)
    (by
      simpa [historyBit, rCoeffValueWord, rCoeffValueBit,
        RegisterBits.rCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.rCoeff_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit) historyIndex)).symm) x
  simpa only [rCoeffValueWord, rCoeffValueBit_get] using h

/-- Every non-target history slot is preserved. -/
theorem activeScratchBToHistoryStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed) (x : Registers n counterWidth) :
    (historyBit n counterWidth observed).get
        (activeScratchBToHistoryStep n counterWidth target x) =
      (historyBit n counterWidth observed).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (scratchBBit n counterWidth)
      (historyBit n counterWidth target) (historyBit n counterWidth observed)
      (historyBit_wire_ne n counterWidth hne) x

theorem activeScratchBToHistoryGate_xMultiplicity
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (activeScratchBToHistoryGate n counterWidth bit).xMultiplicity = 0 := rfl

theorem activeScratchBToHistoryGate_cnotMultiplicity
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (activeScratchBToHistoryGate n counterWidth bit).cnotMultiplicity = 0 := rfl

theorem activeScratchBToHistoryGate_toffoliMultiplicity
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    (activeScratchBToHistoryGate n counterWidth bit).toffoliMultiplicity = 1 := rfl

/-- The literal history atom is self-inverse. -/
theorem activeScratchBToHistoryStep_self
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    activeScratchBToHistoryStep n counterWidth bit
        (activeScratchBToHistoryStep n counterWidth bit x) = x := by
  exact EncodedBit.GateSpec.step_step
    (activeScratchBToHistoryGate n counterWidth bit) x

end Compact

end
end MK
end MAU.Inversion
end QuantumAlg

end
