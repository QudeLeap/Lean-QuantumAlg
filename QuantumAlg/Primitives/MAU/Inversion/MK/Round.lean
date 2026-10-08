/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint
import all QuantumAlg.Primitives.MAU.Inversion.MK.AuxiliaryShift

/-!
# Fixed-round realization

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


end
end MK
end MAU.Inversion
end QuantumAlg


namespace QuantumAlg
namespace NumberTheory.BinaryGCD
namespace RoundState

open QuantumAlg.MAU.Inversion.MK
open QuantumAlg.Nat.FixedWidth

/-- Source-level integer-loop view of the concrete Kaliski registers. -/
def fromRegisters
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (kaliskiSteps paddingSteps : Nat) : RoundState where
  u := x.u.val
  v := x.v.val
  rCoeff := x.rCoeff.val
  sCoeff := x.sCoeff.val
  kaliskiSteps := kaliskiSteps
  paddingSteps := paddingSteps
  active := x.active

/-- The clean finite register seed reads out to the source-level initial
state [RNSL17, ECDLP.tex:409,445-446,468]. -/
theorem fromRegisters_initialRegisters
    (n counterWidth : Nat) (p x : Word n) :
    fromRegisters n counterWidth (initialRegisters n counterWidth p x) 0 0 =
      initial p.val x.val :=
  by
    simp [fromRegisters, initial, initialRegisters]

/-- Source-level branch selection from concrete registers agrees with the
register-facing selector signals when the staged comparison bit is valid. -/
theorem selectBranch_fromRegisters_eq_fromRegisterSignals_of_compare
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (kaliskiSteps paddingSteps : Nat)
    (hcompare : x.compare = decide (x.v.val < x.u.val)) :
    selectBranch (fromRegisters n counterWidth x kaliskiSteps paddingSteps) =
      Branch.fromRegisterSignals n counterWidth x := by
  rw [selectBranch_eq_fromCircuitSignals]
  simp [fromRegisters, Branch.fromRegisterSignals, hcompare]

/-- Source-level branch selection from the registers inside coefficient-adder
work agrees with the coefficient-work selector signals when the staged
comparison bit is valid. -/
theorem selectBranch_fromRegisters_eq_fromCoeffWorkSignals_of_compare
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (kaliskiSteps paddingSteps : Nat)
    (hcompare :
      (coeffAdderCompareBit n counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val)) :
    selectBranch (fromRegisters n counterWidth x.1.1 kaliskiSteps paddingSteps) =
      Branch.fromCoeffWorkSignals n counterWidth x := by
  have hcompareReg :
      x.1.1.compare = decide (x.1.1.v.val < x.1.1.u.val) := by
    simpa [coeffAdderCompareBit_get] using hcompare
  rw [selectBranch_fromRegisters_eq_fromRegisterSignals_of_compare
    n counterWidth x.1.1 kaliskiSteps paddingSteps hcompareReg]
  rfl

/-- When the low `u` and low `v` readouts are true and the staged comparison is
valid with `v < u`, the source selector agrees with the circuit-facing
`uGreater` odd branch. -/
theorem selectBranch_fromRegisters_eq_uGreater_of_coeffWork_odd_compare_valid_lt
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (kaliskiSteps paddingSteps : Nat)
    (hu :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hv :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hlt : x.1.1.v.val < x.1.1.u.val) :
    selectBranch (fromRegisters tail.succ counterWidth x.1.1
        kaliskiSteps paddingSteps) =
      Branch.uGreater := by
  rw [selectBranch_fromRegisters_eq_fromCoeffWorkSignals_of_compare
    tail.succ counterWidth x kaliskiSteps paddingSteps hcompare]
  rw [Branch.fromCoeffWorkSignals_eq_from_branch_bits]
  rw [hcompare]
  simp [hu, hv, hlt]

/-- When the low `u` and low `v` readouts are true and the staged comparison is
valid with `v < u` false, the source selector agrees with the circuit-facing
`vLe` odd branch. -/
theorem selectBranch_fromRegisters_eq_vLe_of_coeffWork_odd_compare_valid_not_lt
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (kaliskiSteps paddingSteps : Nat)
    (hu :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hv :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val))
    (hnlt : ¬ x.1.1.v.val < x.1.1.u.val) :
    selectBranch (fromRegisters tail.succ counterWidth x.1.1
        kaliskiSteps paddingSteps) =
      Branch.vLe := by
  rw [selectBranch_fromRegisters_eq_fromCoeffWorkSignals_of_compare
    tail.succ counterWidth x kaliskiSteps paddingSteps hcompare]
  rw [Branch.fromCoeffWorkSignals_eq_from_branch_bits]
  rw [hcompare]
  simp [hu, hv, hnlt]


/-- Canonical history-register slot used by a source fixed-round schedule
index. -/
def fixedRoundHistoryIndex (n : Nat)
    (roundIndex : Fin (fixedRoundCount n)) :
    Fin (2 * n) :=
  roundIndex

@[simp] theorem fixedRoundHistoryIndex_val (n : Nat)
    (roundIndex : Fin (fixedRoundCount n)) :
    (fixedRoundHistoryIndex n roundIndex).val = roundIndex.val := by
  rfl

/-- Distinct fixed-round schedule slots select distinct history-register
slots. -/
theorem fixedRoundHistoryIndex_ne_of_ne (n : Nat)
    {left right : Fin (fixedRoundCount n)}
    (hne : left ≠ right) :
    fixedRoundHistoryIndex n left ≠ fixedRoundHistoryIndex n right := by
  intro hslot
  apply hne
  apply Fin.ext
  simpa using congrArg Fin.val hslot

/-- The fixed-round history slot selected by a schedule index is initially
clean in the finite register seed. -/
theorem initialRegisters_fixedRoundHistoryBit_get
    (n counterWidth : Nat) (p x : Word n)
    (roundIndex : Fin (fixedRoundCount n)) :
    (RegisterBits.historyBit n counterWidth
        (fixedRoundHistoryIndex n roundIndex)).get
        (initialRegisters n counterWidth p x) =
      false :=
  initialRegisters_historyBit_get n counterWidth p x
    (fixedRoundHistoryIndex n roundIndex)

/-- The fixed source schedule enumerates exactly the `2n` history-register
slots, in round order. -/
def fixedRoundHistorySchedule (n : Nat) : List (Fin (2 * n)) :=
  List.ofFn fun roundIndex : Fin (fixedRoundCount n) =>
    fixedRoundHistoryIndex n roundIndex

@[simp] theorem fixedRoundHistorySchedule_length (n : Nat) :
    (fixedRoundHistorySchedule n).length = 2 * n := by
  simp [fixedRoundHistorySchedule]

/-- The `roundIndex`-th fixed schedule entry is the matching `m_i`
history-register slot. -/
theorem fixedRoundHistorySchedule_get (n : Nat)
    (roundIndex : Fin (fixedRoundCount n)) :
    (fixedRoundHistorySchedule n).get
        ⟨roundIndex.val, by
          rw [fixedRoundHistorySchedule_length]
          exact roundIndex.isLt⟩ =
      fixedRoundHistoryIndex n roundIndex := by
  simp only [fixedRoundHistorySchedule, List.get_ofFn]
  apply congrArg (fixedRoundHistoryIndex n)
  apply Fin.ext
  rfl

end RoundState
end NumberTheory.BinaryGCD
end QuantumAlg

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-! ## Explicit active-branch round family -/

/-- Explicit branch-selected active-round data path over the coefficient-adder
workspace.  This packages the four concrete active Kaliski branch wrappers
under one family indexed by the already-selected branch.  The data-dependent
branch selector and the post-termination counter mode remain separate
obligations [RNSL17, ECDLP.tex:399-421,425-475]. -/
def coeffWorkKaliskiActiveBranchRoundStep
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (branch : Branch) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  match branch with
  | Branch.uEven =>
      coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth uIndex historyIndex
  | Branch.vEven =>
      coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth uIndex vIndex historyIndex
  | Branch.uGreater =>
      coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth comparisonIndex historyIndex
  | Branch.vLe =>
      coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth comparisonIndex historyIndex

/-- Actual circuit for the explicit active-branch round family. -/
def coeffWorkKaliskiActiveBranchRoundProgram
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (branch : Branch) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithCoeffAdderWorkEncoding n counterWidth).width)).toQuantum := by
  cases branch with
  | uEven =>
      exact
        coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchProgram
          n counterWidth uIndex historyIndex
  | vEven =>
      exact
        coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchProgram
          n counterWidth uIndex vIndex historyIndex
  | uGreater =>
      exact
        coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchProgram
          n counterWidth comparisonIndex historyIndex
  | vLe =>
      exact
        coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchProgram
          n counterWidth comparisonIndex historyIndex

/-- The explicit active-branch circuit realizes the branch-selected semantic
step. -/
theorem coeffWorkKaliskiActiveBranchRound_realizes
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (branch : Branch) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkKaliskiActiveBranchRoundProgram
        n counterWidth uIndex vIndex comparisonIndex historyIndex branch)
      (coeffWorkKaliskiActiveBranchRoundStep
        n counterWidth uIndex vIndex comparisonIndex historyIndex branch) := by
  cases branch with
  | uEven =>
      exact coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatch_realizes
        n counterWidth uIndex historyIndex
  | vEven =>
      exact coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatch_realizes
        n counterWidth uIndex vIndex historyIndex
  | uGreater =>
      exact coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatch_realizes
        n counterWidth comparisonIndex historyIndex
  | vLe =>
      exact coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatch_realizes
        n counterWidth comparisonIndex historyIndex

/-- Explicit active-branch round family lifted to the full fixed-round
workspace, preserving the padding-counter increment work. -/
def fullRoundWorkKaliskiActiveBranchRoundStep
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (branch : Branch) :
    RegistersWithFullRoundWork n counterWidth ->
      RegistersWithFullRoundWork n counterWidth :=
  fun x =>
    (coeffWorkKaliskiActiveBranchRoundStep
      n counterWidth uIndex vIndex comparisonIndex historyIndex branch x.1,
      x.2)

/-- Actual circuit for the explicit active-branch family after lifting it to
the full fixed-round workspace. -/
def fullRoundWorkKaliskiActiveBranchRoundProgram
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (branch : Branch) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding n counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinaryPrefix
    (counterIncrementWorkEncoding counterWidth).width
    (coeffWorkKaliskiActiveBranchRoundProgram
      n counterWidth uIndex vIndex comparisonIndex historyIndex branch)

/-- The lifted active-branch circuit realizes the full-round semantic step. -/
theorem fullRoundWorkKaliskiActiveBranchRound_realizes
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (branch : Branch) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding n counterWidth)
      (fullRoundWorkKaliskiActiveBranchRoundProgram
        n counterWidth uIndex vIndex comparisonIndex historyIndex branch)
      (fullRoundWorkKaliskiActiveBranchRoundStep
        n counterWidth uIndex vIndex comparisonIndex historyIndex branch) :=
  UnitaryCircuit.Realizes.onBinaryPrefix
    (right := counterIncrementWorkEncoding counterWidth)
    (coeffWorkKaliskiActiveBranchRound_realizes
      n counterWidth uIndex vIndex comparisonIndex historyIndex branch)

/-- Odd-odd selector latch lifted to the full fixed-round workspace, preserving
the padding-counter increment work. -/
def fullRoundWorkOddOddSelectorToCarryStep
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    (coeffWorkOddOddSelectorToCarryStep
      tail counterWidth selectorIndex x.1,
      x.2)

/-- Gate list for the odd-odd selector latch lifted to the full fixed-round
workspace. -/
def fullRoundWorkOddOddSelectorToCarryGates
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  (coeffWorkOddOddSelectorToCarryGates tail counterWidth selectorIndex).map
    (EncodedBit.GateSpec.prodLeft
      (counterIncrementWorkEncoding counterWidth))

/-- Base-gate program for the full-round odd-odd selector latch. -/
def fullRoundWorkOddOddSelectorToCarryProgram
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkOddOddSelectorToCarryGates
      tail counterWidth selectorIndex)

/-- The full-round odd-odd selector latch gate list has its lifted semantic
step. -/
theorem fullRoundWorkOddOddSelectorToCarryStep_eq_gateList
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (fullRoundWorkOddOddSelectorToCarryGates
          tail counterWidth selectorIndex) x =
      fullRoundWorkOddOddSelectorToCarryStep
        tail counterWidth selectorIndex x := by
  unfold fullRoundWorkOddOddSelectorToCarryGates
    fullRoundWorkOddOddSelectorToCarryStep
  unfold registersWithFullRoundWorkEncoding
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  rw [coeffWorkOddOddSelectorToCarryStep_eq_gateList]

/-- The full-round odd-odd selector latch program realizes its lifted semantic
step. -/
theorem fullRoundWorkOddOddSelectorToCarry_realizes
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkOddOddSelectorToCarryProgram
        tail counterWidth selectorIndex)
      (fullRoundWorkOddOddSelectorToCarryStep
        tail counterWidth selectorIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (fullRoundWorkOddOddSelectorToCarryGates
      tail counterWidth selectorIndex)
    (fullRoundWorkOddOddSelectorToCarryStep_eq_gateList
      tail counterWidth selectorIndex)

/-- The full-round odd-odd selector latch preserves the padding-counter
increment work. -/
theorem fullRoundWorkOddOddSelectorToCarryStep_counterWork
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkOddOddSelectorToCarryStep
      tail counterWidth selectorIndex x).2 = x.2 := by
  rfl

/-- The full-round odd-odd selector latch xors `u[0] && v[0]` into the selected
comparison-carry bit in the lifted coefficient-work state. -/
theorem fullRoundWorkOddOddSelectorToCarryStep_get_selector
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex).get
        (fullRoundWorkOddOddSelectorToCarryStep
          tail counterWidth selectorIndex x).1 =
      ((coeffAdderComparisonCarryBit
          tail.succ counterWidth selectorIndex).get x.1 ^^
        ((coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 &&
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1)) := by
  cases x with
  | mk coeffState counterWork =>
      exact
        coeffWorkOddOddSelectorToCarryStep_get_selector
          tail counterWidth selectorIndex coeffState

/-- On a clean latch bit, the full-round odd-odd selector latch records exactly
`u[0] && v[0]` in the lifted coefficient-work state. -/
theorem fullRoundWorkOddOddSelectorToCarryStep_get_selector_clean
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hclean :
      (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex).get x.1 = false) :
    (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex).get
        (fullRoundWorkOddOddSelectorToCarryStep
          tail counterWidth selectorIndex x).1 =
      ((coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 &&
        (coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1) := by
  cases x with
  | mk coeffState counterWork =>
      exact
        coeffWorkOddOddSelectorToCarryStep_get_selector_clean
          tail counterWidth selectorIndex coeffState hclean

/-- The full-round odd-odd selector latch preserves the low `u` selector readout
in the lifted coefficient-work state. -/
theorem fullRoundWorkOddOddSelectorToCarryStep_get_u_low
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
        (fullRoundWorkOddOddSelectorToCarryStep
          tail counterWidth selectorIndex x).1 =
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 := by
  cases x with
  | mk coeffState counterWork =>
      exact
        coeffWorkOddOddSelectorToCarryStep_get_u_low
          tail counterWidth selectorIndex coeffState

/-- The full-round odd-odd selector latch preserves the low `v` selector readout
in the lifted coefficient-work state. -/
theorem fullRoundWorkOddOddSelectorToCarryStep_get_v_low
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
        (fullRoundWorkOddOddSelectorToCarryStep
          tail counterWidth selectorIndex x).1 =
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 := by
  cases x with
  | mk coeffState counterWork =>
      exact
        coeffWorkOddOddSelectorToCarryStep_get_v_low
          tail counterWidth selectorIndex coeffState

/-- Gate list that latches the active-nonzero odd-odd selector into the
full-round counter-increment carry-in bit.  Unlike comparison-work carry bits,
this bit is disjoint from the coefficient-work branch bodies, so it can serve
as the outer control source for a later selected active-nonzero wrapper. -/
def fullRoundWorkOddOddSelectorToCounterCarryInGates
    (tail counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  [ EncodedBit.GateSpec.toffoli uBit vBit target
      (EncodedBit.GateSpec.prodLeftWire_ne
        (counterIncrementWorkEncoding counterWidth)
        (coeffAdderUBit_coeffAdderVBit_wire_ne
          tail.succ counterWidth low low))
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderUBit tail.succ counterWidth low)
        (counterIncrementCarryInBit counterWidth))
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderVBit tail.succ counterWidth low)
        (counterIncrementCarryInBit counterWidth)) ]

/-- Base-gate program for latching the odd-odd selector into counter work. -/
def fullRoundWorkOddOddSelectorToCounterCarryInProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkOddOddSelectorToCounterCarryInGates
      tail counterWidth)

/-- Semantic step for latching the odd-odd selector into counter work. -/
def fullRoundWorkOddOddSelectorToCounterCarryInStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkOddOddSelectorToCounterCarryInGates
      tail counterWidth)

/-- The counter-work odd-odd selector latch gate list has its semantic step. -/
theorem fullRoundWorkOddOddSelectorToCounterCarryInStep_eq_gateList
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (fullRoundWorkOddOddSelectorToCounterCarryInGates
          tail counterWidth) x =
      fullRoundWorkOddOddSelectorToCounterCarryInStep
        tail counterWidth x := by
  rfl

/-- The counter-work odd-odd selector latch program realizes its semantic step.
-/
theorem fullRoundWorkOddOddSelectorToCounterCarryIn_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkOddOddSelectorToCounterCarryInProgram
        tail counterWidth)
      (fullRoundWorkOddOddSelectorToCounterCarryInStep
        tail counterWidth) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (fullRoundWorkOddOddSelectorToCounterCarryInGates
      tail counterWidth)
    (fullRoundWorkOddOddSelectorToCounterCarryInStep_eq_gateList
      tail counterWidth)

/-- Full-round active-flag bit in the standard full-round workspace layout. -/
def fullRoundWorkActiveBit (tail counterWidth : Nat) :
    EncodedBit (registersWithFullRoundWorkEncoding tail.succ counterWidth) :=
  liftCoeffAdderStateBitToFullRoundWork tail counterWidth
    (coeffAdderActiveBit tail.succ counterWidth)

/-- Gate list that latches `active && u[0] && v[0]` into the full-round
counter carry-in bit, using a selected counter carry-work bit as temporary
work.  This active-guarded selector feeds the latched selected/compare-carried
body dispatcher without recomputing the odd-odd predicate after mutation. -/
def fullRoundWorkActiveOddOddSelectorToCounterCarryInGates
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let active := fullRoundWorkActiveBit tail counterWidth
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  [ EncodedBit.GateSpec.toffoli active uBit work
      (EncodedBit.GateSpec.prodLeftWire_ne
        (counterIncrementWorkEncoding counterWidth)
        (coeffAdderActiveBit_coeffAdderUBit_wire_ne
          tail.succ counterWidth low))
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderActiveBit tail.succ counterWidth)
        (counterIncrementCarryWorkBit counterWidth workIndex))
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderUBit tail.succ counterWidth low)
        (counterIncrementCarryWorkBit counterWidth workIndex))
  , EncodedBit.GateSpec.toffoli work vBit target
      (Ne.symm
        (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
          tail counterWidth
          (coeffAdderVBit tail.succ counterWidth low)
          (counterIncrementCarryWorkBit counterWidth workIndex)))
      (Ne.symm
        (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
          tail counterWidth workIndex))
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderVBit tail.succ counterWidth low)
        (counterIncrementCarryInBit counterWidth))
  , EncodedBit.GateSpec.toffoli active uBit work
      (EncodedBit.GateSpec.prodLeftWire_ne
        (counterIncrementWorkEncoding counterWidth)
        (coeffAdderActiveBit_coeffAdderUBit_wire_ne
          tail.succ counterWidth low))
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderActiveBit tail.succ counterWidth)
        (counterIncrementCarryWorkBit counterWidth workIndex))
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderUBit tail.succ counterWidth low)
        (counterIncrementCarryWorkBit counterWidth workIndex)) ]

private theorem
    fullRoundWorkActiveOddOddSelectorToCounterCarryInGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1)) :
    ((fullRoundWorkActiveOddOddSelectorToCounterCarryInGates
      tail counterWidth workIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 3 := by
  change 1 + 1 + 1 + 0 = 3
  rfl

private theorem
    fullRoundWorkActiveOddOddSelectorToCounterCarryInGates_xMultiplicity_sum
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1)) :
    ((fullRoundWorkActiveOddOddSelectorToCounterCarryInGates
      tail counterWidth workIndex).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  change 0 + 0 + 0 + 0 = 0
  rfl

private theorem
    fullRoundWorkActiveOddOddSelectorToCounterCarryInGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1)) :
    ((fullRoundWorkActiveOddOddSelectorToCounterCarryInGates
      tail counterWidth workIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  change 0 + 0 + 0 + 0 = 0
  rfl

/-- Semantic step for the active-guarded odd-odd counter-work latch. -/
def fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkActiveOddOddSelectorToCounterCarryInGates
      tail counterWidth workIndex)

/-- Actual circuit for the active-guarded odd-odd counter-work latch. -/
def fullRoundWorkActiveOddOddSelectorToCounterCarryInProgram
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkActiveOddOddSelectorToCounterCarryInGates
      tail counterWidth workIndex)

/-- The active-guarded latch circuit realizes its gate-list step. -/
theorem fullRoundWorkActiveOddOddSelectorToCounterCarryIn_realizes
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkActiveOddOddSelectorToCounterCarryInProgram
        tail counterWidth workIndex)
      (fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
        tail counterWidth workIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (fullRoundWorkActiveOddOddSelectorToCounterCarryInGates
      tail counterWidth workIndex)

/-- Starting from clean counter carry-in and carry-work bits, the
active-guarded selector latch records exactly `active && u[0] && v[0]` in the
counter carry-in bit. -/
theorem fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_get_control_clean
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
          tail counterWidth workIndex x) =
      ((fullRoundWorkActiveBit tail counterWidth).get x &&
        (coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 &&
        (coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1) := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let active := fullRoundWorkActiveBit tail counterWidth
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  let y := EncodedBit.toffoliStep active uBit work x
  let z := EncodedBit.toffoliStep work vBit target y
  have hworkX : work.get x = false := by
    dsimp [work]
    exact hwork
  have htargetY : target.get y = false := by
    dsimp [y]
    rw [
      EncodedBit.toffoliStep_get_of_target_ne active uBit work target
        (Ne.symm
          (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
            tail counterWidth workIndex)) x]
    dsimp [target]
    exact hcontrol
  have hworkY :
      work.get y = (active.get x && uBit.get x) := by
    dsimp [y]
    rw [EncodedBit.toffoliStep_get_target]
    cases hactive : active.get x <;> cases hu : uBit.get x <;>
      simp [hworkX]
  have hvY : vBit.get y = vBit.get x := by
    dsimp [y]
    rw [
      EncodedBit.toffoliStep_get_of_target_ne active uBit work vBit
        (Ne.symm
          (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth
            (coeffAdderVBit tail.succ counterWidth low)
            (counterIncrementCarryWorkBit counterWidth workIndex))) x]
  have htargetZ :
      target.get z = (active.get x && uBit.get x && vBit.get x) := by
    dsimp [z]
    rw [EncodedBit.toffoliStep_get_target]
    rw [htargetY, hworkY, hvY]
    cases active.get x <;> cases uBit.get x <;> cases vBit.get x <;> simp
  change target.get (EncodedBit.toffoliStep active uBit work z) =
    ((fullRoundWorkActiveBit tail counterWidth).get x &&
      (coeffAdderUBit tail.succ counterWidth low).get x.1 &&
      (coeffAdderVBit tail.succ counterWidth low).get x.1)
  rw [EncodedBit.toffoliStep_get_of_target_ne active uBit work target]
  · rw [htargetZ]
    simp [active, uBit, vBit, low, fullRoundWorkActiveBit,
      liftCoeffAdderStateBitToFullRoundWork, BinaryLabelEncoding.prodLeftBit]
  · exact Ne.symm
      (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
        tail counterWidth workIndex)

/-- Starting from clean counter carry-work, the active-guarded selector latch
restores its temporary counter carry-work bit to clean. -/
theorem
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_get_counterCarryWork_clean
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
          tail counterWidth workIndex x) =
      false := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let active := fullRoundWorkActiveBit tail counterWidth
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  let y := EncodedBit.toffoliStep active uBit work x
  let z := EncodedBit.toffoliStep work vBit target y
  have hworkX : work.get x = false := by
    dsimp [work]
    exact hwork
  have hworkY :
      work.get y = (active.get x && uBit.get x) := by
    dsimp [y]
    rw [EncodedBit.toffoliStep_get_target]
    cases hactive : active.get x <;> cases hu : uBit.get x <;>
      simp [hworkX]
  have hworkZ : work.get z = (active.get x && uBit.get x) := by
    dsimp [z]
    rw [
      EncodedBit.toffoliStep_get_of_target_ne work vBit target work
        (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
          tail counterWidth workIndex) y]
    exact hworkY
  have hactiveZ : active.get z = active.get x := by
    dsimp [z, y]
    rw [
      EncodedBit.toffoliStep_get_of_target_ne work vBit target active
        (Ne.symm
          (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth
            (coeffAdderActiveBit tail.succ counterWidth)
            (counterIncrementCarryInBit counterWidth))) y]
    rw [
      EncodedBit.toffoliStep_get_of_target_ne active uBit work active
        (Ne.symm
          (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth
            (coeffAdderActiveBit tail.succ counterWidth)
            (counterIncrementCarryWorkBit counterWidth workIndex))) x]
  have huZ : uBit.get z = uBit.get x := by
    dsimp [z, y]
    rw [
      EncodedBit.toffoliStep_get_of_target_ne work vBit target uBit
        (Ne.symm
          (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth
            (coeffAdderUBit tail.succ counterWidth low)
            (counterIncrementCarryInBit counterWidth))) y]
    rw [
      EncodedBit.toffoliStep_get_of_target_ne active uBit work uBit
        (Ne.symm
          (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth
            (coeffAdderUBit tail.succ counterWidth low)
            (counterIncrementCarryWorkBit counterWidth workIndex))) x]
  change work.get (EncodedBit.toffoliStep active uBit work z) = false
  rw [EncodedBit.toffoliStep_get_target, hworkZ, hactiveZ, huZ]
  cases active.get x <;> cases uBit.get x <;> simp

/-- If the active guard is false and the temporary carry-work bit is clean,
the active-guarded odd-odd selector latch is a no-op. -/
theorem fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_eq_self_of_active_false
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : (fullRoundWorkActiveBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
        tail counterWidth workIndex x =
      x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let active := fullRoundWorkActiveBit tail counterWidth
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  have hactiveBit : active.get x = false := by
    dsimp [active]
    exact hactive
  have hworkBit : work.get x = false := by
    dsimp [work]
    exact hwork
  have hfirst : EncodedBit.toffoliStep active uBit work x = x := by
    unfold EncodedBit.toffoliStep
    rw [if_neg]
    simp [hactiveBit]
  have hmiddle : EncodedBit.toffoliStep work vBit target x = x := by
    unfold EncodedBit.toffoliStep
    rw [if_neg]
    simp [hworkBit]
  change EncodedBit.toffoliStep active uBit work
      (EncodedBit.toffoliStep work vBit target
        (EncodedBit.toffoliStep active uBit work x)) = x
  rw [hfirst, hmiddle]
  exact hfirst

/-- If low `u` is false and the temporary carry-work bit is clean, the
active-guarded odd-odd selector latch is a no-op. -/
theorem fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_eq_self_of_uLow_false
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
        tail counterWidth workIndex x =
      x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let active := fullRoundWorkActiveBit tail counterWidth
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  have huBit : uBit.get x = false := by
    simpa [uBit, low, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using huLow
  have hworkBit : work.get x = false := by
    dsimp [work]
    exact hwork
  have hfirst : EncodedBit.toffoliStep active uBit work x = x := by
    unfold EncodedBit.toffoliStep
    rw [if_neg]
    simp [huBit]
  have hmiddle : EncodedBit.toffoliStep work vBit target x = x := by
    unfold EncodedBit.toffoliStep
    rw [if_neg]
    simp [hworkBit]
  change EncodedBit.toffoliStep active uBit work
      (EncodedBit.toffoliStep work vBit target
        (EncodedBit.toffoliStep active uBit work x)) = x
  rw [hfirst, hmiddle]
  exact hfirst

/-- If low `v` is false, the active-guarded odd-odd selector latch leaves the
state unchanged after uncomputing its temporary carry-work bit. -/
theorem fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_eq_self_of_vLow_false
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
        tail counterWidth workIndex x =
      x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let active := fullRoundWorkActiveBit tail counterWidth
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  let y := EncodedBit.toffoliStep active uBit work x
  have hvBit : vBit.get x = false := by
    simpa [vBit, low, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using hvLow
  have hvY : vBit.get y = false := by
    dsimp [y]
    rw [
      EncodedBit.toffoliStep_get_of_target_ne active uBit work vBit
        (Ne.symm
          (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth
            (coeffAdderVBit tail.succ counterWidth low)
            (counterIncrementCarryWorkBit counterWidth workIndex))) x]
    exact hvBit
  have hmiddle : EncodedBit.toffoliStep work vBit target y = y := by
    unfold EncodedBit.toffoliStep
    rw [if_neg]
    simp [hvY]
  change EncodedBit.toffoliStep active uBit work
      (EncodedBit.toffoliStep work vBit target y) = x
  rw [hmiddle]
  exact
    EncodedBit.toffoliStep_toffoliStep active uBit work
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderActiveBit tail.succ counterWidth)
        (counterIncrementCarryWorkBit counterWidth workIndex))
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderUBit tail.succ counterWidth low)
        (counterIncrementCarryWorkBit counterWidth workIndex))
      x

/-- If the active guard and both low readouts are true and the temporary
carry-work bit is clean, the active-guarded selector latch flips the counter
carry-in bit and restores the temporary work. -/
theorem fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_eq_flip_of_active_lsb_true
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : (fullRoundWorkActiveBit tail counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
        tail counterWidth workIndex x =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let active := fullRoundWorkActiveBit tail counterWidth
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  let y := EncodedBit.toffoliStep active uBit work x
  have hactiveBit : active.get x = true := by
    dsimp [active]
    exact hactive
  have huBit : uBit.get x = true := by
    simpa [uBit, low, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using huLow
  have hvBit : vBit.get x = true := by
    simpa [vBit, low, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using hvLow
  have hworkBit : work.get x = false := by
    dsimp [work]
    exact hwork
  have hworkY : work.get y = true := by
    dsimp [y]
    rw [EncodedBit.toffoliStep_get_target]
    simp [hactiveBit, huBit, hworkBit]
  have hvY : vBit.get y = true := by
    dsimp [y]
    rw [
      EncodedBit.toffoliStep_get_of_target_ne active uBit work vBit
        (Ne.symm
          (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth
            (coeffAdderVBit tail.succ counterWidth low)
            (counterIncrementCarryWorkBit counterWidth workIndex))) x]
    exact hvBit
  have hmiddle :
      EncodedBit.toffoliStep work vBit target y = target.flip y := by
    unfold EncodedBit.toffoliStep
    rw [if_pos]
    simp [hworkY, hvY]
  have hactiveFlip :
      active.get (target.flip y) = active.get y := by
    rw [
      EncodedBit.get_flip_of_wire_ne target active
        (Ne.symm
          (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth
            (coeffAdderActiveBit tail.succ counterWidth)
            (counterIncrementCarryInBit counterWidth))) y]
  have huFlip :
      uBit.get (target.flip y) = uBit.get y := by
    rw [
      EncodedBit.get_flip_of_wire_ne target uBit
        (Ne.symm
          (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
            tail counterWidth
            (coeffAdderUBit tail.succ counterWidth low)
            (counterIncrementCarryInBit counterWidth))) y]
  have hcomm :
      EncodedBit.toffoliStep active uBit work (target.flip y) =
        target.flip (EncodedBit.toffoliStep active uBit work y) := by
    unfold EncodedBit.toffoliStep
    rw [hactiveFlip, huFlip]
    cases active.get y <;> cases uBit.get y <;> simp [EncodedBit.flip_comm]
  change EncodedBit.toffoliStep active uBit work
      (EncodedBit.toffoliStep work vBit target y) = target.flip x
  rw [hmiddle, hcomm]
  rw [
    EncodedBit.toffoliStep_toffoliStep active uBit work
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderActiveBit tail.succ counterWidth)
        (counterIncrementCarryWorkBit counterWidth workIndex))
      (liftCoeffAdderStateBit_liftCounterIncrementWorkBitToFullRoundWork_wire_ne
        tail counterWidth
        (coeffAdderUBit tail.succ counterWidth low)
        (counterIncrementCarryWorkBit counterWidth workIndex))
      x]

/-- The counter-work odd-odd selector latch xors `u[0] && v[0]` into the
counter carry-in latch bit. -/
theorem fullRoundWorkOddOddSelectorToCounterCarryInStep_get_control
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (fullRoundWorkOddOddSelectorToCounterCarryInStep
          tail counterWidth x) =
      ((fullRoundWorkCounterCarryInBit tail counterWidth).get x ^^
        ((coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 &&
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1)) := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  simpa [fullRoundWorkOddOddSelectorToCounterCarryInStep,
    fullRoundWorkOddOddSelectorToCounterCarryInGates, low, uBit, vBit,
    target, liftCoeffAdderStateBitToFullRoundWork,
    fullRoundWorkCounterCarryInBit,
    liftCounterIncrementWorkBitToFullRoundWork,
    BinaryLabelEncoding.prodLeftBit,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_target uBit vBit target x

/-- On clean counter carry-in work, the counter-work odd-odd selector latch
records exactly `u[0] && v[0]`. -/
theorem fullRoundWorkOddOddSelectorToCounterCarryInStep_get_control_clean
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hclean :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (fullRoundWorkOddOddSelectorToCounterCarryInStep
          tail counterWidth x) =
      ((coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 &&
        (coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1) := by
  rw [fullRoundWorkOddOddSelectorToCounterCarryInStep_get_control]
  simp [hclean]

/-- Latching the odd-odd selector into counter work preserves the entire
coefficient-work state. -/
theorem fullRoundWorkOddOddSelectorToCounterCarryInStep_coeffState
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkOddOddSelectorToCounterCarryInStep
      tail counterWidth x).1 = x.1 := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  change (EncodedBit.toffoliStep uBit vBit target x).1 = x.1
  unfold EncodedBit.toffoliStep
  by_cases hcontrols : uBit.get x && vBit.get x
  · rw [if_pos hcontrols]
    simp [target, fullRoundWorkCounterCarryInBit,
      liftCounterIncrementWorkBitToFullRoundWork,
      BinaryLabelEncoding.prodRightBit]
  · rw [if_neg hcontrols]

/-- Latching the odd-odd selector into counter carry-in preserves each
counter-increment source bit. -/
theorem fullRoundWorkOddOddSelectorToCounterCarryInStep_get_counterSource
    (tail counterWidth : Nat) (bit : Fin counterWidth)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkCounterSourceBit tail counterWidth bit).get
        (fullRoundWorkOddOddSelectorToCounterCarryInStep
          tail counterWidth x) =
      (fullRoundWorkCounterSourceBit tail counterWidth bit).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  let observed := fullRoundWorkCounterSourceBit tail counterWidth bit
  simpa [fullRoundWorkOddOddSelectorToCounterCarryInStep,
    fullRoundWorkOddOddSelectorToCounterCarryInGates, low, uBit, vBit,
    target, observed, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne uBit vBit target observed
      (fullRoundWorkCounterCarryIn_counterSource_wire_ne
        tail counterWidth bit) x

/-- Latching the odd-odd selector into counter carry-in preserves each
counter-increment carry-work bit. -/
theorem fullRoundWorkOddOddSelectorToCounterCarryInStep_get_counterCarryWork
    (tail counterWidth : Nat) (bit : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkCounterCarryWorkBit tail counterWidth bit).get
        (fullRoundWorkOddOddSelectorToCounterCarryInStep
          tail counterWidth x) =
      (fullRoundWorkCounterCarryWorkBit tail counterWidth bit).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  let observed := fullRoundWorkCounterCarryWorkBit tail counterWidth bit
  simpa [fullRoundWorkOddOddSelectorToCounterCarryInStep,
    fullRoundWorkOddOddSelectorToCounterCarryInGates, low, uBit, vBit,
    target, observed, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne uBit vBit target observed
      (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
        tail counterWidth bit) x

/-- If the low `u` readout is false, the counter-work odd-odd selector latch
is a no-op. -/
theorem fullRoundWorkOddOddSelectorToCounterCarryInStep_eq_self_of_uLow_false
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkOddOddSelectorToCounterCarryInStep tail counterWidth x =
      x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  have hu : uBit.get x = false := by
    simpa [uBit, low, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using huLow
  change EncodedBit.toffoliStep uBit vBit target x = x
  unfold EncodedBit.toffoliStep
  rw [if_neg]
  simp [hu]

/-- If the low `v` readout is false, the counter-work odd-odd selector latch
is a no-op. -/
theorem fullRoundWorkOddOddSelectorToCounterCarryInStep_eq_self_of_vLow_false
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkOddOddSelectorToCounterCarryInStep tail counterWidth x =
      x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  have hv : vBit.get x = false := by
    simpa [vBit, low, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using hvLow
  change EncodedBit.toffoliStep uBit vBit target x = x
  unfold EncodedBit.toffoliStep
  rw [if_neg]
  simp [hv]

/-- If both low readouts are true, the counter-work odd-odd selector latch is
exactly a flip of the counter carry-in latch bit. -/
theorem fullRoundWorkOddOddSelectorToCounterCarryInStep_eq_flip_of_lsb_true
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true) :
    fullRoundWorkOddOddSelectorToCounterCarryInStep tail counterWidth x =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  let uBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderUBit tail.succ counterWidth low)
  let vBit :=
    liftCoeffAdderStateBitToFullRoundWork tail counterWidth
      (coeffAdderVBit tail.succ counterWidth low)
  let target := fullRoundWorkCounterCarryInBit tail counterWidth
  have hu : uBit.get x = true := by
    simpa [uBit, low, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using huLow
  have hv : vBit.get x = true := by
    simpa [vBit, low, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using hvLow
  change EncodedBit.toffoliStep uBit vBit target x = target.flip x
  unfold EncodedBit.toffoliStep
  rw [if_pos]
  simp [hu, hv]

/-- Selected branch-code/history/aux-shift dispatch lifted to the full
fixed-round workspace, preserving the padding-counter increment work. -/
def fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth tempIndex historyIndex x.1,
      x.2)

/-- Gate list for selected branch-code/history/aux-shift dispatch lifted to the
full fixed-round workspace. -/
def fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
    tail counterWidth tempIndex historyIndex).map
      (EncodedBit.GateSpec.prodLeft
        (counterIncrementWorkEncoding counterWidth))

/-- Base-gate program for selected branch-code/history/aux-shift dispatch lifted
to the full fixed-round workspace. -/
def fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchProgram
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex)

/-- The explicit full-round selected branch-code/history/aux-shift gate list has
the existing lifted semantic action. -/
theorem
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
          tail counterWidth tempIndex historyIndex) x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x := by
  unfold fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
  unfold registersWithFullRoundWorkEncoding
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList]

/-- The full-round selected branch-code/history/aux-shift program realizes the
existing lifted semantic action. -/
theorem fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatch_realizes
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchProgram
        tail counterWidth tempIndex historyIndex)
      (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex)
    (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList
      tail counterWidth tempIndex historyIndex)

/-- Full-round product lifting preserves the selected source length. -/
theorem fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_length
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex).length = 18 * tail + 24 := by
  simp only [fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates,
    List.length_map,
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_length]

private theorem
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_events
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex).map (EncodedBit.GateSpec.event .empty) =
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex).map
        (EncodedBit.GateSpec.event .empty) := by
  unfold fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
    registersWithFullRoundWorkEncoding
  rw [EncodedBit.GateSpec.map_event_prodLeft]

/-- Full-round product lifting preserves the selected source CNOT coordinate. -/
theorem
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  calc
    ((fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
        tail counterWidth tempIndex historyIndex).map
          EncodedBit.GateSpec.cnotMultiplicity).sum =
        ((coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
          tail counterWidth tempIndex historyIndex).map
            EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        .empty
        (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_events
          tail counterWidth tempIndex historyIndex)
    _ = 1 :=
      coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_cnotMultiplicity_sum
        tail counterWidth tempIndex historyIndex

/-- Full-round product lifting preserves the selected source Toffoli coordinate. -/
theorem
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 18 * tail + 19 := by
  calc
    ((fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
        tail counterWidth tempIndex historyIndex).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum =
        ((coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
          tail counterWidth tempIndex historyIndex).map
            EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        .empty
        (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_events
          tail counterWidth tempIndex historyIndex)
    _ = 18 * tail + 19 :=
      coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_toffoliMultiplicity_sum
        tail counterWidth tempIndex historyIndex

/-- The selected dispatch source contains exactly four X leaves. -/
theorem
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_xMultiplicity_sum
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex).map
        EncodedBit.GateSpec.xMultiplicity).sum = 4 := by
  have htotal := EncodedBit.GateSpec.length_eq_multiplicity_sums
    (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex)
  rw [fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_length,
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_cnotMultiplicity_sum,
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_toffoliMultiplicity_sum]
    at htotal
  omega

/-- The lifted selected branch-code/history/aux-shift dispatch preserves every
history slot except the selected target slot while carrying padding-counter
work unchanged. -/
theorem
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (target observed : Fin (2 * tail.succ)) (hne : target ≠ observed)
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex target x).1 =
      (coeffAdderHistoryBit tail.succ counterWidth observed).get x.1 := by
  rw [fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
      tail counterWidth tempIndex target observed hne x.1

/-- On inactive clean branch-code work, the lifted selected branch-code/history/
aux-shift dispatch is a no-op and preserves counter work. -/
theorem
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_self_of_active_false_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x.1 = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x.1 = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get
          x.1 = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x.1 = false) :
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x =
      x := by
  cases x with
  | mk coeffState counterWork =>
      simp [fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep,
        coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_self_of_active_false_clean
          tail counterWidth tempIndex historyIndex coeffState hscratchA
          hscratchB htemp hactive]

/-- Selector-selected odd data path followed by carried branch-code/history/
aux-shift dispatch, lifted to the full fixed-round workspace while preserving
padding-counter increment work.  This names the odd semantic route; a
concrete circuit for the data-dependent carried dispatch remains a separate
obligation. -/
def fullRoundWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
      tail counterWidth comparisonIndex historyIndex x.1,
      x.2)

/-- Concrete compare-conditioned carried odd dispatch lifted to the full
fixed-round workspace while preserving padding-counter increment work. -/
def fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
      tail counterWidth comparisonIndex historyIndex x.1,
      x.2)

/-- The lifted latched carried odd route preserves every non-target history
slot on clean selected-control inputs while carrying padding-counter work
unchanged. -/
theorem
    fullRoundWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_get_historyBit_of_ne_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (target observed : Fin (2 * tail.succ)) (hne : target ≠ observed)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (fullRoundWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
          tail counterWidth comparisonIndex target
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      (RegisterBits.historyBit tail.succ counterWidth observed).get x := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep]
    using
      coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_get_historyBit_of_ne_clean
        tail counterWidth comparisonIndex target observed hne x work hscratchA
        hcontrolWork

/-- The lifted concrete compare-carried odd route preserves every non-target
history slot on clean selected-control inputs while carrying padding-counter
work unchanged. -/
theorem
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_get_historyBit_of_ne_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (target observed : Fin (2 * tail.succ)) (hne : target ≠ observed)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex target
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      (RegisterBits.historyBit tail.succ counterWidth observed).get x := by
  simpa [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
    using
      coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_get_historyBit_of_ne_clean
        tail counterWidth comparisonIndex target observed hne x work hscratchA
        hcontrolWork

/-- Short theorem name for non-target history preservation along the
compare-carried branch on clean work inputs. -/
theorem fullRoundWorkCompareCarriedHistoryBitOfNeClean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (target observed : Fin (2 * tail.succ)) (hne : target ≠ observed)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex target
          (((x, cleanComparisonWork tail.succ), work), counterWork)).1 =
      (RegisterBits.historyBit tail.succ counterWidth observed).get x :=
  fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_get_historyBit_of_ne_clean
    tail counterWidth comparisonIndex target observed hne x work counterWork
    hscratchA hcontrolWork

/-- Gate list for the concrete compare-conditioned carried odd dispatch lifted
to the full fixed-round workspace. -/
def fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
    tail counterWidth comparisonIndex historyIndex).map
      (EncodedBit.GateSpec.prodLeft
        (counterIncrementWorkEncoding counterWidth))

/-- Base-gate program for the concrete compare-conditioned carried odd dispatch
lifted to the full fixed-round workspace. -/
def fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex)

/-- The explicit full-round compare-carried odd dispatch gate list has the
existing lifted semantic action. -/
theorem
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
          tail counterWidth comparisonIndex historyIndex) x =
      fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  unfold fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
  unfold registersWithFullRoundWorkEncoding
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  rw [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList]

/-- The full-round compare-carried odd dispatch program realizes the existing
lifted semantic action. -/
theorem
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatch_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchProgram
        tail counterWidth comparisonIndex historyIndex)
      (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex)
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList
      tail counterWidth comparisonIndex historyIndex)

/-- Full-round product lifting preserves the compare-carried source length. -/
theorem
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_length
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex).length =
      108 * tail + 75 := by
  simp only [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates,
    List.length_map,
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_length]

private theorem
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_events
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex).map
        (EncodedBit.GateSpec.event .empty) =
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex).map
        (EncodedBit.GateSpec.event .empty) := by
  unfold fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
    registersWithFullRoundWorkEncoding
  rw [EncodedBit.GateSpec.map_event_prodLeft]

/-- Full-round product lifting preserves the compare-carried CNOT coordinate. -/
theorem
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  calc
    ((fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
        tail counterWidth comparisonIndex historyIndex).map
          EncodedBit.GateSpec.cnotMultiplicity).sum =
        ((coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
          tail counterWidth comparisonIndex historyIndex).map
            EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        .empty
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_events
          tail counterWidth comparisonIndex historyIndex)
    _ = 1 :=
      coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_cnotMultiplicity_sum
        tail counterWidth comparisonIndex historyIndex

/-- Full-round product lifting preserves the compare-carried Toffoli coordinate. -/
theorem
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 104 * tail + 66 := by
  calc
    ((fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
        tail counterWidth comparisonIndex historyIndex).map
          EncodedBit.GateSpec.toffoliMultiplicity).sum =
        ((coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
          tail counterWidth comparisonIndex historyIndex).map
            EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        .empty
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_events
          tail counterWidth comparisonIndex historyIndex)
    _ = 104 * tail + 66 :=
      coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_toffoliMultiplicity_sum
        tail counterWidth comparisonIndex historyIndex

/-- The compare-carried dispatch source contains exactly `4t+8` X leaves. -/
theorem
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_xMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex).map
        EncodedBit.GateSpec.xMultiplicity).sum = 4 * tail + 8 := by
  have htotal := EncodedBit.GateSpec.length_eq_multiplicity_sums
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex)
  rw [fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_length,
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_cnotMultiplicity_sum,
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_toffoliMultiplicity_sum]
    at htotal
  omega

/-- A gate list whose gates are all wire-disjoint from an observed bit preserves
that bit's readout. -/
private theorem gateSpecStepList_get_of_bitDisjoint
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec encoding))
    (observed : EncodedBit encoding)
    (h : ∀ gate, gate ∈ gates ->
      EncodedBit.GateSpec.bitDisjoint observed gate)
    (x : Data) :
    observed.get (EncodedBit.GateSpec.stepList gates x) = observed.get x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      change observed.get (EncodedBit.GateSpec.stepList rest
          (EncodedBit.GateSpec.step gate x)) = observed.get x
      rw [ih (fun next hnext => h next (by simp [hnext]))
        (EncodedBit.GateSpec.step gate x)]
      exact EncodedBit.GateSpec.step_get_of_bitDisjoint gate observed
        (h gate (by simp)) x

/-- The lifted selected branch-code/history/aux-shift dispatch is wire-disjoint
from the full-round counter carry-in latch. -/
theorem
    fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryIn
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ∀ gate,
      gate ∈
          fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
            tail counterWidth tempIndex historyIndex ->
        EncodedBit.GateSpec.bitDisjoint
          (fullRoundWorkCounterCarryInBit tail counterWidth) gate := by
  intro gate hgate
  unfold fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
    at hgate
  rcases List.mem_map.mp hgate with ⟨baseGate, _hbase, rfl⟩
  exact
    fullRoundWorkCounterBit_prodLeftGate_bitDisjoint tail counterWidth
      (counterIncrementCarryInBit counterWidth) baseGate

/-- The lifted selected branch-code/history/aux-shift dispatch is wire-disjoint
from any full-round counter carry-work bit. -/
theorem
    fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryWork
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ∀ gate,
      gate ∈
          fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
            tail counterWidth tempIndex historyIndex ->
        EncodedBit.GateSpec.bitDisjoint
          (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
          gate := by
  intro gate hgate
  unfold fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
    at hgate
  rcases List.mem_map.mp hgate with ⟨baseGate, _hbase, rfl⟩
  exact
    fullRoundWorkCounterBit_prodLeftGate_bitDisjoint tail counterWidth
      (counterIncrementCarryWorkBit counterWidth workIndex) baseGate

/-- The lifted compare-carried odd dispatch is wire-disjoint from the
full-round counter carry-in latch. -/
theorem
    fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryIn
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ∀ gate,
      gate ∈
          fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
            tail counterWidth comparisonIndex historyIndex ->
        EncodedBit.GateSpec.bitDisjoint
          (fullRoundWorkCounterCarryInBit tail counterWidth) gate := by
  intro gate hgate
  unfold fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
    at hgate
  rcases List.mem_map.mp hgate with ⟨baseGate, _hbase, rfl⟩
  exact
    fullRoundWorkCounterBit_prodLeftGate_bitDisjoint tail counterWidth
      (counterIncrementCarryInBit counterWidth) baseGate

/-- The lifted compare-carried odd dispatch is wire-disjoint from any
full-round counter carry-work bit. -/
theorem
    fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryWork
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ∀ gate,
      gate ∈
          fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
            tail counterWidth comparisonIndex historyIndex ->
        EncodedBit.GateSpec.bitDisjoint
          (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
          gate := by
  intro gate hgate
  unfold fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
    at hgate
  rcases List.mem_map.mp hgate with ⟨baseGate, _hbase, rfl⟩
  exact
    fullRoundWorkCounterBit_prodLeftGate_bitDisjoint tail counterWidth
      (counterIncrementCarryWorkBit counterWidth workIndex) baseGate

/-- The lifted selected branch-code/history/aux-shift dispatch preserves the
full-round counter carry-in latch readout. -/
theorem fullRoundWorkSelectedDispatchStep_get_counterCarryIn
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x := by
  rw [←
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList
      tail counterWidth tempIndex historyIndex x]
  exact
    gateSpecStepList_get_of_bitDisjoint
      (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
        tail counterWidth tempIndex historyIndex)
      (fullRoundWorkCounterCarryInBit tail counterWidth)
      (fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryIn
        tail counterWidth tempIndex historyIndex)
      x

/-- The lifted selected branch-code/history/aux-shift dispatch preserves any
full-round counter carry-work readout. -/
theorem fullRoundWorkSelectedDispatchStep_get_counterCarryWork
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x := by
  rw [←
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList
      tail counterWidth tempIndex historyIndex x]
  exact
    gateSpecStepList_get_of_bitDisjoint
      (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
        tail counterWidth tempIndex historyIndex)
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
      (fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryWork
        tail counterWidth tempIndex historyIndex workIndex)
      x

/-- The lifted compare-carried odd dispatch preserves the full-round counter
carry-in latch readout. -/
theorem fullRoundWorkCompareCarriedDispatchStep_get_counterCarryIn
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex x) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x := by
  rw [←
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList
      tail counterWidth comparisonIndex historyIndex x]
  exact
    gateSpecStepList_get_of_bitDisjoint
      (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
        tail counterWidth comparisonIndex historyIndex)
      (fullRoundWorkCounterCarryInBit tail counterWidth)
      (fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryIn
        tail counterWidth comparisonIndex historyIndex)
      x

/-- The lifted compare-carried odd dispatch preserves any full-round counter
carry-work readout. -/
theorem fullRoundWorkCompareCarriedDispatchStep_get_counterCarryWork
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex x) =
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x := by
  rw [←
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList
      tail counterWidth comparisonIndex historyIndex x]
  exact
    gateSpecStepList_get_of_bitDisjoint
      (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
        tail counterWidth comparisonIndex historyIndex)
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
      (fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryWork
        tail counterWidth comparisonIndex historyIndex workIndex)
      x

/-- The lifted compare-carried odd dispatch commutes with flipping the
full-round counter carry-in latch, since that latch is wire-disjoint from the
dispatch body. -/
theorem fullRoundWorkCompareCarriedDispatchStep_flip_counterCarryIn
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex
        ((fullRoundWorkCounterCarryInBit tail counterWidth).flip x) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex x) := by
  rw [←
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList
      tail counterWidth comparisonIndex historyIndex
      ((fullRoundWorkCounterCarryInBit tail counterWidth).flip x)]
  rw [EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex)
    (fullRoundWorkCounterCarryInBit tail counterWidth)
    (fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryIn
      tail counterWidth comparisonIndex historyIndex)
    x]
  rw [
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList
      tail counterWidth comparisonIndex historyIndex x]

/-- Counter-carry-in-controlled selected branch-code/history/aux-shift dispatch
over the full-round workspace.  The control bit is the odd-odd latch and the
work bit is a separate counter carry-work bit. -/
def
    fullRoundWorkCounterCarryInControlledSelectedDispatchGates
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (fullRoundWorkCounterCarryInBit tail counterWidth)
    (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
    (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex)
    (fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryIn
      tail counterWidth tempIndex historyIndex)
    (fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryWork
      tail counterWidth tempIndex historyIndex workIndex)
    (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
      tail counterWidth workIndex)

/-- Step function for the counter-carry-in-controlled selected dispatch. -/
def
    fullRoundWorkCounterCarryInControlledSelectedDispatchStep
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkCounterCarryInControlledSelectedDispatchGates
      tail counterWidth tempIndex historyIndex workIndex)

/-- Actual circuit for the counter-carry-in-controlled selected dispatch. -/
def
    fullRoundWorkCounterCarryInControlledSelectedDispatchProgram
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkCounterCarryInControlledSelectedDispatchGates
      tail counterWidth tempIndex historyIndex workIndex)

/-- The controlled selected-dispatch circuit realizes its gate-list step. -/
theorem fullRoundWorkCounterCarryInControlledSelectedDispatch_realizes
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkCounterCarryInControlledSelectedDispatchProgram
        tail counterWidth tempIndex historyIndex workIndex)
      (fullRoundWorkCounterCarryInControlledSelectedDispatchStep
        tail counterWidth tempIndex historyIndex workIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (fullRoundWorkCounterCarryInControlledSelectedDispatchGates
      tail counterWidth tempIndex historyIndex workIndex)

/-- If the counter carry-in control is false, the controlled selected dispatch
is a no-op. -/
theorem
    fullRoundWorkCounterCarryInControlledSelectedDispatchStep_eq_self_of_control_false
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false) :
    fullRoundWorkCounterCarryInControlledSelectedDispatchStep
        tail counterWidth tempIndex historyIndex workIndex x =
      x := by
  simpa [
    fullRoundWorkCounterCarryInControlledSelectedDispatchStep,
    fullRoundWorkCounterCarryInControlledSelectedDispatchGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (fullRoundWorkCounterCarryInBit tail counterWidth)
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
      (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
        tail counterWidth tempIndex historyIndex)
      (fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryIn
        tail counterWidth tempIndex historyIndex)
      (fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryWork
        tail counterWidth tempIndex historyIndex workIndex)
      (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
        tail counterWidth workIndex)
      x hcontrol

/-- If the counter carry-in control is true and the carry-work bit is clean, the
controlled selected dispatch acts like the original selected dispatch. -/
theorem
    fullRoundWorkCounterCarryInControlledSelectedDispatchStep_eq_dispatch_of_control_true
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = true)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    fullRoundWorkCounterCarryInControlledSelectedDispatchStep
        tail counterWidth tempIndex historyIndex workIndex x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x := by
  calc
    fullRoundWorkCounterCarryInControlledSelectedDispatchStep
        tail counterWidth tempIndex historyIndex workIndex x =
        EncodedBit.GateSpec.stepList
          (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
            tail counterWidth tempIndex historyIndex) x := by
      simpa [
        fullRoundWorkCounterCarryInControlledSelectedDispatchStep,
        fullRoundWorkCounterCarryInControlledSelectedDispatchGates,
        EncodedBit.GateSpec.controlledListWithWorkStep] using
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
          (fullRoundWorkCounterCarryInBit tail counterWidth)
          (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
          (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
            tail counterWidth tempIndex historyIndex)
          (fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryIn
            tail counterWidth tempIndex historyIndex)
          (fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryWork
            tail counterWidth tempIndex historyIndex workIndex)
          (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
            tail counterWidth workIndex)
          x hcontrol hwork
    _ = fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x :=
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList
        tail counterWidth tempIndex historyIndex x

/-- Counter-carry-in-false-controlled selected branch-code/history/aux-shift
dispatch over the full-round workspace. -/
def
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  [EncodedBit.GateSpec.x (fullRoundWorkCounterCarryInBit tail counterWidth)] ++
  fullRoundWorkCounterCarryInControlledSelectedDispatchGates
    tail counterWidth tempIndex historyIndex workIndex ++
  [EncodedBit.GateSpec.x (fullRoundWorkCounterCarryInBit tail counterWidth)]

/-- Step function for the counter-carry-in-false-controlled selected
dispatch. -/
def
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates
      tail counterWidth tempIndex historyIndex workIndex)

/-- Actual circuit for the counter-carry-in-false-controlled selected
dispatch. -/
def
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchProgram
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates
      tail counterWidth tempIndex historyIndex workIndex)

/-- The false-controlled selected-dispatch circuit realizes its gate-list
step. -/
theorem fullRoundWorkCounterCarryInFalseControlledSelectedDispatch_realizes
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkCounterCarryInFalseControlledSelectedDispatchProgram
        tail counterWidth tempIndex historyIndex workIndex)
      (fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
        tail counterWidth tempIndex historyIndex workIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates
      tail counterWidth tempIndex historyIndex workIndex)

/-- The false-control wrapper is a flip-run-flip use of the true-control
selected-dispatch wrapper. -/
theorem
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep_eq_flip_run_flip
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
        tail counterWidth tempIndex historyIndex workIndex x =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkCounterCarryInControlledSelectedDispatchStep
          tail counterWidth tempIndex historyIndex workIndex
          ((fullRoundWorkCounterCarryInBit tail counterWidth).flip x)) := by
  unfold fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates
  simp only [List.cons_append, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step]
  rw [EncodedBit.GateSpec.stepList_append]
  rfl

/-- If the counter carry-in latch is false and the carry-work bit is clean, the
false-controlled selected dispatch acts like the original selected dispatch. -/
theorem
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep_eq_dispatch
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
        tail counterWidth tempIndex historyIndex workIndex x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x := by
  let control := fullRoundWorkCounterCarryInBit tail counterWidth
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  let gates :=
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex
  have hcontrolFlip : control.get (control.flip x) = true := by
    dsimp [control]
    rw [EncodedBit.get_flip_self, hcontrol]
    rfl
  have hworkFlip : work.get (control.flip x) = false := by
    dsimp [work, control]
    rw [EncodedBit.get_flip_of_wire_ne
      (fullRoundWorkCounterCarryInBit tail counterWidth)
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)]
    · exact hwork
    · exact fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
        tail counterWidth workIndex
  have hdispatchFlip :
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex (control.flip x) =
        control.flip
          (fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
            tail counterWidth tempIndex historyIndex x) := by
    rw [←
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList
        tail counterWidth tempIndex historyIndex (control.flip x)]
    rw [EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
      gates control
      (fullRoundWorkSelectedDispatchGates_bitDisjoint_counterCarryIn
        tail counterWidth tempIndex historyIndex) x]
    rw [
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList
        tail counterWidth tempIndex historyIndex x]
  rw [
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep_eq_flip_run_flip]
  rw [
    fullRoundWorkCounterCarryInControlledSelectedDispatchStep_eq_dispatch_of_control_true
      tail counterWidth tempIndex historyIndex workIndex
      (control.flip x) hcontrolFlip hworkFlip]
  rw [hdispatchFlip]
  simp [EncodedBit.flip_flip, control]

/-- If the counter carry-in latch is true, the false-controlled selected
dispatch is a no-op. -/
theorem
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep_eq_self
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = true) :
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
        tail counterWidth tempIndex historyIndex workIndex x =
      x := by
  let control := fullRoundWorkCounterCarryInBit tail counterWidth
  have hcontrolFlip : control.get (control.flip x) = false := by
    dsimp [control]
    rw [EncodedBit.get_flip_self, hcontrol]
    rfl
  rw [
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep_eq_flip_run_flip]
  rw [
    fullRoundWorkCounterCarryInControlledSelectedDispatchStep_eq_self_of_control_false
      tail counterWidth tempIndex historyIndex workIndex
      (control.flip x) hcontrolFlip]
  simp [EncodedBit.flip_flip, control]

/-- Counter-carry-in-controlled compare-carried odd dispatch over the full-round
workspace. -/
def
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (fullRoundWorkCounterCarryInBit tail counterWidth)
    (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
    (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex)
    (fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryIn
      tail counterWidth comparisonIndex historyIndex)
    (fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryWork
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
      tail counterWidth workIndex)

/-- Step function for the counter-carry-in-controlled compare-carried odd
dispatch. -/
def
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Actual circuit for the counter-carry-in-controlled compare-carried odd
dispatch. -/
def
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The controlled compare-carried circuit realizes its gate-list step. -/
theorem fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatch_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- If the counter carry-in control is false, the controlled compare-carried
odd dispatch is a no-op. -/
theorem
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep_eq_self_of_control_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false) :
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      x := by
  simpa [
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep,
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (fullRoundWorkCounterCarryInBit tail counterWidth)
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
      (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
        tail counterWidth comparisonIndex historyIndex)
      (fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryIn
        tail counterWidth comparisonIndex historyIndex)
      (fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryWork
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
        tail counterWidth workIndex)
      x hcontrol

/-- If the counter carry-in control is true and the carry-work bit is clean, the
controlled compare-carried odd dispatch acts like the original odd dispatch. -/
theorem
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep_eq_dispatch_of_control_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = true)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  calc
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
        EncodedBit.GateSpec.stepList
          (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
            tail counterWidth comparisonIndex historyIndex) x := by
      simpa [
        fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep,
        fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates,
        EncodedBit.GateSpec.controlledListWithWorkStep] using
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
          (fullRoundWorkCounterCarryInBit tail counterWidth)
          (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)
          (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
            tail counterWidth comparisonIndex historyIndex)
          (fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryIn
            tail counterWidth comparisonIndex historyIndex)
          (fullRoundWorkCompareCarriedOddDispatchGates_bitDisjoint_counterCarryWork
            tail counterWidth comparisonIndex historyIndex workIndex)
          (fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
            tail counterWidth workIndex)
          x hcontrol hwork
    _ = fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex x :=
      fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList
        tail counterWidth comparisonIndex historyIndex x

/-- Body dispatcher selected by the latched odd-odd counter carry-in bit.  A
false latch runs the selected even-style dispatch; a true latch runs the
compare-carried odd dispatch. -/
def fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates
    tail counterWidth comparisonIndex historyIndex workIndex ++
  fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates
    tail counterWidth comparisonIndex historyIndex workIndex

/-- Step function for the body dispatcher selected by the latched odd-odd
counter carry-in bit. -/
def fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Actual circuit for the body dispatcher selected by the latched odd-odd
counter carry-in bit. -/
def fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The latched body-dispatch circuit realizes its gate-list step. -/
theorem fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatch_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Gate list that first latches the active-guarded odd-odd selector into the
counter carry-in bit, then routes the selected/compare-carried body from that
latched bit. -/
def fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  fullRoundWorkActiveOddOddSelectorToCounterCarryInGates
    tail counterWidth workIndex ++
  fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates
    tail counterWidth comparisonIndex historyIndex workIndex

/-- Exact physical length of the active-latched selected/compare-carried
dispatcher. -/
theorem
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates_length
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex).length =
      370 * tail + 274 := by
  simp only [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates,
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates,
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates,
    fullRoundWorkCounterCarryInControlledSelectedDispatchGates,
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates,
    fullRoundWorkActiveOddOddSelectorToCounterCarryInGates,
    List.length_append, List.length_cons, List.length_nil,
    EncodedBit.GateSpec.controlledListWithWorkGates_length_eq,
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_length,
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_toffoliMultiplicity_sum,
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_length,
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_toffoliMultiplicity_sum]
  omega

/-- Exact Toffoli coordinate of the active-latched selected/compare-carried
dispatcher. -/
theorem
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      366 * tail + 260 := by
  simp only [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates,
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates,
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates,
    fullRoundWorkCounterCarryInControlledSelectedDispatchGates,
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    fullRoundWorkActiveOddOddSelectorToCounterCarryInGates_toffoliMultiplicity_sum,
    EncodedBit.GateSpec.controlledListWithWorkGates_toffoliMultiplicity_sum,
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_cnotMultiplicity_sum,
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_toffoliMultiplicity_sum,
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_cnotMultiplicity_sum,
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_toffoliMultiplicity_sum,
    EncodedBit.GateSpec.toffoliMultiplicity_x]
  omega

/-- Exact X coordinate of the active-latched dispatcher.  Only the two
false-control conjugation flips contribute X leaves. -/
theorem
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates_xMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex).map
        EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  simp only [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates,
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates,
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates,
    fullRoundWorkCounterCarryInControlledSelectedDispatchGates,
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    fullRoundWorkActiveOddOddSelectorToCounterCarryInGates_xMultiplicity_sum,
    EncodedBit.GateSpec.controlledListWithWorkGates_xMultiplicity_sum,
    EncodedBit.GateSpec.xMultiplicity_x]
  omega

/-- Exact CNOT coordinate of the active-latched dispatcher.  Each controlled
body contributes the X coordinate of its source list. -/
theorem
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ((fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 4 * tail + 12 := by
  simp only [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates,
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates,
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchGates,
    fullRoundWorkCounterCarryInControlledSelectedDispatchGates,
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    fullRoundWorkActiveOddOddSelectorToCounterCarryInGates_cnotMultiplicity_sum,
    EncodedBit.GateSpec.controlledListWithWorkGates_cnotMultiplicity_sum,
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_xMultiplicity_sum,
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_xMultiplicity_sum,
    EncodedBit.GateSpec.cnotMultiplicity_x]
  omega

/-- Step that latches the active-guarded odd-odd selector and then runs the
latched body dispatcher. -/
def fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Actual circuit for latching the active-guarded odd-odd selector before
running the latched selected/compare-carried body dispatcher. -/
def fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The active-guarded latch-then-body circuit realizes its gate-list step. -/
theorem fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatch_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Exact actual Toffoli count of the active-latched dispatcher circuit. -/
theorem
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchProgram_toffoli_count
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
          tail counterWidth comparisonIndex historyIndex workIndex).eventCost =
      366 * tail + 260 := by
  rw [fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates_toffoliMultiplicity_sum
      tail counterWidth comparisonIndex historyIndex workIndex

/-! ## Original-active controlled active body over path/control work -/

/-- Active-body gate list lifted over the explicit path and control-work bits. -/
def fullRoundPathControlWorkActiveBodyGates
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth)) :=
  ((fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)

/-- The lifted active-body gates do not touch the explicit path bit. -/
theorem fullRoundPathControlWorkActiveBodyGates_bitDisjoint_path
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ∀ gate,
      gate ∈ fullRoundPathControlWorkActiveBodyGates
        tail counterWidth comparisonIndex historyIndex workIndex ->
      EncodedBit.GateSpec.bitDisjoint
        (fullRoundPathControlWorkPathBit tail counterWidth) gate := by
  intro gate hgate
  unfold fullRoundPathControlWorkActiveBodyGates at hgate
  rcases List.mem_map.mp hgate with ⟨pathGate, hpathGate, rfl⟩
  rcases List.mem_map.mp hpathGate with ⟨baseGate, _hbaseGate, rfl⟩
  exact
    gateSpecProdLeft_bitDisjoint_prodLeftBit BinaryLabelEncoding.bool
      (fullRoundPathWorkPathBit tail counterWidth)
      (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool baseGate)
      (gateSpecProdLeft_bitDisjoint_prodRightBit
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit baseGate)

/-- The lifted active-body gates do not touch the explicit control-work bit. -/
theorem fullRoundPathControlWorkActiveBodyGates_bitDisjoint_controlWork
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    ∀ gate,
      gate ∈ fullRoundPathControlWorkActiveBodyGates
        tail counterWidth comparisonIndex historyIndex workIndex ->
      EncodedBit.GateSpec.bitDisjoint
        (fullRoundPathControlWorkControlWorkBit tail counterWidth) gate := by
  intro gate hgate
  unfold fullRoundPathControlWorkActiveBodyGates at hgate
  rcases List.mem_map.mp hgate with ⟨pathGate, _hpathGate, rfl⟩
  exact
    gateSpecProdLeft_bitDisjoint_prodRightBit
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit pathGate

/-- The path bit and the control-work bit are distinct. -/
theorem fullRoundPathControlWorkPathBit_controlWorkBit_wire_ne
    (tail counterWidth : Nat) :
    (fullRoundPathControlWorkPathBit tail counterWidth).wire ≠
      (fullRoundPathControlWorkControlWorkBit tail counterWidth).wire :=
  prodLeftBit_prodRightBit_wire_ne
    (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
    BinaryLabelEncoding.bool
    (fullRoundPathWorkPathBit tail counterWidth)
    BinaryLabelEncoding.boolBit

/-- Active body controlled by the explicit original-active path bit. -/
def fullRoundPathControlWorkOriginalActiveControlledBodyGates
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (fullRoundPathControlWorkPathBit tail counterWidth)
    (fullRoundPathControlWorkControlWorkBit tail counterWidth)
    (fullRoundPathControlWorkActiveBodyGates
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundPathControlWorkActiveBodyGates_bitDisjoint_path
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundPathControlWorkActiveBodyGates_bitDisjoint_controlWork
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundPathControlWorkPathBit_controlWorkBit_wire_ne
      tail counterWidth)

/-- Step for the original-active-controlled active body. -/
def fullRoundPathControlWorkOriginalActiveControlledBodyStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundPathControlWorkOriginalActiveControlledBodyGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Base-gate program for the original-active-controlled active body. -/
def fullRoundPathControlWorkOriginalActiveControlledBodyProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundPathControlWorkOriginalActiveControlledBodyGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The original-active-controlled active body is realized by its base-gate
program. -/
theorem fullRoundPathControlWorkOriginalActiveControlledBody_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth)
      (fullRoundPathControlWorkOriginalActiveControlledBodyProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (fullRoundPathControlWorkOriginalActiveControlledBodyGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- If the explicit original-active path bit is false, the controlled active
body is a no-op. -/
theorem
    fullRoundPathControlWorkOriginalActiveControlledBodyStep_eq_self_of_path_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth)
    (hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get x = false) :
    fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      x := by
  simpa [
    fullRoundPathControlWorkOriginalActiveControlledBodyStep,
    fullRoundPathControlWorkOriginalActiveControlledBodyGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
      (fullRoundPathControlWorkPathBit tail counterWidth)
      (fullRoundPathControlWorkControlWorkBit tail counterWidth)
      (fullRoundPathControlWorkActiveBodyGates
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathControlWorkActiveBodyGates_bitDisjoint_path
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathControlWorkActiveBodyGates_bitDisjoint_controlWork
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathControlWorkPathBit_controlWorkBit_wire_ne
        tail counterWidth)
      x hpath

/-- The lifted active-body gate list has the lifted full-round active-body
semantic action and preserves the explicit path/control bits. -/
theorem fullRoundPathControlWorkActiveBodyStep_eq_lifted
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (fullRoundPathControlWorkActiveBodyGates
          tail counterWidth comparisonIndex historyIndex workIndex) x =
      liftFullRoundWorkStepToPathControlWork tail.succ counterWidth
        (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex) x := by
  unfold fullRoundPathControlWorkActiveBodyGates
    liftFullRoundWorkStepToPathControlWork
    liftFullRoundPathWorkStepToControlWork
    liftFullRoundWorkStepToPathWork
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
  unfold registersWithFullRoundPathControlWorkEncoding
    registersWithFullRoundPathWorkEncoding
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  rw [EncodedBit.GateSpec.stepList_prodLeft]

/-- If the explicit original-active path bit is true and the control-work bit
is clean, the controlled active body reduces to the lifted active-body gate
list. -/
theorem
    fullRoundPathControlWorkOriginalActiveControlledBodyStep_eq_activeBody_of_path_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth)
    (hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get x = true)
    (hwork :
      (fullRoundPathControlWorkControlWorkBit tail counterWidth).get x =
        false) :
    fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      EncodedBit.GateSpec.stepList
        (fullRoundPathControlWorkActiveBodyGates
          tail counterWidth comparisonIndex historyIndex workIndex) x := by
  simpa [
    fullRoundPathControlWorkOriginalActiveControlledBodyStep,
    fullRoundPathControlWorkOriginalActiveControlledBodyGates,
    EncodedBit.GateSpec.controlledListWithWorkStep] using
    EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
      (fullRoundPathControlWorkPathBit tail counterWidth)
      (fullRoundPathControlWorkControlWorkBit tail counterWidth)
      (fullRoundPathControlWorkActiveBodyGates
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathControlWorkActiveBodyGates_bitDisjoint_path
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathControlWorkActiveBodyGates_bitDisjoint_controlWork
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathControlWorkPathBit_controlWorkBit_wire_ne
        tail counterWidth)
      x hpath hwork

/-- If the explicit original-active path bit is true and the control-work bit
is clean, the controlled active body has the lifted full-round active-body
semantic action. -/
theorem
    fullRoundPathControlWorkOriginalActiveControlledBodyStep_eq_lifted_of_path_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth)
    (hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get x = true)
    (hwork :
      (fullRoundPathControlWorkControlWorkBit tail counterWidth).get x =
        false) :
    fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      liftFullRoundWorkStepToPathControlWork tail.succ counterWidth
        (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex) x := by
  rw [
    fullRoundPathControlWorkOriginalActiveControlledBodyStep_eq_activeBody_of_path_true
      tail counterWidth comparisonIndex historyIndex workIndex x hpath hwork]
  exact
    fullRoundPathControlWorkActiveBodyStep_eq_lifted
      tail counterWidth comparisonIndex historyIndex workIndex x

/-- Semantic reverse of the active-guarded latch-then-body gate list.  This
uncompute leg reverses the same wire-addressed program that created the
active-guarded counter carry-in latch. -/
def fullRoundWorkActiveOddOddLatchThenBodyUncomputeStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex).reverse

/-- Reversing the active-guarded latch-then-body gate list uncomputes a
forward run. -/
theorem fullRoundWorkActiveOddOddLatchThenBody_uncompute_leftInverse
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    fullRoundWorkActiveOddOddLatchThenBodyUncomputeStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      x := by
  unfold fullRoundWorkActiveOddOddLatchThenBodyUncomputeStep
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
  exact
    EncodedBit.GateSpec.stepList_reverse_stepList
      (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
        tail counterWidth comparisonIndex historyIndex workIndex) x

/-- The same reversed gate list is also a right inverse for the forward
active-guarded latch-then-body semantic step. -/
theorem fullRoundWorkActiveOddOddLatchThenBody_compute_rightInverse
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundWorkActiveOddOddLatchThenBodyUncomputeStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      x := by
  unfold fullRoundWorkActiveOddOddLatchThenBodyUncomputeStep
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
  simpa using
    EncodedBit.GateSpec.stepList_reverse_stepList
      (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
        tail counterWidth comparisonIndex historyIndex workIndex).reverse x

/-- Actual reversed circuit for the active-guarded latch-then-body uncompute
leg. -/
def fullRoundWorkActiveOddOddLatchThenBodyUncomputeProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
    tail counterWidth comparisonIndex historyIndex workIndex).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)

/-- The reversed active-guarded latch-then-body program realizes the uncompute
semantic step. -/
theorem fullRoundWorkActiveOddOddLatchThenBody_uncompute_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkActiveOddOddLatchThenBodyUncomputeProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundWorkActiveOddOddLatchThenBodyUncomputeStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  UnitaryCircuit.Realizes.dagger_of_rightInverse
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatch_realizes
      tail counterWidth comparisonIndex historyIndex workIndex)
    (by
      rw [fullRoundWorkActiveOddOddLatchThenBodyUncomputeProgram,
        UnitaryCircuit.dagger_matrix]
      exact Unitary.star_eq_inv _)
    (fullRoundWorkActiveOddOddLatchThenBody_compute_rightInverse
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- With a false latch and clean carry-work bit, the latched body dispatcher
reduces to the selected branch-code/history/aux-shift dispatch. -/
theorem
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_selected
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  let selected :=
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail counterWidth comparisonIndex historyIndex
  have hfirst :
      fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x =
        selected x :=
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep_eq_dispatch
      tail counterWidth comparisonIndex historyIndex workIndex x hcontrol hwork
  have hcontrolSelected :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get (selected x) =
        false := by
    dsimp [selected]
    rw [fullRoundWorkSelectedDispatchStep_get_counterCarryIn]
    exact hcontrol
  unfold fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates
  rw [EncodedBit.GateSpec.stepList_append]
  change fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep
      tail counterWidth comparisonIndex historyIndex workIndex
      (fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x) =
    selected x
  rw [hfirst]
  exact
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep_eq_self_of_control_false
      tail counterWidth comparisonIndex historyIndex workIndex
      (selected x) hcontrolSelected

/-- With a true latch and clean carry-work bit, the latched body dispatcher
reduces to the compare-carried odd dispatch. -/
theorem
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_compareCarried
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = true)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  have hfirst :
      fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x =
        x :=
    fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep_eq_self
      tail counterWidth comparisonIndex historyIndex workIndex x hcontrol
  unfold fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates
  rw [EncodedBit.GateSpec.stepList_append]
  change fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep
      tail counterWidth comparisonIndex historyIndex workIndex
      (fullRoundWorkCounterCarryInFalseControlledSelectedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x) =
    fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
      tail counterWidth comparisonIndex historyIndex x
  rw [hfirst]
  exact
    fullRoundWorkCounterCarryInControlledCompareCarriedOddDispatchStep_eq_dispatch_of_control_true
      tail counterWidth comparisonIndex historyIndex workIndex x hcontrol hwork

/-- With a clean carry-work bit, the latched body dispatcher preserves the
counter carry-in latch. -/
theorem
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_get_counterCarryIn_of_clean_work
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x := by
  cases hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x
  · rw [
      fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_selected
        tail counterWidth comparisonIndex historyIndex workIndex
        x hcontrol hwork]
    rw [fullRoundWorkSelectedDispatchStep_get_counterCarryIn]
    exact hcontrol
  · rw [
      fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_compareCarried
        tail counterWidth comparisonIndex historyIndex workIndex
        x hcontrol hwork]
    rw [fullRoundWorkCompareCarriedDispatchStep_get_counterCarryIn]
    exact hcontrol

/-- With a clean carry-work bit, the latched body dispatcher restores that
carry-work bit to clean. -/
theorem
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_get_counterCarryWork_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      false := by
  cases hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x
  · rw [
      fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_selected
        tail counterWidth comparisonIndex historyIndex workIndex
        x hcontrol hwork]
    rw [fullRoundWorkSelectedDispatchStep_get_counterCarryWork]
    exact hwork
  · rw [
      fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_compareCarried
        tail counterWidth comparisonIndex historyIndex workIndex
        x hcontrol hwork]
    rw [fullRoundWorkCompareCarriedDispatchStep_get_counterCarryWork]
    exact hwork

/-- The active-guarded latch-then-body dispatcher is the latched body
dispatcher applied to the output of the active-guarded odd-odd latch step. -/
theorem
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
          tail counterWidth workIndex x) := by
  unfold fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchGates
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
  rw [EncodedBit.GateSpec.stepList_append]

/-- Starting from clean counter carry-in and carry-work bits, the
active-guarded latch-then-body wrapper leaves the counter carry-in latch equal
to `active && u[0] && v[0]`. -/
theorem
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep_get_counterCarryIn_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      ((fullRoundWorkActiveBit tail counterWidth).get x &&
        (coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 &&
        (coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1) := by
  rw [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  rw [
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_get_counterCarryIn_of_clean_work
  ]
  · exact
      fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_get_control_clean
        tail counterWidth workIndex x hcontrol hwork
  · exact
      fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_get_counterCarryWork_clean
        tail counterWidth workIndex x hwork

/-- Starting from clean counter carry-work, the active-guarded latch-then-body
wrapper restores the dispatcher carry-work bit to clean. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_get_counterCarryWork_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      false := by
  rw [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  exact
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_get_counterCarryWork_clean
      tail counterWidth comparisonIndex historyIndex workIndex
      (fullRoundWorkActiveOddOddSelectorToCounterCarryInStep
        tail counterWidth workIndex x)
      (fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_get_counterCarryWork_clean
        tail counterWidth workIndex x hwork)

/-- If the active guard is false, active-guarded latch-then-body reduces to
the selected branch-code/history/aux-shift dispatch. -/
theorem fullRoundWorkActiveOddOddLatchThenBodyStep_eq_selected_of_inactive
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : (fullRoundWorkActiveBit tail counterWidth).get x = false)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  rw [
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_eq_self_of_active_false
      tail counterWidth workIndex x hactive hwork]
  exact
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_selected
      tail counterWidth comparisonIndex historyIndex workIndex x
      hcontrol hwork

/-- If the active guard is false and the selected-dispatch scratch work is
clean, the active-guarded latch-then-body dispatcher is a no-op. -/
theorem fullRoundWorkActiveOddOddLatchThenBodyStep_eq_self_of_inactive_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : (fullRoundWorkActiveBit tail counterWidth).get x = false)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x.1 = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x.1 = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth comparisonIndex).get
          x.1 = false) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      x := by
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get x.1 = false := by
    simpa [fullRoundWorkActiveBit, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_selected_of_inactive
      tail counterWidth comparisonIndex historyIndex workIndex x
      hactive hcontrol hwork]
  exact
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_self_of_active_false_clean
      tail counterWidth comparisonIndex historyIndex x hscratchA hscratchB
      htemp hactiveCoeff

/-- If low `u` is false, active-guarded latch-then-body reduces to the
selected branch-code/history/aux-shift dispatch. -/
theorem fullRoundWorkActiveOddOddLatchThenBodyStep_eq_selected_of_uLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  rw [
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_eq_self_of_uLow_false
      tail counterWidth workIndex x huLow hwork]
  exact
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_selected
      tail counterWidth comparisonIndex historyIndex workIndex x
      hcontrol hwork

/-- If low `u` is true and low `v` is false, active-guarded latch-then-body
reduces to the selected branch-code/history/aux-shift dispatch. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_selected_of_uLow_true_vLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (_huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  rw [
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_eq_self_of_vLow_false
      tail counterWidth workIndex x hvLow]
  exact
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_selected
      tail counterWidth comparisonIndex historyIndex workIndex x
      hcontrol hwork

/-- In the active odd-odd branch, active-guarded latch-then-body equals the
compare-carried body with the counter carry-in latch flipped. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_compareCarried_of_active_lsb_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : (fullRoundWorkActiveBit tail counterWidth).get x = true)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex x) := by
  let control := fullRoundWorkCounterCarryInBit tail counterWidth
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  have hcontrolFlip : control.get (control.flip x) = true := by
    dsimp [control]
    rw [EncodedBit.get_flip_self, hcontrol]
    rfl
  have hworkFlip : work.get (control.flip x) = false := by
    dsimp [work, control]
    rw [EncodedBit.get_flip_of_wire_ne
      (fullRoundWorkCounterCarryInBit tail counterWidth)
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)]
    · exact hwork
    · exact fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
        tail counterWidth workIndex
  rw [
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  rw [
    fullRoundWorkActiveOddOddSelectorToCounterCarryInStep_eq_flip_of_active_lsb_true
      tail counterWidth workIndex x hactive huLow hvLow hwork]
  rw [
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_compareCarried
      tail counterWidth comparisonIndex historyIndex workIndex
      (control.flip x) hcontrolFlip hworkFlip]
  exact
    fullRoundWorkCompareCarriedDispatchStep_flip_counterCarryIn
      tail counterWidth comparisonIndex historyIndex x

/-- Gate list that first latches the original odd-odd selector into the
counter carry-in bit, then routes the selected/compare-carried body from that
latched bit. -/
def fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchGates
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)) :=
  fullRoundWorkOddOddSelectorToCounterCarryInGates tail counterWidth ++
  fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchGates
    tail counterWidth comparisonIndex historyIndex workIndex

/-- Step that latches the original odd-odd selector and then runs the
latched body dispatcher. -/
def fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Actual circuit for latching the original odd-odd selector before running
the latched selected/compare-carried body dispatcher. -/
def fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The latch-then-body circuit realizes its gate-list semantic step. -/
theorem fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatch_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Semantic reverse of the latch-then-body gate list.  This is the uncompute
leg used to clean the odd-odd counter carry-in latch by reversing the same
wire-addressed program, rather than by recomputing the mutated branch
predicate. -/
def fullRoundWorkOddOddLatchThenBodyUncomputeStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchGates
      tail counterWidth comparisonIndex historyIndex workIndex).reverse

/-- Reversing the latch-then-body gate list uncomputes a forward run. -/
theorem fullRoundWorkOddOddLatchThenBody_uncompute_leftInverse
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    fullRoundWorkOddOddLatchThenBodyUncomputeStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      x := by
  unfold fullRoundWorkOddOddLatchThenBodyUncomputeStep
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
  exact
    EncodedBit.GateSpec.stepList_reverse_stepList
      (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchGates
        tail counterWidth comparisonIndex historyIndex workIndex) x

/-- The same reversed gate list is also a right inverse for the forward
latch-then-body semantic step. -/
theorem fullRoundWorkOddOddLatchThenBody_compute_rightInverse
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundWorkOddOddLatchThenBodyUncomputeStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      x := by
  unfold fullRoundWorkOddOddLatchThenBodyUncomputeStep
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
  simpa using
    EncodedBit.GateSpec.stepList_reverse_stepList
      (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchGates
        tail counterWidth comparisonIndex historyIndex workIndex).reverse x

/-- Actual reversed circuit for the latch-then-body uncompute leg. -/
def fullRoundWorkOddOddLatchThenBodyUncomputeProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
    tail counterWidth comparisonIndex historyIndex workIndex).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)

/-- The reversed latch-then-body program realizes the uncompute semantic step.
-/
theorem fullRoundWorkOddOddLatchThenBody_uncompute_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkOddOddLatchThenBodyUncomputeProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundWorkOddOddLatchThenBodyUncomputeStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  UnitaryCircuit.Realizes.dagger_of_rightInverse
    (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatch_realizes
      tail counterWidth comparisonIndex historyIndex workIndex)
    (by
      rw [fullRoundWorkOddOddLatchThenBodyUncomputeProgram,
        UnitaryCircuit.dagger_matrix]
      exact Unitary.star_eq_inv _)
    (fullRoundWorkOddOddLatchThenBody_compute_rightInverse
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The latch-then-body dispatcher is the latched body dispatcher applied to
the output of the odd-odd latch step. -/
theorem
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth) :
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundWorkOddOddSelectorToCounterCarryInStep
          tail counterWidth x) := by
  unfold fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchGates
    fullRoundWorkOddOddSelectorToCounterCarryInStep
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep
  rw [EncodedBit.GateSpec.stepList_append]

/-- Starting from clean counter carry-in and carry-work bits, latch-then-body
leaves the counter carry-in latch equal to the original odd-odd predicate. -/
theorem
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep_get_counterCarryIn_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      ((coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 &&
        (coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1) := by
  rw [
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  have hbody :=
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_get_counterCarryIn_of_clean_work
  rw [hbody]
  · exact
      fullRoundWorkOddOddSelectorToCounterCarryInStep_get_control_clean
        tail counterWidth x hcontrol
  · rw [fullRoundWorkOddOddSelectorToCounterCarryInStep_get_counterCarryWork]
    exact hwork

/-- Starting from clean counter carry-in and carry-work bits, latch-then-body
restores the dispatcher carry-work bit to clean. -/
theorem
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep_get_counterCarryWork_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (_hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false) :
    (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex x) =
      false := by
  rw [
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  exact
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_get_counterCarryWork_clean
      tail counterWidth comparisonIndex historyIndex workIndex
      (fullRoundWorkOddOddSelectorToCounterCarryInStep
        tail counterWidth x)
      (by
        rw [fullRoundWorkOddOddSelectorToCounterCarryInStep_get_counterCarryWork]
        exact hwork)

/-- If low `u` is false, latch-then-body reduces to the selected dispatch.
The odd-odd latch is a no-op in this branch. -/
theorem fullRoundWorkOddOddLatchThenBodyStep_eq_selected_of_uLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  rw [
    fullRoundWorkOddOddSelectorToCounterCarryInStep_eq_self_of_uLow_false
      tail counterWidth x huLow]
  exact
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_selected
      tail counterWidth comparisonIndex historyIndex workIndex x
      hcontrol hwork

/-- If low `u` is true and low `v` is false, latch-then-body reduces to the
selected dispatch.  The odd-odd latch is still a no-op in this branch. -/
theorem fullRoundWorkOddOddLatchThenBodyStep_eq_selected_of_uLow_true_vLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (_huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  rw [
    fullRoundWorkOddOddSelectorToCounterCarryInStep_eq_self_of_vLow_false
      tail counterWidth x hvLow]
  exact
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_selected
      tail counterWidth comparisonIndex historyIndex workIndex x
      hcontrol hwork

/-- In the odd-odd branch, latch-then-body equals the compare-carried body with
the counter carry-in latch flipped. -/
theorem fullRoundWorkOddOddLatchThenBodyStep_eq_flip_compareCarried_of_lsb_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true) :
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex x) := by
  let control := fullRoundWorkCounterCarryInBit tail counterWidth
  let work := fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex
  have hcontrolFlip : control.get (control.flip x) = true := by
    dsimp [control]
    rw [EncodedBit.get_flip_self, hcontrol]
    rfl
  have hworkFlip : work.get (control.flip x) = false := by
    dsimp [work, control]
    rw [EncodedBit.get_flip_of_wire_ne
      (fullRoundWorkCounterCarryInBit tail counterWidth)
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex)]
    · exact hwork
    · exact fullRoundWorkCounterCarryIn_counterCarryWork_wire_ne
        tail counterWidth workIndex
  rw [
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep_eq_body_after_latch]
  rw [
    fullRoundWorkOddOddSelectorToCounterCarryInStep_eq_flip_of_lsb_true
      tail counterWidth x huLow hvLow]
  rw [
    fullRoundWorkCounterCarryInSelectedOrCompareCarriedDispatchStep_eq_compareCarried
      tail counterWidth comparisonIndex historyIndex workIndex
      (control.flip x) hcontrolFlip hworkFlip]
  exact
    fullRoundWorkCompareCarriedDispatchStep_flip_counterCarryIn
      tail counterWidth comparisonIndex historyIndex x

/-- Semantic selected-branch wrapper for a nonzero active Kaliski round over
coefficient-adder work.  It dispatches to the existing fixed-branch active
family using the concrete low `u`, low `v`, and staged comparison readout bits.
This is not itself an actual circuit for data-dependent gate-level control. -/
def coeffWorkKaliskiActiveSelectedBranchRoundStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithCoeffAdderWork tail.succ counterWidth ->
      RegistersWithCoeffAdderWork tail.succ counterWidth :=
  fun x =>
    coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x) x

/-- The semantic selected-branch wrapper reads the same concrete selector bits
as the coefficient-work branch-signal bridge. -/
theorem coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_from_readout_bits
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        comparisonIndex historyIndex
        (Branch.fromCircuitSignals
          ((coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x)
          ((coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x)
          ((coeffAdderCompareBit tail.succ counterWidth).get x)) x := by
  simp [coeffWorkKaliskiActiveSelectedBranchRoundStep,
    Branch.fromCoeffWorkSignals_eq_from_branch_bits]

/-- If the concrete low `u` readout is false, the selected active wrapper
reduces to the fixed `uEven` branch family. -/
theorem coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uEven_of_u_lsb_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hu :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        comparisonIndex historyIndex Branch.uEven x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_from_readout_bits]
  simp [hu]

/-- If the concrete low `u` readout is true and low `v` readout is false, the
selected active wrapper reduces to the fixed `vEven` branch family. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vEven_of_u_lsb_true_v_lsb_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hu :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hv :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        comparisonIndex historyIndex Branch.vEven x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_from_readout_bits]
  simp [hu, hv]

/-- If both concrete low readouts are true and the staged comparison readout is
true, the selected active wrapper reduces to the fixed `uGreater` branch
family. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uGreater_of_odd_odd_compare_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hu :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hv :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = true) :
    coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        comparisonIndex historyIndex Branch.uGreater x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_from_readout_bits]
  simp [hu, hv, hcompare]

/-- If both concrete low readouts are true and the staged comparison readout is
false, the selected active wrapper reduces to the fixed `vLe` branch family. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vLe_of_odd_odd_compare_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hu :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hv :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false) :
    coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        comparisonIndex historyIndex Branch.vLe x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_from_readout_bits]
  simp [hu, hv, hcompare]

/-- The explicit active-branch family specializes to the concrete `uEven`
branch wrapper. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_uEven
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    coeffWorkKaliskiActiveBranchRoundStep
        n counterWidth uIndex vIndex comparisonIndex historyIndex Branch.uEven =
      coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth uIndex historyIndex :=
  rfl

/-- The explicit active-branch family specializes to the concrete `vEven`
branch wrapper. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_vEven
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    coeffWorkKaliskiActiveBranchRoundStep
        n counterWidth uIndex vIndex comparisonIndex historyIndex Branch.vEven =
      coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth uIndex vIndex historyIndex :=
  rfl

/-- The explicit active-branch family specializes to the corrected `uGreater`
branch wrapper. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_uGreater
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    coeffWorkKaliskiActiveBranchRoundStep
        n counterWidth uIndex vIndex comparisonIndex historyIndex
        Branch.uGreater =
      coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth comparisonIndex historyIndex :=
  rfl

/-- The explicit active-branch family specializes to the corrected `vLe`
branch wrapper. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_vLe
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    coeffWorkKaliskiActiveBranchRoundStep
        n counterWidth uIndex vIndex comparisonIndex historyIndex Branch.vLe =
      coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth comparisonIndex historyIndex :=
  rfl

/-- In the explicit active-round family, the `uEven` branch preserves the
active flag. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_active_uEven
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uEven x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkKaliskiActiveBranchRoundStep,
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_active]
  rw [coeffWorkActiveScratchBToHistoryStep_get_active]
  exact coeffWorkUEvenBranchCodeToScratchStep_get_active
    n counterWidth uIndex x

/-- In the explicit active-round family, the `vEven` branch preserves the
active flag. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_active_vEven
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vEven x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkKaliskiActiveBranchRoundStep,
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_active]
  rw [coeffWorkActiveScratchBToHistoryStep_get_active]
  exact coeffWorkVEvenBranchCodeToScratchStep_get_active
    n counterWidth uIndex vIndex x

/-- In the explicit active-round family, the corrected `uGreater` branch
preserves the active flag. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_active_uGreater
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uGreater x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkKaliskiActiveBranchRoundStep,
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_active]
  exact coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_active
    n counterWidth comparisonIndex historyIndex x

/-- In the explicit active-round family, the corrected `vLe` branch preserves
the active flag. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_active_vLe
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vLe x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkKaliskiActiveBranchRoundStep,
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_active]
  exact coeffWorkVLeSubAddBranchCodeToScratchStep_get_active
    n counterWidth comparisonIndex historyIndex x

/-- The explicit active-round family preserves the active flag for every
branch selection. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_active
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex branch x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  cases branch with
  | uEven =>
      exact coeffWorkKaliskiActiveBranchRoundStep_get_active_uEven
        n counterWidth uIndex vIndex comparisonIndex historyIndex x
  | vEven =>
      exact coeffWorkKaliskiActiveBranchRoundStep_get_active_vEven
        n counterWidth uIndex vIndex comparisonIndex historyIndex x
  | uGreater =>
      exact coeffWorkKaliskiActiveBranchRoundStep_get_active_uGreater
        n counterWidth uIndex vIndex comparisonIndex historyIndex x
  | vLe =>
      exact coeffWorkKaliskiActiveBranchRoundStep_get_active_vLe
        n counterWidth uIndex vIndex comparisonIndex historyIndex x

/-- In the explicit active-round family, the `uEven` branch restores clean
compare. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_compare_uEven_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uEven x) =
      false := by
  rw [coeffWorkKaliskiActiveBranchRoundStep]
  exact
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare_clean
      n counterWidth uIndex historyIndex x hcompare

/-- In the explicit active-round family, the `vEven` branch restores clean
compare. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_compare_vEven_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vEven x) =
      false := by
  rw [coeffWorkKaliskiActiveBranchRoundStep]
  exact
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare_clean
      n counterWidth uIndex vIndex historyIndex x hcompare

/-- In the explicit active-round family, the corrected `uGreater` branch
preserves the staged `v < u` comparison predicate. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_compare_uGreater_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uGreater
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkKaliskiActiveBranchRoundStep]
  exact
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_compare_clean
      n counterWidth comparisonIndex historyIndex x work hscratchA hcompare
      hfinal

/-- In the explicit active-round family, the corrected `vLe` branch preserves
the staged comparison predicate. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_compare_vLe_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vLe
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkKaliskiActiveBranchRoundStep]
  exact
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_compare_clean
      n counterWidth comparisonIndex historyIndex x work hscratchA hcompare
      hfinal

/-- The selected active wrapper preserves the active flag for the branch
chosen by the concrete coefficient-work selector bits. -/
theorem coeffWorkKaliskiActiveSelectedBranchRoundStep_get_active
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderActiveBit tail.succ counterWidth).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      (coeffAdderActiveBit tail.succ counterWidth).get x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_active tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x) x

/-- The selected active wrapper restores clean compare in the concrete
`uEven` case. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_compare_uEven_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    (coeffAdderCompareBit tail.succ counterWidth).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      false := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uEven_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_compare_uEven_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex x hcompare

/-- The selected active wrapper restores clean compare in the concrete
`vEven` case. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_compare_vEven_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    (coeffAdderCompareBit tail.succ counterWidth).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      false := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vEven_of_u_lsb_true_v_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_compare_vEven_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex x hcompare

/-- In the explicit active-round family, the `uEven` branch leaves the selected
history slot unchanged under clean compare/scratchB assumptions. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_history_uEven_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uEven x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
      n counterWidth uIndex historyIndex x hcompare hscratchB

/-- In the explicit active-round family, the `vEven` branch writes the selected
history slot under the active `u`-odd/`v`-even condition. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_history_vEven_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vEven x) =
      ((coeffAdderHistoryBit n counterWidth historyIndex).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderUBit n counterWidth uIndex).get x &&
          !(coeffAdderVBit n counterWidth vIndex).get x)) := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
      n counterWidth uIndex vIndex historyIndex x hcompare hscratchB

/-- In the explicit active-round family, the corrected `uGreater` branch
preserves the selector's branch-history toggle through subtract/add staging and
auxiliary shift dispatch. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_history_uGreater_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : comparisonIndex.val + 1 = n) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uGreater
          ((x, cleanComparisonWork n), work)) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val))) := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_history_clean
      n counterWidth comparisonIndex historyIndex x work hscratchA hcompare
      hscratchB hfinal

/-- In the explicit active-round family, the corrected `vLe` branch leaves the
selected history slot unchanged. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_history_vLe_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vLe
          ((x, cleanComparisonWork n), work)) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_history_clean
      n counterWidth comparisonIndex historyIndex x work hscratchB

/-- In the explicit active-round family, every branch preserves all history
slots except the selected target slot. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_historyBit_of_ne
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (target observed : Fin (2 * n)) (branch : Branch)
    (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex target branch x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  cases branch with
  | uEven =>
      simpa [coeffWorkKaliskiActiveBranchRoundStep] using
        coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
          n counterWidth uIndex target observed hne x
  | vEven =>
      simpa [coeffWorkKaliskiActiveBranchRoundStep] using
        coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
          n counterWidth uIndex vIndex target observed hne x
  | uGreater =>
      simpa [coeffWorkKaliskiActiveBranchRoundStep] using
        coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_historyBit_of_ne
          n counterWidth comparisonIndex target observed hne x
  | vLe =>
      simpa [coeffWorkKaliskiActiveBranchRoundStep] using
        coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_historyBit_of_ne
          n counterWidth comparisonIndex target observed hne x

/-- The semantic selected active-branch wrapper preserves every history slot
except the selected target slot. -/
theorem coeffWorkKaliskiActiveSelectedBranchRoundStep_get_historyBit_of_ne
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (target observed : Fin (2 * tail.succ)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex target x) =
      (coeffAdderHistoryBit tail.succ counterWidth observed).get x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_historyBit_of_ne
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex target observed
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x) hne x

/-- The explicit active-branch full-round wrapper preserves every history slot
except the selected target slot while carrying padding-counter work unchanged. -/
theorem fullRoundWorkKaliskiActiveBranchRoundStep_get_historyBit_of_ne
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (target observed : Fin (2 * n)) (branch : Branch)
    (hne : target ≠ observed)
    (x : RegistersWithFullRoundWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (fullRoundWorkKaliskiActiveBranchRoundStep n counterWidth uIndex
          vIndex comparisonIndex target branch x).1 =
      (coeffAdderHistoryBit n counterWidth observed).get x.1 := by
  rw [fullRoundWorkKaliskiActiveBranchRoundStep]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_historyBit_of_ne
      n counterWidth uIndex vIndex comparisonIndex target observed branch hne
      x.1

/-- In the explicit active-round family, the `uEven` branch preserves the
staged scratchA equation under clean compare. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_scratchA_uEven_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uEven x) =
      ((coeffAdderScratchABit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          !(coeffAdderUBit n counterWidth uIndex).get x)) := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
      n counterWidth uIndex historyIndex x hcompare

/-- In the explicit active-round family, the `uEven` branch preserves scratchB
under clean compare. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_scratchB_uEven_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uEven x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
      n counterWidth uIndex historyIndex x hcompare

/-- In the explicit active-round family, the `vEven` branch preserves scratchA
under clean compare. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_scratchA_vEven_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vEven x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
      n counterWidth uIndex vIndex historyIndex x hcompare

/-- In the explicit active-round family, the `vEven` branch preserves the
staged scratchB equation under clean compare. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_scratchB_vEven_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vEven x) =
      ((coeffAdderScratchBBit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderUBit n counterWidth uIndex).get x &&
          !(coeffAdderVBit n counterWidth vIndex).get x)) := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
      n counterWidth uIndex vIndex historyIndex x hcompare

/-- In the explicit active-round family, the `uEven` branch preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_carryIn_uEven
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uEven x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryIn
      n counterWidth uIndex historyIndex x

/-- In the explicit active-round family, the `uEven` branch preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_carryWorkBit_uEven
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.uEven x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryWorkBit
      n counterWidth uIndex historyIndex workBit x

/-- In the explicit active-round family, the `vEven` branch preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_carryIn_vEven
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vEven x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryIn
      n counterWidth uIndex vIndex historyIndex x

/-- In the explicit active-round family, the `vEven` branch preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkKaliskiActiveBranchRoundStep_get_carryWorkBit_vEven
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n)) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
          comparisonIndex historyIndex Branch.vEven x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryWorkBit
      n counterWidth uIndex vIndex historyIndex workBit x

/-- The selected active wrapper preserves the staged scratchA equation in the
concrete `uEven` case. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_scratchA_uEven_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    (coeffAdderScratchABit tail.succ counterWidth).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      ((coeffAdderScratchABit tail.succ counterWidth).get x ^^
        ((coeffAdderActiveBit tail.succ counterWidth).get x &&
          !(coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x)) := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uEven_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_scratchA_uEven_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex x hcompare

/-- The selected active wrapper preserves scratchB in the concrete `uEven`
case. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_scratchB_uEven_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    (coeffAdderScratchBBit tail.succ counterWidth).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      (coeffAdderScratchBBit tail.succ counterWidth).get x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uEven_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_scratchB_uEven_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex x hcompare

/-- The selected active wrapper preserves scratchA in the concrete `vEven`
case. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_scratchA_vEven_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    (coeffAdderScratchABit tail.succ counterWidth).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      (coeffAdderScratchABit tail.succ counterWidth).get x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vEven_of_u_lsb_true_v_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_scratchA_vEven_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex x hcompare

/-- The selected active wrapper preserves the staged scratchB equation in the
concrete `vEven` case. -/
theorem
    coeffWorkKaliskiActiveSelectedBranchRoundStep_get_scratchB_vEven_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    (coeffAdderScratchBBit tail.succ counterWidth).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      ((coeffAdderScratchBBit tail.succ counterWidth).get x ^^
        ((coeffAdderActiveBit tail.succ counterWidth).get x &&
          (coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          !(coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x)) := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vEven_of_u_lsb_true_v_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_scratchB_vEven_clean
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex x hcompare

/-- The selected active wrapper preserves the coefficient-adder carry-in flag
in the concrete `uEven` case. -/
theorem coeffWorkKaliskiActiveSelectedBranchRoundStep_get_carryIn_uEven
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uEven_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_carryIn_uEven
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex x

/-- The selected active wrapper preserves each coefficient-adder carry-work
bit in the concrete `uEven` case. -/
theorem coeffWorkKaliskiActiveSelectedBranchRoundStep_get_carryWorkBit_uEven
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workBit : Fin ((tail.succ + 1) - 1))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit).get
        x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_uEven_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_carryWorkBit_uEven
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex workBit x

/-- The selected active wrapper preserves the coefficient-adder carry-in flag
in the concrete `vEven` case. -/
theorem coeffWorkKaliskiActiveSelectedBranchRoundStep_get_carryIn_vEven
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vEven_of_u_lsb_true_v_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_carryIn_vEven
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex x

/-- The selected active wrapper preserves each coefficient-adder carry-work
bit in the concrete `vEven` case. -/
theorem coeffWorkKaliskiActiveSelectedBranchRoundStep_get_carryWorkBit_vEven
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workBit : Fin ((tail.succ + 1) - 1))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit).get
        (coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
          comparisonIndex historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit).get
        x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_vEven_of_u_lsb_true_v_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkKaliskiActiveBranchRoundStep_get_carryWorkBit_vEven
      tail.succ counterWidth
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      (WireAddress.littleEndianWire (0 : Fin tail.succ))
      comparisonIndex historyIndex workBit x

/-- The explicit active-round family writes `u := u / 2` in the `uEven`
branch under the clean active/even assumptions. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_u_uEven_wordHalf_of_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hu : (coeffAdderUBit tail.succ counterWidth uIndex).get x = false)
    (hlsb : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.uEven x).1.1.u =
      wordHalf tail.succ x.1.1.u := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_u_wordHalf_of_clean
      tail counterWidth uIndex historyIndex x hcompare hscratchA hactive hu
      hlsb

/-- The explicit active-round family writes `s := 2 * s` in the `uEven`
branch under the clean active/even/top-bit assumptions. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_uEven_wordDouble_of_msb_false
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hu : (coeffAdderUBit n counterWidth uIndex).get x = false)
    (hmsb : x.1.1.sCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uEven x).1.1.sCoeff =
      wordDouble (n + 1) x.1.1.sCoeff := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_sCoeff_wordDouble_of_msb_false
      n counterWidth uIndex historyIndex x hcompare hscratchA hactive hu hmsb

/-- The explicit active-round family writes `v := v / 2` in the `vEven`
branch under the clean active/even assumptions. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_v_vEven_wordHalf_of_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hlsb : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.vEven x).1.1.v =
      wordHalf tail.succ x.1.1.v := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_v_wordHalf_of_clean
      tail counterWidth uIndex vIndex historyIndex x hcompare hscratchA
      hactive hlsb

/-- The explicit active-round family writes `r := 2 * r` in the `vEven`
branch under the clean active/top-bit assumptions. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_vEven_wordDouble_of_msb_false
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hmsb : x.1.1.rCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vEven x).1.1.rCoeff =
      wordDouble (n + 1) x.1.1.rCoeff := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_rCoeff_wordDouble_of_msb_false
      n counterWidth uIndex vIndex historyIndex x hcompare hscratchA hactive
      hmsb

/-- The explicit active-round family writes `u := (u - v) / 2` in the
corrected `uGreater` branch under the clean assumptions. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_u_uGreater_wordHalf_sub_of_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hgreater : decide (x.v.val < x.u.val) = true)
    (hwork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.uGreater
        ((x, cleanComparisonWork tail.succ), work)).1.1.u =
      wordHalf tail.succ (x.u - x.v) := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_u_wordHalf_sub_of_clean
      tail counterWidth comparisonIndex historyIndex x work hscratchA hcompare
      hactive hfinal hgreater hwork hlsb

/-- The explicit active-round family preserves `r := r + s` in the corrected
`uGreater` branch through the paired shift group. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_uGreater_add_of_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hfinal : comparisonIndex.val + 1 = n)
    (hgreater : decide (x.v.val < x.u.val) = true)
    (hcarry :
      (liftedCoeffAdderCarryInBit n counterWidth).get
        ((x, cleanComparisonWork n), work) = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uGreater
        ((x, cleanComparisonWork n), work)).1.1.rCoeff =
      x.rCoeff + x.sCoeff := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_rCoeff_add_of_clean
      n counterWidth comparisonIndex historyIndex x work hscratchA hcompare
      hactive hfinal hgreater hcarry hwork

/-- The explicit active-round family writes `s := 2 * s` in the corrected
`uGreater` branch under the clean active/top-bit assumptions. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_uGreater_wordDouble_of_msb_false
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hfinal : comparisonIndex.val + 1 = n)
    (hgreater : decide (x.v.val < x.u.val) = true)
    (hmsb : x.sCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.uGreater
        ((x, cleanComparisonWork n), work)).1.1.sCoeff =
      wordDouble (n + 1) x.sCoeff := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_sCoeff_wordDouble_of_msb_false
      n counterWidth comparisonIndex historyIndex x work hscratchA hcompare
      hactive hfinal hgreater hmsb

/-- The explicit active-round family writes `v := (v - u) / 2` in the
corrected `vLe` branch under the clean assumptions. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_v_vLe_wordHalf_sub_of_clean
    (tail counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hwork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth uIndex
        vIndex comparisonIndex historyIndex Branch.vLe
        ((x, cleanComparisonWork tail.succ), work)).1.1.v =
      wordHalf tail.succ (x.v - x.u) := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_v_wordHalf_sub_of_clean
      tail counterWidth comparisonIndex historyIndex x work hscratchA hactive
      hwork hlsb

/-- The explicit active-round family preserves `s := s + r` in the corrected
`vLe` branch through the paired shift group. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_sCoeff_vLe_add_of_clean
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hcarry :
      (liftedCoeffAdderCarryInBit n counterWidth).get
        ((x, cleanComparisonWork n), work) = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vLe
        ((x, cleanComparisonWork n), work)).1.1.sCoeff =
      x.sCoeff + x.rCoeff := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_sCoeff_add_of_clean
      n counterWidth comparisonIndex historyIndex x work hscratchA hactive
      hcarry hwork

/-- The explicit active-round family writes `r := 2 * r` in the corrected
`vLe` branch under the clean active/top-bit assumptions. -/
theorem
    coeffWorkKaliskiActiveBranchRoundStep_get_rCoeff_vLe_wordDouble_of_msb_false
    (n counterWidth : Nat) (uIndex vIndex comparisonIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hmsb : x.rCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkKaliskiActiveBranchRoundStep n counterWidth uIndex vIndex
        comparisonIndex historyIndex Branch.vLe
        ((x, cleanComparisonWork n), work)).1.1.rCoeff =
      wordDouble (n + 1) x.rCoeff := by
  simpa [coeffWorkKaliskiActiveBranchRoundStep] using
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_rCoeff_wordDouble_of_msb_false
      n counterWidth comparisonIndex historyIndex x work hscratchA hactive
      hmsb

/-- Scaled unit inverse used by the Montgomery correction route.  The scale
factor is kept explicit so a source-level Montgomery endpoint is not silently
identified with the raw staged inverse. -/
def scaledInverseResidue {p : Nat} (scale : ZMod p) (u : (ZMod p)ˣ) :
    ZMod p :=
  scale * inverseResidue u

theorem scaledInverseResidue_mul_input {p : Nat}
    (scale : ZMod p) (u : (ZMod p)ˣ) :
    scaledInverseResidue scale u * (u : ZMod p) = scale := by
  have hunit : inverseResidue u * (u : ZMod p) = 1 := by
    simp [inverseResidue]
  calc
    scaledInverseResidue scale u * (u : ZMod p)
        = scale * (inverseResidue u * (u : ZMod p)) := by
      rw [scaledInverseResidue]
      ring
    _ = scale * 1 := by
      rw [hunit]
    _ = scale := by
      ring

theorem eq_scaledInverseResidue_of_mul_input_eq {p : Nat}
    (r scale : ZMod p) (u : (ZMod p)ˣ)
    (hmul : r * (u : ZMod p) = scale) :
    r = scaledInverseResidue scale u := by
  have hunit : (u : ZMod p) * inverseResidue u = 1 := by
    simp [inverseResidue]
  calc
    r = r * 1 := by
      ring
    _ = r * ((u : ZMod p) * inverseResidue u) := by
      rw [hunit]
    _ = (r * (u : ZMod p)) * inverseResidue u := by
      ring
    _ = scale * inverseResidue u := by
      rw [hmul]
    _ = scaledInverseResidue scale u := by
      rfl

/-- Remove an explicit multiplicative scale from a residue.  The inverse-scale
law is a premise because this operation is meaningful over the actual modulus
`p`, independently of any register width. -/
def unscaleResidue {p : Nat}
    (inverseScale residue : ZMod p) : ZMod p :=
  inverseScale * residue

theorem unscaleResidue_scaledInverseResidue {p : Nat}
    (inverseScale scale : ZMod p) (u : (ZMod p)ˣ)
    (hinverseScale : inverseScale * scale = 1) :
    unscaleResidue inverseScale (scaledInverseResidue scale u) =
      inverseResidue u := by
  calc
    unscaleResidue inverseScale (scaledInverseResidue scale u) =
        (inverseScale * scale) * inverseResidue u := by
      simp only [unscaleResidue, scaledInverseResidue]
      ring
    _ = 1 * inverseResidue u := by
      rw [hinverseScale]
    _ = inverseResidue u := by
      ring

/-- The positive Montgomery scale as a unit modulo an odd actual modulus.
Oddness makes `2^(2n)` coprime to `p`; the width parameter `n` is used only in
the exponent and is not identified with the modulus. -/
def montgomeryScaleUnit (p n : Nat) (hodd : Odd p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime (2 ^ (2 * n))
    (Nat.Coprime.pow_left (2 * n) hodd.coprime_two_left)

/-- Canonical inverse of the positive Montgomery scale modulo an odd modulus.
-/
def inverseMontgomeryScale (p n : Nat) (hodd : Odd p) : ZMod p :=
  ↑((montgomeryScaleUnit p n hodd)⁻¹)

theorem inverseMontgomeryScale_mul_scale
    (p n : Nat) (hodd : Odd p) :
    inverseMontgomeryScale p n hodd * (2 : ZMod p) ^ (2 * n) = 1 := by
  have hscale :
      ((montgomeryScaleUnit p n hodd : (ZMod p)ˣ) : ZMod p) =
        (2 : ZMod p) ^ (2 * n) := by
    simp [montgomeryScaleUnit]
  rw [← hscale]
  change
    (((montgomeryScaleUnit p n hodd)⁻¹ : (ZMod p)ˣ) : ZMod p) *
        ((montgomeryScaleUnit p n hodd : (ZMod p)ˣ) : ZMod p) = 1
  have hunit :
      (montgomeryScaleUnit p n hodd)⁻¹ * montgomeryScaleUnit p n hodd =
        (1 : (ZMod p)ˣ) :=
    inv_mul_cancel _
  simpa only [Units.val_mul, Units.val_one] using congrArg Units.val hunit

/-- Overwrite-style staged compute step for an explicitly scaled inverse. -/
def stageWithScaledInverse {p : Nat}
    (scale : ZMod p) (s : StageState p) : StageState p where
  input := s.input
  target := s.target
  inverseScratch := scaledInverseResidue scale s.input
  flag := s.flag

theorem stageWithScaledInverse_eq_computeInverse_of_scale_eq_one {p : Nat}
    (s : StageState p) (scale : ZMod p) (hscale : scale = 1) :
    stageWithScaledInverse scale s = StageState.computeInverse s := by
  cases s with
  | mk input target inverseScratch flag =>
    change
      ({ input := input
         target := target
         inverseScratch := scaledInverseResidue scale input
         flag := flag } : StageState p) =
        { input := input
          target := target
          inverseScratch := inverseResidue input
          flag := flag }
    rw [hscale]
    simp [scaledInverseResidue]

/-- In the source terminating case, the active-flag X atom matches the source
round's active-field projection.  This is still the flag-only slice; the
counter incrementer remains a separate gate-level obligation. -/
theorem activeFlagToggleStep_active_eq_source_round_active_of_terminated
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hv : x.v.val = 0) :
    (activeFlagToggleStep n counterWidth x).active =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).active := by
  have hsourceActive :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).active =
        true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).v =
        0 := by
    simpa [RoundState.fromRegisters] using hv
  rw [RoundState.round_active_terminated_active
    (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)
    hsourceActive hsourceV]
  exact activeFlagToggleStep_active_of_active n counterWidth x hactive

/-- In the source terminating case, the active-flag X atom preserves the same
`u` field as the source round. -/
theorem activeFlagToggleStep_u_eq_source_round_u_of_terminated
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hv : x.v.val = 0) :
    (activeFlagToggleStep n counterWidth x).u.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).u := by
  have hsourceActive :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).active =
        true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).v =
        0 := by
    simpa [RoundState.fromRegisters] using hv
  rw [RoundState.round_active_terminated
    (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)
    hsourceActive hsourceV]
  simpa [RoundState.fromRegisters] using
    congrArg Fin.val (activeFlagToggleStep_u n counterWidth x)

/-- In the source terminating case, the active-flag X atom preserves the same
`v` field as the source round. -/
theorem activeFlagToggleStep_v_eq_source_round_v_of_terminated
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hv : x.v.val = 0) :
    (activeFlagToggleStep n counterWidth x).v.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).v := by
  have hsourceActive :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).active =
        true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).v =
        0 := by
    simpa [RoundState.fromRegisters] using hv
  rw [RoundState.round_active_terminated
    (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)
    hsourceActive hsourceV]
  simpa [RoundState.fromRegisters] using
    congrArg Fin.val (activeFlagToggleStep_v n counterWidth x)

/-- In the source terminating case, the active-flag X atom preserves the same
`s` coefficient field as the source round. -/
theorem activeFlagToggleStep_sCoeff_eq_source_round_sCoeff_of_terminated
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hv : x.v.val = 0) :
    (activeFlagToggleStep n counterWidth x).sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).sCoeff := by
  have hsourceActive :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).active =
        true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).v =
        0 := by
    simpa [RoundState.fromRegisters] using hv
  rw [RoundState.round_active_terminated
    (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)
    hsourceActive hsourceV]
  simpa [RoundState.fromRegisters] using
    congrArg Fin.val (activeFlagToggleStep_sCoeff n counterWidth x)

/-- In the source terminating case, the active-flag X atom preserves the same
`r` coefficient field as the source round. -/
theorem activeFlagToggleStep_rCoeff_eq_source_round_rCoeff_of_terminated
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hv : x.v.val = 0) :
    (activeFlagToggleStep n counterWidth x).rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).rCoeff := by
  have hsourceActive :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).active =
        true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).v =
        0 := by
    simpa [RoundState.fromRegisters] using hv
  rw [RoundState.round_active_terminated
    (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)
    hsourceActive hsourceV]
  simpa [RoundState.fromRegisters] using
    congrArg Fin.val (activeFlagToggleStep_rCoeff n counterWidth x)

/-- Flag-only terminating bridge: the active-flag X atom, paired with the
semantic padding-count increment, matches the source terminating round.  The
newer counter-work wrapper below adds the concrete padding-counter endpoint;
this bridge only records the source `paddingSteps + 1` projection. -/
theorem activeFlagToggleStep_fromRegisters_eq_source_round_of_terminated
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hv : x.v.val = 0) :
    RoundState.fromRegisters n counterWidth
        (activeFlagToggleStep n counterWidth x)
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps) := by
  have hsourceActive :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).active =
        true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps).v =
        0 := by
    simpa [RoundState.fromRegisters] using hv
  rw [RoundState.round_active_terminated
    (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)
    hsourceActive hsourceV]
  simp [RoundState.fromRegisters, activeFlagToggleStep_active_of_active,
    activeFlagToggleStep_u, activeFlagToggleStep_v, activeFlagToggleStep_sCoeff,
    activeFlagToggleStep_rCoeff, hactive]

/-- Under the concrete `v`-zero guard, the active-flag X atom matches the
source terminating round's active-field projection. -/
theorem activeFlagToggleStep_active_eq_source_round_active_of_vZeroGuard
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hguard : vZeroGuard n counterWidth x) :
    (activeFlagToggleStep n counterWidth x).active =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).active :=
  activeFlagToggleStep_active_eq_source_round_active_of_terminated
    n counterWidth kaliskiSteps paddingSteps x hactive
    (v_zero_of_vZeroGuard n counterWidth x hguard)

/-- Under the concrete `v`-zero guard, the active-flag X atom preserves the
same `u` field as the source terminating round. -/
theorem activeFlagToggleStep_u_eq_source_round_u_of_vZeroGuard
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hguard : vZeroGuard n counterWidth x) :
    (activeFlagToggleStep n counterWidth x).u.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).u :=
  activeFlagToggleStep_u_eq_source_round_u_of_terminated
    n counterWidth kaliskiSteps paddingSteps x hactive
    (v_zero_of_vZeroGuard n counterWidth x hguard)

/-- Under the concrete `v`-zero guard, the active-flag X atom preserves the
same `v` field as the source terminating round. -/
theorem activeFlagToggleStep_v_eq_source_round_v_of_vZeroGuard
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hguard : vZeroGuard n counterWidth x) :
    (activeFlagToggleStep n counterWidth x).v.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).v :=
  activeFlagToggleStep_v_eq_source_round_v_of_terminated
    n counterWidth kaliskiSteps paddingSteps x hactive
    (v_zero_of_vZeroGuard n counterWidth x hguard)

/-- Under the concrete `v`-zero guard, the active-flag X atom preserves the
same `s` coefficient field as the source terminating round. -/
theorem activeFlagToggleStep_sCoeff_eq_source_round_sCoeff_of_vZeroGuard
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hguard : vZeroGuard n counterWidth x) :
    (activeFlagToggleStep n counterWidth x).sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).sCoeff :=
  activeFlagToggleStep_sCoeff_eq_source_round_sCoeff_of_terminated
    n counterWidth kaliskiSteps paddingSteps x hactive
    (v_zero_of_vZeroGuard n counterWidth x hguard)

/-- Under the concrete `v`-zero guard, the active-flag X atom preserves the
same `r` coefficient field as the source terminating round. -/
theorem activeFlagToggleStep_rCoeff_eq_source_round_rCoeff_of_vZeroGuard
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hguard : vZeroGuard n counterWidth x) :
    (activeFlagToggleStep n counterWidth x).rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)).rCoeff :=
  activeFlagToggleStep_rCoeff_eq_source_round_rCoeff_of_terminated
    n counterWidth kaliskiSteps paddingSteps x hactive
    (v_zero_of_vZeroGuard n counterWidth x hguard)

/-- Under the concrete `v`-zero guard, the flag-only active atom plus the
semantic padding-count increment matches the source terminating round. -/
theorem activeFlagToggleStep_fromRegisters_eq_source_round_of_vZeroGuard
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hguard : vZeroGuard n counterWidth x) :
    RoundState.fromRegisters n counterWidth
        (activeFlagToggleStep n counterWidth x)
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps) :=
  activeFlagToggleStep_fromRegisters_eq_source_round_of_terminated
    n counterWidth kaliskiSteps paddingSteps x hactive
    (v_zero_of_vZeroGuard n counterWidth x hguard)

/-- Under the concrete `v`-zero guard, the terminating counter-mode wrapper
matches the source terminating round while also incrementing the concrete
padding counter in its own register endpoint. -/
theorem
    terminatingCounterModeWithWorkStep_fromRegisters_eq_source_round_of_vZeroGuard
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth)
    (hactive : x.active = true) (hguard : vZeroGuard n counterWidth x) :
    RoundState.fromRegisters n counterWidth
        (terminatingCounterModeWithWorkStep n counterWidth
          (x, cleanCounterIncrementWork counterWidth)).1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps) := by
  rw [terminatingCounterModeWithWorkStep_cleanEndpoint n counterWidth x
    hactive]
  rw [← activeFlagToggleStep_fromRegisters_eq_source_round_of_vZeroGuard
    n counterWidth kaliskiSteps paddingSteps x hactive hguard]
  simp [RoundState.fromRegisters, activeFlagToggleStep_u,
    activeFlagToggleStep_v, activeFlagToggleStep_sCoeff,
    activeFlagToggleStep_rCoeff, activeFlagToggleStep_active_of_active,
    hactive]

/-- The detector-counter terminating counter-mode step matches the source
terminating round on the fields observed by `RoundState.fromRegisters`. -/
theorem
    detectorCounterTerminatingCounterModeStep_fromRegisters_eq_source_round_of_v_zero
    (n counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n)
    (hactive : x.active = true) (hvZero : x.v.val = 0) :
    RoundState.fromRegisters n counterWidth
        (detectorCounterTerminatingCounterModeStep n counterWidth
          ((x, cmpWork), cleanCounterIncrementWork counterWidth)).1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters n counterWidth x
          kaliskiSteps paddingSteps) := by
  let input : RegistersWithDetectorCounterWork n counterWidth :=
    ((x, cmpWork), cleanCounterIncrementWork counterWidth)
  have hsourceActive :
      (RoundState.fromRegisters n counterWidth x
        kaliskiSteps paddingSteps).active = true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters n counterWidth x
        kaliskiSteps paddingSteps).v = 0 := by
    simpa [RoundState.fromRegisters] using hvZero
  rw [RoundState.round_active_terminated
    (RoundState.fromRegisters n counterWidth x kaliskiSteps paddingSteps)
    hsourceActive hsourceV]
  have hu :
      (detectorCounterTerminatingCounterModeStep n counterWidth
          input).1.1.u.val = x.u.val := by
    simpa [input] using
      congrArg Fin.val
        (detectorCounterTerminatingCounterModeStep_u
          n counterWidth input)
  have hv :
      (detectorCounterTerminatingCounterModeStep n counterWidth
          input).1.1.v.val = x.v.val := by
    simpa [input] using
      congrArg Fin.val
        (detectorCounterTerminatingCounterModeStep_v
          n counterWidth input)
  have hs :
      (detectorCounterTerminatingCounterModeStep n counterWidth
          input).1.1.sCoeff.val = x.sCoeff.val := by
    simpa [input] using
      congrArg Fin.val
        (detectorCounterTerminatingCounterModeStep_sCoeff
          n counterWidth input)
  have hr :
      (detectorCounterTerminatingCounterModeStep n counterWidth
          input).1.1.rCoeff.val = x.rCoeff.val := by
    simpa [input] using
      congrArg Fin.val
        (detectorCounterTerminatingCounterModeStep_rCoeff
          n counterWidth input)
  have hactiveOut :
      (detectorCounterTerminatingCounterModeStep n counterWidth
          input).1.1.active = false := by
    simpa [input] using
      detectorCounterTerminatingCounterModeStep_active_of_active
        n counterWidth x cmpWork (cleanCounterIncrementWork counterWidth)
        hactive
  simp [RoundState.fromRegisters, input, hu, hv, hs, hr, hactiveOut,
    hactive]

/-- A clean detector pass only changes compare, which is ignored by
`RoundState.fromRegisters`. -/
theorem detectorCounterVZeroDetectorStep_fromRegisters_eq_self_clean
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (work : CounterIncrementWork counterWidth) :
    RoundState.fromRegisters tail.succ counterWidth
        (detectorCounterVZeroDetectorStep tail.succ counterWidth
          ((x, cleanComparisonWork tail.succ), work)).1.1
        kaliskiSteps paddingSteps =
      RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps := by
  rw [detectorCounterVZeroDetectorStep_cleanEndpoint]
  simp [RoundState.fromRegisters]

/-- In the concrete `v = 0` case, the complete detector-gated terminating
counter-mode wrapper matches the source terminating round on the source-state
projection. -/
theorem
    detectorGatedTerminatingCounterModeWithWorkStep_fromRegisters_eq_source_round_of_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0) :
    RoundState.fromRegisters tail.succ counterWidth
        (detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
          ((x, cleanComparisonWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [detectorGatedTerminatingCounterModeWithWorkStep_eq_terminating_path_of_v_zero
    tail counterWidth x (cleanCounterIncrementWork counterWidth)
    hcompare hvZero]
  rw [detectorCounterVZeroDetectorStep_cleanEndpoint]
  let xDetected : Registers tail.succ counterWidth :=
    { x with compare := x.compare ^^ decide (x.v.val = 0) }
  let y : RegistersWithDetectorCounterWork tail.succ counterWidth :=
    detectorCounterTerminatingCounterModeStep tail.succ counterWidth
      ((xDetected, cleanComparisonWork tail.succ),
        cleanCounterIncrementWork counterWidth)
  have hcmpClean : y.1.2 = cleanComparisonWork tail.succ := by
    simpa [y] using
      detectorCounterTerminatingCounterModeStep_comparisonWork_clean
        tail.succ counterWidth xDetected
        (cleanCounterIncrementWork counterWidth)
  have houter :
      RoundState.fromRegisters tail.succ counterWidth
          (detectorCounterVZeroDetectorStep tail.succ counterWidth y).1.1
          kaliskiSteps (paddingSteps + 1) =
        RoundState.fromRegisters tail.succ counterWidth y.1.1
          kaliskiSteps (paddingSteps + 1) := by
    have hyClean : y = ((y.1.1, cleanComparisonWork tail.succ), y.2) := by
      cases hY : y with
      | mk state counterWork =>
          cases hState : state with
          | mk regs cmpWork =>
              rw [hY, hState] at hcmpClean
              change cmpWork = cleanComparisonWork tail.succ at hcmpClean
              subst cmpWork
              simp
    rw [hyClean]
    simpa using
      detectorCounterVZeroDetectorStep_fromRegisters_eq_self_clean
        tail counterWidth kaliskiSteps (paddingSteps + 1) y.1.1 y.2
  have hterm :
      RoundState.fromRegisters tail.succ counterWidth y.1.1
          kaliskiSteps (paddingSteps + 1) =
        RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth xDetected
            kaliskiSteps paddingSteps) := by
    simpa [y] using
      detectorCounterTerminatingCounterModeStep_fromRegisters_eq_source_round_of_v_zero
        tail.succ counterWidth kaliskiSteps paddingSteps xDetected
        (cleanComparisonWork tail.succ)
        (by simp [xDetected, hactive])
        (by simpa [xDetected] using hvZero)
  have hdetectedSource :
      RoundState.fromRegisters tail.succ counterWidth xDetected
          kaliskiSteps paddingSteps =
        RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps := by
    simp [xDetected, RoundState.fromRegisters]
  calc
    RoundState.fromRegisters tail.succ counterWidth
        (detectorCounterVZeroDetectorStep tail.succ counterWidth y).1.1
        kaliskiSteps (paddingSteps + 1)
        = RoundState.fromRegisters tail.succ counterWidth y.1.1
            kaliskiSteps (paddingSteps + 1) := houter
    _ = RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth xDetected
            kaliskiSteps paddingSteps) := hterm
    _ = RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x
            kaliskiSteps paddingSteps) := by rw [hdetectedSource]

/-- In the concrete `v ≠ 0` case, the complete detector-gated terminating
counter-mode wrapper is a no-op on the source-state projection and does not
consume a padding round. -/
theorem
    detectorGatedTerminatingCounterModeWithWorkStep_fromRegisters_eq_self_of_v_nonzero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hvNonzero : x.v.val ≠ 0) :
    RoundState.fromRegisters tail.succ counterWidth
        (detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
          ((x, cleanComparisonWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1
        kaliskiSteps paddingSteps =
      RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps := by
  rw [detectorGatedTerminatingCounterModeWithWorkStep_cleanEndpoint_of_v_nonzero
    tail counterWidth x hcompare hvNonzero]

/-- In the concrete `v = 0` case, the detector-gated terminating counter-mode
wrapper lifted to the full fixed-round workspace matches the source
terminating round on the source-state projection and preserves the
coefficient-adder work. -/
theorem
    fullRoundWorkTerminatingStep_fromRegisters_eq_source_round_of_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkTerminatingStep tail counterWidth
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [fullRoundWorkTerminatingStep]
  change
    RoundState.fromRegisters tail.succ counterWidth
        (detectorGatedTerminatingCounterModeWithWorkStep tail counterWidth
          ((x, cleanComparisonWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)
  exact
    detectorGatedTerminatingCounterModeWithWorkStep_fromRegisters_eq_source_round_of_v_zero
      tail counterWidth kaliskiSteps paddingSteps x hcompare hactive hvZero

/-- In the concrete `v ≠ 0` case, the detector-gated terminating counter-mode
wrapper lifted to the full fixed-round workspace is a no-op on the source-state
projection and does not consume a padding round. -/
theorem
    fullRoundWorkTerminatingStep_fromRegisters_eq_self_of_v_nonzero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hvNonzero : x.v.val ≠ 0) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkTerminatingStep tail counterWidth
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps paddingSteps =
      RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps := by
  rw [fullRoundWorkTerminatingStep_cleanEndpoint_of_v_nonzero
    tail counterWidth x hcompare hvNonzero]

/-- Inactive padding mode lifted over comparison work and counter-increment
work, preserving comparison work. -/
def detectorCounterInactivePaddingStep
    (n counterWidth : Nat) :
    RegistersWithDetectorCounterWork n counterWidth ->
      RegistersWithDetectorCounterWork n counterWidth :=
  fun x =>
    let y := counterIncrementWithWorkStep n counterWidth (x.1.1, x.2)
    ((y.1, x.1.2), y.2)

/-- Actual inactive-padding circuit over comparison and counter-increment
work. -/
def detectorCounterInactivePaddingProgram
    (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithDetectorCounterWorkEncoding n counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinaryMiddle
    (leftWidth := (registerEncoding n counterWidth).width)
    (middleWidth := (comparisonWorkEncoding n).width)
    (rightWidth := (counterIncrementWorkEncoding counterWidth).width)
    (counterIncrementWithWorkProgram n counterWidth)

/-- The inactive-padding circuit realizes the lifted counter increment. -/
theorem detectorCounterInactivePadding_realizes
    (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithDetectorCounterWorkEncoding n counterWidth)
      (detectorCounterInactivePaddingProgram n counterWidth)
      (detectorCounterInactivePaddingStep n counterWidth) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.onBinaryMiddle
      (left := registerEncoding n counterWidth)
      (middle := comparisonWorkEncoding n)
      (right := counterIncrementWorkEncoding counterWidth)
      (counterIncrementWithWork_realizes n counterWidth))
  intro x
  rcases x with ⟨⟨regs, comparisonWork⟩, counterWork⟩
  rfl

/-- On inactive clean inputs, the explicit detector-counter inactive-padding
gate list increments the padding counter and restores its clean work. -/
theorem detectorCounterInactivePaddingGateStep_cleanEndpoint_of_inactive
    (n counterWidth : Nat)
    (x : Registers n counterWidth) (cmpWork : ComparisonWork n)
    (hactive : x.active = false) :
    detectorCounterInactivePaddingGateStep n counterWidth
        ((x, cmpWork), cleanCounterIncrementWork counterWidth) =
      (({ x with counter := wordIncrement counterWidth x.counter }, cmpWork),
        cleanCounterIncrementWork counterWidth) := by
  let activeInput : Registers n counterWidth := { x with active := true }
  have hterm :=
    detectorCounterTerminatingCounterModeStep_cleanEndpoint
      n counterWidth activeInput cmpWork rfl
  have hnorm :
      detectorCounterTerminatingCounterModeStep n counterWidth
          ((activeInput, cmpWork), cleanCounterIncrementWork counterWidth) =
        detectorCounterInactivePaddingGateStep n counterWidth
          ((x, cmpWork), cleanCounterIncrementWork counterWidth) := by
    rw [detectorCounterTerminatingCounterModeStep_eq_cleanCarrySum_after_active]
    have hx : { x with active := false } = x := by
      cases x
      simp at hactive
      simp [hactive]
    dsimp [activeInput]
    simp only [Bool.not_true]
    rw [hx]
    simp [detectorCounterInactivePaddingGateStep,
      detectorCounterInactivePaddingGates,
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep]
  rw [hnorm] at hterm
  simpa [activeInput, hactive] using hterm

/-- Inactive padding mode lifted to the full fixed-round workspace.  On clean
counter work, the endpoint below increments the concrete padding counter and
preserves the comparison and coefficient-adder work. -/
def fullRoundWorkInactivePaddingStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    let y := counterIncrementWithWorkStep tail.succ counterWidth
      (x.1.1.1, x.2)
    (((y.1, x.1.1.2), x.1.2), y.2)

/-- Actual inactive-padding circuit under the standard full-round work
encoding. -/
def fullRoundWorkInactivePaddingProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinaryMiddle
    (leftWidth :=
      (registersWithComparisonWorkEncoding tail.succ counterWidth).width)
    (middleWidth := (coeffAdderWorkEncoding tail.succ).width)
    (rightWidth := (counterIncrementWorkEncoding counterWidth).width)
    (detectorCounterInactivePaddingProgram tail.succ counterWidth)

/-- The standard-layout inactive-padding circuit realizes its semantic step. -/
theorem fullRoundWorkInactivePadding_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkInactivePaddingProgram tail counterWidth)
      (fullRoundWorkInactivePaddingStep tail counterWidth) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.onBinaryMiddle
      (left := registersWithComparisonWorkEncoding tail.succ counterWidth)
      (middle := coeffAdderWorkEncoding tail.succ)
      (right := counterIncrementWorkEncoding counterWidth)
      (detectorCounterInactivePadding_realizes tail.succ counterWidth))
  intro x
  rcases x with ⟨⟨⟨regs, comparisonWork⟩, coeffWork⟩, counterWork⟩
  rfl

/-- Full-round comparison-work carry bit in the standard full-round workspace. -/
def fullRoundWorkComparisonCarryBit
    (tail counterWidth : Nat) (bit : Fin tail.succ) :
    EncodedBit (registersWithFullRoundWorkEncoding tail.succ counterWidth) :=
  liftCoeffAdderStateBitToFullRoundWork tail counterWidth
    (coeffAdderComparisonCarryBit tail.succ counterWidth bit)

/-- Explicit inactive-padding gate-list action lifted to the full fixed-round
workspace while preserving coefficient-adder work. -/
def fullRoundWorkInactivePaddingGateStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    let y := detectorCounterInactivePaddingGateStep
      tail.succ counterWidth (x.1.1, x.2)
    (((y.1.1, y.1.2), x.1.2), y.2)

/-- Actual inactive-padding gate-list circuit after lifting it to the full
fixed-round workspace. -/
def fullRoundWorkInactivePaddingGateProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinaryMiddle
    (leftWidth :=
      (registersWithComparisonWorkEncoding tail.succ counterWidth).width)
    (middleWidth := (coeffAdderWorkEncoding tail.succ).width)
    (rightWidth := (counterIncrementWorkEncoding counterWidth).width)
    (detectorCounterInactivePaddingGateProgram tail.succ counterWidth)

/-- The lifted inactive-padding gate-list circuit realizes its semantic
step. -/
theorem fullRoundWorkInactivePaddingGate_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkInactivePaddingGateProgram tail counterWidth)
      (fullRoundWorkInactivePaddingGateStep tail counterWidth) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.onBinaryMiddle
      (left := registersWithComparisonWorkEncoding tail.succ counterWidth)
      (middle := coeffAdderWorkEncoding tail.succ)
      (right := counterIncrementWorkEncoding counterWidth)
      (detectorCounterInactivePaddingGate_realizes
        tail.succ counterWidth))
  intro x
  rcases x with ⟨⟨⟨regs, comparisonWork⟩, coeffWork⟩, counterWork⟩
  rfl

/-- Active-false-controlled inactive padding lifted to the full fixed-round
workspace while preserving coefficient-adder work. -/
def fullRoundWorkActiveFalseControlledInactivePaddingStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    let y :=
      detectorCounterActiveFalseControlledInactivePaddingStep
        tail counterWidth (x.1.1, x.2)
    (((y.1.1, y.1.2), x.1.2), y.2)

/-- Actual active-false-controlled inactive-padding circuit after lifting it
to the full fixed-round workspace. -/
def fullRoundWorkActiveFalseControlledInactivePaddingProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  UnitaryCircuit.onBinaryMiddle
    (leftWidth :=
      (registersWithComparisonWorkEncoding tail.succ counterWidth).width)
    (middleWidth := (coeffAdderWorkEncoding tail.succ).width)
    (rightWidth := (counterIncrementWorkEncoding counterWidth).width)
    (detectorCounterActiveFalseControlledInactivePaddingProgram
      tail counterWidth)

/-- The lifted active-false-controlled circuit realizes its semantic step. -/
theorem fullRoundWorkActiveFalseControlledInactivePadding_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkActiveFalseControlledInactivePaddingProgram
        tail counterWidth)
      (fullRoundWorkActiveFalseControlledInactivePaddingStep
        tail counterWidth) := by
  apply UnitaryCircuit.Realizes.congrStep
    (UnitaryCircuit.Realizes.onBinaryMiddle
      (left := registersWithComparisonWorkEncoding tail.succ counterWidth)
      (middle := coeffAdderWorkEncoding tail.succ)
      (right := counterIncrementWorkEncoding counterWidth)
      (detectorCounterActiveFalseControlledInactivePadding_realizes
        tail counterWidth))
  intro x
  rcases x with ⟨⟨⟨regs, comparisonWork⟩, coeffWork⟩, counterWork⟩
  rfl

/-! ## Original-active controlled route over path/control work -/

/-- Active-false inactive-padding wrapper lifted over path/control work. -/
def fullRoundPathControlWorkActiveFalseInactivePaddingStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  liftFullRoundWorkStepToPathControlWork tail.succ counterWidth
    (fullRoundWorkActiveFalseControlledInactivePaddingStep tail counterWidth)

/-- Actual path/control-work-lifted inactive-padding circuit. -/
def fullRoundPathControlWorkActiveFalseInactivePaddingProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).width)).toQuantum :=
  liftFullRoundWorkProgramToPathControlWork tail.succ counterWidth
    (fullRoundWorkActiveFalseControlledInactivePaddingProgram
      tail counterWidth)

/-- The path/control-work-lifted inactive-padding circuit realizes its lifted
step. -/
theorem fullRoundPathControlWorkActiveFalseInactivePadding_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
      (fullRoundPathControlWorkActiveFalseInactivePaddingProgram
        tail counterWidth)
      (fullRoundPathControlWorkActiveFalseInactivePaddingStep
        tail counterWidth) :=
  liftFullRoundWorkProgramToPathControlWork_realizes tail.succ counterWidth
    (fullRoundWorkActiveFalseControlledInactivePadding_realizes
      tail counterWidth)

/-- Terminating prefix lifted over path/control work. -/
def fullRoundPathControlWorkTerminatingStep
    (tail counterWidth : Nat) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  liftFullRoundWorkStepToPathControlWork tail.succ counterWidth
    (fullRoundWorkTerminatingStep tail counterWidth)

/-- Actual path/control-work-lifted terminating-prefix circuit. -/
def fullRoundPathControlWorkTerminatingProgram
    (tail counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).width)).toQuantum :=
  liftFullRoundWorkProgramToPathControlWork tail.succ counterWidth
    (fullRoundWorkTerminatingStandardLayoutProgram tail counterWidth)

/-- The path/control-work-lifted terminating circuit realizes its lifted
step. -/
theorem fullRoundPathControlWorkTerminating_realizes
    (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
      (fullRoundPathControlWorkTerminatingProgram tail counterWidth)
      (fullRoundPathControlWorkTerminatingStep tail counterWidth) :=
  liftFullRoundWorkProgramToPathControlWork_realizes tail.succ counterWidth
    (fullRoundWorkTerminatingStandardLayout_realizes tail counterWidth)

/-- Concrete route using explicit original-active path control: latch original
active, run inactive-padding and terminating prefixes, then run the active body
only when the latched original-active path bit is true. -/
def fullRoundPathControlWorkKaliskiRoundControlledStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  fun x =>
    fullRoundPathControlWorkOriginalActiveControlledBodyStep
      tail counterWidth comparisonIndex historyIndex workIndex
      (fullRoundPathControlWorkTerminatingStep tail counterWidth
        (fullRoundPathControlWorkActiveFalseInactivePaddingStep
          tail counterWidth
          (fullRoundPathControlWorkOriginalActiveLatchStep
            tail counterWidth x)))

/-- Base-gate program for the original-active-controlled concrete route. -/
def fullRoundPathControlWorkKaliskiRoundControlledProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).width)).toQuantum :=
  UnitaryCircuit.seq
    (UnitaryCircuit.seq
      (fullRoundPathControlWorkOriginalActiveLatchProgram
        tail counterWidth)
      (UnitaryCircuit.seq
        (fullRoundPathControlWorkActiveFalseInactivePaddingProgram
          tail counterWidth)
        (fullRoundPathControlWorkTerminatingProgram tail counterWidth)))
    (fullRoundPathControlWorkOriginalActiveControlledBodyProgram
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The original-active-controlled concrete route is realized by its composed
base-gate program. -/
theorem fullRoundPathControlWorkKaliskiRoundControlled_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth)
      (fullRoundPathControlWorkKaliskiRoundControlledProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathControlWorkKaliskiRoundControlledStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  UnitaryCircuit.Realizes.seq
    (firstStep := fun x =>
      fullRoundPathControlWorkTerminatingStep tail counterWidth
        (fullRoundPathControlWorkActiveFalseInactivePaddingStep
          tail counterWidth
          (fullRoundPathControlWorkOriginalActiveLatchStep
            tail counterWidth x)))
    (secondStep :=
      fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex)
    (UnitaryCircuit.Realizes.seq
      (firstStep := fullRoundPathControlWorkOriginalActiveLatchStep
        tail counterWidth)
      (secondStep := fun y =>
        fullRoundPathControlWorkTerminatingStep tail counterWidth
          (fullRoundPathControlWorkActiveFalseInactivePaddingStep
            tail counterWidth y))
      (fullRoundPathControlWorkOriginalActiveLatch_realizes
        tail counterWidth)
      (UnitaryCircuit.Realizes.seq
        (firstStep := fullRoundPathControlWorkActiveFalseInactivePaddingStep
          tail counterWidth)
        (secondStep := fullRoundPathControlWorkTerminatingStep tail counterWidth)
        (fullRoundPathControlWorkActiveFalseInactivePadding_realizes
          tail counterWidth)
        (fullRoundPathControlWorkTerminating_realizes tail counterWidth)))
    (fullRoundPathControlWorkOriginalActiveControlledBody_realizes
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Fixed-round schedule view of the original-active-controlled concrete route:
the `roundIndex` selects the corresponding `m_i` history register slot. -/
def fixedRoundPathControlWorkKaliskiRoundStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
    comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
    workIndex

/-- Base-gate program for one fixed-round schedule slot of the path/control-work
concrete route. -/
def fixedRoundPathControlWorkKaliskiRoundProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).width)).toQuantum :=
  fullRoundPathControlWorkKaliskiRoundControlledProgram tail counterWidth
    comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
    workIndex

/-- The fixed-round schedule view of the path/control-work concrete route is
realized by its composed base-gate program. -/
theorem fixedRoundPathControlWorkKaliskiRound_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
      (fixedRoundPathControlWorkKaliskiRoundProgram
        tail counterWidth comparisonIndex roundIndex workIndex)
      (fixedRoundPathControlWorkKaliskiRoundStep
        tail counterWidth comparisonIndex roundIndex workIndex) :=
  fullRoundPathControlWorkKaliskiRoundControlled_realizes tail counterWidth
    comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
    workIndex

/-- Fixed-round schedule of path/control-work concrete one-round steps.  Each
entry uses the corresponding source `m_i` history register slot. -/
def fixedRoundPathControlWorkKaliskiRoundStepSchedule
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List (RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth) :=
  List.ofFn fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
    fixedRoundPathControlWorkKaliskiRoundStep tail counterWidth
      comparisonIndex roundIndex workIndex

@[simp] theorem fixedRoundPathControlWorkKaliskiRoundStepSchedule_length
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (fixedRoundPathControlWorkKaliskiRoundStepSchedule
      tail counterWidth comparisonIndex workIndex).length =
      2 * tail.succ := by
  simp [fixedRoundPathControlWorkKaliskiRoundStepSchedule]
  omega

/-- The `roundIndex`-th fixed-round schedule entry is the path/control-work route
using the matching `m_i` history register slot. -/
theorem fixedRoundPathControlWorkKaliskiRoundStepSchedule_get
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds) :
    (fixedRoundPathControlWorkKaliskiRoundStepSchedule
      tail counterWidth comparisonIndex workIndex).get
        ⟨roundIndex.val, by
          rw [fixedRoundPathControlWorkKaliskiRoundStepSchedule_length]
          exact roundIndex.isLt⟩ =
      fixedRoundPathControlWorkKaliskiRoundStep
        tail counterWidth comparisonIndex roundIndex workIndex := by
  change
    (List.ofFn
      (fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
        fixedRoundPathControlWorkKaliskiRoundStep tail counterWidth
          comparisonIndex roundIndex workIndex)).get
        ⟨roundIndex.val, by
          simp
          omega⟩ =
      fixedRoundPathControlWorkKaliskiRoundStep
        tail counterWidth comparisonIndex roundIndex workIndex
  rw [List.get_ofFn]
  congr 1

/-- Fixed-round schedule of path/control-work concrete one-round programs. -/
def fixedRoundPathControlWorkKaliskiRoundProgramSchedule
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List (UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).width)).toQuantum) :=
  List.ofFn fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
    fixedRoundPathControlWorkKaliskiRoundProgram tail counterWidth
      comparisonIndex roundIndex workIndex

@[simp] theorem fixedRoundPathControlWorkKaliskiRoundProgramSchedule_length
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (fixedRoundPathControlWorkKaliskiRoundProgramSchedule
      tail counterWidth comparisonIndex workIndex).length =
      2 * tail.succ := by
  simp [fixedRoundPathControlWorkKaliskiRoundProgramSchedule]
  omega

/-- The `roundIndex`-th fixed-round program entry is the program for the
matching path/control-work one-round route. -/
theorem fixedRoundPathControlWorkKaliskiRoundProgramSchedule_get
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds) :
    (fixedRoundPathControlWorkKaliskiRoundProgramSchedule
      tail counterWidth comparisonIndex workIndex).get
        ⟨roundIndex.val, by
          rw [fixedRoundPathControlWorkKaliskiRoundProgramSchedule_length]
          exact roundIndex.isLt⟩ =
      fixedRoundPathControlWorkKaliskiRoundProgram
        tail counterWidth comparisonIndex roundIndex workIndex := by
  change
    (List.ofFn
      (fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
        fixedRoundPathControlWorkKaliskiRoundProgram tail counterWidth
          comparisonIndex roundIndex workIndex)).get
        ⟨roundIndex.val, by
          simp
          omega⟩ =
      fixedRoundPathControlWorkKaliskiRoundProgram
        tail counterWidth comparisonIndex roundIndex workIndex
  rw [List.get_ofFn]
  congr 1

/-- The fixed-round program and step schedules are related pointwise by the
one-round path/control-work realization theorem. -/
theorem fixedRoundPathControlWorkKaliskiRoundSchedule_forall₂_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List.Forall₂
      (fun program step =>
        UnitaryCircuit.Realizes
          (registersWithFullRoundPathControlWorkEncoding
            tail.succ counterWidth)
          program step)
      (fixedRoundPathControlWorkKaliskiRoundProgramSchedule
        tail counterWidth comparisonIndex workIndex)
      (fixedRoundPathControlWorkKaliskiRoundStepSchedule
        tail counterWidth comparisonIndex workIndex) := by
  apply List.forall₂_of_length_eq_of_get
  · rw [fixedRoundPathControlWorkKaliskiRoundProgramSchedule_length,
      fixedRoundPathControlWorkKaliskiRoundStepSchedule_length]
  · intro i hprogram hstep
    let roundIndex :
        Fin (rnsl17MontgomerySchedule tail.succ).rounds :=
      ⟨i, by
        rw [fixedRoundPathControlWorkKaliskiRoundStepSchedule_length] at hstep
        exact hstep⟩
    change
      UnitaryCircuit.Realizes
        (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
        ((List.ofFn
          (fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
            fixedRoundPathControlWorkKaliskiRoundProgram tail counterWidth
              comparisonIndex roundIndex workIndex)).get ⟨i, hprogram⟩)
        ((List.ofFn
          (fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
            fixedRoundPathControlWorkKaliskiRoundStep tail counterWidth
              comparisonIndex roundIndex workIndex)).get ⟨i, hstep⟩)
    rw [List.get_ofFn, List.get_ofFn]
    exact
      fixedRoundPathControlWorkKaliskiRound_realizes
        tail counterWidth comparisonIndex roundIndex workIndex

/-- Folded base-gate program shell for the fixed-round path/control-work route
schedule.  This folds the already-realized one-round programs; source trace
agreement and staged inverse packaging remain separate obligations. -/
def fixedRoundPathControlWorkKaliskiRoundFoldProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).width)).toQuantum :=
  (fixedRoundPathControlWorkKaliskiRoundProgramSchedule
    tail counterWidth comparisonIndex workIndex).foldr UnitaryCircuit.seq
      (UnitaryCircuit.identity AlgorithmGate.model .empty
        (QubitLayout.canonical
          (registersWithFullRoundPathControlWorkEncoding
            tail.succ counterWidth).width).toQuantum)

/-- Folded semantic shell corresponding to the fixed-round path/control-work
route schedule. -/
def fixedRoundPathControlWorkKaliskiRoundFoldStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  UnitaryCircuit.Realizes.stepList
    (fixedRoundPathControlWorkKaliskiRoundStepSchedule
      tail counterWidth comparisonIndex workIndex)

/-- Prefix semantic shell for the fixed-round path/control-work route schedule.
The `rounds` parameter is intentionally a `Nat`; taking beyond the schedule
length is the same as the full fold. -/
def fixedRoundPathControlWorkKaliskiRoundPrefixStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (rounds : Nat) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  UnitaryCircuit.Realizes.stepList
    ((fixedRoundPathControlWorkKaliskiRoundStepSchedule
      tail counterWidth comparisonIndex workIndex).take rounds)

@[simp] theorem fixedRoundPathControlWorkKaliskiRoundPrefixStep_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth) :
    fixedRoundPathControlWorkKaliskiRoundPrefixStep
        tail counterWidth comparisonIndex workIndex 0 x = x := by
  rfl

/-- Prefix successor form for the fixed-round path/control-work route schedule.
This is the induction step shape used by the folded readout-to-trace bridge. -/
theorem fixedRoundPathControlWorkKaliskiRoundPrefixStep_succ
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth) :
    fixedRoundPathControlWorkKaliskiRoundPrefixStep
        tail counterWidth comparisonIndex workIndex
        (roundIndex.val + 1) x =
      fixedRoundPathControlWorkKaliskiRoundStep
        tail counterWidth comparisonIndex roundIndex workIndex
        (fixedRoundPathControlWorkKaliskiRoundPrefixStep
          tail counterWidth comparisonIndex workIndex roundIndex.val x) := by
  unfold fixedRoundPathControlWorkKaliskiRoundPrefixStep
  let schedule :=
    fixedRoundPathControlWorkKaliskiRoundStepSchedule
      tail counterWidth comparisonIndex workIndex
  have hlen : roundIndex.val < schedule.length := by
    rw [fixedRoundPathControlWorkKaliskiRoundStepSchedule_length]
    exact roundIndex.isLt
  rw [UnitaryCircuit.Realizes.stepList_take_succ schedule roundIndex.val hlen]
  have hget :
      schedule.get ⟨roundIndex.val, hlen⟩ =
        fixedRoundPathControlWorkKaliskiRoundStep
          tail counterWidth comparisonIndex roundIndex workIndex := by
    simpa [schedule] using
      fixedRoundPathControlWorkKaliskiRoundStepSchedule_get
        tail counterWidth comparisonIndex workIndex roundIndex
  rw [hget]

/-- The full schedule prefix is the existing folded semantic shell. -/
theorem fixedRoundPathControlWorkKaliskiRoundPrefixStep_full
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    fixedRoundPathControlWorkKaliskiRoundPrefixStep
        tail counterWidth comparisonIndex workIndex
        (rnsl17MontgomerySchedule tail.succ).rounds =
      fixedRoundPathControlWorkKaliskiRoundFoldStep
        tail counterWidth comparisonIndex workIndex := by
  funext x
  unfold fixedRoundPathControlWorkKaliskiRoundPrefixStep
  unfold fixedRoundPathControlWorkKaliskiRoundFoldStep
  rw [List.take_of_length_le]
  rw [fixedRoundPathControlWorkKaliskiRoundStepSchedule_length]
  simp

/-- The folded fixed-round path/control-work route shell is realized by its
folded base-gate program. -/
theorem fixedRoundPathControlWorkKaliskiRoundFold_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
      (fixedRoundPathControlWorkKaliskiRoundFoldProgram
        tail counterWidth comparisonIndex workIndex)
      (fixedRoundPathControlWorkKaliskiRoundFoldStep
        tail counterWidth comparisonIndex workIndex) :=
  UnitaryCircuit.Realizes.appendList
    (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
    (QubitLayout.canonical _)
    (fixedRoundPathControlWorkKaliskiRoundProgramSchedule
      tail counterWidth comparisonIndex workIndex)
    (fixedRoundPathControlWorkKaliskiRoundStepSchedule
      tail counterWidth comparisonIndex workIndex)
    (fixedRoundPathControlWorkKaliskiRoundSchedule_forall₂_realizes
      tail counterWidth comparisonIndex workIndex)

/-- Semantic inverse chosen for the folded fixed-round path/control route.
The inverse is selected on the finite encoded workspace; the staged wrapper
uses the reversed folded base-gate program as the concrete uncompute leg. -/
noncomputable def fixedRoundPathControlWorkKaliskiRoundFoldUncomputeStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  letI : Nonempty
      (RegistersWithFullRoundPathControlWork tail.succ counterWidth) :=
    ⟨withCleanFullRoundPathControlWork tail.succ counterWidth
      (initialRegisters tail.succ counterWidth 0 0)⟩
  Function.invFun
    (fixedRoundPathControlWorkKaliskiRoundFoldStep
      tail counterWidth comparisonIndex workIndex)

/-- The folded fixed-round path/control semantics is surjective because the
same base-gate program that realizes it is reversible on encoded labels. -/
theorem fixedRoundPathControlWorkKaliskiRoundFoldStep_surjective
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    Function.Surjective
      (fixedRoundPathControlWorkKaliskiRoundFoldStep
        tail counterWidth comparisonIndex workIndex) :=
  letI : Finite
      (RegistersWithFullRoundPathControlWork tail.succ counterWidth) :=
    Finite.of_injective
      (registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).encode
      (registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).encode_injective
  Finite.surjective_of_injective
    (UnitaryCircuit.Realizes.injective
      (fixedRoundPathControlWorkKaliskiRoundFold_realizes
        tail counterWidth comparisonIndex workIndex))

/-- The selected semantic inverse is a right inverse for the folded
path/control fixed-round route. -/
theorem fixedRoundPathControlWorkKaliskiRoundFold_compute_rightInverse
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ∀ x,
      fixedRoundPathControlWorkKaliskiRoundFoldStep
          tail counterWidth comparisonIndex workIndex
          (fixedRoundPathControlWorkKaliskiRoundFoldUncomputeStep
            tail counterWidth comparisonIndex workIndex x) =
        x :=
  letI : Nonempty
      (RegistersWithFullRoundPathControlWork tail.succ counterWidth) :=
    ⟨withCleanFullRoundPathControlWork tail.succ counterWidth
      (initialRegisters tail.succ counterWidth 0 0)⟩
  Function.rightInverse_invFun
    (fixedRoundPathControlWorkKaliskiRoundFoldStep_surjective
      tail counterWidth comparisonIndex workIndex)

/-- Running the selected semantic inverse after a folded path/control compute
run restores the original workspace. -/
theorem fixedRoundPathControlWorkKaliskiRoundFold_uncompute_leftInverse_on_range
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    ∀ x,
      fixedRoundPathControlWorkKaliskiRoundFoldUncomputeStep
          tail counterWidth comparisonIndex workIndex
          (fixedRoundPathControlWorkKaliskiRoundFoldStep
            tail counterWidth comparisonIndex workIndex x) =
        x := by
  intro x
  apply UnitaryCircuit.Realizes.injective
    (fixedRoundPathControlWorkKaliskiRoundFold_realizes
      tail counterWidth comparisonIndex workIndex)
  exact
    fixedRoundPathControlWorkKaliskiRoundFold_compute_rightInverse
      tail counterWidth comparisonIndex workIndex
      (fixedRoundPathControlWorkKaliskiRoundFoldStep
        tail counterWidth comparisonIndex workIndex x)

/-- Actual reversed circuit for the folded fixed-round path/control route. -/
noncomputable def fixedRoundPathControlWorkKaliskiRoundFoldUncomputeProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathControlWorkEncoding
        tail.succ counterWidth).width)).toQuantum :=
  (fixedRoundPathControlWorkKaliskiRoundFoldProgram
    tail counterWidth comparisonIndex workIndex).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)

/-- The reversed folded path/control program realizes the selected semantic
uncompute step. -/
theorem fixedRoundPathControlWorkKaliskiRoundFold_uncompute_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathControlWorkEncoding tail.succ counterWidth)
      (fixedRoundPathControlWorkKaliskiRoundFoldUncomputeProgram
        tail counterWidth comparisonIndex workIndex)
      (fixedRoundPathControlWorkKaliskiRoundFoldUncomputeStep
        tail counterWidth comparisonIndex workIndex) :=
  UnitaryCircuit.Realizes.dagger_of_rightInverse
    (fixedRoundPathControlWorkKaliskiRoundFold_realizes
      tail counterWidth comparisonIndex workIndex)
    (by
      rw [fixedRoundPathControlWorkKaliskiRoundFoldUncomputeProgram,
        UnitaryCircuit.dagger_matrix]
      exact Unitary.star_eq_inv _)
    (fixedRoundPathControlWorkKaliskiRoundFold_compute_rightInverse
      tail counterWidth comparisonIndex workIndex)

/-- If active is false and the selected comparison-work bit is clean, the
full-round active-false wrapper runs the explicit inactive-padding gate-list
action. -/
theorem
    fullRoundWorkActiveFalseControlledInactivePaddingStep_eq_gatePadding_of_active_false_clean
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : (fullRoundWorkActiveBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkComparisonCarryBit tail counterWidth
        (Fin.last tail)).get x = false) :
    fullRoundWorkActiveFalseControlledInactivePaddingStep
        tail counterWidth x =
      fullRoundWorkInactivePaddingGateStep tail counterWidth x := by
  rcases x with ⟨⟨state, coeffWork⟩, counterWork⟩
  rcases state with ⟨regs, comparisonWork⟩
  have hdetActive :
      (detectorCounterActiveBit tail.succ counterWidth).get
          ((regs, comparisonWork), counterWork) = false := by
    change regs.active = false
    change regs.active = false at hactive
    exact hactive
  have hdetWork :
      (detectorCounterComparisonCarryBit tail.succ counterWidth
        (Fin.last tail)).get ((regs, comparisonWork), counterWork) =
        false := by
    change
      (comparisonCarryValueBit tail.succ (Fin.last tail)).get
        comparisonWork = false
    change
      (comparisonCarryValueBit tail.succ (Fin.last tail)).get
        comparisonWork = false at hwork
    exact hwork
  simp [fullRoundWorkActiveFalseControlledInactivePaddingStep,
    fullRoundWorkInactivePaddingGateStep,
    detectorCounterActiveFalseControlledInactivePaddingStep_eq_padding_of_active_false_clean
      tail counterWidth ((regs, comparisonWork), counterWork)
      hdetActive hdetWork]

/-- If active is true, the full-round active-false inactive-padding wrapper is
a no-op. -/
theorem
    fullRoundWorkActiveFalseControlledInactivePaddingStep_eq_self_of_active_true
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hactive : (fullRoundWorkActiveBit tail counterWidth).get x = true) :
    fullRoundWorkActiveFalseControlledInactivePaddingStep
        tail counterWidth x = x := by
  rcases x with ⟨⟨state, coeffWork⟩, counterWork⟩
  rcases state with ⟨regs, comparisonWork⟩
  have hdetActive :
      (detectorCounterActiveBit tail.succ counterWidth).get
          ((regs, comparisonWork), counterWork) = true := by
    change regs.active = true
    change regs.active = true at hactive
    exact hactive
  simp [fullRoundWorkActiveFalseControlledInactivePaddingStep,
    detectorCounterActiveFalseControlledInactivePaddingStep_eq_self_of_active_true
      tail counterWidth ((regs, comparisonWork), counterWork) hdetActive]

/-- Clean endpoint for the full-workspace inactive padding mode. -/
theorem fullRoundWorkInactivePaddingStep_cleanEndpoint
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    fullRoundWorkInactivePaddingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  simp [fullRoundWorkInactivePaddingStep,
    counterIncrementWithWorkStep_cleanEndpoint]

/-- On clean inactive inputs, the lifted explicit inactive-padding gate-list
action increments the padding counter and restores its clean work. -/
theorem fullRoundWorkInactivePaddingGateStep_cleanEndpoint_of_inactive
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hactive : x.active = false) :
    fullRoundWorkInactivePaddingGateStep tail counterWidth
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  simp [fullRoundWorkInactivePaddingGateStep,
    detectorCounterInactivePaddingGateStep_cleanEndpoint_of_inactive
      tail.succ counterWidth x (cleanComparisonWork tail.succ) hactive]

/-- On clean inactive inputs, the full-round active-false wrapper increments
the padding counter and restores its clean work. -/
theorem
    fullRoundWorkActiveFalseControlledInactivePaddingStep_cleanInactiveEndpoint
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hactive : x.active = false) :
    fullRoundWorkActiveFalseControlledInactivePaddingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  have hactiveBit :
      (fullRoundWorkActiveBit tail counterWidth).get
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth) = false := by
    simpa [fullRoundWorkActiveBit, coeffAdderActiveBit, liftedActiveBit,
      liftCoeffAdderStateBitToFullRoundWork,
      liftComparisonStateBitToCoeffAdderWork,
      liftRegisterBitToComparisonWork,
      BinaryLabelEncoding.prodLeftBit, RegisterBits.activeBit_get] using
      hactive
  have hwork :
      (fullRoundWorkComparisonCarryBit tail counterWidth
        (Fin.last tail)).get
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth) = false := by
    change
      (comparisonCarryValueBit tail.succ (Fin.last tail)).get
        (cleanComparisonWork tail.succ) = false
    exact comparisonCarryValueBit_clean tail.succ (Fin.last tail)
  rw [
    fullRoundWorkActiveFalseControlledInactivePaddingStep_eq_gatePadding_of_active_false_clean
      tail counterWidth _ hactiveBit hwork]
  exact
    fullRoundWorkInactivePaddingGateStep_cleanEndpoint_of_inactive
      tail counterWidth x hactive

/-- On clean active inputs, the full-round active-false wrapper is a no-op. -/
theorem
    fullRoundWorkActiveFalseControlledInactivePaddingStep_cleanActiveEndpoint
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hactive : x.active = true) :
    fullRoundWorkActiveFalseControlledInactivePaddingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      (((x, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  have hactiveBit :
      (fullRoundWorkActiveBit tail counterWidth).get
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth) = true := by
    simpa [fullRoundWorkActiveBit, coeffAdderActiveBit, liftedActiveBit,
      liftCoeffAdderStateBitToFullRoundWork,
      liftComparisonStateBitToCoeffAdderWork,
      liftRegisterBitToComparisonWork,
      BinaryLabelEncoding.prodLeftBit, RegisterBits.activeBit_get] using
      hactive
  exact
    fullRoundWorkActiveFalseControlledInactivePaddingStep_eq_self_of_active_true
      tail counterWidth _ hactiveBit

/-- On clean inactive path/control-work inputs, the lifted active-false wrapper
increments the padding counter and preserves the explicit path/control bits. -/
theorem
    fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanInactiveEndpoint
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hactive : x.active = false) :
    fullRoundPathControlWorkActiveFalseInactivePaddingStep tail counterWidth
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false) := by
  change
    ((fullRoundWorkActiveFalseControlledInactivePaddingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth),
      false),
      false) =
      ((((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false)
  rw [
    fullRoundWorkActiveFalseControlledInactivePaddingStep_cleanInactiveEndpoint
      tail counterWidth x hactive]

/-- On clean inactive `v = 0` path/control-work inputs, the lifted terminating
prefix flips active on, increments the counter, and preserves path/control
bits. -/
theorem
    fullRoundPathControlWorkTerminatingStep_cleanEndpoint_of_v_zero_inactive
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = false)
    (hvZero : x.v.val = 0) :
    fullRoundPathControlWorkTerminatingStep tail counterWidth
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with
          active := true,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false) := by
  change
    ((fullRoundWorkTerminatingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth),
      false),
      false) =
      ((((({ x with
          active := true,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false)
  rw [
    fullRoundWorkTerminatingStep_cleanEndpoint_of_v_zero_inactive
      tail counterWidth x hcompare hactive hvZero]

/-- On inactive clean `v = 0` inputs, the original-active-controlled concrete
route runs inactive padding and the terminating prefix, then skips the active
body because the explicit original-active path bit is false. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_cleanEndpoint_of_inactive_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvZero : x.v.val = 0) :
    fullRoundPathControlWorkKaliskiRoundControlledStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with
          active := true,
          counter :=
            wordIncrement counterWidth
              (wordIncrement counterWidth x.counter) },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false) := by
  rw [fullRoundPathControlWorkKaliskiRoundControlledStep]
  have hactiveBit :
      (fullRoundPathControlWorkActiveBit tail counterWidth).get
          (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
        false := by
    change
      (fullRoundPathWorkActiveBit tail counterWidth).get
          (withCleanFullRoundPathWork tail.succ counterWidth x) =
        false
    simpa [withCleanFullRoundPathWork, fullRoundPathWorkActiveBit,
      fullRoundWorkActiveBit, coeffAdderActiveBit, liftedActiveBit,
      liftFullRoundWorkBitToPathWork,
      liftCoeffAdderStateBitToFullRoundWork,
      liftComparisonStateBitToCoeffAdderWork,
      liftRegisterBitToComparisonWork,
      BinaryLabelEncoding.prodLeftBit, RegisterBits.activeBit_get] using
      hactive
  rw [
    fullRoundPathControlWorkOriginalActiveLatchStep_eq_self_of_active_false
      tail counterWidth
      (withCleanFullRoundPathControlWork tail.succ counterWidth x)
      hactiveBit]
  rw [
    fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanInactiveEndpoint
      tail counterWidth x hactive]
  let padded : Registers tail.succ counterWidth :=
    { x with counter := wordIncrement counterWidth x.counter }
  change
    fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundPathControlWorkTerminatingStep tail counterWidth
          (withCleanFullRoundPathControlWork tail.succ counterWidth padded)) =
      ((((({ x with
          active := true,
          counter :=
            wordIncrement counterWidth
              (wordIncrement counterWidth x.counter) },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false)
  have hcomparePadded : padded.compare = false := by
    simpa [padded] using hcompare
  have hactivePadded : padded.active = false := by
    simpa [padded] using hactive
  have hvZeroPadded : padded.v.val = 0 := by
    simpa [padded] using hvZero
  rw [
    fullRoundPathControlWorkTerminatingStep_cleanEndpoint_of_v_zero_inactive
      tail counterWidth padded hcomparePadded hactivePadded hvZeroPadded]
  let terminated : Registers tail.succ counterWidth :=
    { padded with
      active := true,
      counter := wordIncrement counterWidth padded.counter }
  change
    fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((((terminated, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth),
          false),
          false) =
      ((((({ x with
          active := true,
          counter :=
            wordIncrement counterWidth
              (wordIncrement counterWidth x.counter) },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false)
  have hpathFalse :
      (fullRoundPathControlWorkPathBit tail counterWidth).get
          (((((terminated, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ),
              cleanCounterIncrementWork counterWidth),
            false),
            false) =
        false := by
    rfl
  rw [
    fullRoundPathControlWorkOriginalActiveControlledBodyStep_eq_self_of_path_false
      tail counterWidth comparisonIndex historyIndex workIndex _ hpathFalse]

/-- On clean inactive inputs, the full-round active-false wrapper matches the
source inactive round on the source-state projection. -/
theorem
    fullRoundWorkActiveFalseControlledInactivePaddingStep_fromRegisters_eq_source_round_of_inactive
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkActiveFalseControlledInactivePaddingStep tail counterWidth
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundWorkActiveFalseControlledInactivePaddingStep_cleanInactiveEndpoint
      tail counterWidth x hactive]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = false := by
    simpa [RoundState.fromRegisters] using hactive
  rw [RoundState.round_inactive
    (RoundState.fromRegisters tail.succ counterWidth x
      kaliskiSteps paddingSteps) hsourceActive]
  simp [RoundState.fromRegisters, hactive]

/-- On clean work in inactive mode, the full-workspace padding step matches
the source inactive round on the source-state projection. -/
theorem
    fullRoundWorkInactivePaddingStep_fromRegisters_eq_source_round_of_inactive
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkInactivePaddingStep tail counterWidth
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [fullRoundWorkInactivePaddingStep_cleanEndpoint]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = false := by
    simpa [RoundState.fromRegisters] using hactive
  rw [RoundState.round_inactive
    (RoundState.fromRegisters tail.succ counterWidth x
      kaliskiSteps paddingSteps) hsourceActive]
  simp [RoundState.fromRegisters, hactive]

/-- Under an explicit valid-comparison assumption, the semantic selected-branch
wrapper dispatches to the same fixed branch as the source-level Kaliski
selector viewed from concrete registers. -/
theorem coeffWorkKaliskiActiveSelectedBranchRoundStep_eq_selectBranch_of_compare
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare :
      (coeffAdderCompareBit tail.succ counterWidth).get x =
        decide (x.1.1.v.val < x.1.1.u.val)) :
    coeffWorkKaliskiActiveSelectedBranchRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      coeffWorkKaliskiActiveBranchRoundStep tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        (WireAddress.littleEndianWire (0 : Fin tail.succ))
        comparisonIndex historyIndex
        (RoundState.selectBranch
          (RoundState.fromRegisters tail.succ counterWidth x.1.1
            kaliskiSteps paddingSteps)) x := by
  rw [coeffWorkKaliskiActiveSelectedBranchRoundStep]
  rw [RoundState.selectBranch_fromRegisters_eq_fromCoeffWorkSignals_of_compare
    tail.succ counterWidth x kaliskiSteps paddingSteps hcompare]

/-- Semantic nonzero-active selected round wrapper over coefficient-adder work.
The even cases use the concrete selected branch-code/history/aux-shift dispatch.
The odd-odd case runs the comparison selector, selected odd data path, and
carried branch-code dispatch so the odd branch decision is latched before
`u`/`v` mutation.  Termination and padding-counter mode remain separate
fixed-round obligations. -/
def coeffWorkKaliskiActiveNonzeroRoundStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithCoeffAdderWork tail.succ counterWidth ->
      RegistersWithCoeffAdderWork tail.succ counterWidth :=
  fun x =>
    if (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x then
      if (coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x then
        coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
          tail counterWidth comparisonIndex historyIndex x
      else
        coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth comparisonIndex historyIndex x
    else
      coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x

/-- Semantic nonzero-active selected round lifted to the full fixed-round
workspace, preserving the padding-counter increment work.  This is still the
semantic data-dependent wrapper; the explicit fixed-branch family above is the
actual circuit family available branch-by-branch. -/
def fullRoundWorkKaliskiActiveNonzeroRoundStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    (coeffWorkKaliskiActiveNonzeroRoundStep
      tail counterWidth comparisonIndex historyIndex x.1,
      x.2)

/-- If the concrete low `u` readout is false, the nonzero-active selected
wrapper uses the even selected branch-code/history/aux-shift dispatch. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  simp [coeffWorkKaliskiActiveNonzeroRoundStep, huLow]

/-- In the full fixed-round workspace, if the concrete low `u` readout is
false, the lifted nonzero-active semantic wrapper uses the even selected
branch-code/history/aux-shift dispatch and preserves counter work. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = false) :
    fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x.1,
        x.2) := by
  cases x with
  | mk coeffState counterWork =>
      simp [fullRoundWorkKaliskiActiveNonzeroRoundStep,
        coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false,
        huLow]

/-- If low `u` is false, the lifted nonzero-active semantic wrapper agrees
with the lifted selected branch-code/history/aux-shift dispatch. -/
theorem fullRoundWorkActiveNonzero_eq_selectedDispatch_of_u_lsb_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = false) :
    fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x =
    fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false]
  · rfl
  · exact huLow

/-- If the concrete low `u` readout is true and low `v` readout is false, the
nonzero-active selected wrapper uses the even selected
branch-code/history/aux-shift dispatch. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false) :
    coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  simp [coeffWorkKaliskiActiveNonzeroRoundStep, huLow, hvLow]

/-- In the full fixed-round workspace, if low `u` is true and low `v` is
false, the lifted nonzero-active semantic wrapper uses the even selected
branch-code/history/aux-shift dispatch and preserves counter work. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = false) :
    fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x.1,
        x.2) := by
  cases x with
  | mk coeffState counterWork =>
      simp [fullRoundWorkKaliskiActiveNonzeroRoundStep,
        coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false,
        huLow, hvLow]

/-- If low `u` is true and low `v` is false, the lifted nonzero-active
semantic wrapper agrees with the lifted selected branch-code/history/aux-shift
dispatch. -/
theorem fullRoundWorkActiveNonzero_eq_selectedDispatch_of_u_lsb_true_v_lsb_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = false) :
    fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      fullRoundWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false]
  · rfl
  · exact huLow
  · exact hvLow

/-- If both concrete low readouts are true, the nonzero-active selected wrapper
uses the carried odd dispatch route so branch signals are not recomputed after
the selected odd data path mutates `u` or `v`. -/
theorem
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true) :
    coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  simp [coeffWorkKaliskiActiveNonzeroRoundStep, huLow, hvLow]

/-- In the full fixed-round workspace, if both low readouts are true, the
lifted nonzero-active semantic wrapper uses the carried odd dispatch route and
preserves counter work. -/
theorem
    fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = true) :
    fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth comparisonIndex historyIndex x.1,
        x.2) := by
  cases x with
  | mk coeffState counterWork =>
      simp [fullRoundWorkKaliskiActiveNonzeroRoundStep,
        coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true,
        huLow, hvLow]

/-- If both low readouts are true, the lifted nonzero-active semantic wrapper
agrees with the lifted selector-selected odd carried dispatch route. -/
theorem fullRoundWorkActiveNonzero_eq_selectedOddCarriedDispatch_of_lsb_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 = true) :
    fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x =
      fullRoundWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [fullRoundWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true]
  · rfl
  · exact huLow
  · exact hvLow

/-- In the active clean odd-odd `v < u` case, the lifted nonzero-active
semantic wrapper agrees with the concrete compare-carried odd dispatch route.
-/
theorem fullRoundWorkActiveNonzero_eq_compareCarriedDispatch_clean_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) =
      fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) := by
  rw [fullRoundWorkActiveNonzero_eq_selectedOddCarriedDispatch_of_lsb_true]
  · change
      (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
          tail counterWidth comparisonIndex historyIndex
          ((x, cleanComparisonWork tail.succ), work),
        counterWork) =
      (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex
          ((x, cleanComparisonWork tail.succ), work),
        counterWork)
    rw [coeffWorkSelectedOddCarriedDispatch_eq_compareCarriedDispatch_clean_lt
      tail counterWidth comparisonIndex historyIndex x work hscratchA
      hcompare hfinal huOdd hvOdd hlt hcontrolWork hactive]
  · rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  · rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd

/-- In the active clean odd-odd non-`v < u` case, the lifted nonzero-active
semantic wrapper agrees with the concrete compare-carried odd dispatch route.
-/
theorem fullRoundWorkActiveNonzero_eq_compareCarriedDispatch_clean_not_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) =
      fullRoundWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) := by
  rw [fullRoundWorkActiveNonzero_eq_selectedOddCarriedDispatch_of_lsb_true]
  · change
      (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
          tail counterWidth comparisonIndex historyIndex
          ((x, cleanComparisonWork tail.succ), work),
        counterWork) =
      (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex
          ((x, cleanComparisonWork tail.succ), work),
        counterWork)
    rw [coeffWorkSelectedOddCarriedDispatch_eq_compareCarriedDispatch_clean_not_lt
      tail counterWidth comparisonIndex historyIndex x work hscratchA
      hcompare hfinal huOdd hvOdd hnlt hcontrolWork hactive]
  · rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  · rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd

/-- In the low-`u` false branch, the odd-odd latch-then-body wrapper agrees
with the nonzero-active semantic wrapper. -/
theorem fullRoundWorkOddOddLatchThenBodyStep_eq_activeNonzero_of_uLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkKaliskiActiveNonzeroRoundStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [fullRoundWorkOddOddLatchThenBodyStep_eq_selected_of_uLow_false
    tail counterWidth comparisonIndex historyIndex workIndex
    x hcontrol hwork huLow]
  rw [← fullRoundWorkActiveNonzero_eq_selectedDispatch_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]

/-- In the low-`u` true and low-`v` false branch, the odd-odd latch-then-body
wrapper agrees with the nonzero-active semantic wrapper. -/
theorem
    fullRoundWorkOddOddLatchThenBodyStep_eq_activeNonzero_of_uLow_true_vLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkKaliskiActiveNonzeroRoundStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkOddOddLatchThenBodyStep_eq_selected_of_uLow_true_vLow_false
      tail counterWidth comparisonIndex historyIndex workIndex
      x hcontrol hwork huLow hvLow]
  rw [←
    fullRoundWorkActiveNonzero_eq_selectedDispatch_of_u_lsb_true_v_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow hvLow]

/-- In the clean odd-odd `v < u` branch, latch-then-body agrees with the
nonzero-active semantic wrapper up to the remaining counter carry-in latch
flip. -/
theorem fullRoundWorkOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkKaliskiActiveNonzeroRoundStep
          tail counterWidth comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)) := by
  rw [
    fullRoundWorkOddOddLatchThenBodyStep_eq_flip_compareCarried_of_lsb_true
      tail counterWidth comparisonIndex historyIndex workIndex
      (((x, cleanComparisonWork tail.succ), work), counterWork)
      hcontrol hcounterWork]
  · rw [fullRoundWorkActiveNonzero_eq_compareCarriedDispatch_clean_lt
      tail counterWidth comparisonIndex historyIndex x work counterWork
      hscratchA hcompare hfinal huOdd hvOdd hlt hcontrolWork hactive]
  · rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  · rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd

/-- In the clean odd-odd non-`v < u` branch, latch-then-body agrees with the
nonzero-active semantic wrapper up to the remaining counter carry-in latch
flip. -/
theorem fullRoundWorkOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_not_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    fullRoundWorkOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkKaliskiActiveNonzeroRoundStep
          tail counterWidth comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)) := by
  rw [
    fullRoundWorkOddOddLatchThenBodyStep_eq_flip_compareCarried_of_lsb_true
      tail counterWidth comparisonIndex historyIndex workIndex
      (((x, cleanComparisonWork tail.succ), work), counterWork)
      hcontrol hcounterWork]
  · rw [fullRoundWorkActiveNonzero_eq_compareCarriedDispatch_clean_not_lt
      tail counterWidth comparisonIndex historyIndex x work counterWork
      hscratchA hcompare hfinal huOdd hvOdd hnlt hcontrolWork hactive]
  · rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  · rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd

/-- In the low-`u` false branch, the active-guarded latch-then-body wrapper
agrees with the nonzero-active semantic wrapper. -/
theorem fullRoundWorkActiveOddOddLatchThenBodyStep_eq_activeNonzero_of_uLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkKaliskiActiveNonzeroRoundStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [fullRoundWorkActiveOddOddLatchThenBodyStep_eq_selected_of_uLow_false
    tail counterWidth comparisonIndex historyIndex workIndex
    x hcontrol hwork huLow]
  rw [← fullRoundWorkActiveNonzero_eq_selectedDispatch_of_u_lsb_false
    tail counterWidth comparisonIndex historyIndex x huLow]

/-- In the low-`u` true and low-`v` false branch, the active-guarded
latch-then-body wrapper agrees with the nonzero-active semantic wrapper. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_activeNonzero_of_uLow_true_vLow_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundWork tail.succ counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get x = false)
    (hwork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get x =
        false)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x.1 =
        false) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      fullRoundWorkKaliskiActiveNonzeroRoundStep
        tail counterWidth comparisonIndex historyIndex x := by
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_selected_of_uLow_true_vLow_false
      tail counterWidth comparisonIndex historyIndex workIndex
      x hcontrol hwork huLow hvLow]
  rw [←
    fullRoundWorkActiveNonzero_eq_selectedDispatch_of_u_lsb_true_v_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow hvLow]

/-- In the active clean odd-odd `v < u` branch, active-guarded
latch-then-body agrees with the nonzero-active semantic wrapper up to the
remaining counter carry-in latch flip. -/
theorem fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkKaliskiActiveNonzeroRoundStep
          tail counterWidth comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)) := by
  have hactiveFull :
      (fullRoundWorkActiveBit tail counterWidth).get
          (((x, cleanComparisonWork tail.succ), work), counterWork) = true := by
    simpa [fullRoundWorkActiveBit, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_compareCarried_of_active_lsb_true
      tail counterWidth comparisonIndex historyIndex workIndex
      (((x, cleanComparisonWork tail.succ), work), counterWork)
      hactiveFull hcontrol hcounterWork]
  · rw [fullRoundWorkActiveNonzero_eq_compareCarriedDispatch_clean_lt
      tail counterWidth comparisonIndex historyIndex x work counterWork
      hscratchA hcompare hfinal huOdd hvOdd hlt hcontrolWork hactive]
  · rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  · rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd

/-- In the active clean odd-odd non-`v < u` branch, active-guarded
latch-then-body agrees with the nonzero-active semantic wrapper up to the
remaining counter carry-in latch flip. -/
theorem
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_activeNonzero_clean_not_lt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hcontrol :
      (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hcounterWork :
      (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ), work), counterWork) = false)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork) =
      (fullRoundWorkCounterCarryInBit tail counterWidth).flip
        (fullRoundWorkKaliskiActiveNonzeroRoundStep
          tail counterWidth comparisonIndex historyIndex
          (((x, cleanComparisonWork tail.succ), work), counterWork)) := by
  have hactiveFull :
      (fullRoundWorkActiveBit tail counterWidth).get
          (((x, cleanComparisonWork tail.succ), work), counterWork) = true := by
    simpa [fullRoundWorkActiveBit, liftCoeffAdderStateBitToFullRoundWork,
      BinaryLabelEncoding.prodLeftBit] using hactive
  rw [
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_flip_compareCarried_of_active_lsb_true
      tail counterWidth comparisonIndex historyIndex workIndex
      (((x, cleanComparisonWork tail.succ), work), counterWork)
      hactiveFull hcontrol hcounterWork]
  · rw [fullRoundWorkActiveNonzero_eq_compareCarriedDispatch_clean_not_lt
      tail counterWidth comparisonIndex historyIndex x work counterWork
      hscratchA hcompare hfinal huOdd hvOdd hnlt hcontrolWork hactive]
  · rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  · rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd

/-! ## Concrete active-only round package -/

/-- Folded concrete route for the active-only fixed-round package.  It first
runs the detector-gated terminating route and then runs the active-guarded
latch/body route.  The clean `v ≠ 0` reductions below show that the
terminating prefix cancels and the latch/body route handles the nonzero active
branch.  The clean `v = 0` endpoint for this folded route is a separate
obligation, because after the terminating route clears `active` the downstream
selected-dispatch no-op fact must still be proved explicitly. -/
def fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
      tail counterWidth comparisonIndex historyIndex workIndex
      (fullRoundWorkTerminatingStep tail counterWidth x)

/-- Base-gate program for the concrete active-only fixed-round route. -/
def fullRoundWorkKaliskiActiveOnlyRoundConcreteProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  UnitaryCircuit.seq
    (fullRoundWorkTerminatingStandardLayoutProgram tail counterWidth)
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchProgram
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The concrete active-only fixed-round program realizes its folded semantic
route. -/
theorem fullRoundWorkKaliskiActiveOnlyRoundConcrete_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  UnitaryCircuit.Realizes.seq
    (firstStep := fullRoundWorkTerminatingStep tail counterWidth)
    (secondStep :=
      fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundWorkTerminatingStandardLayout_realizes tail counterWidth)
    (fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatch_realizes
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- On clean work in the concrete `v ≠ 0` case, the terminating prefix of the
concrete active-only route cancels and the route reduces to the active-guarded
latch/body dispatch. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hvNonzero : x.v.val ≠ 0) :
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep]
  rw [fullRoundWorkTerminatingStep_cleanEndpoint_of_v_nonzero
    tail counterWidth x hcompare hvNonzero]

/-- The full-round counter carry-in latch is clean on the standard clean
full-round work object. -/
theorem fullRoundWorkCounterCarryInBit_get_clean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (fullRoundWorkCounterCarryInBit tail counterWidth).get
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      false := by
  change
    (counterIncrementCarryInBit counterWidth).get
      (cleanCounterIncrementWork counterWidth) = false
  change BinaryLabelEncoding.boolBit.get
      (cleanCounterIncrementWork counterWidth).2.1 = false
  rfl

/-- Each full-round counter carry-work bit is clean on the standard clean
full-round work object. -/
theorem fullRoundWorkCounterCarryWorkBit_get_clean
    (tail counterWidth : Nat) (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) :
    (fullRoundWorkCounterCarryWorkBit tail counterWidth workIndex).get
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      false := by
  change
    (counterIncrementCarryWorkBit counterWidth workIndex).get
      (cleanCounterIncrementWork counterWidth) = false
  change
    (BinaryLabelEncoding.finIdentityBit (counterWidth - 1) workIndex).get
      (PlainAdder.Schedule.PowerOfTwo.cleanCarryWork counterWidth) = false
  simp [PlainAdder.Schedule.PowerOfTwo.cleanCarryWork]

/-- The lifted coefficient-adder carry-in flag is clean on the standard clean
coefficient work object. -/
theorem liftedCoeffAdderCarryInBit_get_clean
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (x, cleanCoeffAdderWork n) =
      false := by
  change (coeffAdderCarryInWorkBit n).get (cleanCoeffAdderWork n) = false
  rfl

/-- Each lifted coefficient-adder carry-work bit is clean on the standard clean
coefficient work object. -/
theorem liftedCoeffAdderCarryWorkBit_get_clean
    (n counterWidth : Nat) (bit : Fin ((n + 1) - 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit bit).get
        (x, cleanCoeffAdderWork n) =
      false := by
  change
    (coeffAdderCarryWorkBit n bit).get (cleanCoeffAdderWork n) = false
  change
    (BinaryLabelEncoding.finIdentityBit ((n + 1) - 1) bit).get
        (PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (n + 1)) =
      false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n bit

/-- Each lifted comparison-carry prefix bit is clean on the standard clean
comparison and coefficient work objects. -/
theorem coeffAdderComparisonCarryPrefixWord_get_clean
    (n counterWidth : Nat) (bit : Fin (n - 1))
    (x : Registers n counterWidth) :
    ((coeffAdderComparisonCarryPrefixWord n counterWidth).bit bit).get
        ((x, cleanComparisonWork n), cleanCoeffAdderWork n) =
      false := by
  change
    (liftedComparisonCarryBit n counterWidth
        (coeffAdderComparisonCarryPrefixIndex n bit)).get
        (x, cleanComparisonWork n) =
      false
  simp

/-- On clean work in the concrete `v = 0` case, the folded concrete
active-only route has the same clean endpoint as the terminating
counter-mode prefix.  The inactive latch/body suffix is a no-op under clean
source scratch bits. -/
theorem fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_cleanEndpoint_of_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep]
  rw [fullRoundWorkTerminatingStep_cleanEndpoint_of_v_zero
    tail counterWidth x hcompare hactive hvZero]
  let terminated : Registers tail.succ counterWidth :=
    { x with
      active := false,
      counter := wordIncrement counterWidth x.counter }
  change fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
      tail counterWidth comparisonIndex historyIndex workIndex
      (((terminated, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) =
    (((terminated, cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
      cleanCounterIncrementWork counterWidth)
  have hactiveFull :
      (fullRoundWorkActiveBit tail counterWidth).get
          (((terminated, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth) =
        false := by
    change (coeffAdderActiveBit tail.succ counterWidth).get
        ((terminated, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ) = false
    change terminated.active = false
    simp [terminated]
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((terminated, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) =
        false := by
    change terminated.scratchA = false
    simpa [terminated] using hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((terminated, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) =
        false := by
    change terminated.scratchB = false
    simpa [terminated] using hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth comparisonIndex).get
          ((terminated, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) =
        false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
          (terminated, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
          (cleanComparisonWork tail.succ) = false
    simp
  exact
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_self_of_inactive_clean
      tail counterWidth comparisonIndex historyIndex workIndex
      (((terminated, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
      hactiveFull
      (fullRoundWorkCounterCarryInBit_get_clean
        tail counterWidth terminated)
      (fullRoundWorkCounterCarryWorkBit_get_clean
        tail counterWidth workIndex terminated)
      hscratchACoeff hscratchBCoeff htemp

/-- On clean work in the concrete `v = 0` case, the folded concrete
active-only route matches the source terminating round on the source-state
projection.  The inactive latch/body suffix is a no-op under clean source
scratch bits. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_fromRegisters_eq_source_round_of_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_cleanEndpoint_of_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero hscratchA hscratchB]
  rw [← fullRoundWorkTerminatingStep_cleanEndpoint_of_v_zero
    tail counterWidth x hcompare hactive hvZero]
  exact
    fullRoundWorkTerminatingStep_fromRegisters_eq_source_round_of_v_zero
      tail counterWidth kaliskiSteps paddingSteps x hcompare hactive hvZero

/-- On clean inactive `v ≠ 0` inputs, the folded concrete active-only route is
a no-op: the terminating detector/counter prefix cancels and the active-guarded
latch/body suffix is inactive. -/
theorem
    fullRoundWorkKaliskiActiveOnlyConcreteStep_eq_self_of_inactive_v_nonzero_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvNonzero : x.v.val ≠ 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      (((x, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex historyIndex workIndex
      x hcompare hvNonzero]
  have hactiveFull :
      (fullRoundWorkActiveBit tail counterWidth).get
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth) = false := by
    change (coeffAdderActiveBit tail.succ counterWidth).get
        ((x, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ) = false
    change x.active = false
    exact hactive
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) =
        false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) =
        false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) =
        false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
          (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
          (cleanComparisonWork tail.succ) = false
    simp
  exact
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_self_of_inactive_clean
      tail counterWidth comparisonIndex historyIndex workIndex
      (((x, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
      hactiveFull
      (fullRoundWorkCounterCarryInBit_get_clean
        tail counterWidth x)
      (fullRoundWorkCounterCarryWorkBit_get_clean
        tail counterWidth workIndex x)
      hscratchACoeff hscratchBCoeff htemp

/-- If inactive padding runs before the folded concrete active-only route, the
composition still has the padding endpoint on clean inactive `v ≠ 0` inputs. -/
theorem
    fullRoundWorkInactivePaddingThenConcrete_cleanEndpoint_of_inactive_v_nonzero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvNonzero : x.v.val ≠ 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundWorkActiveFalseControlledInactivePaddingStep tail counterWidth
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)) =
      ((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [
    fullRoundWorkActiveFalseControlledInactivePaddingStep_cleanInactiveEndpoint
      tail counterWidth x hactive]
  let padded : Registers tail.succ counterWidth :=
    { x with counter := wordIncrement counterWidth x.counter }
  change
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((padded, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      (((padded, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
  have hcomparePadded : padded.compare = false := by
    simpa [padded] using hcompare
  have hactivePadded : padded.active = false := by
    simpa [padded] using hactive
  have hvNonzeroPadded : padded.v.val ≠ 0 := by
    simpa [padded] using hvNonzero
  have hscratchAPadded : padded.scratchA = false := by
    simpa [padded] using hscratchA
  have hscratchBPadded : padded.scratchB = false := by
    simpa [padded] using hscratchB
  exact
    fullRoundWorkKaliskiActiveOnlyConcreteStep_eq_self_of_inactive_v_nonzero_clean
      tail counterWidth comparisonIndex historyIndex workIndex padded
      hcomparePadded hactivePadded hvNonzeroPadded
      hscratchAPadded hscratchBPadded

/-- Concrete outer route for one fixed Montgomery--Kaliski round.  It first
runs active-false-controlled inactive padding, then the folded active-only
concrete route.  This is a reversible concrete route, not the clean-restoring
semantic total selector: the inactive `v = 0` slice needs a separate readout
target before this can serve as the aggregate round witness. -/
def fullRoundWorkKaliskiRoundConcreteStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundWork tail.succ counterWidth ->
      RegistersWithFullRoundWork tail.succ counterWidth :=
  fun x =>
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex historyIndex workIndex
      (fullRoundWorkActiveFalseControlledInactivePaddingStep
        tail counterWidth x)

/-- Base-gate program for the concrete outer route. -/
def fullRoundWorkKaliskiRoundConcreteProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  UnitaryCircuit.seq
    (fullRoundWorkActiveFalseControlledInactivePaddingProgram
      tail counterWidth)
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteProgram
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The concrete outer route is realized by its composed base-gate program. -/
theorem fullRoundWorkKaliskiRoundConcrete_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundWorkEncoding tail.succ counterWidth)
      (fullRoundWorkKaliskiRoundConcreteProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundWorkKaliskiRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  UnitaryCircuit.Realizes.seq
    (firstStep := fullRoundWorkActiveFalseControlledInactivePaddingStep
      tail counterWidth)
    (secondStep := fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundWorkActiveFalseControlledInactivePadding_realizes
      tail counterWidth)
    (fullRoundWorkKaliskiActiveOnlyRoundConcrete_realizes
      tail counterWidth comparisonIndex historyIndex workIndex)

/-! ## Concrete round package with explicit path work -/

/-- Concrete outer-route step lifted over a trailing path bit.  The path bit is
preserved; later wrappers can use it as an explicit route/readout latch instead
of reusing already-occupied full-round work bits. -/
def fullRoundPathWorkKaliskiRoundConcreteStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathWork tail.succ counterWidth ->
      RegistersWithFullRoundPathWork tail.succ counterWidth :=
  liftFullRoundWorkStepToPathWork tail.succ counterWidth
    (fullRoundWorkKaliskiRoundConcreteStep
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- Base-gate program for the path-work-lifted concrete outer route. -/
def fullRoundPathWorkKaliskiRoundConcreteProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  liftFullRoundWorkProgramToPathWork tail.succ counterWidth
    (fullRoundWorkKaliskiRoundConcreteProgram
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The path-work-lifted concrete outer route is realized by its composed
base-gate program. -/
theorem fullRoundPathWorkKaliskiRoundConcrete_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
      (fullRoundPathWorkKaliskiRoundConcreteProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathWorkKaliskiRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  liftFullRoundWorkProgramToPathWork_realizes tail.succ counterWidth
    (fullRoundWorkKaliskiRoundConcrete_realizes
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The lifted concrete outer route preserves the explicit path bit. -/
theorem fullRoundPathWorkKaliskiRoundConcreteStep_path
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathWork tail.succ counterWidth) :
    (fullRoundPathWorkKaliskiRoundConcreteStep
      tail counterWidth comparisonIndex historyIndex workIndex x).2 = x.2 := by
  rfl

/-- The original-active latch only changes the path bit. -/
theorem fullRoundPathWorkOriginalActiveLatchStep_fullRound
    (tail counterWidth : Nat)
    (x : RegistersWithFullRoundPathWork tail.succ counterWidth) :
    (fullRoundPathWorkOriginalActiveLatchStep tail counterWidth x).1 =
      x.1 := by
  unfold fullRoundPathWorkOriginalActiveLatchStep
  simp only [fullRoundPathWorkOriginalActiveLatchGates,
    fullRoundPathWorkOriginalActiveLatchGate,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step]
  unfold EncodedBit.cnotStep
  by_cases hactive : (fullRoundPathWorkActiveBit tail counterWidth).get x
  · simp [hactive, fullRoundPathWorkPathBit,
      BinaryLabelEncoding.prodRightBit]
  · simp [hactive]

/-- The path bit is clean in the standard clean path-work input. -/
theorem fullRoundPathWorkPathBit_get_withClean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (fullRoundPathWorkPathBit tail counterWidth).get
      (withCleanFullRoundPathWork tail.succ counterWidth x) = false := by
  rfl

/-- The lifted active bit reads the source register active flag in the standard
clean path-work input. -/
theorem fullRoundPathWorkActiveBit_get_withClean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (fullRoundPathWorkActiveBit tail counterWidth).get
      (withCleanFullRoundPathWork tail.succ counterWidth x) = x.active := by
  simp [withCleanFullRoundPathWork, fullRoundPathWorkActiveBit,
    liftFullRoundWorkBitToPathWork, liftCoeffAdderStateBitToFullRoundWork,
    coeffAdderActiveBit, liftComparisonStateBitToCoeffAdderWork,
    liftedActiveBit, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit, RegisterBits.activeBit_get]

/-- The path bit is clean in the standard clean path/control-work input. -/
theorem fullRoundPathControlWorkPathBit_get_withClean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (fullRoundPathControlWorkPathBit tail counterWidth).get
      (withCleanFullRoundPathControlWork tail.succ counterWidth x) = false := by
  exact fullRoundPathWorkPathBit_get_withClean tail counterWidth x

/-- The control-work bit is clean in the standard clean path/control-work
input. -/
theorem fullRoundPathControlWorkControlWorkBit_get_withClean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (fullRoundPathControlWorkControlWorkBit tail counterWidth).get
      (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
        false := by
  rfl

/-- The lifted active bit reads the source register active flag in the standard
clean path/control-work input. -/
theorem fullRoundPathControlWorkActiveBit_get_withClean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (fullRoundPathControlWorkActiveBit tail counterWidth).get
      (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
        x.active := by
  exact fullRoundPathWorkActiveBit_get_withClean tail counterWidth x

/-- On clean active path/control-work inputs, the original-active latch keeps
the full-round component and records the source active flag in the path bit. -/
theorem
    fullRoundPathControlWorkOriginalActiveLatchStep_cleanActiveEndpoint
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hactive : x.active = true) :
    fullRoundPathControlWorkOriginalActiveLatchStep tail counterWidth
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      (((withCleanFullRoundPathWork tail.succ counterWidth x).1, true),
        false) := by
  unfold fullRoundPathControlWorkOriginalActiveLatchStep
    liftFullRoundPathWorkStepToControlWork
    withCleanFullRoundPathControlWork
  apply Prod.ext
  · apply Prod.ext
    · change
        (fullRoundPathWorkOriginalActiveLatchStep tail counterWidth
          (withCleanFullRoundPathWork tail.succ counterWidth x)).1 =
          (withCleanFullRoundPathWork tail.succ counterWidth x).1
      rw [fullRoundPathWorkOriginalActiveLatchStep_fullRound]
    · change
        (fullRoundPathWorkPathBit tail counterWidth).get
            (fullRoundPathWorkOriginalActiveLatchStep tail counterWidth
              (withCleanFullRoundPathWork tail.succ counterWidth x)) =
          true
      rw [
        fullRoundPathWorkOriginalActiveLatchStep_path_of_clean
          tail counterWidth
          (withCleanFullRoundPathWork tail.succ counterWidth x)]
      · rw [fullRoundPathWorkActiveBit_get_withClean, hactive]
      · exact fullRoundPathWorkPathBit_get_withClean tail counterWidth x
  · rfl

/-- Concrete outer route preceded by an explicit original-active path latch. -/
def fullRoundPathWorkKaliskiRoundWithOriginalActiveStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathWork tail.succ counterWidth ->
      RegistersWithFullRoundPathWork tail.succ counterWidth :=
  fun x =>
    fullRoundPathWorkKaliskiRoundConcreteStep
      tail counterWidth comparisonIndex historyIndex workIndex
      (fullRoundPathWorkOriginalActiveLatchStep tail counterWidth x)

/-- Base-gate program for the original-active-latched concrete outer route. -/
def fullRoundPathWorkKaliskiRoundWithOriginalActiveProgram
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical
      ((registersWithFullRoundPathWorkEncoding tail.succ counterWidth).width)).toQuantum :=
  UnitaryCircuit.seq
    (fullRoundPathWorkOriginalActiveLatchProgram tail counterWidth)
    (fullRoundPathWorkKaliskiRoundConcreteProgram
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The original-active-latched concrete route is realized by its composed
base-gate program. -/
theorem fullRoundPathWorkKaliskiRoundWithOriginalActive_realizes
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes
      (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
      (fullRoundPathWorkKaliskiRoundWithOriginalActiveProgram
        tail counterWidth comparisonIndex historyIndex workIndex)
      (fullRoundPathWorkKaliskiRoundWithOriginalActiveStep
        tail counterWidth comparisonIndex historyIndex workIndex) :=
  UnitaryCircuit.Realizes.seq
    (firstStep := fullRoundPathWorkOriginalActiveLatchStep tail counterWidth)
    (secondStep := fullRoundPathWorkKaliskiRoundConcreteStep
      tail counterWidth comparisonIndex historyIndex workIndex)
    (fullRoundPathWorkOriginalActiveLatch_realizes tail counterWidth)
    (fullRoundPathWorkKaliskiRoundConcrete_realizes
      tail counterWidth comparisonIndex historyIndex workIndex)

/-- The latched route has the same full-round component as the concrete outer
route on the original full-round input. -/
theorem fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_fullRound
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathWork tail.succ counterWidth) :
    (fullRoundPathWorkKaliskiRoundWithOriginalActiveStep
      tail counterWidth comparisonIndex historyIndex workIndex x).1 =
      fullRoundWorkKaliskiRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex x.1 := by
  rw [fullRoundPathWorkKaliskiRoundWithOriginalActiveStep,
    fullRoundPathWorkKaliskiRoundConcreteStep,
    liftFullRoundWorkStepToPathWork]
  rw [fullRoundPathWorkOriginalActiveLatchStep_fullRound]

/-- If the path bit starts clean, the latched route leaves the path bit equal
to the original active flag. -/
theorem fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_path_of_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathWork tail.succ counterWidth)
    (hclean : (fullRoundPathWorkPathBit tail counterWidth).get x = false) :
    (fullRoundPathWorkKaliskiRoundWithOriginalActiveStep
      tail counterWidth comparisonIndex historyIndex workIndex x).2 =
      (fullRoundPathWorkActiveBit tail counterWidth).get x := by
  rw [fullRoundPathWorkKaliskiRoundWithOriginalActiveStep]
  rw [fullRoundPathWorkKaliskiRoundConcreteStep_path]
  change
    (fullRoundPathWorkPathBit tail counterWidth).get
        (fullRoundPathWorkOriginalActiveLatchStep tail counterWidth x) =
      (fullRoundPathWorkActiveBit tail counterWidth).get x
  exact
    fullRoundPathWorkOriginalActiveLatchStep_path_of_clean
      tail counterWidth x hclean

/-- On standard clean path-work input, the latched route records the source
active flag in the path bit. -/
theorem fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_path_withClean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth) :
    (fullRoundPathWorkKaliskiRoundWithOriginalActiveStep
      tail counterWidth comparisonIndex historyIndex workIndex
      (withCleanFullRoundPathWork tail.succ counterWidth x)).2 = x.active := by
  rw [
    fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_path_of_clean
      tail counterWidth comparisonIndex historyIndex workIndex]
  · exact fullRoundPathWorkActiveBit_get_withClean tail counterWidth x
  · exact fullRoundPathWorkPathBit_get_withClean tail counterWidth x

/-- On clean active `v = 0` inputs, the concrete outer route agrees with the
active terminating endpoint. -/
theorem
    fullRoundWorkKaliskiRoundConcreteStep_cleanEndpoint_of_active_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundWorkKaliskiRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkKaliskiRoundConcreteStep]
  rw [
    fullRoundWorkActiveFalseControlledInactivePaddingStep_cleanActiveEndpoint
      tail counterWidth x hactive]
  exact
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_cleanEndpoint_of_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero hscratchA hscratchB

/-- On clean active `v = 0` inputs, the concrete outer route matches the
source terminating round on the source-state projection. -/
theorem
    fullRoundWorkKaliskiRoundConcreteStep_fromRegisters_eq_source_round_of_active_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkKaliskiRoundConcreteStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundWorkKaliskiRoundConcreteStep_cleanEndpoint_of_active_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero hscratchA hscratchB]
  let st :=
    RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps paddingSteps
  have hsourceActive : st.active = true := by
    simpa [st, RoundState.fromRegisters] using hactive
  have hsourceVZero : st.v = 0 := by
    simpa [st, RoundState.fromRegisters] using hvZero
  rw [RoundState.round_active_terminated st hsourceActive hsourceVZero]
  simp [st, RoundState.fromRegisters, hactive]

/-- On clean inactive `v ≠ 0` inputs, the concrete outer route has the inactive
padding endpoint. -/
theorem
    fullRoundWorkKaliskiRoundConcreteStep_cleanEndpoint_of_inactive_v_nonzero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvNonzero : x.v.val ≠ 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundWorkKaliskiRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      ((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth) := by
  rw [fullRoundWorkKaliskiRoundConcreteStep]
  exact
    fullRoundWorkInactivePaddingThenConcrete_cleanEndpoint_of_inactive_v_nonzero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero hscratchA hscratchB

/-- On clean active `v = 0` inputs, the original-active-latched path-work
route has the concrete terminating endpoint and records that the source state
was active. -/
theorem
    fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_cleanEndpoint_of_active_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundPathWorkKaliskiRoundWithOriginalActiveStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathWork tail.succ counterWidth x) =
      (((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        true) := by
  apply Prod.ext
  · rw [
      fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_fullRound]
    change
      fullRoundWorkKaliskiRoundConcreteStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth) =
        ((({ x with
            active := false,
            counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)
    exact
      fullRoundWorkKaliskiRoundConcreteStep_cleanEndpoint_of_active_v_zero
        tail counterWidth comparisonIndex historyIndex workIndex x hcompare
        hactive hvZero hscratchA hscratchB
  · rw [
      fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_path_withClean
        tail counterWidth comparisonIndex historyIndex workIndex x,
      hactive]

/-- On clean inactive `v ≠ 0` inputs, the original-active-latched path-work
route has the inactive padding endpoint and records that the source state was
inactive. -/
theorem
    fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_cleanEndpoint_of_inactive_v_nonzero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvNonzero : x.v.val ≠ 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundPathWorkKaliskiRoundWithOriginalActiveStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathWork tail.succ counterWidth x) =
      (((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false) := by
  apply Prod.ext
  · rw [
      fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_fullRound]
    change
      fullRoundWorkKaliskiRoundConcreteStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth) =
        ((({ x with counter := wordIncrement counterWidth x.counter },
            cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)
    exact
      fullRoundWorkKaliskiRoundConcreteStep_cleanEndpoint_of_inactive_v_nonzero
        tail counterWidth comparisonIndex historyIndex workIndex x hcompare
        hactive hvNonzero hscratchA hscratchB
  · rw [
      fullRoundPathWorkKaliskiRoundWithOriginalActiveStep_path_withClean
        tail counterWidth comparisonIndex historyIndex workIndex x,
      hactive]

/-- On clean active inputs, the path/control lifted active-false wrapper is a
no-op and preserves the explicit path/control bits. -/
theorem
    fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanActiveEndpoint
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (pathBit controlBit : Bool)
    (hactive : x.active = true) :
    fullRoundPathControlWorkActiveFalseInactivePaddingStep tail counterWidth
        (((((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth),
          pathBit),
          controlBit) =
      (((((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth),
        pathBit),
        controlBit) := by
  change
    ((fullRoundWorkActiveFalseControlledInactivePaddingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth),
      pathBit),
      controlBit) =
    (((((x, cleanComparisonWork tail.succ),
          cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
      pathBit),
      controlBit)
  rw [
    fullRoundWorkActiveFalseControlledInactivePaddingStep_cleanActiveEndpoint
      tail counterWidth x hactive]

/-- On clean active `v = 0` inputs, the path/control lifted terminating prefix
has the active terminating endpoint and preserves the explicit path/control
bits. -/
theorem
    fullRoundPathControlWorkTerminatingStep_cleanEndpoint_of_v_zero_active
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (pathBit controlBit : Bool)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0) :
    fullRoundPathControlWorkTerminatingStep tail counterWidth
        (((((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth),
          pathBit),
          controlBit) =
      ((((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        pathBit),
        controlBit) := by
  change
    ((fullRoundWorkTerminatingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth),
      pathBit),
      controlBit) =
      ((((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        pathBit),
        controlBit)
  rw [
    fullRoundWorkTerminatingStep_cleanEndpoint_of_v_zero
      tail counterWidth x hcompare hactive hvZero]

/-- On clean `v ≠ 0` inputs, the path/control lifted terminating prefix is a
no-op and preserves the explicit path/control bits. -/
theorem fullRoundPathControlWorkTerminatingStep_cleanEndpoint_of_v_nonzero
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (pathBit controlBit : Bool)
    (hcompare : x.compare = false) (hvNonzero : x.v.val ≠ 0) :
    fullRoundPathControlWorkTerminatingStep tail counterWidth
        (((((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth),
          pathBit),
          controlBit) =
      (((((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth),
        pathBit),
        controlBit) := by
  change
    ((fullRoundWorkTerminatingStep tail counterWidth
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth),
      pathBit),
      controlBit) =
      (((((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth),
        pathBit),
        controlBit)
  rw [
    fullRoundWorkTerminatingStep_cleanEndpoint_of_v_nonzero
      tail counterWidth x hcompare hvNonzero]

/-- On clean active `v = 0` inputs, the path/control concrete route has the
terminating endpoint and records that the source state was active. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_cleanEndpoint_of_active_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundPathControlWorkKaliskiRoundControlledStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        true),
        false) := by
  rw [fullRoundPathControlWorkKaliskiRoundControlledStep]
  rw [
    fullRoundPathControlWorkOriginalActiveLatchStep_cleanActiveEndpoint
      tail counterWidth x hactive]
  change
    fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundPathControlWorkTerminatingStep tail counterWidth
          (fullRoundPathControlWorkActiveFalseInactivePaddingStep
            tail counterWidth
            (((((x, cleanComparisonWork tail.succ),
                  cleanCoeffAdderWork tail.succ),
                cleanCounterIncrementWork counterWidth),
              true),
              false))) =
      ((((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        true),
        false)
  rw [
    fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanActiveEndpoint
      tail counterWidth x true false hactive]
  let terminated : RegistersWithFullRoundWork tail.succ counterWidth :=
    ((({ x with
        active := false,
        counter := wordIncrement counterWidth x.counter },
      cleanComparisonWork tail.succ),
      cleanCoeffAdderWork tail.succ),
      cleanCounterIncrementWork counterWidth)
  rw [
    fullRoundPathControlWorkTerminatingStep_cleanEndpoint_of_v_zero_active
      tail counterWidth x true false hcompare hactive hvZero]
  have hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get
          ((terminated, true), false) = true := by
    rfl
  have hwork :
      (fullRoundPathControlWorkControlWorkBit tail counterWidth).get
          ((terminated, true), false) = false := by
    rfl
  rw [
    fullRoundPathControlWorkOriginalActiveControlledBodyStep_eq_lifted_of_path_true
      tail counterWidth comparisonIndex historyIndex workIndex
      ((terminated, true), false) hpath hwork]
  change
    ((fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex terminated,
      true),
      false) =
    ((terminated, true), false)
  have hbody :
      fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
          tail counterWidth comparisonIndex historyIndex workIndex terminated =
        terminated := by
    have hactiveOnly :=
      fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_cleanEndpoint_of_v_zero
        tail counterWidth comparisonIndex historyIndex workIndex x hcompare
        hactive hvZero hscratchA hscratchB
    rw [fullRoundWorkKaliskiActiveOnlyRoundConcreteStep] at hactiveOnly
    rw [
      fullRoundWorkTerminatingStep_cleanEndpoint_of_v_zero
        tail counterWidth x hcompare hactive hvZero] at hactiveOnly
    exact hactiveOnly
  rw [hbody]

/-- On clean inactive `v ≠ 0` inputs, the path/control concrete route has the
inactive padding endpoint and records that the source state was inactive. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_cleanEndpoint_of_inactive_v_nonzero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvNonzero : x.v.val ≠ 0) :
    fullRoundPathControlWorkKaliskiRoundControlledStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with counter := wordIncrement counterWidth x.counter },
          cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false) := by
  rw [fullRoundPathControlWorkKaliskiRoundControlledStep]
  have hactiveBit :
      (fullRoundPathControlWorkActiveBit tail counterWidth).get
          (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
        false := by
    rw [fullRoundPathControlWorkActiveBit_get_withClean, hactive]
  rw [
    fullRoundPathControlWorkOriginalActiveLatchStep_eq_self_of_active_false
      tail counterWidth
      (withCleanFullRoundPathControlWork tail.succ counterWidth x)
      hactiveBit]
  rw [
    fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanInactiveEndpoint
      tail counterWidth x hactive]
  let padded : Registers tail.succ counterWidth :=
    { x with counter := wordIncrement counterWidth x.counter }
  have hcomparePadded : padded.compare = false := by
    simpa [padded] using hcompare
  have hvNonzeroPadded : padded.v.val ≠ 0 := by
    simpa [padded] using hvNonzero
  rw [
    fullRoundPathControlWorkTerminatingStep_cleanEndpoint_of_v_nonzero
      tail counterWidth padded false false hcomparePadded hvNonzeroPadded]
  change
    fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth padded) =
      (withCleanFullRoundPathWork tail.succ counterWidth padded, false)
  have hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get
          (withCleanFullRoundPathControlWork tail.succ counterWidth padded) =
        false :=
    fullRoundPathControlWorkPathBit_get_withClean tail counterWidth padded
  rw [
    fullRoundPathControlWorkOriginalActiveControlledBodyStep_eq_self_of_path_false
      tail counterWidth comparisonIndex historyIndex workIndex
      (withCleanFullRoundPathControlWork tail.succ counterWidth padded) hpath]
  rfl

/-- Semantic wrapper that runs the whole active-only round only when the
latched original-active path bit is true.  This is the control boundary needed
for the repeated fixed-round route: counter-mode inputs must not run the
terminating detector prefix after their padding-counter increment. -/
def fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  fun x =>
    if (fullRoundPathControlWorkPathBit tail counterWidth).get x then
      liftFullRoundWorkStepToPathControlWork tail.succ counterWidth
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex historyIndex workIndex) x
    else
      x

/-- If the latched original-active path bit is false, the semantic
active-only wrapper is a no-op. -/
theorem
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep_eq_self_of_path_false
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth)
    (hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get x = false) :
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      x := by
  simp [
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep,
    hpath]

/-- If the latched original-active path bit is true, the semantic active-only
wrapper runs the lifted active-only concrete round. -/
theorem
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep_eq_lifted_of_path_true
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth)
    (hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get x = true) :
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex x =
      liftFullRoundWorkStepToPathControlWork tail.succ counterWidth
        (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
          tail counterWidth comparisonIndex historyIndex workIndex) x := by
  simp [
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep,
    hpath]

/-- Source-shaped one-round route: latch the original mode flag, run
counter-padding on original counter-mode inputs, and run the whole active-only
round only on original Kaliski-mode inputs.  A later gate-level wrapper must
realize this control boundary without reusing one path bit across all rounds. -/
def fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  fun x =>
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep
      tail counterWidth comparisonIndex historyIndex workIndex
      (fullRoundPathControlWorkActiveFalseInactivePaddingStep tail counterWidth
        (fullRoundPathControlWorkOriginalActiveLatchStep tail counterWidth x))

/-- On clean active `v = 0` inputs, the mode-controlled semantic route runs
the active-only terminating round and records that the source state was active.
-/
theorem
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep_cleanEndpoint_of_active_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        true),
        false) := by
  rw [fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep]
  rw [
    fullRoundPathControlWorkOriginalActiveLatchStep_cleanActiveEndpoint
      tail counterWidth x hactive]
  change
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundPathControlWorkActiveFalseInactivePaddingStep
          tail counterWidth
          (((((x, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ),
              cleanCounterIncrementWork counterWidth),
            true),
            false)) =
      ((((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        true),
        false)
  rw [
    fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanActiveEndpoint
      tail counterWidth x true false hactive]
  let cleanInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (((x, cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
      cleanCounterIncrementWork counterWidth)
  change
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        ((cleanInput, true), false) =
      ((((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        true),
        false)
  have hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get
          ((cleanInput, true), false) = true := by
    rfl
  rw [
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep_eq_lifted_of_path_true
      tail counterWidth comparisonIndex historyIndex workIndex
      ((cleanInput, true), false) hpath]
  change
    ((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex cleanInput,
      true),
      false) =
    ((((({ x with
        active := false,
        counter := wordIncrement counterWidth x.counter },
      cleanComparisonWork tail.succ),
      cleanCoeffAdderWork tail.succ),
      cleanCounterIncrementWork counterWidth),
      true),
      false)
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_cleanEndpoint_of_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero hscratchA hscratchB]

/-- Short theorem name for the clean active-mode endpoint when the second
binary-GCD operand has reached zero. -/
theorem modeControlledSemanticActiveVZeroEndpoint
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        true),
        false) :=
  fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep_cleanEndpoint_of_active_v_zero
    tail counterWidth comparisonIndex historyIndex workIndex x hcompare hactive
    hvZero hscratchA hscratchB

/-- On clean active inputs, the mode-controlled semantic route reduces to the
lifted active-only concrete round and records that the source state was active.
-/
theorem
    modeControlledSemanticStep_eq_activeOnlyConcrete_clean_of_active
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = true) :
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth), true), false) := by
  rw [fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep]
  rw [
    fullRoundPathControlWorkOriginalActiveLatchStep_cleanActiveEndpoint
      tail counterWidth x hactive]
  change
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundPathControlWorkActiveFalseInactivePaddingStep
          tail counterWidth
          (((((x, cleanComparisonWork tail.succ),
                cleanCoeffAdderWork tail.succ),
              cleanCounterIncrementWork counterWidth),
            true),
            false)) =
      ((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth), true), false)
  rw [
    fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanActiveEndpoint
      tail counterWidth x true false hactive]
  let cleanInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (((x, cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
      cleanCounterIncrementWork counterWidth)
  change
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        ((cleanInput, true), false) =
      ((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex cleanInput,
      true),
      false)
  have hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get
          ((cleanInput, true), false) = true := by
    rfl
  rw [
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep_eq_lifted_of_path_true
      tail counterWidth comparisonIndex historyIndex workIndex
      ((cleanInput, true), false) hpath]
  rfl

/-- On clean inactive inputs, the mode-controlled semantic route runs only
counter-padding and skips the active-only terminating prefix. -/
theorem
    modeControlledSemanticStep_cleanEndpoint_of_inactive
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false) :
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false) := by
  rw [fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep]
  have hactiveBit :
      (fullRoundPathControlWorkActiveBit tail counterWidth).get
          (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
        false := by
    rw [fullRoundPathControlWorkActiveBit_get_withClean, hactive]
  rw [
    fullRoundPathControlWorkOriginalActiveLatchStep_eq_self_of_active_false
      tail counterWidth
      (withCleanFullRoundPathControlWork tail.succ counterWidth x)
      hactiveBit]
  rw [
    fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanInactiveEndpoint
      tail counterWidth x hactive]
  let padded : Registers tail.succ counterWidth :=
    { x with counter := wordIncrement counterWidth x.counter }
  change
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth padded) =
      ((((({ x with
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false)
  have hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get
          (withCleanFullRoundPathControlWork tail.succ counterWidth padded) =
        false :=
    fullRoundPathControlWorkPathBit_get_withClean tail counterWidth padded
  rw [
    fullRoundPathControlWorkOriginalActiveControlledActiveOnlySemanticStep_eq_self_of_path_false
      tail counterWidth comparisonIndex historyIndex workIndex
      (withCleanFullRoundPathControlWork tail.succ counterWidth padded) hpath]
  rfl

/-- On clean inactive `v = 0` inputs, the mode-controlled semantic route has
the inactive padding endpoint. -/
theorem
    modeControlledSemanticStep_cleanEndpoint_of_inactive_v_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false)
    (_hvZero : x.v.val = 0) :
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false) :=
  modeControlledSemanticStep_cleanEndpoint_of_inactive
    tail counterWidth comparisonIndex historyIndex workIndex x hactive

/-- On clean inactive `v ≠ 0` inputs, the mode-controlled semantic route has
the inactive padding endpoint. -/
theorem
    modeControlledSemanticStep_cleanEndpoint_of_inactive_v_nonzero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false)
    (_hvNonzero : x.v.val ≠ 0) :
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((((({ x with
          counter := wordIncrement counterWidth x.counter },
        cleanComparisonWork tail.succ),
        cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth),
        false),
        false) :=
  modeControlledSemanticStep_cleanEndpoint_of_inactive
    tail counterWidth comparisonIndex historyIndex workIndex x hactive

/-- Corrected semantic fixed-round schedule view of the path/control route:
the `roundIndex` selects the corresponding `m_i` history register slot.  This
does not claim a base-gate realization; it is the TeX-aligned semantic target
for the later gate-level controlled wrapper. -/
def fixedRoundModeControlledSemanticStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
    tail counterWidth comparisonIndex
    (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex

/-- Corrected semantic fixed-round schedule for the path/control route. -/
def fixedRoundModeControlledSemanticStepSchedule
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List (RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth) :=
  List.ofFn fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
    fixedRoundModeControlledSemanticStep
      tail counterWidth comparisonIndex roundIndex workIndex

@[simp] theorem
    fixedRoundModeControlledSemanticStepSchedule_length
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (fixedRoundModeControlledSemanticStepSchedule
      tail counterWidth comparisonIndex workIndex).length =
      2 * tail.succ := by
  simp [fixedRoundModeControlledSemanticStepSchedule]
  omega

/-- The `roundIndex`-th corrected semantic schedule entry uses the matching
`m_i` history register slot. -/
theorem
    fixedRoundModeControlledSemanticStepSchedule_get
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds) :
    (fixedRoundModeControlledSemanticStepSchedule
      tail counterWidth comparisonIndex workIndex).get
        ⟨roundIndex.val, by
          rw [
            fixedRoundModeControlledSemanticStepSchedule_length]
          exact roundIndex.isLt⟩ =
      fixedRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex roundIndex workIndex := by
  change
    (List.ofFn
      (fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
        fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex)).get
        ⟨roundIndex.val, by
          simp
          omega⟩ =
      fixedRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex roundIndex workIndex
  rw [List.get_ofFn]
  congr 1

/-- Folded corrected semantic shell for the fixed-round path/control route. -/
def fixedRoundModeControlledSemanticFoldStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  UnitaryCircuit.Realizes.stepList
    (fixedRoundModeControlledSemanticStepSchedule
      tail counterWidth comparisonIndex workIndex)

/-- Prefix shell for the corrected semantic fixed-round path/control route. -/
def fixedRoundModeControlledSemanticPrefixStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (rounds : Nat) :
    RegistersWithFullRoundPathControlWork tail.succ counterWidth ->
      RegistersWithFullRoundPathControlWork tail.succ counterWidth :=
  UnitaryCircuit.Realizes.stepList
    ((fixedRoundModeControlledSemanticStepSchedule
      tail counterWidth comparisonIndex workIndex).take rounds)

@[simp] theorem
    fixedRoundModeControlledSemanticPrefixStep_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth) :
    fixedRoundModeControlledSemanticPrefixStep
        tail counterWidth comparisonIndex workIndex 0 x = x := by
  rfl

/-- Prefix successor form for the corrected semantic fixed-round route. -/
theorem
    fixedRoundModeControlledSemanticPrefixStep_succ
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : RegistersWithFullRoundPathControlWork tail.succ counterWidth) :
    fixedRoundModeControlledSemanticPrefixStep
        tail counterWidth comparisonIndex workIndex
        (roundIndex.val + 1) x =
      fixedRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex roundIndex workIndex
        (fixedRoundModeControlledSemanticPrefixStep
          tail counterWidth comparisonIndex workIndex roundIndex.val x) := by
  unfold fixedRoundModeControlledSemanticPrefixStep
  let schedule :=
    fixedRoundModeControlledSemanticStepSchedule
      tail counterWidth comparisonIndex workIndex
  have hlen : roundIndex.val < schedule.length := by
    rw [
      fixedRoundModeControlledSemanticStepSchedule_length]
    exact roundIndex.isLt
  rw [UnitaryCircuit.Realizes.stepList_take_succ schedule roundIndex.val hlen]
  have hget :
      schedule.get ⟨roundIndex.val, hlen⟩ =
        fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex := by
    simpa [schedule] using
      fixedRoundModeControlledSemanticStepSchedule_get
        tail counterWidth comparisonIndex workIndex roundIndex
  rw [hget]

/-- The full corrected semantic prefix is the folded semantic shell. -/
theorem
    fixedRoundModeControlledSemanticPrefixStep_full
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    fixedRoundModeControlledSemanticPrefixStep
        tail counterWidth comparisonIndex workIndex
        (rnsl17MontgomerySchedule tail.succ).rounds =
      fixedRoundModeControlledSemanticFoldStep
        tail counterWidth comparisonIndex workIndex := by
  funext x
  unfold fixedRoundModeControlledSemanticPrefixStep
  unfold fixedRoundModeControlledSemanticFoldStep
  rw [List.take_of_length_le]
  rw [
    fixedRoundModeControlledSemanticStepSchedule_length]
  simp

/-- Register-shaped readout used for `RoundState.fromRegisters` projections of
the path/control route.  The path bit records whether the source state was
active; inactive-source paths restore the readout active flag to `false`.
This helper intentionally keeps the concrete counter output, because
`RoundState.fromRegisters` receives step counts as explicit parameters.  It is
a semantic readout projection: `compare`, `scratchA`, and `scratchB` are masked
to `false` in the readout, not asserted clean for the underlying route. -/
def fullRoundPathControlWorkRoundStateReadoutRegisters
    (n counterWidth : Nat)
    (x : RegistersWithFullRoundPathControlWork n counterWidth) :
    Registers n counterWidth :=
  let regs := x.1.1.1.1.1
  let readout :=
    { regs with
      compare := false
      scratchA := false
      scratchB := false }
  if x.1.2 then readout else { readout with active := false }

/-- The source-shaped readout may restore the active flag, but it does not
change any branch-history register slot. -/
theorem fullRoundPathControlWorkRoundStateReadoutRegisters_get_historyBit
    (n counterWidth : Nat) (observed : Fin (2 * n))
    (x : RegistersWithFullRoundPathControlWork n counterWidth) :
    (RegisterBits.historyBit n counterWidth observed).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          n counterWidth x) =
      (RegisterBits.historyBit n counterWidth observed).get x.1.1.1.1.1 := by
  unfold fullRoundPathControlWorkRoundStateReadoutRegisters
  by_cases hpath : x.1.2
  · simp [hpath, RegisterBits.historyBit_get]
  · simp [hpath, RegisterBits.historyBit_get]

@[simp] theorem fullRoundPathControlWorkRoundStateReadoutRegisters_compare
    (n counterWidth : Nat)
    (x : RegistersWithFullRoundPathControlWork n counterWidth) :
    (fullRoundPathControlWorkRoundStateReadoutRegisters
        n counterWidth x).compare =
      false := by
  unfold fullRoundPathControlWorkRoundStateReadoutRegisters
  by_cases hpath : x.1.2 <;> simp [hpath]

@[simp] theorem fullRoundPathControlWorkRoundStateReadoutRegisters_scratchA
    (n counterWidth : Nat)
    (x : RegistersWithFullRoundPathControlWork n counterWidth) :
    (fullRoundPathControlWorkRoundStateReadoutRegisters
        n counterWidth x).scratchA =
      false := by
  unfold fullRoundPathControlWorkRoundStateReadoutRegisters
  by_cases hpath : x.1.2 <;> simp [hpath]

@[simp] theorem fullRoundPathControlWorkRoundStateReadoutRegisters_scratchB
    (n counterWidth : Nat)
    (x : RegistersWithFullRoundPathControlWork n counterWidth) :
    (fullRoundPathControlWorkRoundStateReadoutRegisters
        n counterWidth x).scratchB =
      false := by
  unfold fullRoundPathControlWorkRoundStateReadoutRegisters
  by_cases hpath : x.1.2 <;> simp [hpath]

/-- On clean active `v = 0` inputs, the corrected semantic path/control route's
RoundState readout matches the source terminating round. -/
theorem
    modeControlledSemanticStep_roundStateReadout_active_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
            tail counterWidth comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep_cleanEndpoint_of_active_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero hscratchA hscratchB]
  let st :=
    RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps paddingSteps
  have hsourceActive : st.active = true := by
    simpa [st, RoundState.fromRegisters] using hactive
  have hsourceVZero : st.v = 0 := by
    simpa [st, RoundState.fromRegisters] using hvZero
  rw [RoundState.round_active_terminated st hsourceActive hsourceVZero]
  simp [fullRoundPathControlWorkRoundStateReadoutRegisters,
    st, RoundState.fromRegisters, hactive]

/-- On clean inactive inputs, the corrected semantic path/control route's
RoundState readout matches the source inactive padding round. -/
theorem
    modeControlledSemanticStep_roundStateReadout_inactive
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
            tail counterWidth comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    modeControlledSemanticStep_cleanEndpoint_of_inactive
      tail counterWidth comparisonIndex historyIndex workIndex x hactive]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = false := by
    simpa [RoundState.fromRegisters] using hactive
  rw [RoundState.round_inactive
    (RoundState.fromRegisters tail.succ counterWidth x
      kaliskiSteps paddingSteps) hsourceActive]
  simp [fullRoundPathControlWorkRoundStateReadoutRegisters,
    RoundState.fromRegisters, hactive]

/-- On clean active `v = 0` inputs, the corrected semantic path/control route's
selected history readout matches the terminating source branch-history bit. -/
theorem
    modeControlledSemanticStep_roundStateReadout_history_active_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
            tail counterWidth comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x))) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep_cleanEndpoint_of_active_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero hscratchA hscratchB]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).v = 0 := by
    simpa [RoundState.fromRegisters] using hvZero
  rw [
    RoundState.historyBit_active_terminated
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps) hsourceActive hsourceV]
  simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
    RoundState.fromRegisters, RegisterBits.historyBit_get] using hhistory

/-- On clean inactive inputs, the corrected semantic path/control route's
selected history readout matches the inactive source branch-history bit. -/
theorem
    modeControlledSemanticStep_roundStateReadout_history_inactive
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
            tail counterWidth comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x))) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    modeControlledSemanticStep_cleanEndpoint_of_inactive
      tail counterWidth comparisonIndex historyIndex workIndex x hactive]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = false := by
    simpa [RoundState.fromRegisters] using hactive
  rw [
    RoundState.historyBit_inactive
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps) hsourceActive]
  simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
    RoundState.fromRegisters, RegisterBits.historyBit_get] using hhistory

/-- On clean active `v = 0` inputs, the corrected semantic path/control route's
complete terminating readout matches the source round and selected history bit.
-/
theorem
    modeControlledSemanticStep_roundStateReadout_active_v_zero_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        kaliskiSteps (paddingSteps + 1)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  dsimp only
  exact ⟨
    modeControlledSemanticStep_roundStateReadout_active_v_zero
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hcompare hactive hvZero hscratchA hscratchB,
    modeControlledSemanticStep_roundStateReadout_history_active_v_zero
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hcompare hactive hvZero hscratchA hscratchB
      hhistory⟩

/-- On clean inactive inputs, the corrected semantic path/control route's
complete readout matches the inactive source round and selected history bit. -/
theorem
    modeControlledSemanticStep_roundStateReadout_inactive_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        kaliskiSteps (paddingSteps + 1)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  dsimp only
  exact ⟨
    modeControlledSemanticStep_roundStateReadout_inactive
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hactive,
    modeControlledSemanticStep_roundStateReadout_history_inactive
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hactive hhistory⟩

/-- Corrected semantic fixed-round wrapper for a clean active terminating slot.
The history register is the slot selected by `roundIndex`. -/
theorem
    fixedRoundModeControlledSemanticStep_roundStateReadout_active_v_zero_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        kaliskiSteps (paddingSteps + 1)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  simpa [fixedRoundModeControlledSemanticStep] using
    modeControlledSemanticStep_roundStateReadout_active_v_zero_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x
      hcompare hactive hvZero hscratchA hscratchB hhistory

/-- Corrected semantic fixed-round wrapper for a clean inactive slot.  The
result is independent of whether `v` is zero. -/
theorem
    fixedRoundModeControlledSemanticStep_roundStateReadout_inactive_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hactive : x.active = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        kaliskiSteps (paddingSteps + 1)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  simpa [fixedRoundModeControlledSemanticStep] using
    modeControlledSemanticStep_roundStateReadout_inactive_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x
      hactive hhistory

/-- On clean active `v = 0` inputs, the path/control route's RoundState readout
matches the source terminating round. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_active_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_cleanEndpoint_of_active_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero hscratchA hscratchB]
  let st :=
    RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps paddingSteps
  have hsourceActive : st.active = true := by
    simpa [st, RoundState.fromRegisters] using hactive
  have hsourceVZero : st.v = 0 := by
    simpa [st, RoundState.fromRegisters] using hvZero
  rw [RoundState.round_active_terminated st hsourceActive hsourceVZero]
  simp [fullRoundPathControlWorkRoundStateReadoutRegisters,
    st, RoundState.fromRegisters, hactive]

/-- On clean inactive `v = 0` inputs, the path/control route's RoundState
readout restores the source inactive mode even though the reversible route keeps
distinct concrete state from the active terminating input. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvZero : x.v.val = 0) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_cleanEndpoint_of_inactive_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = false := by
    simpa [RoundState.fromRegisters] using hactive
  rw [RoundState.round_inactive
    (RoundState.fromRegisters tail.succ counterWidth x
      kaliskiSteps paddingSteps) hsourceActive]
  simp [fullRoundPathControlWorkRoundStateReadoutRegisters,
    RoundState.fromRegisters, hactive]

/-- On clean inactive `v ≠ 0` inputs, the path/control route's RoundState
readout matches the source inactive padding round. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_v_nonzero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvNonzero : x.v.val ≠ 0) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_cleanEndpoint_of_inactive_v_nonzero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = false := by
    simpa [RoundState.fromRegisters] using hactive
  rw [RoundState.round_inactive
    (RoundState.fromRegisters tail.succ counterWidth x
      kaliskiSteps paddingSteps) hsourceActive]
  simp [fullRoundPathControlWorkRoundStateReadoutRegisters,
    RoundState.fromRegisters, hactive]

/-- On clean active `v = 0` inputs, the path/control route's selected history
readout matches the terminating source branch-history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_active_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x))) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_cleanEndpoint_of_active_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero hscratchA hscratchB]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = true := by
    simpa [RoundState.fromRegisters] using hactive
  have hsourceV :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).v = 0 := by
    simpa [RoundState.fromRegisters] using hvZero
  rw [
    RoundState.historyBit_active_terminated
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps) hsourceActive hsourceV]
  simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
    RoundState.fromRegisters, RegisterBits.historyBit_get] using hhistory

/-- On clean inactive `v = 0` inputs, the path/control route's selected history
readout matches the inactive source branch-history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_inactive_v_zero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvZero : x.v.val = 0)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x))) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_cleanEndpoint_of_inactive_v_zero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvZero]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = false := by
    simpa [RoundState.fromRegisters] using hactive
  rw [
    RoundState.historyBit_inactive
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps) hsourceActive]
  simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
    RoundState.fromRegisters, RegisterBits.historyBit_get] using hhistory

/-- On clean inactive `v ≠ 0` inputs, the path/control route's selected history
readout matches the inactive source branch-history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_inactive_v_nonzero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvNonzero : x.v.val ≠ 0)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x))) =
      RoundState.historyBit
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_cleanEndpoint_of_inactive_v_nonzero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = false := by
    simpa [RoundState.fromRegisters] using hactive
  rw [
    RoundState.historyBit_inactive
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps) hsourceActive]
  simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
    RoundState.fromRegisters, RegisterBits.historyBit_get] using hhistory

/-- On clean active `v = 0` inputs, the path/control route's complete
terminating readout matches the source round and selected history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_active_v_zero_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvZero : x.v.val = 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        kaliskiSteps (paddingSteps + 1)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  dsimp only
  exact ⟨
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_active_v_zero
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hcompare hactive hvZero hscratchA hscratchB,
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_active_v_zero
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hcompare hactive hvZero hscratchA hscratchB
      hhistory⟩

/-- On clean inactive `v = 0` inputs, the path/control route's complete readout
matches the inactive source round and selected history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_v_zero_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvZero : x.v.val = 0)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        kaliskiSteps (paddingSteps + 1)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  dsimp only
  exact ⟨
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_v_zero
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hcompare hactive hvZero,
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_inactive_v_zero
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hcompare hactive hvZero hhistory⟩

/-- On clean inactive `v ≠ 0` inputs, the path/control route's complete readout
matches the inactive source round and selected history bit. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_nonzero_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvNonzero : x.v.val ≠ 0)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        kaliskiSteps (paddingSteps + 1)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  dsimp only
  exact ⟨
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_v_nonzero
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hcompare hactive hvNonzero,
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_inactive_v_nonzero
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hcompare hactive hvNonzero hhistory⟩

/-- On clean inactive inputs, the path/control route's complete readout matches
the inactive source round and selected history bit, regardless of `v`. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        kaliskiSteps (paddingSteps + 1)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  by_cases hvZero : x.v.val = 0
  · exact
      fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_v_zero_complete
        tail counterWidth kaliskiSteps paddingSteps comparisonIndex
        historyIndex workIndex x hcompare hactive hvZero hhistory
  · exact
      fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_nonzero_complete
        tail counterWidth kaliskiSteps paddingSteps comparisonIndex
        historyIndex workIndex x hcompare hactive hvZero hhistory

/-- On clean active `v ≠ 0` inputs, the path/control route reduces to the
existing concrete active-only route and records that the source state was
active.  The active-only route carries the branch-specific active-nonzero
source-readout facts. -/
theorem
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false) (hactive : x.active = true)
    (hvNonzero : x.v.val ≠ 0) :
    fullRoundPathControlWorkKaliskiRoundControlledStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      ((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth), true), false) := by
  rw [fullRoundPathControlWorkKaliskiRoundControlledStep]
  rw [
    fullRoundPathControlWorkOriginalActiveLatchStep_cleanActiveEndpoint
      tail counterWidth x hactive]
  change
    fullRoundPathControlWorkOriginalActiveControlledBodyStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (fullRoundPathControlWorkTerminatingStep tail counterWidth
          (fullRoundPathControlWorkActiveFalseInactivePaddingStep
            tail counterWidth
            (((((x, cleanComparisonWork tail.succ),
                  cleanCoeffAdderWork tail.succ),
                cleanCounterIncrementWork counterWidth),
              true),
              false))) =
      ((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth), true), false)
  rw [
    fullRoundPathControlWorkActiveFalseInactivePaddingStep_cleanActiveEndpoint
      tail counterWidth x true false hactive]
  rw [
    fullRoundPathControlWorkTerminatingStep_cleanEndpoint_of_v_nonzero
      tail counterWidth x true false hcompare hvNonzero]
  let cleanInput : RegistersWithFullRoundWork tail.succ counterWidth :=
    (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
      cleanCounterIncrementWork counterWidth)
  have hpath :
      (fullRoundPathControlWorkPathBit tail counterWidth).get
          ((cleanInput, true), false) = true := by
    rfl
  have hwork :
      (fullRoundPathControlWorkControlWorkBit tail counterWidth).get
          ((cleanInput, true), false) = false := by
    rfl
  rw [
    fullRoundPathControlWorkOriginalActiveControlledBodyStep_eq_lifted_of_path_true
      tail counterWidth comparisonIndex historyIndex workIndex
      ((cleanInput, true), false) hpath hwork]
  change
    ((fullRoundWorkActiveOddOddLatchThenSelectedOrCompareCarriedDispatchStep
        tail counterWidth comparisonIndex historyIndex workIndex cleanInput,
      true),
      false) =
    ((fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex cleanInput,
      true),
      false)
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero]

/-- On clean inactive `v ≠ 0` inputs, the concrete outer route matches the
source inactive round on the source-state projection. -/
theorem
    fullRoundWorkKaliskiRoundConcreteStep_fromRegisters_eq_source_round_of_inactive_v_nonzero
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hvNonzero : x.v.val ≠ 0)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false) :
    RoundState.fromRegisters tail.succ counterWidth
        (fullRoundWorkKaliskiRoundConcreteStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (((x, cleanComparisonWork tail.succ),
              cleanCoeffAdderWork tail.succ),
            cleanCounterIncrementWork counterWidth)).1.1.1
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps) := by
  rw [
    fullRoundWorkKaliskiRoundConcreteStep_cleanEndpoint_of_inactive_v_nonzero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero hscratchA hscratchB]
  have hsourceActive :
      (RoundState.fromRegisters tail.succ counterWidth x
        kaliskiSteps paddingSteps).active = false := by
    simpa [RoundState.fromRegisters] using hactive
  rw [RoundState.round_inactive
    (RoundState.fromRegisters tail.succ counterWidth x
      kaliskiSteps paddingSteps) hsourceActive]
  simp [RoundState.fromRegisters, hactive]

/-- In the active nonzero low-`u` false case, the concrete active-only route on
clean full-round work agrees with the active-nonzero semantic wrapper. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hvNonzero : x.v.val ≠ 0)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) =
        false) :
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) := by
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero]
  exact
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_activeNonzero_of_uLow_false
      tail counterWidth comparisonIndex historyIndex workIndex
      (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
      (fullRoundWorkCounterCarryInBit_get_clean tail counterWidth x)
      (fullRoundWorkCounterCarryWorkBit_get_clean
        tail counterWidth workIndex x)
      huLow

/-- In the active nonzero low-`u` true and low-`v` false case, the concrete
active-only route on clean full-round work agrees with the active-nonzero
semantic wrapper. -/
theorem
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_true_vLow_false_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hvNonzero : x.v.val ≠ 0)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) =
        true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) =
        false) :
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) =
      fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth) := by
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeLatchBody_of_v_nonzero_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero]
  exact
    fullRoundWorkActiveOddOddLatchThenBodyStep_eq_activeNonzero_of_uLow_true_vLow_false
      tail counterWidth comparisonIndex historyIndex workIndex
      (((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ),
        cleanCounterIncrementWork counterWidth)
      (fullRoundWorkCounterCarryInBit_get_clean tail counterWidth x)
      (fullRoundWorkCounterCarryWorkBit_get_clean
        tail counterWidth workIndex x)
      huLow hvLow

end
end MK
end MAU.Inversion
end QuantumAlg

end
