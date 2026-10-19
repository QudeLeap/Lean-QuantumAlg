/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.Readout.Round
import all QuantumAlg.Util.NumberTheory.Binary.GCD.Trace

/-!
# Trace readout

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
namespace Trace

open QuantumAlg.MAU.Inversion
open QuantumAlg.MAU.Inversion.MK
open QuantumAlg.Nat.FixedWidth

/-- The canonical trace start agrees with the clean finite register seed
readout. -/
lemma ofInput_start_eq_fromRegisters_initialRegisters
    (n counterWidth : Nat) (p x : Word n) :
    (ofInput n p.val x.val).start =
      RoundState.fromRegisters n counterWidth
        (initialRegisters n counterWidth p x) 0 0 := by
  rw [RoundState.fromRegisters_initialRegisters]
  rfl

end Trace
end NumberTheory.BinaryGCD
end QuantumAlg

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-- The selected branch-code/history/aux-shift dispatch preserves `v` in the
`uEven` source branch, matching the source-level fixed round. -/
lemma
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_v_uEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  let staged :=
    coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
        true := by
    rw [Branch.fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint]
    simp [huLow]
  have hwrittenV : written.1.1.v = x.1.1.v := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_v]
    exact coeffWorkSelectedBranchCodeToScratchStep_get_v
      tail counterWidth tempIndex x
  have hword :=
    coeffWorkUDiv2ThenSMul2Step_get_v tail.succ counterWidth written
  have hdispatch :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
      hactive haux
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  rw [hdispatch]
  change (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.v.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
        paddingSteps)).v
  rw [hword, hwrittenV, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The selected branch-code/history/aux-shift dispatch preserves `r` in the
`uEven` source branch, matching the source-level fixed round. -/
lemma
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_rCoeff_uEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  let staged :=
    coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
        true := by
    rw [Branch.fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint]
    simp [huLow]
  have hwrittenR : written.1.1.rCoeff = x.1.1.rCoeff := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_rCoeff]
    exact coeffWorkSelectedBranchCodeToScratchStep_get_rCoeff
      tail counterWidth tempIndex x
  have hword :=
    coeffWorkUDiv2ThenSMul2Step_get_rCoeff tail.succ counterWidth written
  have hdispatch :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
      hactive haux
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.u.val huEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
  rw [hdispatch]
  change
      (coeffWorkUDiv2ThenSMul2Step
        tail.succ counterWidth written).1.1.rCoeff.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
        paddingSteps)).rCoeff
  rw [hword, hwrittenR, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The selected branch-code/history/aux-shift dispatch preserves `u` in the
`vEven` source branch, matching the source-level fixed round. -/
lemma
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_u_vEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  let staged :=
    coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
        false := by
    rw [Branch.fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint]
    simp [huLow, hvLow]
  have hwrittenU : written.1.1.u = x.1.1.u := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_u]
    exact coeffWorkSelectedBranchCodeToScratchStep_get_u
      tail counterWidth tempIndex x
  have hword :=
    coeffWorkVDiv2ThenRMul2Step_get_u tail.succ counterWidth written
  have hdispatch :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
      hactive haux
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  rw [hdispatch]
  change (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.u.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
        paddingSteps)).u
  rw [hword, hwrittenU, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The selected branch-code/history/aux-shift dispatch preserves `s` in the
`vEven` source branch, matching the source-level fixed round. -/
lemma
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_sCoeff_vEven_eq_source_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  let staged :=
    coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
        false := by
    rw [Branch.fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint]
    simp [huLow, hvLow]
  have hwrittenS : written.1.1.sCoeff = x.1.1.sCoeff := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_sCoeff]
    exact coeffWorkSelectedBranchCodeToScratchStep_get_sCoeff
      tail counterWidth tempIndex x
  have hword :=
    coeffWorkVDiv2ThenRMul2Step_get_sCoeff tail.succ counterWidth written
  have hdispatch :=
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
      tail counterWidth tempIndex historyIndex x hscratchA hscratchB htemp
      hactive haux
  have hactiveField : x.1.1.active = true := by
    change x.1.1.active = true at hactive
    exact hactive
  have huMod : x.1.1.u.val % 2 ≠ 0 :=
    Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.1.1.u.val huOdd
  have hvMod : x.1.1.v.val % 2 = 0 :=
    Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false x.1.1.v.val hvEven
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vEven
          (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vEven
    · change x.1.1.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact hvNonzero
    · dsimp [RoundState.fromRegisters]
      exact huMod
    · dsimp [RoundState.fromRegisters]
      exact hvMod
  rw [hdispatch]
  change
      (coeffWorkVDiv2ThenRMul2Step
        tail.succ counterWidth written).1.1.sCoeff.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
        paddingSteps)).sCoeff
  rw [hword, hwrittenS, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The carried selected-odd dispatch preserves `v` in the `uGreater` source
branch, matching the source-level fixed round. -/
lemma coeffWorkSelectedOddCarriedDispatch_get_v_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkActiveBranchCodeToScratchStep tail.succ counterWidth
      Branch.uGreater selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hselectedV : selected.1.1.v = x.v := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_v_clean_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hlt
        hcontrolWork
  have hstagedV : staged.1.1.v = x.v := by
    dsimp [staged]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_v, hselectedV]
  have hwrittenV : written.1.1.v = x.v := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_v, hstagedV]
  have hword := coeffWorkUDiv2ThenSMul2Step_get_v
    tail.succ counterWidth written
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_uGreater
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hlt
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt hcontrolWork hactiveCoeff]
  change (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.v.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps)).v
  rw [hword, hwrittenV, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The carried selected-odd dispatch preserves `u` in the `vLe` source
branch, matching the source-level fixed round. -/
lemma coeffWorkSelectedOddCarriedDispatch_get_u_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkActiveBranchCodeToScratchStep tail.succ counterWidth Branch.vLe
      selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  have hselectedU : selected.1.1.u = x.u := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_u_clean_not_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hnlt
        hcontrolWork
  have hstagedU : staged.1.1.u = x.u := by
    dsimp [staged]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_u, hselectedU]
  have hwrittenU : written.1.1.u = x.u := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_u, hstagedU]
  have hword := coeffWorkVDiv2ThenRMul2Step_get_u
    tail.succ counterWidth written
  have hactiveField : x.active = true :=
    activeBit_get_eq_active tail.succ counterWidth x ▸ hactive
  have hround :
      RoundState.round
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
            paddingSteps) := by
    apply RoundState.round_active_nonzero_vLe
    · change x.active = true
      exact hactiveField
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.u.val huOdd
    · dsimp [RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true x.v.val hvOdd
    · dsimp [RoundState.fromRegisters]
      exact hnlt
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt hcontrolWork hactiveCoeff]
  change (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.u.val =
    (RoundState.round
      (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps)).u
  rw [hword, hwrittenU, hround]
  simp [RoundState.applyBranch, RoundState.fromRegisters]

/-- The nonzero-active selected wrapper's `uEven` `v` readout agrees with the
source-level fixed round. -/
lemma
    coeffWorkKaliskiActiveNonzeroRoundStep_get_v_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_v_uEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvNonzero huEven

/-- The nonzero-active selected wrapper's `uEven` `r` readout agrees with the
source-level fixed round. -/
lemma
    coeffWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_rCoeff_uEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvNonzero huEven

/-- The nonzero-active selected wrapper's `vEven` `u` readout agrees with the
source-level fixed round. -/
lemma
    coeffWorkKaliskiActiveNonzeroRoundStep_get_u_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_u_vEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvLow hvNonzero huOdd
      hvEven

/-- The nonzero-active selected wrapper's `vEven` `s` readout agrees with the
source-level fixed round. -/
lemma
    coeffWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex x).1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_evenDispatch_of_u_lsb_true_v_lsb_false
      tail counterWidth comparisonIndex historyIndex x huLow hvLow]
  exact
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_sCoeff_vEven_eq_source_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvLow hvNonzero huOdd
      hvEven

/-- The nonzero-active selected wrapper's odd `uGreater` `v` readout agrees
with the source-level fixed round. -/
lemma
    coeffWorkKaliskiActiveNonzeroRoundStep_get_v_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_v_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huOdd hvOdd hlt hcontrolWork

/-- The nonzero-active selected wrapper's odd `vLe` `u` readout agrees with the
source-level fixed round. -/
lemma
    coeffWorkKaliskiActiveNonzeroRoundStep_get_u_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  rw [
    coeffWorkKaliskiActiveNonzeroRoundStep_eq_carriedOddDispatch_of_lsb_true
      tail counterWidth comparisonIndex historyIndex
      ((x, cleanComparisonWork tail.succ), work) huLow hvLow]
  exact
    coeffWorkSelectedOddCarriedDispatch_get_u_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huOdd hvOdd hnlt hcontrolWork

/-- The lifted nonzero-active selected wrapper's `uEven` `v` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_v_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvNonzero huEven

/-- The lifted nonzero-active selected wrapper's `uEven` `r` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvNonzero huEven

/-- The lifted nonzero-active selected wrapper's `vEven` `u` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_u_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvLow hvNonzero huOdd hvEven

/-- The lifted nonzero-active selected wrapper's `vEven` `s` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x hscratchA hscratchB htemp hactive huLow hvLow hvNonzero huOdd hvEven

/-- The lifted nonzero-active selected wrapper's odd `uGreater` `v` readout
agrees with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_v_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huLow hvLow huOdd hvOdd hlt
      hcontrolWork

/-- The lifted nonzero-active selected wrapper's odd `vLe` `u` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (fullRoundWorkKaliskiActiveNonzeroRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  simpa [fullRoundWorkKaliskiActiveNonzeroRoundStep] using
    coeffWorkKaliskiActiveNonzeroRoundStep_get_u_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work hscratchA hcompare hfinal hactive huLow hvLow huOdd hvOdd hnlt
      hcontrolWork

/-- In the nonzero `uEven` branch, the active-only selector's `v` readout
agrees with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_v_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive huLow hvNonzero huEven

/-- In the nonzero `uEven` branch, the active-only selector's `r` readout
agrees with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_rCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive huLow hvNonzero huEven

/-- In the nonzero `vEven` branch, the active-only selector's `u` readout
agrees with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_u_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive huLow hvLow hvNonzero
      huOdd hvEven

/-- In the nonzero `vEven` branch, the active-only selector's `s` readout
agrees with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_sCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex (x, counterWork)
    hvNonzero]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x counterWork hscratchA hscratchB htemp hactive huLow hvLow hvNonzero
      huOdd hvEven

/-- In the nonzero odd `uGreater` branch, the active-only selector's `v`
readout agrees with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_v_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow
      huOdd hvOdd hlt hcontrolWork

/-- In the nonzero odd `vLe` branch, the active-only selector's `u` readout
agrees with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundStep_get_u_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  rw [fullRoundWorkKaliskiActiveOnlyRoundStep_eq_activeNonzero_of_v_nonzero
    tail counterWidth comparisonIndex historyIndex
    (((x, cleanComparisonWork tail.succ), work), counterWork)
    (Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd)]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x work counterWork hscratchA hcompare hfinal hactive huLow hvLow
      huOdd hvOdd hnlt hcontrolWork

/-- In the nonzero `uEven` branch, the active/inactive semantic selector's `v`
readout agrees with the source-level fixed round. -/
lemma fullRoundWorkKaliskiRoundStep_get_v_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).v := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_v_uEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive huLow
        hvNonzero huEven
  · exact hactive

/-- In the nonzero `uEven` branch, the active/inactive semantic selector's `r`
readout agrees with the source-level fixed round. -/
lemma fullRoundWorkKaliskiRoundStep_get_rCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huEven : x.1.1.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).rCoeff := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_rCoeff_uEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive huLow
        hvNonzero huEven
  · exact hactive

/-- In the nonzero `vEven` branch, the active/inactive semantic selector's `u`
readout agrees with the source-level fixed round. -/
lemma fullRoundWorkKaliskiRoundStep_get_u_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).u := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_u_vEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive huLow
        hvLow hvNonzero huOdd hvEven
  · exact hactive

/-- In the nonzero `vEven` branch, the active/inactive semantic selector's `s`
readout agrees with the source-level fixed round. -/
lemma fullRoundWorkKaliskiRoundStep_get_sCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get x = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x = false)
    (hvNonzero : x.1.1.v.val ≠ 0)
    (huOdd : x.1.1.u.val.testBit (0 : Nat) = true)
    (hvEven : x.1.1.v.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex (x, counterWork)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.1.1 kaliskiSteps
          paddingSteps)).sCoeff := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_sCoeff_vEven_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x counterWork hscratchA hscratchB htemp hactive huLow
        hvLow hvNonzero huOdd hvEven
  · exact hactive

/-- In the nonzero odd `uGreater` branch, the active/inactive semantic
selector's `v` readout agrees with the source-level fixed round. -/
lemma fullRoundWorkKaliskiRoundStep_get_v_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_v_uGreater_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hcompare hfinal hactive
        huLow hvLow huOdd hvOdd hlt hcontrolWork
  · exact hactive

/-- In the nonzero odd `vLe` branch, the active/inactive semantic selector's
`u` readout agrees with the source-level fixed round. -/
lemma fullRoundWorkKaliskiRoundStep_get_u_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (counterWork : CounterIncrementWork counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (fullRoundWorkKaliskiRoundStep tail counterWidth
        comparisonIndex historyIndex
        (((x, cleanComparisonWork tail.succ), work), counterWork)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  rw [fullRoundWorkKaliskiRoundStep_eq_activeOnly_of_active]
  · exact
      fullRoundWorkKaliskiActiveOnlyRoundStep_get_u_vLe_eq_sourceRound_clean
        tail counterWidth comparisonIndex historyIndex kaliskiSteps
        paddingSteps x work counterWork hscratchA hcompare hfinal hactive
        huLow hvLow huOdd hvOdd hnlt hcontrolWork
  · exact hactive

/-- In the concrete active-only nonzero `uEven` branch, the `v` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_v_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff huLow hvNonzero huEven

/-- In the concrete active-only nonzero `uEven` branch, the `r` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_uEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.rCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).rCoeff := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_rCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff huLow hvNonzero huEven

/-- In the concrete active-only nonzero `vEven` branch, the `u` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_true_vLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow hvLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_u_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff huLow hvLow hvNonzero huOdd
      hvEven

/-- In the concrete active-only nonzero `vEven` branch, the `s` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_vEven_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.sCoeff.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).sCoeff := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvEven
  have hscratchACoeff :
      (coeffAdderScratchABit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchA = false
    exact hscratchA
  have hscratchBCoeff :
      (coeffAdderScratchBBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change x.scratchB = false
    exact hscratchB
  have htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth
        comparisonIndex).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false := by
    change
      (liftedComparisonCarryBit tail.succ counterWidth comparisonIndex).get
        (x, cleanComparisonWork tail.succ) = false
    change
      (comparisonCarryValueBit tail.succ comparisonIndex).get
        (cleanComparisonWork tail.succ) = false
    simp
  have hactiveCoeff :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get x = true
    exact hactive
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_eq_activeNonzero_of_uLow_true_vLow_false_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hvNonzero huLow hvLow]
  exact
    fullRoundWorkKaliskiActiveNonzeroRoundStep_get_sCoeff_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      ((x, cleanComparisonWork tail.succ), cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchACoeff
      hscratchBCoeff htemp hactiveCoeff huLow hvLow hvNonzero huOdd
      hvEven

/-- In the concrete active-only odd `uGreater` branch, the `v` readout agrees
with the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_uGreater_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.v.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).v := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false :=
    liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_v_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
      hactive huLow hvLow huOdd hvOdd hlt hcontrolWork

/-- In the concrete active-only odd `vLe` branch, the `u` readout agrees with
the source-level fixed round. -/
lemma
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_vLe_eq_sourceRound_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (kaliskiSteps paddingSteps : Nat)
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val) :
    (fullRoundWorkKaliskiActiveOnlyRoundConcreteStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ),
          cleanCounterIncrementWork counterWidth)).1.1.1.u.val =
      (RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
          paddingSteps)).u := by
  have huLow :
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderUBit_get_littleEndian_zero]
    exact huOdd
  have hvLow :
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = true := by
    rw [coeffAdderVBit_get_littleEndian_zero]
    exact hvOdd
  have hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ),
            cleanCoeffAdderWork tail.succ) = false :=
    liftedCoeffAdderCarryInBit_get_clean tail.succ counterWidth
      (x, cleanComparisonWork tail.succ)
  rw [
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_coeffState_eq_kaliskiRound_clean_not_lt
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hfinal hscratchA hactive huOdd hvOdd hnlt]
  exact
    fullRoundWorkKaliskiRoundStep_get_u_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex kaliskiSteps paddingSteps
      x (cleanCoeffAdderWork tail.succ)
      (cleanCounterIncrementWork counterWidth) hscratchA hcompare hfinal
      hactive huLow hvLow huOdd hvOdd hnlt hcontrolWork

/-- On clean active `uEven` inputs, the path/control route's four source data
readouts match the source active Kaliski round. -/
lemma
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uEven_full
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps
    let sourceRound :=
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff := by
  dsimp only
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have huRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit hvNonzero
      huEven
  have hvRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit hvNonzero
      huEven
  have hrRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit hvNonzero
      huEven
  have hsRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_uEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit hvNonzero
      huEven hmsb hdouble
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using huRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hvRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hrRead
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hsRead

/-- On clean active `vEven` inputs, the path/control route's four source data
readouts match the source active Kaliski round. -/
lemma
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vEven_full
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps
    let sourceRound :=
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff := by
  dsimp only
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have huRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit huOdd
      hvEven hvNonzero
  have hvRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit huOdd
      hvEven hvNonzero
  have hrRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit huOdd
      hvEven hvNonzero hmsb hdouble
  have hsRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_vEven_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hscratchB hcompare hactiveBit huOdd
      hvEven hvNonzero
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using huRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hvRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hrRead
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hsRead

/-- On clean active odd `uGreater` inputs, the path/control route's four source
data readouts match the source active Kaliski round. -/
lemma
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uGreater_full
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps
    let sourceRound :=
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff := by
  dsimp only
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have huRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hlt
      hlsb
  have hvRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hlt
  have hrRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hlt
      hadd
  have hsRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_uGreater_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hlt
      hmsb hdouble
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using huRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hvRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hrRead
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hsRead

/-- On clean active odd `vLe` inputs, the path/control route's four source data
readouts match the source active Kaliski round. -/
lemma
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vLe_full
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
            comparisonIndex historyIndex workIndex
            (withCleanFullRoundPathControlWork tail.succ counterWidth x)))
        (kaliskiSteps + 1) paddingSteps
    let sourceRound :=
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x
          kaliskiSteps paddingSteps)
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff := by
  dsimp only
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  have hactiveBit :
      (RegisterBits.activeBit tail.succ counterWidth).get x = true := by
    simpa [RegisterBits.activeBit_get] using hactive
  have huRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_u_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hnlt
  have hvRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_v_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hnlt
      hlsb
  have hrRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_rCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hnlt
      hmsb hdouble
  have hsRead :=
    fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_sCoeff_vLe_eq_sourceRound_clean
      tail counterWidth comparisonIndex historyIndex workIndex kaliskiSteps
      paddingSteps x hscratchA hcompare hfinal hactiveBit huOdd hvOdd hnlt
      hadd
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using huRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hvRead
  constructor
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hrRead
  · simpa [fullRoundPathControlWorkRoundStateReadoutRegisters,
      RoundState.fromRegisters] using hsRead

/-- On clean active `uEven` inputs, the path/control route's complete branch
readout matches the source round's data/metadata and selected branch-history
bit. -/
lemma
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uEven_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  dsimp only
  have hdata :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uEven_full
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hscratchB hcompare hactive
      hvNonzero huEven hmsb hdouble
  have hmetadata :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_active_nonzero_metadata
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hcompare hfinal hactive
      hvNonzero
  have hhistoryRead :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_uEven
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hscratchB hcompare hactive
      hhistory hvNonzero huEven
  dsimp only at hdata
  rcases hdata with ⟨hu, hv, hr, hs⟩
  rcases hmetadata with ⟨ha, hk, hp⟩
  exact ⟨hu, hv, hr, hs, ha, hk, hp, hhistoryRead⟩

/-- On clean active `vEven` inputs, the path/control route's complete branch
readout matches the source round's data/metadata and selected branch-history
bit. -/
lemma
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vEven_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  dsimp only
  have hdata :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vEven_full
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hscratchB hcompare hactive
      huOdd hvEven hvNonzero hmsb hdouble
  have hmetadata :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_active_nonzero_metadata
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hcompare hfinal hactive
      hvNonzero
  have hhistoryRead :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_vEven
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hscratchB hcompare hactive
      hhistory huOdd hvEven hvNonzero
  dsimp only at hdata
  rcases hdata with ⟨hu, hv, hr, hs⟩
  rcases hmetadata with ⟨ha, hk, hp⟩
  exact ⟨hu, hv, hr, hs, ha, hk, hp, hhistoryRead⟩

/-- On clean active odd `uGreater` inputs, the path/control route's complete
branch readout matches the source round's data/metadata and selected
branch-history bit. -/
lemma
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uGreater_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  dsimp only
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hdata :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uGreater_full
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hcompare hfinal hactive
      huOdd hvOdd hlt hlsb hadd hmsb hdouble
  have hmetadata :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_active_nonzero_metadata
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hcompare hfinal hactive
      hvNonzero
  have hhistoryRead :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_uGreater
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hscratchB hcompare hfinal
      hactive hhistory huOdd hvOdd hlt
  dsimp only at hdata
  rcases hdata with ⟨hu, hv, hr, hs⟩
  rcases hmetadata with ⟨ha, hk, hp⟩
  exact ⟨hu, hv, hr, hs, ha, hk, hp, hhistoryRead⟩

/-- On clean active odd `vLe` inputs, the path/control route's complete branch
readout matches the source round's data/metadata and selected branch-history
bit. -/
lemma
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vLe_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundControlledStep tail counterWidth
          comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  dsimp only
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  have hdata :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vLe_full
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hcompare hfinal hactive
      huOdd hvOdd hnlt hlsb hadd hmsb hdouble
  have hmetadata :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_active_nonzero_metadata
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hcompare hfinal hactive
      hvNonzero
  have hhistoryRead :=
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_history_vLe
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      historyIndex workIndex x hscratchA hscratchB hcompare hfinal
      hactive hhistory huOdd hvOdd hnlt
  dsimp only at hdata
  rcases hdata with ⟨hu, hv, hr, hs⟩
  rcases hmetadata with ⟨ha, hk, hp⟩
  exact ⟨hu, hv, hr, hs, ha, hk, hp, hhistoryRead⟩

/-- Fixed-round schedule wrapper for a clean active terminating slot.  The
history register is the slot selected by `roundIndex`. -/
lemma
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_active_v_zero_complete
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
        (fixedRoundPathControlWorkKaliskiRoundStep tail counterWidth
          comparisonIndex roundIndex workIndex
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
  simpa [fixedRoundPathControlWorkKaliskiRoundStep] using
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_active_v_zero_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x
      hcompare hactive hvZero hscratchA hscratchB hhistory

/-- Fixed-round schedule wrapper for a clean inactive slot.  The result is
independent of whether `v` is zero. -/
lemma
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_inactive_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = false)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundPathControlWorkKaliskiRoundStep tail counterWidth
          comparisonIndex roundIndex workIndex
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
  simpa [fixedRoundPathControlWorkKaliskiRoundStep] using
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_inactive_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x
      hcompare hactive hhistory

/-- Fixed-round schedule wrapper for a clean active `uEven` slot. -/
lemma
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_uEven_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundPathControlWorkKaliskiRoundStep tail counterWidth
          comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  simpa [fixedRoundPathControlWorkKaliskiRoundStep] using
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uEven_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x
      hscratchA hscratchB hcompare hfinal hactive hhistory hvNonzero
      huEven hmsb hdouble

/-- Fixed-round schedule wrapper for a clean active `vEven` slot. -/
lemma
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_vEven_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundPathControlWorkKaliskiRoundStep tail counterWidth
          comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  simpa [fixedRoundPathControlWorkKaliskiRoundStep] using
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vEven_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x
      hscratchA hscratchB hcompare hfinal hactive hhistory huOdd hvEven
      hvNonzero hmsb hdouble

/-- Fixed-round schedule wrapper for a clean active odd `uGreater` slot. -/
lemma
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_uGreater_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundPathControlWorkKaliskiRoundStep tail counterWidth
          comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  simpa [fixedRoundPathControlWorkKaliskiRoundStep] using
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uGreater_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x
      hscratchA hscratchB hcompare hfinal hactive hhistory huOdd hvOdd
      hlt hlsb hadd hmsb hdouble

/-- Fixed-round schedule wrapper for a clean active odd `vLe` slot. -/
lemma
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_vLe_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundPathControlWorkKaliskiRoundStep tail counterWidth
          comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  simpa [fixedRoundPathControlWorkKaliskiRoundStep] using
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vLe_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x
      hscratchA hscratchB hcompare hfinal hactive hhistory huOdd hvOdd
      hnlt hlsb hadd hmsb hdouble

/-- On clean active nonzero inputs, the corrected semantic route agrees with
the existing path-controlled concrete route. -/
lemma
    modeControlledSemanticStep_eq_controlledStep_clean_of_active_nonzero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvNonzero : x.v.val ≠ 0) :
    fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      fullRoundPathControlWorkKaliskiRoundControlledStep
        tail counterWidth comparisonIndex historyIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) := by
  rw [
    modeControlledSemanticStep_eq_activeOnlyConcrete_clean_of_active
      tail counterWidth comparisonIndex historyIndex workIndex x hactive]
  rw [
    fullRoundPathControlWorkKaliskiRoundControlledStep_eq_activeOnlyConcrete_clean
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]

/-- On clean active nonzero fixed-round inputs, the corrected semantic route
agrees with the existing path-controlled concrete fixed-round route. -/
lemma
    fixedRoundModeControlledSemanticStep_eq_pathControlled_clean_of_active_nonzero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hcompare : x.compare = false)
    (hactive : x.active = true)
    (hvNonzero : x.v.val ≠ 0) :
    fixedRoundModeControlledSemanticStep
        tail counterWidth comparisonIndex roundIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) =
      fixedRoundPathControlWorkKaliskiRoundStep
        tail counterWidth comparisonIndex roundIndex workIndex
        (withCleanFullRoundPathControlWork tail.succ counterWidth x) := by
  simpa [
    fixedRoundModeControlledSemanticStep,
    fixedRoundPathControlWorkKaliskiRoundStep] using
    modeControlledSemanticStep_eq_controlledStep_clean_of_active_nonzero
      tail counterWidth comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x
      hcompare hactive hvNonzero

/-- Corrected semantic route wrapper for a clean active `uEven` slot. -/
lemma
    modeControlledSemanticStep_roundStateReadout_uEven_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  rw [
    modeControlledSemanticStep_eq_controlledStep_clean_of_active_nonzero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  exact
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uEven_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex historyIndex
      workIndex x hscratchA hscratchB hcompare hfinal hactive hhistory
      hvNonzero huEven hmsb hdouble

/-- Corrected semantic route wrapper for a clean active `vEven` slot. -/
lemma
    modeControlledSemanticStep_roundStateReadout_vEven_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  rw [
    modeControlledSemanticStep_eq_controlledStep_clean_of_active_nonzero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  exact
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vEven_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex historyIndex
      workIndex x hscratchA hscratchB hcompare hfinal hactive hhistory
      huOdd hvEven hvNonzero hmsb hdouble

/-- Corrected semantic route wrapper for a clean active odd `uGreater` slot. -/
lemma
    modeControlledSemanticStep_roundStateReadout_uGreater_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    modeControlledSemanticStep_eq_controlledStep_clean_of_active_nonzero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  exact
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_uGreater_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex historyIndex
      workIndex x hscratchA hscratchB hcompare hfinal hactive hhistory huOdd
      hvOdd hlt hlsb hadd hmsb hdouble

/-- Corrected semantic route wrapper for a clean active odd `vLe` slot. -/
lemma
    modeControlledSemanticStep_roundStateReadout_vLe_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    modeControlledSemanticStep_eq_controlledStep_clean_of_active_nonzero
      tail counterWidth comparisonIndex historyIndex workIndex x hcompare
      hactive hvNonzero]
  exact
    fullRoundPathControlWorkKaliskiRoundControlledStep_roundStateReadout_vLe_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex historyIndex
      workIndex x hscratchA hscratchB hcompare hfinal hactive hhistory huOdd
      hvOdd hnlt hlsb hadd hmsb hdouble

/-- Corrected semantic fixed-round wrapper for a clean active `uEven` slot. -/
lemma
    fixedRoundModeControlledSemanticStep_roundStateReadout_uEven_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false)
    (hvNonzero : x.v.val ≠ 0)
    (huEven : x.u.val.testBit (0 : Nat) = false)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  rw [
    fixedRoundModeControlledSemanticStep_eq_pathControlled_clean_of_active_nonzero
      tail counterWidth comparisonIndex roundIndex workIndex x hcompare
      hactive hvNonzero]
  exact
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_uEven_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex roundIndex
      workIndex x hscratchA hscratchB hcompare hfinal hactive hhistory
      hvNonzero huEven hmsb hdouble

/-- Corrected semantic fixed-round wrapper for a clean active `vEven` slot. -/
lemma
    fixedRoundModeControlledSemanticStep_roundStateReadout_vEven_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvEven : x.v.val.testBit (0 : Nat) = false)
    (hvNonzero : x.v.val ≠ 0)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  rw [
    fixedRoundModeControlledSemanticStep_eq_pathControlled_clean_of_active_nonzero
      tail counterWidth comparisonIndex roundIndex workIndex x hcompare
      hactive hvNonzero]
  exact
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_vEven_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex roundIndex
      workIndex x hscratchA hscratchB hcompare hfinal hactive hhistory huOdd
      hvEven hvNonzero hmsb hdouble

/-- Corrected semantic fixed-round wrapper for a clean active odd `uGreater`
slot. -/
lemma
    fixedRoundModeControlledSemanticStep_roundStateReadout_uGreater_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false)
    (hadd :
      x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.sCoeff.val < 2 ^ (tail.succ + 1)) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fixedRoundModeControlledSemanticStep_eq_pathControlled_clean_of_active_nonzero
      tail counterWidth comparisonIndex roundIndex workIndex x hcompare
      hactive hvNonzero]
  exact
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_uGreater_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex roundIndex
      workIndex x hscratchA hscratchB hcompare hfinal hactive hhistory huOdd
      hvOdd hlt hlsb hadd hmsb hdouble

/-- Corrected semantic fixed-round wrapper for a clean active odd `vLe` slot. -/
lemma
    fixedRoundModeControlledSemanticStep_roundStateReadout_vLe_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hactive : x.active = true)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get x =
        false)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false)
    (hadd :
      x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1))
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false)
    (hdouble : 2 * x.rCoeff.val < 2 ^ (tail.succ + 1)) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (kaliskiSteps + 1) paddingSteps
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout.u = sourceRound.u ∧
      readout.v = sourceRound.v ∧
      readout.rCoeff = sourceRound.rCoeff ∧
      readout.sCoeff = sourceRound.sCoeff ∧
      readout.active = sourceRound.active ∧
      readout.kaliskiSteps = sourceRound.kaliskiSteps ∧
      readout.paddingSteps = sourceRound.paddingSteps ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  have hvNonzero : x.v.val ≠ 0 :=
    Nat.BinaryArithmetic.ne_zero_of_testBit_zero_true x.v.val hvOdd
  rw [
    fixedRoundModeControlledSemanticStep_eq_pathControlled_clean_of_active_nonzero
      tail counterWidth comparisonIndex roundIndex workIndex x hcompare
      hactive hvNonzero]
  exact
    fixedRoundPathControlWorkKaliskiRoundStep_roundStateReadout_vLe_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex roundIndex
      workIndex x hscratchA hscratchB hcompare hfinal hactive hhistory huOdd
      hvOdd hnlt hlsb hadd hmsb hdouble

/-- Kaliski-step readout count after one mode-controlled semantic round. -/
def modeControlledSemanticReadoutKaliskiSteps
    {n counterWidth : Nat} (kaliskiSteps : Nat)
    (x : Registers n counterWidth) : Nat :=
  if x.active && decide (x.v.val ≠ 0) then kaliskiSteps + 1 else kaliskiSteps

/-- Padding-step readout count after one mode-controlled semantic round. -/
def modeControlledSemanticReadoutPaddingSteps
    {n counterWidth : Nat} (paddingSteps : Nat)
    (x : Registers n counterWidth) : Nat :=
  if x.active && decide (x.v.val ≠ 0) then paddingSteps else paddingSteps + 1

/-- Side-condition package for the all-branch mode-controlled semantic round
readout dispatcher.  The branch-specific fields are only consumed in the
matching source branch. -/
structure ModeControlledSemanticStepReadoutCertificate
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) : Prop where
  scratchA : x.scratchA = false
  scratchB : x.scratchB = false
  compare : x.compare = false
  final : comparisonIndex.val + 1 = tail.succ
  history :
    (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x = false
  uEven_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = false ->
        x.sCoeff.val.testBit (Fin.last tail.succ).val = false
  uEven_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = false ->
        2 * x.sCoeff.val < 2 ^ (tail.succ + 1)
  vEven_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = false ->
          x.rCoeff.val.testBit (Fin.last tail.succ).val = false
  vEven_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = false ->
          2 * x.rCoeff.val < 2 ^ (tail.succ + 1)
  uGreater_lsb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          (x.u - x.v).val.testBit (0 : Nat) = false
  uGreater_add :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)
  uGreater_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          x.sCoeff.val.testBit (Fin.last tail.succ).val = false
  uGreater_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          2 * x.sCoeff.val < 2 ^ (tail.succ + 1)
  vLe_lsb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          (x.v - x.u).val.testBit (0 : Nat) = false
  vLe_add :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)
  vLe_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          x.rCoeff.val.testBit (Fin.last tail.succ).val = false
  vLe_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          2 * x.rCoeff.val < 2 ^ (tail.succ + 1)

/-- Arithmetic side conditions of the all-branch mode-controlled semantic
readout dispatcher.  Clean workspace, clean selected history slot, and the
final comparison-index condition are supplied separately by the fresh-workspace
readout fold. -/
structure ModeControlledSemanticStepArithmeticCertificate
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth) : Prop where
  uEven_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = false ->
        x.sCoeff.val.testBit (Fin.last tail.succ).val = false
  uEven_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = false ->
        2 * x.sCoeff.val < 2 ^ (tail.succ + 1)
  vEven_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = false ->
          x.rCoeff.val.testBit (Fin.last tail.succ).val = false
  vEven_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = false ->
          2 * x.rCoeff.val < 2 ^ (tail.succ + 1)
  uGreater_lsb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          (x.u - x.v).val.testBit (0 : Nat) = false
  uGreater_add :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)
  uGreater_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          x.sCoeff.val.testBit (Fin.last tail.succ).val = false
  uGreater_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          2 * x.sCoeff.val < 2 ^ (tail.succ + 1)
  vLe_lsb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          (x.v - x.u).val.testBit (0 : Nat) = false
  vLe_add :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)
  vLe_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          x.rCoeff.val.testBit (Fin.last tail.succ).val = false
  vLe_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          2 * x.rCoeff.val < 2 ^ (tail.succ + 1)

/-- Non-LSB arithmetic side conditions for the all-branch mode-controlled
semantic readout dispatcher.  The odd-minus-odd LSB guards are discharged
uniformly from the selected comparison branch. -/
structure ModeControlledSemanticStepOverflowCertificate
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth) : Prop where
  uEven_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = false ->
        x.sCoeff.val.testBit (Fin.last tail.succ).val = false
  uEven_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = false ->
        2 * x.sCoeff.val < 2 ^ (tail.succ + 1)
  vEven_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = false ->
          x.rCoeff.val.testBit (Fin.last tail.succ).val = false
  vEven_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = false ->
          2 * x.rCoeff.val < 2 ^ (tail.succ + 1)
  uGreater_add :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)
  uGreater_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          x.sCoeff.val.testBit (Fin.last tail.succ).val = false
  uGreater_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          2 * x.sCoeff.val < 2 ^ (tail.succ + 1)
  vLe_add :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)
  vLe_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          x.rCoeff.val.testBit (Fin.last tail.succ).val = false
  vLe_double :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          2 * x.rCoeff.val < 2 ^ (tail.succ + 1)

/-- Coefficient top-bit bounds for one mode-controlled semantic readout slot.
These are the remaining branch-independent arithmetic facts after the generic
odd-minus-odd, add, and double guards are factored out. -/
structure ModeControlledSemanticStepMsbCertificate
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth) : Prop where
  rCoeff_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.rCoeff.val.testBit (Fin.last tail.succ).val = false
  sCoeff_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.sCoeff.val.testBit (Fin.last tail.succ).val = false

/-- Build coefficient top-bit bounds from the source Bezout invariant and
nonzero active operands.  This is the arithmetic entrypoint for discharging
the remaining fresh-workspace readout side condition from source invariants. -/
lemma modeControlledSemanticStepMsbCertificate_of_bezout_bound
    (tail counterWidth p : Nat)
    (x : Registers tail.succ counterWidth)
    (hbezout :
      x.rCoeff.val * x.v.val + x.sCoeff.val * x.u.val = p)
    (hpBound : p < 2 ^ tail.succ)
    (huNonzero :
      x.active = true -> x.v.val ≠ 0 -> x.u.val ≠ 0) :
    ModeControlledSemanticStepMsbCertificate tail counterWidth x where
  rCoeff_msb := by
    intro _hactive hvNonzero
    have hvPos : 0 < x.v.val := Nat.pos_of_ne_zero hvNonzero
    have hrLeMul : x.rCoeff.val <= x.rCoeff.val * x.v.val := by
      calc
        x.rCoeff.val = x.rCoeff.val * 1 := by rw [Nat.mul_one]
        _ <= x.rCoeff.val * x.v.val :=
          Nat.mul_le_mul_left x.rCoeff.val (Nat.succ_le_of_lt hvPos)
    have hmulLeP : x.rCoeff.val * x.v.val <= p := by
      rw [← hbezout]
      exact Nat.le_add_right _ _
    have hrLt : x.rCoeff.val < 2 ^ tail.succ :=
      lt_of_le_of_lt (Nat.le_trans hrLeMul hmulLeP) hpBound
    simpa [Fin.last] using Nat.testBit_lt_two_pow hrLt
  sCoeff_msb := by
    intro hactive hvNonzero
    have huPos : 0 < x.u.val :=
      Nat.pos_of_ne_zero (huNonzero hactive hvNonzero)
    have hsLeMul : x.sCoeff.val <= x.sCoeff.val * x.u.val := by
      calc
        x.sCoeff.val = x.sCoeff.val * 1 := by rw [Nat.mul_one]
        _ <= x.sCoeff.val * x.u.val :=
          Nat.mul_le_mul_left x.sCoeff.val (Nat.succ_le_of_lt huPos)
    have hmulLeP : x.sCoeff.val * x.u.val <= p := by
      rw [← hbezout]
      exact Nat.le_add_left _ _
    have hsLt : x.sCoeff.val < 2 ^ tail.succ :=
      lt_of_le_of_lt (Nat.le_trans hsLeMul hmulLeP) hpBound
    simpa [Fin.last] using Nat.testBit_lt_two_pow hsLt

/-- Minimal branch arithmetic fields after mechanical LSB and double guards
are discharged.  The remaining obligations are the true add/no-overflow and
top-bit facts that must come from source/register invariants. -/
structure ModeControlledSemanticStepAddMsbCertificate
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth) : Prop where
  uEven_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = false ->
        x.sCoeff.val.testBit (Fin.last tail.succ).val = false
  vEven_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = false ->
          x.rCoeff.val.testBit (Fin.last tail.succ).val = false
  uGreater_add :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          x.rCoeff.val + x.sCoeff.val < 2 ^ (tail.succ + 1)
  uGreater_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> x.v.val < x.u.val ->
          x.sCoeff.val.testBit (Fin.last tail.succ).val = false
  vLe_add :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          x.sCoeff.val + x.rCoeff.val < 2 ^ (tail.succ + 1)
  vLe_msb :
    x.active = true -> x.v.val ≠ 0 ->
      x.u.val.testBit (0 : Nat) = true ->
        x.v.val.testBit (0 : Nat) = true -> ¬ x.v.val < x.u.val ->
          x.rCoeff.val.testBit (Fin.last tail.succ).val = false

/-- Build the add/MSB package from branch-independent coefficient top-bit
bounds. -/
lemma modeControlledSemanticStepAddMsbCertificate_of_msb_fields
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepMsbCertificate tail counterWidth x) :
    ModeControlledSemanticStepAddMsbCertificate tail counterWidth x where
  uEven_msb := by
    intro hactive hvNonzero _huEven
    exact cert.sCoeff_msb hactive hvNonzero
  vEven_msb := by
    intro hactive hvNonzero _huOdd _hvEven
    exact cert.rCoeff_msb hactive hvNonzero
  uGreater_add := by
    intro hactive hvNonzero _huOdd _hvOdd _hlt
    exact
      word_add_val_lt_two_pow_succ_of_msb_false x.rCoeff x.sCoeff
        (cert.rCoeff_msb hactive hvNonzero)
        (cert.sCoeff_msb hactive hvNonzero)
  uGreater_msb := by
    intro hactive hvNonzero _huOdd _hvOdd _hlt
    exact cert.sCoeff_msb hactive hvNonzero
  vLe_add := by
    intro hactive hvNonzero _huOdd _hvOdd _hnlt
    exact
      word_add_val_lt_two_pow_succ_of_msb_false x.sCoeff x.rCoeff
        (cert.sCoeff_msb hactive hvNonzero)
        (cert.rCoeff_msb hactive hvNonzero)
  vLe_msb := by
    intro hactive hvNonzero _huOdd _hvOdd _hnlt
    exact cert.rCoeff_msb hactive hvNonzero

/-- Build the non-LSB overflow package from the true add/MSB fields.  The
doubling bounds follow from the matching top-bit facts. -/
lemma modeControlledSemanticStepOverflowCertificate_of_add_msb_fields
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepAddMsbCertificate tail counterWidth x) :
    ModeControlledSemanticStepOverflowCertificate tail counterWidth x where
  uEven_msb := cert.uEven_msb
  uEven_double := by
    intro hactive hvNonzero huEven
    exact
      word_two_mul_lt_of_msb_false x.sCoeff
        (cert.uEven_msb hactive hvNonzero huEven)
  vEven_msb := cert.vEven_msb
  vEven_double := by
    intro hactive hvNonzero huOdd hvEven
    exact
      word_two_mul_lt_of_msb_false x.rCoeff
        (cert.vEven_msb hactive hvNonzero huOdd hvEven)
  uGreater_add := cert.uGreater_add
  uGreater_msb := cert.uGreater_msb
  uGreater_double := by
    intro hactive hvNonzero huOdd hvOdd hlt
    exact
      word_two_mul_lt_of_msb_false x.sCoeff
        (cert.uGreater_msb hactive hvNonzero huOdd hvOdd hlt)
  vLe_add := cert.vLe_add
  vLe_msb := cert.vLe_msb
  vLe_double := by
    intro hactive hvNonzero huOdd hvOdd hnlt
    exact
      word_two_mul_lt_of_msb_false x.rCoeff
        (cert.vLe_msb hactive hvNonzero huOdd hvOdd hnlt)

/-- Build the non-LSB overflow package from branch-independent coefficient
top-bit bounds. -/
lemma modeControlledSemanticStepOverflowCertificate_of_msb_fields
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepMsbCertificate tail counterWidth x) :
    ModeControlledSemanticStepOverflowCertificate tail counterWidth x :=
  modeControlledSemanticStepOverflowCertificate_of_add_msb_fields
    tail counterWidth x
    (modeControlledSemanticStepAddMsbCertificate_of_msb_fields
      tail counterWidth x cert)

/-- Build the arithmetic side-condition package from the non-LSB branch
guards.  The odd-minus-odd LSB guards are consequences of the selected
comparison branch and do not need to be supplied by callers. -/
lemma modeControlledSemanticStepArithmeticCertificate_of_overflow_fields
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (overflow :
      ModeControlledSemanticStepOverflowCertificate tail counterWidth x) :
    ModeControlledSemanticStepArithmeticCertificate tail counterWidth x where
  uEven_msb := overflow.uEven_msb
  uEven_double := overflow.uEven_double
  vEven_msb := overflow.vEven_msb
  vEven_double := overflow.vEven_double
  uGreater_lsb := by
    intro _hactive _hvNonzero huOdd hvOdd hlt
    exact word_sub_testBit_zero_false_of_odd_lt x.u x.v huOdd hvOdd hlt
  uGreater_add := overflow.uGreater_add
  uGreater_msb := overflow.uGreater_msb
  uGreater_double := overflow.uGreater_double
  vLe_lsb := by
    intro _hactive _hvNonzero huOdd hvOdd hnlt
    exact
      word_sub_testBit_zero_false_of_odd_not_lt x.u x.v huOdd hvOdd hnlt
  vLe_add := overflow.vLe_add
  vLe_msb := overflow.vLe_msb
  vLe_double := overflow.vLe_double

/-- Build the arithmetic side-condition package from the true add/MSB fields.
The odd-minus-odd LSB and top-bit-to-double guards are discharged uniformly. -/
lemma modeControlledSemanticStepArithmeticCertificate_of_add_msb_fields
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepAddMsbCertificate tail counterWidth x) :
    ModeControlledSemanticStepArithmeticCertificate tail counterWidth x :=
  modeControlledSemanticStepArithmeticCertificate_of_overflow_fields
    tail counterWidth x
    (modeControlledSemanticStepOverflowCertificate_of_add_msb_fields
      tail counterWidth x cert)

/-- Build the arithmetic side-condition package from branch-independent
coefficient top-bit bounds.  LSB, add, and double guards are discharged
uniformly. -/
lemma modeControlledSemanticStepArithmeticCertificate_of_msb_fields
    (tail counterWidth : Nat)
    (x : Registers tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepMsbCertificate tail counterWidth x) :
    ModeControlledSemanticStepArithmeticCertificate tail counterWidth x :=
  modeControlledSemanticStepArithmeticCertificate_of_overflow_fields
    tail counterWidth x
    (modeControlledSemanticStepOverflowCertificate_of_msb_fields
      tail counterWidth x cert)

/-- Build the add/MSB package from a Bezout equality plus bounded modulus. -/
lemma modeControlledSemanticStepAddMsbCertificate_of_bezout_bound
    (tail counterWidth p : Nat)
    (x : Registers tail.succ counterWidth)
    (hbezout :
      x.rCoeff.val * x.v.val + x.sCoeff.val * x.u.val = p)
    (hpBound : p < 2 ^ tail.succ)
    (huNonzero :
      x.active = true -> x.v.val ≠ 0 -> x.u.val ≠ 0) :
    ModeControlledSemanticStepAddMsbCertificate tail counterWidth x :=
  modeControlledSemanticStepAddMsbCertificate_of_msb_fields tail counterWidth x
    (modeControlledSemanticStepMsbCertificate_of_bezout_bound
      tail counterWidth p x hbezout hpBound huNonzero)

/-- Build the non-LSB overflow package from a Bezout equality plus bounded
modulus. -/
lemma modeControlledSemanticStepOverflowCertificate_of_bezout_bound
    (tail counterWidth p : Nat)
    (x : Registers tail.succ counterWidth)
    (hbezout :
      x.rCoeff.val * x.v.val + x.sCoeff.val * x.u.val = p)
    (hpBound : p < 2 ^ tail.succ)
    (huNonzero :
      x.active = true -> x.v.val ≠ 0 -> x.u.val ≠ 0) :
    ModeControlledSemanticStepOverflowCertificate tail counterWidth x :=
  modeControlledSemanticStepOverflowCertificate_of_msb_fields tail counterWidth x
    (modeControlledSemanticStepMsbCertificate_of_bezout_bound
      tail counterWidth p x hbezout hpBound huNonzero)

/-- Build the full arithmetic side-condition package from a Bezout equality
plus bounded modulus. -/
lemma modeControlledSemanticStepArithmeticCertificate_of_bezout_bound
    (tail counterWidth p : Nat)
    (x : Registers tail.succ counterWidth)
    (hbezout :
      x.rCoeff.val * x.v.val + x.sCoeff.val * x.u.val = p)
    (hpBound : p < 2 ^ tail.succ)
    (huNonzero :
      x.active = true -> x.v.val ≠ 0 -> x.u.val ≠ 0) :
    ModeControlledSemanticStepArithmeticCertificate tail counterWidth x :=
  modeControlledSemanticStepArithmeticCertificate_of_msb_fields
    tail counterWidth x
    (modeControlledSemanticStepMsbCertificate_of_bezout_bound
      tail counterWidth p x hbezout hpBound huNonzero)

/-- Build the full readout certificate from clean/basic fields plus the
branch arithmetic side-condition package. -/
lemma modeControlledSemanticStepReadoutCertificate_of_clean_arithmetic
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x =
        false)
    (arith :
      ModeControlledSemanticStepArithmeticCertificate tail counterWidth x) :
    ModeControlledSemanticStepReadoutCertificate tail counterWidth
      comparisonIndex historyIndex x where
  scratchA := hscratchA
  scratchB := hscratchB
  compare := hcompare
  final := hfinal
  history := hhistory
  uEven_msb := arith.uEven_msb
  uEven_double := arith.uEven_double
  vEven_msb := arith.vEven_msb
  vEven_double := arith.vEven_double
  uGreater_lsb := arith.uGreater_lsb
  uGreater_add := arith.uGreater_add
  uGreater_msb := arith.uGreater_msb
  uGreater_double := arith.uGreater_double
  vLe_lsb := arith.vLe_lsb
  vLe_add := arith.vLe_add
  vLe_msb := arith.vLe_msb
  vLe_double := arith.vLe_double

private lemma roundState_eq_of_component_readouts
    {left right : RoundState}
    (hu : left.u = right.u) (hv : left.v = right.v)
    (hr : left.rCoeff = right.rCoeff) (hs : left.sCoeff = right.sCoeff)
    (ha : left.active = right.active)
    (hk : left.kaliskiSteps = right.kaliskiSteps)
    (hp : left.paddingSteps = right.paddingSteps) :
    left = right := by
  cases left
  cases right
  simp_all

/-- All-branch corrected semantic route wrapper for one clean source-shaped
round.  The full readout certificate supplies clean/basic fields plus the
branch arithmetic side conditions needed by the selected source branch. -/
lemma modeControlledSemanticStep_roundStateReadout_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ) (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepReadoutCertificate
        tail counterWidth comparisonIndex historyIndex x) :
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fullRoundPathControlWorkKaliskiRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex historyIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (modeControlledSemanticReadoutKaliskiSteps kaliskiSteps x)
        (modeControlledSemanticReadoutPaddingSteps paddingSteps x)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  by_cases hactive : x.active = true
  · by_cases hvZero : x.v.val = 0
    · have hread :=
        modeControlledSemanticStep_roundStateReadout_active_v_zero_complete
          tail counterWidth kaliskiSteps paddingSteps comparisonIndex
          historyIndex workIndex x cert.compare hactive hvZero cert.scratchA
          cert.scratchB cert.history
      simpa [
        modeControlledSemanticReadoutKaliskiSteps,
        modeControlledSemanticReadoutPaddingSteps, hactive, hvZero] using hread
    · by_cases huEven : x.u.val.testBit (0 : Nat) = false
      · have hread :=
          modeControlledSemanticStep_roundStateReadout_uEven_complete
            tail counterWidth kaliskiSteps paddingSteps comparisonIndex
            historyIndex workIndex x cert.scratchA cert.scratchB cert.compare
            cert.final hactive cert.history hvZero huEven
            (cert.uEven_msb hactive hvZero huEven)
            (cert.uEven_double hactive hvZero huEven)
        rcases hread with ⟨hu, hv, hr, hs, ha, hk, hp, hhistory⟩
        have heq :=
          roundState_eq_of_component_readouts hu hv hr hs ha hk hp
        simpa [
          modeControlledSemanticReadoutKaliskiSteps,
          modeControlledSemanticReadoutPaddingSteps, hactive, hvZero] using
          And.intro heq hhistory
      · have huOdd : x.u.val.testBit (0 : Nat) = true := by
          cases hu : x.u.val.testBit (0 : Nat)
          · exact False.elim (huEven hu)
          · rfl
        by_cases hvEven : x.v.val.testBit (0 : Nat) = false
        · have hread :=
            modeControlledSemanticStep_roundStateReadout_vEven_complete
              tail counterWidth kaliskiSteps paddingSteps comparisonIndex
              historyIndex workIndex x cert.scratchA cert.scratchB cert.compare
              cert.final hactive cert.history huOdd hvEven hvZero
              (cert.vEven_msb hactive hvZero huOdd hvEven)
              (cert.vEven_double hactive hvZero huOdd hvEven)
          rcases hread with ⟨hu, hv, hr, hs, ha, hk, hp, hhistory⟩
          have heq :=
            roundState_eq_of_component_readouts hu hv hr hs ha hk hp
          simpa [
            modeControlledSemanticReadoutKaliskiSteps,
            modeControlledSemanticReadoutPaddingSteps, hactive, hvZero] using
            And.intro heq hhistory
        · have hvOdd : x.v.val.testBit (0 : Nat) = true := by
            cases hv : x.v.val.testBit (0 : Nat)
            · exact False.elim (hvEven hv)
            · rfl
          by_cases hlt : x.v.val < x.u.val
          · have hread :=
              modeControlledSemanticStep_roundStateReadout_uGreater_complete
                tail counterWidth kaliskiSteps paddingSteps comparisonIndex
                historyIndex workIndex x cert.scratchA cert.scratchB
                cert.compare cert.final hactive cert.history huOdd hvOdd hlt
                (cert.uGreater_lsb hactive hvZero huOdd hvOdd hlt)
                (cert.uGreater_add hactive hvZero huOdd hvOdd hlt)
                (cert.uGreater_msb hactive hvZero huOdd hvOdd hlt)
                (cert.uGreater_double hactive hvZero huOdd hvOdd hlt)
            rcases hread with ⟨hu, hv, hr, hs, ha, hk, hp, hhistory⟩
            have heq :=
              roundState_eq_of_component_readouts hu hv hr hs ha hk hp
            simpa [
              modeControlledSemanticReadoutKaliskiSteps,
              modeControlledSemanticReadoutPaddingSteps, hactive, hvZero] using
              And.intro heq hhistory
          · have hread :=
              modeControlledSemanticStep_roundStateReadout_vLe_complete
                tail counterWidth kaliskiSteps paddingSteps comparisonIndex
                historyIndex workIndex x cert.scratchA cert.scratchB
                cert.compare cert.final hactive cert.history huOdd hvOdd hlt
                (cert.vLe_lsb hactive hvZero huOdd hvOdd hlt)
                (cert.vLe_add hactive hvZero huOdd hvOdd hlt)
                (cert.vLe_msb hactive hvZero huOdd hvOdd hlt)
                (cert.vLe_double hactive hvZero huOdd hvOdd hlt)
            rcases hread with ⟨hu, hv, hr, hs, ha, hk, hp, hhistory⟩
            have heq :=
              roundState_eq_of_component_readouts hu hv hr hs ha hk hp
            simpa [
              modeControlledSemanticReadoutKaliskiSteps,
              modeControlledSemanticReadoutPaddingSteps, hactive, hvZero] using
              And.intro heq hhistory
  · have hactiveFalse : x.active = false := by
      cases hx : x.active
      · rfl
      · exact False.elim (hactive hx)
    have hread :=
      modeControlledSemanticStep_roundStateReadout_inactive_complete
        tail counterWidth kaliskiSteps paddingSteps comparisonIndex
        historyIndex workIndex x hactiveFalse cert.history
    simpa [
      modeControlledSemanticReadoutKaliskiSteps,
      modeControlledSemanticReadoutPaddingSteps, hactiveFalse] using hread

/-- Schedule-slot wrapper for the all-branch corrected semantic route readout. -/
lemma fixedRoundModeControlledSemanticStep_roundStateReadout_complete
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepReadoutCertificate tail counterWidth
        comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        x) :
    let historyIndex := RoundState.fixedRoundHistoryIndex tail.succ roundIndex
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters tail.succ counterWidth
        (fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork tail.succ counterWidth x))
    let readout :=
      RoundState.fromRegisters tail.succ counterWidth readoutRegisters
        (modeControlledSemanticReadoutKaliskiSteps kaliskiSteps x)
        (modeControlledSemanticReadoutPaddingSteps paddingSteps x)
    let sourceState :=
      RoundState.fromRegisters tail.succ counterWidth x kaliskiSteps
        paddingSteps
    let sourceRound := RoundState.round sourceState
    readout = sourceRound ∧
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
          readoutRegisters =
        RoundState.historyBit sourceState := by
  simpa [fixedRoundModeControlledSemanticStep] using
    modeControlledSemanticStep_roundStateReadout_complete
      tail counterWidth kaliskiSteps paddingSteps comparisonIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex x cert

/-- Register/count state used by the iterable corrected semantic readout
fold.  Each round consumes a fresh clean path/control workspace and records
only the source-shaped register readout plus the explicit Kaliski/padding
counts needed by `RoundState.fromRegisters`. -/
structure ModeControlledSemanticReadoutFoldState
    (n counterWidth : Nat) where
  /-- Source-shaped finite-register readout carried between fold rounds. -/
  registers : Registers n counterWidth
  /-- Number of Kaliski rounds represented by the source readout. -/
  kaliskiSteps : Nat
  /-- Number of padding rounds represented by the source readout. -/
  paddingSteps : Nat

/-- Source-level readout of an iterable corrected semantic readout-fold state.
-/
def modeControlledSemanticReadoutFoldStateRoundState
    (n counterWidth : Nat)
    (state : ModeControlledSemanticReadoutFoldState n counterWidth) :
    RoundState :=
  RoundState.fromRegisters n counterWidth state.registers
    state.kaliskiSteps state.paddingSteps

/-- Clean finite-register seed for the iterable corrected semantic readout
fold. -/
def initialModeControlledSemanticReadoutFoldState
    (n counterWidth : Nat) (p x : Word n) :
    ModeControlledSemanticReadoutFoldState n counterWidth where
  registers := initialRegisters n counterWidth p x
  kaliskiSteps := 0
  paddingSteps := 0

@[simp] lemma initialModeControlledSemanticReadoutFoldState_roundState
    (n counterWidth : Nat) (p x : Word n) :
    modeControlledSemanticReadoutFoldStateRoundState n counterWidth
        (initialModeControlledSemanticReadoutFoldState
          n counterWidth p x) =
      RoundState.initial p.val x.val := by
  simp [
    initialModeControlledSemanticReadoutFoldState,
    modeControlledSemanticReadoutFoldStateRoundState,
    RoundState.fromRegisters_initialRegisters]

/-- One schedule slot of the iterable corrected semantic readout fold.  The
local path/control workspace is reintroduced cleanly for this slot, then
discarded after the source-shaped readout. -/
def fixedRoundModeControlledSemanticReadoutStep
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) :
    ModeControlledSemanticReadoutFoldState tail.succ counterWidth ->
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth :=
  fun state =>
    let readoutRegisters :=
      fullRoundPathControlWorkRoundStateReadoutRegisters
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticStep
          tail counterWidth comparisonIndex roundIndex workIndex
          (withCleanFullRoundPathControlWork
            tail.succ counterWidth state.registers))
    { registers := readoutRegisters
      kaliskiSteps :=
        modeControlledSemanticReadoutKaliskiSteps
          state.kaliskiSteps state.registers
      paddingSteps :=
        modeControlledSemanticReadoutPaddingSteps
          state.paddingSteps state.registers }

/-- One fresh-workspace readout step agrees with one source `RoundState.round`
and writes the selected history slot with the source prefix history bit. -/
lemma fixedRoundModeControlledSemanticReadoutStep_roundState_complete
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepReadoutCertificate tail counterWidth
        comparisonIndex
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        state.registers) :
    let nextState :=
      fixedRoundModeControlledSemanticReadoutStep
        tail counterWidth comparisonIndex roundIndex workIndex state
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth nextState =
      RoundState.round
        (modeControlledSemanticReadoutFoldStateRoundState
          tail.succ counterWidth state) ∧
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        nextState.registers =
      RoundState.historyBit
        (modeControlledSemanticReadoutFoldStateRoundState
          tail.succ counterWidth state) := by
  simpa [
    fixedRoundModeControlledSemanticReadoutStep,
    modeControlledSemanticReadoutFoldStateRoundState] using
    fixedRoundModeControlledSemanticStep_roundStateReadout_complete
      tail counterWidth state.kaliskiSteps state.paddingSteps
      comparisonIndex roundIndex workIndex state.registers cert

/-- One fresh-workspace readout step preserves every branch-history slot except
the slot selected for the current fixed-round schedule entry. -/
lemma fixedRoundModeControlledSemanticReadoutStep_get_historyBit_of_ne
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (observed : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepReadoutCertificate tail counterWidth
        comparisonIndex
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        state.registers)
    (hne :
      RoundState.fixedRoundHistoryIndex tail.succ roundIndex ≠ observed) :
    (RegisterBits.historyBit tail.succ counterWidth observed).get
        (fixedRoundModeControlledSemanticReadoutStep
          tail counterWidth comparisonIndex roundIndex workIndex state).registers =
      (RegisterBits.historyBit tail.succ counterWidth observed).get
        state.registers := by
  change
    (RegisterBits.historyBit tail.succ counterWidth observed).get
        (fullRoundPathControlWorkRoundStateReadoutRegisters
          tail.succ counterWidth
          (fixedRoundModeControlledSemanticStep
            tail counterWidth comparisonIndex roundIndex workIndex
            (withCleanFullRoundPathControlWork
              tail.succ counterWidth state.registers))) =
      (RegisterBits.historyBit tail.succ counterWidth observed).get
        state.registers
  rw [fullRoundPathControlWorkRoundStateReadoutRegisters_get_historyBit]
  by_cases hactive : state.registers.active = true
  · by_cases hvEqZero : state.registers.v.val = 0
    · rw [fixedRoundModeControlledSemanticStep]
      rw [
        modeControlledSemanticActiveVZeroEndpoint
          tail counterWidth comparisonIndex
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
          workIndex state.registers cert.compare hactive hvEqZero
          cert.scratchA cert.scratchB]
      simp [RegisterBits.historyBit_get]
    · rw [fixedRoundModeControlledSemanticStep]
      rw [
        modeControlledSemanticStep_eq_activeOnlyConcrete_clean_of_active
          tail counterWidth comparisonIndex
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
          workIndex state.registers hactive]
      simpa [coeffAdderHistoryBit, liftedHistoryBit,
        liftComparisonStateBitToCoeffAdderWork, liftRegisterBitToComparisonWork,
        BinaryLabelEncoding.prodLeftBit] using
        fullRoundWorkKaliskiActiveOnlyRoundConcreteStep_get_historyBit_of_ne_clean
          tail counterWidth comparisonIndex
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) observed
          workIndex state.registers cert.compare hactive hvEqZero
          cert.scratchA hne
  · have hactiveFalse : state.registers.active = false := by
      cases h : state.registers.active
      · rfl
      · exact False.elim (hactive h)
    rw [fixedRoundModeControlledSemanticStep]
    rw [
      modeControlledSemanticStep_cleanEndpoint_of_inactive
        tail counterWidth comparisonIndex
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        workIndex state.registers hactiveFalse]
    simp [RegisterBits.historyBit_get]

@[simp] lemma fixedRoundModeControlledSemanticReadoutStep_scratchA
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    (fixedRoundModeControlledSemanticReadoutStep
        tail counterWidth comparisonIndex roundIndex workIndex state).registers.scratchA =
      false := by
  simp [fixedRoundModeControlledSemanticReadoutStep]

@[simp] lemma fixedRoundModeControlledSemanticReadoutStep_scratchB
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    (fixedRoundModeControlledSemanticReadoutStep
        tail counterWidth comparisonIndex roundIndex workIndex state).registers.scratchB =
      false := by
  simp [fixedRoundModeControlledSemanticReadoutStep]

@[simp] lemma fixedRoundModeControlledSemanticReadoutStep_compare
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    (fixedRoundModeControlledSemanticReadoutStep
        tail counterWidth comparisonIndex roundIndex workIndex state).registers.compare =
      false := by
  simp [fixedRoundModeControlledSemanticReadoutStep]

/-- Fixed-round schedule of fresh-workspace corrected semantic readout steps.
-/
def fixedRoundModeControlledSemanticReadoutStepSchedule
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List
      (ModeControlledSemanticReadoutFoldState tail.succ counterWidth ->
        ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :=
  List.ofFn fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
    fixedRoundModeControlledSemanticReadoutStep
      tail counterWidth comparisonIndex roundIndex workIndex

@[simp] lemma
    fixedRoundModeControlledSemanticReadoutStepSchedule_length
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (fixedRoundModeControlledSemanticReadoutStepSchedule
      tail counterWidth comparisonIndex workIndex).length =
      2 * tail.succ := by
  simp [fixedRoundModeControlledSemanticReadoutStepSchedule]
  omega

/-- The `roundIndex`-th fresh-workspace readout schedule entry is the matching
fixed-round source slot. -/
lemma fixedRoundModeControlledSemanticReadoutStepSchedule_get
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds) :
    (fixedRoundModeControlledSemanticReadoutStepSchedule
      tail counterWidth comparisonIndex workIndex).get
        ⟨roundIndex.val, by
          rw [fixedRoundModeControlledSemanticReadoutStepSchedule_length]
          exact roundIndex.isLt⟩ =
      fixedRoundModeControlledSemanticReadoutStep
        tail counterWidth comparisonIndex roundIndex workIndex := by
  change
    (List.ofFn
      (fun roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
        fixedRoundModeControlledSemanticReadoutStep
          tail counterWidth comparisonIndex roundIndex workIndex)).get
        ⟨roundIndex.val, by
          simp
          omega⟩ =
      fixedRoundModeControlledSemanticReadoutStep
        tail counterWidth comparisonIndex roundIndex workIndex
  rw [List.get_ofFn]
  congr 1

/-- Prefix state for the fresh-workspace corrected semantic readout schedule.
-/
def fixedRoundModeControlledSemanticReadoutPrefixState
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (rounds : Nat) :
    ModeControlledSemanticReadoutFoldState tail.succ counterWidth ->
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth :=
  UnitaryCircuit.Realizes.stepList
    ((fixedRoundModeControlledSemanticReadoutStepSchedule
      tail counterWidth comparisonIndex workIndex).take rounds)

@[simp] lemma fixedRoundModeControlledSemanticReadoutPrefixState_zero
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    fixedRoundModeControlledSemanticReadoutPrefixState
        tail counterWidth comparisonIndex workIndex 0 state =
      state := by
  rfl

/-- Prefix successor form for the fresh-workspace corrected semantic readout
schedule. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_succ
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    fixedRoundModeControlledSemanticReadoutPrefixState
        tail counterWidth comparisonIndex workIndex
        (roundIndex.val + 1) state =
      fixedRoundModeControlledSemanticReadoutStep
        tail counterWidth comparisonIndex roundIndex workIndex
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val state) := by
  unfold fixedRoundModeControlledSemanticReadoutPrefixState
  let schedule :=
    fixedRoundModeControlledSemanticReadoutStepSchedule
      tail counterWidth comparisonIndex workIndex
  have hlen : roundIndex.val < schedule.length := by
    rw [fixedRoundModeControlledSemanticReadoutStepSchedule_length]
    exact roundIndex.isLt
  rw [UnitaryCircuit.Realizes.stepList_take_succ schedule roundIndex.val hlen]
  have hget :
      schedule.get ⟨roundIndex.val, hlen⟩ =
        fixedRoundModeControlledSemanticReadoutStep
          tail counterWidth comparisonIndex roundIndex workIndex := by
    simpa [schedule] using
      fixedRoundModeControlledSemanticReadoutStepSchedule_get
        tail counterWidth comparisonIndex workIndex roundIndex
  rw [hget]

/-- Fresh-workspace readout prefixes keep the source-shaped `scratchA`
ancilla clean. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_scratchA_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    ∀ (rounds : Nat),
      rounds ≤ (rnsl17MontgomerySchedule tail.succ).rounds ->
        state.registers.scratchA = false ->
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex rounds state).registers.scratchA =
            false
  | 0, _hrounds, hclean => by simpa using hclean
  | rounds + 1, hrounds, _hclean => by
      have hroundIndex :
          rounds < (rnsl17MontgomerySchedule tail.succ).rounds :=
        Nat.lt_of_succ_le hrounds
      let roundIndex :
          Fin (rnsl17MontgomerySchedule tail.succ).rounds :=
        ⟨rounds, hroundIndex⟩
      rw [
        fixedRoundModeControlledSemanticReadoutPrefixState_succ
          tail counterWidth comparisonIndex roundIndex workIndex state]
      simp

/-- Fresh-workspace readout prefixes keep the source-shaped `scratchB`
ancilla clean. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_scratchB_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    ∀ (rounds : Nat),
      rounds ≤ (rnsl17MontgomerySchedule tail.succ).rounds ->
        state.registers.scratchB = false ->
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex rounds state).registers.scratchB =
            false
  | 0, _hrounds, hclean => by simpa using hclean
  | rounds + 1, hrounds, _hclean => by
      have hroundIndex :
          rounds < (rnsl17MontgomerySchedule tail.succ).rounds :=
        Nat.lt_of_succ_le hrounds
      let roundIndex :
          Fin (rnsl17MontgomerySchedule tail.succ).rounds :=
        ⟨rounds, hroundIndex⟩
      rw [
        fixedRoundModeControlledSemanticReadoutPrefixState_succ
          tail counterWidth comparisonIndex roundIndex workIndex state]
      simp

/-- Fresh-workspace readout prefixes keep the source-shaped comparison
ancilla clean. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_compare_clean
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    ∀ (rounds : Nat),
      rounds ≤ (rnsl17MontgomerySchedule tail.succ).rounds ->
        state.registers.compare = false ->
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex rounds state).registers.compare =
            false
  | 0, _hrounds, hclean => by simpa using hclean
  | rounds + 1, hrounds, _hclean => by
      have hroundIndex :
          rounds < (rnsl17MontgomerySchedule tail.succ).rounds :=
        Nat.lt_of_succ_le hrounds
      let roundIndex :
          Fin (rnsl17MontgomerySchedule tail.succ).rounds :=
        ⟨rounds, hroundIndex⟩
      rw [
        fixedRoundModeControlledSemanticReadoutPrefixState_succ
          tail counterWidth comparisonIndex roundIndex workIndex state]
      simp

/-- Before a fixed-round schedule slot is consumed by the fresh-workspace
readout fold, its selected history register is still clean.  The induction
only requires certificates for earlier consumed slots, so this is not circular
in the certificate for the current slot. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_clean_before
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (targetIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ) :
    ∀ (rounds : Nat),
      rounds ≤ targetIndex.val ->
        rounds ≤ (rnsl17MontgomerySchedule tail.succ).rounds ->
          (∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
            priorIndex.val < rounds ->
              ModeControlledSemanticStepReadoutCertificate tail counterWidth
                comparisonIndex
                (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
                (fixedRoundModeControlledSemanticReadoutPrefixState
                  tail counterWidth comparisonIndex workIndex priorIndex.val
                  (initialModeControlledSemanticReadoutFoldState
                    tail.succ counterWidth p x)).registers) ->
            (RegisterBits.historyBit tail.succ counterWidth
                (RoundState.fixedRoundHistoryIndex tail.succ targetIndex)).get
                (fixedRoundModeControlledSemanticReadoutPrefixState
                  tail counterWidth comparisonIndex workIndex rounds
                  (initialModeControlledSemanticReadoutFoldState
                    tail.succ counterWidth p x)).registers =
              false
  | 0, _htarget, _hrounds, _certAt => by
      simpa [initialModeControlledSemanticReadoutFoldState] using
        initialRegisters_historyBit_get tail.succ counterWidth p x
          (RoundState.fixedRoundHistoryIndex tail.succ targetIndex)
  | rounds + 1, htarget, hrounds, certAt => by
      have hcurrentLt :
          rounds < (rnsl17MontgomerySchedule tail.succ).rounds :=
        Nat.lt_of_succ_le hrounds
      let currentIndex :
          Fin (rnsl17MontgomerySchedule tail.succ).rounds :=
        ⟨rounds, hcurrentLt⟩
      have hcurrentNe : currentIndex ≠ targetIndex := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [currentIndex] at hval
        omega
      have hslotNe :
          RoundState.fixedRoundHistoryIndex tail.succ currentIndex ≠
            RoundState.fixedRoundHistoryIndex tail.succ targetIndex :=
        RoundState.fixedRoundHistoryIndex_ne_of_ne tail.succ hcurrentNe
      have hstep :=
        fixedRoundModeControlledSemanticReadoutStep_get_historyBit_of_ne
          tail counterWidth comparisonIndex currentIndex
          (RoundState.fixedRoundHistoryIndex tail.succ targetIndex)
          workIndex
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex rounds
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x))
          (certAt currentIndex (Nat.lt_succ_self rounds))
          hslotNe
      have hprev :
          (RegisterBits.historyBit tail.succ counterWidth
              (RoundState.fixedRoundHistoryIndex tail.succ targetIndex)).get
              (fixedRoundModeControlledSemanticReadoutPrefixState
                tail counterWidth comparisonIndex workIndex rounds
                (initialModeControlledSemanticReadoutFoldState
                  tail.succ counterWidth p x)).registers =
            false :=
        fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_clean_before
          tail counterWidth comparisonIndex targetIndex workIndex p x rounds
          (by omega)
          (Nat.le_trans (Nat.le_succ rounds) hrounds)
          (fun priorIndex hprior =>
            certAt priorIndex
              (Nat.lt_trans hprior (Nat.lt_succ_self rounds)))
      rw [
        fixedRoundModeControlledSemanticReadoutPrefixState_succ
          tail counterWidth comparisonIndex currentIndex workIndex
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)]
      exact hstep.trans hprev

/-- The selected history register for a schedule slot is clean immediately
before that slot executes. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_clean_before_slot
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certBefore :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        priorIndex.val < roundIndex.val ->
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers =
      false :=
  fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_clean_before
    tail counterWidth comparisonIndex roundIndex workIndex p x roundIndex.val
    (Nat.le_refl roundIndex.val) (Nat.le_of_lt roundIndex.isLt) certBefore

/-- Build the per-slot readout certificate for a fresh-workspace prefix from
automatic clean/readout fields plus explicit branch arithmetic side
conditions. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_readoutCertificate_of_arithmetic
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (certBefore :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        priorIndex.val < roundIndex.val ->
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers)
    (arith :
      ModeControlledSemanticStepArithmeticCertificate tail counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers) :
    ModeControlledSemanticStepReadoutCertificate tail counterWidth
      comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
      (fixedRoundModeControlledSemanticReadoutPrefixState
        tail counterWidth comparisonIndex workIndex roundIndex.val
        (initialModeControlledSemanticReadoutFoldState
          tail.succ counterWidth p x)).registers :=
  modeControlledSemanticStepReadoutCertificate_of_clean_arithmetic
    tail counterWidth comparisonIndex
    (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
    (fixedRoundModeControlledSemanticReadoutPrefixState
      tail counterWidth comparisonIndex workIndex roundIndex.val
      (initialModeControlledSemanticReadoutFoldState
        tail.succ counterWidth p x)).registers
    (fixedRoundModeControlledSemanticReadoutPrefixState_scratchA_clean
      tail counterWidth comparisonIndex workIndex
      (initialModeControlledSemanticReadoutFoldState
        tail.succ counterWidth p x) roundIndex.val
      (Nat.le_of_lt roundIndex.isLt) rfl)
    (fixedRoundModeControlledSemanticReadoutPrefixState_scratchB_clean
      tail counterWidth comparisonIndex workIndex
      (initialModeControlledSemanticReadoutFoldState
        tail.succ counterWidth p x) roundIndex.val
      (Nat.le_of_lt roundIndex.isLt) rfl)
    (fixedRoundModeControlledSemanticReadoutPrefixState_compare_clean
      tail counterWidth comparisonIndex workIndex
      (initialModeControlledSemanticReadoutFoldState
        tail.succ counterWidth p x) roundIndex.val
      (Nat.le_of_lt roundIndex.isLt) rfl)
    hfinal
    (fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_clean_before_slot
      tail counterWidth comparisonIndex roundIndex workIndex p x certBefore)
    arith

/-- Generate the full per-slot readout certificate package from per-slot
arithmetic side conditions.  The induction supplies only earlier-slot
certificates to the current slot, matching the before-write history-clean
dependency. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_arithmetic
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepArithmeticCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
      ModeControlledSemanticStepReadoutCertificate tail counterWidth
        comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers := by
  have hcertByVal :
      ∀ k : Nat,
        k < (rnsl17MontgomerySchedule tail.succ).rounds ->
          ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
            roundIndex.val = k ->
              ModeControlledSemanticStepReadoutCertificate tail counterWidth
                comparisonIndex
                (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
                (fixedRoundModeControlledSemanticReadoutPrefixState
                  tail counterWidth comparisonIndex workIndex roundIndex.val
                  (initialModeControlledSemanticReadoutFoldState
                    tail.succ counterWidth p x)).registers := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk roundIndex hroundIndex
        exact
          fixedRoundModeControlledSemanticReadoutPrefixState_readoutCertificate_of_arithmetic
            tail counterWidth comparisonIndex roundIndex workIndex p x hfinal
            (fun priorIndex hprior =>
              ih priorIndex.val (by omega) priorIndex.isLt priorIndex rfl)
            (arithAt roundIndex)
  intro roundIndex
  exact hcertByVal roundIndex.val roundIndex.isLt roundIndex rfl

/-- Generate the full per-slot readout certificate package from per-slot
non-LSB arithmetic side conditions. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_overflow_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (overflowAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepOverflowCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
      ModeControlledSemanticStepReadoutCertificate tail counterWidth
        comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_arithmetic
      tail counterWidth comparisonIndex workIndex p x hfinal
      (fun roundIndex =>
        modeControlledSemanticStepArithmeticCertificate_of_overflow_fields
          tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers
          (overflowAt roundIndex))

/-- Generate the full per-slot readout certificate package from the true
per-slot add/MSB arithmetic fields. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_add_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (addMsbAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepAddMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
      ModeControlledSemanticStepReadoutCertificate tail counterWidth
        comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_overflow_fields
      tail counterWidth comparisonIndex workIndex p x hfinal
      (fun roundIndex =>
        modeControlledSemanticStepOverflowCertificate_of_add_msb_fields
          tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers
          (addMsbAt roundIndex))

/-- Generate the full per-slot readout certificate package from per-slot
coefficient top-bit bounds. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (msbAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
      ModeControlledSemanticStepReadoutCertificate tail counterWidth
        comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_add_msb_fields
      tail counterWidth comparisonIndex workIndex p x hfinal
      (fun roundIndex =>
        modeControlledSemanticStepAddMsbCertificate_of_msb_fields
          tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers
          (msbAt roundIndex))

/-- Per-slot source-invariant package that is sufficient to discharge the
fresh-workspace readout arithmetic certificate through coefficient top-bit
bounds.  It is deliberately stated on the concrete prefix registers, so using
it does not rely on the readout certificate being proved already. -/
structure FixedRoundModeControlledSemanticReadoutPrefixBezoutBounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ) : Prop where
  bezoutAt :
    ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
      let registers :=
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers
      registers.rCoeff.val * registers.v.val +
          registers.sCoeff.val * registers.u.val = p.val
  uNonzeroAt :
    ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
      let registers :=
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers
      registers.active = true -> registers.v.val ≠ 0 -> registers.u.val ≠ 0

/-- Generate the full per-slot readout certificate package from concrete
per-slot Bezout bounds. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_bezout_bounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (bounds :
      FixedRoundModeControlledSemanticReadoutPrefixBezoutBounds
        tail counterWidth comparisonIndex workIndex p x) :
    ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
      ModeControlledSemanticStepReadoutCertificate tail counterWidth
        comparisonIndex (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_msb_fields
      tail counterWidth comparisonIndex workIndex p x hfinal
      (fun roundIndex =>
        modeControlledSemanticStepMsbCertificate_of_bezout_bound
          tail counterWidth p.val
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers
          (by simpa using bounds.bezoutAt roundIndex)
          p.isLt
          (by simpa using bounds.uNonzeroAt roundIndex))

/-- A one-slot extension of the fresh-workspace readout prefix agrees with a
one-round source extension of the readout prefix state. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_roundState_succ
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth)
    (cert :
      ModeControlledSemanticStepReadoutCertificate tail counterWidth
        comparisonIndex
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex roundIndex.val
          state).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (roundIndex.val + 1) state) =
      RoundState.round
        (modeControlledSemanticReadoutFoldStateRoundState
          tail.succ counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            state)) ∧
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (roundIndex.val + 1) state).registers =
      RoundState.historyBit
        (modeControlledSemanticReadoutFoldStateRoundState
          tail.succ counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            state)) := by
  rw [
    fixedRoundModeControlledSemanticReadoutPrefixState_succ
      tail counterWidth comparisonIndex roundIndex workIndex state]
  exact
    fixedRoundModeControlledSemanticReadoutStep_roundState_complete
      tail counterWidth comparisonIndex roundIndex workIndex
      (fixedRoundModeControlledSemanticReadoutPrefixState
        tail counterWidth comparisonIndex workIndex roundIndex.val state)
      cert

/-- Conditional prefix induction for the fresh-workspace corrected semantic
readout fold: if every consumed source slot has the full readout certificate
needed by the one-round dispatcher, the prefix readout agrees with the source
`RoundState.runRounds` prefix. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_roundState_eq_runRounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    ∀ (rounds : Nat),
      rounds ≤ (rnsl17MontgomerySchedule tail.succ).rounds ->
        (∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
          roundIndex.val < rounds ->
            ModeControlledSemanticStepReadoutCertificate tail counterWidth
              comparisonIndex
              (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
              (fixedRoundModeControlledSemanticReadoutPrefixState
                tail counterWidth comparisonIndex workIndex roundIndex.val
                state).registers) ->
        modeControlledSemanticReadoutFoldStateRoundState
            tail.succ counterWidth
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex rounds state) =
          RoundState.runRounds rounds
            (modeControlledSemanticReadoutFoldStateRoundState
              tail.succ counterWidth state)
  | 0, _hrounds, _certAt => rfl
  | rounds + 1, hrounds, certAt => by
      have hroundIndex : rounds <
          (rnsl17MontgomerySchedule tail.succ).rounds :=
        Nat.lt_of_succ_le hrounds
      let roundIndex :
          Fin (rnsl17MontgomerySchedule tail.succ).rounds :=
        ⟨rounds, hroundIndex⟩
      have hprev :
          modeControlledSemanticReadoutFoldStateRoundState
              tail.succ counterWidth
              (fixedRoundModeControlledSemanticReadoutPrefixState
                tail counterWidth comparisonIndex workIndex rounds state) =
            RoundState.runRounds rounds
              (modeControlledSemanticReadoutFoldStateRoundState
                tail.succ counterWidth state) :=
        fixedRoundModeControlledSemanticReadoutPrefixState_roundState_eq_runRounds
          tail counterWidth comparisonIndex workIndex state rounds
          (Nat.le_trans (Nat.le_succ rounds) hrounds)
          (fun priorIndex hprior =>
            certAt priorIndex
              (Nat.lt_trans hprior (Nat.lt_succ_self rounds)))
      have hstep :=
        fixedRoundModeControlledSemanticReadoutPrefixState_roundState_succ
          tail counterWidth comparisonIndex roundIndex workIndex state
          (certAt roundIndex (Nat.lt_succ_self rounds))
      calc
        modeControlledSemanticReadoutFoldStateRoundState
            tail.succ counterWidth
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex
              (rounds + 1) state)
            = RoundState.round
                (modeControlledSemanticReadoutFoldStateRoundState
                  tail.succ counterWidth
                  (fixedRoundModeControlledSemanticReadoutPrefixState
                    tail counterWidth comparisonIndex workIndex rounds
                    state)) := hstep.1
        _ = RoundState.round
              (RoundState.runRounds rounds
                (modeControlledSemanticReadoutFoldStateRoundState
                  tail.succ counterWidth state)) := by
          rw [hprev]
        _ = RoundState.runRounds (rounds + 1)
              (modeControlledSemanticReadoutFoldStateRoundState
                tail.succ counterWidth state) := by
          rw [RoundState.runRounds_succ_eq_round_runRounds]

/-- Full fixed-round source-state corollary for the fresh-workspace corrected
semantic readout fold started from the clean finite-register seed. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepReadoutCertificate tail counterWidth
          comparisonIndex
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      RoundState.fixedRoundState tail.succ p.val x.val := by
  have hprefix :=
    fixedRoundModeControlledSemanticReadoutPrefixState_roundState_eq_runRounds
      tail counterWidth comparisonIndex workIndex
      (initialModeControlledSemanticReadoutFoldState
        tail.succ counterWidth p x)
      (rnsl17MontgomerySchedule tail.succ).rounds (by rfl)
      (fun roundIndex _h => certAt roundIndex)
  simpa [
    RoundState.fixedRoundState,
    initialModeControlledSemanticReadoutFoldState_roundState] using hprefix

/-- Full fixed-round source-state corollary using only per-slot arithmetic
side conditions plus the final comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState_of_arithmetic
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepArithmeticCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      RoundState.fixedRoundState tail.succ p.val x.val := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_arithmetic
        tail counterWidth comparisonIndex workIndex p x hfinal arithAt)

/-- Full fixed-round source-state corollary using only per-slot non-LSB
arithmetic side conditions plus the final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState_of_overflow_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (overflowAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepOverflowCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      RoundState.fixedRoundState tail.succ p.val x.val := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_overflow_fields
        tail counterWidth comparisonIndex workIndex p x hfinal overflowAt)

/-- Full fixed-round source-state corollary using only per-slot add/MSB
arithmetic side conditions plus the final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState_of_add_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (addMsbAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepAddMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      RoundState.fixedRoundState tail.succ p.val x.val := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_add_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal addMsbAt)

/-- Full fixed-round source-state corollary using only per-slot coefficient
top-bit bounds plus the final comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState_of_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (msbAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      RoundState.fixedRoundState tail.succ p.val x.val := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal msbAt)

/-- Full fixed-round source-state corollary using concrete per-slot Bezout
bounds plus the final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState_of_bezout_bounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (bounds :
      FixedRoundModeControlledSemanticReadoutPrefixBezoutBounds
        tail counterWidth comparisonIndex workIndex p x) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      RoundState.fixedRoundState tail.succ p.val x.val := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_bezout_bounds
        tail counterWidth comparisonIndex workIndex p x hfinal bounds)

/-- The selected history slot after its fresh-workspace readout step agrees
with the source history bit of the corresponding `runRounds` prefix. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_succ_eq_runRounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth)
    (certAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        priorIndex.val ≤ roundIndex.val ->
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              state).registers) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (roundIndex.val + 1) state).registers =
      RoundState.historyBit
        (RoundState.runRounds roundIndex.val
          (modeControlledSemanticReadoutFoldStateRoundState
            tail.succ counterWidth state)) := by
  have hstep :=
    fixedRoundModeControlledSemanticReadoutPrefixState_roundState_succ
      tail counterWidth comparisonIndex roundIndex workIndex state
      (certAt roundIndex (Nat.le_refl roundIndex.val))
  have hprefix :
      modeControlledSemanticReadoutFoldStateRoundState
          tail.succ counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            state) =
        RoundState.runRounds roundIndex.val
          (modeControlledSemanticReadoutFoldStateRoundState
            tail.succ counterWidth state) :=
    fixedRoundModeControlledSemanticReadoutPrefixState_roundState_eq_runRounds
      tail counterWidth comparisonIndex workIndex state roundIndex.val
      (Nat.le_of_lt roundIndex.isLt)
      (fun priorIndex hprior => certAt priorIndex (Nat.le_of_lt hprior))
  calc
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (roundIndex.val + 1) state).registers
        = RoundState.historyBit
            (modeControlledSemanticReadoutFoldStateRoundState
              tail.succ counterWidth
              (fixedRoundModeControlledSemanticReadoutPrefixState
                tail counterWidth comparisonIndex workIndex roundIndex.val
                state)) := hstep.2
    _ = RoundState.historyBit
          (RoundState.runRounds roundIndex.val
            (modeControlledSemanticReadoutFoldStateRoundState
              tail.succ counterWidth state)) := by
      rw [hprefix]

/-- Clean-seed history readout corollary for one fixed-round schedule slot of
the fresh-workspace corrected semantic readout fold. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_succ_eq_fixedRoundHistoryAt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        priorIndex.val ≤ roundIndex.val ->
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (roundIndex.val + 1)
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers =
      RoundState.fixedRoundHistoryAt
        tail.succ p.val x.val roundIndex := by
  have hhistory :=
    fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_succ_eq_runRounds
      tail counterWidth comparisonIndex roundIndex workIndex
      (initialModeControlledSemanticReadoutFoldState
        tail.succ counterWidth p x)
      certAt
  calc
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (roundIndex.val + 1)
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers
        = RoundState.historyBit
            (RoundState.runRounds roundIndex.val
              (modeControlledSemanticReadoutFoldStateRoundState
                tail.succ counterWidth
                (initialModeControlledSemanticReadoutFoldState
                  tail.succ counterWidth p x))) := hhistory
    _ = RoundState.fixedRoundHistoryAt tail.succ p.val x.val roundIndex := by
      rw [initialModeControlledSemanticReadoutFoldState_roundState]
      exact
        (RoundState.fixedRoundHistoryAt_eq_historyBit_prefix
          tail.succ p.val x.val roundIndex).symm

/-- Once a schedule slot has been written, every later fresh-workspace readout
step preserves that slot. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_preserved_after
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (targetIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (observed : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1))
    (state :
      ModeControlledSemanticReadoutFoldState tail.succ counterWidth) :
    ∀ (rounds : Nat),
      targetIndex.val + 1 ≤ rounds ->
        rounds ≤ (rnsl17MontgomerySchedule tail.succ).rounds ->
          observed = RoundState.fixedRoundHistoryIndex tail.succ targetIndex ->
            (∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
              roundIndex.val < rounds ->
                ModeControlledSemanticStepReadoutCertificate tail counterWidth
                  comparisonIndex
                  (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
                  (fixedRoundModeControlledSemanticReadoutPrefixState
                    tail counterWidth comparisonIndex workIndex roundIndex.val
                    state).registers) ->
            (RegisterBits.historyBit tail.succ counterWidth observed).get
                (fixedRoundModeControlledSemanticReadoutPrefixState
                  tail counterWidth comparisonIndex workIndex rounds
                  state).registers =
              (RegisterBits.historyBit tail.succ counterWidth observed).get
                (fixedRoundModeControlledSemanticReadoutPrefixState
                  tail counterWidth comparisonIndex workIndex
                  (targetIndex.val + 1) state).registers
  | 0, htarget, _hrounds, _hobserved, _certAt => by
      omega
  | rounds + 1, htarget, hrounds, hobserved, certAt => by
      by_cases hbase : rounds = targetIndex.val
      · have hs : rounds + 1 = targetIndex.val + 1 := by omega
        rw [hs]
      · have htargetPrev : targetIndex.val + 1 ≤ rounds := by
          omega
        have hroundsPrev :
            rounds ≤ (rnsl17MontgomerySchedule tail.succ).rounds := by
          exact Nat.le_trans (Nat.le_succ rounds) hrounds
        have hcurrentLt :
            rounds < (rnsl17MontgomerySchedule tail.succ).rounds :=
          Nat.lt_of_succ_le hrounds
        let currentIndex :
            Fin (rnsl17MontgomerySchedule tail.succ).rounds :=
          ⟨rounds, hcurrentLt⟩
        have hcurrentNe : currentIndex ≠ targetIndex := by
          intro heq
          have hval := congrArg Fin.val heq
          dsimp [currentIndex] at hval
          omega
        have hslotNe :
            RoundState.fixedRoundHistoryIndex tail.succ currentIndex ≠
              observed := by
          rw [hobserved]
          exact
            RoundState.fixedRoundHistoryIndex_ne_of_ne
              tail.succ hcurrentNe
        have hstep :=
          fixedRoundModeControlledSemanticReadoutStep_get_historyBit_of_ne
            tail counterWidth comparisonIndex currentIndex observed workIndex
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex rounds state)
            (certAt currentIndex (Nat.lt_succ_self rounds))
            hslotNe
        rw [
          fixedRoundModeControlledSemanticReadoutPrefixState_succ
            tail counterWidth comparisonIndex currentIndex workIndex state]
        calc
          (RegisterBits.historyBit tail.succ counterWidth observed).get
              (fixedRoundModeControlledSemanticReadoutStep
                tail counterWidth comparisonIndex currentIndex workIndex
                (fixedRoundModeControlledSemanticReadoutPrefixState
                  tail counterWidth comparisonIndex workIndex rounds
                  state)).registers
              =
            (RegisterBits.historyBit tail.succ counterWidth observed).get
              (fixedRoundModeControlledSemanticReadoutPrefixState
                tail counterWidth comparisonIndex workIndex rounds
                state).registers := hstep
          _ =
            (RegisterBits.historyBit tail.succ counterWidth observed).get
              (fixedRoundModeControlledSemanticReadoutPrefixState
                tail counterWidth comparisonIndex workIndex
                (targetIndex.val + 1) state).registers :=
            fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_preserved_after
              tail counterWidth comparisonIndex targetIndex observed workIndex
              state rounds htargetPrev hroundsPrev hobserved
              (fun priorIndex hprior =>
                certAt priorIndex
                  (Nat.lt_trans hprior (Nat.lt_succ_self rounds)))

/-- Under the per-slot readout certificates, the final register for a fixed
history slot in the full fresh-workspace readout fold agrees with the source
fixed-round history value. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_eq_fixedRoundHistoryAt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers =
      RoundState.fixedRoundHistoryAt tail.succ p.val x.val roundIndex := by
  have hpreserve :=
    fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_preserved_after
      tail counterWidth comparisonIndex roundIndex
      (RoundState.fixedRoundHistoryIndex tail.succ roundIndex) workIndex
      (initialModeControlledSemanticReadoutFoldState
        tail.succ counterWidth p x)
      (rnsl17MontgomerySchedule tail.succ).rounds
      (Nat.succ_le_of_lt roundIndex.isLt) (by rfl) rfl
      (fun priorIndex _hprior => certAt priorIndex)
  have himmediate :=
    fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_succ_eq_fixedRoundHistoryAt
      tail counterWidth comparisonIndex roundIndex workIndex p x
      (fun priorIndex _hprior => certAt priorIndex)
  exact hpreserve.trans himmediate

/-- Final-register history-slot corollary using only per-slot arithmetic side
conditions plus the final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_of_arithmetic
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepArithmeticCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers =
      RoundState.fixedRoundHistoryAt tail.succ p.val x.val roundIndex := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_eq_fixedRoundHistoryAt
      tail counterWidth comparisonIndex roundIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_arithmetic
        tail counterWidth comparisonIndex workIndex p x hfinal arithAt)

/-- Final-register history-slot corollary using only per-slot non-LSB
arithmetic side conditions plus the final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_of_overflow_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (overflowAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepOverflowCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers =
      RoundState.fixedRoundHistoryAt tail.succ p.val x.val roundIndex := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_eq_fixedRoundHistoryAt
      tail counterWidth comparisonIndex roundIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_overflow_fields
        tail counterWidth comparisonIndex workIndex p x hfinal overflowAt)

/-- Final-register history-slot corollary using only per-slot add/MSB
arithmetic side conditions plus the final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_of_add_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (addMsbAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepAddMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers =
      RoundState.fixedRoundHistoryAt tail.succ p.val x.val roundIndex := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_eq_fixedRoundHistoryAt
      tail counterWidth comparisonIndex roundIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_add_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal addMsbAt)

/-- Final-register history-slot corollary using only per-slot coefficient
top-bit bounds plus the final comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_of_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (msbAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers =
      RoundState.fixedRoundHistoryAt tail.succ p.val x.val roundIndex := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_eq_fixedRoundHistoryAt
      tail counterWidth comparisonIndex roundIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal msbAt)

/-- Final-register history-slot corollary using concrete per-slot Bezout
bounds plus the final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_of_bezout_bounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (bounds :
      FixedRoundModeControlledSemanticReadoutPrefixBezoutBounds
        tail counterWidth comparisonIndex workIndex p x) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers =
      RoundState.fixedRoundHistoryAt tail.succ p.val x.val roundIndex := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_eq_fixedRoundHistoryAt
      tail counterWidth comparisonIndex roundIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_bezout_bounds
        tail counterWidth comparisonIndex workIndex p x hfinal bounds)

end
end MK
end MAU.Inversion
end QuantumAlg


namespace QuantumAlg
namespace NumberTheory.BinaryGCD
namespace Trace

open QuantumAlg.MAU.Inversion
open QuantumAlg.MAU.Inversion.MK
open QuantumAlg.Nat.FixedWidth


/-- Fresh-workspace corrected semantic readout fold reaches the finish state of
the canonical fixed-round trace, under the same per-slot certificate package as
the source-prefix theorem. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_finish
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepReadoutCertificate tail counterWidth
          comparisonIndex
          (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      (Trace.ofInput tail.succ p.val x.val).finish := by
  simpa [Trace.ofInput] using
    fixedRoundModeControlledSemanticReadoutPrefixState_full_roundState
      tail counterWidth comparisonIndex workIndex p x certAt

/-- Fresh-workspace corrected semantic readout fold reaches the canonical
finish state from per-slot arithmetic side conditions plus the final
comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_finish_of_arithmetic
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepArithmeticCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      (Trace.ofInput tail.succ p.val x.val).finish := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_finish
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_arithmetic
        tail counterWidth comparisonIndex workIndex p x hfinal arithAt)

/-- Fresh-workspace corrected semantic readout fold reaches the canonical
finish state from per-slot non-LSB arithmetic side conditions plus the final
comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_finish_of_overflow_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (overflowAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepOverflowCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      (Trace.ofInput tail.succ p.val x.val).finish := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_finish
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_overflow_fields
        tail counterWidth comparisonIndex workIndex p x hfinal overflowAt)

/-- Fresh-workspace corrected semantic readout fold reaches the canonical
finish state from per-slot add/MSB arithmetic side conditions plus the final
comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_finish_of_add_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (addMsbAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepAddMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      (Trace.ofInput tail.succ p.val x.val).finish := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_finish
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_add_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal addMsbAt)

/-- Fresh-workspace corrected semantic readout fold reaches the canonical
finish state from per-slot coefficient top-bit bounds plus the final
comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_finish_of_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (msbAt :
      ∀ roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex roundIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      (Trace.ofInput tail.succ p.val x.val).finish := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_finish
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal msbAt)

/-- Fresh-workspace corrected semantic readout fold reaches the canonical
finish state from concrete per-slot Bezout bounds plus the final
comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_full_finish_of_bezout_bounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (bounds :
      FixedRoundModeControlledSemanticReadoutPrefixBezoutBounds
        tail counterWidth comparisonIndex workIndex p x) :
    modeControlledSemanticReadoutFoldStateRoundState
        tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      (Trace.ofInput tail.succ p.val x.val).finish := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixState_full_finish
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_bezout_bounds
        tail counterWidth comparisonIndex workIndex p x hfinal bounds)

/-- Fresh-workspace corrected semantic readout fold's selected `m_i` readout
agrees with the canonical trace history view for the same schedule slot. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_succ_eq_historyAt
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (roundIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        priorIndex.val ≤ roundIndex.val ->
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers) :
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (roundIndex.val + 1)
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers =
      (Trace.ofInput tail.succ p.val x.val).historyAt roundIndex := by
  exact
    (fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_succ_eq_fixedRoundHistoryAt
      tail counterWidth comparisonIndex roundIndex workIndex p x certAt).trans
        (Trace.ofInput_historyAt tail.succ p.val x.val roundIndex).symm

/-- Final-register history readout list from the full fresh-workspace
corrected semantic fold. -/
def fixedRoundModeControlledSemanticReadoutFinalHistory
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ) :
    List Bool :=
  List.ofFn fun roundIndex :
      Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers

/-- Under the per-slot readout certificates, the final-register fresh-workspace
history readout list agrees pointwise with the canonical trace history
accessor. -/
lemma fixedRoundModeControlledSemanticReadoutFinalHistory_eq_historyAtList
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutFinalHistory
        tail counterWidth comparisonIndex workIndex p x =
      List.ofFn
        (fun roundIndex :
            Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
          (Trace.ofInput tail.succ p.val x.val).historyAt roundIndex) := by
  unfold fixedRoundModeControlledSemanticReadoutFinalHistory
  exact
    congrArg List.ofFn
      (funext fun roundIndex => by
        exact
          (fixedRoundModeControlledSemanticReadoutPrefixState_full_historyBit_eq_fixedRoundHistoryAt
            tail counterWidth comparisonIndex roundIndex workIndex p x certAt).trans
              (Trace.ofInput_historyAt tail.succ p.val x.val roundIndex).symm)

/-- Under the per-slot readout certificates, the final-register fresh-workspace
history readout list agrees with the materialized canonical trace history list.
-/
lemma fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutFinalHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  rw [
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_historyAtList
      tail counterWidth comparisonIndex workIndex p x certAt]
  exact
    (Trace.history_eq_ofFn_historyAt
      (Trace.ofInput tail.succ p.val x.val)).symm

/-- Final-register fresh-workspace history readout list agrees with the
canonical trace history list from per-slot arithmetic side conditions plus the
final comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory_of_arithmetic
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepArithmeticCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutFinalHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_arithmetic
        tail counterWidth comparisonIndex workIndex p x hfinal arithAt)

/-- Final-register fresh-workspace history readout list agrees with the
canonical trace history list from per-slot non-LSB arithmetic side conditions
plus the final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory_of_overflow_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (overflowAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepOverflowCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutFinalHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_overflow_fields
        tail counterWidth comparisonIndex workIndex p x hfinal overflowAt)

/-- Final-register fresh-workspace history readout list agrees with the
canonical trace history list from per-slot add/MSB arithmetic side conditions
plus the final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory_of_add_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (addMsbAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepAddMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutFinalHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_add_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal addMsbAt)

/-- Final-register fresh-workspace history readout list agrees with the
canonical trace history list from per-slot coefficient top-bit bounds plus the
final comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory_of_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (msbAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutFinalHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal msbAt)

/-- Final-register fresh-workspace history readout list agrees with the
canonical trace history list from concrete per-slot Bezout bounds plus the
final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory_of_bezout_bounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (bounds :
      FixedRoundModeControlledSemanticReadoutPrefixBezoutBounds
        tail counterWidth comparisonIndex workIndex p x) :
    fixedRoundModeControlledSemanticReadoutFinalHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_bezout_bounds
        tail counterWidth comparisonIndex workIndex p x hfinal bounds)

/-- List of per-slot history readouts from the fresh-workspace corrected
semantic fold.  The `i`-th entry is read immediately after executing slot `i`.
-/
def fixedRoundModeControlledSemanticReadoutPrefixHistory
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ) :
    List Bool :=
  List.ofFn fun roundIndex :
      Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
    (RegisterBits.historyBit tail.succ counterWidth
        (RoundState.fixedRoundHistoryIndex tail.succ roundIndex)).get
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (roundIndex.val + 1)
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)).registers

/-- The per-slot fresh-workspace history readout list agrees pointwise with the
canonical trace history accessor. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_historyAtList
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutPrefixHistory
        tail counterWidth comparisonIndex workIndex p x =
      List.ofFn
        (fun roundIndex :
            Fin (rnsl17MontgomerySchedule tail.succ).rounds =>
          (Trace.ofInput tail.succ p.val x.val).historyAt roundIndex) := by
  unfold fixedRoundModeControlledSemanticReadoutPrefixHistory
  exact
    congrArg List.ofFn
      (funext fun roundIndex =>
        fixedRoundModeControlledSemanticReadoutPrefixState_historyBit_succ_eq_historyAt
          tail counterWidth comparisonIndex roundIndex workIndex p x
          (fun priorIndex _ => certAt priorIndex))

/-- The per-slot fresh-workspace history readout list agrees with the
materialized canonical trace history list. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutPrefixHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  rw [
    fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_historyAtList
      tail counterWidth comparisonIndex workIndex p x certAt]
  exact
    (Trace.history_eq_ofFn_historyAt
      (Trace.ofInput tail.succ p.val x.val)).symm

/-- Per-slot fresh-workspace history readout list agrees with the canonical
trace history list from per-slot arithmetic side conditions plus the final
comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory_of_arithmetic
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepArithmeticCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutPrefixHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_arithmetic
        tail counterWidth comparisonIndex workIndex p x hfinal arithAt)

/-- Per-slot fresh-workspace history readout list agrees with the canonical
trace history list from per-slot non-LSB arithmetic side conditions plus the
final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory_of_overflow_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (overflowAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepOverflowCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutPrefixHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_overflow_fields
        tail counterWidth comparisonIndex workIndex p x hfinal overflowAt)

/-- Per-slot fresh-workspace history readout list agrees with the canonical
trace history list from per-slot add/MSB arithmetic side conditions plus the
final comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory_of_add_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (addMsbAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepAddMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutPrefixHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_add_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal addMsbAt)

/-- Per-slot fresh-workspace history readout list agrees with the canonical
trace history list from per-slot coefficient top-bit bounds plus the final
comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory_of_msb_fields
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (msbAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
        ModeControlledSemanticStepMsbCertificate tail counterWidth
          (fixedRoundModeControlledSemanticReadoutPrefixState
            tail counterWidth comparisonIndex workIndex priorIndex.val
            (initialModeControlledSemanticReadoutFoldState
              tail.succ counterWidth p x)).registers) :
    fixedRoundModeControlledSemanticReadoutPrefixHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_msb_fields
        tail counterWidth comparisonIndex workIndex p x hfinal msbAt)

/-- Per-slot fresh-workspace history readout list agrees with the canonical
trace history list from concrete per-slot Bezout bounds plus the final
comparison-index condition. -/
lemma
    fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory_of_bezout_bounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (bounds :
      FixedRoundModeControlledSemanticReadoutPrefixBezoutBounds
        tail counterWidth comparisonIndex workIndex p x) :
    fixedRoundModeControlledSemanticReadoutPrefixHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history := by
  exact
    fixedRoundModeControlledSemanticReadoutPrefixHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x
      (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_bezout_bounds
        tail counterWidth comparisonIndex workIndex p x hfinal bounds)

/-- Combined fixed-round agreement between the fresh-workspace corrected
semantic readout fold and the canonical trace: the final source-shaped state and
the final stored history bits both match the trace produced by the selected
`2n` schedule. -/
structure FixedRoundModeControlledSemanticReadoutAgreement
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ) : Prop where
  finish :
    modeControlledSemanticReadoutFoldStateRoundState tail.succ counterWidth
        (fixedRoundModeControlledSemanticReadoutPrefixState
          tail counterWidth comparisonIndex workIndex
          (rnsl17MontgomerySchedule tail.succ).rounds
          (initialModeControlledSemanticReadoutFoldState
            tail.succ counterWidth p x)) =
      (Trace.ofInput tail.succ p.val x.val).finish
  history :
    fixedRoundModeControlledSemanticReadoutFinalHistory
        tail counterWidth comparisonIndex workIndex p x =
      (Trace.ofInput tail.succ p.val x.val).history

/-- Package the fresh-workspace fixed-round final state and final stored-history
readout equalities into one trace-agreement witness. -/
lemma fixedRoundModeControlledSemanticReadoutAgreement
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (certAt :
      ∀ priorIndex : Fin (rnsl17MontgomerySchedule tail.succ).rounds,
          ModeControlledSemanticStepReadoutCertificate tail counterWidth
            comparisonIndex
            (RoundState.fixedRoundHistoryIndex tail.succ priorIndex)
            (fixedRoundModeControlledSemanticReadoutPrefixState
              tail counterWidth comparisonIndex workIndex priorIndex.val
              (initialModeControlledSemanticReadoutFoldState
                tail.succ counterWidth p x)).registers) :
    FixedRoundModeControlledSemanticReadoutAgreement
      tail counterWidth comparisonIndex workIndex p x where
  finish :=
    fixedRoundModeControlledSemanticReadoutPrefixState_full_finish
      tail counterWidth comparisonIndex workIndex p x certAt
  history :=
    fixedRoundModeControlledSemanticReadoutFinalHistory_eq_traceHistory
      tail counterWidth comparisonIndex workIndex p x certAt

/-- Package the fresh-workspace fixed-round trace agreement from concrete
per-slot Bezout bounds and the final comparison-index condition. -/
lemma fixedRoundModeControlledSemanticReadoutAgreement_of_bezout_bounds
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (p x : Word tail.succ)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (bounds :
      FixedRoundModeControlledSemanticReadoutPrefixBezoutBounds
        tail counterWidth comparisonIndex workIndex p x) :
    FixedRoundModeControlledSemanticReadoutAgreement
      tail counterWidth comparisonIndex workIndex p x :=
  fixedRoundModeControlledSemanticReadoutAgreement
    tail counterWidth comparisonIndex workIndex p x
    (fixedRoundModeControlledSemanticReadoutPrefixState_certAt_of_bezout_bounds
      tail counterWidth comparisonIndex workIndex p x hfinal bounds)

/-- Arithmetic bridge predicate for a scaled endpoint: the corrected trace-side
residue equals the explicitly scaled inverse of the supplied staged input. -/
def CorrectedResidueMatchesScaledUnitInverse {n p : Nat}
    (trace : Trace n) (scale : ZMod p) (u : (ZMod p)ˣ) : Prop :=
  trace.correctedInverseResidue p = scaledInverseResidue scale u

lemma correctedResidueMatchesScaledUnitInverse_of_mul_input_eq {n p : Nat}
    (trace : Trace n) (scale : ZMod p) (u : (ZMod p)ˣ)
    (hmul : trace.correctedInverseResidue p * (u : ZMod p) = scale) :
    trace.CorrectedResidueMatchesScaledUnitInverse scale u := by
  change trace.correctedInverseResidue p = scaledInverseResidue scale u
  exact eq_scaledInverseResidue_of_mul_input_eq
    (trace.correctedInverseResidue p) scale u hmul

/-- Final fixed-trace correction bridge into the explicitly scaled endpoint.
For the RNSL/HJN Montgomery route, the scale is the fixed source factor. -/
lemma ofInput_correctedResidueMatchesScaledUnitInverse_of_final_state
    (n p x : Nat) (u : (ZMod p)ˣ)
    (hx : (x : ZMod p) = (u : ZMod p))
    (hfinish : (ofInput n p x).finish.u = 1) :
    (ofInput n p x).CorrectedResidueMatchesScaledUnitInverse
      (-((2 : ZMod p) ^ (2 * n))) u := by
  apply correctedResidueMatchesScaledUnitInverse_of_mul_input_eq
  calc
    (ofInput n p x).correctedInverseResidue p * (u : ZMod p)
        = (ofInput n p x).correctedInverseResidue p * (x : ZMod p) := by
      rw [hx]
    _ = -((2 : ZMod p) ^ (2 * n)) :=
      ofInput_correctedInverseResidue_mul_input_eq_neg_pow_of_final_state
        n p x hfinish

/-- Unit-input form of the final fixed-trace correction bridge into the scaled
endpoint. -/
lemma ofUnitInput_correctedResidueMatchesScaledUnitInverse_of_final_state
    (n p : Nat) [NeZero p] (u : (ZMod p)ˣ)
    (hfinish : (ofUnitInput n p u).finish.u = 1) :
    (ofUnitInput n p u).CorrectedResidueMatchesScaledUnitInverse
      (-((2 : ZMod p) ^ (2 * n))) u := by
  change
    (ofInput n p (u : ZMod p).val).CorrectedResidueMatchesScaledUnitInverse
      (-((2 : ZMod p) ^ (2 * n))) u
  exact ofInput_correctedResidueMatchesScaledUnitInverse_of_final_state
    n p (u : ZMod p).val u
    (by simp)
    (by simpa [ofUnitInput] using hfinish)

/-- The sign-adjusted unit-input endpoint is the unit inverse scaled by the
positive Montgomery factor `2^(2n)`. -/
lemma
    ofUnitInput_signedCorrectedInverseResidue_eq_scaledInverseResidue_of_final_state
    (n p : Nat) [NeZero p] (u : (ZMod p)ˣ)
    (hfinish : (ofUnitInput n p u).finish.u = 1) :
    (ofUnitInput n p u).signedCorrectedInverseResidue p =
      scaledInverseResidue ((2 : ZMod p) ^ (2 * n)) u := by
  exact eq_scaledInverseResidue_of_mul_input_eq
    ((ofUnitInput n p u).signedCorrectedInverseResidue p)
    ((2 : ZMod p) ^ (2 * n)) u
    (ofUnitInput_signedCorrectedInverseResidue_mul_input_eq_pow_of_final_state
      n p u hfinish)

/-- Explicit raw-inverse bridge for any supplied inverse of the positive
Montgomery scale.  Unlike the old normalization premise, this asks for a
multiplicative inverse of the scale rather than asking the scale itself to be
`1`. -/
lemma
    ofUnitInput_unscaleSignedCorrectedInverseResidue_eq_inverseResidue_of_final_state
    (n p : Nat) [NeZero p] (u : (ZMod p)ˣ) (inverseScale : ZMod p)
    (hfinish : (ofUnitInput n p u).finish.u = 1)
    (hinverseScale :
      inverseScale * (2 : ZMod p) ^ (2 * n) = 1) :
    unscaleResidue inverseScale
        ((ofUnitInput n p u).signedCorrectedInverseResidue p) =
      inverseResidue u := by
  rw [
    ofUnitInput_signedCorrectedInverseResidue_eq_scaledInverseResidue_of_final_state
      n p u hfinish]
  exact unscaleResidue_scaledInverseResidue
    inverseScale ((2 : ZMod p) ^ (2 * n)) u hinverseScale

/-- For an odd actual modulus, the canonical inverse-scale construction
discharges the raw-unscale premise. -/
lemma
    ofUnitInput_inverseMontgomeryScale_mul_signedCorrectedInverseResidue_eq_inverseResidue
    (n p : Nat) (hodd : Odd p) (u : (ZMod p)ˣ)
    (hfinish : (ofUnitInput n p u).finish.u = 1) :
    unscaleResidue (inverseMontgomeryScale p n hodd)
        ((ofUnitInput n p u).signedCorrectedInverseResidue p) =
      inverseResidue u := by
  let _ : NeZero p := ⟨by
    rcases hodd with ⟨k, hk⟩
    omega⟩
  exact
    ofUnitInput_unscaleSignedCorrectedInverseResidue_eq_inverseResidue_of_final_state
      n p u (inverseMontgomeryScale p n hodd) hfinish
      (inverseMontgomeryScale_mul_scale p n hodd)

end Trace
end NumberTheory.BinaryGCD
end QuantumAlg

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

end
