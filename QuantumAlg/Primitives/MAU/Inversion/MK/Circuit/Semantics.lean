/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.MK.Readout.Trace
import all QuantumAlg.Primitives.MAU.Inversion.MK.AuxiliaryShift

/-!
# Compact fixed-round semantics

This leaf proves that the literal compact active-branch body implements the
source-level Montgomery--Kaliski updates.  Physical gate composition and the
full fixed-round fold remain in the MK circuit module.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Circuit

noncomputable section

open MK
open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

namespace CompactCertificate

open MK.Compact

-- Keep the two actual semantic heads intact while applying their proved
-- cleanup projections; expanding the full routed gate interpreter here repeats
-- the same conversion for every field. This attribute is local to this proof file.
attribute [local irreducible] activeBranchBodyStep activeBranchRoutedStep

set_option maxHeartbeats 2000000 in
-- The four exact word bridges normalize the literal routed gate stages.
/-- On the active `uEven` branch, the complete compact body has exactly the
source-level Montgomery--Kaliski data semantics. -/
lemma activeBranchBody_uEven_sourceStep
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hvNonzero : x.core.v.val ≠ 0)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (huEven : x.core.u.val.testBit (0 : Nat) = false)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RoundState.fromRegisters tail.succ counterWidth
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x).core
        (kaliskiSteps + 1) paddingSteps =
      RoundState.applyBranch Branch.uEven
        (RoundState.fromRegisters tail.succ counterWidth x.core
          kaliskiSteps paddingSteps) := by
  let routed := activeBranchRoutedStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  let output := activeBranchBodyStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  let staged := selectedBranchCodeToScratchStep tail.succ counterWidth
    (0 : Fin tail.succ) tempIndex x
  let written := MK.Compact.activeScratchBToHistoryStep tail.succ counterWidth
    historyIndex staged
  let legacy := selectedBranchCodeThenHistoryThenShiftStep
    tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
  have hactiveBit : (activeBit tail.succ counterWidth).get x = true := by
    simpa only [activeBit_get] using hactive
  have hcompareBit : (compareBit tail.succ counterWidth).get x = false := by
    simpa only [compareBit_get] using hcompare
  have hscratchABit :
      (scratchABit tail.succ counterWidth).get x = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBBit :
      (scratchBBit tail.succ counterWidth).get x = false := by
    simpa only [scratchBBit_get] using hscratchB
  have huLow :
      (uLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = false := by
    simpa [uLowBit] using huEven
  have hpair :
      (((uValueWord tail.succ counterWidth).bit (0 : Fin tail.succ)).get x &&
        ((vValueWord tail.succ counterWidth).bit (0 : Fin tail.succ)).get x) =
        false := by
    rw [show ((uValueWord tail.succ counterWidth).bit
      (0 : Fin tail.succ)).get x = false by simpa [uLowBit] using huLow]
    rfl
  have hroute : routed = legacy := by
    dsimp [routed, legacy]
    exact activeBranchRoutedStep_eq_selected_even_route_of_pair_false
      tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
      historyIndex x hactiveBit hpath hcontrol hcompareBit hscratchABit
      hscratchBBit hpair
  have hshift : legacy = uDiv2ThenSMul2Step
      tail.succ counterWidth written := by
    dsimp [legacy, written, staged]
    exact selectedBranchCodeThenHistoryThenShiftStep_eq_uShift_of_uEven
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hactiveBit huLow hscratchABit hscratchBBit (hwork tempIndex)
  have hwrittenU : written.core.u = x.core.u := by
    dsimp [written, staged]
    rw [MK.Compact.activeScratchBToHistoryStep_core_u,
      selectedBranchCodeToScratchStep_core_u]
  have hwrittenV : written.core.v = x.core.v := by
    dsimp [written, staged]
    rw [MK.Compact.activeScratchBToHistoryStep_core_v,
      selectedBranchCodeToScratchStep_core_v]
  have hwrittenS : written.core.sCoeff = x.core.sCoeff := by
    dsimp [written, staged]
    rw [MK.Compact.activeScratchBToHistoryStep_core_sCoeff,
      selectedBranchCodeToScratchStep_core_sCoeff]
  have hwrittenR : written.core.rCoeff = x.core.rCoeff := by
    dsimp [written, staged]
    rw [MK.Compact.activeScratchBToHistoryStep_core_rCoeff,
      selectedBranchCodeToScratchStep_core_rCoeff]
  have hlsbWritten :
      written.core.u.val.testBit (0 : Nat) = false := by
    rw [hwrittenU]
    exact huEven
  have hmsb :
      x.core.sCoeff.val.testBit (Fin.last tail.succ).val = false :=
    arith.uEven_msb hactive hvNonzero huEven
  have hmsbWritten :
      written.core.sCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenS]
    exact hmsb
  have hroutedU : routed.core.u = wordHalf tail.succ x.core.u := by
    calc
      routed.core.u = legacy.core.u := congrArg (fun y => y.core.u) hroute
      _ = (uDiv2ThenSMul2Step tail.succ counterWidth written).core.u :=
        congrArg (fun y => y.core.u) hshift
      _ = wordHalf tail.succ written.core.u :=
        uDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
          tail counterWidth written hlsbWritten
      _ = wordHalf tail.succ x.core.u := by rw [hwrittenU]
  have hroutedV : routed.core.v = x.core.v := by
    calc
      routed.core.v = legacy.core.v := congrArg (fun y => y.core.v) hroute
      _ = (uDiv2ThenSMul2Step tail.succ counterWidth written).core.v :=
        congrArg (fun y => y.core.v) hshift
      _ = written.core.v := uDiv2ThenSMul2Step_core_v
        tail.succ counterWidth written
      _ = x.core.v := hwrittenV
  have hroutedS : routed.core.sCoeff =
      wordDouble (tail.succ + 1) x.core.sCoeff := by
    calc
      routed.core.sCoeff = legacy.core.sCoeff :=
        congrArg (fun y => y.core.sCoeff) hroute
      _ = (uDiv2ThenSMul2Step tail.succ counterWidth written).core.sCoeff :=
        congrArg (fun y => y.core.sCoeff) hshift
      _ = wordDouble (tail.succ + 1) written.core.sCoeff :=
        uDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
          tail.succ counterWidth written hmsbWritten
      _ = wordDouble (tail.succ + 1) x.core.sCoeff := by rw [hwrittenS]
  have hroutedR : routed.core.rCoeff = x.core.rCoeff := by
    calc
      routed.core.rCoeff = legacy.core.rCoeff :=
        congrArg (fun y => y.core.rCoeff) hroute
      _ = (uDiv2ThenSMul2Step tail.succ counterWidth written).core.rCoeff :=
        congrArg (fun y => y.core.rCoeff) hshift
      _ = written.core.rCoeff := uDiv2ThenSMul2Step_core_rCoeff
        tail.succ counterWidth written
      _ = x.core.rCoeff := hwrittenR
  have hroutedActive : routed.core.active = true := by
    rw [hroute]
    have h := selectedBranchCodeThenHistoryThenShiftStep_get_active
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
    simpa only [legacy, activeBit_get, hactive] using h
  have houtputU : output.core.u = wordHalf tail.succ x.core.u := by
    calc
      output.core.u = routed.core.u := by
        exact activeBranchBodyStep_core_u_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = wordHalf tail.succ x.core.u := hroutedU
  have houtputV : output.core.v = x.core.v := by
    calc
      output.core.v = routed.core.v := by
        exact activeBranchBodyStep_core_v_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = x.core.v := hroutedV
  have houtputS : output.core.sCoeff =
      wordDouble (tail.succ + 1) x.core.sCoeff := by
    calc
      output.core.sCoeff = routed.core.sCoeff := by
        exact activeBranchBodyStep_core_sCoeff_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = wordDouble (tail.succ + 1) x.core.sCoeff := hroutedS
  have houtputR : output.core.rCoeff = x.core.rCoeff := by
    calc
      output.core.rCoeff = routed.core.rCoeff := by
        exact activeBranchBodyStep_core_rCoeff_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = x.core.rCoeff := hroutedR
  have houtputActive : output.core.active = true := by
    calc
      output.core.active = routed.core.active := by
        exact activeBranchBodyStep_core_active_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = true := hroutedActive
  have hdouble : 2 * x.core.sCoeff.val < 2 ^ (tail.succ + 1) :=
    arith.uEven_double hactive hvNonzero huEven
  have houtputUVal : output.core.u.val = x.core.u.val / 2 := by
    rw [houtputU, wordHalf_val]
  have houtputSVal : output.core.sCoeff.val = 2 * x.core.sCoeff.val := by
    rw [houtputS, wordDouble_val_of_no_overflow _ _ hdouble]
  simp [output, RoundState.fromRegisters, RoundState.applyBranch,
    hactive, houtputUVal, houtputV, houtputR, houtputSVal, houtputActive]

set_option maxHeartbeats 2000000 in
-- The four exact word bridges normalize the literal routed gate stages.
/-- On the active `vEven` branch, the complete compact body has exactly the
source-level Montgomery--Kaliski data semantics. -/
lemma activeBranchBody_vEven_sourceStep
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hvNonzero : x.core.v.val ≠ 0)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (huOdd : x.core.u.val.testBit (0 : Nat) = true)
    (hvEven : x.core.v.val.testBit (0 : Nat) = false)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RoundState.fromRegisters tail.succ counterWidth
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x).core
        (kaliskiSteps + 1) paddingSteps =
      RoundState.applyBranch Branch.vEven
        (RoundState.fromRegisters tail.succ counterWidth x.core
          kaliskiSteps paddingSteps) := by
  let routed := activeBranchRoutedStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  let output := activeBranchBodyStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  let staged := selectedBranchCodeToScratchStep tail.succ counterWidth
    (0 : Fin tail.succ) tempIndex x
  let written := MK.Compact.activeScratchBToHistoryStep tail.succ counterWidth
    historyIndex staged
  let legacy := selectedBranchCodeThenHistoryThenShiftStep
    tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
  have hactiveBit : (activeBit tail.succ counterWidth).get x = true := by
    simpa only [activeBit_get] using hactive
  have hcompareBit : (compareBit tail.succ counterWidth).get x = false := by
    simpa only [compareBit_get] using hcompare
  have hscratchABit :
      (scratchABit tail.succ counterWidth).get x = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBBit :
      (scratchBBit tail.succ counterWidth).get x = false := by
    simpa only [scratchBBit_get] using hscratchB
  have huLow :
      (uLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = true := by
    simpa [uLowBit] using huOdd
  have hvLow :
      (vLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = false := by
    simpa [vLowBit] using hvEven
  have hpair :
      (((uValueWord tail.succ counterWidth).bit (0 : Fin tail.succ)).get x &&
        ((vValueWord tail.succ counterWidth).bit (0 : Fin tail.succ)).get x) =
        false := by
    rw [show ((vValueWord tail.succ counterWidth).bit
      (0 : Fin tail.succ)).get x = false by simpa [vLowBit] using hvLow]
    simp
  have hroute : routed = legacy := by
    dsimp [routed, legacy]
    exact activeBranchRoutedStep_eq_selected_even_route_of_pair_false
      tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
      historyIndex x hactiveBit hpath hcontrol hcompareBit hscratchABit
      hscratchBBit hpair
  have hshift : legacy = vDiv2ThenRMul2Step
      tail.succ counterWidth written := by
    dsimp [legacy, written, staged]
    exact selectedBranchCodeThenHistoryThenShiftStep_eq_vShift_of_vEven
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hactiveBit huLow hvLow hscratchABit hscratchBBit (hwork tempIndex)
  have hwrittenU : written.core.u = x.core.u := by
    dsimp [written, staged]
    rw [MK.Compact.activeScratchBToHistoryStep_core_u,
      selectedBranchCodeToScratchStep_core_u]
  have hwrittenV : written.core.v = x.core.v := by
    dsimp [written, staged]
    rw [MK.Compact.activeScratchBToHistoryStep_core_v,
      selectedBranchCodeToScratchStep_core_v]
  have hwrittenS : written.core.sCoeff = x.core.sCoeff := by
    dsimp [written, staged]
    rw [MK.Compact.activeScratchBToHistoryStep_core_sCoeff,
      selectedBranchCodeToScratchStep_core_sCoeff]
  have hwrittenR : written.core.rCoeff = x.core.rCoeff := by
    dsimp [written, staged]
    rw [MK.Compact.activeScratchBToHistoryStep_core_rCoeff,
      selectedBranchCodeToScratchStep_core_rCoeff]
  have hlsbWritten :
      written.core.v.val.testBit (0 : Nat) = false := by
    rw [hwrittenV]
    exact hvEven
  have hmsb :
      x.core.rCoeff.val.testBit (Fin.last tail.succ).val = false :=
    arith.vEven_msb hactive hvNonzero huOdd hvEven
  have hmsbWritten :
      written.core.rCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenR]
    exact hmsb
  have hroutedU : routed.core.u = x.core.u := by
    calc
      routed.core.u = legacy.core.u := congrArg (fun y => y.core.u) hroute
      _ = (vDiv2ThenRMul2Step tail.succ counterWidth written).core.u :=
        congrArg (fun y => y.core.u) hshift
      _ = written.core.u := vDiv2ThenRMul2Step_core_u
        tail.succ counterWidth written
      _ = x.core.u := hwrittenU
  have hroutedV : routed.core.v = wordHalf tail.succ x.core.v := by
    calc
      routed.core.v = legacy.core.v := congrArg (fun y => y.core.v) hroute
      _ = (vDiv2ThenRMul2Step tail.succ counterWidth written).core.v :=
        congrArg (fun y => y.core.v) hshift
      _ = wordHalf tail.succ written.core.v :=
        vDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
          tail counterWidth written hlsbWritten
      _ = wordHalf tail.succ x.core.v := by rw [hwrittenV]
  have hroutedS : routed.core.sCoeff = x.core.sCoeff := by
    calc
      routed.core.sCoeff = legacy.core.sCoeff :=
        congrArg (fun y => y.core.sCoeff) hroute
      _ = (vDiv2ThenRMul2Step tail.succ counterWidth written).core.sCoeff :=
        congrArg (fun y => y.core.sCoeff) hshift
      _ = written.core.sCoeff := vDiv2ThenRMul2Step_core_sCoeff
        tail.succ counterWidth written
      _ = x.core.sCoeff := hwrittenS
  have hroutedR : routed.core.rCoeff =
      wordDouble (tail.succ + 1) x.core.rCoeff := by
    calc
      routed.core.rCoeff = legacy.core.rCoeff :=
        congrArg (fun y => y.core.rCoeff) hroute
      _ = (vDiv2ThenRMul2Step tail.succ counterWidth written).core.rCoeff :=
        congrArg (fun y => y.core.rCoeff) hshift
      _ = wordDouble (tail.succ + 1) written.core.rCoeff :=
        vDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
          tail.succ counterWidth written hmsbWritten
      _ = wordDouble (tail.succ + 1) x.core.rCoeff := by rw [hwrittenR]
  have hroutedActive : routed.core.active = true := by
    rw [hroute]
    have h := selectedBranchCodeThenHistoryThenShiftStep_get_active
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
    simpa only [legacy, activeBit_get, hactive] using h
  have houtputU : output.core.u = x.core.u := by
    calc
      output.core.u = routed.core.u := by
        exact activeBranchBodyStep_core_u_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = x.core.u := hroutedU
  have houtputV : output.core.v = wordHalf tail.succ x.core.v := by
    calc
      output.core.v = routed.core.v := by
        exact activeBranchBodyStep_core_v_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = wordHalf tail.succ x.core.v := hroutedV
  have houtputS : output.core.sCoeff = x.core.sCoeff := by
    calc
      output.core.sCoeff = routed.core.sCoeff := by
        exact activeBranchBodyStep_core_sCoeff_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = x.core.sCoeff := hroutedS
  have houtputR : output.core.rCoeff =
      wordDouble (tail.succ + 1) x.core.rCoeff := by
    calc
      output.core.rCoeff = routed.core.rCoeff := by
        exact activeBranchBodyStep_core_rCoeff_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = wordDouble (tail.succ + 1) x.core.rCoeff := hroutedR
  have houtputActive : output.core.active = true := by
    calc
      output.core.active = routed.core.active := by
        exact activeBranchBodyStep_core_active_eq_routed tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x
      _ = true := hroutedActive
  have hdouble : 2 * x.core.rCoeff.val < 2 ^ (tail.succ + 1) :=
    arith.vEven_double hactive hvNonzero huOdd hvEven
  have houtputVVal : output.core.v.val = x.core.v.val / 2 := by
    rw [houtputV, wordHalf_val]
  have houtputRVal : output.core.rCoeff.val = 2 * x.core.rCoeff.val := by
    rw [houtputR, wordDouble_val_of_no_overflow _ _ hdouble]
  simp [output, RoundState.fromRegisters, RoundState.applyBranch,
    hactive, houtputU, houtputVVal, houtputRVal, houtputS, houtputActive]

set_option maxHeartbeats 2000000 in
-- The selected odd path combines two restored VBE uses with the routed shift.
/-- The selected compare-true odd route has the exact `uGreater` source
semantics before the reusable route-cleanup suffix. -/
lemma selectedOddDataThenBranchHistoryShift_uGreater_sourceStep
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hvNonzero : x.core.v.val ≠ 0)
    (huOdd : x.core.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.core.v.val.testBit (0 : Nat) = true)
    (hlt : x.core.v.val < x.core.u.val)
    (hcompare : x.core.compare = true)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RoundState.fromRegisters tail.succ counterWidth
        (selectedOddDataThenBranchHistoryShiftStep tail.succ counterWidth
          historyIndex x).core
        (kaliskiSteps + 1) paddingSteps =
      RoundState.applyBranch Branch.uGreater
        (RoundState.fromRegisters tail.succ counterWidth x.core
          kaliskiSteps paddingSteps) := by
  let data := compareSelectedOddDataPathStep tail.succ counterWidth x
  let staged := oddBranchCodeToScratchStep tail.succ counterWidth data
  let written := MK.Compact.activeScratchBToHistoryStep
    tail.succ counterWidth historyIndex staged
  let routed := selectedOddDataThenBranchHistoryShiftStep
    tail.succ counterWidth historyIndex x
  have hcompareBit : (compareBit tail.succ counterWidth).get x = true := by
    simpa only [compareBit_get] using hcompare
  have hscratchABit :
      (scratchABit tail.succ counterWidth).get x = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBBit :
      (scratchBBit tail.succ counterWidth).get x = false := by
    simpa only [scratchBBit_get] using hscratchB
  have hpreserve
      (observed : EncodedBit (registerEncoding tail.succ counterWidth))
      (hu : ∀ bit : Fin tail.succ,
        (RegisterBits.uValueBit tail.succ counterWidth bit).wire ≠ observed.wire)
      (hr : ∀ bit : Fin (tail.succ + 1),
        (RegisterBits.rCoeffValueBit tail.succ counterWidth bit).wire ≠
          observed.wire) :
      observed.get data.core = observed.get x.core := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_get_coreBit_of_compare_true
      tail.succ counterWidth observed hu hr x hcompareBit
      hscratchABit hscratchBBit
  have hactiveData : (activeBit tail.succ counterWidth).get data = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get data.core = true
    rw [hpreserve (RegisterBits.activeBit tail.succ counterWidth)
      (fun bit => (RegisterBits.active_u_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit)).symm)
      (fun bit => (RegisterBits.active_rCoeff_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit)).symm)]
    simpa only [RegisterBits.activeBit_get] using hactive
  have hcompareData : (compareBit tail.succ counterWidth).get data = true := by
    change (RegisterBits.compareBit tail.succ counterWidth).get data.core = true
    rw [hpreserve (RegisterBits.compareBit tail.succ counterWidth)
      (fun bit => RegisterBits.u_compare_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => (RegisterBits.compare_rCoeff_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit)).symm)]
    simpa only [RegisterBits.compareBit_get] using hcompare
  have hscratchAData :
      (scratchABit tail.succ counterWidth).get data = false := by
    change (RegisterBits.scratchABit tail.succ counterWidth).get data.core = false
    rw [hpreserve (RegisterBits.scratchABit tail.succ counterWidth)
      (fun bit => RegisterBits.u_scratchA_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.rCoeff_scratchA_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))]
    simpa only [RegisterBits.scratchABit_get] using hscratchA
  have hroute : routed = uDiv2ThenSMul2Step
      tail.succ counterWidth written := by
    dsimp [routed, written, staged, data,
      selectedOddDataThenBranchHistoryShiftStep]
    exact oddBranchCodeThenHistoryThenShiftStep_eq_uShift
      tail.succ counterWidth historyIndex
      (compareSelectedOddDataPathStep tail.succ counterWidth x)
      hactiveData hcompareData hscratchAData
  have hdataU : data.core.u = x.core.u - x.core.v := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_core_u_of_compare_true_cleanWork
      tail.succ counterWidth x hcompareBit hscratchABit hscratchBBit hwork
  have hdataV : data.core.v = x.core.v := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_core_v_of_compare_true
      tail.succ counterWidth x hcompareBit hscratchABit hscratchBBit
  have hdataR : data.core.rCoeff = x.core.rCoeff + x.core.sCoeff := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_core_rCoeff_of_compare_true_cleanWork
      tail.succ counterWidth x hcompareBit hscratchABit hscratchBBit
      hcarry hwork
  have hdataS : data.core.sCoeff = x.core.sCoeff := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_core_sCoeff_of_compare_true
      tail.succ counterWidth x hcompareBit hscratchABit hscratchBBit
  have hstagedU : staged.core.u = data.core.u := by
    dsimp [staged]
    exact oddBranchCodeToScratchStep_core_u tail.succ counterWidth data
  have hstagedV : staged.core.v = data.core.v := by
    dsimp [staged]
    exact oddBranchCodeToScratchStep_core_v tail.succ counterWidth data
  have hstagedR : staged.core.rCoeff = data.core.rCoeff := by
    dsimp [staged]
    exact oddBranchCodeToScratchStep_core_rCoeff tail.succ counterWidth data
  have hstagedS : staged.core.sCoeff = data.core.sCoeff := by
    dsimp [staged]
    exact oddBranchCodeToScratchStep_core_sCoeff tail.succ counterWidth data
  have hwrittenU : written.core.u = x.core.u - x.core.v := by
    dsimp [written]
    rw [MK.Compact.activeScratchBToHistoryStep_core_u, hstagedU, hdataU]
  have hwrittenV : written.core.v = x.core.v := by
    dsimp [written]
    rw [MK.Compact.activeScratchBToHistoryStep_core_v, hstagedV, hdataV]
  have hwrittenR : written.core.rCoeff = x.core.rCoeff + x.core.sCoeff := by
    dsimp [written]
    rw [MK.Compact.activeScratchBToHistoryStep_core_rCoeff, hstagedR, hdataR]
  have hwrittenS : written.core.sCoeff = x.core.sCoeff := by
    dsimp [written]
    rw [MK.Compact.activeScratchBToHistoryStep_core_sCoeff, hstagedS, hdataS]
  have hlsbWritten :
      written.core.u.val.testBit (0 : Nat) = false := by
    rw [hwrittenU]
    exact arith.uGreater_lsb hactive hvNonzero huOdd hvOdd hlt
  have hmsbWritten :
      written.core.sCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenS]
    exact arith.uGreater_msb hactive hvNonzero huOdd hvOdd hlt
  have hroutedU : routed.core.u =
      wordHalf tail.succ (x.core.u - x.core.v) := by
    rw [hroute,
      uDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
        tail counterWidth written hlsbWritten,
      hwrittenU]
  have hroutedV : routed.core.v = x.core.v := by
    rw [hroute, uDiv2ThenSMul2Step_core_v, hwrittenV]
  have hroutedR : routed.core.rCoeff = x.core.rCoeff + x.core.sCoeff := by
    rw [hroute, uDiv2ThenSMul2Step_core_rCoeff, hwrittenR]
  have hroutedS : routed.core.sCoeff =
      wordDouble (tail.succ + 1) x.core.sCoeff := by
    rw [hroute,
      uDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
        tail.succ counterWidth written hmsbWritten,
      hwrittenS]
  have hroutedActive : routed.core.active = true := by
    change (activeBit tail.succ counterWidth).get routed = true
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_active, hactiveData]
  have hsubVal : (x.core.u - x.core.v).val =
      x.core.u.val - x.core.v.val := by
    exact Fin.sub_val_of_le (Nat.le_of_lt hlt)
  have hadd := arith.uGreater_add hactive hvNonzero huOdd hvOdd hlt
  have haddVal : (x.core.rCoeff + x.core.sCoeff).val =
      x.core.rCoeff.val + x.core.sCoeff.val :=
    Fin.val_add_eq_of_add_lt hadd
  have hdouble := arith.uGreater_double hactive hvNonzero huOdd hvOdd hlt
  have hroutedUVal : routed.core.u.val =
      (x.core.u.val - x.core.v.val) / 2 := by
    rw [hroutedU, wordHalf_val, hsubVal]
  have hroutedRVal : routed.core.rCoeff.val =
      x.core.rCoeff.val + x.core.sCoeff.val := by
    rw [hroutedR, haddVal]
  have hroutedSVal : routed.core.sCoeff.val = 2 * x.core.sCoeff.val := by
    rw [hroutedS, wordDouble_val_of_no_overflow _ _ hdouble]
  change RoundState.fromRegisters tail.succ counterWidth routed.core
      (kaliskiSteps + 1) paddingSteps = _
  simp [RoundState.fromRegisters, RoundState.applyBranch, hactive,
    hroutedUVal, hroutedV, hroutedRVal, hroutedSVal, hroutedActive]

set_option maxHeartbeats 2000000 in
-- The selected odd path combines two restored VBE uses with the routed shift.
/-- The selected compare-false odd route has the exact `vLe` source semantics
before the reusable route-cleanup suffix. -/
lemma selectedOddDataThenBranchHistoryShift_vLe_sourceStep
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hvNonzero : x.core.v.val ≠ 0)
    (huOdd : x.core.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.core.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.core.v.val < x.core.u.val)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RoundState.fromRegisters tail.succ counterWidth
        (selectedOddDataThenBranchHistoryShiftStep tail.succ counterWidth
          historyIndex x).core
        (kaliskiSteps + 1) paddingSteps =
      RoundState.applyBranch Branch.vLe
        (RoundState.fromRegisters tail.succ counterWidth x.core
          kaliskiSteps paddingSteps) := by
  let data := compareSelectedOddDataPathStep tail.succ counterWidth x
  let staged := oddBranchCodeToScratchStep tail.succ counterWidth data
  let written := MK.Compact.activeScratchBToHistoryStep
    tail.succ counterWidth historyIndex staged
  let routed := selectedOddDataThenBranchHistoryShiftStep
    tail.succ counterWidth historyIndex x
  have hcompareBit : (compareBit tail.succ counterWidth).get x = false := by
    simpa only [compareBit_get] using hcompare
  have hscratchABit :
      (scratchABit tail.succ counterWidth).get x = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBBit :
      (scratchBBit tail.succ counterWidth).get x = false := by
    simpa only [scratchBBit_get] using hscratchB
  have hpreserve
      (observed : EncodedBit (registerEncoding tail.succ counterWidth))
      (hv : ∀ bit : Fin tail.succ,
        (RegisterBits.vValueBit tail.succ counterWidth bit).wire ≠ observed.wire)
      (hs : ∀ bit : Fin (tail.succ + 1),
        (RegisterBits.sCoeffValueBit tail.succ counterWidth bit).wire ≠
          observed.wire) :
      observed.get data.core = observed.get x.core := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_get_coreBit_of_compare_false
      tail.succ counterWidth observed hv hs x hcompareBit
      hscratchABit hscratchBBit
  have hactiveData : (activeBit tail.succ counterWidth).get data = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get data.core = true
    rw [hpreserve (RegisterBits.activeBit tail.succ counterWidth)
      (fun bit => (RegisterBits.active_v_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit)).symm)
      (fun bit => (RegisterBits.active_sCoeff_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit)).symm)]
    simpa only [RegisterBits.activeBit_get] using hactive
  have hcompareData : (compareBit tail.succ counterWidth).get data = false := by
    change (RegisterBits.compareBit tail.succ counterWidth).get data.core = false
    rw [hpreserve (RegisterBits.compareBit tail.succ counterWidth)
      (fun bit => RegisterBits.v_compare_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => (RegisterBits.compare_sCoeff_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit)).symm)]
    simpa only [RegisterBits.compareBit_get] using hcompare
  have hscratchAData :
      (scratchABit tail.succ counterWidth).get data = false := by
    change (RegisterBits.scratchABit tail.succ counterWidth).get data.core = false
    rw [hpreserve (RegisterBits.scratchABit tail.succ counterWidth)
      (fun bit => RegisterBits.v_scratchA_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.sCoeff_scratchA_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))]
    simpa only [RegisterBits.scratchABit_get] using hscratchA
  have hroute : routed = vDiv2ThenRMul2Step
      tail.succ counterWidth written := by
    dsimp [routed, written, staged, data,
      selectedOddDataThenBranchHistoryShiftStep]
    exact oddBranchCodeThenHistoryThenShiftStep_eq_vShift
      tail.succ counterWidth historyIndex
      (compareSelectedOddDataPathStep tail.succ counterWidth x)
      hactiveData hcompareData hscratchAData
  have hdataU : data.core.u = x.core.u := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_core_u_of_compare_false
      tail.succ counterWidth x hcompareBit hscratchABit hscratchBBit
  have hdataV : data.core.v = x.core.v - x.core.u := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_core_v_of_compare_false_cleanWork
      tail.succ counterWidth x hcompareBit hscratchABit hscratchBBit hwork
  have hdataR : data.core.rCoeff = x.core.rCoeff := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_core_rCoeff_of_compare_false
      tail.succ counterWidth x hcompareBit hscratchABit hscratchBBit
  have hdataS : data.core.sCoeff = x.core.sCoeff + x.core.rCoeff := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_core_sCoeff_of_compare_false_cleanWork
      tail.succ counterWidth x hcompareBit hscratchABit hscratchBBit
      hcarry hwork
  have hstagedU : staged.core.u = data.core.u := by
    dsimp [staged]
    exact oddBranchCodeToScratchStep_core_u tail.succ counterWidth data
  have hstagedV : staged.core.v = data.core.v := by
    dsimp [staged]
    exact oddBranchCodeToScratchStep_core_v tail.succ counterWidth data
  have hstagedR : staged.core.rCoeff = data.core.rCoeff := by
    dsimp [staged]
    exact oddBranchCodeToScratchStep_core_rCoeff tail.succ counterWidth data
  have hstagedS : staged.core.sCoeff = data.core.sCoeff := by
    dsimp [staged]
    exact oddBranchCodeToScratchStep_core_sCoeff tail.succ counterWidth data
  have hwrittenU : written.core.u = x.core.u := by
    dsimp [written]
    rw [MK.Compact.activeScratchBToHistoryStep_core_u, hstagedU, hdataU]
  have hwrittenV : written.core.v = x.core.v - x.core.u := by
    dsimp [written]
    rw [MK.Compact.activeScratchBToHistoryStep_core_v, hstagedV, hdataV]
  have hwrittenR : written.core.rCoeff = x.core.rCoeff := by
    dsimp [written]
    rw [MK.Compact.activeScratchBToHistoryStep_core_rCoeff, hstagedR, hdataR]
  have hwrittenS : written.core.sCoeff = x.core.sCoeff + x.core.rCoeff := by
    dsimp [written]
    rw [MK.Compact.activeScratchBToHistoryStep_core_sCoeff, hstagedS, hdataS]
  have hlsbWritten :
      written.core.v.val.testBit (0 : Nat) = false := by
    rw [hwrittenV]
    exact arith.vLe_lsb hactive hvNonzero huOdd hvOdd hnlt
  have hmsbWritten :
      written.core.rCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenR]
    exact arith.vLe_msb hactive hvNonzero huOdd hvOdd hnlt
  have hroutedU : routed.core.u = x.core.u := by
    rw [hroute, vDiv2ThenRMul2Step_core_u, hwrittenU]
  have hroutedV : routed.core.v =
      wordHalf tail.succ (x.core.v - x.core.u) := by
    rw [hroute,
      vDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
        tail counterWidth written hlsbWritten,
      hwrittenV]
  have hroutedR : routed.core.rCoeff =
      wordDouble (tail.succ + 1) x.core.rCoeff := by
    rw [hroute,
      vDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
        tail.succ counterWidth written hmsbWritten,
      hwrittenR]
  have hroutedS : routed.core.sCoeff = x.core.sCoeff + x.core.rCoeff := by
    rw [hroute, vDiv2ThenRMul2Step_core_sCoeff, hwrittenS]
  have hroutedActive : routed.core.active = true := by
    change (activeBit tail.succ counterWidth).get routed = true
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_active, hactiveData]
  have hsubVal : (x.core.v - x.core.u).val =
      x.core.v.val - x.core.u.val := by
    exact Fin.sub_val_of_le (Nat.le_of_not_gt hnlt)
  have hadd := arith.vLe_add hactive hvNonzero huOdd hvOdd hnlt
  have haddVal : (x.core.sCoeff + x.core.rCoeff).val =
      x.core.sCoeff.val + x.core.rCoeff.val :=
    Fin.val_add_eq_of_add_lt hadd
  have hdouble := arith.vLe_double hactive hvNonzero huOdd hvOdd hnlt
  have hroutedVVal : routed.core.v.val =
      (x.core.v.val - x.core.u.val) / 2 := by
    rw [hroutedV, wordHalf_val, hsubVal]
  have hroutedRVal : routed.core.rCoeff.val = 2 * x.core.rCoeff.val := by
    rw [hroutedR, wordDouble_val_of_no_overflow _ _ hdouble]
  have hroutedSVal : routed.core.sCoeff.val =
      x.core.sCoeff.val + x.core.rCoeff.val := by
    rw [hroutedS, haddVal]
  change RoundState.fromRegisters tail.succ counterWidth routed.core
      (kaliskiSteps + 1) paddingSteps = _
  simp [RoundState.fromRegisters, RoundState.applyBranch, hactive,
    hroutedU, hroutedVVal, hroutedRVal, hroutedSVal, hroutedActive,
    Nat.add_comm]

private lemma arithmeticCertificate_setCompare
    (tail counterWidth : Nat)
    (core : MK.Registers tail.succ counterWidth) (compare : Bool)
    (arith : ModeControlledSemanticStepArithmeticCertificate
      tail counterWidth core) :
    ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      { core with compare := compare } where
  uEven_msb := by simpa using arith.uEven_msb
  uEven_double := by simpa using arith.uEven_double
  vEven_msb := by simpa using arith.vEven_msb
  vEven_double := by simpa using arith.vEven_double
  uGreater_lsb := by simpa using arith.uGreater_lsb
  uGreater_add := by simpa using arith.uGreater_add
  uGreater_msb := by simpa using arith.uGreater_msb
  uGreater_double := by simpa using arith.uGreater_double
  vLe_lsb := by simpa using arith.vLe_lsb
  vLe_add := by simpa using arith.vLe_add
  vLe_msb := by simpa using arith.vLe_msb
  vLe_double := by simpa using arith.vLe_double

set_option maxHeartbeats 2000000 in
-- Selector normalization and five cleanup projections cross the literal body.
/-- On the active odd `uGreater` branch, the complete compact body has exactly
the source-level Montgomery--Kaliski data semantics. -/
lemma activeBranchBody_uGreater_sourceStep
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hvNonzero : x.core.v.val ≠ 0)
    (huOdd : x.core.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.core.v.val.testBit (0 : Nat) = true)
    (hlt : x.core.v.val < x.core.u.val)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RoundState.fromRegisters tail.succ counterWidth
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x).core
        (kaliskiSteps + 1) paddingSteps =
      RoundState.applyBranch Branch.uGreater
        (RoundState.fromRegisters tail.succ counterWidth x.core
          kaliskiSteps paddingSteps) := by
  let selected := activeOddUGreaterSelectorStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit x
  let routed := activeBranchRoutedStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  let output := activeBranchBodyStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have hactiveBit : (activeBit tail.succ counterWidth).get x = true := by
    simpa only [activeBit_get] using hactive
  have hcompareBit : (compareBit tail.succ counterWidth).get x = false := by
    simpa only [compareBit_get] using hcompare
  have hscratchABit :
      (scratchABit tail.succ counterWidth).get x = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBBit :
      (scratchBBit tail.succ counterWidth).get x = false := by
    simpa only [scratchBBit_get] using hscratchB
  have huLow :
      (uLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = true := by
    simpa [uLowBit] using huOdd
  have hvLow :
      (vLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = true := by
    simpa [vLowBit] using hvOdd
  have endpoint := activeOddUGreaterSelectorStep_cleanEndpoint
    tail.succ counterWidth (0 : Fin tail.succ) finalBit x hpath hcontrol
    hcompareBit hscratchABit hscratchBBit hcarry hwork hfinal
  have hselectedPath : (pathBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    have huValue : ((uValueWord tail.succ counterWidth).bit
        (0 : Fin tail.succ)).get x = true := by
      simpa only [uLowBit] using huLow
    have hvValue : ((vValueWord tail.succ counterWidth).bit
        (0 : Fin tail.succ)).get x = true := by
      simpa only [vLowBit] using hvLow
    rw [endpoint.path, hactiveBit, huValue, hvValue]
    rfl
  have hselectedCompareBit :
      (compareBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    have huValue : ((uValueWord tail.succ counterWidth).bit
        (0 : Fin tail.succ)).get x = true := by
      simpa only [uLowBit] using huLow
    have hvValue : ((vValueWord tail.succ counterWidth).bit
        (0 : Fin tail.succ)).get x = true := by
      simpa only [vLowBit] using hvLow
    rw [endpoint.compare, hactiveBit, huValue, hvValue]
    simp [hlt]
  have hcoreEq : selected.core =
      { x.core with compare := selected.core.compare } := by
    dsimp [selected]
    exact activeOddUGreaterSelectorStep_core_eq_setCompare
      tail.succ counterWidth (0 : Fin tail.succ) finalBit x hcontrol
  have hselectedActive : selected.core.active = true := by
    rw [hcoreEq]
    exact hactive
  have hselectedVNonzero : selected.core.v.val ≠ 0 := by
    rw [hcoreEq]
    exact hvNonzero
  have hselectedUOdd : selected.core.u.val.testBit (0 : Nat) = true := by
    rw [hcoreEq]
    exact huOdd
  have hselectedVOdd : selected.core.v.val.testBit (0 : Nat) = true := by
    rw [hcoreEq]
    exact hvOdd
  have hselectedLt : selected.core.v.val < selected.core.u.val := by
    rw [hcoreEq]
    exact hlt
  have hselectedCompare : selected.core.compare = true := by
    simpa only [compareBit_get] using hselectedCompareBit
  have hselectedScratchA : selected.core.scratchA = false := by
    simpa only [scratchABit_get] using endpoint.scratchA
  have hselectedScratchB : selected.core.scratchB = false := by
    simpa only [scratchBBit_get] using endpoint.scratchB
  have hselectedArith :
      ModeControlledSemanticStepArithmeticCertificate tail counterWidth
        selected.core := by
    rw [hcoreEq]
    exact arithmeticCertificate_setCompare
      tail counterWidth x.core selected.core.compare arith
  have huSelected :
      (uLowBit tail.succ counterWidth (0 : Fin tail.succ)).get selected = true := by
    simpa [uLowBit] using hselectedUOdd
  have hvSelected :
      (vLowBit tail.succ counterWidth (0 : Fin tail.succ)).get selected = true := by
    simpa [vLowBit] using hselectedVOdd
  have hroute : routed = selectedOddDataThenBranchHistoryShiftStep
      tail.succ counterWidth historyIndex selected := by
    dsimp [routed, selected]
    exact activeBranchRoutedStep_eq_selected_odd_route
      tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
      historyIndex x huSelected hvSelected hselectedPath endpoint.control
      endpoint.scratchA endpoint.scratchB (endpoint.carryWork tempIndex)
  have hselectedSource :
      RoundState.fromRegisters tail.succ counterWidth selected.core
          kaliskiSteps paddingSteps =
        RoundState.fromRegisters tail.succ counterWidth x.core
          kaliskiSteps paddingSteps := by
    rw [hcoreEq]
    rfl
  have hroutedSource :
      RoundState.fromRegisters tail.succ counterWidth routed.core
          (kaliskiSteps + 1) paddingSteps =
        RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth x.core
            kaliskiSteps paddingSteps) := by
    rw [hroute]
    calc
      _ = RoundState.applyBranch Branch.uGreater
          (RoundState.fromRegisters tail.succ counterWidth selected.core
            kaliskiSteps paddingSteps) :=
        selectedOddDataThenBranchHistoryShift_uGreater_sourceStep
          tail counterWidth kaliskiSteps paddingSteps historyIndex selected
          hselectedActive hselectedVNonzero hselectedUOdd hselectedVOdd
          hselectedLt hselectedCompare hselectedScratchA hselectedScratchB
          endpoint.carryIn endpoint.carryWork hselectedArith
      _ = _ := by rw [hselectedSource]
  have houtputU : output.core.u = routed.core.u :=
    activeBranchBodyStep_core_u_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputV : output.core.v = routed.core.v :=
    activeBranchBodyStep_core_v_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputR : output.core.rCoeff = routed.core.rCoeff :=
    activeBranchBodyStep_core_rCoeff_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputS : output.core.sCoeff = routed.core.sCoeff :=
    activeBranchBodyStep_core_sCoeff_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputActive : output.core.active = routed.core.active :=
    activeBranchBodyStep_core_active_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputSource :
      RoundState.fromRegisters tail.succ counterWidth output.core
          (kaliskiSteps + 1) paddingSteps =
        RoundState.fromRegisters tail.succ counterWidth routed.core
          (kaliskiSteps + 1) paddingSteps := by
    simp [RoundState.fromRegisters, houtputU, houtputV, houtputR,
      houtputS, houtputActive]
  change RoundState.fromRegisters tail.succ counterWidth output.core
      (kaliskiSteps + 1) paddingSteps = _
  exact houtputSource.trans hroutedSource

set_option maxHeartbeats 2000000 in
-- Selector normalization and five cleanup projections cross the literal body.
/-- On the active odd `vLe` branch, the complete compact body has exactly the
source-level Montgomery--Kaliski data semantics. -/
lemma activeBranchBody_vLe_sourceStep
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hvNonzero : x.core.v.val ≠ 0)
    (huOdd : x.core.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.core.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.core.v.val < x.core.u.val)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RoundState.fromRegisters tail.succ counterWidth
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x).core
        (kaliskiSteps + 1) paddingSteps =
      RoundState.applyBranch Branch.vLe
        (RoundState.fromRegisters tail.succ counterWidth x.core
          kaliskiSteps paddingSteps) := by
  let selected := activeOddUGreaterSelectorStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit x
  let routed := activeBranchRoutedStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  let output := activeBranchBodyStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have hactiveBit : (activeBit tail.succ counterWidth).get x = true := by
    simpa only [activeBit_get] using hactive
  have hcompareBit : (compareBit tail.succ counterWidth).get x = false := by
    simpa only [compareBit_get] using hcompare
  have hscratchABit :
      (scratchABit tail.succ counterWidth).get x = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBBit :
      (scratchBBit tail.succ counterWidth).get x = false := by
    simpa only [scratchBBit_get] using hscratchB
  have huLow :
      (uLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = true := by
    simpa [uLowBit] using huOdd
  have hvLow :
      (vLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = true := by
    simpa [vLowBit] using hvOdd
  have endpoint := activeOddUGreaterSelectorStep_cleanEndpoint
    tail.succ counterWidth (0 : Fin tail.succ) finalBit x hpath hcontrol
    hcompareBit hscratchABit hscratchBBit hcarry hwork hfinal
  have hselectedPath : (pathBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    have huValue : ((uValueWord tail.succ counterWidth).bit
        (0 : Fin tail.succ)).get x = true := by
      simpa only [uLowBit] using huLow
    have hvValue : ((vValueWord tail.succ counterWidth).bit
        (0 : Fin tail.succ)).get x = true := by
      simpa only [vLowBit] using hvLow
    rw [endpoint.path, hactiveBit, huValue, hvValue]
    rfl
  have hselectedCompareBit :
      (compareBit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    have huValue : ((uValueWord tail.succ counterWidth).bit
        (0 : Fin tail.succ)).get x = true := by
      simpa only [uLowBit] using huLow
    have hvValue : ((vValueWord tail.succ counterWidth).bit
        (0 : Fin tail.succ)).get x = true := by
      simpa only [vLowBit] using hvLow
    rw [endpoint.compare, hactiveBit, huValue, hvValue]
    simp [hnlt]
  have hcoreEq : selected.core =
      { x.core with compare := selected.core.compare } := by
    dsimp [selected]
    exact activeOddUGreaterSelectorStep_core_eq_setCompare
      tail.succ counterWidth (0 : Fin tail.succ) finalBit x hcontrol
  have hselectedActive : selected.core.active = true := by
    rw [hcoreEq]
    exact hactive
  have hselectedVNonzero : selected.core.v.val ≠ 0 := by
    rw [hcoreEq]
    exact hvNonzero
  have hselectedUOdd : selected.core.u.val.testBit (0 : Nat) = true := by
    rw [hcoreEq]
    exact huOdd
  have hselectedVOdd : selected.core.v.val.testBit (0 : Nat) = true := by
    rw [hcoreEq]
    exact hvOdd
  have hselectedNlt : ¬ selected.core.v.val < selected.core.u.val := by
    rw [hcoreEq]
    exact hnlt
  have hselectedCompare : selected.core.compare = false := by
    simpa only [compareBit_get] using hselectedCompareBit
  have hselectedScratchA : selected.core.scratchA = false := by
    simpa only [scratchABit_get] using endpoint.scratchA
  have hselectedScratchB : selected.core.scratchB = false := by
    simpa only [scratchBBit_get] using endpoint.scratchB
  have hselectedArith :
      ModeControlledSemanticStepArithmeticCertificate tail counterWidth
        selected.core := by
    rw [hcoreEq]
    exact arithmeticCertificate_setCompare
      tail counterWidth x.core selected.core.compare arith
  have huSelected :
      (uLowBit tail.succ counterWidth (0 : Fin tail.succ)).get selected = true := by
    simpa [uLowBit] using hselectedUOdd
  have hvSelected :
      (vLowBit tail.succ counterWidth (0 : Fin tail.succ)).get selected = true := by
    simpa [vLowBit] using hselectedVOdd
  have hroute : routed = selectedOddDataThenBranchHistoryShiftStep
      tail.succ counterWidth historyIndex selected := by
    dsimp [routed, selected]
    exact activeBranchRoutedStep_eq_selected_odd_route
      tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
      historyIndex x huSelected hvSelected hselectedPath endpoint.control
      endpoint.scratchA endpoint.scratchB (endpoint.carryWork tempIndex)
  have hselectedSource :
      RoundState.fromRegisters tail.succ counterWidth selected.core
          kaliskiSteps paddingSteps =
        RoundState.fromRegisters tail.succ counterWidth x.core
          kaliskiSteps paddingSteps := by
    rw [hcoreEq]
    rfl
  have hroutedSource :
      RoundState.fromRegisters tail.succ counterWidth routed.core
          (kaliskiSteps + 1) paddingSteps =
        RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth x.core
            kaliskiSteps paddingSteps) := by
    rw [hroute]
    calc
      _ = RoundState.applyBranch Branch.vLe
          (RoundState.fromRegisters tail.succ counterWidth selected.core
            kaliskiSteps paddingSteps) :=
        selectedOddDataThenBranchHistoryShift_vLe_sourceStep
          tail counterWidth kaliskiSteps paddingSteps historyIndex selected
          hselectedActive hselectedVNonzero hselectedUOdd hselectedVOdd
          hselectedNlt hselectedCompare hselectedScratchA hselectedScratchB
          endpoint.carryIn endpoint.carryWork hselectedArith
      _ = _ := by rw [hselectedSource]
  have houtputU : output.core.u = routed.core.u :=
    activeBranchBodyStep_core_u_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputV : output.core.v = routed.core.v :=
    activeBranchBodyStep_core_v_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputR : output.core.rCoeff = routed.core.rCoeff :=
    activeBranchBodyStep_core_rCoeff_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputS : output.core.sCoeff = routed.core.sCoeff :=
    activeBranchBodyStep_core_sCoeff_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputActive : output.core.active = routed.core.active :=
    activeBranchBodyStep_core_active_eq_routed tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x
  have houtputSource :
      RoundState.fromRegisters tail.succ counterWidth output.core
          (kaliskiSteps + 1) paddingSteps =
        RoundState.fromRegisters tail.succ counterWidth routed.core
          (kaliskiSteps + 1) paddingSteps := by
    simp [RoundState.fromRegisters, houtputU, houtputV, houtputR,
      houtputS, houtputActive]
  change RoundState.fromRegisters tail.succ counterWidth output.core
      (kaliskiSteps + 1) paddingSteps = _
  exact houtputSource.trans hroutedSource

set_option maxHeartbeats 2000000 in
-- This symbolic split reuses the four branch proofs without enumerating words.
/-- The complete compact active body implements one source Montgomery--Kaliski
round.  The proof classifies only the two low bits and the strict comparison. -/
lemma activeBranchBody_sourceRound
    (tail counterWidth kaliskiSteps paddingSteps : Nat)
    (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hvNonzero : x.core.v.val ≠ 0)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RoundState.fromRegisters tail.succ counterWidth
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x).core
        (kaliskiSteps + 1) paddingSteps =
      RoundState.round
        (RoundState.fromRegisters tail.succ counterWidth x.core
          kaliskiSteps paddingSteps) := by
  let source := RoundState.fromRegisters tail.succ counterWidth x.core
    kaliskiSteps paddingSteps
  have hsourceActive : source.active = true := by
    simpa [source, RoundState.fromRegisters] using hactive
  have hsourceV : source.v ≠ 0 := by
    simpa [source, RoundState.fromRegisters] using hvNonzero
  cases hu : x.core.u.val.testBit (0 : Nat) with
  | false =>
      have huMod : source.u % 2 = 0 := by
        dsimp [source, RoundState.fromRegisters]
        exact Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false
          x.core.u.val hu
      have hbody := activeBranchBody_uEven_sourceStep tail counterWidth
        kaliskiSteps paddingSteps finalBit tempIndex historyIndex x hactive
        hpath hcontrol hvNonzero hcompare hscratchA hscratchB hwork hu arith
      exact hbody.trans
        (RoundState.round_active_nonzero_uEven
          source hsourceActive hsourceV huMod).symm
  | true =>
      have huMod : source.u % 2 ≠ 0 := by
        dsimp [source, RoundState.fromRegisters]
        exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true
          x.core.u.val hu
      cases hv : x.core.v.val.testBit (0 : Nat) with
      | false =>
          have hvMod : source.v % 2 = 0 := by
            dsimp [source, RoundState.fromRegisters]
            exact Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false
              x.core.v.val hv
          have hbody := activeBranchBody_vEven_sourceStep tail counterWidth
            kaliskiSteps paddingSteps finalBit tempIndex historyIndex x hactive
            hpath hcontrol hvNonzero hcompare hscratchA hscratchB hwork hu hv
            arith
          exact hbody.trans
            (RoundState.round_active_nonzero_vEven
              source hsourceActive hsourceV huMod hvMod).symm
      | true =>
          have hvMod : source.v % 2 ≠ 0 := by
            dsimp [source, RoundState.fromRegisters]
            exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true
              x.core.v.val hv
          by_cases hlt : x.core.v.val < x.core.u.val
          · have hbody := activeBranchBody_uGreater_sourceStep tail counterWidth
              kaliskiSteps paddingSteps finalBit tempIndex historyIndex x
              hactive hpath hcontrol hvNonzero hu hv hlt hcompare hscratchA
              hscratchB hcarry hwork hfinal arith
            have hsourceLt : source.v < source.u := by
              simpa [source, RoundState.fromRegisters] using hlt
            exact hbody.trans
              (RoundState.round_active_nonzero_uGreater source hsourceActive
                hsourceV huMod hvMod hsourceLt).symm
          · have hbody := activeBranchBody_vLe_sourceStep tail counterWidth
              kaliskiSteps paddingSteps finalBit tempIndex historyIndex x
              hactive hpath hcontrol hvNonzero hu hv hlt hcompare hscratchA
              hscratchB hcarry hwork hfinal arith
            have hsourceNlt : ¬ source.v < source.u := by
              simpa [source, RoundState.fromRegisters] using hlt
            exact hbody.trans
              (RoundState.round_active_nonzero_vLe source hsourceActive
                hsourceV huMod hvMod hsourceNlt).symm
end CompactCertificate
end
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end
