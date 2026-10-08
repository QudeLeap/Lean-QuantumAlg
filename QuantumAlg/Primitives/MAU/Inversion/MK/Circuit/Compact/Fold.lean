/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Semantics
import all QuantumAlg.Primitives.MAU.Inversion.MK.Termination
import all QuantumAlg.Util.NumberTheory.Binary.GCD.Termination

/-!
# Compact fixed-round inversion circuit and fold
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

/-! ## Source parity needed by physical auxiliary-code cleanup -/

/-- For an odd modulus, the `r` coefficient produced by the selected active
branch has parity equal to the redundant auxiliary branch-code bit.  This is
the source invariant used by the final physical cleanup Toffoli. -/
theorem sourceApplyBranch_rCoeff_mod_two_eq_auxBit
    (p : Nat) (st : RoundState)
    (hpOdd : p % 2 = 1)
    (hinv : RoundState.BezoutInvariant p st) :
    (RoundState.applyBranch (RoundState.selectBranch st) st).rCoeff % 2 =
      if (RoundState.selectBranch st).auxBit then 1 else 0 := by
  have hbezout :
      st.rCoeff * st.v + st.sCoeff * st.u = p := by
    simpa [RoundState.BezoutInvariant, RoundState.bezoutValue] using hinv
  have hbezoutOdd :
      Odd (st.rCoeff * st.v + st.sCoeff * st.u) := by
    rw [hbezout]
    exact Nat.odd_iff.mpr hpOdd
  by_cases hu : st.u % 2 = 0
  · rw [RoundState.selectBranch_uEven_of_even st hu]
    have hrvOdd : Odd (st.rCoeff * st.v) :=
      (Nat.odd_add.mp hbezoutOdd).mpr
        ((Nat.even_iff.mpr hu).mul_left st.sCoeff)
    have hrOdd : Odd st.rCoeff := (Nat.odd_mul.mp hrvOdd).1
    change st.rCoeff % 2 = 1
    exact Nat.odd_iff.mp hrOdd
  · by_cases hv : st.v % 2 = 0
    · rw [RoundState.selectBranch_vEven_of_u_odd_v_even st hu hv]
      simp [RoundState.applyBranch, Branch.auxBit]
    · have huMod : st.u % 2 = 1 := Nat.mod_two_ne_zero.mp hu
      have hvMod : st.v % 2 = 1 := Nat.mod_two_ne_zero.mp hv
      by_cases hlt : st.v < st.u
      · rw [RoundState.selectBranch_uGreater_of_odd_odd_lt st hu hv hlt]
        have huOdd : Odd st.u := Nat.odd_iff.mpr huMod
        have hvOdd : Odd st.v := Nat.odd_iff.mpr hvMod
        have hprod :
            Odd (st.rCoeff * st.v) ↔ Even (st.sCoeff * st.u) :=
          Nat.odd_add.mp hbezoutOdd
        have hrsParity : Odd st.rCoeff ↔ Even st.sCoeff := by
          constructor
          · intro hrOdd
            have hsuEven : Even (st.sCoeff * st.u) :=
              hprod.mp (hrOdd.mul hvOdd)
            exact (Nat.even_mul.mp hsuEven).resolve_right
              (Nat.not_even_iff_odd.mpr huOdd)
          · intro hsEven
            exact (Nat.odd_mul.mp
              (hprod.mpr (hsEven.mul_right st.u))).1
        have hrsOdd : Odd (st.rCoeff + st.sCoeff) :=
          Nat.odd_add.mpr hrsParity
        change (st.rCoeff + st.sCoeff) % 2 = 1
        exact Nat.odd_iff.mp hrsOdd
      · rw [RoundState.selectBranch_vLe_of_odd_odd_not_lt st hu hv hlt]
        simp [RoundState.applyBranch, Branch.auxBit]

/-- Bit-level form of `sourceApplyBranch_rCoeff_mod_two_eq_auxBit`. -/
theorem sourceApplyBranch_rCoeff_testBit_zero_eq_auxBit
    (p : Nat) (st : RoundState)
    (hpOdd : p % 2 = 1)
    (hinv : RoundState.BezoutInvariant p st) :
    (RoundState.applyBranch
      (RoundState.selectBranch st) st).rCoeff.testBit 0 =
        (RoundState.selectBranch st).auxBit := by
  rw [Nat.testBit_zero,
    sourceApplyBranch_rCoeff_mod_two_eq_auxBit p st hpOdd hinv]
  cases (RoundState.selectBranch st).auxBit <;> simp

/-! ## Compact-carrier residue bridge -/

namespace CompactCertificate

open MK.Compact

/-- The Bezout invariant forces the unchanged `r` coefficient to be odd on
the `uEven` branch.  This is the mathematical input to the compact physical
cleanup suffix. -/
theorem source_uEven_rCoeff_testBit_zero
    (n counterWidth modulus kaliskiSteps paddingSteps : Nat)
    (x : MK.Compact.Registers n counterWidth)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters n counterWidth x.core
        kaliskiSteps paddingSteps))
    (huEven : x.core.u.val.testBit (0 : Nat) = false) :
    x.core.rCoeff.val.testBit 0 = true := by
  let source := RoundState.fromRegisters n counterWidth x.core
    kaliskiSteps paddingSteps
  have hselect : RoundState.selectBranch source = Branch.uEven := by
    apply RoundState.selectBranch_uEven_of_even
    dsimp [source, RoundState.fromRegisters]
    exact Nat.BinaryArithmetic.mod_two_eq_zero_of_testBit_zero_false
      x.core.u.val huEven
  have hparity := sourceApplyBranch_rCoeff_testBit_zero_eq_auxBit
    modulus source hmodulusOdd hbezout
  rw [hselect] at hparity
  simpa [source, RoundState.fromRegisters, RoundState.applyBranch,
    Branch.auxBit] using hparity

/-- The Bezout invariant forces `r+s` to be odd on the `uGreater` branch. -/
theorem source_uGreater_rCoeff_add_testBit_zero
    (n counterWidth modulus kaliskiSteps paddingSteps : Nat)
    (x : MK.Compact.Registers n counterWidth)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters n counterWidth x.core
        kaliskiSteps paddingSteps))
    (huOdd : x.core.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.core.v.val.testBit (0 : Nat) = true)
    (hlt : x.core.v.val < x.core.u.val) :
    (x.core.rCoeff.val + x.core.sCoeff.val).testBit 0 = true := by
  let source := RoundState.fromRegisters n counterWidth x.core
    kaliskiSteps paddingSteps
  have hselect : RoundState.selectBranch source = Branch.uGreater := by
    apply RoundState.selectBranch_uGreater_of_odd_odd_lt
    · dsimp [source, RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true
        x.core.u.val huOdd
    · dsimp [source, RoundState.fromRegisters]
      exact Nat.BinaryArithmetic.mod_two_ne_zero_of_testBit_zero_true
        x.core.v.val hvOdd
    · simpa [source, RoundState.fromRegisters] using hlt
  have hparity := sourceApplyBranch_rCoeff_testBit_zero_eq_auxBit
    modulus source hmodulusOdd hbezout
  rw [hselect] at hparity
  simpa [source, RoundState.fromRegisters, RoundState.applyBranch,
    Branch.auxBit] using hparity

/-- The literal compact even-route gates reach the exact `uEven` residue
certificate consumed by the three-gate cleanup suffix. -/
theorem selected_uEven_residueCertificate
    (tail counterWidth modulus kaliskiSteps paddingSteps : Nat)
    (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hhistory :
      x.core.history.val.testBit (WireAddress.bitIndex historyIndex).val = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (huEven : x.core.u.val.testBit (0 : Nat) = false)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters tail.succ counterWidth x.core
        kaliskiSteps paddingSteps)) :
    BranchResidueCertificate tail.succ counterWidth historyIndex
      (selectedBranchCodeThenHistoryThenShiftStep tail.succ counterWidth
        (0 : Fin tail.succ) tempIndex historyIndex x) := by
  let routed := selectedBranchCodeThenHistoryThenShiftStep
    tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
  let staged := selectedBranchCodeToScratchStep
    tail.succ counterWidth (0 : Fin tail.succ) tempIndex x
  let written := MK.Compact.activeScratchBToHistoryStep
    tail.succ counterWidth historyIndex staged
  have hactiveBit : (activeBit tail.succ counterWidth).get x = true := by
    simpa only [activeBit_get] using hactive
  have hcompareBit : (compareBit tail.succ counterWidth).get x = false := by
    simpa only [compareBit_get] using hcompare
  have hscratchABit : (scratchABit tail.succ counterWidth).get x = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBBit : (scratchBBit tail.succ counterWidth).get x = false := by
    simpa only [scratchBBit_get] using hscratchB
  have hhistoryBit :
      (historyBit tail.succ counterWidth historyIndex).get x = false := by
    simpa only [historyBit_get] using hhistory
  have huLow :
      (uLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = false := by
    simpa [uLowBit] using huEven
  have hroute : routed = uDiv2ThenSMul2Step tail.succ counterWidth written := by
    exact selectedBranchCodeThenHistoryThenShiftStep_eq_uShift_of_uEven
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hactiveBit huLow hscratchABit hscratchBBit (hwork tempIndex)
  have hactiveOut : (activeBit tail.succ counterWidth).get routed = true := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_active, hactiveBit]
  have hcompareOut : (compareBit tail.succ counterWidth).get routed = false := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_compare, hcompareBit]
  have hscratchAOut :
      (scratchABit tail.succ counterWidth).get routed = true := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_scratchA_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hactiveBit, huLow]
    rfl
  have hscratchBOut :
      (scratchBBit tail.succ counterWidth).get routed = false := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_scratchB_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hactiveBit, huLow]
    rfl
  have hhistoryOut :
      (historyBit tail.succ counterWidth historyIndex).get routed = false := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_history_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hhistoryBit, hactiveBit,
      huLow]
    rfl
  have hsourceParity : x.core.rCoeff.val.testBit 0 = true :=
    source_uEven_rCoeff_testBit_zero tail.succ counterWidth modulus
      kaliskiSteps paddingSteps x hmodulusOdd hbezout huEven
  have hrLowOut :
      (rCoeffLowBit tail.succ counterWidth).get routed = true := by
    calc
      (rCoeffLowBit tail.succ counterWidth).get routed =
          (rCoeffValueBit tail.succ counterWidth 0).get
            (uDiv2ThenSMul2Step tail.succ counterWidth written) := by
        rw [hroute]
        rfl
      _ = (rCoeffValueBit tail.succ counterWidth 0).get written :=
        uDiv2ThenSMul2Step_get_rCoeffValueBit
          tail.succ counterWidth 0 written
      _ = (rCoeffValueBit tail.succ counterWidth 0).get staged := by
        dsimp [written]
        exact MK.Compact.activeScratchBToHistoryStep_get_of_target_ne
          tail.succ counterWidth historyIndex
          (rCoeffValueBit tail.succ counterWidth 0)
          (by
            simpa [rCoeffValueBit, historyBit,
              RegisterBits.rCoeffValueBit] using
              (liftCoreBit_wire_ne tail.succ counterWidth
                (RegisterBits.rCoeff_history_wire_ne tail.succ counterWidth
                  (WireAddress.littleEndianWire
                    (0 : Fin (tail.succ + 1))) historyIndex)).symm)
          staged
      _ = (rCoeffValueBit tail.succ counterWidth 0).get x := by
        dsimp [staged]
        exact selectedBranchCodeToScratchStep_get_rCoeffValueBit
          tail.succ counterWidth (0 : Fin tail.succ) tempIndex 0 x
      _ = true := by
        rw [rCoeffValueBit_get]
        change x.core.rCoeff.val.testBit (0 : Nat) = true
        exact hsourceParity
  exact branchResidueCertificate_uEven tail.succ counterWidth historyIndex
    routed hactiveOut hcompareOut hscratchAOut hscratchBOut hhistoryOut
    hrLowOut

/-- The complete new compact body reaches a clean reusable routing boundary
on the active `uEven` branch. -/
theorem activeBranchBody_uEven_routeCleanup_clean
    (tail counterWidth modulus kaliskiSteps paddingSteps : Nat)
    (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hhistory :
      x.core.history.val.testBit (WireAddress.bitIndex historyIndex).val = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (huEven : x.core.u.val.testBit (0 : Nat) = false)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters tail.succ counterWidth x.core
        kaliskiSteps paddingSteps)) :
    RouteCleanupCleanEndpoint tail.succ counterWidth
      (activeBranchBodyStep tail.succ counterWidth
        (0 : Fin tail.succ) finalBit tempIndex historyIndex x) := by
  let routed := activeBranchRoutedStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
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
  have hresidue :
      BranchResidueCertificate tail.succ counterWidth historyIndex routed := by
    rw [hroute]
    exact selected_uEven_residueCertificate tail counterWidth modulus
      kaliskiSteps paddingSteps tempIndex historyIndex x hactive hcompare
      hscratchA hscratchB hhistory hwork huEven hmodulusOdd hbezout
  have hpathOut : (pathBit tail.succ counterWidth).get routed = false := by
    rw [hroute]
    exact (selectedBranchCodeThenHistoryThenShiftStep_get_path
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x).trans
      hpath
  have hactiveOut : (activeBit tail.succ counterWidth).get routed = true := by
    rw [hroute, selectedBranchCodeThenHistoryThenShiftStep_get_active,
      hactiveBit]
  have hscratchAOut :
      (scratchABit tail.succ counterWidth).get routed = true := by
    rw [hroute, selectedBranchCodeThenHistoryThenShiftStep_get_scratchA_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hactiveBit, huLow]
    rfl
  have hscratchBOut :
      (scratchBBit tail.succ counterWidth).get routed = false := by
    rw [hroute, selectedBranchCodeThenHistoryThenShiftStep_get_scratchB_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hactiveBit, huLow]
    rfl
  have hpathCertificate :
      BranchCodePathCertificate tail.succ counterWidth routed := by
    constructor
    rw [hpathOut, hactiveOut, hscratchAOut, hscratchBOut]
    rfl
  rw [activeBranchBodyStep_eq_stages]
  exact routeCleanup_cleanEndpoint tail.succ counterWidth historyIndex routed
    hpathCertificate hresidue

/-- The literal compact even-route gates reach the exact `vEven` residue
certificate; the zero low `r` bit follows from the established coefficient
top-bit range certificate and the physical cyclic shift. -/
theorem selected_vEven_residueCertificate
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hvNonzero : x.core.v.val ≠ 0)
    (huOdd : x.core.u.val.testBit (0 : Nat) = true)
    (hvEven : x.core.v.val.testBit (0 : Nat) = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hhistory :
      x.core.history.val.testBit (WireAddress.bitIndex historyIndex).val = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    BranchResidueCertificate tail.succ counterWidth historyIndex
      (selectedBranchCodeThenHistoryThenShiftStep tail.succ counterWidth
        (0 : Fin tail.succ) tempIndex historyIndex x) := by
  let routed := selectedBranchCodeThenHistoryThenShiftStep
    tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
  let staged := selectedBranchCodeToScratchStep
    tail.succ counterWidth (0 : Fin tail.succ) tempIndex x
  let written := MK.Compact.activeScratchBToHistoryStep
    tail.succ counterWidth historyIndex staged
  have hactiveBit : (activeBit tail.succ counterWidth).get x = true := by
    simpa only [activeBit_get] using hactive
  have hcompareBit : (compareBit tail.succ counterWidth).get x = false := by
    simpa only [compareBit_get] using hcompare
  have hscratchABit : (scratchABit tail.succ counterWidth).get x = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBBit : (scratchBBit tail.succ counterWidth).get x = false := by
    simpa only [scratchBBit_get] using hscratchB
  have hhistoryBit :
      (historyBit tail.succ counterWidth historyIndex).get x = false := by
    simpa only [historyBit_get] using hhistory
  have huLow :
      (uLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = true := by
    simpa [uLowBit] using huOdd
  have hvLow :
      (vLowBit tail.succ counterWidth (0 : Fin tail.succ)).get x = false := by
    simpa [vLowBit] using hvEven
  have hroute : routed = vDiv2ThenRMul2Step tail.succ counterWidth written := by
    exact selectedBranchCodeThenHistoryThenShiftStep_eq_vShift_of_vEven
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hactiveBit huLow hvLow hscratchABit hscratchBBit (hwork tempIndex)
  have hactiveOut : (activeBit tail.succ counterWidth).get routed = true := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_active, hactiveBit]
  have hcompareOut : (compareBit tail.succ counterWidth).get routed = false := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_compare, hcompareBit]
  have hscratchAOut :
      (scratchABit tail.succ counterWidth).get routed = false := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_scratchA_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hactiveBit, huLow, hvLow]
    rfl
  have hscratchBOut :
      (scratchBBit tail.succ counterWidth).get routed = true := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_scratchB_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hactiveBit, huLow, hvLow]
    rfl
  have hhistoryOut :
      (historyBit tail.succ counterWidth historyIndex).get routed = true := by
    dsimp [routed]
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_history_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hhistoryBit, hactiveBit,
      huLow, hvLow]
    rfl
  have htop :
      x.core.rCoeff.val.testBit (Fin.last tail.succ).val = false :=
    arith.vEven_msb hactive hvNonzero huOdd hvEven
  have hrLowOut :
      (rCoeffLowBit tail.succ counterWidth).get routed = false := by
    calc
      (rCoeffLowBit tail.succ counterWidth).get routed =
          (rCoeffValueBit tail.succ counterWidth 0).get
            (vDiv2ThenRMul2Step tail.succ counterWidth written) := by
        rw [hroute]
        rfl
      _ = (rCoeffValueBit tail.succ counterWidth
          (Fin.last tail.succ)).get written :=
        vDiv2ThenRMul2Step_get_rCoeffValueBit_zero
          tail.succ counterWidth written
      _ = (rCoeffValueBit tail.succ counterWidth
          (Fin.last tail.succ)).get staged := by
        dsimp [written]
        exact MK.Compact.activeScratchBToHistoryStep_get_of_target_ne
          tail.succ counterWidth historyIndex
          (rCoeffValueBit tail.succ counterWidth (Fin.last tail.succ))
          (by
            simpa [rCoeffValueBit, historyBit,
              RegisterBits.rCoeffValueBit] using
              (liftCoreBit_wire_ne tail.succ counterWidth
                (RegisterBits.rCoeff_history_wire_ne tail.succ counterWidth
                  (WireAddress.littleEndianWire (Fin.last tail.succ))
                  historyIndex)).symm)
          staged
      _ = (rCoeffValueBit tail.succ counterWidth
          (Fin.last tail.succ)).get x := by
        dsimp [staged]
        exact selectedBranchCodeToScratchStep_get_rCoeffValueBit
          tail.succ counterWidth (0 : Fin tail.succ) tempIndex
          (Fin.last tail.succ) x
      _ = false := by
        rw [rCoeffValueBit_get]
        exact htop
  exact branchResidueCertificate_vEven tail.succ counterWidth historyIndex
    routed hactiveOut hcompareOut hscratchAOut hscratchBOut hhistoryOut
    hrLowOut

/-- The complete new compact body reaches a clean reusable routing boundary
on the active `vEven` branch. -/
theorem activeBranchBody_vEven_routeCleanup_clean
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hvNonzero : x.core.v.val ≠ 0)
    (huOdd : x.core.u.val.testBit (0 : Nat) = true)
    (hvEven : x.core.v.val.testBit (0 : Nat) = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hhistory :
      x.core.history.val.testBit (WireAddress.bitIndex historyIndex).val = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RouteCleanupCleanEndpoint tail.succ counterWidth
      (activeBranchBodyStep tail.succ counterWidth
        (0 : Fin tail.succ) finalBit tempIndex historyIndex x) := by
  let routed := activeBranchRoutedStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit tempIndex historyIndex x
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
  have hresidue :
      BranchResidueCertificate tail.succ counterWidth historyIndex routed := by
    rw [hroute]
    exact selected_vEven_residueCertificate tail counterWidth tempIndex
      historyIndex x hactive hvNonzero huOdd hvEven hcompare hscratchA
      hscratchB hhistory hwork arith
  have hpathOut : (pathBit tail.succ counterWidth).get routed = false := by
    rw [hroute]
    exact (selectedBranchCodeThenHistoryThenShiftStep_get_path
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x).trans
      hpath
  have hactiveOut : (activeBit tail.succ counterWidth).get routed = true := by
    rw [hroute, selectedBranchCodeThenHistoryThenShiftStep_get_active,
      hactiveBit]
  have hscratchAOut :
      (scratchABit tail.succ counterWidth).get routed = false := by
    rw [hroute, selectedBranchCodeThenHistoryThenShiftStep_get_scratchA_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hactiveBit, huLow, hvLow]
    rfl
  have hscratchBOut :
      (scratchBBit tail.succ counterWidth).get routed = true := by
    rw [hroute, selectedBranchCodeThenHistoryThenShiftStep_get_scratchB_clean
      tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
      hscratchABit hscratchBBit (hwork tempIndex), hactiveBit, huLow, hvLow]
    rfl
  have hpathCertificate :
      BranchCodePathCertificate tail.succ counterWidth routed := by
    constructor
    rw [hpathOut, hactiveOut, hscratchAOut, hscratchBOut]
    rfl
  rw [activeBranchBodyStep_eq_stages]
  exact routeCleanup_cleanEndpoint tail.succ counterWidth historyIndex routed
    hpathCertificate hresidue

/-- The complete literal compact odd slice reaches the `uGreater` residue
certificate, including the coefficient-parity fact needed by cleanup. -/
theorem selected_uGreater_residueCertificate
    (tail counterWidth modulus kaliskiSteps paddingSteps : Nat)
    (historyIndex : Fin (2 * tail.succ))
    (input : MK.Compact.Registers tail.succ counterWidth)
    (hactive : input.core.active = true)
    (hvNonzero : input.core.v.val ≠ 0)
    (huOdd : input.core.u.val.testBit (0 : Nat) = true)
    (hvOdd : input.core.v.val.testBit (0 : Nat) = true)
    (hlt : input.core.v.val < input.core.u.val)
    (hcompare : input.core.compare = true)
    (hscratchA : input.core.scratchA = false)
    (hscratchB : input.core.scratchB = false)
    (hhistory :
      input.core.history.val.testBit
        (WireAddress.bitIndex historyIndex).val = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get input = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get input = false)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters tail.succ counterWidth input.core
        kaliskiSteps paddingSteps))
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      input.core) :
    BranchResidueCertificate tail.succ counterWidth historyIndex
      (selectedOddDataThenBranchHistoryShiftStep tail.succ counterWidth
        historyIndex input) := by
  let data := compareSelectedOddDataPathStep tail.succ counterWidth input
  let routed := selectedOddDataThenBranchHistoryShiftStep
    tail.succ counterWidth historyIndex input
  let staged := oddBranchCodeToScratchStep tail.succ counterWidth data
  let written := MK.Compact.activeScratchBToHistoryStep
    tail.succ counterWidth historyIndex staged
  have hcompareInput : (compareBit tail.succ counterWidth).get input = true := by
    simpa only [compareBit_get] using hcompare
  have hscratchAInput :
      (scratchABit tail.succ counterWidth).get input = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBInput :
      (scratchBBit tail.succ counterWidth).get input = false := by
    simpa only [scratchBBit_get] using hscratchB
  have hpreserve
      (observed : EncodedBit (registerEncoding tail.succ counterWidth))
      (hu : ∀ bit : Fin tail.succ,
        (RegisterBits.uValueBit tail.succ counterWidth bit).wire ≠ observed.wire)
      (hr : ∀ bit : Fin (tail.succ + 1),
        (RegisterBits.rCoeffValueBit tail.succ counterWidth bit).wire ≠
          observed.wire) :
      observed.get data.core = observed.get input.core := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_get_coreBit_of_compare_true
      tail.succ counterWidth observed hu hr input hcompareInput
      hscratchAInput hscratchBInput
  have hactiveData : (activeBit tail.succ counterWidth).get data = true := by
    change (RegisterBits.activeBit tail.succ counterWidth).get data.core = true
    rw [hpreserve (RegisterBits.activeBit tail.succ counterWidth)
      (fun bit => (RegisterBits.active_u_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit)).symm)
      (fun bit => (RegisterBits.active_rCoeff_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit)).symm)]
    simpa only [activeBit_get, RegisterBits.activeBit_get] using hactive
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
    simpa only [scratchABit_get, RegisterBits.scratchABit_get] using hscratchA
  have hscratchBData :
      (scratchBBit tail.succ counterWidth).get data = false := by
    change (RegisterBits.scratchBBit tail.succ counterWidth).get data.core = false
    rw [hpreserve (RegisterBits.scratchBBit tail.succ counterWidth)
      (fun bit => RegisterBits.u_scratchB_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.rCoeff_scratchB_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))]
    simpa only [scratchBBit_get, RegisterBits.scratchBBit_get] using hscratchB
  have hhistoryData :
      (historyBit tail.succ counterWidth historyIndex).get data = false := by
    change (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
      data.core = false
    rw [hpreserve (RegisterBits.historyBit tail.succ counterWidth historyIndex)
      (fun bit => RegisterBits.u_history_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit) historyIndex)
      (fun bit => RegisterBits.rCoeff_history_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit) historyIndex)]
    simpa only [RegisterBits.historyBit_get] using hhistory
  have hroute : routed = uDiv2ThenSMul2Step tail.succ counterWidth written := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    exact oddBranchCodeThenHistoryThenShiftStep_eq_uShift
      tail.succ counterWidth historyIndex data hactiveData hcompareData
      hscratchAData
  have hactiveOut : (activeBit tail.succ counterWidth).get routed = true := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_active, hactiveData]
  have hcompareOut : (compareBit tail.succ counterWidth).get routed = true := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_compare, hcompareData]
  have hscratchAOut :
      (scratchABit tail.succ counterWidth).get routed = true := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_scratchA,
      hscratchAData, hactiveData, hcompareData]
    rfl
  have hscratchBOut :
      (scratchBBit tail.succ counterWidth).get routed = true := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_scratchB,
      hscratchBData, hactiveData, hcompareData]
    rfl
  have hhistoryOut :
      (historyBit tail.succ counterWidth historyIndex).get routed = true := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_history,
      hhistoryData, hscratchBData, hactiveData, hcompareData]
    rfl
  have hsourceParity :
      (input.core.rCoeff.val + input.core.sCoeff.val).testBit 0 = true :=
    source_uGreater_rCoeff_add_testBit_zero tail.succ counterWidth modulus
      kaliskiSteps paddingSteps input hmodulusOdd hbezout huOdd hvOdd hlt
  have hadd :
      input.core.rCoeff.val + input.core.sCoeff.val < 2 ^ (tail.succ + 1) :=
    arith.uGreater_add hactive hvNonzero huOdd hvOdd hlt
  have haddVal :
      (input.core.rCoeff + input.core.sCoeff).val =
        input.core.rCoeff.val + input.core.sCoeff.val :=
    Fin.val_add_eq_of_add_lt hadd
  have hdataR : data.core.rCoeff.val.testBit 0 = true := by
    calc
      data.core.rCoeff.val.testBit 0 =
          (input.core.rCoeff + input.core.sCoeff).val.testBit 0 := by
        simpa [data] using
          (compareSelectedOddDataPathStep_get_rCoeff_add_of_compare_true_cleanWork
            tail.succ counterWidth input (0 : Fin (tail.succ + 1))
            hcompareInput hscratchAInput hscratchBInput hcarry hwork)
      _ = (input.core.rCoeff.val + input.core.sCoeff.val).testBit 0 := by
        rw [haddVal]
      _ = true := hsourceParity
  have hrLowOut :
      (rCoeffLowBit tail.succ counterWidth).get routed = true := by
    calc
      (rCoeffLowBit tail.succ counterWidth).get routed =
          (rCoeffValueBit tail.succ counterWidth 0).get
            (uDiv2ThenSMul2Step tail.succ counterWidth written) := by
        rw [hroute]
        rfl
      _ = (rCoeffValueBit tail.succ counterWidth 0).get written :=
        uDiv2ThenSMul2Step_get_rCoeffValueBit
          tail.succ counterWidth 0 written
      _ = (rCoeffValueBit tail.succ counterWidth 0).get staged := by
        dsimp [written]
        exact MK.Compact.activeScratchBToHistoryStep_get_of_target_ne
          tail.succ counterWidth historyIndex
          (rCoeffValueBit tail.succ counterWidth 0)
          (by
            simpa [rCoeffValueBit, historyBit,
              RegisterBits.rCoeffValueBit] using
              (liftCoreBit_wire_ne tail.succ counterWidth
                (RegisterBits.rCoeff_history_wire_ne tail.succ counterWidth
                  (WireAddress.littleEndianWire
                    (0 : Fin (tail.succ + 1))) historyIndex)).symm)
          staged
      _ = (rCoeffValueBit tail.succ counterWidth 0).get data := by
        dsimp [staged]
        exact oddBranchCodeToScratchStep_get_of_targets_ne
          tail.succ counterWidth (rCoeffValueBit tail.succ counterWidth 0)
          (by
            simpa [rCoeffValueBit, scratchABit,
              RegisterBits.rCoeffValueBit] using
              (liftCoreBit_wire_ne tail.succ counterWidth
                (RegisterBits.rCoeff_scratchA_wire_ne tail.succ counterWidth
                  (WireAddress.littleEndianWire
                    (0 : Fin (tail.succ + 1))))).symm)
          (by
            simpa [rCoeffValueBit, scratchBBit,
              RegisterBits.rCoeffValueBit] using
              (liftCoreBit_wire_ne tail.succ counterWidth
                (RegisterBits.rCoeff_scratchB_wire_ne tail.succ counterWidth
                  (WireAddress.littleEndianWire
                    (0 : Fin (tail.succ + 1))))).symm)
          data
      _ = true := by
        rw [rCoeffValueBit_get]
        change data.core.rCoeff.val.testBit (0 : Nat) = true
        exact hdataR
  exact branchResidueCertificate_uGreater tail.succ counterWidth historyIndex
    routed hactiveOut hcompareOut hscratchAOut hscratchBOut hhistoryOut
    hrLowOut

/-- The complete literal compact odd slice reaches the `vLe` residue
certificate.  The physical odd arithmetic leaves `r` unchanged, so the
subsequent cyclic doubling exposes its certified-zero top bit at the low
position consumed by cleanup. -/
theorem selected_vLe_residueCertificate
    (tail counterWidth : Nat)
    (historyIndex : Fin (2 * tail.succ))
    (input : MK.Compact.Registers tail.succ counterWidth)
    (hactive : input.core.active = true)
    (hvNonzero : input.core.v.val ≠ 0)
    (huOdd : input.core.u.val.testBit (0 : Nat) = true)
    (hvOdd : input.core.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ input.core.v.val < input.core.u.val)
    (hcompare : input.core.compare = false)
    (hscratchA : input.core.scratchA = false)
    (hscratchB : input.core.scratchB = false)
    (hhistory :
      input.core.history.val.testBit
        (WireAddress.bitIndex historyIndex).val = false)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      input.core) :
    BranchResidueCertificate tail.succ counterWidth historyIndex
      (selectedOddDataThenBranchHistoryShiftStep tail.succ counterWidth
        historyIndex input) := by
  let data := compareSelectedOddDataPathStep tail.succ counterWidth input
  let routed := selectedOddDataThenBranchHistoryShiftStep
    tail.succ counterWidth historyIndex input
  let staged := oddBranchCodeToScratchStep tail.succ counterWidth data
  let written := MK.Compact.activeScratchBToHistoryStep
    tail.succ counterWidth historyIndex staged
  have hcompareInput : (compareBit tail.succ counterWidth).get input = false := by
    simpa only [compareBit_get] using hcompare
  have hscratchAInput :
      (scratchABit tail.succ counterWidth).get input = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBInput :
      (scratchBBit tail.succ counterWidth).get input = false := by
    simpa only [scratchBBit_get] using hscratchB
  have hpreserve
      (observed : EncodedBit (registerEncoding tail.succ counterWidth))
      (hv : ∀ bit : Fin tail.succ,
        (RegisterBits.vValueBit tail.succ counterWidth bit).wire ≠ observed.wire)
      (hs : ∀ bit : Fin (tail.succ + 1),
        (RegisterBits.sCoeffValueBit tail.succ counterWidth bit).wire ≠
          observed.wire) :
      observed.get data.core = observed.get input.core := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_get_coreBit_of_compare_false
      tail.succ counterWidth observed hv hs input hcompareInput
      hscratchAInput hscratchBInput
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
  have hscratchBData :
      (scratchBBit tail.succ counterWidth).get data = false := by
    change (RegisterBits.scratchBBit tail.succ counterWidth).get data.core = false
    rw [hpreserve (RegisterBits.scratchBBit tail.succ counterWidth)
      (fun bit => RegisterBits.v_scratchB_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.sCoeff_scratchB_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))]
    simpa only [RegisterBits.scratchBBit_get] using hscratchB
  have hhistoryData :
      (historyBit tail.succ counterWidth historyIndex).get data = false := by
    change (RegisterBits.historyBit tail.succ counterWidth historyIndex).get
      data.core = false
    rw [hpreserve (RegisterBits.historyBit tail.succ counterWidth historyIndex)
      (fun bit => RegisterBits.v_history_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit) historyIndex)
      (fun bit => RegisterBits.sCoeff_history_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit) historyIndex)]
    simpa only [RegisterBits.historyBit_get] using hhistory
  have hroute : routed = vDiv2ThenRMul2Step tail.succ counterWidth written := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    exact oddBranchCodeThenHistoryThenShiftStep_eq_vShift
      tail.succ counterWidth historyIndex data hactiveData hcompareData
      hscratchAData
  have hactiveOut : (activeBit tail.succ counterWidth).get routed = true := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_active, hactiveData]
  have hcompareOut : (compareBit tail.succ counterWidth).get routed = false := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_compare, hcompareData]
  have hscratchAOut :
      (scratchABit tail.succ counterWidth).get routed = false := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_scratchA,
      hscratchAData, hactiveData, hcompareData]
    rfl
  have hscratchBOut :
      (scratchBBit tail.succ counterWidth).get routed = false := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_scratchB,
      hscratchBData, hactiveData, hcompareData]
    rfl
  have hhistoryOut :
      (historyBit tail.succ counterWidth historyIndex).get routed = false := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_history,
      hhistoryData, hscratchBData, hactiveData, hcompareData]
    rfl
  have htop :
      input.core.rCoeff.val.testBit (Fin.last tail.succ).val = false :=
    arith.vLe_msb hactive hvNonzero huOdd hvOdd hnlt
  have hrLowOut :
      (rCoeffLowBit tail.succ counterWidth).get routed = false := by
    calc
      (rCoeffLowBit tail.succ counterWidth).get routed =
          (rCoeffValueBit tail.succ counterWidth 0).get
            (vDiv2ThenRMul2Step tail.succ counterWidth written) := by
        rw [hroute]
        rfl
      _ = (rCoeffValueBit tail.succ counterWidth
          (Fin.last tail.succ)).get written :=
        vDiv2ThenRMul2Step_get_rCoeffValueBit_zero
          tail.succ counterWidth written
      _ = (rCoeffValueBit tail.succ counterWidth
          (Fin.last tail.succ)).get staged := by
        dsimp [written]
        exact MK.Compact.activeScratchBToHistoryStep_get_of_target_ne
          tail.succ counterWidth historyIndex
          (rCoeffValueBit tail.succ counterWidth (Fin.last tail.succ))
          (by
            simpa [rCoeffValueBit, historyBit,
              RegisterBits.rCoeffValueBit] using
              (liftCoreBit_wire_ne tail.succ counterWidth
                (RegisterBits.rCoeff_history_wire_ne tail.succ counterWidth
                  (WireAddress.littleEndianWire (Fin.last tail.succ))
                  historyIndex)).symm)
          staged
      _ = (rCoeffValueBit tail.succ counterWidth
          (Fin.last tail.succ)).get data := by
        dsimp [staged]
        exact oddBranchCodeToScratchStep_get_of_targets_ne
          tail.succ counterWidth
          (rCoeffValueBit tail.succ counterWidth (Fin.last tail.succ))
          (by
            simpa [rCoeffValueBit, scratchABit,
              RegisterBits.rCoeffValueBit] using
              (liftCoreBit_wire_ne tail.succ counterWidth
                (RegisterBits.rCoeff_scratchA_wire_ne tail.succ counterWidth
                  (WireAddress.littleEndianWire
                    (Fin.last tail.succ)))).symm)
          (by
            simpa [rCoeffValueBit, scratchBBit,
              RegisterBits.rCoeffValueBit] using
              (liftCoreBit_wire_ne tail.succ counterWidth
                (RegisterBits.rCoeff_scratchB_wire_ne tail.succ counterWidth
                  (WireAddress.littleEndianWire
                    (Fin.last tail.succ)))).symm)
          data
      _ = input.core.rCoeff.val.testBit (Fin.last tail.succ).val := by
        simpa [rCoeffValueBit_get, data] using
          (compareSelectedOddDataPathStep_get_rCoeff_of_compare_false
            tail.succ counterWidth input (Fin.last tail.succ)
            hcompareInput hscratchAInput hscratchBInput)
      _ = false := htop
  exact branchResidueCertificate_vLe tail.succ counterWidth historyIndex
    routed hactiveOut hcompareOut hscratchAOut hscratchBOut hhistoryOut
    hrLowOut

/-- Both selected odd codes toggle the same two scratch bits.  Consequently
their xor is false, so a retained odd-route `path` bit already satisfies the
route-cleanup certificate independently of the comparison result. -/
theorem selectedOddDataThenBranchHistoryShift_pathCertificate
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (input : MK.Compact.Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get input = true)
    (hpath : (pathBit n counterWidth).get input = true)
    (hscratchA : (scratchABit n counterWidth).get input = false)
    (hscratchB : (scratchBBit n counterWidth).get input = false) :
    BranchCodePathCertificate n counterWidth
      (selectedOddDataThenBranchHistoryShiftStep
        n counterWidth historyIndex input) := by
  let data := compareSelectedOddDataPathStep n counterWidth input
  let routed := selectedOddDataThenBranchHistoryShiftStep
    n counterWidth historyIndex input
  have hpreserve
      (observed : EncodedBit (registerEncoding n counterWidth))
      (hu : ∀ bit : Fin n,
        (RegisterBits.uValueBit n counterWidth bit).wire ≠ observed.wire)
      (hv : ∀ bit : Fin n,
        (RegisterBits.vValueBit n counterWidth bit).wire ≠ observed.wire)
      (hr : ∀ bit : Fin (n + 1),
        (RegisterBits.rCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
      (hs : ∀ bit : Fin (n + 1),
        (RegisterBits.sCoeffValueBit n counterWidth bit).wire ≠ observed.wire) :
      observed.get data.core = observed.get input.core := by
    dsimp [data]
    exact compareSelectedOddDataPathStep_get_coreBit_of_disjoint_clean
      n counterWidth observed hu hv hr hs input hscratchA hscratchB
  have hactiveData : (activeBit n counterWidth).get data = true := by
    change (RegisterBits.activeBit n counterWidth).get data.core = true
    rw [hpreserve (RegisterBits.activeBit n counterWidth)
      (fun bit => (RegisterBits.active_u_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)).symm)
      (fun bit => (RegisterBits.active_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)).symm)
      (fun bit => (RegisterBits.active_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)).symm)
      (fun bit => (RegisterBits.active_sCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit)).symm)]
    simpa only [activeBit_get, RegisterBits.activeBit_get] using hactive
  have hscratchAData :
      (scratchABit n counterWidth).get data = false := by
    change (RegisterBits.scratchABit n counterWidth).get data.core = false
    rw [hpreserve (RegisterBits.scratchABit n counterWidth)
      (fun bit => RegisterBits.u_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.v_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))]
    simpa only [scratchABit_get, RegisterBits.scratchABit_get] using hscratchA
  have hscratchBData :
      (scratchBBit n counterWidth).get data = false := by
    change (RegisterBits.scratchBBit n counterWidth).get data.core = false
    rw [hpreserve (RegisterBits.scratchBBit n counterWidth)
      (fun bit => RegisterBits.u_scratchB_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.v_scratchB_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))
      (fun bit => RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))]
    simpa only [scratchBBit_get, RegisterBits.scratchBBit_get] using hscratchB
  have hactiveOut : (activeBit n counterWidth).get routed = true := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_active, hactiveData]
  have hpathOut : (pathBit n counterWidth).get routed = true := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_path,
      compareSelectedOddDataPathStep_get_path_clean
        n counterWidth input hscratchA hscratchB]
    exact hpath
  have hscratchAOut :
      (scratchABit n counterWidth).get routed =
        (compareBit n counterWidth).get data := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_scratchA,
      hscratchAData, hactiveData]
    cases (compareBit n counterWidth).get data <;> rfl
  have hscratchBOut :
      (scratchBBit n counterWidth).get routed =
        (compareBit n counterWidth).get data := by
    dsimp [routed, selectedOddDataThenBranchHistoryShiftStep]
    rw [oddBranchCodeThenHistoryThenShiftStep_get_scratchB,
      hscratchBData, hactiveData]
    cases (compareBit n counterWidth).get data <;> rfl
  constructor
  rw [hpathOut, hactiveOut, hscratchAOut, hscratchBOut]
  cases (compareBit n counterWidth).get data <;> rfl

private theorem modeControlledArithmeticCertificate_setCompare
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

/-- The complete native body reaches a reusable route boundary on the active
odd `uGreater` branch. -/
theorem activeBranchBody_uGreater_routeCleanup_clean
    (tail counterWidth modulus kaliskiSteps paddingSteps : Nat)
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
    (hhistory :
      x.core.history.val.testBit
        (WireAddress.bitIndex historyIndex).val = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters tail.succ counterWidth x.core
        kaliskiSteps paddingSteps))
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RouteCleanupCleanEndpoint tail.succ counterWidth
      (activeBranchBodyStep tail.succ counterWidth
        (0 : Fin tail.succ) finalBit tempIndex historyIndex x) := by
  let selected := activeOddUGreaterSelectorStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit x
  let routed := activeBranchRoutedStep tail.succ counterWidth
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
  have hselectedHistory : selected.core.history.val.testBit
      (WireAddress.bitIndex historyIndex).val = false := by
    rw [hcoreEq]
    exact hhistory
  have hselectedBezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters tail.succ counterWidth selected.core
        kaliskiSteps paddingSteps) := by
    rw [hcoreEq]
    simpa [RoundState.fromRegisters] using hbezout
  have hselectedArith :
      ModeControlledSemanticStepArithmeticCertificate tail counterWidth
        selected.core := by
    rw [hcoreEq]
    exact modeControlledArithmeticCertificate_setCompare
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
  have hresidue :
      BranchResidueCertificate tail.succ counterWidth historyIndex routed := by
    rw [hroute]
    exact selected_uGreater_residueCertificate tail counterWidth modulus
      kaliskiSteps paddingSteps historyIndex selected hselectedActive
      hselectedVNonzero hselectedUOdd hselectedVOdd hselectedLt
      hselectedCompare hselectedScratchA hselectedScratchB hselectedHistory
      endpoint.carryIn endpoint.carryWork hmodulusOdd hselectedBezout
      hselectedArith
  have hpathCertificate :
      BranchCodePathCertificate tail.succ counterWidth routed := by
    rw [hroute]
    exact selectedOddDataThenBranchHistoryShift_pathCertificate
      tail.succ counterWidth historyIndex selected
      (by simpa only [activeBit_get] using hselectedActive) hselectedPath
      endpoint.scratchA endpoint.scratchB
  rw [activeBranchBodyStep_eq_stages]
  exact routeCleanup_cleanEndpoint tail.succ counterWidth historyIndex routed
    hpathCertificate hresidue

/-- The complete native body reaches a reusable route boundary on the active
odd `vLe` branch. -/
theorem activeBranchBody_vLe_routeCleanup_clean
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
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
    (hhistory :
      x.core.history.val.testBit
        (WireAddress.bitIndex historyIndex).val = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ)
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RouteCleanupCleanEndpoint tail.succ counterWidth
      (activeBranchBodyStep tail.succ counterWidth
        (0 : Fin tail.succ) finalBit tempIndex historyIndex x) := by
  let selected := activeOddUGreaterSelectorStep tail.succ counterWidth
    (0 : Fin tail.succ) finalBit x
  let routed := activeBranchRoutedStep tail.succ counterWidth
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
  have hselectedHistory : selected.core.history.val.testBit
      (WireAddress.bitIndex historyIndex).val = false := by
    rw [hcoreEq]
    exact hhistory
  have hselectedArith :
      ModeControlledSemanticStepArithmeticCertificate tail counterWidth
        selected.core := by
    rw [hcoreEq]
    exact modeControlledArithmeticCertificate_setCompare
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
  have hresidue :
      BranchResidueCertificate tail.succ counterWidth historyIndex routed := by
    rw [hroute]
    exact selected_vLe_residueCertificate tail counterWidth historyIndex
      selected hselectedActive hselectedVNonzero hselectedUOdd hselectedVOdd
      hselectedNlt hselectedCompare hselectedScratchA hselectedScratchB
      hselectedHistory hselectedArith
  have hpathCertificate :
      BranchCodePathCertificate tail.succ counterWidth routed := by
    rw [hroute]
    exact selectedOddDataThenBranchHistoryShift_pathCertificate
      tail.succ counterWidth historyIndex selected
      (by simpa only [activeBit_get] using hselectedActive) hselectedPath
      endpoint.scratchA endpoint.scratchB
  rw [activeBranchBodyStep_eq_stages]
  exact routeCleanup_cleanEndpoint tail.succ counterWidth historyIndex routed
    hpathCertificate hresidue

/-- Every active compact branch returns the sole reusable VBE carry object to
its clean value.  The odd paths reuse it first for source subtraction and then
for coefficient addition; the even paths borrow and restore one of its bits
for branch-code staging. -/
theorem activeBranchBody_coefficientAdder_cleanEndpoint
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ) :
    (activeBranchBodyStep tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x).shared.coefficientAdder =
        cleanCoeffAdderWork tail.succ := by
  let routed := activeBranchRoutedStep tail.succ counterWidth
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
  have hrouted : routed.shared.coefficientAdder = cleanCoeffAdderWork tail.succ := by
    cases hu : x.core.u.val.testBit (0 : Nat) with
    | false =>
        have huLow :
            (uLowBit tail.succ counterWidth
              (0 : Fin tail.succ)).get x = false := by
          simpa [uLowBit] using hu
        have hpair :
            (((uValueWord tail.succ counterWidth).bit
                (0 : Fin tail.succ)).get x &&
              ((vValueWord tail.succ counterWidth).bit
                (0 : Fin tail.succ)).get x) = false := by
          rw [show ((uValueWord tail.succ counterWidth).bit
            (0 : Fin tail.succ)).get x = false by
              simpa only [uLowBit] using huLow]
          simp
        have hroute : routed = selectedBranchCodeThenHistoryThenShiftStep
            tail.succ counterWidth (0 : Fin tail.succ) tempIndex
              historyIndex x := by
          dsimp [routed]
          exact activeBranchRoutedStep_eq_selected_even_route_of_pair_false
            tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
            historyIndex x hactiveBit hpath hcontrol hcompareBit hscratchABit
            hscratchBBit hpair
        rw [hroute]
        exact
          selectedBranchCodeThenHistoryThenShiftStep_coefficientAdder_cleanEndpoint
            tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex x
            hscratchABit hscratchBBit hcarry hwork
    | true =>
        cases hv : x.core.v.val.testBit (0 : Nat) with
        | false =>
            have hvLow :
                (vLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get x = false := by
              simpa [vLowBit] using hv
            have hpair :
                (((uValueWord tail.succ counterWidth).bit
                    (0 : Fin tail.succ)).get x &&
                  ((vValueWord tail.succ counterWidth).bit
                    (0 : Fin tail.succ)).get x) = false := by
              rw [show ((vValueWord tail.succ counterWidth).bit
                (0 : Fin tail.succ)).get x = false by
                  simpa only [vLowBit] using hvLow]
              simp
            have hroute : routed = selectedBranchCodeThenHistoryThenShiftStep
                tail.succ counterWidth (0 : Fin tail.succ) tempIndex
                  historyIndex x := by
              dsimp [routed]
              exact activeBranchRoutedStep_eq_selected_even_route_of_pair_false
                tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
                historyIndex x hactiveBit hpath hcontrol hcompareBit
                hscratchABit hscratchBBit hpair
            rw [hroute]
            exact
              selectedBranchCodeThenHistoryThenShiftStep_coefficientAdder_cleanEndpoint
                tail.succ counterWidth (0 : Fin tail.succ) tempIndex
                historyIndex x hscratchABit hscratchBBit hcarry hwork
        | true =>
            let selected := activeOddUGreaterSelectorStep tail.succ counterWidth
              (0 : Fin tail.succ) finalBit x
            have huLow :
                (uLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get x = true := by
              simpa [uLowBit] using hu
            have hvLow :
                (vLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get x = true := by
              simpa [vLowBit] using hv
            have endpoint := activeOddUGreaterSelectorStep_cleanEndpoint
              tail.succ counterWidth (0 : Fin tail.succ) finalBit x hpath
              hcontrol hcompareBit hscratchABit hscratchBBit hcarry hwork hfinal
            have hcoreEq : selected.core =
                { x.core with compare := selected.core.compare } := by
              dsimp [selected]
              exact activeOddUGreaterSelectorStep_core_eq_setCompare
                tail.succ counterWidth (0 : Fin tail.succ) finalBit x hcontrol
            have huSelected :
                (uLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get selected = true := by
              have hselectedUOdd :
                  selected.core.u.val.testBit (0 : Nat) = true := by
                rw [hcoreEq]
                exact hu
              simpa [uLowBit] using hselectedUOdd
            have hvSelected :
                (vLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get selected = true := by
              have hselectedVOdd :
                  selected.core.v.val.testBit (0 : Nat) = true := by
                rw [hcoreEq]
                exact hv
              simpa [vLowBit] using hselectedVOdd
            have hselectedPath :
                (pathBit tail.succ counterWidth).get selected = true := by
              dsimp [selected]
              have huValue : ((uValueWord tail.succ counterWidth).bit
                  (0 : Fin tail.succ)).get x = true := by
                simpa only [uLowBit] using huLow
              have hvValue : ((vValueWord tail.succ counterWidth).bit
                  (0 : Fin tail.succ)).get x = true := by
                simpa only [vLowBit] using hvLow
              rw [endpoint.path, hactiveBit, huValue, hvValue]
              rfl
            have hroute : routed = selectedOddDataThenBranchHistoryShiftStep
                tail.succ counterWidth historyIndex selected := by
              dsimp [routed, selected]
              exact activeBranchRoutedStep_eq_selected_odd_route
                tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
                historyIndex x huSelected hvSelected hselectedPath
                endpoint.control endpoint.scratchA endpoint.scratchB
                (endpoint.carryWork tempIndex)
            rw [hroute]
            exact
              selectedOddDataThenBranchHistoryShiftStep_coefficientAdder_cleanEndpoint
                tail.succ counterWidth historyIndex selected endpoint.scratchA
                endpoint.scratchB endpoint.carryIn endpoint.carryWork
  change
    (activeBranchBodyStep tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x).shared.coefficientAdder =
        (false,
          PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (tail.succ + 1))
  apply Prod.ext
  · have hpreserved := activeBranchBodyStep_get_of_cleanup_targets_ne
      tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
      historyIndex (coefficientCarryInBit tail.succ counterWidth)
      (pathBit_coefficientCarryInBit_wire_ne tail.succ counterWidth)
      (by
        simpa [compareBit] using
          liftCoreBit_coefficientCarryInBit_wire_ne tail.succ counterWidth
            (RegisterBits.compareBit tail.succ counterWidth))
      (by
        simpa [scratchABit] using
          liftCoreBit_coefficientCarryInBit_wire_ne tail.succ counterWidth
            (RegisterBits.scratchABit tail.succ counterWidth))
      (by
        simpa [scratchBBit] using
          liftCoreBit_coefficientCarryInBit_wire_ne tail.succ counterWidth
            (RegisterBits.scratchBBit tail.succ counterWidth)) x
    have hclean : (coefficientCarryInBit tail.succ counterWidth).get
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x) = false := by
      calc
        _ = (coefficientCarryInBit tail.succ counterWidth).get routed := hpreserved
        _ = false := by rw [coefficientCarryInBit_get, hrouted]; rfl
    simpa only [coefficientCarryInBit_get] using hclean
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    have hpreserved := activeBranchBodyStep_get_of_cleanup_targets_ne
      tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
      historyIndex (coefficientCarryWorkBit tail.succ counterWidth bit)
      (pathBit_coefficientCarryWorkBit_wire_ne tail.succ counterWidth bit)
      (by
        simpa [compareBit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne tail.succ counterWidth
            (RegisterBits.compareBit tail.succ counterWidth) bit)
      (by
        simpa [scratchABit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne tail.succ counterWidth
            (RegisterBits.scratchABit tail.succ counterWidth) bit)
      (by
        simpa [scratchBBit] using
          liftCoreBit_coefficientCarryWorkBit_wire_ne tail.succ counterWidth
            (RegisterBits.scratchBBit tail.succ counterWidth) bit) x
    have hclean : (coefficientCarryWorkBit tail.succ counterWidth bit).get
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x) = false := by
      calc
        _ = (coefficientCarryWorkBit tail.succ counterWidth bit).get routed := hpreserved
        _ = false := by
          rw [coefficientCarryWorkBit_get, hrouted]
          exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero
            tail.succ bit
    have hclean' :
        (BinaryLabelEncoding.finIdentityBit tail.succ bit).get
          (activeBranchBodyStep tail.succ counterWidth
            (0 : Fin tail.succ) finalBit tempIndex historyIndex
              x).shared.coefficientAdder.2 = false := by
      simpa only [coefficientCarryWorkBit_get] using hclean
    change
      (BinaryLabelEncoding.finIdentityBit tail.succ bit).get
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex
            x).shared.coefficientAdder.2 = false
    exact hclean'

/-- The complete active body preserves any observation outside its selector
and residue targets, four arithmetic words, reusable VBE work bank, and the
single history slot selected for this round. -/
theorem activeBranchBodyStep_get_of_stable
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (observed : EncodedBit (encoding tail.succ counterWidth))
    (hpathObserved : (pathBit tail.succ counterWidth).wire ≠ observed.wire)
    (hcontrolObserved :
      (controlBit tail.succ counterWidth).wire ≠ observed.wire)
    (hcompareObserved :
      (compareBit tail.succ counterWidth).wire ≠ observed.wire)
    (hscratchAObserved :
      (scratchABit tail.succ counterWidth).wire ≠ observed.wire)
    (hscratchBObserved :
      (scratchBBit tail.succ counterWidth).wire ≠ observed.wire)
    (hhistoryObserved :
      (historyBit tail.succ counterWidth historyIndex).wire ≠ observed.wire)
    (hu : ∀ bit,
      ((uValueWord tail.succ counterWidth).bit bit).wire ≠ observed.wire)
    (hv : ∀ bit,
      ((vValueWord tail.succ counterWidth).bit bit).wire ≠ observed.wire)
    (hr : ∀ bit,
      (rCoeffValueBit tail.succ counterWidth bit).wire ≠ observed.wire)
    (hs : ∀ bit,
      (sCoeffValueBit tail.succ counterWidth bit).wire ≠ observed.wire)
    (hworkObserved : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).wire ≠
        observed.wire)
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ) :
    observed.get (activeBranchBodyStep tail.succ counterWidth
        (0 : Fin tail.succ) finalBit tempIndex historyIndex x) =
      observed.get x := by
  let routed := activeBranchRoutedStep tail.succ counterWidth
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
  have huLowObserved :
      (uLowBit tail.succ counterWidth
        (0 : Fin tail.succ)).wire ≠ observed.wire := by
    simpa only [uLowBit] using hu (0 : Fin tail.succ)
  have hvLowObserved :
      (vLowBit tail.succ counterWidth
        (0 : Fin tail.succ)).wire ≠ observed.wire := by
    simpa only [vLowBit] using hv (0 : Fin tail.succ)
  have hrWord : ∀ bit,
      ((rCoeffValueWord tail.succ counterWidth).bit bit).wire ≠
        observed.wire := by
    intro bit
    simpa only [rCoeffValueWord] using hr bit
  have hsWord : ∀ bit,
      ((sCoeffValueWord tail.succ counterWidth).bit bit).wire ≠
        observed.wire := by
    intro bit
    simpa only [sCoeffValueWord] using hs bit
  have hrouted : observed.get routed = observed.get x := by
    cases huValue : x.core.u.val.testBit (0 : Nat) with
    | false =>
        have huLow :
            (uLowBit tail.succ counterWidth
              (0 : Fin tail.succ)).get x = false := by
          simpa [uLowBit] using huValue
        have hpair :
            (((uValueWord tail.succ counterWidth).bit
                (0 : Fin tail.succ)).get x &&
              ((vValueWord tail.succ counterWidth).bit
                (0 : Fin tail.succ)).get x) = false := by
          rw [show ((uValueWord tail.succ counterWidth).bit
            (0 : Fin tail.succ)).get x = false by
              simpa only [uLowBit] using huLow]
          simp
        have hroute : routed = selectedBranchCodeThenHistoryThenShiftStep
            tail.succ counterWidth (0 : Fin tail.succ) tempIndex
              historyIndex x := by
          dsimp [routed]
          exact activeBranchRoutedStep_eq_selected_even_route_of_pair_false
            tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
            historyIndex x hactiveBit hpath hcontrol hcompareBit hscratchABit
            hscratchBBit hpair
        rw [hroute]
        exact selectedBranchCodeThenHistoryThenShiftStep_get_of_preserved
          tail.succ counterWidth (0 : Fin tail.succ) tempIndex historyIndex
          observed huLowObserved hvLowObserved (hworkObserved tempIndex)
          hscratchAObserved hscratchBObserved hhistoryObserved hu hsWord hv
          hrWord x
    | true =>
        cases hvValue : x.core.v.val.testBit (0 : Nat) with
        | false =>
            have hvLow :
                (vLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get x = false := by
              simpa [vLowBit] using hvValue
            have hpair :
                (((uValueWord tail.succ counterWidth).bit
                    (0 : Fin tail.succ)).get x &&
                  ((vValueWord tail.succ counterWidth).bit
                    (0 : Fin tail.succ)).get x) = false := by
              rw [show ((vValueWord tail.succ counterWidth).bit
                (0 : Fin tail.succ)).get x = false by
                  simpa only [vLowBit] using hvLow]
              simp
            have hroute : routed = selectedBranchCodeThenHistoryThenShiftStep
                tail.succ counterWidth (0 : Fin tail.succ) tempIndex
                  historyIndex x := by
              dsimp [routed]
              exact activeBranchRoutedStep_eq_selected_even_route_of_pair_false
                tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
                historyIndex x hactiveBit hpath hcontrol hcompareBit
                hscratchABit hscratchBBit hpair
            rw [hroute]
            exact selectedBranchCodeThenHistoryThenShiftStep_get_of_preserved
              tail.succ counterWidth (0 : Fin tail.succ) tempIndex
              historyIndex observed huLowObserved hvLowObserved
              (hworkObserved tempIndex) hscratchAObserved hscratchBObserved
              hhistoryObserved hu hsWord hv hrWord x
        | true =>
            let selected := activeOddUGreaterSelectorStep tail.succ counterWidth
              (0 : Fin tail.succ) finalBit x
            have huLow :
                (uLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get x = true := by
              simpa [uLowBit] using huValue
            have hvLow :
                (vLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get x = true := by
              simpa [vLowBit] using hvValue
            have endpoint := activeOddUGreaterSelectorStep_cleanEndpoint
              tail.succ counterWidth (0 : Fin tail.succ) finalBit x hpath
              hcontrol hcompareBit hscratchABit hscratchBBit hcarry hwork hfinal
            have hcoreEq : selected.core =
                { x.core with compare := selected.core.compare } := by
              dsimp [selected]
              exact activeOddUGreaterSelectorStep_core_eq_setCompare
                tail.succ counterWidth (0 : Fin tail.succ) finalBit x hcontrol
            have huSelected :
                (uLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get selected = true := by
              have hselectedUOdd :
                  selected.core.u.val.testBit (0 : Nat) = true := by
                rw [hcoreEq]
                exact huValue
              simpa [uLowBit] using hselectedUOdd
            have hvSelected :
                (vLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get selected = true := by
              have hselectedVOdd :
                  selected.core.v.val.testBit (0 : Nat) = true := by
                rw [hcoreEq]
                exact hvValue
              simpa [vLowBit] using hselectedVOdd
            have hselectedPath :
                (pathBit tail.succ counterWidth).get selected = true := by
              dsimp [selected]
              have huWordValue : ((uValueWord tail.succ counterWidth).bit
                  (0 : Fin tail.succ)).get x = true := by
                simpa only [uLowBit] using huLow
              have hvWordValue : ((vValueWord tail.succ counterWidth).bit
                  (0 : Fin tail.succ)).get x = true := by
                simpa only [vLowBit] using hvLow
              rw [endpoint.path, hactiveBit, huWordValue, hvWordValue]
              rfl
            have hroute : routed = selectedOddDataThenBranchHistoryShiftStep
                tail.succ counterWidth historyIndex selected := by
              dsimp [routed, selected]
              exact activeBranchRoutedStep_eq_selected_odd_route
                tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
                historyIndex x huSelected hvSelected hselectedPath
                endpoint.control endpoint.scratchA endpoint.scratchB
                (endpoint.carryWork tempIndex)
            rw [hroute]
            calc
              observed.get (selectedOddDataThenBranchHistoryShiftStep
                  tail.succ counterWidth historyIndex selected) =
                  observed.get selected :=
                selectedOddDataThenBranchHistoryShiftStep_get_of_preserved
                  tail.succ counterWidth historyIndex observed hu hv hr hs
                  hworkObserved hscratchAObserved hscratchBObserved
                  hhistoryObserved selected endpoint.scratchA endpoint.scratchB
              _ = observed.get x :=
                activeOddUGreaterSelectorStep_get_of_preserved
                  tail.succ counterWidth (0 : Fin tail.succ) finalBit observed
                  hpathObserved hcontrolObserved hcompareObserved hv
                  hworkObserved x hcontrol
  calc
    observed.get (activeBranchBodyStep tail.succ counterWidth
        (0 : Fin tail.succ) finalBit tempIndex historyIndex x) =
        observed.get routed :=
      activeBranchBodyStep_get_of_cleanup_targets_ne
        tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
        historyIndex observed hpathObserved hcompareObserved
        hscratchAObserved hscratchBObserved x
    _ = observed.get x := hrouted

/-- The temporary masked-route control is clean after every complete active
body.  Even routes never select it; odd routes set it only around the
`vLe` arithmetic and erase it before branch-history staging. -/
theorem activeBranchBody_control_cleanEndpoint
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ) :
    (controlBit tail.succ counterWidth).get
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x) = false := by
  let observed := controlBit tail.succ counterWidth
  let routed := activeBranchRoutedStep tail.succ counterWidth
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
  have hpathObserved :
      (pathBit tail.succ counterWidth).wire ≠ observed.wire := by
    dsimp [observed]
    exact pathBit_controlBit_wire_ne tail.succ counterWidth
  have hcompareObserved :
      (compareBit tail.succ counterWidth).wire ≠ observed.wire := by
    dsimp [observed]
    simpa [compareBit, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.compareBit tail.succ counterWidth)
        (sharedControlBit tail.succ counterWidth)
  have hscratchAObserved :
      (scratchABit tail.succ counterWidth).wire ≠ observed.wire := by
    dsimp [observed]
    simpa [scratchABit, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.scratchABit tail.succ counterWidth)
        (sharedControlBit tail.succ counterWidth)
  have hscratchBObserved :
      (scratchBBit tail.succ counterWidth).wire ≠ observed.wire := by
    dsimp [observed]
    simpa [scratchBBit, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.scratchBBit tail.succ counterWidth)
        (sharedControlBit tail.succ counterWidth)
  have hhistoryObserved :
      (historyBit tail.succ counterWidth historyIndex).wire ≠
        observed.wire := by
    dsimp [observed]
    simpa [historyBit, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.historyBit tail.succ counterWidth historyIndex)
        (sharedControlBit tail.succ counterWidth)
  have hu : ∀ bit,
      ((uValueWord tail.succ counterWidth).bit bit).wire ≠
        observed.wire := by
    intro bit
    dsimp [observed]
    simpa [uValueWord, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.uValueBit tail.succ counterWidth bit)
        (sharedControlBit tail.succ counterWidth)
  have hv : ∀ bit,
      ((vValueWord tail.succ counterWidth).bit bit).wire ≠
        observed.wire := by
    intro bit
    dsimp [observed]
    simpa [vValueWord, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.vValueBit tail.succ counterWidth bit)
        (sharedControlBit tail.succ counterWidth)
  have hr : ∀ bit,
      (rCoeffValueBit tail.succ counterWidth bit).wire ≠
        observed.wire := by
    intro bit
    dsimp [observed]
    simpa [rCoeffValueBit, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.rCoeffValueBit tail.succ counterWidth bit)
        (sharedControlBit tail.succ counterWidth)
  have hs : ∀ bit,
      (sCoeffValueBit tail.succ counterWidth bit).wire ≠
        observed.wire := by
    intro bit
    dsimp [observed]
    simpa [sCoeffValueBit, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.sCoeffValueBit tail.succ counterWidth bit)
        (sharedControlBit tail.succ counterWidth)
  have hworkObserved : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).wire ≠
        observed.wire := by
    intro bit
    dsimp [observed]
    exact (controlBit_coefficientCarryWorkBit_wire_ne
      tail.succ counterWidth bit).symm
  have hrouteControl : observed.get routed = false := by
    cases huValue : x.core.u.val.testBit (0 : Nat) with
    | false =>
        have huLow :
            (uLowBit tail.succ counterWidth
              (0 : Fin tail.succ)).get x = false := by
          simpa [uLowBit] using huValue
        have hpair :
            (((uValueWord tail.succ counterWidth).bit
                (0 : Fin tail.succ)).get x &&
              ((vValueWord tail.succ counterWidth).bit
                (0 : Fin tail.succ)).get x) = false := by
          rw [show ((uValueWord tail.succ counterWidth).bit
            (0 : Fin tail.succ)).get x = false by
              simpa only [uLowBit] using huLow]
          simp
        have hroute : routed = selectedBranchCodeThenHistoryThenShiftStep
            tail.succ counterWidth (0 : Fin tail.succ) tempIndex
              historyIndex x := by
          dsimp [routed]
          exact activeBranchRoutedStep_eq_selected_even_route_of_pair_false
            tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
            historyIndex x hactiveBit hpath hcontrol hcompareBit hscratchABit
            hscratchBBit hpair
        rw [hroute]
        calc
          observed.get (selectedBranchCodeThenHistoryThenShiftStep
              tail.succ counterWidth (0 : Fin tail.succ) tempIndex
                historyIndex x) = observed.get x :=
            selectedBranchCodeThenHistoryThenShiftStep_get_of_preserved
              tail.succ counterWidth (0 : Fin tail.succ) tempIndex
              historyIndex observed (hu (0 : Fin tail.succ))
              (hv (0 : Fin tail.succ)) (hworkObserved tempIndex)
              hscratchAObserved hscratchBObserved hhistoryObserved hu
              (by simpa only [sCoeffValueWord] using hs) hv
              (by simpa only [rCoeffValueWord] using hr) x
          _ = false := hcontrol
    | true =>
        cases hvValue : x.core.v.val.testBit (0 : Nat) with
        | false =>
            have hvLow :
                (vLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get x = false := by
              simpa [vLowBit] using hvValue
            have hpair :
                (((uValueWord tail.succ counterWidth).bit
                    (0 : Fin tail.succ)).get x &&
                  ((vValueWord tail.succ counterWidth).bit
                    (0 : Fin tail.succ)).get x) = false := by
              rw [show ((vValueWord tail.succ counterWidth).bit
                (0 : Fin tail.succ)).get x = false by
                  simpa only [vLowBit] using hvLow]
              simp
            have hroute : routed = selectedBranchCodeThenHistoryThenShiftStep
                tail.succ counterWidth (0 : Fin tail.succ) tempIndex
                  historyIndex x := by
              dsimp [routed]
              exact activeBranchRoutedStep_eq_selected_even_route_of_pair_false
                tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
                historyIndex x hactiveBit hpath hcontrol hcompareBit
                hscratchABit hscratchBBit hpair
            rw [hroute]
            calc
              observed.get (selectedBranchCodeThenHistoryThenShiftStep
                  tail.succ counterWidth (0 : Fin tail.succ) tempIndex
                    historyIndex x) = observed.get x :=
                selectedBranchCodeThenHistoryThenShiftStep_get_of_preserved
                  tail.succ counterWidth (0 : Fin tail.succ) tempIndex
                  historyIndex observed (hu (0 : Fin tail.succ))
                  (hv (0 : Fin tail.succ)) (hworkObserved tempIndex)
                  hscratchAObserved hscratchBObserved hhistoryObserved hu
                  (by simpa only [sCoeffValueWord] using hs) hv
                  (by simpa only [rCoeffValueWord] using hr) x
              _ = false := hcontrol
        | true =>
            let selected := activeOddUGreaterSelectorStep tail.succ
              counterWidth (0 : Fin tail.succ) finalBit x
            have huLow :
                (uLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get x = true := by
              simpa [uLowBit] using huValue
            have hvLow :
                (vLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get x = true := by
              simpa [vLowBit] using hvValue
            have endpoint := activeOddUGreaterSelectorStep_cleanEndpoint
              tail.succ counterWidth (0 : Fin tail.succ) finalBit x hpath
              hcontrol hcompareBit hscratchABit hscratchBBit hcarry hwork
              hfinal
            have hcoreEq : selected.core =
                { x.core with compare := selected.core.compare } := by
              dsimp [selected]
              exact activeOddUGreaterSelectorStep_core_eq_setCompare
                tail.succ counterWidth (0 : Fin tail.succ) finalBit x
                hcontrol
            have huSelected :
                (uLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get selected = true := by
              have hselectedUOdd :
                  selected.core.u.val.testBit (0 : Nat) = true := by
                rw [hcoreEq]
                exact huValue
              simpa [uLowBit] using hselectedUOdd
            have hvSelected :
                (vLowBit tail.succ counterWidth
                  (0 : Fin tail.succ)).get selected = true := by
              have hselectedVOdd :
                  selected.core.v.val.testBit (0 : Nat) = true := by
                rw [hcoreEq]
                exact hvValue
              simpa [vLowBit] using hselectedVOdd
            have hselectedPath :
                (pathBit tail.succ counterWidth).get selected = true := by
              dsimp [selected]
              have huWordValue : ((uValueWord tail.succ counterWidth).bit
                  (0 : Fin tail.succ)).get x = true := by
                simpa only [uLowBit] using huLow
              have hvWordValue : ((vValueWord tail.succ counterWidth).bit
                  (0 : Fin tail.succ)).get x = true := by
                simpa only [vLowBit] using hvLow
              rw [endpoint.path, hactiveBit, huWordValue, hvWordValue]
              rfl
            have hroute : routed = selectedOddDataThenBranchHistoryShiftStep
                tail.succ counterWidth historyIndex selected := by
              dsimp [routed, selected]
              exact activeBranchRoutedStep_eq_selected_odd_route
                tail.succ counterWidth (0 : Fin tail.succ) finalBit tempIndex
                historyIndex x huSelected hvSelected hselectedPath
                endpoint.control endpoint.scratchA endpoint.scratchB
                (endpoint.carryWork tempIndex)
            rw [hroute]
            calc
              observed.get (selectedOddDataThenBranchHistoryShiftStep
                  tail.succ counterWidth historyIndex selected) =
                  observed.get selected :=
                selectedOddDataThenBranchHistoryShiftStep_get_of_preserved
                  tail.succ counterWidth historyIndex observed hu hv hr hs
                  hworkObserved hscratchAObserved hscratchBObserved
                  hhistoryObserved selected endpoint.scratchA
                  endpoint.scratchB
              _ = false := endpoint.control
  calc
    observed.get (activeBranchBodyStep tail.succ counterWidth
        (0 : Fin tail.succ) finalBit tempIndex historyIndex x) =
        observed.get routed :=
      activeBranchBodyStep_get_of_cleanup_targets_ne tail.succ counterWidth
        (0 : Fin tail.succ) finalBit tempIndex historyIndex observed
        hpathObserved hcompareObserved hscratchAObserved hscratchBObserved x
    _ = false := hrouteControl

/-- A compact core observation outside the branch arithmetic and the selected
history cell is preserved by the complete active body.  Carrier-level
disjointness from shared routing and VBE work follows from the encoding. -/
theorem activeBranchBodyStep_get_coreBit_of_stable
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (coreBit : EncodedBit (registerEncoding tail.succ counterWidth))
    (hcompare : (RegisterBits.compareBit tail.succ counterWidth).wire ≠
      coreBit.wire)
    (hscratchA : (RegisterBits.scratchABit tail.succ counterWidth).wire ≠
      coreBit.wire)
    (hscratchB : (RegisterBits.scratchBBit tail.succ counterWidth).wire ≠
      coreBit.wire)
    (hhistory :
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).wire ≠
        coreBit.wire)
    (hu : ∀ bit,
      (RegisterBits.uValueBit tail.succ counterWidth bit).wire ≠
        coreBit.wire)
    (hv : ∀ bit,
      (RegisterBits.vValueBit tail.succ counterWidth bit).wire ≠
        coreBit.wire)
    (hr : ∀ bit,
      (RegisterBits.rCoeffValueBit tail.succ counterWidth bit).wire ≠
        coreBit.wire)
    (hs : ∀ bit,
      (RegisterBits.sCoeffValueBit tail.succ counterWidth bit).wire ≠
        coreBit.wire)
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hcompareClean : x.core.compare = false)
    (hscratchAClean : x.core.scratchA = false)
    (hscratchBClean : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ) :
    (liftCoreBit tail.succ counterWidth coreBit).get
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x) =
      (liftCoreBit tail.succ counterWidth coreBit).get x := by
  apply activeBranchBodyStep_get_of_stable tail counterWidth finalBit
    tempIndex historyIndex (liftCoreBit tail.succ counterWidth coreBit)
  · exact (liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
      coreBit (sharedPathBit tail.succ counterWidth)).symm
  · exact (liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
      coreBit (sharedControlBit tail.succ counterWidth)).symm
  · simpa [compareBit] using
      liftCoreBit_wire_ne tail.succ counterWidth hcompare
  · simpa [scratchABit] using
      liftCoreBit_wire_ne tail.succ counterWidth hscratchA
  · simpa [scratchBBit] using
      liftCoreBit_wire_ne tail.succ counterWidth hscratchB
  · simpa [historyBit] using
      liftCoreBit_wire_ne tail.succ counterWidth hhistory
  · intro bit
    simpa [uValueWord] using
      liftCoreBit_wire_ne tail.succ counterWidth (hu bit)
  · intro bit
    simpa [vValueWord] using
      liftCoreBit_wire_ne tail.succ counterWidth (hv bit)
  · intro bit
    simpa [rCoeffValueBit] using
      liftCoreBit_wire_ne tail.succ counterWidth (hr bit)
  · intro bit
    simpa [sCoeffValueBit] using
      liftCoreBit_wire_ne tail.succ counterWidth (hs bit)
  · intro bit
    exact (liftCoreBit_coefficientCarryWorkBit_wire_ne tail.succ
      counterWidth coreBit bit).symm
  · exact hactive
  · exact hpath
  · exact hcontrol
  · exact hcompareClean
  · exact hscratchAClean
  · exact hscratchBClean
  · exact hcarry
  · exact hwork
  · exact hfinal

set_option maxHeartbeats 2000000 in
-- Bitwise word extensionality instantiates eleven symbolic wire families.
/-- The active arithmetic body does not mutate the padding counter; only the
round handoff owns that word. -/
theorem activeBranchBodyStep_counter
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ) :
    (activeBranchBodyStep tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x).core.counter =
        x.core.counter := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa only [liftCoreBit_get, RegisterBits.counterBit_get,
    WireAddress.bitIndex_littleEndianWire] using
    activeBranchBodyStep_get_coreBit_of_stable tail counterWidth finalBit
      tempIndex historyIndex
      (RegisterBits.counterBit tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (RegisterBits.compare_counter_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (RegisterBits.scratchA_counter_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (RegisterBits.scratchB_counter_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))
      (RegisterBits.history_counter_wire_ne tail.succ counterWidth
        historyIndex (WireAddress.littleEndianWire bit))
      (fun uBit => by
        simpa [RegisterBits.uValueBit] using
          RegisterBits.u_counter_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire uBit)
            (WireAddress.littleEndianWire bit))
      (fun vBit => by
        simpa [RegisterBits.vValueBit] using
          RegisterBits.v_counter_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire vBit)
            (WireAddress.littleEndianWire bit))
      (fun rBit => by
        simpa [RegisterBits.rCoeffValueBit] using
          RegisterBits.rCoeff_counter_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire rBit)
            (WireAddress.littleEndianWire bit))
      (fun sBit => by
        simpa [RegisterBits.sCoeffValueBit] using
          RegisterBits.sCoeff_counter_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire sBit)
            (WireAddress.littleEndianWire bit))
      x hactive hpath hcontrol hcompare hscratchA hscratchB hcarry hwork
      hfinal

/-- An active body writes only its current route-history cell. -/
theorem activeBranchBodyStep_get_history_of_ne
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
    (historyIndex observedIndex : Fin (2 * tail.succ))
    (hne : historyIndex ≠ observedIndex)
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ) :
    (historyBit tail.succ counterWidth observedIndex).get
        (activeBranchBodyStep tail.succ counterWidth
          (0 : Fin tail.succ) finalBit tempIndex historyIndex x) =
      (historyBit tail.succ counterWidth observedIndex).get x := by
  simpa only [historyBit] using
    activeBranchBodyStep_get_coreBit_of_stable tail counterWidth finalBit
      tempIndex historyIndex
      (RegisterBits.historyBit tail.succ counterWidth observedIndex)
      (RegisterBits.compare_history_wire_ne tail.succ counterWidth
        observedIndex)
      (RegisterBits.scratchA_history_wire_ne tail.succ counterWidth
        observedIndex)
      (RegisterBits.scratchB_history_wire_ne tail.succ counterWidth
        observedIndex)
      (RegisterBits.history_history_wire_ne tail.succ counterWidth hne)
      (fun uBit => by
        simpa [RegisterBits.uValueBit] using
          RegisterBits.u_history_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire uBit) observedIndex)
      (fun vBit => by
        simpa [RegisterBits.vValueBit] using
          RegisterBits.v_history_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire vBit) observedIndex)
      (fun rBit => by
        simpa [RegisterBits.rCoeffValueBit] using
          RegisterBits.rCoeff_history_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire rBit) observedIndex)
      (fun sBit => by
        simpa [RegisterBits.sCoeffValueBit] using
          RegisterBits.sCoeff_history_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire sBit) observedIndex)
      x hactive hpath hcontrol hcompare hscratchA hscratchB hcarry hwork
      hfinal

set_option maxHeartbeats 2000000 in
-- Bitwise word extensionality instantiates eleven symbolic wire families.
/-- The active body preserves the public copy target bitwise. -/
theorem activeBranchBodyStep_target
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ) :
    (activeBranchBodyStep tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex x).target =
        x.target := by
  apply word_eq_of_testBit_eq
  intro bit
  let observed := targetValueBit tail.succ counterWidth bit
  simpa only [observed, targetValueBit_get] using
    activeBranchBodyStep_get_of_stable tail counterWidth finalBit tempIndex
      historyIndex observed
      (by
        simpa only [observed, targetValueBit, pathBit] using
          liftSharedBit_targetBit_wire_ne tail.succ counterWidth
          (sharedPathBit tail.succ counterWidth)
          (WireAddress.littleEndianWire bit))
      (by
        simpa only [observed, targetValueBit, controlBit] using
          liftSharedBit_targetBit_wire_ne tail.succ counterWidth
          (sharedControlBit tail.succ counterWidth)
          (WireAddress.littleEndianWire bit))
      (by
        simpa only [observed, targetValueBit, compareBit] using
          liftCoreBit_targetBit_wire_ne tail.succ counterWidth
          (RegisterBits.compareBit tail.succ counterWidth)
          (WireAddress.littleEndianWire bit))
      (by
        simpa only [observed, targetValueBit, scratchABit] using
          liftCoreBit_targetBit_wire_ne tail.succ counterWidth
          (RegisterBits.scratchABit tail.succ counterWidth)
          (WireAddress.littleEndianWire bit))
      (by
        simpa only [observed, targetValueBit, scratchBBit] using
          liftCoreBit_targetBit_wire_ne tail.succ counterWidth
          (RegisterBits.scratchBBit tail.succ counterWidth)
          (WireAddress.littleEndianWire bit))
      (by
        simpa only [observed, targetValueBit, historyBit] using
          liftCoreBit_targetBit_wire_ne tail.succ counterWidth
          (RegisterBits.historyBit tail.succ counterWidth historyIndex)
          (WireAddress.littleEndianWire bit))
      (fun uBit => by
        simpa only [observed, targetValueBit, uValueWord] using
          liftCoreBit_targetBit_wire_ne tail.succ counterWidth
          (RegisterBits.uValueBit tail.succ counterWidth uBit)
          (WireAddress.littleEndianWire bit))
      (fun vBit => by
        simpa only [observed, targetValueBit, vValueWord] using
          liftCoreBit_targetBit_wire_ne tail.succ counterWidth
          (RegisterBits.vValueBit tail.succ counterWidth vBit)
          (WireAddress.littleEndianWire bit))
      (fun rBit => by
        simpa only [observed, targetValueBit, rCoeffValueBit] using
          liftCoreBit_targetBit_wire_ne tail.succ counterWidth
          (RegisterBits.rCoeffValueBit tail.succ counterWidth rBit)
          (WireAddress.littleEndianWire bit))
      (fun sBit => by
        simpa only [observed, targetValueBit, sCoeffValueBit] using
          liftCoreBit_targetBit_wire_ne tail.succ counterWidth
          (RegisterBits.sCoeffValueBit tail.succ counterWidth sBit)
          (WireAddress.littleEndianWire bit))
      (fun workBit => by
        simpa only [observed, targetValueBit,
            coefficientCarryWorkBit] using
          liftSharedBit_targetBit_wire_ne tail.succ counterWidth
          (sharedCoefficientCarryWorkBit tail.succ counterWidth workBit)
          (WireAddress.littleEndianWire bit))
      x hactive hpath hcontrol hcompare hscratchA hscratchB hcarry hwork
      hfinal

set_option maxHeartbeats 2000000 in
-- Bitwise word extensionality instantiates eleven symbolic wire families.
/-- The active body preserves the logarithmic correction word borrowed only
by later counter correction. -/
theorem activeBranchBodyStep_correctionCounter
    (tail counterWidth : Nat) (finalBit tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : MK.Compact.Registers tail.succ counterWidth)
    (hactive : x.core.active = true)
    (hpath : (pathBit tail.succ counterWidth).get x = false)
    (hcontrol : (controlBit tail.succ counterWidth).get x = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ) :
    (activeBranchBodyStep tail.succ counterWidth
      (0 : Fin tail.succ) finalBit tempIndex historyIndex
        x).shared.correctionCounter = x.shared.correctionCounter := by
  apply word_eq_of_testBit_eq
  intro bit
  let observed := correctionCounterValueBit tail.succ counterWidth bit
  simpa only [observed, correctionCounterValueBit_get] using
    activeBranchBodyStep_get_of_stable tail counterWidth finalBit tempIndex
      historyIndex observed
      (by
        simpa only [observed, correctionCounterValueBit] using
          pathBit_correctionCounterBit_wire_ne tail.succ counterWidth
          (WireAddress.littleEndianWire bit))
      (by
        simpa only [observed, correctionCounterValueBit] using
          controlBit_correctionCounterBit_wire_ne tail.succ counterWidth
          (WireAddress.littleEndianWire bit))
      (by
        simpa only [observed, correctionCounterValueBit, compareBit,
            correctionCounterBit] using
          liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
          (RegisterBits.compareBit tail.succ counterWidth)
          (sharedCorrectionCounterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa only [observed, correctionCounterValueBit, scratchABit,
            correctionCounterBit] using
          liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
          (RegisterBits.scratchABit tail.succ counterWidth)
          (sharedCorrectionCounterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa only [observed, correctionCounterValueBit, scratchBBit,
            correctionCounterBit] using
          liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
          (RegisterBits.scratchBBit tail.succ counterWidth)
          (sharedCorrectionCounterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (by
        simpa only [observed, correctionCounterValueBit, historyBit,
            correctionCounterBit] using
          liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
          (RegisterBits.historyBit tail.succ counterWidth historyIndex)
          (sharedCorrectionCounterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (fun uBit => by
        simpa only [observed, correctionCounterValueBit, uValueWord,
            correctionCounterBit] using
          liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
          (RegisterBits.uValueBit tail.succ counterWidth uBit)
          (sharedCorrectionCounterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (fun vBit => by
        simpa only [observed, correctionCounterValueBit, vValueWord,
            correctionCounterBit] using
          liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
          (RegisterBits.vValueBit tail.succ counterWidth vBit)
          (sharedCorrectionCounterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (fun rBit => by
        simpa only [observed, correctionCounterValueBit, rCoeffValueBit,
            correctionCounterBit] using
          liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
          (RegisterBits.rCoeffValueBit tail.succ counterWidth rBit)
          (sharedCorrectionCounterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (fun sBit => by
        simpa only [observed, correctionCounterValueBit, sCoeffValueBit,
            correctionCounterBit] using
          liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
          (RegisterBits.sCoeffValueBit tail.succ counterWidth sBit)
          (sharedCorrectionCounterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
      (fun workBit => by
        simpa only [observed, correctionCounterValueBit] using
          (correctionCounterBit_coefficientCarryWorkBit_wire_ne
          tail.succ counterWidth (WireAddress.littleEndianWire bit)
            workBit).symm)
      x hactive hpath hcontrol hcompare hscratchA hscratchB hcarry hwork
      hfinal

/-- Symbolic four-way classification of the complete compact active body.
The proof splits only on the two low bits and the strict comparison; it does
not enumerate any fixed-width register value. -/
theorem activeBranchBody_routeCleanup_clean
    (tail counterWidth modulus kaliskiSteps paddingSteps : Nat)
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
    (hhistory : x.core.history.val.testBit
      (WireAddress.bitIndex historyIndex).val = false)
    (hcarry : (coefficientCarryInBit tail.succ counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit tail.succ counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = tail.succ)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters tail.succ counterWidth x.core
        kaliskiSteps paddingSteps))
    (arith : ModeControlledSemanticStepArithmeticCertificate tail counterWidth
      x.core) :
    RouteCleanupCleanEndpoint tail.succ counterWidth
      (activeBranchBodyStep tail.succ counterWidth
        (0 : Fin tail.succ) finalBit tempIndex historyIndex x) := by
  cases hu : x.core.u.val.testBit (0 : Nat) with
  | false =>
      exact activeBranchBody_uEven_routeCleanup_clean tail counterWidth
        modulus kaliskiSteps paddingSteps finalBit tempIndex historyIndex x
        hactive hpath hcontrol hcompare hscratchA hscratchB hhistory hwork hu
        hmodulusOdd hbezout
  | true =>
      cases hv : x.core.v.val.testBit (0 : Nat) with
      | false =>
          exact activeBranchBody_vEven_routeCleanup_clean tail counterWidth
            finalBit tempIndex historyIndex x hactive hpath hcontrol hvNonzero
            hu hv hcompare hscratchA hscratchB hhistory hwork arith
      | true =>
          by_cases hlt : x.core.v.val < x.core.u.val
          · exact activeBranchBody_uGreater_routeCleanup_clean tail
              counterWidth modulus kaliskiSteps paddingSteps finalBit tempIndex
              historyIndex x hactive hpath hcontrol hvNonzero hu hv hlt
              hcompare hscratchA hscratchB hhistory hcarry hwork hfinal
              hmodulusOdd hbezout arith
          · exact activeBranchBody_vLe_routeCleanup_clean tail counterWidth
              finalBit tempIndex historyIndex x hactive hpath hcontrol
              hvNonzero hu hv hlt hcompare hscratchA hscratchB hhistory hcarry
              hwork hfinal arith

/-! ## Complete compact round ledger -/

/-- Clear the nonterminated-active route latch left by
`terminationHandoffStep`.  This is the same physical CNOT used to create the
latch: after the handoff both its source and target equal the new active flag,
so a second application returns the shared path bit to zero. -/
def compactRoundPathResetGate (fieldTail counterWidth : Nat) :
    EncodedBit.GateSpec (MK.Compact.encoding fieldTail.succ counterWidth) :=
  MK.Compact.terminationRoutePrefixActivePathGate fieldTail counterWidth

/-- Folded action of the one-gate compact round path reset. -/
def compactRoundPathResetStep (fieldTail counterWidth : Nat) :
    MK.Compact.Registers fieldTail.succ counterWidth ->
      MK.Compact.Registers fieldTail.succ counterWidth :=
  (compactRoundPathResetGate fieldTail counterWidth).step

/-- When the handoff latch equals the current active flag, the reset clears
only that latch. -/
theorem compactRoundPathResetStep_clean
    (fieldTail counterWidth : Nat)
    (x : MK.Compact.Registers fieldTail.succ counterWidth)
    (hpath : x.shared.path = x.core.active) :
    compactRoundPathResetStep fieldTail counterWidth x =
      { x with shared := { x.shared with path := false } } := by
  unfold compactRoundPathResetStep compactRoundPathResetGate
  change EncodedBit.cnotStep
      (MK.Compact.activeVZeroActiveBit fieldTail counterWidth)
      (MK.Compact.pathBit fieldTail.succ counterWidth) x = _
  unfold EncodedBit.cnotStep
  cases hactive : x.core.active
  · simp only [MK.Compact.activeVZeroActiveBit_get, hactive,
      Bool.false_eq_true, ↓reduceIte]
    cases x with
    | mk core shared target =>
      cases shared with
      | mk coefficientAdder correctionCounter path control =>
        simp_all
  · simp only [MK.Compact.activeVZeroActiveBit_get, hactive, ↓reduceIte]
    rw [MK.Compact.terminationRoutePrefixPathBit_flip_eq_update, hpath,
      hactive]
    rfl

/-- Termination/counter handoff followed by restoration of the shared path
bit.  This is the clean input boundary consumed by the compact active body. -/
def compactRoundPreparedStep
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ (counterTail + 2) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 2) :=
  fun x => compactRoundPathResetStep fieldTail (counterTail + 2)
    (MK.Compact.terminationHandoffStep fieldTail counterTail hfit x)

/-- A nonterminated active input passes through the termination/counter
handoff unchanged once its temporary path latch has been reset. -/
theorem compactRoundPreparedStep_eq_self_of_active_nonzero
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (hcoeff : x.shared.coefficientAdder =
      cleanCoeffAdderWork fieldTail.succ)
    (hcorrection : x.shared.correctionCounter = 0)
    (hpath : x.shared.path = false) (hcontrol : x.shared.control = false)
    (hmode : x.core.active = decide (x.core.counter = 0))
    (hroom : x.core.counter.val + 1 < 2 ^ (counterTail + 2))
    (hactive : x.core.active = true) (hvNonzero : x.core.v ≠ 0) :
    compactRoundPreparedStep fieldTail counterTail hfit x = x := by
  unfold compactRoundPreparedStep
  rw [MK.Compact.terminationHandoffStep_cleanEndpoint
    fieldTail counterTail hfit x hcoeff hcorrection hpath hcontrol hmode hroom]
  rw [compactRoundPathResetStep_clean]
  · cases x with
    | mk core shared target =>
      cases core
      cases shared
      simp_all [MK.Compact.inactiveCounterSourceValue]
  · simp [hactive, hvNonzero]

/-- Full record endpoint of the compact round prefix.  The extra reset CNOT
removes the handoff's temporary route latch and changes no other field. -/
theorem compactRoundPreparedStep_cleanEndpoint
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (hcoeff : x.shared.coefficientAdder =
      cleanCoeffAdderWork fieldTail.succ)
    (hcorrection : x.shared.correctionCounter = 0)
    (hpath : x.shared.path = false) (hcontrol : x.shared.control = false)
    (hmode : x.core.active = decide (x.core.counter = 0))
    (hroom : x.core.counter.val + 1 < 2 ^ (counterTail + 2)) :
    compactRoundPreparedStep fieldTail counterTail hfit x =
      { x with
        core := { x.core with
          active := x.core.active && !decide (x.core.v = 0)
          counter := x.core.counter +
            MK.Compact.inactiveCounterSourceValue counterTail.succ
              (x.core.active && !decide (x.core.v = 0)) }
        shared := { x.shared with path := false, control := false } } := by
  unfold compactRoundPreparedStep
  rw [MK.Compact.terminationHandoffStep_cleanEndpoint
    fieldTail counterTail hfit x hcoeff hcorrection hpath hcontrol hmode hroom]
  rw [compactRoundPathResetStep_clean]
  · cases x
    rfl

/-- Exact native gate table for one complete compact fixed round.  The
termination handoff updates the active flag and padding counter, the single
CNOT clears its route latch, and the active body performs exactly one of the
four nonzero Montgomery--Kaliski branches. -/
def compactRoundGates
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ)) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ (counterTail + 2))) :=
  MK.Compact.terminationHandoffGates fieldTail counterTail hfit ++
    [compactRoundPathResetGate fieldTail (counterTail + 2)] ++
      MK.Compact.activeBranchBodyGates fieldTail.succ (counterTail + 2)
        (0 : Fin fieldTail.succ) (Fin.last fieldTail)
        (0 : Fin fieldTail.succ) historyIndex

/-- One complete compact round is disjoint from every caller-owned target
bit. -/
theorem compactRoundGates_bitDisjoint_target
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ))
    (targetIndex : Fin fieldTail.succ) :
    ∀ gate,
      gate ∈ compactRoundGates fieldTail counterTail hfit historyIndex →
        EncodedBit.GateSpec.bitDisjoint
          (MK.Compact.targetValueBit fieldTail.succ (counterTail + 2)
            targetIndex) gate := by
  intro gate hgate
  rw [compactRoundGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | hbody
  · rcases List.mem_append.mp hprefix with htermination | hreset
    · exact MK.Compact.terminationHandoffGates_bitDisjoint_target fieldTail
        counterTail hfit targetIndex gate htermination
    · have : gate = compactRoundPathResetGate fieldTail (counterTail + 2) := by
        simpa only [List.mem_cons, List.not_mem_nil, or_false] using hreset
      subst gate
      exact ⟨
        MK.Compact.liftCoreBit_targetValueBit_wire_ne fieldTail.succ
          (counterTail + 2)
          (RegisterBits.activeBit fieldTail.succ (counterTail + 2))
          targetIndex,
        MK.Compact.liftSharedBit_targetValueBit_wire_ne fieldTail.succ
          (counterTail + 2)
          (MK.Compact.sharedPathBit fieldTail.succ (counterTail + 2))
          targetIndex⟩
  · exact MK.Compact.activeBranchBodyGates_bitDisjoint_target
      fieldTail.succ (counterTail + 2) (0 : Fin fieldTail.succ)
      (Fin.last fieldTail) (0 : Fin fieldTail.succ) historyIndex targetIndex
      gate hbody

/-- Folded state action of one complete compact fixed round. -/
def compactRoundStep
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ)) :
    MK.Compact.Registers fieldTail.succ (counterTail + 2) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 2) :=
  EncodedBit.GateSpec.stepList
    (compactRoundGates fieldTail counterTail hfit historyIndex)

/-- Physical circuit compiled from the literal compact one-round gate table. -/
def compactRoundProgram
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ (counterTail + 2)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compactRoundGates fieldTail counterTail hfit historyIndex)

/-- The compiled compact round realizes its exact native gate-list action. -/
theorem compactRound_realizes
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ)) :
    UnitaryCircuit.Realizes
      (MK.Compact.encoding fieldTail.succ (counterTail + 2))
      (compactRoundProgram fieldTail counterTail hfit historyIndex)
      (compactRoundStep fieldTail counterTail hfit historyIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (compactRoundGates fieldTail counterTail hfit historyIndex)

/-- Expose the physical order of the compact round. -/
theorem compactRoundStep_eq_stages
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ))
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)) :
    compactRoundStep fieldTail counterTail hfit historyIndex x =
      MK.Compact.activeBranchBodyStep fieldTail.succ (counterTail + 2)
        (0 : Fin fieldTail.succ) (Fin.last fieldTail)
        (0 : Fin fieldTail.succ) historyIndex
        (compactRoundPreparedStep fieldTail counterTail hfit x) := by
  unfold compactRoundStep compactRoundGates compactRoundPreparedStep
    compactRoundPathResetStep
    MK.Compact.terminationHandoffStep MK.Compact.activeBranchBodyStep
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rfl

/-- Clean routing endpoint for a complete compact round whose source state is
still active and nonterminated.  The handoff is proved to be the identity,
then the four physical Montgomery--Kaliski branches are discharged by the
symbolic low-bit/comparison classification above. -/
theorem compactRound_activeNonzero_routeCleanup_clean
    (fieldTail counterTail modulus kaliskiSteps paddingSteps : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ))
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork fieldTail.succ)
    (hcorrection : x.shared.correctionCounter = 0)
    (hpath : x.shared.path = false) (hcontrol : x.shared.control = false)
    (hmode : x.core.active = decide (x.core.counter = 0))
    (hroom : x.core.counter.val + 1 < 2 ^ (counterTail + 2))
    (hactive : x.core.active = true) (hvNonzero : x.core.v.val ≠ 0)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hhistory : x.core.history.val.testBit
      (WireAddress.bitIndex historyIndex).val = false)
    (hmodulusOdd : modulus % 2 = 1)
    (hbezout : RoundState.BezoutInvariant modulus
      (RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
        kaliskiSteps paddingSteps))
    (arith : ModeControlledSemanticStepArithmeticCertificate fieldTail
      (counterTail + 2) x.core) :
    RouteCleanupCleanEndpoint fieldTail.succ (counterTail + 2)
      (compactRoundStep fieldTail counterTail hfit historyIndex x) := by
  have hvWord : x.core.v ≠ 0 := by
    intro hv
    apply hvNonzero
    simp [hv]
  have hpathBit : (pathBit fieldTail.succ (counterTail + 2)).get x = false := by
    simpa only [pathBit_get] using hpath
  have hcontrolBit :
      (controlBit fieldTail.succ (counterTail + 2)).get x = false := by
    simpa only [controlBit_get] using hcontrol
  have hcarry :
      (coefficientCarryInBit fieldTail.succ (counterTail + 2)).get x = false := by
    change x.shared.coefficientAdder.1 = false
    rw [hcoeff]
    rfl
  have hwork : ∀ bit,
      (coefficientCarryWorkBit fieldTail.succ (counterTail + 2) bit).get x =
        false := by
    intro bit
    change (BinaryLabelEncoding.finIdentityBit fieldTail.succ bit).get
      x.shared.coefficientAdder.2 = false
    rw [hcoeff]
    exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero
      fieldTail.succ bit
  have hfinal : (Fin.last fieldTail).val + 1 = fieldTail.succ := by
    simp
  rw [compactRoundStep_eq_stages,
    compactRoundPreparedStep_eq_self_of_active_nonzero fieldTail counterTail
      hfit x hcoeff hcorrection hpath hcontrol hmode hroom hactive hvWord]
  exact activeBranchBody_routeCleanup_clean fieldTail (counterTail + 2)
    modulus kaliskiSteps paddingSteps (Fin.last fieldTail)
    (0 : Fin fieldTail.succ) historyIndex x hactive hpathBit hcontrolBit
    hvNonzero hcompare hscratchA hscratchB hhistory hcarry hwork hfinal
    hmodulusOdd hbezout arith

/-- A complete compact physical round implements one source
Montgomery--Kaliski round while the source is active and nonterminated. -/
theorem compactRound_activeNonzero_sourceRound
    (fieldTail counterTail kaliskiSteps paddingSteps : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ))
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork fieldTail.succ)
    (hcorrection : x.shared.correctionCounter = 0)
    (hpath : x.shared.path = false) (hcontrol : x.shared.control = false)
    (hmode : x.core.active = decide (x.core.counter = 0))
    (hroom : x.core.counter.val + 1 < 2 ^ (counterTail + 2))
    (hactive : x.core.active = true) (hvNonzero : x.core.v.val ≠ 0)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (arith : ModeControlledSemanticStepArithmeticCertificate fieldTail
      (counterTail + 2) x.core) :
    RoundState.fromRegisters fieldTail.succ (counterTail + 2)
        (compactRoundStep fieldTail counterTail hfit historyIndex x).core
        (kaliskiSteps + 1) paddingSteps =
      RoundState.round
        (RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
          kaliskiSteps paddingSteps) := by
  have hvWord : x.core.v ≠ 0 := by
    intro hv
    apply hvNonzero
    simp [hv]
  have hpathBit :
      (pathBit fieldTail.succ (counterTail + 2)).get x = false := by
    simpa only [pathBit_get] using hpath
  have hcontrolBit :
      (controlBit fieldTail.succ (counterTail + 2)).get x = false := by
    simpa only [controlBit_get] using hcontrol
  have hcarry :
      (coefficientCarryInBit fieldTail.succ (counterTail + 2)).get x = false := by
    change x.shared.coefficientAdder.1 = false
    rw [hcoeff]
    rfl
  have hwork : ∀ bit,
      (coefficientCarryWorkBit fieldTail.succ (counterTail + 2) bit).get x =
        false := by
    intro bit
    change (BinaryLabelEncoding.finIdentityBit fieldTail.succ bit).get
      x.shared.coefficientAdder.2 = false
    rw [hcoeff]
    exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero
      fieldTail.succ bit
  have hfinal : (Fin.last fieldTail).val + 1 = fieldTail.succ := by
    simp
  rw [compactRoundStep_eq_stages,
    compactRoundPreparedStep_eq_self_of_active_nonzero fieldTail counterTail
      hfit x hcoeff hcorrection hpath hcontrol hmode hroom hactive hvWord]
  exact activeBranchBody_sourceRound fieldTail (counterTail + 2)
    kaliskiSteps paddingSteps (Fin.last fieldTail)
    (0 : Fin fieldTail.succ) historyIndex x hactive hpathBit hcontrolBit
    hvNonzero hcompare hscratchA hscratchB hcarry hwork hfinal arith

/-- A terminating or already inactive source performs only the compact
handoff update.  The arithmetic body and both cleanup suffixes are proved to
be exact no-ops on the resulting inactive clean state. -/
theorem compactRoundStep_eq_cleanHandoff_of_inactive
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ))
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork fieldTail.succ)
    (hcorrection : x.shared.correctionCounter = 0)
    (hpath : x.shared.path = false) (hcontrol : x.shared.control = false)
    (hmode : x.core.active = decide (x.core.counter = 0))
    (hroom : x.core.counter.val + 1 < 2 ^ (counterTail + 2))
    (hinactive : (x.core.active && !decide (x.core.v = 0)) = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hhistory : x.core.history.val.testBit
      (WireAddress.bitIndex historyIndex).val = false) :
    compactRoundStep fieldTail counterTail hfit historyIndex x =
      { x with
        core := { x.core with
          active := x.core.active && !decide (x.core.v = 0)
          counter := x.core.counter +
            MK.Compact.inactiveCounterSourceValue counterTail.succ
              (x.core.active && !decide (x.core.v = 0)) }
        shared := { x.shared with path := false, control := false } } := by
  rw [compactRoundStep_eq_stages,
    compactRoundPreparedStep_cleanEndpoint fieldTail counterTail hfit x
      hcoeff hcorrection hpath hcontrol hmode hroom]
  apply MK.Compact.activeBranchBodyStep_eq_self_of_inactive_clean
  · change (x.core.active && !decide (x.core.v = 0)) = false
    exact hinactive
  · rfl
  · rfl
  · change x.core.compare = false
    exact hcompare
  · change x.core.scratchA = false
    exact hscratchA
  · change x.core.scratchB = false
    exact hscratchB
  · change x.core.history.val.testBit
        (WireAddress.bitIndex historyIndex).val = false
    exact hhistory

/-- A terminating or already inactive compact physical round implements the
matching source padding round. -/
theorem compactRound_inactive_sourceRound
    (fieldTail counterTail kaliskiSteps paddingSteps : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ))
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork fieldTail.succ)
    (hcorrection : x.shared.correctionCounter = 0)
    (hpath : x.shared.path = false) (hcontrol : x.shared.control = false)
    (hmode : x.core.active = decide (x.core.counter = 0))
    (hroom : x.core.counter.val + 1 < 2 ^ (counterTail + 2))
    (hinactive : (x.core.active && !decide (x.core.v = 0)) = false)
    (hcompare : x.core.compare = false)
    (hscratchA : x.core.scratchA = false)
    (hscratchB : x.core.scratchB = false)
    (hhistory : x.core.history.val.testBit
      (WireAddress.bitIndex historyIndex).val = false) :
    RoundState.fromRegisters fieldTail.succ (counterTail + 2)
        (compactRoundStep fieldTail counterTail hfit historyIndex x).core
        kaliskiSteps (paddingSteps + 1) =
      RoundState.round
        (RoundState.fromRegisters fieldTail.succ (counterTail + 2) x.core
          kaliskiSteps paddingSteps) := by
  rw [compactRoundStep_eq_cleanHandoff_of_inactive fieldTail counterTail hfit
    historyIndex x hcoeff hcorrection hpath hcontrol hmode hroom hinactive
    hcompare hscratchA hscratchB hhistory]
  cases hactive : x.core.active <;>
      cases hzero : decide (x.core.v = 0) <;>
    simp_all [RoundState.fromRegisters, RoundState.round]

/-- Exact X coordinate of one compact fixed round. -/
theorem compactRoundGates_xMultiplicity_sum
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ)) :
    ((compactRoundGates fieldTail counterTail hfit historyIndex).map
      EncodedBit.GateSpec.xMultiplicity).sum =
        10 * fieldTail + 2 * counterTail + 30 := by
  simp only [compactRoundGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    MK.Compact.terminationHandoffGates_xMultiplicity_sum,
    MK.Compact.activeBranchBodyGates_xMultiplicity_sum,
    compactRoundPathResetGate,
    MK.Compact.terminationRoutePrefixActivePathGate,
    EncodedBit.GateSpec.xMultiplicity_cnot]
  omega

/-- Exact CNOT coordinate of one compact fixed round. -/
theorem compactRoundGates_cnotMultiplicity_sum
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ)) :
    ((compactRoundGates fieldTail counterTail hfit historyIndex).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * counterTail + 13 := by
  simp only [compactRoundGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    MK.Compact.terminationHandoffGates_cnotMultiplicity_sum,
    MK.Compact.activeBranchBodyGates_cnotMultiplicity_sum,
    compactRoundPathResetGate,
    MK.Compact.terminationRoutePrefixActivePathGate,
    EncodedBit.GateSpec.cnotMultiplicity_cnot]
  omega

/-- Exact Toffoli coordinate of one compact fixed round. -/
theorem compactRoundGates_toffoliMultiplicity_sum
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ)) :
    ((compactRoundGates fieldTail counterTail hfit historyIndex).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
        112 * fieldTail + 8 * counterTail + 95 := by
  simp only [compactRoundGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    MK.Compact.terminationHandoffGates_toffoliMultiplicity_sum,
    MK.Compact.activeBranchBodyGates_toffoliMultiplicity_sum,
    compactRoundPathResetGate,
    MK.Compact.terminationRoutePrefixActivePathGate,
    EncodedBit.GateSpec.toffoliMultiplicity_cnot, Nat.succ_sub_one]
  omega

/-- Exact primitive-gate length of one compact fixed round. -/
theorem compactRoundGates_length
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (historyIndex : Fin (2 * fieldTail.succ)) :
    (compactRoundGates fieldTail counterTail hfit historyIndex).length =
      122 * fieldTail + 12 * counterTail + 138 := by
  rw [EncodedBit.GateSpec.length_eq_multiplicity_sums,
    compactRoundGates_xMultiplicity_sum,
    compactRoundGates_cnotMultiplicity_sum,
    compactRoundGates_toffoliMultiplicity_sum]
  omega

/-! ## Static compact `2n` fold -/

/-- Increasing static schedule of all `2n` compact round indices. -/
def compactFoldRoundIndices (fieldTail : Nat) :
    List (Fin (2 * fieldTail.succ)) :=
  List.ofFn fun roundIndex : Fin (2 * fieldTail.succ) => roundIndex

@[simp] theorem compactFoldRoundIndices_length (fieldTail : Nat) :
    (compactFoldRoundIndices fieldTail).length = 2 * fieldTail.succ := by
  simp [compactFoldRoundIndices]
  omega

/-- Literal native gate table for the complete compact fixed-round fold. -/
def compactFoldGates
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ (counterTail + 2))) :=
  (compactFoldRoundIndices fieldTail).flatMap
    (compactRoundGates fieldTail counterTail hfit)

/-- The flattened fixed-round ledger is disjoint from every caller-owned
target bit. -/
theorem compactFoldGates_bitDisjoint_target
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (targetIndex : Fin fieldTail.succ) :
    ∀ gate, gate ∈ compactFoldGates fieldTail counterTail hfit →
      EncodedBit.GateSpec.bitDisjoint
        (MK.Compact.targetValueBit fieldTail.succ (counterTail + 2)
          targetIndex) gate := by
  intro gate hgate
  unfold compactFoldGates at hgate
  simp only [List.mem_flatMap] at hgate
  rcases hgate with ⟨historyIndex, _hindex, hgate⟩
  exact compactRoundGates_bitDisjoint_target fieldTail counterTail hfit
    historyIndex targetIndex gate hgate

/-- Direct circuit compiled from the full compact primitive ledger. -/
def compactFoldProgram
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ (counterTail + 2)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compactFoldGates fieldTail counterTail hfit)

/-- Folded action of the complete compact primitive ledger. -/
def compactFoldStep
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ (counterTail + 2) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 2) :=
  EncodedBit.GateSpec.stepList
    (compactFoldGates fieldTail counterTail hfit)

/-- The direct compact fold circuit realizes its literal gate-list action. -/
theorem compactFold_realizes
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    UnitaryCircuit.Realizes
      (MK.Compact.encoding fieldTail.succ (counterTail + 2))
      (compactFoldProgram fieldTail counterTail hfit)
      (compactFoldStep fieldTail counterTail hfit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (compactFoldGates fieldTail counterTail hfit)

private theorem flatMap_compactRoundGates_xMultiplicity_sum
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    forall roundIndices : List (Fin (2 * fieldTail.succ)),
      (((roundIndices.flatMap
          (compactRoundGates fieldTail counterTail hfit)).map
        EncodedBit.GateSpec.xMultiplicity).sum) =
        roundIndices.length * (10 * fieldTail + 2 * counterTail + 30)
  | [] => by simp
  | roundIndex :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons,
        compactRoundGates_xMultiplicity_sum fieldTail counterTail hfit
          roundIndex,
        flatMap_compactRoundGates_xMultiplicity_sum fieldTail counterTail
          hfit rest]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

private theorem flatMap_compactRoundGates_cnotMultiplicity_sum
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    forall roundIndices : List (Fin (2 * fieldTail.succ)),
      (((roundIndices.flatMap
          (compactRoundGates fieldTail counterTail hfit)).map
        EncodedBit.GateSpec.cnotMultiplicity).sum) =
        roundIndices.length * (2 * counterTail + 13)
  | [] => by simp
  | roundIndex :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons,
        compactRoundGates_cnotMultiplicity_sum fieldTail counterTail hfit
          roundIndex,
        flatMap_compactRoundGates_cnotMultiplicity_sum fieldTail counterTail
          hfit rest]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

private theorem flatMap_compactRoundGates_toffoliMultiplicity_sum
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    forall roundIndices : List (Fin (2 * fieldTail.succ)),
      (((roundIndices.flatMap
          (compactRoundGates fieldTail counterTail hfit)).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum) =
        roundIndices.length *
          (112 * fieldTail + 8 * counterTail + 95)
  | [] => by simp
  | roundIndex :: rest => by
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.length_cons,
        compactRoundGates_toffoliMultiplicity_sum fieldTail counterTail hfit
          roundIndex,
        flatMap_compactRoundGates_toffoliMultiplicity_sum fieldTail counterTail
          hfit rest]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

private theorem flatMap_compactRoundGates_length
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    forall roundIndices : List (Fin (2 * fieldTail.succ)),
      (roundIndices.flatMap
        (compactRoundGates fieldTail counterTail hfit)).length =
        roundIndices.length *
          (122 * fieldTail + 12 * counterTail + 138)
  | [] => by simp
  | roundIndex :: rest => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        compactRoundGates_length fieldTail counterTail hfit roundIndex,
        flatMap_compactRoundGates_length fieldTail counterTail hfit rest]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

/-- Exact X coordinate of the complete compact `2n` fold. -/
theorem compactFoldGates_xMultiplicity_sum
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    ((compactFoldGates fieldTail counterTail hfit).map
      EncodedBit.GateSpec.xMultiplicity).sum =
      2 * fieldTail.succ * (10 * fieldTail + 2 * counterTail + 30) := by
  simpa only [compactFoldGates, compactFoldRoundIndices_length] using
    flatMap_compactRoundGates_xMultiplicity_sum fieldTail counterTail hfit
      (compactFoldRoundIndices fieldTail)

/-- Exact CNOT coordinate of the complete compact `2n` fold. -/
theorem compactFoldGates_cnotMultiplicity_sum
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    ((compactFoldGates fieldTail counterTail hfit).map
      EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * fieldTail.succ * (2 * counterTail + 13) := by
  simpa only [compactFoldGates, compactFoldRoundIndices_length] using
    flatMap_compactRoundGates_cnotMultiplicity_sum fieldTail counterTail hfit
      (compactFoldRoundIndices fieldTail)

/-- Exact Toffoli coordinate of the complete compact `2n` fold. -/
theorem compactFoldGates_toffoliMultiplicity_sum
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    ((compactFoldGates fieldTail counterTail hfit).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * fieldTail.succ *
        (112 * fieldTail + 8 * counterTail + 95) := by
  simpa only [compactFoldGates, compactFoldRoundIndices_length] using
    flatMap_compactRoundGates_toffoliMultiplicity_sum
      fieldTail counterTail hfit (compactFoldRoundIndices fieldTail)

/-- Exact primitive-gate length of the complete compact `2n` fold. -/
theorem compactFoldGates_length
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    (compactFoldGates fieldTail counterTail hfit).length =
      2 * fieldTail.succ *
        (122 * fieldTail + 12 * counterTail + 138) := by
  simpa only [compactFoldGates, compactFoldRoundIndices_length] using
    flatMap_compactRoundGates_length fieldTail counterTail hfit
      (compactFoldRoundIndices fieldTail)

/-- The compiled fold has the exact X count of its literal ledger. -/
theorem compactFoldProgram_x_count
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
        (compactFoldProgram fieldTail counterTail hfit).eventCost =
      2 * fieldTail.succ *
        (10 * fieldTail + 2 * counterTail + 30) := by
  rw [compactFoldProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum,
    compactFoldGates_xMultiplicity_sum]

/-- The compiled fold has the exact CNOT count of its literal ledger. -/
theorem compactFoldProgram_cnot_count
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
        (compactFoldProgram fieldTail counterTail hfit).eventCost =
      2 * fieldTail.succ * (2 * counterTail + 13) := by
  rw [compactFoldProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    compactFoldGates_cnotMultiplicity_sum]

/-- The compiled fold has the exact Toffoli count of its literal ledger. -/
theorem compactFoldProgram_toffoli_count
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (compactFoldProgram fieldTail counterTail hfit).eventCost =
      2 * fieldTail.succ *
        (112 * fieldTail + 8 * counterTail + 95) := by
  rw [compactFoldProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    compactFoldGates_toffoliMultiplicity_sum]

private theorem depthEval_compactDepthOfEvents
    (assignment : Resource.Event (.quantum AlgorithmGate.model .empty) -> Nat) :
    forall events : List (Resource.Event (.quantum AlgorithmGate.model .empty)),
      DepthExpr.depthEval assignment
          (EncodedBit.GateSpec.depthOfEvents events) =
        (events.map assignment).sum
  | [] => rfl
  | event :: rest => by
      simp only [EncodedBit.GateSpec.depthOfEvents,
        DepthExpr.depthEval_seq, DepthExpr.depthEval_atom,
        List.map_cons, List.sum_cons,
        depthEval_compactDepthOfEvents assignment rest]

private theorem sum_map_one {Alpha : Type} :
    forall values : List Alpha, (values.map fun _ => 1).sum = values.length
  | [] => rfl
  | _ :: rest => by
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        sum_map_one rest]
      omega

/-- The compact fold's symbolic depth is derived from the same ordered
primitive event trace used by the resource ledger. -/
theorem compactFoldProgram_eventDepth
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    (compactFoldProgram fieldTail counterTail hfit).eventDepth =
      EncodedBit.GateSpec.depthOfEvents
        ((compactFoldGates fieldTail counterTail hfit).map
          (EncodedBit.GateSpec.event .empty)) := by
  exact EncodedBit.GateSpec.programList_eventDepth
    (QubitLayout.canonical _) .empty
    (compactFoldGates fieldTail counterTail hfit)

/-- With unit cost per native event, the exact compact fold depth equals the
literal sequential gate-table length. -/
theorem compactFoldProgram_unitDepth_eq
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    (compactFoldProgram fieldTail counterTail hfit).evaluatedEventDepth
        (fun _ => 1) =
      2 * fieldTail.succ *
        (122 * fieldTail + 12 * counterTail + 138) := by
  rw [UnitaryCircuit.evaluatedEventDepth, compactFoldProgram_eventDepth,
    depthEval_compactDepthOfEvents]
  change
    (((compactFoldGates fieldTail counterTail hfit).map
      (EncodedBit.GateSpec.event .empty)).map fun _ => 1).sum = _
  rw [sum_map_one, List.length_map,
    compactFoldGates_length fieldTail counterTail hfit]

/-- Literal reverse gate table for exact fold uncomputation. -/
def compactFoldReverseGates
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ (counterTail + 2))) :=
  (compactFoldGates fieldTail counterTail hfit).reverse

/-- Circuit compiled from the reverse compact fold gate table. -/
def compactFoldReverseProgram
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (MK.Compact.encoding fieldTail.succ (counterTail + 2)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (compactFoldReverseGates fieldTail counterTail hfit)

/-- Folded action of the reverse compact ledger. -/
def compactFoldReverseStep
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    MK.Compact.Registers fieldTail.succ (counterTail + 2) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 2) :=
  EncodedBit.GateSpec.stepList
    (compactFoldReverseGates fieldTail counterTail hfit)

/-- The reverse compact fold is also realized by its literal gate table. -/
theorem compactFoldReverse_realizes
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    UnitaryCircuit.Realizes
      (MK.Compact.encoding fieldTail.succ (counterTail + 2))
      (compactFoldReverseProgram fieldTail counterTail hfit)
      (compactFoldReverseStep fieldTail counterTail hfit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (compactFoldReverseGates fieldTail counterTail hfit)

/-- Reversing the full literal fold restores every compact register. -/
theorem compactFoldReverseStep_after_compactFoldStep
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)) :
    compactFoldReverseStep fieldTail counterTail hfit
      (compactFoldStep fieldTail counterTail hfit x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (compactFoldGates fieldTail counterTail hfit) x

/-! ### Prefix schedule for source-state induction -/

/-- Named semantic schedule corresponding pointwise to the static round
indices in `compactFoldGates`. -/
def compactFoldSteps
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    List (MK.Compact.Registers fieldTail.succ (counterTail + 2) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 2)) :=
  List.ofFn fun roundIndex : Fin (2 * fieldTail.succ) =>
    compactRoundStep fieldTail counterTail hfit roundIndex

@[simp] theorem compactFoldSteps_length
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    (compactFoldSteps fieldTail counterTail hfit).length =
      2 * fieldTail.succ := by
  simp [compactFoldSteps]
  omega

theorem compactFoldSteps_get
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (roundIndex : Fin (2 * fieldTail.succ)) :
    (compactFoldSteps fieldTail counterTail hfit).get
        ⟨roundIndex.val, by
          rw [compactFoldSteps_length]
          exact roundIndex.isLt⟩ =
      compactRoundStep fieldTail counterTail hfit roundIndex := by
  change
    (List.ofFn
      (fun roundIndex : Fin (2 * fieldTail.succ) =>
        compactRoundStep fieldTail counterTail hfit roundIndex)).get
        ⟨roundIndex.val, by simp; omega⟩ =
      compactRoundStep fieldTail counterTail hfit roundIndex
  rw [List.get_ofFn]
  congr 1

private theorem stepList_flatMap_compactRoundGates
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    forall (roundIndices : List (Fin (2 * fieldTail.succ)))
      (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)),
      EncodedBit.GateSpec.stepList
          (roundIndices.flatMap
            (compactRoundGates fieldTail counterTail hfit)) x =
        UnitaryCircuit.Realizes.stepList
          (roundIndices.map
            (compactRoundStep fieldTail counterTail hfit)) x
  | [], _ => rfl
  | roundIndex :: rest, x => by
      change
        EncodedBit.GateSpec.stepList
            (compactRoundGates fieldTail counterTail hfit roundIndex ++
              rest.flatMap
                (compactRoundGates fieldTail counterTail hfit)) x =
          UnitaryCircuit.Realizes.stepList
            (rest.map (compactRoundStep fieldTail counterTail hfit))
            (compactRoundStep fieldTail counterTail hfit roundIndex x)
      rw [EncodedBit.GateSpec.stepList_append]
      exact stepList_flatMap_compactRoundGates
        fieldTail counterTail hfit rest
          (compactRoundStep fieldTail counterTail hfit roundIndex x)

/-- The flattened primitive fold and its named round schedule have the same
state action. -/
theorem compactFoldStep_eq_stepSchedule
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)) :
    compactFoldStep fieldTail counterTail hfit x =
      UnitaryCircuit.Realizes.stepList
        (compactFoldSteps fieldTail counterTail hfit) x := by
  simpa only [compactFoldStep, compactFoldGates, compactFoldRoundIndices,
    compactFoldSteps, List.map_ofFn, Function.comp_def] using
    stepList_flatMap_compactRoundGates fieldTail counterTail hfit
      (List.ofFn fun roundIndex : Fin (2 * fieldTail.succ) => roundIndex) x

/-- Semantic action of a bounded prefix of the compact static schedule. -/
def compactFoldPrefix
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) (rounds : Nat) :
    MK.Compact.Registers fieldTail.succ (counterTail + 2) ->
      MK.Compact.Registers fieldTail.succ (counterTail + 2) :=
  UnitaryCircuit.Realizes.stepList
    ((compactFoldSteps fieldTail counterTail hfit).take rounds)

@[simp] theorem compactFoldPrefix_zero
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)) :
    compactFoldPrefix fieldTail counterTail hfit 0 x = x := by
  rfl

theorem compactFoldPrefix_succ
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ)
    (roundIndex : Fin (2 * fieldTail.succ))
    (x : MK.Compact.Registers fieldTail.succ (counterTail + 2)) :
    compactFoldPrefix fieldTail counterTail hfit (roundIndex.val + 1) x =
      compactRoundStep fieldTail counterTail hfit roundIndex
        (compactFoldPrefix fieldTail counterTail hfit roundIndex.val x) := by
  unfold compactFoldPrefix
  let schedule := compactFoldSteps fieldTail counterTail hfit
  have hlen : roundIndex.val < schedule.length := by
    rw [compactFoldSteps_length]
    exact roundIndex.isLt
  rw [UnitaryCircuit.Realizes.stepList_take_succ schedule roundIndex.val hlen]
  have hget :
      schedule.get ⟨roundIndex.val, hlen⟩ =
        compactRoundStep fieldTail counterTail hfit roundIndex := by
    simpa [schedule] using
      compactFoldSteps_get fieldTail counterTail hfit roundIndex
  rw [hget]

theorem compactFoldPrefix_full
    (fieldTail counterTail : Nat)
    (hfit : counterTail.succ <= fieldTail.succ) :
    compactFoldPrefix fieldTail counterTail hfit (2 * fieldTail.succ) =
      compactFoldStep fieldTail counterTail hfit := by
  funext x
  rw [compactFoldStep_eq_stepSchedule]
  unfold compactFoldPrefix
  rw [List.take_of_length_le]
  rw [compactFoldSteps_length]

end CompactCertificate

end
end Circuit
end MK
end MAU.Inversion
end QuantumAlg

end
