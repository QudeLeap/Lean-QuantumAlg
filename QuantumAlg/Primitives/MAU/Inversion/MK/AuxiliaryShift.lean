/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Primitives.MAU.Inversion.MK.Conditions

/-!
# Auxiliary branch shifts

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

/-! ## Coefficient-work-lifted even branch-code staging -/

/-- Lifted semantic step for the `uEven` branch-code staging over the attached
comparison-work register. -/
def liftedUEvenBranchCodeToScratchStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x => (uEvenBranchCodeToScratchStep n counterWidth bit x.1, x.2)

/-- Actual circuit for the lifted `uEven` branch-code staging slice. -/
def liftedUEvenBranchCodeToScratchProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (uEvenBranchCodeToScratchProgram n counterWidth bit)

/-- The lifted `uEven` circuit realizes the product action. -/
theorem liftedUEvenBranchCodeToScratch_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes
      (registersWithComparisonWorkEncoding n counterWidth)
      (liftedUEvenBranchCodeToScratchProgram n counterWidth bit)
      (liftedUEvenBranchCodeToScratchStep n counterWidth bit) :=
  UnitaryCircuit.Realizes.onBinaryPrefix
    (right := comparisonWorkEncoding n)
    (uEvenBranchCodeToScratch_realizes n counterWidth bit)

/-- The lifted `uEven` branch-code staging preserves the active flag. -/
theorem liftedUEvenBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth bit x) =
      (liftedActiveBit n counterWidth).get x := by
  simpa [liftedActiveBit, liftedUEvenBranchCodeToScratchStep,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit] using
    uEvenBranchCodeToScratchStep_get_active n counterWidth bit x.1

/-- On clean lifted compare, the lifted `uEven` branch-code staging restores
compare. -/
theorem liftedUEvenBranchCodeToScratchStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedCompareBit n counterWidth).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth bit x) =
      false := by
  change (RegisterBits.compareBit n counterWidth).get
        (uEvenBranchCodeToScratchStep n counterWidth bit x.1) = false
  exact uEvenBranchCodeToScratchStep_get_compare_clean
    n counterWidth bit x.1 (by
      simpa [liftedCompareBit, liftRegisterBitToComparisonWork,
        BinaryLabelEncoding.prodLeftBit] using hcompare)

/-- On clean lifted compare, the lifted `uEven` branch-code staging toggles
scratchA exactly under the active `uEven` condition. -/
theorem liftedUEvenBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedScratchABit n counterWidth).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth bit x) =
      ((liftedScratchABit n counterWidth).get x ^^
        ((liftedActiveBit n counterWidth).get x &&
          !(liftedUBit n counterWidth bit).get x)) := by
  simpa [liftedScratchABit, liftedActiveBit, liftedUBit,
    liftedCompareBit, liftedUEvenBranchCodeToScratchStep,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit] using
    uEvenBranchCodeToScratchStep_get_scratchA_clean n counterWidth bit x.1
      (by simpa [liftedCompareBit, liftRegisterBitToComparisonWork,
        BinaryLabelEncoding.prodLeftBit] using hcompare)

/-- The lifted `uEven` branch-code staging preserves each `u` word bit. -/
theorem liftedUEvenBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedUWord n counterWidth).bit targetBit).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      ((liftedUWord n counterWidth).bit targetBit).get x := by
  change (RegisterBits.uValueBit n counterWidth targetBit).get
        (uEvenBranchCodeToScratchStep n counterWidth selectorBit x.1) =
      (RegisterBits.uValueBit n counterWidth targetBit).get x.1
  exact uEvenBranchCodeToScratchStep_get_uWordBit n counterWidth selectorBit
    targetBit x.1

/-- The lifted `uEven` branch-code staging preserves each `v` word bit. -/
theorem liftedUEvenBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit targetBit).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      ((liftedVWord n counterWidth).bit targetBit).get x := by
  change (RegisterBits.vValueBit n counterWidth targetBit).get
        (uEvenBranchCodeToScratchStep n counterWidth selectorBit x.1) =
      (RegisterBits.vValueBit n counterWidth targetBit).get x.1
  exact uEvenBranchCodeToScratchStep_get_vWordBit n counterWidth selectorBit
    targetBit x.1

/-- The lifted `uEven` branch-code staging preserves each `s` coefficient
value bit. -/
theorem liftedUEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x := by
  change (RegisterBits.sCoeffValueBit n counterWidth targetBit).get
        (uEvenBranchCodeToScratchStep n counterWidth selectorBit x.1) =
      (RegisterBits.sCoeffValueBit n counterWidth targetBit).get x.1
  exact uEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth selectorBit targetBit x.1

/-- The lifted `uEven` branch-code staging preserves each `r` coefficient
value bit. -/
theorem liftedUEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x := by
  change (RegisterBits.rCoeffValueBit n counterWidth targetBit).get
        (uEvenBranchCodeToScratchStep n counterWidth selectorBit x.1) =
      (RegisterBits.rCoeffValueBit n counterWidth targetBit).get x.1
  exact uEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth selectorBit targetBit x.1

/-- Lifted semantic step for the `vEven` branch-code staging over the attached
comparison-work register. -/
def liftedVEvenBranchCodeToScratchStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x => (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x.1,
    x.2)

/-- Actual circuit for the lifted `vEven` branch-code staging slice. -/
def liftedVEvenBranchCodeToScratchProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (vEvenBranchCodeToScratchProgram n counterWidth uIndex vIndex)

/-- The lifted `vEven` circuit realizes the product action. -/
theorem liftedVEvenBranchCodeToScratch_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit.Realizes
      (registersWithComparisonWorkEncoding n counterWidth)
      (liftedVEvenBranchCodeToScratchProgram n counterWidth uIndex vIndex)
      (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex) :=
  UnitaryCircuit.Realizes.onBinaryPrefix
    (right := comparisonWorkEncoding n)
    (vEvenBranchCodeToScratch_realizes n counterWidth uIndex vIndex)

/-- The lifted `vEven` branch-code staging preserves the active flag. -/
theorem liftedVEvenBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (liftedActiveBit n counterWidth).get x := by
  simpa [liftedActiveBit, liftedVEvenBranchCodeToScratchStep,
    liftRegisterBitToComparisonWork, BinaryLabelEncoding.prodLeftBit] using
    vEvenBranchCodeToScratchStep_get_active n counterWidth uIndex vIndex x.1

/-- On clean lifted compare, the lifted `vEven` branch-code staging restores
compare. -/
theorem liftedVEvenBranchCodeToScratchStep_get_compare_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedCompareBit n counterWidth).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      false := by
  change (RegisterBits.compareBit n counterWidth).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x.1) =
      false
  exact vEvenBranchCodeToScratchStep_get_compare_clean
    n counterWidth uIndex vIndex x.1 (by
      simpa [liftedCompareBit, liftRegisterBitToComparisonWork,
        BinaryLabelEncoding.prodLeftBit] using hcompare)

/-- On clean lifted compare, the lifted `vEven` branch-code staging preserves
scratchA because the `vEven` auxiliary code bit is false. -/
theorem liftedVEvenBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hcompare : (liftedCompareBit n counterWidth).get x = false) :
    (liftedScratchABit n counterWidth).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      (liftedScratchABit n counterWidth).get x := by
  simpa [liftedScratchABit, liftedCompareBit,
    liftedVEvenBranchCodeToScratchStep, liftRegisterBitToComparisonWork,
    BinaryLabelEncoding.prodLeftBit] using
    vEvenBranchCodeToScratchStep_get_scratchA_clean n counterWidth uIndex
    vIndex x.1
      (by simpa [liftedCompareBit, liftRegisterBitToComparisonWork,
        BinaryLabelEncoding.prodLeftBit] using hcompare)

/-- The lifted `vEven` branch-code staging preserves each `u` word bit. -/
theorem liftedVEvenBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (uIndex vIndex targetBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedUWord n counterWidth).bit targetBit).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      ((liftedUWord n counterWidth).bit targetBit).get x := by
  change (RegisterBits.uValueBit n counterWidth targetBit).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x.1) =
      (RegisterBits.uValueBit n counterWidth targetBit).get x.1
  exact vEvenBranchCodeToScratchStep_get_uWordBit n counterWidth uIndex
    vIndex targetBit x.1

/-- The lifted `vEven` branch-code staging preserves each `v` word bit. -/
theorem liftedVEvenBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (uIndex vIndex targetBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit targetBit).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      ((liftedVWord n counterWidth).bit targetBit).get x := by
  change (RegisterBits.vValueBit n counterWidth targetBit).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x.1) =
      (RegisterBits.vValueBit n counterWidth targetBit).get x.1
  exact vEvenBranchCodeToScratchStep_get_vWordBit n counterWidth uIndex
    vIndex targetBit x.1

/-- The lifted `vEven` branch-code staging preserves each `s` coefficient
value bit. -/
theorem liftedVEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (targetBit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x := by
  change (RegisterBits.sCoeffValueBit n counterWidth targetBit).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x.1) =
      (RegisterBits.sCoeffValueBit n counterWidth targetBit).get x.1
  exact vEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth uIndex vIndex targetBit x.1

/-- The lifted `vEven` branch-code staging preserves each `r` coefficient
value bit. -/
theorem liftedVEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (targetBit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x := by
  change (RegisterBits.rCoeffValueBit n counterWidth targetBit).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x.1) =
      (RegisterBits.rCoeffValueBit n counterWidth targetBit).get x.1
  exact vEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth uIndex vIndex targetBit x.1

/-- Coefficient-work-lifted `uEven` branch-code staging. -/
def coeffWorkUEvenBranchCodeToScratchStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (liftedUEvenBranchCodeToScratchStep n counterWidth bit)

/-- Actual circuit for coefficient-work-lifted `uEven` branch-code staging. -/
def coeffWorkUEvenBranchCodeToScratchProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (liftedUEvenBranchCodeToScratchProgram n counterWidth bit)

/-- The coefficient-work-lifted `uEven` circuit realizes its lifted action. -/
theorem coeffWorkUEvenBranchCodeToScratch_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUEvenBranchCodeToScratchProgram n counterWidth bit)
      (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit) :=
  liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (liftedUEvenBranchCodeToScratch_realizes n counterWidth bit)

/-- Coefficient-work-lifted `vEven` branch-code staging. -/
def coeffWorkVEvenBranchCodeToScratchStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex)

/-- Actual circuit for coefficient-work-lifted `vEven` branch-code staging. -/
def coeffWorkVEvenBranchCodeToScratchProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (liftedVEvenBranchCodeToScratchProgram n counterWidth uIndex vIndex)

/-- The coefficient-work-lifted `vEven` circuit realizes its lifted action. -/
theorem coeffWorkVEvenBranchCodeToScratch_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVEvenBranchCodeToScratchProgram n counterWidth uIndex vIndex)
      (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex) :=
  liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (liftedVEvenBranchCodeToScratch_realizes n counterWidth uIndex vIndex)

private def oddOddCompareBranchCodeToScratchStepCore
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding) :
    Data -> Data :=
  fun x =>
    EncodedBit.toffoliStep u v temp
      (EncodedBit.cnotStep scratchB scratchA
        (EncodedBit.toffoliStep active temp scratchA
          (EncodedBit.toffoliStep scratchA compare scratchB
            (EncodedBit.toffoliStep active temp scratchA
              (EncodedBit.toffoliStep u v temp x)))))

private theorem oddOddCompareBranchCodeToScratchStepCore_get_scratchB_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (htempU : temp.wire ≠ u.wire)
    (htempV : temp.wire ≠ v.wire)
    (htempActive : temp.wire ≠ active.wire)
    (htempCompare : temp.wire ≠ compare.wire)
    (htempScratchA : temp.wire ≠ scratchA.wire)
    (htempScratchB : temp.wire ≠ scratchB.wire)
    (hscratchAU : scratchA.wire ≠ u.wire)
    (hscratchAV : scratchA.wire ≠ v.wire)
    (hscratchATemp : scratchA.wire ≠ temp.wire)
    (hscratchAActive : scratchA.wire ≠ active.wire)
    (hscratchACompare : scratchA.wire ≠ compare.wire)
    (hscratchAScratchB : scratchA.wire ≠ scratchB.wire)
    (hscratchBU : scratchB.wire ≠ u.wire)
    (hscratchBV : scratchB.wire ≠ v.wire)
    (hscratchBTemp : scratchB.wire ≠ temp.wire)
    (hscratchBActive : scratchB.wire ≠ active.wire)
    (x : Data)
    (hscratchA : scratchA.get x = false)
    (hscratchB : scratchB.get x = false)
    (htemp : temp.get x = false) :
    scratchB.get
        (oddOddCompareBranchCodeToScratchStepCore
          u v temp active compare scratchA scratchB x) =
      (active.get x && u.get x && v.get x && compare.get x) := by
  cases hactive : active.get x <;>
    cases hu : u.get x <;>
    cases hv : v.get x <;>
    cases hcompare : compare.get x <;>
    simp [oddOddCompareBranchCodeToScratchStepCore,
      EncodedBit.toffoliStep, EncodedBit.cnotStep, hscratchA, hscratchB,
      htemp, hactive, hu, hv, hcompare, EncodedBit.get_flip_self,
      EncodedBit.get_flip_of_wire_ne, htempU, htempV, htempActive,
      htempCompare, htempScratchA, htempScratchB, hscratchAU, hscratchAV,
      hscratchATemp, hscratchAActive, hscratchACompare, hscratchAScratchB,
      hscratchBU, hscratchBV, hscratchBTemp, hscratchBActive]

private theorem oddOddCompareBranchCodeToScratchStepCore_get_scratchA_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (htempU : temp.wire ≠ u.wire)
    (htempV : temp.wire ≠ v.wire)
    (htempActive : temp.wire ≠ active.wire)
    (htempCompare : temp.wire ≠ compare.wire)
    (htempScratchA : temp.wire ≠ scratchA.wire)
    (htempScratchB : temp.wire ≠ scratchB.wire)
    (hscratchAU : scratchA.wire ≠ u.wire)
    (hscratchAV : scratchA.wire ≠ v.wire)
    (hscratchATemp : scratchA.wire ≠ temp.wire)
    (hscratchAActive : scratchA.wire ≠ active.wire)
    (hscratchACompare : scratchA.wire ≠ compare.wire)
    (hscratchAScratchB : scratchA.wire ≠ scratchB.wire)
    (hscratchBU : scratchB.wire ≠ u.wire)
    (hscratchBV : scratchB.wire ≠ v.wire)
    (hscratchBTemp : scratchB.wire ≠ temp.wire)
    (hscratchBActive : scratchB.wire ≠ active.wire)
    (hscratchBScratchA : scratchB.wire ≠ scratchA.wire)
    (x : Data)
    (hscratchA : scratchA.get x = false)
    (hscratchB : scratchB.get x = false)
    (htemp : temp.get x = false) :
    scratchA.get
        (oddOddCompareBranchCodeToScratchStepCore
          u v temp active compare scratchA scratchB x) =
      (active.get x && u.get x && v.get x && compare.get x) := by
  cases hactive : active.get x <;>
    cases hu : u.get x <;>
    cases hv : v.get x <;>
    cases hcompare : compare.get x <;>
    simp [oddOddCompareBranchCodeToScratchStepCore,
      EncodedBit.toffoliStep, EncodedBit.cnotStep, hscratchA, hscratchB,
      htemp, hactive, hu, hv, hcompare, EncodedBit.get_flip_self,
      EncodedBit.get_flip_of_wire_ne, htempU, htempV, htempActive,
      htempCompare, htempScratchA, htempScratchB, hscratchAU, hscratchAV,
      hscratchATemp, hscratchAActive, hscratchACompare, hscratchAScratchB,
      hscratchBU, hscratchBV, hscratchBTemp, hscratchBActive,
      hscratchBScratchA]

private theorem oddOddCompareBranchCodeToScratchStepCore_get_temp_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (htempU : temp.wire ≠ u.wire)
    (htempV : temp.wire ≠ v.wire)
    (htempActive : temp.wire ≠ active.wire)
    (htempCompare : temp.wire ≠ compare.wire)
    (htempScratchA : temp.wire ≠ scratchA.wire)
    (htempScratchB : temp.wire ≠ scratchB.wire)
    (hscratchAU : scratchA.wire ≠ u.wire)
    (hscratchAV : scratchA.wire ≠ v.wire)
    (hscratchATemp : scratchA.wire ≠ temp.wire)
    (hscratchAActive : scratchA.wire ≠ active.wire)
    (hscratchACompare : scratchA.wire ≠ compare.wire)
    (hscratchAScratchB : scratchA.wire ≠ scratchB.wire)
    (hscratchBU : scratchB.wire ≠ u.wire)
    (hscratchBV : scratchB.wire ≠ v.wire)
    (hscratchBTemp : scratchB.wire ≠ temp.wire)
    (hscratchBActive : scratchB.wire ≠ active.wire)
    (x : Data)
    (hscratchA : scratchA.get x = false)
    (hscratchB : scratchB.get x = false)
    (htemp : temp.get x = false) :
    temp.get
        (oddOddCompareBranchCodeToScratchStepCore
          u v temp active compare scratchA scratchB x) =
      false := by
  cases hactive : active.get x <;>
    cases hu : u.get x <;>
    cases hv : v.get x <;>
    cases hcompare : compare.get x <;>
    simp [oddOddCompareBranchCodeToScratchStepCore,
      EncodedBit.toffoliStep, EncodedBit.cnotStep, hscratchA, hscratchB,
      htemp, hactive, hu, hv, hcompare, EncodedBit.get_flip_self,
      EncodedBit.get_flip_of_wire_ne, htempU, htempV, htempActive,
      htempCompare, htempScratchA, htempScratchB, hscratchAU, hscratchAV,
      hscratchATemp, hscratchAActive, hscratchACompare, hscratchAScratchB,
      hscratchBU, hscratchBV, hscratchBTemp, hscratchBActive]

/-- Gate-level staging for the active odd-odd comparison branch-code term. -/
def coeffWorkOddOddCompareBranchCodeToScratchGates
    (n counterWidth : Nat) (uIndex vIndex tempIndex : Fin n) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  [ EncodedBit.GateSpec.toffoli
      (coeffAdderUBit n counterWidth uIndex)
      (coeffAdderVBit n counterWidth vIndex)
      (coeffAdderComparisonCarryBit n counterWidth tempIndex)
      (coeffAdderUBit_coeffAdderVBit_wire_ne n counterWidth uIndex vIndex)
      (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
        n counterWidth uIndex tempIndex)
      (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
        n counterWidth vIndex tempIndex)
  , EncodedBit.GateSpec.toffoli
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderComparisonCarryBit n counterWidth tempIndex)
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
        n counterWidth tempIndex)
      (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne n counterWidth)
      (Ne.symm (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
        n counterWidth tempIndex))
  , EncodedBit.GateSpec.toffoli
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderCompareBit n counterWidth)
      (coeffAdderScratchBBit n counterWidth)
      (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne n counterWidth)
      (coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne n counterWidth)
      (coeffAdderCompareBit_coeffAdderScratchBBit_wire_ne n counterWidth)
  , EncodedBit.GateSpec.toffoli
      (coeffAdderActiveBit n counterWidth)
      (coeffAdderComparisonCarryBit n counterWidth tempIndex)
      (coeffAdderScratchABit n counterWidth)
      (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
        n counterWidth tempIndex)
      (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne n counterWidth)
      (Ne.symm (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
        n counterWidth tempIndex))
  , EncodedBit.GateSpec.cnot
      (coeffAdderScratchBBit n counterWidth)
      (coeffAdderScratchABit n counterWidth)
      (Ne.symm (coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne
        n counterWidth))
  , EncodedBit.GateSpec.toffoli
      (coeffAdderUBit n counterWidth uIndex)
      (coeffAdderVBit n counterWidth vIndex)
      (coeffAdderComparisonCarryBit n counterWidth tempIndex)
      (coeffAdderUBit_coeffAdderVBit_wire_ne n counterWidth uIndex vIndex)
      (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
        n counterWidth uIndex tempIndex)
      (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
        n counterWidth vIndex tempIndex)
  ]

/-- Base-gate program for active odd-odd comparison branch-code staging. -/
def coeffWorkOddOddCompareBranchCodeToScratchProgram
    (n counterWidth : Nat) (uIndex vIndex tempIndex : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkOddOddCompareBranchCodeToScratchGates
      n counterWidth uIndex vIndex tempIndex)

/-- Semantic step for active odd-odd comparison branch-code staging. -/
def coeffWorkOddOddCompareBranchCodeToScratchStep
    (n counterWidth : Nat) (uIndex vIndex tempIndex : Fin n) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (coeffWorkOddOddCompareBranchCodeToScratchGates
      n counterWidth uIndex vIndex tempIndex)

/-- The active odd-odd comparison branch-code staging program is a concrete
encoded-bit base-gate realization. -/
theorem coeffWorkOddOddCompareBranchCodeToScratch_realizes
    (n counterWidth : Nat) (uIndex vIndex tempIndex : Fin n) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkOddOddCompareBranchCodeToScratchProgram
        n counterWidth uIndex vIndex tempIndex)
      (coeffWorkOddOddCompareBranchCodeToScratchStep
        n counterWidth uIndex vIndex tempIndex) := by
  change UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (coeffWorkOddOddCompareBranchCodeToScratchGates
          n counterWidth uIndex vIndex tempIndex))
      (EncodedBit.GateSpec.stepList
        (coeffWorkOddOddCompareBranchCodeToScratchGates
          n counterWidth uIndex vIndex tempIndex))
  exact EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (coeffWorkOddOddCompareBranchCodeToScratchGates
      n counterWidth uIndex vIndex tempIndex)

/-- On clean scratch and comparison-carry ancillas, odd-odd comparison
branch-code staging restores the selected comparison-carry work bit. -/
theorem coeffWorkOddOddCompareBranchCodeToScratchStep_get_comparisonCarry_clean
    (n counterWidth : Nat) (uIndex vIndex tempIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit n counterWidth tempIndex).get x =
        false) :
    (coeffAdderComparisonCarryBit n counterWidth tempIndex).get
        (coeffWorkOddOddCompareBranchCodeToScratchStep
          n counterWidth uIndex vIndex tempIndex x) =
      false := by
  change (coeffAdderComparisonCarryBit n counterWidth tempIndex).get
      (oddOddCompareBranchCodeToScratchStepCore
        (coeffAdderUBit n counterWidth uIndex)
        (coeffAdderVBit n counterWidth vIndex)
        (coeffAdderComparisonCarryBit n counterWidth tempIndex)
        (coeffAdderActiveBit n counterWidth)
        (coeffAdderCompareBit n counterWidth)
        (coeffAdderScratchABit n counterWidth)
        (coeffAdderScratchBBit n counterWidth) x) =
    false
  exact oddOddCompareBranchCodeToScratchStepCore_get_temp_clean
    (coeffAdderUBit n counterWidth uIndex)
    (coeffAdderVBit n counterWidth vIndex)
    (coeffAdderComparisonCarryBit n counterWidth tempIndex)
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderCompareBit n counterWidth)
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderScratchBBit n counterWidth)
    (Ne.symm (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth uIndex tempIndex))
    (Ne.symm (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth vIndex tempIndex))
    (Ne.symm (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderUBit_coeffAdderScratchABit_wire_ne
      n counterWidth uIndex))
    (Ne.symm (coeffAdderVBit_coeffAdderScratchABit_wire_ne
      n counterWidth vIndex))
    (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
      n counterWidth))
    (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne n counterWidth)
    (coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne n counterWidth)
    (Ne.symm (coeffAdderUBit_coeffAdderScratchBBit_wire_ne
      n counterWidth uIndex))
    (Ne.symm (coeffAdderVBit_coeffAdderScratchBBit_wire_ne
      n counterWidth vIndex))
    (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
      n counterWidth))
    x hscratchA hscratchB htemp

/-- On clean scratch and comparison-carry ancillas, odd-odd comparison
branch-code staging writes the comparison branch term to scratchA. -/
theorem coeffWorkOddOddCompareBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (uIndex vIndex tempIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit n counterWidth tempIndex).get x =
        false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkOddOddCompareBranchCodeToScratchStep
          n counterWidth uIndex vIndex tempIndex x) =
      ((coeffAdderActiveBit n counterWidth).get x &&
        (coeffAdderUBit n counterWidth uIndex).get x &&
        (coeffAdderVBit n counterWidth vIndex).get x &&
        (coeffAdderCompareBit n counterWidth).get x) := by
  change (coeffAdderScratchABit n counterWidth).get
      (oddOddCompareBranchCodeToScratchStepCore
        (coeffAdderUBit n counterWidth uIndex)
        (coeffAdderVBit n counterWidth vIndex)
        (coeffAdderComparisonCarryBit n counterWidth tempIndex)
        (coeffAdderActiveBit n counterWidth)
        (coeffAdderCompareBit n counterWidth)
        (coeffAdderScratchABit n counterWidth)
        (coeffAdderScratchBBit n counterWidth) x) =
    ((coeffAdderActiveBit n counterWidth).get x &&
      (coeffAdderUBit n counterWidth uIndex).get x &&
      (coeffAdderVBit n counterWidth vIndex).get x &&
      (coeffAdderCompareBit n counterWidth).get x)
  exact oddOddCompareBranchCodeToScratchStepCore_get_scratchA_clean
    (coeffAdderUBit n counterWidth uIndex)
    (coeffAdderVBit n counterWidth vIndex)
    (coeffAdderComparisonCarryBit n counterWidth tempIndex)
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderCompareBit n counterWidth)
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderScratchBBit n counterWidth)
    (Ne.symm (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth uIndex tempIndex))
    (Ne.symm (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth vIndex tempIndex))
    (Ne.symm (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderUBit_coeffAdderScratchABit_wire_ne
      n counterWidth uIndex))
    (Ne.symm (coeffAdderVBit_coeffAdderScratchABit_wire_ne
      n counterWidth vIndex))
    (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
      n counterWidth))
    (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne n counterWidth)
    (coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne n counterWidth)
    (Ne.symm (coeffAdderUBit_coeffAdderScratchBBit_wire_ne
      n counterWidth uIndex))
    (Ne.symm (coeffAdderVBit_coeffAdderScratchBBit_wire_ne
      n counterWidth vIndex))
    (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
      n counterWidth))
    (Ne.symm (coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne
      n counterWidth))
    x hscratchA hscratchB htemp

/-- On clean scratch and comparison-carry ancillas, odd-odd comparison
branch-code staging writes the comparison branch term to scratchB. -/
theorem coeffWorkOddOddCompareBranchCodeToScratchStep_get_scratchB_clean
    (n counterWidth : Nat) (uIndex vIndex tempIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit n counterWidth tempIndex).get x =
        false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkOddOddCompareBranchCodeToScratchStep
          n counterWidth uIndex vIndex tempIndex x) =
      ((coeffAdderActiveBit n counterWidth).get x &&
        (coeffAdderUBit n counterWidth uIndex).get x &&
        (coeffAdderVBit n counterWidth vIndex).get x &&
        (coeffAdderCompareBit n counterWidth).get x) := by
  change (coeffAdderScratchBBit n counterWidth).get
      (oddOddCompareBranchCodeToScratchStepCore
        (coeffAdderUBit n counterWidth uIndex)
        (coeffAdderVBit n counterWidth vIndex)
        (coeffAdderComparisonCarryBit n counterWidth tempIndex)
        (coeffAdderActiveBit n counterWidth)
        (coeffAdderCompareBit n counterWidth)
        (coeffAdderScratchABit n counterWidth)
        (coeffAdderScratchBBit n counterWidth) x) =
    ((coeffAdderActiveBit n counterWidth).get x &&
      (coeffAdderUBit n counterWidth uIndex).get x &&
      (coeffAdderVBit n counterWidth vIndex).get x &&
      (coeffAdderCompareBit n counterWidth).get x)
  exact oddOddCompareBranchCodeToScratchStepCore_get_scratchB_clean
    (coeffAdderUBit n counterWidth uIndex)
    (coeffAdderVBit n counterWidth vIndex)
    (coeffAdderComparisonCarryBit n counterWidth tempIndex)
    (coeffAdderActiveBit n counterWidth)
    (coeffAdderCompareBit n counterWidth)
    (coeffAdderScratchABit n counterWidth)
    (coeffAdderScratchBBit n counterWidth)
    (Ne.symm (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth uIndex tempIndex))
    (Ne.symm (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth vIndex tempIndex))
    (Ne.symm (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex))
    (Ne.symm (coeffAdderUBit_coeffAdderScratchABit_wire_ne
      n counterWidth uIndex))
    (Ne.symm (coeffAdderVBit_coeffAdderScratchABit_wire_ne
      n counterWidth vIndex))
    (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
      n counterWidth))
    (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne n counterWidth)
    (coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne n counterWidth)
    (Ne.symm (coeffAdderUBit_coeffAdderScratchBBit_wire_ne
      n counterWidth uIndex))
    (Ne.symm (coeffAdderVBit_coeffAdderScratchBBit_wire_ne
      n counterWidth vIndex))
    (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      n counterWidth tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
      n counterWidth))
    x hscratchA hscratchB htemp

private theorem oddOddCompareBranchCodeToScratchStepCore_get_of_targets_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB observed :
      EncodedBit encoding)
    (htempObserved : temp.wire ≠ observed.wire)
    (hscratchAObserved : scratchA.wire ≠ observed.wire)
    (hscratchBObserved : scratchB.wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (oddOddCompareBranchCodeToScratchStepCore
          u v temp active compare scratchA scratchB x) =
      observed.get x := by
  unfold oddOddCompareBranchCodeToScratchStepCore
  rw [EncodedBit.toffoliStep_get_of_target_ne u v temp observed
    htempObserved]
  rw [EncodedBit.cnotStep_get_of_target_ne scratchB scratchA observed
    hscratchAObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne active temp scratchA
    observed hscratchAObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne scratchA compare scratchB
    observed hscratchBObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne active temp scratchA
    observed hscratchAObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne u v temp observed
    htempObserved]

private theorem oddOddCompareBranchCodeToScratchStepCore_eq_self_of_active_false_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (hUTemp : u.wire ≠ temp.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (hTempActive : temp.wire ≠ active.wire)
    (hTempScratchA : temp.wire ≠ scratchA.wire)
    (hTempScratchB : temp.wire ≠ scratchB.wire)
    (x : Data)
    (hactive : active.get x = false)
    (hscratchA : scratchA.get x = false)
    (hscratchB : scratchB.get x = false) :
    oddOddCompareBranchCodeToScratchStepCore
        u v temp active compare scratchA scratchB x =
      x := by
  let y0 := EncodedBit.toffoliStep u v temp x
  have hactiveY0 : active.get y0 = false := by
    dsimp [y0]
    rw [EncodedBit.toffoliStep_get_of_target_ne u v temp active
      hTempActive]
    exact hactive
  have hscratchAY0 : scratchA.get y0 = false := by
    dsimp [y0]
    rw [EncodedBit.toffoliStep_get_of_target_ne u v temp scratchA
      hTempScratchA]
    exact hscratchA
  have hscratchBY0 : scratchB.get y0 = false := by
    dsimp [y0]
    rw [EncodedBit.toffoliStep_get_of_target_ne u v temp scratchB
      hTempScratchB]
    exact hscratchB
  change EncodedBit.toffoliStep u v temp
      (EncodedBit.cnotStep scratchB scratchA
        (EncodedBit.toffoliStep active temp scratchA
          (EncodedBit.toffoliStep scratchA compare scratchB
            (EncodedBit.toffoliStep active temp scratchA y0)))) =
    x
  have hactiveNoop :
      EncodedBit.toffoliStep active temp scratchA y0 = y0 := by
    simp [EncodedBit.toffoliStep, hactiveY0]
  have hcompareNoop :
      EncodedBit.toffoliStep scratchA compare scratchB y0 = y0 := by
    simp [EncodedBit.toffoliStep, hscratchAY0]
  have hcnotNoop : EncodedBit.cnotStep scratchB scratchA y0 = y0 := by
    simp [EncodedBit.cnotStep, hscratchBY0]
  rw [hactiveNoop, hcompareNoop, hactiveNoop, hcnotNoop]
  dsimp [y0]
  exact EncodedBit.toffoliStep_toffoliStep u v temp hUTemp hVTemp x

private theorem oddOddCompareBranchCodeToScratchStepCore_eq_self_of_compare_false_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (hUTemp : u.wire ≠ temp.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (_hTempActive : temp.wire ≠ active.wire)
    (hTempCompare : temp.wire ≠ compare.wire)
    (hTempScratchA : temp.wire ≠ scratchA.wire)
    (hTempScratchB : temp.wire ≠ scratchB.wire)
    (hActiveScratchA : active.wire ≠ scratchA.wire)
    (hCompareScratchA : compare.wire ≠ scratchA.wire)
    (_hCompareScratchB : compare.wire ≠ scratchB.wire)
    (hScratchAScratchB : scratchA.wire ≠ scratchB.wire)
    (x : Data)
    (hcompare : compare.get x = false)
    (_hscratchA : scratchA.get x = false)
    (hscratchB : scratchB.get x = false) :
    oddOddCompareBranchCodeToScratchStepCore
        u v temp active compare scratchA scratchB x = x := by
  let y0 := EncodedBit.toffoliStep u v temp x
  let y1 := EncodedBit.toffoliStep active temp scratchA y0
  have hcompareY1 : compare.get y1 = false := by
    dsimp [y1, y0]
    rw [EncodedBit.toffoliStep_get_of_target_ne active temp scratchA compare
      hCompareScratchA.symm,
      EncodedBit.toffoliStep_get_of_target_ne u v temp compare hTempCompare]
    exact hcompare
  have hscratchBY1 : scratchB.get y1 = false := by
    dsimp [y1, y0]
    rw [EncodedBit.toffoliStep_get_of_target_ne active temp scratchA scratchB
      hScratchAScratchB,
      EncodedBit.toffoliStep_get_of_target_ne u v temp scratchB
        hTempScratchB]
    exact hscratchB
  change EncodedBit.toffoliStep u v temp
      (EncodedBit.cnotStep scratchB scratchA
        (EncodedBit.toffoliStep active temp scratchA
          (EncodedBit.toffoliStep scratchA compare scratchB y1))) = x
  have hcompareNoop :
      EncodedBit.toffoliStep scratchA compare scratchB y1 = y1 := by
    simp [EncodedBit.toffoliStep, hcompareY1]
  rw [hcompareNoop]
  have hactiveCancel :
      EncodedBit.toffoliStep active temp scratchA y1 = y0 := by
    dsimp [y1]
    exact EncodedBit.toffoliStep_toffoliStep active temp scratchA
      hActiveScratchA hTempScratchA y0
  rw [hactiveCancel]
  have hscratchBY0 : scratchB.get y0 = false := by
    dsimp [y0]
    rw [EncodedBit.toffoliStep_get_of_target_ne u v temp scratchB
      hTempScratchB]
    exact hscratchB
  have hcnotNoop : EncodedBit.cnotStep scratchB scratchA y0 = y0 := by
    simp [EncodedBit.cnotStep, hscratchBY0]
  rw [hcnotNoop]
  dsimp [y0]
  exact EncodedBit.toffoliStep_toffoliStep u v temp hUTemp hVTemp x

private def notUBranchCodeToScratchAStepCore
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u active scratchA : EncodedBit encoding) : Data -> Data :=
  fun x => u.flip (EncodedBit.toffoliStep active u scratchA (u.flip x))

private theorem notUBranchCodeToScratchAStepCore_get_scratchA
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u active scratchA : EncodedBit encoding)
    (hUActive : u.wire ≠ active.wire)
    (hUScratchA : u.wire ≠ scratchA.wire)
    (x : Data) :
    scratchA.get
        (notUBranchCodeToScratchAStepCore u active scratchA x) =
      (scratchA.get x ^^ (active.get x && !u.get x)) := by
  unfold notUBranchCodeToScratchAStepCore
  rw [EncodedBit.get_flip_of_wire_ne u scratchA hUScratchA]
  rw [EncodedBit.toffoliStep_get_target]
  rw [EncodedBit.get_flip_of_wire_ne u active hUActive]
  rw [EncodedBit.get_flip_self]
  rw [EncodedBit.get_flip_of_wire_ne u scratchA hUScratchA]

private theorem notUBranchCodeToScratchAStepCore_get_u
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u active scratchA : EncodedBit encoding)
    (hUScratchA : u.wire ≠ scratchA.wire)
    (x : Data) :
    u.get (notUBranchCodeToScratchAStepCore u active scratchA x) =
      u.get x := by
  unfold notUBranchCodeToScratchAStepCore
  rw [EncodedBit.get_flip_self]
  rw [EncodedBit.toffoliStep_get_of_target_ne active u scratchA u
    (Ne.symm hUScratchA)]
  rw [EncodedBit.get_flip_self]
  cases u.get x <;> simp

private theorem notUBranchCodeToScratchAStepCore_get_of_targets_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u active scratchA observed : EncodedBit encoding)
    (hUObserved : u.wire ≠ observed.wire)
    (hScratchAObserved : scratchA.wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (notUBranchCodeToScratchAStepCore u active scratchA x) =
      observed.get x := by
  unfold notUBranchCodeToScratchAStepCore
  rw [EncodedBit.get_flip_of_wire_ne u observed hUObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne active u scratchA observed
    hScratchAObserved]
  rw [EncodedBit.get_flip_of_wire_ne u observed hUObserved]

private theorem notUBranchCodeToScratchAStepCore_eq_self_of_active_false
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u active scratchA : EncodedBit encoding)
    (hUActive : u.wire ≠ active.wire)
    (x : Data)
    (hactive : active.get x = false) :
    notUBranchCodeToScratchAStepCore u active scratchA x = x := by
  unfold notUBranchCodeToScratchAStepCore
  have hactiveFlip : active.get (u.flip x) = false := by
    rw [EncodedBit.get_flip_of_wire_ne u active hUActive]
    exact hactive
  have htoffoli :
      EncodedBit.toffoliStep active u scratchA (u.flip x) = u.flip x := by
    simp [EncodedBit.toffoliStep, hactiveFlip]
  rw [htoffoli]
  exact EncodedBit.flip_flip u x

private theorem notUBranchCodeToScratchAStepCore_eq_self_of_u_true
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u active scratchA : EncodedBit encoding)
    (x : Data) (hu : u.get x = true) :
    notUBranchCodeToScratchAStepCore u active scratchA x = x := by
  unfold notUBranchCodeToScratchAStepCore
  have huFlip : u.get (u.flip x) = false := by
    rw [EncodedBit.get_flip_self, hu]
    rfl
  have htoffoli :
      EncodedBit.toffoliStep active u scratchA (u.flip x) = u.flip x := by
    simp [EncodedBit.toffoliStep, huFlip]
  rw [htoffoli]
  exact EncodedBit.flip_flip u x

private def uNotVBranchCodeToScratchBStepCore
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active scratchB : EncodedBit encoding) : Data -> Data :=
  fun x =>
    v.flip
      (EncodedBit.toffoliStep u v temp
        (EncodedBit.toffoliStep active temp scratchB
          (EncodedBit.toffoliStep u v temp (v.flip x))))

private theorem uNotVBranchCodeToScratchBStepCore_get_temp_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active scratchB : EncodedBit encoding)
    (hUV : u.wire ≠ v.wire)
    (hUTemp : u.wire ≠ temp.wire)
    (hUScratchB : u.wire ≠ scratchB.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (_hVActive : v.wire ≠ active.wire)
    (hVScratchB : v.wire ≠ scratchB.wire)
    (_hTempActive : temp.wire ≠ active.wire)
    (hTempScratchB : temp.wire ≠ scratchB.wire)
    (x : Data)
    (htemp : temp.get x = false) :
    temp.get
        (uNotVBranchCodeToScratchBStepCore u v temp active scratchB x) =
      false := by
  cases hactive : active.get x <;>
    cases hu : u.get x <;>
    cases hv : v.get x <;>
    simp [uNotVBranchCodeToScratchBStepCore,
      EncodedBit.toffoliStep_get_target,
      EncodedBit.toffoliStep_get_of_target_ne, htemp, hu, hv,
      EncodedBit.get_flip_self, EncodedBit.get_flip_of_wire_ne,
      Ne.symm hUV, Ne.symm hUTemp, Ne.symm hUScratchB, hVTemp,
      Ne.symm hVTemp, Ne.symm hVScratchB, Ne.symm hTempScratchB]

private theorem uNotVBranchCodeToScratchBStepCore_get_scratchB_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active scratchB : EncodedBit encoding)
    (hUV : u.wire ≠ v.wire)
    (_hUTemp : u.wire ≠ temp.wire)
    (_hUScratchB : u.wire ≠ scratchB.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (hVActive : v.wire ≠ active.wire)
    (hVScratchB : v.wire ≠ scratchB.wire)
    (hTempActive : temp.wire ≠ active.wire)
    (hTempScratchB : temp.wire ≠ scratchB.wire)
    (x : Data)
    (htemp : temp.get x = false) :
    scratchB.get
        (uNotVBranchCodeToScratchBStepCore u v temp active scratchB x) =
      (scratchB.get x ^^ (active.get x && u.get x && !v.get x)) := by
  cases hactive : active.get x <;>
    cases hu : u.get x <;>
    cases hv : v.get x <;>
    cases hscratchB : scratchB.get x <;>
    simp [uNotVBranchCodeToScratchBStepCore,
      EncodedBit.toffoliStep_get_target,
      EncodedBit.toffoliStep_get_of_target_ne, htemp, hactive, hu, hv,
      hscratchB, EncodedBit.get_flip_self, EncodedBit.get_flip_of_wire_ne,
      Ne.symm hUV, hVTemp, hVActive, hVScratchB, hTempActive,
      hTempScratchB]

private theorem uNotVBranchCodeToScratchBStepCore_get_v
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active scratchB : EncodedBit encoding)
    (hVTemp : v.wire ≠ temp.wire)
    (hVScratchB : v.wire ≠ scratchB.wire)
    (x : Data) :
    v.get (uNotVBranchCodeToScratchBStepCore u v temp active scratchB x) =
      v.get x := by
  unfold uNotVBranchCodeToScratchBStepCore
  rw [EncodedBit.get_flip_self]
  rw [EncodedBit.toffoliStep_get_of_target_ne u v temp v
    (Ne.symm hVTemp)]
  rw [EncodedBit.toffoliStep_get_of_target_ne active temp scratchB v
    (Ne.symm hVScratchB)]
  rw [EncodedBit.toffoliStep_get_of_target_ne u v temp v
    (Ne.symm hVTemp)]
  rw [EncodedBit.get_flip_self]
  cases v.get x <;> simp

private theorem uNotVBranchCodeToScratchBStepCore_get_of_targets_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active scratchB observed : EncodedBit encoding)
    (hVObserved : v.wire ≠ observed.wire)
    (hTempObserved : temp.wire ≠ observed.wire)
    (hScratchBObserved : scratchB.wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (uNotVBranchCodeToScratchBStepCore u v temp active scratchB x) =
      observed.get x := by
  unfold uNotVBranchCodeToScratchBStepCore
  rw [EncodedBit.get_flip_of_wire_ne v observed hVObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne u v temp observed
    hTempObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne active temp scratchB observed
    hScratchBObserved]
  rw [EncodedBit.toffoliStep_get_of_target_ne u v temp observed
    hTempObserved]
  rw [EncodedBit.get_flip_of_wire_ne v observed hVObserved]

private theorem uNotVBranchCodeToScratchBStepCore_eq_self_of_active_false
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active scratchB : EncodedBit encoding)
    (hUTemp : u.wire ≠ temp.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (hVActive : v.wire ≠ active.wire)
    (hTempActive : temp.wire ≠ active.wire)
    (x : Data)
    (hactive : active.get x = false) :
    uNotVBranchCodeToScratchBStepCore u v temp active scratchB x = x := by
  unfold uNotVBranchCodeToScratchBStepCore
  let y0 := v.flip x
  let y1 := EncodedBit.toffoliStep u v temp y0
  have hactiveY1 : active.get y1 = false := by
    dsimp [y1]
    rw [EncodedBit.toffoliStep_get_of_target_ne u v temp active
      hTempActive]
    dsimp [y0]
    rw [EncodedBit.get_flip_of_wire_ne v active hVActive]
    exact hactive
  have hmiddle :
      EncodedBit.toffoliStep active temp scratchB y1 = y1 := by
    simp [EncodedBit.toffoliStep, hactiveY1]
  change v.flip
      (EncodedBit.toffoliStep u v temp
        (EncodedBit.toffoliStep active temp scratchB y1)) =
    x
  rw [hmiddle]
  dsimp [y1, y0]
  rw [EncodedBit.toffoliStep_toffoliStep u v temp hUTemp hVTemp]
  exact EncodedBit.flip_flip v x

private theorem uNotVBranchCodeToScratchBStepCore_eq_self_of_v_true_temp_false
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active scratchB : EncodedBit encoding)
    (hVTemp : v.wire ≠ temp.wire)
    (x : Data) (hv : v.get x = true) (htemp : temp.get x = false) :
    uNotVBranchCodeToScratchBStepCore u v temp active scratchB x = x := by
  unfold uNotVBranchCodeToScratchBStepCore
  let flipped := v.flip x
  have hvFlipped : v.get flipped = false := by
    dsimp [flipped]
    rw [EncodedBit.get_flip_self, hv]
    rfl
  have htempFlipped : temp.get flipped = false := by
    dsimp [flipped]
    rw [EncodedBit.get_flip_of_wire_ne v temp hVTemp]
    exact htemp
  have hfirst : EncodedBit.toffoliStep u v temp flipped = flipped := by
    simp [EncodedBit.toffoliStep, hvFlipped]
  rw [show v.flip x = flipped by rfl, hfirst]
  have hmiddle :
      EncodedBit.toffoliStep active temp scratchB flipped = flipped := by
    simp [EncodedBit.toffoliStep, htempFlipped]
  rw [hmiddle]
  have hlast : EncodedBit.toffoliStep u v temp flipped = flipped := by
    simp [EncodedBit.toffoliStep, hvFlipped]
  rw [hlast]
  exact EncodedBit.flip_flip v x

private def selectedBranchCodeToScratchStepCore
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding) :
    Data -> Data :=
  fun x =>
    uNotVBranchCodeToScratchBStepCore u v temp active scratchB
      (notUBranchCodeToScratchAStepCore u active scratchA
        (oddOddCompareBranchCodeToScratchStepCore
          u v temp active compare scratchA scratchB x))

private theorem selectedBranchCodeToScratchStepCore_get_of_targets_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB observed :
      EncodedBit encoding)
    (hUObserved : u.wire ≠ observed.wire)
    (hVObserved : v.wire ≠ observed.wire)
    (hTempObserved : temp.wire ≠ observed.wire)
    (hScratchAObserved : scratchA.wire ≠ observed.wire)
    (hScratchBObserved : scratchB.wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (selectedBranchCodeToScratchStepCore
          u v temp active compare scratchA scratchB x) =
      observed.get x := by
  unfold selectedBranchCodeToScratchStepCore
  rw [uNotVBranchCodeToScratchBStepCore_get_of_targets_ne
    u v temp active scratchB observed hVObserved hTempObserved
    hScratchBObserved]
  rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
    u active scratchA observed hUObserved hScratchAObserved]
  exact oddOddCompareBranchCodeToScratchStepCore_get_of_targets_ne
    u v temp active compare scratchA scratchB observed hTempObserved
    hScratchAObserved hScratchBObserved x

private theorem selectedBranchCodeToScratchStepCore_get_u
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (hUV : u.wire ≠ v.wire)
    (hUTemp : u.wire ≠ temp.wire)
    (hUScratchA : u.wire ≠ scratchA.wire)
    (hUScratchB : u.wire ≠ scratchB.wire)
    (x : Data) :
    u.get (selectedBranchCodeToScratchStepCore
      u v temp active compare scratchA scratchB x) =
      u.get x := by
  let y0 :=
    oddOddCompareBranchCodeToScratchStepCore
      u v temp active compare scratchA scratchB x
  let y1 := notUBranchCodeToScratchAStepCore u active scratchA y0
  change u.get (uNotVBranchCodeToScratchBStepCore u v temp active scratchB y1) =
    u.get x
  rw [uNotVBranchCodeToScratchBStepCore_get_of_targets_ne
    u v temp active scratchB u (Ne.symm hUV) (Ne.symm hUTemp)
      (Ne.symm hUScratchB)]
  dsimp [y1]
  rw [notUBranchCodeToScratchAStepCore_get_u u active scratchA hUScratchA]
  dsimp [y0]
  exact oddOddCompareBranchCodeToScratchStepCore_get_of_targets_ne
    u v temp active compare scratchA scratchB u (Ne.symm hUTemp)
    (Ne.symm hUScratchA) (Ne.symm hUScratchB) x

private theorem selectedBranchCodeToScratchStepCore_get_v
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (hUV : u.wire ≠ v.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (hVScratchA : v.wire ≠ scratchA.wire)
    (hVScratchB : v.wire ≠ scratchB.wire)
    (x : Data) :
    v.get (selectedBranchCodeToScratchStepCore
      u v temp active compare scratchA scratchB x) =
      v.get x := by
  let y0 :=
    oddOddCompareBranchCodeToScratchStepCore
      u v temp active compare scratchA scratchB x
  let y1 := notUBranchCodeToScratchAStepCore u active scratchA y0
  change v.get (uNotVBranchCodeToScratchBStepCore u v temp active scratchB y1) =
    v.get x
  rw [uNotVBranchCodeToScratchBStepCore_get_v
    u v temp active scratchB hVTemp hVScratchB]
  dsimp [y1]
  rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
    u active scratchA v hUV (Ne.symm hVScratchA)]
  dsimp [y0]
  exact oddOddCompareBranchCodeToScratchStepCore_get_of_targets_ne
    u v temp active compare scratchA scratchB v (Ne.symm hVTemp)
    (Ne.symm hVScratchA) (Ne.symm hVScratchB) x

private theorem selectedBranchCodeToScratchStepCore_get_temp_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (hUV : u.wire ≠ v.wire)
    (hUTemp : u.wire ≠ temp.wire)
    (_hUActive : u.wire ≠ active.wire)
    (_hUCompare : u.wire ≠ compare.wire)
    (hUScratchA : u.wire ≠ scratchA.wire)
    (hUScratchB : u.wire ≠ scratchB.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (hVActive : v.wire ≠ active.wire)
    (_hVCompare : v.wire ≠ compare.wire)
    (hVScratchA : v.wire ≠ scratchA.wire)
    (hVScratchB : v.wire ≠ scratchB.wire)
    (hTempActive : temp.wire ≠ active.wire)
    (hTempCompare : temp.wire ≠ compare.wire)
    (hTempScratchA : temp.wire ≠ scratchA.wire)
    (hTempScratchB : temp.wire ≠ scratchB.wire)
    (_hActiveCompare : active.wire ≠ compare.wire)
    (hActiveScratchA : active.wire ≠ scratchA.wire)
    (hActiveScratchB : active.wire ≠ scratchB.wire)
    (hCompareScratchA : compare.wire ≠ scratchA.wire)
    (_hCompareScratchB : compare.wire ≠ scratchB.wire)
    (hScratchAScratchB : scratchA.wire ≠ scratchB.wire)
    (x : Data)
    (hscratchA : scratchA.get x = false)
    (hscratchB : scratchB.get x = false)
    (htemp : temp.get x = false) :
    temp.get
        (selectedBranchCodeToScratchStepCore
          u v temp active compare scratchA scratchB x) =
      false := by
  let y0 :=
    oddOddCompareBranchCodeToScratchStepCore
      u v temp active compare scratchA scratchB x
  let y1 := notUBranchCodeToScratchAStepCore u active scratchA y0
  change temp.get
      (uNotVBranchCodeToScratchBStepCore u v temp active scratchB y1) =
    false
  have htemp0 : temp.get y0 = false := by
    dsimp [y0]
    exact oddOddCompareBranchCodeToScratchStepCore_get_temp_clean
      u v temp active compare scratchA scratchB
      (Ne.symm hUTemp) (Ne.symm hVTemp) hTempActive hTempCompare
      hTempScratchA hTempScratchB (Ne.symm hUScratchA)
      (Ne.symm hVScratchA) (Ne.symm hTempScratchA)
      (Ne.symm hActiveScratchA) (Ne.symm hCompareScratchA)
      hScratchAScratchB (Ne.symm hUScratchB) (Ne.symm hVScratchB)
      (Ne.symm hTempScratchB) (Ne.symm hActiveScratchB)
      x hscratchA hscratchB htemp
  have htemp1 : temp.get y1 = false := by
    dsimp [y1]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      u active scratchA temp hUTemp (Ne.symm hTempScratchA)]
    exact htemp0
  exact uNotVBranchCodeToScratchBStepCore_get_temp_clean
    u v temp active scratchB hUV hUTemp hUScratchB hVTemp hVActive
    hVScratchB hTempActive hTempScratchB y1 htemp1

private theorem selectedBranchCodeToScratchStepCore_get_scratchA_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (_hUV : u.wire ≠ v.wire)
    (hUTemp : u.wire ≠ temp.wire)
    (hUActive : u.wire ≠ active.wire)
    (_hUCompare : u.wire ≠ compare.wire)
    (hUScratchA : u.wire ≠ scratchA.wire)
    (hUScratchB : u.wire ≠ scratchB.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (_hVActive : v.wire ≠ active.wire)
    (_hVCompare : v.wire ≠ compare.wire)
    (hVScratchA : v.wire ≠ scratchA.wire)
    (hVScratchB : v.wire ≠ scratchB.wire)
    (hTempActive : temp.wire ≠ active.wire)
    (hTempCompare : temp.wire ≠ compare.wire)
    (hTempScratchA : temp.wire ≠ scratchA.wire)
    (hTempScratchB : temp.wire ≠ scratchB.wire)
    (_hActiveCompare : active.wire ≠ compare.wire)
    (hActiveScratchA : active.wire ≠ scratchA.wire)
    (hActiveScratchB : active.wire ≠ scratchB.wire)
    (hCompareScratchA : compare.wire ≠ scratchA.wire)
    (_hCompareScratchB : compare.wire ≠ scratchB.wire)
    (hScratchAScratchB : scratchA.wire ≠ scratchB.wire)
    (x : Data)
    (hscratchA : scratchA.get x = false)
    (hscratchB : scratchB.get x = false)
    (htemp : temp.get x = false) :
    scratchA.get
        (selectedBranchCodeToScratchStepCore
          u v temp active compare scratchA scratchB x) =
      (active.get x && (!u.get x || u.get x && v.get x && compare.get x)) := by
  let y0 :=
    oddOddCompareBranchCodeToScratchStepCore
      u v temp active compare scratchA scratchB x
  let y1 := notUBranchCodeToScratchAStepCore u active scratchA y0
  change scratchA.get
      (uNotVBranchCodeToScratchBStepCore u v temp active scratchB y1) =
    (active.get x && (!u.get x || u.get x && v.get x && compare.get x))
  rw [uNotVBranchCodeToScratchBStepCore_get_of_targets_ne
    u v temp active scratchB scratchA hVScratchA hTempScratchA
      (Ne.symm hScratchAScratchB)]
  dsimp [y1]
  rw [notUBranchCodeToScratchAStepCore_get_scratchA
    u active scratchA hUActive hUScratchA]
  have hscratchA0 :
      scratchA.get y0 =
        (active.get x && u.get x && v.get x && compare.get x) := by
    dsimp [y0]
    exact oddOddCompareBranchCodeToScratchStepCore_get_scratchA_clean
      u v temp active compare scratchA scratchB
      (Ne.symm hUTemp) (Ne.symm hVTemp) hTempActive hTempCompare
      hTempScratchA hTempScratchB (Ne.symm hUScratchA)
      (Ne.symm hVScratchA) (Ne.symm hTempScratchA)
      (Ne.symm hActiveScratchA) (Ne.symm hCompareScratchA)
      hScratchAScratchB (Ne.symm hUScratchB) (Ne.symm hVScratchB)
      (Ne.symm hTempScratchB) (Ne.symm hActiveScratchB)
      (Ne.symm hScratchAScratchB) x hscratchA hscratchB htemp
  have hactive0 : active.get y0 = active.get x := by
    dsimp [y0]
    exact oddOddCompareBranchCodeToScratchStepCore_get_of_targets_ne
      u v temp active compare scratchA scratchB active
      hTempActive (Ne.symm hActiveScratchA)
      (Ne.symm hActiveScratchB) x
  have hu0 : u.get y0 = u.get x := by
    dsimp [y0]
    exact oddOddCompareBranchCodeToScratchStepCore_get_of_targets_ne
      u v temp active compare scratchA scratchB u
      (Ne.symm hUTemp) (Ne.symm hUScratchA)
      (Ne.symm hUScratchB) x
  rw [hscratchA0, hactive0, hu0]
  cases active.get x <;>
    cases u.get x <;>
    cases v.get x <;>
    cases compare.get x <;>
    simp

private theorem selectedBranchCodeToScratchStepCore_get_scratchB_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (hUV : u.wire ≠ v.wire)
    (hUTemp : u.wire ≠ temp.wire)
    (hUActive : u.wire ≠ active.wire)
    (_hUCompare : u.wire ≠ compare.wire)
    (hUScratchA : u.wire ≠ scratchA.wire)
    (hUScratchB : u.wire ≠ scratchB.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (hVActive : v.wire ≠ active.wire)
    (_hVCompare : v.wire ≠ compare.wire)
    (hVScratchA : v.wire ≠ scratchA.wire)
    (hVScratchB : v.wire ≠ scratchB.wire)
    (hTempActive : temp.wire ≠ active.wire)
    (hTempCompare : temp.wire ≠ compare.wire)
    (hTempScratchA : temp.wire ≠ scratchA.wire)
    (hTempScratchB : temp.wire ≠ scratchB.wire)
    (_hActiveCompare : active.wire ≠ compare.wire)
    (hActiveScratchA : active.wire ≠ scratchA.wire)
    (hActiveScratchB : active.wire ≠ scratchB.wire)
    (hCompareScratchA : compare.wire ≠ scratchA.wire)
    (_hCompareScratchB : compare.wire ≠ scratchB.wire)
    (hScratchAScratchB : scratchA.wire ≠ scratchB.wire)
    (x : Data)
    (hscratchA : scratchA.get x = false)
    (hscratchB : scratchB.get x = false)
    (htemp : temp.get x = false) :
    scratchB.get
        (selectedBranchCodeToScratchStepCore
          u v temp active compare scratchA scratchB x) =
      (active.get x &&
        (u.get x && !v.get x || u.get x && v.get x && compare.get x)) := by
  let y0 :=
    oddOddCompareBranchCodeToScratchStepCore
      u v temp active compare scratchA scratchB x
  let y1 := notUBranchCodeToScratchAStepCore u active scratchA y0
  change scratchB.get
      (uNotVBranchCodeToScratchBStepCore u v temp active scratchB y1) =
    (active.get x &&
      (u.get x && !v.get x || u.get x && v.get x && compare.get x))
  have htemp0 : temp.get y0 = false := by
    dsimp [y0]
    exact oddOddCompareBranchCodeToScratchStepCore_get_temp_clean
      u v temp active compare scratchA scratchB
      (Ne.symm hUTemp) (Ne.symm hVTemp) hTempActive hTempCompare
      hTempScratchA hTempScratchB (Ne.symm hUScratchA)
      (Ne.symm hVScratchA) (Ne.symm hTempScratchA)
      (Ne.symm hActiveScratchA) (Ne.symm hCompareScratchA)
      hScratchAScratchB (Ne.symm hUScratchB) (Ne.symm hVScratchB)
      (Ne.symm hTempScratchB) (Ne.symm hActiveScratchB)
      x hscratchA hscratchB htemp
  have htemp1 : temp.get y1 = false := by
    dsimp [y1]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      u active scratchA temp hUTemp (Ne.symm hTempScratchA)]
    exact htemp0
  rw [uNotVBranchCodeToScratchBStepCore_get_scratchB_clean
    u v temp active scratchB hUV hUTemp hUScratchB hVTemp hVActive
      hVScratchB hTempActive hTempScratchB y1 htemp1]
  have hscratchB1 : scratchB.get y1 = scratchB.get y0 := by
    dsimp [y1]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      u active scratchA scratchB hUScratchB hScratchAScratchB]
  have hactive1 : active.get y1 = active.get y0 := by
    dsimp [y1]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      u active scratchA active hUActive (Ne.symm hActiveScratchA)]
  have hu1 : u.get y1 = u.get y0 := by
    dsimp [y1]
    rw [notUBranchCodeToScratchAStepCore_get_u u active scratchA
      hUScratchA]
  have hv1 : v.get y1 = v.get y0 := by
    dsimp [y1]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      u active scratchA v hUV (Ne.symm hVScratchA)]
  rw [hscratchB1, hactive1, hu1, hv1]
  have hscratchB0 :
      scratchB.get y0 =
        (active.get x && u.get x && v.get x && compare.get x) := by
    dsimp [y0]
    exact oddOddCompareBranchCodeToScratchStepCore_get_scratchB_clean
      u v temp active compare scratchA scratchB
      (Ne.symm hUTemp) (Ne.symm hVTemp) hTempActive hTempCompare
      hTempScratchA hTempScratchB (Ne.symm hUScratchA)
      (Ne.symm hVScratchA) (Ne.symm hTempScratchA)
      (Ne.symm hActiveScratchA) (Ne.symm hCompareScratchA)
      hScratchAScratchB (Ne.symm hUScratchB) (Ne.symm hVScratchB)
      (Ne.symm hTempScratchB) (Ne.symm hActiveScratchB)
      x hscratchA hscratchB htemp
  have hactive0 : active.get y0 = active.get x := by
    dsimp [y0]
    exact oddOddCompareBranchCodeToScratchStepCore_get_of_targets_ne
      u v temp active compare scratchA scratchB active
      hTempActive (Ne.symm hActiveScratchA)
      (Ne.symm hActiveScratchB) x
  have hu0 : u.get y0 = u.get x := by
    dsimp [y0]
    exact oddOddCompareBranchCodeToScratchStepCore_get_of_targets_ne
      u v temp active compare scratchA scratchB u
      (Ne.symm hUTemp) (Ne.symm hUScratchA)
      (Ne.symm hUScratchB) x
  have hv0 : v.get y0 = v.get x := by
    dsimp [y0]
    exact oddOddCompareBranchCodeToScratchStepCore_get_of_targets_ne
      u v temp active compare scratchA scratchB v
      (Ne.symm hVTemp) (Ne.symm hVScratchA)
      (Ne.symm hVScratchB) x
  rw [hscratchB0, hactive0, hu0, hv0]
  cases active.get x <;>
    cases u.get x <;>
    cases v.get x <;>
    cases compare.get x <;>
    simp

private theorem selectedBranchCodeToScratchStepCore_eq_self_of_active_false_clean
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active compare scratchA scratchB : EncodedBit encoding)
    (hUTemp : u.wire ≠ temp.wire)
    (hUActive : u.wire ≠ active.wire)
    (hVTemp : v.wire ≠ temp.wire)
    (hVActive : v.wire ≠ active.wire)
    (hTempActive : temp.wire ≠ active.wire)
    (hTempScratchA : temp.wire ≠ scratchA.wire)
    (hTempScratchB : temp.wire ≠ scratchB.wire)
    (x : Data)
    (hactive : active.get x = false)
    (hscratchA : scratchA.get x = false)
    (hscratchB : scratchB.get x = false) :
    selectedBranchCodeToScratchStepCore
        u v temp active compare scratchA scratchB x =
      x := by
  unfold selectedBranchCodeToScratchStepCore
  rw [oddOddCompareBranchCodeToScratchStepCore_eq_self_of_active_false_clean
    u v temp active compare scratchA scratchB hUTemp hVTemp hTempActive
    hTempScratchA hTempScratchB x hactive hscratchA hscratchB]
  rw [notUBranchCodeToScratchAStepCore_eq_self_of_active_false
    u active scratchA hUActive x hactive]
  exact uNotVBranchCodeToScratchBStepCore_eq_self_of_active_false
    u v temp active scratchB hUTemp hVTemp hVActive hTempActive x hactive

/-- Gate-level selected branch-code staging from the concrete low `u`, low
`v`, and comparison readouts into the active-guarded branch-code scratch
bits. -/
def coeffWorkSelectedBranchCodeToScratchGates
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)) :=
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  coeffWorkOddOddCompareBranchCodeToScratchGates
    tail.succ counterWidth low low tempIndex ++
  [ EncodedBit.GateSpec.x
      (coeffAdderUBit tail.succ counterWidth low)
  , EncodedBit.GateSpec.toffoli
      (coeffAdderActiveBit tail.succ counterWidth)
      (coeffAdderUBit tail.succ counterWidth low)
      (coeffAdderScratchABit tail.succ counterWidth)
      (coeffAdderActiveBit_coeffAdderUBit_wire_ne
        tail.succ counterWidth low)
      (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
        tail.succ counterWidth)
      (coeffAdderUBit_coeffAdderScratchABit_wire_ne
        tail.succ counterWidth low)
  , EncodedBit.GateSpec.x
      (coeffAdderUBit tail.succ counterWidth low)
  , EncodedBit.GateSpec.x
      (coeffAdderVBit tail.succ counterWidth low)
  , EncodedBit.GateSpec.toffoli
      (coeffAdderUBit tail.succ counterWidth low)
      (coeffAdderVBit tail.succ counterWidth low)
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
      (coeffAdderUBit_coeffAdderVBit_wire_ne
        tail.succ counterWidth low low)
      (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth low tempIndex)
      (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth low tempIndex)
  , EncodedBit.GateSpec.toffoli
      (coeffAdderActiveBit tail.succ counterWidth)
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
      (coeffAdderScratchBBit tail.succ counterWidth)
      (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth tempIndex)
      (coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
        tail.succ counterWidth)
      (Ne.symm (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth tempIndex))
  , EncodedBit.GateSpec.toffoli
      (coeffAdderUBit tail.succ counterWidth low)
      (coeffAdderVBit tail.succ counterWidth low)
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
      (coeffAdderUBit_coeffAdderVBit_wire_ne
        tail.succ counterWidth low low)
      (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth low tempIndex)
      (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth low tempIndex)
  , EncodedBit.GateSpec.x
      (coeffAdderVBit tail.succ counterWidth low)
  ]

/-- Base-gate program for active selected branch-code staging. -/
def coeffWorkSelectedBranchCodeToScratchProgram
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkSelectedBranchCodeToScratchGates
      tail counterWidth tempIndex)

/-- Semantic step for active selected branch-code staging. -/
def coeffWorkSelectedBranchCodeToScratchStep
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ) :
    RegistersWithCoeffAdderWork tail.succ counterWidth ->
      RegistersWithCoeffAdderWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (coeffWorkSelectedBranchCodeToScratchGates
      tail counterWidth tempIndex)

/-- The active selected branch-code staging program is a concrete encoded-bit
base-gate realization. -/
theorem coeffWorkSelectedBranchCodeToScratch_realizes
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
      (coeffWorkSelectedBranchCodeToScratchProgram
        tail counterWidth tempIndex)
      (coeffWorkSelectedBranchCodeToScratchStep
        tail counterWidth tempIndex) := by
  change UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
      (EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (coeffWorkSelectedBranchCodeToScratchGates
          tail counterWidth tempIndex))
      (EncodedBit.GateSpec.stepList
        (coeffWorkSelectedBranchCodeToScratchGates
          tail counterWidth tempIndex))
  exact EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (coeffWorkSelectedBranchCodeToScratchGates
      tail counterWidth tempIndex)

/-- Selected branch-code staging has fourteen physical leaves. -/
theorem coeffWorkSelectedBranchCodeToScratchGates_length
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ) :
    (coeffWorkSelectedBranchCodeToScratchGates
      tail counterWidth tempIndex).length = 14 := by
  simp [coeffWorkSelectedBranchCodeToScratchGates,
    coeffWorkOddOddCompareBranchCodeToScratchGates]

/-- Selected branch-code staging has one CNOT leaf. -/
theorem coeffWorkSelectedBranchCodeToScratchGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ) :
    ((coeffWorkSelectedBranchCodeToScratchGates tail counterWidth tempIndex).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp [coeffWorkSelectedBranchCodeToScratchGates,
    coeffWorkOddOddCompareBranchCodeToScratchGates]

/-- Selected branch-code staging has nine Toffoli leaves. -/
theorem coeffWorkSelectedBranchCodeToScratchGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ) :
    ((coeffWorkSelectedBranchCodeToScratchGates tail counterWidth tempIndex).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 9 := by
  simp [coeffWorkSelectedBranchCodeToScratchGates,
    coeffWorkOddOddCompareBranchCodeToScratchGates]

/-- On clean scratch and comparison-carry ancillas, selected branch-code
staging restores the selected comparison-carry work bit. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_comparisonCarry_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false) :
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      false := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_temp_clean
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderUBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low low)
    (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderUBit_wire_ne
      tail.succ counterWidth low))
    (coeffAdderUBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderUBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderUBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low))
    (coeffAdderVBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth low)
    (Ne.symm (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (coeffAdderActiveBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth)
    (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth)
    (coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)
    (Ne.symm (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth))
    (coeffAdderCompareBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)
    (coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)
    x hscratchA hscratchB htemp

/-- Selected branch-code staging preserves every non-selected comparison-work
bit.  Together with the selected-bit cleanup theorem above, this exposes the
complete physical comparison-work boundary to downstream circuit proofs. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_comparisonCarry_of_ne
    (tail counterWidth : Nat) (tempIndex observed : Fin tail.succ)
    (hne : tempIndex ≠ observed)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderComparisonCarryBit tail.succ counterWidth observed).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      (coeffAdderComparisonCarryBit tail.succ counterWidth observed).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderComparisonCarryBit tail.succ counterWidth observed)
    (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low observed)
    (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low observed)
    (coeffAdderComparisonCarryBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex observed hne)
    (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth observed)
    (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth observed)
    x

/-- Selected branch-code staging leaves the dedicated coefficient-adder
carry-in work bit untouched. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_carryIn
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (liftedCoeffAdderCarryInBit tail.succ counterWidth)
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth (liftedUBit tail.succ counterWidth low)
          (coeffAdderCarryInWorkBit tail.succ))
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth (liftedVBit tail.succ counterWidth low)
          (coeffAdderCarryInWorkBit tail.succ))
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth
          (liftedComparisonCarryBit tail.succ counterWidth tempIndex)
          (coeffAdderCarryInWorkBit tail.succ))
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth (liftedScratchABit tail.succ counterWidth)
          (coeffAdderCarryInWorkBit tail.succ))
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth (liftedScratchBBit tail.succ counterWidth)
          (coeffAdderCarryInWorkBit tail.succ))
    x

/-- Selected branch-code staging leaves every dedicated coefficient-adder
carry-work bit untouched. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_carryWorkBit
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (workBit : Fin ((tail.succ + 1) - 1))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit).get
        x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit)
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth (liftedUBit tail.succ counterWidth low)
          (coeffAdderCarryWorkBit tail.succ workBit))
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth (liftedVBit tail.succ counterWidth low)
          (coeffAdderCarryWorkBit tail.succ workBit))
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth
          (liftedComparisonCarryBit tail.succ counterWidth tempIndex)
          (coeffAdderCarryWorkBit tail.succ workBit))
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth (liftedScratchABit tail.succ counterWidth)
          (coeffAdderCarryWorkBit tail.succ workBit))
    (by
      exact liftComparisonStateBit_liftCoeffAdderWorkBit_wire_ne
        tail.succ counterWidth (liftedScratchBBit tail.succ counterWidth)
          (coeffAdderCarryWorkBit tail.succ workBit))
    x

/-- On clean scratch and comparison-carry ancillas, selected branch-code
staging writes the active-guarded auxiliary code bit to scratchA. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_scratchA_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false) :
    (coeffAdderScratchABit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      ((coeffAdderActiveBit tail.succ counterWidth).get x &&
        (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit) := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  rw [Branch.fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint]
  exact selectedBranchCodeToScratchStepCore_get_scratchA_clean
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderUBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low low)
    (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderUBit_wire_ne
      tail.succ counterWidth low))
    (coeffAdderUBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderUBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderUBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low))
    (coeffAdderVBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth low)
    (Ne.symm (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (coeffAdderActiveBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth)
    (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth)
    (coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)
    (Ne.symm (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth))
    (coeffAdderCompareBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)
    (coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)
    x hscratchA hscratchB htemp

/-- On clean scratch and comparison-carry ancillas, selected branch-code
staging writes the active-guarded branch-history code bit to scratchB. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_scratchB_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false) :
    (coeffAdderScratchBBit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      ((coeffAdderActiveBit tail.succ counterWidth).get x &&
        (Branch.fromCoeffWorkSignals tail.succ counterWidth x).historyBit) := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  rw [Branch.fromCoeffWorkSignals_historyBit_eq_branch_bits_disjoint]
  exact selectedBranchCodeToScratchStepCore_get_scratchB_clean
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderUBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low low)
    (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderUBit_wire_ne
      tail.succ counterWidth low))
    (coeffAdderUBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderUBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderUBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low))
    (coeffAdderVBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth low)
    (Ne.symm (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (coeffAdderActiveBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth)
    (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth)
    (coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)
    (Ne.symm (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth))
    (coeffAdderCompareBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)
    (coeffAdderScratchABit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth)
    x hscratchA hscratchB htemp

/-- Selected branch-code staging preserves the active flag. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_active
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderActiveBit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      (coeffAdderActiveBit tail.succ counterWidth).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderActiveBit tail.succ counterWidth)
    (Ne.symm (coeffAdderActiveBit_coeffAdderUBit_wire_ne
      tail.succ counterWidth low))
    (Ne.symm (coeffAdderActiveBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low))
    (Ne.symm (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderActiveBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth))
    (Ne.symm (coeffAdderActiveBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth))
    x

/-- Selected branch-code staging preserves the comparison readout. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_compare
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderCompareBit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      (coeffAdderCompareBit tail.succ counterWidth).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderUBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth low)
    (Ne.symm (coeffAdderCompareBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (coeffAdderScratchABit_coeffAdderCompareBit_wire_ne
      tail.succ counterWidth)
    (Ne.symm (coeffAdderCompareBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth))
    x

/-- Selected branch-code staging preserves the low `u` selector readout. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_u_low
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_u
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderUBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low low)
    (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (coeffAdderUBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderUBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth low)
    x

/-- Selected branch-code staging preserves the low `v` selector readout. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_v_low
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_v
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderUBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low low)
    (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (coeffAdderVBit_coeffAdderScratchABit_wire_ne
      tail.succ counterWidth low)
    (coeffAdderVBit_coeffAdderScratchBBit_wire_ne
      tail.succ counterWidth low)
    x

/-- Gate list that latches the active-nonzero odd-odd selector `u[0] && v[0]`
into a clean comparison-carry work bit.  The latch is a stable control source
for later data-dependent dispatch; the branch bodies must not use the mutable
low source bits directly as outer controls. -/
def coeffWorkOddOddSelectorToCarryGates
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)) :=
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  [ EncodedBit.GateSpec.toffoli
      (coeffAdderUBit tail.succ counterWidth low)
      (coeffAdderVBit tail.succ counterWidth low)
      (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex)
      (coeffAdderUBit_coeffAdderVBit_wire_ne
        tail.succ counterWidth low low)
      (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth low selectorIndex)
      (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth low selectorIndex) ]

/-- Base-gate program for latching the active-nonzero odd-odd selector. -/
def coeffWorkOddOddSelectorToCarryProgram
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkOddOddSelectorToCarryGates
      tail counterWidth selectorIndex)

/-- Semantic step for latching the active-nonzero odd-odd selector. -/
def coeffWorkOddOddSelectorToCarryStep
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ) :
    RegistersWithCoeffAdderWork tail.succ counterWidth ->
      RegistersWithCoeffAdderWork tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (coeffWorkOddOddSelectorToCarryGates
      tail counterWidth selectorIndex)

/-- The odd-odd selector latch gate list has its semantic step. -/
theorem coeffWorkOddOddSelectorToCarryStep_eq_gateList
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkOddOddSelectorToCarryGates
          tail counterWidth selectorIndex) x =
      coeffWorkOddOddSelectorToCarryStep
        tail counterWidth selectorIndex x := by
  rfl

/-- The odd-odd selector latch program realizes its semantic step. -/
theorem coeffWorkOddOddSelectorToCarry_realizes
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
      (coeffWorkOddOddSelectorToCarryProgram
        tail counterWidth selectorIndex)
      (coeffWorkOddOddSelectorToCarryStep
        tail counterWidth selectorIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkOddOddSelectorToCarryGates tail counterWidth selectorIndex)
    (coeffWorkOddOddSelectorToCarryStep_eq_gateList
      tail counterWidth selectorIndex)

/-- The odd-odd selector latch xors `u[0] && v[0]` into the selected
comparison-carry bit. -/
theorem coeffWorkOddOddSelectorToCarryStep_get_selector
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex).get
        (coeffWorkOddOddSelectorToCarryStep
          tail counterWidth selectorIndex x) =
      ((coeffAdderComparisonCarryBit
          tail.succ counterWidth selectorIndex).get x ^^
        ((coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x)) := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  simpa [coeffWorkOddOddSelectorToCarryStep,
    coeffWorkOddOddSelectorToCarryGates, low,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_target
      (coeffAdderUBit tail.succ counterWidth low)
      (coeffAdderVBit tail.succ counterWidth low)
      (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex) x

/-- On a clean latch bit, the odd-odd selector latch records exactly
`u[0] && v[0]`. -/
theorem coeffWorkOddOddSelectorToCarryStep_get_selector_clean
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hclean :
      (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex).get x = false) :
    (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex).get
        (coeffWorkOddOddSelectorToCarryStep
          tail counterWidth selectorIndex x) =
      ((coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
        (coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x) := by
  rw [coeffWorkOddOddSelectorToCarryStep_get_selector]
  simp [hclean]

/-- The odd-odd selector latch preserves the low `u` selector readout. -/
theorem coeffWorkOddOddSelectorToCarryStep_get_u_low
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
        (coeffWorkOddOddSelectorToCarryStep
          tail counterWidth selectorIndex x) =
      (coeffAdderUBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  simpa [coeffWorkOddOddSelectorToCarryStep,
    coeffWorkOddOddSelectorToCarryGates, low,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne
      (coeffAdderUBit tail.succ counterWidth low)
      (coeffAdderVBit tail.succ counterWidth low)
      (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex)
      (coeffAdderUBit tail.succ counterWidth low)
      (Ne.symm (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth low selectorIndex)) x

/-- The odd-odd selector latch preserves the low `v` selector readout. -/
theorem coeffWorkOddOddSelectorToCarryStep_get_v_low
    (tail counterWidth : Nat) (selectorIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
        (coeffWorkOddOddSelectorToCarryStep
          tail counterWidth selectorIndex x) =
      (coeffAdderVBit tail.succ counterWidth
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  simpa [coeffWorkOddOddSelectorToCarryStep,
    coeffWorkOddOddSelectorToCarryGates, low,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step] using
    EncodedBit.toffoliStep_get_of_target_ne
      (coeffAdderUBit tail.succ counterWidth low)
      (coeffAdderVBit tail.succ counterWidth low)
      (coeffAdderComparisonCarryBit
        tail.succ counterWidth selectorIndex)
      (coeffAdderVBit tail.succ counterWidth low)
      (Ne.symm (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
        tail.succ counterWidth low selectorIndex)) x

/-- Selected branch-code staging preserves every stored branch-history bit. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_historyBit
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex)
    (coeffAdderUBit_coeffAdderHistoryBit_wire_ne
      tail.succ counterWidth low historyIndex)
    (coeffAdderVBit_coeffAdderHistoryBit_wire_ne
      tail.succ counterWidth low historyIndex)
      (coeffAdderComparisonCarryBit_coeffAdderHistoryBit_wire_ne
        tail.succ counterWidth tempIndex historyIndex)
    (coeffAdderScratchABit_coeffAdderHistoryBit_wire_ne
      tail.succ counterWidth historyIndex)
    (coeffAdderScratchBBit_coeffAdderHistoryBit_wire_ne
      tail.succ counterWidth historyIndex)
    x

/-- Selected branch-code staging preserves every `u` value bit. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_uWordBit
    (tail counterWidth : Nat) (tempIndex bit : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderUWord tail.succ counterWidth).bit bit).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      ((coeffAdderUWord tail.succ counterWidth).bit bit).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  by_cases hbit : bit = 0
  · subst bit
    simpa [coeffAdderUBit, liftedUBit, coeffAdderUWord, liftedUWord,
      RegisterBits.uValueBit, RegisterBits.uBit] using
      coeffWorkSelectedBranchCodeToScratchStep_get_u_low
        tail counterWidth tempIndex x
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    ((coeffAdderUWord tail.succ counterWidth).bit bit)
    (by
      simpa [coeffAdderUBit, liftedUBit, coeffAdderUWord, liftedUWord,
        RegisterBits.uValueBit, RegisterBits.uBit] using
        coeffAdderUWordBit_coeffAdderUWordBit_wire_ne
          tail.succ counterWidth 0 bit (Ne.symm hbit))
    (by
      simpa [coeffAdderVBit, liftedVBit, coeffAdderUWord, liftedUWord,
        coeffAdderVWord, liftedVWord, RegisterBits.uValueBit,
        RegisterBits.vValueBit, RegisterBits.vBit] using
        Ne.symm (coeffAdderUWordBit_coeffAdderVWordBit_wire_ne
          tail.succ counterWidth bit 0))
    (by
      simpa [coeffAdderUWord, liftedUWord] using
        Ne.symm
          (coeffAdderUWordBit_coeffAdderComparisonCarryBit_wire_ne
            tail.succ counterWidth bit tempIndex))
    (by
      simpa [coeffAdderUWord, liftedUWord] using
        coeffAdderScratchABit_coeffAdderUWordBit_wire_ne
          tail.succ counterWidth bit)
    (by
      simpa [coeffAdderUBit, liftedUBit, coeffAdderUWord, liftedUWord,
        RegisterBits.uValueBit, RegisterBits.uBit] using
        Ne.symm (coeffAdderUBit_coeffAdderScratchBBit_wire_ne
          tail.succ counterWidth (WireAddress.littleEndianWire bit)))
    x

/-- Selected branch-code staging preserves every `v` value bit. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_vWordBit
    (tail counterWidth : Nat) (tempIndex bit : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderVWord tail.succ counterWidth).bit bit).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      ((coeffAdderVWord tail.succ counterWidth).bit bit).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  by_cases hbit : bit = 0
  · subst bit
    simpa [coeffAdderVBit, liftedVBit, coeffAdderVWord, liftedVWord,
      RegisterBits.vValueBit, RegisterBits.vBit] using
      coeffWorkSelectedBranchCodeToScratchStep_get_v_low
        tail counterWidth tempIndex x
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    ((coeffAdderVWord tail.succ counterWidth).bit bit)
    (by
      simpa [coeffAdderUBit, liftedUBit, coeffAdderUWord, liftedUWord,
        coeffAdderVWord, liftedVWord, RegisterBits.uValueBit,
        RegisterBits.uBit, RegisterBits.vValueBit] using
        coeffAdderUWordBit_coeffAdderVWordBit_wire_ne
          tail.succ counterWidth 0 bit)
    (by
      simpa [coeffAdderVBit, liftedVBit, coeffAdderVWord, liftedVWord,
        RegisterBits.vValueBit, RegisterBits.vBit] using
        coeffAdderVWordBit_coeffAdderVWordBit_wire_ne
          tail.succ counterWidth 0 bit (Ne.symm hbit))
    (by
      simpa [coeffAdderVWord, liftedVWord] using
        Ne.symm
          (coeffAdderVWordBit_coeffAdderComparisonCarryBit_wire_ne
            tail.succ counterWidth bit tempIndex))
    (by
      simpa [coeffAdderVWord, liftedVWord] using
        coeffAdderScratchABit_coeffAdderVWordBit_wire_ne
          tail.succ counterWidth bit)
    (by
      simpa [coeffAdderVBit, liftedVBit, coeffAdderVWord, liftedVWord,
        RegisterBits.vValueBit, RegisterBits.vBit] using
        Ne.symm (coeffAdderVBit_coeffAdderScratchBBit_wire_ne
          tail.succ counterWidth (WireAddress.littleEndianWire bit)))
    x

/-- Selected branch-code staging preserves every little-endian `s`
coefficient value bit. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_sCoeffValueWordBit
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (bit : Fin (tail.succ + 1))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderSCoeffValueWord tail.succ counterWidth).bit bit).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      ((coeffAdderSCoeffValueWord tail.succ counterWidth).bit bit).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    ((coeffAdderSCoeffValueWord tail.succ counterWidth).bit bit)
    (by
      simpa [coeffAdderUBit, liftedUBit, coeffAdderUWord, liftedUWord,
        coeffAdderSCoeffValueWord, liftedSCoeffValueWord,
        RegisterBits.uValueBit, RegisterBits.uBit] using
        coeffAdderUWordBit_coeffAdderSCoeffValueWordBit_wire_ne
          tail.succ counterWidth 0 bit)
    (by
      simpa [coeffAdderVBit, liftedVBit, coeffAdderVWord, liftedVWord,
        coeffAdderSCoeffValueWord, liftedSCoeffValueWord,
        RegisterBits.vValueBit, RegisterBits.vBit] using
        coeffAdderVWordBit_coeffAdderSCoeffValueWordBit_wire_ne
          tail.succ counterWidth 0 bit)
    (by
      simpa [coeffAdderSCoeffValueWord, liftedSCoeffValueWord] using
        Ne.symm
          (coeffAdderSCoeffValueWordBit_coeffAdderComparisonCarryBit_wire_ne
            tail.succ counterWidth bit tempIndex))
    (by
      simpa [coeffAdderSCoeffValueWord, liftedSCoeffValueWord] using
        coeffAdderScratchABit_coeffAdderSCoeffValueWordBit_wire_ne
          tail.succ counterWidth bit)
    (by
      exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
        tail.succ counterWidth
        (liftedScratchBBit tail.succ counterWidth)
        ((liftedSCoeffValueWord tail.succ counterWidth).bit bit)
        (by
          simpa [liftedScratchBBit, liftedSCoeffValueWord, liftedSCoeffWord,
            RegisterBits.sCoeffValueBit] using
            liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
              (RegisterBits.scratchBBit tail.succ counterWidth)
              (RegisterBits.sCoeffValueBit tail.succ counterWidth bit)
              (by
                simpa [RegisterBits.sCoeffValueBit] using
                  Ne.symm (RegisterBits.sCoeff_scratchB_wire_ne
                    tail.succ counterWidth
                    (WireAddress.littleEndianWire bit)))))
    x

/-- Selected branch-code staging preserves every little-endian `r`
coefficient value bit. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_rCoeffValueWordBit
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (bit : Fin (tail.succ + 1))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit bit).get
        (coeffWorkSelectedBranchCodeToScratchStep
          tail counterWidth tempIndex x) =
      ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit bit).get x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit bit)
    (by
      simpa [coeffAdderUBit, liftedUBit, coeffAdderUWord, liftedUWord,
        coeffAdderRCoeffValueWord, liftedRCoeffValueWord,
        RegisterBits.uValueBit, RegisterBits.uBit] using
        coeffAdderUWordBit_coeffAdderRCoeffValueWordBit_wire_ne
          tail.succ counterWidth 0 bit)
    (by
      simpa [coeffAdderVBit, liftedVBit, coeffAdderVWord, liftedVWord,
        coeffAdderRCoeffValueWord, liftedRCoeffValueWord,
        RegisterBits.vValueBit, RegisterBits.vBit] using
        coeffAdderVWordBit_coeffAdderRCoeffValueWordBit_wire_ne
          tail.succ counterWidth 0 bit)
    (by
      simpa [coeffAdderRCoeffValueWord, liftedRCoeffValueWord] using
        Ne.symm
          (coeffAdderRCoeffValueWordBit_coeffAdderComparisonCarryBit_wire_ne
            tail.succ counterWidth bit tempIndex))
    (by
      simpa [coeffAdderRCoeffValueWord, liftedRCoeffValueWord] using
        coeffAdderScratchABit_coeffAdderRCoeffValueWordBit_wire_ne
          tail.succ counterWidth bit)
    (by
      exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
        tail.succ counterWidth
        (liftedScratchBBit tail.succ counterWidth)
        ((liftedRCoeffValueWord tail.succ counterWidth).bit bit)
        (by
          simpa [liftedScratchBBit, liftedRCoeffValueWord, liftedRCoeffWord,
            RegisterBits.rCoeffValueBit] using
            liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
              (RegisterBits.scratchBBit tail.succ counterWidth)
              (RegisterBits.rCoeffValueBit tail.succ counterWidth bit)
              (by
                simpa [RegisterBits.rCoeffValueBit] using
                  Ne.symm (RegisterBits.rCoeff_scratchB_wire_ne
                    tail.succ counterWidth
                    (WireAddress.littleEndianWire bit)))))
    x

/-- Selected branch-code staging preserves the `u` word. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_u
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffWorkSelectedBranchCodeToScratchStep
        tail counterWidth tempIndex x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkSelectedBranchCodeToScratchStep_get_uWordBit
    tail counterWidth tempIndex bit x
  simpa [coeffAdderUWord_get_testBit] using h

/-- Selected branch-code staging preserves the `v` word. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_v
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffWorkSelectedBranchCodeToScratchStep
        tail counterWidth tempIndex x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkSelectedBranchCodeToScratchStep_get_vWordBit
    tail counterWidth tempIndex bit x
  simpa [coeffAdderVWord_get_testBit] using h

/-- Selected branch-code staging preserves the `s` coefficient word. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_sCoeff
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffWorkSelectedBranchCodeToScratchStep
        tail counterWidth tempIndex x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkSelectedBranchCodeToScratchStep_get_sCoeffValueWordBit
    tail counterWidth tempIndex bit x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- Selected branch-code staging preserves the `r` coefficient word. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_rCoeff
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffWorkSelectedBranchCodeToScratchStep
        tail counterWidth tempIndex x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkSelectedBranchCodeToScratchStep_get_rCoeffValueWordBit
    tail counterWidth tempIndex bit x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- Selected branch-code staging preserves the physical padding counter. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_get_counter
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffWorkSelectedBranchCodeToScratchStep
        tail counterWidth tempIndex x).1.1.counter =
      x.1.1.counter := by
  apply word_eq_of_testBit_eq
  intro bit
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  have hcounter := selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderCounterValueBit tail.succ counterWidth bit)
    (by
      exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
        tail.succ counterWidth
        (liftedUBit tail.succ counterWidth low)
        (liftRegisterBitToComparisonWork tail.succ counterWidth
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
        (liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
          (RegisterBits.uBit tail.succ counterWidth low)
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit))
          (RegisterBits.u_counter_wire_ne tail.succ counterWidth low
            (WireAddress.littleEndianWire bit))))
    (by
      exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
        tail.succ counterWidth
        (liftedVBit tail.succ counterWidth low)
        (liftRegisterBitToComparisonWork tail.succ counterWidth
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
        (liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
          (RegisterBits.vBit tail.succ counterWidth low)
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit))
          (RegisterBits.v_counter_wire_ne tail.succ counterWidth low
            (WireAddress.littleEndianWire bit))))
    (by
      exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
        tail.succ counterWidth
        (liftedComparisonCarryBit tail.succ counterWidth tempIndex)
        (liftRegisterBitToComparisonWork tail.succ counterWidth
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
        (Ne.symm (liftRegisterBit_liftComparisonWorkBit_wire_ne
          tail.succ counterWidth
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit))
          (comparisonCarryValueBit tail.succ tempIndex))))
    (by
      exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
        tail.succ counterWidth
        (liftedScratchABit tail.succ counterWidth)
        (liftRegisterBitToComparisonWork tail.succ counterWidth
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
        (liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
          (RegisterBits.scratchABit tail.succ counterWidth)
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit))
          (RegisterBits.scratchA_counter_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire bit))))
    (by
      exact liftComparisonStateBit_liftComparisonStateBit_wire_ne
        tail.succ counterWidth
        (liftedScratchBBit tail.succ counterWidth)
        (liftRegisterBitToComparisonWork tail.succ counterWidth
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit)))
        (liftRegisterBit_liftRegisterBit_wire_ne tail.succ counterWidth
          (RegisterBits.scratchBBit tail.succ counterWidth)
          (RegisterBits.counterBit tail.succ counterWidth
            (WireAddress.littleEndianWire bit))
          (RegisterBits.scratchB_counter_wire_ne tail.succ counterWidth
            (WireAddress.littleEndianWire bit))))
    x
  change
    (selectedBranchCodeToScratchStepCore
      (coeffAdderUBit tail.succ counterWidth low)
      (coeffAdderVBit tail.succ counterWidth low)
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
      (coeffAdderActiveBit tail.succ counterWidth)
      (coeffAdderCompareBit tail.succ counterWidth)
      (coeffAdderScratchABit tail.succ counterWidth)
      (coeffAdderScratchBBit tail.succ counterWidth) x).1.1.counter.val.testBit
        bit.val = x.1.1.counter.val.testBit bit.val
  simpa [coeffAdderCounterValueBit_get] using hcounter

/-- On inactive clean branch-code work, selected branch-code staging is a
no-op. -/
theorem coeffWorkSelectedBranchCodeToScratchStep_eq_self_of_active_false_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (_htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = false) :
    coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x =
      x := by
  let low := WireAddress.littleEndianWire (0 : Fin tail.succ)
  exact selectedBranchCodeToScratchStepCore_eq_self_of_active_false_clean
    (coeffAdderUBit tail.succ counterWidth low)
    (coeffAdderVBit tail.succ counterWidth low)
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex)
    (coeffAdderActiveBit tail.succ counterWidth)
    (coeffAdderCompareBit tail.succ counterWidth)
    (coeffAdderScratchABit tail.succ counterWidth)
    (coeffAdderScratchBBit tail.succ counterWidth)
    (coeffAdderUBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderUBit_wire_ne
      tail.succ counterWidth low))
    (coeffAdderVBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth low tempIndex)
    (Ne.symm (coeffAdderActiveBit_coeffAdderVBit_wire_ne
      tail.succ counterWidth low))
    (Ne.symm (coeffAdderActiveBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchABit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    (Ne.symm (coeffAdderScratchBBit_coeffAdderComparisonCarryBit_wire_ne
      tail.succ counterWidth tempIndex))
    x hactive hscratchA hscratchB

/-- Coefficient-work-lifted `uEven` branch-code staging preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_carryIn
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- Coefficient-work-lifted `uEven` branch-code staging preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_carryWorkBit
    (n counterWidth : Nat) (bit : Fin n)
    (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- Coefficient-work-lifted `vEven` branch-code staging preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_carryIn
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- Coefficient-work-lifted `vEven` branch-code staging preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_carryWorkBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- Coefficient-work-lifted `uEven` branch-code staging preserves the active
flag. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  change (liftedActiveBit n counterWidth).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth bit x.1) =
      (liftedActiveBit n counterWidth).get x.1
  exact liftedUEvenBranchCodeToScratchStep_get_active n counterWidth bit x.1

/-- On clean compare, coefficient-work-lifted `uEven` branch-code staging
restores compare. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) =
      false := by
  change (liftedCompareBit n counterWidth).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth bit x.1) =
      false
  exact liftedUEvenBranchCodeToScratchStep_get_compare_clean
    n counterWidth bit x.1 (by
      change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
      exact hcompare)

/-- On clean compare, coefficient-work-lifted `uEven` branch-code staging
toggles scratchA exactly under the active `uEven` condition. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) =
      ((coeffAdderScratchABit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          !(coeffAdderUBit n counterWidth bit).get x)) := by
  change (liftedScratchABit n counterWidth).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth bit x.1) =
      ((liftedScratchABit n counterWidth).get x.1 ^^
        ((liftedActiveBit n counterWidth).get x.1 &&
          !(liftedUBit n counterWidth bit).get x.1))
  exact liftedUEvenBranchCodeToScratchStep_get_scratchA_clean
    n counterWidth bit x.1 (by
      change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
      exact hcompare)

/-- Coefficient-work-lifted `uEven` branch-code staging preserves each `u`
word bit. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit targetBit).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      ((coeffAdderUWord n counterWidth).bit targetBit).get x := by
  change ((liftedUWord n counterWidth).bit targetBit).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth selectorBit x.1) =
      ((liftedUWord n counterWidth).bit targetBit).get x.1
  exact liftedUEvenBranchCodeToScratchStep_get_uWordBit n counterWidth
    selectorBit targetBit x.1

/-- Coefficient-work-lifted `uEven` branch-code staging preserves the `u`
source word. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_u
    (n counterWidth : Nat) (selectorBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUEvenBranchCodeToScratchStep n counterWidth selectorBit x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUEvenBranchCodeToScratchStep_get_uWordBit
    n counterWidth selectorBit bit x
  simpa [coeffAdderUWord_get_testBit] using h

/-- Coefficient-work-lifted `uEven` branch-code staging preserves each `v`
word bit. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit targetBit).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      ((coeffAdderVWord n counterWidth).bit targetBit).get x := by
  change ((liftedVWord n counterWidth).bit targetBit).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth selectorBit x.1) =
      ((liftedVWord n counterWidth).bit targetBit).get x.1
  exact liftedUEvenBranchCodeToScratchStep_get_vWordBit n counterWidth
    selectorBit targetBit x.1

/-- Coefficient-work-lifted `uEven` branch-code staging preserves the `v`
source word. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_v
    (n counterWidth : Nat) (selectorBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUEvenBranchCodeToScratchStep n counterWidth selectorBit x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUEvenBranchCodeToScratchStep_get_vWordBit
    n counterWidth selectorBit bit x
  simpa [coeffAdderVWord_get_testBit] using h

/-- Coefficient-work-lifted `uEven` branch-code staging preserves each `s`
coefficient value bit. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth selectorBit x.1) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact liftedUEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth selectorBit targetBit x.1

/-- Coefficient-work-lifted `uEven` branch-code staging preserves each `r`
coefficient value bit. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth selectorBit x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (liftedUEvenBranchCodeToScratchStep n counterWidth selectorBit x.1) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact liftedUEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth selectorBit targetBit x.1

/-- Coefficient-work-lifted `uEven` branch-code staging preserves the `s`
coefficient word. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_sCoeff
    (n counterWidth : Nat) (selectorBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUEvenBranchCodeToScratchStep n counterWidth selectorBit x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth selectorBit bit x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- Coefficient-work-lifted `uEven` branch-code staging preserves the `r`
coefficient word. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_rCoeff
    (n counterWidth : Nat) (selectorBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUEvenBranchCodeToScratchStep n counterWidth selectorBit x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkUEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth selectorBit bit x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- Coefficient-work-lifted `vEven` branch-code staging preserves the active
flag. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  change (liftedActiveBit n counterWidth).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x.1) =
      (liftedActiveBit n counterWidth).get x.1
  exact liftedVEvenBranchCodeToScratchStep_get_active n counterWidth uIndex
    vIndex x.1

/-- On clean compare, coefficient-work-lifted `vEven` branch-code staging
restores compare. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_compare_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      false := by
  change (liftedCompareBit n counterWidth).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x.1) =
      false
  exact liftedVEvenBranchCodeToScratchStep_get_compare_clean
    n counterWidth uIndex vIndex x.1 (by
      change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
      exact hcompare)

/-- On clean compare, coefficient-work-lifted `vEven` branch-code staging
preserves scratchA. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  change (liftedScratchABit n counterWidth).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x.1) =
      (liftedScratchABit n counterWidth).get x.1
  exact liftedVEvenBranchCodeToScratchStep_get_scratchA_clean n counterWidth
    uIndex vIndex x.1 (by
      change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
      exact hcompare)

/-- Coefficient-work-lifted `vEven` branch-code staging preserves each `u`
word bit. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_uWordBit
    (n counterWidth : Nat) (uIndex vIndex targetBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderUWord n counterWidth).bit targetBit).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      ((coeffAdderUWord n counterWidth).bit targetBit).get x := by
  change ((liftedUWord n counterWidth).bit targetBit).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x.1) =
      ((liftedUWord n counterWidth).bit targetBit).get x.1
  exact liftedVEvenBranchCodeToScratchStep_get_uWordBit n counterWidth uIndex
    vIndex targetBit x.1

/-- Coefficient-work-lifted `vEven` branch-code staging preserves the `u`
source word. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_u
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVEvenBranchCodeToScratchStep_get_uWordBit
    n counterWidth uIndex vIndex bit x
  simpa [coeffAdderUWord_get_testBit] using h

/-- Coefficient-work-lifted `vEven` branch-code staging preserves each `v`
word bit. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_vWordBit
    (n counterWidth : Nat) (uIndex vIndex targetBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderVWord n counterWidth).bit targetBit).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      ((coeffAdderVWord n counterWidth).bit targetBit).get x := by
  change ((liftedVWord n counterWidth).bit targetBit).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x.1) =
      ((liftedVWord n counterWidth).bit targetBit).get x.1
  exact liftedVEvenBranchCodeToScratchStep_get_vWordBit n counterWidth uIndex
    vIndex targetBit x.1

/-- Coefficient-work-lifted `vEven` branch-code staging preserves the `v`
source word. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_v
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVEvenBranchCodeToScratchStep_get_vWordBit
    n counterWidth uIndex vIndex bit x
  simpa [coeffAdderVWord_get_testBit] using h

/-- Coefficient-work-lifted `vEven` branch-code staging preserves each `s`
coefficient value bit. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (targetBit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      ((coeffAdderSCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x.1) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact liftedVEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth uIndex vIndex targetBit x.1

/-- Coefficient-work-lifted `vEven` branch-code staging preserves each `r`
coefficient value bit. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (targetBit : Fin (n + 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      ((coeffAdderRCoeffValueWord n counterWidth).bit targetBit).get x := by
  change ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (liftedVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x.1) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x.1
  exact liftedVEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth uIndex vIndex targetBit x.1

/-- Coefficient-work-lifted `vEven` branch-code staging preserves the `s`
coefficient word. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_sCoeff
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVEvenBranchCodeToScratchStep_get_sCoeffValueWordBit
    n counterWidth uIndex vIndex bit x
  simpa [coeffAdderSCoeffValueWord_get_testBit] using h

/-- Coefficient-work-lifted `vEven` branch-code staging preserves the `r`
coefficient word. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_rCoeff
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := coeffWorkVEvenBranchCodeToScratchStep_get_rCoeffValueWordBit
    n counterWidth uIndex vIndex bit x
  simpa [coeffAdderRCoeffValueWord_get_testBit] using h

/-- After clean concrete `uEven` branch-code staging, the aux-active shift
dispatch selects the unconditioned `u/s` shift group when the staged branch is
active. -/
theorem
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_after_uEvenBranchCodeToScratch_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hu : (coeffAdderUBit n counterWidth bit).get x = false) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) =
      coeffWorkUDiv2ThenSMul2Step n counterWidth
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) := by
  let staged := coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x
  have hactiveStaged :
      (coeffAdderActiveBit n counterWidth).get staged = true := by
    dsimp [staged]
    rw [coeffWorkUEvenBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAStaged :
      (coeffAdderScratchABit n counterWidth).get staged = true := by
    dsimp [staged]
    rw [coeffWorkUEvenBranchCodeToScratchStep_get_scratchA_clean
      n counterWidth bit x hcompare]
    simp [hscratchA, hactive, hu]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_of_active_true_scratchA_true
      n counterWidth staged hactiveStaged hscratchAStaged

/-- After clean concrete `vEven` branch-code staging, the aux-active shift
dispatch selects the unconditioned `v/r` shift group when the active flag
remains true and the staged auxiliary bit remains false. -/
theorem
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_after_vEvenBranchCodeToScratch_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true) :
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      coeffWorkVDiv2ThenRMul2Step n counterWidth
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) := by
  let staged :=
    coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x
  have hactiveStaged :
      (coeffAdderActiveBit n counterWidth).get staged = true := by
    dsimp [staged]
    rw [coeffWorkVEvenBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAStaged :
      (coeffAdderScratchABit n counterWidth).get staged = false := by
    dsimp [staged]
    rw [coeffWorkVEvenBranchCodeToScratchStep_get_scratchA_clean
      n counterWidth uIndex vIndex x hcompare]
    exact hscratchA
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_of_active_true_scratchA_false
      n counterWidth staged hactiveStaged hscratchAStaged

/-! ## Branch-code to auxiliary-shift dispatch wrappers -/

/-- Coefficient-work-lifted `uEven` branch-code staging followed by the
auxiliary active/branch-code shift dispatch. -/
def coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
      (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x)

/-- Actual circuit for `uEven` branch-code staging followed by the auxiliary
shift dispatch. -/
def coeffWorkUEvenBranchCodeThenAuxShiftDispatchProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUEvenBranchCodeToScratchProgram n counterWidth bit)
    (coeffWorkAuxActiveShiftDispatchProgram n counterWidth)

/-- The composed `uEven` circuit realizes the staged dispatch action. -/
theorem coeffWorkUEvenBranchCodeThenAuxShiftDispatch_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUEvenBranchCodeThenAuxShiftDispatchProgram
        n counterWidth bit)
      (coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep n counterWidth bit) := by
  unfold coeffWorkUEvenBranchCodeThenAuxShiftDispatchProgram
    coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit)
    (secondStep := coeffWorkAuxActiveShiftDispatchStep n counterWidth)
    (coeffWorkUEvenBranchCodeToScratch_realizes n counterWidth bit)
    (coeffWorkAuxActiveShiftDispatch_realizes n counterWidth)

/-- On clean inputs with an active `uEven` staged code, the composed
branch-code/dispatch wrapper selects the unconditioned `u/s` shift group. -/
theorem coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep_eq_uShift_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hu : (coeffAdderUBit n counterWidth bit).get x = false) :
    coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep n counterWidth bit x =
      coeffWorkUDiv2ThenSMul2Step n counterWidth
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) := by
  rw [coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_after_uEvenBranchCodeToScratch_clean
      n counterWidth bit x hcompare hscratchA hactive hu

/-- Coefficient-work-lifted `vEven` branch-code staging followed by the
auxiliary active/branch-code shift dispatch. -/
def coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
      (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x)

/-- Actual circuit for `vEven` branch-code staging followed by the auxiliary
shift dispatch. -/
def coeffWorkVEvenBranchCodeThenAuxShiftDispatchProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVEvenBranchCodeToScratchProgram
      n counterWidth uIndex vIndex)
    (coeffWorkAuxActiveShiftDispatchProgram n counterWidth)

/-- The composed `vEven` circuit realizes the staged dispatch action. -/
theorem coeffWorkVEvenBranchCodeThenAuxShiftDispatch_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVEvenBranchCodeThenAuxShiftDispatchProgram
        n counterWidth uIndex vIndex)
      (coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep n counterWidth uIndex
        vIndex) := by
  unfold coeffWorkVEvenBranchCodeThenAuxShiftDispatchProgram
    coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex)
    (secondStep := coeffWorkAuxActiveShiftDispatchStep n counterWidth)
    (coeffWorkVEvenBranchCodeToScratch_realizes n counterWidth uIndex vIndex)
    (coeffWorkAuxActiveShiftDispatch_realizes n counterWidth)

/-- On clean active `vEven` staging, the composed branch-code/dispatch wrapper
selects the unconditioned `v/r` shift group. -/
theorem coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep_eq_vShift_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true) :
    coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep n counterWidth uIndex
        vIndex x =
      coeffWorkVDiv2ThenRMul2Step n counterWidth
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) := by
  rw [coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_after_vEvenBranchCodeToScratch_clean
      n counterWidth uIndex vIndex x hcompare hscratchA hactive

/-- The `uEven` branch-code/dispatch wrapper writes `u := u / 2` when the
staged branch is active and the source `u` word is even. -/
theorem coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep_get_u_wordHalf_of_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hu : (coeffAdderUBit tail.succ counterWidth bit).get x = false)
    (hlsb : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep
        tail.succ counterWidth bit x).1.1.u =
      wordHalf tail.succ x.1.1.u := by
  let staged :=
    coeffWorkUEvenBranchCodeToScratchStep tail.succ counterWidth bit x
  have hstagedU : staged.1.1.u = x.1.1.u := by
    dsimp [staged]
    exact coeffWorkUEvenBranchCodeToScratchStep_get_u
      tail.succ counterWidth bit x
  have hlsbStaged : staged.1.1.u.val.testBit (0 : Nat) = false := by
    rw [hstagedU]
    exact hlsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
      tail counterWidth staged hlsbStaged
  have hdispatch :=
    coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep_eq_uShift_clean
      tail.succ counterWidth bit x hcompare hscratchA hactive hu
  rw [hdispatch]
  change
    (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth staged).1.1.u =
      wordHalf tail.succ x.1.1.u
  rw [hstagedU] at hmain
  exact hmain

/-- The `vEven` branch-code/dispatch wrapper writes `v := v / 2` when the
staged branch is active and the source `v` word is even. -/
theorem coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep_get_v_wordHalf_of_clean
    (tail counterWidth : Nat) (uIndex vIndex : Fin tail.succ)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hlsb : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep
        tail.succ counterWidth uIndex vIndex x).1.1.v =
      wordHalf tail.succ x.1.1.v := by
  let staged :=
    coeffWorkVEvenBranchCodeToScratchStep tail.succ counterWidth uIndex
      vIndex x
  have hstagedV : staged.1.1.v = x.1.1.v := by
    dsimp [staged]
    exact coeffWorkVEvenBranchCodeToScratchStep_get_v
      tail.succ counterWidth uIndex vIndex x
  have hlsbStaged : staged.1.1.v.val.testBit (0 : Nat) = false := by
    rw [hstagedV]
    exact hlsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
      tail counterWidth staged hlsbStaged
  have hdispatch :=
    coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep_eq_vShift_clean
      tail.succ counterWidth uIndex vIndex x hcompare hscratchA hactive
  rw [hdispatch]
  change
    (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth staged).1.1.v =
      wordHalf tail.succ x.1.1.v
  rw [hstagedV] at hmain
  exact hmain

/-- The `uEven` branch-code/dispatch wrapper writes `s := 2 * s` through the
paired shift group when the source coefficient top bit is false. -/
theorem
    coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep_get_sCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hu : (coeffAdderUBit n counterWidth bit).get x = false)
    (hmsb : x.1.1.sCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit x).1.1.sCoeff =
      wordDouble (n + 1) x.1.1.sCoeff := by
  let staged :=
    coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x
  have hstagedS : staged.1.1.sCoeff = x.1.1.sCoeff := by
    dsimp [staged]
    exact coeffWorkUEvenBranchCodeToScratchStep_get_sCoeff
      n counterWidth bit x
  have hmsbStaged :
      staged.1.1.sCoeff.val.testBit (Fin.last n).val = false := by
    rw [hstagedS]
    exact hmsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
      n counterWidth staged hmsbStaged
  have hdispatch :=
    coeffWorkUEvenBranchCodeThenAuxShiftDispatchStep_eq_uShift_clean
      n counterWidth bit x hcompare hscratchA hactive hu
  rw [hdispatch]
  change
    (coeffWorkUDiv2ThenSMul2Step n counterWidth staged).1.1.sCoeff =
      wordDouble (n + 1) x.1.1.sCoeff
  rw [hstagedS] at hmain
  exact hmain

/-- The `vEven` branch-code/dispatch wrapper writes `r := 2 * r` through the
paired shift group when the source coefficient top bit is false. -/
theorem
    coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep_get_rCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hmsb : x.1.1.rCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep
        n counterWidth uIndex vIndex x).1.1.rCoeff =
      wordDouble (n + 1) x.1.1.rCoeff := by
  let staged :=
    coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x
  have hstagedR : staged.1.1.rCoeff = x.1.1.rCoeff := by
    dsimp [staged]
    exact coeffWorkVEvenBranchCodeToScratchStep_get_rCoeff
      n counterWidth uIndex vIndex x
  have hmsbStaged :
      staged.1.1.rCoeff.val.testBit (Fin.last n).val = false := by
    rw [hstagedR]
    exact hmsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
      n counterWidth staged hmsbStaged
  have hdispatch :=
    coeffWorkVEvenBranchCodeThenAuxShiftDispatchStep_eq_vShift_clean
      n counterWidth uIndex vIndex x hcompare hscratchA hactive
  rw [hdispatch]
  change
    (coeffWorkVDiv2ThenRMul2Step n counterWidth staged).1.1.rCoeff =
      wordDouble (n + 1) x.1.1.rCoeff
  rw [hstagedR] at hmain
  exact hmain

/-- Lifted history-write atom that xors the staged branch-history code bit from
scratchB into one stored history slot. -/
def liftedActiveScratchBToHistoryStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x => (activeScratchBToHistoryStep n counterWidth historyIndex x.1, x.2)

/-- Actual circuit for the lifted active/scratchB-to-history atom. -/
def liftedActiveScratchBToHistoryProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (activeScratchBToHistoryProgram n counterWidth historyIndex)

/-- The lifted history-write circuit realizes the product action. -/
theorem liftedActiveScratchBToHistory_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithComparisonWorkEncoding n counterWidth)
      (liftedActiveScratchBToHistoryProgram n counterWidth historyIndex)
      (liftedActiveScratchBToHistoryStep n counterWidth historyIndex) :=
  UnitaryCircuit.Realizes.onBinaryPrefix
    (right := comparisonWorkEncoding n)
    (activeScratchBToHistory_realizes n counterWidth historyIndex)

/-- Coefficient-work-lifted history-write atom for a staged branch-history code
bit. -/
def coeffWorkActiveScratchBToHistoryStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (liftedActiveScratchBToHistoryStep n counterWidth historyIndex)

/-- Gate list for the coefficient-work-lifted history-write atom. -/
def coeffWorkActiveScratchBToHistoryGates
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  (([activeScratchBToHistoryGate n counterWidth historyIndex].map
      (EncodedBit.GateSpec.prodLeft (comparisonWorkEncoding n))).map
    (EncodedBit.GateSpec.prodLeft (coeffAdderWorkEncoding n)))

/-- Base-gate program for the coefficient-work-lifted history-write atom. -/
def coeffWorkActiveScratchBToHistoryProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkActiveScratchBToHistoryGates n counterWidth historyIndex)

/-- The explicit coefficient-work-lifted history-write gate list has the
existing lifted semantic action. -/
theorem coeffWorkActiveScratchBToHistoryStep_eq_gateList
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkActiveScratchBToHistoryGates n counterWidth historyIndex) x =
      coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x := by
  unfold coeffWorkActiveScratchBToHistoryGates
    coeffWorkActiveScratchBToHistoryStep
    liftComparisonWorkStepToCoeffAdderWork
    liftedActiveScratchBToHistoryStep
    activeScratchBToHistoryStep
  unfold registersWithCoeffAdderWorkEncoding
    registersWithComparisonWorkEncoding
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  rfl

/-- The coefficient-work-lifted history-write program realizes the existing
semantic action. -/
theorem coeffWorkActiveScratchBToHistory_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveScratchBToHistoryProgram n counterWidth historyIndex)
      (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkActiveScratchBToHistoryGates n counterWidth historyIndex)
    (coeffWorkActiveScratchBToHistoryStep_eq_gateList n counterWidth
      historyIndex)

/-- Product lifting preserves the one-leaf history-write length. -/
theorem coeffWorkActiveScratchBToHistoryGates_length
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    (coeffWorkActiveScratchBToHistoryGates
      n counterWidth historyIndex).length = 1 := by
  unfold coeffWorkActiveScratchBToHistoryGates
    registersWithCoeffAdderWorkEncoding registersWithComparisonWorkEncoding
  simp

private theorem coeffWorkActiveScratchBToHistoryGates_events
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    (coeffWorkActiveScratchBToHistoryGates n counterWidth historyIndex).map
        (EncodedBit.GateSpec.event .empty) =
      [activeScratchBToHistoryGate n counterWidth historyIndex].map
        (EncodedBit.GateSpec.event .empty) := by
  unfold coeffWorkActiveScratchBToHistoryGates
    registersWithCoeffAdderWorkEncoding registersWithComparisonWorkEncoding
  rw [EncodedBit.GateSpec.map_event_prodLeft,
    EncodedBit.GateSpec.map_event_prodLeft]

/-- The lifted history-write atom contains no CNOT leaf. -/
theorem coeffWorkActiveScratchBToHistoryGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((coeffWorkActiveScratchBToHistoryGates n counterWidth historyIndex).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  calc
    ((coeffWorkActiveScratchBToHistoryGates n counterWidth historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
        ([activeScratchBToHistoryGate n counterWidth historyIndex].map
          EncodedBit.GateSpec.cnotMultiplicity).sum :=
      EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
        .empty
        (coeffWorkActiveScratchBToHistoryGates_events
          n counterWidth historyIndex)
    _ = 0 := by simp [activeScratchBToHistoryGate]

/-- The lifted history-write atom is exactly one Toffoli leaf. -/
theorem coeffWorkActiveScratchBToHistoryGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((coeffWorkActiveScratchBToHistoryGates n counterWidth historyIndex).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 1 := by
  calc
    ((coeffWorkActiveScratchBToHistoryGates n counterWidth historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
        ([activeScratchBToHistoryGate n counterWidth historyIndex].map
          EncodedBit.GateSpec.toffoliMultiplicity).sum :=
      EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
        .empty
        (coeffWorkActiveScratchBToHistoryGates_events
          n counterWidth historyIndex)
    _ = 1 := by simp [activeScratchBToHistoryGate]

/-- The coefficient-work-lifted history-write atom preserves the dedicated
coefficient-adder carry-in flag. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_carryIn
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- The coefficient-work-lifted history-write atom preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_carryWorkBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- The coefficient-work-lifted history-write atom preserves active. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_active
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  change (RegisterBits.activeBit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth historyIndex x.1.1) =
      (RegisterBits.activeBit n counterWidth).get x.1.1
  exact activeScratchBToHistoryStep_get_active n counterWidth historyIndex x.1.1

/-- The coefficient-work-lifted history-write atom preserves scratchA. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_scratchA
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  change (RegisterBits.scratchABit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth historyIndex x.1.1) =
      (RegisterBits.scratchABit n counterWidth).get x.1.1
  exact activeScratchBToHistoryStep_get_scratchA
    n counterWidth historyIndex x.1.1

/-- The coefficient-work-lifted history-write atom preserves scratchB. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_scratchB
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  change (RegisterBits.scratchBBit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth historyIndex x.1.1) =
      (RegisterBits.scratchBBit n counterWidth).get x.1.1
  exact activeScratchBToHistoryStep_get_scratchB
    n counterWidth historyIndex x.1.1

/-- The coefficient-work-lifted history-write atom preserves compare. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_compare
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  change (RegisterBits.compareBit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth historyIndex x.1.1) =
      (RegisterBits.compareBit n counterWidth).get x.1.1
  exact activeScratchBToHistoryStep_get_compare
    n counterWidth historyIndex x.1.1

/-- The coefficient-work-lifted history-write atom preserves every
comparison-work carry bit. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_comparisonCarry
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  rfl

/-- The coefficient-work-lifted history-write atom toggles the selected history
slot exactly under active and staged scratchB. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_historyBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x) =
      ((coeffAdderHistoryBit n counterWidth historyIndex).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderScratchBBit n counterWidth).get x)) := by
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (activeScratchBToHistoryStep n counterWidth historyIndex x.1.1) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x.1.1 ^^
        ((RegisterBits.activeBit n counterWidth).get x.1.1 &&
          (RegisterBits.scratchBBit n counterWidth).get x.1.1))
  exact activeScratchBToHistoryStep_get_historyBit
    n counterWidth historyIndex x.1.1

/-- The coefficient-work-lifted history-write atom preserves every history
slot except the selected target slot. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkActiveScratchBToHistoryStep n counterWidth target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  change (RegisterBits.historyBit n counterWidth observed).get
        (activeScratchBToHistoryStep n counterWidth target x.1.1) =
      (RegisterBits.historyBit n counterWidth observed).get x.1.1
  exact activeScratchBToHistoryStep_get_historyBit_of_ne
    n counterWidth target observed hne x.1.1

/-- The coefficient-work-lifted history-write atom preserves the `u` word. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_u
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  dsimp [coeffWorkActiveScratchBToHistoryStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedActiveScratchBToHistoryStep]
  simpa using activeScratchBToHistoryStep_get_of_history_ne
    n counterWidth historyIndex
    (RegisterBits.uValueBit n counterWidth bit)
    (by
      simpa [RegisterBits.uValueBit] using
        Ne.symm (RegisterBits.u_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit) historyIndex))
    x.1.1

/-- The coefficient-work-lifted history-write atom preserves the `v` word. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_v
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  dsimp [coeffWorkActiveScratchBToHistoryStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedActiveScratchBToHistoryStep]
  simpa using activeScratchBToHistoryStep_get_of_history_ne
    n counterWidth historyIndex
    (RegisterBits.vValueBit n counterWidth bit)
    (by
      simpa [RegisterBits.vValueBit] using
        Ne.symm (RegisterBits.v_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit) historyIndex))
    x.1.1

/-- The coefficient-work-lifted history-write atom preserves the `s`
coefficient word. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_sCoeff
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  dsimp [coeffWorkActiveScratchBToHistoryStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedActiveScratchBToHistoryStep]
  simpa using activeScratchBToHistoryStep_get_of_history_ne
    n counterWidth historyIndex
    (RegisterBits.sCoeffValueBit n counterWidth bit)
    (by
      simpa [RegisterBits.sCoeffValueBit] using
        Ne.symm (RegisterBits.sCoeff_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit) historyIndex))
    x.1.1

/-- The coefficient-work-lifted history-write atom preserves the `r`
coefficient word. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_rCoeff
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  dsimp [coeffWorkActiveScratchBToHistoryStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedActiveScratchBToHistoryStep]
  simpa using activeScratchBToHistoryStep_get_of_history_ne
    n counterWidth historyIndex
    (RegisterBits.rCoeffValueBit n counterWidth bit)
    (by
      simpa [RegisterBits.rCoeffValueBit] using
        Ne.symm (RegisterBits.rCoeff_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit) historyIndex))
    x.1.1

/-- The branch-history write atom preserves the physical padding counter. -/
theorem coeffWorkActiveScratchBToHistoryStep_get_counter
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveScratchBToHistoryStep
        n counterWidth historyIndex x).1.1.counter =
      x.1.1.counter := by
  apply word_eq_of_testBit_eq
  intro bit
  dsimp [coeffWorkActiveScratchBToHistoryStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedActiveScratchBToHistoryStep]
  simpa [RegisterBits.counterBit_get,
    WireAddress.bitIndex_littleEndianWire] using
    activeScratchBToHistoryStep_get_of_history_ne
      n counterWidth historyIndex
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire bit))
      (RegisterBits.history_counter_wire_ne n counterWidth historyIndex
        (WireAddress.littleEndianWire bit))
      x.1.1

/-- If the active flag is false, the active/scratchB history-write atom is a
no-op. -/
theorem coeffWorkActiveScratchBToHistoryStep_eq_self_of_active_false
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = false) :
    coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x = x := by
  change
    ((activeScratchBToHistoryStep n counterWidth historyIndex x.1.1, x.1.2),
        x.2) = x
  have hbase :
      activeScratchBToHistoryStep n counterWidth historyIndex x.1.1 =
        x.1.1 := by
    change
      EncodedBit.toffoliStep
          (RegisterBits.activeBit n counterWidth)
          (RegisterBits.scratchBBit n counterWidth)
          (RegisterBits.historyBit n counterWidth historyIndex)
          x.1.1 =
        x.1.1
    unfold EncodedBit.toffoliStep
    change (RegisterBits.activeBit n counterWidth).get x.1.1 = false
      at hactive
    simp [hactive]
  simp [hbase]

/-- Coefficient-work-lifted `uEven` branch-code staging preserves scratchB under
clean compare. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_scratchB_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  change (RegisterBits.scratchBBit n counterWidth).get
        (uEvenBranchCodeToScratchStep n counterWidth bit x.1.1) =
      (RegisterBits.scratchBBit n counterWidth).get x.1.1
  exact uEvenBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth bit x.1.1 hcompare

/-- Coefficient-work-lifted `uEven` branch-code staging preserves the observed
history slot. -/
theorem coeffWorkUEvenBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (uEvenBranchCodeToScratchStep n counterWidth bit x.1.1) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x.1.1
  exact uEvenBranchCodeToScratchStep_get_historyBit
    n counterWidth bit historyIndex x.1.1

/-- Coefficient-work-lifted `vEven` branch-code staging writes scratchB exactly
under the active `u`-odd/`v`-even condition. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_scratchB_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      ((coeffAdderScratchBBit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderUBit n counterWidth uIndex).get x &&
          !(coeffAdderVBit n counterWidth vIndex).get x)) := by
  change (RegisterBits.scratchBBit n counterWidth).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x.1.1) =
      ((RegisterBits.scratchBBit n counterWidth).get x.1.1 ^^
        ((RegisterBits.activeBit n counterWidth).get x.1.1 &&
          (RegisterBits.uBit n counterWidth uIndex).get x.1.1 &&
          !(RegisterBits.vBit n counterWidth vIndex).get x.1.1))
  exact vEvenBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth uIndex vIndex x.1.1 hcompare

/-- Coefficient-work-lifted `vEven` branch-code staging preserves the observed
history slot. -/
theorem coeffWorkVEvenBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
          x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (vEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x.1.1) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x.1.1
  exact vEvenBranchCodeToScratchStep_get_historyBit
    n counterWidth uIndex vIndex historyIndex x.1.1

/-! ## Explicit carried branch-code staging -/

/-- Lifted active-guarded branch-code staging for an already selected branch.
This is the fixed-branch hook used when the branch decision has been latched
before later data-path mutations. -/
def liftedActiveBranchCodeToScratchStep
    (n counterWidth : Nat) (branch : Branch) :
    RegistersWithComparisonWork n counterWidth ->
      RegistersWithComparisonWork n counterWidth :=
  fun x => (activeBranchCodeToScratchStep n counterWidth branch x.1, x.2)

/-- Actual circuit for lifted active-guarded carried branch-code staging. -/
def liftedActiveBranchCodeToScratchProgram
    (n counterWidth : Nat) (branch : Branch) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix (comparisonWorkEncoding n).width
    (activeBranchCodeToScratchProgram n counterWidth branch)

/-- The lifted carried-code circuit realizes the product action. -/
theorem liftedActiveBranchCodeToScratch_realizes
    (n counterWidth : Nat) (branch : Branch) :
    UnitaryCircuit.Realizes
      (registersWithComparisonWorkEncoding n counterWidth)
      (liftedActiveBranchCodeToScratchProgram n counterWidth branch)
      (liftedActiveBranchCodeToScratchStep n counterWidth branch) :=
  UnitaryCircuit.Realizes.onBinaryPrefix
    (right := comparisonWorkEncoding n)
    (activeBranchCodeToScratch_realizes n counterWidth branch)

/-- Lifted carried branch-code staging preserves active. -/
theorem liftedActiveBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (liftedActiveBranchCodeToScratchStep n counterWidth branch x) =
      (liftedActiveBit n counterWidth).get x := by
  change (RegisterBits.activeBit n counterWidth).get
        (activeBranchCodeToScratchStep n counterWidth branch x.1) =
      (RegisterBits.activeBit n counterWidth).get x.1
  exact activeBranchCodeToScratchStep_get_active n counterWidth branch x.1

/-- Lifted carried branch-code staging toggles scratchA by the carried auxiliary
code bit. -/
theorem liftedActiveBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (liftedActiveBranchCodeToScratchStep n counterWidth branch x) =
      ((liftedScratchABit n counterWidth).get x ^^
        ((liftedActiveBit n counterWidth).get x && branch.auxBit)) := by
  change (RegisterBits.scratchABit n counterWidth).get
        (activeBranchCodeToScratchStep n counterWidth branch x.1) =
      ((RegisterBits.scratchABit n counterWidth).get x.1 ^^
        ((RegisterBits.activeBit n counterWidth).get x.1 && branch.auxBit))
  exact activeBranchCodeToScratchStep_get_scratchA n counterWidth branch x.1

/-- Lifted carried branch-code staging toggles scratchB by the carried history
code bit. -/
theorem liftedActiveBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchBBit n counterWidth).get
        (liftedActiveBranchCodeToScratchStep n counterWidth branch x) =
      ((liftedScratchBBit n counterWidth).get x ^^
        ((liftedActiveBit n counterWidth).get x && branch.historyBit)) := by
  change (RegisterBits.scratchBBit n counterWidth).get
        (activeBranchCodeToScratchStep n counterWidth branch x.1) =
      ((RegisterBits.scratchBBit n counterWidth).get x.1 ^^
        ((RegisterBits.activeBit n counterWidth).get x.1 &&
          branch.historyBit))
  exact activeBranchCodeToScratchStep_get_scratchB n counterWidth branch x.1

/-- Lifted carried branch-code staging preserves each stored history bit. -/
theorem liftedActiveBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (branch : Branch) (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (liftedActiveBranchCodeToScratchStep n counterWidth branch x) =
      (liftedHistoryBit n counterWidth historyIndex).get x := by
  change (RegisterBits.historyBit n counterWidth historyIndex).get
        (activeBranchCodeToScratchStep n counterWidth branch x.1) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x.1
  exact activeBranchCodeToScratchStep_get_historyBit
    n counterWidth branch historyIndex x.1

/-- Coefficient-work-lifted active-guarded branch-code staging for an already
selected branch. -/
def coeffWorkActiveBranchCodeToScratchStep
    (n counterWidth : Nat) (branch : Branch) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (liftedActiveBranchCodeToScratchStep n counterWidth branch)

/-- Actual circuit for coefficient-work-lifted carried branch-code staging. -/
def coeffWorkActiveBranchCodeToScratchProgram
    (n counterWidth : Nat) (branch : Branch) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (liftedActiveBranchCodeToScratchProgram n counterWidth branch)

/-- The coefficient-work lifted carried-code circuit realizes its action. -/
theorem coeffWorkActiveBranchCodeToScratch_realizes
    (n counterWidth : Nat) (branch : Branch) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveBranchCodeToScratchProgram n counterWidth branch)
      (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch) :=
  liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (liftedActiveBranchCodeToScratch_realizes n counterWidth branch)

/-- Coefficient-work carried branch-code staging preserves the dedicated
coefficient-adder work object. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_coeffAdderWork
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x).2 =
      x.2 := by
  rfl

/-- Coefficient-work carried branch-code staging preserves carry-in. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_carryIn
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- Coefficient-work carried branch-code staging preserves every carry-work bit.
-/
theorem coeffWorkActiveBranchCodeToScratchStep_get_carryWorkBit
    (n counterWidth : Nat) (branch : Branch)
    (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- Coefficient-work carried branch-code staging preserves the `u` word. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_u
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x).1.1.u =
      x.1.1.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeBranchCodeToScratchStep_get_of_scratch_ne
    n counterWidth branch (RegisterBits.uValueBit n counterWidth bit)
    (by
      simpa [RegisterBits.uValueBit] using
        Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)))
    (by
      simpa [RegisterBits.uValueBit] using
        Ne.symm (RegisterBits.u_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)))
    x.1.1
  simpa [coeffWorkActiveBranchCodeToScratchStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedActiveBranchCodeToScratchStep] using h

/-- Coefficient-work carried branch-code staging preserves the `v` word. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_v
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x).1.1.v =
      x.1.1.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeBranchCodeToScratchStep_get_of_scratch_ne
    n counterWidth branch (RegisterBits.vValueBit n counterWidth bit)
    (by
      simpa [RegisterBits.vValueBit] using
        Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)))
    (by
      simpa [RegisterBits.vValueBit] using
        Ne.symm (RegisterBits.v_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)))
    x.1.1
  simpa [coeffWorkActiveBranchCodeToScratchStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedActiveBranchCodeToScratchStep] using h

/-- Coefficient-work carried branch-code staging preserves the `s` coefficient
word. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_sCoeff
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x).1.1.sCoeff =
      x.1.1.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeBranchCodeToScratchStep_get_of_scratch_ne
    n counterWidth branch (RegisterBits.sCoeffValueBit n counterWidth bit)
    (by
      simpa [RegisterBits.sCoeffValueBit] using
        Ne.symm (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)))
    (by
      simpa [RegisterBits.sCoeffValueBit] using
        Ne.symm (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)))
    x.1.1
  simpa [coeffWorkActiveBranchCodeToScratchStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedActiveBranchCodeToScratchStep] using h

/-- Coefficient-work carried branch-code staging preserves the `r` coefficient
word. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_rCoeff
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x).1.1.rCoeff =
      x.1.1.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeBranchCodeToScratchStep_get_of_scratch_ne
    n counterWidth branch (RegisterBits.rCoeffValueBit n counterWidth bit)
    (by
      simpa [RegisterBits.rCoeffValueBit] using
        Ne.symm (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)))
    (by
      simpa [RegisterBits.rCoeffValueBit] using
        Ne.symm (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)))
    x.1.1
  simpa [coeffWorkActiveBranchCodeToScratchStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedActiveBranchCodeToScratchStep] using h

/-- Carried branch-code staging preserves the complete physical padding
counter. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_counter
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveBranchCodeToScratchStep
        n counterWidth branch x).1.1.counter = x.1.1.counter := by
  change
    (activeBranchCodeToScratchStep n counterWidth branch x.1.1).counter =
      x.1.1.counter
  apply word_eq_of_testBit_eq
  intro bit
  simpa [RegisterBits.counterBit_get,
    WireAddress.bitIndex_littleEndianWire] using
    activeBranchCodeToScratchStep_get_of_scratch_ne
      n counterWidth branch
      (RegisterBits.counterBit n counterWidth
        (WireAddress.littleEndianWire bit))
      (RegisterBits.scratchA_counter_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))
      (RegisterBits.scratchB_counter_wire_ne n counterWidth
        (WireAddress.littleEndianWire bit))
      x.1.1

/-- Coefficient-work carried branch-code staging preserves active. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  change (liftedActiveBit n counterWidth).get
        (liftedActiveBranchCodeToScratchStep n counterWidth branch x.1) =
      (liftedActiveBit n counterWidth).get x.1
  exact liftedActiveBranchCodeToScratchStep_get_active
    n counterWidth branch x.1

/-- Coefficient-work carried branch-code staging toggles scratchA by the carried
auxiliary code bit. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x) =
      ((coeffAdderScratchABit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x && branch.auxBit)) := by
  change (liftedScratchABit n counterWidth).get
        (liftedActiveBranchCodeToScratchStep n counterWidth branch x.1) =
      ((liftedScratchABit n counterWidth).get x.1 ^^
        ((liftedActiveBit n counterWidth).get x.1 && branch.auxBit))
  exact liftedActiveBranchCodeToScratchStep_get_scratchA
    n counterWidth branch x.1

/-- On clean scratchA, coefficient-work carried branch-code staging writes the
active-guarded auxiliary code bit. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x) =
      ((coeffAdderActiveBit n counterWidth).get x && branch.auxBit) := by
  rw [coeffWorkActiveBranchCodeToScratchStep_get_scratchA]
  simp [hscratchA]

/-- Coefficient-work carried branch-code staging toggles scratchB by the carried
history code bit. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x) =
      ((coeffAdderScratchBBit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x && branch.historyBit)) := by
  change (liftedScratchBBit n counterWidth).get
        (liftedActiveBranchCodeToScratchStep n counterWidth branch x.1) =
      ((liftedScratchBBit n counterWidth).get x.1 ^^
        ((liftedActiveBit n counterWidth).get x.1 && branch.historyBit))
  exact liftedActiveBranchCodeToScratchStep_get_scratchB
    n counterWidth branch x.1

/-- On clean scratchB, coefficient-work carried branch-code staging writes the
active-guarded history code bit. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_scratchB_clean
    (n counterWidth : Nat) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x) =
      ((coeffAdderActiveBit n counterWidth).get x && branch.historyBit) := by
  rw [coeffWorkActiveBranchCodeToScratchStep_get_scratchB]
  simp [hscratchB]

/-- Coefficient-work carried branch-code staging preserves each stored history
bit. -/
theorem coeffWorkActiveBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (branch : Branch) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  change (liftedHistoryBit n counterWidth historyIndex).get
        (liftedActiveBranchCodeToScratchStep n counterWidth branch x.1) =
      (liftedHistoryBit n counterWidth historyIndex).get x.1
  exact liftedActiveBranchCodeToScratchStep_get_historyBit
    n counterWidth branch historyIndex x.1

/-- When the compare selector is true, coefficient-work-lifted
compare-conditioned `uGreater` staging matches the fixed carried `uGreater`
staging. -/
theorem
    coeffWorkUGreaterBranchCodeToScratchStep_eq_activeBranchCodeToScratchStep_clean_true
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = true) :
    coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x =
      coeffWorkActiveBranchCodeToScratchStep n counterWidth Branch.uGreater
        x := by
  have hregister :
      uGreaterBranchCodeToScratchStep n counterWidth x.1.1 =
        activeBranchCodeToScratchStep n counterWidth Branch.uGreater
          x.1.1 := by
    exact
      uGreaterBranchCodeToScratchStep_eq_activeBranchCodeToScratchStep_of_compare_true
        n counterWidth x.1.1
        (by simpa [coeffAdderCompareBit_get] using hcompare)
  simp [coeffWorkUGreaterBranchCodeToScratchStep,
    coeffWorkActiveBranchCodeToScratchStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedUGreaterBranchCodeToScratchStep,
    liftedActiveBranchCodeToScratchStep, hregister]

/-- When the compare selector is false, coefficient-work-lifted
compare-conditioned `uGreater` staging matches the fixed carried `vLe`
staging. -/
theorem
    coeffWorkUGreaterBranchCodeToScratchStep_eq_activeBranchCodeToScratchStep_clean_false
    (n counterWidth : Nat) (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x =
      coeffWorkActiveBranchCodeToScratchStep n counterWidth Branch.vLe
        x := by
  have hregister :
      uGreaterBranchCodeToScratchStep n counterWidth x.1.1 =
        activeBranchCodeToScratchStep n counterWidth Branch.vLe
          x.1.1 := by
    exact
      uGreaterBranchCodeToScratchStep_eq_activeBranchCodeToScratchStep_of_compare_false
        n counterWidth x.1.1
        (by simpa [coeffAdderCompareBit_get] using hcompare)
  simp [coeffWorkUGreaterBranchCodeToScratchStep,
    coeffWorkActiveBranchCodeToScratchStep,
    liftComparisonWorkStepToCoeffAdderWork,
    liftedUGreaterBranchCodeToScratchStep,
    liftedActiveBranchCodeToScratchStep, hregister]

/-- History write followed by the auxiliary active/branch-code shift dispatch.
-/
def coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
      (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x)

/-- Gate list for history write followed by auxiliary shift dispatch. -/
def coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  coeffWorkActiveScratchBToHistoryGates n counterWidth historyIndex ++
  coeffWorkAuxActiveShiftDispatchGates n counterWidth

/-- Base-gate program for history write followed by auxiliary shift dispatch. -/
def coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates
      n counterWidth historyIndex)

/-- The explicit history-write/auxiliary-shift-dispatch gate list has the
existing composite semantic action. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_eq_gateList
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates
          n counterWidth historyIndex) x =
      coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [coeffWorkActiveScratchBToHistoryStep_eq_gateList]
  rw [coeffWorkAuxActiveShiftDispatchStep_eq_gateList]
  rfl

/-- The history-write/auxiliary-shift-dispatch program realizes the existing
composite semantic action. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatch_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchProgram
        n counterWidth historyIndex)
      (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates
      n counterWidth historyIndex)
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_eq_gateList
      n counterWidth historyIndex)

/-- Exact physical length of history write followed by auxiliary shifts. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates_length
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates
      n counterWidth historyIndex).length = 9 * (n - 1) + 9 * n + 1 := by
  simp only [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates,
    List.length_append, coeffWorkActiveScratchBToHistoryGates_length,
    coeffWorkAuxActiveShiftDispatchGates_length]
  omega

/-- History write followed by auxiliary shifts contains no CNOT leaf. -/
theorem
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates
      n counterWidth historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates,
    List.map_append, List.sum_append,
    coeffWorkActiveScratchBToHistoryGates_cnotMultiplicity_sum,
    coeffWorkAuxActiveShiftDispatchGates_cnotMultiplicity_sum,
    Nat.zero_add]

/-- Exact Toffoli coordinate of history write followed by auxiliary shifts. -/
theorem
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates
      n counterWidth historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      9 * (n - 1) + 9 * n + 1 := by
  simp only [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates,
    List.map_append, List.sum_append,
    coeffWorkActiveScratchBToHistoryGates_toffoliMultiplicity_sum,
    coeffWorkAuxActiveShiftDispatchGates_toffoliMultiplicity_sum]
  omega

/-- If both dispatch controls are false, history write followed by auxiliary
shift dispatch is a no-op. -/
theorem
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_eq_self_of_active_false_scratchA_false
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false) :
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex x =
      x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [
    coeffWorkActiveScratchBToHistoryStep_eq_self_of_active_false
      n counterWidth historyIndex x hactive]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_self_of_active_false_scratchA_false
      n counterWidth x hactive hscratchA

/-- History write followed by auxiliary shift dispatch preserves the active
flag. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_active
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_active]
  exact coeffWorkActiveScratchBToHistoryStep_get_active
    n counterWidth historyIndex x

/-- History write followed by auxiliary shift dispatch preserves compare. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_compare
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex x) =
      (coeffAdderCompareBit n counterWidth).get x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_compare]
  exact coeffWorkActiveScratchBToHistoryStep_get_compare
    n counterWidth historyIndex x

/-- History write followed by auxiliary shift dispatch preserves scratchA. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchA
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_scratchA]
  exact coeffWorkActiveScratchBToHistoryStep_get_scratchA
    n counterWidth historyIndex x

/-- History write followed by auxiliary shift dispatch preserves scratchB. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchB
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_scratchB]
  exact coeffWorkActiveScratchBToHistoryStep_get_scratchB
    n counterWidth historyIndex x

/-- History write followed by auxiliary shift dispatch preserves every
history slot except the selected target slot. -/
theorem
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
          n counterWidth target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  exact coeffWorkActiveScratchBToHistoryStep_get_historyBit_of_ne
    n counterWidth target observed hne x

/-- History write followed by auxiliary shift dispatch preserves the physical
padding counter. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_counter
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex x).1.1.counter =
      x.1.1.counter := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  apply word_eq_of_testBit_eq
  intro bit
  have haux := coeffWorkAuxActiveShiftDispatchStep_get_counterValueBit
    n counterWidth bit
    (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex x)
  rw [coeffAdderCounterValueBit_get,
    coeffAdderCounterValueBit_get] at haux
  rw [haux, coeffWorkActiveScratchBToHistoryStep_get_counter]

/-- History write followed by auxiliary shift dispatch preserves the dedicated
coefficient-adder carry-in flag. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryIn
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_carryIn]
  exact coeffWorkActiveScratchBToHistoryStep_get_carryIn
    n counterWidth historyIndex x

/-- History write followed by auxiliary shift dispatch preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryWorkBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_carryWorkBit]
  exact coeffWorkActiveScratchBToHistoryStep_get_carryWorkBit
    n counterWidth historyIndex workBit x

/-- History write followed by auxiliary shift dispatch preserves each
comparison-work carry bit. -/
theorem
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_comparisonCarry
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_comparisonCarry]
  exact coeffWorkActiveScratchBToHistoryStep_get_comparisonCarry
    n counterWidth historyIndex workBit x

/-- Carried branch-code staging, history write, then auxiliary shift dispatch.
The branch is an explicit parameter, so callers can pass a decision latched
before an earlier data-path mutation. -/
def coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
      n counterWidth historyIndex
      (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x)

/-- Carried branch-code staging, history write, and auxiliary dispatch preserve
the complete physical padding counter. -/
theorem
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_counter
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex branch x).1.1.counter =
      x.1.1.counter := by
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_counter]
  exact coeffWorkActiveBranchCodeToScratchStep_get_counter
    n counterWidth branch x

/-- Actual circuit for carried branch-code staging followed by history write
and auxiliary shift dispatch. -/
def coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkActiveBranchCodeToScratchProgram n counterWidth branch)
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchProgram
      n counterWidth historyIndex)

/-- The carried-code/history/dispatch circuit realizes its composed action. -/
theorem coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatch_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchProgram
        n counterWidth historyIndex branch)
      (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex branch) := by
  unfold coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchProgram
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkActiveBranchCodeToScratchStep
      n counterWidth branch)
    (secondStep :=
      coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex)
    (coeffWorkActiveBranchCodeToScratch_realizes n counterWidth branch)
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatch_realizes
      n counterWidth historyIndex)

/-- Compare-conditioned carried odd branch-code staging, history write, then
auxiliary shift dispatch.  The fixed gate program writes the odd carried branch
code `(compare, compare)`: `compare = true` behaves as `uGreater`, while
`compare = false` leaves the scratch code as the `vLe` branch. -/
def coeffWorkCompareConditionedCarriedBranchDispatchStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
      n counterWidth historyIndex
      (coeffWorkUGreaterBranchCodeToScratchStep n counterWidth x)

/-- Gate list for compare-conditioned carried odd branch-code staging, history
write, and auxiliary shift dispatch. -/
def coeffWorkCompareConditionedCarriedBranchDispatchGates
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding n counterWidth)) :=
  coeffWorkUGreaterBranchCodeToScratchGates n counterWidth ++
  coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates
    n counterWidth historyIndex

/-- Base-gate program for compare-conditioned carried odd branch-code staging,
history write, and auxiliary shift dispatch. -/
def coeffWorkCompareConditionedCarriedBranchDispatchProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareConditionedCarriedBranchDispatchGates
      n counterWidth historyIndex)

/-- The explicit compare-conditioned carried-dispatch gate list has the existing
composite semantic action. -/
theorem coeffWorkCompareConditionedCarriedBranchDispatchStep_eq_gateList
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkCompareConditionedCarriedBranchDispatchGates
          n counterWidth historyIndex) x =
      coeffWorkCompareConditionedCarriedBranchDispatchStep
        n counterWidth historyIndex x := by
  rw [coeffWorkCompareConditionedCarriedBranchDispatchGates]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_eq_gateList]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_eq_gateList]
  rfl

/-- The compare-conditioned carried-dispatch program realizes the existing
composite semantic action. -/
theorem coeffWorkCompareConditionedCarriedBranchDispatch_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkCompareConditionedCarriedBranchDispatchProgram
        n counterWidth historyIndex)
      (coeffWorkCompareConditionedCarriedBranchDispatchStep
        n counterWidth historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkCompareConditionedCarriedBranchDispatchGates
      n counterWidth historyIndex)
    (coeffWorkCompareConditionedCarriedBranchDispatchStep_eq_gateList
      n counterWidth historyIndex)

/-- Exact physical length of compare-conditioned carried dispatch. -/
theorem coeffWorkCompareConditionedCarriedBranchDispatchGates_length
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    (coeffWorkCompareConditionedCarriedBranchDispatchGates
      n counterWidth historyIndex).length = 9 * (n - 1) + 9 * n + 3 := by
  simp only [coeffWorkCompareConditionedCarriedBranchDispatchGates,
    List.length_append, coeffWorkUGreaterBranchCodeToScratchGates_length,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates_length]
  omega

/-- Compare-conditioned carried dispatch contains no CNOT leaf. -/
theorem
    coeffWorkCompareConditionedCarriedBranchDispatchGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((coeffWorkCompareConditionedCarriedBranchDispatchGates
      n counterWidth historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [coeffWorkCompareConditionedCarriedBranchDispatchGates,
    List.map_append, List.sum_append,
    coeffWorkUGreaterBranchCodeToScratchGates_cnotMultiplicity_sum,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates_cnotMultiplicity_sum,
    Nat.zero_add]

/-- Exact Toffoli coordinate of compare-conditioned carried dispatch. -/
theorem
    coeffWorkCompareConditionedCarriedBranchDispatchGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((coeffWorkCompareConditionedCarriedBranchDispatchGates
      n counterWidth historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      9 * (n - 1) + 9 * n + 3 := by
  simp only [coeffWorkCompareConditionedCarriedBranchDispatchGates,
    List.map_append, List.sum_append,
    coeffWorkUGreaterBranchCodeToScratchGates_toffoliMultiplicity_sum,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates_toffoliMultiplicity_sum]
  omega

/-- Compare-conditioned carried branch-code/history/aux-shift dispatch
preserves every history slot except the selected target slot. -/
theorem
    coeffWorkCompareConditionedCarriedBranchDispatchStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkCompareConditionedCarriedBranchDispatchStep
          n counterWidth target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkCompareConditionedCarriedBranchDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    n counterWidth target observed hne]
  exact coeffWorkUGreaterBranchCodeToScratchStep_get_historyBit
    n counterWidth observed x

/-- Selector-selected odd data path followed by a concrete
compare-conditioned carried branch-code/history/aux-shift dispatch. -/
def coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithCoeffAdderWork tail.succ counterWidth ->
      RegistersWithCoeffAdderWork tail.succ counterWidth :=
  fun x =>
    coeffWorkCompareConditionedCarriedBranchDispatchStep
      tail.succ counterWidth historyIndex
      (coeffWorkCompareSelectorThenSelectedOddDataPathStep
        tail.succ counterWidth bit x)

/-- Gate list for the selector-selected odd data path followed by concrete
compare-conditioned carried branch-code/history/aux-shift dispatch. -/
def coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)) :=
  coeffWorkCompareSelectorThenSelectedOddDataPathGates
    tail.succ counterWidth bit ++
  coeffWorkCompareConditionedCarriedBranchDispatchGates
    tail.succ counterWidth historyIndex

/-- Base-gate program for selector-selected odd data path followed by concrete
compare-conditioned carried branch-code/history/aux-shift dispatch. -/
def coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchProgram
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth bit historyIndex)

/-- The explicit selector-selected-odd/compare-carried dispatch gate list has the
existing composite semantic action. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
          tail counterWidth bit historyIndex) x =
      coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex x := by
  rw [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [coeffWorkCompareSelectorThenSelectedOddDataPathStep_eq_gateList]
  rw [coeffWorkCompareConditionedCarriedBranchDispatchStep_eq_gateList]
  rfl

/-- The selector-selected-odd/compare-carried dispatch program realizes the
existing composite semantic action. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatch_realizes
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
      (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchProgram
        tail counterWidth bit historyIndex)
      (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth bit historyIndex)
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_gateList
      tail counterWidth bit historyIndex)

/-- Exact physical length of the selector-selected compare-carried source. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_length
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth bit historyIndex).length = 108 * tail + 75 := by
  simp only [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates,
    List.length_append,
    coeffWorkCompareSelectorThenSelectedOddDataPathGates_length,
    coeffWorkCompareConditionedCarriedBranchDispatchGates_length]
  omega

/-- Exact CNOT coordinate of the selector-selected compare-carried source. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth bit historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp only [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates,
    List.map_append, List.sum_append,
    coeffWorkCompareSelectorThenSelectedOddDataPathGates_cnotMultiplicity_sum,
    coeffWorkCompareConditionedCarriedBranchDispatchGates_cnotMultiplicity_sum,
    Nat.add_zero]

/-- Exact Toffoli coordinate of the selector-selected compare-carried source. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates
      tail counterWidth bit historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      104 * tail + 66 := by
  simp only [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchGates,
    List.map_append, List.sum_append,
    coeffWorkCompareSelectorThenSelectedOddDataPathGates_toffoliMultiplicity_sum,
    coeffWorkCompareConditionedCarriedBranchDispatchGates_toffoliMultiplicity_sum]
  omega

/-- On clean selected-control inputs, the concrete compare-carried odd route
preserves every history slot except the selected target slot. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_get_historyBit_of_ne_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (target observed : Fin (2 * tail.succ)) (hne : target ≠ observed)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth bit target
          ((x, cleanComparisonWork tail.succ), work)) =
      (RegisterBits.historyBit tail.succ counterWidth observed).get x := by
  rw [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep]
  rw [coeffWorkCompareConditionedCarriedBranchDispatchStep_get_historyBit_of_ne
    tail.succ counterWidth target observed hne]
  exact
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_historyBit
      tail.succ counterWidth bit observed x work hscratchA hcontrolWork

/-- In the active clean `v < u` case, the concrete compare-carried odd route
reduces to the `u/s` auxiliary-shift group after compare-conditioned carried
branch-code staging and history write. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_uShift_clean_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) =
      coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth
        (coeffWorkActiveScratchBToHistoryStep
          tail.succ counterWidth historyIndex
          (coeffWorkUGreaterBranchCodeToScratchStep
            tail.succ counterWidth
            (coeffWorkCompareSelectorThenSelectedOddDataPathStep
              tail.succ counterWidth bit
              ((x, cleanComparisonWork tail.succ), work)))) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep
      tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep
      tail.succ counterWidth historyIndex staged
  have hselectedScratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchA_clean
        tail.succ counterWidth bit x work hscratchA hcontrolWork
  have hselectedActive :
      (coeffAdderActiveBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
      tail.succ counterWidth bit x work hscratchA hcontrolWork]
    exact hactive
  have hselectedCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth bit x work hscratchA hcompare hfinal
      hcontrolWork]
    simp [hlt]
  have hactiveWritten :
      (coeffAdderActiveBit tail.succ counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_active]
    exact hselectedActive
  have hscratchAWritten :
      (coeffAdderScratchABit tail.succ counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_scratchA]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_scratchA]
    rw [hselectedScratchA, hselectedActive, hselectedCompare]
    simp
  rw [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep,
    coeffWorkCompareConditionedCarriedBranchDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_of_active_true_scratchA_true
      tail.succ counterWidth written hactiveWritten hscratchAWritten

/-- In the active clean non-`v < u` case, the concrete compare-carried odd route
reduces to the `v/r` auxiliary-shift group after compare-conditioned carried
branch-code staging and history write. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_vShift_clean_not_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) =
      coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth
        (coeffWorkActiveScratchBToHistoryStep
          tail.succ counterWidth historyIndex
          (coeffWorkUGreaterBranchCodeToScratchStep
            tail.succ counterWidth
            (coeffWorkCompareSelectorThenSelectedOddDataPathStep
              tail.succ counterWidth bit
              ((x, cleanComparisonWork tail.succ), work)))) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep
      tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep
      tail.succ counterWidth historyIndex staged
  have hselectedScratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchA_clean
        tail.succ counterWidth bit x work hscratchA hcontrolWork
  have hselectedActive :
      (coeffAdderActiveBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
      tail.succ counterWidth bit x work hscratchA hcontrolWork]
    exact hactive
  have hselectedCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth bit x work hscratchA hcompare hfinal
      hcontrolWork]
    simp [hnlt]
  have hactiveWritten :
      (coeffAdderActiveBit tail.succ counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_active]
    exact hselectedActive
  have hscratchAWritten :
      (coeffAdderScratchABit tail.succ counterWidth).get written = false := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_scratchA]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_scratchA]
    rw [hselectedScratchA, hselectedActive, hselectedCompare]
    simp
  rw [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep,
    coeffWorkCompareConditionedCarriedBranchDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_of_active_true_scratchA_false
      tail.succ counterWidth written hactiveWritten hscratchAWritten

/-- In the active clean `v < u` case, the concrete compare-carried odd route
keeps the active flag set. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_get_active_clean_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    (coeffAdderActiveBit tail.succ counterWidth).get
        (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      true := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep
      tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep
      tail.succ counterWidth historyIndex staged
  have hselectedActive :
      (coeffAdderActiveBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
      tail.succ counterWidth bit x work hscratchA hcontrolWork]
    exact hactive
  have hactiveWritten :
      (coeffAdderActiveBit tail.succ counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_active]
    exact hselectedActive
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hlt hcontrolWork hactive]
  rw [coeffWorkUDiv2ThenSMul2Step_get_active]
  exact hactiveWritten

/-- In the active clean non-`v < u` case, the concrete compare-carried odd route
keeps the active flag set. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_get_active_clean_not_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    (coeffAdderActiveBit tail.succ counterWidth).get
        (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      true := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep
      tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep
      tail.succ counterWidth historyIndex staged
  have hselectedActive :
      (coeffAdderActiveBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
      tail.succ counterWidth bit x work hscratchA hcontrolWork]
    exact hactive
  have hactiveWritten :
      (coeffAdderActiveBit tail.succ counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_active]
    exact hselectedActive
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hnlt hcontrolWork hactive]
  rw [coeffWorkVDiv2ThenRMul2Step_get_active]
  exact hactiveWritten

/-- In the clean `v < u` case, the concrete compare-carried odd route writes
the selected history slot with the carried `uGreater` history code. -/
theorem coeffWorkCompareCarriedDispatch_get_history_uGreater_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      ((RegisterBits.historyBit tail.succ counterWidth historyIndex).get x ^^
        (RegisterBits.activeBit tail.succ counterWidth).get x) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  have hselectedScratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchB
      tail.succ counterWidth bit x work hscratchA hcontrolWork]
    change x.scratchB = false
    exact hscratchB
  have hselectedCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth bit x work hscratchA hcompare hfinal
      hcontrolWork]
    simp [hlt]
  rw [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep,
    coeffWorkCompareConditionedCarriedBranchDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  rw [coeffWorkActiveScratchBToHistoryStep_get_historyBit]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_historyBit]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_active]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_scratchB]
  rw [hselectedScratchB, hselectedCompare]
  rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_historyBit
    tail.succ counterWidth bit historyIndex x work hscratchA hcontrolWork]
  rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
    tail.succ counterWidth bit x work hscratchA hcontrolWork]
  simp

/-- In the clean non-`v < u` case, the concrete compare-carried odd route
preserves the selected history slot because the carried history code is zero.
-/
theorem coeffWorkCompareCarriedDispatch_get_history_vLe_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  have hselectedScratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchB
      tail.succ counterWidth bit x work hscratchA hcontrolWork]
    change x.scratchB = false
    exact hscratchB
  have hselectedCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth bit x work hscratchA hcompare hfinal
      hcontrolWork]
    simp [hnlt]
  rw [coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep,
    coeffWorkCompareConditionedCarriedBranchDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  rw [coeffWorkActiveScratchBToHistoryStep_get_historyBit]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_historyBit]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_active]
  rw [coeffWorkUGreaterBranchCodeToScratchStep_get_scratchB]
  rw [hselectedScratchB, hselectedCompare]
  rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_historyBit
    tail.succ counterWidth bit historyIndex x work hscratchA hcontrolWork]
  rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
    tail.succ counterWidth bit x work hscratchA hcontrolWork]
  simp

/-- In the active clean `v < u` case, the concrete compare-carried odd route
writes `u := (u - v) / 2` when the selected subtraction result is even. -/
theorem
    coeffWorkCompareCarriedDispatch_get_u_uGreater_wordHalf_sub_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.u =
      wordHalf tail.succ (x.u - x.v) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hselectedU : selected.1.1.u = x.u - x.v := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_u_sub_clean_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hlt
        hcontrolWork hsourceWork
  have hstagedU : staged.1.1.u = x.u - x.v := by
    dsimp [staged]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_u, hselectedU]
  have hwrittenU : written.1.1.u = x.u - x.v := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_u, hstagedU]
  have hlsbWritten : written.1.1.u.val.testBit (0 : Nat) = false := by
    rw [hwrittenU]
    exact hlsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
      tail counterWidth written hlsbWritten
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hlt hcontrolWork hactive]
  change (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.u =
    wordHalf tail.succ (x.u - x.v)
  rw [hmain, hwrittenU]

/-- In the active clean `v < u` case, the concrete compare-carried odd route
preserves the selected `r := r + s` coefficient update. -/
theorem coeffWorkCompareCarriedDispatch_get_rCoeff_uGreater_add_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff =
      x.rCoeff + x.sCoeff := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hselectedR : selected.1.1.rCoeff = x.rCoeff + x.sCoeff := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_rCoeff_add_clean_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hlt
        hcontrolWork hcoeffWork
  have hstagedR : staged.1.1.rCoeff = x.rCoeff + x.sCoeff := by
    dsimp [staged]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_rCoeff, hselectedR]
  have hwrittenR : written.1.1.rCoeff = x.rCoeff + x.sCoeff := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_rCoeff, hstagedR]
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_rCoeff tail.succ counterWidth written
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hlt hcontrolWork hactive]
  change
      (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.rCoeff =
    x.rCoeff + x.sCoeff
  rw [hmain, hwrittenR]

/-- In the active clean `v < u` case, the concrete compare-carried odd route
writes `s := 2 * s` when the input coefficient top bit is false. -/
theorem
    coeffWorkCompareCarriedDispatch_get_sCoeff_uGreater_wordDouble_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff =
      wordDouble (tail.succ + 1) x.sCoeff := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hselectedS : selected.1.1.sCoeff = x.sCoeff := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_sCoeff_clean_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hlt
        hcontrolWork
  have hstagedS : staged.1.1.sCoeff = x.sCoeff := by
    dsimp [staged]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_sCoeff, hselectedS]
  have hwrittenS : written.1.1.sCoeff = x.sCoeff := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_sCoeff, hstagedS]
  have hmsbWritten :
      written.1.1.sCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenS]
    exact hmsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
      tail.succ counterWidth written hmsbWritten
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hlt hcontrolWork hactive]
  change
      (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.sCoeff =
    wordDouble (tail.succ + 1) x.sCoeff
  rw [hmain, hwrittenS]

/-- In the active clean non-`v < u` case, the concrete compare-carried odd
route writes `v := (v - u) / 2` when the selected subtraction result is even. -/
theorem coeffWorkCompareCarriedDispatch_get_v_vLe_wordHalf_sub_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.v =
      wordHalf tail.succ (x.v - x.u) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hselectedV : selected.1.1.v = x.v - x.u := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_v_sub_clean_not_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hnlt
        hcontrolWork hsourceWork
  have hstagedV : staged.1.1.v = x.v - x.u := by
    dsimp [staged]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_v, hselectedV]
  have hwrittenV : written.1.1.v = x.v - x.u := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_v, hstagedV]
  have hlsbWritten : written.1.1.v.val.testBit (0 : Nat) = false := by
    rw [hwrittenV]
    exact hlsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
      tail counterWidth written hlsbWritten
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hnlt hcontrolWork hactive]
  change (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.v =
    wordHalf tail.succ (x.v - x.u)
  rw [hmain, hwrittenV]

/-- In the active clean non-`v < u` case, the concrete compare-carried odd
route preserves the selected `s := s + r` coefficient update. -/
theorem coeffWorkCompareCarriedDispatch_get_sCoeff_vLe_add_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff =
      x.sCoeff + x.rCoeff := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hselectedS : selected.1.1.sCoeff = x.sCoeff + x.rCoeff := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_sCoeff_add_clean_not_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hnlt
        hcontrolWork hcoeffWork
  have hstagedS : staged.1.1.sCoeff = x.sCoeff + x.rCoeff := by
    dsimp [staged]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_sCoeff, hselectedS]
  have hwrittenS : written.1.1.sCoeff = x.sCoeff + x.rCoeff := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_sCoeff, hstagedS]
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_sCoeff tail.succ counterWidth written
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hnlt hcontrolWork hactive]
  change
      (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.sCoeff =
    x.sCoeff + x.rCoeff
  rw [hmain, hwrittenS]

/-- In the active clean non-`v < u` case, the concrete compare-carried odd
route writes `r := 2 * r` when the input coefficient top bit is false. -/
theorem coeffWorkCompareCarriedDispatch_get_rCoeff_vLe_wordDouble_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false) :
    (coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff =
      wordDouble (tail.succ + 1) x.rCoeff := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterBranchCodeToScratchStep tail.succ counterWidth selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hselectedR : selected.1.1.rCoeff = x.rCoeff := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_rCoeff_clean_not_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hnlt
        hcontrolWork
  have hstagedR : staged.1.1.rCoeff = x.rCoeff := by
    dsimp [staged]
    rw [coeffWorkUGreaterBranchCodeToScratchStep_get_rCoeff, hselectedR]
  have hwrittenR : written.1.1.rCoeff = x.rCoeff := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_rCoeff, hstagedR]
  have hmsbWritten :
      written.1.1.rCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenR]
    exact hmsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
      tail.succ counterWidth written hmsbWritten
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hnlt hcontrolWork hactive]
  change
      (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.rCoeff =
    wordDouble (tail.succ + 1) x.rCoeff
  rw [hmain, hwrittenR]

/-- Carried branch-code/history/aux-shift dispatch preserves the active flag. -/
theorem
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex branch x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_active]
  exact coeffWorkActiveBranchCodeToScratchStep_get_active
    n counterWidth branch x

/-- On clean scratchA, carried branch-code/history/aux-shift dispatch preserves
the staged auxiliary code bit. -/
theorem
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex branch x) =
      ((coeffAdderActiveBit n counterWidth).get x && branch.auxBit) := by
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchA]
  exact coeffWorkActiveBranchCodeToScratchStep_get_scratchA_clean
    n counterWidth branch x hscratchA

/-- On clean scratchB, carried branch-code/history/aux-shift dispatch preserves
the staged branch-history code bit. -/
theorem
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex branch x) =
      ((coeffAdderActiveBit n counterWidth).get x && branch.historyBit) := by
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchB]
  exact coeffWorkActiveBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth branch x hscratchB

/-- On clean scratchB, carried branch-code/history/aux-shift dispatch writes the
selected history slot under the carried branch history-code bit. -/
theorem
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth historyIndex branch x) =
      ((coeffAdderHistoryBit n counterWidth historyIndex).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x && branch.historyBit)) := by
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  rw [coeffWorkActiveScratchBToHistoryStep_get_historyBit]
  rw [coeffWorkActiveBranchCodeToScratchStep_get_historyBit]
  rw [coeffWorkActiveBranchCodeToScratchStep_get_active]
  rw [coeffWorkActiveBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth branch x hscratchB]
  cases (coeffAdderActiveBit n counterWidth).get x <;>
    cases branch.historyBit <;>
      simp

/-- Carried branch-code/history/aux-shift dispatch preserves every history
slot except the selected target slot. -/
theorem
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth target branch x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    n counterWidth target observed hne]
  exact coeffWorkActiveBranchCodeToScratchStep_get_historyBit
    n counterWidth branch observed x

/-- Under active carried auxiliary code one, the carried branch-code dispatch
reduces to the unconditioned `u/s` shift group after history write. -/
theorem
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (haux : branch.auxBit = true) :
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex branch x =
      coeffWorkUDiv2ThenSMul2Step n counterWidth
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex
          (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x)) := by
  let staged := coeffWorkActiveBranchCodeToScratchStep
    n counterWidth branch x
  let written :=
    coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex staged
  have hactiveWritten :
      (coeffAdderActiveBit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAWritten :
      (coeffAdderScratchABit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_scratchA]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_scratchA_clean
      n counterWidth branch x hscratchA]
    simp [hactive, haux]
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_of_active_true_scratchA_true
      n counterWidth written hactiveWritten hscratchAWritten

/-- Under active carried auxiliary code zero, the carried branch-code dispatch
reduces to the unconditioned `v/r` shift group after history write. -/
theorem
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (branch : Branch)
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (haux : branch.auxBit = false) :
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex branch x =
      coeffWorkVDiv2ThenRMul2Step n counterWidth
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex
          (coeffWorkActiveBranchCodeToScratchStep n counterWidth branch x)) := by
  let staged := coeffWorkActiveBranchCodeToScratchStep
    n counterWidth branch x
  let written :=
    coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex staged
  have hactiveWritten :
      (coeffAdderActiveBit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAWritten :
      (coeffAdderScratchABit n counterWidth).get written = false := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_scratchA]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_scratchA_clean
      n counterWidth branch x hscratchA]
    simp [hactive, haux]
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_of_active_true_scratchA_false
      n counterWidth written hactiveWritten hscratchAWritten

/-- Semantic wrapper that runs the clean comparison selector, the selected odd
data path, and then dispatches using the branch decision latched at the selector
output.  This avoids recomputing branch signals from the post-data-path state;
the data-dependent same-Circuit control object remains a later wrapper. -/
def coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithCoeffAdderWork tail.succ counterWidth ->
      RegistersWithCoeffAdderWork tail.succ counterWidth :=
  fun x =>
    let selected :=
      coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth bit x
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail.succ counterWidth historyIndex
      (Branch.fromCoeffWorkSignals tail.succ counterWidth selected)
      (coeffWorkCompareSelectedOddDataPathStep
        tail.succ counterWidth selected)

/-- On clean selected-control inputs, the latched carried odd route preserves
every history slot except the selected target slot. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_get_historyBit_of_ne_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (target observed : Fin (2 * tail.succ)) (hne : target ≠ observed)
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
          tail counterWidth bit target
          ((x, cleanComparisonWork tail.succ), work)) =
      (RegisterBits.historyBit tail.succ counterWidth observed).get x := by
  let selected :=
    coeffWorkUGreaterScratchACompareSelectorStep tail.succ counterWidth bit
      ((x, cleanComparisonWork tail.succ), work)
  rw [coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep]
  change
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail.succ counterWidth target
          (Branch.fromCoeffWorkSignals tail.succ counterWidth selected)
          (coeffWorkCompareSelectedOddDataPathStep
            tail.succ counterWidth selected)) =
      (RegisterBits.historyBit tail.succ counterWidth observed).get x
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    tail.succ counterWidth target observed hne]
  exact
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_historyBit
      tail.succ counterWidth bit observed x work hscratchA hcontrolWork

/-- The selector-selected carried odd route preserves the physical padding
counter on clean selected-control inputs. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_get_counter_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get x = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex x).1.1.counter =
      x.1.1.counter := by
  let selected :=
    coeffWorkUGreaterScratchACompareSelectorStep
      tail.succ counterWidth bit x
  have hselectedScratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_scratchA]
    exact hscratchA
  have hselectedControlWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get selected =
        false := by
    dsimp [selected]
    rw [coeffWorkUGreaterScratchACompareSelectorStep_get_coeffCarryIn]
    exact hcontrolWork
  rw [coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep]
  change
    (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
      tail.succ counterWidth historyIndex
      (Branch.fromCoeffWorkSignals tail.succ counterWidth selected)
      (coeffWorkCompareSelectedOddDataPathStep
        tail.succ counterWidth selected)).1.1.counter =
      x.1.1.counter
  rw [coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_counter]
  rw [coeffWorkCompareSelectedOddDataPathStep_get_counter_clean
    tail.succ counterWidth selected hselectedControlWork hselectedScratchA]
  exact coeffWorkUGreaterScratchACompareSelectorStep_get_counter
    tail.succ counterWidth bit x

/-- In the clean odd-odd `v < u` case, the selector-selected odd wrapper carries
the latched `uGreater` branch into history and auxiliary-shift dispatch. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uGreaterDispatch_clean_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val) :
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) =
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail.succ counterWidth historyIndex Branch.uGreater
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep
          tail.succ counterWidth bit
          ((x, cleanComparisonWork tail.succ), work)) := by
  rw [coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep,
    coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  rw [
    coeffWorkUGreaterScratchACompareSelectorStep_fromCoeffWorkSignals_uGreater_clean
      tail counterWidth bit x work hscratchA hcompare hfinal huOdd hvOdd hlt]

/-- In the clean odd-odd non-`v < u` case, the selector-selected odd wrapper
carries the latched `vLe` branch into history and auxiliary-shift dispatch. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vLeDispatch_clean_not_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val) :
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) =
      coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail.succ counterWidth historyIndex Branch.vLe
        (coeffWorkCompareSelectorThenSelectedOddDataPathStep
          tail.succ counterWidth bit
          ((x, cleanComparisonWork tail.succ), work)) := by
  rw [coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep,
    coeffWorkCompareSelectorThenSelectedOddDataPathStep]
  rw [
    coeffWorkUGreaterScratchACompareSelectorStep_fromCoeffWorkSignals_vLe_clean
      tail counterWidth bit x work hscratchA hcompare hfinal huOdd hvOdd hnlt]

/-- In the active clean odd-odd `v < u` case, the carried selector-selected odd
wrapper reduces to the `u/s` auxiliary-shift group after history write. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uShift_clean_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) =
      coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth
        (coeffWorkActiveScratchBToHistoryStep
          tail.succ counterWidth historyIndex
          (coeffWorkActiveBranchCodeToScratchStep
            tail.succ counterWidth Branch.uGreater
            (coeffWorkCompareSelectorThenSelectedOddDataPathStep
              tail.succ counterWidth bit
              ((x, cleanComparisonWork tail.succ), work)))) := by
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uGreaterDispatch_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt]
  exact
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
      tail.succ counterWidth historyIndex Branch.uGreater
      (coeffWorkCompareSelectorThenSelectedOddDataPathStep
        tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work))
      (coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchA_clean
        tail.succ counterWidth bit x work hscratchA hcontrolWork)
      (by
        rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
          tail.succ counterWidth bit x work hscratchA hcontrolWork]
        exact hactive)
      rfl

/-- In the active clean odd-odd non-`v < u` case, the carried selector-selected
odd wrapper reduces to the `v/r` auxiliary-shift group after history write. -/
theorem
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vShift_clean_not_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) =
      coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth
        (coeffWorkActiveScratchBToHistoryStep
          tail.succ counterWidth historyIndex
          (coeffWorkActiveBranchCodeToScratchStep
            tail.succ counterWidth Branch.vLe
            (coeffWorkCompareSelectorThenSelectedOddDataPathStep
              tail.succ counterWidth bit
              ((x, cleanComparisonWork tail.succ), work)))) := by
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vLeDispatch_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt]
  exact
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
      tail.succ counterWidth historyIndex Branch.vLe
      (coeffWorkCompareSelectorThenSelectedOddDataPathStep
        tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work))
      (coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchA_clean
        tail.succ counterWidth bit x work hscratchA hcontrolWork)
      (by
        rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
          tail.succ counterWidth bit x work hscratchA hcontrolWork]
        exact hactive)
      rfl

/-- In the active clean odd-odd `v < u` case, the older latched-branch odd
dispatch agrees with the concrete compare-carried dispatch. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_eq_compareCarriedDispatch_clean_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) =
      coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  have hselectedCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get selected = true := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth bit x work hscratchA hcompare hfinal
      hcontrolWork]
    simp [hlt]
  have hstage :
      coeffWorkUGreaterBranchCodeToScratchStep tail.succ counterWidth
          selected =
        coeffWorkActiveBranchCodeToScratchStep
          tail.succ counterWidth Branch.uGreater selected := by
    exact
      coeffWorkUGreaterBranchCodeToScratchStep_eq_activeBranchCodeToScratchStep_clean_true
        tail.succ counterWidth selected hselectedCompare
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt hcontrolWork hactive]
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hlt hcontrolWork hactive]
  rw [hstage]

/-- In the active clean odd-odd non-`v < u` case, the older latched-branch odd
dispatch agrees with the concrete compare-carried dispatch. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_eq_compareCarriedDispatch_clean_not_lt
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true) :
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) =
      coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep
      tail.succ counterWidth bit ((x, cleanComparisonWork tail.succ), work)
  have hselectedCompare :
      (coeffAdderCompareBit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    rw [coeffWorkCompareSelectorSelectedOddDataPathStep_get_compare_clean
      tail.succ counterWidth bit x work hscratchA hcompare hfinal
      hcontrolWork]
    simp [hnlt]
  have hstage :
      coeffWorkUGreaterBranchCodeToScratchStep tail.succ counterWidth
          selected =
        coeffWorkActiveBranchCodeToScratchStep
          tail.succ counterWidth Branch.vLe selected := by
    exact
      coeffWorkUGreaterBranchCodeToScratchStep_eq_activeBranchCodeToScratchStep_clean_false
        tail.succ counterWidth selected hselectedCompare
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt hcontrolWork hactive]
  rw [
    coeffWorkCompareSelectorSelectedOddThenCompareCarriedDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      hnlt hcontrolWork hactive]
  rw [hstage]

/-- In the clean odd-odd `v < u` case, the carried selector-selected odd
wrapper writes the selected history slot with the latched `uGreater` history
code. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_history_uGreater_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      ((RegisterBits.historyBit tail.succ counterWidth historyIndex).get x ^^
        (RegisterBits.activeBit tail.succ counterWidth).get x) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  have hselectedScratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    rw [
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchB
        tail.succ counterWidth bit x work hscratchA hcontrolWork]
    change x.scratchB = false
    exact hscratchB
  have hmain :=
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
      tail.succ counterWidth historyIndex Branch.uGreater selected
      hselectedScratchB
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uGreaterDispatch_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt]
  change
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
          (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
            tail.succ counterWidth historyIndex Branch.uGreater selected) =
        ((RegisterBits.historyBit tail.succ counterWidth historyIndex).get x ^^
          (RegisterBits.activeBit tail.succ counterWidth).get x)
  rw [hmain]
  rw [
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_historyBit
      tail.succ counterWidth bit historyIndex x work hscratchA hcontrolWork]
  rw [
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
      tail.succ counterWidth bit x work hscratchA hcontrolWork]
  simp [Branch.historyBit]

/-- In the clean odd-odd non-`v < u` case, the carried selector-selected odd
wrapper preserves the selected history slot because `vLe` has history code
zero. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_history_vLe_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hscratchB : x.scratchB = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
          tail counterWidth bit historyIndex
          ((x, cleanComparisonWork tail.succ), work)) =
      (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  have hselectedScratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get selected = false := by
    dsimp [selected]
    rw [
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_scratchB
        tail.succ counterWidth bit x work hscratchA hcontrolWork]
    change x.scratchB = false
    exact hscratchB
  have hmain :=
    coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
      tail.succ counterWidth historyIndex Branch.vLe selected
      hselectedScratchB
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vLeDispatch_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt]
  change
      (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
          (coeffWorkActiveBranchCodeThenHistoryThenAuxShiftDispatchStep
            tail.succ counterWidth historyIndex Branch.vLe selected) =
        (RegisterBits.historyBit tail.succ counterWidth historyIndex).get x
  rw [hmain]
  rw [
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_historyBit
      tail.succ counterWidth bit historyIndex x work hscratchA hcontrolWork]
  rw [
    coeffWorkCompareSelectorSelectedOddDataPathStep_get_active
      tail.succ counterWidth bit x work hscratchA hcontrolWork]
  simp [Branch.historyBit]

/-- In the active clean odd-odd `v < u` case, the carried selector-selected odd
wrapper writes `u := (u - v) / 2` when the selected subtraction result is even. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_u_uGreater_wordHalf_sub_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.u =
      wordHalf tail.succ (x.u - x.v) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkActiveBranchCodeToScratchStep tail.succ counterWidth
      Branch.uGreater selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hselectedU : selected.1.1.u = x.u - x.v := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_u_sub_clean_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hlt
        hcontrolWork hsourceWork
  have hstagedU : staged.1.1.u = x.u - x.v := by
    dsimp [staged]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_u, hselectedU]
  have hwrittenU : written.1.1.u = x.u - x.v := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_u, hstagedU]
  have hlsbWritten : written.1.1.u.val.testBit (0 : Nat) = false := by
    rw [hwrittenU]
    exact hlsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
      tail counterWidth written hlsbWritten
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt hcontrolWork hactive]
  change (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.u =
    wordHalf tail.succ (x.u - x.v)
  rw [hmain, hwrittenU]

/-- In the active clean odd-odd `v < u` case, the carried selector-selected odd
wrapper preserves the selected `r := r + s` coefficient update. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_rCoeff_uGreater_add_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff =
      x.rCoeff + x.sCoeff := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkActiveBranchCodeToScratchStep tail.succ counterWidth
      Branch.uGreater selected
  let written := coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth
    historyIndex staged
  have hselectedR : selected.1.1.rCoeff = x.rCoeff + x.sCoeff := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_rCoeff_add_clean_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hlt
        hcontrolWork hcoeffWork
  have hstagedR : staged.1.1.rCoeff = x.rCoeff + x.sCoeff := by
    dsimp [staged]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_rCoeff, hselectedR]
  have hwrittenR : written.1.1.rCoeff = x.rCoeff + x.sCoeff := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_rCoeff, hstagedR]
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_rCoeff tail.succ counterWidth written
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt hcontrolWork hactive]
  change (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.rCoeff =
    x.rCoeff + x.sCoeff
  rw [hmain, hwrittenR]

/-- In the active clean odd-odd `v < u` case, the carried selector-selected odd
wrapper writes `s := 2 * s` when the input coefficient top bit is false. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_sCoeff_uGreater_wordDouble_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hlt : x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hmsb : x.sCoeff.val.testBit (Fin.last tail.succ).val = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff =
      wordDouble (tail.succ + 1) x.sCoeff := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkActiveBranchCodeToScratchStep tail.succ counterWidth
      Branch.uGreater selected
  let written := coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth
    historyIndex staged
  have hselectedS : selected.1.1.sCoeff = x.sCoeff := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_sCoeff_clean_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hlt
        hcontrolWork
  have hstagedS : staged.1.1.sCoeff = x.sCoeff := by
    dsimp [staged]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_sCoeff, hselectedS]
  have hwrittenS : written.1.1.sCoeff = x.sCoeff := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_sCoeff, hstagedS]
  have hmsbWritten :
      written.1.1.sCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenS]
    exact hmsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
      tail.succ counterWidth written hmsbWritten
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_uShift_clean_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hlt hcontrolWork hactive]
  change (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.sCoeff =
    wordDouble (tail.succ + 1) x.sCoeff
  rw [hmain, hwrittenS]

/-- In the active clean odd-odd non-`v < u` case, the carried selector-selected
odd wrapper writes `v := (v - u) / 2` when the selected subtraction result is
even. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_v_vLe_wordHalf_sub_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hsourceWork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.v =
      wordHalf tail.succ (x.v - x.u) := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkActiveBranchCodeToScratchStep tail.succ counterWidth Branch.vLe
      selected
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hselectedV : selected.1.1.v = x.v - x.u := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_v_sub_clean_not_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hnlt
        hcontrolWork hsourceWork
  have hstagedV : staged.1.1.v = x.v - x.u := by
    dsimp [staged]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_v, hselectedV]
  have hwrittenV : written.1.1.v = x.v - x.u := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_v, hstagedV]
  have hlsbWritten : written.1.1.v.val.testBit (0 : Nat) = false := by
    rw [hwrittenV]
    exact hlsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
      tail counterWidth written hlsbWritten
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt hcontrolWork hactive]
  change (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.v =
    wordHalf tail.succ (x.v - x.u)
  rw [hmain, hwrittenV]

/-- In the active clean odd-odd non-`v < u` case, the carried selector-selected
odd wrapper preserves the selected `s := s + r` coefficient update. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_sCoeff_vLe_add_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hcoeffWork :
      ∀ k : Fin ((tail.succ + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.sCoeff =
      x.sCoeff + x.rCoeff := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkActiveBranchCodeToScratchStep tail.succ counterWidth Branch.vLe
      selected
  let written := coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth
    historyIndex staged
  have hselectedS : selected.1.1.sCoeff = x.sCoeff + x.rCoeff := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_sCoeff_add_clean_not_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hnlt
        hcontrolWork hcoeffWork
  have hstagedS : staged.1.1.sCoeff = x.sCoeff + x.rCoeff := by
    dsimp [staged]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_sCoeff, hselectedS]
  have hwrittenS : written.1.1.sCoeff = x.sCoeff + x.rCoeff := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_sCoeff, hstagedS]
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_sCoeff tail.succ counterWidth written
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt hcontrolWork hactive]
  change (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.sCoeff =
    x.sCoeff + x.rCoeff
  rw [hmain, hwrittenS]

/-- In the active clean odd-odd non-`v < u` case, the carried selector-selected
odd wrapper writes `r := 2 * r` when the input coefficient top bit is false. -/
theorem
    coeffWorkSelectedOddCarriedDispatch_get_rCoeff_vLe_wordDouble_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = tail.succ)
    (huOdd : x.u.val.testBit (0 : Nat) = true)
    (hvOdd : x.v.val.testBit (0 : Nat) = true)
    (hnlt : ¬ x.v.val < x.u.val)
    (hcontrolWork :
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get
          ((x, cleanComparisonWork tail.succ), work) = true)
    (hmsb : x.rCoeff.val.testBit (Fin.last tail.succ).val = false) :
    (coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep
        tail counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.rCoeff =
      wordDouble (tail.succ + 1) x.rCoeff := by
  let selected :=
    coeffWorkCompareSelectorThenSelectedOddDataPathStep tail.succ counterWidth
      bit ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkActiveBranchCodeToScratchStep tail.succ counterWidth Branch.vLe
      selected
  let written := coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth
    historyIndex staged
  have hselectedR : selected.1.1.rCoeff = x.rCoeff := by
    dsimp [selected]
    exact
      coeffWorkCompareSelectorSelectedOddDataPathStep_get_rCoeff_clean_not_lt
        tail.succ counterWidth bit x work hscratchA hcompare hfinal hnlt
        hcontrolWork
  have hstagedR : staged.1.1.rCoeff = x.rCoeff := by
    dsimp [staged]
    rw [coeffWorkActiveBranchCodeToScratchStep_get_rCoeff, hselectedR]
  have hwrittenR : written.1.1.rCoeff = x.rCoeff := by
    dsimp [written]
    rw [coeffWorkActiveScratchBToHistoryStep_get_rCoeff, hstagedR]
  have hmsbWritten :
      written.1.1.rCoeff.val.testBit (Fin.last tail.succ).val = false := by
    rw [hwrittenR]
    exact hmsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
      tail.succ counterWidth written hmsbWritten
  rw [
    coeffWorkCompareSelectorSelectedOddThenCarriedBranchDispatchStep_eq_vShift_clean_not_lt
      tail counterWidth bit historyIndex x work hscratchA hcompare hfinal
      huOdd hvOdd hnlt hcontrolWork hactive]
  change (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.rCoeff =
    wordDouble (tail.succ + 1) x.rCoeff
  rw [hmain, hwrittenR]

/-- Selected branch-code staging, history write, then auxiliary shift dispatch.
This is the gate-level selected branch-code hook into the existing auxiliary
shift dispatch. -/
def coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    RegistersWithCoeffAdderWork tail.succ counterWidth ->
      RegistersWithCoeffAdderWork tail.succ counterWidth :=
  fun x =>
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
      tail.succ counterWidth historyIndex
      (coeffWorkSelectedBranchCodeToScratchStep tail counterWidth tempIndex x)

/-- Gate list for selected branch-code staging, history write, and auxiliary
shift dispatch. -/
def coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    List (EncodedBit.GateSpec
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)) :=
  coeffWorkSelectedBranchCodeToScratchGates tail counterWidth tempIndex ++
  coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates
    tail.succ counterWidth historyIndex

/-- Base-gate program for selected branch-code staging, history write, and
auxiliary shift dispatch. -/
def coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchProgram
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding tail.succ counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex)

/-- The explicit selected branch-code/history/auxiliary-dispatch gate list has
the existing composite semantic action. -/
theorem coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    EncodedBit.GateSpec.stepList
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
          tail counterWidth tempIndex historyIndex) x =
      coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates]
  rw [EncodedBit.GateSpec.stepList_append]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_eq_gateList]
  rfl

/-- The selected branch-code/history/auxiliary-dispatch program realizes the
existing composite semantic action. -/
theorem coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatch_realizes
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)
      (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchProgram
        tail counterWidth tempIndex historyIndex)
      (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex)
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_gateList
      tail counterWidth tempIndex historyIndex)

/-- Exact physical length of the selected branch-code source. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_length
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex).length = 18 * tail + 24 := by
  simp only [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates,
    List.length_append, coeffWorkSelectedBranchCodeToScratchGates_length,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates_length]
  omega

/-- Exact CNOT coordinate of the selected branch-code source. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_cnotMultiplicity_sum
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp only [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates,
    List.map_append, List.sum_append,
    coeffWorkSelectedBranchCodeToScratchGates_cnotMultiplicity_sum,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates_cnotMultiplicity_sum,
    Nat.add_zero]

/-- Exact Toffoli coordinate of the selected branch-code source. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates_toffoliMultiplicity_sum
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) :
    ((coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates
      tail counterWidth tempIndex historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      18 * tail + 19 := by
  simp only [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchGates,
    List.map_append, List.sum_append,
    coeffWorkSelectedBranchCodeToScratchGates_toffoliMultiplicity_sum,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchGates_toffoliMultiplicity_sum]
  omega

/-- On inactive clean branch-code work, selected branch-code staging followed by
history write and auxiliary-shift dispatch is a no-op. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_self_of_active_false_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive :
      (coeffAdderActiveBit tail.succ counterWidth).get x = false) :
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x =
      x := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkSelectedBranchCodeToScratchStep_eq_self_of_active_false_clean
    tail counterWidth tempIndex x hscratchA hscratchB htemp hactive]
  exact
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_eq_self_of_active_false_scratchA_false
      tail.succ counterWidth historyIndex x hactive hscratchA

/-- Selected branch-code/history/aux-shift dispatch preserves the active flag.
-/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderActiveBit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      (coeffAdderActiveBit tail.succ counterWidth).get x := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_active]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_active
    tail counterWidth tempIndex x

/-- Selected branch-code/history/aux-shift dispatch preserves compare. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderCompareBit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      (coeffAdderCompareBit tail.succ counterWidth).get x := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_compare]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_compare
    tail counterWidth tempIndex x

/-- The complete selected even dispatcher preserves the physical padding
counter. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_counter
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x).1.1.counter =
      x.1.1.counter := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_counter]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_counter
    tail counterWidth tempIndex x

/-- On clean scratch/code-work inputs, selected branch-code/history/aux-shift
dispatch preserves the staged auxiliary code bit. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false) :
    (coeffAdderScratchABit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      ((coeffAdderActiveBit tail.succ counterWidth).get x &&
        (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit) := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchA]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_scratchA_clean
    tail counterWidth tempIndex x hscratchA hscratchB htemp

/-- On clean scratch/code-work inputs, selected branch-code/history/aux-shift
dispatch preserves the staged branch-history code bit. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false) :
    (coeffAdderScratchBBit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      ((coeffAdderActiveBit tail.succ counterWidth).get x &&
        (Branch.fromCoeffWorkSignals tail.succ counterWidth x).historyBit) := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchB]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_scratchB_clean
    tail counterWidth tempIndex x hscratchA hscratchB htemp

/-- On clean scratch/code-work inputs, selected branch-code/history/aux-shift
dispatch restores the selected comparison-carry temporary bit. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_comparisonCarry_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false) :
    (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      false := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_comparisonCarry]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_comparisonCarry_clean
    tail counterWidth tempIndex x hscratchA hscratchB htemp

/-- The selected branch-code/history/aux-shift composition preserves every
non-selected comparison-work bit. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_comparisonCarry_of_ne
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) (observed : Fin tail.succ)
    (hne : tempIndex ≠ observed)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderComparisonCarryBit tail.succ counterWidth observed).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      (coeffAdderComparisonCarryBit tail.succ counterWidth observed).get x := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_comparisonCarry]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_comparisonCarry_of_ne
    tail counterWidth tempIndex observed hne x

/-- The selected branch-code/history/aux-shift composition preserves the
dedicated coefficient-adder carry-in work bit. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryIn
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (liftedCoeffAdderCarryInBit tail.succ counterWidth).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      (liftedCoeffAdderCarryInBit tail.succ counterWidth).get x := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryIn]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_carryIn
    tail counterWidth tempIndex x

/-- The selected branch-code/history/aux-shift composition preserves every
dedicated coefficient-adder carry-work bit. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryWorkBit
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workBit : Fin ((tail.succ + 1) - 1))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord tail.succ counterWidth).bit workBit).get
        x := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryWorkBit]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_carryWorkBit
    tail counterWidth tempIndex workBit x

/-- On clean scratch/code-work inputs, selected branch-code/history/aux-shift
dispatch writes the selected history slot under the staged selected history
code bit. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false) :
    (coeffAdderHistoryBit tail.succ counterWidth historyIndex).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex historyIndex x) =
      ((coeffAdderHistoryBit tail.succ counterWidth historyIndex).get x ^^
        ((coeffAdderActiveBit tail.succ counterWidth).get x &&
          (Branch.fromCoeffWorkSignals tail.succ counterWidth x).historyBit)) := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  rw [coeffWorkActiveScratchBToHistoryStep_get_historyBit]
  rw [coeffWorkSelectedBranchCodeToScratchStep_get_historyBit]
  rw [coeffWorkSelectedBranchCodeToScratchStep_get_active]
  rw [coeffWorkSelectedBranchCodeToScratchStep_get_scratchB_clean
    tail counterWidth tempIndex x hscratchA hscratchB htemp]
  cases (coeffAdderActiveBit tail.succ counterWidth).get x <;>
    cases (Branch.fromCoeffWorkSignals tail.succ counterWidth x).historyBit <;>
      simp

/-- Selected branch-code/history/aux-shift dispatch preserves every history
slot except the selected target slot. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (target observed : Fin (2 * tail.succ)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (coeffAdderHistoryBit tail.succ counterWidth observed).get
        (coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
          tail counterWidth tempIndex target x) =
      (coeffAdderHistoryBit tail.succ counterWidth observed).get x := by
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    tail.succ counterWidth target observed hne]
  exact coeffWorkSelectedBranchCodeToScratchStep_get_historyBit
    tail counterWidth tempIndex observed x

/-- Under active selected auxiliary code one, the selected dispatch reduces to
the unconditioned `u/s` shift group after history write. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive : (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit = true) :
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x =
      coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth
        (coeffWorkActiveScratchBToHistoryStep
          tail.succ counterWidth historyIndex
          (coeffWorkSelectedBranchCodeToScratchStep
            tail counterWidth tempIndex x)) := by
  let staged := coeffWorkSelectedBranchCodeToScratchStep
    tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep
      tail.succ counterWidth historyIndex staged
  have hactiveWritten :
      (coeffAdderActiveBit tail.succ counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkSelectedBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAWritten :
      (coeffAdderScratchABit tail.succ counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_scratchA]
    rw [coeffWorkSelectedBranchCodeToScratchStep_get_scratchA_clean
      tail counterWidth tempIndex x hscratchA hscratchB htemp]
    simp [hactive, haux]
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_of_active_true_scratchA_true
      tail.succ counterWidth written hactiveWritten hscratchAWritten

/-- Under active selected auxiliary code zero, the selected dispatch reduces to
the unconditioned `v/r` shift group after history write. -/
theorem
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
    (tail counterWidth : Nat) (tempIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hscratchA :
      (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hscratchB :
      (coeffAdderScratchBBit tail.succ counterWidth).get x = false)
    (htemp :
      (coeffAdderComparisonCarryBit tail.succ counterWidth tempIndex).get x =
        false)
    (hactive : (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (haux :
      (Branch.fromCoeffWorkSignals tail.succ counterWidth x).auxBit = false) :
    coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail counterWidth tempIndex historyIndex x =
      coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth
        (coeffWorkActiveScratchBToHistoryStep
          tail.succ counterWidth historyIndex
          (coeffWorkSelectedBranchCodeToScratchStep
            tail counterWidth tempIndex x)) := by
  let staged := coeffWorkSelectedBranchCodeToScratchStep
    tail counterWidth tempIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep
      tail.succ counterWidth historyIndex staged
  have hactiveWritten :
      (coeffAdderActiveBit tail.succ counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkSelectedBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAWritten :
      (coeffAdderScratchABit tail.succ counterWidth).get written = false := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_scratchA]
    rw [coeffWorkSelectedBranchCodeToScratchStep_get_scratchA_clean
      tail counterWidth tempIndex x hscratchA hscratchB htemp]
    simp [hactive, haux]
  rw [coeffWorkSelectedBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_of_active_true_scratchA_false
      tail.succ counterWidth written hactiveWritten hscratchAWritten

/-- `uEven` branch-code staging, history write, then auxiliary shift dispatch. -/
def coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
      n counterWidth historyIndex
      (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x)

/-- Actual circuit for `uEven` branch-code staging, history write, and auxiliary
shift dispatch. -/
def coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUEvenBranchCodeToScratchProgram n counterWidth bit)
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchProgram
      n counterWidth historyIndex)

/-- The `uEven` code/history/dispatch circuit realizes its action. -/
theorem coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatch_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchProgram
        n counterWidth bit historyIndex)
      (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchProgram
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit)
    (secondStep :=
      coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex)
    (coeffWorkUEvenBranchCodeToScratch_realizes n counterWidth bit)
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatch_realizes
      n counterWidth historyIndex)

/-- The `uEven` branch-code/history/dispatch wrapper preserves the active
flag. -/
theorem coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth bit historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_active]
  exact coeffWorkUEvenBranchCodeToScratchStep_get_active
    n counterWidth bit x

/-- On clean compare, the `uEven` branch-code/history/dispatch wrapper
restores compare. -/
theorem
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth bit historyIndex x) =
      false := by
  rw [coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_compare]
  exact coeffWorkUEvenBranchCodeToScratchStep_get_compare_clean
    n counterWidth bit x hcompare

/-- On clean compare, the `uEven` branch-code/history/dispatch wrapper
preserves the staged scratchA equation. -/
theorem
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth bit historyIndex x) =
      ((coeffAdderScratchABit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          !(coeffAdderUBit n counterWidth bit).get x)) := by
  rw [coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchA]
  exact coeffWorkUEvenBranchCodeToScratchStep_get_scratchA_clean
    n counterWidth bit x hcompare

/-- On clean compare, the `uEven` branch-code/history/dispatch wrapper
preserves scratchB. -/
theorem
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth bit historyIndex x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  rw [coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchB]
  exact coeffWorkUEvenBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth bit x hcompare

/-- The `uEven` branch-code/history/dispatch wrapper preserves the dedicated
coefficient-adder carry-in flag. -/
theorem coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryIn
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth bit historyIndex x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rw [coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryIn]
  exact coeffWorkUEvenBranchCodeToScratchStep_get_carryIn
    n counterWidth bit x

/-- The `uEven` branch-code/history/dispatch wrapper preserves each
coefficient-adder temporary carry-work bit. -/
theorem
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryWorkBit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth bit historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rw [coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryWorkBit]
  exact coeffWorkUEvenBranchCodeToScratchStep_get_carryWorkBit
    n counterWidth bit workBit x

/-- On clean active `uEven` inputs, history write preserves the staged auxiliary
selector and the composed wrapper selects the unconditioned `u/s` shift group. -/
theorem
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hu : (coeffAdderUBit n counterWidth bit).get x = false) :
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth bit historyIndex x =
      coeffWorkUDiv2ThenSMul2Step n counterWidth
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex
          (coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x)) := by
  let staged := coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x
  let written := coeffWorkActiveScratchBToHistoryStep
    n counterWidth historyIndex staged
  have hactiveWritten :
      (coeffAdderActiveBit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkUEvenBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAWritten :
      (coeffAdderScratchABit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_scratchA]
    rw [coeffWorkUEvenBranchCodeToScratchStep_get_scratchA_clean
      n counterWidth bit x hcompare]
    simp [hscratchA, hactive, hu]
  rw [coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step_of_active_true_scratchA_true
      n counterWidth written hactiveWritten hscratchAWritten

/-- The `uEven` branch-code/history/dispatch wrapper leaves the selected
history slot unchanged when the staged history code bit is clean false. -/
theorem
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth bit historyIndex x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  rw [coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  rw [coeffWorkActiveScratchBToHistoryStep_get_historyBit]
  rw [coeffWorkUEvenBranchCodeToScratchStep_get_historyBit]
  rw [coeffWorkUEvenBranchCodeToScratchStep_get_active]
  rw [coeffWorkUEvenBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth bit x hcompare]
  simp [hscratchB]

/-- The `uEven` branch-code/history/dispatch wrapper preserves every history
slot except the selected target slot. -/
theorem
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth bit target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    n counterWidth target observed hne]
  exact coeffWorkUEvenBranchCodeToScratchStep_get_historyBit
    n counterWidth bit observed x

/-- The `uEven` branch-code/history/dispatch wrapper writes `u := u / 2` when
the staged branch is active and the source `u` word is even. -/
theorem
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_u_wordHalf_of_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hu : (coeffAdderUBit tail.succ counterWidth bit).get x = false)
    (hlsb : x.1.1.u.val.testBit (0 : Nat) = false) :
    (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail.succ counterWidth bit historyIndex x).1.1.u =
      wordHalf tail.succ x.1.1.u := by
  let staged :=
    coeffWorkUEvenBranchCodeToScratchStep tail.succ counterWidth bit x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hwrittenU : written.1.1.u = x.1.1.u := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_u]
    exact coeffWorkUEvenBranchCodeToScratchStep_get_u
      tail.succ counterWidth bit x
  have hlsbWritten : written.1.1.u.val.testBit (0 : Nat) = false := by
    rw [hwrittenU]
    exact hlsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
      tail counterWidth written hlsbWritten
  have hdispatch :=
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
      tail.succ counterWidth bit historyIndex x hcompare hscratchA hactive hu
  rw [hdispatch]
  change (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth written).1.1.u =
    wordHalf tail.succ x.1.1.u
  rw [hwrittenU] at hmain
  exact hmain

/-- The `uEven` branch-code/history/dispatch wrapper writes `s := 2 * s` when
the source coefficient top bit is false. -/
theorem
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_sCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hu : (coeffAdderUBit n counterWidth bit).get x = false)
    (hmsb : x.1.1.sCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth bit historyIndex x).1.1.sCoeff =
      wordDouble (n + 1) x.1.1.sCoeff := by
  let staged :=
    coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x
  let written :=
    coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex staged
  have hwrittenS : written.1.1.sCoeff = x.1.1.sCoeff := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_sCoeff]
    exact coeffWorkUEvenBranchCodeToScratchStep_get_sCoeff
      n counterWidth bit x
  have hmsbWritten :
      written.1.1.sCoeff.val.testBit (Fin.last n).val = false := by
    rw [hwrittenS]
    exact hmsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
      n counterWidth written hmsbWritten
  have hdispatch :=
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
      n counterWidth bit historyIndex x hcompare hscratchA hactive hu
  rw [hdispatch]
  change (coeffWorkUDiv2ThenSMul2Step n counterWidth written).1.1.sCoeff =
    wordDouble (n + 1) x.1.1.sCoeff
  rw [hwrittenS] at hmain
  exact hmain

/-- The `uEven` branch-code/history/dispatch wrapper preserves the untouched
`v` source word. -/
theorem coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_v
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hu : (coeffAdderUBit n counterWidth bit).get x = false) :
    (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth bit historyIndex x).1.1.v =
      x.1.1.v := by
  let staged := coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x
  let written :=
    coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex staged
  have hwrittenV : written.1.1.v = x.1.1.v := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_v]
    exact coeffWorkUEvenBranchCodeToScratchStep_get_v
      n counterWidth bit x
  have hdispatch :=
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
      n counterWidth bit historyIndex x hcompare hscratchA hactive hu
  rw [hdispatch]
  change (coeffWorkUDiv2ThenSMul2Step n counterWidth written).1.1.v =
    x.1.1.v
  rw [coeffWorkUDiv2ThenSMul2Step_get_v, hwrittenV]

/-- The `uEven` branch-code/history/dispatch wrapper preserves the untouched
`r` coefficient word. -/
theorem coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_rCoeff
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hu : (coeffAdderUBit n counterWidth bit).get x = false) :
    (coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth bit historyIndex x).1.1.rCoeff =
      x.1.1.rCoeff := by
  let staged := coeffWorkUEvenBranchCodeToScratchStep n counterWidth bit x
  let written :=
    coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex staged
  have hwrittenR : written.1.1.rCoeff = x.1.1.rCoeff := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_rCoeff]
    exact coeffWorkUEvenBranchCodeToScratchStep_get_rCoeff
      n counterWidth bit x
  have hdispatch :=
    coeffWorkUEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_uShift_clean
      n counterWidth bit historyIndex x hcompare hscratchA hactive hu
  rw [hdispatch]
  change (coeffWorkUDiv2ThenSMul2Step n counterWidth written).1.1.rCoeff =
    x.1.1.rCoeff
  rw [coeffWorkUDiv2ThenSMul2Step_get_rCoeff, hwrittenR]

/-- `vEven` branch-code staging, history write, then auxiliary shift dispatch. -/
def coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
      n counterWidth historyIndex
      (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x)

/-- Actual circuit for `vEven` branch-code staging, history write, and auxiliary
shift dispatch. -/
def coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVEvenBranchCodeToScratchProgram n counterWidth uIndex vIndex)
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchProgram
      n counterWidth historyIndex)

/-- The `vEven` code/history/dispatch circuit realizes its action. -/
theorem coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatch_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchProgram
        n counterWidth uIndex vIndex historyIndex)
      (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth uIndex vIndex historyIndex) := by
  unfold coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchProgram
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex)
    (secondStep :=
      coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep
        n counterWidth historyIndex)
    (coeffWorkVEvenBranchCodeToScratch_realizes n counterWidth uIndex vIndex)
    (coeffWorkActiveScratchBToHistoryThenAuxShiftDispatch_realizes
      n counterWidth historyIndex)

/-- The `vEven` branch-code/history/dispatch wrapper preserves the active
flag. -/
theorem coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_active
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth uIndex vIndex historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_active]
  exact coeffWorkVEvenBranchCodeToScratchStep_get_active
    n counterWidth uIndex vIndex x

/-- On clean compare, the `vEven` branch-code/history/dispatch wrapper
restores compare. -/
theorem
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_compare_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth uIndex vIndex historyIndex x) =
      false := by
  rw [coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_compare]
  exact coeffWorkVEvenBranchCodeToScratchStep_get_compare_clean
    n counterWidth uIndex vIndex x hcompare

/-- On clean compare, the `vEven` branch-code/history/dispatch wrapper
preserves scratchA. -/
theorem
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchA_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth uIndex vIndex historyIndex x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  rw [coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchA]
  exact coeffWorkVEvenBranchCodeToScratchStep_get_scratchA_clean
    n counterWidth uIndex vIndex x hcompare

/-- On clean compare, the `vEven` branch-code/history/dispatch wrapper
preserves the staged scratchB equation. -/
theorem
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_scratchB_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth uIndex vIndex historyIndex x) =
      ((coeffAdderScratchBBit n counterWidth).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderUBit n counterWidth uIndex).get x &&
          !(coeffAdderVBit n counterWidth vIndex).get x)) := by
  rw [coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_scratchB]
  exact coeffWorkVEvenBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth uIndex vIndex x hcompare

/-- The `vEven` branch-code/history/dispatch wrapper preserves the dedicated
coefficient-adder carry-in flag. -/
theorem coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryIn
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth uIndex vIndex historyIndex x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rw [coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryIn]
  exact coeffWorkVEvenBranchCodeToScratchStep_get_carryIn
    n counterWidth uIndex vIndex x

/-- The `vEven` branch-code/history/dispatch wrapper preserves each
coefficient-adder temporary carry-work bit. -/
theorem
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_carryWorkBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth uIndex vIndex historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rw [coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_carryWorkBit]
  exact coeffWorkVEvenBranchCodeToScratchStep_get_carryWorkBit
    n counterWidth uIndex vIndex workBit x

/-- On clean active `vEven` inputs, history write preserves the staged auxiliary
selector and the composed wrapper selects the unconditioned `v/r` shift group. -/
theorem
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true) :
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth uIndex vIndex historyIndex x =
      coeffWorkVDiv2ThenRMul2Step n counterWidth
        (coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex
          (coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex
            x)) := by
  let staged :=
    coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x
  let written := coeffWorkActiveScratchBToHistoryStep
    n counterWidth historyIndex staged
  have hactiveWritten :
      (coeffAdderActiveBit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_active]
    rw [coeffWorkVEvenBranchCodeToScratchStep_get_active]
    exact hactive
  have hscratchAWritten :
      (coeffAdderScratchABit n counterWidth).get written = false := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_scratchA]
    rw [coeffWorkVEvenBranchCodeToScratchStep_get_scratchA_clean
      n counterWidth uIndex vIndex x hcompare]
    exact hscratchA
  rw [coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step_of_active_true_scratchA_false
      n counterWidth written hactiveWritten hscratchAWritten

/-- The `vEven` branch-code/history/dispatch wrapper writes the selected
history slot under the active `u`-odd/`v`-even condition. -/
theorem
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_history_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth uIndex vIndex historyIndex x) =
      ((coeffAdderHistoryBit n counterWidth historyIndex).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderUBit n counterWidth uIndex).get x &&
          !(coeffAdderVBit n counterWidth vIndex).get x)) := by
  rw [coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep,
    coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  rw [coeffWorkActiveScratchBToHistoryStep_get_historyBit]
  rw [coeffWorkVEvenBranchCodeToScratchStep_get_historyBit]
  rw [coeffWorkVEvenBranchCodeToScratchStep_get_active]
  rw [coeffWorkVEvenBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth uIndex vIndex x hcompare]
  cases (coeffAdderActiveBit n counterWidth).get x <;>
    cases (coeffAdderUBit n counterWidth uIndex).get x <;>
      cases (coeffAdderVBit n counterWidth vIndex).get x <;>
        simp [hscratchB]

/-- The `vEven` branch-code/history/dispatch wrapper preserves every history
slot except the selected target slot. -/
theorem
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
          n counterWidth uIndex vIndex target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep]
  rw [coeffWorkActiveScratchBToHistoryThenAuxShiftDispatchStep_get_historyBit_of_ne
    n counterWidth target observed hne]
  exact coeffWorkVEvenBranchCodeToScratchStep_get_historyBit
    n counterWidth uIndex vIndex observed x

/-- The `vEven` branch-code/history/dispatch wrapper writes `v := v / 2` when
the staged branch is active and the source `v` word is even. -/
theorem
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_v_wordHalf_of_clean
    (tail counterWidth : Nat) (uIndex vIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcompare : (coeffAdderCompareBit tail.succ counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit tail.succ counterWidth).get x = true)
    (hlsb : x.1.1.v.val.testBit (0 : Nat) = false) :
    (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        tail.succ counterWidth uIndex vIndex historyIndex x).1.1.v =
      wordHalf tail.succ x.1.1.v := by
  let staged :=
    coeffWorkVEvenBranchCodeToScratchStep
      tail.succ counterWidth uIndex vIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep tail.succ counterWidth historyIndex
      staged
  have hwrittenV : written.1.1.v = x.1.1.v := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_v]
    exact coeffWorkVEvenBranchCodeToScratchStep_get_v
      tail.succ counterWidth uIndex vIndex x
  have hlsbWritten : written.1.1.v.val.testBit (0 : Nat) = false := by
    rw [hwrittenV]
    exact hlsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
      tail counterWidth written hlsbWritten
  have hdispatch :=
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
      tail.succ counterWidth uIndex vIndex historyIndex x hcompare hscratchA
      hactive
  rw [hdispatch]
  change (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth written).1.1.v =
    wordHalf tail.succ x.1.1.v
  rw [hwrittenV] at hmain
  exact hmain

/-- The `vEven` branch-code/history/dispatch wrapper writes `r := 2 * r` when
the source coefficient top bit is false. -/
theorem
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_rCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true)
    (hmsb : x.1.1.rCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth uIndex vIndex historyIndex x).1.1.rCoeff =
      wordDouble (n + 1) x.1.1.rCoeff := by
  let staged :=
    coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex staged
  have hwrittenR : written.1.1.rCoeff = x.1.1.rCoeff := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_rCoeff]
    exact coeffWorkVEvenBranchCodeToScratchStep_get_rCoeff
      n counterWidth uIndex vIndex x
  have hmsbWritten :
      written.1.1.rCoeff.val.testBit (Fin.last n).val = false := by
    rw [hwrittenR]
    exact hmsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
      n counterWidth written hmsbWritten
  have hdispatch :=
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
      n counterWidth uIndex vIndex historyIndex x hcompare hscratchA hactive
  rw [hdispatch]
  change (coeffWorkVDiv2ThenRMul2Step n counterWidth written).1.1.rCoeff =
    wordDouble (n + 1) x.1.1.rCoeff
  rw [hwrittenR] at hmain
  exact hmain

/-- The `vEven` branch-code/history/dispatch wrapper preserves the untouched
`u` source word. -/
theorem coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_u
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true) :
    (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth uIndex vIndex historyIndex x).1.1.u =
      x.1.1.u := by
  let staged :=
    coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex staged
  have hwrittenU : written.1.1.u = x.1.1.u := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_u]
    exact coeffWorkVEvenBranchCodeToScratchStep_get_u
      n counterWidth uIndex vIndex x
  have hdispatch :=
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
      n counterWidth uIndex vIndex historyIndex x hcompare hscratchA hactive
  rw [hdispatch]
  change (coeffWorkVDiv2ThenRMul2Step n counterWidth written).1.1.u =
    x.1.1.u
  rw [coeffWorkVDiv2ThenRMul2Step_get_u, hwrittenU]

/-- The `vEven` branch-code/history/dispatch wrapper preserves the untouched
`s` coefficient word. -/
theorem coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_get_sCoeff
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchA : (coeffAdderScratchABit n counterWidth).get x = false)
    (hactive : (coeffAdderActiveBit n counterWidth).get x = true) :
    (coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep
        n counterWidth uIndex vIndex historyIndex x).1.1.sCoeff =
      x.1.1.sCoeff := by
  let staged :=
    coeffWorkVEvenBranchCodeToScratchStep n counterWidth uIndex vIndex x
  let written :=
    coeffWorkActiveScratchBToHistoryStep n counterWidth historyIndex staged
  have hwrittenS : written.1.1.sCoeff = x.1.1.sCoeff := by
    dsimp [written, staged]
    rw [coeffWorkActiveScratchBToHistoryStep_get_sCoeff]
    exact coeffWorkVEvenBranchCodeToScratchStep_get_sCoeff
      n counterWidth uIndex vIndex x
  have hdispatch :=
    coeffWorkVEvenBranchCodeThenHistoryThenAuxShiftDispatchStep_eq_vShift_clean
      n counterWidth uIndex vIndex historyIndex x hcompare hscratchA hactive
  rw [hdispatch]
  change (coeffWorkVDiv2ThenRMul2Step n counterWidth written).1.1.sCoeff =
    x.1.1.sCoeff
  rw [coeffWorkVDiv2ThenRMul2Step_get_sCoeff, hwrittenS]

/-- Corrected `uGreater` subtract/add branch-code staging followed by the
auxiliary active/branch-code shift dispatch. -/
def coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
      (coeffWorkUGreaterSubAddBranchCodeToScratchStep n counterWidth bit
        historyIndex x)

/-- Actual circuit for corrected `uGreater` subtract/add branch-code staging
followed by the auxiliary shift dispatch. -/
def coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUGreaterSubAddBranchCodeToScratchProgram
      n counterWidth bit historyIndex)
    (coeffWorkAuxActiveShiftDispatchProgram n counterWidth)

/-- The corrected `uGreater` code/dispatch circuit realizes its action. -/
theorem coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatch_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchProgram
        n counterWidth bit historyIndex)
      (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchProgram
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkUGreaterSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex)
    (secondStep := coeffWorkAuxActiveShiftDispatchStep n counterWidth)
    (coeffWorkUGreaterSubAddBranchCodeToScratch_realizes
      n counterWidth bit historyIndex)
    (coeffWorkAuxActiveShiftDispatch_realizes n counterWidth)

/-- The corrected `uGreater` branch-code/dispatch wrapper preserves the active
flag. -/
theorem coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
          n counterWidth bit historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_active]
  exact coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_active
    n counterWidth bit historyIndex x

/-- On clean comparison inputs, the corrected `uGreater`
branch-code/dispatch wrapper preserves the staged `v < u` predicate. -/
theorem
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_compare]
  exact
    coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_compare_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- On clean active `uGreater` inputs, the corrected subtract/add
branch-code/dispatch wrapper selects the unconditioned `u/s` shift group. -/
theorem
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_eq_uShift_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hfinal : bit.val + 1 = n)
    (hgreater : decide (x.v.val < x.u.val) = true) :
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex ((x, cleanComparisonWork n), work) =
      coeffWorkUDiv2ThenSMul2Step n counterWidth
        (coeffWorkUGreaterSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) := by
  rw [coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxShiftDispatch_eq_uShift_after_uGreaterSubAddCode_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hactive
      hfinal hgreater

/-- The corrected `uGreater` branch-code/dispatch wrapper preserves the
selector's branch-history toggle through the auxiliary shift dispatch. -/
theorem
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val))) := by
  rw [coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  exact
    coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_history_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hscratchB
      hfinal

/-- The corrected `uGreater` branch-code/dispatch wrapper preserves every
history slot except the selected target slot. -/
theorem
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
          n counterWidth bit target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  exact
    coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_historyBit_of_ne
      n counterWidth bit target observed hne x

/-- Corrected `vLe` subtract/add branch-code staging followed by the auxiliary
active/branch-code shift dispatch. -/
def coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkAuxActiveShiftDispatchStep n counterWidth
      (coeffWorkVLeSubAddBranchCodeToScratchStep n counterWidth bit
        historyIndex x)

/-- Actual circuit for corrected `vLe` subtract/add branch-code staging
followed by the auxiliary shift dispatch. -/
def coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVLeSubAddBranchCodeToScratchProgram
      n counterWidth bit historyIndex)
    (coeffWorkAuxActiveShiftDispatchProgram n counterWidth)

/-- The corrected `vLe` code/dispatch circuit realizes its action. -/
theorem coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatch_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchProgram
        n counterWidth bit historyIndex)
      (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchProgram
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVLeSubAddBranchCodeToScratchStep
        n counterWidth bit historyIndex)
    (secondStep := coeffWorkAuxActiveShiftDispatchStep n counterWidth)
    (coeffWorkVLeSubAddBranchCodeToScratch_realizes
      n counterWidth bit historyIndex)
    (coeffWorkAuxActiveShiftDispatch_realizes n counterWidth)

/-- The corrected `vLe` branch-code/dispatch wrapper preserves the active flag.
-/
theorem coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderActiveBit n counterWidth).get
        (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
          n counterWidth bit historyIndex x) =
      (coeffAdderActiveBit n counterWidth).get x := by
  rw [coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_active]
  exact coeffWorkVLeSubAddBranchCodeToScratchStep_get_active
    n counterWidth bit historyIndex x

/-- On clean comparison inputs, the corrected `vLe` branch-code/dispatch
wrapper preserves the staged comparison predicate. -/
theorem coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_compare]
  exact
    coeffWorkVLeSubAddBranchCodeToScratchStep_get_compare_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- On clean active `vLe` inputs, the corrected subtract/add
branch-code/dispatch wrapper selects the unconditioned `v/r` shift group. -/
theorem coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_eq_vShift_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true) :
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex ((x, cleanComparisonWork n), work) =
      coeffWorkVDiv2ThenRMul2Step n counterWidth
        (coeffWorkVLeSubAddBranchCodeToScratchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) := by
  rw [coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep]
  exact
    coeffWorkAuxShiftDispatch_eq_vShift_after_vLeSubAddCode_clean
      n counterWidth bit historyIndex x work hscratchA hactive

/-- The corrected `vLe` branch-code/dispatch wrapper preserves the zero-code
branch-history no-op through the auxiliary shift dispatch. -/
theorem coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
          n counterWidth bit historyIndex
          ((x, cleanComparisonWork n), work)) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  rw [coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  exact
    coeffWorkVLeSubAddBranchCodeToScratchStep_get_history_clean
      n counterWidth bit historyIndex x work hscratchB

/-- The corrected `vLe` branch-code/dispatch wrapper preserves every history
slot except the selected target slot. -/
theorem
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
          n counterWidth bit target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  rw [coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep]
  rw [coeffWorkAuxActiveShiftDispatchStep_get_historyBit]
  exact
    coeffWorkVLeSubAddBranchCodeToScratchStep_get_historyBit_of_ne
      n counterWidth bit target observed hne x

/-! ## Coefficient-work-lifted even branch-history selectors -/

/-- Coefficient-work-lifted `uEven` branch-history slice.  This places the
concrete even-branch history writer in the same workspace as the later
coefficient data path [RNSL17, ECDLP.tex:468-475]. -/
def coeffWorkUEvenBranchHistoryWriteStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex)

/-- Actual circuit for the coefficient-work-lifted `uEven` branch-history
slice. -/
def coeffWorkUEvenBranchHistoryWriteProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (liftedUEvenBranchHistoryWriteProgram n counterWidth bit historyIndex)

/-- The coefficient-work-lifted `uEven` history circuit realizes its action. -/
theorem coeffWorkUEvenBranchHistoryWrite_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUEvenBranchHistoryWriteProgram
        n counterWidth bit historyIndex)
      (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex) :=
  liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (liftedUEvenBranchHistoryWrite_realizes
      n counterWidth bit historyIndex)

/-- Coefficient-work-lifted `vEven` branch-history slice. -/
def coeffWorkVEvenBranchHistoryWriteStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  liftComparisonWorkStepToCoeffAdderWork n counterWidth
    (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
      historyIndex)

/-- Actual circuit for the coefficient-work-lifted `vEven` branch-history
slice. -/
def coeffWorkVEvenBranchHistoryWriteProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  liftComparisonWorkProgramToCoeffAdderWork n counterWidth
    (liftedVEvenBranchHistoryWriteProgram
      n counterWidth uIndex vIndex historyIndex)

/-- The coefficient-work-lifted `vEven` history circuit realizes its action. -/
theorem coeffWorkVEvenBranchHistoryWrite_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVEvenBranchHistoryWriteProgram
        n counterWidth uIndex vIndex historyIndex)
      (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
        historyIndex) :=
  liftComparisonWorkProgramToCoeffAdderWork_realizes n counterWidth
    (liftedVEvenBranchHistoryWrite_realizes
      n counterWidth uIndex vIndex historyIndex)

/-- The coefficient-work-lifted `uEven` branch-history slice preserves the
dedicated coefficient-adder work object. -/
theorem coeffWorkUEvenBranchHistoryWriteStep_get_coeffAdderWork
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex x).2 =
      x.2 := by
  rfl

/-- The coefficient-work-lifted `vEven` branch-history slice preserves the
dedicated coefficient-adder work object. -/
theorem coeffWorkVEvenBranchHistoryWriteStep_get_coeffAdderWork
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
        historyIndex x).2 = x.2 := by
  rfl

/-- The coefficient-work-lifted `uEven` branch-history slice preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkUEvenBranchHistoryWriteStep_get_carryIn
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- The coefficient-work-lifted `vEven` branch-history slice preserves the
dedicated coefficient-adder carry-in flag. -/
theorem coeffWorkVEvenBranchHistoryWriteStep_get_carryIn
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (liftedCoeffAdderCarryInBit n counterWidth).get
        (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (liftedCoeffAdderCarryInBit n counterWidth).get x := by
  rfl

/-- The coefficient-work-lifted `uEven` branch-history slice preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkUEvenBranchHistoryWriteStep_get_carryWorkBit
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- The coefficient-work-lifted `vEven` branch-history slice preserves each
coefficient-adder temporary carry-work bit. -/
theorem coeffWorkVEvenBranchHistoryWriteStep_get_carryWorkBit
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (workBit : Fin ((n + 1) - 1))
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get
        (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      ((liftedCoeffAdderCarryWorkWord n counterWidth).bit workBit).get x := by
  rfl

/-- The coefficient-work-lifted `uEven` branch-history slice preserves every
comparison-work carry bit. -/
theorem coeffWorkUEvenBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (workBit : Fin n) (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  change (liftedComparisonCarryBit n counterWidth workBit).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x.1) =
      (liftedComparisonCarryBit n counterWidth workBit).get x.1
  exact liftedUEvenBranchHistoryWriteStep_get_comparisonCarry
    n counterWidth bit historyIndex workBit x.1

/-- The coefficient-work-lifted `vEven` branch-history slice preserves every
comparison-work carry bit. -/
theorem coeffWorkVEvenBranchHistoryWriteStep_get_comparisonCarry
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) (workBit : Fin n)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderComparisonCarryBit n counterWidth workBit).get
        (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (coeffAdderComparisonCarryBit n counterWidth workBit).get x := by
  change (liftedComparisonCarryBit n counterWidth workBit).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      (liftedComparisonCarryBit n counterWidth workBit).get x.1
  exact liftedVEvenBranchHistoryWriteStep_get_comparisonCarry
    n counterWidth uIndex vIndex historyIndex workBit x.1

/-- On clean compare and scratchB, the coefficient-work-lifted `uEven`
branch-history slice leaves the selected history bit unchanged. -/
theorem coeffWorkUEvenBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  change (liftedHistoryBit n counterWidth historyIndex).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x.1) =
      (liftedHistoryBit n counterWidth historyIndex).get x.1
  apply liftedUEvenBranchHistoryWriteStep_get_history_clean
  · change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
    exact hcompare
  · change (liftedScratchBBit n counterWidth).get x.1 = false at hscratchB
    exact hscratchB

/-- On clean compare and scratchB, the coefficient-work-lifted `vEven`
branch-history slice toggles the selected history bit under the staged
`u`-odd/`v`-even condition. -/
theorem coeffWorkVEvenBranchHistoryWriteStep_get_history_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      ((coeffAdderHistoryBit n counterWidth historyIndex).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderUBit n counterWidth uIndex).get x &&
          !(coeffAdderVBit n counterWidth vIndex).get x)) := by
  change (liftedHistoryBit n counterWidth historyIndex).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      ((liftedHistoryBit n counterWidth historyIndex).get x.1 ^^
        ((liftedActiveBit n counterWidth).get x.1 &&
          (liftedUBit n counterWidth uIndex).get x.1 &&
          !(liftedVBit n counterWidth vIndex).get x.1))
  apply liftedVEvenBranchHistoryWriteStep_get_history_clean
  · change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
    exact hcompare
  · change (liftedScratchBBit n counterWidth).get x.1 = false at hscratchB
    exact hscratchB

/-- The coefficient-work-lifted `uEven` branch-history slice preserves every
history slot except the selected target slot. -/
theorem coeffWorkUEvenBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (bit : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  change (liftedHistoryBit n counterWidth observed).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit target x.1) =
      (liftedHistoryBit n counterWidth observed).get x.1
  exact liftedUEvenBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth bit target observed hne x.1

/-- The coefficient-work-lifted `vEven` branch-history slice preserves every
history slot except the selected target slot. -/
theorem coeffWorkVEvenBranchHistoryWriteStep_get_historyBit_of_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (target observed : Fin (2 * n)) (hne : target ≠ observed)
    (x : RegistersWithCoeffAdderWork n counterWidth) :
    (coeffAdderHistoryBit n counterWidth observed).get
        (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          target x) =
      (coeffAdderHistoryBit n counterWidth observed).get x := by
  change (liftedHistoryBit n counterWidth observed).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          target x.1) =
      (liftedHistoryBit n counterWidth observed).get x.1
  exact liftedVEvenBranchHistoryWriteStep_get_historyBit_of_ne
    n counterWidth uIndex vIndex target observed hne x.1

/-- On clean compare, the coefficient-work-lifted `uEven` branch-history slice
restores compare. -/
theorem coeffWorkUEvenBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x) =
      false := by
  change (liftedCompareBit n counterWidth).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x.1) =
      false
  apply liftedUEvenBranchHistoryWriteStep_get_compare_clean
  change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- On clean compare, the coefficient-work-lifted `vEven` branch-history slice
restores compare. -/
theorem coeffWorkVEvenBranchHistoryWriteStep_get_compare_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      false := by
  change (liftedCompareBit n counterWidth).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      false
  apply liftedVEvenBranchHistoryWriteStep_get_compare_clean
  change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- On clean compare, the coefficient-work-lifted `uEven` branch-history slice
restores scratchA. -/
theorem coeffWorkUEvenBranchHistoryWriteStep_get_scratchA_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  change (liftedScratchABit n counterWidth).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x.1) =
      (liftedScratchABit n counterWidth).get x.1
  apply liftedUEvenBranchHistoryWriteStep_get_scratchA_clean
  change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- On clean compare, the coefficient-work-lifted `vEven` branch-history slice
restores scratchA. -/
theorem coeffWorkVEvenBranchHistoryWriteStep_get_scratchA_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchABit n counterWidth).get
        (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (coeffAdderScratchABit n counterWidth).get x := by
  change (liftedScratchABit n counterWidth).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      (liftedScratchABit n counterWidth).get x.1
  apply liftedVEvenBranchHistoryWriteStep_get_scratchA_clean
  change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- On clean compare, the coefficient-work-lifted `uEven` branch-history slice
restores scratchB. -/
theorem coeffWorkUEvenBranchHistoryWriteStep_get_scratchB_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  change (liftedScratchBBit n counterWidth).get
        (liftedUEvenBranchHistoryWriteStep n counterWidth bit historyIndex
          x.1) =
      (liftedScratchBBit n counterWidth).get x.1
  apply liftedUEvenBranchHistoryWriteStep_get_scratchB_clean
  change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-- On clean compare, the coefficient-work-lifted `vEven` branch-history slice
restores scratchB. -/
theorem coeffWorkVEvenBranchHistoryWriteStep_get_scratchB_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderScratchBBit n counterWidth).get
        (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x) =
      (coeffAdderScratchBBit n counterWidth).get x := by
  change (liftedScratchBBit n counterWidth).get
        (liftedVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
          historyIndex x.1) =
      (liftedScratchBBit n counterWidth).get x.1
  apply liftedVEvenBranchHistoryWriteStep_get_scratchB_clean
  change (liftedCompareBit n counterWidth).get x.1 = false at hcompare
  exact hcompare

/-! ## Branch-level cyclic-shift data-path scaffolds -/

/-- Coefficient-work-lifted `uEven` branch scaffold: write the branch-history
bit, then run the paired cyclic shifts for `u / 2` and `s * 2`.  This packages
the concrete gate-level branch data path from RNSL17, but does not yet prove
the arithmetic division/doubling invariant [RNSL17, ECDLP.tex:425-475]. -/
def coeffWorkUEvenSelectorThenShiftPairStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkUDiv2ThenSMul2Step n counterWidth
      (coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex x)

/-- Actual circuit for the coefficient-work-lifted `uEven`
selector-plus-shift data path. -/
def coeffWorkUEvenSelectorThenShiftPairProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUEvenBranchHistoryWriteProgram
      n counterWidth bit historyIndex)
    (coeffWorkUDiv2ThenSMul2Program n counterWidth)

/-- The `uEven` selector/shift circuit realizes its composed action. -/
theorem coeffWorkUEvenSelectorThenShiftPair_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUEvenSelectorThenShiftPairProgram
        n counterWidth bit historyIndex)
      (coeffWorkUEvenSelectorThenShiftPairStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkUEvenSelectorThenShiftPairProgram
    coeffWorkUEvenSelectorThenShiftPairStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkUEvenBranchHistoryWriteStep n counterWidth bit historyIndex)
    (secondStep := coeffWorkUDiv2ThenSMul2Step n counterWidth)
    (coeffWorkUEvenBranchHistoryWrite_realizes
      n counterWidth bit historyIndex)
    (coeffWorkUDiv2ThenSMul2_realizes n counterWidth)

/-- Coefficient-work-lifted `vEven` branch scaffold: write the branch-history
bit, then run the paired cyclic shifts for `v / 2` and `r * 2` [RNSL17,
ECDLP.tex:425-475]. -/
def coeffWorkVEvenSelectorThenShiftPairStep
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkVDiv2ThenRMul2Step n counterWidth
      (coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
        historyIndex x)

/-- Actual circuit for the coefficient-work-lifted `vEven`
selector-plus-shift data path. -/
def coeffWorkVEvenSelectorThenShiftPairProgram
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVEvenBranchHistoryWriteProgram
      n counterWidth uIndex vIndex historyIndex)
    (coeffWorkVDiv2ThenRMul2Program n counterWidth)

/-- The `vEven` selector/shift circuit realizes its composed action. -/
theorem coeffWorkVEvenSelectorThenShiftPair_realizes
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVEvenSelectorThenShiftPairProgram
        n counterWidth uIndex vIndex historyIndex)
      (coeffWorkVEvenSelectorThenShiftPairStep
        n counterWidth uIndex vIndex historyIndex) := by
  unfold coeffWorkVEvenSelectorThenShiftPairProgram
    coeffWorkVEvenSelectorThenShiftPairStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVEvenBranchHistoryWriteStep n counterWidth uIndex vIndex
        historyIndex)
    (secondStep := coeffWorkVDiv2ThenRMul2Step n counterWidth)
    (coeffWorkVEvenBranchHistoryWrite_realizes
      n counterWidth uIndex vIndex historyIndex)
    (coeffWorkVDiv2ThenRMul2_realizes n counterWidth)

/-- Legacy coefficient-work-lifted `uGreater` add-only branch scaffold: run the
selector, controlled swap-and-add data path, and then the paired cyclic shifts.
This is a same-circuit object for the older add path only; the corrected
subtract/add odd branch scaffold is below [RNSL17, ECDLP.tex:425-475]. -/
def coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkUDiv2ThenSMul2Step n counterWidth
      (coeffWorkUGreaterSelectorThenAddRIntoSStep n counterWidth bit
        historyIndex x)

/-- Actual circuit for the coefficient-work-lifted `uGreater`
selector-plus-add-plus-shift data path. -/
def coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUGreaterSelectorThenAddRIntoSProgram
      n counterWidth bit historyIndex)
    (coeffWorkUDiv2ThenSMul2Program n counterWidth)

/-- The legacy `uGreater` add/shift circuit realizes its composed action. -/
theorem coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPair_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairProgram
        n counterWidth bit historyIndex)
      (coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairProgram
    coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkUGreaterSelectorThenAddRIntoSStep n counterWidth bit
        historyIndex)
    (secondStep := coeffWorkUDiv2ThenSMul2Step n counterWidth)
    (coeffWorkUGreaterSelectorThenAddRIntoS_realizes
      n counterWidth bit historyIndex)
    (coeffWorkUDiv2ThenSMul2_realizes n counterWidth)

/-- Legacy coefficient-work-lifted `vLe` add-only branch scaffold: run the
selector, controlled swap-and-add data path, and then the paired cyclic shifts.
This is a same-circuit object for the older add path only; the corrected
subtract/add odd branch scaffold is below [RNSL17, ECDLP.tex:425-475]. -/
def coeffWorkVLeSelectorThenAddSIntoRThenShiftPairStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkVDiv2ThenRMul2Step n counterWidth
      (coeffWorkVLeSelectorThenAddSIntoRStep n counterWidth bit historyIndex
        x)

/-- Actual circuit for the coefficient-work-lifted `vLe`
selector-plus-add-plus-shift data path. -/
def coeffWorkVLeSelectorThenAddSIntoRThenShiftPairProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVLeSelectorThenAddSIntoRProgram
      n counterWidth bit historyIndex)
    (coeffWorkVDiv2ThenRMul2Program n counterWidth)

/-- The legacy `vLe` add/shift circuit realizes its composed action. -/
theorem coeffWorkVLeSelectorThenAddSIntoRThenShiftPair_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVLeSelectorThenAddSIntoRThenShiftPairProgram
        n counterWidth bit historyIndex)
      (coeffWorkVLeSelectorThenAddSIntoRThenShiftPairStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkVLeSelectorThenAddSIntoRThenShiftPairProgram
    coeffWorkVLeSelectorThenAddSIntoRThenShiftPairStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVLeSelectorThenAddSIntoRStep n counterWidth bit historyIndex)
    (secondStep := coeffWorkVDiv2ThenRMul2Step n counterWidth)
    (coeffWorkVLeSelectorThenAddSIntoR_realizes
      n counterWidth bit historyIndex)
    (coeffWorkVDiv2ThenRMul2_realizes n counterWidth)

/-- Corrected coefficient-work-lifted `uGreater` branch scaffold: run the
selector/history slice, the concrete `u := u - v; r := r + s` data path, and
then the paired `u / 2, s * 2` shifts. -/
def coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkUDiv2ThenSMul2Step n counterWidth
      (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
        n counterWidth bit historyIndex x)

/-- Actual circuit for the corrected `uGreater`
selector-plus-subtract-plus-add-plus-shift data path. -/
def coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRProgram
      n counterWidth bit historyIndex)
    (coeffWorkUDiv2ThenSMul2Program n counterWidth)

/-- The corrected `uGreater` branch circuit realizes its composed action. -/
theorem
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPair_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairProgram
        n counterWidth bit historyIndex)
      (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep
        n counterWidth bit historyIndex) := by
  unfold
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairProgram
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
        n counterWidth bit historyIndex)
    (secondStep := coeffWorkUDiv2ThenSMul2Step n counterWidth)
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoR_realizes
      n counterWidth bit historyIndex)
    (coeffWorkUDiv2ThenSMul2_realizes n counterWidth)

/-- Corrected coefficient-work-lifted `vLe` branch scaffold: run the
selector/history slice, the concrete `v := v - u; s := s + r` data path, and
then the paired `v / 2, r * 2` shifts. -/
def coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    RegistersWithCoeffAdderWork n counterWidth ->
      RegistersWithCoeffAdderWork n counterWidth :=
  fun x =>
    coeffWorkVDiv2ThenRMul2Step n counterWidth
      (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
        n counterWidth bit historyIndex x)

/-- Actual circuit for the corrected `vLe`
selector-plus-subtract-plus-add-plus-shift data path. -/
def coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairProgram
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCoeffAdderWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSProgram
      n counterWidth bit historyIndex)
    (coeffWorkVDiv2ThenRMul2Program n counterWidth)

/-- The corrected `vLe` branch circuit realizes its composed action. -/
theorem
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPair_realizes
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes
      (registersWithCoeffAdderWorkEncoding n counterWidth)
      (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairProgram
        n counterWidth bit historyIndex)
      (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep
        n counterWidth bit historyIndex) := by
  unfold coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairProgram
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep :=
      coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
        n counterWidth bit historyIndex)
    (secondStep := coeffWorkVDiv2ThenRMul2Step n counterWidth)
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoS_realizes
      n counterWidth bit historyIndex)
    (coeffWorkVDiv2ThenRMul2_realizes n counterWidth)

/-- On clean compare, the `uEven` selector-plus-shift branch restores the
comparison ancilla after branch-code staging and the paired `u/s` shifts. -/
theorem coeffWorkUEvenSelectorThenShiftPairStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUEvenSelectorThenShiftPairStep n counterWidth bit
          historyIndex x) =
      false := by
  rw [coeffWorkUEvenSelectorThenShiftPairStep]
  rw [coeffWorkUDiv2ThenSMul2Step_get_compare]
  exact coeffWorkUEvenBranchHistoryWriteStep_get_compare_clean
    n counterWidth bit historyIndex x hcompare

/-- On clean compare and scratchB, the `uEven` selector-plus-shift branch
preserves the selected history bit through the paired `u/s` shifts. -/
theorem coeffWorkUEvenSelectorThenShiftPairStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUEvenSelectorThenShiftPairStep n counterWidth bit
          historyIndex x) =
      (coeffAdderHistoryBit n counterWidth historyIndex).get x := by
  rw [coeffWorkUEvenSelectorThenShiftPairStep]
  rw [coeffWorkUDiv2ThenSMul2Step_get_historyBit]
  exact coeffWorkUEvenBranchHistoryWriteStep_get_history_clean
    n counterWidth bit historyIndex x hcompare hscratchB

/-- On clean compare, the `vEven` selector-plus-shift branch restores the
comparison ancilla after branch-code staging and the paired `v/r` shifts. -/
theorem coeffWorkVEvenSelectorThenShiftPairStep_get_compare_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVEvenSelectorThenShiftPairStep n counterWidth uIndex vIndex
          historyIndex x) =
      false := by
  rw [coeffWorkVEvenSelectorThenShiftPairStep]
  rw [coeffWorkVDiv2ThenRMul2Step_get_compare]
  exact coeffWorkVEvenBranchHistoryWriteStep_get_compare_clean
    n counterWidth uIndex vIndex historyIndex x hcompare

/-- On clean compare and scratchB, the `vEven` selector-plus-shift branch
preserves the staged history toggle through the paired `v/r` shifts. -/
theorem coeffWorkVEvenSelectorThenShiftPairStep_get_history_clean
    (n counterWidth : Nat) (uIndex vIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcompare : (coeffAdderCompareBit n counterWidth).get x = false)
    (hscratchB : (coeffAdderScratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVEvenSelectorThenShiftPairStep n counterWidth uIndex vIndex
          historyIndex x) =
      ((coeffAdderHistoryBit n counterWidth historyIndex).get x ^^
        ((coeffAdderActiveBit n counterWidth).get x &&
          (coeffAdderUBit n counterWidth uIndex).get x &&
          !(coeffAdderVBit n counterWidth vIndex).get x)) := by
  rw [coeffWorkVEvenSelectorThenShiftPairStep]
  rw [coeffWorkVDiv2ThenRMul2Step_get_historyBit]
  exact coeffWorkVEvenBranchHistoryWriteStep_get_history_clean
    n counterWidth uIndex vIndex historyIndex x hcompare hscratchB

/-- On clean comparison inputs, the `uGreater` selector-plus-add-plus-shift
branch keeps the staged `v < u` predicate available through the paired `u/s`
shifts. -/
theorem
    coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairStep n counterWidth
          bit historyIndex ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairStep]
  rw [coeffWorkUDiv2ThenSMul2Step_get_compare]
  exact coeffWorkUGreaterSelectorThenAddRIntoSStep_get_compare_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- On clean inputs, the `uGreater` selector-plus-add-plus-shift branch
preserves the selector's history toggle through the paired `u/s` shifts. -/
theorem
    coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairStep n counterWidth
          bit historyIndex ((x, cleanComparisonWork n), work)) =
      ((RegisterBits.historyBit n counterWidth historyIndex).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          decide (x.v.val < x.u.val))) := by
  rw [coeffWorkUGreaterSelectorThenAddRIntoSThenShiftPairStep]
  rw [coeffWorkUDiv2ThenSMul2Step_get_historyBit]
  exact coeffWorkUGreaterSelectorThenAddRIntoSStep_get_history_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hscratchB
    hfinal

/-- On clean comparison inputs, the `vLe` selector-plus-add-plus-shift branch
keeps the staged `v < u` predicate available through the paired `v/r` shifts. -/
theorem coeffWorkVLeSelectorThenAddSIntoRThenShiftPairStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (coeffAdderCompareBit n counterWidth).get
        (coeffWorkVLeSelectorThenAddSIntoRThenShiftPairStep n counterWidth bit
          historyIndex ((x, cleanComparisonWork n), work)) =
      decide (x.v.val < x.u.val) := by
  rw [coeffWorkVLeSelectorThenAddSIntoRThenShiftPairStep]
  rw [coeffWorkVDiv2ThenRMul2Step_get_compare]
  exact coeffWorkVLeSelectorThenAddSIntoRStep_get_compare_clean
    n counterWidth bit historyIndex x work hscratchA hcompare hfinal

/-- On clean scratchB, the `vLe` selector-plus-add-plus-shift branch preserves
the zero-code history no-op through the paired `v/r` shifts. -/
theorem coeffWorkVLeSelectorThenAddSIntoRThenShiftPairStep_get_history_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchB : (RegisterBits.scratchBBit n counterWidth).get x = false) :
    (coeffAdderHistoryBit n counterWidth historyIndex).get
        (coeffWorkVLeSelectorThenAddSIntoRThenShiftPairStep n counterWidth bit
          historyIndex ((x, cleanComparisonWork n), work)) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  rw [coeffWorkVLeSelectorThenAddSIntoRThenShiftPairStep]
  rw [coeffWorkVDiv2ThenRMul2Step_get_historyBit]
  exact coeffWorkVLeSelectorThenAddSIntoRStep_get_history_clean
    n counterWidth bit historyIndex x work hscratchB

/-- The corrected `uGreater` branch writes `u := (u - v) / 2` through the
paired shift group when the source-subtract work is clean and the subtraction
result is even. -/
theorem
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep_get_u_wordHalf_sub_of_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcarry : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          x = false)
    (hlsb : (x.1.1.u - x.1.1.v).val.testBit (0 : Nat) = false) :
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep
        tail.succ counterWidth bit historyIndex x).1.1.u =
      wordHalf tail.succ (x.1.1.u - x.1.1.v) := by
  let y :=
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep
      tail.succ counterWidth bit historyIndex x
  have hyu :
      y.1.1.u = x.1.1.u - x.1.1.v := by
    dsimp [y]
    exact
      coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRStep_get_u_sub_of_clean
        tail.succ counterWidth bit historyIndex x hcarry hwork
  have hlsbY : y.1.1.u.val.testBit (0 : Nat) = false := by
    rw [hyu]
    exact hlsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
      tail counterWidth y hlsbY
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep]
  change
    (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth y).1.1.u =
      wordHalf tail.succ (x.1.1.u - x.1.1.v)
  rw [hyu] at hmain
  exact hmain

/-- The corrected `uGreater` branch preserves the `r := r + s` coefficient
update through the paired `u/s` shift group. -/
theorem
    coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep_get_rCoeff_add_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep
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
  have hmain := coeffWorkUDiv2ThenSMul2Step_get_rCoeff n counterWidth y
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep]
  change
    (coeffWorkUDiv2ThenSMul2Step n counterWidth y).1.1.rCoeff =
      x.1.1.rCoeff + x.1.1.sCoeff
  rw [hyr] at hmain
  exact hmain

/-- The corrected `uGreater` branch writes `s := 2 * s` through the paired
shift group when the input coefficient top bit is false. -/
theorem
    coeffWorkUGreaterSubAddShiftPairStep_get_sCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hmsb : x.1.1.sCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep
        n counterWidth bit historyIndex x).1.1.sCoeff =
      wordDouble (n + 1) x.1.1.sCoeff := by
  let z :=
    coeffWorkUGreaterSelectorBranchHistoryWriteStep n counterWidth bit
      historyIndex x
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
  have hmsbY : y.1.1.sCoeff.val.testBit (Fin.last n).val = false := by
    rw [hys]
    exact hmsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
      n counterWidth y hmsbY
  rw [coeffWorkUGreaterSelectorThenSubVFromUThenAddSIntoRThenShiftPairStep]
  change
    (coeffWorkUDiv2ThenSMul2Step n counterWidth y).1.1.sCoeff =
      wordDouble (n + 1) x.1.1.sCoeff
  rw [hys] at hmain
  exact hmain

/-- The corrected `vLe` branch writes `v := (v - u) / 2` through the paired
shift group when the source-subtract work is clean and the subtraction result
is even. -/
theorem
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep_get_v_wordHalf_sub_of_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth)
    (hcarry : (coeffAdderScratchABit tail.succ counterWidth).get x = false)
    (hwork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          x = false)
    (hlsb : (x.1.1.v - x.1.1.u).val.testBit (0 : Nat) = false) :
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep
        tail.succ counterWidth bit historyIndex x).1.1.v =
      wordHalf tail.succ (x.1.1.v - x.1.1.u) := by
  let y :=
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep
      tail.succ counterWidth bit historyIndex x
  have hyv :
      y.1.1.v = x.1.1.v - x.1.1.u := by
    dsimp [y]
    exact
      coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSStep_get_v_sub_of_clean
        tail.succ counterWidth bit historyIndex x hcarry hwork
  have hlsbY : y.1.1.v.val.testBit (0 : Nat) = false := by
    rw [hyv]
    exact hlsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
      tail counterWidth y hlsbY
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep]
  change
    (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth y).1.1.v =
      wordHalf tail.succ (x.1.1.v - x.1.1.u)
  rw [hyv] at hmain
  exact hmain

/-- The corrected `vLe` branch preserves the `s := s + r` coefficient update
through the paired `v/r` shift group. -/
theorem
    coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep_get_sCoeff_add_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hcarry : (liftedCoeffAdderCarryInBit n counterWidth).get x = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get x =
          false) :
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep
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
  have hmain := coeffWorkVDiv2ThenRMul2Step_get_sCoeff n counterWidth y
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep]
  change
    (coeffWorkVDiv2ThenRMul2Step n counterWidth y).1.1.sCoeff =
      x.1.1.sCoeff + x.1.1.rCoeff
  rw [hys] at hmain
  exact hmain

/-- The corrected `vLe` branch writes `r := 2 * r` through the paired shift
group when the input coefficient top bit is false. -/
theorem
    coeffWorkVLeSubAddShiftPairStep_get_rCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : RegistersWithCoeffAdderWork n counterWidth)
    (hmsb : x.1.1.rCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep
        n counterWidth bit historyIndex x).1.1.rCoeff =
      wordDouble (n + 1) x.1.1.rCoeff := by
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
  have hmsbY : y.1.1.rCoeff.val.testBit (Fin.last n).val = false := by
    rw [hyr]
    exact hmsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
      n counterWidth y hmsbY
  rw [coeffWorkVLeSelectorThenSubUFromVThenAddRIntoSThenShiftPairStep]
  change
    (coeffWorkVDiv2ThenRMul2Step n counterWidth y).1.1.rCoeff =
      wordDouble (n + 1) x.1.1.rCoeff
  rw [hyr] at hmain
  exact hmain

/-- The corrected `uGreater` branch-code/dispatch wrapper writes
`u := (u - v) / 2` when the staged branch is active and the subtraction result
is even. -/
theorem
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_u_wordHalf_sub_of_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hfinal : bit.val + 1 = tail.succ)
    (hgreater : decide (x.v.val < x.u.val) = true)
    (hwork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.u - x.v).val.testBit (0 : Nat) = false) :
    (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
        tail.succ counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.u =
      wordHalf tail.succ (x.u - x.v) := by
  let input : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkUGreaterSubAddBranchCodeToScratchStep
      tail.succ counterWidth bit historyIndex input
  have hcarry :
      (coeffAdderScratchABit tail.succ counterWidth).get input = false := by
    change x.scratchA = false
    exact hscratchA
  have hstagedU : staged.1.1.u = x.u - x.v := by
    dsimp [staged, input]
    exact
      coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_u_sub_of_clean
        tail.succ counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) hcarry hwork
  have hlsbStaged : staged.1.1.u.val.testBit (0 : Nat) = false := by
    rw [hstagedU]
    exact hlsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_u_wordHalf_of_lsb_false
      tail counterWidth staged hlsbStaged
  have hdispatch :=
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_eq_uShift_clean
      tail.succ counterWidth bit historyIndex x work hscratchA hcompare
      hactive hfinal hgreater
  rw [hdispatch]
  change
    (coeffWorkUDiv2ThenSMul2Step tail.succ counterWidth staged).1.1.u =
      wordHalf tail.succ (x.u - x.v)
  rw [hstagedU] at hmain
  exact hmain

/-- The corrected `vLe` branch-code/dispatch wrapper writes
`v := (v - u) / 2` when the staged branch is active and the subtraction result
is even. -/
theorem
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_v_wordHalf_sub_of_clean
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (x : Registers tail.succ counterWidth) (work : CoeffAdderWork tail.succ)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit tail.succ counterWidth).get x = true)
    (hwork :
      ∀ k : Fin (tail.succ - 1),
        ((coeffAdderComparisonCarryPrefixWord tail.succ counterWidth).bit k).get
          ((x, cleanComparisonWork tail.succ), work) = false)
    (hlsb : (x.v - x.u).val.testBit (0 : Nat) = false) :
    (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
        tail.succ counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work)).1.1.v =
      wordHalf tail.succ (x.v - x.u) := by
  let input : RegistersWithCoeffAdderWork tail.succ counterWidth :=
    ((x, cleanComparisonWork tail.succ), work)
  let staged :=
    coeffWorkVLeSubAddBranchCodeToScratchStep
      tail.succ counterWidth bit historyIndex input
  have hcarry :
      (coeffAdderScratchABit tail.succ counterWidth).get input = false := by
    change x.scratchA = false
    exact hscratchA
  have hstagedV : staged.1.1.v = x.v - x.u := by
    dsimp [staged, input]
    exact
      coeffWorkVLeSubAddBranchCodeToScratchStep_get_v_sub_of_clean
        tail.succ counterWidth bit historyIndex
        ((x, cleanComparisonWork tail.succ), work) hcarry hwork
  have hlsbStaged : staged.1.1.v.val.testBit (0 : Nat) = false := by
    rw [hstagedV]
    exact hlsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_v_wordHalf_of_lsb_false
      tail counterWidth staged hlsbStaged
  have hdispatch :=
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_eq_vShift_clean
      tail.succ counterWidth bit historyIndex x work hscratchA hactive
  rw [hdispatch]
  change
    (coeffWorkVDiv2ThenRMul2Step tail.succ counterWidth staged).1.1.v =
      wordHalf tail.succ (x.v - x.u)
  rw [hstagedV] at hmain
  exact hmain

/-- The corrected `uGreater` branch-code/dispatch wrapper preserves
`r := r + s` through the paired shift group. -/
theorem
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_rCoeff_add_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hfinal : bit.val + 1 = n)
    (hgreater : decide (x.v.val < x.u.val) = true)
    (hcarry :
      (liftedCoeffAdderCarryInBit n counterWidth).get
        ((x, cleanComparisonWork n), work) = false)
    (hwork :
      ∀ k : Fin ((n + 1) - 1),
        ((liftedCoeffAdderCarryWorkWord n counterWidth).bit k).get
          ((x, cleanComparisonWork n), work) = false) :
    (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work)).1.1.rCoeff =
      x.rCoeff + x.sCoeff := by
  let input : RegistersWithCoeffAdderWork n counterWidth :=
    ((x, cleanComparisonWork n), work)
  let staged :=
    coeffWorkUGreaterSubAddBranchCodeToScratchStep
      n counterWidth bit historyIndex input
  have hstagedR : staged.1.1.rCoeff = x.rCoeff + x.sCoeff := by
    dsimp [staged, input]
    exact
      coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_rCoeff_add_of_clean
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work) hcarry hwork
  have hmain := coeffWorkUDiv2ThenSMul2Step_get_rCoeff
    n counterWidth staged
  have hdispatch :=
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_eq_uShift_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hactive
      hfinal hgreater
  rw [hdispatch]
  change
    (coeffWorkUDiv2ThenSMul2Step n counterWidth staged).1.1.rCoeff =
      x.rCoeff + x.sCoeff
  rw [hstagedR] at hmain
  exact hmain

/-- The corrected `uGreater` branch-code/dispatch wrapper writes
`s := 2 * s` through the paired shift group when the input coefficient top bit
is false. -/
theorem
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_sCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hfinal : bit.val + 1 = n)
    (hgreater : decide (x.v.val < x.u.val) = true)
    (hmsb : x.sCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work)).1.1.sCoeff =
      wordDouble (n + 1) x.sCoeff := by
  let input : RegistersWithCoeffAdderWork n counterWidth :=
    ((x, cleanComparisonWork n), work)
  let staged :=
    coeffWorkUGreaterSubAddBranchCodeToScratchStep
      n counterWidth bit historyIndex input
  have hstagedS : staged.1.1.sCoeff = x.sCoeff := by
    dsimp [staged, input]
    exact
      coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_sCoeff
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work)
  have hmsbStaged :
      staged.1.1.sCoeff.val.testBit (Fin.last n).val = false := by
    rw [hstagedS]
    exact hmsb
  have hmain :=
    coeffWorkUDiv2ThenSMul2Step_get_sCoeff_wordDouble_of_msb_false
      n counterWidth staged hmsbStaged
  have hdispatch :=
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_eq_uShift_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hactive
      hfinal hgreater
  rw [hdispatch]
  change
    (coeffWorkUDiv2ThenSMul2Step n counterWidth staged).1.1.sCoeff =
      wordDouble (n + 1) x.sCoeff
  rw [hstagedS] at hmain
  exact hmain

/-- The corrected `uGreater` branch-code/dispatch wrapper preserves the
untouched `v` source word through the paired shift group. -/
theorem coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_get_v
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hfinal : bit.val + 1 = n)
    (hgreater : decide (x.v.val < x.u.val) = true) :
    (coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work)).1.1.v =
      x.v := by
  let staged :=
    coeffWorkUGreaterSubAddBranchCodeToScratchStep
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hstagedV : staged.1.1.v = x.v := by
    dsimp [staged]
    exact coeffWorkUGreaterSubAddBranchCodeToScratchStep_get_v
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hmain := coeffWorkUDiv2ThenSMul2Step_get_v n counterWidth staged
  have hdispatch :=
    coeffWorkUGreaterSubAddBranchCodeThenAuxShiftDispatchStep_eq_uShift_clean
      n counterWidth bit historyIndex x work hscratchA hcompare hactive
      hfinal hgreater
  rw [hdispatch]
  change (coeffWorkUDiv2ThenSMul2Step n counterWidth staged).1.1.v = x.v
  rw [hmain, hstagedV]

/-- The corrected `vLe` branch-code/dispatch wrapper preserves
`s := s + r` through the paired shift group. -/
theorem
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_sCoeff_add_of_clean
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
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
    (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work)).1.1.sCoeff =
      x.sCoeff + x.rCoeff := by
  let input : RegistersWithCoeffAdderWork n counterWidth :=
    ((x, cleanComparisonWork n), work)
  let staged :=
    coeffWorkVLeSubAddBranchCodeToScratchStep
      n counterWidth bit historyIndex input
  have hstagedS : staged.1.1.sCoeff = x.sCoeff + x.rCoeff := by
    dsimp [staged, input]
    exact
      coeffWorkVLeSubAddBranchCodeToScratchStep_get_sCoeff_add_of_clean
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work) hcarry hwork
  have hmain := coeffWorkVDiv2ThenRMul2Step_get_sCoeff
    n counterWidth staged
  have hdispatch :=
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_eq_vShift_clean
      n counterWidth bit historyIndex x work hscratchA hactive
  rw [hdispatch]
  change
    (coeffWorkVDiv2ThenRMul2Step n counterWidth staged).1.1.sCoeff =
      x.sCoeff + x.rCoeff
  rw [hstagedS] at hmain
  exact hmain

/-- The corrected `vLe` branch-code/dispatch wrapper writes `r := 2 * r`
through the paired shift group when the input coefficient top bit is false. -/
theorem
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_rCoeff_wordDouble_of_msb_false
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true)
    (hmsb : x.rCoeff.val.testBit (Fin.last n).val = false) :
    (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work)).1.1.rCoeff =
      wordDouble (n + 1) x.rCoeff := by
  let input : RegistersWithCoeffAdderWork n counterWidth :=
    ((x, cleanComparisonWork n), work)
  let staged :=
    coeffWorkVLeSubAddBranchCodeToScratchStep
      n counterWidth bit historyIndex input
  have hstagedR : staged.1.1.rCoeff = x.rCoeff := by
    dsimp [staged, input]
    exact
      coeffWorkVLeSubAddBranchCodeToScratchStep_get_rCoeff
        n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hmsbStaged :
      staged.1.1.rCoeff.val.testBit (Fin.last n).val = false := by
    rw [hstagedR]
    exact hmsb
  have hmain :=
    coeffWorkVDiv2ThenRMul2Step_get_rCoeff_wordDouble_of_msb_false
      n counterWidth staged hmsbStaged
  have hdispatch :=
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_eq_vShift_clean
      n counterWidth bit historyIndex x work hscratchA hactive
  rw [hdispatch]
  change
    (coeffWorkVDiv2ThenRMul2Step n counterWidth staged).1.1.rCoeff =
      wordDouble (n + 1) x.rCoeff
  rw [hstagedR] at hmain
  exact hmain

/-- The corrected `vLe` branch-code/dispatch wrapper preserves the untouched
`u` source word through the paired shift group. -/
theorem coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_get_u
    (n counterWidth : Nat) (bit : Fin n) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) (work : CoeffAdderWork n)
    (hscratchA : x.scratchA = false)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true) :
    (coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep
        n counterWidth bit historyIndex
        ((x, cleanComparisonWork n), work)).1.1.u =
      x.u := by
  let staged :=
    coeffWorkVLeSubAddBranchCodeToScratchStep
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hstagedU : staged.1.1.u = x.u := by
    dsimp [staged]
    exact coeffWorkVLeSubAddBranchCodeToScratchStep_get_u
      n counterWidth bit historyIndex ((x, cleanComparisonWork n), work)
  have hmain := coeffWorkVDiv2ThenRMul2Step_get_u n counterWidth staged
  have hdispatch :=
    coeffWorkVLeSubAddBranchCodeThenAuxShiftDispatchStep_eq_vShift_clean
      n counterWidth bit historyIndex x work hscratchA hactive
  rw [hdispatch]
  change (coeffWorkVDiv2ThenRMul2Step n counterWidth staged).1.1.u = x.u
  rw [hmain, hstagedU]

/-! ## Compact selected branch-code staging -/

namespace Compact

/-- Selected low `u` bit on the compact carrier. -/
def uLowBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (encoding n counterWidth) :=
  (uValueWord n counterWidth).bit bit

/-- Selected low `v` bit on the compact carrier. -/
def vLowBit (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit (encoding n counterWidth) :=
  (vValueWord n counterWidth).bit bit

private theorem uLowBit_vLowBit_wire_ne
    (n counterWidth : Nat) (uIndex vIndex : Fin n) :
    (uLowBit n counterWidth uIndex).wire ≠
      (vLowBit n counterWidth vIndex).wire := by
  simpa [uLowBit, vLowBit, uValueWord, vValueWord,
    RegisterBits.uValueBit, RegisterBits.vValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.u_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire uIndex)
        (WireAddress.littleEndianWire vIndex))

private theorem uLowBit_work_wire_ne
    (n counterWidth : Nat) (low work : Fin n) :
    (uLowBit n counterWidth low).wire ≠
      (coefficientCarryWorkBit n counterWidth work).wire := by
  simpa [uLowBit, uValueWord] using
    liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth low) work

private theorem vLowBit_work_wire_ne
    (n counterWidth : Nat) (low work : Fin n) :
    (vLowBit n counterWidth low).wire ≠
      (coefficientCarryWorkBit n counterWidth work).wire := by
  simpa [vLowBit, vValueWord] using
    liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth low) work

private theorem activeBit_work_wire_ne
    (n counterWidth : Nat) (work : Fin n) :
    (activeBit n counterWidth).wire ≠
      (coefficientCarryWorkBit n counterWidth work).wire :=
  liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
    (RegisterBits.activeBit n counterWidth) work

private theorem uLowBit_activeBit_wire_ne
    (n counterWidth : Nat) (low : Fin n) :
    (uLowBit n counterWidth low).wire ≠
      (activeBit n counterWidth).wire := by
  simpa [uLowBit, uValueWord, RegisterBits.uValueBit, activeBit] using
    liftCoreBit_wire_ne n counterWidth
      (Ne.symm (RegisterBits.active_u_wire_ne n counterWidth
        (WireAddress.littleEndianWire low)))

private theorem vLowBit_activeBit_wire_ne
    (n counterWidth : Nat) (low : Fin n) :
    (vLowBit n counterWidth low).wire ≠
      (activeBit n counterWidth).wire := by
  simpa [vLowBit, vValueWord, RegisterBits.vValueBit, activeBit] using
    liftCoreBit_wire_ne n counterWidth
      (Ne.symm (RegisterBits.active_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire low)))

private theorem uLowBit_compareBit_wire_ne
    (n counterWidth : Nat) (low : Fin n) :
    (uLowBit n counterWidth low).wire ≠
      (compareBit n counterWidth).wire := by
  simpa [uLowBit, uValueWord, RegisterBits.uValueBit, compareBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.u_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire low))

private theorem vLowBit_compareBit_wire_ne
    (n counterWidth : Nat) (low : Fin n) :
    (vLowBit n counterWidth low).wire ≠
      (compareBit n counterWidth).wire := by
  simpa [vLowBit, vValueWord, RegisterBits.vValueBit, compareBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.v_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire low))

private theorem uLowBit_scratchABit_wire_ne
    (n counterWidth : Nat) (low : Fin n) :
    (uLowBit n counterWidth low).wire ≠
      (scratchABit n counterWidth).wire := by
  simpa [uLowBit, uValueWord, RegisterBits.uValueBit, scratchABit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.u_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire low))

private theorem uLowBit_scratchBBit_wire_ne
    (n counterWidth : Nat) (low : Fin n) :
    (uLowBit n counterWidth low).wire ≠
      (scratchBBit n counterWidth).wire := by
  simpa [uLowBit, uValueWord, RegisterBits.uValueBit, scratchBBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.u_scratchB_wire_ne n counterWidth
        (WireAddress.littleEndianWire low))

private theorem vLowBit_scratchABit_wire_ne
    (n counterWidth : Nat) (low : Fin n) :
    (vLowBit n counterWidth low).wire ≠
      (scratchABit n counterWidth).wire := by
  simpa [vLowBit, vValueWord, RegisterBits.vValueBit, scratchABit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.v_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire low))

private theorem vLowBit_scratchBBit_wire_ne
    (n counterWidth : Nat) (low : Fin n) :
    (vLowBit n counterWidth low).wire ≠
      (scratchBBit n counterWidth).wire := by
  simpa [vLowBit, vValueWord, RegisterBits.vValueBit, scratchBBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.v_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire low))

/-! ### Even-only branch-code staging -/

/-- Eight native gates stage only the two even branch codes.  Odd inputs leave
both scratch bits clean so the following selected odd arithmetic may reuse
them as control work.  One VBE carry bit is borrowed and restored. -/
def selectedEvenBranchCodeToScratchGates
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  let u := uLowBit n counterWidth low
  let v := vLowBit n counterWidth low
  let temp := coefficientCarryWorkBit n counterWidth tempIndex
  let active := activeBit n counterWidth
  let scratchA := scratchABit n counterWidth
  let scratchB := scratchBBit n counterWidth
  [ EncodedBit.GateSpec.x u
  , EncodedBit.GateSpec.toffoli active u scratchA
      (uLowBit_activeBit_wire_ne n counterWidth low).symm
      (activeBit_scratchABit_wire_ne n counterWidth)
      (uLowBit_scratchABit_wire_ne n counterWidth low)
  , EncodedBit.GateSpec.x u
  , EncodedBit.GateSpec.x v
  , EncodedBit.GateSpec.toffoli u v temp
      (uLowBit_vLowBit_wire_ne n counterWidth low low)
      (uLowBit_work_wire_ne n counterWidth low tempIndex)
      (vLowBit_work_wire_ne n counterWidth low tempIndex)
  , EncodedBit.GateSpec.toffoli active temp scratchB
      (activeBit_work_wire_ne n counterWidth tempIndex)
      (activeBit_scratchBBit_wire_ne n counterWidth)
      (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth) tempIndex).symm
  , EncodedBit.GateSpec.toffoli u v temp
      (uLowBit_vLowBit_wire_ne n counterWidth low low)
      (uLowBit_work_wire_ne n counterWidth low tempIndex)
      (vLowBit_work_wire_ne n counterWidth low tempIndex)
  , EncodedBit.GateSpec.x v ]

/-- Even-branch code staging uses only core and shared-work wires, so it is
disjoint from every public target bit. -/
theorem selectedEvenBranchCodeToScratchGates_bitDisjoint_target
    (n counterWidth : Nat) (low tempIndex targetIndex : Fin n) :
    ∀ gate,
      gate ∈ selectedEvenBranchCodeToScratchGates n counterWidth low
          tempIndex →
        EncodedBit.GateSpec.bitDisjoint
          (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  simp only [selectedEvenBranchCodeToScratchGates, List.mem_cons,
    List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth low) targetIndex
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.uValueBit n counterWidth low) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) targetIndex⟩
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth low) targetIndex
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth low) targetIndex
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.uValueBit n counterWidth low) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth low) targetIndex,
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedCoefficientCarryWorkBit n counterWidth tempIndex) targetIndex⟩
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth) targetIndex,
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedCoefficientCarryWorkBit n counterWidth tempIndex) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth) targetIndex⟩
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.uValueBit n counterWidth low) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth low) targetIndex,
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedCoefficientCarryWorkBit n counterWidth tempIndex) targetIndex⟩
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth low) targetIndex

def selectedEvenBranchCodeToScratchStep
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (selectedEvenBranchCodeToScratchGates n counterWidth low tempIndex)

def selectedEvenBranchCodeToScratchProgram
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (selectedEvenBranchCodeToScratchGates n counterWidth low tempIndex)

theorem selectedEvenBranchCodeToScratch_realizes
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (selectedEvenBranchCodeToScratchProgram n counterWidth low tempIndex)
      (selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (selectedEvenBranchCodeToScratchGates n counterWidth low tempIndex)

@[simp] theorem selectedEvenBranchCodeToScratchGates_length
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    (selectedEvenBranchCodeToScratchGates
      n counterWidth low tempIndex).length = 8 := by
  rfl

@[simp] theorem selectedEvenBranchCodeToScratchGates_xMultiplicity_sum
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    ((selectedEvenBranchCodeToScratchGates n counterWidth low tempIndex).map
      EncodedBit.GateSpec.xMultiplicity).sum = 4 := by
  rfl

@[simp] theorem selectedEvenBranchCodeToScratchGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    ((selectedEvenBranchCodeToScratchGates n counterWidth low tempIndex).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  rfl

@[simp] theorem selectedEvenBranchCodeToScratchGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    ((selectedEvenBranchCodeToScratchGates n counterWidth low tempIndex).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 4 := by
  rfl

private def selectedEvenBranchCodeToScratchStepCore
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active scratchA scratchB : EncodedBit encoding) :
    Data -> Data :=
  fun x =>
    uNotVBranchCodeToScratchBStepCore u v temp active scratchB
      (notUBranchCodeToScratchAStepCore u active scratchA x)

private theorem selectedEvenBranchCodeToScratchStep_eq_core
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x =
      selectedEvenBranchCodeToScratchStepCore
        (uLowBit n counterWidth low) (vLowBit n counterWidth low)
        (coefficientCarryWorkBit n counterWidth tempIndex)
        (activeBit n counterWidth) (scratchABit n counterWidth)
        (scratchBBit n counterWidth) x := by
  rfl

/-- Odd low bits make both even-only branch-code terms false.  When the one
borrowed VBE bit is clean, the complete staging circuit is therefore the
identity, leaving the scratch pair available to the odd arithmetic. -/
theorem selectedEvenBranchCodeToScratchStep_eq_self_of_odd_pair_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth)
    (hu : (uLowBit n counterWidth low).get x = true)
    (hv : (vLowBit n counterWidth low).get x = true)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x = x := by
  rw [selectedEvenBranchCodeToScratchStep_eq_core]
  unfold selectedEvenBranchCodeToScratchStepCore
  rw [notUBranchCodeToScratchAStepCore_eq_self_of_u_true
    (uLowBit n counterWidth low) (activeBit n counterWidth)
    (scratchABit n counterWidth) x hu]
  exact uNotVBranchCodeToScratchBStepCore_eq_self_of_v_true_temp_false
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (scratchBBit n counterWidth)
    (vLowBit_work_wire_ne n counterWidth low tempIndex) x hv htemp

/-- Inactive inputs bypass both even branch-code terms.  The borrowed VBE bit
is computed and uncomputed inside the second term, so no extra cleanliness
assumption on that bit is needed. -/
theorem selectedEvenBranchCodeToScratchStep_eq_self_of_active_false
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = false) :
    selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x = x := by
  rw [selectedEvenBranchCodeToScratchStep_eq_core]
  unfold selectedEvenBranchCodeToScratchStepCore
  rw [notUBranchCodeToScratchAStepCore_eq_self_of_active_false
    (uLowBit n counterWidth low) (activeBit n counterWidth)
    (scratchABit n counterWidth)
    (uLowBit_activeBit_wire_ne n counterWidth low) x hactive]
  exact uNotVBranchCodeToScratchBStepCore_eq_self_of_active_false
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (scratchBBit n counterWidth)
    (uLowBit_work_wire_ne n counterWidth low tempIndex)
    (vLowBit_work_wire_ne n counterWidth low tempIndex)
    (vLowBit_activeBit_wire_ne n counterWidth low)
    (activeBit_work_wire_ne n counterWidth tempIndex).symm x hactive

private theorem selectedEvenBranchCodeToScratchStepCore_get_of_targets_ne
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (u v temp active scratchA scratchB observed : EncodedBit encoding)
    (hUObserved : u.wire ≠ observed.wire)
    (hVObserved : v.wire ≠ observed.wire)
    (hTempObserved : temp.wire ≠ observed.wire)
    (hScratchAObserved : scratchA.wire ≠ observed.wire)
    (hScratchBObserved : scratchB.wire ≠ observed.wire)
    (x : Data) :
    observed.get
        (selectedEvenBranchCodeToScratchStepCore
          u v temp active scratchA scratchB x) =
      observed.get x := by
  unfold selectedEvenBranchCodeToScratchStepCore
  rw [uNotVBranchCodeToScratchBStepCore_get_of_targets_ne
    u v temp active scratchB observed hVObserved hTempObserved
      hScratchBObserved]
  exact notUBranchCodeToScratchAStepCore_get_of_targets_ne
    u active scratchA observed hUObserved hScratchAObserved x

/-- Even-only staging preserves every observation outside its two low input
bits, borrowed carry bit, and two branch-code targets. -/
theorem selectedEvenBranchCodeToScratchStep_get_of_preserved
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (observed : EncodedBit (encoding n counterWidth))
    (hu : (uLowBit n counterWidth low).wire ≠ observed.wire)
    (hv : (vLowBit n counterWidth low).wire ≠ observed.wire)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).wire ≠
      observed.wire)
    (hscratchA : (scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB : (scratchBBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x) =
      observed.get x := by
  rw [selectedEvenBranchCodeToScratchStep_eq_core]
  exact selectedEvenBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (scratchABit n counterWidth)
    (scratchBBit n counterWidth) observed hu hv htemp hscratchA hscratchB x

theorem selectedEvenBranchCodeToScratchStep_get_u
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    (uLowBit n counterWidth low).get
        (selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x) =
      (uLowBit n counterWidth low).get x := by
  rw [selectedEvenBranchCodeToScratchStep_eq_core]
  unfold selectedEvenBranchCodeToScratchStepCore
  rw [uNotVBranchCodeToScratchBStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (scratchBBit n counterWidth)
    (uLowBit n counterWidth low)
    (uLowBit_vLowBit_wire_ne n counterWidth low low).symm
    (uLowBit_work_wire_ne n counterWidth low tempIndex).symm
    (uLowBit_scratchBBit_wire_ne n counterWidth low).symm]
  exact notUBranchCodeToScratchAStepCore_get_u
    (uLowBit n counterWidth low) (activeBit n counterWidth)
    (scratchABit n counterWidth)
    (uLowBit_scratchABit_wire_ne n counterWidth low) x

theorem selectedEvenBranchCodeToScratchStep_get_v
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    (vLowBit n counterWidth low).get
        (selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x) =
      (vLowBit n counterWidth low).get x := by
  rw [selectedEvenBranchCodeToScratchStep_eq_core]
  unfold selectedEvenBranchCodeToScratchStepCore
  rw [uNotVBranchCodeToScratchBStepCore_get_v
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (scratchBBit n counterWidth)
    (vLowBit_work_wire_ne n counterWidth low tempIndex)
    (vLowBit_scratchBBit_wire_ne n counterWidth low)]
  exact notUBranchCodeToScratchAStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (activeBit n counterWidth)
    (scratchABit n counterWidth) (vLowBit n counterWidth low)
    (uLowBit_vLowBit_wire_ne n counterWidth low low)
    (vLowBit_scratchABit_wire_ne n counterWidth low).symm x

theorem selectedEvenBranchCodeToScratchStep_get_temp_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    (coefficientCarryWorkBit n counterWidth tempIndex).get
        (selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x) =
      false := by
  rw [selectedEvenBranchCodeToScratchStep_eq_core]
  unfold selectedEvenBranchCodeToScratchStepCore
  let staged := notUBranchCodeToScratchAStepCore
    (uLowBit n counterWidth low) (activeBit n counterWidth)
    (scratchABit n counterWidth) x
  have htempStaged :
      (coefficientCarryWorkBit n counterWidth tempIndex).get staged = false := by
    dsimp [staged]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      (uLowBit n counterWidth low) (activeBit n counterWidth)
      (scratchABit n counterWidth)
      (coefficientCarryWorkBit n counterWidth tempIndex)
      (uLowBit_work_wire_ne n counterWidth low tempIndex)
      (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) tempIndex)]
    exact htemp
  exact uNotVBranchCodeToScratchBStepCore_get_temp_clean
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (scratchBBit n counterWidth)
    (uLowBit_vLowBit_wire_ne n counterWidth low low)
    (uLowBit_work_wire_ne n counterWidth low tempIndex)
    (uLowBit_scratchBBit_wire_ne n counterWidth low)
    (vLowBit_work_wire_ne n counterWidth low tempIndex)
    (vLowBit_activeBit_wire_ne n counterWidth low)
    (vLowBit_scratchBBit_wire_ne n counterWidth low)
    (activeBit_work_wire_ne n counterWidth tempIndex).symm
    (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth) tempIndex).symm
    staged htempStaged

theorem selectedEvenBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false) :
    (scratchABit n counterWidth).get
        (selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x) =
      ((activeBit n counterWidth).get x &&
        !(uLowBit n counterWidth low).get x) := by
  rw [selectedEvenBranchCodeToScratchStep_eq_core]
  unfold selectedEvenBranchCodeToScratchStepCore
  rw [uNotVBranchCodeToScratchBStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (scratchBBit n counterWidth)
    (scratchABit n counterWidth)
    (vLowBit_scratchABit_wire_ne n counterWidth low)
    (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth) tempIndex).symm
    (scratchABit_scratchBBit_wire_ne n counterWidth).symm]
  rw [notUBranchCodeToScratchAStepCore_get_scratchA
    (uLowBit n counterWidth low) (activeBit n counterWidth)
    (scratchABit n counterWidth)
    (uLowBit_activeBit_wire_ne n counterWidth low)
    (uLowBit_scratchABit_wire_ne n counterWidth low), hscratchA]
  simp

theorem selectedEvenBranchCodeToScratchStep_get_scratchB_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    (scratchBBit n counterWidth).get
        (selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x) =
      (((activeBit n counterWidth).get x &&
          (uLowBit n counterWidth low).get x) &&
        !(vLowBit n counterWidth low).get x) := by
  rw [selectedEvenBranchCodeToScratchStep_eq_core]
  unfold selectedEvenBranchCodeToScratchStepCore
  let staged := notUBranchCodeToScratchAStepCore
    (uLowBit n counterWidth low) (activeBit n counterWidth)
    (scratchABit n counterWidth) x
  have htempStaged :
      (coefficientCarryWorkBit n counterWidth tempIndex).get staged = false := by
    dsimp [staged]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      (uLowBit n counterWidth low) (activeBit n counterWidth)
      (scratchABit n counterWidth)
      (coefficientCarryWorkBit n counterWidth tempIndex)
      (uLowBit_work_wire_ne n counterWidth low tempIndex)
      (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) tempIndex)]
    exact htemp
  rw [uNotVBranchCodeToScratchBStepCore_get_scratchB_clean
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (scratchBBit n counterWidth)
    (uLowBit_vLowBit_wire_ne n counterWidth low low)
    (uLowBit_work_wire_ne n counterWidth low tempIndex)
    (uLowBit_scratchBBit_wire_ne n counterWidth low)
    (vLowBit_work_wire_ne n counterWidth low tempIndex)
    (vLowBit_activeBit_wire_ne n counterWidth low)
    (vLowBit_scratchBBit_wire_ne n counterWidth low)
    (activeBit_work_wire_ne n counterWidth tempIndex).symm
    (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth) tempIndex).symm
    staged htempStaged]
  have hscratchBStaged :
      (scratchBBit n counterWidth).get staged = false := by
    dsimp [staged]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      (uLowBit n counterWidth low) (activeBit n counterWidth)
      (scratchABit n counterWidth) (scratchBBit n counterWidth)
      (uLowBit_scratchBBit_wire_ne n counterWidth low)
      (scratchABit_scratchBBit_wire_ne n counterWidth)]
    exact hscratchB
  have hactiveStaged :
      (activeBit n counterWidth).get staged =
        (activeBit n counterWidth).get x := by
    dsimp [staged]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      (uLowBit n counterWidth low) (activeBit n counterWidth)
      (scratchABit n counterWidth) (activeBit n counterWidth)
      (uLowBit_activeBit_wire_ne n counterWidth low)
      (activeBit_scratchABit_wire_ne n counterWidth).symm]
  have huStaged :
      (uLowBit n counterWidth low).get staged =
        (uLowBit n counterWidth low).get x := by
    dsimp [staged]
    exact notUBranchCodeToScratchAStepCore_get_u
      (uLowBit n counterWidth low) (activeBit n counterWidth)
      (scratchABit n counterWidth)
      (uLowBit_scratchABit_wire_ne n counterWidth low) x
  have hvStaged :
      (vLowBit n counterWidth low).get staged =
        (vLowBit n counterWidth low).get x := by
    dsimp [staged]
    rw [notUBranchCodeToScratchAStepCore_get_of_targets_ne
      (uLowBit n counterWidth low) (activeBit n counterWidth)
      (scratchABit n counterWidth) (vLowBit n counterWidth low)
      (uLowBit_vLowBit_wire_ne n counterWidth low low)
      (vLowBit_scratchABit_wire_ne n counterWidth low).symm]
  rw [hscratchBStaged, hactiveStaged, huStaged, hvStaged]
  simp

/-- Fourteen native gates compute the active branch code.  One restored VBE
carry bit is borrowed as temporary work and uncomputed before return. -/
def selectedBranchCodeToScratchGates
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  let u := uLowBit n counterWidth low
  let v := vLowBit n counterWidth low
  let temp := coefficientCarryWorkBit n counterWidth tempIndex
  let active := activeBit n counterWidth
  let compare := compareBit n counterWidth
  let scratchA := scratchABit n counterWidth
  let scratchB := scratchBBit n counterWidth
  [ EncodedBit.GateSpec.toffoli u v temp
      (uLowBit_vLowBit_wire_ne n counterWidth low low)
      (uLowBit_work_wire_ne n counterWidth low tempIndex)
      (vLowBit_work_wire_ne n counterWidth low tempIndex)
  , EncodedBit.GateSpec.toffoli active temp scratchA
      (activeBit_work_wire_ne n counterWidth tempIndex)
      (activeBit_scratchABit_wire_ne n counterWidth)
      (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) tempIndex))
  , EncodedBit.GateSpec.toffoli scratchA compare scratchB
      (Ne.symm (compareBit_scratchABit_wire_ne n counterWidth))
      (scratchABit_scratchBBit_wire_ne n counterWidth)
      (compareBit_scratchBBit_wire_ne n counterWidth)
  , EncodedBit.GateSpec.toffoli active temp scratchA
      (activeBit_work_wire_ne n counterWidth tempIndex)
      (activeBit_scratchABit_wire_ne n counterWidth)
      (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) tempIndex))
  , EncodedBit.GateSpec.cnot scratchB scratchA
      (Ne.symm (scratchABit_scratchBBit_wire_ne n counterWidth))
  , EncodedBit.GateSpec.toffoli u v temp
      (uLowBit_vLowBit_wire_ne n counterWidth low low)
      (uLowBit_work_wire_ne n counterWidth low tempIndex)
      (vLowBit_work_wire_ne n counterWidth low tempIndex)
  , EncodedBit.GateSpec.x u
  , EncodedBit.GateSpec.toffoli active u scratchA
      (Ne.symm (uLowBit_activeBit_wire_ne n counterWidth low))
      (activeBit_scratchABit_wire_ne n counterWidth)
      (uLowBit_scratchABit_wire_ne n counterWidth low)
  , EncodedBit.GateSpec.x u
  , EncodedBit.GateSpec.x v
  , EncodedBit.GateSpec.toffoli u v temp
      (uLowBit_vLowBit_wire_ne n counterWidth low low)
      (uLowBit_work_wire_ne n counterWidth low tempIndex)
      (vLowBit_work_wire_ne n counterWidth low tempIndex)
  , EncodedBit.GateSpec.toffoli active temp scratchB
      (activeBit_work_wire_ne n counterWidth tempIndex)
      (activeBit_scratchBBit_wire_ne n counterWidth)
      (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth) tempIndex))
  , EncodedBit.GateSpec.toffoli u v temp
      (uLowBit_vLowBit_wire_ne n counterWidth low low)
      (uLowBit_work_wire_ne n counterWidth low tempIndex)
      (vLowBit_work_wire_ne n counterWidth low tempIndex)
  , EncodedBit.GateSpec.x v ]

def selectedBranchCodeToScratchStep
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (selectedBranchCodeToScratchGates n counterWidth low tempIndex)

def selectedBranchCodeToScratchProgram
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (selectedBranchCodeToScratchGates n counterWidth low tempIndex)

theorem selectedBranchCodeToScratch_realizes
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (selectedBranchCodeToScratchProgram n counterWidth low tempIndex)
      (selectedBranchCodeToScratchStep n counterWidth low tempIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (selectedBranchCodeToScratchGates n counterWidth low tempIndex)

theorem selectedBranchCodeToScratchGates_length
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    (selectedBranchCodeToScratchGates n counterWidth low tempIndex).length =
      14 := by
  simp [selectedBranchCodeToScratchGates]

theorem selectedBranchCodeToScratchGates_xMultiplicity_sum
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    ((selectedBranchCodeToScratchGates n counterWidth low tempIndex).map
      EncodedBit.GateSpec.xMultiplicity).sum = 4 := by
  simp [selectedBranchCodeToScratchGates]

theorem selectedBranchCodeToScratchGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    ((selectedBranchCodeToScratchGates n counterWidth low tempIndex).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp [selectedBranchCodeToScratchGates]

theorem selectedBranchCodeToScratchGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (low tempIndex : Fin n) :
    ((selectedBranchCodeToScratchGates n counterWidth low tempIndex).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 9 := by
  simp [selectedBranchCodeToScratchGates]

private theorem selectedBranchCodeToScratchStep_eq_core
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    selectedBranchCodeToScratchStep n counterWidth low tempIndex x =
      selectedBranchCodeToScratchStepCore
        (uLowBit n counterWidth low) (vLowBit n counterWidth low)
        (coefficientCarryWorkBit n counterWidth tempIndex)
        (activeBit n counterWidth) (compareBit n counterWidth)
        (scratchABit n counterWidth) (scratchBBit n counterWidth) x := by
  rfl

/-- Selected branch-code staging preserves the active-round flag. -/
theorem selectedBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) =
      (activeBit n counterWidth).get x := by
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (activeBit n counterWidth)
    (uLowBit_activeBit_wire_ne n counterWidth low)
    (vLowBit_activeBit_wire_ne n counterWidth low)
    (Ne.symm (activeBit_work_wire_ne n counterWidth tempIndex))
    (Ne.symm (activeBit_scratchABit_wire_ne n counterWidth))
    (Ne.symm (activeBit_scratchBBit_wire_ne n counterWidth)) x

/-- Selected branch-code staging preserves the comparison result. -/
theorem selectedBranchCodeToScratchStep_get_compare
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) =
      (compareBit n counterWidth).get x := by
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (compareBit n counterWidth)
    (uLowBit_compareBit_wire_ne n counterWidth low)
    (vLowBit_compareBit_wire_ne n counterWidth low)
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) tempIndex))
    (Ne.symm (compareBit_scratchABit_wire_ne n counterWidth))
    (Ne.symm (compareBit_scratchBBit_wire_ne n counterWidth)) x

/-- Selected branch-code staging preserves every persistent history slot. -/
theorem selectedBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (historyBit n counterWidth historyIndex).get
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) =
      (historyBit n counterWidth historyIndex).get x := by
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (historyBit n counterWidth historyIndex)
    (by
      simpa [uLowBit, uValueWord, historyBit,
        RegisterBits.uValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire low) historyIndex))
    (by
      simpa [vLowBit, vValueWord, historyBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_history_wire_ne n counterWidth
            (WireAddress.littleEndianWire low) historyIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.historyBit n counterWidth historyIndex) tempIndex))
    (scratchABit_historyBit_wire_ne n counterWidth historyIndex)
    (scratchBBit_historyBit_wire_ne n counterWidth historyIndex) x

theorem selectedBranchCodeToScratchStep_get_path
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    (pathBit n counterWidth).get
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) =
      (pathBit n counterWidth).get x := by
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (pathBit n counterWidth)
    (by
      simpa [uLowBit, uValueWord, pathBit, RegisterBits.uValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth low)
          (sharedPathBit n counterWidth))
    (by
      simpa [vLowBit, vValueWord, pathBit, RegisterBits.vValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth low)
          (sharedPathBit n counterWidth))
    (pathBit_coefficientCarryWorkBit_wire_ne
      n counterWidth tempIndex).symm
    (by
      simpa [scratchABit, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedPathBit n counterWidth))
    (by
      simpa [scratchBBit, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchBBit n counterWidth)
          (sharedPathBit n counterWidth)) x

/-- Every non-borrowed VBE carry bit is preserved by branch-code staging. -/
theorem selectedBranchCodeToScratchStep_get_work_of_ne
    (n counterWidth : Nat) (low tempIndex observed : Fin n)
    (hne : tempIndex ≠ observed) (x : Registers n counterWidth) :
    (coefficientCarryWorkBit n counterWidth observed).get
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) =
      (coefficientCarryWorkBit n counterWidth observed).get x := by
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (coefficientCarryWorkBit n counterWidth observed)
    (uLowBit_work_wire_ne n counterWidth low observed)
    (vLowBit_work_wire_ne n counterWidth low observed)
    (coefficientCarryWorkBit_wire_ne n counterWidth hne)
    (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth) observed)
    (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth) observed) x

/-- Branch-code staging preserves every coefficient bit. -/
theorem selectedBranchCodeToScratchStep_get_rCoeffValueBit
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (bit : Fin (n + 1)) (x : Registers n counterWidth) :
    (rCoeffValueBit n counterWidth bit).get
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) =
      (rCoeffValueBit n counterWidth bit).get x := by
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (rCoeffValueBit n counterWidth bit)
    (by
      simpa [uLowBit, uValueWord, rCoeffValueBit,
        RegisterBits.uValueBit, RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire low)
            (WireAddress.littleEndianWire bit)))
    (by
      simpa [vLowBit, vValueWord, rCoeffValueBit,
        RegisterBits.vValueBit, RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire low)
            (WireAddress.littleEndianWire bit)))
    (by
      simpa [rCoeffValueBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.rCoeffValueBit n counterWidth bit) tempIndex).symm)
    (by
      simpa [rCoeffValueBit, scratchABit,
        RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)).symm)
    (by
      simpa [rCoeffValueBit, scratchBBit,
        RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)).symm) x

/-- Branch-code staging preserves the whole compact `u` word. -/
theorem selectedBranchCodeToScratchStep_core_u
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    (selectedBranchCodeToScratchStep n counterWidth low tempIndex x).core.u =
      x.core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [selectedBranchCodeToScratchStep_eq_core]
  by_cases hbit : bit = low
  · subst bit
    have h := selectedBranchCodeToScratchStepCore_get_u
      (uLowBit n counterWidth low) (vLowBit n counterWidth low)
      (coefficientCarryWorkBit n counterWidth tempIndex)
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) (scratchBBit n counterWidth)
      (uLowBit_vLowBit_wire_ne n counterWidth low low)
      (uLowBit_work_wire_ne n counterWidth low tempIndex)
      (uLowBit_scratchABit_wire_ne n counterWidth low)
      (uLowBit_scratchBBit_wire_ne n counterWidth low) x
    simpa [uLowBit] using h
  · have h := selectedBranchCodeToScratchStepCore_get_of_targets_ne
      (uLowBit n counterWidth low) (vLowBit n counterWidth low)
      (coefficientCarryWorkBit n counterWidth tempIndex)
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) (scratchBBit n counterWidth)
      ((uValueWord n counterWidth).bit bit)
      (by
        simpa [uLowBit, uValueWord, RegisterBits.uValueBit] using
          liftCoreBit_wire_ne n counterWidth
            (u_u_wire_ne n counterWidth
              (WireAddress.littleEndianWire low)
              (WireAddress.littleEndianWire bit)
              (littleEndianWire_ne (Ne.symm hbit))))
      (by
        simpa [vLowBit, uValueWord, vValueWord, RegisterBits.uValueBit,
          RegisterBits.vValueBit] using
          (liftCoreBit_wire_ne n counterWidth
            (RegisterBits.u_v_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)
              (WireAddress.littleEndianWire low))).symm)
      (by
        simpa [uValueWord] using
          (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
            (RegisterBits.uValueBit n counterWidth bit) tempIndex).symm)
      (by
        simpa [uValueWord, scratchABit, RegisterBits.uValueBit] using
          (liftCoreBit_wire_ne n counterWidth
            (RegisterBits.u_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit))).symm)
      (by
        simpa [uValueWord, scratchBBit, RegisterBits.uValueBit] using
          (liftCoreBit_wire_ne n counterWidth
            (RegisterBits.u_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit))).symm) x
    simpa only [uValueWord_get] using h

/-- Branch-code staging preserves the whole compact `v` word. -/
theorem selectedBranchCodeToScratchStep_core_v
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    (selectedBranchCodeToScratchStep n counterWidth low tempIndex x).core.v =
      x.core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [selectedBranchCodeToScratchStep_eq_core]
  by_cases hbit : bit = low
  · subst bit
    have h := selectedBranchCodeToScratchStepCore_get_v
      (uLowBit n counterWidth low) (vLowBit n counterWidth low)
      (coefficientCarryWorkBit n counterWidth tempIndex)
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) (scratchBBit n counterWidth)
      (uLowBit_vLowBit_wire_ne n counterWidth low low)
      (vLowBit_work_wire_ne n counterWidth low tempIndex)
      (vLowBit_scratchABit_wire_ne n counterWidth low)
      (vLowBit_scratchBBit_wire_ne n counterWidth low) x
    simpa [vLowBit] using h
  · have h := selectedBranchCodeToScratchStepCore_get_of_targets_ne
      (uLowBit n counterWidth low) (vLowBit n counterWidth low)
      (coefficientCarryWorkBit n counterWidth tempIndex)
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) (scratchBBit n counterWidth)
      ((vValueWord n counterWidth).bit bit)
      (by
        simpa [uLowBit, vValueWord, uValueWord, RegisterBits.uValueBit,
          RegisterBits.vValueBit] using
          liftCoreBit_wire_ne n counterWidth
            (RegisterBits.u_v_wire_ne n counterWidth
              (WireAddress.littleEndianWire low)
              (WireAddress.littleEndianWire bit)))
      (by
        simpa [vLowBit, vValueWord, RegisterBits.vValueBit] using
          liftCoreBit_wire_ne n counterWidth
            (v_v_wire_ne n counterWidth
              (WireAddress.littleEndianWire low)
              (WireAddress.littleEndianWire bit)
              (littleEndianWire_ne (Ne.symm hbit))))
      (by
        simpa [vValueWord] using
          (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
            (RegisterBits.vValueBit n counterWidth bit) tempIndex).symm)
      (by
        simpa [vValueWord, scratchABit, RegisterBits.vValueBit] using
          (liftCoreBit_wire_ne n counterWidth
            (RegisterBits.v_scratchA_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit))).symm)
      (by
        simpa [vValueWord, scratchBBit, RegisterBits.vValueBit] using
          (liftCoreBit_wire_ne n counterWidth
            (RegisterBits.v_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit))).symm) x
    simpa only [vValueWord_get] using h

/-- Branch-code staging preserves the whole compact `s` coefficient word. -/
theorem selectedBranchCodeToScratchStep_core_sCoeff
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    (selectedBranchCodeToScratchStep n counterWidth low tempIndex x).core.sCoeff =
      x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  rw [selectedBranchCodeToScratchStep_eq_core]
  have h := selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    ((sCoeffValueWord n counterWidth).bit bit)
    (by
      simpa [uLowBit, uValueWord, sCoeffValueWord, sCoeffValueBit,
        RegisterBits.uValueBit, RegisterBits.sCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire low)
            (WireAddress.littleEndianWire bit)))
    (by
      simpa [vLowBit, vValueWord, sCoeffValueWord, sCoeffValueBit,
        RegisterBits.vValueBit, RegisterBits.sCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire low)
            (WireAddress.littleEndianWire bit)))
    (by
      simpa [sCoeffValueWord, sCoeffValueBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.sCoeffValueBit n counterWidth bit) tempIndex).symm)
    (by
      simpa [sCoeffValueWord, sCoeffValueBit, scratchABit,
        RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [sCoeffValueWord, sCoeffValueBit, scratchBBit,
        RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm) x
  simpa only [sCoeffValueWord, sCoeffValueBit_get] using h

/-- Branch-code staging preserves the whole compact `r` coefficient word. -/
theorem selectedBranchCodeToScratchStep_core_rCoeff
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    (selectedBranchCodeToScratchStep n counterWidth low tempIndex x).core.rCoeff =
      x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa only [rCoeffValueBit_get] using
    selectedBranchCodeToScratchStep_get_rCoeffValueBit
      n counterWidth low tempIndex bit x

/-- On clean code targets and a clean borrowed VBE bit, branch-code staging
restores the borrowed bit. -/
theorem selectedBranchCodeToScratchStep_get_temp_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    (coefficientCarryWorkBit n counterWidth tempIndex).get
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) =
      false := by
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_temp_clean
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (uLowBit_vLowBit_wire_ne n counterWidth low low)
    (uLowBit_work_wire_ne n counterWidth low tempIndex)
    (uLowBit_activeBit_wire_ne n counterWidth low)
    (uLowBit_compareBit_wire_ne n counterWidth low)
    (uLowBit_scratchABit_wire_ne n counterWidth low)
    (uLowBit_scratchBBit_wire_ne n counterWidth low)
    (vLowBit_work_wire_ne n counterWidth low tempIndex)
    (vLowBit_activeBit_wire_ne n counterWidth low)
    (vLowBit_compareBit_wire_ne n counterWidth low)
    (vLowBit_scratchABit_wire_ne n counterWidth low)
    (vLowBit_scratchBBit_wire_ne n counterWidth low)
    (Ne.symm (activeBit_work_wire_ne n counterWidth tempIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) tempIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth) tempIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth) tempIndex))
    (activeBit_compareBit_wire_ne n counterWidth)
    (activeBit_scratchABit_wire_ne n counterWidth)
    (activeBit_scratchBBit_wire_ne n counterWidth)
    (compareBit_scratchABit_wire_ne n counterWidth)
    (compareBit_scratchBBit_wire_ne n counterWidth)
    (scratchABit_scratchBBit_wire_ne n counterWidth)
    x hscratchA hscratchB htemp

/-- On clean code targets and borrowed work, scratchA stores the selected
auxiliary branch bit. -/
theorem selectedBranchCodeToScratchStep_get_scratchA_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    (scratchABit n counterWidth).get
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) =
      ((activeBit n counterWidth).get x &&
        (!(uLowBit n counterWidth low).get x ||
          (uLowBit n counterWidth low).get x &&
            (vLowBit n counterWidth low).get x &&
              (compareBit n counterWidth).get x)) := by
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_scratchA_clean
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (uLowBit_vLowBit_wire_ne n counterWidth low low)
    (uLowBit_work_wire_ne n counterWidth low tempIndex)
    (uLowBit_activeBit_wire_ne n counterWidth low)
    (uLowBit_compareBit_wire_ne n counterWidth low)
    (uLowBit_scratchABit_wire_ne n counterWidth low)
    (uLowBit_scratchBBit_wire_ne n counterWidth low)
    (vLowBit_work_wire_ne n counterWidth low tempIndex)
    (vLowBit_activeBit_wire_ne n counterWidth low)
    (vLowBit_compareBit_wire_ne n counterWidth low)
    (vLowBit_scratchABit_wire_ne n counterWidth low)
    (vLowBit_scratchBBit_wire_ne n counterWidth low)
    (Ne.symm (activeBit_work_wire_ne n counterWidth tempIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) tempIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth) tempIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth) tempIndex))
    (activeBit_compareBit_wire_ne n counterWidth)
    (activeBit_scratchABit_wire_ne n counterWidth)
    (activeBit_scratchBBit_wire_ne n counterWidth)
    (compareBit_scratchABit_wire_ne n counterWidth)
    (compareBit_scratchBBit_wire_ne n counterWidth)
    (scratchABit_scratchBBit_wire_ne n counterWidth)
    x hscratchA hscratchB htemp

/-- On clean code targets and borrowed work, scratchB stores the selected
persistent-history bit. -/
theorem selectedBranchCodeToScratchStep_get_scratchB_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    (scratchBBit n counterWidth).get
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) =
      ((activeBit n counterWidth).get x &&
        ((uLowBit n counterWidth low).get x &&
            !(vLowBit n counterWidth low).get x ||
          (uLowBit n counterWidth low).get x &&
            (vLowBit n counterWidth low).get x &&
              (compareBit n counterWidth).get x)) := by
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_scratchB_clean
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (uLowBit_vLowBit_wire_ne n counterWidth low low)
    (uLowBit_work_wire_ne n counterWidth low tempIndex)
    (uLowBit_activeBit_wire_ne n counterWidth low)
    (uLowBit_compareBit_wire_ne n counterWidth low)
    (uLowBit_scratchABit_wire_ne n counterWidth low)
    (uLowBit_scratchBBit_wire_ne n counterWidth low)
    (vLowBit_work_wire_ne n counterWidth low tempIndex)
    (vLowBit_activeBit_wire_ne n counterWidth low)
    (vLowBit_compareBit_wire_ne n counterWidth low)
    (vLowBit_scratchABit_wire_ne n counterWidth low)
    (vLowBit_scratchBBit_wire_ne n counterWidth low)
    (Ne.symm (activeBit_work_wire_ne n counterWidth tempIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) tempIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth) tempIndex))
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth) tempIndex))
    (activeBit_compareBit_wire_ne n counterWidth)
    (activeBit_scratchABit_wire_ne n counterWidth)
    (activeBit_scratchBBit_wire_ne n counterWidth)
    (compareBit_scratchABit_wire_ne n counterWidth)
    (compareBit_scratchBBit_wire_ne n counterWidth)
    (scratchABit_scratchBBit_wire_ne n counterWidth)
    x hscratchA hscratchB htemp

/-- With a false comparison bit, the all-code staging reduces exactly to the
even-only staging.  This bridge reuses the established even-route semantic
certificates without occupying the scratch pair before odd arithmetic. -/
theorem selectedBranchCodeToScratchStep_eq_selectedEven_of_compare_false_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false) :
    selectedBranchCodeToScratchStep n counterWidth low tempIndex x =
      selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex x := by
  rw [selectedBranchCodeToScratchStep_eq_core,
    selectedEvenBranchCodeToScratchStep_eq_core]
  unfold selectedBranchCodeToScratchStepCore
    selectedEvenBranchCodeToScratchStepCore
  rw [oddOddCompareBranchCodeToScratchStepCore_eq_self_of_compare_false_clean
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (uLowBit_work_wire_ne n counterWidth low tempIndex)
    (vLowBit_work_wire_ne n counterWidth low tempIndex)
    (activeBit_work_wire_ne n counterWidth tempIndex).symm
    (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) tempIndex).symm
    (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth) tempIndex).symm
    (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchBBit n counterWidth) tempIndex).symm
    (activeBit_scratchABit_wire_ne n counterWidth)
    (compareBit_scratchABit_wire_ne n counterWidth)
    (compareBit_scratchBBit_wire_ne n counterWidth)
    (scratchABit_scratchBBit_wire_ne n counterWidth)
    x hcompare hscratchA hscratchB]

/-! ### Selected branch code, sole history word, and shift dispatch -/

def selectedBranchCodeThenHistoryThenShiftGates
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  selectedBranchCodeToScratchGates n counterWidth low tempIndex ++
    [activeScratchBToHistoryGate n counterWidth historyIndex] ++
      auxActiveShiftDispatchGates n counterWidth

def selectedBranchCodeThenHistoryThenShiftStep
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x => auxActiveShiftDispatchStep n counterWidth
    (activeScratchBToHistoryStep n counterWidth historyIndex
      (selectedBranchCodeToScratchStep n counterWidth low tempIndex x))

def selectedBranchCodeThenHistoryThenShiftProgram
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (selectedBranchCodeThenHistoryThenShiftGates
      n counterWidth low tempIndex historyIndex)

theorem selectedBranchCodeThenHistoryThenShift_realizes
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (selectedBranchCodeThenHistoryThenShiftProgram
        n counterWidth low tempIndex historyIndex)
      (selectedBranchCodeThenHistoryThenShiftStep
        n counterWidth low tempIndex historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (selectedBranchCodeThenHistoryThenShiftGates
      n counterWidth low tempIndex historyIndex) (by
        intro x
        unfold selectedBranchCodeThenHistoryThenShiftGates
          selectedBranchCodeThenHistoryThenShiftStep
          selectedBranchCodeToScratchStep activeScratchBToHistoryStep
        repeat rw [EncodedBit.GateSpec.stepList_append]
        rw [auxActiveShiftDispatchStep_eq_gateList]
        rfl)

theorem selectedBranchCodeThenHistoryThenShiftGates_length
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    (selectedBranchCodeThenHistoryThenShiftGates
      n counterWidth low tempIndex historyIndex).length = 18 * n + 6 := by
  simp only [selectedBranchCodeThenHistoryThenShiftGates,
    List.length_append, List.length_cons, List.length_nil,
    selectedBranchCodeToScratchGates_length,
    auxActiveShiftDispatchGates_length]
  have hpositive : 0 < n := by
    have hlt := low.isLt
    omega
  omega

theorem selectedBranchCodeThenHistoryThenShiftGates_xMultiplicity_sum
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    ((selectedBranchCodeThenHistoryThenShiftGates
      n counterWidth low tempIndex historyIndex).map
        EncodedBit.GateSpec.xMultiplicity).sum = 4 := by
  simp only [selectedBranchCodeThenHistoryThenShiftGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    selectedBranchCodeToScratchGates_xMultiplicity_sum,
    activeScratchBToHistoryGate_xMultiplicity,
    auxActiveShiftDispatchGates_xMultiplicity_sum]
  rfl

theorem selectedBranchCodeThenHistoryThenShiftGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    ((selectedBranchCodeThenHistoryThenShiftGates
      n counterWidth low tempIndex historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp only [selectedBranchCodeThenHistoryThenShiftGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    selectedBranchCodeToScratchGates_cnotMultiplicity_sum,
    activeScratchBToHistoryGate_cnotMultiplicity,
    auxActiveShiftDispatchGates_cnotMultiplicity_sum]
  rfl

theorem selectedBranchCodeThenHistoryThenShiftGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    ((selectedBranchCodeThenHistoryThenShiftGates
      n counterWidth low tempIndex historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 18 * n + 1 := by
  simp only [selectedBranchCodeThenHistoryThenShiftGates,
    List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    selectedBranchCodeToScratchGates_toffoliMultiplicity_sum,
    activeScratchBToHistoryGate_toffoliMultiplicity,
    auxActiveShiftDispatchGates_toffoliMultiplicity_sum]
  have hpositive : 0 < n := by
    have hlt := low.isLt
    omega
  omega

theorem selectedBranchCodeThenHistoryThenShiftStep_get_active
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (selectedBranchCodeThenHistoryThenShiftStep
          n counterWidth low tempIndex historyIndex x) =
      (activeBit n counterWidth).get x := by
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_active,
    activeScratchBToHistoryStep_get_active,
    selectedBranchCodeToScratchStep_get_active]

theorem selectedBranchCodeThenHistoryThenShiftStep_get_path
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (pathBit n counterWidth).get
        (selectedBranchCodeThenHistoryThenShiftStep
          n counterWidth low tempIndex historyIndex x) =
      (pathBit n counterWidth).get x := by
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth (pathBit n counterWidth)]
  · rw [activeScratchBToHistoryStep_get_of_target_ne
      n counterWidth historyIndex (pathBit n counterWidth)]
    · exact selectedBranchCodeToScratchStep_get_path
        n counterWidth low tempIndex x
    · simpa [historyBit, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.historyBit n counterWidth historyIndex)
          (sharedPathBit n counterWidth)
  · intro bit
    simpa [uValueWord, pathBit, RegisterBits.uValueBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.uValueBit n counterWidth bit)
        (sharedPathBit n counterWidth)
  · intro bit
    simpa [sCoeffValueWord, sCoeffValueBit, pathBit,
      RegisterBits.sCoeffValueBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.sCoeffValueBit n counterWidth bit)
        (sharedPathBit n counterWidth)
  · intro bit
    simpa [vValueWord, pathBit, RegisterBits.vValueBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth bit)
        (sharedPathBit n counterWidth)
  · intro bit
    simpa [rCoeffValueWord, rCoeffValueBit, pathBit,
      RegisterBits.rCoeffValueBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.rCoeffValueBit n counterWidth bit)
        (sharedPathBit n counterWidth)

theorem selectedBranchCodeThenHistoryThenShiftStep_get_compare
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (selectedBranchCodeThenHistoryThenShiftStep
          n counterWidth low tempIndex historyIndex x) =
      (compareBit n counterWidth).get x := by
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_compare,
    activeScratchBToHistoryStep_get_compare,
    selectedBranchCodeToScratchStep_get_compare]

theorem selectedBranchCodeThenHistoryThenShiftStep_get_scratchA_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    (scratchABit n counterWidth).get
        (selectedBranchCodeThenHistoryThenShiftStep
          n counterWidth low tempIndex historyIndex x) =
      ((activeBit n counterWidth).get x &&
        (!(uLowBit n counterWidth low).get x ||
          (uLowBit n counterWidth low).get x &&
            (vLowBit n counterWidth low).get x &&
              (compareBit n counterWidth).get x)) := by
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_scratchA,
    activeScratchBToHistoryStep_get_scratchA]
  exact selectedBranchCodeToScratchStep_get_scratchA_clean
    n counterWidth low tempIndex x hscratchA hscratchB htemp

theorem selectedBranchCodeThenHistoryThenShiftStep_get_scratchB_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    (scratchBBit n counterWidth).get
        (selectedBranchCodeThenHistoryThenShiftStep
          n counterWidth low tempIndex historyIndex x) =
      ((activeBit n counterWidth).get x &&
        ((uLowBit n counterWidth low).get x &&
            !(vLowBit n counterWidth low).get x ||
          (uLowBit n counterWidth low).get x &&
            (vLowBit n counterWidth low).get x &&
              (compareBit n counterWidth).get x)) := by
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_scratchB,
    activeScratchBToHistoryStep_get_scratchB]
  exact selectedBranchCodeToScratchStep_get_scratchB_clean
    n counterWidth low tempIndex x hscratchA hscratchB htemp

theorem selectedBranchCodeThenHistoryThenShiftStep_get_history_clean
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    (historyBit n counterWidth historyIndex).get
        (selectedBranchCodeThenHistoryThenShiftStep
          n counterWidth low tempIndex historyIndex x) =
      ((historyBit n counterWidth historyIndex).get x ^^
        ((activeBit n counterWidth).get x &&
          ((uLowBit n counterWidth low).get x &&
              !(vLowBit n counterWidth low).get x ||
            (uLowBit n counterWidth low).get x &&
              (vLowBit n counterWidth low).get x &&
                (compareBit n counterWidth).get x))) := by
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_historyBit,
    activeScratchBToHistoryStep_get_historyBit,
    selectedBranchCodeToScratchStep_get_historyBit,
    selectedBranchCodeToScratchStep_get_active,
    selectedBranchCodeToScratchStep_get_scratchB_clean
      n counterWidth low tempIndex x hscratchA hscratchB htemp]
  cases (activeBit n counterWidth).get x <;> simp

theorem selectedBranchCodeThenHistoryThenShiftStep_get_work_clean
    (n counterWidth : Nat) (low tempIndex observed : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (coefficientCarryWorkBit n counterWidth observed).get
        (selectedBranchCodeThenHistoryThenShiftStep
          n counterWidth low tempIndex historyIndex x) = false := by
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_coefficientCarryWorkBit]
  rw [activeScratchBToHistoryStep_get_of_target_ne n counterWidth historyIndex
    (coefficientCarryWorkBit n counterWidth observed)
    (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.historyBit n counterWidth historyIndex) observed)]
  by_cases hindex : tempIndex = observed
  · subst observed
    exact selectedBranchCodeToScratchStep_get_temp_clean
      n counterWidth low tempIndex x hscratchA hscratchB (hwork tempIndex)
  · rw [selectedBranchCodeToScratchStep_get_work_of_ne
      n counterWidth low tempIndex observed hindex x]
    exact hwork observed

theorem selectedBranchCodeThenHistoryThenShiftStep_get_carryIn
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (coefficientCarryInBit n counterWidth).get
        (selectedBranchCodeThenHistoryThenShiftStep
          n counterWidth low tempIndex historyIndex x) =
      (coefficientCarryInBit n counterWidth).get x := by
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_coefficientCarryInBit]
  rw [activeScratchBToHistoryStep_get_of_target_ne n counterWidth historyIndex
    (coefficientCarryInBit n counterWidth)
    (liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
      (RegisterBits.historyBit n counterWidth historyIndex))]
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    (coefficientCarryInBit n counterWidth)
    (by
      simpa [uLowBit, uValueWord, RegisterBits.uValueBit] using
        liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth low))
    (by
      simpa [vLowBit, vValueWord, RegisterBits.vValueBit] using
        liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth low))
    (coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
      n counterWidth tempIndex).symm
    (by
      simpa [scratchABit] using
        liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth))
    (by
      simpa [scratchBBit] using
        liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
          (RegisterBits.scratchBBit n counterWidth))
    x

/-- The selected even-route staging and shift restore the sole VBE carry
bank after borrowing one work bit for branch-code synthesis. -/
theorem selectedBranchCodeThenHistoryThenShiftStep_coefficientAdder_cleanEndpoint
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (selectedBranchCodeThenHistoryThenShiftStep
      n counterWidth low tempIndex historyIndex x).shared.coefficientAdder =
        cleanCoeffAdderWork n := by
  apply Prod.ext
  · change (coefficientCarryInBit n counterWidth).get
        (selectedBranchCodeThenHistoryThenShiftStep
          n counterWidth low tempIndex historyIndex x) = false
    rw [selectedBranchCodeThenHistoryThenShiftStep_get_carryIn, hcarry]
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    exact selectedBranchCodeThenHistoryThenShiftStep_get_work_clean
      n counterWidth low tempIndex bit historyIndex x hscratchA hscratchB hwork

/-- The complete selected even route preserves every observation outside its
two branch-code targets, borrowed temporary bit, selected history target, and
the four conditionally shifted words. -/
theorem selectedBranchCodeThenHistoryThenShiftStep_get_of_preserved
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (observed : EncodedBit (encoding n counterWidth))
    (huLow : (uLowBit n counterWidth low).wire ≠ observed.wire)
    (hvLow : (vLowBit n counterWidth low).wire ≠ observed.wire)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).wire ≠
      observed.wire)
    (hscratchA : (scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB : (scratchBBit n counterWidth).wire ≠ observed.wire)
    (hhistory : (historyBit n counterWidth historyIndex).wire ≠
      observed.wire)
    (hu : ∀ bit, ((uValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hs : ∀ bit,
      ((sCoeffValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hv : ∀ bit, ((vValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hr : ∀ bit,
      ((rCoeffValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (selectedBranchCodeThenHistoryThenShiftStep
        n counterWidth low tempIndex historyIndex x) = observed.get x := by
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth observed hu hs hv hr]
  rw [activeScratchBToHistoryStep_get_of_target_ne
    n counterWidth historyIndex observed hhistory]
  rw [selectedBranchCodeToScratchStep_eq_core]
  exact selectedBranchCodeToScratchStepCore_get_of_targets_ne
    (uLowBit n counterWidth low) (vLowBit n counterWidth low)
    (coefficientCarryWorkBit n counterWidth tempIndex)
    (activeBit n counterWidth) (compareBit n counterWidth)
    (scratchABit n counterWidth) (scratchBBit n counterWidth)
    observed huLow hvLow htemp hscratchA hscratchB x

/-- Clean active `uEven` code selects the compact `u/s` shift group. -/
theorem selectedBranchCodeThenHistoryThenShiftStep_eq_uShift_of_uEven
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (huLow : (uLowBit n counterWidth low).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    selectedBranchCodeThenHistoryThenShiftStep
        n counterWidth low tempIndex historyIndex x =
      uDiv2ThenSMul2Step n counterWidth
        (activeScratchBToHistoryStep n counterWidth historyIndex
          (selectedBranchCodeToScratchStep n counterWidth low tempIndex x)) := by
  let staged := selectedBranchCodeToScratchStep n counterWidth low tempIndex x
  let written := activeScratchBToHistoryStep n counterWidth historyIndex staged
  have hactiveWritten : (activeBit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [activeScratchBToHistoryStep_get_active,
      selectedBranchCodeToScratchStep_get_active, hactive]
  have hauxWritten : (scratchABit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [activeScratchBToHistoryStep_get_scratchA,
      selectedBranchCodeToScratchStep_get_scratchA_clean
        n counterWidth low tempIndex x hscratchA hscratchB htemp,
      hactive, huLow]
    rfl
  exact auxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step
    n counterWidth written hactiveWritten hauxWritten

/-- Clean active `vEven` code selects the compact `v/r` shift group. -/
theorem selectedBranchCodeThenHistoryThenShiftStep_eq_vShift_of_vEven
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (huLow : (uLowBit n counterWidth low).get x = true)
    (hvLow : (vLowBit n counterWidth low).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get x = false) :
    selectedBranchCodeThenHistoryThenShiftStep
        n counterWidth low tempIndex historyIndex x =
      vDiv2ThenRMul2Step n counterWidth
        (activeScratchBToHistoryStep n counterWidth historyIndex
          (selectedBranchCodeToScratchStep n counterWidth low tempIndex x)) := by
  let staged := selectedBranchCodeToScratchStep n counterWidth low tempIndex x
  let written := activeScratchBToHistoryStep n counterWidth historyIndex staged
  have hactiveWritten : (activeBit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [activeScratchBToHistoryStep_get_active,
      selectedBranchCodeToScratchStep_get_active, hactive]
  have hauxWritten : (scratchABit n counterWidth).get written = false := by
    dsimp [written, staged]
    rw [activeScratchBToHistoryStep_get_scratchA,
      selectedBranchCodeToScratchStep_get_scratchA_clean
        n counterWidth low tempIndex x hscratchA hscratchB htemp,
      hactive, huLow, hvLow]
    rfl
  exact auxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step
    n counterWidth written hactiveWritten hauxWritten

/-! ### Odd-branch code carried by the restored comparison bit -/

/-- After the compact odd arithmetic slice, `compare = true` selects
`uGreater`, whose branch code is `11`; `compare = false` selects `vLe`, whose
branch code is `00`.  The two Toffoli leaves therefore stage the complete odd
branch code without rereading the low source bits changed by subtraction. -/
def oddBranchCodeToScratchGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  [ EncodedBit.GateSpec.toffoli
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth)
      (activeBit_compareBit_wire_ne n counterWidth)
      (activeBit_scratchABit_wire_ne n counterWidth)
      (compareBit_scratchABit_wire_ne n counterWidth)
  , EncodedBit.GateSpec.toffoli
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchBBit n counterWidth)
      (activeBit_compareBit_wire_ne n counterWidth)
      (activeBit_scratchBBit_wire_ne n counterWidth)
      (compareBit_scratchBBit_wire_ne n counterWidth) ]

/-- Odd-branch code staging is disjoint from every public target bit. -/
theorem oddBranchCodeToScratchGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ oddBranchCodeToScratchGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  simp only [oddBranchCodeToScratchGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) targetIndex⟩
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth) targetIndex⟩

def oddBranchCodeToScratchStep (n counterWidth : Nat) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (oddBranchCodeToScratchGates n counterWidth)

def oddBranchCodeToScratchProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (oddBranchCodeToScratchGates n counterWidth)

theorem oddBranchCodeToScratch_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (oddBranchCodeToScratchProgram n counterWidth)
      (oddBranchCodeToScratchStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (oddBranchCodeToScratchGates n counterWidth)

@[simp] theorem oddBranchCodeToScratchGates_length
    (n counterWidth : Nat) :
    (oddBranchCodeToScratchGates n counterWidth).length = 2 := by
  rfl

@[simp] theorem oddBranchCodeToScratchGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((oddBranchCodeToScratchGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  rfl

@[simp] theorem oddBranchCodeToScratchGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((oddBranchCodeToScratchGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  rfl

@[simp] theorem oddBranchCodeToScratchGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((oddBranchCodeToScratchGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 := by
  rfl

theorem oddBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (oddBranchCodeToScratchStep n counterWidth x) =
      (activeBit n counterWidth).get x := by
  unfold oddBranchCodeToScratchStep oddBranchCodeToScratchGates
  change (activeBit n counterWidth).get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (compareBit n counterWidth) (scratchBBit n counterWidth)
        (EncodedBit.toffoliStep (activeBit n counterWidth)
          (compareBit n counterWidth) (scratchABit n counterWidth) x)) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchBBit n counterWidth) (activeBit n counterWidth)
      (activeBit_scratchBBit_wire_ne n counterWidth).symm,
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) (activeBit n counterWidth)
      (activeBit_scratchABit_wire_ne n counterWidth).symm]

theorem oddBranchCodeToScratchStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (oddBranchCodeToScratchStep n counterWidth x) =
      (compareBit n counterWidth).get x := by
  unfold oddBranchCodeToScratchStep oddBranchCodeToScratchGates
  change (compareBit n counterWidth).get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (compareBit n counterWidth) (scratchBBit n counterWidth)
        (EncodedBit.toffoliStep (activeBit n counterWidth)
          (compareBit n counterWidth) (scratchABit n counterWidth) x)) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchBBit n counterWidth) (compareBit n counterWidth)
      (compareBit_scratchBBit_wire_ne n counterWidth).symm,
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) (compareBit n counterWidth)
      (compareBit_scratchABit_wire_ne n counterWidth).symm]

theorem oddBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get
        (oddBranchCodeToScratchStep n counterWidth x) =
      ((scratchABit n counterWidth).get x ^^
        ((activeBit n counterWidth).get x &&
          (compareBit n counterWidth).get x)) := by
  unfold oddBranchCodeToScratchStep oddBranchCodeToScratchGates
  change (scratchABit n counterWidth).get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (compareBit n counterWidth) (scratchBBit n counterWidth)
        (EncodedBit.toffoliStep (activeBit n counterWidth)
          (compareBit n counterWidth) (scratchABit n counterWidth) x)) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchBBit n counterWidth) (scratchABit n counterWidth)
      (scratchABit_scratchBBit_wire_ne n counterWidth).symm,
    EncodedBit.toffoliStep_get_target]

theorem oddBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (scratchBBit n counterWidth).get
        (oddBranchCodeToScratchStep n counterWidth x) =
      ((scratchBBit n counterWidth).get x ^^
        ((activeBit n counterWidth).get x &&
          (compareBit n counterWidth).get x)) := by
  unfold oddBranchCodeToScratchStep oddBranchCodeToScratchGates
  change (scratchBBit n counterWidth).get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (compareBit n counterWidth) (scratchBBit n counterWidth)
        (EncodedBit.toffoliStep (activeBit n counterWidth)
          (compareBit n counterWidth) (scratchABit n counterWidth) x)) = _
  rw [EncodedBit.toffoliStep_get_target,
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) (scratchBBit n counterWidth)
      (scratchABit_scratchBBit_wire_ne n counterWidth),
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) (activeBit n counterWidth)
      (activeBit_scratchABit_wire_ne n counterWidth).symm,
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) (compareBit n counterWidth)
      (compareBit_scratchABit_wire_ne n counterWidth).symm]

theorem oddBranchCodeToScratchStep_eq_self_of_compare_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcompare : (compareBit n counterWidth).get x = false) :
    oddBranchCodeToScratchStep n counterWidth x = x := by
  have hcoreCompare : x.core.compare = false := by
    simpa only [compareBit_get] using hcompare
  unfold oddBranchCodeToScratchStep oddBranchCodeToScratchGates
  simp [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.toffoliStep, hcoreCompare]

/-- The fixed odd-code staging preserves every bit other than its two scratch
targets. -/
theorem oddBranchCodeToScratchStep_get_of_targets_ne
    (n counterWidth : Nat) (observed : EncodedBit (encoding n counterWidth))
    (hscratchA : (scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB : (scratchBBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (oddBranchCodeToScratchStep n counterWidth x) =
      observed.get x := by
  unfold oddBranchCodeToScratchStep oddBranchCodeToScratchGates
  change observed.get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (compareBit n counterWidth) (scratchBBit n counterWidth)
        (EncodedBit.toffoliStep (activeBit n counterWidth)
          (compareBit n counterWidth) (scratchABit n counterWidth) x)) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchBBit n counterWidth) observed hscratchB,
    EncodedBit.toffoliStep_get_of_target_ne
      (activeBit n counterWidth) (compareBit n counterWidth)
      (scratchABit n counterWidth) observed hscratchA]

/-- Odd branch-code staging preserves the complete compact `u` word. -/
theorem oddBranchCodeToScratchStep_core_u
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (oddBranchCodeToScratchStep n counterWidth x).core.u = x.core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := oddBranchCodeToScratchStep_get_of_targets_ne
    n counterWidth ((uValueWord n counterWidth).bit bit)
    (by
      simpa [uValueWord, scratchABit, RegisterBits.uValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [uValueWord, scratchBBit, RegisterBits.uValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm) x
  simpa only [uValueWord_get] using h

/-- Odd branch-code staging preserves the complete compact `v` word. -/
theorem oddBranchCodeToScratchStep_core_v
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (oddBranchCodeToScratchStep n counterWidth x).core.v = x.core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := oddBranchCodeToScratchStep_get_of_targets_ne
    n counterWidth ((vValueWord n counterWidth).bit bit)
    (by
      simpa [vValueWord, scratchABit, RegisterBits.vValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [vValueWord, scratchBBit, RegisterBits.vValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm) x
  simpa only [vValueWord_get] using h

/-- Odd branch-code staging preserves the complete compact `s` word. -/
theorem oddBranchCodeToScratchStep_core_sCoeff
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (oddBranchCodeToScratchStep n counterWidth x).core.sCoeff =
      x.core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := oddBranchCodeToScratchStep_get_of_targets_ne
    n counterWidth ((sCoeffValueWord n counterWidth).bit bit)
    (by
      simpa [sCoeffValueWord, sCoeffValueBit, scratchABit,
        RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [sCoeffValueWord, sCoeffValueBit, scratchBBit,
        RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm) x
  simpa only [sCoeffValueWord, sCoeffValueBit_get] using h

/-- Odd branch-code staging preserves the complete compact `r` word. -/
theorem oddBranchCodeToScratchStep_core_rCoeff
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (oddBranchCodeToScratchStep n counterWidth x).core.rCoeff =
      x.core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := oddBranchCodeToScratchStep_get_of_targets_ne
    n counterWidth ((rCoeffValueWord n counterWidth).bit bit)
    (by
      simpa [rCoeffValueWord, rCoeffValueBit, scratchABit,
        RegisterBits.rCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [rCoeffValueWord, rCoeffValueBit, scratchBBit,
        RegisterBits.rCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm) x
  simpa only [rCoeffValueWord, rCoeffValueBit_get] using h

/-- Literal odd branch-code staging, sole-history write, and compact shift
dispatch. -/
def oddBranchCodeThenHistoryThenShiftGates
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  oddBranchCodeToScratchGates n counterWidth ++
    [activeScratchBToHistoryGate n counterWidth historyIndex] ++
      auxActiveShiftDispatchGates n counterWidth

def oddBranchCodeThenHistoryThenShiftStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x => auxActiveShiftDispatchStep n counterWidth
    (activeScratchBToHistoryStep n counterWidth historyIndex
      (oddBranchCodeToScratchStep n counterWidth x))

def oddBranchCodeThenHistoryThenShiftProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (oddBranchCodeThenHistoryThenShiftGates n counterWidth historyIndex)

theorem oddBranchCodeThenHistoryThenShift_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (oddBranchCodeThenHistoryThenShiftProgram n counterWidth historyIndex)
      (oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (oddBranchCodeThenHistoryThenShiftGates n counterWidth historyIndex) (by
      intro x
      unfold oddBranchCodeThenHistoryThenShiftGates
        oddBranchCodeThenHistoryThenShiftStep
        oddBranchCodeToScratchStep activeScratchBToHistoryStep
      repeat rw [EncodedBit.GateSpec.stepList_append]
      rw [auxActiveShiftDispatchStep_eq_gateList]
      rfl)

theorem oddBranchCodeThenHistoryThenShiftGates_length
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    (oddBranchCodeThenHistoryThenShiftGates
      n counterWidth historyIndex).length = 18 * n - 6 := by
  simp only [oddBranchCodeThenHistoryThenShiftGates, List.length_append,
    List.length_cons, List.length_nil, oddBranchCodeToScratchGates_length,
    auxActiveShiftDispatchGates_length]
  have hpositive : 0 < n := by
    have hlt := historyIndex.isLt
    omega
  omega

theorem oddBranchCodeThenHistoryThenShiftGates_xMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((oddBranchCodeThenHistoryThenShiftGates n counterWidth historyIndex).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simp only [oddBranchCodeThenHistoryThenShiftGates, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    oddBranchCodeToScratchGates_xMultiplicity_sum,
    activeScratchBToHistoryGate_xMultiplicity,
    auxActiveShiftDispatchGates_xMultiplicity_sum]
  rfl

theorem oddBranchCodeThenHistoryThenShiftGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((oddBranchCodeThenHistoryThenShiftGates n counterWidth historyIndex).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [oddBranchCodeThenHistoryThenShiftGates, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    oddBranchCodeToScratchGates_cnotMultiplicity_sum,
    activeScratchBToHistoryGate_cnotMultiplicity,
    auxActiveShiftDispatchGates_cnotMultiplicity_sum]
  rfl

theorem oddBranchCodeThenHistoryThenShiftGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((oddBranchCodeThenHistoryThenShiftGates n counterWidth historyIndex).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 18 * n - 6 := by
  simp only [oddBranchCodeThenHistoryThenShiftGates, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    oddBranchCodeToScratchGates_toffoliMultiplicity_sum,
    activeScratchBToHistoryGate_toffoliMultiplicity,
    auxActiveShiftDispatchGates_toffoliMultiplicity_sum]
  have hpositive : 0 < n := by
    have hlt := historyIndex.isLt
    omega
  omega

theorem oddBranchCodeThenHistoryThenShiftStep_get_active
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex x) =
      (activeBit n counterWidth).get x := by
  unfold oddBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_active,
    activeScratchBToHistoryStep_get_active,
    oddBranchCodeToScratchStep_get_active]

theorem oddBranchCodeThenHistoryThenShiftStep_get_path
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (pathBit n counterWidth).get
        (oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex x) =
      (pathBit n counterWidth).get x := by
  unfold oddBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth (pathBit n counterWidth)]
  · rw [activeScratchBToHistoryStep_get_of_target_ne
      n counterWidth historyIndex (pathBit n counterWidth)]
    · exact oddBranchCodeToScratchStep_get_of_targets_ne
        n counterWidth (pathBit n counterWidth)
        (by
          simpa [scratchABit, pathBit] using
            liftCoreBit_liftSharedBit_wire_ne n counterWidth
              (RegisterBits.scratchABit n counterWidth)
              (sharedPathBit n counterWidth))
        (by
          simpa [scratchBBit, pathBit] using
            liftCoreBit_liftSharedBit_wire_ne n counterWidth
              (RegisterBits.scratchBBit n counterWidth)
              (sharedPathBit n counterWidth)) x
    · simpa [historyBit, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.historyBit n counterWidth historyIndex)
          (sharedPathBit n counterWidth)
  · intro bit
    simpa [uValueWord, pathBit, RegisterBits.uValueBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.uValueBit n counterWidth bit)
        (sharedPathBit n counterWidth)
  · intro bit
    simpa [sCoeffValueWord, sCoeffValueBit, pathBit,
      RegisterBits.sCoeffValueBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.sCoeffValueBit n counterWidth bit)
        (sharedPathBit n counterWidth)
  · intro bit
    simpa [vValueWord, pathBit, RegisterBits.vValueBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth bit)
        (sharedPathBit n counterWidth)
  · intro bit
    simpa [rCoeffValueWord, rCoeffValueBit, pathBit,
      RegisterBits.rCoeffValueBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.rCoeffValueBit n counterWidth bit)
        (sharedPathBit n counterWidth)

theorem oddBranchCodeThenHistoryThenShiftStep_get_compare
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex x) =
      (compareBit n counterWidth).get x := by
  unfold oddBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_compare,
    activeScratchBToHistoryStep_get_compare,
    oddBranchCodeToScratchStep_get_compare]

theorem oddBranchCodeThenHistoryThenShiftStep_get_scratchA
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get
        (oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex x) =
      ((scratchABit n counterWidth).get x ^^
        ((activeBit n counterWidth).get x &&
          (compareBit n counterWidth).get x)) := by
  unfold oddBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_scratchA,
    activeScratchBToHistoryStep_get_scratchA,
    oddBranchCodeToScratchStep_get_scratchA]

theorem oddBranchCodeThenHistoryThenShiftStep_get_scratchB
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (scratchBBit n counterWidth).get
        (oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex x) =
      ((scratchBBit n counterWidth).get x ^^
        ((activeBit n counterWidth).get x &&
          (compareBit n counterWidth).get x)) := by
  unfold oddBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_scratchB,
    activeScratchBToHistoryStep_get_scratchB,
    oddBranchCodeToScratchStep_get_scratchB]

theorem oddBranchCodeThenHistoryThenShiftStep_get_history
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (historyBit n counterWidth historyIndex).get
        (oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex x) =
      ((historyBit n counterWidth historyIndex).get x ^^
        ((activeBit n counterWidth).get x &&
          ((scratchBBit n counterWidth).get x ^^
            ((activeBit n counterWidth).get x &&
              (compareBit n counterWidth).get x)))) := by
  unfold oddBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_historyBit,
    activeScratchBToHistoryStep_get_historyBit,
    oddBranchCodeToScratchStep_get_of_targets_ne n counterWidth
      (historyBit n counterWidth historyIndex)
      (scratchABit_historyBit_wire_ne n counterWidth historyIndex)
      (scratchBBit_historyBit_wire_ne n counterWidth historyIndex),
    oddBranchCodeToScratchStep_get_active,
    oddBranchCodeToScratchStep_get_scratchB]

theorem oddBranchCodeThenHistoryThenShiftStep_get_work
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (work : Fin n) (x : Registers n counterWidth) :
    (coefficientCarryWorkBit n counterWidth work).get
        (oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex x) =
      (coefficientCarryWorkBit n counterWidth work).get x := by
  unfold oddBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_coefficientCarryWorkBit,
    activeScratchBToHistoryStep_get_of_target_ne n counterWidth historyIndex
      (coefficientCarryWorkBit n counterWidth work)
      (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.historyBit n counterWidth historyIndex) work),
    oddBranchCodeToScratchStep_get_of_targets_ne n counterWidth
      (coefficientCarryWorkBit n counterWidth work)
      (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) work)
      (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth) work)]

theorem oddBranchCodeThenHistoryThenShiftStep_get_carryIn
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (coefficientCarryInBit n counterWidth).get
        (oddBranchCodeThenHistoryThenShiftStep
          n counterWidth historyIndex x) =
      (coefficientCarryInBit n counterWidth).get x := by
  unfold oddBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_coefficientCarryInBit,
    activeScratchBToHistoryStep_get_of_target_ne n counterWidth historyIndex
      (coefficientCarryInBit n counterWidth)
      (liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
        (RegisterBits.historyBit n counterWidth historyIndex)),
    oddBranchCodeToScratchStep_get_of_targets_ne n counterWidth
      (coefficientCarryInBit n counterWidth)
      (liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth))
      (liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth))]

/-- Odd branch-code staging, history writing, and the selected shift preserve
an already clean VBE carry bank. -/
theorem oddBranchCodeThenHistoryThenShiftStep_coefficientAdder_cleanEndpoint
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (oddBranchCodeThenHistoryThenShiftStep
      n counterWidth historyIndex x).shared.coefficientAdder =
        cleanCoeffAdderWork n := by
  apply Prod.ext
  · change (coefficientCarryInBit n counterWidth).get
        (oddBranchCodeThenHistoryThenShiftStep
          n counterWidth historyIndex x) = false
    rw [oddBranchCodeThenHistoryThenShiftStep_get_carryIn, hcarry]
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    change (coefficientCarryWorkBit n counterWidth bit).get
        (oddBranchCodeThenHistoryThenShiftStep
          n counterWidth historyIndex x) = false
    rw [oddBranchCodeThenHistoryThenShiftStep_get_work, hwork bit]

/-- Odd branch-code staging, its single history write, and the selected shift
preserve every observation outside the two code targets, selected history
target, and four shifted data words. -/
theorem oddBranchCodeThenHistoryThenShiftStep_get_of_preserved
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (observed : EncodedBit (encoding n counterWidth))
    (hscratchA : (scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB : (scratchBBit n counterWidth).wire ≠ observed.wire)
    (hhistory : (historyBit n counterWidth historyIndex).wire ≠
      observed.wire)
    (hu : ∀ bit, ((uValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hs : ∀ bit,
      ((sCoeffValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hv : ∀ bit, ((vValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hr : ∀ bit,
      ((rCoeffValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (oddBranchCodeThenHistoryThenShiftStep
        n counterWidth historyIndex x) = observed.get x := by
  unfold oddBranchCodeThenHistoryThenShiftStep
  rw [auxActiveShiftDispatchStep_get_observed_of_words_ne
    n counterWidth observed hu hs hv hr]
  rw [activeScratchBToHistoryStep_get_of_target_ne
    n counterWidth historyIndex observed hhistory]
  exact oddBranchCodeToScratchStep_get_of_targets_ne
    n counterWidth observed hscratchA hscratchB x

/-- A true retained comparison chooses the physical `uGreater` shift group. -/
theorem oddBranchCodeThenHistoryThenShiftStep_eq_uShift
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hscratchA : (scratchABit n counterWidth).get x = false) :
    oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex x =
      uDiv2ThenSMul2Step n counterWidth
        (activeScratchBToHistoryStep n counterWidth historyIndex
          (oddBranchCodeToScratchStep n counterWidth x)) := by
  let staged := oddBranchCodeToScratchStep n counterWidth x
  let written := activeScratchBToHistoryStep n counterWidth historyIndex staged
  have hactiveWritten : (activeBit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [activeScratchBToHistoryStep_get_active,
      oddBranchCodeToScratchStep_get_active, hactive]
  have hauxWritten : (scratchABit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [activeScratchBToHistoryStep_get_scratchA,
      oddBranchCodeToScratchStep_get_scratchA, hscratchA, hactive, hcompare]
    rfl
  exact auxActiveShiftDispatchStep_eq_uDiv2ThenSMul2Step
    n counterWidth written hactiveWritten hauxWritten

/-- A false retained comparison chooses the physical `vLe` shift group. -/
theorem oddBranchCodeThenHistoryThenShiftStep_eq_vShift
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false) :
    oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex x =
      vDiv2ThenRMul2Step n counterWidth
        (activeScratchBToHistoryStep n counterWidth historyIndex
          (oddBranchCodeToScratchStep n counterWidth x)) := by
  let staged := oddBranchCodeToScratchStep n counterWidth x
  let written := activeScratchBToHistoryStep n counterWidth historyIndex staged
  have hactiveWritten : (activeBit n counterWidth).get written = true := by
    dsimp [written, staged]
    rw [activeScratchBToHistoryStep_get_active,
      oddBranchCodeToScratchStep_get_active, hactive]
  have hauxWritten : (scratchABit n counterWidth).get written = false := by
    dsimp [written, staged]
    rw [activeScratchBToHistoryStep_get_scratchA,
      oddBranchCodeToScratchStep_get_scratchA, hscratchA, hactive, hcompare]
    rfl
  exact auxActiveShiftDispatchStep_eq_vDiv2ThenRMul2Step
    n counterWidth written hactiveWritten hauxWritten

/-! ### Compact selected odd arithmetic followed by carried routing -/

/-- The complete compact odd-branch slice first performs the compare-selected
source/coefficient arithmetic, then consumes the retained comparison bit to
stage history and select the physical shift group. -/
def selectedOddDataThenBranchHistoryShiftGates
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  compareSelectedOddDataPathGates n counterWidth ++
    oddBranchCodeThenHistoryThenShiftGates n counterWidth historyIndex

def selectedOddDataThenBranchHistoryShiftStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    Registers n counterWidth → Registers n counterWidth :=
  fun x => oddBranchCodeThenHistoryThenShiftStep n counterWidth historyIndex
    (compareSelectedOddDataPathStep n counterWidth x)

def selectedOddDataThenBranchHistoryShiftProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (selectedOddDataThenBranchHistoryShiftGates
      n counterWidth historyIndex)

theorem selectedOddDataThenBranchHistoryShift_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (selectedOddDataThenBranchHistoryShiftProgram
        n counterWidth historyIndex)
      (selectedOddDataThenBranchHistoryShiftStep
        n counterWidth historyIndex) :=
  EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty
    (selectedOddDataThenBranchHistoryShiftGates
      n counterWidth historyIndex) (by
        intro x
        unfold selectedOddDataThenBranchHistoryShiftGates
          selectedOddDataThenBranchHistoryShiftStep
        rw [EncodedBit.GateSpec.stepList_append,
          compareSelectedOddDataPathStep_eq_gateList]
        unfold oddBranchCodeThenHistoryThenShiftGates
          oddBranchCodeThenHistoryThenShiftStep
          oddBranchCodeToScratchStep activeScratchBToHistoryStep
        repeat rw [EncodedBit.GateSpec.stepList_append]
        rw [auxActiveShiftDispatchStep_eq_gateList]
        rfl)

/-- The complete selected odd arithmetic/history/shift route restores the
same VBE carry bank after the subtraction and addition reuse it in sequence. -/
theorem selectedOddDataThenBranchHistoryShiftStep_coefficientAdder_cleanEndpoint
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hcarry : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit n counterWidth bit).get x = false) :
    (selectedOddDataThenBranchHistoryShiftStep
      n counterWidth historyIndex x).shared.coefficientAdder =
        cleanCoeffAdderWork n := by
  let arithmetic := compareSelectedOddDataPathStep n counterWidth x
  have hbank : arithmetic.shared.coefficientAdder = cleanCoeffAdderWork n :=
    compareSelectedOddDataPathStep_coefficientAdder_cleanEndpoint
      n counterWidth x hscratchA hscratchB hcarry hwork
  have hcarryArithmetic :
      (coefficientCarryInBit n counterWidth).get arithmetic = false := by
    rw [coefficientCarryInBit_get, hbank]
    rfl
  have hworkArithmetic : ∀ bit,
      (coefficientCarryWorkBit n counterWidth bit).get arithmetic = false := by
    intro bit
    change (BinaryLabelEncoding.finIdentityBit n bit).get
      arithmetic.shared.coefficientAdder.2 = false
    rw [hbank]
    exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n bit
  exact oddBranchCodeThenHistoryThenShiftStep_coefficientAdder_cleanEndpoint
    n counterWidth historyIndex arithmetic hcarryArithmetic hworkArithmetic

/-- The selected odd arithmetic/history/shift route preserves every
observation outside the arithmetic words, VBE work bank, branch-code targets,
and selected history target. -/
theorem selectedOddDataThenBranchHistoryShiftStep_get_of_preserved
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (observed : EncodedBit (encoding n counterWidth))
    (hu : ∀ bit, ((uValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hv : ∀ bit, ((vValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hr : ∀ bit,
      (rCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (hs : ∀ bit,
      (sCoeffValueBit n counterWidth bit).wire ≠ observed.wire)
    (hwork : ∀ bit,
      (coefficientCarryWorkBit n counterWidth bit).wire ≠ observed.wire)
    (hscratchA : (scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB : (scratchBBit n counterWidth).wire ≠ observed.wire)
    (hhistory : (historyBit n counterWidth historyIndex).wire ≠
      observed.wire)
    (x : Registers n counterWidth)
    (hscratchAValue : (scratchABit n counterWidth).get x = false)
    (hscratchBValue : (scratchBBit n counterWidth).get x = false) :
    observed.get (selectedOddDataThenBranchHistoryShiftStep
        n counterWidth historyIndex x) = observed.get x := by
  unfold selectedOddDataThenBranchHistoryShiftStep
  rw [oddBranchCodeThenHistoryThenShiftStep_get_of_preserved
    n counterWidth historyIndex observed hscratchA hscratchB hhistory
    hu (by simpa only [sCoeffValueWord] using hs) hv
    (by simpa only [rCoeffValueWord] using hr)]
  exact compareSelectedOddDataPathStep_get_observed_of_words_work_ne
    n counterWidth observed hu hv hr hs hwork x
      hscratchAValue hscratchBValue

theorem selectedOddDataThenBranchHistoryShiftGates_length
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    (selectedOddDataThenBranchHistoryShiftGates
      n counterWidth historyIndex).length =
        36 * (n - 1) + 62 * n + 2 := by
  rw [selectedOddDataThenBranchHistoryShiftGates, List.length_append,
    compareSelectedOddDataPathGates_length,
    oddBranchCodeThenHistoryThenShiftGates_length]
  have hpositive : 0 < n := by
    have hlt := historyIndex.isLt
    omega
  omega

theorem selectedOddDataThenBranchHistoryShiftGates_xMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((selectedOddDataThenBranchHistoryShiftGates
      n counterWidth historyIndex).map
        EncodedBit.GateSpec.xMultiplicity).sum = 4 := by
  simp only [selectedOddDataThenBranchHistoryShiftGates, List.map_append,
    List.sum_append, compareSelectedOddDataPathGates_xMultiplicity_sum,
    oddBranchCodeThenHistoryThenShiftGates_xMultiplicity_sum]

theorem selectedOddDataThenBranchHistoryShiftGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((selectedOddDataThenBranchHistoryShiftGates
      n counterWidth historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp only [selectedOddDataThenBranchHistoryShiftGates, List.map_append,
    List.sum_append, compareSelectedOddDataPathGates_cnotMultiplicity_sum,
    oddBranchCodeThenHistoryThenShiftGates_cnotMultiplicity_sum]

theorem selectedOddDataThenBranchHistoryShiftGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((selectedOddDataThenBranchHistoryShiftGates
      n counterWidth historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          36 * (n - 1) + 62 * n - 2 := by
  rw [selectedOddDataThenBranchHistoryShiftGates, List.map_append,
    List.sum_append,
    compareSelectedOddDataPathGates_toffoliMultiplicity_sum,
    oddBranchCodeThenHistoryThenShiftGates_toffoliMultiplicity_sum]
  have hpositive : 0 < n := by
    have hlt := historyIndex.isLt
    omega
  omega

/-! ### Branch-code path cleanup -/

/-- Three native gates erase the retained active-odd route bit from the final
two-bit branch code.  For active branches, oddness is exactly equality of the
two code bits; inactive states contribute no toggle. -/
def branchCodePathCleanupGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  [ EncodedBit.GateSpec.cnot
      (activeBit n counterWidth) (pathBit n counterWidth)
      (by
        simpa [activeBit, pathBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.activeBit n counterWidth)
            (sharedPathBit n counterWidth))
  , EncodedBit.GateSpec.toffoli
      (activeBit n counterWidth) (scratchABit n counterWidth)
      (pathBit n counterWidth)
      (activeBit_scratchABit_wire_ne n counterWidth)
      (by
        simpa [activeBit, pathBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.activeBit n counterWidth)
            (sharedPathBit n counterWidth))
      (by
        simpa [scratchABit, pathBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchABit n counterWidth)
            (sharedPathBit n counterWidth))
  , EncodedBit.GateSpec.toffoli
      (activeBit n counterWidth) (scratchBBit n counterWidth)
      (pathBit n counterWidth)
      (activeBit_scratchBBit_wire_ne n counterWidth)
      (by
        simpa [activeBit, pathBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.activeBit n counterWidth)
            (sharedPathBit n counterWidth))
      (by
        simpa [scratchBBit, pathBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchBBit n counterWidth)
            (sharedPathBit n counterWidth)) ]

/-- Branch-path cleanup is disjoint from every public target bit. -/
theorem branchCodePathCleanupGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ branchCodePathCleanupGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  simp only [branchCodePathCleanupGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth) targetIndex,
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedPathBit n counterWidth) targetIndex⟩
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) targetIndex,
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedPathBit n counterWidth) targetIndex⟩
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth) targetIndex,
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedPathBit n counterWidth) targetIndex⟩

def branchCodePathCleanupStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (branchCodePathCleanupGates n counterWidth)

def branchCodePathCleanupProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (branchCodePathCleanupGates n counterWidth)

theorem branchCodePathCleanup_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (branchCodePathCleanupProgram n counterWidth)
      (branchCodePathCleanupStep n counterWidth) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (branchCodePathCleanupGates n counterWidth)

@[simp] theorem branchCodePathCleanupGates_length (n counterWidth : Nat) :
    (branchCodePathCleanupGates n counterWidth).length = 3 := by
  rfl

@[simp] theorem branchCodePathCleanupGates_xMultiplicity_sum
    (n counterWidth : Nat) :
    ((branchCodePathCleanupGates n counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  rfl

@[simp] theorem branchCodePathCleanupGates_cnotMultiplicity_sum
    (n counterWidth : Nat) :
    ((branchCodePathCleanupGates n counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  rfl

@[simp] theorem branchCodePathCleanupGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) :
    ((branchCodePathCleanupGates n counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 := by
  rfl

structure BranchCodePathCertificate
    (n counterWidth : Nat) (x : Registers n counterWidth) : Prop where
  path : (pathBit n counterWidth).get x =
    ((activeBit n counterWidth).get x &&
      !((scratchABit n counterWidth).get x ^^
        (scratchBBit n counterWidth).get x))

theorem branchCodePathCleanupStep_get_path
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (pathBit n counterWidth).get
        (branchCodePathCleanupStep n counterWidth x) =
      ((((pathBit n counterWidth).get x ^^
          (activeBit n counterWidth).get x) ^^
        ((activeBit n counterWidth).get x &&
          (scratchABit n counterWidth).get x)) ^^
        ((activeBit n counterWidth).get x &&
          (scratchBBit n counterWidth).get x)) := by
  unfold branchCodePathCleanupStep branchCodePathCleanupGates
  change (pathBit n counterWidth).get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (scratchBBit n counterWidth) (pathBit n counterWidth)
        (EncodedBit.toffoliStep (activeBit n counterWidth)
          (scratchABit n counterWidth) (pathBit n counterWidth)
          (EncodedBit.cnotStep (activeBit n counterWidth)
            (pathBit n counterWidth) x))) = _
  have hpathActive : (pathBit n counterWidth).wire ≠
      (activeBit n counterWidth).wire := by
    simpa [activeBit, pathBit] using
      (liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (sharedPathBit n counterWidth)).symm
  have hpathScratchA : (pathBit n counterWidth).wire ≠
      (scratchABit n counterWidth).wire := by
    simpa [scratchABit, pathBit] using
      (liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth)
        (sharedPathBit n counterWidth)).symm
  have hpathScratchB : (pathBit n counterWidth).wire ≠
      (scratchBBit n counterWidth).wire := by
    simpa [scratchBBit, pathBit] using
      (liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth)
        (sharedPathBit n counterWidth)).symm
  rw [EncodedBit.toffoliStep_get_target]
  rw [EncodedBit.toffoliStep_get_of_target_ne _ _ _
      (activeBit n counterWidth) hpathActive,
    EncodedBit.cnotStep_get_of_target_ne _ _ (activeBit n counterWidth)
      hpathActive,
    EncodedBit.toffoliStep_get_of_target_ne _ _ _
      (scratchBBit n counterWidth) hpathScratchB,
    EncodedBit.cnotStep_get_of_target_ne _ _ (scratchBBit n counterWidth)
      hpathScratchB,
    EncodedBit.toffoliStep_get_target,
    EncodedBit.cnotStep_get_of_target_ne _ _ (activeBit n counterWidth)
      hpathActive,
    EncodedBit.cnotStep_get_of_target_ne _ _ (scratchABit n counterWidth)
      hpathScratchA,
    EncodedBit.cnotStep_get_target]

theorem branchCodePathCleanupStep_get_path_clean
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (cert : BranchCodePathCertificate n counterWidth x) :
    (pathBit n counterWidth).get
        (branchCodePathCleanupStep n counterWidth x) = false := by
  rw [branchCodePathCleanupStep_get_path, cert.path]
  cases (activeBit n counterWidth).get x <;>
    cases (scratchABit n counterWidth).get x <;>
      cases (scratchBBit n counterWidth).get x <;> rfl

theorem branchCodePathCleanupStep_get_of_path_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hne : (pathBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (branchCodePathCleanupStep n counterWidth x) =
      observed.get x := by
  unfold branchCodePathCleanupStep branchCodePathCleanupGates
  change observed.get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (scratchBBit n counterWidth) (pathBit n counterWidth)
        (EncodedBit.toffoliStep (activeBit n counterWidth)
          (scratchABit n counterWidth) (pathBit n counterWidth)
          (EncodedBit.cnotStep (activeBit n counterWidth)
            (pathBit n counterWidth) x))) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne _ _ _ observed hne,
    EncodedBit.toffoliStep_get_of_target_ne _ _ _ observed hne,
    EncodedBit.cnotStep_get_of_target_ne _ _ observed hne]

/-! ### Compact three-gate residue cleanup -/

/-- Low bit of the `r` coefficient used to erase the redundant auxiliary
branch-code bit. -/
def rCoeffLowBit (n counterWidth : Nat) :
    EncodedBit (encoding n counterWidth) :=
  rCoeffValueBit n counterWidth ⟨0, Nat.succ_pos n⟩

private theorem activeBit_rCoeffLowBit_wire_ne
    (n counterWidth : Nat) :
    (activeBit n counterWidth).wire ≠
      (rCoeffLowBit n counterWidth).wire := by
  simpa [activeBit, rCoeffLowBit, rCoeffValueBit,
    RegisterBits.rCoeffValueBit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.active_rCoeff_wire_ne n counterWidth
        (WireAddress.littleEndianWire ⟨0, Nat.succ_pos n⟩))

private theorem rCoeffLowBit_scratchABit_wire_ne
    (n counterWidth : Nat) :
    (rCoeffLowBit n counterWidth).wire ≠
      (scratchABit n counterWidth).wire := by
  simpa [rCoeffLowBit, rCoeffValueBit, RegisterBits.rCoeffValueBit,
    scratchABit] using
    liftCoreBit_wire_ne n counterWidth
      (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire ⟨0, Nat.succ_pos n⟩))

/-- Once the compact counter carry is no longer duplicated into round routing,
the physical branch residue is erased by exactly three gates. -/
def branchResidueCleanupGates
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  [ EncodedBit.GateSpec.toffoli
      (scratchABit n counterWidth) (scratchBBit n counterWidth)
      (compareBit n counterWidth)
      (scratchABit_scratchBBit_wire_ne n counterWidth)
      (compareBit_scratchABit_wire_ne n counterWidth).symm
      (compareBit_scratchBBit_wire_ne n counterWidth).symm
  , EncodedBit.GateSpec.cnot
      (historyBit n counterWidth historyIndex)
      (scratchBBit n counterWidth)
      (scratchBBit_historyBit_wire_ne n counterWidth historyIndex).symm
  , EncodedBit.GateSpec.toffoli
      (activeBit n counterWidth) (rCoeffLowBit n counterWidth)
      (scratchABit n counterWidth)
      (activeBit_rCoeffLowBit_wire_ne n counterWidth)
      (activeBit_scratchABit_wire_ne n counterWidth)
      (rCoeffLowBit_scratchABit_wire_ne n counterWidth) ]

/-- Branch-residue cleanup is disjoint from every public target bit. -/
theorem branchResidueCleanupGates_bitDisjoint_target
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (targetIndex : Fin n) :
    ∀ gate,
      gate ∈ branchResidueCleanupGates n counterWidth historyIndex →
        EncodedBit.GateSpec.bitDisjoint
          (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  simp only [branchResidueCleanupGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth) targetIndex⟩
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.historyBit n counterWidth historyIndex) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth) targetIndex⟩
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.rCoeffValueBit n counterWidth
          ⟨0, Nat.succ_pos n⟩) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth) targetIndex⟩

def branchResidueCleanupStep
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (branchResidueCleanupGates n counterWidth historyIndex)

def branchResidueCleanupProgram
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (branchResidueCleanupGates n counterWidth historyIndex)

theorem branchResidueCleanup_realizes
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (branchResidueCleanupProgram n counterWidth historyIndex)
      (branchResidueCleanupStep n counterWidth historyIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (branchResidueCleanupGates n counterWidth historyIndex)

@[simp] theorem branchResidueCleanupGates_length
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    (branchResidueCleanupGates n counterWidth historyIndex).length = 3 := by
  rfl

@[simp] theorem branchResidueCleanupGates_xMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((branchResidueCleanupGates n counterWidth historyIndex).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  rfl

@[simp] theorem branchResidueCleanupGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((branchResidueCleanupGates n counterWidth historyIndex).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  rfl

@[simp] theorem branchResidueCleanupGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) :
    ((branchResidueCleanupGates n counterWidth historyIndex).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 := by
  rfl

structure BranchResidueCertificate
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) : Prop where
  compare :
    (compareBit n counterWidth).get x =
      ((scratchABit n counterWidth).get x &&
        (scratchBBit n counterWidth).get x)
  history :
    (scratchBBit n counterWidth).get x =
      (historyBit n counterWidth historyIndex).get x
  auxiliary :
    (scratchABit n counterWidth).get x =
      ((activeBit n counterWidth).get x &&
        (rCoeffLowBit n counterWidth).get x)

structure BranchResidueCleanEndpoint
    (n counterWidth : Nat) (x : Registers n counterWidth) : Prop where
  compare : (compareBit n counterWidth).get x = false
  scratchA : (scratchABit n counterWidth).get x = false
  scratchB : (scratchBBit n counterWidth).get x = false

theorem branchResidueCertificate_uEven
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = true)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hhistory : (historyBit n counterWidth historyIndex).get x = false)
    (hrLow : (rCoeffLowBit n counterWidth).get x = true) :
    BranchResidueCertificate n counterWidth historyIndex x := by
  constructor
  · rw [hcompare, hscratchA, hscratchB]
    rfl
  · rw [hscratchB, hhistory]
  · rw [hscratchA, hactive, hrLow]
    rfl

theorem branchResidueCertificate_vEven
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = true)
    (hhistory : (historyBit n counterWidth historyIndex).get x = true)
    (hrLow : (rCoeffLowBit n counterWidth).get x = false) :
    BranchResidueCertificate n counterWidth historyIndex x := by
  constructor
  · rw [hcompare, hscratchA, hscratchB]
    rfl
  · rw [hscratchB, hhistory]
  · rw [hscratchA, hactive, hrLow]
    rfl

theorem branchResidueCertificate_uGreater
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (hcompare : (compareBit n counterWidth).get x = true)
    (hscratchA : (scratchABit n counterWidth).get x = true)
    (hscratchB : (scratchBBit n counterWidth).get x = true)
    (hhistory : (historyBit n counterWidth historyIndex).get x = true)
    (hrLow : (rCoeffLowBit n counterWidth).get x = true) :
    BranchResidueCertificate n counterWidth historyIndex x := by
  constructor
  · rw [hcompare, hscratchA, hscratchB]
    rfl
  · rw [hscratchB, hhistory]
  · rw [hscratchA, hactive, hrLow]
    rfl

theorem branchResidueCertificate_vLe
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hhistory : (historyBit n counterWidth historyIndex).get x = false)
    (hrLow : (rCoeffLowBit n counterWidth).get x = false) :
    BranchResidueCertificate n counterWidth historyIndex x := by
  constructor
  · rw [hcompare, hscratchA, hscratchB]
    rfl
  · rw [hscratchB, hhistory]
  · rw [hscratchA, hactive, hrLow]
    rfl

theorem branchResidueCleanupStep_get_compare
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (branchResidueCleanupStep n counterWidth historyIndex x) =
      ((compareBit n counterWidth).get x ^^
        ((scratchABit n counterWidth).get x &&
          (scratchBBit n counterWidth).get x)) := by
  unfold branchResidueCleanupStep branchResidueCleanupGates
  change (compareBit n counterWidth).get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (rCoeffLowBit n counterWidth) (scratchABit n counterWidth)
        (EncodedBit.cnotStep (historyBit n counterWidth historyIndex)
          (scratchBBit n counterWidth)
          (EncodedBit.toffoliStep (scratchABit n counterWidth)
            (scratchBBit n counterWidth) (compareBit n counterWidth) x))) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
      (compareBit_scratchABit_wire_ne n counterWidth).symm,
    EncodedBit.cnotStep_get_of_target_ne _ _ _
      (compareBit_scratchBBit_wire_ne n counterWidth).symm,
    EncodedBit.toffoliStep_get_target]

theorem branchResidueCleanupStep_get_scratchB
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (scratchBBit n counterWidth).get
        (branchResidueCleanupStep n counterWidth historyIndex x) =
      ((scratchBBit n counterWidth).get x ^^
        (historyBit n counterWidth historyIndex).get x) := by
  unfold branchResidueCleanupStep branchResidueCleanupGates
  change (scratchBBit n counterWidth).get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (rCoeffLowBit n counterWidth) (scratchABit n counterWidth)
        (EncodedBit.cnotStep (historyBit n counterWidth historyIndex)
          (scratchBBit n counterWidth)
          (EncodedBit.toffoliStep (scratchABit n counterWidth)
            (scratchBBit n counterWidth) (compareBit n counterWidth) x))) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
      (scratchABit_scratchBBit_wire_ne n counterWidth),
    EncodedBit.cnotStep_get_target,
    EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
      (compareBit_scratchBBit_wire_ne n counterWidth),
    EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
      (compareBit_historyBit_wire_ne n counterWidth historyIndex)]

theorem branchResidueCleanupStep_get_scratchA
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get
        (branchResidueCleanupStep n counterWidth historyIndex x) =
      ((scratchABit n counterWidth).get x ^^
        ((activeBit n counterWidth).get x &&
          (rCoeffLowBit n counterWidth).get x)) := by
  unfold branchResidueCleanupStep branchResidueCleanupGates
  change (scratchABit n counterWidth).get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (rCoeffLowBit n counterWidth) (scratchABit n counterWidth)
        (EncodedBit.cnotStep (historyBit n counterWidth historyIndex)
          (scratchBBit n counterWidth)
          (EncodedBit.toffoliStep (scratchABit n counterWidth)
            (scratchBBit n counterWidth) (compareBit n counterWidth) x))) = _
  rw [EncodedBit.toffoliStep_get_target,
    EncodedBit.cnotStep_get_of_target_ne _ _ _
      (scratchABit_scratchBBit_wire_ne n counterWidth).symm,
    EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
      (compareBit_scratchABit_wire_ne n counterWidth)]
  rw [EncodedBit.cnotStep_get_of_target_ne _ _ _
      (activeBit_scratchBBit_wire_ne n counterWidth).symm,
    EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
      (activeBit_compareBit_wire_ne n counterWidth).symm]
  rw [EncodedBit.cnotStep_get_of_target_ne _ _ _
      (by
        simpa [rCoeffLowBit, rCoeffValueBit, RegisterBits.rCoeffValueBit,
          scratchBBit] using
          (liftCoreBit_wire_ne n counterWidth
            (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire ⟨0, Nat.succ_pos n⟩))).symm),
    EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
      (by
        simpa [rCoeffLowBit, rCoeffValueBit, RegisterBits.rCoeffValueBit,
          compareBit] using
          liftCoreBit_wire_ne n counterWidth
            (RegisterBits.compare_rCoeff_wire_ne n counterWidth
              (WireAddress.littleEndianWire ⟨0, Nat.succ_pos n⟩)))]

/-- The compact residue cleanup preserves every observation outside its three
targets. -/
theorem branchResidueCleanupStep_get_of_targets_ne
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (observed : EncodedBit (encoding n counterWidth))
    (hcompare : (compareBit n counterWidth).wire ≠ observed.wire)
    (hscratchB : (scratchBBit n counterWidth).wire ≠ observed.wire)
    (hscratchA : (scratchABit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (branchResidueCleanupStep n counterWidth historyIndex x) =
      observed.get x := by
  unfold branchResidueCleanupStep branchResidueCleanupGates
  change observed.get
      (EncodedBit.toffoliStep (activeBit n counterWidth)
        (rCoeffLowBit n counterWidth) (scratchABit n counterWidth)
        (EncodedBit.cnotStep (historyBit n counterWidth historyIndex)
          (scratchBBit n counterWidth)
          (EncodedBit.toffoliStep (scratchABit n counterWidth)
            (scratchBBit n counterWidth) (compareBit n counterWidth) x))) = _
  rw [EncodedBit.toffoliStep_get_of_target_ne _ _ _ observed hscratchA,
    EncodedBit.cnotStep_get_of_target_ne _ _ observed hscratchB,
    EncodedBit.toffoliStep_get_of_target_ne _ _ _ observed hcompare]

theorem branchResidueCleanupStep_cleanEndpoint
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (certificate : BranchResidueCertificate n counterWidth historyIndex x) :
    BranchResidueCleanEndpoint n counterWidth
      (branchResidueCleanupStep n counterWidth historyIndex x) := by
  constructor
  · rw [branchResidueCleanupStep_get_compare, certificate.compare]
    cases (scratchABit n counterWidth).get x <;>
      cases (scratchBBit n counterWidth).get x <;> rfl
  · rw [branchResidueCleanupStep_get_scratchA, certificate.auxiliary]
    cases (activeBit n counterWidth).get x <;>
      cases (rCoeffLowBit n counterWidth).get x <;> rfl
  · rw [branchResidueCleanupStep_get_scratchB, certificate.history]
    cases (historyBit n counterWidth historyIndex).get x <;> rfl

/-- Path cleanup changes only the shared path bit, so a branch-residue
certificate remains valid for the following three-gate cleanup. -/
theorem branchCodePathCleanupStep_preserves_residueCertificate
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (certificate : BranchResidueCertificate n counterWidth historyIndex x) :
    BranchResidueCertificate n counterWidth historyIndex
      (branchCodePathCleanupStep n counterWidth x) := by
  have hcompare := branchCodePathCleanupStep_get_of_path_ne n counterWidth
    (compareBit n counterWidth)
    (by
      simpa [pathBit, compareBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedPathBit n counterWidth)).symm) x
  have hscratchA := branchCodePathCleanupStep_get_of_path_ne n counterWidth
    (scratchABit n counterWidth)
    (by
      simpa [pathBit, scratchABit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedPathBit n counterWidth)).symm) x
  have hscratchB := branchCodePathCleanupStep_get_of_path_ne n counterWidth
    (scratchBBit n counterWidth)
    (by
      simpa [pathBit, scratchBBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchBBit n counterWidth)
          (sharedPathBit n counterWidth)).symm) x
  have hhistory := branchCodePathCleanupStep_get_of_path_ne n counterWidth
    (historyBit n counterWidth historyIndex)
    (by
      simpa [pathBit, historyBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.historyBit n counterWidth historyIndex)
          (sharedPathBit n counterWidth)).symm) x
  have hactive := branchCodePathCleanupStep_get_of_path_ne n counterWidth
    (activeBit n counterWidth)
    (by
      simpa [pathBit, activeBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.activeBit n counterWidth)
          (sharedPathBit n counterWidth)).symm) x
  have hrLow := branchCodePathCleanupStep_get_of_path_ne n counterWidth
    (rCoeffLowBit n counterWidth)
    (by
      simpa [pathBit, rCoeffLowBit, rCoeffValueBit,
        RegisterBits.rCoeffValueBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.rCoeffValueBit n counterWidth
            (0 : Fin (n + 1))) (sharedPathBit n counterWidth)).symm) x
  constructor
  · rw [hcompare, hscratchA, hscratchB]
    exact certificate.compare
  · rw [hscratchB, hhistory]
    exact certificate.history
  · rw [hscratchA, hactive, hrLow]
    exact certificate.auxiliary

/-- Clean endpoint of the two compact route-cleanup suffixes. -/
structure RouteCleanupCleanEndpoint
    (n counterWidth : Nat) (x : Registers n counterWidth) : Prop where
  path : (pathBit n counterWidth).get x = false
  compare : (compareBit n counterWidth).get x = false
  scratchA : (scratchABit n counterWidth).get x = false
  scratchB : (scratchBBit n counterWidth).get x = false

/-- A certified route code is enough to erase both the shared path bit and all
three persistent branch residues. -/
theorem routeCleanup_cleanEndpoint
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (pathCertificate : BranchCodePathCertificate n counterWidth x)
    (residueCertificate :
      BranchResidueCertificate n counterWidth historyIndex x) :
    RouteCleanupCleanEndpoint n counterWidth
      (branchResidueCleanupStep n counterWidth historyIndex
        (branchCodePathCleanupStep n counterWidth x)) := by
  let pathCleaned := branchCodePathCleanupStep n counterWidth x
  have hpath : (pathBit n counterWidth).get pathCleaned = false :=
    branchCodePathCleanupStep_get_path_clean
      n counterWidth x pathCertificate
  have hresidue :
      BranchResidueCleanEndpoint n counterWidth
        (branchResidueCleanupStep n counterWidth historyIndex pathCleaned) :=
    branchResidueCleanupStep_cleanEndpoint n counterWidth historyIndex
      pathCleaned
      (branchCodePathCleanupStep_preserves_residueCertificate
        n counterWidth historyIndex x residueCertificate)
  refine
    { path := ?_
      compare := hresidue.compare
      scratchA := hresidue.scratchA
      scratchB := hresidue.scratchB }
  rw [branchResidueCleanupStep_get_of_targets_ne n counterWidth historyIndex
    (pathBit n counterWidth)]
  · exact hpath
  · simpa [pathBit, compareBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (sharedPathBit n counterWidth)
  · simpa [pathBit, scratchBBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.scratchBBit n counterWidth)
        (sharedPathBit n counterWidth)
  · simpa [pathBit, scratchABit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.scratchABit n counterWidth)
        (sharedPathBit n counterWidth)

/-! ### Complete compact active-branch body -/

/-- Semantic prefix ending after branch-code staging, the single history
write, and the selected paired shift, but before route cleanup. -/
def activeBranchRoutedStep
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    Registers n counterWidth -> Registers n counterWidth :=
  fun x =>
    auxActiveShiftDispatchStep n counterWidth
      (activeScratchBToHistoryStep n counterWidth historyIndex
        (oddBranchCodeToScratchStep n counterWidth
          (activeOddSelectedDataPathStep n counterWidth
            (selectedEvenBranchCodeToScratchStep n counterWidth low tempIndex
              (activeOddUGreaterSelectorStep
                n counterWidth low finalBit x)))))

/-- On an even selector result, the new scratch-reusing routed prefix is
extensionally the already-certified selected even route. -/
theorem activeBranchRoutedStep_eq_selected_even_route
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hselectedCompare :
      (compareBit n counterWidth).get
        (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = false)
    (hselectedPath :
      (pathBit n counterWidth).get
        (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = false)
    (hselectedControl :
      (controlBit n counterWidth).get
        (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = false)
    (hselectedScratchA :
      (scratchABit n counterWidth).get
        (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = false)
    (hselectedScratchB :
      (scratchBBit n counterWidth).get
        (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = false) :
    activeBranchRoutedStep
        n counterWidth low finalBit tempIndex historyIndex x =
      selectedBranchCodeThenHistoryThenShiftStep
        n counterWidth low tempIndex historyIndex
        (activeOddUGreaterSelectorStep n counterWidth low finalBit x) := by
  let selected := activeOddUGreaterSelectorStep
    n counterWidth low finalBit x
  let evenStaged := selectedEvenBranchCodeToScratchStep
    n counterWidth low tempIndex selected
  have hcompareEven :
      (compareBit n counterWidth).get evenStaged = false := by
    dsimp [evenStaged]
    rw [selectedEvenBranchCodeToScratchStep_get_of_preserved
      n counterWidth low tempIndex (compareBit n counterWidth)]
    · exact hselectedCompare
    · exact uLowBit_compareBit_wire_ne n counterWidth low
    · exact vLowBit_compareBit_wire_ne n counterWidth low
    · exact (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth) tempIndex).symm
    · exact (compareBit_scratchABit_wire_ne n counterWidth).symm
    · exact (compareBit_scratchBBit_wire_ne n counterWidth).symm
  have hpathEven : (pathBit n counterWidth).get evenStaged = false := by
    dsimp [evenStaged]
    rw [selectedEvenBranchCodeToScratchStep_get_of_preserved
      n counterWidth low tempIndex (pathBit n counterWidth)]
    · exact hselectedPath
    · simpa [uLowBit, uValueWord, pathBit, RegisterBits.uValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth low)
          (sharedPathBit n counterWidth)
    · simpa [vLowBit, vValueWord, pathBit, RegisterBits.vValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth low)
          (sharedPathBit n counterWidth)
    · exact (pathBit_coefficientCarryWorkBit_wire_ne
        n counterWidth tempIndex).symm
    · simpa [pathBit, scratchABit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedPathBit n counterWidth)
    · simpa [pathBit, scratchBBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchBBit n counterWidth)
          (sharedPathBit n counterWidth)
  have hcontrolEven :
      (controlBit n counterWidth).get evenStaged = false := by
    dsimp [evenStaged]
    rw [selectedEvenBranchCodeToScratchStep_get_of_preserved
      n counterWidth low tempIndex (controlBit n counterWidth)]
    · exact hselectedControl
    · simpa [uLowBit, uValueWord, controlBit, RegisterBits.uValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth low)
          (sharedControlBit n counterWidth)
    · simpa [vLowBit, vValueWord, controlBit, RegisterBits.vValueBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth low)
          (sharedControlBit n counterWidth)
    · exact (controlBit_coefficientCarryWorkBit_wire_ne
        n counterWidth tempIndex).symm
    · simpa [controlBit, scratchABit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedControlBit n counterWidth)
    · simpa [controlBit, scratchBBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchBBit n counterWidth)
          (sharedControlBit n counterWidth)
  have hdata :
      activeOddSelectedDataPathStep n counterWidth evenStaged = evenStaged :=
    activeOddSelectedDataPathStep_eq_self_of_path_false
      n counterWidth evenStaged hcompareEven hpathEven hcontrolEven
  have hodd : oddBranchCodeToScratchStep n counterWidth evenStaged =
      evenStaged :=
    oddBranchCodeToScratchStep_eq_self_of_compare_false
      n counterWidth evenStaged hcompareEven
  rw [activeBranchRoutedStep]
  change auxActiveShiftDispatchStep n counterWidth
      (activeScratchBToHistoryStep n counterWidth historyIndex
        (oddBranchCodeToScratchStep n counterWidth
          (activeOddSelectedDataPathStep n counterWidth evenStaged))) = _
  rw [hdata, hodd]
  unfold selectedBranchCodeThenHistoryThenShiftStep
  rw [selectedBranchCodeToScratchStep_eq_selectedEven_of_compare_false_clean
    n counterWidth low tempIndex selected hselectedCompare
    hselectedScratchA hselectedScratchB]

theorem activeBranchRoutedStep_eq_selected_even_route_of_pair_false
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (hpath : (pathBit n counterWidth).get x = false)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hpair :
      (((uValueWord n counterWidth).bit low).get x &&
        ((vValueWord n counterWidth).bit low).get x) = false) :
    activeBranchRoutedStep
        n counterWidth low finalBit tempIndex historyIndex x =
      selectedBranchCodeThenHistoryThenShiftStep
        n counterWidth low tempIndex historyIndex x := by
  have hselector :
      activeOddUGreaterSelectorStep n counterWidth low finalBit x = x :=
    activeOddUGreaterSelectorStep_eq_self_of_pair_false
      n counterWidth low finalBit x hactive hpath hcontrol hpair
  simpa [hselector] using
    activeBranchRoutedStep_eq_selected_even_route
      n counterWidth low finalBit tempIndex historyIndex x
      (by simpa [hselector] using hcompare)
      (by simpa [hselector] using hpath)
      (by simpa [hselector] using hcontrol)
      (by simpa [hselector] using hscratchA)
      (by simpa [hselector] using hscratchB)

/-- On an odd selector endpoint, even-code staging is the identity and the
masked arithmetic reduces exactly to the already-certified selected odd
route. -/
theorem activeBranchRoutedStep_eq_selected_odd_route
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hu : (uLowBit n counterWidth low).get
      (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = true)
    (hv : (vLowBit n counterWidth low).get
      (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = true)
    (hpath : (pathBit n counterWidth).get
      (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = true)
    (hcontrol : (controlBit n counterWidth).get
      (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = false)
    (hscratchA : (scratchABit n counterWidth).get
      (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = false)
    (hscratchB : (scratchBBit n counterWidth).get
      (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = false)
    (htemp : (coefficientCarryWorkBit n counterWidth tempIndex).get
      (activeOddUGreaterSelectorStep n counterWidth low finalBit x) = false) :
    activeBranchRoutedStep
        n counterWidth low finalBit tempIndex historyIndex x =
      selectedOddDataThenBranchHistoryShiftStep n counterWidth historyIndex
        (activeOddUGreaterSelectorStep n counterWidth low finalBit x) := by
  let selected := activeOddUGreaterSelectorStep
    n counterWidth low finalBit x
  have heven : selectedEvenBranchCodeToScratchStep
      n counterWidth low tempIndex selected = selected :=
    selectedEvenBranchCodeToScratchStep_eq_self_of_odd_pair_clean
      n counterWidth low tempIndex selected hu hv htemp
  have hdata : activeOddSelectedDataPathStep n counterWidth selected =
      compareSelectedOddDataPathStep n counterWidth selected :=
    activeOddSelectedDataPathStep_eq_compareSelected
      n counterWidth selected hpath hcontrol hscratchA hscratchB
  rw [activeBranchRoutedStep]
  change auxActiveShiftDispatchStep n counterWidth
      (activeScratchBToHistoryStep n counterWidth historyIndex
        (oddBranchCodeToScratchStep n counterWidth
          (activeOddSelectedDataPathStep n counterWidth
            (selectedEvenBranchCodeToScratchStep
              n counterWidth low tempIndex selected)))) = _
  rw [heven, hdata]
  rfl

/-- An inactive source cannot write branch history, independently of the
staged branch-code bit. -/
theorem activeScratchBToHistoryStep_eq_self_of_active_false
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = false) :
    activeScratchBToHistoryStep n counterWidth historyIndex x = x := by
  have hactiveCore : x.core.active = false := by
    simpa only [activeBit_get] using hactive
  change EncodedBit.toffoliStep
      (activeBit n counterWidth) (scratchBBit n counterWidth)
        (historyBit n counterWidth historyIndex) x = x
  unfold EncodedBit.toffoliStep
  simp [hactiveCore]

/-- The path-cleanup suffix is disabled as a whole when `active` is false. -/
theorem branchCodePathCleanupStep_eq_self_of_active_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = false) :
    branchCodePathCleanupStep n counterWidth x = x := by
  have hactiveCore : x.core.active = false := by
    simpa only [activeBit_get] using hactive
  unfold branchCodePathCleanupStep branchCodePathCleanupGates
  simp [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.cnotStep, EncodedBit.toffoliStep, hactiveCore]

/-- On an inactive, unwritten clean branch boundary, all three residue
cleanup gates are no-ops. -/
theorem branchResidueCleanupStep_eq_self_of_inactive_clean
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hhistory : (historyBit n counterWidth historyIndex).get x = false) :
    branchResidueCleanupStep n counterWidth historyIndex x = x := by
  have hactiveCore : x.core.active = false := by
    simpa only [activeBit_get] using hactive
  have hscratchACore : x.core.scratchA = false := by
    simpa only [scratchABit_get] using hscratchA
  have hscratchBCore : x.core.scratchB = false := by
    simpa only [scratchBBit_get] using hscratchB
  have hhistoryCore :
      x.core.history.val.testBit
          (WireAddress.bitIndex historyIndex).val = false := by
    simpa only [historyBit_get] using hhistory
  unfold branchResidueCleanupStep branchResidueCleanupGates
  simp [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.cnotStep, EncodedBit.toffoliStep, hactiveCore,
    hscratchACore, hscratchBCore, hhistoryCore]

/-- The routed compact body is extensionally idle on an inactive clean route.
This packages the individual native-gate no-op contracts without inspecting
any finite register value. -/
theorem activeBranchRoutedStep_eq_self_of_inactive_clean
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = false)
    (hpath : (pathBit n counterWidth).get x = false)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (_hscratchB : (scratchBBit n counterWidth).get x = false) :
    activeBranchRoutedStep
        n counterWidth low finalBit tempIndex historyIndex x = x := by
  rw [activeBranchRoutedStep,
    activeOddUGreaterSelectorStep_eq_self_of_active_false
      n counterWidth low finalBit x hactive hpath hcontrol,
    selectedEvenBranchCodeToScratchStep_eq_self_of_active_false
      n counterWidth low tempIndex x hactive,
    activeOddSelectedDataPathStep_eq_self_of_path_false
      n counterWidth x hcompare hpath hcontrol,
    oddBranchCodeToScratchStep_eq_self_of_compare_false
      n counterWidth x hcompare,
    activeScratchBToHistoryStep_eq_self_of_active_false
      n counterWidth historyIndex x hactive]
  exact auxActiveShiftDispatchStep_eq_self_of_active_false_scratchA_false
    n counterWidth x hactive hscratchA

/-- Literal native gate table for the compact nonzero round body.  The table
uses the masked odd selector, stages only even codes before arithmetic, reuses
the same two scratch bits for selected odd arithmetic, writes one history bit,
dispatches the paired shift, and erases all route residue. -/
def activeBranchBodyGates
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  activeOddUGreaterSelectorGates n counterWidth low finalBit ++
    selectedEvenBranchCodeToScratchGates n counterWidth low tempIndex ++
      activeOddSelectedDataPathGates n counterWidth ++
        oddBranchCodeToScratchGates n counterWidth ++
          [activeScratchBToHistoryGate n counterWidth historyIndex] ++
            auxActiveShiftDispatchGates n counterWidth ++
              branchCodePathCleanupGates n counterWidth ++
                branchResidueCleanupGates n counterWidth historyIndex

/-- Every native gate in the compact active body is disjoint from the
caller-owned target word. -/
theorem activeBranchBodyGates_bitDisjoint_target
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (targetIndex : Fin n) :
    ∀ gate,
      gate ∈ activeBranchBodyGates n counterWidth low finalBit tempIndex
          historyIndex →
        EncodedBit.GateSpec.bitDisjoint
          (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  rw [activeBranchBodyGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | hresidueCleanup
  · rcases List.mem_append.mp hprefix with hprefix | hpathCleanup
    · rcases List.mem_append.mp hprefix with hprefix | hshift
      · rcases List.mem_append.mp hprefix with hprefix | hhistory
        · rcases List.mem_append.mp hprefix with hprefix | hodd
          · rcases List.mem_append.mp hprefix with hprefix | hdata
            · rcases List.mem_append.mp hprefix with hselector | heven
              · exact activeOddUGreaterSelectorGates_bitDisjoint_target
                  n counterWidth low finalBit targetIndex gate hselector
              · exact selectedEvenBranchCodeToScratchGates_bitDisjoint_target
                  n counterWidth low tempIndex targetIndex gate heven
            · exact activeOddSelectedDataPathGates_bitDisjoint_target n
                counterWidth targetIndex gate hdata
          · exact oddBranchCodeToScratchGates_bitDisjoint_target n
              counterWidth targetIndex gate hodd
        · have : gate = activeScratchBToHistoryGate n counterWidth
              historyIndex := by
            simpa only [List.mem_cons, List.not_mem_nil, or_false] using
              hhistory
          subst gate
          exact ⟨
            liftCoreBit_targetValueBit_wire_ne n counterWidth
              (RegisterBits.activeBit n counterWidth) targetIndex,
            liftCoreBit_targetValueBit_wire_ne n counterWidth
              (RegisterBits.scratchBBit n counterWidth) targetIndex,
            liftCoreBit_targetValueBit_wire_ne n counterWidth
              (RegisterBits.historyBit n counterWidth historyIndex)
                targetIndex⟩
      · exact auxActiveShiftDispatchGates_bitDisjoint_target n counterWidth
          targetIndex gate hshift
    · exact branchCodePathCleanupGates_bitDisjoint_target n counterWidth
        targetIndex gate hpathCleanup
  · exact branchResidueCleanupGates_bitDisjoint_target n counterWidth
      historyIndex targetIndex gate hresidueCleanup

def activeBranchBodyStep
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (activeBranchBodyGates n counterWidth low finalBit tempIndex historyIndex)

theorem activeBranchBodyStep_eq_stages
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    activeBranchBodyStep
        n counterWidth low finalBit tempIndex historyIndex x =
      branchResidueCleanupStep n counterWidth historyIndex
        (branchCodePathCleanupStep n counterWidth
          (activeBranchRoutedStep
            n counterWidth low finalBit tempIndex historyIndex x)) := by
  unfold activeBranchBodyStep activeBranchBodyGates
  repeat rw [EncodedBit.GateSpec.stepList_append]
  simp only [activeOddUGreaterSelectorStep,
    selectedEvenBranchCodeToScratchStep, activeOddSelectedDataPathStep,
    oddBranchCodeToScratchStep, activeScratchBToHistoryStep,
    branchCodePathCleanupStep, branchResidueCleanupStep,
    activeBranchRoutedStep]
  rw [auxActiveShiftDispatchStep_eq_gateList]
  rfl

/-- The two compact cleanup suffixes preserve every observation outside the
shared path bit and the three core residue targets. -/
theorem activeBranchBodyStep_get_of_cleanup_targets_ne
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n))
    (observed : EncodedBit (encoding n counterWidth))
    (hpath : (pathBit n counterWidth).wire ≠ observed.wire)
    (hcompare : (compareBit n counterWidth).wire ≠ observed.wire)
    (hscratchA : (scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB : (scratchBBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (activeBranchBodyStep
          n counterWidth low finalBit tempIndex historyIndex x) =
      observed.get
        (activeBranchRoutedStep
          n counterWidth low finalBit tempIndex historyIndex x) := by
  rw [activeBranchBodyStep_eq_stages,
    branchResidueCleanupStep_get_of_targets_ne
      n counterWidth historyIndex observed hcompare hscratchB hscratchA,
    branchCodePathCleanupStep_get_of_path_ne
      n counterWidth observed hpath]

/-- Route cleanup preserves the complete compact `u` word. -/
theorem activeBranchBodyStep_core_u_eq_routed
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (activeBranchBodyStep
      n counterWidth low finalBit tempIndex historyIndex x).core.u =
      (activeBranchRoutedStep
        n counterWidth low finalBit tempIndex historyIndex x).core.u := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeBranchBodyStep_get_of_cleanup_targets_ne
    n counterWidth low finalBit tempIndex historyIndex
    ((uValueWord n counterWidth).bit bit)
    (by
      simpa [uValueWord, pathBit, RegisterBits.uValueBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth bit)
          (sharedPathBit n counterWidth)).symm)
    (by
      simpa [uValueWord, compareBit, RegisterBits.uValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [uValueWord, scratchABit, RegisterBits.uValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [uValueWord, scratchBBit, RegisterBits.uValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm) x
  simpa only [uValueWord_get] using h

/-- Route cleanup preserves the complete compact `v` word. -/
theorem activeBranchBodyStep_core_v_eq_routed
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (activeBranchBodyStep
      n counterWidth low finalBit tempIndex historyIndex x).core.v =
      (activeBranchRoutedStep
        n counterWidth low finalBit tempIndex historyIndex x).core.v := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeBranchBodyStep_get_of_cleanup_targets_ne
    n counterWidth low finalBit tempIndex historyIndex
    ((vValueWord n counterWidth).bit bit)
    (by
      simpa [vValueWord, pathBit, RegisterBits.vValueBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth bit)
          (sharedPathBit n counterWidth)).symm)
    (by
      simpa [vValueWord, compareBit, RegisterBits.vValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [vValueWord, scratchABit, RegisterBits.vValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [vValueWord, scratchBBit, RegisterBits.vValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm) x
  simpa only [vValueWord_get] using h

/-- Route cleanup preserves the complete compact `s` coefficient word. -/
theorem activeBranchBodyStep_core_sCoeff_eq_routed
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (activeBranchBodyStep
      n counterWidth low finalBit tempIndex historyIndex x).core.sCoeff =
      (activeBranchRoutedStep
        n counterWidth low finalBit tempIndex historyIndex x).core.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeBranchBodyStep_get_of_cleanup_targets_ne
    n counterWidth low finalBit tempIndex historyIndex
    ((sCoeffValueWord n counterWidth).bit bit)
    (by
      simpa [sCoeffValueWord, sCoeffValueBit, pathBit,
        RegisterBits.sCoeffValueBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.sCoeffValueBit n counterWidth bit)
          (sharedPathBit n counterWidth)).symm)
    (by
      simpa [sCoeffValueWord, sCoeffValueBit, compareBit,
        RegisterBits.sCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_sCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
    (by
      simpa [sCoeffValueWord, sCoeffValueBit, scratchABit,
        RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [sCoeffValueWord, sCoeffValueBit, scratchBBit,
        RegisterBits.sCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.sCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm) x
  simpa only [sCoeffValueWord, sCoeffValueBit_get] using h

/-- Route cleanup preserves the complete compact `r` coefficient word. -/
theorem activeBranchBodyStep_core_rCoeff_eq_routed
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (activeBranchBodyStep
      n counterWidth low finalBit tempIndex historyIndex x).core.rCoeff =
      (activeBranchRoutedStep
        n counterWidth low finalBit tempIndex historyIndex x).core.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  have h := activeBranchBodyStep_get_of_cleanup_targets_ne
    n counterWidth low finalBit tempIndex historyIndex
    ((rCoeffValueWord n counterWidth).bit bit)
    (by
      simpa [rCoeffValueWord, rCoeffValueBit, pathBit,
        RegisterBits.rCoeffValueBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.rCoeffValueBit n counterWidth bit)
          (sharedPathBit n counterWidth)).symm)
    (by
      simpa [rCoeffValueWord, rCoeffValueBit, compareBit,
        RegisterBits.rCoeffValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_rCoeff_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)))
    (by
      simpa [rCoeffValueWord, rCoeffValueBit, scratchABit,
        RegisterBits.rCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.rCoeff_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm)
    (by
      simpa [rCoeffValueWord, rCoeffValueBit, scratchBBit,
        RegisterBits.rCoeffValueBit] using
        (liftCoreBit_wire_ne n counterWidth
          (RegisterBits.rCoeff_scratchB_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit))).symm) x
  simpa only [rCoeffValueWord, rCoeffValueBit_get] using h

/-- Route cleanup preserves the compact active flag. -/
theorem activeBranchBodyStep_core_active_eq_routed
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth) :
    (activeBranchBodyStep
      n counterWidth low finalBit tempIndex historyIndex x).core.active =
      (activeBranchRoutedStep
        n counterWidth low finalBit tempIndex historyIndex x).core.active := by
  have h := activeBranchBodyStep_get_of_cleanup_targets_ne
    n counterWidth low finalBit tempIndex historyIndex
    (activeBit n counterWidth)
    (by
      simpa [activeBit, pathBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.activeBit n counterWidth)
          (sharedPathBit n counterWidth)).symm)
    (activeBit_compareBit_wire_ne n counterWidth).symm
    (activeBit_scratchABit_wire_ne n counterWidth).symm
    (activeBit_scratchBBit_wire_ne n counterWidth).symm x
  simpa only [activeBit_get] using h

/-- A complete compact branch body is exactly the identity after termination
or during padding, provided the current history slot is still unwritten. -/
theorem activeBranchBodyStep_eq_self_of_inactive_clean
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = false)
    (hpath : (pathBit n counterWidth).get x = false)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hhistory : (historyBit n counterWidth historyIndex).get x = false) :
    activeBranchBodyStep
        n counterWidth low finalBit tempIndex historyIndex x = x := by
  rw [activeBranchBodyStep_eq_stages,
    activeBranchRoutedStep_eq_self_of_inactive_clean
      n counterWidth low finalBit tempIndex historyIndex x hactive hpath
        hcontrol hcompare hscratchA hscratchB,
    branchCodePathCleanupStep_eq_self_of_active_false
      n counterWidth x hactive]
  exact branchResidueCleanupStep_eq_self_of_inactive_clean
    n counterWidth historyIndex x hactive hscratchA hscratchB hhistory

def activeBranchBodyProgram
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeBranchBodyGates n counterWidth low finalBit tempIndex historyIndex)

theorem activeBranchBody_realizes
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (activeBranchBodyProgram
        n counterWidth low finalBit tempIndex historyIndex)
      (activeBranchBodyStep
        n counterWidth low finalBit tempIndex historyIndex) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (activeBranchBodyGates n counterWidth low finalBit tempIndex historyIndex)

theorem activeBranchBodyGates_length
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    (activeBranchBodyGates
      n counterWidth low finalBit tempIndex historyIndex).length =
        45 * (n - 1) + 73 * n + 35 := by
  simp only [activeBranchBodyGates, List.length_append, List.length_cons,
    List.length_nil, activeOddUGreaterSelectorGates_length,
    selectedEvenBranchCodeToScratchGates_length,
    activeOddSelectedDataPathGates_length,
    oddBranchCodeToScratchGates_length,
    auxActiveShiftDispatchGates_length,
    branchCodePathCleanupGates_length,
    branchResidueCleanupGates_length]
  omega

theorem activeBranchBodyGates_xMultiplicity_sum
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    ((activeBranchBodyGates
      n counterWidth low finalBit tempIndex historyIndex).map
        EncodedBit.GateSpec.xMultiplicity).sum = 8 * n + 8 := by
  simp only [activeBranchBodyGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    activeOddUGreaterSelectorGates_xMultiplicity_sum,
    selectedEvenBranchCodeToScratchGates_xMultiplicity_sum,
    activeOddSelectedDataPathGates_xMultiplicity_sum,
    oddBranchCodeToScratchGates_xMultiplicity_sum,
    activeScratchBToHistoryGate_xMultiplicity,
    auxActiveShiftDispatchGates_xMultiplicity_sum,
    branchCodePathCleanupGates_xMultiplicity_sum,
    branchResidueCleanupGates_xMultiplicity_sum]
  omega

theorem activeBranchBodyGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    ((activeBranchBodyGates
      n counterWidth low finalBit tempIndex historyIndex).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 5 := by
  simp only [activeBranchBodyGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    activeOddUGreaterSelectorGates_cnotMultiplicity_sum,
    selectedEvenBranchCodeToScratchGates_cnotMultiplicity_sum,
    activeOddSelectedDataPathGates_cnotMultiplicity_sum,
    oddBranchCodeToScratchGates_cnotMultiplicity_sum,
    activeScratchBToHistoryGate_cnotMultiplicity,
    auxActiveShiftDispatchGates_cnotMultiplicity_sum,
    branchCodePathCleanupGates_cnotMultiplicity_sum,
    branchResidueCleanupGates_cnotMultiplicity_sum]
  omega

theorem activeBranchBodyGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    ((activeBranchBodyGates
      n counterWidth low finalBit tempIndex historyIndex).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
          45 * (n - 1) + 65 * n + 22 := by
  simp only [activeBranchBodyGates, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    activeOddUGreaterSelectorGates_toffoliMultiplicity_sum,
    selectedEvenBranchCodeToScratchGates_toffoliMultiplicity_sum,
    activeOddSelectedDataPathGates_toffoliMultiplicity_sum,
    oddBranchCodeToScratchGates_toffoliMultiplicity_sum,
    activeScratchBToHistoryGate_toffoliMultiplicity,
    auxActiveShiftDispatchGates_toffoliMultiplicity_sum,
    branchCodePathCleanupGates_toffoliMultiplicity_sum,
    branchResidueCleanupGates_toffoliMultiplicity_sum]
  omega

theorem activeBranchBodyProgram_x_count
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
        (activeBranchBodyProgram
          n counterWidth low finalBit tempIndex historyIndex).eventCost =
      8 * n + 8 := by
  rw [activeBranchBodyProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum,
    activeBranchBodyGates_xMultiplicity_sum]

theorem activeBranchBodyProgram_cnot_count
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
        (activeBranchBodyProgram
          n counterWidth low finalBit tempIndex historyIndex).eventCost = 5 := by
  rw [activeBranchBodyProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    activeBranchBodyGates_cnotMultiplicity_sum]

theorem activeBranchBodyProgram_toffoli_count
    (n counterWidth : Nat) (low finalBit tempIndex : Fin n)
    (historyIndex : Fin (2 * n)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (activeBranchBodyProgram
          n counterWidth low finalBit tempIndex historyIndex).eventCost =
      45 * (n - 1) + 65 * n + 22 := by
  rw [activeBranchBodyProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    activeBranchBodyGates_toffoliMultiplicity_sum]

/-- Literal reversal restores the full carrier after branch-code staging. -/
theorem selectedBranchCodeToScratchStep_reverse_identity
    (n counterWidth : Nat) (low tempIndex : Fin n)
    (x : Registers n counterWidth) :
    EncodedBit.GateSpec.stepList
        (selectedBranchCodeToScratchGates n counterWidth low tempIndex).reverse
        (selectedBranchCodeToScratchStep n counterWidth low tempIndex x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (selectedBranchCodeToScratchGates n counterWidth low tempIndex) x

end Compact

end
end MK
end MAU.Inversion
end QuantumAlg

end
