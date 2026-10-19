/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.ModularOperations

/-!
# Native controlled modular operations for the in-place point schedule

Only the arithmetic update at the center of each compute--update--uncompute
sandwich is controlled.  Its three-control gates are decomposed with the
existing clean compact path bit, so the ledger remains in the native
X/CNOT/Toffoli gate set and allocates no new wire.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace ControlledOperations

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK
open MAU.Inversion.MK.Circuit

/-- Reusable clean work bit for native control decomposition. -/
def pathWorkBit (fieldWidth counterWidth : Nat) :
    EncodedBit (Layout.encoding fieldWidth counterWidth) :=
  Layout.liftArithmeticBit fieldWidth counterWidth
    (MK.Compact.pathBit fieldWidth counterWidth)

/-- Lifted subtraction body acting on the compact public target. -/
def targetSubtractBodyGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  ArithmeticLift.gates fieldTail.succ counterWidth
    (CompactCorrection.targetUpdateGates fieldTail counterWidth p)

/-- Lifted addition body, the exact reverse of target subtraction. -/
def targetAddBodyGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  ArithmeticLift.gates fieldTail.succ counterWidth
    (CompactCorrection.targetUpdateGates fieldTail counterWidth p).reverse

lemma targetSubtractBodyGates_bitDisjoint_control
    (fieldTail counterWidth p : Nat) :
    ∀ gate, gate ∈ targetSubtractBodyGates fieldTail counterWidth p →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.controlBit fieldTail.succ counterWidth) gate :=
  ArithmeticLift.gates_bitDisjoint_controlBit fieldTail.succ counterWidth _

lemma targetAddBodyGates_bitDisjoint_control
    (fieldTail counterWidth p : Nat) :
    ∀ gate, gate ∈ targetAddBodyGates fieldTail counterWidth p →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.controlBit fieldTail.succ counterWidth) gate :=
  ArithmeticLift.gates_bitDisjoint_controlBit fieldTail.succ counterWidth _

lemma targetSubtractBodyGates_bitDisjoint_path
    (fieldTail counterWidth p : Nat) :
    ∀ gate, gate ∈ targetSubtractBodyGates fieldTail counterWidth p →
      EncodedBit.GateSpec.bitDisjoint
        (pathWorkBit fieldTail.succ counterWidth) gate := by
  exact ArithmeticLift.gates_bitDisjoint_liftArithmeticBit
    fieldTail.succ counterWidth
    (MK.Compact.pathBit fieldTail.succ counterWidth) _
    (CompactCorrection.targetUpdateGates_bitDisjoint_path
      fieldTail counterWidth p)

lemma targetAddBodyGates_bitDisjoint_path
    (fieldTail counterWidth p : Nat) :
    ∀ gate, gate ∈ targetAddBodyGates fieldTail counterWidth p →
      EncodedBit.GateSpec.bitDisjoint
        (pathWorkBit fieldTail.succ counterWidth) gate := by
  exact ArithmeticLift.gates_bitDisjoint_liftArithmeticBit
    fieldTail.succ counterWidth
    (MK.Compact.pathBit fieldTail.succ counterWidth) _
    (CompactCorrection.targetUpdateReverseGates_bitDisjoint_path
      fieldTail counterWidth p)

lemma controlBit_wire_ne_pathWorkBit (fieldWidth counterWidth : Nat) :
    (Layout.controlBit fieldWidth counterWidth).wire ≠
      (pathWorkBit fieldWidth counterWidth).wire :=
  Ne.symm (Layout.liftArithmeticBit_wire_ne_controlBit fieldWidth counterWidth
    (MK.Compact.pathBit fieldWidth counterWidth))

/-- Native controlled subtraction at a prepared target-update boundary. -/
def controlledTargetSubtractGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (Layout.controlBit fieldTail.succ counterWidth)
    (pathWorkBit fieldTail.succ counterWidth)
    (targetSubtractBodyGates fieldTail counterWidth p)
    (targetSubtractBodyGates_bitDisjoint_control fieldTail counterWidth p)
    (targetSubtractBodyGates_bitDisjoint_path fieldTail counterWidth p)
    (controlBit_wire_ne_pathWorkBit fieldTail.succ counterWidth)

/-- Native controlled addition at a prepared target-update boundary. -/
def controlledTargetAddGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (Layout.controlBit fieldTail.succ counterWidth)
    (pathWorkBit fieldTail.succ counterWidth)
    (targetAddBodyGates fieldTail counterWidth p)
    (targetAddBodyGates_bitDisjoint_control fieldTail counterWidth p)
    (targetAddBodyGates_bitDisjoint_path fieldTail counterWidth p)
    (controlBit_wire_ne_pathWorkBit fieldTail.succ counterWidth)

/-- Generic compute--controlled-update--uncompute semantics. -/
private lemma controlledSandwich_stepList
    {Data : Type} {encoding : BinaryLabelEncoding Data}
    (control work : EncodedBit encoding)
    (body prep : List (EncodedBit.GateSpec encoding))
    (hcontrolBody : ∀ gate, gate ∈ body →
      EncodedBit.GateSpec.bitDisjoint control gate)
    (hworkBody : ∀ gate, gate ∈ body →
      EncodedBit.GateSpec.bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire)
    (input : Data) (selected : Bool)
    (hcontrol : control.get
      (EncodedBit.GateSpec.stepList prep input) = selected)
    (hwork : work.get
      (EncodedBit.GateSpec.stepList prep input) = false) :
    EncodedBit.GateSpec.stepList
        (prep ++
          EncodedBit.GateSpec.controlledListWithWorkGates control work body
            hcontrolBody hworkBody hcontrolWork ++ prep.reverse) input =
      if selected then
        EncodedBit.GateSpec.stepList (prep ++ body ++ prep.reverse) input
      else input := by
  simp only [EncodedBit.GateSpec.stepList_append]
  cases selected with
  | false =>
      have hselected :=
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
          control work body hcontrolBody hworkBody hcontrolWork
          (EncodedBit.GateSpec.stepList prep input) hcontrol
      rw [show EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates control work body
            hcontrolBody hworkBody hcontrolWork)
          (EncodedBit.GateSpec.stepList prep input) =
          EncodedBit.GateSpec.stepList prep input by
        simpa only [EncodedBit.GateSpec.controlledListWithWorkStep] using
          hselected]
      simp only [Bool.false_eq_true, if_false]
      exact EncodedBit.GateSpec.stepList_reverse_stepList prep input
  | true =>
      have hselected :=
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
          control work body hcontrolBody hworkBody hcontrolWork
          (EncodedBit.GateSpec.stepList prep input) hcontrol hwork
      rw [show EncodedBit.GateSpec.stepList
          (EncodedBit.GateSpec.controlledListWithWorkGates control work body
            hcontrolBody hworkBody hcontrolWork)
          (EncodedBit.GateSpec.stepList prep input) =
          EncodedBit.GateSpec.stepList body
            (EncodedBit.GateSpec.stepList prep input) by
        simpa only [EncodedBit.GateSpec.controlledListWithWorkStep] using
          hselected]
      rfl

/-! ## Controlled constant coordinate updates -/

def subtractConstantXGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := ModularOperations.constantXPrefixGates fieldTail counterWidth p
    hp constant
  prep ++ controlledTargetSubtractGates fieldTail counterWidth p ++
    prep.reverse

def addConstantXGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := ModularOperations.constantXPrefixGates fieldTail counterWidth p
    hp constant
  prep ++ controlledTargetAddGates fieldTail counterWidth p ++ prep.reverse

def subtractConstantXStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (subtractConstantXGates fieldTail counterWidth p hp constant)

def addConstantXStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (addConstantXGates fieldTail counterWidth p hp constant)

lemma subtractConstantXStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 constant : Word fieldTail.succ)
    (hx : mutableX.val < p) (hc : constant.val < p) :
    subtractConstantXStep fieldTail counterWidth p hp constant
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩
        (if control then
          CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
            mutableX constant
        else mutableX) t0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let prep := ModularOperations.constantXPrefixGates fieldTail counterWidth p
    hp constant
  have hprefix := ModularOperations.constantXPrefixGates_stepList fieldTail
    counterWidth p hp control mutableY «λ» mutableX t0 constant
  have hsandwich := controlledSandwich_stepList
    (Layout.controlBit fieldTail.succ counterWidth)
    (pathWorkBit fieldTail.succ counterWidth)
    (targetSubtractBodyGates fieldTail counterWidth p) prep
    (targetSubtractBodyGates_bitDisjoint_control fieldTail counterWidth p)
    (targetSubtractBodyGates_bitDisjoint_path fieldTail counterWidth p)
    (controlBit_wire_ne_pathWorkBit fieldTail.succ counterWidth)
    input control
    (by rw [hprefix]; rfl)
    (by rw [hprefix]; rfl)
  change EncodedBit.GateSpec.stepList
      (prep ++ controlledTargetSubtractGates fieldTail counterWidth p ++
        prep.reverse) input = _
  rw [show EncodedBit.GateSpec.stepList
      (prep ++ controlledTargetSubtractGates fieldTail counterWidth p ++
        prep.reverse) input =
      if control then EncodedBit.GateSpec.stepList
        (prep ++ targetSubtractBodyGates fieldTail counterWidth p ++
          prep.reverse) input else input by
    simpa [controlledTargetSubtractGates] using hsandwich]
  cases control with
  | false => rfl
  | true =>
      simpa [input, prep, targetSubtractBodyGates,
        ModularOperations.subtractConstantXStep,
        ModularOperations.subtractConstantXGates] using
        ModularOperations.subtractConstantXStep_cleanEndpoint fieldTail
          counterWidth p hpPos hp true mutableY «λ» mutableX t0 constant
          hx hc

lemma addConstantXStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 constant : Word fieldTail.succ)
    (hx : mutableX.val < p) (hc : constant.val < p) :
    addConstantXStep fieldTail counterWidth p hp constant
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩
        (if control then
          CompactCorrection.modularSumFixedWord fieldTail p hpPos hp mutableX
            constant
        else mutableX) t0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let prep := ModularOperations.constantXPrefixGates fieldTail counterWidth p
    hp constant
  have hprefix := ModularOperations.constantXPrefixGates_stepList fieldTail
    counterWidth p hp control mutableY «λ» mutableX t0 constant
  have hsandwich := controlledSandwich_stepList
    (Layout.controlBit fieldTail.succ counterWidth)
    (pathWorkBit fieldTail.succ counterWidth)
    (targetAddBodyGates fieldTail counterWidth p) prep
    (targetAddBodyGates_bitDisjoint_control fieldTail counterWidth p)
    (targetAddBodyGates_bitDisjoint_path fieldTail counterWidth p)
    (controlBit_wire_ne_pathWorkBit fieldTail.succ counterWidth)
    input control
    (by rw [hprefix]; rfl)
    (by rw [hprefix]; rfl)
  change EncodedBit.GateSpec.stepList
      (prep ++ controlledTargetAddGates fieldTail counterWidth p ++
        prep.reverse) input = _
  rw [show EncodedBit.GateSpec.stepList
      (prep ++ controlledTargetAddGates fieldTail counterWidth p ++
        prep.reverse) input =
      if control then EncodedBit.GateSpec.stepList
        (prep ++ targetAddBodyGates fieldTail counterWidth p ++ prep.reverse)
          input else input by
    simpa [controlledTargetAddGates] using hsandwich]
  cases control with
  | false => rfl
  | true =>
      simpa [input, prep, targetAddBodyGates,
        ModularOperations.addConstantXStep,
        ModularOperations.addConstantXGates] using
        ModularOperations.addConstantXStep_cleanEndpoint fieldTail counterWidth
          p hpPos hp true mutableY «λ» mutableX t0 constant hx hc

/-! ## Controlled variable subtraction -/

def subtractT0FromXGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let prep := ModularOperations.xFromT0PrefixGates fieldTail counterWidth p hp
  prep ++ controlledTargetSubtractGates fieldTail counterWidth p ++
    prep.reverse

def subtractT0FromXStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (subtractT0FromXGates fieldTail counterWidth p hp)

lemma subtractT0FromXStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX t0 : Word fieldTail.succ)
    (hx : mutableX.val < p) (ht0 : t0.val < p) :
    subtractT0FromXStep fieldTail counterWidth p hp
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX t0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩
        (if control then
          CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
            mutableX t0
        else mutableX) t0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX t0
  let prep := ModularOperations.xFromT0PrefixGates fieldTail counterWidth p hp
  have hprefix := ModularOperations.xFromT0PrefixGates_stepList fieldTail
    counterWidth p hp control mutableY «λ» mutableX t0
  have hsandwich := controlledSandwich_stepList
    (Layout.controlBit fieldTail.succ counterWidth)
    (pathWorkBit fieldTail.succ counterWidth)
    (targetSubtractBodyGates fieldTail counterWidth p) prep
    (targetSubtractBodyGates_bitDisjoint_control fieldTail counterWidth p)
    (targetSubtractBodyGates_bitDisjoint_path fieldTail counterWidth p)
    (controlBit_wire_ne_pathWorkBit fieldTail.succ counterWidth)
    input control
    (by rw [hprefix]; rfl)
    (by rw [hprefix]; rfl)
  change EncodedBit.GateSpec.stepList
      (prep ++ controlledTargetSubtractGates fieldTail counterWidth p ++
        prep.reverse) input = _
  rw [show EncodedBit.GateSpec.stepList
      (prep ++ controlledTargetSubtractGates fieldTail counterWidth p ++
        prep.reverse) input =
      if control then EncodedBit.GateSpec.stepList
        (prep ++ targetSubtractBodyGates fieldTail counterWidth p ++
          prep.reverse) input else input by
    simpa [controlledTargetSubtractGates] using hsandwich]
  cases control with
  | false => rfl
  | true =>
      simpa [input, prep, targetSubtractBodyGates,
        ModularOperations.subtractT0FromXStep,
        ModularOperations.subtractT0FromXGates] using
        ModularOperations.subtractT0FromXStep_cleanEndpoint fieldTail
          counterWidth p hpPos hp true mutableY «λ» mutableX t0 hx ht0

/-! ## Controlled y constant update by coordinate conjugation -/

def subtractConstantYGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let swap := ModularOperations.swapXYGates fieldTail.succ counterWidth
  swap ++ subtractConstantXGates fieldTail counterWidth p hp constant ++
    swap.reverse

def subtractConstantYStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (subtractConstantYGates fieldTail counterWidth p hp constant)

lemma subtractConstantYStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX constant : Word fieldTail.succ)
    (hy : mutableY.val < p) (hc : constant.val < p) :
    subtractConstantYStep fieldTail counterWidth p hp constant
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        (if control then
          CompactCorrection.modularDifferenceWord fieldTail p hpPos hp
            mutableY constant
        else mutableY) «λ» ⟨p, hp⟩ mutableX 0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX 0
  let result := if control then
    CompactCorrection.modularDifferenceWord fieldTail p hpPos hp mutableY
      constant else mutableY
  let output := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control result «λ» ⟨p, hp⟩ mutableX 0
  let swap := ModularOperations.swapXYGates fieldTail.succ counterWidth
  have hinput := ModularOperations.swapXYGates_cleanEndpoint fieldTail.succ
    counterWidth p hp control mutableY «λ» mutableX
  have hmiddle := subtractConstantXStep_cleanEndpoint fieldTail counterWidth p
    hpPos hp control mutableX «λ» mutableY 0 constant hy hc
  have houtput := ModularOperations.swapXYGates_cleanEndpoint fieldTail.succ
    counterWidth p hp control result «λ» mutableX
  change EncodedBit.GateSpec.stepList
      (swap ++ subtractConstantXGates fieldTail counterWidth p hp constant ++
        swap.reverse) input = output
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList swap input =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableX «λ» ⟨p, hp⟩ mutableY 0 by
    simpa [swap, input] using hinput]
  rw [show EncodedBit.GateSpec.stepList
      (subtractConstantXGates fieldTail counterWidth p hp constant)
      (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableX «λ» ⟨p, hp⟩ mutableY 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableX «λ» ⟨p, hp⟩ result 0 by
    simpa [subtractConstantXStep, result] using hmiddle]
  rw [show MontgomeryOperations.cleanState fieldTail.succ counterWidth control
      mutableX «λ» ⟨p, hp⟩ result 0 =
      EncodedBit.GateSpec.stepList swap output by
    simpa [swap, output, result] using houtput.symm]
  exact EncodedBit.GateSpec.stepList_reverse_stepList swap output

/-! ## Controlled modular negation -/

private lemma swapXT0Gates_bitDisjoint_control
    (fieldWidth counterWidth : Nat) :
    ∀ gate, gate ∈ RegisterRouting.swapXT0Gates fieldWidth counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.controlBit fieldWidth counterWidth) gate := by
  intro gate hgate
  simp only [RegisterRouting.swapXT0Gates, RegisterRouting.swapGates,
    EncodedBit.Word.swapGates, List.mem_flatMap] at hgate
  rcases hgate with ⟨bit, _hbit, hgate⟩
  simp only [EncodedBit.swapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact ⟨Layout.liftArithmeticBit_wire_ne_controlBit _ _ _,
      Layout.liftArithmeticBit_wire_ne_controlBit _ _ _⟩
  · exact ⟨Layout.liftArithmeticBit_wire_ne_controlBit _ _ _,
      Layout.liftArithmeticBit_wire_ne_controlBit _ _ _⟩
  · exact ⟨Layout.liftArithmeticBit_wire_ne_controlBit _ _ _,
      Layout.liftArithmeticBit_wire_ne_controlBit _ _ _⟩

private lemma swapXT0Gates_bitDisjoint_path
    (fieldWidth counterWidth : Nat) :
    ∀ gate, gate ∈ RegisterRouting.swapXT0Gates fieldWidth counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (pathWorkBit fieldWidth counterWidth) gate := by
  have hx : ∀ bit,
      ((RegisterRouting.mutableXPort fieldWidth counterWidth).word.bit
        bit).wire ≠ (pathWorkBit fieldWidth counterWidth).wire := by
    intro bit
    simpa [RegisterRouting.mutableXPort, Layout.mutableXWord,
      Layout.liftArithmeticWord, pathWorkBit, MK.Compact.vValueWord,
      MK.Compact.pathBit] using
        Layout.liftArithmeticBit_wire_ne fieldWidth counterWidth _ _
          (MK.Compact.liftCoreBit_liftSharedBit_wire_ne fieldWidth counterWidth
            (MK.RegisterBits.vValueBit fieldWidth counterWidth
              bit)
            (MK.Compact.sharedPathBit fieldWidth counterWidth))
  have ht0 : ∀ bit,
      ((RegisterRouting.t0Port fieldWidth counterWidth).word.bit bit).wire ≠
        (pathWorkBit fieldWidth counterWidth).wire := by
    intro bit
    exact Ne.symm (Layout.liftArithmeticBit_wire_ne fieldWidth counterWidth _ _
      (MK.Compact.liftSharedBit_targetValueBit_wire_ne fieldWidth counterWidth
        (MK.Compact.sharedPathBit fieldWidth counterWidth) bit))
  intro gate hgate
  simp only [RegisterRouting.swapXT0Gates, RegisterRouting.swapGates,
    EncodedBit.Word.swapGates, List.mem_flatMap] at hgate
  rcases hgate with ⟨bit, _hbit, hgate⟩
  simp only [EncodedBit.swapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact ⟨hx bit, ht0 bit⟩
  · exact ⟨ht0 bit, hx bit⟩
  · exact ⟨hx bit, ht0 bit⟩

def controlledSwapXT0Gates (fieldWidth counterWidth : Nat) :
    List (EncodedBit.GateSpec (Layout.encoding fieldWidth counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (Layout.controlBit fieldWidth counterWidth)
    (pathWorkBit fieldWidth counterWidth)
    (RegisterRouting.swapXT0Gates fieldWidth counterWidth)
    (swapXT0Gates_bitDisjoint_control fieldWidth counterWidth)
    (swapXT0Gates_bitDisjoint_path fieldWidth counterWidth)
    (controlBit_wire_ne_pathWorkBit fieldWidth counterWidth)

def negateXGates
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  let compute := ModularOperations.subtractXFromT0Gates fieldTail counterWidth
    p hp
  compute ++ controlledSwapXT0Gates fieldTail.succ counterWidth ++
    compute.reverse

def negateXStep
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList (negateXGates fieldTail counterWidth p hp)

lemma negateXStep_cleanEndpoint
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (control : Bool) (mutableY «λ» mutableX : Word fieldTail.succ)
    (hx : mutableX.val < p) :
    negateXStep fieldTail counterWidth p hp
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX 0) =
      MontgomeryOperations.cleanState fieldTail.succ counterWidth control
        mutableY «λ» ⟨p, hp⟩
        (if control then
          CompactCorrection.modularDifferenceWord fieldTail p hpPos hp 0
            mutableX
        else mutableX) 0 := by
  let input := MontgomeryOperations.cleanState fieldTail.succ counterWidth
    control mutableY «λ» ⟨p, hp⟩ mutableX 0
  let compute := ModularOperations.subtractXFromT0Gates fieldTail counterWidth
    p hp
  have hcompute := ModularOperations.subtractXFromT0Step_cleanEndpoint
    fieldTail counterWidth p hpPos hp control mutableY «λ» mutableX 0 hx
      (by simp [hpPos])
  have hsandwich := controlledSandwich_stepList
    (Layout.controlBit fieldTail.succ counterWidth)
    (pathWorkBit fieldTail.succ counterWidth)
    (RegisterRouting.swapXT0Gates fieldTail.succ counterWidth) compute
    (swapXT0Gates_bitDisjoint_control fieldTail.succ counterWidth)
    (swapXT0Gates_bitDisjoint_path fieldTail.succ counterWidth)
    (controlBit_wire_ne_pathWorkBit fieldTail.succ counterWidth)
    input control
    (by rw [show EncodedBit.GateSpec.stepList compute input =
        MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX
            (CompactCorrection.modularDifferenceWord fieldTail p hpPos hp 0
              mutableX) by
          simpa [compute, input, ModularOperations.subtractXFromT0Step] using
            hcompute]; rfl)
    (by rw [show EncodedBit.GateSpec.stepList compute input =
        MontgomeryOperations.cleanState fieldTail.succ counterWidth control
          mutableY «λ» ⟨p, hp⟩ mutableX
            (CompactCorrection.modularDifferenceWord fieldTail p hpPos hp 0
              mutableX) by
          simpa [compute, input, ModularOperations.subtractXFromT0Step] using
            hcompute]; rfl)
  change EncodedBit.GateSpec.stepList
      (compute ++ controlledSwapXT0Gates fieldTail.succ counterWidth ++
        compute.reverse) input = _
  rw [show EncodedBit.GateSpec.stepList
      (compute ++ controlledSwapXT0Gates fieldTail.succ counterWidth ++
        compute.reverse) input =
      if control then EncodedBit.GateSpec.stepList
        (compute ++ RegisterRouting.swapXT0Gates fieldTail.succ counterWidth ++
          compute.reverse) input else input by
    simpa [controlledSwapXT0Gates] using hsandwich]
  cases control with
  | false => rfl
  | true =>
      let neg := CompactCorrection.modularDifferenceWord fieldTail p hpPos hp 0
        mutableX
      have hneg : neg.val < p := by
        simp [neg, CompactCorrection.modularDifferenceWord_val,
          Nat.mod_lt _ hpPos]
      have hnegneg :
          CompactCorrection.modularDifferenceWord fieldTail p hpPos hp 0 neg =
            mutableX := by
        apply Fin.ext
        simp only [neg, CompactCorrection.modularDifferenceWord_val,
          Fin.val_zero]
        by_cases hx0 : mutableX.val = 0
        · simp [hx0]
        · have hsub : p - mutableX.val < p := by omega
          rw [Nat.zero_add, Nat.mod_eq_of_lt hsub]
          have hsubsub : p - (p - mutableX.val) = mutableX.val := by omega
          rw [hsubsub, Nat.mod_eq_of_lt hx]
      have hcomputed : EncodedBit.GateSpec.stepList compute input =
          MontgomeryOperations.cleanState fieldTail.succ counterWidth true
            mutableY «λ» ⟨p, hp⟩ mutableX neg := by
        simpa [compute, input, neg, ModularOperations.subtractXFromT0Step] using
          hcompute
      have hswapped := RegisterRouting.swapXT0Gates_stepList fieldTail.succ
        counterWidth
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth true
          mutableY «λ» ⟨p, hp⟩ mutableX neg)
      have houtputCompute :=
        ModularOperations.subtractXFromT0Step_cleanEndpoint fieldTail
          counterWidth p hpPos hp true mutableY «λ» neg 0 hneg
          (by simp [hpPos])
      simp only [EncodedBit.GateSpec.stepList_append]
      rw [hcomputed]
      rw [show EncodedBit.GateSpec.stepList
          (RegisterRouting.swapXT0Gates fieldTail.succ counterWidth)
          (MontgomeryOperations.cleanState fieldTail.succ counterWidth true
            mutableY «λ» ⟨p, hp⟩ mutableX neg) =
          MontgomeryOperations.cleanState fieldTail.succ counterWidth true
            mutableY «λ» ⟨p, hp⟩ neg mutableX by
        simpa [MontgomeryOperations.cleanState, MK.initialRegisters] using
          hswapped]
      rw [show MontgomeryOperations.cleanState fieldTail.succ counterWidth true
          mutableY «λ» ⟨p, hp⟩ neg mutableX =
          EncodedBit.GateSpec.stepList compute
            (MontgomeryOperations.cleanState fieldTail.succ counterWidth true
              mutableY «λ» ⟨p, hp⟩ neg 0) by
        simpa [compute, ModularOperations.subtractXFromT0Step, hnegneg] using
          houtputCompute.symm]
      exact EncodedBit.GateSpec.stepList_reverse_stepList compute
        (MontgomeryOperations.cleanState fieldTail.succ counterWidth true
          mutableY «λ» ⟨p, hp⟩ neg 0)

lemma subtractConstantX_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (subtractConstantXGates fieldTail counterWidth p hp constant)) environment
      (subtractConstantXStep fieldTail counterWidth p hp constant) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma addConstantX_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (addConstantXGates fieldTail counterWidth p hp constant)) environment
      (addConstantXStep fieldTail counterWidth p hp constant) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma subtractT0FromX_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (subtractT0FromXGates fieldTail counterWidth p hp)) environment
      (subtractT0FromXStep fieldTail counterWidth p hp) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma subtractConstantY_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ)
    (constant : Word fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (subtractConstantYGates fieldTail counterWidth p hp constant)) environment
      (subtractConstantYStep fieldTail counterWidth p hp constant) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

lemma negateX_realizes
    (fieldTail counterWidth p : Nat) (hp : p < 2 ^ fieldTail.succ) :
    UnitaryCircuit.Realizes (Layout.encoding fieldTail.succ counterWidth)
      (EncodedBit.GateSpec.programList
        (QubitLayout.canonical _) .empty
        (negateXGates fieldTail counterWidth p hp)) environment
      (negateXStep fieldTail counterWidth p hp) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty _

end
end ControlledOperations
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
