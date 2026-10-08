/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Components.Encoded.BasisMap
import Mathlib.Tactic
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.MAU.Addition
import all QuantumAlg.Primitives.MAU.Addition.VBE.Arithmetic

/-!
# Fixed-layout VBE modular-addition circuits

This module realizes the general-modulus compare/subtract/add-back route as one
explicit X/CNOT/Toffoli program.  The register routing and stage order follow
[VBE95, 9511018.tex:294-327]; controlled constant loading for downstream
modular multiplication follows [VBE95, 9511018.tex:350-367].
-/

section

namespace QuantumAlg
namespace MAU.Addition
namespace VBECircuit

noncomputable section

/-- The canonical adder is one bit wider than the source/modulus words so its
target word retains the ordinary-sum overflow bit. -/
abbrev AdderWidth (n : Nat) : Nat :=
  n + 1

/-- Logical registers of the VBE modular adder.  Only the low `n` bits of the
active source participate in source swapping; its extra high bit stays zero. -/
structure Registers (n : Nat) where
  /-- Active source word, widened by one overflow bit. -/
  activeSource : PlainAdder.Word (AdderWidth n)
  /-- Arithmetic target word, widened by one overflow bit. -/
  target : PlainAdder.Word (AdderWidth n)
  /-- Canonical plain-adder carry bit. -/
  carry : Bool
  /-- Separate `n`-bit source or modulus word parked during arithmetic. -/
  parkedSource : PlainAdder.Word n
  /-- Canonical plain-adder carry workspace. -/
  carryWork : PlainAdder.Schedule.PowerOfTwo.CarryWork (AdderWidth n)
  /-- Temporary flag recording whether modular reduction is required. -/
  reductionFlag : Bool
deriving DecidableEq

/-- Product carrier matching the physical field order: adder data, parked
source, carry work, then the reduction flag. -/
abbrev RawRegisters (n : Nat) : Type :=
  (((PlainAdder.Data (AdderWidth n) × PlainAdder.Word n) ×
      PlainAdder.Schedule.PowerOfTwo.CarryWork (AdderWidth n)) × Bool)

/-- Fieldwise equivalence between the named logical registers and their packed
physical carrier. -/
def registersEquiv (n : Nat) : Registers n ≃ RawRegisters n where
  toFun := fun x =>
    ((({ left := x.activeSource, right := x.target, carry := x.carry },
        x.parkedSource), x.carryWork), x.reductionFlag)
  invFun := fun x =>
    { activeSource := x.1.1.1.left
      target := x.1.1.1.right
      carry := x.1.1.1.carry
      parkedSource := x.1.1.2
      carryWork := x.1.2
      reductionFlag := x.2 }
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rcases x with ⟨left, reductionFlag⟩
    rcases left with ⟨dataAndParked, carryWork⟩
    rcases dataAndParked with ⟨data, parkedSource⟩
    cases data
    rfl

/-- Packed encoding of the adder data and the source word parked beside it. -/
abbrev dataAndParkedEncoding (n : Nat) :
    BinaryLabelEncoding
      (PlainAdder.Data (AdderWidth n) × PlainAdder.Word n) :=
  BinaryLabelEncoding.prod
    (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n)

/-- Packed encoding after appending the canonical carry-work register. -/
abbrev dataParkedWorkEncoding (n : Nat) :
    BinaryLabelEncoding
      ((PlainAdder.Data (AdderWidth n) × PlainAdder.Word n) ×
        PlainAdder.Schedule.PowerOfTwo.CarryWork (AdderWidth n)) :=
  BinaryLabelEncoding.prod
    (dataAndParkedEncoding n)
    (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n))

/-- Packed product encoding before field names are restored. -/
abbrev rawEncoding (n : Nat) : BinaryLabelEncoding (RawRegisters n) :=
  BinaryLabelEncoding.prod (dataParkedWorkEncoding n) BinaryLabelEncoding.bool

/-- Fixed faithful binary layout used by every VBE modular-addition stage. -/
abbrev encoding (n : Nat) : BinaryLabelEncoding (Registers n) :=
  (rawEncoding n).relabel (registersEquiv n)

@[simp] private theorem event_insertMiddleGateSpec
    {Left Middle Right : Type}
    {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}
    (middle : BinaryLabelEncoding Middle)
    (gate : EncodedBit.GateSpec (BinaryLabelEncoding.prod left right)) :
    (EncodedBit.GateSpec.event .empty)
        (EncodedBit.GateSpec.insertMiddle middle gate) =
      (EncodedBit.GateSpec.event .empty) gate := by
  cases gate <;> rfl

/-! ### Exact field lenses -/

/-- Lift one canonical plain-adder data bit through the parked, work, and flag
fields, then restore named registers. -/
def liftAdderDataBit (n : Nat)
    (bit : EncodedBit
      (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))) :
    EncodedBit (encoding n) :=
  (BinaryLabelEncoding.prodLeftBit
    (dataParkedWorkEncoding n) BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prodLeftBit
      (dataAndParkedEncoding n)
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n))
      (BinaryLabelEncoding.prodLeftBit
        (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))
        (PlainAdder.Schedule.PowerOfTwo.wordEncoding n) bit))).relabel
          (registersEquiv n)

/-- One bit of the full `(n+1)`-bit active source word. -/
def activeSourceBit (n : Nat) (bit : Fin (AdderWidth n)) :
    EncodedBit (encoding n) :=
  liftAdderDataBit n
    (PlainAdder.Schedule.PowerOfTwo.leftBit (AdderWidth n) bit)

/-- One low source bit, excluding the dedicated high overflow position. -/
def activeSourceLowBit (n : Nat) (bit : Fin n) :
    EncodedBit (encoding n) :=
  activeSourceBit n ⟨bit.val, by simp [AdderWidth]⟩

/-- One bit of the full `(n+1)`-bit arithmetic target. -/
def targetBit (n : Nat) (bit : Fin (AdderWidth n)) :
    EncodedBit (encoding n) :=
  liftAdderDataBit n
    (PlainAdder.Schedule.PowerOfTwo.rightBit (AdderWidth n) bit)

/-- The canonical plain-adder carry bit. -/
def carryBit (n : Nat) : EncodedBit (encoding n) :=
  liftAdderDataBit n
    (PlainAdder.Schedule.PowerOfTwo.carryBit (AdderWidth n))

/-- One bit of the separately parked `n`-bit source/modulus word. -/
def parkedSourceBit (n : Nat) (bit : Fin n) :
    EncodedBit (encoding n) :=
  (BinaryLabelEncoding.prodLeftBit
    (dataParkedWorkEncoding n) BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prodLeftBit
      (dataAndParkedEncoding n)
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n))
      (BinaryLabelEncoding.prodRightBit
        (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))
        (PlainAdder.Schedule.PowerOfTwo.wordEncoding n)
        (PlainAdder.Schedule.PowerOfTwo.wordBit n bit)))).relabel
          (registersEquiv n)

/-- The temporary reduction flag copied from the target high bit. -/
def reductionFlagBit (n : Nat) : EncodedBit (encoding n) :=
  (BinaryLabelEncoding.prodRightBit
    (dataParkedWorkEncoding n) BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit).relabel (registersEquiv n)

/-- One addressed carry-work bit, used to prove that source routing preserves
the clean work register. -/
def carryWorkBit (n : Nat) (bit : Fin (AdderWidth n - 1)) :
    EncodedBit (encoding n) :=
  (BinaryLabelEncoding.prodLeftBit
    (dataParkedWorkEncoding n) BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prodRightBit
      (dataAndParkedEncoding n)
      (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n))
      (BinaryLabelEncoding.finIdentityBit (AdderWidth n - 1) bit))).relabel
        (registersEquiv n)

/-- Low `n` bits of the active source, used for source/modulus swapping and
constant loading. -/
def activeSourceLowWord (n : Nat) : EncodedBit.Word (encoding n) n where
  bit := activeSourceLowBit n

/-- Full active source word.  Constant clear/restore uses this view so the
extra high zero bit is part of the same exact target layout. -/
def activeSourceWord (n : Nat) :
    EncodedBit.Word (encoding n) (AdderWidth n) where
  bit := activeSourceBit n

/-- The unexchanged high bit of the active `(n+1)`-bit source word. -/
def activeSourceHighBit (n : Nat) : EncodedBit (encoding n) :=
  activeSourceBit n (Fin.last n)

/-- Full arithmetic target word, including the overflow probe bit. -/
def targetWord (n : Nat) :
    EncodedBit.Word (encoding n) (AdderWidth n) where
  bit := targetBit n

/-- Separately parked source/modulus word. -/
def parkedSourceWord (n : Nat) : EncodedBit.Word (encoding n) n where
  bit := parkedSourceBit n

@[simp] theorem activeSourceBit_get (n : Nat) (bit : Fin (AdderWidth n))
    (x : Registers n) :
    (activeSourceBit n bit).get x =
      (PlainAdder.Schedule.PowerOfTwo.wordBit (AdderWidth n) bit).get
        x.activeSource :=
  rfl

@[simp] theorem targetBit_get (n : Nat) (bit : Fin (AdderWidth n))
    (x : Registers n) :
    (targetBit n bit).get x =
      (PlainAdder.Schedule.PowerOfTwo.wordBit (AdderWidth n) bit).get
        x.target :=
  rfl

@[simp] theorem activeSourceLowBit_get (n : Nat) (bit : Fin n)
    (x : Registers n) :
    (activeSourceLowBit n bit).get x =
      x.activeSource.val.testBit bit.val := by
  simp [activeSourceLowBit]

@[simp] theorem activeSourceHighBit_get (n : Nat) (x : Registers n) :
    (activeSourceHighBit n).get x = x.activeSource.val.testBit n := by
  simp [activeSourceHighBit]

@[simp] theorem parkedSourceBit_get (n : Nat) (bit : Fin n)
    (x : Registers n) :
    (parkedSourceBit n bit).get x =
      (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get x.parkedSource :=
  rfl

@[simp] theorem carryBit_get (n : Nat) (x : Registers n) :
    (carryBit n).get x = x.carry :=
  rfl

@[simp] theorem reductionFlagBit_get (n : Nat) (x : Registers n) :
    (reductionFlagBit n).get x = x.reductionFlag :=
  rfl

@[simp] theorem carryWorkBit_get (n : Nat)
    (bit : Fin (AdderWidth n - 1)) (x : Registers n) :
    (carryWorkBit n bit).get x =
      (BinaryLabelEncoding.finIdentityBit
        (AdderWidth n - 1) bit).get x.carryWork :=
  rfl

theorem encoding_width (n : Nat) :
    (encoding n).width = 4 * n + 4 := by
  simp [encoding, rawEncoding, dataParkedWorkEncoding,
    dataAndParkedEncoding,
    PlainAdder.Schedule.PowerOfTwo.wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding, AdderWidth]
  omega

@[simp] theorem activeSourceBit_wire_val (n : Nat)
    (bit : Fin (AdderWidth n)) :
    (activeSourceBit n bit).wire.val = n - bit.val := by
  change AdderWidth n - 1 - bit.val = n - bit.val
  simp [AdderWidth]

@[simp] theorem activeSourceLowBit_wire_val (n : Nat) (bit : Fin n) :
    (activeSourceLowBit n bit).wire.val = n - bit.val := by
  simp [activeSourceLowBit]

@[simp] theorem activeSourceHighBit_wire_val (n : Nat) :
    (activeSourceHighBit n).wire.val = 0 := by
  simp [activeSourceHighBit, AdderWidth]

@[simp] theorem targetBit_wire_val (n : Nat)
    (bit : Fin (AdderWidth n)) :
    (targetBit n bit).wire.val = (n + 1) + (n - bit.val) := by
  change AdderWidth n + (AdderWidth n - 1 - bit.val) = _
  simp [AdderWidth]

@[simp] theorem carryBit_wire_val (n : Nat) :
    (carryBit n).wire.val = 2 * n + 2 := by
  change AdderWidth n + AdderWidth n = _
  simp [AdderWidth]
  omega

@[simp] theorem parkedSourceBit_wire_val (n : Nat) (bit : Fin n) :
    (parkedSourceBit n bit).wire.val =
      2 * n + 3 + (n - 1 - bit.val) := by
  change
    (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n)).width +
        (n - 1 - bit.val) = _
  simp [AdderWidth]
  omega

@[simp] theorem carryWorkBit_wire_val (n : Nat)
    (bit : Fin (AdderWidth n - 1)) :
    (carryWorkBit n bit).wire.val = 3 * n + 3 + bit.val := by
  change (dataAndParkedEncoding n).width + bit.val = _
  simp [dataAndParkedEncoding,
    PlainAdder.Schedule.PowerOfTwo.wordEncoding, AdderWidth]
  omega

@[simp] theorem reductionFlagBit_wire_val (n : Nat) :
    (reductionFlagBit n).wire.val = 4 * n + 3 := by
  change (dataParkedWorkEncoding n).width = _
  simp [dataParkedWorkEncoding, dataAndParkedEncoding,
    PlainAdder.Schedule.PowerOfTwo.wordEncoding,
    PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding, AdderWidth]
  omega

/-! ### Canonical `(n+1)`-bit plain-adder lift -/

/-- Full-carrier action of the canonical plain adder, preserving the parked
source and reduction flag. -/
def activeAdderCarrierStep (n : Nat) : RawRegisters n → RawRegisters n :=
  fun x =>
    let y :=
      PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumStep
        (AdderWidth n) (x.1.1.1, x.1.2)
    (((y.1, x.1.1.2), y.2), x.2)

/-- Canonical cleanup-aware adder gates with the source product encoding made
explicit at this lifting boundary. -/
def activeAdderCoreGates (n : Nat) :
    List (EncodedBit.GateSpec
      (BinaryLabelEncoding.prod
        (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))
        (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n)))) :=
  PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumGates (AdderWidth n)

/-- Canonical adder gates after inserting the parked source word. -/
def activeAdderInsertedGates (n : Nat) :
    List (EncodedBit.GateSpec
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod
          (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))
          (PlainAdder.Schedule.PowerOfTwo.wordEncoding n))
        (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n)))) :=
  (activeAdderCoreGates n).map
    (EncodedBit.GateSpec.insertMiddle
      (PlainAdder.Schedule.PowerOfTwo.wordEncoding n))

/-- Canonical adder gates after appending the reduction flag field. -/
def activeAdderCarrierGates (n : Nat) :
    List (EncodedBit.GateSpec
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod
            (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))
            (PlainAdder.Schedule.PowerOfTwo.wordEncoding n))
          (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n)))
        BinaryLabelEncoding.bool)) :=
  (activeAdderInsertedGates n).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)

/-- The canonical adder's primitive gates lifted through the parked source,
carry-work, flag, and named-register layout. -/
def activeAdderGates (n : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  (activeAdderCarrierGates n).map
    (EncodedBit.GateSpec.relabel (registersEquiv n))

private theorem activeAdderCoreGates_step (n : Nat)
    (x : PlainAdder.Data (AdderWidth n) ×
      PlainAdder.Schedule.PowerOfTwo.CarryWork (AdderWidth n)) :
    EncodedBit.GateSpec.stepList (activeAdderCoreGates n) x =
      PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumStep
        (AdderWidth n) x := by
  rfl

private theorem activeAdderCarrierGates_step (n : Nat)
    (x : RawRegisters n) :
    EncodedBit.GateSpec.stepList (activeAdderCarrierGates n) x =
      activeAdderCarrierStep n x := by
  unfold activeAdderCarrierGates
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  unfold activeAdderInsertedGates
  rw [EncodedBit.GateSpec.stepList_insertMiddle]
  unfold activeAdderCarrierStep
  rw [activeAdderCoreGates_step]

/-- Canonical actual circuit for the cleanup-aware plain-adder core. -/
def activeAdderCoreProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (PlainAdder.Schedule.PowerOfTwo.dataWithCarryWorkEncoding
          (AdderWidth n)).width).toQuantum :=
  PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumProgram (AdderWidth n)

/-- Direct realization of the cleanup-aware plain-adder core. -/
theorem activeAdderCore_realizes (n : Nat) :
    UnitaryCircuit.Realizes
      (PlainAdder.Schedule.PowerOfTwo.dataWithCarryWorkEncoding (AdderWidth n))
      (activeAdderCoreProgram n)
      (PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumStep
        (AdderWidth n)) :=
  PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySum_realizes (AdderWidth n)

/-- Forward-adder circuit lifted across parked data and the reduction flag. -/
def activeAdderCarrierProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (rawEncoding n).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeAdderCarrierGates n)

/-- Direct realization of the forward adder on the packed carrier. -/
theorem activeAdderCarrier_realizes (n : Nat) :
    UnitaryCircuit.Realizes (rawEncoding n) (activeAdderCarrierProgram n)
      (activeAdderCarrierStep n) := by
  exact EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty (activeAdderCarrierGates n)
    (activeAdderCarrierGates_step n)

/-- Folded full-register action of the canonical forward plain-adder program. -/
def activeAdderStep (n : Nat) : Registers n → Registers n :=
  fun x =>
    (registersEquiv n).symm
      (activeAdderCarrierStep n (registersEquiv n x))

/-- The lifted gate list has exactly the established full-register adder
semantics. -/
theorem activeAdderStep_eq_gateList (n : Nat) (x : Registers n) :
    EncodedBit.GateSpec.stepList (activeAdderGates n) x =
      activeAdderStep n x := by
  unfold activeAdderGates activeAdderStep
  rw [EncodedBit.GateSpec.stepList_relabel]
  rw [activeAdderCarrierGates_step]

/-- Canonical forward plain-adder program lifted into the exact VBE layout. -/
def activeAdderProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeAdderGates n)

/-- Direct realization of the lifted forward plain adder. -/
theorem activeAdder_realizes (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (activeAdderProgram n)
      (activeAdderStep n) := by
  exact EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty (activeAdderGates n)
    (activeAdderStep_eq_gateList n)

/-- Clean forward endpoint of the lifted canonical plain adder. -/
theorem activeAdderStep_cleanEndpoint (n : Nat) (x : Registers n)
    (hcarry : x.carry = false)
    (hwork : x.carryWork =
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n)) :
    activeAdderStep n x =
      { x with target := x.target + x.activeSource } := by
  have hclean :=
    PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumStep_cleanEndpoint
      (AdderWidth n)
      ({ left := x.activeSource, right := x.target, carry := x.carry } :
        PlainAdder.Data (AdderWidth n)) hcarry
  apply (registersEquiv n).injective
  change
    ((((PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumStep
          (AdderWidth n)
          (({ left := x.activeSource, right := x.target, carry := x.carry } :
              PlainAdder.Data (AdderWidth n)), x.carryWork)).1,
        x.parkedSource),
      (PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumStep
        (AdderWidth n)
        (({ left := x.activeSource, right := x.target, carry := x.carry } :
            PlainAdder.Data (AdderWidth n)), x.carryWork)).2),
      x.reductionFlag) =
    (((({ left := x.activeSource,
          right := x.target + x.activeSource,
          carry := x.carry } : PlainAdder.Data (AdderWidth n)),
        x.parkedSource), x.carryWork), x.reductionFlag)
  rw [hwork, hclean]
  rfl

/-! ### True reverse-program plain adder -/

/-- Folded action of the actual reversed canonical gate list.  This is the
global inverse semantics; it is intentionally not replaced by a clean-only
word-subtraction formula on dirty work states. -/
def adderInverseCoreStep (n : Nat) :
    (PlainAdder.Data (AdderWidth n) ×
      PlainAdder.Schedule.PowerOfTwo.CarryWork (AdderWidth n)) →
    (PlainAdder.Data (AdderWidth n) ×
      PlainAdder.Schedule.PowerOfTwo.CarryWork (AdderWidth n)) :=
  EncodedBit.GateSpec.stepList
    (PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumGates
      (AdderWidth n)).reverse

/-- Actual circuit folded from the reversed canonical plain-adder gate list. -/
def adderInverseCoreProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (PlainAdder.Schedule.PowerOfTwo.dataWithCarryWorkEncoding
          (AdderWidth n)).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumGates
      (AdderWidth n)).reverse

/-- Direct realization of the reversed canonical plain-adder gate list. -/
theorem adderInverseCore_realizes (n : Nat) :
    UnitaryCircuit.Realizes
      (PlainAdder.Schedule.PowerOfTwo.dataWithCarryWorkEncoding (AdderWidth n))
      (adderInverseCoreProgram n) (adderInverseCoreStep n) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumGates
      (AdderWidth n)).reverse

/-- Full-carrier action of the reversed canonical plain-adder program. -/
def activeAdderInverseCarrierStep (n : Nat) :
    RawRegisters n → RawRegisters n :=
  fun x =>
    let y := adderInverseCoreStep n (x.1.1.1, x.1.2)
    (((y.1, x.1.1.2), y.2), x.2)

/-- Reversed cleanup-aware core gates with their canonical product encoding
made explicit. -/
def activeAdderInverseCoreGates (n : Nat) :
    List (EncodedBit.GateSpec
      (BinaryLabelEncoding.prod
        (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))
        (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n)))) :=
  (activeAdderCoreGates n).reverse

/-- Reversed adder gates after inserting the parked source word. -/
def activeAdderInverseInsertedGates (n : Nat) :
    List (EncodedBit.GateSpec
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod
          (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))
          (PlainAdder.Schedule.PowerOfTwo.wordEncoding n))
        (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n)))) :=
  (activeAdderInverseCoreGates n).map
    (EncodedBit.GateSpec.insertMiddle
      (PlainAdder.Schedule.PowerOfTwo.wordEncoding n))

/-- Reversed adder gates after appending the reduction flag field. -/
def activeAdderInverseCarrierGates (n : Nat) :
    List (EncodedBit.GateSpec
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.prod
          (BinaryLabelEncoding.prod
            (PlainAdder.Schedule.PowerOfTwo.dataEncoding (AdderWidth n))
            (PlainAdder.Schedule.PowerOfTwo.wordEncoding n))
          (PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding (AdderWidth n)))
        BinaryLabelEncoding.bool)) :=
  (activeAdderInverseInsertedGates n).map
    (EncodedBit.GateSpec.prodLeft BinaryLabelEncoding.bool)

/-- The reversed canonical adder gate list lifted through the complete VBE
layout. -/
def activeAdderInverseGates (n : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  (activeAdderInverseCarrierGates n).map
    (EncodedBit.GateSpec.relabel (registersEquiv n))

private theorem activeAdderInverseCoreGates_step (n : Nat)
    (x : PlainAdder.Data (AdderWidth n) ×
      PlainAdder.Schedule.PowerOfTwo.CarryWork (AdderWidth n)) :
    EncodedBit.GateSpec.stepList (activeAdderInverseCoreGates n) x =
      adderInverseCoreStep n x := by
  rfl

private theorem activeAdderInverseCarrierGates_step (n : Nat)
    (x : RawRegisters n) :
    EncodedBit.GateSpec.stepList (activeAdderInverseCarrierGates n) x =
      activeAdderInverseCarrierStep n x := by
  unfold activeAdderInverseCarrierGates
  rw [EncodedBit.GateSpec.stepList_prodLeft]
  unfold activeAdderInverseInsertedGates
  rw [EncodedBit.GateSpec.stepList_insertMiddle]
  unfold activeAdderInverseCarrierStep
  rw [activeAdderInverseCoreGates_step]

/-- Inverse-adder circuit lifted across parked data and the reduction flag. -/
def activeAdderInverseCarrierProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (rawEncoding n).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeAdderInverseCarrierGates n)

/-- Direct realization of the inverse adder on the packed carrier. -/
theorem activeAdderInverseCarrier_realizes (n : Nat) :
    UnitaryCircuit.Realizes (rawEncoding n) (activeAdderInverseCarrierProgram n)
      (activeAdderInverseCarrierStep n) := by
  exact EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty (activeAdderInverseCarrierGates n)
    (activeAdderInverseCarrierGates_step n)

/-- Folded full-register action of the reversed canonical program. -/
def activeAdderInverseStep (n : Nat) : Registers n → Registers n :=
  fun x =>
    (registersEquiv n).symm
      (activeAdderInverseCarrierStep n (registersEquiv n x))

/-- The lifted reverse gate list has exactly the established full-register
inverse-adder semantics. -/
theorem activeAdderInverseStep_eq_gateList (n : Nat) (x : Registers n) :
    EncodedBit.GateSpec.stepList (activeAdderInverseGates n) x =
      activeAdderInverseStep n x := by
  unfold activeAdderInverseGates activeAdderInverseStep
  rw [EncodedBit.GateSpec.stepList_relabel]
  rw [activeAdderInverseCarrierGates_step]

/-- Reverse-program canonical plain adder lifted into the VBE layout. -/
def activeAdderInverseProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeAdderInverseGates n)

/-- Direct realization of the lifted reverse plain adder. -/
theorem activeAdderInverse_realizes (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (activeAdderInverseProgram n)
      (activeAdderInverseStep n) := by
  exact EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty (activeAdderInverseGates n)
    (activeAdderInverseStep_eq_gateList n)

theorem adderInverseCoreStep_cleanEndpoint (n : Nat)
    (x : PlainAdder.Data (AdderWidth n))
    (hcarry : x.carry = false) :
    adderInverseCoreStep n
        (x, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n)) =
      (x.subFromRight,
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n)) := by
  let pre := x.subFromRight
  have hpreCarry : pre.carry = false := by
    simpa [pre] using hcarry
  have hforward :=
    PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumStep_cleanEndpoint
      (AdderWidth n) pre hpreCarry
  have hadd : pre.addIntoRight = x := by
    rcases x with ⟨left, right, carry⟩
    simp [pre, PlainAdder.Data.subFromRight, PlainAdder.Data.addIntoRight]
  have hinverse :=
    EncodedBit.GateSpec.stepList_reverse_stepList
      (PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumGates
        (AdderWidth n))
      (pre, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n))
  change
    adderInverseCoreStep n
      (PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumStep
        (AdderWidth n)
        (pre, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n))) =
      (pre, PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n)) at hinverse
  rw [hforward, hadd] at hinverse
  simpa [pre] using hinverse

/-- Clean reverse endpoint of the lifted canonical plain adder. -/
theorem activeAdderInverseStep_cleanEndpoint (n : Nat) (x : Registers n)
    (hcarry : x.carry = false)
    (hwork : x.carryWork =
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n)) :
    activeAdderInverseStep n x =
      { x with target := x.target - x.activeSource } := by
  have hclean := adderInverseCoreStep_cleanEndpoint n
    ({ left := x.activeSource, right := x.target, carry := x.carry } :
      PlainAdder.Data (AdderWidth n)) hcarry
  apply (registersEquiv n).injective
  change
    ((((adderInverseCoreStep n
          (({ left := x.activeSource, right := x.target, carry := x.carry } :
              PlainAdder.Data (AdderWidth n)), x.carryWork)).1,
        x.parkedSource),
      (adderInverseCoreStep n
        (({ left := x.activeSource, right := x.target, carry := x.carry } :
            PlainAdder.Data (AdderWidth n)), x.carryWork)).2),
      x.reductionFlag) =
    (((({ left := x.activeSource,
          right := x.target - x.activeSource,
          carry := x.carry } : PlainAdder.Data (AdderWidth n)),
        x.parkedSource), x.carryWork), x.reductionFlag)
  rw [hwork, hclean]
  rfl

/-! ### Source/modulus word swap -/

theorem activeSourceLow_parked_diagonal_ne (n : Nat) :
    ∀ i,
      ((activeSourceLowWord n).bit i).wire ≠
        ((parkedSourceWord n).bit i).wire := by
  intro i h
  have hv := congrArg Fin.val h
  simp [activeSourceLowWord, activeSourceLowBit, parkedSourceWord] at hv
  omega

theorem activeSourceLow_pairwise_ne (n : Nat) :
    ∀ i j, i ≠ j →
      ((activeSourceLowWord n).bit i).wire ≠
        ((activeSourceLowWord n).bit j).wire := by
  intro i j hij h
  have hv := congrArg Fin.val h
  simp [activeSourceLowWord, activeSourceLowBit] at hv
  apply hij
  apply Fin.ext
  omega

theorem parkedSource_pairwise_ne (n : Nat) :
    ∀ i j, i ≠ j →
      ((parkedSourceWord n).bit i).wire ≠
        ((parkedSourceWord n).bit j).wire := by
  intro i j hij h
  have hv := congrArg Fin.val h
  simp [parkedSourceWord] at hv
  apply hij
  apply Fin.ext
  omega

theorem activeSourceLow_parked_cross_ne (n : Nat) :
    ∀ i j,
      ((activeSourceLowWord n).bit i).wire ≠
        ((parkedSourceWord n).bit j).wire := by
  intro i j h
  have hv := congrArg Fin.val h
  simp [activeSourceLowWord, activeSourceLowBit, parkedSourceWord] at hv
  omega

theorem activeSourceLow_target_ne (n : Nat) (i : Fin n)
    (j : Fin (AdderWidth n)) :
    (activeSourceLowBit n i).wire ≠ (targetBit n j).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [activeSourceLowBit_wire_val, targetBit_wire_val] at hv
  have hi := i.isLt
  have hj : j.val < n + 1 := by simpa [AdderWidth] using j.isLt
  omega

theorem parkedSource_target_ne (n : Nat) (i : Fin n)
    (j : Fin (AdderWidth n)) :
    (parkedSourceBit n i).wire ≠ (targetBit n j).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [parkedSourceBit_wire_val, targetBit_wire_val] at hv
  have hi := i.isLt
  have hj : j.val < n + 1 := by simpa [AdderWidth] using j.isLt
  omega

theorem activeSourceLow_carry_ne (n : Nat) (i : Fin n) :
    (activeSourceLowBit n i).wire ≠ (carryBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [activeSourceLowBit_wire_val, carryBit_wire_val] at hv
  have hi := i.isLt
  omega

theorem parkedSource_carry_ne (n : Nat) (i : Fin n) :
    (parkedSourceBit n i).wire ≠ (carryBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [parkedSourceBit_wire_val, carryBit_wire_val] at hv
  have hi := i.isLt
  omega

theorem activeSourceLow_carryWork_ne (n : Nat) (i : Fin n)
    (j : Fin (AdderWidth n - 1)) :
    (activeSourceLowBit n i).wire ≠ (carryWorkBit n j).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [activeSourceLowBit_wire_val, carryWorkBit_wire_val] at hv
  have hi := i.isLt
  omega

theorem parkedSource_carryWork_ne (n : Nat) (i : Fin n)
    (j : Fin (AdderWidth n - 1)) :
    (parkedSourceBit n i).wire ≠ (carryWorkBit n j).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [parkedSourceBit_wire_val, carryWorkBit_wire_val] at hv
  have hi := i.isLt
  omega

theorem activeSourceLow_reductionFlag_ne (n : Nat) (i : Fin n) :
    (activeSourceLowBit n i).wire ≠ (reductionFlagBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [activeSourceLowBit_wire_val, reductionFlagBit_wire_val] at hv
  have hi := i.isLt
  omega

theorem parkedSource_reductionFlag_ne (n : Nat) (i : Fin n) :
    (parkedSourceBit n i).wire ≠ (reductionFlagBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [parkedSourceBit_wire_val, reductionFlagBit_wire_val] at hv
  have hi := i.isLt
  omega

theorem activeSourceLow_activeSourceHigh_ne (n : Nat) (i : Fin n) :
    (activeSourceLowBit n i).wire ≠ (activeSourceHighBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [activeSourceLowBit_wire_val, activeSourceHighBit_wire_val] at hv
  have hi := i.isLt
  omega

theorem parkedSource_activeSourceHigh_ne (n : Nat) (i : Fin n) :
    (parkedSourceBit n i).wire ≠ (activeSourceHighBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [parkedSourceBit_wire_val, activeSourceHighBit_wire_val] at hv
  have hi := i.isLt
  omega

/-- Three-CNOT-per-bit swap of the active low word and parked source word. -/
def sourceSwapProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  EncodedBit.Word.swapProgram (QubitLayout.canonical _) .empty
    (activeSourceLowWord n) (parkedSourceWord n)
    (activeSourceLow_parked_diagonal_ne n)

/-- Folded semantic action of the exact source-swap program. -/
def sourceSwapStep (n : Nat) : Registers n → Registers n :=
  EncodedBit.Word.swapStep
    (activeSourceLowWord n) (parkedSourceWord n)
    (activeSourceLow_parked_diagonal_ne n)

theorem sourceSwap_realizes (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (sourceSwapProgram n)
      (sourceSwapStep n) :=
  EncodedBit.Word.swap_realizes (QubitLayout.canonical _) .empty
    (activeSourceLowWord n) (parkedSourceWord n)
    (activeSourceLow_parked_diagonal_ne n)

theorem sourceSwapStep_get_activeSourceLow (n : Nat) (bit : Fin n)
    (x : Registers n) :
    (activeSourceLowBit n bit).get (sourceSwapStep n x) =
      (parkedSourceBit n bit).get x := by
  have h :=
    EncodedBit.Word.swapStep_get_left_word
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n)
      (activeSourceLow_pairwise_ne n)
      (parkedSource_pairwise_ne n)
      (activeSourceLow_parked_cross_ne n) x
  simpa [sourceSwapStep, activeSourceLowWord, parkedSourceWord] using
    congrFun h bit

theorem sourceSwapStep_get_parkedSource (n : Nat) (bit : Fin n)
    (x : Registers n) :
    (parkedSourceBit n bit).get (sourceSwapStep n x) =
      (activeSourceLowBit n bit).get x := by
  have h :=
    EncodedBit.Word.swapStep_get_right_word
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n)
      (activeSourceLow_pairwise_ne n)
      (parkedSource_pairwise_ne n)
      (activeSourceLow_parked_cross_ne n) x
  simpa [sourceSwapStep, activeSourceLowWord, parkedSourceWord] using
    congrFun h bit

theorem sourceSwapStep_get_activeSourceHigh (n : Nat) (x : Registers n) :
    (activeSourceHighBit n).get (sourceSwapStep n x) =
      (activeSourceHighBit n).get x := by
  simpa [sourceSwapStep] using
    EncodedBit.Word.swapStep_get_observed_of_swap_ne
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n) (activeSourceHighBit n)
      (activeSourceLow_activeSourceHigh_ne n)
      (parkedSource_activeSourceHigh_ne n) x

theorem sourceSwapStep_get_target (n : Nat) (bit : Fin (AdderWidth n))
    (x : Registers n) :
    (targetBit n bit).get (sourceSwapStep n x) =
      (targetBit n bit).get x := by
  simpa [sourceSwapStep] using
    EncodedBit.Word.swapStep_get_observed_of_swap_ne
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n) (targetBit n bit)
      (fun i => activeSourceLow_target_ne n i bit)
      (fun i => parkedSource_target_ne n i bit) x

theorem sourceSwapStep_get_carry (n : Nat) (x : Registers n) :
    (carryBit n).get (sourceSwapStep n x) = (carryBit n).get x := by
  simpa [sourceSwapStep] using
    EncodedBit.Word.swapStep_get_observed_of_swap_ne
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n) (carryBit n)
      (activeSourceLow_carry_ne n) (parkedSource_carry_ne n) x

theorem sourceSwapStep_get_carryWork (n : Nat)
    (bit : Fin (AdderWidth n - 1)) (x : Registers n) :
    (carryWorkBit n bit).get (sourceSwapStep n x) =
      (carryWorkBit n bit).get x := by
  simpa [sourceSwapStep] using
    EncodedBit.Word.swapStep_get_observed_of_swap_ne
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n) (carryWorkBit n bit)
      (fun i => activeSourceLow_carryWork_ne n i bit)
      (fun i => parkedSource_carryWork_ne n i bit) x

theorem sourceSwapStep_get_reductionFlag (n : Nat) (x : Registers n) :
    (reductionFlagBit n).get (sourceSwapStep n x) =
      (reductionFlagBit n).get x := by
  simpa [sourceSwapStep] using
    EncodedBit.Word.swapStep_get_observed_of_swap_ne
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n) (reductionFlagBit n)
      (activeSourceLow_reductionFlag_ne n)
      (parkedSource_reductionFlag_ne n) x

/-- Embed an `n`-bit source/modulus word into the low bits of the canonical
`(n+1)`-bit adder source. -/
def widenWord (n : Nat) (x : PlainAdder.Word n) :
    PlainAdder.Word (AdderWidth n) :=
  (x.val : PlainAdder.Word (AdderWidth n))

@[simp] theorem widenWord_val (n : Nat) (x : PlainAdder.Word n) :
    (widenWord n x).val = x.val := by
  unfold widenWord
  apply ZMod.val_natCast_of_lt
  have hx := ZMod.val_lt x
  have hp := Nat.two_pow_pos n
  rw [show AdderWidth n = n + 1 by rfl, pow_succ]
  omega

/-- Canonical clean source-swap state.  The target and reduction flag remain
arbitrary so the same endpoint applies to both swaps in the VBE ledger. -/
def sourceSwapCleanState (n : Nat) (active parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) : Registers n where
  activeSource := widenWord n active
  target := target
  carry := false
  parkedSource := parked
  carryWork := PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n)
  reductionFlag := flag

/-- On canonical clean VBE states, the concrete three-CNOT word network
exchanges active and parked source values and preserves every other field. -/
theorem sourceSwapStep_cleanEndpoint (n : Nat)
    (active parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    sourceSwapStep n (sourceSwapCleanState n active parked target flag) =
      sourceSwapCleanState n parked active target flag := by
  let input := sourceSwapCleanState n active parked target flag
  have hactive :
      (sourceSwapStep n input).activeSource = widenWord n parked := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    by_cases hlow : bit.val < n
    · let low : Fin n := ⟨bit.val, hlow⟩
      have hbit :
          bit = (⟨low.val, by simp [AdderWidth]⟩ : Fin (AdderWidth n)) := by
        apply Fin.ext
        rfl
      rw [hbit]
      have hread := sourceSwapStep_get_activeSourceLow n low input
      simpa [input, sourceSwapCleanState] using hread
    · have hlast : bit = (Fin.last n : Fin (AdderWidth n)) := by
        apply Fin.ext
        have hbitLt := bit.isLt
        simp [AdderWidth] at hbitLt
        simp
        omega
      rw [hlast]
      have hread := sourceSwapStep_get_activeSourceHigh n input
      have hactiveHigh : active.val.testBit n = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt active)
      have hparkedHigh : parked.val.testBit n = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt parked)
      simpa [input, sourceSwapCleanState, hactiveHigh, hparkedHigh] using hread
  have htarget : (sourceSwapStep n input).target = target := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread := sourceSwapStep_get_target n bit input
    simpa [input, sourceSwapCleanState] using hread
  have hcarry : (sourceSwapStep n input).carry = false := by
    have hread := sourceSwapStep_get_carry n input
    simpa [input, sourceSwapCleanState] using hread
  have hparked : (sourceSwapStep n input).parkedSource = active := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread := sourceSwapStep_get_parkedSource n bit input
    simpa [input, sourceSwapCleanState] using hread
  have hwork :
      (sourceSwapStep n input).carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n) := by
    change (sourceSwapStep n input).carryWork = 0
    apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    rw [← carryWorkBit_get n bit (sourceSwapStep n input)]
    rw [sourceSwapStep_get_carryWork n bit input]
    rw [carryWorkBit_get]
    simp [input, sourceSwapCleanState,
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork]
  have hflag : (sourceSwapStep n input).reductionFlag = flag := by
    have hread := sourceSwapStep_get_reductionFlag n input
    simpa [input, sourceSwapCleanState] using hread
  change sourceSwapStep n input = sourceSwapCleanState n parked active target flag
  apply (registersEquiv n).injective
  simp [registersEquiv, sourceSwapCleanState, hactive, htarget, hcarry,
    hparked, hwork, hflag]

/-- Forward-adder action specialized to the canonical clean VBE layout. -/
theorem activeAdderStep_sourceSwapCleanState (n : Nat)
    (active parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    activeAdderStep n (sourceSwapCleanState n active parked target flag) =
      sourceSwapCleanState n active parked
        (target + widenWord n active) flag := by
  rw [activeAdderStep_cleanEndpoint]
  · rfl
  · rfl
  · rfl

/-- Reverse-adder action specialized to the canonical clean VBE layout. -/
theorem activeAdderInverseStep_sourceSwapCleanState (n : Nat)
    (active parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    activeAdderInverseStep n
        (sourceSwapCleanState n active parked target flag) =
      sourceSwapCleanState n active parked
        (target - widenWord n active) flag := by
  rw [activeAdderInverseStep_cleanEndpoint]
  · rfl
  · rfl
  · rfl

/-! ### Overflow flag and conditional modulus clear/restore -/

/-- Most-significant target bit containing the subtraction underflow probe. -/
def targetOverflowBit (n : Nat) : EncodedBit (encoding n) :=
  targetBit n (Fin.last n)

theorem targetOverflow_reductionFlag_ne (n : Nat) :
    (targetOverflowBit n).wire ≠ (reductionFlagBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp [targetOverflowBit, AdderWidth] at hv
  omega

theorem activeSource_pairwise_ne (n : Nat) :
    ∀ i j, i ≠ j →
      ((activeSourceWord n).bit i).wire ≠
        ((activeSourceWord n).bit j).wire := by
  intro i j hij h
  have hv := congrArg Fin.val h
  change
    AdderWidth n - 1 - i.val = AdderWidth n - 1 - j.val at hv
  simp [AdderWidth] at hv
  apply hij
  apply Fin.ext
  have hi : i.val < n + 1 := by
    simpa [AdderWidth] using i.isLt
  have hj : j.val < n + 1 := by
    simpa [AdderWidth] using j.isLt
  omega

theorem reductionFlag_activeSource_ne (n : Nat) :
    ∀ i,
      (reductionFlagBit n).wire ≠ ((activeSourceWord n).bit i).wire := by
  intro i h
  have hv := congrArg Fin.val h
  simp [activeSourceWord] at hv
  omega

theorem activeSource_target_ne (n : Nat) (i j : Fin (AdderWidth n)) :
    ((activeSourceWord n).bit i).wire ≠ (targetBit n j).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [activeSourceWord, activeSourceBit_wire_val,
    targetBit_wire_val] at hv
  have hi : i.val < n + 1 := by simpa [AdderWidth] using i.isLt
  have hj : j.val < n + 1 := by simpa [AdderWidth] using j.isLt
  omega

theorem activeSource_carry_ne (n : Nat) (i : Fin (AdderWidth n)) :
    ((activeSourceWord n).bit i).wire ≠ (carryBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [activeSourceWord, activeSourceBit_wire_val,
    carryBit_wire_val] at hv
  have hi : i.val < n + 1 := by simpa [AdderWidth] using i.isLt
  omega

theorem activeSource_parked_ne (n : Nat) (i : Fin (AdderWidth n))
    (j : Fin n) :
    ((activeSourceWord n).bit i).wire ≠ (parkedSourceBit n j).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [activeSourceWord, activeSourceBit_wire_val,
    parkedSourceBit_wire_val] at hv
  have hi : i.val < n + 1 := by simpa [AdderWidth] using i.isLt
  have hj := j.isLt
  omega

theorem activeSource_carryWork_ne (n : Nat) (i : Fin (AdderWidth n))
    (j : Fin (AdderWidth n - 1)) :
    ((activeSourceWord n).bit i).wire ≠ (carryWorkBit n j).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp only [activeSourceWord, activeSourceBit_wire_val,
    carryWorkBit_wire_val] at hv
  have hi : i.val < n + 1 := by simpa [AdderWidth] using i.isLt
  omega

/-- X the clean flag, then xor the subtraction MSB into it.  On a clean input
this stores the complement of underflow, namely `decide (N ≤ a+b)`. -/
def copyReductionFlagGates (n : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  [ .x (reductionFlagBit n),
    .cnot (targetOverflowBit n) (reductionFlagBit n)
      (targetOverflow_reductionFlag_ne n) ]

/-- Base-gate program that records the modular-reduction decision. -/
def copyReductionFlagProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (copyReductionFlagGates n)

/-- Folded register action of the reduction-flag copy program. -/
def copyReductionFlagStep (n : Nat) : Registers n → Registers n :=
  EncodedBit.GateSpec.stepList (copyReductionFlagGates n)

theorem copyReductionFlag_realizes (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (copyReductionFlagProgram n)
      (copyReductionFlagStep n) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (copyReductionFlagGates n)

@[simp] theorem reductionFlagBit_flip (n : Nat) (x : Registers n) :
    (reductionFlagBit n).flip x =
      { x with reductionFlag := !x.reductionFlag } := by
  rcases x with ⟨activeSource, target, carry, parkedSource, carryWork,
    reductionFlag⟩
  rfl

@[simp] theorem targetOverflowBit_get (n : Nat) (x : Registers n) :
    (targetOverflowBit n).get x = x.target.val.testBit n := by
  simp [targetOverflowBit, AdderWidth]

/-- Exact record action of the X/CNOT overflow-copy pair. -/
theorem copyReductionFlagStep_eq (n : Nat) (x : Registers n) :
    copyReductionFlagStep n x =
      { x with reductionFlag :=
          (!x.reductionFlag) ^^ x.target.val.testBit n } := by
  rcases x with ⟨activeSource, target, carry, parkedSource, carryWork,
    reductionFlag⟩
  by_cases htarget : target.val.testBit n <;>
    cases reductionFlag <;>
    simp [copyReductionFlagStep, copyReductionFlagGates,
      EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
      EncodedBit.cnotStep, htarget]

theorem copyReductionFlagStep_sourceSwapCleanState (n : Nat)
    (active parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    copyReductionFlagStep n
        (sourceSwapCleanState n active parked target flag) =
      sourceSwapCleanState n active parked target
        ((!flag) ^^ target.val.testBit n) := by
  rw [copyReductionFlagStep_eq]
  rfl

/-- Final CNOT that removes the stored reduction flag after the cleanup probe. -/
def cleanupReductionFlagProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  EncodedBit.GateSpec.program
    (.cnot (targetOverflowBit n) (reductionFlagBit n)
      (targetOverflow_reductionFlag_ne n))
    (QubitLayout.canonical _) .empty

/-- Folded register action of the final reduction-flag cleanup CNOT. -/
def cleanupReductionFlagStep (n : Nat) : Registers n → Registers n :=
  EncodedBit.GateSpec.step
    (.cnot (targetOverflowBit n) (reductionFlagBit n)
      (targetOverflow_reductionFlag_ne n))

theorem cleanupReductionFlag_realizes (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (cleanupReductionFlagProgram n)
      (cleanupReductionFlagStep n) :=
  EncodedBit.GateSpec.realizes (QubitLayout.canonical _) .empty
    (.cnot (targetOverflowBit n) (reductionFlagBit n)
      (targetOverflow_reductionFlag_ne n))

/-- Exact record action of the final overflow-cleanup CNOT. -/
theorem cleanupReductionFlagStep_eq (n : Nat) (x : Registers n) :
    cleanupReductionFlagStep n x =
      { x with reductionFlag :=
          x.reductionFlag ^^ x.target.val.testBit n } := by
  rcases x with ⟨activeSource, target, carry, parkedSource, carryWork,
    reductionFlag⟩
  by_cases htarget : target.val.testBit n <;>
    cases reductionFlag <;>
    simp [cleanupReductionFlagStep, EncodedBit.GateSpec.step,
      EncodedBit.cnotStep, htarget]

theorem cleanupReductionFlagStep_sourceSwapCleanState (n : Nat)
    (active parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    cleanupReductionFlagStep n
        (sourceSwapCleanState n active parked target flag) =
      sourceSwapCleanState n active parked target
        (flag ^^ target.val.testBit n) := by
  rw [cleanupReductionFlagStep_eq]
  rfl

/-- Fixed-width encoded label of the widened modulus word. -/
def modulusWordLabel (n N : Nat) : Fin (2 ^ AdderWidth n) :=
  PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv (AdderWidth n)
    (widenWord n (N : PlainAdder.Word n))

/-- Clear the active modulus word iff the stored reduction flag is set. -/
def clearActiveModulusProgram (n N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  EncodedBit.Word.controlledXorConstantProgram (QubitLayout.canonical _) .empty
    (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
    (reductionFlag_activeSource_ne n)

/-- Folded action that conditionally clears the active modulus word. -/
def clearActiveModulusStep (n N : Nat) : Registers n → Registers n :=
  EncodedBit.Word.controlledXorConstantStep
    (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
    (reductionFlag_activeSource_ne n)

theorem clearActiveModulus_realizes (n N : Nat) :
    UnitaryCircuit.Realizes (encoding n) (clearActiveModulusProgram n N)
      (clearActiveModulusStep n N) :=
  EncodedBit.Word.controlledXorConstant_realizes (QubitLayout.canonical _) .empty
    (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
    (reductionFlag_activeSource_ne n)

theorem modulusWordLabel_testBit (n N : Nat) (bit : Fin (AdderWidth n)) :
    (modulusWordLabel n N).val.testBit bit.val =
      (widenWord n (N : PlainAdder.Word n)).val.testBit bit.val := by
  unfold modulusWordLabel
  rw [← PlainAdder.Schedule.PowerOfTwo.wordBit_get]
  simp [PlainAdder.Schedule.PowerOfTwo.wordBit,
    BinaryLabelEncoding.ofEquivBit]

/-- On a canonical clean state whose active source holds `N`, the controlled
constant load clears that word exactly when the reduction flag is true. -/
theorem clearActiveModulusStep_cleanEndpoint (n N : Nat)
    (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    clearActiveModulusStep n N
        (sourceSwapCleanState n (N : PlainAdder.Word n) parked target flag) =
      sourceSwapCleanState n
        (if flag then 0 else (N : PlainAdder.Word n)) parked target flag := by
  let input :=
    sourceSwapCleanState n (N : PlainAdder.Word n) parked target flag
  have hactive :
      (clearActiveModulusStep n N input).activeSource =
        widenWord n (if flag then 0 else (N : PlainAdder.Word n)) := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_target
        (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
        (reductionFlag_activeSource_ne n) bit
        (fun other hother => activeSource_pairwise_ne n other bit hother)
        input
    have hconstant := modulusWordLabel_testBit n N bit
    cases flag <;>
      cases hbit :
        (widenWord n (N : PlainAdder.Word n)).val.testBit bit.val <;>
      simpa [clearActiveModulusStep, input, sourceSwapCleanState,
        activeSourceWord, hconstant, hbit] using hread
  have htarget : (clearActiveModulusStep n N input).target = target := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
        (reductionFlag_activeSource_ne n) (targetBit n bit)
        (fun i => activeSource_target_ne n i bit) input
    simpa [clearActiveModulusStep, input, sourceSwapCleanState] using hread
  have hcarry : (clearActiveModulusStep n N input).carry = false := by
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
        (reductionFlag_activeSource_ne n) (carryBit n)
        (activeSource_carry_ne n) input
    simpa [clearActiveModulusStep, input, sourceSwapCleanState] using hread
  have hparked : (clearActiveModulusStep n N input).parkedSource = parked := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
        (reductionFlag_activeSource_ne n) (parkedSourceBit n bit)
        (fun i => activeSource_parked_ne n i bit) input
    simpa [clearActiveModulusStep, input, sourceSwapCleanState] using hread
  have hwork :
      (clearActiveModulusStep n N input).carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n) := by
    change (clearActiveModulusStep n N input).carryWork = 0
    apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    rw [← carryWorkBit_get n bit (clearActiveModulusStep n N input)]
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
        (reductionFlag_activeSource_ne n) (carryWorkBit n bit)
        (fun i => activeSource_carryWork_ne n i bit) input
    have hread' :
        (carryWorkBit n bit).get (clearActiveModulusStep n N input) =
          (carryWorkBit n bit).get input := by
      simpa [clearActiveModulusStep] using hread
    rw [hread', carryWorkBit_get]
    simp [input, sourceSwapCleanState,
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork]
  have hflag : (clearActiveModulusStep n N input).reductionFlag = flag := by
    have hread :=
      EncodedBit.Word.controlledXorConstantStep_get_observed_of_target_ne
        (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
        (reductionFlag_activeSource_ne n) (reductionFlagBit n)
        (fun i => Ne.symm (reductionFlag_activeSource_ne n i)) input
    simpa [clearActiveModulusStep, input, sourceSwapCleanState] using hread
  change clearActiveModulusStep n N input =
    sourceSwapCleanState n
      (if flag then 0 else (N : PlainAdder.Word n)) parked target flag
  apply (registersEquiv n).injective
  simp [registersEquiv, sourceSwapCleanState, hactive, htarget, hcarry,
    hparked, hwork, hflag]

/-- Reverse-list unload restoring the active modulus after the add-back stage. -/
def restoreActiveModulusProgram (n N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  EncodedBit.Word.controlledXorConstantUnloadProgram
    (QubitLayout.canonical _) .empty
    (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
    (reductionFlag_activeSource_ne n)

/-- Folded reverse-list action that restores the active modulus word. -/
def restoreActiveModulusStep (n N : Nat) : Registers n → Registers n :=
  EncodedBit.Word.controlledXorConstantUnloadStep
    (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
    (reductionFlag_activeSource_ne n)

theorem restoreActiveModulus_realizes (n N : Nat) :
    UnitaryCircuit.Realizes (encoding n) (restoreActiveModulusProgram n N)
      (restoreActiveModulusStep n N) :=
  EncodedBit.Word.controlledXorConstantUnload_realizes
    (QubitLayout.canonical _) .empty
    (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
    (reductionFlag_activeSource_ne n)

/-- The reverse constant-xor stage restores the active modulus exactly after
the matching clear stage, including the branch where the flag is false. -/
theorem restoreActiveModulusStep_cleanEndpoint (n N : Nat)
    (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    restoreActiveModulusStep n N
        (sourceSwapCleanState n
          (if flag then 0 else (N : PlainAdder.Word n)) parked target flag) =
      sourceSwapCleanState n (N : PlainAdder.Word n) parked target flag := by
  let original :=
    sourceSwapCleanState n (N : PlainAdder.Word n) parked target flag
  have hclear :=
    clearActiveModulusStep_cleanEndpoint n N parked target flag
  have hinverse :=
    EncodedBit.Word.controlledXorConstantUnloadStep_after_controlledXorConstantStep
      (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
      (reductionFlag_activeSource_ne n) original
  change restoreActiveModulusStep n N
      (clearActiveModulusStep n N original) = original at hinverse
  rw [hclear] at hinverse
  simpa [original] using hinverse

/-! ### Source-faithful modular-add stage ledger -/

/-- Exact three-CNOT source-routing gates used by each swap stage. -/
def sourceSwapGates (n : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  EncodedBit.Word.swapGates
    (activeSourceLowWord n) (parkedSourceWord n)
    (activeSourceLow_parked_diagonal_ne n)

/-- Exact controlled-XOR gates that conditionally clear the active modulus. -/
def clearActiveModulusGates (n N : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  EncodedBit.Word.controlledXorConstantGates
    (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
    (reductionFlag_activeSource_ne n)

/-- Reverse controlled-XOR gate list that restores the active modulus. -/
def restoreActiveModulusGates (n N : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  (clearActiveModulusGates n N).reverse

/-- The final CNOT that cleans the reduction flag, represented as a list so
the complete modular-adder schedule can be flattened without recompilation. -/
def cleanupReductionFlagGates (n : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  [.cnot (targetOverflowBit n) (reductionFlagBit n)
    (targetOverflow_reductionFlag_ne n)]

/-- Complete eleven-stage VBE modular-add gate list in execution order. -/
def modularAddGates (n N : Nat) :
    List (EncodedBit.GateSpec (encoding n)) :=
  activeAdderGates n ++
    sourceSwapGates n ++
    activeAdderInverseGates n ++
    copyReductionFlagGates n ++
    clearActiveModulusGates n N ++
    activeAdderGates n ++
    restoreActiveModulusGates n N ++
    sourceSwapGates n ++
    activeAdderInverseGates n ++
    cleanupReductionFlagGates n ++
    activeAdderGates n

/-- The eleven concrete VBE programs, in the order in which they act.  This is
the single source of truth for both the semantic fold and the circuit ledger. -/
def modularAddPrograms (n N : Nat) :
    List (UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum) :=
  [ activeAdderProgram n,
    sourceSwapProgram n,
    activeAdderInverseProgram n,
    copyReductionFlagProgram n,
    clearActiveModulusProgram n N,
    activeAdderProgram n,
    restoreActiveModulusProgram n N,
    sourceSwapProgram n,
    activeAdderInverseProgram n,
    cleanupReductionFlagProgram n,
    activeAdderProgram n ]

/-- Semantic steps paired one-for-one with `modularAddPrograms`. -/
def modularAddSteps (n N : Nat) : List (Registers n → Registers n) :=
  [ activeAdderStep n,
    sourceSwapStep n,
    activeAdderInverseStep n,
    copyReductionFlagStep n,
    clearActiveModulusStep n N,
    activeAdderStep n,
    restoreActiveModulusStep n N,
    sourceSwapStep n,
    activeAdderInverseStep n,
    cleanupReductionFlagStep n,
    activeAdderStep n ]

theorem modularAddStages_realize (n N : Nat) :
    List.Forall₂
      (fun program step => UnitaryCircuit.Realizes (encoding n) program step)
      (modularAddPrograms n N) (modularAddSteps n N) := by
  unfold modularAddPrograms modularAddSteps
  exact .cons (activeAdder_realizes n) <|
    .cons (sourceSwap_realizes n) <|
    .cons (activeAdderInverse_realizes n) <|
    .cons (copyReductionFlag_realizes n) <|
    .cons (clearActiveModulus_realizes n N) <|
    .cons (activeAdder_realizes n) <|
    .cons (restoreActiveModulus_realizes n N) <|
    .cons (sourceSwap_realizes n) <|
    .cons (activeAdderInverse_realizes n) <|
    .cons (cleanupReductionFlag_realizes n) <|
    .cons (activeAdder_realizes n) .nil

/-- Folded semantics of the exact eleven-stage VBE gate program. -/
def modularAddStep (n N : Nat) : Registers n → Registers n :=
  UnitaryCircuit.Realizes.stepList (modularAddSteps n N)

/-- The flattened primitive list agrees pointwise with the established
eleven-stage modular-add semantics. -/
theorem modularAddStep_eq_gateList (n N : Nat) (x : Registers n) :
    EncodedBit.GateSpec.stepList (modularAddGates n N) x =
      modularAddStep n N x := by
  simp only [modularAddGates, EncodedBit.GateSpec.stepList_append]
  rw [activeAdderStep_eq_gateList, activeAdderInverseStep_eq_gateList,
    activeAdderStep_eq_gateList, activeAdderInverseStep_eq_gateList,
    activeAdderStep_eq_gateList]
  rfl

/-- Exact concatenated X/CNOT/Toffoli program for general modular addition. -/
def modularAddProgram (n N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (modularAddGates n N)























private theorem activeAdderGates_length_eq_carrier (n : Nat) :
    (activeAdderGates n).length =
      (activeAdderCarrierGates n).length := by
  simp only [activeAdderGates, List.length_map]

private theorem activeAdderCarrierGates_length_eq_inserted (n : Nat) :
    (activeAdderCarrierGates n).length =
      (activeAdderInsertedGates n).length := by
  simp only [activeAdderCarrierGates, List.length_map]

private theorem activeAdderInsertedGates_length_eq_core (n : Nat) :
    (activeAdderInsertedGates n).length =
      (activeAdderCoreGates n).length := by
  simp only [activeAdderInsertedGates, List.length_map]

private theorem activeAdderCoreGates_length_eq_schedule (n : Nat) :
    (activeAdderCoreGates n).length =
      (PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumGates
        (AdderWidth n)).length := by
  rfl

private theorem activeAdderInverseGates_length_eq_carrier (n : Nat) :
    (activeAdderInverseGates n).length =
      (activeAdderInverseCarrierGates n).length := by
  simp only [activeAdderInverseGates, List.length_map]

private theorem activeAdderInverseCarrierGates_length_eq_inserted (n : Nat) :
    (activeAdderInverseCarrierGates n).length =
      (activeAdderInverseInsertedGates n).length := by
  simp only [activeAdderInverseCarrierGates, List.length_map]

private theorem activeAdderInverseInsertedGates_length_eq_core (n : Nat) :
    (activeAdderInverseInsertedGates n).length =
      (activeAdderInverseCoreGates n).length := by
  simp only [activeAdderInverseInsertedGates, List.length_map]

private theorem activeAdderInverseCoreGates_length_eq_core_reverse (n : Nat) :
    (activeAdderInverseCoreGates n).length =
      (activeAdderCoreGates n).reverse.length := by
  rfl

private theorem activeAdderCoreGates_reverse_length_eq_schedule (n : Nat) :
    (activeAdderCoreGates n).reverse.length =
      (PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumGates
        (AdderWidth n)).reverse.length := by
  rfl

/-! ### Strict-event size bound -/

/-- The flattened eleven-stage schedule has a linear leaf bound derived
directly from its gate lists. -/
theorem modularAddGates_length_le (n N : Nat) :
    (modularAddGates n N).length ≤ 48 * n + 45 := by
  have hadd : (activeAdderGates n).length ≤ 8 * (n + 1) := by
    rw [activeAdderGates_length_eq_carrier,
      activeAdderCarrierGates_length_eq_inserted,
      activeAdderInsertedGates_length_eq_core,
      activeAdderCoreGates_length_eq_schedule]
    simpa only [AdderWidth,
      PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumGates] using
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length_le
        (PlainAdder.Schedule.PowerOfTwo.carryWorkLayout (AdderWidth n))
  have hinverse :
      (activeAdderInverseGates n).length ≤ 8 * (n + 1) := by
    rw [activeAdderInverseGates_length_eq_carrier,
      activeAdderInverseCarrierGates_length_eq_inserted,
      activeAdderInverseInsertedGates_length_eq_core,
      activeAdderInverseCoreGates_length_eq_core_reverse,
      List.length_reverse,
      activeAdderCoreGates_length_eq_schedule]
    simpa only [AdderWidth,
      PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumGates] using
      PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_length_le
        (PlainAdder.Schedule.PowerOfTwo.carryWorkLayout (AdderWidth n))
  have hswap : (sourceSwapGates n).length = 3 * n := by
    exact EncodedBit.Word.swapGates_length
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n)
  have hcopy : (copyReductionFlagGates n).length = 2 := rfl
  have hclear : (clearActiveModulusGates n N).length ≤ n + 1 := by
    exact EncodedBit.Word.controlledXorConstantGates_length_le_width
      (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
      (reductionFlag_activeSource_ne n)
  have hrestore : (restoreActiveModulusGates n N).length ≤ n + 1 := by
    simpa only [restoreActiveModulusGates, List.length_reverse] using hclear
  have hcleanup : (cleanupReductionFlagGates n).length = 1 := rfl
  simp only [modularAddGates, List.length_append]
  omega

private theorem activeAdderGates_events_eq_core (n : Nat) :
    (activeAdderGates n).map (EncodedBit.GateSpec.event .empty) =
      (activeAdderCoreGates n).map (EncodedBit.GateSpec.event .empty) := by
  simp [activeAdderGates, activeAdderCarrierGates,
    activeAdderInsertedGates, List.map_map]

private theorem activeAdderInverseGates_events_eq_core (n : Nat) :
    (activeAdderInverseGates n).map (EncodedBit.GateSpec.event .empty) =
      (activeAdderCoreGates n).reverse.map (EncodedBit.GateSpec.event .empty) := by
  simp [activeAdderInverseGates, activeAdderInverseCarrierGates,
    activeAdderInverseInsertedGates, activeAdderInverseCoreGates,
    List.map_map]

private theorem activeAdderCoreGates_events_eq_schedule (n : Nat) :
    (activeAdderCoreGates n).map (EncodedBit.GateSpec.event .empty) =
      (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates
        (PlainAdder.Schedule.PowerOfTwo.carryWorkLayout (AdderWidth n))).map
          (EncodedBit.GateSpec.event .empty) := by
  rfl

theorem activeAdderGates_toffoliMultiplicity_sum (n : Nat) :
    ((activeAdderGates n).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * n := by
  have h := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    .empty (activeAdderGates_events_eq_core n)
  rw [h]
  have hschedule := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    .empty (activeAdderCoreGates_events_eq_schedule n)
  rw [hschedule]
  simpa [AdderWidth] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum
      (PlainAdder.Schedule.PowerOfTwo.carryWorkLayout (AdderWidth n)))

theorem activeAdderGates_cnotMultiplicity_sum (n : Nat) :
    ((activeAdderGates n).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * (n + 1) := by
  have h := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    .empty (activeAdderGates_events_eq_core n)
  rw [h]
  have hschedule := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    .empty (activeAdderCoreGates_events_eq_schedule n)
  rw [hschedule]
  simpa [AdderWidth] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum
      (PlainAdder.Schedule.PowerOfTwo.carryWorkLayout (AdderWidth n)))

theorem activeAdderGates_xMultiplicity_sum (n : Nat) :
    ((activeAdderGates n).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  have h := EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
    .empty (activeAdderGates_events_eq_core n)
  rw [h]
  have hschedule := EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
    .empty (activeAdderCoreGates_events_eq_schedule n)
  rw [hschedule]
  simpa [AdderWidth] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum
      (PlainAdder.Schedule.PowerOfTwo.carryWorkLayout (AdderWidth n)))

theorem activeAdderInverseGates_toffoliMultiplicity_sum (n : Nat) :
    ((activeAdderInverseGates n).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * n := by
  have h := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    .empty (activeAdderInverseGates_events_eq_core n)
  rw [h, List.map_reverse, List.sum_reverse]
  have hschedule := EncodedBit.GateSpec.sum_toffoliMultiplicity_eq_of_events_eq
    .empty (activeAdderCoreGates_events_eq_schedule n)
  rw [hschedule]
  simpa [AdderWidth] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_toffoliMultiplicity_sum
      (PlainAdder.Schedule.PowerOfTwo.carryWorkLayout (AdderWidth n)))

theorem activeAdderInverseGates_cnotMultiplicity_sum (n : Nat) :
    ((activeAdderInverseGates n).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * (n + 1) := by
  have h := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    .empty (activeAdderInverseGates_events_eq_core n)
  rw [h, List.map_reverse, List.sum_reverse]
  have hschedule := EncodedBit.GateSpec.sum_cnotMultiplicity_eq_of_events_eq
    .empty (activeAdderCoreGates_events_eq_schedule n)
  rw [hschedule]
  simpa [AdderWidth] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_cnotMultiplicity_sum
      (PlainAdder.Schedule.PowerOfTwo.carryWorkLayout (AdderWidth n)))

theorem activeAdderInverseGates_xMultiplicity_sum (n : Nat) :
    ((activeAdderInverseGates n).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  have h := EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
    .empty (activeAdderInverseGates_events_eq_core n)
  rw [h, List.map_reverse, List.sum_reverse]
  have hschedule := EncodedBit.GateSpec.sum_xMultiplicity_eq_of_events_eq
    .empty (activeAdderCoreGates_events_eq_schedule n)
  rw [hschedule]
  simpa [AdderWidth] using
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_xMultiplicity_sum
      (PlainAdder.Schedule.PowerOfTwo.carryWorkLayout (AdderWidth n)))

private theorem sourceSwapGates_cnotMultiplicity_sum (n : Nat) :
    ((sourceSwapGates n).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 3 * n := by
  rw [← EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  simpa [sourceSwapGates, EncodedBit.Word.swapCircuit,
    EncodedBit.Word.swapProgram] using
    (EncodedBit.Word.swapCircuit_cnot_eventCount
      (QubitLayout.canonical _) .empty
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n))

private theorem primitiveMultiplicity_sums_eq_length
    {Data : Type} {dataEncoding : BinaryLabelEncoding Data}
    (gates : List (EncodedBit.GateSpec dataEncoding)) :
    (gates.map EncodedBit.GateSpec.xMultiplicity).sum +
        (gates.map EncodedBit.GateSpec.cnotMultiplicity).sum +
        (gates.map EncodedBit.GateSpec.toffoliMultiplicity).sum =
      gates.length := by
  have h := EncodedBit.GateSpec.primitiveEventCount_programList
    (QubitLayout.canonical dataEncoding.width) .empty gates
  unfold EncodedBit.GateSpec.primitiveEventCount at h
  rw [EncodedBit.GateSpec.programList_x_count_eq_sum,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum] at h
  exact h

private theorem sourceSwapGates_toffoliMultiplicity_sum (n : Nat) :
    ((sourceSwapGates n).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  have htotal := primitiveMultiplicity_sums_eq_length (sourceSwapGates n)
  have hc := sourceSwapGates_cnotMultiplicity_sum n
  have hlen : (sourceSwapGates n).length = 3 * n := by
    exact EncodedBit.Word.swapGates_length
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n)
  omega

private theorem sourceSwapGates_xMultiplicity_sum (n : Nat) :
    ((sourceSwapGates n).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  have htotal := primitiveMultiplicity_sums_eq_length (sourceSwapGates n)
  have hc := sourceSwapGates_cnotMultiplicity_sum n
  have hlen : (sourceSwapGates n).length = 3 * n := by
    exact EncodedBit.Word.swapGates_length
      (activeSourceLowWord n) (parkedSourceWord n)
      (activeSourceLow_parked_diagonal_ne n)
  omega

private theorem clearActiveModulusGates_cnotMultiplicity_sum_eq_length
    (n N : Nat) :
    ((clearActiveModulusGates n N).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      (clearActiveModulusGates n N).length := by
  simp only [clearActiveModulusGates,
    EncodedBit.Word.controlledXorConstantGates, List.map_map]
  generalize
    EncodedBit.Word.constantOneIndices (modulusWordLabel n N) = indices
  induction indices with
  | nil => rfl
  | cons bit rest ih => simp [ih, Nat.add_comm]

private theorem clearActiveModulusGates_toffoliMultiplicity_sum
    (n N : Nat) :
    ((clearActiveModulusGates n N).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  have htotal := primitiveMultiplicity_sums_eq_length
    (clearActiveModulusGates n N)
  have hc := clearActiveModulusGates_cnotMultiplicity_sum_eq_length n N
  omega

private theorem clearActiveModulusGates_xMultiplicity_sum
    (n N : Nat) :
    ((clearActiveModulusGates n N).map
        EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  have htotal := primitiveMultiplicity_sums_eq_length
    (clearActiveModulusGates n N)
  have hc := clearActiveModulusGates_cnotMultiplicity_sum_eq_length n N
  omega

/-- Five clean-carry adders contribute the complete Toffoli coordinate of the
eleven-stage modular-add schedule. -/
theorem modularAddGates_toffoliMultiplicity_sum (n N : Nat) :
    ((modularAddGates n N).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 30 * n := by
  simp [modularAddGates, activeAdderGates_toffoliMultiplicity_sum,
    activeAdderInverseGates_toffoliMultiplicity_sum,
    sourceSwapGates_toffoliMultiplicity_sum,
    clearActiveModulusGates_toffoliMultiplicity_sum,
    restoreActiveModulusGates, copyReductionFlagGates,
    cleanupReductionFlagGates]
  ring

/-- Bit-pattern-independent CNOT bound for the eleven-stage modular-add
schedule.  The two controlled modulus loads are bounded by their full word
width; every other summand is exact. -/
theorem modularAddGates_cnotMultiplicity_sum_le (n N : Nat) :
    ((modularAddGates n N).map
        EncodedBit.GateSpec.cnotMultiplicity).sum ≤ 18 * n + 14 := by
  have hclear : (clearActiveModulusGates n N).length ≤ n + 1 :=
    EncodedBit.Word.controlledXorConstantGates_length_le_width
      (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
      (reductionFlag_activeSource_ne n)
  have hrestore :
      ((restoreActiveModulusGates n N).map
          EncodedBit.GateSpec.cnotMultiplicity).sum ≤ n + 1 := by
    rw [restoreActiveModulusGates, List.map_reverse, List.sum_reverse,
      clearActiveModulusGates_cnotMultiplicity_sum_eq_length]
    exact hclear
  have hclearCount :
      ((clearActiveModulusGates n N).map
          EncodedBit.GateSpec.cnotMultiplicity).sum ≤ n + 1 := by
    rw [clearActiveModulusGates_cnotMultiplicity_sum_eq_length]
    exact hclear
  simp only [modularAddGates, List.map_append, List.sum_append,
    activeAdderGates_cnotMultiplicity_sum,
    activeAdderInverseGates_cnotMultiplicity_sum,
    sourceSwapGates_cnotMultiplicity_sum, copyReductionFlagGates,
    cleanupReductionFlagGates, EncodedBit.GateSpec.cnotMultiplicity_x,
    EncodedBit.GateSpec.cnotMultiplicity_cnot, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

/-- The overflow-decision copy is the sole X coordinate in one modular add. -/
theorem modularAddGates_xMultiplicity_sum (n N : Nat) :
    ((modularAddGates n N).map
        EncodedBit.GateSpec.xMultiplicity).sum = 1 := by
  simp [modularAddGates, activeAdderGates_xMultiplicity_sum,
    activeAdderInverseGates_xMultiplicity_sum,
    sourceSwapGates_xMultiplicity_sum,
    clearActiveModulusGates_xMultiplicity_sum,
    restoreActiveModulusGates, copyReductionFlagGates,
    cleanupReductionFlagGates]

/-- Exact Toffoli count of the production modular-add circuit, projected from
the same primitive list used by its semantics. -/
theorem modularAddProgram_toffoli_count_eq (n N : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
        (modularAddProgram n N).eventCost = 30 * n := by
  rw [modularAddProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact modularAddGates_toffoliMultiplicity_sum n N

/-- Bit-pattern-independent CNOT bound of the production modular-add circuit. -/
theorem modularAddProgram_cnot_count_le (n N : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
        (modularAddProgram n N).eventCost ≤ 18 * n + 14 := by
  rw [modularAddProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  exact modularAddGates_cnotMultiplicity_sum_le n N

/-- Exact X count of the production modular-add circuit. -/
theorem modularAddProgram_x_count_eq (n N : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
        (modularAddProgram n N).eventCost = 1 := by
  rw [modularAddProgram, EncodedBit.GateSpec.programList_x_count_eq_sum]
  exact modularAddGates_xMultiplicity_sum n N





















theorem modularAdd_realizes (n N : Nat) :
    UnitaryCircuit.Realizes (encoding n) (modularAddProgram n N)
      (modularAddStep n N) := by
  unfold modularAddProgram
  exact EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty (modularAddGates n N)
    (modularAddStep_eq_gateList n N)

/-- On clean inputs with canonical representatives, the exact VBE program
adds the active source into the target modulo `N`, restores the parked modulus,
and cleans every carry and comparison bit. -/
theorem modularAddStep_cleanEndpoint (n N : Nat)
    (a b : PlainAdder.Word n)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (ha : a.val < N) (hb : b.val < N) :
    modularAddStep n N
        (sourceSwapCleanState n a (N : PlainAdder.Word n)
          (widenWord n b) false) =
      sourceSwapCleanState n a (N : PlainAdder.Word n)
        ((a.val + b.val) % N : PlainAdder.Word (AdderWidth n)) false := by
  let sumWord : PlainAdder.Word (AdderWidth n) :=
    widenWord n b + widenWord n a
  let subWord : PlainAdder.Word (AdderWidth n) :=
    sumWord - widenWord n (N : PlainAdder.Word n)
  let reducedWord : PlainAdder.Word (AdderWidth n) :=
    (VBEArithmetic.reduceOnce N (a.val + b.val) :
      PlainAdder.Word (AdderWidth n))
  let reducedFlag : Bool := decide (N ≤ a.val + b.val)
  have hNval : ((N : PlainAdder.Word n)).val = N :=
    ZMod.val_natCast_of_lt hN
  have hsubWord :
      subWord =
        (((a.val + b.val : Nat) : PlainAdder.Word (AdderWidth n)) -
          (N : PlainAdder.Word (AdderWidth n))) := by
    simp only [subWord, sumWord, widenWord]
    rw [hNval, Nat.cast_add]
    ring
  have hsubBit :
      subWord.val.testBit n = decide (a.val + b.val < N) := by
    have h := VBEArithmetic.subtractModulus_msb
      (n := n) (N := N) (a := a.val) (b := b.val)
      (Nat.le_of_lt hN) ha hb
    rw [hsubWord]
    exact h
  have hunderflow :
      decide (a.val + b.val < N) = !reducedFlag := by
    by_cases h : N ≤ a.val + b.val
    · have hnlt : ¬a.val + b.val < N := Nat.not_lt_of_ge h
      simp [reducedFlag, h, hnlt]
    · have hlt : a.val + b.val < N := Nat.lt_of_not_ge h
      simp [reducedFlag, h, hlt]
  have hwidenConditional :
      widenWord n
          (if reducedFlag then 0 else (N : PlainAdder.Word n)) =
        (if N ≤ a.val + b.val then 0
          else (N : PlainAdder.Word (AdderWidth n))) := by
    by_cases h : N ≤ a.val + b.val <;>
      simp [reducedFlag, h, widenWord, hNval]
  have haddBack :
      subWord + widenWord n
          (if reducedFlag then 0 else (N : PlainAdder.Word n)) =
        reducedWord := by
    have h := VBEArithmetic.addBack_word_eq_reduceOnce
      (n := n) (N := N) (a := a.val) (b := b.val)
    rw [hsubWord, hwidenConditional]
    exact h
  have hcleanupBit :
      (reducedWord - widenWord n a).val.testBit n = reducedFlag := by
    have h := VBEArithmetic.cleanupProbe_msb
      (n := n) (N := N) (a := a.val) (b := b.val)
      (Nat.le_of_lt hN) ha hb
    simpa [reducedWord, reducedFlag, widenWord] using h
  have hreduce :
      VBEArithmetic.reduceOnce N (a.val + b.val) =
        (a.val + b.val) % N :=
    VBEArithmetic.reduceOnce_eq_mod hNpos (by omega)
  let s0 := sourceSwapCleanState n a (N : PlainAdder.Word n)
    (widenWord n b) false
  let s1 := sourceSwapCleanState n a (N : PlainAdder.Word n) sumWord false
  let s2 := sourceSwapCleanState n (N : PlainAdder.Word n) a sumWord false
  let s3 := sourceSwapCleanState n (N : PlainAdder.Word n) a subWord false
  let s4 := sourceSwapCleanState n (N : PlainAdder.Word n) a subWord reducedFlag
  let s5 := sourceSwapCleanState n
    (if reducedFlag then 0 else (N : PlainAdder.Word n)) a subWord reducedFlag
  let s6 := sourceSwapCleanState n
    (if reducedFlag then 0 else (N : PlainAdder.Word n)) a reducedWord reducedFlag
  let s7 := sourceSwapCleanState n (N : PlainAdder.Word n) a reducedWord reducedFlag
  let s8 := sourceSwapCleanState n a (N : PlainAdder.Word n) reducedWord reducedFlag
  let s9 := sourceSwapCleanState n a (N : PlainAdder.Word n)
    (reducedWord - widenWord n a) reducedFlag
  let s10 := sourceSwapCleanState n a (N : PlainAdder.Word n)
    (reducedWord - widenWord n a) false
  let s11 := sourceSwapCleanState n a (N : PlainAdder.Word n) reducedWord false
  have hs1 : activeAdderStep n s0 = s1 := by
    simpa [s0, s1, sumWord] using
      activeAdderStep_sourceSwapCleanState n a (N : PlainAdder.Word n)
        (widenWord n b) false
  have hs2 : sourceSwapStep n s1 = s2 := by
    simpa [s1, s2] using
      sourceSwapStep_cleanEndpoint n a (N : PlainAdder.Word n) sumWord false
  have hs3 : activeAdderInverseStep n s2 = s3 := by
    simpa [s2, s3, subWord, sourceSwapCleanState] using
      activeAdderInverseStep_sourceSwapCleanState n
        (N : PlainAdder.Word n) a sumWord false
  have hs4 : copyReductionFlagStep n s3 = s4 := by
    rw [copyReductionFlagStep_eq]
    simp [s3, s4, sourceSwapCleanState, hsubBit, hunderflow]
  have hs5 : clearActiveModulusStep n N s4 = s5 := by
    simpa [s4, s5] using
      clearActiveModulusStep_cleanEndpoint n N a subWord reducedFlag
  have hs6 : activeAdderStep n s5 = s6 := by
    simpa [s5, s6, haddBack] using
      activeAdderStep_sourceSwapCleanState n
        (if reducedFlag then 0 else (N : PlainAdder.Word n))
        a subWord reducedFlag
  have hs7 : restoreActiveModulusStep n N s6 = s7 := by
    simpa [s6, s7] using
      restoreActiveModulusStep_cleanEndpoint n N a reducedWord reducedFlag
  have hs8 : sourceSwapStep n s7 = s8 := by
    simpa [s7, s8] using
      sourceSwapStep_cleanEndpoint n (N : PlainAdder.Word n) a
        reducedWord reducedFlag
  have hs9 : activeAdderInverseStep n s8 = s9 := by
    simpa [s8, s9, sourceSwapCleanState] using
      activeAdderInverseStep_sourceSwapCleanState n a
        (N : PlainAdder.Word n) reducedWord reducedFlag
  have hs10 : cleanupReductionFlagStep n s9 = s10 := by
    rw [cleanupReductionFlagStep_eq]
    simp [s9, s10, sourceSwapCleanState, hcleanupBit]
  have hs11 : activeAdderStep n s10 = s11 := by
    simpa [s10, s11, sub_add_cancel] using
      activeAdderStep_sourceSwapCleanState n a (N : PlainAdder.Word n)
        (reducedWord - widenWord n a) false
  change modularAddStep n N s0 = _
  have hstages : modularAddStep n N s0 = s11 := by
    simp only [modularAddStep, modularAddSteps,
      UnitaryCircuit.Realizes.stepList, hs1, hs2, hs3, hs4, hs5, hs6,
      hs7, hs8, hs9, hs10, hs11, id_eq]
  rw [hstages]
  simp [s11, reducedWord, hreduce, sourceSwapCleanState]

/-- With a zero active source, the same fixed VBE ledger performs one
conditional reduction of an arbitrary target below `2 * N`.  The comparison
flag is intentionally retained: a caller may copy the reduced target and then
run the exact inverse program, which restores the complete input state. -/
theorem modularAddStep_zeroSource_reduceOnceEndpoint (n N : Nat)
    (raw : PlainAdder.Word (AdderWidth n))
    (hNpos : 0 < N) (hN : N < 2 ^ n) (hraw : raw.val < 2 * N) :
    modularAddStep n N
        (sourceSwapCleanState n 0 (N : PlainAdder.Word n) raw false) =
      sourceSwapCleanState n 0 (N : PlainAdder.Word n)
        (raw.val % N : PlainAdder.Word (AdderWidth n))
        (decide (N ≤ raw.val)) := by
  let subWord : PlainAdder.Word (AdderWidth n) :=
    raw - widenWord n (N : PlainAdder.Word n)
  let reducedWord : PlainAdder.Word (AdderWidth n) :=
    (VBEArithmetic.reduceOnce N raw.val :
      PlainAdder.Word (AdderWidth n))
  let reducedFlag : Bool := decide (N ≤ raw.val)
  have hNval : ((N : PlainAdder.Word n)).val = N :=
    ZMod.val_natCast_of_lt hN
  have hrawCast :
      (raw.val : PlainAdder.Word (AdderWidth n)) = raw := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hsubWord :
      subWord =
        ((raw.val : PlainAdder.Word (AdderWidth n)) -
          (N : PlainAdder.Word (AdderWidth n))) := by
    simp only [subWord, widenWord]
    rw [hNval, hrawCast]
  have hsubBit :
      subWord.val.testBit n = decide (raw.val < N) := by
    have h := VBEArithmetic.subtractModulusRaw_msb
      (n := n) (N := N) (s := raw.val) hNpos hN hraw
    rw [hsubWord]
    exact h
  have hunderflow : decide (raw.val < N) = !reducedFlag := by
    by_cases h : N ≤ raw.val
    · have hnlt : ¬raw.val < N := Nat.not_lt_of_ge h
      simp [reducedFlag, h, hnlt]
    · have hlt : raw.val < N := Nat.lt_of_not_ge h
      simp [reducedFlag, h, hlt]
  have hwidenConditional :
      widenWord n
          (if reducedFlag then 0 else (N : PlainAdder.Word n)) =
        (if N ≤ raw.val then 0
          else (N : PlainAdder.Word (AdderWidth n))) := by
    by_cases h : N ≤ raw.val <;>
      simp [reducedFlag, h, widenWord, hNval]
  have haddBack :
      subWord + widenWord n
          (if reducedFlag then 0 else (N : PlainAdder.Word n)) =
        reducedWord := by
    have h := VBEArithmetic.addBack_word_eq_reduceOnce
      (n := n) (N := N) (a := 0) (b := raw.val)
    simp only [Nat.zero_add] at h
    rw [hsubWord, hwidenConditional]
    exact h
  have hreducedLtN : VBEArithmetic.reduceOnce N raw.val < N :=
    VBEArithmetic.reduceOnce_lt hNpos hraw
  have hreducedLtPow : VBEArithmetic.reduceOnce N raw.val < 2 ^ n :=
    hreducedLtN.trans hN
  have hreducedLtWord :
      VBEArithmetic.reduceOnce N raw.val < 2 ^ (n + 1) := by
    exact hreducedLtPow.trans
      (Nat.pow_lt_pow_right (by decide) n.lt_succ_self)
  have hcleanupBit :
      (reducedWord - widenWord n (0 : PlainAdder.Word n)).val.testBit n =
        false := by
    have hbit := Nat.testBit_lt_two_pow hreducedLtPow
    simpa [reducedWord, widenWord,
      ZMod.val_natCast_of_lt hreducedLtWord] using hbit
  have hreduce :
      VBEArithmetic.reduceOnce N raw.val = raw.val % N :=
    VBEArithmetic.reduceOnce_eq_mod hNpos hraw
  let s0 := sourceSwapCleanState n (0 : PlainAdder.Word n)
    (N : PlainAdder.Word n) raw false
  let s1 := sourceSwapCleanState n (0 : PlainAdder.Word n)
    (N : PlainAdder.Word n) raw false
  let s2 := sourceSwapCleanState n (N : PlainAdder.Word n)
    (0 : PlainAdder.Word n) raw false
  let s3 := sourceSwapCleanState n (N : PlainAdder.Word n)
    (0 : PlainAdder.Word n) subWord false
  let s4 := sourceSwapCleanState n (N : PlainAdder.Word n)
    (0 : PlainAdder.Word n) subWord reducedFlag
  let s5 := sourceSwapCleanState n
    (if reducedFlag then 0 else (N : PlainAdder.Word n))
    (0 : PlainAdder.Word n) subWord reducedFlag
  let s6 := sourceSwapCleanState n
    (if reducedFlag then 0 else (N : PlainAdder.Word n))
    (0 : PlainAdder.Word n) reducedWord reducedFlag
  let s7 := sourceSwapCleanState n (N : PlainAdder.Word n)
    (0 : PlainAdder.Word n) reducedWord reducedFlag
  let s8 := sourceSwapCleanState n (0 : PlainAdder.Word n)
    (N : PlainAdder.Word n) reducedWord reducedFlag
  let s9 := sourceSwapCleanState n (0 : PlainAdder.Word n)
    (N : PlainAdder.Word n)
    (reducedWord - widenWord n (0 : PlainAdder.Word n)) reducedFlag
  let s10 := sourceSwapCleanState n (0 : PlainAdder.Word n)
    (N : PlainAdder.Word n)
    (reducedWord - widenWord n (0 : PlainAdder.Word n)) reducedFlag
  let s11 := sourceSwapCleanState n (0 : PlainAdder.Word n)
    (N : PlainAdder.Word n) reducedWord reducedFlag
  have hs1 : activeAdderStep n s0 = s1 := by
    simpa [s0, s1, widenWord] using
      activeAdderStep_sourceSwapCleanState n (0 : PlainAdder.Word n)
        (N : PlainAdder.Word n) raw false
  have hs2 : sourceSwapStep n s1 = s2 := by
    simpa [s1, s2] using
      sourceSwapStep_cleanEndpoint n (0 : PlainAdder.Word n)
        (N : PlainAdder.Word n) raw false
  have hs3 : activeAdderInverseStep n s2 = s3 := by
    simpa [s2, s3, subWord, sourceSwapCleanState] using
      activeAdderInverseStep_sourceSwapCleanState n
        (N : PlainAdder.Word n) (0 : PlainAdder.Word n) raw false
  have hs4 : copyReductionFlagStep n s3 = s4 := by
    rw [copyReductionFlagStep_eq]
    simp [s3, s4, sourceSwapCleanState, hsubBit, hunderflow]
  have hs5 : clearActiveModulusStep n N s4 = s5 := by
    simpa [s4, s5] using
      clearActiveModulusStep_cleanEndpoint n N (0 : PlainAdder.Word n)
        subWord reducedFlag
  have hs6 : activeAdderStep n s5 = s6 := by
    simpa [s5, s6, haddBack] using
      activeAdderStep_sourceSwapCleanState n
        (if reducedFlag then 0 else (N : PlainAdder.Word n))
        (0 : PlainAdder.Word n) subWord reducedFlag
  have hs7 : restoreActiveModulusStep n N s6 = s7 := by
    simpa [s6, s7] using
      restoreActiveModulusStep_cleanEndpoint n N (0 : PlainAdder.Word n)
        reducedWord reducedFlag
  have hs8 : sourceSwapStep n s7 = s8 := by
    simpa [s7, s8] using
      sourceSwapStep_cleanEndpoint n (N : PlainAdder.Word n)
        (0 : PlainAdder.Word n) reducedWord reducedFlag
  have hs9 : activeAdderInverseStep n s8 = s9 := by
    simpa [s8, s9, sourceSwapCleanState] using
      activeAdderInverseStep_sourceSwapCleanState n
        (0 : PlainAdder.Word n) (N : PlainAdder.Word n)
        reducedWord reducedFlag
  have hs10 : cleanupReductionFlagStep n s9 = s10 := by
    rw [cleanupReductionFlagStep_eq]
    simp [s9, s10, sourceSwapCleanState, hcleanupBit]
  have hs11 : activeAdderStep n s10 = s11 := by
    simpa [s10, s11, widenWord] using
      activeAdderStep_sourceSwapCleanState n (0 : PlainAdder.Word n)
        (N : PlainAdder.Word n)
        (reducedWord - widenWord n (0 : PlainAdder.Word n)) reducedFlag
  change modularAddStep n N s0 = _
  have hstages : modularAddStep n N s0 = s11 := by
    simp only [modularAddStep, modularAddSteps,
      UnitaryCircuit.Realizes.stepList, hs1, hs2, hs3, hs4, hs5, hs6,
      hs7, hs8, hs9, hs10, hs11, id_eq]
  rw [hstages]
  simp [s11, reducedWord, reducedFlag, hreduce, sourceSwapCleanState]

/-- Typed circuit obtained from the exact VBE program. -/
def modularAddCircuit (n N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  modularAddProgram n N

/-- Ordered strict events of the concrete modular-add circuit. -/
def modularAddEventTrace (n N : Nat) :
    List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (modularAddCircuit n N).eventTrace

/-- Strict event pool of the concrete modular-add circuit. -/
def modularAddEventCost (n N : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (modularAddCircuit n N).eventCost

/-- Strict symbolic event critical path of the modular-add circuit. -/
def modularAddEventDepth (n N : Nat) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (modularAddCircuit n N).eventDepth

/-- Evaluated strict event depth of the modular-add circuit. -/
def modularAddEvaluatedEventDepth (n N : Nat)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) : Nat :=
  (modularAddCircuit n N).evaluatedEventDepth assign

/-- Literal depth of one strict event coordinate in the modular-add circuit. -/
def modularAddEventQueryDepth (n N : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  (modularAddCircuit n N).eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the modular-add event pool. -/
def modularAddEventGateCount (n N : Nat)
    (label : AlgorithmGate.Coordinate) : Nat :=
  ResourcePool.count
    (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) label)
    (modularAddCircuit n N).eventCost

/-- Linearizing modular-add event depth recovers its exact strict event pool. -/
theorem modularAddCircuit_resourcesFromEventDepth_eq_eventCost (n N : Nat) :
    (modularAddCircuit n N).resourcesFromEventDepth =
      (modularAddCircuit n N).eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost (modularAddCircuit n N)









/-- Normalized-ket correctness for the actual circuit whose resources are
projected above. -/
theorem modularAddCircuit_applyNormalized_clean_ket (n N : Nat)
    (a b : PlainAdder.Word n)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (ha : a.val < N) (hb : b.val < N) :
    (modularAddCircuit n N).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
            ((encoding n).encode
              (sourceSwapCleanState n a (N : PlainAdder.Word n)
                (widenWord n b) false)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding n).width).basisEquiv.symm
          ((encoding n).encode
            (sourceSwapCleanState n a (N : PlainAdder.Word n)
              ((a.val + b.val) % N : PlainAdder.Word (AdderWidth n)) false))) := by
  simpa only [modularAddCircuit,
    modularAddStep_cleanEndpoint n N a b hNpos hN ha hb] using
    (modularAdd_realizes n N).apply_encoded_ket
      (sourceSwapCleanState n a (N : PlainAdder.Word n)
        (widenWord n b) false)

/-! ### Doubly controlled constant-add composition -/

/-- Two external controls together with the complete fixed-layout arithmetic
state.  The first control is the enclosing modular-multiplication control and
the second is the selected multiplier bit from the VBE construction. -/
structure ControlledRegisters (n : Nat) where
  /-- Outer control for the modular-multiplication step. -/
  externalControl : Bool
  /-- Selected multiplier bit controlling this addition. -/
  multiplierBit : Bool
  /-- Complete fixed-layout VBE arithmetic state. -/
  arithmetic : Registers n
deriving DecidableEq

/-- Packed carrier with the two controls preceding the arithmetic state. -/
abbrev RawControlledRegisters (n : Nat) : Type :=
  (Bool × Bool) × Registers n

/-- Fieldwise equivalence between named and packed controlled registers. -/
def controlledRegistersEquiv (n : Nat) :
    ControlledRegisters n ≃ RawControlledRegisters n where
  toFun := fun x => ((x.externalControl, x.multiplierBit), x.arithmetic)
  invFun := fun x =>
    { externalControl := x.1.1
      multiplierBit := x.1.2
      arithmetic := x.2 }
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨externalControl, multiplierBit⟩, arithmetic⟩
    rfl

/-- Product encoding for the two Boolean control wires. -/
def controlPairEncoding : BinaryLabelEncoding (Bool × Bool) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool

/-- Packed encoding of both controls followed by the arithmetic layout. -/
def rawControlledEncoding (n : Nat) :
    BinaryLabelEncoding (RawControlledRegisters n) :=
  BinaryLabelEncoding.prod controlPairEncoding (encoding n)

/-- Fixed controlled layout: two control wires followed by the VBE arithmetic
layout. -/
def controlledEncoding (n : Nat) :
    BinaryLabelEncoding (ControlledRegisters n) :=
  (rawControlledEncoding n).relabel (controlledRegistersEquiv n)

@[simp] theorem controlledEncoding_width (n : Nat) :
    (controlledEncoding n).width = 4 * n + 6 := by
  simp [controlledEncoding, rawControlledEncoding, controlPairEncoding,
    AdderWidth, PlainAdder.Schedule.PowerOfTwo.wordEncoding]
  omega

/-- Encoded bit selecting the outer control wire. -/
def controlABit (n : Nat) : EncodedBit (controlledEncoding n) :=
  (BinaryLabelEncoding.prodLeftBit controlPairEncoding (encoding n)
    (BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)).relabel
        (controlledRegistersEquiv n)

/-- Encoded bit selecting the multiplier control wire. -/
def controlBBit (n : Nat) : EncodedBit (controlledEncoding n) :=
  (BinaryLabelEncoding.prodLeftBit controlPairEncoding (encoding n)
    (BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)).relabel
        (controlledRegistersEquiv n)

/-- Lift any arithmetic-layout bit past the two external controls. -/
def liftControlledRegisterBit (n : Nat) (bit : EncodedBit (encoding n)) :
    EncodedBit (controlledEncoding n) :=
  (BinaryLabelEncoding.prodRightBit controlPairEncoding (encoding n) bit).relabel
    (controlledRegistersEquiv n)

/-- One active-source bit lifted past both control wires. -/
def controlledActiveSourceBit (n : Nat) (bit : Fin (AdderWidth n)) :
    EncodedBit (controlledEncoding n) :=
  liftControlledRegisterBit n (activeSourceBit n bit)

/-- Full active-source word in the controlled layout. -/
def controlledActiveSourceWord (n : Nat) :
    EncodedBit.Word (controlledEncoding n) (AdderWidth n) where
  bit := controlledActiveSourceBit n

@[simp] theorem controlABit_get (n : Nat) (x : ControlledRegisters n) :
    (controlABit n).get x = x.externalControl :=
  rfl

@[simp] theorem controlBBit_get (n : Nat) (x : ControlledRegisters n) :
    (controlBBit n).get x = x.multiplierBit :=
  rfl

@[simp] theorem liftControlledRegisterBit_get (n : Nat)
    (bit : EncodedBit (encoding n)) (x : ControlledRegisters n) :
    (liftControlledRegisterBit n bit).get x = bit.get x.arithmetic :=
  rfl

@[simp] theorem controlledActiveSourceBit_get (n : Nat)
    (bit : Fin (AdderWidth n)) (x : ControlledRegisters n) :
    (controlledActiveSourceBit n bit).get x =
      x.arithmetic.activeSource.val.testBit bit.val := by
  simp [controlledActiveSourceBit]

@[simp] theorem controlABit_wire_val (n : Nat) :
    (controlABit n).wire.val = 0 :=
  rfl

@[simp] theorem controlBBit_wire_val (n : Nat) :
    (controlBBit n).wire.val = 1 :=
  rfl

@[simp] theorem liftControlledRegisterBit_wire_val (n : Nat)
    (bit : EncodedBit (encoding n)) :
    (liftControlledRegisterBit n bit).wire.val = 2 + bit.wire.val := by
  change controlPairEncoding.width + bit.wire.val = 2 + bit.wire.val
  rfl

theorem controlA_controlB_ne (n : Nat) :
    (controlABit n).wire ≠ (controlBBit n).wire := by
  intro h
  have hv := congrArg Fin.val h
  simp at hv

theorem controlA_activeSource_ne (n : Nat) :
    ∀ bit,
      (controlABit n).wire ≠ ((controlledActiveSourceWord n).bit bit).wire := by
  intro bit h
  have hv := congrArg Fin.val h
  simp [controlledActiveSourceWord, controlledActiveSourceBit] at hv
  omega

theorem controlB_activeSource_ne (n : Nat) :
    ∀ bit,
      (controlBBit n).wire ≠ ((controlledActiveSourceWord n).bit bit).wire := by
  intro bit h
  have hv := congrArg Fin.val h
  simp [controlledActiveSourceWord, controlledActiveSourceBit] at hv
  omega

theorem controlledActiveSource_pairwise_ne (n : Nat) :
    ∀ i j, i ≠ j →
      ((controlledActiveSourceWord n).bit i).wire ≠
        ((controlledActiveSourceWord n).bit j).wire := by
  intro i j hij h
  have hv := congrArg Fin.val h
  simp [controlledActiveSourceWord, controlledActiveSourceBit] at hv
  apply hij
  apply Fin.ext
  have hi : i.val < n + 1 := by simpa [AdderWidth] using i.isLt
  have hj : j.val < n + 1 := by simpa [AdderWidth] using j.isLt
  omega

/-- Fixed-width encoded label of the widened controlled-add constant. -/
def controlledConstantLabel (n : Nat) (a : PlainAdder.Word n) :
    Fin (2 ^ AdderWidth n) :=
  PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv (AdderWidth n) (widenWord n a)

theorem controlledConstantLabel_testBit (n : Nat) (a : PlainAdder.Word n)
    (bit : Fin (AdderWidth n)) :
    (controlledConstantLabel n a).val.testBit bit.val =
      (widenWord n a).val.testBit bit.val := by
  unfold controlledConstantLabel
  rw [← PlainAdder.Schedule.PowerOfTwo.wordBit_get]
  simp [PlainAdder.Schedule.PowerOfTwo.wordBit,
    BinaryLabelEncoding.ofEquivBit]

/-- Load the constant source word iff both VBE controls are set. -/
def controlledLoadProgram (n : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (controlledEncoding n).width).toQuantum :=
  EncodedBit.Word.doubleControlledXorConstantProgram
    (QubitLayout.canonical _) .empty
    (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
    (controlledConstantLabel n a) (controlA_controlB_ne n)
    (controlA_activeSource_ne n) (controlB_activeSource_ne n)

/-- Folded action that loads the constant when both controls are set. -/
def controlledLoadStep (n : Nat) (a : PlainAdder.Word n) :
    ControlledRegisters n → ControlledRegisters n :=
  EncodedBit.Word.doubleControlledXorConstantStep
    (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
    (controlledConstantLabel n a) (controlA_controlB_ne n)
    (controlA_activeSource_ne n) (controlB_activeSource_ne n)

theorem controlledLoad_realizes (n : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit.Realizes (controlledEncoding n) (controlledLoadProgram n a)
      (controlledLoadStep n a) :=
  EncodedBit.Word.doubleControlledXorConstant_realizes
    (QubitLayout.canonical _) .empty
    (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
    (controlledConstantLabel n a) (controlA_controlB_ne n)
    (controlA_activeSource_ne n) (controlB_activeSource_ne n)

/-- Reverse-list unload paired with `controlledLoadProgram`. -/
def controlledUnloadProgram (n : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (controlledEncoding n).width).toQuantum :=
  EncodedBit.Word.doubleControlledXorConstantUnloadProgram
    (QubitLayout.canonical _) .empty
    (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
    (controlledConstantLabel n a) (controlA_controlB_ne n)
    (controlA_activeSource_ne n) (controlB_activeSource_ne n)

/-- Folded reverse-list action that unloads the controlled constant. -/
def controlledUnloadStep (n : Nat) (a : PlainAdder.Word n) :
    ControlledRegisters n → ControlledRegisters n :=
  EncodedBit.Word.doubleControlledXorConstantUnloadStep
    (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
    (controlledConstantLabel n a) (controlA_controlB_ne n)
    (controlA_activeSource_ne n) (controlB_activeSource_ne n)

theorem controlledUnload_realizes (n : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit.Realizes (controlledEncoding n)
      (controlledUnloadProgram n a) (controlledUnloadStep n a) :=
  EncodedBit.Word.doubleControlledXorConstantUnload_realizes
    (QubitLayout.canonical _) .empty
    (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
    (controlledConstantLabel n a) (controlA_controlB_ne n)
    (controlA_activeSource_ne n) (controlB_activeSource_ne n)

/-- Lift the already proved modular adder past both unchanged controls. -/
def controlledArithmeticStep (n N : Nat) :
    ControlledRegisters n → ControlledRegisters n :=
  fun x => { x with arithmetic := modularAddStep n N x.arithmetic }

/-- Modular-adder gates lifted past both unchanged controls. -/
def controlledArithmeticGates (n N : Nat) :
    List (EncodedBit.GateSpec (controlledEncoding n)) :=
  ((modularAddGates n N).map
      (EncodedBit.GateSpec.prodRight controlPairEncoding)).map
    (EncodedBit.GateSpec.relabel (controlledRegistersEquiv n))

/-- The lifted gate list updates only the arithmetic field. -/
theorem controlledArithmeticGates_step (n N : Nat)
    (x : ControlledRegisters n) :
    EncodedBit.GateSpec.stepList (controlledArithmeticGates n N) x =
      controlledArithmeticStep n N x := by
  unfold controlledArithmeticGates controlledArithmeticStep controlledEncoding
    rawControlledEncoding
  rw [EncodedBit.GateSpec.stepList_relabel]
  rw [EncodedBit.GateSpec.stepList_prodRight]
  rw [modularAddStep_eq_gateList]
  cases x
  rfl

/-- Actual modular-adder circuit compiled on the complete controlled layout. -/
def controlledArithmeticProgram (n N : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (controlledEncoding n).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (controlledArithmeticGates n N)

/-- Direct realization of the modular adder lifted past both controls. -/
theorem controlledArithmetic_realizes (n N : Nat) :
    UnitaryCircuit.Realizes (controlledEncoding n) (controlledArithmeticProgram n N)
      (controlledArithmeticStep n N) := by
  exact EncodedBit.GateSpec.realizesList_congrStep
    (QubitLayout.canonical _) .empty (controlledArithmeticGates n N)
    (controlledArithmeticGates_step n N)

/-- The controlled VBE program is load, the exact modular add, then reverse
unload, all on one encoding and one strict event trace. -/
def controlledAddPrograms (n N : Nat) (a : PlainAdder.Word n) :
    List (UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (controlledEncoding n).width).toQuantum) :=
  [ controlledLoadProgram n a,
    controlledArithmeticProgram n N,
    controlledUnloadProgram n a ]

/-- Semantic stage list matching load, modular add, and unload. -/
def controlledAddSteps (n N : Nat) (a : PlainAdder.Word n) :
    List (ControlledRegisters n → ControlledRegisters n) :=
  [ controlledLoadStep n a,
    controlledArithmeticStep n N,
    controlledUnloadStep n a ]

theorem controlledAddStages_realize (n N : Nat) (a : PlainAdder.Word n) :
    List.Forall₂
      (fun program step =>
        UnitaryCircuit.Realizes (controlledEncoding n) program step)
      (controlledAddPrograms n N a) (controlledAddSteps n N a) := by
  unfold controlledAddPrograms controlledAddSteps
  exact .cons (controlledLoad_realizes n a) <|
    .cons (controlledArithmetic_realizes n N) <|
    .cons (controlledUnload_realizes n a) .nil

/-- Folded semantics of the complete controlled-add stage list. -/
def controlledAddStep (n N : Nat) (a : PlainAdder.Word n) :
    ControlledRegisters n → ControlledRegisters n :=
  UnitaryCircuit.Realizes.stepList (controlledAddSteps n N a)

/-- Concatenated base-gate program for controlled modular addition. -/
def controlledAddProgram (n N : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (controlledEncoding n).width).toQuantum :=
  (controlledAddPrograms n N a).foldr UnitaryCircuit.seq
    (UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical (controlledEncoding n).width).toQuantum)

theorem controlledAdd_realizes (n N : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit.Realizes (controlledEncoding n)
      (controlledAddProgram n N a) (controlledAddStep n N a) :=
  UnitaryCircuit.Realizes.appendList (controlledEncoding n) (QubitLayout.canonical _)
    (controlledAddPrograms n N a) (controlledAddSteps n N a)
    (controlledAddStages_realize n N a)

/-- Canonical controlled state used by the load/add/unload endpoint. -/
def controlledCleanState (n : Nat) (externalControl multiplierBit : Bool)
    (active parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    ControlledRegisters n where
  externalControl := externalControl
  multiplierBit := multiplierBit
  arithmetic := sourceSwapCleanState n active parked target flag

/-- Lifting past the two controls preserves every arithmetic wire
separation. -/
theorem controlledActiveSource_liftRegister_ne (n : Nat)
    (observed : EncodedBit (encoding n))
    (hne : ∀ bit,
      ((activeSourceWord n).bit bit).wire ≠ observed.wire) :
    ∀ bit,
      ((controlledActiveSourceWord n).bit bit).wire ≠
        (liftControlledRegisterBit n observed).wire := by
  intro bit h
  apply hne bit
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa [controlledActiveSourceWord, controlledActiveSourceBit,
    activeSourceWord] using hv

/-- Loading into an initially zero active source produces exactly the selected
constant and preserves both controls and every other arithmetic field. -/
theorem controlledLoadStep_cleanEndpoint (n : Nat) (a : PlainAdder.Word n)
    (externalControl multiplierBit : Bool) (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    controlledLoadStep n a
        (controlledCleanState n externalControl multiplierBit 0 parked
          target flag) =
      controlledCleanState n externalControl multiplierBit
        (if externalControl && multiplierBit then a else 0) parked target flag := by
  let input := controlledCleanState n externalControl multiplierBit 0 parked
    target flag
  have hactive :
      (controlledLoadStep n a input).arithmetic.activeSource =
        widenWord n (if externalControl && multiplierBit then a else 0) := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_target
        (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
        (controlledConstantLabel n a) (controlA_controlB_ne n)
        (controlA_activeSource_ne n) (controlB_activeSource_ne n) bit
        (fun other hother =>
          controlledActiveSource_pairwise_ne n other bit hother) input
    have hconstant := controlledConstantLabel_testBit n a bit
    have hzeroBit :
        (widenWord n (0 : PlainAdder.Word n)).val.testBit bit.val = false := by
      rw [widenWord_val]
      simp
    cases externalControl <;>
      cases multiplierBit <;>
      cases hbit : (widenWord n a).val.testBit bit.val <;>
      simpa [controlledLoadStep, input, controlledCleanState,
        controlledActiveSourceWord, sourceSwapCleanState,
        hconstant, hzeroBit, hbit] using hread
  have hexternal :
      (controlledLoadStep n a input).externalControl = externalControl := by
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
        (controlledConstantLabel n a) (controlA_controlB_ne n)
        (controlA_activeSource_ne n) (controlB_activeSource_ne n)
        (controlABit n) (fun bit => Ne.symm (controlA_activeSource_ne n bit)) input
    simpa [controlledLoadStep, input, controlledCleanState,
      sourceSwapCleanState] using hread
  have hmultiplier :
      (controlledLoadStep n a input).multiplierBit = multiplierBit := by
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
        (controlledConstantLabel n a) (controlA_controlB_ne n)
        (controlA_activeSource_ne n) (controlB_activeSource_ne n)
        (controlBBit n) (fun bit => Ne.symm (controlB_activeSource_ne n bit)) input
    simpa [controlledLoadStep, input, controlledCleanState,
      sourceSwapCleanState] using hread
  have htarget : (controlledLoadStep n a input).arithmetic.target = target := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
        (controlledConstantLabel n a) (controlA_controlB_ne n)
        (controlA_activeSource_ne n) (controlB_activeSource_ne n)
        (liftControlledRegisterBit n (targetBit n bit))
        (controlledActiveSource_liftRegister_ne n (targetBit n bit)
          (fun sourceBit => activeSource_target_ne n sourceBit bit)) input
    simpa [controlledLoadStep, input, controlledCleanState,
      sourceSwapCleanState] using hread
  have hcarry : (controlledLoadStep n a input).arithmetic.carry = false := by
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
        (controlledConstantLabel n a) (controlA_controlB_ne n)
        (controlA_activeSource_ne n) (controlB_activeSource_ne n)
        (liftControlledRegisterBit n (carryBit n))
        (controlledActiveSource_liftRegister_ne n (carryBit n)
          (activeSource_carry_ne n)) input
    simpa [controlledLoadStep, input, controlledCleanState,
      sourceSwapCleanState] using hread
  have hparked :
      (controlledLoadStep n a input).arithmetic.parkedSource = parked := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
        (controlledConstantLabel n a) (controlA_controlB_ne n)
        (controlA_activeSource_ne n) (controlB_activeSource_ne n)
        (liftControlledRegisterBit n (parkedSourceBit n bit))
        (controlledActiveSource_liftRegister_ne n (parkedSourceBit n bit)
          (fun sourceBit => activeSource_parked_ne n sourceBit bit)) input
    simpa [controlledLoadStep, input, controlledCleanState,
      sourceSwapCleanState] using hread
  have hwork :
      (controlledLoadStep n a input).arithmetic.carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n) := by
    change (controlledLoadStep n a input).arithmetic.carryWork = 0
    apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro bit
    rw [← carryWorkBit_get n bit
      (controlledLoadStep n a input).arithmetic]
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
        (controlledConstantLabel n a) (controlA_controlB_ne n)
        (controlA_activeSource_ne n) (controlB_activeSource_ne n)
        (liftControlledRegisterBit n (carryWorkBit n bit))
        (controlledActiveSource_liftRegister_ne n (carryWorkBit n bit)
          (fun sourceBit => activeSource_carryWork_ne n sourceBit bit)) input
    have hread' :
        (carryWorkBit n bit).get
            (controlledLoadStep n a input).arithmetic =
          (carryWorkBit n bit).get input.arithmetic := by
      simpa [controlledLoadStep] using hread
    rw [hread', carryWorkBit_get]
    simp [input, controlledCleanState, sourceSwapCleanState,
      PlainAdder.Schedule.PowerOfTwo.cleanCarryWork]
  have hflag :
      (controlledLoadStep n a input).arithmetic.reductionFlag = flag := by
    have hread :=
      EncodedBit.Word.doubleControlledXorConstantStep_get_observed_of_target_ne
        (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
        (controlledConstantLabel n a) (controlA_controlB_ne n)
        (controlA_activeSource_ne n) (controlB_activeSource_ne n)
        (liftControlledRegisterBit n (reductionFlagBit n))
        (controlledActiveSource_liftRegister_ne n (reductionFlagBit n)
          (fun sourceBit => Ne.symm
            (reductionFlag_activeSource_ne n sourceBit))) input
    simpa [controlledLoadStep, input, controlledCleanState,
      sourceSwapCleanState] using hread
  change controlledLoadStep n a input = _
  have harithmetic :
      (controlledLoadStep n a input).arithmetic =
        sourceSwapCleanState n
          (if externalControl && multiplierBit then a else 0)
          parked target flag := by
    apply (registersEquiv n).injective
    change
      (((({ left := (controlledLoadStep n a input).arithmetic.activeSource,
            right := (controlledLoadStep n a input).arithmetic.target,
            carry := (controlledLoadStep n a input).arithmetic.carry } :
          PlainAdder.Data (AdderWidth n)),
          (controlledLoadStep n a input).arithmetic.parkedSource),
        (controlledLoadStep n a input).arithmetic.carryWork),
        (controlledLoadStep n a input).arithmetic.reductionFlag) =
      (((({ left := widenWord n
              (if externalControl && multiplierBit then a else 0),
            right := target,
            carry := false } : PlainAdder.Data (AdderWidth n)), parked),
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork (AdderWidth n)), flag)
    rw [hactive, htarget, hcarry, hparked, hwork, hflag]
  apply (controlledRegistersEquiv n).injective
  change
    (((controlledLoadStep n a input).externalControl,
        (controlledLoadStep n a input).multiplierBit),
      (controlledLoadStep n a input).arithmetic) =
    ((externalControl, multiplierBit),
      sourceSwapCleanState n
        (if externalControl && multiplierBit then a else 0) parked target flag)
  rw [hexternal, hmultiplier, harithmetic]

/-- Reverse-list unloading removes precisely the source created by the matching
double-controlled load. -/
theorem controlledUnloadStep_cleanEndpoint (n : Nat) (a : PlainAdder.Word n)
    (externalControl multiplierBit : Bool) (parked : PlainAdder.Word n)
    (target : PlainAdder.Word (AdderWidth n)) (flag : Bool) :
    controlledUnloadStep n a
        (controlledCleanState n externalControl multiplierBit
          (if externalControl && multiplierBit then a else 0) parked
          target flag) =
      controlledCleanState n externalControl multiplierBit 0 parked target flag := by
  let input := controlledCleanState n externalControl multiplierBit 0 parked
    target flag
  have hload := controlledLoadStep_cleanEndpoint n a externalControl
    multiplierBit parked target flag
  have hinverse :=
    EncodedBit.Word.doubleControlledXorConstantUnloadStep_after_doubleControlledXorConstantStep
      (controlABit n) (controlBBit n) (controlledActiveSourceWord n)
      (controlledConstantLabel n a) (controlA_controlB_ne n)
      (controlA_activeSource_ne n) (controlB_activeSource_ne n) input
  change controlledUnloadStep n a (controlledLoadStep n a input) = input at hinverse
  rw [hload] at hinverse
  simpa [input] using hinverse

/-- Clean endpoint of the source-backed controlled modular add.  The selected
constant contributes exactly when both controls are true; the active source,
carry work, and reduction flag are zero/clean again at the endpoint. -/
theorem controlledAddStep_cleanEndpoint (n N : Nat)
    (a b : PlainAdder.Word n) (externalControl multiplierBit : Bool)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (ha : a.val < N) (hb : b.val < N) :
    controlledAddStep n N a
        (controlledCleanState n externalControl multiplierBit 0
          (N : PlainAdder.Word n) (widenWord n b) false) =
      controlledCleanState n externalControl multiplierBit 0
        (N : PlainAdder.Word n)
        (((if externalControl && multiplierBit then a.val else 0) + b.val) % N :
          PlainAdder.Word (AdderWidth n)) false := by
  let loaded : PlainAdder.Word n :=
    if externalControl && multiplierBit then a else 0
  let result : PlainAdder.Word (AdderWidth n) :=
    ((loaded.val + b.val) % N : PlainAdder.Word (AdderWidth n))
  have hloadedLt : loaded.val < N := by
    cases externalControl <;>
      cases multiplierBit <;>
      simp [loaded, hNpos, ha]
  have hmod := modularAddStep_cleanEndpoint n N loaded b
    hNpos hN hloadedLt hb
  let s0 := controlledCleanState n externalControl multiplierBit 0
    (N : PlainAdder.Word n) (widenWord n b) false
  let s1 := controlledCleanState n externalControl multiplierBit loaded
    (N : PlainAdder.Word n) (widenWord n b) false
  let s2 := controlledCleanState n externalControl multiplierBit loaded
    (N : PlainAdder.Word n) result false
  let s3 := controlledCleanState n externalControl multiplierBit 0
    (N : PlainAdder.Word n) result false
  have hs1 : controlledLoadStep n a s0 = s1 := by
    simpa [s0, s1, loaded] using
      controlledLoadStep_cleanEndpoint n a externalControl multiplierBit
        (N : PlainAdder.Word n) (widenWord n b) false
  have hs2 : controlledArithmeticStep n N s1 = s2 := by
    apply (controlledRegistersEquiv n).injective
    change
      ((externalControl, multiplierBit),
        modularAddStep n N
          (sourceSwapCleanState n loaded (N : PlainAdder.Word n)
            (widenWord n b) false)) =
      ((externalControl, multiplierBit),
        sourceSwapCleanState n loaded (N : PlainAdder.Word n) result false)
    simpa [result] using congrArg
      (fun arithmetic => ((externalControl, multiplierBit), arithmetic)) hmod
  have hs3 : controlledUnloadStep n a s2 = s3 := by
    simpa [s2, s3, loaded] using
      controlledUnloadStep_cleanEndpoint n a externalControl multiplierBit
        (N : PlainAdder.Word n) result false
  change controlledAddStep n N a s0 = _
  have hstages : controlledAddStep n N a s0 = s3 := by
    simp only [controlledAddStep, controlledAddSteps,
      UnitaryCircuit.Realizes.stepList, hs1, hs2, hs3, id_eq]
  rw [hstages]
  cases externalControl <;>
    cases multiplierBit <;>
    simp [s3, result, loaded]

/-- Concrete circuit used by the controlled-add semantic and resource APIs. -/
def controlledAddCircuit (n N : Nat) (a : PlainAdder.Word n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (controlledEncoding n).width).toQuantum :=
  controlledAddProgram n N a

/-- Ordered strict events of the concrete controlled-add circuit. -/
def controlledAddEventTrace (n N : Nat) (a : PlainAdder.Word n) :
    List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (controlledAddCircuit n N a).eventTrace

/-- Strict event pool of the concrete controlled-add circuit. -/
def controlledAddEventCost (n N : Nat) (a : PlainAdder.Word n) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (controlledAddCircuit n N a).eventCost

/-- Strict symbolic event critical path of the controlled-add circuit. -/
def controlledAddEventDepth (n N : Nat) (a : PlainAdder.Word n) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (controlledAddCircuit n N a).eventDepth

/-- Evaluated strict event depth of the controlled-add circuit. -/
def controlledAddEvaluatedEventDepth (n N : Nat) (a : PlainAdder.Word n)
    (assign : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat) : Nat :=
  (controlledAddCircuit n N a).evaluatedEventDepth assign

/-- Literal depth of one strict event coordinate in the controlled-add circuit. -/
def controlledAddEventQueryDepth (n N : Nat) (a : PlainAdder.Word n)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  (controlledAddCircuit n N a).eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the controlled-add pool. -/
def controlledAddEventGateCount (n N : Nat) (a : PlainAdder.Word n)
    (label : AlgorithmGate.Coordinate) : Nat :=
  ResourcePool.count
    (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) label)
    (controlledAddCircuit n N a).eventCost

/-- Linearizing controlled-add event depth recovers its exact event pool. -/
theorem controlledAddCircuit_resourcesFromEventDepth_eq_eventCost
    (n N : Nat) (a : PlainAdder.Word n) :
    (controlledAddCircuit n N a).resourcesFromEventDepth =
      (controlledAddCircuit n N a).eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost (controlledAddCircuit n N a)









theorem controlledAddCircuit_applyNormalized_clean_ket (n N : Nat)
    (a b : PlainAdder.Word n) (externalControl multiplierBit : Bool)
    (hNpos : 0 < N) (hN : N < 2 ^ n)
    (ha : a.val < N) (hb : b.val < N) :
    (controlledAddCircuit n N a).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical (controlledEncoding n).width).basisEquiv.symm
            ((controlledEncoding n).encode
              (controlledCleanState n externalControl multiplierBit 0
                (N : PlainAdder.Word n) (widenWord n b) false)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (controlledEncoding n).width).basisEquiv.symm
          ((controlledEncoding n).encode
            (controlledCleanState n externalControl multiplierBit 0
              (N : PlainAdder.Word n)
              (((if externalControl && multiplierBit then a.val else 0) + b.val) % N :
                PlainAdder.Word (AdderWidth n)) false))) := by
  simpa only [controlledAddCircuit,
    controlledAddStep_cleanEndpoint n N a b externalControl multiplierBit
      hNpos hN ha hb] using
    (controlledAdd_realizes n N a).apply_encoded_ket
      (controlledCleanState n externalControl multiplierBit 0
        (N : PlainAdder.Word n) (widenWord n b) false)

end

end VBECircuit
end MAU.Addition
end QuantumAlg

end
