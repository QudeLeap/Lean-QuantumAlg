/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.Comparator
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule.ZeroTestValue
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Util.ZModUnits
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap

/-!
# Encoded base-gate modular-addition target-update witnesses

This module provides the narrow actual-circuit interfaces needed when a modular
adder is embedded as a target-update block inside larger modular-arithmetic
pipelines.  A closing witness must still supply the concrete Toffoli/CNOT/X
program; this file only fixes the field order and semantic action for
the target-add subprograms used by the staged inversion and division routes.

The target-update role follows the reversible compare/subtract/add-back
modular-addition route [VBE95, 9511018.tex:274-316,634-643].
-/

section

namespace QuantumAlg
namespace MAU.Addition

noncomputable section

namespace TargetAdd

/-- Field tuple for a target-add block: target, scratch source, and one clean
flag/control bit. -/
abbrev Data (N : Nat) :=
  ZMod N × (ZMod N × Bool)

/-- Field-by-field encoding for a target-add block. -/
def encoding {N n : Nat} (E : BinaryResidueEncoding N n) :
    BinaryLabelEncoding (Data N) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
      BinaryLabelEncoding.bool)

/-- Add the scratch/source residue into the target field, preserving the source
and flag. -/
def step {N : Nat} : Data N -> Data N
  | (target, (scratch, flag)) => (target + scratch, (scratch, flag))

namespace RawLayout

/-- Wire address for a bit of the target field. -/
def targetWire {N n : Nat} (E : BinaryResidueEncoding N n) (bit : Fin n) :
    Fin (encoding E).width :=
  ⟨bit.val, by
    have hbit := bit.isLt
    change bit.val < n + (n + 1)
    omega⟩

/-- Wire address for a bit of the scratch/source field. -/
def scratchWire {N n : Nat} (E : BinaryResidueEncoding N n) (bit : Fin n) :
    Fin (encoding E).width :=
  ⟨n + bit.val, by
    have hbit := bit.isLt
    change n + bit.val < n + (n + 1)
    omega⟩

/-- Wire address for the one-bit flag field. -/
def flagWire {N n : Nat} (E : BinaryResidueEncoding N n) :
    Fin (encoding E).width :=
  ⟨n + n, by
    change n + n < n + (n + 1)
    omega⟩

@[simp] theorem targetWire_val {N n : Nat}
    (E : BinaryResidueEncoding N n) (bit : Fin n) :
    (targetWire E bit).val = bit.val :=
  rfl

@[simp] theorem scratchWire_val {N n : Nat}
    (E : BinaryResidueEncoding N n) (bit : Fin n) :
    (scratchWire E bit).val = n + bit.val :=
  rfl

@[simp] theorem flagWire_val {N n : Nat}
    (E : BinaryResidueEncoding N n) :
    (flagWire E).val = n + n :=
  rfl

/-- One CNOT that xors one scratch bit into the corresponding target bit. -/
def cnotScratchToTarget {N n : Nat}
    (E : BinaryResidueEncoding N n) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding E).width).toQuantum :=
  QubitPrimitive.circuit
    (.cnot (scratchWire E bit) (targetWire E bit) (by
      intro h
      have hbit := bit.isLt
      have hv : n + bit.val = bit.val := by
        simpa [scratchWire, targetWire] using congrArg Fin.val h
      omega))
    (QubitLayout.canonical _) .empty

/-- Two-bit ripple-style block for a selected low/high bit pair: carry from
the low scratch/target pair into the high target bit, then xor the high and low
scratch bits into the target field. -/
def twoBitRippleProgram {N n : Nat}
    (E : BinaryResidueEncoding N n) (low high : Fin n) (hlh : low ≠ high) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding E).width).toQuantum :=
  BitSlice.Raw.targetAdd2Program
    (scratchWire E low) (targetWire E low) (scratchWire E high) (targetWire E high)
    (by
      intro h
      have hv : n + low.val = low.val := by
        simpa [scratchWire, targetWire] using congrArg Fin.val h
      omega)
    (by
      intro h
      have hhigh := high.isLt
      have hv : n + low.val = high.val := by
        simpa [scratchWire, targetWire] using congrArg Fin.val h
      omega)
    (by
      intro h
      apply hlh
      apply Fin.ext
      simpa [targetWire] using congrArg Fin.val h)
    (by
      intro h
      have hv : n + high.val = high.val := by
        simpa [scratchWire, targetWire] using congrArg Fin.val h
      omega)

end RawLayout

/-- A target-add circuit witness over the exact field order used by staged
modular-inversion target updates. -/
structure Witness {N n : Nat} (E : BinaryResidueEncoding N n) where
  /-- Program acting on the target/scratch/flag field layout. -/
  program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding E).width).toQuantum
  /-- Correctness of the target-add program on encoded basis states. -/
  realizes : UnitaryCircuit.Realizes (encoding E) program step

/-- Raw-label correctness package for a target-add program on canonical
target/scratch/flag inputs.  This is the shape naturally discharged by a
concrete Toffoli/CNOT/X schedule before it is exposed as a semantic witness. -/
structure RawCanonicalWitness {N n : Nat} (E : BinaryResidueEncoding N n) where
  /-- Program acting on the packed target/scratch/flag binary layout. -/
  program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding E).width).toQuantum
  /-- The same program has the required action on canonical basis states. -/
  applyNormalized_encode_eq :
    ∀ (target scratch : ZMod N) (flag : Bool),
      program.applyNormalized
          (NormalizedVector.ket
            ((QubitLayout.canonical (encoding E).width).basisEquiv.symm
              ((encoding E).encode (target, (scratch, flag))))) =
        NormalizedVector.ket
          ((QubitLayout.canonical (encoding E).width).basisEquiv.symm
            ((encoding E).encode (step (target, (scratch, flag)))))

namespace RawCanonicalWitness

variable {N n : Nat} {E : BinaryResidueEncoding N n}

/-- Convert canonical-label correctness of one raw base-gate program into the
semantic target-add witness used by staged modular-arithmetic callers. -/
def toWitness (w : RawCanonicalWitness E) : Witness E where
  program := w.program
  realizes := by
    exact
      { apply_encoded_ket := by
          intro x
          rcases x with ⟨target, rest⟩
          rcases rest with ⟨scratch, flag⟩
          exact w.applyNormalized_encode_eq target scratch flag }

end RawCanonicalWitness

namespace PowerOfTwo
-- Declaration-scoped exception: a transparent named encoding parameter for circuit construction.
set_option linter.defProp false in
/-- Canonical `n`-bit residue encoding for the power-of-two modulus. -/
def residueEncoding (n : Nat) : BinaryResidueEncoding (2 ^ n) n where
  modulus_pos := by
    exact pow_pos (by decide : (0 : Nat) < 2) n
  register_fits := le_rfl

/-- Carry-work labels used by the VBE full-adder route. -/
abbrev CarryWork (n : Nat) : Type :=
  PlainAdder.Schedule.PowerOfTwo.CarryWork n

/-- Encoding for the VBE carry-work register. -/
def carryWorkEncoding (n : Nat) : BinaryLabelEncoding (CarryWork n) :=
  PlainAdder.Schedule.PowerOfTwo.carryWorkEncoding n

/-- Distinguished clean carry-work label. -/
def cleanCarryWork (n : Nat) : CarryWork n :=
  PlainAdder.Schedule.PowerOfTwo.cleanCarryWork n

@[simp] theorem targetEncoding_width (n : Nat) :
    (encoding (residueEncoding n)).width = n + (n + 1) := by
  rfl

/-- Target-add data plus VBE carry work in the physical target/scratch/flag/work
order used by MAU callers. -/
def withCarryWorkEncoding (n : Nat) :
    BinaryLabelEncoding (Data (2 ^ n) × CarryWork n) :=
  BinaryLabelEncoding.prod (encoding (residueEncoding n)) (carryWorkEncoding n)

/-- Target-field bit lens in the target/scratch/flag layout. -/
def targetBit (n : Nat) (bit : Fin n) :
    EncodedBit (encoding (residueEncoding n)) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      BinaryLabelEncoding.bool)
    (PlainAdder.Schedule.PowerOfTwo.wordBit n bit)

/-- Scratch/source-field bit lens in the target/scratch/flag layout. -/
def scratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (encoding (residueEncoding n)) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      BinaryLabelEncoding.bool
      (PlainAdder.Schedule.PowerOfTwo.wordBit n bit))

/-- Flag bit lens in the target/scratch/flag layout. -/
def flagBit (n : Nat) : EncodedBit (encoding (residueEncoding n)) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      BinaryLabelEncoding.bool
      BinaryLabelEncoding.boolBit)

/-- Target-field bit lens lifted to the target/scratch/flag/work layout. -/
def withCarryWorkTargetBit (n : Nat) (bit : Fin n) :
    EncodedBit (withCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (encoding (residueEncoding n))
    (carryWorkEncoding n) (targetBit n bit)

/-- Scratch/source-field bit lens lifted to the target/scratch/flag/work
layout. -/
def withCarryWorkScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (withCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (encoding (residueEncoding n))
    (carryWorkEncoding n) (scratchBit n bit)

/-- Flag bit lens lifted to the target/scratch/flag/work layout. -/
def withCarryWorkFlagBit (n : Nat) :
    EncodedBit (withCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (encoding (residueEncoding n))
    (carryWorkEncoding n) (flagBit n)

/-- Carry-work bit lens in the target/scratch/flag/work layout. -/
def carryWorkBit (n : Nat) (bit : Fin (n - 1)) :
    EncodedBit (withCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodRightBit (encoding (residueEncoding n))
    (carryWorkEncoding n)
    (BinaryLabelEncoding.finIdentityBit (n - 1) bit)

@[simp] theorem targetBit_get_testBit (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n)) :
    (targetBit n bit).get x = x.1.val.testBit bit.val := by
  rcases x with ⟨target, scratch, flag⟩
  change (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get target =
    target.val.testBit bit.val
  exact PlainAdder.Schedule.PowerOfTwo.wordBit_get n bit target

@[simp] theorem scratchBit_get_testBit (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n)) :
    (scratchBit n bit).get x = x.2.1.val.testBit bit.val := by
  rcases x with ⟨target, scratch, flag⟩
  change (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get scratch =
    scratch.val.testBit bit.val
  exact PlainAdder.Schedule.PowerOfTwo.wordBit_get n bit scratch

@[simp] theorem flagBit_get (n : Nat) (x : Data (2 ^ n)) :
    (flagBit n).get x = x.2.2 := by
  rcases x with ⟨target, scratch, flag⟩
  rfl

theorem withCarryWorkTargetBit_get_testBit (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n)) (work : CarryWork n) :
    (withCarryWorkTargetBit n bit).get (x, work) =
      x.1.val.testBit bit.val := by
  change (targetBit n bit).get x = x.1.val.testBit bit.val
  exact targetBit_get_testBit n bit x

theorem withCarryWorkScratchBit_get_testBit (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n)) (work : CarryWork n) :
    (withCarryWorkScratchBit n bit).get (x, work) =
      x.2.1.val.testBit bit.val := by
  change (scratchBit n bit).get x = x.2.1.val.testBit bit.val
  exact scratchBit_get_testBit n bit x

theorem withCarryWorkFlagBit_get (n : Nat)
    (x : Data (2 ^ n)) (work : CarryWork n) :
    (withCarryWorkFlagBit n).get (x, work) = x.2.2 := by
  change (flagBit n).get x = x.2.2
  exact flagBit_get n x

theorem carryWorkBit_get_clean (n : Nat) (bit : Fin (n - 1))
    (x : Data (2 ^ n)) :
    (carryWorkBit n bit).get (x, cleanCarryWork n) = false := by
  change
    (BinaryLabelEncoding.finIdentityBit (n - 1) bit).get
      (cleanCarryWork n) = false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero (n - 1) bit

@[simp] theorem withCarryWorkTargetBit_get_fst (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n) × CarryWork n) :
    (withCarryWorkTargetBit n bit).get x =
      x.1.1.val.testBit bit.val := by
  rcases x with ⟨data, work⟩
  exact withCarryWorkTargetBit_get_testBit n bit data work

@[simp] theorem withCarryWorkScratchBit_get_fst (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n) × CarryWork n) :
    (withCarryWorkScratchBit n bit).get x =
      x.1.2.1.val.testBit bit.val := by
  rcases x with ⟨data, work⟩
  exact withCarryWorkScratchBit_get_testBit n bit data work

@[simp] theorem withCarryWorkFlagBit_get_fst (n : Nat)
    (x : Data (2 ^ n) × CarryWork n) :
    (withCarryWorkFlagBit n).get x = x.1.2.2 := by
  rcases x with ⟨data, work⟩
  exact withCarryWorkFlagBit_get n data work

@[simp] theorem carryWorkBit_get_snd (n : Nat) (bit : Fin (n - 1))
    (x : Data (2 ^ n) × CarryWork n) :
    (carryWorkBit n bit).get x =
      (BinaryLabelEncoding.finIdentityBit (n - 1) bit).get x.2 := by
  rfl

/-- Scratch/source word in the target/scratch/flag/work layout. -/
def withCarryWorkScratchWord (n : Nat) :
    EncodedBit.Word (withCarryWorkEncoding n) n where
  bit := withCarryWorkScratchBit n

/-- Target word in the target/scratch/flag/work layout. -/
def withCarryWorkTargetWord (n : Nat) :
    EncodedBit.Word (withCarryWorkEncoding n) n where
  bit := withCarryWorkTargetBit n

/-- Temporary carry-work word in the target/scratch/flag/work layout. -/
def carryWorkWord (n : Nat) :
    EncodedBit.Word (withCarryWorkEncoding n) (n - 1) where
  bit := carryWorkBit n

@[simp] theorem targetBit_wire_val (n : Nat) (bit : Fin n) :
    ((targetBit n bit).wire).val = n - 1 - bit.val := by
  rfl

@[simp] theorem scratchBit_wire_val (n : Nat) (bit : Fin n) :
    ((scratchBit n bit).wire).val = n + (n - 1 - bit.val) := by
  rfl

@[simp] theorem flagBit_wire_val (n : Nat) :
    ((flagBit n).wire).val = n + n := by
  rfl

@[simp] theorem withCarryWorkTargetBit_wire_val (n : Nat) (bit : Fin n) :
    ((withCarryWorkTargetBit n bit).wire).val = n - 1 - bit.val := by
  rfl

@[simp] theorem withCarryWorkScratchBit_wire_val (n : Nat) (bit : Fin n) :
    ((withCarryWorkScratchBit n bit).wire).val = n + (n - 1 - bit.val) := by
  rfl

@[simp] theorem withCarryWorkFlagBit_wire_val (n : Nat) :
    ((withCarryWorkFlagBit n).wire).val = n + n := by
  rfl

@[simp] theorem carryWorkBit_wire_val (n : Nat) (bit : Fin (n - 1)) :
    ((carryWorkBit n bit).wire).val =
      (encoding (residueEncoding n)).width + bit.val := by
  rfl

/-- VBE carry-work layout specialized to the MAU target/scratch/flag physical
order.  The plain-adder left/source word is the MAU scratch field and the
plain-adder right/updated word is the MAU target field [VBE95,
9511018.tex:237-264,591-618]. -/
def carryWorkLayout (n : Nat) :
    PlainAdder.Schedule.CarryWorkLayout (encoding := withCarryWorkEncoding n) n where
  left := withCarryWorkScratchWord n
  right := withCarryWorkTargetWord n
  carryIn := withCarryWorkFlagBit n
  workCarry := carryWorkWord n
  leftLeft_ne := by
    intro i j hij
    change (withCarryWorkScratchBit n i).wire ≠
      (withCarryWorkScratchBit n j).wire
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [withCarryWorkScratchBit_wire_val] at hv
    omega
  rightRight_ne := by
    intro i j hij
    change (withCarryWorkTargetBit n i).wire ≠
      (withCarryWorkTargetBit n j).wire
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [withCarryWorkTargetBit_wire_val] at hv
    omega
  leftRight_ne := by
    intro i j
    change (withCarryWorkScratchBit n i).wire ≠
      (withCarryWorkTargetBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := j.isLt
    simp only [withCarryWorkScratchBit_wire_val,
      withCarryWorkTargetBit_wire_val] at hv
    omega
  leftCarryIn_ne := by
    intro i
    change (withCarryWorkScratchBit n i).wire ≠
      (withCarryWorkFlagBit n).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkScratchBit_wire_val,
      withCarryWorkFlagBit_wire_val] at hv
    omega
  rightCarryIn_ne := by
    intro i
    change (withCarryWorkTargetBit n i).wire ≠
      (withCarryWorkFlagBit n).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkTargetBit_wire_val,
      withCarryWorkFlagBit_wire_val] at hv
    omega
  leftWork_ne := by
    intro i j
    change (withCarryWorkScratchBit n i).wire ≠ (carryWorkBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkScratchBit_wire_val, carryWorkBit_wire_val,
      targetEncoding_width] at hv
    omega
  rightWork_ne := by
    intro i j
    change (withCarryWorkTargetBit n i).wire ≠ (carryWorkBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkTargetBit_wire_val, carryWorkBit_wire_val,
      targetEncoding_width] at hv
    omega
  carryInWork_ne := by
    intro j
    change (withCarryWorkFlagBit n).wire ≠ (carryWorkBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    simp only [withCarryWorkFlagBit_wire_val, carryWorkBit_wire_val,
      targetEncoding_width] at hv
    omega
  workWork_ne := by
    intro i j hij
    change (carryWorkBit n i).wire ≠ (carryWorkBit n j).wire
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [carryWorkBit_wire_val] at hv
    omega

@[simp] theorem carryWorkLayout_carryInput_get_clean
    (n : Nat) (j : Fin (n - 1)) (x : Data (2 ^ n)) :
    (PlainAdder.Schedule.CarryWorkLayout.carryInput (carryWorkLayout n) j).get
        (x, cleanCarryWork n) =
      if j.val = 0 then x.2.2 else false := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
  by_cases h : j.val = 0
  · simp [h, carryWorkLayout]
  · simpa [h, carryWorkLayout, carryWorkWord] using
      carryWorkBit_get_clean n
        (PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j h) x

/-- Folded carry/sum/cleanup gate list for target-add with clean carry work. -/
def cleanCarrySumGates (n : Nat) :
    List (EncodedBit.GateSpec (withCarryWorkEncoding n)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates (carryWorkLayout n)

/-- Base-gate program for target-add with clean carry work. -/
def cleanCarrySumProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (withCarryWorkEncoding n).width).toQuantum :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumProgram (carryWorkLayout n)

/-- Folded semantic action for target-add with clean carry work. -/
def cleanCarrySumStep (n : Nat) :
    Data (2 ^ n) × CarryWork n -> Data (2 ^ n) × CarryWork n :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep (carryWorkLayout n)

/-- The target-layout carry-work schedule is realized by the same folded
base-gate program used for resources. -/
theorem cleanCarrySum_realizes (n : Nat) :
    UnitaryCircuit.Realizes (withCarryWorkEncoding n)
      (cleanCarrySumProgram n) (cleanCarrySumStep n) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySum_realizes (carryWorkLayout n)

theorem carryStageIndexStep_get_workCarry_recurrence_testBit
    (n : Nat) (j : Fin (n - 1)) (x : Data (2 ^ n)) :
    (carryWorkBit n j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (carryWorkLayout n) (x, cleanCarryWork n)) =
      Bool.carry
        (x.2.1.val.testBit j.val)
        (x.1.val.testBit j.val)
        ((PlainAdder.Schedule.CarryWorkLayout.carryInput (carryWorkLayout n) j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (carryWorkLayout n) (x, cleanCarryWork n))) := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
      (carryWorkLayout n) j (x, cleanCarryWork n)
      (by
        intro k
        exact carryWorkBit_get_clean n k x)
  simpa [carryWorkLayout, carryWorkWord, withCarryWorkScratchWord,
    withCarryWorkTargetWord, PlainAdder.Schedule.CarryWorkLayout.lowIndex] using h

/-- The forward carry pass computes the propagated carry for the scratch+target
sum on clean flag/work inputs [VBE95, 9511018.tex:237-264,591-618]. -/
theorem carryStageIndexStep_get_workCarry_natAddCarry
    (n : Nat) (j : Fin (n - 1)) (x : Data (2 ^ n))
    (hflag : x.2.2 = false) :
    (carryWorkBit n j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (carryWorkLayout n) (x, cleanCarryWork n)) =
      Nat.BinaryArithmetic.natAddCarry
        x.2.1.val x.1.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (carryWorkLayout n) (x, cleanCarryWork n)
  change (carryWorkBit n j).get stage =
    Nat.BinaryArithmetic.natAddCarry x.2.1.val x.1.val (j.val + 1)
  have hmain : forall m, forall j : Fin (n - 1), j.val = m ->
      (carryWorkBit n j).get stage =
        Nat.BinaryArithmetic.natAddCarry
          x.2.1.val x.1.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          carryStageIndexStep_get_workCarry_recurrence_testBit n j x
        change (carryWorkBit n j).get stage =
          Nat.BinaryArithmetic.natAddCarry
            x.2.1.val x.1.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (carryWorkLayout n) (x, cleanCarryWork n)
          rw [hdata]
          simp [carryWorkLayout, hflag,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let p := PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          change
            Bool.carry (x.2.1.val.testBit j.val) (x.1.val.testBit j.val)
              ((carryWorkBit n p).get stage) =
            Nat.BinaryArithmetic.natAddCarry
              x.2.1.val x.1.val (j.val + 1)
          rw [hpRec, hpSucc]
          simp [Nat.BinaryArithmetic.natAddCarry]
  exact hmain j.val j rfl

/-- The carry selected before target bit `i` is the propagated natural carry
for the scratch+target sum. -/
theorem carryBeforeSum_get_natAddCarry
    (n : Nat) (i : Fin n) (x : Data (2 ^ n)) (hflag : x.2.2 = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum (carryWorkLayout n) i).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (carryWorkLayout n) (x, cleanCarryWork n)) =
      Nat.BinaryArithmetic.natAddCarry x.2.1.val x.1.val i.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : i.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (carryWorkLayout n) (x, cleanCarryWork n)
    rw [hdata]
    simp [carryWorkLayout, hflag,
      Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : i.val - 1 < n - 1 := by
      have hi := i.isLt
      omega
    let j : Fin (n - 1) := { val := i.val - 1, isLt := hjLt }
    have hwork :=
      carryStageIndexStep_get_workCarry_natAddCarry n j x hflag
    have hjSucc : j.val + 1 = i.val := by
      dsimp [j]
      omega
    change
      (carryWorkBit n j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (carryWorkLayout n) (x, cleanCarryWork n)) =
        Nat.BinaryArithmetic.natAddCarry x.2.1.val x.1.val i.val
    rw [hwork, hjSucc]

/-- Target-bit formula for the target-layout cleanup-aware carry/sum schedule. -/
theorem cleanCarrySumStep_get_target_testBit
    (n : Nat) (i : Fin n) (x : Data (2 ^ n)) :
    (Prod.fst
        (cleanCarrySumStep n (x, cleanCarryWork n))).1.val.testBit i.val =
      ((x.1.val.testBit i.val ^^ x.2.1.val.testBit i.val) ^^
        (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum (carryWorkLayout n) i).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (carryWorkLayout n) (x, cleanCarryWork n))) := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (carryWorkLayout n) i (x, cleanCarryWork n)
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep] at h
  simpa [cleanCarrySumStep, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout, carryWorkWord, withCarryWorkTargetWord,
    withCarryWorkScratchWord] using h

/-- On clean flag/work inputs, the target word is updated by adding the scratch
word. -/
theorem cleanCarrySumStep_get_target_add
    (n : Nat) (x : Data (2 ^ n)) (hflag : x.2.2 = false) :
    (Prod.fst (cleanCarrySumStep n (x, cleanCarryWork n))).1 =
      (step x).1 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro i
  rw [cleanCarrySumStep_get_target_testBit]
  rw [carryBeforeSum_get_natAddCarry n i x hflag]
  simp [step]
  simpa [Bool.xor_assoc] using
    (PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
      n x.2.1 x.1 i).symm

/-- The cleanup-aware target-add schedule preserves the scratch/source word. -/
theorem cleanCarrySumStep_get_scratch
    (n : Nat) (x : Data (2 ^ n)) :
    (Prod.fst (cleanCarrySumStep n (x, cleanCarryWork n))).2.1 = x.2.1 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro i
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (carryWorkLayout n) i (x, cleanCarryWork n)
  simpa [cleanCarrySumStep, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout, carryWorkWord, withCarryWorkScratchWord] using h

/-- The cleanup-aware target-add schedule preserves the flag bit. -/
theorem cleanCarrySumStep_get_flag
    (n : Nat) (x : Data (2 ^ n)) :
    (Prod.fst (cleanCarrySumStep n (x, cleanCarryWork n))).2.2 = x.2.2 := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (carryWorkLayout n) (x, cleanCarryWork n)
  simpa [cleanCarrySumStep, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout] using h

/-- The cleanup-aware target-add schedule restores the carry-work register. -/
theorem cleanCarrySumStep_get_work_clean
    (n : Nat) (x : Data (2 ^ n)) :
    Prod.snd (cleanCarrySumStep n (x, cleanCarryWork n)) =
      cleanCarryWork n := by
  apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
  intro bit
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (carryWorkLayout n) bit (x, cleanCarryWork n)
      (by
        intro k
        exact carryWorkBit_get_clean n k x)
  have hbit :
      (carryWorkBit n bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (carryWorkLayout n) (x, cleanCarryWork n)) =
        false := by
    simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
      carryWorkLayout, carryWorkWord] using h
  change
    (BinaryLabelEncoding.finIdentityBit (n - 1) bit).get
      (Prod.snd
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (carryWorkLayout n) (x, cleanCarryWork n))) =
      false
  rw [← carryWorkBit_get_snd n bit
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
      (carryWorkLayout n) (x, cleanCarryWork n))]
  simpa [cleanCarrySumStep, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep]
    using hbit

/-- Full clean endpoint for target-add with VBE carry work.  The statement is
intentionally conditional on a clean input flag, matching the reusable
plain-adder carry convention [VBE95, 9511018.tex:237-264,591-618]. -/
theorem cleanCarrySumStep_cleanEndpoint
    (n : Nat) (x : Data (2 ^ n)) (hflag : x.2.2 = false) :
    cleanCarrySumStep n (x, cleanCarryWork n) =
      (step x, cleanCarryWork n) := by
  apply Prod.ext
  · let y := Prod.fst (cleanCarrySumStep n (x, cleanCarryWork n))
    have htarget : y.1 = (step x).1 :=
      cleanCarrySumStep_get_target_add n x hflag
    have hscratch : y.2.1 = x.2.1 :=
      cleanCarrySumStep_get_scratch n x
    have hflag' : y.2.2 = x.2.2 :=
      cleanCarrySumStep_get_flag n x
    change y = step x
    clear_value y
    rcases y with ⟨target', scratch', flag'⟩
    rcases x with ⟨target, scratch, flag⟩
    change target' = target + scratch at htarget
    change scratch' = scratch at hscratch
    change flag' = flag at hflag'
    change (target', (scratch', flag')) = (target + scratch, (scratch, flag))
    rw [htarget, hscratch, hflag']
  · exact cleanCarrySumStep_get_work_clean n x

/-- Clean-work target-add witness used by decomposed MAU callers before a
no-work all-flags target-add program is available. -/
structure CleanWorkWitness (n : Nat) where
  /-- Distinguished clean work label. -/
  cleanWork : CarryWork n
  /-- Folded full-register semantic action. -/
  stepWithWork : Data (2 ^ n) × CarryWork n -> Data (2 ^ n) × CarryWork n
  /-- Actual folded full-register program. -/
  program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (withCarryWorkEncoding n).width).toQuantum
  /-- Direct realization of the folded full-register action. -/
  realizes :
    UnitaryCircuit.Realizes (withCarryWorkEncoding n) program stepWithWork
  /-- Clean endpoint for target-add when the flag/work registers start clean. -/
  cleanEndpoint :
    ∀ x : Data (2 ^ n), x.2.2 = false ->
      stepWithWork (x, cleanWork) = (step x, cleanWork)

/-- VBE carry-work target-add witness in the MAU target/scratch/flag/work
layout.  Resource and correctness projections are tied to `program`
[VBE95, 9511018.tex:237-264,591-618]. -/
def cleanWorkWitness (n : Nat) : CleanWorkWitness n where
  cleanWork := cleanCarryWork n
  stepWithWork := cleanCarrySumStep n
  program := cleanCarrySumProgram n
  realizes := cleanCarrySum_realizes n
  cleanEndpoint := cleanCarrySumStep_cleanEndpoint n

end PowerOfTwo

namespace Mod2
-- Declaration-scoped exception: a transparent named encoding parameter for circuit construction.
set_option linter.defProp false in
/-- One-bit canonical residue encoding for `ZMod 2`. -/
def residueEncoding : BinaryResidueEncoding 2 1 where
  modulus_pos := by decide
  register_fits := by decide

/-- One CNOT implements target update over `ZMod 2`. -/
def cnotProgram :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding residueEncoding).width).toQuantum :=
  RawLayout.cnotScratchToTarget residueEncoding ⟨0, by decide⟩

/-- Raw canonical-label action of the one-CNOT `ZMod 2` target update. -/
theorem cnotProgram_applyNormalized_encode_eq
    (target scratch : ZMod 2) (flag : Bool) :
    cnotProgram.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical
              (encoding residueEncoding).width).basisEquiv.symm
            ((encoding residueEncoding).encode (target, (scratch, flag))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
            (encoding residueEncoding).width).basisEquiv.symm
          ((encoding residueEncoding).encode
            (step (target, (scratch, flag))))) := by
  rw [cnotProgram, RawLayout.cnotScratchToTarget,
    QubitPrimitive.circuit_applyNormalized_ket]
  congr 1
  fin_cases target <;> fin_cases scratch <;> cases flag <;> decide

/-- End-to-end raw witness for the one-bit modular-add target update. -/
def rawCanonicalWitness : RawCanonicalWitness residueEncoding where
  program := cnotProgram
  applyNormalized_encode_eq := cnotProgram_applyNormalized_encode_eq

/-- Semantic witness obtained from the same one-CNOT raw program. -/
def witness : Witness residueEncoding :=
  rawCanonicalWitness.toWitness

end Mod2

namespace Mod4
-- Declaration-scoped exception: a transparent named encoding parameter for circuit construction.
set_option linter.defProp false in
/-- Two-bit canonical residue encoding for `ZMod 4`. -/
def residueEncoding : BinaryResidueEncoding 4 2 where
  modulus_pos := by decide
  register_fits := by decide

/-- Least-significant target bit in the packed target/scratch/flag layout. -/
def targetLSB : Fin (encoding residueEncoding).width :=
  RawLayout.targetWire residueEncoding ⟨1, by decide⟩

/-- Most-significant target bit in the packed target/scratch/flag layout. -/
def targetMSB : Fin (encoding residueEncoding).width :=
  RawLayout.targetWire residueEncoding ⟨0, by decide⟩

/-- Least-significant scratch/source bit in the packed target/scratch/flag
layout. -/
def scratchLSB : Fin (encoding residueEncoding).width :=
  RawLayout.scratchWire residueEncoding ⟨1, by decide⟩

/-- Most-significant scratch/source bit in the packed target/scratch/flag
layout. -/
def scratchMSB : Fin (encoding residueEncoding).width :=
  RawLayout.scratchWire residueEncoding ⟨0, by decide⟩

/-- Two-bit ripple-carry target update over `ZMod 4`: compute the low-bit carry
into the target MSB, xor the scratch MSB, then xor the scratch LSB. -/
def rippleProgram :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding residueEncoding).width).toQuantum :=
  RawLayout.twoBitRippleProgram residueEncoding
    ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)

/-- Raw canonical-label action of the two-bit ripple-carry `ZMod 4` target
update. -/
theorem rippleProgram_applyNormalized_encode_eq
    (target scratch : ZMod 4) (flag : Bool) :
    rippleProgram.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical
              (encoding residueEncoding).width).basisEquiv.symm
            ((encoding residueEncoding).encode (target, (scratch, flag))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
            (encoding residueEncoding).width).basisEquiv.symm
          ((encoding residueEncoding).encode
            (step (target, (scratch, flag))))) := by
  rw [rippleProgram, RawLayout.twoBitRippleProgram,
    BitSlice.Raw.targetAdd2Program, UnitaryCircuit.applyNormalized_seq,
    UnitaryCircuit.applyNormalized_seq,
    QubitPrimitive.circuit_applyNormalized_ket,
    QubitPrimitive.circuit_applyNormalized_ket,
    QubitPrimitive.circuit_applyNormalized_ket]
  apply congrArg (fun label : Fin (2 ^ (encoding residueEncoding).width) =>
    NormalizedVector.ket
      ((QubitLayout.canonical (encoding residueEncoding).width).basisEquiv.symm label))
  fin_cases target <;> fin_cases scratch <;> cases flag <;> decide

/-- End-to-end raw witness for the two-bit modular-add target update. -/
def rawCanonicalWitness : RawCanonicalWitness residueEncoding where
  program := rippleProgram
  applyNormalized_encode_eq := rippleProgram_applyNormalized_encode_eq

/-- Semantic witness obtained from the same two-bit ripple raw program. -/
def witness : Witness residueEncoding :=
  rawCanonicalWitness.toWitness

end Mod4

end TargetAdd

namespace TargetAddWithAux

/-- Field tuple for a target-add block with one untouched auxiliary residue
between the target and scratch source. -/
abbrev Data (N : Nat) :=
  ZMod N × (ZMod N × (ZMod N × Bool))

/-- Field-by-field encoding for a target-add block with one auxiliary residue. -/
def encoding {N n : Nat} (E : BinaryResidueEncoding N n) :
    BinaryLabelEncoding (Data N) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool))

/-- Add the scratch/source residue into the target field, preserving the
auxiliary residue, source, and flag. -/
def step {N : Nat} : Data N -> Data N
  | (target, (aux, (scratch, flag))) =>
      (target + scratch, (aux, (scratch, flag)))

namespace RawLayout

/-- Wire address for a bit of the target field. -/
def targetWire {N n : Nat} (E : BinaryResidueEncoding N n) (bit : Fin n) :
    Fin (encoding E).width :=
  ⟨bit.val, by
    have hbit := bit.isLt
    change bit.val < n + (n + (n + 1))
    omega⟩

/-- Wire address for a bit of the untouched auxiliary field. -/
def auxWire {N n : Nat} (E : BinaryResidueEncoding N n) (bit : Fin n) :
    Fin (encoding E).width :=
  ⟨n + bit.val, by
    have hbit := bit.isLt
    change n + bit.val < n + (n + (n + 1))
    omega⟩

/-- Wire address for a bit of the scratch/source field. -/
def scratchWire {N n : Nat} (E : BinaryResidueEncoding N n) (bit : Fin n) :
    Fin (encoding E).width :=
  ⟨n + n + bit.val, by
    have hbit := bit.isLt
    change n + n + bit.val < n + (n + (n + 1))
    omega⟩

/-- Wire address for the one-bit flag field. -/
def flagWire {N n : Nat} (E : BinaryResidueEncoding N n) :
    Fin (encoding E).width :=
  ⟨n + n + n, by
    change n + n + n < n + (n + (n + 1))
    omega⟩

@[simp] theorem targetWire_val {N n : Nat}
    (E : BinaryResidueEncoding N n) (bit : Fin n) :
    (targetWire E bit).val = bit.val :=
  rfl

@[simp] theorem auxWire_val {N n : Nat}
    (E : BinaryResidueEncoding N n) (bit : Fin n) :
    (auxWire E bit).val = n + bit.val :=
  rfl

@[simp] theorem scratchWire_val {N n : Nat}
    (E : BinaryResidueEncoding N n) (bit : Fin n) :
    (scratchWire E bit).val = n + n + bit.val :=
  rfl

@[simp] theorem flagWire_val {N n : Nat}
    (E : BinaryResidueEncoding N n) :
    (flagWire E).val = n + n + n :=
  rfl

/-- One CNOT that xors one scratch bit into the corresponding target bit,
leaving the auxiliary field untouched. -/
def cnotScratchToTarget {N n : Nat}
    (E : BinaryResidueEncoding N n) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding E).width).toQuantum :=
  QubitPrimitive.circuit
    (.cnot (scratchWire E bit) (targetWire E bit) (by
      intro h
      have hbit := bit.isLt
      have hv : n + n + bit.val = bit.val := by
        simpa [scratchWire, targetWire] using congrArg Fin.val h
      omega))
    (QubitLayout.canonical _) .empty

/-- Two-bit ripple-style block for a selected low/high bit pair, preserving
the auxiliary field. -/
def twoBitRippleProgram {N n : Nat}
    (E : BinaryResidueEncoding N n) (low high : Fin n) (hlh : low ≠ high) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding E).width).toQuantum :=
  BitSlice.Raw.targetAdd2Program
    (scratchWire E low) (targetWire E low) (scratchWire E high) (targetWire E high)
    (by
      intro h
      have hv : n + n + low.val = low.val := by
        simpa [scratchWire, targetWire] using congrArg Fin.val h
      omega)
    (by
      intro h
      have hhigh := high.isLt
      have hv : n + n + low.val = high.val := by
        simpa [scratchWire, targetWire] using congrArg Fin.val h
      omega)
    (by
      intro h
      apply hlh
      apply Fin.ext
      simpa [targetWire] using congrArg Fin.val h)
    (by
      intro h
      have hv : n + n + high.val = high.val := by
        simpa [scratchWire, targetWire] using congrArg Fin.val h
      omega)

end RawLayout

/-- A target-add circuit witness over the exact field order used by staged
modular-division target updates. -/
structure Witness {N n : Nat} (E : BinaryResidueEncoding N n) where
  /-- Program acting on the target/auxiliary/scratch/flag field layout. -/
  program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding E).width).toQuantum
  /-- Correctness of the target-add program on encoded basis states. -/
  realizes : UnitaryCircuit.Realizes (encoding E) program step

/-- Raw-label correctness package for a target-add program on canonical
target/auxiliary/scratch/flag inputs. -/
structure RawCanonicalWitness {N n : Nat} (E : BinaryResidueEncoding N n) where
  /-- Program acting on the packed target/auxiliary/scratch/flag binary layout. -/
  program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding E).width).toQuantum
  /-- The same program has the required action on canonical basis states. -/
  applyNormalized_encode_eq :
    ∀ (target aux scratch : ZMod N) (flag : Bool),
      program.applyNormalized
          (NormalizedVector.ket
            ((QubitLayout.canonical (encoding E).width).basisEquiv.symm
              ((encoding E).encode (target, (aux, (scratch, flag)))))) =
        NormalizedVector.ket
          ((QubitLayout.canonical (encoding E).width).basisEquiv.symm
            ((encoding E).encode (step (target, (aux, (scratch, flag))))))

namespace RawCanonicalWitness

variable {N n : Nat} {E : BinaryResidueEncoding N n}

/-- Convert canonical-label correctness of one raw base-gate program into the
semantic target-add-with-aux witness used by staged modular-arithmetic callers. -/
def toWitness (w : RawCanonicalWitness E) : Witness E where
  program := w.program
  realizes := by
    exact
      { apply_encoded_ket := by
          intro x
          rcases x with ⟨target, rest⟩
          rcases rest with ⟨aux, rest⟩
          rcases rest with ⟨scratch, flag⟩
          exact w.applyNormalized_encode_eq target aux scratch flag }

end RawCanonicalWitness

namespace PowerOfTwo
-- Declaration-scoped exception: a transparent named encoding parameter for circuit construction.
set_option linter.defProp false in
/-- Canonical `n`-bit residue encoding for the power-of-two modulus. -/
def residueEncoding (n : Nat) : BinaryResidueEncoding (2 ^ n) n where
  modulus_pos := by
    exact pow_pos (by decide : (0 : Nat) < 2) n
  register_fits := le_rfl

/-- Carry-work labels used by the VBE full-adder route with one auxiliary
residue field. -/
abbrev CarryWork (n : Nat) : Type :=
  TargetAdd.PowerOfTwo.CarryWork n

/-- Encoding for the VBE carry-work register. -/
def carryWorkEncoding (n : Nat) : BinaryLabelEncoding (CarryWork n) :=
  TargetAdd.PowerOfTwo.carryWorkEncoding n

/-- Distinguished clean carry-work label. -/
def cleanCarryWork (n : Nat) : CarryWork n :=
  TargetAdd.PowerOfTwo.cleanCarryWork n

@[simp] theorem targetAuxEncoding_width (n : Nat) :
    (encoding (residueEncoding n)).width = n + (n + (n + 1)) := by
  rfl

/-- Target-add-with-aux data plus VBE carry work in the physical
target/auxiliary/scratch/flag/work order. -/
def withCarryWorkEncoding (n : Nat) :
    BinaryLabelEncoding (Data (2 ^ n) × CarryWork n) :=
  BinaryLabelEncoding.prod (encoding (residueEncoding n)) (carryWorkEncoding n)

/-- Target-field bit lens in the target/auxiliary/scratch/flag layout. -/
def targetBit (n : Nat) (bit : Fin n) :
    EncodedBit (encoding (residueEncoding n)) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
        BinaryLabelEncoding.bool))
    (PlainAdder.Schedule.PowerOfTwo.wordBit n bit)

/-- Auxiliary-field bit lens in the target/auxiliary/scratch/flag layout. -/
def auxBit (n : Nat) (bit : Fin n) :
    EncodedBit (encoding (residueEncoding n)) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodLeftBit
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
        BinaryLabelEncoding.bool)
      (PlainAdder.Schedule.PowerOfTwo.wordBit n bit))

/-- Scratch/source-field bit lens in the target/auxiliary/scratch/flag layout. -/
def scratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (encoding (residueEncoding n)) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodLeftBit
        (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
        BinaryLabelEncoding.bool
        (PlainAdder.Schedule.PowerOfTwo.wordBit n bit)))

/-- Flag bit lens in the target/auxiliary/scratch/flag layout. -/
def flagBit (n : Nat) : EncodedBit (encoding (residueEncoding n)) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit
      (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
      (BinaryLabelEncoding.prod
        (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodRightBit
        (BinaryLabelEncoding.ofResidueEncoding (residueEncoding n))
        BinaryLabelEncoding.bool
        BinaryLabelEncoding.boolBit))

/-- Target-field bit lens lifted to target/auxiliary/scratch/flag/work. -/
def withCarryWorkTargetBit (n : Nat) (bit : Fin n) :
    EncodedBit (withCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (encoding (residueEncoding n))
    (carryWorkEncoding n) (targetBit n bit)

/-- Auxiliary-field bit lens lifted to target/auxiliary/scratch/flag/work. -/
def withCarryWorkAuxBit (n : Nat) (bit : Fin n) :
    EncodedBit (withCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (encoding (residueEncoding n))
    (carryWorkEncoding n) (auxBit n bit)

/-- Scratch/source-field bit lens lifted to target/auxiliary/scratch/flag/work. -/
def withCarryWorkScratchBit (n : Nat) (bit : Fin n) :
    EncodedBit (withCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (encoding (residueEncoding n))
    (carryWorkEncoding n) (scratchBit n bit)

/-- Flag bit lens lifted to target/auxiliary/scratch/flag/work. -/
def withCarryWorkFlagBit (n : Nat) :
    EncodedBit (withCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (encoding (residueEncoding n))
    (carryWorkEncoding n) (flagBit n)

/-- Carry-work bit lens in the target/auxiliary/scratch/flag/work layout. -/
def carryWorkBit (n : Nat) (bit : Fin (n - 1)) :
    EncodedBit (withCarryWorkEncoding n) :=
  BinaryLabelEncoding.prodRightBit (encoding (residueEncoding n))
    (carryWorkEncoding n)
    (BinaryLabelEncoding.finIdentityBit (n - 1) bit)

@[simp] theorem targetBit_get_testBit (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n)) :
    (targetBit n bit).get x = x.1.val.testBit bit.val := by
  rcases x with ⟨target, aux, scratch, flag⟩
  change (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get target =
    target.val.testBit bit.val
  exact PlainAdder.Schedule.PowerOfTwo.wordBit_get n bit target

@[simp] theorem auxBit_get_testBit (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n)) :
    (auxBit n bit).get x = x.2.1.val.testBit bit.val := by
  rcases x with ⟨target, aux, scratch, flag⟩
  change (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get aux =
    aux.val.testBit bit.val
  exact PlainAdder.Schedule.PowerOfTwo.wordBit_get n bit aux

@[simp] theorem scratchBit_get_testBit (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n)) :
    (scratchBit n bit).get x = x.2.2.1.val.testBit bit.val := by
  rcases x with ⟨target, aux, scratch, flag⟩
  change (PlainAdder.Schedule.PowerOfTwo.wordBit n bit).get scratch =
    scratch.val.testBit bit.val
  exact PlainAdder.Schedule.PowerOfTwo.wordBit_get n bit scratch

@[simp] theorem flagBit_get (n : Nat) (x : Data (2 ^ n)) :
    (flagBit n).get x = x.2.2.2 := by
  rcases x with ⟨target, aux, scratch, flag⟩
  rfl

@[simp] theorem withCarryWorkTargetBit_get_fst (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n) × CarryWork n) :
    (withCarryWorkTargetBit n bit).get x =
      x.1.1.val.testBit bit.val := by
  rcases x with ⟨data, work⟩
  change (targetBit n bit).get data = data.1.val.testBit bit.val
  exact targetBit_get_testBit n bit data

@[simp] theorem withCarryWorkAuxBit_get_fst (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n) × CarryWork n) :
    (withCarryWorkAuxBit n bit).get x =
      x.1.2.1.val.testBit bit.val := by
  rcases x with ⟨data, work⟩
  change (auxBit n bit).get data = data.2.1.val.testBit bit.val
  exact auxBit_get_testBit n bit data

@[simp] theorem withCarryWorkScratchBit_get_fst (n : Nat) (bit : Fin n)
    (x : Data (2 ^ n) × CarryWork n) :
    (withCarryWorkScratchBit n bit).get x =
      x.1.2.2.1.val.testBit bit.val := by
  rcases x with ⟨data, work⟩
  change (scratchBit n bit).get data = data.2.2.1.val.testBit bit.val
  exact scratchBit_get_testBit n bit data

@[simp] theorem withCarryWorkFlagBit_get_fst (n : Nat)
    (x : Data (2 ^ n) × CarryWork n) :
    (withCarryWorkFlagBit n).get x = x.1.2.2.2 := by
  rcases x with ⟨data, work⟩
  change (flagBit n).get data = data.2.2.2
  exact flagBit_get n data

@[simp] theorem carryWorkBit_get_snd (n : Nat) (bit : Fin (n - 1))
    (x : Data (2 ^ n) × CarryWork n) :
    (carryWorkBit n bit).get x =
      (BinaryLabelEncoding.finIdentityBit (n - 1) bit).get x.2 := by
  rfl

theorem carryWorkBit_get_clean (n : Nat) (bit : Fin (n - 1))
    (x : Data (2 ^ n)) :
    (carryWorkBit n bit).get (x, cleanCarryWork n) = false := by
  change
    (BinaryLabelEncoding.finIdentityBit (n - 1) bit).get
      (cleanCarryWork n) = false
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero (n - 1) bit

/-- Scratch/source word in the target/auxiliary/scratch/flag/work layout. -/
def withCarryWorkScratchWord (n : Nat) :
    EncodedBit.Word (withCarryWorkEncoding n) n where
  bit := withCarryWorkScratchBit n

/-- Target word in the target/auxiliary/scratch/flag/work layout. -/
def withCarryWorkTargetWord (n : Nat) :
    EncodedBit.Word (withCarryWorkEncoding n) n where
  bit := withCarryWorkTargetBit n

/-- Auxiliary word in the target/auxiliary/scratch/flag/work layout. -/
def withCarryWorkAuxWord (n : Nat) :
    EncodedBit.Word (withCarryWorkEncoding n) n where
  bit := withCarryWorkAuxBit n

/-- Temporary carry-work word in the target/auxiliary/scratch/flag/work layout. -/
def carryWorkWord (n : Nat) :
    EncodedBit.Word (withCarryWorkEncoding n) (n - 1) where
  bit := carryWorkBit n

@[simp] theorem withCarryWorkTargetBit_wire_val (n : Nat) (bit : Fin n) :
    ((withCarryWorkTargetBit n bit).wire).val = n - 1 - bit.val := by
  rfl

@[simp] theorem withCarryWorkAuxBit_wire_val (n : Nat) (bit : Fin n) :
    ((withCarryWorkAuxBit n bit).wire).val = n + (n - 1 - bit.val) := by
  rfl

@[simp] theorem withCarryWorkScratchBit_wire_val (n : Nat) (bit : Fin n) :
    ((withCarryWorkScratchBit n bit).wire).val =
      n + n + (n - 1 - bit.val) := by
  change n + (n + (n - 1 - bit.val)) =
    n + n + (n - 1 - bit.val)
  omega

@[simp] theorem withCarryWorkFlagBit_wire_val (n : Nat) :
    ((withCarryWorkFlagBit n).wire).val = n + n + n := by
  change n + (n + n) = n + n + n
  omega

@[simp] theorem carryWorkBit_wire_val (n : Nat) (bit : Fin (n - 1)) :
    ((carryWorkBit n bit).wire).val =
      (encoding (residueEncoding n)).width + bit.val := by
  rfl

/-- VBE carry-work layout specialized to the target/auxiliary/scratch/flag
physical order.  The auxiliary field is not part of the adder layout; it is
proved untouched separately by wire preservation [VBE95,
9511018.tex:237-264,591-618]. -/
def carryWorkLayout (n : Nat) :
    PlainAdder.Schedule.CarryWorkLayout (encoding := withCarryWorkEncoding n) n where
  left := withCarryWorkScratchWord n
  right := withCarryWorkTargetWord n
  carryIn := withCarryWorkFlagBit n
  workCarry := carryWorkWord n
  leftLeft_ne := by
    intro i j hij
    change (withCarryWorkScratchBit n i).wire ≠
      (withCarryWorkScratchBit n j).wire
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [withCarryWorkScratchBit_wire_val] at hv
    omega
  rightRight_ne := by
    intro i j hij
    change (withCarryWorkTargetBit n i).wire ≠
      (withCarryWorkTargetBit n j).wire
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [withCarryWorkTargetBit_wire_val] at hv
    omega
  leftRight_ne := by
    intro i j
    change (withCarryWorkScratchBit n i).wire ≠
      (withCarryWorkTargetBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := j.isLt
    simp only [withCarryWorkScratchBit_wire_val,
      withCarryWorkTargetBit_wire_val] at hv
    omega
  leftCarryIn_ne := by
    intro i
    change (withCarryWorkScratchBit n i).wire ≠
      (withCarryWorkFlagBit n).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkScratchBit_wire_val,
      withCarryWorkFlagBit_wire_val] at hv
    omega
  rightCarryIn_ne := by
    intro i
    change (withCarryWorkTargetBit n i).wire ≠
      (withCarryWorkFlagBit n).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkTargetBit_wire_val,
      withCarryWorkFlagBit_wire_val] at hv
    omega
  leftWork_ne := by
    intro i j
    change (withCarryWorkScratchBit n i).wire ≠ (carryWorkBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkScratchBit_wire_val, carryWorkBit_wire_val,
      targetAuxEncoding_width] at hv
    omega
  rightWork_ne := by
    intro i j
    change (withCarryWorkTargetBit n i).wire ≠ (carryWorkBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    have hlt := i.isLt
    simp only [withCarryWorkTargetBit_wire_val, carryWorkBit_wire_val,
      targetAuxEncoding_width] at hv
    omega
  carryInWork_ne := by
    intro j
    change (withCarryWorkFlagBit n).wire ≠ (carryWorkBit n j).wire
    intro h
    have hv := congrArg Fin.val h
    simp only [withCarryWorkFlagBit_wire_val, carryWorkBit_wire_val,
      targetAuxEncoding_width] at hv
    omega
  workWork_ne := by
    intro i j hij
    change (carryWorkBit n i).wire ≠ (carryWorkBit n j).wire
    intro h
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [carryWorkBit_wire_val] at hv
    omega

@[simp] theorem auxTarget_ne (n : Nat) (aux target : Fin n) :
    (withCarryWorkAuxBit n aux).wire ≠
      (withCarryWorkTargetBit n target).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hlt := target.isLt
  simp only [withCarryWorkAuxBit_wire_val,
    withCarryWorkTargetBit_wire_val] at hv
  omega

@[simp] theorem auxWork_ne (n : Nat) (aux : Fin n) (work : Fin (n - 1)) :
    (withCarryWorkAuxBit n aux).wire ≠ (carryWorkBit n work).wire := by
  intro h
  have hv := congrArg Fin.val h
  have hlt := aux.isLt
  simp only [withCarryWorkAuxBit_wire_val, carryWorkBit_wire_val,
    targetAuxEncoding_width] at hv
  omega

@[simp] theorem carryWorkLayout_carryInput_get_clean
    (n : Nat) (j : Fin (n - 1)) (x : Data (2 ^ n)) :
    (PlainAdder.Schedule.CarryWorkLayout.carryInput (carryWorkLayout n) j).get
        (x, cleanCarryWork n) =
      if j.val = 0 then x.2.2.2 else false := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
  by_cases h : j.val = 0
  · simp [h, carryWorkLayout]
  · simpa [h, carryWorkLayout, carryWorkWord] using
      carryWorkBit_get_clean n
        (PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j h) x

/-- Folded carry/sum/cleanup gate list for target-add-with-aux with clean carry
work. -/
def cleanCarrySumGates (n : Nat) :
    List (EncodedBit.GateSpec (withCarryWorkEncoding n)) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates (carryWorkLayout n)

/-- Base-gate program for target-add-with-aux with clean carry work. -/
def cleanCarrySumProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (withCarryWorkEncoding n).width).toQuantum :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumProgram (carryWorkLayout n)

/-- Folded semantic action for target-add-with-aux with clean carry work. -/
def cleanCarrySumStep (n : Nat) :
    Data (2 ^ n) × CarryWork n -> Data (2 ^ n) × CarryWork n :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep (carryWorkLayout n)

/-- The target-add-with-aux carry-work schedule is realized by the same folded
base-gate program used for resources. -/
theorem cleanCarrySum_realizes (n : Nat) :
    UnitaryCircuit.Realizes (withCarryWorkEncoding n)
      (cleanCarrySumProgram n) (cleanCarrySumStep n) :=
  PlainAdder.Schedule.CarryWorkLayout.cleanCarrySum_realizes (carryWorkLayout n)

theorem carryStageIndexStep_get_workCarry_recurrence_testBit
    (n : Nat) (j : Fin (n - 1)) (x : Data (2 ^ n)) :
    (carryWorkBit n j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (carryWorkLayout n) (x, cleanCarryWork n)) =
      Bool.carry
        (x.2.2.1.val.testBit j.val)
        (x.1.val.testBit j.val)
        ((PlainAdder.Schedule.CarryWorkLayout.carryInput (carryWorkLayout n) j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (carryWorkLayout n) (x, cleanCarryWork n))) := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_workCarry_recurrence
      (carryWorkLayout n) j (x, cleanCarryWork n)
      (by
        intro k
        exact carryWorkBit_get_clean n k x)
  simpa [carryWorkLayout, carryWorkWord, withCarryWorkScratchWord,
    withCarryWorkTargetWord, PlainAdder.Schedule.CarryWorkLayout.lowIndex] using h

/-- The forward carry pass computes the propagated carry for the scratch+target
sum on clean flag/work inputs [VBE95, 9511018.tex:237-264,591-618]. -/
theorem carryStageIndexStep_get_workCarry_natAddCarry
    (n : Nat) (j : Fin (n - 1)) (x : Data (2 ^ n))
    (hflag : x.2.2.2 = false) :
    (carryWorkBit n j).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (carryWorkLayout n) (x, cleanCarryWork n)) =
      Nat.BinaryArithmetic.natAddCarry
        x.2.2.1.val x.1.val (j.val + 1) := by
  let stage :=
    PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
      (carryWorkLayout n) (x, cleanCarryWork n)
  change (carryWorkBit n j).get stage =
    Nat.BinaryArithmetic.natAddCarry x.2.2.1.val x.1.val
      (j.val + 1)
  have hmain : forall m, forall j : Fin (n - 1), j.val = m ->
      (carryWorkBit n j).get stage =
        Nat.BinaryArithmetic.natAddCarry
          x.2.2.1.val x.1.val (j.val + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro j hjm
        have hrec :=
          carryStageIndexStep_get_workCarry_recurrence_testBit n j x
        change (carryWorkBit n j).get stage =
          Nat.BinaryArithmetic.natAddCarry
            x.2.2.1.val x.1.val (j.val + 1)
        rw [hrec]
        unfold PlainAdder.Schedule.CarryWorkLayout.carryInput
        by_cases hzero : j.val = 0
        · rw [dif_pos hzero]
          have hdata :=
            PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
              (carryWorkLayout n) (x, cleanCarryWork n)
          rw [hdata]
          simp [carryWorkLayout, hflag,
            Nat.BinaryArithmetic.natAddCarry, hzero]
        · rw [dif_neg hzero]
          let p := PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex j hzero
          have hpLt : p.val < m := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          have hpRec := ih p.val hpLt p rfl
          have hpSucc : p.val + 1 = j.val := by
            dsimp [p, PlainAdder.Schedule.CarryWorkLayout.previousWorkIndex]
            omega
          change
            Bool.carry (x.2.2.1.val.testBit j.val) (x.1.val.testBit j.val)
              ((carryWorkBit n p).get stage) =
            Nat.BinaryArithmetic.natAddCarry
              x.2.2.1.val x.1.val (j.val + 1)
          rw [hpRec, hpSucc]
          simp [Nat.BinaryArithmetic.natAddCarry]
  exact hmain j.val j rfl

/-- The carry selected before target bit `i` is the propagated natural carry
for the scratch+target sum. -/
theorem carryBeforeSum_get_natAddCarry
    (n : Nat) (i : Fin n) (x : Data (2 ^ n)) (hflag : x.2.2.2 = false) :
    (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum (carryWorkLayout n) i).get
        (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
          (carryWorkLayout n) (x, cleanCarryWork n)) =
      Nat.BinaryArithmetic.natAddCarry x.2.2.1.val x.1.val i.val := by
  unfold PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum
  by_cases hzero : i.val = 0
  · rw [dif_pos hzero]
    have hdata :=
      PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep_get_dataCarry
        (carryWorkLayout n) (x, cleanCarryWork n)
    rw [hdata]
    simp [carryWorkLayout, hflag,
      Nat.BinaryArithmetic.natAddCarry, hzero]
  · rw [dif_neg hzero]
    have hjLt : i.val - 1 < n - 1 := by
      have hi := i.isLt
      omega
    let j : Fin (n - 1) := { val := i.val - 1, isLt := hjLt }
    have hwork :=
      carryStageIndexStep_get_workCarry_natAddCarry n j x hflag
    have hjSucc : j.val + 1 = i.val := by
      dsimp [j]
      omega
    change
      (carryWorkBit n j).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (carryWorkLayout n) (x, cleanCarryWork n)) =
        Nat.BinaryArithmetic.natAddCarry x.2.2.1.val x.1.val i.val
    rw [hwork, hjSucc]

/-- Target-bit formula for the target/auxiliary/scratch/flag cleanup-aware
carry/sum schedule. -/
theorem cleanCarrySumStep_get_target_testBit
    (n : Nat) (i : Fin n) (x : Data (2 ^ n)) :
    (Prod.fst
        (cleanCarrySumStep n (x, cleanCarryWork n))).1.val.testBit i.val =
      ((x.1.val.testBit i.val ^^ x.2.2.1.val.testBit i.val) ^^
        (PlainAdder.Schedule.CarryWorkLayout.carryBeforeSum (carryWorkLayout n) i).get
          (PlainAdder.Schedule.CarryWorkLayout.carryStageIndexStep
            (carryWorkLayout n) (x, cleanCarryWork n))) := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_right
      (carryWorkLayout n) i (x, cleanCarryWork n)
  rw [PlainAdder.Schedule.CarryWorkLayout.carryStage_stepList_eq_indexStep] at h
  simpa [cleanCarrySumStep, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout, carryWorkWord, withCarryWorkTargetWord,
    withCarryWorkScratchWord] using h

/-- On clean flag/work inputs, the target word is updated by adding the scratch
word. -/
theorem cleanCarrySumStep_get_target_add
    (n : Nat) (x : Data (2 ^ n)) (hflag : x.2.2.2 = false) :
    (Prod.fst (cleanCarrySumStep n (x, cleanCarryWork n))).1 =
      (step x).1 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro i
  rw [cleanCarrySumStep_get_target_testBit]
  rw [carryBeforeSum_get_natAddCarry n i x hflag]
  simp [step]
  simpa [Bool.xor_assoc] using
    (PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
      n x.2.2.1 x.1 i).symm

/-- The cleanup-aware target-add-with-aux schedule preserves the auxiliary
word because no gate targets its wires. -/
theorem cleanCarrySumStep_get_aux
    (n : Nat) (x : Data (2 ^ n)) :
    (Prod.fst (cleanCarrySumStep n (x, cleanCarryWork n))).2.1 = x.2.1 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro i
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_observed_of_right_work_ne
      (carryWorkLayout n) (withCarryWorkAuxBit n i)
      (by
        intro target
        exact Ne.symm (auxTarget_ne n i target))
      (by
        intro work
        exact Ne.symm (auxWork_ne n i work))
      (x, cleanCarryWork n)
  simpa [cleanCarrySumStep, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout, withCarryWorkAuxWord] using h

/-- The cleanup-aware target-add-with-aux schedule preserves the scratch/source
word. -/
theorem cleanCarrySumStep_get_scratch
    (n : Nat) (x : Data (2 ^ n)) :
    (Prod.fst (cleanCarrySumStep n (x, cleanCarryWork n))).2.2.1 =
      x.2.2.1 := by
  apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
  intro i
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_left
      (carryWorkLayout n) i (x, cleanCarryWork n)
  simpa [cleanCarrySumStep, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout, carryWorkWord, withCarryWorkScratchWord] using h

/-- The cleanup-aware target-add-with-aux schedule preserves the flag bit. -/
theorem cleanCarrySumStep_get_flag
    (n : Nat) (x : Data (2 ^ n)) :
    (Prod.fst (cleanCarrySumStep n (x, cleanCarryWork n))).2.2.2 =
      x.2.2.2 := by
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_dataCarry
      (carryWorkLayout n) (x, cleanCarryWork n)
  simpa [cleanCarrySumStep, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
    carryWorkLayout] using h

/-- The cleanup-aware target-add-with-aux schedule restores the carry-work
register. -/
theorem cleanCarrySumStep_get_work_clean
    (n : Nat) (x : Data (2 ^ n)) :
    Prod.snd (cleanCarrySumStep n (x, cleanCarryWork n)) =
      cleanCarryWork n := by
  apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
  intro bit
  have h :=
    PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumGates_get_workCarry_clean
      (carryWorkLayout n) bit (x, cleanCarryWork n)
      (by
        intro k
        exact carryWorkBit_get_clean n k x)
  have hbit :
      (carryWorkBit n bit).get
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (carryWorkLayout n) (x, cleanCarryWork n)) =
        false := by
    simpa [PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep,
      carryWorkLayout, carryWorkWord] using h
  change
    (BinaryLabelEncoding.finIdentityBit (n - 1) bit).get
      (Prod.snd
        (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
          (carryWorkLayout n) (x, cleanCarryWork n))) =
      false
  rw [← carryWorkBit_get_snd n bit
    (PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep
      (carryWorkLayout n) (x, cleanCarryWork n))]
  simpa [cleanCarrySumStep, PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumStep]
    using hbit

/-- Full clean endpoint for target-add-with-aux with VBE carry work.  The
statement is conditional on clean flag/work inputs, matching the reusable
plain-adder carry convention [VBE95, 9511018.tex:237-264,591-618]. -/
theorem cleanCarrySumStep_cleanEndpoint
    (n : Nat) (x : Data (2 ^ n)) (hflag : x.2.2.2 = false) :
    cleanCarrySumStep n (x, cleanCarryWork n) =
      (step x, cleanCarryWork n) := by
  apply Prod.ext
  · let y := Prod.fst (cleanCarrySumStep n (x, cleanCarryWork n))
    have htarget : y.1 = (step x).1 :=
      cleanCarrySumStep_get_target_add n x hflag
    have haux : y.2.1 = x.2.1 :=
      cleanCarrySumStep_get_aux n x
    have hscratch : y.2.2.1 = x.2.2.1 :=
      cleanCarrySumStep_get_scratch n x
    have hflag' : y.2.2.2 = x.2.2.2 :=
      cleanCarrySumStep_get_flag n x
    change y = step x
    clear_value y
    rcases y with ⟨target', aux', scratch', flag'⟩
    rcases x with ⟨target, aux, scratch, flag⟩
    change target' = target + scratch at htarget
    change aux' = aux at haux
    change scratch' = scratch at hscratch
    change flag' = flag at hflag'
    change (target', (aux', (scratch', flag'))) =
      (target + scratch, (aux, (scratch, flag)))
    rw [htarget, haux, hscratch, hflag']
  · exact cleanCarrySumStep_get_work_clean n x

/-- Clean-work target-add-with-aux witness used by decomposed MAU callers before
a no-work all-flags target-add-with-aux program is available. -/
structure CleanWorkWitness (n : Nat) where
  /-- Distinguished clean work label. -/
  cleanWork : CarryWork n
  /-- Folded full-register semantic action. -/
  stepWithWork : Data (2 ^ n) × CarryWork n -> Data (2 ^ n) × CarryWork n
  /-- Actual folded full-register program. -/
  program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (withCarryWorkEncoding n).width).toQuantum
  /-- Direct realization of the folded full-register action. -/
  realizes :
    UnitaryCircuit.Realizes (withCarryWorkEncoding n) program stepWithWork
  /-- Clean endpoint for target-add-with-aux when flag/work start clean. -/
  cleanEndpoint :
    ∀ x : Data (2 ^ n), x.2.2.2 = false ->
      stepWithWork (x, cleanWork) = (step x, cleanWork)

/-- VBE carry-work target-add-with-aux witness in the
target/auxiliary/scratch/flag/work layout.  Resource and correctness
projections are tied to `program` [VBE95,
9511018.tex:237-264,591-618]. -/
def cleanWorkWitness (n : Nat) : CleanWorkWitness n where
  cleanWork := cleanCarryWork n
  stepWithWork := cleanCarrySumStep n
  program := cleanCarrySumProgram n
  realizes := cleanCarrySum_realizes n
  cleanEndpoint := cleanCarrySumStep_cleanEndpoint n

end PowerOfTwo

namespace Mod2
-- Declaration-scoped exception: a transparent named encoding parameter for circuit construction.
set_option linter.defProp false in
/-- One-bit canonical residue encoding for `ZMod 2`. -/
def residueEncoding : BinaryResidueEncoding 2 1 where
  modulus_pos := by decide
  register_fits := by decide

/-- One CNOT implements target update over `ZMod 2`, preserving the auxiliary
field. -/
def cnotProgram :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding residueEncoding).width).toQuantum :=
  RawLayout.cnotScratchToTarget residueEncoding ⟨0, by decide⟩

/-- Raw canonical-label action of the one-CNOT `ZMod 2` target update with an
untouched auxiliary field. -/
theorem cnotProgram_applyNormalized_encode_eq
    (target aux scratch : ZMod 2) (flag : Bool) :
    cnotProgram.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical
              (encoding residueEncoding).width).basisEquiv.symm
            ((encoding residueEncoding).encode
              (target, (aux, (scratch, flag)))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
            (encoding residueEncoding).width).basisEquiv.symm
          ((encoding residueEncoding).encode
            (step (target, (aux, (scratch, flag)))))) := by
  rw [cnotProgram, RawLayout.cnotScratchToTarget,
    QubitPrimitive.circuit_applyNormalized_ket]
  congr 1
  fin_cases target <;> fin_cases aux <;> fin_cases scratch <;> cases flag <;>
    decide

/-- End-to-end raw witness for the one-bit modular-add target update with an
auxiliary field. -/
def rawCanonicalWitness : RawCanonicalWitness residueEncoding where
  program := cnotProgram
  applyNormalized_encode_eq := cnotProgram_applyNormalized_encode_eq

/-- Semantic witness obtained from the same one-CNOT raw program. -/
def witness : Witness residueEncoding :=
  rawCanonicalWitness.toWitness

end Mod2

namespace Mod4
-- Declaration-scoped exception: a transparent named encoding parameter for circuit construction.
set_option linter.defProp false in
/-- Two-bit canonical residue encoding for `ZMod 4`. -/
def residueEncoding : BinaryResidueEncoding 4 2 where
  modulus_pos := by decide
  register_fits := by decide

/-- Least-significant target bit in the packed target/auxiliary/scratch/flag
layout. -/
def targetLSB : Fin (encoding residueEncoding).width :=
  RawLayout.targetWire residueEncoding ⟨1, by decide⟩

/-- Most-significant target bit in the packed target/auxiliary/scratch/flag
layout. -/
def targetMSB : Fin (encoding residueEncoding).width :=
  RawLayout.targetWire residueEncoding ⟨0, by decide⟩

/-- Least-significant scratch/source bit in the packed
target/auxiliary/scratch/flag layout. -/
def scratchLSB : Fin (encoding residueEncoding).width :=
  RawLayout.scratchWire residueEncoding ⟨1, by decide⟩

/-- Most-significant scratch/source bit in the packed
target/auxiliary/scratch/flag layout. -/
def scratchMSB : Fin (encoding residueEncoding).width :=
  RawLayout.scratchWire residueEncoding ⟨0, by decide⟩

/-- Two-bit ripple-carry target update over `ZMod 4`, preserving the auxiliary
field. -/
def rippleProgram :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding residueEncoding).width).toQuantum :=
  RawLayout.twoBitRippleProgram residueEncoding
    ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)

/-- Raw canonical-label action of the two-bit ripple-carry `ZMod 4` target
update with an untouched auxiliary field. -/
theorem rippleProgram_applyNormalized_encode_eq
    (target aux scratch : ZMod 4) (flag : Bool) :
    rippleProgram.applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical
              (encoding residueEncoding).width).basisEquiv.symm
            ((encoding residueEncoding).encode
              (target, (aux, (scratch, flag)))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
            (encoding residueEncoding).width).basisEquiv.symm
          ((encoding residueEncoding).encode
            (step (target, (aux, (scratch, flag)))))) := by
  rw [rippleProgram, RawLayout.twoBitRippleProgram,
    BitSlice.Raw.targetAdd2Program, UnitaryCircuit.applyNormalized_seq,
    UnitaryCircuit.applyNormalized_seq,
    QubitPrimitive.circuit_applyNormalized_ket,
    QubitPrimitive.circuit_applyNormalized_ket,
    QubitPrimitive.circuit_applyNormalized_ket]
  apply congrArg (fun label : Fin (2 ^ (encoding residueEncoding).width) =>
    NormalizedVector.ket
      ((QubitLayout.canonical (encoding residueEncoding).width).basisEquiv.symm label))
  fin_cases target <;> fin_cases aux <;> fin_cases scratch <;> cases flag <;>
    decide

/-- End-to-end raw witness for the two-bit modular-add target update with an
auxiliary field. -/
def rawCanonicalWitness : RawCanonicalWitness residueEncoding where
  program := rippleProgram
  applyNormalized_encode_eq := rippleProgram_applyNormalized_encode_eq

/-- Semantic witness obtained from the same two-bit ripple raw program. -/
def witness : Witness residueEncoding :=
  rawCanonicalWitness.toWitness

end Mod4

end TargetAddWithAux

end

end MAU.Addition
end QuantumAlg

end
