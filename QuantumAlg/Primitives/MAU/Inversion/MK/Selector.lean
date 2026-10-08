/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Primitives.MAU.Inversion.MK.DataPath.Coefficient
import all QuantumAlg.Primitives.MAU.Inversion.MK.DataPath.Shift

/-!
# Branch selector

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

/-- Concrete borrow-chain layout comparing the RNSL17 `u` and `v` words inside
the Montgomery--Kaliski work register.  The layout wires the reusable
subtract-borrow gate slices to `u`, `v`, the clean comparison ancilla, and the
separate comparison-work word [RNSL17, ECDLP.tex:399-421,468-475]. -/
def comparisonBorrowLayout (n counterWidth : Nat) :
    QuantumAlg.Comparator.BorrowWorkLayout
      (encoding := registersWithComparisonWorkEncoding n counterWidth) n where
  minuend := liftedUWord n counterWidth
  subtrahend := liftedVWord n counterWidth
  initialBorrow := liftedCompareBit n counterWidth
  workBorrow := liftedComparisonCarryWord n counterWidth
  minuendMinuend_ne := by
    intro i j hij
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i)
      (RegisterBits.uValueBit n counterWidth j)
      (u_u_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j)
        (littleEndianWire_ne hij))
  subtrahendSubtrahend_ne := by
    intro i j hij
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i)
      (RegisterBits.vValueBit n counterWidth j)
      (v_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j)
        (littleEndianWire_ne hij))
  minuendSubtrahend_ne := by
    intro i j
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i)
      (RegisterBits.vValueBit n counterWidth j)
      (RegisterBits.u_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j))
  minuendInitialBorrow_ne := by
    intro i
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.u_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire i))
  subtrahendInitialBorrow_ne := by
    intro i
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.v_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire i))
  minuendWork_ne := by
    intro i j
    exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i) (comparisonCarryValueBit n j)
  subtrahendWork_ne := by
    intro i j
    exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i) (comparisonCarryValueBit n j)
  initialBorrowWork_ne := by
    intro j
    exact liftedCompare_liftedComparisonCarry_wire_ne n counterWidth j
  workWork_ne := by
    intro i j hij
    exact liftComparisonWorkBit_liftComparisonWorkBit_wire_ne n counterWidth
      (comparisonCarryValueBit n i) (comparisonCarryValueBit n j)
      (comparisonCarryValue_comparisonCarryValue_wire_ne n i j hij)

/-- Concrete borrow-chain layout comparing `v - u` inside the
Montgomery--Kaliski work register.  This is the orientation needed for the
RNSL17 odd-branch selector predicate `u > v`, because the final borrow of
`v - u` is `v < u` [RNSL17, ECDLP.tex:399-421,468-475]. -/
def comparisonBorrowLayoutVU (n counterWidth : Nat) :
    QuantumAlg.Comparator.BorrowWorkLayout
      (encoding := registersWithComparisonWorkEncoding n counterWidth) n where
  minuend := liftedVWord n counterWidth
  subtrahend := liftedUWord n counterWidth
  initialBorrow := liftedCompareBit n counterWidth
  workBorrow := liftedComparisonCarryWord n counterWidth
  minuendMinuend_ne := by
    intro i j hij
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i)
      (RegisterBits.vValueBit n counterWidth j)
      (v_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j)
        (littleEndianWire_ne hij))
  subtrahendSubtrahend_ne := by
    intro i j hij
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i)
      (RegisterBits.uValueBit n counterWidth j)
      (u_u_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j)
        (littleEndianWire_ne hij))
  minuendSubtrahend_ne := by
    intro i j
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i)
      (RegisterBits.uValueBit n counterWidth j)
      (Ne.symm
        (RegisterBits.u_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire j)
          (WireAddress.littleEndianWire i)))
  minuendInitialBorrow_ne := by
    intro i
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.v_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire i))
  subtrahendInitialBorrow_ne := by
    intro i
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i)
      (RegisterBits.compareBit n counterWidth)
      (RegisterBits.u_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire i))
  minuendWork_ne := by
    intro i j
    exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i) (comparisonCarryValueBit n j)
  subtrahendWork_ne := by
    intro i j
    exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i) (comparisonCarryValueBit n j)
  initialBorrowWork_ne := by
    intro j
    exact liftedCompare_liftedComparisonCarry_wire_ne n counterWidth j
  workWork_ne := by
    intro i j hij
    exact liftComparisonWorkBit_liftComparisonWorkBit_wire_ne n counterWidth
      (comparisonCarryValueBit n i) (comparisonCarryValueBit n j)
      (comparisonCarryValue_comparisonCarryValue_wire_ne n i j hij)

/-- Concrete `v - u` borrow-chain layout whose clean initial borrow is the
independent `scratchA` ancilla rather than `compare`.  This orientation and
ancilla choice are what make a later compute-copy-uncompute selector possible:
`compare` can receive the final borrow while the borrow stage still sees the
same clean initial borrow during cleanup [RNSL17, ECDLP.tex:399-421,468-475]. -/
def uGreaterBorrowLayout (n counterWidth : Nat) :
    QuantumAlg.Comparator.BorrowWorkLayout
      (encoding := registersWithComparisonWorkEncoding n counterWidth) n where
  minuend := liftedVWord n counterWidth
  subtrahend := liftedUWord n counterWidth
  initialBorrow := liftedScratchABit n counterWidth
  workBorrow := liftedComparisonCarryWord n counterWidth
  minuendMinuend_ne := by
    intro i j hij
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i)
      (RegisterBits.vValueBit n counterWidth j)
      (v_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j)
        (littleEndianWire_ne hij))
  subtrahendSubtrahend_ne := by
    intro i j hij
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i)
      (RegisterBits.uValueBit n counterWidth j)
      (u_u_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j)
        (littleEndianWire_ne hij))
  minuendSubtrahend_ne := by
    intro i j
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i)
      (RegisterBits.uValueBit n counterWidth j)
      (Ne.symm
        (RegisterBits.u_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire j)
          (WireAddress.littleEndianWire i)))
  minuendInitialBorrow_ne := by
    intro i
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i)
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.v_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire i))
  subtrahendInitialBorrow_ne := by
    intro i
    exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i)
      (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.u_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire i))
  minuendWork_ne := by
    intro i j
    exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i) (comparisonCarryValueBit n j)
  subtrahendWork_ne := by
    intro i j
    exact liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i) (comparisonCarryValueBit n j)
  initialBorrowWork_ne := by
    intro j
    exact liftedScratchA_liftedComparisonCarry_wire_ne n counterWidth j
  workWork_ne := by
    intro i j hij
    exact liftComparisonWorkBit_liftComparisonWorkBit_wire_ne n counterWidth
      (comparisonCarryValueBit n i) (comparisonCarryValueBit n j)
      (comparisonCarryValue_comparisonCarryValue_wire_ne n i j hij)

/-- One concrete subtract-borrow slice of the Kaliski comparison layout. -/
def comparisonBorrowOutGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowOutGatesAt
    (comparisonBorrowLayout n counterWidth) bit

/-- Base-gate program for one Kaliski comparison borrow-output slice. -/
def comparisonBorrowOutProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowOutProgramAt
    (comparisonBorrowLayout n counterWidth) bit

/-- Semantic step for one Kaliski comparison borrow-output slice. -/
def comparisonBorrowOutStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithComparisonWork n counterWidth →
      RegistersWithComparisonWork n counterWidth :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowOutStepAt
    (comparisonBorrowLayout n counterWidth) bit

/-- The Kaliski comparison borrow-output slice is a concrete base-gate
realization over the register-plus-comparison-work encoding. -/
theorem comparisonBorrowOut_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (comparisonBorrowOutProgram n counterWidth bit)
      (comparisonBorrowOutStep n counterWidth bit) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowOut_realizesAt
    (comparisonBorrowLayout n counterWidth) bit

/-- On clean comparison work, one Kaliski comparison borrow slice writes the
local subtract-borrow recurrence into its selected work bit. -/
theorem comparisonBorrowOutStep_get_work_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hclean :
      (liftedComparisonCarryBit n counterWidth bit).get x = false) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (comparisonBorrowOutStep n counterWidth bit x) =
      Bool.carry
        (!(liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.uValueBit n counterWidth bit)).get x)
        ((liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.vValueBit n counterWidth bit)).get x)
        ((QuantumAlg.Comparator.BorrowWorkLayout.borrowInput
          (comparisonBorrowLayout n counterWidth) bit).get x) := by
  simpa [comparisonBorrowOutStep, comparisonBorrowLayout, liftedUWord,
    liftedVWord, liftedComparisonCarryWord]
    using
      QuantumAlg.Comparator.BorrowWorkLayout.borrowOutGatesAt_get_workBorrow_clean
        (comparisonBorrowLayout n counterWidth) bit x hclean

/-- One Kaliski comparison borrow slice preserves the selected `u` input bit. -/
theorem comparisonBorrowOutStep_get_uBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.uValueBit n counterWidth bit)).get
        (comparisonBorrowOutStep n counterWidth bit x) =
      (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.uValueBit n counterWidth bit)).get x := by
  simpa [comparisonBorrowOutStep, comparisonBorrowLayout, liftedUWord,
    liftedVWord, liftedComparisonCarryWord]
    using
      QuantumAlg.Comparator.BorrowWorkLayout.borrowOutGatesAt_get_minuend
        (comparisonBorrowLayout n counterWidth) bit x

/-- One Kaliski comparison borrow slice preserves the selected `v` input bit. -/
theorem comparisonBorrowOutStep_get_vBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.vValueBit n counterWidth bit)).get
        (comparisonBorrowOutStep n counterWidth bit x) =
      (liftRegisterBitToComparisonWork n counterWidth
        (RegisterBits.vValueBit n counterWidth bit)).get x := by
  simpa [comparisonBorrowOutStep, comparisonBorrowLayout, liftedUWord,
    liftedVWord, liftedComparisonCarryWord]
    using
      QuantumAlg.Comparator.BorrowWorkLayout.borrowOutGatesAt_get_subtrahend
        (comparisonBorrowLayout n counterWidth) bit x

/-- Folded forward borrow-chain gate list for the Kaliski `u - v` comparison
workspace.  This is the concrete comparator work pass; the final branch
condition invariant is a separate proof obligation for this gate object [RNSL17,
ECDLP.tex:399-421,468-475]. -/
def comparisonBorrowStageGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStage
    (comparisonBorrowLayout n counterWidth)

/-- Base-gate program for the folded Kaliski comparison borrow-chain pass. -/
def comparisonBorrowStageProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStageProgram
    (comparisonBorrowLayout n counterWidth)

/-- Folded semantic action of the Kaliski comparison borrow-chain pass. -/
def comparisonBorrowStageStep (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth →
      RegistersWithComparisonWork n counterWidth :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStageStep
    (comparisonBorrowLayout n counterWidth)

/-- The folded Kaliski comparison borrow-chain pass is a concrete base-gate
realization over the register-plus-comparison-work encoding. -/
theorem comparisonBorrowStage_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (comparisonBorrowStageProgram n counterWidth)
      (comparisonBorrowStageStep n counterWidth) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_realizes
    (comparisonBorrowLayout n counterWidth)

/-- Folded forward borrow-chain gate list for the Kaliski `v - u` comparison
workspace.  This is the comparison orientation used to stage the `uGreater`
selector condition [RNSL17, ECDLP.tex:399-421,468-475]. -/
def comparisonBorrowStageVUGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStage
    (comparisonBorrowLayoutVU n counterWidth)

/-- Base-gate program for the folded `v - u` comparison borrow-chain pass. -/
def comparisonBorrowStageVUProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStageProgram
    (comparisonBorrowLayoutVU n counterWidth)

/-- Folded semantic action of the `v - u` comparison borrow-chain pass. -/
def comparisonBorrowStageVUStep (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth →
      RegistersWithComparisonWork n counterWidth :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStageStep
    (comparisonBorrowLayoutVU n counterWidth)

/-- The folded `v - u` comparison borrow-chain pass is a concrete base-gate
realization over the register-plus-comparison-work encoding. -/
theorem comparisonBorrowStageVU_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (comparisonBorrowStageVUProgram n counterWidth)
      (comparisonBorrowStageVUStep n counterWidth) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_realizes
    (comparisonBorrowLayoutVU n counterWidth)

/-- Folded forward borrow-chain gate list for the cleanup-compatible
`uGreater` selector comparison.  It computes `v - u` using `scratchA` as the
clean initial borrow and leaves `compare` available as the output condition bit
[RNSL17, ECDLP.tex:399-421,468-475]. -/
def uGreaterBorrowStageGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStage
    (uGreaterBorrowLayout n counterWidth)

/-- Base-gate program for the cleanup-compatible `uGreater` borrow pass. -/
def uGreaterBorrowStageProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStageProgram
    (uGreaterBorrowLayout n counterWidth)

/-- Folded semantic action of the cleanup-compatible `uGreater` borrow pass. -/
def uGreaterBorrowStageStep (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth →
      RegistersWithComparisonWork n counterWidth :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStageStep
    (uGreaterBorrowLayout n counterWidth)

/-- The cleanup-compatible `uGreater` borrow pass is a concrete base-gate
realization over the register-plus-comparison-work encoding. -/
theorem uGreaterBorrowStage_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (uGreaterBorrowStageProgram n counterWidth)
      (uGreaterBorrowStageStep n counterWidth) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_realizes
    (uGreaterBorrowLayout n counterWidth)

/-- The cleanup-compatible `uGreater` borrow gate list neither reads nor writes
the lifted comparison bit. -/
theorem uGreaterBorrowStageGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    ∀ gate, gate ∈ uGreaterBorrowStageGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (liftedCompareBit n counterWidth)
        gate := by
  simpa [uGreaterBorrowStageGates, uGreaterBorrowLayout, liftedVWord,
    liftedUWord, liftedComparisonCarryWord] using
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_bitDisjoint
      (uGreaterBorrowLayout n counterWidth)
      (liftedCompareBit n counterWidth)
      (by
        intro j
        exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth j)
          (RegisterBits.compareBit n counterWidth)
          (RegisterBits.v_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire j)))
      (by
        intro j
        exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth j)
          (RegisterBits.compareBit n counterWidth)
          (RegisterBits.u_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire j)))
      (by
        exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (RegisterBits.compareBit n counterWidth)
          (RegisterBits.compare_scratchA_wire_ne n counterWidth).symm)
      (by
        intro j
        exact Ne.symm
          (liftedCompare_liftedComparisonCarry_wire_ne n counterWidth j))

/-- The folded gate-list action agrees with the ordered index-step action for
the Kaliski comparison borrow-chain pass. -/
theorem comparisonBorrowStageStep_eq_indexStep
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    comparisonBorrowStageStep n counterWidth x =
      QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep
        (comparisonBorrowLayout n counterWidth) x := by
  exact
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_stepList_eq_indexStep
      (comparisonBorrowLayout n counterWidth) x

/-- The folded `v - u` gate-list action agrees with the ordered index-step
action for the Kaliski comparison borrow-chain pass. -/
theorem comparisonBorrowStageVUStep_eq_indexStep
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    comparisonBorrowStageVUStep n counterWidth x =
      QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep
        (comparisonBorrowLayoutVU n counterWidth) x := by
  exact
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_stepList_eq_indexStep
      (comparisonBorrowLayoutVU n counterWidth) x

/-- The cleanup-compatible `uGreater` borrow gate-list action agrees with the
ordered index-step action. -/
theorem uGreaterBorrowStageStep_eq_indexStep
    (n counterWidth : Nat) (x : RegistersWithComparisonWork n counterWidth) :
    uGreaterBorrowStageStep n counterWidth x =
      QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep
        (uGreaterBorrowLayout n counterWidth) x := by
  exact
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_stepList_eq_indexStep
      (uGreaterBorrowLayout n counterWidth) x

/-- Folded Kaliski comparison borrow-stage recurrence for each comparison-work
bit.  This is the bit-level invariant for the concrete `u - v` borrow-chain
object; the word-level branch condition is a separate theorem [RNSL17,
ECDLP.tex:399-421,468-475]. -/
theorem comparisonBorrowStageStep_get_work_recurrence
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hclean :
      forall k, (liftedComparisonCarryBit n counterWidth k).get x = false) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (comparisonBorrowStageStep n counterWidth x) =
      Bool.carry
        (!(liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.uValueBit n counterWidth bit)).get x)
        ((liftRegisterBitToComparisonWork n counterWidth
          (RegisterBits.vValueBit n counterWidth bit)).get x)
        ((QuantumAlg.Comparator.BorrowWorkLayout.borrowInput
          (comparisonBorrowLayout n counterWidth) bit).get
            (comparisonBorrowStageStep n counterWidth x)) := by
  rw [comparisonBorrowStageStep_eq_indexStep]
  simpa [comparisonBorrowLayout, liftedUWord, liftedVWord,
    liftedComparisonCarryWord]
    using
      QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_workBorrow_recurrence
        (comparisonBorrowLayout n counterWidth) bit x
        (by
          intro k
          simpa [comparisonBorrowLayout, liftedComparisonCarryWord]
            using hclean k)

/-- The folded Kaliski comparison borrow-chain computes the pure subtract-borrow
recurrence over the `u - v` value bits.  The same folded base-gate object is
used for resources and for this correctness invariant [RNSL17,
ECDLP.tex:399-421,468-475]. -/
theorem comparisonBorrowStageStep_get_work_natSubBorrow
    (n counterWidth : Nat) (borrow0 : Bool) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hclean :
      forall k, (liftedComparisonCarryBit n counterWidth k).get x = false)
    (hcompare : (liftedCompareBit n counterWidth).get x = borrow0) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (comparisonBorrowStageStep n counterWidth x) =
      QuantumAlg.Comparator.natSubBorrow x.1.u.val x.1.v.val borrow0
        (bit.val + 1) := by
  rw [comparisonBorrowStageStep_eq_indexStep]
  simpa [comparisonBorrowLayout, liftedUWord, liftedVWord,
    liftedComparisonCarryWord]
    using
      QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_workBorrow_natSubBorrow
        (comparisonBorrowLayout n counterWidth)
        x.1.u.val x.1.v.val borrow0 bit x
        (by
          intro k
          simpa [comparisonBorrowLayout, liftedComparisonCarryWord]
            using hclean k)
        (by
          simpa [comparisonBorrowLayout] using hcompare)
        (by
          intro k
          change
            (RegisterBits.uValueBit n counterWidth k).get x.1 =
              x.1.u.val.testBit k.val
          simp)
        (by
          intro k
          change
            (RegisterBits.vValueBit n counterWidth k).get x.1 =
              x.1.v.val.testBit k.val
          simp)

/-- Clean-initial-borrow specialization for the folded Kaliski comparison pass:
each work bit stores the natural borrow propagated through the low value bits of
`u - v` [RNSL17, ECDLP.tex:399-421,468-475]. -/
theorem comparisonBorrowStageStep_get_work_natBorrow_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hcompare : x.compare = false) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (comparisonBorrowStageStep n counterWidth
          (x, cleanComparisonWork n)) =
      QuantumAlg.Comparator.natBorrow x.u.val x.v.val (bit.val + 1) := by
  simpa [QuantumAlg.Comparator.natBorrow] using
    comparisonBorrowStageStep_get_work_natSubBorrow n counterWidth false bit
      (x, cleanComparisonWork n)
      (by
        intro k
        change (comparisonCarryValueBit n k).get
          (cleanComparisonWork n) = false
        simp)
      (by
        change (RegisterBits.compareBit n counterWidth).get x = false
        simp [hcompare])

/-- At the final borrow position, the folded local `u - v` comparison pass
characterizes its gate-level borrow-work bit as the ordinary `u < v` predicate;
the selector that routes a branch condition into `compare` is a separate circuit
obligation [RNSL17, ECDLP.tex:399-421,468-475]. -/
theorem comparisonBorrowStageStep_get_final_work_decide_u_lt_v_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (comparisonBorrowStageStep n counterWidth
          (x, cleanComparisonWork n)) =
      decide (x.u.val < x.v.val) := by
  rw [comparisonBorrowStageStep_get_work_natBorrow_clean n counterWidth bit x
    hcompare]
  have hu : x.u.val < 2 ^ (bit.val + 1) := by
    simp [hfinal]
  have hv : x.v.val < 2 ^ (bit.val + 1) := by
    simp [hfinal]
  simpa using
    QuantumAlg.Comparator.natBorrow_eq_decide_lt_of_lt_two_pow
      (a := x.u.val) (b := x.v.val) (n := bit.val + 1) hu hv

/-- The folded `v - u` Kaliski comparison borrow-chain computes the pure
subtract-borrow recurrence over the value bits.  This is the gate-level core of
the `uGreater` selector condition [RNSL17, ECDLP.tex:399-421,468-475]. -/
theorem comparisonBorrowStageVUStep_get_work_natSubBorrow
    (n counterWidth : Nat) (borrow0 : Bool) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hclean :
      forall k, (liftedComparisonCarryBit n counterWidth k).get x = false)
    (hcompare : (liftedCompareBit n counterWidth).get x = borrow0) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (comparisonBorrowStageVUStep n counterWidth x) =
      QuantumAlg.Comparator.natSubBorrow x.1.v.val x.1.u.val borrow0
        (bit.val + 1) := by
  rw [comparisonBorrowStageVUStep_eq_indexStep]
  simpa [comparisonBorrowLayoutVU, liftedUWord, liftedVWord,
    liftedComparisonCarryWord]
    using
      QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_workBorrow_natSubBorrow
        (comparisonBorrowLayoutVU n counterWidth)
        x.1.v.val x.1.u.val borrow0 bit x
        (by
          intro k
          simpa [comparisonBorrowLayoutVU, liftedComparisonCarryWord]
            using hclean k)
        (by
          simpa [comparisonBorrowLayoutVU] using hcompare)
        (by
          intro k
          change
            (RegisterBits.vValueBit n counterWidth k).get x.1 =
              x.1.v.val.testBit k.val
          simp)
        (by
          intro k
          change
            (RegisterBits.uValueBit n counterWidth k).get x.1 =
              x.1.u.val.testBit k.val
          simp)

/-- Clean-initial-borrow specialization for the folded `v - u` comparison pass:
each work bit stores the natural borrow propagated through the low value bits of
`v - u` [RNSL17, ECDLP.tex:399-421,468-475]. -/
theorem comparisonBorrowStageVUStep_get_work_natBorrow_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hcompare : x.compare = false) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (comparisonBorrowStageVUStep n counterWidth
          (x, cleanComparisonWork n)) =
      QuantumAlg.Comparator.natBorrow x.v.val x.u.val (bit.val + 1) := by
  simpa [QuantumAlg.Comparator.natBorrow] using
    comparisonBorrowStageVUStep_get_work_natSubBorrow n counterWidth false bit
      (x, cleanComparisonWork n)
      (by
        intro k
        change (comparisonCarryValueBit n k).get
          (cleanComparisonWork n) = false
        simp)
      (by
        change (RegisterBits.compareBit n counterWidth).get x = false
        simp [hcompare])

/-- At the final borrow position, the folded local `v - u` comparison pass
characterizes its gate-level borrow-work bit as the `uGreater` predicate
`v < u`; routing that predicate into `compare` remains a separate selector
circuit obligation [RNSL17, ECDLP.tex:399-421,468-475]. -/
theorem comparisonBorrowStageVUStep_get_final_work_decide_v_lt_u_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (comparisonBorrowStageVUStep n counterWidth
          (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val) := by
  rw [comparisonBorrowStageVUStep_get_work_natBorrow_clean n counterWidth bit x
    hcompare]
  have hv : x.v.val < 2 ^ (bit.val + 1) := by
    simp [hfinal]
  have hu : x.u.val < 2 ^ (bit.val + 1) := by
    simp [hfinal]
  simpa using
    QuantumAlg.Comparator.natBorrow_eq_decide_lt_of_lt_two_pow
      (a := x.v.val) (b := x.u.val) (n := bit.val + 1) hv hu

/-- The cleanup-compatible `uGreater` borrow pass computes the pure
subtract-borrow recurrence over the `v - u` value bits, using `scratchA` as the
independent initial-borrow input [RNSL17, ECDLP.tex:399-421,468-475]. -/
theorem uGreaterBorrowStageStep_get_work_natSubBorrow
    (n counterWidth : Nat) (borrow0 : Bool) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth)
    (hclean :
      forall k, (liftedComparisonCarryBit n counterWidth k).get x = false)
    (hscratchA : (liftedScratchABit n counterWidth).get x = borrow0) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (uGreaterBorrowStageStep n counterWidth x) =
      QuantumAlg.Comparator.natSubBorrow x.1.v.val x.1.u.val borrow0
        (bit.val + 1) := by
  rw [uGreaterBorrowStageStep_eq_indexStep]
  simpa [uGreaterBorrowLayout, liftedUWord, liftedVWord,
    liftedComparisonCarryWord]
    using
      QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_workBorrow_natSubBorrow
        (uGreaterBorrowLayout n counterWidth)
        x.1.v.val x.1.u.val borrow0 bit x
        (by
          intro k
          simpa [uGreaterBorrowLayout, liftedComparisonCarryWord]
            using hclean k)
        (by
          simpa [uGreaterBorrowLayout] using hscratchA)
        (by
          intro k
          change
            (RegisterBits.vValueBit n counterWidth k).get x.1 =
              x.1.v.val.testBit k.val
          simp)
        (by
          intro k
          change
            (RegisterBits.uValueBit n counterWidth k).get x.1 =
              x.1.u.val.testBit k.val
          simp)

/-- Clean-initial-scratchA specialization for the cleanup-compatible
`uGreater` borrow pass. -/
theorem uGreaterBorrowStageStep_get_work_natBorrow_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : x.scratchA = false) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (uGreaterBorrowStageStep n counterWidth
          (x, cleanComparisonWork n)) =
      QuantumAlg.Comparator.natBorrow x.v.val x.u.val (bit.val + 1) := by
  simpa [QuantumAlg.Comparator.natBorrow] using
    uGreaterBorrowStageStep_get_work_natSubBorrow n counterWidth false bit
      (x, cleanComparisonWork n)
      (by
        intro k
        change (comparisonCarryValueBit n k).get
          (cleanComparisonWork n) = false
        simp)
      (by
        change x.scratchA = false
        exact hscratchA)

/-- At the final borrow position, the cleanup-compatible `uGreater` borrow pass
characterizes its gate-level work bit as `v < u`. -/
theorem uGreaterBorrowStageStep_get_final_work_decide_v_lt_u_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : x.scratchA = false)
    (hfinal : bit.val + 1 = n) :
    (liftedComparisonCarryBit n counterWidth bit).get
        (uGreaterBorrowStageStep n counterWidth
          (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val) := by
  rw [uGreaterBorrowStageStep_get_work_natBorrow_clean n counterWidth bit x
    hscratchA]
  have hv : x.v.val < 2 ^ (bit.val + 1) := by
    simp [hfinal]
  have hu : x.u.val < 2 ^ (bit.val + 1) := by
    simp [hfinal]
  simpa using
    QuantumAlg.Comparator.natBorrow_eq_decide_lt_of_lt_two_pow
      (a := x.v.val) (b := x.u.val) (n := bit.val + 1) hv hu

/-- The cleanup-compatible `uGreater` borrow pass preserves `compare`, because
`compare` is not used as the initial borrow and is never a work target. -/
theorem uGreaterBorrowStageStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (uGreaterBorrowStageStep n counterWidth x) =
      (liftedCompareBit n counterWidth).get x := by
  rw [uGreaterBorrowStageStep_eq_indexStep]
  exact
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_of_minuend_work_ne
      (uGreaterBorrowLayout n counterWidth)
      (liftedCompareBit n counterWidth)
      (by
        intro j
        exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth j)
          (RegisterBits.compareBit n counterWidth)
          (RegisterBits.v_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire j)))
      (by
        intro j
        exact Ne.symm
          (liftedCompare_liftedComparisonCarry_wire_ne n counterWidth j))
      x

/-- The cleanup-compatible `uGreater` borrow pass preserves any observed
readout whose wire is neither a `v`-word target nor a comparison-work target. -/
theorem uGreaterBorrowStageStep_get_of_minuend_work_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (hminuend :
      forall j : Fin n, ((liftedVWord n counterWidth).bit j).wire ≠
        observed.wire)
    (hwork :
      forall j : Fin n, (liftedComparisonCarryBit n counterWidth j).wire ≠
        observed.wire)
    (x : RegistersWithComparisonWork n counterWidth) :
    observed.get (uGreaterBorrowStageStep n counterWidth x) =
      observed.get x := by
  rw [uGreaterBorrowStageStep_eq_indexStep]
  simpa [uGreaterBorrowLayout, liftedVWord, liftedComparisonCarryWord] using
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_of_minuend_work_ne
      (uGreaterBorrowLayout n counterWidth) observed
      (by
        intro j
        simpa [uGreaterBorrowLayout, liftedVWord] using hminuend j)
      (by
        intro j
        simpa [uGreaterBorrowLayout, liftedComparisonCarryWord] using hwork j)
      x

/-- The folded `v - u` comparison borrow-chain preserves the external
comparison ancilla used as its clean initial borrow. -/
theorem comparisonBorrowStageVUStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (comparisonBorrowStageVUStep n counterWidth x) =
      (liftedCompareBit n counterWidth).get x := by
  rw [comparisonBorrowStageVUStep_eq_indexStep]
  simpa [comparisonBorrowLayoutVU] using
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_initialBorrow
      (comparisonBorrowLayoutVU n counterWidth) x

/-- CNOT that copies the selected comparison-work borrow bit into the lifted
comparison ancilla.  This is the small bridge from the gate-level comparator
work word to the branch-condition bit [RNSL17, ECDLP.tex:468-475]. -/
def comparisonWorkToCompareGate
    (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth) :=
  EncodedBit.GateSpec.cnot
    (liftedComparisonCarryBit n counterWidth bit)
    (liftedCompareBit n counterWidth)
    (Ne.symm (liftedCompare_liftedComparisonCarry_wire_ne n counterWidth bit))

/-- Base-gate program for `comparisonWorkToCompareGate`. -/
def comparisonWorkToCompareProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.program
    (comparisonWorkToCompareGate n counterWidth bit)
    (QubitLayout.canonical _) .empty

/-- Semantic step for `comparisonWorkToCompareGate`. -/
def comparisonWorkToCompareStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithComparisonWork n counterWidth →
      RegistersWithComparisonWork n counterWidth :=
  EncodedBit.GateSpec.step (comparisonWorkToCompareGate n counterWidth bit)

/-- The work-to-compare CNOT is a concrete base-gate realization. -/
theorem comparisonWorkToCompare_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (comparisonWorkToCompareProgram n counterWidth bit)
      (comparisonWorkToCompareStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizes (QubitLayout.canonical _) .empty
    (comparisonWorkToCompareGate n counterWidth bit)

/-- The work-to-compare CNOT toggles `compare` by the selected borrow-work bit. -/
theorem comparisonWorkToCompareStep_get_compare
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (comparisonWorkToCompareStep n counterWidth bit x) =
      ((liftedCompareBit n counterWidth).get x ^^
        (liftedComparisonCarryBit n counterWidth bit).get x) := by
  simpa [comparisonWorkToCompareStep, comparisonWorkToCompareGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.cnotStep_get_target
        (liftedComparisonCarryBit n counterWidth bit)
        (liftedCompareBit n counterWidth) x

/-- The work-to-compare CNOT preserves any observed readout whose wire is not
the lifted comparison target. -/
theorem comparisonWorkToCompareStep_get_of_compare_ne
    (n counterWidth : Nat) (bit : Fin n)
    (observed :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (hcompare : (liftedCompareBit n counterWidth).wire ≠ observed.wire)
    (x : RegistersWithComparisonWork n counterWidth) :
    observed.get (comparisonWorkToCompareStep n counterWidth bit x) =
      observed.get x := by
  simpa [comparisonWorkToCompareStep, comparisonWorkToCompareGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.cnotStep_get_of_target_ne
        (liftedComparisonCarryBit n counterWidth bit)
        (liftedCompareBit n counterWidth) observed hcompare x

/-- Forward `v - u` borrow computation followed by copying the final borrow
into `compare`.  It computes the `uGreater` condition into `compare`, while
cleanup of the comparison-work word is handled by the later uncompute slice
[RNSL17, ECDLP.tex:399-421,468-475]. -/
def uGreaterCompareComputeGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  comparisonBorrowStageVUGates n counterWidth ++
    [comparisonWorkToCompareGate n counterWidth bit]

/-- Base-gate program for computing the `uGreater` condition into `compare`. -/
def uGreaterCompareComputeProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uGreaterCompareComputeGates n counterWidth bit)

/-- Semantic step for computing the `uGreater` condition into `compare`. -/
def uGreaterCompareComputeStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithComparisonWork n counterWidth →
      RegistersWithComparisonWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uGreaterCompareComputeGates n counterWidth bit)

/-- The forward `uGreater` compare-compute slice is a concrete base-gate
realization over the register-plus-comparison-work encoding. -/
theorem uGreaterCompareCompute_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (uGreaterCompareComputeProgram n counterWidth bit)
      (uGreaterCompareComputeStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uGreaterCompareComputeGates n counterWidth bit)

/-- On clean comparison work and a clean comparison ancilla, the forward
compare-compute slice writes the `uGreater` predicate `v < u` into `compare`. -/
theorem uGreaterCompareComputeStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (liftedCompareBit n counterWidth).get
        (uGreaterCompareComputeStep n counterWidth bit
          (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val) := by
  rw [uGreaterCompareComputeStep, uGreaterCompareComputeGates,
    EncodedBit.GateSpec.stepList_append]
  change
    (liftedCompareBit n counterWidth).get
        (comparisonWorkToCompareStep n counterWidth bit
          (comparisonBorrowStageVUStep n counterWidth
            (x, cleanComparisonWork n))) =
      decide (x.v.val < x.u.val)
  rw [comparisonWorkToCompareStep_get_compare]
  rw [comparisonBorrowStageVUStep_get_compare]
  have hcleanCompare :
      (liftedCompareBit n counterWidth).get
          (x, cleanComparisonWork n) = false := by
    change (RegisterBits.compareBit n counterWidth).get x = false
    simp [hcompare]
  rw [hcleanCompare]
  simp only [Bool.false_bne, Fin.val_fin_lt]
  rw [comparisonBorrowStageVUStep_get_final_work_decide_v_lt_u_clean
    n counterWidth bit x hcompare hfinal]
  rfl

/-- Cleanup-compatible forward `uGreater` compare-compute gates.  The borrow
stage uses `scratchA` as its clean initial borrow and copies the final
`v - u` borrow into `compare`; this is intended to support a later reverse
borrow cleanup without changing the initial-borrow input [RNSL17,
ECDLP.tex:399-421,468-475]. -/
def uGreaterScratchACompareComputeGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  uGreaterBorrowStageGates n counterWidth ++
    [comparisonWorkToCompareGate n counterWidth bit]

/-- Base-gate program for the cleanup-compatible forward `uGreater`
compare-compute slice. -/
def uGreaterScratchACompareComputeProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uGreaterScratchACompareComputeGates n counterWidth bit)

/-- Semantic step for the cleanup-compatible forward `uGreater`
compare-compute slice. -/
def uGreaterScratchACompareComputeStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithComparisonWork n counterWidth →
      RegistersWithComparisonWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uGreaterScratchACompareComputeGates n counterWidth bit)

/-- The cleanup-compatible forward `uGreater` compare-compute slice is a
concrete base-gate realization. -/
theorem uGreaterScratchACompareCompute_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (uGreaterScratchACompareComputeProgram n counterWidth bit)
      (uGreaterScratchACompareComputeStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uGreaterScratchACompareComputeGates n counterWidth bit)

/-- On clean comparison work, clean `scratchA`, and clean `compare`, the
cleanup-compatible forward compute slice writes the `uGreater` predicate
`v < u` into `compare`. -/
theorem uGreaterScratchACompareComputeStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (liftedCompareBit n counterWidth).get
        (uGreaterScratchACompareComputeStep n counterWidth bit
          (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val) := by
  rw [uGreaterScratchACompareComputeStep,
    uGreaterScratchACompareComputeGates,
    EncodedBit.GateSpec.stepList_append]
  change
    (liftedCompareBit n counterWidth).get
        (comparisonWorkToCompareStep n counterWidth bit
          (uGreaterBorrowStageStep n counterWidth
            (x, cleanComparisonWork n))) =
      decide (x.v.val < x.u.val)
  rw [comparisonWorkToCompareStep_get_compare]
  rw [uGreaterBorrowStageStep_get_compare]
  have hcleanCompare :
      (liftedCompareBit n counterWidth).get
          (x, cleanComparisonWork n) = false := by
    change (RegisterBits.compareBit n counterWidth).get x = false
    simp [hcompare]
  rw [hcleanCompare]
  simp only [Bool.false_bne, Fin.val_fin_lt]
  rw [uGreaterBorrowStageStep_get_final_work_decide_v_lt_u_clean
    n counterWidth bit x hscratchA hfinal]
  rfl

/-- Reverse semantic step for the cleanup-compatible `uGreater` borrow pass. -/
def uGreaterBorrowStageReverseStep (n counterWidth : Nat) :
    RegistersWithComparisonWork n counterWidth →
      RegistersWithComparisonWork n counterWidth :=
  EncodedBit.GateSpec.stepList (uGreaterBorrowStageGates n counterWidth).reverse

/-- The reverse cleanup-compatible `uGreater` borrow pass preserves `compare`.
This follows from the forward pass preserving `compare` and the generic
gate-list reverse-inverse theorem. -/
theorem uGreaterBorrowStageReverseStep_get_compare
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedCompareBit n counterWidth).get
        (uGreaterBorrowStageReverseStep n counterWidth x) =
      (liftedCompareBit n counterWidth).get x := by
  let gates := uGreaterBorrowStageGates n counterWidth
  have hleft :
      uGreaterBorrowStageStep n counterWidth
          (EncodedBit.GateSpec.stepList gates.reverse x) = x := by
    change EncodedBit.GateSpec.stepList gates
        (EncodedBit.GateSpec.stepList gates.reverse x) = x
    simpa [gates] using
      EncodedBit.GateSpec.stepList_reverse_stepList gates.reverse x
  have hpres :=
    uGreaterBorrowStageStep_get_compare n counterWidth
      (EncodedBit.GateSpec.stepList gates.reverse x)
  change
    (liftedCompareBit n counterWidth).get
        (EncodedBit.GateSpec.stepList gates.reverse x) =
      (liftedCompareBit n counterWidth).get x
  rw [hleft] at hpres
  exact hpres.symm

/-- The reverse cleanup-compatible `uGreater` borrow pass commutes with flipping
the comparison bit, because the borrow pass neither reads nor writes that bit. -/
theorem uGreaterBorrowStageReverseStep_flip_compare_comm
    (n counterWidth : Nat)
    (x : RegistersWithComparisonWork n counterWidth) :
    uGreaterBorrowStageReverseStep n counterWidth
        ((liftedCompareBit n counterWidth).flip x) =
      (liftedCompareBit n counterWidth).flip
        (uGreaterBorrowStageReverseStep n counterWidth x) := by
  change EncodedBit.GateSpec.stepList
      (uGreaterBorrowStageGates n counterWidth).reverse
        ((liftedCompareBit n counterWidth).flip x) =
    (liftedCompareBit n counterWidth).flip
      (EncodedBit.GateSpec.stepList
        (uGreaterBorrowStageGates n counterWidth).reverse x)
  apply EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
  intro gate hmem
  exact uGreaterBorrowStageGates_bitDisjoint_compare n counterWidth gate
    (by simpa using hmem)

/-- The reverse cleanup-compatible `uGreater` borrow pass preserves any
observed readout whose wire is neither a `v`-word target nor a comparison-work
target. -/
theorem uGreaterBorrowStageReverseStep_get_of_minuend_work_ne
    (n counterWidth : Nat)
    (observed :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (hminuend :
      forall j : Fin n, ((liftedVWord n counterWidth).bit j).wire ≠
        observed.wire)
    (hwork :
      forall j : Fin n, (liftedComparisonCarryBit n counterWidth j).wire ≠
        observed.wire)
    (x : RegistersWithComparisonWork n counterWidth) :
    observed.get (uGreaterBorrowStageReverseStep n counterWidth x) =
      observed.get x := by
  let gates := uGreaterBorrowStageGates n counterWidth
  have hleft :
      uGreaterBorrowStageStep n counterWidth
          (EncodedBit.GateSpec.stepList gates.reverse x) = x := by
    change EncodedBit.GateSpec.stepList gates
        (EncodedBit.GateSpec.stepList gates.reverse x) = x
    simpa [gates] using
      EncodedBit.GateSpec.stepList_reverse_stepList gates.reverse x
  have hpres :=
    uGreaterBorrowStageStep_get_of_minuend_work_ne n counterWidth observed
      hminuend hwork (EncodedBit.GateSpec.stepList gates.reverse x)
  change
    observed.get (EncodedBit.GateSpec.stepList gates.reverse x) =
      observed.get x
  rw [hleft] at hpres
  exact hpres.symm

/-- Full gate list that computes the `uGreater` comparison predicate into
`compare`, then runs the reverse borrow pass.  This records the intended
compute-copy-uncompute circuit object; the work-clean restoration theorem below
uses this same gate list [RNSL17, ECDLP.tex:399-421,468-475]. -/
def uGreaterScratchACompareSelectorGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec
      (registersWithComparisonWorkEncoding n counterWidth)) :=
  uGreaterScratchACompareComputeGates n counterWidth bit ++
    (uGreaterBorrowStageGates n counterWidth).reverse

/-- Base-gate program for the full `uGreater` comparison selector gate list. -/
def uGreaterScratchACompareSelectorProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithComparisonWorkEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uGreaterScratchACompareSelectorGates n counterWidth bit)

/-- Semantic step for the full `uGreater` comparison selector gate list. -/
def uGreaterScratchACompareSelectorStep
    (n counterWidth : Nat) (bit : Fin n) :
    RegistersWithComparisonWork n counterWidth →
      RegistersWithComparisonWork n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uGreaterScratchACompareSelectorGates n counterWidth bit)

/-- The full `uGreater` comparison selector gate list is a concrete base-gate
realization over the register-plus-comparison-work encoding. -/
theorem uGreaterScratchACompareSelector_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes (registersWithComparisonWorkEncoding n counterWidth)
      (uGreaterScratchACompareSelectorProgram n counterWidth bit)
      (uGreaterScratchACompareSelectorStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uGreaterScratchACompareSelectorGates n counterWidth bit)

/-- Exact physical length of the cleanup-compatible comparison selector. -/
theorem uGreaterScratchACompareSelectorGates_length
    (n counterWidth : Nat) (bit : Fin n) :
    (uGreaterScratchACompareSelectorGates n counterWidth bit).length =
      10 * n + 1 := by
  simp only [uGreaterScratchACompareSelectorGates,
    uGreaterScratchACompareComputeGates, uGreaterBorrowStageGates,
    List.length_append, List.length_reverse, List.length_cons, List.length_nil,
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_length]
  omega

/-- Exact X coordinate of the cleanup-compatible comparison selector. -/
theorem uGreaterScratchACompareSelectorGates_xMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((uGreaterScratchACompareSelectorGates n counterWidth bit).map
      EncodedBit.GateSpec.xMultiplicity).sum = 4 * n := by
  simp only [uGreaterScratchACompareSelectorGates,
    uGreaterScratchACompareComputeGates, uGreaterBorrowStageGates,
    comparisonWorkToCompareGate,
    List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_xMultiplicity_sum,
    EncodedBit.GateSpec.xMultiplicity_cnot]
  omega

/-- Exact CNOT coordinate of the cleanup-compatible comparison selector. -/
theorem uGreaterScratchACompareSelectorGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((uGreaterScratchACompareSelectorGates n counterWidth bit).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp only [uGreaterScratchACompareSelectorGates,
    uGreaterScratchACompareComputeGates, uGreaterBorrowStageGates,
    comparisonWorkToCompareGate,
    List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_cnotMultiplicity_sum,
    EncodedBit.GateSpec.cnotMultiplicity_cnot]
  rfl

/-- Exact Toffoli coordinate of the cleanup-compatible comparison selector. -/
theorem uGreaterScratchACompareSelectorGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((uGreaterScratchACompareSelectorGates n counterWidth bit).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * n := by
  simp only [uGreaterScratchACompareSelectorGates,
    uGreaterScratchACompareComputeGates, uGreaterBorrowStageGates,
    comparisonWorkToCompareGate,
    List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_toffoliMultiplicity_sum,
    EncodedBit.GateSpec.toffoliMultiplicity_cnot]
  omega

/-- The cleanup-compatible forward `uGreater` compare-compute slice preserves
any observed readout whose wire is not the comparison target, any `v`-word
borrow target, or any comparison-work target. -/
theorem uGreaterScratchACompareComputeStep_get_of_preserved
    (n counterWidth : Nat) (bit : Fin n)
    (observed :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (hcompare : (liftedCompareBit n counterWidth).wire ≠ observed.wire)
    (hminuend :
      forall j : Fin n, ((liftedVWord n counterWidth).bit j).wire ≠
        observed.wire)
    (hwork :
      forall j : Fin n, (liftedComparisonCarryBit n counterWidth j).wire ≠
        observed.wire)
    (x : RegistersWithComparisonWork n counterWidth) :
    observed.get (uGreaterScratchACompareComputeStep n counterWidth bit x) =
      observed.get x := by
  rw [uGreaterScratchACompareComputeStep,
    uGreaterScratchACompareComputeGates,
    EncodedBit.GateSpec.stepList_append]
  change observed.get
      (comparisonWorkToCompareStep n counterWidth bit
        (uGreaterBorrowStageStep n counterWidth x)) =
    observed.get x
  rw [comparisonWorkToCompareStep_get_of_compare_ne n counterWidth bit
    observed hcompare]
  exact uGreaterBorrowStageStep_get_of_minuend_work_ne n counterWidth
    observed hminuend hwork x

/-- The full compute-copy-reverse `uGreater` comparison selector preserves any
observed readout whose wire is not the comparison target, any `v`-word borrow
target, or any comparison-work target. -/
theorem uGreaterScratchACompareSelectorStep_get_of_preserved
    (n counterWidth : Nat) (bit : Fin n)
    (observed :
      EncodedBit (registersWithComparisonWorkEncoding n counterWidth))
    (hcompare : (liftedCompareBit n counterWidth).wire ≠ observed.wire)
    (hminuend :
      forall j : Fin n, ((liftedVWord n counterWidth).bit j).wire ≠
        observed.wire)
    (hwork :
      forall j : Fin n, (liftedComparisonCarryBit n counterWidth j).wire ≠
        observed.wire)
    (x : RegistersWithComparisonWork n counterWidth) :
    observed.get (uGreaterScratchACompareSelectorStep n counterWidth bit x) =
      observed.get x := by
  rw [uGreaterScratchACompareSelectorStep,
    uGreaterScratchACompareSelectorGates,
    EncodedBit.GateSpec.stepList_append]
  change observed.get
      (uGreaterBorrowStageReverseStep n counterWidth
        (uGreaterScratchACompareComputeStep n counterWidth bit x)) =
    observed.get x
  rw [uGreaterBorrowStageReverseStep_get_of_minuend_work_ne n counterWidth
    observed hminuend hwork]
  exact uGreaterScratchACompareComputeStep_get_of_preserved n counterWidth bit
    observed hcompare hminuend hwork x

/-- The full compute-copy-reverse `uGreater` comparison selector restores every
comparison-work carry bit.  The middle work-to-compare CNOT only targets
`compare`, and the reverse borrow pass commutes with that compare flip. -/
theorem uGreaterScratchACompareSelectorStep_get_comparisonCarry
    (n counterWidth : Nat) (bit workBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedComparisonCarryBit n counterWidth workBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (liftedComparisonCarryBit n counterWidth workBit).get x := by
  let gates := uGreaterBorrowStageGates n counterWidth
  let work := liftedComparisonCarryBit n counterWidth workBit
  let compare := liftedCompareBit n counterWidth
  let y := uGreaterBorrowStageStep n counterWidth x
  have hreverse_forward :
      uGreaterBorrowStageReverseStep n counterWidth y = x := by
    dsimp [y, uGreaterBorrowStageReverseStep, uGreaterBorrowStageStep, gates]
    exact EncodedBit.GateSpec.stepList_reverse_stepList
      (uGreaterBorrowStageGates n counterWidth) x
  rw [uGreaterScratchACompareSelectorStep,
    uGreaterScratchACompareSelectorGates,
    uGreaterScratchACompareComputeGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  change work.get
      (uGreaterBorrowStageReverseStep n counterWidth
        (comparisonWorkToCompareStep n counterWidth bit y)) =
    work.get x
  unfold comparisonWorkToCompareStep comparisonWorkToCompareGate
  change work.get
      (uGreaterBorrowStageReverseStep n counterWidth
        (EncodedBit.cnotStep (liftedComparisonCarryBit n counterWidth bit)
          compare y)) =
    work.get x
  unfold EncodedBit.cnotStep
  by_cases hcontrol :
      (liftedComparisonCarryBit n counterWidth bit).get y
  · rw [if_pos hcontrol]
    rw [uGreaterBorrowStageReverseStep_flip_compare_comm]
    rw [EncodedBit.get_flip_of_wire_ne compare work
      (liftedCompare_liftedComparisonCarry_wire_ne n counterWidth workBit)]
    rw [hreverse_forward]
  · rw [if_neg hcontrol]
    rw [hreverse_forward]

/-- The full compute-copy-reverse `uGreater` comparison selector leaves
`compare` equal to the `uGreater` predicate `v < u`.  This theorem is about the
condition bit; comparison-work restoration is proved by the companion theorem
above [RNSL17, ECDLP.tex:399-421,468-475]. -/
theorem uGreaterScratchACompareSelectorStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : x.scratchA = false)
    (hcompare : x.compare = false)
    (hfinal : bit.val + 1 = n) :
    (liftedCompareBit n counterWidth).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit
          (x, cleanComparisonWork n)) =
      decide (x.v.val < x.u.val) := by
  rw [uGreaterScratchACompareSelectorStep,
    uGreaterScratchACompareSelectorGates,
    EncodedBit.GateSpec.stepList_append]
  change
    (liftedCompareBit n counterWidth).get
        (uGreaterBorrowStageReverseStep n counterWidth
          (uGreaterScratchACompareComputeStep n counterWidth bit
            (x, cleanComparisonWork n))) =
      decide (x.v.val < x.u.val)
  rw [uGreaterBorrowStageReverseStep_get_compare]
  exact
    uGreaterScratchACompareComputeStep_get_compare_clean n counterWidth bit
      x hscratchA hcompare hfinal

/-- The full `uGreater` comparison selector preserves the active flag. -/
theorem uGreaterScratchACompareSelectorStep_get_active
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedActiveBit n counterWidth).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (liftedActiveBit n counterWidth).get x := by
  exact uGreaterScratchACompareSelectorStep_get_of_preserved n counterWidth bit
    (liftedActiveBit n counterWidth)
    (by
      exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.activeBit n counterWidth)
        (Ne.symm (RegisterBits.active_compare_wire_ne n counterWidth)))
    (by
      intro j
      exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth j)
        (RegisterBits.activeBit n counterWidth)
        (Ne.symm (RegisterBits.active_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire j))))
    (by
      intro j
      exact Ne.symm
        (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
          (RegisterBits.activeBit n counterWidth)
          (comparisonCarryValueBit n j)))
    x

/-- The full `uGreater` comparison selector preserves the second scratch bit. -/
theorem uGreaterScratchACompareSelectorStep_get_scratchB
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchBBit n counterWidth).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (liftedScratchBBit n counterWidth).get x := by
  exact uGreaterScratchACompareSelectorStep_get_of_preserved n counterWidth bit
    (liftedScratchBBit n counterWidth)
    (by
      exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.compare_scratchB_wire_ne n counterWidth))
    (by
      intro j
      exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth j)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.v_scratchB_wire_ne n counterWidth
          (WireAddress.littleEndianWire j)))
    (by
      intro j
      exact Ne.symm
        (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
          (RegisterBits.scratchBBit n counterWidth)
          (comparisonCarryValueBit n j)))
    x

/-- The full `uGreater` comparison selector restores the first scratch bit
used as the cleanup-compatible borrow input. -/
theorem uGreaterScratchACompareSelectorStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedScratchABit n counterWidth).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (liftedScratchABit n counterWidth).get x := by
  exact uGreaterScratchACompareSelectorStep_get_of_preserved n counterWidth bit
    (liftedScratchABit n counterWidth)
    (by
      exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.scratchABit n counterWidth)
        (RegisterBits.compare_scratchA_wire_ne n counterWidth))
    (by
      intro j
      exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth j)
        (RegisterBits.scratchABit n counterWidth)
        (RegisterBits.v_scratchA_wire_ne n counterWidth
          (WireAddress.littleEndianWire j)))
    (by
      intro j
      exact Ne.symm
        (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (comparisonCarryValueBit n j)))
    x

/-- The full `uGreater` comparison selector preserves the selected `u`
register bit. -/
theorem uGreaterScratchACompareSelectorStep_get_uBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedUBit n counterWidth bit).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (liftedUBit n counterWidth bit).get x := by
  exact uGreaterScratchACompareSelectorStep_get_of_preserved n counterWidth bit
    (liftedUBit n counterWidth bit)
    (liftedCompare_liftedUBit_wire_ne n counterWidth bit)
    (by
      intro j
      exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth j)
        (RegisterBits.uBit n counterWidth bit)
        (Ne.symm (RegisterBits.u_v_wire_ne n counterWidth bit
          (WireAddress.littleEndianWire j))))
    (by
      intro j
      exact Ne.symm
        (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
          (RegisterBits.uBit n counterWidth bit)
          (comparisonCarryValueBit n j)))
    x

/-- The full `uGreater` comparison selector preserves every little-endian `u`
value bit. -/
theorem uGreaterScratchACompareSelectorStep_get_uWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedUWord n counterWidth).bit targetBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth selectorBit x) =
      ((liftedUWord n counterWidth).bit targetBit).get x := by
  exact uGreaterScratchACompareSelectorStep_get_of_preserved
    n counterWidth selectorBit ((liftedUWord n counterWidth).bit targetBit)
    (liftedCompare_liftedUWordBit_wire_ne n counterWidth targetBit)
    (by
      intro j
      exact Ne.symm
        (liftedUWordBit_liftedVWordBit_wire_ne n counterWidth targetBit j))
    (by
      intro j
      exact Ne.symm
        (liftedUWordBit_liftedComparisonCarry_wire_ne n counterWidth
          targetBit j))
    x

/-- The full `uGreater` comparison selector restores every little-endian `v`
value bit after the borrow compute-copy-uncompute path. -/
theorem uGreaterScratchACompareSelectorStep_get_vWordBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedVWord n counterWidth).bit targetBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth selectorBit x) =
      ((liftedVWord n counterWidth).bit targetBit).get x := by
  let gates := uGreaterBorrowStageGates n counterWidth
  let source := (liftedVWord n counterWidth).bit targetBit
  let compare := liftedCompareBit n counterWidth
  let y := uGreaterBorrowStageStep n counterWidth x
  have hreverse_forward :
      uGreaterBorrowStageReverseStep n counterWidth y = x := by
    dsimp [y, uGreaterBorrowStageReverseStep, uGreaterBorrowStageStep, gates]
    exact EncodedBit.GateSpec.stepList_reverse_stepList
      (uGreaterBorrowStageGates n counterWidth) x
  rw [uGreaterScratchACompareSelectorStep,
    uGreaterScratchACompareSelectorGates,
    uGreaterScratchACompareComputeGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  change source.get
      (uGreaterBorrowStageReverseStep n counterWidth
        (comparisonWorkToCompareStep n counterWidth selectorBit y)) =
    source.get x
  unfold comparisonWorkToCompareStep comparisonWorkToCompareGate
  change source.get
      (uGreaterBorrowStageReverseStep n counterWidth
        (EncodedBit.cnotStep
          (liftedComparisonCarryBit n counterWidth selectorBit)
          compare y)) =
    source.get x
  unfold EncodedBit.cnotStep
  by_cases hcontrol :
      (liftedComparisonCarryBit n counterWidth selectorBit).get y
  · rw [if_pos hcontrol]
    rw [uGreaterBorrowStageReverseStep_flip_compare_comm]
    rw [EncodedBit.get_flip_of_wire_ne compare source
      (liftedCompare_liftedVWordBit_wire_ne n counterWidth targetBit)]
    rw [hreverse_forward]
  · rw [if_neg hcontrol]
    rw [hreverse_forward]

/-- The full `uGreater` comparison selector preserves every little-endian `s`
coefficient value bit. -/
theorem uGreaterScratchACompareSelectorStep_get_sCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedSCoeffValueWord n counterWidth).bit targetBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth selectorBit x) =
      ((liftedSCoeffValueWord n counterWidth).bit targetBit).get x := by
  exact uGreaterScratchACompareSelectorStep_get_of_preserved
    n counterWidth selectorBit
    ((liftedSCoeffValueWord n counterWidth).bit targetBit)
    (liftedCompare_liftedSCoeffValueWordBit_wire_ne n counterWidth targetBit)
    (by
      intro j
      exact liftedVWordBit_liftedSCoeffValueWordBit_wire_ne
        n counterWidth j targetBit)
    (by
      intro j
      exact Ne.symm
        (liftedSCoeffValueWordBit_liftedComparisonCarry_wire_ne
          n counterWidth targetBit j))
    x

/-- The full `uGreater` comparison selector preserves every little-endian `r`
coefficient value bit. -/
theorem uGreaterScratchACompareSelectorStep_get_rCoeffValueWordBit
    (n counterWidth : Nat) (selectorBit : Fin n) (targetBit : Fin (n + 1))
    (x : RegistersWithComparisonWork n counterWidth) :
    ((liftedRCoeffValueWord n counterWidth).bit targetBit).get
        (uGreaterScratchACompareSelectorStep n counterWidth selectorBit x) =
      ((liftedRCoeffValueWord n counterWidth).bit targetBit).get x := by
  exact uGreaterScratchACompareSelectorStep_get_of_preserved
    n counterWidth selectorBit
    ((liftedRCoeffValueWord n counterWidth).bit targetBit)
    (liftedCompare_liftedRCoeffValueWordBit_wire_ne n counterWidth targetBit)
    (by
      intro j
      exact liftedVWordBit_liftedRCoeffValueWordBit_wire_ne
        n counterWidth j targetBit)
    (by
      intro j
      exact Ne.symm
        (liftedRCoeffValueWordBit_liftedComparisonCarry_wire_ne
          n counterWidth targetBit j))
    x

/-- The full `uGreater` comparison selector preserves every stored
branch-history bit. -/
theorem uGreaterScratchACompareSelectorStep_get_historyBit
    (n counterWidth : Nat) (bit : Fin n)
    (historyIndex : Fin (2 * n))
    (x : RegistersWithComparisonWork n counterWidth) :
    (liftedHistoryBit n counterWidth historyIndex).get
        (uGreaterScratchACompareSelectorStep n counterWidth bit x) =
      (liftedHistoryBit n counterWidth historyIndex).get x := by
  exact uGreaterScratchACompareSelectorStep_get_of_preserved n counterWidth bit
    (liftedHistoryBit n counterWidth historyIndex)
    (by
      exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.historyBit n counterWidth historyIndex)
        (RegisterBits.compare_history_wire_ne n counterWidth historyIndex))
    (by
      intro j
      exact liftRegisterBit_liftRegisterBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth j)
        (RegisterBits.historyBit n counterWidth historyIndex)
        (RegisterBits.v_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire j) historyIndex))
    (by
      intro j
      exact Ne.symm
        (liftRegisterBit_liftComparisonWorkBit_wire_ne n counterWidth
          (RegisterBits.historyBit n counterWidth historyIndex)
          (comparisonCarryValueBit n j)))
    x

/-- Clean finite register seed corresponding to `xmg p x 0 1 0`, with
ancillas, branch history, and counter initially clear [RNSL17,
ECDLP.tex:399-421,425-475]. -/
def initialRegisters (n counterWidth : Nat) (p x : Word n) :
    Registers n counterWidth where
  u := p
  v := x
  compare := false
  sCoeff := 1
  rCoeff := 0
  scratchA := false
  scratchB := false
  history := 0
  active := true
  counter := 0

@[simp] theorem initialRegisters_history (n counterWidth : Nat) (p x : Word n) :
    (initialRegisters n counterWidth p x).history = 0 :=
  rfl

@[simp] theorem initialRegisters_active (n counterWidth : Nat) (p x : Word n) :
    (initialRegisters n counterWidth p x).active = true :=
  rfl

/-- Every branch-history slot is initially clean in the finite register seed. -/
theorem initialRegisters_historyBit_get
    (n counterWidth : Nat) (p x : Word n)
    (historyIndex : Fin (2 * n)) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (initialRegisters n counterWidth p x) =
      false := by
  simp [RegisterBits.historyBit_get]

/-! ## Concrete register-gate atoms -/

/-- One X atom that toggles the Kaliski active flag.  Under an active-state
precondition this is the concrete flag-clear step used by a terminating
fixed-round route; by itself it is only the flag toggle, not the full
termination detector or padding counter [RNSL17, ECDLP.tex:468]. -/
def activeFlagToggleGate (n counterWidth : Nat) :
    EncodedBit.GateSpec (registerEncoding n counterWidth) :=
  EncodedBit.GateSpec.x (RegisterBits.activeBit n counterWidth)

/-- Base-gate program for `activeFlagToggleGate`. -/
def activeFlagToggleProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.program (activeFlagToggleGate n counterWidth)
    (QubitLayout.canonical _) .empty

/-- Semantic step implemented by `activeFlagToggleProgram`. -/
def activeFlagToggleStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.step (activeFlagToggleGate n counterWidth)

/-- The active-flag X atom is a concrete encoded-bit base-gate realization over
the Montgomery--Kaliski register layout. -/
theorem activeFlagToggle_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (activeFlagToggleProgram n counterWidth)
      (activeFlagToggleStep n counterWidth) :=
  EncodedBit.GateSpec.realizes (QubitLayout.canonical _) .empty
    (activeFlagToggleGate n counterWidth)

/-- The active-flag X atom toggles the active bit. -/
theorem activeFlagToggleStep_get_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (activeFlagToggleStep n counterWidth x) =
      ! (RegisterBits.activeBit n counterWidth).get x := by
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_self (RegisterBits.activeBit n counterWidth) x

/-- On an active state, the active-flag X atom clears the active flag. -/
theorem activeFlagToggleStep_get_active_of_active
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hactive : (RegisterBits.activeBit n counterWidth).get x = true) :
    (RegisterBits.activeBit n counterWidth).get
        (activeFlagToggleStep n counterWidth x) = false := by
  rw [activeFlagToggleStep_get_active, hactive]
  rfl

/-- The active-flag X atom preserves every padding-counter bit. -/
theorem activeFlagToggleStep_get_counterBit
    (n counterWidth : Nat) (bit : Fin counterWidth)
    (x : Registers n counterWidth) :
    (RegisterBits.counterBit n counterWidth bit).get
        (activeFlagToggleStep n counterWidth x) =
      (RegisterBits.counterBit n counterWidth bit).get x := by
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.counterBit n counterWidth bit)
        (RegisterBits.active_counter_wire_ne n counterWidth bit) x

/-- The active-flag X atom preserves the padding counter field. -/
theorem activeFlagToggleStep_counter
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).counter = x.counter := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa using activeFlagToggleStep_get_counterBit n counterWidth
    (WireAddress.littleEndianWire bit) x

/-- The active-flag X atom toggles the concrete active field. -/
theorem activeFlagToggleStep_active
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).active = !x.active := by
  simpa [RegisterBits.activeBit_get] using
    activeFlagToggleStep_get_active n counterWidth x

/-- On an active concrete state, the active-flag X atom clears the active field. -/
theorem activeFlagToggleStep_active_of_active
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hactive : x.active = true) :
    (activeFlagToggleStep n counterWidth x).active = false := by
  rw [activeFlagToggleStep_active, hactive]
  rfl

/-- The active-flag X atom preserves the `u` word. -/
theorem activeFlagToggleStep_u
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).u = x.u := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.uValueBit n counterWidth bit)
        (RegisterBits.active_u_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)) x

/-- The active-flag X atom preserves the `v` word. -/
theorem activeFlagToggleStep_v
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).v = x.v := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.vValueBit n counterWidth bit)
        (RegisterBits.active_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)) x

/-- The active-flag X atom preserves the `s` coefficient word. -/
theorem activeFlagToggleStep_sCoeff
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).sCoeff = x.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.sCoeffValueBit n counterWidth bit)
        (RegisterBits.active_sCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)) x

/-- The active-flag X atom preserves the `r` coefficient word. -/
theorem activeFlagToggleStep_rCoeff
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).rCoeff = x.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.rCoeffValueBit n counterWidth bit)
        (RegisterBits.active_rCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)) x

/-- The active-flag X atom preserves the comparison ancilla. -/
theorem activeFlagToggleStep_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).compare = x.compare := by
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.compareBit n counterWidth)
        (RegisterBits.active_compare_wire_ne n counterWidth) x

/-- The active-flag X atom preserves the first scratch bit. -/
theorem activeFlagToggleStep_scratchA
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).scratchA = x.scratchA := by
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step, RegisterBits.scratchABit_get] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchABit n counterWidth)
        (RegisterBits.active_scratchA_wire_ne n counterWidth) x

/-- The active-flag X atom preserves the second scratch bit. -/
theorem activeFlagToggleStep_scratchB
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).scratchB = x.scratchB := by
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step, RegisterBits.scratchBBit_get] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.active_scratchB_wire_ne n counterWidth) x

/-- The active-flag X atom preserves the branch-history word. -/
theorem activeFlagToggleStep_history
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (activeFlagToggleStep n counterWidth x).history = x.history := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [activeFlagToggleStep, activeFlagToggleGate,
    EncodedBit.GateSpec.step, RegisterBits.historyBit_get] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.historyBit n counterWidth
          (WireAddress.littleEndianWire bit))
        (RegisterBits.active_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit)) x

/-- Lift a Kaliski-register update over the trailing counter-increment work
object. -/
def liftRegisterStepToCounterIncrementWork
    (n counterWidth : Nat)
    (step : Registers n counterWidth -> Registers n counterWidth) :
    RegistersWithCounterIncrementWork n counterWidth ->
      RegistersWithCounterIncrementWork n counterWidth :=
  fun x => (step x.1, x.2)

/-- Active-flag toggle lifted over the dedicated counter-increment work
object. -/
def counterWorkActiveFlagToggleStep (n counterWidth : Nat) :
    RegistersWithCounterIncrementWork n counterWidth ->
      RegistersWithCounterIncrementWork n counterWidth :=
  liftRegisterStepToCounterIncrementWork n counterWidth
    (activeFlagToggleStep n counterWidth)

/-- Base-gate program for the active-flag toggle lifted over counter work. -/
def counterWorkActiveFlagToggleProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCounterIncrementWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix
    (counterIncrementWorkEncoding counterWidth).width
    (activeFlagToggleProgram n counterWidth)

/-- The lifted active-flag toggle realizes its product-lifted semantic action. -/
theorem counterWorkActiveFlagToggle_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithCounterIncrementWorkEncoding n counterWidth)
      (counterWorkActiveFlagToggleProgram n counterWidth)
      (counterWorkActiveFlagToggleStep n counterWidth) := by
  unfold counterWorkActiveFlagToggleProgram counterWorkActiveFlagToggleStep
    liftRegisterStepToCounterIncrementWork
  exact UnitaryCircuit.Realizes.onBinaryPrefix
    (right := counterIncrementWorkEncoding counterWidth)
    (activeFlagToggle_realizes n counterWidth)

/-- Concrete terminating counter-mode program: clear the active flag, then
increment the padding counter with clean work. -/
def terminatingCounterModeWithWorkProgram (n counterWidth : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registersWithCounterIncrementWorkEncoding n counterWidth).width).toQuantum :=
  UnitaryCircuit.seq
    (counterWorkActiveFlagToggleProgram n counterWidth)
    (counterIncrementWithWorkProgram n counterWidth)

/-- Semantic action for the terminating counter-mode program. -/
def terminatingCounterModeWithWorkStep (n counterWidth : Nat) :
    RegistersWithCounterIncrementWork n counterWidth ->
      RegistersWithCounterIncrementWork n counterWidth :=
  fun x =>
    counterIncrementWithWorkStep n counterWidth
      (counterWorkActiveFlagToggleStep n counterWidth x)

/-- The terminating counter-mode program realizes the composed flag-clear and
padding-counter increment action. -/
theorem terminatingCounterModeWithWork_realizes (n counterWidth : Nat) :
    UnitaryCircuit.Realizes
      (registersWithCounterIncrementWorkEncoding n counterWidth)
      (terminatingCounterModeWithWorkProgram n counterWidth)
      (terminatingCounterModeWithWorkStep n counterWidth) := by
  unfold terminatingCounterModeWithWorkProgram
    terminatingCounterModeWithWorkStep
  exact UnitaryCircuit.Realizes.seq
    (firstStep := counterWorkActiveFlagToggleStep n counterWidth)
    (secondStep := counterIncrementWithWorkStep n counterWidth)
    (counterWorkActiveFlagToggle_realizes n counterWidth)
    (counterIncrementWithWork_realizes n counterWidth)

/-- On clean counter-increment work and an active input, the terminating
counter-mode wrapper clears `active`, increments the padding counter, and
restores its work object. -/
theorem terminatingCounterModeWithWorkStep_cleanEndpoint
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hactive : x.active = true) :
    terminatingCounterModeWithWorkStep n counterWidth
        (x, cleanCounterIncrementWork counterWidth) =
      ({ x with
          active := false,
          counter := wordIncrement counterWidth x.counter },
        cleanCounterIncrementWork counterWidth) := by
  rw [terminatingCounterModeWithWorkStep, counterWorkActiveFlagToggleStep,
    liftRegisterStepToCounterIncrementWork,
    counterIncrementWithWorkStep_cleanEndpoint]
  simp [activeFlagToggleStep_u, activeFlagToggleStep_v,
    activeFlagToggleStep_compare, activeFlagToggleStep_sCoeff,
    activeFlagToggleStep_rCoeff, activeFlagToggleStep_scratchA,
    activeFlagToggleStep_scratchB, activeFlagToggleStep_history,
    activeFlagToggleStep_active_of_active, activeFlagToggleStep_counter,
    hactive]

/-- One X atom that toggles the low bit of the padding counter.  This narrow
bit-slice is retained as a reusable atom; the full clean-work incrementer is
provided separately. -/
def counterLowToggleGate (n tail : Nat) :
    EncodedBit.GateSpec (registerEncoding n tail.succ) :=
  EncodedBit.GateSpec.x
    (RegisterBits.counterBit n tail.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ)))

/-- Base-gate program for `counterLowToggleGate`. -/
def counterLowToggleProgram (n tail : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n tail.succ).width).toQuantum :=
  EncodedBit.GateSpec.program (counterLowToggleGate n tail)
    (QubitLayout.canonical _) .empty

/-- Semantic step implemented by `counterLowToggleProgram`. -/
def counterLowToggleStep (n tail : Nat) :
    Registers n tail.succ -> Registers n tail.succ :=
  EncodedBit.GateSpec.step (counterLowToggleGate n tail)

/-- The counter-low X atom is a concrete encoded-bit base-gate realization over
the Montgomery--Kaliski register layout. -/
theorem counterLowToggle_realizes (n tail : Nat) :
    UnitaryCircuit.Realizes (registerEncoding n tail.succ)
      (counterLowToggleProgram n tail)
      (counterLowToggleStep n tail) :=
  EncodedBit.GateSpec.realizes (QubitLayout.canonical _) .empty
    (counterLowToggleGate n tail)

/-- The counter-low X atom toggles the low padding-counter bit. -/
theorem counterLowToggleStep_get_counterBit_zero
    (n tail : Nat) (x : Registers n tail.succ) :
    (RegisterBits.counterBit n tail.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
        (counterLowToggleStep n tail x) =
      ! (RegisterBits.counterBit n tail.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x := by
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_self
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ))) x

/-- The counter-low X atom makes the low padding-counter bit agree with the low
bit of the width-preserving counter increment. -/
theorem counterLowToggleStep_get_counterBit_zero_eq_wordIncrement
    (n tail : Nat) (x : Registers n tail.succ) :
    (RegisterBits.counterBit n tail.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ))).get
        (counterLowToggleStep n tail x) =
      (wordIncrement tail.succ x.counter).val.testBit 0 := by
  rw [counterLowToggleStep_get_counterBit_zero, wordIncrement_testBit_zero]
  simp [RegisterBits.counterBit_get]

/-- The counter-low X atom preserves every non-low padding-counter value bit. -/
theorem counterLowToggleStep_get_counterBit_succ
    (n tail : Nat) (bit : Fin tail) (x : Registers n tail.succ) :
    (RegisterBits.counterBit n tail.succ
        (WireAddress.littleEndianWire bit.succ)).get
        (counterLowToggleStep n tail x) =
      (RegisterBits.counterBit n tail.succ
        (WireAddress.littleEndianWire bit.succ)).get x := by
  have hne : (0 : Fin tail.succ) ≠ bit.succ := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire bit.succ))
        (counterValue_counterValue_wire_ne n tail.succ
          (0 : Fin tail.succ) bit.succ hne) x

/-- The counter-low X atom preserves the active flag readout. -/
theorem counterLowToggleStep_get_active
    (n tail : Nat) (x : Registers n tail.succ) :
    (RegisterBits.activeBit n tail.succ).get
        (counterLowToggleStep n tail x) =
      (RegisterBits.activeBit n tail.succ).get x := by
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.activeBit n tail.succ)
        (Ne.symm (RegisterBits.active_counter_wire_ne n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))) x

/-- The counter-low X atom preserves the concrete active field. -/
theorem counterLowToggleStep_active
    (n tail : Nat) (x : Registers n tail.succ) :
    (counterLowToggleStep n tail x).active = x.active := by
  simpa [RegisterBits.activeBit_get] using
    counterLowToggleStep_get_active n tail x

/-- The counter-low X atom preserves the `u` word. -/
theorem counterLowToggleStep_u
    (n tail : Nat) (x : Registers n tail.succ) :
    (counterLowToggleStep n tail x).u = x.u := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.uValueBit n tail.succ bit)
        (Ne.symm (RegisterBits.u_counter_wire_ne n tail.succ
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))) x

/-- The counter-low X atom preserves the `v` word. -/
theorem counterLowToggleStep_v
    (n tail : Nat) (x : Registers n tail.succ) :
    (counterLowToggleStep n tail x).v = x.v := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.vValueBit n tail.succ bit)
        (Ne.symm (RegisterBits.v_counter_wire_ne n tail.succ
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))) x

/-- The counter-low X atom preserves the `s` coefficient word. -/
theorem counterLowToggleStep_sCoeff
    (n tail : Nat) (x : Registers n tail.succ) :
    (counterLowToggleStep n tail x).sCoeff = x.sCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.sCoeffValueBit n tail.succ bit)
        (Ne.symm (RegisterBits.sCoeff_counter_wire_ne n tail.succ
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))) x

/-- The counter-low X atom preserves the `r` coefficient word. -/
theorem counterLowToggleStep_rCoeff
    (n tail : Nat) (x : Registers n tail.succ) :
    (counterLowToggleStep n tail x).rCoeff = x.rCoeff := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.rCoeffValueBit n tail.succ bit)
        (Ne.symm (RegisterBits.rCoeff_counter_wire_ne n tail.succ
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))) x

/-- The counter-low X atom preserves the comparison ancilla. -/
theorem counterLowToggleStep_compare
    (n tail : Nat) (x : Registers n tail.succ) :
    (counterLowToggleStep n tail x).compare = x.compare := by
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.compareBit n tail.succ)
        (Ne.symm (RegisterBits.compare_counter_wire_ne n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))) x

/-- The counter-low X atom preserves the first scratch bit. -/
theorem counterLowToggleStep_scratchA
    (n tail : Nat) (x : Registers n tail.succ) :
    (counterLowToggleStep n tail x).scratchA = x.scratchA := by
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step, RegisterBits.scratchABit_get] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.scratchABit n tail.succ)
        (Ne.symm (RegisterBits.scratchA_counter_wire_ne n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))) x

/-- The counter-low X atom preserves the second scratch bit. -/
theorem counterLowToggleStep_scratchB
    (n tail : Nat) (x : Registers n tail.succ) :
    (counterLowToggleStep n tail x).scratchB = x.scratchB := by
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step, RegisterBits.scratchBBit_get] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.scratchBBit n tail.succ)
        (Ne.symm (RegisterBits.scratchB_counter_wire_ne n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))) x

/-- The counter-low X atom preserves the branch-history word. -/
theorem counterLowToggleStep_history
    (n tail : Nat) (x : Registers n tail.succ) :
    (counterLowToggleStep n tail x).history = x.history := by
  apply word_eq_of_testBit_eq
  intro bit
  simpa [counterLowToggleStep, counterLowToggleGate,
    EncodedBit.GateSpec.step, RegisterBits.historyBit_get] using
      EncodedBit.get_flip_of_wire_ne
        (RegisterBits.counterBit n tail.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))
        (RegisterBits.historyBit n tail.succ
          (WireAddress.littleEndianWire bit))
        (Ne.symm (RegisterBits.history_counter_wire_ne n tail.succ
          (WireAddress.littleEndianWire bit)
          (WireAddress.littleEndianWire (0 : Fin tail.succ)))) x

/-- One CNOT atom that propagates the low padding-counter carry into the
second-lowest counter value bit.  This is the next bit-slice of the incrementer;
higher carries remain separate obligations. -/
def counterLowCarryGate (n tail : Nat) :
    EncodedBit.GateSpec (registerEncoding n tail.succ.succ) :=
  EncodedBit.GateSpec.cnot
    (RegisterBits.counterBit n tail.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ)))
    (RegisterBits.counterBit n tail.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ)))
    (counterValue_counterValue_wire_ne n tail.succ.succ
      (0 : Fin tail.succ.succ) (1 : Fin tail.succ.succ)
      (by
        intro h
        have hval := congrArg Fin.val h
        simp at hval))

/-- Base-gate program for `counterLowCarryGate`. -/
def counterLowCarryProgram (n tail : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n tail.succ.succ).width).toQuantum :=
  EncodedBit.GateSpec.program (counterLowCarryGate n tail)
    (QubitLayout.canonical _) .empty

/-- Semantic step implemented by `counterLowCarryProgram`. -/
def counterLowCarryStep (n tail : Nat) :
    Registers n tail.succ.succ -> Registers n tail.succ.succ :=
  EncodedBit.GateSpec.step (counterLowCarryGate n tail)

/-- The low-carry CNOT atom is a concrete encoded-bit base-gate realization
over the Montgomery--Kaliski register layout. -/
theorem counterLowCarry_realizes (n tail : Nat) :
    UnitaryCircuit.Realizes (registerEncoding n tail.succ.succ)
      (counterLowCarryProgram n tail)
      (counterLowCarryStep n tail) :=
  EncodedBit.GateSpec.realizes (QubitLayout.canonical _) .empty
    (counterLowCarryGate n tail)

/-- The low-carry CNOT atom toggles the second-lowest counter value bit exactly
when the low counter value bit is set. -/
theorem counterLowCarryStep_get_counterBit_one
    (n tail : Nat) (x : Registers n tail.succ.succ) :
    (RegisterBits.counterBit n tail.succ.succ
        (WireAddress.littleEndianWire (1 : Fin tail.succ.succ))).get
        (counterLowCarryStep n tail x) =
      ((RegisterBits.counterBit n tail.succ.succ
        (WireAddress.littleEndianWire (1 : Fin tail.succ.succ))).get x ^^
        (RegisterBits.counterBit n tail.succ.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ.succ))).get x) := by
  simpa [counterLowCarryStep, counterLowCarryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.cnotStep_get_target
        (RegisterBits.counterBit n tail.succ.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ.succ)))
        (RegisterBits.counterBit n tail.succ.succ
          (WireAddress.littleEndianWire (1 : Fin tail.succ.succ))) x

/-- The low-carry CNOT atom preserves the low counter value bit. -/
theorem counterLowCarryStep_get_counterBit_zero
    (n tail : Nat) (x : Registers n tail.succ.succ) :
    (RegisterBits.counterBit n tail.succ.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ.succ))).get
        (counterLowCarryStep n tail x) =
      (RegisterBits.counterBit n tail.succ.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ.succ))).get x := by
  simpa [counterLowCarryStep, counterLowCarryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.cnotStep_get_of_target_ne
        (RegisterBits.counterBit n tail.succ.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ.succ)))
        (RegisterBits.counterBit n tail.succ.succ
          (WireAddress.littleEndianWire (1 : Fin tail.succ.succ)))
        (RegisterBits.counterBit n tail.succ.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ.succ)))
        (Ne.symm (counterValue_counterValue_wire_ne n tail.succ.succ
          (0 : Fin tail.succ.succ) (1 : Fin tail.succ.succ)
          (by
            intro h
            have hval := congrArg Fin.val h
            simp at hval))) x

/-- Gate list for the two-low-bit prefix of the padding-counter incrementer.
The carry CNOT must run before the low-bit X atom so the carry observes the
original low bit. -/
def counterTwoLowIncrementGates (n tail : Nat) :
    List (EncodedBit.GateSpec (registerEncoding n tail.succ.succ)) :=
  [counterLowCarryGate n tail, counterLowToggleGate n tail.succ]

/-- Base-gate program for the two-low-bit increment prefix. -/
def counterTwoLowIncrementProgram (n tail : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n tail.succ.succ).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (counterTwoLowIncrementGates n tail)

/-- Semantic step implemented by `counterTwoLowIncrementProgram`. -/
def counterTwoLowIncrementStep (n tail : Nat) :
    Registers n tail.succ.succ -> Registers n tail.succ.succ :=
  EncodedBit.GateSpec.stepList (counterTwoLowIncrementGates n tail)

/-- The two-low-bit increment prefix is a concrete encoded-bit base-gate
realization over the Montgomery--Kaliski register layout. -/
theorem counterTwoLowIncrement_realizes (n tail : Nat) :
    UnitaryCircuit.Realizes (registerEncoding n tail.succ.succ)
      (counterTwoLowIncrementProgram n tail)
      (counterTwoLowIncrementStep n tail) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (counterTwoLowIncrementGates n tail)

/-- The two-low-bit prefix makes the low counter bit agree with the
width-preserving counter increment. -/
theorem counterTwoLowIncrementStep_get_counterBit_zero_eq_wordIncrement
    (n tail : Nat) (x : Registers n tail.succ.succ) :
    (RegisterBits.counterBit n tail.succ.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ.succ))).get
        (counterTwoLowIncrementStep n tail x) =
      (wordIncrement tail.succ.succ x.counter).val.testBit 0 := by
  rw [counterTwoLowIncrementStep, counterTwoLowIncrementGates]
  change
    (RegisterBits.counterBit n tail.succ.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ.succ))).get
        (counterLowToggleStep n tail.succ (counterLowCarryStep n tail x)) =
      (wordIncrement tail.succ.succ x.counter).val.testBit 0
  rw [counterLowToggleStep_get_counterBit_zero]
  rw [counterLowCarryStep_get_counterBit_zero]
  rw [wordIncrement_testBit_zero]
  simp [RegisterBits.counterBit_get]

/-- The two-low-bit prefix makes the second-lowest counter bit agree with the
width-preserving counter increment. -/
theorem counterTwoLowIncrementStep_get_counterBit_one_eq_wordIncrement
    (n tail : Nat) (x : Registers n tail.succ.succ) :
    (RegisterBits.counterBit n tail.succ.succ
        (WireAddress.littleEndianWire (1 : Fin tail.succ.succ))).get
        (counterTwoLowIncrementStep n tail x) =
      (wordIncrement tail.succ.succ x.counter).val.testBit 1 := by
  rw [counterTwoLowIncrementStep, counterTwoLowIncrementGates]
  change
    (RegisterBits.counterBit n tail.succ.succ
        (WireAddress.littleEndianWire (1 : Fin tail.succ.succ))).get
        (counterLowToggleStep n tail.succ (counterLowCarryStep n tail x)) =
      (wordIncrement tail.succ.succ x.counter).val.testBit 1
  rw [show
      (RegisterBits.counterBit n tail.succ.succ
        (WireAddress.littleEndianWire (1 : Fin tail.succ.succ))).get
          (counterLowToggleStep n tail.succ
            (counterLowCarryStep n tail x)) =
        (RegisterBits.counterBit n tail.succ.succ
          (WireAddress.littleEndianWire (1 : Fin tail.succ.succ))).get
          (counterLowCarryStep n tail x) by
    simpa [counterLowToggleStep, counterLowToggleGate,
      EncodedBit.GateSpec.step] using
        EncodedBit.get_flip_of_wire_ne
          (RegisterBits.counterBit n tail.succ.succ
            (WireAddress.littleEndianWire (0 : Fin tail.succ.succ)))
          (RegisterBits.counterBit n tail.succ.succ
            (WireAddress.littleEndianWire (1 : Fin tail.succ.succ)))
          (counterValue_counterValue_wire_ne n tail.succ.succ
            (0 : Fin tail.succ.succ) (1 : Fin tail.succ.succ)
            (by
              intro h
              have hval := congrArg Fin.val h
              simp at hval))
          (counterLowCarryStep n tail x)]
  rw [counterLowCarryStep_get_counterBit_one]
  rw [wordIncrement_testBit_one]
  simp [RegisterBits.counterBit_get]

/-- Toffoli atom that computes the original low-two-bit counter carry into the
first scratch bit.  It is used before the low bits are toggled, and is run
again to restore the scratch bit. -/
def counterBitTwoCarryToScratchGate (n tail : Nat) :
    EncodedBit.GateSpec (registerEncoding n tail.succ.succ.succ) :=
  EncodedBit.GateSpec.toffoli
    (RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ)))
    (RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ)))
    (RegisterBits.scratchABit n tail.succ.succ.succ)
    (counterValue_counterValue_wire_ne n tail.succ.succ.succ
      (0 : Fin tail.succ.succ.succ) (1 : Fin tail.succ.succ.succ)
      (by
        intro h
        have hval := congrArg Fin.val h
        simp at hval))
    (Ne.symm (RegisterBits.scratchA_counter_wire_ne n tail.succ.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))))
    (Ne.symm (RegisterBits.scratchA_counter_wire_ne n tail.succ.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))))

/-- CNOT atom that propagates the scratch-carried low-two-bit carry into the
third-lowest counter bit. -/
def counterScratchCarryToBitTwoGate (n tail : Nat) :
    EncodedBit.GateSpec (registerEncoding n tail.succ.succ.succ) :=
  EncodedBit.GateSpec.cnot
    (RegisterBits.scratchABit n tail.succ.succ.succ)
    (RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ)))
    (RegisterBits.scratchA_counter_wire_ne n tail.succ.succ.succ
      (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ)))

/-- Gate list for computing the carry into counter bit two and restoring the
scratch bit. -/
def counterBitTwoCarryPrefixGates (n tail : Nat) :
    List (EncodedBit.GateSpec (registerEncoding n tail.succ.succ.succ)) :=
  [ counterBitTwoCarryToScratchGate n tail
  , counterScratchCarryToBitTwoGate n tail
  , counterBitTwoCarryToScratchGate n tail ]

/-- Base-gate program for the carry-into-bit-two prefix. -/
def counterBitTwoCarryPrefixProgram (n tail : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n tail.succ.succ.succ).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (counterBitTwoCarryPrefixGates n tail)

/-- Semantic step implemented by `counterBitTwoCarryPrefixProgram`. -/
def counterBitTwoCarryPrefixStep (n tail : Nat) :
    Registers n tail.succ.succ.succ -> Registers n tail.succ.succ.succ :=
  EncodedBit.GateSpec.stepList (counterBitTwoCarryPrefixGates n tail)

/-- The carry-into-bit-two prefix is a concrete encoded-bit base-gate
realization over the Montgomery--Kaliski register layout. -/
theorem counterBitTwoCarryPrefix_realizes (n tail : Nat) :
    UnitaryCircuit.Realizes (registerEncoding n tail.succ.succ.succ)
      (counterBitTwoCarryPrefixProgram n tail)
      (counterBitTwoCarryPrefixStep n tail) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (counterBitTwoCarryPrefixGates n tail)

/-- Gate list for the three-low-bit prefix of the padding-counter incrementer.
The bit-two carry is computed and cleaned before the lower two bits are
mutated. -/
def counterThreeLowIncrementGates (n tail : Nat) :
    List (EncodedBit.GateSpec (registerEncoding n tail.succ.succ.succ)) :=
  counterBitTwoCarryPrefixGates n tail ++
    counterTwoLowIncrementGates n tail.succ

/-- Base-gate program for the three-low-bit increment prefix. -/
def counterThreeLowIncrementProgram (n tail : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n tail.succ.succ.succ).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (counterThreeLowIncrementGates n tail)

/-- Semantic step implemented by `counterThreeLowIncrementProgram`. -/
def counterThreeLowIncrementStep (n tail : Nat) :
    Registers n tail.succ.succ.succ -> Registers n tail.succ.succ.succ :=
  EncodedBit.GateSpec.stepList (counterThreeLowIncrementGates n tail)

/-- The three-low-bit increment prefix is a concrete encoded-bit base-gate
realization over the Montgomery--Kaliski register layout. -/
theorem counterThreeLowIncrement_realizes (n tail : Nat) :
    UnitaryCircuit.Realizes (registerEncoding n tail.succ.succ.succ)
      (counterThreeLowIncrementProgram n tail)
      (counterThreeLowIncrementStep n tail) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (counterThreeLowIncrementGates n tail)

/-- The low-carry CNOT atom preserves the first scratch bit readout. -/
theorem counterLowCarryStep_get_scratchA
    (n tail : Nat) (x : Registers n tail.succ.succ) :
    (RegisterBits.scratchABit n tail.succ.succ).get
        (counterLowCarryStep n tail x) =
      (RegisterBits.scratchABit n tail.succ.succ).get x := by
  simpa [counterLowCarryStep, counterLowCarryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.cnotStep_get_of_target_ne
        (RegisterBits.counterBit n tail.succ.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ.succ)))
        (RegisterBits.counterBit n tail.succ.succ
          (WireAddress.littleEndianWire (1 : Fin tail.succ.succ)))
        (RegisterBits.scratchABit n tail.succ.succ)
        (Ne.symm (RegisterBits.scratchA_counter_wire_ne n tail.succ.succ
          (WireAddress.littleEndianWire (1 : Fin tail.succ.succ)))) x

/-- The low-carry CNOT atom preserves the concrete first scratch field. -/
theorem counterLowCarryStep_scratchA
    (n tail : Nat) (x : Registers n tail.succ.succ) :
    (counterLowCarryStep n tail x).scratchA = x.scratchA := by
  simpa [RegisterBits.scratchABit_get] using
    counterLowCarryStep_get_scratchA n tail x

/-- The two-low-bit increment prefix preserves the third-lowest counter bit
when the counter has at least three bits. -/
theorem counterTwoLowIncrementStep_get_counterBit_two
    (n tail : Nat) (x : Registers n tail.succ.succ.succ) :
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))).get
        (counterTwoLowIncrementStep n tail.succ x) =
      (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))).get x := by
  let bit0 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))
  let bit1 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))
  let bit2 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))
  have hbit0Bit2 : bit0.wire ≠ bit2.wire := by
    dsimp [bit0, bit2]
    exact counterValue_counterValue_wire_ne n tail.succ.succ.succ
      (0 : Fin tail.succ.succ.succ) (2 : Fin tail.succ.succ.succ)
      (by
        intro h
        have hval := congrArg Fin.val h
        have hmod : 2 % tail.succ.succ.succ = 2 :=
          Nat.mod_eq_of_lt (by omega)
        simp [hmod] at hval)
  have hbit1Bit2 : bit1.wire ≠ bit2.wire := by
    dsimp [bit1, bit2]
    exact counterValue_counterValue_wire_ne n tail.succ.succ.succ
      (1 : Fin tail.succ.succ.succ) (2 : Fin tail.succ.succ.succ)
      (by
        intro h
        have hval := congrArg Fin.val h
        have hmod : 2 % tail.succ.succ.succ = 2 :=
          Nat.mod_eq_of_lt (by omega)
        simp [hmod] at hval)
  rw [counterTwoLowIncrementStep, counterTwoLowIncrementGates]
  change bit2.get
      (counterLowToggleStep n tail.succ.succ
        (counterLowCarryStep n tail.succ x)) = bit2.get x
  rw [show
      bit2.get
          (counterLowToggleStep n tail.succ.succ
            (counterLowCarryStep n tail.succ x)) =
        bit2.get (counterLowCarryStep n tail.succ x) by
    simpa [counterLowToggleStep, counterLowToggleGate,
      EncodedBit.GateSpec.step, bit0, bit2] using
        EncodedBit.get_flip_of_wire_ne bit0 bit2 hbit0Bit2
          (counterLowCarryStep n tail.succ x)]
  simpa [counterLowCarryStep, counterLowCarryGate,
    EncodedBit.GateSpec.step, bit0, bit1, bit2] using
      EncodedBit.cnotStep_get_of_target_ne bit0 bit1 bit2 hbit1Bit2 x

/-- The two-low-bit increment prefix preserves the concrete first scratch
field. -/
theorem counterTwoLowIncrementStep_scratchA
    (n tail : Nat) (x : Registers n tail.succ.succ) :
    (counterTwoLowIncrementStep n tail x).scratchA = x.scratchA := by
  rw [counterTwoLowIncrementStep, counterTwoLowIncrementGates]
  change
    (counterLowToggleStep n tail.succ (counterLowCarryStep n tail x)).scratchA =
      x.scratchA
  rw [counterLowToggleStep_scratchA]
  exact counterLowCarryStep_scratchA n tail x

/-- The carry-into-bit-two prefix preserves the low counter bit. -/
theorem counterBitTwoCarryPrefixStep_get_counterBit_zero
    (n tail : Nat) (x : Registers n tail.succ.succ.succ) :
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))).get
        (counterBitTwoCarryPrefixStep n tail x) =
      (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))).get x := by
  let bit0 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))
  let bit1 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))
  let bit2 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))
  let scratch := RegisterBits.scratchABit n tail.succ.succ.succ
  have hscratchBit0 : scratch.wire ≠ bit0.wire := by
    dsimp [scratch, bit0]
    exact RegisterBits.scratchA_counter_wire_ne n tail.succ.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))
  have hbit2Bit0 : bit2.wire ≠ bit0.wire := by
    dsimp [bit2, bit0]
    exact counterValue_counterValue_wire_ne n tail.succ.succ.succ
      (2 : Fin tail.succ.succ.succ) (0 : Fin tail.succ.succ.succ)
      (by
        intro h
        have hval := congrArg Fin.val h
        have hmod : 2 % tail.succ.succ.succ = 2 :=
          Nat.mod_eq_of_lt (by omega)
        simp [hmod] at hval)
  rw [counterBitTwoCarryPrefixStep, counterBitTwoCarryPrefixGates,
    counterBitTwoCarryToScratchGate, counterScratchCarryToBitTwoGate]
  change bit0.get
      (EncodedBit.toffoliStep bit0 bit1 scratch
        (EncodedBit.cnotStep scratch bit2
          (EncodedBit.toffoliStep bit0 bit1 scratch x))) = bit0.get x
  rw [EncodedBit.toffoliStep_get_of_target_ne bit0 bit1 scratch bit0
    hscratchBit0]
  rw [EncodedBit.cnotStep_get_of_target_ne scratch bit2 bit0 hbit2Bit0]
  rw [EncodedBit.toffoliStep_get_of_target_ne bit0 bit1 scratch bit0
    hscratchBit0]

/-- The carry-into-bit-two prefix preserves the second-lowest counter bit. -/
theorem counterBitTwoCarryPrefixStep_get_counterBit_one
    (n tail : Nat) (x : Registers n tail.succ.succ.succ) :
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))).get
        (counterBitTwoCarryPrefixStep n tail x) =
      (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))).get x := by
  let bit0 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))
  let bit1 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))
  let bit2 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))
  let scratch := RegisterBits.scratchABit n tail.succ.succ.succ
  have hscratchBit1 : scratch.wire ≠ bit1.wire := by
    dsimp [scratch, bit1]
    exact RegisterBits.scratchA_counter_wire_ne n tail.succ.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))
  have hbit2Bit1 : bit2.wire ≠ bit1.wire := by
    dsimp [bit2, bit1]
    exact counterValue_counterValue_wire_ne n tail.succ.succ.succ
      (2 : Fin tail.succ.succ.succ) (1 : Fin tail.succ.succ.succ)
      (by
        intro h
        have hval := congrArg Fin.val h
        have hmod : 2 % tail.succ.succ.succ = 2 :=
          Nat.mod_eq_of_lt (by omega)
        simp [hmod] at hval)
  rw [counterBitTwoCarryPrefixStep, counterBitTwoCarryPrefixGates,
    counterBitTwoCarryToScratchGate, counterScratchCarryToBitTwoGate]
  change bit1.get
      (EncodedBit.toffoliStep bit0 bit1 scratch
        (EncodedBit.cnotStep scratch bit2
          (EncodedBit.toffoliStep bit0 bit1 scratch x))) = bit1.get x
  rw [EncodedBit.toffoliStep_get_of_target_ne bit0 bit1 scratch bit1
    hscratchBit1]
  rw [EncodedBit.cnotStep_get_of_target_ne scratch bit2 bit1 hbit2Bit1]
  rw [EncodedBit.toffoliStep_get_of_target_ne bit0 bit1 scratch bit1
    hscratchBit1]

/-- The carry-into-bit-two prefix restores the first scratch bit. -/
theorem counterBitTwoCarryPrefixStep_get_scratchA
    (n tail : Nat) (x : Registers n tail.succ.succ.succ) :
    (RegisterBits.scratchABit n tail.succ.succ.succ).get
        (counterBitTwoCarryPrefixStep n tail x) =
      (RegisterBits.scratchABit n tail.succ.succ.succ).get x := by
  let bit0 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))
  let bit1 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))
  let bit2 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))
  let scratch := RegisterBits.scratchABit n tail.succ.succ.succ
  let y := EncodedBit.toffoliStep bit0 bit1 scratch x
  let middle := EncodedBit.cnotStep scratch bit2 y
  have hscratchBit0 : scratch.wire ≠ bit0.wire := by
    dsimp [scratch, bit0]
    exact RegisterBits.scratchA_counter_wire_ne n tail.succ.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))
  have hscratchBit1 : scratch.wire ≠ bit1.wire := by
    dsimp [scratch, bit1]
    exact RegisterBits.scratchA_counter_wire_ne n tail.succ.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))
  have hbit2Scratch : bit2.wire ≠ scratch.wire := by
    dsimp [bit2, scratch]
    exact Ne.symm (RegisterBits.scratchA_counter_wire_ne
      n tail.succ.succ.succ
      (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ)))
  have hbit2Bit0 : bit2.wire ≠ bit0.wire := by
    dsimp [bit2, bit0]
    exact counterValue_counterValue_wire_ne n tail.succ.succ.succ
      (2 : Fin tail.succ.succ.succ) (0 : Fin tail.succ.succ.succ)
      (by
        intro h
        have hval := congrArg Fin.val h
        have hmod : 2 % tail.succ.succ.succ = 2 :=
          Nat.mod_eq_of_lt (by omega)
        simp [hmod] at hval)
  have hbit2Bit1 : bit2.wire ≠ bit1.wire := by
    dsimp [bit2, bit1]
    exact counterValue_counterValue_wire_ne n tail.succ.succ.succ
      (2 : Fin tail.succ.succ.succ) (1 : Fin tail.succ.succ.succ)
      (by
        intro h
        have hval := congrArg Fin.val h
        have hmod : 2 % tail.succ.succ.succ = 2 :=
          Nat.mod_eq_of_lt (by omega)
        simp [hmod] at hval)
  have hscratchMiddle : scratch.get middle = scratch.get y := by
    dsimp [middle]
    exact EncodedBit.cnotStep_get_of_target_ne scratch bit2 scratch
      hbit2Scratch y
  have hbit0Y : bit0.get y = bit0.get x := by
    dsimp [y]
    exact EncodedBit.toffoliStep_get_of_target_ne bit0 bit1 scratch bit0
      hscratchBit0 x
  have hbit1Y : bit1.get y = bit1.get x := by
    dsimp [y]
    exact EncodedBit.toffoliStep_get_of_target_ne bit0 bit1 scratch bit1
      hscratchBit1 x
  have hbit0Middle : bit0.get middle = bit0.get x := by
    dsimp [middle]
    rw [EncodedBit.cnotStep_get_of_target_ne scratch bit2 bit0 hbit2Bit0 y,
      hbit0Y]
  have hbit1Middle : bit1.get middle = bit1.get x := by
    dsimp [middle]
    rw [EncodedBit.cnotStep_get_of_target_ne scratch bit2 bit1 hbit2Bit1 y,
      hbit1Y]
  rw [counterBitTwoCarryPrefixStep, counterBitTwoCarryPrefixGates,
    counterBitTwoCarryToScratchGate, counterScratchCarryToBitTwoGate]
  change scratch.get (EncodedBit.toffoliStep bit0 bit1 scratch middle) =
    scratch.get x
  rw [EncodedBit.toffoliStep_get_target, hscratchMiddle, hbit0Middle,
    hbit1Middle]
  dsimp [y]
  rw [EncodedBit.toffoliStep_get_target]
  cases scratch.get x <;> cases bit0.get x <;> cases bit1.get x <;> simp

/-- The carry-into-bit-two prefix restores the concrete first scratch field. -/
theorem counterBitTwoCarryPrefixStep_scratchA
    (n tail : Nat) (x : Registers n tail.succ.succ.succ) :
    (counterBitTwoCarryPrefixStep n tail x).scratchA = x.scratchA := by
  simpa [RegisterBits.scratchABit_get] using
    counterBitTwoCarryPrefixStep_get_scratchA n tail x

/-- On a clean scratch input, the carry-into-bit-two prefix toggles bit two
exactly when the two lower counter bits are both set. -/
theorem counterBitTwoCarryPrefixStep_get_counterBit_two_clean
    (n tail : Nat) (x : Registers n tail.succ.succ.succ)
    (hscratchA :
      (RegisterBits.scratchABit n tail.succ.succ.succ).get x = false) :
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))).get
        (counterBitTwoCarryPrefixStep n tail x) =
      ((RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))).get x ^^
        ((RegisterBits.counterBit n tail.succ.succ.succ
          (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))).get x &&
          (RegisterBits.counterBit n tail.succ.succ.succ
            (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))).get
            x)) := by
  let bit0 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))
  let bit1 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))
  let bit2 :=
    RegisterBits.counterBit n tail.succ.succ.succ
      (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))
  let scratch := RegisterBits.scratchABit n tail.succ.succ.succ
  let y := EncodedBit.toffoliStep bit0 bit1 scratch x
  let middle := EncodedBit.cnotStep scratch bit2 y
  have hscratchBit2 : scratch.wire ≠ bit2.wire := by
    dsimp [scratch, bit2]
    exact RegisterBits.scratchA_counter_wire_ne n tail.succ.succ.succ
      (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))
  have hbit2Scratch : bit2.wire ≠ scratch.wire := Ne.symm hscratchBit2
  have hscratchY :
      scratch.get y = (scratch.get x ^^ (bit0.get x && bit1.get x)) := by
    dsimp [y]
    rw [EncodedBit.toffoliStep_get_target]
  have hbit2Y : bit2.get y = bit2.get x := by
    dsimp [y]
    exact EncodedBit.toffoliStep_get_of_target_ne bit0 bit1 scratch bit2
      hscratchBit2 x
  rw [counterBitTwoCarryPrefixStep, counterBitTwoCarryPrefixGates,
    counterBitTwoCarryToScratchGate, counterScratchCarryToBitTwoGate]
  change bit2.get (EncodedBit.toffoliStep bit0 bit1 scratch middle) =
    (bit2.get x ^^ (bit0.get x && bit1.get x))
  rw [EncodedBit.toffoliStep_get_of_target_ne bit0 bit1 scratch bit2
    hscratchBit2]
  dsimp [middle]
  rw [EncodedBit.cnotStep_get_target, hbit2Y, hscratchY, hscratchA]
  cases bit2.get x <;> cases bit0.get x <;> cases bit1.get x <;> simp

/-- The three-low-bit prefix makes the low counter bit agree with the
width-preserving counter increment. -/
theorem counterThreeLowIncrementStep_get_counterBit_zero_eq_wordIncrement
    (n tail : Nat) (x : Registers n tail.succ.succ.succ)
    (_hscratchA : x.scratchA = false) :
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))).get
        (counterThreeLowIncrementStep n tail x) =
      (wordIncrement tail.succ.succ.succ x.counter).val.testBit 0 := by
  rw [counterThreeLowIncrementStep, counterThreeLowIncrementGates,
    EncodedBit.GateSpec.stepList_append]
  change
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (0 : Fin tail.succ.succ.succ))).get
        (counterTwoLowIncrementStep n tail.succ
          (counterBitTwoCarryPrefixStep n tail x)) =
      (wordIncrement tail.succ.succ.succ x.counter).val.testBit 0
  rw [counterTwoLowIncrementStep_get_counterBit_zero_eq_wordIncrement]
  rw [wordIncrement_testBit_zero, wordIncrement_testBit_zero]
  have hprefix := counterBitTwoCarryPrefixStep_get_counterBit_zero n tail x
  simpa [RegisterBits.counterBit_get] using congrArg not hprefix

/-- The three-low-bit prefix makes the second-lowest counter bit agree with the
width-preserving counter increment. -/
theorem counterThreeLowIncrementStep_get_counterBit_one_eq_wordIncrement
    (n tail : Nat) (x : Registers n tail.succ.succ.succ)
    (_hscratchA : x.scratchA = false) :
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))).get
        (counterThreeLowIncrementStep n tail x) =
      (wordIncrement tail.succ.succ.succ x.counter).val.testBit 1 := by
  rw [counterThreeLowIncrementStep, counterThreeLowIncrementGates,
    EncodedBit.GateSpec.stepList_append]
  change
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (1 : Fin tail.succ.succ.succ))).get
        (counterTwoLowIncrementStep n tail.succ
          (counterBitTwoCarryPrefixStep n tail x)) =
      (wordIncrement tail.succ.succ.succ x.counter).val.testBit 1
  rw [counterTwoLowIncrementStep_get_counterBit_one_eq_wordIncrement]
  rw [wordIncrement_testBit_one, wordIncrement_testBit_one]
  have hprefix0 := counterBitTwoCarryPrefixStep_get_counterBit_zero n tail x
  have hprefix1 := counterBitTwoCarryPrefixStep_get_counterBit_one n tail x
  simpa [RegisterBits.counterBit_get] using
    congrArg₂ (fun a b => a ^^ b) hprefix1 hprefix0

/-- On a clean scratch input, the three-low-bit prefix makes the third-lowest
counter bit agree with the width-preserving counter increment. -/
theorem counterThreeLowIncrementStep_get_counterBit_two_eq_wordIncrement
    (n tail : Nat) (x : Registers n tail.succ.succ.succ)
    (hscratchA : x.scratchA = false) :
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))).get
        (counterThreeLowIncrementStep n tail x) =
      (wordIncrement tail.succ.succ.succ x.counter).val.testBit 2 := by
  rw [counterThreeLowIncrementStep, counterThreeLowIncrementGates,
    EncodedBit.GateSpec.stepList_append]
  change
    (RegisterBits.counterBit n tail.succ.succ.succ
        (WireAddress.littleEndianWire (2 : Fin tail.succ.succ.succ))).get
        (counterTwoLowIncrementStep n tail.succ
          (counterBitTwoCarryPrefixStep n tail x)) =
      (wordIncrement tail.succ.succ.succ x.counter).val.testBit 2
  rw [counterTwoLowIncrementStep_get_counterBit_two]
  rw [counterBitTwoCarryPrefixStep_get_counterBit_two_clean]
  · rw [wordIncrement_testBit_two]
    have hmod : 2 % tail.succ.succ.succ = 2 :=
      Nat.mod_eq_of_lt (by omega)
    simp [RegisterBits.counterBit_get, hmod]
  · simpa [RegisterBits.scratchABit_get] using hscratchA

/-- The three-low-bit increment prefix preserves the concrete first scratch
field. -/
theorem counterThreeLowIncrementStep_scratchA
    (n tail : Nat) (x : Registers n tail.succ.succ.succ) :
    (counterThreeLowIncrementStep n tail x).scratchA = x.scratchA := by
  rw [counterThreeLowIncrementStep, counterThreeLowIncrementGates,
    EncodedBit.GateSpec.stepList_append]
  change
    (counterTwoLowIncrementStep n tail.succ
      (counterBitTwoCarryPrefixStep n tail x)).scratchA = x.scratchA
  rw [counterTwoLowIncrementStep_scratchA]
  exact counterBitTwoCarryPrefixStep_scratchA n tail x

/-- Concrete bit-level guard for `v = 0`: every little-endian `v` value bit is
false.  This is the semantic guard used before replacing it by a detector
circuit; it is not itself the detector implementation. -/
def vZeroGuard (n counterWidth : Nat) (x : Registers n counterWidth) : Prop :=
  forall bit : Fin n, (RegisterBits.vValueBit n counterWidth bit).get x = false

/-- The concrete `v`-zero bit guard implies the source-level `v = 0` fact. -/
theorem v_zero_of_vZeroGuard
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hguard : vZeroGuard n counterWidth x) :
    x.v.val = 0 := by
  have hv : x.v = (0 : Word n) := by
    apply word_eq_of_testBit_eq
    intro bit
    simpa using hguard bit
  exact congrArg Fin.val hv

/-- A source-level `v = 0` fact supplies the concrete bit-level guard. -/
theorem vZeroGuard_of_v_zero
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hv : x.v.val = 0) :
    vZeroGuard n counterWidth x := by
  intro bit
  exact RegisterBits.vValueBit_get_false_of_v_zero n counterWidth bit x hv

/-- One CNOT atom that xors the Kaliski active flag into a selected `m_i`
history bit.  This is a reusable branch-history write primitive for the
fixed-round RNSL17 route; it is not yet the full branch-selection circuit
[RNSL17, ECDLP.tex:468-475]. -/
def activeToHistoryGate (n counterWidth : Nat) (bit : Fin (2 * n)) :
    EncodedBit.GateSpec (registerEncoding n counterWidth) :=
  EncodedBit.GateSpec.cnot
    (RegisterBits.activeBit n counterWidth)
    (RegisterBits.historyBit n counterWidth bit)
    (RegisterBits.active_history_wire_ne n counterWidth bit)

/-- Base-gate program for `activeToHistoryGate`. -/
def activeToHistoryProgram (n counterWidth : Nat) (bit : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.program (activeToHistoryGate n counterWidth bit)
    (QubitLayout.canonical _) .empty

/-- Semantic step implemented by `activeToHistoryProgram`. -/
def activeToHistoryStep (n counterWidth : Nat) (bit : Fin (2 * n)) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.step (activeToHistoryGate n counterWidth bit)

/-- The active-to-history CNOT atom is a concrete encoded-bit base-gate
realization over the Montgomery--Kaliski register layout. -/
theorem activeToHistory_realizes (n counterWidth : Nat) (bit : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (activeToHistoryProgram n counterWidth bit)
      (activeToHistoryStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizes (QubitLayout.canonical _) .empty
    (activeToHistoryGate n counterWidth bit)

/-- The active-to-history atom toggles the selected history bit exactly when
the active flag is set. -/
theorem activeToHistoryStep_get_historyBit
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth bit).get
        (activeToHistoryStep n counterWidth bit x) =
      ((RegisterBits.historyBit n counterWidth bit).get x ^^
        (RegisterBits.activeBit n counterWidth).get x) := by
  simpa [activeToHistoryStep, activeToHistoryGate, EncodedBit.GateSpec.step]
    using
      EncodedBit.cnotStep_get_target
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.historyBit n counterWidth bit) x

/-- The active-to-history atom preserves the active flag. -/
theorem activeToHistoryStep_get_active
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (activeToHistoryStep n counterWidth bit x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  simpa [activeToHistoryStep, activeToHistoryGate, EncodedBit.GateSpec.step]
    using
      EncodedBit.cnotStep_get_of_target_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.historyBit n counterWidth bit)
        (RegisterBits.activeBit n counterWidth)
        (Ne.symm (RegisterBits.active_history_wire_ne n counterWidth bit)) x

/-- One Toffoli atom that writes a selected `m_i` history bit from the second
scratch bit, guarded by the active flag.  This is the branch-history write
primitive used once `scratchB` stores the RNSL17 branch-history code bit; it is
not yet the full branch-selection circuit [RNSL17, ECDLP.tex:468-475]. -/
def activeScratchBToHistoryGate
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    EncodedBit.GateSpec (registerEncoding n counterWidth) :=
  EncodedBit.GateSpec.toffoli
    (RegisterBits.activeBit n counterWidth)
    (RegisterBits.scratchBBit n counterWidth)
    (RegisterBits.historyBit n counterWidth bit)
    (RegisterBits.active_scratchB_wire_ne n counterWidth)
    (RegisterBits.active_history_wire_ne n counterWidth bit)
    (RegisterBits.scratchB_history_wire_ne n counterWidth bit)

/-- Base-gate program for `activeScratchBToHistoryGate`. -/
def activeScratchBToHistoryProgram
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.program
    (activeScratchBToHistoryGate n counterWidth bit)
    (QubitLayout.canonical _) .empty

/-- Semantic step implemented by `activeScratchBToHistoryProgram`. -/
def activeScratchBToHistoryStep
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.step (activeScratchBToHistoryGate n counterWidth bit)

/-- The active/scratchB-to-history Toffoli atom is a concrete encoded-bit
base-gate realization over the Montgomery--Kaliski register layout. -/
theorem activeScratchBToHistory_realizes
    (n counterWidth : Nat) (bit : Fin (2 * n)) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (activeScratchBToHistoryProgram n counterWidth bit)
      (activeScratchBToHistoryStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizes (QubitLayout.canonical _) .empty
    (activeScratchBToHistoryGate n counterWidth bit)

/-- The active/scratchB-to-history atom toggles the selected history bit exactly
when both the active flag and second scratch bit are set. -/
theorem activeScratchBToHistoryStep_get_historyBit
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth bit).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      ((RegisterBits.historyBit n counterWidth bit).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          (RegisterBits.scratchBBit n counterWidth).get x)) := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.toffoliStep_get_target
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.historyBit n counterWidth bit) x

/-- The active/scratchB-to-history atom preserves the active flag. -/
theorem activeScratchBToHistoryStep_get_active
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.toffoliStep_get_of_target_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.historyBit n counterWidth bit)
        (RegisterBits.activeBit n counterWidth)
        (Ne.symm (RegisterBits.active_history_wire_ne n counterWidth bit)) x

/-- The active/scratchB-to-history atom preserves the second scratch bit. -/
theorem activeScratchBToHistoryStep_get_scratchB
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.scratchBBit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      (RegisterBits.scratchBBit n counterWidth).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.toffoliStep_get_of_target_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.historyBit n counterWidth bit)
        (RegisterBits.scratchBBit n counterWidth)
        (Ne.symm (RegisterBits.scratchB_history_wire_ne n counterWidth bit)) x

/-- The active/scratchB-to-history atom preserves the comparison bit. -/
theorem activeScratchBToHistoryStep_get_compare
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.compareBit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      (RegisterBits.compareBit n counterWidth).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.toffoliStep_get_of_target_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.historyBit n counterWidth bit)
        (RegisterBits.compareBit n counterWidth)
        (Ne.symm (RegisterBits.compare_history_wire_ne n counterWidth bit)) x

/-- The active/scratchB-to-history atom preserves any supplied condition bit
that is disjoint from the selected history target. -/
theorem activeScratchBToHistoryStep_get_condition
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hconditionHistory :
      condition.wire ≠ (RegisterBits.historyBit n counterWidth bit).wire)
    (x : Registers n counterWidth) :
    condition.get (activeScratchBToHistoryStep n counterWidth bit x) =
      condition.get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.toffoliStep_get_of_target_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.historyBit n counterWidth bit)
        condition (Ne.symm hconditionHistory) x

/-- The active/scratchB-to-history atom preserves the first scratch bit. -/
theorem activeScratchBToHistoryStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (activeScratchBToHistoryStep n counterWidth bit x) =
      (RegisterBits.scratchABit n counterWidth).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.toffoliStep_get_of_target_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.historyBit n counterWidth bit)
        (RegisterBits.scratchABit n counterWidth)
        (Ne.symm (RegisterBits.scratchA_history_wire_ne n counterWidth bit)) x

/-- The active/scratchB-to-history atom preserves any observed bit disjoint
from the selected history target. -/
theorem activeScratchBToHistoryStep_get_of_history_ne
    (n counterWidth : Nat) (historyIndex : Fin (2 * n))
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hhistory :
      (RegisterBits.historyBit n counterWidth historyIndex).wire ≠
        observed.wire)
    (x : Registers n counterWidth) :
    observed.get (activeScratchBToHistoryStep n counterWidth historyIndex x) =
      observed.get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.toffoliStep_get_of_target_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.historyBit n counterWidth historyIndex)
        observed hhistory x

/-- The active/scratchB-to-history atom preserves every history slot except
the selected target slot. -/
theorem activeScratchBToHistoryStep_get_historyBit_of_ne
    (n counterWidth : Nat) (target observed : Fin (2 * n))
    (hne : target ≠ observed) (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth observed).get
        (activeScratchBToHistoryStep n counterWidth target x) =
      (RegisterBits.historyBit n counterWidth observed).get x :=
  activeScratchBToHistoryStep_get_of_history_ne
    n counterWidth target (RegisterBits.historyBit n counterWidth observed)
    (RegisterBits.history_history_wire_ne n counterWidth hne) x

/-- The active/scratchB-to-history atom preserves every `u` bit. -/
theorem activeScratchBToHistoryStep_get_uBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.uBit n counterWidth bit).get
        (activeScratchBToHistoryStep n counterWidth historyIndex x) =
      (RegisterBits.uBit n counterWidth bit).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.toffoliStep_get_of_target_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.historyBit n counterWidth historyIndex)
        (RegisterBits.uBit n counterWidth bit)
        (Ne.symm (RegisterBits.u_history_wire_ne n counterWidth bit
          historyIndex)) x

/-- The active/scratchB-to-history atom preserves every `v` bit. -/
theorem activeScratchBToHistoryStep_get_vBit
    (n counterWidth : Nat) (historyIndex : Fin (2 * n)) (bit : Fin n)
    (x : Registers n counterWidth) :
    (RegisterBits.vBit n counterWidth bit).get
        (activeScratchBToHistoryStep n counterWidth historyIndex x) =
      (RegisterBits.vBit n counterWidth bit).get x := by
  simpa [activeScratchBToHistoryStep, activeScratchBToHistoryGate,
    EncodedBit.GateSpec.step] using
      EncodedBit.toffoliStep_get_of_target_ne
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.historyBit n counterWidth historyIndex)
        (RegisterBits.vBit n counterWidth bit)
        (Ne.symm (RegisterBits.v_history_wire_ne n counterWidth bit
          historyIndex)) x

end
end MK
end MAU.Inversion
end QuantumAlg


namespace QuantumAlg
namespace NumberTheory.BinaryGCD
namespace Branch

open QuantumAlg.MAU.Inversion.MK
open QuantumAlg.Nat.FixedWidth

/-- Branch selected from concrete register signals: low `u`, low `v`, and the
staged comparison bit. -/
def fromRegisterSignals
    (n counterWidth : Nat) (x : Registers n counterWidth) : Branch :=
  fromCircuitSignals (x.u.val.testBit (0 : Nat))
    (x.v.val.testBit (0 : Nat)) x.compare

/-- Branch selected from the concrete register signals inside the
coefficient-adder work object. -/
def fromCoeffWorkSignals
    (n counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork n counterWidth) : Branch :=
  fromCircuitSignals (x.1.1.u.val.testBit (0 : Nat))
    (x.1.1.v.val.testBit (0 : Nat)) x.1.1.compare

/-- The coefficient-work selector signals are exactly the lifted low `u`, low
`v`, and comparison readout bits used by the branch selector. -/
theorem fromCoeffWorkSignals_eq_from_branch_bits
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    fromCoeffWorkSignals tail.succ counterWidth x =
      fromCircuitSignals
        ((coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x)
        ((coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x)
        ((coeffAdderCompareBit tail.succ counterWidth).get x) := by
  simp [fromCoeffWorkSignals, coeffAdderUBit_get_littleEndian_zero,
    coeffAdderVBit_get_littleEndian_zero, coeffAdderCompareBit_get]

/-- The selected branch's auxiliary code bit, expressed directly in terms of
the coefficient-work readouts used by the circuit-facing selector. -/
theorem fromCoeffWorkSignals_auxBit_eq_branch_bits
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
      (!(coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x ||
        ((coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderCompareBit tail.succ counterWidth).get x)) := by
  rw [fromCoeffWorkSignals_eq_from_branch_bits]
  exact fromCircuitSignals_auxBit _ _ _

/-- The selected branch's history code bit, expressed directly in terms of the
coefficient-work readouts used by the circuit-facing selector. -/
theorem fromCoeffWorkSignals_historyBit_eq_branch_bits
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (fromCoeffWorkSignals tail.succ counterWidth x).historyBit =
      ((coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
        (!(coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x ||
          (coeffAdderCompareBit tail.succ counterWidth).get x)) := by
  rw [fromCoeffWorkSignals_eq_from_branch_bits]
  exact fromCircuitSignals_historyBit _ _ _

/-- The selected two-bit branch code, expressed directly in terms of the
coefficient-work readouts used by the circuit-facing selector. -/
theorem fromCoeffWorkSignals_code_eq_branch_bits
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    code (fromCoeffWorkSignals tail.succ counterWidth x) =
      (!(coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x ||
        ((coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderCompareBit tail.succ counterWidth).get x),
       (coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
        (!(coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x ||
          (coeffAdderCompareBit tail.succ counterWidth).get x)) := by
  rw [code, fromCoeffWorkSignals_auxBit_eq_branch_bits,
    fromCoeffWorkSignals_historyBit_eq_branch_bits]

/-- The selected branch's auxiliary code bit, expressed as disjoint selector
terms over the coefficient-work readouts used by the circuit-facing selector.
-/
theorem fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (fromCoeffWorkSignals tail.succ counterWidth x).auxBit =
      (!(coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x ||
        ((coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderCompareBit tail.succ counterWidth).get x)) := by
  rw [fromCoeffWorkSignals_eq_from_branch_bits]
  exact fromCircuitSignals_auxBit_disjoint _ _ _

/-- The selected branch's history code bit, expressed as disjoint selector
terms over the coefficient-work readouts used by the circuit-facing selector.
-/
theorem fromCoeffWorkSignals_historyBit_eq_branch_bits_disjoint
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    (fromCoeffWorkSignals tail.succ counterWidth x).historyBit =
      (((coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
        !(coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x) ||
        ((coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderCompareBit tail.succ counterWidth).get x)) := by
  rw [fromCoeffWorkSignals_eq_from_branch_bits]
  exact fromCircuitSignals_historyBit_disjoint _ _ _

/-- The selected two-bit branch code, expressed as disjoint selector terms over
the coefficient-work readouts used by the circuit-facing selector. -/
theorem fromCoeffWorkSignals_code_eq_branch_bits_disjoint
    (tail counterWidth : Nat)
    (x : RegistersWithCoeffAdderWork tail.succ counterWidth) :
    code (fromCoeffWorkSignals tail.succ counterWidth x) =
      (!(coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x ||
        ((coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderCompareBit tail.succ counterWidth).get x),
       ((coeffAdderUBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
        !(coeffAdderVBit tail.succ counterWidth
          (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x) ||
        ((coeffAdderUBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderVBit tail.succ counterWidth
            (WireAddress.littleEndianWire (0 : Fin tail.succ))).get x &&
          (coeffAdderCompareBit tail.succ counterWidth).get x)) := by
  rw [code, fromCoeffWorkSignals_auxBit_eq_branch_bits_disjoint,
    fromCoeffWorkSignals_historyBit_eq_branch_bits_disjoint]

end Branch
end NumberTheory.BinaryGCD
end QuantumAlg

namespace QuantumAlg
namespace MAU.Inversion
namespace MK

noncomputable section

open Nat.FixedWidth
open Nat.BinaryArithmetic
open NumberTheory.BinaryGCD

/-! ## Active-guarded branch-code staging -/

/-- CNOT gate list that xors a fixed RNSL17 branch code into the scratch
encoder bits, guarded by the Kaliski active flag.  It is branch-specific
staging for the source branch codes `10, 01, 11, 00`; a full compute circuit
still has to route the appropriate branch condition into this staging point
[RNSL17, ECDLP.tex:468-475]. -/
def activeBranchCodeToScratchGates
    (n counterWidth : Nat) (branch : Branch) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  (if branch.auxBit then
      [EncodedBit.GateSpec.cnot
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchABit n counterWidth)
        (RegisterBits.active_scratchA_wire_ne n counterWidth)]
    else []) ++
  (if branch.historyBit then
      [EncodedBit.GateSpec.cnot
        (RegisterBits.activeBit n counterWidth)
        (RegisterBits.scratchBBit n counterWidth)
        (RegisterBits.active_scratchB_wire_ne n counterWidth)]
    else [])

/-- Base-gate program for active-guarded branch-code staging. -/
def activeBranchCodeToScratchProgram
    (n counterWidth : Nat) (branch : Branch) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeBranchCodeToScratchGates n counterWidth branch)

/-- Semantic step implemented by active-guarded branch-code staging. -/
def activeBranchCodeToScratchStep
    (n counterWidth : Nat) (branch : Branch) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (activeBranchCodeToScratchGates n counterWidth branch)

/-- The active-guarded branch-code staging program is a concrete encoded-bit
base-gate realization over the Montgomery--Kaliski register layout. -/
theorem activeBranchCodeToScratch_realizes
    (n counterWidth : Nat) (branch : Branch) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (activeBranchCodeToScratchProgram n counterWidth branch)
      (activeBranchCodeToScratchStep n counterWidth branch) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (activeBranchCodeToScratchGates n counterWidth branch)

/-- Active-guarded branch-code staging toggles scratchA exactly when the active
flag and the source auxiliary branch-code bit are set
[RNSL17, ECDLP.tex:471]. -/
theorem activeBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat) (branch : Branch)
    (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (activeBranchCodeToScratchStep n counterWidth branch x) =
      ((RegisterBits.scratchABit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x && branch.auxBit)) := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.cnotStep_get_target active scratchA x
  | vEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, scratchB] using
        EncodedBit.cnotStep_get_of_target_ne active scratchB scratchA
          (Ne.symm (RegisterBits.scratchA_scratchB_wire_ne n counterWidth)) x
  | uGreater =>
      change scratchA.get (EncodedBit.cnotStep active scratchB
          (EncodedBit.cnotStep active scratchA x)) =
        (scratchA.get x ^^ (active.get x && true))
      rw [EncodedBit.cnotStep_get_of_target_ne active scratchB scratchA
        (Ne.symm (RegisterBits.scratchA_scratchB_wire_ne n counterWidth))]
      rw [EncodedBit.cnotStep_get_target]
      simp
  | vLe =>
      simp [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-guarded branch-code staging toggles scratchB exactly when the active
flag and the source history branch-code bit are set
[RNSL17, ECDLP.tex:471]. -/
theorem activeBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat) (branch : Branch)
    (x : Registers n counterWidth) :
    (RegisterBits.scratchBBit n counterWidth).get
        (activeBranchCodeToScratchStep n counterWidth branch x) =
      ((RegisterBits.scratchBBit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x && branch.historyBit)) := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, scratchB] using
        EncodedBit.cnotStep_get_of_target_ne active scratchA scratchB
          (RegisterBits.scratchA_scratchB_wire_ne n counterWidth) x
  | vEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.cnotStep_get_target active scratchB x
  | uGreater =>
      change scratchB.get (EncodedBit.cnotStep active scratchB
          (EncodedBit.cnotStep active scratchA x)) =
        (scratchB.get x ^^ (active.get x && true))
      rw [EncodedBit.cnotStep_get_target]
      rw [EncodedBit.cnotStep_get_of_target_ne active scratchA scratchB
        (RegisterBits.scratchA_scratchB_wire_ne n counterWidth)]
      rw [EncodedBit.cnotStep_get_of_target_ne active scratchA active
        (Ne.symm (RegisterBits.active_scratchA_wire_ne n counterWidth))]
      simp
  | vLe =>
      simp [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-guarded branch-code staging preserves the active flag. -/
theorem activeBranchCodeToScratchStep_get_active
    (n counterWidth : Nat) (branch : Branch)
    (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (activeBranchCodeToScratchStep n counterWidth branch x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.cnotStep_get_of_target_ne active scratchA active
          (Ne.symm (RegisterBits.active_scratchA_wire_ne n counterWidth)) x
  | vEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.cnotStep_get_of_target_ne active scratchB active
          (Ne.symm (RegisterBits.active_scratchB_wire_ne n counterWidth)) x
  | uGreater =>
      change active.get (EncodedBit.cnotStep active scratchB
          (EncodedBit.cnotStep active scratchA x)) = active.get x
      rw [EncodedBit.cnotStep_get_of_target_ne active scratchB active
        (Ne.symm (RegisterBits.active_scratchB_wire_ne n counterWidth))]
      rw [EncodedBit.cnotStep_get_of_target_ne active scratchA active
        (Ne.symm (RegisterBits.active_scratchA_wire_ne n counterWidth))]
  | vLe =>
      simp [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-guarded branch-code staging preserves each stored history bit. -/
theorem activeBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat) (branch : Branch) (historyIndex : Fin (2 * n))
    (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (activeBranchCodeToScratchStep n counterWidth branch x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  let history := RegisterBits.historyBit n counterWidth historyIndex
  cases branch with
  | uEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, history] using
        EncodedBit.cnotStep_get_of_target_ne active scratchA history
          (RegisterBits.scratchA_history_wire_ne n counterWidth historyIndex) x
  | vEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB, history] using
        EncodedBit.cnotStep_get_of_target_ne active scratchB history
          (RegisterBits.scratchB_history_wire_ne n counterWidth historyIndex) x
  | uGreater =>
      change history.get
          (EncodedBit.cnotStep active scratchB
            (EncodedBit.cnotStep active scratchA x)) =
        history.get x
      rw [EncodedBit.cnotStep_get_of_target_ne active scratchB history
        (RegisterBits.scratchB_history_wire_ne n counterWidth historyIndex)]
      rw [EncodedBit.cnotStep_get_of_target_ne active scratchA history
        (RegisterBits.scratchA_history_wire_ne n counterWidth historyIndex)]
  | vLe =>
      simp [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-guarded branch-code staging preserves any observed bit disjoint from
the two scratch-code targets. -/
theorem activeBranchCodeToScratchStep_get_of_scratch_ne
    (n counterWidth : Nat) (branch : Branch)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hscratchA :
      (RegisterBits.scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB :
      (RegisterBits.scratchBBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (activeBranchCodeToScratchStep n counterWidth branch x) =
      observed.get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.cnotStep_get_of_target_ne active scratchA observed hscratchA x
  | vEven =>
      simpa [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.cnotStep_get_of_target_ne active scratchB observed hscratchB x
  | uGreater =>
      change observed.get
          (EncodedBit.cnotStep active scratchB
            (EncodedBit.cnotStep active scratchA x)) =
        observed.get x
      rw [EncodedBit.cnotStep_get_of_target_ne active scratchB observed hscratchB]
      rw [EncodedBit.cnotStep_get_of_target_ne active scratchA observed hscratchA]
  | vLe =>
      simp [activeBranchCodeToScratchStep, activeBranchCodeToScratchGates,
        Branch.auxBit, Branch.historyBit, EncodedBit.GateSpec.stepList]

/-! ## Active-and-condition-guarded branch-code staging -/

/-- Toffoli gate list that xors a fixed RNSL17 branch code into the scratch
encoder bits, guarded by the active flag and a supplied branch-condition bit.
This is the plug-in point for later parity/comparison selector circuits; it
still does not implement those selectors by itself [RNSL17,
ECDLP.tex:468-475]. -/
def activeConditionBranchCodeToScratchGates
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) :
    List (EncodedBit.GateSpec (registerEncoding n counterWidth)) :=
  (if branch.auxBit then
      [EncodedBit.GateSpec.toffoli
        (RegisterBits.activeBit n counterWidth)
        condition
        (RegisterBits.scratchABit n counterWidth)
        hactiveCondition
        (RegisterBits.active_scratchA_wire_ne n counterWidth)
        hconditionScratchA]
    else []) ++
  (if branch.historyBit then
      [EncodedBit.GateSpec.toffoli
        (RegisterBits.activeBit n counterWidth)
        condition
        (RegisterBits.scratchBBit n counterWidth)
        hactiveCondition
        (RegisterBits.active_scratchB_wire_ne n counterWidth)
        hconditionScratchB]
    else [])

/-- Base-gate program for active-and-condition-guarded branch-code staging. -/
def activeConditionBranchCodeToScratchProgram
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (registerEncoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeConditionBranchCodeToScratchGates n counterWidth condition
      hactiveCondition hconditionScratchA hconditionScratchB branch)

/-- Semantic step implemented by active-and-condition-guarded branch-code
staging. -/
def activeConditionBranchCodeToScratchStep
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (activeConditionBranchCodeToScratchGates n counterWidth condition
      hactiveCondition hconditionScratchA hconditionScratchB branch)

/-- The active-and-condition-guarded branch-code staging program is a concrete
encoded-bit base-gate realization over the Montgomery--Kaliski register
layout. -/
theorem activeConditionBranchCodeToScratch_realizes
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) :
    UnitaryCircuit.Realizes (registerEncoding n counterWidth)
      (activeConditionBranchCodeToScratchProgram n counterWidth condition
        hactiveCondition hconditionScratchA hconditionScratchB branch)
      (activeConditionBranchCodeToScratchStep n counterWidth condition
        hactiveCondition hconditionScratchA hconditionScratchB branch) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (activeConditionBranchCodeToScratchGates n counterWidth condition
      hactiveCondition hconditionScratchA hconditionScratchB branch)

/-- Active-and-condition-guarded branch-code staging toggles scratchA exactly
when the active flag, supplied condition, and source auxiliary code bit are set
[RNSL17, ECDLP.tex:471].
-/
theorem activeConditionBranchCodeToScratchStep_get_scratchA
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (activeConditionBranchCodeToScratchStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch x) =
      ((RegisterBits.scratchABit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          condition.get x && branch.auxBit)) := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.toffoliStep_get_target active condition scratchA x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          scratchA (Ne.symm (RegisterBits.scratchA_scratchB_wire_ne
            n counterWidth)) x
  | uGreater =>
      change scratchA.get
          (EncodedBit.toffoliStep active condition scratchB
            (EncodedBit.toffoliStep active condition scratchA x)) =
        (scratchA.get x ^^ (active.get x && condition.get x && true))
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        scratchA (Ne.symm (RegisterBits.scratchA_scratchB_wire_ne
          n counterWidth))]
      rw [EncodedBit.toffoliStep_get_target]
      simp
  | vLe =>
      simp [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-and-condition-guarded branch-code staging toggles scratchB exactly
when the active flag, supplied condition, and source history code bit are set
[RNSL17, ECDLP.tex:471].
-/
theorem activeConditionBranchCodeToScratchStep_get_scratchB
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (x : Registers n counterWidth) :
    (RegisterBits.scratchBBit n counterWidth).get
        (activeConditionBranchCodeToScratchStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch x) =
      ((RegisterBits.scratchBBit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          condition.get x && branch.historyBit)) := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          scratchB (RegisterBits.scratchA_scratchB_wire_ne n counterWidth) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.toffoliStep_get_target active condition scratchB x
  | uGreater =>
      change scratchB.get
          (EncodedBit.toffoliStep active condition scratchB
            (EncodedBit.toffoliStep active condition scratchA x)) =
        (scratchB.get x ^^ (active.get x && condition.get x && true))
      rw [EncodedBit.toffoliStep_get_target]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        scratchB (RegisterBits.scratchA_scratchB_wire_ne n counterWidth)]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        active (Ne.symm (RegisterBits.active_scratchA_wire_ne n counterWidth))]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        condition (Ne.symm hconditionScratchA)]
      simp
  | vLe =>
      simp [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-and-condition-guarded branch-code staging preserves the active flag.
-/
theorem activeConditionBranchCodeToScratchStep_get_active
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (activeConditionBranchCodeToScratchStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          active (Ne.symm (RegisterBits.active_scratchA_wire_ne
            n counterWidth)) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          active (Ne.symm (RegisterBits.active_scratchB_wire_ne
            n counterWidth)) x
  | uGreater =>
      change active.get
          (EncodedBit.toffoliStep active condition scratchB
            (EncodedBit.toffoliStep active condition scratchA x)) =
        active.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        active (Ne.symm (RegisterBits.active_scratchB_wire_ne n counterWidth))]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        active (Ne.symm (RegisterBits.active_scratchA_wire_ne n counterWidth))]
  | vLe =>
      simp [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-and-condition-guarded branch-code staging preserves the supplied
condition bit. -/
theorem activeConditionBranchCodeToScratchStep_get_condition
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (x : Registers n counterWidth) :
    condition.get
        (activeConditionBranchCodeToScratchStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch x) =
      condition.get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          condition (Ne.symm hconditionScratchA) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          condition (Ne.symm hconditionScratchB) x
  | uGreater =>
      change condition.get
          (EncodedBit.toffoliStep active condition scratchB
            (EncodedBit.toffoliStep active condition scratchA x)) =
        condition.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        condition (Ne.symm hconditionScratchB)]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        condition (Ne.symm hconditionScratchA)]
  | vLe =>
      simp [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-and-condition-guarded branch-code staging preserves every `u` bit. -/
theorem activeConditionBranchCodeToScratchStep_get_uBit
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (bit : Fin n) (x : Registers n counterWidth) :
    (RegisterBits.uBit n counterWidth bit).get
        (activeConditionBranchCodeToScratchStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch x) =
      (RegisterBits.uBit n counterWidth bit).get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  let source := RegisterBits.uBit n counterWidth bit
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, source] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          source (Ne.symm (RegisterBits.u_scratchA_wire_ne
            n counterWidth bit)) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB, source] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          source (Ne.symm (RegisterBits.u_scratchB_wire_ne
            n counterWidth bit)) x
  | uGreater =>
      change source.get
          (EncodedBit.toffoliStep active condition scratchB
            (EncodedBit.toffoliStep active condition scratchA x)) =
        source.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        source (Ne.symm (RegisterBits.u_scratchB_wire_ne n counterWidth bit))]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        source (Ne.symm (RegisterBits.u_scratchA_wire_ne n counterWidth bit))]
  | vLe =>
      simp [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-and-condition-guarded branch-code staging preserves every `v` bit. -/
theorem activeConditionBranchCodeToScratchStep_get_vBit
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (bit : Fin n) (x : Registers n counterWidth) :
    (RegisterBits.vBit n counterWidth bit).get
        (activeConditionBranchCodeToScratchStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch x) =
      (RegisterBits.vBit n counterWidth bit).get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  let source := RegisterBits.vBit n counterWidth bit
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, source] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          source (Ne.symm (RegisterBits.v_scratchA_wire_ne
            n counterWidth bit)) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB, source] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          source (Ne.symm (RegisterBits.v_scratchB_wire_ne
            n counterWidth bit)) x
  | uGreater =>
      change source.get
          (EncodedBit.toffoliStep active condition scratchB
            (EncodedBit.toffoliStep active condition scratchA x)) =
        source.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        source (Ne.symm (RegisterBits.v_scratchB_wire_ne n counterWidth bit))]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        source (Ne.symm (RegisterBits.v_scratchA_wire_ne n counterWidth bit))]
  | vLe =>
      simp [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-and-condition-guarded branch-code staging preserves every stored
branch-history bit. -/
theorem activeConditionBranchCodeToScratchStep_get_historyBit
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (bit : Fin (2 * n)) (x : Registers n counterWidth) :
    (RegisterBits.historyBit n counterWidth bit).get
        (activeConditionBranchCodeToScratchStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch x) =
      (RegisterBits.historyBit n counterWidth bit).get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  let history := RegisterBits.historyBit n counterWidth bit
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, history] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          history (RegisterBits.scratchA_history_wire_ne n counterWidth bit) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB, history] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          history (RegisterBits.scratchB_history_wire_ne n counterWidth bit) x
  | uGreater =>
      change history.get
          (EncodedBit.toffoliStep active condition scratchB
            (EncodedBit.toffoliStep active condition scratchA x)) =
        history.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        history (RegisterBits.scratchB_history_wire_ne n counterWidth bit)]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        history (RegisterBits.scratchA_history_wire_ne n counterWidth bit)]
  | vLe =>
      simp [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Active-and-condition-guarded branch-code staging preserves any observed bit
disjoint from the two scratch-code targets. -/
theorem activeConditionBranchCodeToScratchStep_get_of_scratch_ne
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hscratchA :
      (RegisterBits.scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB :
      (RegisterBits.scratchBBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (activeConditionBranchCodeToScratchStep n counterWidth condition
          hactiveCondition hconditionScratchA hconditionScratchB branch x) =
      observed.get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          observed hscratchA x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          observed hscratchB x
  | uGreater =>
      change observed.get
          (EncodedBit.toffoliStep active condition scratchB
            (EncodedBit.toffoliStep active condition scratchA x)) =
        observed.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        observed hscratchB]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        observed hscratchA]
  | vLe =>
      simp [activeConditionBranchCodeToScratchStep,
        activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

theorem activeConditionBranchCodeToScratchReverseStep_get_historyBit
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
    (RegisterBits.historyBit n counterWidth historyIndex).get
        (EncodedBit.GateSpec.stepList
          (activeConditionBranchCodeToScratchGates n counterWidth condition
            hactiveCondition hconditionScratchA hconditionScratchB
            branch).reverse x) =
      (RegisterBits.historyBit n counterWidth historyIndex).get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  let history := RegisterBits.historyBit n counterWidth historyIndex
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          history (RegisterBits.scratchA_history_wire_ne n counterWidth
            historyIndex) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          history (RegisterBits.scratchB_history_wire_ne n counterWidth
            historyIndex) x
  | uGreater =>
      change history.get
          (EncodedBit.toffoliStep active condition scratchA
            (EncodedBit.toffoliStep active condition scratchB x)) =
        history.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        history (RegisterBits.scratchA_history_wire_ne n counterWidth
          historyIndex)]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        history (RegisterBits.scratchB_history_wire_ne n counterWidth
          historyIndex)]
  | vLe =>
      simp [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Reversing active-and-condition-guarded branch-code staging toggles scratchA
by the same source auxiliary code bit used by the forward staging slice
[RNSL17, ECDLP.tex:471]. -/
theorem activeConditionBranchCodeToScratchReverseStep_get_scratchA
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (x : Registers n counterWidth) :
    (RegisterBits.scratchABit n counterWidth).get
        (EncodedBit.GateSpec.stepList
          (activeConditionBranchCodeToScratchGates n counterWidth condition
            hactiveCondition hconditionScratchA hconditionScratchB
            branch).reverse x) =
      ((RegisterBits.scratchABit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          condition.get x && branch.auxBit)) := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.toffoliStep_get_target active condition scratchA x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          scratchA (Ne.symm (RegisterBits.scratchA_scratchB_wire_ne
            n counterWidth)) x
  | uGreater =>
      change scratchA.get
          (EncodedBit.toffoliStep active condition scratchA
            (EncodedBit.toffoliStep active condition scratchB x)) =
        (scratchA.get x ^^ (active.get x && condition.get x && true))
      rw [EncodedBit.toffoliStep_get_target]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        scratchA (Ne.symm (RegisterBits.scratchA_scratchB_wire_ne
          n counterWidth))]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        active (Ne.symm (RegisterBits.active_scratchB_wire_ne n counterWidth))]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        condition (Ne.symm hconditionScratchB)]
      simp
  | vLe =>
      simp [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Reversing active-and-condition-guarded branch-code staging toggles scratchB
by the same source history code bit used by the forward staging slice
[RNSL17, ECDLP.tex:471]. -/
theorem activeConditionBranchCodeToScratchReverseStep_get_scratchB
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (x : Registers n counterWidth) :
    (RegisterBits.scratchBBit n counterWidth).get
        (EncodedBit.GateSpec.stepList
          (activeConditionBranchCodeToScratchGates n counterWidth condition
            hactiveCondition hconditionScratchA hconditionScratchB
            branch).reverse x) =
      ((RegisterBits.scratchBBit n counterWidth).get x ^^
        ((RegisterBits.activeBit n counterWidth).get x &&
          condition.get x && branch.historyBit)) := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          scratchB (RegisterBits.scratchA_scratchB_wire_ne n counterWidth) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.toffoliStep_get_target active condition scratchB x
  | uGreater =>
      change scratchB.get
          (EncodedBit.toffoliStep active condition scratchA
            (EncodedBit.toffoliStep active condition scratchB x)) =
        (scratchB.get x ^^ (active.get x && condition.get x && true))
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        scratchB (RegisterBits.scratchA_scratchB_wire_ne n counterWidth)]
      rw [EncodedBit.toffoliStep_get_target]
      simp
  | vLe =>
      simp [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Reversing active-and-condition-guarded branch-code staging preserves the
active flag. -/
theorem activeConditionBranchCodeToScratchReverseStep_get_active
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (x : Registers n counterWidth) :
    (RegisterBits.activeBit n counterWidth).get
        (EncodedBit.GateSpec.stepList
          (activeConditionBranchCodeToScratchGates n counterWidth condition
            hactiveCondition hconditionScratchA hconditionScratchB
            branch).reverse x) =
      (RegisterBits.activeBit n counterWidth).get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          active (Ne.symm (RegisterBits.active_scratchA_wire_ne
            n counterWidth)) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          active (Ne.symm (RegisterBits.active_scratchB_wire_ne
            n counterWidth)) x
  | uGreater =>
      change active.get
          (EncodedBit.toffoliStep active condition scratchA
            (EncodedBit.toffoliStep active condition scratchB x)) =
        active.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        active (Ne.symm (RegisterBits.active_scratchA_wire_ne n counterWidth))]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        active (Ne.symm (RegisterBits.active_scratchB_wire_ne n counterWidth))]
  | vLe =>
      simp [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Reversing active-and-condition-guarded branch-code staging preserves the
supplied branch-condition bit. -/
theorem activeConditionBranchCodeToScratchReverseStep_get_condition
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch) (x : Registers n counterWidth) :
    condition.get
        (EncodedBit.GateSpec.stepList
          (activeConditionBranchCodeToScratchGates n counterWidth condition
            hactiveCondition hconditionScratchA hconditionScratchB
            branch).reverse x) =
      condition.get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          condition (Ne.symm hconditionScratchA) x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          condition (Ne.symm hconditionScratchB) x
  | uGreater =>
      change condition.get
          (EncodedBit.toffoliStep active condition scratchA
            (EncodedBit.toffoliStep active condition scratchB x)) =
        condition.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        condition (Ne.symm hconditionScratchA)]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        condition (Ne.symm hconditionScratchB)]
  | vLe =>
      simp [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-- Reversing active-and-condition-guarded branch-code staging preserves any
observed bit disjoint from the two scratch-code targets. -/
theorem activeConditionBranchCodeToScratchReverseStep_get_of_scratch_ne
    (n counterWidth : Nat)
    (condition : EncodedBit (registerEncoding n counterWidth))
    (hactiveCondition :
      (RegisterBits.activeBit n counterWidth).wire ≠ condition.wire)
    (hconditionScratchA :
      condition.wire ≠ (RegisterBits.scratchABit n counterWidth).wire)
    (hconditionScratchB :
      condition.wire ≠ (RegisterBits.scratchBBit n counterWidth).wire)
    (branch : Branch)
    (observed : EncodedBit (registerEncoding n counterWidth))
    (hscratchA :
      (RegisterBits.scratchABit n counterWidth).wire ≠ observed.wire)
    (hscratchB :
      (RegisterBits.scratchBBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (EncodedBit.GateSpec.stepList
          (activeConditionBranchCodeToScratchGates n counterWidth condition
            hactiveCondition hconditionScratchA hconditionScratchB
            branch).reverse x) =
      observed.get x := by
  let active := RegisterBits.activeBit n counterWidth
  let scratchA := RegisterBits.scratchABit n counterWidth
  let scratchB := RegisterBits.scratchBBit n counterWidth
  cases branch with
  | uEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchA] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
          observed hscratchA x
  | vEven =>
      simpa [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList,
        EncodedBit.GateSpec.step, active, scratchB] using
        EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
          observed hscratchB x
  | uGreater =>
      change observed.get
          (EncodedBit.toffoliStep active condition scratchA
            (EncodedBit.toffoliStep active condition scratchB x)) =
        observed.get x
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchA
        observed hscratchA]
      rw [EncodedBit.toffoliStep_get_of_target_ne active condition scratchB
        observed hscratchB]
  | vLe =>
      simp [activeConditionBranchCodeToScratchGates, Branch.auxBit,
        Branch.historyBit, EncodedBit.GateSpec.stepList]

/-! ## Compact-carrier comparison -/

namespace Compact

/-- The `v-u` comparison borrows the existing VBE carry bank instead of
allocating a separate comparison word. -/
def uGreaterBorrowLayout (n counterWidth : Nat) :
    QuantumAlg.Comparator.BorrowWorkLayout
      (encoding := encoding n counterWidth) n where
  minuend := vValueWord n counterWidth
  subtrahend := uValueWord n counterWidth
  initialBorrow := scratchABit n counterWidth
  workBorrow := coefficientCarryWorkWord n counterWidth
  minuendMinuend_ne := by
    intro i j hij
    exact liftCoreBit_wire_ne n counterWidth
      (v_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j)
        (littleEndianWire_ne hij))
  subtrahendSubtrahend_ne := by
    intro i j hij
    exact liftCoreBit_wire_ne n counterWidth
      (u_u_wire_ne n counterWidth
        (WireAddress.littleEndianWire i)
        (WireAddress.littleEndianWire j)
        (littleEndianWire_ne hij))
  minuendSubtrahend_ne := by
    intro i j
    exact liftCoreBit_wire_ne n counterWidth
      (Ne.symm (RegisterBits.u_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire j)
        (WireAddress.littleEndianWire i)))
  minuendInitialBorrow_ne := by
    intro i
    exact liftCoreBit_wire_ne n counterWidth
      (RegisterBits.v_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire i))
  subtrahendInitialBorrow_ne := by
    intro i
    exact liftCoreBit_wire_ne n counterWidth
      (RegisterBits.u_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire i))
  minuendWork_ne := by
    intro i j
    exact liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.vValueBit n counterWidth i) j
  subtrahendWork_ne := by
    intro i j
    exact liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.uValueBit n counterWidth i) j
  initialBorrowWork_ne := by
    intro j
    exact liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.scratchABit n counterWidth) j
  workWork_ne := by
    intro i j hij
    exact coefficientCarryWorkBit_wire_ne n counterWidth hij

/-- Forward subtract-borrow gates on the compact carrier. -/
def uGreaterBorrowGates (n counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  QuantumAlg.Comparator.BorrowWorkLayout.borrowStage
    (uGreaterBorrowLayout n counterWidth)

/-- Semantic action of the forward compact subtract-borrow pass. -/
def uGreaterBorrowStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList (uGreaterBorrowGates n counterWidth)

/-- Semantic action of the reverse compact subtract-borrow pass. -/
def uGreaterBorrowReverseStep (n counterWidth : Nat) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uGreaterBorrowGates n counterWidth).reverse

/-- The concrete forward gate-list action agrees with the generic ordered
borrow recurrence. -/
theorem uGreaterBorrowStep_eq_indexStep
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    uGreaterBorrowStep n counterWidth x =
      QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep
        (uGreaterBorrowLayout n counterWidth) x := by
  exact QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_stepList_eq_indexStep
    (uGreaterBorrowLayout n counterWidth) x

/-- The compact forward borrow pass preserves the core comparison bit. -/
theorem uGreaterBorrowStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (uGreaterBorrowStep n counterWidth x) =
      (compareBit n counterWidth).get x := by
  rw [uGreaterBorrowStep_eq_indexStep]
  exact
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_of_minuend_work_ne
      (uGreaterBorrowLayout n counterWidth) (compareBit n counterWidth)
      (fun j => liftCoreBit_wire_ne n counterWidth
        (RegisterBits.v_compare_wire_ne n counterWidth
          (WireAddress.littleEndianWire j)))
      (fun j => Ne.symm
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth) j)) x

/-- The compact borrow pass preserves any observation outside its `v` targets
and the borrowed VBE carry word. -/
theorem uGreaterBorrowStep_get_of_minuend_work_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hminuend : ∀ j : Fin n,
      ((vValueWord n counterWidth).bit j).wire ≠ observed.wire)
    (hwork : ∀ j : Fin n,
      (coefficientCarryWorkBit n counterWidth j).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (uGreaterBorrowStep n counterWidth x) = observed.get x := by
  rw [uGreaterBorrowStep_eq_indexStep]
  simpa [uGreaterBorrowLayout, vValueWord, coefficientCarryWorkWord] using
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_of_minuend_work_ne
      (uGreaterBorrowLayout n counterWidth) observed
      (by
        intro j
        simpa [uGreaterBorrowLayout, vValueWord] using hminuend j)
      (by
        intro j
        simpa [uGreaterBorrowLayout, coefficientCarryWorkWord] using hwork j)
      x

/-- On clean shared work, the final borrowed VBE carry bit is exactly the
`v<u` predicate needed by the odd-odd branch. -/
theorem uGreaterBorrowStep_get_final_work_clean
    (n counterWidth : Nat) (bit : Fin n)
    (core : MK.Registers n counterWidth) (target : Word n)
    (hscratchA : core.scratchA = false)
    (hfinal : bit.val + 1 = n) :
    (coefficientCarryWorkBit n counterWidth bit).get
        (uGreaterBorrowStep n counterWidth
          { core := core
            shared := cleanSharedWork n counterWidth
            target := target }) =
      decide (core.v.val < core.u.val) := by
  rw [uGreaterBorrowStep_eq_indexStep]
  have hborrow :=
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_workBorrow_natBorrow
      (uGreaterBorrowLayout n counterWidth)
      core.v.val core.u.val bit
      { core := core
        shared := cleanSharedWork n counterWidth
        target := target }
      (by
        intro k
        exact coefficientCarryWorkBit_get_clean n counterWidth k core target)
      (by simp [uGreaterBorrowLayout, hscratchA])
      (by intro k; simp [uGreaterBorrowLayout])
      (by intro k; simp [uGreaterBorrowLayout])
  rw [show
    (coefficientCarryWorkBit n counterWidth bit).get
        (QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep
          (uGreaterBorrowLayout n counterWidth)
          { core := core
            shared := cleanSharedWork n counterWidth
            target := target }) =
      QuantumAlg.Comparator.natBorrow core.v.val core.u.val (bit.val + 1) by
    simpa [uGreaterBorrowLayout, coefficientCarryWorkWord] using hborrow]
  have hv : core.v.val < 2 ^ (bit.val + 1) := by
    simp [hfinal]
  have hu : core.u.val < 2 ^ (bit.val + 1) := by
    simp [hfinal]
  simpa using
    QuantumAlg.Comparator.natBorrow_eq_decide_lt_of_lt_two_pow
      (a := core.v.val) (b := core.u.val) (n := bit.val + 1) hv hu

/-- General clean-bank form of the final compact borrow theorem.  Other
reusable fields may already hold routing data; only the borrowed VBE word and
the initial-borrow bit need to be clean. -/
theorem uGreaterBorrowStep_get_final_work_of_clean_bank
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hwork : ∀ k : Fin n,
      (coefficientCarryWorkBit n counterWidth k).get x = false)
    (hfinal : bit.val + 1 = n) :
    (coefficientCarryWorkBit n counterWidth bit).get
        (uGreaterBorrowStep n counterWidth x) =
      decide (x.core.v.val < x.core.u.val) := by
  rw [uGreaterBorrowStep_eq_indexStep]
  have hborrow :=
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_workBorrow_natBorrow
      (uGreaterBorrowLayout n counterWidth)
      x.core.v.val x.core.u.val bit x
      (by
        intro k
        simpa [uGreaterBorrowLayout, coefficientCarryWorkWord] using hwork k)
      (by simpa [uGreaterBorrowLayout] using hscratchA)
      (by intro k; simp [uGreaterBorrowLayout])
      (by intro k; simp [uGreaterBorrowLayout])
  rw [show
    (coefficientCarryWorkBit n counterWidth bit).get
        (QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep
          (uGreaterBorrowLayout n counterWidth) x) =
      QuantumAlg.Comparator.natBorrow x.core.v.val x.core.u.val
        (bit.val + 1) by
    simpa [uGreaterBorrowLayout, coefficientCarryWorkWord] using hborrow]
  have hv : x.core.v.val < 2 ^ (bit.val + 1) := by simp [hfinal]
  have hu : x.core.u.val < 2 ^ (bit.val + 1) := by simp [hfinal]
  simpa using
    QuantumAlg.Comparator.natBorrow_eq_decide_lt_of_lt_two_pow
      (a := x.core.v.val) (b := x.core.u.val) (n := bit.val + 1) hv hu

/-- Copy the final borrow into the core comparison bit. -/
def uGreaterCopyGate (n counterWidth : Nat) (bit : Fin n) :
    EncodedBit.GateSpec (encoding n counterWidth) :=
  EncodedBit.GateSpec.cnot
    (coefficientCarryWorkBit n counterWidth bit)
    (compareBit n counterWidth)
    (Ne.symm (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth) bit))

/-- Forward borrow computation followed by copying its final bit into the
core comparison flag. -/
def uGreaterComputeGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  uGreaterBorrowGates n counterWidth ++
    [uGreaterCopyGate n counterWidth bit]

/-- Semantic action of the compact forward comparison computation. -/
def uGreaterComputeStep
    (n counterWidth : Nat) (bit : Fin n) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uGreaterComputeGates n counterWidth bit)

/-- Compute-copy-uncompute selector using the shared VBE carry bank. -/
def uGreaterSelectorGates
    (n counterWidth : Nat) (bit : Fin n) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  uGreaterComputeGates n counterWidth bit ++
    (uGreaterBorrowGates n counterWidth).reverse

/-- Actual base-gate program for the compact comparison selector. -/
def uGreaterSelectorProgram
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (uGreaterSelectorGates n counterWidth bit)

/-- Semantic action of the compact comparison selector. -/
def uGreaterSelectorStep
    (n counterWidth : Nat) (bit : Fin n) :
    Registers n counterWidth -> Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (uGreaterSelectorGates n counterWidth bit)

/-- The compact selector is realized by the same native gate list used for
its resource ledger. -/
theorem uGreaterSelector_realizes
    (n counterWidth : Nat) (bit : Fin n) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (uGreaterSelectorProgram n counterWidth bit)
      (uGreaterSelectorStep n counterWidth bit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (uGreaterSelectorGates n counterWidth bit)

/-- The compute-copy-uncompute comparator selector is self-inverse. -/
theorem uGreaterSelectorStep_self
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    uGreaterSelectorStep n counterWidth bit
        (uGreaterSelectorStep n counterWidth bit x) = x := by
  let gates := uGreaterSelectorGates n counterWidth bit
  have hreverse : gates.reverse = gates := by
    simp [gates, uGreaterSelectorGates, uGreaterComputeGates,
      List.reverse_append, List.append_assoc]
  change EncodedBit.GateSpec.stepList gates
      (EncodedBit.GateSpec.stepList gates x) = x
  simpa [hreverse] using
    EncodedBit.GateSpec.stepList_reverse_stepList gates x

/-- Reversing the borrow pass preserves the comparison flag. -/
theorem uGreaterBorrowReverseStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (uGreaterBorrowReverseStep n counterWidth x) =
      (compareBit n counterWidth).get x := by
  let gates := uGreaterBorrowGates n counterWidth
  have hleft :
      uGreaterBorrowStep n counterWidth
          (EncodedBit.GateSpec.stepList gates.reverse x) = x := by
    change EncodedBit.GateSpec.stepList gates
        (EncodedBit.GateSpec.stepList gates.reverse x) = x
    simpa [gates] using
      EncodedBit.GateSpec.stepList_reverse_stepList gates.reverse x
  have hpres := uGreaterBorrowStep_get_compare n counterWidth
    (EncodedBit.GateSpec.stepList gates.reverse x)
  change (compareBit n counterWidth).get
      (EncodedBit.GateSpec.stepList gates.reverse x) =
    (compareBit n counterWidth).get x
  rw [hleft] at hpres
  exact hpres.symm

/-- The reverse compact borrow pass has the same preservation boundary as the
forward pass. -/
theorem uGreaterBorrowReverseStep_get_of_minuend_work_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hminuend : ∀ j : Fin n,
      ((vValueWord n counterWidth).bit j).wire ≠ observed.wire)
    (hwork : ∀ j : Fin n,
      (coefficientCarryWorkBit n counterWidth j).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (uGreaterBorrowReverseStep n counterWidth x) =
      observed.get x := by
  let gates := uGreaterBorrowGates n counterWidth
  have hleft :
      uGreaterBorrowStep n counterWidth
          (EncodedBit.GateSpec.stepList gates.reverse x) = x := by
    change EncodedBit.GateSpec.stepList gates
        (EncodedBit.GateSpec.stepList gates.reverse x) = x
    simpa [gates] using
      EncodedBit.GateSpec.stepList_reverse_stepList gates.reverse x
  have hpres := uGreaterBorrowStep_get_of_minuend_work_ne
    n counterWidth observed hminuend hwork
      (EncodedBit.GateSpec.stepList gates.reverse x)
  change observed.get (EncodedBit.GateSpec.stepList gates.reverse x) =
    observed.get x
  rw [hleft] at hpres
  exact hpres.symm

/-- The compact compute-copy-uncompute selector preserves every observation
outside the comparison target, the temporary `v` targets, and the borrowed
VBE carry word. -/
theorem uGreaterSelectorStep_get_of_preserved
    (n counterWidth : Nat) (bit : Fin n)
    (observed : EncodedBit (encoding n counterWidth))
    (hcompare : (compareBit n counterWidth).wire ≠ observed.wire)
    (hminuend : ∀ j : Fin n,
      ((vValueWord n counterWidth).bit j).wire ≠ observed.wire)
    (hwork : ∀ j : Fin n,
      (coefficientCarryWorkBit n counterWidth j).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get (uGreaterSelectorStep n counterWidth bit x) =
      observed.get x := by
  rw [uGreaterSelectorStep, uGreaterSelectorGates,
    EncodedBit.GateSpec.stepList_append]
  change observed.get
      (uGreaterBorrowReverseStep n counterWidth
        (uGreaterComputeStep n counterWidth bit x)) = observed.get x
  rw [uGreaterBorrowReverseStep_get_of_minuend_work_ne
    n counterWidth observed hminuend hwork]
  rw [uGreaterComputeStep, uGreaterComputeGates,
    EncodedBit.GateSpec.stepList_append]
  change observed.get
      (EncodedBit.cnotStep (coefficientCarryWorkBit n counterWidth bit)
        (compareBit n counterWidth)
        (uGreaterBorrowStep n counterWidth x)) = observed.get x
  rw [EncodedBit.cnotStep_get_of_target_ne _ _ observed hcompare]
  exact uGreaterBorrowStep_get_of_minuend_work_ne
    n counterWidth observed hminuend hwork x

/-- The forward compact borrow gates do not touch the comparison flag. -/
theorem uGreaterBorrowGates_bitDisjoint_compare
    (n counterWidth : Nat) :
    forall gate, gate ∈ uGreaterBorrowGates n counterWidth ->
      EncodedBit.GateSpec.bitDisjoint (compareBit n counterWidth) gate := by
  exact QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_bitDisjoint
    (uGreaterBorrowLayout n counterWidth) (compareBit n counterWidth)
    (fun j => liftCoreBit_wire_ne n counterWidth
      (RegisterBits.v_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire j)))
    (fun j => liftCoreBit_wire_ne n counterWidth
      (RegisterBits.u_compare_wire_ne n counterWidth
        (WireAddress.littleEndianWire j)))
    (liftCoreBit_wire_ne n counterWidth
      (Ne.symm (RegisterBits.compare_scratchA_wire_ne n counterWidth)))
    (fun j => Ne.symm
      (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth) j))

/-- The compact borrow pass uses only core and shared-work wires, hence it is
disjoint from every caller-owned target bit. -/
theorem uGreaterBorrowGates_bitDisjoint_target
    (n counterWidth : Nat) (targetIndex : Fin n) :
    ∀ gate, gate ∈ uGreaterBorrowGates n counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  exact QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_bitDisjoint
    (uGreaterBorrowLayout n counterWidth)
    (targetValueBit n counterWidth targetIndex)
    (fun j => by
      simpa [uGreaterBorrowLayout, vValueWord] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth j) targetIndex)
    (fun j => by
      simpa [uGreaterBorrowLayout, uValueWord] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth j) targetIndex)
    (by
      simpa [uGreaterBorrowLayout, scratchABit] using
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth) targetIndex)
    (fun j => by
      simpa [uGreaterBorrowLayout, coefficientCarryWorkWord,
        coefficientCarryWorkBit] using
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedCoefficientCarryWorkBit n counterWidth j) targetIndex)

/-- The compute-copy-uncompute compact comparison selector never reads or
writes the public target word. -/
theorem uGreaterSelectorGates_bitDisjoint_target
    (n counterWidth : Nat) (bit targetIndex : Fin n) :
    ∀ gate, gate ∈ uGreaterSelectorGates n counterWidth bit →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  simp only [uGreaterSelectorGates, uGreaterComputeGates, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with (hborrow | rfl) | hreverse
  · exact uGreaterBorrowGates_bitDisjoint_target n counterWidth targetIndex
      gate hborrow
  · exact ⟨
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedCoefficientCarryWorkBit n counterWidth bit) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth) targetIndex⟩
  · exact uGreaterBorrowGates_bitDisjoint_target n counterWidth targetIndex
      gate (List.mem_reverse.mp hreverse)

/-- Reverse borrow cleanup commutes with flipping the untouched comparison
flag. -/
theorem uGreaterBorrowReverseStep_flip_compare_comm
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    uGreaterBorrowReverseStep n counterWidth
        ((compareBit n counterWidth).flip x) =
      (compareBit n counterWidth).flip
        (uGreaterBorrowReverseStep n counterWidth x) := by
  apply EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
  intro gate hgate
  exact uGreaterBorrowGates_bitDisjoint_compare n counterWidth gate
    (by simpa [uGreaterBorrowReverseStep] using hgate)

/-- The compute-copy-uncompute selector restores every borrowed VBE carry bit.
This is the central clean-bank guarantee allowing the following coefficient
adder to reuse the same physical work object. -/
theorem uGreaterSelectorStep_get_coefficientCarryWorkBit
    (n counterWidth : Nat) (bit workBit : Fin n)
    (x : Registers n counterWidth) :
    (coefficientCarryWorkBit n counterWidth workBit).get
        (uGreaterSelectorStep n counterWidth bit x) =
      (coefficientCarryWorkBit n counterWidth workBit).get x := by
  let gates := uGreaterBorrowGates n counterWidth
  let work := coefficientCarryWorkBit n counterWidth workBit
  let compare := compareBit n counterWidth
  let y := uGreaterBorrowStep n counterWidth x
  have hreverse_forward :
      uGreaterBorrowReverseStep n counterWidth y = x := by
    dsimp [y, uGreaterBorrowReverseStep, uGreaterBorrowStep, gates]
    exact EncodedBit.GateSpec.stepList_reverse_stepList
      (uGreaterBorrowGates n counterWidth) x
  rw [uGreaterSelectorStep, uGreaterSelectorGates, uGreaterComputeGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  change work.get
      (uGreaterBorrowReverseStep n counterWidth
        (EncodedBit.GateSpec.step (uGreaterCopyGate n counterWidth bit) y)) =
    work.get x
  change work.get
      (uGreaterBorrowReverseStep n counterWidth
        (EncodedBit.cnotStep (coefficientCarryWorkBit n counterWidth bit)
          compare y)) = work.get x
  unfold EncodedBit.cnotStep
  by_cases hcontrol :
      (coefficientCarryWorkBit n counterWidth bit).get y
  · rw [if_pos hcontrol]
    rw [uGreaterBorrowReverseStep_flip_compare_comm]
    rw [EncodedBit.get_flip_of_wire_ne compare work
      (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
        (RegisterBits.compareBit n counterWidth) workBit)]
    exact congrArg work.get hreverse_forward
  · rw [if_neg hcontrol]
    exact congrArg work.get hreverse_forward

/-- The forward compact borrow pass preserves the VBE carry-in bit. -/
theorem uGreaterBorrowStep_get_coefficientCarryInBit
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (coefficientCarryInBit n counterWidth).get
        (uGreaterBorrowStep n counterWidth x) =
      (coefficientCarryInBit n counterWidth).get x := by
  rw [uGreaterBorrowStep_eq_indexStep]
  exact
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStageIndexStep_get_of_minuend_work_ne
      (uGreaterBorrowLayout n counterWidth)
      (coefficientCarryInBit n counterWidth)
      (fun j => liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth j))
      (fun j => Ne.symm
        (coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
          n counterWidth j)) x

/-- The reverse compact borrow pass preserves the VBE carry-in bit. -/
theorem uGreaterBorrowReverseStep_get_coefficientCarryInBit
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (coefficientCarryInBit n counterWidth).get
        (uGreaterBorrowReverseStep n counterWidth x) =
      (coefficientCarryInBit n counterWidth).get x := by
  let gates := uGreaterBorrowGates n counterWidth
  have hleft :
      uGreaterBorrowStep n counterWidth
          (EncodedBit.GateSpec.stepList gates.reverse x) = x := by
    change EncodedBit.GateSpec.stepList gates
        (EncodedBit.GateSpec.stepList gates.reverse x) = x
    simpa [gates] using
      EncodedBit.GateSpec.stepList_reverse_stepList gates.reverse x
  have hpres := uGreaterBorrowStep_get_coefficientCarryInBit n counterWidth
    (EncodedBit.GateSpec.stepList gates.reverse x)
  change (coefficientCarryInBit n counterWidth).get
      (EncodedBit.GateSpec.stepList gates.reverse x) =
    (coefficientCarryInBit n counterWidth).get x
  rw [hleft] at hpres
  exact hpres.symm

/-- The full compact selector preserves the VBE carry-in bit. -/
theorem uGreaterSelectorStep_get_coefficientCarryInBit
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth) :
    (coefficientCarryInBit n counterWidth).get
        (uGreaterSelectorStep n counterWidth bit x) =
      (coefficientCarryInBit n counterWidth).get x := by
  rw [uGreaterSelectorStep, uGreaterSelectorGates,
    EncodedBit.GateSpec.stepList_append]
  change (coefficientCarryInBit n counterWidth).get
      (uGreaterBorrowReverseStep n counterWidth
        (uGreaterComputeStep n counterWidth bit x)) = _
  rw [uGreaterBorrowReverseStep_get_coefficientCarryInBit]
  rw [uGreaterComputeStep, uGreaterComputeGates,
    EncodedBit.GateSpec.stepList_append]
  change (coefficientCarryInBit n counterWidth).get
      (EncodedBit.cnotStep (coefficientCarryWorkBit n counterWidth bit)
        (compareBit n counterWidth)
        (uGreaterBorrowStep n counterWidth x)) = _
  rw [EncodedBit.cnotStep_get_of_target_ne
    (coefficientCarryWorkBit n counterWidth bit)
    (compareBit n counterWidth) (coefficientCarryInBit n counterWidth)
    (liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
      (RegisterBits.compareBit n counterWidth))]
  exact uGreaterBorrowStep_get_coefficientCarryInBit n counterWidth x

/-- Starting with clean shared work, the compact selector restores the entire
VBE coefficient-adder work object, not only its temporary word. -/
theorem uGreaterSelectorStep_coefficientAdder_clean
    (n counterWidth : Nat) (bit : Fin n)
    (core : MK.Registers n counterWidth) (target : Word n) :
    (uGreaterSelectorStep n counterWidth bit
      { core := core
        shared := cleanSharedWork n counterWidth
        target := target }).shared.coefficientAdder =
      cleanCoeffAdderWork n := by
  apply Prod.ext
  · change (coefficientCarryInBit n counterWidth).get
        (uGreaterSelectorStep n counterWidth bit
          { core := core
            shared := cleanSharedWork n counterWidth
            target := target }) = false
    rw [uGreaterSelectorStep_get_coefficientCarryInBit]
    exact coefficientCarryInBit_get_clean n counterWidth core target
  · apply PlainAdder.Schedule.PowerOfTwo.finIdentity_eq_zero_of_get_false
    intro workBit
    change (coefficientCarryWorkBit n counterWidth workBit).get
        (uGreaterSelectorStep n counterWidth bit
          { core := core
            shared := cleanSharedWork n counterWidth
            target := target }) = false
    rw [uGreaterSelectorStep_get_coefficientCarryWorkBit]
    exact coefficientCarryWorkBit_get_clean n counterWidth workBit core target

/-- On a clean compact boundary, the selector leaves `compare` equal to the
mathematical `u>v` predicate while restoring its borrowed VBE bank. -/
theorem uGreaterSelectorStep_get_compare_clean
    (n counterWidth : Nat) (bit : Fin n)
    (core : MK.Registers n counterWidth) (target : Word n)
    (hscratchA : core.scratchA = false)
    (hcompare : core.compare = false)
    (hfinal : bit.val + 1 = n) :
    (compareBit n counterWidth).get
        (uGreaterSelectorStep n counterWidth bit
          { core := core
            shared := cleanSharedWork n counterWidth
            target := target }) =
      decide (core.v.val < core.u.val) := by
  let x : Registers n counterWidth :=
    { core := core
      shared := cleanSharedWork n counterWidth
      target := target }
  rw [uGreaterSelectorStep, uGreaterSelectorGates,
    EncodedBit.GateSpec.stepList_append]
  change (compareBit n counterWidth).get
      (uGreaterBorrowReverseStep n counterWidth
        (uGreaterComputeStep n counterWidth bit x)) = _
  rw [uGreaterBorrowReverseStep_get_compare]
  rw [uGreaterComputeStep, uGreaterComputeGates,
    EncodedBit.GateSpec.stepList_append]
  change (compareBit n counterWidth).get
      (EncodedBit.GateSpec.step (uGreaterCopyGate n counterWidth bit)
        (uGreaterBorrowStep n counterWidth x)) = _
  rw [show EncodedBit.GateSpec.step (uGreaterCopyGate n counterWidth bit) =
      EncodedBit.cnotStep (coefficientCarryWorkBit n counterWidth bit)
        (compareBit n counterWidth) by rfl]
  rw [EncodedBit.cnotStep_get_target]
  rw [uGreaterBorrowStep_get_compare]
  have hxcompare : (compareBit n counterWidth).get x = false := by
    simp [x, hcompare]
  rw [hxcompare]
  simpa using
    uGreaterBorrowStep_get_final_work_clean n counterWidth bit core target
      hscratchA hfinal

/-- With a clean borrowed VBE word, the compact selector xors the mathematical
`u>v` predicate into an arbitrary pre-existing comparison bit. -/
theorem uGreaterSelectorStep_get_compare_of_clean_bank
    (n counterWidth : Nat) (bit : Fin n)
    (x : Registers n counterWidth)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hwork : ∀ k : Fin n,
      (coefficientCarryWorkBit n counterWidth k).get x = false)
    (hfinal : bit.val + 1 = n) :
    (compareBit n counterWidth).get
        (uGreaterSelectorStep n counterWidth bit x) =
      ((compareBit n counterWidth).get x ^^
        decide (x.core.v.val < x.core.u.val)) := by
  rw [uGreaterSelectorStep, uGreaterSelectorGates,
    EncodedBit.GateSpec.stepList_append]
  change (compareBit n counterWidth).get
      (uGreaterBorrowReverseStep n counterWidth
        (uGreaterComputeStep n counterWidth bit x)) = _
  rw [uGreaterBorrowReverseStep_get_compare]
  rw [uGreaterComputeStep, uGreaterComputeGates,
    EncodedBit.GateSpec.stepList_append]
  change (compareBit n counterWidth).get
      (EncodedBit.cnotStep (coefficientCarryWorkBit n counterWidth bit)
        (compareBit n counterWidth)
        (uGreaterBorrowStep n counterWidth x)) = _
  rw [EncodedBit.cnotStep_get_target, uGreaterBorrowStep_get_compare,
    uGreaterBorrowStep_get_final_work_of_clean_bank n counterWidth bit x
      hscratchA hwork hfinal]

/-- The VBE-work reuse changes no comparator gates: it only changes which
clean physical word supplies the borrow bits. -/
theorem uGreaterSelectorGates_length
    (n counterWidth : Nat) (bit : Fin n) :
    (uGreaterSelectorGates n counterWidth bit).length = 10 * n + 1 := by
  simp [uGreaterSelectorGates, uGreaterBorrowGates,
    uGreaterComputeGates,
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_length]
  omega

/-- Exact X coordinate of the compact comparison selector. -/
theorem uGreaterSelectorGates_xMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((uGreaterSelectorGates n counterWidth bit).map
      EncodedBit.GateSpec.xMultiplicity).sum = 4 * n := by
  simp [uGreaterSelectorGates, uGreaterComputeGates, uGreaterBorrowGates,
    uGreaterCopyGate,
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_xMultiplicity_sum]
  omega

/-- Exact CNOT coordinate of the compact comparison selector. -/
theorem uGreaterSelectorGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((uGreaterSelectorGates n counterWidth bit).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp [uGreaterSelectorGates, uGreaterComputeGates, uGreaterBorrowGates,
    uGreaterCopyGate,
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_cnotMultiplicity_sum]

/-- Exact Toffoli coordinate of the compact comparison selector. -/
theorem uGreaterSelectorGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (bit : Fin n) :
    ((uGreaterSelectorGates n counterWidth bit).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 6 * n := by
  simp [uGreaterSelectorGates, uGreaterComputeGates, uGreaterBorrowGates,
    uGreaterCopyGate,
    QuantumAlg.Comparator.BorrowWorkLayout.borrowStage_toffoliMultiplicity_sum]
  omega

/-- The compact selector preserves the shared path bit. -/
theorem uGreaterSelectorStep_get_path
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    (pathBit n counterWidth).get
        (uGreaterSelectorStep n counterWidth bit x) =
      (pathBit n counterWidth).get x := by
  exact uGreaterSelectorStep_get_of_preserved n counterWidth bit
    (pathBit n counterWidth)
    (by
      simpa [compareBit, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedPathBit n counterWidth))
    (by
      intro j
      simpa [vValueWord, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth j)
          (sharedPathBit n counterWidth))
    (fun j => (pathBit_coefficientCarryWorkBit_wire_ne
      n counterWidth j).symm) x

/-- The compact selector preserves the shared clean control bit. -/
theorem uGreaterSelectorStep_get_control
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    (controlBit n counterWidth).get
        (uGreaterSelectorStep n counterWidth bit x) =
      (controlBit n counterWidth).get x := by
  exact uGreaterSelectorStep_get_of_preserved n counterWidth bit
    (controlBit n counterWidth)
    (by
      simpa [compareBit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedControlBit n counterWidth))
    (by
      intro j
      simpa [vValueWord, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth j)
          (sharedControlBit n counterWidth))
    (fun j => (controlBit_coefficientCarryWorkBit_wire_ne
      n counterWidth j).symm) x

/-- The compact selector restores its clean initial-borrow bit. -/
theorem uGreaterSelectorStep_get_scratchA
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    (scratchABit n counterWidth).get
        (uGreaterSelectorStep n counterWidth bit x) =
      (scratchABit n counterWidth).get x := by
  exact uGreaterSelectorStep_get_of_preserved n counterWidth bit
    (scratchABit n counterWidth)
    (by
      simpa [compareBit, scratchABit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_scratchA_wire_ne n counterWidth))
    (by
      intro j
      simpa [vValueWord, scratchABit, RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_scratchA_wire_ne n counterWidth
            (WireAddress.littleEndianWire j)))
    (by
      intro j
      simpa [scratchABit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth) j).symm) x

/-- The compact selector preserves the active-round bit. -/
theorem uGreaterSelectorStep_get_active
    (n counterWidth : Nat) (bit : Fin n) (x : Registers n counterWidth) :
    (activeBit n counterWidth).get
        (uGreaterSelectorStep n counterWidth bit x) =
      (activeBit n counterWidth).get x := by
  exact uGreaterSelectorStep_get_of_preserved n counterWidth bit
    (activeBit n counterWidth)
    (by
      simpa [compareBit, activeBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.active_compare_wire_ne n counterWidth).symm)
    (by
      intro j
      simpa [vValueWord, activeBit, RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.active_v_wire_ne n counterWidth
            (WireAddress.littleEndianWire j)).symm)
    (by
      intro j
      simpa [activeBit] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.activeBit n counterWidth) j).symm) x

/-- The compact selector preserves every `u` value bit. -/
theorem uGreaterSelectorStep_get_uValueBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : Registers n counterWidth) :
    ((uValueWord n counterWidth).bit targetBit).get
        (uGreaterSelectorStep n counterWidth selectorBit x) =
      ((uValueWord n counterWidth).bit targetBit).get x := by
  exact uGreaterSelectorStep_get_of_preserved n counterWidth selectorBit
    ((uValueWord n counterWidth).bit targetBit)
    (by
      simpa [compareBit, uValueWord, RegisterBits.uValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire targetBit)).symm)
    (by
      intro j
      simpa [uValueWord, vValueWord, RegisterBits.uValueBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_v_wire_ne n counterWidth
            (WireAddress.littleEndianWire targetBit)
            (WireAddress.littleEndianWire j)).symm)
    (by
      intro j
      simpa [uValueWord] using
        (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth targetBit) j).symm) x

/-- The compute-copy-uncompute selector restores every `v` value bit. -/
theorem uGreaterSelectorStep_get_vValueBit
    (n counterWidth : Nat) (selectorBit targetBit : Fin n)
    (x : Registers n counterWidth) :
    ((vValueWord n counterWidth).bit targetBit).get
        (uGreaterSelectorStep n counterWidth selectorBit x) =
      ((vValueWord n counterWidth).bit targetBit).get x := by
  let gates := uGreaterBorrowGates n counterWidth
  let source := (vValueWord n counterWidth).bit targetBit
  let compare := compareBit n counterWidth
  let y := uGreaterBorrowStep n counterWidth x
  have hreverse_forward :
      uGreaterBorrowReverseStep n counterWidth y = x := by
    dsimp [y, uGreaterBorrowReverseStep, uGreaterBorrowStep, gates]
    exact EncodedBit.GateSpec.stepList_reverse_stepList
      (uGreaterBorrowGates n counterWidth) x
  rw [uGreaterSelectorStep, uGreaterSelectorGates, uGreaterComputeGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  change source.get
      (uGreaterBorrowReverseStep n counterWidth
        (EncodedBit.cnotStep
          (coefficientCarryWorkBit n counterWidth selectorBit)
          compare y)) = source.get x
  unfold EncodedBit.cnotStep
  by_cases hcopy :
      (coefficientCarryWorkBit n counterWidth selectorBit).get y
  · rw [if_pos hcopy, uGreaterBorrowReverseStep_flip_compare_comm]
    rw [EncodedBit.get_flip_of_wire_ne compare source]
    · exact congrArg source.get hreverse_forward
    · simpa [compare, source, compareBit, vValueWord,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.v_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire targetBit)).symm
  · rw [if_neg hcopy]
    exact congrArg source.get hreverse_forward

theorem uGreaterSelectorStep_core_u
    (n counterWidth : Nat) (selectorBit : Fin n)
    (x : Registers n counterWidth) :
    (uGreaterSelectorStep n counterWidth selectorBit x).core.u = x.core.u := by
  apply word_eq_of_testBit_eq
  intro targetBit
  simpa only [uValueWord_get] using
    uGreaterSelectorStep_get_uValueBit n counterWidth selectorBit targetBit x

theorem uGreaterSelectorStep_core_v
    (n counterWidth : Nat) (selectorBit : Fin n)
    (x : Registers n counterWidth) :
    (uGreaterSelectorStep n counterWidth selectorBit x).core.v = x.core.v := by
  apply word_eq_of_testBit_eq
  intro targetBit
  simpa only [vValueWord_get] using
    uGreaterSelectorStep_get_vValueBit n counterWidth selectorBit targetBit x

/-! ### Active odd-odd comparison mask -/

/-- The original low source bits toggle the reusable path bit exactly when
both source words are odd. -/
def oddPairPathGate (n counterWidth : Nat) (low : Fin n) :
    EncodedBit.GateSpec (encoding n counterWidth) :=
  EncodedBit.GateSpec.toffoli
    ((uValueWord n counterWidth).bit low)
    ((vValueWord n counterWidth).bit low)
    (pathBit n counterWidth)
    (by
      simpa [uValueWord, vValueWord, RegisterBits.uValueBit,
        RegisterBits.vValueBit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.u_v_wire_ne n counterWidth
            (WireAddress.littleEndianWire low)
            (WireAddress.littleEndianWire low)))
    (by
      simpa [uValueWord, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth low)
          (sharedPathBit n counterWidth))
    (by
      simpa [vValueWord, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth low)
          (sharedPathBit n counterWidth))

theorem oddPairPathGate_bitDisjoint_active
    (n counterWidth : Nat) (low : Fin n) :
    EncodedBit.GateSpec.bitDisjoint (activeBit n counterWidth)
      (oddPairPathGate n counterWidth low) := by
  simp only [oddPairPathGate, EncodedBit.GateSpec.bitDisjoint]
  constructor
  · simpa [uValueWord, activeBit, RegisterBits.uValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.active_u_wire_ne n counterWidth
          (WireAddress.littleEndianWire low)).symm
  constructor
  · simpa [vValueWord, activeBit, RegisterBits.vValueBit] using
      liftCoreBit_wire_ne n counterWidth
        (RegisterBits.active_v_wire_ne n counterWidth
          (WireAddress.littleEndianWire low)).symm
  · simpa [pathBit, activeBit] using
      (liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.activeBit n counterWidth)
        (sharedPathBit n counterWidth)).symm

theorem oddPairPathGate_bitDisjoint_control
    (n counterWidth : Nat) (low : Fin n) :
    EncodedBit.GateSpec.bitDisjoint (controlBit n counterWidth)
      (oddPairPathGate n counterWidth low) := by
  simp only [oddPairPathGate, EncodedBit.GateSpec.bitDisjoint]
  constructor
  · simpa [uValueWord, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.uValueBit n counterWidth low)
        (sharedControlBit n counterWidth)
  constructor
  · simpa [vValueWord, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth low)
        (sharedControlBit n counterWidth)
  · exact pathBit_controlBit_wire_ne n counterWidth

/-- Three native Toffolis compute `active ∧ u₀ ∧ v₀` into the reusable
path bit and restore the reusable control bit. -/
def activeOddPathGates (n counterWidth : Nat) (low : Fin n) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  EncodedBit.GateSpec.controlledWithWorkGates
    (activeBit n counterWidth) (controlBit n counterWidth)
    (oddPairPathGate n counterWidth low)
    (oddPairPathGate_bitDisjoint_active n counterWidth low)
    (oddPairPathGate_bitDisjoint_control n counterWidth low)
    (by
      simpa [activeBit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.activeBit n counterWidth)
          (sharedControlBit n counterWidth))

/-- The masked odd-pair path computation is disjoint from every public target
bit. -/
theorem activeOddPathGates_bitDisjoint_target
    (n counterWidth : Nat) (low targetIndex : Fin n) :
    ∀ gate, gate ∈ activeOddPathGates n counterWidth low →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit n counterWidth targetIndex) gate := by
  unfold activeOddPathGates
  apply EncodedBit.GateSpec.controlledWithWorkGates_bitDisjoint
  · exact liftCoreBit_targetValueBit_wire_ne n counterWidth
      (RegisterBits.activeBit n counterWidth) targetIndex
  · exact liftSharedBit_targetValueBit_wire_ne n counterWidth
      (sharedControlBit n counterWidth) targetIndex
  · exact ⟨
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.uValueBit n counterWidth low) targetIndex,
      liftCoreBit_targetValueBit_wire_ne n counterWidth
        (RegisterBits.vValueBit n counterWidth low) targetIndex,
      liftSharedBit_targetValueBit_wire_ne n counterWidth
        (sharedPathBit n counterWidth) targetIndex⟩

def activeOddPathStep (n counterWidth : Nat) (low : Fin n) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.controlledWithWorkStep
    (activeBit n counterWidth) (controlBit n counterWidth)
    (oddPairPathGate n counterWidth low)
    (oddPairPathGate_bitDisjoint_active n counterWidth low)
    (oddPairPathGate_bitDisjoint_control n counterWidth low)
    (by
      simpa [activeBit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.activeBit n counterWidth)
          (sharedControlBit n counterWidth))

def activeOddPathProgram (n counterWidth : Nat) (low : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeOddPathGates n counterWidth low)

/-- With a true active flag, clean shared control, and a non-odd input pair,
the masked odd-path computation is the identity. -/
theorem activeOddPathStep_eq_self_of_pair_false
    (n counterWidth : Nat) (low : Fin n)
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hpair :
      (((uValueWord n counterWidth).bit low).get x &&
        ((vValueWord n counterWidth).bit low).get x) = false) :
    activeOddPathStep n counterWidth low x = x := by
  have hcontrolled :=
    EncodedBit.GateSpec.controlledWithWorkStep_eq_step_of_control_true
      (activeBit n counterWidth) (controlBit n counterWidth)
      (oddPairPathGate n counterWidth low)
      (oddPairPathGate_bitDisjoint_active n counterWidth low)
      (oddPairPathGate_bitDisjoint_control n counterWidth low)
      (by
        simpa [activeBit, controlBit] using
          liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.activeBit n counterWidth)
            (sharedControlBit n counterWidth))
      x hactive hcontrol
  rw [activeOddPathStep, hcontrolled]
  change EncodedBit.toffoliStep
      ((uValueWord n counterWidth).bit low)
      ((vValueWord n counterWidth).bit low)
      (pathBit n counterWidth) x = x
  unfold EncodedBit.toffoliStep
  rw [if_neg]
  intro htrue
  rw [hpair] at htrue
  contradiction

theorem activeOddPath_realizes
    (n counterWidth : Nat) (low : Fin n) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (activeOddPathProgram n counterWidth low)
      (activeOddPathStep n counterWidth low) := by
  exact EncodedBit.GateSpec.controlledWithWorkWitness
    (QubitLayout.canonical _) .empty
    (activeBit n counterWidth) (controlBit n counterWidth)
    (oddPairPathGate n counterWidth low)
    (oddPairPathGate_bitDisjoint_active n counterWidth low)
    (oddPairPathGate_bitDisjoint_control n counterWidth low)
    (by
      simpa [activeBit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.activeBit n counterWidth)
          (sharedControlBit n counterWidth))

@[simp] theorem activeOddPathGates_length
    (n counterWidth : Nat) (low : Fin n) :
    (activeOddPathGates n counterWidth low).length = 3 := by
  simp [activeOddPathGates, oddPairPathGate,
    EncodedBit.GateSpec.controlledWithWorkGates]

@[simp] theorem activeOddPathGates_xMultiplicity_sum
    (n counterWidth : Nat) (low : Fin n) :
    ((activeOddPathGates n counterWidth low).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simp [activeOddPathGates, oddPairPathGate,
    EncodedBit.GateSpec.controlledWithWorkGates]

@[simp] theorem activeOddPathGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (low : Fin n) :
    ((activeOddPathGates n counterWidth low).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp [activeOddPathGates, oddPairPathGate,
    EncodedBit.GateSpec.controlledWithWorkGates]

@[simp] theorem activeOddPathGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (low : Fin n) :
    ((activeOddPathGates n counterWidth low).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 3 := by
  simp [activeOddPathGates, oddPairPathGate,
    EncodedBit.GateSpec.controlledWithWorkGates]

theorem activeOddPathStep_get_path_of_clean_control
    (n counterWidth : Nat) (low : Fin n) (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    (pathBit n counterWidth).get (activeOddPathStep n counterWidth low x) =
      Bool.xor ((pathBit n counterWidth).get x)
        (((activeBit n counterWidth).get x &&
          ((uValueWord n counterWidth).bit low).get x) &&
            ((vValueWord n counterWidth).bit low).get x) := by
  by_cases hactive : (activeBit n counterWidth).get x = true
  · rw [activeOddPathStep]
    rw [EncodedBit.GateSpec.controlledWithWorkStep_eq_step_of_control_true
      (activeBit n counterWidth) (controlBit n counterWidth)
      (oddPairPathGate n counterWidth low)
      (oddPairPathGate_bitDisjoint_active n counterWidth low)
      (oddPairPathGate_bitDisjoint_control n counterWidth low) _ x hactive
      hcontrol]
    change (pathBit n counterWidth).get
        (EncodedBit.toffoliStep
          ((uValueWord n counterWidth).bit low)
          ((vValueWord n counterWidth).bit low)
          (pathBit n counterWidth) x) = _
    rw [EncodedBit.toffoliStep_get_target, hactive]
    cases ((uValueWord n counterWidth).bit low).get x <;>
      cases ((vValueWord n counterWidth).bit low).get x <;> rfl
  · have hactiveFalse : (activeBit n counterWidth).get x = false := by
      cases h : (activeBit n counterWidth).get x
      · rfl
      · exact False.elim (hactive h)
    rw [activeOddPathStep]
    rw [EncodedBit.GateSpec.controlledWithWorkStep_eq_self_of_control_false
      (activeBit n counterWidth) (controlBit n counterWidth)
      (oddPairPathGate n counterWidth low)
      (oddPairPathGate_bitDisjoint_active n counterWidth low)
      (oddPairPathGate_bitDisjoint_control n counterWidth low) _ x
      hactiveFalse]
    have hactiveField : x.core.active = false := by
      simpa only [activeBit_get] using hactiveFalse
    simp [hactiveField]

theorem activeOddPathStep_get_control_of_clean
    (n counterWidth : Nat) (low : Fin n) (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    (controlBit n counterWidth).get
        (activeOddPathStep n counterWidth low x) = false := by
  by_cases hactive : (activeBit n counterWidth).get x = true
  · rw [activeOddPathStep]
    rw [EncodedBit.GateSpec.controlledWithWorkStep_eq_step_of_control_true
      (activeBit n counterWidth) (controlBit n counterWidth)
      (oddPairPathGate n counterWidth low)
      (oddPairPathGate_bitDisjoint_active n counterWidth low)
      (oddPairPathGate_bitDisjoint_control n counterWidth low) _ x hactive
      hcontrol]
    change (controlBit n counterWidth).get
        (EncodedBit.toffoliStep
          ((uValueWord n counterWidth).bit low)
          ((vValueWord n counterWidth).bit low)
          (pathBit n counterWidth) x) = false
    rw [EncodedBit.toffoliStep_get_of_target_ne _ _ _
      (controlBit n counterWidth) (pathBit_controlBit_wire_ne n counterWidth),
      hcontrol]
  · have hactiveFalse : (activeBit n counterWidth).get x = false := by
      cases h : (activeBit n counterWidth).get x
      · rfl
      · exact False.elim (hactive h)
    rw [activeOddPathStep]
    rw [EncodedBit.GateSpec.controlledWithWorkStep_eq_self_of_control_false
      (activeBit n counterWidth) (controlBit n counterWidth)
      (oddPairPathGate n counterWidth low)
      (oddPairPathGate_bitDisjoint_active n counterWidth low)
      (oddPairPathGate_bitDisjoint_control n counterWidth low) _ x
      hactiveFalse, hcontrol]

/-- With clean reusable control work, active-odd staging changes only the path
bit. -/
theorem activeOddPathStep_get_of_path_ne
    (n counterWidth : Nat) (low : Fin n)
    (observed : EncodedBit (encoding n counterWidth))
    (hpath : (pathBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    observed.get (activeOddPathStep n counterWidth low x) = observed.get x := by
  by_cases hactive : (activeBit n counterWidth).get x = true
  · rw [activeOddPathStep]
    rw [EncodedBit.GateSpec.controlledWithWorkStep_eq_step_of_control_true
      (activeBit n counterWidth) (controlBit n counterWidth)
      (oddPairPathGate n counterWidth low)
      (oddPairPathGate_bitDisjoint_active n counterWidth low)
      (oddPairPathGate_bitDisjoint_control n counterWidth low) _ x hactive
      hcontrol]
    change observed.get
        (EncodedBit.toffoliStep
          ((uValueWord n counterWidth).bit low)
          ((vValueWord n counterWidth).bit low)
          (pathBit n counterWidth) x) = observed.get x
    exact EncodedBit.toffoliStep_get_of_target_ne _ _ _ observed hpath x
  · have hactiveFalse : (activeBit n counterWidth).get x = false := by
      cases h : (activeBit n counterWidth).get x
      · rfl
      · exact False.elim (hactive h)
    rw [activeOddPathStep]
    exact congrArg observed.get
      (EncodedBit.GateSpec.controlledWithWorkStep_eq_self_of_control_false
        (activeBit n counterWidth) (controlBit n counterWidth)
        (oddPairPathGate n counterWidth low)
        (oddPairPathGate_bitDisjoint_active n counterWidth low)
      (oddPairPathGate_bitDisjoint_control n counterWidth low) _ x
        hactiveFalse)

theorem activeOddPathStep_core_u
    (n counterWidth : Nat) (low : Fin n) (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    (activeOddPathStep n counterWidth low x).core.u = x.core.u := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h := activeOddPathStep_get_of_path_ne n counterWidth low
    ((uValueWord n counterWidth).bit targetBit)
    (by
      simpa [uValueWord, pathBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth targetBit)
          (sharedPathBit n counterWidth)).symm)
    x hcontrol
  simpa only [uValueWord_get] using h

theorem activeOddPathStep_core_v
    (n counterWidth : Nat) (low : Fin n) (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    (activeOddPathStep n counterWidth low x).core.v = x.core.v := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h := activeOddPathStep_get_of_path_ne n counterWidth low
    ((vValueWord n counterWidth).bit targetBit)
    (by
      simpa [vValueWord, pathBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth targetBit)
          (sharedPathBit n counterWidth)).symm)
    x hcontrol
  simpa only [vValueWord_get] using h

/-- Store `path ∧ compare` in the clean control bit.  The same self-inverse
gate erases that temporary value after the masked result has been copied. -/
def activeOddCompareStoreGate (n counterWidth : Nat) :
    EncodedBit.GateSpec (encoding n counterWidth) :=
  EncodedBit.GateSpec.toffoli
    (pathBit n counterWidth) (compareBit n counterWidth)
    (controlBit n counterWidth)
    (by
      simpa [pathBit, compareBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedPathBit n counterWidth)).symm)
    (pathBit_controlBit_wire_ne n counterWidth)
    (by
      simpa [compareBit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedControlBit n counterWidth))

/-- Copy the stored masked predicate into the core comparison bit. -/
def activeOddCompareCopyGate (n counterWidth : Nat) :
    EncodedBit.GateSpec (encoding n counterWidth) :=
  EncodedBit.GateSpec.cnot
    (controlBit n counterWidth) (compareBit n counterWidth)
    (by
      simpa [compareBit, controlBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedControlBit n counterWidth)).symm)

theorem activeOddCompareStoreStep_get_control
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (controlBit n counterWidth).get
        (EncodedBit.GateSpec.step
          (activeOddCompareStoreGate n counterWidth) x) =
      ((controlBit n counterWidth).get x ^^
        ((pathBit n counterWidth).get x &&
          (compareBit n counterWidth).get x)) := by
  exact EncodedBit.toffoliStep_get_target _ _ _ x

theorem activeOddCompareStoreStep_get_of_control_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hne : (controlBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (EncodedBit.GateSpec.step
          (activeOddCompareStoreGate n counterWidth) x) = observed.get x := by
  exact EncodedBit.toffoliStep_get_of_target_ne _ _ _ observed hne x

theorem activeOddCompareStoreStep_core_u
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (EncodedBit.GateSpec.step
      (activeOddCompareStoreGate n counterWidth) x).core.u = x.core.u := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h := activeOddCompareStoreStep_get_of_control_ne n counterWidth
    ((uValueWord n counterWidth).bit targetBit)
    (by
      simpa [uValueWord, controlBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.uValueBit n counterWidth targetBit)
          (sharedControlBit n counterWidth)).symm) x
  simpa only [uValueWord_get] using h

theorem activeOddCompareStoreStep_core_v
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (EncodedBit.GateSpec.step
      (activeOddCompareStoreGate n counterWidth) x).core.v = x.core.v := by
  apply word_eq_of_testBit_eq
  intro targetBit
  have h := activeOddCompareStoreStep_get_of_control_ne n counterWidth
    ((vValueWord n counterWidth).bit targetBit)
    (by
      simpa [vValueWord, controlBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.vValueBit n counterWidth targetBit)
          (sharedControlBit n counterWidth)).symm) x
  simpa only [vValueWord_get] using h

theorem activeOddCompareCopyStep_get_compare
    (n counterWidth : Nat) (x : Registers n counterWidth) :
    (compareBit n counterWidth).get
        (EncodedBit.GateSpec.step
          (activeOddCompareCopyGate n counterWidth) x) =
      ((compareBit n counterWidth).get x ^^
        (controlBit n counterWidth).get x) := by
  exact EncodedBit.cnotStep_get_target _ _ x

theorem activeOddCompareCopyStep_get_of_compare_ne
    (n counterWidth : Nat)
    (observed : EncodedBit (encoding n counterWidth))
    (hne : (compareBit n counterWidth).wire ≠ observed.wire)
    (x : Registers n counterWidth) :
    observed.get
        (EncodedBit.GateSpec.step
          (activeOddCompareCopyGate n counterWidth) x) = observed.get x := by
  exact EncodedBit.cnotStep_get_of_target_ne _ _ observed hne x

theorem activeOddCompareStoreStep_eq_self_of_path_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hpath : (pathBit n counterWidth).get x = false) :
    EncodedBit.GateSpec.step
        (activeOddCompareStoreGate n counterWidth) x = x := by
  have hpathCore : x.shared.path = false := by
    simpa only [pathBit_get] using hpath
  change EncodedBit.toffoliStep (pathBit n counterWidth)
      (compareBit n counterWidth) (controlBit n counterWidth) x = x
  unfold EncodedBit.toffoliStep
  rw [if_neg]
  simp [hpathCore]

theorem activeOddCompareCopyStep_eq_self_of_control_false
    (n counterWidth : Nat) (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    EncodedBit.GateSpec.step
        (activeOddCompareCopyGate n counterWidth) x = x := by
  have hcontrolCore : x.shared.control = false := by
    simpa only [controlBit_get] using hcontrol
  change EncodedBit.cnotStep (controlBit n counterWidth)
      (compareBit n counterWidth) x = x
  unfold EncodedBit.cnotStep
  rw [if_neg]
  simp [hcontrolCore]

/-- Literal native selector that leaves `compare` equal to
`active ∧ u₀ ∧ v₀ ∧ (v<u)` and retains `active ∧ u₀ ∧ v₀` in `path` for the
following route selection.  It runs the compact comparator twice: the first
pass exposes the predicate, while the second reversibly erases the unmasked
copy before the masked value is installed.  The control bit and sole VBE bank
are restored; the route erases `path` from the emitted branch code. -/
def activeOddUGreaterSelectorGates
    (n counterWidth : Nat) (low finalBit : Fin n) :
    List (EncodedBit.GateSpec (encoding n counterWidth)) :=
  activeOddPathGates n counterWidth low ++
    uGreaterSelectorGates n counterWidth finalBit ++
      [activeOddCompareStoreGate n counterWidth] ++
        uGreaterSelectorGates n counterWidth finalBit ++
          [activeOddCompareCopyGate n counterWidth,
            activeOddCompareStoreGate n counterWidth]

/-- The complete masked odd selector stays within the compact core/shared
carrier and is disjoint from each public target bit. -/
theorem activeOddUGreaterSelectorGates_bitDisjoint_target
    (n counterWidth : Nat) (low finalBit targetIndex : Fin n) :
    ∀ gate,
      gate ∈ activeOddUGreaterSelectorGates n counterWidth low finalBit →
        EncodedBit.GateSpec.bitDisjoint
          (targetValueBit n counterWidth targetIndex) gate := by
  intro gate hgate
  rw [activeOddUGreaterSelectorGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | hgate
  · rcases List.mem_append.mp hprefix with hprefix | hselector
    · rcases List.mem_append.mp hprefix with hprefix | hstore
      · rcases List.mem_append.mp hprefix with hpath | hselector
        · exact activeOddPathGates_bitDisjoint_target n counterWidth low
            targetIndex gate hpath
        · exact uGreaterSelectorGates_bitDisjoint_target n counterWidth
            finalBit targetIndex gate hselector
      · have : gate = activeOddCompareStoreGate n counterWidth := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false] using hstore
        subst gate
        exact ⟨
          liftSharedBit_targetValueBit_wire_ne n counterWidth
            (sharedPathBit n counterWidth) targetIndex,
          liftCoreBit_targetValueBit_wire_ne n counterWidth
            (RegisterBits.compareBit n counterWidth) targetIndex,
          liftSharedBit_targetValueBit_wire_ne n counterWidth
            (sharedControlBit n counterWidth) targetIndex⟩
    · exact uGreaterSelectorGates_bitDisjoint_target n counterWidth finalBit
        targetIndex gate hselector
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hgate
    rcases hgate with rfl | rfl
    · exact ⟨
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedControlBit n counterWidth) targetIndex,
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth) targetIndex⟩
    · exact ⟨
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedPathBit n counterWidth) targetIndex,
        liftCoreBit_targetValueBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth) targetIndex,
        liftSharedBit_targetValueBit_wire_ne n counterWidth
          (sharedControlBit n counterWidth) targetIndex⟩

def activeOddUGreaterSelectorStep
    (n counterWidth : Nat) (low finalBit : Fin n) :
    Registers n counterWidth → Registers n counterWidth :=
  EncodedBit.GateSpec.stepList
    (activeOddUGreaterSelectorGates n counterWidth low finalBit)

def activeOddUGreaterSelectorProgram
    (n counterWidth : Nat) (low finalBit : Fin n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        (encoding n counterWidth).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (activeOddUGreaterSelectorGates n counterWidth low finalBit)

theorem activeOddUGreaterSelector_realizes
    (n counterWidth : Nat) (low finalBit : Fin n) :
    UnitaryCircuit.Realizes (encoding n counterWidth)
      (activeOddUGreaterSelectorProgram n counterWidth low finalBit)
      (activeOddUGreaterSelectorStep n counterWidth low finalBit) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty
    (activeOddUGreaterSelectorGates n counterWidth low finalBit)

theorem activeOddUGreaterSelectorStep_eq_stages
    (n counterWidth : Nat) (low finalBit : Fin n)
    (x : Registers n counterWidth) :
    activeOddUGreaterSelectorStep n counterWidth low finalBit x =
      EncodedBit.GateSpec.step (activeOddCompareStoreGate n counterWidth)
        (EncodedBit.GateSpec.step (activeOddCompareCopyGate n counterWidth)
          (uGreaterSelectorStep n counterWidth finalBit
            (EncodedBit.GateSpec.step
              (activeOddCompareStoreGate n counterWidth)
              (uGreaterSelectorStep n counterWidth finalBit
                (activeOddPathStep n counterWidth low x))))) := by
  unfold activeOddUGreaterSelectorStep activeOddUGreaterSelectorGates
  repeat rw [EncodedBit.GateSpec.stepList_append]
  rfl

/-- If the selected low pair is not odd, the masked comparison selector is
the identity on a clean path/control boundary. -/
theorem activeOddUGreaterSelectorStep_eq_self_of_pair_false
    (n counterWidth : Nat) (low finalBit : Fin n)
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = true)
    (hpath : (pathBit n counterWidth).get x = false)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hpair :
      (((uValueWord n counterWidth).bit low).get x &&
        ((vValueWord n counterWidth).bit low).get x) = false) :
    activeOddUGreaterSelectorStep n counterWidth low finalBit x = x := by
  have hpathStep : activeOddPathStep n counterWidth low x = x :=
    activeOddPathStep_eq_self_of_pair_false n counterWidth low x
      hactive hcontrol hpair
  let first := uGreaterSelectorStep n counterWidth finalBit x
  have hpathFirst : (pathBit n counterWidth).get first = false := by
    dsimp [first]
    rw [uGreaterSelectorStep_get_path, hpath]
  have hstoreFirst :
      EncodedBit.GateSpec.step
          (activeOddCompareStoreGate n counterWidth) first = first :=
    activeOddCompareStoreStep_eq_self_of_path_false
      n counterWidth first hpathFirst
  have hselectorSelf :
      uGreaterSelectorStep n counterWidth finalBit first = x := by
    dsimp [first]
    exact uGreaterSelectorStep_self n counterWidth finalBit x
  have hcopy :
      EncodedBit.GateSpec.step
          (activeOddCompareCopyGate n counterWidth) x = x :=
    activeOddCompareCopyStep_eq_self_of_control_false
      n counterWidth x hcontrol
  have hstore :
      EncodedBit.GateSpec.step
          (activeOddCompareStoreGate n counterWidth) x = x :=
    activeOddCompareStoreStep_eq_self_of_path_false
      n counterWidth x hpath
  rw [activeOddUGreaterSelectorStep_eq_stages, hpathStep]
  change EncodedBit.GateSpec.step (activeOddCompareStoreGate n counterWidth)
      (EncodedBit.GateSpec.step (activeOddCompareCopyGate n counterWidth)
        (uGreaterSelectorStep n counterWidth finalBit
          (EncodedBit.GateSpec.step
            (activeOddCompareStoreGate n counterWidth) first))) = x
  rw [hstoreFirst, hselectorSelf, hcopy, hstore]

/-- An inactive clean route bypasses the complete masked comparison
selector.  The first controlled odd-pair stage is disabled by `active`; the
two unconditional comparison passes then cancel exactly. -/
theorem activeOddUGreaterSelectorStep_eq_self_of_active_false
    (n counterWidth : Nat) (low finalBit : Fin n)
    (x : Registers n counterWidth)
    (hactive : (activeBit n counterWidth).get x = false)
    (hpath : (pathBit n counterWidth).get x = false)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    activeOddUGreaterSelectorStep n counterWidth low finalBit x = x := by
  have hpathStep : activeOddPathStep n counterWidth low x = x := by
    unfold activeOddPathStep
    exact
      EncodedBit.GateSpec.controlledWithWorkStep_eq_self_of_control_false
        (activeBit n counterWidth) (controlBit n counterWidth)
        (oddPairPathGate n counterWidth low)
        (oddPairPathGate_bitDisjoint_active n counterWidth low)
        (oddPairPathGate_bitDisjoint_control n counterWidth low)
        (by
          simpa [activeBit, controlBit] using
            liftCoreBit_liftSharedBit_wire_ne n counterWidth
              (RegisterBits.activeBit n counterWidth)
              (sharedControlBit n counterWidth))
        x hactive
  let first := uGreaterSelectorStep n counterWidth finalBit x
  have hpathFirst : (pathBit n counterWidth).get first = false := by
    dsimp [first]
    rw [uGreaterSelectorStep_get_path, hpath]
  have hstoreFirst :
      EncodedBit.GateSpec.step
          (activeOddCompareStoreGate n counterWidth) first = first :=
    activeOddCompareStoreStep_eq_self_of_path_false
      n counterWidth first hpathFirst
  have hselectorSelf :
      uGreaterSelectorStep n counterWidth finalBit first = x := by
    dsimp [first]
    exact uGreaterSelectorStep_self n counterWidth finalBit x
  have hcopy :
      EncodedBit.GateSpec.step
          (activeOddCompareCopyGate n counterWidth) x = x :=
    activeOddCompareCopyStep_eq_self_of_control_false
      n counterWidth x hcontrol
  have hstore :
      EncodedBit.GateSpec.step
          (activeOddCompareStoreGate n counterWidth) x = x :=
    activeOddCompareStoreStep_eq_self_of_path_false
      n counterWidth x hpath
  rw [activeOddUGreaterSelectorStep_eq_stages, hpathStep]
  change EncodedBit.GateSpec.step (activeOddCompareStoreGate n counterWidth)
      (EncodedBit.GateSpec.step (activeOddCompareCopyGate n counterWidth)
        (uGreaterSelectorStep n counterWidth finalBit
          (EncodedBit.GateSpec.step
            (activeOddCompareStoreGate n counterWidth) first))) = x
  rw [hstoreFirst, hselectorSelf, hcopy, hstore]

/-- The active odd selector preserves every observation outside its four
logical targets and the temporary borrow word. -/
theorem activeOddUGreaterSelectorStep_get_of_preserved
    (n counterWidth : Nat) (low finalBit : Fin n)
    (observed : EncodedBit (encoding n counterWidth))
    (hpath : (pathBit n counterWidth).wire ≠ observed.wire)
    (hcontrol : (controlBit n counterWidth).wire ≠ observed.wire)
    (hcompare : (compareBit n counterWidth).wire ≠ observed.wire)
    (hv : ∀ bit : Fin n,
      ((vValueWord n counterWidth).bit bit).wire ≠ observed.wire)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).wire ≠ observed.wire)
    (x : Registers n counterWidth)
    (hcontrolClean : (controlBit n counterWidth).get x = false) :
    observed.get
        (activeOddUGreaterSelectorStep n counterWidth low finalBit x) =
      observed.get x := by
  rw [activeOddUGreaterSelectorStep_eq_stages]
  rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth observed
    hcontrol]
  rw [activeOddCompareCopyStep_get_of_compare_ne n counterWidth observed
    hcompare]
  rw [uGreaterSelectorStep_get_of_preserved n counterWidth finalBit observed
    hcompare hv hwork]
  rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth observed
    hcontrol]
  rw [uGreaterSelectorStep_get_of_preserved n counterWidth finalBit observed
    hcompare hv hwork]
  exact activeOddPathStep_get_of_path_ne n counterWidth low observed hpath x
    hcontrolClean

/-- The complete masked selector restores the `v` word after its two
comparison passes. -/
theorem activeOddUGreaterSelectorStep_core_v
    (n counterWidth : Nat) (low finalBit : Fin n)
    (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    (activeOddUGreaterSelectorStep n counterWidth low finalBit x).core.v =
      x.core.v := by
  let staged := activeOddPathStep n counterWidth low x
  let first := uGreaterSelectorStep n counterWidth finalBit staged
  let stored := EncodedBit.GateSpec.step
    (activeOddCompareStoreGate n counterWidth) first
  let second := uGreaterSelectorStep n counterWidth finalBit stored
  let copied := EncodedBit.GateSpec.step
    (activeOddCompareCopyGate n counterWidth) second
  let cleared := EncodedBit.GateSpec.step
    (activeOddCompareStoreGate n counterWidth) copied
  have hcopied : copied.core.v = second.core.v := by
    apply word_eq_of_testBit_eq
    intro bit
    have h := activeOddCompareCopyStep_get_of_compare_ne n counterWidth
      ((vValueWord n counterWidth).bit bit)
      (by
        simpa [vValueWord, compareBit, RegisterBits.vValueBit] using
          (liftCoreBit_wire_ne n counterWidth
            (RegisterBits.v_compare_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit))).symm) second
    simpa only [vValueWord_get] using h
  rw [activeOddUGreaterSelectorStep_eq_stages]
  change cleared.core.v = x.core.v
  calc
    cleared.core.v = copied.core.v :=
      activeOddCompareStoreStep_core_v n counterWidth copied
    _ = second.core.v := hcopied
    _ = stored.core.v := uGreaterSelectorStep_core_v
      n counterWidth finalBit stored
    _ = first.core.v := activeOddCompareStoreStep_core_v
      n counterWidth first
    _ = staged.core.v := uGreaterSelectorStep_core_v
      n counterWidth finalBit staged
    _ = x.core.v := activeOddPathStep_core_v
      n counterWidth low x hcontrol

/-- Apart from installing the masked comparison result, the complete selector
preserves the Montgomery--Kaliski core exactly. -/
theorem activeOddUGreaterSelectorStep_core_eq_setCompare
    (n counterWidth : Nat) (low finalBit : Fin n)
    (x : Registers n counterWidth)
    (hcontrol : (controlBit n counterWidth).get x = false) :
    (activeOddUGreaterSelectorStep n counterWidth low finalBit x).core =
      { x.core with compare :=
          (activeOddUGreaterSelectorStep
            n counterWidth low finalBit x).core.compare } := by
  let output := activeOddUGreaterSelectorStep n counterWidth low finalBit x
  have hpreserveCore
      (observed : EncodedBit (registerEncoding n counterWidth))
      (hcompare : (RegisterBits.compareBit n counterWidth).wire ≠ observed.wire)
      (hv : ∀ bit : Fin n,
        (RegisterBits.vValueBit n counterWidth bit).wire ≠ observed.wire) :
      observed.get output.core = observed.get x.core := by
    have h := activeOddUGreaterSelectorStep_get_of_preserved
      n counterWidth low finalBit (liftCoreBit n counterWidth observed)
      (by
        simpa [pathBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth observed
            (sharedPathBit n counterWidth)).symm)
      (by
        simpa [controlBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth observed
            (sharedControlBit n counterWidth)).symm)
      (by
        simpa [compareBit] using liftCoreBit_wire_ne n counterWidth hcompare)
      (by
        intro bit
        simpa [vValueWord, RegisterBits.vValueBit] using
          liftCoreBit_wire_ne n counterWidth (hv bit))
      (by
        intro bit
        exact (liftCoreBit_coefficientCarryWorkBit_wire_ne
          n counterWidth observed bit).symm)
      x hcontrol
    simpa only [output, liftCoreBit_get] using h
  have hu : output.core.u = x.core.u := by
    apply word_eq_of_testBit_eq
    intro bit
    simpa only [RegisterBits.uValueBit_get] using
      hpreserveCore (RegisterBits.uValueBit n counterWidth bit)
        (by
          exact (RegisterBits.u_compare_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)).symm)
        (fun vBit => by
          exact (RegisterBits.u_v_wire_ne n counterWidth
            (WireAddress.littleEndianWire bit)
            (WireAddress.littleEndianWire vBit)).symm)
  have hv : output.core.v = x.core.v := by
    simpa only [output] using activeOddUGreaterSelectorStep_core_v
      n counterWidth low finalBit x hcontrol
  have hsCoeff : output.core.sCoeff = x.core.sCoeff := by
    apply word_eq_of_testBit_eq
    intro bit
    simpa only [RegisterBits.sCoeffValueBit_get] using
      hpreserveCore (RegisterBits.sCoeffValueBit n counterWidth bit)
        (RegisterBits.compare_sCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit))
        (fun vBit => RegisterBits.v_sCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire vBit)
          (WireAddress.littleEndianWire bit))
  have hrCoeff : output.core.rCoeff = x.core.rCoeff := by
    apply word_eq_of_testBit_eq
    intro bit
    simpa only [RegisterBits.rCoeffValueBit_get] using
      hpreserveCore (RegisterBits.rCoeffValueBit n counterWidth bit)
        (RegisterBits.compare_rCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit))
        (fun vBit => RegisterBits.v_rCoeff_wire_ne n counterWidth
          (WireAddress.littleEndianWire vBit)
          (WireAddress.littleEndianWire bit))
  have hscratchA : output.core.scratchA = x.core.scratchA :=
    hpreserveCore (RegisterBits.scratchABit n counterWidth)
      (RegisterBits.compare_scratchA_wire_ne n counterWidth)
      (fun vBit => RegisterBits.v_scratchA_wire_ne n counterWidth
        (WireAddress.littleEndianWire vBit))
  have hscratchB : output.core.scratchB = x.core.scratchB :=
    hpreserveCore (RegisterBits.scratchBBit n counterWidth)
      (RegisterBits.compare_scratchB_wire_ne n counterWidth)
      (fun vBit => RegisterBits.v_scratchB_wire_ne n counterWidth
        (WireAddress.littleEndianWire vBit))
  have hhistory : output.core.history = x.core.history := by
    apply word_eq_of_testBit_eq
    intro bit
    simpa only [RegisterBits.historyBit_get,
      WireAddress.bitIndex_littleEndianWire] using
      hpreserveCore (RegisterBits.historyBit n counterWidth
          (WireAddress.littleEndianWire bit))
        (RegisterBits.compare_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit))
        (fun vBit => RegisterBits.v_history_wire_ne n counterWidth
          (WireAddress.littleEndianWire vBit)
          (WireAddress.littleEndianWire bit))
  have hactive : output.core.active = x.core.active :=
    hpreserveCore (RegisterBits.activeBit n counterWidth)
      (RegisterBits.active_compare_wire_ne n counterWidth).symm
      (fun vBit => (RegisterBits.active_v_wire_ne n counterWidth
        (WireAddress.littleEndianWire vBit)).symm)
  have hcounter : output.core.counter = x.core.counter := by
    apply word_eq_of_testBit_eq
    intro bit
    simpa only [RegisterBits.counterBit_get,
      WireAddress.bitIndex_littleEndianWire] using
      hpreserveCore (RegisterBits.counterBit n counterWidth
          (WireAddress.littleEndianWire bit))
        (RegisterBits.compare_counter_wire_ne n counterWidth
          (WireAddress.littleEndianWire bit))
        (fun vBit => RegisterBits.v_counter_wire_ne n counterWidth
          (WireAddress.littleEndianWire vBit)
          (WireAddress.littleEndianWire bit))
  change output.core = { x.core with compare := output.core.compare }
  cases hOut : output.core
  cases hIn : x.core
  simp_all

/-- Reusable-work endpoint of the active odd-odd selector.  The selector keeps
the odd-route predicate in `path`, installs the masked comparison result, and
restores every temporary bit needed by the following data path. -/
structure ActiveOddUGreaterSelectorCleanEndpoint
    (n counterWidth : Nat) (low finalBit : Fin n)
    (input output : Registers n counterWidth) : Prop where
  compare :
    (compareBit n counterWidth).get output =
      ((((activeBit n counterWidth).get input &&
          ((uValueWord n counterWidth).bit low).get input) &&
          ((vValueWord n counterWidth).bit low).get input) &&
        decide (input.core.v.val < input.core.u.val))
  path :
    (pathBit n counterWidth).get output =
      (((activeBit n counterWidth).get input &&
          ((uValueWord n counterWidth).bit low).get input) &&
        ((vValueWord n counterWidth).bit low).get input)
  control : (controlBit n counterWidth).get output = false
  scratchA : (scratchABit n counterWidth).get output = false
  scratchB : (scratchBBit n counterWidth).get output = false
  carryIn : (coefficientCarryInBit n counterWidth).get output = false
  carryWork : ∀ bit : Fin n,
    (coefficientCarryWorkBit n counterWidth bit).get output = false

/-- On a clean routing/comparison boundary, the literal masked selector reaches
its complete reusable-work endpoint. -/
theorem activeOddUGreaterSelectorStep_cleanEndpoint
    (n counterWidth : Nat) (low finalBit : Fin n)
    (x : Registers n counterWidth)
    (hpath : (pathBit n counterWidth).get x = false)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hcarryIn : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = n) :
    ActiveOddUGreaterSelectorCleanEndpoint n counterWidth low finalBit x
      (activeOddUGreaterSelectorStep n counterWidth low finalBit x) := by
  let p : Bool :=
    (((activeBit n counterWidth).get x &&
      ((uValueWord n counterWidth).bit low).get x) &&
        ((vValueWord n counterWidth).bit low).get x)
  let q : Bool := decide (x.core.v.val < x.core.u.val)
  let staged := activeOddPathStep n counterWidth low x
  let first := uGreaterSelectorStep n counterWidth finalBit staged
  let stored := EncodedBit.GateSpec.step
    (activeOddCompareStoreGate n counterWidth) first
  let second := uGreaterSelectorStep n counterWidth finalBit stored
  let copied := EncodedBit.GateSpec.step
    (activeOddCompareCopyGate n counterWidth) second
  let cleared := EncodedBit.GateSpec.step
    (activeOddCompareStoreGate n counterWidth) copied
  have hstagedPath : (pathBit n counterWidth).get staged = p := by
    dsimp [staged, p]
    rw [activeOddPathStep_get_path_of_clean_control
      n counterWidth low x hcontrol, hpath]
    simp
  have hstagedControl :
      (controlBit n counterWidth).get staged = false := by
    exact activeOddPathStep_get_control_of_clean
      n counterWidth low x hcontrol
  have hstagedCompare :
      (compareBit n counterWidth).get staged = false := by
    calc
      (compareBit n counterWidth).get staged =
          (compareBit n counterWidth).get x :=
        activeOddPathStep_get_of_path_ne n counterWidth low
          (compareBit n counterWidth)
          (by
            simpa [pathBit, compareBit] using
              (liftCoreBit_liftSharedBit_wire_ne n counterWidth
                (RegisterBits.compareBit n counterWidth)
                (sharedPathBit n counterWidth)).symm)
          x hcontrol
      _ = false := hcompare
  have hstagedScratchA :
      (scratchABit n counterWidth).get staged = false := by
    calc
      (scratchABit n counterWidth).get staged =
          (scratchABit n counterWidth).get x :=
        activeOddPathStep_get_of_path_ne n counterWidth low
          (scratchABit n counterWidth)
          (by
            simpa [pathBit, scratchABit] using
              (liftCoreBit_liftSharedBit_wire_ne n counterWidth
                (RegisterBits.scratchABit n counterWidth)
                (sharedPathBit n counterWidth)).symm)
          x hcontrol
      _ = false := hscratchA
  have hstagedWork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get staged = false := by
    intro bit
    calc
      (coefficientCarryWorkBit n counterWidth bit).get staged =
          (coefficientCarryWorkBit n counterWidth bit).get x :=
        activeOddPathStep_get_of_path_ne n counterWidth low
          (coefficientCarryWorkBit n counterWidth bit)
          (pathBit_coefficientCarryWorkBit_wire_ne n counterWidth bit)
          x hcontrol
      _ = false := hwork bit
  have hstagedU : staged.core.u = x.core.u :=
    activeOddPathStep_core_u n counterWidth low x hcontrol
  have hstagedV : staged.core.v = x.core.v :=
    activeOddPathStep_core_v n counterWidth low x hcontrol
  have hstagedPredicate : decide (staged.core.v.val < staged.core.u.val) = q := by
    rw [hstagedU, hstagedV]
  have hfirstCompare : (compareBit n counterWidth).get first = q := by
    dsimp [first]
    rw [uGreaterSelectorStep_get_compare_of_clean_bank
      n counterWidth finalBit staged hstagedScratchA hstagedWork hfinal,
      hstagedCompare, hstagedPredicate]
    simp
  have hfirstPath : (pathBit n counterWidth).get first = p := by
    dsimp [first]
    rw [uGreaterSelectorStep_get_path, hstagedPath]
  have hfirstControl :
      (controlBit n counterWidth).get first = false := by
    dsimp [first]
    rw [uGreaterSelectorStep_get_control, hstagedControl]
  have hfirstScratchA :
      (scratchABit n counterWidth).get first = false := by
    dsimp [first]
    rw [uGreaterSelectorStep_get_scratchA, hstagedScratchA]
  have hfirstWork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get first = false := by
    intro bit
    dsimp [first]
    rw [uGreaterSelectorStep_get_coefficientCarryWorkBit, hstagedWork bit]
  have hstoredCompare : (compareBit n counterWidth).get stored = q := by
    dsimp [stored]
    rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth
      (compareBit n counterWidth)]
    · exact hfirstCompare
    · simpa [compareBit, controlBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedControlBit n counterWidth)).symm
  have hstoredPath : (pathBit n counterWidth).get stored = p := by
    dsimp [stored]
    rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth
      (pathBit n counterWidth) (pathBit_controlBit_wire_ne
        n counterWidth).symm]
    exact hfirstPath
  have hstoredControl :
      (controlBit n counterWidth).get stored = (p && q) := by
    dsimp [stored]
    rw [activeOddCompareStoreStep_get_control, hfirstControl,
      hfirstPath, hfirstCompare]
    simp
  have hstoredScratchA :
      (scratchABit n counterWidth).get stored = false := by
    dsimp [stored]
    rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth
      (scratchABit n counterWidth)]
    · exact hfirstScratchA
    · simpa [scratchABit, controlBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedControlBit n counterWidth)).symm
  have hstoredWork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get stored = false := by
    intro bit
    dsimp [stored]
    rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth
      (coefficientCarryWorkBit n counterWidth bit)
      (controlBit_coefficientCarryWorkBit_wire_ne n counterWidth bit),
      hfirstWork bit]
  have hfirstU : first.core.u = staged.core.u :=
    uGreaterSelectorStep_core_u n counterWidth finalBit staged
  have hfirstV : first.core.v = staged.core.v :=
    uGreaterSelectorStep_core_v n counterWidth finalBit staged
  have hstoredU : stored.core.u = first.core.u :=
    activeOddCompareStoreStep_core_u n counterWidth first
  have hstoredV : stored.core.v = first.core.v :=
    activeOddCompareStoreStep_core_v n counterWidth first
  have hstoredPredicate : decide (stored.core.v.val < stored.core.u.val) = q := by
    rw [hstoredU, hstoredV, hfirstU, hfirstV, hstagedU, hstagedV]
  have hsecondCompare :
      (compareBit n counterWidth).get second = false := by
    dsimp [second]
    rw [uGreaterSelectorStep_get_compare_of_clean_bank
      n counterWidth finalBit stored hstoredScratchA hstoredWork hfinal,
      hstoredCompare, hstoredPredicate]
    cases q <;> rfl
  have hsecondPath : (pathBit n counterWidth).get second = p := by
    dsimp [second]
    rw [uGreaterSelectorStep_get_path, hstoredPath]
  have hsecondControl :
      (controlBit n counterWidth).get second = (p && q) := by
    dsimp [second]
    rw [uGreaterSelectorStep_get_control, hstoredControl]
  have hcopiedCompare :
      (compareBit n counterWidth).get copied = (p && q) := by
    dsimp [copied]
    rw [activeOddCompareCopyStep_get_compare, hsecondCompare,
      hsecondControl]
    simp
  have hcopiedPath : (pathBit n counterWidth).get copied = p := by
    dsimp [copied]
    rw [activeOddCompareCopyStep_get_of_compare_ne n counterWidth
      (pathBit n counterWidth)]
    · exact hsecondPath
    · simpa [compareBit, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedPathBit n counterWidth)
  have hcopiedControl :
      (controlBit n counterWidth).get copied = (p && q) := by
    dsimp [copied]
    rw [activeOddCompareCopyStep_get_of_compare_ne n counterWidth
      (controlBit n counterWidth)]
    · exact hsecondControl
    · simpa [compareBit, controlBit] using
        liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedControlBit n counterWidth)
  have hclearedCompare :
      (compareBit n counterWidth).get cleared = (p && q) := by
    dsimp [cleared]
    rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth
      (compareBit n counterWidth)]
    · exact hcopiedCompare
    · simpa [compareBit, controlBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth)
          (sharedControlBit n counterWidth)).symm
  have hclearedControl :
      (controlBit n counterWidth).get cleared = false := by
    dsimp [cleared]
    rw [activeOddCompareStoreStep_get_control, hcopiedControl,
      hcopiedPath, hcopiedCompare]
    cases p <;> cases q <;> rfl
  have hclearedPath : (pathBit n counterWidth).get cleared = p := by
    dsimp [cleared]
    rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth
      (pathBit n counterWidth) (pathBit_controlBit_wire_ne
        n counterWidth).symm]
    exact hcopiedPath
  have hsecondScratchA :
      (scratchABit n counterWidth).get second = false := by
    dsimp [second]
    rw [uGreaterSelectorStep_get_scratchA, hstoredScratchA]
  have hcopiedScratchA :
      (scratchABit n counterWidth).get copied = false := by
    dsimp [copied]
    rw [activeOddCompareCopyStep_get_of_compare_ne n counterWidth
      (scratchABit n counterWidth)]
    · exact hsecondScratchA
    · simpa [compareBit, scratchABit] using
        liftCoreBit_wire_ne n counterWidth
          (RegisterBits.compare_scratchA_wire_ne n counterWidth)
  have hclearedScratchA :
      (scratchABit n counterWidth).get cleared = false := by
    dsimp [cleared]
    rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth
      (scratchABit n counterWidth)]
    · exact hcopiedScratchA
    · simpa [scratchABit, controlBit] using
        (liftCoreBit_liftSharedBit_wire_ne n counterWidth
          (RegisterBits.scratchABit n counterWidth)
          (sharedControlBit n counterWidth)).symm
  have hsecondWork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get second = false := by
    intro bit
    dsimp [second]
    rw [uGreaterSelectorStep_get_coefficientCarryWorkBit, hstoredWork bit]
  have hcopiedWork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get copied = false := by
    intro bit
    dsimp [copied]
    rw [activeOddCompareCopyStep_get_of_compare_ne n counterWidth
      (coefficientCarryWorkBit n counterWidth bit)]
    · exact hsecondWork bit
    · simpa [compareBit] using
        liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
          (RegisterBits.compareBit n counterWidth) bit
  have hclearedWork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get cleared = false := by
    intro bit
    dsimp [cleared]
    rw [activeOddCompareStoreStep_get_of_control_ne n counterWidth
      (coefficientCarryWorkBit n counterWidth bit)
      (controlBit_coefficientCarryWorkBit_wire_ne n counterWidth bit),
      hcopiedWork bit]
  have hclearedScratchB :
      (scratchBBit n counterWidth).get cleared = false := by
    have hpres := activeOddUGreaterSelectorStep_get_of_preserved
      n counterWidth low finalBit (scratchBBit n counterWidth)
      (by
        simpa [pathBit, scratchBBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchBBit n counterWidth)
            (sharedPathBit n counterWidth)).symm)
      (by
        simpa [controlBit, scratchBBit] using
          (liftCoreBit_liftSharedBit_wire_ne n counterWidth
            (RegisterBits.scratchBBit n counterWidth)
            (sharedControlBit n counterWidth)).symm)
      (by
        simpa [compareBit, scratchBBit] using
          liftCoreBit_wire_ne n counterWidth
            (RegisterBits.compare_scratchB_wire_ne n counterWidth))
      (by
        intro bit
        simpa [vValueWord, scratchBBit, RegisterBits.vValueBit] using
          liftCoreBit_wire_ne n counterWidth
            (RegisterBits.v_scratchB_wire_ne n counterWidth
              (WireAddress.littleEndianWire bit)))
      (by
        intro bit
        simpa [scratchBBit] using
          (liftCoreBit_coefficientCarryWorkBit_wire_ne n counterWidth
            (RegisterBits.scratchBBit n counterWidth) bit).symm)
      x hcontrol
    rw [activeOddUGreaterSelectorStep_eq_stages] at hpres
    exact hpres.trans hscratchB
  have hclearedCarryIn :
      (coefficientCarryInBit n counterWidth).get cleared = false := by
    have hpres := activeOddUGreaterSelectorStep_get_of_preserved
      n counterWidth low finalBit (coefficientCarryInBit n counterWidth)
      (pathBit_coefficientCarryInBit_wire_ne n counterWidth)
      (controlBit_coefficientCarryInBit_wire_ne n counterWidth)
      (by
        simpa [compareBit] using
          liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
            (RegisterBits.compareBit n counterWidth))
      (by
        intro bit
        simpa [vValueWord, RegisterBits.vValueBit] using
          liftCoreBit_coefficientCarryInBit_wire_ne n counterWidth
            (RegisterBits.vValueBit n counterWidth bit))
      (fun bit => (coefficientCarryInBit_coefficientCarryWorkBit_wire_ne
        n counterWidth bit).symm)
      x hcontrol
    rw [activeOddUGreaterSelectorStep_eq_stages] at hpres
    exact hpres.trans hcarryIn
  refine
    { compare := ?_
      path := ?_
      control := ?_
      scratchA := ?_
      scratchB := ?_
      carryIn := ?_
      carryWork := ?_ }
  · rw [activeOddUGreaterSelectorStep_eq_stages]
    exact hclearedCompare
  · rw [activeOddUGreaterSelectorStep_eq_stages]
    exact hclearedPath
  · rw [activeOddUGreaterSelectorStep_eq_stages]
    exact hclearedControl
  · rw [activeOddUGreaterSelectorStep_eq_stages]
    exact hclearedScratchA
  · rw [activeOddUGreaterSelectorStep_eq_stages]
    exact hclearedScratchB
  · rw [activeOddUGreaterSelectorStep_eq_stages]
    exact hclearedCarryIn
  · intro bit
    rw [activeOddUGreaterSelectorStep_eq_stages]
    exact hclearedWork bit

/-- The comparison projection of the complete clean selector endpoint. -/
theorem activeOddUGreaterSelectorStep_get_compare_clean
    (n counterWidth : Nat) (low finalBit : Fin n)
    (x : Registers n counterWidth)
    (hpath : (pathBit n counterWidth).get x = false)
    (hcontrol : (controlBit n counterWidth).get x = false)
    (hcompare : (compareBit n counterWidth).get x = false)
    (hscratchA : (scratchABit n counterWidth).get x = false)
    (hscratchB : (scratchBBit n counterWidth).get x = false)
    (hcarryIn : (coefficientCarryInBit n counterWidth).get x = false)
    (hwork : ∀ bit : Fin n,
      (coefficientCarryWorkBit n counterWidth bit).get x = false)
    (hfinal : finalBit.val + 1 = n) :
    (compareBit n counterWidth).get
        (activeOddUGreaterSelectorStep n counterWidth low finalBit x) =
      ((((activeBit n counterWidth).get x &&
          ((uValueWord n counterWidth).bit low).get x) &&
          ((vValueWord n counterWidth).bit low).get x) &&
        decide (x.core.v.val < x.core.u.val)) :=
  (activeOddUGreaterSelectorStep_cleanEndpoint n counterWidth low finalBit x
    hpath hcontrol hcompare hscratchA hscratchB hcarryIn hwork hfinal).compare

theorem activeOddUGreaterSelectorGates_length
    (n counterWidth : Nat) (low finalBit : Fin n) :
    (activeOddUGreaterSelectorGates n counterWidth low finalBit).length =
      20 * n + 8 := by
  simp only [activeOddUGreaterSelectorGates, List.length_append,
    List.length_cons, List.length_nil, activeOddPathGates_length,
    uGreaterSelectorGates_length]
  omega

theorem activeOddUGreaterSelectorGates_xMultiplicity_sum
    (n counterWidth : Nat) (low finalBit : Fin n) :
    ((activeOddUGreaterSelectorGates n counterWidth low finalBit).map
      EncodedBit.GateSpec.xMultiplicity).sum = 8 * n := by
  simp [activeOddUGreaterSelectorGates, activeOddCompareStoreGate,
    activeOddCompareCopyGate,
    uGreaterSelectorGates_xMultiplicity_sum]
  omega

theorem activeOddUGreaterSelectorGates_cnotMultiplicity_sum
    (n counterWidth : Nat) (low finalBit : Fin n) :
    ((activeOddUGreaterSelectorGates n counterWidth low finalBit).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 3 := by
  simp [activeOddUGreaterSelectorGates, activeOddCompareStoreGate,
    activeOddCompareCopyGate,
    uGreaterSelectorGates_cnotMultiplicity_sum]

theorem activeOddUGreaterSelectorGates_toffoliMultiplicity_sum
    (n counterWidth : Nat) (low finalBit : Fin n) :
    ((activeOddUGreaterSelectorGates n counterWidth low finalBit).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 12 * n + 5 := by
  simp [activeOddUGreaterSelectorGates, activeOddCompareStoreGate,
    activeOddCompareCopyGate,
    uGreaterSelectorGates_toffoliMultiplicity_sum]
  omega

end Compact

end
end MK
end MAU.Inversion
end QuantumAlg

end
