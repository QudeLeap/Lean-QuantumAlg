/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.Arithmetic.Comparator

/-!
# A cleanup-aware fixed-layout comparator circuit

This module turns the reusable subtract-borrow chain into one concrete
base-gate comparator.  The circuit computes the final borrow into an output
flag and then reverses the borrow chain, so every work bit is returned clean.
The exact same folded program supplies the semantic endpoint and all resource
projections.
-/

section

namespace QuantumAlg
namespace Comparator
namespace CleanCircuit

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Canonical `(n + 1)`-bit word used by the general modular-adder route. -/
abbrev Word (n : Nat) := Fin (2 ^ (n + 1))

/-- Read-only comparator inputs together with an xor-output flag. -/
structure Data (n : Nat) where
  /-- Left read-only input word. -/
  left : Word n
  /-- Right read-only input word. -/
  right : Word n
  /-- Xor-output bit receiving the comparison result. -/
  flag : Bool
deriving DecidableEq

/-- Clean incoming borrow and the borrow-chain workspace. -/
structure Work (n : Nat) where
  /-- Clean incoming-borrow bit. -/
  initialBorrow : Bool
  /-- Borrow-chain workspace word. -/
  borrow : Word n
deriving DecidableEq

/-- Complete semantic carrier for the fixed comparator layout. -/
abbrev Carrier (n : Nat) := Data n × Work n

/-- Tuple presentation used by the product encoding of comparator data. -/
def dataTupleEquiv (n : Nat) :
    Data n ≃ Word n × (Word n × Bool) where
  toFun x := (x.left, (x.right, x.flag))
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨left, right, flag⟩; rfl

/-- Tuple presentation used by the product encoding of comparator work. -/
def workTupleEquiv (n : Nat) : Work n ≃ Bool × Word n where
  toFun x := (x.initialBorrow, x.borrow)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨initialBorrow, borrow⟩; rfl

/-- Exact identity encoding of one `(n + 1)`-bit word. -/
def wordEncoding (n : Nat) : BinaryLabelEncoding (Word n) :=
  BinaryLabelEncoding.finIdentity (n + 1)

/-- Product encoding before transporting back to the `Data` structure. -/
def dataTupleEncoding (n : Nat) :
    BinaryLabelEncoding (Word n × (Word n × Bool)) :=
  BinaryLabelEncoding.prod (wordEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding n) BinaryLabelEncoding.bool)

/-- Fixed encoding of the two words and output flag. -/
def dataEncoding (n : Nat) : BinaryLabelEncoding (Data n) :=
  (dataTupleEncoding n).relabel (dataTupleEquiv n)

/-- Product encoding before transporting back to the `Work` structure. -/
def workTupleEncoding (n : Nat) : BinaryLabelEncoding (Bool × Word n) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool (wordEncoding n)

/-- Fixed encoding of the incoming borrow and borrow workspace. -/
def workEncoding (n : Nat) : BinaryLabelEncoding (Work n) :=
  (workTupleEncoding n).relabel (workTupleEquiv n)

/-- Full fixed comparator encoding. -/
def encoding (n : Nat) : BinaryLabelEncoding (Carrier n) :=
  BinaryLabelEncoding.prod (dataEncoding n) (workEncoding n)

/-- Little-endian value bit of a canonical word. -/
def wordValueBit (n : Nat) (bit : Fin (n + 1)) :
    EncodedBit (wordEncoding n) :=
  BinaryLabelEncoding.finIdentityBit (n + 1)
    (WireAddress.littleEndianWire bit)

/-- Left-word bit in the tuple presentation of comparator data. -/
def tupleLeftBit (n : Nat) (bit : Fin (n + 1)) :
    EncodedBit (dataTupleEncoding n) :=
  BinaryLabelEncoding.prodLeftBit (wordEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding n) BinaryLabelEncoding.bool)
    (wordValueBit n bit)

/-- Right-word bit in the tuple presentation of comparator data. -/
def tupleRightBit (n : Nat) (bit : Fin (n + 1)) :
    EncodedBit (dataTupleEncoding n) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding n) BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodLeftBit (wordEncoding n)
      BinaryLabelEncoding.bool (wordValueBit n bit))

/-- Output-flag bit in the tuple presentation of comparator data. -/
def tupleFlagBit (n : Nat) : EncodedBit (dataTupleEncoding n) :=
  BinaryLabelEncoding.prodRightBit (wordEncoding n)
    (BinaryLabelEncoding.prod (wordEncoding n) BinaryLabelEncoding.bool)
    (BinaryLabelEncoding.prodRightBit (wordEncoding n)
      BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit)

/-- Left-word bit after transporting the tuple encoding to `Data`. -/
def dataLeftBit (n : Nat) (bit : Fin (n + 1)) :
    EncodedBit (dataEncoding n) :=
  (tupleLeftBit n bit).relabel (dataTupleEquiv n)

/-- Right-word bit after transporting the tuple encoding to `Data`. -/
def dataRightBit (n : Nat) (bit : Fin (n + 1)) :
    EncodedBit (dataEncoding n) :=
  (tupleRightBit n bit).relabel (dataTupleEquiv n)

/-- Output-flag bit after transporting the tuple encoding to `Data`. -/
def dataFlagBit (n : Nat) : EncodedBit (dataEncoding n) :=
  (tupleFlagBit n).relabel (dataTupleEquiv n)

/-- Incoming-borrow bit in the tuple presentation of comparator work. -/
def tupleInitialBorrowBit (n : Nat) :
    EncodedBit (workTupleEncoding n) :=
  BinaryLabelEncoding.prodLeftBit BinaryLabelEncoding.bool (wordEncoding n)
    BinaryLabelEncoding.boolBit

/-- Borrow-work bit in the tuple presentation of comparator work. -/
def tupleBorrowBit (n : Nat) (bit : Fin (n + 1)) :
    EncodedBit (workTupleEncoding n) :=
  BinaryLabelEncoding.prodRightBit BinaryLabelEncoding.bool (wordEncoding n)
    (wordValueBit n bit)

/-- Incoming-borrow bit after transporting the tuple encoding to `Work`. -/
def workInitialBorrowBit (n : Nat) : EncodedBit (workEncoding n) :=
  (tupleInitialBorrowBit n).relabel (workTupleEquiv n)

/-- Borrow-work bit after transporting the tuple encoding to `Work`. -/
def workBorrowBit (n : Nat) (bit : Fin (n + 1)) :
    EncodedBit (workEncoding n) :=
  (tupleBorrowBit n bit).relabel (workTupleEquiv n)

/-- Little-endian value bit in the left input word. -/
def leftBit (n : Nat) (bit : Fin (n + 1)) : EncodedBit (encoding n) :=
  BinaryLabelEncoding.prodLeftBit (dataEncoding n) (workEncoding n)
    (dataLeftBit n bit)

/-- Little-endian value bit in the right input word. -/
def rightBit (n : Nat) (bit : Fin (n + 1)) : EncodedBit (encoding n) :=
  BinaryLabelEncoding.prodLeftBit (dataEncoding n) (workEncoding n)
    (dataRightBit n bit)

/-- Output flag bit. -/
def flagBit (n : Nat) : EncodedBit (encoding n) :=
  BinaryLabelEncoding.prodLeftBit (dataEncoding n) (workEncoding n)
    (dataFlagBit n)

/-- Clean incoming-borrow bit. -/
def initialBorrowBit (n : Nat) : EncodedBit (encoding n) :=
  BinaryLabelEncoding.prodRightBit (dataEncoding n) (workEncoding n)
    (workInitialBorrowBit n)

/-- Little-endian borrow-work bit. -/
def borrowBit (n : Nat) (bit : Fin (n + 1)) : EncodedBit (encoding n) :=
  BinaryLabelEncoding.prodRightBit (dataEncoding n) (workEncoding n)
    (workBorrowBit n bit)

/-- Left input word lens. -/
def leftWord (n : Nat) : EncodedBit.Word (encoding n) (n + 1) where
  bit := leftBit n

/-- Right input word lens. -/
def rightWord (n : Nat) : EncodedBit.Word (encoding n) (n + 1) where
  bit := rightBit n

/-- Borrow-work word lens. -/
def borrowWord (n : Nat) : EncodedBit.Word (encoding n) (n + 1) where
  bit := borrowBit n

@[simp] lemma leftBit_get (n : Nat) (bit : Fin (n + 1))
    (x : Carrier n) :
    (leftBit n bit).get x = x.1.left.val.testBit bit.val := by
  simp [leftBit, dataLeftBit, tupleLeftBit, wordValueBit, dataTupleEquiv,
    wordEncoding, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    EncodedBit.relabel, WireAddress.bitIndex_littleEndianWire]

@[simp] lemma rightBit_get (n : Nat) (bit : Fin (n + 1))
    (x : Carrier n) :
    (rightBit n bit).get x = x.1.right.val.testBit bit.val := by
  simp [rightBit, dataRightBit, tupleRightBit, wordValueBit, dataTupleEquiv,
    wordEncoding, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    WireAddress.bitIndex_littleEndianWire]

@[simp] lemma flagBit_get (n : Nat) (x : Carrier n) :
    (flagBit n).get x = x.1.flag := by
  simp [flagBit, dataFlagBit, tupleFlagBit, dataTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel, BinaryLabelEncoding.boolBit]

@[simp] lemma initialBorrowBit_get (n : Nat) (x : Carrier n) :
    (initialBorrowBit n).get x = x.2.initialBorrow := by
  simp [initialBorrowBit, workInitialBorrowBit, tupleInitialBorrowBit,
    workTupleEquiv, BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit, EncodedBit.relabel,
    BinaryLabelEncoding.boolBit]

@[simp] lemma borrowBit_get (n : Nat) (bit : Fin (n + 1))
    (x : Carrier n) :
    (borrowBit n bit).get x = x.2.borrow.val.testBit bit.val := by
  simp [borrowBit, workBorrowBit, tupleBorrowBit, wordValueBit,
    workTupleEquiv, wordEncoding, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    EncodedBit.relabel, WireAddress.bitIndex_littleEndianWire]

/-- Flipping the output lens changes only the semantic flag. -/
lemma flagBit_flip (n : Nat) (x : Carrier n) :
    (flagBit n).flip x = ({ x.1 with flag := !x.1.flag }, x.2) := by
  simp [flagBit, dataFlagBit, tupleFlagBit, dataTupleEquiv,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    EncodedBit.relabel, BinaryLabelEncoding.boolBit]

@[simp] lemma leftBit_wire_val (n : Nat) (i : Fin (n + 1)) :
    (leftBit n i).wire.val = n - i.val := by
  simp [leftBit, dataLeftBit, tupleLeftBit, wordValueBit,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    EncodedBit.relabel, WireAddress.littleEndianWire,
    WireAddress.bitIndex]

@[simp] lemma rightBit_wire_val (n : Nat) (i : Fin (n + 1)) :
    (rightBit n i).wire.val = (n + 1) + (n - i.val) := by
  simp [rightBit, dataRightBit, tupleRightBit, wordValueBit, wordEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit,
    BinaryLabelEncoding.finIdentity_width, EncodedBit.relabel,
    WireAddress.littleEndianWire, WireAddress.bitIndex]

@[simp] lemma flagBit_wire_val (n : Nat) :
    (flagBit n).wire.val = 2 * (n + 1) := by
  simp [flagBit, dataFlagBit, tupleFlagBit, wordEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel]
  omega

@[simp] lemma initialBorrowBit_wire_val (n : Nat) :
    (initialBorrowBit n).wire.val = 2 * (n + 1) + 1 := by
  simp [initialBorrowBit, workInitialBorrowBit, tupleInitialBorrowBit,
    encoding, dataEncoding, dataTupleEncoding, wordEncoding,
    BinaryLabelEncoding.prodLeftBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire, BinaryLabelEncoding.prodRightWire,
    EncodedBit.relabel]
  omega

@[simp] lemma borrowBit_wire_val (n : Nat) (i : Fin (n + 1)) :
    (borrowBit n i).wire.val = 2 * (n + 1) + 2 + (n - i.val) := by
  simp [borrowBit, workBorrowBit, tupleBorrowBit, wordValueBit, encoding,
    dataEncoding, dataTupleEncoding, workEncoding, workTupleEncoding,
    wordEncoding, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire, BinaryLabelEncoding.finIdentityBit,
    BinaryLabelEncoding.ofEquivBit, EncodedBit.relabel,
    WireAddress.littleEndianWire, WireAddress.bitIndex]
  omega

lemma left_left_wire_ne (n : Nat) (i j : Fin (n + 1))
    (h : i ≠ j) : (leftBit n i).wire ≠ (leftBit n j).wire := by
  intro heq
  apply h
  apply Fin.ext
  have hv := congrArg Fin.val heq
  simp only [leftBit_wire_val] at hv
  omega

lemma right_right_wire_ne (n : Nat) (i j : Fin (n + 1))
    (h : i ≠ j) : (rightBit n i).wire ≠ (rightBit n j).wire := by
  intro heq
  apply h
  apply Fin.ext
  have hv := congrArg Fin.val heq
  simp only [rightBit_wire_val] at hv
  omega

lemma borrow_borrow_wire_ne (n : Nat) (i j : Fin (n + 1))
    (h : i ≠ j) : (borrowBit n i).wire ≠ (borrowBit n j).wire := by
  intro heq
  apply h
  apply Fin.ext
  have hv := congrArg Fin.val heq
  simp only [borrowBit_wire_val] at hv
  omega

lemma left_right_wire_ne (n : Nat) (i j : Fin (n + 1)) :
    (leftBit n i).wire ≠ (rightBit n j).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [leftBit_wire_val, rightBit_wire_val] at hv
  have hi := i.isLt
  omega

lemma left_initial_wire_ne (n : Nat) (i : Fin (n + 1)) :
    (leftBit n i).wire ≠ (initialBorrowBit n).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [leftBit_wire_val, initialBorrowBit_wire_val] at hv
  have hi := i.isLt
  omega

lemma right_initial_wire_ne (n : Nat) (i : Fin (n + 1)) :
    (rightBit n i).wire ≠ (initialBorrowBit n).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [rightBit_wire_val, initialBorrowBit_wire_val] at hv
  have hi := i.isLt
  omega

lemma left_borrow_wire_ne (n : Nat) (i j : Fin (n + 1)) :
    (leftBit n i).wire ≠ (borrowBit n j).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [leftBit_wire_val, borrowBit_wire_val] at hv
  have hi := i.isLt
  omega

lemma right_borrow_wire_ne (n : Nat) (i j : Fin (n + 1)) :
    (rightBit n i).wire ≠ (borrowBit n j).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [rightBit_wire_val, borrowBit_wire_val] at hv
  have hi := i.isLt
  omega

lemma initial_borrow_wire_ne (n : Nat) (j : Fin (n + 1)) :
    (initialBorrowBit n).wire ≠ (borrowBit n j).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [initialBorrowBit_wire_val, borrowBit_wire_val] at hv
  omega

lemma left_flag_wire_ne (n : Nat) (i : Fin (n + 1)) :
    (leftBit n i).wire ≠ (flagBit n).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [leftBit_wire_val, flagBit_wire_val] at hv
  have hi := i.isLt
  omega

lemma right_flag_wire_ne (n : Nat) (i : Fin (n + 1)) :
    (rightBit n i).wire ≠ (flagBit n).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [rightBit_wire_val, flagBit_wire_val] at hv
  have hi := i.isLt
  omega

lemma initial_flag_wire_ne (n : Nat) :
    (initialBorrowBit n).wire ≠ (flagBit n).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [initialBorrowBit_wire_val, flagBit_wire_val] at hv
  omega

lemma borrow_flag_wire_ne (n : Nat) (i : Fin (n + 1)) :
    (borrowBit n i).wire ≠ (flagBit n).wire := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [borrowBit_wire_val, flagBit_wire_val] at hv
  omega

/-- Borrow-chain layout used by the concrete comparator. -/
def borrowLayout (n : Nat) :
    BorrowWorkLayout (encoding := encoding n) (n + 1) where
  minuend := leftWord n
  subtrahend := rightWord n
  initialBorrow := initialBorrowBit n
  workBorrow := borrowWord n
  minuendMinuend_ne := left_left_wire_ne n
  subtrahendSubtrahend_ne := right_right_wire_ne n
  minuendSubtrahend_ne := left_right_wire_ne n
  minuendInitialBorrow_ne := left_initial_wire_ne n
  subtrahendInitialBorrow_ne := right_initial_wire_ne n
  minuendWork_ne := left_borrow_wire_ne n
  subtrahendWork_ne := right_borrow_wire_ne n
  initialBorrowWork_ne := initial_borrow_wire_ne n
  workWork_ne := borrow_borrow_wire_ne n

/-- Fully clean comparator work state. -/
def cleanWork (n : Nat) : Work n := ⟨false, 0⟩

/-- Semantic xor-update performed by the clean comparator. -/
def compareIntoFlag {n : Nat} (x : Data n) : Data n :=
  { x with flag := x.flag ^^ decide (x.left.val < x.right.val) }

/-- Forward borrow-chain gate list. -/
def borrowGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  BorrowWorkLayout.borrowStage (borrowLayout n)

/-- Final work-borrow bit carrying the full-word comparison. -/
def finalBorrowIndex (n : Nat) : Fin (n + 1) := Fin.last n

/-- Copy the final borrow into the external xor-output flag. -/
def copyFlagGate (n : Nat) : EncodedBit.GateSpec (encoding n) :=
  EncodedBit.GateSpec.cnot (borrowBit n (finalBorrowIndex n)) (flagBit n)
    (borrow_flag_wire_ne n (finalBorrowIndex n))

/-- Compute-copy-uncompute gate list for the comparator. -/
def compareGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  borrowGates n ++ [copyFlagGate n] ++ (borrowGates n).reverse

/-- Concrete fixed-layout base-gate comparator program. -/
def compareProgram (n : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding n).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty (compareGates n)

/-- Exact semantic action of the comparator program. -/
def compareStep (n : Nat) : Carrier n → Carrier n :=
  EncodedBit.GateSpec.stepList (compareGates n)

/-- The folded comparator gate list realizes its exact semantic action. -/
lemma compareProgram_realizes (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (compareProgram n) environment (compareStep n) :=
  EncodedBit.GateSpec.realizesList (QubitLayout.canonical _) .empty (compareGates n) environment

lemma borrowGates_flag_disjoint (n : Nat) :
    ∀ gate, gate ∈ borrowGates n →
      EncodedBit.GateSpec.bitDisjoint (flagBit n) gate := by
  exact BorrowWorkLayout.borrowStage_bitDisjoint (borrowLayout n) (flagBit n)
    (left_flag_wire_ne n) (right_flag_wire_ne n) (initial_flag_wire_ne n)
    (borrow_flag_wire_ne n)

/-- On clean work, the forward chain's final work bit is ordinary comparison. -/
lemma borrowGates_finalBorrow_get (n : Nat) (x : Data n) :
    (borrowBit n (finalBorrowIndex n)).get
        (EncodedBit.GateSpec.stepList (borrowGates n) (x, cleanWork n)) =
      decide (x.left.val < x.right.val) := by
  change
    (borrowBit n (finalBorrowIndex n)).get
        (BorrowWorkLayout.borrowStageStep (borrowLayout n)
          (x, cleanWork n)) =
      decide (x.left.val < x.right.val)
  rw [BorrowWorkLayout.borrowStage_stepList_eq_indexStep]
  have hborrow :=
    BorrowWorkLayout.borrowStageIndexStep_get_workBorrow_natBorrow
      (borrowLayout n) x.left.val x.right.val (finalBorrowIndex n)
      (x, cleanWork n)
      (by intro k; simp [borrowLayout, borrowWord, cleanWork])
      (by simp [borrowLayout, cleanWork])
      (by intro k; simp [borrowLayout, leftWord])
      (by intro k; simp [borrowLayout, rightWord])
  have hborrow' :
      (borrowBit n (finalBorrowIndex n)).get
          (BorrowWorkLayout.borrowStageIndexStep (borrowLayout n)
            (x, cleanWork n)) =
        natBorrow x.left.val x.right.val ((finalBorrowIndex n).val + 1) := by
    simpa [borrowLayout, borrowWord] using hborrow
  rw [hborrow']
  simpa [finalBorrowIndex] using
    natBorrow_eq_decide_lt_of_lt_two_pow x.left.isLt x.right.isLt

/-- The exact program updates only the flag and restores all borrow work. -/
lemma compareStep_clean (n : Nat) (x : Data n) :
    compareStep n (x, cleanWork n) = (compareIntoFlag x, cleanWork n) := by
  have hreverseDisjoint :
      ∀ gate, gate ∈ (borrowGates n).reverse →
        EncodedBit.GateSpec.bitDisjoint (flagBit n) gate := by
    intro gate hgate
    exact borrowGates_flag_disjoint n gate (by simpa using hgate)
  have hborrow := borrowGates_finalBorrow_get n x
  unfold compareStep compareGates
  rw [EncodedBit.GateSpec.stepList_append]
  rw [EncodedBit.GateSpec.stepList_append]
  change
    EncodedBit.GateSpec.stepList (borrowGates n).reverse
        ((copyFlagGate n).step
          (EncodedBit.GateSpec.stepList (borrowGates n) (x, cleanWork n))) =
      (compareIntoFlag x, cleanWork n)
  cases hcmp : decide (x.left.val < x.right.val) with
  | false =>
      have hcontrol :
          (borrowBit n (finalBorrowIndex n)).get
              (EncodedBit.GateSpec.stepList (borrowGates n)
                (x, cleanWork n)) = false := by
        rw [hborrow, hcmp]
      rw [show
        (copyFlagGate n).step
            (EncodedBit.GateSpec.stepList (borrowGates n) (x, cleanWork n)) =
          EncodedBit.GateSpec.stepList (borrowGates n) (x, cleanWork n) by
            change
              (if (borrowBit n (finalBorrowIndex n)).get
                    (EncodedBit.GateSpec.stepList (borrowGates n)
                      (x, cleanWork n))
                then (flagBit n).flip
                  (EncodedBit.GateSpec.stepList (borrowGates n)
                    (x, cleanWork n))
                else EncodedBit.GateSpec.stepList (borrowGates n)
                  (x, cleanWork n)) = _
            rw [hcontrol]
            rfl]
      rw [EncodedBit.GateSpec.stepList_reverse_stepList]
      cases x with
      | mk left right flag =>
          cases flag <;> simp_all [compareIntoFlag]
  | true =>
      have hcontrol :
          (borrowBit n (finalBorrowIndex n)).get
              (EncodedBit.GateSpec.stepList (borrowGates n)
                (x, cleanWork n)) = true := by
        rw [hborrow, hcmp]
      rw [show
        (copyFlagGate n).step
            (EncodedBit.GateSpec.stepList (borrowGates n) (x, cleanWork n)) =
          (flagBit n).flip
            (EncodedBit.GateSpec.stepList (borrowGates n) (x, cleanWork n)) by
            change
              (if (borrowBit n (finalBorrowIndex n)).get
                    (EncodedBit.GateSpec.stepList (borrowGates n)
                      (x, cleanWork n))
                then (flagBit n).flip
                  (EncodedBit.GateSpec.stepList (borrowGates n)
                    (x, cleanWork n))
                else EncodedBit.GateSpec.stepList (borrowGates n)
                  (x, cleanWork n)) = _
            rw [hcontrol]
            rfl]
      rw [EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
        (borrowGates n).reverse (flagBit n) hreverseDisjoint]
      rw [EncodedBit.GateSpec.stepList_reverse_stepList]
      rw [flagBit_flip]
      cases x with
      | mk left right flag =>
          cases flag <;> simp_all [compareIntoFlag]

/-- Typed circuit folded from the exact comparator program. -/
def compareCircuit (n : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding n).width).toQuantum :=
  compareProgram n

/-- Clean encoded-ket endpoint of the exact comparator circuit. -/
lemma compareCircuit_applyNormalized_clean_ket (n : Nat) (x : Data n) :
    (compareCircuit n).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding n).encode (x, cleanWork n)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical _).basisEquiv.symm
          ((encoding n).encode (compareIntoFlag x, cleanWork n))) := by
  have h := (compareProgram_realizes (environment := environment) n).apply_encoded_ket
    (x, cleanWork n)
  rw [compareStep_clean] at h
  exact h

/-- Ordered strict execution events derived from the exact comparator circuit. -/
def compareEventTrace (n : Nat) : List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (compareCircuit n).eventTrace

/-- Strict event pool derived from the exact comparator circuit. -/
def compareEventCost (n : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (compareCircuit n).eventCost

/-- Strict symbolic event critical path of the exact comparator circuit. -/
def compareEventDepth (n : Nat) :
    DepthExpr (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  (compareCircuit n).eventDepth

/-- Literal event-coordinate depth of the exact comparator circuit. -/
def compareEventQueryDepth (n : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  (compareCircuit n).eventQueryDepth focus

/-- Exact multiplicity of one gate coordinate in the comparator event pool. -/
def compareEventGateCount (n : Nat) (label : AlgorithmGate.Coordinate) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate label)
    (compareCircuit n).eventCost

/-- Linearizing comparator event depth recovers the exact strict event pool. -/
lemma compareCircuit_resourcesFromEventDepth_eq_eventCost (n : Nat) :
    (compareCircuit n).resourcesFromEventDepth = (compareCircuit n).eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost (compareCircuit n)











end

end CleanCircuit
end Comparator
end QuantumAlg

end
