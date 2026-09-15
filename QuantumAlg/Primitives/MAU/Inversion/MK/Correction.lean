/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.VBECircuit
import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Resource
import all QuantumAlg.Primitives.MAU.Inversion.MK.StructuredWitness
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Physical
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.VBECircuit.Resource

/-!
# Static inverse correction circuit
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Correction

noncomputable section

open MK
open MK.Circuit
open Nat.FixedWidth
open NumberTheory.BinaryGCD

/-- Fixed-round registers, one shared VBE multiplication workspace, and the
public target word.  The multiplication workspace reuses its internal VBE
adder first for reduction and later for the staged target addition. -/
abbrev Registers (tail counterWidth : Nat) :=
  (MK.Circuit.RegistersWithRouteHistory tail.succ counterWidth ×
      MAU.Multiplication.VBECircuit.Registers tail.succ) ×
    Word tail.succ

/-- The exact physical encoding of the closing circuit. -/
def encoding (tail counterWidth : Nat) :
    BinaryLabelEncoding (Registers tail counterWidth) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ))
    (wordEncoding tail.succ)

/-- Complete physical basis-label carrier. -/
abbrev Label (tail counterWidth : Nat) :=
  Fin (2 ^ (encoding tail counterWidth).width)

/-- Canonical clean input for the exact fixed-compute/correct/add/uncompute
ledger.  The physical modulus label must match the static circuit-family
parameter; the input and target labels do not select the program. -/
def initialRegisters (tail counterWidth : Nat)
    (p input target : Word tail.succ) : Registers tail counterWidth :=
  ((MK.Circuit.withCleanRouteHistory tail.succ counterWidth
      (MK.initialRegisters tail.succ counterWidth p input),
    MAU.Multiplication.Accumulate.VBECircuit.cleanState tail.succ p.val 0 0),
   target)

/-- The closing layout has a canonical clean inhabitant. -/
instance registersNonempty (tail counterWidth : Nat) :
    Nonempty (Registers tail counterWidth) :=
  ⟨initialRegisters tail counterWidth 0 0 0⟩

/-- The physical encoding embeds the closing layout into a finite label type. -/
noncomputable instance registersFinite (tail counterWidth : Nat) :
    Finite (Registers tail counterWidth) :=
  Finite.of_injective (encoding tail counterWidth).encode
    (encoding tail counterWidth).encode_injective

/-- Canonical correction boundary: the fixed-round state is retained, the
shared VBE workspace is clean with `value` in its multiplicand register, and
the public target contains `target`. -/
def cleanCorrectionRegisters (tail counterWidth p : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (value target : ZMod p) : Registers tail counterWidth :=
  ((fixed,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState tail.succ p
        ((value.val : Nat) : PlainAdder.Word tail.succ) 0),
    ⟨target.val % 2 ^ tail.succ,
      Nat.mod_lt _ (Nat.two_pow_pos tail.succ)⟩)

/-- Runtime pseudo-residue read from the complete physical Kaliski
coefficient, before the counter-controlled correction. -/
def runtimePseudoResidue (tail counterWidth p : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth) : ZMod p :=
  (MK.Circuit.dataRegisters tail counterWidth fixed).rCoeff.val

/-- Physical `(n+1)`-bit view of the complete runtime pseudo-residue. -/
def runtimePseudoResidueWord (tail counterWidth : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth) :
    PlainAdder.Word (MAU.Addition.VBECircuit.AdderWidth tail.succ) :=
  ((MK.Circuit.dataRegisters
      tail counterWidth fixed).rCoeff.val : Nat)

@[simp] theorem runtimePseudoResidueWord_val
    (tail counterWidth : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth) :
    (runtimePseudoResidueWord tail counterWidth fixed).val =
      (MK.Circuit.dataRegisters
        tail counterWidth fixed).rCoeff.val := by
  exact ZMod.val_natCast_of_lt
    (MK.Circuit.dataRegisters
      tail counterWidth fixed).rCoeff.isLt

/-- Runtime corrected residue.  The exponent is read from the physical
padding counter, rather than selected from a source trace. -/
def runtimeCorrectedResidue (tail counterWidth p : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth) : ZMod p :=
  (2 : ZMod p) ^
      (MK.Circuit.dataRegisters tail counterWidth fixed).counter.val *
    runtimePseudoResidue tail counterWidth p fixed

/-- Runtime sign-adjusted correction used by the target-transfer ledger. -/
def runtimeSignedCorrectedResidue (tail counterWidth p : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth) : ZMod p :=
  -runtimeCorrectedResidue tail counterWidth p fixed

/-! ## Bit-lens lifting into the closing layout -/

/-- Lift one fixed-round bit over the VBE workspace and public target. -/
def liftFixedBit (tail counterWidth : Nat)
    (bit : EncodedBit
      (MK.Circuit.encoding tail.succ counterWidth)) :
    EncodedBit (encoding tail counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.prod
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ))
    (wordEncoding tail.succ)
    (BinaryLabelEncoding.prodLeftBit
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ) bit)

/-- Lift one shared VBE-workspace bit over the fixed fold and public target. -/
def liftWorkBit (tail counterWidth : Nat)
    (bit : EncodedBit (MAU.Multiplication.VBECircuit.encoding tail.succ)) :
    EncodedBit (encoding tail counterWidth) :=
  BinaryLabelEncoding.prodLeftBit
    (BinaryLabelEncoding.prod
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ))
    (wordEncoding tail.succ)
    (BinaryLabelEncoding.prodRightBit
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ) bit)

/-- Lift one public-target value bit over the complete compute workspace. -/
def liftTargetBit (tail counterWidth : Nat)
    (bit : EncodedBit (wordEncoding tail.succ)) :
    EncodedBit (encoding tail counterWidth) :=
  BinaryLabelEncoding.prodRightBit
    (BinaryLabelEncoding.prod
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ))
    (wordEncoding tail.succ) bit

/-- A bit in the left product slice is separated from every bit in the right
slice.  Keeping this lemma shallow avoids unfolding either component's
encoding when closing disjointness obligations. -/
private theorem prodLeftBit_prodRightBit_wire_ne
    {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right)
    (leftBit : EncodedBit left) (rightBit : EncodedBit right) :
    (BinaryLabelEncoding.prodLeftBit left right leftBit).wire ≠
      (BinaryLabelEncoding.prodRightBit left right rightBit).wire := by
  intro hwire
  have hval := congrArg Fin.val hwire
  have hlt : leftBit.wire.val < left.width := leftBit.wire.isLt
  simp only [BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire] at hval
  omega

/-- Lifting two separated right-product bits preserves their separation. -/
private theorem prodRightBit_wire_ne
    {Left Right : Type} (left : BinaryLabelEncoding Left)
    (right : BinaryLabelEncoding Right)
    {first second : EncodedBit right}
    (hne : first.wire ≠ second.wire) :
    (BinaryLabelEncoding.prodRightBit left right first).wire ≠
      (BinaryLabelEncoding.prodRightBit left right second).wire := by
  intro hwire
  apply hne
  apply Fin.ext
  have hval := congrArg Fin.val hwire
  simp only [BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodRightWire] at hval
  omega

/-- Lifting two separated fixed-register bits through the two enclosing left
products preserves their separation. -/
private theorem liftFixedBit_wire_ne
    (tail counterWidth : Nat)
    {first second : EncodedBit
      (MK.Circuit.encoding tail.succ counterWidth)}
    (hne : first.wire ≠ second.wire) :
    (liftFixedBit tail counterWidth first).wire ≠
      (liftFixedBit tail counterWidth second).wire := by
  exact EncodedBit.GateSpec.prodLeftWire_ne (wordEncoding tail.succ)
    (EncodedBit.GateSpec.prodLeftWire_ne
      (MAU.Multiplication.VBECircuit.encoding tail.succ) hne)

/-- The internal Kaliski coefficient-state lift preserves distinct wires. -/
private theorem liftMKCoeffStateBit_wire_ne
    (tail counterWidth : Nat)
    {first second : EncodedBit
      (registersWithCoeffAdderWorkEncoding tail.succ counterWidth)}
    (hne : first.wire ≠ second.wire) :
    (MK.Circuit.liftCoeffStateBit
        tail counterWidth first).wire ≠
      (MK.Circuit.liftCoeffStateBit
        tail counterWidth second).wire := by
  exact EncodedBit.GateSpec.prodLeftWire_ne
    (wordEncoding (2 * tail.succ))
    (EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
      (EncodedBit.GateSpec.prodLeftWire_ne BinaryLabelEncoding.bool
        (EncodedBit.GateSpec.prodLeftWire_ne
          (counterIncrementWorkEncoding counterWidth) hne)))

/-- Lifting two separated VBE-workspace bits through the enclosing products
preserves their separation. -/
private theorem liftWorkBit_wire_ne
    (tail counterWidth : Nat)
    {first second : EncodedBit
      (MAU.Multiplication.VBECircuit.encoding tail.succ)}
    (hne : first.wire ≠ second.wire) :
    (liftWorkBit tail counterWidth first).wire ≠
      (liftWorkBit tail counterWidth second).wire := by
  exact EncodedBit.GateSpec.prodLeftWire_ne (wordEncoding tail.succ)
    (prodRightBit_wire_ne
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ) hne)

/-- Lifting two separated public-target bits through the outer right product
preserves their separation. -/
private theorem liftTargetBit_wire_ne
    (tail counterWidth : Nat)
    {first second : EncodedBit (wordEncoding tail.succ)}
    (hne : first.wire ≠ second.wire) :
    (liftTargetBit tail counterWidth first).wire ≠
      (liftTargetBit tail counterWidth second).wire :=
  prodRightBit_wire_ne
    (BinaryLabelEncoding.prod
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ))
    (wordEncoding tail.succ) hne

/-- Full `n+1`-bit Kaliski pseudo-residue register, in little-endian value
order.  The high bit is retained for the mandatory reduction modulo `p`. -/
def pseudoResidueWord (tail counterWidth : Nat) :
    EncodedBit.Word (encoding tail counterWidth) (tail.succ + 1) where
  bit := fun bit =>
    liftFixedBit tail counterWidth
      (MK.Circuit.liftCoeffStateBit tail counterWidth
        ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit bit))

/-- Runtime padding-counter value bit controlling one static correction
multiplication. -/
def paddingCounterBit (tail counterWidth : Nat)
    (bit : Fin counterWidth) : EncodedBit (encoding tail counterWidth) :=
  liftFixedBit tail counterWidth
    (MK.Circuit.liftCoeffStateBit tail counterWidth
      (coeffAdderCounterValueBit tail.succ counterWidth bit))

/-- The complete VBE arithmetic target used transiently for raw reduction. -/
def reductionTargetWord (tail counterWidth : Nat) :
    EncodedBit.Word (encoding tail counterWidth) (tail.succ + 1) where
  bit := fun bit =>
    liftWorkBit tail counterWidth
      ((MAU.Multiplication.Accumulate.VBECircuit.targetWord tail.succ).bit bit)

/-- Low `n` value bits of the reduction/target-add accumulator. -/
def reductionTargetLowWord (tail counterWidth : Nat) :
    EncodedBit.Word (encoding tail counterWidth) tail.succ where
  bit := fun bit =>
    liftWorkBit tail counterWidth
      (MAU.Multiplication.Accumulate.VBECircuit.targetBit tail.succ
        ⟨bit.val, by
          change bit.val < tail.succ + 1
          omega⟩)

/-- Canonical correction value stored in the VBE multiplication
multiplicand. -/
def correctionValueWord (tail counterWidth : Nat) :
    EncodedBit.Word (encoding tail counterWidth) tail.succ where
  bit := fun bit =>
    liftWorkBit tail counterWidth
      ((MAU.Multiplication.VBECircuit.multiplicandWord tail.succ).bit bit)

/-- Low `n` bits of the VBE active source used by the staged target add. -/
def targetAddSourceLowWord (tail counterWidth : Nat) :
    EncodedBit.Word (encoding tail counterWidth) tail.succ where
  bit := fun bit =>
    liftWorkBit tail counterWidth
      (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit tail.succ
        ⟨bit.val, by
          change bit.val < tail.succ + 1
          omega⟩)

/-- Public target word in little-endian value order. -/
def publicTargetWord (tail counterWidth : Nat) :
    EncodedBit.Word (encoding tail counterWidth) tail.succ where
  bit := fun bit =>
    liftTargetBit tail counterWidth
      (BinaryLabelEncoding.finIdentityBit tail.succ
        (WireAddress.littleEndianWire bit))

/-- Clean work bit reused by every counter-controlled whole-program lift. -/
def correctionControlWorkBit (tail counterWidth : Nat) :
    EncodedBit (encoding tail counterWidth) :=
  liftFixedBit tail counterWidth
    (MK.Circuit.workingControlBit tail counterWidth)

@[simp] theorem pseudoResidueWord_get
    (tail counterWidth : Nat) (bit : Fin (tail.succ + 1))
    (x : Registers tail counterWidth) :
    ((pseudoResidueWord tail counterWidth).bit bit).get x =
      (MK.Circuit.dataRegisters tail counterWidth x.1.1).rCoeff.val.testBit
        bit.val := by
  change
    ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit bit).get
        x.1.1.1.1.1.1 = _
  exact coeffAdderRCoeffValueWord_get_testBit
    tail.succ counterWidth bit x.1.1.1.1.1.1

@[simp] theorem paddingCounterBit_get
    (tail counterWidth : Nat) (bit : Fin counterWidth)
    (x : Registers tail counterWidth) :
    (paddingCounterBit tail counterWidth bit).get x =
      (MK.Circuit.dataRegisters tail counterWidth x.1.1).counter.val.testBit
        bit.val := by
  change
    (coeffAdderCounterValueBit tail.succ counterWidth bit).get
        x.1.1.1.1.1.1 = _
  exact coeffAdderCounterValueBit_get
    tail.succ counterWidth bit x.1.1.1.1.1.1

@[simp] theorem correctionControlWorkBit_get
    (tail counterWidth : Nat) (x : Registers tail counterWidth) :
    (correctionControlWorkBit tail counterWidth).get x = x.1.1.1.2 := by
  rfl

@[simp] theorem reductionTargetLowWord_get
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail counterWidth) :
    ((reductionTargetLowWord tail counterWidth).bit bit).get x =
      x.1.2.arithmetic.target.val.testBit bit.val := by
  change
    (MAU.Multiplication.Accumulate.VBECircuit.targetBit tail.succ
      ⟨bit.val, by
        change bit.val < tail.succ + 1
        omega⟩).get x.1.2 = _
  exact MAU.Multiplication.Accumulate.VBECircuit.targetBit_get
    tail.succ _ x.1.2

@[simp] theorem correctionValueWord_get
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail counterWidth) :
    ((correctionValueWord tail counterWidth).bit bit).get x =
      x.1.2.multiplicand.val.testBit bit.val := by
  change
    (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit
      tail.succ bit).get x.1.2 = _
  exact MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit_get
    tail.succ bit x.1.2

@[simp] theorem targetAddSourceLowWord_get
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail counterWidth) :
    ((targetAddSourceLowWord tail counterWidth).bit bit).get x =
      x.1.2.arithmetic.activeSource.val.testBit bit.val := by
  change
    (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit tail.succ
      ⟨bit.val, by
        change bit.val < tail.succ + 1
        omega⟩).get x.1.2 = _
  exact MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get
    tail.succ _ x.1.2

@[simp] theorem publicTargetWord_get
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail counterWidth) :
    ((publicTargetWord tail counterWidth).bit bit).get x =
      x.2.val.testBit bit.val := by
  change
    x.2.val.testBit
        (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

/-! ## Cross-register copies and program lifting -/

theorem pseudoResidue_reductionTarget_ne
    (tail counterWidth : Nat) :
    ∀ bit,
      ((pseudoResidueWord tail counterWidth).bit bit).wire ≠
        ((reductionTargetWord tail counterWidth).bit bit).wire := by
  intro bit
  have hinner := prodLeftBit_prodRightBit_wire_ne
    (MK.Circuit.encoding tail.succ counterWidth)
    (MAU.Multiplication.VBECircuit.encoding tail.succ)
    (MK.Circuit.liftCoeffStateBit tail counterWidth
      ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit bit))
    ((MAU.Multiplication.Accumulate.VBECircuit.targetWord tail.succ).bit bit)
  have houter := EncodedBit.GateSpec.prodLeftWire_ne
    (wordEncoding tail.succ) hinner
  simpa only [pseudoResidueWord, reductionTargetWord, liftFixedBit,
    liftWorkBit, encoding] using houter

theorem pseudoResidue_reductionTarget_cross_ne
    (tail counterWidth : Nat) :
    ∀ sourceBit targetBit,
      ((pseudoResidueWord tail counterWidth).bit sourceBit).wire ≠
        ((reductionTargetWord tail counterWidth).bit targetBit).wire := by
  intro sourceBit targetBit
  have hinner := prodLeftBit_prodRightBit_wire_ne
    (MK.Circuit.encoding tail.succ counterWidth)
    (MAU.Multiplication.VBECircuit.encoding tail.succ)
    (MK.Circuit.liftCoeffStateBit tail counterWidth
      ((coeffAdderRCoeffValueWord tail.succ counterWidth).bit sourceBit))
    ((MAU.Multiplication.Accumulate.VBECircuit.targetWord tail.succ).bit targetBit)
  have houter := EncodedBit.GateSpec.prodLeftWire_ne
    (wordEncoding tail.succ) hinner
  simpa only [pseudoResidueWord, reductionTargetWord, liftFixedBit,
    liftWorkBit, encoding] using houter

theorem reductionTarget_pairwise_ne (tail counterWidth : Nat) :
    ∀ i j, i ≠ j ->
      ((reductionTargetWord tail counterWidth).bit i).wire ≠
        ((reductionTargetWord tail counterWidth).bit j).wire := by
  intro i j hij
  apply liftWorkBit_wire_ne tail counterWidth
  apply MAU.Multiplication.VBECircuit.liftArithmeticBit_ne
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  simp only [MAU.Addition.VBECircuit.targetBit_wire_val] at hv
  omega

theorem reductionTargetLow_correctionValue_ne
    (tail counterWidth : Nat) :
    ∀ bit,
      ((reductionTargetLowWord tail counterWidth).bit bit).wire ≠
        ((correctionValueWord tail counterWidth).bit bit).wire := by
  intro bit
  let targetIndex :
      Fin (MAU.Addition.VBECircuit.AdderWidth tail.succ) :=
    ⟨bit.val, by
      change bit.val < tail.succ + 1
      omega⟩
  have hworkspace :
      (MAU.Multiplication.Accumulate.VBECircuit.targetBit
          tail.succ targetIndex).wire ≠
        ((MAU.Multiplication.VBECircuit.multiplicandWord
          tail.succ).bit bit).wire := by
    exact Ne.symm
      (MAU.Multiplication.VBECircuit.multiplicand_liftArithmetic_ne
        tail.succ bit
        (MAU.Addition.VBECircuit.targetBit tail.succ targetIndex))
  have hinner := prodRightBit_wire_ne
    (MK.Circuit.encoding tail.succ counterWidth)
    (MAU.Multiplication.VBECircuit.encoding tail.succ) hworkspace
  have houter := EncodedBit.GateSpec.prodLeftWire_ne
    (wordEncoding tail.succ) hinner
  simpa only [reductionTargetLowWord, correctionValueWord, liftWorkBit,
    encoding, targetIndex] using houter

theorem reductionTargetLow_correctionValue_cross_ne
    (tail counterWidth : Nat) :
    ∀ targetBit valueBit,
      ((reductionTargetLowWord tail counterWidth).bit targetBit).wire ≠
        ((correctionValueWord tail counterWidth).bit valueBit).wire := by
  intro targetBit valueBit
  let targetIndex :
      Fin (MAU.Addition.VBECircuit.AdderWidth tail.succ) :=
    ⟨targetBit.val, by
      change targetBit.val < tail.succ + 1
      omega⟩
  have hworkspace :
      (MAU.Multiplication.Accumulate.VBECircuit.targetBit
          tail.succ targetIndex).wire ≠
        ((MAU.Multiplication.VBECircuit.multiplicandWord
          tail.succ).bit valueBit).wire :=
    Ne.symm
      (MAU.Multiplication.VBECircuit.multiplicand_liftArithmetic_ne
        tail.succ valueBit
        (MAU.Addition.VBECircuit.targetBit tail.succ targetIndex))
  exact liftWorkBit_wire_ne tail counterWidth hworkspace

theorem correctionValue_targetAddSourceLow_ne
    (tail counterWidth : Nat) :
    ∀ bit,
      ((correctionValueWord tail counterWidth).bit bit).wire ≠
        ((targetAddSourceLowWord tail counterWidth).bit bit).wire := by
  intro bit
  let sourceIndex :
      Fin (MAU.Addition.VBECircuit.AdderWidth tail.succ) :=
    ⟨bit.val, by
      change bit.val < tail.succ + 1
      omega⟩
  have hworkspace :
      ((MAU.Multiplication.VBECircuit.multiplicandWord
          tail.succ).bit bit).wire ≠
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit
          tail.succ sourceIndex).wire := by
    exact
      MAU.Multiplication.VBECircuit.multiplicand_liftArithmetic_ne
        tail.succ bit
        (MAU.Addition.VBECircuit.activeSourceBit tail.succ sourceIndex)
  have hinner := prodRightBit_wire_ne
    (MK.Circuit.encoding tail.succ counterWidth)
    (MAU.Multiplication.VBECircuit.encoding tail.succ) hworkspace
  have houter := EncodedBit.GateSpec.prodLeftWire_ne
    (wordEncoding tail.succ) hinner
  simpa only [correctionValueWord, targetAddSourceLowWord, liftWorkBit,
    encoding, sourceIndex] using houter

theorem correctionValue_targetAddSourceLow_cross_ne
    (tail counterWidth : Nat) :
    ∀ valueBit sourceBit,
      ((correctionValueWord tail counterWidth).bit valueBit).wire ≠
        ((targetAddSourceLowWord tail counterWidth).bit sourceBit).wire := by
  intro valueBit sourceBit
  let sourceIndex :
      Fin (MAU.Addition.VBECircuit.AdderWidth tail.succ) :=
    ⟨sourceBit.val, by
      change sourceBit.val < tail.succ + 1
      omega⟩
  have hworkspace :
      ((MAU.Multiplication.VBECircuit.multiplicandWord
          tail.succ).bit valueBit).wire ≠
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit
          tail.succ sourceIndex).wire :=
    MAU.Multiplication.VBECircuit.multiplicand_liftArithmetic_ne
      tail.succ valueBit
      (MAU.Addition.VBECircuit.activeSourceBit tail.succ sourceIndex)
  exact liftWorkBit_wire_ne tail counterWidth hworkspace

theorem publicTarget_reductionTargetLow_ne
    (tail counterWidth : Nat) :
    ∀ bit,
      ((publicTargetWord tail counterWidth).bit bit).wire ≠
        ((reductionTargetLowWord tail counterWidth).bit bit).wire := by
  intro bit
  let targetIndex :
      Fin (MAU.Addition.VBECircuit.AdderWidth tail.succ) :=
    ⟨bit.val, by
      change bit.val < tail.succ + 1
      omega⟩
  let workBit := BinaryLabelEncoding.prodRightBit
    (MK.Circuit.encoding tail.succ counterWidth)
    (MAU.Multiplication.VBECircuit.encoding tail.succ)
    (MAU.Multiplication.Accumulate.VBECircuit.targetBit
      tail.succ targetIndex)
  have houter := prodLeftBit_prodRightBit_wire_ne
    (BinaryLabelEncoding.prod
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ))
    (wordEncoding tail.succ) workBit
    (BinaryLabelEncoding.finIdentityBit tail.succ
      (WireAddress.littleEndianWire bit))
  simpa only [publicTargetWord, reductionTargetLowWord, liftTargetBit,
    liftWorkBit, encoding, targetIndex, workBit] using Ne.symm houter

theorem publicTarget_reductionTargetLow_cross_ne
    (tail counterWidth : Nat) :
    ∀ publicBit workBit,
      ((publicTargetWord tail counterWidth).bit publicBit).wire ≠
        ((reductionTargetLowWord tail counterWidth).bit workBit).wire := by
  intro publicBit workBit
  let targetIndex :
      Fin (MAU.Addition.VBECircuit.AdderWidth tail.succ) :=
    ⟨workBit.val, by
      change workBit.val < tail.succ + 1
      omega⟩
  let innerWorkBit := BinaryLabelEncoding.prodRightBit
    (MK.Circuit.encoding tail.succ counterWidth)
    (MAU.Multiplication.VBECircuit.encoding tail.succ)
    (MAU.Multiplication.Accumulate.VBECircuit.targetBit tail.succ targetIndex)
  have houter := prodLeftBit_prodRightBit_wire_ne
    (BinaryLabelEncoding.prod
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ))
    (wordEncoding tail.succ) innerWorkBit
    (BinaryLabelEncoding.finIdentityBit tail.succ
      (WireAddress.littleEndianWire publicBit))
  simpa only [publicTargetWord, reductionTargetLowWord, liftTargetBit,
    liftWorkBit, encoding, targetIndex, innerWorkBit] using Ne.symm houter

theorem publicTarget_reductionTargetHigh_ne
    (tail counterWidth : Nat) :
    ∀ publicBit,
      ((publicTargetWord tail counterWidth).bit publicBit).wire ≠
        ((reductionTargetWord tail counterWidth).bit
          (Fin.last tail.succ)).wire := by
  intro publicBit
  let innerWorkBit := BinaryLabelEncoding.prodRightBit
    (MK.Circuit.encoding tail.succ counterWidth)
    (MAU.Multiplication.VBECircuit.encoding tail.succ)
    (MAU.Multiplication.Accumulate.VBECircuit.targetBit
      tail.succ (Fin.last tail.succ))
  have houter := prodLeftBit_prodRightBit_wire_ne
    (BinaryLabelEncoding.prod
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ))
    (wordEncoding tail.succ) innerWorkBit
    (BinaryLabelEncoding.finIdentityBit tail.succ
      (WireAddress.littleEndianWire publicBit))
  simpa only [publicTargetWord, reductionTargetWord, liftTargetBit,
    liftWorkBit, encoding, innerWorkBit,
    MAU.Multiplication.Accumulate.VBECircuit.targetWord] using Ne.symm houter

theorem reductionTargetLow_reductionTargetHigh_ne
    (tail counterWidth : Nat) :
    ∀ lowBit,
      ((reductionTargetLowWord tail counterWidth).bit lowBit).wire ≠
        ((reductionTargetWord tail counterWidth).bit
          (Fin.last tail.succ)).wire := by
  intro lowBit
  let lowIndex : Fin (tail.succ + 1) :=
    ⟨lowBit.val, by
      omega⟩
  have hne : lowIndex ≠ Fin.last tail.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [lowIndex, Fin.val_last] at hv
    exact (Nat.ne_of_lt lowBit.isLt) hv
  simpa only [reductionTargetLowWord, reductionTargetWord, lowIndex,
    MAU.Multiplication.Accumulate.VBECircuit.targetWord] using
    reductionTarget_pairwise_ne tail counterWidth lowIndex
      (Fin.last tail.succ) hne

theorem pseudoResidue_pairwise_ne (tail counterWidth : Nat) :
    ∀ i j, i ≠ j ->
      ((pseudoResidueWord tail counterWidth).bit i).wire ≠
        ((pseudoResidueWord tail counterWidth).bit j).wire := by
  intro i j hij
  apply liftFixedBit_wire_ne tail counterWidth
  exact liftMKCoeffStateBit_wire_ne tail counterWidth
    (coeffAdderRCoeffValueWordBit_coeffAdderRCoeffValueWordBit_wire_ne
      tail.succ counterWidth i j hij)

theorem reductionTargetLow_pairwise_ne (tail counterWidth : Nat) :
    ∀ i j, i ≠ j ->
      ((reductionTargetLowWord tail counterWidth).bit i).wire ≠
        ((reductionTargetLowWord tail counterWidth).bit j).wire := by
  intro i j hij
  apply liftWorkBit_wire_ne tail counterWidth
  simpa only [MAU.Multiplication.VBECircuit.accumulatorWord,
    MAU.Multiplication.VBECircuit.accumulatorBit,
    reductionTargetLowWord] using
      MAU.Multiplication.VBECircuit.accumulator_pairwise_ne
        tail.succ i j hij

theorem correctionValue_pairwise_ne (tail counterWidth : Nat) :
    ∀ i j, i ≠ j ->
      ((correctionValueWord tail counterWidth).bit i).wire ≠
        ((correctionValueWord tail counterWidth).bit j).wire := by
  intro i j hij
  exact liftWorkBit_wire_ne tail counterWidth
    (MAU.Multiplication.VBECircuit.multiplicand_pairwise_ne
      tail.succ i j hij)

theorem targetAddSourceLow_pairwise_ne (tail counterWidth : Nat) :
    ∀ i j, i ≠ j ->
      ((targetAddSourceLowWord tail counterWidth).bit i).wire ≠
        ((targetAddSourceLowWord tail counterWidth).bit j).wire := by
  intro i j hij
  apply liftWorkBit_wire_ne tail counterWidth
  let i' : Fin (MAU.Addition.VBECircuit.AdderWidth tail.succ) :=
    ⟨i.val, by
      change i.val < tail.succ + 1
      omega⟩
  let j' : Fin (MAU.Addition.VBECircuit.AdderWidth tail.succ) :=
    ⟨j.val, by
      change j.val < tail.succ + 1
      omega⟩
  have hij' : i' ≠ j' := by
    intro h
    apply hij
    have hv : i.val = j.val := by
      simpa only [i', j'] using congrArg Fin.val h
    exact Fin.ext hv
  simpa only [targetAddSourceLowWord,
    MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord, i', j'] using
    MAU.Multiplication.Accumulate.VBECircuit.activeSource_pairwise_ne
      tail.succ i' j' hij'

theorem targetAddSourceLow_targetAddSourceHigh_ne
    (tail counterWidth : Nat) :
    ∀ lowBit,
      ((targetAddSourceLowWord tail counterWidth).bit lowBit).wire ≠
        (liftWorkBit tail counterWidth
          (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit
            tail.succ (Fin.last tail.succ))).wire := by
  intro lowBit
  apply liftWorkBit_wire_ne tail counterWidth
  let lowIndex : Fin (tail.succ + 1) :=
    ⟨lowBit.val, by omega⟩
  have hne : lowIndex ≠ Fin.last tail.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [lowIndex, Fin.val_last] at hv
    exact (Nat.ne_of_lt lowBit.isLt) hv
  simpa only [targetAddSourceLowWord, lowIndex,
    MAU.Multiplication.Accumulate.VBECircuit.activeSourceWord] using
    MAU.Multiplication.Accumulate.VBECircuit.activeSource_pairwise_ne
      tail.succ lowIndex (Fin.last tail.succ) hne

theorem publicTarget_pairwise_ne (tail counterWidth : Nat) :
    ∀ i j, i ≠ j ->
      ((publicTargetWord tail counterWidth).bit i).wire ≠
        ((publicTargetWord tail counterWidth).bit j).wire := by
  intro i j hij
  apply liftTargetBit_wire_ne tail counterWidth
  change
    (WireAddress.littleEndianWire i : Fin tail.succ) ≠
      WireAddress.littleEndianWire j
  exact littleEndianWire_ne hij

/-- A word-xor fold preserves any projection preserved by every target-bit
flip.  This packages the unchanged-register side conditions used by the two
cross-register copies below. -/
private theorem xorIntoStep_preserves_projection
    {Data Projection : Type} {wordWidth : Nat}
    {dataEncoding : BinaryLabelEncoding Data}
    (source target : EncodedBit.Word dataEncoding wordWidth)
    (hdisjoint : ∀ i, (source.bit i).wire ≠ (target.bit i).wire)
    (project : Data -> Projection)
    (hpreserve : ∀ i x, project ((target.bit i).flip x) = project x)
    (x : Data) :
    project (EncodedBit.Word.xorIntoStep source target hdisjoint x) =
      project x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [EncodedBit.Word.xorIntoGates] at hgate
  rcases List.mem_ofFn.mp hgate with ⟨bit, rfl⟩
  exact hpreserve bit

/-- A word-swap fold preserves a projection preserved by flips in both swapped
words. -/
private theorem swapStep_preserves_projection
    {Data Projection : Type} {wordWidth : Nat}
    {dataEncoding : BinaryLabelEncoding Data}
    (left right : EncodedBit.Word dataEncoding wordWidth)
    (hdisjoint : ∀ i, (left.bit i).wire ≠ (right.bit i).wire)
    (project : Data -> Projection)
    (hleft : ∀ i x, project ((left.bit i).flip x) = project x)
    (hright : ∀ i x, project ((right.bit i).flip x) = project x)
    (x : Data) :
    project (EncodedBit.Word.swapStep left right hdisjoint x) = project x := by
  apply EncodedBit.GateSpec.stepList_preserves_of_targetFlipPreserves
  intro gate hgate
  simp only [EncodedBit.Word.swapGates, List.mem_flatMap] at hgate
  rcases hgate with ⟨bit, _hbit, hgate⟩
  simp only [EncodedBit.swapGates, List.mem_cons, List.not_mem_nil,
    or_false] at hgate
  rcases hgate with rfl | rfl | rfl
  · exact hright bit
  · exact hleft bit
  · exact hright bit

/-- Lift a fixed-round raw program over the VBE workspace and public target. -/
def liftFixedProgram (tail counterWidth : Nat)
    (program : UnitaryCircuit (Qubits
      (MK.Circuit.encoding tail.succ counterWidth).width)) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  UnitaryCircuit.prodLeft (n := (wordEncoding tail.succ).width)
    (UnitaryCircuit.prodLeft
      (n := (MAU.Multiplication.VBECircuit.encoding tail.succ).width)
      program)

/-- Lift a VBE-workspace raw program over the fixed fold and public target. -/
def liftWorkProgram (tail counterWidth : Nat)
    (program : UnitaryCircuit (Qubits
      (MAU.Multiplication.VBECircuit.encoding tail.succ).width)) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  UnitaryCircuit.prodLeft (n := (wordEncoding tail.succ).width)
    (UnitaryCircuit.prodRight
      (m := (MK.Circuit.encoding tail.succ counterWidth).width)
      program)

/-- Lift a fixed-register semantic step while preserving VBE work and target. -/
def liftFixedStep (tail counterWidth : Nat)
    (step : MK.Circuit.RegistersWithRouteHistory tail.succ counterWidth ->
      MK.Circuit.RegistersWithRouteHistory tail.succ counterWidth) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  fun x => ((step x.1.1, x.1.2), x.2)

/-- Lift a VBE-workspace semantic step while preserving fixed state and target. -/
def liftWorkStep (tail counterWidth : Nat)
    (step : MAU.Multiplication.VBECircuit.Registers tail.succ ->
      MAU.Multiplication.VBECircuit.Registers tail.succ) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  fun x => ((x.1.1, step x.1.2), x.2)

/-- Lift every fixed-round gate over the VBE workspace and public target. -/
def liftFixedGates (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MK.Circuit.encoding tail.succ counterWidth))) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  (gates.map (EncodedBit.GateSpec.prodLeft
    (MAU.Multiplication.VBECircuit.encoding tail.succ))).map
    (EncodedBit.GateSpec.prodLeft (wordEncoding tail.succ))

/-- Lifting the complete fixed-round payload preserves its folded action. -/
private theorem liftFixedGates_stepList (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MK.Circuit.encoding tail.succ counterWidth)))
    (x : Registers tail counterWidth) :
    EncodedBit.GateSpec.stepList
        (liftFixedGates tail counterWidth gates) x =
      liftFixedStep tail counterWidth
        (EncodedBit.GateSpec.stepList gates) x := by
  change
    EncodedBit.GateSpec.stepList
        ((gates.map (EncodedBit.GateSpec.prodLeft
          (MAU.Multiplication.VBECircuit.encoding tail.succ))).map
          (EncodedBit.GateSpec.prodLeft (wordEncoding tail.succ))) x =
      ((EncodedBit.GateSpec.stepList gates x.1.1, x.1.2), x.2)
  rw [EncodedBit.GateSpec.stepList_prodLeft,
    EncodedBit.GateSpec.stepList_prodLeft]

/-- Lift every VBE-workspace gate over the fixed fold and public target. -/
def liftWorkGates (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MAU.Multiplication.VBECircuit.encoding tail.succ))) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  (gates.map (EncodedBit.GateSpec.prodRight
      (MK.Circuit.encoding tail.succ counterWidth))).map
    (EncodedBit.GateSpec.prodLeft (wordEncoding tail.succ))

/-- Lifting the complete VBE payload gate list has exactly the lifted VBE
semantic action; no payload segment is selected or omitted. -/
private theorem liftWorkGates_stepList (tail counterWidth : Nat)
    (gates : List (EncodedBit.GateSpec
      (MAU.Multiplication.VBECircuit.encoding tail.succ)))
    (x : Registers tail counterWidth) :
    EncodedBit.GateSpec.stepList
        (liftWorkGates tail counterWidth gates) x =
      liftWorkStep tail counterWidth
        (EncodedBit.GateSpec.stepList gates) x := by
  change
    EncodedBit.GateSpec.stepList
        ((gates.map (EncodedBit.GateSpec.prodRight
          (MK.Circuit.encoding tail.succ counterWidth))).map
          (EncodedBit.GateSpec.prodLeft (wordEncoding tail.succ))) x =
      ((x.1.1, EncodedBit.GateSpec.stepList gates x.1.2), x.2)
  rw [EncodedBit.GateSpec.stepList_prodLeft,
    EncodedBit.GateSpec.stepList_prodRight]

/-- The complete VBE modular-add payload lifted into the correction layout. -/
def liftedWorkModularAddGates (tail counterWidth p : Nat) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  liftWorkGates tail counterWidth
    (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates
      tail.succ p)

/-- Folded action of the lifted VBE modular-add payload. -/
def liftedWorkModularAddStep (tail counterWidth p : Nat) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (liftedWorkModularAddGates tail counterWidth p)

/-- The lifted VBE modular-add payload agrees with the established workspace
semantic action. -/
theorem liftedWorkModularAddStep_eq_liftWorkStep
    (tail counterWidth p : Nat) (x : Registers tail counterWidth) :
    liftedWorkModularAddStep tail counterWidth p x =
      liftWorkStep tail counterWidth
        (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
          tail.succ p) x := by
  change EncodedBit.GateSpec.stepList
      (liftWorkGates tail counterWidth
        (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates
          tail.succ p)) x =
    ((x.1.1,
        MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
          tail.succ p x.1.2), x.2)
  rw [liftWorkGates_stepList]
  change ((x.1.1,
      EncodedBit.GateSpec.stepList
        (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddGates
          tail.succ p) x.1.2), x.2) = _
  exact congrArg (fun work => ((x.1.1, work), x.2))
    (MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep_eq_gateList
      tail.succ p x.1.2)

/-- Realization transport for a fixed-register actual circuit. -/
theorem liftFixed_realizes (tail counterWidth : Nat)
    {program : UnitaryCircuit (Qubits
      (MK.Circuit.encoding tail.succ counterWidth).width)}
    {step : MK.Circuit.RegistersWithRouteHistory tail.succ counterWidth ->
      MK.Circuit.RegistersWithRouteHistory tail.succ counterWidth}
    (h : UnitaryCircuit.Realizes (MK.Circuit.encoding tail.succ counterWidth)
      program step) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (liftFixedProgram tail counterWidth program)
      (liftFixedStep tail counterWidth step) :=
  UnitaryCircuit.Realizes.prodLeft
    (right := wordEncoding tail.succ)
    (UnitaryCircuit.Realizes.prodLeft
      (right := MAU.Multiplication.VBECircuit.encoding tail.succ) h)

/-- Realization transport for a VBE-workspace actual circuit. -/
theorem liftWork_realizes (tail counterWidth : Nat)
    {program : UnitaryCircuit (Qubits
      (MAU.Multiplication.VBECircuit.encoding tail.succ).width)}
    {step : MAU.Multiplication.VBECircuit.Registers tail.succ ->
      MAU.Multiplication.VBECircuit.Registers tail.succ}
    (h : UnitaryCircuit.Realizes
      (MAU.Multiplication.VBECircuit.encoding tail.succ) program step) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (liftWorkProgram tail counterWidth program)
      (liftWorkStep tail counterWidth step) :=
  UnitaryCircuit.Realizes.prodLeft
    (right := wordEncoding tail.succ)
    (UnitaryCircuit.Realizes.prodRight
      (left := MK.Circuit.encoding tail.succ counterWidth) h)

/-- Complete fixed-round payload lifted into the correction layout. -/
def fixedComputeGates (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  liftFixedGates tail counterWidth
    (MK.Circuit.foldGates tail counterWidth comparisonIndex workIndex)

/-- Exact static fixed-round compute program compiled from its full gate list. -/
def fixedComputeProgram (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (fixedComputeGates tail counterWidth comparisonIndex workIndex)

/-- Folded action of the complete lifted fixed-round gate schedule. -/
def fixedComputeStep (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (fixedComputeGates tail counterWidth comparisonIndex workIndex)

/-- The lifted fixed-round gate list agrees with the established fold action. -/
theorem fixedComputeStep_eq_liftFixedStep
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (x : Registers tail counterWidth) :
    fixedComputeStep tail counterWidth comparisonIndex workIndex x =
      liftFixedStep tail counterWidth
        (MK.Circuit.foldStep tail counterWidth comparisonIndex workIndex) x := by
  change EncodedBit.GateSpec.stepList
      (liftFixedGates tail counterWidth
        (MK.Circuit.foldGates tail counterWidth comparisonIndex workIndex)) x =
    ((MK.Circuit.foldStep tail counterWidth comparisonIndex workIndex x.1.1,
      x.1.2), x.2)
  rw [liftFixedGates_stepList]
  change ((EncodedBit.GateSpec.stepList
      (MK.Circuit.foldGates tail counterWidth comparisonIndex workIndex) x.1.1,
      x.1.2), x.2) = _
  exact congrArg (fun fixed => ((fixed, x.1.2), x.2))
    (MK.Circuit.foldStep_eq_gateList
      tail counterWidth comparisonIndex workIndex x.1.1)

/-- The fixed-round actual circuit realizes its complete gate list. -/
theorem fixedCompute_realizes (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (fixedComputeProgram tail counterWidth comparisonIndex workIndex)
      (fixedComputeStep tail counterWidth comparisonIndex workIndex) :=
  EncodedBit.GateSpec.realizesList
    (fixedComputeGates tail counterWidth comparisonIndex workIndex)

/-- The lifted fixed-round program reaches one physical clean endpoint that
is independent of the shared VBE workspace and public target.  The endpoint
retains both the physical prefix invariant and its exact source-state
readout, so the correction ledger can consume the runtime registers and then
reverse this same compute program. -/
theorem fixedComputeProgram_cleanEndpoint
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (p input : Word tail.succ)
    (hpOdd : p.val % 2 = 1)
    (hfinal : comparisonIndex.val + 1 = tail.succ)
    (arithAt :
      ∀ (roundIndex : Fin (2 * tail.succ))
        (x : MK.Circuit.RegistersWithRouteHistory
          tail.succ counterWidth),
        MK.Circuit.CleanPrefixInvariant
            tail counterWidth p input roundIndex.val x ->
          ModeControlledSemanticStepArithmeticCertificate tail counterWidth
            (MK.Circuit.dataRegisters tail counterWidth x)) :
    ∃ fixed : MK.Circuit.RegistersWithRouteHistory
        tail.succ counterWidth,
      (∀ (work : MAU.Multiplication.VBECircuit.Registers tail.succ)
          (target : Word tail.succ),
        fixedComputeStep tail counterWidth comparisonIndex workIndex
            (((MK.Circuit.withCleanRouteHistory
                tail.succ counterWidth
                (MK.initialRegisters
                  tail.succ counterWidth p input)), work), target) =
          ((fixed, work), target)) ∧
      MK.Circuit.CleanPrefixInvariant
        tail counterWidth p input (2 * tail.succ) fixed ∧
      RoundState.fromRegisters tail.succ counterWidth
          (MK.Circuit.dataRegisters tail counterWidth fixed)
          (RoundState.fixedRoundState
            tail.succ p.val input.val).kaliskiSteps
          (RoundState.fixedRoundState
            tail.succ p.val input.val).paddingSteps =
        RoundState.fixedRoundState tail.succ p.val input.val := by
  rcases MK.Circuit.foldStep_cleanEndpoint_eq_source
      tail counterWidth comparisonIndex workIndex p input hpOdd hfinal arithAt
      with ⟨fixed, hfold, hinvariant, hsource⟩
  refine ⟨fixed, ?_, hinvariant, hsource⟩
  intro work target
  rw [fixedComputeStep_eq_liftFixedStep]
  change
    ((MK.Circuit.foldStep tail counterWidth comparisonIndex workIndex
        (MK.Circuit.withCleanRouteHistory tail.succ counterWidth
          (MK.initialRegisters tail.succ counterWidth p input)), work),
      target) = _
  rw [hfold]

/-! ## Runtime pseudo-residue reduction -/

private theorem copyPseudoResidueStep_cleanEndpoint
    (tail counterWidth p : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (multiplicand : PlainAdder.Word tail.succ)
    (target : Word tail.succ) :
    EncodedBit.Word.xorIntoStep
        (pseudoResidueWord tail counterWidth)
        (reductionTargetWord tail counterWidth)
        (pseudoResidue_reductionTarget_ne tail counterWidth)
        (((fixed,
            MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
              multiplicand 0 (p : PlainAdder.Word tail.succ) 0 false),
          target) : Registers tail counterWidth) =
      ((fixed,
          MAU.Multiplication.Accumulate.VBECircuit.workspaceState
            tail.succ multiplicand 0 (p : PlainAdder.Word tail.succ)
            (runtimePseudoResidueWord tail counterWidth fixed) false),
        target) := by
  let before : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          multiplicand 0 (p : PlainAdder.Word tail.succ) 0 false),
      target)
  let step := EncodedBit.Word.xorIntoStep
    (pseudoResidueWord tail counterWidth)
    (reductionTargetWord tail counterWidth)
    (pseudoResidue_reductionTarget_ne tail counterWidth)
  have hfixed : (step before).1.1 = fixed := by
    exact xorIntoStep_preserves_projection
      (pseudoResidueWord tail counterWidth)
      (reductionTargetWord tail counterWidth)
      (pseudoResidue_reductionTarget_ne tail counterWidth)
      (fun x => x.1.1) (fun _ _ => rfl) before
  have hpublic : (step before).2 = target := by
    exact xorIntoStep_preserves_projection
      (pseudoResidueWord tail counterWidth)
      (reductionTargetWord tail counterWidth)
      (pseudoResidue_reductionTarget_ne tail counterWidth)
      (fun x => x.2) (fun _ _ => rfl) before
  have hmultiplicand :
      (step before).1.2.multiplicand = multiplicand := by
    simpa only [before,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using
      xorIntoStep_preserves_projection
        (pseudoResidueWord tail counterWidth)
        (reductionTargetWord tail counterWidth)
        (pseudoResidue_reductionTarget_ne tail counterWidth)
        (fun x => x.1.2.multiplicand) (fun _ _ => rfl) before
  have hactive :
      (step before).1.2.arithmetic.activeSource =
        MAU.Addition.VBECircuit.widenWord tail.succ
          (0 : PlainAdder.Word tail.succ) := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (pseudoResidueWord tail counterWidth)
        (reductionTargetWord tail counterWidth)
        (pseudoResidue_reductionTarget_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.activeSource) (fun _ _ => rfl) before
  have htarget :
      (step before).1.2.arithmetic.target =
        runtimePseudoResidueWord tail counterWidth fixed := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread := EncodedBit.Word.xorIntoStep_get_target
      (pseudoResidueWord tail counterWidth)
      (reductionTargetWord tail counterWidth)
      (pseudoResidue_reductionTarget_ne tail counterWidth) bit
      (fun other hne =>
        reductionTarget_pairwise_ne tail counterWidth other bit hne)
      (fun other => Ne.symm
        (pseudoResidue_reductionTarget_cross_ne
          tail counterWidth bit other)) before
    have hzero :
        ((reductionTargetWord tail counterWidth).bit bit).get before =
          false := by
      change
        (MAU.Multiplication.Accumulate.VBECircuit.targetBit
          tail.succ bit).get
            (MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
              multiplicand 0 (p : PlainAdder.Word tail.succ) 0 false) = false
      rw [MAU.Multiplication.Accumulate.VBECircuit.targetBit_get]
      simp [MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState]
    rw [hzero] at hread
    rw [← MAU.Multiplication.Accumulate.VBECircuit.targetBit_get]
    change
      ((reductionTargetWord tail counterWidth).bit bit).get (step before) =
        (runtimePseudoResidueWord tail counterWidth fixed).val.testBit bit.val
    simpa [step, before] using hread
  have hcarry : (step before).1.2.arithmetic.carry = false := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (pseudoResidueWord tail counterWidth)
        (reductionTargetWord tail counterWidth)
        (pseudoResidue_reductionTarget_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.carry) (fun _ _ => rfl) before
  have hparked :
      (step before).1.2.arithmetic.parkedSource =
        (p : PlainAdder.Word tail.succ) := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (pseudoResidueWord tail counterWidth)
        (reductionTargetWord tail counterWidth)
        (pseudoResidue_reductionTarget_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.parkedSource) (fun _ _ => rfl) before
  have hcarryWork :
      (step before).1.2.arithmetic.carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
          (MAU.Addition.VBECircuit.AdderWidth tail.succ) := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (pseudoResidueWord tail counterWidth)
        (reductionTargetWord tail counterWidth)
        (pseudoResidue_reductionTarget_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.carryWork) (fun _ _ => rfl) before
  have hflag : (step before).1.2.arithmetic.reductionFlag = false := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (pseudoResidueWord tail counterWidth)
        (reductionTargetWord tail counterWidth)
        (pseudoResidue_reductionTarget_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.reductionFlag) (fun _ _ => rfl) before
  change step before = _
  apply Prod.ext
  · apply Prod.ext
    · exact hfixed
    · apply
        (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv
          tail.succ).injective
      change
        ((step before).1.2.multiplicand,
            (step before).1.2.arithmetic) =
          (multiplicand, MAU.Addition.VBECircuit.sourceSwapCleanState
            tail.succ 0 (p : PlainAdder.Word tail.succ)
            (runtimePseudoResidueWord tail counterWidth fixed) false)
      rw [hmultiplicand]
      congr 1
      apply (MAU.Addition.VBECircuit.registersEquiv tail.succ).injective
      simp [MAU.Addition.VBECircuit.registersEquiv,
        MAU.Addition.VBECircuit.sourceSwapCleanState,
        hactive, htarget, hcarry, hparked, hcarryWork, hflag]
  · exact hpublic

private theorem copyReducedStep_cleanEndpoint
    (tail counterWidth p : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (value : PlainAdder.Word tail.succ) (flag : Bool)
    (target : Word tail.succ) :
    EncodedBit.Word.xorIntoStep
        (reductionTargetLowWord tail counterWidth)
        (correctionValueWord tail counterWidth)
        (reductionTargetLow_correctionValue_ne tail counterWidth)
        (((fixed,
            MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
              0 0 (p : PlainAdder.Word tail.succ)
              (MAU.Addition.VBECircuit.widenWord tail.succ value) flag),
          target) : Registers tail counterWidth) =
      ((fixed,
          MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
            value 0 (p : PlainAdder.Word tail.succ)
            (MAU.Addition.VBECircuit.widenWord tail.succ value) flag),
        target) := by
  let before : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          0 0 (p : PlainAdder.Word tail.succ)
          (MAU.Addition.VBECircuit.widenWord tail.succ value) flag),
      target)
  let step := EncodedBit.Word.xorIntoStep
    (reductionTargetLowWord tail counterWidth)
    (correctionValueWord tail counterWidth)
    (reductionTargetLow_correctionValue_ne tail counterWidth)
  have hfixed : (step before).1.1 = fixed := by
    exact xorIntoStep_preserves_projection
      (reductionTargetLowWord tail counterWidth)
      (correctionValueWord tail counterWidth)
      (reductionTargetLow_correctionValue_ne tail counterWidth)
      (fun x => x.1.1) (fun _ _ => rfl) before
  have hpublic : (step before).2 = target := by
    exact xorIntoStep_preserves_projection
      (reductionTargetLowWord tail counterWidth)
      (correctionValueWord tail counterWidth)
      (reductionTargetLow_correctionValue_ne tail counterWidth)
      (fun x => x.2) (fun _ _ => rfl) before
  have harithmetic :
      (step before).1.2.arithmetic =
        MAU.Addition.VBECircuit.sourceSwapCleanState tail.succ
          0 (p : PlainAdder.Word tail.succ)
          (MAU.Addition.VBECircuit.widenWord tail.succ value) flag := by
    simpa only [before,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using
      xorIntoStep_preserves_projection
        (reductionTargetLowWord tail counterWidth)
        (correctionValueWord tail counterWidth)
        (reductionTargetLow_correctionValue_ne tail counterWidth)
        (fun x => x.1.2.arithmetic) (fun _ _ => rfl) before
  have hmultiplicand : (step before).1.2.multiplicand = value := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    have hread := EncodedBit.Word.xorIntoStep_get_target
      (reductionTargetLowWord tail counterWidth)
      (correctionValueWord tail counterWidth)
      (reductionTargetLow_correctionValue_ne tail counterWidth) bit
      (fun other hne =>
        correctionValue_pairwise_ne tail counterWidth other bit hne)
      (fun other => Ne.symm
        (reductionTargetLow_correctionValue_cross_ne
          tail counterWidth bit other)) before
    have hzero :
        ((correctionValueWord tail counterWidth).bit bit).get before =
          false := by
      change
        (MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit
          tail.succ bit).get
            (MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
              0 0 (p : PlainAdder.Word tail.succ)
              (MAU.Addition.VBECircuit.widenWord tail.succ value) flag) =
          false
      rw [MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit_get]
      simp [MAU.Multiplication.Accumulate.VBECircuit.workspaceState]
    have hsource :
        ((reductionTargetLowWord tail counterWidth).bit bit).get before =
          value.val.testBit bit.val := by
      change
        (MAU.Multiplication.Accumulate.VBECircuit.targetBit tail.succ
          ⟨bit.val, by
            change bit.val < tail.succ + 1
            omega⟩).get
            (MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
              0 0 (p : PlainAdder.Word tail.succ)
              (MAU.Addition.VBECircuit.widenWord tail.succ value) flag) =
          value.val.testBit bit.val
      rw [MAU.Multiplication.Accumulate.VBECircuit.targetBit_get]
      simp [MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState]
    rw [hzero, hsource] at hread
    rw [← MAU.Multiplication.Accumulate.VBECircuit.multiplicandBit_get]
    change
      ((correctionValueWord tail counterWidth).bit bit).get (step before) =
        _
    simpa [step] using hread
  change step before = _
  apply Prod.ext
  · apply Prod.ext
    · exact hfixed
    · apply
        (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv
          tail.succ).injective
      change
        ((step before).1.2.multiplicand,
            (step before).1.2.arithmetic) =
          (value, MAU.Addition.VBECircuit.sourceSwapCleanState tail.succ
            0 (p : PlainAdder.Word tail.succ)
            (MAU.Addition.VBECircuit.widenWord tail.succ value) flag)
      rw [hmultiplicand, harithmetic]
  · exact hpublic

/-- Complete base-gate schedule for loading, reducing, copying, and
uncomputing the runtime pseudo-residue. -/
def rawPseudoResidueLoadGates (tail counterWidth p : Nat) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  let copyRaw := EncodedBit.Word.xorIntoGates
    (pseudoResidueWord tail counterWidth)
    (reductionTargetWord tail counterWidth)
    (pseudoResidue_reductionTarget_ne tail counterWidth)
  let copyReduced := EncodedBit.Word.xorIntoGates
    (reductionTargetLowWord tail counterWidth)
    (correctionValueWord tail counterWidth)
    (reductionTargetLow_correctionValue_ne tail counterWidth)
  let reduce := liftedWorkModularAddGates tail counterWidth p
  copyRaw ++ reduce ++ copyReduced ++ reduce.reverse ++ copyRaw.reverse

/-- Copy the full pseudo-residue into the VBE target, reduce it once modulo
`p`, copy the canonical low word into correction scratch, and reverse the
reducer.  The program depends only on layout and modulus. -/
def rawPseudoResidueLoadProgram (tail counterWidth p : Nat) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (rawPseudoResidueLoadGates tail counterWidth p)

/-- Folded action of the complete raw-loader gate schedule. -/
def rawPseudoResidueLoadStep (tail counterWidth p : Nat) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (rawPseudoResidueLoadGates tail counterWidth p)

/-- The actual raw-loader circuit realizes the gate schedule it compiles. -/
theorem rawPseudoResidueLoad_realizes (tail counterWidth p : Nat) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (rawPseudoResidueLoadProgram tail counterWidth p)
      (rawPseudoResidueLoadStep tail counterWidth p) :=
  EncodedBit.GateSpec.realizesList
    (rawPseudoResidueLoadGates tail counterWidth p)

/-- The static raw loader reduces the complete runtime coefficient once,
copies its canonical residue into correction scratch, and restores the VBE
arithmetic workspace exactly. -/
theorem rawPseudoResidueLoadProgram_cleanEndpoint
    (tail counterWidth p : Nat)
    (hpPos : 0 < p) (hpBound : p < 2 ^ tail.succ)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (hraw :
      (MK.Circuit.dataRegisters
        tail counterWidth fixed).rCoeff.val < 2 * p)
    (target : ZMod p) :
    rawPseudoResidueLoadStep tail counterWidth p
        (cleanCorrectionRegisters tail counterWidth p fixed 0 target) =
      cleanCorrectionRegisters tail counterWidth p fixed
        (runtimePseudoResidue tail counterWidth p fixed) target := by
  let _ : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  let raw := runtimePseudoResidueWord tail counterWidth fixed
  let reduced := raw.val % p
  let reducedLow : PlainAdder.Word tail.succ := reduced
  let flag := decide (p ≤ raw.val)
  let publicTarget : Word tail.succ :=
    ⟨target.val % 2 ^ tail.succ,
      Nat.mod_lt _ (Nat.two_pow_pos tail.succ)⟩
  let copyRawGates := EncodedBit.Word.xorIntoGates
    (pseudoResidueWord tail counterWidth)
    (reductionTargetWord tail counterWidth)
    (pseudoResidue_reductionTarget_ne tail counterWidth)
  let copyReducedGates := EncodedBit.Word.xorIntoGates
    (reductionTargetLowWord tail counterWidth)
    (correctionValueWord tail counterWidth)
    (reductionTargetLow_correctionValue_ne tail counterWidth)
  let reduceGates := liftedWorkModularAddGates tail counterWidth p
  let copyRawStep := EncodedBit.Word.xorIntoStep
    (pseudoResidueWord tail counterWidth)
    (reductionTargetWord tail counterWidth)
    (pseudoResidue_reductionTarget_ne tail counterWidth)
  let copyReducedStep := EncodedBit.Word.xorIntoStep
    (reductionTargetLowWord tail counterWidth)
    (correctionValueWord tail counterWidth)
    (reductionTargetLow_correctionValue_ne tail counterWidth)
  let reduceStep := liftedWorkModularAddStep tail counterWidth p
  let s0 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          0 0 (p : PlainAdder.Word tail.succ) 0 false),
      publicTarget)
  let s1 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          0 0 (p : PlainAdder.Word tail.succ) raw false),
      publicTarget)
  let s2 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          0 0 (p : PlainAdder.Word tail.succ)
          (MAU.Addition.VBECircuit.widenWord tail.succ reducedLow) flag),
      publicTarget)
  let s3 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          reducedLow 0 (p : PlainAdder.Word tail.succ)
          (MAU.Addition.VBECircuit.widenWord tail.succ reducedLow) flag),
      publicTarget)
  let s4 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          reducedLow 0 (p : PlainAdder.Word tail.succ) raw false),
      publicTarget)
  let s5 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          reducedLow 0 (p : PlainAdder.Word tail.succ) 0 false),
      publicTarget)
  have hraw' : raw.val < 2 * p := by
    simpa only [raw, runtimePseudoResidueWord_val] using hraw
  have hreduced : reduced < 2 ^ tail.succ := by
    exact (Nat.mod_lt raw.val hpPos).trans hpBound
  have hwiden :
      MAU.Addition.VBECircuit.widenWord tail.succ reducedLow =
        (reduced : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth tail.succ)) := by
    simpa only [reducedLow] using
      MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
        tail.succ reduced hreduced
  have hresidueVal :
      (runtimePseudoResidue tail counterWidth p fixed).val = reduced := by
    simp only [runtimePseudoResidue, reduced, raw, ZMod.val_natCast,
      runtimePseudoResidueWord_val]
  have hcopyRaw
      (multiplicand : PlainAdder.Word tail.succ) :
      copyRawStep
          ((fixed,
              MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
                multiplicand 0 (p : PlainAdder.Word tail.succ) 0 false),
            publicTarget) =
        ((fixed,
            MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
              multiplicand 0 (p : PlainAdder.Word tail.succ) raw false),
          publicTarget) := by
    simpa only [copyRawStep, raw] using
      copyPseudoResidueStep_cleanEndpoint
        tail counterWidth p fixed multiplicand publicTarget
  have hreduce
      (multiplicand : PlainAdder.Word tail.succ) :
      reduceStep
          ((fixed,
              MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
                multiplicand 0 (p : PlainAdder.Word tail.succ) raw false),
            publicTarget) =
        ((fixed,
            MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
              multiplicand 0 (p : PlainAdder.Word tail.succ)
              (MAU.Addition.VBECircuit.widenWord tail.succ reducedLow)
              flag),
          publicTarget) := by
    let beforeWork :=
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
        multiplicand 0 (p : PlainAdder.Word tail.succ) raw false
    let afterWork :=
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
        multiplicand 0 (p : PlainAdder.Word tail.succ)
        (MAU.Addition.VBECircuit.widenWord tail.succ reducedLow) flag
    have hstep :
        MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
            tail.succ p beforeWork = afterWork := by
      apply (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv
        tail.succ).injective
      change
        (multiplicand,
            MAU.Addition.VBECircuit.modularAddStep tail.succ p
              (MAU.Addition.VBECircuit.sourceSwapCleanState tail.succ
                0 (p : PlainAdder.Word tail.succ) raw false)) =
          (multiplicand,
            MAU.Addition.VBECircuit.sourceSwapCleanState tail.succ
              0 (p : PlainAdder.Word tail.succ)
              (MAU.Addition.VBECircuit.widenWord tail.succ reducedLow)
              flag)
      rw [MAU.Addition.VBECircuit.modularAddStep_zeroSource_reduceOnceEndpoint
        tail.succ p raw hpPos hpBound hraw']
      simp only [reduced, flag, hwiden]
    dsimp only [reduceStep]
    rw [liftedWorkModularAddStep_eq_liftWorkStep]
    change ((fixed,
      MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
        tail.succ p beforeWork), publicTarget) = _
    rw [hstep]
  have hcopyReduced :
      copyReducedStep s2 = s3 := by
    change
      EncodedBit.Word.xorIntoStep
          (reductionTargetLowWord tail counterWidth)
          (correctionValueWord tail counterWidth)
          (reductionTargetLow_correctionValue_ne tail counterWidth) s2 = s3
    simpa only [s2, s3] using
      copyReducedStep_cleanEndpoint tail counterWidth p fixed
        reducedLow flag publicTarget
  have hinverseReduce :
      EncodedBit.GateSpec.stepList reduceGates.reverse s3 = s4 := by
    rw [← show EncodedBit.GateSpec.stepList reduceGates s4 = s3 by
      change reduceStep s4 = s3
      exact hreduce reducedLow]
    exact EncodedBit.GateSpec.stepList_reverse_stepList reduceGates s4
  have hinverseCopyRaw :
      EncodedBit.GateSpec.stepList copyRawGates.reverse s4 = s5 := by
    rw [← show EncodedBit.GateSpec.stepList copyRawGates s5 = s4 by
      change copyRawStep s5 = s4
      exact hcopyRaw reducedLow]
    exact EncodedBit.GateSpec.stepList_reverse_stepList copyRawGates s5
  have hs0 :
      cleanCorrectionRegisters tail counterWidth p fixed 0 target = s0 := by
    simp [cleanCorrectionRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      s0, publicTarget]
  have hs5 :
      cleanCorrectionRegisters tail counterWidth p fixed
          (runtimePseudoResidue tail counterWidth p fixed) target = s5 := by
    simp [cleanCorrectionRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      s5, publicTarget, hresidueVal, reducedLow]
  rw [hs0, hs5]
  change EncodedBit.GateSpec.stepList
    (copyRawGates ++ reduceGates ++ copyReducedGates ++
      reduceGates.reverse ++ copyRawGates.reverse) s0 = s5
  simp only [EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList copyRawGates s0 = s1 by
    change copyRawStep s0 = s1
    exact hcopyRaw 0]
  rw [show EncodedBit.GateSpec.stepList reduceGates s1 = s2 by
    change reduceStep s1 = s2
    exact hreduce 0]
  rw [show EncodedBit.GateSpec.stepList copyReducedGates s2 = s3 by
    change copyReducedStep s2 = s3
    exact hcopyReduced,
    hinverseReduce, hinverseCopyRaw]

/-! ## Counter-driven correction and sign handling -/

/-- The unit represented by the static base `2` modulo an odd modulus. -/
def twoUnit (p : Nat) (hpOdd : Odd p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime 2 hpOdd.coprime_two_left

/-- Static unit selected for one runtime counter bit. -/
def counterBitUnit (p : Nat) (hpOdd : Odd p) (bit : Nat) : (ZMod p)ˣ :=
  (twoUnit p hpOdd) ^ (2 ^ bit)

/-- Complete VBE multiplication payload lifted into the correction layout. -/
def liftedUnitMultiplicationGates
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  liftWorkGates tail counterWidth
    (MAU.Multiplication.VBECircuit.multiplicationGates tail.succ p unit)

/-- Whole lifted modular-multiplication program for one static unit. -/
def liftedUnitMultiplicationProgram
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (liftedUnitMultiplicationGates tail counterWidth p unit)

/-- Folded action of one lifted unit-multiplication gate schedule. -/
def liftedUnitMultiplicationStep
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (liftedUnitMultiplicationGates tail counterWidth p unit)

/-- The lifted multiplication gate schedule agrees with the established
workspace action. -/
theorem liftedUnitMultiplicationStep_eq_liftWorkStep
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ)
    (x : Registers tail counterWidth) :
    liftedUnitMultiplicationStep tail counterWidth p unit x =
      liftWorkStep tail counterWidth
        (MAU.Multiplication.VBECircuit.multiplicationStep tail.succ p unit) x := by
  change EncodedBit.GateSpec.stepList
      (liftWorkGates tail counterWidth
        (MAU.Multiplication.VBECircuit.multiplicationGates
          tail.succ p unit)) x =
    ((x.1.1,
        MAU.Multiplication.VBECircuit.multiplicationStep
          tail.succ p unit x.1.2), x.2)
  rw [liftWorkGates_stepList]
  change ((x.1.1,
      EncodedBit.GateSpec.stepList
        (MAU.Multiplication.VBECircuit.multiplicationGates
          tail.succ p unit) x.1.2), x.2) = _
  exact congrArg (fun work => ((x.1.1, work), x.2))
    (MAU.Multiplication.VBECircuit.multiplicationStep_eq_gateList
      tail.succ p unit x.1.2)

/-- The lifted actual multiplication circuit realizes its complete gate list. -/
theorem liftedUnitMultiplication_realizes
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (liftedUnitMultiplicationProgram tail counterWidth p unit)
      (liftedUnitMultiplicationStep tail counterWidth p unit) :=
  EncodedBit.GateSpec.realizesList
    (liftedUnitMultiplicationGates tail counterWidth p unit)

/-- A lifted unit-multiplication payload updates only the correction value and
returns the complete shared VBE workspace clean. -/
theorem liftedUnitMultiplicationProgram_cleanEndpoint
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (hpBound : p < 2 ^ tail.succ) (unit : (ZMod p)ˣ)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (value target : ZMod p) :
    liftedUnitMultiplicationStep tail counterWidth p unit
        (cleanCorrectionRegisters tail counterWidth p fixed value target) =
      cleanCorrectionRegisters tail counterWidth p fixed
        ((unit : ZMod p) * value) target := by
  rw [liftedUnitMultiplicationStep_eq_liftWorkStep]
  let before := MAU.Multiplication.Accumulate.VBECircuit.cleanState
    tail.succ p ((value.val : Nat) : PlainAdder.Word tail.succ) 0
  let after := MAU.Multiplication.Accumulate.VBECircuit.cleanState
    tail.succ p
      ((((unit : ZMod p) * value).val : Nat) : PlainAdder.Word tail.succ) 0
  have hbase :
      MAU.Multiplication.VBECircuit.multiplicationStep tail.succ p unit
        before = after := by
    simpa only [before, after,
      MAU.Multiplication.Accumulate.VBECircuit.cleanEmbedding,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.cleanInput, MAU.Multiplication.cleanOutput,
      ZMod.val_zero] using
      MAU.Multiplication.VBECircuit.multiplicationStep_cleanEndpoint
        tail.succ p unit value hpOdd.pos hpBound
  change ((fixed,
    MAU.Multiplication.VBECircuit.multiplicationStep tail.succ p unit before),
      _) = _
  rw [hbase]
  rfl

/-! ### Complete GateSpec payload for embedded clean-work control -/

/-- Every gate in a lifted complete VBE payload is disjoint from every
fixed-round bit. -/
theorem liftWorkGates_bitDisjoint_liftFixedBit
    (tail counterWidth : Nat)
    (fixedBit : EncodedBit
      (MK.Circuit.encoding tail.succ counterWidth))
    (gates : List (EncodedBit.GateSpec
      (MAU.Multiplication.VBECircuit.encoding tail.succ))) :
    ∀ gate, gate ∈ liftWorkGates tail counterWidth gates ->
      EncodedBit.GateSpec.bitDisjoint
        (liftFixedBit tail counterWidth fixedBit) gate := by
  intro gate hgate
  unfold liftWorkGates at hgate
  rcases List.mem_map.mp hgate with ⟨innerGate, hinnerGate, rfl⟩
  rcases List.mem_map.mp hinnerGate with ⟨sourceGate, _hsourceGate, rfl⟩
  change EncodedBit.GateSpec.bitDisjoint
    (BinaryLabelEncoding.prodLeftBit
      (BinaryLabelEncoding.prod
        (MK.Circuit.encoding tail.succ counterWidth)
        (MAU.Multiplication.VBECircuit.encoding tail.succ))
      (wordEncoding tail.succ)
      (BinaryLabelEncoding.prodLeftBit
        (MK.Circuit.encoding tail.succ counterWidth)
        (MAU.Multiplication.VBECircuit.encoding tail.succ) fixedBit))
    (EncodedBit.GateSpec.prodLeft (wordEncoding tail.succ)
      (EncodedBit.GateSpec.prodRight
        (MK.Circuit.encoding tail.succ counterWidth) sourceGate))
  exact EncodedBit.GateSpec.bitDisjoint_prodLeft_of_bitDisjoint
    (wordEncoding tail.succ)
    (BinaryLabelEncoding.prodLeftBit
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ) fixedBit)
    (EncodedBit.GateSpec.prodRight
      (MK.Circuit.encoding tail.succ counterWidth) sourceGate)
    (EncodedBit.GateSpec.bitDisjoint_prodRight_leftBit
      (MK.Circuit.encoding tail.succ counterWidth)
      (MAU.Multiplication.VBECircuit.encoding tail.succ)
      fixedBit sourceGate)

theorem paddingCounter_controlWork_ne
    (tail counterWidth : Nat) (bit : Fin counterWidth) :
    (paddingCounterBit tail counterWidth bit).wire ≠
      (correctionControlWorkBit tail counterWidth).wire := by
  let counterBit := coeffAdderCounterValueBit
    tail.succ counterWidth bit
  let fullRoundBit := liftCoeffAdderStateBitToFullRoundWork
    tail counterWidth counterBit
  let pathWorkBit := liftFullRoundWorkBitToPathWork
    tail counterWidth fullRoundBit
  have hpathRaw := prodLeftBit_prodRightBit_wire_ne
    (registersWithFullRoundPathWorkEncoding tail.succ counterWidth)
    BinaryLabelEncoding.bool pathWorkBit BinaryLabelEncoding.boolBit
  have hpath :
      (liftFullRoundWorkBitToPathControlWork
          tail counterWidth fullRoundBit).wire ≠
        (fullRoundPathControlWorkControlWorkBit
          tail counterWidth).wire := by
    simpa only [liftFullRoundWorkBitToPathControlWork,
      liftFullRoundPathWorkBitToControlWork,
      fullRoundPathControlWorkControlWorkBit,
      registersWithFullRoundPathControlWorkEncoding,
      pathWorkBit] using hpathRaw
  have hroute := EncodedBit.GateSpec.prodLeftWire_ne
    (wordEncoding (2 * tail.succ)) hpath
  have hfixed :
      (MK.Circuit.liftCoeffStateBit
          tail counterWidth counterBit).wire ≠
        (MK.Circuit.workingControlBit
          tail counterWidth).wire := by
    simpa only [MK.Circuit.liftCoeffStateBit,
      MK.Circuit.liftFullRoundBit,
      MK.Circuit.workingControlBit,
      MK.Circuit.liftPathControlBit,
      MK.Circuit.encoding, fullRoundBit] using hroute
  have hinner := EncodedBit.GateSpec.prodLeftWire_ne
    (MAU.Multiplication.VBECircuit.encoding tail.succ) hfixed
  have houter := EncodedBit.GateSpec.prodLeftWire_ne
    (wordEncoding tail.succ) hinner
  simpa only [paddingCounterBit, correctionControlWorkBit, liftFixedBit,
    encoding, counterBit] using houter

/-- The shared control-decomposition work bit is clean at every certified
fixed-round workspace boundary. -/
theorem correctionControlWorkBit_get_false_of_clean
    (tail counterWidth : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (hclean : MK.Circuit.PhysicalWorkspaceClean
      tail counterWidth fixed)
    (work : MAU.Multiplication.VBECircuit.Registers tail.succ)
    (target : Word tail.succ) :
    (correctionControlWorkBit tail counterWidth).get
        ((fixed, work), target) = false := by
  rw [correctionControlWorkBit_get]
  have hcontrol := congrArg Prod.snd hclean.workspace
  simpa only [withCleanFullRoundPathControlWork] using hcontrol

/-- Unit selected by one physical runtime counter bit. -/
def selectedCounterUnitAt
    (p : Nat) (hpOdd : Odd p) (counter bit : Nat) : (ZMod p)ˣ :=
  if counter.testBit bit then counterBitUnit p hpOdd bit else 1

private theorem selectedCounterUnitAt_eq_pow_selectedBitWeight
    (p : Nat) (hpOdd : Odd p) (counter bit : Nat) :
    selectedCounterUnitAt p hpOdd counter bit =
      (twoUnit p hpOdd) ^
        Nat.FixedWidth.ModularAccumulate.selectedBitWeight counter bit := by
  cases hbit : counter.testBit bit <;>
    simp [selectedCounterUnitAt, counterBitUnit,
      Nat.FixedWidth.ModularAccumulate.selectedBitWeight, hbit]

private theorem selectedCounterUnits_prod_eq_pow_selectedLowWeight
    (p : Nat) (hpOdd : Odd p) (counter width : Nat) :
    (List.ofFn fun bit : Fin width =>
      selectedCounterUnitAt p hpOdd counter bit.val).prod =
        (twoUnit p hpOdd) ^
          Nat.FixedWidth.ModularAccumulate.selectedLowWeight
            counter width := by
  induction width with
  | zero =>
      simp
  | succ width ih =>
      rw [List.ofFn_succ', List.prod_concat]
      rw [show
        (List.ofFn fun bit : Fin width =>
          selectedCounterUnitAt p hpOdd counter (Fin.castSucc bit).val).prod =
            (List.ofFn fun bit : Fin width =>
              selectedCounterUnitAt p hpOdd counter bit.val).prod by rfl]
      rw [ih]
      rw [selectedCounterUnitAt_eq_pow_selectedBitWeight]
      simp only [Fin.val_last]
      rw [← pow_add]
      rfl

private theorem selectedCounterUnits_prod_eq_pow
    (p : Nat) (hpOdd : Odd p) (counter width : Nat)
    (hcounter : counter < 2 ^ width) :
    (List.ofFn fun bit : Fin width =>
      selectedCounterUnitAt p hpOdd counter bit.val).prod =
        (twoUnit p hpOdd) ^ counter := by
  rw [selectedCounterUnits_prod_eq_pow_selectedLowWeight]
  rw [Nat.FixedWidth.ModularAccumulate.selectedLowWeight_eq_self_of_lt_two_pow
    hcounter]

/-- The complete physical gate list of one multiplication payload, lifted into
the correction layout without selecting or omitting any payload segment. -/
def counterCorrectionBitPayloadGates
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  liftWorkGates tail counterWidth
    (MAU.Multiplication.VBECircuit.multiplicationGates tail.succ p
      (counterBitUnit p hpOdd bit.val))

private theorem counterCorrectionBitPayload_stepList
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) (x : Registers tail counterWidth) :
    EncodedBit.GateSpec.stepList
        (counterCorrectionBitPayloadGates
          tail counterWidth p hpOdd bit) x =
      liftedUnitMultiplicationStep tail counterWidth p
        (counterBitUnit p hpOdd bit.val) x := by
  rw [liftedUnitMultiplicationStep_eq_liftWorkStep]
  rw [counterCorrectionBitPayloadGates, liftWorkGates_stepList]
  change
    ((x.1.1,
        EncodedBit.GateSpec.stepList
          (MAU.Multiplication.VBECircuit.multiplicationGates tail.succ p
            (counterBitUnit p hpOdd bit.val)) x.1.2), x.2) =
      ((x.1.1,
        MAU.Multiplication.VBECircuit.multiplicationStep tail.succ p
          (counterBitUnit p hpOdd bit.val) x.1.2), x.2)
  exact congrArg (fun work => ((x.1.1, work), x.2))
    (MAU.Multiplication.VBECircuit.multiplicationStep_eq_gateList
      tail.succ p (counterBitUnit p hpOdd bit.val) x.1.2)

/-- Every physical counter-control wire is disjoint from its lifted payload. -/
theorem counterCorrectionBitPayload_controlDisjoint
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    ∀ gate,
      gate ∈ counterCorrectionBitPayloadGates
          tail counterWidth p hpOdd bit ->
        EncodedBit.GateSpec.bitDisjoint
          (paddingCounterBit tail counterWidth bit) gate := by
  simpa only [counterCorrectionBitPayloadGates, paddingCounterBit] using
    liftWorkGates_bitDisjoint_liftFixedBit tail counterWidth
      (MK.Circuit.liftCoeffStateBit tail counterWidth
        (coeffAdderCounterValueBit tail.succ counterWidth bit))
      (MAU.Multiplication.VBECircuit.multiplicationGates tail.succ p
        (counterBitUnit p hpOdd bit.val))

/-- The dedicated clean control-work wire is disjoint from the lifted payload. -/
theorem counterCorrectionBitPayload_workDisjoint
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    ∀ gate,
      gate ∈ counterCorrectionBitPayloadGates
          tail counterWidth p hpOdd bit ->
        EncodedBit.GateSpec.bitDisjoint
          (correctionControlWorkBit tail counterWidth) gate := by
  simpa only [counterCorrectionBitPayloadGates,
    correctionControlWorkBit] using
    liftWorkGates_bitDisjoint_liftFixedBit tail counterWidth
      (MK.Circuit.workingControlBit tail counterWidth)
      (MAU.Multiplication.VBECircuit.multiplicationGates tail.succ p
        (counterBitUnit p hpOdd bit.val))

/-- Exact clean-work control expansion of the complete multiplication gate
list for one physical runtime-counter bit. -/
def counterCorrectionBitGates
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (paddingCounterBit tail counterWidth bit)
    (correctionControlWorkBit tail counterWidth)
    (counterCorrectionBitPayloadGates tail counterWidth p hpOdd bit)
    (counterCorrectionBitPayload_controlDisjoint
      tail counterWidth p hpOdd bit)
    (counterCorrectionBitPayload_workDisjoint
      tail counterWidth p hpOdd bit)
    (paddingCounter_controlWork_ne tail counterWidth bit)

/-- One runtime-counter-controlled multiplication by a static power of two. -/
def counterCorrectionBitProgram
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (counterCorrectionBitGates tail counterWidth p hpOdd bit)

/-- Semantic action of one exact clean-work controlled multiplication list. -/
def counterCorrectionBitStep
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  EncodedBit.GateSpec.controlledListWithWorkStep
    (paddingCounterBit tail counterWidth bit)
    (correctionControlWorkBit tail counterWidth)
    (counterCorrectionBitPayloadGates tail counterWidth p hpOdd bit)
    (counterCorrectionBitPayload_controlDisjoint
      tail counterWidth p hpOdd bit)
    (counterCorrectionBitPayload_workDisjoint
      tail counterWidth p hpOdd bit)
    (paddingCounter_controlWork_ne tail counterWidth bit)

/-- The exact controlled gate list realizes its semantic action. -/
theorem counterCorrectionBit_realizes
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bit : Fin counterWidth) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (counterCorrectionBitProgram tail counterWidth p hpOdd bit)
      (counterCorrectionBitStep tail counterWidth p hpOdd bit) := by
  simpa only [counterCorrectionBitProgram, counterCorrectionBitGates,
    counterCorrectionBitStep] using
    EncodedBit.GateSpec.controlledListWithWorkWitness
      (paddingCounterBit tail counterWidth bit)
      (correctionControlWorkBit tail counterWidth)
      (counterCorrectionBitPayloadGates tail counterWidth p hpOdd bit)
      (counterCorrectionBitPayload_controlDisjoint
        tail counterWidth p hpOdd bit)
      (counterCorrectionBitPayload_workDisjoint
        tail counterWidth p hpOdd bit)
      (paddingCounter_controlWork_ne tail counterWidth bit)

/-- One physical counter bit either preserves the clean correction boundary or
applies its statically assigned power-of-two unit. -/
private theorem counterCorrectionBitProgram_cleanEndpoint
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (hpBound : p < 2 ^ tail.succ)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (hclean : MK.Circuit.PhysicalWorkspaceClean
      tail counterWidth fixed)
    (value target : ZMod p) (bit : Fin counterWidth) :
    let counter :=
      (MK.Circuit.dataRegisters tail counterWidth fixed).counter.val
    counterCorrectionBitStep tail counterWidth p hpOdd bit
        (cleanCorrectionRegisters tail counterWidth p fixed value target) =
      cleanCorrectionRegisters tail counterWidth p fixed
        (((selectedCounterUnitAt p hpOdd counter bit.val : (ZMod p)ˣ) :
            ZMod p) * value) target := by
  dsimp only
  let state := cleanCorrectionRegisters tail counterWidth p fixed value target
  have hcontrolRead :
      (paddingCounterBit tail counterWidth bit).get state =
        (MK.Circuit.dataRegisters
          tail counterWidth fixed).counter.val.testBit bit.val := by
    simp only [state, cleanCorrectionRegisters, paddingCounterBit_get]
  have hworkRead :
      (correctionControlWorkBit tail counterWidth).get state = false := by
    exact correctionControlWorkBit_get_false_of_clean
      tail counterWidth fixed hclean
      (MAU.Multiplication.Accumulate.VBECircuit.cleanState tail.succ p
        ((value.val : Nat) : PlainAdder.Word tail.succ) 0)
      ⟨target.val % 2 ^ tail.succ,
        Nat.mod_lt _ (Nat.two_pow_pos tail.succ)⟩
  cases hbit :
      (MK.Circuit.dataRegisters
        tail counterWidth fixed).counter.val.testBit bit.val
  · rw [show counterCorrectionBitStep tail counterWidth p hpOdd bit state =
        state by
      unfold counterCorrectionBitStep
      exact
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
          (paddingCounterBit tail counterWidth bit)
          (correctionControlWorkBit tail counterWidth)
          (counterCorrectionBitPayloadGates
            tail counterWidth p hpOdd bit)
          (counterCorrectionBitPayload_controlDisjoint
            tail counterWidth p hpOdd bit)
          (counterCorrectionBitPayload_workDisjoint
            tail counterWidth p hpOdd bit)
          (paddingCounter_controlWork_ne tail counterWidth bit)
          state (hcontrolRead.trans hbit)]
    simp [state, selectedCounterUnitAt, hbit]
  · rw [show counterCorrectionBitStep tail counterWidth p hpOdd bit state =
        EncodedBit.GateSpec.stepList
          (counterCorrectionBitPayloadGates
            tail counterWidth p hpOdd bit) state by
      unfold counterCorrectionBitStep
      exact
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
          (paddingCounterBit tail counterWidth bit)
          (correctionControlWorkBit tail counterWidth)
          (counterCorrectionBitPayloadGates
            tail counterWidth p hpOdd bit)
          (counterCorrectionBitPayload_controlDisjoint
            tail counterWidth p hpOdd bit)
          (counterCorrectionBitPayload_workDisjoint
            tail counterWidth p hpOdd bit)
          (paddingCounter_controlWork_ne tail counterWidth bit)
          state (hcontrolRead.trans hbit) hworkRead]
    rw [counterCorrectionBitPayload_stepList]
    simp only [selectedCounterUnitAt, hbit, if_true]
    exact liftedUnitMultiplicationProgram_cleanEndpoint
      tail counterWidth p hpOdd hpBound
      (counterBitUnit p hpOdd bit.val) fixed value target

private theorem counterCorrectionList_cleanEndpoint
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (hpBound : p < 2 ^ tail.succ)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (hclean : MK.Circuit.PhysicalWorkspaceClean
      tail counterWidth fixed)
    (value target : ZMod p) (bits : List (Fin counterWidth)) :
    let counter :=
      (MK.Circuit.dataRegisters tail counterWidth fixed).counter.val
    UnitaryCircuit.Realizes.stepList
        (bits.map fun bit =>
          counterCorrectionBitStep tail counterWidth p hpOdd bit)
        (cleanCorrectionRegisters tail counterWidth p fixed value target) =
      cleanCorrectionRegisters tail counterWidth p fixed
        ((((bits.map fun bit =>
            selectedCounterUnitAt p hpOdd counter bit.val).prod :
              (ZMod p)ˣ) : ZMod p) * value) target := by
  dsimp only
  induction bits generalizing value with
  | nil =>
      simp [UnitaryCircuit.Realizes.stepList]
  | cons bit bits ih =>
      rw [List.map_cons]
      change UnitaryCircuit.Realizes.stepList
        (bits.map fun next =>
          counterCorrectionBitStep tail counterWidth p hpOdd next)
        (counterCorrectionBitStep tail counterWidth p hpOdd bit
          (cleanCorrectionRegisters tail counterWidth p fixed value target)) = _
      rw [counterCorrectionBitProgram_cleanEndpoint
        tail counterWidth p hpOdd hpBound fixed hclean value target bit]
      rw [ih (value :=
        (((selectedCounterUnitAt p hpOdd
          (MK.Circuit.dataRegisters tail counterWidth fixed).counter.val
          bit.val : (ZMod p)ˣ) : ZMod p) * value))]
      apply congrArg (fun nextValue =>
        cleanCorrectionRegisters tail counterWidth p fixed nextValue target)
      simp only [List.map_cons, List.prod_cons, Units.val_mul]
      calc
        _ =
            ((selectedCounterUnitAt p hpOdd
                (MK.Circuit.dataRegisters tail counterWidth fixed).counter.val
                bit.val : (ZMod p)ˣ) : ZMod p) *
              ((((bits.map fun next =>
                selectedCounterUnitAt p hpOdd
                  (MK.Circuit.dataRegisters tail counterWidth fixed).counter.val
                  next.val).prod : (ZMod p)ˣ) : ZMod p) * value) :=
          (mul_left_comm _ _ _).symm
        _ = _ := (mul_assoc _ _ _).symm

/-- Complete base-gate schedule containing one controlled multiplication per
runtime counter bit. -/
def counterCorrectionGates
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  (List.ofFn fun bit : Fin counterWidth => bit).flatMap
    (counterCorrectionBitGates tail counterWidth p hpOdd)

/-- Flattening the per-bit controlled payloads preserves their execution
order and semantic action. -/
private theorem counterCorrectionGates_stepList
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (bits : List (Fin counterWidth)) (x : Registers tail counterWidth) :
    EncodedBit.GateSpec.stepList
        (bits.flatMap (counterCorrectionBitGates tail counterWidth p hpOdd)) x =
      UnitaryCircuit.Realizes.stepList
        (bits.map (counterCorrectionBitStep tail counterWidth p hpOdd)) x := by
  induction bits generalizing x with
  | nil =>
      rfl
  | cons bit bits ih =>
      simp only [List.flatMap_cons, List.map_cons,
        EncodedBit.GateSpec.stepList_append, UnitaryCircuit.Realizes.stepList]
      change
        EncodedBit.GateSpec.stepList
            (bits.flatMap
              (counterCorrectionBitGates tail counterWidth p hpOdd))
            (counterCorrectionBitStep tail counterWidth p hpOdd bit x) =
          UnitaryCircuit.Realizes.stepList
            (bits.map (counterCorrectionBitStep tail counterWidth p hpOdd))
            (counterCorrectionBitStep tail counterWidth p hpOdd bit x)
      exact ih _

/-- Exact counter-driven correction program. -/
def counterCorrectionProgram
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (counterCorrectionGates tail counterWidth p hpOdd)

/-- Folded action of every physical runtime-counter control. -/
def counterCorrectionStep
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (counterCorrectionGates tail counterWidth p hpOdd)

/-- The actual counter-controlled circuit realizes its complete gate list. -/
theorem counterCorrection_realizes
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (counterCorrectionProgram tail counterWidth p hpOdd)
      (counterCorrectionStep tail counterWidth p hpOdd) :=
  EncodedBit.GateSpec.realizesList
    (counterCorrectionGates tail counterWidth p hpOdd)

/-- The complete counter-controlled program multiplies the clean correction
value by `2^k`, where `k` is read directly from the physical runtime counter. -/
theorem counterCorrection_cleanEndpoint
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (hpBound : p < 2 ^ tail.succ)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (hclean : MK.Circuit.PhysicalWorkspaceClean
      tail counterWidth fixed)
    (value target : ZMod p) :
    let counter :=
      (MK.Circuit.dataRegisters tail counterWidth fixed).counter.val
    counterCorrectionStep tail counterWidth p hpOdd
        (cleanCorrectionRegisters tail counterWidth p fixed value target) =
      cleanCorrectionRegisters tail counterWidth p fixed
        ((2 : ZMod p) ^ counter * value) target := by
  dsimp only
  let counter :=
    (MK.Circuit.dataRegisters tail counterWidth fixed).counter.val
  let bits := List.ofFn fun bit : Fin counterWidth => bit
  have hlist := counterCorrectionList_cleanEndpoint
    tail counterWidth p hpOdd hpBound fixed hclean value target bits
  have hgateSteps :
      counterCorrectionStep tail counterWidth p hpOdd
          (cleanCorrectionRegisters tail counterWidth p fixed value target) =
        UnitaryCircuit.Realizes.stepList
          (bits.map (counterCorrectionBitStep tail counterWidth p hpOdd))
          (cleanCorrectionRegisters tail counterWidth p fixed value target) := by
    unfold counterCorrectionStep counterCorrectionGates
    simpa only [bits] using
      counterCorrectionGates_stepList tail counterWidth p hpOdd bits
        (cleanCorrectionRegisters tail counterWidth p fixed value target)
  have hunits :
      (bits.map fun bit =>
        selectedCounterUnitAt p hpOdd counter bit.val).prod =
        (List.ofFn fun bit : Fin counterWidth =>
          selectedCounterUnitAt p hpOdd counter bit.val).prod := by
    congr 1
    simpa only [bits, id_eq] using
      (List.ofFn_comp'
        (fun bit : Fin counterWidth => bit)
        (fun bit => selectedCounterUnitAt p hpOdd counter bit.val)).symm
  have hcounter : counter < 2 ^ counterWidth :=
    (MK.Circuit.dataRegisters
      tail counterWidth fixed).counter.isLt
  have hunit := selectedCounterUnits_prod_eq_pow
    p hpOdd counter counterWidth hcounter
  have hcoe := congrArg Units.val hunit
  have hcoefficient :
      (((bits.map fun bit =>
          selectedCounterUnitAt p hpOdd counter bit.val).prod :
            (ZMod p)ˣ) : ZMod p) =
        (2 : ZMod p) ^ counter := by
    rw [hunits]
    simpa only [twoUnit, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime, Nat.cast_ofNat] using hcoe
  rw [hgateSteps]
  simpa only [hcoefficient, counter] using hlist

/-- Static modular sign correction required by the Montgomery--Kaliski source
convention. -/
def signCorrectionGates (tail counterWidth p : Nat) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  liftedUnitMultiplicationGates tail counterWidth p
    (-1 : (ZMod p)ˣ)

/-- Static modular sign-correction circuit compiled from its complete gate list. -/
def signCorrectionProgram (tail counterWidth p : Nat) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (signCorrectionGates tail counterWidth p)

/-- Folded action of the static sign-correction gate schedule. -/
def signCorrectionStep (tail counterWidth p : Nat) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (signCorrectionGates tail counterWidth p)

/-- The actual static sign-correction circuit realizes its complete gate list. -/
theorem signCorrection_realizes (tail counterWidth p : Nat) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (signCorrectionProgram tail counterWidth p)
      (signCorrectionStep tail counterWidth p) :=
  EncodedBit.GateSpec.realizesList
    (signCorrectionGates tail counterWidth p)

/-- The static sign segment negates the correction value and returns every VBE
work register clean. -/
theorem signCorrectionProgram_cleanEndpoint
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (hpBound : p < 2 ^ tail.succ)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (value target : ZMod p) :
    signCorrectionStep tail counterWidth p
        (cleanCorrectionRegisters tail counterWidth p fixed value target) =
      cleanCorrectionRegisters tail counterWidth p fixed (-value) target := by
  change liftedUnitMultiplicationStep tail counterWidth p (-1 : (ZMod p)ˣ)
      (cleanCorrectionRegisters tail counterWidth p fixed value target) = _
  simpa only [Units.val_neg, Units.val_one, neg_mul,
    one_mul] using
    liftedUnitMultiplicationProgram_cleanEndpoint
      tail counterWidth p hpOdd hpBound (-1 : (ZMod p)ˣ)
      fixed value target

/-- Complete base-gate schedule for raw reduction, runtime correction, and the
source-required sign correction. -/
def correctionComputeGates
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  rawPseudoResidueLoadGates tail counterWidth p ++
    counterCorrectionGates tail counterWidth p hpOdd ++
      signCorrectionGates tail counterWidth p

/-- Concatenate the three static correction segments from one gate schedule. -/
def correctionComputeProgram
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (correctionComputeGates tail counterWidth p hpOdd)

/-- Folded action of the complete correction-compute gate schedule. -/
def correctionComputeStep
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (correctionComputeGates tail counterWidth p hpOdd)

/-- The actual correction-compute circuit realizes its complete gate list. -/
theorem correctionCompute_realizes
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (correctionComputeProgram tail counterWidth p hpOdd)
      (correctionComputeStep tail counterWidth p hpOdd) :=
  EncodedBit.GateSpec.realizesList
    (correctionComputeGates tail counterWidth p hpOdd)

/-- The correction-compute gate list executes its three constituent stages in
their physical order. -/
private theorem correctionComputeStep_eq_stages
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (x : Registers tail counterWidth) :
    correctionComputeStep tail counterWidth p hpOdd x =
      signCorrectionStep tail counterWidth p
        (counterCorrectionStep tail counterWidth p hpOdd
          (rawPseudoResidueLoadStep tail counterWidth p x)) := by
  change EncodedBit.GateSpec.stepList
      (rawPseudoResidueLoadGates tail counterWidth p ++
        counterCorrectionGates tail counterWidth p hpOdd ++
          signCorrectionGates tail counterWidth p) x = _
  rw [EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  change signCorrectionStep tail counterWidth p
      (counterCorrectionStep tail counterWidth p hpOdd
        (rawPseudoResidueLoadStep tail counterWidth p x)) = _
  rfl

/-- The three static correction segments produce the sign-adjusted runtime
residue and return the complete shared VBE workspace clean. -/
theorem correctionCompute_cleanEndpoint
    (tail counterWidth p : Nat) (hpOdd : Odd p)
    (hpBound : p < 2 ^ tail.succ)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (hclean : MK.Circuit.PhysicalWorkspaceClean
      tail counterWidth fixed)
    (hraw :
      (MK.Circuit.dataRegisters
        tail counterWidth fixed).rCoeff.val < 2 * p)
    (target : ZMod p) :
    correctionComputeStep tail counterWidth p hpOdd
        (cleanCorrectionRegisters tail counterWidth p fixed 0 target) =
      cleanCorrectionRegisters tail counterWidth p fixed
        (runtimeSignedCorrectedResidue tail counterWidth p fixed) target := by
  rw [correctionComputeStep_eq_stages]
  rw [rawPseudoResidueLoadProgram_cleanEndpoint
    tail counterWidth p hpOdd.pos hpBound fixed hraw target]
  rw [counterCorrection_cleanEndpoint tail counterWidth p hpOdd hpBound
    fixed hclean (runtimePseudoResidue tail counterWidth p fixed) target]
  rw [signCorrectionProgram_cleanEndpoint tail counterWidth p hpOdd hpBound]
  rfl

/-- A logarithmic counter does not wrap the physical padding count when the
input is positive: at least one of the `2n` rounds is an active Kaliski update,
so strictly fewer than `2n` rounds increment the counter. -/
theorem fixedRoundPaddingSteps_lt_counterCapacity
    (tail counterWidth p input : Nat)
    (hinput : 0 < input)
    (hcapacity : 2 * tail.succ ≤ 2 ^ counterWidth) :
    let paddingSteps :=
      (RoundState.fixedRoundState tail.succ p input).paddingSteps
    paddingSteps < 2 ^ counterWidth := by
  dsimp only
  exact (RoundState.fixedRoundState_paddingSteps_lt_two_mul
    tail.succ p input (Nat.succ_pos tail) hinput).trans_le hcapacity

/-- The physical counter and coefficient readout agree with the registered
source trace once the no-wrap capacity condition is discharged. -/
theorem correctionCompute_correctedResidue
    (tail counterWidth p input : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (hsource :
      RoundState.fromRegisters tail.succ counterWidth
          (MK.Circuit.dataRegisters tail counterWidth fixed)
          (RoundState.fixedRoundState tail.succ p input).kaliskiSteps
          (RoundState.fixedRoundState tail.succ p input).paddingSteps =
        RoundState.fixedRoundState tail.succ p input)
    (hcounter :
      (MK.Circuit.dataRegisters
          tail counterWidth fixed).counter.val =
        (RoundState.fixedRoundState tail.succ p input).paddingSteps %
          2 ^ counterWidth)
    (hnoWrap :
      (RoundState.fixedRoundState tail.succ p input).paddingSteps <
        2 ^ counterWidth) :
    runtimeCorrectedResidue tail counterWidth p fixed =
      (Trace.ofInput tail.succ p input).correctedInverseResidue p := by
  have hrCoeff := congrArg RoundState.rCoeff hsource
  have hrCoeff' :
      (MK.Circuit.dataRegisters
          tail counterWidth fixed).rCoeff.val =
        (RoundState.fixedRoundState tail.succ p input).rCoeff := by
    simpa only [RoundState.fromRegisters] using hrCoeff
  have hcounter' :
      (MK.Circuit.dataRegisters
          tail counterWidth fixed).counter.val =
        (RoundState.fixedRoundState tail.succ p input).paddingSteps := by
    calc
      _ = (RoundState.fixedRoundState tail.succ p input).paddingSteps %
          2 ^ counterWidth := hcounter
      _ = _ := Nat.mod_eq_of_lt hnoWrap
  rw [Trace.ofInput_correctedInverseResidue_eq_fixedRoundState]
  simp only [runtimeCorrectedResidue, runtimePseudoResidue,
    RoundState.correctedInverseResidue,
    RoundState.correctionFactor, RoundState.correctionRounds,
    RoundState.pseudoInverseResidue, hcounter', hrCoeff']

/-- Full source-facing correction endpoint.  This theorem is a rewrite of the
physical program result, not a trace-selected program construction. -/
theorem correctionCompute_signedResidue
    (tail counterWidth p input : Nat) (hpOdd : Odd p)
    (hpBound : p < 2 ^ tail.succ)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (hclean : MK.Circuit.PhysicalWorkspaceClean
      tail counterWidth fixed)
    (hsource :
      RoundState.fromRegisters tail.succ counterWidth
          (MK.Circuit.dataRegisters tail counterWidth fixed)
          (RoundState.fixedRoundState tail.succ p input).kaliskiSteps
          (RoundState.fixedRoundState tail.succ p input).paddingSteps =
        RoundState.fixedRoundState tail.succ p input)
    (hcounter :
      (MK.Circuit.dataRegisters
          tail counterWidth fixed).counter.val =
        (RoundState.fixedRoundState tail.succ p input).paddingSteps %
          2 ^ counterWidth)
    (hnoWrap :
      (RoundState.fixedRoundState tail.succ p input).paddingSteps <
        2 ^ counterWidth)
    (target : ZMod p) :
    correctionComputeStep tail counterWidth p hpOdd
        (cleanCorrectionRegisters tail counterWidth p fixed 0 target) =
      cleanCorrectionRegisters tail counterWidth p fixed
        ((Trace.ofInput tail.succ p input).signedCorrectedInverseResidue p)
        target := by
  have hrCoeff := congrArg RoundState.rCoeff hsource
  have hraw :
      (MK.Circuit.dataRegisters
        tail counterWidth fixed).rCoeff.val < 2 * p := by
    have hrCoeff' :
        (MK.Circuit.dataRegisters
            tail counterWidth fixed).rCoeff.val =
          (RoundState.fixedRoundState tail.succ p input).rCoeff := by
      simpa only [RoundState.fromRegisters] using hrCoeff
    rw [hrCoeff']
    exact RoundState.fixedRoundState_rCoeff_lt_two_mul_modulus
      tail.succ p input hpOdd.pos
  have hcorrected := correctionCompute_correctedResidue
    tail counterWidth p input fixed hsource hcounter hnoWrap
  have hsigned :
      runtimeSignedCorrectedResidue tail counterWidth p fixed =
        (Trace.ofInput tail.succ p input).signedCorrectedInverseResidue p := by
    rw [runtimeSignedCorrectedResidue,
      Trace.signedCorrectedInverseResidue_eq_neg_corrected, hcorrected]
  simpa only [hsigned] using
    correctionCompute_cleanEndpoint tail counterWidth p hpOdd hpBound
      fixed hclean hraw target

/-! ## Staged target transfer -/

private theorem swapTargetStep_cleanEndpoint
    (tail counterWidth p : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (value : PlainAdder.Word tail.succ)
    (publicWord : Word tail.succ) :
    EncodedBit.Word.swapStep
        (publicTargetWord tail counterWidth)
        (reductionTargetLowWord tail counterWidth)
        (publicTarget_reductionTargetLow_ne tail counterWidth)
        (((fixed,
            MAU.Multiplication.Accumulate.VBECircuit.cleanState
              tail.succ p value 0), publicWord) : Registers tail counterWidth) =
      ((fixed,
          MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
            value 0 (p : PlainAdder.Word tail.succ)
            (MAU.Addition.VBECircuit.widenWord tail.succ
              (publicWord.val : PlainAdder.Word tail.succ)) false),
        0) := by
  let before : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.cleanState tail.succ p value 0),
      publicWord)
  let step := EncodedBit.Word.swapStep
    (publicTargetWord tail counterWidth)
    (reductionTargetLowWord tail counterWidth)
    (publicTarget_reductionTargetLow_ne tail counterWidth)
  have hfixed : (step before).1.1 = fixed := by
    exact swapStep_preserves_projection
      (publicTargetWord tail counterWidth)
      (reductionTargetLowWord tail counterWidth)
      (publicTarget_reductionTargetLow_ne tail counterWidth)
      (fun x => x.1.1) (fun _ _ => rfl) (fun _ _ => rfl) before
  have hmultiplicand : (step before).1.2.multiplicand = value := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using
      swapStep_preserves_projection
        (publicTargetWord tail counterWidth)
        (reductionTargetLowWord tail counterWidth)
        (publicTarget_reductionTargetLow_ne tail counterWidth)
        (fun x => x.1.2.multiplicand)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  have hactive :
      (step before).1.2.arithmetic.activeSource =
        MAU.Addition.VBECircuit.widenWord tail.succ
          (0 : PlainAdder.Word tail.succ) := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      swapStep_preserves_projection
        (publicTargetWord tail counterWidth)
        (reductionTargetLowWord tail counterWidth)
        (publicTarget_reductionTargetLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.activeSource)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  have htarget :
      (step before).1.2.arithmetic.target =
        MAU.Addition.VBECircuit.widenWord tail.succ
          (publicWord.val : PlainAdder.Word tail.succ) := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    by_cases hlow : bit.val < tail.succ
    · let low : Fin tail.succ := ⟨bit.val, hlow⟩
      have hbit :
          bit = (⟨low.val, by
            omega⟩ : Fin (tail.succ + 1)) := by
        apply Fin.ext
        rfl
      rw [hbit]
      have hread := congrFun
        (EncodedBit.Word.swapStep_get_right_word
          (publicTargetWord tail counterWidth)
          (reductionTargetLowWord tail counterWidth)
          (publicTarget_reductionTargetLow_ne tail counterWidth)
          (publicTarget_pairwise_ne tail counterWidth)
          (reductionTargetLow_pairwise_ne tail counterWidth)
          (publicTarget_reductionTargetLow_cross_ne tail counterWidth)
          before) low
      rw [← MAU.Multiplication.Accumulate.VBECircuit.targetBit_get]
      simp only [MAU.Addition.VBECircuit.widenWord_val,
        ZMod.val_natCast_of_lt publicWord.isLt]
      change
        ((reductionTargetLowWord tail counterWidth).bit low).get
            (step before) = publicWord.val.testBit low.val
      simpa only [step, publicTargetWord_get] using hread
    · have hlast : bit = Fin.last tail.succ := by
        apply Fin.ext
        have hbitLt := bit.isLt
        change bit.val < tail.succ + 1 at hbitLt
        simp only [Fin.val_last]
        omega
      rw [hlast]
      have hread := EncodedBit.Word.swapStep_get_observed_of_swap_ne
        (publicTargetWord tail counterWidth)
        (reductionTargetLowWord tail counterWidth)
        (publicTarget_reductionTargetLow_ne tail counterWidth)
        ((reductionTargetWord tail counterWidth).bit (Fin.last tail.succ))
        (publicTarget_reductionTargetHigh_ne tail counterWidth)
        (reductionTargetLow_reductionTargetHigh_ne tail counterWidth)
        before
      have hpublicHigh : publicWord.val.testBit tail.succ = false :=
        Nat.testBit_lt_two_pow publicWord.isLt
      have hrightHigh :
          (MAU.Addition.VBECircuit.widenWord tail.succ
              (publicWord.val : PlainAdder.Word tail.succ)).val.testBit
              (Fin.last tail.succ).val = false := by
        simp [hpublicHigh]
      rw [← MAU.Multiplication.Accumulate.VBECircuit.targetBit_get]
      change
        ((reductionTargetWord tail counterWidth).bit
            (Fin.last tail.succ)).get (step before) =
          (MAU.Addition.VBECircuit.widenWord tail.succ
            (publicWord.val : PlainAdder.Word tail.succ)).val.testBit
            (Fin.last tail.succ).val
      rw [hrightHigh, hread]
      change
        (MAU.Multiplication.Accumulate.VBECircuit.targetBit tail.succ
          (Fin.last tail.succ)).get
            (MAU.Multiplication.Accumulate.VBECircuit.cleanState
              tail.succ p value 0) = false
      rw [MAU.Multiplication.Accumulate.VBECircuit.targetBit_get]
      simp [MAU.Multiplication.Accumulate.VBECircuit.cleanState,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState]
  have hcarry : (step before).1.2.arithmetic.carry = false := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      swapStep_preserves_projection
        (publicTargetWord tail counterWidth)
        (reductionTargetLowWord tail counterWidth)
        (publicTarget_reductionTargetLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.carry)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  have hparked :
      (step before).1.2.arithmetic.parkedSource =
        (p : PlainAdder.Word tail.succ) := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      swapStep_preserves_projection
        (publicTargetWord tail counterWidth)
        (reductionTargetLowWord tail counterWidth)
        (publicTarget_reductionTargetLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.parkedSource)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  have hcarryWork :
      (step before).1.2.arithmetic.carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
          (MAU.Addition.VBECircuit.AdderWidth tail.succ) := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      swapStep_preserves_projection
        (publicTargetWord tail counterWidth)
        (reductionTargetLowWord tail counterWidth)
        (publicTarget_reductionTargetLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.carryWork)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  have hflag : (step before).1.2.arithmetic.reductionFlag = false := by
    simpa only [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      swapStep_preserves_projection
        (publicTargetWord tail counterWidth)
        (reductionTargetLowWord tail counterWidth)
        (publicTarget_reductionTargetLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.reductionFlag)
        (fun _ _ => rfl) (fun _ _ => rfl) before
  have hpublic : (step before).2 = 0 := by
    apply word_eq_of_testBit_eq
    intro bit
    have hread := congrFun
      (EncodedBit.Word.swapStep_get_left_word
        (publicTargetWord tail counterWidth)
        (reductionTargetLowWord tail counterWidth)
        (publicTarget_reductionTargetLow_ne tail counterWidth)
        (publicTarget_pairwise_ne tail counterWidth)
        (reductionTargetLow_pairwise_ne tail counterWidth)
        (publicTarget_reductionTargetLow_cross_ne tail counterWidth)
        before) bit
    rw [← publicTargetWord_get tail counterWidth bit (step before)]
    rw [hread]
    simp [before, MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState]
  change step before = _
  apply Prod.ext
  · apply Prod.ext
    · exact hfixed
    · apply
        (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv
          tail.succ).injective
      change
        ((step before).1.2.multiplicand,
            (step before).1.2.arithmetic) =
          (value, MAU.Addition.VBECircuit.sourceSwapCleanState tail.succ
            0 (p : PlainAdder.Word tail.succ)
            (MAU.Addition.VBECircuit.widenWord tail.succ
              (publicWord.val : PlainAdder.Word tail.succ)) false)
      rw [hmultiplicand]
      congr 1
      apply (MAU.Addition.VBECircuit.registersEquiv tail.succ).injective
      simp [MAU.Addition.VBECircuit.registersEquiv,
        MAU.Addition.VBECircuit.sourceSwapCleanState,
        hactive, htarget, hcarry, hparked, hcarryWork, hflag]
  · exact hpublic

private theorem copySourceStep_cleanEndpoint
    (tail counterWidth p : Nat)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (value accumulator : PlainAdder.Word tail.succ)
    (publicWord : Word tail.succ) :
    EncodedBit.Word.xorIntoStep
        (correctionValueWord tail counterWidth)
        (targetAddSourceLowWord tail counterWidth)
        (correctionValue_targetAddSourceLow_ne tail counterWidth)
        (((fixed,
            MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
              value 0 (p : PlainAdder.Word tail.succ)
              (MAU.Addition.VBECircuit.widenWord tail.succ accumulator)
              false), publicWord) : Registers tail counterWidth) =
      ((fixed,
          MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
            value value (p : PlainAdder.Word tail.succ)
            (MAU.Addition.VBECircuit.widenWord tail.succ accumulator)
            false), publicWord) := by
  let before : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          value 0 (p : PlainAdder.Word tail.succ)
          (MAU.Addition.VBECircuit.widenWord tail.succ accumulator) false),
      publicWord)
  let step := EncodedBit.Word.xorIntoStep
    (correctionValueWord tail counterWidth)
    (targetAddSourceLowWord tail counterWidth)
    (correctionValue_targetAddSourceLow_ne tail counterWidth)
  have hfixed : (step before).1.1 = fixed := by
    exact xorIntoStep_preserves_projection
      (correctionValueWord tail counterWidth)
      (targetAddSourceLowWord tail counterWidth)
      (correctionValue_targetAddSourceLow_ne tail counterWidth)
      (fun x => x.1.1) (fun _ _ => rfl) before
  have hpublic : (step before).2 = publicWord := by
    exact xorIntoStep_preserves_projection
      (correctionValueWord tail counterWidth)
      (targetAddSourceLowWord tail counterWidth)
      (correctionValue_targetAddSourceLow_ne tail counterWidth)
      (fun x => x.2) (fun _ _ => rfl) before
  have hmultiplicand : (step before).1.2.multiplicand = value := by
    simpa only [before,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState] using
      xorIntoStep_preserves_projection
        (correctionValueWord tail counterWidth)
        (targetAddSourceLowWord tail counterWidth)
        (correctionValue_targetAddSourceLow_ne tail counterWidth)
        (fun x => x.1.2.multiplicand) (fun _ _ => rfl) before
  have hactive :
      (step before).1.2.arithmetic.activeSource =
        MAU.Addition.VBECircuit.widenWord tail.succ value := by
    apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro bit
    by_cases hlow : bit.val < tail.succ
    · let low : Fin tail.succ := ⟨bit.val, hlow⟩
      have hbit :
          bit = (⟨low.val, by omega⟩ : Fin (tail.succ + 1)) := by
        apply Fin.ext
        rfl
      rw [hbit]
      have hread := EncodedBit.Word.xorIntoStep_get_target
        (correctionValueWord tail counterWidth)
        (targetAddSourceLowWord tail counterWidth)
        (correctionValue_targetAddSourceLow_ne tail counterWidth) low
        (fun other hne =>
          targetAddSourceLow_pairwise_ne
            tail counterWidth other low hne)
        (fun other => Ne.symm
          (correctionValue_targetAddSourceLow_cross_ne
            tail counterWidth low other)) before
      have hzero :
          ((targetAddSourceLowWord tail counterWidth).bit low).get before =
            false := by
        simp [before,
          MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
          MAU.Addition.VBECircuit.sourceSwapCleanState]
      have hsource :
          ((correctionValueWord tail counterWidth).bit low).get before =
            value.val.testBit low.val := by
        simp [before,
          MAU.Multiplication.Accumulate.VBECircuit.workspaceState]
      rw [hzero, hsource] at hread
      rw [← MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get]
      simp only [MAU.Addition.VBECircuit.widenWord_val]
      change
        ((targetAddSourceLowWord tail counterWidth).bit low).get
            (step before) = value.val.testBit low.val
      cases hvalueBit : value.val.testBit low.val <;>
        simpa [step, hvalueBit] using hread
    · have hlast : bit = Fin.last tail.succ := by
        apply Fin.ext
        have hbitLt := bit.isLt
        change bit.val < tail.succ + 1 at hbitLt
        simp only [Fin.val_last]
        omega
      rw [hlast]
      have hread := EncodedBit.Word.xorIntoStep_get_observed_of_target_ne
        (correctionValueWord tail counterWidth)
        (targetAddSourceLowWord tail counterWidth)
        (correctionValue_targetAddSourceLow_ne tail counterWidth)
        (liftWorkBit tail counterWidth
          (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit
            tail.succ (Fin.last tail.succ)))
        (targetAddSourceLow_targetAddSourceHigh_ne tail counterWidth)
        before
      have hvalueHigh : value.val.testBit tail.succ = false :=
        Nat.testBit_lt_two_pow (ZMod.val_lt value)
      have hrightHigh :
          (MAU.Addition.VBECircuit.widenWord tail.succ value).val.testBit
              (Fin.last tail.succ).val = false := by
        simp [hvalueHigh]
      rw [← MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get]
      change
        (liftWorkBit tail counterWidth
          (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit tail.succ
            (Fin.last tail.succ))).get (step before) =
          (MAU.Addition.VBECircuit.widenWord tail.succ value).val.testBit
            (Fin.last tail.succ).val
      rw [hrightHigh, hread]
      change
        (MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit tail.succ
          (Fin.last tail.succ)).get
            (MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
              value 0 (p : PlainAdder.Word tail.succ)
              (MAU.Addition.VBECircuit.widenWord tail.succ accumulator)
              false) = false
      rw [MAU.Multiplication.Accumulate.VBECircuit.activeSourceBit_get]
      simp [MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
        MAU.Addition.VBECircuit.sourceSwapCleanState]
  have htarget :
      (step before).1.2.arithmetic.target =
        MAU.Addition.VBECircuit.widenWord tail.succ accumulator := by
    simpa only [before,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (correctionValueWord tail counterWidth)
        (targetAddSourceLowWord tail counterWidth)
        (correctionValue_targetAddSourceLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.target) (fun _ _ => rfl) before
  have hcarry : (step before).1.2.arithmetic.carry = false := by
    simpa only [before,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (correctionValueWord tail counterWidth)
        (targetAddSourceLowWord tail counterWidth)
        (correctionValue_targetAddSourceLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.carry) (fun _ _ => rfl) before
  have hparked :
      (step before).1.2.arithmetic.parkedSource =
        (p : PlainAdder.Word tail.succ) := by
    simpa only [before,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (correctionValueWord tail counterWidth)
        (targetAddSourceLowWord tail counterWidth)
        (correctionValue_targetAddSourceLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.parkedSource) (fun _ _ => rfl) before
  have hcarryWork :
      (step before).1.2.arithmetic.carryWork =
        PlainAdder.Schedule.PowerOfTwo.cleanCarryWork
          (MAU.Addition.VBECircuit.AdderWidth tail.succ) := by
    simpa only [before,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (correctionValueWord tail counterWidth)
        (targetAddSourceLowWord tail counterWidth)
        (correctionValue_targetAddSourceLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.carryWork) (fun _ _ => rfl) before
  have hflag : (step before).1.2.arithmetic.reductionFlag = false := by
    simpa only [before,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      MAU.Addition.VBECircuit.sourceSwapCleanState] using
      xorIntoStep_preserves_projection
        (correctionValueWord tail counterWidth)
        (targetAddSourceLowWord tail counterWidth)
        (correctionValue_targetAddSourceLow_ne tail counterWidth)
        (fun x => x.1.2.arithmetic.reductionFlag) (fun _ _ => rfl) before
  change step before = _
  apply Prod.ext
  · apply Prod.ext
    · exact hfixed
    · apply
        (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv
          tail.succ).injective
      change
        ((step before).1.2.multiplicand,
            (step before).1.2.arithmetic) =
          (value, MAU.Addition.VBECircuit.sourceSwapCleanState tail.succ
            value (p : PlainAdder.Word tail.succ)
            (MAU.Addition.VBECircuit.widenWord tail.succ accumulator)
            false)
      rw [hmultiplicand]
      congr 1
      apply (MAU.Addition.VBECircuit.registersEquiv tail.succ).injective
      simp [MAU.Addition.VBECircuit.registersEquiv,
        MAU.Addition.VBECircuit.sourceSwapCleanState,
        hactive, htarget, hcarry, hparked, hcarryWork, hflag]
  · exact hpublic

/-- Complete base-gate schedule for swapping the target in, copying the
source, adding, and uncomputing both transfers. -/
def stagedTargetAddGates (tail counterWidth p : Nat) :
    List (EncodedBit.GateSpec (encoding tail counterWidth)) :=
  let swapTarget := EncodedBit.Word.swapGates
    (publicTargetWord tail counterWidth)
    (reductionTargetLowWord tail counterWidth)
    (publicTarget_reductionTargetLow_ne tail counterWidth)
  let copySource := EncodedBit.Word.xorIntoGates
    (correctionValueWord tail counterWidth)
    (targetAddSourceLowWord tail counterWidth)
    (correctionValue_targetAddSourceLow_ne tail counterWidth)
  let add := liftedWorkModularAddGates tail counterWidth p
  swapTarget ++ copySource ++ add ++ copySource.reverse ++ swapTarget.reverse

/-- Swap the public target into the shared VBE target, add corrected scratch
modulo `p`, clear the staged source, and swap the result back out. -/
def stagedTargetAddProgram (tail counterWidth p : Nat) :
    UnitaryCircuit (Qubits (encoding tail counterWidth).width) :=
  EncodedBit.GateSpec.programList
    (stagedTargetAddGates tail counterWidth p)

/-- Folded action of the complete staged target-add gate schedule. -/
def stagedTargetAddStep (tail counterWidth p : Nat) :
    Registers tail counterWidth -> Registers tail counterWidth :=
  EncodedBit.GateSpec.stepList
    (stagedTargetAddGates tail counterWidth p)

/-- The actual staged target-add circuit realizes its complete gate list. -/
theorem stagedTargetAdd_realizes (tail counterWidth p : Nat) :
    UnitaryCircuit.Realizes (encoding tail counterWidth)
      (stagedTargetAddProgram tail counterWidth p)
      (stagedTargetAddStep tail counterWidth p) :=
  EncodedBit.GateSpec.realizesList
    (stagedTargetAddGates tail counterWidth p)

/-- The staged transfer adds correction scratch into the public target while
restoring the complete VBE workspace and leaving correction scratch intact. -/
theorem stagedTargetAddProgram_cleanEndpoint
    (tail counterWidth p : Nat)
    (hpPos : 0 < p) (hpBound : p < 2 ^ tail.succ)
    (fixed : MK.Circuit.RegistersWithRouteHistory
      tail.succ counterWidth)
    (value target : ZMod p) :
    stagedTargetAddStep tail counterWidth p
        (cleanCorrectionRegisters tail counterWidth p fixed value target) =
      cleanCorrectionRegisters tail counterWidth p fixed value
        (target + value) := by
  let _ : NeZero p := ⟨Nat.ne_of_gt hpPos⟩
  let valueWord : PlainAdder.Word tail.succ := value.val
  let targetWord : PlainAdder.Word tail.succ := target.val
  let sum : ZMod p := target + value
  let sumWord : PlainAdder.Word tail.succ := sum.val
  have hvalueBound : value.val < 2 ^ tail.succ :=
    (ZMod.val_lt value).trans hpBound
  have htargetBound : target.val < 2 ^ tail.succ :=
    (ZMod.val_lt target).trans hpBound
  have hsumBound : sum.val < 2 ^ tail.succ :=
    (ZMod.val_lt sum).trans hpBound
  let targetPublic : Word tail.succ := ⟨target.val, htargetBound⟩
  let sumPublic : Word tail.succ := ⟨sum.val, hsumBound⟩
  have hvalueWordVal : valueWord.val = value.val := by
    exact ZMod.val_natCast_of_lt hvalueBound
  have htargetWordVal : targetWord.val = target.val := by
    exact ZMod.val_natCast_of_lt htargetBound
  have hsumWordVal : sumWord.val = sum.val := by
    exact ZMod.val_natCast_of_lt hsumBound
  have hsum : (valueWord.val + targetWord.val) % p = sum.val := by
    rw [hvalueWordVal, htargetWordVal]
    simp only [sum, ZMod.val_add]
    rw [Nat.add_comm]
  have hwidenSum :
      MAU.Addition.VBECircuit.widenWord tail.succ sumWord =
        (sum.val : PlainAdder.Word
          (MAU.Addition.VBECircuit.AdderWidth tail.succ)) := by
    simpa only [sumWord] using
      MAU.Multiplication.Accumulate.VBECircuit.widenWord_natCast_of_lt
        tail.succ sum.val hsumBound
  let swapTargetGates := EncodedBit.Word.swapGates
    (publicTargetWord tail counterWidth)
    (reductionTargetLowWord tail counterWidth)
    (publicTarget_reductionTargetLow_ne tail counterWidth)
  let copySourceGates := EncodedBit.Word.xorIntoGates
    (correctionValueWord tail counterWidth)
    (targetAddSourceLowWord tail counterWidth)
    (correctionValue_targetAddSourceLow_ne tail counterWidth)
  let addGates := liftedWorkModularAddGates tail counterWidth p
  let swapTargetStep := EncodedBit.Word.swapStep
    (publicTargetWord tail counterWidth)
    (reductionTargetLowWord tail counterWidth)
    (publicTarget_reductionTargetLow_ne tail counterWidth)
  let copySourceStep := EncodedBit.Word.xorIntoStep
    (correctionValueWord tail counterWidth)
    (targetAddSourceLowWord tail counterWidth)
    (correctionValue_targetAddSourceLow_ne tail counterWidth)
  let addStep := liftedWorkModularAddStep tail counterWidth p
  let s0 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.cleanState
          tail.succ p valueWord 0), targetPublic)
  let s1 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          valueWord 0 (p : PlainAdder.Word tail.succ)
          (MAU.Addition.VBECircuit.widenWord tail.succ targetWord) false),
      0)
  let s2 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          valueWord valueWord (p : PlainAdder.Word tail.succ)
          (MAU.Addition.VBECircuit.widenWord tail.succ targetWord) false),
      0)
  let s3 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          valueWord valueWord (p : PlainAdder.Word tail.succ)
          (MAU.Addition.VBECircuit.widenWord tail.succ sumWord) false),
      0)
  let s4 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
          valueWord 0 (p : PlainAdder.Word tail.succ)
          (MAU.Addition.VBECircuit.widenWord tail.succ sumWord) false),
      0)
  let s5 : Registers tail counterWidth :=
    ((fixed,
        MAU.Multiplication.Accumulate.VBECircuit.cleanState
          tail.succ p valueWord 0), sumPublic)
  have hswapInitial : swapTargetStep s0 = s1 := by
    simpa only [swapTargetStep, s0, s1, targetPublic, targetWord] using
      swapTargetStep_cleanEndpoint tail counterWidth p fixed
        valueWord targetPublic
  have hcopyInitial : copySourceStep s1 = s2 := by
    simpa only [copySourceStep, s1, s2] using
      copySourceStep_cleanEndpoint tail counterWidth p fixed
        valueWord targetWord 0
  have hadd : addStep s2 = s3 := by
    let beforeWork :=
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
        valueWord valueWord (p : PlainAdder.Word tail.succ)
        (MAU.Addition.VBECircuit.widenWord tail.succ targetWord) false
    let afterWork :=
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState tail.succ
        valueWord valueWord (p : PlainAdder.Word tail.succ)
        (MAU.Addition.VBECircuit.widenWord tail.succ sumWord) false
    have hvalueLt : valueWord.val < p := by
      simpa only [hvalueWordVal] using ZMod.val_lt value
    have htargetLt : targetWord.val < p := by
      simpa only [htargetWordVal] using ZMod.val_lt target
    have hstep :
        MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
            tail.succ p beforeWork = afterWork := by
      apply (MAU.Multiplication.Accumulate.VBECircuit.registersEquiv
        tail.succ).injective
      change
        (valueWord,
            MAU.Addition.VBECircuit.modularAddStep tail.succ p
              (MAU.Addition.VBECircuit.sourceSwapCleanState tail.succ
                valueWord (p : PlainAdder.Word tail.succ)
                (MAU.Addition.VBECircuit.widenWord tail.succ targetWord)
                false)) =
          (valueWord,
            MAU.Addition.VBECircuit.sourceSwapCleanState tail.succ
              valueWord (p : PlainAdder.Word tail.succ)
              (MAU.Addition.VBECircuit.widenWord tail.succ sumWord) false)
      rw [MAU.Addition.VBECircuit.modularAddStep_cleanEndpoint
        tail.succ p valueWord targetWord hpPos hpBound hvalueLt htargetLt]
      simp only [hsum, hwidenSum]
    dsimp only [addStep]
    rw [liftedWorkModularAddStep_eq_liftWorkStep]
    change ((fixed,
      MAU.Multiplication.Accumulate.VBECircuit.liftedModularAddStep
        tail.succ p beforeWork), 0) = _
    rw [hstep]
  have hcopyFinal : copySourceStep s4 = s3 := by
    simpa only [copySourceStep, s3, s4] using
      copySourceStep_cleanEndpoint tail counterWidth p fixed
        valueWord sumWord 0
  have hinverseCopy :
      EncodedBit.GateSpec.stepList copySourceGates.reverse s3 = s4 := by
    rw [← show EncodedBit.GateSpec.stepList copySourceGates s4 = s3 by
      change copySourceStep s4 = s3
      exact hcopyFinal]
    exact EncodedBit.GateSpec.stepList_reverse_stepList copySourceGates s4
  have hswapFinal : swapTargetStep s5 = s4 := by
    simpa only [swapTargetStep, s4, s5, sumPublic, sumWord] using
      swapTargetStep_cleanEndpoint tail counterWidth p fixed
        valueWord sumPublic
  have hinverseSwap :
      EncodedBit.GateSpec.stepList swapTargetGates.reverse s4 = s5 := by
    rw [← show EncodedBit.GateSpec.stepList swapTargetGates s5 = s4 by
      change swapTargetStep s5 = s4
      exact hswapFinal]
    exact EncodedBit.GateSpec.stepList_reverse_stepList swapTargetGates s5
  have hs0 :
      cleanCorrectionRegisters tail counterWidth p fixed value target = s0 := by
    simp [cleanCorrectionRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      s0, valueWord, targetPublic, Nat.mod_eq_of_lt htargetBound]
  have hs5 :
      cleanCorrectionRegisters tail counterWidth p fixed value
          (target + value) = s5 := by
    simp [cleanCorrectionRegisters,
      MAU.Multiplication.Accumulate.VBECircuit.cleanState,
      MAU.Multiplication.Accumulate.VBECircuit.workspaceState,
      s5, sum, valueWord, sumPublic, Nat.mod_eq_of_lt hsumBound]
  rw [hs0, hs5]
  change EncodedBit.GateSpec.stepList
    (swapTargetGates ++ copySourceGates ++ addGates ++
      copySourceGates.reverse ++ swapTargetGates.reverse) s0 = s5
  simp only [EncodedBit.GateSpec.stepList_append]
  rw [show EncodedBit.GateSpec.stepList swapTargetGates s0 = s1 by
    change swapTargetStep s0 = s1
    exact hswapInitial]
  rw [show EncodedBit.GateSpec.stepList copySourceGates s1 = s2 by
    change copySourceStep s1 = s2
    exact hcopyInitial]
  rw [show EncodedBit.GateSpec.stepList addGates s2 = s3 by
    change addStep s2 = s3
    exact hadd,
    hinverseCopy, hinverseSwap]

end
end Correction
end MK
end MAU.Inversion
end QuantumAlg

end
