/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.ArithmeticLift
import all QuantumAlg.Primitives.Arithmetic.Comparator

/-!
# Width-neutral Montgomery multiplication on the in-place point carrier

Montgomery multiplication is implemented with the same compact arithmetic
state used by inversion.  The retained coefficient is first divided by
`R = 2^n` by running the certified modular-doubling ledger backwards `n`
times.  The multiplier bits then control modular additions while each round
doubles the coefficient again.  Consequently the coefficient is restored,
the public target receives one Montgomery product, and no register is added to
the 2587-qubit P-256 carrier.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace MontgomeryMultiplication

noncomputable section

open Nat.FixedWidth
open MAU.Inversion
open MAU.Inversion.MK
open MAU.Inversion.MK.Circuit

/-- Canonical modular half.  For an odd modulus, doubling this residue returns
the input residue. -/
def halfResidueWord (fieldTail p : Nat) (_hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (coefficient : Word (fieldTail.succ + 1)) :
    Word (fieldTail.succ + 1) :=
  ⟨if coefficient.val % 2 = 0 then coefficient.val / 2
    else (coefficient.val + p) / 2, by
    split_ifs with heven
    · have hcoefficient : coefficient.val < 2 ^ (fieldTail.succ + 1) :=
        coefficient.isLt
      omega
    · have hmodulus : p < 2 ^ (fieldTail.succ + 1) := by
        have hpow : 2 ^ fieldTail.succ < 2 ^ (fieldTail.succ + 1) :=
          Nat.pow_lt_pow_right (by decide) fieldTail.succ.lt_succ_self
        exact hp.trans hpow
      have hsum : coefficient.val + p < 2 * 2 ^ (fieldTail.succ + 1) := by
        omega
      omega⟩

@[simp] lemma halfResidueWord_val (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (coefficient : Word (fieldTail.succ + 1)) :
    (halfResidueWord fieldTail p hpPos hp coefficient).val =
      if coefficient.val % 2 = 0 then coefficient.val / 2
      else (coefficient.val + p) / 2 :=
  rfl

/-- A canonical residue remains canonical after modular halving. -/
lemma halfResidueWord_lt (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (coefficient : Word (fieldTail.succ + 1))
    (hcoefficient : coefficient.val < p) :
    (halfResidueWord fieldTail p hpPos hp coefficient).val < p := by
  rw [halfResidueWord_val]
  split_ifs with heven
  · omega
  · have hpMod : p % 2 = 1 := Nat.odd_iff.mp hpOdd
    have hcMod : coefficient.val % 2 = 1 := by omega
    have hsumEven : (coefficient.val + p) % 2 = 0 := by omega
    have htwice :
        2 * ((coefficient.val + p) / 2) = coefficient.val + p :=
      Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero _ hsumEven
    omega

/-- Modular doubling of the canonical half returns the original residue
exactly, not merely after a cast into the residue field. -/
lemma doublingResidueWord_halfResidueWord
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (coefficient : Word (fieldTail.succ + 1))
    (hcoefficient : coefficient.val < p) :
    CompactCorrection.doublingResidueWord fieldTail p hpPos hp
        (halfResidueWord fieldTail p hpPos hp coefficient) = coefficient := by
  apply Fin.ext
  rw [CompactCorrection.doublingResidueWord_val, halfResidueWord_val]
  split_ifs with heven
  · have htwice : 2 * (coefficient.val / 2) = coefficient.val :=
      Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero _ heven
    rw [htwice, Nat.mod_eq_of_lt hcoefficient]
  · have hpMod : p % 2 = 1 := Nat.odd_iff.mp hpOdd
    have hcMod : coefficient.val % 2 = 1 := by omega
    have hsumEven : (coefficient.val + p) % 2 = 0 := by omega
    have htwice :
        2 * ((coefficient.val + p) / 2) = coefficient.val + p :=
      Nat.BinaryArithmetic.two_mul_div_two_of_mod_two_eq_zero _ hsumEven
    rw [htwice, Nat.add_mod, Nat.mod_eq_of_lt hcoefficient]
    simp [Nat.mod_eq_of_lt hcoefficient]

/-- Running the literal doubling ledger backwards performs one canonical
modular halving while restoring the same borrowed arithmetic boundary. -/
lemma reverseDoublingStep_state
    (fieldTail counterWidth p : Nat)
    (base : MK.Compact.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : coefficient.val < p) :
    EncodedBit.GateSpec.stepList
        (CompactCorrection.doublingGates fieldTail counterWidth p).reverse
        (CompactCorrection.doublingState fieldTail counterWidth base coefficient
          (CompactCorrection.widenFixedWord fieldTail.succ 0) 0 ⟨p, hp⟩ false) =
      CompactCorrection.doublingState fieldTail counterWidth base
        (halfResidueWord fieldTail p hpPos hp coefficient)
        (CompactCorrection.widenFixedWord fieldTail.succ 0) 0 ⟨p, hp⟩ false := by
  let half := halfResidueWord fieldTail p hpPos hp coefficient
  have hhalf : half.val < p :=
    halfResidueWord_lt fieldTail p hpPos hp hpOdd coefficient hcoefficient
  have hforward := CompactCorrection.doublingStep_state
    fieldTail counterWidth p base half hpPos hp hpOdd hhalf
  have hdoubled :
      CompactCorrection.doublingResidueWord fieldTail p hpPos hp half =
        coefficient := by
    exact doublingResidueWord_halfResidueWord fieldTail p hpPos hp hpOdd
      coefficient hcoefficient
  have hinverse := EncodedBit.GateSpec.stepList_reverse_stepList
    (CompactCorrection.doublingGates fieldTail counterWidth p)
    (CompactCorrection.doublingState fieldTail counterWidth base half
      (CompactCorrection.widenFixedWord fieldTail.succ 0) 0 ⟨p, hp⟩ false)
  change EncodedBit.GateSpec.stepList
      (CompactCorrection.doublingGates fieldTail counterWidth p).reverse
      (CompactCorrection.doublingStep fieldTail counterWidth p
        (CompactCorrection.doublingState fieldTail counterWidth base half
          (CompactCorrection.widenFixedWord fieldTail.succ 0) 0 ⟨p, hp⟩ false)) = _ at hinverse
  rw [hforward, hdoubled] at hinverse
  exact hinverse

/-- Repeated reverse-doubling ledger used to divide a variable coefficient by
the Montgomery radix before the shift-and-add pass. -/
def inverseScaleGates (fieldTail counterWidth p : Nat) :
    Nat → List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth))
  | 0 => []
  | rounds + 1 =>
      inverseScaleGates fieldTail counterWidth p rounds ++
        (CompactCorrection.doublingGates fieldTail counterWidth p).reverse

/-- Pure residue recurrence corresponding to `inverseScaleGates`. -/
def inverseScaleWord (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) :
    Nat → Word (fieldTail.succ + 1) → Word (fieldTail.succ + 1)
  | 0, coefficient => coefficient
  | rounds + 1, coefficient =>
      halfResidueWord fieldTail p hpPos hp
        (inverseScaleWord fieldTail p hpPos hp rounds coefficient)

/-- Every intermediate radix-division residue stays canonical. -/
lemma inverseScaleWord_lt
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p) :
    ∀ rounds (coefficient : Word (fieldTail.succ + 1)),
      coefficient.val < p →
      (inverseScaleWord fieldTail p hpPos hp rounds coefficient).val < p := by
  intro rounds
  induction rounds with
  | zero =>
      intro coefficient hcoefficient
      exact hcoefficient
  | succ rounds ih =>
      intro coefficient hcoefficient
      exact halfResidueWord_lt fieldTail p hpPos hp hpOdd _
        (ih coefficient hcoefficient)

/-- The repeated literal reverse ledger implements exact radix division and
returns every borrowed arithmetic field to its clean boundary. -/
lemma inverseScaleGates_stepList
    (fieldTail counterWidth p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p) :
    ∀ rounds (base : MK.Compact.Registers fieldTail.succ counterWidth)
      (coefficient : Word (fieldTail.succ + 1)),
      coefficient.val < p →
      EncodedBit.GateSpec.stepList
          (inverseScaleGates fieldTail counterWidth p rounds)
          (CompactCorrection.doublingState fieldTail counterWidth base
            coefficient (CompactCorrection.widenFixedWord fieldTail.succ 0) 0
              ⟨p, hp⟩ false) =
        CompactCorrection.doublingState fieldTail counterWidth base
          (inverseScaleWord fieldTail p hpPos hp rounds coefficient)
          (CompactCorrection.widenFixedWord fieldTail.succ 0) 0 ⟨p, hp⟩ false := by
  intro rounds
  induction rounds with
  | zero =>
      intro base coefficient hcoefficient
      rfl
  | succ rounds ih =>
      intro base coefficient hcoefficient
      rw [inverseScaleGates, EncodedBit.GateSpec.stepList_append]
      rw [ih base coefficient hcoefficient]
      exact reverseDoublingStep_state fieldTail counterWidth p base _ hpPos hp
        hpOdd (inverseScaleWord_lt fieldTail p hpPos hp hpOdd rounds coefficient
          hcoefficient)

/-! ## Bit-selected Montgomery accumulation -/

/-- Canonical point-carrier boundary used by multiplication: the coefficient
lives in compact `r`, the public target is the accumulator, and every borrowed
VBE arithmetic field is clean. -/
def multiplicationState (fieldTail counterWidth p : Nat)
    (hp : p < 2 ^ fieldTail.succ)
    (base : Layout.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (target : Word fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth :=
  { base with
    arithmetic := CompactCorrection.targetUpdateState fieldTail counterWidth
      base.arithmetic coefficient
      (CompactCorrection.widenFixedWord fieldTail.succ 0)
      (CompactCorrection.widenFixedWord fieldTail.succ 0) ⟨p, hp⟩ false target }

/-- Compact source ledger for one modular addition into the public target. -/
def targetAddSourceGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (MK.Compact.encoding fieldTail.succ counterWidth)) :=
  (CompactCorrection.targetUpdateGates fieldTail counterWidth p).reverse

/-- Width-neutral lift of one modular-add source ledger into the point
carrier. -/
def targetAddGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  ArithmeticLift.gates fieldTail.succ counterWidth
    (targetAddSourceGates fieldTail counterWidth p)

/-- The lifted modular-add ledger is disjoint from its clean path work bit. -/
lemma targetAddGates_bitDisjoint_path
    (fieldTail counterWidth p : Nat) :
    ∀ gate, gate ∈ targetAddGates fieldTail counterWidth p →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.liftArithmeticBit fieldTail.succ counterWidth
          (MK.Compact.pathBit fieldTail.succ counterWidth)) gate := by
  exact ArithmeticLift.gates_bitDisjoint_liftArithmeticBit
    fieldTail.succ counterWidth
    (MK.Compact.pathBit fieldTail.succ counterWidth)
    (targetAddSourceGates fieldTail counterWidth p)
    (CompactCorrection.targetUpdateReverseGates_bitDisjoint_path
      fieldTail counterWidth p)

/-- The lifted modular-add ledger is disjoint from every multiplier bit. -/
lemma targetAddGates_bitDisjoint_multiplier
    (fieldTail counterWidth p : Nat) (bit : Fin fieldTail.succ) :
    ∀ gate, gate ∈ targetAddGates fieldTail counterWidth p →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.mutableYBit fieldTail.succ counterWidth bit) gate :=
  ArithmeticLift.gates_bitDisjoint_mutableYBit fieldTail.succ counterWidth bit
    (targetAddSourceGates fieldTail counterWidth p)

/-- Clean-work control lift selecting one modular addition by one multiplier
bit. -/
def selectedAddGates (fieldTail counterWidth p : Nat)
    (bit : Fin fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  EncodedBit.GateSpec.controlledListWithWorkGates
    (Layout.mutableYBit fieldTail.succ counterWidth bit)
    (Layout.liftArithmeticBit fieldTail.succ counterWidth
      (MK.Compact.pathBit fieldTail.succ counterWidth))
    (targetAddGates fieldTail counterWidth p)
    (targetAddGates_bitDisjoint_multiplier fieldTail counterWidth p bit)
    (targetAddGates_bitDisjoint_path fieldTail counterWidth p)
    (Layout.mutableYBit_wire_ne_liftArithmeticBit
      fieldTail.succ counterWidth bit
      (MK.Compact.pathBit fieldTail.succ counterWidth))

/-- One selected-add ledger never reads or writes the persistent slope word. -/
lemma selectedAddGates_bitDisjoint_lambdaBit
    (fieldTail counterWidth p : Nat) (multiplierBit lambdaBit : Fin fieldTail.succ) :
    ∀ gate, gate ∈ selectedAddGates fieldTail counterWidth p multiplierBit →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldTail.succ counterWidth lambdaBit) gate := by
  exact EncodedBit.GateSpec.controlledListWithWorkGates_bitDisjoint
    (Layout.mutableYBit fieldTail.succ counterWidth multiplierBit)
    (Layout.liftArithmeticBit fieldTail.succ counterWidth
      (MK.Compact.pathBit fieldTail.succ counterWidth))
    (Layout.lambdaBit fieldTail.succ counterWidth lambdaBit)
    (targetAddGates fieldTail counterWidth p)
    (targetAddGates_bitDisjoint_multiplier fieldTail counterWidth p
      multiplierBit)
    (targetAddGates_bitDisjoint_path fieldTail counterWidth p)
    (Layout.mutableYBit_wire_ne_liftArithmeticBit fieldTail.succ counterWidth
      multiplierBit (MK.Compact.pathBit fieldTail.succ counterWidth))
    (Layout.mutableYBit_wire_ne_lambdaBit fieldTail.succ counterWidth
      multiplierBit lambdaBit)
    (Ne.symm (Layout.lambdaBit_wire_ne_liftArithmeticBit fieldTail.succ
      counterWidth lambdaBit
      (MK.Compact.pathBit fieldTail.succ counterWidth)))
    (ArithmeticLift.gates_bitDisjoint_lambdaBit fieldTail.succ counterWidth
      lambdaBit (targetAddSourceGates fieldTail counterWidth p))

/-- Folded action of one bit-selected modular addition. -/
def selectedAddStep (fieldTail counterWidth p : Nat)
    (bit : Fin fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (selectedAddGates fieldTail counterWidth p bit)

/-- One selected-add stage adds the canonical coefficient exactly when the
chosen multiplier bit is set.  The multiplier, clean path work, coefficient,
and complete borrowed VBE boundary are restored. -/
lemma selectedAddStep_state
    (fieldTail counterWidth p : Nat)
    (bit : Fin fieldTail.succ)
    (base : Layout.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (target : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hcoefficient : coefficient.val < p) (htarget : target.val < p)
    (hpath : base.arithmetic.shared.path = false) :
    selectedAddStep fieldTail counterWidth p bit
        (multiplicationState fieldTail counterWidth p hp base coefficient
          target) =
      multiplicationState fieldTail counterWidth p hp base coefficient
        (if base.mutableY.val.testBit bit.val then
          CompactCorrection.modularSumFixedWord fieldTail p hpPos hp target
            (CompactCorrection.truncateFixedWord fieldTail.succ coefficient)
        else target) := by
  let input := multiplicationState fieldTail counterWidth p hp base coefficient
    target
  let source := CompactCorrection.truncateFixedWord fieldTail.succ coefficient
  have hsource : source.val < p := by
    have hfit : coefficient.val < 2 ^ fieldTail.succ :=
      hcoefficient.trans hp
    simpa [source, CompactCorrection.truncateFixedWord,
      Nat.mod_eq_of_lt hfit] using hcoefficient
  have hwiden :
      CompactCorrection.widenFixedWord fieldTail.succ source = coefficient :=
    CompactCorrection.widenFixedWord_truncateFixedWord_of_lt
      fieldTail.succ coefficient (hcoefficient.trans hp)
  have hcontrol :
      (Layout.mutableYBit fieldTail.succ counterWidth bit).get input =
        base.mutableY.val.testBit bit.val := by
    simp [input, multiplicationState]
  have hwork :
      (Layout.liftArithmeticBit fieldTail.succ counterWidth
        (MK.Compact.pathBit fieldTail.succ counterWidth)).get input = false := by
    simp [input, multiplicationState, CompactCorrection.targetUpdateState,
      CompactCorrection.arithmeticState, hpath]
  cases hbit : base.mutableY.val.testBit bit.val with
  | false =>
      have hcontrolFalse :
          (Layout.mutableYBit fieldTail.succ counterWidth bit).get input =
            false := hcontrol.trans hbit
      have hselected :=
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_self_of_control_false
          (Layout.mutableYBit fieldTail.succ counterWidth bit)
          (Layout.liftArithmeticBit fieldTail.succ counterWidth
            (MK.Compact.pathBit fieldTail.succ counterWidth))
          (targetAddGates fieldTail counterWidth p)
          (targetAddGates_bitDisjoint_multiplier fieldTail counterWidth p bit)
          (targetAddGates_bitDisjoint_path fieldTail counterWidth p)
          (Layout.mutableYBit_wire_ne_liftArithmeticBit
            fieldTail.succ counterWidth bit
            (MK.Compact.pathBit fieldTail.succ counterWidth))
          input hcontrolFalse
      simpa [selectedAddStep, selectedAddGates,
        EncodedBit.GateSpec.controlledListWithWorkStep, input, hbit] using
        hselected
  | true =>
      have hcontrolTrue :
          (Layout.mutableYBit fieldTail.succ counterWidth bit).get input =
            true := hcontrol.trans hbit
      have hselected :=
        EncodedBit.GateSpec.controlledListWithWorkStep_eq_stepList_of_control_true
          (Layout.mutableYBit fieldTail.succ counterWidth bit)
          (Layout.liftArithmeticBit fieldTail.succ counterWidth
            (MK.Compact.pathBit fieldTail.succ counterWidth))
          (targetAddGates fieldTail counterWidth p)
          (targetAddGates_bitDisjoint_multiplier fieldTail counterWidth p bit)
          (targetAddGates_bitDisjoint_path fieldTail counterWidth p)
          (Layout.mutableYBit_wire_ne_liftArithmeticBit
            fieldTail.succ counterWidth bit
            (MK.Compact.pathBit fieldTail.succ counterWidth))
          input hcontrolTrue hwork
      have hlift := ArithmeticLift.gates_stepList fieldTail.succ counterWidth
        (targetAddSourceGates fieldTail counterWidth p) input
      have hadd := CompactCorrection.targetUpdateReverseStep_state
        fieldTail counterWidth p base.arithmetic source target hpPos hp hsource
        htarget
      have hraw :
          EncodedBit.GateSpec.stepList
              (targetAddGates fieldTail counterWidth p) input =
            multiplicationState fieldTail counterWidth p hp base coefficient
              (CompactCorrection.modularSumFixedWord fieldTail p hpPos hp
                target source) := by
        rw [targetAddGates]
        rw [ArithmeticLift.gates_stepList]
        simp only [input, multiplicationState]
        rw [show coefficient =
            CompactCorrection.widenFixedWord fieldTail.succ source by
          exact hwiden.symm]
        simpa [targetAddSourceGates,
          CompactCorrection.targetUpdateReverseStep] using hadd
      have hselected' : selectedAddStep fieldTail counterWidth p bit input =
          EncodedBit.GateSpec.stepList
            (targetAddGates fieldTail counterWidth p) input := by
        simpa only [selectedAddStep, selectedAddGates,
          EncodedBit.GateSpec.controlledListWithWorkStep] using hselected
      rw [hselected', hraw]
      simp [source]

/-! ## Shift-and-add schedule -/

/-- One compact modular doubling lifted into the point carrier. -/
def coefficientDoublingGates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  ArithmeticLift.gates fieldTail.succ counterWidth
    (CompactCorrection.doublingGates fieldTail counterWidth p)

/-- Coefficient doubling is entirely inside the compact arithmetic suffix. -/
lemma coefficientDoublingGates_bitDisjoint_lambdaBit
    (fieldTail counterWidth p : Nat) (bit : Fin fieldTail.succ) :
    ∀ gate, gate ∈ coefficientDoublingGates fieldTail counterWidth p →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldTail.succ counterWidth bit) gate :=
  ArithmeticLift.gates_bitDisjoint_lambdaBit fieldTail.succ counterWidth bit
    (CompactCorrection.doublingGates fieldTail counterWidth p)

/-- Folded action of one lifted coefficient doubling. -/
def coefficientDoublingStep (fieldTail counterWidth p : Nat) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList
    (coefficientDoublingGates fieldTail counterWidth p)

/-- Lifted modular doubling updates only the retained coefficient and restores
the accumulator and complete borrowed arithmetic boundary. -/
lemma coefficientDoublingStep_state
    (fieldTail counterWidth p : Nat)
    (base : Layout.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (target : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : coefficient.val < p) :
    coefficientDoublingStep fieldTail counterWidth p
        (multiplicationState fieldTail counterWidth p hp base coefficient
          target) =
      multiplicationState fieldTail counterWidth p hp base
        (CompactCorrection.doublingResidueWord fieldTail p hpPos hp coefficient)
        target := by
  let compactBase : MK.Compact.Registers fieldTail.succ counterWidth :=
    { base.arithmetic with target := target }
  have hcompact := CompactCorrection.doublingStep_state fieldTail counterWidth p
    compactBase coefficient hpPos hp hpOdd hcoefficient
  rw [coefficientDoublingStep, coefficientDoublingGates,
    ArithmeticLift.gates_stepList]
  simpa [multiplicationState, CompactCorrection.targetUpdateState,
    CompactCorrection.doublingState, CompactCorrection.doublingStep,
    CompactCorrection.widenFixedWord_zero, compactBase] using hcompact

/-- Literal selected-add followed by coefficient doubling for one multiplier
bit. -/
def roundGates (fieldTail counterWidth p : Nat)
    (bit : Fin fieldTail.succ) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  selectedAddGates fieldTail counterWidth p bit ++
    coefficientDoublingGates fieldTail counterWidth p

/-- A complete multiplication round leaves the persistent slope untouched. -/
lemma roundGates_bitDisjoint_lambdaBit
    (fieldTail counterWidth p : Nat)
    (multiplierBit lambdaBit : Fin fieldTail.succ) :
    ∀ gate, gate ∈ roundGates fieldTail counterWidth p multiplierBit →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldTail.succ counterWidth lambdaBit) gate := by
  intro gate hgate
  rcases List.mem_append.mp hgate with hselected | hdoubling
  · exact selectedAddGates_bitDisjoint_lambdaBit fieldTail counterWidth p
      multiplierBit lambdaBit gate hselected
  · exact coefficientDoublingGates_bitDisjoint_lambdaBit fieldTail
      counterWidth p lambdaBit gate hdoubling

/-- Folded action of one multiplication round. -/
def roundStep (fieldTail counterWidth p : Nat)
    (bit : Fin fieldTail.succ) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList (roundGates fieldTail counterWidth p bit)

/-- Pure coefficient/accumulator pair tracked across multiplication rounds. -/
structure Residues (fieldWidth : Nat) where
  coefficient : Word (fieldWidth + 1)
  target : Word fieldWidth
deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprResidues.repr

/-- Pure residue transition for one multiplier bit. -/
def residueRound (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (multiplier : Word fieldTail.succ) (bit : Fin fieldTail.succ)
    (state : Residues fieldTail.succ) : Residues fieldTail.succ where
  coefficient := CompactCorrection.doublingResidueWord fieldTail p hpPos hp
    state.coefficient
  target := if multiplier.val.testBit bit.val then
    CompactCorrection.modularSumFixedWord fieldTail p hpPos hp state.target
      (CompactCorrection.truncateFixedWord fieldTail.succ state.coefficient)
  else state.target

/-- One pure multiplication round preserves coefficient canonicity. -/
lemma residueRound_coefficient_lt
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (multiplier : Word fieldTail.succ) (bit : Fin fieldTail.succ)
    (state : Residues fieldTail.succ)
    (_hcoefficient : state.coefficient.val < p) :
    (residueRound fieldTail p hpPos hp multiplier bit state).coefficient.val <
      p := by
  simp only [residueRound, CompactCorrection.doublingResidueWord_val]
  exact Nat.mod_lt _ hpPos

/-- One pure multiplication round preserves accumulator canonicity. -/
lemma residueRound_target_lt
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (multiplier : Word fieldTail.succ) (bit : Fin fieldTail.succ)
    (state : Residues fieldTail.succ)
    (htarget : state.target.val < p) :
    (residueRound fieldTail p hpPos hp multiplier bit state).target.val < p := by
  simp only [residueRound]
  split_ifs
  · exact Nat.mod_lt _ hpPos
  · exact htarget

/-- The physical round realizes the pure selected-add/doubling transition on
the same clean point-carrier boundary. -/
lemma roundStep_state
    (fieldTail counterWidth p : Nat)
    (bit : Fin fieldTail.succ)
    (base : Layout.Registers fieldTail.succ counterWidth)
    (state : Residues fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : state.coefficient.val < p)
    (htarget : state.target.val < p)
    (hpath : base.arithmetic.shared.path = false) :
    roundStep fieldTail counterWidth p bit
        (multiplicationState fieldTail counterWidth p hp base
          state.coefficient state.target) =
      multiplicationState fieldTail counterWidth p hp base
        (residueRound fieldTail p hpPos hp base.mutableY bit state).coefficient
        (residueRound fieldTail p hpPos hp base.mutableY bit state).target := by
  let selectedTarget : Word fieldTail.succ :=
    if base.mutableY.val.testBit bit.val then
      CompactCorrection.modularSumFixedWord fieldTail p hpPos hp state.target
        (CompactCorrection.truncateFixedWord fieldTail.succ state.coefficient)
    else state.target
  have hselectedTarget : selectedTarget.val < p := by
    dsimp [selectedTarget]
    split_ifs
    · exact Nat.mod_lt _ hpPos
    · exact htarget
  rw [roundStep, roundGates, EncodedBit.GateSpec.stepList_append]
  change coefficientDoublingStep fieldTail counterWidth p
      (selectedAddStep fieldTail counterWidth p bit
        (multiplicationState fieldTail counterWidth p hp base
          state.coefficient state.target)) = _
  rw [selectedAddStep_state fieldTail counterWidth p bit base
    state.coefficient state.target hpPos hp hcoefficient htarget hpath]
  rw [coefficientDoublingStep_state fieldTail counterWidth p base
    state.coefficient selectedTarget hpPos hp hpOdd hcoefficient]
  rfl

/-- Concatenated physical rounds for an explicit little-endian bit schedule. -/
def roundsGates (fieldTail counterWidth p : Nat) :
    List (Fin fieldTail.succ) →
      List (EncodedBit.GateSpec
        (Layout.encoding fieldTail.succ counterWidth))
  | [] => []
  | bit :: rest => roundGates fieldTail counterWidth p bit ++
      roundsGates fieldTail counterWidth p rest

/-- Every finite multiplication-round fold leaves `lambda` untouched. -/
lemma roundsGates_bitDisjoint_lambdaBit
    (fieldTail counterWidth p : Nat) (lambdaBit : Fin fieldTail.succ) :
    ∀ bits gate, gate ∈ roundsGates fieldTail counterWidth p bits →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldTail.succ counterWidth lambdaBit) gate := by
  intro bits
  induction bits with
  | nil => simp [roundsGates]
  | cons bit rest ih =>
      intro gate hgate
      rw [roundsGates, List.mem_append] at hgate
      rcases hgate with hround | hrest
      · exact roundGates_bitDisjoint_lambdaBit fieldTail counterWidth p bit
          lambdaBit gate hround
      · exact ih gate hrest

/-- Pure fold matching `roundsGates` in physical execution order. -/
def residueRounds (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (multiplier : Word fieldTail.succ) :
    List (Fin fieldTail.succ) → Residues fieldTail.succ →
      Residues fieldTail.succ
  | [], state => state
  | bit :: rest, state =>
      residueRounds fieldTail p hpPos hp multiplier rest
        (residueRound fieldTail p hpPos hp multiplier bit state)

/-- The pure round fold preserves both canonical residue bounds. -/
lemma residueRounds_bounds
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (multiplier : Word fieldTail.succ) :
    ∀ bits (state : Residues fieldTail.succ),
      state.coefficient.val < p → state.target.val < p →
      (residueRounds fieldTail p hpPos hp multiplier bits state).coefficient.val <
          p ∧
        (residueRounds fieldTail p hpPos hp multiplier bits state).target.val <
          p := by
  intro bits
  induction bits with
  | nil =>
      intro state hcoefficient htarget
      exact ⟨hcoefficient, htarget⟩
  | cons bit rest ih =>
      intro state hcoefficient htarget
      exact ih _
        (residueRound_coefficient_lt fieldTail p hpPos hp multiplier bit state
          hcoefficient)
        (residueRound_target_lt fieldTail p hpPos hp multiplier bit state
          htarget)

/-- Residue folding over concatenated bit schedules is sequential folding. -/
lemma residueRounds_append
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (multiplier : Word fieldTail.succ) :
    ∀ first second (state : Residues fieldTail.succ),
      residueRounds fieldTail p hpPos hp multiplier (first ++ second) state =
        residueRounds fieldTail p hpPos hp multiplier second
          (residueRounds fieldTail p hpPos hp multiplier first state) := by
  intro first
  induction first with
  | nil =>
      intro second state
      rfl
  | cons bit rest ih =>
      intro second state
      exact ih second
        (residueRound fieldTail p hpPos hp multiplier bit state)

/-- Pure repeated modular doubling. -/
def forwardScaleWord (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) :
    Nat → Word (fieldTail.succ + 1) → Word (fieldTail.succ + 1)
  | 0, coefficient => coefficient
  | rounds + 1, coefficient =>
      forwardScaleWord fieldTail p hpPos hp rounds
        (CompactCorrection.doublingResidueWord fieldTail p hpPos hp coefficient)

/-- The coefficient component of a bit schedule depends only on the schedule
length and is exactly repeated modular doubling. -/
lemma residueRounds_coefficient_eq_forwardScaleWord
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (multiplier : Word fieldTail.succ) :
    ∀ bits (state : Residues fieldTail.succ),
      (residueRounds fieldTail p hpPos hp multiplier bits state).coefficient =
        forwardScaleWord fieldTail p hpPos hp bits.length state.coefficient := by
  intro bits
  induction bits with
  | nil =>
      intro state
      rfl
  | cons bit rest ih =>
      intro state
      simpa [residueRounds, residueRound, forwardScaleWord] using
        ih (residueRound fieldTail p hpPos hp multiplier bit state)

/-- Forward modular doubling cancels the same number of certified reverse
doublings exactly on every canonical residue. -/
lemma forwardScaleWord_inverseScaleWord
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p) :
    ∀ rounds (coefficient : Word (fieldTail.succ + 1)),
      coefficient.val < p →
      forwardScaleWord fieldTail p hpPos hp rounds
          (inverseScaleWord fieldTail p hpPos hp rounds coefficient) =
        coefficient := by
  intro rounds
  induction rounds with
  | zero =>
      intro coefficient hcoefficient
      rfl
  | succ rounds ih =>
      intro coefficient hcoefficient
      rw [inverseScaleWord, forwardScaleWord]
      rw [doublingResidueWord_halfResidueWord fieldTail p hpPos hp hpOdd
        (inverseScaleWord fieldTail p hpPos hp rounds coefficient)
        (inverseScaleWord_lt fieldTail p hpPos hp hpOdd rounds coefficient
          hcoefficient)]
      exact ih coefficient hcoefficient

/-- After all width-many rounds, the pre-scaled coefficient is restored
exactly. -/
lemma residueRounds_finRange_coefficient_restored
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (multiplier : Word fieldTail.succ)
    (coefficient : Word (fieldTail.succ + 1))
    (target : Word fieldTail.succ)
    (hcoefficient : coefficient.val < p) :
    let initial : Residues fieldTail.succ :=
      { coefficient := inverseScaleWord fieldTail p hpPos hp fieldTail.succ
          coefficient
        target := target }
    (residueRounds fieldTail p hpPos hp multiplier
      (List.finRange fieldTail.succ) initial).coefficient = coefficient := by
  dsimp
  rw [residueRounds_coefficient_eq_forwardScaleWord]
  rw [List.length_finRange]
  exact forwardScaleWord_inverseScaleWord fieldTail p hpPos hp hpOdd
    fieldTail.succ coefficient hcoefficient

/-- Modular doubling has its expected residue-field action. -/
lemma doublingResidueWord_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (coefficient : Word (fieldTail.succ + 1)) :
    ((CompactCorrection.doublingResidueWord fieldTail p hpPos hp
      coefficient).val : ZMod p) =
      2 * (coefficient.val : ZMod p) := by
  rw [CompactCorrection.doublingResidueWord_val, ZMod.natCast_mod]
  push_cast
  rfl

/-- Repeated modular doubling multiplies by the corresponding power of two in
the residue field. -/
lemma forwardScaleWord_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) :
    ∀ rounds (coefficient : Word (fieldTail.succ + 1)),
      ((forwardScaleWord fieldTail p hpPos hp rounds coefficient).val :
          ZMod p) =
        (2 : ZMod p) ^ rounds * (coefficient.val : ZMod p) := by
  intro rounds
  induction rounds with
  | zero =>
      intro coefficient
      simp [forwardScaleWord]
  | succ rounds ih =>
      intro coefficient
      change
        ((forwardScaleWord fieldTail p hpPos hp rounds
          (CompactCorrection.doublingResidueWord fieldTail p hpPos hp
            coefficient)).val : ZMod p) = _
      calc
        _ = (2 : ZMod p) ^ rounds *
            ((CompactCorrection.doublingResidueWord fieldTail p hpPos hp
              coefficient).val : ZMod p) := ih _
        _ = (2 : ZMod p) ^ rounds * (2 * (coefficient.val : ZMod p)) := by
          rw [doublingResidueWord_cast]
        _ = (2 : ZMod p) ^ (rounds + 1) *
            (coefficient.val : ZMod p) := by
          simpa only [pow_succ] using
            (mul_assoc ((2 : ZMod p) ^ rounds) 2
              (coefficient.val : ZMod p)).symm

/-- The canonical fixed-width modular sum has its expected residue-field
action. -/
lemma modularSumFixedWord_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ)
    (target source : Word fieldTail.succ) :
    ((CompactCorrection.modularSumFixedWord fieldTail p hpPos hp target
      source).val : ZMod p) =
      (target.val : ZMod p) + (source.val : ZMod p) := by
  rw [CompactCorrection.modularSumFixedWord_val, ZMod.natCast_mod]
  push_cast
  rfl

/-- The next canonical finite index extends its low-to-high prefix by one. -/
lemma finRange_take_succ {width : Nat} (round : Fin width) :
    (List.finRange width).take (round.val + 1) =
      (List.finRange width).take round.val ++ [round] := by
  have hround : round.val < (List.finRange width).length := by
    simpa only [List.length_finRange] using round.isLt
  have hat : (List.finRange width)[round.val]'hround = round := by
    simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  simpa only [hat] using
    (List.take_concat_get' (List.finRange width) round.val hround).symm

/-- The target after a canonical low-bit prefix is the initial target plus the
corresponding binary prefix times the initial coefficient, in the residue
field. -/
lemma residueRounds_finRange_take_target_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (multiplier : Word fieldTail.succ) :
    ∀ rounds, rounds ≤ fieldTail.succ →
      ∀ initial : Residues fieldTail.succ,
        initial.coefficient.val < p → initial.target.val < p →
        ((residueRounds fieldTail p hpPos hp multiplier
          ((List.finRange fieldTail.succ).take rounds) initial).target.val :
          ZMod p) =
          (initial.target.val : ZMod p) +
            ((multiplier.val % 2 ^ rounds : Nat) : ZMod p) *
              (initial.coefficient.val : ZMod p) := by
  intro rounds hrounds initial hcoefficient htarget
  induction rounds generalizing initial with
  | zero =>
      change (initial.target.val : ZMod p) =
        (initial.target.val : ZMod p) +
          ((multiplier.val % 1 : Nat) : ZMod p) *
            (initial.coefficient.val : ZMod p)
      rw [Nat.mod_one]
      simp
  | succ rounds ih =>
      let round : Fin fieldTail.succ :=
        ⟨rounds, Nat.lt_of_succ_le hrounds⟩
      let prefixState : Residues fieldTail.succ :=
        residueRounds fieldTail p hpPos hp multiplier
          ((List.finRange fieldTail.succ).take rounds) initial
      have hbounds := residueRounds_bounds fieldTail p hpPos hp multiplier
        ((List.finRange fieldTail.succ).take rounds) initial hcoefficient htarget
      have htargetPrefix := ih
        (Nat.le_trans (Nat.le_succ rounds) hrounds) initial hcoefficient htarget
      have hcoefficientPrefix :
          (prefixState.coefficient.val : ZMod p) =
            (2 : ZMod p) ^ rounds *
              (initial.coefficient.val : ZMod p) := by
        have hlength :
            ((List.finRange fieldTail.succ).take rounds).length = rounds := by
          simp [Nat.min_eq_left
            (Nat.le_trans (Nat.le_succ rounds) hrounds)]
        rw [show prefixState.coefficient =
            forwardScaleWord fieldTail p hpPos hp rounds initial.coefficient by
          simpa [prefixState, hlength] using
            residueRounds_coefficient_eq_forwardScaleWord
            fieldTail p hpPos hp multiplier
            ((List.finRange fieldTail.succ).take rounds) initial]
        exact forwardScaleWord_cast fieldTail p hpPos hp rounds
          initial.coefficient
      have hdecompCast :
          (((multiplier.val % 2 ^ (rounds + 1) : Nat) : ZMod p)) =
            ((multiplier.val % 2 ^ rounds : Nat) : ZMod p) +
              ((multiplier.val.testBit rounds).toNat : ZMod p) *
                (2 : ZMod p) ^ rounds := by
        rw [Comparator.mod_two_pow_succ_decomp]
        push_cast
        rfl
      rw [show (List.finRange fieldTail.succ).take (rounds + 1) =
          (List.finRange fieldTail.succ).take rounds ++ [round] by
        simpa only [round, Nat.succ_eq_add_one] using finRange_take_succ round]
      rw [residueRounds_append]
      simp only [residueRounds]
      cases hbit : multiplier.val.testBit rounds
      · simp only [residueRound, round, hbit, Bool.false_eq_true,
          ↓reduceIte]
        rw [htargetPrefix]
        rw [hdecompCast]
        simp [hbit]
      · simp only [residueRound, round, hbit, ↓reduceIte]
        rw [modularSumFixedWord_cast]
        have hfit : prefixState.coefficient.val < 2 ^ fieldTail.succ :=
          hbounds.1.trans hp
        rw [CompactCorrection.truncateFixedWord_val,
          Nat.mod_eq_of_lt hfit, hcoefficientPrefix, htargetPrefix,
          hdecompCast]
        simp [hbit]
        ring

/-- Consuming the full finite range replaces the low-bit prefix by the exact
fixed-width multiplier value. -/
lemma residueRounds_finRange_target_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (multiplier : Word fieldTail.succ)
    (initial : Residues fieldTail.succ)
    (hcoefficient : initial.coefficient.val < p)
    (htarget : initial.target.val < p) :
    ((residueRounds fieldTail p hpPos hp multiplier
      (List.finRange fieldTail.succ) initial).target.val : ZMod p) =
      (initial.target.val : ZMod p) +
        (multiplier.val : ZMod p) *
          (initial.coefficient.val : ZMod p) := by
  have hprefix := residueRounds_finRange_take_target_cast fieldTail p hpPos hp
    multiplier fieldTail.succ (Nat.le_refl _) initial hcoefficient htarget
  have htake :
      (List.finRange fieldTail.succ).take fieldTail.succ =
        List.finRange fieldTail.succ := by
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange fieldTail.succ))
  rw [htake, Nat.mod_eq_of_lt multiplier.isLt] at hprefix
  exact hprefix

/-! ## Closed Montgomery semantics -/

/-- The unit represented by two modulo the odd modulus. -/
def twoUnit (p : Nat) (hpOdd : Odd p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime 2 hpOdd.coprime_two_left

/-- The inverse Montgomery radix, represented as `rounds` successive inverse
factors of two. -/
def inverseRadixUnit (p : Nat) (hpOdd : Odd p) : Nat → (ZMod p)ˣ
  | 0 => 1
  | rounds + 1 => (twoUnit p hpOdd)⁻¹ * inverseRadixUnit p hpOdd rounds

/-- One canonical modular half is multiplication by the inverse-two unit. -/
lemma halfResidueWord_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (coefficient : Word (fieldTail.succ + 1))
    (hcoefficient : coefficient.val < p) :
    ((halfResidueWord fieldTail p hpPos hp coefficient).val : ZMod p) =
      ((twoUnit p hpOdd)⁻¹ : ZMod p) *
        (coefficient.val : ZMod p) := by
  let half := halfResidueWord fieldTail p hpPos hp coefficient
  have hdoubled := congrArg (fun word => (word.val : ZMod p))
    (doublingResidueWord_halfResidueWord fieldTail p hpPos hp hpOdd
      coefficient hcoefficient)
  have hdouble :
      (2 : ZMod p) * (half.val : ZMod p) =
        (coefficient.val : ZMod p) := by
    rw [← doublingResidueWord_cast fieldTail p hpPos hp half]
    exact hdoubled
  have htwo : (twoUnit p hpOdd : ZMod p) = 2 := by
    simp [twoUnit, ZMod.coe_unitOfCoprime]
  calc
    (half.val : ZMod p) =
        ((((twoUnit p hpOdd)⁻¹ * twoUnit p hpOdd : (ZMod p)ˣ) :
          ZMod p) * (half.val : ZMod p)) := by simp
    _ = ((twoUnit p hpOdd)⁻¹ : ZMod p) *
        ((twoUnit p hpOdd : ZMod p) * (half.val : ZMod p)) := by
          simp only [Units.val_mul]
          rw [mul_assoc]
          rfl
    _ = ((twoUnit p hpOdd)⁻¹ : ZMod p) *
        ((2 : ZMod p) * (half.val : ZMod p)) := by rw [htwo]
    _ = ((twoUnit p hpOdd)⁻¹ : ZMod p) *
        (coefficient.val : ZMod p) := by rw [hdouble]

/-- The certified reverse-doubling chain multiplies by the inverse Montgomery
radix in the residue field. -/
lemma inverseScaleWord_cast
    (fieldTail p : Nat) (hpPos : 0 < p)
    (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p) :
    ∀ rounds (coefficient : Word (fieldTail.succ + 1)),
      coefficient.val < p →
      ((inverseScaleWord fieldTail p hpPos hp rounds coefficient).val :
          ZMod p) =
        (inverseRadixUnit p hpOdd rounds : ZMod p) *
          (coefficient.val : ZMod p) := by
  intro rounds
  induction rounds with
  | zero =>
      intro coefficient hcoefficient
      simp [inverseScaleWord, inverseRadixUnit]
  | succ rounds ih =>
      intro coefficient hcoefficient
      rw [inverseScaleWord]
      rw [halfResidueWord_cast fieldTail p hpPos hp hpOdd _
        (inverseScaleWord_lt fieldTail p hpPos hp hpOdd rounds coefficient
          hcoefficient)]
      rw [ih coefficient hcoefficient]
      simp only [inverseRadixUnit, Units.val_mul]
      rw [mul_assoc]
      rfl

/-- The concatenated literal round ledger realizes the complete pure residue
fold without changing the carrier base. -/
lemma roundsGates_stepList
    (fieldTail counterWidth p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p) :
    ∀ bits (base : Layout.Registers fieldTail.succ counterWidth)
      (state : Residues fieldTail.succ),
      state.coefficient.val < p → state.target.val < p →
      base.arithmetic.shared.path = false →
      EncodedBit.GateSpec.stepList
          (roundsGates fieldTail counterWidth p bits)
          (multiplicationState fieldTail counterWidth p hp base
            state.coefficient state.target) =
        multiplicationState fieldTail counterWidth p hp base
          (residueRounds fieldTail p hpPos hp base.mutableY bits state).coefficient
          (residueRounds fieldTail p hpPos hp base.mutableY bits state).target := by
  intro bits
  induction bits with
  | nil =>
      intro base state hcoefficient htarget hpath
      rfl
  | cons bit rest ih =>
      intro base state hcoefficient htarget hpath
      rw [roundsGates, EncodedBit.GateSpec.stepList_append]
      change EncodedBit.GateSpec.stepList
          (roundsGates fieldTail counterWidth p rest)
          (roundStep fieldTail counterWidth p bit
            (multiplicationState fieldTail counterWidth p hp base
              state.coefficient state.target)) = _
      rw [roundStep_state fieldTail counterWidth p bit base state hpPos hp hpOdd
        hcoefficient htarget hpath]
      exact ih base _
        (residueRound_coefficient_lt fieldTail p hpPos hp base.mutableY bit state
          hcoefficient)
        (residueRound_target_lt fieldTail p hpPos hp base.mutableY bit state
          htarget)
        hpath

/-! ## Complete Montgomery product ledger -/

/-- Lift the `R⁻¹` coefficient pre-scaling ledger into the point carrier. -/
def inverseScalePointGates (fieldTail counterWidth p rounds : Nat) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  ArithmeticLift.gates fieldTail.succ counterWidth
    (inverseScaleGates fieldTail counterWidth p rounds)

/-- The lifted inverse-scaling prefix leaves `lambda` untouched. -/
lemma inverseScalePointGates_bitDisjoint_lambdaBit
    (fieldTail counterWidth p rounds : Nat) (bit : Fin fieldTail.succ) :
    ∀ gate, gate ∈ inverseScalePointGates fieldTail counterWidth p rounds →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldTail.succ counterWidth bit) gate :=
  ArithmeticLift.gates_bitDisjoint_lambdaBit fieldTail.succ counterWidth bit
    (inverseScaleGates fieldTail counterWidth p rounds)

/-- The lifted inverse scaling changes only the retained coefficient. -/
lemma inverseScalePointGates_stepList
    (fieldTail counterWidth p rounds : Nat)
    (base : Layout.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (target : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : coefficient.val < p) :
    EncodedBit.GateSpec.stepList
        (inverseScalePointGates fieldTail counterWidth p rounds)
        (multiplicationState fieldTail counterWidth p hp base coefficient
          target) =
      multiplicationState fieldTail counterWidth p hp base
        (inverseScaleWord fieldTail p hpPos hp rounds coefficient) target := by
  let compactBase : MK.Compact.Registers fieldTail.succ counterWidth :=
    { base.arithmetic with target := target }
  have hcompact := inverseScaleGates_stepList fieldTail counterWidth p hpPos hp
    hpOdd rounds compactBase coefficient hcoefficient
  rw [inverseScalePointGates, ArithmeticLift.gates_stepList]
  simpa [multiplicationState, CompactCorrection.targetUpdateState,
    CompactCorrection.doublingState, CompactCorrection.widenFixedWord_zero,
    compactBase] using hcompact

/-- Full literal Montgomery accumulation: divide the coefficient by `R`, then
consume every little-endian multiplier bit while restoring that coefficient. -/
def gates (fieldTail counterWidth p : Nat) :
    List (EncodedBit.GateSpec
      (Layout.encoding fieldTail.succ counterWidth)) :=
  inverseScalePointGates fieldTail counterWidth p fieldTail.succ ++
    roundsGates fieldTail counterWidth p (List.finRange fieldTail.succ)

/-- The complete Montgomery multiplication reads `mutableY` but never reads
or writes the persistent slope word. -/
lemma gates_bitDisjoint_lambdaBit
    (fieldTail counterWidth p : Nat) (bit : Fin fieldTail.succ) :
    ∀ gate, gate ∈ gates fieldTail counterWidth p →
      EncodedBit.GateSpec.bitDisjoint
        (Layout.lambdaBit fieldTail.succ counterWidth bit) gate := by
  intro gate hgate
  rcases List.mem_append.mp hgate with hscale | hrounds
  · exact inverseScalePointGates_bitDisjoint_lambdaBit fieldTail
      counterWidth p fieldTail.succ bit gate hscale
  · exact roundsGates_bitDisjoint_lambdaBit fieldTail counterWidth p bit
      (List.finRange fieldTail.succ) gate hrounds

/-- Folded action of the complete literal Montgomery multiplication ledger. -/
def step (fieldTail counterWidth p : Nat) :
    Layout.Registers fieldTail.succ counterWidth →
      Layout.Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList (gates fieldTail counterWidth p)

/-- Exact cleaned endpoint of the complete physical ledger, before reducing
the pure residue fold to the closed Montgomery-product formula. -/
lemma step_state
    (fieldTail counterWidth p : Nat)
    (base : Layout.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (target : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : coefficient.val < p) (htarget : target.val < p)
    (hpath : base.arithmetic.shared.path = false) :
    step fieldTail counterWidth p
        (multiplicationState fieldTail counterWidth p hp base coefficient
          target) =
      let initial : Residues fieldTail.succ :=
        { coefficient := inverseScaleWord fieldTail p hpPos hp fieldTail.succ
            coefficient
          target := target }
      multiplicationState fieldTail counterWidth p hp base
        (residueRounds fieldTail p hpPos hp base.mutableY
          (List.finRange fieldTail.succ) initial).coefficient
        (residueRounds fieldTail p hpPos hp base.mutableY
          (List.finRange fieldTail.succ) initial).target := by
  let initial : Residues fieldTail.succ :=
    { coefficient := inverseScaleWord fieldTail p hpPos hp fieldTail.succ
        coefficient
      target := target }
  have hscaled : initial.coefficient.val < p := by
    exact inverseScaleWord_lt fieldTail p hpPos hp hpOdd fieldTail.succ
      coefficient hcoefficient
  rw [step, gates, EncodedBit.GateSpec.stepList_append]
  rw [inverseScalePointGates_stepList fieldTail counterWidth p fieldTail.succ
    base coefficient target hpPos hp hpOdd hcoefficient]
  exact roundsGates_stepList fieldTail counterWidth p hpPos hp hpOdd
    (List.finRange fieldTail.succ) base initial hscaled htarget hpath

/-- Clean Montgomery-accumulation endpoint of the literal physical ledger.
The coefficient is restored exactly; the only live change is
`target + multiplier * R⁻¹ * coefficient`, where `R = 2^fieldWidth`. -/
lemma step_cleanMontgomeryEndpoint
    (fieldTail counterWidth p : Nat)
    (base : Layout.Registers fieldTail.succ counterWidth)
    (coefficient : Word (fieldTail.succ + 1))
    (target : Word fieldTail.succ)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ) (hpOdd : Odd p)
    (hcoefficient : coefficient.val < p) (htarget : target.val < p)
    (hpath : base.arithmetic.shared.path = false) :
    let initial : Residues fieldTail.succ :=
      { coefficient := inverseScaleWord fieldTail p hpPos hp fieldTail.succ
          coefficient
        target := target }
    let result := residueRounds fieldTail p hpPos hp base.mutableY
      (List.finRange fieldTail.succ) initial
    step fieldTail counterWidth p
        (multiplicationState fieldTail counterWidth p hp base coefficient
          target) =
        multiplicationState fieldTail counterWidth p hp base coefficient
          result.target ∧
      (result.target.val : ZMod p) =
        (target.val : ZMod p) +
          (base.mutableY.val : ZMod p) *
            (inverseRadixUnit p hpOdd fieldTail.succ : ZMod p) *
              (coefficient.val : ZMod p) := by
  let initial : Residues fieldTail.succ :=
    { coefficient := inverseScaleWord fieldTail p hpPos hp fieldTail.succ
        coefficient
      target := target }
  let result := residueRounds fieldTail p hpPos hp base.mutableY
    (List.finRange fieldTail.succ) initial
  have hscaled : initial.coefficient.val < p := by
    exact inverseScaleWord_lt fieldTail p hpPos hp hpOdd fieldTail.succ
      coefficient hcoefficient
  have hphysical := step_state fieldTail counterWidth p base coefficient target
    hpPos hp hpOdd hcoefficient htarget hpath
  have hrestored := residueRounds_finRange_coefficient_restored fieldTail p
    hpPos hp hpOdd base.mutableY coefficient target hcoefficient
  have hsemantic := residueRounds_finRange_target_cast fieldTail p hpPos hp
    base.mutableY initial hscaled htarget
  have hscaledCast := inverseScaleWord_cast fieldTail p hpPos hp hpOdd
    fieldTail.succ coefficient hcoefficient
  dsimp only at hrestored
  change result.coefficient = coefficient at hrestored
  change step fieldTail counterWidth p
      (multiplicationState fieldTail counterWidth p hp base coefficient target) =
    multiplicationState fieldTail counterWidth p hp base result.coefficient
      result.target at hphysical
  change (result.target.val : ZMod p) =
    (target.val : ZMod p) +
      (base.mutableY.val : ZMod p) * (initial.coefficient.val : ZMod p)
    at hsemantic
  constructor
  · rw [hphysical, hrestored]
  · rw [hsemantic]
    change (target.val : ZMod p) +
        (base.mutableY.val : ZMod p) *
          ((inverseScaleWord fieldTail p hpPos hp fieldTail.succ
            coefficient).val : ZMod p) = _
    rw [hscaledCast]
    ring

end
end MontgomeryMultiplication
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
