/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
/-!
# Encoded bit-slice arithmetic blocks

This module packages small X/CNOT/Toffoli bit-slice blocks that later plain and
modular arithmetic circuits can fold into larger word-level programs.  VBE's
plain-adder route decomposes addition into carry calculation, reverse cleanup,
and sum operations [VBE95, 9511018.tex:244-264,591-618].  The declarations here
only provide actual circuits and direct realization theorems for local
encoded-bit gate lists; word-level arithmetic correctness is supplied by the
modules that instantiate these blocks into a full schedule.
-/

section

namespace QuantumAlg
namespace BitSlice

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

namespace Raw

/-- Raw two-bit target-add block: compute the low-bit carry from `srcLo` and
`tgtLo` into `tgtHi`, then xor `srcHi` and `srcLo` into the target pair. -/
def targetAdd2Program {width : Nat}
    (srcLo tgtLo srcHi tgtHi : Fin width)
    (hSrcLoTgtLo : srcLo ≠ tgtLo) (hSrcLoTgtHi : srcLo ≠ tgtHi)
    (hTgtLoTgtHi : tgtLo ≠ tgtHi) (hSrcHiTgtHi : srcHi ≠ tgtHi) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical (width)).toQuantum :=
  UnitaryCircuit.seq
    (QubitPrimitive.circuit
      (.toffoli srcLo tgtLo tgtHi
        hSrcLoTgtLo hSrcLoTgtHi hTgtLoTgtHi)
      (QubitLayout.canonical _) .empty)
    (UnitaryCircuit.seq
      (QubitPrimitive.circuit (.cnot srcHi tgtHi hSrcHiTgtHi)
        (QubitLayout.canonical _) .empty)
      (QubitPrimitive.circuit (.cnot srcLo tgtLo hSrcLoTgtLo)
        (QubitLayout.canonical _) .empty))

/-- Raw basis-label action of `targetAdd2Program`. -/
def targetAdd2Step {width : Nat}
    (srcLo tgtLo srcHi tgtHi : Fin width)
    (hSrcLoTgtLo : srcLo ≠ tgtLo) (hSrcLoTgtHi : srcLo ≠ tgtHi)
    (hTgtLoTgtHi : tgtLo ≠ tgtHi) (hSrcHiTgtHi : srcHi ≠ tgtHi) :
    Fin (2 ^ width) → Fin (2 ^ width) :=
  fun label =>
    QubitPrimitive.applyLabel (.cnot srcLo tgtLo hSrcLoTgtLo)
      (QubitPrimitive.applyLabel (.cnot srcHi tgtHi hSrcHiTgtHi)
        (QubitPrimitive.applyLabel
          (.toffoli srcLo tgtLo tgtHi
            hSrcLoTgtLo hSrcLoTgtHi hTgtLoTgtHi)
          label))

end Raw

namespace Boolean

/-- The pairwise-product XOR form of a full-adder carry agrees with
`Bool.carry`.  This is the Boolean recurrence used by the plain-adder carry
stage [VBE95, 9511018.tex:248-253]. -/
lemma pairwiseXor_eq_carry (left right carryIn : Bool) :
    Bool.xor (Bool.xor (left && right) (left && carryIn))
        (right && carryIn) =
      Bool.carry left right carryIn := by
  cases left <;> cases right <;> cases carryIn <;> rfl

end Boolean

namespace Encoded

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- Two CNOTs that xor two source bits into one target bit. -/
def sumGates (left carry target : EncodedBit encoding)
    (hlt : left.wire ≠ target.wire) (hct : carry.wire ≠ target.wire) :
    List (EncodedBit.GateSpec encoding) :=
  [ EncodedBit.GateSpec.cnot left target hlt
  , EncodedBit.GateSpec.cnot carry target hct ]

/-- The local sum gate list is disjoint from an observed bit when all three
participating wires are disjoint from it. -/
lemma sumGates_bitDisjoint
    (left carry target observed : EncodedBit encoding)
    (hlt : left.wire ≠ target.wire) (hct : carry.wire ≠ target.wire)
    (hleft : left.wire ≠ observed.wire)
    (hcarry : carry.wire ≠ observed.wire)
    (htarget : target.wire ≠ observed.wire) :
    ∀ gate, gate ∈ sumGates left carry target hlt hct ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hmem
  simp only [sumGates, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem
  · subst gate
    simpa [EncodedBit.GateSpec.bitDisjoint] using
      (⟨hleft, htarget⟩ :
        left.wire ≠ observed.wire ∧ target.wire ≠ observed.wire)
  · subst gate
    simpa [EncodedBit.GateSpec.bitDisjoint] using
      (⟨hcarry, htarget⟩ :
        carry.wire ≠ observed.wire ∧ target.wire ≠ observed.wire)

/-- Base-gate program for the local two-control xor/sum block. -/
def sumProgram (left carry target : EncodedBit encoding)
    (hlt : left.wire ≠ target.wire) (hct : carry.wire ≠ target.wire) :
  UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical (encoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (sumGates left carry target hlt hct)

/-- Folded semantic action of the local two-control xor/sum block. -/
def sumStep (left carry target : EncodedBit encoding)
    (hlt : left.wire ≠ target.wire) (hct : carry.wire ≠ target.wire) :
    Data → Data :=
  EncodedBit.GateSpec.stepList (sumGates left carry target hlt hct)

/-- Closed-form target readout of the local two-control xor/sum block. -/
lemma sumStep_get_target (left carry target : EncodedBit encoding)
    (hlt : left.wire ≠ target.wire) (hct : carry.wire ≠ target.wire)
    (x : Data) :
    target.get (sumStep left carry target hlt hct x) =
      ((target.get x ^^ left.get x) ^^ carry.get x) := by
  simp [sumStep, sumGates, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, EncodedBit.cnotStep_get_target,
    EncodedBit.cnotStep_get_of_target_ne, Ne.symm hct]

/-- The local two-control xor/sum block preserves its left readout. -/
lemma sumStep_get_left (left carry target : EncodedBit encoding)
    (hlt : left.wire ≠ target.wire) (hct : carry.wire ≠ target.wire)
    (x : Data) :
    left.get (sumStep left carry target hlt hct x) = left.get x := by
  simp [sumStep, sumGates, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, EncodedBit.cnotStep_get_of_target_ne,
    Ne.symm hlt]

/-- The local two-control xor/sum block preserves its carry readout. -/
lemma sumStep_get_carry (left carry target : EncodedBit encoding)
    (hlt : left.wire ≠ target.wire) (hct : carry.wire ≠ target.wire)
    (x : Data) :
    carry.get (sumStep left carry target hlt hct x) = carry.get x := by
  simp [sumStep, sumGates, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, EncodedBit.cnotStep_get_of_target_ne,
    Ne.symm hct]

/-- The local two-control xor/sum block preserves any readout whose wire is
not the target wire. -/
lemma sumStep_get_of_target_ne
    (left carry target observed : EncodedBit encoding)
    (hlt : left.wire ≠ target.wire) (hct : carry.wire ≠ target.wire)
    (hobs : target.wire ≠ observed.wire) (x : Data) :
    observed.get (sumStep left carry target hlt hct x) = observed.get x := by
  simp [sumStep, sumGates, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, EncodedBit.cnotStep_get_of_target_ne, hobs]

/-- The local two-control xor/sum program realizes its folded bit semantics. -/
lemma sum_realizes (left carry target : EncodedBit encoding)
    (hlt : left.wire ≠ target.wire) (hct : carry.wire ≠ target.wire) :
    UnitaryCircuit.Realizes encoding (sumProgram left carry target hlt hct) environment
      (sumStep left carry target hlt hct) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (sumGates left carry target hlt hct)

/-- Three Toffoli gates that xor the pairwise-control products
`left ∧ right`, `left ∧ carryIn`, and `right ∧ carryIn` into a separate
`carryOut` work bit.  This is a local carry-work ingredient; full adder
schedules state and prove the word-level carry invariant separately. -/
def carryOutGates (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) :
    List (EncodedBit.GateSpec encoding) :=
  [ EncodedBit.GateSpec.toffoli left right carryOut hlr hlco hrco
  , EncodedBit.GateSpec.toffoli left carryIn carryOut hlci hlco hcico
  , EncodedBit.GateSpec.toffoli right carryIn carryOut hrci hrco hcico ]

/-- The local carry-output gate list is disjoint from an observed bit when all
four participating wires are disjoint from it. -/
lemma carryOutGates_bitDisjoint
    (left right carryIn carryOut observed : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire)
    (hleft : left.wire ≠ observed.wire)
    (hright : right.wire ≠ observed.wire)
    (hcarryIn : carryIn.wire ≠ observed.wire)
    (hcarryOut : carryOut.wire ≠ observed.wire) :
    ∀ gate, gate ∈ carryOutGates left right carryIn carryOut
        hlr hlci hlco hrci hrco hcico ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hmem
  simp only [carryOutGates, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem | hmem
  · subst gate
    simpa [EncodedBit.GateSpec.bitDisjoint] using
      (⟨hleft, hright, hcarryOut⟩ :
        left.wire ≠ observed.wire ∧ right.wire ≠ observed.wire ∧
          carryOut.wire ≠ observed.wire)
  · subst gate
    simpa [EncodedBit.GateSpec.bitDisjoint] using
      (⟨hleft, hcarryIn, hcarryOut⟩ :
        left.wire ≠ observed.wire ∧ carryIn.wire ≠ observed.wire ∧
          carryOut.wire ≠ observed.wire)
  · subst gate
    simpa [EncodedBit.GateSpec.bitDisjoint] using
      (⟨hright, hcarryIn, hcarryOut⟩ :
        right.wire ≠ observed.wire ∧ carryIn.wire ≠ observed.wire ∧
          carryOut.wire ≠ observed.wire)

/-- Base-gate program for the local separate-output carry block. -/
def carryOutProgram (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical (encoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (carryOutGates left right carryIn carryOut
      hlr hlci hlco hrci hrco hcico)

/-- Folded semantic action of the local separate-output carry block. -/
def carryOutStep (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) :
    Data -> Data :=
  EncodedBit.GateSpec.stepList
    (carryOutGates left right carryIn carryOut
      hlr hlci hlco hrci hrco hcico)

/-- Closed-form output readout of the separate-output carry block.  The three
Toffoli gates xor the pairwise-control products into the output carry wire. -/
lemma carryOutStep_get_carryOut
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data) :
    carryOut.get
        (carryOutStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      (((carryOut.get x ^^ (left.get x && right.get x)) ^^
          (left.get x && carryIn.get x)) ^^
        (right.get x && carryIn.get x)) := by
  simp [carryOutStep, carryOutGates, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, EncodedBit.toffoliStep_get_target,
    EncodedBit.toffoliStep_get_of_target_ne, Ne.symm hlco, Ne.symm hrco,
    Ne.symm hcico]

/-- On a clean output carry wire, the separate-output carry block computes the
Boolean full-adder carry used by the VBE recurrence [VBE95,
9511018.tex:248-253]. -/
lemma carryOutStep_get_carryOut_clean
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data)
    (hclean : carryOut.get x = false) :
    carryOut.get
        (carryOutStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      Bool.carry (left.get x) (right.get x) (carryIn.get x) := by
  rw [carryOutStep_get_carryOut left right carryIn carryOut
    hlr hlci hlco hrci hrco hcico x]
  simpa [hclean] using
    Boolean.pairwiseXor_eq_carry (left.get x) (right.get x) (carryIn.get x)

/-! ### Local subtraction-borrow block -/

/-- Gate list that computes one subtract-borrow bit into a separate output.
It reuses the full-adder carry block by complementing the minuend bit before
and after the carry calculation. -/
def borrowOutGates
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) :
    List (EncodedBit.GateSpec encoding) :=
  [EncodedBit.GateSpec.x minuend] ++
  carryOutGates minuend subtrahend borrowIn borrowOut
    hms hmbi hmbo hsbi hsbo hbibo ++
  [EncodedBit.GateSpec.x minuend]

/-- One subtract-borrow block has two X gates around three Toffoli gates. -/
@[simp] lemma borrowOutGates_length
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) :
    (borrowOutGates minuend subtrahend borrowIn borrowOut
      hms hmbi hmbo hsbi hsbo hbibo).length = 5 := by
  simp [borrowOutGates, carryOutGates]

/-- Exact X coordinate of one subtract-borrow block. -/
@[simp] lemma borrowOutGates_xMultiplicity_sum
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) :
    ((borrowOutGates minuend subtrahend borrowIn borrowOut
      hms hmbi hmbo hsbi hsbo hbibo).map
        EncodedBit.GateSpec.xMultiplicity).sum = 2 := by
  simp [borrowOutGates, carryOutGates]

/-- One subtract-borrow block contains no CNOT gate. -/
@[simp] lemma borrowOutGates_cnotMultiplicity_sum
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) :
    ((borrowOutGates minuend subtrahend borrowIn borrowOut
      hms hmbi hmbo hsbi hsbo hbibo).map
        EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp [borrowOutGates, carryOutGates]

/-- Exact Toffoli coordinate of one subtract-borrow block. -/
@[simp] lemma borrowOutGates_toffoliMultiplicity_sum
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) :
    ((borrowOutGates minuend subtrahend borrowIn borrowOut
      hms hmbi hmbo hsbi hsbo hbibo).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 3 := by
  simp [borrowOutGates, carryOutGates]

/-- The local borrow-output gate list is disjoint from an observed bit when all
four participating wires are disjoint from it. -/
lemma borrowOutGates_bitDisjoint
    (minuend subtrahend borrowIn borrowOut observed : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire)
    (hminuend : minuend.wire ≠ observed.wire)
    (hsubtrahend : subtrahend.wire ≠ observed.wire)
    (hborrowIn : borrowIn.wire ≠ observed.wire)
    (hborrowOut : borrowOut.wire ≠ observed.wire) :
    ∀ gate, gate ∈ borrowOutGates minuend subtrahend borrowIn borrowOut
        hms hmbi hmbo hsbi hsbo hbibo ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hmem
  simp only [borrowOutGates, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem
  · rcases hmem with hmem | hmem
    · subst gate
      simpa [EncodedBit.GateSpec.bitDisjoint] using hminuend
    · exact carryOutGates_bitDisjoint minuend subtrahend borrowIn borrowOut
        observed hms hmbi hmbo hsbi hsbo hbibo hminuend hsubtrahend
        hborrowIn hborrowOut gate hmem
  · subst gate
    simpa [EncodedBit.GateSpec.bitDisjoint] using hminuend

/-- Base-gate program for the local separate-output borrow block. -/
def borrowOutProgram
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical (encoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (borrowOutGates minuend subtrahend borrowIn borrowOut
      hms hmbi hmbo hsbi hsbo hbibo)

/-- Folded semantic action of the local separate-output borrow block. -/
def borrowOutStep
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) :
    Data -> Data :=
  EncodedBit.GateSpec.stepList
    (borrowOutGates minuend subtrahend borrowIn borrowOut
      hms hmbi hmbo hsbi hsbo hbibo)

/-- The local borrow block is a concrete encoded-bit base-gate realization. -/
lemma borrowOut_realizes
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) :
    UnitaryCircuit.Realizes encoding
      (borrowOutProgram minuend subtrahend borrowIn borrowOut
        hms hmbi hmbo hsbi hsbo hbibo) environment
      (borrowOutStep minuend subtrahend borrowIn borrowOut
        hms hmbi hmbo hsbi hsbo hbibo) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (borrowOutGates minuend subtrahend borrowIn borrowOut
      hms hmbi hmbo hsbi hsbo hbibo)

/-- Closed-form output readout of the local separate-output borrow block. -/
lemma borrowOutStep_get_borrowOut
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) (x : Data) :
    borrowOut.get
        (borrowOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo x) =
      (((borrowOut.get x ^^ (!minuend.get x && subtrahend.get x)) ^^
          (!minuend.get x && borrowIn.get x)) ^^
        (subtrahend.get x && borrowIn.get x)) := by
  change borrowOut.get
      (minuend.flip
        (carryOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo (minuend.flip x))) =
    (((borrowOut.get x ^^ (!minuend.get x && subtrahend.get x)) ^^
        (!minuend.get x && borrowIn.get x)) ^^
      (subtrahend.get x && borrowIn.get x))
  rw [EncodedBit.get_flip_of_wire_ne minuend borrowOut hmbo]
  rw [carryOutStep_get_carryOut]
  rw [EncodedBit.get_flip_of_wire_ne minuend borrowOut hmbo]
  rw [EncodedBit.get_flip_self]
  rw [EncodedBit.get_flip_of_wire_ne minuend subtrahend hms]
  rw [EncodedBit.get_flip_of_wire_ne minuend borrowIn hmbi]

/-- On a clean output borrow wire, the block computes the subtract-borrow
recurrence for `minuend - subtrahend - borrowIn`. -/
lemma borrowOutStep_get_borrowOut_clean
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) (x : Data)
    (hclean : borrowOut.get x = false) :
    borrowOut.get
        (borrowOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo x) =
      Bool.carry (!minuend.get x) (subtrahend.get x) (borrowIn.get x) := by
  rw [borrowOutStep_get_borrowOut]
  simpa [hclean] using
    Boolean.pairwiseXor_eq_carry (!minuend.get x) (subtrahend.get x)
      (borrowIn.get x)

/-- The local borrow block restores the minuend readout. -/
lemma borrowOutStep_get_minuend
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) (x : Data) :
    minuend.get
        (borrowOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo x) =
      minuend.get x := by
  change minuend.get
      (minuend.flip
        (carryOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo (minuend.flip x))) =
    minuend.get x
  rw [EncodedBit.get_flip_self]
  have hpres :
      minuend.get
          (carryOutStep minuend subtrahend borrowIn borrowOut
            hms hmbi hmbo hsbi hsbo hbibo (minuend.flip x)) =
        minuend.get (minuend.flip x) := by
    simp [carryOutStep, carryOutGates, EncodedBit.GateSpec.stepList,
      EncodedBit.GateSpec.step, EncodedBit.toffoliStep_get_of_target_ne,
      Ne.symm hmbo]
  rw [hpres]
  rw [EncodedBit.get_flip_self]
  cases minuend.get x <;> rfl

/-- The local borrow block preserves the subtrahend readout. -/
lemma borrowOutStep_get_subtrahend
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) (x : Data) :
    subtrahend.get
        (borrowOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo x) =
      subtrahend.get x := by
  change subtrahend.get
      (minuend.flip
        (carryOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo (minuend.flip x))) =
    subtrahend.get x
  rw [EncodedBit.get_flip_of_wire_ne minuend subtrahend hms]
  have hpres :
      subtrahend.get
          (carryOutStep minuend subtrahend borrowIn borrowOut
            hms hmbi hmbo hsbi hsbo hbibo (minuend.flip x)) =
        subtrahend.get (minuend.flip x) := by
    simp [carryOutStep, carryOutGates, EncodedBit.GateSpec.stepList,
      EncodedBit.GateSpec.step, EncodedBit.toffoliStep_get_of_target_ne,
      Ne.symm hsbo]
  rw [hpres]
  rw [EncodedBit.get_flip_of_wire_ne minuend subtrahend hms]

/-- The local borrow block preserves the input borrow readout. -/
lemma borrowOutStep_get_borrowIn
    (minuend subtrahend borrowIn borrowOut : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire) (x : Data) :
    borrowIn.get
        (borrowOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo x) =
      borrowIn.get x := by
  change borrowIn.get
      (minuend.flip
        (carryOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo (minuend.flip x))) =
    borrowIn.get x
  rw [EncodedBit.get_flip_of_wire_ne minuend borrowIn hmbi]
  have hpres :
      borrowIn.get
          (carryOutStep minuend subtrahend borrowIn borrowOut
            hms hmbi hmbo hsbi hsbo hbibo (minuend.flip x)) =
        borrowIn.get (minuend.flip x) := by
    simp [carryOutStep, carryOutGates, EncodedBit.GateSpec.stepList,
      EncodedBit.GateSpec.step, EncodedBit.toffoliStep_get_of_target_ne,
      Ne.symm hbibo]
  rw [hpres]
  rw [EncodedBit.get_flip_of_wire_ne minuend borrowIn hmbi]

/-- The separate-output carry block preserves the left input readout. -/
lemma carryOutStep_get_left
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data) :
    left.get
        (carryOutStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      left.get x := by
  simp [carryOutStep, carryOutGates, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, EncodedBit.toffoliStep_get_of_target_ne,
    Ne.symm hlco]

/-- The separate-output carry block preserves the right input readout. -/
lemma carryOutStep_get_right
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data) :
    right.get
        (carryOutStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      right.get x := by
  simp [carryOutStep, carryOutGates, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, EncodedBit.toffoliStep_get_of_target_ne,
    Ne.symm hrco]

/-- The separate-output carry block preserves the input carry readout. -/
lemma carryOutStep_get_carryIn
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data) :
    carryIn.get
        (carryOutStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      carryIn.get x := by
  simp [carryOutStep, carryOutGates, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, EncodedBit.toffoliStep_get_of_target_ne,
    Ne.symm hcico]

/-- The separate-output carry block preserves any readout whose wire is not the
output carry wire. -/
lemma carryOutStep_get_of_carryOut_ne
    (left right carryIn carryOut observed : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire)
    (hobs : carryOut.wire ≠ observed.wire) (x : Data) :
    observed.get
        (carryOutStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      observed.get x := by
  simp [carryOutStep, carryOutGates, EncodedBit.GateSpec.stepList,
    EncodedBit.GateSpec.step, EncodedBit.toffoliStep_get_of_target_ne, hobs]

/-- The local borrow block preserves any readout whose wire is distinct from
both the temporary minuend flip and the borrow-output wire. -/
lemma borrowOutStep_get_of_minuend_borrowOut_ne
    (minuend subtrahend borrowIn borrowOut observed : EncodedBit encoding)
    (hms : minuend.wire ≠ subtrahend.wire)
    (hmbi : minuend.wire ≠ borrowIn.wire)
    (hmbo : minuend.wire ≠ borrowOut.wire)
    (hsbi : subtrahend.wire ≠ borrowIn.wire)
    (hsbo : subtrahend.wire ≠ borrowOut.wire)
    (hbibo : borrowIn.wire ≠ borrowOut.wire)
    (hmo : minuend.wire ≠ observed.wire)
    (hboo : borrowOut.wire ≠ observed.wire) (x : Data) :
    observed.get
        (borrowOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo x) =
      observed.get x := by
  change observed.get
      (minuend.flip
        (carryOutStep minuend subtrahend borrowIn borrowOut
          hms hmbi hmbo hsbi hsbo hbibo (minuend.flip x))) =
    observed.get x
  rw [EncodedBit.get_flip_of_wire_ne minuend observed hmo]
  rw [carryOutStep_get_of_carryOut_ne minuend subtrahend borrowIn borrowOut
    observed hms hmbi hmbo hsbi hsbo hbibo hboo]
  rw [EncodedBit.get_flip_of_wire_ne minuend observed hmo]

/-- Reverse gate list for the local separate-output carry block.  This is the
local cleanup primitive used when the surrounding schedule has not yet changed
the carry block's control readouts [VBE95, 9511018.tex:254-264,596-618]. -/
def carryOutCleanupGates (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) :
    List (EncodedBit.GateSpec encoding) :=
  (carryOutGates left right carryIn carryOut
    hlr hlci hlco hrci hrco hcico).reverse

/-- The reverse local carry cleanup gate list is disjoint from an observed bit
when all four participating wires are disjoint from it. -/
lemma carryOutCleanupGates_bitDisjoint
    (left right carryIn carryOut observed : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire)
    (hleft : left.wire ≠ observed.wire)
    (hright : right.wire ≠ observed.wire)
    (hcarryIn : carryIn.wire ≠ observed.wire)
    (hcarryOut : carryOut.wire ≠ observed.wire) :
    ∀ gate, gate ∈ carryOutCleanupGates left right carryIn carryOut
        hlr hlci hlco hrci hrco hcico ->
      EncodedBit.GateSpec.bitDisjoint observed gate := by
  intro gate hmem
  have hforward :
      gate ∈ carryOutGates left right carryIn carryOut
        hlr hlci hlco hrci hrco hcico := by
    simpa [carryOutCleanupGates] using hmem
  exact carryOutGates_bitDisjoint left right carryIn carryOut observed
    hlr hlci hlco hrci hrco hcico hleft hright hcarryIn hcarryOut gate
    hforward

/-- Folded semantic action of the reverse local separate-output carry block. -/
def carryOutCleanupStep (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) :
    Data -> Data :=
  EncodedBit.GateSpec.stepList
    (carryOutCleanupGates left right carryIn carryOut
      hlr hlci hlco hrci hrco hcico)

/-- Closed-form output readout of the reverse separate-output carry block. -/
lemma carryOutCleanupStep_get_carryOut
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data) :
    carryOut.get
        (carryOutCleanupStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      (((carryOut.get x ^^ (right.get x && carryIn.get x)) ^^
          (left.get x && carryIn.get x)) ^^
        (left.get x && right.get x)) := by
  simp [carryOutCleanupStep, carryOutCleanupGates, carryOutGates,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.toffoliStep_get_target,
    EncodedBit.toffoliStep_get_of_target_ne, Ne.symm hlco, Ne.symm hrco,
    Ne.symm hcico]

/-- If the separate-output carry wire currently stores the full-adder carry,
the reverse block restores it to zero. -/
lemma carryOutCleanupStep_get_carryOut_computed
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data)
    (hcomputed : carryOut.get x =
      Bool.carry (left.get x) (right.get x) (carryIn.get x)) :
    carryOut.get
        (carryOutCleanupStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) = false := by
  rw [carryOutCleanupStep_get_carryOut]
  generalize hleft : left.get x = leftVal
  generalize hright : right.get x = rightVal
  generalize hcarry : carryIn.get x = carryVal
  generalize hout : carryOut.get x = outVal
  cases leftVal <;> cases rightVal <;> cases carryVal <;> cases outVal <;>
    simp_all [Bool.carry]

/-- The reverse separate-output carry block preserves the left input readout. -/
lemma carryOutCleanupStep_get_left
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data) :
    left.get
        (carryOutCleanupStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      left.get x := by
  simp [carryOutCleanupStep, carryOutCleanupGates, carryOutGates,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.toffoliStep_get_of_target_ne, Ne.symm hlco]

/-- The reverse separate-output carry block preserves the right input readout. -/
lemma carryOutCleanupStep_get_right
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data) :
    right.get
        (carryOutCleanupStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      right.get x := by
  simp [carryOutCleanupStep, carryOutCleanupGates, carryOutGates,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.toffoliStep_get_of_target_ne, Ne.symm hrco]

/-- The reverse separate-output carry block preserves the input carry readout. -/
lemma carryOutCleanupStep_get_carryIn
    (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) (x : Data) :
    carryIn.get
        (carryOutCleanupStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      carryIn.get x := by
  simp [carryOutCleanupStep, carryOutCleanupGates, carryOutGates,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.toffoliStep_get_of_target_ne, Ne.symm hcico]

/-- The reverse separate-output carry block preserves any readout whose wire is
not the output carry wire. -/
lemma carryOutCleanupStep_get_of_carryOut_ne
    (left right carryIn carryOut observed : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire)
    (hobs : carryOut.wire ≠ observed.wire) (x : Data) :
    observed.get
        (carryOutCleanupStep left right carryIn carryOut
          hlr hlci hlco hrci hrco hcico x) =
      observed.get x := by
  simp [carryOutCleanupStep, carryOutCleanupGates, carryOutGates,
    EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step,
    EncodedBit.toffoliStep_get_of_target_ne, hobs]

/-- The local separate-output carry program realizes its folded bit
semantics. -/
lemma carryOut_realizes (left right carryIn carryOut : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlci : left.wire ≠ carryIn.wire)
    (hlco : left.wire ≠ carryOut.wire) (hrci : right.wire ≠ carryIn.wire)
    (hrco : right.wire ≠ carryOut.wire)
    (hcico : carryIn.wire ≠ carryOut.wire) :
    UnitaryCircuit.Realizes encoding
      (carryOutProgram left right carryIn carryOut
        hlr hlci hlco hrci hrco hcico) environment
      (carryOutStep left right carryIn carryOut
        hlr hlci hlco hrci hrco hcico) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (carryOutGates left right carryIn carryOut
      hlr hlci hlco hrci hrco hcico)

/-- Local encoded two-bit target-add block: compute the low-bit carry into the
high target bit, then xor the high and low source bits into the target pair.
It is a reusable VBE-style bit-slice ingredient, not a complete word-level
adder invariant [VBE95, 9511018.tex:244-264,591-618]. -/
def targetAdd2Gates (srcLo tgtLo srcHi tgtHi : EncodedBit encoding)
    (hSrcLoTgtLo : srcLo.wire ≠ tgtLo.wire)
    (hSrcLoTgtHi : srcLo.wire ≠ tgtHi.wire)
    (hTgtLoTgtHi : tgtLo.wire ≠ tgtHi.wire)
    (hSrcHiTgtHi : srcHi.wire ≠ tgtHi.wire) :
    List (EncodedBit.GateSpec encoding) :=
  [ EncodedBit.GateSpec.toffoli srcLo tgtLo tgtHi
      hSrcLoTgtLo hSrcLoTgtHi hTgtLoTgtHi
  , EncodedBit.GateSpec.cnot srcHi tgtHi hSrcHiTgtHi
  , EncodedBit.GateSpec.cnot srcLo tgtLo hSrcLoTgtLo ]

/-- Base-gate program for the local encoded two-bit target-add block. -/
def targetAdd2Program (srcLo tgtLo srcHi tgtHi : EncodedBit encoding)
    (hSrcLoTgtLo : srcLo.wire ≠ tgtLo.wire)
    (hSrcLoTgtHi : srcLo.wire ≠ tgtHi.wire)
    (hTgtLoTgtHi : tgtLo.wire ≠ tgtHi.wire)
    (hSrcHiTgtHi : srcHi.wire ≠ tgtHi.wire) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical (encoding.width)).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (targetAdd2Gates srcLo tgtLo srcHi tgtHi
      hSrcLoTgtLo hSrcLoTgtHi hTgtLoTgtHi hSrcHiTgtHi)

/-- Folded semantic action of the local encoded two-bit target-add block. -/
def targetAdd2Step (srcLo tgtLo srcHi tgtHi : EncodedBit encoding)
    (hSrcLoTgtLo : srcLo.wire ≠ tgtLo.wire)
    (hSrcLoTgtHi : srcLo.wire ≠ tgtHi.wire)
    (hTgtLoTgtHi : tgtLo.wire ≠ tgtHi.wire)
    (hSrcHiTgtHi : srcHi.wire ≠ tgtHi.wire) :
    Data -> Data :=
  EncodedBit.GateSpec.stepList
    (targetAdd2Gates srcLo tgtLo srcHi tgtHi
      hSrcLoTgtLo hSrcLoTgtHi hTgtLoTgtHi hSrcHiTgtHi)

/-- The local encoded two-bit target-add program realizes its folded bit
semantics. -/
lemma targetAdd2_realizes (srcLo tgtLo srcHi tgtHi : EncodedBit encoding)
    (hSrcLoTgtLo : srcLo.wire ≠ tgtLo.wire)
    (hSrcLoTgtHi : srcLo.wire ≠ tgtHi.wire)
    (hTgtLoTgtHi : tgtLo.wire ≠ tgtHi.wire)
    (hSrcHiTgtHi : srcHi.wire ≠ tgtHi.wire) :
    UnitaryCircuit.Realizes encoding
      (targetAdd2Program srcLo tgtLo srcHi tgtHi
        hSrcLoTgtLo hSrcLoTgtHi hTgtLoTgtHi hSrcHiTgtHi) environment
      (targetAdd2Step srcLo tgtLo srcHi tgtHi
        hSrcLoTgtLo hSrcLoTgtHi hTgtLoTgtHi hSrcHiTgtHi) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (targetAdd2Gates srcLo tgtLo srcHi tgtHi
      hSrcLoTgtLo hSrcLoTgtHi hTgtLoTgtHi hSrcHiTgtHi)

/-- A three-gate majority-style carry-propagation block.  The exact Boolean
meaning is the folded action of the listed encoded-bit gates; full adder
schedules state the word-level invariant separately. -/
def majorityGates (left right carry : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlc : left.wire ≠ carry.wire)
    (hrc : right.wire ≠ carry.wire) :
    List (EncodedBit.GateSpec encoding) :=
  [ EncodedBit.GateSpec.cnot carry right (Ne.symm hrc)
  , EncodedBit.GateSpec.cnot carry left (Ne.symm hlc)
  , EncodedBit.GateSpec.toffoli left right carry hlr hlc hrc ]

/-- The reverse cleanup block corresponding to `majorityGates`. -/
def unmajorityGates (left right carry : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlc : left.wire ≠ carry.wire)
    (hrc : right.wire ≠ carry.wire) :
    List (EncodedBit.GateSpec encoding) :=
  [ EncodedBit.GateSpec.toffoli left right carry hlr hlc hrc
  , EncodedBit.GateSpec.cnot carry left (Ne.symm hlc)
  , EncodedBit.GateSpec.cnot carry right (Ne.symm hrc) ]

@[simp] lemma unmajorityGates_eq_reverse
    (left right carry : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlc : left.wire ≠ carry.wire)
    (hrc : right.wire ≠ carry.wire) :
    unmajorityGates left right carry hlr hlc hrc =
      (majorityGates left right carry hlr hlc hrc).reverse :=
  rfl

/-- Base-gate program for the local majority-style block. -/
def majorityProgram (left right carry : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlc : left.wire ≠ carry.wire)
    (hrc : right.wire ≠ carry.wire) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (majorityGates left right carry hlr hlc hrc)

/-- Base-gate program for the reverse cleanup block. -/
def unmajorityProgram (left right carry : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlc : left.wire ≠ carry.wire)
    (hrc : right.wire ≠ carry.wire) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
    (unmajorityGates left right carry hlr hlc hrc)

/-- Folded semantic action of the local majority-style block. -/
def majorityStep (left right carry : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlc : left.wire ≠ carry.wire)
    (hrc : right.wire ≠ carry.wire) : Data → Data :=
  EncodedBit.GateSpec.stepList
    (majorityGates left right carry hlr hlc hrc)

/-- Folded semantic action of the reverse cleanup block. -/
def unmajorityStep (left right carry : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlc : left.wire ≠ carry.wire)
    (hrc : right.wire ≠ carry.wire) : Data → Data :=
  EncodedBit.GateSpec.stepList
    (unmajorityGates left right carry hlr hlc hrc)

/-- The local majority-style program realizes its folded bit semantics. -/
lemma majority_realizes (left right carry : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlc : left.wire ≠ carry.wire)
    (hrc : right.wire ≠ carry.wire) :
    UnitaryCircuit.Realizes encoding
      (majorityProgram left right carry hlr hlc hrc) environment
      (majorityStep left right carry hlr hlc hrc) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (majorityGates left right carry hlr hlc hrc)

/-- The reverse cleanup program realizes its folded bit semantics. -/
lemma unmajority_realizes (left right carry : EncodedBit encoding)
    (hlr : left.wire ≠ right.wire) (hlc : left.wire ≠ carry.wire)
    (hrc : right.wire ≠ carry.wire) :
    UnitaryCircuit.Realizes encoding
      (unmajorityProgram left right carry hlr hlc hrc) environment
      (unmajorityStep left right carry hlr hlc hrc) :=
  EncodedBit.GateSpec.realizesList (environment := environment) (QubitLayout.canonical _) .empty
    (unmajorityGates left right carry hlr hlc hrc)

end Encoded

end

end BitSlice
end QuantumAlg

end
