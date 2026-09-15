/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.MK.DataPath.Counter
import all QuantumAlg.Components.Encoded.BitGates.Word.ZeroTest

/-!
# Compact active-`v=0` termination detector

The detector is a physical compute-copy-uncompute zero test on the one active
bit followed by the `v` word.  Its only borrowed workspace is the first
`tail` positions of the existing VBE coefficient-carry bank for
`n = tail + 1`; no comparison, path, correction-counter, carry-in, or target
wire participates.
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace MK
namespace Compact

noncomputable section

open Nat.FixedWidth

/-- The compact active flag used as the leading source bit of the termination
test. -/
def activeVZeroActiveBit (tail counterWidth : Nat) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftCoreBit tail.succ counterWidth
    (RegisterBits.activeBit tail.succ counterWidth)

/-- One little-endian `v` value bit used after the active source bit. -/
def activeVZeroVBit (tail counterWidth : Nat) (bit : Fin tail.succ) :
    EncodedBit (encoding tail.succ counterWidth) :=
  liftCoreBit tail.succ counterWidth
    (RegisterBits.vValueBit tail.succ counterWidth bit)

/-- The `v` index represented by a non-leading source position. -/
def activeVZeroSourceVIndex {tail : Nat} (bit : Fin (tail + 2))
    (_hbit : bit.val ≠ 0) : Fin tail.succ :=
  ⟨bit.val - 1, by
    have hlt := bit.isLt
    omega⟩

@[simp] theorem activeVZeroSourceVIndex_val {tail : Nat}
    (bit : Fin (tail + 2)) (hbit : bit.val ≠ 0) :
    (activeVZeroSourceVIndex bit hbit).val = bit.val - 1 :=
  rfl

/-- Source bit order for the width-`tail + 2` zero test: active first, then
the `tail + 1` little-endian value bits of `v`. -/
def activeVZeroSourceBit (tail counterWidth : Nat) (bit : Fin (tail + 2)) :
    EncodedBit (encoding tail.succ counterWidth) :=
  if hbit : bit.val = 0 then activeVZeroActiveBit tail counterWidth
  else activeVZeroVBit tail counterWidth
    (activeVZeroSourceVIndex bit hbit)

@[simp] theorem activeVZeroSourceBit_zero (tail counterWidth : Nat) :
    activeVZeroSourceBit tail counterWidth (0 : Fin (tail + 2)) =
      activeVZeroActiveBit tail counterWidth := by
  simp [activeVZeroSourceBit]

@[simp] theorem activeVZeroSourceBit_succ
    (tail counterWidth : Nat) (bit : Fin tail.succ) :
    activeVZeroSourceBit tail counterWidth bit.succ =
      activeVZeroVBit tail counterWidth bit := by
  simp [activeVZeroSourceBit, activeVZeroSourceVIndex]

/-- The source word `[active, v₀, ..., v_tail]` before its outer active-bit
negation. -/
def activeVZeroSourceWord (tail counterWidth : Nat) :
    EncodedBit.Word (encoding tail.succ counterWidth) (tail + 2) where
  bit := activeVZeroSourceBit tail counterWidth

/-- The prefix of the existing VBE carry bank borrowed for the conjunction
chain.  It has exactly `tail` positions for a source of width `tail + 2`. -/
def activeVZeroWorkBit (tail counterWidth : Nat) (bit : Fin tail) :
    EncodedBit (encoding tail.succ counterWidth) :=
  coefficientCarryWorkBit tail.succ counterWidth bit.castSucc

/-- The unique borrowed `tail`-bit VBE carry prefix. -/
def activeVZeroWorkWord (tail counterWidth : Nat) :
    EncodedBit.Word (encoding tail.succ counterWidth) tail where
  bit := activeVZeroWorkBit tail counterWidth

@[simp] theorem activeVZeroActiveBit_get
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (activeVZeroActiveBit tail counterWidth).get x = x.core.active := by
  simpa [activeVZeroActiveBit] using
    RegisterBits.activeBit_get tail.succ counterWidth x.core

@[simp] theorem activeVZeroVBit_get
    (tail counterWidth : Nat) (bit : Fin tail.succ)
    (x : Registers tail.succ counterWidth) :
    (activeVZeroVBit tail counterWidth bit).get x =
      x.core.v.val.testBit bit.val := by
  rw [activeVZeroVBit, liftCoreBit_get]
  exact RegisterBits.vValueBit_get tail.succ counterWidth bit x.core

/-- The active source wire is distinct from each `v` source wire. -/
theorem activeVZeroActiveBit_vBit_wire_ne
    (tail counterWidth : Nat) (bit : Fin tail.succ) :
    (activeVZeroActiveBit tail counterWidth).wire ≠
      (activeVZeroVBit tail counterWidth bit).wire := by
  simpa [activeVZeroActiveBit, activeVZeroVBit,
    RegisterBits.vValueBit] using
    liftCoreBit_wire_ne tail.succ counterWidth
      (RegisterBits.active_v_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire bit))

/-- The outer active X is disjoint from every borrowed carry-prefix bit. -/
theorem activeVZeroActiveBit_workBit_wire_ne
    (tail counterWidth : Nat) (work : Fin tail) :
    (activeVZeroActiveBit tail counterWidth).wire ≠
      (activeVZeroWorkBit tail counterWidth work).wire := by
  simpa [activeVZeroActiveBit, activeVZeroWorkBit] using
    liftCoreBit_coefficientCarryWorkBit_wire_ne tail.succ counterWidth
      (RegisterBits.activeBit tail.succ counterWidth) work.castSucc

/-- Distinct `v` source indices select distinct compact wires. -/
theorem activeVZeroVBit_wire_ne
    (tail counterWidth : Nat) {left right : Fin tail.succ} (hne : left ≠ right) :
    (activeVZeroVBit tail counterWidth left).wire ≠
      (activeVZeroVBit tail counterWidth right).wire := by
  simpa [activeVZeroVBit, RegisterBits.vValueBit] using
    liftCoreBit_wire_ne tail.succ counterWidth
      (v_v_wire_ne tail.succ counterWidth
        (WireAddress.littleEndianWire left)
        (WireAddress.littleEndianWire right)
        (littleEndianWire_ne hne))

/-- Distinct source positions of `[active, v]` select distinct wires. -/
theorem activeVZeroSourceBit_wire_ne
    (tail counterWidth : Nat) {left right : Fin (tail + 2)} (hne : left ≠ right) :
    (activeVZeroSourceBit tail counterWidth left).wire ≠
      (activeVZeroSourceBit tail counterWidth right).wire := by
  by_cases hleft : left.val = 0
  · have hright : right.val ≠ 0 := by
      intro hright
      apply hne
      apply Fin.ext
      omega
    rw [show activeVZeroSourceBit tail counterWidth left =
      activeVZeroActiveBit tail counterWidth by simp [activeVZeroSourceBit, hleft],
      show activeVZeroSourceBit tail counterWidth right =
        activeVZeroVBit tail counterWidth
          (activeVZeroSourceVIndex right hright) by
        simp [activeVZeroSourceBit, hright]]
    exact activeVZeroActiveBit_vBit_wire_ne tail counterWidth _
  · by_cases hright : right.val = 0
    · rw [show activeVZeroSourceBit tail counterWidth left =
        activeVZeroVBit tail counterWidth
          (activeVZeroSourceVIndex left hleft) by
          simp [activeVZeroSourceBit, hleft],
        show activeVZeroSourceBit tail counterWidth right =
          activeVZeroActiveBit tail counterWidth by
          simp [activeVZeroSourceBit, hright]]
      exact (activeVZeroActiveBit_vBit_wire_ne tail counterWidth _).symm
    · rw [show activeVZeroSourceBit tail counterWidth left =
        activeVZeroVBit tail counterWidth
          (activeVZeroSourceVIndex left hleft) by
          simp [activeVZeroSourceBit, hleft],
        show activeVZeroSourceBit tail counterWidth right =
          activeVZeroVBit tail counterWidth
            (activeVZeroSourceVIndex right hright) by
            simp [activeVZeroSourceBit, hright]]
      apply activeVZeroVBit_wire_ne tail counterWidth
      intro hindex
      apply hne
      apply Fin.ext
      have hval := congrArg Fin.val hindex
      simp only [activeVZeroSourceVIndex_val] at hval
      omega

/-- Every source wire is disjoint from the control-xor output. -/
theorem activeVZeroSourceBit_controlBit_wire_ne
    (tail counterWidth : Nat) (source : Fin (tail + 2)) :
    (activeVZeroSourceBit tail counterWidth source).wire ≠
      (controlBit tail.succ counterWidth).wire := by
  by_cases hsource : source.val = 0
  · rw [show activeVZeroSourceBit tail counterWidth source =
      activeVZeroActiveBit tail counterWidth by
      simp [activeVZeroSourceBit, hsource]]
    simpa [activeVZeroActiveBit, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.activeBit tail.succ counterWidth)
        (sharedControlBit tail.succ counterWidth)
  · rw [show activeVZeroSourceBit tail counterWidth source =
      activeVZeroVBit tail counterWidth
        (activeVZeroSourceVIndex source hsource) by
        simp [activeVZeroSourceBit, hsource]]
    simpa [activeVZeroVBit, controlBit] using
      liftCoreBit_liftSharedBit_wire_ne tail.succ counterWidth
        (RegisterBits.vValueBit tail.succ counterWidth
          (activeVZeroSourceVIndex source hsource))
        (sharedControlBit tail.succ counterWidth)

/-- Every source wire is disjoint from every borrowed carry-prefix bit. -/
theorem activeVZeroSourceBit_workBit_wire_ne
    (tail counterWidth : Nat) (source : Fin (tail + 2)) (work : Fin tail) :
    (activeVZeroSourceBit tail counterWidth source).wire ≠
      (activeVZeroWorkBit tail counterWidth work).wire := by
  by_cases hsource : source.val = 0
  · rw [show activeVZeroSourceBit tail counterWidth source =
      activeVZeroActiveBit tail counterWidth by
      simp [activeVZeroSourceBit, hsource]]
    simpa [activeVZeroActiveBit, activeVZeroWorkBit] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne tail.succ counterWidth
        (RegisterBits.activeBit tail.succ counterWidth) work.castSucc
  · rw [show activeVZeroSourceBit tail counterWidth source =
      activeVZeroVBit tail counterWidth
        (activeVZeroSourceVIndex source hsource) by
        simp [activeVZeroSourceBit, hsource]]
    simpa [activeVZeroVBit, activeVZeroWorkBit] using
      liftCoreBit_coefficientCarryWorkBit_wire_ne tail.succ counterWidth
        (RegisterBits.vValueBit tail.succ counterWidth
          (activeVZeroSourceVIndex source hsource)) work.castSucc

/-- Distinct borrowed carry-prefix positions remain distinct in the VBE bank. -/
theorem activeVZeroWorkBit_wire_ne
    (tail counterWidth : Nat) {left right : Fin tail} (hne : left ≠ right) :
    (activeVZeroWorkBit tail counterWidth left).wire ≠
      (activeVZeroWorkBit tail counterWidth right).wire := by
  apply coefficientCarryWorkBit_wire_ne tail.succ counterWidth
  intro hcast
  apply hne
  exact (Fin.castSucc_injective tail) hcast

/-- Every borrowed carry-prefix wire is disjoint from the control output. -/
theorem activeVZeroWorkBit_controlBit_wire_ne
    (tail counterWidth : Nat) (work : Fin tail) :
    (activeVZeroWorkBit tail counterWidth work).wire ≠
      (controlBit tail.succ counterWidth).wire := by
  exact (controlBit_coefficientCarryWorkBit_wire_ne tail.succ counterWidth
    work.castSucc).symm

/-- Fully instantiated zero-test layout for the compact active-`v=0`
predicate. -/
def activeVZeroLayout (tail counterWidth : Nat) :
    EncodedBit.Word.ZeroTestLayout
      (encoding := encoding tail.succ counterWidth) tail where
  source := activeVZeroSourceWord tail counterWidth
  output := controlBit tail.succ counterWidth
  work := activeVZeroWorkWord tail counterWidth
  source_source_ne := by
    intro i j hij
    exact activeVZeroSourceBit_wire_ne tail counterWidth hij
  source_output_ne := by
    intro i
    exact activeVZeroSourceBit_controlBit_wire_ne tail counterWidth i
  source_work_ne := by
    intro i j
    exact activeVZeroSourceBit_workBit_wire_ne tail counterWidth i j
  work_work_ne := by
    intro i j hij
    exact activeVZeroWorkBit_wire_ne tail counterWidth hij
  work_output_ne := by
    intro j
    exact activeVZeroWorkBit_controlBit_wire_ne tail counterWidth j

/-- The outer X gate negates the active source bit before and after the
zero-test compute-copy-uncompute sandwich. -/
def activeVZeroActiveGate (tail counterWidth : Nat) :
    EncodedBit.GateSpec (encoding tail.succ counterWidth) :=
  .x (activeVZeroActiveBit tail counterWidth)

/-- Actual X--zero-test--X schedule.  The zero test sees `[!active, v]`, so
its all-zero predicate is exactly `active && v = 0`. -/
def activeVZeroGates (tail counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding tail.succ counterWidth)) :=
  [activeVZeroActiveGate tail counterWidth] ++
    (activeVZeroLayout tail counterWidth).gates ++
    [activeVZeroActiveGate tail counterWidth]

/-- Every source bit of the active-`v=0` detector is disjoint from every
public target bit. -/
theorem activeVZeroSourceBit_targetValueBit_wire_ne
    (tail counterWidth : Nat) (source : Fin (tail + 2))
    (target : Fin tail.succ) :
    (activeVZeroSourceBit tail counterWidth source).wire ≠
      (targetValueBit tail.succ counterWidth target).wire := by
  by_cases hsource : source.val = 0
  · have hsourceEq : source = 0 := Fin.ext hsource
    rw [hsourceEq, activeVZeroSourceBit_zero]
    simpa [activeVZeroActiveBit, targetValueBit] using
      liftCoreBit_targetBit_wire_ne tail.succ counterWidth
        (RegisterBits.activeBit tail.succ counterWidth)
        (WireAddress.littleEndianWire target)
  · rw [activeVZeroSourceBit, dif_neg hsource]
    simpa [activeVZeroVBit, targetValueBit] using
      liftCoreBit_targetBit_wire_ne tail.succ counterWidth
        (RegisterBits.vValueBit tail.succ counterWidth
          (activeVZeroSourceVIndex source hsource))
        (WireAddress.littleEndianWire target)

/-- Every borrowed VBE work bit of the active-`v=0` detector is disjoint from
every public target bit. -/
theorem activeVZeroWorkBit_targetValueBit_wire_ne
    (tail counterWidth : Nat) (work : Fin tail) (target : Fin tail.succ) :
    (activeVZeroWorkBit tail counterWidth work).wire ≠
      (targetValueBit tail.succ counterWidth target).wire := by
  simpa [activeVZeroWorkBit, coefficientCarryWorkBit, targetValueBit] using
    liftSharedBit_targetBit_wire_ne tail.succ counterWidth
      (sharedCoefficientCarryWorkBit tail.succ counterWidth work.castSucc)
      (WireAddress.littleEndianWire target)

/-- The active-`v=0` detector control is disjoint from every public target bit. -/
theorem controlBit_targetValueBit_wire_ne
    (n counterWidth : Nat) (target : Fin n) :
    (controlBit n counterWidth).wire ≠
      (targetValueBit n counterWidth target).wire := by
  simpa [controlBit, targetValueBit] using
    liftSharedBit_targetBit_wire_ne n counterWidth
      (sharedControlBit n counterWidth)
      (WireAddress.littleEndianWire target)

/-- The active source bit is disjoint from every public target bit. -/
theorem activeVZeroActiveBit_targetValueBit_wire_ne
    (tail counterWidth : Nat) (target : Fin tail.succ) :
    (activeVZeroActiveBit tail counterWidth).wire ≠
      (targetValueBit tail.succ counterWidth target).wire := by
  simpa [activeVZeroActiveBit, targetValueBit] using
    liftCoreBit_targetBit_wire_ne tail.succ counterWidth
      (RegisterBits.activeBit tail.succ counterWidth)
      (WireAddress.littleEndianWire target)

/-- The active-`v=0` detector never reads or writes a public target bit. -/
theorem activeVZeroGates_bitDisjoint_target
    (tail counterWidth : Nat) (target : Fin tail.succ) :
    ∀ gate, gate ∈ activeVZeroGates tail counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit tail.succ counterWidth target) gate := by
  intro gate hgate
  rw [activeVZeroGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | hlast
  · rcases List.mem_append.mp hprefix with hfirst | htest
    · rw [List.mem_singleton] at hfirst
      subst gate
      exact activeVZeroActiveBit_targetValueBit_wire_ne tail counterWidth target
    · exact EncodedBit.Word.ZeroTestLayout.gates_bitDisjoint
        (activeVZeroLayout tail counterWidth)
        (targetValueBit tail.succ counterWidth target)
        (fun source =>
          activeVZeroSourceBit_targetValueBit_wire_ne
            tail counterWidth source target)
        (controlBit_targetValueBit_wire_ne tail.succ counterWidth target)
        (fun work =>
          activeVZeroWorkBit_targetValueBit_wire_ne
            tail counterWidth work target)
        gate htest
  · rw [List.mem_singleton] at hlast
    subst gate
    exact activeVZeroActiveBit_targetValueBit_wire_ne tail counterWidth target

/-- Physical circuit compiled from the exact active-`v=0` gate list. -/
def activeVZeroProgram (tail counterWidth : Nat) :
    UnitaryCircuit (Qubits (encoding tail.succ counterWidth).width) :=
  EncodedBit.GateSpec.programList (activeVZeroGates tail counterWidth)

/-- Folded semantic step of the active-`v=0` detector. -/
def activeVZeroStep (tail counterWidth : Nat) :
    Registers tail.succ counterWidth → Registers tail.succ counterWidth :=
  EncodedBit.GateSpec.stepList (activeVZeroGates tail counterWidth)

/-- The compiled detector realizes its exact folded bit-lens action. -/
theorem activeVZero_realizes (tail counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding tail.succ counterWidth)
      (activeVZeroProgram tail counterWidth)
      (activeVZeroStep tail counterWidth) :=
  EncodedBit.GateSpec.realizesList (activeVZeroGates tail counterWidth)

/-- Exact X coordinate: two outer active X gates plus the clean zero test. -/
theorem activeVZeroGates_xMultiplicity_sum (tail counterWidth : Nat) :
    ((activeVZeroGates tail counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 2 * tail + 6 := by
  simp [activeVZeroGates, activeVZeroActiveGate,
    EncodedBit.Word.ZeroTestLayout.gates_xMultiplicity_sum]
  omega

/-- The active-`v=0` detector contains no CNOT leaves. -/
theorem activeVZeroGates_cnotMultiplicity_sum (tail counterWidth : Nat) :
    ((activeVZeroGates tail counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp [activeVZeroGates, activeVZeroActiveGate,
    EncodedBit.Word.ZeroTestLayout.gates_cnotMultiplicity_sum]

/-- Exact Toffoli coordinate inherited from the `tail`-work-bit zero test. -/
theorem activeVZeroGates_toffoliMultiplicity_sum (tail counterWidth : Nat) :
    ((activeVZeroGates tail counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 * tail + 1 := by
  simp [activeVZeroGates, activeVZeroActiveGate,
    EncodedBit.Word.ZeroTestLayout.gates_toffoliMultiplicity_sum]

/-- Exact primitive-gate length of the active-`v=0` detector. -/
theorem activeVZeroGates_length (tail counterWidth : Nat) :
    (activeVZeroGates tail counterWidth).length = 4 * tail + 7 := by
  rw [EncodedBit.GateSpec.length_eq_multiplicity_sums,
    activeVZeroGates_xMultiplicity_sum,
    activeVZeroGates_cnotMultiplicity_sum,
    activeVZeroGates_toffoliMultiplicity_sum]
  omega

/-- The compiled detector retains its exact X count. -/
theorem activeVZeroProgram_x_count (tail counterWidth : Nat) :
    ResourcePool.count (.gate (.builtin "x"))
        (activeVZeroProgram tail counterWidth).eventCost = 2 * tail + 6 := by
  rw [activeVZeroProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum,
    activeVZeroGates_xMultiplicity_sum]

/-- The compiled detector retains its exact zero CNOT count. -/
theorem activeVZeroProgram_cnot_count (tail counterWidth : Nat) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (activeVZeroProgram tail counterWidth).eventCost = 0 := by
  rw [activeVZeroProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    activeVZeroGates_cnotMultiplicity_sum]

/-- The compiled detector retains its exact Toffoli count. -/
theorem activeVZeroProgram_toffoli_count (tail counterWidth : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (activeVZeroProgram tail counterWidth).eventCost = 2 * tail + 1 := by
  rw [activeVZeroProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    activeVZeroGates_toffoliMultiplicity_sum]

/-- A clean VBE coefficient-adder object makes every borrowed conjunction
work bit clean, including naturally the empty `tail = 0` prefix. -/
theorem activeVZeroWorkBit_get_of_coefficientAdder_clean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork tail.succ)
    (bit : Fin tail) :
    (activeVZeroWorkBit tail counterWidth bit).get x = false := by
  change (BinaryLabelEncoding.finIdentityBit tail.succ bit.castSucc).get
      x.shared.coefficientAdder.2 = false
  rw [hcoeff]
  exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero tail.succ
    bit.castSucc

/-- The leading active X leaves the borrowed VBE carry prefix clean. -/
theorem activeVZeroWorkBit_get_activeFlip_of_coefficientAdder_clean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork tail.succ)
    (bit : Fin tail) :
    (activeVZeroWorkBit tail counterWidth bit).get
        ((activeVZeroActiveBit tail counterWidth).flip x) = false := by
  rw [EncodedBit.get_flip_of_wire_ne
    (activeVZeroActiveBit tail counterWidth)
    (activeVZeroWorkBit tail counterWidth bit)
    (activeVZeroActiveBit_workBit_wire_ne tail counterWidth bit)]
  exact activeVZeroWorkBit_get_of_coefficientAdder_clean
    tail counterWidth x hcoeff bit

/-- Symbolic, non-enumerative characterization of the zero-test source after
the leading active X: it is all false exactly on an active state with `v = 0`.
-/
theorem activeVZeroSource_all_false_after_activeFlip_iff
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (∀ source, ((activeVZeroSourceWord tail counterWidth).bit source).get
        ((activeVZeroActiveBit tail counterWidth).flip x) = false) ↔
      x.core.active = true ∧ x.core.v = 0 := by
  constructor
  · intro hsource
    have hactive := hsource (0 : Fin (tail + 2))
    change (activeVZeroSourceBit tail counterWidth (0 : Fin (tail + 2))).get
        ((activeVZeroActiveBit tail counterWidth).flip x) = false at hactive
    rw [activeVZeroSourceBit_zero, EncodedBit.get_flip_self,
      activeVZeroActiveBit_get] at hactive
    have hactiveTrue : x.core.active = true := by
      cases hactiveValue : x.core.active <;> simp_all
    refine ⟨hactiveTrue, ?_⟩
    apply word_eq_of_testBit_eq
    intro bit
    have hbit := hsource bit.succ
    change (activeVZeroSourceBit tail counterWidth bit.succ).get
        ((activeVZeroActiveBit tail counterWidth).flip x) = false at hbit
    rw [activeVZeroSourceBit_succ,
      EncodedBit.get_flip_of_wire_ne
        (activeVZeroActiveBit tail counterWidth)
        (activeVZeroVBit tail counterWidth bit)
        (activeVZeroActiveBit_vBit_wire_ne tail counterWidth bit)] at hbit
    simpa [activeVZeroVBit_get] using hbit
  · rintro ⟨hactive, hvzero⟩ source
    change (activeVZeroSourceBit tail counterWidth source).get
        ((activeVZeroActiveBit tail counterWidth).flip x) = false
    by_cases hsource : source.val = 0
    · rw [show activeVZeroSourceBit tail counterWidth source =
        activeVZeroActiveBit tail counterWidth by
        simp [activeVZeroSourceBit, hsource]]
      rw [EncodedBit.get_flip_self, activeVZeroActiveBit_get, hactive]
      rfl
    · rw [show activeVZeroSourceBit tail counterWidth source =
        activeVZeroVBit tail counterWidth
          (activeVZeroSourceVIndex source hsource) by
          simp [activeVZeroSourceBit, hsource]]
      rw [EncodedBit.get_flip_of_wire_ne
        (activeVZeroActiveBit tail counterWidth)
        (activeVZeroVBit tail counterWidth
          (activeVZeroSourceVIndex source hsource))
        (activeVZeroActiveBit_vBit_wire_ne tail counterWidth _)]
      simp [activeVZeroVBit_get, hvzero]

/-- Expose the outer X--zero-test--X decomposition of the folded step. -/
theorem activeVZeroStep_decompose
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    activeVZeroStep tail counterWidth x =
      (activeVZeroActiveBit tail counterWidth).flip
        ((activeVZeroLayout tail counterWidth).step
          ((activeVZeroActiveBit tail counterWidth).flip x)) := by
  rw [activeVZeroStep, activeVZeroGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rfl

/-- With a clean VBE bank, the generic zero-test final control is exactly the
compact active-`v=0` predicate. -/
theorem activeVZeroFinalControl_eq_predicate
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork tail.succ) :
    EncodedBit.Word.ZeroTestLayout.finalControl
      (activeVZeroLayout tail counterWidth)
      (EncodedBit.GateSpec.stepList
        ((activeVZeroLayout tail counterWidth).computeGates)
        ((activeVZeroActiveBit tail counterWidth).flip x)) =
      (x.core.active && decide (x.core.v = 0)) := by
  have hclean : ∀ work,
      (activeVZeroWorkBit tail counterWidth work).get
        ((activeVZeroActiveBit tail counterWidth).flip x) = false := by
    intro work
    exact activeVZeroWorkBit_get_activeFlip_of_coefficientAdder_clean
      tail counterWidth x hcoeff work
  have hindicator :
      EncodedBit.Word.ZeroTestLayout.finalControl
        (activeVZeroLayout tail counterWidth)
        (EncodedBit.GateSpec.stepList
          ((activeVZeroLayout tail counterWidth).computeGates)
          ((activeVZeroActiveBit tail counterWidth).flip x)) =
        decide (∀ source,
          ((activeVZeroSourceWord tail counterWidth).bit source).get
            ((activeVZeroActiveBit tail counterWidth).flip x) = false) := by
    by_cases hzero : ∀ source,
        ((activeVZeroSourceWord tail counterWidth).bit source).get
          ((activeVZeroActiveBit tail counterWidth).flip x) = false
    · have htrue :=
        (EncodedBit.Word.ZeroTestLayout.finalControl_compute_eq_true_iff
          (activeVZeroLayout tail counterWidth)
          ((activeVZeroActiveBit tail counterWidth).flip x) hclean).mpr hzero
      rw [htrue]
      simp [hzero]
    · have hnotTrue :
        EncodedBit.Word.ZeroTestLayout.finalControl
          (activeVZeroLayout tail counterWidth)
          (EncodedBit.GateSpec.stepList
            ((activeVZeroLayout tail counterWidth).computeGates)
            ((activeVZeroActiveBit tail counterWidth).flip x)) ≠ true := by
        intro htrue
        exact hzero
          ((EncodedBit.Word.ZeroTestLayout.finalControl_compute_eq_true_iff
            (activeVZeroLayout tail counterWidth)
            ((activeVZeroActiveBit tail counterWidth).flip x) hclean).mp htrue)
      have hfalse :
          EncodedBit.Word.ZeroTestLayout.finalControl
            (activeVZeroLayout tail counterWidth)
            (EncodedBit.GateSpec.stepList
              ((activeVZeroLayout tail counterWidth).computeGates)
              ((activeVZeroActiveBit tail counterWidth).flip x)) = false :=
        Bool.eq_false_of_not_eq_true hnotTrue
      rw [hfalse]
      simp [hzero]
  calc
    _ = decide (∀ source,
        ((activeVZeroSourceWord tail counterWidth).bit source).get
          ((activeVZeroActiveBit tail counterWidth).flip x) = false) := hindicator
    _ = (x.core.active && decide (x.core.v = 0)) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq, Bool.and_eq_true] using
        activeVZeroSource_all_false_after_activeFlip_iff tail counterWidth x

/-- Full-state clean endpoint: the actual physical detector leaves every
compact field untouched except for xoring the active-`v=0` predicate into the
shared control bit. -/
theorem activeVZeroStep_eq_controlConditional
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork tail.succ) :
    activeVZeroStep tail counterWidth x =
      if x.core.active && decide (x.core.v = 0) then
        (controlBit tail.succ counterWidth).flip x
      else x := by
  rw [activeVZeroStep_decompose,
    EncodedBit.Word.ZeroTestLayout.step_eq_outputConditional,
    activeVZeroFinalControl_eq_predicate tail counterWidth x hcoeff]
  by_cases hp : (x.core.active && decide (x.core.v = 0)) = true
  · rw [if_pos hp, if_pos hp]
    change (activeVZeroActiveBit tail counterWidth).flip
        ((controlBit tail.succ counterWidth).flip
          ((activeVZeroActiveBit tail counterWidth).flip x)) =
      (controlBit tail.succ counterWidth).flip x
    rw [EncodedBit.flip_comm, EncodedBit.flip_flip]
  · rw [if_neg hp, if_neg hp]
    exact EncodedBit.flip_flip (activeVZeroActiveBit tail counterWidth) x

/-- Control readout form of the full-state endpoint. -/
theorem activeVZeroStep_controlBit_get
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork tail.succ) :
    (controlBit tail.succ counterWidth).get
        (activeVZeroStep tail counterWidth x) =
      ((controlBit tail.succ counterWidth).get x ^^
        (x.core.active && decide (x.core.v = 0))) := by
  rw [activeVZeroStep_eq_controlConditional tail counterWidth x hcoeff]
  by_cases hp : (x.core.active && decide (x.core.v = 0)) = true
  · rw [if_pos hp, EncodedBit.get_flip_self, hp]
    cases (controlBit tail.succ counterWidth).get x <;> rfl
  · rw [if_neg hp]
    have hfalse : (x.core.active && decide (x.core.v = 0)) = false :=
      Bool.eq_false_of_not_eq_true hp
    rw [hfalse, Bool.xor_false]

/-- If the shared control bit is clean at entry, the endpoint stores precisely
the active-`v=0` termination predicate there. -/
theorem activeVZeroStep_control_clean
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork tail.succ)
    (hcontrol : x.shared.control = false) :
    (activeVZeroStep tail counterWidth x).shared.control =
      (x.core.active && decide (x.core.v = 0)) := by
  change (controlBit tail.succ counterWidth).get
      (activeVZeroStep tail counterWidth x) =
        (x.core.active && decide (x.core.v = 0))
  rw [activeVZeroStep_controlBit_get tail counterWidth x hcoeff,
    controlBit_get, hcontrol, Bool.false_xor]

/-- The encoded shared-control flip is exactly the record update that toggles
only that one compact field. -/
theorem activeVZeroControlBit_flip_eq_update
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth) :
    (controlBit tail.succ counterWidth).flip x =
      { x with shared := { x.shared with control := !x.shared.control } } := by
  rfl

/-- Explicit frame form of the clean endpoint.  The core contains both the
original `active` flag and `v`; the unchanged coefficient-adder object contains
the carry-in and every borrowed VBE work bit. -/
theorem activeVZeroStep_cleanEndpoint
    (tail counterWidth : Nat) (x : Registers tail.succ counterWidth)
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork tail.succ) :
    (activeVZeroStep tail counterWidth x).core = x.core ∧
      (activeVZeroStep tail counterWidth x).shared.coefficientAdder =
        x.shared.coefficientAdder ∧
      (activeVZeroStep tail counterWidth x).shared.correctionCounter =
        x.shared.correctionCounter ∧
      (activeVZeroStep tail counterWidth x).shared.path = x.shared.path ∧
      (activeVZeroStep tail counterWidth x).target = x.target ∧
      (activeVZeroStep tail counterWidth x).shared.control =
        (x.shared.control ^^ (x.core.active && decide (x.core.v = 0))) := by
  rw [activeVZeroStep_eq_controlConditional tail counterWidth x hcoeff]
  by_cases hp : (x.core.active && decide (x.core.v = 0)) = true
  · rw [if_pos hp, activeVZeroControlBit_flip_eq_update]
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [hp, Bool.xor_true]
  · rw [if_neg hp]
    have hfalse : (x.core.active && decide (x.core.v = 0)) = false :=
      Bool.eq_false_of_not_eq_true hp
    rw [hfalse, Bool.xor_false]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Compact termination-route prefix -/

/-- The first route-prefix CNOT saves the pre-termination active flag in the
shared path bit. -/
def terminationRoutePrefixActivePathGate (fieldTail counterWidth : Nat) :
    EncodedBit.GateSpec (encoding fieldTail.succ counterWidth) :=
  .cnot (activeVZeroActiveBit fieldTail counterWidth)
    (pathBit fieldTail.succ counterWidth)
    (by
      simpa [activeVZeroActiveBit, pathBit] using
        liftCoreBit_liftSharedBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.activeBit fieldTail.succ counterWidth)
          (sharedPathBit fieldTail.succ counterWidth))

/-- After detecting `active && v = 0`, this CNOT removes that termination
case from the active flag. -/
def terminationRoutePrefixControlActiveGate (fieldTail counterWidth : Nat) :
    EncodedBit.GateSpec (encoding fieldTail.succ counterWidth) :=
  .cnot (controlBit fieldTail.succ counterWidth)
    (activeVZeroActiveBit fieldTail counterWidth)
    (by
      simpa [activeVZeroActiveBit, controlBit] using
        (liftCoreBit_liftSharedBit_wire_ne fieldTail.succ counterWidth
          (RegisterBits.activeBit fieldTail.succ counterWidth)
          (sharedControlBit fieldTail.succ counterWidth)).symm)

/-- The final route-prefix CNOT converts the saved original-active path bit
into the active-and-nonzero routing predicate. -/
def terminationRoutePrefixControlPathGate (fieldTail counterWidth : Nat) :
    EncodedBit.GateSpec (encoding fieldTail.succ counterWidth) :=
  .cnot (controlBit fieldTail.succ counterWidth)
    (pathBit fieldTail.succ counterWidth)
    (pathBit_controlBit_wire_ne fieldTail.succ counterWidth).symm

/-- Physical compact-round prefix: latch old active, test `active && v = 0`,
clear the terminating active flag, then retain the active-and-nonzero path. -/
def terminationRoutePrefixGates (fieldTail counterWidth : Nat) :
    List (EncodedBit.GateSpec (encoding fieldTail.succ counterWidth)) :=
  [terminationRoutePrefixActivePathGate fieldTail counterWidth] ++
    activeVZeroGates fieldTail counterWidth ++
    [terminationRoutePrefixControlActiveGate fieldTail counterWidth,
      terminationRoutePrefixControlPathGate fieldTail counterWidth]

/-- The compact route-path workspace bit is disjoint from every public target
bit. -/
theorem pathBit_targetValueBit_wire_ne
    (n counterWidth : Nat) (target : Fin n) :
    (pathBit n counterWidth).wire ≠
      (targetValueBit n counterWidth target).wire := by
  simpa [pathBit, targetValueBit] using
    liftSharedBit_targetBit_wire_ne n counterWidth
      (sharedPathBit n counterWidth)
      (WireAddress.littleEndianWire target)

/-- The compact termination-route prefix never reads or writes a public target
bit. -/
theorem terminationRoutePrefixGates_bitDisjoint_target
    (fieldTail counterWidth : Nat) (target : Fin fieldTail.succ) :
    ∀ gate, gate ∈ terminationRoutePrefixGates fieldTail counterWidth →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit fieldTail.succ counterWidth target) gate := by
  intro gate hgate
  rw [terminationRoutePrefixGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | htail
  · rcases List.mem_append.mp hprefix with hfirst | hzero
    · rw [List.mem_singleton] at hfirst
      subst gate
      exact ⟨activeVZeroActiveBit_targetValueBit_wire_ne
        fieldTail counterWidth target,
        pathBit_targetValueBit_wire_ne fieldTail.succ counterWidth target⟩
    · exact activeVZeroGates_bitDisjoint_target fieldTail counterWidth target
        gate hzero
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at htail
    rcases htail with hgate | hgate
    · subst gate
      exact ⟨controlBit_targetValueBit_wire_ne
        fieldTail.succ counterWidth target,
        activeVZeroActiveBit_targetValueBit_wire_ne
          fieldTail counterWidth target⟩
    · subst gate
      exact ⟨controlBit_targetValueBit_wire_ne
        fieldTail.succ counterWidth target,
        pathBit_targetValueBit_wire_ne fieldTail.succ counterWidth target⟩

/-- Folded register action of the compact termination-route prefix. -/
def terminationRoutePrefixStep (fieldTail counterWidth : Nat) :
    Registers fieldTail.succ counterWidth → Registers fieldTail.succ counterWidth :=
  EncodedBit.GateSpec.stepList (terminationRoutePrefixGates fieldTail counterWidth)

/-- Physical circuit for the compact termination-route prefix. -/
def terminationRoutePrefixProgram (fieldTail counterWidth : Nat) :
    UnitaryCircuit (Qubits (encoding fieldTail.succ counterWidth).width) :=
  EncodedBit.GateSpec.programList (terminationRoutePrefixGates fieldTail counterWidth)

/-- The physical route-prefix circuit realizes exactly its folded bit-lens
action. -/
theorem terminationRoutePrefix_realizes (fieldTail counterWidth : Nat) :
    UnitaryCircuit.Realizes (encoding fieldTail.succ counterWidth)
      (terminationRoutePrefixProgram fieldTail counterWidth)
      (terminationRoutePrefixStep fieldTail counterWidth) :=
  EncodedBit.GateSpec.realizesList
    (terminationRoutePrefixGates fieldTail counterWidth)

/-- The route prefix adds no X leaves to the active-`v=0` detector. -/
theorem terminationRoutePrefixGates_xMultiplicity_sum
    (fieldTail counterWidth : Nat) :
    ((terminationRoutePrefixGates fieldTail counterWidth).map
      EncodedBit.GateSpec.xMultiplicity).sum = 2 * fieldTail + 6 := by
  simp [terminationRoutePrefixGates, terminationRoutePrefixActivePathGate,
    terminationRoutePrefixControlActiveGate,
    terminationRoutePrefixControlPathGate,
    activeVZeroGates_xMultiplicity_sum]

/-- The route prefix adds exactly its three explicit CNOT leaves. -/
theorem terminationRoutePrefixGates_cnotMultiplicity_sum
    (fieldTail counterWidth : Nat) :
    ((terminationRoutePrefixGates fieldTail counterWidth).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 3 := by
  simp [terminationRoutePrefixGates, terminationRoutePrefixActivePathGate,
    terminationRoutePrefixControlActiveGate,
    terminationRoutePrefixControlPathGate,
    activeVZeroGates_cnotMultiplicity_sum]

/-- The route prefix retains the detector's Toffoli coordinate. -/
theorem terminationRoutePrefixGates_toffoliMultiplicity_sum
    (fieldTail counterWidth : Nat) :
    ((terminationRoutePrefixGates fieldTail counterWidth).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 * fieldTail + 1 := by
  simp [terminationRoutePrefixGates, terminationRoutePrefixActivePathGate,
    terminationRoutePrefixControlActiveGate,
    terminationRoutePrefixControlPathGate,
    activeVZeroGates_toffoliMultiplicity_sum]

/-- Exact primitive-gate length of the compact termination-route prefix. -/
theorem terminationRoutePrefixGates_length (fieldTail counterWidth : Nat) :
    (terminationRoutePrefixGates fieldTail counterWidth).length =
      4 * fieldTail + 10 := by
  rw [EncodedBit.GateSpec.length_eq_multiplicity_sums,
    terminationRoutePrefixGates_xMultiplicity_sum,
    terminationRoutePrefixGates_cnotMultiplicity_sum,
    terminationRoutePrefixGates_toffoliMultiplicity_sum]
  omega

/-- The compiled route prefix retains its exact X count. -/
theorem terminationRoutePrefixProgram_x_count (fieldTail counterWidth : Nat) :
    ResourcePool.count (.gate (.builtin "x"))
        (terminationRoutePrefixProgram fieldTail counterWidth).eventCost =
      2 * fieldTail + 6 := by
  rw [terminationRoutePrefixProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum,
    terminationRoutePrefixGates_xMultiplicity_sum]

/-- The compiled route prefix has the detector CNOT count plus three route
leaves. -/
theorem terminationRoutePrefixProgram_cnot_count (fieldTail counterWidth : Nat) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (terminationRoutePrefixProgram fieldTail counterWidth).eventCost = 3 := by
  rw [terminationRoutePrefixProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    terminationRoutePrefixGates_cnotMultiplicity_sum]

/-- The compiled route prefix retains its exact Toffoli count. -/
theorem terminationRoutePrefixProgram_toffoli_count
    (fieldTail counterWidth : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (terminationRoutePrefixProgram fieldTail counterWidth).eventCost =
      2 * fieldTail + 1 := by
  rw [terminationRoutePrefixProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    terminationRoutePrefixGates_toffoliMultiplicity_sum]

/-- The encoded shared-path flip is the corresponding named-workspace update. -/
theorem terminationRoutePrefixPathBit_flip_eq_update
    (fieldTail counterWidth : Nat) (x : Registers fieldTail.succ counterWidth) :
    (pathBit fieldTail.succ counterWidth).flip x =
      { x with shared := { x.shared with path := !x.shared.path } } := by
  rfl

/-- The encoded active-bit flip is the corresponding named-core update. -/
theorem terminationRoutePrefixActiveBit_flip_eq_update
    (fieldTail counterWidth : Nat) (x : Registers fieldTail.succ counterWidth) :
    (activeVZeroActiveBit fieldTail counterWidth).flip x =
      { x with core := { x.core with active := !x.core.active } } := by
  rfl

/-- On a clean path bit, the opening CNOT stores the original active flag. -/
theorem terminationRoutePrefixActivePathStep_clean
    (fieldTail counterWidth : Nat) (x : Registers fieldTail.succ counterWidth)
    (hpath : x.shared.path = false) :
    (terminationRoutePrefixActivePathGate fieldTail counterWidth).step x =
      { x with shared := { x.shared with path := x.core.active } } := by
  change EncodedBit.cnotStep (activeVZeroActiveBit fieldTail counterWidth)
      (pathBit fieldTail.succ counterWidth) x = _
  rw [EncodedBit.cnotStep]
  change (if x.core.active then (pathBit fieldTail.succ counterWidth).flip x else x) = _
  cases hactive : x.core.active
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases x with
    | mk core shared target =>
      cases shared with
      | mk coefficientAdder correctionCounter path control =>
        simp_all
  · simp only [↓reduceIte]
    rw [terminationRoutePrefixPathBit_flip_eq_update, hpath]
    rfl

/-- Expose the literal latch--detector--two-CNOT decomposition of the folded
route-prefix step. -/
theorem terminationRoutePrefixStep_decompose
    (fieldTail counterWidth : Nat) (x : Registers fieldTail.succ counterWidth) :
    terminationRoutePrefixStep fieldTail counterWidth x =
      (terminationRoutePrefixControlPathGate fieldTail counterWidth).step
        ((terminationRoutePrefixControlActiveGate fieldTail counterWidth).step
          (activeVZeroStep fieldTail counterWidth
            ((terminationRoutePrefixActivePathGate fieldTail counterWidth).step x))) := by
  rw [terminationRoutePrefixStep, terminationRoutePrefixGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rfl

/-- On clean shared path/control work, the route prefix has one explicit
record endpoint.  Every field not named by this update is preserved by
definition, including the VBE bank, correction counter, target, and all core
fields other than `active`. -/
theorem terminationRoutePrefixStep_cleanEndpoint
    (fieldTail counterWidth : Nat) (x : Registers fieldTail.succ counterWidth)
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork fieldTail.succ)
    (hpath : x.shared.path = false) (hcontrol : x.shared.control = false) :
    terminationRoutePrefixStep fieldTail counterWidth x =
      { x with
        core := { x.core with
          active := x.core.active && !decide (x.core.v = 0) }
        shared := { x.shared with
          path := x.core.active && !decide (x.core.v = 0)
          control := x.core.active && decide (x.core.v = 0) } } := by
  rw [terminationRoutePrefixStep_decompose,
    terminationRoutePrefixActivePathStep_clean fieldTail counterWidth x hpath]
  have hcoeffLatched :
      ({ x with shared := { x.shared with path := x.core.active } }).shared.coefficientAdder =
        cleanCoeffAdderWork fieldTail.succ := by
    exact hcoeff
  rw [activeVZeroStep_eq_controlConditional fieldTail counterWidth
    { x with shared := { x.shared with path := x.core.active } } hcoeffLatched]
  cases hactive : x.core.active <;>
    cases hzero : decide (x.core.v = 0) <;>
    simp only [Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
  all_goals
    simp only [terminationRoutePrefixControlPathGate,
      terminationRoutePrefixControlActiveGate, EncodedBit.GateSpec.step]
    unfold EncodedBit.cnotStep
    simp_all [terminationRoutePrefixActiveBit_flip_eq_update,
      activeVZeroControlBit_flip_eq_update,
      terminationRoutePrefixPathBit_flip_eq_update]
  all_goals
    cases hcore : x.core
    cases hshared : x.shared
    simp_all

/-- Explicit clean-boundary frame for the compact termination route.  In
particular, the VBE coefficient-adder bank, correction counter, target, and
every non-active core field are preserved. -/
theorem terminationRoutePrefixStep_cleanFrame
    (fieldTail counterWidth : Nat) (x : Registers fieldTail.succ counterWidth)
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork fieldTail.succ)
    (hpath : x.shared.path = false) (hcontrol : x.shared.control = false) :
    (terminationRoutePrefixStep fieldTail counterWidth x).core.u = x.core.u ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).core.v = x.core.v ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).core.compare =
        x.core.compare ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).core.sCoeff =
        x.core.sCoeff ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).core.rCoeff =
        x.core.rCoeff ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).core.scratchA =
        x.core.scratchA ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).core.scratchB =
        x.core.scratchB ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).core.history =
        x.core.history ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).core.active =
        (x.core.active && !decide (x.core.v = 0)) ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).core.counter =
        x.core.counter ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).shared.coefficientAdder =
        x.shared.coefficientAdder ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).shared.correctionCounter =
        x.shared.correctionCounter ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).shared.path =
        (x.core.active && !decide (x.core.v = 0)) ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).shared.control =
        (x.core.active && decide (x.core.v = 0)) ∧
      (terminationRoutePrefixStep fieldTail counterWidth x).target = x.target := by
  rw [terminationRoutePrefixStep_cleanEndpoint fieldTail counterWidth x
    hcoeff hpath hcontrol]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl⟩

/-! ## Compact padding-counter-one detector -/

/-- The fixed-width literal one used to turn a counter-equals-one test into a
zero test. -/
private def positiveCounterOneConstant (tail : Nat) : Fin (2 ^ (tail + 2)) :=
  ⟨1, by
    exact Nat.one_lt_two_pow (by omega)⟩

@[simp] private theorem positiveCounterOneConstant_val (tail : Nat) :
    (positiveCounterOneConstant tail).val = 1 :=
  rfl

/-- The positive-width detector's width-`tail + 2` counter word. -/
private def positiveCounterOneWord (n tail : Nat) :
    EncodedBit.Word (encoding n (tail + 2)) (tail + 2) :=
  paddingCounterValueWord n tail.succ

/-- The first `tail` bits of the sole VBE coefficient carry bank.  The
explicit `htail` proof is the only fit condition for the borrowed prefix. -/
private def positiveCounterOneWorkBit (n tail : Nat) (htail : tail ≤ n)
    (bit : Fin tail) : EncodedBit (encoding n (tail + 2)) :=
  coefficientCarryWorkBit n (tail + 2) (Fin.castLE htail bit)

/-- The uniquely selected VBE carry-bank prefix used by the counter detector. -/
private def positiveCounterOneWorkWord (n tail : Nat) (htail : tail ≤ n) :
    EncodedBit.Word (encoding n (tail + 2)) tail where
  bit := positiveCounterOneWorkBit n tail htail

private theorem positiveCounterOneWord_bit_wire_ne
    (n tail : Nat) {left right : Fin (tail + 2)} (hne : left ≠ right) :
    ((positiveCounterOneWord n tail).bit left).wire ≠
      ((positiveCounterOneWord n tail).bit right).wire := by
  simpa [positiveCounterOneWord, paddingCounterValueWord] using
    paddingCounterValueBit_wire_ne n tail.succ hne

private theorem positiveCounterOneWord_controlBit_wire_ne
    (n tail : Nat) (bit : Fin (tail + 2)) :
    ((positiveCounterOneWord n tail).bit bit).wire ≠
      (controlBit n (tail + 2)).wire := by
  simpa [positiveCounterOneWord, paddingCounterValueWord] using
    (controlBit_paddingCounterValueBit_wire_ne n tail.succ bit).symm

private theorem positiveCounterOneWord_workBit_wire_ne
    (n tail : Nat) (htail : tail ≤ n) (source : Fin (tail + 2))
    (work : Fin tail) :
    ((positiveCounterOneWord n tail).bit source).wire ≠
      (positiveCounterOneWorkBit n tail htail work).wire := by
  simpa [positiveCounterOneWord, paddingCounterValueWord,
    paddingCounterValueBit, positiveCounterOneWorkBit, coefficientCarryWorkBit] using
    liftCoreBit_liftSharedBit_wire_ne n (tail + 2)
      (RegisterBits.counterBit n (tail + 2)
        (WireAddress.littleEndianWire source))
      (sharedCoefficientCarryWorkBit n (tail + 2) (Fin.castLE htail work))

private theorem positiveCounterOneWorkBit_wire_ne
    (n tail : Nat) (htail : tail ≤ n) {left right : Fin tail} (hne : left ≠ right) :
    (positiveCounterOneWorkBit n tail htail left).wire ≠
      (positiveCounterOneWorkBit n tail htail right).wire := by
  apply coefficientCarryWorkBit_wire_ne n (tail + 2)
  intro hcast
  apply hne
  exact (Fin.castLE_injective htail) hcast

private theorem positiveCounterOneWorkBit_controlBit_wire_ne
    (n tail : Nat) (htail : tail ≤ n) (work : Fin tail) :
    (positiveCounterOneWorkBit n tail htail work).wire ≠
      (controlBit n (tail + 2)).wire := by
  exact (controlBit_coefficientCarryWorkBit_wire_ne n (tail + 2)
    (Fin.castLE htail work)).symm

/-- Clean zero-test layout after xoring the literal one into the counter. -/
private def positiveCounterOneLayout (n tail : Nat) (htail : tail ≤ n) :
    EncodedBit.Word.ZeroTestLayout
      (encoding := encoding n (tail + 2)) tail where
  source := positiveCounterOneWord n tail
  output := controlBit n (tail + 2)
  work := positiveCounterOneWorkWord n tail htail
  source_source_ne := by
    intro i j hij
    exact positiveCounterOneWord_bit_wire_ne n tail hij
  source_output_ne := by
    intro i
    exact positiveCounterOneWord_controlBit_wire_ne n tail i
  source_work_ne := by
    intro i j
    exact positiveCounterOneWord_workBit_wire_ne n tail htail i j
  work_work_ne := by
    intro i j hij
    exact positiveCounterOneWorkBit_wire_ne n tail htail hij
  work_output_ne := by
    intro j
    exact positiveCounterOneWorkBit_controlBit_wire_ne n tail htail j

/-- The literal-one load, clean zero test, and reverse unload schedule.
`tail` is the detector tail, so the counter width is `tail + 2`. -/
def counterOneGates (n tail : Nat) (htail : tail ≤ n) :
    List (EncodedBit.GateSpec (encoding n (tail + 2))) :=
  EncodedBit.Word.xorConstantGates (positiveCounterOneWord n tail)
      (positiveCounterOneConstant tail) ++
    (positiveCounterOneLayout n tail htail).gates ++
    EncodedBit.Word.xorConstantUnloadGates (positiveCounterOneWord n tail)
      (positiveCounterOneConstant tail)

/-- The compact counter-one detector never reads or writes a public target
bit. -/
theorem counterOneGates_bitDisjoint_target
    (n tail : Nat) (htail : tail ≤ n) (target : Fin n) :
    ∀ gate, gate ∈ counterOneGates n tail htail →
      EncodedBit.GateSpec.bitDisjoint (targetValueBit n (tail + 2) target) gate := by
  intro gate hgate
  rw [counterOneGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | hunload
  · rcases List.mem_append.mp hprefix with hload | htest
    · rw [EncodedBit.Word.xorConstantGates] at hload
      rcases List.mem_map.mp hload with ⟨bit, _hbit, rfl⟩
      exact paddingCounterValueBit_targetValueBit_wire_ne n tail.succ bit target
    · exact EncodedBit.Word.ZeroTestLayout.gates_bitDisjoint
        (positiveCounterOneLayout n tail htail)
        (targetValueBit n (tail + 2) target)
        (fun source => by
          change ((positiveCounterOneWord n tail).bit source).wire ≠
            (targetValueBit n (tail + 2) target).wire
          simpa [positiveCounterOneWord, paddingCounterValueWord,
            paddingCounterValueBit] using
            liftCoreBit_targetValueBit_wire_ne n (tail + 2)
              (RegisterBits.counterBit n (tail + 2)
                (WireAddress.littleEndianWire source)) target)
        (controlBit_targetValueBit_wire_ne n (tail + 2) target)
        (fun work => by
          change (positiveCounterOneWorkBit n tail htail work).wire ≠
            (targetValueBit n (tail + 2) target).wire
          simpa [positiveCounterOneWorkBit, coefficientCarryWorkBit] using
            liftSharedBit_targetValueBit_wire_ne n (tail + 2)
              (sharedCoefficientCarryWorkBit n (tail + 2)
                (Fin.castLE htail work))
              target)
        gate htest
  · have hforward : gate ∈ EncodedBit.Word.xorConstantGates
      (positiveCounterOneWord n tail) (positiveCounterOneConstant tail) := by
      exact List.mem_reverse.mp (by
        simpa [EncodedBit.Word.xorConstantUnloadGates] using hunload)
    rw [EncodedBit.Word.xorConstantGates] at hforward
    rcases List.mem_map.mp hforward with ⟨bit, _hbit, rfl⟩
    exact paddingCounterValueBit_targetValueBit_wire_ne n tail.succ bit target

/-- Physical circuit for the compact padding-counter-one detector. -/
def counterOneProgram (n tail : Nat) (htail : tail ≤ n) :
    UnitaryCircuit (Qubits (encoding n (tail + 2)).width) :=
  EncodedBit.GateSpec.programList (counterOneGates n tail htail)

/-- Folded semantic action of the compact padding-counter-one detector. -/
def counterOneStep (n tail : Nat) (htail : tail ≤ n) :
    Registers n (tail + 2) → Registers n (tail + 2) :=
  EncodedBit.GateSpec.stepList (counterOneGates n tail htail)

/-- The compiled detector realizes exactly its literal gate-list step. -/
theorem counterOne_realizes (n tail : Nat) (htail : tail ≤ n) :
    UnitaryCircuit.Realizes (encoding n (tail + 2))
      (counterOneProgram n tail htail) (counterOneStep n tail htail) :=
  EncodedBit.GateSpec.realizesList (counterOneGates n tail htail)

private theorem positiveCounterOneConstant_oneIndices_length (tail : Nat) :
    (EncodedBit.Word.constantOneIndices (positiveCounterOneConstant tail)).length = 1 := by
  suffices h : Nat.testBit 1 1 = false ∧
      ∀ bit : Fin tail, Nat.testBit 1 (bit.val + 1 + 1) = false by
    simpa [EncodedBit.Word.constantOneIndices, positiveCounterOneConstant] using h
  constructor
  · exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
  · intro bit
    exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))

/-- Exact X coordinate: the literal-one load/unload and the clean zero test. -/
theorem counterOneGates_xMultiplicity_sum (n tail : Nat) (htail : tail ≤ n) :
    ((counterOneGates n tail htail).map
      EncodedBit.GateSpec.xMultiplicity).sum = 2 * tail + 6 := by
  simp [counterOneGates, EncodedBit.Word.xorConstantGates_xMultiplicity_sum,
    EncodedBit.Word.xorConstantUnloadGates,
    EncodedBit.Word.ZeroTestLayout.gates_xMultiplicity_sum,
    positiveCounterOneConstant_oneIndices_length]
  omega

/-- The counter-one detector contains no CNOT leaves. -/
theorem counterOneGates_cnotMultiplicity_sum (n tail : Nat) (htail : tail ≤ n) :
    ((counterOneGates n tail htail).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 0 := by
  simp [counterOneGates, EncodedBit.Word.xorConstantGates_cnotMultiplicity_sum,
    EncodedBit.Word.xorConstantUnloadGates,
    EncodedBit.Word.ZeroTestLayout.gates_cnotMultiplicity_sum]

/-- Exact Toffoli coordinate inherited from the clean zero test. -/
theorem counterOneGates_toffoliMultiplicity_sum (n tail : Nat) (htail : tail ≤ n) :
    ((counterOneGates n tail htail).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 * tail + 1 := by
  simp [counterOneGates, EncodedBit.Word.xorConstantGates_toffoliMultiplicity_sum,
    EncodedBit.Word.xorConstantUnloadGates,
    EncodedBit.Word.ZeroTestLayout.gates_toffoliMultiplicity_sum]

/-- Exact primitive-gate length of the compact counter-one detector. -/
theorem counterOneGates_length (n tail : Nat) (htail : tail ≤ n) :
    (counterOneGates n tail htail).length = 4 * tail + 7 := by
  rw [EncodedBit.GateSpec.length_eq_multiplicity_sums,
    counterOneGates_xMultiplicity_sum,
    counterOneGates_cnotMultiplicity_sum,
    counterOneGates_toffoliMultiplicity_sum]
  omega

/-- Xoring the literal one into the counter makes the tested word all zero
exactly when the original compact counter is one. -/
private theorem positiveCounterOneWord_all_false_after_load_iff
    (n tail : Nat) (x : Registers n (tail + 2)) :
    (∀ bit, ((positiveCounterOneWord n tail).bit bit).get
      (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
        (positiveCounterOneConstant tail) x) = false) ↔
      x.core.counter = 1 := by
  constructor
  · intro h
    apply word_eq_of_testBit_eq
    intro bit
    have hloaded := EncodedBit.Word.xorConstantStep_get_target
      (positiveCounterOneWord n tail) (positiveCounterOneConstant tail) bit
      (fun other hne => positiveCounterOneWord_bit_wire_ne n tail hne) x
    have hbit := h bit
    rw [hloaded] at hbit
    have hsource : ((positiveCounterOneWord n tail).bit bit).get x =
        x.core.counter.val.testBit bit.val := by
      exact paddingCounterValueBit_get n tail.succ bit x
    rw [hsource] at hbit
    have honeWord : (1 : Word (tail + 2)).val = 1 := by
      change 1 % 2 ^ (tail + 2) = 1
      exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
    change x.core.counter.val.testBit bit.val =
      (1 : Word (tail + 2)).val.testBit bit.val
    rw [honeWord]
    by_cases hzero : bit.val = 0
    · have hbit : bit = 0 := Fin.ext hzero
      subst bit
      simpa [positiveCounterOneConstant] using hbit
    · have hconstant :
          (positiveCounterOneConstant tail).val.testBit bit.val = false := by
        rw [positiveCounterOneConstant_val]
        exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hzero)
      rw [hconstant, Bool.xor_false] at hbit
      rw [hbit]
      exact (Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hzero)).symm
  · intro hcounter bit
    have hloaded := EncodedBit.Word.xorConstantStep_get_target
      (positiveCounterOneWord n tail) (positiveCounterOneConstant tail) bit
      (fun other hne => positiveCounterOneWord_bit_wire_ne n tail hne) x
    rw [hloaded]
    have hsource : ((positiveCounterOneWord n tail).bit bit).get x =
        x.core.counter.val.testBit bit.val := by
      exact paddingCounterValueBit_get n tail.succ bit x
    rw [hsource]
    have hvalue : x.core.counter.val = 1 := by
      have := congrArg Fin.val hcounter
      simpa using this
    rw [hvalue, positiveCounterOneConstant_val]
    exact Bool.xor_self _

/-- The literal-one load does not disturb the borrowed VBE carry prefix. -/
private theorem positiveCounterOneWorkBit_get_after_load_of_coefficientAdder_clean
    (n tail : Nat) (htail : tail ≤ n) (x : Registers n (tail + 2))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n)
    (bit : Fin tail) :
    (positiveCounterOneWorkBit n tail htail bit).get
      (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
        (positiveCounterOneConstant tail) x) = false := by
  rw [EncodedBit.Word.xorConstantStep_get_observed_of_target_ne
    (positiveCounterOneWord n tail) (positiveCounterOneConstant tail)
      (positiveCounterOneWorkBit n tail htail bit)]
  · change (BinaryLabelEncoding.finIdentityBit n (Fin.castLE htail bit)).get
      x.shared.coefficientAdder.2 = false
    rw [hcoeff]
    exact PlainAdder.Schedule.PowerOfTwo.finIdentityBit_get_zero n
      (Fin.castLE htail bit)
  · intro source
    exact positiveCounterOneWord_workBit_wire_ne n tail htail source bit

/-- The zero-test final control after loading one is precisely the
counter-equals-one predicate. -/
private theorem positiveCounterOneFinalControl_eq_predicate
    (n tail : Nat) (htail : tail ≤ n) (x : Registers n (tail + 2))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n) :
    EncodedBit.Word.ZeroTestLayout.finalControl
      (positiveCounterOneLayout n tail htail)
      (EncodedBit.GateSpec.stepList
        ((positiveCounterOneLayout n tail htail).computeGates)
        (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
          (positiveCounterOneConstant tail) x)) =
      decide (x.core.counter = 1) := by
  have hclean : ∀ work,
      (positiveCounterOneWorkBit n tail htail work).get
        (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
          (positiveCounterOneConstant tail) x) = false := by
    intro work
    exact positiveCounterOneWorkBit_get_after_load_of_coefficientAdder_clean
      n tail htail x hcoeff work
  have hindicator :
      EncodedBit.Word.ZeroTestLayout.finalControl
        (positiveCounterOneLayout n tail htail)
        (EncodedBit.GateSpec.stepList
          ((positiveCounterOneLayout n tail htail).computeGates)
          (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
            (positiveCounterOneConstant tail) x)) =
        decide (∀ source, ((positiveCounterOneWord n tail).bit source).get
          (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
            (positiveCounterOneConstant tail) x) = false) := by
    by_cases hzero : ∀ source, ((positiveCounterOneWord n tail).bit source).get
        (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
          (positiveCounterOneConstant tail) x) = false
    · rw [(EncodedBit.Word.ZeroTestLayout.finalControl_compute_eq_true_iff
        (positiveCounterOneLayout n tail htail)
        (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
          (positiveCounterOneConstant tail) x) hclean).mpr hzero]
      simp [hzero]
    · have hnotTrue :
          EncodedBit.Word.ZeroTestLayout.finalControl
            (positiveCounterOneLayout n tail htail)
            (EncodedBit.GateSpec.stepList
              ((positiveCounterOneLayout n tail htail).computeGates)
              (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
                (positiveCounterOneConstant tail) x)) ≠ true := by
        intro htrue
        exact hzero
          ((EncodedBit.Word.ZeroTestLayout.finalControl_compute_eq_true_iff
            (positiveCounterOneLayout n tail htail)
            (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
              (positiveCounterOneConstant tail) x) hclean).mp htrue)
      rw [Bool.eq_false_of_not_eq_true hnotTrue]
      simp [hzero]
  rw [hindicator]
  exact Bool.eq_iff_iff.mpr
    (by
      simpa only [decide_eq_true_eq] using
        positiveCounterOneWord_all_false_after_load_iff n tail x)

/-- Expose the literal-one-load, zero-test, literal-one-unload decomposition. -/
private theorem counterOneStep_decompose
    (n tail : Nat) (htail : tail ≤ n) (x : Registers n (tail + 2)) :
    counterOneStep n tail htail x =
      EncodedBit.Word.xorConstantUnloadStep (positiveCounterOneWord n tail)
        (positiveCounterOneConstant tail)
        ((positiveCounterOneLayout n tail htail).step
          (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
            (positiveCounterOneConstant tail) x)) := by
  rw [counterOneStep, counterOneGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rfl

private theorem positiveCounterOneUnload_control_flip_comm
    (n tail : Nat) (x : Registers n (tail + 2)) :
    EncodedBit.Word.xorConstantUnloadStep (positiveCounterOneWord n tail)
      (positiveCounterOneConstant tail) ((controlBit n (tail + 2)).flip x) =
      (controlBit n (tail + 2)).flip
        (EncodedBit.Word.xorConstantUnloadStep (positiveCounterOneWord n tail)
          (positiveCounterOneConstant tail) x) := by
  unfold EncodedBit.Word.xorConstantUnloadStep
  apply EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint
  intro gate hgate
  have hforward : gate ∈ EncodedBit.Word.xorConstantGates
      (positiveCounterOneWord n tail) (positiveCounterOneConstant tail) := by
    exact List.mem_reverse.mp (by
      simpa [EncodedBit.Word.xorConstantUnloadGates] using hgate)
  rw [EncodedBit.Word.xorConstantGates] at hforward
  rcases List.mem_map.mp hforward with ⟨bit, _hbit, rfl⟩
  change ((positiveCounterOneWord n tail).bit bit).wire ≠
    (controlBit n (tail + 2)).wire
  exact positiveCounterOneWord_controlBit_wire_ne n tail bit

/-- Full-state clean endpoint: the compact detector restores the counter and
the entire borrowed carry prefix, and xors only the counter-equals-one
predicate into the shared control bit. -/
theorem counterOneStep_eq_controlConditional
    (n tail : Nat) (htail : tail ≤ n) (x : Registers n (tail + 2))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork n) :
    counterOneStep n tail htail x =
      if decide (x.core.counter = 1) then
        (controlBit n (tail + 2)).flip x
      else x := by
  rw [counterOneStep_decompose,
    EncodedBit.Word.ZeroTestLayout.step_eq_outputConditional,
    positiveCounterOneFinalControl_eq_predicate n tail htail x hcoeff]
  by_cases hp : decide (x.core.counter = 1) = true
  · rw [if_pos hp, if_pos hp]
    change EncodedBit.Word.xorConstantUnloadStep (positiveCounterOneWord n tail)
      (positiveCounterOneConstant tail)
      ((controlBit n (tail + 2)).flip
        (EncodedBit.Word.xorConstantStep (positiveCounterOneWord n tail)
          (positiveCounterOneConstant tail) x)) =
        (controlBit n (tail + 2)).flip x
    rw [positiveCounterOneUnload_control_flip_comm,
      EncodedBit.Word.xorConstantUnloadStep_after_xorConstantStep]
  · rw [if_neg hp, if_neg hp,
      EncodedBit.Word.xorConstantUnloadStep_after_xorConstantStep]

/-! ### Compact positive-counter termination handoff -/

/-- The complete compact handoff after a terminating round: route the active
flag, advance the inactive padding counter, then clear the transient control
exactly at counter value one. -/
def terminationHandoffGates (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ) :
    List (EncodedBit.GateSpec (encoding fieldTail.succ (counterTail + 2))) :=
  terminationRoutePrefixGates fieldTail (counterTail + 2) ++
    inactiveCounterIncrementGates fieldTail.succ counterTail.succ hfit ++
      counterOneGates fieldTail.succ counterTail
        (Nat.le_trans (Nat.le_succ counterTail) hfit)

/-- The complete compact termination handoff never reads or writes a public
target bit. -/
theorem terminationHandoffGates_bitDisjoint_target
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ)
    (target : Fin fieldTail.succ) :
    ∀ gate, gate ∈ terminationHandoffGates fieldTail counterTail hfit →
      EncodedBit.GateSpec.bitDisjoint
        (targetValueBit fieldTail.succ (counterTail + 2) target) gate := by
  intro gate hgate
  rw [terminationHandoffGates] at hgate
  rcases List.mem_append.mp hgate with hprefix | hcounterOne
  · rcases List.mem_append.mp hprefix with hroute | hincrement
    · exact terminationRoutePrefixGates_bitDisjoint_target
        fieldTail (counterTail + 2) target gate hroute
    · exact inactiveCounterIncrementGates_bitDisjoint_target
        fieldTail.succ counterTail.succ hfit target gate hincrement
  · exact counterOneGates_bitDisjoint_target fieldTail.succ counterTail
      (Nat.le_trans (Nat.le_succ counterTail) hfit) target gate hcounterOne

/-- Physical program for the compact positive-counter termination handoff. -/
def terminationHandoffProgram (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ) :
    UnitaryCircuit (Qubits (encoding fieldTail.succ (counterTail + 2)).width) :=
  EncodedBit.GateSpec.programList
    (terminationHandoffGates fieldTail counterTail hfit)

/-- Folded state action of the compact positive-counter termination handoff. -/
def terminationHandoffStep (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ) :
    Registers fieldTail.succ (counterTail + 2) →
      Registers fieldTail.succ (counterTail + 2) :=
  EncodedBit.GateSpec.stepList
    (terminationHandoffGates fieldTail counterTail hfit)

/-- The physical handoff program realizes its literal gate-list action. -/
theorem terminationHandoff_realizes (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ) :
    UnitaryCircuit.Realizes (encoding fieldTail.succ (counterTail + 2))
      (terminationHandoffProgram fieldTail counterTail hfit)
      (terminationHandoffStep fieldTail counterTail hfit) :=
  EncodedBit.GateSpec.realizesList
    (terminationHandoffGates fieldTail counterTail hfit)

/-- Reverse gate order for exact reversible handoff cleanup. -/
def terminationHandoffReverseGates (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ) :
    List (EncodedBit.GateSpec (encoding fieldTail.succ (counterTail + 2))) :=
  (terminationHandoffGates fieldTail counterTail hfit).reverse

/-- Physical reverse program for the compact termination handoff. -/
def terminationHandoffReverseProgram (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ) :
    UnitaryCircuit (Qubits (encoding fieldTail.succ (counterTail + 2)).width) :=
  EncodedBit.GateSpec.programList
    (terminationHandoffReverseGates fieldTail counterTail hfit)

/-- Folded inverse action of the compact termination handoff. -/
def terminationHandoffReverseStep (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ) :
    Registers fieldTail.succ (counterTail + 2) →
      Registers fieldTail.succ (counterTail + 2) :=
  EncodedBit.GateSpec.stepList
    (terminationHandoffReverseGates fieldTail counterTail hfit)

/-- The reverse physical program realizes its literal reverse gate action. -/
theorem terminationHandoffReverse_realizes (fieldTail counterTail : Nat)
    (hfit : counterTail.succ ≤ fieldTail.succ) :
    UnitaryCircuit.Realizes (encoding fieldTail.succ (counterTail + 2))
      (terminationHandoffReverseProgram fieldTail counterTail hfit)
      (terminationHandoffReverseStep fieldTail counterTail hfit) :=
  EncodedBit.GateSpec.realizesList
    (terminationHandoffReverseGates fieldTail counterTail hfit)

/-- Running the reverse handoff after the forward handoff restores every
register exactly. -/
theorem terminationHandoffReverseStep_after_terminationHandoffStep
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ)
    (x : Registers fieldTail.succ (counterTail + 2)) :
    terminationHandoffReverseStep fieldTail counterTail hfit
      (terminationHandoffStep fieldTail counterTail hfit x) = x := by
  exact EncodedBit.GateSpec.stepList_reverse_stepList
    (terminationHandoffGates fieldTail counterTail hfit) x

/-- The forward handoff also restores every state after its reverse action. -/
theorem terminationHandoffStep_after_terminationHandoffReverseStep
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ)
    (x : Registers fieldTail.succ (counterTail + 2)) :
    terminationHandoffStep fieldTail counterTail hfit
      (terminationHandoffReverseStep fieldTail counterTail hfit x) = x := by
  change EncodedBit.GateSpec.stepList
      (terminationHandoffGates fieldTail counterTail hfit)
      (EncodedBit.GateSpec.stepList
        (terminationHandoffGates fieldTail counterTail hfit).reverse x) = x
  simpa only [List.reverse_reverse] using
    (EncodedBit.GateSpec.stepList_reverse_stepList
      (terminationHandoffGates fieldTail counterTail hfit).reverse x)

/-- Exact X coordinate of the complete compact termination handoff. -/
theorem terminationHandoffGates_xMultiplicity_sum
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ) :
    ((terminationHandoffGates fieldTail counterTail hfit).map
      EncodedBit.GateSpec.xMultiplicity).sum =
      2 * fieldTail + 2 * counterTail + 14 := by
  simp only [terminationHandoffGates, List.map_append, List.sum_append,
    terminationRoutePrefixGates_xMultiplicity_sum,
    inactiveCounterIncrementGates_xMultiplicity_sum,
    counterOneGates_xMultiplicity_sum]
  omega

/-- Exact CNOT coordinate of the complete compact termination handoff. -/
theorem terminationHandoffGates_cnotMultiplicity_sum
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ) :
    ((terminationHandoffGates fieldTail counterTail hfit).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 2 * counterTail + 7 := by
  simp only [terminationHandoffGates, List.map_append, List.sum_append,
    terminationRoutePrefixGates_cnotMultiplicity_sum,
    inactiveCounterIncrementGates_cnotMultiplicity_sum,
    counterOneGates_cnotMultiplicity_sum]
  omega

/-- Exact Toffoli coordinate of the complete compact termination handoff. -/
theorem terminationHandoffGates_toffoliMultiplicity_sum
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ) :
    ((terminationHandoffGates fieldTail counterTail hfit).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * fieldTail + 8 * counterTail + 8 := by
  simp only [terminationHandoffGates, List.map_append, List.sum_append,
    terminationRoutePrefixGates_toffoliMultiplicity_sum,
    inactiveCounterIncrementGates_toffoliMultiplicity_sum,
    counterOneGates_toffoliMultiplicity_sum]
  omega

/-- Exact primitive-gate length of the complete compact termination handoff. -/
theorem terminationHandoffGates_length
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ) :
    (terminationHandoffGates fieldTail counterTail hfit).length =
      4 * fieldTail + 12 * counterTail + 29 := by
  rw [EncodedBit.GateSpec.length_eq_multiplicity_sums,
    terminationHandoffGates_xMultiplicity_sum,
    terminationHandoffGates_cnotMultiplicity_sum,
    terminationHandoffGates_toffoliMultiplicity_sum]
  omega

/-- The compiled handoff retains its exact X coordinate. -/
theorem terminationHandoffProgram_x_count
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (terminationHandoffProgram fieldTail counterTail hfit).eventCost =
      2 * fieldTail + 2 * counterTail + 14 := by
  rw [terminationHandoffProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum,
    terminationHandoffGates_xMultiplicity_sum]

/-- The compiled handoff retains its exact CNOT coordinate. -/
theorem terminationHandoffProgram_cnot_count
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (terminationHandoffProgram fieldTail counterTail hfit).eventCost =
      2 * counterTail + 7 := by
  rw [terminationHandoffProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum,
    terminationHandoffGates_cnotMultiplicity_sum]

/-- The compiled handoff retains its exact Toffoli coordinate. -/
theorem terminationHandoffProgram_toffoli_count
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (terminationHandoffProgram fieldTail counterTail hfit).eventCost =
      2 * fieldTail + 8 * counterTail + 8 := by
  rw [terminationHandoffProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum,
    terminationHandoffGates_toffoliMultiplicity_sum]

/-- Expose the route-prefix, inactive-increment, counter-one decomposition. -/
theorem terminationHandoffStep_decompose
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ)
    (x : Registers fieldTail.succ (counterTail + 2)) :
    terminationHandoffStep fieldTail counterTail hfit x =
      counterOneStep fieldTail.succ counterTail
        (Nat.le_trans (Nat.le_succ counterTail) hfit)
        (inactiveCounterIncrementStep fieldTail.succ counterTail.succ hfit
          (terminationRoutePrefixStep fieldTail (counterTail + 2) x)) := by
  rw [terminationHandoffStep, terminationHandoffGates,
    EncodedBit.GateSpec.stepList_append,
    EncodedBit.GateSpec.stepList_append]
  rfl

/-- At a clean compact endpoint, the handoff exposes its full record update.
The inactive counter addition is symbolic so its fixed-width interpretation is
preserved exactly. -/
theorem terminationHandoffStep_cleanEndpoint
    (fieldTail counterTail : Nat) (hfit : counterTail.succ ≤ fieldTail.succ)
    (x : Registers fieldTail.succ (counterTail + 2))
    (hcoeff : x.shared.coefficientAdder = cleanCoeffAdderWork fieldTail.succ)
    (hcorrection : x.shared.correctionCounter = 0)
    (hpath : x.shared.path = false) (hcontrol : x.shared.control = false)
    (hmode : x.core.active = decide (x.core.counter = 0))
    (hroom : x.core.counter.val + 1 < 2 ^ (counterTail + 2)) :
    terminationHandoffStep fieldTail counterTail hfit x =
      { x with
        core := { x.core with
          active := x.core.active && !decide (x.core.v = 0)
          counter := x.core.counter + inactiveCounterSourceValue counterTail.succ
            (x.core.active && !decide (x.core.v = 0)) }
        shared := { x.shared with
          path := x.core.active && !decide (x.core.v = 0)
          control := false } } := by
  rw [terminationHandoffStep_decompose,
    terminationRoutePrefixStep_cleanEndpoint fieldTail (counterTail + 2) x
      hcoeff hpath hcontrol]
  rw [inactiveCounterIncrementStep_cleanEndpoint fieldTail.succ counterTail.succ hfit
    _ (by simpa using hcoeff) (by simpa using hcorrection)]
  rw [counterOneStep_eq_controlConditional fieldTail.succ counterTail
    (Nat.le_trans (Nat.le_succ counterTail) hfit) _ (by simpa using hcoeff)]
  cases hactive : x.core.active <;> cases hzero : decide (x.core.v = 0)
  · have hcounter : x.core.counter ≠ 0 := by
      apply of_decide_eq_false
      simpa [hactive] using hmode.symm
    have hcounterVal : x.core.counter.val ≠ 0 := by
      intro hzeroVal
      apply hcounter
      apply Fin.ext
      simpa using hzeroVal
    have haddBound : x.core.counter.val +
        (1 : Word (counterTail + 2)).val < 2 ^ (counterTail + 2) := by
      simpa using hroom
    have hadd : (x.core.counter + (1 : Word (counterTail + 2))).val =
        x.core.counter.val + 1 := by
      simpa using Fin.val_add_eq_of_add_lt haddBound
    have hnotOne : x.core.counter + (1 : Word (counterTail + 2)) ≠ 1 := by
      intro hone
      have hval := congrArg Fin.val hone
      rw [hadd] at hval
      have : x.core.counter.val = 0 := by simpa using hval
      exact hcounterVal this
    simp [inactiveCounterSourceValue, hnotOne]
  · have hcounter : x.core.counter ≠ 0 := by
      apply of_decide_eq_false
      simpa [hactive] using hmode.symm
    have hcounterVal : x.core.counter.val ≠ 0 := by
      intro hzeroVal
      apply hcounter
      apply Fin.ext
      simpa using hzeroVal
    have haddBound : x.core.counter.val +
        (1 : Word (counterTail + 2)).val < 2 ^ (counterTail + 2) := by
      simpa using hroom
    have hadd : (x.core.counter + (1 : Word (counterTail + 2))).val =
        x.core.counter.val + 1 := by
      simpa using Fin.val_add_eq_of_add_lt haddBound
    have hnotOne : x.core.counter + (1 : Word (counterTail + 2)) ≠ 1 := by
      intro hone
      have hval := congrArg Fin.val hone
      rw [hadd] at hval
      have : x.core.counter.val = 0 := by simpa using hval
      exact hcounterVal this
    simp [inactiveCounterSourceValue, hnotOne]
  · have hcounter : x.core.counter = 0 := by
      apply of_decide_eq_true
      simpa [hactive] using hmode.symm
    simp [hcounter, inactiveCounterSourceValue]
  · have hcounter : x.core.counter = 0 := by
      apply of_decide_eq_true
      simpa [hactive] using hmode.symm
    simp [hcounter, inactiveCounterSourceValue,
      activeVZeroControlBit_flip_eq_update]

/-! ### Width-one boundary -/

/-- At counter width one, equality with one is a single CNOT into the shared
control bit and needs no borrowed carry workspace. -/
def counterOneWidthOneGates (n : Nat) :
    List (EncodedBit.GateSpec (encoding n 1)) :=
  [.cnot (paddingCounterValueBit n 0 0) (controlBit n 1)
    ((controlBit_paddingCounterValueBit_wire_ne n 0 0).symm)]

/-- Folded action of the workspace-free width-one counter detector. -/
def counterOneWidthOneStep (n : Nat) :
    Registers n 1 → Registers n 1 :=
  EncodedBit.GateSpec.stepList (counterOneWidthOneGates n)

/-- Physical circuit for the width-one boundary detector. -/
def counterOneWidthOneProgram (n : Nat) :
    UnitaryCircuit (Qubits (encoding n 1).width) :=
  EncodedBit.GateSpec.programList (counterOneWidthOneGates n)

theorem counterOneWidthOne_realizes (n : Nat) :
    UnitaryCircuit.Realizes (encoding n 1)
      (counterOneWidthOneProgram n) (counterOneWidthOneStep n) :=
  EncodedBit.GateSpec.realizesList (counterOneWidthOneGates n)

/-- The width-one boundary xors its sole counter bit directly into control. -/
theorem counterOneWidthOneStep_controlBit_get
    (n : Nat) (x : Registers n 1) :
    (controlBit n 1).get (counterOneWidthOneStep n x) =
      ((controlBit n 1).get x ^^
        (paddingCounterValueBit n 0 0).get x) := by
  change (controlBit n 1).get
      ((EncodedBit.GateSpec.cnot (paddingCounterValueBit n 0 0)
        (controlBit n 1)
        ((controlBit_paddingCounterValueBit_wire_ne n 0 0).symm)).step x) = _
  exact EncodedBit.cnotStep_get_target
    (paddingCounterValueBit n 0 0) (controlBit n 1) x

theorem counterOneWidthOneGates_xMultiplicity_sum (n : Nat) :
    ((counterOneWidthOneGates n).map
      EncodedBit.GateSpec.xMultiplicity).sum = 0 := by
  simp [counterOneWidthOneGates]

theorem counterOneWidthOneGates_cnotMultiplicity_sum (n : Nat) :
    ((counterOneWidthOneGates n).map
      EncodedBit.GateSpec.cnotMultiplicity).sum = 1 := by
  simp [counterOneWidthOneGates]

theorem counterOneWidthOneGates_toffoliMultiplicity_sum (n : Nat) :
    ((counterOneWidthOneGates n).map
      EncodedBit.GateSpec.toffoliMultiplicity).sum = 0 := by
  simp [counterOneWidthOneGates]

theorem counterOneWidthOneGates_length (n : Nat) :
    (counterOneWidthOneGates n).length = 1 := by
  rw [EncodedBit.GateSpec.length_eq_multiplicity_sums,
    counterOneWidthOneGates_xMultiplicity_sum,
    counterOneWidthOneGates_cnotMultiplicity_sum,
    counterOneWidthOneGates_toffoliMultiplicity_sum]

end

end Compact
end MK
end MAU.Inversion
end QuantumAlg

end
