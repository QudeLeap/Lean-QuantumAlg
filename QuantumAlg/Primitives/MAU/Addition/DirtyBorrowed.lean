/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
/-!
# Constant addition with dirty borrowed state

This module fixes the semantic contract for an in-place constant adder whose
borrowed register may start in an arbitrary state.  The borrowed register is
left abstract on purpose: it may include qubits entangled with an external
system.  Correctness is therefore stated for every joint amplitude, not only
for computational-basis inputs or a distinguished clean ancilla.

The contract follows the dirty-ancilla convention of [HRS16,
paper.tex:169-180,354]: borrowed qubits may be in an unknown, entangled state
and must be returned exactly.  Concrete implementations must inhabit
`CircuitRealization`; their semantics, event trace, cost, and depth then come
from one stored `UnitaryCircuit`.
-/

section

namespace QuantumAlg
namespace MAU.Addition.DirtyBorrowed

noncomputable section

/-- Register of one `n`-bit target word. -/
@[implicit_reducible]
def targetRegister (n : Nat) : Register where
  Index := PlainAdder.Word n
  fintype := inferInstance
  decEq := inferInstance

/-- Add a classical constant to an `n`-bit word. -/
def addConstant {n : Nat} (constant target : PlainAdder.Word n) :
    PlainAdder.Word n :=
  target + constant

/-- Subtract a classical constant from an `n`-bit word. -/
def subConstant {n : Nat} (constant target : PlainAdder.Word n) :
    PlainAdder.Word n :=
  target - constant

/-- Reversible in-place addition by one classical constant. -/
def addConstantEquiv (n : Nat) (constant : PlainAdder.Word n) :
    Equiv.Perm (PlainAdder.Word n) where
  toFun := addConstant constant
  invFun := subConstant constant
  left_inv := by
    intro target
    simp [addConstant, subConstant]
  right_inv := by
    intro target
    simp [addConstant, subConstant]

@[simp] theorem addConstantEquiv_apply {n : Nat}
    (constant target : PlainAdder.Word n) :
    addConstantEquiv n constant target = target + constant :=
  rfl

@[simp] theorem addConstantEquiv_symm_apply {n : Nat}
    (constant target : PlainAdder.Word n) :
    (addConstantEquiv n constant).symm target = target - constant :=
  rfl

/-- The target-only constant-adder operator. -/
def targetOp (n : Nat) (constant : PlainAdder.Word n) :
    UnitaryOperator (targetRegister n) :=
  UnitaryOperator.ofPerm (addConstantEquiv n constant).symm

/-- Basis action of the target-only constant adder. -/
@[simp] theorem targetOp_apply_ket (n : Nat)
    (constant target : PlainAdder.Word n) :
    (targetOp n constant).apply
        (NormalizedVector.ket (R := targetRegister n) target) =
      NormalizedVector.ket (R := targetRegister n) (target + constant) := by
  rw [targetOp, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-- Joint basis permutation: update the target and preserve the entire
borrowed label.  The abstract borrowed register may itself include an external
environment, so this definition does not assume a product input state. -/
def jointEquiv (n : Nat) (Borrowed : Register)
    (constant : PlainAdder.Word n) :
    Equiv.Perm ((Register.prod (targetRegister n) Borrowed).Index) :=
  Equiv.prodCongr (addConstantEquiv n constant) (Equiv.refl Borrowed.Index)

@[simp] theorem jointEquiv_apply (n : Nat) (Borrowed : Register)
    (constant target : PlainAdder.Word n) (borrowed : Borrowed.Index) :
    jointEquiv n Borrowed constant (target, borrowed) =
      (target + constant, borrowed) :=
  rfl

@[simp] theorem jointEquiv_symm_apply (n : Nat) (Borrowed : Register)
    (constant target : PlainAdder.Word n) (borrowed : Borrowed.Index) :
    (jointEquiv n Borrowed constant).symm (target, borrowed) =
      (target - constant, borrowed) :=
  rfl

/-- Exact constant-adder operator with identity action on an arbitrary
borrowed register. -/
def op (n : Nat) (Borrowed : Register)
    (constant : PlainAdder.Word n) :
    UnitaryOperator (Register.prod (targetRegister n) Borrowed) :=
  UnitaryOperator.ofPerm (jointEquiv n Borrowed constant).symm

/-- Exact basis action preserves every borrowed label. -/
@[simp] theorem op_apply_ket (n : Nat) (Borrowed : Register)
    (constant target : PlainAdder.Word n) (borrowed : Borrowed.Index) :
    (op n Borrowed constant).apply
        (NormalizedVector.ket
          (R := Register.prod (targetRegister n) Borrowed)
          (target, borrowed)) =
      NormalizedVector.ket
        (R := Register.prod (targetRegister n) Borrowed)
        (target + constant, borrowed) := by
  rw [op, UnitaryOperator.ofPerm_apply_ket]
  rfl

/-- Strong dirty-state restoration law.  For an arbitrary joint state, the
output amplitude at `(target, borrowed)` reads the input amplitude at
`(target - constant, borrowed)`.  In particular, no amplitude ever moves
between distinct borrowed labels.  Taking `Borrowed` to include an external
environment covers borrowed ancillas entangled with that environment. -/
theorem op_applyVec_arbitrary_joint_state (n : Nat) (Borrowed : Register)
    (constant : PlainAdder.Word n)
    (state : HilbertVector (Register.prod (targetRegister n) Borrowed))
    (target : PlainAdder.Word n) (borrowed : Borrowed.Index) :
    (op n Borrowed constant).applyVec state (target, borrowed) =
      state (target - constant, borrowed) := by
  rw [op, UnitaryOperator.ofPerm_applyVec]
  rfl

/-- One concrete circuit realization of dirty-borrowed constant addition.
The exact operator equality prevents an implementation from proving only a
clean-basis special case or attaching unrelated accounting metadata. -/
structure CircuitRealization (n : Nat) (Borrowed : Register)
    (constant : PlainAdder.Word n) where
  /-- Executable circuit owning semantics and all strict event metadata. -/
  circuit : UnitaryCircuit (Register.prod (targetRegister n) Borrowed)
  /-- The circuit is target addition tensor identity on the entire borrowed
  register. -/
  matrix_eq : circuit.matrix = op n Borrowed constant

namespace CircuitRealization

variable {n : Nat} {Borrowed : Register}
variable {constant : PlainAdder.Word n}

/-- Ordered strict events derived from the realized circuit. -/
def eventTrace (realization : CircuitRealization n Borrowed constant) :
    List (Resource.Event .quantum) :=
  realization.circuit.eventTrace

/-- Strict event pool derived from the realized circuit. -/
def eventCost (realization : CircuitRealization n Borrowed constant) :
    ResourcePool .quantum :=
  realization.circuit.eventCost

/-- Strict symbolic critical path derived from the realized circuit. -/
def eventDepth (realization : CircuitRealization n Borrowed constant) :
    DepthExpr (Resource.Event .quantum) :=
  realization.circuit.eventDepth

/-- Exact multiplicity of one native gate coordinate. -/
def eventGateCount (realization : CircuitRealization n Borrowed constant)
    (label : Resource.GateLabel) : Nat :=
  ResourcePool.count (.gate label) realization.circuit.eventCost

/-- Linearizing the circuit depth recovers the same strict event pool. -/
theorem resourcesFromEventDepth_eq_eventCost
    (realization : CircuitRealization n Borrowed constant) :
    realization.circuit.resourcesFromEventDepth =
      realization.circuit.eventCost :=
  UnitaryCircuit.resourcesFromEventDepth_eq_eventCost realization.circuit

/-- Realized basis action returns every borrowed basis label unchanged. -/
theorem applyNormalized_ket
    (realization : CircuitRealization n Borrowed constant)
    (target : PlainAdder.Word n) (borrowed : Borrowed.Index) :
    realization.circuit.applyNormalized
        (NormalizedVector.ket
          (R := Register.prod (targetRegister n) Borrowed)
          (target, borrowed)) =
      NormalizedVector.ket
        (R := Register.prod (targetRegister n) Borrowed)
        (target + constant, borrowed) := by
  change realization.circuit.matrix.apply _ = _
  rw [realization.matrix_eq]
  exact op_apply_ket n Borrowed constant target borrowed

/-- Realized strong restoration law for every joint state, including states
where the borrowed ancilla is entangled with an external subsystem included in
`Borrowed`. -/
theorem applyVec_arbitrary_joint_state
    (realization : CircuitRealization n Borrowed constant)
    (state : HilbertVector (Register.prod (targetRegister n) Borrowed))
    (target : PlainAdder.Word n) (borrowed : Borrowed.Index) :
    realization.circuit.applyVec state (target, borrowed) =
      state (target - constant, borrowed) := by
  change realization.circuit.matrix.applyVec state (target, borrowed) = _
  rw [realization.matrix_eq]
  exact op_applyVec_arbitrary_joint_state n Borrowed constant state target borrowed

end CircuitRealization

/-! ## Straightforward dirty-carry implementation -/

/-- The HRS straight-forward construction uses `n` borrowed dirty carry bits
for an `(n + 1)`-bit target.  It is the quadratic-size predecessor of the
paper's serial divide-and-conquer construction, not the later one-dirty-bit
variant [HRS16, paper.tex:190-241]. -/
abbrev StraightforwardDirty (n : Nat) : Type :=
  Fin (2 ^ n)

/-- The full binary encoding of an `(n + 1)`-bit target and its `n` dirty
carry bits. -/
def straightforwardEncoding (n : Nat) :
    BinaryLabelEncoding (PlainAdder.Word n.succ × StraightforwardDirty n) :=
  BinaryLabelEncoding.prod
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n.succ)
    (BinaryLabelEncoding.finIdentity n)

/-- The R.0 implementation uses exactly `n+1` target qubits and `n` borrowed
dirty qubits. -/
theorem straightforwardEncoding_width (n : Nat) :
    (straightforwardEncoding n).width = 2 * n + 1 := by
  simp [straightforwardEncoding,
    PlainAdder.Schedule.PowerOfTwo.wordEncoding,
    BinaryLabelEncoding.ofEquiv]
  omega

/-- Exact semantic-pair to flat-basis layout used by the straightforward
circuit. -/
def straightforwardLabelEquiv (n : Nat) :
    (PlainAdder.Word n.succ × StraightforwardDirty n) ≃
      Fin (2 ^ (straightforwardEncoding n).width) :=
  (Equiv.prodCongr
      (PlainAdder.Schedule.PowerOfTwo.wordLabelEquiv n.succ)
      (Equiv.refl (StraightforwardDirty n))).trans prodEquiv

@[simp] theorem straightforwardEncoding_encode (n : Nat)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    (straightforwardEncoding n).encode state =
      straightforwardLabelEquiv n state :=
  rfl

/-- Register-typed direction of the exact flat-label equivalence. -/
def straightforwardIndexEquiv (n : Nat) :
    (Qubits (straightforwardEncoding n).width).Index ≃
      (Register.prod (targetRegister n.succ) (Qubits n)).Index :=
  (straightforwardLabelEquiv n).symm

theorem straightforwardIndexEquiv_encode (n : Nat)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    straightforwardIndexEquiv n ((straightforwardEncoding n).encode state) =
      state := by
  change (straightforwardLabelEquiv n).symm
      (straightforwardLabelEquiv n state) = state
  exact Equiv.symm_apply_apply (straightforwardLabelEquiv n) state

/-- One little-endian target bit in the straight-forward HRS layout. -/
def straightforwardTargetBit (n : Nat) (bit : Fin n.succ) :
    EncodedBit (straightforwardEncoding n) :=
  BinaryLabelEncoding.prodLeftBit
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n.succ)
    (BinaryLabelEncoding.finIdentity n)
    (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ bit)

/-- One little-endian borrowed dirty carry bit in the straight-forward HRS
layout. -/
def straightforwardDirtyBit (n : Nat) (bit : Fin n) :
    EncodedBit (straightforwardEncoding n) :=
  BinaryLabelEncoding.prodRightBit
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n.succ)
    (BinaryLabelEncoding.finIdentity n)
    (BinaryLabelEncoding.finIdentityBit n (WireAddress.littleEndianWire bit))

@[simp] theorem straightforwardTargetBit_get (n : Nat) (bit : Fin n.succ)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    (straightforwardTargetBit n bit).get state =
      state.1.val.testBit bit.val := by
  simp [straightforwardTargetBit, BinaryLabelEncoding.prodLeftBit,
    PlainAdder.Schedule.PowerOfTwo.wordBit_get]

@[simp] theorem straightforwardDirtyBit_get (n : Nat) (bit : Fin n)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    (straightforwardDirtyBit n bit).get state =
      state.2.val.testBit bit.val := by
  simp [straightforwardDirtyBit, BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.finIdentityBit, BinaryLabelEncoding.ofEquivBit]

/-- Classical carry toggle produced in dirty bit `bit`.  This is the carry
entering target bit `bit + 1` in ordinary little-endian addition. -/
def straightforwardCarryToggle (n : Nat)
    (constant target : PlainAdder.Word n.succ) (bit : Fin n) : Bool :=
  Nat.BinaryArithmetic.natAddCarry target.val constant.val (bit.val + 1)

/-- A propagated carry through `count` low bits only observes input bits below
`count`. -/
theorem natAddCarry_congr_left_of_testBit_eq_lt
    (left first second count : Nat)
    (hbits : ∀ bit, bit < count → first.testBit bit = second.testBit bit) :
    Nat.BinaryArithmetic.natAddCarry first left count =
      Nat.BinaryArithmetic.natAddCarry second left count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [Nat.BinaryArithmetic.natAddCarry]
      rw [hbits count (Nat.lt_succ_self count)]
      rw [ih (fun bit hbit => hbits bit (hbit.trans (Nat.lt_succ_self count)))]

theorem straightforwardTargetBit_wire_ne
    (n : Nat) {left right : Fin n.succ} (hne : left ≠ right) :
    (straightforwardTargetBit n left).wire ≠
      (straightforwardTargetBit n right).wire := by
  apply EncodedBit.GateSpec.prodLeftWire_ne (BinaryLabelEncoding.finIdentity n)
  change WireAddress.littleEndianWire left ≠ WireAddress.littleEndianWire right
  intro hwire
  exact hne (WireAddress.bitIndex_injective hwire)

theorem straightforwardWordBit_wire_ne
    (width : Nat) {left right : Fin width} (hne : left ≠ right) :
    (PlainAdder.Schedule.PowerOfTwo.wordBit width left).wire ≠
      (PlainAdder.Schedule.PowerOfTwo.wordBit width right).wire := by
  change WireAddress.littleEndianWire left ≠
    WireAddress.littleEndianWire right
  intro hwire
  exact hne (WireAddress.bitIndex_injective hwire)

theorem straightforwardDirtyBit_wire_ne
    (n : Nat) {left right : Fin n} (hne : left ≠ right) :
    (straightforwardDirtyBit n left).wire ≠
      (straightforwardDirtyBit n right).wire := by
  apply EncodedBit.GateSpec.prodRightWire_ne
    (PlainAdder.Schedule.PowerOfTwo.wordEncoding n.succ)
  change WireAddress.littleEndianWire left ≠ WireAddress.littleEndianWire right
  intro hwire
  exact hne (WireAddress.bitIndex_injective hwire)

theorem straightforwardTargetBit_wire_ne_dirtyBit
    (n : Nat) (target : Fin n.succ) (dirty : Fin n) :
    (straightforwardTargetBit n target).wire ≠
      (straightforwardDirtyBit n dirty).wire := by
  intro hwire
  have hval := congrArg Fin.val hwire
  have hlt :
      (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ target).wire.val <
        (PlainAdder.Schedule.PowerOfTwo.wordEncoding n.succ).width :=
    (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ target).wire.isLt
  simp only [straightforwardTargetBit, straightforwardDirtyBit,
    BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodRightBit,
    BinaryLabelEncoding.prodLeftWire,
    BinaryLabelEncoding.prodRightWire] at hval
  omega

/-- HRS's carry-toggle subnetwork for the carry from bit `i` to `i + 1`.

The nested pair of Toffoli gates is placed around the lower carry subnetwork:
it therefore reacts to the *toggle* of the preceding dirty bit, rather than
reading that bit as though it were clean.  When this network is reversed, all
borrowed dirty bits are restored exactly [HRS16, paper.tex:202-241]. -/
def straightforwardCarryGates (n : Nat) (constant : PlainAdder.Word n.succ)
    (bit : Fin n) : List (EncodedBit.GateSpec (straightforwardEncoding n)) :=
  match bit with
  | ⟨0, hzero⟩ =>
      if constant.val.testBit 0 then
        [EncodedBit.GateSpec.cnot
          (straightforwardTargetBit n 0)
          (straightforwardDirtyBit n ⟨0, hzero⟩)
          (straightforwardTargetBit_wire_ne_dirtyBit n 0 ⟨0, hzero⟩)]
      else
        []
  | ⟨index + 1, hindex⟩ =>
      let current : Fin n := ⟨index + 1, hindex⟩
      let currentTarget : Fin n.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self n)⟩
      let previous : Fin n := ⟨index, by omega⟩
      let previous_ne_current : previous ≠ current := by
        apply Fin.ne_of_val_ne
        dsimp [previous, current]
        omega
      let target := straightforwardTargetBit n currentTarget
      let previousDirty := straightforwardDirtyBit n previous
      let currentDirty := straightforwardDirtyBit n current
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty target currentDirty
        (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget previous).symm
        (straightforwardDirtyBit_wire_ne n previous_ne_current)
        (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget current)
      (if constant.val.testBit current.val then
        [EncodedBit.GateSpec.cnot target currentDirty
            (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget current),
          EncodedBit.GateSpec.x target]
       else
        []) ++
        [toffoli] ++
        straightforwardCarryGates n constant ⟨index, by omega⟩ ++
        [toffoli] ++
        if constant.val.testBit current.val then
          [EncodedBit.GateSpec.x target]
        else
          []
termination_by bit.val
decreasing_by omega

/-- The carry-toggle network only borrows target bits as controls; every
temporary target flip is undone before the network returns. -/
@[simp] theorem straightforwardCarryGates_fst (n : Nat)
    (constant : PlainAdder.Word n.succ) (bit : Fin n)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    (EncodedBit.GateSpec.stepList
      (straightforwardCarryGates n constant bit) state).1 = state.1 := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · rw [show straightforwardCarryGates n constant ⟨0, hbit⟩ =
            [EncodedBit.GateSpec.cnot
              (straightforwardTargetBit n 0)
              (straightforwardDirtyBit n ⟨0, hbit⟩)
              (straightforwardTargetBit_wire_ne_dirtyBit n 0 ⟨0, hbit⟩)] by
            simp [straightforwardCarryGates, hc]]
        simp only [EncodedBit.GateSpec.stepList, id_eq]
        simp [EncodedBit.GateSpec.step, EncodedBit.cnotStep,
          straightforwardDirtyBit, BinaryLabelEncoding.prodRightBit]
        split <;> rfl
      · simp [straightforwardCarryGates, hc,
          EncodedBit.GateSpec.stepList]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin n := ⟨index + 1, hbit⟩
      let currentTarget : Fin n.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self n)⟩
      let previous : Fin n := ⟨index, by omega⟩
      let target := straightforwardTargetBit n currentTarget
      let previousDirty := straightforwardDirtyBit n previous
      let currentDirty := straightforwardDirtyBit n current
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty target currentDirty
        (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget previous).symm
        (straightforwardDirtyBit_wire_ne n (by
          apply Fin.ne_of_val_ne
          dsimp [previous, current]
          omega))
        (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget current)
      have toffoli_fst
          (input : PlainAdder.Word n.succ × StraightforwardDirty n) :
          (toffoli.step input).1 = input.1 := by
        simp [toffoli, EncodedBit.GateSpec.step,
          EncodedBit.toffoliStep, currentDirty, straightforwardDirtyBit,
          BinaryLabelEncoding.prodRightBit]
        split <;> rfl
      by_cases hc : constant.val.testBit current.val
      · let prefixCnot := EncodedBit.GateSpec.cnot target currentDirty
          (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget current)
        let afterCnot := prefixCnot.step state
        let afterX := (EncodedBit.GateSpec.x target).step afterCnot
        let afterFirstToffoli := toffoli.step afterX
        let afterCarry := EncodedBit.GateSpec.stepList
          (straightforwardCarryGates n constant previous) afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hcnotFst : afterCnot.1 = state.1 := by
          simp [afterCnot, prefixCnot, EncodedBit.GateSpec.step,
            EncodedBit.cnotStep, currentDirty, straightforwardDirtyBit,
            BinaryLabelEncoding.prodRightBit]
          split <;> rfl
        have hxFst : afterX.1 =
            (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ currentTarget).flip
              state.1 := by
          change
            (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ currentTarget).flip
                afterCnot.1 = _
          rw [hcnotFst]
        have hfirstFst : afterFirstToffoli.1 = afterX.1 :=
          toffoli_fst afterX
        have hcarryFst : afterCarry.1 = afterFirstToffoli.1 :=
          straightforwardCarryGates_fst n constant previous afterFirstToffoli
        have hsecondFst : afterSecondToffoli.1 = afterCarry.1 :=
          toffoli_fst afterCarry
        rw [show straightforwardCarryGates n constant ⟨index + 1, hbit⟩ =
            [prefixCnot, EncodedBit.GateSpec.x target] ++ [toffoli] ++
              straightforwardCarryGates n constant previous ++ [toffoli] ++
              [EncodedBit.GateSpec.x target] by
          simp [straightforwardCarryGates, current, currentTarget, previous,
            target, previousDirty, currentDirty, toffoli, prefixCnot, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change
          (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ currentTarget).flip
              afterSecondToffoli.1 = state.1
        rw [hsecondFst, hcarryFst, hfirstFst, hxFst]
        exact EncodedBit.flip_flip
          (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ currentTarget) state.1
      · let afterFirstToffoli := toffoli.step state
        let afterCarry := EncodedBit.GateSpec.stepList
          (straightforwardCarryGates n constant previous) afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hfirstFst : afterFirstToffoli.1 = state.1 :=
          toffoli_fst state
        have hcarryFst : afterCarry.1 = afterFirstToffoli.1 :=
          straightforwardCarryGates_fst n constant previous afterFirstToffoli
        have hsecondFst : afterSecondToffoli.1 = afterCarry.1 :=
          toffoli_fst afterCarry
        rw [show straightforwardCarryGates n constant ⟨index + 1, hbit⟩ =
            [toffoli] ++ straightforwardCarryGates n constant previous ++
              [toffoli] by
          simp [straightforwardCarryGates, current, currentTarget, previous,
            target, previousDirty, currentDirty, toffoli, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change afterSecondToffoli.1 = state.1
        rw [hsecondFst, hcarryFst, hfirstFst]
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- The selected dirty bit is toggled by exactly the classical carry and is
independent of every dirty input value.  Lower dirty bits may also be toggled
by this prefix; the enclosing output block later reverses the whole prefix. -/
theorem straightforwardCarryGates_currentDirty_get_of_higher (n : Nat)
    (constant : PlainAdder.Word n.succ) (bit : Fin n)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n)
    (hhigher : ∀ (lower upper : Fin n), lower.val < upper.val →
      ∀ input : PlainAdder.Word n.succ × StraightforwardDirty n,
        (straightforwardDirtyBit n upper).get
            (EncodedBit.GateSpec.stepList
              (straightforwardCarryGates n constant lower) input) =
          (straightforwardDirtyBit n upper).get input) :
    (straightforwardDirtyBit n bit).get
        (EncodedBit.GateSpec.stepList
          (straightforwardCarryGates n constant bit) state) =
      ((straightforwardDirtyBit n bit).get state ^^
        straightforwardCarryToggle n constant state.1 bit) := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · rw [show straightforwardCarryGates n constant ⟨0, hbit⟩ =
            [EncodedBit.GateSpec.cnot
              (straightforwardTargetBit n 0)
              (straightforwardDirtyBit n ⟨0, hbit⟩)
              (straightforwardTargetBit_wire_ne_dirtyBit n 0 ⟨0, hbit⟩)] by
            simp [straightforwardCarryGates, hc]]
        simp only [EncodedBit.GateSpec.stepList, id_eq]
        change (straightforwardDirtyBit n ⟨0, hbit⟩).get
            (EncodedBit.cnotStep (straightforwardTargetBit n 0)
              (straightforwardDirtyBit n ⟨0, hbit⟩) state) = _
        rw [EncodedBit.cnotStep_get_target]
        simp [straightforwardCarryToggle,
          Nat.BinaryArithmetic.natAddCarry, hc, Bool.carry]
      · simp [straightforwardCarryGates, hc,
          EncodedBit.GateSpec.stepList, straightforwardCarryToggle,
          Nat.BinaryArithmetic.natAddCarry, Bool.carry]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin n := ⟨index + 1, hbit⟩
      let currentTarget : Fin n.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self n)⟩
      let previous : Fin n := ⟨index, by omega⟩
      let target := straightforwardTargetBit n currentTarget
      let previousDirty := straightforwardDirtyBit n previous
      let currentDirty := straightforwardDirtyBit n current
      have hpreviousCurrent : previous ≠ current := by
        apply Fin.ne_of_val_ne
        dsimp [previous, current]
        omega
      have hpreviousCurrentWire :
          previousDirty.wire ≠ currentDirty.wire :=
        straightforwardDirtyBit_wire_ne n hpreviousCurrent
      have htargetCurrentWire : target.wire ≠ currentDirty.wire :=
        straightforwardTargetBit_wire_ne_dirtyBit n currentTarget current
      have htargetPreviousWire : target.wire ≠ previousDirty.wire :=
        straightforwardTargetBit_wire_ne_dirtyBit n currentTarget previous
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty target currentDirty
        htargetPreviousWire.symm hpreviousCurrentWire htargetCurrentWire
      have toffoli_current
          (input : PlainAdder.Word n.succ × StraightforwardDirty n) :
          currentDirty.get (toffoli.step input) =
            (currentDirty.get input ^^
              (previousDirty.get input && target.get input)) := by
        dsimp [toffoli]
        exact EncodedBit.toffoliStep_get_target _ _ _ input
      have toffoli_previous
          (input : PlainAdder.Word n.succ × StraightforwardDirty n) :
          previousDirty.get (toffoli.step input) =
            previousDirty.get input := by
        dsimp [toffoli]
        exact EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
          hpreviousCurrentWire.symm input
      have toffoli_target
          (input : PlainAdder.Word n.succ × StraightforwardDirty n) :
          target.get (toffoli.step input) = target.get input := by
        dsimp [toffoli]
        exact EncodedBit.toffoliStep_get_of_target_ne _ _ _ _
          htargetCurrentWire.symm input
      have hcarryRecurrence :
          straightforwardCarryToggle n constant state.1 current =
            Bool.carry (target.get state)
              (constant.val.testBit current.val)
              (straightforwardCarryToggle n constant state.1 previous) := by
        simp [straightforwardCarryToggle, target, currentTarget, current,
          previous, Nat.BinaryArithmetic.natAddCarry]
      by_cases hc : constant.val.testBit current.val
      · let prefixCnot := EncodedBit.GateSpec.cnot target currentDirty
          htargetCurrentWire
        let afterCnot := prefixCnot.step state
        let afterX := (EncodedBit.GateSpec.x target).step afterCnot
        let afterFirstToffoli := toffoli.step afterX
        let afterCarry := EncodedBit.GateSpec.stepList
          (straightforwardCarryGates n constant previous) afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hcnotCurrent : currentDirty.get afterCnot =
            (currentDirty.get state ^^ target.get state) := by
          dsimp [afterCnot, prefixCnot]
          exact EncodedBit.cnotStep_get_target target currentDirty state
        have hcnotPrevious : previousDirty.get afterCnot =
            previousDirty.get state := by
          dsimp [afterCnot, prefixCnot]
          exact EncodedBit.cnotStep_get_of_target_ne target currentDirty
            previousDirty hpreviousCurrentWire.symm state
        have hcnotTarget : target.get afterCnot = target.get state := by
          dsimp [afterCnot, prefixCnot]
          exact EncodedBit.cnotStep_get_of_target_ne target currentDirty target
            htargetCurrentWire.symm state
        have hxCurrent : currentDirty.get afterX = currentDirty.get afterCnot := by
          change currentDirty.get (target.flip afterCnot) = _
          exact EncodedBit.get_flip_of_wire_ne target currentDirty
            htargetCurrentWire afterCnot
        have hxPrevious : previousDirty.get afterX =
            previousDirty.get afterCnot := by
          change previousDirty.get (target.flip afterCnot) = _
          exact EncodedBit.get_flip_of_wire_ne target previousDirty
            htargetPreviousWire afterCnot
        have hxTarget : target.get afterX = !target.get afterCnot := by
          change target.get (target.flip afterCnot) = _
          exact EncodedBit.get_flip_self target afterCnot
        have hfirstCurrent : currentDirty.get afterFirstToffoli =
            (currentDirty.get afterX ^^
              (previousDirty.get afterX && target.get afterX)) :=
          toffoli_current afterX
        have hfirstPrevious : previousDirty.get afterFirstToffoli =
            previousDirty.get afterX := toffoli_previous afterX
        have hfirstTarget : target.get afterFirstToffoli =
            target.get afterX := toffoli_target afterX
        have hcarryCurrent : currentDirty.get afterCarry =
            currentDirty.get afterFirstToffoli :=
          hhigher previous current (by dsimp [previous, current]; omega)
            afterFirstToffoli
        have hcarryPrevious : previousDirty.get afterCarry =
            (previousDirty.get afterFirstToffoli ^^
              straightforwardCarryToggle n constant afterFirstToffoli.1
                previous) :=
          straightforwardCarryGates_currentDirty_get_of_higher n constant
            previous afterFirstToffoli hhigher
        have hcarryTarget : target.get afterCarry =
            target.get afterFirstToffoli := by
          dsimp [target]
          simp only [straightforwardTargetBit_get]
          rw [show afterCarry.1 = afterFirstToffoli.1 from
            straightforwardCarryGates_fst n constant previous
              afterFirstToffoli]
        have hafterCnotFst : afterCnot.1 = state.1 := by
          dsimp [afterCnot, prefixCnot]
          simp [EncodedBit.GateSpec.step, EncodedBit.cnotStep,
            currentDirty, straightforwardDirtyBit,
            BinaryLabelEncoding.prodRightBit]
          split <;> rfl
        have hafterXFst : afterX.1 =
            (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ currentTarget).flip
              state.1 := by
          change
            (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ currentTarget).flip
                afterCnot.1 = _
          rw [hafterCnotFst]
        have hafterFirstFst : afterFirstToffoli.1 = afterX.1 := by
          dsimp [afterFirstToffoli, toffoli]
          simp [EncodedBit.GateSpec.step, EncodedBit.toffoliStep,
            currentDirty, straightforwardDirtyBit,
            BinaryLabelEncoding.prodRightBit]
          split <;> rfl
        have hlowerCarry :
            straightforwardCarryToggle n constant afterFirstToffoli.1
                previous =
              straightforwardCarryToggle n constant state.1 previous := by
          unfold straightforwardCarryToggle
          apply natAddCarry_congr_left_of_testBit_eq_lt
          intro low hlow
          rw [hafterFirstFst, hafterXFst]
          let lowBit : Fin n.succ := ⟨low, by
            dsimp [previous] at hlow
            omega⟩
          have hne : currentTarget ≠ lowBit := by
            apply Fin.ne_of_val_ne
            have hlowCurrent : low < current.val := by
              dsimp [previous, current] at hlow ⊢
              omega
            dsimp [currentTarget, lowBit]
            exact (Nat.ne_of_lt hlowCurrent).symm
          simpa [PlainAdder.Schedule.PowerOfTwo.wordBit_get] using
            (EncodedBit.get_flip_of_wire_ne
              (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ currentTarget)
              (PlainAdder.Schedule.PowerOfTwo.wordBit n.succ lowBit)
              (straightforwardWordBit_wire_ne n.succ hne) state.1)
        have hsecondCurrent : currentDirty.get afterSecondToffoli =
            (currentDirty.get afterCarry ^^
              (previousDirty.get afterCarry && target.get afterCarry)) :=
          toffoli_current afterCarry
        rw [show straightforwardCarryGates n constant ⟨index + 1, hbit⟩ =
            [prefixCnot, EncodedBit.GateSpec.x target] ++ [toffoli] ++
              straightforwardCarryGates n constant previous ++ [toffoli] ++
              [EncodedBit.GateSpec.x target] by
          simp [straightforwardCarryGates, current, currentTarget, previous,
            target, previousDirty, currentDirty, toffoli, prefixCnot, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change currentDirty.get ((EncodedBit.GateSpec.x target).step
          afterSecondToffoli) =
            (currentDirty.get state ^^
              straightforwardCarryToggle n constant state.1 current)
        rw [show currentDirty.get ((EncodedBit.GateSpec.x target).step
            afterSecondToffoli) = currentDirty.get afterSecondToffoli by
          change currentDirty.get (target.flip afterSecondToffoli) = _
          exact EncodedBit.get_flip_of_wire_ne target currentDirty
            htargetCurrentWire afterSecondToffoli]
        rw [hsecondCurrent, hcarryCurrent, hcarryPrevious, hcarryTarget,
          hfirstCurrent, hfirstPrevious, hfirstTarget, hxCurrent, hxPrevious,
          hxTarget, hcnotCurrent, hcnotPrevious, hcnotTarget, hlowerCarry]
        rw [hcarryRecurrence, hc]
        cases currentDirty.get state <;>
          cases previousDirty.get state <;>
          cases target.get state <;>
          cases straightforwardCarryToggle n constant state.1 previous <;> rfl
      · have hcFalse : constant.val.testBit current.val = false :=
          Bool.eq_false_of_not_eq_true hc
        let afterFirstToffoli := toffoli.step state
        let afterCarry := EncodedBit.GateSpec.stepList
          (straightforwardCarryGates n constant previous) afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hfirstCurrent : currentDirty.get afterFirstToffoli =
            (currentDirty.get state ^^
              (previousDirty.get state && target.get state)) :=
          toffoli_current state
        have hfirstPrevious : previousDirty.get afterFirstToffoli =
            previousDirty.get state := toffoli_previous state
        have hfirstTarget : target.get afterFirstToffoli = target.get state :=
          toffoli_target state
        have hcarryCurrent : currentDirty.get afterCarry =
            currentDirty.get afterFirstToffoli :=
          hhigher previous current (by dsimp [previous, current]; omega)
            afterFirstToffoli
        have hcarryPrevious : previousDirty.get afterCarry =
            (previousDirty.get afterFirstToffoli ^^
              straightforwardCarryToggle n constant afterFirstToffoli.1
                previous) :=
          straightforwardCarryGates_currentDirty_get_of_higher n constant
            previous afterFirstToffoli hhigher
        have hcarryTarget : target.get afterCarry =
            target.get afterFirstToffoli := by
          dsimp [target]
          simp only [straightforwardTargetBit_get]
          rw [show afterCarry.1 = afterFirstToffoli.1 from
            straightforwardCarryGates_fst n constant previous
              afterFirstToffoli]
        have hafterFirstFst : afterFirstToffoli.1 = state.1 := by
          dsimp [afterFirstToffoli, toffoli]
          simp [EncodedBit.GateSpec.step, EncodedBit.toffoliStep,
            currentDirty, straightforwardDirtyBit,
            BinaryLabelEncoding.prodRightBit]
          split <;> rfl
        have hlowerCarry :
            straightforwardCarryToggle n constant afterFirstToffoli.1
                previous =
              straightforwardCarryToggle n constant state.1 previous := by
          rw [hafterFirstFst]
        have hsecondCurrent : currentDirty.get afterSecondToffoli =
            (currentDirty.get afterCarry ^^
              (previousDirty.get afterCarry && target.get afterCarry)) :=
          toffoli_current afterCarry
        rw [show straightforwardCarryGates n constant ⟨index + 1, hbit⟩ =
            [toffoli] ++ straightforwardCarryGates n constant previous ++
              [toffoli] by
          simp [straightforwardCarryGates, current, currentTarget, previous,
            target, previousDirty, currentDirty, toffoli, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change currentDirty.get afterSecondToffoli =
          (currentDirty.get state ^^
            straightforwardCarryToggle n constant state.1 current)
        rw [hsecondCurrent, hcarryCurrent, hcarryPrevious, hcarryTarget,
          hfirstCurrent, hfirstPrevious, hfirstTarget, hlowerCarry]
        rw [hcarryRecurrence, hcFalse]
        cases currentDirty.get state <;>
          cases previousDirty.get state <;>
          cases target.get state <;>
          cases straightforwardCarryToggle n constant state.1 previous <;> rfl
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- A carry prefix never writes a dirty bit above its selected carry output.
This is the separation fact used when the enclosing recurrence reads the
unknown higher dirty value on both sides of a lower carry computation. -/
theorem straightforwardCarryGates_higherDirty_get (n : Nat)
    (constant : PlainAdder.Word n.succ) (bit observed : Fin n)
    (hlt : bit.val < observed.val)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    (straightforwardDirtyBit n observed).get
        (EncodedBit.GateSpec.stepList
          (straightforwardCarryGates n constant bit) state) =
      (straightforwardDirtyBit n observed).get state := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · rw [show straightforwardCarryGates n constant ⟨0, hbit⟩ =
            [EncodedBit.GateSpec.cnot
              (straightforwardTargetBit n 0)
              (straightforwardDirtyBit n ⟨0, hbit⟩)
              (straightforwardTargetBit_wire_ne_dirtyBit n 0 ⟨0, hbit⟩)] by
            simp [straightforwardCarryGates, hc]]
        simp only [EncodedBit.GateSpec.stepList, id_eq]
        exact EncodedBit.cnotStep_get_of_target_ne
          (straightforwardTargetBit n 0)
          (straightforwardDirtyBit n ⟨0, hbit⟩)
          (straightforwardDirtyBit n observed)
          (straightforwardDirtyBit_wire_ne n (by
            apply Fin.ne_of_val_ne
            omega)) state
      · simp [straightforwardCarryGates, hc,
          EncodedBit.GateSpec.stepList]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin n := ⟨index + 1, hbit⟩
      let currentTarget : Fin n.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self n)⟩
      let previous : Fin n := ⟨index, by omega⟩
      let target := straightforwardTargetBit n currentTarget
      let previousDirty := straightforwardDirtyBit n previous
      let currentDirty := straightforwardDirtyBit n current
      let observedDirty := straightforwardDirtyBit n observed
      have hcurrentLt : current.val < observed.val := by
        simpa [current] using hlt
      have hpreviousLt : previous.val < observed.val := by
        exact lt_trans (by simp [previous, current]) hcurrentLt
      have hcurrentObserved : current ≠ observed := by
        apply Fin.ne_of_val_ne
        exact Nat.ne_of_lt hcurrentLt
      have hcurrentDirtyObserved : currentDirty.wire ≠ observedDirty.wire :=
        straightforwardDirtyBit_wire_ne n hcurrentObserved
      have htargetObserved : target.wire ≠ observedDirty.wire :=
        straightforwardTargetBit_wire_ne_dirtyBit n currentTarget observed
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty target currentDirty
        (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget previous).symm
        (straightforwardDirtyBit_wire_ne n (by
          apply Fin.ne_of_val_ne
          dsimp [previous, current]
          omega))
        (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget current)
      have toffoli_get
          (input : PlainAdder.Word n.succ × StraightforwardDirty n) :
          observedDirty.get (toffoli.step input) = observedDirty.get input := by
        dsimp [toffoli]
        exact EncodedBit.toffoliStep_get_of_target_ne
          previousDirty target currentDirty observedDirty
          hcurrentDirtyObserved input
      have x_get
          (input : PlainAdder.Word n.succ × StraightforwardDirty n) :
          observedDirty.get ((EncodedBit.GateSpec.x target).step input) =
            observedDirty.get input := by
        change observedDirty.get (target.flip input) = observedDirty.get input
        exact EncodedBit.get_flip_of_wire_ne target observedDirty
          htargetObserved input
      by_cases hc : constant.val.testBit current.val
      · let prefixCnot := EncodedBit.GateSpec.cnot target currentDirty
          (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget current)
        let afterCnot := prefixCnot.step state
        let afterX := (EncodedBit.GateSpec.x target).step afterCnot
        let afterFirstToffoli := toffoli.step afterX
        let afterCarry := EncodedBit.GateSpec.stepList
          (straightforwardCarryGates n constant previous) afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hcnotGet : observedDirty.get afterCnot = observedDirty.get state := by
          dsimp [afterCnot, prefixCnot]
          exact EncodedBit.cnotStep_get_of_target_ne target currentDirty
            observedDirty hcurrentDirtyObserved state
        have hxFirstGet : observedDirty.get afterX = observedDirty.get afterCnot :=
          x_get afterCnot
        have hfirstGet : observedDirty.get afterFirstToffoli =
            observedDirty.get afterX := toffoli_get afterX
        have hcarryGet : observedDirty.get afterCarry =
            observedDirty.get afterFirstToffoli :=
          straightforwardCarryGates_higherDirty_get n constant previous observed
            hpreviousLt afterFirstToffoli
        have hsecondGet : observedDirty.get afterSecondToffoli =
            observedDirty.get afterCarry := toffoli_get afterCarry
        rw [show straightforwardCarryGates n constant ⟨index + 1, hbit⟩ =
            [prefixCnot, EncodedBit.GateSpec.x target] ++ [toffoli] ++
              straightforwardCarryGates n constant previous ++ [toffoli] ++
              [EncodedBit.GateSpec.x target] by
          simp [straightforwardCarryGates, current, currentTarget, previous,
            target, previousDirty, currentDirty, toffoli, prefixCnot, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change observedDirty.get ((EncodedBit.GateSpec.x target).step
          afterSecondToffoli) = observedDirty.get state
        rw [x_get, hsecondGet, hcarryGet, hfirstGet, hxFirstGet, hcnotGet]
      · let afterFirstToffoli := toffoli.step state
        let afterCarry := EncodedBit.GateSpec.stepList
          (straightforwardCarryGates n constant previous) afterFirstToffoli
        let afterSecondToffoli := toffoli.step afterCarry
        have hfirstGet : observedDirty.get afterFirstToffoli =
            observedDirty.get state := toffoli_get state
        have hcarryGet : observedDirty.get afterCarry =
            observedDirty.get afterFirstToffoli :=
          straightforwardCarryGates_higherDirty_get n constant previous observed
            hpreviousLt afterFirstToffoli
        have hsecondGet : observedDirty.get afterSecondToffoli =
            observedDirty.get afterCarry := toffoli_get afterCarry
        rw [show straightforwardCarryGates n constant ⟨index + 1, hbit⟩ =
            [toffoli] ++ straightforwardCarryGates n constant previous ++
              [toffoli] by
          simp [straightforwardCarryGates, current, currentTarget, previous,
            target, previousDirty, currentDirty, toffoli, hc]]
        simp only [EncodedBit.GateSpec.stepList_append,
          EncodedBit.GateSpec.stepList, id_eq]
        change observedDirty.get afterSecondToffoli = observedDirty.get state
        rw [hsecondGet, hcarryGet, hfirstGet]
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- The selected dirty bit is toggled by exactly the propagated carry. -/
theorem straightforwardCarryGates_currentDirty_get (n : Nat)
    (constant : PlainAdder.Word n.succ) (bit : Fin n)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    (straightforwardDirtyBit n bit).get
        (EncodedBit.GateSpec.stepList
          (straightforwardCarryGates n constant bit) state) =
      ((straightforwardDirtyBit n bit).get state ^^
        straightforwardCarryToggle n constant state.1 bit) :=
  straightforwardCarryGates_currentDirty_get_of_higher n constant bit state
    (fun lower upper hlt input =>
      straightforwardCarryGates_higherDirty_get n constant lower upper hlt input)

/-- Every gate in a carry prefix is disjoint from any strictly higher target
bit.  In particular, the prefix commutes with flipping its output bit. -/
theorem straightforwardCarryGates_forall_bitDisjoint_target_of_lt (n : Nat)
    (constant : PlainAdder.Word n.succ) (bit : Fin n)
    (observed : Fin n.succ) (hlt : bit.val < observed.val) :
    (straightforwardCarryGates n constant bit).Forall
      (EncodedBit.GateSpec.bitDisjoint
        (straightforwardTargetBit n observed)) := by
  match bit with
  | ⟨0, hbit⟩ =>
      have hzeroObserved : (0 : Fin n.succ) ≠ observed := by
        apply Fin.ne_of_val_ne
        exact Nat.ne_of_lt hlt
      by_cases hc : constant.val.testBit 0
      · simp [straightforwardCarryGates, hc,
          EncodedBit.GateSpec.bitDisjoint,
          straightforwardTargetBit_wire_ne n hzeroObserved,
          (straightforwardTargetBit_wire_ne_dirtyBit n observed
            ⟨0, hbit⟩).symm]
      · simp [straightforwardCarryGates, hc]
  | ⟨index + 1, hbit⟩ =>
      let current : Fin n := ⟨index + 1, hbit⟩
      let currentTarget : Fin n.succ :=
        ⟨current.val, current.isLt.trans (Nat.lt_succ_self n)⟩
      let previous : Fin n := ⟨index, by omega⟩
      let target := straightforwardTargetBit n currentTarget
      let previousDirty := straightforwardDirtyBit n previous
      let currentDirty := straightforwardDirtyBit n current
      have hcurrentObserved : currentTarget ≠ observed := by
        apply Fin.ne_of_val_ne
        dsimp [currentTarget, current]
        exact Nat.ne_of_lt hlt
      have hpreviousObserved : previous.val < observed.val := by
        exact lt_trans (by simp [previous]) hlt
      have htargetObserved : target.wire ≠
          (straightforwardTargetBit n observed).wire :=
        straightforwardTargetBit_wire_ne n hcurrentObserved
      have hpreviousDirtyObserved : previousDirty.wire ≠
          (straightforwardTargetBit n observed).wire :=
        (straightforwardTargetBit_wire_ne_dirtyBit n observed previous).symm
      have hcurrentDirtyObserved : currentDirty.wire ≠
          (straightforwardTargetBit n observed).wire :=
        (straightforwardTargetBit_wire_ne_dirtyBit n observed current).symm
      let toffoli := EncodedBit.GateSpec.toffoli
        previousDirty target currentDirty
        (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget previous).symm
        (straightforwardDirtyBit_wire_ne n (by
          apply Fin.ne_of_val_ne
          dsimp [previous, current]
          omega))
        (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget current)
      have htoffoli : EncodedBit.GateSpec.bitDisjoint
          (straightforwardTargetBit n observed) toffoli := by
        exact ⟨hpreviousDirtyObserved, htargetObserved,
          hcurrentDirtyObserved⟩
      have hrecursive :=
        straightforwardCarryGates_forall_bitDisjoint_target_of_lt n constant
          previous observed hpreviousObserved
      by_cases hc : constant.val.testBit current.val
      · let prefixCnot := EncodedBit.GateSpec.cnot target currentDirty
          (straightforwardTargetBit_wire_ne_dirtyBit n currentTarget current)
        have hprefix : EncodedBit.GateSpec.bitDisjoint
            (straightforwardTargetBit n observed) prefixCnot :=
          ⟨htargetObserved, hcurrentDirtyObserved⟩
        have hx : EncodedBit.GateSpec.bitDisjoint
            (straightforwardTargetBit n observed)
            (EncodedBit.GateSpec.x target) := htargetObserved
        rw [show straightforwardCarryGates n constant ⟨index + 1, hbit⟩ =
            [prefixCnot, EncodedBit.GateSpec.x target] ++ [toffoli] ++
              straightforwardCarryGates n constant previous ++ [toffoli] ++
              [EncodedBit.GateSpec.x target] by
          simp [straightforwardCarryGates, current, currentTarget, previous,
            target, previousDirty, currentDirty, toffoli, prefixCnot, hc]]
        simp [hprefix, hx, htoffoli, hrecursive]
      · rw [show straightforwardCarryGates n constant ⟨index + 1, hbit⟩ =
            [toffoli] ++ straightforwardCarryGates n constant previous ++
              [toffoli] by
          simp [straightforwardCarryGates, current, currentTarget, previous,
            target, previousDirty, currentDirty, toffoli, hc]]
        simp [htoffoli, hrecursive]
termination_by bit.val
decreasing_by
  all_goals exact Nat.lt_succ_self index

/-- The literal dirty-carry block used to write one non-low target output
bit.  It computes the carry toggle, applies one CNOT, uncomputes the same
network in reverse, applies the matching CNOT, then adds the known constant
bit.  The two CNOTs cancel the unknown dirty initial value and retain only the
computed carry. -/
def straightforwardOutputBitGates (n : Nat)
    (constant : PlainAdder.Word n.succ) (bit : Fin n) :
    List (EncodedBit.GateSpec (straightforwardEncoding n)) :=
  let carry := straightforwardCarryGates n constant bit
  let target := straightforwardTargetBit n bit.succ
  let dirty := straightforwardDirtyBit n bit
  carry ++
    [EncodedBit.GateSpec.cnot dirty target
      (straightforwardTargetBit_wire_ne_dirtyBit n bit.succ bit).symm] ++
    carry.reverse ++
    [EncodedBit.GateSpec.cnot dirty target
      (straightforwardTargetBit_wire_ne_dirtyBit n bit.succ bit).symm] ++
    if constant.val.testBit bit.succ.val then
      [EncodedBit.GateSpec.x target]
    else
      []

/-- One compute-copy-uncompute output block cancels the unknown initial dirty
bit and writes exactly the propagated carry together with the known constant
bit.  The whole data value is restored apart from that one target flip. -/
theorem straightforwardOutputBitGates_step (n : Nat)
    (constant : PlainAdder.Word n.succ) (bit : Fin n)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    EncodedBit.GateSpec.stepList
        (straightforwardOutputBitGates n constant bit) state =
      if (straightforwardCarryToggle n constant state.1 bit ^^
          constant.val.testBit bit.succ.val) then
        (straightforwardTargetBit n bit.succ).flip state
      else
        state := by
  let carry := straightforwardCarryGates n constant bit
  let target := straightforwardTargetBit n bit.succ
  let dirty := straightforwardDirtyBit n bit
  let cnot := EncodedBit.GateSpec.cnot dirty target
    (straightforwardTargetBit_wire_ne_dirtyBit n bit.succ bit).symm
  have hdisjoint :
      ∀ gate, gate ∈ carry → EncodedBit.GateSpec.bitDisjoint target gate := by
    intro gate hgate
    exact List.forall_iff_forall_mem.mp
      (straightforwardCarryGates_forall_bitDisjoint_target_of_lt n constant
        bit bit.succ (by simp)) gate hgate
  have huncomputeFlip :
      EncodedBit.GateSpec.stepList carry.reverse
          (target.flip (EncodedBit.GateSpec.stepList carry state)) =
        target.flip state := by
    rw [EncodedBit.GateSpec.stepList_flip_comm_of_bitDisjoint]
    · exact congrArg target.flip
        (EncodedBit.GateSpec.stepList_reverse_stepList carry state)
    · intro gate hgate
      exact hdisjoint gate (List.mem_reverse.mp hgate)
  have huncompute :
      EncodedBit.GateSpec.stepList carry.reverse
          (EncodedBit.GateSpec.stepList carry state) = state :=
    EncodedBit.GateSpec.stepList_reverse_stepList carry state
  have hdirtyAfter :
      dirty.get (EncodedBit.GateSpec.stepList carry state) =
        (dirty.get state ^^
          straightforwardCarryToggle n constant state.1 bit) := by
    exact straightforwardCarryGates_currentDirty_get n constant bit state
  have hdirtyTargetFlip (input :
      PlainAdder.Word n.succ × StraightforwardDirty n) :
      dirty.get (target.flip input) = dirty.get input := by
    exact EncodedBit.get_flip_of_wire_ne target dirty
      (straightforwardTargetBit_wire_ne_dirtyBit n bit.succ bit) input
  unfold straightforwardOutputBitGates
  change EncodedBit.GateSpec.stepList
      (carry ++ [cnot] ++ carry.reverse ++ [cnot] ++
        if constant.val.testBit bit.succ.val then
          [EncodedBit.GateSpec.x target]
        else []) state = _
  simp only [EncodedBit.GateSpec.stepList_append]
  cases hinitial : dirty.get state <;>
    cases hcarry : straightforwardCarryToggle n constant state.1 bit <;>
    cases hconstant : constant.val.testBit bit.succ.val <;>
    simp [EncodedBit.GateSpec.stepList, cnot, target,
      EncodedBit.GateSpec.step,
      EncodedBit.cnotStep,
      hinitial, hcarry, hdirtyAfter, huncompute, huncomputeFlip,
      hdirtyTargetFlip, EncodedBit.flip_flip]

/-- An output block restores the complete borrowed dirty register. -/
theorem straightforwardOutputBitGates_snd (n : Nat)
    (constant : PlainAdder.Word n.succ) (bit : Fin n)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    (EncodedBit.GateSpec.stepList
        (straightforwardOutputBitGates n constant bit) state).2 = state.2 := by
  rw [straightforwardOutputBitGates_step]
  split
  · rfl
  · rfl

/-- An output block changes no target readout except its selected output bit;
that bit is the xor of its input, the propagated carry, and the constant. -/
theorem straightforwardOutputBitGates_fst_testBit (n : Nat)
    (constant : PlainAdder.Word n.succ) (bit : Fin n)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n)
    (observed : Fin n.succ) :
    (EncodedBit.GateSpec.stepList
        (straightforwardOutputBitGates n constant bit) state).1.val.testBit
          observed.val =
      if observed = bit.succ then
        ((state.1.val.testBit observed.val ^^
            straightforwardCarryToggle n constant state.1 bit) ^^
          constant.val.testBit observed.val)
      else
        state.1.val.testBit observed.val := by
  rw [← straightforwardTargetBit_get n observed
    (EncodedBit.GateSpec.stepList
      (straightforwardOutputBitGates n constant bit) state)]
  rw [← straightforwardTargetBit_get n observed state]
  rw [straightforwardOutputBitGates_step]
  have hflip :
      ((straightforwardTargetBit n bit.succ).flip state).1.val.testBit
          bit.succ.val =
        !state.1.val.testBit bit.succ.val := by
    simpa [straightforwardTargetBit_get] using
      (EncodedBit.get_flip_self
        (straightforwardTargetBit n bit.succ) state)
  simp only [Fin.val_succ] at hflip
  by_cases heq : observed = bit.succ
  · subst observed
    simp only [if_pos]
    cases hcarry : straightforwardCarryToggle n constant state.1 bit <;>
      cases hconstant : constant.val.testBit bit.succ.val <;>
      simp [hflip]
  · simp only [if_neg heq]
    split
    · exact EncodedBit.get_flip_of_wire_ne
        (straightforwardTargetBit n bit.succ)
        (straightforwardTargetBit n observed)
        (straightforwardTargetBit_wire_ne n (Ne.symm heq)) state
    · rfl

/-- Recursive high-to-low form of the HRS output sweep.  `count` processes
target bits `count, ..., 1`; the proof argument records that every selected
dirty carry bit exists in the fixed `n`-bit borrowed register. -/
def straightforwardHighGates (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    (count : Nat) → count ≤ n →
      List (EncodedBit.GateSpec (straightforwardEncoding n))
  | 0, _ => []
  | count + 1, hcount =>
      straightforwardOutputBitGates n constant ⟨count, by omega⟩ ++
        straightforwardHighGates n constant count (by omega)

/-- A fixed-width addition output bit depends only on input bits at or below
that position. -/
theorem word_add_testBit_congr_left_of_testBit_eq_le (width : Nat)
    (constant first second : PlainAdder.Word width) (observed : Fin width)
    (hbits : ∀ bit, bit ≤ observed.val →
      first.val.testBit bit = second.val.testBit bit) :
    (first + constant).val.testBit observed.val =
      (second + constant).val.testBit observed.val := by
  rw [PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
    width constant first observed]
  rw [PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
    width constant second observed]
  rw [hbits observed.val le_rfl]
  rw [Nat.BinaryArithmetic.natAddCarry_comm constant.val first.val]
  rw [Nat.BinaryArithmetic.natAddCarry_comm constant.val second.val]
  rw [natAddCarry_congr_left_of_testBit_eq_lt constant.val first.val
    second.val observed.val (fun bit hbit => hbits bit (Nat.le_of_lt hbit))]

/-- The recursive high-to-low sweep restores the borrowed dirty register. -/
theorem straightforwardHighGates_snd (n : Nat)
    (constant : PlainAdder.Word n.succ) (count : Nat) (hcount : count ≤ n)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    (EncodedBit.GateSpec.stepList
        (straightforwardHighGates n constant count hcount) state).2 = state.2 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      rw [show straightforwardHighGates n constant (count + 1) hcount =
          straightforwardOutputBitGates n constant ⟨count, by omega⟩ ++
            straightforwardHighGates n constant count (by omega) by rfl]
      rw [EncodedBit.GateSpec.stepList_append]
      rw [ih (by omega)]
      exact straightforwardOutputBitGates_snd n constant ⟨count, by omega⟩ state

/-- After processing `count` non-low output bits, precisely target bits
`1, ..., count` agree with addition by the constant; every other target bit
still agrees with the input. -/
theorem straightforwardHighGates_fst_testBit (n : Nat)
    (constant : PlainAdder.Word n.succ) (count : Nat) (hcount : count ≤ n)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n)
    (observed : Fin n.succ) :
    (EncodedBit.GateSpec.stepList
        (straightforwardHighGates n constant count hcount) state).1.val.testBit
          observed.val =
      if 0 < observed.val ∧ observed.val ≤ count then
        (state.1 + constant).val.testBit observed.val
      else
        state.1.val.testBit observed.val := by
  induction count generalizing state with
  | zero =>
      have houtside : ¬(0 < observed.val ∧ observed.val ≤ 0) := by omega
      rw [show straightforwardHighGates n constant 0 hcount = [] by rfl]
      change state.1.val.testBit observed.val =
        if 0 < observed.val ∧ observed.val ≤ 0 then _ else _
      rw [if_neg houtside]
  | succ count ih =>
      let top : Fin n := ⟨count, by omega⟩
      let afterTop := EncodedBit.GateSpec.stepList
        (straightforwardOutputBitGates n constant top) state
      rw [show straightforwardHighGates n constant (count + 1) hcount =
          straightforwardOutputBitGates n constant top ++
            straightforwardHighGates n constant count (by omega) by
        rfl]
      rw [EncodedBit.GateSpec.stepList_append]
      rw [ih (by omega) afterTop]
      by_cases hinside : 0 < observed.val ∧ observed.val ≤ count
      · rw [if_pos hinside]
        have houter : 0 < observed.val ∧ observed.val ≤ count + 1 :=
          ⟨hinside.1, by omega⟩
        rw [if_pos houter]
        apply word_add_testBit_congr_left_of_testBit_eq_le
        intro inputBit hinputBit
        let selected : Fin n.succ := ⟨inputBit, by omega⟩
        have hselected : selected ≠ top.succ := by
          apply Fin.ne_of_val_ne
          dsimp [selected, top]
          omega
        have hread := straightforwardOutputBitGates_fst_testBit n constant
          top state selected
        simpa [afterTop, if_neg hselected] using hread
      · rw [if_neg hinside]
        by_cases htop : observed.val = count + 1
        · have hselected : observed = top.succ := by
            apply Fin.ext
            simpa [top] using htop
          have houter : 0 < observed.val ∧ observed.val ≤ count + 1 := by
            omega
          rw [if_pos houter]
          have hread := straightforwardOutputBitGates_fst_testBit n constant
            top state observed
          rw [hread, if_pos hselected]
          simpa [straightforwardCarryToggle, top, Fin.val_succ, htop,
            Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm,
            Nat.BinaryArithmetic.natAddCarry_comm] using
              (PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
                n.succ constant state.1 observed).symm
        · have houter :
              ¬(0 < observed.val ∧ observed.val ≤ count + 1) := by
            omega
          rw [if_neg houter]
          have hselected : observed ≠ top.succ := by
            apply Fin.ne_of_val_ne
            dsimp [top]
            omega
          have hread := straightforwardOutputBitGates_fst_testBit n constant
            top state observed
          simpa [afterTop, if_neg hselected] using hread

/-- The final low-bit layer is a single known X gate exactly when the
least-significant constant bit is set. -/
def straightforwardLowGates (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    List (EncodedBit.GateSpec (straightforwardEncoding n)) :=
  if constant.val.testBit 0 then
    [EncodedBit.GateSpec.x (straightforwardTargetBit n 0)]
  else
    []

/-- The low-bit layer preserves the complete borrowed dirty register. -/
theorem straightforwardLowGates_snd (n : Nat)
    (constant : PlainAdder.Word n.succ)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    (EncodedBit.GateSpec.stepList
        (straightforwardLowGates n constant) state).2 = state.2 := by
  unfold straightforwardLowGates
  split <;> rfl

/-- Exact target-bit readout after the final low-bit layer. -/
theorem straightforwardLowGates_fst_testBit (n : Nat)
    (constant : PlainAdder.Word n.succ)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n)
    (observed : Fin n.succ) :
    (EncodedBit.GateSpec.stepList
        (straightforwardLowGates n constant) state).1.val.testBit observed.val =
      if observed = 0 then
        (state.1.val.testBit observed.val ^^ constant.val.testBit 0)
      else
        state.1.val.testBit observed.val := by
  rw [← straightforwardTargetBit_get n observed
    (EncodedBit.GateSpec.stepList
      (straightforwardLowGates n constant) state)]
  rw [← straightforwardTargetBit_get n observed state]
  have hflip :
      ((straightforwardTargetBit n 0).flip state).1.val.testBit 0 =
        !state.1.val.testBit 0 := by
    simpa only [straightforwardTargetBit_get, Fin.val_zero] using
      (EncodedBit.get_flip_self (straightforwardTargetBit n 0) state)
  unfold straightforwardLowGates
  by_cases hconstant : constant.val.testBit 0
  · rw [if_pos hconstant]
    simp only [EncodedBit.GateSpec.stepList, EncodedBit.GateSpec.step, id_eq]
    by_cases hzero : observed = 0
    · subst observed
      simp [hconstant, hflip]
    · rw [if_neg hzero]
      exact EncodedBit.get_flip_of_wire_ne
        (straightforwardTargetBit n 0)
        (straightforwardTargetBit n observed)
        (straightforwardTargetBit_wire_ne n (Ne.symm hzero)) state
  · rw [if_neg hconstant]
    simp [EncodedBit.GateSpec.stepList, hconstant]

/-- Literal HRS Fig. 2/3 gate schedule: process high bits first so each
carry network reads the still-unmodified lower target bits, then add the
least-significant constant bit.  The list contains only X, CNOT, and Toffoli
specifications and is compiled directly to the circuit below. -/
def straightforwardGates (n : Nat) (constant : PlainAdder.Word n.succ) :
    List (EncodedBit.GateSpec (straightforwardEncoding n)) :=
  straightforwardHighGates n constant n le_rfl ++
    straightforwardLowGates n constant

/-! ### Exact primitive coordinates -/

/-- Arithmetic indicator for one compile-time constant bit. -/
def constantBitMultiplicity {width : Nat}
    (constant : PlainAdder.Word width) (bit : Nat) : Nat :=
  if constant.val.testBit bit then 1 else 0

/-- Number of set constant bits below `count`.  This is the exact CNOT
coordinate of one carry network, before its compute/uncompute duplication in
an output block. -/
def carryCnotClosedForm {width : Nat}
    (constant : PlainAdder.Word width) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      carryCnotClosedForm constant count +
        constantBitMultiplicity constant count

/-- Twice the number of set non-low constant bits through `count`.  These are
the temporary target X gates in one carry network. -/
def carryXClosedForm {width : Nat}
    (constant : PlainAdder.Word width) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      carryXClosedForm constant count +
        2 * constantBitMultiplicity constant (count + 1)

/-- Exact CNOT coordinate of the high-to-low output sweep. -/
def highCnotClosedForm {width : Nat}
    (constant : PlainAdder.Word width) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      2 * carryCnotClosedForm constant (count + 1) + 2 +
        highCnotClosedForm constant count

/-- Exact X coordinate of the high-to-low output sweep. -/
def highXClosedForm {width : Nat}
    (constant : PlainAdder.Word width) : Nat → Nat
  | 0 => 0
  | count + 1 =>
      2 * carryXClosedForm constant count +
        constantBitMultiplicity constant (count + 1) +
        highXClosedForm constant count

theorem straightforwardCarryGates_toffoliMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ) (bit : Fin n) :
    ((straightforwardCarryGates n constant bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 2 * bit.val := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · simp [straightforwardCarryGates, hc]
      · simp [straightforwardCarryGates, hc]
  | ⟨index + 1, hbit⟩ =>
      let previous : Fin n := ⟨index, by omega⟩
      have ih := straightforwardCarryGates_toffoliMultiplicity_sum
        n constant previous
      by_cases hc : constant.val.testBit (index + 1)
      · simp [straightforwardCarryGates, previous, hc, ih]
        omega
      · simp [straightforwardCarryGates, previous, hc, ih]
        omega
termination_by bit.val
decreasing_by omega

theorem straightforwardCarryGates_cnotMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ) (bit : Fin n) :
    ((straightforwardCarryGates n constant bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      carryCnotClosedForm constant (bit.val + 1) := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · simp [straightforwardCarryGates, carryCnotClosedForm,
          constantBitMultiplicity, hc]
      · simp [straightforwardCarryGates, carryCnotClosedForm,
          constantBitMultiplicity, hc]
  | ⟨index + 1, hbit⟩ =>
      let previous : Fin n := ⟨index, by omega⟩
      have ih := straightforwardCarryGates_cnotMultiplicity_sum
        n constant previous
      by_cases hc : constant.val.testBit (index + 1)
      · simp [straightforwardCarryGates, carryCnotClosedForm,
          constantBitMultiplicity, previous, hc, ih]
        omega
      · simp [straightforwardCarryGates, carryCnotClosedForm,
          constantBitMultiplicity, previous, hc, ih]
termination_by bit.val
decreasing_by omega

theorem straightforwardCarryGates_xMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ) (bit : Fin n) :
    ((straightforwardCarryGates n constant bit).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      carryXClosedForm constant bit.val := by
  match bit with
  | ⟨0, hbit⟩ =>
      by_cases hc : constant.val.testBit 0
      · simp [straightforwardCarryGates, carryXClosedForm, hc]
      · simp [straightforwardCarryGates, carryXClosedForm, hc]
  | ⟨index + 1, hbit⟩ =>
      let previous : Fin n := ⟨index, by omega⟩
      have ih := straightforwardCarryGates_xMultiplicity_sum
        n constant previous
      by_cases hc : constant.val.testBit (index + 1)
      · simp [straightforwardCarryGates, carryXClosedForm,
          constantBitMultiplicity, previous, hc, ih]
        omega
      · simp [straightforwardCarryGates, carryXClosedForm,
          constantBitMultiplicity, previous, hc, ih]
termination_by bit.val
decreasing_by omega

theorem straightforwardOutputBitGates_toffoliMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ) (bit : Fin n) :
    ((straightforwardOutputBitGates n constant bit).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum = 4 * bit.val := by
  by_cases hc : constant.val.testBit (bit.val + 1)
  · simp [straightforwardOutputBitGates,
      straightforwardCarryGates_toffoliMultiplicity_sum, hc]
    omega
  · simp [straightforwardOutputBitGates,
      straightforwardCarryGates_toffoliMultiplicity_sum, hc]
    omega

theorem straightforwardOutputBitGates_cnotMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ) (bit : Fin n) :
    ((straightforwardOutputBitGates n constant bit).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      2 * carryCnotClosedForm constant (bit.val + 1) + 2 := by
  by_cases hc : constant.val.testBit (bit.val + 1)
  · simp [straightforwardOutputBitGates,
      straightforwardCarryGates_cnotMultiplicity_sum, hc]
    omega
  · simp [straightforwardOutputBitGates,
      straightforwardCarryGates_cnotMultiplicity_sum, hc]
    omega

theorem straightforwardOutputBitGates_xMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ) (bit : Fin n) :
    ((straightforwardOutputBitGates n constant bit).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      2 * carryXClosedForm constant bit.val +
        constantBitMultiplicity constant (bit.val + 1) := by
  by_cases hc : constant.val.testBit (bit.val + 1)
  · simp [straightforwardOutputBitGates,
      straightforwardCarryGates_xMultiplicity_sum,
      constantBitMultiplicity, hc]
    omega
  · simp [straightforwardOutputBitGates,
      straightforwardCarryGates_xMultiplicity_sum,
      constantBitMultiplicity, hc]
    omega

theorem straightforwardHighGates_toffoliMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ)
    (count : Nat) (hcount : count ≤ n) :
    ((straightforwardHighGates n constant count hcount).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * count * (count - 1) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show straightforwardHighGates n constant (count + 1) hcount =
          straightforwardOutputBitGates n constant ⟨count, by omega⟩ ++
            straightforwardHighGates n constant count (by omega) by rfl]
      simp only [List.map_append, List.sum_append,
        straightforwardOutputBitGates_toffoliMultiplicity_sum,
        ih (by omega)]
      cases count with
      | zero => simp
      | succ count => simp; ring

theorem straightforwardHighGates_cnotMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ)
    (count : Nat) (hcount : count ≤ n) :
    ((straightforwardHighGates n constant count hcount).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      highCnotClosedForm constant count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show straightforwardHighGates n constant (count + 1) hcount =
          straightforwardOutputBitGates n constant ⟨count, by omega⟩ ++
            straightforwardHighGates n constant count (by omega) by rfl]
      simp [highCnotClosedForm,
        straightforwardOutputBitGates_cnotMultiplicity_sum, ih (by omega)]

theorem straightforwardHighGates_xMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ)
    (count : Nat) (hcount : count ≤ n) :
    ((straightforwardHighGates n constant count hcount).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      highXClosedForm constant count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [show straightforwardHighGates n constant (count + 1) hcount =
          straightforwardOutputBitGates n constant ⟨count, by omega⟩ ++
            straightforwardHighGates n constant count (by omega) by rfl]
      simp [highXClosedForm,
        straightforwardOutputBitGates_xMultiplicity_sum, ih (by omega)]

/-- Exact Toffoli coordinate of the concrete R.0 schedule. -/
theorem straightforwardGates_toffoliMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ) :
    ((straightforwardGates n constant).map
        EncodedBit.GateSpec.toffoliMultiplicity).sum =
      2 * n * (n - 1) := by
  by_cases hc : constant.val.testBit 0
  · simp [straightforwardGates,
      straightforwardHighGates_toffoliMultiplicity_sum,
      straightforwardLowGates, hc]
  · simp [straightforwardGates,
      straightforwardHighGates_toffoliMultiplicity_sum,
      straightforwardLowGates, hc]

/-- Exact constant-pattern-dependent CNOT coordinate of the R.0 schedule. -/
theorem straightforwardGates_cnotMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ) :
    ((straightforwardGates n constant).map
        EncodedBit.GateSpec.cnotMultiplicity).sum =
      highCnotClosedForm constant n := by
  by_cases hc : constant.val.testBit 0
  · simp [straightforwardGates,
      straightforwardHighGates_cnotMultiplicity_sum,
      straightforwardLowGates, hc]
  · simp [straightforwardGates,
      straightforwardHighGates_cnotMultiplicity_sum,
      straightforwardLowGates, hc]

/-- Exact constant-pattern-dependent X coordinate of the R.0 schedule. -/
theorem straightforwardGates_xMultiplicity_sum
    (n : Nat) (constant : PlainAdder.Word n.succ) :
    ((straightforwardGates n constant).map
        EncodedBit.GateSpec.xMultiplicity).sum =
      highXClosedForm constant n + constantBitMultiplicity constant 0 := by
  by_cases hc : constant.val.testBit 0
  · simp [straightforwardGates,
      straightforwardHighGates_xMultiplicity_sum,
      straightforwardLowGates, constantBitMultiplicity, hc]
  · simp [straightforwardGates,
      straightforwardHighGates_xMultiplicity_sum,
      straightforwardLowGates, constantBitMultiplicity, hc]

/-- The complete literal HRS schedule is exact fixed-width addition on the
target and the identity on every borrowed dirty basis label. -/
theorem straightforwardGates_step (n : Nat)
    (constant : PlainAdder.Word n.succ)
    (state : PlainAdder.Word n.succ × StraightforwardDirty n) :
    EncodedBit.GateSpec.stepList (straightforwardGates n constant) state =
      (state.1 + constant, state.2) := by
  unfold straightforwardGates
  rw [EncodedBit.GateSpec.stepList_append]
  apply Prod.ext
  · apply PlainAdder.Schedule.PowerOfTwo.word_eq_of_testBit_eq
    intro observed
    rw [straightforwardLowGates_fst_testBit]
    by_cases hzero : observed = 0
    · rw [if_pos hzero]
      subst observed
      rw [straightforwardHighGates_fst_testBit]
      rw [if_neg (by simp : ¬(0 < (0 : Fin n.succ).val ∧
        (0 : Fin n.succ).val ≤ n))]
      simpa [Nat.BinaryArithmetic.natAddCarry] using
        (PlainAdder.Schedule.PowerOfTwo.word_add_val_testBit_eq_xor3
          n.succ constant state.1 0).symm
    · rw [if_neg hzero]
      rw [straightforwardHighGates_fst_testBit]
      have hpositive : 0 < observed.val := by
        have hval : observed.val ≠ 0 := by
          intro h
          exact hzero (Fin.ext h)
        omega
      have hle : observed.val ≤ n := by omega
      rw [if_pos ⟨hpositive, hle⟩]
  · rw [straightforwardLowGates_snd]
    exact straightforwardHighGates_snd n constant n le_rfl state

/-- Actual X/CNOT/Toffoli circuit compiled from the HRS straight-forward
gate list.  Its trace, resource pool, and depth are therefore all derived
from the same physical circuit. -/
def straightforwardProgram (n : Nat) (constant : PlainAdder.Word n.succ) :
    UnitaryCircuit (Qubits (straightforwardEncoding n).width) :=
  EncodedBit.GateSpec.programList (straightforwardGates n constant)

/-- Exact Toffoli count of the actual compiled R.0 program. -/
theorem straightforwardProgram_toffoli_count_eq
    (n : Nat) (constant : PlainAdder.Word n.succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (straightforwardProgram n constant).eventCost =
      2 * n * (n - 1) := by
  rw [straightforwardProgram,
    EncodedBit.GateSpec.programList_toffoli_count_eq_sum]
  exact straightforwardGates_toffoliMultiplicity_sum n constant

/-- Exact CNOT count of the actual compiled R.0 program. -/
theorem straightforwardProgram_cnot_count_eq
    (n : Nat) (constant : PlainAdder.Word n.succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (straightforwardProgram n constant).eventCost =
      highCnotClosedForm constant n := by
  rw [straightforwardProgram,
    EncodedBit.GateSpec.programList_cnot_count_eq_sum]
  exact straightforwardGates_cnotMultiplicity_sum n constant

/-- Exact X count of the actual compiled R.0 program. -/
theorem straightforwardProgram_x_count_eq
    (n : Nat) (constant : PlainAdder.Word n.succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (straightforwardProgram n constant).eventCost =
      highXClosedForm constant n + constantBitMultiplicity constant 0 := by
  rw [straightforwardProgram,
    EncodedBit.GateSpec.programList_x_count_eq_sum]
  exact straightforwardGates_xMultiplicity_sum n constant

/-- The actual straight-forward HRS program realizes its literal folded
encoded-bit schedule. -/
theorem straightforwardProgram_realizesFoldedStep (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    UnitaryCircuit.Realizes (straightforwardEncoding n)
      (straightforwardProgram n constant)
      (EncodedBit.GateSpec.stepList (straightforwardGates n constant)) :=
  EncodedBit.GateSpec.realizesList (straightforwardGates n constant)

/-- The flat physical program realizes exact addition while restoring every
dirty basis label. -/
theorem straightforwardProgram_realizes (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    UnitaryCircuit.Realizes (straightforwardEncoding n)
      (straightforwardProgram n constant)
      (fun state => (state.1 + constant, state.2)) :=
  UnitaryCircuit.Realizes.congrStep
    (straightforwardProgram_realizesFoldedStep n constant)
    (straightforwardGates_step n constant)

/-- The same physical program transported from its flat qubit label to the
typed target/borrowed product carrier. -/
def straightforwardCircuit (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    UnitaryCircuit (Register.prod (targetRegister n.succ) (Qubits n)) :=
  UnitaryCircuit.reindex (straightforwardIndexEquiv n)
    (straightforwardProgram n constant)

/-- Reindexing to the typed target/borrowed carrier preserves the exact
Toffoli coordinate. -/
theorem straightforwardCircuit_toffoli_count_eq
    (n : Nat) (constant : PlainAdder.Word n.succ) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (straightforwardCircuit n constant).eventCost =
      2 * n * (n - 1) := by
  change ResourcePool.count (.gate (.builtin "toffoli"))
      (straightforwardProgram n constant).eventCost = _
  exact straightforwardProgram_toffoli_count_eq n constant

/-- Reindexing to the typed target/borrowed carrier preserves the exact CNOT
coordinate. -/
theorem straightforwardCircuit_cnot_count_eq
    (n : Nat) (constant : PlainAdder.Word n.succ) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (straightforwardCircuit n constant).eventCost =
      highCnotClosedForm constant n := by
  change ResourcePool.count (.gate (.builtin "cnot"))
      (straightforwardProgram n constant).eventCost = _
  exact straightforwardProgram_cnot_count_eq n constant

/-- Reindexing to the typed target/borrowed carrier preserves the exact X
coordinate. -/
theorem straightforwardCircuit_x_count_eq
    (n : Nat) (constant : PlainAdder.Word n.succ) :
    ResourcePool.count (.gate (.builtin "x"))
        (straightforwardCircuit n constant).eventCost =
      highXClosedForm constant n + constantBitMultiplicity constant 0 := by
  change ResourcePool.count (.gate (.builtin "x"))
      (straightforwardProgram n constant).eventCost = _
  exact straightforwardProgram_x_count_eq n constant

/-- Basis action of the transported concrete circuit. -/
theorem straightforwardCircuit_applyNormalized_ket (n : Nat)
    (constant target : PlainAdder.Word n.succ)
    (dirty : (Qubits n).Index) :
    (straightforwardCircuit n constant).applyNormalized
        (NormalizedVector.ket
          (R := Register.prod (targetRegister n.succ) (Qubits n))
          (target, dirty)) =
      NormalizedVector.ket
        (R := Register.prod (targetRegister n.succ) (Qubits n))
        (target + constant, dirty) := by
  have hflat :=
    (straightforwardProgram_realizes n constant).apply_encoded_ket
      (target, dirty)
  have hreindexed := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
    (R := Qubits (straightforwardEncoding n).width)
    (S := Register.prod (targetRegister n.succ) (Qubits n))
    (straightforwardIndexEquiv n)
    (straightforwardProgram n constant)
    ((straightforwardEncoding n).encode (target, dirty))
    ((straightforwardEncoding n).encode (target + constant, dirty))
    hflat
  rw [straightforwardIndexEquiv_encode,
    straightforwardIndexEquiv_encode] at hreindexed
  unfold straightforwardCircuit
  convert hreindexed using 1

/-- Operator equality of the transported literal circuit with the strong
dirty-borrowed constant-adder specification. -/
theorem straightforwardCircuit_matrix_eq (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    (straightforwardCircuit n constant).matrix =
      op n.succ (Qubits n) constant := by
  apply Subtype.ext
  apply Matrix.ext
  intro output input
  rcases input with ⟨target, dirty⟩
  have hcircuit := straightforwardCircuit_applyNormalized_ket n constant
    target dirty
  have hop := op_apply_ket n.succ (Qubits n) constant target dirty
  have heq := hcircuit.trans hop.symm
  have hpoint := congrArg
    (fun state : NormalizedVector
      (Register.prod (targetRegister n.succ) (Qubits n)) => state output) heq
  simpa [UnitaryCircuit.applyNormalized, UnitaryOperator.apply,
    UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] using hpoint

/-- Same-circuit realization of the exact dirty-borrowed contract. -/
def straightforwardRealization (n : Nat)
    (constant : PlainAdder.Word n.succ) :
    CircuitRealization n.succ (Qubits n) constant where
  circuit := straightforwardCircuit n constant
  matrix_eq := straightforwardCircuit_matrix_eq n constant

/-- The concrete HRS schedule restores arbitrary dirty joint amplitudes, not
only clean or computational-basis ancillas. -/
theorem straightforwardCircuit_applyVec_arbitrary_joint_state (n : Nat)
    (constant : PlainAdder.Word n.succ)
    (state : HilbertVector
      (Register.prod (targetRegister n.succ) (Qubits n)))
    (target : PlainAdder.Word n.succ) (dirty : (Qubits n).Index) :
    (straightforwardCircuit n constant).applyVec state (target, dirty) =
      state (target - constant, dirty) :=
  CircuitRealization.applyVec_arbitrary_joint_state
    (straightforwardRealization n constant) state target dirty

end

end MAU.Addition.DirtyBorrowed
end QuantumAlg

end
