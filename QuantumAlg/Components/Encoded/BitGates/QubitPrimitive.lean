/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Word.CyclicShift
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Xor
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding

/-!
# Sealed qubit-primitive lifting

This focused module is re-exported by `QuantumAlg.Components.EncodedBitGates`.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit
namespace GateSpec

variable {Left Right : Type} {left : BinaryLabelEncoding Left}
  {right : BinaryLabelEncoding Right}

/-- Distinct wires remain distinct after lifting encoded bits to the left
field of a product encoding. -/
theorem prodLeftWire_ne (right : BinaryLabelEncoding Right)
    {a b : EncodedBit left} (h : a.wire ≠ b.wire) :
    (BinaryLabelEncoding.prodLeftBit left right a).wire ≠
      (BinaryLabelEncoding.prodLeftBit left right b).wire := by
  intro hwire
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hwire
  simpa [BinaryLabelEncoding.prodLeftBit,
    BinaryLabelEncoding.prodLeftWire] using hval

/-- Distinct wires remain distinct after lifting encoded bits to the right
field of a product encoding. -/
theorem prodRightWire_ne (left : BinaryLabelEncoding Left)
    {a b : EncodedBit right} (h : a.wire ≠ b.wire) :
    (BinaryLabelEncoding.prodRightBit left right a).wire ≠
      (BinaryLabelEncoding.prodRightBit left right b).wire := by
  intro hwire
  apply h
  apply Fin.ext
  have hval := congrArg Fin.val hwire
  have hval' : left.width + a.wire.val = left.width + b.wire.val := by
    simpa [BinaryLabelEncoding.prodRightBit,
      BinaryLabelEncoding.prodRightWire] using hval
  exact Nat.add_left_cancel hval'

/-- Lift an encoded-bit gate so it acts on the left field of a product
encoding and preserves the right field. -/
def prodLeft (right : BinaryLabelEncoding Right) :
    GateSpec left -> GateSpec (BinaryLabelEncoding.prod left right)
  | x target =>
      GateSpec.x (BinaryLabelEncoding.prodLeftBit left right target)
  | cnot control target hct =>
      GateSpec.cnot
        (BinaryLabelEncoding.prodLeftBit left right control)
        (BinaryLabelEncoding.prodLeftBit left right target)
        (prodLeftWire_ne right hct)
  | toffoli controlA controlB target hab ha hb =>
      GateSpec.toffoli
        (BinaryLabelEncoding.prodLeftBit left right controlA)
        (BinaryLabelEncoding.prodLeftBit left right controlB)
        (BinaryLabelEncoding.prodLeftBit left right target)
        (prodLeftWire_ne right hab)
        (prodLeftWire_ne right ha)
        (prodLeftWire_ne right hb)

/-- Lift an encoded-bit gate so it acts on the right field of a product
encoding and preserves the left field. -/
def prodRight (left : BinaryLabelEncoding Left) :
    GateSpec right -> GateSpec (BinaryLabelEncoding.prod left right)
  | x target =>
      GateSpec.x (BinaryLabelEncoding.prodRightBit left right target)
  | cnot control target hct =>
      GateSpec.cnot
        (BinaryLabelEncoding.prodRightBit left right control)
        (BinaryLabelEncoding.prodRightBit left right target)
        (prodRightWire_ne left hct)
  | toffoli controlA controlB target hab ha hb =>
      GateSpec.toffoli
        (BinaryLabelEncoding.prodRightBit left right controlA)
        (BinaryLabelEncoding.prodRightBit left right controlB)
        (BinaryLabelEncoding.prodRightBit left right target)
        (prodRightWire_ne left hab)
        (prodRightWire_ne left ha)
        (prodRightWire_ne left hb)

/-- Left-product lifting preserves the strict primitive event coordinate. -/
@[simp] theorem event_prodLeft (right : BinaryLabelEncoding Right)
    (gate : GateSpec left) :
    event (prodLeft right gate) = event gate := by
  cases gate <;> rfl

/-- Right-product lifting preserves the strict primitive event coordinate. -/
@[simp] theorem event_prodRight (left : BinaryLabelEncoding Left)
    (gate : GateSpec right) :
    event (prodRight left gate) = event gate := by
  cases gate <;> rfl

/-- Left-product lifting preserves the complete ordered strict event trace. -/
theorem map_event_prodLeft (right : BinaryLabelEncoding Right)
    (gates : List (GateSpec left)) :
    (gates.map (prodLeft right)).map event = gates.map event := by
  simp

/-- Right-product lifting preserves the complete ordered strict event trace. -/
theorem map_event_prodRight (left : BinaryLabelEncoding Left)
    (gates : List (GateSpec right)) :
    (gates.map (prodRight left)).map event = gates.map event := by
  simp










theorem length_prodLeft (right : BinaryLabelEncoding Right)
    (gates : List (GateSpec left)) :
    (gates.map (prodLeft right)).length = gates.length := by
  simp

theorem length_prodRight (left : BinaryLabelEncoding Left)
    (gates : List (GateSpec right)) :
    (gates.map (prodRight left)).length = gates.length := by
  simp

/-- A lifted left-product gate has exactly the original semantic action on the
left field and leaves the right field untouched. -/
theorem step_prodLeft (right : BinaryLabelEncoding Right)
    (gate : GateSpec left) (x : Left × Right) :
    (prodLeft right gate).step x = (gate.step x.1, x.2) := by
  cases gate with
  | x target =>
      rfl
  | cnot control target hct =>
      by_cases hcontrol : control.get x.1
      · simp [prodLeft, step, EncodedBit.cnotStep,
          BinaryLabelEncoding.prodLeftBit, hcontrol]
      · simp [prodLeft, step, EncodedBit.cnotStep,
          BinaryLabelEncoding.prodLeftBit, hcontrol]
  | toffoli controlA controlB target hab ha hb =>
      by_cases hcontrols : controlA.get x.1 && controlB.get x.1
      · simp [prodLeft, step, EncodedBit.toffoliStep,
          BinaryLabelEncoding.prodLeftBit, hcontrols]
      · simp [prodLeft, step, EncodedBit.toffoliStep,
          BinaryLabelEncoding.prodLeftBit, hcontrols]

/-- A lifted right-product gate has exactly the original semantic action on
the right field and leaves the left field untouched. -/
theorem step_prodRight (left : BinaryLabelEncoding Left)
    (gate : GateSpec right) (x : Left × Right) :
    (prodRight left gate).step x = (x.1, gate.step x.2) := by
  cases gate with
  | x target =>
      rfl
  | cnot control target hct =>
      by_cases hcontrol : control.get x.2
      · simp [prodRight, step, EncodedBit.cnotStep,
          BinaryLabelEncoding.prodRightBit, hcontrol]
      · simp [prodRight, step, EncodedBit.cnotStep,
          BinaryLabelEncoding.prodRightBit, hcontrol]
  | toffoli controlA controlB target hab ha hb =>
      by_cases hcontrols : controlA.get x.2 && controlB.get x.2
      · simp [prodRight, step, EncodedBit.toffoliStep,
          BinaryLabelEncoding.prodRightBit, hcontrols]
      · simp [prodRight, step, EncodedBit.toffoliStep,
          BinaryLabelEncoding.prodRightBit, hcontrols]

/-- A lifted left-product gate list has exactly the original folded semantic
action on the left field and leaves the right field untouched. -/
theorem stepList_prodLeft (right : BinaryLabelEncoding Right) :
    ∀ (gates : List (GateSpec left)) (x : Left × Right),
      stepList (gates.map (prodLeft right)) x =
        (stepList gates x.1, x.2)
  | [], _state => rfl
  | gate :: rest, state => by
      change stepList (rest.map (prodLeft right))
          ((prodLeft right gate).step state) =
        (stepList rest (gate.step state.1), state.2)
      rw [step_prodLeft right gate state]
      exact stepList_prodLeft right rest (gate.step state.1, state.2)

/-- A lifted right-product gate list has exactly the original folded semantic
action on the right field and leaves the left field untouched. -/
theorem stepList_prodRight (left : BinaryLabelEncoding Left) :
    ∀ (gates : List (GateSpec right)) (x : Left × Right),
      stepList (gates.map (prodRight left)) x =
        (x.1, stepList gates x.2)
  | [], _state => rfl
  | gate :: rest, state => by
      change stepList (rest.map (prodRight left))
          ((prodRight left gate).step state) =
        (state.1, stepList rest (gate.step state.2))
      rw [step_prodRight left gate state]
      exact stepList_prodRight left rest (state.1, gate.step state.2)

/-- A right-field wire can never equal a left-field wire in the same product
encoding. -/
theorem prodRightBit_wire_ne_prodLeftBit_wire
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (rightBit : EncodedBit right) (leftBit : EncodedBit left) :
    (BinaryLabelEncoding.prodRightBit left right rightBit).wire ≠
      (BinaryLabelEncoding.prodLeftBit left right leftBit).wire := by
  intro hwire
  have hval := congrArg Fin.val hwire
  change left.width + rightBit.wire.val = leftBit.wire.val at hval
  have hleft := leftBit.wire.isLt
  omega

/-- Every gate lifted into the right field is disjoint from every observed bit
in the left field. -/
theorem bitDisjoint_prodRight_leftBit
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (observed : EncodedBit left) (gate : GateSpec right) :
    bitDisjoint (BinaryLabelEncoding.prodLeftBit left right observed)
      (prodRight left gate) := by
  cases gate with
  | x target =>
      exact prodRightBit_wire_ne_prodLeftBit_wire left right target observed
  | cnot control target hct =>
      exact ⟨prodRightBit_wire_ne_prodLeftBit_wire left right control observed,
        prodRightBit_wire_ne_prodLeftBit_wire left right target observed⟩
  | toffoli controlA controlB target hab ha hb =>
      exact ⟨prodRightBit_wire_ne_prodLeftBit_wire left right controlA observed,
        prodRightBit_wire_ne_prodLeftBit_wire left right controlB observed,
        prodRightBit_wire_ne_prodLeftBit_wire left right target observed⟩

/-- Every gate lifted into the left field is disjoint from every observed bit
in the right field. -/
theorem bitDisjoint_prodLeft_rightBit
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (observed : EncodedBit right) (gate : GateSpec left) :
    bitDisjoint (BinaryLabelEncoding.prodRightBit left right observed)
      (prodLeft right gate) := by
  cases gate with
  | x target =>
      exact (prodRightBit_wire_ne_prodLeftBit_wire
        left right observed target).symm
  | cnot control target hct =>
      exact ⟨(prodRightBit_wire_ne_prodLeftBit_wire
          left right observed control).symm,
        (prodRightBit_wire_ne_prodLeftBit_wire
          left right observed target).symm⟩
  | toffoli controlA controlB target hab ha hb =>
      exact ⟨(prodRightBit_wire_ne_prodLeftBit_wire
          left right observed controlA).symm,
        (prodRightBit_wire_ne_prodLeftBit_wire
          left right observed controlB).symm,
        (prodRightBit_wire_ne_prodLeftBit_wire
          left right observed target).symm⟩

/-- Lifting both an observed bit and a disjoint gate into the left field
preserves their disjointness. -/
theorem bitDisjoint_prodLeft_of_bitDisjoint
    (right : BinaryLabelEncoding Right) (observed : EncodedBit left)
    (gate : GateSpec left) (h : bitDisjoint observed gate) :
    bitDisjoint (BinaryLabelEncoding.prodLeftBit left right observed)
      (prodLeft right gate) := by
  cases gate with
  | x target =>
      exact prodLeftWire_ne right h
  | cnot control target hct =>
      exact ⟨prodLeftWire_ne right h.1, prodLeftWire_ne right h.2⟩
  | toffoli controlA controlB target hab ha hb =>
      exact ⟨prodLeftWire_ne right h.1, prodLeftWire_ne right h.2.1,
        prodLeftWire_ne right h.2.2⟩

/-- Lifting both an observed bit and a disjoint gate into the right field
preserves their disjointness. -/
theorem bitDisjoint_prodRight_of_bitDisjoint
    (left : BinaryLabelEncoding Left) (observed : EncodedBit right)
    (gate : GateSpec right) (h : bitDisjoint observed gate) :
    bitDisjoint (BinaryLabelEncoding.prodRightBit left right observed)
      (prodRight left gate) := by
  cases gate with
  | x target =>
      exact prodRightWire_ne left h
  | cnot control target hct =>
      exact ⟨prodRightWire_ne left h.1, prodRightWire_ne left h.2⟩
  | toffoli controlA controlB target hab ha hb =>
      exact ⟨prodRightWire_ne left h.1, prodRightWire_ne left h.2.1,
        prodRightWire_ne left h.2.2⟩

end GateSpec
end EncodedBit

namespace QubitPrimitive

/-! ### Product-register lifting for raw basis-label programs -/

/-- Wire inherited from the left field of an `m + n` product register. -/
def prodLeftWire {m n : Nat} (wire : Fin m) : Fin (m + n) :=
  ⟨wire.val, by omega⟩

/-- Wire inherited from the right field of an `m + n` product register. -/
def prodRightWire {m n : Nat} (wire : Fin n) : Fin (m + n) :=
  ⟨m + wire.val, by omega⟩

@[simp] theorem prodLeftWire_val {m n : Nat} (wire : Fin m) :
    (prodLeftWire (n := n) wire).val = wire.val :=
  rfl

@[simp] theorem prodRightWire_val {m n : Nat} (wire : Fin n) :
    (prodRightWire (m := m) wire).val = m + wire.val :=
  rfl

theorem bitIndex_prodLeftWire {m n : Nat} (wire : Fin m) :
    (WireAddress.bitIndex (prodLeftWire (n := n) wire)).val =
      n + (WireAddress.bitIndex wire).val := by
  dsimp [WireAddress.bitIndex, prodLeftWire]
  omega

theorem bitIndex_prodRightWire {m n : Nat} (wire : Fin n) :
    (WireAddress.bitIndex (prodRightWire (m := m) wire)).val =
      (WireAddress.bitIndex wire).val := by
  dsimp [WireAddress.bitIndex, prodRightWire]
  omega

/-- Flipping a left-field wire commutes with product-label packing. -/
theorem prodEquiv_flip_left {m n : Nat} (wire : Fin m)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    prodEquiv (m := m) (n := n)
        (WireAddress.flipBit wire leftLabel, rightLabel) =
      WireAddress.flipBit (prodLeftWire (n := n) wire)
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) := by
  have h :=
    BinaryLabelEncoding.prodEquiv_flip_left
      (BinaryLabelEncoding.finIdentity m) (BinaryLabelEncoding.finIdentity n)
      wire leftLabel rightLabel
  exact h.trans (by
    congr 1)

/-- Flipping a right-field wire commutes with product-label packing. -/
theorem prodEquiv_flip_right {m n : Nat} (wire : Fin n)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    prodEquiv (m := m) (n := n)
        (leftLabel, WireAddress.flipBit wire rightLabel) =
      WireAddress.flipBit (prodRightWire (m := m) wire)
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) := by
  have h :=
    BinaryLabelEncoding.prodEquiv_flip_right
      (BinaryLabelEncoding.finIdentity m) (BinaryLabelEncoding.finIdentity n)
      wire leftLabel rightLabel
  exact h.trans (by
    congr 1)

/-- Lift a base-gate operation on the left field into an `m + n` register. -/
def prodLeft {m n : Nat} : QubitPrimitive m -> QubitPrimitive (m + n)
  | x target =>
      x (prodLeftWire (n := n) target)
  | cnot control target hct =>
      cnot (prodLeftWire (n := n) control) (prodLeftWire (n := n) target)
        (by
          intro h
          apply hct
          apply Fin.ext
          simpa [prodLeftWire] using congrArg Fin.val h)
  | toffoli controlA controlB target hab ha hb =>
      toffoli (prodLeftWire (n := n) controlA) (prodLeftWire (n := n) controlB)
        (prodLeftWire (n := n) target)
        (by
          intro h
          apply hab
          apply Fin.ext
          simpa [prodLeftWire] using congrArg Fin.val h)
        (by
          intro h
          apply ha
          apply Fin.ext
          simpa [prodLeftWire] using congrArg Fin.val h)
        (by
          intro h
          apply hb
          apply Fin.ext
          simpa [prodLeftWire] using congrArg Fin.val h)

/-- Lift a base-gate operation on the right field into an `m + n` register. -/
def prodRight {m n : Nat} : QubitPrimitive n -> QubitPrimitive (m + n)
  | x target =>
      x (prodRightWire (m := m) target)
  | cnot control target hct =>
      cnot (prodRightWire (m := m) control) (prodRightWire (m := m) target)
        (by
          intro h
          apply hct
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [prodRightWire_val] at hv
          omega)
  | toffoli controlA controlB target hab ha hb =>
      toffoli (prodRightWire (m := m) controlA)
        (prodRightWire (m := m) controlB) (prodRightWire (m := m) target)
        (by
          intro h
          apply hab
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [prodRightWire_val] at hv
          omega)
        (by
          intro h
          apply ha
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [prodRightWire_val] at hv
          omega)
        (by
          intro h
          apply hb
          apply Fin.ext
          have hv := congrArg Fin.val h
          simp only [prodRightWire_val] at hv
          omega)

/-- Lifting an operation to the left field preserves disjointness from a lifted
left-field observed wire. -/
theorem wireDisjoint_prodLeft_of_wireDisjoint {m n : Nat}
    {observed : Fin m} {op : QubitPrimitive m}
    (h : wireDisjoint observed op) :
    wireDisjoint (prodLeftWire (n := n) observed) (prodLeft (n := n) op) := by
  cases op with
  | x target =>
      intro heq
      apply h
      apply Fin.ext
      simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
  | cnot control target hct =>
      rcases h with ⟨hcontrol, htarget⟩
      constructor
      · intro heq
        apply hcontrol
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
      · intro heq
        apply htarget
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
  | toffoli controlA controlB target hab ha hb =>
      rcases h with ⟨hcontrolA, hcontrolB, htarget⟩
      constructor
      · intro heq
        apply hcontrolA
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
      constructor
      · intro heq
        apply hcontrolB
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq
      · intro heq
        apply htarget
        apply Fin.ext
        simpa [prodLeft, prodLeftWire] using congrArg Fin.val heq

/-- Lifting an operation to the right field preserves disjointness from a
lifted right-field observed wire. -/
theorem wireDisjoint_prodRight_of_wireDisjoint {m n : Nat}
    {observed : Fin n} {op : QubitPrimitive n}
    (h : wireDisjoint observed op) :
    wireDisjoint (prodRightWire (m := m) observed)
      (prodRight (m := m) op) := by
  cases op with
  | x target =>
      intro heq
      apply h
      apply Fin.ext
      have hv := congrArg Fin.val heq
      simp [prodRightWire] at hv
      omega
  | cnot control target hct =>
      rcases h with ⟨hcontrol, htarget⟩
      constructor
      · intro heq
        apply hcontrol
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega
      · intro heq
        apply htarget
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega
  | toffoli controlA controlB target hab ha hb =>
      rcases h with ⟨hcontrolA, hcontrolB, htarget⟩
      constructor
      · intro heq
        apply hcontrolA
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega
      constructor
      · intro heq
        apply hcontrolB
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega
      · intro heq
        apply htarget
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [prodRightWire] at hv
        omega

/-- A left-field observed wire is disjoint from any operation lifted from the
right field. -/
theorem wireDisjoint_prodRight_leftWire {m n : Nat}
    (observed : Fin m) (op : QubitPrimitive n) :
    wireDisjoint (prodLeftWire (n := n) observed)
      (prodRight (m := m) op) := by
  cases op with
  | x target =>
      intro heq
      have hv := congrArg Fin.val heq
      simp [prodLeftWire, prodRightWire] at hv
      omega
  | cnot control target hct =>
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
  | toffoli controlA controlB target hab ha hb =>
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega

/-- A right-field observed wire is disjoint from any operation lifted from the
left field. -/
theorem wireDisjoint_prodLeft_rightWire {m n : Nat}
    (observed : Fin n) (op : QubitPrimitive m) :
    wireDisjoint (prodRightWire (m := m) observed)
      (prodLeft (n := n) op) := by
  cases op with
  | x target =>
      intro heq
      have hv := congrArg Fin.val heq
      simp [prodLeftWire, prodRightWire] at hv
      omega
  | cnot control target hct =>
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
  | toffoli controlA controlB target hab ha hb =>
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      constructor
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [prodLeftWire, prodRightWire] at hv
        omega

/-- Wire map that inserts a middle field between the left and right fields of
an existing product register.  Left-field wires keep their address, while
right-field wires are shifted past the inserted middle field. -/
def insertMiddleWire {leftWidth middleWidth rightWidth : Nat}
    (wire : Fin (leftWidth + rightWidth)) :
    Fin (leftWidth + middleWidth + rightWidth) :=
  if h : wire.val < leftWidth then
    ⟨wire.val, by omega⟩
  else
    ⟨wire.val + middleWidth, by
      have hlt := wire.isLt
      omega⟩

theorem insertMiddleWire_injective {leftWidth middleWidth rightWidth : Nat}
    {left right : Fin (leftWidth + rightWidth)}
    (h :
      insertMiddleWire (middleWidth := middleWidth) left =
        insertMiddleWire (middleWidth := middleWidth) right) :
    left = right := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  by_cases hleft : left.val < leftWidth <;>
    by_cases hright : right.val < leftWidth <;>
      simp [insertMiddleWire, hleft, hright] at hv <;> omega

theorem insertMiddleWire_ne {leftWidth middleWidth rightWidth : Nat}
    {left right : Fin (leftWidth + rightWidth)}
    (h : left ≠ right) :
    insertMiddleWire (middleWidth := middleWidth) left ≠
      insertMiddleWire (middleWidth := middleWidth) right := by
  intro hmap
  exact h (insertMiddleWire_injective hmap)

/-- Lift a base-gate operation across an inserted middle register. -/
def insertMiddle {leftWidth middleWidth rightWidth : Nat} :
    QubitPrimitive (leftWidth + rightWidth) ->
      QubitPrimitive (leftWidth + middleWidth + rightWidth)
  | x target =>
      x (insertMiddleWire (middleWidth := middleWidth) target)
  | cnot control target hct =>
      cnot (insertMiddleWire (middleWidth := middleWidth) control)
        (insertMiddleWire (middleWidth := middleWidth) target)
        (insertMiddleWire_ne (middleWidth := middleWidth) hct)
  | toffoli controlA controlB target hab ha hb =>
      toffoli (insertMiddleWire (middleWidth := middleWidth) controlA)
        (insertMiddleWire (middleWidth := middleWidth) controlB)
        (insertMiddleWire (middleWidth := middleWidth) target)
        (insertMiddleWire_ne (middleWidth := middleWidth) hab)
        (insertMiddleWire_ne (middleWidth := middleWidth) ha)
        (insertMiddleWire_ne (middleWidth := middleWidth) hb)

/-- Pack a source product label and a middle label into the corresponding
three-field label where the middle field sits between source-left and
source-right. -/
def insertMiddleLabel
    (leftWidth middleWidth rightWidth : Nat)
    (source : Fin (2 ^ (leftWidth + rightWidth)))
    (middleLabel : Fin (2 ^ middleWidth)) :
    Fin (2 ^ (leftWidth + middleWidth + rightWidth)) :=
  let sourceParts :=
    (prodEquiv (m := leftWidth) (n := rightWidth)).symm source
  prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)
    (prodEquiv (m := leftWidth) (n := middleWidth)
      (sourceParts.1, middleLabel), sourceParts.2)

@[simp] theorem insertMiddleLabel_prodEquiv
    {leftWidth middleWidth rightWidth : Nat}
    (leftLabel : Fin (2 ^ leftWidth))
    (middleLabel : Fin (2 ^ middleWidth))
    (rightLabel : Fin (2 ^ rightWidth)) :
    insertMiddleLabel leftWidth middleWidth rightWidth
        (prodEquiv (m := leftWidth) (n := rightWidth)
          (leftLabel, rightLabel))
        middleLabel =
      prodEquiv (m := leftWidth + middleWidth) (n := rightWidth)
        (prodEquiv (m := leftWidth) (n := middleWidth)
          (leftLabel, middleLabel), rightLabel) := by
  simp [insertMiddleLabel]

theorem insertMiddleLabel_flipBit
    {leftWidth middleWidth rightWidth : Nat}
    (wire : Fin (leftWidth + rightWidth))
    (source : Fin (2 ^ (leftWidth + rightWidth)))
    (middleLabel : Fin (2 ^ middleWidth)) :
    WireAddress.flipBit
        (insertMiddleWire (middleWidth := middleWidth) wire)
        (insertMiddleLabel leftWidth middleWidth rightWidth source
          middleLabel) =
      insertMiddleLabel leftWidth middleWidth rightWidth
        (WireAddress.flipBit wire source) middleLabel := by
  rcases hparts :
      (prodEquiv (m := leftWidth) (n := rightWidth)).symm source with
    ⟨leftLabel, rightLabel⟩
  have hsource :
      prodEquiv (m := leftWidth) (n := rightWidth)
          (leftLabel, rightLabel) = source := by
    rw [← hparts]
    exact Equiv.apply_symm_apply
      (prodEquiv (m := leftWidth) (n := rightWidth)) source
  rw [← hsource]
  by_cases hleft : wire.val < leftWidth
  · let leftWire : Fin leftWidth := ⟨wire.val, hleft⟩
    have hwireSource :
        wire = prodLeftWire (n := rightWidth) leftWire := by
      apply Fin.ext
      simp [leftWire, prodLeftWire]
    have hwireTarget :
        insertMiddleWire (middleWidth := middleWidth) wire =
          prodLeftWire (n := rightWidth)
            (prodLeftWire (n := middleWidth) leftWire) := by
      apply Fin.ext
      simp [insertMiddleWire, hleft, leftWire, prodLeftWire]
    rw [hwireTarget, insertMiddleLabel_prodEquiv]
    rw [← prodEquiv_flip_left (n := rightWidth)
      (prodLeftWire (n := middleWidth) leftWire)
      (prodEquiv (m := leftWidth) (n := middleWidth)
        (leftLabel, middleLabel)) rightLabel]
    rw [← prodEquiv_flip_left (n := middleWidth)
      leftWire leftLabel middleLabel]
    rw [hwireSource]
    rw [← prodEquiv_flip_left (n := rightWidth)
      leftWire leftLabel rightLabel]
    rw [insertMiddleLabel_prodEquiv]
  · let rightWire : Fin rightWidth := ⟨wire.val - leftWidth, by
        have hlt := wire.isLt
        omega⟩
    have hwireSource :
        wire = prodRightWire (m := leftWidth) rightWire := by
      apply Fin.ext
      simp [rightWire, prodRightWire]
      omega
    have hwireTarget :
        insertMiddleWire (middleWidth := middleWidth) wire =
          prodRightWire (m := leftWidth + middleWidth) rightWire := by
      apply Fin.ext
      simp [insertMiddleWire, hleft, rightWire, prodRightWire]
      omega
    rw [hwireTarget, insertMiddleLabel_prodEquiv]
    rw [← prodEquiv_flip_right (m := leftWidth + middleWidth)
      rightWire
      (prodEquiv (m := leftWidth) (n := middleWidth)
        (leftLabel, middleLabel)) rightLabel]
    rw [hwireSource]
    rw [← prodEquiv_flip_right (m := leftWidth)
      rightWire leftLabel rightLabel]
    rw [insertMiddleLabel_prodEquiv]

theorem insertMiddleLabel_get_source_bit
    {leftWidth middleWidth rightWidth : Nat}
    (wire : Fin (leftWidth + rightWidth))
    (source : Fin (2 ^ (leftWidth + rightWidth)))
    (middleLabel : Fin (2 ^ middleWidth)) :
    (insertMiddleLabel leftWidth middleWidth rightWidth source
        middleLabel).val.testBit
        (WireAddress.bitIndex
          (insertMiddleWire (middleWidth := middleWidth) wire)).val =
      source.val.testBit (WireAddress.bitIndex wire).val := by
  rcases hparts :
      (prodEquiv (m := leftWidth) (n := rightWidth)).symm source with
    ⟨leftLabel, rightLabel⟩
  have hsource :
      prodEquiv (m := leftWidth) (n := rightWidth)
          (leftLabel, rightLabel) = source := by
    rw [← hparts]
    exact Equiv.apply_symm_apply
      (prodEquiv (m := leftWidth) (n := rightWidth)) source
  rw [← hsource]
  by_cases hleft : wire.val < leftWidth
  · let leftWire : Fin leftWidth := ⟨wire.val, hleft⟩
    have hwireSource :
        wire = prodLeftWire (n := rightWidth) leftWire := by
      apply Fin.ext
      simp [leftWire, prodLeftWire]
    have hwireTarget :
        insertMiddleWire (middleWidth := middleWidth) wire =
          prodLeftWire (n := rightWidth)
            (prodLeftWire (n := middleWidth) leftWire) := by
      apply Fin.ext
      simp [insertMiddleWire, hleft, leftWire, prodLeftWire]
    rw [hwireTarget, hwireSource, insertMiddleLabel_prodEquiv]
    rw [bitIndex_prodLeftWire]
    rw [prodEquiv_testBit_left]
    rw [bitIndex_prodLeftWire]
    rw [prodEquiv_testBit_left]
    rw [bitIndex_prodLeftWire]
    rw [prodEquiv_testBit_left]
  · let rightWire : Fin rightWidth := ⟨wire.val - leftWidth, by
        have hlt := wire.isLt
        omega⟩
    have hwireSource :
        wire = prodRightWire (m := leftWidth) rightWire := by
      apply Fin.ext
      simp [rightWire, prodRightWire]
      omega
    have hwireTarget :
        insertMiddleWire (middleWidth := middleWidth) wire =
          prodRightWire (m := leftWidth + middleWidth) rightWire := by
      apply Fin.ext
      simp [insertMiddleWire, hleft, rightWire, prodRightWire]
      omega
    rw [hwireTarget, hwireSource, insertMiddleLabel_prodEquiv]
    simp [bitIndex_prodRightWire, prodEquiv_testBit_right]

theorem applyLabel_prodLeft {m n : Nat} (op : QubitPrimitive m)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    (op.prodLeft (n := n)).applyLabel
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) =
      prodEquiv (m := m) (n := n)
        (op.applyLabel leftLabel, rightLabel) := by
  cases op with
  | x target =>
      simpa [prodLeft, applyLabel] using
        (prodEquiv_flip_left (n := n) target leftLabel rightLabel).symm
  | cnot control target hct =>
      unfold prodLeft applyLabel WireAddress.cnotMap
      simp only [bitIndex_prodLeftWire, prodEquiv_testBit_left]
      split
      · exact (prodEquiv_flip_left (n := n) target leftLabel rightLabel).symm
      · rfl
  | toffoli controlA controlB target hab ha hb =>
      unfold prodLeft applyLabel WireAddress.toffoliMap
      simp only [bitIndex_prodLeftWire, prodEquiv_testBit_left]
      split
      · exact (prodEquiv_flip_left (n := n) target leftLabel rightLabel).symm
      · rfl

theorem applyLabel_prodRight {m n : Nat} (op : QubitPrimitive n)
    (leftLabel : Fin (2 ^ m)) (rightLabel : Fin (2 ^ n)) :
    (op.prodRight (m := m)).applyLabel
        (prodEquiv (m := m) (n := n) (leftLabel, rightLabel)) =
      prodEquiv (m := m) (n := n)
        (leftLabel, op.applyLabel rightLabel) := by
  cases op with
  | x target =>
      simpa [prodRight, applyLabel] using
        (prodEquiv_flip_right (m := m) target leftLabel rightLabel).symm
  | cnot control target hct =>
      unfold prodRight applyLabel WireAddress.cnotMap
      simp only [bitIndex_prodRightWire, prodEquiv_testBit_right]
      split
      · exact (prodEquiv_flip_right (m := m) target leftLabel rightLabel).symm
      · rfl
  | toffoli controlA controlB target hab ha hb =>
      unfold prodRight applyLabel WireAddress.toffoliMap
      simp only [bitIndex_prodRightWire, prodEquiv_testBit_right]
      split
      · exact (prodEquiv_flip_right (m := m) target leftLabel rightLabel).symm
      · rfl

end QubitPrimitive

namespace EncodedBit

variable {Left Middle Right : Type}
  {left : BinaryLabelEncoding Left} {right : BinaryLabelEncoding Right}

/-- Lift an encoded bit across a newly inserted middle register.  The semantic
bit still acts on the original left/right pair and preserves the inserted
field, while its physical wire is moved by the same injection used by
`UnitaryCircuit.insertMiddle`. -/
def insertMiddle (middle : BinaryLabelEncoding Middle)
    (bit : EncodedBit (BinaryLabelEncoding.prod left right)) :
    EncodedBit
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.prod left middle) right) where
  wire := QubitPrimitive.insertMiddleWire
    (leftWidth := left.width) (middleWidth := middle.width) bit.wire
  get := fun x => bit.get (x.1.1, x.2)
  flip := fun x =>
    let y := bit.flip (x.1.1, x.2)
    ((y.1, x.1.2), y.2)
  get_eq := by
    intro x
    change
      (prodEquiv
          (prodEquiv (left.encode x.1.1, middle.encode x.1.2),
            right.encode x.2)).val.testBit
          (WireAddress.bitIndex
            (QubitPrimitive.insertMiddleWire
              (leftWidth := left.width) (middleWidth := middle.width)
              (rightWidth := right.width)
              (show Fin (left.width + right.width) from bit.wire))).val =
        bit.get (x.1.1, x.2)
    rw [← QubitPrimitive.insertMiddleLabel_prodEquiv
      (leftWidth := left.width) (middleWidth := middle.width)
      (rightWidth := right.width)]
    rw [QubitPrimitive.insertMiddleLabel_get_source_bit
      (leftWidth := left.width) (middleWidth := middle.width)
      (rightWidth := right.width)
      (wire := (show Fin (left.width + right.width) from bit.wire))]
    exact bit.get_eq (x.1.1, x.2)
  encode_flip := by
    intro x
    change
      prodEquiv
          (prodEquiv
              (left.encode (bit.flip (x.1.1, x.2)).1,
                middle.encode x.1.2),
            right.encode (bit.flip (x.1.1, x.2)).2) =
        WireAddress.flipBit (QubitPrimitive.insertMiddleWire bit.wire)
          (prodEquiv
            (prodEquiv (left.encode x.1.1, middle.encode x.1.2),
              right.encode x.2))
    rw [← QubitPrimitive.insertMiddleLabel_prodEquiv]
    rw [← QubitPrimitive.insertMiddleLabel_prodEquiv]
    have hbit :
        prodEquiv
            (left.encode (bit.flip (x.1.1, x.2)).1,
              right.encode (bit.flip (x.1.1, x.2)).2) =
          WireAddress.flipBit
            (show Fin (left.width + right.width) from bit.wire)
            (prodEquiv (left.encode x.1.1, right.encode x.2)) := by
      have h := bit.encode_flip (x.1.1, x.2)
      change
        prodEquiv
            (left.encode (bit.flip (x.1.1, x.2)).1,
              right.encode (bit.flip (x.1.1, x.2)).2) =
          WireAddress.flipBit
            (show Fin (left.width + right.width) from bit.wire)
            (prodEquiv (left.encode x.1.1, right.encode x.2)) at h
      exact h
    rw [hbit]
    exact (QubitPrimitive.insertMiddleLabel_flipBit
      (show Fin (left.width + right.width) from bit.wire)
      (prodEquiv (left.encode x.1.1, right.encode x.2))
      (middle.encode x.1.2)).symm

namespace GateSpec

/-- Lift an encoded base gate across a newly inserted middle register. -/
def insertMiddle (middle : BinaryLabelEncoding Middle) :
    GateSpec (BinaryLabelEncoding.prod left right) →
      GateSpec
        (BinaryLabelEncoding.prod (BinaryLabelEncoding.prod left middle) right)
  | .x target => .x (EncodedBit.insertMiddle middle target)
  | .cnot control target hct =>
      .cnot (EncodedBit.insertMiddle middle control)
        (EncodedBit.insertMiddle middle target)
        (QubitPrimitive.insertMiddleWire_ne
          (middleWidth := middle.width) hct)
  | .toffoli controlA controlB target hab ha hb =>
      .toffoli (EncodedBit.insertMiddle middle controlA)
        (EncodedBit.insertMiddle middle controlB)
        (EncodedBit.insertMiddle middle target)
        (QubitPrimitive.insertMiddleWire_ne
          (middleWidth := middle.width) hab)
        (QubitPrimitive.insertMiddleWire_ne
          (middleWidth := middle.width) ha)
        (QubitPrimitive.insertMiddleWire_ne
          (middleWidth := middle.width) hb)

/-- Inserting a middle register preserves one gate's semantic action on the
original left/right fields and leaves the inserted field untouched. -/
theorem step_insertMiddle (middle : BinaryLabelEncoding Middle)
    (gate : GateSpec (BinaryLabelEncoding.prod left right))
    (x : (Left × Middle) × Right) :
    (insertMiddle middle gate).step x =
      let y := gate.step (x.1.1, x.2)
      ((y.1, x.1.2), y.2) := by
  rcases x with ⟨⟨leftValue, middleValue⟩, rightValue⟩
  cases gate with
  | x target =>
      simp [insertMiddle, step, EncodedBit.insertMiddle]
  | cnot control target hct =>
      by_cases hcontrol : control.get (leftValue, rightValue)
      · simp [insertMiddle, step, EncodedBit.cnotStep,
          EncodedBit.insertMiddle, hcontrol]
      · simp [insertMiddle, step, EncodedBit.cnotStep,
          EncodedBit.insertMiddle, hcontrol]
  | toffoli controlA controlB target hab ha hb =>
      by_cases hcontrols :
          controlA.get (leftValue, rightValue) &&
            controlB.get (leftValue, rightValue)
      · simp [insertMiddle, step, EncodedBit.toffoliStep,
          EncodedBit.insertMiddle, hcontrols]
      · simp [insertMiddle, step, EncodedBit.toffoliStep,
          EncodedBit.insertMiddle, hcontrols]

/-- The list fold of inserted-middle gates is the lifted source fold. -/
theorem stepList_insertMiddle (middle : BinaryLabelEncoding Middle) :
    ∀ (gates : List (GateSpec (BinaryLabelEncoding.prod left right)))
      (x : (Left × Middle) × Right),
      stepList (gates.map (insertMiddle middle)) x =
        let y := stepList gates (x.1.1, x.2)
        ((y.1, x.1.2), y.2)
  | [], _ => rfl
  | gate :: rest, state => by
      change
        stepList (rest.map (insertMiddle middle))
            ((insertMiddle middle gate).step state) = _
      rw [step_insertMiddle middle gate state]
      exact stepList_insertMiddle middle rest
        (((gate.step (state.1.1, state.2)).1, state.1.2),
          (gate.step (state.1.1, state.2)).2)

end GateSpec
end EncodedBit

end

end QuantumAlg

end
