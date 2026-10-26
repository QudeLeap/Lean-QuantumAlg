/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Pruned unitary address selection on the existing physical frame

The address order is most significant bit first. A supplied enable and one
clean prefix bit per address bit suffice for a depth-first traversal. Each
retained fork emits two Toffolis, one CNOT and two X gates. Whole missing
subtrees execute identity. No measurement clears the selector workspace.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

/-- A static finite address tree, permitting entire absent subtrees. -/
inductive SelectorTrie : Nat → Type where
  | skip (remaining : Nat) : SelectorTrie remaining
  | leaf : SelectorTrie 0
  | fork {remaining : Nat} (left right : SelectorTrie remaining) :
      SelectorTrie (remaining + 1)

namespace SelectorTrie

/-- Count retained actual selector forks; skipped subtrees contribute nothing. -/
def forks : {remaining : Nat} → SelectorTrie remaining → Nat
  | _, .skip _ => 0
  | _, .leaf => 0
  | _, .fork left right => 1 + left.forks + right.forks

/-- Count the callbacks that are physically present in the static program. -/
def leaves : {remaining : Nat} → SelectorTrie remaining → Nat
  | _, .skip _ => 0
  | _, .leaf => 1
  | _, .fork left right => left.leaves + right.leaves

/-- Remove a fork exactly when neither of its subtrees contains an operation. -/
def compactFork {remaining : Nat} (left right : SelectorTrie remaining) :
    SelectorTrie (remaining + 1) :=
  match left, right with
  | .skip _, .skip _ => .skip _
  | left, right => .fork left right

end SelectorTrie

/-- The original address positions, existing enable and clean prefix positions. -/
structure SelectorFrame {Data : Type} (encoding : BinaryLabelEncoding Data) (width : Nat) where
  /-- Address order is most significant bit first. -/
  address : Fin width → EncodedBit encoding
  /-- Position zero is the existing enable; positions 1 through width are clean prefixes. -/
  stack : Fin (width + 1) → EncodedBit encoding
  addressDistinct : Function.Injective (fun index => (address index).wire)
  stackDistinct : Function.Injective (fun index => (stack index).wire)
  separate : ∀ addressIndex stackIndex,
    (address addressIndex).wire ≠ (stack stackIndex).wire

namespace SelectorFrame

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- A leaf action must protect all address and stack fields, including unused prefix bits. -/
def Preserves (frame : SelectorFrame encoding width) (action : Data → Data) : Prop :=
  (∀ index state, (frame.address index).get (action state) = (frame.address index).get state) ∧
    (∀ index state, (frame.stack index).get (action state) = (frame.stack index).get state)

private def addressAt (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) : EncodedBit encoding := frame.address ⟨depth, present⟩

private def enableAt (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) : EncodedBit encoding := frame.stack ⟨depth, by omega⟩

private def prefixAt (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) : EncodedBit encoding := frame.stack ⟨depth + 1, by omega⟩

private lemma enable_address (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) :
    (frame.enableAt depth present).wire ≠ (frame.addressAt depth present).wire :=
  Ne.symm (frame.separate _ _)

private lemma enable_prefix (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) :
    (frame.enableAt depth present).wire ≠ (frame.prefixAt depth present).wire := by
  intro same
  have values := congrArg Fin.val (frame.stackDistinct same)
  change depth = depth + 1 at values
  omega

private lemma address_prefix (frame : SelectorFrame encoding width) (depth : Nat)
    (present : depth < width) :
    (frame.addressAt depth present).wire ≠ (frame.prefixAt depth present).wire :=
  frame.separate _ _

/-- Compute the zero-address child into the current clean prefix by actual native gates. -/
def leftGates (frame : SelectorFrame encoding width) (depth : Nat) (present : depth < width) :
    List (GateSpec encoding) :=
  [.x (frame.addressAt depth present),
    .toffoli (frame.enableAt depth present) (frame.addressAt depth present)
      (frame.prefixAt depth present) (frame.enable_address depth present)
      (frame.enable_prefix depth present) (frame.address_prefix depth present),
    .x (frame.addressAt depth present)]

/-- Toggle the prefix from the zero-address child to the one-address child. -/
def nextGate (frame : SelectorFrame encoding width) (depth : Nat) (present : depth < width) :
    GateSpec encoding :=
  .cnot (frame.enableAt depth present) (frame.prefixAt depth present)
    (frame.enable_prefix depth present)

/-- Clear the current one-address child with the original address and enable. -/
def clearGate (frame : SelectorFrame encoding width) (depth : Nat) (present : depth < width) :
    GateSpec encoding :=
  .toffoli (frame.enableAt depth present) (frame.addressAt depth present)
    (frame.prefixAt depth present) (frame.enable_address depth present)
    (frame.enable_prefix depth present) (frame.address_prefix depth present)

private lemma left_bound {offset remaining width : Nat}
    (bounded : offset + 2 ^ (remaining + 1) ≤ 2 ^ width) :
    offset + 2 ^ remaining ≤ 2 ^ width := by
  rw [pow_succ] at bounded
  omega

private lemma right_bound {offset remaining width : Nat}
    (bounded : offset + 2 ^ (remaining + 1) ≤ 2 ^ width) :
    offset + 2 ^ remaining + 2 ^ remaining ≤ 2 ^ width := by
  rw [pow_succ] at bounded
  omega

/-- Compile the actual finite subtree, retaining each supplied physical leaf program. -/
def programAt (frame : SelectorFrame encoding width) (physical : QubitLayout encoding.width)
    (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum) :
    {remaining : Nat} → (tree : SelectorTrie remaining) →
      (depth : Nat) → depth + remaining = width →
      (offset : Nat) → offset + 2 ^ remaining ≤ 2 ^ width →
        UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum
  | _, .skip _, _, _, _, _ => UnitaryCircuit.identity _ _ _
  | 0, .leaf, _, _, offset, bounded =>
      callback ⟨offset, by have := bounded; simp only [pow_zero] at this; omega⟩
  | remaining + 1, .fork left right, depth, fits, offset, bounded =>
      let present : depth < width := by omega
      (GateSpec.programList physical oracles (frame.leftGates depth present)).seq
        ((frame.programAt physical oracles callback left (depth + 1) (by omega)
          offset (left_bound bounded)).seq
          (((frame.nextGate depth present).program physical oracles).seq
            ((frame.programAt physical oracles callback right (depth + 1) (by omega)
              (offset + 2 ^ remaining) (right_bound bounded)).seq
                ((frame.clearGate depth present).program physical oracles))))

/-- The complete pruned traversal starts from the original address interval. -/
def program (frame : SelectorFrame encoding width) (physical : QubitLayout encoding.width)
    (oracles : OracleModel)
    (callback : Fin (2 ^ width) → UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum)
    (tree : SelectorTrie width) :
    UnitaryCircuit AlgorithmGate.model oracles physical.toQuantum :=
  frame.programAt physical oracles callback tree 0 (by omega) 0 (by omega)

end SelectorFrame

end

end QuantumAlg.EncodedBit.WindowLookup
