/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Classical inputs beneath a prepared quantum layout

Preparing owned quantum systems adds a presence marker to the classical store.
Every existing structural classical operand retains its actual stored value.
This permits a sampled classical parameter to be consumed after preparation
without copying it or changing the program's instruction order.
-/

namespace QuantumAlg

namespace CStorageRef

/-- Lift a classical storage reference beneath one owned quantum layout. -/
public def underOwnedLayout {ctx : RuntimeCtx .quantum} {shape : CShape}
    (ref : CStorageRef ctx shape) (key : StorageKey) {systemCount : Nat}
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    CStorageRef (ctx.addOwnedLayout key layout fresh disjoint) shape where
  key := ref.key
  role := ref.role
  slot := .there ref.slot

end CStorageRef

namespace CInputRef

/-- Lift a complete structural operand beneath one owned quantum layout. -/
public def underOwnedLayout {ctx : RuntimeCtx .quantum} {shape : CShape}
    (input : CInputRef ctx shape) (key : StorageKey) {systemCount : Nat}
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    CInputRef (ctx.addOwnedLayout key layout fresh disjoint) shape :=
  match input with
  | .storage ref => .storage (ref.underOwnedLayout key layout fresh disjoint)
  | .product left right =>
      .product (left.underOwnedLayout key layout fresh disjoint)
        (right.underOwnedLayout key layout fresh disjoint)
  | .fixedVector entries =>
      .fixedVector fun index => (entries index).underOwnedLayout key layout fresh disjoint
  | .first source => .first (source.underOwnedLayout key layout fresh disjoint)
  | .second source => .second (source.underOwnedLayout key layout fresh disjoint)
  | .vectorGet source index =>
      .vectorGet (source.underOwnedLayout key layout fresh disjoint) index
  | .bitsGet source index =>
      .bitsGet (source.underOwnedLayout key layout fresh disjoint) index
  | .wordBitGet source index =>
      .wordBitGet (source.underOwnedLayout key layout fresh disjoint) index

end CInputRef

namespace Execution.Store

/-- Quantum preparation preserves every previously readable classical value. -/
public lemma read_pushOwnedLayout_underOwnedLayout {ctx : RuntimeCtx .quantum}
    (store : Store ctx) (key : StorageKey) {systemCount : Nat}
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    {observed : CShape} (input : CInputRef ctx observed) :
    (store.pushOwnedLayout key layout fresh disjoint).read
        (input.underOwnedLayout key layout fresh disjoint) = store.read input := by
  induction input with
  | storage => rfl
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CShape.Value.first sourceIH
  | second source sourceIH => exact congrArg CShape.Value.second sourceIH
  | vectorGet source index sourceIH => exact congrArg (fun value => value.get index) sourceIH
  | bitsGet source index sourceIH => exact congrArg (fun value => value.bitGet index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => value.wordBitGet index) sourceIH

end Execution.Store

end QuantumAlg
