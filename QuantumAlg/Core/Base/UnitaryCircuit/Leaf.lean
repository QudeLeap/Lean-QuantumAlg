/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# One sealed circuit leaf

`UnitaryLeaf` is the sole atomic execution object used by the circuit syntax.
It fixes one role/label, one placement, and one certified unitary operator.
The event coordinate is a deterministic projection of that same role;
callers cannot supply a ledger or a depth expression.

Sealing establishes projection coherence, not mathematical label truth.  A
`UnitaryOperator` proves unitarity, but this module cannot prove that an
operator deserves its declared gate or opaque-subroutine label.  That
declaration is an explicit, auditable trust boundary.  An opaque subroutine
also makes no claim about a hidden expansion, ancilla usage, or hardware cost.
-/

section

namespace QuantumAlg

namespace Resource.GateLabel

/-- A standard gate coordinate. -/
public def builtin (name : String) (parameters : List Nat := []) : GateLabel :=
  { family := "builtin", name := name, parameters := parameters }

/-- A declaration-scoped non-builtin gate coordinate. -/
def declared (family name : String) (parameters : List Nat := []) : GateLabel :=
  { family := family, name := name, parameters := parameters }

end Resource.GateLabel

/-- The two and only two semantic roles of a unitary circuit leaf. -/
inductive UnitaryLeafRole where
  | gate (label : Resource.GateLabel)
  | subroutine (label : Resource.SubroutineLabel)
deriving DecidableEq

namespace UnitaryLeafRole

/-- The strict event coordinate fixed by a leaf role. -/
def event : UnitaryLeafRole → Resource.Event .quantum
  | .gate label => .gate label
  | .subroutine label => .quantumSubroutine label.quantum

@[simp] theorem event_gate (label : Resource.GateLabel) :
    event (.gate label) = (.gate label : Resource.Event .quantum) := rfl

@[simp] theorem event_subroutine (label : Resource.SubroutineLabel) :
    event (.subroutine label) =
      (.quantumSubroutine label.quantum : Resource.Event .quantum) := rfl

end UnitaryLeafRole

/-- One sealed atomic circuit execution.  Resource ledgers and depth are
intentionally absent from the stored object. -/
structure UnitaryLeaf (R : Register) where
  private mk ::
  /-- Gate versus opaque-subroutine role, including its event label. -/
  role : UnitaryLeafRole
  /-- Physical systems touched by this occurrence. -/
  systemIdx : List Nat
  /-- Certified unitary semantics of this occurrence. -/
  operator : UnitaryOperator R

namespace UnitaryLeaf

noncomputable section

/-- Declare one gate occurrence.  The label/operator association is an explicit
trust boundary; resource and depth metadata cannot be supplied. -/
def gate {R : Register} (label : Resource.GateLabel) (systemIdx : List Nat)
    (operator : UnitaryOperator R) : UnitaryLeaf R :=
  .mk (.gate label) systemIdx operator

/-- Declare one opaque-subroutine occurrence.  The declaration claims no
hidden expansion or hidden space usage. -/
def subroutine {R : Register} (label : Resource.SubroutineLabel)
    (systemIdx : List Nat) (operator : UnitaryOperator R) : UnitaryLeaf R :=
  .mk (.subroutine label) systemIdx operator

/-- Strict event coordinate projected from the sealed role. -/
def event {R : Register} (leaf : UnitaryLeaf R) : Resource.Event .quantum :=
  leaf.role.event

/-- Rewrite placement without changing role, event, or operator. -/
def rewriteSystemIdx {R : Register} (mapping : Nat → Nat)
    (leaf : UnitaryLeaf R) : UnitaryLeaf R :=
  .mk leaf.role (leaf.systemIdx.map mapping) leaf.operator

@[simp] theorem gate_role {R : Register} (label : Resource.GateLabel)
    (systemIdx : List Nat) (operator : UnitaryOperator R) :
    (gate label systemIdx operator).role = .gate label := rfl

@[simp] theorem gate_systemIdx {R : Register} (label : Resource.GateLabel)
    (systemIdx : List Nat) (operator : UnitaryOperator R) :
    (gate label systemIdx operator).systemIdx = systemIdx := rfl

@[simp] theorem gate_operator {R : Register} (label : Resource.GateLabel)
    (systemIdx : List Nat) (operator : UnitaryOperator R) :
    (gate label systemIdx operator).operator = operator := rfl

@[simp] theorem gate_event {R : Register} (label : Resource.GateLabel)
    (systemIdx : List Nat) (operator : UnitaryOperator R) :
    (gate label systemIdx operator).event =
      (.gate label : Resource.Event .quantum) := rfl

@[simp] theorem subroutine_role {R : Register}
    (label : Resource.SubroutineLabel) (systemIdx : List Nat)
    (operator : UnitaryOperator R) :
    (subroutine label systemIdx operator).role = .subroutine label := rfl

@[simp] theorem subroutine_systemIdx {R : Register}
    (label : Resource.SubroutineLabel) (systemIdx : List Nat)
    (operator : UnitaryOperator R) :
    (subroutine label systemIdx operator).systemIdx = systemIdx := rfl

@[simp] theorem subroutine_operator {R : Register}
    (label : Resource.SubroutineLabel) (systemIdx : List Nat)
    (operator : UnitaryOperator R) :
    (subroutine label systemIdx operator).operator = operator := rfl

@[simp] theorem subroutine_event {R : Register}
    (label : Resource.SubroutineLabel) (systemIdx : List Nat)
    (operator : UnitaryOperator R) :
    (subroutine label systemIdx operator).event =
      (.quantumSubroutine label.quantum : Resource.Event .quantum) := rfl

@[simp] theorem rewriteSystemIdx_role {R : Register} (mapping : Nat → Nat)
    (leaf : UnitaryLeaf R) :
    (leaf.rewriteSystemIdx mapping).role = leaf.role := rfl

@[simp] theorem rewriteSystemIdx_systemIdx {R : Register}
    (mapping : Nat → Nat) (leaf : UnitaryLeaf R) :
    (leaf.rewriteSystemIdx mapping).systemIdx = leaf.systemIdx.map mapping := rfl

@[simp] theorem rewriteSystemIdx_operator {R : Register}
    (mapping : Nat → Nat) (leaf : UnitaryLeaf R) :
    (leaf.rewriteSystemIdx mapping).operator = leaf.operator := rfl

@[simp] theorem rewriteSystemIdx_event {R : Register} (mapping : Nat → Nat)
    (leaf : UnitaryLeaf R) :
    (leaf.rewriteSystemIdx mapping).event = leaf.event := rfl

end

end UnitaryLeaf

end QuantumAlg

end
