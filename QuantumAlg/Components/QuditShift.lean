/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum
public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Gate.Unitary
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Cyclic shifts on one finite-dimensional physical system

A declared shift adds a fixed finite value at one selected wire of a
heterogeneous quantum layout. Every other basis coordinate is unchanged.
The native gate coordinate records the selected dimension and shift amount;
its placement is the selected wire's actual physical identity.

The operator is certified by its computational-basis permutation. Its use in
state evolution follows unitary conjugation [dW19, qcnotes.tex:5405].
-/

section

namespace QuantumAlg.QuditShift

noncomputable section

variable {systemCount : Nat}

private instance positiveDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

private def labelShift (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) : Equiv.Perm layout.Basis where
  toFun basis := Function.update basis wire (basis wire + amount)
  invFun basis := Function.update basis wire (basis wire - amount)
  left_inv basis := by
    funext index
    by_cases same : index = wire
    · subst index
      simp
    · simp [Function.update_of_ne same]
  right_inv basis := by
    funext index
    by_cases same : index = wire
    · subst index
      simp
    · simp [Function.update_of_ne same]

/-- Add the shift amount modulo the selected physical system's dimension. -/
public def operator (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) : UnitaryOperator layout.register :=
  UnitaryOperator.ofPerm (R := layout.register) (labelShift layout wire amount).symm

/-- Exact basis action on the complete heterogeneous register. -/
theorem operator_apply_ket (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) (basis : layout.Basis) :
    (operator layout wire amount).apply (NormalizedVector.ket basis) =
      NormalizedVector.ket (R := layout.register)
        (Function.update basis wire (basis wire + amount)) := by
  exact UnitaryOperator.ofPerm_apply_ket (R := layout.register)
    (labelShift layout wire amount).symm basis

/-- Public basis action of the declared finite-dimensional shift. -/
public theorem quditShift_operator_apply_ket (layout : QuantumLayout systemCount)
    (wire : Fin systemCount) (amount : Fin (layout.wire wire).dimension) (basis : layout.Basis) :
    (operator layout wire amount).apply (NormalizedVector.ket basis) =
      NormalizedVector.ket (R := layout.register)
        (Function.update basis wire (basis wire + amount)) :=
  operator_apply_ket layout wire amount basis

/-- The selected wire is updated by addition in its own finite basis. -/
theorem shifted_selected_value (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) (basis : layout.Basis) :
    (Function.update basis wire (basis wire + amount)) wire = basis wire + amount := by
  simp

/-- Every unselected physical system keeps its original basis value,
independently of its dimension. -/
theorem shifted_other_value (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) (basis : layout.Basis)
    (other : Fin systemCount) (different : other ≠ wire) :
    (Function.update basis wire (basis wire + amount)) other = basis other := by
  simp [Function.update_of_ne different]

/-- The declaration owns the native gate name, dimension, and modular shift. -/
def gateLabel {dimension : ℕ+} (amount : Fin dimension) : Resource.GateLabel :=
  .builtin "qudit-cyclic-shift" [dimension, amount.val]

/-- One gate occurrence at the selected wire's actual physical identity. -/
def leafAt (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) : UnitaryLeaf layout.register :=
  UnitaryLeaf.gate (gateLabel amount) [(layout.wire wire).identity]
    (operator layout wire amount)

/-- The atomic placement contains precisely the selected physical system. -/
theorem leafAt_systemIdx (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) :
    (leafAt layout wire amount).systemIdx = [(layout.wire wire).identity] := rfl

/-- The gate occurrence has the declared native coordinate. -/
theorem leafAt_event (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) :
    (leafAt layout wire amount).event = .gate (gateLabel amount) := rfl

/-- Execute the selected one-system gate within the complete physical layout. -/
public def program (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) : UnitaryCircuit layout.register :=
  UnitaryCircuit.ofLeafAt layout.identities (leafAt layout wire amount)
    layout.identities_nodup (by simp [leafAt]) (by
      intro identity member
      have same : identity = (layout.wire wire).identity := by
        simpa [leafAt] using member
      subst identity
      exact List.mem_ofFn.mpr ⟨wire, rfl⟩)

/-- Gate execution uses exactly the certified shift operator. -/
theorem program_matrix (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) :
    (program layout wire amount).matrix = operator layout wire amount := rfl

/-- The full layout remains available after the selected gate. -/
theorem program_physical_idx (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) :
    (program layout wire amount).physical_idx = layout.identities := rfl

/-- The public placed program executes the certified shift operator. -/
public theorem quditShift_program_matrix (layout : QuantumLayout systemCount)
    (wire : Fin systemCount) (amount : Fin (layout.wire wire).dimension) :
    (program layout wire amount).matrix = operator layout wire amount :=
  program_matrix layout wire amount

/-- The public placed program retains the exact complete physical footprint. -/
public theorem quditShift_program_physical_idx (layout : QuantumLayout systemCount)
    (wire : Fin systemCount) (amount : Fin (layout.wire wire).dimension) :
    (program layout wire amount).physical_idx = layout.identities :=
  program_physical_idx layout wire amount

/-- The actual native trace consists of the one selected gate occurrence. -/
theorem program_eventTrace (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) :
    (program layout wire amount).eventTrace = [.gate (gateLabel amount)] := rfl

/-- The event pool is recovered from that same one-gate program. -/
theorem program_eventCost (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) :
    (program layout wire amount).eventCost =
      ResourcePool.singleton (.gate (gateLabel amount)) := rfl

/-- The event critical path is the one declared gate occurrence. -/
theorem program_eventDepth (layout : QuantumLayout systemCount) (wire : Fin systemCount)
    (amount : Fin (layout.wire wire).dimension) :
    (program layout wire amount).eventDepth = .atom (.gate (gateLabel amount)) := rfl

end

end QuantumAlg.QuditShift

end
