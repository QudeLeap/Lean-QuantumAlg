/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Layout.Quantum

/-!
# Physical segments of a parallel Hadamard layer

The prefix occupies its original positions and the final qubit occupies the
next physical identity. Appending them yields exactly the canonical layout.
-/

namespace QuantumAlg.Gate.HadamardLayer

/-- Canonical ordered qubits for the complete layer. -/
public abbrev layout (width : Nat) : QuantumLayout width :=
  (QuantumSignature.qubits width).canonicalPlacement.layout

/-- The one actual final qubit, with physical identity equal to the prefix width. -/
@[expose, implicit_reducible]
public def lastLayout (width : Nat) : QuantumLayout 1 :=
  QuantumLayout.uniform 1 2 (fun _ => width) (fun _ _ _ => Subsingleton.elim _ _)

/-- The final physical system has qubit dimension. -/
public theorem hadamardLayer_last_dimension (width : Nat) :
    ((lastLayout width).wire 0).dimension = 2 := by
  rfl

/-- The new final qubit is disjoint from all prefix systems. -/
public theorem hadamardLayer_layout_disjoint (width : Nat) :
    List.Disjoint (layout width).identities (lastLayout width).identities := by
  apply List.disjoint_left.mpr
  intro identity inPrefix inLast
  obtain ⟨index, same⟩ := List.mem_ofFn.mp inPrefix
  obtain ⟨last, lastSame⟩ := List.mem_ofFn.mp inLast
  change index.val = identity at same
  change width = identity at lastSame
  omega

private theorem layout_eq_of_wire_eq {count : Nat} (first second : QuantumLayout count)
    (same : first.wire = second.wire) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Appending the original prefix and final physical qubit changes no layout information. -/
public theorem hadamardLayer_layout_append (width : Nat) :
    QuantumLayout.append (layout width) (lastLayout width)
      (hadamardLayer_layout_disjoint width) = layout (width + 1) := by
  apply layout_eq_of_wire_eq
  funext index
  refine Fin.addCases (fun first => ?_) (fun last => ?_) index
  · simp [QuantumLayout.append, layout, QuantumSignature.canonicalPlacement,
      QuantumSignature.place, QuantumSignature.qubits]
  · have lastZero : last = 0 := Subsingleton.elim _ _
    subst last
    simp [QuantumLayout.append, lastLayout, QuantumLayout.uniform, layout,
      QuantumSignature.canonicalPlacement, QuantumSignature.place, QuantumSignature.qubits]

end QuantumAlg.Gate.HadamardLayer
