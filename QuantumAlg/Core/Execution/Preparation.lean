/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.State.Normalized
public import QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Computational-basis preparation on actual quantum systems

The prepared basis has one bounded value at each physical wire's declared
dimension. Its normalized state and native event both follow from these
values. Physical allocation and disjointness are checked by the circuit
constructor; external unknown inputs enter through the initial runtime state.
-/

namespace QuantumAlg

/-- A closed computational-basis preparation on one finite-dimensional layout. -/
public structure BasisPreparation {systemCount : Nat} (layout : QuantumLayout systemCount) where
  /-- One actual finite value for every declared physical system. -/
  value : layout.Basis

namespace BasisPreparation

/-- Prepare every declared system in its zero computational-basis state. -/
public def zero {systemCount : Nat} (layout : QuantumLayout systemCount) :
    BasisPreparation layout :=
  ⟨layout.zeroLabel⟩

/-- The normalized vector fixed by the specified computational-basis values. -/
public noncomputable def normalized {systemCount : Nat} {layout : QuantumLayout systemCount}
    (preparation : BasisPreparation layout) : NormalizedVector layout.register :=
  NormalizedVector.ket preparation.value

/-- Native label records ordered dimensions and values, independently of placement. -/
public def label {systemCount : Nat} {layout : QuantumLayout systemCount}
    (preparation : BasisPreparation layout) : Resource.PreparationLabel where
  family := "builtin"
  name := "computational-basis"
  parameters := systemCount ::
    ((layout.dimensions.map PNat.val) ++ List.ofFn (fun wire => (preparation.value wire).val))

/-- The preparation event belongs to the same declared basis operation. -/
public def event {systemCount : Nat} {layout : QuantumLayout systemCount}
    (preparation : BasisPreparation layout) : Resource.Event .quantum :=
  .preparation preparation.label

/-- Exact preparation cost derives from the single emitted native event. -/
public def eventCost {systemCount : Nat} {layout : QuantumLayout systemCount}
    (preparation : BasisPreparation layout) : ResourcePool .quantum :=
  ResourcePool.singleton preparation.event

end BasisPreparation

end QuantumAlg
