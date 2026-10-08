/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Core.Base.Register
public import QuantumAlg.Core.Base.State
public import QuantumAlg.Core.Base.Gate.Basic
public import QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Core.Base.Gate.OperatorNorm
public import QuantumAlg.Core.Base.Gate.Placement
public import QuantumAlg.Core.Base.Hamiltonian
public import QuantumAlg.Core.Base.Tensor
public import QuantumAlg.Core.Base.Tensor.Basic
public import QuantumAlg.Core.Base.Tensor.Certified
public import QuantumAlg.Core.Base.Marginal
public import QuantumAlg.Core.Base.Depth
public import QuantumAlg.Core.Base.Layout
public import QuantumAlg.Core.Base.Accounting
public import QuantumAlg.Core.Base.Accounting.Kind
public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Control.Operator
public import QuantumAlg.Core.Base.UnitaryCircuit.Leaf
public import QuantumAlg.Core.Base.UnitaryCircuit.Construction
public import QuantumAlg.Core.Base.UnitaryCircuit.Space
public import QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.UnitaryCircuit.Family
public import QuantumAlg.Core.Base.UnitaryCircuit.Physical
public import QuantumAlg.Core.Base.UnitaryCircuit.Realization

/-!
# QuantumAlg core base layer

This head exports state and operator semantics, sealed pure UnitaryCircuit
construction (including dagger and activation-parametric control), tensor,
event/space accounting, and symbolic-depth foundations. Concrete Z-state laws
are exported by `QuantumAlg.Core.Measure`; complete
classical and quantum execution is exported by `QuantumAlg.Core.Algorithm`.
-/

section

end
