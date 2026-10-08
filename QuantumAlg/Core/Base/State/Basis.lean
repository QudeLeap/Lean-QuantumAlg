/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.State.Normalized
public import QuantumAlg.Core.Base.Layout.Quantum
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Computational-basis preparation targets

A basis target specifies a mathematical normalized state on actual system
dimensions. It is not an executable preparation capability or a resource claim.
Executable zero preparation is fixed separately; other targets require an
actual construction in the selected operation language.
-/

namespace QuantumAlg

/-- A mathematical computational-basis preparation target on one finite-dimensional layout. -/
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

end BasisPreparation

end QuantumAlg
