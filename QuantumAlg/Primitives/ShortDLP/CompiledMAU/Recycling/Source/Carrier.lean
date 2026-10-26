/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Word

/-! # Mathematical modular-unit comparison carrier -/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Carrier

noncomputable section

abbrev units (N : Nat) [NeZero N] : Register where
  Index := (ZMod N)ˣ
  fintype := inferInstance
  decEq := inferInstance

abbrev full (N : Nat) [NeZero N] : Register := (Qubits 1).prod (units N)

variable {width : Nat} (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]

/-- The actual native control selects multiplication by the coefficient or identity. -/
def controlledAction (coefficient : (ZMod modulus.val)ˣ) :
    Equiv.Perm (full modulus.val).Index :=
  Equiv.prodCongrRight fun bit =>
    Equiv.mulLeft (if bit.val.testBit 0 then coefficient else 1)

/-- Translation of the same unit seed, with its full coherent phase. -/
def translation (coefficient : (ZMod modulus.val)ˣ) : UnitaryOperator (units modulus.val) :=
  UnitaryOperator.ofPerm (Equiv.mulLeft coefficient).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Carrier
