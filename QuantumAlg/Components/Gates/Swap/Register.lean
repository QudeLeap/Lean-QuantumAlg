/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Register exchange operator

These mathematical operators grant no native instruction or oracle access.
-/

namespace QuantumAlg

noncomputable section

/-- The permutation of joint basis labels that exchanges two `n`-qubit
registers. -/
public def swapRegistersPerm (n : ℕ) : Equiv.Perm (Fin (2 ^ (n + n))) :=
  ((prodEquiv (m := n) (n := n)).symm.trans
    (Equiv.prodComm (Fin (2 ^ n)) (Fin (2 ^ n)))).trans prodEquiv

/-- Metadata-free unitary operator that exchanges two `n`-qubit registers. -/
public def swapRegistersOp (n : ℕ) : UnitaryOperator (Qubits (n + n)) :=
  UnitaryOperator.ofPerm (swapRegistersPerm n)


end

end QuantumAlg
