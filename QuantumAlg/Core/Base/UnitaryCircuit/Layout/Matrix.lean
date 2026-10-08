/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Matrix entries after identifying equal layouts

Exact layout equality transports the same computational values. The resulting
matrix entry is read at the correspondingly transported original coordinates.
-/

namespace QuantumAlg.UnitaryCircuit

/-- Transporting a physical basis vector along an equality of complete layouts
preserves its value at the inverse-transported label. -/
public theorem castLayout_vector_apply {count : Nat} {source target : QuantumLayout count}
    (same : source = target) (state : HilbertVector source.register)
    (basis : target.Basis) :
    (same ▸ state : HilbertVector target.register) basis =
      state (same.symm ▸ basis) := by
  cases same
  rfl

/-- Exact layout equality carries the all-zero physical label to the all-zero
label of the target layout. -/
public theorem castLayout_zeroLabel {count : Nat} {source target : QuantumLayout count}
    (same : source = target) :
    (same ▸ source.zeroLabel : target.Basis) = target.zeroLabel := by
  cases same
  rfl

/-- Transporting a target label backward and then forward along the same
layout equality restores that exact target label. -/
public theorem castLayout_symm_basis {count : Nat} {source target : QuantumLayout count}
    (same : source = target) (basis : target.Basis) :
    (same ▸ (same.symm ▸ basis : source.Basis) : target.Basis) = basis := by
  cases same
  rfl

/-- A computational-basis vector is unchanged apart from the label transport
induced by an equality of complete layouts. -/
public theorem castLayout_ket {count : Nat} {source target : QuantumLayout count}
    (same : source = target) (basis : source.Basis) :
    (same ▸ (NormalizedVector.ket (R := source.register) basis :
      HilbertVector source.register) : HilbertVector target.register) =
      (NormalizedVector.ket (R := target.register) (same ▸ basis) :
        HilbertVector target.register) := by
  cases same
  rfl

/-- Identifying full layouts retains every original local computational value. -/
public theorem castLayout_basis_value {count : Nat} {source target : QuantumLayout count}
    (same : source = target) (basis : source.Basis) (index : Fin count) :
    (((same ▸ basis : target.Basis) index).val) = (basis index).val := by
  cases same
  rfl

/-- Exact layout equality transports the input and output labels of the actual matrix. -/
public theorem castLayout_matrix_entry {gates : GateModel} {oracles : OracleModel}
    {count : Nat} {source target : QuantumLayout count} (same : source = target)
    (body : UnitaryCircuit gates oracles source) (row column : target.Basis) :
    (body.castLayout same).matrix row column =
      body.matrix (same.symm ▸ row) (same.symm ▸ column) := by
  cases same
  rfl

end QuantumAlg.UnitaryCircuit
