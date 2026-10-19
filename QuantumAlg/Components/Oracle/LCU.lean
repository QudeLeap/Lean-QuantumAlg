/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.UnitarySource.Model
public import QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Components.Oracle.UnitarySource.Model
import all QuantumAlg.Components.Oracle.BlockEncoding
import all QuantumAlg.Core.Base.Layout.Signature

/-!
# Fixed LCU preparation and SELECT access

The access contract grants the preparation V, its inverse and one SELECT
operator for the fixed indexed unitary family. These are three independent
query coordinates; no inverse SELECT or controlled preparation is inferred
[Lin22, hermfunc.tex:531-554].
-/

namespace QuantumAlg.LCUOracle
noncomputable section

/-- Precisely the three accesses used by the LCU construction. -/
public inductive Query where
  | prepare
  | unprepare
  | select
  deriving DecidableEq

/-- The public source widths fix the three query signatures and coordinates. -/
@[expose, implicit_reducible]
public def model (a n : Nat) : OracleModel where
  Query := Query
  Coordinate := Query
  coordinateDecidableEq := inferInstance
  signature query := match query with
    | .prepare | .unprepare => QuantumSignature.qubits a
    | .select => QuantumSignature.qubits (a + n)
  coordinate query := query

/-- Source operators interpret the fixed preparation and SELECT interface. -/
public def interpretation {a n : Nat} (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) : (model a n).Interpretation where
  operator query := match query with
    | .prepare =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv a).symm V
    | .unprepare =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv a).symm V⁻¹
    | .select =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (a + n)).symm
          (lcuSelectOp U)

/-- Inverse preparation is counted independently from forward preparation. -/
public lemma lcuOracle_preparation_coordinates_distinct (a n : Nat) :
    (model a n).coordinate .prepare ≠ (model a n).coordinate .unprepare := by
  change Query.prepare ≠ Query.unprepare
  decide

end
end QuantumAlg.LCUOracle
