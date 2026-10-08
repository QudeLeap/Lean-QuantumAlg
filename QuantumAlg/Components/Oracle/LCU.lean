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

/-- Fix the preparation and full SELECT family at the Problem boundary. -/
@[expose, implicit_reducible]
public def model {a n : Nat} (V : UnitaryOperator (Qubits a))
    (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) : OracleModel where
  Query := Query
  Coordinate := Query
  coordinateDecidableEq := inferInstance
  signature query := match query with
    | .prepare | .unprepare => QuantumSignature.qubits a
    | .select => QuantumSignature.qubits (a + n)
  operator query := match query with
    | .prepare => (UnitarySource.model V false true).operator .ordinary
    | .unprepare => (UnitarySource.model V false true).operator (.inverse rfl)
    | .select =>
        UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (a + n)).symm
          (lcuSelectOp U)
  coordinate query := query

/-- Inverse preparation is counted independently from forward preparation. -/
public theorem lcuOracle_preparation_coordinates_distinct {a n : Nat}
    (V : UnitaryOperator (Qubits a)) (U : Fin (2 ^ a) → UnitaryOperator (Qubits n)) :
    (model V U).coordinate .prepare ≠ (model V U).coordinate .unprepare := by
  change Query.prepare ≠ Query.unprepare
  decide

end
end QuantumAlg.LCUOracle
