/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Real
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Real.Results
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Complex
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Complex.Results
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Queries
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Projected
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Projected.Results
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Endpoint.Projected.Queries
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Execution.Asymptotics
public import QuantumAlg.Core.Algorithm.Unitary.Owned.Binary.Space

/-!
# Complete quantum singular value transformation endpoints

Projected and Hermitian polynomial transformations use actual native circuits
under explicit source-access models. Their source block equalities, complete
execution contracts, query counts, physical space and depth all refer to the
same constructed words, including the degree-zero boundary.
-/
