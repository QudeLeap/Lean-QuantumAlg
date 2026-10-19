/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Construction
public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Construction
import all QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Basic
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Unitary.Requirement
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Borrowed.Empty
import all QuantumAlg.Core.Execution.Output
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Borrowed

public import QuantumAlg.Primitives.QSP.SingleQubit.Chebyshev.Execution

/-!
# Polynomial characterization with complete executions

One common phase sequence realizes the prescribed polynomial pair for every
signal value, with the complete execution contract for each value
[Lin22, hermfunc.tex:1118-1138].
-/

namespace QuantumAlg.ReflectionBasedQuantumSignalProcessing.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution.OwnedQubits Polynomial

variable (φ₀ : Real) (φs : List Real) (x : Real) (hx : x ∈ Set.Icc (-1 : Real) 1)

/-- The original degree/parity/normalization characterization holds exactly,
and each synthesizing source word has a complete execution satisfying its
independent native contract [Lin22, hermfunc.tex:1118-1138]. -/
public lemma reflectionQSP_completeContract (d : Nat) (P Q : ℂ[X]) :
    IsQSPPair d P Q ↔
      ∃ (φ₀ : Real) (φs : List Real), φs.length = d ∧
        ∀ (x : Real) (hx : x ∈ Set.Icc (-1 : Real) 1),
          qspO φ₀ φs x = qspMat P Q x ∧
            ∃ candidate : Algorithm model (context 1) (context 1) .unit,
              candidate.Solves (problem φ₀ φs x hx) := by
  constructor
  · intro admissible
    obtain ⟨φ₀, φs, length, realizes⟩ := (characterization d P Q).mp admissible
    exact ⟨φ₀, φs, length, fun x hx =>
      ⟨realizes x hx, main φ₀ φs x hx⟩⟩
  · rintro ⟨φ₀, φs, length, realizes⟩
    exact (characterization d P Q).mpr ⟨φ₀, φs, length, fun x hx => (realizes x hx).1⟩

end

end QuantumAlg.ReflectionBasedQuantumSignalProcessing.Execution
