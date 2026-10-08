/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed

/-!
# Exact source amplitudes of the actual runtime member

The placed compiled member acts on the same source seed established by the
zero preparation and literal loading, and by each actual reset/reload. Its amplitudes agree
exactly with the existing short-DLP evolved state through the proved physical
basis correspondence. The original Born analysis therefore applies without
a substituted oracle or an independently prescribed probability kernel.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimePlacement

noncomputable section

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Each amplitude of the actual placed member is the source compiled amplitude on the same seed. -/
theorem shortDLP_runtimeMember_seed_amplitude (N : Nat) (generator target : (ZMod N)ˣ)
    (row : ctx.register.Index) :
    (memberProgram m ell width sameWires N generator target).applyNormalized
      (NormalizedVector.ket (R := ctx.register)
        ((basisEquiv m ell width sameWires).symm (CompiledMAU.reloadLabel m ell width N))) row =
      (CompiledMAU.evolvedState m ell width N generator target).normalized
        (basisEquiv m ell width sameWires row) := by
  have actualColumn := HilbertOperator.applyVec_ket
    ((memberProgram m ell width sameWires N generator target).matrix :
      HilbertOperator ctx.register)
    ((basisEquiv m ell width sameWires).symm (CompiledMAU.reloadLabel m ell width N)) row
  have sourceColumn := HilbertOperator.applyVec_ket
    ((compiledCircuit m ell width N generator target).binaryMatrix :
      HilbertOperator (Qubits (totalQubits (registerParameters m ell width))))
    (CompiledMAU.reloadLabel m ell width N) (basisEquiv m ell width sameWires row)
  have actualEntry := shortDLP_runtimeMember_matrix_entry m ell width sameWires N
    generator target row
    ((basisEquiv m ell width sameWires).symm (CompiledMAU.reloadLabel m ell width N))
  have sourceEntry := congrArg
    (fun column : Fin (2 ^ totalQubits (registerParameters m ell width)) =>
      (compiledCircuit m ell width N generator target).binaryMatrix
        (basisEquiv m ell width sameWires row) column)
    ((basisEquiv m ell width sameWires).apply_symm_apply (CompiledMAU.reloadLabel m ell width N))
  exact actualColumn.trans (actualEntry.trans (sourceEntry.trans sourceColumn.symm))

/-- On the established seed, the actual runtime amplitudes are exactly the original Born source. -/
theorem shortDLP_runtimeMember_ideal_amplitude (N : Nat) (generator target : (ZMod N)ˣ)
    (nontrivial : 1 < N) (capacity : N < 2 ^ width) (row : ctx.register.Index) :
    (memberProgram m ell width sameWires N generator target).applyNormalized
      (NormalizedVector.ket (R := ctx.register)
        ((basisEquiv m ell width sameWires).symm (CompiledMAU.reloadLabel m ell width N))) row =
      (BornProbability.evolvedState (unitEncoding width N nontrivial capacity)
        generator target).normalized (basisEquiv m ell width sameWires row) :=
  (shortDLP_runtimeMember_seed_amplitude m ell width sameWires N generator target row).trans
    (congrArg (fun vector : NormalizedVector
        (Qubits (totalQubits (registerParameters m ell width))) =>
          vector (basisEquiv m ell width sameWires row))
      (CompiledMAU.evolvedState_normalized_eq_ideal m ell width N generator target
        nontrivial capacity))

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimePlacement
