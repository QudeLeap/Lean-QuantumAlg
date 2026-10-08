/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Placement
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# The actual reset basis and the original short-DLP seed

The runtime layout correspondence preserves each wire value. In particular,
the binary zero label is precisely the all-zero label produced by the real
bank reset. The placed literal X reload therefore maps that established basis
state to the original source seed exactly, with no extra phase or allocation.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimePlacement

noncomputable section

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- The source's binary zero and the actual reset's wirewise zero are the same basis label. -/
theorem shortDLP_runtimeBasis_zero :
    (basisEquiv m ell width sameWires).symm 0 = ctx.quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (wireEquiv m ell width sameWires).surjective target
  apply Fin.ext
  have corresponding := Execution.basisOfEqualWires_value (runtimeLayout m ell width)
    ctx.quantumLayout (layoutWires m ell width sameWires)
    ((ShortDLP.layout (registerParameters m ell width)).binaryIndexEquiv.symm 0) source
  refine corresponding.trans ?_
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ totalQubits (registerParameters m ell width))).val.testBit
      source.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

/-- The existing X program maps the internally established reset state to the original seed. -/
theorem shortDLP_runtimeReload_apply_zero (N : Nat) :
    (reloadProgram m ell width sameWires N).applyNormalized
      (NormalizedVector.ket (R := ctx.register) ctx.quantumLayout.zeroLabel) =
      NormalizedVector.ket (R := ctx.register)
        ((basisEquiv m ell width sameWires).symm (CompiledMAU.reloadLabel m ell width N)) := by
  let corresponding : (runtimeLayout m ell width).register.Index ≃ ctx.register.Index :=
    Execution.basisOfEqualWires (runtimeLayout m ell width)
      ctx.quantumLayout (layoutWires m ell width sameWires)
  let sourceBasis : (runtimeLayout m ell width).register.Index ≃
      (Qubits (totalQubits (registerParameters m ell width))).Index :=
    (QubitLayout.canonical (totalQubits (registerParameters m ell width))).basisEquiv
  have action :
      (reloadProgram m ell width sameWires N).applyVec
          (HilbertVector.reindex (R := (runtimeLayout m ell width).register)
            (S := ctx.register) corresponding
            (NormalizedVector.ket (R := (runtimeLayout m ell width).register)
              (sourceBasis.symm 0)).vec) =
        HilbertVector.reindex (R := (runtimeLayout m ell width).register)
          (S := ctx.register) corresponding
          (NormalizedVector.ket (R := (runtimeLayout m ell width).register)
            (sourceBasis.symm (CompiledMAU.reloadLabel m ell width N))).vec := by
    change (reloadProgram m ell width sameWires N).matrix.applyVec _ = _
    rw [reloadProgram, Execution.unitaryOfEqualWires_matrix,
      UnitaryOperator.reindex_applyVec]
    exact congrArg (HilbertVector.reindex (R := (runtimeLayout m ell width).register)
      (S := ctx.register) corresponding)
      (congrArg (NormalizedVector.vec (R := (runtimeLayout m ell width).register))
        (CompiledMAU.shortDLP_reload_apply_zero m ell width N))
  rw [HilbertVector.reindex_ket, HilbertVector.reindex_ket] at action
  change (reloadProgram m ell width sameWires N).applyVec
      (NormalizedVector.ket (R := ctx.register) ((basisEquiv m ell width sameWires).symm 0)).vec =
    (NormalizedVector.ket (R := ctx.register)
      ((basisEquiv m ell width sameWires).symm (CompiledMAU.reloadLabel m ell width N))).vec
      at action
  rw [shortDLP_runtimeBasis_zero] at action
  apply NormalizedVector.ext
  intro row
  exact congrArg (fun vector : HilbertVector ctx.register => vector row) action

/-- A placed member's exact matrix uses the same source input and output labels. -/
theorem shortDLP_runtimeMember_matrix_entry (N : Nat) (generator target : (ZMod N)ˣ)
    (row column : ctx.register.Index) :
    (memberProgram m ell width sameWires N generator target).matrix row column =
      (compiledCircuit m ell width N generator target).binaryMatrix
        (basisEquiv m ell width sameWires row) (basisEquiv m ell width sameWires column) := by
  rw [memberProgram, Execution.unitaryOfEqualWires_matrix]
  let corresponding : (runtimeLayout m ell width).register.Index ≃ ctx.register.Index :=
    Execution.basisOfEqualWires (runtimeLayout m ell width)
      ctx.quantumLayout (layoutWires m ell width sameWires)
  let sourceBasis : (runtimeLayout m ell width).register.Index ≃
      (Qubits (totalQubits (registerParameters m ell width))).Index :=
    (QubitLayout.canonical (totalQubits (registerParameters m ell width))).basisEquiv
  change (compiledCircuit m ell width N generator target).matrix
      (corresponding.symm row) (corresponding.symm column) =
    (compiledCircuit m ell width N generator target).matrix
      (sourceBasis.symm (sourceBasis (corresponding.symm row)))
      (sourceBasis.symm (sourceBasis (corresponding.symm column)))
  exact congrArg₂ (fun first second : (runtimeLayout m ell width).register.Index =>
    (compiledCircuit m ell width N generator target).matrix first second)
    (sourceBasis.symm_apply_apply (corresponding.symm row)).symm
    (sourceBasis.symm_apply_apply (corresponding.symm column)).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimePlacement
