/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Semantics

/-!
# Born state of the placed declared short-DLP member

The actual zero-prepared bank is transported to the source's binary zero.
Every selected member matrix column is then the previously proved complete
declared short-DLP output state, with the original group workspace retained.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

noncomputable section

private lemma layoutWires {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (Native.layout N).wires) :
    (Native.layout N).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- The source binary zero is the physical zero of the actual EH bank. -/
lemma declared_basis_zero {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (Native.layout N).wires) :
    (Native.basisEquiv N sameWires).symm 0 = ctx.quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (Native.wireEquiv N sameWires).surjective target
  apply Fin.ext
  have corresponding := Execution.basisOfEqualWires_value (Native.layout N)
    ctx.quantumLayout (layoutWires N sameWires)
    ((ShortDLP.layout (Native.parameters N)).binaryIndexEquiv.symm 0) source
  refine corresponding.trans ?_
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ ShortDLP.totalQubits (Native.parameters N))).val.testBit
      source.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

/-- A selected declared member applied to the live physical zero has exactly
the complete short-DLP Born state in the source's binary coordinates. -/
lemma declared_member_zero_amplitude {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (Native.layout N).wires) (input : Input N)
    (parameter : (ParameterShape N).Value) (row : ctx.register.Index) :
    (Native.declaredMember N sameWires parameter).matrix (sourceEnvironment input).quantum row
        ctx.quantumLayout.zeroLabel =
      (ShortDLP.BornProbability.evolvedState (Native.encoding input)
        (parameterUnit parameter) (parameterTarget parameter)).normalized
          (Native.basisEquiv N sameWires row) := by
  rw [← declared_basis_zero N sameWires,
    declaredMember_binaryMatrix_entry, Equiv.apply_symm_apply]
  change (ShortDLP.DeclaredStage.circuit N (Native.parameters N)
      (parameterUnit parameter) (parameterTarget parameter)).binaryMatrix (sourceEnvironment
        input).quantum
        (Native.basisEquiv N sameWires row)
        (prodEquiv
          ((0 : Fin (2 ^ (ShortDLP.firstBits (Native.parameters N) +
              (Native.parameters N).ell))),
            (0 : Fin (2 ^ (Native.parameters N).workspaceBits)))) =
      ((ShortDLP.DeclaredStage.circuit N (Native.parameters N)
        (parameterUnit parameter) (parameterTarget parameter)).binaryMatrix (sourceEnvironment
          input).quantum).applyVec
          (NormalizedVector.ket (R := Qubits
            (ShortDLP.totalQubits (Native.parameters N)))
            (prodEquiv
              ((0 : Fin (2 ^ (ShortDLP.firstBits (Native.parameters N) +
                  (Native.parameters N).ell))),
                (0 : Fin (2 ^ (Native.parameters N).workspaceBits)))) :
            HilbertVector (Qubits (ShortDLP.totalQubits (Native.parameters N))))
          (Native.basisEquiv N sameWires row)
  exact (HilbertOperator.applyVec_ket
    ((ShortDLP.DeclaredStage.circuit N (Native.parameters N)
      (parameterUnit parameter) (parameterTarget parameter)).binaryMatrix (sourceEnvironment
        input).quantum :
        HilbertOperator (Qubits (ShortDLP.totalQubits (Native.parameters N))))
    (prodEquiv
      ((0 : Fin (2 ^ (ShortDLP.firstBits (Native.parameters N) +
          (Native.parameters N).ell))),
        (0 : Fin (2 ^ (Native.parameters N).workspaceBits))))
    (Native.basisEquiv N sameWires row)).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
