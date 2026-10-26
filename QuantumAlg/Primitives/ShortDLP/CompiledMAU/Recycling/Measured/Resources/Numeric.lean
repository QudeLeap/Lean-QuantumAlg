/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.SuffixResources
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Space
import Mathlib.Tactic.NormNum

/-!
# Fixed-width actual measured-member Toffoli and qubit bounds

The original 1025/513 exponent configuration executes 2051 measured
multiplications. This specializes the actual complete measured member;
the surrounding retry, recovery, reset and reload program is accounted for
separately [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources

noncomputable section

open Execution

private lemma fixed_member_toffoli :
    resultBits 1025 513 * (28 * 2048 ^ 2 - 45 * 2048) = 240681469952 := by
  norm_num [resultBits]

/-- The actual configured measured member has the bound of its 2051 original multiplications. -/
lemma measuredRsa2048Member_toffoli_bound (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (modulus : BitVec 2048)
    (positive : 0 < modulus.toNat) (odd : modulus.getLsbD 0 = true)
    (generator target : (ZMod modulus.toNat)ˣ)
    (path : (member base noQuantum 1025 513 2048 (by decide) modulus generator target).Path) :
    ResourcePool.count (model := model) (.gate .toffoli)
      ((member base noQuantum 1025 513 2048 (by decide) modulus generator target).resourcePool
        path) ≤ 240681469952 :=
  (measuredMember_toffoli_bound base noQuantum 1025 513 2048 (by decide) (by decide)
    modulus positive odd generator target path).trans_eq fixed_member_toffoli

/-- The actual complete configured measured member retains exactly 4100 simultaneous qubits. -/
lemma measuredRsa2048Member_qubits (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (modulus : BitVec 2048)
    (generator target : (ZMod modulus.toNat)ˣ)
    (path : (member base noQuantum 1025 513 2048 (by decide) modulus generator target).Path) :
    (member base noQuantum 1025 513 2048 (by decide) modulus generator target).peakResidentSpace
      path (.quantumSystems 2) = 4100 :=
  measuredMember_qubits base noQuantum 1025 513 2048 (by decide) modulus generator target path

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Resources
