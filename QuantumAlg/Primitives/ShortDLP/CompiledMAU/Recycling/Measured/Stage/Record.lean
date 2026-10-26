/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Operator

/-!
# Full actual chronological record of a measured exponent stage

The old Store, overwritten arithmetic cells, prior-output feedback reads,
new exponent measurement and physical reset all retain their actual paths.
No chronological arithmetic outcome is identified with its reused storage
cell [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- Full actual Store/path of the original H/arithmetic/feedback/H/MZ/reset stage. -/
def stageRecord (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits)
    (store : Store (Context base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    Store (Context base noQuantum m ell width) ×
      (stage base noQuantum m ell width wide inverse outputs modulus unit position).Path :=
  let middle := stageArithmeticRecord base noQuantum m ell width modulus wide unit position
    store measured
  (middle.1.write
      (finiteOutput (control_qubit base noQuantum m ell width) (outputs position))
      (.finite outcome),
    ((), (middle.2,
      (feedbackPath base noQuantum m ell width inverse outputs position position.val le_rfl
        middle.1,
        ((), (outcome, ⟨.finite outcome, ()⟩))))))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
