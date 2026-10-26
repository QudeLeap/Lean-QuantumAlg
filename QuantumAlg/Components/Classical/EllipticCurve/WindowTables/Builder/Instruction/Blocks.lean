/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Instruction.Sequence

/-!
# Block composition of the same chronological row Store updates

The finite-word Store interpreter is the ordered fold of the original
literal instruction slots. Grouping a fixed row into small consecutive
blocks shares its actual intermediate Stores; it changes no instruction
and avoids repeating large Store conversions in row-value proofs.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.RowInstruction

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width length : Nat}

/-- The native slots' same ordered finite-word Store updates form their literal left fold. -/
lemma updates_eq_foldl (spec : ModulusSpec width)
    (modulus : CWriteRef ctx (.unsignedWord (width + 1)))
    (count : Nat) (instructions : Fin count → RowInstruction ctx width length)
    (store : Store ctx) :
    updates spec modulus count instructions store =
      (List.ofFn instructions).foldl
        (fun current instruction => instruction.update spec modulus current) store := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      change updates spec modulus count (fun index => instructions index.succ)
        ((instructions 0).update spec modulus store) = _
      rw [ih, List.ofFn_succ, List.foldl_cons]

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.RowInstruction
