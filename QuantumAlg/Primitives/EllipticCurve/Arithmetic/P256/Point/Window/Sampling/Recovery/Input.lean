/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Program
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Original paired Fourier cells supplied to the paid nearest decoder

Each chronological stream is reversed once for the existing big-endian
packing instruction. These are structural read operands. The actual packing,
decode, split, nearest scaling and candidate check remain real instructions
of the recovery consumer; this module executes none of them twice.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Recovery

noncomputable section

open Execution

/-- Original stream 0 followed by stream 1, each in the real decoder's bit order. -/
def pairedInput {ctx : RuntimeCtx .quantum} (original : Sampling.Parameters ctx) :
    CInputRef ctx (.fixedVector (260 + 260) (.finite 2)) :=
  .fixedVector (Fin.addCases
    (fun position => .storage (original.results.cells (0, position.rev)).toCStorageRef)
    (fun position => .storage (original.results.cells (1, position.rev)).toCStorageRef))

lemma pairedInput_first {ctx : RuntimeCtx .quantum} (original : Sampling.Parameters ctx)
    (store : Store ctx) (position : Fin 260) :
    (store.read (pairedInput original)).get (position.castAdd 260) =
      store.read (.storage (original.results.cells (0, position.rev)).toCStorageRef) := by
  change store.read (Fin.addCases _ _ (position.castAdd 260)) = _
  rw [Fin.addCases_left]

lemma pairedInput_second {ctx : RuntimeCtx .quantum} (original : Sampling.Parameters ctx)
    (store : Store ctx) (position : Fin 260) :
    (store.read (pairedInput original)).get (position.natAdd 260) =
      store.read (.storage (original.results.cells (1, position.rev)).toCStorageRef) := by
  change store.read (Fin.addCases _ _ (position.natAdd 260)) = _
  rw [Fin.addCases_right]

end

end Recovery

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
