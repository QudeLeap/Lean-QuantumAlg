/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Stream

/-! # Contiguous positions of each original mathematical source stream -/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

/-- The second source follows the first source; each retains its original chronological offset. -/
lemma window_source_streamPositions_val {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
    (ports : Ports ctx totalBits active) (index : Fin active) :
    (streamPositions ports index).val =
      (if ports.stream.val = 0 then ports.start else totalBits + ports.start) + index.val := by
  by_cases first : ports.stream.val = 0
  · simp [streamPositions, first, Ports.position]
  · simp [streamPositions, first, Ports.position, Nat.add_left_comm, Nat.add_comm]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
