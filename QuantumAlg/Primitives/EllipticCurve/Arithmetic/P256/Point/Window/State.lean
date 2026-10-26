/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Transport
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.State

/-!
# Original arithmetic input coverage under either physical stream placement

The source labels retain the same three original words and initialized pool.
Only the C/W source roles change. The other stream may have either value and
remain coherently correlated with every original system and Reference.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

def sourceState (stream : Fin 2) (state : Raw) : Frame.Raw :=
  ((streamPlacement stream).grouping state).1

lemma sourceState_data (stream : Fin 2) (state : Raw) :
    (sourceState stream state).1 = state.1.1 := by
  unfold sourceState
  rw [streamPlacement_grouping]
  split <;> rfl

lemma sourceState_address (stream : Fin 2) (state : Raw) :
    ((streamPlacement stream).grouping state).2 = state.2 := by
  rw [streamPlacement_grouping]
  split <;> rfl

lemma sourceState_word (stream : Fin 2) (port : WordPort) (state : Raw) :
    port.value (sourceState stream state) = port.value state.1 := by
  unfold sourceState
  rw [streamPlacement_grouping]
  split <;> cases port <;> rfl

lemma sourceState_cleanPool (stream : Fin 2) (state : Raw) :
    Frame.CleanPool (sourceState stream state) ↔ Frame.CleanPool state.1 := by
  change (sourceState stream state).1.1.2 = (0, (0, false)) ↔
    state.1.1.1.2 = (0, (0, false))
  rw [sourceState_data]

lemma streamInput_sourceState (stream : Fin 2) (state : Raw) :
    streamInput stream (sourceState stream state) state.2 = state := by
  apply (streamPlacement stream).grouping.injective
  rw [streamInput_grouping]
  exact Prod.ext rfl (sourceState_address stream state).symm

/-- All original inputs with the actual clean pool have the complete arithmetic coordinates. -/
lemma state_eq_arithmeticInput (stream : Fin 2) (ports : PortAssignment) (state : Raw)
    (clean : Frame.CleanPool state.1) :
    state = streamInput stream (Native.arithmeticState ports
      (ports.source.value (sourceState stream state))
      (ports.target.value (sourceState stream state))
      (ports.multiplier.value (sourceState stream state))
      ((Placement.layout ports).grouping (sourceState stream state)).2.2) state.2 :=
  (streamInput_sourceState stream state).symm.trans
    (congrArg (fun initial => streamInput stream initial state.2)
      (Native.state_eq_arithmeticState ports (sourceState stream state)
        ((sourceState_cleanPool stream state).mpr clean)))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
