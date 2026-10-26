/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word16Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word16State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word16Step0 :
    word16Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word16State1 := by decide +kernel

private def word16Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word16State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word16Step1 :
    word16Chunk1.foldl (fun acc a => a.applyPacked acc)
      word16State1 = word16State2 := by decide +kernel

private def word16Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word16State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word16Step2 :
    word16Chunk2.foldl (fun acc a => a.applyPacked acc)
      word16State2 = word16State3 := by decide +kernel

private def word16Chunk3 : List Letter := [.s, .s, .s, .t, .h, .s, .t, .h]
private def word16State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word16Step3 :
    word16Chunk3.foldl (fun acc a => a.applyPacked acc)
      word16State3 = word16State4 := by decide +kernel

private def word16Chunk4 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word16State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word16Step4 :
    word16Chunk4.foldl (fun acc a => a.applyPacked acc)
      word16State4 = word16State5 := by decide +kernel

private def word16Chunk5 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word16State6 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word16Step5 :
    word16Chunk5.foldl (fun acc a => a.applyPacked acc)
      word16State5 = word16State6 := by decide +kernel

private def word16Chunk6 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word16State7 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word16Step6 :
    word16Chunk6.foldl (fun acc a => a.applyPacked acc)
      word16State6 = word16State7 := by decide +kernel

private def word16Chunk7 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word16State8 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word16Step7 :
    word16Chunk7.foldl (fun acc a => a.applyPacked acc)
      word16State7 = word16State8 := by decide +kernel

private def word16Chunk8 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word16State9 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((17 : Dyadic) * half ^ 5),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((13 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word16Step8 :
    word16Chunk8.foldl (fun acc a => a.applyPacked acc)
      word16State8 = word16State9 := by decide +kernel

private def word16Chunk9 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word16State10 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 6),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((21 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 6),
        ((37 : Dyadic) * half ^ 6)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((-11 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-17 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word16Step9 :
    word16Chunk9.foldl (fun acc a => a.applyPacked acc)
      word16State9 = word16State10 := by decide +kernel

private def word16Chunk10 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word16State11 : PackedMat2 :=
    ⟨⟨⟨((-93 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 6)⟩,
       ⟨((3 : Dyadic) * half ^ 7),
        ((15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 7),
        ((31 : Dyadic) * half ^ 7)⟩,
       ⟨((45 : Dyadic) * half ^ 7),
        ((15 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 7),
        ((21 : Dyadic) * half ^ 6)⟩,
       ⟨((61 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-17 : Dyadic) * half ^ 7),
        ((45 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word16Step10 :
    word16Chunk10.foldl (fun acc a => a.applyPacked acc)
      word16State10 = word16State11 := by decide +kernel

private def word16Chunk11 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word16State12 : PackedMat2 :=
    ⟨⟨⟨((61 : Dyadic) * half ^ 7),
        ((-35 : Dyadic) * half ^ 8)⟩,
       ⟨((-59 : Dyadic) * half ^ 7),
        ((-27 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-59 : Dyadic) * half ^ 7)⟩,
       ⟨((35 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-39 : Dyadic) * half ^ 8)⟩,
       ⟨((29 : Dyadic) * half ^ 6),
        ((-31 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((-15 : Dyadic) * half ^ 5)⟩,
       ⟨((-31 : Dyadic) * half ^ 7),
        ((1 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word16Step11 :
    word16Chunk11.foldl (fun acc a => a.applyPacked acc)
      word16State11 = word16State12 := by decide +kernel

private def word16Chunk12 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word16State13 : PackedMat2 :=
    ⟨⟨⟨((5 : Dyadic) * half ^ 6),
        ((31 : Dyadic) * half ^ 9)⟩,
       ⟨((-1 : Dyadic) * half ^ 8),
        ((-155 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-107 : Dyadic) * half ^ 7),
        ((25 : Dyadic) * half ^ 9)⟩,
       ⟨((-61 : Dyadic) * half ^ 8),
        ((-75 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-25 : Dyadic) * half ^ 8),
        ((-275 : Dyadic) * half ^ 9)⟩,
       ⟨((25 : Dyadic) * half ^ 7),
        ((-153 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((31 : Dyadic) * half ^ 7),
        ((-19 : Dyadic) * half ^ 9)⟩,
       ⟨((-93 : Dyadic) * half ^ 8),
        ((-21 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word16Step12 :
    word16Chunk12.foldl (fun acc a => a.applyPacked acc)
      word16State12 = word16State13 := by decide +kernel

private def word16Chunk13 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word16State14 : PackedMat2 :=
    ⟨⟨⟨((-99 : Dyadic) * half ^ 9),
        ((-375 : Dyadic) * half ^ 10)⟩,
       ⟨((-31 : Dyadic) * half ^ 6),
        ((63 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 7),
        ((233 : Dyadic) * half ^ 10)⟩,
       ⟨((-19 : Dyadic) * half ^ 9),
        ((-389 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((19 : Dyadic) * half ^ 9),
        ((389 : Dyadic) * half ^ 10)⟩,
       ⟨((31 : Dyadic) * half ^ 7),
        ((-233 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 6),
        ((63 : Dyadic) * half ^ 10)⟩,
       ⟨((-99 : Dyadic) * half ^ 9),
        ((-375 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word16Step13 :
    word16Chunk13.foldl (fun acc a => a.applyPacked acc)
      word16State13 = word16State14 := by decide +kernel

private def word16Chunk14 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word16State15 : PackedMat2 :=
    ⟨⟨⟨((147 : Dyadic) * half ^ 10),
        ((425 : Dyadic) * half ^ 10)⟩,
       ⟨((117 : Dyadic) * half ^ 10),
        ((-509 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((103 : Dyadic) * half ^ 9),
        ((57 : Dyadic) * half ^ 10)⟩,
       ⟨((-141 : Dyadic) * half ^ 9),
        ((13 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((109 : Dyadic) * half ^ 10),
        ((-19 : Dyadic) * half ^ 9)⟩,
       ⟨((5 : Dyadic) * half ^ 10),
        ((61 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((21 : Dyadic) * half ^ 8),
        ((-33 : Dyadic) * half ^ 8)⟩,
       ⟨((-467 : Dyadic) * half ^ 9),
        ((-15 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word16Step14 :
    word16Chunk14.foldl (fun acc a => a.applyPacked acc)
      word16State14 = word16State15 := by decide +kernel

private def word16Chunk15 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word16State16 : PackedMat2 :=
    ⟨⟨⟨((451 : Dyadic) * half ^ 11),
        ((177 : Dyadic) * half ^ 9)⟩,
       ⟨((-665 : Dyadic) * half ^ 11),
        ((599 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((279 : Dyadic) * half ^ 11),
        ((663 : Dyadic) * half ^ 11)⟩,
       ⟨((163 : Dyadic) * half ^ 11),
        ((-325 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-279 : Dyadic) * half ^ 11),
        ((-663 : Dyadic) * half ^ 11)⟩,
       ⟨((163 : Dyadic) * half ^ 11),
        ((-325 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((451 : Dyadic) * half ^ 11),
        ((177 : Dyadic) * half ^ 9)⟩,
       ⟨((665 : Dyadic) * half ^ 11),
        ((-599 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word16Step15 :
    word16Chunk15.foldl (fun acc a => a.applyPacked acc)
      word16State15 = word16State16 := by decide +kernel

private def word16Chunk16 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word16State17 : PackedMat2 :=
    ⟨⟨⟨((1047 : Dyadic) * half ^ 11),
        ((73 : Dyadic) * half ^ 12)⟩,
       ⟨((1481 : Dyadic) * half ^ 11),
        ((101 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 8),
        ((259 : Dyadic) * half ^ 10)⟩,
       ⟨((-565 : Dyadic) * half ^ 11),
        ((67 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 4),
        ((493 : Dyadic) * half ^ 12)⟩,
       ⟨((-163 : Dyadic) * half ^ 9),
        ((637 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 10),
        ((217 : Dyadic) * half ^ 11)⟩,
       ⟨((87 : Dyadic) * half ^ 11),
        ((79 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word16Step16 :
    word16Chunk16.foldl (fun acc a => a.applyPacked acc)
      word16State16 = word16State17 := by decide +kernel

private def word16Chunk17 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word16State18 : PackedMat2 :=
    ⟨⟨⟨((-1079 : Dyadic) * half ^ 11),
        ((-115 : Dyadic) * half ^ 13)⟩,
       ⟨((-999 : Dyadic) * half ^ 12),
        ((3137 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1035 : Dyadic) * half ^ 12),
        ((-377 : Dyadic) * half ^ 13)⟩,
       ⟨((77 : Dyadic) * half ^ 8),
        ((2659 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((77 : Dyadic) * half ^ 8),
        ((2659 : Dyadic) * half ^ 13)⟩,
       ⟨((1035 : Dyadic) * half ^ 12),
        ((-377 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((999 : Dyadic) * half ^ 12),
        ((-3137 : Dyadic) * half ^ 13)⟩,
       ⟨((1079 : Dyadic) * half ^ 11),
        ((115 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word16Step17 :
    word16Chunk17.foldl (fun acc a => a.applyPacked acc)
      word16State17 = word16State18 := by decide +kernel

private def word16Chunk18 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word16State19 : PackedMat2 :=
    ⟨⟨⟨((2763 : Dyadic) * half ^ 13),
        ((-761 : Dyadic) * half ^ 13)⟩,
       ⟨((1387 : Dyadic) * half ^ 13),
        ((-3393 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1393 : Dyadic) * half ^ 12),
        ((-351 : Dyadic) * half ^ 10)⟩,
       ⟨((1551 : Dyadic) * half ^ 12),
        ((-327 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((3135 : Dyadic) * half ^ 13),
        ((-79 : Dyadic) * half ^ 12)⟩,
       ⟨((2481 : Dyadic) * half ^ 13),
        ((23 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-2077 : Dyadic) * half ^ 12),
        ((2075 : Dyadic) * half ^ 13)⟩,
       ⟨((329 : Dyadic) * half ^ 10),
        ((43 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word16Step18 :
    word16Chunk18.foldl (fun acc a => a.applyPacked acc)
      word16State18 = word16State19 := by decide +kernel

private def word16Chunk19 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word16State20 : PackedMat2 :=
    ⟨⟨⟨((-6011 : Dyadic) * half ^ 14),
        ((6483 : Dyadic) * half ^ 14)⟩,
       ⟨((-1237 : Dyadic) * half ^ 14),
        ((1717 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-7331 : Dyadic) * half ^ 14),
        ((-1463 : Dyadic) * half ^ 12)⟩,
       ⟨((-677 : Dyadic) * half ^ 14),
        ((-467 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-7331 : Dyadic) * half ^ 14),
        ((-1463 : Dyadic) * half ^ 12)⟩,
       ⟨((677 : Dyadic) * half ^ 14),
        ((467 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((6011 : Dyadic) * half ^ 14),
        ((-6483 : Dyadic) * half ^ 14)⟩,
       ⟨((-1237 : Dyadic) * half ^ 14),
        ((1717 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word16Step19 :
    word16Chunk19.foldl (fun acc a => a.applyPacked acc)
      word16State19 = word16State20 := by decide +kernel

private def word16Chunk20 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word16State21 : PackedMat2 :=
    ⟨⟨⟨((1971 : Dyadic) * half ^ 13),
        ((-13449 : Dyadic) * half ^ 15)⟩,
       ⟨((-283 : Dyadic) * half ^ 11),
        ((1919 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-1309 : Dyadic) * half ^ 11),
        ((-405 : Dyadic) * half ^ 12)⟩,
       ⟨((-5657 : Dyadic) * half ^ 14),
        ((-2071 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-451 : Dyadic) * half ^ 14),
        ((4815 : Dyadic) * half ^ 15)⟩,
       ⟨((-3691 : Dyadic) * half ^ 14),
        ((-16129 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-1921 : Dyadic) * half ^ 12),
        ((3103 : Dyadic) * half ^ 14)⟩,
       ⟨((5765 : Dyadic) * half ^ 14),
        ((-839 : Dyadic) * half ^ 14)⟩⟩⟩
private lemma word16Step20 :
    word16Chunk20.foldl (fun acc a => a.applyPacked acc)
      word16State20 = word16State21 := by decide +kernel

private def word16Chunk21 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word16State22 : PackedMat2 :=
    ⟨⟨⟨((-3777 : Dyadic) * half ^ 15),
        ((6363 : Dyadic) * half ^ 15)⟩,
       ⟨((-201 : Dyadic) * half ^ 8),
        ((989 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-2291 : Dyadic) * half ^ 13),
        ((-6591 : Dyadic) * half ^ 16)⟩,
       ⟨((-2351 : Dyadic) * half ^ 14),
        ((-19023 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((777 : Dyadic) * half ^ 12),
        ((-2231 : Dyadic) * half ^ 15)⟩,
       ⟨((12807 : Dyadic) * half ^ 15),
        ((6933 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-4385 : Dyadic) * half ^ 15),
        ((-21951 : Dyadic) * half ^ 16)⟩,
       ⟨((8341 : Dyadic) * half ^ 15),
        ((-29505 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word16Step21 :
    word16Chunk21.foldl (fun acc a => a.applyPacked acc)
      word16State21 = word16State22 := by decide +kernel

private def word16Chunk22 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word16State23 : PackedMat2 :=
    ⟨⟨⟨((-1117 : Dyadic) * half ^ 12),
        ((3317 : Dyadic) * half ^ 13)⟩,
       ⟨((20173 : Dyadic) * half ^ 16),
        ((-10079 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-267 : Dyadic) * half ^ 11),
        ((-13175 : Dyadic) * half ^ 17)⟩,
       ⟨((-13323 : Dyadic) * half ^ 15),
        ((-46633 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-16729 : Dyadic) * half ^ 16),
        ((-9051 : Dyadic) * half ^ 16)⟩,
       ⟨((-1869 : Dyadic) * half ^ 12),
        ((-17595 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((36615 : Dyadic) * half ^ 16),
        ((-38045 : Dyadic) * half ^ 17)⟩,
       ⟨((-16457 : Dyadic) * half ^ 16),
        ((-2301 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word16Step22 :
    word16Chunk22.foldl (fun acc a => a.applyPacked acc)
      word16State22 = word16State23 := by decide +kernel

private def word16Chunk23 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word16State24 : PackedMat2 :=
    ⟨⟨⟨((17585 : Dyadic) * half ^ 17),
        ((-89061 : Dyadic) * half ^ 18)⟩,
       ⟨((-12873 : Dyadic) * half ^ 15),
        ((40341 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((44267 : Dyadic) * half ^ 16),
        ((39865 : Dyadic) * half ^ 18)⟩,
       ⟨((-28259 : Dyadic) * half ^ 17),
        ((-4033 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((28259 : Dyadic) * half ^ 17),
        ((4033 : Dyadic) * half ^ 18)⟩,
       ⟨((-44267 : Dyadic) * half ^ 16),
        ((-39865 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-12873 : Dyadic) * half ^ 15),
        ((40341 : Dyadic) * half ^ 18)⟩,
       ⟨((17585 : Dyadic) * half ^ 17),
        ((-89061 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word16Step23 :
    word16Chunk23.foldl (fun acc a => a.applyPacked acc)
      word16State23 = word16State24 := by decide +kernel

private def word16Chunk24 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word16State25 : PackedMat2 :=
    ⟨⟨⟨((-55485 : Dyadic) * half ^ 18),
        ((-32723 : Dyadic) * half ^ 18)⟩,
       ⟨((35977 : Dyadic) * half ^ 18),
        ((-154419 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((10941 : Dyadic) * half ^ 16),
        ((73597 : Dyadic) * half ^ 18)⟩,
       ⟨((2475 : Dyadic) * half ^ 15),
        ((6553 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((99809 : Dyadic) * half ^ 18),
        ((15891 : Dyadic) * half ^ 17)⟩,
       ⟨((47385 : Dyadic) * half ^ 18),
        ((5991 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((93571 : Dyadic) * half ^ 17),
        ((4877 : Dyadic) * half ^ 17)⟩,
       ⟨((-3803 : Dyadic) * half ^ 13),
        ((45731 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word16Step24 :
    word16Chunk24.foldl (fun acc a => a.applyPacked acc)
      word16State24 = word16State25 := by decide +kernel

private def word16Chunk25 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word16State26 : PackedMat2 :=
    ⟨⟨⟨((-325989 : Dyadic) * half ^ 19),
        ((12495 : Dyadic) * half ^ 16)⟩,
       ⟨((-41395 : Dyadic) * half ^ 19),
        ((-109629 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((245469 : Dyadic) * half ^ 19),
        ((8359 : Dyadic) * half ^ 17)⟩,
       ⟨((203321 : Dyadic) * half ^ 19),
        ((97581 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((64145 : Dyadic) * half ^ 19),
        ((-10537 : Dyadic) * half ^ 18)⟩,
       ⟨((131017 : Dyadic) * half ^ 19),
        ((224395 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((209589 : Dyadic) * half ^ 19),
        ((-142297 : Dyadic) * half ^ 19)⟩,
       ⟨((9669 : Dyadic) * half ^ 19),
        ((45923 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word16Step25 :
    word16Chunk25.foldl (fun acc a => a.applyPacked acc)
      word16State25 = word16State26 := by decide +kernel

private def word16Chunk26 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word16State27 : PackedMat2 :=
    ⟨⟨⟨((-485471 : Dyadic) * half ^ 20),
        ((65401 : Dyadic) * half ^ 18)⟩,
       ⟨((-112765 : Dyadic) * half ^ 20),
        ((-122651 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((94899 : Dyadic) * half ^ 20),
        ((-42217 : Dyadic) * half ^ 19)⟩,
       ⟨((218895 : Dyadic) * half ^ 20),
        ((553613 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((94899 : Dyadic) * half ^ 20),
        ((-42217 : Dyadic) * half ^ 19)⟩,
       ⟨((-218895 : Dyadic) * half ^ 20),
        ((-553613 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((485471 : Dyadic) * half ^ 20),
        ((-65401 : Dyadic) * half ^ 18)⟩,
       ⟨((-112765 : Dyadic) * half ^ 20),
        ((-122651 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word16Step26 :
    word16Chunk26.foldl (fun acc a => a.applyPacked acc)
      word16State26 = word16State27 := by decide +kernel

private def word16Chunk27 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word16State28 : PackedMat2 :=
    ⟨⟨⟨((-1037 : Dyadic) * half ^ 20),
        ((-212409 : Dyadic) * half ^ 20)⟩,
       ⟨((-74997 : Dyadic) * half ^ 17),
        ((-4029 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-386009 : Dyadic) * half ^ 20),
        ((-272361 : Dyadic) * half ^ 21)⟩,
       ⟨((670539 : Dyadic) * half ^ 20),
        ((-164657 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((13463 : Dyadic) * half ^ 18),
        ((264137 : Dyadic) * half ^ 19)⟩,
       ⟨((-218509 : Dyadic) * half ^ 20),
        ((142265 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-52095 : Dyadic) * half ^ 18),
        ((598939 : Dyadic) * half ^ 21)⟩,
       ⟨((108219 : Dyadic) * half ^ 19),
        ((601013 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word16Step27 :
    word16Chunk27.foldl (fun acc a => a.applyPacked acc)
      word16State27 = word16State28 := by decide +kernel

private def word16Chunk28 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word16State29 : PackedMat2 :=
    ⟨⟨⟨((845697 : Dyadic) * half ^ 21),
        ((-158673 : Dyadic) * half ^ 22)⟩,
       ⟨((-12347 : Dyadic) * half ^ 16),
        ((-1897131 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-85731 : Dyadic) * half ^ 19),
        ((-599303 : Dyadic) * half ^ 22)⟩,
       ⟨((-549629 : Dyadic) * half ^ 21),
        ((1493535 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((549629 : Dyadic) * half ^ 21),
        ((-1493535 : Dyadic) * half ^ 22)⟩,
       ⟨((85731 : Dyadic) * half ^ 19),
        ((599303 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-12347 : Dyadic) * half ^ 16),
        ((-1897131 : Dyadic) * half ^ 22)⟩,
       ⟨((845697 : Dyadic) * half ^ 21),
        ((-158673 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word16Step28 :
    word16Chunk28.foldl (fun acc a => a.applyPacked acc)
      word16State28 = word16State29 := by decide +kernel

private def word16Chunk29 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word16State30 : PackedMat2 :=
    ⟨⟨⟨((-202497 : Dyadic) * half ^ 20),
        ((1897615 : Dyadic) * half ^ 22)⟩,
       ⟨((-749275 : Dyadic) * half ^ 21),
        ((-7041 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-918903 : Dyadic) * half ^ 22),
        ((-427523 : Dyadic) * half ^ 20)⟩,
       ⟨((122709 : Dyadic) * half ^ 22),
        ((-38999 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-918903 : Dyadic) * half ^ 22),
        ((-427523 : Dyadic) * half ^ 20)⟩,
       ⟨((-122709 : Dyadic) * half ^ 22),
        ((38999 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((202497 : Dyadic) * half ^ 20),
        ((-1897615 : Dyadic) * half ^ 22)⟩,
       ⟨((-749275 : Dyadic) * half ^ 21),
        ((-7041 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word16Step29 :
    word16Chunk29.foldl (fun acc a => a.applyPacked acc)
      word16State29 = word16State30 := by decide +kernel

private def word16Chunk30 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word16State31 : PackedMat2 :=
    ⟨⟨⟨((3148209 : Dyadic) * half ^ 23),
        ((-255747 : Dyadic) * half ^ 20)⟩,
       ⟨((4892089 : Dyadic) * half ^ 23),
        ((1169607 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-2215693 : Dyadic) * half ^ 23),
        ((1468989 : Dyadic) * half ^ 23)⟩,
       ⟨((-1506237 : Dyadic) * half ^ 23),
        ((-1319237 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((2215693 : Dyadic) * half ^ 23),
        ((-1468989 : Dyadic) * half ^ 23)⟩,
       ⟨((-1506237 : Dyadic) * half ^ 23),
        ((-1319237 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((3148209 : Dyadic) * half ^ 23),
        ((-255747 : Dyadic) * half ^ 20)⟩,
       ⟨((-4892089 : Dyadic) * half ^ 23),
        ((-1169607 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word16Step30 :
    word16Chunk30.foldl (fun acc a => a.applyPacked acc)
      word16State30 = word16State31 := by decide +kernel

private def word16Chunk31 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word16State32 : PackedMat2 :=
    ⟨⟨⟨((-5076763 : Dyadic) * half ^ 23),
        ((117637 : Dyadic) * half ^ 24)⟩,
       ⟨((4797443 : Dyadic) * half ^ 23),
        ((2491385 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((665073 : Dyadic) * half ^ 21),
        ((-449671 : Dyadic) * half ^ 21)⟩,
       ⟨((-2138529 : Dyadic) * half ^ 23),
        ((208673 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1108015 : Dyadic) * half ^ 22),
        ((4798821 : Dyadic) * half ^ 24)⟩,
       ⟨((690669 : Dyadic) * half ^ 22),
        ((-521763 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((593437 : Dyadic) * half ^ 22),
        ((4937103 : Dyadic) * half ^ 23)⟩,
       ⟨((1304511 : Dyadic) * half ^ 23),
        ((-34915 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word16Step31 :
    word16Chunk31.foldl (fun acc a => a.applyPacked acc)
      word16State31 = word16State32 := by decide +kernel

private def word16Chunk32 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word16State33 : PackedMat2 :=
    ⟨⟨⟨((-3670049 : Dyadic) * half ^ 23),
        ((-9047543 : Dyadic) * half ^ 25)⟩,
       ⟨((-4723907 : Dyadic) * half ^ 24),
        ((10547215 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-3267801 : Dyadic) * half ^ 23),
        ((4603529 : Dyadic) * half ^ 25)⟩,
       ⟨((-1302459 : Dyadic) * half ^ 24),
        ((-10365811 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-1302459 : Dyadic) * half ^ 24),
        ((-10365811 : Dyadic) * half ^ 25)⟩,
       ⟨((-3267801 : Dyadic) * half ^ 23),
        ((4603529 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((4723907 : Dyadic) * half ^ 24),
        ((-10547215 : Dyadic) * half ^ 25)⟩,
       ⟨((3670049 : Dyadic) * half ^ 23),
        ((9047543 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word16Step32 :
    word16Chunk32.foldl (fun acc a => a.applyPacked acc)
      word16State32 = word16State33 := by decide +kernel

private def word16Chunk33 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word16State34 : PackedMat2 :=
    ⟨⟨⟨((1580517 : Dyadic) * half ^ 24),
        ((-15230277 : Dyadic) * half ^ 25)⟩,
       ⟨((3044129 : Dyadic) * half ^ 24),
        ((-666081 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((15703367 : Dyadic) * half ^ 25),
        ((-44601 : Dyadic) * half ^ 25)⟩,
       ⟨((-16151577 : Dyadic) * half ^ 25),
        ((-5032697 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-15703367 : Dyadic) * half ^ 25),
        ((44601 : Dyadic) * half ^ 25)⟩,
       ⟨((-16151577 : Dyadic) * half ^ 25),
        ((-5032697 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1580517 : Dyadic) * half ^ 24),
        ((-15230277 : Dyadic) * half ^ 25)⟩,
       ⟨((-3044129 : Dyadic) * half ^ 24),
        ((666081 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word16Step33 :
    word16Chunk33.foldl (fun acc a => a.applyPacked acc)
      word16State33 = word16State34 := by decide +kernel

private def word16Chunk34 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word16State35 : PackedMat2 :=
    ⟨⟨⟨((-3868705 : Dyadic) * half ^ 26),
        ((-2205435 : Dyadic) * half ^ 23)⟩,
       ⟨((-4696877 : Dyadic) * half ^ 26),
        ((-12208963 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((7467819 : Dyadic) * half ^ 24),
        ((4309275 : Dyadic) * half ^ 25)⟩,
       ⟨((-18137603 : Dyadic) * half ^ 25),
        ((12140317 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((20758867 : Dyadic) * half ^ 26),
        ((-3201965 : Dyadic) * half ^ 26)⟩,
       ⟨((-3521767 : Dyadic) * half ^ 26),
        ((33073241 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((21030703 : Dyadic) * half ^ 25),
        ((4282791 : Dyadic) * half ^ 26)⟩,
       ⟨((-3387223 : Dyadic) * half ^ 25),
        ((-207043 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word16Step34 :
    word16Chunk34.foldl (fun acc a => a.applyPacked acc)
      word16State34 = word16State35 := by decide +kernel

private def word16Chunk35 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word16State36 : PackedMat2 :=
    ⟨⟨⟨((5685123 : Dyadic) * half ^ 27),
        ((1051113 : Dyadic) * half ^ 24)⟩,
       ⟨((-82575833 : Dyadic) * half ^ 27),
        ((-30958907 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((48815429 : Dyadic) * half ^ 27),
        ((-6686967 : Dyadic) * half ^ 27)⟩,
       ⟨((50283205 : Dyadic) * half ^ 27),
        ((-5662517 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-48815429 : Dyadic) * half ^ 27),
        ((6686967 : Dyadic) * half ^ 27)⟩,
       ⟨((50283205 : Dyadic) * half ^ 27),
        ((-5662517 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((5685123 : Dyadic) * half ^ 27),
        ((1051113 : Dyadic) * half ^ 24)⟩,
       ⟨((82575833 : Dyadic) * half ^ 27),
        ((30958907 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word16Step35 :
    word16Chunk35.foldl (fun acc a => a.applyPacked acc)
      word16State35 = word16State36 := by decide +kernel

private def word16Chunk36 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word16State37 : PackedMat2 :=
    ⟨⟨⟨((23703269 : Dyadic) * half ^ 27),
        ((86193347 : Dyadic) * half ^ 28)⟩,
       ⟨((-8809761 : Dyadic) * half ^ 27),
        ((-74900817 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-642299 : Dyadic) * half ^ 22),
        ((16570115 : Dyadic) * half ^ 25)⟩,
       ⟨((-40576327 : Dyadic) * half ^ 27),
        ((-16695 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((16636895 : Dyadic) * half ^ 25),
        ((20022759 : Dyadic) * half ^ 28)⟩,
       ⟨((-16503335 : Dyadic) * half ^ 25),
        ((61129895 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-40273541 : Dyadic) * half ^ 26),
        ((-16256515 : Dyadic) * half ^ 27)⟩,
       ⟨((5646265 : Dyadic) * half ^ 27),
        ((3723377 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word16Step36 :
    word16Chunk36.foldl (fun acc a => a.applyPacked acc)
      word16State36 = word16State37 := by decide +kernel

private def word16Chunk37 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word16State38 : PackedMat2 :=
    ⟨⟨⟨((66100577 : Dyadic) * half ^ 27),
        ((41243259 : Dyadic) * half ^ 29)⟩,
       ⟨((-27854045 : Dyadic) * half ^ 28),
        ((237117567 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((47130393 : Dyadic) * half ^ 28),
        ((-144516951 : Dyadic) * half ^ 29)⟩,
       ⟨((22920591 : Dyadic) * half ^ 26),
        ((86858773 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((22920591 : Dyadic) * half ^ 26),
        ((86858773 : Dyadic) * half ^ 29)⟩,
       ⟨((47130393 : Dyadic) * half ^ 28),
        ((-144516951 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((27854045 : Dyadic) * half ^ 28),
        ((-237117567 : Dyadic) * half ^ 29)⟩,
       ⟨((-66100577 : Dyadic) * half ^ 27),
        ((-41243259 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word16Step37 :
    word16Chunk37.foldl (fun acc a => a.applyPacked acc)
      word16State37 = word16State38 := by decide +kernel

private def word16Chunk38 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word16State39 : PackedMat2 :=
    ⟨⟨⟨((252105219 : Dyadic) * half ^ 29),
        ((6623719 : Dyadic) * half ^ 27)⟩,
       ⟨((293966627 : Dyadic) * half ^ 29),
        ((12822775 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((29410047 : Dyadic) * half ^ 28),
        ((-12829927 : Dyadic) * half ^ 28)⟩,
       ⟨((35294333 : Dyadic) * half ^ 26),
        ((-125111887 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-29410047 : Dyadic) * half ^ 28),
        ((12829927 : Dyadic) * half ^ 28)⟩,
       ⟨((35294333 : Dyadic) * half ^ 26),
        ((-125111887 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((252105219 : Dyadic) * half ^ 29),
        ((6623719 : Dyadic) * half ^ 27)⟩,
       ⟨((-293966627 : Dyadic) * half ^ 29),
        ((-12822775 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word16Step38 :
    word16Chunk38.foldl (fun acc a => a.applyPacked acc)
      word16State38 = word16State39 := by decide +kernel

private def word16Chunk39 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word16State40 : PackedMat2 :=
    ⟨⟨⟨((-721611203 : Dyadic) * half ^ 30),
        ((-38240495 : Dyadic) * half ^ 30)⟩,
       ⟨((-63556073 : Dyadic) * half ^ 30),
        ((183767989 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-317810049 : Dyadic) * half ^ 30),
        ((2259219 : Dyadic) * half ^ 27)⟩,
       ⟨((-503383387 : Dyadic) * half ^ 30),
        ((-2996511 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((21070263 : Dyadic) * half ^ 30),
        ((92786669 : Dyadic) * half ^ 30)⟩,
       ⟨((-15077241 : Dyadic) * half ^ 30),
        ((205298359 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((405776473 : Dyadic) * half ^ 30),
        ((329027565 : Dyadic) * half ^ 30)⟩,
       ⟨((329295483 : Dyadic) * half ^ 30),
        ((-196291819 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word16Step39 :
    word16Chunk39.foldl (fun acc a => a.applyPacked acc)
      word16State39 = word16State40 := by decide +kernel

private def word16Chunk40 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word16State41 : PackedMat2 :=
    ⟨⟨⟨((-8498795 : Dyadic) * half ^ 29),
        ((-590966925 : Dyadic) * half ^ 30)⟩,
       ⟨((14268997 : Dyadic) * half ^ 30),
        ((-256196643 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((66877209 : Dyadic) * half ^ 30),
        ((-643841103 : Dyadic) * half ^ 31)⟩,
       ⟨((-326549277 : Dyadic) * half ^ 30),
        ((-92725997 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-326549277 : Dyadic) * half ^ 30),
        ((-92725997 : Dyadic) * half ^ 31)⟩,
       ⟨((66877209 : Dyadic) * half ^ 30),
        ((-643841103 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-14268997 : Dyadic) * half ^ 30),
        ((256196643 : Dyadic) * half ^ 30)⟩,
       ⟨((8498795 : Dyadic) * half ^ 29),
        ((590966925 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word16Step40 :
    word16Chunk40.foldl (fun acc a => a.applyPacked acc)
      word16State40 = word16State41 := by decide +kernel

private def word16Chunk41 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word16State42 : PackedMat2 :=
    ⟨⟨⟨((415650277 : Dyadic) * half ^ 31),
        ((-15360421 : Dyadic) * half ^ 25)⟩,
       ⟨((-106927995 : Dyadic) * half ^ 29),
        ((-989330637 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-139824589 : Dyadic) * half ^ 30),
        ((237316599 : Dyadic) * half ^ 32)⟩,
       ⟨((-253237963 : Dyadic) * half ^ 30),
        ((-73631053 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((77736913 : Dyadic) * half ^ 30),
        ((56706687 : Dyadic) * half ^ 30)⟩,
       ⟨((-81842773 : Dyadic) * half ^ 31),
        ((49132819 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-6263693 : Dyadic) * half ^ 31),
        ((-843362257 : Dyadic) * half ^ 32)⟩,
       ⟨((-1972397581 : Dyadic) * half ^ 31),
        ((-12061703 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word16Step41 :
    word16Chunk41.foldl (fun acc a => a.applyPacked acc)
      word16State41 = word16State42 := by decide +kernel

private def word16Chunk42 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word16State43 : PackedMat2 :=
    ⟨⟨⟨((1963414705 : Dyadic) * half ^ 32),
        ((-1406914171 : Dyadic) * half ^ 32)⟩,
       ⟨((-545623639 : Dyadic) * half ^ 32),
        ((-335577835 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1019308805 : Dyadic) * half ^ 31),
        ((376770585 : Dyadic) * half ^ 30)⟩,
       ⟨((-386458035 : Dyadic) * half ^ 31),
        ((637983663 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1019308805 : Dyadic) * half ^ 31),
        ((376770585 : Dyadic) * half ^ 30)⟩,
       ⟨((386458035 : Dyadic) * half ^ 31),
        ((-637983663 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1963414705 : Dyadic) * half ^ 32),
        ((1406914171 : Dyadic) * half ^ 32)⟩,
       ⟨((-545623639 : Dyadic) * half ^ 32),
        ((-335577835 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word16Step42 :
    word16Chunk42.foldl (fun acc a => a.applyPacked acc)
      word16State42 = word16State43 := by decide +kernel

private def word16Chunk43 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word16State44 : PackedMat2 :=
    ⟨⟨⟨((-1620028725 : Dyadic) * half ^ 33),
        ((2201389009 : Dyadic) * half ^ 32)⟩,
       ⟨((-1378519665 : Dyadic) * half ^ 33),
        ((-995291573 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((674733473 : Dyadic) * half ^ 33),
        ((-1993818335 : Dyadic) * half ^ 33)⟩,
       ⟨((3214107677 : Dyadic) * half ^ 33),
        ((552711245 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-674733473 : Dyadic) * half ^ 33),
        ((1993818335 : Dyadic) * half ^ 33)⟩,
       ⟨((3214107677 : Dyadic) * half ^ 33),
        ((552711245 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-1620028725 : Dyadic) * half ^ 33),
        ((2201389009 : Dyadic) * half ^ 32)⟩,
       ⟨((1378519665 : Dyadic) * half ^ 33),
        ((995291573 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word16Step43 :
    word16Chunk43.foldl (fun acc a => a.applyPacked acc)
      word16State43 = word16State44 := by decide +kernel

private def word16Chunk44 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word16State45 : PackedMat2 :=
    ⟨⟨⟨((5200551173 : Dyadic) * half ^ 33),
        ((1319683423 : Dyadic) * half ^ 34)⟩,
       ⟨((-3907637593 : Dyadic) * half ^ 33),
        ((1754571251 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1326153849 : Dyadic) * half ^ 31),
        ((-575583 : Dyadic) * half ^ 28)⟩,
       ⟨((-150823079 : Dyadic) * half ^ 33),
        ((41907621 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-43058787 : Dyadic) * half ^ 29),
        ((-5153792317 : Dyadic) * half ^ 34)⟩,
       ⟨((-40756455 : Dyadic) * half ^ 29),
        ((5455438475 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((108721957 : Dyadic) * half ^ 32),
        ((-4554094383 : Dyadic) * half ^ 33)⟩,
       ⟨((1537127337 : Dyadic) * half ^ 33),
        ((323228395 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word16Step44 :
    word16Chunk44.foldl (fun acc a => a.applyPacked acc)
      word16State44 = word16State45 := by decide +kernel

private def word16Chunk45 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word16State46 : PackedMat2 :=
    ⟨⟨⟨((11297419383 : Dyadic) * half ^ 34),
        ((-4597412723 : Dyadic) * half ^ 35)⟩,
       ⟨((410708451 : Dyadic) * half ^ 33),
        ((-11187726409 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-3019408187 : Dyadic) * half ^ 33),
        ((-8126233239 : Dyadic) * half ^ 35)⟩,
       ⟨((-4549053969 : Dyadic) * half ^ 34),
        ((-2650189889 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-1347052891 : Dyadic) * half ^ 32),
        ((-10587870343 : Dyadic) * half ^ 35)⟩,
       ⟨((-2738021675 : Dyadic) * half ^ 34),
        ((-1489762405 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((3946284783 : Dyadic) * half ^ 33),
        ((-12118836285 : Dyadic) * half ^ 35)⟩,
       ⟨((-3295156843 : Dyadic) * half ^ 34),
        ((-10476002481 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word16Step45 :
    word16Chunk45.foldl (fun acc a => a.applyPacked acc)
      word16State45 = word16State46 := by decide +kernel

private def word16Chunk46 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word16State47 : PackedMat2 :=
    ⟨⟨⟨((-10807041189 : Dyadic) * half ^ 35),
        ((1449668427 : Dyadic) * half ^ 32)⟩,
       ⟨((-2628328701 : Dyadic) * half ^ 35),
        ((-1111085331 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((539423787 : Dyadic) * half ^ 32),
        ((-2693284893 : Dyadic) * half ^ 33)⟩,
       ⟨((-5992081553 : Dyadic) * half ^ 34),
        ((-13850171829 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-539423787 : Dyadic) * half ^ 32),
        ((2693284893 : Dyadic) * half ^ 33)⟩,
       ⟨((-5992081553 : Dyadic) * half ^ 34),
        ((-13850171829 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-10807041189 : Dyadic) * half ^ 35),
        ((1449668427 : Dyadic) * half ^ 32)⟩,
       ⟨((2628328701 : Dyadic) * half ^ 35),
        ((1111085331 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word16Step46 :
    word16Chunk46.foldl (fun acc a => a.applyPacked acc)
      word16State46 = word16State47 := by decide +kernel

private def word16Chunk47 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word16State48 : PackedMat2 :=
    ⟨⟨⟨((21507633237 : Dyadic) * half ^ 36),
        ((2188269045 : Dyadic) * half ^ 36)⟩,
       ⟨((-27235545619 : Dyadic) * half ^ 36),
        ((-2440576557 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-20369157227 : Dyadic) * half ^ 36),
        ((29762909541 : Dyadic) * half ^ 36)⟩,
       ⟨((-20756624661 : Dyadic) * half ^ 36),
        ((-1283445751 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((50298041557 : Dyadic) * half ^ 36),
        ((193733717 : Dyadic) * half ^ 36)⟩,
       ⟨((-9227777525 : Dyadic) * half ^ 36),
        ((321295171 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-7069422159 : Dyadic) * half ^ 36),
        ((-6092897357 : Dyadic) * half ^ 34)⟩,
       ⟨((-2692884069 : Dyadic) * half ^ 36),
        ((-2863956191 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word16Step47 :
    word16Chunk47.foldl (fun acc a => a.applyPacked acc)
      word16State47 = word16State48 := by decide +kernel

private def word16Chunk48 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word16State49 : PackedMat2 :=
    ⟨⟨⟨((16776979601 : Dyadic) * half ^ 36),
        ((47599605513 : Dyadic) * half ^ 37)⟩,
       ⟨((33209726007 : Dyadic) * half ^ 36),
        ((-25557443573 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((32094138913 : Dyadic) * half ^ 36),
        ((-6957598461 : Dyadic) * half ^ 36)⟩,
       ⟨((7780719549 : Dyadic) * half ^ 35),
        ((15961709829 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((11459654145 : Dyadic) * half ^ 35),
        ((-16532699815 : Dyadic) * half ^ 37)⟩,
       ⟨((1125513921 : Dyadic) * half ^ 33),
        ((47655578011 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((36578524543 : Dyadic) * half ^ 36),
        ((-8216373203 : Dyadic) * half ^ 36)⟩,
       ⟨((-5510540485 : Dyadic) * half ^ 35),
        ((-6248338201 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word16Step48 :
    word16Chunk48.foldl (fun acc a => a.applyPacked acc)
      word16State48 = word16State49 := by decide +kernel

private def word16Chunk49 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word16State50 : PackedMat2 :=
    ⟨⟨⟨((46484018419 : Dyadic) * half ^ 37),
        ((45196205853 : Dyadic) * half ^ 38)⟩,
       ⟨((-12170951535 : Dyadic) * half ^ 36),
        ((82095637869 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-46253615621 : Dyadic) * half ^ 37),
        ((-15334747345 : Dyadic) * half ^ 38)⟩,
       ⟨((48613642289 : Dyadic) * half ^ 36),
        ((-8349762299 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((5921127411 : Dyadic) * half ^ 36),
        ((-50973668957 : Dyadic) * half ^ 38)⟩,
       ⟨((3492492523 : Dyadic) * half ^ 37),
        ((143480900199 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((63645921861 : Dyadic) * half ^ 37),
        ((22142115349 : Dyadic) * half ^ 38)⟩,
       ⟨((-2306214501 : Dyadic) * half ^ 34),
        ((70825921489 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word16Step49 :
    word16Chunk49.foldl (fun acc a => a.applyPacked acc)
      word16State49 = word16State50 := by decide +kernel

private def word16Chunk50 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word16State51 : PackedMat2 :=
    ⟨⟨⟨((707723033 : Dyadic) * half ^ 35),
        ((-5141396861 : Dyadic) * half ^ 36)⟩,
       ⟨((28962390991 : Dyadic) * half ^ 35),
        ((-11553539483 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-7982143061 : Dyadic) * half ^ 38),
        ((-37300092351 : Dyadic) * half ^ 38)⟩,
       ⟨((-130981251951 : Dyadic) * half ^ 38),
        ((-19053476979 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-28176784665 : Dyadic) * half ^ 37),
        ((-34740848753 : Dyadic) * half ^ 37)⟩,
       ⟨((-4561653843 : Dyadic) * half ^ 36),
        ((61499554445 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((32119126927 : Dyadic) * half ^ 38),
        ((-3708764253 : Dyadic) * half ^ 33)⟩,
       ⟨((9012047961 : Dyadic) * half ^ 38),
        ((14127333979 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word16Step50 :
    word16Chunk50.foldl (fun acc a => a.applyPacked acc)
      word16State50 = word16State51 := by decide +kernel

private def word16Chunk51 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word16State52 : PackedMat2 :=
    ⟨⟨⟨((-403811554767 : Dyadic) * half ^ 39),
        ((-114884577 : Dyadic) * half ^ 35)⟩,
       ⟨((-25427437763 : Dyadic) * half ^ 39),
        ((173833448133 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-175318060679 : Dyadic) * half ^ 39),
        ((22624873401 : Dyadic) * half ^ 39)⟩,
       ⟨((-51750881283 : Dyadic) * half ^ 39),
        ((-73857878429 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((175318060679 : Dyadic) * half ^ 39),
        ((-22624873401 : Dyadic) * half ^ 39)⟩,
       ⟨((-51750881283 : Dyadic) * half ^ 39),
        ((-73857878429 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-403811554767 : Dyadic) * half ^ 39),
        ((-114884577 : Dyadic) * half ^ 35)⟩,
       ⟨((25427437763 : Dyadic) * half ^ 39),
        ((-173833448133 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word16Step51 :
    word16Chunk51.foldl (fun acc a => a.applyPacked acc)
      word16State51 = word16State52 := by decide +kernel

private def word16Chunk52 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word16State53 : PackedMat2 :=
    ⟨⟨⟨((107221362961 : Dyadic) * half ^ 38),
        ((-95953056701 : Dyadic) * half ^ 38)⟩,
       ⟨((-129069851693 : Dyadic) * half ^ 39),
        ((-67250856811 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-3200991273 : Dyadic) * half ^ 39),
        ((61469140527 : Dyadic) * half ^ 40)⟩,
       ⟨((-111615312545 : Dyadic) * half ^ 39),
        ((-117027288855 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((89248214691 : Dyadic) * half ^ 39),
        ((13551790159 : Dyadic) * half ^ 37)⟩,
       ⟨((6944768541 : Dyadic) * half ^ 37),
        ((57408151909 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-38548656921 : Dyadic) * half ^ 38),
        ((-343512577615 : Dyadic) * half ^ 40)⟩,
       ⟨((-230454770323 : Dyadic) * half ^ 38),
        ((85372874229 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word16Step52 :
    word16Chunk52.foldl (fun acc a => a.applyPacked acc)
      word16State52 = word16State53 := by decide +kernel

private def word16Chunk53 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word16State54 : PackedMat2 :=
    ⟨⟨⟨((-16121460399 : Dyadic) * half ^ 36),
        ((1028361446859 : Dyadic) * half ^ 41)⟩,
       ⟨((-211948816021 : Dyadic) * half ^ 40),
        ((-524924641335 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-20679136425 : Dyadic) * half ^ 39),
        ((494437533113 : Dyadic) * half ^ 41)⟩,
       ⟨((-249298131821 : Dyadic) * half ^ 40),
        ((-699768339051 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-102665402969 : Dyadic) * half ^ 40),
        ((-290656404671 : Dyadic) * half ^ 41)⟩,
       ⟨((298551468041 : Dyadic) * half ^ 39),
        ((207939858971 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-125859201381 : Dyadic) * half ^ 39),
        ((469892182405 : Dyadic) * half ^ 41)⟩,
       ⟨((-776643044097 : Dyadic) * half ^ 40),
        ((45994550363 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word16Step53 :
    word16Chunk53.foldl (fun acc a => a.applyPacked acc)
      word16State53 = word16State54 := by decide +kernel

private def word16Chunk54 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word16State55 : PackedMat2 :=
    ⟨⟨⟨((1342975665849 : Dyadic) * half ^ 41),
        ((149847156619 : Dyadic) * half ^ 41)⟩,
       ⟨((-1379970943801 : Dyadic) * half ^ 41),
        ((198261977923 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((62215879231 : Dyadic) * half ^ 37),
        ((73579805473 : Dyadic) * half ^ 41)⟩,
       ⟨((8879108049 : Dyadic) * half ^ 39),
        ((-12538320223 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-62215879231 : Dyadic) * half ^ 37),
        ((-73579805473 : Dyadic) * half ^ 41)⟩,
       ⟨((8879108049 : Dyadic) * half ^ 39),
        ((-12538320223 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((1342975665849 : Dyadic) * half ^ 41),
        ((149847156619 : Dyadic) * half ^ 41)⟩,
       ⟨((1379970943801 : Dyadic) * half ^ 41),
        ((-198261977923 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word16Step54 :
    word16Chunk54.foldl (fun acc a => a.applyPacked acc)
      word16State54 = word16State55 := by decide +kernel

private def word16Chunk55 : List Letter := [.h, .t, .h, .s, .t, .h]
private def word16State56 : PackedMat2 :=
    ⟨⟨⟨((2675119324735 : Dyadic) * half ^ 42),
        ((1218293493399 : Dyadic) * half ^ 42)⟩,
       ⟨((1703983189499 : Dyadic) * half ^ 42),
        ((-75315446671 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-1231332487099 : Dyadic) * half ^ 42),
        ((870683551523 : Dyadic) * half ^ 42)⟩,
       ⟨((-434670156997 : Dyadic) * half ^ 42),
        ((38419776949 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((1231332487099 : Dyadic) * half ^ 42),
        ((-870683551523 : Dyadic) * half ^ 42)⟩,
       ⟨((-434670156997 : Dyadic) * half ^ 42),
        ((38419776949 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((2675119324735 : Dyadic) * half ^ 42),
        ((1218293493399 : Dyadic) * half ^ 42)⟩,
       ⟨((-1703983189499 : Dyadic) * half ^ 42),
        ((75315446671 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word16Step55 :
    word16Chunk55.foldl (fun acc a => a.applyPacked acc)
      word16State55 = word16State56 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word16_check : check word16 16 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word16 = word16State56.toMatrix := by
    unfold evalRingPacked
    change ((
      word16Chunk0 ++ word16Chunk1 ++ word16Chunk2 ++ word16Chunk3 ++
      word16Chunk4 ++ word16Chunk5 ++ word16Chunk6 ++ word16Chunk7 ++
      word16Chunk8 ++ word16Chunk9 ++ word16Chunk10 ++ word16Chunk11 ++
      word16Chunk12 ++ word16Chunk13 ++ word16Chunk14 ++ word16Chunk15 ++
      word16Chunk16 ++ word16Chunk17 ++ word16Chunk18 ++ word16Chunk19 ++
      word16Chunk20 ++ word16Chunk21 ++ word16Chunk22 ++ word16Chunk23 ++
      word16Chunk24 ++ word16Chunk25 ++ word16Chunk26 ++ word16Chunk27 ++
      word16Chunk28 ++ word16Chunk29 ++ word16Chunk30 ++ word16Chunk31 ++
      word16Chunk32 ++ word16Chunk33 ++ word16Chunk34 ++ word16Chunk35 ++
      word16Chunk36 ++ word16Chunk37 ++ word16Chunk38 ++ word16Chunk39 ++
      word16Chunk40 ++ word16Chunk41 ++ word16Chunk42 ++ word16Chunk43 ++
      word16Chunk44 ++ word16Chunk45 ++ word16Chunk46 ++ word16Chunk47 ++
      word16Chunk48 ++ word16Chunk49 ++ word16Chunk50 ++ word16Chunk51 ++
      word16Chunk52 ++ word16Chunk53 ++ word16Chunk54 ++ word16Chunk55
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word16Step0, word16Step1, word16Step2, word16Step3, word16Step4,
      word16Step5, word16Step6, word16Step7, word16Step8, word16Step9,
      word16Step10, word16Step11, word16Step12, word16Step13, word16Step14,
      word16Step15, word16Step16, word16Step17, word16Step18, word16Step19,
      word16Step20, word16Step21, word16Step22, word16Step23, word16Step24,
      word16Step25, word16Step26, word16Step27, word16Step28, word16Step29,
      word16Step30, word16Step31, word16Step32, word16Step33, word16Step34,
      word16Step35, word16Step36, word16Step37, word16Step38, word16Step39,
      word16Step40, word16Step41, word16Step42, word16Step43, word16Step44,
      word16Step45, word16Step46, word16Step47, word16Step48, word16Step49,
      word16Step50, word16Step51, word16Step52, word16Step53, word16Step54,
      word16Step55]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
