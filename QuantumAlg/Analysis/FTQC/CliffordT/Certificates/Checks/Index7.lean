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
private def word7Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word7State1 : PackedMat2 :=
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
private lemma word7Step0 :
    word7Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word7State1 := by decide +kernel

private def word7Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word7State2 : PackedMat2 :=
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
private lemma word7Step1 :
    word7Chunk1.foldl (fun acc a => a.applyPacked acc)
      word7State1 = word7State2 := by decide +kernel

private def word7Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word7State3 : PackedMat2 :=
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
private lemma word7Step2 :
    word7Chunk2.foldl (fun acc a => a.applyPacked acc)
      word7State2 = word7State3 := by decide +kernel

private def word7Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word7State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word7Step3 :
    word7Chunk3.foldl (fun acc a => a.applyPacked acc)
      word7State3 = word7State4 := by decide +kernel

private def word7Chunk4 : List Letter := [.s, .h, .h, .t, .h, .t, .h, .t]
private def word7State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word7Step4 :
    word7Chunk4.foldl (fun acc a => a.applyPacked acc)
      word7State4 = word7State5 := by decide +kernel

private def word7Chunk5 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word7State6 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word7Step5 :
    word7Chunk5.foldl (fun acc a => a.applyPacked acc)
      word7State5 = word7State6 := by decide +kernel

private def word7Chunk6 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word7State7 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((9 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word7Step6 :
    word7Chunk6.foldl (fun acc a => a.applyPacked acc)
      word7State6 = word7State7 := by decide +kernel

private def word7Chunk7 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word7State8 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word7Step7 :
    word7Chunk7.foldl (fun acc a => a.applyPacked acc)
      word7State7 = word7State8 := by decide +kernel

private def word7Chunk8 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word7State9 : PackedMat2 :=
    ⟨⟨⟨((-9 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-17 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((21 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((-19 : Dyadic) * half ^ 5)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word7Step8 :
    word7Chunk8.foldl (fun acc a => a.applyPacked acc)
      word7State8 = word7State9 := by decide +kernel

private def word7Chunk9 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word7State10 : PackedMat2 :=
    ⟨⟨⟨((11 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-15 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 4),
        ((-37 : Dyadic) * half ^ 6)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((-7 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-19 : Dyadic) * half ^ 6)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word7Step9 :
    word7Chunk9.foldl (fun acc a => a.applyPacked acc)
      word7State9 = word7State10 := by decide +kernel

private def word7Chunk10 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word7State11 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 5),
        ((-21 : Dyadic) * half ^ 7)⟩,
       ⟨((7 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 5),
        ((-75 : Dyadic) * half ^ 7)⟩,
       ⟨((-5 : Dyadic) * half ^ 6),
        ((-41 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((75 : Dyadic) * half ^ 7)⟩,
       ⟨((-5 : Dyadic) * half ^ 6),
        ((-41 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((-21 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word7Step10 :
    word7Chunk10.foldl (fun acc a => a.applyPacked acc)
      word7State10 = word7State11 := by decide +kernel

private def word7Chunk11 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word7State12 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 7),
        ((-3 : Dyadic) * half ^ 6)⟩,
       ⟨((-83 : Dyadic) * half ^ 7),
        ((-7 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 7),
        ((55 : Dyadic) * half ^ 7)⟩,
       ⟨((-39 : Dyadic) * half ^ 7),
        ((-15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 7),
        ((55 : Dyadic) * half ^ 7)⟩,
       ⟨((39 : Dyadic) * half ^ 7),
        ((15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 7),
        ((3 : Dyadic) * half ^ 6)⟩,
       ⟨((-83 : Dyadic) * half ^ 7),
        ((-7 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word7Step11 :
    word7Chunk11.foldl (fun acc a => a.applyPacked acc)
      word7State11 = word7State12 := by decide +kernel

private def word7Chunk12 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word7State13 : PackedMat2 :=
    ⟨⟨⟨((31 : Dyadic) * half ^ 8),
        ((7 : Dyadic) * half ^ 5)⟩,
       ⟨((-91 : Dyadic) * half ^ 8),
        ((-93 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((129 : Dyadic) * half ^ 8),
        ((-27 : Dyadic) * half ^ 7)⟩,
       ⟨((-53 : Dyadic) * half ^ 8),
        ((61 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-53 : Dyadic) * half ^ 8),
        ((61 : Dyadic) * half ^ 8)⟩,
       ⟨((129 : Dyadic) * half ^ 8),
        ((-27 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((91 : Dyadic) * half ^ 8),
        ((93 : Dyadic) * half ^ 8)⟩,
       ⟨((-31 : Dyadic) * half ^ 8),
        ((-7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word7Step12 :
    word7Chunk12.foldl (fun acc a => a.applyPacked acc)
      word7State12 = word7State13 := by decide +kernel

private def word7Chunk13 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word7State14 : PackedMat2 :=
    ⟨⟨⟨((-27 : Dyadic) * half ^ 9),
        ((81 : Dyadic) * half ^ 9)⟩,
       ⟨((223 : Dyadic) * half ^ 9),
        ((-17 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((185 : Dyadic) * half ^ 9),
        ((213 : Dyadic) * half ^ 9)⟩,
       ⟨((-53 : Dyadic) * half ^ 9),
        ((65 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((83 : Dyadic) * half ^ 9),
        ((119 : Dyadic) * half ^ 9)⟩,
       ⟨((-343 : Dyadic) * half ^ 9),
        ((-33 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-217 : Dyadic) * half ^ 9),
        ((125 : Dyadic) * half ^ 9)⟩,
       ⟨((-55 : Dyadic) * half ^ 9),
        ((49 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word7Step13 :
    word7Chunk13.foldl (fun acc a => a.applyPacked acc)
      word7State13 = word7State14 := by decide +kernel

private def word7Chunk14 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word7State15 : PackedMat2 :=
    ⟨⟨⟨((159 : Dyadic) * half ^ 9),
        ((179 : Dyadic) * half ^ 10)⟩,
       ⟨((177 : Dyadic) * half ^ 8),
        ((71 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-163 : Dyadic) * half ^ 9),
        ((185 : Dyadic) * half ^ 10)⟩,
       ⟨((-5 : Dyadic) * half ^ 5),
        ((293 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-163 : Dyadic) * half ^ 9),
        ((185 : Dyadic) * half ^ 10)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-293 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-159 : Dyadic) * half ^ 9),
        ((-179 : Dyadic) * half ^ 10)⟩,
       ⟨((177 : Dyadic) * half ^ 8),
        ((71 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word7Step14 :
    word7Chunk14.foldl (fun acc a => a.applyPacked acc)
      word7State14 = word7State15 := by decide +kernel

private def word7Chunk15 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word7State16 : PackedMat2 :=
    ⟨⟨⟨((131 : Dyadic) * half ^ 10),
        ((-255 : Dyadic) * half ^ 11)⟩,
       ⟨((457 : Dyadic) * half ^ 9),
        ((-47 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-289 : Dyadic) * half ^ 10),
        ((-197 : Dyadic) * half ^ 11)⟩,
       ⟨((29 : Dyadic) * half ^ 9),
        ((335 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-69 : Dyadic) * half ^ 10),
        ((231 : Dyadic) * half ^ 11)⟩,
       ⟨((133 : Dyadic) * half ^ 9),
        ((347 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-151 : Dyadic) * half ^ 10),
        ((1045 : Dyadic) * half ^ 11)⟩,
       ⟨((-13 : Dyadic) * half ^ 7),
        ((-783 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word7Step15 :
    word7Chunk15.foldl (fun acc a => a.applyPacked acc)
      word7State15 = word7State16 := by decide +kernel

private def word7Chunk16 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word7State17 : PackedMat2 :=
    ⟨⟨⟨((-1227 : Dyadic) * half ^ 11),
        ((-13 : Dyadic) * half ^ 11)⟩,
       ⟨((373 : Dyadic) * half ^ 11),
        ((885 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((659 : Dyadic) * half ^ 11),
        ((-15 : Dyadic) * half ^ 6)⟩,
       ⟨((177 : Dyadic) * half ^ 11),
        ((-21 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-39 : Dyadic) * half ^ 8),
        ((241 : Dyadic) * half ^ 11)⟩,
       ⟨((81 : Dyadic) * half ^ 8),
        ((-209 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((449 : Dyadic) * half ^ 10),
        ((25 : Dyadic) * half ^ 6)⟩,
       ⟨((109 : Dyadic) * half ^ 8),
        ((-427 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word7Step16 :
    word7Chunk16.foldl (fun acc a => a.applyPacked acc)
      word7State16 = word7State17 := by decide +kernel

private def word7Chunk17 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word7State18 : PackedMat2 :=
    ⟨⟨⟨((-1163 : Dyadic) * half ^ 11),
        ((-1061 : Dyadic) * half ^ 12)⟩,
       ⟨((327 : Dyadic) * half ^ 11),
        ((111 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((595 : Dyadic) * half ^ 10),
        ((-487 : Dyadic) * half ^ 11)⟩,
       ⟨((451 : Dyadic) * half ^ 11),
        ((-327 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-595 : Dyadic) * half ^ 10),
        ((487 : Dyadic) * half ^ 11)⟩,
       ⟨((451 : Dyadic) * half ^ 11),
        ((-327 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1163 : Dyadic) * half ^ 11),
        ((-1061 : Dyadic) * half ^ 12)⟩,
       ⟨((-327 : Dyadic) * half ^ 11),
        ((-111 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word7Step17 :
    word7Chunk17.foldl (fun acc a => a.applyPacked acc)
      word7State17 = word7State18 := by decide +kernel

private def word7Chunk18 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word7State19 : PackedMat2 :=
    ⟨⟨⟨((-4721 : Dyadic) * half ^ 13),
        ((-7 : Dyadic) * half ^ 5)⟩,
       ⟨((-2769 : Dyadic) * half ^ 13),
        ((1625 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((831 : Dyadic) * half ^ 13),
        ((19 : Dyadic) * half ^ 7)⟩,
       ⟨((1603 : Dyadic) * half ^ 13),
        ((-3101 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1603 : Dyadic) * half ^ 13),
        ((3101 : Dyadic) * half ^ 13)⟩,
       ⟨((-831 : Dyadic) * half ^ 13),
        ((-19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-2769 : Dyadic) * half ^ 13),
        ((1625 : Dyadic) * half ^ 13)⟩,
       ⟨((-4721 : Dyadic) * half ^ 13),
        ((-7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word7Step18 :
    word7Chunk18.foldl (fun acc a => a.applyPacked acc)
      word7State18 = word7State19 := by decide +kernel

private def word7Chunk19 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word7State20 : PackedMat2 :=
    ⟨⟨⟨((2979 : Dyadic) * half ^ 13),
        ((-1013 : Dyadic) * half ^ 13)⟩,
       ⟨((-1609 : Dyadic) * half ^ 12),
        ((-847 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((429 : Dyadic) * half ^ 12),
        ((-1123 : Dyadic) * half ^ 13)⟩,
       ⟨((-3037 : Dyadic) * half ^ 13),
        ((2279 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-3037 : Dyadic) * half ^ 13),
        ((2279 : Dyadic) * half ^ 13)⟩,
       ⟨((429 : Dyadic) * half ^ 12),
        ((-1123 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1609 : Dyadic) * half ^ 12),
        ((847 : Dyadic) * half ^ 11)⟩,
       ⟨((-2979 : Dyadic) * half ^ 13),
        ((1013 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word7Step19 :
    word7Chunk19.foldl (fun acc a => a.applyPacked acc)
      word7State19 = word7State20 := by decide +kernel

private def word7Chunk20 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word7State21 : PackedMat2 :=
    ⟨⟨⟨((-1105 : Dyadic) * half ^ 13),
        ((16629 : Dyadic) * half ^ 15)⟩,
       ⟨((-4953 : Dyadic) * half ^ 14),
        ((-6283 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-99 : Dyadic) * half ^ 10),
        ((-9039 : Dyadic) * half ^ 15)⟩,
       ⟨((1015 : Dyadic) * half ^ 14),
        ((-8559 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((8799 : Dyadic) * half ^ 14),
        ((569 : Dyadic) * half ^ 15)⟩,
       ⟨((15 : Dyadic) * half ^ 10),
        ((2599 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((5173 : Dyadic) * half ^ 14),
        ((-7163 : Dyadic) * half ^ 15)⟩,
       ⟨((179 : Dyadic) * half ^ 8),
        ((2743 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word7Step20 :
    word7Chunk20.foldl (fun acc a => a.applyPacked acc)
      word7State20 = word7State21 := by decide +kernel

private def word7Chunk21 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word7State22 : PackedMat2 :=
    ⟨⟨⟨((3895 : Dyadic) * half ^ 13),
        ((20653 : Dyadic) * half ^ 16)⟩,
       ⟨((17935 : Dyadic) * half ^ 15),
        ((-19005 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-371 : Dyadic) * half ^ 12),
        ((-12193 : Dyadic) * half ^ 16)⟩,
       ⟨((-2333 : Dyadic) * half ^ 15),
        ((7333 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-1215 : Dyadic) * half ^ 14),
        ((-5301 : Dyadic) * half ^ 16)⟩,
       ⟨((-9763 : Dyadic) * half ^ 15),
        ((-635 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-103 : Dyadic) * half ^ 12),
        ((-33515 : Dyadic) * half ^ 16)⟩,
       ⟨((-19829 : Dyadic) * half ^ 15),
        ((2355 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word7Step21 :
    word7Chunk21.foldl (fun acc a => a.applyPacked acc)
      word7State21 = word7State22 := by decide +kernel

private def word7Chunk22 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word7State23 : PackedMat2 :=
    ⟨⟨⟨((47105 : Dyadic) * half ^ 16),
        ((-24229 : Dyadic) * half ^ 17)⟩,
       ⟨((2957 : Dyadic) * half ^ 15),
        ((16535 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-23335 : Dyadic) * half ^ 16),
        ((-19491 : Dyadic) * half ^ 17)⟩,
       ⟨((-8679 : Dyadic) * half ^ 15),
        ((-33915 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((26703 : Dyadic) * half ^ 16),
        ((40693 : Dyadic) * half ^ 17)⟩,
       ⟨((-1803 : Dyadic) * half ^ 14),
        ((5977 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-3847 : Dyadic) * half ^ 16),
        ((53019 : Dyadic) * half ^ 17)⟩,
       ⟨((-10191 : Dyadic) * half ^ 15),
        ((41191 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word7Step22 :
    word7Chunk22.foldl (fun acc a => a.applyPacked acc)
      word7State22 = word7State23 := by decide +kernel

private def word7Chunk23 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word7State24 : PackedMat2 :=
    ⟨⟨⟨((34829 : Dyadic) * half ^ 17),
        ((-25679 : Dyadic) * half ^ 16)⟩,
       ⟨((29593 : Dyadic) * half ^ 17),
        ((66167 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-23355 : Dyadic) * half ^ 17),
        ((265 : Dyadic) * half ^ 14)⟩,
       ⟨((-8079 : Dyadic) * half ^ 17),
        ((14831 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((8079 : Dyadic) * half ^ 17),
        ((-14831 : Dyadic) * half ^ 17)⟩,
       ⟨((23355 : Dyadic) * half ^ 17),
        ((-265 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((29593 : Dyadic) * half ^ 17),
        ((66167 : Dyadic) * half ^ 17)⟩,
       ⟨((34829 : Dyadic) * half ^ 17),
        ((-25679 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word7Step23 :
    word7Chunk23.foldl (fun acc a => a.applyPacked acc)
      word7State23 = word7State24 := by decide +kernel

private def word7Chunk24 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word7State25 : PackedMat2 :=
    ⟨⟨⟨((-99449 : Dyadic) * half ^ 17),
        ((1763 : Dyadic) * half ^ 17)⟩,
       ⟨((8189 : Dyadic) * half ^ 16),
        ((-19419 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((8383 : Dyadic) * half ^ 16),
        ((3811 : Dyadic) * half ^ 17)⟩,
       ⟨((-57925 : Dyadic) * half ^ 17),
        ((-12905 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-4547 : Dyadic) * half ^ 16),
        ((-41159 : Dyadic) * half ^ 18)⟩,
       ⟨((4179 : Dyadic) * half ^ 15),
        ((74691 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((37075 : Dyadic) * half ^ 17),
        ((83071 : Dyadic) * half ^ 18)⟩,
       ⟨((-40601 : Dyadic) * half ^ 17),
        ((115827 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word7Step24 :
    word7Chunk24.foldl (fun acc a => a.applyPacked acc)
      word7State24 = word7State25 := by decide +kernel

private def word7Chunk25 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word7State26 : PackedMat2 :=
    ⟨⟨⟨((21135 : Dyadic) * half ^ 18),
        ((-20201 : Dyadic) * half ^ 16)⟩,
       ⟨((18213 : Dyadic) * half ^ 16),
        ((-145 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((24407 : Dyadic) * half ^ 17),
        ((130023 : Dyadic) * half ^ 18)⟩,
       ⟨((-23553 : Dyadic) * half ^ 18),
        ((-16333 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((23553 : Dyadic) * half ^ 18),
        ((16333 : Dyadic) * half ^ 17)⟩,
       ⟨((-24407 : Dyadic) * half ^ 17),
        ((-130023 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((18213 : Dyadic) * half ^ 16),
        ((-145 : Dyadic) * half ^ 9)⟩,
       ⟨((21135 : Dyadic) * half ^ 18),
        ((-20201 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word7Step25 :
    word7Chunk25.foldl (fun acc a => a.applyPacked acc)
      word7State25 = word7State26 := by decide +kernel

private def word7Chunk26 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word7State27 : PackedMat2 :=
    ⟨⟨⟨((183519 : Dyadic) * half ^ 19),
        ((-93371 : Dyadic) * half ^ 20)⟩,
       ⟨((-352643 : Dyadic) * half ^ 19),
        ((-24485 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((39901 : Dyadic) * half ^ 17),
        ((272693 : Dyadic) * half ^ 20)⟩,
       ⟨((78693 : Dyadic) * half ^ 18),
        ((-222523 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((78693 : Dyadic) * half ^ 18),
        ((-222523 : Dyadic) * half ^ 20)⟩,
       ⟨((39901 : Dyadic) * half ^ 17),
        ((272693 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((352643 : Dyadic) * half ^ 19),
        ((24485 : Dyadic) * half ^ 20)⟩,
       ⟨((-183519 : Dyadic) * half ^ 19),
        ((93371 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word7Step26 :
    word7Chunk26.foldl (fun acc a => a.applyPacked acc)
      word7State26 = word7State27 := by decide +kernel

private def word7Chunk27 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word7State28 : PackedMat2 :=
    ⟨⟨⟨((-219133 : Dyadic) * half ^ 20),
        ((739655 : Dyadic) * half ^ 21)⟩,
       ⟨((-78853 : Dyadic) * half ^ 20),
        ((233527 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((99711 : Dyadic) * half ^ 17),
        ((188117 : Dyadic) * half ^ 21)⟩,
       ⟨((145785 : Dyadic) * half ^ 19),
        ((104395 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-145785 : Dyadic) * half ^ 19),
        ((-104395 : Dyadic) * half ^ 21)⟩,
       ⟨((-99711 : Dyadic) * half ^ 17),
        ((-188117 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-78853 : Dyadic) * half ^ 20),
        ((233527 : Dyadic) * half ^ 21)⟩,
       ⟨((-219133 : Dyadic) * half ^ 20),
        ((739655 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word7Step27 :
    word7Chunk27.foldl (fun acc a => a.applyPacked acc)
      word7State27 = word7State28 := by decide +kernel

private def word7Chunk28 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word7State29 : PackedMat2 :=
    ⟨⟨⟨((860369 : Dyadic) * half ^ 21),
        ((-165675 : Dyadic) * half ^ 22)⟩,
       ⟨((-65931 : Dyadic) * half ^ 20),
        ((-507309 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-356517 : Dyadic) * half ^ 21),
        ((1631261 : Dyadic) * half ^ 22)⟩,
       ⟨((694337 : Dyadic) * half ^ 20),
        ((473271 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-356517 : Dyadic) * half ^ 21),
        ((1631261 : Dyadic) * half ^ 22)⟩,
       ⟨((-694337 : Dyadic) * half ^ 20),
        ((-473271 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-860369 : Dyadic) * half ^ 21),
        ((165675 : Dyadic) * half ^ 22)⟩,
       ⟨((-65931 : Dyadic) * half ^ 20),
        ((-507309 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word7Step28 :
    word7Chunk28.foldl (fun acc a => a.applyPacked acc)
      word7State28 = word7State29 := by decide +kernel

private def word7Chunk29 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word7State30 : PackedMat2 :=
    ⟨⟨⟨((974179 : Dyadic) * half ^ 22),
        ((2104673 : Dyadic) * half ^ 23)⟩,
       ⟨((224553 : Dyadic) * half ^ 21),
        ((-1392215 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1708209 : Dyadic) * half ^ 22),
        ((782627 : Dyadic) * half ^ 23)⟩,
       ⟨((1583737 : Dyadic) * half ^ 21),
        ((-27841 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-377393 : Dyadic) * half ^ 22),
        ((-1459265 : Dyadic) * half ^ 23)⟩,
       ⟨((-202617 : Dyadic) * half ^ 21),
        ((4875683 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((356229 : Dyadic) * half ^ 22),
        ((1423285 : Dyadic) * half ^ 23)⟩,
       ⟨((437111 : Dyadic) * half ^ 20),
        ((525073 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word7Step29 :
    word7Chunk29.foldl (fun acc a => a.applyPacked acc)
      word7State29 = word7State30 := by decide +kernel

private def word7Chunk30 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word7State31 : PackedMat2 :=
    ⟨⟨⟨((-1511907 : Dyadic) * half ^ 23),
        ((1684207 : Dyadic) * half ^ 23)⟩,
       ⟨((1290173 : Dyadic) * half ^ 23),
        ((1110129 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1935741 : Dyadic) * half ^ 23),
        ((-597599 : Dyadic) * half ^ 21)⟩,
       ⟨((-761871 : Dyadic) * half ^ 23),
        ((1152781 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1935741 : Dyadic) * half ^ 23),
        ((-597599 : Dyadic) * half ^ 21)⟩,
       ⟨((761871 : Dyadic) * half ^ 23),
        ((-1152781 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((1511907 : Dyadic) * half ^ 23),
        ((-1684207 : Dyadic) * half ^ 23)⟩,
       ⟨((1290173 : Dyadic) * half ^ 23),
        ((1110129 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word7Step30 :
    word7Chunk30.foldl (fun acc a => a.applyPacked acc)
      word7State30 = word7State31 := by decide +kernel

private def word7Chunk31 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word7State32 : PackedMat2 :=
    ⟨⟨⟨((-548265 : Dyadic) * half ^ 21),
        ((-506465 : Dyadic) * half ^ 24)⟩,
       ⟨((170381 : Dyadic) * half ^ 22),
        ((-1068421 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-7267395 : Dyadic) * half ^ 23),
        ((131575 : Dyadic) * half ^ 23)⟩,
       ⟨((732109 : Dyadic) * half ^ 22),
        ((1542131 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((7267395 : Dyadic) * half ^ 23),
        ((-131575 : Dyadic) * half ^ 23)⟩,
       ⟨((732109 : Dyadic) * half ^ 22),
        ((1542131 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-548265 : Dyadic) * half ^ 21),
        ((-506465 : Dyadic) * half ^ 24)⟩,
       ⟨((-170381 : Dyadic) * half ^ 22),
        ((1068421 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word7Step31 :
    word7Chunk31.foldl (fun acc a => a.applyPacked acc)
      word7State31 = word7State32 := by decide +kernel

private def word7Chunk32 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word7State33 : PackedMat2 :=
    ⟨⟨⟨((-415473 : Dyadic) * half ^ 25),
        ((8619177 : Dyadic) * half ^ 25)⟩,
       ⟨((-11128207 : Dyadic) * half ^ 25),
        ((-2814059 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((1365083 : Dyadic) * half ^ 25),
        ((-18610743 : Dyadic) * half ^ 25)⟩,
       ⟨((-6670379 : Dyadic) * half ^ 25),
        ((1260971 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-23654627 : Dyadic) * half ^ 25),
        ((4017731 : Dyadic) * half ^ 25)⟩,
       ⟨((13566859 : Dyadic) * half ^ 25),
        ((331581 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-14247295 : Dyadic) * half ^ 25),
        ((-5356367 : Dyadic) * half ^ 25)⟩,
       ⟨((2991059 : Dyadic) * half ^ 25),
        ((-90185 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word7Step32 :
    word7Chunk32.foldl (fun acc a => a.applyPacked acc)
      word7State32 = word7State33 := by decide +kernel

private def word7Chunk33 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word7State34 : PackedMat2 :=
    ⟨⟨⟨((7432911 : Dyadic) * half ^ 24),
        ((-6699049 : Dyadic) * half ^ 25)⟩,
       ⟨((-2500665 : Dyadic) * half ^ 25),
        ((-3776457 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-15067817 : Dyadic) * half ^ 25),
        ((-6148989 : Dyadic) * half ^ 25)⟩,
       ⟨((81161 : Dyadic) * half ^ 24),
        ((-3863655 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((81161 : Dyadic) * half ^ 24),
        ((-3863655 : Dyadic) * half ^ 23)⟩,
       ⟨((-15067817 : Dyadic) * half ^ 25),
        ((-6148989 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((2500665 : Dyadic) * half ^ 25),
        ((3776457 : Dyadic) * half ^ 25)⟩,
       ⟨((-7432911 : Dyadic) * half ^ 24),
        ((6699049 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word7Step33 :
    word7Chunk33.foldl (fun acc a => a.applyPacked acc)
      word7State33 = word7State34 := by decide +kernel

private def word7Chunk34 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word7State35 : PackedMat2 :=
    ⟨⟨⟨((-803107 : Dyadic) * half ^ 26),
        ((248337 : Dyadic) * half ^ 27)⟩,
       ⟨((-39459535 : Dyadic) * half ^ 26),
        ((-6517855 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((7441801 : Dyadic) * half ^ 24),
        ((-37417997 : Dyadic) * half ^ 27)⟩,
       ⟨((-9810529 : Dyadic) * half ^ 25),
        ((-43669259 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((9810529 : Dyadic) * half ^ 25),
        ((43669259 : Dyadic) * half ^ 27)⟩,
       ⟨((-7441801 : Dyadic) * half ^ 24),
        ((37417997 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-39459535 : Dyadic) * half ^ 26),
        ((-6517855 : Dyadic) * half ^ 27)⟩,
       ⟨((-803107 : Dyadic) * half ^ 26),
        ((248337 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word7Step34 :
    word7Chunk34.foldl (fun acc a => a.applyPacked acc)
      word7State34 = word7State35 := by decide +kernel

private def word7Chunk35 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word7State36 : PackedMat2 :=
    ⟨⟨⟨((42833503 : Dyadic) * half ^ 27),
        ((54299903 : Dyadic) * half ^ 28)⟩,
       ⟨((16611333 : Dyadic) * half ^ 26),
        ((-88816879 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-21180035 : Dyadic) * half ^ 27),
        ((64547239 : Dyadic) * half ^ 28)⟩,
       ⟨((-8518407 : Dyadic) * half ^ 26),
        ((-116922755 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-13093879 : Dyadic) * half ^ 26),
        ((-38216849 : Dyadic) * half ^ 28)⟩,
       ⟨((90734997 : Dyadic) * half ^ 27),
        ((-4143221 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((2157311 : Dyadic) * half ^ 24),
        ((-76056169 : Dyadic) * half ^ 28)⟩,
       ⟨((-71558391 : Dyadic) * half ^ 27),
        ((-9610837 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word7Step35 :
    word7Chunk35.foldl (fun acc a => a.applyPacked acc)
      word7State35 = word7State36 := by decide +kernel

private def word7Chunk36 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word7State37 : PackedMat2 :=
    ⟨⟨⟨((38114051 : Dyadic) * half ^ 28),
        ((18212915 : Dyadic) * half ^ 25)⟩,
       ⟨((-24803341 : Dyadic) * half ^ 28),
        ((14049499 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((114806719 : Dyadic) * half ^ 28),
        ((-7127097 : Dyadic) * half ^ 28)⟩,
       ⟨((-95269287 : Dyadic) * half ^ 28),
        ((42386757 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-114806719 : Dyadic) * half ^ 28),
        ((7127097 : Dyadic) * half ^ 28)⟩,
       ⟨((-95269287 : Dyadic) * half ^ 28),
        ((42386757 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((38114051 : Dyadic) * half ^ 28),
        ((18212915 : Dyadic) * half ^ 25)⟩,
       ⟨((24803341 : Dyadic) * half ^ 28),
        ((-14049499 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word7Step36 :
    word7Chunk36.foldl (fun acc a => a.applyPacked acc)
      word7State36 = word7State37 := by decide +kernel

private def word7Chunk37 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word7State38 : PackedMat2 :=
    ⟨⟨⟨((331988997 : Dyadic) * half ^ 29),
        ((10234115 : Dyadic) * half ^ 26)⟩,
       ⟨((-219100331 : Dyadic) * half ^ 29),
        ((149470719 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((220532325 : Dyadic) * half ^ 29),
        ((-2911535 : Dyadic) * half ^ 27)⟩,
       ⟨((107165337 : Dyadic) * half ^ 29),
        ((75924977 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-107165337 : Dyadic) * half ^ 29),
        ((-75924977 : Dyadic) * half ^ 29)⟩,
       ⟨((-220532325 : Dyadic) * half ^ 29),
        ((2911535 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-219100331 : Dyadic) * half ^ 29),
        ((149470719 : Dyadic) * half ^ 29)⟩,
       ⟨((331988997 : Dyadic) * half ^ 29),
        ((10234115 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word7Step37 :
    word7Chunk37.foldl (fun acc a => a.applyPacked acc)
      word7State37 = word7State38 := by decide +kernel

private def word7Chunk38 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word7State39 : PackedMat2 :=
    ⟨⟨⟨((-122382651 : Dyadic) * half ^ 29),
        ((-59823903 : Dyadic) * half ^ 29)⟩,
       ⟨((217501021 : Dyadic) * half ^ 28),
        ((-2119905 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-45981285 : Dyadic) * half ^ 28),
        ((24424495 : Dyadic) * half ^ 29)⟩,
       ⟨((55024013 : Dyadic) * half ^ 29),
        ((175911189 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((50083921 : Dyadic) * half ^ 27),
        ((-36938557 : Dyadic) * half ^ 30)⟩,
       ⟨((-75743347 : Dyadic) * half ^ 28),
        ((-146986583 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((93742383 : Dyadic) * half ^ 29),
        ((-312619391 : Dyadic) * half ^ 30)⟩,
       ⟨((25905423 : Dyadic) * half ^ 29),
        ((557384693 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word7Step38 :
    word7Chunk38.foldl (fun acc a => a.applyPacked acc)
      word7State38 = word7State39 := by decide +kernel

private def word7Chunk39 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word7State40 : PackedMat2 :=
    ⟨⟨⟨((-53810923 : Dyadic) * half ^ 27),
        ((-321050937 : Dyadic) * half ^ 31)⟩,
       ⟨((-706151089 : Dyadic) * half ^ 30),
        ((-91013833 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((3917257 : Dyadic) * half ^ 29),
        ((-428010145 : Dyadic) * half ^ 31)⟩,
       ⟨((488351143 : Dyadic) * half ^ 30),
        ((-407748905 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-3917257 : Dyadic) * half ^ 29),
        ((428010145 : Dyadic) * half ^ 31)⟩,
       ⟨((488351143 : Dyadic) * half ^ 30),
        ((-407748905 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-53810923 : Dyadic) * half ^ 27),
        ((-321050937 : Dyadic) * half ^ 31)⟩,
       ⟨((706151089 : Dyadic) * half ^ 30),
        ((91013833 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word7Step39 :
    word7Chunk39.foldl (fun acc a => a.applyPacked acc)
      word7State39 = word7State40 := by decide +kernel

private def word7Chunk40 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word7State41 : PackedMat2 :=
    ⟨⟨⟨((1031750541 : Dyadic) * half ^ 31),
        ((73015319 : Dyadic) * half ^ 28)⟩,
       ⟨((-348248205 : Dyadic) * half ^ 31),
        ((-13601405 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-621334829 : Dyadic) * half ^ 31),
        ((315453063 : Dyadic) * half ^ 31)⟩,
       ⟨((-692363769 : Dyadic) * half ^ 31),
        ((806281445 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-245414191 : Dyadic) * half ^ 30),
        ((17757235 : Dyadic) * half ^ 30)⟩,
       ⟨((-280433627 : Dyadic) * half ^ 29),
        ((656849299 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-127420939 : Dyadic) * half ^ 28),
        ((-689999373 : Dyadic) * half ^ 31)⟩,
       ⟨((18609699 : Dyadic) * half ^ 28),
        ((2669931 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word7Step40 :
    word7Chunk40.foldl (fun acc a => a.applyPacked acc)
      word7State40 = word7State41 := by decide +kernel

private def word7Chunk41 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word7State42 : PackedMat2 :=
    ⟨⟨⟨((2007321691 : Dyadic) * half ^ 32),
        ((1431481031 : Dyadic) * half ^ 32)⟩,
       ⟨((1282995129 : Dyadic) * half ^ 32),
        ((-52621869 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((2342637407 : Dyadic) * half ^ 32),
        ((-737616901 : Dyadic) * half ^ 32)⟩,
       ⟨((842350469 : Dyadic) * half ^ 32),
        ((-359330937 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((842350469 : Dyadic) * half ^ 32),
        ((-359330937 : Dyadic) * half ^ 31)⟩,
       ⟨((2342637407 : Dyadic) * half ^ 32),
        ((-737616901 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1282995129 : Dyadic) * half ^ 32),
        ((52621869 : Dyadic) * half ^ 29)⟩,
       ⟨((-2007321691 : Dyadic) * half ^ 32),
        ((-1431481031 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word7Step41 :
    word7Chunk41.foldl (fun acc a => a.applyPacked acc)
      word7State41 = word7State42 := by decide +kernel

private def word7Chunk42 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word7State43 : PackedMat2 :=
    ⟨⟨⟨((2895957263 : Dyadic) * half ^ 33),
        ((-2016747589 : Dyadic) * half ^ 33)⟩,
       ⟨((4285787221 : Dyadic) * half ^ 33),
        ((-120893525 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((2821804995 : Dyadic) * half ^ 33),
        ((1201549167 : Dyadic) * half ^ 33)⟩,
       ⟨((-4719265519 : Dyadic) * half ^ 33),
        ((-698717709 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((2598984585 : Dyadic) * half ^ 33),
        ((3770535257 : Dyadic) * half ^ 33)⟩,
       ⟨((195886251 : Dyadic) * half ^ 33),
        ((474365131 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1049599389 : Dyadic) * half ^ 33),
        ((694914979 : Dyadic) * half ^ 33)⟩,
       ⟨((-2983895789 : Dyadic) * half ^ 33),
        ((1795436121 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word7Step42 :
    word7Chunk42.foldl (fun acc a => a.applyPacked acc)
      word7State42 = word7State43 := by decide +kernel

private def word7Chunk43 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word7State44 : PackedMat2 :=
    ⟨⟨⟨((-225001055 : Dyadic) * half ^ 30),
        ((5260540881 : Dyadic) * half ^ 34)⟩,
       ⟨((-465036033 : Dyadic) * half ^ 32),
        ((1067490465 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((5704075537 : Dyadic) * half ^ 33),
        ((3252092213 : Dyadic) * half ^ 34)⟩,
       ⟨((1461445711 : Dyadic) * half ^ 33),
        ((-5534463941 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((1461445711 : Dyadic) * half ^ 33),
        ((-5534463941 : Dyadic) * half ^ 34)⟩,
       ⟨((5704075537 : Dyadic) * half ^ 33),
        ((3252092213 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((465036033 : Dyadic) * half ^ 32),
        ((-1067490465 : Dyadic) * half ^ 34)⟩,
       ⟨((225001055 : Dyadic) * half ^ 30),
        ((-5260540881 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word7Step43 :
    word7Chunk43.foldl (fun acc a => a.applyPacked acc)
      word7State43 = word7State44 := by decide +kernel

private def word7Chunk44 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word7State45 : PackedMat2 :=
    ⟨⟨⟨((-4763456893 : Dyadic) * half ^ 33),
        ((-1213496037 : Dyadic) * half ^ 34)⟩,
       ⟨((-220672403 : Dyadic) * half ^ 31),
        ((-2394884919 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((4104634317 : Dyadic) * half ^ 33),
        ((-345742165 : Dyadic) * half ^ 33)⟩,
       ⟨((4440660531 : Dyadic) * half ^ 33),
        ((-1614630477 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-923146147 : Dyadic) * half ^ 34),
        ((168013107 : Dyadic) * half ^ 33)⟩,
       ⟨((-2306114807 : Dyadic) * half ^ 34),
        ((16690029 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((3576273801 : Dyadic) * half ^ 34),
        ((-3880767281 : Dyadic) * half ^ 34)⟩,
       ⟨((6003265875 : Dyadic) * half ^ 34),
        ((5646146505 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word7Step44 :
    word7Chunk44.foldl (fun acc a => a.applyPacked acc)
      word7State44 = word7State45 := by decide +kernel

private def word7Chunk45 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word7State46 : PackedMat2 :=
    ⟨⟨⟨((-9388918277 : Dyadic) * half ^ 34),
        ((3525524205 : Dyadic) * half ^ 34)⟩,
       ⟨((-4490239941 : Dyadic) * half ^ 34),
        ((-8911798425 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((4315748115 : Dyadic) * half ^ 34),
        ((-6789515113 : Dyadic) * half ^ 35)⟩,
       ⟨((879241271 : Dyadic) * half ^ 31),
        ((3944270115 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((4315748115 : Dyadic) * half ^ 34),
        ((-6789515113 : Dyadic) * half ^ 35)⟩,
       ⟨((-879241271 : Dyadic) * half ^ 31),
        ((-3944270115 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((9388918277 : Dyadic) * half ^ 34),
        ((-3525524205 : Dyadic) * half ^ 34)⟩,
       ⟨((-4490239941 : Dyadic) * half ^ 34),
        ((-8911798425 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word7Step45 :
    word7Chunk45.foldl (fun acc a => a.applyPacked acc)
      word7State45 = word7State46 := by decide +kernel

private def word7Chunk46 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word7State47 : PackedMat2 :=
    ⟨⟨⟨((21983551585 : Dyadic) * half ^ 36),
        ((-5303929103 : Dyadic) * half ^ 34)⟩,
       ⟨((-21923378061 : Dyadic) * half ^ 36),
        ((788750581 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-29507640577 : Dyadic) * half ^ 36),
        ((-6568101109 : Dyadic) * half ^ 35)⟩,
       ⟨((40371423525 : Dyadic) * half ^ 36),
        ((2379666887 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((15515869105 : Dyadic) * half ^ 36),
        ((34939532051 : Dyadic) * half ^ 36)⟩,
       ⟨((-10756535331 : Dyadic) * half ^ 36),
        ((2715945737 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-22004466993 : Dyadic) * half ^ 36),
        ((21953464823 : Dyadic) * half ^ 36)⟩,
       ⟨((20426965831 : Dyadic) * half ^ 36),
        ((-15043381 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word7Step46 :
    word7Chunk46.foldl (fun acc a => a.applyPacked acc)
      word7State46 = word7State47 := by decide +kernel

private def word7Chunk47 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word7State48 : PackedMat2 :=
    ⟨⟨⟨((-12503923835 : Dyadic) * half ^ 35),
        ((4029299393 : Dyadic) * half ^ 36)⟩,
       ⟨((-8405185389 : Dyadic) * half ^ 36),
        ((-2844922585 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-44313689773 : Dyadic) * half ^ 36),
        ((-2667897763 : Dyadic) * half ^ 35)⟩,
       ⟨((-182311269 : Dyadic) * half ^ 29),
        ((1751498243 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-4338095209 : Dyadic) * half ^ 35),
        ((67649532205 : Dyadic) * half ^ 37)⟩,
       ⟨((9673890735 : Dyadic) * half ^ 35),
        ((20977847341 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-18730081287 : Dyadic) * half ^ 36),
        ((-33413033059 : Dyadic) * half ^ 37)⟩,
       ⟨((26788680073 : Dyadic) * half ^ 36),
        ((-16602662281 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word7Step47 :
    word7Chunk47.foldl (fun acc a => a.applyPacked acc)
      word7State47 = word7State48 := by decide +kernel

private def word7Chunk48 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word7State49 : PackedMat2 :=
    ⟨⟨⟨((104515402905 : Dyadic) * half ^ 37),
        ((31529091345 : Dyadic) * half ^ 38)⟩,
       ⟨((-3666786625 : Dyadic) * half ^ 33),
        ((48188298975 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((23293903065 : Dyadic) * half ^ 37),
        ((-30271629391 : Dyadic) * half ^ 38)⟩,
       ⟨((-1948235767 : Dyadic) * half ^ 36),
        ((-60826333785 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((23293903065 : Dyadic) * half ^ 37),
        ((-30271629391 : Dyadic) * half ^ 38)⟩,
       ⟨((1948235767 : Dyadic) * half ^ 36),
        ((60826333785 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-104515402905 : Dyadic) * half ^ 37),
        ((-31529091345 : Dyadic) * half ^ 38)⟩,
       ⟨((-3666786625 : Dyadic) * half ^ 33),
        ((48188298975 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word7Step48 :
    word7Chunk48.foldl (fun acc a => a.applyPacked acc)
      word7State48 = word7State49 := by decide +kernel

private def word7Chunk49 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word7State50 : PackedMat2 :=
    ⟨⟨⟨((8362971785 : Dyadic) * half ^ 35),
        ((95557068113 : Dyadic) * half ^ 38)⟩,
       ⟨((74403615173 : Dyadic) * half ^ 37),
        ((-18329301805 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((9767530631 : Dyadic) * half ^ 35),
        ((34735807815 : Dyadic) * half ^ 37)⟩,
       ⟨((1321009705 : Dyadic) * half ^ 34),
        ((-43126435717 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-112598051347 : Dyadic) * half ^ 38),
        ((-7125511221 : Dyadic) * half ^ 36)⟩,
       ⟨((26345179913 : Dyadic) * half ^ 38),
        ((12409550041 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((168874275333 : Dyadic) * half ^ 38),
        ((-40951728033 : Dyadic) * half ^ 38)⟩,
       ⟨((-22239860893 : Dyadic) * half ^ 38),
        ((-107855502313 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word7Step49 :
    word7Chunk49.foldl (fun acc a => a.applyPacked acc)
      word7State49 = word7State50 := by decide +kernel

private def word7Chunk50 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word7State51 : PackedMat2 :=
    ⟨⟨⟨((-25700574013 : Dyadic) * half ^ 39),
        ((-106318024643 : Dyadic) * half ^ 39)⟩,
       ⟨((18476649875 : Dyadic) * half ^ 39),
        ((86550348319 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-135485579327 : Dyadic) * half ^ 39),
        ((75474072191 : Dyadic) * half ^ 39)⟩,
       ⟨((16445495401 : Dyadic) * half ^ 39),
        ((33339591699 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-16445495401 : Dyadic) * half ^ 39),
        ((-33339591699 : Dyadic) * half ^ 38)⟩,
       ⟨((135485579327 : Dyadic) * half ^ 39),
        ((-75474072191 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((18476649875 : Dyadic) * half ^ 39),
        ((86550348319 : Dyadic) * half ^ 37)⟩,
       ⟨((-25700574013 : Dyadic) * half ^ 39),
        ((-106318024643 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word7Step50 :
    word7Chunk50.foldl (fun acc a => a.applyPacked acc)
      word7State50 = word7State51 := by decide +kernel

private def word7Chunk51 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word7State52 : PackedMat2 :=
    ⟨⟨⟨((-293724374685 : Dyadic) * half ^ 39),
        ((-101225969307 : Dyadic) * half ^ 39)⟩,
       ⟨((11681953497 : Dyadic) * half ^ 36),
        ((-5940091291 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((45964792669 : Dyadic) * half ^ 37),
        ((-110865377511 : Dyadic) * half ^ 39)⟩,
       ⟨((-231148618529 : Dyadic) * half ^ 39),
        ((-36406882557 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-231148618529 : Dyadic) * half ^ 39),
        ((-36406882557 : Dyadic) * half ^ 39)⟩,
       ⟨((45964792669 : Dyadic) * half ^ 37),
        ((-110865377511 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-11681953497 : Dyadic) * half ^ 36),
        ((5940091291 : Dyadic) * half ^ 34)⟩,
       ⟨((293724374685 : Dyadic) * half ^ 39),
        ((101225969307 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word7Step51 :
    word7Chunk51.foldl (fun acc a => a.applyPacked acc)
      word7State51 = word7State52 := by decide +kernel

private def word7Chunk52 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word7State53 : PackedMat2 :=
    ⟨⟨⟨((57977080185 : Dyadic) * half ^ 40),
        ((122624013463 : Dyadic) * half ^ 41)⟩,
       ⟨((-123657430651 : Dyadic) * half ^ 38),
        ((-244285597721 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-120624675077 : Dyadic) * half ^ 40),
        ((1089718151965 : Dyadic) * half ^ 41)⟩,
       ⟨((280729951911 : Dyadic) * half ^ 39),
        ((6245500853 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-547981826409 : Dyadic) * half ^ 40),
        ((-440835228745 : Dyadic) * half ^ 41)⟩,
       ⟨((-135434081389 : Dyadic) * half ^ 38),
        ((682084578899 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-60830792129 : Dyadic) * half ^ 40),
        ((-436652642419 : Dyadic) * half ^ 41)⟩,
       ⟨((22931850699 : Dyadic) * half ^ 37),
        ((552606802789 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word7Step52 :
    word7Chunk52.foldl (fun acc a => a.applyPacked acc)
      word7State52 = word7State53 := by decide +kernel

private def word7Chunk53 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word7State54 : PackedMat2 :=
    ⟨⟨⟨((1039757837069 : Dyadic) * half ^ 41),
        ((185546098755 : Dyadic) * half ^ 41)⟩,
       ⟨((-78371122455 : Dyadic) * half ^ 41),
        ((-678176482973 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-73271960361 : Dyadic) * half ^ 41),
        ((490240130569 : Dyadic) * half ^ 40)⟩,
       ⟨((-284355902403 : Dyadic) * half ^ 41),
        ((19147522327 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-73271960361 : Dyadic) * half ^ 41),
        ((490240130569 : Dyadic) * half ^ 40)⟩,
       ⟨((284355902403 : Dyadic) * half ^ 41),
        ((-19147522327 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-1039757837069 : Dyadic) * half ^ 41),
        ((-185546098755 : Dyadic) * half ^ 41)⟩,
       ⟨((-78371122455 : Dyadic) * half ^ 41),
        ((-678176482973 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word7Step53 :
    word7Chunk53.foldl (fun acc a => a.applyPacked acc)
      word7State53 = word7State54 := by decide +kernel

private def word7Chunk54 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word7State55 : PackedMat2 :=
    ⟨⟨⟨((706064687941 : Dyadic) * half ^ 40),
        ((1111899356501 : Dyadic) * half ^ 42)⟩,
       ⟨((-343331877167 : Dyadic) * half ^ 40),
        ((223692177379 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-545007277617 : Dyadic) * half ^ 41),
        ((385378341799 : Dyadic) * half ^ 41)⟩,
       ⟨((153862287873 : Dyadic) * half ^ 39),
        ((-870376536991 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((545007277617 : Dyadic) * half ^ 41),
        ((-385378341799 : Dyadic) * half ^ 41)⟩,
       ⟨((153862287873 : Dyadic) * half ^ 39),
        ((-870376536991 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((706064687941 : Dyadic) * half ^ 40),
        ((1111899356501 : Dyadic) * half ^ 42)⟩,
       ⟨((343331877167 : Dyadic) * half ^ 40),
        ((-223692177379 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word7Step54 :
    word7Chunk54.foldl (fun acc a => a.applyPacked acc)
      word7State54 = word7State55 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word7_check : check word7 7 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word7 = word7State55.toMatrix := by
    unfold evalRingPacked
    change ((
      word7Chunk0 ++ word7Chunk1 ++ word7Chunk2 ++ word7Chunk3 ++
      word7Chunk4 ++ word7Chunk5 ++ word7Chunk6 ++ word7Chunk7 ++
      word7Chunk8 ++ word7Chunk9 ++ word7Chunk10 ++ word7Chunk11 ++
      word7Chunk12 ++ word7Chunk13 ++ word7Chunk14 ++ word7Chunk15 ++
      word7Chunk16 ++ word7Chunk17 ++ word7Chunk18 ++ word7Chunk19 ++
      word7Chunk20 ++ word7Chunk21 ++ word7Chunk22 ++ word7Chunk23 ++
      word7Chunk24 ++ word7Chunk25 ++ word7Chunk26 ++ word7Chunk27 ++
      word7Chunk28 ++ word7Chunk29 ++ word7Chunk30 ++ word7Chunk31 ++
      word7Chunk32 ++ word7Chunk33 ++ word7Chunk34 ++ word7Chunk35 ++
      word7Chunk36 ++ word7Chunk37 ++ word7Chunk38 ++ word7Chunk39 ++
      word7Chunk40 ++ word7Chunk41 ++ word7Chunk42 ++ word7Chunk43 ++
      word7Chunk44 ++ word7Chunk45 ++ word7Chunk46 ++ word7Chunk47 ++
      word7Chunk48 ++ word7Chunk49 ++ word7Chunk50 ++ word7Chunk51 ++
      word7Chunk52 ++ word7Chunk53 ++ word7Chunk54
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word7Step0, word7Step1, word7Step2, word7Step3, word7Step4,
      word7Step5, word7Step6, word7Step7, word7Step8, word7Step9,
      word7Step10, word7Step11, word7Step12, word7Step13, word7Step14,
      word7Step15, word7Step16, word7Step17, word7Step18, word7Step19,
      word7Step20, word7Step21, word7Step22, word7Step23, word7Step24,
      word7Step25, word7Step26, word7Step27, word7Step28, word7Step29,
      word7Step30, word7Step31, word7Step32, word7Step33, word7Step34,
      word7Step35, word7Step36, word7Step37, word7Step38, word7Step39,
      word7Step40, word7Step41, word7Step42, word7Step43, word7Step44,
      word7Step45, word7Step46, word7Step47, word7Step48, word7Step49,
      word7Step50, word7Step51, word7Step52, word7Step53, word7Step54]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
