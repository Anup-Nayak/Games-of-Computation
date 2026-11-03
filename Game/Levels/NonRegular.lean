import Game.Levels.NonRegular.L01_Indist
import Game.Levels.NonRegular.L02_Pigeonhole
import Game.Levels.NonRegular.L03_CountA
import Game.Levels.NonRegular.L04_CountB
import Game.Levels.NonRegular.L05_Exponents
import Game.Levels.NonRegular.L06_Anbn
import Game.Levels.NonRegular.L07_Balanced

World "NonRegular"
Title "Non-regular Languages"

Introduction "
Regular languages are closed under every operation you've tried. Is *every*
language regular?

No. A DFA has finite memory, and some languages need unbounded memory. In
this world you'll turn that intuition into a proof: `aⁿbⁿ` is not regular.
"
