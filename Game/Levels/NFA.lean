import Game.Levels.NFA.L01_Path
import Game.Levels.NFA.L02_Moves
import Game.Levels.NFA.L03_Accepts
import Game.Levels.NFA.L04_PathNil
import Game.Levels.NFA.L05_PathCons
import Game.Levels.NFA.L06_DeadEnd
import Game.Levels.NFA.L07_Wait
import Game.Levels.NFA.L08_Stay
import Game.Levels.NFA.L09_Glue
import Game.Levels.NFA.L10_ContainsAB
import Game.Levels.NFA.L11_DFAPath
import Game.Levels.NFA.L12_SameLanguage

World "NFA"
Title "Nondeterministic Automata"

Introduction "
A DFA has exactly one move for every symbol. An NFA may have several, or none,
and it accepts a string if *some* sequence of choices works.

In this world you'll build paths by guessing, take paths apart, and design an
NFA that finds `ab` anywhere in a string. At the end you'll show that every
DFA is an NFA.
"
