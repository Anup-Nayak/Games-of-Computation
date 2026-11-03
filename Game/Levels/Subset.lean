import Game.Levels.Subset.L01_SubsetStep
import Game.Levels.Subset.L02_Track
import Game.Levels.Subset.L03_NotS2
import Game.Levels.Subset.L04_Nil
import Game.Levels.Subset.L05_OneSymbol
import Game.Levels.Subset.L06_Run
import Game.Levels.Subset.L07_Accepts
import Game.Levels.Subset.L08_Regular
import Game.Levels.Subset.L09_Combined

World "Subset"
Title "Determinization"

Introduction "
NFAs can guess; DFAs can't. Does guessing let NFAs recognise more languages?

No. In this world you'll build the **subset construction**, which turns any NFA
into a DFA with the same language by tracking all its guesses at once, and
prove it correct.
"
