module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

data Color = Red | Green | Blue | Yellow | Cyan | Magenta

Show Color where
  show Red     = "Red"
  show Green   = "Green"
  show Blue    = "Blue"
  show Yellow  = "Yellow"
  show Cyan    = "Cyan"
  show Magenta = "Magenta"

-- Chunk 1: warm colors
genWarm : Fuel -> Gen MaybeEmpty Color
genWarm = deriveGenSubset [`{Red}, `{Yellow}]

-- Chunk 2: cool colors
genCool : Fuel -> Gen MaybeEmpty Color
genCool = deriveGenSubset [`{Green}, `{Blue}, `{Cyan}, `{Magenta}]

-- Compose: all colors
genAll : Fuel -> Gen MaybeEmpty Color
genAll fuel = oneOf $ alternativesOf (genWarm fuel) ++ alternativesOf (genCool fuel)

main : IO ()
main = runGs [ G genWarm, G genCool, G genAll ]
