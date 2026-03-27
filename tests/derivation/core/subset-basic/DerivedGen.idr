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

-- Only derive for Red, Green, Blue (never Yellow, Cyan, Magenta)
genPartial : Fuel -> Gen MaybeEmpty Color
genPartial = deriveGenSubset [`{Red}, `{Green}, `{Blue}]

main : IO ()
main = runGs [ G genPartial ]
