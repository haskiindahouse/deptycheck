module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

-- 20 constructors: baseline test for deriveGen
data SmallType
  = C0 | C1 | C2 | C3 | C4
  | C5 | C6 | C7 | C8 | C9
  | C10 | C11 | C12 | C13 | C14
  | C15 | C16 | C17 | C18 | C19

%hint showSmallType : Show SmallType
showSmallType = %runElab derive

checkedGen : Fuel -> Gen MaybeEmpty SmallType
checkedGen = deriveGen

main : IO ()
main = runGs [ G checkedGen ]
