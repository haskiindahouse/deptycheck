module ValidateInput

import Deriving.DepTyCheck.Gen

%language ElabReflection
%default total

checkedGen : Fuel -> (x, y : Type) -> Gen MaybeEmpty (x = y)
checkedGen = deriveGen
