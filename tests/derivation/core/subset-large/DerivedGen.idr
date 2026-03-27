module DerivedGen

import RunDerivedGen

%default total

%language ElabReflection

-- 100 constructors: split into 10 chunks of 10 using deriveGenSubset
data LargeType
  = C0 | C1 | C2 | C3 | C4 | C5 | C6 | C7 | C8 | C9
  | C10 | C11 | C12 | C13 | C14 | C15 | C16 | C17 | C18 | C19
  | C20 | C21 | C22 | C23 | C24 | C25 | C26 | C27 | C28 | C29
  | C30 | C31 | C32 | C33 | C34 | C35 | C36 | C37 | C38 | C39
  | C40 | C41 | C42 | C43 | C44 | C45 | C46 | C47 | C48 | C49
  | C50 | C51 | C52 | C53 | C54 | C55 | C56 | C57 | C58 | C59
  | C60 | C61 | C62 | C63 | C64 | C65 | C66 | C67 | C68 | C69
  | C70 | C71 | C72 | C73 | C74 | C75 | C76 | C77 | C78 | C79
  | C80 | C81 | C82 | C83 | C84 | C85 | C86 | C87 | C88 | C89
  | C90 | C91 | C92 | C93 | C94 | C95 | C96 | C97 | C98 | C99

%hint showLargeType : Show LargeType
showLargeType = %runElab derive

-- Chunk 1: C0-C9
genChunk1 : Fuel -> Gen MaybeEmpty LargeType
genChunk1 = deriveGenSubset [`{C0}, `{C1}, `{C2}, `{C3}, `{C4}, `{C5}, `{C6}, `{C7}, `{C8}, `{C9}]

-- Chunk 2: C10-C19
genChunk2 : Fuel -> Gen MaybeEmpty LargeType
genChunk2 = deriveGenSubset [`{C10}, `{C11}, `{C12}, `{C13}, `{C14}, `{C15}, `{C16}, `{C17}, `{C18}, `{C19}]

-- Chunk 3: C20-C29
genChunk3 : Fuel -> Gen MaybeEmpty LargeType
genChunk3 = deriveGenSubset [`{C20}, `{C21}, `{C22}, `{C23}, `{C24}, `{C25}, `{C26}, `{C27}, `{C28}, `{C29}]

-- Chunk 4: C30-C39
genChunk4 : Fuel -> Gen MaybeEmpty LargeType
genChunk4 = deriveGenSubset [`{C30}, `{C31}, `{C32}, `{C33}, `{C34}, `{C35}, `{C36}, `{C37}, `{C38}, `{C39}]

-- Chunk 5: C40-C49
genChunk5 : Fuel -> Gen MaybeEmpty LargeType
genChunk5 = deriveGenSubset [`{C40}, `{C41}, `{C42}, `{C43}, `{C44}, `{C45}, `{C46}, `{C47}, `{C48}, `{C49}]

-- Chunk 6: C50-C59
genChunk6 : Fuel -> Gen MaybeEmpty LargeType
genChunk6 = deriveGenSubset [`{C50}, `{C51}, `{C52}, `{C53}, `{C54}, `{C55}, `{C56}, `{C57}, `{C58}, `{C59}]

-- Chunk 7: C60-C69
genChunk7 : Fuel -> Gen MaybeEmpty LargeType
genChunk7 = deriveGenSubset [`{C60}, `{C61}, `{C62}, `{C63}, `{C64}, `{C65}, `{C66}, `{C67}, `{C68}, `{C69}]

-- Chunk 8: C70-C79
genChunk8 : Fuel -> Gen MaybeEmpty LargeType
genChunk8 = deriveGenSubset [`{C70}, `{C71}, `{C72}, `{C73}, `{C74}, `{C75}, `{C76}, `{C77}, `{C78}, `{C79}]

-- Chunk 9: C80-C89
genChunk9 : Fuel -> Gen MaybeEmpty LargeType
genChunk9 = deriveGenSubset [`{C80}, `{C81}, `{C82}, `{C83}, `{C84}, `{C85}, `{C86}, `{C87}, `{C88}, `{C89}]

-- Chunk 10: C90-C99
genChunk10 : Fuel -> Gen MaybeEmpty LargeType
genChunk10 = deriveGenSubset [`{C90}, `{C91}, `{C92}, `{C93}, `{C94}, `{C95}, `{C96}, `{C97}, `{C98}, `{C99}]

-- Compose all chunks
genAll : Fuel -> Gen MaybeEmpty LargeType
genAll fuel = oneOf $ alternativesOf (genChunk1 fuel)
                   ++ alternativesOf (genChunk2 fuel)
                   ++ alternativesOf (genChunk3 fuel)
                   ++ alternativesOf (genChunk4 fuel)
                   ++ alternativesOf (genChunk5 fuel)
                   ++ alternativesOf (genChunk6 fuel)
                   ++ alternativesOf (genChunk7 fuel)
                   ++ alternativesOf (genChunk8 fuel)
                   ++ alternativesOf (genChunk9 fuel)
                   ++ alternativesOf (genChunk10 fuel)

main : IO ()
main = runGs [ G genAll ]
