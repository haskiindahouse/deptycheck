||| A bridge between a single act of derivation (for a single type) and a user derivation task
module Deriving.DepTyCheck.Gen.ForAllNeededTypes.Impl

import public Control.Monad.State

import public Data.DPair
import public Data.List.Set
import public Data.SortedMap

import public Decidable.Equality

import public Deriving.DepTyCheck.Gen.ForOneType.Interface

%default total

--- Particular implementations producing the-core-derivation-function closure ---

ClosuringContext : (Type -> Type) -> Type
ClosuringContext m =
  ( ListSet GenSignature                                                 -- gens already asked to be derived
  , MonadState  (ListSet GenSignature, ListSet GenSignature) m           -- two queues of gens to be derived, one for known types, one the unknown ones
  )

nameForGen : GenSignature -> Name
nameForGen sig = let (ty, givs) = characteristics sig in UN $ Basic $ "<\{ty}>\{show givs}"
-- I'm using `UN` but containing chars that cannot be present in the code parsed from the Idris frontend.

-- Instead of staticaly ensuring that map holds only correct values, we check dynamically, because it's hard to go through `==`-based lookup of maps.
lookupLengthChecked : (intSig : GenSignature) -> SortedMap GenSignature (ExternalGenSignature, Name) ->
                      Maybe (Name, Subset ExternalGenSignature $ \extSig => extSig.givenParams.size = intSig.givenParams.size)
lookupLengthChecked intSig m = lookup intSig m >>= \(extSig, name) => (name,) <$>
                                 case decEq extSig.givenParams.size intSig.givenParams.size of
                                    Yes prf => Just $ Element extSig prf
                                    No _    => Nothing

-- Helper: get n-th element of a list (0-indexed)
listIndex : Nat -> List a -> Maybe a
listIndex _     []        = Nothing
listIndex Z     (x :: _)  = Just x
listIndex (S k) (_ :: xs) = listIndex k xs

-- Check if the arg type at the given index in the target type has a simple type (no type params)
isSimpleArgType : GenSignature -> Nat -> Bool
isSimpleArgType sig n = case listIndex n sig.targetType.args of
  Nothing => False
  Just (MkArg _ _ _ ty) => case ty of
    IVar _ _ => True
    _        => False

-- Find an external gen where intSig.givenParams is a proper subset of extSig.givenParams.
-- Only matches when: same type, proper subset, ext gen has ALL params given, extras have simple types.
lookupSupersetMatch : (intSig : GenSignature) -> SortedMap GenSignature (ExternalGenSignature, Name) ->
                      Maybe (Name, ExternalGenSignature, List Nat)
lookupSupersetMatch intSig m = go $ SortedMap.toList m where
  go : List (GenSignature, (ExternalGenSignature, Name)) -> Maybe (Name, ExternalGenSignature, List Nat)
  go [] = Nothing
  go ((_, (extSig, name)) :: rest) =
    let (extTyName, extGivNats) = ExternalGenSignature.characteristics extSig
        (intTyName, intGivNats) = characteristics intSig
        extraNats = filter (\n => not $ n `elem` intGivNats) extGivNats
    in if extTyName == intTyName &&
          length extGivNats > length intGivNats &&
          all (\n => n `elem` extGivNats) intGivNats &&
          length extGivNats == length intSig.targetType.args &&
          all (isSimpleArgType intSig) extraNats
       then Just (name, extSig, extraNats)
       else go rest

-- Build a wrapper that generates extra params, calls the external gen, and wraps in DPair.
buildSupersetCall : DerivationClosure m => NamesInfoInTypes => ConsRecs => Elaboration m =>
                    (intSig : GenSignature) -> ExternalGenSignature -> Name ->
                    List Nat -> Vect intSig.givenParams.size TTImp ->
                    m (TTImp, Maybe (gend ** Vect gend $ Fin gend))
buildSupersetCall intSig extSig extName extraNats callerValues = do

  -- Step 1: For each extra param, generate a sub-generator call
  extraCalls <- for extraNats $ \natIdx => do
    let Just (MkArg _ _ _ argTy) = listIndex natIdx intSig.targetType.args
      | Nothing => fail "INTERNAL ERROR: superset extra param index \{show natIdx} out of bounds"
    let IVar _ tyName = argTy
      | _ => fail "INTERNAL ERROR: superset extra param \{show natIdx} has non-simple type"
    let Just extraTyInfo = lookupType tyName
      | Nothing => fail "INTERNAL ERROR: cannot find type info for superset extra param type \{show tyName}"
    let extraSig : GenSignature = MkGenSignature extraTyInfo @{believe_me ()} empty
    let emptyVals : Vect extraSig.givenParams.size TTImp = believe_me (the (Vect 0 TTImp) [])
    (extraGenExpr, _) <- assert_total $ callGen extraSig (var outmostFuelArg) emptyVals
    let bindName = UN $ Basic $ "^superset_extra_" ++ show natIdx ++ "^"
    pure (natIdx, extraGenExpr, bindName)

  -- Step 2: Build a map from Nat index to TTImp value (caller values + extra bind vars)
  let intGivList = Prelude.toList intSig.givenParams
  let callerPairs : List (Nat, TTImp) = zip (map finToNat intGivList) (toList callerValues)
  let extraPairs : List (Nat, TTImp) = map (\(ni, _, bn) => (ni, var bn)) extraCalls
  let allValMap : SortedMap Nat TTImp = SortedMap.fromList (callerPairs ++ extraPairs)

  -- Step 3: Build full values Vect for external gen (mapped over extSig's asVect for correct size)
  let fullValues : Vect extSig.givenParams.size TTImp =
        extSig.givenParams.asVect <&> \(idx, _) =>
          fromMaybe implicitTrue $ SortedMap.lookup (finToNat idx) allValMap

  -- Step 4: Call the external gen
  let extCall = callExternalGen extSig extName (var outmostFuelArg) fullValues

  -- Step 5: Build DPair wrapping + pure
  let resultBind = UN $ Basic "^superset_result^"
  let extraBindNames : List Name = map (\(_, _, bn) => bn) extraCalls
  let dpairExpr = foldr (\bn, r => var `{Builtin.DPair.MkDPair} .$ var bn .$ r) (var resultBind) extraBindNames
  let pureExpr = `(Prelude.pure {f=Test.DepTyCheck.Gen.Gen _} ~dpairExpr)

  -- Step 6: Build monadic chain (inside-out via foldr)
  let innerBind = `(~extCall >>= ~(lam (MkArg MW ExplicitArg (Just resultBind) implicitFalse) pureExpr))
  let wrapperExpr = foldr (\(_, genExpr, bn), inner => `(~genExpr >>= ~(lam (MkArg MW ExplicitArg (Just bn) implicitFalse) inner))) innerBind extraCalls

  pure (wrapperExpr, Nothing)

deriveAll : NamesInfoInTypes => ConsRecs => (cc : ClosuringContext m) => DeriveBodyForType => DerivationClosure m => Elaboration m =>
            ListSet TypeInfo -> List (Decl, Decl) -> m (ListSet TypeInfo, List (Decl, Decl))
deriveAll weightFunTys decls {cc=(alreadyDerived, _)}= do
  (toDeriveKnown, toDeriveUnknown) <- mapHom ((`difference` alreadyDerived) . normalise) <$> get {stateType=(ListSet _, ListSet _)}
  put (empty, toDeriveUnknown)
  (weightFunTys, decls) <- bimap (foldl insert' weightFunTys . join) (decls ++) . unzip <$> for (toList toDeriveKnown) deriveOne
  if not $ null toDeriveKnown
    then assert_total $ deriveAll {cc=(alreadyDerived `union` toDeriveKnown, %search)} weightFunTys decls
    else if null toDeriveUnknown
      then pure (weightFunTys, decls)
      else do
        (niit, cr) <- updateNamesAndConsRecs $ targetType <$> toList toDeriveUnknown
        put (toDeriveUnknown, empty)
        assert_total $ deriveAll @{niit} @{cr} {cc=(alreadyDerived `union` toDeriveUnknown, %search)} weightFunTys decls
  where
    deriveOne : GenSignature -> m (List TypeInfo, Decl, Decl)
    deriveOne sig = do
      let name = nameForGen sig
      -- derive declaration and body for the asked signature. It's important to call it AFTER update of the map in the state to not to cycle
      let genFunClaim = export' name $ canonicSig sig
      (tyWithWeightFuns, genFunBody) <- logBounds Info "deptycheck.derive.type" [sig] $ canonicBody sig name
      pure (tyWithWeightFuns, genFunClaim, def name genFunBody)

DeriveBodyForType => ClosuringContext m => Elaboration m => SortedMap GenSignature (ExternalGenSignature, Name) => DerivationClosure m where

  callGen sig fuel values = do

    -- DEBUG: log what we're looking for
    logPoint Info "deptycheck.derive.closuring.lookup" [sig] "looking for external gen, givens=\{showGivens sig}"

    -- look for external gens, and call it if exists
    let Nothing = lookupLengthChecked sig %search
      | Just (name, Element extSig lenEq) =>
          logValue Details "deptycheck.derive.closuring.external" [sig] "is used as an external generator" $
            (callExternalGen extSig name (var outmostFuelArg) $ rewrite lenEq in values, Just (_ ** extSig.gendOrder))

    -- look for superset match (external gen with more given params than we need)
    let Nothing = lookupSupersetMatch sig %search
      | Just (name, extSig, extraNats) => do
          logPoint Details "deptycheck.derive.closuring.superset" [sig]
            "superset match via \{show name}, extras=\{show extraNats}"
          assert_total $ buildSupersetCall sig extSig name extraNats values

    -- put to derivation queue if necessary
    when (not $ List.Set.contains sig %search) $ do

      -- remember the task to derive
      modify $ if isTypeKnown sig.targetType then mapFst $ normalise . List.Set.insert sig else mapSnd $ normalise . List.Set.insert sig

    -- call the internal gen
    logValue DetailedDebug "deptycheck.derive.closuring.internal" [sig] "is used as an internal generator"
      (callCanonic sig (nameForGen sig) fuel values, Nothing)

--- Canonic-dischagring function ---

%hide Data.Vect.Dependent.(<*>)

declName : Decl -> String
declName $ IClaim $ MkFCVal _ $ MkIClaimData {type = MkTy {ty, _}, _} = show ty
declName $ IData _ _ _ $ MkData  {n, _} = show n
declName $ IData _ _ _ $ MkLater {n, _} = show n
declName $ IDef _ nm _ = show nm
declName $ IParameters _ _ [] = "P"
declName $ IParameters _ _ (d::_) = declName d
declName $ IRecord _ _ _ _ $ MkRecord {n, _} = show n
declName $ INamespace _ (MkNS ns) _ = joinBy "." $ reverse ns
declName $ ITransform _ nm _ _ = show nm
declName $ IRunElabDecl {} = "Z"
declName $ ILog {} = "Z"
declName $ IBuiltin _ _ nm = show nm

export
runCanonic : DeriveBodyForType => NamesInfoInTypes => ConsRecs =>
             SortedMap ExternalGenSignature Name -> (forall m. DerivationClosure m => m a) -> Elab (a, List Decl)
runCanonic exts calc = do
  let exts = SortedMap.fromList $ exts.asList <&> \namedSig => (fst $ internalise $ fst namedSig, namedSig)
  (x, weightingFuns, derived) <- evalStateT
                         (empty, empty)
                         [| (calc, deriveAll (empty @{TypeInfoEqByName}) []) |]
                         {stateType=(ListSet GenSignature, ListSet GenSignature)}
                         {m=Elab}
  let derived = sortBy (compare `on` declName . fst) $ derived ++ mapMaybe deriveWeightingFun (Prelude.toList weightingFuns)
  let (defs, bodies) = unzip derived
  pure (x, defs ++ bodies)
