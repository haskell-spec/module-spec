{- This module contains (modernized) code for the paper "A Formal Specification of the Haskell 98 Module System" by Diatchki, Jones and Hallgren
-}
module Main where

import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Maybe (isJust, isNothing)
import Data.List (nub, partition)

-- Section 2: Relations

type Rel  a b = S.Set (a,b)

listToRel :: (Ord a, Ord b) => [(a,b)] -> Rel a b
listToRel = S.fromList

relToList :: Rel a b -> [(a,b)]
relToList = S.toList

emptyRel :: Rel a b
emptyRel = S.empty

restrictDom :: (Ord a, Ord b)
            => (a -> Bool)
            -> Rel a b
            -> Rel a b
restrictDom p r = listToRel [(x,y) | (x,y) <- relToList r, p x]

restrictRng :: (Ord a, Ord b)
            => (b -> Bool)
            -> Rel a b
            -> Rel a b
restrictRng p r = listToRel [(x,y) | (x,y) <- relToList r, p y]

dom :: Ord a => Rel a b -> S.Set a
dom = S.map fst

rng :: Ord b => Rel a b -> S.Set b
rng = S.map snd

mapDom :: (Ord b, Ord x)
       => (a -> x)
       -> Rel a b
       -> Rel x b
mapDom f = S.map (\(x,y) -> (f x, y))

mapRng :: (Ord a, Ord x)
       => (b -> x)
       -> Rel a b
       -> Rel a x
mapRng f = S.map (\(x,y) -> (x, f y))

intersectRel :: (Ord a, Ord b)
             => Rel a b
             -> Rel a b
             -> Rel a b
intersectRel = S.intersection

unionRels :: (Ord a, Ord b)
          => [Rel a b]
          -> Rel a b
unionRels = S.unions

minusRel :: (Ord a, Ord b)
         => Rel a b
         -> Rel a b
         -> Rel a b
minusRel = S.difference

partitionDom :: (Ord a, Ord b)
             => (a -> Bool)
             -> Rel a b
             -> (Rel a b, Rel a b)
partitionDom p r = (restrictDom p r, restrictDom (not . p) r)

applyRel :: (Ord a, Ord b)
         => Rel a b
         -> a
         -> [b]
applyRel r a = S.toList (rng (restrictDom (== a) r))

unionMapSet :: Ord b => (a -> S.Set b) -> (S.Set a -> S.Set b)
unionMapSet f = S.unions . map f . S.toList

-- Section 3: Names and Entities


newtype EntityFun = MkEntityFun Text
  deriving (Eq, Ord)

newtype EntityTmCon = MkEntityTmCon Text
  deriving (Eq, Ord)

newtype EntityFieldLabel = MkEntityFieldLabel Text
  deriving (Eq, Ord)

data EntityTyCon = MkEntityTyCon Text [EntityTmCon] [EntityFieldLabel]
  deriving (Eq, Ord)

newtype EntityClassMethod = MkEntityClassMethod Text
  deriving (Eq, Ord)

data EntityTyClass = MkEntityTyClass Text [EntityClassMethod]
  deriving (Eq, Ord)

data Entity =
      Fun EntityFun
    | TyCon EntityTyCon
    | TmCon EntityTmCon
    | FieldLabel EntityFieldLabel
    | TyCls EntityTyClass
    | ClsMethod EntityClassMethod
    deriving (Eq, Ord)

class ToEntity a where
    toEntity :: a -> Entity

instance ToEntity EntityFun where
    toEntity = Fun

instance ToEntity EntityTyCon where
    toEntity = TyCon

instance ToEntity EntityTmCon where
    toEntity = TmCon
instance ToEntity EntityFieldLabel where
    toEntity = FieldLabel

instance ToEntity EntityTyClass where
    toEntity = TyCls

instance ToEntity EntityClassMethod where
    toEntity = ClsMethod


isCon :: Entity -> Bool
isCon (TmCon _) = True
isCon _ = False

-- | Type constructors own their value constructors and field labels.
-- Classes own their methods.
owns :: Entity -> S.Set Entity
owns (Fun _) = S.empty
owns (TyCon (MkEntityTyCon _ tmcons fieldlabels)) = S.fromList ((toEntity <$> tmcons) <> (toEntity <$> fieldlabels))
owns (TmCon _) = S.empty
owns (FieldLabel _) = S.empty
owns (TyCls (MkEntityTyClass _ methods)) = S.fromList (toEntity <$> methods)
owns (ClsMethod _) = S.empty

newtype Name = MkName Text
  deriving (Eq, Ord)

newtype ModName = ModName Text -- Haskell 98
  deriving (Eq, Ord)

data QName = Qualified ModName Name | UnQualified Name
  deriving (Eq, Ord)

getQualifier :: QName -> Maybe ModName
getQualifier (Qualified m _) = Just m
getQualifier (UnQualified _) = Nothing

getQualified :: QName -> Name
getQualified (Qualified _ n) = n
getQualified (UnQualified n) = n

mkUnqual :: Name -> QName
mkUnqual = UnQualified

mkQual :: ModName -> Name -> QName
mkQual = Qualified

isQual :: QName -> Bool
isQual = isJust . getQualifier

qual :: ModName -> QName -> QName
qual m = mkQual m . getQualified

class ToSimple t where
    toSimple :: t -> Name

instance ToSimple Name where
    toSimple  = id

instance ToSimple QName where
    toSimple = getQualified

-- Section 4: Abstract Syntax

data SubSpec = AllSubs | Subs [Name]

data EntSpec j = Ent j (Maybe SubSpec)

data ExpListEntry = EntExp (EntSpec QName) | ModuleExp ModName

data Import = Import {
    impQualified :: Bool,
    impSource :: ModName,
    impAs :: ModName,
    impHiding :: Bool,
    impList :: [EntSpec Name]
}

data Module = Module {
    modName :: ModName,
    modExpList :: Maybe [ExpListEntry],
    modImports :: [Import],
    modDefines :: Rel Name Entity
}

-- Section 5: The semantics of Imports and Exports
mEntSpec :: (Ord j, ToSimple j)
         => Bool            -- ^ Is it a hiding import?
         -> Rel j Entity    -- ^ The original relation
         -> EntSpec j       -- ^ The specification
         -> Rel j Entity    -- ^ The subset satisfying the specification
mEntSpec isHiding rel (Ent x subspec) =
    unionRels [mSpec, mSub]
    where
        mSpec = restrictRng consider (restrictDom (== x) rel)
        allSubs = owns `unionMapSet` rng mSpec
        subs = restrictRng (`S.member` allSubs) rel
        mSub =
            case subspec of
                Nothing -> emptyRel
                Just AllSubs -> subs
                Just (Subs xs) ->
                    restrictDom ((`elem` xs) . toSimple) subs
        consider
          | isHiding && isNothing subspec = const True
          | otherwise                     = not . isCon

mExpListEntry :: Rel QName Entity
              -> ExpListEntry
              -> Rel QName Entity
mExpListEntry inscp (EntExp it) = mEntSpec False inscp it
mExpListEntry inscp (ModuleExp m) =
    (qual m `mapDom` unqs) `intersectRel` qs
    where
        (qs, unqs) = partitionDom isQual inscp

exports :: Module -> Rel QName Entity -> Rel Name Entity
exports mod inscp =
    case modExpList mod of
        Nothing -> modDefines mod
        Just es -> getQualified `mapDom` unionRels exps
          where
            exps = mExpListEntry inscp `map` es

mImp :: (ModName -> Rel Name Entity)
     -> Import
     -> Rel QName Entity
mImp expsOf imp
    | impQualified imp = qs
    | otherwise = unionRels [unqs, qs]
    where
        qs = mkQual (impAs imp) `mapDom` incoming
        unqs = mkUnqual `mapDom` incoming

        listed = unionRels $ map (mEntSpec isHiding exps) (impList imp)
        incoming
          | isHiding = exps `minusRel` listed
          | otherwise = listed
        
        isHiding = impHiding imp
        exps = expsOf (impSource imp)


inscope :: Module
        -> (ModName -> Rel Name Entity)
        -> Rel QName Entity
inscope m expsOf = unionRels [imports, locals]
  where
    defEnts = modDefines m
    locals = unionRels [ mkUnqual `mapDom` defEnts
                       , mkQual (modName m) `mapDom` defEnts]
    imports =
        unionRels $ map (mImp expsOf) (modImports m)

-- Section 6: Error Detection

data ModSysErr =
    UndefinedModuleAlias ModName
    | UndefinedExport QName
    | UndefinedSubExport QName Name
    | AmbiguousExport Name [Entity]
    | MissingModule ModName
    | UndefinedImport ModName Name
    | UndefinedSubImport ModName Name Name

chkAmbigExps :: Rel Name Entity -> [ModSysErr]
chkAmbigExps exps = concatMap isAmbig (S.toList (dom exps))
  where
    isAmbig n =
        let (cons, other) = partition isCon (applyRel exps n)
        in ambig n cons <> ambig n other
    ambig n ents@(_:_:_) = [AmbiguousExport n ents]
    ambig n _ = []

chkEntSpec :: (Ord j, ToSimple j)
           => Bool -- ^ Is it a hiding import?
           -> (j -> ModSysErr) -- ^ Report error
           -> (j -> Name -> ModSysErr) -- ^ Report error
           -> EntSpec j -- ^ The specification
           -> Rel j Entity -- ^ The relation to check
           -> [ModSysErr] -- ^ Detected Errors
chkEntSpec isHiding errUndef errUndefSub  (Ent x subspec) rel =
    case xents of
        [] -> [errUndef x]
        ents -> concatMap chk ents
    where
        xents = filter consider (applyRel rel x)
        
        chk ent =
            case subspec of
                Just (Subs subs) ->
                    map (errUndefSub x) (filter (not . (`S.member` subsInScope)) subs)
                    where
                        subsInScope = S.map toSimple $ dom $ restrictRng (`S.member` owns ent) rel
                _ -> []
        consider
          | isHiding && isNothing subspec = const True
          | otherwise = not . isCon

chkExpSpec :: Rel QName Entity -> Module -> [ModSysErr]
chkExpSpec inscp mod =
    case modExpList mod of
        Nothing -> []
        Just exps -> concatMap chk exps
    where
        aliases = modName mod : impAs `map` modImports mod
        chk (ModuleExp x)
          | x `elem` aliases = []
          | otherwise = [UndefinedModuleAlias x]
        chk (EntExp spec) = chkEntSpec False UndefinedExport UndefinedSubExport spec inscp

chkImport :: Rel Name Entity
          -> Import
          -> [ModSysErr]
chkImport exps imp = concatMap chk (impList imp)
  where
    src = impSource imp
    chk spec =
        chkEntSpec (impHiding imp) (UndefinedImport src) (UndefinedSubImport src) spec exps


chkModule :: (ModName -> Maybe (Rel Name Entity))
          -> Rel QName Entity
          -> Module
          -> [ModSysErr]
chkModule expsOf inscp mod =
    chkAmbigExps mod_exports <> if null missingModules
                                then chkExpSpec inscp mod <> [err | (imp, Just exps) <- impSources, err <- chkImport exps imp]
                                else map MissingModule missingModules
    where
        Just mod_exports = expsOf (modName mod)
        missingModules = nub [impSource imp | (imp, Nothing) <- impSources]
        impSources = [(imp, expsOf (impSource imp)) | imp <- modImports mod]



main :: IO ()
main = print "hello"