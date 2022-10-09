module Lambda where
import Control.Monad.Error (MonadError(throwError))
import Control.Monad (unless)

{-
    Abstract Syntax
-}

{-| Inferable term 
-}
data ITerm
  = Ann CTerm Type
  | Bound Int
  | Free Name
  | ITerm :@: CTerm
  deriving (Show, Eq)

{-| Checkable term
-}
data CTerm
  = Inf ITerm
  | Lam CTerm
  deriving (Show, Eq)

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

data Type
  = TFree Name
  | Fun Type Type
  deriving (Show, Eq)

data Value
  = VLam (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApp Neutral Value

type Env = [Value]

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

{-
    Evaluation
-}

iEval :: ITerm -> Env -> Value
iEval (Ann e _)  d = cEval e d
iEval (Free x)   d = vfree x
iEval (Bound i)  d = d!!i
iEval (e :@: e') d = vapp (iEval e d) (cEval e' d)

vapp :: Value -> Value -> Value
vapp (VLam f)     v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

cEval :: CTerm -> Env -> Value
cEval (Inf i) d = iEval i d
cEval (Lam e) d = VLam (\x -> cEval e (x : d))

{-
    Contexts
-}

data Kind = Star deriving (Show)

data Info 
  = HasKind Kind
  | HasType Type
  deriving (Show)

type Context = [(Name, Info)]

{-
    Type Checking
-}

type Result a = Either String a

cKind :: Context -> Type -> Kind -> Result ()
cKind ctx (TFree x) Star
  = case lookup x ctx of
    Just (HasKind Star) -> return ()
    Just (HasType _)    -> throwError "ASSERT FAILED"
    Nothing             -> throwError "unknown Identifier"
cKind ctx (Fun k k') Star = do 
  cKind ctx k  Star
  cKind ctx k' Star

iType0 :: Context -> ITerm -> Result Type
iType0 = iType 0

iType :: Int -> Context -> ITerm -> Result Type
iType i ctx (Ann e t) = do
  cKind ctx t Star
  cType i ctx e t
  return t
iType _ ctx (Free x) = 
  case lookup x ctx of 
    Just (HasType t) -> return t
    Just (HasKind _) -> throwError "ASSERT FAILED"
    Nothing          -> throwError "Unknown identifier"
iType i ctx (e :@: e') = do
  g <- iType i ctx e
  case g of
    Fun t t' -> do 
      cType i ctx e' t
      return t'
    _ -> throwError "illegal operation"
iType _ _ _ = throwError "ASSERT FAILED"

cType :: Int -> Context -> CTerm -> Type -> Result ()
cType i ctx (Inf e) t = do
  t' <- iType i ctx e
  unless (t == t') (throwError "illegal application")
cType i ctx (Lam e) (Fun t t') =
  cType (i + 1) ((Local i, HasType t) : ctx) (cSubst 0 (Free (Local i)) e) t'
cType _ _ _ _ = throwError "type mismatch"

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst i r (Ann e t)  = Ann (cSubst i r e) t
iSubst i r (Bound j)  = if i == j then r else Bound j
iSubst _ _ (Free y)   = Free y
iSubst i r (e :@: e') = iSubst i r e :@: cSubst i r e'

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst i r (Inf e) = Inf (iSubst i r e)
cSubst i r (Lam e) = Lam (cSubst (i + 1) r e)