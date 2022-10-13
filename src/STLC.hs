{-
    λ🠚
    The Simply Typed Lambda Calculus 
-}
module STLC where
import Control.Monad (unless)

{-
    Abstract Syntax
-}

-- | Inferable Term
data ITerm
  = Ann CTerm Type    -- ^ Annotated term
  | Bound Int         -- ^ Bound variables represended with de Bruijn indicies
  | Free Name         -- ^ Free variables are represented by name
  | ITerm :@: CTerm   -- ^ Application represented by the infix character
  deriving (Eq, Show)

-- | Checkable term
data CTerm            
  = Inf ITerm         -- ^ Inferrable term embedded in a checkable term
  | Lam CTerm         -- ^ Lambda abstraction
  deriving (Show, Eq)

data Name
  = Global String     -- ^ Global binding
  | Local Int         -- ^ Used when converting a bound to free var when passing a binder
  | Quote Int         -- ^ When quoting a haskell representation of an abstraction
  deriving (Show, Eq)

{-| Types consist of only type identifiers or arrows. There are no bound names
    on the type level, so there is no need for a @TBound@ constructor. -}
data Type
  = TFree Name        -- ^ Type identifiers
  | Fun Type Type     -- ^ Arrow type
  deriving (Eq, Show)

-- | Values are lambda abstractions or neutral terms
data Value 
  = VLam (Value -> Value)   {-^ Function value as Haskell function ex: @const@  when evaluated
                                results in the value @VLam (\x -> VLam (\y -> x))@  -}
  | VNeutral Neutral        -- ^ Neutral term

{-| A Neutral term is either a free variable or a application of a neutral term 
    to a value. Neutral terms contain a free variable at a 'head' position. 
    Thus, they cannot be reduced any further without instantiating that variable. 
    For example, the term @x N@ where @N@ is a normal form is a neutral term: it 
    cannot be reduced unless we instantiate @x@ with a λ-abstraction. -}
data Neutral
  = NFree Name          -- ^ free variable neutral term
  | NApp Neutral Value  -- ^ application of a neutral term to a value


vfree :: Name -> Value
vfree = VNeutral . NFree 

{-
    Evaluation

    Compare the rules to in Figure 1 reveals that the implementation
    is mostly straight forward.

    Substitution is handled by passing around an environment of values. Since 
    bound variables are represented as integers, the environment is just a list
    of values where the i-th position corresponds to the value of variable @i@.
    We add a new element to the environment whenver evaluating underneath a 
    binder, and lookup the correct element using Haskell's list lookup operator
    @!!@ when we encounter a bound variable.
-}

type Env = [Value]

-- | big step evaluation of inferable terms
iEval :: ITerm -> Env -> Value
iEval (Ann e _)  d = cEval e d
iEval (Free x)   _ = vfree x
iEval (Bound i)  d = d !! i
iEval (e :@: e') d = vapp (iEval e d) (cEval e' d)

{-| For lambda functions (Lam) we introduce a Haskell function and add the 
    bound variable @x@ to the environment while evaluating the body -} 
vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

-- | big step evaluation of checkable terms
cEval :: CTerm -> Env -> Value
cEval (Inf i) d = iEval i d
cEval (Lam e) d = VLam (\x -> cEval e (x : d))

{-
    Contexts

    Contexts are implemented as revered lists associating names with either ★
    (@HasKind Star@) or a type (@HasType t@).
-}

-- | λ🠚 has only one kind for types, star, which are monomorphic types
data Kind = Star deriving (Show)

-- | Information in the context associated with a name
data Info
  = HasKind Kind 
  | HasType Type
  deriving (Show)

{-| list associating names with information about the kind (if it's a type)
    or type if it isn't -}
type Context = [(Name, Info)]

{-
    Type Checking

    The type checking algorithm can fail, and to do so gracefully, it returns
    the @Result@ monad. For simplicity, we choose a standard error monad
-}

type Result a = Either String a

-- | function for throwing error results
throwError :: String -> Result a
throwError = Left

cKind :: Context -> Type -> Kind -> Result ()
cKind ctx (TFree x) Star =
  case lookup x ctx of
    Just (HasKind Star) -> return ()
    Just _              -> throwError "assert failed"
    Nothing             -> throwError "unknown identifier"
cKind ctx (Fun kappa kappa') Star = do
  cKind ctx kappa  Star
  cKind ctx kappa' Star

iType0 :: Context -> ITerm -> Result Type
iType0 = iType 0

iType :: Int -> Context -> ITerm -> Result Type
iType i ctx (Ann e tau) = do
  cKind ctx tau Star
  cType i ctx e tau
  pure tau
iType _ ctx (Free x) =
  case lookup x ctx of
    Just (HasType t) -> return t
    Just _           -> throwError "assertion failed"
    Nothing          -> throwError "unknown identifier"
iType i ctx (e :@: e') = do
  sigma <- iType i ctx e
  case sigma of
    Fun tau tau'  -> do 
      cType i ctx e' tau
      pure tau'
    _         -> throwError "illegal application"
iType _ _ _ = throwError "assertion failed - iType"

cType :: Int -> Context -> CTerm -> Type -> Result ()
cType i ctx (Inf e) tau = do
  tau' <- iType i ctx e
  unless (tau == tau') $ throwError "type mismatch"
cType i ctx (Lam e) (Fun tau tau') =
  cType (i + 1) ((Local i, HasType tau) : ctx) (cSubst 0 (Free (Local i)) e) tau'
cType _ _ _ _ = throwError "type mismatch" 

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst i r (Ann e tau)  = Ann (cSubst i r e) tau
iSubst i r (Bound j)  = if i == j then r else Bound j
iSubst _ _ (Free y)   = Free y
iSubst i r (e :@: e') = iSubst i r e :@: cSubst i r e' 

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst i r (Inf e) = Inf (iSubst i r e)
cSubst i r (Lam e) = Lam (cSubst (i +  1) r e)

{-
    Quotation
-}

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote i (VLam fun)     = Lam (quote (i + 1) (fun (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote i (NFree x)  = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> ITerm
boundfree i (Quote k) = Bound (i - k - 1)
boundfree _ x         = Free x

{-
    Examples
-}

id' :: CTerm
id' = Lam (Inf (Bound 0))

const' :: CTerm
const' = Lam (Lam (Inf (Bound 1)))

tfree :: String -> Type
tfree α = TFree (Global α)

free :: String -> CTerm
free x = Inf (Free (Global x))

term1 :: ITerm
term1 = Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"

term2 :: ITerm
term2 = Ann const' (Fun (Fun (tfree "b") (tfree "b"))
                        (Fun (tfree "a")
                              (Fun (tfree "b") (tfree "b"))))
        :@: id' :@: free "y"

env1 :: [(Name, Info)]
env1 = [ (Global "y", HasType (tfree "a"))
       , (Global "a", HasKind Star)]

env2 :: [(Name, Info)]
env2 = (Global "b", HasKind Star) : env1