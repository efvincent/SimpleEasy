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
vapp (VLam fn) v     = fn v
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
    the @Result@ monad. For simplicity, we choose a standard error monad.

    Note that the type equality check performed when checking an inferable term 
    is implemented by a straightforeward syntactic equality on the data @Type@.
    Our type checker doesn't perform unification.

    the code for substitution comprises of one for checkable and one for 
    inferable terms. 

-}

type Result a = Either String a

-- | function for throwing error results
throwError :: String -> Result a
throwError = Left

{-| Checks the well formedness of types
-}
cKind :: Context -> Type -> Kind -> Result ()
cKind ctx (TFree x) Star =
  case lookup x ctx of
    Just (HasKind Star) -> return ()
    Just _              -> throwError "assert failed"
    Nothing             -> throwError "unknown identifier"
cKind ctx (Fun kappa kappa') Star = do
  cKind ctx kappa  Star
  cKind ctx kappa' Star

{-| type checking functions are parameterized by a de Bruijn index indicating
    the number of binders encountered. On the initial call this is zero so
    we provide @iType0@ as a wrapper function.

    We use this integer to simulate type rules for bound variables. In the type
    rule for lambda abstraction, we add he bound variable to the context while
    checking the body. We do the same in implementation. The counter @i@ 
    indicates the number of binders we've passed, so @Local i@ is a fresh name 
    that we can associate with the bound variable. We then add @Local i@ to 
    the context @ctx@ to perform the corresponding substitution on the body. The
    type checker will never encountere a bound variable; correspondingly the 
    function @iType@ has no case for @Bound@. 
-}
iType0 :: Context -> ITerm -> Result Type
iType0 = iType 0

{-| function for inferrable terms returns a @Result Type@
-}
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

{-| function for checkable terms takes a type and returns @Result ()@
-}
cType :: Int -> Context -> CTerm -> Type -> Result ()
cType i ctx (Inf e) tau = do
  tau' <- iType i ctx e
  unless (tau == tau') $ throwError "type mismatch"
cType i ctx (Lam e) (Fun tau tau') =
  cType (i + 1) ((Local i, HasType tau) : ctx) (cSubst 0 (Free (Local i)) e) tau'
cType _ _ _ _ = throwError "type mismatch" 

{-| substitution for inferable terms. The integer argument indicates which 
    variable is to be substituted. For @Bound@ we check if the variable
    encountered is the one to be substituted.
-}
iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst i r (Ann e tau)  = Ann (cSubst i r e) tau
iSubst i r (Bound j)  = if i == j then r else Bound j
iSubst _ _ (Free y)   = Free y
iSubst i r (e :@: e') = iSubst i r e :@: cSubst i r e' 

{-| substitution for checkable terms. The integer argument indicates which 
    variable is to be substituted. In the case of @Lam@ we increase @i@ to 
    reflect that the variable to substitute is refrenced by a higher number 
    underneath the binder.
-}
cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst i r (Inf e) = Inf (iSubst i r e)
cSubst i r (Lam e) = Lam (cSubst (i +  1) r e)

{-
    Quotation

    The use of higher order abstract syntax requires us to define a @quote@ 
    function that takes a @Value@ back to a term. As the @VLam@ constructor of 
    the @Value@ data type takes a function as argument, we cannot simply derive 
    @Show@ and @Eq@ as we did for other types. Therefore as soon as we want to
    get back at the internal structure of a value, for instance to display 
    results of evaluation, we need the function @quote@.
-}

{-| initial db Bruijn index for @quote@ is zero, so we provide this wrapper 
-}
quote0 :: Value -> CTerm
quote0 = quote 0

{-| the function @quote@ takes an integer argument that counts the number of 
    binders we have traversed. If the value is a lambda abstraction, we generate 
    a fresh variable @Quote i@ and apply the Haskel function fn to this fresh 
    variable. The value resulting from this function application is then 
    quoted at level @i + 1@. We use the constructor @Quote@ that takes an 
    argument of type @Int@ here to ensure that the newly created names don't 
    clash with other names in the value.
-}
quote :: Int -> Value -> CTerm
quote i (VLam fn)     = Lam (quote (i + 1) (fn (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)

{-| if under @quote@ the value is a neutral term (hence the application of a
    free variable to a value), @neutralQuote@ quotes its arguments.
-}
neutralQuote :: Int -> Neutral -> ITerm
neutralQuote i (NFree x)  = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

{-| the @boundfree@ function checks if the variable occuring at the head of the 
    application is a @Quote@, and thus a bound variable, or a free name.
-}
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