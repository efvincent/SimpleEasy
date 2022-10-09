module Lambda where

data ITerm
  = Ann CTerm Type
  | Bound Int
  | Free Name
  | ITerm :@: CTerm
  deriving (Show, Eq)

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

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

