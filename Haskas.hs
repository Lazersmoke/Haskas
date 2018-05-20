{-# LANGUAGE OverloadedStrings #-}
module Haskas where
import Data.String
import Data.List
import qualified Data.Set as Set

data Term = Term String | BranchTerm String [Term] deriving Ord

instance IsString Term where
  fromString = Term

instance Show Term where
  show (Term s) = s
  show (BranchTerm s l) = if length l == 2
    then "{" ++ show (l !! 0) ++ s ++ show (l !! 1) ++ "}"
    else s ++ show l

instance Eq Term where
  (Term a) == (Term b) = a == b
  (BranchTerm a xs) == (BranchTerm b ys) = a == b && xs == ys
  _ == _ = False

main :: IO ()
main = putStrLn . showProp . logicReduceQuantification $ testTerm

testTerm :: Prop
testTerm = ForAll (\_ -> Top)

elementOf :: Term -> Term -> Prop
elementOf x s = Judgement $ BranchTerm "∈" [x,s]

data Prop = ForAll (Term -> Prop) | Judgement Term | Equals Term Term | Top | LogicAnd Prop Prop | LogicNot Prop

recurProp :: (Prop -> Prop) -> Prop -> Prop
recurProp f (ForAll p) = f $ ForAll (f . p)
recurProp f (LogicAnd a b) = f $ LogicAnd (f a) (f b)
recurProp f (LogicNot p) = f $ LogicNot (f p)
recurProp _ p = p

instance IsString Prop where
  fromString = Judgement . Term

variables :: [String]
variables = map (:[]) "xyzuvwabc"

decidablyEqual :: Prop -> Prop -> Bool
decidablyEqual (Judgement a) (Judgement b) = a == b
decidablyEqual Top Top = True
decidablyEqual (LogicAnd a b) (LogicAnd c d) = decidablyEqual a c && decidablyEqual b d
decidablyEqual (Equals a b) (Equals c d) = a == c && b == d
decidablyEqual (LogicNot a) (LogicNot b) = decidablyEqual a b
decidablyEqual _ _ = False


instance Show Prop where
  show = showProp

showProp :: Prop -> String
showProp = showProp' 0
  where
    showProp' :: Int -> Prop -> String
    showProp' i (ForAll p) = let v = variables !! i in "∀" ++ v ++ "." ++ showProp' (i + 1) (p (Term v))
    showProp' _ (Judgement t) = show t
    showProp' _ Top = "⊤"
    showProp' i (LogicAnd (LogicNot (LogicAnd a (LogicNot b))) (LogicNot (LogicAnd c (LogicNot d)))) | decidablyEqual a d && decidablyEqual c b = "(" ++ showProp' i a ++ "⇔" ++ showProp' i b ++ ")"
    showProp' i (LogicAnd a b) = "(" ++ showProp' i a ++ "∧" ++ showProp' i b ++ ")"
    showProp' i (LogicNot (LogicAnd (LogicNot a) (LogicNot b))) = "(" ++ showProp' i a ++ "∨" ++ showProp' i b ++ ")"
    showProp' i (LogicNot (LogicAnd a (LogicNot b))) = "(" ++ showProp' i a ++ "⇒" ++ showProp' i b ++ ")"
    showProp' i (LogicNot p@(LogicAnd _ _)) = "¬" ++ showProp' i p
    showProp' i (LogicNot (Equals a b)) = "(" ++ show a ++ "≠" ++ show b ++ ")"
    showProp' i (LogicNot p) = "¬(" ++ showProp' i p ++ ")"
    showProp' i (Equals a b) | a == b = showProp' i Top
    showProp' _ (Equals a b) = "(" ++ show a ++ "=" ++ show b ++ ")"
  --show Bot = "⊥"
  --show (LogicOr a b) = show a ++ "∨" ++ show b
  --show (Exists b p) = "∃" ++ show b ++ "." ++ show p

dequantify :: Prop -> Prop
dequantify (ForAll p) = dequantify (p "dummy")
dequantify p = p

logicReduceQuantification :: Prop -> Prop
logicReduceQuantification p = case dequantify p of
  Top -> Top
  _ -> p

freeVariables :: Prop -> Set.Set Term
freeVariables = fv 0
  where
    fv :: Int -> Prop -> Set.Set Term
    fv i (ForAll p) = Set.delete (Term $ variables !! i) $ fv (i + 1) (p (Term $ variables !! i))
    fv _ (Judgement t) = Set.singleton t
    fv _ Top = Set.empty
    fv i (LogicAnd a b) = Set.union (fv i a) (fv i b)
    fv i (LogicNot p) = fv i p

-- fa x,y: (xVy)V-(xVy)
-- xVy = -(-x^-y)
logicOr :: Term -> Term -> Term
logicOr a b = BranchTerm "∨" [a,b]

logicOrDef :: Prop
logicOrDef = ForAll $ \x -> (ForAll $ \y -> iff (Judgement $ logicOr x y) (constOr x y))
  where
    constOr a b = LogicNot (LogicAnd (LogicNot $ Judgement a) (LogicNot $ Judgement b))

data Defeq = Term := Term

iff :: Prop -> Prop -> Prop
iff a b = LogicAnd (impl a b) (impl b a)

impl :: Prop -> Prop -> Prop
impl p q = LogicNot (LogicAnd p (LogicNot q))

exists :: (Term -> Prop) -> Prop
exists f = LogicNot (ForAll $ \x -> LogicNot (f x))

orProp :: Prop -> Prop -> Prop
orProp a b = LogicNot (LogicAnd (LogicNot a) (LogicNot b))

unionDef :: Prop
unionDef = forAllIn "Set" $ \s -> forAllIn "Set" $ \a -> forAllIn "Set" $ \b -> iff (ForAll $ \x -> iff (elementOf x s) (LogicAnd (elementOf x a) (elementOf x b))) (Equals s (BranchTerm "∪" [a,b]))

excludedMiddle :: Prop -> Prop
excludedMiddle p = orProp p (LogicNot p)

projLAnd :: Prop -> Prop -> Prop
projLAnd a b = impl (LogicAnd a b) a

projRAnd :: Prop -> Prop -> Prop
projRAnd a b = impl (LogicAnd a b) b

commuteAnd :: Prop -> Prop -> Prop
commuteAnd a b = iff (LogicAnd a b) (LogicAnd b a)

decidedAnd :: Prop -> Prop
decidedAnd (LogicAnd Top Top) = Top
decidedAnd p = p

forAllIn :: Term -> (Term -> Prop) -> Prop
forAllIn s f = ForAll $ \x -> impl (elementOf x s) (f x)

extensionality :: Prop
extensionality = forAllIn "Set" $ \a -> forAllIn "Set" $ \b -> iff (Equals a b) (ForAll $ \x -> iff (elementOf x a) (elementOf x b))

-- x impl y := yV-x
--logicImply :: Prop
--logicImply = ForAll "x" (ForAll "y" ()
  --where
    --stmt = Judgement (BranchTerm "Impl" ["x","y"])
