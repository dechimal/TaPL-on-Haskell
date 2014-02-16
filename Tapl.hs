import Control.Monad
import Data.List

class System t where
    isValue :: t -> Bool
    evalStep :: t -> t

eval :: System t => t -> t
eval t = if isValue t then t else eval $ evalStep t

evalProgress :: System t => t -> [t]
evalProgress t = (flip unfoldr) (Just t)
                 $ fmap
                 $ \t'->(t', if isValue t'
                             then Nothing
                             else Just $ evalStep t')

data Term = TTrue
          | TFalse
          | TIf Term Term Term
          | TZero
          | TSucc Term
          | TPred Term
          | TIsZero Term
          | TAbs Term
          | TIndex Int
          | TApply Term Term
            deriving (Show,Eq)
instance System Term where
    isValue TTrue = True
    isValue TFalse = True
    isValue TZero = True
    isValue t@(TSucc _) = isIntValue t
    isValue t@(TPred _) = isIntValue t
    isValue (TAbs _) = True
    isValue _ = False
    evalStep (TIf TTrue t _) = t
    evalStep (TIf TFalse _ f) = f
    evalStep (TIf c t f) = TIf (evalStep c) t f
    evalStep (TIsZero TZero) = TTrue
    evalStep (TIsZero n) | isIntValue n = TFalse
                         | otherwise = TIsZero $ evalStep n
    evalStep (TSucc (TPred n)) | isIntValue n = n
    evalStep (TPred (TSucc n)) | isIntValue n = n
    evalStep (TSucc n) | not $ isIntValue n = TSucc $ evalStep n
    evalStep (TPred n) | not $ isIntValue n = TPred $ evalStep n
    evalStep (TApply t1 t2) | not $ isValue t1 = TApply (evalStep t1) t2
                            | not $ isValue t2 = TApply t1 $ evalStep t2
                            | otherwise = case t1 of (TAbs t') -> substitute t' t2

isIntValue :: Term -> Bool
isIntValue TZero = True
isIntValue (TSucc TZero) = True
isIntValue (TPred TZero) = True
isIntValue (TSucc t@(TSucc _)) = isIntValue $ t
isIntValue (TPred t@(TPred _)) = isIntValue $ t
isIntValue _ = False

substitute :: Term -> Term -> Term
substitute t1 t2 = subst' t1 t2 1
    where subst' (TIndex j) t2 i | j == i = t2
          subst' (TIf c t f) t2 i = TIf (subst' c t2 i) (subst' t t2 i) (subst' f t2 i)
          subst' (TSucc n) t2 i = TSucc $ subst' n t2 i
          subst' (TPred n) t2 i = TPred $ subst' n t2 i
          subst' (TIsZero n) t2 i = TIsZero $ subst' n t2 i
          subst' (TAbs t) t2 i = TAbs $ subst' t t2 $ i + 1
          subst' (TApply t3 t4) t2 i = TApply (subst' t3 t2 i) (subst' t4 t2 i)
          subst' t1 _ _ = t1

test :: (Eq a, Show a) => a -> a -> IO ()
test actual expected = if actual == expected
                       then return ()
                       else error $ concat [ "failed\nExpected: "
                                           , show expected
                                           , "\nActual: "
                                           , show actual]

main :: IO ()
main = forM_ (zipWith (\x y->(x, x:y)) term expected) $ \(x, y) -> test (evalProgress x) y
    where term = [ TIf (TIf TTrue (TIf TFalse TTrue TFalse) TTrue)
                       (TSucc $ TSucc $ TPred TZero) $
                       TApply (TAbs $ TSucc $ TIndex 1) $ TPred TZero
                 , TApply (TApply (TApply tst t) TTrue) $ TPred $ TSucc TZero
                 ]
          expected = [ [ TIf (TIf TFalse TTrue TFalse)
                             (TSucc $ TSucc $ TPred TZero) $
                             TApply (TAbs $ TSucc $ TIndex 1) $ TPred TZero
                       , TIf TFalse
                             (TSucc $ TSucc $ TPred TZero) $
                             TApply (TAbs $ TSucc $ TIndex 1) $ TPred TZero
                       , TApply (TAbs $ TSucc $ TIndex 1) $ TPred TZero
                       , TSucc $ TPred TZero
                       , TZero
                       ]
                     , [ TApply (TApply (TAbs $ TAbs $ TApply (TApply t $ TIndex 2) $ TIndex 1) TTrue) $ TPred $ TSucc TZero
                       , TApply (TAbs $ TApply (TApply t TTrue) $ TIndex 1) $ TPred $ TSucc TZero
                       , TApply (TAbs $ TApply (TApply t TTrue) $ TIndex 1) $ TZero
                       , TApply (TApply t TTrue) TZero
                       , TApply (TAbs TTrue) TZero
                       , TTrue
                       ]
                     ]

t = TAbs $ TAbs $ TIndex 2
f = TAbs $ TAbs $ TIndex 1
tst = TAbs
      $ TAbs
      $ TAbs
      $ TApply (TApply (TIndex 3) $ TIndex 2) $ TIndex 1
