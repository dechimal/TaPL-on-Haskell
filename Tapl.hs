import Control.Monad
import Data.List

class System t where
    isValue :: t -> Bool
    evalStep :: t -> t

eval :: System t => t -> t
eval t = if isValue t then t else eval $ evalStep t

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
            deriving (Show)
instance System Term where
    isValue TTrue = True
    isValue TFalse = True
    isValue TZero = True
    isValue (TSucc t) = isIntValue t
    isValue (TPred t) = isIntValue t
    isValue (TIsZero t) = False
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
    evalStep (TApply t1@(TAbs t') t2) | not $ isValue t2 = TApply t1 $ evalStep t2
                                      | otherwise = substitute t' t2

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

main :: IO ()
main = mapM_ print $ (flip unfoldr) (Just term) $ fmap $ \t->(t, if isValue t
                                                                 then Nothing
                                                                 else Just $ evalStep t)
    where term = TIf (TIf TTrue (TIf TFalse TTrue TFalse) TTrue)
                     (TSucc $ TSucc $ TPred TZero) $
                     TApply (TAbs $ TSucc $ TIndex 1) $ TPred TZero
