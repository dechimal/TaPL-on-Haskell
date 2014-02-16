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
            deriving (Show)
instance System Term where
    isValue TTrue = True
    isValue TFalse = True
    isValue TZero = True
    isValue (TSucc t) = isIntValue t
    isValue (TPred t) = isIntValue t
    isValue (TIsZero t) = False
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

isIntValue :: Term -> Bool
isIntValue TZero = True
isIntValue (TSucc TZero) = True
isIntValue (TPred TZero) = True
isIntValue (TSucc t@(TSucc _)) = isIntValue $ t
isIntValue (TPred t@(TPred _)) = isIntValue $ t
isIntValue _ = False

main :: IO ()
main = mapM_ print $ (flip unfoldr) (Just term) $ fmap $ \t->(t, if isValue t
                                                                 then Nothing
                                                                 else Just $ evalStep t)
    where term = TIf (TIf TTrue (TIf TFalse TTrue TFalse) TTrue)
                     (TSucc $ TSucc $ TPred TZero) $
                     TIsZero $ TSucc $ TSucc $ TPred $ TSucc TZero
