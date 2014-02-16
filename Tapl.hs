
class System t where
    isValue :: t -> Bool
    evalStep :: t -> t

eval :: System t => t -> t
eval t = if isValue t then t else eval $ evalStep t

data Term = TTrue
          | TFalse
          | TIf Term Term Term
            deriving (Show)
instance System Term where
    isValue TTrue = True
    isValue TFalse = True
    isValue _ = False
    evalStep (TIf TTrue t _) = t
    evalStep (TIf TFalse _ f) = f
    evalStep (TIf c t f) = TIf (evalStep c) t f

main :: IO ()
main = print $ eval $
       TIf (TIf TTrue (TIf TFalse TTrue TFalse) TTrue)
           TTrue
           TFalse
