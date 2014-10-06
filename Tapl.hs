import Control.Applicative

class System t where
    isValue :: t -> Bool
    evalStep :: t -> Maybe t


evalProgress :: System t => t -> (Bool, [t])
evalProgress t = f t
    where f t = if isValue t
                then (True, [])
                else case evalStep t of
                       Just t' -> let (b, ts) = evalProgress t' in (b, t':ts)
                       Nothing -> (False, [])

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
            deriving (Show, Eq)

instance System Term where
    isValue TTrue = True
    isValue TFalse = True
    isValue TZero = True
    isValue t@(TSucc _) = isIntValue t
    isValue t@(TPred _) = isIntValue t
    isValue (TAbs _) = True
    isValue _ = False
    evalStep (TIf TTrue t _) = Just t
    evalStep (TIf TFalse _ f) = Just f
    evalStep (TIf c t f) = TIf <$> evalStep c <*> pure t <*> pure f
    evalStep (TIsZero TZero) = Just TTrue
    evalStep (TIsZero n) | isIntValue n = Just TFalse
                         | otherwise = TIsZero <$> evalStep n
    evalStep (TSucc (TPred n)) | isIntValue n = Just n
    evalStep (TPred (TSucc n)) | isIntValue n = Just n
    evalStep (TSucc n) | not $ isValue n = TSucc <$> evalStep n
    evalStep (TPred n) | not $ isValue n = TPred <$> evalStep n
    evalStep (TApply t1 t2) | not $ isValue t1 = TApply <$> evalStep t1 <*> pure t2
                            | not $ isValue t2 = TApply t1 <$> evalStep t2
                            | (TAbs t') <- t1 = let t'' = substitute t' t2 0
                                                in Just $ shift t'' 1 (-1)
    evalStep _ = Nothing

isIntValue :: Term -> Bool
isIntValue TZero = True
isIntValue (TSucc TZero) = True
isIntValue (TPred TZero) = True
isIntValue (TSucc t@(TSucc _)) = isIntValue $ t
isIntValue (TPred t@(TPred _)) = isIntValue $ t
isIntValue _ = False

substitute :: Term -> Term -> Int -> Term
substitute (TIndex j) t2 i | j == i = t2
substitute (TAbs t) t2 i = TAbs $ substitute t (shift t2 1 1) (i+1)
substitute (TIf c t f) t2 i = TIf (substitute c t2 i) (substitute t t2 i) (substitute f t2 i)
substitute (TSucc n) t2 i = TSucc $ substitute n t2 i
substitute (TPred n) t2 i = TPred $ substitute n t2 i
substitute (TIsZero n) t2 i = TIsZero $ substitute n t2 i
substitute (TApply t3 t4) t2 i = TApply (substitute t3 t2 i) (substitute t4 t2 i)
substitute t1 _ _ = t1

shift :: Term -> Int -> Int -> Term
shift (TIndex j) i n | j >= i = TIndex $ j + n
shift (TAbs t) i n = TAbs $ shift t (i + 1) n
shift (TIf c t f) i n = TIf (shift c i n) (shift t i n) (shift f i n)
shift (TSucc z) i n = TSucc $ shift z i n
shift (TPred z) i n = TPred $ shift z i n
shift (TIsZero z) i n = TIsZero $ shift z i n
shift (TApply t1 t2) i n = TApply (shift t1 i n) (shift t2 i n)
shift t _ _ = t

test :: (Eq a, Show a) => a -> a -> IO ()
test actual expected = if actual == expected
                       then return ()
                       else error $ concat [ "failed\nExpected: "
                                           , show expected
                                           , "\nActual: "
                                           , show actual
                                           ]

testSubstitute :: IO ()
testSubstitute = test actual expected
    where actual = substitute
                       (TAbs (TApply (TApply (TApply v0 v1)
                                             v2)
                                     (TAbs (TApply (TApply v0 v1) v2))))
                       (TAbs (TApply v2 v3))
                       0
          expected = (TAbs (TApply (TApply (TApply v0 (TAbs (TApply v3 v4)))
                                           v2)
                                   (TAbs (TApply (TApply v0 v1) (TAbs (TApply v4 v5))))))
          v0 = TIndex 0
          v1 = TIndex 1
          v2 = TIndex 2
          v3 = TIndex 3
          v4 = TIndex 4
          v5 = TIndex 5

testEvalStep :: [IO ()]
testEvalStep = zipWith test (map evalProgress term) expected
    where term = [ TIf (TIf TTrue (TIf TFalse TTrue TFalse) TTrue)
                       (TSucc $ TSucc $ TPred TZero) $
                       TApply (TAbs $ TSucc $ TIndex 0) $ TPred TZero
                 , TApply (TApply (TApply tst t) TTrue) $ TPred $ TSucc TZero
                 ]
          expected = [ (True,
                        [ TIf (TIf TFalse TTrue TFalse)
                              (TSucc $ TSucc $ TPred TZero) $
                              TApply (TAbs $ TSucc $ TIndex 0) $ TPred TZero
                        , TIf TFalse
                              (TSucc $ TSucc $ TPred TZero) $
                              TApply (TAbs $ TSucc $ TIndex 0) $ TPred TZero
                        , TApply (TAbs $ TSucc $ TIndex 0) $ TPred TZero
                        , TSucc $ TPred TZero
                        , TZero
                        ])
                     , (True,
                        [ TApply (TApply (TAbs $ TAbs $ TApply (TApply t $ TIndex 1) $ TIndex 0) TTrue) $ TPred $ TSucc TZero
                        , TApply (TAbs $ TApply (TApply t TTrue) $ TIndex 0) $ TPred $ TSucc TZero
                        , TApply (TAbs $ TApply (TApply t TTrue) $ TIndex 0) $ TZero
                        , TApply (TApply t TTrue) TZero
                        , TApply (TAbs TTrue) TZero
                        , TTrue
                        ])
                     ]

t = TAbs $ TAbs $ TIndex 1
f = TAbs $ TAbs $ TIndex 0
tst = TAbs
      $ TAbs
      $ TAbs
      $ TApply (TApply (TIndex 2) $ TIndex 1) $ TIndex 0

tests :: [IO ()]
tests = testSubstitute:testEvalStep

main :: IO ()
main = sequence_ $ tests
