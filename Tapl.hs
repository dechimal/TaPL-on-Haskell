import Control.Applicative

class System t where
    isValue :: t -> Bool
    evalStep :: t -> Maybe t

eval :: System t => t -> Maybe t
eval t | isValue t = Just t
       | otherwise = evalStep t >>= eval

trace :: System t => t -> (Bool, [t])
trace t | isValue t = (True, [])
        | Just t' <- evalStep t = let (b, ts) = trace t'
                                  in (b, t':ts)
        | otherwise = (False, [])

data Term = TTrue {}
          | TFalse {}
          | TIf { cond :: Term, true :: Term, false :: Term }
          | TZero {}
          | TSucc { unsucc :: Term }
          | TPred { unpred :: Term }
          | TIsZero { zero :: Term }
          | TAbs { body :: Term }
          | TIndex { index :: Int }
          | TApply { func :: Term, arg :: Term }
            deriving (Show, Eq)

instance System Term where
    isValue TTrue = True
    isValue TFalse = True
    isValue TZero = True
    isValue t@(TSucc {}) = isIntValue t
    isValue t@(TPred {}) = isIntValue t
    isValue (TAbs {}) = True
    isValue _ = False
    evalStep (TIf { cond = TTrue, true = t }) = Just t
    evalStep (TIf { cond = TFalse, false = t }) = Just t
    evalStep (TIf { cond = c, true = t, false = f}) = TIf <$> evalStep c <*> pure t <*> pure f
    evalStep (TIsZero { zero = TZero }) = Just TTrue
    evalStep (TIsZero { zero = n }) | isIntValue n = Just TFalse
                                    | otherwise = TIsZero <$> evalStep n
    evalStep (TSucc { unsucc = (TPred { unpred = n })}) | isIntValue n = Just n
    evalStep (TPred { unpred = (TSucc { unsucc = n })}) | isIntValue n = Just n
    evalStep (TSucc { unsucc = n}) | not $ isValue n = TSucc <$> evalStep n
    evalStep (TPred { unpred = n}) | not $ isValue n = TPred <$> evalStep n
    evalStep (TApply { func = t1, arg = t2 }) | not $ isValue t1 = TApply <$> evalStep t1 <*> pure t2
                                             | not $ isValue t2 = TApply t1 <$> evalStep t2
                                             | (TAbs { body = t' }) <- t1 = let t'' = substitute t' t2 0
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
substitute (TIndex { index = j }) t2 i | j == i = t2
substitute t@(TAbs { body = t' }) t2 i = t { body = substitute t' (shift t2 1 1) (i+1) }
substitute (TIf { cond = c, true = t, false = f}) t2 i = TIf (substitute c t2 i) (substitute t t2 i) (substitute f t2 i)
substitute (TSucc { unsucc = n }) t2 i = TSucc $ substitute n t2 i
substitute (TPred { unpred = n }) t2 i = TPred $ substitute n t2 i
substitute (TIsZero { zero = n }) t2 i = TIsZero $ substitute n t2 i
substitute (TApply { func = t3, arg = t4 }) t2 i = TApply (substitute t3 t2 i) (substitute t4 t2 i)
substitute t1 _ _ = t1

shift :: Term -> Int -> Int -> Term
shift (TIndex { index = j }) i n | j >= i = TIndex $ j + n
shift t@(TAbs { body = t' }) i n = t { body = shift t' (i + 1) n }
shift (TIf { cond = c, true = t, false = f}) i n = TIf (shift c i n) (shift t i n) (shift f i n)
shift (TSucc { unsucc = z }) i n = TSucc $ shift z i n
shift (TPred { unpred = z }) i n = TPred $ shift z i n
shift (TIsZero { zero = z }) i n = TIsZero $ shift z i n
shift (TApply { func = t1, arg = t2 }) i n = TApply (shift t1 i n) (shift t2 i n)
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
testEvalStep = zipWith test (map trace term) expected
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
