import Control.Applicative
import Data.Maybe
import Data.Foldable(for_)

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
          | TAbs { body :: Term, typeAnno :: Type }
          | TIndex { index :: Int }
          | TApply { func :: Term, arg :: Term }
          | TAs { as :: Term, asAnno :: Type }
            deriving (Show, Eq)

data Type = TyInt
          | TyBool
          | TyAbs Type Type
          | TyAtom
            deriving (Show, Eq)

instance System Term where
    isValue TTrue {} = True
    isValue TFalse {} = True
    isValue TZero {} = True
    isValue t@TSucc {} = isIntValue t
    isValue t@TPred {} = isIntValue t
    isValue TAbs {} = True
    isValue _ = False
    evalStep TIf { cond = TTrue, true = t } = Just t
    evalStep TIf { cond = TFalse, false = t } = Just t
    evalStep TIf { cond = c, true = t, false = f } = TIf <$> evalStep c <*> pure t <*> pure f
    evalStep TIsZero { zero = TZero } = Just TTrue
    evalStep TIsZero { zero = n } | isIntValue n = Just TFalse
                                  | otherwise = TIsZero <$> evalStep n
    evalStep TSucc { unsucc = TPred { unpred = n } } | isIntValue n = Just n
    evalStep TPred { unpred = TSucc { unsucc = n } } | isIntValue n = Just n
    evalStep TSucc { unsucc = n} | not $ isValue n = TSucc <$> evalStep n
    evalStep TPred { unpred = n} | not $ isValue n = TPred <$> evalStep n
    evalStep TApply { func = t1, arg = t2 } | not $ isValue t1 = TApply <$> evalStep t1 <*> pure t2
                                            | not $ isValue t2 = TApply t1 <$> evalStep t2
                                            | TAbs { body = t' } <- t1 = let t'' = substitute t' t2 0
                                                                         in Just $ shift t'' 1 (-1)
    evalStep t@TAs { as = t' } | isValue t' = Just t'
                               | otherwise = do t'' <- evalStep t'
                                                return t { as = t'' }
    evalStep _ = Nothing

isIntValue :: Term -> Bool
isIntValue TZero = True
isIntValue TSucc { unsucc = TZero } = True
isIntValue TPred { unpred = TZero } = True
isIntValue TSucc { unsucc = t@TSucc {} } = isIntValue $ t
isIntValue TPred { unpred = t@TPred {} } = isIntValue $ t
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

deduce :: TypeEnv -> Term -> Maybe Type
deduce e (TTrue {}) = Just TyBool
deduce e (TFalse {}) = Just TyBool
deduce e (TIf { cond = c, true = t, false = f }) | d <- deduce e
                                                 , Just TyBool <- d c
                                                 , ty <- d t
                                                 , d f == ty = ty
deduce e (TZero {}) = Just TyInt
deduce e (TSucc { unsucc = z }) | ty@(Just TyInt) <- deduce e z = ty
deduce e (TPred { unpred = z }) | ty@(Just TyInt) <- deduce e z = ty
deduce e (TIsZero { zero = z }) | Just TyInt <- deduce e z = Just TyBool
deduce e (TAbs { body = t, typeAnno = ty }) | Just ty' <- deduce (ty:e) t = Just $ TyAbs ty ty'
deduce e (TApply { func = t1, arg = t2 }) | Just (TyAbs ty1 ty2) <- deduce e t1
                                          , Just ty3 <- deduce e t2
                                          , ty1 == ty3 = Just ty2
deduce e (TIndex { index = i }) | (ty:tys) <- drop i e = Just $ ty
deduce e (TAs { as = t, asAnno = ty }) | ty' <- Just ty
                                       , deduce e t == ty' = ty'
deduce _ _ = Nothing

type TypeEnv = [Type]


-- tests

test :: (Eq a, Show a) => a -> a -> IO ()
test actual expected = if actual == expected
                       then return ()
                       else error $ concat [ "failed\nExpected: "
                                           , show expected
                                           , "\nActual: "
                                           , show actual
                                           ]

test' :: (Eq b, Show b) => (a -> b) -> [(a, b)] -> IO ()
test' f xs = for_ xs $ \(t, r)->
                 test (f t) r

-- TAbsの型は適当
testSubstitute :: IO ()
testSubstitute = test actual expected
    where actual = substitute
                       (TAbs (TApply (TApply (TApply v0 v1)
                                             v2)
                                     (TAbs (TApply (TApply v0 v1) v2) TyAtom)) TyAtom)
                       (TAbs (TApply v2 v3) TyAtom)
                       0
          expected = (TAbs (TApply (TApply (TApply v0 (TAbs (TApply v3 v4) TyAtom))
                                          v2)
                                   (TAbs (TApply (TApply v0 v1) (TAbs (TApply v4 v5) TyAtom)) TyAtom)) TyAtom)
          v0 = TIndex 0
          v1 = TIndex 1
          v2 = TIndex 2
          v3 = TIndex 3
          v4 = TIndex 4
          v5 = TIndex 5

-- TAbsの型は適当
testEvalStep :: IO ()
testEvalStep = test' trace
               [ ( TIf (TIf TTrue (TIf TFalse TTrue TFalse) TTrue)
                       (TSucc $ TSucc $ TPred TZero) $
                       TApply (TAbs (TSucc $ TIndex 0) TyAtom) $ TPred TZero
                 , ( True
                   , [ TIf (TIf TFalse TTrue TFalse)
                           (TSucc $ TSucc $ TPred TZero) $
                           TApply (TAbs (TSucc $ TIndex 0) TyAtom) $ TPred TZero
                     , TIf TFalse
                           (TSucc $ TSucc $ TPred TZero) $
                           TApply (TAbs (TSucc $ TIndex 0) TyAtom) $ TPred TZero
                     , TApply (TAbs (TSucc $ TIndex 0) TyAtom) $ TPred TZero
                     , TSucc $ TPred TZero
                     , TZero
                     ]))
               , ( TApply (TApply (TApply tst t) TTrue) $ TPred $ TSucc TZero
                 , (True
                   , [ TApply (TApply (TAbs (TAbs (TApply (TApply t $ TIndex 1) $ TIndex 0) TyAtom) TyAtom) TTrue) $ TPred $ TSucc TZero
                     , TApply (TAbs (TApply (TApply t TTrue) $ TIndex 0) TyAtom) $ TPred $ TSucc TZero
                     , TApply (TAbs (TApply (TApply t TTrue) $ TIndex 0) TyAtom) $ TZero
                     , TApply (TApply t TTrue) TZero
                     , TApply (TAbs TTrue TyAtom) TZero
                     , TTrue
                     ]))
               , ( TAs (TApply (TAbs (TIndex 0) TyInt) (TSucc TZero)) TyAtom
                 , (True
                   , [ TAs (TSucc TZero) TyAtom
                     , TSucc TZero
                     ]))
               ]
    where t = TAbs (TAbs (TIndex 1) TyAtom) TyAtom
          f = TAbs (TAbs (TIndex 0) TyAtom) TyAtom
          tst = TAbs (TAbs (TAbs (TApply (TApply (TIndex 2) $ TIndex 1) $ TIndex 0) TyAtom) TyAtom) TyAtom

testDeduce :: IO ()
testDeduce = test' (deduce [])
             [ ( TApply (TApply (TAbs (TAbs (TIf (TIndex 1)
                                                 (TPred $ TSucc $ TZero)
                                                 (TApply (TAbs (TSucc $ TIndex 0)
                                                               TyInt)
                                            (TIndex 0)))
                                            TyInt)
                                      TyBool)
                                TFalse)
                        (TSucc TZero)
               , Just TyInt
               )
             , ( TAs (TAbs (TAbs (TIsZero (TApply (TIndex 0) (TIndex 1))) (TyAbs TyInt TyInt)) TyInt) (TyAbs TyInt $ TyAbs (TyAbs TyInt TyInt) TyBool)
               , Just $ TyAbs TyInt $ TyAbs (TyAbs TyInt TyInt) TyBool
               )
             ]

tests :: [IO ()]
tests = testDeduce:testSubstitute:testEvalStep:[]

main :: IO ()
main = sequence_ $ tests
