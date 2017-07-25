{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}

--------------------------------------------------------------------------------
-- | This module contains the code for Static Checking an `Expr`
--------------------------------------------------------------------------------
module Language.Garter.Checker
  ( -- * Top-level Static Checker
    check

    -- * Error Constructors
  , errUnboundVar
  , errUnboundFun

    -- * To silence unused var warnings
  , errSignature
  , errMismatch
  , freshFun
  , eqPoly
  , extTypesEnv

  ) where


import           Data.Maybe (fromMaybe)
import qualified Data.Map          as M
import qualified Data.List         as L
import qualified Control.Exception as Ex
import           Text.Printf        (printf)
import           Language.Garter.Types
import           Language.Garter.Utils
-- import           Debug.Trace (trace)

--------------------------------------------------------------------------------
check :: Bare -> Bare
--------------------------------------------------------------------------------
check p = case wellFormed p of
            [] -> typeCheck p
            es -> Ex.throw es

--------------------------------------------------------------------------------
-- | `wellFormed e` returns the list of errors for an expression `e`
--------------------------------------------------------------------------------
wellFormed :: Bare -> [UserError]
wellFormed = go emptyEnv
  where
    gos                       = concatMap . go
    go _    (Boolean {})      = []
    go _    (Number  n     l) = largeNumberErrors      n l
    go vEnv (Id      x     l) = unboundVarErrors  vEnv x l
    go vEnv (Prim1 _ e     _) = go  vEnv e
    go vEnv (Prim2 _ e1 e2 _) = gos vEnv [e1, e2]
    go vEnv (If   e1 e2 e3 _) = gos vEnv [e1, e2, e3]
    go vEnv (Let x e1 e2   _) = duplicateBindErrors vEnv x
                             ++ go vEnv e1
                             ++ go (addEnv x vEnv) e2
    go vEnv (Tuple e1 e2   _) = gos vEnv [e1, e2]
    go vEnv (GetItem e1 _ _)  = go  vEnv e1
    go vEnv (App e es      _) = gos vEnv (e:es)
    go vEnv (Lam xs e      _) = duplicateParamErrors xs
                             ++ go (addsEnv xs vEnv) e
    go vEnv (Fun f _ xs e  _) = duplicateParamErrors xs
                             ++ go (addsEnv (f:xs) vEnv) e

addsEnv :: [BareBind] -> Env -> Env
addsEnv xs env = L.foldl' (flip addEnv) env xs

--------------------------------------------------------------------------------
-- | Error Checkers: In each case, return an empty list if no errors.
--------------------------------------------------------------------------------
duplicateParamErrors :: [BareBind] -> [UserError]
duplicateParamErrors xs
  = map (errDupParam . head)
  . dupBy bindId
  $ xs

duplicateBindErrors :: Env -> BareBind -> [UserError]
duplicateBindErrors vEnv x
  = condError (memberEnv (bindId x) vEnv) (errDupBind x)

largeNumberErrors :: Integer -> SourceSpan -> [UserError]
largeNumberErrors n l
  = condError (n < -maxInt || maxInt <= n) (errLargeNum l n)

maxInt :: Integer
maxInt = 1073741824

unboundVarErrors :: Env -> Id -> SourceSpan -> [UserError]
unboundVarErrors vEnv x l
  = condError (not (memberEnv x vEnv)) (errUnboundVar l x)

--------------------------------------------------------------------------------
-- | Error Constructors
--------------------------------------------------------------------------------

condError :: Bool -> UserError -> [UserError]
condError True  e = [e]
condError False _ = []

errDupParam     x  = mkError (printf "Duplicate parameter '%s'" (bindId x)) (sourceSpan x)
errDupBind      x  = mkError (printf "Shadow binding '%s'" (bindId x))      (sourceSpan x)
errLargeNum   l n  = mkError (printf "Number '%d' is too large" n) l
errUnboundVar l x  = mkError (printf "Unbound variable '%s'" x) l
errUnboundFun l f  = mkError (printf "Function '%s' is not defined" f) l
errUnify l t1 t2   = mkError (printf "Type error: cannot unify %s and %s" (show t1) (show t2)) l
errSignature l t   = mkError (printf "Type error: malformed function signature %s" (show t)) l
errMismatch l s s' = mkError (printf "Type error: mismatched function signature: specified %s but inferred %s" (show s) (show s')) l
errOccurs l a t    = mkError (printf "Type error: occurs check fails: %s occurs in %s" (show a) (show t)) l

--------------------------------------------------------------------------------
typeCheck :: (Located a) => Expr a -> Expr a
--------------------------------------------------------------------------------
typeCheck e = case show t of
                _:_ -> e
                _   -> error "Impossible"
  where
    t       = typeInfer env0 e
    env0    = TypeEnv M.empty

_showType :: Expr a -> Type -> IO ()
_showType e t = putStrLn $ pprint e ++ " :: " ++ show t

--------------------------------------------------------------------------------
typeInfer :: (Located a) => TypeEnv -> Expr a -> Type
--------------------------------------------------------------------------------
typeInfer env e = apply su t
  where
    (su, t)     = ti env empSubst e

--------------------------------------------------------------------------------
ti :: (Located a) => TypeEnv -> Subst -> Expr a -> (Subst, Type)
--------------------------------------------------------------------------------

-- For numbers and booleans, we just return
-- the respective type and the input `Subst`
-- without any modifications

ti _ su   (Number {})      = (su, TInt)

ti _ su   (Boolean {})     = (su, TBool)


-- For identifiers, we
-- 1. lookup their type in the `env` and
-- 2. instantiate type-variables to get different types at different uses.

ti env su (Id x l)         = instantiate su (lookupTypeEnv (sourceSpan l) x env)

-- the following cases reduce to special "function applications", handled by instApp
ti env su (If e1 e2 e3 l)  = instApp (sourceSpan l) env su ifPoly [e1, e2, e3]

ti env su (Prim1 p e l)    = instApp (sourceSpan l) env su (prim1Poly p) [e]

ti env su (Prim2 p e e' l) = instApp (sourceSpan l) env su (prim2Poly p) [e,e']

ti env su (Tuple e e' l)   = instApp (sourceSpan l) env su tupPoly [e, e']

ti env su (GetItem e f l)  = instApp (sourceSpan l) env su (fieldPoly f) [e]

-- Trusted function: just add x := s to the env and use it to check `e`
ti env su (Let x (Fun _ (Assume s) _ _ _) e _)
                           = ti env' su e
  where
    env'                   = extTypeEnv (bindId x) s env

-- For let-binders
-- 1. **Infer** the type `t1` for `e1`,
-- 2. **Apply** the substitutions from (1) to the `env`,
-- 3. **Generalize** `t1` to make it a `Poly` type `s1`,
-- 4. **Extend** the env to map `x` to `s1` and,
-- 5. **Infer** the type of `e2` in the extended environment

ti env su (Let x e1 e2 _)  = ti env'' su1 e2
  where
    env''                  = extTypeEnv (bindId x) s1 env'
    (su1, t1)              = ti env su e1
    env'                   = apply su1 env
    s1                     = generalize env' t1

-- For function calls (applications)
-- 1. **Infer** the type `t1` for `e1`,
-- 2. **Apply** the substitutions from (1) to the `env`,
-- 3. **Generalize** `t1` to make it a `Poly` type `s1`,
-- 4. **Extend** the env to map `x` to `s1` and,
-- 5. **Infer** the type of `e2` in the extended environment.
-- steps 3-6 factored into `tiApp` so we can reuse it for primitive operations

ti env su (App eF eArgs l) = tiApp (sourceSpan l) sF (apply sF env) tF eArgs
  where
    (sF, tF)               = ti env su eF

-- For lambda-definitions
-- 1. Generate a *function type* with fresh variables for the
   -- unknown inputs (`tXs`) and output (`tOut`),
-- 2. Extend the `env` so the parameters `xs` have types `tXs`,
-- 3. Infer the type of `body` under the extended `env'` as `tBody`,
-- 4. Unify the *expected* output `tOut` with the *actual* `tBody`
-- 5. Apply the substitutions to infer the function's type `tXs :=> tOut`.

--ti _env _su (Lam _xs _body _l) = error "TBD:ti:lam"

ti env su (Lam xs body l) = (su3, apply su3 (tXs :=>tOut))   -- (5)
  where
    (su1, tXs :=> tOut) = freshFun su (length xs)           -- (1)
    env'                = extTypesEnv env (zip xs tXs)      -- (2)
    (su2, tBody)        = ti env' su1 body                  -- (3)
    su3                 = unify (sourceSpan l) su2 tBody (apply su2 tOut)  -- (4)


-- HINT: this is just like Lam except you have to figure out what
-- type "f" should have when checking the body "e"

--ti _env _su (Fun _f Infer _xs _e _) = error "TBD:ti:fun:infer"
ti env su (Fun f Infer xs e l) = (su3, apply su3 (tXs :=>tOut))   -- (5)
  where
    (su1, tXs :=> tOut) = freshFun su (length (f:xs))           -- (1)
    env'                = extTypesEnv env (zip (f:xs) tXs)      -- (2)
    (su2, tBody)        = ti env' su1 e                  -- (3)
    su3                 = unify (sourceSpan l) su2 tBody (apply su2 tOut)  -- (4)

-- HINT: this is hard, super EXTRA CREDIT.
ti _env _su (Fun _f (Check _s) _xs _e _) = error "TBD:ti:0fun:check"

ti _ _ e = panic "ti:dead code (ignore me)" (sourceSpan (getLabel e))

extTypesEnv :: TypeEnv -> [(Bind a, Type)] -> TypeEnv
extTypesEnv = foldr (\(x, t) -> extTypeEnv (bindId x) (Forall [] t))

freshFun :: Subst -> Int -> (Subst, Type)
freshFun su arity    = (su', tXs :=> tOut)
  where
    (su' , tOut:tXs) = freshTVars su (1 + arity)

eqPoly  :: Poly -> Poly -> Bool
eqPoly = error "TBD:HINT for ti:fun:check"

-----------------------------------------------------------------------------------------------
instApp :: (Located a) => SourceSpan -> TypeEnv -> Subst -> Poly -> [Expr a] -> (Subst, Type)
-----------------------------------------------------------------------------------------------
instApp sp env su sF       = tiApp sp su' env tF
  where
    (su', tF)              = instantiate su sF

-----------------------------------------------------------------------------------------------
tiApp :: (Located a) => SourceSpan -> Subst -> TypeEnv -> Type -> [Expr a] -> (Subst, Type)
-----------------------------------------------------------------------------------------------
tiApp sp su env tF eIns   = (su''', apply su''' tOut)
  where
    (su' , tIns)          = L.mapAccumL (ti env) su eIns
    (su'', tOut)          = freshTVar su'
    su'''                 = unify sp su'' tF (tIns :=> tOut)


prim1Poly :: Prim1 -> Poly
prim1Poly Add1  = Forall [   ] ([TInt] :=> TInt)
prim1Poly Sub1  = Forall [   ] ([TInt] :=> TInt)
prim1Poly Print = Forall ["a"] ([ "a"] :=> "a")

prim2Poly :: Prim2 -> Poly
prim2Poly Plus    = Forall [   ] ([TInt, TInt] :=> TInt)
prim2Poly Minus   = Forall [   ] ([TInt, TInt] :=> TInt)
prim2Poly Times   = Forall [   ] ([TInt, TInt] :=> TInt)
prim2Poly Less    = Forall [   ] ([TInt, TInt] :=> TBool)
prim2Poly Greater = Forall [   ] ([TInt, TInt] :=> TBool)
prim2Poly Equal   = Forall [   ] ([TInt, TInt] :=> TBool)

tupPoly, ifPoly :: Poly
tupPoly           = Forall ["a", "b"] ([TPair ("a") ("b")] :=> TPair ("a") ("b"))
ifPoly            = Forall ["a"] ([TBool, "a", "a"] :=> "a")

fieldPoly :: Field -> Poly
fieldPoly Zero    = Forall ["a", "b"] ([TPair ("a") ("b")] :=> "a")
fieldPoly One     = Forall ["a", "b"] ([TPair ("a") ("b")] :=> "b")

--------------------------------------------------------------------------------
unify :: SourceSpan -> Subst -> Type -> Type -> Subst
--------------------------------------------------------------------------------
unify sp su (ls :=> r) (ls' :=> r')
  | length ls == length ls'           = s2
  where
    s1                                = unifys sp su ls ls'
    s2                                = unify sp s1 (apply s1 r) (apply s1 r')

unify _sp _su (TCtor _c _ts) (TCtor _c' _ts') =
  if (_c == _c') then unifys _sp _su _ts _ts'
  else abort (errUnify _sp _c _c')

unify _sp _su (TPair _s1 _s2) (TPair _t1 _t2) = error "TBD:unify:pair"

unify sp su (TVar a) t                  = varAsgn sp su a t
unify sp su t (TVar a)                  = varAsgn sp su a t
unify _ su TInt TInt                    = su
unify _ su TBool TBool                  = su
unify sp _  t1 t2                       = abort (errUnify sp t1 t2)

-- | `unifys` recursively calls `unify` on *lists* of types:
unifys :: SourceSpan -> Subst -> [Type] -> [Type] -> Subst
unifys sp su (t:ts) (t':ts') = unifys sp su' (apply su' ts) (apply su' ts')
  where
    su'                      = unify sp su t t'
unifys _  su []     []       = su
unifys sp _  _      _        = panic "unifys: dead code" sp

_unify sp env su t1 t2 = traceShow ("MGU: env = " ++ show env ++ " t1 = " ++ show t1 ++ ", t2 = " ++ show t2) su'
  where
    su'           = unify sp su t1 t2

--------------------------------------------------------------------------------
-- | `varAsgn su a t` extends `su` with `[a := t]` if **required** and **possible**!
varAsgn :: SourceSpan -> Subst -> TVar -> Type -> Subst
--------------------------------------------------------------------------------
varAsgn sp su a t
  | t == TVar a          =  su
  | a `elem` freeTvars t =  abort (errOccurs sp a t)
  | otherwise            =  extSubst su a t

--------------------------------------------------------------------------------
generalize :: TypeEnv -> Type -> Poly
--------------------------------------------------------------------------------
generalize env t = Forall as t
  where
    as           = L.nub (tvs L.\\ evs)
    tvs          = freeTvars t
    evs          = freeTvars env

--------------------------------------------------------------------------------
instantiate :: Subst -> Poly -> (Subst, Type)
--------------------------------------------------------------------------------
instantiate su (Forall as t) = (su', apply suInst t)
  where
    (su', as')               = freshTVars su (length as)
    suInst                   = mkSubst (zip as as')

--------------------------------------------------------------------------------
-- | Environments --------------------------------------------------------------
--------------------------------------------------------------------------------

newtype TypeEnv = TypeEnv (M.Map Id Poly)

extTypeEnv :: Id -> Poly -> TypeEnv -> TypeEnv
extTypeEnv x s (TypeEnv env) =  TypeEnv $ M.insert x s env
  where
    _env  = traceShow _msg _env
    _msg  = "extTypeEnv: " ++ show x ++ " := " ++ show s

lookupTypeEnv :: SourceSpan -> Id -> TypeEnv -> Poly
lookupTypeEnv l x (TypeEnv env) = fromMaybe err  (M.lookup x env)
  where
    err                         = abort (errUnboundVar l x)

--------------------------------------------------------------------------------
-- | Substitutions -------------------------------------------------------------
--------------------------------------------------------------------------------
data Subst   = Su { suMap :: M.Map TVar Type
                  , suCnt :: !Int
                  }

empSubst :: Subst
empSubst =  Su M.empty 0

extSubst :: Subst -> TVar -> Type -> Subst
extSubst su a t = su { suMap = M.insert a t su' }
  where
     su'        = apply (mkSubst [(a, t)]) (suMap su)


mkSubst :: [(TVar, Type)] -> Subst
mkSubst ats = Su (M.fromList ats) 666

unSubst :: [TVar] -> Subst -> Subst
unSubst as su = su { suMap = foldr M.delete (suMap su) as }

freshTVars :: Subst -> Int -> (Subst, [Type])
freshTVars su n = L.mapAccumL (\a _ -> freshTVar a) su (replicate n ())

freshTVar :: Subst -> (Subst, Type)
freshTVar su = (su', TVar (TV ("a" ++ show i)))
  where
    (su', i) = fresh su

fresh :: Subst -> (Subst, Int)
fresh su  = (su {suCnt = n + 1}, n) where n = suCnt su

--------------------------------------------------------------------------------
-- Applying Substitutions ------------------------------------------------------
--------------------------------------------------------------------------------

class Substitutable a where
  apply     :: Subst -> a -> a
  freeTvars :: a -> [TVar]

instance Substitutable Type where
  apply _  TInt            = TInt
  apply _  TBool           = TBool
  apply su t@(TVar a)      = M.findWithDefault t a (suMap su)
  apply su (ts :=> t)      = apply su ts :=> apply su t
  apply su (TPair t1 t2)   = TPair (apply su t1) (apply su t2)
  apply su (TCtor c ts)    = TCtor c (apply su ts)

  freeTvars TInt           = []
  freeTvars TBool          = []
  freeTvars (TVar a)       = [a]
  freeTvars (ts :=> t)     = freeTvars ts ++ freeTvars t
  freeTvars (TPair t1 t2)  = freeTvars t1 ++ freeTvars t2
  freeTvars (TCtor _ ts)   = freeTvars ts

instance Substitutable Poly where
 apply s   (Forall as t) = Forall as $ apply (unSubst as s)  t
 freeTvars (Forall as t) = freeTvars t L.\\ as

instance (Functor t, Foldable t, Substitutable a) => Substitutable (t a) where
  apply     = fmap . apply
  freeTvars = foldr (\x r -> freeTvars x ++ r) []

instance Substitutable TypeEnv where
  apply s   (TypeEnv env) =  TypeEnv   (apply s <$> env)
  freeTvars (TypeEnv env) =  freeTvars (M.elems     env)

--------------------------------------------------------------------------------
-- Printing Types --------------------------------------------------------------
--------------------------------------------------------------------------------

instance Show Subst where
  show (Su m n) = show (m, n)

instance Show TypeEnv where
  showsPrec x (TypeEnv m) = showsPrec x (M.toList m)

instance Ex.Exception String where
