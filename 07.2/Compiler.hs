{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

--------------------------------------------------------------------------------
-- | The entry point for the compiler: a function that takes a Text
--   representation of the source and returns a (Text) representation
--   of the assembly-program string representing the compiled version
--------------------------------------------------------------------------------

module Language.Garter.Compiler ( compiler, compile, compileEnv, countVars, freeVars, typeTag, typeMask ) where

import           Prelude                  hiding (compare)
import           Control.Arrow            ((>>>))
import           Data.Maybe
import           Data.Bits                       (shift)
import qualified Data.Set                as S
-- import           Language.Garter.Utils
import           Language.Garter.Types      hiding (Tag)
import           Language.Garter.Parser     (parse)
import           Language.Garter.Checker    (check, errUnboundVar)
import           Language.Garter.Normalizer (anormal)
import           Language.Garter.Asm        (asm)

--------------------------------------------------------------------------------
compiler :: FilePath -> Text -> Text
--------------------------------------------------------------------------------
compiler f = parse f >>> check >>> anormal >>> tag >>> compile >>> asm

--------------------------------------------------------------------------------
-- | The compilation (code generation) works with AST nodes labeled by @Tag@
--------------------------------------------------------------------------------
type Tag   = (SourceSpan, Int)
type AExp  = AnfExpr Tag
type IExp  = ImmExpr Tag
type ABind = Bind    Tag

instance Located Tag where
  sourceSpan = fst

instance Located a => Located (Expr a) where
  sourceSpan = sourceSpan . getLabel

--------------------------------------------------------------------------------
-- | @tag@ annotates each AST node with a distinct Int value
--------------------------------------------------------------------------------
tag :: AnfExpr SourceSpan -> AExp
--------------------------------------------------------------------------------
tag = label

--------------------------------------------------------------------------------
compile :: AExp -> [Instruction]
--------------------------------------------------------------------------------
compile e = compileBody emptyEnv e

compileBody :: Env -> AExp -> [Instruction]
compileBody env e = funInstrs (countVars e) (compileEnv env e)

funInstrs :: Int -> [Instruction] -> [Instruction]
funInstrs n instrs = funEntry n ++ instrs ++ funExit

funEntry :: Int -> [Instruction]
funEntry n = [ IPush (Reg EBP)                       -- save caller's ebp
             , IMov  (Reg EBP) (Reg ESP)             -- set callee's ebp
             , ISub  (Reg ESP) (Const (4 * n))       -- allocate n local-vars
             , IAnd  (Reg ESP) (HexConst 0xFFFFFFF0) -- MacOS stack alignment
             ]

funExit :: [Instruction]
funExit   = [ IMov (Reg ESP) (Reg EBP)          -- restore callee's esp
            , IPop (Reg EBP)                    -- restore callee's ebp
            , IRet                              -- jump back to caller
            ]

--------------------------------------------------------------------------------
-- | @countVars e@ returns the maximum stack-size needed to evaluate e,
--   which is the maximum number of let-binds in scope at any point in e.
--------------------------------------------------------------------------------
countVars :: AnfExpr a -> Int
--------------------------------------------------------------------------------
countVars (Let _ e b _)  = max (countVars e)  (1 + countVars b)
countVars (If v e1 e2 _) = maximum [countVars v, countVars e1, countVars e2]
countVars _              = 0

--------------------------------------------------------------------------------
freeVars :: Expr a -> [Id]
--------------------------------------------------------------------------------
freeVars e = S.toList (go e)
  where
    go :: Expr a -> S.Set Id
    go (Id x _)           = S.singleton x
    go (Number _ _)       = S.empty
    go (Boolean _ _)      = S.empty
    go (If e e1 e2 _)     = S.unions (map go [e, e1, e2])
    go (App e es _)       = S.unions (map go (e:es))
    go (Let x e1 e2 _)    = S.union (go e1) (S.delete (getId x) (go e2))
    go (Lam xs e _)       = S.difference (go e) (S.fromList (getIdList xs))
    go (Prim1 _ e     _)  = go e
    go (Prim2 _ e1 e2 _)  = S.unions (map go [e1,e2])
    go (Tuple _e1 _e2 _)  = S.unions (map go [_e1, _e2])
    go (GetItem e f _)    = go e
    go (Fun f _ xs e  _)  = S.difference (go e) (S.fromList (getIdList (f:xs)))

--------------------------------------------------------------------------------
compileEnv :: Env -> AExp -> [Instruction]
--------------------------------------------------------------------------------
compileEnv env v@(Number {})     = [ compileImm env v  ]

compileEnv env v@(Boolean {})    = [ compileImm env v  ]

compileEnv env v@(Id {})         = [ compileImm env v  ]

compileEnv env e@(Let {})        = is ++ compileEnv env' body
  where
    (env', is)                   = compileBinds env [] binds
    (binds, body)                = exprBinds e

compileEnv env (Prim1 o v l)     = compilePrim1 l env o v

compileEnv env (Prim2 o v1 v2 l) = compilePrim2 l env o v1 v2

compileEnv env (If v e1 e2 l)    = IMov (Reg EAX) (immArg env v)
                                 : ICmp (Reg EAX) (repr False)
                                 : branch l IJe i1s i2s
  where
    i1s                          = compileEnv env e1
    i2s                          = compileEnv env e2

compileEnv _env (Tuple _e1 _e2 _)    = tupleAlloc (length (_e1:[_e2]))
				                    ++ tupleWrites args
    				                ++ setTag EAX TTuple
                  where
                     args = [immArg _env e | e <- (_e1:[_e2])]

compileEnv _env (GetItem _vE _f _)   = case _f of
  Zero -> tupleReadRaw (immArg _env _vE) (Const 0)
  One  -> tupleReadRaw (immArg _env _vE) (Const 1)

compileEnv _env (Lam _xs _e _l)      = IJmp  end
                                     : ILabel start
                                     : lambdaBody ys (getIdList _xs) _e
                                    ++ ILabel end
                                     : lamTuple arity start _env ys _l
  where
    ys    = freeVars (Lam _xs _e _l)
    arity = length _xs
    start = LamStart (snd _l)
    end   = LamEnd   (snd _l)

compileEnv _env (Fun _f _ _xs _e _l) = IJmp  end
                                     : ILabel start
                                     : funcBody (getId _f) ys (getIdList _xs) _e
                                    ++ ILabel end
                                     : lamTuple arity start _env ys _l
  where
    ys    = freeVars (Fun _f Infer _xs _e _l)
    arity = length _xs
    start = LamStart (snd _l)
    end   = LamEnd   (snd _l)

compileEnv _env (App _v _vs _l)      = assertArity   _env _v (length _vs)
                                    ++ tupleReadRaw (immArg _env _v) (repr(1::Int))
                                    ++ call (Reg EAX) (param _env <$> (_v:_vs))

compileImm :: Env -> IExp -> Instruction
compileImm env v = IMov (Reg EAX) (immArg env v)

compileBinds :: Env -> [Instruction] -> [(ABind, AExp)] -> (Env, [Instruction])
compileBinds env is []     = (env, is)
compileBinds env is (b:bs) = compileBinds env' (is ++ is') bs
  where
    (env', is')            = compileBind env b

compileBind :: Env -> (ABind, AExp) -> (Env, [Instruction])
compileBind env (x, e) = (env', is)
  where
    is                 = compileEnv env e
                      ++ [IMov (stackVar i) (Reg EAX)]
    (i, env')          = pushEnv x env

compilePrim1 :: Tag -> Env -> Prim1 -> IExp -> [Instruction]
compilePrim1 l env Add1   v = compilePrim2 l env Plus  v (Number 1 l)
compilePrim1 l env Sub1   v = compilePrim2 l env Minus v (Number 1 l)
compilePrim1 _ env Print  v = call (builtin "print") [param env v]

compilePrim2 :: Tag -> Env -> Prim2 -> IExp -> IExp -> [Instruction]
compilePrim2 _ env Plus    = arith     env addOp
compilePrim2 _ env Minus   = arith     env subOp
compilePrim2 _ env Times   = arith     env mulOp
compilePrim2 l env Less    = compare l env IJl
compilePrim2 l env Greater = compare l env IJg
compilePrim2 l env Equal   = compare l env IJe

immArg :: Env -> IExp -> Arg
immArg _   (Number n _)  = repr n
immArg _   (Boolean b _) = repr b
immArg env e@(Id x _)    = stackVar (fromMaybe err (lookupEnv x env))
  where
    err                  = abort (errUnboundVar (sourceSpan e) x)
immArg _   e             = panic msg (sourceSpan e)
  where
    msg                  = "Unexpected non-immExpr in immArg: " ++ show (strip e)

strip = fmap (const ())

--------------------------------------------------------------------------------
-- | Lambda
--------------------------------------------------------------------------------
lamTuple :: Int -> Label -> Env -> [Id] -> Tag -> [Instruction]
lamTuple arity start env ys l = tupleAlloc (2 + length ys)
                             ++ tupleWrites (repr arity
                                            : CodePtr start
                                            : [immArg env (Id y l) | y <- ys] )
                             ++ [ IOr (Reg EAX) (typeTag TClosure) ]

lambdaBody :: [Id] -> [Id] -> AExp -> [Instruction]
lambdaBody ys xs e = funInstrs maxStack (restore ys ++ compileEnv env e)
  where
    maxStack = envMax env + countVars e
    env      = fromListEnv bs
    bs       = zip xs [-3, -4..]
            ++ zip ys [1..]

funcBody :: Id -> [Id] -> [Id] -> AExp -> [Instruction]
funcBody f ys xs e = funInstrs maxStack (restore ys ++ compileEnv env e)
  where
    maxStack = envMax env + countVars e
    env      = fromListEnv bs
    bs       = zip [f] [-2]
            ++ zip xs [-3, -4..]
            ++ zip ys [1..]

restore :: [Id] -> [Instruction]
restore ys = concat [ copy i | (y, i) <- zip ys [1..]]
  where
    closPtr = RegOffset 8 EBP
    copy i  = tupleReadRaw closPtr (repr (i + 1))
           ++ [ IMov (stackVar i) (Reg EAX) ]

getId :: Bind a -> Id
getId (Bind x _) = x

getIdList :: [Bind a] -> [Id]
getIdList xs = case xs of
  e:es 	    -> getId e : getIdList es
  []	    -> []

--------------------------------------------------------------------------------
-- | Tuples
--------------------------------------------------------------------------------
tupleAlloc :: Int -> [Instruction]
tupleAlloc n = [ IMov (Reg EAX) (Reg ESI)
      	       , IMov (Sized DWordPtr (RegOffset 0 EAX)) (repr n)
    	       , IAdd (Reg ESI) (Const size)
    	       ]
  where
    size = 4 * makeEven (n + 1)

makeEven :: Int -> Int
makeEven n
  | n `mod` 2 == 0 = n
  | otherwise      = n + 1

tupleWrites :: [Arg] -> [Instruction]
tupleWrites args = concat (zipWith tupleWrite [1..] args)
  where
    tupleWrite i a = [ IMov (Reg EBX) a
                     , IMov (Sized DWordPtr (tupleLoc i)) (Reg EBX)
                     ]

tupleLoc :: Int -> Arg
tupleLoc i = RegOffset (4*i) EAX

tupleReadRaw :: Arg -> Arg -> [Instruction]
tupleReadRaw aE aI
  =  tupleAddr aE
  ++ [ IMov (Reg EBX) (aI)
     , IShr (Reg EBX) (Const 1)
     , IAdd (Reg EBX) (Const 1)
     , IMov (Reg EAX) (RegIndex EAX EBX)
     ]

assertArity :: Env -> IExp -> Int -> [Instruction]
assertArity env v n
  = tupleAddr (immArg env v)
 ++ [ IMov (Reg EBX) (tupleLoc 1)
    , ISar (Reg EBX) (Const 1)
    , ICmp (Reg EBX) (Const n)
    , IJne (DynamicErr ArityError)
    ]

tupleAddr :: Arg -> [Instruction]
tupleAddr a
  = [ IMov (Reg EAX) a
    , ISub (Reg EAX) (typeTag TTuple)
    , IAnd (Reg EAX) (HexConst 0xfffffff8) ]

setTag :: Reg -> Ty -> [Instruction]
setTag r ty = [ IAdd (Reg r) (typeTag ty) ]

unsetTag :: Reg -> Ty -> [Instruction]
unsetTag r ty = [ ISub (Reg r) (typeTag ty) ]

--------------------------------------------------------------------------------
-- | Arithmetic
--------------------------------------------------------------------------------
arith :: Env -> AOp -> IExp -> IExp  -> [Instruction]
--------------------------------------------------------------------------------
arith env aop v1 v2
  =  IMov (Reg EAX) (immArg env v1)
   : IMov (Reg EBX) (immArg env v2)
   : aop (Reg EAX) (Reg EBX)

addOp :: AOp
addOp a1 a2 = [ IAdd a1 a2
              , overflow
              ]

subOp :: AOp
subOp a1 a2 = [ ISub a1 a2
              , overflow
              ]

mulOp :: AOp
mulOp a1 a2 = [ ISar a1 (Const 1)
              , IMul a1 a2
              , overflow
              ]

overflow :: Instruction
overflow = IJo (DynamicErr ArithOverflow)

--------------------------------------------------------------------------------
-- | Comparisons
--------------------------------------------------------------------------------
-- | @compare v1 v2@ generates the instructions at the
--   end of which EAX is TRUE/FALSE depending on the comparison
--------------------------------------------------------------------------------
compare :: Tag -> Env -> COp -> IExp -> IExp -> [Instruction]
compare l env j v1 v2
   = IMov (Reg EAX) (immArg env v1)
   : IMov (Reg EBX) (immArg env v2)
   : ICmp (Reg EAX) (Reg EBX)
   : boolBranch l j

--------------------------------------------------------------------------------
-- | Assignment
--------------------------------------------------------------------------------
assign :: (Repr a) => Reg -> a -> Instruction
assign r v = IMov (Reg r) (repr v)

--------------------------------------------------------------------------------
-- | Function call
--------------------------------------------------------------------------------
call :: Arg -> [Arg] -> [Instruction]
call f args
  =    ISub (Reg ESP) (Const (4 * k))
  :  [ IPush a | a <- reverse args ]
  ++ [ ICall f
     , IAdd (Reg ESP) (Const (4 * (n + k)))  ]
  where
    n = length args
    k = 4 - (n `mod` 4)

param :: Env -> IExp -> Arg
param env v = Sized DWordPtr (immArg env v)

--------------------------------------------------------------------------------
-- | Branching
--------------------------------------------------------------------------------
branch :: Tag -> COp -> [Instruction] -> [Instruction] -> [Instruction]
branch l j falseIs trueIs = concat
  [ [ j lTrue ]
  , falseIs
  , [ IJmp lDone
    , ILabel lTrue  ]
  , trueIs
  , [ ILabel lDone ]
  ]
  where
    lTrue = BranchTrue i
    lDone = BranchDone i
    i     = snd l

boolBranch :: Tag -> COp -> [Instruction]
boolBranch l j = branch l j [assign EAX False] [assign EAX True]

type AOp = Arg -> Arg -> [Instruction]
type COp = Label -> Instruction

stackVar :: Int -> Arg
stackVar i = RegOffset (-4 * i) EBP

--------------------------------------------------------------------------------
-- | Representing Values
--------------------------------------------------------------------------------

class Repr a where
  repr :: a -> Arg

instance Repr Bool where
  repr True  = HexConst 0xffffffff
  repr False = HexConst 0x7fffffff

instance Repr Int where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Integer where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Field where
  repr Zero = repr (0 :: Int)
  repr One  = repr (1 :: Int)

typeTag :: Ty -> Arg
typeTag TNumber   = HexConst 0x00000000
typeTag TBoolean  = HexConst 0x7fffffff
typeTag TTuple    = HexConst 0x00000001
typeTag TClosure  = HexConst 0x00000005

typeMask :: Ty -> Arg
typeMask TNumber  = HexConst 0x00000001
typeMask TBoolean = HexConst 0x7fffffff
typeMask TTuple   = HexConst 0x00000007
typeMask TClosure = HexConst 0x00000007
