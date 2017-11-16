{-|
Note [Nested closure transformation for Stg]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-}

module StgNc (stgNc) where

import CoreSyn (AltCon(..))
import Id
import Unique
import VarEnv
import VarSet
import StgSyn
import UniqFM
import UniqSet

import Control.Monad (liftM, ap, mapM)

data OuterClosure = MkOuterClosure {
    oc_binder :: Id
  , oc_fvs    :: FvEnv
  }

newtype NcM a = NcM { unNcM :: OuterClosure -> a }

instance Functor NcM where
  fmap = liftM

instance Applicative NcM where
  pure = return
  (<*>) = ap

instance Monad NcM where
  return a = NcM (\_ -> a)
  NcM m >>= f = NcM (\oc -> unNcM (f (m oc)) oc)

outerClosureBinder :: NcM Id
outerClosureBinder = NcM (\oc -> oc_binder oc)

outerClosureFvs :: NcM FvEnv
outerClosureFvs = NcM (\oc -> oc_fvs oc)

initNcM :: Id -> NcM a -> a
initNcM bndr action =
  unNcM action (MkOuterClosure bndr emptyFvEnv)

inClosure :: Id -> FvEnv -> NcM a -> NcM a
inClosure bndr fvs m = NcM (\_ -> unNcM m (MkOuterClosure bndr fvs))

stgNc :: [InStgTopBinding] -> [OutStgTopBinding]
stgNc = map stgNcTopLvl

stgNcTopLvl :: InStgTopBinding -> OutStgTopBinding
stgNcTopLvl t@StgTopStringLit{} = t
stgNcTopLvl (StgTopLifted (StgNonRec bndr rhs)) =
  StgTopLifted (StgNonRec bndr (stgNcTopLvlRhs bndr rhs))
stgNcTopLvl (StgTopLifted (StgRec eqs)) =
  StgTopLifted (StgRec [ (bndr, stgNcTopLvlRhs bndr rhs) | (bndr, rhs) <- eqs ])

stgNcTopLvlRhs :: OutId -> InStgRhs -> OutStgRhs
stgNcTopLvlRhs bndr (StgRhsClosure ccs info fvs upd args body) =
  StgRhsClosure ccs info fvs upd args (initNcM bndr (stgNcExpr body))
stgNcTopLvlRhs _ rhs = rhs

stgNcExpr :: InStgExpr -> NcM OutStgExpr
stgNcExpr (StgCase scrut bndr ty alts) = do
  scrut' <- stgNcExpr scrut
  alts'  <- mapM (stgNcAlt bndr) alts
  return (StgCase scrut' bndr ty alts')
stgNcExpr (StgLet binds body) = do
  binds' <- stgNcBind binds
  body'  <- stgNcExpr body
  return (StgLet binds' body')
stgNcExpr e = return e

stgNcBind :: InStgBinding -> NcM OutStgBinding
stgNcBind (StgNonRec bndr rhs) = do
  rhs' <- stgNcRhs bndr rhs
  return (StgNonRec bndr rhs')
stgNcBind (StgRec pairs) = do
  pairs' <- mapM (\(bndr, rhs) -> do
                     rhs' <- stgNcRhs bndr rhs
                     return (bndr, rhs')
                 ) pairs
  return (StgRec pairs')

stgNcAlt :: OutId -> InStgAlt -> NcM OutStgAlt
stgNcAlt case_bndr (alt, args, rhs) = do
  rhs' <- stgNcExpr rhs
  return (alt, args, rhs')

stgNcRhs :: OutId -> InStgRhs -> NcM OutStgRhs
stgNcRhs bndr (StgRhsClosure ccs info fvs upd args body) = do
  outer_bndr <- outerClosureBinder
  outer_fvs  <- outerClosureFvs
  let fv_env = commonUpFreeVars outer_bndr outer_fvs (fvEnvFromStgFreeVars fvs)
  rhs <- inClosure bndr fv_env (stgNcExpr body)
  return (StgRhsClosure ccs info (fvEnvToStgFreeVars fv_env) upd args rhs)

stgNcRhs _ rhs = return rhs

type FvEnv = IdEnv (Id, Maybe Id)

emptyFvEnv :: FvEnv
emptyFvEnv = emptyVarEnv

isEmptyFvEnv :: FvEnv -> Bool
isEmptyFvEnv = isEmptyVarEnv

isSubFvEnv :: FvEnv -> FvEnv -> Bool
isSubFvEnv fvs1 fvs2 = isEmptyVarEnv (fvs1 `minusVarEnv` fvs2)

minusFvEnv :: FvEnv -> FvEnv -> FvEnv
minusFvEnv fv1 fv2 = fv1 `minusVarEnv` fv2

fvEnvFromStgFreeVars :: [StgFreeVar] -> FvEnv
fvEnvFromStgFreeVars fvs = mkVarEnv (concatMap all_fvs fvs)
  where
    all_fvs (StgFreeVar fv nested) =
      (fv, (fv, Nothing)) : [ (id, (id, Just fv)) | id <- nested ]

fvEnvToStgFreeVars :: FvEnv -> [StgFreeVar]
fvEnvToStgFreeVars fvs =
  map mk_stg_fv (nonDetEltsUFM (foldl mk_fvs emptyVarEnv (nonDetEltsUFM fvs)))
  where
    mk_stg_fv (id, nested) = StgFreeVar id (nonDetEltsUniqSet nested)
    union_fv (id, fv1) (_, fv2) = (id, unionVarSet fv1 fv2)

    mk_fvs :: IdEnv (Id, VarSet) -> (Id, Maybe Id) -> IdEnv (Id, VarSet)
    mk_fvs acc (id, Nothing)  = extendVarEnv_C union_fv acc id  (id,  emptyVarSet)
    mk_fvs acc (id, Just ind) = extendVarEnv_C union_fv acc ind (ind, unitVarSet id)

commonUpFreeVars :: Id -> FvEnv -> FvEnv -> FvEnv
commonUpFreeVars outer_binder outer_fvs fvs
  | not (isEmptyFvEnv outer_fvs)
  , outer_fvs `isSubFvEnv` fvs
  = let
      ref_cl = True

      effective_fvs =
        plusVarEnvList
          [ if ref_cl
            then plusVarEnv
                   (unitVarEnv outer_binder (outer_binder, Nothing))
                   (mapVarEnv (\(id, _) -> (id, Just outer_binder)) non_ind_fvs)
            else non_ind_fvs

          , ind_fvs

          , fvs `minusFvEnv` outer_fvs
          ]
    in effective_fvs
  | otherwise = fvs
  where
    fv_ind (_ ,Just{}) = True
    fv_ind _           = False

    (ind_fvs, non_ind_fvs) = partitionVarEnv fv_ind outer_fvs
