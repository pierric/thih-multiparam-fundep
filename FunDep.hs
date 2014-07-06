
module FunDep where

import Pred
import Type
import Subst
import Unify
import TIMonad
import Data.List((!!),nub,intersect)
import Data.Maybe(catMaybes,fromMaybe)
import Data.Monoid(mconcat)
import Control.Monad(liftM,foldM)
import Control.Monad.Identity
import Debug.Trace
import PPrint

resolve :: ClassEnv -> Pred -> TI Subst
resolve ce pr = do eqs <- walk' nullSubst [pr]
                   -- apply eqs to tv(pr) continuously until reaching
                   -- a fix point.
                   -- the eqs may not apply to the tv(pr) at all, in
                   -- that case, a identity substitution occurs in eqs.
                   return $ rem_id_subst $ S 
                       [(t, applyFix eqs (TVar t)) | t <- tv pr]
  where
    -- Search in a BFS way.
    walk :: Subst -> ([Pred],[Pred]) -> TI (Subst, [Pred])
    walk subst (acc_preds,[]) = return (subst, acc_preds)
    walk acc_subst (acc_preds, pr:workingqueue) = do
        (new_subst, more_preds) <- resolve_pred ce pr
        let acc_preds'    = apply new_subst (pr:acc_preds)
            workingqueue' = apply new_subst workingqueue ++ more_preds
            acc_subst'    = runIdentity (merge acc_subst new_subst)
        walk acc_subst' (acc_preds', workingqueue')

    walk' :: Subst -> [Pred] -> TI Subst
    walk' subst prs = do 
        (s,p) <- walk subst ([],prs)
        -- In following case, the resolution completes:
        -- 1. no more predicates rest
        -- 2. resolution results in the same set of predicates,
        --    which means resolution can not solve it.
        -- 3. resolution result is alpha equivalence to 
        --    input predicates to solve.
        if null p || p == prs || p `aeq` prs then
            return s
          else
            walk' s $ filter (not . null . tv) p

    -- notIn pr prs = null [x | x <- prs, pr `aeq` x]
    applyFix eqs tv = let tv' = apply eqs tv
                      in if tv' == tv then tv' else applyFix eqs tv'

resolve_pred :: ClassEnv -> Pred -> TI (Subst, [Pred])
resolve_pred ce pr@(IsIn ci _) = do
    res  <- mapM resolve_fd (fundeps ce ci)
    return $ mconcat res

  where
    resolve_fd :: FunDep -> TI (Subst, [Pred])
    resolve_fd fd = do
        matched <- mapM (resolve_fd_inst fd) (insts ce ci)
        case catMaybes matched of 
          []      -> return (nullSubst, [])
          [subst] -> return subst
          (_:_:_) -> fail "Overlapping instances."

    resolve_fd_inst :: FunDep -> Inst -> TI (Maybe (Subst, [Pred]))
    resolve_fd_inst fd@(fd_var :~> fd_cov) instance_ = do
        fresh_inst@(fresh_cnxt :=> fresh_head) <- freshInst instance_
        return $ do -- pick up the fd_var columns in both head and pred
                    (h0, p0) <- select fd_var (fresh_head, pr)
                    -- pick up the columns of ground-type in pred
                    let (h1, p1) = ground (fresh_head, pr)
                    -- some entries in fd_var columns may have be repeated
                    -- but it does not matter
                    s0 <- match (h0++h1) (p0++p1)
                    let fresh_cnxt' :=> fresh_head' = apply s0 fresh_inst
                    s1 <- match pr fresh_head'
                    return (rem_id_subst s1, fresh_cnxt')

select :: [Int] -> (Pred, Pred) -> Maybe ([Type], [Type])
select xs (IsIn i1 p1, IsIn i2 p2) 
  | i1 == i2 && m < length p1 && m < length p2 = Just (map (p1!!) xs, map (p2!!) xs)
  | otherwise = Nothing
  where m = maximum xs
  
ground :: (Pred, Pred) -> ([Type], [Type])
ground (IsIn i1 p1, IsIn i2 p2) = unzip $ filter (\(_,t2)-> null (tv t2)) (zip p1 p2)

-- fixup does following
-- removing those irrelated predicates
-- removing those predicates of none fundeps
-- removing those bad predicates, tv(fd_cov) is subset of tv(fd_var)
-- sorting the rest in dependency order
-- fixup ce (IsIn c1 tyv1) (InsIn c2 tyv2) = 

aeq :: Match a => a -> a -> Bool
aeq ty1 ty2 = fromMaybe False $ do
                S s   <- match ty1 ty2
                --trace ("> " ++ pretty s) (return s)
                let to = map (tyvar . snd) s
                return $ all isTVar (map snd s) &&
                         null (to `intersect` (map fst s)) && 
                         nub to == to
  where
    isTVar (TVar _)  = True
    isTVar _         = False
    tyvar (TVar tyv) = tyv

rem_id_subst (S subst) = S $ filter (\(x,y) -> TVar x /= y) subst

freshInst :: Inst -> TI (Qual Pred)
freshInst (InstanceScheme ks it) = mapM newTVar ks >>= (return . flip inst it)