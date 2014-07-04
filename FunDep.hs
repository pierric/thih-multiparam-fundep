
module FunDep where

import Pred
import Type
import Subst
import Unify
import TIMonad
import Data.List((!!),nub,intersect)
import Data.Maybe(catMaybes,fromMaybe)
import Control.Monad(liftM,foldM)
import Debug.Trace
import PPrint

resolve :: ClassEnv -> Pred -> TI Subst
resolve ce pr@(IsIn ci _) = do 
    let fds = fundeps ce ci
    substs <- mapM resolve_fd fds
    return $ fromMaybe nullSubst (foldM merge nullSubst substs)
  where
    resolve_fd :: FunDep -> TI Subst
    resolve_fd fd = do let all_instances = insts ce ci
                       matched <- liftM catMaybes $
                                    mapM (resolve_fd_inst fd) all_instances
                       case matched of 
                         []      -> return nullSubst
                         [subst] -> return subst
                         (_:_:_) -> fail "Functional dependencies doesn't hold"
  
    resolve_fd_inst :: FunDep -> Inst -> TI (Maybe Subst)
    resolve_fd_inst fd@(fd_var :~> fd_cov) instance_ = do
        fresh_inst@(_ :=> fresh_head) <- freshInst instance_
        let maybe_subst = do -- pick up the fd_var columns in both head and pred
                             (h0, p0) <- select fd_var (fresh_head, pr)
                             -- pick up the columns of ground-type in pred
                             let (h1, p1) = ground (fresh_head, pr)
                             -- some entries in fd_var columns may have be repeated
                             -- but it does not matter
                             mgu (h0++h1) (p0++p1)
        trace ("+ " ++ pretty pr ++ " ~ " ++ pretty fresh_head) (return ())
        trace ("+ " ++ pretty (fromMaybe nullSubst maybe_subst)) (return ())
        case maybe_subst of 
          Nothing -> return Nothing
          Just subst -> do
              let (cnxt :=> head) = apply subst fresh_inst
                  go hd []        = return hd
                  go hd (pr:rest) = do s <- resolve ce pr
                                       go (apply s hd) (map (apply s) rest)
              head' <- go head cnxt
              return $ do (h, p) <- select fd_cov (pr, head')
                          mgu h p

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

freshInst :: Inst -> TI (Qual Pred)
freshInst (InstanceScheme ks it) = mapM newTVar ks >>= (return . flip inst it)