import Type
import Kind
import Pred
import FunDep
import PPrint
import TIMonad
import Data.Maybe

tZ = TCon (Tycon "Z" Star)
tS = TCon (Tycon "S" (Kfun Star Star))

t0 = tZ
s  = TAp tS
t1 = s t0
t2 = s t1
t3 = s t2
t4 = s t3

tyvar_c = TVar (Tyvar "c" Star)
                 
ce  = fromJust $ cet initialEnv
  where 
    cet = let tva = Tyvar "a" Star
              tvb = Tyvar "b" Star
              tvc = Tyvar "c" Star
          in  addClass "A" [tva,tvb,tvc] [] [[0,1]:~>[2]]
          <:> addInst [Star] [] (IsIn "A" [t0, TGen 0, TGen 0])
          <:> addInst [Star,Star,Star] 
                      [IsIn "A" [TGen 0, TGen 1, TGen 2]]
                      (IsIn "A" [s (TGen 0), TGen 1, s (TGen 2)])
          <:> addClass "M" [tva,tvb,tvc] [] [[0,1]:~>[2]]                     
          <:> addInst [Star] [] (IsIn "M" [t0, TGen 0, t0])
          <:> addInst [Star, Star, Star, Star]
                      [IsIn "M" [TGen 0, TGen 1, TGen 2],
                       IsIn "A" [TGen 2, TGen 1, TGen 3]]
                      (IsIn "M" [s (TGen 0), TGen 1, TGen 3])
          <:> addClass "C" [tva,tvb,tvc] [] [[0]:~>[1,2]]
          <:> addInst [Star] [] (IsIn "C" [s (TGen 0), TGen 0, TGen 0])

ut1 = resolve ce (IsIn "C" [s tyvar_c, tInt, tyvar_c])
ut2 = resolve ce (IsIn "A" [t2, t3, tyvar_c])
ut3 = resolve ce (IsIn "M" [t3, t2, tyvar_c])

ce2 = fromJust $ cet initialEnv
  where 
    cet = let tva = Tyvar "a" Star
              tvb = Tyvar "b" Star
              tvc = Tyvar "c" Star
          in  addClass "A" [tva,tvb,tvc] [] [[0,1]:~>[2]]
          <:> addInst [Star] [] (IsIn "A" [t0, TGen 0, TGen 0])
          <:> addInst [Star,Star,Star] 
                      [IsIn "A" [TGen 0, TGen 1, TGen 2]]
                      (IsIn "A" [s (TGen 0), TGen 1, s (TGen 2)])
          <:> addClass "M" [tva,tvb,tvc] [] [[0,1]:~>[2]]                     
          <:> addInst [Star] [] (IsIn "M" [t0, TGen 0, t0])
          <:> addInst [Star, Star, Star, Star]
                      [IsIn "A" [TGen 2, TGen 1, TGen 3],
                       IsIn "M" [TGen 0, TGen 1, TGen 2]]
                      (IsIn "M" [s (TGen 0), TGen 1, TGen 3])
          <:> addClass "C" [tva,tvb,tvc] [] [[0]:~>[1,2]]
          <:> addInst [Star] [] (IsIn "C" [s (TGen 0), TGen 0, TGen 0])
ut4 = resolve ce2 (IsIn "M" [t3, t2, tyvar_c])