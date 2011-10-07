-----------------------------------------------------------------------------
-- |
-- Module      :  Language.HaLex.RegExp2Fa
-- Copyright   :  (c) João Saraiva 2001,2002,2003,2004,2005
-- License     :  LGPL
--
-- Maintainer  :  jas@di.uminho.pt
-- Stability   :  provisional
-- Portability :  portable
--
-- From Regular Expressions into Non-Deterministic and Deterministic Finite Automata
--
-- Code Included in the Lecture Notes on
--         Language Processing (with a functional flavour).
--
-----------------------------------------------------------------------------

module Language.HaLex.RegExp2Fa (
                   regExp2Ndfa
                 , regExp2Dfa
                 , regExp2Ndfa'
                 ) where

import Data.List
import Language.HaLex.RegExp
import Language.HaLex.Dfa
import Language.HaLex.Ndfa
import Language.HaLex.FaOperations


-- |  Compute a 'Ndfa' from a 'RegExp'.

regExp2Ndfa :: Eq sy
            => RegExp sy     -- ^ Regular expression
            -> Ndfa Int sy   -- ^ Automaton
regExp2Ndfa er = fst (regExp2Ndfa' er 1)



-- |  Compute a 'Ndfa' from a 'RegExp'.
--    Auxiliar function threading the context: the first available int to
--    name the states

regExp2Ndfa' :: Eq sy => RegExp sy -> Int -> (Ndfa Int sy , Int)


regExp2Ndfa' Empty n = ( Ndfa [] [sa,za] [sa] [za] delta , n+2 )
  where sa = n
        za = n+1
        delta _ _ = []


regExp2Ndfa' Epsilon n = ( Ndfa [] [sa] [sa] [sa] delta , n+1 )
  where sa = n
        delta _ _ = []

regExp2Ndfa' (Literal a) n = ( Ndfa [a] [sa,za] [sa] [za] delta , n+2)
  where sa = n
        za = n+1
        delta q (Just v) | q == sa && (v == a) = [za]
        delta _ _ = []

regExp2Ndfa' (Then p q) n = ( Ndfa v' q' s' z' delta' , nq)
  where (Ndfa vp qp sp zp dp , np) = regExp2Ndfa' p n
        (Ndfa vq qq sq zq dq , nq) = regExp2Ndfa' q np
        v' = vp `union` vq
        q' = qp `union` qq
        s' = sp
        z' = zq
        delta' q2 | q2 `elem` qp = if q2 `elem` zp then dp' q2
                                                   else dp  q2
                  | otherwise   = dq q2
         where dp' q3 Nothing   = (dp q3 Nothing) `union` sq
               dp' q3 (Just aa) = dp q3 (Just aa)

regExp2Ndfa' (Or p q) n = ( Ndfa v' q' s' z' delta' , nq+1 )
  where (Ndfa vp qp sp zp dp , np) = regExp2Ndfa' p (n + 1)
        (Ndfa vq qq sq zq dq , nq) = regExp2Ndfa' q np
        v' = vp `union` vq
        s' = [n]
        z' = [nq]
        q' = s' `union` qp `union` qq `union` z'
        delta' q2 | q2 `elem` s' = dd q2
                  | q2 `elem` zp = ddp' q2
                  | q2 `elem` zq = ddq' q2
                  | q2 `elem` qp = dp q2
                  | q2 `elem` qq = dq q2
                  | otherwise    = dd'' q2
         where dd _ Nothing = sp `union` sq
               dd _ _         = []

               ddp' q3 Nothing = z' `union` (dp q3 Nothing)
               ddp' _ _       = []

               ddq' q3 Nothing = z' `union` (dq q3 Nothing)
               ddq' _ _        = []

               dd'' _ _        = []

regExp2Ndfa' (Star p) n = ( Ndfa v' q' s' z' delta' , np+1 )
  where (Ndfa vp qp sp zp dp , np) = regExp2Ndfa' p (n + 1)
        v' = vp
        s' = [n]
        z' = [np]
        q' = s'  `union` qp `union` z'
        delta' q2 | q2 `elem` s' = dd q2
                  | q2 `elem` zp = dd' q2
                  | otherwise    = dp q2
          where dd _ Nothing = sp `union` z'
                dd _ _ = []

                dd' _ Nothing = sp `union` z'
                dd' _ _ = []

-- | Compute a 'Dfa' from a 'RegExp'.
--   (via the intermediate 'Ndfa')
regExp2Dfa :: Eq sy
           => RegExp sy       -- ^ Regular expression
           -> Dfa [Int] sy    -- ^ Automaton
regExp2Dfa = ndfa2dfa . regExp2Ndfa


