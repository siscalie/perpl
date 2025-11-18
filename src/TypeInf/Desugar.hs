module TypeInf.Desugar where

import Control.Monad.Except (runExcept)
import Control.Monad.RWS.Lazy (runRWST)
import Scope.Ctxt (emptyCtxt)
import Struct.Exprs (UsProgs)
import TypeInf.Check (CheckR(CheckR), Loc(Loc))

-- Try to desugar an entire file, running the CheckM monad
desugarFile :: UsProgs -> Either String UsProgs
desugarFile ps =
  either (\ (e, loc) -> Left (if null (show loc) then show e else show e ++ ", " ++ show loc))
         (\ (a, s, w) -> Right a)
    (runExcept (runRWST (desugarProgs ps)
                        (CheckR emptyCtxt (Loc Nothing "")) mempty))