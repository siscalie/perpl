module TypeInf.Desugar where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad (zipWithM_)
import Control.Monad.Except (MonadError(throwError), runExcept)
import Control.Monad.RWS.Lazy (RWST(runRWST))
import Data.List (intercalate)
import Scope.Subst (Subst(tmVars, tpVars, tags), STerm(Replace), FreeVars(freeTmVars, freeTpVars), subst, freeVars, freeDatatypes, substTags)
import Scope.Free (robust, positive, isAff)
import Scope.Fresh (newVar)
import Scope.Ctxt (Ctxt, emptyCtxt, ctxtLookupType2, ctxtAddData)
import Struct.Exprs (SProgs, UsProgs, UsProgs(UsProgs), Case(..), CaseUs(..), Ctor(..), Term(TmCase), Type(TpData), UsTm(UsCase))
import Struct.Helpers (sortCases, typeof)
import TypeInf.Check (anyDupDefs, constrain, constrainIf, freshTag, freshTp, guardM, inEnvs, infer, localCurExpr, lookupCtorType,
    CheckM, CheckR(CheckR), Constraint(Robust, Unify), Loc(Loc), TypeError(WrongNumArgs, WrongNumCases, MissingCases) )
import TypeInf.Solve
import Util.Graph (scc, SCC(..))
import Util.Helpers (listDifference, pickyZip)

{-
Let's de-sugar in a new mini-phase!
1. Read through a file, and while it is reading...
2. Recognize any UsProgData's that appear (those represent data structures like Lists).
3. See if the UsProgData is used by a case (for now) (later we'll get into lambda's and let's).
4. If the answer to 3. is yes, then de-sugar that case (or lambda or let),
  since it is here that we can deduce that Nil is a List, Cons is a List, etc.
  Ex: For case's, it is in seeing a Nil case that we can deduce the thing being case'd is a List.
5. We may have to make small, effortless changes to progBuiltIns and ctxtAddUsProgs, which come before this mini-phase
(in order to get input and output types correct).

Recall in Struct.Exprs, individual user-level definitions of data structures go like this:
data UsProg = UsProgData TpName [TpVar] [Ctor]    -- lhs, type params, constructors
That last part, the [Ctor], is a list storing all the possible constructors!
We can use that to determine if we are missing any cases,
and know how to de-sugar into the correct constructors.
-}

-- Infers/checks a term, elaborating it from a user-term (UsTm) to a full Term
myInfer' :: UsTm -> CheckM Term
myInfer' (UsCase tm cs) =
  -- (CALCULATES the missing cases by running lookupCtorType to get the constructors this type is supposed to have)
  -- (EX: can deduce that a List is either a Nil or a Cons)
  -- *** Can we use lookupCtorType in our mini-phase? ***
  lookupCtorType cs >>= \ (y, tgs, ps, ctors) -> -- lookup the datatype we have cases for
  mapM (const freshTag) tgs >>= \ itgs -> -- pick fresh tags
  mapM (const freshTp) ps >>= \ ips -> -- and pick fresh type vars
  let -- here we substitute old tags/type vars for new
      psub = mempty{tags   = Map.fromList (pickyZip tgs itgs),
                    tpVars = Map.fromList (pickyZip ps  ips)}
      cs' = sortCases ctors (subst psub cs) -- sort cases
      ctors' = subst psub ctors -- sub old tags/type vars for new ones in constructors
      -- here v we're saying that missing cases = ctors - cases
      missingCases = listDifference [y | (Ctor y _) <- ctors] [x | (CaseUs x _ _) <- cs] in
  guardM (null missingCases) (MissingCases missingCases) >> -- guard against missing cases
  guardM (length ctors == length cs) (WrongNumCases (length ctors) (length cs)) >> -- guard against wrong # of cases
  infer tm >>= \ tm' ->
  -- add a constraint here v that (y itgs ips) = (typeof tm')
  constrain (Unify (TpData y itgs ips) (typeof tm')) >>
  freshTp >>= \ itp -> -- itp is the cases return type
  mapM (uncurry myInferCase) (pickyZip cs' ctors') >>= \ cs'' -> -- infer the cases
  -- add another constraint v that for each case `| x ps -> tm`, itp = (typeof tm)
  mapM_ (\ (Case x ps tm) -> constrain (Unify itp (typeof tm))) cs'' >>
  return (TmCase tm' (y, itgs, ips) cs'' itp)


-- Desugars an entire program
desugarProgs :: UsProgs -> CheckM UsProgs
desugarProgs = CheckM

-- Try to desugar an entire file, running the CheckM monad
desugarFile :: UsProgs -> Either String UsProgs
desugarFile ps =
  either (\ (e, loc) -> Left (if null (show loc) then show e else show e ++ ", " ++ show loc))
         (\ (a, s, w) -> Right a)
    (runExcept (runRWST (desugarProgs ps)
                        (CheckR emptyCtxt (Loc Nothing "")) mempty))