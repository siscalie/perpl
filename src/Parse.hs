module Parse where
import Exprs
import Lex

lexErr (line, col) = Left $ "Lex error at line " ++ show line ++ ", column " ++ show col

parseErr' p s = Left (p, s)

eofPos = (-1, 0)
eofErr = parseErr' eofPos "unexpected EOF"

parseErr s = ParseM $ \ ts ->
  let p = case ts of [] -> eofPos; ((p, _) : ts) -> p in
    Left (p, s)

formatParseErr (line, col) emsg = Left $
  "Parse error at line " ++ show line ++
    ", column " ++ show col ++ ": " ++ emsg

-- Parsing monad
newtype ParseM a = ParseM ([(Pos, Token)] -> Either (Pos, String) (a, [(Pos, Token)]))

-- Extract the function from ParseM
parseMf (ParseM f) = f

-- Call a ParseM's function with some tokens
parseMt ts (ParseM f) = f ts

-- Given something and a list of tokens, return them in the ParseM monad
parseMr = curry Right

-- Try to parse the second arg, falling back to the first if fails
parseElse a' (ParseM a) =
  ParseM $ \ ts -> either (\ _ -> Right (a', ts)) Right (a ts)

instance Functor ParseM where
  fmap f (ParseM g) = ParseM $ \ ts -> g ts >>= \ p -> Right (f (fst p), snd p)

instance Applicative ParseM where
  pure = ParseM . parseMr
  ParseM f <*> ParseM g =
    ParseM $ \ ts -> f ts >>= \ p ->
    g (snd p) >>= \ p' ->
    Right (fst p (fst p'), snd p')

instance Monad ParseM where
  (ParseM f) >>= g = ParseM $ \ ts -> f ts >>= \ (a, ts') -> parseMf (g a) ts'

parsePeeks :: Int -> ParseM [Token]
parsePeeks n = ParseM $ \ ts -> if length ts < n then eofErr else parseMr [t | (_, t) <- take n ts] ts

parsePeek :: ParseM Token
parsePeek = head <$> parsePeeks 1

-- Add semicolon to end of toks, if not already there
parseAddEOF :: ParseM ()
parseAddEOF =
  ParseM $ \ ts ->
  let ((lastrow, lastcol), lasttok) = last ts
  
      ts' = if lasttok == TkSemicolon then [] else [((lastrow, lastcol + 1), TkSemicolon)]
  in
    Right ((), ts ++ ts')

-- Drop the next token
parseEat :: ParseM ()
parseEat = ParseM $ \ ts -> case ts of
  [] -> eofErr
  (_ : ts') -> Right ((), ts')

-- Consume token t.
parseDrop t = parsePeek >>= \ t' ->
  if t == t' then parseEat else parseErr ("expecting " ++ show t)

-- Consume token t if there is one.
-- (can't use parsePeek because there could be an optional EOF token ';')
parseDropSoft t = ParseM $ \ ts -> case ts of
  ((_, t') : ts') -> parseMr () (if t == t' then ts' else ts)
  [] -> parseMr () ts

-- Parse a symbol.
parseVar :: ParseM Var
parseVar = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure v
  _ -> parseErr (if t `elem` keywords then show t ++ " is a reserved keyword"
                  else "expected a variable name here")

-- Parse zero or more symbols.
parseVars :: ParseM [Var]
parseVars = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure ((:) v) <*> parseVars
  _ -> pure []

parseVarsCommas :: ParseM [Var]
parseVarsCommas = parsePeeks 2 >>= \ ts -> case ts of
  [TkVar v, TkComma] -> parseEat *> parseEat *> pure ((:) v) <*> parseVarsCommas
  [TkVar v, TkParenR] -> parseEat *> parseEat *> pure [v]
  _ -> parseErr "Expecting a right parenthesis"

-- Parse a branch of a case expression.
parseCase :: ParseM CaseUs
parseCase = (*>) (parseDropSoft TkBar) $ parsePeek >>= \ t -> case t of
  TkVar c -> parseEat *> pure (CaseUs c) <*> parseVars <* parseDrop TkArr <*> parseTerm2
  _ -> parseErr "expecting another case"

-- Parse zero or more branches of a case expression.
parseCases :: ParseM [CaseUs]
parseCases = (*>) (parseDropSoft TkBar) $ parsePeek >>= \ t -> case t of
  TkVar _ -> pure (:) <*> parseCase <*> parseCases
  _ -> pure []

-- CaseOf, Lam, Let
parseTerm1 :: ParseM UsTm
parseTerm1 = parsePeeks 2 >>= \ t1t2 -> case t1t2 of
-- case term of term
  [TkCase, _] -> parseEat *> pure UsCase <*> parseTerm1 <* parseDrop TkOf <*> parseCases
-- if term then term else term
  [TkIf, _] -> parseEat *> pure UsIf <*> parseTerm1 <* parseDrop TkThen <*> parseTerm1 <* parseDrop TkElse <*> parseTerm1
-- \ x : type. term
  [TkLam, _] -> parseEat *> pure (flip (foldr (uncurry UsLam))) <*> parseLamArgs <* parseDrop TkDot <*> parseTerm1
-- let (x, y, ...) = term in term
  [TkLet, TkParenL] -> parseEat *> parseEat *> pure (flip UsProdOut) <*> parseVarsCommas <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
-- let x = term in term
  [TkLet, _] -> parseEat *> pure UsLet <*> parseVar <* parseDrop TkEq
             <*> parseTerm1 <* parseDrop TkIn <*> parseTerm1
  _ -> parseTerm2

parseLamArgs :: ParseM [(Var, Type)]
parseLamArgs =
  pure (curry (:)) <*> parseVar <* parseDrop TkColon <*> parseType1
    <*> parseElse [] (parseDrop TkComma >> parseLamArgs)

-- Sample
parseTerm2 :: ParseM UsTm
parseTerm2 = parsePeek >>= \ t -> case t of
    -- parseEat *> pure UsLam <*> parseVar <* parseDrop TkColon <*> parseType1 <* parseDrop TkDot <*> parseTerm1
-- sample dist : type
  TkSample -> parseEat *> pure UsSamp <*> parseDist <* parseDrop TkColon <*> parseType1
  TkAmb -> parseEat *> parseAmbs []
  _ -> parseTerm3

parseTmsDelim :: Token -> [UsTm] -> ParseM [UsTm]
parseTmsDelim tok tms = parsePeek >>= \ t ->
  if t == tok
    then parseEat >> parseTerm1 >>= \ tm -> parseTmsDelim tok (tm : tms)
    else return (reverse tms)

parseNum :: ParseM Int
parseNum = parsePeek >>= \ t -> case t of
  TkNum o -> parseEat >> return (o - 1)
  _ -> parseErr "Expected a number here"

-- App
parseTerm3 :: ParseM UsTm
parseTerm3 = parseTerm4 >>= \ tm -> parsePeek >>= \ t -> case t of
  -- TkComma -> pure UsProdIn <*> parseTmsDelim TkComma [tm]
  TkDot -> parseEat >> parseNum >>= return . UsAmpOut tm
  _ -> return tm

-- TODO: let (x, y) = tm1 in tm2

parseTerm4 :: ParseM UsTm
parseTerm4 =
  parseTerm5 >>= \ tm ->
  parsePeek >>= \ t -> case t of
    TkDoubleEq -> UsEqs <$> parseTmsDelim TkDoubleEq [tm]
    _ -> parseTermApp tm


parseAmbs tms =
  parseElse (UsAmb (reverse tms)) (parseTerm5 >>= \ tm -> parseAmbs (tm : tms))

-- Parse an application spine
parseTermApp tm =
  parseElse tm $ parseTerm5 >>= parseTermApp . UsApp tm

-- Var, Parens
parseTerm5 :: ParseM UsTm
parseTerm5 = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure (UsVar v)
  TkParenL -> parseEat *> (parseTerm1 >>= \ tm -> parseTmsDelim TkComma [tm] >>= \ tms -> pure (if length tms == 1 then tm else UsProdIn tms)) <* parseDrop TkParenR -- TODO: product
  TkLangle -> parseEat *> pure UsAmpIn <*> (parseTerm1 >>= \ tm -> parseTmsDelim TkComma [tm]) <* parseDrop TkRangle
  _ -> parseErr "couldn't parse a term here; perhaps add parentheses?"

parseTpsDelim tok tps = parsePeek >>= \ t ->
  if t == tok
    then (parseEat >> parseType3 >>= \ tp' -> parseTpsDelim tok (tp' : tps))
    else pure (reverse tps)

-- Arrow
parseType1 :: ParseM Type
parseType1 = parseType2 >>= \ tp -> parsePeek >>= \ t -> case t of
  TkArr -> parseEat *> pure (TpArr tp) <*> parseType1
  _ -> pure tp

-- Product, Ampersand
parseType2 :: ParseM Type
parseType2 = parseType3 >>= \ tp -> parsePeek >>= \ t -> case t of
  TkStar -> pure TpProd <*> parseTpsDelim TkStar [tp]
  TkAmp  -> pure TpAmp <*> parseTpsDelim TkAmp [tp]
  _ -> pure tp

-- TypeVar
parseType3 :: ParseM Type
parseType3 = parsePeek >>= \ t -> case t of
  TkVar v -> parseEat *> pure (TpVar v)
  TkBool -> parseEat *> pure (TpVar "Bool")
  TkParenL -> parseEat *> parseType1 <* parseDrop TkParenR
  _ -> parseErr "couldn't parse a type here; perhaps add parentheses?"

-- List of Constructors
parseCtors :: ParseM [Ctor]
parseCtors = ParseM $ \ ts -> case ts of
  ((p, TkVar _) : _) -> parseMt ((p, TkBar) : ts) parseCtorsH
  _ -> parseMt ts parseCtorsH
parseCtorsH = parsePeek >>= \ t -> case t of
  TkBar -> parseEat *> pure (:) <*> (pure Ctor <*> parseVar <*> parseTypes) <*> parseCtorsH
  _ -> pure []

-- Dist
parseDist :: ParseM Dist
parseDist = parsePeek >>= \ t -> case t of
  TkAmb  -> parseEat *> pure DistAmb
  TkFail -> parseEat *> pure DistFail
  TkUni  -> parseEat *> pure DistUni
  _ -> parseErr ("expected one of " ++ show TkAmb ++ ", " ++ show TkFail ++ ", or " ++ show TkUni ++ " here")

-- List of Types
parseTypes :: ParseM [Type]
parseTypes = parseElse [] (parseType3 >>= \ tp -> fmap ((:) tp) parseTypes)

-- Program
parseProg :: ParseM UsProgs
parseProg = parsePeek >>= \ t -> case t of
-- define x : type = term; ...
  TkFun -> parseEat *> pure UsProgFun <*> parseVar <* parseDrop TkColon <*> parseType1
             <* parseDrop TkEq <*> parseTerm1 <* parseDrop TkSemicolon <*> parseProg
-- extern x : type; ...
  TkExtern -> parseEat *> pure UsProgExtern <*> parseVar <* parseDrop TkColon
                <*> parseType1 <* parseDrop TkSemicolon <*> parseProg
-- data Y = ctors; ...
  TkData -> parseEat *> pure UsProgData <*> parseVar <* parseDrop TkEq
              <*> parseCtors <* parseDrop TkSemicolon <*> parseProg
-- term
  _ -> pure UsProgExec <*> parseTerm1 <* parseDropSoft TkSemicolon

parseFormatErr :: [(Pos, Token)] -> Either (Pos, String) a -> Either String a
parseFormatErr ts (Left (p, emsg))
  | p == eofPos = formatParseErr (fst (last ts)) emsg
  | otherwise = formatParseErr p emsg
parseFormatErr ts (Right a) = Right a

-- Extract the value from a ParseM, if it consumed all tokens
parseOut :: ParseM a -> [(Pos, Token)] -> Either String a
parseOut m ts =
  parseFormatErr ts $
  parseMf m ts >>= \ (a, ts') ->
  if length ts' == 0
    then Right a
    else parseErr' (fst $ head $ drop (length ts - length ts' - 1) ts)
           "couldn't parse after this"

-- Parse a whole program.
parseFile :: [(Pos, Token)] -> Either String UsProgs
parseFile = parseOut (parseAddEOF >> parseProg)
