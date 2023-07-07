{-# LANGUAGE LambdaCase #-}
module Parser where

import Control.Monad (when, void, guard)
import Data.Char (isSpace)
import Data.Functor.Identity (Identity)
import Data.Maybe (catMaybes)
import Text.Parsec
import Text.Parsec.Expr

-- import Debug.Trace

import AST
import Util


type Parser = Parsec String () 

parseContext :: String -> Either ParseError FAgdaContext
parseContext input = parse (pContext <* spaces <* eof) "" input

parseExpr :: String -> Either ParseError FExpr
parseExpr input = parse (pExpr <* spaces <* eof) "" (substitute '\n' ' ' input)

pContext :: Parser FAgdaContext
pContext = do
  pHeader "Goal"

  goalentry <- pEntry
  goalexpr <- case goalentry of
    Nothing -> fail "Goal out of scope?"
    Just (goalname, goalexpr)
      | goalname == "Goal" -> return goalexpr
      | otherwise -> fail $ "Goal statement not called 'Goal' (instead found '" ++ goalname ++ "')"

  pHeader "Context"

  es <- catMaybes <$> many pEntry
  return (Context goalexpr es [])

pHeader :: String -> Parser ()
pHeader str = do
  assertLeft "pHeader"
  many_ emptyLine
  unit "-- ## "
  unit str
  _ <- newline
  return ()

pEntry :: Parser (Maybe (String, FExpr))
pEntry = do
  assertLeft "pEntry"
  name <- try $ do
    many_ emptyLine
    pVarName

  outscope <- (True <$ unit " (out of scope)") <|> return False
  _ <- newline
  spaces
  _ <- char ':'
  _ <- space
  ex <- pExpr
  eof <|> void newline

  return $ if outscope then Nothing else Just (name, ex)

pExpr :: Parser FExpr
pExpr = buildExpressionParser operatorTable' pExprAtom

pExprAtom :: Parser FExpr
pExprAtom = choice
  [do try (inlineSpaces >> unit "∣")
      e <- pExpr
      inlineSpaces
      unit "∣"
      return (UOp Abs e)
  ,do try (inlineSpaces >> unit "-[1+")
      e <- pExpr
      inlineSpaces
      unit "]"
      return (UOp Neg (BOp (UOp Pos (Lit 1)) Add (UOp Pos e)))
  ,do try (inlineSpaces >> unit "+[1+")
      e <- pExpr
      inlineSpaces
      unit "]"
      return (BOp (UOp Pos (Lit 1)) Add (UOp Pos e))
  ,do try (inlineSpaces >> unit "+0")
      return (UOp Pos (Lit 0))
  ,do try (inlineSpaces >> (unit "λ" <|> unit "\\"))
      inlineSpaces
      choice
        [do _ <- char '{'
            let consume :: Int -> Parser String
                consume 0 = return ""
                consume depth = choice
                  [(:) <$> char '{' <*> consume (depth + 1)
                  ,(:) <$> char '}' <*> consume (depth - 1)
                  ,(:) <$> anyChar  <*> consume depth]
            s <- consume 1
            return (OpaqueArg ("λ {" ++ s))
        ,do n <- (Nothing <$ unit "_") <|> Just <$> pVarName
            inlineSpaces
            unit "→" <|> unit "->"
            e <- pExpr
            return (Lam n e)]
  ,do e1 <- pCallAtom
      es <- many pCallAtom
      case es of [] -> return e1
                 _ -> return (Call e1 es)]

pCallAtom :: Parser FExpr
pCallAtom = choice
  [do x <- try (inlineSpaces >> many1 digit <* notFollowedBy pNameChar)
      return (Lit (read x))
  ,do n <- try (inlineSpaces >> pVarName)
      return (Var n)
  ,do _ <- try (inlineSpaces >> char '(')
      e <- pExpr
      inlineSpaces
      _ <- char ')'
      return e]

pVarName :: Parser Name
pVarName = try $ do
  name <- pAnyName
  guard (name `notElem` (keywords ++ operators))
  return name

pAnyName :: Parser Name
pAnyName = try $ do
  inlineSpaces
  name <- many1 pNameChar
  return name

pNameChar :: Parser Char
pNameChar = satisfy (\c -> not (isSpace c) && c `notElem` "(){}")

keywords :: [Name]
keywords =
  ["λ", "\\", "_", ":"
  -- hack to not misparse some mixfix notation:
  ,"∣", "-[1+", "]"]

operators :: [Name]
operators = concatMap (concatMap (\case OpPrefix ns _ -> ns
                                        OpInfix ns _ _ -> ns))
                      operatorTable

operatorTable' :: [[Operator String () Identity FExpr]]
operatorTable' =
  map (map (\case OpPrefix ns uop -> Prefix (unop uop ns)
                  OpInfix ns bop as -> Infix (binop bop ns) as))
      operatorTable
  where
    unop uop alts = try $ do
      inlineSpaces
      name <- pAnyName
      guard (name `elem` alts)
      return (UOp uop)
    binop bop alts = try $ do
      inlineSpaces
      name <- pAnyName
      guard (name `elem` alts)
      return (\e1 e2 -> BOp e1 bop e2)

unit :: String -> Parser ()
unit s = try (string s) >> return ()

emptyLine :: Parser ()
emptyLine = try $ do
  assertLeft "emptyLine"
  s <- many (satisfy (\c -> isSpace c && c `notElem` "\r\n"))
  (guard (not (null s)) >> eof) <|> void newline

many_ :: Parser a -> Parser ()
many_ p = many p >> return ()

inlineSpaces :: Parser ()
inlineSpaces = choice
  [try $ do
      spaces
      col <- sourceColumn <$> getPosition
      guard (col > 1)
  ,return ()]

assertNotLeft :: String -> Parser ()
assertNotLeft fun = do
  col <- sourceColumn <$> getPosition
  when (col <= 1) $
    fail $ fun ++ " called outside of indented block"

assertLeft :: String -> Parser ()
assertLeft fun = do
  col <- sourceColumn <$> getPosition
  when (col /= 1) $
    fail $ fun ++ " not called at start of line"
