{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
module AgdaIO (
  AgdaM,
  runAgdaM,
  Loc(..), Range(..), IPoint(..),
  cmdLoad, cmdContext, cmdNormalise,
) where

import qualified Text.JSON as J
import Text.JSON (JSValue(..))

import AgdaIO.Monad
import GHC.TypeLits (KnownSymbol, symbolVal)
import Data.Proxy
import Data.Ratio (denominator, numerator)


data Loc = Loc Int Int Int  -- line col offset
  deriving (Show)

data Range = Range Loc Loc  -- start end
  deriving (Show)

data IPoint = IPoint Int Range  -- id range
  deriving (Show)

cmdLoad' :: FilePath -> AgdaM [JSValue]
cmdLoad' fp = sendAndGets $ "IOTCM " ++ show fp ++ " None Direct (Cmd_load " ++ show fp ++ " [])"

cmdLoad :: FilePath -> AgdaM (Either String [IPoint])
cmdLoad fp = do
  vals <- cmdLoad' fp
  return $ case filter ((== Right "InteractionPoints") . getKind) vals of
    JObj' @'["interactionPoints"] [JSArray arr] : _ -> traverse parseIPoint arr
    _ -> Left $ "cmdLoad : " ++ show vals

cmdContext' :: FilePath -> Int -> AgdaM [JSValue]
cmdContext' fp pointid =
  sendAndGets $ "IOTCM " ++ show fp ++ " None Direct (Cmd_goal_type_context Normalised " ++ show pointid ++ " noRange \"\")"

cmdContext :: FilePath -> Int -> AgdaM (Either String (String, [(String, String)]))
cmdContext fp pointid = do
  vals <- cmdContext' fp pointid
  return $ case filter ((== Right "DisplayInfo") . getKind) vals of
    JObj' @'["info"]
        [JObj' @["kind", "goalInfo"]
          [JStr "GoalSpecific"
          ,JObj' @'["kind", "typeAux", "type", "entries"]
            [JStr "GoalType", JObj' @'["kind"] [JStr "GoalOnly"], JStr goal, JSArray givens]]]
      : _ ->
        (goal,) . concat <$> traverse parseGiven givens
    _ -> Left "cmdContext"

cmdNormalise' :: FilePath -> Int -> String -> AgdaM [JSValue]
cmdNormalise' fp pointid expr =
  sendAndGets $ "IOTCM " ++ show fp ++ " None Direct (Cmd_compute DefaultCompute " ++ show pointid ++ " noRange " ++ show expr ++ ")"

cmdNormalise :: FilePath -> Int -> String -> AgdaM (Either String String)
cmdNormalise fp pointid expr = do
  vals <- cmdNormalise' fp pointid expr
  return $ case filter ((== Right "DisplayInfo") . getKind) vals of
    JObj' @'["info"]
        [JObj' @["kind", "goalInfo"]
          [JStr "GoalSpecific"
          ,JObj' @'["kind", "expr"]
            [JStr "NormalForm", JStr result]]]
      : _ ->
        Right result
    _ -> Left "cmdContext"

sendAndGets :: String -> AgdaM [JSValue]
sendAndGets line = do
  sendLine line
  let loop prefix = do
        recvLine >>= \case
          Nothing -> return (prefix [])
          Just s -> case J.decode s of
                      J.Ok v -> loop (prefix . (v :))
                      J.Error err -> fail $ "Failed to decode JSON from agda: " ++ err
  loop id

getKind :: JSValue -> Either String String
getKind (JObj' @'["kind"] [JStr s]) = Right s
getKind _ = Left "getKind"

parseIPoint :: JSValue -> Either String IPoint
parseIPoint (JObj' @["id", "range"] [JInt n, parseRange -> range]) =
  IPoint n <$> range
parseIPoint _ = Left "parseIPoint"

parseRange :: JSValue -> Either String Range
parseRange (JSArray [JObj' @["start" ,"end"] [parseLoc -> start, parseLoc -> end]]) =
  Range <$> start <*> end
parseRange _ = Left "parseRange"

parseLoc :: JSValue -> Either String Loc
parseLoc (JObj' @["line", "col", "pos"] [JInt a, JInt b, JInt c]) = Right (Loc a b c)
parseLoc _ = Left "parseLoc"

parseGiven :: JSValue -> Either String [(String, String)]
parseGiven (JObj' @["reifiedName", "binding", "inScope"] [JStr name, JStr expr, JSBool inScope]) = Right $ if inScope then [(name, expr)] else []
parseGiven _ = Left "parseGiven"

pattern JStr :: String -> JSValue
pattern JStr s <- JSString (J.fromJSString -> s)
  where JStr = JSString . J.toJSString

pattern JObj :: [(String, JSValue)] -> JSValue
pattern JObj l <- JSObject (J.fromJSObject -> l)
  where JObj = JSObject . J.toJSObject

pattern JInt :: Int -> JSValue
pattern JInt x <- JSRational _ (safeToInt -> Just x)
  where JInt = JSRational False . fromIntegral

safeToInt :: Rational -> Maybe Int
safeToInt r
  | denominator r == 1
  , let n = fromIntegral (numerator r)
  , toInteger n == numerator r
  = Just n
safeToInt _ = Nothing

data Symbols l where
  SCons :: KnownSymbol s => Symbols l -> Symbols (s ': l)
  SNil :: Symbols '[]

class KnownSymbols l where knownSymbols :: Symbols l
instance KnownSymbols '[] where knownSymbols = SNil
instance (KnownSymbol s, KnownSymbols l) => KnownSymbols (s ': l) where knownSymbols = SCons knownSymbols

pattern JObj' :: forall l. KnownSymbols l => [JSValue] -> JSValue
pattern JObj' spec <- (matchKeys (knownSymbols @l) -> Just spec)

matchKeys :: Symbols l -> JSValue -> Maybe [JSValue]
matchKeys SNil _ = Just []
matchKeys (SCons @s ss) val@(JObj pairs) =
  case lookup (symbolVal (Proxy @s)) pairs of
    Just x -> (x :) <$> matchKeys ss val
    Nothing -> Nothing
matchKeys _ _ = Nothing
