{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
module Main where

import Control.Monad (forM_)
import Control.Monad.IO.Class
import Data.Functor.Compose
import Data.List (intersect)
import Data.Map.Strict (Map)
import Data.Maybe (mapMaybe, fromMaybe)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Environment (getArgs)
import System.Exit (die, exitSuccess, exitFailure)
import Text.Read (readMaybe)

import Abstract
import AgdaIO
import AST
import Parser
import Reexpress
import Tactic
import ToAgda
import ToSMT
import Unnormalise
import Util
import Data.Bifunctor (second, first)


handle :: MonadIO m => Either String a -> m a
handle = either (liftIO . die) return

handleShow :: (Show e, MonadIO m) => String -> Either e a -> m a
handleShow note = either (\x -> liftIO $ die (note ++ ": " ++ show x)) return

{-
mainStdin :: IO ()
mainStdin = do
  src <- getContents

  ctx <- case parseContext src of
           Left err -> die (show err)
           Right ctx -> return ctx

  let ctx1 = unnormaliseContext ctx
      (absvars, ctx2) = abstractContext ctx1
      Context goal givens _ = ctx2

  putStrLn "Goal:"
  putStrLn $ "  " ++ exprToAgda goal
  putStrLn ""
  putStrLn "Givens:"
  forM_ givens $ \(name, rhs) ->
    putStrLn $ name ++ " : " ++ exprToAgda rhs
  putStrLn ""
  putStrLn "Abstract variables:"
  forM_ (Map.assocs absvars) $ \(name, rhs) ->
    putStrLn $ name ++ " = " ++ exprToAgda rhs

  putStr $ contextToSMT ctx2
-}

extendedContext :: FilePath -> Int -> AgdaM (AAgdaContext, Map Name FExpr)
extendedContext fpath pointid = do
  liftIO $ putStrLn "Computing normalised context..."
  (goalstr, givenstrs) <- handle =<< cmdContext fpath pointid

  -- Parse the goal and givens, in their full (non-abstracted) form
  goal0 <- handleShow "Parsing goal" $ parseExpr goalstr
  givens0 <- handle $
    traverse (\(name, s) -> first (\err -> "Parsing type of '" ++ name ++ "':\n" ++ s ++ "\nError: " ++ show err) $
                              (name,) <$> parseExpr s)
             givenstrs

  let zvarnames = [var | (var, Var "ℤ") <- givens0]
  liftIO $ putStrLn "Computing normalised forms of ℤ variables..."
  zvarsstr <- handle =<< getCompose (traverse (\var -> (var,) <$> Compose (cmdNormalise fpath pointid var)) zvarnames)
  zvars0 <- handle $
    traverse (\(name, s) -> first (\err -> "Parsing normalise '" ++ name ++ "':" ++ show err) $
                              (name,) <$> parseExpr s)
             zvarsstr

  let ctx1 = unnormaliseContext (Context goal0 givens0 zvars0)
      (absvars, ctx2) = abstractContext ctx1
      -- ctx3 = reexpressContext (Map.keys absvars) ctx2 expressvars

  return (ctx2, absvars)

verboseContext :: AAgdaContext -> Map Name FExpr -> IO ()
verboseContext (Context goal givens zvars) absvars = do
  putStrLn "Goal:"
  putStrLn $ "  " ++ exprToAgda goal
  putStrLn ""
  putStrLn "Givens:"
  forM_ givens $ \(name, rhs) ->
    putStrLn $ name ++ " : " ++ exprToAgda rhs
  putStrLn ""
  putStrLn "Abstract variables:"
  forM_ (Map.assocs absvars) $ \(name, rhs) ->
    putStrLn $ name ++ " = " ++ exprToAgda rhs
  putStrLn ""
  putStrLn "Integer values in context:"
  forM_ zvars $ \(v, e) ->
    putStrLn $ v ++ " = " ++ exprToAgda e

mainCollect :: FilePath -> Maybe Int -> Maybe FilePath -> IO ()
mainCollect fpath mpointid mserctxoutfile = do
  agdaret <- (handle =<<) . runAgdaM $ do
    liftIO $ putStrLn "Loading file..."
    ipoints <- handle =<< cmdLoad fpath

    case mpointid of
      Nothing -> do
        liftIO $ mapM_ print ipoints
        return Nothing
      Just pointid -> do
        Just <$> extendedContext fpath pointid

  (ctx, absvars) <-
    case agdaret of
      Nothing -> exitSuccess
      Just res -> return res

  print ctx

  verboseContext ctx absvars
  putStr $ contextToSMT ctx

  case mserctxoutfile of
    Nothing -> return ()
    Just fname -> writeFile fname (show (ctx, absvars))

packLemma :: AAgdaContext -> Map Name FExpr -> AAgdaContext -> FExpr -> String -> Either String String
packLemma origCtx absvars (Context _ givens zvars) proof lemname = do
  let -- first collect the givens used in the proof
      freesProof = freeVars proof
      usedGivensProof = filter ((`Set.member` freesProof) . fst) givens
      -- then collect the givens mentioned in the types of those givens, so that
      -- the telescope we're going to write is well-scoped
      frees = freesProof <> foldMap (freeVars . snd) usedGivensProof
      -- collect all the abstracts that we used so that we can provide them as
      -- inputs to the lemma
      usedAbstracts' = mapMaybe (\n -> (n,) <$> Map.lookup n absvars) (Set.toList frees)
      orderedUsedNames =
        map (second Left) (filter ((`Set.member` frees) . fst) givens)
        ++ map (second Right) usedAbstracts'
  sortedNames <- case topSortOpposite fst (either freeVars freeVars . snd) orderedUsedNames of
                   Nothing -> Left "Givens telescope contains cycle?"
                   Just l -> return l
  let -- I hope this backsubstitutes all the necessary things...
      usedZvars = map fst sortedNames `intersect` map fst zvars
      goal' = case backsubstituteContext usedZvars origCtx of
                Left err -> error $ "unexpected: " ++ err
                Right (Context g _ _) -> g
  return $ unlines
    [lemname ++ " : "
        ++ concatMap (\(n, e) -> "(" ++ n ++ " : " ++ either exprToAgda (const "_") e ++ ") ") sortedNames
        ++ "-> " ++ exprToAgda goal'
    ,lemname
        ++ concatMap (\(n, _) -> ' ' : n) sortedNames
        ++ " ="
    ,"  "++ exprToAgda proof
    ,""
    ,lemname
        ++ concatMap (\(n, e) -> ' ' : either (const n) exprToAgdaInArg e) sortedNames]

mainProve :: FilePath -> String -> Maybe String -> IO ()
mainProve serfpath tacticstr mlemname = do
  (ctx, absvars) <- read @(AAgdaContext, Map Name FExpr) <$> readFile serfpath

  (ptacs, mfintac) <- handle $ parseTacticString tacticstr
  let Tactic ptac = mconcat ptacs
  (ctx2, prooffun) <- handle $ ptac ctx
  case mfintac of
    Nothing -> do
      verboseContext ctx2 absvars
    Just (Tactic' ftac) -> do
      prf' <- handle $ ftac ctx2
      let Proof prf = prooffun prf'
      putStrLn ("-- " ++ tacticstr)
      lemma <- handle $ packLemma ctx absvars ctx2 prf (fromMaybe "lemma" mlemname)
      putStrLn lemma
      -- putStrLn (exprToAgda prf)
      -- let Context _ givens _ = ctx2
      -- let usedVars = freeVars prf `Set.intersection` Set.fromList (map fst givens)
      -- putStrLn "Used givens:"
      -- forM_ (filter ((`Set.member` usedVars) . fst) givens) $ \(name, ty) ->
      --   putStrLn ("- " ++ name ++ " : " ++ exprToAgda ty)

main :: IO ()
main = do
  getArgs >>= \case
    ["-ipoints", fpath] -> mainCollect fpath Nothing Nothing
    ["-ctx", fpath, readMaybe -> Just pointid] -> mainCollect fpath (Just pointid) Nothing
    ["-ctx", fpath, readMaybe -> Just pointid, serctxoutfile] -> mainCollect fpath (Just pointid) (Just serctxoutfile)
    ["-prove", serfile, tacticstr] -> mainProve serfile tacticstr Nothing
    ["-prove", serfile, tacticstr, lemname] -> mainProve serfile tacticstr (Just lemname)
    _ -> do
      putStrLn "Usage:"
      putStrLn "  arith-solver -ipoints <file.agda>"
      putStrLn "    -- show interaction points"
      putStrLn "  arith-solver -ctx <file.agda> <interaction point ID> [serialised.context]"
      putStrLn "    -- show extended context at interaction point, and optionally save to file"
      putStrLn "  arith-solver -prove <serialised.context> <tactic string> [lemma name]"
      putStrLn "    -- prove goal using tactics (see Tactic.hs for how)"
      exitFailure
