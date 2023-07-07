{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module AgdaIO.Monad (
  AgdaM,
  runAgdaM,
  sendLine,
  recvLine,
) where

import Control.Monad.IO.Class
import Control.Monad (replicateM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import System.IO
import System.Process


newtype AgdaM a =
  AgdaM (ReaderT (Handle, Handle)  -- stdin, stdout
             (StateT Bool  -- whether agda is currently on a JSON> prompt
                (ExceptT String IO))
           a)
  deriving newtype (Functor, Applicative, Monad, MonadIO)

instance MonadFail AgdaM where
  fail s = AgdaM (lift (lift (throwE s)))

runAgdaM :: AgdaM a -> IO (Either String a)
runAgdaM (AgdaM act) = do
  (minh, mouth, _, ph) <- createProcess (proc "agda" ["--interaction-json"])
                                          { std_in = CreatePipe
                                          , std_out = CreatePipe }
  (inh, outh) <- case (minh, mouth) of
    (Just inh, Just outh) -> return (inh, outh)
    _ -> error "Invalid output from createProcess"

  prefix <- replicateM 6 (hGetChar outh)
  if prefix == "JSON> "
    then do
      res <- runExceptT (evalStateT (runReaderT act (inh, outh)) False)

      terminateProcess ph
      return res
    else do
      return (Left "No JSON> prompt from Agda")

sendLine :: String -> AgdaM ()
sendLine s = do
  ain <- AgdaM (asks fst)
  liftIO $ hPutStrLn ain s
  -- liftIO $ hPutStrLn stderr $ "send>> " ++ s
  liftIO $ hFlush ain
  AgdaM (lift (put False))  -- no JSON> prompt any more

recvLine :: AgdaM (Maybe String)
recvLine = do
  isatprompt <- AgdaM (lift get)
  if isatprompt
    then return Nothing
    else do
      aout <- AgdaM (asks snd)
      let loop [] = return Nothing
          loop (c:cs) = do
            c' <- liftIO $ hGetChar aout
            if c' == c
              then fmap (c:) <$> loop cs
              else return (Just [c'])
      loop "JSON> " >>= \case
        Nothing -> do
          AgdaM (lift (put True))
          return Nothing
        Just prefix -> do
          AgdaM (lift (put False))
          line <- (prefix ++) <$> liftIO (hGetLine aout)
          -- liftIO $ hPutStrLn stderr $ "recv> " ++ line
          return (Just line)
