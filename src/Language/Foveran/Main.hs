{-# LANGUAGE OverloadedStrings, MultiParamTypeClasses #-}

module Main where

import           System.Exit
import           System.IO
import           System.Environment
import           Text.PrettyPrint
import qualified Language.Foveran.Parsing as P
import qualified Language.Foveran.Typing  as T
import qualified Language.Foveran.Util.Html as H

data Action
    = GenerateHtml FilePath (Maybe FilePath)
    | TypeCheck    FilePath

parseArgs :: IO Action
parseArgs = getArgs >>= parse
    where
      parse [ "html", fnm ]       = return $ GenerateHtml fnm Nothing
      parse [ "html", fnm, ofnm ] = return $ GenerateHtml fnm (Just ofnm)
      parse [ fnm ]               = return $ TypeCheck fnm
      parse _ = do
        hPutStrLn stderr "Usage: "
        hPutStrLn stderr "  foveran <filename>.fv"
        hPutStrLn stderr "  foveran html <filename>.fv [<filename>.html]"
        exitFailure

main :: IO ()
main = do
  action <- parseArgs
  case action of
    GenerateHtml fnm ofnm ->
       H.writeHtmlDocument fnm ofnm
    TypeCheck filename ->
        do readResult <- P.readFoveranFile filename
           case readResult of 
             Left err ->
                 do hPutStrLn stderr $ render (P.ppInputError err)
                    exitFailure
             Right decls ->
                 do T.checkDeclarations decls
                    exitSuccess
