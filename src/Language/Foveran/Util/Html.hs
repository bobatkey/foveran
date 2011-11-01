{-# LANGUAGE OverloadedStrings #-}

module Language.Foveran.Util.Html
    where

import           System.Exit
import           System.IO

import           Data.MonadicStream ((|>|))

import           Text.Blaze.Html5 ((!))
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import qualified Data.ByteString.Lazy as BL
import           Text.Blaze.Renderer.Utf8

import           Language.Forvie.SyntaxHighlight.Html (generateHtml)

import           Language.Foveran.Parsing.Token ()
import           Language.Foveran.Parsing (lexFile)

writeHtmlDocument :: FilePath -> Maybe FilePath -> IO ()
writeHtmlDocument fnm ofnm = do
  tokens <- lexFile fnm
  result <- return (tokens |>| generateHtml)
  case result of
    Left err   ->
        do hPutStrLn stderr $ "An error occured"
           exitFailure
    Right html ->
        do let output = case ofnm of Nothing -> fnm ++ ".html"; Just nm -> nm
           BL.writeFile output $ renderHtml $ do
                          H.docTypeHtml ! A.lang "en-GB" $ do
                                             H.head $ do
                                               H.meta ! A.httpEquiv "Content-Type" ! A.content "text/html; charset=utf-8"
                                               H.title $ H.toHtml fnm
                                               H.link ! A.rel "stylesheet" ! A.href "style.css" ! A.type_ "text/css"
                                             H.body $ do
                                                H.h1 $ H.toHtml fnm
                                                html
           exitSuccess