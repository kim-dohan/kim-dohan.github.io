{-
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015, 2017)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2014)
Author:  Akihisa Yamada <akihisa.yamada@uibk.ac.at> (2017)
License: LGPL (see file COPYING.LESSER)
-}
module Main (main) where

import Ceta -- the certifier
import Text.Read -- for readMaybe
import System.Environment -- for getArgs
import System.IO -- for file reading
import System.Exit -- for error codes

mapMaybe f Nothing = Nothing
mapMaybe f (Just x) = Just (f x)

explodeMaybe Nothing = Nothing
explodeMaybe (Just x) = Just (explode x)

noWhite = filter (\x -> not (x `elem` " \t\n\r"))

replace f s = case f (noWhite s) of 
  Nothing -> s
  Just s' -> s'

complexityStart = "WORST_CASE(?,O(n^"  
complexityEnd = "))"

xml tag e = "<" ++ tag ++ ">" ++ e ++ "</" ++ tag ++ ">"
xmlLeaf tag = "<" ++ tag ++ "/>"
  
shortAnswer "YES" = Just (xml "answer" (xmlLeaf "yes"))
shortAnswer "NO" = Just (xml "answer" (xmlLeaf "no"))
shortAnswer s = let 
   (start,s1) = splitAt (length complexityStart) s
   in if start == complexityStart then
     let (end, num) = splitAt (length complexityEnd) (reverse s1)
       in if end == complexityEnd then
         mapMaybe (\ deg -> 
            (xml "answer" (xml "upperBound" (xml "polynomial" (show deg)))))
         (readMaybe num :: Maybe Integer)
         else Nothing
        else Nothing

shortProperty "SN" = Just (xml "property" (xmlLeaf "termination"))
shortProperty "CR" = Just (xml "property" (xmlLeaf "confluence"))
shortProperty "COM" = Just (xml "property" (xmlLeaf "commutation"))
shortProperty "DC" = Just (xml "property" (xml "complexity" (xmlLeaf "derivationalComplexity")))
shortProperty "RC" = Just (xml "property" (xml "complexity" (xmlLeaf "runtimeComplexity")))
shortProperty "INF" = Just (xml "property" (xmlLeaf "infeasibility"))
shortProperty _ = Nothing

main = getArgs >>= parse False Nothing Nothing Nothing

parse _ _ _ _ ("--version":_) = putStrLn version
parse _ inp prop answ ("--allow-assumptions":args) = parse True inp prop answ args
parse a _ prop answ ("--inputf":fname:args) = do
  inp <- readFile fname
  parse a (Just inp) prop answ args
parse a inp _ answ ("--propertyf":fname:args) = do
  prop <- readFile fname
  parse a inp (Just prop) answ args
parse a inp _ answ ("--property":prop:args) = 
  parse a inp (Just prop) answ args
parse a inp prop _ ("--answerf":fname:args) = do
  answ <- readFile fname
  parse a inp prop (Just answ) args
parse a inp prop _ ("--answer":answ:args) = 
  parse a inp prop (Just answ) args
parse a inp prop answ [fname] = do
  cpf <- readFile fname
  start a 
    (mapMaybe explode inp) 
    (mapMaybe (explode . replace shortProperty) prop) 
    (mapMaybe (explode . replace shortAnswer) answ) 
    (explode cpf)
parse _ _ _ _ _ = do
  hPutStrLn stderr usage
  exitWith (ExitFailure 4)

start a inputO propertyO answerO proofString = 
    do case certify_proof a inputO propertyO answerO proofString of
         Certified -> 
             do putStrLn ("CERTIFIED")
                exitWith ExitSuccess
         Error message -> 
             do putStrLn "REJECTED"
                hPutStrLn stderr message
                exitWith (ExitFailure 1)
         Unsupported message -> 
             do putStrLn "UNSUPPORTED" 
                hPutStrLn stderr message
                exitWith (ExitFailure 2)

usage = "usage: ceta [(parameters) certificate | --version]\n\
        \  \n\
        \  A \"certificate\" is an XML file in the certification problem format (CPF 3.x).\n\
        \  \n\
        \  (manually setting a parameter overwrites information in CPF):\n\
        \  --allow-assumptions    Allow (axiomatic) assumptions in the certificate.\n\
        \  --inputf fname         Read input from separate file.\n\
        \  --propertyf fname      Read property from separate file.\n\
        \  --property p           Read property from string p.\n\
        \  --answerf fname        Read answer from separate file.\n\
        \  --answer a             Read answer from string a.\n\
        \  --version              Print the version number (+ mercurial id)."
