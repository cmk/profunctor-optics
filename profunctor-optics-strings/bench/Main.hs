{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Criterion.Main

import Control.Applicative (liftA2)
import Data.Bits (complement, xor)

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Optic as BO
import Data.Profunctor.Optic
import qualified Data.Text as T
import qualified Data.Text.Optic as TO
import Data.Word (Word8, Word16, Word32, Word64)
import Data.Word.Optic

main :: IO ()
main = defaultMain
    [ bgroup "cotraversal"
        [ bgroup "bits8"
            [ bench "over bits8 not"    $ whnf (over bits8 not) w8
            , bench "complement"        $ whnf complement w8
            ]
        , bgroup "bits16"
            [ bench "over bits16 not"   $ whnf (over bits16 not) w16
            , bench "complement"        $ whnf complement w16
            ]
        , bgroup "bits32"
            [ bench "over bits32 not"   $ whnf (over bits32 not) w32
            , bench "complement"        $ whnf complement w32
            ]
        , bgroup "bits64"
            [ bench "over bits64 not"   $ whnf (over bits64 not) w64
            , bench "complement"        $ whnf complement w64
            ]
        ]
    , bgroup "indexed-cotraversal"
        [ bgroup "ibits8"
            [ bench "reoverWithKey ibits8 (const not)"
                $ whnf (reoverWithKey ibits8 (const not)) w8
            , bench "complement"
                $ whnf complement w8
            ]
        , bgroup "ibits16"
            [ bench "reoverWithKey ibits16 (const not)"
                $ whnf (reoverWithKey ibits16 (const not)) w16
            , bench "complement"
                $ whnf complement w16
            ]
        , bgroup "ibits32"
            [ bench "reoverWithKey ibits32 (const not)"
                $ whnf (reoverWithKey ibits32 (const not)) w32
            , bench "complement"
                $ whnf complement w32
            ]
        , bgroup "ibits64"
            [ bench "reoverWithKey ibits64 (const not)"
                $ whnf (reoverWithKey ibits64 (const not)) w64
            , bench "complement"
                $ whnf complement w64
            ]
        ]
    , bgroup "grate"
        [ bgroup "grate8"
            [ bench "zipsWith grate8 boolXor"
                $ whnf (zipsWith grate8 (liftA2 (/=)) w8) w8
            , bench "xor"
                $ whnf (xor w8) w8
            ]
        , bgroup "grate16"
            [ bench "zipsWith grate16 boolXor"
                $ whnf (zipsWith grate16 (liftA2 (/=)) w16) w16
            , bench "xor"
                $ whnf (xor w16) w16
            ]
        , bgroup "grate32"
            [ bench "zipsWith grate32 boolXor"
                $ whnf (zipsWith grate32 (liftA2 (/=)) w32) w32
            , bench "xor"
                $ whnf (xor w32) w32
            ]
        , bgroup "grate64"
            [ bench "zipsWith grate64 boolXor"
                $ whnf (zipsWith grate64 (liftA2 (/=)) w64) w64
            , bench "xor"
                $ whnf (xor w64) w64
            ]
        ]
    , bgroup "traversal"
        [ bgroup "bytes"
            [ bench "over bytes (+1)"   $ whnf (over BO.bytes (+ 1)) bs
            , bench "BS.map (+1)"       $ whnf (BS.map (+ 1)) bs
            ]
        , bgroup "chars"
            [ bench "over chars succ"   $ whnf (over TO.chars succ) txt
            , bench "T.map succ"        $ whnf (T.map succ) txt
            ]
        ]
    , bgroup "splitting"
        [ bgroup "bs-lined"
            [ bench "view lined"        $ nf (view BO.lined) bsLines
            , bench "B8.lines"          $ nf B8.lines bsLines
            ]
        , bgroup "bs-worded"
            [ bench "view worded"       $ nf (view BO.worded) bsWords
            , bench "B8.words"          $ nf B8.words bsWords
            ]
        , bgroup "text-lined"
            [ bench "view lined"        $ nf (view TO.lined) txtLines
            , bench "T.lines"           $ nf T.lines txtLines
            ]
        , bgroup "text-worded"
            [ bench "view worded"       $ nf (view TO.worded) txtWords
            , bench "T.words"           $ nf T.words txtWords
            ]
        ]
    ]
  where
    w8  = 0xAA :: Word8
    w16 = 0xAAAA :: Word16
    w32 = 0xAAAAAAAA :: Word32
    w64 = 0xAAAAAAAAAAAAAAAA :: Word64
    bs  = BS.replicate 1000 0x42
    txt = T.replicate 1000 "x"
    bsLines = B8.intercalate "\n" $ replicate 100 "hello world"
    bsWords = B8.intercalate " " $ replicate 100 "hello"
    txtLines = T.intercalate "\n" $ replicate 100 "hello world"
    txtWords = T.intercalate " " $ replicate 100 "hello"
