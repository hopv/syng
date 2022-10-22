--------------------------------------------------------------------------------
-- Just import all the relevant parts of Syho
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syho.All where

-- Paradoxes for the logic

import Syho.Logic.Paradox

-- Examples for the logic

import Syho.Logic.Example

-- Semantic soundness and adequacy of the Hoare triples

import Syho.Model.Hor.Sound
