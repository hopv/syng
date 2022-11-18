--------------------------------------------------------------------------------
-- Just import all the relevant parts of Syng
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Syng.All where

-- Paradoxes for the logic

import Syng.Logic.Paradox

-- Examples for the logic

import Syng.Logic.Example

-- Semantic soundness and adequacy of the Hoare triples

import Syng.Model.Hor.Sound
