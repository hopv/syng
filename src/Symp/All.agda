--------------------------------------------------------------------------------
-- Just import all the relevant parts of Symp
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Symp.All where

-- Paradoxes for the logic

import Symp.Logic.Paradox

-- Examples for the logic

import Symp.Logic.Example

-- Semantic soundness and adequacy of the Hoare triples

import Symp.Model.Hor.Sound
