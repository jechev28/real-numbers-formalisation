-- Tested with GHC 8.0.2 and QuickCheck 2.9.2.

import Test.QuickCheck

xor :: Bool -> Bool -> Bool
xor p q = (p || q) && not (p && q)

prop_Assoc :: Bool -> Bool -> Bool -> Bool
prop_Assoc p q r = (p `xor` q) `xor`r == p `xor` (q `xor`r)

main :: IO ()
main = quickCheck prop_Assoc
