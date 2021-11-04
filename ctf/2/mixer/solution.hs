import Data.List
import Data.Char
import qualified Data.Map as Map
import Data.Map ((!))

aAbc = "abcdefghijklmnopqrstuvwxyz_{}0123456789"
-- lenAbc  = "abcdefghijklmnopqrstuvwxyz_{}0123456789"
lenAbc = length aAbc
aWmf = "wmf9slha2r}v7te_13kby8ug4c{oz5j0idp6nqx"

unwants = Map.fromList $ zip aWmf [0..]

wants = "k_mfblobadb{udp{idp4{iaxz"

main = do
	print $ map (\x -> aAbc !! (unwants ! x)) wants