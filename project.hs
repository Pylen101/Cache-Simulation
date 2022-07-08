data Item a = It Tag (Data a) Bool Int | NotPresent deriving (Show, Eq)
data Tag = T Int deriving (Show, Eq)
data Data a = D a deriving (Show, Eq)

data Output a = Out (a, Int) | NoOutput deriving (Show, Eq)
-------------------------------------------------------------------- GENERAL -----------------------------------------------------------

-- >> Converting a Binary number to a decimal number

convertBinToDec :: Integral a => a -> a
convertBinToDec b = convertBinToDecHelper b 0
convertBinToDecHelper 0 n = 0
convertBinToDecHelper b n = (b `mod` 10)*(2^n) + convertBinToDecHelper (div b 10) (n+1)

-- >> replaceIthItem

replaceIthItem :: (Eq a, Num a) => t -> [t] -> a -> [t]
replaceIthItem x (y:ys) 0 = [x] ++ ys
replaceIthItem x (y:ys) i = [y] ++ replaceIthItem x ys (i-1)

-- >> logBase2

logBase2 :: Floating a => a -> a
logBase2 n = logBase2Helper n 0
logBase2Helper 1 p = p
logBase2Helper n p = logBase2Helper (n/2) (p+1)

-- >> splitEvery

removeFirstN 0 l = l
removeFirstN n (x:xs) = (removeFirstN (n-1) xs)

splitEvery 0 l = [l]
splitEvery _ [] = []
splitEvery n l = (splitEveryHelper n l: splitEvery n (removeFirstN n l))

splitEveryHelper n [] = []
splitEveryHelper 0 l = []
splitEveryHelper n (x:xs) = (x:(splitEveryHelper (n-1) xs))																				

-- >> getNumBits

logBaseInt2 :: (Integral a, Num b) => a -> b
logBaseInt2 n = logBaseInt2Helper n 0
logBaseInt2Helper n i 
	| n<=1 = i
	| otherwise = logBaseInt2Helper (div n 2) (i+1)

getNumBits :: Num a => Int -> [Char] -> [b] -> a
getNumBits numOfSets cacheType cache 
	| cacheType == "fullyAssoc" = 0
	| cacheType == "setAssoc" = logBaseInt2(div (length cache) (numOfSets))
	| cacheType == "directMap" = (logBaseInt2 (length cache) )

-- >> fillZeros

fillZeros :: (Eq a, Num a) => [Char] -> a -> [Char]
fillZeros s 0 = s
fillZeros s n = "0" ++ fillZeros s (n-1)

------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------------
------------------------------------------------------ COMPONENTS ------------------------------------------------------

-- >> getDataFromCache

getDataFromCache stringAddress cache "setAssoc" bitsNum = getDataFromCacheSetHelper (convertAddress (read stringAddress::Int) bitsNum "setAssoc") (splitEvery (2^bitsNum) cache) 

getDataFromCache address cache directMap bitsNum = getDataFromCachehelper (getDataFromCachegetindex (read address::Int) bitsNum) (getDataFromCachetag (read address::Int) bitsNum) cache

getDataFromCacheSetHelper (t,i) splitCache = getDataFromCacheSetHelper2 t (convertBinToDec i) splitCache

getDataFromCacheSetHelper2 tag 0 (x:xs) = getDataFromCacheSetHelper3 tag x 0
getDataFromCacheSetHelper2 tag index (x:xs) = getDataFromCacheSetHelper2 tag (index - 1) xs

getDataFromCacheSetHelper3 _ [] _ = NoOutput
getDataFromCacheSetHelper3 tag ((It (T t) (D a) (b) _ ):xs) hops 
	| (tag == t) && (b==True) = Out (a , hops)
	| otherwise = getDataFromCacheSetHelper3 tag xs (hops +1)

getFirstN 0 m = ""
getFirstN n (x:xs) = (x:(getFirstN (n-1) xs))

measureLength [] = 0
measureLength (x:xs) = 1 + measureLength xs 

checkIfZero "" = 0
checkIfZero n = read n :: Int

getDataFromCachehelper index tag cache = if b == True && t == tag then Out(d,tag) else NoOutput
										 where It (T t) (D d) b o = cache !! index
										
										

getDataFromCachegetindex address bitsNum= convertBinToDec(mod address (10 ^ bitsNum))
getDataFromCachetag address bitsNum= div address (10 ^ bitsNum)
-- >> convertAddress

convertAddress bin bitsNum "directMap"= ( div bin (10 ^ bitsNum), mod bin (10 ^ bitsNum))

convertAddress binAddress bitsNum "setAssoc" = ( (checkIfZero (getFirstN (measureLength (show binAddress) - bitsNum) (show binAddress) )) , (checkIfZero (reverse (getFirstN (bitsNum) (reverse (show binAddress))))))

convertAddress bin bitsNum "directMap"= ( div bin (10 ^ bitsNum), mod bin (10 ^ bitsNum))
----------------------------------------------------- REPLACEMENT ------------------------------------------------------

-- >> replaceInCache (directMap)

replaceInCache tag idx memory oldCache "directMap" bitsNum	= replaceHelperDirectMap tag (convertBinToDec idx) (getFromMemoryDM tag idx memory bitsNum) oldCache

-- >> replaceInCache (fullyAssoc)

replaceInCache tag idx memory oldCache "fullyAssoc" bitsNum	
						| isValidBit oldCache = ((getDataFromMemoryFA tag memory) ,replaceInCacheVB tag (getDataFromMemoryFA tag memory) oldCache)
						| otherwise = ((getDataFromMemoryFA tag memory) ,replaceInCacheMO tag (getDataFromMemoryFA tag memory) (getMaxOrder oldCache) oldCache)

-- >> replaceInCache (setAssoc)

replaceInCache tag idx memory oldCache "setAssoc" bitsNum
				| isValidBit (getSet idx oldCache bitsNum) = (getDataFromMemorySA tag idx memory bitsNum ,
				concat (replaceIthItem (replaceInCacheVB tag (getDataFromMemorySA tag idx memory bitsNum) (getSet idx oldCache bitsNum )) (splitEvery (2^bitsNum) oldCache)  (convertBinToDec idx)) )
				| otherwise = (getDataFromMemorySA tag idx memory bitsNum ,
				concat (replaceIthItem (replaceInCacheMO tag (getDataFromMemorySA tag idx memory bitsNum) (getMaxOrder (getSet idx oldCache bitsNum )) (getSet idx oldCache bitsNum )) (splitEvery (2^bitsNum) oldCache)  (convertBinToDec idx)) )



---------------------------------------------------------- Replacement Helpers ------------------------------------------

-- >> DirectMap Helpers
getFromMemoryDM tag idx memory bitsNum	| (length (show idx)) == bitsNum = memory!!(convertBinToDec (read (show tag ++ show idx)))
										| otherwise = memory!!(convertBinToDec (read (show tag ++ (fillZeros (show idx) (length (show idx))))))

replaceHelperDirectMap tag idx dat oldCache = (dat, replaceIthItem (It (T tag) (D dat) True 0) oldCache idx)

-- >> fullyAssoc Helpers

isValidBit [] = False
isValidBit ((It (T t) (D d) b o):xs) = if (b == False) then True else isValidBit xs

getDataFromMemoryFA tag memory = memory!!(convertBinToDec tag) -- returns the data specified by the address

replaceInCacheVB tag d ((It (T t) (D dat) b o):xs)	| b == False = ((It (T tag) (D d) True 0):incrementOrder xs) -- Replacing incase of valid bit
													| otherwise = ((It (T t) (D dat) b (o+1)): replaceInCacheVB tag d xs)

replaceInCacheMO tag d maxOrder ((It (T t) (D dat) b o):xs)	| o == maxOrder = ((It (T tag) (D d) True 0):incrementOrder xs) -- Replacing incase of no valid bit
															| otherwise = ((It (T t) (D dat) b (o+1)): replaceInCacheMO tag d maxOrder xs)

incrementOrder [] = [] -- incrementing the order of the rest of the valid items in cache
incrementOrder ((It (T t) (D dat) b o):xs)	| b == True = ((It (T t) (D dat) b (o+1)): incrementOrder xs)
											| otherwise = ((It (T t) (D dat) b (o)): incrementOrder xs)

getMaxOrder [] = 0 --  getting the max order (last item placed) in the cache
getMaxOrder ((It (T t) (D dat) b o):xs) = max o (getMaxOrder xs)

-- >> setAssoc Helpers

getSet idx oldCache bitsNum = (splitEvery (2^bitsNum) oldCache)!!(convertBinToDec idx)

getDataFromMemorySA tag idx memory bitsNum 	| (length (show idx)) == bitsNum = memory!!(convertBinToDec (read (show tag ++ show idx)))
											| otherwise = memory!!(convertBinToDec (read (show tag ++ (fillZeros (show idx) (length (show idx))))))


-- >> getData

getData stringAddress cache memory cacheType bitsNum
								| x == NoOutput = replaceInCache tag index memory cache cacheType bitsNum
								| otherwise = (getX x, cache)
				where
						x = getDataFromCache stringAddress cache cacheType bitsNum
						address = read stringAddress:: Int
						(tag, index) = convertAddress address bitsNum cacheType
						getX (Out (d, _)) = d

-- >> runProgram

runProgram [] cache _ _ _ = ([], cache)
runProgram (addr: xs) cache memory cacheType numOfSets = ((d:prevData), finalCache)
				where
							bitsNum = round(logBase2 numOfSets)
							(d, updatedCache) = getData addr cache memory cacheType bitsNum
							(prevData, finalCache) = runProgram xs updatedCache memory cacheType numOfSets