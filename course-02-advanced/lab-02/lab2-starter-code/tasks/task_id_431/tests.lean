#guard hasCommonElement (#[1, 2, 3]) (#[4, 5, 6]) = (false)
#guard hasCommonElement (#[1, 2, 3]) (#[3, 4, 5]) = (true)
#guard hasCommonElement (#[7, 8, 9]) (#[10, 11, 7]) = (true)
#guard hasCommonElement (#[1, 2, 3, 4]) (#[5, 6, 7, 8]) = (false)
#guard hasCommonElement (#[1, 2, 3, 4]) (#[4, 5, 6]) = (true)
#guard hasCommonElement (#[1, 1, 1]) (#[1, 2, 1]) = (true)
#guard hasCommonElement (#[0]) (#[0]) = (true)
#guard hasCommonElement (#[0]) (#[-1, 1]) = (false)