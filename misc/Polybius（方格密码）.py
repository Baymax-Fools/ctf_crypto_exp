from itertools import permutations
nums = [1,2,3,4,5]

for item in permutations(nums,len(nums)):
    #item 是 nums的全排列
    dict = {
        'a':item[0],
        'e':item[1],
        'i':item[2],
        'o':item[3],
        'u':item[4]
    }
    data = "ouauuuoooeeaaiaeauieuooeeiea"
    key = "abcdefghiklmnopqrstuvwxyz"
    encText = ""
    for i in data:
        encText += str(dict[i])
    index_list = []
    for i in range(0,len(encText),2):
        tmp = (int(encText[i])-1)*5 + int(encText[i+1])
        index_list.append(tmp)
    # print(index_list)
    flag = ''
    for index in index_list:
        flag += key[index-1]
    print(flag)
