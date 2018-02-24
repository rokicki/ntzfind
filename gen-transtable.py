import re
from sys import argv
from os import system
zorq = "z" #Change to "q" for ntqfind
#Binary encoding of each isotropic configuration
#Ordering is:
#8 1 2
#7 0 3
#6 5 4
#This could probably be changed by bit-shuffling if necessary.
transitions = {
    '0' : [0],
    '1c': [64, 4, 16, 1],
    '1e': [128, 2, 32, 8],
    '2a': [192, 6, 48, 129, 12, 96, 3, 24],
    '2c': [80, 20, 5, 65],
    '2e': [160, 10, 40, 130],
    '2i': [136, 34],
    '2k': [144, 18, 36, 132, 9, 33, 66, 72],
    '2n': [68, 17],
    '3a': [224, 14, 56, 131],
    '3c': [84, 21, 69, 81],
    '3e': [168, 42, 138, 162],
    '3i': [193, 7, 112, 28],
    '3j': [194, 134, 176, 161, 44, 104, 11, 26],
    '3k': [164, 74, 41, 146],
    '3n': [208, 22, 52, 133, 13, 97, 67, 88],
    '3q': [196, 70, 49, 145, 76, 100, 19, 25],
    '3r': [200, 38, 50, 137, 140, 98, 35, 152],
    '3y': [148, 82, 37, 73],
    '4a': [240, 30, 60, 135, 15, 225, 195, 120],
    '4c': [85],
    '4e': [170],
    '4i': [216, 54, 141, 99],
    '4j': [202, 166, 178, 169, 172, 106, 43, 154],
    '4k': [210, 150, 180, 165, 45, 105, 75, 90],
    '4n': [209, 23, 116, 197, 29, 113, 71, 92],
    '4q': [228, 78, 57, 147],
    '4r': [232, 46, 58, 139, 142, 226, 163, 184],
    '4t': [201, 39, 114, 156],
    '4w': [198, 177, 108, 27],
    '4y': [212, 86, 53, 149, 77, 101, 83, 89],
    '4z': [204, 102, 51, 153],
    '5a': [241, 31, 124, 199],
    '5c': [234, 174, 186, 171],
    '5e': [213, 87, 117, 93],
    '5i': [248, 62, 143, 227],
    '5j': [244, 94, 61, 151, 79, 229, 211, 121],
    '5k': [214, 181, 109, 91],
    '5n': [242, 158, 188, 167, 47, 233, 203, 122],
    '5q': [236, 110, 59, 155, 206, 230, 179, 185],
    '5r': [220, 118, 55, 157, 205, 103, 115, 217],
    '5y': [218, 182, 173, 107],
    '6a': [252, 126, 63, 159, 207, 231, 243, 249],
    '6c': [250, 190, 175, 235],
    '6e': [245, 95, 125, 215],
    '6i': [221, 119],
    '6k': [246, 222, 189, 183, 111, 237, 219, 123],
    '6n': [238, 187],
    '7c': [254, 191, 239, 251],
    '7e': [253, 127, 223, 247],
    '8' : [255]
}
transtable = [0]*512
rulestring = argv[1]

#Parse the rulestring:
b, s = rulestring.split("/") #Separate B and S transitions
b, s = b[1:], s[1:] #Remove the characters 'B' and 'S'
transgroup = re.compile(r"([0-8][a-zA-Z\-]*)") #Matches a group of isotropic transitions sharing the same outer-totalistic count
b, s = re.findall(transgroup, b), re.findall(transgroup, s) #Divide into transition groups

#Build first half of transition table
for i in b:
    # e.g. B3 or B2-an
    if len(i) == 1 or i[1] == "-":
        #Set all transitions with the given outer-totalistic count (possibly preemptively)
        for j in transitions:
            if j[0] == i[0]:
                for k in transitions[j]:
                    transtable[k] = 1
    # e.g. B2ce
    else:
        #Set all given transitions in group
        for j in i[1:]:
            for k in transitions[i[0]+j]:
                transtable[k] = 1
    # e.g. B2-an
    if len(i) > 1 and i[1] == "-":
        #Unset all given transitions in group
        for j in i[2:]:
            for k in transitions[i[0]+j]:
                transtable[k] = 0

#Build second half
for i in s:
    # e.g. B3 or B2-an
    if len(i) == 1 or i[1] == "-":
        #Set all transitions with the given outer-totalistic count (possibly preemptively)
        for j in transitions:
            if j[0] == i[0]:
                for k in transitions[j]:
                    transtable[k|256] = 1
    # e.g. B2ce
    else:
        #Set all given transitions in group
        for j in i[1:]:
            for k in transitions[i[0]+j]:
                transtable[k|256] = 1
    # e.g. B2-an
    if len(i) > 1 and i[1] == "-":
        #Unset all given transitions in group
        for j in i[2:]:
            for k in transitions[i[0]+j]:
                transtable[k|256] = 0

#Print transition table
with open("nttable.c", "w") as f:
    f.write("int nttable[] = {" + "".join([str(transtable[i]) + (",\n"+" "*17 if not (i+1)%16 else ", ") for i in xrange(512)])[:-19] + "};")

system("g++ -O3 nt%sfind.cpp -o nt%sfind" % ((zorq,)*2)) #Change this command if not applicable to your system
