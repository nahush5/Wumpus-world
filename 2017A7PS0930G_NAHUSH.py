#!/usr/bin/env python3
from Agent import * # See the Agent.py file
from copy import copy # needed for getting copy of dictionaries


#### All your code can go here.

#### You can change the main function as you wish. Run this program to see the output. Also see Agent.py code.

visited = [] ### used to check whether a square has been visited or not; visited[x][y] = 1 is [x, y] is visited else set to 0
safe = [] ### can be treated as the set of safe squares; if safe[x][y] = 1 then square x,y is safe; if safe[x][y] = 0, then it is unsafe; if safe[x][y] = -1, then we cannot conclude anything about the square
flag = 0  ### is set to 1 if the agent was successful in reaching the goal state [4, 4] 
symbols = ['B11', 'B21', 'B31', 'B41', 'B12', 'B22', 'B32', 'B42', 'B13', 'B23', 'B33', 'B43', 'B14', 'B24', 'B34', 'B44', ## B for breeze
           'S11', 'S21', 'S31', 'S41', 'S12', 'S22', 'S32', 'S42', 'S13', 'S23', 'S33', 'S43', 'S14', 'S24', 'S34', 'S44', ## S for stench
           'P11', 'P21', 'P31', 'P41', 'P12', 'P22', 'P32', 'P42', 'P13', 'P23', 'P33', 'P43', 'P14', 'P24', 'P34', 'P44', ## P for pit
           'W11', 'W21', 'W31', 'W41', 'W12', 'W22', 'W32', 'W42', 'W13', 'W23', 'W33', 'W43', 'W14', 'W24', 'W34', 'W44'] ## W for wumpus
KB = []  ### stores the Knowledge Base of the agent to make inferences off

callsToDPLL = 0 ## used to find overall calls made to dpll in the whole environment

def setVisited(): ## sets visited[x][y] = 0 for all [x, y]
    global visited

    visited = []
    for i in range(0, 5):
        v = []
        for j in range(0, 5):
            v.append(0)

        visited.append(v)

def setSafe(): ## sets safe[x][y] = -1 for all [x, y]
    global safe 

    for i in range(0, 5):
        o = []
        for j in range(0, 5):
            o.append(-1)

        safe.append(o)

    safe[1][1] = 1 ## [1, 1] was told to be safe from the problem statement



def everyClauseIsTrue(clauses): ## checks whether every clause is true while inferencing through the dpll algo. 
    for clause, value in clauses.items():
        if value != 'True':
            return False

    return True

def someClauseIsFalse(clauses): ## checks whether some clause is false while inferencing through the dpll algo. If yes, then you can return false immediately and implement early termination
    for clause, value in clauses.items():
        if value == 'False':
            return True

    return False

def findPureSymbol(clauses, symbolsUnassigned): ## Finds pure symbol among the clauses.

    for symbol, value in symbolsUnassigned.items():
        if(value == 'None'):
            negSign = 0
            posSign = 0
            
            for clause, val in clauses.items():
                if val == 'None':
                    index = clause.find(symbol)
                    if index != -1:
                        if index >= 1 and clause[index - 1] == '!':
                            negSign += 1
                        else:
                            posSign += 1

            if posSign == 0 and negSign > 0:
                return symbol, 'False'
            elif negSign == 0 and posSign > 0:
                return symbol, 'True'
            else:
                continue

    return 'None', 'None'


def setClause(clauses, clause, symbolToAssign, value, model): ## sets a clause to true if one of the literals turns out to be true. Sets to false if all literals are false. Else sets to None

    f = 0

    for i in clause.split(' '):
        if i.find(symbolToAssign) == -1:
            if i.find('!') != -1:
                string = i[1:4]
            else:
                string = i

            if model[string] == 'None':
                return
        else:
            if i.find('!') != -1: f = 1
            continue

    if f == 0:
        clauses[clause] = value
    else:
        if value == 'True':
            clauses[clause] = 'False' ## for implementing early termination
        else:
            clauses[clause] = 'True' ## for implementing early termination

    return




def setClauses(clauses, symbolToAssign, count, value, model): ### Sets all clauses to their required values
    for clause, val in clauses.items():
        if val == 'None':
            index = clause.find(symbolToAssign)
            if index != -1:
                if index >= 1 and clause[index - 1] == '!':
                    if value == 'False':
                        clauses[clause] = 'True' ## for implementing early termination
                    else:
                        setClause(clauses, clause, symbolToAssign, value, model)
                else:
                    if value == 'True':
                        clauses[clause] = 'True' ## for implementing early termination
                    else:
                        setClause(clauses, clause, symbolToAssign, value, model)
                count[clause] -= 1

    return clauses, count

def firstOf(symbolsUnassigned): ## returns the unassigned atomic propositions among the symbols.
    for symbol, value in symbolsUnassigned.items():
        if value == 'None':
            return symbol

    return 'None'

def assign(clauses, symbolsUnassigned, symbolToAssign, count, model, value): ## used for setting the clauses and creating new maps to use (to prevent the call by refernce problem to functions)
    new_symbolsUnassigned = copy(symbolsUnassigned)
    new_symbolsUnassigned[symbolToAssign] = value

    new_clauses = copy(clauses)
    new_count = copy(count)
    new_clauses, new_count = setClauses(new_clauses, symbolToAssign, new_count, value, model)
    
    new_model = copy(model)
    new_model[symbolToAssign] = value
    
    return new_clauses, new_symbolsUnassigned, new_model, new_count

def findUnitClause(clauses, count, symbolsUnassigned): ## finds unit clause.
    for clause, value in clauses.items():
        if value == 'None':
            if count[clause] == 1:
                for i in clause.split(' '):
                    if i.find('!') != -1:
                        string = i[1:4]
                        if symbolsUnassigned[string] == 'None':
                            return string, 'False'
                    else:
                        if symbolsUnassigned[i] == 'None':
                            return i, 'True'

    return 'None', 'None'

def dpll(clauses, symbolsUnassigned, model, count): ## The dpll algorithm
    global callsToDPLL

    callsToDPLL += 1

    if everyClauseIsTrue(clauses): return True
    if someClauseIsFalse(clauses): return False ## early termination

    symbolToAssign, value = findPureSymbol(clauses, symbolsUnassigned) ## find pure symbol

    if(symbolToAssign != 'None'):
        new_clauses, new_symbolsUnassigned, new_model, new_count = assign(clauses, symbolsUnassigned, symbolToAssign, count, model, value)
        return dpll(new_clauses, new_symbolsUnassigned, new_model, new_count)

    #### adding unit-clause heuristics

    symbolToAssign, value = findUnitClause(clauses, count, symbolsUnassigned) 

    if(symbolToAssign != 'None'):
        new_clauses, new_symbolsUnassigned, new_model, new_count = assign(clauses, symbolsUnassigned, symbolToAssign, count, model, value)
        return dpll(new_clauses, new_symbolsUnassigned, new_model, new_count)

    symbolToAssign = firstOf(symbolsUnassigned)

    new_clauses, new_symbolsUnassigned, new_model, new_count = assign(clauses, symbolsUnassigned, symbolToAssign, count, model, 'True')

    val1 = dpll(new_clauses, new_symbolsUnassigned, new_model, new_count)

    new_clauses, new_symbolsUnassigned, new_model, new_count = assign(clauses, symbolsUnassigned, symbolToAssign, count, model, 'False')

    val2 = dpll(new_clauses, new_symbolsUnassigned, new_model, new_count)

    return (val1 or val2)

def appendIfNotThere(str): ## appends str to KB if its not already there
    global KB
    if str not in KB:
        KB.append(str)

def tell(currentLocation, percept): ## uses the present percept to update the KB

    x = currentLocation[0]
    y = currentLocation[1]
    string = str(x) + str(y)

    if percept[0] == True:
        appendIfNotThere('B' + string) ## adding Bxy to KB
    else:
        appendIfNotThere('!B' + string) ## adding !Bxy to KB

    if percept[1] == True:
        appendIfNotThere('S' + string) ## adding Sxy to KB
    else:
        appendIfNotThere('!S' + string) ## adding !Sxy to KB


def reset(clauses, symbolsUnassigned, model, count): ## Resets the dictionaries before using them
    global KB

    clauses = {}
    symbolsUnassigned = {}
    model = {}
    count = {}

    for symbol in symbols:
        symbolsUnassigned[symbol] = 'None'
        model[symbol] = 'None'

    for clause in KB:
        clauses[clause] = 'None'

        c = 0
        for i in clause.split(' '):
            c += 1
        count[clause] = c

    return clauses, symbolsUnassigned, model, count

def ask(location): ## used for asking whether a square is safe or not. This is used by the agent to make inferences

    x = location[0]
    y = location[1]

    if safe[x][y] == 1: ## if the square was inferred before as safe by the dpll algorithm then return true
        return True
    elif safe[x][y] == 0: ## if it was inferred as unsafe by the dpll algorithm then return false
        return False

    clauses = {} ## map between clause and its truth value
    symbolsUnassigned = {} ## map between symbol and its truth value
    model = {} ## map between symbol and its truth value. Sort of like symbolsUnassigned, but used for clarity.
    count = {} ## map between clause and the number of unassigned symbols in the clause

    string = str(x) + str(y)

    clauses, symbolsUnassigned, model, count = reset(clauses, symbolsUnassigned, model, count)
    clauses[('P' + string + " " + 'W' + string)] = 'None' ## To check !P ^ !W we must get a false for KB ^ (P V W) by the dpll algorithm
    count[('P' + string + " " + 'W' + string)] = 2 

    val = dpll(clauses, symbolsUnassigned, model, count) ## asking whether there is a pit or wumpus

    if val == False: ## false means the square is safe
        safe[x][y] = 1
        return safe[x][y]
    
    return safe[x][y]


def getAdjacentRooms(x, y): ## returns the adjacent squares to current square and also the action needed to reach them
    room = []
    action = []

    if(x < 4):
        room.append([x + 1, y])
        action.append("Right")
    if(y < 4):
        room.append([x, y + 1])
        action.append("Up")   
    if(x > 1):
        room.append([x - 1, y])
        action.append("Left") 
    if(y > 1):
        room.append([x, y - 1])
        action.append("Down")    

    return room, action    
        
def reverse(act): ## returns the reverse action of the inputted action

    if(act == "Right"):
        return "Left"
    elif(act == "Left"):
        return "Right"
    elif(act == "Up"):
        return "Down"
    else:
        return "Up"

def getAns(ag, prev, did_action):
    global flag

    if flag == 1: return

    x, y = ag.FindCurrentLocation()
    percept = ag.PerceiveCurrentLocation()
    
    tell([x, y], percept) ## to update KB based on present percepts

    visited[x][y] = 1 ## [x, y] has been visited

    if x == 4 and y == 4: ## to check whether current location is goal or not
        flag = 1 ## flag is set to 1 if the goal was reached
        return

    rooms, action = getAdjacentRooms(x, y) 

    for index in range(len(rooms)):
        x0 = rooms[index][0]
        y0 = rooms[index][1]
        if rooms[index] == prev or visited[x0][y0] == 1: continue

        i = ask([x0, y0]) # ask whether the location is safe
        
        if i == -1 or i == 0: continue ## if not safe, don't proceed to it and try other adjacent squares

        ag.TakeAction(action[index]) ## proceed if safe
        getAns(ag, [x, y], action[index])

        if flag == 1: return ## if the goal location was reached, return

    ag.TakeAction(reverse(did_action)) ## this is effectively going back to previous location, so the agent should do the reverse of its latest action. This situation arises if -
                                       ## none of the adjacent unvisited squares are safe

def setKB():
    global KB

    KB.append('P11 P21 P31 P41 P12 P22 P32 P42 P13 P23 P33 P43 P14 P24 P34 P44') ## Indicates: Atleast one pit exists
    KB.append('W11 W21 W31 W41 W12 W22 W32 W42 W13 W23 W33 W43 W14 W24 W34 W44') ## Indicates: Atleast one wumpus exists

    ## Adding rules for: There is breeze in rooms adjacent to pits and stench in rooms adjacent to wumpus. This has two parts to it.

    for x in range(1, 5):
        for y in range(1, 5):
            ## Part1: For adding rules: Breeze in present square implies pit in one of the adjacent rooms and stench implies wumpus in one of teh adjacent rooms
            string1 = '!B' + str(x) + str(y) 
            string2 = '!S' + str(x) + str(y)
            if(x > 1):
                string1 += " " + "P" + str(x - 1) + str(y)
                string2 += " " + "W" + str(x - 1) + str(y)
            if(x < 4):
                string1 += " " + "P" + str(x + 1) + str(y)
                string2 += " " + "W" + str(x + 1) + str(y) 
            if(y > 1):
                string1 += " " + "P" + str(x) + str(y - 1)
                string2 += " " + "W" + str(x) + str(y - 1)    
            if(y < 4):
                string1 += " " + "P" + str(x) + str(y + 1)
                string2 += " " + "W" + str(x) + str(y + 1)

            KB.append(string1)
            KB.append(string2)

            ## Part2: For adding rules: No Breeze implies no pits in any of the adjacent rooms and no stench implies no wumpus in any of the adjacent rooms
            string1 = 'B' + str(x) + str(y)
            string2 = 'S' + str(x) + str(y)
            if(x > 1):
                str1 = string1 + " " + "!P" + str(x - 1) + str(y)
                str2 = string2 + " " + "!W" + str(x - 1) + str(y)
                KB.append(str1)
                KB.append(str2)
            if(x < 4):
                str1 = string1 + " " + "!P" + str(x + 1) + str(y)
                str2 = string2 + " " + "!W" + str(x + 1) + str(y) 
                KB.append(str1)
                KB.append(str2)
            if(y > 1):
                str1 = string1 + " " + "!P" + str(x) + str(y - 1)
                str2 = string2 + " " + "!W" + str(x) + str(y - 1) 
                KB.append(str1)
                KB.append(str2)
            if(y < 4):
                str1 = string1 + " " + "!P" + str(x) + str(y + 1)
                str2 = string2 + " " + "!W" + str(x) + str(y + 1)
                KB.append(str1)
                KB.append(str2)

    ## Adding rules for atmost one pit and atmost one wumpus.
    for x in range(1, 5):
        for y in range(1, 5):
            for i in range(1, 5):
                for j in range(1, 5):

                    if x == i and y == j: continue

                    string1 = '!P' + str(x) + str(y)
                    string2 = '!P' + str(i) + str(j)

                    str1 = string1 + " " + string2
                    str2 = string2 + " " + string1
                    if str1 not in KB and str2 not in KB:
                        KB.append(str1)

                    string1 = '!W' + str(x) + str(y)
                    string2 = '!W' + str(i) + str(j)

                    str1 = string1 + " " + string2
                    str2 = string2 + " " + string1
                    if str1 not in KB and str2 not in KB:
                        KB.append(str1)

    ## Rule for no pit or wumpus in starting location

    KB.append('!P11') ## No pit in room [1, 1]
    KB.append('!W11') ## No wumpus in room [1, 1]

    return


def main():
    ag = Agent()
    setKB() ## Sets the initial KB
    setSafe() ## sets the squares to -1 except for [1, 1]
    print("Agent Enters Wumpus world, Current Location [1, 1]")

    while 1:
        setVisited() ## sets visited to 0 for all squares. 
        getAns(ag, [0, 0], "Right") ## Agent makes an attempt

        if(flag == 1): ## if agent reaches goal then break
            break

        ## if agent doesn't reach goal, then it returns to [1, 1] and retries, in which cases visited[x][y] is set to 0 for all [x, y] onces again.

    print("\nCalls made to dpll: " + str(callsToDPLL)) 


if __name__=='__main__':
    main()
