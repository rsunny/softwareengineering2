sig Position{
    latitude : Int,
    longitude : Int
}

sig phoneNumber{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

sig User{
    currentPosition : Position,
    reservedCar : lone Car,
    currentCar : lone Car,
    phonenumber : phoneNumber,
    sharing : one Bool
}

sig Car{
    currentPosition : Position,
    code : Int,
    seats : Int,
    lock : one Bool
}{
    code > 0
    seats > 0
    seats <= 4
}

fact CarIsUnlockedWhileUse{
    all c: Car | CarInUse[c] implies c.lock = False
}


fact carNotFilledByTwoPersons{
    no disjoint u, u' : User | u.currentCar = u'.currentCar
}

fact PhoneNumbersAreUnique {
    no disjoint p, p': User | (p != p') => p.phonenumber != p'.phonenumber
}

fact carNotReservedByTwoPeopleUnlessShared{
    no disjoint u, u' : User | ( u = u' and u.reservedCar =  u'.reservedCar) or (u.reservedCar =  u'.reservedCar and u.sharing = True and u'.sharing=True)
}

fact userMustReserveAndUse{
    no u : User | #u.reservedCar = 1 and #u.currentCar = 1
}

fact CarCodesAreUnique {
    no disjoint c, c': Car | (c != c') => c.code != c'.code
}

fact carNotShownWhileUsed{
    all c: Car | CarInUse[c] implies !CarReserved[c]
}

fact CarReservedWithProperSeats{
    all c : Car | CarReserved[c] implies c.seats<=4
}

fact CarReservedNotInUse{
    all c : Car | CarReserved[c] implies !CarInUse[c]
}

pred CarInUse [c : Car]{
    one u : User | u.currentCar = c
}

pred CarReserved[c: Car]{
    one u : User | u.reservedCar = c and c.lock = False
}

pred reserveCar [u : User, c : Car,  u' : User]{
    u.reservedCar = none and u.currentCar = none and 
    !(CarReserved[c]) and !(CarInUse[c])
    u'.currentPosition = u.currentPosition and u'.currentCar = none and u'.reservedCar = c
}

pred useCar[u, u' : User, c : Car] {
    u.currentCar = none and !(CarInUse[c]) and 
    (u.reservedCar = c or u.reservedCar = none)
    (u.reservedCar = c implies u'.reservedCar = none) and 
    u'.currentPosition = u.currentPosition and u'.currentCar = c
}

pred show{}

run CarInUse

run CarReserved

run reserveCar

run useCar
