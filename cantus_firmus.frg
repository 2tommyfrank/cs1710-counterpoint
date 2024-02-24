#lang forge/bsl

// Cantus firmus
one sig Cf {
    mode: one Int,
    degrees: pfunc Int -> Int
}

fun lastMeasure: Int {
    max[{ i: Int | some Cf.degrees[i] }]
}

fun intervalOf[i, j : Int] : Int {
    add[abs[subtract[j, i]], 1]
}

pred wellformed {
    Cf.mode >= 0
    Cf.mode <= 6
    some Cf.degrees[0]
    // all i: Int | i != 0 implies {
    //     some Cf.degrees[i] implies some Cf.degrees[subtract[i, 1]]
    // }
    isSeqOf[Cf.degrees, Int]
}

pred validMode {
    let F = 3, B = 6 {
        Cf.mode != F
        Cf.mode != B
    }
}

pred validLength {
    lastMeasure >= 7
    lastMeasure <= 15
}

//starts and ends on modal final
pred validStartEnd {
    seqFirst[Cf.degrees] = 0
    seqLast[Cf.degrees] = 0
}

pred validRange {
    all disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] <= 8
    }
    some disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] >= 5
    }   
}

pred penultimateDescent {
    Cf.degrees[subtract[lastMeasure, 1]] = 1
}

pred validClimax {
    some i: Int | all j: Int | i != j implies {
        Cf.degrees[i] > Cf.degrees[j]
        Cf.degrees[i] != 6 // no seventh climax
    }
}

pred cantusFirmus {
    wellformed
    validMode
    validLength
    validStartEnd
    validRange
    penultimateDescent
    validClimax
}

run { cantusFirmus } for 5 Int
